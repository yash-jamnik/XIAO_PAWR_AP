

/*
 * Copyright (c) 2023 Nordic Semiconductor ASA
 *
 * SPDX-License-Identifier: Apache-2.0
 */
/*
 * Copyright (c) 2023 Nordic Semiconductor ASA
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include "src/command.pb.h"
#include "pb_encode.h"
#include <zephyr/bluetooth/att.h>
#include <zephyr/bluetooth/bluetooth.h>
#include <zephyr/bluetooth/conn.h>
#include <zephyr/bluetooth/gatt.h>
#include <zephyr/bluetooth/hci.h>
#include <zephyr/drivers/uart.h>
#include <zephyr/console/console.h>
#include <zephyr/sys/reboot.h>
#include <zephyr/linker/section_tags.h>
#include <zephyr/kernel.h>
#include <zephyr/sys/__assert.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <zephyr/fs/nvs.h>
#include "pb_decode.h"
#include <zephyr/app_version.h>

static int target_response_subevent = -1;

static struct nvs_fs fs;
static char active_command_mac[BT_ADDR_STR_LEN] = {0};
#define NVS_ID_MCUMGR_MODE 1

#include <zephyr/storage/flash_map.h>

static int nvs_init_app(void)
{
	const struct flash_area *fa;
	int rc;

	rc = flash_area_open(FIXED_PARTITION_ID(storage), &fa);
	if (rc)
	{
		return rc;
	}

	fs.flash_device = flash_area_get_device(fa);
	fs.offset = fa->fa_off;
	fs.sector_size = 4096;
	fs.sector_count = 4;

	return nvs_mount(&fs);
}

__noinit static bool mcumgr_mode;
static bool logs_enabled = true;

#define APP_LOG(...)             \
	do                           \
	{                            \
		if (logs_enabled)        \
		{                        \
			printk(__VA_ARGS__); \
		}                        \
	} while (0)

int parse_mac(const char *str, uint8_t *mac)
{
	return sscanf(str, "%hhx:%hhx:%hhx:%hhx:%hhx:%hhx",
				  &mac[0], &mac[1], &mac[2],
				  &mac[3], &mac[4], &mac[5]);
}

void test_proto(void)
{
	Command cmd = Command_init_zero;

	// 🔹 Fill data
	cmd.request_id = 1;
	cmd.which_cmd = Command_led_tag;
	// cmd.cmd.led = 123;

	uint8_t buffer[30];

	pb_ostream_t stream = pb_ostream_from_buffer(buffer, sizeof(buffer));

	// 🔹 Encode
	if (!pb_encode(&stream, Command_fields, &cmd))
	{
		APP_LOG("❌ Encode failed\n");
		return;
	}

	size_t len = stream.bytes_written;

	// 🔹 Print result
	APP_LOG("✅ Encoded size: %d\n", (int)len);

	APP_LOG("HEX: ");
	for (int i = 0; i < len; i++)
	{
		APP_LOG("%02X ", buffer[i]);
	}
	APP_LOG("\n");

	// 🔹 Optional: store globally for later PAwR use
}
#define ONBOARDING_COOLDOWN_MS 3000

static atomic_t onboarding_busy = ATOMIC_INIT(0);
static int64_t last_onboard_time = 0;

#define NUM_RSP_SLOTS 10
#define NUM_SUBEVENTS 15
#define PACKET_SIZE 30
#define NAME_LEN 30
#define UART_BUF_SIZE 256
#define CMD_BUF_SIZE 128

static char active_cmd[PACKET_SIZE];
static size_t active_cmd_len;

void prepare_active_command(const char *mac)
{
	snprintf(active_cmd,
			 sizeof(active_cmd),
			 "ACTIVE,%s",
			 mac);

	active_cmd_len = strlen(active_cmd);

	printk("Prepared PAwR command: %s (len=%d)\n",
		   active_cmd,
		   (int)active_cmd_len);
}
#define MAX_SYNCS (NUM_SUBEVENTS * NUM_RSP_SLOTS)
#define SLOT_TIMEOUT_MS 45000 // 90 seconds
#define INVALID_SLOT 0xFF
#define ADDR_STR_LEN BT_ADDR_LE_STR_LEN // full bt_addr_le_to_str() string

static uint8_t proto_buf[PACKET_SIZE];
static size_t proto_len = 0;
static bool proto_command_active = false;
static K_SEM_DEFINE(sem_connected, 0, 1);
static K_SEM_DEFINE(sem_discovered, 0, 1);
static K_SEM_DEFINE(sem_written, 0, 1);
static K_SEM_DEFINE(sem_disconnected, 0, 1);

static struct bt_uuid_128 pawr_char_uuid =
	BT_UUID_INIT_128(BT_UUID_128_ENCODE(0x12345678, 0x1234, 0x5678, 0x1234, 0x56789abcdef1));
static uint16_t pawr_attr_handle;

static const struct bt_le_per_adv_param per_adv_params = {
	.interval_min = 0xC00,
	.interval_max = 0xC00,
	.options = 0,
	.num_subevents = NUM_SUBEVENTS,
	.subevent_interval = 0xA0,
	.response_slot_delay = 0x10,
	.response_slot_spacing = 0x20,
	.num_response_slots = NUM_RSP_SLOTS,
};

#define JOIN_THREAD_STACK_SIZE 2048
#define JOIN_THREAD_PRIORITY 5
K_THREAD_STACK_DEFINE(join_thread_stack, JOIN_THREAD_STACK_SIZE);

static struct bt_le_per_adv_subevent_data_params subevent_data_params[NUM_SUBEVENTS];
static struct net_buf_simple bufs[NUM_SUBEVENTS];
static uint8_t backing_store[NUM_SUBEVENTS][PACKET_SIZE];
static struct bt_le_ext_adv *pawr_adv = NULL;

BUILD_ASSERT(ARRAY_SIZE(bufs) == ARRAY_SIZE(subevent_data_params));
BUILD_ASSERT(ARRAY_SIZE(backing_store) == ARRAY_SIZE(subevent_data_params));
static void device_found(const bt_addr_le_t *addr, int8_t rssi, uint8_t type,
						 struct net_buf_simple *ad);
struct pawr_timing
{
	uint8_t subevent;
	uint8_t response_slot;
} __packed;

// Command handling structures
static const struct device *uart_dev;
static uint8_t num_synced;

// Default and current command
static const char default_command[] = "[+]join,9999";
static char current_command[CMD_BUF_SIZE] = "[+]join,9999";

// Temporary "join" command state: active for N ms, then revert to default
#define TEMP_CMD_DURATION_MS 5000 // "few seconds" – adjust as you like
#define RESPONSE_WINDOW_TIMEOUT_MS 3000
static bool temp_command_active = false;
static int64_t temp_command_expiry_ms = 0;
static bool response_window_active = false;
static int64_t response_window_expiry_ms = 0;

enum pawr_device_state
{
	PAWR_DEVICE_DISCONNECTED = 0,
	PAWR_DEVICE_SYNCED,
	PAWR_DEVICE_VERIFYING,
};
// Structure to store synced device information
struct synced_device
{
	bool active;
	enum pawr_device_state state;
	uint8_t subevent;
	uint8_t response_slot;

	char address[ADDR_STR_LEN]; // BT addr as string (from onboarding)
	char device_id[16];			// ID from "devid,XXXX"
	bool has_device_id;

	int64_t last_update_time;
	int64_t last_response_time;
	int64_t last_sync_time;
	bool active_check_pending;
	uint8_t active_check_retry;
	int64_t active_check_time;
};

static struct synced_device synced_devices[MAX_SYNCS];

// Forward declarations
void display_synced_devices_status(void);
void restart_advertising(void);

// Helper: check if a slot is still responsive (based on last_update_time)
static bool is_slot_responsive(int slot_index)
{

	if (!synced_devices[slot_index].active)
		return false;

	int64_t now = k_uptime_get();

	/* Never received a response yet → allow grace period */
	if (synced_devices[slot_index].last_response_time == 0)
	{
		return true;
	}

	int64_t diff = now - synced_devices[slot_index].last_response_time;

	if (diff > SLOT_TIMEOUT_MS)
	{
		// APP_LOG("Slot %d lost device (no PAwR response for %lld ms)\n",
		// 		slot_index, diff);
		return false;
	}

	return true;
}

// Clear a slot completely (only for errors/timeouts, not normal disconnect)
static void clear_slot(int slot_index)
{

	if (synced_devices[slot_index].active)
	{
		APP_LOG("[+]DISCONNECTED,%s\n",
				synced_devices[slot_index].address);
		if (num_synced > 0)
		{
			num_synced--;
		}
	}

	synced_devices[slot_index].state = PAWR_DEVICE_DISCONNECTED;
	synced_devices[slot_index].active = false;
	synced_devices[slot_index].subevent = INVALID_SLOT;
	synced_devices[slot_index].response_slot = INVALID_SLOT;

	memset(synced_devices[slot_index].address, 0, sizeof(synced_devices[slot_index].address));
	memset(synced_devices[slot_index].device_id, 0, sizeof(synced_devices[slot_index].device_id));
	synced_devices[slot_index].has_device_id = false;

	synced_devices[slot_index].last_update_time = 0;
	synced_devices[slot_index].last_response_time = 0;
	synced_devices[slot_index].last_sync_time = 0;
	synced_devices[slot_index].active_check_pending = false;
	synced_devices[slot_index].active_check_retry = 0;
	synced_devices[slot_index].active_check_time = 0;
	synced_devices[slot_index].state = PAWR_DEVICE_DISCONNECTED;

	// APP_LOG("Cleared slot %d\n", slot_index);
}
// Same as clear_slot but without DISCONNTED log
static void clear_slot_silent(int slot_index)
{
	if (synced_devices[slot_index].active)
	{
		if (num_synced > 0)
		{
			num_synced--;
		}
	}
	synced_devices[slot_index].state = PAWR_DEVICE_DISCONNECTED;
	synced_devices[slot_index].active = false;
	synced_devices[slot_index].subevent = INVALID_SLOT;
	synced_devices[slot_index].response_slot = INVALID_SLOT;

	memset(synced_devices[slot_index].address, 0, sizeof(synced_devices[slot_index].address));
	memset(synced_devices[slot_index].device_id, 0, sizeof(synced_devices[slot_index].device_id));
	synced_devices[slot_index].has_device_id = false;
	synced_devices[slot_index].last_update_time = 0;
	synced_devices[slot_index].last_response_time = 0;
	synced_devices[slot_index].last_sync_time = 0;
	synced_devices[slot_index].active_check_pending = false;
	synced_devices[slot_index].active_check_retry = 0;
	synced_devices[slot_index].active_check_time = 0;
	synced_devices[slot_index].state = PAWR_DEVICE_DISCONNECTED;

	APP_LOG("Cleared slot %d (silent)\n", slot_index);
}

// Find existing slot by address, or assign a new one
static int find_or_assign_slot(const char *address, uint8_t *subevent, uint8_t *response_slot)
{
	// First, search for an existing active slot with same address
	for (int i = 0; i < MAX_SYNCS; i++)
	{
		if (synced_devices[i].active &&
			strcmp(synced_devices[i].address, address) == 0)
		{
			// Check if the slot is still responsive
			if (is_slot_responsive(i))
			{
				*subevent = synced_devices[i].subevent;
				*response_slot = synced_devices[i].response_slot;
				synced_devices[i].last_update_time = k_uptime_get();

				APP_LOG("[+]new,%s\n", address);
				APP_LOG("Reusing slot %d for device %s (subevent %d, response_slot %d)\n",
						i, address, *subevent, *response_slot);
				return i;
			}
			else
			{
				APP_LOG("Clearing unresponsive slot %d for device %s\n", i, address);
				clear_slot_silent(i);
			}
		}
	}

	// Reuse any inactive slot for new device
	for (int i = 0; i < MAX_SYNCS; i++)
	{
		if (!synced_devices[i].active)
		{
			*subevent = i % NUM_SUBEVENTS;
			*response_slot = i / NUM_SUBEVENTS;

			strncpy(synced_devices[i].address, address,
					sizeof(synced_devices[i].address) - 1);
			synced_devices[i].address[sizeof(synced_devices[i].address) - 1] = '\0';

			synced_devices[i].active = true;
			synced_devices[i].state = PAWR_DEVICE_SYNCED;
			synced_devices[i].subevent = *subevent;
			synced_devices[i].response_slot = *response_slot;
			synced_devices[i].last_update_time = k_uptime_get();

			// device_id not known yet at onboarding
			synced_devices[i].device_id[0] = '\0';
			synced_devices[i].has_device_id = false;

			num_synced++;
			APP_LOG("[+]new,%s\n", synced_devices[i].address);
			APP_LOG("Assigned new slot %d for device %s (subevent %d, response_slot %d)\n",
					i, address, *subevent, *response_slot);
			return i;
		}
	}

	APP_LOG("No available slot for device %s\n", address);
	return -1; // No slot available
}

// UART polling function for reading commands (currently unused in main loop)
static int uart_read_command(char *buffer, size_t buffer_size)
{
	static char rx_buffer[UART_BUF_SIZE];
	static int rx_pos = 0;
	uint8_t c;

	int chars_read = 0;
	while (uart_poll_in(uart_dev, &c) == 0 && chars_read < 50)
	{
		chars_read++;

		if (c == '\n' || c == '\r')
		{
			if (rx_pos > 0)
			{
				rx_buffer[rx_pos] = '\0';
				strncpy(buffer, rx_buffer, buffer_size - 1);
				buffer[buffer_size - 1] = '\0';
				APP_LOG("\nUART: Command received: '%s'\n", buffer);
				rx_pos = 0;
				return strlen(buffer);
			}
		}
		else if (c == '\b' || c == 0x7F)
		{
			if (rx_pos > 0)
			{
				rx_pos--;
				uart_poll_out(uart_dev, '\b');
				uart_poll_out(uart_dev, ' ');
				uart_poll_out(uart_dev, '\b');
			}
		}
		else if (rx_pos < sizeof(rx_buffer) - 1 && c >= 0x20 && c <= 0x7E)
		{
			rx_buffer[rx_pos++] = c;
			uart_poll_out(uart_dev, c);
		}
	}

	return 0;
}

// Function to send command data to all synced devices (immediate push)
static int send_command_to_synced_devices(struct bt_le_ext_adv *pawr_adv, const char *command)
{
	int err;
	uint8_t active_devices = 0;
	size_t cmd_len = strlen(command);

	APP_LOG("Updating command to: '%s'\n", command);

	// Update the global current command
	strncpy(current_command, command, CMD_BUF_SIZE - 1);
	current_command[CMD_BUF_SIZE - 1] = '\0';

	// Count active synced devices
	for (int i = 0; i < MAX_SYNCS; i++)
	{
		if (synced_devices[i].active)
		{
			active_devices++;
		}
	}

	if (active_devices == 0)
	{
		APP_LOG("No synced devices available - but command updated for future requests\n");
		APP_LOG("Current command will be sent when devices sync or on next PAwR request\n");
		return 0;
	}

	// Immediately prepare and send the new command data
	for (size_t i = 0; i < NUM_SUBEVENTS; i++)
	{
		struct net_buf_simple *buf = &bufs[i];

		memset(buf->data, 0, PACKET_SIZE);

		size_t copy_len = MIN(cmd_len, PACKET_SIZE - 1);
		memcpy(buf->data, command, copy_len);
		buf->data[copy_len] = '\0';
		buf->len = copy_len + 1;

		subevent_data_params[i].subevent = i;
		subevent_data_params[i].response_slot_start = 0;
		subevent_data_params[i].response_slot_count = NUM_RSP_SLOTS;
		subevent_data_params[i].data = buf;
	}

	err = bt_le_per_adv_set_subevent_data(pawr_adv, NUM_SUBEVENTS, subevent_data_params);
	APP_LOG("Command '%s' sent immediately to %d synced devices\n", command, active_devices);
	APP_LOG("Current active command: '%s'\n", current_command);

	return 0;
}

static void format_mac_hex(const uint8_t *mac,
						   char *out,
						   size_t out_size)
{
	snprintf(out,
			 out_size,
			 "%02X:%02X:%02X:%02X:%02X:%02X",
			 mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]);
}

static bool decode_tel_response(const uint8_t *data, size_t len,
								char *mac_out, size_t mac_out_size,
								char *meta_out, size_t meta_out_size)
{
	Command msg = Command_init_zero;
	pb_istream_t stream = pb_istream_from_buffer(data, len);

	if (!pb_decode(&stream, Command_fields, &msg))
		return false;

	if (msg.which_cmd != Command_tel_res_tag)
		return false;

	if (msg.cmd.tel_res.mac.size != 6)
		return false;

	format_mac_hex(msg.cmd.tel_res.mac.bytes, mac_out, mac_out_size);
	strncpy(meta_out, msg.cmd.tel_res.meta, meta_out_size - 1);
	meta_out[meta_out_size - 1] = '\0';

	return true;
}

void encode_led_command_with_mac(uint8_t *mac)
{
	Command cmd = Command_init_zero;
	cmd.request_id = 1;
	cmd.which_cmd = Command_led_tag;
	memcpy(cmd.cmd.led.mac.bytes, mac, 6);
	cmd.cmd.led.mac.size = 6;

	pb_ostream_t stream = pb_ostream_from_buffer(proto_buf, sizeof(proto_buf));
	if (!pb_encode(&stream, Command_fields, &cmd))
	{
		APP_LOG("Encode failed\n");
		proto_len = 0;
		proto_command_active = false;
		return;
	}
	proto_len = stream.bytes_written;
	proto_command_active = true;
	APP_LOG("Proto len: %d\n", (int)proto_len);
}
void encode_splash_command_with_mac(uint8_t *mac)
{
	Command cmd = Command_init_zero;
	cmd.request_id = 1;
	cmd.which_cmd = Command_default_image_tag;
	memcpy(cmd.cmd.default_image.mac.bytes, mac, 6);
	cmd.cmd.default_image.mac.size = 6;

	pb_ostream_t stream = pb_ostream_from_buffer(proto_buf, sizeof(proto_buf));
	if (!pb_encode(&stream, Command_fields, &cmd))
	{
		APP_LOG("SPLASH encode failed\n");
		proto_len = 0;
		proto_command_active = false;
		return;
	}
	proto_len = stream.bytes_written;
	proto_command_active = true;
	APP_LOG("SPLASH proto len: %d\n", (int)proto_len);
}
void encode_clear_command_with_mac(uint8_t *mac)
{
	Command cmd = Command_init_zero;
	cmd.request_id = 1;
	cmd.which_cmd = Command_clear_epd_tag;
	memcpy(cmd.cmd.clear_epd.mac.bytes, mac, 6);
	cmd.cmd.clear_epd.mac.size = 6;

	pb_ostream_t stream = pb_ostream_from_buffer(proto_buf, sizeof(proto_buf));
	if (!pb_encode(&stream, Command_fields, &cmd))
	{
		APP_LOG("CLEAR encode failed\n");
		proto_len = 0;
		proto_command_active = false;
		return;
	}
	proto_len = stream.bytes_written;
	proto_command_active = true;
	APP_LOG("CLEAR proto len: %d\n", (int)proto_len);
}

void encode_join_command_with_mac(uint8_t *esl_mac, uint8_t *ots_mac)
{
	Command cmd = Command_init_zero;
	cmd.request_id = 1;
	cmd.which_cmd = Command_join_tag;
	memcpy(cmd.cmd.join.mac.bytes, esl_mac, 6);
	cmd.cmd.join.mac.size = 6;
	memcpy(cmd.cmd.join.ots_mac.bytes, ots_mac, 6);
	cmd.cmd.join.ots_mac.size = 6;

	pb_ostream_t stream = pb_ostream_from_buffer(proto_buf, sizeof(proto_buf));
	if (!pb_encode(&stream, Command_fields, &cmd))
	{
		APP_LOG("Join encode failed\n");
		proto_len = 0;
		proto_command_active = false;
		return;
	}
	proto_len = stream.bytes_written;
	proto_command_active = true;
	APP_LOG("Join proto len: %d\n", (int)proto_len);
}

void encode_ota_command_with_mac(uint8_t *esl_mac, uint8_t *ots_mac)
{
	Command cmd = Command_init_zero;
	cmd.request_id = 1;
	cmd.which_cmd = Command_ota_tag;
	memcpy(cmd.cmd.ota.mac.bytes, esl_mac, 6);
	cmd.cmd.ota.mac.size = 6;
	memcpy(cmd.cmd.ota.ots_mac.bytes, ots_mac, 6);
	cmd.cmd.ota.ots_mac.size = 6;

	pb_ostream_t stream = pb_ostream_from_buffer(proto_buf, sizeof(proto_buf));
	if (!pb_encode(&stream, Command_fields, &cmd))
	{
		APP_LOG("OTA encode failed\n");
		proto_len = 0;
		proto_command_active = false;
		return;
	}
	proto_len = stream.bytes_written;
	proto_command_active = true;
	APP_LOG("OTA proto len: %d\n", (int)proto_len);
}

void encode_tel_command_with_mac(uint8_t *mac)
{
	Command cmd = Command_init_zero;
	cmd.request_id = 1;
	cmd.which_cmd = Command_tel_tag;
	memcpy(cmd.cmd.tel.mac.bytes, mac, 6);
	cmd.cmd.tel.mac.size = 6;

	pb_ostream_t stream = pb_ostream_from_buffer(proto_buf, sizeof(proto_buf));
	if (!pb_encode(&stream, Command_fields, &cmd))
	{
		APP_LOG("TEL encode failed\n");
		proto_len = 0;
		proto_command_active = false;
		return;
	}
	proto_len = stream.bytes_written;
	proto_command_active = true;
	APP_LOG("TEL proto len: %d\n", (int)proto_len);
}
// Function to parse and handle commands
static void process_command(struct bt_le_ext_adv *pawr_adv, const char *cmd)
{

	APP_LOG("CMD: '%s'\n", cmd);

	if (strncmp(cmd, "[+]join,", 8) == 0)
	{
		char esl_mac_str[32];
		char ots_mac_str[32];

		uint8_t esl_mac[6];
		uint8_t ots_mac[6];

		if (sscanf(cmd,
				   "[+]join,%31[^,],%31s",
				   esl_mac_str,
				   ots_mac_str) != 2)
		{
			APP_LOG("Invalid join format\n");
			APP_LOG("Expected: [+]join,<esl_mac>,<ots_mac>\n");
			return;
		}

		if (parse_mac(esl_mac_str, esl_mac) != 6)
		{
			APP_LOG("Invalid ESL MAC\n");
			return;
		}

		if (parse_mac(ots_mac_str, ots_mac) != 6)
		{
			APP_LOG("Invalid OTS MAC\n");
			return;
		}

		display_synced_devices_status();

		temp_command_active = true;
		temp_command_expiry_ms = k_uptime_get() + TEMP_CMD_DURATION_MS;
		for (int i = 0; i < MAX_SYNCS; i++)
		{
			if (synced_devices[i].active &&
				strcmp(synced_devices[i].address, esl_mac_str) == 0)
			{
				synced_devices[i].state = PAWR_DEVICE_VERIFYING;
				break;
			}
		}
		encode_join_command_with_mac(esl_mac, ots_mac);

		if (proto_command_active && proto_len > 0)
		{
			APP_LOG("SUCCESS: Join command sent\n");
			APP_LOG("ESL MAC : %s\n", esl_mac_str);
			APP_LOG("OTS MAC : %s\n", ots_mac_str);
		}
		else
		{
			APP_LOG("ERROR: Failed to send join command\n");
		}
	}
	else if (strncmp(cmd, "join,", 5) == 0)

	{
		const char *param = cmd + 5;
		int join_param = atoi(param);
		char full_cmd[64];

		snprintf(full_cmd, sizeof(full_cmd), "[+]join,%d", join_param);
		APP_LOG("Join command detected (auto-format) with parameter: %d\n", join_param);
		APP_LOG("Formatted command: %s\n", full_cmd);

		// Activate temporary join command for a few seconds
		temp_command_active = true;
		temp_command_expiry_ms = k_uptime_get() + TEMP_CMD_DURATION_MS;

		display_synced_devices_status();

		int err = send_command_to_synced_devices(pawr_adv, full_cmd);
		if (err)
		{
			APP_LOG("ERROR: Failed to send join command to devices (err %d)\n", err);
		}
		else
		{
			APP_LOG("SUCCESS: Join command sent to all synced devices (burst mode)\n");
			APP_LOG("Temporary command active for %d ms\n", TEMP_CMD_DURATION_MS);
		}
	}
	else if (strcmp(cmd, "test") == 0 || strcmp(cmd, "t") == 0)
	{
		APP_LOG("Resetting to default join command: %s\n", default_command);
		strncpy(current_command, default_command, CMD_BUF_SIZE - 1);
		current_command[CMD_BUF_SIZE - 1] = '\0';
		temp_command_active = false;
		temp_command_expiry_ms = 0;
		APP_LOG("Global command updated to default: '%s'\n", current_command);
		return;
	}
	else if (strcmp(cmd, "status") == 0)
	{
		display_synced_devices_status();
		APP_LOG("Current active command: '%s'\n", current_command);
		APP_LOG("Temp command active: %s\n", temp_command_active ? "true" : "false");
		if (temp_command_active)
		{
			int64_t now = k_uptime_get();
			APP_LOG("Time left: %lld ms\n", (long long)(temp_command_expiry_ms - now));
		}
	}
	else if (strcmp(cmd, "refresh") == 0)
	{
		APP_LOG("Forcing refresh of current command: '%s'\n", current_command);
		int err = send_command_to_synced_devices(pawr_adv, current_command);
		if (err)
		{
			APP_LOG("Failed to refresh command (err %d)\n", err);
		}
		else
		{
			APP_LOG("Command refreshed successfully\n");
		}
	}
	else if (strncmp(cmd, "[+]led,", 7) == 0)
	{

		const char *mac_str = cmd + 7;

		uint8_t mac[6];

		if (parse_mac(mac_str, mac) != 6)
		{
			APP_LOG("Invalid MAC format\n");
			return;
		}

		APP_LOG("LED command for MAC: %s\n", mac_str);

		display_synced_devices_status();

		// keep your existing timing logic
		temp_command_active = true;
		temp_command_expiry_ms = k_uptime_get() + TEMP_CMD_DURATION_MS;

		response_window_active = true;
		response_window_expiry_ms = k_uptime_get() + RESPONSE_WINDOW_TIMEOUT_MS;

		encode_led_command_with_mac(mac);

		APP_LOG("[+]LED_PROTO_READY\n");
	}
	else if (strncmp(cmd, "[+]splash,", 10) == 0)
	{
		const char *mac_str = cmd + 10;
		uint8_t mac[6];

		if (parse_mac(mac_str, mac) != 6)
		{
			APP_LOG("Invalid MAC format\n");
			return;
		}

		APP_LOG("SPLASH command for MAC: %s\n", mac_str);

		display_synced_devices_status();

		temp_command_active = true;
		temp_command_expiry_ms = k_uptime_get() + TEMP_CMD_DURATION_MS;

		response_window_active = true;
		response_window_expiry_ms = k_uptime_get() + RESPONSE_WINDOW_TIMEOUT_MS;

		encode_splash_command_with_mac(mac);
		APP_LOG("[+]SPLASH_PROTO_READY\n");
	}
	else if (strncmp(cmd, "[+]clear,", 9) == 0)
	{
		const char *mac_str = cmd + 9;
		uint8_t mac[6];

		if (parse_mac(mac_str, mac) != 6)
		{
			APP_LOG("Invalid MAC format\n");
			return;
		}

		APP_LOG("CLEAR command for MAC: %s\n", mac_str);

		display_synced_devices_status();

		temp_command_active = true;
		temp_command_expiry_ms = k_uptime_get() + TEMP_CMD_DURATION_MS;

		response_window_active = true;
		response_window_expiry_ms = k_uptime_get() + RESPONSE_WINDOW_TIMEOUT_MS;

		//  THIS IS THE MAIN CHANGE

		encode_clear_command_with_mac(mac);
		APP_LOG("[+]CLEAR_PROTO_READY\n");
	}
	else if (strncmp(cmd, "[+]ota,", 7) == 0)
	{
		char esl_mac_str[32];
		char ots_mac_str[32];

		uint8_t esl_mac[6];
		uint8_t ots_mac[6];

		if (sscanf(cmd,
				   "[+]ota,%31[^,],%31s",
				   esl_mac_str,
				   ots_mac_str) != 2)
		{
			APP_LOG("Invalid OTA format\n");
			APP_LOG("Expected: [+]ota,<esl_mac>,<ots_mac>\n");
			return;
		}

		if (parse_mac(esl_mac_str, esl_mac) != 6)
		{
			APP_LOG("Invalid ESL MAC\n");
			return;
		}

		if (parse_mac(ots_mac_str, ots_mac) != 6)
		{
			APP_LOG("Invalid OTS MAC\n");
			return;
		}

		APP_LOG("OTA command for ESL MAC: %s\n", esl_mac_str);
		APP_LOG("OTA command for OTS MAC: %s\n", ots_mac_str);

		display_synced_devices_status();

		// keep your existing timing logic
		temp_command_active = true;
		temp_command_expiry_ms = k_uptime_get() + TEMP_CMD_DURATION_MS;

		response_window_active = true;
		response_window_expiry_ms = k_uptime_get() + RESPONSE_WINDOW_TIMEOUT_MS;

		encode_ota_command_with_mac(esl_mac, ots_mac);

		APP_LOG("[+]OTA_PROTO_READY\n");
	}
	else if (strncmp(cmd, "[+]tel,", 7) == 0)
	{
		const char *mac_str = cmd + 7;
		uint8_t mac[6];

		if (parse_mac(mac_str, mac) != 6)
		{
			APP_LOG("Invalid MAC format\n");
			APP_LOG("Expected: [+]tel,<mac>\n");
			return;
		}

		APP_LOG("TEL command for MAC: %s\n", mac_str);

		display_synced_devices_status();

		temp_command_active = true;
		temp_command_expiry_ms = k_uptime_get() + TEMP_CMD_DURATION_MS;

		response_window_active = true;
		response_window_expiry_ms = k_uptime_get() + RESPONSE_WINDOW_TIMEOUT_MS;
		// snprintf(active_command_mac, sizeof(active_command_mac),
		// 		 "%s (random)", mac_str);
		strncpy(active_command_mac, mac_str, sizeof(active_command_mac) - 1);
		active_command_mac[sizeof(active_command_mac) - 1] = '\0';
		encode_tel_command_with_mac(mac);

		APP_LOG("[+]TEL_PROTO_READY\n");
	}
	else if (strncmp(cmd, "[+]active,", 10) == 0)
	{
		const char *mac = cmd + 10;

		prepare_active_command(mac);

		temp_command_active = true;
		temp_command_expiry_ms = k_uptime_get() + TEMP_CMD_DURATION_MS;

		response_window_active = true;
		response_window_expiry_ms = k_uptime_get() + RESPONSE_WINDOW_TIMEOUT_MS;

		APP_LOG("[+]ACTIVE READY\n");
	}
	else if (strcmp(cmd, "version") == 0 || strcmp(cmd, "ver") == 0)
	{
		APP_LOG("\n========== Firmware Version ==========\n");
		APP_LOG("Version : %s\n", APP_VERSION_STRING);
		// APP_LOG("Major   : %d\n", APP_VERSION_MAJOR);
		// APP_LOG("Minor   : %d\n", APP_VERSION_MINOR);
		// APP_LOG("Patch   : %d\n", APP_PATCHLEVEL);
		// APP_LOG("Tweak   : %d\n", APP_VERSION_TWEAK);
		APP_LOG("======================================\n");
	}
	else if (strcmp(cmd, "help") == 0)
	{
		APP_LOG("\nAvailable commands:\n");
		APP_LOG("  <number>         - Set join command (e.g., '1234' sends [+]join,1234 in burst)\n");
		APP_LOG("  [+]join,<esl_mac>,<ots_mac> - Set join command (burst for a few seconds)\n");
		APP_LOG("  [+]led,<esl_mac> - Set LED command (burst for a few seconds)\n");
		APP_LOG("  [+]ota,<esl_mac>,<ots_mac> - Set OTA command (burst for a few seconds)\n");
		APP_LOG("  [+]tel,<mac> - Set TEL command (burst for a few seconds)\n");
		APP_LOG("  join,<param>     - Auto-format join command (burst)\n");
		APP_LOG("  test             - Reset to default join command [+]join,9999\n");
		APP_LOG("  status           - Show synced devices and current command\n");
		APP_LOG("  refresh          - Force send current command now\n");
		APP_LOG("  help             - Show this help message\n");
		APP_LOG("Examples:\n");
		APP_LOG("  1234             - Send [+]join,1234 for a few seconds then revert\n");
		APP_LOG("  [+]join,1234     - Same as above\n");
		APP_LOG("  join,9999        - Same as above\n");
		APP_LOG("  ver              - shows firmware version\n");
		APP_LOG("Current command: '%s'\n\n", current_command);
	}
	else if (strlen(cmd) > 0)
	{
		bool is_number = true;
		for (int i = 0; i < strlen(cmd); i++)
		{
			if (cmd[i] < '0' || cmd[i] > '9')
			{
				is_number = false;
				break;
			}
		}

		if (is_number && strlen(cmd) > 0)
		{
			int join_param = atoi(cmd);
			char full_cmd[64];

			snprintf(full_cmd, sizeof(full_cmd), "[+]join,%d", join_param);
			APP_LOG("Numeric shortcut detected - join parameter: %d\n", join_param);
			APP_LOG("Formatted command: %s\n", full_cmd);

			// Activate temporary join command for a few seconds
			temp_command_active = true;
			temp_command_expiry_ms = k_uptime_get() + TEMP_CMD_DURATION_MS;

			display_synced_devices_status();

			int err = send_command_to_synced_devices(pawr_adv, full_cmd);
			if (err)
			{
				APP_LOG("ERROR: Failed to send join command to devices (err %d)\n", err);
			}
			else
			{
				APP_LOG("SUCCESS: Join command sent to all synced devices (burst mode)\n");
				APP_LOG("Temporary command active for %d ms\n", TEMP_CMD_DURATION_MS);
			}
		}
		else if (strcmp(cmd, "logs on") == 0)
		{
			logs_enabled = true;
			APP_LOG("Logs enabled\n");
		}
		else if (strcmp(cmd, "logs off") == 0)
		{
			logs_enabled = false;
			APP_LOG("Logs disabled\n");
		}
		else if (strcmp(cmd, "mcumgr") == 0)
		{
			uint8_t flag = 1;

			nvs_write(&fs,
					  NVS_ID_MCUMGR_MODE,
					  &flag,
					  sizeof(flag));
			sys_reboot(SYS_REBOOT_COLD);
		}
		else
		{
			APP_LOG("WARNING: Unknown command: '%s'\n", cmd);
			APP_LOG("Use 'help' for available commands\n");
			APP_LOG("Quick usage: Type a number (e.g., '1234') to send [+]join,1234 in burst\n");
		}
	}

	APP_LOG("CMD: '%s'\n", cmd);
}

void join_command_thread(void *pawr_adv_ptr, void *unused1, void *unused2)
{
	struct bt_le_ext_adv *pawr_adv = (struct bt_le_ext_adv *)pawr_adv_ptr;
	char cmd_buf[CMD_BUF_SIZE];

	APP_LOG("=== Command Processing Thread Started ===\n");
	APP_LOG("Ready to receive commands via UART\n");
	APP_LOG("Default command: %s\n", current_command);
	APP_LOG("Quick commands:\n");
	APP_LOG("  1234             - Send join command with parameter 1234 (burst)\n");
	APP_LOG("  join,1234        - Send join command with parameter 1234 (burst)\n");
	APP_LOG("  [+]tel,AA:BB:CC:DD:EE:FF - Send TEL command for one device\n");
	APP_LOG("  test             - Reset to default join command [+]join,9999\n");
	APP_LOG("  status           - Show synced devices and current command\n");
	APP_LOG("  refresh          - Force send current command now\n");
	APP_LOG("  help             - Show all commands\n");
	APP_LOG("Type command and press ENTER:\n");
	APP_LOG(">>> \n");

	while (1)
	{
		char *input = console_getline();
		if (input && strlen(input) > 0)
		{
			strncpy(cmd_buf, input, sizeof(cmd_buf) - 1);
			cmd_buf[sizeof(cmd_buf) - 1] = '\0';
			APP_LOG("\nUART: Command received: '%s'\n", cmd_buf);
			process_command(pawr_adv, cmd_buf);
			APP_LOG(">>> ");
		}
		k_sleep(K_MSEC(1));
	}
}

// Update current_command if temporary join has expired
static void update_temp_command_state(void)
{
	if (!temp_command_active)
	{
		proto_len = 0; // Clear proto buffer when not active
		proto_command_active = false;
		return;
	}

	int64_t now = k_uptime_get();
	if (now >= temp_command_expiry_ms)
	{
		APP_LOG("Temporary join command duration expired. Reverting to default.\n");
		strncpy(current_command, default_command, CMD_BUF_SIZE - 1);
		current_command[CMD_BUF_SIZE - 1] = '\0';
		temp_command_active = false;
		temp_command_expiry_ms = 0;
		proto_len = 0;
		proto_command_active = false;
		active_command_mac[0] = '\0';
		APP_LOG("Current command reverted to: '%s'\n", current_command);
	}
}

static void update_response_window_state(void)
{
	if (!response_window_active)
	{
		return;
	}

	int64_t now = k_uptime_get();
	if (now >= response_window_expiry_ms)
	{
		response_window_active = false;
		APP_LOG("Response window expired\n");
	}
}
static uint8_t current_response_subevent = 0;
static void request_cb(struct bt_le_ext_adv *adv,
					   const struct bt_le_per_adv_data_request *request)
{
	if (atomic_get(&onboarding_busy))
	{
		update_temp_command_state();
		update_response_window_state();

		char cmd_local[CMD_BUF_SIZE];
		strncpy(cmd_local, current_command, CMD_BUF_SIZE - 1);
		cmd_local[CMD_BUF_SIZE - 1] = '\0';
		size_t cmd_len = strlen(cmd_local);

		for (size_t i = 0; i < NUM_SUBEVENTS; i++)
		{
			struct net_buf_simple *buf = &bufs[i];
			memset(buf->data, 0, PACKET_SIZE);

			if (proto_command_active && proto_len > 0)
			{
				size_t copy_len = MIN(proto_len, PACKET_SIZE);
				memcpy(buf->data, proto_buf, copy_len);
				buf->len = copy_len;
			}
			else
			{
				size_t len = MIN(cmd_len, PACKET_SIZE - 1);
				memcpy(buf->data, cmd_local, len);
				buf->data[len] = '\0';
				buf->len = len + 1;
			}

			subevent_data_params[i].subevent = i;
			subevent_data_params[i].response_slot_start = 0;
			subevent_data_params[i].response_slot_count = 0; // still no responses while onboarding
			subevent_data_params[i].data = buf;
		}

		bt_le_per_adv_set_subevent_data(adv, NUM_SUBEVENTS, subevent_data_params);
		return;
	}
	int err;
	uint8_t to_send;
	struct net_buf_simple *buf;

	// Handle temporary command expiry
	update_temp_command_state();
	update_response_window_state();
	// APP_LOG("REQUEST_CB: temp=%d proto=%d current='%s'\n",
	// 		temp_command_active,
	// 		proto_command_active,
	// 		current_command);

	// Local copy of command
	char cmd_local[CMD_BUF_SIZE];
	strncpy(cmd_local, current_command, CMD_BUF_SIZE - 1);
	cmd_local[CMD_BUF_SIZE - 1] = '\0';

	size_t cmd_len = strlen(cmd_local);

	to_send = MIN(request->count, ARRAY_SIZE(subevent_data_params));

	for (size_t i = 0; i < to_send; i++)
	{
		uint8_t subevent =
			(request->start + i) % per_adv_params.num_subevents;

		buf = &bufs[i];

		memset(buf->data, 0, PACKET_SIZE);

		if (proto_command_active && proto_len > 0)
		{
			// APP_LOG("TX PROTO len=%d\n", proto_len);
			size_t copy_len = MIN(proto_len, PACKET_SIZE);

			memcpy(buf->data, proto_buf, copy_len);
			//  APP_LOG("Sending proto len: %d\n", proto_len);
			buf->len = copy_len;
		}
		else
		{

			const char *msg;

			if (temp_command_active)
			{
				msg = active_cmd;
			}
			else
			{
				msg = "CHECK_DEVICE";
			}

			// APP_LOG("TX TEXT: '%s'\n", msg);
			size_t len = strlen(msg);

			memcpy(buf->data, msg, len);
			buf->len = len;
			// APP_LOG(">>> Sending CHECK_DEVICE\n");
		}

		subevent_data_params[i].subevent = subevent;
		subevent_data_params[i].response_slot_start = 0;
		if (proto_command_active && proto_len > 0)
		{
			subevent_data_params[i].response_slot_count = NUM_RSP_SLOTS;
		}
		else if (subevent == current_response_subevent ||
				 subevent == ((current_response_subevent + 1) % NUM_SUBEVENTS))
		{
			subevent_data_params[i].response_slot_count = NUM_RSP_SLOTS;
		}
		else
		{
			subevent_data_params[i].response_slot_count = 0;
		}
		subevent_data_params[i].data = buf;
	}

	err = bt_le_per_adv_set_subevent_data(adv, to_send, subevent_data_params);
	if (err)
	{
		APP_LOG("Failed to set PAwR command data (err %d)\n", err);
		return;
	}

	//  Rotate ONLY once per full PAwR event
	if (request->start == 0)
	{
		current_response_subevent++;
		if (current_response_subevent >= NUM_SUBEVENTS)
		{
			current_response_subevent = 0;
		}

		// Debug (optional)
		APP_LOG("Active response subevent: %d\n", current_response_subevent);
	}
}
static bool print_ad_field(struct bt_data *data, void *user_data)
{
	ARG_UNUSED(user_data);

	APP_LOG("    0x%02X: ", data->type);
	for (size_t i = 0; i < data->data_len; i++)
	{
		APP_LOG("%02X", data->data[i]);
	}
	APP_LOG("\n");

	return true;
}

static struct bt_conn *default_conn;

static void response_cb(struct bt_le_ext_adv *adv,
						struct bt_le_per_adv_response_info *info,
						struct net_buf_simple *buf)
{
	ARG_UNUSED(adv);

	bool should_print = response_window_active;
	if (buf && buf->len > 0)
	{
		char tel_mac[24] = {0};
		char tel_meta[64] = {0};
		if (buf && buf->len > 3)
		{
			if (strncmp((char *)buf->data, "OK,", 3) == 0)
			{
				char mac[BT_ADDR_LE_STR_LEN] = {0};

				size_t copy_len = MIN(buf->len - 3, sizeof(mac) - 1);

				memcpy(mac,
					   buf->data + 3,
					   copy_len);

				mac[copy_len] = '\0';
				mac[buf->len - 3] = '\0';

				printk("RX MAC='%s'\n", mac);

				for (int i = 0; i < MAX_SYNCS; i++)
				{
					if (!synced_devices[i].active)
						continue;

					if (strncmp(mac, synced_devices[i].address, 17) == 0)
					{
						printk("MATCH FOUND!\n");

						synced_devices[i].last_response_time = k_uptime_get();
						synced_devices[i].state = PAWR_DEVICE_SYNCED;
						synced_devices[i].active_check_pending = false;
						synced_devices[i].active_check_retry = 0;

						APP_LOG("Recovered device %s\n", mac);
						return;
					}
				}

				printk("NO MATCH FOUND\n");
			}
		}
		if (decode_tel_response(buf->data,
								buf->len,
								tel_mac,
								sizeof(tel_mac),
								tel_meta,
								sizeof(tel_meta)))
		{
			if (strcmp(tel_mac, active_command_mac) != 0)
			{
				return;
			}
			char tin[20] = {0};
			char batt[20] = {0};
			char *comma = strchr(tel_meta, ',');

			if (comma)
			{
				size_t tin_len = (size_t)(comma - tel_meta);
				if (tin_len >= sizeof(tin))
				{
					tin_len = sizeof(tin) - 1;
				}

				memcpy(tin, tel_meta, tin_len);
				tin[tin_len] = '\0';

				strncpy(batt, comma + 1, sizeof(batt) - 1);
				batt[sizeof(batt) - 1] = '\0';

				APP_LOG("[+]res,%s,%s,%s\n", tel_mac, tin, batt);
			}
			else
			{
				APP_LOG("[+]res,%s,%s\n", tel_mac, tel_meta);
			}

			return;
		}

		if (should_print)
		{
			// APP_LOG("Response text: ");
			// for (size_t i = 0; i < buf->len; i++)
			// {
			// 	char c = buf->data[i];
			// 	if (c == '\0')
			// 	{
			// 		break;
			// 	}
			// 	if (c >= 0x20 && c <= 0x7E)
			// 	{
			// 		APP_LOG("%c", c);
			// 	}
			// }
			// APP_LOG("\n");
		}
		// APP_LOG("=== Device Response ===\n");
		// APP_LOG("From: subevent %d, slot %d\n", info->subevent, info->response_slot);
		// APP_LOG("Response length: %d bytes\n", buf->len);

		bool is_text = true;
		for (size_t i = 0; i < buf->len && i < 64; i++)
		{
			if (buf->data[i] < 0x20 &&
				buf->data[i] != 0x00 &&
				buf->data[i] != '\n' &&
				buf->data[i] != '\r')
			{
				is_text = false;
				break;
			}
		}

		char parsed_dev_id[16] = {0};

		if (is_text && buf->len < 128)
		{
			// APP_LOG("\n");

			// If response starts with "devid,", extract the ID
			if (buf->len > 6 && strncmp((char *)buf->data, "devid,", 6) == 0)
			{
				size_t id_len = buf->len - 6;
				if (id_len >= sizeof(parsed_dev_id))
				{
					id_len = sizeof(parsed_dev_id) - 1;
				}
				memcpy(parsed_dev_id, &buf->data[6], id_len);
				parsed_dev_id[id_len] = '\0';
				// APP_LOG("Parsed device ID from response: %s\n", parsed_dev_id);
			}
		}

		// Update slot by subevent/response_slot
		int idx = -1;
		for (int i = 0; i < MAX_SYNCS; i++)
		{
			if (synced_devices[i].active &&
				synced_devices[i].subevent == info->subevent &&
				synced_devices[i].response_slot == info->response_slot)
			{
				idx = i;
				synced_devices[i].last_response_time = k_uptime_get();

				// If we parsed an ID, store it in this slot

				// Only print debug for the device we sent a command to
				if (active_command_mac[0] != '\0' &&
					strcmp(synced_devices[idx].address, active_command_mac) == 0)
				{
					char dbg_mac[24] = {0};
					char dbg_meta[64] = {0};

					// try without offset first, then with +1
					bool decoded = decode_tel_response(buf->data, buf->len,
													   dbg_mac, sizeof(dbg_mac),
													   dbg_meta, sizeof(dbg_meta));
					if (!decoded && buf->len > 1)
					{
						decoded = decode_tel_response(buf->data + 1, buf->len - 1,
													  dbg_mac, sizeof(dbg_mac),
													  dbg_meta, sizeof(dbg_meta));
					}

					if (decoded)
					{
						char dbg_tin[20] = {0};
						char dbg_batt[20] = {0};
						char *comma = strchr(dbg_meta, ',');
						if (comma)
						{
							size_t tin_len = (size_t)(comma - dbg_meta);
							if (tin_len >= sizeof(dbg_tin))
								tin_len = sizeof(dbg_tin) - 1;
							memcpy(dbg_tin, dbg_meta, tin_len);
							dbg_tin[tin_len] = '\0';
							strncpy(dbg_batt, comma + 1, sizeof(dbg_batt) - 1);
							APP_LOG("[+]DEBUG MAC=%s TIN=%s BATT=%s\n", dbg_mac, dbg_tin, dbg_batt);
						}
						else
						{
							APP_LOG("[+]DEBUG MAC=%s META=%s\n", dbg_mac, dbg_meta);
						}
					}
					else
					{
						// decode failed - print raw as text skipping non-printable
						char text_buf[64] = {0};
						int ti = 0;
						for (size_t j = 0; j < buf->len && ti < 63; j++)
						{
							char c = buf->data[j];
							if (c >= 0x20 && c <= 0x7E)
								text_buf[ti++] = c;
						}
						text_buf[ti] = '\0';
						APP_LOG("[+]DEBUG RAW=%s\n", text_buf);
						APP_LOG("[+]DEBUG HINT: protobuf mismatch - fix command.options and regenerate\n");
					}
				}

				if (parsed_dev_id[0] != '\0')
				{
					// strncpy(synced_devices[i].device_id,
					// 		parsed_dev_id,
					// 		sizeof(synced_devices[i].device_id) - 1);
					// synced_devices[i].device_id[sizeof(synced_devices[i].device_id) - 1] = '\0';
					// synced_devices[i].has_device_id = true;
					bool first_time = !synced_devices[i].has_device_id; // was empty before?

					strncpy(synced_devices[i].device_id,
							parsed_dev_id,
							sizeof(synced_devices[i].device_id) - 1);
					synced_devices[i].device_id[sizeof(synced_devices[i].device_id) - 1] = '\0';
					synced_devices[i].has_device_id = true;
				}
				break;
			}
		}

		if (idx >= 0)
		{
			// APP_LOG("Updated slot %d (subevent %d, response_slot %d) for response\n",
			// 	   idx, info->subevent, info->response_slot);
			if (parsed_dev_id[0] != '\0')
			{
				// APP_LOG("[PAWR] mac=%s subevent=%d slot=%d\n",
				// 	   synced_devices[idx].address,
				// 	   info->subevent,
				// 	   info->response_slot);
			}
		}
		else
		{
			// APP_LOG("Response from unknown slot (subevent %d, response_slot %d)\n",
			// 		info->subevent, info->response_slot);
		}
		// APP_LOG("\n");

		// APP_LOG("==================\n");
	}
	else
	{
		APP_LOG("Empty response from subevent %d, slot %d\n",
				info->subevent, info->response_slot);
	}
}

static const struct bt_le_ext_adv_cb adv_cb = {
	.pawr_data_request = request_cb,
	.pawr_response = response_cb,
};

void connected_cb(struct bt_conn *conn, uint8_t err)
{
	APP_LOG("Connected (err 0x%02X)\n", err);

	__ASSERT(conn == default_conn, "Unexpected connected callback");

	if (err)
	{
		APP_LOG("Connection failed (err 0x%02X)\n", err);

		if (default_conn)
		{
			bt_conn_unref(default_conn);
			default_conn = NULL;
		}

		atomic_set(&onboarding_busy, 0);

		k_sem_give(&sem_connected); // failure path
		return;
	}

	// ✅ SUCCESS PATH (YOU MISSED THIS)
	k_sem_give(&sem_connected);
}

void disconnected_cb(struct bt_conn *conn, uint8_t reason)
{
	APP_LOG("Disconnected, reason 0x%02X %s\n", reason, bt_hci_err_to_str(reason));

	if (conn)
	{
		const bt_addr_le_t *dev_addr = bt_conn_get_dst(conn);
		if (dev_addr)
		{
			char addr_str[BT_ADDR_LE_STR_LEN] = {0};
			bt_addr_le_to_str(dev_addr, addr_str, sizeof(addr_str));

			for (int i = 0; i < MAX_SYNCS; i++)
			{
				if (synced_devices[i].active &&
					strcmp(synced_devices[i].address, addr_str) == 0)
				{
					APP_LOG("Device %s disconnected, keeping slot %d (subevent %d, slot %d)\n",
							addr_str,
							i,
							synced_devices[i].subevent,
							synced_devices[i].response_slot);
				}
			}
		}
	}

	if (default_conn)
	{
		bt_conn_unref(default_conn);
		default_conn = NULL;
	}

	/* release onboarding lock */
	last_onboard_time = k_uptime_get();
	atomic_set(&onboarding_busy, 0);

	k_sem_give(&sem_disconnected);
}

void remote_info_available_cb(struct bt_conn *conn, struct bt_conn_remote_info *remote_info)
{
	k_sem_give(&sem_connected);
}

BT_CONN_CB_DEFINE(conn_cb) = {
	.connected = connected_cb,
	.disconnected = disconnected_cb,
	.remote_info_available = remote_info_available_cb,
};

static bool data_cb(struct bt_data *data, void *user_data)
{
	char *name = user_data;
	uint8_t len;

	switch (data->type)
	{
	case BT_DATA_NAME_SHORTENED:
	case BT_DATA_NAME_COMPLETE:
		len = MIN(data->data_len, NAME_LEN - 1);
		memcpy(name, data->data, len);
		name[len] = '\0';
		return false;
	default:
		return true;
	}
}

static void device_found(const bt_addr_le_t *addr, int8_t rssi, uint8_t type,
						 struct net_buf_simple *ad)
{
	char name[NAME_LEN];
	int err;

	/* Prevent multiple onboarding at once */
	if (atomic_get(&onboarding_busy))
		return;

	if (default_conn)
		return;

	if (type != BT_GAP_ADV_TYPE_ADV_IND &&
		type != BT_GAP_ADV_TYPE_ADV_DIRECT_IND)
		return;

	// if (rssi < -70)
	// 	return;

	memset(name, 0, sizeof(name));
	bt_data_parse(ad, data_cb, name);

	if (strcmp(name, "PAwR sync sample"))
		return;

	/* Controller cooldown protection */
	// if (k_uptime_get() - last_onboard_time < ONBOARDING_COOLDOWN_MS)
	// 	return;

	if (!atomic_cas(&onboarding_busy, 0, 1))
	{
		return;
	}

	if (bt_le_scan_stop())
	{
		atomic_set(&onboarding_busy, 0);
		return;
	}

	/* Allow controller to settle */
	// k_sleep(K_MSEC(200));

	err = bt_conn_le_create(addr,
							BT_CONN_LE_CREATE_CONN,
							BT_LE_CONN_PARAM_DEFAULT,
							&default_conn);

	if (err)
	{
		APP_LOG("Create conn failed (%u)\n", err);
		atomic_set(&onboarding_busy, 0);
	}
}

static uint8_t discover_func(struct bt_conn *conn, const struct bt_gatt_attr *attr,
							 struct bt_gatt_discover_params *params)
{
	struct bt_gatt_chrc *chrc;
	char str[BT_UUID_STR_LEN];

	APP_LOG("Discovery: attr %p\n", attr);

	if (!attr)
	{
		APP_LOG("Characteristic not found");
		k_sem_give(&sem_discovered);
		return BT_GATT_ITER_STOP;
	}

	chrc = (struct bt_gatt_chrc *)attr->user_data;
	bt_uuid_to_str(chrc->uuid, str, sizeof(str));
	APP_LOG("UUID %s\n", str);

	if (!bt_uuid_cmp(chrc->uuid, &pawr_char_uuid.uuid))
	{
		pawr_attr_handle = chrc->value_handle;
		APP_LOG("Characteristic handle: %d\n", pawr_attr_handle);
		k_sem_give(&sem_discovered);
	}

	return BT_GATT_ITER_STOP;
}

static void write_func(struct bt_conn *conn, uint8_t err, struct bt_gatt_write_params *params)
{
	if (err)
	{
		APP_LOG("Write failed (err %d)\n", err);
		return;
	}

	k_sem_give(&sem_written);
}

void init_bufs(void)
{
	for (size_t i = 0; i < ARRAY_SIZE(backing_store); i++)
	{
		backing_store[i][0] = ARRAY_SIZE(backing_store[i]) - 1;
		backing_store[i][1] = BT_DATA_MANUFACTURER_DATA;
		backing_store[i][2] = 0x59; /* Nordic */
		backing_store[i][3] = 0x00;

		net_buf_simple_init_with_data(&bufs[i],
									  &backing_store[i],
									  ARRAY_SIZE(backing_store[i]));
	}
}

// Function to display synced devices status
void display_synced_devices_status(void)
{
	int active_count = 0;

	for (int i = 0; i < MAX_SYNCS; i++)
	{
		if (synced_devices[i].active)
		{
			active_count++;
		}
		else
		{
			if (k_uptime_get() - synced_devices[i].active_check_time > 3000)
			{
				clear_slot(i);
			}
		}
	}

	APP_LOG("Synced devices: %d\n", active_count);
}
void cleanup_inactive_slots(void)
{

	for (int i = 0; i < MAX_SYNCS; i++)
	{

		// 1) Active but timed out? -> treat as disconnected and clear slot
		if (synced_devices[i].active && !is_slot_responsive(i))
		{
			if (!synced_devices[i].active_check_pending)
			{
				char cmd[64];

				snprintf(cmd,
						 sizeof(cmd),
						 "ACTIVE,%s",

						 synced_devices[i].address);

				strncpy(current_command, cmd, CMD_BUF_SIZE - 1);
				current_command[CMD_BUF_SIZE - 1] = '\0';

				temp_command_active = true;
				temp_command_expiry_ms = k_uptime_get() + 10000;

				response_window_active = true;
				response_window_expiry_ms = k_uptime_get() + 10000;

				synced_devices[i].active_check_pending = true;
				synced_devices[i].active_check_retry = 0;
				synced_devices[i].active_check_time = k_uptime_get();

				APP_LOG("Sent ACTIVE check to %s\n",
						synced_devices[i].address);
			}
			else
			{
				APP_LOG("ACTIVE pending: elapsed=%lld\n",
						k_uptime_get() - synced_devices[i].active_check_time);
				APP_LOG("RESPONSE_WINDOW_TIMEOUT_MS=%d\n",
						RESPONSE_WINDOW_TIMEOUT_MS);
				if (k_uptime_get() - synced_devices[i].active_check_time >
					RESPONSE_WINDOW_TIMEOUT_MS)
				{
					APP_LOG("ACTIVE timeout -> clearing slot %d\n", i);

					clear_slot(i);
				}
			}
			APP_LOG("slot=%d active=%d pending=%d retry=%d\n",
					i,
					synced_devices[i].active,
					synced_devices[i].active_check_pending,
					synced_devices[i].active_check_retry);
			continue;
		}

		// 2) Already inactive but still has stale address/device_id -> wipe it
		if (!synced_devices[i].active &&
			synced_devices[i].address[0] != '\0')
		{
			APP_LOG("Cleaning up inactive slot %d\n", i);
			memset(synced_devices[i].address, 0,
				   sizeof(synced_devices[i].address));
			memset(synced_devices[i].device_id, 0,
				   sizeof(synced_devices[i].device_id));
			synced_devices[i].has_device_id = false;
			synced_devices[i].subevent = INVALID_SLOT;
			synced_devices[i].response_slot = INVALID_SLOT;
		}
	}
}

void reset_synchronization(void)
{
	APP_LOG("Resetting synchronization state...\n");
	for (int i = 0; i < MAX_SYNCS; i++)
	{
		if (!synced_devices[i].active)
		{
			synced_devices[i].address[0] = '\0';
			synced_devices[i].device_id[0] = '\0';
			synced_devices[i].has_device_id = false;
			synced_devices[i].subevent = INVALID_SLOT;
			synced_devices[i].response_slot = INVALID_SLOT;
		}
	}
	num_synced = 0;
	APP_LOG("Synchronization state reset.\n");
}

void restart_advertising(void)
{

	int err = bt_le_per_adv_start(pawr_adv);
	if (err)
	{
		APP_LOG("Failed to restart periodic advertising: %d\n", err);
	}
	else
	{
		APP_LOG("Periodic advertising restarted\n");
	}

	err = bt_le_ext_adv_start(pawr_adv, BT_LE_EXT_ADV_START_DEFAULT);
	if (err)
	{
		APP_LOG("Failed to restart extended advertising: %d\n", err);
	}
	else
	{
		APP_LOG("Extended advertising restartedr\n");
	}
}
#define MAINT_THREAD_STACK_SIZE 2048
#define MAINT_THREAD_PRIORITY 6
K_THREAD_STACK_DEFINE(maint_thread_stack, MAINT_THREAD_STACK_SIZE);
static struct k_thread maint_thread_data;
void maint_thread(void *p1, void *p2, void *p3)
{
	ARG_UNUSED(p1);
	ARG_UNUSED(p2);
	ARG_UNUSED(p3);

	APP_LOG("Maintenance thread started (will cleanup inactive slots)\n");

	while (1)
	{
		k_sleep(K_SECONDS(5));
		cleanup_inactive_slots();
	}
}

int main(void)
{
	APP_LOG("APPLICATION STARTED 2\n");
	int err;
	static struct bt_gatt_discover_params discover_params;
	static struct bt_gatt_write_params write_params;
	static struct pawr_timing sync_config;

	init_bufs();
	// NVS initialization
	err = nvs_init_app();
	if (err)
	{
		APP_LOG("NVS initialization failed (err %d)\n", err);
		return 0;
	}
	uart_dev = DEVICE_DT_GET(DT_NODELABEL(uart20));
	if (!device_is_ready(uart_dev))
	{
		APP_LOG("UART device not ready!\n");
		return 0;
	}
	for (int i = 0; i < MAX_SYNCS; i++)
	{
		memset(&synced_devices[i], 0, sizeof(synced_devices[i]));

		synced_devices[i].subevent = INVALID_SLOT;
		synced_devices[i].response_slot = INVALID_SLOT;
		synced_devices[i].state = PAWR_DEVICE_DISCONNECTED;
	}

	uint8_t flag = 0;

	ssize_t len = nvs_read(&fs,
						   NVS_ID_MCUMGR_MODE,
						   &flag,
						   sizeof(flag));

	if (len > 0 && flag == 1)
	{
		printk("MCUmgr boot\n");

		flag = 0;
		nvs_write(&fs,
				  NVS_ID_MCUMGR_MODE,
				  &flag,
				  sizeof(flag));

		/* Skip console_getline_init() */
	}
	else
	{
		console_getline_init();
	}
	APP_LOG("UART configured for command input\n");
	APP_LOG("System initialized - UART ready for commands\n");
	APP_LOG("Starting Periodic Advertising Demo\n");

	err = bt_enable(NULL);
	if (err)
	{
		APP_LOG("Bluetooth init failed (err %d)\n", err);
		return 0;
	}

	err = bt_le_ext_adv_create(BT_LE_EXT_ADV_NCONN, &adv_cb, &pawr_adv);
	if (err)
	{
		APP_LOG("Failed to create advertising set (err %d)\n", err);
		return 0;
	}

	err = bt_le_per_adv_set_param(pawr_adv, &per_adv_params);
	if (err)
	{
		APP_LOG("Failed to set periodic advertising parameters (err %d)\n", err);
		return 0;
	}

	APP_LOG("Start Periodic Advertising\n");
	err = bt_le_per_adv_start(pawr_adv);
	if (err)
	{
		APP_LOG("Failed to enable periodic advertising (err %d)\n", err);
		return 0;
	}

	APP_LOG("Start Extended Advertising\n");
	err = bt_le_ext_adv_start(pawr_adv, BT_LE_EXT_ADV_START_DEFAULT);
	if (err)
	{
		APP_LOG("Failed to start extended advertising (err %d)\n", err);
		return 0;
	}

	struct k_thread join_thread_data;
	k_thread_create(&join_thread_data,
					join_thread_stack,
					JOIN_THREAD_STACK_SIZE,
					join_command_thread,
					pawr_adv, NULL, NULL,
					JOIN_THREAD_PRIORITY, 0, K_NO_WAIT);

	k_thread_create(&maint_thread_data,
					maint_thread_stack,
					MAINT_THREAD_STACK_SIZE,
					maint_thread,
					NULL, NULL, NULL,
					MAINT_THREAD_PRIORITY, 0, K_NO_WAIT);

	while (num_synced < MAX_SYNCS)
	{
		err = 0;

		if (num_synced >= MAX_SYNCS)
		{
			k_sleep(K_SECONDS(1));
			continue;
		}

		if (!default_conn)
		{
			err = bt_le_scan_start(BT_LE_SCAN_PASSIVE_CONTINUOUS, device_found);
		}
		if (err && err != -EALREADY)
		{
			APP_LOG("Scanning failed to start (err %d)\n", err);
			k_sleep(K_SECONDS(1));
			continue;
		}

		if (k_sem_take(&sem_connected, K_SECONDS(6)) != 0)
		{
			APP_LOG("Connection wait timeout → recovering...\n");

			//  1. Reset connection state
			if (default_conn)
			{
				bt_conn_unref(default_conn);
				default_conn = NULL;
			}

			//  2. Reset onboarding state
			atomic_set(&onboarding_busy, 0);

			//  3. Stop scan (important reset)
			bt_le_scan_stop();

			k_sleep(K_MSEC(200));

			//  5. Small recovery delay
			k_sleep(K_MSEC(500));

			continue;
		}
		if (!default_conn)
		{
			APP_LOG("Connection failed, retrying...\n");
			atomic_set(&onboarding_busy, 0);
			default_conn = NULL;

			k_sleep(K_MSEC(200));
			continue;
		}
		k_sleep(K_MSEC(300));
		if (!default_conn)
			goto disconnect;
		err = bt_le_per_adv_set_info_transfer(pawr_adv, default_conn, 0);
		if (err)
		{
			APP_LOG("Failed to send PAST (err %d)\n", err);
			goto disconnect;
		}

		APP_LOG("PAST sent\n");
		// k_sleep(K_MSEC(500));
		k_sleep(K_MSEC(3000));
		memset(&discover_params, 0, sizeof(discover_params));
		discover_params.uuid = &pawr_char_uuid.uuid;
		discover_params.func = discover_func;
		discover_params.start_handle = BT_ATT_FIRST_ATTRIBUTE_HANDLE;
		discover_params.end_handle = BT_ATT_LAST_ATTRIBUTE_HANDLE;
		discover_params.type = BT_GATT_DISCOVER_CHARACTERISTIC;

		if (!default_conn)
			goto disconnect;
		pawr_attr_handle = 0;
		err = bt_gatt_discover(default_conn, &discover_params);
		if (err)
		{
			APP_LOG("Discovery failed (err %d)\n", err);
			goto disconnect;
		}

		APP_LOG("Discovery started\n");

		err = k_sem_take(&sem_discovered, K_SECONDS(10));
		if (err)
		{
			APP_LOG("Timed out during GATT discovery\n");
			goto disconnect;
		}
		if (pawr_attr_handle == 0)
		{
			APP_LOG("Characteristic not found");
			goto disconnect;
		}

		char addr_str[BT_ADDR_LE_STR_LEN] = {0};
		if (default_conn)
		{
			const bt_addr_le_t *dev_addr = bt_conn_get_dst(default_conn);
			if (dev_addr)
			{
				bt_addr_le_to_str(dev_addr, addr_str, sizeof(addr_str));
			}
		}

		uint8_t subevent = 0, response_slot = 0;
		int slot_idx = find_or_assign_slot(addr_str, &subevent, &response_slot);
		if (slot_idx < 0)
		{
			APP_LOG("No slot available for device %s\n", addr_str);
			goto disconnect;
		}

		sync_config.subevent = subevent;
		sync_config.response_slot = response_slot;
		memset(&write_params, 0, sizeof(write_params));
		write_params.func = write_func;
		write_params.handle = pawr_attr_handle;
		write_params.offset = 0;
		write_params.data = &sync_config;
		write_params.length = sizeof(sync_config);

		if (!default_conn)
			goto disconnect;
		err = bt_gatt_write(default_conn, &write_params);
		if (err)
		{
			APP_LOG("Write failed (err %d)\n", err);
			clear_slot(slot_idx);
			goto disconnect;
		}

		APP_LOG("Write started\n");

		err = k_sem_take(&sem_written, K_SECONDS(10));
		if (err)
		{
			APP_LOG("Timed out during GATT write\n");
			clear_slot(slot_idx);
			goto disconnect;
		}
		k_sleep(K_MSEC(2000));
		// Mark initial "alive" timestamp for this slot
		// synced_devices[slot_idx].last_update_time = k_uptime_get();
		synced_devices[slot_idx].last_sync_time = k_uptime_get();
		synced_devices[slot_idx].last_response_time = 0;

		APP_LOG("PAwR config written to sync %d (subevent %d, slot %d), disconnecting\n",
				slot_idx, sync_config.subevent, sync_config.response_slot);

	disconnect:
		k_sleep(K_MSEC(per_adv_params.interval_max * 2));

		if (default_conn)
		{
			k_sleep(K_MSEC(4000));
			err = bt_conn_disconnect(default_conn,
									 BT_HCI_ERR_REMOTE_USER_TERM_CONN);
			if (err)
			{
				APP_LOG("Disconnect failed (err %d)\n", err);
				atomic_set(&onboarding_busy, 0);
				k_sleep(K_MSEC(200));
				continue;
			}
		}

		if (k_sem_take(&sem_disconnected, K_SECONDS(5)))
		{
			APP_LOG("Disconnect timeout\n");

			if (default_conn)
			{
				bt_conn_unref(default_conn);
				default_conn = NULL;
			}

			continue;
		}
		// k_sleep(K_MSEC(400));
		k_sleep(K_MSEC(1200));
	}

	APP_LOG("Maximum number of syncs onboarded: %d devices\n", num_synced);
	APP_LOG("System ready - listening for commands via UART\n");
	APP_LOG("Command format: number OR join,<param> OR [+]join,<param>\n");
	APP_LOG("Example: 1234  (sends [+]join,1234 for a few seconds)\n");

	APP_LOG("\n=== Synced Devices Status ===\n");
	for (int i = 0; i < MAX_SYNCS; i++)
	{
		if (synced_devices[i].active)
		{
			const char *id_str = synced_devices[i].has_device_id ? synced_devices[i].device_id : "unknown";

			APP_LOG("Device %d: dev_id %s, subevent %d, response_slot %d, addr %s\n",
					i,
					id_str,
					synced_devices[i].subevent,
					synced_devices[i].response_slot,
					synced_devices[i].address);
		}
	}
	APP_LOG("============================\n\n");

	while (1)
	{
		k_sleep(K_SECONDS(5));
		static int status_counter = 0;
		if (++status_counter >= 12)
		{
			status_counter = 0;
			APP_LOG("System status: %d synced devices active, waiting for commands...\n",
					num_synced);
			APP_LOG("Current command: %s | temp_active: %s\n",
					current_command,
					temp_command_active ? "true" : "false");
		}
		cleanup_inactive_slots();
	}

	return 0;
}
