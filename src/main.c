

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
#include <zephyr/bluetooth/att.h>
#include <zephyr/bluetooth/bluetooth.h>
#include <zephyr/bluetooth/conn.h>
#include <zephyr/bluetooth/gatt.h>
#include <zephyr/bluetooth/hci.h>
#include <zephyr/drivers/uart.h>
#include <zephyr/console/console.h>
#include <zephyr/kernel.h>
#include <zephyr/sys/__assert.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>

#define ONBOARDING_COOLDOWN_MS 3000

static atomic_t onboarding_busy = ATOMIC_INIT(0);
static int64_t last_onboard_time = 0;

#define NUM_RSP_SLOTS 5
#define NUM_SUBEVENTS 8
#define PACKET_SIZE 30
#define NAME_LEN 30
#define UART_BUF_SIZE 256
#define CMD_BUF_SIZE 128

#define MAX_SYNCS (NUM_SUBEVENTS * NUM_RSP_SLOTS)
#define SLOT_TIMEOUT_MS 45000 // 90 seconds
#define INVALID_SLOT 0xFF
#define ADDR_STR_LEN BT_ADDR_LE_STR_LEN // full bt_addr_le_to_str() string

static K_SEM_DEFINE(sem_connected, 0, 1);
static K_SEM_DEFINE(sem_discovered, 0, 1);
static K_SEM_DEFINE(sem_written, 0, 1);
static K_SEM_DEFINE(sem_disconnected, 0, 1);

static struct bt_uuid_128 pawr_char_uuid =
	BT_UUID_INIT_128(BT_UUID_128_ENCODE(0x12345678, 0x1234, 0x5678, 0x1234, 0x56789abcdef1));
static uint16_t pawr_attr_handle;

static const struct bt_le_per_adv_param per_adv_params = {
	.interval_min = 0x400, // 625 ms
	.interval_max = 0x400, // 937.5 ms
	.options = 0,
	.num_subevents = NUM_SUBEVENTS,
	.subevent_interval = 0x50,	   // 31.25 ms
	.response_slot_delay = 0x10,   // 6.25 ms
	.response_slot_spacing = 0x40, // 50 ms
	.num_response_slots = NUM_RSP_SLOTS,
};

#define JOIN_THREAD_STACK_SIZE 1024
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
static bool temp_command_active = false;
static int64_t temp_command_expiry_ms = 0;

// Structure to store synced device information
struct synced_device
{
	bool active;
	uint8_t subevent;
	uint8_t response_slot;

	char address[ADDR_STR_LEN]; // BT addr as string (from onboarding)
	char device_id[16];			// ID from "devid,XXXX"
	bool has_device_id;

	int64_t last_update_time;
	int64_t last_response_time;
	int64_t last_sync_time;
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
		printk("Slot %d lost device (no PAwR response for %lld ms)\n",
			   slot_index, diff);
		return false;
	}

	return true;
}

// Clear a slot completely (only for errors/timeouts, not normal disconnect)
static void clear_slot(int slot_index)
{
	if (synced_devices[slot_index].active)
	{
		printk("[+]DISCONNECTED,%s\n",
			   synced_devices[slot_index].address);
		if (num_synced > 0)
		{
			num_synced--;
		}
	}

	synced_devices[slot_index].active = false;
	synced_devices[slot_index].subevent = INVALID_SLOT;
	synced_devices[slot_index].response_slot = INVALID_SLOT;

	memset(synced_devices[slot_index].address, 0, sizeof(synced_devices[slot_index].address));
	memset(synced_devices[slot_index].device_id, 0, sizeof(synced_devices[slot_index].device_id));
	synced_devices[slot_index].has_device_id = false;

	synced_devices[slot_index].last_update_time = 0;

	printk("Cleared slot %d\n", slot_index);
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

	synced_devices[slot_index].active = false;
	synced_devices[slot_index].subevent = INVALID_SLOT;
	synced_devices[slot_index].response_slot = INVALID_SLOT;

	memset(synced_devices[slot_index].address, 0, sizeof(synced_devices[slot_index].address));
	memset(synced_devices[slot_index].device_id, 0, sizeof(synced_devices[slot_index].device_id));
	synced_devices[slot_index].has_device_id = false;
	synced_devices[slot_index].last_update_time = 0;

	printk("Cleared slot %d (silent)\n", slot_index);
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

				printk("Reusing slot %d for device %s (subevent %d, response_slot %d)\n",
					   i, address, *subevent, *response_slot);
				return i;
			}
			else
			{
				printk("Clearing unresponsive slot %d for device %s\n", i, address);
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
			synced_devices[i].subevent = *subevent;
			synced_devices[i].response_slot = *response_slot;
			synced_devices[i].last_update_time = k_uptime_get();

			// device_id not known yet at onboarding
			synced_devices[i].device_id[0] = '\0';
			synced_devices[i].has_device_id = false;

			num_synced++;

			printk("Assigned new slot %d for device %s (subevent %d, response_slot %d)\n",
				   i, address, *subevent, *response_slot);
			return i;
		}
	}

	printk("No available slot for device %s\n", address);
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
				printk("\nUART: Command received: '%s'\n", buffer);
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

	printk("Updating command to: '%s'\n", command);

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
		printk("No synced devices available - but command updated for future requests\n");
		printk("Current command will be sent when devices sync or on next PAwR request\n");
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
	printk("Command '%s' sent immediately to %d synced devices\n", command, active_devices);
	printk("Current active command: '%s'\n", current_command);

	return 0;
}

// Function to parse and handle commands
static void process_command(struct bt_le_ext_adv *pawr_adv, const char *cmd)
{
	printk("=== PROCESSING COMMAND ===\n");
	printk("Command received: '%s' (length: %d)\n", cmd, (int)strlen(cmd));
	printk("Current command before: '%s'\n", current_command);

	if (strncmp(cmd, "[+]join,", 8) == 0)
	{
		const char *param = cmd + 8;
		int join_param = atoi(param);

		printk("Join command detected with parameter: %d\n", join_param);
		display_synced_devices_status();

		// Activate temporary join command for a few seconds
		temp_command_active = true;
		temp_command_expiry_ms = k_uptime_get() + TEMP_CMD_DURATION_MS;

		int err = send_command_to_synced_devices(pawr_adv, cmd);
		if (err)
		{
			printk("ERROR: Failed to send join command to devices (err %d)\n", err);
		}
		else
		{
			printk("SUCCESS: Join command sent to all synced devices (burst mode)\n");
			printk("Temporary command active for %d ms\n", TEMP_CMD_DURATION_MS);
		}
	}
	else if (strncmp(cmd, "join,", 5) == 0)
	{
		const char *param = cmd + 5;
		int join_param = atoi(param);
		char full_cmd[64];

		snprintf(full_cmd, sizeof(full_cmd), "[+]join,%d", join_param);
		printk("Join command detected (auto-format) with parameter: %d\n", join_param);
		printk("Formatted command: %s\n", full_cmd);

		// Activate temporary join command for a few seconds
		temp_command_active = true;
		temp_command_expiry_ms = k_uptime_get() + TEMP_CMD_DURATION_MS;

		display_synced_devices_status();

		int err = send_command_to_synced_devices(pawr_adv, full_cmd);
		if (err)
		{
			printk("ERROR: Failed to send join command to devices (err %d)\n", err);
		}
		else
		{
			printk("SUCCESS: Join command sent to all synced devices (burst mode)\n");
			printk("Temporary command active for %d ms\n", TEMP_CMD_DURATION_MS);
		}
	}
	else if (strcmp(cmd, "test") == 0 || strcmp(cmd, "t") == 0)
	{
		printk("Resetting to default join command: %s\n", default_command);
		strncpy(current_command, default_command, CMD_BUF_SIZE - 1);
		current_command[CMD_BUF_SIZE - 1] = '\0';
		temp_command_active = false;
		temp_command_expiry_ms = 0;
		printk("Global command updated to default: '%s'\n", current_command);
		return;
	}
	else if (strcmp(cmd, "status") == 0)
	{
		display_synced_devices_status();
		printk("Current active command: '%s'\n", current_command);
		printk("Temp command active: %s\n", temp_command_active ? "true" : "false");
		if (temp_command_active)
		{
			int64_t now = k_uptime_get();
			printk("Time left: %lld ms\n", (long long)(temp_command_expiry_ms - now));
		}
	}
	else if (strcmp(cmd, "refresh") == 0)
	{
		printk("Forcing refresh of current command: '%s'\n", current_command);
		int err = send_command_to_synced_devices(pawr_adv, current_command);
		if (err)
		{
			printk("Failed to refresh command (err %d)\n", err);
		}
		else
		{
			printk("Command refreshed successfully\n");
		}
	}
	else if (strncmp(cmd, "[+]led,", 7) == 0)
	{

		const char *param = cmd + 7;

		printk("LED command detected with parameter: %s\n", param);
		display_synced_devices_status();

		// Activate temporary LED command for a few seconds
		temp_command_active = true;
		temp_command_expiry_ms = k_uptime_get() + TEMP_CMD_DURATION_MS;

		int err = send_command_to_synced_devices(pawr_adv, cmd);
		printk("[+]LED_COMMAND_SENT_SUCCESS\n");
	}

	else if (strcmp(cmd, "help") == 0)
	{
		printk("\nAvailable commands:\n");
		printk("  <number>         - Set join command (e.g., '1234' sends [+]join,1234 in burst)\n");
		printk("  [+]join,<param>  - Set join command (burst for a few seconds)\n");
		printk("[+]led,<param>   - Set LED command (burst for a few seconds)\n");
		printk("  join,<param>     - Auto-format join command (burst)\n");
		printk("  test             - Reset to default join command [+]join,9999\n");
		printk("  status           - Show synced devices and current command\n");
		printk("  refresh          - Force send current command now\n");
		printk("  help             - Show this help message\n");
		printk("Examples:\n");
		printk("  1234             - Send [+]join,1234 for a few seconds then revert\n");
		printk("  [+]join,1234     - Same as above\n");
		printk("  join,9999        - Same as above\n");
		printk("Current command: '%s'\n\n", current_command);
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
			printk("Numeric shortcut detected - join parameter: %d\n", join_param);
			printk("Formatted command: %s\n", full_cmd);

			// Activate temporary join command for a few seconds
			temp_command_active = true;
			temp_command_expiry_ms = k_uptime_get() + TEMP_CMD_DURATION_MS;

			display_synced_devices_status();

			int err = send_command_to_synced_devices(pawr_adv, full_cmd);
			if (err)
			{
				printk("ERROR: Failed to send join command to devices (err %d)\n", err);
			}
			else
			{
				printk("SUCCESS: Join command sent to all synced devices (burst mode)\n");
				printk("Temporary command active for %d ms\n", TEMP_CMD_DURATION_MS);
			}
		}
		else
		{
			printk("WARNING: Unknown command: '%s'\n", cmd);
			printk("Use 'help' for available commands\n");
			printk("Quick usage: Type a number (e.g., '1234') to send [+]join,1234 in burst\n");
		}
	}

	printk("Current command after processing: '%s'\n", current_command);
	printk("Temp command active: %s\n", temp_command_active ? "true" : "false");
	printk("=== COMMAND PROCESSING COMPLETE ===\n");
}

void join_command_thread(void *pawr_adv_ptr, void *unused1, void *unused2)
{
	struct bt_le_ext_adv *pawr_adv = (struct bt_le_ext_adv *)pawr_adv_ptr;
	char cmd_buf[CMD_BUF_SIZE];

	printk("=== Command Processing Thread Started ===\n");
	printk("Ready to receive commands via UART\n");
	printk("Default command: %s\n", current_command);
	printk("Quick commands:\n");
	printk("  1234             - Send join command with parameter 1234 (burst)\n");
	printk("  join,1234        - Send join command with parameter 1234 (burst)\n");
	printk("  test             - Reset to default join command [+]join,9999\n");
	printk("  status           - Show synced devices and current command\n");
	printk("  refresh          - Force send current command now\n");
	printk("  help             - Show all commands\n");
	printk("Type command and press ENTER:\n");
	printk(">>> ");

	while (1)
	{
		char *input = console_getline();
		if (input && strlen(input) > 0)
		{
			strncpy(cmd_buf, input, sizeof(cmd_buf) - 1);
			cmd_buf[sizeof(cmd_buf) - 1] = '\0';
			printk("\nUART: Command received: '%s'\n", cmd_buf);
			process_command(pawr_adv, cmd_buf);
			printk(">>> ");
		}
		k_sleep(K_MSEC(1));
	}
}

// Update current_command if temporary join has expired
static void update_temp_command_state(void)
{
	if (!temp_command_active)
	{
		return;
	}

	int64_t now = k_uptime_get();
	if (now >= temp_command_expiry_ms)
	{
		printk("Temporary join command duration expired. Reverting to default.\n");
		strncpy(current_command, default_command, CMD_BUF_SIZE - 1);
		current_command[CMD_BUF_SIZE - 1] = '\0';
		temp_command_active = false;
		temp_command_expiry_ms = 0;
		printk("Current command reverted to: '%s'\n", current_command);
	}
}
static uint8_t current_response_subevent = 0;
static void request_cb(struct bt_le_ext_adv *adv,
					   const struct bt_le_per_adv_data_request *request)
{
	if (atomic_get(&onboarding_busy))
	{
		// Still send command, but disable responses
		for (size_t i = 0; i < NUM_SUBEVENTS; i++)
		{
			subevent_data_params[i].subevent = i;
			subevent_data_params[i].response_slot_start = 0;
			subevent_data_params[i].response_slot_count = 0; // no responses
			subevent_data_params[i].data = &bufs[i];
		}

		bt_le_per_adv_set_subevent_data(adv, NUM_SUBEVENTS, subevent_data_params);
		return;
	}
	int err;
	uint8_t to_send;
	struct net_buf_simple *buf;

	// Handle temporary command expiry
	update_temp_command_state();

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

		size_t copy_len = MIN(cmd_len, PACKET_SIZE - 1);
		memcpy(buf->data, cmd_local, copy_len);
		buf->data[copy_len] = '\0';
		buf->len = copy_len + 1;

		subevent_data_params[i].subevent = subevent;
		subevent_data_params[i].response_slot_start = 0;
		if (subevent == current_response_subevent ||
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
		printk("Failed to set PAwR command data (err %d)\n", err);
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
		printk("Active response subevent: %d\n", current_response_subevent);
	}
}
static bool print_ad_field(struct bt_data *data, void *user_data)
{
	ARG_UNUSED(user_data);

	printk("    0x%02X: ", data->type);
	for (size_t i = 0; i < data->data_len; i++)
	{
		printk("%02X", data->data[i]);
	}
	printk("\n");

	return true;
}

static struct bt_conn *default_conn;

static void response_cb(struct bt_le_ext_adv *adv,
						struct bt_le_per_adv_response_info *info,
						struct net_buf_simple *buf)
{
	if (buf && buf->len > 0)
	{
		// printk("=== Device Response ===\n");
		// printk("From: subevent %d, slot %d\n", info->subevent, info->response_slot);
		// printk("Response length: %d bytes\n", buf->len);

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
			// printk("Response text: ");
			for (size_t i = 0; i < buf->len; i++)
			{
				if (buf->data[i] >= 0x20 && buf->data[i] <= 0x7E)
				{
					// printk("%c", buf->data[i]);
				}
				else if (buf->data[i] == 0x00)
				{
					break;
				}
			}
			// printk("\n");

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
				// printk("Parsed device ID from response: %s\n", parsed_dev_id);
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

					if (first_time)
					{
						// New device ID learned for this slot – print join event
						printk("[+]new,%s\n", synced_devices[i].address);
					}
				}
				break;
			}
		}

		if (idx >= 0)
		{
			// printk("Updated slot %d (subevent %d, response_slot %d) for response\n",
			// 	   idx, info->subevent, info->response_slot);
			if (parsed_dev_id[0] != '\0')
			{
				// printk("[PAWR] mac=%s subevent=%d slot=%d\n",
				// 	   synced_devices[idx].address,
				// 	   info->subevent,
				// 	   info->response_slot);
			}
		}
		else
		{
			printk("Response from unknown slot (subevent %d, response_slot %d)\n",
				   info->subevent, info->response_slot);
		}
		// printk("\n");

		// printk("==================\n");
	}
	else
	{
		printk("Empty response from subevent %d, slot %d\n",
			   info->subevent, info->response_slot);
	}
}

static const struct bt_le_ext_adv_cb adv_cb = {
	.pawr_data_request = request_cb,
	.pawr_response = response_cb,
};

void connected_cb(struct bt_conn *conn, uint8_t err)
{
	printk("Connected (err 0x%02X)\n", err);

	__ASSERT(conn == default_conn, "Unexpected connected callback");

	if (err)
	{
		printk("Connection failed (err 0x%02X)\n", err);

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
	printk("Disconnected, reason 0x%02X %s\n", reason, bt_hci_err_to_str(reason));

	if (default_conn)
	{
		const bt_addr_le_t *dev_addr = bt_conn_get_dst(default_conn);
		if (dev_addr)
		{
			char addr_str[BT_ADDR_LE_STR_LEN] = {0};
			bt_addr_le_to_str(dev_addr, addr_str, sizeof(addr_str));

			for (int i = 0; i < MAX_SYNCS; i++)
			{
				if (synced_devices[i].active &&
					strcmp(synced_devices[i].address, addr_str) == 0)
				{
					printk("Device %s disconnected, keeping slot %d (subevent %d, slot %d)\n",
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
	// default_conn = NULL;
	printk("Restarting scan\n");
	k_sleep(K_MSEC(800));
	bt_le_scan_start(BT_LE_SCAN_PASSIVE_CONTINUOUS, device_found);
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
	int64_t now = k_uptime_get();
	// if (now - last_onboard_time < ONBOARDING_COOLDOWN_MS)
	// 	return;

	atomic_set(&onboarding_busy, 0);

	if (bt_le_scan_stop())
	{
		atomic_set(&onboarding_busy, 0);
		return;
	}

	/* Allow controller to settle */
	k_sleep(K_MSEC(200));

	err = bt_conn_le_create(addr,
							BT_CONN_LE_CREATE_CONN,
							BT_LE_CONN_PARAM_DEFAULT,
							&default_conn);

	if (err)
	{
		printk("Create conn failed (%u)\n", err);
		atomic_set(&onboarding_busy, 0);
	}
}

static uint8_t discover_func(struct bt_conn *conn, const struct bt_gatt_attr *attr,
							 struct bt_gatt_discover_params *params)
{
	struct bt_gatt_chrc *chrc;
	char str[BT_UUID_STR_LEN];

	printk("Discovery: attr %p\n", attr);

	if (!attr)
	{
		return BT_GATT_ITER_STOP;
	}

	chrc = (struct bt_gatt_chrc *)attr->user_data;
	bt_uuid_to_str(chrc->uuid, str, sizeof(str));
	printk("UUID %s\n", str);

	if (!bt_uuid_cmp(chrc->uuid, &pawr_char_uuid.uuid))
	{
		pawr_attr_handle = chrc->value_handle;
		printk("Characteristic handle: %d\n", pawr_attr_handle);
		k_sem_give(&sem_discovered);
	}

	return BT_GATT_ITER_STOP;
}

static void write_func(struct bt_conn *conn, uint8_t err, struct bt_gatt_write_params *params)
{
	if (err)
	{
		printk("Write failed (err %d)\n", err);
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

	printk("\n=== Current Synced Devices ===\n");
	for (int i = 0; i < MAX_SYNCS; i++)
	{
		if (synced_devices[i].active)
		{
			printk("Device %d: mac %s, dev_id %s, subevent %d, slot %d\n",
				   i,
				   synced_devices[i].address,
				   synced_devices[i].has_device_id ? synced_devices[i].device_id : "na",
				   synced_devices[i].subevent,
				   synced_devices[i].response_slot);
		}
	}

	if (active_count == 0)
	{
		printk("No devices currently synced\n");
	}
	else
	{
		printk("Total active devices: %d\n", active_count);
	}
	printk("============================\n\n");
}

void cleanup_inactive_slots(void)
{
	for (int i = 0; i < MAX_SYNCS; i++)
	{
		// 1) Active but timed out? -> treat as disconnected and clear slot
		if (synced_devices[i].active && !is_slot_responsive(i))
		{
			printk("Slot %d timed out, marking device as disconnected\n", i);
			clear_slot(i); // This will print [+]DISCONNTED,<dev_id> and set active=false
			continue;
		}

		// 2) Already inactive but still has stale address/device_id -> wipe it
		if (!synced_devices[i].active &&
			synced_devices[i].address[0] != '\0')
		{
			printk("Cleaning up inactive slot %d\n", i);
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
	printk("Resetting synchronization state...\n");
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
	printk("Synchronization state reset.\n");
}

void restart_advertising(void)
{

	int err = bt_le_per_adv_start(pawr_adv);
	if (err)
	{
		printk("Failed to restart periodic advertising: %d\n", err);
	}
	else
	{
		printk("Periodic advertising restarted\n");
	}

	err = bt_le_ext_adv_start(pawr_adv, BT_LE_EXT_ADV_START_DEFAULT);
	if (err)
	{
		printk("Failed to restart extended advertising: %d\n", err);
	}
	else
	{
		printk("Extended advertising restartedr\n");
	}
}
#define MAINT_THREAD_STACK_SIZE 1024
#define MAINT_THREAD_PRIORITY 6
K_THREAD_STACK_DEFINE(maint_thread_stack, MAINT_THREAD_STACK_SIZE);
static struct k_thread maint_thread_data;
void maint_thread(void *p1, void *p2, void *p3)
{
	ARG_UNUSED(p1);
	ARG_UNUSED(p2);
	ARG_UNUSED(p3);

	printk("Maintenance thread started (will cleanup inactive slots)\n");

	while (1)
	{
		k_sleep(K_SECONDS(5));
		cleanup_inactive_slots();
	}
}

int main(void)
{
	int err;
	struct bt_gatt_discover_params discover_params;
	struct bt_gatt_write_params write_params;
	struct pawr_timing sync_config;

	init_bufs();

	uart_dev = DEVICE_DT_GET(DT_NODELABEL(uart20));
	if (!device_is_ready(uart_dev))
	{
		printk("UART device not ready!\n");
		return 0;
	}

	for (int i = 0; i < MAX_SYNCS; i++)
	{
		synced_devices[i].active = false;
		synced_devices[i].subevent = INVALID_SLOT;
		synced_devices[i].response_slot = INVALID_SLOT;
		synced_devices[i].address[0] = '\0';
		synced_devices[i].device_id[0] = '\0';
		synced_devices[i].has_device_id = false;
		synced_devices[i].last_update_time = 0;
	}

	console_getline_init();
	printk("UART configured for command input\n");
	printk("System initialized - UART ready for commands\n");
	printk("Starting Periodic Advertising Demo\n");

	err = bt_enable(NULL);
	if (err)
	{
		printk("Bluetooth init failed (err %d)\n", err);
		return 0;
	}

	err = bt_le_ext_adv_create(BT_LE_EXT_ADV_NCONN, &adv_cb, &pawr_adv);
	if (err)
	{
		printk("Failed to create advertising set (err %d)\n", err);
		return 0;
	}

	err = bt_le_per_adv_set_param(pawr_adv, &per_adv_params);
	if (err)
	{
		printk("Failed to set periodic advertising parameters (err %d)\n", err);
		return 0;
	}

	printk("Start Periodic Advertising\n");
	err = bt_le_per_adv_start(pawr_adv);
	if (err)
	{
		printk("Failed to enable periodic advertising (err %d)\n", err);
		return 0;
	}

	printk("Start Extended Advertising\n");
	err = bt_le_ext_adv_start(pawr_adv, BT_LE_EXT_ADV_START_DEFAULT);
	if (err)
	{
		printk("Failed to start extended advertising (err %d)\n", err);
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
			printk("Scanning failed to start (err %d)\n", err);
			k_sleep(K_SECONDS(1));
			continue;
		}

		if (k_sem_take(&sem_connected, K_SECONDS(6)) != 0)
		{
			printk("Connection wait timeout → recovering...\n");

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

			//  4. Restart scan cleanly
			int err = bt_le_scan_start(BT_LE_SCAN_PASSIVE_CONTINUOUS, device_found);
			if (err && err != -EALREADY)
			{
				printk("Scan restart failed (%d)\n", err);
			}

			//  5. Small recovery delay
			k_sleep(K_MSEC(500));

			continue;
		}
		if (!default_conn)
		{
			printk("Connection failed, retrying...\n");
			atomic_set(&onboarding_busy, 0);
			default_conn = NULL;

			// 🔥 FORCE SCAN RESTART
			bt_le_scan_start(BT_LE_SCAN_PASSIVE_CONTINUOUS, device_found);

			k_sleep(K_MSEC(200));
			continue;
		}
		k_sleep(K_MSEC(300));
		err = bt_le_per_adv_set_info_transfer(pawr_adv, default_conn, 0);
		if (err)
		{
			printk("Failed to send PAST (err %d)\n", err);
			goto disconnect;
		}

		printk("PAST sent\n");
		// k_sleep(K_MSEC(500));
		k_sleep(K_MSEC(1500));
		discover_params.uuid = &pawr_char_uuid.uuid;
		discover_params.func = discover_func;
		discover_params.start_handle = BT_ATT_FIRST_ATTRIBUTE_HANDLE;
		discover_params.end_handle = BT_ATT_LAST_ATTRIBUTE_HANDLE;
		discover_params.type = BT_GATT_DISCOVER_CHARACTERISTIC;

		err = bt_gatt_discover(default_conn, &discover_params);
		if (err)
		{
			printk("Discovery failed (err %d)\n", err);
			goto disconnect;
		}

		printk("Discovery started\n");

		err = k_sem_take(&sem_discovered, K_SECONDS(10));
		if (err)
		{
			printk("Timed out during GATT discovery\n");
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
			printk("No slot available for device %s\n", addr_str);
			goto disconnect;
		}

		sync_config.subevent = subevent;
		sync_config.response_slot = response_slot;

		write_params.func = write_func;
		write_params.handle = pawr_attr_handle;
		write_params.offset = 0;
		write_params.data = &sync_config;
		write_params.length = sizeof(sync_config);

		err = bt_gatt_write(default_conn, &write_params);
		if (err)
		{
			printk("Write failed (err %d)\n", err);
			clear_slot(slot_idx);
			goto disconnect;
		}

		printk("Write started\n");

		err = k_sem_take(&sem_written, K_SECONDS(10));
		if (err)
		{
			printk("Timed out during GATT write\n");
			clear_slot(slot_idx);
			goto disconnect;
		}
		k_sleep(K_MSEC(800));
		// Mark initial "alive" timestamp for this slot
		// synced_devices[slot_idx].last_update_time = k_uptime_get();
		synced_devices[slot_idx].last_sync_time = k_uptime_get();
		synced_devices[slot_idx].last_response_time = 0;

		printk("PAwR config written to sync %d (subevent %d, slot %d), disconnecting\n",
			   slot_idx, sync_config.subevent, sync_config.response_slot);

	disconnect:
		k_sleep(K_MSEC(per_adv_params.interval_max * 2));

		if (default_conn)
		{
			// k_sleep(K_MSEC(100));
			k_sleep(K_MSEC(1200));
			err = bt_conn_disconnect(default_conn,
									 BT_HCI_ERR_REMOTE_USER_TERM_CONN);
			if (err)
			{
				printk("Disconnect failed (err %d)\n", err);
				return 0;
			}
		}

		k_sem_take(&sem_disconnected, K_FOREVER);
		// k_sleep(K_MSEC(400));
		k_sleep(K_MSEC(1200));
	}

	printk("Maximum number of syncs onboarded: %d devices\n", num_synced);
	printk("System ready - listening for commands via UART\n");
	printk("Command format: number OR join,<param> OR [+]join,<param>\n");
	printk("Example: 1234  (sends [+]join,1234 for a few seconds)\n");

	printk("\n=== Synced Devices Status ===\n");
	for (int i = 0; i < MAX_SYNCS; i++)
	{
		if (synced_devices[i].active)
		{
			const char *id_str = synced_devices[i].has_device_id ? synced_devices[i].device_id : "unknown";

			printk("Device %d: dev_id %s, subevent %d, response_slot %d, addr %s\n",
				   i,
				   id_str,
				   synced_devices[i].subevent,
				   synced_devices[i].response_slot,
				   synced_devices[i].address);
		}
	}
	printk("============================\n\n");

	while (1)
	{
		k_sleep(K_SECONDS(5));
		static int status_counter = 0;
		if (++status_counter >= 12)
		{
			status_counter = 0;
			printk("System status: %d synced devices active, waiting for commands...\n",
				   num_synced);
			printk("Current command: %s | temp_active: %s\n",
				   current_command,
				   temp_command_active ? "true" : "false");
		}
		cleanup_inactive_slots();
	}

	return 0;
}
