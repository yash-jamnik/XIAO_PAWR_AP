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
#include <zephyr/storage/flash_map.h>

/* Variable Declaration for Scanning Usage */
#define DEVICE_NAME "PARALLEL"		//  "PAwR sync sample" ,  "Internal_testing"

#define DEVICE_NAME_LEN (sizeof(DEVICE_NAME) - 1)
#define MAX_SCAN_RESULTS 20
#define SCAN_WINDOW_SECONDS 10

/* ---- Result storage ---- */
struct scan_result_t
{
	bt_addr_le_t addr;
	int8_t rssi;
};

static struct scan_result_t scan_results[MAX_SCAN_RESULTS];
static uint8_t scan_result_count;
static struct k_mutex results_mutex;
static struct k_mutex radio_mutex;
static struct k_mutex synced_devices_mutex;


/* ---- Control primitives ---- */
K_SEM_DEFINE(scan_done_sem, 0, 1);	  /* signaled when 20 found, or on timeout fallback */
K_SEM_DEFINE(scan_restart_sem, 0, 1); /* external trigger to force a rescan */
K_SEM_DEFINE(sem_remote_info, 0, 1);

// Worker Thread
struct wdisc_job
{
	bt_addr_le_t addr;
	struct bt_conn *conn; /* ref already held from bt_conn_le_create */
};
static bool tel_all_active = false;
#define PAWR_EVENT_MS 3840
#define TEL_ALL_DURATION_MS (3 * PAWR_EVENT_MS + 500) /* keep proto alive ~3 events */
#define PROTO_CMD_DURATION_MS (3 * PAWR_EVENT_MS + 500)
#define WDISC_QUEUE_LEN 16
K_MSGQ_DEFINE(wdisc_job_q, sizeof(struct wdisc_job), WDISC_QUEUE_LEN, 4);
K_MSGQ_DEFINE(scan_result_msgq, sizeof(struct scan_result_t), MAX_SCAN_RESULTS, 4);

#define WDISC_POOL_SIZE 5 /* start here */
#define WDISC_POOL_MAX 10 /* ceiling you can bump to */

struct wdisc_worker
{
	int id;
	struct k_thread thread;
	k_tid_t tid;

	struct bt_conn *conn; /* conn this worker is currently handling */

	struct bt_gatt_discover_params discover_params;
	struct bt_gatt_write_params write_params;

	struct k_sem sem_discovered;
	struct k_sem sem_written;
	struct k_sem sem_remote_info;
	uint16_t pawr_attr_handle;
};

/* Thread Declarations */
static bool scanning_enabled = false;
#define SCAN_THREAD_STACK_SIZE 1024
#define SCAN_THREAD_PRIORITY 5
K_THREAD_STACK_DEFINE(scan_thread_stack, SCAN_THREAD_STACK_SIZE);
static struct k_thread scan_thread_data;

#define GATT_THREAD_STACK_SIZE 2048
#define GATT_THREAD_PRIORITY 5
K_THREAD_STACK_DEFINE(gatt_thread_stack, GATT_THREAD_STACK_SIZE);
static struct k_thread gatt_thread_data;

#define MAIN_THREAD_STACK_SIZE 2048
#define MAIN_THREAD_PRIORITY 5
K_THREAD_STACK_DEFINE(main_thread_stack, MAIN_THREAD_STACK_SIZE);
static struct k_thread main_thread_data;

#define JOIN_THREAD_STACK_SIZE 2048
#define JOIN_THREAD_PRIORITY 5
K_THREAD_STACK_DEFINE(join_thread_stack, JOIN_THREAD_STACK_SIZE);
struct k_thread join_thread_data;

#define WDISC_THREAD_STACK_SIZE 2048
#define WDISC_THREAD_PRIORITY 5
K_THREAD_STACK_ARRAY_DEFINE(wdisc_stacks, WDISC_POOL_MAX, WDISC_THREAD_STACK_SIZE);
static struct wdisc_worker wdisc_workers[WDISC_POOL_MAX];
static int wdisc_pool_size;

static K_SEM_DEFINE(sem_connected, 0, 1);
static K_SEM_DEFINE(sem_disconnected, 0, 1);

static struct nvs_fs fs;
static char active_command_mac[BT_ADDR_STR_LEN] = {0};
#define NVS_ID_MCUMGR_MODE 1

static struct bt_le_conn_param *fast_conn_param =
	BT_LE_CONN_PARAM(0x0010, 0x0010, 5, 1000); /* 20ms fixed interval, latency 0, 4s timeout */

static struct bt_conn_le_create_param *fast_create_param =
	BT_CONN_LE_CREATE_PARAM(BT_CONN_LE_OPT_NONE,
							BT_GAP_SCAN_FAST_INTERVAL,
							BT_GAP_SCAN_FAST_INTERVAL);

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

static void conn_state_check_cb(struct bt_conn *conn, void *user_data)
{
	bool *busy = user_data;
	struct bt_conn_info info;

	if (bt_conn_get_info(conn, &info) == 0 &&
		info.state == BT_CONN_STATE_CONNECTING)
	{
		*busy = true;
	}
}

static bool connect_in_progress(void)
{
	bool busy = false;

	bt_conn_foreach(BT_CONN_TYPE_LE, conn_state_check_cb, &busy);
	return busy;
}

#define CONN_WAIT_TIMEOUT_MS 5000
#define CONN_POLL_INTERVAL_MS 50

bool wait_for_connected_state(struct bt_conn *conn, int timeout_ms)
{
	int elapsed = 0;
	struct bt_conn_info info;

	while (elapsed < timeout_ms)
	{
		int err = bt_conn_get_info(conn, &info);
		if (err)
		{
			APP_LOG("Failed to get conn info (err %d)\n", err);
			return false;
		}

		if (info.state == BT_CONN_STATE_CONNECTED)
		{
			APP_LOG("Conn state: CONNECTED (took ~%d ms)\n", elapsed);
			APP_LOG("Interval: %d (%d.%02d ms), latency: %d, timeout: %d\n",
					info.le.interval,
					(info.le.interval * 125) / 100,
					(info.le.interval * 125) % 100,
					info.le.latency, info.le.timeout);
			return true;
		}

		if (info.state == BT_CONN_STATE_DISCONNECTED)
		{
			APP_LOG("Conn state: DISCONNECTED while waiting — aborting\n");
			return false;
		}

		k_sleep(K_MSEC(CONN_POLL_INTERVAL_MS));
		elapsed += CONN_POLL_INTERVAL_MS;
	}

	APP_LOG("Timed out waiting for connection (state=%d)\n", info.state);
	return false;
}

/* Helper Function for the Scanning */
static bool addr_already_present(const bt_addr_le_t *addr)
{
	for (int i = 0; i < scan_result_count; i++)
	{
		if (bt_addr_le_cmp(&scan_results[i].addr, addr) == 0)
		{
			return true;
		}
	}
	return false;
}

/* AD data parsing callback for bt_data_parse */
struct name_check_ctx
{
	bool match;
};

static bool ad_parse_cb(struct bt_data *data, void *user_data)
{
	struct name_check_ctx *ctx = user_data;

	if (data->type == BT_DATA_NAME_COMPLETE ||
		data->type == BT_DATA_NAME_SHORTENED)
	{
		if (data->data_len == DEVICE_NAME_LEN &&
			memcmp(data->data, DEVICE_NAME, DEVICE_NAME_LEN) == 0)
		{
			ctx->match = true;
			return false; /* stop parsing, found it */
		}
	}
	return true; /* continue parsing */
}

static bool name_matches(struct net_buf_simple *ad)
{
	struct name_check_ctx ctx = {.match = false};
	struct net_buf_simple ad_copy;

	/* bt_data_parse consumes the buffer, so work on a copy */
	net_buf_simple_clone(ad, &ad_copy);
	bt_data_parse(&ad_copy, ad_parse_cb, &ctx);

	return ctx.match;
}

static atomic_t onboarding_busy = ATOMIC_INIT(0);
static atomic_t conn_activity = ATOMIC_INIT(0);
static K_SEM_DEFINE(radio_free_sem, 0, 1);

static int64_t last_onboard_time = 0;

#define NUM_RSP_SLOTS 10
#define NUM_SUBEVENTS 15
#define PACKET_SIZE 30
#define NAME_LEN 30
#define UART_BUF_SIZE 256
#define CMD_BUF_SIZE 128

#define MAX_SYNCS (NUM_SUBEVENTS * NUM_RSP_SLOTS)
#define SLOT_TIMEOUT_MS 45000 // 90 seconds
#define INVALID_SLOT 0xFF
#define ADDR_STR_LEN BT_ADDR_LE_STR_LEN // full bt_addr_le_to_str() string

static uint8_t proto_buf[PACKET_SIZE];
static size_t proto_len = 0;
static bool proto_command_active = false;

static struct bt_uuid_128 pawr_char_uuid =
	BT_UUID_INIT_128(BT_UUID_128_ENCODE(0x12345678, 0x1234, 0x5678, 0x1234, 0x56789abcdef1));
// static uint16_t pawr_attr_handle;

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
	bool tel_reported;
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
	// k_mutex_lock(&synced_devices_mutex, K_FOREVER);

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
	// k_mutex_unlock(&synced_devices_mutex);
	return -1; // No slot available
}

// Function to send command data to all synced devices (immediate push)
static int send_command_to_synced_devices(struct bt_le_ext_adv *pawr_adv, const char *command)
{
    int active_devices = 0;
    APP_LOG("Updating command to: '%s'\n", command);
    strncpy(current_command, command, CMD_BUF_SIZE - 1);
    current_command[CMD_BUF_SIZE - 1] = '\0';

    for (int i = 0; i < MAX_SYNCS; i++) {
        if (synced_devices[i].active) active_devices++;
    }

    if (active_devices == 0) {
        APP_LOG("No synced devices available - command updated for future requests\n");
        return 0;
    }
	APP_LOG("Command '%s' queued; will be sent on next PAwR request\n", command);
	return 0;

	// int err;
	// uint8_t active_devices = 0;
	// size_t cmd_len = strlen(command);

	// APP_LOG("Updating command to: '%s'\n", command);

	// // Update the global current command
	// strncpy(current_command, command, CMD_BUF_SIZE - 1);
	// current_command[CMD_BUF_SIZE - 1] = '\0';

	// // Count active synced devices
	// for (int i = 0; i < MAX_SYNCS; i++)
	// {
	// 	if (synced_devices[i].active)
	// 	{
	// 		active_devices++;
	// 	}
	// }

	// if (active_devices == 0)
	// {
	// 	APP_LOG("No synced devices available - but command updated for future requests\n");
	// 	APP_LOG("Current command will be sent when devices sync or on next PAwR request\n");
	// 	return 0;
	// }

	// // Immediately prepare and send the new command data
	// for (size_t i = 0; i < NUM_SUBEVENTS; i++)
	// {
	// 	struct net_buf_simple *buf = &bufs[i];

	// 	memset(buf->data, 0, PACKET_SIZE);

	// 	size_t copy_len = MIN(cmd_len, PACKET_SIZE - 1);
	// 	memcpy(buf->data, command, copy_len);
	// 	buf->data[copy_len] = '\0';
	// 	buf->len = copy_len + 1;

	// 	subevent_data_params[i].subevent = i;
	// 	subevent_data_params[i].response_slot_start = 0;
	// 	subevent_data_params[i].response_slot_count = NUM_RSP_SLOTS;
	// 	subevent_data_params[i].data = buf;
	// }

	// err = bt_le_per_adv_set_subevent_data(pawr_adv, NUM_SUBEVENTS, subevent_data_params);
	// APP_LOG("Command '%s' sent immediately to %d synced devices\n", command, active_devices);
	// APP_LOG("Current active command: '%s'\n", current_command);

	// return 0;
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
void encode_tel_all_command(void)
{
	uint8_t bcast_mac[6] = {0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF};
	encode_tel_command_with_mac(bcast_mac);
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

		/*
		 * Keep TEL protobuf active for multiple PAwR events.
		 */
		temp_command_active = true;
		temp_command_expiry_ms =
			k_uptime_get() + PROTO_CMD_DURATION_MS;

		/*
		 * Do not use the 3-second response window.
		 * PAwR event itself is 3840 ms.
		 */
		response_window_active = false;
		response_window_expiry_ms = 0;

		/*
		 * Store the MAC of the device we are waiting for.
		 */
		strncpy(active_command_mac,
				mac_str,
				sizeof(active_command_mac) - 1);

		active_command_mac[sizeof(active_command_mac) - 1] = '\0';

		/*
		 * Encode TEL protobuf.
		 */
		encode_tel_command_with_mac(mac);

		if (proto_command_active && proto_len > 0)
		{
			APP_LOG("[+]TEL_PROTO_READY len=%d target=%s\n",
					(int)proto_len,
					active_command_mac);
		}
		else
		{
			APP_LOG("[TEL] ERROR: protobuf encoding failed\n");
		}
	}
	else if (strcmp(cmd, "[+]ping_all") == 0 || strcmp(cmd, "ping_all") == 0)
	{
		APP_LOG("TEL_ALL: polling all synced devices\n");
		display_synced_devices_status();

		/* reset per-device reported flags */
		for (int i = 0; i < MAX_SYNCS; i++)
		{
			synced_devices[i].tel_reported = false;
		}

		temp_command_active = true;
		temp_command_expiry_ms = k_uptime_get() + TEL_ALL_DURATION_MS;

		/* no 3s response window - PAwR event itself is 3840 ms */
		response_window_active = false;
		response_window_expiry_ms = 0;

		/* broadcast mode: no single target MAC */
		active_command_mac[0] = '\0';
		tel_all_active = true;

		encode_tel_all_command();

		if (proto_command_active && proto_len > 0)
		{
			APP_LOG("[+]TEL_ALL_PROTO_READY len=%d\n", (int)proto_len);
		}
		else
		{
			tel_all_active = false;
			APP_LOG("[TEL_ALL] ERROR: protobuf encoding failed\n");
		}
	}
	else if (strncmp(cmd, "[+]active,", 10) == 0)
	{
		const char *mac = cmd + 10;

		snprintf(current_command, CMD_BUF_SIZE, "ACTIVE,%s", mac);

		temp_command_active = true;
		temp_command_expiry_ms = k_uptime_get() + PROTO_CMD_DURATION_MS;

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
	
	else if (strncmp(cmd, "[+]list", 7) == 0 || strncmp(cmd, "list", 4) == 0)
	{
#define LIST_MAX_RANGE 20 /* serial protection: cap devices per request */

		/* Parse: "list" | "list,<start>" | "list,<start>,<end>" */
		int start_index = -1;
		int end_index = -1;

		const char *comma = strchr(cmd, ',');
		if (comma)
		{
			start_index = atoi(comma + 1);

			const char *comma2 = strchr(comma + 1, ',');
			if (comma2)
			{
				end_index = atoi(comma2 + 1);
			}
			else
			{
				end_index = start_index; /* single index -> just that one */
			}
		}

		/* Collect active slots so indices are contiguous 0..total-1
		 * (slot numbers in the table can have gaps) */
		int active_idx[MAX_SYNCS];
		int total = 0;
		for (int i = 0; i < MAX_SYNCS; i++)
		{
			if (synced_devices[i].active)
			{
				active_idx[total++] = i;
			}
		}

		/* Bare "list" -> header only */
		if (start_index < 0)
		{
			APP_LOG("[+]list,%d\n", total);
			APP_LOG("[+]listend\n");
			return;
		}

		/* Validate range */
		if (start_index >= total || end_index < start_index)
		{
			APP_LOG("[+]list,err,invalid range (%d devices, valid 0-%d)\n",
					total, total > 0 ? total - 1 : 0);
			APP_LOG("[+]listend\n");
			return;
		}

		/* Clamp end to available devices and to max chunk size */
		if (end_index >= total)
		{
			end_index = total - 1;
		}
		if (end_index - start_index + 1 > LIST_MAX_RANGE)
		{
			end_index = start_index + LIST_MAX_RANGE - 1;
		}

		APP_LOG("[+]list,%d,%d,%d\n", total, start_index, end_index);

		for (int n = start_index; n <= end_index; n++)
		{
			int i = active_idx[n];
			APP_LOG("[+]dev,%d,%s,%d,%d\n",
					n,
					synced_devices[i].address,
					synced_devices[i].subevent,
					synced_devices[i].response_slot);
		}

		APP_LOG("[+]listend\n");
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

void join_command(void *pawr_adv_ptr, void *unused1, void *unused2)
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

	// Local copy of command
	char cmd_local[CMD_BUF_SIZE];
	strncpy(cmd_local, current_command, CMD_BUF_SIZE - 1);
	cmd_local[CMD_BUF_SIZE - 1] = '\0';

	size_t cmd_len = strlen(cmd_local);

	to_send = MIN(request->count, ARRAY_SIZE(subevent_data_params));

	/* Clamp instead of wrap — never produce a non-increasing subevent list */
	uint8_t max_from_start = per_adv_params.num_subevents - request->start;
	if (to_send > max_from_start) {
		to_send = max_from_start;
	}

	for (size_t i = 0; i < to_send; i++)
	{
		uint8_t subevent = (request->start + i);// % per_adv_params.num_subevents;

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
				msg = cmd_local;
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
	// "[+]join,E1:CE:45:CC:AC:C4,CB:C3:09:B3:18:8E"
	err = bt_le_per_adv_set_subevent_data(adv, to_send, subevent_data_params);
	if (err)
	{
	    APP_LOG("Failed to set PAwR command data (err %d) req_start=%u req_count=%u to_send=%u\n",
            err, request->start, request->count, to_send);
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
static void response_cb(struct bt_le_ext_adv *adv,
						struct bt_le_per_adv_response_info *info,
						struct net_buf_simple *buf)
{
	// debug check which subevnt and slot are respoding

	ARG_UNUSED(adv);

	if (!buf || buf->len == 0)
	{
		return;
	}

	APP_LOG("[RESP] se=%d slot=%d len=%d raw=%s\n",
			info->subevent, info->response_slot, buf->len,
			bt_hex(buf->data, buf->len));
	

	/* 1. Identify device by its slot */
	int idx = -1;
	for (int i = 0; i < MAX_SYNCS; i++)
	{
		if (synced_devices[i].active &&
			synced_devices[i].subevent == info->subevent &&
			synced_devices[i].response_slot == info->response_slot)
		{
			idx = i;
			break;
		}
	}

	/* 2. Any response means the device is alive */
	if (idx >= 0)
	{
		synced_devices[idx].last_response_time = k_uptime_get();
		synced_devices[idx].state = PAWR_DEVICE_SYNCED;
		synced_devices[idx].active_check_pending = false;
		synced_devices[idx].active_check_retry = 0;
	}

	/* 3. TEL protobuf response */
	/* 3. TEL protobuf response */
	char tel_mac[24] = {0};
	char tel_meta[64] = {0};

	if (decode_tel_response(buf->data, buf->len,
							tel_mac, sizeof(tel_mac),
							tel_meta, sizeof(tel_meta)))
	{
		if (tel_all_active)
		{
			/* already reported this device during this poll? */
			if (idx >= 0 && synced_devices[idx].tel_reported)
			{
				return;
			}
			if (idx >= 0)
			{
				synced_devices[idx].tel_reported = true;
			}

			/* meta is "tin,batt" - extract tin */
			char tin[20] = {0};
			char *comma = strchr(tel_meta, ',');
			size_t tin_len = comma ? (size_t)(comma - tel_meta)
								   : strlen(tel_meta);
			if (tin_len >= sizeof(tin))
			{
				tin_len = sizeof(tin) - 1;
			}
			memcpy(tin, tel_meta, tin_len);
			tin[tin_len] = '\0';

			APP_LOG("[+]res,ping,%s\n", tin);
			return;
		}
		APP_LOG("[TEL] RX se=%d slot=%d MAC=%s META=%s expected=%s\n",
				info->subevent,
				info->response_slot,
				tel_mac,
				tel_meta,
				active_command_mac);

		/* No TEL command is currently waiting for a response */
		if (active_command_mac[0] == '\0')
		{
			APP_LOG("[TEL] Ignoring response - no active TEL request\n");
			return;
		}

		/* Response came from another device */
		if (strcasecmp(tel_mac, active_command_mac) != 0)
		{
			APP_LOG("[TEL] Wrong device response: %s\n", tel_mac);
			return;
		}

		/* Correct TEL device responded */
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

			APP_LOG("[+]res,%s,%s,%s\n",
					tel_mac,
					tin,
					batt);
		}
		else
		{
			APP_LOG("[+]res,%s,%s\n",
					tel_mac,
					tel_meta);
		}

		/* Only clear after the CORRECT device responds */
		active_command_mac[0] = '\0';

		return;
	}

	/* 4. Text ack: "[+]res,<mac>,..." */
	if (buf->len > 7 && strncmp((char *)buf->data, "[+]res,", 7) == 0)
	{
		char res_str[64] = {0};
		size_t copy_len = MIN(buf->len, sizeof(res_str) - 1);
		memcpy(res_str, buf->data, copy_len);
		APP_LOG("%s\n", res_str);
		return;
	}

	/* 5. Text ack: "OK,<mac>" - liveness already handled in step 2 */
	if (buf->len > 3 && strncmp((char *)buf->data, "OK,", 3) == 0)
	{
		return;
	}

	/* 6. "devid,<id>" - store the device ID */
	if (idx >= 0 && buf->len > 6 &&
		strncmp((char *)buf->data, "devid,", 6) == 0)
	{
		size_t id_len = buf->len - 6;
		if (id_len >= sizeof(synced_devices[idx].device_id))
		{
			id_len = sizeof(synced_devices[idx].device_id) - 1;
		}
		memcpy(synced_devices[idx].device_id, &buf->data[6], id_len);
		synced_devices[idx].device_id[id_len] = '\0';
		synced_devices[idx].has_device_id = true;
	}
	/* 7. Anything unrecognized - never drop silently */
	// APP_LOG("[?] Unhandled response se=%d slot=%d len=%d first=%02X\n",
	// 		info->subevent, info->response_slot, buf->len, buf->data[0]);
}

static const struct bt_le_ext_adv_cb adv_cb = {
	.pawr_data_request = request_cb, // pap to esl
	.pawr_response = response_cb,	 // esl to pap
};

static bool conn_is_live(struct bt_conn *conn)
{
	if (!conn)
		return false;
	struct bt_conn_info info;
	if (bt_conn_get_info(conn, &info))
		return false;
	return info.state == BT_CONN_STATE_CONNECTED;
}

int64_t startTime = 0;
int64_t endTime = 0;

void connected_cb(struct bt_conn *conn, uint8_t err)
{
	if (err)
	{
		APP_LOG("Connection failed (err 0x%02X), elapsed %lld ms\n",
				err, endTime - startTime);

		bt_conn_unref(conn);
		conn = NULL;

		k_sem_give(&sem_connected);
		k_sem_give(&sem_disconnected); /* signal AFTER this thread is truly done */
		return;
	}

	struct wdisc_job job;
	bt_addr_le_copy(&job.addr, bt_conn_get_dst(conn));
	job.conn = conn; /* default_conn already holds the ref from bt_conn_le_create */

	char addr_str[BT_ADDR_LE_STR_LEN];
	bt_addr_le_to_str(&job.addr, addr_str, sizeof(addr_str));
	APP_LOG("Connected CB: connection established for %s\n", addr_str);

	if (k_msgq_put(&wdisc_job_q, &job, K_NO_WAIT) != 0)
	{
		APP_LOG("wdisc queue full, dropping connection %s\n", addr_str);
		bt_conn_disconnect(conn, BT_HCI_ERR_REMOTE_USER_TERM_CONN);
		bt_conn_unref(conn);
		conn = NULL;
		k_sem_give(&sem_connected); /* wake gatt_thread NOW, not after 10s */
		k_sem_give(&sem_disconnected);
		return;
	}

	k_sem_give(&sem_connected);
}

void disconnected_cb(struct bt_conn *conn, uint8_t reason)
{
	if (reason == BT_HCI_ERR_REMOTE_USER_TERM_CONN ||
		reason == BT_HCI_ERR_LOCALHOST_TERM_CONN)
	{
		/* graceful, expected */
	}
	else if (reason == BT_HCI_ERR_CONN_TIMEOUT)
	{
		APP_LOG("Supervision timeout for this device — link dropped abnormally\n");
		/* consider: mark this MAC for a longer backoff/cooldown before
		 * scan_thread re-attempts a connect, since the controller may
		 * need time to release resources internally */
	}

	char addr_str[BT_ADDR_LE_STR_LEN];
	const bt_addr_le_t *dev_addr = bt_conn_get_dst(conn);

	if (dev_addr)
	{
		bt_addr_le_to_str(dev_addr, addr_str, sizeof(addr_str));
	}

	APP_LOG("Disconnected CB : %s, reason 0x%02X %s\n\n",
			dev_addr ? addr_str : "(unknown)", reason, bt_hci_err_to_str(reason));

	if (conn && dev_addr)
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

	/* NEW: wake the owning worker immediately, whichever wait it's in */
	for (int i = 0; i < wdisc_pool_size; i++)
	{
		if (wdisc_workers[i].conn == conn)
		{
			k_sem_give(&wdisc_workers[i].sem_remote_info);
			k_sem_give(&wdisc_workers[i].sem_discovered);
			k_sem_give(&wdisc_workers[i].sem_written);
			break;
		}
	}

	/* release onboarding lock */
	last_onboard_time = k_uptime_get();
	atomic_set(&onboarding_busy, 0);
}

void remote_info_available_cb(struct bt_conn *conn, struct bt_conn_remote_info *remote_info)
{
	for (int i = 0; i < wdisc_pool_size; i++)
	{
		if (wdisc_workers[i].conn == conn)
		{
			k_sem_give(&wdisc_workers[i].sem_remote_info);
			return;
		}
	}
}

BT_CONN_CB_DEFINE(conn_cb) = {
	.connected = connected_cb,
	.disconnected = disconnected_cb,
	.remote_info_available = remote_info_available_cb,
};

static void device_found(const bt_addr_le_t *addr, int8_t rssi, uint8_t type,
						 struct net_buf_simple *ad)
{
	if (!scanning_enabled)
	{
		return;
	}

	if (!name_matches(ad))
	{
		return;
	}
	k_mutex_lock(&results_mutex, K_FOREVER);
	if (scan_result_count < MAX_SCAN_RESULTS &&
		!addr_already_present(addr))
	{

		bt_addr_le_copy(&scan_results[scan_result_count].addr, addr);
		scan_results[scan_result_count].rssi = rssi;
		scan_result_count++;

		char addr_str[BT_ADDR_LE_STR_LEN];
		bt_addr_le_to_str(addr, addr_str, sizeof(addr_str));
		APP_LOG("Matched device %d/%d: %s rssi %d\n",
				scan_result_count, MAX_SCAN_RESULTS, addr_str, rssi);

		if (scan_result_count >= MAX_SCAN_RESULTS)
		{
			k_sem_give(&scan_done_sem); /* early exit: 20 found */
		}
	}

	k_mutex_unlock(&results_mutex);
}

/* ---- Push collected results to msgq ---- */

static void flush_results_to_queue(void)
{
	k_sleep(K_SECONDS(2)); /* check again periodically */
	k_mutex_lock(&results_mutex, K_FOREVER);
	for (int i = 0; i < scan_result_count; i++)
	{
		int ret = k_msgq_put(&scan_result_msgq, &scan_results[i], K_NO_WAIT);
		if (ret != 0)
		{
			APP_LOG("msgq full, dropping result %d (err %d)\n", i, ret);
		}
	}

	APP_LOG("Flushed %d results to queue\n", scan_result_count);
	scan_result_count = 0;

	k_mutex_unlock(&results_mutex);
}

static uint8_t discover_func(struct bt_conn *conn, const struct bt_gatt_attr *attr,
							 struct bt_gatt_discover_params *params)
{
	struct wdisc_worker *self = CONTAINER_OF(params, struct wdisc_worker, discover_params);

	if (!attr)
	{
		k_sem_give(&self->sem_discovered);
		return BT_GATT_ITER_STOP;
	}

	struct bt_gatt_chrc *chrc = (struct bt_gatt_chrc *)attr->user_data;
	if (!bt_uuid_cmp(chrc->uuid, &pawr_char_uuid.uuid))
	{
		self->pawr_attr_handle = chrc->value_handle;
		k_sem_give(&self->sem_discovered);
	}

	return BT_GATT_ITER_STOP;
}

static void write_func(struct bt_conn *conn, uint8_t err, struct bt_gatt_write_params *params)
{
	struct wdisc_worker *self = CONTAINER_OF(params, struct wdisc_worker, write_params);
	if (!err)
	{
		k_sem_give(&self->sem_written);
	}
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
				proto_command_active = false;
				proto_len = 0;

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

void scan_thread(void *p1, void *p2, void *p3)
{
	ARG_UNUSED(p1);
	ARG_UNUSED(p2);
	ARG_UNUSED(p3);

	const char *tag_name = "SCAN_THREAD";
	APP_LOG("%s :  Scanning Thread Started \n", tag_name);
	scanning_enabled = true;
	k_mutex_init(&results_mutex);

	while (1)
	{
		/* Don't scan if all slots are already allocated */
		if (num_synced >= MAX_SYNCS)
		{
			APP_LOG("%s : All %d slots full, pausing scan\n", tag_name, MAX_SYNCS);
			k_sleep(K_SECONDS(2)); /* check again periodically */
			continue;
		}

		bool queue_empty = (k_msgq_num_used_get(&scan_result_msgq) == 0);
		if (!queue_empty)
		{
			/* Block here until either queue drains or someone forces a restart */
			k_sem_take(&scan_restart_sem, K_FOREVER);
		}
		k_sem_reset(&scan_done_sem);
		scan_result_count = 0;

		int err;
		for (;;)
		{
			k_mutex_lock(&radio_mutex, K_FOREVER);

			if (!atomic_get(&conn_activity) && !connect_in_progress())
			{
				/* Radio is free — start scan while still holding the lock */
				scanning_enabled = true;
				err = bt_le_scan_start(BT_LE_SCAN_PASSIVE_CONTINUOUS,
									   device_found);
				k_mutex_unlock(&radio_mutex);
				break;
			}

			/* Radio busy — release lock, wait for gatt_thread's signal,
			 * then re-check (timeout covers zombie links winding down) */
			k_mutex_unlock(&radio_mutex);
			k_sem_take(&radio_free_sem, K_MSEC(500));
		}

		if (err)
		{
			APP_LOG("%s :  bt_le_scan_start failed (err %d) \n", tag_name, err);
			k_sleep(K_SECONDS(1));
			continue;
		}

		APP_LOG("%s : Scan window started (%ds max, 20 devices max) \n", tag_name, SCAN_WINDOW_SECONDS);

		/* Wait for either: 20 devices found, or 5s timeout */
		k_sem_take(&scan_done_sem, K_SECONDS(SCAN_WINDOW_SECONDS));
		scanning_enabled = false;
		bt_le_scan_stop();
		APP_LOG("%s :Scan window ended, %d device(s) collected\n", tag_name, scan_result_count);

		if (scan_result_count > 0)
		{
			flush_results_to_queue();
		}
	}
}

/* One connect→onboard→disconnect cycle. Cleanup is the CALLER's job. */
static void process_scan_item(struct scan_result_t *item, const char *addr_str)
{
	struct bt_conn *new_conn = NULL;
	int err;

	k_sem_reset(&sem_connected);
	k_sem_reset(&sem_disconnected);

	k_mutex_lock(&radio_mutex, K_FOREVER);
	atomic_set(&conn_activity, 1);
	scanning_enabled = false;
	bt_le_scan_stop(); /* kills any scan that snuck in; -EALREADY harmless */

	err = bt_conn_le_create(&item->addr, fast_create_param,
							fast_conn_param, &new_conn);
	k_mutex_unlock(&radio_mutex); /* unconditional — before any return */

	if (err)
	{
		APP_LOG("Create conn failed for %s (%d): %s\n",
				addr_str, err, strerror(-err));
		return;
	}

	if (k_sem_take(&sem_connected, K_SECONDS(10)) != 0)
	{
		APP_LOG("Connect confirmation timeout for %s\n", addr_str);
		if (new_conn)
		{
			bt_conn_disconnect(new_conn, BT_HCI_ERR_REMOTE_USER_TERM_CONN);
			k_sem_take(&sem_disconnected, K_SECONDS(3));
		}
		return;
	}

	if (new_conn == NULL)
	{
		APP_LOG("Connection to %s failed (handled in connected_cb)\n", addr_str);
		return;
	}

	APP_LOG("Connect succeeded for %s, handed off to write_disconnect\n", addr_str);
	if (k_sem_take(&sem_disconnected, K_SECONDS(30)) != 0)
	{
		APP_LOG("Disconnect confirmation timeout for %s — proceeding anyway\n",
				addr_str);
	}
}

void gatt_thread(void *p1, void *p2, void *p3)
{
	ARG_UNUSED(p1);
	ARG_UNUSED(p2);
	ARG_UNUSED(p3);

	APP_LOG("GATT THREAD STARTED, Will Wait till Scanning Thread fills the Queqe \n");
	struct scan_result_t item;
	char addr_str[BT_ADDR_LE_STR_LEN];
	while (1)
	{
		int ret = k_msgq_get(&scan_result_msgq, &item, K_FOREVER);
		if (ret == 0)
		{
			bt_addr_le_to_str(&item.addr, addr_str, sizeof(addr_str));
			APP_LOG("Consumed: %s  RSSI: %d  (queue remaining: %d)\n",
					addr_str, item.rssi,
					k_msgq_num_used_get(&scan_result_msgq));

			process_scan_item(&item, addr_str);

			atomic_set(&conn_activity, 0);
			k_sem_give(&radio_free_sem);

			if (k_msgq_num_used_get(&scan_result_msgq) == 0)
			{
				k_sem_give(&scan_restart_sem);
			}
		}
	}
}

static void wdisc_process_job(struct wdisc_worker *self, struct wdisc_job *job)
{
	char addr_str[BT_ADDR_LE_STR_LEN];
	bt_addr_le_to_str(&job->addr, addr_str, sizeof(addr_str));
	APP_LOG("wdisc worker %d: started for %s\n", self->id, addr_str);

	k_sem_reset(&self->sem_remote_info);
	if (k_sem_take(&self->sem_remote_info, K_SECONDS(10)) != 0)
	{
		APP_LOG("Remote info not available in time for %s, trying PAST anyway\n", addr_str);
	}

	if (!self->conn)
	{
		APP_LOG("No active connection for %s — aborting\n", addr_str);
		return;
	}

	int err;
	bool proceed = true;
	int slot_idx = -1;

	if (!wait_for_connected_state(self->conn, CONN_WAIT_TIMEOUT_MS))
	{
		APP_LOG("Connection did not reach CONNECTED state in time\n");

		int derr = bt_conn_disconnect(self->conn, BT_HCI_ERR_REMOTE_USER_TERM_CONN);
		if (derr)
		{
			APP_LOG("Disconnect call failed for %s (err %d) — likely already down\n",
					addr_str, derr);
		}
		bt_conn_unref(self->conn);
		self->conn = NULL;

		k_sem_give(&sem_disconnected); /* signal AFTER this thread is truly done */
		return;
	}

	/* ---- STEP 1: PAST ---- */
	err = bt_le_per_adv_set_info_transfer(pawr_adv, self->conn, 0);
	if (err)
	{
		APP_LOG("PAST failed for %s (err %d)\n", addr_str, err);
		/* not fatal — continue to discover anyway */
	}
	else
	{
		APP_LOG("PAST sent for %s\n", addr_str);
	}

	k_sem_give(&sem_disconnected);
	/* ---- STEP 2: GATT DISCOVER ---- */
	if (proceed)
	{
		memset(&self->discover_params, 0, sizeof(self->discover_params));
		self->discover_params.uuid = &pawr_char_uuid.uuid;
		self->discover_params.func = discover_func;
		self->discover_params.start_handle = BT_ATT_FIRST_ATTRIBUTE_HANDLE;
		self->discover_params.end_handle = BT_ATT_LAST_ATTRIBUTE_HANDLE;
		self->discover_params.type = BT_GATT_DISCOVER_CHARACTERISTIC;

		self->pawr_attr_handle = 0;
		k_sem_reset(&self->sem_discovered);

		err = bt_gatt_discover(self->conn, &self->discover_params);
		if (err)
		{
			APP_LOG("Discovery start failed for %s (err %d)\n", addr_str, err);
			proceed = false;
		}
		else if (!conn_is_live(self->conn))
		{
			APP_LOG("Discovery aborted for %s — connection dropped before wait\n", addr_str);
			proceed = false;
		}
		else if (k_sem_take(&self->sem_discovered, K_SECONDS(10)) != 0)
		{
			APP_LOG("Discovery timed out for %s\n", addr_str);
			proceed = false;
		}
		else if (!conn_is_live(self->conn))
		{ // <-- ADD this second check
			APP_LOG("Discovery aborted for %s — connection dropped during wait\n", addr_str);
			proceed = false;
		}
		else if (self->pawr_attr_handle == 0)
		{
			APP_LOG("Characteristic not found for %s\n", addr_str);
			proceed = false;
		}
		else
		{
			APP_LOG("Discovery succeeded for %s, handle = %d\n", addr_str, self->pawr_attr_handle);
		}
	}

	/* ---- STEP 3: ASSIGN SLOT + WRITE CONFIG ---- */
	if (proceed)
	{
		uint8_t subevent = 0, response_slot = 0;
		slot_idx = find_or_assign_slot(addr_str, &subevent, &response_slot);

		if (slot_idx < 0)
		{
			APP_LOG("No slot available for %s\n", addr_str);
			proceed = false;
		}
		else
		{
			struct pawr_timing sync_config;
			sync_config.subevent = subevent;
			sync_config.response_slot = response_slot;

			memset(&self->write_params, 0, sizeof(self->write_params));
			self->write_params.func = write_func;
			self->write_params.handle = self->pawr_attr_handle;
			self->write_params.offset = 0;
			self->write_params.data = &sync_config;
			self->write_params.length = sizeof(sync_config);

			k_sem_reset(&self->sem_written);

			err = bt_gatt_write(self->conn, &self->write_params);
			if (err)
			{
				APP_LOG("Write start failed for %s (err %d)\n", addr_str, err);
				clear_slot(slot_idx);
				proceed = false;
			}
			else if (k_sem_take(&self->sem_written, K_SECONDS(10)) != 0)
			{
				APP_LOG("Write timed out for %s\n", addr_str);
				clear_slot(slot_idx);
				proceed = false;
			}
			else
			{
				synced_devices[slot_idx].last_sync_time = k_uptime_get();
				synced_devices[slot_idx].last_response_time = 0;
				APP_LOG("PAwR config written for %s (subevent %d, slot %d)\n",
						addr_str, subevent, response_slot);
			}
		}
	}

	if (proceed)
	{
		int64_t write_time = k_uptime_get();
		int64_t sync_wait_timeout_ms = 6000;
		bool got_response = false;

		APP_LOG("Waiting for PAwR sync confirmation from %s...\n", addr_str);

		while (k_uptime_get() - write_time < sync_wait_timeout_ms)
		{
			if (synced_devices[slot_idx].last_response_time > write_time)
			{
				got_response = true;
				APP_LOG("PAwR sync confirmed for %s (took %lld ms)\n",
						addr_str, k_uptime_get() - write_time);
				break;
			}
			if (!conn_is_live(self->conn))
			{
				APP_LOG("PAwR sync wait aborted for %s — connection dropped\n", addr_str);
				break;
			}
			k_sleep(K_MSEC(100));
		}
		if (!got_response)
		{
			APP_LOG("WARNING: No PAwR response from %s within %lld ms — "
					"sync may not be established\n",
					addr_str, sync_wait_timeout_ms);
		}
	}

	/* ---- STEP 4: DISCONNECT — always runs, regardless of proceed state ---- */
	if (conn_is_live(self->conn))
	{
		err = bt_conn_disconnect(self->conn, BT_HCI_ERR_REMOTE_USER_TERM_CONN);
		if (err)
		{
			APP_LOG("Disconnect call failed for %s (err %d)\n", addr_str, err);
		}
		else
		{
			APP_LOG("Disconnect requested for %s\n", addr_str);
			/* wait for the disconnect to actually complete before unref'ing,
			 * so the peer's conn slot is fully freed before the next
			 * connection attempt to this same address */
			int wait_ms = 0;
			while (conn_is_live(self->conn) && wait_ms < 2000)
			{
				k_sleep(K_MSEC(50));
				wait_ms += 50;
			}
		}
	}
	else
	{
		APP_LOG("Conn for %s already down, skipping disconnect call\n", addr_str);
	}

	bt_conn_unref(self->conn);
	self->conn = NULL;

	APP_LOG("wdisc worker %d: finished for %s\n", self->id, addr_str);
	// k_sem_give(&sem_disconnected);   /* signal AFTER this thread is truly done */
}

void wdisc_worker_thread(void *p1, void *p2, void *p3)
{
	ARG_UNUSED(p1);
	ARG_UNUSED(p2);
	ARG_UNUSED(p3);

	struct wdisc_worker *self = p1;
	struct wdisc_job job;

	APP_LOG("wdisc worker %d ready\n", self->id);

	while (1)
	{
		k_msgq_get(&wdisc_job_q, &job, K_FOREVER);
		APP_LOG("Received data is : ");

		self->conn = job.conn;
		wdisc_process_job(self, &job);
		self->conn = NULL;
	}
}

void wdisc_pool_init(int n)
{
	if (n > WDISC_POOL_MAX)
		n = WDISC_POOL_MAX;

	for (int i = 0; i < n; i++)
	{
		struct wdisc_worker *w = &wdisc_workers[i];

		w->id = i;
		w->conn = NULL;
		w->pawr_attr_handle = 0;
		k_sem_init(&w->sem_discovered, 0, 1);
		k_sem_init(&w->sem_written, 0, 1);
		k_sem_init(&w->sem_remote_info, 0, 1);

		w->tid = k_thread_create(&w->thread, wdisc_stacks[i], WDISC_THREAD_STACK_SIZE,
								 wdisc_worker_thread, w, NULL, NULL,
								 WDISC_THREAD_PRIORITY, 0, K_NO_WAIT);

		char name[16];
		snprintf(name, sizeof(name), "wdisc%d", i);
		k_thread_name_set(w->tid, name);
	}
	wdisc_pool_size = n;
}

void main_thread(void *p1, void *p2, void *p3)
{
	ARG_UNUSED(p1);
	ARG_UNUSED(p2);
	ARG_UNUSED(p3);

	APP_LOG("Maintenance thread started (will cleanup inactive slots)\n");

	while (1)
	{
		k_sleep(K_SECONDS(60));
		cleanup_inactive_slots();
	}
}

int app_initilisation(void)
{
	int err;
	uint8_t flag = 0;

	APP_LOG("APPLICATION STARTED 2\n");

	init_bufs();
	err = nvs_init_app();
	if (err)
	{
		APP_LOG("NVS initialization failed (err %d)\n", err);
		return 0;
	}

	uart_dev = DEVICE_DT_GET(DT_NODELABEL(uart20));
	if (!device_is_ready(uart_dev)){
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

	ssize_t len = nvs_read(&fs, NVS_ID_MCUMGR_MODE, &flag, sizeof(flag));
	if (len > 0 && flag == 1)
	{
		printk("MCUmgr boot\n");
		flag = 0;
		nvs_write(&fs, NVS_ID_MCUMGR_MODE, &flag, sizeof(flag));
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

	wdisc_pool_init(WDISC_POOL_SIZE);
	k_mutex_init(&radio_mutex);
	k_mutex_init(&synced_devices_mutex);

	return 1;
}

int main(void)
{
	if (app_initilisation())
	{
		APP_LOG("Application Initialised Successfully \n \n");
	}
	else
	{
		APP_LOG("Application Initialised Failed \n \n");
	}

	k_thread_create(&scan_thread_data, scan_thread_stack, SCAN_THREAD_STACK_SIZE,
					scan_thread, NULL, NULL, NULL,
					SCAN_THREAD_PRIORITY, 0, K_NO_WAIT);

	k_thread_create(&gatt_thread_data, gatt_thread_stack, GATT_THREAD_STACK_SIZE,
					gatt_thread, NULL, NULL, NULL,
					GATT_THREAD_PRIORITY, 0, K_NO_WAIT);

	k_thread_create(&join_thread_data, join_thread_stack, JOIN_THREAD_STACK_SIZE,
					join_command, pawr_adv, NULL, NULL,
					JOIN_THREAD_PRIORITY, 0, K_NO_WAIT);

	k_thread_create(&main_thread_data, main_thread_stack, MAIN_THREAD_STACK_SIZE,
					main_thread, NULL, NULL, NULL,
					MAIN_THREAD_PRIORITY, 0, K_NO_WAIT);

	while (1)
	{
		static int status_counter = 0;
		if (++status_counter >= 12)
		{
			status_counter = 0;
			APP_LOG("System status: %d synced devices active, waiting for commands...\n", num_synced);
			APP_LOG("Current command: %s | temp_active: %s\n", current_command,
					temp_command_active ? "true" : "false");
		}
		cleanup_inactive_slots();
		k_sleep(K_SECONDS(5));
	}

	/* ---- rest of function unchanged ---- */
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
					i, id_str, synced_devices[i].subevent,
					synced_devices[i].response_slot, synced_devices[i].address);
		}
	}
	APP_LOG("============================\n\n");

	return 0;
}