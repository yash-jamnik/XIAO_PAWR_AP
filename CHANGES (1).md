# Firmware Change Log — PAwR Onboarding & Response Handling

**File:** `main.c` (Zephyr PAwR sample application)
**Summary:** Five fixes addressing bus faults during/after onboarding, silent device drops requiring re-onboarding, and slow onboarding time.

---

## 1. Connection Reference Race Fix (`main()`)

### Problem
`default_conn` was a shared global `struct bt_conn *`, written by `device_found()`, `connected_cb()`, and `disconnected_cb()`, while the onboarding loop in `main()` read and dereferenced it across a long sequence of blocking operations (PAST transfer, GATT discovery, GATT write, multiple `k_sleep()` calls spanning several seconds).

Because `disconnected_cb()` runs in BT stack callback context and can fire at any time, this created a check-then-use race (TOCTOU): `default_conn` could go from valid to `NULL`/freed between a null check and its actual use a few lines later — a use-after-free on the connection object, and a plausible direct cause of the bus faults observed during onboarding.

### Fix
A locally owned, reference-counted connection pointer (`conn`) is now taken exactly once per onboarding iteration, immediately after `sem_connected` succeeds:

```c
k_sched_lock();
conn = default_conn ? bt_conn_ref(default_conn) : NULL;
k_sched_unlock();
```

Every subsequent operation in that iteration (`bt_le_per_adv_set_info_transfer`, `bt_gatt_discover`, `bt_conn_get_dst`, `bt_gatt_write`, `bt_conn_disconnect`) now uses `conn`, not `default_conn`. `conn` is explicitly `bt_conn_unref()`'d and set to `NULL` on every exit path of the loop (normal completion, `disconnect:` fallthrough, disconnect-failure branch, disconnect-timeout branch), so reference counting stays balanced with no leaks or double-frees.

### Result
The connection object used throughout one onboarding sequence is now guaranteed valid for the full duration of that sequence, regardless of what the BT stack does to the global `default_conn` in the background. This closes the most likely cause of bus faults occurring *during* onboarding.

**Note:** relies on `k_sched_lock()`, which protects against preemption by another thread on the same core but not against ISR context or a second core on SMP targets. Correct and sufficient for single-core targets (e.g. nRF52-series).

---

## 2. Stack Buffer Overflow Fix (`response_cb()`)

### Problem
```c
size_t copy_len = MIN(buf->len - 3, sizeof(mac) - 1);
memcpy(mac, buf->data + 3, copy_len);
mac[copy_len] = '\0';
mac[buf->len - 3] = '\0';   // <-- unclamped, removed
```
The second null-terminator write used the raw, unclamped `buf->len - 3` instead of the clamped `copy_len`. Any `"OK,"`-prefixed peer response longer than 23 bytes of payload (buffer `mac[24]`) wrote past the end of the stack buffer — a stack overflow triggerable by a single oversized response, independent of onboarding state. This was the most likely cause of bus faults occurring *after* onboarding completed, during normal PAwR response traffic.

### Fix
The unclamped line was deleted. `mac[copy_len] = '\0'` alone correctly and safely terminates the string, since `copy_len` is guaranteed `<= sizeof(mac) - 1` by the `MIN()` clamp.

### Result
Oversized `"OK,<mac>"` responses are now safely truncated instead of corrupting the stack. Normal-length responses are unaffected.

---

## 3. `active_cmd` / `current_command` Divergence Fix (Device Drop / Forced Re-onboarding)

### Problem
Two separate code paths existed for sending an `"ACTIVE,<mac>"` recovery ping to a stale device:

- `cleanup_inactive_slots()` wrote the ping into `current_command`.
- `request_cb()`'s text-transmit branch, however, sent a **different** global buffer, `active_cmd`, which was only ever populated by the now-unused `[+]active,<mac>` UART command handler via `prepare_active_command()`.

As a result, the automatic stale-device recovery ping built by `cleanup_inactive_slots()` was **never actually transmitted** — `request_cb` kept sending whatever was last in `active_cmd` (often stale or empty). The targeted device never received the check, never responded, the recovery timeout expired, and `clear_slot()` dropped it — forcing a full re-onboard even though the device may have still been reachable.

### Fix
- `request_cb()` changed to send `cmd_local` (built from `current_command`) instead of `active_cmd`.
- `active_cmd`, `active_cmd_len`, and `prepare_active_command()` were removed entirely.
- The `[+]active,<mac>` UART command handler now writes directly into `current_command` via `snprintf`, matching what `cleanup_inactive_slots()` already does.

### Result
Both the manual `[+]active,<mac>` command and the automatic maintenance-thread recovery check now go through the single, same path (`current_command` → `cmd_local` → transmitted), eliminating the divergence and the resulting false device drops.

---

## 4. Protobuf Command Shadowing Fix (`cleanup_inactive_slots()`)

### Problem
`request_cb()` always prioritizes an active protobuf command over any text command:
```c
if (proto_command_active && proto_len > 0) { /* send proto_buf */ }
else { /* send text command, e.g. ACTIVE ping */ }
```
If a protobuf command (LED/TEL/OTA/SPLASH/CLEAR/JOIN) was still marked active when `cleanup_inactive_slots()` armed an `"ACTIVE,<mac>"` recovery ping for a different, unrelated stale device, the stale protobuf state kept winning in `request_cb()`. The ACTIVE ping was built and logged as "sent," but never actually transmitted over the air — leading to the same silent device-drop failure mode as issue #3, triggered whenever a manual command and an automatic recovery check happened to overlap in time.

### Fix
Two lines added in `cleanup_inactive_slots()`, immediately after building the ACTIVE command string and before re-arming `temp_command_active`:

```c
proto_command_active = false;
proto_len = 0;
```

### Result
Any lingering protobuf command is now forcibly cleared whenever an ACTIVE recovery check is armed, guaranteeing the recovery ping actually transmits instead of being silently shadowed. This closes the last known path to unnecessary device drops / forced re-onboarding.

---

## 5. Onboarding Delay Reduction (Performance)

### Problem
The onboarding loop in `main()` contained six sequential fixed `k_sleep()` calls per device, totaling roughly **18.2 seconds** of pure wait time per device before counting semaphore waits (connect, discovery, write). At scale (up to `MAX_SYNCS` = 150 devices), this dominated total onboarding time.

### Fix
Four of the six delays — identified as conservative/arbitrary padding rather than delays tied to actual BLE controller or periodic-advertising timing — were reduced:

| Location | Old | New |
|---|---|---|
| Before PAST transfer | `K_MSEC(300)` | `K_MSEC(150)` |
| After GATT write success | `K_MSEC(2000)` | `K_MSEC(500)` |
| Immediately before `bt_conn_disconnect()` | `K_MSEC(4000)` | `K_MSEC(800)` |
| End of loop, before next onboarding attempt | `K_MSEC(1200)` | `K_MSEC(400)` |

Two delays were deliberately **left unchanged**, since they are tied to real BLE timing rather than arbitrary padding:
- **3000ms after PAST sent** — gives the peer time to actually receive and begin processing the Periodic Advertising Sync Transfer before GATT discovery starts.
- **`per_adv_params.interval_max * 2` (~7680ms) before disconnect** — ensures the peer has had time to sync onto the periodic advertising train before the connection is dropped.

### Result
Approximately **5.65 seconds saved per device** onboarded, with low risk to onboarding reliability since only non-BLE-timing-dependent padding was reduced. The two delays most likely to affect actual sync success were intentionally left untouched.

**Recommended follow-up:** validate onboarding success rate over multiple runs with several devices onboarding back-to-back before considering further reduction of the two remaining (PAST-settle and pre-disconnect interval) delays — these are the ones most likely to reintroduce intermittent onboarding failures if cut too aggressively.

---

## Summary Table

| # | Fix | Symptom addressed | Type |
|---|---|---|---|
| 1 | Local ref-counted `conn` in `main()` | Bus faults during onboarding | Use-after-free / concurrency |
| 2 | Removed unclamped terminator in `response_cb()` | Bus faults after onboarding, during normal response traffic | Stack buffer overflow |
| 3 | Unified `active_cmd` → `current_command` | Devices silently dropped, requiring re-onboarding | Logic bug (dead code path) |
| 4 | Clear `proto_command_active`/`proto_len` in `cleanup_inactive_slots()` | Devices silently dropped when a manual command overlapped a recovery check | Logic bug (command precedence) |
| 5 | Reduced 4 of 6 onboarding delays | Slow onboarding time | Performance |


