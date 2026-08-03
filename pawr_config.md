# PAwR Configuration for 300 Devices

## Overview

This configuration is designed for **Bluetooth Periodic Advertising with
Responses (PAwR)** and provides **300 response opportunities** by using:

-   **20 subevents**
-   **15 response slots per subevent**

Total capacity:

``` text
20 × 15 = 300 devices
```

------------------------------------------------------------------------

## Configuration

``` c
#define NUM_SUBEVENTS     20
#define NUM_RSP_SLOTS     15

static const struct bt_le_per_adv_param per_adv_params = {
    .interval_min          = 0x2800,
    .interval_max          = 0x2800,
    .options               = 0,

    .num_subevents         = NUM_SUBEVENTS,
    .subevent_interval     = 0x200,

    .response_slot_delay   = 0x10,
    .response_slot_spacing = 0x20,

    .num_response_slots    = NUM_RSP_SLOTS,
};
```

------------------------------------------------------------------------

# Timing Parameter Explanation

## 1. interval_min / interval_max

``` c
.interval_min = 0x2800
.interval_max = 0x2800
```

**Purpose**

Defines how often the Access Point (AP) starts a new PAwR event.

**Calculation**

    0x2800 = 12800 units
    1 unit = 1.25 ms

    12800 × 1.25 = 16000 ms = 16 seconds

**Why is it used?**

This is the complete communication cycle. Every 16 seconds the AP begins
a new PAwR event and all devices get another opportunity to communicate.

Timeline

    0 s --------16 s--------32 s--------48 s
         Event 1    Event 2    Event 3

------------------------------------------------------------------------

## 2. num_subevents

``` c
.num_subevents = 20
```

**Purpose**

Divides one PAwR event into 20 smaller communication windows.

**Why is it used?**

Instead of allowing 300 devices to respond together, they are divided
into 20 groups.

    Event

    Sub0
    Sub1
    Sub2
    ...
    Sub19

Each group has its own response window, reducing collisions.

------------------------------------------------------------------------

## 3. subevent_interval

``` c
.subevent_interval = 0x200
```

**Calculation**

    0x200 = 512

    512 × 1.25 = 640 ms

**Purpose**

Time between the start of two consecutive subevents.

**Why is it used?**

It gives enough time for all response slots in one subevent to finish
before the next subevent starts.

Timeline

    Sub0

    640 ms

    Sub1

    640 ms

    Sub2

------------------------------------------------------------------------

## 4. response_slot_delay

``` c
.response_slot_delay = 0x10
```

**Calculation**

    0x10 = 16

    16 × 1.25 = 20 ms

**Purpose**

Wait time after the AP transmits before the first device is allowed to
respond.

**Why is it used?**

The AP needs time to switch from transmitting to receiving. Without this
delay, responses may be missed.

    AP TX

    20 ms wait

    Slot 0 opens

------------------------------------------------------------------------

## 5. response_slot_spacing

``` c
.response_slot_spacing = 0x20
```

**Calculation**

    0x20 = 32

    32 × 1.25 = 40 ms

**Purpose**

Defines the time between consecutive response slots.

**Why is it used?**

Each device gets its own transmission window, preventing two devices
from transmitting simultaneously.

    Slot0

    40 ms

    Slot1

    40 ms

    Slot2

------------------------------------------------------------------------

## 6. num_response_slots

``` c
.num_response_slots = 15
```

**Purpose**

Specifies how many devices can respond in one subevent.

Example

    Subevent 0

    Slot0 -> Device1
    Slot1 -> Device2
    ...
    Slot14 -> Device15

**Why is it used?**

Increasing this value allows more devices to respond in the same
subevent, but it also increases the response window length.

------------------------------------------------------------------------

# Total Capacity

    20 subevents
    ×

    15 response slots

    =

    300 response opportunities

Each device is assigned one unique combination of:

-   Subevent
-   Response Slot

so that no two devices transmit at the same time.

------------------------------------------------------------------------

# Summary

  Parameter               Meaning                         Configured Value
  ----------------------- ----------------------------- ------------------
  interval_min/max        Time between PAwR events                    16 s
  num_subevents           Number of groups                              20
  subevent_interval       Time between groups                       640 ms
  response_slot_delay     Delay before first response                20 ms
  response_slot_spacing   Time between slots                         40 ms
  num_response_slots      Slots per group                               15
  Total capacity          Subevents × Slots                    300 devices
