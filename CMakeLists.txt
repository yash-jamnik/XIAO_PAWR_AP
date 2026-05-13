cmake_minimum_required(VERSION 3.20.0)
find_package(Zephyr REQUIRED HINTS $ENV{ZEPHYR_BASE})

project(NRF54L15_XIAO_AP_PAWR)
list(APPEND CMAKE_MODULE_PATH ${ZEPHYR_BASE}/modules/nanopb)
include(nanopb)
zephyr_nanopb_sources(app src/command.proto)

# zephyr_nanopb_sources(app src/simple.proto)

FILE(GLOB app_sources src/*.c)
target_sources(app PRIVATE ${app_sources})