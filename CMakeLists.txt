cmake_minimum_required(VERSION 3.20.0)
find_package(Zephyr REQUIRED HINTS $ENV{ZEPHYR_BASE})

project(NRF54L15_XIAO_AP_PAWR)

target_sources(app PRIVATE src/main.c)
