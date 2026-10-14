# UVL on a Raspberry Pi Pico (RP2040) or Pico 2 (RP2350) with an ST7789 SPI display.
#
#   baremetal/tools/test.sh            # or uvl_bundle.py: produces .lake/baremetal/bundle
#   cmake -S baremetal/pico -B build/pico -G Ninja \
#         -DPICO_SDK_PATH=/path/to/pico-sdk -DUVL_BUNDLE=$PWD/.lake/baremetal/bundle \
#         [-DPICO_BOARD=pico2]
#   cmake --build build/pico           # -> build/pico/uvl_pico.uf2
#
# Pin and panel settings are compile definitions; the defaults match the
# Waveshare Pico-LCD-2 (320x240 ST7789VW, four keys). See config.h.
cmake_minimum_required(VERSION 3.13)

if(NOT DEFINED PICO_SDK_PATH AND DEFINED ENV{PICO_SDK_PATH})
  set(PICO_SDK_PATH $ENV{PICO_SDK_PATH})
endif()
include(${PICO_SDK_PATH}/external/pico_sdk_import.cmake)

project(uvl_pico C CXX ASM)
pico_sdk_init()

if(NOT UVL_BUNDLE)
  message(FATAL_ERROR "Pass -DUVL_BUNDLE=<dir> (the output directory of baremetal/tools/uvl_bundle.py)")
endif()
include(${UVL_BUNDLE}/uvl_bundle.cmake)

set(UVL_HEAP_SIZE 98304 CACHE STRING "Bytes of SRAM for the Lean object pool")

add_executable(uvl_pico main.c st7789.c ${UVL_BUNDLE_SOURCES})
# The bundle's lean/config.h must shadow the toolchain's; generated code is not warning-clean.
target_include_directories(uvl_pico BEFORE PRIVATE ${UVL_BUNDLE_INCLUDE} ${CMAKE_CURRENT_LIST_DIR})
set_source_files_properties(${UVL_BUNDLE_SOURCES} PROPERTIES COMPILE_OPTIONS "-w;-O2")
target_compile_definitions(uvl_pico PRIVATE UVL_HEAP_SIZE=${UVL_HEAP_SIZE})
target_link_libraries(uvl_pico pico_stdlib hardware_spi hardware_dma)
pico_enable_stdio_uart(uvl_pico 1)
pico_enable_stdio_usb(uvl_pico 0)
pico_add_extra_outputs(uvl_pico)
