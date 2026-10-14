# UVL on an ESP32 with an ST7789 SPI display (ESP-IDF 5.x).
#
#   baremetal/tools/test.sh                    # produces .lake/baremetal/bundle
#   export UVL_BUNDLE=$PWD/.lake/baremetal/bundle
#   cd baremetal/esp-idf && idf.py set-target esp32 && idf.py build flash monitor
#
# Pins and panel settings are in main/config.h.
cmake_minimum_required(VERSION 3.16)
include($ENV{IDF_PATH}/tools/cmake/project.cmake)
project(uvl_esp32)
