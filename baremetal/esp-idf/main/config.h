/*
 * Board configuration, selected with CONFIG_UVL_BOARD_* (menu "UVL board" in
 * `idf.py menuconfig`, or boards/<board>.defaults).
 */
#pragma once

#include "sdkconfig.h"

#define LCD_HOST SPI2_HOST
#define LCD_PIXEL_CLOCK_HZ (40 * 1000 * 1000)

#if CONFIG_UVL_BOARD_TDISPLAY
/* LilyGO T-Display: 1.14" ST7789V, 135x240 window of a 240x320 controller,
   used in landscape. Buttons: GPIO 0 (BOOT) and GPIO 35, with external pull-ups. */
#define PIN_LCD_SCLK 18
#define PIN_LCD_MOSI 19
#define PIN_LCD_CS 5
#define PIN_LCD_DC 16
#define PIN_LCD_RST 23
#define PIN_LCD_BL 4

#define LCD_WIDTH 240
#define LCD_HEIGHT 135
// Landscape, MADCTL MV|MY (TFT_eSPI rotation 3). The 135x240
// glass sits inside the controller's 240x320 RAM, hence the gaps.
#define LCD_SWAP_XY 1
#define LCD_MIRROR_X 0
#define LCD_MIRROR_Y 1
#define LCD_INVERT 1
#define LCD_GAP_X 40
#define LCD_GAP_Y 52

#define KEYS {0, UVL_KEY_DOWN}, {35, UVL_KEY_UP}
#else
/* ESP32 DevKit wired to a 320x240 ST7789 module. */
#define PIN_LCD_SCLK 18
#define PIN_LCD_MOSI 23
#define PIN_LCD_CS 5
#define PIN_LCD_DC 16
#define PIN_LCD_RST 17
#define PIN_LCD_BL 4

#define LCD_WIDTH 320
#define LCD_HEIGHT 240
#define LCD_SWAP_XY 1
#define LCD_MIRROR_X 1
#define LCD_MIRROR_Y 0
#define LCD_INVERT 1
#define LCD_GAP_X 0
#define LCD_GAP_Y 0

/* GPIO 0 is the BOOT button. */
#define KEYS {0, UVL_KEY_UP}, {35, UVL_KEY_DOWN}, {34, UVL_KEY_ENTER}
#endif

/* Keys are active low. GPIOs 34-39 are input-only and have no internal
   pull-ups, so those buttons need external ones. */

#define TILE_W 64
#define TILE_H 16
