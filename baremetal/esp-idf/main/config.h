/* Board configuration: an ESP32 DevKit wired to a 320x240 ST7789 module. */
#pragma once

#define LCD_HOST SPI2_HOST
#define LCD_PIXEL_CLOCK_HZ (40 * 1000 * 1000)
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

/* Keys (active low, internal pull-ups). GPIO 0 is the BOOT button. */
#define PIN_KEY_UP 0
#define PIN_KEY_DOWN 35
#define PIN_KEY_ENTER 34

#define TILE_W 64
#define TILE_H 16
