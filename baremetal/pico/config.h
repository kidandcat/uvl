/* Board configuration. Defaults: Waveshare Pico-LCD-2 (ST7789VW, 320x240 landscape). */
#pragma once

#ifndef LCD_SPI
#define LCD_SPI spi1
#endif
#ifndef LCD_SPI_HZ
#define LCD_SPI_HZ (62500 * 1000)
#endif
#ifndef PIN_LCD_SCK
#define PIN_LCD_SCK 10
#endif
#ifndef PIN_LCD_MOSI
#define PIN_LCD_MOSI 11
#endif
#ifndef PIN_LCD_CS
#define PIN_LCD_CS 9
#endif
#ifndef PIN_LCD_DC
#define PIN_LCD_DC 8
#endif
#ifndef PIN_LCD_RST
#define PIN_LCD_RST 12
#endif
#ifndef PIN_LCD_BL
#define PIN_LCD_BL 13
#endif

/* Panel geometry after rotation, and the MADCTL value that produces it. */
#ifndef LCD_WIDTH
#define LCD_WIDTH 320
#endif
#ifndef LCD_HEIGHT
#define LCD_HEIGHT 240
#endif
#ifndef LCD_MADCTL
#define LCD_MADCTL 0x70 /* MV | MX | ML: landscape */
#endif
#ifndef LCD_INVERT
#define LCD_INVERT 1 /* IPS panels need display inversion on */
#endif

/* Keys (active low, internal pull-ups) and the UVL key codes they send. */
#ifndef PIN_KEY_A
#define PIN_KEY_A 15
#endif
#ifndef PIN_KEY_B
#define PIN_KEY_B 17
#endif
#ifndef PIN_KEY_X
#define PIN_KEY_X 2
#endif
#ifndef PIN_KEY_Y
#define PIN_KEY_Y 3
#endif

/* Tile size: two RGB565 tiles are double-buffered for DMA (2 x 2 KB). */
#ifndef TILE_W
#define TILE_W 64
#endif
#ifndef TILE_H
#define TILE_H 16
#endif
