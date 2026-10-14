/* Minimal ST7789 driver: blocking commands, DMA pixel transfers. */
#pragma once
#include <stddef.h>
#include <stdint.h>

void st7789_init(void);
/* Wait until the previous DMA transfer has left the SPI shifter. */
void st7789_wait(void);
/* Set the write window to the w x h rectangle at (x, y) and start sending
   `len` bytes of big-endian RGB565 from `px` by DMA. `px` must stay untouched
   until st7789_wait() returns. */
void st7789_blit_async(uint16_t x, uint16_t y, uint16_t w, uint16_t h, const uint8_t *px, size_t len);
