#include "st7789.h"

#include "config.h"
#include "hardware/dma.h"
#include "hardware/gpio.h"
#include "hardware/spi.h"
#include "pico/stdlib.h"

static int dma_chan = -1;

static void cmd(uint8_t c, const uint8_t *data, size_t n) {
    gpio_put(PIN_LCD_CS, 0);
    gpio_put(PIN_LCD_DC, 0);
    spi_write_blocking(LCD_SPI, &c, 1);
    if (n) {
        gpio_put(PIN_LCD_DC, 1);
        spi_write_blocking(LCD_SPI, data, n);
    }
    gpio_put(PIN_LCD_CS, 1);
}

void st7789_init(void) {
    spi_init(LCD_SPI, LCD_SPI_HZ);
    spi_set_format(LCD_SPI, 8, SPI_CPOL_1, SPI_CPHA_1, SPI_MSB_FIRST);
    gpio_set_function(PIN_LCD_SCK, GPIO_FUNC_SPI);
    gpio_set_function(PIN_LCD_MOSI, GPIO_FUNC_SPI);
    const uint pins[] = {PIN_LCD_CS, PIN_LCD_DC, PIN_LCD_RST, PIN_LCD_BL};
    for (unsigned i = 0; i < 4; i++) {
        gpio_init(pins[i]);
        gpio_set_dir(pins[i], GPIO_OUT);
        gpio_put(pins[i], 1);
    }
    gpio_put(PIN_LCD_RST, 0);
    sleep_ms(20);
    gpio_put(PIN_LCD_RST, 1);
    sleep_ms(120);

    cmd(0x01, NULL, 0); /* SWRESET */
    sleep_ms(150);
    cmd(0x11, NULL, 0); /* SLPOUT */
    sleep_ms(120);
    const uint8_t colmod = 0x55; /* 16 bits per pixel */
    cmd(0x3A, &colmod, 1);
    const uint8_t madctl = LCD_MADCTL;
    cmd(0x36, &madctl, 1);
    cmd(LCD_INVERT ? 0x21 : 0x20, NULL, 0); /* INVON / INVOFF */
    cmd(0x13, NULL, 0); /* NORON */
    cmd(0x29, NULL, 0); /* DISPON */
    sleep_ms(10);

    dma_chan = dma_claim_unused_channel(true);
    dma_channel_config c = dma_channel_get_default_config(dma_chan);
    channel_config_set_transfer_data_size(&c, DMA_SIZE_8);
    channel_config_set_dreq(&c, spi_get_dreq(LCD_SPI, true));
    channel_config_set_read_increment(&c, true);
    channel_config_set_write_increment(&c, false);
    dma_channel_configure(dma_chan, &c, &spi_get_hw(LCD_SPI)->dr, NULL, 0, false);
}

void st7789_wait(void) {
    dma_channel_wait_for_finish_blocking(dma_chan);
    while (spi_is_busy(LCD_SPI)) tight_loop_contents();
    /* Drain the RX FIFO the transmit-only DMA left behind. */
    while (spi_is_readable(LCD_SPI)) (void)spi_get_hw(LCD_SPI)->dr;
    spi_get_hw(LCD_SPI)->icr = SPI_SSPICR_RORIC_BITS;
    gpio_put(PIN_LCD_CS, 1);
}

void st7789_blit_async(uint16_t x, uint16_t y, uint16_t w, uint16_t h, const uint8_t *px, size_t len) {
    const uint16_t x1 = x + w - 1, y1 = y + h - 1;
    const uint8_t caset[4] = {x >> 8, x & 0xff, x1 >> 8, x1 & 0xff};
    const uint8_t raset[4] = {y >> 8, y & 0xff, y1 >> 8, y1 & 0xff};
    cmd(0x2A, caset, 4);
    cmd(0x2B, raset, 4);
    /* RAMWR, then the pixels by DMA with CS held low until st7789_wait(). */
    const uint8_t ramwr = 0x2C;
    gpio_put(PIN_LCD_CS, 0);
    gpio_put(PIN_LCD_DC, 0);
    spi_write_blocking(LCD_SPI, &ramwr, 1);
    gpio_put(PIN_LCD_DC, 1);
    dma_channel_transfer_from_buffer_now(dma_chan, px, len);
}
