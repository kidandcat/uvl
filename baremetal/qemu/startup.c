/*
 * Minimal Cortex-M startup for running the host harness (host/main.c) on
 * QEMU's mps2-an385 board (Cortex-M3) with ARM semihosting: newlib's rdimon
 * crt0 (`_start`) zeroes .bss, sets up stdio/files over semihosting and calls
 * main. Used by tools/qemu_test.sh to run the bundle as 32-bit ARM code.
 */
#include <stdint.h>

extern void _start(void);
extern uint32_t __stack_top;

static void fault(void) { for (;;) { } }

__attribute__((section(".vectors"), used))
const void *vectors[16] = {
    &__stack_top, (void *)_start, (void *)fault, (void *)fault, (void *)fault, (void *)fault, (void *)fault,
    0, 0, 0, 0, (void *)fault, (void *)fault, 0, (void *)fault, (void *)fault,
};
