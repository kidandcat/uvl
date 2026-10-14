/* mps2-an385: 4 MB code SRAM at 0, 4 MB data SRAM at 0x20000000.
   QEMU loads every ELF segment where it is linked, so .data needs no copy. */
MEMORY {
  FLASH (rx) : ORIGIN = 0x00000000, LENGTH = 4M
  RAM (rwx)  : ORIGIN = 0x20000000, LENGTH = 4M
}
ENTRY(_start)
SECTIONS {
  .text : {
    KEEP(*(.vectors))
    *(.text*) *(.rodata*)
    KEEP(*(.init)) KEEP(*(.fini))
    . = ALIGN(4);
    __preinit_array_start = .; KEEP(*(.preinit_array)) __preinit_array_end = .;
    __init_array_start = .; KEEP(*(SORT(.init_array.*))) KEEP(*(.init_array)) __init_array_end = .;
    __fini_array_start = .; KEEP(*(SORT(.fini_array.*))) KEEP(*(.fini_array)) __fini_array_end = .;
    *(.eh_frame*)
  } > FLASH
  .ARM.exidx : { *(.ARM.exidx*) } > FLASH
  .data : { __data_start__ = .; *(.data*) __data_end__ = .; } > RAM
  .bss (NOLOAD) : { __bss_start__ = .; *(.bss*) *(COMMON) __bss_end__ = .; } > RAM
  . = ALIGN(8);
  end = .;
  __end__ = .;
  __stack_top = ORIGIN(RAM) + LENGTH(RAM);
  __HeapLimit = __stack_top - 0x10000;
}
