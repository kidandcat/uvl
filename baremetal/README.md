# UVL en microcontroladores

La misma app Lean que corre en desktop (`Examples/Counter.lean`) compilada a C y
ejecutada sin `libleanrt`, sin sistema operativo y sin heap del sistema. La
probamos de forma automática en x86-64, i386 y ARM Cortex-M3 (QEMU). En los tres
casos genera frames idénticos byte a byte a los del binario Lean nativo.

```
baremetal/
  include/uvl.h          ABI C entre el firmware y la app Lean
  include/lean/config.h  sustituye al config.h del toolchain (sin mimalloc, 32 bits)
  rt/uvl_rt.c            runtime mínimo: pool estático, RC, closures, arrays, strings, Nat/Int pequeños
  rt/uvl_shell.c         wrappers que prestan el estado (render de tile a buffer DMA)
  tools/uvl_bundle.py    junta el C generado + Init/Std alcanzable en un bundle compilable
  tools/gen_c.sh         genera C de módulos del toolchain (Init/Std/Lean solo vienen como .a)
  tools/test.sh          test extremo a extremo (host 64/32 bits + QEMU)
  host/main.c            harness: aplica eventos y vuelca frames por tiles
  qemu/                  startup + linker script para mps2-an385 (Cortex-M3)
```

## Cómo funciona

1. **Lado Lean.** `UniversalViz/BareMetal/Shell.lean` envuelve una `App` con el
   modelo, la escena actual partida en tiles (`TileList`) y la configuración de
   la pantalla. `Examples/BareMetalCounter.lean` exporta la API C con
   `@[export]`: `uvl_init`, `uvl_event`, `uvl_needs_redraw`, `uvl_begin_frame`,
   `uvl_tile_rgb565` y `uvl_tile_mono`.
2. **Bundle.** `uvl_bundle.py` toma el C que genera `lake` y le añade el C de
   los módulos de Init/Std que realmente se usan, enlazando y reiterando con
   `--gc-sections` hasta llegar a un punto fijo. Después reescribe los
   inicializadores de módulo para que solo inicialicen las constantes
   alcanzables (`uvl_init.c`). El resultado es `src/*.c`, `rt/*.c` e `include/`,
   junto con `uvl_bundle.cmake` para Pico SDK o ESP-IDF.
3. **Firmware.** El bucle principal es el de `include/uvl.h`: convierte los
   eventos de botones o del táctil en llamadas a `uvl_event`. Si hay que
   redibujar, renderiza tile a tile (64×16 por defecto) en uno de dos buffers
   y envía el otro por DMA.

### Memoria: pool estático, no arena por frame

El plan original proponía una arena de 16 KB que se resetea en cada frame. No
lo hicimos así porque, con el conteo de referencias de Lean, los temporales de
un tile se liberan en cuanto dejan de usarse. Por eso el pico de memoria no
crece con el número de tiles. Un reset ciego destruiría el estado de la UI
(modelo y escena) que sobrevive entre frames.

`uvl_rt.c` usa un pool estático (`UVL_HEAP_SIZE`, 96 KB por defecto) con
clases de tamaño de 8 bytes hasta 512 B (O(1), listas libres), best-fit para
bloques grandes y desfragmentación al quedarse sin memoria. No llama nunca a
`malloc`. `uvl_heap_stats()` informa del uso.

Medido con el contador a 320×240 en 32 bits, tiles de 64×16:

| | |
| --- | --- |
| Vivo tras `uvl_rt_init` + `uvl_init` | ~38 KB (constantes cerradas, incl. ~23 KB de la tabla de glifos) |
| Pico de memoria viva renderizando | ~62 KB |
| Marca máxima del pool (con fragmentación) | ~71 KB de 96 KB |
| Código ARM (Thumb-2, `-O2`) | ~347 KB de `.text` incluyendo newlib + semihosting |

Cabe en un RP2040 (264 KB de SRAM, 2 MB de flash) y en un ESP32. La mayor parte
de lo que ocupa tras el init es `Font.glyphTable`, que se construye como
`Array` en el arranque. Pasarla a datos estáticos en flash ahorraría ~23 KB de
RAM y es la siguiente optimización obvia.

### Detalles de 32 bits

- `include/lean/config.h` define `LEAN_EMSCRIPTEN` en targets de 32 bits.
  `lean.h` solo usa esa macro para partir los literales escalares de 8 bytes
  en dos palabras.
- El compilador de Lean asume que los literales `Nat` menores que 2^63 son
  escalares y nunca les hace `dec`. En 32 bits algunos (por ejemplo
  `9007199254740992` en el modelo de `Float`) son objetos en el heap. Para no
  perder memoria, el bundler los convierte en literales internados y
  persistentes (`uvl_nat_literal`).
- Los `Nat`/`Int` grandes se implementan con magnitud de 64 bits. Si un
  cálculo se sale de ese rango, se produce un pánico fatal. En el código de
  UVL no ocurre.
- No hay `Task`s, IO de ficheros ni hilos; la app no los necesita.

## Probarlo

```sh
baremetal/tools/test.sh
```

El script:

1. Compila `Examples` y `uvl-baremetal-ref`, la referencia nativa en Lean.
2. Genera, solo la primera vez, el C de Init en `.lake/baremetal/init-c`
   (unos 3 minutos).
3. Crea el bundle en `.lake/baremetal/bundle`.
4. Compara `frame0`/`frame1.rgb565` contra la referencia en tres builds:
   - host de 64 bits;
   - host de 32 bits (`gcc -m32`) con un pool de 96 KB;
   - Cortex-M3 bajo QEMU, si están `arm-none-eabi-gcc` y `qemu-system-arm`.

Para usar el bundle en otro proyecto, añade `uvl_bundle.cmake` y compila
`UVL_BUNDLE_SOURCES` con `UVL_BUNDLE_INCLUDE` por delante del include del
toolchain de Lean. No hay que enlazar contra `libleanrt` ni contra `libInit`.
