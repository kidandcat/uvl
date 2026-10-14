# uvl — universal visualization library

Librería de visualización universal escrita **100% en Lean 4**: sin DOM, sin GTK/UIKit, sin
dependencias en C. Lean controla todo, desde el árbol de widgets hasta el último píxel; la
plataforma anfitriona solo tiene que entregar un *framebuffer* y un flujo de eventos.

![dashboard](Tests/golden/dashboard.png)

## Estado

| Hito | Contenido | Estado |
| --- | --- | --- |
| 1. Core e imagen | `FrameBuffer` verificado, primitivas 2D con SDF, paths Bézier, gradientes, sombras, texto, rasterizador CPU, PNG/PPM | ✅ |
| 2. Layout y DSL | Motor *Box Constraints* con invariantes en el tipo, flex (row/col/expanded), stack, DSL `ui!`, gráficos | ✅ (primera versión) |
| 3. Interactividad desktop | Runtime estilo Elm (`App`, `Event`), hit testing, hover/press, runner SDL3 (~170 líneas de C) | ✅ |
| 4. GPU y navegador | `webgpu.h`, Emscripten | pendiente |
| Bare metal | Tiled rendering (RGB565 / 1-bit, identical to the full frame), C runtime without `libleanrt` tested on ARM Cortex-M3 (QEMU); see [`baremetal/`](baremetal/README.md) | in progress |

## Uso rápido

```bash
lake build              # la librería
lake exe uvl-demo      # escribe out/primitives.png, out/hello.png, out/dashboard.png
lake test               # tests golden + layout + códecs
lake test -- --update   # regenera las imágenes golden
lake exe uvl-bench     # tiempo por frame del rasterizador
lake exe uvl-counter    # app de escritorio (requiere SDL3)
```

Requiere Lean `v4.35.0` (fijado en `lean-toolchain`).

### API de funciones

```lean
import UVL
open UVL UI

def hello : UI.Widget Unit :=
  center <| card <| col [ row [ text "Hola", button "Click" ] ]

def main : IO Unit :=
  Image.writePNG "hello.png" (UI.render hello 320 160)
```

![hello](Tests/golden/hello.png)

### DSL `ui!`

Sintaxis por indentación; cada línea es `widget args*` y `:` abre un bloque de hijos
(o `;` en la misma línea). Es azúcar puro sobre la API de funciones: `nombre` se resuelve a
`UVL.UI.nombre`, así que añadir un widget nuevo es definir una función.

```lean
def dashboard : UI.Widget Unit := ui! pad 20:
  col (gap := 16) (align := .stretch):
    row (gap := 12):
      text "Universal Viz" (size := 3)
      spacer
      chip "Lean 4"
    expanded:
      card:
        lineChart [[3, 5, 4, 8, 7, 11], [1, 2, 4, 3, 6, 5]]
```

### Apps interactivas (arquitectura Elm)

Una app es `init`, un `update : Msg → Model → Model` puro y un
`view : Model → Widget Msg` puro. El runtime (también puro) se encarga del layout,
del *hit testing*, del feedback de hover/press y de decidir cuándo hace falta un frame
nuevo. Ver [Examples/Counter.lean](Examples/Counter.lean):

```lean
inductive Msg | inc | dec | reset

def view (m : Model) : UI.Widget Msg := ui! pad 24:
  card:
    row (gap := 16) (justify := .center):
      button "-" (onTap := some Msg.dec)
      text (toString m.count) (size := 6)
      button "+" (onTap := some Msg.inc)

def app : App Model Msg where
  init := {}
  update
  view
  subscriptions                      -- teclado, ticks, ...
    | .keyDown .up, _ => some .inc
    | _, _ => none
```

![counter](Tests/golden/counter.png)

* **Escritorio:** `UVL.SDL.run app` abre una ventana con SDL3. El shell en C
  ([native/sdl_shell.c](native/sdl_shell.c)) solo traduce eventos y copia el buffer RGBA a
  una textura; no hay lógica de UI en C. Solo se redibuja cuando algo cambia, así que una UI
  en reposo no gasta CPU.
* **Headless / tests:** `Runtime.simulate` alimenta eventos de un guion; los tests hacen
  clics y comparan el frame resultante con una imagen golden.

Para compilar la app de escritorio hace falta SDL3 (`brew install sdl3`, o compilarlo
desde las releases de GitHub). Lake lo busca con `pkg-config sdl3` o en los prefijos
habituales. Sin pantalla se puede probar con
`SDL_VIDEO_DRIVER=offscreen UVL_MAX_FRAMES=2 UVL_CLICK_TARGET=1 UVL_SCREENSHOT=shot.png lake exe uvl-counter`.

### Rendimiento

CPU, un núcleo, 800×600 (`lake exe uvl-bench`): contador ~7 ms/frame, dashboard completo
~35 ms/frame. Dos claves:

* El rasterizador aprovecha que un SDF es 1-Lipschitz: con una evaluación salta tramos
  enteros fuera de la forma o rellena tramos enteros dentro, y solo evalúa píxel a píxel el
  borde antialiasado.
* Los literales `Float` se elaboran a `Float.ofBits` con el patrón de bits calculado en
  compilación ([Core/FloatLit.lean](UVL/Core/FloatLit.lean)); Lean los compilaba
  como `Float.ofScientific` con aritmética de precisión arbitraria en cada evaluación.

### Escena de bajo nivel (`RenderOp`)

```lean
def scene : Array RenderOp := #[
  .shadow ⟨32, 40, 200, 120⟩ 16 10 (Color.black.withAlpha 0.35),
  RenderOp.roundRect ⟨24, 28, 200, 120⟩ 16 Color.white,
  .fill (.circle ⟨320, 90⟩ 56) (.radial ⟨300, 70⟩ 80 #[(0, Color.yellow), (1, Color.red)]),
  RenderOp.path (Path.star ⟨90, 240⟩ 56 24 5) Color.yellow ]

#eval Image.writePNG "scene.png" (Raster.render 480 320 scene)
```

![primitives](Tests/golden/primitives.png)

## Arquitectura

```
UVL/
  Core/       Color, Vec2/Rect/Affine, literales Float rápidos
  Render/     FrameBuffer (verificado), SDF, Paint, Path, Font, RenderOp, Raster
  Output/     Deflate/zlib y PNG/PPM en Lean puro
  Layout/     Constraints, Placed (árbol posicionado), Widget + motor de layout
  UI/         API de widgets, DSL ui!, gráficos (barras, líneas, donut)
  App/        Event, App y Runtime (Elm architecture, hit testing)
UVLWindow.lean  shell SDL3 (FFI) — solo lo usan los ejecutables uvl-*
native/       sdl_shell.c
Examples/     escenas de ejemplo + ejecutable de demo
Tests/        imágenes golden, decodificador PNG de test, test driver
```

### Qué está garantizado por tipos

* **Ninguna escritura fuera del buffer.** `FrameBuffer w h` lleva la prueba
  `data.size = w * h * 4`; los píxeles se direccionan con `Fin w × Fin h` y
  `pixel_index_lt` demuestra que el offset de cada byte está en rango. Los bucles del
  rasterizador recorren un `Clip w h` con cotas probadas, así que no hay *bounds checks*
  en el camino caliente.
* **Mutación in situ.** El `FrameBuffer` se pasa de función en función con referencia única,
  y el runtime de Lean (Perceus/FBIP) muta el `ByteArray` sin copias.
* **El tamaño de un widget siempre respeta las restricciones del padre.**
  `layout w c : Result c` incluye `ok : c.Admits size`
  (`minW ≤ w ≤ maxW ∧ minH ≤ h ≤ maxH`). Ver `Constraints.constrain_admits`.
* **Ningún hijo se sale de su padre.** El árbol posicionado `Placed s` está indexado por su
  tamaño y cada hijo lleva la prueba `x + child.w ≤ s.w ∧ y + child.h ≤ s.h`; un árbol con
  *overflow* simplemente no tipa.
* **El layout siempre termina.** `layout` es una función total (recursión bien fundada sobre
  el árbol de widgets), no `partial`.

### Rasterizador

* Formas analíticas (rectángulos, rectángulos con radios por esquina, círculos, elipses,
  segmentos, sombras gaussianas) a partir de su SDF: una evaluación de distancia por píxel y
  antialiasing gratis.
* Paths (líneas, Bézier cuadráticas y cúbicas) aplanados y rellenados por scanline con
  regla *non-zero* o *even-odd*, cobertura horizontal exacta y 4 sub-muestras verticales.
* Trazos con uniones y extremos redondeados; transformaciones afines y recorte anidados.
* Texto con una fuente bitmap 5×7 integrada (ASCII + acentos y ñ), rasterizada con
  cobertura de área exacta para cualquier escala. TTF + MSDF está previsto para más adelante.

## Próximos pasos

1. Hito 4: backend `webgpu.h` y build con Emscripten (el mismo `Runtime` en el navegador).
2. Texto con salto de línea y parser TrueType + atlas MSDF.
3. Widgets con estado propio: campo de texto, scroll, sliders; animaciones con `tick`.
4. Redibujado parcial (solo las regiones sucias) para pantallas grandes.
