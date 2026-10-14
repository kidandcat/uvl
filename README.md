# universal-viz

Librería de visualización universal escrita **100% en Lean 4**: sin DOM, sin GTK/UIKit, sin
dependencias en C. Lean controla todo, desde el árbol de widgets hasta el último píxel; la
plataforma anfitriona solo tiene que entregar un *framebuffer* y un flujo de eventos.

![dashboard](Tests/golden/dashboard.png)

## Estado

| Hito | Contenido | Estado |
| --- | --- | --- |
| 1. Core e imagen | `FrameBuffer` verificado, primitivas 2D con SDF, paths Bézier, gradientes, sombras, texto, rasterizador CPU, PNG/PPM | ✅ |
| 2. Layout y DSL | Motor *Box Constraints* con invariantes en el tipo, flex (row/col/expanded), stack, DSL `ui!`, gráficos | ✅ (primera versión) |
| 3. Interactividad desktop | Runner en C (SDL3/Sokol), bucle de eventos | pendiente |
| 4. GPU y navegador | `webgpu.h`, Emscripten | pendiente |

## Uso rápido

```bash
lake build              # la librería
lake exe uviz-demo      # escribe out/primitives.png, out/hello.png, out/dashboard.png
lake test               # tests golden + layout + códecs
lake test -- --update   # regenera las imágenes golden
```

Requiere Lean `v4.35.0` (fijado en `lean-toolchain`).

### API de funciones

```lean
import UniversalViz
open UViz UI

def hello : UI.Widget :=
  center <| card <| col [ row [ text "Hola", button "Click" ] ]

def main : IO Unit :=
  Image.writePNG "hello.png" (UI.render hello 320 160)
```

![hello](Tests/golden/hello.png)

### DSL `ui!`

Sintaxis por indentación; cada línea es `widget args*` y `:` abre un bloque de hijos
(o `;` en la misma línea). Es azúcar puro sobre la API de funciones: `nombre` se resuelve a
`UViz.UI.nombre`, así que añadir un widget nuevo es definir una función.

```lean
def dashboard : UI.Widget := ui! pad 20:
  col (gap := 16) (align := .stretch):
    row (gap := 12):
      text "Universal Viz" (size := 3)
      spacer
      chip "Lean 4"
    expanded:
      card:
        lineChart [[3, 5, 4, 8, 7, 11], [1, 2, 4, 3, 6, 5]]
```

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
UniversalViz/
  Core/       Color, Vec2/Rect/Affine
  Render/     FrameBuffer (verificado), SDF, Paint, Path, Font, RenderOp, Raster
  Output/     Deflate/zlib y PNG/PPM en Lean puro
  Layout/     Constraints, Placed (árbol posicionado), Widget + motor de layout
  UI/         API de widgets, DSL ui!, gráficos (barras, líneas, donut)
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

1. Texto con salto de línea y parser TrueType + atlas MSDF.
2. Modelo TEA (`view : State → Widget`, `update : Msg → State → State`) con `Event` unificado
   y *hit testing* sobre `Placed`.
3. Runner desktop en C (SDL3) que copie el `ByteArray` a una textura a 60 FPS.
4. Backend `webgpu.h` y build con Emscripten.
