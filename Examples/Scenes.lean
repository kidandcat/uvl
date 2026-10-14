import UVL

/-! Example scenes shared by the demo executable and the golden tests. -/

namespace Examples
open UVL

/-- Milestone 1 showcase: SDF shapes, gradients, shadows, Bézier paths and text. -/
def primitives : Array RenderOp := #[
  .fill (.rect ⟨0, 0, 480, 320⟩)
    (.linear ⟨0, 0⟩ ⟨480, 320⟩ #[(0, Color.hex 0xE3F2FD), (1, Color.hex 0xFCE4EC)]),
  .shadow ⟨32, 40, 200, 120⟩ 16 10 (Color.black.withAlpha 0.35),
  RenderOp.roundRect ⟨24, 28, 200, 120⟩ 16 Color.white,
  .stroke (.roundedRect ⟨24, 28, 200, 120⟩ (.all 16)) 2 (Color.hex 0x90CAF9),
  .text ⟨40, 44⟩ "Hola, Lean 4!" 2 Color.darkGray,
  .text ⟨40, 72⟩ "SDF + FBIP" 1 (Color.hex 0x1565C0),
  .fill (.roundedRect ⟨40, 100, 72, 30⟩ ⟨15, 4, 15, 4⟩) Color.blue,
  .text ⟨53, 108⟩ "Click" 2 Color.white,
  .fill (.circle ⟨320, 90⟩ 56)
    (.radial ⟨300, 70⟩ 80 #[(0, Color.hex 0xFFF59D), (0.6, Color.orange), (1, Color.red)]),
  .stroke (.circle ⟨320, 90⟩ 56) 3 Color.darkGray,
  .fill (.ellipse ⟨430, 90⟩ 30 50) (Color.purple.withAlpha 0.7),
  RenderOp.path (Path.star ⟨90, 240⟩ 56 24 5) Color.yellow,
  RenderOp.strokePath (Path.star ⟨90, 240⟩ 56 24 5) 2 Color.orange,
  RenderOp.strokePath ({ : Path }.moveTo 170 280 |>.cubicTo 220 160 300 340 360 210) 6
    (.linear ⟨170, 0⟩ ⟨360, 0⟩ #[(0, Color.teal), (1, Color.blue)]),
  RenderOp.line ⟨380, 180⟩ ⟨460, 300⟩ 4 Color.red,
  RenderOp.line ⟨380, 300⟩ ⟨460, 180⟩ 1.5 Color.darkGray,
  .transform (Affine.translate 400 250 |>.compose (Affine.rotate 0.5))
    #[RenderOp.roundRect ⟨-20, -12, 40, 24⟩ 6 (Color.green.withAlpha 0.8)]
]

open UI in
/-- The example from the roadmap, written with the function API. -/
def hello : UI.Widget Unit :=
  center <| card <| col [ row [ text "Hola", button "Click" ] ]

open UI in
/-- A small dashboard written with the `ui!` DSL. -/
def dashboard : UI.Widget Unit := ui! pad 20:
  col (gap := 16) (align := .stretch):
    row (gap := 12):
      text "Universal Viz" (size := 3) (color := Color.hex 0x0D47A1)
      spacer
      chip "Lean 4"
      chip "100% puro" (color := Color.hex 0xC8E6C9) (textColor := Color.hex 0x1B5E20)
    row (gap := 16) (align := .stretch):
      expanded:
        card:
          col (gap := 10) (align := .stretch):
            text "Ventas por trimestre"
            barChart [("Q1", 12), ("Q2", 19), ("Q3", 7), ("Q4", 24)] (h := 180)
      card:
        col (gap := 10) (align := .center):
          text "Reparto"
          donutChart [5, 3, 2, 1]
    expanded:
      card:
        col (gap := 10) (align := .stretch):
          row:
            text "Usuarios activos"
            spacer
            button "Exportar" (size := 1)
          expanded: lineChart [[3, 5, 4, 8, 7, 11, 10, 14], [1, 2, 4, 3, 6, 5, 8, 9]]

end Examples
