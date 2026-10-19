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
  .text ⟨40, 44⟩ "Hello, Lean 4!" 2 Color.darkGray,
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
  center <| card <| col [ row [ text "Hello", button "Click" ] ]

open UI in
/-- A small dashboard written with the `ui!` DSL. -/
def dashboard : UI.Widget Unit := ui! pad 20:
  col (gap := 16) (align := .stretch):
    row (gap := 12):
      text "UVL" (size := 3) (color := Color.hex 0x0D47A1)
      spacer
      chip "Lean 4"
      chip "100% pure" (color := Color.hex 0xC8E6C9) (textColor := Color.hex 0x1B5E20)
    row (gap := 16) (align := .stretch):
      expanded:
        card:
          col (gap := 10) (align := .stretch):
            text "Sales per quarter"
            barChart [("Q1", 12), ("Q2", 19), ("Q3", 7), ("Q4", 24)] (h := 180)
      card:
        col (gap := 10) (align := .center):
          text "Share"
          donutChart [5, 3, 2, 1]
    expanded:
      card:
        col (gap := 10) (align := .stretch):
          row:
            text "Active users"
            spacer
            button "Export" (size := 1)
          expanded: lineChart [[3, 5, 4, 8, 7, 11, 10, 14], [1, 2, 4, 3, 6, 5, 8, 9]]

/-- MSDF text: sizes from 10 to 48 px, a rotated line and a gradient fill. -/
def msdfText : Array RenderOp :=
  let f := Text.uvlSans ()
  let sizes : List Float := [10, 13, 16, 22, 32, 48]
  let (ops, _) := sizes.foldl (init := (#[], 8.0)) fun (ops, y) s =>
    (ops ++ Text.linesOpsMSDF f #[s!"MSDF {s.toUInt32} px · Ångström"] s
      (.solid (Color.hex 0x263238)) ⟨10, y⟩, y + s * 1.25)
  ops ++ #[.transform (Affine.translate 300 222 |>.compose (Affine.rotate (-0.12)))
    (Text.linesOpsMSDF f #["rotated & scaled"] 26
      (.linear ⟨0, 0⟩ ⟨220, 0⟩ #[(0, Color.hex 0xD81B60), (1, Color.hex 0x1E88E5)]) ⟨0, 0⟩)]

open UI in
/-- TrueType text (the bundled UVL Sans) at several sizes, with kerning,
accents and a wrapped paragraph. -/
def typography : UI.Widget Unit :=
  pad 16 <| card (padding := 20) <| col (gap := 6) [
    label "Typography in pure Lean" (size := 28) (color := Color.hex 0x0D47A1),
    label "AVA Today, Wave · ¡Olé! àéîõü ñ ç ß" (size := 18),
    row (gap := 12) [label "12 px" (size := 12), label "14 px" (size := 14),
      label "16 px" (size := 16), label "20 px" (size := 20)],
    paragraph ("TrueType outlines are parsed from an embedded font, laid out with " ++
      "advances and pair kerning, wrapped at spaces, and drawn as ordinary path fills, " ++
      "so the CPU rasterizer and the GPU kernels share one code path.") 380 (size := 14)
      (color := Color.hex 0x37474F)
  ]

/-- A 32×16 sprite sheet with two 16×16 frames: a shaded ball with a soft,
semi-transparent rim on a transparent background, and an opaque checker. -/
def spriteSheet : Texture := Id.run do
  let mut px := ByteArray.emptyWithCapacity (32 * 16 * 4)
  for y in [0:16] do
    for x in [0:32] do
      if x < 16 then
        let dx := x.toFloat - 7.5; let dy := y.toFloat - 7.5
        let r := Float.sqrt (dx * dx + dy * dy)
        let a := if r < 6 then 255 else if r < 8 then 110 else 0
        let shade := Max.max (255 - 12 * r) 0
        px := px.push (shade.toUInt8) |>.push (40 + 9 * x).toUInt8 |>.push (200 - 8 * y).toUInt8
          |>.push a.toUInt8
      else
        let on := ((x / 4) + (y / 4)) % 2 == 0
        px := px.push (if on then 230 else 30) |>.push (if on then 180 else 60)
          |>.push (17 * (x % 16)).toUInt8 |>.push 255
  return { id := 1, w := 32, h := 16, pixels := px }

/-- Sprites: nearest and bilinear sampling, magnified, rotated, translucent,
clipped and partly off-screen. -/
def spriteScene : Array RenderOp :=
  let ball : Rect := ⟨0, 0, 16, 16⟩
  let check : Rect := ⟨16, 0, 16, 16⟩
  #[.fill (.rect ⟨0, 0, 240, 160⟩) (Color.hex 0xDDE6EE),
    .sprites spriteSheet #[⟨ball, ⟨4, 4, 16, 16⟩, 1⟩, ⟨check, ⟨24, 4, 16, 16⟩, 1⟩,
      ⟨ball, ⟨44, 4, 48, 48⟩, 1⟩, ⟨check, ⟨96.25, 4.25, 40, 40⟩, 0.5⟩,
      ⟨⟨20, 4, 8, 8⟩, ⟨140, 4, 32, 32⟩, 1⟩, ⟨ball, ⟨-6, 60, 24, 24⟩, 1⟩,
      ⟨ball, ⟨226, 140, 30, 30⟩, 1⟩],
    .sprites spriteSheet #[⟨ball, ⟨24.3, 58.6, 40, 40⟩, 1⟩, ⟨check, ⟨70.1, 60.2, 37.5, 37.5⟩, 0.8⟩]
      (smooth := true),
    .transform (Affine.translate 170 100 |>.compose (Affine.rotate 0.4))
      #[.sprites spriteSheet #[⟨ball, ⟨-20, -20, 40, 40⟩, 1⟩] (smooth := true),
        .sprites spriteSheet #[⟨check, ⟨24, -12, 24, 24⟩, 1⟩]],
    .clip ⟨10, 110, 60, 30⟩ #[.sprites spriteSheet #[⟨check, ⟨2, 100, 50, 50⟩, 1⟩,
      ⟨ball, ⟨40, 104, 44, 44⟩, 0.7⟩] (smooth := true)]]

end Examples
