import UVL.Render.Raster
import UVL.Core.PixelFormat

/-!
# Tile-based rendering

A 320×240 RGBA8 frame is 300 KB: more SRAM than an RP2040 has. Embedded
targets instead render the frame as a grid of small tiles (e.g. 64×16 pixels,
2 KB in RGB565) and stream each one to the display while the next is computed.

`Raster.renderWindow` renders any window of a scene, in device coordinates, so
each pixel of a tile goes through exactly the same coverage computation and the
same sequence of blends as in a full-frame render. The test suite checks that a
frame assembled from tiles is **bit-identical** to `Raster.render`.

Binning (`TileList`): each top-level op gets a conservative device-space bound
once per frame; a tile only visits the ops whose bound meets it. Skipping an op
that cannot touch the tile leaves the tile unchanged, so binning is invisible in
the output (also covered by the bit-identity test).
-/

namespace UVL

/-- Points that bound a path (Bézier curves lie in the hull of their controls). -/
def Path.controlPoints (p : Path) : Array Vec2 :=
  p.cmds.foldl (init := #[]) fun acc c =>
    match c with
    | .moveTo q | .lineTo q => acc.push q
    | .quadTo c q => acc.push c |>.push q
    | .cubicTo c1 c2 q => acc.push c1 |>.push c2 |>.push q
    | .close => acc

namespace Shape

/-- Local-space bounding box of the shape's geometry. -/
def bounds : Shape → Rect
  | .rect r | .roundedRect r _ => r
  | .circle c r => ⟨c.x - r, c.y - r, 2 * r, 2 * r⟩
  | .ellipse c rx ry => ⟨c.x - rx, c.y - ry, 2 * rx, 2 * ry⟩
  | .line a b => Rect.ofPoints #[a, b]
  | .path p _ => Rect.ofPoints p.controlPoints

end Shape

namespace RenderOp

def Rect.union (a b : Rect) : Rect :=
  let x0 := Min.min a.x b.x; let y0 := Min.min a.y b.y
  ⟨x0, y0, Max.max (a.x + a.w) (b.x + b.w) - x0, Max.max (a.y + a.h) (b.y + b.h) - y0⟩

/-- Conservative device-space bounds of an op drawn through `m`; `none` when the
op draws nothing. Generous margins: over-approximating only costs a little time. -/
partial def bounds (m : Affine) : RenderOp → Option Rect
  | .fill s _ => some ((m.mapRect s.bounds).inflate 2.0)
  | .stroke s width _ =>
    some ((m.mapRect (s.bounds.inflate (width / 2.0))).inflate (2.0 + width * m.scaleFactor))
  | .shadow r _ blur _ => some ((m.mapRect r).inflate (2.0 + 4.0 * blur * m.scaleFactor))
  | .text pos s scale _ =>
    -- glyphs are drawn axis-aligned at the transformed origin (see `Raster.drawText`)
    let o := m.apply pos
    let sc := scale * m.scaleFactor
    let n := s.length.toFloat
    some (Rect.inflate ⟨o.x, o.y, (n * Font.advance.toFloat + 1.0) * sc, 8.0 * sc⟩ 2.0)
  | .transform m' ops => boundsAll (m.compose m') ops
  | .clip r ops => (boundsAll m ops).map fun b =>
    -- intersection is contained in both; keep the smaller one cheaply
    let c := (m.mapRect r).inflate 1.0
    if c.w * c.h < b.w * b.h then c else b
  | .group ops => boundsAll m ops
where
  boundsAll (m : Affine) (ops : Array RenderOp) : Option Rect :=
    ops.foldl (init := none) fun acc op =>
      match acc, bounds m op with
      | none, b => b
      | a, none => a
      | some a, some b => some (Rect.union a b)

end RenderOp

/-- A scene prepared for tile rendering: top-level ops with their device bounds. -/
structure TileList where
  ops : Array (Rect × RenderOp)

namespace TileList

def build (ops : Array RenderOp) : TileList :=
  ⟨ops.filterMap fun op => (op.bounds {}).map (·, op)⟩

@[inline] def meets (b : Rect) (x y w h : Nat) : Bool :=
  b.x < (x + w).toFloat && b.y < (y + h).toFloat &&
    b.x + b.w > x.toFloat && b.y + b.h > y.toFloat

/-- The ops (in paint order) whose bounds meet the window `[x, x+w) × [y, y+h)`. -/
def select (t : TileList) (x y w h : Nat) : Array RenderOp :=
  t.ops.filterMap fun (b, op) => if meets b x y w h then some op else none

end TileList

namespace Tile

/-- Width/height of the tile starting at `t` along an axis of length `n` (edge
tiles are clipped to the frame). -/
@[inline] def extent (n tileSize t : Nat) : Nat := Min.min tileSize (n - t)

/-- Render the tile whose top-left device pixel is `(tx, ty)` of a `w × h` frame. -/
def render (scene : TileList) (w h tw th tx ty : Nat) (bg : Color := Color.white) :
    FrameBuffer (extent w tw tx) (extent h th ty) :=
  let cw := extent w tw tx; let ch := extent h th ty
  Raster.renderWindow tx ty cw ch (scene.select tx ty cw ch) bg

/-- Top-left corners of all tiles, row by row. -/
def origins (w h tw th : Nat) : Array (Nat × Nat) := Id.run do
  let mut out := #[]
  if tw == 0 || th == 0 then return out
  for j in [0:(h + th - 1) / th] do
    for i in [0:(w + tw - 1) / tw] do
      out := out.push (i * tw, j * th)
  return out

/-- Copy a `cw × ch` RGBA tile into a `w`-wide RGBA image at `(tx, ty)`. -/
def blit (dst : ByteArray) (w : Nat) (tile : ByteArray) (cw ch tx ty : Nat) : ByteArray :=
  (List.range ch).foldl (init := dst) fun dst row =>
    tile.copySlice (row * cw * 4) dst (((ty + row) * w + tx) * 4) (cw * 4)

/-- Render a full frame tile by tile and assemble it (desktop validation path:
must equal `Raster.render w h ops bg` byte for byte). -/
def renderTiled (w h tw th : Nat) (ops : Array RenderOp) (bg : Color := Color.white) :
    FrameBuffer w h :=
  let scene := TileList.build ops
  let data := (origins w h tw th).foldl (init := (FrameBuffer.new w h bg).data) fun acc (tx, ty) =>
    blit acc w (render scene w h tw th tx ty bg).data (extent w tw tx) (extent h th ty) tx ty
  if hs : data.size = w * h * 4 then ⟨data, hs⟩ else FrameBuffer.new w h bg

/-- Big-endian RGB565 bytes of one tile: what goes into the SPI DMA buffer. -/
def renderRGB565 (scene : TileList) (w h tw th tx ty : Nat) (bg : Color := Color.white) :
    ByteArray :=
  (render scene w h tw th tx ty bg).toRGB565

/-- A whole frame streamed as RGB565 tiles, re-assembled into a row-major
RGB565 image (`2 * w * h` bytes), as the panel's GRAM would end up. -/
def renderTiledRGB565 (w h tw th : Nat) (ops : Array RenderOp) (bg : Color := Color.white) :
    ByteArray :=
  let scene := TileList.build ops
  (origins w h tw th).foldl (init := ByteArray.mk (Array.replicate (2 * w * h) 0)) fun acc (tx, ty) =>
    let cw := extent w tw tx; let ch := extent h th ty
    let tile := renderRGB565 scene w h tw th tx ty bg
    (List.range ch).foldl (init := acc) fun acc row =>
      tile.copySlice (row * cw * 2) acc (((ty + row) * w + tx) * 2) (cw * 2)

end Tile

end UVL
