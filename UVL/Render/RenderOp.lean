import UVL.Render.SDF
import UVL.Render.Paint
import UVL.Render.Path
import UVL.Render.MSDF
import UVL.Render.Sprite

/-!
# RenderOp: the immutable scene graph

`RenderOp` is the intermediate representation every higher layer (layout,
widgets, charts) lowers to, and every backend (CPU rasterizer today, WebGPU
later) consumes.
-/

namespace UVL

inductive FillRule where
  | nonZero
  | evenOdd
deriving Inhabited, Repr, BEq

inductive Shape where
  | rect (r : Rect)
  | roundedRect (r : Rect) (radii : SDF.Corners)
  | circle (c : Vec2) (r : Float)
  | ellipse (c : Vec2) (rx ry : Float)
  /-- A line segment; only meaningful when stroked. -/
  | line (a b : Vec2)
  | path (p : Path) (rule : FillRule := .nonZero)
deriving Inhabited, BEq

inductive RenderOp where
  | fill (s : Shape) (p : Paint)
  | stroke (s : Shape) (width : Float) (p : Paint)
  /-- Gaussian drop shadow of a rounded rectangle. -/
  | shadow (r : Rect) (radius blur : Float) (c : Color)
  /-- Text with the built-in font; `pos` is the top-left corner, `scale` the cell size in px. -/
  | text (pos : Vec2) (s : String) (scale : Float) (c : Color)
  /-- Glyphs drawn from an MSDF atlas (see `Render/MSDF.lean`). -/
  | glyphs (atlas : MSDF.Atlas) (quads : Array MSDF.GlyphQuad) (p : Paint)
  /-- Textured quads cut from `tex` (see `Render/Sprite.lean`), sampled nearest
  or, with `smooth`, bilinear. -/
  | sprites (tex : Texture) (quads : Array Sprite) (smooth : Bool := false)
  /-- A static sprite layer (see `SpriteLayer`): drawn like `sprites`, but GPU
  hosts keep its instances uploaded across frames. -/
  | layer (l : SpriteLayer)
  | transform (m : Affine) (ops : Array RenderOp)
  | clip (r : Rect) (ops : Array RenderOp)
  | group (ops : Array RenderOp)
deriving Inhabited, BEq

namespace RenderOp

def rect (r : Rect) (p : Paint) : RenderOp := .fill (.rect r) p
def roundRect (r : Rect) (radius : Float) (p : Paint) : RenderOp :=
  .fill (.roundedRect r (SDF.Corners.all radius)) p
def circle (c : Vec2) (r : Float) (p : Paint) : RenderOp := .fill (.circle c r) p
def line (a b : Vec2) (width : Float) (p : Paint) : RenderOp := .stroke (.line a b) width p
def path (p : Path) (paint : Paint) : RenderOp := .fill (.path p) paint
def strokePath (p : Path) (width : Float) (paint : Paint) : RenderOp := .stroke (.path p) width paint
def translate (dx dy : Float) (ops : Array RenderOp) : RenderOp :=
  .transform (Affine.translate dx dy) ops

end RenderOp

end UVL
