import UVL.Render.SDF
import UVL.Core.Color

/-!
# Textures and sprites

A `Texture` is an RGBA8 image (straight alpha, row-major, like `FrameBuffer`)
that sprites are cut from: typically one atlas holding every unit, building and
terrain frame of a game. A `Sprite` maps a texel rectangle of the texture onto
a local-space rectangle.

Sampling is defined here once (`sampleNearest`, `sampleLinear`) and used by the
CPU rasterizer; the GPU kernel (`GPU/Kernels.lean`) performs the same
operations in the same order, so both backends agree to the bit in the
interpreted reference renderer.
-/

namespace UVL

/-- An RGBA8 image (straight alpha). Like `MSDF.Atlas`, textures compare by
`id`: two textures with the same id are assumed to hold the same pixels (scene
diffing and GPU uploads rely on it). -/
structure Texture where
  id : Nat
  w : Nat
  h : Nat
  /-- `w * h * 4` bytes, RGBA, row-major. -/
  pixels : ByteArray

instance : Inhabited Texture := ⟨{ id := 0, w := 0, h := 0, pixels := .empty }⟩
instance : BEq Texture := ⟨fun a b => a.id == b.id⟩

/-- One textured quad: texel rectangle `src` of the texture drawn onto the
local rectangle `dst`, with an extra `opacity`. -/
structure Sprite where
  src : Rect
  dst : Rect
  opacity : Float := 1
deriving Inhabited, Repr, BEq

namespace Sprite

/-- The parameters both backends compute a sprite's pixels from: box center
and half size (coverage), the local → texel map `u = (x - dx) * ku + sx`, and
the source rectangle (texels). -/
structure Params where
  cx : Float
  cy : Float
  hx : Float
  hy : Float
  dx : Float
  dy : Float
  ku : Float
  kv : Float
  sx : Float
  sy : Float
  sw : Float
  sh : Float

def params (s : Sprite) : Params :=
  { cx := s.dst.center.x, cy := s.dst.center.y, hx := s.dst.w / 2, hy := s.dst.h / 2
    dx := s.dst.x, dy := s.dst.y
    ku := if s.dst.w == 0 then 0 else s.src.w / s.dst.w
    kv := if s.dst.h == 0 then 0 else s.src.h / s.dst.h
    sx := s.src.x, sy := s.src.y, sw := s.src.w, sh := s.src.h }

end Sprite

namespace Texture

/-- Channel `c` of texel `(x, y)` in `[0, 1]`. -/
@[inline] def chan (t : Texture) (x y c : Nat) : Float :=
  (t.pixels.get! ((y * t.w + x) * 4 + c)).toFloat / 255

/-- Clamp a texel coordinate to `[lo, lo + n - 1]`. -/
@[inline] def clampTexel (v lo n : Float) : Float := Max.max lo (Min.min v (lo + n - 1))

@[inline] def toIdx (v : Float) : Nat := if v <= 0 then 0 else v.toUInt64.toNat

/-- Nearest texel at texel-space point `(u, v)`, clamped to the source rectangle. -/
@[inline] def sampleNearest (t : Texture) (p : Sprite.Params) (u v : Float) : Color :=
  let x := toIdx (clampTexel u.floor p.sx p.sw)
  let y := toIdx (clampTexel v.floor p.sy p.sh)
  ⟨t.chan x y 0, t.chan x y 1, t.chan x y 2, t.chan x y 3⟩

/-- Bilinear filtering of premultiplied texels at texel-space point `(u, v)`
(texel centers at half-integers), clamped to the source rectangle, returned
with straight alpha. -/
@[inline] def sampleLinear (t : Texture) (p : Sprite.Params) (u v : Float) : Color :=
  let tx := u - 0.5
  let ty := v - 0.5
  let fx := tx.floor
  let fy := ty.floor
  let ax := tx - fx
  let ay := ty - fy
  let x0 := toIdx (clampTexel fx p.sx p.sw)
  let x1 := toIdx (clampTexel (fx + 1) p.sx p.sw)
  let y0 := toIdx (clampTexel fy p.sy p.sh)
  let y1 := toIdx (clampTexel (fy + 1) p.sy p.sh)
  let lerp (c : Nat) : Float :=
    let pm (x y : Nat) : Float := if c == 3 then t.chan x y 3 else t.chan x y c * t.chan x y 3
    let top := pm x0 y0 + ax * (pm x1 y0 - pm x0 y0)
    let bot := pm x0 y1 + ax * (pm x1 y1 - pm x0 y1)
    top + ay * (bot - top)
  let a := lerp 3
  if a <= 0 then ⟨0, 0, 0, 0⟩ else ⟨lerp 0 / a, lerp 1 / a, lerp 2 / a, a⟩

end Texture

/-- A static sprite layer: quads that stay the same for many frames (terrain,
scenery). The GPU host uploads its instances once per `key` and afterwards only
draws them with the current transform, so a layer costs nothing to lower.
Layers compare by `key` and texture id: change the key whenever the quads
change. The CPU rasterizer draws a layer exactly like `RenderOp.sprites`. -/
structure SpriteLayer where
  key : Nat
  tex : Texture
  quads : Array Sprite
  smooth : Bool := false
deriving Inhabited

instance : BEq SpriteLayer := ⟨fun a b => a.key == b.key && a.tex.id == b.tex.id⟩

end UVL
