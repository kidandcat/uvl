import UVL.UI.Basic
import UVL.Text.Layout

/-!
# TrueType text widgets

`label` and `paragraph` draw text with a TrueType font (by default the bundled
`Text.uvlSans ()`) at any pixel size. They are opt-in: `text` keeps using the
built-in bitmap font, which is what the bare-metal targets rely on.

Glyphs are drawn from their outlines (exact) unless `msdf := true`, which
draws them from the font's MSDF atlas: constant cost per pixel, the better
choice for a lot of text on the GPU.
-/

namespace UVL.UI

variable {Msg : Type}

/-- Text ops for a block of lines in the top-left corner of `r`. -/
def textOps (font : Text.Font) (lines : Array String) (size : Float) (color : Color)
    (msdf : Bool) (r : Rect) : Array RenderOp :=
  if msdf then Text.linesOpsMSDF font lines size (.solid color) ⟨r.x, r.y⟩
  else Text.linesOps font lines size color ⟨r.x, r.y⟩

/-- One line of TrueType text, `size` pixels per em. -/
def label (s : String) (size : Float := 16) (color : Color := Color.darkGray)
    (font : Text.Font := Text.uvlSans ()) (msdf : Bool := false) : Widget Msg :=
  let (w, h) := Text.linesSize font #[s] size
  canvas w h (textOps font #[s] size color msdf)

/-- TrueType text wrapped at spaces (and at `'\n'`) to `maxWidth` pixels. -/
def paragraph (s : String) (maxWidth : Nat) (size : Float := 16)
    (color : Color := Color.darkGray) (font : Text.Font := Text.uvlSans ())
    (msdf : Bool := false) : Widget Msg :=
  let lines := Text.wrap font s size maxWidth.toFloat
  let (w, h) := Text.linesSize font lines size
  canvas w h (textOps font lines size color msdf)

end UVL.UI
