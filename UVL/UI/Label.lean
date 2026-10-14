import UVL.UI.Basic
import UVL.Text.Layout

/-!
# TrueType text widgets

`label` and `paragraph` draw text with a TrueType font (by default the bundled
`Text.uvlSans ()`) at any pixel size. They are opt-in: `text` keeps using the
built-in bitmap font, which is what the bare-metal targets rely on.
-/

namespace UVL.UI

variable {Msg : Type}

/-- One line of TrueType text, `size` pixels per em. -/
def label (s : String) (size : Float := 16) (color : Color := Color.darkGray)
    (font : Text.Font := Text.uvlSans ()) : Widget Msg :=
  let (w, h) := Text.linesSize font #[s] size
  canvas w h fun r => Text.linesOps font #[s] size color ⟨r.x, r.y⟩

/-- TrueType text wrapped at spaces (and at `'\n'`) to `maxWidth` pixels. -/
def paragraph (s : String) (maxWidth : Nat) (size : Float := 16)
    (color : Color := Color.darkGray) (font : Text.Font := Text.uvlSans ()) : Widget Msg :=
  let lines := Text.wrap font s size maxWidth.toFloat
  let (w, h) := Text.linesSize font lines size
  canvas w h fun r => Text.linesOps font lines size color ⟨r.x, r.y⟩

end UVL.UI
