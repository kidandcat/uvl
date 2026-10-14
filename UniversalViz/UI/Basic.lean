import UniversalViz.Layout.Widget
import UniversalViz.Render.Raster

/-!
# Widget combinators

The function-call API of the declarative layer:

```
col [ row [ text "Hola", button "Click" ] ]
```

Every function returns a `Layout.Widget`; `UI.render` lays it out and rasterizes it.
-/

namespace UViz.UI

open Layout

abbrev Widget := Layout.Widget

def empty : Widget := .empty

def text (s : String) (size : Nat := 2) (color : Color := Color.darkGray) : Widget :=
  .text s size color

def box (w h : Nat) (color : Paint := Color.gray) : Widget := .box w h color

def canvas (w h : Nat) (draw : Rect → Array RenderOp) : Widget := .canvas w h draw

def padding (l t r b : Nat) (child : Widget) : Widget := .padding l t r b child
def pad (n : Nat) (child : Widget) : Widget := .padding n n n n child
def padXY (x y : Nat) (child : Widget) : Widget := .padding x y x y child

def center (child : Widget) : Widget := .center child
def sized (w h : Nat) (child : Widget) : Widget := .sized (some w) (some h) child
def width (w : Nat) (child : Widget) : Widget := .sized (some w) none child
def height (h : Nat) (child : Widget) : Widget := .sized none (some h) child

def expanded (child : Widget) (flex : Nat := 1) : Widget := .expanded flex child
/-- Flexible empty space. -/
def spacer (flex : Nat := 1) : Widget := .expanded flex .empty

def col (children : List Widget) (gap : Nat := 8) (justify : Justify := .start)
    (align : Align := .start) : Widget :=
  .flex .vertical gap justify align children

def row (children : List Widget) (gap : Nat := 8) (justify : Justify := .start)
    (align : Align := .center) : Widget :=
  .flex .horizontal gap justify align children

/-- A list where a single widget is expected: one child stays as is, several
become a column. This is what lets `ui!` blocks feed single-child widgets. -/
def ofList : List Widget → Widget
  | [w] => w
  | ws => col ws

instance : Coe (List Widget) Widget := ⟨ofList⟩

def stack (children : List Widget) (h : Align := .start) (v : Align := .start) : Widget :=
  .stack h v children

def decorated (child : Widget) (fill : Option Paint := none) (radius : Float := 0)
    (border : Option (Float × Color) := none) (shadow : Option (Float × Color) := none) : Widget :=
  .decorated { fill, radius, border, shadow } child

def card (child : Widget) (bg : Paint := Color.white) (radius : Float := 12)
    (padding : Nat := 16) : Widget :=
  .decorated { fill := some bg, radius, shadow := some (8, Color.black.withAlpha 0.25) }
    (.padding padding padding padding padding child)

def button (label : String) (color : Color := Color.blue) (textColor : Color := Color.white)
    (size : Nat := 2) : Widget :=
  .decorated { fill := some (.solid color), radius := 8 }
    (.padding 14 8 14 8 (.text label size textColor))

def chip (label : String) (color : Color := Color.lightGray) (textColor : Color := Color.darkGray) :
    Widget :=
  .decorated { fill := some (.solid color), radius := 10 } (.padding 8 4 8 4 (.text label 1 textColor))

def divider (color : Color := Color.lightGray) (thickness : Nat := 1) : Widget :=
  .sized none (some thickness) (.box 0 thickness color)

/-- Lay out `w` to exactly fill a `width × height` surface and rasterize it. -/
def render (w : Widget) (width height : Nat) (bg : Color := Color.white) : FrameBuffer width height :=
  Raster.render width height (w.toOps width height) bg

end UViz.UI
