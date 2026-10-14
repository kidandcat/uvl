/-!
# Events

A single algebraic event type fed to the UI from any platform shell
(SDL3 desktop, browser, headless scripts).
-/

namespace UVL

inductive MouseButton where
  | left
  | middle
  | right
  | other (n : Nat)
deriving Inhabited, Repr, BEq

inductive Key where
  | char (c : Char)
  | enter
  | escape
  | backspace
  | tab
  | delete
  | left
  | right
  | up
  | down
  | other (code : Nat)
deriving Inhabited, Repr, BEq

inductive Event where
  | pointerMove (x y : Float)
  | pointerDown (x y : Float) (button : MouseButton)
  | pointerUp (x y : Float) (button : MouseButton)
  | pointerLeave
  | scroll (dx dy : Float)
  | keyDown (key : Key)
  | keyUp (key : Key)
  | textInput (s : String)
  | resize (w h : Nat)
  /-- Animation frame; `dt` in seconds. -/
  | tick (dt : Float)
  | quit
deriving Inhabited, Repr

end UVL
