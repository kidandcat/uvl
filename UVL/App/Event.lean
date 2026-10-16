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
  | home
  | end_
  /-- Either Shift key (tracked by the runtime as a modifier). -/
  | shift
  /-- Either Ctrl key, or Cmd on macOS (tracked by the runtime as a modifier). -/
  | ctrl
  | other (code : Nat)
deriving Inhabited, Repr, BEq

inductive Event where
  | pointerMove (x y : Float)
  | pointerDown (x y : Float) (button : MouseButton)
  | pointerUp (x y : Float) (button : MouseButton)
  | pointerLeave
  /-- Wheel or trackpad scroll, in pixels; positive `dy` scrolls the content up
  (shows what is further down), like the browser's `deltaY`. -/
  | scroll (dx dy : Float)
  | keyDown (key : Key)
  | keyUp (key : Key)
  | textInput (s : String)
  /-- Text being composed by an input method (IME), not committed yet; `""`
  when the composition ends. The committed text then arrives as `textInput`. -/
  | compose (s : String)
  | resize (w h : Nat)
  /-- Animation frame; `dt` in seconds. -/
  | tick (dt : Float)
  | quit
deriving Inhabited, Repr

end UVL
