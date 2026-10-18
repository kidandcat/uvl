import UVL

/-!
The HTML-like markup elaborates to the function API: checked at compile time
with `#guard`, comparing the text it passes and the frames it renders.
-/

namespace Tests.Html
open UVL UI

inductive Msg | inc | pick (i : Nat)
deriving BEq

def str (s : String) : String := s
def n : Nat := 3

-- text content: whitespace collapses, `{x}` goes through `toString`
#guard <str>{n} words, {n + 1} characters!</str> == "3 words, 4 characters!"
#guard <str>  Hello,
         world   {n}{n}  x </str> == "Hello, world 33 x"
#guard <str>{n}</str> == "3"
#guard <str>100% → ok.</str> == "100% → ok."
-- `<` stays a comparison when followed by a space
#guard (n < 4 && 2 <n)

def frame (w : Widget Msg) : List UInt8 := (UI.render w 200 160).data.data.toList

def items : List String := ["a", "b"]

def markup (on : Bool) : Widget Msg :=
  <pad n=8>
    <col gap=4 align=.stretch>
      <row><text size=1>Count: {n}</text><spacer/><button size=1 onTap={.inc}>+</button></row>
      <card padding=4><chip>one</chip><chip>two</chip></card>
      {if on then some (box 20 4 (.solid Color.red)) else none}
      {items.zipIdx.map fun (s, i) => <onTap msg={.pick i}><text>{s}</text></onTap>}
      <divider/>
    </col>
  </pad>

def calls (on : Bool) : Widget Msg :=
  pad 8 <| col (gap := 4) (align := .stretch) ([
    row [text s!"Count: {n}" (size := 1), spacer, button "+" (size := 1) (onTap := some .inc)],
    card (padding := 4) (col [chip "one", chip "two"])] ++
    (if on then [box 20 4 (.solid Color.red)] else []) ++
    (items.zipIdx.map fun (s, i) => onTap (.pick i) (text s)) ++
    [divider])

#guard frame (markup true) == frame (calls true)
#guard frame (markup false) == frame (calls false)

end Tests.Html
