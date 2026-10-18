import UVL

/-! Interactive example: stateful controls (slider, checkboxes, text field and
a scroll view, a multi-line text area), with all their state in the model (Elm
architecture), and a level meter that follows the slider with a tween. The view
is written in the HTML-like markup (`UVL.UI.Html`). -/

namespace Examples.Controls
open UVL UI

inductive Msg where
  | volume (v : Float)
  | toggle (i : Nat)
  | name (st : TextInput)
  | submit
  | scrolled (offset : Nat)
  | pick (i : Nat)
  | frame (dt : Float)
  | notes (st : TextInput)

structure Model where
  volume : Float := 0.4
  /-- The level meter, easing towards `volume`. -/
  meter : Tween := .at 0.4 (duration := 0.4) (easing := .outBack)
  options : Array Bool := #[true, false]
  name : TextInput := {}
  greeted : String := ""
  scroll : Nat := 0
  picked : Option Nat := none
  notes : TextInput := { text := "UVL draws everything in Lean: layout, text and pixels.\nTry Ctrl+arrows, double-click and Shift+Up." }

def update : Msg → Model → Model
  | .volume v, m => { m with volume := v, meter := m.meter.to v }
  | .toggle i, m => { m with options := m.options.modify i (!·) }
  | .name st, m => { m with name := st }
  | .submit, m => { m with greeted := m.name.text }
  | .scrolled o, m => { m with scroll := o }
  | .pick i, m => { m with picked := some i }
  | .frame dt, m => { m with meter := m.meter.step dt }
  | .notes st, m => { m with notes := st }

def items : List String :=
  (List.range 30).map fun i => s!"Item {i + 1}: " ++
    #["Lean", "WebGPU", "MSDF", "SDF", "Flexbox", "Elm"][i % 6]!

/-- A bar filled to `v ∈ [0, 1]` (it can overshoot slightly with `outBack`). -/
def meter (v : Float) : UI.Widget Msg :=
  canvas 220 10 fun r =>
    let fill := Max.max 0 (Min.min r.w (r.w * v))
    #[.fill (.roundedRect r (.all 5)) (Color.hex 0xE3E8EC),
      .fill (.roundedRect ⟨r.x, r.y, fill, r.h⟩ (.all 5))
        (.linear ⟨r.x, 0⟩ ⟨r.x + r.w, 0⟩ #[(0, Color.hex 0x43A047), (0.7, Color.hex 0xFDD835),
          (1, Color.hex 0xE53935)])]

def wordCount (s : String) : Nat :=
  ((s.split fun c => c == ' ' || c == '\n').filter (!·.isEmpty)).length

def view (m : Model) : UI.Widget Msg :=
  <pad n=20>
    <row gap=20 align=.start>
      <card>
        <col gap=14>
          <label size=24 color={Color.hex 0x0D47A1}>Controls</label>
          <row gap=10>
            <label size=15>Volume</label>
            <slider value={m.volume} onChange={.volume} width=180 label="Volume"/>
            <label size=15>{(m.volume * 100).round.toUInt32}%</label>
          </row>
          <row gap=10>
            <label size=15>Level</label>
            <meter v={m.meter.value}/>
          </row>
          <checkbox checked={m.options[0]!} onToggle={.toggle 0} size=15>Dark grid lines</checkbox>
          <checkbox checked={m.options[1]!} onToggle={.toggle 1} size=15>Show legend</checkbox>
          <textField id="name" st={m.name} onChange={.name} width=260
            placeholder="Type your name…" onSubmit={.submit}/>
          <label size=15 color={Color.hex 0x546E7A}>
            {if m.greeted.isEmpty then "Press Enter to greet" else s!"Hello, {m.greeted}!"}
          </label>
        </col>
      </card>
      <card padding=8>
        <width w=200>
          <scrollView offset={m.scroll} onScroll={.scrolled} height=280>
            <col gap=2 align=.stretch>
              {items.zipIdx.map fun (s, i) =>
                <onTap msg={.pick i} radius=6>
                  <decorated radius=6
                      fill={if m.picked.any (· == i) then some (.solid (Color.hex 0xBBDEFB)) else none}>
                    <padXY x=10 y=6><label size=14>{s}</label></padXY>
                  </decorated>
                </onTap>}
            </col>
          </scrollView>
        </width>
      </card>
      <card>
        <col gap=10>
          <label size=18 color={Color.hex 0x0D47A1}>Notes</label>
          <textArea id="notes" st={m.notes} onChange={.notes} width=200 lines=9 size=15/>
          <label size=13 color={Color.hex 0x546E7A}>
            {wordCount m.notes.text} words, {m.notes.text.length} characters
          </label>
        </col>
      </card>
    </row>
  </pad>

def app : App Model Msg where
  init := {}
  update
  view
  subscriptions := fun e _ => match e with
    | .tick dt => some (.frame dt)
    | _ => none
  animating := fun m => !m.meter.done
  background := Color.hex 0xF5F7FA
  title := "uvl · controls"

end Examples.Controls
