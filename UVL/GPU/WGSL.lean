import UVL.Core.Geometry

/-!
# A typed shader DSL that emits WGSL

Shaders are written in Lean as values of `Expr t`, indexed by their WGSL type,
so an ill-typed shader (adding a `vec2f` to an `f32`, branching on a float,
calling a function with the wrong arguments) is a Lean type error rather than a
WGSL compilation error at run time in the browser.

Programs are built in the `ShaderM` monad: `let_` binds an expression to a
fresh immutable name, `var_` declares a mutable variable, `if_`, `for_` and
`ret` build control flow, and `Fn.def1` … `Fn.def4` turn a Lean function over `Expr`s
into a WGSL function plus a typed Lean function that calls it.

Every program also has a meaning in Lean: `eval` runs expressions and
statements on `Float`s. The test suite uses it to check that the shader
versions of the signed distance functions agree with `UVL.SDF`, and to render
whole scenes through the shader without a GPU (`GPU/Reference.lean`).
-/

namespace UVL.GPU

/-- The WGSL types the DSL uses. -/
inductive Ty where
  | f32
  | u32
  | bool
  | v2
  | v4
deriving BEq, DecidableEq, Repr, Inhabited

def Ty.wgsl : Ty → String
  | .f32 => "f32"
  | .u32 => "u32"
  | .bool => "bool"
  | .v2 => "vec2f"
  | .v4 => "vec4f"

/-- Four floats (`vec4f`). -/
structure V4 where
  x : Float
  y : Float
  z : Float
  w : Float
deriving Inhabited, Repr, BEq

/-- Lean meaning of a WGSL type (32-bit floats are modelled by `Float`). -/
abbrev Ty.denote : Ty → Type
  | .f32 => Float
  | .u32 => UInt32
  | .bool => Bool
  | .v2 => Vec2
  | .v4 => V4

instance (t : Ty) : Inhabited t.denote := by cases t <;> exact ⟨default⟩

/-- Types with `+ - * / min max` (component-wise on vectors). -/
class Arith (t : Ty) : Prop where
instance : Arith .f32 := ⟨⟩
instance : Arith .u32 := ⟨⟩
instance : Arith .v2 := ⟨⟩
instance : Arith .v4 := ⟨⟩

/-- Float types with `abs sqrt floor …` (component-wise on vectors). -/
class Floating (t : Ty) : Prop where
instance : Floating .f32 := ⟨⟩
instance : Floating .v2 := ⟨⟩
instance : Floating .v4 := ⟨⟩

/-- Scalar types with ordering. -/
class Ordered (t : Ty) : Prop where
instance : Ordered .f32 := ⟨⟩
instance : Ordered .u32 := ⟨⟩

inductive BinOp where
  | add | sub | mul | div | min | max
deriving BEq, Repr

inductive CmpOp where
  | lt | le | gt | ge | eq | ne
deriving BEq, Repr

inductive Fn1 where
  | neg | abs | sqrt | floor | ceil | exp
deriving BEq, Repr

/-- A read-only storage buffer of `f32`s, declared by the shader skeleton. -/
structure Buffer where
  name : String
deriving BEq, Repr

/-- A function of the shader module, by name, with its parameter and result types. -/
structure FnRef (ps : List Ty) (r : Ty) where
  name : String

mutual

/-- WGSL expressions of type `t`. -/
inductive Expr : Ty → Type where
  | litF (x : Float) : Expr .f32
  | litU (n : UInt32) : Expr .u32
  | litB (b : Bool) : Expr .bool
  | var {t : Ty} (name : String) : Expr t
  | bin {t : Ty} (op : BinOp) (a b : Expr t) : Expr t
  | un {t : Ty} (op : Fn1) (a : Expr t) : Expr t
  | cmp {t : Ty} (op : CmpOp) (a b : Expr t) : Expr .bool
  | and (a b : Expr .bool) : Expr .bool
  | or (a b : Expr .bool) : Expr .bool
  | not (a : Expr .bool) : Expr .bool
  /-- `c ? a : b` (WGSL `select(b, a, c)`); both sides are evaluated. -/
  | select {t : Ty} (c : Expr .bool) (a b : Expr t) : Expr t
  | scale (k : Expr .f32) (v : Expr .v2) : Expr .v2
  | vec2 (x y : Expr .f32) : Expr .v2
  | vec4 (x y z w : Expr .f32) : Expr .v4
  | x (v : Expr .v2) : Expr .f32
  | y (v : Expr .v2) : Expr .f32
  | comp (v : Expr .v4) (i : Fin 4) : Expr .f32
  | length (v : Expr .v2) : Expr .f32
  | dot (a b : Expr .v2) : Expr .f32
  | toF (a : Expr .u32) : Expr .f32
  | toU (a : Expr .f32) : Expr .u32
  | shr (a b : Expr .u32) : Expr .u32
  | band (a b : Expr .u32) : Expr .u32
  | load (buf : Buffer) (i : Expr .u32) : Expr .f32
  | call {ps : List Ty} {r : Ty} (f : FnRef ps r) (args : Args ps) : Expr r

/-- Typed argument lists. -/
inductive Args : List Ty → Type where
  | nil : Args []
  | cons {t : Ty} {ts : List Ty} (a : Expr t) (as : Args ts) : Args (t :: ts)

end

/-- Statements. Variables are introduced by the `ShaderM` builders, which keep
them well typed. -/
inductive Stmt where
  | decl {t : Ty} (name : String) (mutable : Bool) (e : Expr t)
  | assign {t : Ty} (name : String) (e : Expr t)
  | ite (c : Expr .bool) (th el : Array Stmt)
  /-- `for (var i = lo; i < hi; i++) { body }` -/
  | loop (i : String) (lo hi : Expr .u32) (body : Array Stmt)
  | brk
  | ret {t : Ty} (e : Expr t)

/-! ### Surface syntax -/

namespace Expr

instance : OfScientific (Expr .f32) := ⟨fun m s e => .litF (OfScientific.ofScientific m s e)⟩
instance {n : Nat} : OfNat (Expr .f32) n := ⟨.litF n.toF⟩
instance {n : Nat} : OfNat (Expr .u32) n := ⟨.litU n.toUInt32⟩
instance {t} [Arith t] : Add (Expr t) := ⟨.bin .add⟩
instance {t} [Arith t] : Sub (Expr t) := ⟨.bin .sub⟩
instance {t} [Arith t] : Mul (Expr t) := ⟨.bin .mul⟩
instance {t} [Arith t] : Div (Expr t) := ⟨.bin .div⟩
instance {t} [Floating t] : Neg (Expr t) := ⟨.un .neg⟩
instance : HMul (Expr .f32) (Expr .v2) (Expr .v2) := ⟨.scale⟩
instance : Coe Float (Expr .f32) := ⟨.litF⟩

def min {t} [Arith t] (a b : Expr t) : Expr t := .bin .min a b
def max {t} [Arith t] (a b : Expr t) : Expr t := .bin .max a b
def abs {t} [Floating t] (a : Expr t) : Expr t := .un .abs a
def sqrt {t} [Floating t] (a : Expr t) : Expr t := .un .sqrt a
def floor {t} [Floating t] (a : Expr t) : Expr t := .un .floor a
def ceil {t} [Floating t] (a : Expr t) : Expr t := .un .ceil a
def exp {t} [Floating t] (a : Expr t) : Expr t := .un .exp a
def clamp {t} [Arith t] (a lo hi : Expr t) : Expr t := min (max a lo) hi

def lt {t} [Ordered t] (a b : Expr t) : Expr .bool := .cmp .lt a b
def le {t} [Ordered t] (a b : Expr t) : Expr .bool := .cmp .le a b
def gt {t} [Ordered t] (a b : Expr t) : Expr .bool := .cmp .gt a b
def ge {t} [Ordered t] (a b : Expr t) : Expr .bool := .cmp .ge a b
def eq {t} [Ordered t] (a b : Expr t) : Expr .bool := .cmp .eq a b
def ne {t} [Ordered t] (a b : Expr t) : Expr .bool := .cmp .ne a b

infix:50 " <. " => Expr.lt
infix:50 " <=. " => Expr.le
infix:50 " >. " => Expr.gt
infix:50 " >=. " => Expr.ge
infix:50 " ==. " => Expr.eq
infix:50 " !=. " => Expr.ne
infixr:35 " &&. " => Expr.and
infixr:30 " ||. " => Expr.or

end Expr

/-! ### Building programs -/

structure BuildState where
  fresh : Nat := 0
  stmts : Array Stmt := #[]

abbrev ShaderM := StateM BuildState

def emit (s : Stmt) : ShaderM Unit := modify fun st => { st with stmts := st.stmts.push s }

def freshName (pre : String := "v") : ShaderM String := do
  let st ← get
  set { st with fresh := st.fresh + 1 }
  return s!"{pre}{st.fresh}"

/-- Bind `e` to a fresh immutable name (WGSL `let`). -/
def let_ {t : Ty} (e : Expr t) : ShaderM (Expr t) := do
  let n ← freshName
  emit (.decl n false e)
  return .var n

/-- A mutable variable (WGSL `var`). -/
structure Var (t : Ty) where
  name : String

def Var.get {t : Ty} (v : Var t) : Expr t := .var v.name
def Var.set {t : Ty} (v : Var t) (e : Expr t) : ShaderM Unit := emit (.assign v.name e)

def var_ {t : Ty} (e : Expr t) : ShaderM (Var t) := do
  let n ← freshName "m"
  emit (.decl n true e)
  return ⟨n⟩

/-- Run a sub-block, returning its statements (fresh names stay unique). -/
def block (m : ShaderM Unit) : ShaderM (Array Stmt) := do
  let st ← get
  let ((), st') := m.run { st with stmts := #[] }
  set { st with fresh := st'.fresh }
  return st'.stmts

def if_ (c : Expr .bool) (th : ShaderM Unit) (el : ShaderM Unit := pure ()) : ShaderM Unit := do
  let a ← block th
  let b ← block el
  emit (.ite c a b)

def for_ (lo hi : Expr .u32) (body : Expr .u32 → ShaderM Unit) : ShaderM Unit := do
  let i ← freshName "i"
  let b ← block (body (.var i))
  emit (.loop i lo hi b)

def ret {t : Ty} (e : Expr t) : ShaderM Unit := emit (.ret e)
def break_ : ShaderM Unit := emit .brk

/-- A function definition of the shader module. -/
structure FnDef where
  name : String
  params : List (String × Ty)
  result : Ty
  body : Array Stmt

private def defineWith (name : String) (params : List (String × Ty)) (r : Ty)
    (m : ShaderM Unit) : FnDef :=
  let ((), st) := m.run {}
  ⟨name, params, r, st.stmts⟩

/-! `Fn.defN name t₁ … tₙ r body` defines a shader function with `n` parameters
and returns its definition together with a typed Lean function that calls it. -/

def Fn.def1 (name : String) (t1 r : Ty) (body : Expr t1 → ShaderM Unit) :
    FnDef × (Expr t1 → Expr r) :=
  (defineWith name [("p0", t1)] r (body (.var "p0")),
   fun a => .call (ps := [t1]) ⟨name⟩ (.cons a .nil))

def Fn.def2 (name : String) (t1 t2 r : Ty) (body : Expr t1 → Expr t2 → ShaderM Unit) :
    FnDef × (Expr t1 → Expr t2 → Expr r) :=
  (defineWith name [("p0", t1), ("p1", t2)] r (body (.var "p0") (.var "p1")),
   fun a b => .call (ps := [t1, t2]) ⟨name⟩ (.cons a (.cons b .nil)))

def Fn.def3 (name : String) (t1 t2 t3 r : Ty)
    (body : Expr t1 → Expr t2 → Expr t3 → ShaderM Unit) :
    FnDef × (Expr t1 → Expr t2 → Expr t3 → Expr r) :=
  (defineWith name [("p0", t1), ("p1", t2), ("p2", t3)] r
     (body (.var "p0") (.var "p1") (.var "p2")),
   fun a b c => .call (ps := [t1, t2, t3]) ⟨name⟩ (.cons a (.cons b (.cons c .nil))))

def Fn.def4 (name : String) (t1 t2 t3 t4 r : Ty)
    (body : Expr t1 → Expr t2 → Expr t3 → Expr t4 → ShaderM Unit) :
    FnDef × (Expr t1 → Expr t2 → Expr t3 → Expr t4 → Expr r) :=
  (defineWith name [("p0", t1), ("p1", t2), ("p2", t3), ("p3", t4)] r
     (body (.var "p0") (.var "p1") (.var "p2") (.var "p3")),
   fun a b c d => .call (ps := [t1, t2, t3, t4]) ⟨name⟩
     (.cons a (.cons b (.cons c (.cons d .nil)))))

/-! ### WGSL emission -/

/-- A WGSL literal with 17 significant digits (`toString` keeps only 6 decimals). -/
def fmtFloat (x : Float) : String :=
  if x.isNaN then "(0.0 / 0.0)"
  else if x.isInf then (if x > 0 then "3.4e38" else "-3.4e38")
  else if x == 0 then "0.0"
  else
    let a := x.abs
    let k := a.log10.floor
    let n := (a * Float.pow 10 (16 - k)).round.toUInt64.toNat
    let ds := toString n
    let e := k.toInt64.toInt + (ds.length - 17 : Int)
    let cs := ds.toList
    let frac := (cs.drop 1).reverse.dropWhile (· == '0') |>.reverse
    let frac := if frac.isEmpty then "0" else String.ofList frac
    s!"{if x < 0 then "-" else ""}{String.ofList (cs.take 1)}.{frac}e{e}"

def BinOp.wgsl : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .min => "min" | .max => "max"

def CmpOp.wgsl : CmpOp → String
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">=" | .eq => "==" | .ne => "!="

def Fn1.wgsl : Fn1 → String
  | .neg => "-" | .abs => "abs" | .sqrt => "sqrt" | .floor => "floor" | .ceil => "ceil"
  | .exp => "exp"

mutual
def Expr.toWGSL {t : Ty} : Expr t → String
  | .litF x => fmtFloat x
  | .litU n => s!"{n}u"
  | .litB b => if b then "true" else "false"
  | .var n => n
  | .bin op a b =>
    match op with
    | .min | .max => s!"{op.wgsl}({a.toWGSL}, {b.toWGSL})"
    | _ => s!"({a.toWGSL} {op.wgsl} {b.toWGSL})"
  | .un .neg a => s!"(-{a.toWGSL})"
  | .un op a => s!"{op.wgsl}({a.toWGSL})"
  | .cmp op a b => s!"({a.toWGSL} {op.wgsl} {b.toWGSL})"
  | .and a b => s!"({a.toWGSL} && {b.toWGSL})"
  | .or a b => s!"({a.toWGSL} || {b.toWGSL})"
  | .not a => s!"(!{a.toWGSL})"
  | .select c a b => s!"select({b.toWGSL}, {a.toWGSL}, {c.toWGSL})"
  | .scale k v => s!"({k.toWGSL} * {v.toWGSL})"
  | .vec2 x y => s!"vec2f({x.toWGSL}, {y.toWGSL})"
  | .vec4 x y z w => s!"vec4f({x.toWGSL}, {y.toWGSL}, {z.toWGSL}, {w.toWGSL})"
  | .x v => s!"{v.toWGSL}.x"
  | .y v => s!"{v.toWGSL}.y"
  | .comp v i => s!"{v.toWGSL}.{#["x", "y", "z", "w"][i.val]!}"
  | .length v => s!"length({v.toWGSL})"
  | .dot a b => s!"dot({a.toWGSL}, {b.toWGSL})"
  | .toF a => s!"f32({a.toWGSL})"
  | .toU a => s!"u32({a.toWGSL})"
  | .shr a b => s!"({a.toWGSL} >> {b.toWGSL})"
  | .band a b => s!"({a.toWGSL} & {b.toWGSL})"
  | .load buf i => s!"{buf.name}[{i.toWGSL}]"
  | .call f as => s!"{f.name}({", ".intercalate as.toWGSL})"

def Args.toWGSL {ts : List Ty} : Args ts → List String
  | .nil => []
  | .cons a as => a.toWGSL :: as.toWGSL
end

/-- Concatenate strings. Written out instead of `String.join`, whose compiled
specialization lives in the `Lean` package (not linked into WebAssembly builds). -/
def concatAll : List String → String → String
  | [], acc => acc
  | s :: ss, acc => concatAll ss (acc ++ s)

-- A statement's children are a smaller `sizeOf` than the statement, and each
-- element of a statement array is a smaller `sizeOf` than the array.
mutual

def Stmt.toWGSL (ind : String) (s : Stmt) : String :=
  match s with
  | @Stmt.decl t n m e => s!"{ind}{if m then "var" else "let"} {n} : {t.wgsl} = {e.toWGSL};\n"
  | .assign n e => s!"{ind}{n} = {e.toWGSL};\n"
  | .ite c th el =>
    let a := stmtsToWGSL (ind ++ "  ") th 0
    let b := stmtsToWGSL (ind ++ "  ") el 0
    if el.isEmpty then s!"{ind}if {c.toWGSL} \{\n{a}{ind}}\n"
    else s!"{ind}if {c.toWGSL} \{\n{a}{ind}} else \{\n{b}{ind}}\n"
  | .loop i lo hi body =>
    let b := stmtsToWGSL (ind ++ "  ") body 0
    s!"{ind}for (var {i} : u32 = {lo.toWGSL}; {i} < {hi.toWGSL}; {i}++) \{\n{b}{ind}}\n"
  | .brk => s!"{ind}break;\n"
  | .ret e => s!"{ind}return {e.toWGSL};\n"
termination_by (sizeOf s, 0)

def stmtsToWGSL (ind : String) (ss : Array Stmt) (i : Nat) : String :=
  if h : i < ss.size then
    Stmt.toWGSL ind ss[i] ++ stmtsToWGSL ind ss (i + 1)
  else
    ""
termination_by (sizeOf ss, ss.size - i)

end

def FnDef.toWGSL (f : FnDef) : String :=
  let ps := ", ".intercalate (f.params.map fun (n, t) => s!"{n} : {t.wgsl}")
  s!"fn {f.name}({ps}) -> {f.result.wgsl} \{\n{concatAll (f.body.toList.map (Stmt.toWGSL "  ")) ""}}\n"

/-! ### Lean semantics -/

/-- A value of some type. -/
def Value := (t : Ty) × t.denote

instance : Inhabited Value := ⟨⟨.f32, 0⟩⟩

/-- Evaluation context: variables, storage buffers and the module's functions. -/
structure Env where
  vars : List (String × Value) := []
  buffers : String → FloatArray := fun _ => .empty
  fns : String → Option FnDef := fun _ => none

def Env.get (env : Env) (t : Ty) (n : String) : t.denote :=
  match env.vars.lookup n with
  | some ⟨t', v⟩ => if h : t' = t then h ▸ v else default
  | none => default

def Env.bind (env : Env) (n : String) (v : Value) : Env := { env with vars := (n, v) :: env.vars }

def Float.toU32 (x : Float) : UInt32 := if x <= 0 then 0 else x.toUInt32

def V4.map (f : Float → Float) (v : V4) : V4 := ⟨f v.x, f v.y, f v.z, f v.w⟩
def V4.zip (f : Float → Float → Float) (a b : V4) : V4 := ⟨f a.x b.x, f a.y b.y, f a.z b.z, f a.w b.w⟩

def BinOp.evalF : BinOp → Float → Float → Float
  | .add, a, b => a + b | .sub, a, b => a - b | .mul, a, b => a * b | .div, a, b => a / b
  | .min, a, b => Min.min a b | .max, a, b => Max.max a b

def BinOp.evalU : BinOp → UInt32 → UInt32 → UInt32
  | .add, a, b => a + b | .sub, a, b => a - b | .mul, a, b => a * b | .div, a, b => a / b
  | .min, a, b => Min.min a b | .max, a, b => Max.max a b

def Fn1.evalF : Fn1 → Float → Float
  | .neg, a => -a | .abs, a => a.abs | .sqrt, a => a.sqrt | .floor, a => a.floor
  | .ceil, a => a.ceil | .exp, a => a.exp

def CmpOp.evalF : CmpOp → Float → Float → Bool
  | .lt, a, b => a < b | .le, a, b => a <= b | .gt, a, b => a > b | .ge, a, b => a >= b
  | .eq, a, b => a == b | .ne, a, b => a != b

def CmpOp.evalU : CmpOp → UInt32 → UInt32 → Bool
  | .lt, a, b => a < b | .le, a, b => a ≤ b | .gt, a, b => a > b | .ge, a, b => a ≥ b
  | .eq, a, b => a == b | .ne, a, b => a != b

/-- Result of running statements: fell through, `break`, or `return v`. -/
inductive Flow where
  | next (env : Env)
  | brk (env : Env)
  | ret (v : Value)

instance : Inhabited Flow := ⟨.ret default⟩

/-- Leaving a block: keep the variables of the outer scope, with the values
assigned inside the block (assignments are recorded as new bindings). -/
def restore (outer inner : Env) : List (String × Value) :=
  outer.vars.map fun (n, _) => (n, (inner.vars.lookup n).getD default)

/-- Steps of the reference interpreter before it returns `default`.

Each expression, argument and statement takes one step, and so does each loop
iteration. One pixel of `shade` is a few thousand steps and the kernels' loops
run over a few dozen edges or samples, so programs this library builds stay
inside the bound. A shader that recurses past it used to diverge: the callee
body is data in `Env`, not a subterm of the call, so the step counter is what
makes evaluation well-founded. -/
def evalStepBound : Nat := 10000000

mutual

def exprEval : Nat → Env → {t : Ty} → Expr t → t.denote
  | 0, _, _, _ => default
  | fuel + 1, env, _, .litF x => x
  | fuel + 1, env, _, .litU n => n
  | fuel + 1, env, _, .litB b => b
  | fuel + 1, env, t, .var n => env.get t n
  | fuel + 1, env, .f32, .bin op a b => op.evalF (exprEval fuel env a) (exprEval fuel env b)
  | fuel + 1, env, .u32, .bin op a b => op.evalU (exprEval fuel env a) (exprEval fuel env b)
  | fuel + 1, env, .v2, .bin op a b =>
    let a := exprEval fuel env a; let b := exprEval fuel env b
    ⟨op.evalF a.x b.x, op.evalF a.y b.y⟩
  | fuel + 1, env, .v4, .bin op a b => V4.zip op.evalF (exprEval fuel env a) (exprEval fuel env b)
  | fuel + 1, _, .bool, .bin .. => default
  | fuel + 1, env, .f32, .un op a => op.evalF (exprEval fuel env a)
  | fuel + 1, env, .v2, .un op a => let a := exprEval fuel env a; ⟨op.evalF a.x, op.evalF a.y⟩
  | fuel + 1, env, .v4, .un op a => V4.map op.evalF (exprEval fuel env a)
  | fuel + 1, _, _, .un .. => default
  | fuel + 1, env, _, @Expr.cmp .f32 op a b => op.evalF (exprEval fuel env a) (exprEval fuel env b)
  | fuel + 1, env, _, @Expr.cmp .u32 op a b => op.evalU (exprEval fuel env a) (exprEval fuel env b)
  | fuel + 1, _, _, .cmp .. => default
  | fuel + 1, env, _, .and a b => exprEval fuel env a && exprEval fuel env b
  | fuel + 1, env, _, .or a b => exprEval fuel env a || exprEval fuel env b
  | fuel + 1, env, _, .not a => !(exprEval fuel env a)
  | fuel + 1, env, _, .select c a b =>
    let a := exprEval fuel env a; let b := exprEval fuel env b
    if exprEval fuel env c then a else b
  | fuel + 1, env, _, .scale k v =>
    let k := exprEval fuel env k; let v := exprEval fuel env v; ⟨k * v.x, k * v.y⟩
  | fuel + 1, env, _, .vec2 x y => ⟨exprEval fuel env x, exprEval fuel env y⟩
  | fuel + 1, env, _, .vec4 x y z w =>
    ⟨exprEval fuel env x, exprEval fuel env y, exprEval fuel env z, exprEval fuel env w⟩
  | fuel + 1, env, _, .x v => (exprEval fuel env v).x
  | fuel + 1, env, _, .y v => (exprEval fuel env v).y
  | fuel + 1, env, _, .comp v i =>
    let v := exprEval fuel env v
    match i with | 0 => v.x | 1 => v.y | 2 => v.z | 3 => v.w
  | fuel + 1, env, _, .length v => (exprEval fuel env v).length
  | fuel + 1, env, _, .dot a b => (exprEval fuel env a).dot (exprEval fuel env b)
  | fuel + 1, env, _, .toF a => (exprEval fuel env a).toFloat
  | fuel + 1, env, _, .toU a => Float.toU32 (exprEval fuel env a)
  | fuel + 1, env, _, .shr a b => exprEval fuel env a >>> exprEval fuel env b
  | fuel + 1, env, _, .band a b => exprEval fuel env a &&& exprEval fuel env b
  | fuel + 1, env, _, .load buf i =>
    let arr := env.buffers buf.name
    let i := (exprEval fuel env i).toNat
    if h : i < arr.size then arr[i] else 0
  | fuel + 1, env, r, .call f as =>
    match env.fns f.name with
    | none => default
    | some d =>
      let vals := argsEval fuel env as
      let callee := (d.params.zip vals).foldl (fun e ((n, _), v) => e.bind n v)
        { env with vars := [] }
      match stmtRun fuel callee d.body.toList with
      | .ret ⟨t', v⟩ => if h : t' = r then h ▸ v else default
      | _ => default
termination_by fuel _ _ _ => fuel

def argsEval (fuel : Nat) (env : Env) {ts : List Ty} (as : Args ts) : List Value :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    match as with
    | .nil => []
    | @Args.cons t _ a as => ⟨t, exprEval fuel env a⟩ :: argsEval fuel env as
termination_by fuel

def stmtRun (fuel : Nat) (env : Env) (ss : List Stmt) : Flow :=
  match fuel with
  | 0 => .next env
  | fuel + 1 =>
    match ss with
    | [] => .next env
    | s :: rest =>
      match s with
      | @Stmt.decl t n _ e => stmtRun fuel (env.bind n ⟨t, exprEval fuel env e⟩) rest
      | @Stmt.assign t n e => stmtRun fuel (env.bind n ⟨t, exprEval fuel env e⟩) rest
      | .ite c th el =>
        match stmtRun fuel env (if exprEval fuel env c then th else el).toList with
        | .next env' => stmtRun fuel { env with vars := restore env env' } rest
        | .brk env' => .brk { env with vars := restore env env' }
        | r => r
      | .loop i lo hi body =>
        let hi := exprEval fuel env hi
        let rec go (k : UInt32) (fuel : Nat) (env : Env) : Flow :=
          match fuel with
          | 0 => .next env
          | fuel + 1 =>
            if k < hi then
              match stmtRun fuel (env.bind i ⟨.u32, k⟩) body.toList with
              | .next env' => go (k + 1) fuel { env with vars := restore env env' }
              | .brk env' => .next { env with vars := restore env env' }
              | r => r
            else
              .next env
        termination_by fuel
        match go (exprEval fuel env lo) fuel env with
        | .next env' => stmtRun fuel env' rest
        | r => r
      | .brk => .brk env
      | @Stmt.ret t e => .ret ⟨t, exprEval fuel env e⟩
termination_by fuel

end

def Expr.eval (env : Env) {t : Ty} (e : Expr t) : t.denote :=
  exprEval evalStepBound env e

def Args.eval (env : Env) {ts : List Ty} (as : Args ts) : List Value :=
  argsEval evalStepBound env as

def Stmt.run (env : Env) (ss : List Stmt) : Flow :=
  stmtRun evalStepBound env ss

/-- Call a shader function from Lean (for tests). -/
def FnDef.eval (fns : List FnDef) (f : FnDef) (args : List Value)
    (buffers : String → FloatArray := fun _ => .empty) : Value :=
  let env : Env := { buffers, fns := fun n => fns.find? (·.name == n) }
  let callee := (f.params.zip args).foldl (fun e ((n, _), v) => e.bind n v) env
  match Stmt.run callee f.body.toList with
  | .ret v => v
  | _ => default

end UVL.GPU
