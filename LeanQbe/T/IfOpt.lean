module

public import LeanQbe.T.OptUtil

/-!
# Diamond `jnz` → `select` If-Conversion (`O-M2`, `MB3`)

Pure 100%-PHOAS if-conversion pass (`ifOpt` / `Func.ifOpt`) using local label tagging
`JLabel L ts` (no `reify`/`TFlat`):

* Recognizes 1-block join groups `.group (sig := [ts]) (.cons joinBlk .nil) k` whose entry `k`
  reaches `.jnz c thenArm elseArm` (at root or after straight-line entry prefixes) where:
  - `thenArm` and `elseArm` each contain at most `4` pure, total, non-UB `.let_` instructions
    from the whitelisted safe opcode set (`isSafeOp`, guarding `!t.hasFloat` on arithmetic/shifts/
    comparisons and `m ≤ n`/`n ≤ m` on `zext`/`sext`/`trunc`; excluding `udiv`/`sdiv`/`urem`/`srem`,
    all float ops, `bswap`, `.load`, `.store`, `.call`),
  - both arms terminate at `.jump J argsT` and `.jump J argsE` on the current `.group`'s binder `J`,
  - `ts` consists solely of `select`-compatible non-float types (`!t.hasFloat`).
* Hoists the pure prefixes of both arms, emits nested `.select`s across `.pair`s / elementwise
  tuple `.select`s onto `.bits`/`bool` (keeping identical operands un-selected via symbolic keys),
  and jumps to `J` with the selected arguments while preserving the `.group` structure for
  `SimplifyGroupPlan`. Never turns `.select` into `.jnz` (`G2`).

Correctness (`LeanQbe/T/IfOptLemmas.lean`): `ifOpt_wp`, `ifOpt_wf`, `Func.ifOpt_wf`,
`Func.ifOpt_spec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

namespace IfOptImpl

/-! ## Local PHOAS label tagging and symbolic value keys -/

/-- Label representation for `IfOpt`: `outer` preserves enclosing labels while `loc` tags
the current `.group`'s binder for exact decidable identity checks. -/
inductive JLabel (L : List Ty → Type) : List Ty → Type
  | outer {ts : List Ty} : L ts → JLabel L ts
  | loc {ts : List Ty} (id : Nat) : JLabel L ts

/-- Input variable representation in `ifOpt`: output operand paired with symbolic `FKey`. -/
abbrev IVal (V : Ty → Type) (t : Ty) : Type := Arg V t × FKey t

/-- Output operand of an `Arg (IVal V) t`. -/
def iout {V : Ty → Type} {t : Ty} : Arg (IVal V) t → Arg V t
  | .var p => p.1
  | .imm c => .imm c

/-- Symbolic key of an `Arg (IVal V) t`. -/
def ikey {V : Ty → Type} {t : Ty} : Arg (IVal V) t → FKey t
  | .var p => p.2
  | .imm c => .imm c

/-- Map `iout` across an operand tuple. -/
abbrev tupIOut {V : Ty → Type} :
    {ts : List Ty} → Tup (Arg (IVal V)) ts → Tup (Arg V) ts :=
  tupMapArg fun _ => iout

/-- Wrap bound output variables `xs : Tup V ts` into fresh `IVal V`s starting at `next`. -/
abbrev freshIVals {V : Ty → Type} : (ts : List Ty) → Tup V ts → Nat → Tup (IVal V) ts :=
  tupFreshWith fun x next => (.var x, .var next)

/-- Inhabited dummy `IVal V` tuple for speculative diamond inspection (never emitted). -/
def dummyIVals {V : Ty → Type} : (ts : List Ty) → Nat → Tup (IVal V) ts
  | [], _ => ()
  | _ :: ts, next => ((.imm default, .var next), dummyIVals ts (next + 1))

/-! ## Safe speculative opcode whitelist and diamond pattern checker -/

/-- Whitelist of pure, total, non-UB opcodes eligible for speculative hoisting in `IfOpt`. -/
def isSafeOp {sig rs : List Ty} : OpCode sig rs → Bool
  | .copy _ => true
  | .add t | .sub t | .mul t | .neg t => !t.hasFloat
  | .and _ | .or _ | .xor _ | .not _ => true
  | .shl t | .lshr t | .ashr t | .rotl t | .rotr t => !t.hasFloat
  | .fshl _ | .fshr _ => true
  | .clz _ | .cls _ | .rbit _ | .ctz _ | .popcnt _ => true
  | .cmp _ t _ _ => !t.hasFloat
  | .select _ => true
  | .ofBool _ => true
  | .addc _ | .subb _ | .umulw _ | .smulw _ => true
  | .udiv0 _ | .sdiv0 _ => true
  | .mkpair _ _ | .unpair _ _ => true
  | .zext m n | .sext m n => Nat.ble m n
  | .trunc m n => Nat.ble n m
  | .bitcast _ _ _ => true
  | _ => false

/-- Type eligible for `select` conversion (leaves are `.bool` and `.bits`, no floats). -/
def isSelectTy (t : Ty) : Bool := !t.hasFloat

/-- Signature eligible for `select` conversion. -/
def isSelectSig (ts : List Ty) : Bool := ts.all isSelectTy

/-- Variant of `isSelectTy` optionally restricting to machine `.bits` (`8`/`16`/`32`/`64`) so
post-`Legal` targets never see `.select .bool` or `.select (.pair ..)`. -/
def isSelectTyWith (bitsOnly : Bool) (t : Ty) : Bool :=
  if bitsOnly then match t with | .bits n => [8, 16, 32, 64].contains n | _ => false
  else isSelectTy t

/-- Signature filter parameterized by `bitsOnly`. -/
def isSelectSigWith (bitsOnly : Bool) (ts : List Ty) : Bool :=
  ts.all (isSelectTyWith bitsOnly)

/-- Structural plan for a matched diamond inside a 1-block `.group` continuation. -/
inductive DiamondPlan : Type
  | jnz (nT nE : Nat)
  | let_ (rest : DiamondPlan)
  | load (rest : DiamondPlan)
  | store (rest : DiamondPlan)
  | call (rest : DiamondPlan)

/-- Check that `e` consists of at most `fuel` safe `.let_` bindings terminating at
`.jump (.loc jId) args` with matching signature `jTs`. Returns the `.let_` count on success. -/
def checkArm {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (jId : Nat) (jTs : List Ty) : Nat → Nat → Expr (IVal V) (JLabel L) rs → Option Nat
  | fuel, next, .let_ (ts := ts) op k =>
    if isSafeOp op.code then
      match fuel with
      | 0 => none
      | fuel' + 1 =>
        (checkArm jId jTs fuel' (next + ts.length) (k (dummyIVals ts next))).map (· + 1)
    else none
  | _, _, .jump (ts := ts) (.loc id) _ =>
    if id == jId && Ty.listBeq ts jTs then some 0 else none
  | _, _, _ => none

/-- Check whether `e` is a straight-line entry prefix ending in a diamond `.jnz` whose arms each
have `≤ 4` safe `.let_`s jumping to `(.loc jId)` with `select`-compatible signature `jTs`. -/
def checkDiamondWith {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (bitsOnly : Bool) (jId : Nat) (jTs : List Ty) (next : Nat) :
    Expr (IVal V) (JLabel L) rs → Option DiamondPlan
  | .let_ (ts := ts) _ k =>
    (checkDiamondWith bitsOnly jId jTs (next + ts.length) (k (dummyIVals ts next))).map .let_
  | .load _ _ k =>
    (checkDiamondWith bitsOnly jId jTs (next + 1) (k (.imm default, .var next))).map .load
  | .store _ _ k =>
    (checkDiamondWith bitsOnly jId jTs next k).map .store
  | .call _ (bs := bs) _ k =>
    (checkDiamondWith bitsOnly jId jTs (next + bs.length) (k (dummyIVals bs next))).map .call
  | .jnz _ t e =>
    if isSelectSigWith bitsOnly jTs then
      match checkArm jId jTs 4 next t, checkArm jId jTs 4 next e with
      | some nT, some nE => some (.jnz nT nE)
      | _, _ => none
    else none
  | _ => none

/-- Default (`bitsOnly = false`) alias for `checkDiamondWith`. -/
abbrev checkDiamond {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :=
  @checkDiamondWith V L rs false

/-! ## Hoisting pure arm prefixes and emitting scalar/pair `select`s -/

/-- Recombine pair components without emitting `mkpair` when both components are immediates. -/
def mkPairArg {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} {a b : Ty}
    (x : Arg V a) (y : Arg V b) (cont : Arg V (.pair a b) → Expr V L rs) : Expr V L rs :=
  match x, y with
  | .imm cx, .imm cy => cont (.imm (cx, cy))
  | _, _ => .let_ (op2 (.mkpair a b) x y) fun (p, ()) => cont (.var p)

/-- Decompose a pair `Arg (IVal V) (.pair a b)` into component `Arg (IVal V)`s. -/
def splitPairIVal {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} {a b : Ty}
    (next : Nat) (p : Arg (IVal V) (.pair a b))
    (cont : Nat → Arg (IVal V) a → Arg (IVal V) b → Expr V L rs) : Expr V L rs :=
  match iout p with
  | .imm (c₁, c₂) => cont next (Arg.imm c₁) (Arg.imm c₂)
  | .var v =>
    .let_ (op1 (.unpair a b) (.var v)) fun (v₁, v₂, ()) =>
      cont (next + 2) (Arg.var (.var v₁, .var next)) (Arg.var (.var v₂, .var (next + 1)))

/-- Emit nested `.select`s across a single non-float type `t` onto `.bits`/`.bool`, keeping
identical operands (`fKeyBeq (ikey aT) (ikey aE)`) un-selected. -/
def emitSelectTy {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (c : Arg V .bool) : (t : Ty) → Nat → Arg (IVal V) t → Arg (IVal V) t →
    (Nat → Arg V t → Expr V L rs) → Expr V L rs
  | .bool, next, aT, aE, cont =>
    if fKeyBeq (ikey aT) (ikey aE) then cont next (iout aT)
    else .let_ (op3 (.select .bool) c (iout aT) (iout aE)) fun (r, ()) => cont next (.var r)
  | .bits n, next, aT, aE, cont =>
    if fKeyBeq (ikey aT) (ikey aE) then cont next (iout aT)
    else .let_ (op3 (.select (.bits n)) c (iout aT) (iout aE)) fun (r, ()) => cont next (.var r)
  | .float _, next, aT, _, cont => cont next (iout aT)
  | .pair a b, next, aT, aE, cont =>
    if fKeyBeq (ikey aT) (ikey aE) then cont next (iout aT)
    else
      splitPairIVal next aT fun next₁ aT₁ aT₂ =>
      splitPairIVal next₁ aE fun next₂ aE₁ aE₂ =>
      emitSelectTy c a next₂ aT₁ aE₁ fun next₃ r₁ =>
      emitSelectTy c b next₃ aT₂ aE₂ fun next₄ r₂ =>
      mkPairArg r₁ r₂ fun r => cont next₄ r

/-- Emit elementwise `.select`s over a tuple of arguments `(argsT, argsE)`. -/
def emitSelectTup {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (c : Arg V .bool) : (ts : List Ty) → Nat →
    Tup (Arg (IVal V)) ts → Tup (Arg (IVal V)) ts →
    (Tup (Arg V) ts → Expr V L rs) → Expr V L rs
  | [], _, (), (), cont => cont ()
  | t :: ts, next, (aT, asT), (aE, asE), cont =>
    emitSelectTy c t next aT aE fun next' r =>
    emitSelectTup c ts next' asT asE fun rs' =>
    cont (r, rs')

/-- Hoist `n` `.let_` instructions from a validated diamond arm and pass its final `.jump`
arguments to `cont`. -/
def hoistArm {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (jTs : List Ty) :
    Nat → Nat → Expr (IVal V) (JLabel L) rs →
    (Nat → Tup (Arg (IVal V)) jTs → Expr V L rs) → Expr V L rs
  | 0, next, .jump (ts := ts) _ args, cont =>
    match listTyDecEq ts jTs with
    | isTrue h => cont next (h ▸ args)
    | isFalse _ => .hlt
  | n + 1, next, .let_ (ts := ts) op k, cont =>
    .let_ ⟨op.code, tupIOut op.args⟩ fun xs =>
      hoistArm jTs n (next + ts.length) (k (freshIVals ts xs next)) cont
  | _, _, _, _ => .hlt

/-- Rewrite a planned diamond entry into hoisted `.let_`s + `.select`s + `.jump jLbl`. -/
def hoistDiamond {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} {jTs : List Ty}
    (jLbl : L jTs) : DiamondPlan → Nat → Expr (IVal V) (JLabel L) rs → Expr V L rs
  | .jnz nT nE, next, .jnz c t e =>
    hoistArm jTs nT next t fun next₁ argsT =>
    hoistArm jTs nE next₁ e fun next₂ argsE =>
    emitSelectTup (iout c) jTs next₂ argsT argsE fun selArgs =>
    .jump jLbl selArgs
  | .let_ rest, next, .let_ (ts := ts) op k =>
    .let_ ⟨op.code, tupIOut op.args⟩ fun xs =>
      hoistDiamond jLbl rest (next + ts.length) (k (freshIVals ts xs next))
  | .load rest, next, .load t a k =>
    .load t (iout a) fun v =>
      hoistDiamond jLbl rest (next + 1) (k (.var v, .var next))
  | .store rest, next, .store v a k =>
    .store (iout v) (iout a) (hoistDiamond jLbl rest next k)
  | .call rest, next, .call f (bs := bs) args k =>
    .call f (tupIOut args) fun xs =>
      hoistDiamond jLbl rest (next + bs.length) (k (freshIVals bs xs next))
  | _, _, _ => .hlt

end IfOptImpl

open IfOptImpl

mutual
/-- PHOAS-to-PHOAS if-conversion pass (`MB3`: diamond `jnz` → `select`), preserving `.group`
block structure. When `bitsOnly = true`, only `.bits` (`8/16/32/64`) join values are converted. -/
def ifOptWith {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (bitsOnly : Bool) (depth next : Nat) : Expr (IVal V) (JLabel L) rs → Expr V L rs
  | .let_ (ts := ts) op k =>
    .let_ ⟨op.code, tupIOut op.args⟩ fun xs =>
      ifOptWith bitsOnly depth (next + ts.length) (k (freshIVals ts xs next))
  | .load t a k =>
    .load t (iout a) fun v => ifOptWith bitsOnly depth (next + 1) (k (.var v, .var next))
  | .store v a k =>
    .store (iout v) (iout a) (ifOptWith bitsOnly depth next k)
  | .call f (bs := bs) args k =>
    .call f (tupIOut args) fun xs =>
      ifOptWith bitsOnly depth (next + bs.length) (k (freshIVals bs xs next))
  | .jnz c t e =>
    .jnz (iout c) (ifOptWith bitsOnly depth next t) (ifOptWith bitsOnly depth next e)
  | .jump j args =>
    match j with
    | .outer l => .jump l (tupIOut args)
    | .loc _ => .hlt
  | .ret vs => .ret (tupIOut vs)
  | .exit f args => .exit f (tupIOut args)
  | .hlt => .hlt
  | .group (sig := [ts]) bodies k =>
    let plan? := checkDiamondWith bitsOnly depth ts next (k (.loc depth, ()))
    .group (sig := [ts])
      (fun Js => ifOptBWith bitsOnly (depth + 1) next (bodies (Js.map fun _ l => .outer l)))
      (fun Js =>
        match plan? with
        | some plan => hoistDiamond Js.1 plan next (k (.outer Js.1, ()))
        | none => ifOptWith bitsOnly (depth + 1) next (k (.outer Js.1, ())))
  | .group (sig := []) bodies k =>
    .group
      (fun Js => ifOptBWith bitsOnly depth next (bodies (Js.map fun _ l => .outer l)))
      (fun Js => ifOptWith bitsOnly depth next (k (Js.map fun _ l => .outer l)))
  | .group (sig := _ :: _ :: rest) bodies k =>
    .group
      (fun Js =>
        ifOptBWith bitsOnly (depth + rest.length + 2) next (bodies (Js.map fun _ l => .outer l)))
      (fun Js =>
        ifOptWith bitsOnly (depth + rest.length + 2) next (k (Js.map fun _ l => .outer l)))

/-- Block-list companion of `ifOptWith`. -/
def ifOptBWith {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (bitsOnly : Bool) (depth next : Nat) : {sig : List (List Ty)} →
    Blocks (IVal V) (JLabel L) rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons (ts := ts) b bs =>
    .cons (fun xs => ifOptWith bitsOnly depth (next + ts.length) (b (freshIVals ts xs next)))
      (ifOptBWith bitsOnly depth next bs)
end

/-- Default (`bitsOnly = false`) alias for `ifOptWith`. -/
abbrev ifOpt {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :=
  @ifOptWith V L rs false

/-- Default (`bitsOnly = false`) alias for `ifOptBWith`. -/
abbrev ifOptB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :=
  @ifOptBWith V L rs false

/-- Convert eligible diamond `jnz` patterns into `.select`s on a closed typed function `Func`. -/
def Func.ifOptWith (bitsOnly : Bool) {as rs : List Ty} (f : Func as rs) : Func as rs :=
  fun V L xs =>
    _root_.LeanQbe.T.ifOptWith bitsOnly 0 as.length (f (IVal V) (JLabel L) (freshIVals as xs 0))

/-- Pre-`Legal` if-conversion allowing `.bool`/`.bits`/`.pair` select values. -/
abbrev Func.ifOpt {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.ifOptWith false f

/-- Post-`Legal` if-conversion restricted to machine `.bits` (`8/16/32/64`) select values. -/
def Func.ifOptBits {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.ifOptWith true f

end LeanQbe.T
