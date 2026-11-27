module

public import LeanQbe.T.OptUtil
public import LeanQbe.T.Flat
public import LeanQbe.T.Fold

/-!
# Conditional Branch Threading & Known-Condition Elimination (`LeanQbe.T.CondThreadOpt`)

Single-pass `O(N)` typed-IR optimizations targeting redundant condition re-tests and constant
boolean/integer block-argument branches:

1. **Path-fact & known-condition elimination (`Func.pathCondOpt`)**:
   Single-pass PHOAS traversal carrying lexical identities (`id : Nat`), `zext`/`sext` symbolic
   keys (`SymBits`), and dominating `.jnz` edge facts (`BoolFact`):
   * Eliminates dominated `.cmp` operations whose outcome is fixed by dominating comparisons
     (identical/swapped operands, `cmpImplies` implication table, unsigned/signed constant-bound
     subsumption `cmpConstImplies`, `x != 0 → x ≥u 1`, and `a <u b → b ≠ 0`), replacing them
     with `.imm true`/`false`.
   * Propagates known `.bool` values (`varEq` and refuted `tf`/`ff` facts) into `.jnz` conditions
     (pruning dead arms), `.select`/`.not`/`.and`/`.or`/`.xor`/`.copy`/`.cmp .bool`, and `.jump`/
     `.ret`/`.exit` arguments.
2. **Constant-arg branch threading & bool-param block splitting (`Func.condThreadPass`)**:
   Two-phase `O(N)` (`TFlat` oracle `CTPlan` + verified PHOAS validator/rewriter):
   * Splits `.jnz`-on-bool-parameter blocks (`splitBool`) into specialized `(b_T, b_F)` blocks
     (omitting dead branches and only keeping a 3-node dispatcher when `≥ 2` dynamic jumps remain).
   * Threads small straight-line jump targets directly into `.jump` sites when constant/known
     arguments resolve a prefix of pure ops + `.jnz` down to `≤ 8` nodes (or tiny `≤ 3`-node
     forwarding blocks), eliminating jump-to-jump chains and constant-arg `test; jcc`.
3. **Combined entrypoints**:
   * `Func.condThreadOpt` / `Fn.condThreadOpt`: `pathCondOpt → condThreadPass`.
   * `Func.condThreadLateOpt`: standalone post-`Legal` wrapper ready for W3 integration.

Correctness (`LeanQbe/T/CondThreadOptLemmas.lean`): `Func.condThreadOpt_wf`,
`Func.condThreadOpt_spec`, `condThread_ok`, `Func.condThreadOpt_callsOk`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

attribute [local instance] Val.inhabited

namespace CondThreadOpt

/-! ## Part 1: Dominating Path-Fact & Known-Condition Elimination (`pathCondOpt`) -/

/-- Extension kind tracked in `SymBits`. -/
inductive ExtKind : Type
  | zext
  | sext
  deriving DecidableEq, Repr, Inhabited

/-- Symbolic bitvector key (`V`-independent): either an `FKey` or a `zext`/`sext` of one. -/
inductive SymBits : Nat → Type
  | fkey {w : Nat} (k : FKey (.bits w)) : SymBits w
  | ext (kind : ExtKind) (m w : Nat) (hle : m ≤ w) (src : FKey (.bits m)) : SymBits w

/-- Kernel-reducible equality on `SymBits w`. -/
def symBitsBeq {w : Nat} : SymBits w → SymBits w → Bool
  | .fkey k₁, .fkey k₂ => fKeyBeq k₁ k₂
  | .ext k₁ m₁ _ _ s₁, .ext k₂ m₂ _ _ s₂ =>
    if h : k₁ = k₂ ∧ m₁ = m₂ then fKeyBeq s₁ (h.2 ▸ s₂) else false
  | _, _ => false

/-- Provenance of a `zext`/`sext` value. -/
structure ExtProv : Type where
  kind : ExtKind
  m : Nat
  w : Nat
  hle : m ≤ w
  src : FKey (.bits m)

/-- A dominating boolean fact active on a path. -/
inductive BoolFact : Type
  | varEq (id : Nat) (b : Bool)
  | cmpBits (o : CmpOp) (w : Nat) (lhs rhs : SymBits w)
  | cmpBool (o : CmpOp) (lhs rhs : FKey .bool)

/-- `V`-independent value metadata for `pathCondOpt`. -/
structure PInfo : Type where
  id : Option Nat := none
  tf : List BoolFact := []
  ff : List BoolFact := []
  ext? : Option ExtProv := none

/-- Value representation during `pathCondOpt`. -/
structure PVal (V : Ty → Type) (t : Ty) : Type where
  out : Arg V t
  info : PInfo

/-- Fresh `PVal` for bound variable `v` with lexical identity `next` (seeding `.varEq next` facts
for `.bool` variables). -/
def PVal.fresh {V : Ty → Type} : (t : Ty) → V t → Nat → PVal V t
  | .bool, v, next =>
    ⟨.var v, ⟨some next, [.varEq next true], [.varEq next false], none⟩⟩
  | _, v, next => ⟨.var v, ⟨some next, [], [], none⟩⟩

/-- Wrap bound variables `xs : Tup V ts` into fresh `PVal V`s starting at `next`. -/
abbrev freshPVals {V : Ty → Type} : (ts : List Ty) → Tup V ts → Nat → Tup (PVal V) ts :=
  tupFreshWith fun {t} x next => PVal.fresh t x next

/-- Extract `PInfo` of an `Arg (PVal V) t`. -/
def pInfo {V : Ty → Type} {t : Ty} : Arg (PVal V) t → PInfo
  | .var p => p.info
  | .imm _ => {}

/-- Extract output `Arg V t` of an `Arg (PVal V) t`. -/
def pOut {V : Ty → Type} {t : Ty} : Arg (PVal V) t → Arg V t
  | .var p => p.out
  | .imm c => .imm c

/-- Promote an `Arg (PVal V) t` to `PVal V t`. -/
def toPVal {V : Ty → Type} {t : Ty} : Arg (PVal V) t → PVal V t
  | .var p => p
  | .imm c => ⟨.imm c, {}⟩

/-- Constant boolean `PVal V .bool`. -/
def pBoolImm {V : Ty → Type} (b : Bool) : PVal V .bool :=
  ⟨.imm b, {}⟩

/-- Extract symbolic `FKey t` of an `Arg (PVal V) t`. -/
def pFKey {V : Ty → Type} {t : Ty} (a : Arg (PVal V) t) : Option (FKey t) :=
  match pOut a with
  | .imm c => some (.imm c)
  | .var _ => (pInfo a).id.map .var

/-- Build `SymBits w` for an `Arg (PVal V) (.bits w)` if it has an identity or immediate. -/
def symBits? {V : Ty → Type} {w : Nat} (a : Arg (PVal V) (.bits w)) : Option (SymBits w) :=
  match pOut a with
  | .imm c => some (.fkey (.imm c))
  | .var _ =>
    let info := pInfo a
    match info.ext? with
    | some e =>
      if h : e.w = w then some (.ext e.kind e.m w (h ▸ e.hle) e.src)
      else info.id.map fun i => .fkey (.var i)
    | none => info.id.map fun i => .fkey (.var i)

/-- Map `pOut` across an operand tuple. -/
abbrev tupPOut {V : Ty → Type} :
    {ts : List Ty} → Tup (Arg (PVal V)) ts → Tup (Arg V) ts :=
  tupMapArg fun _ => pOut

/-! ## Comparison implication and path-fact queries -/

/-- Implication between two `CmpOp`s on the same ordered pair `(x, y)`:
if `x o₁ y = true`, returns `some b` when `x o₂ y` is forced to `b`. -/
def cmpImplies (o₁ o₂ : CmpOp) : Option Bool :=
  if o₁ == o₂ then some true
  else if o₁ == o₂.neg then some false
  else match o₁, o₂ with
  | .eq, .ule | .eq, .uge | .eq, .sle | .eq, .sge => some true
  | .eq, .ult | .eq, .ugt | .eq, .slt | .eq, .sgt => some false
  | .ult, .ule | .ult, .ne => some true
  | .ult, .eq | .ult, .ugt => some false
  | .ugt, .uge | .ugt, .ne => some true
  | .ugt, .eq | .ugt, .ult => some false
  | .slt, .sle | .slt, .ne => some true
  | .slt, .eq | .slt, .sgt => some false
  | .sgt, .sge | .sgt, .ne => some true
  | .sgt, .eq | .sgt, .slt => some false
  | _, _ => none

/-- Unsigned tight upper bound `x.toNat ≤ u` implied by `x o c`. -/
def uUpper? {n : Nat} : CmpOp → BitVec n → Option Nat
  | .ule, c => some c.toNat
  | .ult, c => if c.toNat == 0 then none else some (c.toNat - 1)
  | _, _ => none

/-- Unsigned tight lower bound `l ≤ x.toNat` implied by `x o c`. -/
def uLower? {n : Nat} : CmpOp → BitVec n → Option Nat
  | .uge, c => some c.toNat
  | .ugt, c => some (c.toNat + 1)
  | .ne, c => if c == 0#n then some 1 else none
  | _, _ => none

/-- Signed tight upper bound `x.toInt ≤ u` implied by `x o c`. -/
def sUpper? {n : Nat} : CmpOp → BitVec n → Option Int
  | .sle, c => some c.toInt
  | .slt, c => some (c.toInt - 1)
  | _, _ => none

/-- Signed tight lower bound `l ≤ x.toInt` implied by `x o c`. -/
def sLower? {n : Nat} : CmpOp → BitVec n → Option Int
  | .sge, c => some c.toInt
  | .sgt, c => some (c.toInt + 1)
  | _, _ => none

/-- Check whether `x o₁ c₁ = true` implies `x o₂ c₂ = b`. -/
def cmpConstImplies {n : Nat} (o₁ : CmpOp) (c₁ : BitVec n) (o₂ : CmpOp) (c₂ : BitVec n) :
    Option Bool :=
  if o₁ == .eq then some (CmpOp.evalBits o₂ c₁ c₂)
  else if o₁ == .ne && o₂ == .eq && c₁ == c₂ then some false
  else if o₁ == .ne && o₂ == .ne && c₁ == c₂ then some true
  else
    match uUpper? o₁ c₁ with
    | some u =>
      match o₂ with
      | .ult => if u < c₂.toNat then some true else none
      | .ule => if u ≤ c₂.toNat then some true else none
      | .ugt => if u ≤ c₂.toNat then some false else none
      | .uge => if u < c₂.toNat then some false else none
      | .eq => if u < c₂.toNat then some false else none
      | .ne => if u < c₂.toNat then some true else none
      | _ => none
    | none =>
      match uLower? o₁ c₁ with
      | some l =>
        match o₂ with
        | .ugt => if c₂.toNat < l then some true else none
        | .uge => if c₂.toNat ≤ l then some true else none
        | .ult => if c₂.toNat ≤ l then some false else none
        | .ule => if c₂.toNat < l then some false else none
        | .eq => if c₂.toNat < l then some false else none
        | .ne => if c₂.toNat < l then some true else none
        | _ => none
      | none =>
        match sUpper? o₁ c₁ with
        | some u =>
          match o₂ with
          | .slt => if u < c₂.toInt then some true else none
          | .sle => if u ≤ c₂.toInt then some true else none
          | .sgt => if u ≤ c₂.toInt then some false else none
          | .sge => if u < c₂.toInt then some false else none
          | .eq => if u < c₂.toInt then some false else none
          | .ne => if u < c₂.toInt then some true else none
          | _ => none
        | none =>
          match sLower? o₁ c₁ with
          | some l =>
            match o₂ with
            | .sgt => if c₂.toInt < l then some true else none
            | .sge => if c₂.toInt ≤ l then some true else none
            | .slt => if c₂.toInt ≤ l then some false else none
            | .sle => if c₂.toInt < l then some false else none
            | .eq => if c₂.toInt < l then some false else none
            | .ne => if c₂.toInt < l then some true else none
            | _ => none
          | none => none

/-- Check whether one fact `x₁ o₁ y₁` implies `x o₂ y = b`. -/
def factImpliesCmpBits {w : Nat} (o₁ : CmpOp) (x₁ y₁ : SymBits w)
    (o₂ : CmpOp) (x y : SymBits w) : Option Bool :=
  if symBitsBeq x x₁ && symBitsBeq y y₁ then
    cmpImplies o₁ o₂
  else if symBitsBeq x y₁ && symBitsBeq y x₁ then
    cmpImplies o₁ o₂.swap
  else
    match y₁, y with
    | .fkey (.imm c₁), .fkey (.imm c₂) =>
      if symBitsBeq x x₁ then cmpConstImplies o₁ c₁ o₂ c₂ else none
    | _, .fkey (.imm c₂) =>
      -- `a <u b` (`a >u b`) implies `b >u 0` (`a >u 0`), i.e., `≠ 0` and `≥u 1`
      let matchesHi := (o₁ == .ult && symBitsBeq x y₁) || (o₁ == .ugt && symBitsBeq x x₁)
      if matchesHi then
        if c₂ == 0#w then
          match o₂ with
          | .eq | .ult | .ule => some false
          | .ne | .ugt | .uge => some true
          | _ => none
        else if c₂ == 1#w && 0 < w then
          match o₂ with
          | .uge => some true
          | .ult => some false
          | _ => none
        else none
      else none
    | _, _ => none

/-- Query `facts` for the boolean outcome of `x o y` at `.bits w`. -/
def queryCmpBits (facts : List BoolFact) (o : CmpOp) (w : Nat) (x y : SymBits w) : Option Bool :=
  match facts with
  | [] => none
  | f :: rest =>
    let res := match f with
      | .cmpBits o₁ w₁ x₁ y₁ =>
        if h : w₁ = w then factImpliesCmpBits o₁ (h ▸ x₁) (h ▸ y₁) o x y else none
      | _ => none
    match res with
    | some b => some b
    | none => queryCmpBits rest o w x y

/-- Query `facts` for the boolean outcome of `x o y` at `.bool`. -/
def queryCmpBool (facts : List BoolFact) (o : CmpOp) (x y : FKey .bool) : Option Bool :=
  match facts with
  | [] => none
  | .cmpBool o₁ x₁ y₁ :: rest =>
    let res :=
      if fKeyBeq x x₁ && fKeyBeq y y₁ then cmpImplies o₁ o
      else if fKeyBeq x y₁ && fKeyBeq y x₁ then cmpImplies o₁ o.swap
      else none
    match res with
    | some b => some b
    | none => queryCmpBool rest o x y
  | _ :: rest => queryCmpBool rest o x y

/-- Look up a `varEq` fact for identity `i`. -/
def lookupVarFact (facts : List BoolFact) (i : Nat) : Option Bool :=
  match facts with
  | [] => none
  | .varEq j b :: rest => if i == j then some b else lookupVarFact rest i
  | _ :: rest => lookupVarFact rest i

/-- True iff `facts` directly refutes `f` (`f` must evaluate to `false` under `facts`). -/
def factRefuted (facts : List BoolFact) : BoolFact → Bool
  | .varEq i b => match lookupVarFact facts i with | some b' => b != b' | none => false
  | .cmpBits o w l r => queryCmpBits facts o w l r == some false
  | .cmpBool o l r => queryCmpBool facts o l r == some false

/-- Resolve a `.bool` operand `a` to a known constant `Bool` using `.imm`, `varEq`, or refuted
`tf`/`ff` branch facts. -/
def resolveBool? {V : Ty → Type} (facts : List BoolFact) (a : Arg (PVal V) .bool) : Option Bool :=
  match pOut a with
  | .imm b => some b
  | .var _ =>
    let info := pInfo a
    match info.id.bind (lookupVarFact facts) with
    | some b => some b
    | none =>
      if info.tf.any (factRefuted facts) then some false
      else if info.ff.any (factRefuted facts) then some true
      else none

/-- Resolve a `.bool` operand, replacing known variables with `.imm b`. -/
def resolveBoolArg {V : Ty → Type} (facts : List BoolFact) (a : Arg (PVal V) .bool) :
    Arg (PVal V) .bool :=
  match resolveBool? facts a with
  | some b => .imm b
  | none => a

/-- Resolve any `.bool`-typed elements inside an operand tuple `Tup (Arg (PVal V)) ts` to `.imm`
when known in `facts`. -/
def resolveBoolArgs {V : Ty → Type} (facts : List BoolFact) :
    {ts : List Ty} → Tup (Arg (PVal V)) ts → Tup (Arg (PVal V)) ts
  | [], () => ()
  | .bool :: _, (a, as) => (resolveBoolArg facts a, resolveBoolArgs facts as)
  | _ :: _, (a, as) => (a, resolveBoolArgs facts as)

/-! ## Single-step `let_` simplification (`pcStep`) -/

/-- Outcome of lowering one `let_` binding in `pathCondOpt`. -/
inductive PCStep (V : Ty → Type) (ts : List Ty) : Type
  | elim (res : Tup (PVal V) ts)
  | emit (op : Op V ts) (wrap : Tup V ts → Tup (PVal V) ts)

/-- Build `PVal V .bool` wrapper for a non-eliminated `.let_` binding with `(tf, ff)` facts. -/
def wrapBool {V : Ty → Type} (next : Nat) (tf ff : List BoolFact) :
    Tup V [.bool] → Tup (PVal V) [.bool]
  | (x, ()) =>
    (⟨.var x, ⟨some next, .varEq next true :: tf, .varEq next false :: ff, none⟩⟩, ())

/-- Build `PVal V (.bits w)` wrapper for an emitted `zext`/`sext` binding. -/
def wrapExt {V : Ty → Type} (next : Nat) (kind : ExtKind) (m w : Nat) (hle : m ≤ w)
    (src : FKey (.bits m)) : Tup V [.bits w] → Tup (PVal V) [.bits w]
  | (x, ()) => (⟨.var x, ⟨some next, [], [], some ⟨kind, m, w, hle, src⟩⟩⟩, ())

/-- Lower one `OpCode` + operand tuple under dominating path facts `facts`. -/
def pcStepAux {V : Ty → Type} : {sig ts : List Ty} →
    OpCode sig ts → Tup (Arg (PVal V)) sig → List BoolFact → Nat → PCStep V ts
  | _, _, .copy _, (a, ()), _, _ =>
    match a with
    | .var p => .elim (p, ())
    | .imm c => .elim (⟨.imm c, {}⟩, ())
  | _, _, .not .bool, (a, ()), facts, next =>
    let a' := resolveBoolArg facts a
    match pOut a' with
    | .imm b => .elim (pBoolImm (!b), ())
    | .var _ =>
      let info := pInfo a'
      .emit (op1 (.not .bool) (pOut a')) (wrapBool next info.ff info.tf)
  | _, _, .and .bool, (a, b, ()), facts, next =>
    let a' := resolveBoolArg facts a
    let b' := resolveBoolArg facts b
    match pOut a', pOut b' with
    | .imm false, _ | _, .imm false => .elim (pBoolImm false, ())
    | .imm true, _ => .elim (toPVal b', ())
    | _, .imm true => .elim (toPVal a', ())
    | .var _, .var _ =>
      let ia := pInfo a'
      let ib := pInfo b'
      if ia.id == ib.id && ia.id.isSome then .elim (toPVal a', ())
      else
        .emit (op2 (.and .bool) (pOut a') (pOut b'))
          (wrapBool next (ia.tf ++ ib.tf) [])
  | _, _, .or .bool, (a, b, ()), facts, next =>
    let a' := resolveBoolArg facts a
    let b' := resolveBoolArg facts b
    match pOut a', pOut b' with
    | .imm true, _ | _, .imm true => .elim (pBoolImm true, ())
    | .imm false, _ => .elim (toPVal b', ())
    | _, .imm false => .elim (toPVal a', ())
    | .var _, .var _ =>
      let ia := pInfo a'
      let ib := pInfo b'
      if ia.id == ib.id && ia.id.isSome then .elim (toPVal a', ())
      else
        .emit (op2 (.or .bool) (pOut a') (pOut b'))
          (wrapBool next [] (ia.ff ++ ib.ff))
  | _, _, .xor .bool, (a, b, ()), facts, next =>
    let a' := resolveBoolArg facts a
    let b' := resolveBoolArg facts b
    match pOut a', pOut b' with
    | .imm ca, .imm cb => .elim (pBoolImm (ca != cb), ())
    | .imm false, _ => .elim (toPVal b', ())
    | _, .imm false => .elim (toPVal a', ())
    | .imm true, _ =>
      let info := pInfo b'
      .emit (op2 (.xor .bool) (.imm true) (pOut b')) (wrapBool next info.ff info.tf)
    | _, .imm true =>
      let info := pInfo a'
      .emit (op2 (.xor .bool) (pOut a') (.imm true)) (wrapBool next info.ff info.tf)
    | .var _, .var _ =>
      if (pInfo a').id == (pInfo b').id && (pInfo a').id.isSome then .elim (pBoolImm false, ())
      else
        .emit (op2 (.xor .bool) (pOut a') (pOut b')) (fun xs => freshPVals [.bool] xs next)
  | _, _, .select t, (c, x, y, ()), facts, next =>
    let c' := resolveBoolArg facts c
    match pOut c' with
    | .imm true => .elim (toPVal x, ())
    | .imm false => .elim (toPVal y, ())
    | .var _ =>
      .emit (op3 (.select t) (pOut c') (pOut x) (pOut y)) (fun xs => freshPVals [t] xs next)
  | _, _, .zext m n, (a, ()), _, next =>
    if h : m ≤ n then
      match pFKey a with
      | some sk => .emit (op1 (.zext m n) (pOut a)) (wrapExt next .zext m n h sk)
      | none => .emit (op1 (.zext m n) (pOut a)) (fun xs => freshPVals [.bits n] xs next)
    else .emit (op1 (.zext m n) (pOut a)) (fun xs => freshPVals [.bits n] xs next)
  | _, _, .sext m n, (a, ()), _, next =>
    if h : m ≤ n then
      match pFKey a with
      | some sk => .emit (op1 (.sext m n) (pOut a)) (wrapExt next .sext m n h sk)
      | none => .emit (op1 (.sext m n) (pOut a)) (fun xs => freshPVals [.bits n] xs next)
    else .emit (op1 (.sext m n) (pOut a)) (fun xs => freshPVals [.bits n] xs next)
  | _, _, .cmp o (.bits w) _ rfl, (a, b, ()), facts, next =>
    let (o', a', b') := match (pOut a).imm?, (pOut b).imm? with
      | some _, none => (o.swap, b, a)
      | _, _ => (o, a, b)
    match (pOut a').imm?, (pOut b').imm? with
    | some ca, some cb => .elim (pBoolImm (CmpOp.evalBits o' ca cb), ())
    | _, _ =>
      match symBits? a', symBits? b' with
      | some sa, some sb =>
        if symBitsBeq sa sb then
          .elim (pBoolImm o'.isRefl, ())
        else
          match queryCmpBits facts o' w sa sb with
          | some res => .elim (pBoolImm res, ())
          | none =>
            let tf := [.cmpBits o' w sa sb]
            let ff := [.cmpBits o'.neg w sa sb]
            .emit (op2 (.cmp o' (.bits w)) (pOut a') (pOut b')) (wrapBool next tf ff)
      | _, _ =>
        .emit (op2 (.cmp o (.bits w)) (pOut a) (pOut b))
          (fun xs => freshPVals [.bool] xs next)
  | _, _, .cmp o .bool _ rfl, (a, b, ()), facts, next =>
    let a' := resolveBoolArg facts a
    let b' := resolveBoolArg facts b
    match (pOut a').imm?, (pOut b').imm? with
    | some ca, some cb => .elim (pBoolImm (CmpOp.evalBool o ca cb), ())
    | _, _ =>
      if o == .eq && (pOut b').imm? == some true then .elim (toPVal a', ())
      else if o == .eq && (pOut a').imm? == some true then .elim (toPVal b', ())
      else if o == .ne && (pOut b').imm? == some false then .elim (toPVal a', ())
      else if o == .ne && (pOut a').imm? == some false then .elim (toPVal b', ())
      else
        match pFKey a', pFKey b' with
        | some ka, some kb =>
          if fKeyBeq ka kb then .elim (pBoolImm o.isRefl, ())
          else
            match queryCmpBool facts o ka kb with
            | some res => .elim (pBoolImm res, ())
            | none =>
              let extraTf :=
                if o == .eq && (pOut b').imm? == some false then (pInfo a').ff
                else if o == .eq && (pOut a').imm? == some false then (pInfo b').ff
                else if o == .ne && (pOut b').imm? == some true then (pInfo a').ff
                else if o == .ne && (pOut a').imm? == some true then (pInfo b').ff
                else []
              let extraFf :=
                if o == .eq && (pOut b').imm? == some false then (pInfo a').tf
                else if o == .eq && (pOut a').imm? == some false then (pInfo b').tf
                else if o == .ne && (pOut b').imm? == some true then (pInfo a').tf
                else if o == .ne && (pOut a').imm? == some true then (pInfo b').tf
                else []
              let tf := .cmpBool o ka kb :: extraTf
              let ff := .cmpBool o.neg ka kb :: extraFf
              .emit (op2 (.cmp o .bool) (pOut a') (pOut b')) (wrapBool next tf ff)
        | _, _ =>
          .emit (op2 (.cmp o .bool) (pOut a') (pOut b'))
            (fun xs => freshPVals [.bool] xs next)
  | _, ts, code, args, _, next =>
    .emit ⟨code, tupPOut args⟩ (fun xs => freshPVals ts xs next)

/-- Lower one `Op (PVal V) ts` under dominating path facts `facts`. -/
def pcStep {V : Ty → Type} {ts : List Ty} (op : Op (PVal V) ts)
    (facts : List BoolFact) (next : Nat) : PCStep V ts :=
  pcStepAux op.code op.args facts next

/-- Prepend new dominating facts while bounding list length to `48` to stay strictly linear. -/
def pushFacts (newFs facts : List BoolFact) : List BoolFact :=
  (newFs ++ facts).take 48

mutual
/-- Top-down dominating path-fact and known-condition simplification pass. -/
def pathCondOpt {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (facts : List BoolFact) : Expr (PVal V) L rs → Expr V L rs
  | .let_ (ts := ts) op k =>
    match pcStep op facts next with
    | .elim res => pathCondOpt next facts (k res)
    | .emit op' wrap => .let_ op' fun xs => pathCondOpt (next + ts.length) facts (k (wrap xs))
  | .load t a k =>
    .load t (pOut a) fun v => pathCondOpt (next + 1) facts (k (PVal.fresh t v next))
  | .store v a k =>
    .store (pOut v) (pOut a) (pathCondOpt next facts k)
  | .call f (bs := bs) args k =>
    .call f (tupPOut args) fun xs =>
      pathCondOpt (next + bs.length) facts (k (freshPVals bs xs next))
  | .jnz c t e =>
    match resolveBool? facts c with
    | some true => pathCondOpt next facts t
    | some false => pathCondOpt next facts e
    | none =>
      let info := pInfo c
      .jnz (pOut c)
        (pathCondOpt next (pushFacts info.tf facts) t)
        (pathCondOpt next (pushFacts info.ff facts) e)
  | .jump j args => .jump j (tupPOut (resolveBoolArgs facts args))
  | .ret vs => .ret (tupPOut (resolveBoolArgs facts vs))
  | .exit f args => .exit f (tupPOut (resolveBoolArgs facts args))
  | .hlt => .hlt
  | .group bodies k =>
    .group (fun Js => pathCondOptB next facts (bodies Js)) (fun Js => pathCondOpt next facts (k Js))

/-- Block-list companion of `pathCondOpt`. -/
def pathCondOptB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (facts : List BoolFact) :
    {sig : List (List Ty)} → Blocks (PVal V) L rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons (ts := ts) b bs =>
    .cons (fun xs => pathCondOpt (next + ts.length) facts (b (freshPVals ts xs next)))
      (pathCondOptB next facts bs)
end

end CondThreadOpt

open CondThreadOpt in
/-- Dominating path-fact and known-condition elimination on a closed function `Func`. -/
def Func.pathCondOpt {as rs : List Ty} (f : Func as rs) : Func as rs :=
  fun V L xs => CondThreadOpt.pathCondOpt as.length [] (f (PVal V) L (freshPVals as xs 0))

/-! ## Part 2: Constant-Arg Branch Threading & Bool-Param Splitting (`condThreadPass`) -/

namespace CondThreadOpt

/-- Typed member lookup (`Member .bool ts`) from a `Nat` parameter position `p`. -/
def splitMember? : Nat → (ts : List Ty) → Option (Member .bool ts)
  | 0, .bool :: _ => some .here
  | n + 1, _ :: ts => (splitMember? n ts).map .there
  | _, _ => none

/-- Signature obtained by dropping parameter at `m` from `ts`. -/
@[reducible] def eraseMem {α : Type} {u : α} : {ts : List α} → Member u ts → List α
  | _ :: ts, .here => ts
  | t :: _, .there m => t :: eraseMem m

/-- Read element at `m` from `Tup f ts`. -/
def getTupMem {f : Ty → Type} {u : Ty} : {ts : List Ty} → Member u ts → Tup f ts → f u
  | _ :: _, .here, (x, _) => x
  | _ :: _, .there m, (_, xs) => getTupMem m xs

/-- Drop element at `m` from `Tup f ts`. -/
def dropTupMem {f : Ty → Type} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → Tup f ts → Tup f (eraseMem m)
  | _ :: _, .here, (_, xs) => xs
  | _ :: _, .there m, (x, xs) => (x, dropTupMem m xs)

/-- Insert element `v : f u` at `m` into `Tup f (eraseMem m)`. -/
def insertTupMem {f : Ty → Type} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → f u → Tup f (eraseMem m) → Tup f ts
  | _ :: _, .here, v, xs => (v, xs)
  | _ :: _, .there m, v, xs => (xs.1, insertTupMem m v xs.2)

/-- Per-block action inside a `.group` node. -/
inductive BlockAct : Type
  | keep (keepBlock : Bool) (allowThread : Bool)
  | splitBool (paramIdx : Nat) (keepT keepF keepDisp : Bool) (inlineT inlineF : Bool)
  deriving DecidableEq, Repr

mutual
/-- Structural plan guiding constant-arg branch threading and bool-param block splitting. -/
inductive CTPlan : Type
  | leaf
  | node1 (k : CTPlan)
  | node2 (t e : CTPlan)
  | jump (tryInline : Bool)
  | group (acts : List BlockAct) (bs : CTPlanB) (k : CTPlan)
  deriving DecidableEq, Repr

/-- Block-list companion of `CTPlan`. -/
inductive CTPlanB : Type
  | nil
  | cons (b : CTPlan) (bs : CTPlanB)
  deriving DecidableEq, Repr
end

mutual
/-- True iff `p` performs at least one rewrite (split, drop, or jump threading). -/
def CTPlan.hasChanges : CTPlan → Bool
  | .leaf => false
  | .node1 k => k.hasChanges
  | .node2 t e => t.hasChanges || e.hasChanges
  | .jump tryInline => tryInline
  | .group acts bs k =>
    acts.any (fun | .keep true false => false | _ => true) || bs.hasChanges || k.hasChanges

/-- Block-list companion of `CTPlan.hasChanges`. -/
def CTPlanB.hasChanges : CTPlanB → Bool
  | .nil => false
  | .cons b bs => b.hasChanges || bs.hasChanges
end

/-! ### Phase 1: Untrusted `O(N)` `TFlat` statistics & planner (`buildCTPlan`) -/

/-- Per-block jump summary for a group: `(totalJumps, immBoolCounts)` where `immBoolCounts[p]`
counts `(trueJumps, falseJumps)` for parameter `p`. -/
structure BlkStat : Type where
  total : Nat := 0
  immBools : List (Nat × Nat) := []
  deriving Inhabited

/-- Jump-stat map indexed by label level `lvl`. -/
abbrev StatTrie := Trie BlkStat

/-- Merge two `immBools` lists elementwise. -/
def mergeImmLists : List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | [], ys => ys
  | xs, [] => xs
  | (t1, f1) :: xs, (t2, f2) :: ys => (t1 + t2, f1 + f2) :: mergeImmLists xs ys

/-- Summarize boolean immediate arguments of a `.jump` operand tuple (up to first 64 params). -/
def jumpImmBools : Nat → {ts : List Ty} → Tup (Arg K) ts → List (Nat × Nat)
  | 0, _, _ => []
  | _, [], _ => []
  | c + 1, .bool :: _, (a, as) =>
    let pair := match a with | .imm true => (1, 0) | .imm false => (0, 1) | .var _ => (0, 0)
    pair :: jumpImmBools c as
  | c + 1, _ :: _, (_, as) =>
    (0, 0) :: jumpImmBools c as

/-- Merge two `StatTrie`s structurally. -/
def mergeStatTrie : StatTrie → StatTrie → StatTrie
  | .empty, t => t
  | t, .empty => t
  | .node v1 e1 o1, .node v2 e2 o2 =>
    let v := match v1, v2 with
      | some s1, some s2 => some ⟨s1.total + s2.total, mergeImmLists s1.immBools s2.immBools⟩
      | some s1, none => some s1
      | none, some s2 => some s2
      | none, none => none
    .node v (mergeStatTrie e1 e2) (mergeStatTrie o1 o2)

/-- Add one jump occurrence `(total := 1, immBools)` at label level `lvl`. -/
def addStat (st : StatTrie) (lvl : Nat) (imms : List (Nat × Nat)) : StatTrie :=
  let s := match st.find? lvl with
    | some old => ⟨old.total + 1, mergeImmLists old.immBools imms⟩
    | none => ⟨1, imms⟩
  st.insert lvl s

-- Per-`.group` precomputed incoming jump statistics mirroring `.group` structure.
mutual
/-- Per-`.group` jump statistics tree mirroring `TFlat`. -/
inductive StatTree : Type
  | leaf
  | node1 (k : StatTree)
  | node2 (t e : StatTree)
  | group (blkStats : List BlkStat) (bs : StatTreeB) (k : StatTree)

/-- Block-list companion of `StatTree`. -/
inductive StatTreeB : Type
  | nil
  | cons (b : StatTree) (bs : StatTreeB)
end

/-- Collect jump statistics for `[nl, nl + len)` from `st`. -/
def readGroupStats (nl : Nat) : Nat → StatTrie → List BlkStat
  | 0, _ => []
  | len + 1, st => st.getD nl {} :: readGroupStats (nl + 1) len st

mutual
/-- Single bottom-up `O(N)` pass collecting per-group incoming jump statistics. -/
def collectStats {rs : List Ty} (nl : Nat) : TFlat rs → StatTree × StatTrie
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k =>
    let (sk, st) := collectStats nl k
    (.node1 sk, st)
  | .jnz _ t e =>
    let (st1, m1) := collectStats nl t
    let (st2, m2) := collectStats nl e
    (.node2 st1 st2, mergeStatTrie m1 m2)
  | .jump j args =>
    if j < nl then
      let lvl := nl - 1 - j
      (.leaf, addStat .empty lvl (jumpImmBools 64 args))
    else (.leaf, .empty)
  | .ret _ | .exit _ _ | .hlt => (.leaf, .empty)
  | .group (sig := sig) bs k =>
    let nl' := nl + sig.length
    let (sbs, mb) := collectStatsB nl' bs
    let (sk, mk) := collectStats nl' k
    let m := mergeStatTrie mb mk
    let gStats := readGroupStats nl sig.length m
    (.group gStats sbs sk, m)

/-- Block-list companion of `collectStats`. -/
def collectStatsB {rs : List Ty} (nl : Nat) :
    {sig : List (List Ty)} → TBlocks rs sig → StatTreeB × StatTrie
  | _, .nil => (.nil, .empty)
  | _, .cons b bs =>
    let (sb, mb) := collectStats nl b
    let (sbs, mbs) := collectStatsB nl bs
    (.cons sb sbs, mergeStatTrie mb mbs)
end

/-- Safe total pure opcodes eligible for constant-arg branch evaluation in `tryThread`. -/
def isThreadSafeOp {sig rs : List Ty} : OpCode sig rs → Bool
  | .copy _ => true
  | .not t => !t.hasFloat
  | .and t | .or t | .xor t => !t.hasFloat
  | .cmp _ t _ _ => !t.hasFloat
  | .select t => !t.hasFloat
  | .add t | .sub t | .mul t | .neg t => !t.hasFloat
  | .shl t | .lshr t | .ashr t | .rotl t | .rotr t => !t.hasFloat
  | .zext m n | .sext m n => Nat.ble m n
  | .trunc m n => Nat.ble n m
  | .ofBool _ => true
  | _ => false

/-- Bounded AST node count for `TFlat` (returns `none` if `> budget` or contains `.group`). -/
def tflatSmallNoGroup? {rs : List Ty} (budget : Nat) : TFlat rs → Option Nat
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k =>
    match budget with
    | 0 => none
    | b + 1 => (tflatSmallNoGroup? b k).map (· + 1)
  | .jnz _ t e =>
    match budget with
    | 0 => none
    | b + 1 => do
      let st ← tflatSmallNoGroup? b t
      let se ← tflatSmallNoGroup? (b - st) e
      pure (1 + st + se)
  | .jump _ _ | .ret _ | .exit _ _ | .hlt =>
    match budget with
    | 0 => none
    | _ + 1 => some 1
  | .group _ _ => none

mutual
/-- Check whether `tf` contains a jump targeting label index `targetIdx`. -/
def tflatJumpsTo {rs : List Ty} (targetIdx : Nat) : TFlat rs → Bool
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => tflatJumpsTo targetIdx k
  | .jnz _ t e => tflatJumpsTo targetIdx t || tflatJumpsTo targetIdx e
  | .jump j _ => j == targetIdx
  | .ret _ | .exit _ _ | .hlt => false
  | .group (sig := sig) bs k =>
    tblocksJumpsTo (targetIdx + sig.length) bs || tflatJumpsTo (targetIdx + sig.length) k

/-- Block-list companion of `tflatJumpsTo`. -/
def tblocksJumpsTo {rs : List Ty} (targetIdx : Nat) : {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, .nil => false
  | _, .cons b bs => tflatJumpsTo targetIdx b || tblocksJumpsTo targetIdx bs
end

/-- Evaluator environment for `TFlat` head simulation during Phase 1 oracle planning. -/
abbrev SimEnv := Nat → Option ((t : Ty) × Val t)

/-- Look up an `Arg K t` at de Bruijn index `idx` under `nv` and `SimEnv`. -/
def simArg (env : SimEnv) (nv : Nat) {t : Ty} : Arg K t → Option (Val t)
  | .imm c => some c
  | .var idx =>
    if idx < nv then
      match env (nv - 1 - idx) with
      | some ⟨t', v⟩ => castTy t' t v
      | none => none
    else none

/-- Look up all operands in `Tup (Arg K) ts`. -/
def simArgs (env : SimEnv) (nv : Nat) : {ts : List Ty} → Tup (Arg K) ts → Option (Tup Val ts)
  | [], () => some ()
  | _ :: _, (a, as) => do
    let v ← simArg env nv a
    let vs ← simArgs env nv as
    pure (v, vs)

/-- Extend `SimEnv` with constant `c` at `nv`, or `none` if unknown. -/
def simPush (env : SimEnv) (nv : Nat) (t : Ty) (v? : Option (Val t)) : SimEnv :=
  fun k => if k == nv then v?.map fun v => ⟨t, v⟩ else env k

/-- Extend `SimEnv` with `Tup Val ts` starting at `nv`. -/
def simPushConsts (env : SimEnv) (nv : Nat) : {ts : List Ty} → Option (Tup Val ts) → SimEnv
  | [], _ => env
  | t :: _, some (v, vs) => simPushConsts (simPush env nv t (some v)) (nv + 1) (some vs)
  | t :: ts, none => simPushConsts (simPush env nv t none) (nv + 1) (ts := ts) none

/-- Simulate one `isThreadSafeOp` step in `simCanThread`. -/
def simLetStep (env : SimEnv) (nv : Nat) :
    {sig dts : List Ty} → OpCode sig dts → Tup (Arg K) sig → Option (Tup Val dts)
  | _, _, .copy _, (a, ()) => (simArg env nv a).map fun v => (v, ())
  | _, _, code, args =>
    if isThreadSafeOp code then (simArgs env nv args).bind code.eval? else none

/-- Initialize `SimEnv` from jump operand constants. -/
def simInitEnv (env : SimEnv) (nv : Nat) : {us : List Ty} → Tup (Arg K) us → SimEnv
  | [], () => env
  | u :: _, (a, as) =>
    let v? := match a with | .imm c => some c | .var _ => none
    simInitEnv (simPush env nv u v?) (nv + 1) as

/-- Simulate the head of a `TFlat` block `b` (bound with `ts` params) on incoming jump operands
`jumpArgs`, returning `true` iff `tryThread` can inline it cleanly. -/
def simCanThread {rs : List Ty} (blockSelfIdx : Nat) (ts : List Ty) (b : TFlat rs)
    (jumpArgs : Tup (Arg K) ts) : Bool :=
  let env0 := simInitEnv (fun _ => none) 0 jumpArgs
  let rec go (fuel : Nat) (resolved : Bool) (nv : Nat) (env : SimEnv) : TFlat rs → Bool
    | .let_ (ts := dts) ⟨code, args⟩ k =>
      let checkTail := fun tf =>
        let budget := if resolved then 8 else 3
        (tflatSmallNoGroup? budget tf).isSome && !tflatJumpsTo blockSelfIdx tf
      match fuel with
      | 0 => false
      | fuel' + 1 =>
        match simLetStep env nv code args with
        | some res => go fuel' resolved (nv + dts.length) (simPushConsts env nv (some res)) k
        | none => checkTail (.let_ ⟨code, args⟩ k)
    | .jnz c t e =>
      let checkTail := fun tf =>
        let budget := if resolved then 8 else 3
        (tflatSmallNoGroup? budget tf).isSome && !tflatJumpsTo blockSelfIdx tf
      match fuel with
      | 0 => false
      | fuel' + 1 =>
        match simArg env nv c with
        | some true => go fuel' true nv env t
        | some false => go fuel' true nv env e
        | none => checkTail (.jnz c t e)
    | tf =>
      let budget := if resolved then 8 else 3
      (tflatSmallNoGroup? budget tf).isSome && !tflatJumpsTo blockSelfIdx tf
  go 4 false ts.length env0 b

/-- Block descriptor in the top-down `buildCTPlan` environment. -/
structure BlockOracleInfo (rs : List Ty) where
  ts : List Ty
  body : TFlat rs
  act : BlockAct
  selfIdx : Nat

mutual
/-- Exact AST node count of a `TFlat` expression (including nested `.group` blocks). -/
def ctFlatSize {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => 1 + ctFlatSize k
  | .jnz _ t e => 1 + ctFlatSize t + ctFlatSize e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => 1
  | .group bs k => 1 + ctBlocksSize bs + ctFlatSize k

/-- Total AST node count across all blocks in a `TBlocks` tuple. -/
def ctBlocksSize {rs : List Ty} : {s : List (List Ty)} → TBlocks rs s → Nat
  | _, .nil => 0
  | _, .cons b bs => ctFlatSize b + ctBlocksSize bs
end

/-- Peel up to `grpBudget` inner-group AST nodes and pure `.let_` wrappers to find a head
`.jnz (.var idx)` testing a boolean parameter of the enclosing block with constant callers.
Returns `(paramIdx, trueArm, falseArm, hadWrapper)`. -/
def findSplitCandidate? {rs : List Ty} (grpBudget : Nat) (ts : List Ty) (st : BlkStat) :
    TFlat rs → Nat → Bool → Option (Nat × TFlat rs × TFlat rs × Bool)
  | .jnz (.var idx) t e, depth, wrapped =>
    if idx ≥ depth && idx - depth < ts.length then
      let p := ts.length - 1 - (idx - depth)
      match splitMember? p ts with
      | some _ =>
        let (tJ, fJ) := (st.immBools.drop p).headD (0, 0)
        if tJ + fJ > 0 then some (p, t, e, wrapped) else none
      | none => none
    else none
  | .group bs k, depth, _ =>
    let bsz := ctBlocksSize bs
    if bsz ≤ grpBudget then findSplitCandidate? (grpBudget - bsz) ts st k depth true
    else none
  | .let_ (ts := dts) _ k, depth, _ =>
    findSplitCandidate? grpBudget ts st k (depth + dts.length) true
  | _, _, _ => none

/-- Decide the `BlockAct` for block `b` (`ts`) given its incoming `BlkStat` and self index.
When `splitOnly = true`, only bool-param splitting and pure `≤ 1`-node forwarding are enabled
(omitting generic `≤ 3`-node single-pred / dynamic-arg inlining). -/
def decideBlockAct {rs : List Ty} (selfIdx : Nat) (ts : List Ty) (b : TFlat rs) (st : BlkStat)
    (splitOnly : Bool := false) : BlockAct :=
  let selfRec := tflatJumpsTo selfIdx b
  let isPureRet := match b with | .ret _ => true | _ => false
  if !selfRec && (((!isPureRet || st.total ≤ 1) && (tflatSmallNoGroup? 1 b).isSome) ||
      (!splitOnly && st.total ≤ 1 && (tflatSmallNoGroup? 3 b).isSome)) then
    .keep false true
  else
    match findSplitCandidate? 16 ts st b 0 false with
    | some (p, t, e, wrapped) =>
      let (tJ, fJ) := (st.immBools.drop p).headD (0, 0)
      let dynJ := st.total - tJ - fJ
      let inlT := !wrapped && (tflatSmallNoGroup? 8 t).isSome && !tflatJumpsTo selfIdx t
      let inlF := !wrapped && (tflatSmallNoGroup? 8 e).isSome && !tflatJumpsTo selfIdx e
      let keepT := (!inlT && tJ > 0) || dynJ > 0
      let keepF := (!inlF && fJ > 0) || dynJ > 0
      let keepDisp := dynJ ≥ 2
      .splitBool p keepT keepF keepDisp inlT inlF
    | none =>
      let hasGroupHead := match b with | .group _ _ => true | _ => false
      .keep true (st.total > 0 && !hasGroupHead && !splitOnly && !(isPureRet && st.total ≥ 2))

/-- Build `List BlockAct × List (Option (BlockOracleInfo rs))` for all blocks in a `.group`. -/
def decideGroupActs {rs : List Ty} (len : Nat) :
    Nat → {sig : List (List Ty)} → TBlocks rs sig → List BlkStat → (splitOnly : Bool) →
    List BlockAct × List (Option (BlockOracleInfo rs))
  | _, _, .nil, _, _ => ([], [])
  | idx, ts :: _, .cons b bs, stats, splitOnly =>
    let st := stats.headD {}
    let selfIdx := len - 1 - idx
    let act := decideBlockAct selfIdx ts b st splitOnly
    let info : Option (BlockOracleInfo rs) :=
      match act with
      | .keep _ false => none
      | _ => some ⟨ts, b, act, selfIdx⟩
    let (acts, infos) := decideGroupActs len (idx + 1) bs stats.tail splitOnly
    (act :: acts, info :: infos)

mutual
/-- Top-down `O(N)` planner over `TFlat` + `StatTree`, tracking enclosing `BlockOracleInfo`s
(newest label first, matching de Bruijn label index `0`). -/
def buildCTPlan {rs : List Ty} (env : List (Option (BlockOracleInfo rs))) :
    TFlat rs → StatTree → (splitOnly : Bool := false) → CTPlan
  | .let_ _ k, .node1 sk, s | .load _ _ k, .node1 sk, s | .store _ _ k, .node1 sk, s
  | .call _ _ _ k, .node1 sk, s => .node1 (buildCTPlan env k sk s)
  | .jnz _ t e, .node2 st se, s => .node2 (buildCTPlan env t st s) (buildCTPlan env e se s)
  | .jump (ts := ts) j args, .leaf, _ =>
    match (env.drop j).headD none with
    | some info =>
      if h : info.ts = ts then
        let args' : Tup (Arg K) info.ts := h ▸ args
        match info.act with
        | .keep _ false => .jump false
        | .keep _ true => .jump (simCanThread info.selfIdx info.ts info.body args')
        | .splitBool p _ _ _ inlT inlF =>
          match splitMember? p info.ts with
          | some m =>
            match getTupMem m args' with
            | .imm true => .jump inlT
            | .imm false => .jump inlF
            | .var _ => .jump false
          | none => .jump false
      else .jump false
    | none => .jump false
  | .group (sig := sig) bs k, .group blkStats sbs sk, splitOnly =>
    let (acts, newInfos) := decideGroupActs sig.length 0 bs blkStats splitOnly
    let env' := newInfos.reverse ++ env
    .group acts (buildCTPlanB env' bs sbs splitOnly) (buildCTPlan env' k sk splitOnly)
  | _, _, _ => .leaf

/-- Block-list companion of `buildCTPlan`. -/
def buildCTPlanB {rs : List Ty} (env : List (Option (BlockOracleInfo rs))) :
    {sig : List (List Ty)} → TBlocks rs sig → StatTreeB → (splitOnly : Bool := false) → CTPlanB
  | _, .nil, .nil, _ => .nil
  | _, .cons b bs, .cons sb sbs, splitOnly =>
    .cons (buildCTPlan env b sb splitOnly) (buildCTPlanB env bs sbs splitOnly)
  | _, _, _, _ => .nil
end

/-! ### Phase 2: Verified PHOAS validator (`validateCTPlan`) and rewriter (`rewriteCTAux`) -/

/-- Right-associated transformed signature for one `.splitBool` block. -/
@[reducible] def splitSig (keepDisp keepT keepF : Bool) (ts ts' : List Ty) : List (List Ty) :=
  (if keepDisp then [ts] else []) ++
    ((if keepT then [ts'] else []) ++ ((if keepF then [ts'] else []) ++ []))

/-- Transformed signature for one `.splitBool` block indexed directly by `splitMember? p ts`. -/
@[reducible] def splitMemberSig (ts : List Ty) (keepT keepF keepDisp : Bool) :
    Option (Member .bool ts) → List (List Ty)
  | some m => splitSig keepDisp keepT keepF ts (eraseMem m)
  | none => [ts]

/-- Compute the transformed `.group` signature for one block given its `BlockAct`. -/
@[reducible] def actSig (ts : List Ty) : BlockAct → List (List Ty)
  | .keep true _ => [ts]
  | .keep false _ => []
  | .splitBool p keepT keepF keepDisp _ _ =>
    splitMemberSig ts keepT keepF keepDisp (splitMember? p ts)

/-- Compute the transformed `.group` signature from `acts : List BlockAct` and `sig`. -/
@[reducible] def threadSig : List BlockAct → List (List Ty) → List (List Ty)
  | _, [] => []
  | [], ts :: sig => ts :: threadSig [] sig
  | a :: acts, ts :: sig => actSig ts a ++ threadSig acts sig

/-- Optionalized variable type used by `rewriteCTAux` and `validateInline`, where `.var none`
represents an abstract unknown runtime binding introduced inside `validateInline`. -/
abbrev CTOptV (V : Ty → Type) : Ty → Type := fun t => Option (V t)

/-- Lift `Tup V ts` to `Tup (Arg (CTOptV V)) ts` with `.var (some x)`. -/
def toOptArgTup {V : Ty → Type} : {ts : List Ty} → Tup V ts → Tup (Arg (CTOptV V)) ts
  | [], () => ()
  | _ :: _, (x, xs) => (.var (some x), toOptArgTup xs)

/-- Abstract unknown bindings `Tup (Arg (CTOptV V)) ts` with `.var none` for `validateInline`. -/
def noneArgTup {V : Ty → Type} : (ts : List Ty) → Tup (Arg (CTOptV V)) ts
  | [] => ()
  | _ :: ts => (.var none, noneArgTup ts)

/-- Convert an `Arg (CTOptV V) t` back to `Arg V t` (`none` iff an abstract `none` leaked). -/
def toRealArg? {V : Ty → Type} {t : Ty} : Arg (CTOptV V) t → Option (Arg V t)
  | .imm c => some (.imm c)
  | .var (some v) => some (.var v)
  | .var none => none

/-- Convert `Tup (Arg (CTOptV V)) ts` back to `Tup (Arg V) ts`. -/
def toRealArgs? {V : Ty → Type} : {ts : List Ty} → Tup (Arg (CTOptV V)) ts → Option (Tup (Arg V) ts)
  | [], () => some ()
  | _ :: _, (a, as) => do
    let r ← toRealArg? a
    let rs ← toRealArgs? as
    pure (r, rs)

/-- Target label representation for `rewriteCTAux` (without inlining). -/
inductive CTTarget (V : Ty → Type) (L : List Ty → Type) : List Ty → Type
  | keep {ts : List Ty} (l : L ts) : CTTarget V L ts
  | dead {ts : List Ty} : CTTarget V L ts
  | split {ts : List Ty} (m : Member .bool ts)
      (lT? : Option (L (eraseMem m)))
      (lF? : Option (L (eraseMem m)))
      (lD? : Option (L ts)) : CTTarget V L ts

/-- Full label representation for `rewriteCTAux`: target + optional bounded head-threading. -/
structure CTLabel (V : Ty → Type) (L : List Ty → Type) (rs : List Ty) (ts : List Ty) where
  target : CTTarget V L ts
  inline? : Tup (Arg (CTOptV V)) ts → Option (Expr V L rs)

/-- Build a label with `inline? := fun _ => none`. -/
def CTLabel.noInline {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} {ts : List Ty}
    (t : CTTarget V L ts) : CTLabel V L rs ts :=
  ⟨t, fun _ => none⟩

/-- True iff `t` can safely emit a jump/branch for operand tuple `args` without hitting `.hlt`. -/
def CTTarget.canEmit {W : Ty → Type} {V : Ty → Type} {L : List Ty → Type} {ts : List Ty}
    (args : Tup (Arg W) ts) : CTTarget V L ts → Bool
  | .keep _ => true
  | .dead => false
  | .split m lT? lF? lD? =>
    match getTupMem m args with
    | .imm true => lT?.isSome
    | .imm false => lF?.isSome
    | .var _ => lD?.isSome || (lT?.isSome && lF?.isSome)

/-- Emit a jump/branch for a validated `CTTarget` (falling back to `.hlt` only if `canEmit` is false
or an abstract `.var none` leaks). -/
def CTTarget.emit {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} {ts : List Ty}
    (args : Tup (Arg (CTOptV V)) ts) : CTTarget V L ts → Expr V L rs
  | .keep l => match toRealArgs? args with | some ra => .jump l ra | none => .hlt
  | .dead => .hlt
  | .split m lT? lF? lD? =>
    match getTupMem m args with
    | .imm true =>
      match lT?, toRealArgs? (dropTupMem m args) with
      | some lT, some ra => .jump lT ra
      | _, _ => .hlt
    | .imm false =>
      match lF?, toRealArgs? (dropTupMem m args) with
      | some lF, some ra => .jump lF ra
      | _, _ => .hlt
    | .var (some v) =>
      match lD? with
      | some lD => match toRealArgs? args with | some ra => .jump lD ra | none => .hlt
      | none =>
        match lT?, lF?, toRealArgs? (dropTupMem m args) with
        | some lT, some lF, some ra => .jnz (.var v) (.jump lT ra) (.jump lF ra)
        | _, _, _ => .hlt
    | .var none => .hlt

/-- Emit a `.jump` through a `CTLabel` (trying `inline?` when `tryInline = true`). -/
def CTLabel.emitJump {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} {ts : List Ty}
    (tryInline : Bool) (j : CTLabel V L rs ts) (args : Tup (Arg (CTOptV V)) ts) : Expr V L rs :=
  if tryInline then
    match j.inline? args with
    | some e => e
    | none => j.target.emit args
  else
    j.target.emit args

/-- Tuple of immediate constants from `Tup Val ts`. -/
def immsTup {V : Ty → Type} : {ts : List Ty} → Tup Val ts → Tup (Arg V) ts
  | [], () => ()
  | _ :: _, (c, cs) => (.imm c, immsTup cs)

/-- Single shared helper evaluating `.copy` and constant `isThreadSafeOp` operations over
flattened operands `Tup (Arg V) sig`. -/
def evalThreadLet? {V : Ty → Type} :
    {sig dts : List Ty} → OpCode sig dts → Tup (Arg V) sig → Option (Tup (Arg V) dts)
  | _, _, .copy _, (a, ()) => some (a, ())
  | _, _, code, args =>
    if isThreadSafeOp code then ((tupImms? args).bind code.eval?).map immsTup else none

/-- Step-by-step constant/copy reduction of the head of an expression along `p : CTPlan`,
returning `(resolvedBranch?, p', e')` when at most `fuel` head steps finish. -/
def peelThreadHead {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Nat → Bool → CTPlan → Expr (Arg (CTOptV V)) (CTLabel V L rs) rs →
    Bool × CTPlan × Expr (Arg (CTOptV V)) (CTLabel V L rs) rs
  | 0, res, p, e => (res, p, e)
  | fuel + 1, res, .node1 pk, .let_ ⟨code, args⟩ k =>
    match evalThreadLet? code (flattenArgs args) with
    | some out => peelThreadHead fuel res pk (k out)
    | none => (res, .node1 pk, .let_ ⟨code, args⟩ k)
  | fuel + 1, res, .node2 pt pe, .jnz c t e =>
    match flattenArg c with
    | .imm true => peelThreadHead fuel true pt t
    | .imm false => peelThreadHead fuel true pe e
    | .var _ => (res, .node2 pt pe, .jnz c t e)
  | _, res, p, e => (res, p, e)

/-- Unit variable type for `validateCTPlan`. -/
abbrev UnitV : Ty → Type := fun _ => Unit

/-- Validate a `.group`-free inline snippet against `plan` within AST budget `budget`, ensuring
every reachable `.jump` has `j.target.canEmit args' = true` or `(j.inline? args').isSome = true`,
binding runtime results to abstract `.var none` so branch validation never speculates defaults. -/
def validateInline {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Nat → CTPlan → Expr (Arg (CTOptV V)) (CTLabel V L rs) rs → Option Nat
  | 0, _, _ => none
  | b + 1, .node1 pk, .let_ (ts := dts) ⟨code, args⟩ k =>
    match evalThreadLet? code (flattenArgs args) with
    | some out => validateInline (b + 1) pk (k out)
    | none => (validateInline b pk (k (noneArgTup dts))).map (· + 1)
  | b + 1, .node1 pk, .load _ _ k =>
    (validateInline b pk (k (.var none))).map (· + 1)
  | b + 1, .node1 pk, .store _ _ k =>
    (validateInline b pk k).map (· + 1)
  | b + 1, .node1 pk, .call _ (bs := bs) _ k =>
    (validateInline b pk (k (noneArgTup bs))).map (· + 1)
  | b + 1, .node2 pt pe, .jnz c t e =>
    match flattenArg c with
    | .imm true => validateInline (b + 1) pt t
    | .imm false => validateInline (b + 1) pe e
    | .var _ => do
      let st ← validateInline b pt t
      let se ← validateInline (b - st) pe e
      pure (1 + st + se)
  | _ + 1, .jump _, .jump j args =>
    let args' := flattenArgs args
    if j.target.canEmit args' || (j.inline? args').isSome then some 1 else none
  | _ + 1, .leaf, .ret _ | _ + 1, .leaf, .exit _ _ | _ + 1, .leaf, .hlt => some 1
  | _, _, _ => none

/-- Non-`.group` single-pass rewriter used exclusively inside validated inline snippets. -/
def rewriteCTInline {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    CTPlan → Expr (Arg (CTOptV V)) (CTLabel V L rs) rs → Expr V L rs
  | .node1 pk, .let_ ⟨code, args⟩ k =>
    let args' := flattenArgs args
    match evalThreadLet? code args' with
    | some out => rewriteCTInline pk (k out)
    | none =>
      match toRealArgs? args' with
      | some rargs => .let_ ⟨code, rargs⟩ fun xs => rewriteCTInline pk (k (toOptArgTup xs))
      | none => .hlt
  | .node1 pk, .load t a k =>
    match toRealArg? (flattenArg a) with
    | some ra => .load t ra fun v => rewriteCTInline pk (k (.var (some v)))
    | none => .hlt
  | .node1 pk, .store v a k =>
    match toRealArg? (flattenArg v), toRealArg? (flattenArg a) with
    | some rv, some ra => .store rv ra (rewriteCTInline pk k)
    | _, _ => .hlt
  | .node1 pk, .call f args k =>
    match toRealArgs? (flattenArgs args) with
    | some rargs => .call f rargs fun xs => rewriteCTInline pk (k (toOptArgTup xs))
    | none => .hlt
  | .node2 pt pe, .jnz c t e =>
    match flattenArg c with
    | .imm true => rewriteCTInline pt t
    | .imm false => rewriteCTInline pe e
    | .var (some v) => .jnz (.var v) (rewriteCTInline pt t) (rewriteCTInline pe e)
    | .var none => .hlt
  | .jump _, .jump j args =>
    let args' := flattenArgs args
    if j.target.canEmit args' then j.target.emit args'
    else match j.inline? args' with | some e => e | none => .hlt
  | .leaf, .ret vs =>
    match toRealArgs? (flattenArgs vs) with | some rvs => .ret rvs | none => .hlt
  | .leaf, .exit f args =>
    match toRealArgs? (flattenArgs args) with | some rargs => .exit f rargs | none => .hlt
  | .leaf, .hlt => .hlt
  | _, _ => .hlt

/-- Try attaching a depth-1 inline closure onto `l` using `pb` and block function `b`. -/
def tryMakeInlineLabel {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} {ts : List Ty}
    (act : BlockAct) (pb : CTPlan)
    (b : Tup (Arg (CTOptV V)) ts → Expr (Arg (CTOptV V)) (CTLabel V L rs) rs)
    (l : CTLabel V L rs ts) : CTLabel V L rs ts :=
  match act with
  | .keep _ false => l
  | .keep _ true =>
    ⟨l.target, fun args =>
      let (res, p', e') := peelThreadHead 4 false pb (b args)
      let budget := if res then 8 else 3
      if (validateInline budget p' e').isSome then
        some (rewriteCTInline p' e')
      else none⟩
  | .splitBool _ _ _ _ inlT inlF =>
    if inlT || inlF then
      ⟨l.target, fun args =>
        let (res, p', e') := peelThreadHead 4 false pb (b args)
        if res && (validateInline 8 p' e').isSome then
          some (rewriteCTInline p' e')
        else none⟩
    else l

/-- Attach bounded head-inlining closures `inline?` onto `lsNoInl`. -/
def attachInlines {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} →
    Blocks (Arg (CTOptV V)) (CTLabel V L rs) rs sig → Tup (CTLabel V L rs) sig →
    Tup (CTLabel V L rs) sig
  | _, _, [], .nil, () => ()
  | a :: acts, .cons pb pbs, _ :: _, .cons b bs, (l, ls) =>
    (tryMakeInlineLabel a pb b l, attachInlines acts pbs bs ls)
  | _, _, _ :: _, .cons _ bs, (l, ls) =>
    (l, attachInlines [] .nil bs ls)

/-- Slice `Tup L (as ++ bs)` into `(headTargets, tailLabels)`. -/
def splitLabelTup {L : List Ty → Type} : (as bs : List (List Ty)) → Tup L (as ++ bs) →
    Tup L as × Tup L bs
  | [], _, js => ((), js)
  | _ :: _, _, (j, js) =>
    let (hs, ts) := splitLabelTup _ _ js
    ((j, hs), ts)

/-- Extract an optional label from a conditional singleton head of `Tup L`. -/
def splitOptLabel {L : List Ty → Type} {ts : List Ty} :
    (b : Bool) → {rest : List (List Ty)} → Tup L ((if b then [ts] else []) ++ rest) →
    Option (L ts) × Tup L rest
  | true, _, (l, rest) => (some l, rest)
  | false, _, rest => (none, rest)

/-- Helper for `mkActTarget` indexed directly on `splitMember? p ts`, avoiding dependent casts. -/
def mkSplitTarget {V : Ty → Type} {L : List Ty → Type} (ts : List Ty)
    (keepT keepF keepDisp : Bool) :
    (sp : Option (Member .bool ts)) → Tup L (splitMemberSig ts keepT keepF keepDisp sp) →
    CTTarget V L ts
  | none, (l, ()) => .keep l
  | some m, js =>
    let (lD?, tfPart) := splitOptLabel keepDisp js
    let (lT?, fPart) := splitOptLabel keepT tfPart
    let (lF?, _) := splitOptLabel keepF fPart
    .split m lT? lF? lD?

/-- Build `CTTarget`s for one block given `act` and its allocated labels `Tup L (actSig ts act)`. -/
def mkActTarget {V : Ty → Type} {L : List Ty → Type} (ts : List Ty) :
    (act : BlockAct) → Tup L (actSig ts act) → CTTarget V L ts
  | .keep true _, (l, ()) => .keep l
  | .keep false _, () => .dead
  | .splitBool p keepT keepF keepDisp _ _, js =>
    mkSplitTarget ts keepT keepF keepDisp (splitMember? p ts) js

/-- Build `Tup (CTLabel V L rs) sig` without `inline?` (`tryInline = false`). -/
def buildTargets {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (acts : List BlockAct) → (sig : List (List Ty)) → Tup L (threadSig acts sig) →
    Tup (CTLabel V L rs) sig
  | _, [], () => ()
  | [], _ :: sig, (j, js) => (CTLabel.noInline (.keep j), buildTargets [] sig js)
  | a :: acts, ts :: sig, js =>
    let (headJs, tailJs) := splitLabelTup (actSig ts a) (threadSig acts sig) js
    (CTLabel.noInline (mkActTarget ts a headJs), buildTargets acts sig tailJs)

/-- Concatenate two `Blocks` lists. -/
def blocksAppend {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {s₁ s₂ : List (List Ty)} → Blocks V L rs s₁ → Blocks V L rs s₂ → Blocks V L rs (s₁ ++ s₂)
  | [], _, .nil, bs₂ => bs₂
  | _ :: _, _, .cons b bs₁, bs₂ => .cons b (blocksAppend bs₁ bs₂)

/-- Prepend a block conditionally, avoiding dependent list casts. -/
def condConsBlock {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} {ts : List Ty}
    (b : Bool) (blk : Unit → Tup V ts → Expr V L rs) {rest : List (List Ty)}
    (tl : Blocks V L rs rest) : Blocks V L rs ((if b then [ts] else []) ++ rest) :=
  match b with
  | true => .cons (blk ()) tl
  | false => tl

/-- Fallback `.hlt` blocks for mismatched plan branches rejected by `validateCTPlan`. -/
def mkHltBlocks {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (sig : List (List Ty)) → Blocks V L rs sig
  | [] => .nil
  | _ :: sig => .cons (fun _ => .hlt) (mkHltBlocks sig)

/-- Assemble transformed blocks for a `.splitBool` block (dispatcher, true-arm, false-arm). -/
def mkSplitBlocks {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} {ts : List Ty}
    (m : Member .bool ts) (keepDisp keepT keepF : Bool) (lbl : CTLabel V L rs ts)
    (rwT : Tup V (eraseMem m) → Expr V L rs)
    (rwF : Tup V (eraseMem m) → Expr V L rs) :
    Blocks V L rs (splitSig keepDisp keepT keepF ts (eraseMem m)) :=
  condConsBlock keepDisp (fun () xs =>
    match lbl.target with
    | .split m' (some lT) (some lF) _ =>
      let args' := dropTupMem m' (toArgTup xs)
      .jnz (.var (getTupMem m' xs)) (.jump lT args') (.jump lF args')
    | _ => .hlt)
    (condConsBlock keepT (fun () => rwT)
      (condConsBlock keepF (fun () => rwF) .nil))

/-- Helper for `rewriteCTBlocks` indexed on `splitMember? p ts`, avoiding dependent casts. -/
def mkSplitCurBlocks {V : Ty → Type} {L : List Ty → Type} {rs ts : List Ty}
    (keepT keepF keepDisp : Bool) (l : CTLabel V L rs ts)
    (rwId : Tup V ts → Expr V L rs)
    (rwSplit : (m : Member .bool ts) → Bool → Tup V (eraseMem m) → Expr V L rs) :
    (sp : Option (Member .bool ts)) →
    Blocks V L rs (splitMemberSig ts keepT keepF keepDisp sp)
  | none => .cons rwId .nil
  | some m => mkSplitBlocks m keepDisp keepT keepF l (rwSplit m true) (rwSplit m false)

mutual
/-- Emit all transformed blocks of a `.group`, structurally recursive on `pbs`. -/
def rewriteCTBlocks {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} →
    Blocks (Arg (CTOptV V)) (CTLabel V L rs) rs sig → Tup (CTLabel V L rs) sig →
    Blocks V L rs (threadSig acts sig)
  | acts, _, [], .nil, () => mkHltBlocks (threadSig acts [])
  | [], _, ts :: sig, .cons _ _, _ => mkHltBlocks (threadSig [] (ts :: sig))
  | a :: acts, .nil, ts :: sig, .cons _ _, _ => mkHltBlocks (threadSig (a :: acts) (ts :: sig))
  | a :: acts, .cons pb pbs, ts :: _, .cons b bs, (l, ls) =>
    let cur : Blocks V L rs (actSig ts a) := match a with
      | .keep true _ =>
        .cons (fun xs => rewriteCTAux pb (b (toOptArgTup xs))) .nil
      | .keep false _ => .nil
      | .splitBool p keepT keepF keepDisp _ _ =>
        mkSplitCurBlocks keepT keepF keepDisp l
          (fun xs => rewriteCTAux pb (b (toOptArgTup xs)))
          (fun m bVal xs => rewriteCTAux pb (b (insertTupMem m (.imm bVal) (toOptArgTup xs))))
          (splitMember? p ts)
    blocksAppend cur (rewriteCTBlocks acts pbs bs ls)

/-- Core verified single-pass PHOAS rewriter (`rewriteCTAux`), structurally recursive. -/
def rewriteCTAux {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    CTPlan → Expr (Arg (CTOptV V)) (CTLabel V L rs) rs → Expr V L rs
  | .node1 pk, .let_ ⟨code, args⟩ k =>
    let args' := flattenArgs args
    match evalThreadLet? code args' with
    | some out => rewriteCTAux pk (k out)
    | none =>
      match toRealArgs? args' with
      | some rargs => .let_ ⟨code, rargs⟩ fun xs => rewriteCTAux pk (k (toOptArgTup xs))
      | none => .hlt
  | .node1 pk, .load t a k =>
    match toRealArg? (flattenArg a) with
    | some ra => .load t ra fun v => rewriteCTAux pk (k (.var (some v)))
    | none => .hlt
  | .node1 pk, .store v a k =>
    match toRealArg? (flattenArg v), toRealArg? (flattenArg a) with
    | some rv, some ra => .store rv ra (rewriteCTAux pk k)
    | _, _ => .hlt
  | .node1 pk, .call f args k =>
    match toRealArgs? (flattenArgs args) with
    | some rargs => .call f rargs fun xs => rewriteCTAux pk (k (toOptArgTup xs))
    | none => .hlt
  | .node2 pt pe, .jnz c t e =>
    match flattenArg c with
    | .imm true => rewriteCTAux pt t
    | .imm false => rewriteCTAux pe e
    | .var (some v) => .jnz (.var v) (rewriteCTAux pt t) (rewriteCTAux pe e)
    | .var none => .hlt
  | .jump tryInl, .jump j args =>
    j.emitJump tryInl (flattenArgs args)
  | .leaf, .ret vs =>
    match toRealArgs? (flattenArgs vs) with | some rvs => .ret rvs | none => .hlt
  | .leaf, .exit f args =>
    match toRealArgs? (flattenArgs args) with | some rargs => .exit f rargs | none => .hlt
  | .leaf, .hlt => .hlt
  | .group acts pbs pk, .group (sig := sig) bodies k =>
    .group (sig := threadSig acts sig)
      (fun Js =>
        let lsNoInl := buildTargets acts sig Js
        let lsBody := attachInlines acts pbs (bodies lsNoInl) lsNoInl
        rewriteCTBlocks acts pbs (bodies lsBody) lsNoInl)
      (fun Js =>
        let lsNoInl := buildTargets acts sig Js
        let lsBody := attachInlines acts pbs (bodies lsNoInl) lsNoInl
        rewriteCTAux pk (k lsBody))
  | _, _ => .hlt
end

/-! ### Structural plan validator (`validateCTPlan`) -/

/-- Dummy label token for `validateCTPlan`. -/
abbrev ValidL (rs : List Ty) := CTLabel UnitV (fun _ => Unit) rs

/-- Build `ValidL` targets for `validateCTPlan` matching `actSig` / `threadSig`. -/
def validTargets {rs : List Ty} :
    (acts : List BlockAct) → (sig : List (List Ty)) → Tup (ValidL rs) sig
  | _, [] => ()
  | [], _ :: sig => (CTLabel.noInline (.keep ()), validTargets [] sig)
  | a :: acts, ts :: sig =>
    let tgt : CTTarget UnitV (fun _ => Unit) ts := match a with
      | .keep true _ => .keep ()
      | .keep false _ => .dead
      | .splitBool p keepT keepF keepDisp _ _ =>
        match splitMember? p ts with
        | none => .keep ()
        | some m =>
          .split m (if keepT then some () else none) (if keepF then some () else none)
            (if keepDisp then some () else none)
    (CTLabel.noInline tgt, validTargets acts sig)

/-- Check block action invariant (`keepDisp = true → keepT && keepF`). -/
def validateAct (ts : List Ty) : BlockAct → Bool
  | .keep _ _ => true
  | .splitBool p keepT keepF keepDisp _ _ =>
    match splitMember? p ts with
    | some _ => !keepDisp || (keepT && keepF)
    | none => true

mutual
/-- Validate `CTPlan` structurally and check that every reachable jump is valid (`canEmit` or
self-validated `inline?`). -/
def validateCTPlan {rs : List Ty} :
    CTPlan → Expr (Arg (CTOptV UnitV)) (ValidL rs) rs → Bool
  | .node1 pk, .let_ (ts := dts) ⟨code, args⟩ k =>
    match evalThreadLet? code (flattenArgs args) with
    | some out => validateCTPlan pk (k out)
    | none => validateCTPlan pk (k (toOptArgTup (Tup.units dts)))
  | .node1 pk, .load _ _ k => validateCTPlan pk (k (.var (some ())))
  | .node1 pk, .store _ _ k => validateCTPlan pk k
  | .node1 pk, .call _ (bs := bs) _ k =>
    validateCTPlan pk (k (toOptArgTup (Tup.units bs)))
  | .node2 pt pe, .jnz c t e =>
    match flattenArg c with
    | .imm true => validateCTPlan pt t
    | .imm false => validateCTPlan pe e
    | .var _ => validateCTPlan pt t && validateCTPlan pe e
  | .jump tryInl, .jump j args =>
    let args' := flattenArgs args
    if tryInl then
      match j.inline? args' with
      | some _ => true
      | none => j.target.canEmit args'
    else
      j.target.canEmit args'
  | .leaf, .ret _ | .leaf, .exit _ _ | .leaf, .hlt => true
  | .group acts pbs pk, .group (sig := sig) bodies k =>
    let lsNoInl := validTargets acts sig
    let lsBody := attachInlines acts pbs (bodies lsNoInl) lsNoInl
    validateCTBlocks acts pbs (bodies lsBody) &&
    validateCTPlan pk (k lsBody)
  | _, _ => false

/-- Validate block branches under `pbs` matching `emitActBlocks`. -/
def validateCTBlocks {rs : List Ty} :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} →
    Blocks (Arg (CTOptV UnitV)) (ValidL rs) rs sig → Bool
  | [], .nil, [], .nil => true
  | a :: acts, .cons pb pbs, ts :: _, .cons b bs =>
    let bodyOk := match a with
      | .keep true _ => validateCTPlan pb (b (toOptArgTup (Tup.units ts)))
      | .keep false _ => true
      | .splitBool p keepT keepF _ _ _ =>
        match splitMember? p ts with
        | none => validateCTPlan pb (b (toOptArgTup (Tup.units ts)))
        | some m =>
          let argsBase := toOptArgTup (Tup.units (eraseMem m))
          (!keepT || validateCTPlan pb (b (insertTupMem m (.imm true) argsBase))) &&
          (!keepF || validateCTPlan pb (b (insertTupMem m (.imm false) argsBase)))
    validateAct ts a && bodyOk && validateCTBlocks acts pbs bs
  | _, _, _, _ => false
end

end CondThreadOpt

open CondThreadOpt in
/-- Apply a precomputed `CTPlan` to a closed `Func` if it passes linear `validateCTPlan`. -/
def Func.condThreadWithPlan {as rs : List Ty} (plan : CTPlan) (f : Func as rs) : Func as rs :=
  if validateCTPlan plan (f (Arg (CTOptV UnitV)) (ValidL rs) (toOptArgTup (Tup.units as))) then
    fun V L xs => rewriteCTAux plan (f (Arg (CTOptV V)) (CTLabel V L rs) (toOptArgTup xs))
  else
    f

open CondThreadOpt in
/-- Single `O(N)` pass of constant-arg branch threading and bool-param block splitting on a
closed `Func` (`splitOnly = true` disables generic `≤ 3`-node single-pred inlining). -/
def Func.condThreadPassOnce {as rs : List Ty} (splitOnly : Bool := false)
    (f : Func as rs) : Func as rs × Bool :=
  let tf := reifyFunc f
  let (st, _) := collectStats 0 tf
  let plan := buildCTPlan [] tf st splitOnly
  if plan.hasChanges then (Func.condThreadWithPlan plan (denoteFunc tf), true)
  else (denoteFunc tf, false)

open CondThreadOpt in
/-- Bounded two-iteration constant-arg branch threading and bool-param block splitting on a
closed `Func`. Pass 1 runs full threading; if changes occur, pass 2 runs a split/forwarding
cleanup pass so newly exposed inner forwarders and cascaded splits thread cleanly. -/
def Func.condThreadPass {as rs : List Ty} (f : Func as rs) : Func as rs :=
  let (f1, ch1) := Func.condThreadPassOnce false f
  if ch1 then (Func.condThreadPassOnce true f1).1 else f1

/-- Combined conditional branch threading and dominating known-condition elimination on `Func`. -/
def Func.condThreadOpt {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.condThreadPass (Func.pathCondOpt f)

/-- Named-function wrapper for `Func.condThreadOpt`. -/
def Fn.condThreadOpt (fn : Fn) : Fn :=
  ⟨fn.name, fn.as, fn.rs, Func.condThreadOpt fn.body⟩

/-- Standalone post-`Legal` late-opt wrapper running `condThreadOpt` + `renorm`
(keeping `Opt.lean` untouched until W3 batching). -/
def Func.condThreadLateOpt {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.renorm (Func.condThreadOpt f)

attribute [irreducible] Func.condThreadPass

end LeanQbe.T
