module

public import LeanQbe.T.IL
public import LeanQbe.T.Ops
public import LeanQbe.T.Fold
public import LeanQbe.T.Flat
public import LeanQbe.T.WP
public import LeanQbe.T.Module
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.FoldLemmas
public import Kraken.Mem

/-!
# Executable and Verified First-Order Interpreter for Deterministic Kissat IL

This leaf module provides an additive, purely verified Lean executable interpreter
for the deterministic Kissat IL subset (`TFlat` + `OpCode.eval?` + `fuel` + `Kraken.Mem 64`),
along with full formal soundness proofs relating axiomatic `Func.wp` / `ModuleOk` semantics
and fuel-indexed evaluation:
- Complete coverage of the Kissat IL subset: `bool`, `i8`, `i32`, `i64`, all deterministic
  arithmetic, bitwise, shifts, comparisons, extensions, truncations, `ofBool`, `udiv`, `urem`,
  `select`, `umulw`, memory `load`/`store`, direct acyclic `.call`s, `.group`/`.jump`/`.jnz`/`.ret`,
  and `hlt` trap to undefined behavior.
- Full soundness theorems:
  - `interpFlat_sound`: `FramesRel` + `wp` implies `InterpOk` for flat terms.
  - `interpFunc_sound`: `ModuleEnvSound` + `Func.Wf` + `Func.wp` implies `InterpOk` for functions.
  - `interpFn_sound`: `ModuleEnvSound` + `Fn.Wf` + `Func.wp` implies `InterpOk` for top-level `Fn`s.
  - `interpModule_sound`: `ModuleEnvSound` + `lookupFn` + `Func.Wf` + `Func.wp` implies `InterpOk`.
  - `interpModule_not_ub`: `wp` guarantees absence of undefined behavior (`interp ≠ .ub`).
  - `interpModule_ok_witness`: any terminating `.ok` execution witnesses the exact postcondition `Q`.
  - `ModuleOk.env_sound`: a verified closed module (`ModuleOk Γ M`, `M.externs = []`) produces
    a sound evaluation environment (`ModuleEnvSound (Env.ofModule M Γ) M`).
- All proofs are free of `sorry` and depend strictly on standard Lean axioms (`std3`: `propext`,
  `Classical.choice`, `Quot.sound`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

public section

namespace LeanQbe.T

/-! ## Interpreter Data Structures and Execution Semantics -/

/-- Result of interpreter execution. -/
inductive InterpResult (rs : List Ty) where
  | ok (res : Tup Val rs) (m : Mem 64)
  | outOfFuel
  | ub
  | exit (f : Sym) {as : List Ty} (args : Tup Val as) (m : Mem 64)

/-- Postcondition satisfaction for an interpreter result. -/
def InterpOk {rs : List Ty} (Q : Post rs) (X : XPost) : InterpResult rs → Prop
  | .ok res m' => Q res m'
  | .outOfFuel => True
  | .ub => False
  | .exit f args m' => X f _ args m'

theorem InterpOk.mono {rs : List Ty} {Q Q' : Post rs} {X X' : XPost}
    (hQ : ∀ r m, Q r m → Q' r m) (hX : ∀ f as args m, X f as args m → X' f as args m)
    {r : InterpResult rs} (h : InterpOk Q X r) : InterpOk Q' X' r := by
  cases r with
  | ok res m' => exact hQ res m' h
  | outOfFuel => trivial
  | ub => exact False.elim h
  | exit f args m' => exact hX f _ args m' h

/-- Group frame capturing the mutually recursive block entries and captured value environment. -/
structure GroupFrame (rs : List Ty) where
  entries : List ((ts : List Ty) × TFlat rs)
  vs : List ((t : Ty) × Val t)

/-- Convert mutually recursive `TBlocks` into a flat list of entries prepended to `acc`. -/
def pushTBlocks {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig →
    List ((ts : List Ty) × TFlat rs) → List ((ts : List Ty) × TFlat rs)
  | [], .nil, acc => acc
  | _ :: _, .cons (ts := ts) b bs, acc => pushTBlocks bs (⟨ts, b⟩ :: acc)

/-- Construct a `GroupFrame` from `TBlocks` and current environment `vs`. -/
def GroupFrame.ofTBlocks {rs : List Ty} {sig : List (List Ty)}
    (bodies : TBlocks rs sig) (vs : List ((t : Ty) × Val t)) : GroupFrame rs :=
  ⟨pushTBlocks bodies [], vs⟩

/-- Dynamic label lookup traversing lexical group frames using relative de Bruijn index `j`. -/
def lookupLabel {rs : List Ty} : List (GroupFrame rs) → Nat →
    Option ((ts : List Ty) × TFlat rs × List ((t : Ty) × Val t) × List (GroupFrame rs))
  | [], _ => none
  | frame :: rest, j =>
    if j < frame.entries.length then
      match listGet? frame.entries j with
      | some ⟨ts, b⟩ => some ⟨ts, b, frame.vs, frame :: rest⟩
      | none => none
    else
      lookupLabel rest (j - frame.entries.length)

/-- Evaluate an argument in the runtime environment `vs`. -/
def evalArg (vs : List ((t : Ty) × Val t)) {t : Ty} : Arg K t → Option (Val t)
  | .var i => lookupV vs t i
  | .imm c => some c

/-- Evaluate a tuple of arguments in the runtime environment `vs`. -/
def evalArgs (vs : List ((t : Ty) × Val t)) : {ts : List Ty} → Tup (Arg K) ts → Option (Tup Val ts)
  | [], () => some ()
  | _ :: _, (a, as) => do
    let v ← evalArg vs a
    let vs' ← evalArgs vs as
    some (v, vs')

/-- Evaluate an operation using the deterministic `OpCode.eval?`. -/
def evalOp (vs : List ((t : Ty) × Val t)) {rs : List Ty} (op : Op K rs) : Option (Tup Val rs) := do
  let args ← evalArgs vs op.args
  op.code.eval? args

/-- Look up a function by symbol name and signature in a `Module`. -/
def lookupFn (M : Module) (f : Sym) (as bs : List Ty) : Option (Func as bs) :=
  match M.fns.find? (fun fn => fn.name == f && Ty.listBeq fn.as as && Ty.listBeq fn.rs bs) with
  | some fn =>
    match listTyDecEq fn.as as, listTyDecEq fn.rs bs with
    | isTrue h1, isTrue h2 => some (h1 ▸ h2 ▸ fn.body)
    | _, _ => none
  | none => none

/-- Core fuel-indexed interpreter for flat first-order IL terms (`TFlat`). -/
def interpFlat (M : Module) (fuel : Nat) {rs : List Ty}
    (ls : List (GroupFrame rs)) (vs : List ((t : Ty) × Val t))
    (tf : TFlat rs) (m : Mem 64) : InterpResult rs :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match tf with
    | .let_ op k =>
      match evalOp vs op with
      | some r => interpFlat M fuel ls (pushTup r vs) k m
      | none => .ub
    | .load t a k =>
      match evalArg vs a with
      | some a_val =>
        match loadVal m t a_val with
        | some v => interpFlat M fuel ls (⟨t, v⟩ :: vs) k m
        | none => .ub
      | none => .ub
    | .store (t := t) v a k =>
      match evalArg vs v, evalArg vs a with
      | some v_val, some a_val =>
        match m.loadInt a_val t.bytes with
        | some _ => interpFlat M fuel ls vs k (storeMem m t a_val v_val)
        | none => .ub
      | _, _ => .ub
    | .call f (as := as) bs args k =>
      match evalArgs vs args with
      | some vargs =>
        match lookupFn M f as bs with
        | some calleeBody =>
          let calleeTf := reifyFunc calleeBody
          match interpFlat M fuel [] (pushTup vargs []) calleeTf m with
          | .ok rets m' => interpFlat M fuel ls (pushTup rets vs) k m'
          | .outOfFuel => .outOfFuel
          | .ub => .ub
          | .exit sym eargs m' => .exit sym eargs m'
        | none => .ub
      | none => .ub
    | .jnz c t e =>
      match evalArg vs c with
      | some true => interpFlat M fuel ls vs t m
      | some false => interpFlat M fuel ls vs e m
      | none => .ub
    | .jump (ts := ts) j args =>
      match evalArgs vs args with
      | some vargs =>
        match lookupLabel ls j with
        | some ⟨ts', b, vs_tgt, ls_tgt⟩ =>
          match listTyDecEq ts' ts with
          | isTrue hts =>
            let vargs' : Tup Val ts' := hts ▸ vargs
            interpFlat M fuel ls_tgt (pushTup vargs' vs_tgt) b m
          | isFalse _ => .ub
        | none => .ub
      | none => .ub
    | .ret vs' =>
      match evalArgs vs vs' with
      | some rets => .ok rets m
      | none => .ub
    | .exit f args =>
      match evalArgs vs args with
      | some eargs => .exit f eargs m
      | none => .ub
    | .hlt => .ub
    | .group bodies k =>
      let frame := GroupFrame.ofTBlocks bodies vs
      interpFlat M fuel (frame :: ls) vs k m

/-- Interpret a `Func` by reifying to `TFlat` and initializing arguments. -/
def interpFunc (M : Module) (fuel : Nat) {as rs : List Ty}
    (f : Func as rs) (args : Tup Val as) (m : Mem 64) : InterpResult rs :=
  interpFlat M fuel [] (pushTup args []) (reifyFunc f) m

/-- Interpret a top-level `Fn`. -/
def interpFn (M : Module) (fuel : Nat) (fn : Fn) (args : Tup Val fn.as) (m : Mem 64) : InterpResult fn.rs :=
  interpFunc M fuel fn.body args m

/-- Interpret a whole module from a designated entry symbol. -/
def interpModule (M : Module) (fuel : Nat) (entry : Sym)
    (as rs : List Ty) (args : Tup Val as) (m : Mem 64) : InterpResult rs :=
  match lookupFn M entry as rs with
  | some f => interpFunc M fuel f args m
  | none => .ub

/-! ## Helper Lemmas Relating Evaluation and Denotation -/

theorem evalArg_eq_denoteArg (vs : List ((t : Ty) × Val t)) {t : Ty} (a : Arg K t) :
    evalArg vs a = (denoteArg vs a).map Arg.val := by
  cases a with
  | var i =>
    dsimp only [evalArg, denoteArg]
    cases lookupV vs t i with
    | none => rfl
    | some v => rfl
  | imm c => rfl

theorem evalArg_of_denoteArg {vs : List ((t : Ty) × Val t)} {t : Ty} {a : Arg K t} {a' : Arg Val t}
    (h : denoteArg vs a = some a') : evalArg vs a = some a'.val := by
  have := evalArg_eq_denoteArg vs a
  rw [h] at this
  exact this

theorem evalArgs_eq_denoteArgs (vs : List ((t : Ty) × Val t)) :
    {ts : List Ty} → (args : Tup (Arg K) ts) →
    evalArgs vs args = (denoteArgs vs args).map vals
  | [], () => rfl
  | _ :: _, (a, as) => by
    dsimp only [evalArgs, denoteArgs, Option.bind_eq_bind]
    rw [evalArg_eq_denoteArg vs a, evalArgs_eq_denoteArgs vs as]
    cases denoteArg vs a <;> cases denoteArgs vs as <;> rfl

theorem evalArgs_of_denoteArgs {vs : List ((t : Ty) × Val t)} :
    {ts : List Ty} → {args : Tup (Arg K) ts} → {args' : Tup (Arg Val) ts} →
    denoteArgs vs args = some args' → evalArgs vs args = some (vals args')
  | [], (), (), _ => rfl
  | _ :: _, (a, as), (a', as'), h => by
    dsimp only [denoteArgs] at h
    revert h
    cases h1 : denoteArg vs a <;> cases h2 : denoteArgs vs as <;> intro h
    · contradiction
    · contradiction
    · contradiction
    · cases h
      dsimp only [evalArgs]
      rw [evalArg_of_denoteArg h1, evalArgs_of_denoteArgs h2]
      rfl

theorem pushTup_append {α : Type} {f : α → Type} :
    {as : List α} → (xs : Tup f as) → (acc : List ((a : α) × f a)) →
    pushTup xs acc = pushTup xs [] ++ acc
  | [], () , acc => rfl
  | a :: as, (x, xs), acc => by
    change pushTup xs (⟨a, x⟩ :: acc) = pushTup xs [⟨a, x⟩] ++ acc
    rw [pushTup_append xs (⟨a, x⟩ :: acc), pushTup_append xs [⟨a, x⟩]]
    simp only [List.append_assoc, List.singleton_append]

theorem pushTBlocks_append {rs : List Ty} :
    {sig : List (List Ty)} → (bodies : TBlocks rs sig) →
    (acc : List ((ts : List Ty) × TFlat rs)) →
    pushTBlocks bodies acc = pushTBlocks bodies [] ++ acc
  | [], .nil, acc => rfl
  | _ :: _, .cons (ts := ts) b bs, acc => by
    change pushTBlocks bs (⟨ts, b⟩ :: acc) = pushTBlocks bs [⟨ts, b⟩] ++ acc
    rw [pushTBlocks_append bs (⟨ts, b⟩ :: acc), pushTBlocks_append bs [⟨ts, b⟩]]
    simp only [List.append_assoc, List.singleton_append]

theorem pushTBlocks_length {rs : List Ty} :
    {sig : List (List Ty)} → (bodies : TBlocks rs sig) →
    (pushTBlocks bodies []).length = sig.length
  | [], .nil => rfl
  | ts :: sig, .cons b bs => by
    change (pushTBlocks bs [⟨ts, b⟩]).length = (ts :: sig).length
    rw [pushTBlocks_append bs [⟨ts, b⟩]]
    simp [pushTBlocks_length bs]

/-! ## Opcode Soundness Theorem across all 64 OpCodes -/

theorem evalFloat1_isSome (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (t : Ty) (ht : t.isFloatTree = true) (a : Val t) :
    (evalFloat1 op t a).isSome = true := by
  induction t with
  | float f => rfl
  | pair s u ihs ihu =>
    simp only [Ty.isFloatTree, Bool.and_eq_true] at ht
    dsimp only [evalFloat1]
    rcases Option.isSome_iff_exists.1 (ihs ht.1 a.1) with ⟨r1, hr1⟩
    rcases Option.isSome_iff_exists.1 (ihu ht.2 a.2) with ⟨r2, hr2⟩
    simp [hr1, hr2]
  | bool => cases ht
  | bits => cases ht

theorem evalFloat2_isSome (op : Float.Model.Format → Float.Model.UnpackedFloat →
    Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (t : Ty) (ht : t.isFloatTree = true) (a b : Val t) :
    (evalFloat2 op t a b).isSome = true := by
  induction t with
  | float f => rfl
  | pair s u ihs ihu =>
    simp only [Ty.isFloatTree, Bool.and_eq_true] at ht
    dsimp only [evalFloat2]
    rcases Option.isSome_iff_exists.1 (ihs ht.1 a.1 b.1) with ⟨r1, hr1⟩
    rcases Option.isSome_iff_exists.1 (ihu ht.2 a.2 b.2) with ⟨r2, hr2⟩
    simp [hr1, hr2]
  | bool => cases ht
  | bits => cases ht

theorem evalFloat3_isSome (op : Float.Model.Format → Float.Model.UnpackedFloat →
    Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (t : Ty) (ht : t.isFloatTree = true) (a b c : Val t) :
    (evalFloat3 op t a b c).isSome = true := by
  induction t with
  | float f => rfl
  | pair s u ihs ihu =>
    simp only [Ty.isFloatTree, Bool.and_eq_true] at ht
    dsimp only [evalFloat3]
    rcases Option.isSome_iff_exists.1 (ihs ht.1 a.1 b.1 c.1) with ⟨r1, hr1⟩
    rcases Option.isSome_iff_exists.1 (ihu ht.2 a.2 b.2 c.2) with ⟨r2, hr2⟩
    simp [hr1, hr2]
  | bool => cases ht
  | bits => cases ht

/-- Exact operational soundness for all 64 OpCodes: `wp` guarantees `eval?` produces a result satisfying `post`. -/
theorem OpCode.eval?_of_wp : {sig rs : List Ty} → (c : OpCode sig rs) → (args : Tup Val sig) →
    {post : Tup Val rs → Prop} → c.wp args post → ∃ res, c.eval? args = some res ∧ post res
  | _, _, .copy _, (_, ()), _, hw | _, _, .not _, (_, ()), _, hw
  | _, _, .clz _, (_, ()), _, hw | _, _, .cls _, (_, ()), _, hw
  | _, _, .rbit _, (_, ()), _, hw | _, _, .ctz _, (_, ()), _, hw
  | _, _, .popcnt _, (_, ()), _, hw | _, _, .ofBool _, (_, ()), _, hw
  | _, _, .unpair _ _, (_, ()), _, hw | _, _, .bitcast _ _ _, (_, ()), _, hw
  | _, _, .uitofp _ _, (_, ()), _, hw | _, _, .sitofp _ _, (_, ()), _, hw => by
    dsimp only [OpCode.eval?]; exact ⟨_, rfl, hw⟩
  | _, _, .fcvt f g, (a, ()), post, hw => by
    dsimp only [OpCode.eval?]; exact ⟨_, rfl, evalConvertFloat_sound f g a hw⟩
  | _, _, .and _, (_, _, ()), _, hw | _, _, .or _, (_, _, ()), _, hw
  | _, _, .xor _, (_, _, ()), _, hw | _, _, .umulw _, (_, _, ()), _, hw
  | _, _, .smulw _, (_, _, ()), _, hw | _, _, .udiv0 _, (_, _, ()), _, hw
  | _, _, .sdiv0 _, (_, _, ()), _, hw | _, _, .mkpair _ _, (_, _, ()), _, hw
  | _, _, .sha256msg1, (_, _, ()), _, hw | _, _, .sha256msg2, (_, _, ()), _, hw => by
    dsimp only [OpCode.eval?]; exact ⟨_, rfl, hw⟩
  | _, _, .ternlog _ _, (_, _, _, ()), _, hw | _, _, .fshl _, (_, _, _, ()), _, hw
  | _, _, .fshr _, (_, _, _, ()), _, hw | _, _, .select _, (_, _, _, ()), _, hw
  | _, _, .addc _, (_, _, _, ()), _, hw | _, _, .subb _, (_, _, _, ()), _, hw
  | _, _, .sha256rnds2, (_, _, _, ()), _, hw => by
    dsimp only [OpCode.eval?]; exact ⟨_, rfl, hw⟩
  | _, _, .neg _, (_, ()), _, hw => by
    dsimp only [OpCode.wp] at hw; dsimp only [OpCode.eval?]
    revert hw; split <;> intro hw
    · exact False.elim hw
    · exact ⟨_, rfl, hw⟩
  | _, _, .bswap t, (a, ()), _, hw => by
    dsimp only [OpCode.wp] at hw; dsimp only [OpCode.eval?]
    cases h : t.bswapOk
    · simp only [h, Bool.not_false, ↓reduceIte] at hw
    · simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      exact ⟨_, rfl, hw⟩
  | _, _, .zext m n, (_, ()), _, hw => by
    dsimp only [OpCode.wp] at hw; dsimp only [OpCode.eval?]
    obtain ⟨hmn, hp⟩ := hw; simp only [hmn, ↓reduceIte]; exact ⟨_, rfl, hp⟩
  | _, _, .sext m n, (_, ()), _, hw => by
    dsimp only [OpCode.wp] at hw; dsimp only [OpCode.eval?]
    obtain ⟨hmn, hp⟩ := hw; simp only [hmn, ↓reduceIte]; exact ⟨_, rfl, hp⟩
  | _, _, .trunc m n, (_, ()), _, hw => by
    dsimp only [OpCode.wp] at hw; dsimp only [OpCode.eval?]
    obtain ⟨hmn, hp⟩ := hw; simp only [hmn, ↓reduceIte]; exact ⟨_, rfl, hp⟩
  | _, _, .shufd t imm, (_, ()), _, hw => by
    dsimp only [OpCode.wp] at hw; dsimp only [OpCode.eval?]
    obtain ⟨h1, h2, hp⟩ := hw
    simp only [decide_eq_true_iff.mpr h1, beq_iff_eq.mpr h2, Bool.and_self, ↓reduceIte]
    exact ⟨_, rfl, hp⟩
  | _, _, .fneg t, (a, ()), _, hw | _, _, .fabs t, (a, ()), _, hw => by
    dsimp only [OpCode.wp] at hw; dsimp only [OpCode.eval?]
    cases h : t.isFloatTree
    · simp only [h, Bool.not_false, ↓reduceIte] at hw
    · simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      exact ⟨_, rfl, hw⟩
  | _, _, .add _, (_, _, ()), _, hw | _, _, .sub _, (_, _, ()), _, hw
  | _, _, .mul _, (_, _, ()), _, hw | _, _, .shl _, (_, _, ()), _, hw
  | _, _, .lshr _, (_, _, ()), _, hw | _, _, .ashr _, (_, _, ()), _, hw
  | _, _, .rotl _, (_, _, ()), _, hw | _, _, .rotr _, (_, _, ()), _, hw => by
    dsimp only [OpCode.wp] at hw; dsimp only [OpCode.eval?]
    revert hw; split <;> intro hw
    · exact False.elim hw
    · exact ⟨_, rfl, hw⟩
  | _, _, .udiv _, (a, b, ()), _, hw | _, _, .urem _, (a, b, ()), _, hw => by
    dsimp only [OpCode.wp] at hw; dsimp only [OpCode.eval?]
    obtain ⟨h1, hp⟩ := hw; simp only [ne_eq, h1, not_false_eq_true, ↓reduceIte]; exact ⟨_, rfl, hp⟩
  | _, _, .sdiv _, (_, _, ()), _, hw | _, _, .srem _, (_, _, ()), _, hw => by
    dsimp only [OpCode.wp] at hw; dsimp only [OpCode.eval?]
    obtain ⟨h1, hp⟩ := hw; simp only [h1, ↓reduceIte]; exact ⟨_, rfl, hp⟩
  | _, _, .shufb t, (_, _, ()), _, hw | _, _, .alignr t _, (_, _, ()), _, hw
  | _, _, .blendw t _, (_, _, ()), _, hw => by
    dsimp only [OpCode.wp] at hw; dsimp only [OpCode.eval?]
    obtain ⟨h1, h2, hp⟩ := hw
    simp only [decide_eq_true_iff.mpr h1, beq_iff_eq.mpr h2, Bool.and_self, ↓reduceIte]
    exact ⟨_, rfl, hp⟩
  | _, _, .cmp _ t _ h', (_, _, ()), _, hw => by
    subst h'; dsimp only [OpCode.wp] at hw; dsimp only [OpCode.eval?]; simp only [cast_eq]
    cases h : t.hasFloat
    · simp only [h, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      exact ⟨_, rfl, hw⟩
    · simp only [h, ↓reduceIte] at hw
  | _, _, .blend _ _ h', (_, _, _, ()), _, hw => by
    subst h'; dsimp only [OpCode.eval?]
    exact ⟨_, rfl, hw⟩
  | _, _, .fcmp _ t _ h', (_, _, ()), _, hw => by
    subst h'; dsimp only [OpCode.wp] at hw; dsimp only [OpCode.eval?]; simp only [cast_eq]
    cases h : t.isFloatTree
    · simp only [h, Bool.not_false, ↓reduceIte] at hw
    · simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      exact ⟨_, rfl, hw⟩
  | _, _, .fadd t, (a, b, ()), post, hw => by
    dsimp only [OpCode.wp] at hw; dsimp only [OpCode.eval?]
    cases h : t.isFloatTree
    · simp only [h, Bool.not_false, ↓reduceIte] at hw
    · simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      have he := evalFloat2_isSome Float.Model.UnpackedFloat.add t h a b
      rcases Option.isSome_iff_exists.1 he with ⟨r, hr⟩
      have heq : OpCode.eval? (.fadd t) (a, b, ()) = some (r, ()) := by
        dsimp only [OpCode.eval?]; simp [hr]
      have hp := OpCode.eval?_sound (.fadd t) (a, b, ()) post heq (by
        dsimp only [OpCode.wp]; simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hw)
      exact ⟨(r, ()), heq, hp⟩
  | _, _, .fsub t, (a, b, ()), post, hw => by
    dsimp only [OpCode.wp] at hw; dsimp only [OpCode.eval?]
    cases h : t.isFloatTree
    · simp only [h, Bool.not_false, ↓reduceIte] at hw
    · simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      have he := evalFloat2_isSome Float.Model.UnpackedFloat.sub t h a b
      rcases Option.isSome_iff_exists.1 he with ⟨r, hr⟩
      have heq : OpCode.eval? (.fsub t) (a, b, ()) = some (r, ()) := by
        dsimp only [OpCode.eval?]; simp [hr]
      have hp := OpCode.eval?_sound (.fsub t) (a, b, ()) post heq (by
        dsimp only [OpCode.wp]; simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hw)
      exact ⟨(r, ()), heq, hp⟩
  | _, _, .fmul t, (a, b, ()), post, hw => by
    dsimp only [OpCode.wp] at hw; dsimp only [OpCode.eval?]
    cases h : t.isFloatTree
    · simp only [h, Bool.not_false, ↓reduceIte] at hw
    · simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      have he := evalFloat2_isSome Float.Model.UnpackedFloat.mul t h a b
      rcases Option.isSome_iff_exists.1 he with ⟨r, hr⟩
      have heq : OpCode.eval? (.fmul t) (a, b, ()) = some (r, ()) := by
        dsimp only [OpCode.eval?]; simp [hr]
      have hp := OpCode.eval?_sound (.fmul t) (a, b, ()) post heq (by
        dsimp only [OpCode.wp]; simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hw)
      exact ⟨(r, ()), heq, hp⟩
  | _, _, .fdiv t, (a, b, ()), post, hw => by
    dsimp only [OpCode.wp] at hw; dsimp only [OpCode.eval?]
    cases h : t.isFloatTree
    · simp only [h, Bool.not_false, ↓reduceIte] at hw
    · simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      have he := evalFloat2_isSome Float.Model.UnpackedFloat.div t h a b
      rcases Option.isSome_iff_exists.1 he with ⟨r, hr⟩
      have heq : OpCode.eval? (.fdiv t) (a, b, ()) = some (r, ()) := by
        dsimp only [OpCode.eval?]; simp [hr]
      have hp := OpCode.eval?_sound (.fdiv t) (a, b, ()) post heq (by
        dsimp only [OpCode.wp]; simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hw)
      exact ⟨(r, ()), heq, hp⟩
  | _, _, .ffma t, (a, b, d, ()), post, hw => by
    dsimp only [OpCode.wp] at hw; dsimp only [OpCode.eval?]
    cases h : t.isFloatTree
    · simp only [h, Bool.not_false, ↓reduceIte] at hw
    · simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      have he := evalFloat3_isSome Float.Model.UnpackedFloat.fma t h a b d
      rcases Option.isSome_iff_exists.1 he with ⟨r, hr⟩
      have heq : OpCode.eval? (.ffma t) (a, b, d, ()) = some (r, ()) := by
        dsimp only [OpCode.eval?]; simp [hr]
      have hp := OpCode.eval?_sound (.ffma t) (a, b, d, ()) post heq (by
        dsimp only [OpCode.wp]; simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hw)
      exact ⟨(r, ()), heq, hp⟩
  | _, _, .fsqrt t, (a, ()), post, hw => by
    dsimp only [OpCode.wp] at hw; dsimp only [OpCode.eval?]
    cases h : t.isFloatTree
    · simp only [h, Bool.not_false, ↓reduceIte] at hw
    · simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      have he := evalFloat1_isSome Float.Model.UnpackedFloat.sqrt t h a
      rcases Option.isSome_iff_exists.1 he with ⟨r, hr⟩
      have heq : OpCode.eval? (.fsqrt t) (a, ()) = some (r, ()) := by
        dsimp only [OpCode.eval?]; simp [hr]
      have hp := OpCode.eval?_sound (.fsqrt t) (a, ()) post heq (by
        dsimp only [OpCode.wp]; simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hw)
      exact ⟨(r, ()), heq, hp⟩
  | _, _, .fptoui f n, (a, ()), _, hw => by
    dsimp only [OpCode.wp] at hw; dsimp only [OpCode.eval?]
    cases hz : truncToInt (unpackFloat f a) with
    | none => rw [hz] at hw; exact False.elim hw
    | some z =>
      rw [hz] at hw
      obtain ⟨hz0, hzn, hp⟩ := hw
      dsimp only [Option.bind]
      simp only [hz0, hzn, and_self, ↓reduceIte]
      exact ⟨_, rfl, hp⟩
  | _, _, .fptosi f n, (a, ()), _, hw => by
    dsimp only [OpCode.wp] at hw; dsimp only [OpCode.eval?]
    obtain ⟨hn, hw⟩ := hw
    simp only [ne_eq, hn, not_false_eq_true, ↓reduceIte]
    cases hz : truncToInt (unpackFloat f a) with
    | none => rw [hz] at hw; exact False.elim hw
    | some z =>
      rw [hz] at hw
      obtain ⟨hz0, hzn, hp⟩ := hw
      dsimp only [Option.bind]
      simp only [hz0, hzn, and_self, ↓reduceIte]
      exact ⟨_, rfl, hp⟩

/-! ## Label Environment Relations and Group Invariant -/

/-- Build fuel-indexed semantic continuations for a mutual group frame. -/
def mkJs (M : Module) (fuel : Nat) {rs : List Ty} (Q : Post rs) (X : XPost)
    {sig : List (List Ty)} (bodies : TBlocks rs sig)
    (frame_ls : List (GroupFrame rs)) (vs : List ((t : Ty) × Val t)) :
    Tup Cont sig :=
  match sig, bodies with
  | [], .nil => ()
  | _ :: _, .cons b bs =>
      (fun xs m' => ∀ f ≤ fuel, InterpOk Q X (interpFlat M f frame_ls (pushTup xs vs) b m'),
       mkJs M fuel Q X bs frame_ls vs)

/-- Relation between group frame entries and semantic continuations. -/
inductive FrameEntriesRel (M : Module) (fuel : Nat) {rs : List Ty} (Q : Post rs) (X : XPost)
    (ls_tgt : List (GroupFrame rs)) (vs_saved : List ((t : Ty) × Val t)) :
    List ((ts : List Ty) × TFlat rs) → List ((ts : List Ty) × Cont ts) → Prop
  | nil : FrameEntriesRel M fuel Q X ls_tgt vs_saved [] []
  | cons {ts : List Ty} (b : TFlat rs) (J : Cont ts)
      {entries : List ((ts : List Ty) × TFlat rs)} {seg : List ((ts : List Ty) × Cont ts)} :
      (∀ f ≤ fuel, ∀ xs m', J xs m' → InterpOk Q X (interpFlat M f ls_tgt (pushTup xs vs_saved) b m')) →
      FrameEntriesRel M fuel Q X ls_tgt vs_saved entries seg →
      FrameEntriesRel M fuel Q X ls_tgt vs_saved (⟨ts, b⟩ :: entries) (⟨ts, J⟩ :: seg)

theorem frameEntriesRel_mono {M : Module} {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {rs : List Ty} {Q : Post rs} {X : XPost}
    {ls_tgt : List (GroupFrame rs)} {vs_saved : List ((t : Ty) × Val t)}
    {entries : List ((ts : List Ty) × TFlat rs)} {seg : List ((ts : List Ty) × Cont ts)}
    (h : FrameEntriesRel M fuel' Q X ls_tgt vs_saved entries seg) :
    FrameEntriesRel M fuel Q X ls_tgt vs_saved entries seg := by
  induction h with
  | nil => exact .nil
  | cons b J hJ hrest ih =>
    exact .cons b J (fun f hf => hJ f (Nat.le_trans hf hle)) ih

theorem frameEntriesRel_append {M : Module} {fuel : Nat} {rs : List Ty} {Q : Post rs} {X : XPost}
    {ls_tgt : List (GroupFrame rs)} {vs_saved : List ((t : Ty) × Val t)}
    {e1 e2 : List ((ts : List Ty) × TFlat rs)} {s1 s2 : List ((ts : List Ty) × Cont ts)}
    (h1 : FrameEntriesRel M fuel Q X ls_tgt vs_saved e1 s1)
    (h2 : FrameEntriesRel M fuel Q X ls_tgt vs_saved e2 s2) :
    FrameEntriesRel M fuel Q X ls_tgt vs_saved (e1 ++ e2) (s1 ++ s2) := by
  induction h1 generalizing e2 s2 with
  | nil => exact h2
  | cons b J hJ hrest ih =>
    simp only [List.cons_append]
    exact .cons b J hJ (ih h2)

theorem frameEntriesRel_ofTBlocks (M : Module) (fuel : Nat) {rs : List Ty} (Q : Post rs) (X : XPost)
    (frame_ls : List (GroupFrame rs)) (vs : List ((t : Ty) × Val t)) :
    {sig : List (List Ty)} → (bodies : TBlocks rs sig) →
    FrameEntriesRel M fuel Q X frame_ls vs
      (pushTBlocks bodies []) (pushTup (mkJs M fuel Q X bodies frame_ls vs) [])
  | [], .nil => .nil
  | ts :: sig, .cons b bs => by
    change FrameEntriesRel M fuel Q X frame_ls vs
      (pushTBlocks bs [⟨ts, b⟩]) (pushTup (mkJs M fuel Q X bs frame_ls vs) [⟨ts, _⟩])
    rw [pushTBlocks_append bs [⟨ts, b⟩], pushTup_append (mkJs M fuel Q X bs frame_ls vs) [⟨ts, _⟩]]
    exact frameEntriesRel_append
      (frameEntriesRel_ofTBlocks M fuel Q X frame_ls vs bs)
      (.cons b _ (fun f hf xs m' hj => hj f hf) .nil)

theorem frameEntriesRel_length {M : Module} {fuel : Nat} {rs : List Ty} {Q : Post rs} {X : XPost}
    {ls_tgt : List (GroupFrame rs)} {vs_saved : List ((t : Ty) × Val t)}
    {entries : List ((ts : List Ty) × TFlat rs)} {seg : List ((ts : List Ty) × Cont ts)}
    (h : FrameEntriesRel M fuel Q X ls_tgt vs_saved entries seg) :
    entries.length = seg.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ ih => simp [ih]

theorem listGet?_append_left {α : Type} : ∀ (l1 l2 : List α) (idx : Nat),
    idx < l1.length → listGet? (l1 ++ l2) idx = listGet? l1 idx
  | [], _, idx, h => (Nat.not_lt_zero idx h).elim
  | a :: as, l2, 0, _ => rfl
  | a :: as, l2, idx + 1, h => by
    dsimp only [listGet?, List.cons_append]
    exact listGet?_append_left as l2 idx (Nat.lt_of_succ_lt_succ h)

theorem listGet?_append_right {α : Type} : ∀ (l1 l2 : List α) (idx : Nat),
    l1.length ≤ idx → listGet? (l1 ++ l2) idx = listGet? l2 (idx - l1.length)
  | [], l2, idx, _ => rfl
  | a :: as, l2, 0, h => (Nat.not_succ_le_zero as.length h).elim
  | a :: as, l2, idx + 1, h => by
    dsimp only [listGet?, List.cons_append]
    have hle : as.length ≤ idx := Nat.le_of_succ_le_succ h
    rw [listGet?_append_right as l2 idx hle]
    congr 1
    exact (Nat.succ_sub_succ idx as.length).symm

theorem frameEntriesRel_listGet? {M : Module} {fuel : Nat} {rs : List Ty} {Q : Post rs} {X : XPost}
    {ls_tgt : List (GroupFrame rs)} {vs_saved : List ((t : Ty) × Val t)}
    {entries : List ((ts : List Ty) × TFlat rs)} {seg : List ((ts : List Ty) × Cont ts)}
    (hrel : FrameEntriesRel M fuel Q X ls_tgt vs_saved entries seg) :
    ∀ idx, match listGet? entries idx, listGet? seg idx with
      | some ⟨ts, b⟩, some ⟨ts', J⟩ =>
          ∃ h : ts = ts', ∀ f ≤ fuel, ∀ xs m', (h ▸ J) xs m' → InterpOk Q X (interpFlat M f ls_tgt (pushTup xs vs_saved) b m')
      | none, none => True
      | _, _ => False
  | 0 => by
    cases hrel with
    | nil => trivial
    | cons b J hJ _ => exact ⟨rfl, hJ⟩
  | idx + 1 => by
    cases hrel with
    | nil => trivial
    | cons _ _ _ hrest => exact frameEntriesRel_listGet? hrest idx

/-- Relation between list of dynamic group frames and static semantic continuation environment. -/
inductive FramesRel (M : Module) (fuel : Nat) {rs : List Ty} (Q : Post rs) (X : XPost) :
    List (GroupFrame rs) → List ((ts : List Ty) × Cont ts) → Prop
  | nil : FramesRel M fuel Q X [] []
  | cons (frame : GroupFrame rs) (rest : List (GroupFrame rs))
      (seg : List ((ts : List Ty) × Cont ts)) (ls_d' : List ((ts : List Ty) × Cont ts)) :
      FrameEntriesRel M fuel Q X (frame :: rest) frame.vs frame.entries seg →
      FramesRel M fuel Q X rest ls_d' →
      FramesRel M fuel Q X (frame :: rest) (seg ++ ls_d')

theorem framesRel_mono {M : Module} {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {rs : List Ty} {Q : Post rs} {X : XPost}
    {ls_i : List (GroupFrame rs)} {ls_d : List ((ts : List Ty) × Cont ts)}
    (h : FramesRel M fuel' Q X ls_i ls_d) :
    FramesRel M fuel Q X ls_i ls_d := by
  induction h with
  | nil => exact .nil
  | cons frame rest seg ls_d' hEntries hRest ih =>
    exact .cons frame rest seg ls_d' (frameEntriesRel_mono hle hEntries) ih

theorem framesRel_lookup {M : Module} {fuel : Nat} {rs : List Ty} {Q : Post rs} {X : XPost}
    {ls_i : List (GroupFrame rs)} {ls_d : List ((ts : List Ty) × Cont ts)}
    (hrel : FramesRel M fuel Q X ls_i ls_d) :
    ∀ (ts : List Ty) (j : Nat) (j' : Cont ts),
    lookupL ls_d ts j = some j' →
    ∃ b vs_tgt ls_tgt,
      lookupLabel ls_i j = some ⟨ts, b, vs_tgt, ls_tgt⟩ ∧
      (∀ f ≤ fuel, ∀ xs m', j' xs m' → InterpOk Q X (interpFlat M f ls_tgt (pushTup xs vs_tgt) b m')) := by
  induction hrel with
  | nil =>
    intro ts j j' hj
    dsimp only [lookupL, listGet?] at hj
    contradiction
  | cons frame rest seg ls_d' hEntries hRest ih =>
    intro ts j j' hj
    have hlen : frame.entries.length = seg.length := frameEntriesRel_length hEntries
    dsimp only [lookupLabel]
    by_cases hj_lt : j < frame.entries.length
    · simp only [hj_lt, ↓reduceIte]
      have hj_lt_seg : j < seg.length := hlen ▸ hj_lt
      dsimp only [lookupL] at hj
      rw [listGet?_append_left seg ls_d' j hj_lt_seg] at hj
      have hget := frameEntriesRel_listGet? hEntries j
      cases hg1 : listGet? frame.entries j with
      | none =>
        cases hg2 : listGet? seg j with
        | none => rw [hg2] at hj; contradiction
        | some entry => rw [hg1, hg2] at hget; contradiction
      | some entry =>
        cases hg2 : listGet? seg j with
        | none => rw [hg1, hg2] at hget; contradiction
        | some entry' =>
          rcases entry with ⟨ts_e, b⟩
          rcases entry' with ⟨ts_s, J⟩
          rw [hg1, hg2] at hget
          rcases hget with ⟨rfl, hJ⟩
          rw [hg2] at hj
          dsimp only [lookupL, castListTy] at hj
          revert hj
          cases h_dec : listTyDecEq ts_e ts with
          | isTrue heq =>
            intro hj
            cases hj
            cases heq
            exact ⟨b, frame.vs, frame :: rest, rfl, hJ⟩
          | isFalse _ =>
            intro hj
            contradiction
    · simp only [hj_lt, ↓reduceIte]
      have hle_seg : seg.length ≤ j := by
        rw [← hlen]
        exact Nat.le_of_not_lt hj_lt
      dsimp only [lookupL] at hj
      rw [listGet?_append_right seg ls_d' j hle_seg] at hj
      rw [hlen]
      exact ih ts (j - seg.length) j' hj

theorem closed_of_mkJs (M : Module) (fuel : Nat) {rs : List Ty} (Γ : Env) (Q : Post rs) (X : XPost)
    (frame_ls : List (GroupFrame rs)) (vs : List ((t : Ty) × Val t))
    (ls_d' : List ((ts : List Ty) × Cont ts)) :
    {sig : List (List Ty)} → (bodies : TBlocks rs sig) →
    (hIH : ∀ {ts : List Ty} (b : TFlat rs) (xs : Tup Val ts) (m' : Mem 64),
      wp Γ Q X (denote Val Cont b (pushTup xs vs) ls_d') m' →
      ∀ f ≤ fuel, InterpOk Q X (interpFlat M f frame_ls (pushTup xs vs) b m')) →
    Closed Γ Q X
      (denoteB Val Cont bodies vs ls_d')
      (mkJs M fuel Q X bodies frame_ls vs)
  | [], .nil, _ => trivial
  | _ :: _, .cons b bs, hIH => by
    dsimp only [denoteB, Closed, mkJs]
    constructor
    · intro xs m' hwp f hf
      exact hIH b xs m' hwp f hf
    · exact closed_of_mkJs M fuel Γ Q X frame_ls vs ls_d' bs (fun b' xs m' hwp f hf => hIH b' xs m' hwp f hf)

/-- An environment `Γ` is sound with respect to module `M` if every function contract in `Γ` is
implemented by a function in `M` whose reified body satisfies `wp`. -/
def ModuleEnvSound (Γ : Env) (M : Module) : Prop :=
  ∀ (f : Sym) (as bs : List Ty) (xs : Tup Val as) (m : Mem 64) (P : Post bs) (E : XPost),
    Γ f as bs xs m P E →
    ∃ fnBody, lookupFn M f as bs = some fnBody ∧
      wp Γ P E (denote Val Cont (reifyFunc fnBody) (pushTup xs []) []) m

/-! ## Strong Induction and Main Soundness Theorems -/

theorem nat_strong_induction {P : Nat → Prop} (h : ∀ n, (∀ m < n, P m) → P n) (n : Nat) : P n := by
  have : ∀ m ≤ n, P m := by
    induction n with
    | zero =>
      intro m hm
      have hm0 : m = 0 := Nat.le_zero.mp hm
      subst hm0
      exact h 0 (fun k hk => (Nat.not_lt_zero k hk).elim)
    | succ n ih =>
      intro m hm
      cases Nat.lt_or_eq_of_le hm with
      | inl hlt => exact ih m (Nat.le_of_lt_succ hlt)
      | inr heq =>
        subst heq
        exact h (n + 1) (fun k hk => ih k (Nat.le_of_lt_succ hk))
  exact this n (Nat.le_refl n)

/-- Flat term soundness: evaluating a `TFlat` with sufficient fuel produces a result satisfying `InterpOk`. -/
theorem interpFlat_sound (M : Module) (Γ : Env) (hEnv : ModuleEnvSound Γ M) :
    (fuel : Nat) → ∀ {rs : List Ty} (Q : Post rs) (X : XPost)
      (ls_i : List (GroupFrame rs)) (ls_d : List ((ts : List Ty) × Cont ts))
      (vs : List ((t : Ty) × Val t)) (tf : TFlat rs) (m : Mem 64),
      FramesRel M fuel Q X ls_i ls_d →
      wp Γ Q X (denote Val Cont tf vs ls_d) m →
      InterpOk Q X (interpFlat M fuel ls_i vs tf m) := by
  intro fuel
  induction fuel using nat_strong_induction with
  | h fuel ih =>
    intro rs Q X ls_i ls_d vs tf m hrel hwp
    cases fuel with
    | zero =>
      dsimp only [interpFlat, InterpOk]
    | succ fuel =>
      have hle_fuel : fuel ≤ fuel + 1 := Nat.le_succ fuel
      have hrel_fuel : FramesRel M fuel Q X ls_i ls_d := framesRel_mono hle_fuel hrel
      have hlt_fuel : fuel < fuel + 1 := Nat.lt_succ_self fuel
      cases tf with
      | let_ op k =>
        dsimp only [denote] at hwp
        cases hargs : denoteArgs vs op.args with
        | none => rw [hargs] at hwp; exact False.elim hwp
        | some dargs =>
          rw [hargs] at hwp
          dsimp only [wp] at hwp
          have heval_args : evalArgs vs op.args = some (vals dargs) := evalArgs_of_denoteArgs hargs
          rcases OpCode.eval?_of_wp op.code (vals dargs) hwp with ⟨r, heval_op, hwp_k⟩
          have heval : evalOp vs op = some r := by
            dsimp only [evalOp]
            rw [heval_args]
            exact heval_op
          dsimp only [interpFlat]
          rw [heval]
          dsimp only
          exact ih fuel hlt_fuel Q X ls_i ls_d (pushTup r vs) k m hrel_fuel hwp_k
      | load t a k =>
        dsimp only [denote] at hwp
        cases ha : denoteArg vs a with
        | none => rw [ha] at hwp; exact False.elim hwp
        | some da =>
          rw [ha] at hwp
          dsimp only [wp] at hwp
          rcases hwp with ⟨v, hload, hwp_k⟩
          have heval_a : evalArg vs a = some da.val := evalArg_of_denoteArg ha
          dsimp only [interpFlat]
          rw [heval_a]
          dsimp only
          rw [hload]
          dsimp only
          exact ih fuel hlt_fuel Q X ls_i ls_d (⟨t, v⟩ :: vs) k m hrel_fuel hwp_k
      | store v a k =>
        dsimp only [denote] at hwp
        cases hv : denoteArg vs v with
        | none => rw [hv] at hwp; exact False.elim hwp
        | some dv =>
          cases ha : denoteArg vs a with
          | none => rw [hv, ha] at hwp; exact False.elim hwp
          | some da =>
            rw [hv, ha] at hwp
            dsimp only [wp] at hwp
            rcases hwp with ⟨⟨i, hload_int⟩, hwp_k⟩
            have heval_v : evalArg vs v = some dv.val := evalArg_of_denoteArg hv
            have heval_a : evalArg vs a = some da.val := evalArg_of_denoteArg ha
            dsimp only [interpFlat]
            rw [heval_v, heval_a]
            dsimp only
            rw [hload_int]
            dsimp only
            exact ih fuel hlt_fuel Q X ls_i ls_d vs k (storeMem m _ da.val dv.val) hrel_fuel hwp_k
      | call f bs args k =>
        dsimp only [denote] at hwp
        cases hargs : denoteArgs vs args with
        | none => rw [hargs] at hwp; exact False.elim hwp
        | some dargs =>
          rw [hargs] at hwp
          dsimp only [wp] at hwp
          rcases hwp with ⟨P, E, hΓ, hP, hE⟩
          have heval_args : evalArgs vs args = some (vals dargs) := evalArgs_of_denoteArgs hargs
          rcases hEnv f _ bs (vals dargs) m P E hΓ with ⟨calleeBody, hlook, hwp_callee⟩
          have hcall_sound := ih fuel hlt_fuel P E [] [] (pushTup (vals dargs) []) (reifyFunc calleeBody) m .nil hwp_callee
          dsimp only [interpFlat]
          rw [heval_args, hlook]
          dsimp only
          cases hres : interpFlat M fuel [] (pushTup (vals dargs) []) (reifyFunc calleeBody) m with
          | ok rets m' =>
            rw [hres] at hcall_sound
            dsimp only [InterpOk] at hcall_sound
            have hwp_k := hP rets m' hcall_sound
            dsimp only
            exact ih fuel hlt_fuel Q X ls_i ls_d (pushTup rets vs) k m' hrel_fuel hwp_k
          | outOfFuel =>
            dsimp only [InterpOk]
          | ub =>
            rw [hres] at hcall_sound
            exact False.elim hcall_sound
          | exit sym eargs m' =>
            rw [hres] at hcall_sound
            dsimp only [InterpOk] at hcall_sound
            dsimp only [InterpOk]
            exact hE sym _ eargs m' hcall_sound
      | jnz c t e =>
        dsimp only [denote] at hwp
        cases hc : denoteArg vs c with
        | none => rw [hc] at hwp; exact False.elim hwp
        | some dc =>
          rw [hc] at hwp
          dsimp only [wp] at hwp
          have heval_c : evalArg vs c = some dc.val := evalArg_of_denoteArg hc
          dsimp only [interpFlat]
          rw [heval_c]
          cases hval : dc.val with
          | true =>
            dsimp only
            exact ih fuel hlt_fuel Q X ls_i ls_d vs t m hrel_fuel (hwp.1 hval)
          | false =>
            dsimp only
            exact ih fuel hlt_fuel Q X ls_i ls_d vs e m hrel_fuel (hwp.2 hval)
      | jump j args =>
        dsimp only [denote] at hwp
        cases hj : lookupL ls_d _ j with
        | none => rw [hj] at hwp; exact False.elim hwp
        | some j' =>
          cases hargs : denoteArgs vs args with
          | none => rw [hj, hargs] at hwp; exact False.elim hwp
          | some dargs =>
            rw [hj, hargs] at hwp
            dsimp only [wp] at hwp
            have heval_args : evalArgs vs args = some (vals dargs) := evalArgs_of_denoteArgs hargs
            rcases framesRel_lookup hrel _ j j' hj with ⟨b, vs_tgt, ls_tgt, hlook, hcont⟩
            dsimp only [interpFlat]
            rw [heval_args, hlook]
            dsimp only
            cases hdec : listTyDecEq _ _ with
            | isTrue heq =>
              cases heq
              dsimp only
              exact hcont fuel hle_fuel (vals dargs) m hwp
            | isFalse hne =>
              contradiction
      | ret vs' =>
        dsimp only [denote] at hwp
        cases hvs' : denoteArgs vs vs' with
        | none => rw [hvs'] at hwp; exact False.elim hwp
        | some dargs =>
          rw [hvs'] at hwp
          dsimp only [wp] at hwp
          have heval_vs' : evalArgs vs vs' = some (vals dargs) := evalArgs_of_denoteArgs hvs'
          dsimp only [interpFlat]
          rw [heval_vs']
          dsimp only [InterpOk]
          exact hwp
      | exit f args =>
        dsimp only [denote] at hwp
        cases hargs : denoteArgs vs args with
        | none => rw [hargs] at hwp; exact False.elim hwp
        | some dargs =>
          rw [hargs] at hwp
          dsimp only [wp] at hwp
          have heval_args : evalArgs vs args = some (vals dargs) := evalArgs_of_denoteArgs hargs
          dsimp only [interpFlat]
          rw [heval_args]
          dsimp only [InterpOk]
          exact hwp
      | hlt =>
        exact False.elim hwp
      | group bodies k =>
        dsimp only [denote, wp] at hwp
        let frame := GroupFrame.ofTBlocks bodies vs
        let Js := mkJs M fuel Q X bodies (frame :: ls_i) vs
        have hrel_frame : FrameEntriesRel M fuel Q X (frame :: ls_i) vs
            (pushTBlocks bodies []) (pushTup Js []) :=
          frameEntriesRel_ofTBlocks M fuel Q X (frame :: ls_i) vs bodies
        have hrel' : FramesRel M fuel Q X (frame :: ls_i) (pushTup Js ls_d) := by
          rw [pushTup_append Js ls_d]
          exact .cons frame ls_i (pushTup Js []) ls_d hrel_frame hrel_fuel
        have hclosed : Closed Γ Q X (denoteB Val Cont bodies vs (pushTup Js ls_d)) Js := by
          apply closed_of_mkJs M fuel Γ Q X (frame :: ls_i) vs (pushTup Js ls_d) bodies
          intro ts b' xs' m' hwp_b f hf
          have hrel_f : FramesRel M f Q X (frame :: ls_i) (pushTup Js ls_d) :=
            framesRel_mono hf hrel'
          have hlt_f : f < fuel + 1 := Nat.lt_succ_of_le (Nat.le_trans hf (Nat.le_refl fuel))
          exact ih f hlt_f Q X (frame :: ls_i) (pushTup Js ls_d) (pushTup xs' vs) b' m' hrel_f hwp_b
        have hwp_k := hwp Js hclosed
        dsimp only [interpFlat]
        exact ih fuel hlt_fuel Q X (frame :: ls_i) (pushTup Js ls_d) vs k m hrel' hwp_k

/-- Soundness for `Func` execution: `Func.wp` implies `InterpOk`. -/
theorem interpFunc_sound (M : Module) (Γ : Env) (hEnv : ModuleEnvSound Γ M)
    {as rs : List Ty} (f : Func as rs) (args : Tup Val as) (m : Mem 64)
    (Q : Post rs) (X : XPost) (hf : f.Wf)
    (hwp : Func.wp Γ f args m Q X) (fuel : Nat) :
    InterpOk Q X (interpFunc M fuel f args m) := by
  have hrenorm := Func.renorm_spec hf hwp
  dsimp only [Func.wp, Func.renorm, denoteFunc] at hrenorm
  dsimp only [interpFunc]
  exact interpFlat_sound M Γ hEnv fuel Q X [] [] (pushTup args []) (reifyFunc f) m .nil hrenorm

/-- Soundness for `Fn` execution. -/
theorem interpFn_sound (M : Module) (Γ : Env) (hEnv : ModuleEnvSound Γ M)
    (fn : Fn) (args : Tup Val fn.as) (m : Mem 64)
    (Q : Post fn.rs) (X : XPost) (hfn : fn.Wf)
    (hwp : Func.wp Γ fn.body args m Q X) (fuel : Nat) :
    InterpOk Q X (interpFn M fuel fn args m) :=
  interpFunc_sound M Γ hEnv fn.body args m Q X hfn hwp fuel

/-- Soundness for whole-module entry point execution. -/
theorem interpModule_sound (M : Module) (Γ : Env) (hEnv : ModuleEnvSound Γ M)
    (entry : Sym) (as rs : List Ty) (args : Tup Val as) (m : Mem 64)
    (Q : Post rs) (X : XPost) (fnBody : Func as rs)
    (hlook : lookupFn M entry as rs = some fnBody)
    (hWf : fnBody.Wf) (hwp : Func.wp Γ fnBody args m Q X) (fuel : Nat) :
    InterpOk Q X (interpModule M fuel entry as rs args m) := by
  dsimp only [interpModule]
  rw [hlook]
  exact interpFunc_sound M Γ hEnv fnBody args m Q X hWf hwp fuel

/-- Soundness corollary: under `wp`, the interpreter NEVER produces undefined behavior (`.ub`). -/
theorem interpModule_not_ub (M : Module) (Γ : Env) (hEnv : ModuleEnvSound Γ M)
    (entry : Sym) (as rs : List Ty) (args : Tup Val as) (m : Mem 64)
    (Q : Post rs) (X : XPost) (fnBody : Func as rs)
    (hlook : lookupFn M entry as rs = some fnBody)
    (hWf : fnBody.Wf) (hwp : Func.wp Γ fnBody args m Q X) (fuel : Nat) :
    interpModule M fuel entry as rs args m ≠ .ub := by
  intro hub
  have hok := interpModule_sound M Γ hEnv entry as rs args m Q X fnBody hlook hWf hwp fuel
  rw [hub] at hok
  exact hok

/-- Soundness corollary: any terminating `.ok` result witnesses the concrete postcondition `Q`. -/
theorem interpModule_ok_witness (M : Module) (Γ : Env) (hEnv : ModuleEnvSound Γ M)
    (entry : Sym) (as rs : List Ty) (args : Tup Val as) (m : Mem 64)
    (Q : Post rs) (X : XPost) (fnBody : Func as rs)
    (hlook : lookupFn M entry as rs = some fnBody)
    (hWf : fnBody.Wf) (hwp : Func.wp Γ fnBody args m Q X) (fuel : Nat)
    (res : Tup Val rs) (m' : Mem 64)
    (hrun : interpModule M fuel entry as rs args m = .ok res m') :
    Q res m' := by
  have hok := interpModule_sound M Γ hEnv entry as rs args m Q X fnBody hlook hWf hwp fuel
  rw [hrun] at hok
  exact hok

/-! ## Module Environment Soundness Construction -/

theorem lookupFn_find?_eq : ∀ (fns : List Fn) (fn : Fn),
    (fns.map Fn.name).Nodup → fn ∈ fns →
    fns.find? (fun f => f.name == fn.name && Ty.listBeq f.as fn.as && Ty.listBeq f.rs fn.rs) = some fn
  | [], _, _, hmem => nomatch hmem
  | f :: rest, fn, hnd, hmem => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with rfl | hrest
    · dsimp only [List.find?]
      have h1 : (fn.name == fn.name) = true := beq_self_eq_true fn.name
      have h2 : Ty.listBeq fn.as fn.as = true := Ty.listBeq_iff_eq.2 rfl
      have h3 : Ty.listBeq fn.rs fn.rs = true := Ty.listBeq_iff_eq.2 rfl
      simp only [h1, h2, h3, Bool.and_self]
    · dsimp only [List.find?]
      cases hf : (f.name == fn.name && Ty.listBeq f.as fn.as && Ty.listBeq f.rs fn.rs) with
      | true =>
        simp only [Bool.and_eq_true, beq_iff_eq, Ty.listBeq_iff_eq] at hf
        rcases hf with ⟨⟨hf_name, _⟩, _⟩
        have hfn_name_mem : fn.name ∈ rest.map Fn.name := List.mem_map.2 ⟨fn, hrest, rfl⟩
        rw [← hf_name] at hfn_name_mem
        exact False.elim (hnd.1 hfn_name_mem)
      | false =>
        dsimp only
        exact lookupFn_find?_eq rest fn hnd.2 hrest

theorem lookupFn_of_mem {M : Module} (hnd : M.namesNodup) {fn : Fn} (hfn : fn ∈ M.fns) :
    lookupFn M fn.name fn.as fn.rs = some fn.body := by
  dsimp only [lookupFn]
  have hnd_fns : (M.fns.map Fn.name).Nodup := (List.nodup_append.mp hnd).1
  have hfind := lookupFn_find?_eq M.fns fn hnd_fns hfn
  rw [hfind]
  dsimp only
  cases listTyDecEq fn.as fn.as with
  | isTrue h1 =>
    cases listTyDecEq fn.rs fn.rs with
    | isTrue h2 => rfl
    | isFalse hne => exact False.elim (hne rfl)
  | isFalse hne => exact False.elim (hne rfl)

/-- A verified closed module (`ModuleOk Γ M`, `M.externs = []`) produces a sound environment
`ModuleEnvSound (Env.ofModule M Γ) M` for all internal calls. -/
theorem ModuleOk.env_sound {Γ : Env} {M : Module} (hM : ModuleOk Γ M) (hext : M.externs = []) :
    ModuleEnvSound (Env.ofModule M Γ) M := by
  intro f as bs xs m P E hspec
  dsimp only [Env.ofModule, Env.restrict] at hspec
  obtain ⟨hsig, hG⟩ := hspec
  simp only [Module.sigs, hext, List.map_nil, List.append_nil, List.mem_map] at hsig
  rcases hsig with ⟨fn, hfn_mem, hsig_eq⟩
  have hname : fn.name = f := congrArg (·.1) hsig_eq
  have has : fn.as = as := congrArg (·.2.1) hsig_eq
  have hrs : fn.rs = bs := congrArg (·.2.2) hsig_eq
  subst hname has hrs
  have hlook : lookupFn M fn.name fn.as fn.rs = some fn.body := lookupFn_of_mem hM.nodup hfn_mem
  have hM_mod := hM.ofModule
  rcases List.mem_iff_append.mp hfn_mem with ⟨pre, post, hsplit⟩
  have ⟨hwf, _, hwp⟩ := hM_mod.fnsOk pre fn post hsplit
  have hwp_spec := hwp xs m P E ⟨by simp [Module.sigs, hsplit, Fn.sig], hG⟩
  have hrenorm := Func.renorm_spec hwf hwp_spec
  dsimp only [Func.wp, Func.renorm, denoteFunc] at hrenorm
  exact ⟨fn.body, hlook, hrenorm⟩

end LeanQbe.T
