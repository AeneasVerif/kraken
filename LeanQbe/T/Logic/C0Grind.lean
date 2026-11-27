module

public import LeanQbe.T.Logic.Mem
public meta import Lean

/-!
# `C0Grind`: Spatial-Pruning `grind` & Pure-Kernel Bitfield Automation for C0 WP Proofs

Standalone leaf proof-automation kit unlocking Lean 4 `nightly-2026-11-08`'s built-in `grind`
(`hom := true`, `Init.Grind.Homo.*`, `List` `@[grind =]`) inside C0 weakest-precondition proofs
without exposing `grind`'s `initCore` to large `Mem 64` separation-logic chains or C0 AST terms:

1. **Curated `@[grind =]` / `[grind hom]` bridges**:
   * Non-looping `List.getD` read-over-write bridge (`list_getD_set`) compatible with `Init`'s
     `List.getD_eq_getElem?_getD`, `List.getElem?_set`, and `List.length_set`, plus convenience
     lemmas `list_getD_set_eq`, `list_getD_set_ne`, `list_getD_eq_getElem`,
     `list_getD_of_length_le`.
   * Missing `[grind hom]` rules `BitVec.ult_eq_decide` and `BitVec.ule_eq_decide` (complementing
     `Init.Grind.Homo.BitVec`'s `slt_eq_decide` / `sle_eq_decide`).
2. **`c0_grind` tactic** (`c0_grind`, `c0_grind [extra, ...]`, optional `grind` config flags):
   Prunes spatial `Mem 64` / `⋆` / `array` / `array64` / `bytes` / `region` / `cell` / `SepTree` /
   `SlabChain` hypotheses, `wp` / `Env` / `Expr` / C0 program terms, and unreferenced FVars while
   keeping all pure `Prop` hypotheses and the goal's dependency closure, then invokes `grind`
   (`hom := true`).
3. **`c0_bv_bit_grind` tactic** (`c0_bv_bit_grind`, `c0_bv_bit_grind [extra, ...]`):
   Runs the same spatial/AST context pruning, applies `BitVec.eq_of_getLsbD_eq`, projects pure
   `BitVec` equalities and upper bounds to `getLsbD`, decomposes closed bitmask literals (`≤ 64`
   bits) into linear `Nat` bit-range predicates via kernel `Eq.refl`, and closes via `grind` in
   strictly `std3` axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

set_option autoImplicit false

namespace LeanQbe.T.C0Grind

public section

/-! ## 1. Curated `List.getD` & `BitVec` `grind` Bridges -/

/-- Direct read-over-write rule for `List.getD` over `List.set`, strictly shrinking `List.set`
nesting without E-matching loops alongside `List.getD_eq_getElem?_getD` and `List.length_set`. -/
@[grind =] theorem list_getD_set {α : Type _} (xs : List α) (i j : Nat) (v d : α) :
    (xs.set i v).getD j d =
      if i = j then (if i < xs.length then v else d) else xs.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = j
  · simp only [h, ↓reduceIte]; by_cases hl : j < xs.length <;> simp [hl]
  · simp [h]

theorem list_getD_set_eq {α : Type _} {xs : List α} {i : Nat} {v d : α}
    (hi : i < xs.length) : (xs.set i v).getD i d = v := by
  rw [list_getD_set]; simp [hi]

theorem list_getD_set_ne {α : Type _} {xs : List α} {i j : Nat} {v d : α}
    (hne : i ≠ j) : (xs.set i v).getD j d = xs.getD j d := by
  rw [list_getD_set]; simp [hne]

theorem list_getD_eq_getElem {α : Type _} {xs : List α} {i : Nat} {d : α}
    (hi : i < xs.length) : xs.getD i d = xs[i]'hi := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem list_getD_of_length_le {α : Type _} {xs : List α} {i : Nat} {d : α}
    (hi : xs.length ≤ i) : xs.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

/- `Init.Grind.Homo.BitVec` registers `sle_eq_decide` / `slt_eq_decide` but omits `ule` / `ult`. -/
attribute [grind hom] BitVec.ult_eq_decide BitVec.ule_eq_decide

/-! ## 2. Pure-Kernel `getLsbD` Helpers for `c0_bv_bit_grind` -/

theorem bv_toNat_lt_of_lt {w : Nat} {x y : BitVec w} (h : x < y) : x.toNat < y.toNat :=
  BitVec.lt_def.mp h

theorem bv_toNat_le_of_le {w : Nat} {x y : BitVec w} (h : x ≤ y) : x.toNat ≤ y.toNat :=
  BitVec.le_def.mp h

theorem bv_toNat_lt_of_ult {w : Nat} {x y : BitVec w} (h : x.ult y = true) : x.toNat < y.toNat :=
  BitVec.ult_iff_toNat_lt.mp h

theorem bv_toNat_le_of_ule {w : Nat} {x y : BitVec w} (h : x.ule y = true) : x.toNat ≤ y.toNat :=
  BitVec.ule_iff_toNat_le.mp h

theorem bv_getLsbD_false_of_toNat_lt_two_pow {w k : Nat} {x : BitVec w}
    (hx : x.toNat < 2 ^ k) (j : Nat) (hj : k ≤ j) : x.getLsbD j = false := by
  rw [BitVec.getLsbD]
  exact Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 0 < 2) hj))

theorem bv_getLsbD_false_of_toNat_lt_ble {w B k : Nat} {x : BitVec w}
    (hx : x.toNat < B) (hble : Nat.ble B (2 ^ k) = true) (j : Nat) (hj : k ≤ j) :
    x.getLsbD j = false :=
  bv_getLsbD_false_of_toNat_lt_two_pow
    (Nat.lt_of_lt_of_le hx (Nat.le_of_ble_eq_true hble)) j hj

theorem bv_getLsbD_false_of_toNat_le_ble {w B k : Nat} {x : BitVec w}
    (hx : x.toNat ≤ B) (hble : Nat.ble (B + 1) (2 ^ k) = true) (j : Nat) (hj : k ≤ j) :
    x.getLsbD j = false :=
  bv_getLsbD_false_of_toNat_lt_two_pow
    (Nat.lt_of_le_of_lt hx (Nat.lt_of_succ_le (Nat.le_of_ble_eq_true hble))) j hj

theorem bv_getLsbD_false_of_toNat_le_two_pow_sub_one {w k : Nat} {x : BitVec w}
    (hx : x.toNat ≤ 2 ^ k - 1) (j : Nat) (hj : k ≤ j) : x.getLsbD j = false := by
  have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide : 0 < 2)
  exact bv_getLsbD_false_of_toNat_lt_two_pow (by omega) j hj

theorem bv_getLsbD_lit_zero {w : Nat} {x : BitVec w} (h : x = 0#w) (j : Nat) :
    x.getLsbD j = false := by rw [h, BitVec.getLsbD_zero]

theorem bv_getLsbD_lit_allOnes {w : Nat} {x : BitVec w} (h : x = BitVec.allOnes w) (j : Nat) :
    x.getLsbD j = decide (j < w) := by rw [h, BitVec.getLsbD_allOnes]

theorem bv_getLsbD_lit_bit {w k : Nat} {x : BitVec w}
    (h : x = BitVec.ofNat w (2 ^ k)) (hk : Nat.ble (k + 1) w = true) (j : Nat) :
    x.getLsbD j = decide (j = k) := by
  have hlt : k < w := Nat.lt_of_succ_le (Nat.le_of_ble_eq_true hk)
  rw [h, BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
  by_cases hjk : j = k
  · subst hjk; simp [hlt]
  · simp [hjk, Ne.symm hjk]

theorem bv_getLsbD_lit_low {w len : Nat} {x : BitVec w}
    (h : x = BitVec.ofNat w (2 ^ len - 1)) (hlen : Nat.ble len w = true) (j : Nat) :
    x.getLsbD j = decide (j < len) := by
  have hle : len ≤ w := Nat.le_of_ble_eq_true hlen
  rw [h, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < len
  · simp [hj, Nat.lt_of_lt_of_le hj hle]
  · simp [hj]

theorem bv_getLsbD_lit_range {w lo len : Nat} {x : BitVec w}
    (h : x = BitVec.ofNat w ((2 ^ len - 1) <<< lo)) (hlen : Nat.ble (lo + len) w = true)
    (j : Nat) : x.getLsbD j = decide (lo ≤ j ∧ j < lo + len) := by
  have hle : lo + len ≤ w := Nat.le_of_ble_eq_true hlen
  rw [h, BitVec.getLsbD_ofNat, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases hlo : lo ≤ j
  · by_cases hhi : j < lo + len
    · simp [hlo, hhi, Nat.lt_of_lt_of_le hhi hle, show j - lo < len by omega]
    · simp [hlo, hhi, show ¬ (j - lo < len) by omega]
  · simp [hlo]

theorem bv_getLsbD_lit_or {w a b : Nat} {x : BitVec w}
    (h : x = BitVec.ofNat w (a ||| b)) (j : Nat) :
    x.getLsbD j = ((BitVec.ofNat w a).getLsbD j || (BitVec.ofNat w b).getLsbD j) := by
  rw [h, BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat, Nat.testBit_or]
  by_cases hj : j < w <;> simp [hj]

/-! ## 3. Spatial & C0-AST Context Pruning -/

open Lean Meta Elab Tactic

private meta def isSpatialOrAstConst (nm : Name) : Bool :=
  match nm with
  | `Mem | `Std.ExtHashMap | `Std.ExtHashMap.sep | `Std.ExtHashMap.emp
  | `Std.ExtHashMap.union | `Std.ExtHashMap.inter | `List.At
  | `LeanQbe.T.cell | `LeanQbe.T.cell64 | `LeanQbe.T.array | `LeanQbe.T.array64
  | `LeanQbe.T.bytes | `LeanQbe.T.region
  | `LeanQbe.T.loadVal | `LeanQbe.T.storeMem | `LeanQbe.T.storeOk
  | `LeanQbe.T.wp | `LeanQbe.T.Func.wp | `LeanQbe.T.Func.spec | `LeanQbe.T.Closed
  | `LeanQbe.T.Op.wp | `LeanQbe.T.Op | `LeanQbe.T.Expr | `LeanQbe.T.Blocks
  | `LeanQbe.T.Func | `LeanQbe.T.Fn | `LeanQbe.T.Module | `LeanQbe.T.Env
  | `LeanQbe.T.Env.ofTable | `LeanQbe.T.Env.Has | `LeanQbe.T.Env.Sat
  | `LeanQbe.T.SegCert | `LeanQbe.T.Spec | `LeanQbe.T.Post | `LeanQbe.T.XPost
  | `LeanQbe.T.Cont | `LeanQbe.T.TableImpl | `LeanQbe.T.SpecEntry
  | `LeanQbe.T.SpecEntry.Impl => true
  | _ =>
    (`LeanQbe.T.SepTree).isPrefixOf nm || (`LeanQbe.T.SlabChain).isPrefixOf nm ||
    (`LeanQbe.T.SlabSeg).isPrefixOf nm || (`LeanQbe.T.Frontend.C0).isPrefixOf nm

private meta def exprHasHeavy (heavy : FVarIdSet) (e : Lean.Expr) : Bool :=
  (e.find? fun
    | .const nm _ => isSpatialOrAstConst nm
    | .fvar fid => heavy.contains fid
    | _ => false).isSome

private meta def isHeavyDecl (heavy : FVarIdSet) (decl : LocalDecl) : MetaM Bool := do
  let ty ← instantiateMVars decl.type
  if exprHasHeavy heavy ty then return true
  if exprHasHeavy heavy (← whnfR ty) then return true
  if decl.isLet then
    return exprHasHeavy heavy (← instantiateMVars decl.value)
  return false

private meta partial def collectFVars (e : Lean.Expr) (acc : FVarIdSet) : FVarIdSet :=
  if !e.hasFVar then acc else
  match e with
  | .fvar fid => acc.insert fid
  | .app f a => collectFVars a (collectFVars f acc)
  | .lam _ t b _ | .forallE _ t b _ => collectFVars b (collectFVars t acc)
  | .letE _ t v b _ => collectFVars b (collectFVars v (collectFVars t acc))
  | .mdata _ b | .proj _ _ b => collectFVars b acc
  | _ => acc

private meta partial def collectSyntaxIdents (stx : Syntax) (acc : NameSet) : NameSet :=
  match stx with
  | .ident _ _ val _ => acc.insert val
  | .node _ _ args => args.foldl (fun s a => collectSyntaxIdents a s) acc
  | _ => acc

private meta def depClosure (lctx : LocalContext) (seeds : FVarIdSet) : FVarIdSet := Id.run do
  let mut closed := seeds
  let mut stack := seeds.toArray
  while !stack.isEmpty do
    let some fid := stack.back? | break
    stack := stack.pop
    if let some d := lctx.find? fid then
      for f in collectFVars d.type (if d.isLet then collectFVars d.value {} else {}) do
        if !closed.contains f then
          closed := closed.insert f; stack := stack.push f
  return closed

/-- Prune spatial `Mem 64` / `⋆` / `SepTree` / `SlabChain`, `wp` / `Env` / `Expr` / C0 AST, and
unreferenced local declarations while keeping all pure `Prop` hypotheses and dependencies. -/
private meta def pruneC0Goal (mvar : MVarId) (paramStxs : Array Syntax) : MetaM MVarId :=
  mvar.withContext do
    let lctx ← getLCtx
    let mut heavy : FVarIdSet := {}
    for d in lctx do
      if !d.isImplementationDetail then
        if ← isHeavyDecl heavy d then
          heavy := heavy.insert d.fvarId
    let pNames := paramStxs.foldl (fun s stx => collectSyntaxIdents stx s) {}
    let mut seeds := collectFVars (← instantiateMVars (← mvar.getType)) {}
    for d in lctx do
      if !d.isImplementationDetail && !heavy.contains d.fvarId then
        if (← isProp d.type) || d.binderInfo == .instImplicit || pNames.contains d.userName then
          seeds := seeds.insert d.fvarId
    let keep := depClosure lctx seeds
    let mut toClear : Array FVarId := #[]
    for d in lctx do
      if !d.isImplementationDetail && !keep.contains d.fvarId then
        toClear := toClear.push d.fvarId
    if toClear.isEmpty then return mvar else mvar.tryClearMany toClear

/-! ## 4. Bitmask Literal `getLsbD` Decomposition & Bound Projection -/

private meta partial def evalClosedBvLit? (e : Lean.Expr) : MetaM (Option (Nat × Nat)) := do
  let e := e.consumeMData
  if e.isAppOfArity ``BitVec.ofNat 2 then
    let some w ← Meta.getNatValue? (e.getArg! 0) | return none
    let some n ← Meta.getNatValue? (e.getArg! 1) | return none
    return some (w, n % 2 ^ w)
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let ty ← whnfR (e.getArg! 0)
    if ty.isAppOfArity ``BitVec 1 then
      let some w ← Meta.getNatValue? ty.appArg! | return none
      let some n ← Meta.getNatValue? (e.getArg! 1) | return none
      return some (w, n % 2 ^ w)
  if e.isAppOfArity ``BitVec.allOnes 1 then
    let some w ← Meta.getNatValue? e.appArg! | return none
    return some (w, 2 ^ w - 1)
  if e.isAppOfArity ``Complement.complement 3 then
    let some (w, v) ← evalClosedBvLit? (e.getArg! 2) | return none
    return some (w, (2 ^ w - 1) - v)
  let evalBin (op : Nat → Nat → Nat) : MetaM (Option (Nat × Nat)) := do
    let some (w1, v1) ← evalClosedBvLit? (e.getArg! 4) | return none
    let some (w2, v2) ← evalClosedBvLit? (e.getArg! 5) | return none
    return if w1 == w2 then some (w1, op v1 v2) else none
  if e.isAppOfArity ``HAnd.hAnd 6 then return ← evalBin (· &&& ·)
  if e.isAppOfArity ``HOr.hOr 6 then return ← evalBin (· ||| ·)
  if e.isAppOfArity ``HXor.hXor 6 then return ← evalBin (· ^^^ ·)
  if e.isAppOfArity ``HShiftLeft.hShiftLeft 6 || e.isAppOfArity ``HShiftRight.hShiftRight 6 then
    let some (w, v) ← evalClosedBvLit? (e.getArg! 4) | return none
    let k? ← match ← Meta.getNatValue? (e.getArg! 5) with
      | some k => pure (some k)
      | none => pure ((← evalClosedBvLit? (e.getArg! 5)).map (·.2))
    let some k := k? | return none
    let res := if e.isAppOfArity ``HShiftLeft.hShiftLeft 6 then (v <<< k) % 2 ^ w else v >>> k
    return some (w, res)
  let e' ← whnfR e
  if e' != e then evalClosedBvLit? e' else return none

private meta def bitRuns (w v : Nat) : List (Nat × Nat) := Id.run do
  let mut runs : List (Nat × Nat) := []
  let mut i : Nat := 0
  while i < w do
    if v.testBit i then
      let lo := i
      while i < w && v.testBit i do i := i + 1
      runs := runs ++ [(lo, i - lo)]
    else i := i + 1
  return runs

/-- Kernel-sound pre-simproc decomposing closed `BitVec w` (`w ≤ 64`) mask `getLsbD` terms into
linear `Nat` bit-range predicates via `Eq.refl`. -/
simproc ↑ bvLitGetLsbDSimproc (BitVec.getLsbD _ _) := fun e => do
  if e.hasLooseBVars || !e.isAppOfArity ``BitVec.getLsbD 3 then return .continue
  let (wE, xE, jE) := (e.getArg! 0, e.getArg! 1, e.getArg! 2)
  let some w ← Meta.getNatValue? wE | return .continue
  unless w ≤ 64 do return .continue
  let some (wx, v) ← evalClosedBvLit? xE | return .continue
  unless wx == w do return .continue
  let runs := bitRuns w v
  let tRefl := mkEqRefl (mkConst ``Bool.true)
  match runs with
  | [] =>
    unless ← withDefault (isDefEq xE (mkApp2 (mkConst ``BitVec.ofNat) wE (mkNatLit 0))) do
      return .continue
    let prf := mkApp4 (mkConst ``bv_getLsbD_lit_zero) wE xE (← mkEqRefl xE) jE
    return .done { expr := mkConst ``Bool.false, proof? := some prf }
  | [(0, len)] =>
    if len == w then
      unless ← withDefault (isDefEq xE (mkApp (mkConst ``BitVec.allOnes) wE)) do return .continue
      let rhs ← mkDecide (← mkAppM ``LT.lt #[jE, wE])
      let prf := mkApp4 (mkConst ``bv_getLsbD_lit_allOnes) wE xE (← mkEqRefl xE) jE
      return .done { expr := rhs, proof? := some prf }
    let lenE := mkNatLit len
    unless ← withDefault (isDefEq xE (mkApp2 (mkConst ``BitVec.ofNat) wE (mkNatLit (2 ^ len - 1))))
      do return .continue
    let rhs ← mkDecide (← mkAppM ``LT.lt #[jE, lenE])
    let prf := mkAppN (mkConst ``bv_getLsbD_lit_low) #[wE, lenE, xE, ← mkEqRefl xE, ← tRefl, jE]
    return .done { expr := rhs, proof? := some prf }
  | [(k, 1)] =>
    let kE := mkNatLit k
    unless ← withDefault (isDefEq xE (mkApp2 (mkConst ``BitVec.ofNat) wE (mkNatLit (2 ^ k)))) do
      return .continue
    let rhs ← mkDecide (← mkEq jE kE)
    let prf := mkAppN (mkConst ``bv_getLsbD_lit_bit) #[wE, kE, xE, ← mkEqRefl xE, ← tRefl, jE]
    return .done { expr := rhs, proof? := some prf }
  | [(lo, len)] =>
    let (loE, lenE) := (mkNatLit lo, mkNatLit len)
    unless ← withDefault (isDefEq xE
        (mkApp2 (mkConst ``BitVec.ofNat) wE (mkNatLit ((2 ^ len - 1) <<< lo)))) do
      return .continue
    let hiE ← mkAppM ``HAdd.hAdd #[loE, lenE]
    let prop ← mkAppM ``And #[← mkAppM ``LE.le #[loE, jE], ← mkAppM ``LT.lt #[jE, hiE]]
    let rhs ← mkDecide prop
    let prf := mkAppN (mkConst ``bv_getLsbD_lit_range)
      #[wE, loE, lenE, xE, ← mkEqRefl xE, ← tRefl, jE]
    return .done { expr := rhs, proof? := some prf }
  | (lo, len) :: _ =>
    if runs.length > 16 then return .continue
    let headVal := (2 ^ len - 1) <<< lo
    let tailVal := v ^^^ headVal
    let (aNat, bNat) := (mkNatLit headVal, mkNatLit tailVal)
    let aE := mkApp2 (mkConst ``BitVec.ofNat) wE aNat
    let bE := mkApp2 (mkConst ``BitVec.ofNat) wE bNat
    let targetBv := mkApp2 (mkConst ``BitVec.ofNat) wE (← mkAppM ``HOr.hOr #[aNat, bNat])
    unless ← withDefault (isDefEq xE targetBv) do return .continue
    let rhs := mkApp2 (mkConst ``Bool.or)
      (mkApp3 (mkConst ``BitVec.getLsbD) wE aE jE) (mkApp3 (mkConst ``BitVec.getLsbD) wE bE jE)
    let prf := mkAppN (mkConst ``bv_getLsbD_lit_or) #[wE, aNat, bNat, xE, ← mkEqRefl xE, jE]
    return .visit { expr := rhs, proof? := some prf }

private meta def extractTwoPowExp? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let e := e.consumeMData
  if e.isAppOfArity ``HPow.hPow 6 then
    if (← Meta.getNatValue? (e.getArg! 4)) == some 2 then
      return some (e.getArg! 5)
  return none

private meta def evalNatOrBvToNat? (e : Lean.Expr) : MetaM (Option Nat) := do
  if let some n ← Meta.getNatValue? e then return some n
  let e := e.consumeMData
  if e.isAppOfArity ``BitVec.toNat 2 then
    return (← evalClosedBvLit? (e.getArg! 1)).map (·.2)
  return none

private meta def tryExtractToNatBound (hExpr ty : Lean.Expr) :
    MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  let ty := ty.consumeMData
  let mkBnd (isLt : Bool) (lhs rhs hPrf : Lean.Expr) :
      MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr)) := do
    let lhs := lhs.consumeMData
    unless lhs.isAppOfArity ``BitVec.toNat 2 do return none
    let (wE, xE) := (lhs.getArg! 0, lhs.getArg! 1)
    if isLt then
      if let some kE ← extractTwoPowExp? rhs then
        return some (xE, kE, mkApp4 (mkConst ``bv_getLsbD_false_of_toNat_lt_two_pow) wE kE xE hPrf)
      if let some b ← evalNatOrBvToNat? rhs then
        if 0 < b && b ≤ 2 ^ 64 then
          let kE := mkNatLit (if b ≤ 1 then 0 else Nat.log2 (b - 1) + 1)
          return some (xE, kE, mkAppN (mkConst ``bv_getLsbD_false_of_toNat_lt_ble)
            #[wE, rhs, kE, xE, hPrf, ← mkEqRefl (mkConst ``Bool.true)])
    else
      let rhsC := rhs.consumeMData
      if rhsC.isAppOfArity ``HSub.hSub 6 then
        if (← Meta.getNatValue? (rhsC.getArg! 5)) == some 1 then
          if let some kE ← extractTwoPowExp? (rhsC.getArg! 4) then
            return some (xE, kE,
              mkApp4 (mkConst ``bv_getLsbD_false_of_toNat_le_two_pow_sub_one) wE kE xE hPrf)
      if let some b ← evalNatOrBvToNat? rhs then
        if b < 2 ^ 64 then
          let kE := mkNatLit (if b == 0 then 0 else Nat.log2 b + 1)
          return some (xE, kE, mkAppN (mkConst ``bv_getLsbD_false_of_toNat_le_ble)
            #[wE, rhs, kE, xE, hPrf, ← mkEqRefl (mkConst ``Bool.true)])
    return none
  let bvCmp (isLt : Bool) (fn : Name) (a b : Lean.Expr) := do
    mkBnd isLt (← mkAppM ``BitVec.toNat #[a]) (← mkAppM ``BitVec.toNat #[b])
      (← mkAppM fn #[hExpr])
  if ty.isAppOfArity ``LT.lt 4 then
    let α := ty.getArg! 0
    if α.isConstOf ``Nat then return ← mkBnd true (ty.getArg! 2) (ty.getArg! 3) hExpr
    if (← whnfR α).isAppOfArity ``BitVec 1 then
      return ← bvCmp true ``bv_toNat_lt_of_lt (ty.getArg! 2) (ty.getArg! 3)
  if ty.isAppOfArity ``GT.gt 4 && (ty.getArg! 0).isConstOf ``Nat then
    return ← mkBnd true (ty.getArg! 3) (ty.getArg! 2) hExpr
  if ty.isAppOfArity ``LE.le 4 then
    let α := ty.getArg! 0
    if α.isConstOf ``Nat then return ← mkBnd false (ty.getArg! 2) (ty.getArg! 3) hExpr
    if (← whnfR α).isAppOfArity ``BitVec 1 then
      return ← bvCmp false ``bv_toNat_le_of_le (ty.getArg! 2) (ty.getArg! 3)
  if ty.isAppOfArity ``GE.ge 4 && (ty.getArg! 0).isConstOf ``Nat then
    return ← mkBnd false (ty.getArg! 3) (ty.getArg! 2) hExpr
  if let some (_, lhs, rhs) := ty.eq? then
    if rhs.consumeMData.isConstOf ``Bool.true then
      let lhs := lhs.consumeMData
      if lhs.isAppOfArity ``BitVec.ult 3 then
        return ← bvCmp true ``bv_toNat_lt_of_ult (lhs.getArg! 1) (lhs.getArg! 2)
      if lhs.isAppOfArity ``BitVec.ule 3 then
        return ← bvCmp false ``bv_toNat_le_of_ule (lhs.getArg! 1) (lhs.getArg! 2)
  return none

private meta def injectBitHyps (mvar : MVarId) : MetaM (MVarId × Array FVarId) :=
  mvar.withContext do
    let decls := (← getLCtx).decls.toArray.filterMap id
    let mut cur := mvar
    let mut eqHyps : Array FVarId := #[]
    let mut seenBnd : Std.HashSet (Lean.Expr × Lean.Expr) := {}
    let mut idx : Nat := 0
    for d in decls do
      if d.isImplementationDetail then continue
      let ty ← cur.withContext do instantiateMVars d.type
      let mut handled := false
      if let some (α, lhs, rhs) := ty.eq? then
        let αR ← cur.withContext do whnfR α
        if αR.isAppOfArity ``BitVec 1 && !(lhs.isFVar && rhs.isFVar) && lhs != rhs then
          let wE := αR.appArg!
          let bitEqTy ← cur.withContext do
            withLocalDeclD `_j (mkConst ``Nat) fun j => do
              mkForallFVars #[j] (← mkEq (mkApp3 (mkConst ``BitVec.getLsbD) wE lhs j)
                (mkApp3 (mkConst ``BitVec.getLsbD) wE rhs j))
          let bitEqPrf ← cur.withContext do
            withLocalDeclD `_j (mkConst ``Nat) fun j => do
              let f ← withLocalDeclD `_z α fun z =>
                mkLambdaFVars #[z] (mkApp3 (mkConst ``BitVec.getLsbD) wE z j)
              mkLambdaFVars #[j] (← mkCongrArg f d.toExpr)
          cur ← cur.assert (Name.mkSimple s!"_c0_bit_eq_{idx}") bitEqTy bitEqPrf
          let (fid, cur') ← cur.intro1P
          cur := cur'; eqHyps := eqHyps.push fid; idx := idx + 1; handled := true
      if !handled then
        if let some (xE, kE, prf) ← cur.withContext (tryExtractToNatBound d.toExpr ty) then
          if !seenBnd.contains (xE, kE) then
            seenBnd := seenBnd.insert (xE, kE)
            cur ← cur.assert (Name.mkSimple s!"_c0_bit_bnd_{idx}")
              (← cur.withContext (inferType prf)) prf
            let (_, cur') ← cur.intro1P
            cur := cur'; idx := idx + 1
    return (cur, eqHyps)

private meta def bitGetLsbDConstNames : Array Name := #[
  ``BitVec.getLsbD_and, ``BitVec.getLsbD_or, ``BitVec.getLsbD_xor, ``BitVec.getLsbD_not,
  ``BitVec.getLsbD_shiftLeft, ``BitVec.getLsbD_ushiftRight,
  ``BitVec.shiftLeft_eq', ``BitVec.ushiftRight_eq',
  ``BitVec.getLsbD_setWidth, ``BitVec.getLsbD_setWidth',
  ``BitVec.getLsbD_signExtend, ``BitVec.getLsbD_extractLsb',
  ``BitVec.getLsbD_zero, ``BitVec.getLsbD_one, ``BitVec.getLsbD_allOnes, ``BitVec.getLsbD_ofNat,
  ``Nat.testBit_and, ``Nat.testBit_or, ``Nat.testBit_xor,
  ``Nat.testBit_shiftLeft, ``Nat.testBit_shiftRight,
  ``Nat.testBit_two_pow_sub_one, ``Nat.testBit_mod_two_pow, ``Nat.testBit_two_pow,
  ``Nat.zero_testBit,
  ``UInt8.toBitVec_and, ``UInt8.toBitVec_or, ``UInt8.toBitVec_xor, ``UInt8.toBitVec_not,
  ``UInt8.toBitVec_shiftLeft, ``UInt8.toBitVec_shiftRight,
  ``UInt32.toBitVec_and, ``UInt32.toBitVec_or, ``UInt32.toBitVec_xor, ``UInt32.toBitVec_not,
  ``UInt32.toBitVec_shiftLeft, ``UInt32.toBitVec_shiftRight,
  ``UInt64.toBitVec_and, ``UInt64.toBitVec_or, ``UInt64.toBitVec_xor, ``UInt64.toBitVec_not,
  ``UInt64.toBitVec_shiftLeft, ``UInt64.toBitVec_shiftRight
]

private meta def runBitGetLsbDSimp (mvar : MVarId) (hyps : Array FVarId) :
    MetaM (Option MVarId) :=
  mvar.withContext do
    let mut thms : SimpTheorems := {}
    for c in bitGetLsbDConstNames do thms ← thms.addConst c
    let simprocs ← ({} : Simp.Simprocs).add ``bvLitGetLsbDSimproc false
    let ctx ← Simp.mkContext
      (config := { failIfUnchanged := false, zeta := true, zetaDelta := true, maxSteps := 100000 })
      (simpTheorems := #[thms])
    let (res?, _) ← simpGoal mvar ctx #[simprocs] (simplifyTarget := true) (fvarIdsToSimp := hyps)
    return res?.map (·.2)

/-! ## 5. `c0_grind` and `c0_bv_bit_grind` Tactics -/

/-- Spatial-pruning `grind` for C0 WP proofs: clears `Mem 64` / `⋆` / `SepTree` / `SlabChain` /
`wp` / `Env` / `Expr` / C0 AST hypotheses and unreferenced FVars while keeping all pure `Prop`
hypotheses, then invokes `grind` with `hom := true`. -/
syntax (name := c0Grind) "c0_grind" Parser.Tactic.optConfig
  (" [" withoutPosition(Parser.Tactic.grindParam,*) "]")? : tactic

/-- Bit-extensional spatial-pruning `grind` for packed-word, clause-header, and ModRM/SIB/REX
bitfield equalities (`std3` axioms only). Prunes spatial/AST context, applies
`BitVec.eq_of_getLsbD_eq`, projects bit bounds and concrete bitmasks, and closes via `grind`. -/
syntax (name := c0BvBitGrind) "c0_bv_bit_grind" Parser.Tactic.optConfig
  (" [" withoutPosition(Parser.Tactic.grindParam,*) "]")? : tactic

private meta def runGrindOnMain (ref : Syntax) (configStx : TSyntax ``Parser.Tactic.optConfig)
    (params? : Option (Syntax.TSepArray ``Parser.Tactic.grindParam ",")) : TacticM Unit := do
  let config ← elabGrindConfig configStx
  evalGrindCore ref { config with hom := true } none params? none (identity := `c0_grind)

elab_rules : tactic
  | `(tactic| c0_grind $configStx:optConfig $[ [ $params?:grindParam,* ] ]?) => do
    let paramRaw := params?.map (·.getElems.map (·.raw)) |>.getD #[]
    let g' ← pruneC0Goal (← getMainGoal) paramRaw
    replaceMainGoal [g']
    runGrindOnMain (← getRef) configStx params?

private meta def isBitEqConclusion (ty : Lean.Expr) : MetaM Bool :=
  forallTelescopeReducing ty fun _ body => do
    let some (α, _, _) := body.eq? | return false
    let αR ← whnfR α
    return αR.isAppOfArity ``BitVec 1 || αR.isConstOf ``UInt8 ||
      αR.isConstOf ``UInt16 || αR.isConstOf ``UInt32 || αR.isConstOf ``UInt64

elab_rules : tactic
  | `(tactic| c0_bv_bit_grind $configStx:optConfig $[ [ $params?:grindParam,* ] ]?) => do
    let paramRaw := params?.map (·.getElems.map (·.raw)) |>.getD #[]
    let mut g ← getMainGoal
    let tgt0 ← g.withContext do instantiateMVars (← g.getType)
    if (← g.withContext (whnfR tgt0)).isForall then
      if ← g.withContext (isBitEqConclusion tgt0) then
        g := (← g.intros).2
    g ← pruneC0Goal g paramRaw
    if let some (α, _, _) := (← g.withContext (instantiateMVars (← g.getType))).eq? then
      let αR ← g.withContext do whnfR α
      let uintEq? :=
        if αR.isConstOf ``UInt8 then some ``UInt8.eq_of_toBitVec_eq
        else if αR.isConstOf ``UInt16 then some ``UInt16.eq_of_toBitVec_eq
        else if αR.isConstOf ``UInt32 then some ``UInt32.eq_of_toBitVec_eq
        else if αR.isConstOf ``UInt64 then some ``UInt64.eq_of_toBitVec_eq
        else none
      if let some uEq := uintEq? then
        if let [g1] ← g.apply (mkConst uEq) then g := g1
    if let some (α, _, _) := (← g.withContext (instantiateMVars (← g.getType))).eq? then
      if (← g.withContext (whnfR α)).isAppOfArity ``BitVec 1 then
        let [gExt] ← g.apply (mkConst ``BitVec.eq_of_getLsbD_eq)
          | throwError "c0_bv_bit_grind: failed to apply BitVec.eq_of_getLsbD_eq"
        let (_, g1) ← gExt.intro1P
        let (_, g2) ← g1.intro1P
        let (g3, eqHyps) ← injectBitHyps g2
        match ← runBitGetLsbDSimp g3 eqHyps with
        | none => replaceMainGoal []; return
        | some g4 =>
          replaceMainGoal [g4]
          runGrindOnMain (← getRef) configStx params?
          return
    replaceMainGoal [g]
    runGrindOnMain (← getRef) configStx params?

end

end LeanQbe.T.C0Grind
