module

public import LeanQbe.T.Examples.Kissat.FullPropDecLemmas3
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` `full_prop_lit` `Func.wp` Proof (`Stage 4`, Part 4)

Provides:
1. Local O(1) head-only stepper (`fp_head_steps`) specialized for `FullMem` / `FullCfg`.
2. Parametric `(Γ : Env)` `Func.wp` proof for `full_prop_lit` (`full_prop_lit_wp`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
  LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test
open scoped FullArenaTactics FullPropDecTactics
open FullPropDecSpecs

/-! ## 1. Local O(1) head-only stepper (`fp_head_steps`) for `FullMem` -/

private theorem wp_head_eq {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {e1 e2 : Expr Val Cont rs} (h : e1 = e2) (hk : wp Γ Q X e2 m) :
    wp Γ Q X e1 m := h ▸ hk

private theorem wp_let_head {Γ : Env} {rs sig ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : OpCode sig ts} {args : Tup (Arg Val) sig} {k : Tup Val ts → Expr Val Cont rs}
    {r : Tup Val ts} (hr : ∀ P, P r → c.wp (vals args) P) (hk : wp Γ Q X (k r) m) :
    wp Γ Q X (.let_ (Op.mk c args) k) m := hr _ hk

private theorem wp_blocks_here {Γ : Env} {rs ts : List Ty} {sig : List (List Ty)}
    {Q : Post rs} {X : XPost} {m : Mem 64}
    {b : Tup Val ts → Expr Val Cont rs} {bs : Blocks Val Cont rs sig} {xs : Tup Val ts}
    (h : wp Γ Q X (b xs) m) :
    wp Γ Q X (Blocks.get (Blocks.cons b bs) .here xs) m := h

private theorem wp_ret_head {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {xs : Tup (Arg Val) rs} (h : Q (vals xs) m) : wp Γ Q X (.ret xs) m := h

private theorem wp_jump_head {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {J : Cont ts} {xs : Tup (Arg Val) ts} (h : J (vals xs) m) : wp Γ Q X (.jump J xs) m := h

section FastLet
variable {Γ : Env} {rs : List Ty} {n : Nat} {Q : Post rs} {X : XPost} {m : Mem 64}
private theorem wp_let_add_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va + vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.add (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_sub_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va - vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sub (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_mul_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va * vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.mul (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_and_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va &&& vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.and (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_or_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va ||| vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.or (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_xor_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va ^^^ vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.xor (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_eq_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va == vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq (.bits n)) (a, b, ())) k) m := by
  cases ha; cases hb
  simpa only [wp, Op.wp, OpCode.wp, vals, liftCmp, evalBits_eq_beq, Ty.hasFloat,
    Bool.false_eq_true, ite_false] using hk
private theorem wp_let_ne_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va != vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ne (.bits n)) (a, b, ())) k) m := by
  cases ha; cases hb
  simpa only [wp, Op.wp, OpCode.wp, vals, liftCmp, evalBits_ne_bne, Ty.hasFloat,
    Bool.false_eq_true, ite_false] using hk
private theorem wp_let_ult_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va.ult vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_ule_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va.ule vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ule (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_ugt_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (vb.ult va, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ugt (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_uge_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (vb.ule va, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .uge (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_slt_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va.slt vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .slt (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_sle_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (va.sle vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .sle (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_sgt_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (vb.slt va, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .sgt (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_sge_b {a b : Arg Val (.bits n)} {va vb : BitVec n} {k} (ha : a.val = va)
    (hb : b.val = vb) (hk : wp Γ Q X (k (vb.sle va, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .sge (.bits n)) (a, b, ())) k) m := by cases ha; cases hb; exact hk
private theorem wp_let_zext32_64 {a : Arg Val i32} {va : BitVec 32} {k} (ha : a.val = va)
    (hk : wp Γ Q X (k (va.setWidth 64, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.zext 32 64) (a, ())) k) m := by cases ha; exact ⟨by decide, hk⟩
private theorem wp_let_sext8_32 {a : Arg Val i8} {va : BitVec 8} {k} (ha : a.val = va)
    (hk : wp Γ Q X (k (va.signExtend 32, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext 8 32) (a, ())) k) m := by cases ha; exact ⟨by decide, hk⟩
private theorem wp_let_trunc64_32 {a : Arg Val i64} {va : BitVec 64} {k} (ha : a.val = va)
    (hk : wp Γ Q X (k (va.setWidth 32, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.trunc 64 32) (a, ())) k) m := by cases ha; exact ⟨by decide, hk⟩
private theorem wp_let_shl64_1 {a b : Arg Val i64} {va : BitVec 64} {k} (ha : a.val = va)
    (hb : b.val = 1#64) (hk : wp Γ Q X (k (va <<< (1 : Nat), ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shl i64) (a, b, ())) k) m := by
  cases ha
  simpa only [wp, Op.wp, OpCode.wp, vals, lift2, hb, BitVec.reduceToNat, Nat.reduceMod,
    Ty.hasFloat, Bool.false_eq_true, ite_false] using hk
private theorem wp_let_lshr32_1 {a b : Arg Val i32} {va : BitVec 32} {k} (ha : a.val = va)
    (hb : b.val = 1#32) (hk : wp Γ Q X (k (va >>> (1 : Nat), ())) m) :
    wp Γ Q X (.let_ (Op.mk (.lshr i32) (a, b, ())) k) m := by
  cases ha
  simpa only [wp, Op.wp, OpCode.wp, vals, lift2, hb, BitVec.reduceToNat, Nat.reduceMod,
    Ty.hasFloat, Bool.false_eq_true, ite_false] using hk
end FastLet

local macro "fp_head_let" : tactic =>
  `(tactic| (
    apply wp_let_head
    · intro P hP; try dsimp (config := { zeta := false }) only
      simp only [OpCode.wp, OpCode.wp_cmp, OpCode.wp_select, OpCode.eq, OpCode.ne, OpCode.ult,
        OpCode.ule, OpCode.ugt, OpCode.uge, OpCode.slt, OpCode.sle, OpCode.sgt, OpCode.sge,
        vals_nil, vals_cons, Arg.val_var, Arg.val_imm, Ty.hasFloat_vec, Ty.hasFloat, Ty.isFloatTree,
        evalBits_eq_beq, evalBits_ne_bne, evalBits_ult_eq, evalBits_ule_eq, evalBits_ugt_eq,
        evalBits_uge_eq, evalBits_slt_eq, evalBits_sle_eq, evalBits_sgt_eq, evalBits_sge_eq,
        evalBool_eq_beq, evalBool_ne_bne, evalBool_ult_eq, evalBool_ule_eq, evalBool_ugt_eq,
        evalBool_uge_eq, evalBool_slt_eq, evalBool_sle_eq, evalBool_sgt_eq, evalBool_sge_eq,
        lift1, lift2, lift3, liftCmp, cast_eq, ite_true, ite_false, Bool.false_eq_true,
        Bool.true_eq_false, BitVec.reduceSignExtend, BitVec.reduceSetWidth, BitVec.reduceAdd,
        BitVec.reduceMul, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceDiv]
      try refine ⟨by decide, ?_⟩
      exact hP))

private theorem bv64_shl1_u32_nat (x : BitVec 32) :
    (x.setWidth 64 <<< (1 : Nat)).toNat = 2 * x.toNat := bv64_shl1_u32 x

private theorem bv64_shl1_add1_nat (x : BitVec 32) :
    ((x.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * x.toNat + 1 := by
  have hx := x.isLt
  rw [bv64_add1_toNat (by rw [bv64_shl1_u32_nat]; omega), bv64_shl1_u32_nat]

local elab "fp_head_steps" : tactic => do
  let binOps : Array (Lean.Name × Lean.Name) := #[
    (``OpCode.add, ``wp_let_add_b), (``OpCode.sub, ``wp_let_sub_b), (``OpCode.mul, ``wp_let_mul_b),
    (``OpCode.and, ``wp_let_and_b), (``OpCode.or, ``wp_let_or_b), (``OpCode.xor, ``wp_let_xor_b),
    (``OpCode.eq, ``wp_let_eq_b), (``CmpOp.eq, ``wp_let_eq_b), (``OpCode.ne, ``wp_let_ne_b),
    (``CmpOp.ne, ``wp_let_ne_b), (``OpCode.ult, ``wp_let_ult_b), (``CmpOp.ult, ``wp_let_ult_b),
    (``OpCode.ule, ``wp_let_ule_b), (``CmpOp.ule, ``wp_let_ule_b), (``OpCode.ugt, ``wp_let_ugt_b),
    (``CmpOp.ugt, ``wp_let_ugt_b), (``OpCode.uge, ``wp_let_uge_b), (``CmpOp.uge, ``wp_let_uge_b),
    (``OpCode.slt, ``wp_let_slt_b), (``CmpOp.slt, ``wp_let_slt_b), (``OpCode.sle, ``wp_let_sle_b),
    (``CmpOp.sle, ``wp_let_sle_b), (``OpCode.sgt, ``wp_let_sgt_b), (``CmpOp.sgt, ``wp_let_sgt_b),
    (``OpCode.sge, ``wp_let_sge_b), (``CmpOp.sge, ``wp_let_sge_b)]
  let unOps : Array (Lean.Name × Lean.Name) := #[
    (``OpCode.zext, ``wp_let_zext32_64), (``OpCode.sext, ``wp_let_sext8_32),
    (``OpCode.trunc, ``wp_let_trunc64_32)]
  let clearSet : Array Lean.Name := #[
    ``Exists, ``Std.ExtHashMap.sep, ``FullMem, ``FullCoreInv, ``FullWitnessInv, ``PropLitInv,
    ``SplitWatchesInv, ``AgreesExcept, ``FullTrailExt, ``FullArenaPermEq, ``FullState.LengthsOk,
    ``FullCoreState.LengthsOk, ``FullScratch.LengthsOk]
  let rec normProj : Nat → Lean.Expr → Lean.Expr
    | 0, x => x
    | n + 1, x =>
      let x := x.consumeMData
      if (x.isAppOf ``Prod.fst || x.isAppOf ``Prod.snd) && x.getAppNumArgs ≥ 3 then
        let p := normProj n (x.getArg! 2)
        if p.isAppOf ``Prod.mk && p.getAppNumArgs ≥ 4 then
          normProj n (p.getArg! (if x.isAppOf ``Prod.fst then 2 else 3))
        else x
      else x
  let argVal (x : Lean.Expr) : Option (Lean.Expr × Bool) :=
    let x := x.consumeMData
    if x.isAppOf ``LeanQbe.T.Arg.var then
      let v := normProj 6 x.appArg!
      some (v, v.isAppOf ``OfNat.ofNat || v.isAppOf ``BitVec.ofNat)
    else if x.isAppOf ``LeanQbe.T.Arg.imm then some (normProj 6 x.appArg!, true)
    else none
  let hdrLoadLems : Array Lean.Name := #[
    ``FullArenaTactics.load_full_arena_len, ``FullArenaTactics.load_full_search_ticks,
    ``FullArenaTactics.load_full_wusable, ``FullArenaTactics.load_full_values_ptr,
    ``FullArenaTactics.load_full_watch_vec_ptr, ``FullArenaTactics.load_full_arena_ptr,
    ``FullArenaTactics.load_full_watch_stk_ptr, ``FullArenaTactics.load_full_level_ptr,
    ``FullArenaTactics.load_full_cur_vars]
  let hdrStoreLems : Array Lean.Name := #[
    ``FullArenaTactics.store_full_search_ticks, ``FullArenaTactics.store_full_wusable,
    ``FullArenaTactics.store_full_oom, ``FullArenaTactics.store_full_confl_type,
    ``FullArenaTactics.store_full_confl_ref, ``FullArenaTactics.store_full_confl_lit0,
    ``FullArenaTactics.store_full_confl_lit1]
  let pickLems (isLoad : Bool) (ty : Lean.Expr) : Array Lean.Name :=
    if (ty.find? (·.isConstOf ``FullCfg.pWstk)).isSome then
      if isLoad then #[``FullArenaTactics.c0_load_full_wstk]
      else #[``FullArenaTactics.c0_store_full_wstk]
    else if (ty.find? (·.isConstOf ``FullCfg.pArena)).isSome then
      if isLoad then #[``FullArenaTactics.c0_load_full_arena]
      else #[``FullArenaTactics.c0_store_full_arena]
    else if (ty.find? (·.isConstOf ``FullCfg.pVals)).isSome then
      if isLoad then #[``FullArenaTactics.c0_load_full_vals] else #[]
    else if (ty.find? (·.isConstOf ``FullCfg.pWvec)).isSome then
      if isLoad then #[``FullArenaTactics.c0_load_full_wvec]
      else #[``FullArenaTactics.c0_store_full_wvec]
    else if (ty.find? (·.isConstOf ``FullCfg.pLevel)).isSome then
      if isLoad then #[``FullArenaTactics.c0_load_full_lvl] else #[]
    else if isLoad then hdrLoadLems else hdrStoreLems
  let solveMem (isLoad : Bool) (hmv : Lean.MVarId) : Lean.Elab.Tactic.TacticM Unit := do
    Lean.Elab.Tactic.setGoals [hmv]
    Lean.Elab.Tactic.evalTactic
      (← `(tactic| (try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]);
        (try dsimp (config := { zeta := false }) only)))
    let hmv ← Lean.Elab.Tactic.getMainGoal
    let lems := pickLems isLoad (← Lean.instantiateMVars (← hmv.getType))
    let mut solved := false
    for nm in lems do
      let s ← Lean.saveState
      let ok ← try
        let sub ← Lean.Meta.withReducible <|
          hmv.apply (← Lean.Meta.mkConstWithFreshMVarLevels nm)
        let mut allOk := true
        for g' in sub do
          if !allOk then break
          if (← Lean.instantiateMVars (← g'.getType)).isAppOf ``Std.ExtHashMap.sep then
            Lean.Elab.Tactic.setGoals [g']
            Lean.Meta.withReducible <|
              Lean.Elab.Tactic.evalTactic (← `(tactic| first | assumption | c0_frame))
            if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then allOk := false
        for g' in sub do
          if !allOk || (← g'.isAssigned) then continue
          if ← Lean.Meta.isProp (← g'.getType) then
            Lean.Elab.Tactic.setGoals [g']
            Lean.Elab.Tactic.evalTactic (← `(tactic| first | rfl | assumption | decide | skip))
            if (← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then continue
            let g' ← Lean.Elab.Tactic.getMainGoal
            let toClear ← g'.withContext do
              let mut ids : Array Lean.FVarId := #[]
              for d in (← Lean.getLCtx).decls do
                let some d := d | continue
                if d.isAuxDecl || d.isLet then continue
                if ← Lean.Meta.isProp d.type then
                  let ty := d.type.consumeMData
                  let isBig := ty.isForall && !ty.bindingBody!.consumeMData.isConstOf ``False
                  if isBig || (ty.getAppFn.constName?.any (clearSet.contains ·)) then
                    ids := ids.push d.fvarId
              pure ids
            let g' ← g'.tryClearMany toClear
            Lean.Elab.Tactic.setGoals [g']
            Lean.Elab.Tactic.evalTactic (← `(tactic|
              ((try dsimp (config := { zeta := false }) only)
               (try simp only [List.length_set])
               first | assumption | rfl | decide | omega
                     | (simp only [bv_c0_zext32_64, bv32_xor_1, bv32_lshr_1, bv64_shl1_u32_nat,
                          bv64_shl1_add1_nat, BitVec.toNat_add, ← BitVec.ofNat_eq_ofNat,
                          BitVec.toNat_ofNat, Nat.reduceMod, BitVec.reduceToNat]; omega))))
            if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then allOk := false
        for g' in sub do if !(← g'.isAssigned) then allOk := false
        pure allOk
      catch _ => pure false
      if ok then solved := true; break else s.restore
    if !solved then throwError "fp_head_steps: solveMem failed on {← hmv.getType}"
  let headBetaWp (g : Lean.MVarId) : Lean.Elab.Tactic.TacticM Lean.MVarId :=
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData.headBeta
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
        let e' := (ty.getArg! 4).consumeMData.headBeta.consumeMData
        if e' == ty.getArg! 4 then return g
        let mvar ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar
          (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e'))
        g.assign (← Lean.Meta.mkAppM ``wp_head_eq #[← Lean.Meta.mkEqRefl e', mvar])
        return mvar.mvarId!
      return g
  let mut todo ← Lean.Elab.Tactic.getGoals
  let mut done : List Lean.MVarId := []
  while !todo.isEmpty do
    let g0 :: rest := todo | break
    todo := rest
    let g ← headBetaWp g0
    let head? ← g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
        return some ((ty.getArg! 4).consumeMData.getAppFn.constName?, ty.getArg! 5)
      return none
    let some (fn?, m0) := head? | done := g :: done; continue
    if fn? == some ``LeanQbe.T.Blocks.get then
      Lean.Elab.Tactic.setGoals [g]
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply wp_blocks_here))
      todo := (← Lean.Elab.Tactic.getGoals) ++ todo
    else if fn? == some ``LeanQbe.T.Expr.let_ then
      let fastGoal? ← g.withContext do
        let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
        let e := (ty.getArg! 4).consumeMData
        if e.getAppNumArgs < 6 then return none
        let op := (e.getArg! 4).consumeMData
        if !(op.isAppOf ``LeanQbe.T.Op.mk && op.getAppNumArgs ≥ 5) then return none
        let gΓ := ty.getArg! 0; let grs := ty.getArg! 1; let gQ := ty.getArg! 2
        let gX := ty.getArg! 3; let gm := ty.getArg! 5; let gk := e.getArg! 5
        let code := (op.getArg! 3).consumeMData; let args := (op.getArg! 4).consumeMData
        let applyPf (nm : Lean.Name) (xs : Array (Option Lean.Expr)) :
            Lean.Meta.MetaM (Option Lean.MVarId) := do
          let s ← Lean.saveState
          try
            let [hk] ← g.apply (← Lean.Meta.mkAppOptM nm xs) | s.restore; return none
            return some hk
          catch _ => s.restore; return none
        let c := code.getAppFn.constName?
        let key? :=
          if c == some ``OpCode.cmp && code.getAppNumArgs ≥ 1 then
            (code.getArg! 0).consumeMData.getAppFn.constName?
          else c
        if !(args.isAppOf ``Prod.mk && args.getAppNumArgs ≥ 4) then return none
        let a := args.getArg! 2; let r := (args.getArg! 3).consumeMData
        let some (va, ia) := argVal a | return none
        if let some (_, nm) := key?.bind fun k => binOps.find? (·.1 == k) then
          if !(r.isAppOf ``Prod.mk && r.getAppNumArgs ≥ 4) then return none
          let b := r.getArg! 2
          let some (vb, ib) := argVal b | return none
          if ia && ib then return none
          applyPf nm #[some gΓ, some grs, none, some gQ, some gX, some gm, some a, some b,
            some va, some vb, some gk, some (← Lean.Meta.mkEqRefl va),
            some (← Lean.Meta.mkEqRefl vb)]
        else if let some (_, nm) := c.bind fun k => unOps.find? (·.1 == k) then
          if ia then return none
          applyPf nm #[some gΓ, some grs, some gQ, some gX, some gm, some a, some va, some gk,
            some (← Lean.Meta.mkEqRefl va)]
        else if c == some ``OpCode.shl && !ia && r.isAppOf ``Prod.mk &&
            r.getAppNumArgs ≥ 4 then
          let b := r.getArg! 2
          let some (vb, _) := argVal b | return none
          applyPf ``wp_let_shl64_1 #[some gΓ, some grs, some gQ, some gX, some gm, some a, some b,
            some va, some gk, some (← Lean.Meta.mkEqRefl va), some (← Lean.Meta.mkEqRefl vb)]
        else if c == some ``OpCode.lshr && !ia && r.isAppOf ``Prod.mk &&
            r.getAppNumArgs ≥ 4 then
          let b := r.getArg! 2
          let some (vb, _) := argVal b | return none
          applyPf ``wp_let_lshr32_1 #[some gΓ, some grs, some gQ, some gX, some gm, some a, some b,
            some va, some gk, some (← Lean.Meta.mkEqRefl va), some (← Lean.Meta.mkEqRefl vb)]
        else return none
      if let some hk := fastGoal? then
        todo := hk :: todo
      else
        Lean.Elab.Tactic.setGoals [g]
        Lean.Elab.Tactic.evalTactic (← `(tactic| fp_head_let))
        todo := (← Lean.Elab.Tactic.getGoals) ++ todo
    else if fn? == some ``LeanQbe.T.Expr.load then
      let gs ← g.withContext <|
        g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``LeanQbe.T.wp_load_of)
      let [hl, hk] := gs.take 2 | throwError "fp_head_steps: bad load"
      solveMem true hl
      todo := hk :: todo
    else if fn? == some ``LeanQbe.T.Expr.store then
      let gs ← g.withContext <|
        g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``LeanQbe.T.wp_store_sep)
      let [hs, hk] := gs.take 2 | throwError "fp_head_steps: bad store"
      solveMem false hs
      Lean.Elab.Tactic.setGoals [hk]
      let mId := Lean.mkIdent `m
      let hmId := Lean.mkIdent `hm
      Lean.Elab.Tactic.evalTactic (← `(tactic| intro $mId:ident $hmId:ident))
      Lean.Elab.Tactic.evalTactic (← `(tactic| try simp only [LeanQbe.T.Arg.val_var,
        LeanQbe.T.Arg.val_imm, Std.ExtHashMap.sep_emp] at $hmId:ident))
      Lean.Elab.Tactic.evalTactic
        (← `(tactic| try dsimp (config := { zeta := false }) only at $hmId:ident))
      if let .fvar mId0 := m0 then
        Lean.Elab.Tactic.withMainContext do
          for d in (← Lean.getLCtx).decls.toArray.reverse do
            let some d := d | continue
            let t ← Lean.instantiateMVars d.type
            if t.isAppOf ``Std.ExtHashMap.sep && t.appArg! == m0 then
              try Lean.Elab.Tactic.liftMetaTactic1 fun g => some <$> g.clear d.fvarId
              catch _ => pure ()
          try Lean.Elab.Tactic.liftMetaTactic1 fun g => some <$> g.clear mId0
          catch _ => pure ()
      todo := (← Lean.Elab.Tactic.getGoals) ++ todo
    else if fn? == some ``LeanQbe.T.Expr.jnz then
      Lean.Elab.Tactic.setGoals [g]
      let hc := Lean.mkIdent `hc
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        refine wp_jnz_of (fun $hc:ident => ?_) (fun $hc:ident => ?_) <;> (
          try simp only [Arg.val_var, Arg.val_imm] at $hc:ident
          c0_cond $hc
          try (first | exact ($hc).elim | exact absurd rfl $hc | exact $hc rfl
                     | exact absurd trivial $hc))))
      todo := (← Lean.Elab.Tactic.getGoals) ++ todo
    else if fn? == some ``LeanQbe.T.Expr.ret then
      Lean.Elab.Tactic.setGoals [g]
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        (apply wp_ret_head; simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm])))
      done := (← Lean.Elab.Tactic.getGoals).reverse ++ done
    else if fn? == some ``LeanQbe.T.Expr.jump then
      Lean.Elab.Tactic.setGoals [g]
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        (apply wp_jump_head; simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm])))
      done := (← Lean.Elab.Tactic.getGoals).reverse ++ done
    else
      done := g :: done
  Lean.Elab.Tactic.setGoals done.reverse

/-! ## 2. `full_prop_lit` `Func.wp` proof -/

theorem full_prop_lit_wp (Γ : Env)
    (hFind : ∀ args m Q X, fullFindReplSpec args m Q X →
      Γ "full_find_repl" [i64, i64] [i64] args m Q X)
    (hPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hAssignLvl : ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hAssignLevel : ∀ args m Q X, fullAssignLevelSpec args m Q X →
      Γ "full_assign_level" [i64, i32, i32] [i32] args m Q X) :
    ∀ args m Q X, fullPropLitSpec args m Q X →
      Func.wp Γ full_prop_lit_body args m Q X := by
  rintro ⟨h, lit, ignore_ref, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hoom0, hm, hQ⟩
  have hmaxv := c.hmaxv; have har := c.harena; have hwc := c.hwcap
  unfold dimacsBound at hmaxv har hwc
  have hcv0 := hlen0.core_ok.cur_vars_le
  let not_lit : BitVec 32 := lit ^^^ 1#32
  have hret_st : ∀ (ok : Bool) (st : FullState) (ml : Mem 64),
      st.LengthsOk c → FullWitnessInv c F0 F_cur st.core →
      AgreesExcept propLitCoreMask s.core st.core →
      FullTrailExt s.core st.core → FullArenaPermEq s.core st.core →
      st.scratch = { s.scratch with
        search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
        phases := st.scratch.phases } →
      (ok = true → st.core.oom = 0#64 ∧ st.core.confl_type = s.core.confl_type) →
      (ok = false → PropLitConfl F_cur ignore_ref st.core) →
      (FullMem c st ⋆ R) ml → Q (ok, ()) ml := by
    intro ok st ml hst_l hst_w hag htr hperm hsc hok_oom hcf hml
    have hst_eq := propLit_eq_upd hag hsc
    have hst_l' := hst_l; have hst_w' := hst_w; have htr' := htr; have hperm' := hperm
    rw [hst_eq] at hst_l' hst_w' htr' hperm' hml
    refine hQ ok st.core.vals st.core.flags st.core.lvl st.core.rsns st.core.trl st.core.trail_pos
      st.core.trail_end st.core.unassigned st.core.unflushed st.core.wvec st.core.arena
      st.core.wstk st.core.wlen st.core.wusable st.core.confl_type st.core.confl_ref
      st.core.confl_lit0 st.core.confl_lit1 st.core.oom st.scratch.search_ticks st.scratch.wsort
      st.scratch.phases ml hst_l' hst_w' htr' hperm' hok_oom ?_ hml
    intro hf; have hcf' := hcf hf; unfold PropLitConfl at hcf'; rw [hst_eq] at hcf'; exact hcf'
  have hret_noop : Q (true, ()) m :=
    hret_st true s m hlen0 hw0 (.refl _ _) (.refl _) (.refl _) rfl (fun _ => ⟨hoom0, rfl⟩)
      (by simp) hm
  have hvl0 := hlen0.core_ok.vals_len; have hwv0 := hlen0.core_ok.wvec_len
  unfold Func.wp full_prop_lit_body
  fp_head_steps
  · exact hret_noop
  · exact hret_noop
  · exact hret_noop
  · have hnot_xor : not_lit.toNat = lit.toNat ^^^ 1 := bv32_xor_1 lit
    have hnot_lt : not_lit.toNat < 2 * s.core.cur_vars := by
      have h1 : ¬ 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 ≤ lit.toNat ^^^ 1 := by assumption
      rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at h1; omega
    have hnot_f0 : s.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 := by
      have hsge : (0#32).sle ((s.core.vals[not_lit.toNat]'(by omega)).signExtend 32) = false := by
        have h2 : (0#32).sle ((s.core.vals[lit.toNat ^^^ 1]'(by omega)).signExtend 32) = false := by
          assumption
        simpa only [hnot_xor] using h2
      rw [bv32_sle0_eq_not_slt0, Bool.not_eq_false'] at hsge
      have hget : s.core.vals[not_lit.toNat]?.getD 0#8 = s.core.vals[not_lit.toNat]'(by omega) := by
        simp [List.getElem?_eq_getElem (show not_lit.toNat < s.core.vals.length by omega)]
      rw [hget]; exact (full_i8_vals_slt0 (by rw [← hget]; exact hw0.vals_domain _ hnot_lt)).mp hsge
    have hidx0 : ((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)).toNat =
        2 * not_lit.toNat := bv64_shl1_u32 not_lit
    have hidx1 : (((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
        (1 : BitVec 64)).toNat = 2 * not_lit.toNat + 1 := by
      rw [bv64_add1_toNat (by rw [hidx0]; omega), hidx0]
    have hoff0_eq : (s.core.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<<
        (1 : BitVec 64)).toNat]'(by omega)).toNat = fullWatchOffCore s.core not_lit.toNat := by
      unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact congrArg BitVec.toNat (by congr 1)
    have hsz0_eq : (s.core.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
        (1 : BitVec 64)).toNat]'(by omega)).toNat = fullWatchSizeCore s.core not_lit.toNat := by
      unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact congrArg BitVec.toNat (by congr 1)
    have hsz0_pos : 0 < fullWatchSizeCore s.core not_lit.toNat := by
      rw [← hsz0_eq]
      have h1 : (2 * (lit.toNat ^^^ 1) + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
          (((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
            (1 : BitVec 64)).toNat := by
        rw [hidx1, ← hnot_xor]; change (2 * not_lit.toNat + 1) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      have heq_w : s.core.wvec[(2 * (lit.toNat ^^^ 1) + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(
            by omega) = s.core.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
            (1 : BitVec 64)).toNat]'(by omega) := by congr 1
      have hne0 : (s.core.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
          (1 : BitVec 64)).toNat]'(by omega)).setWidth 64 ≠ 0#64 := fun heq => hc (by
        change (s.core.wvec[(2 * (lit.toNat ^^^ 1) + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(
          by omega)).setWidth 64 = 0#64
        rw [heq_w]; exact heq)
      exact Nat.pos_of_ne_zero fun h0 =>
        hne0 (BitVec.eq_of_toNat_eq (by rw [bv_c0_zext32_64, h0]; rfl))
    clear hc; clear hc
    let st0 : FullState :=
      { s with scratch := { s.scratch with search_ticks := s.scratch.search_ticks + 1#64 } }
    have hlen_st0 : st0.LengthsOk c := ⟨hlen0.core_ok, hlen0.scratch_ok.with_ticks _⟩
    have hwat0 : WatchesInv F_cur s.core := by
      have h := hw0.watches; unfold ModeWatchesInv at h; simpa [hdense0] using h
    have hpi0 : PropLitInv c F0 F_cur s st0 not_lit.toNat (fullWatchOffCore s.core not_lit.toNat)
        (fullWatchOffCore s.core not_lit.toNat) (fullWatchOffCore s.core not_lit.toNat)
        (fullWatchOffCore s.core not_lit.toNat + fullWatchSizeCore s.core not_lit.toNat) :=
      { len := hlen_st0
        nw := fullWitnessInv_to_nw hcv0 hw0
        sw := SplitWatchesInv.init hnot_lt hwat0 hsz0_pos
        ag := .refl _ _, tr := .refl _, perm := .refl _, sc_eq := rfl, not_f := hnot_f0 }
    refine wp_loop_break_group
      (fun (off_v, p_v, q_v, end_v, confl_v, ()) mb => ∃ st : FullState,
        PropLitInv c F0 F_cur s st not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat ∧
        (confl_v = false → st.core.oom = 0#64 ∧ st.core.confl_type = s.core.confl_type) ∧
        (confl_v = true → PropLitConfl F_cur ignore_ref st.core) ∧
        (FullMem c st ⋆ R) mb)
      (fun rem (off_v, p_v, q_v, end_v, ()) ml => ∃ st : FullState,
        rem = end_v.toNat - p_v.toNat ∧
        PropLitInv c F0 F_cur s st not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat ∧
        st.core.oom = 0#64 ∧ st.core.confl_type = s.core.confl_type ∧
        (FullMem c st ⋆ R) ml) ?_ ?_ ?_
    · -- Post-loop break/exit join `B`: Loop 2 (tail copy) -> Loop 3 (sentinel fill) -> store -> ret
      rintro _ ⟨off_v, p_v, q_v, end_v, confl_v, ⟨⟩⟩ mb ⟨st, hpi, hcf_f, hcf_t, hmb⟩
      have hnot_st : not_lit.toNat < 2 * st.core.cur_vars := hpi.cur_vars_eq.symm ▸ hnot_lt
      clear hc hret_noop hvl0 hwv0 hoff0_eq hsz0_eq hsz0_pos hpi0 hlen_st0 st0 hnot_f0 hm hw0 hlen0
        hoom0 hidx0 hwat0
      have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_st
      have hq_ge := hpi.sw.q_ge; have hq_le := hpi.sw.q_le_p; have hp_le := hpi.sw.p_le_end
      have hwstk_len := hpi.len.core_ok.wstk_len_arr; have hwvec_len := hpi.len.core_ok.wvec_len
      let q_fin : Nat := q_v.toNat + (end_v.toNat - p_v.toNat)
      -- Loop 2: `while (p < end) { wstk[q] = wstk[p]; q++; p++; }`
      refine wp_loop_inv
        (fun (p_c, q_c, ()) m2 => ∃ wstk_c : List (BitVec 32),
          wstk_c.length = c.wcap ∧ p_v.toNat ≤ p_c.toNat ∧ p_c.toNat ≤ end_v.toNat ∧
          q_c.toNat = q_v.toNat + (p_c.toNat - p_v.toNat) ∧
          (∀ k, off_v.toNat ≤ k → k < q_v.toNat → wstk_c[k]? = st.core.wstk[k]?) ∧
          (∀ k < p_c.toNat - p_v.toNat, wstk_c[q_v.toNat + k]? = st.core.wstk[p_v.toNat + k]?) ∧
          (∀ k, p_c.toNat ≤ k → k < end_v.toNat → wstk_c[k]? = st.core.wstk[k]?) ∧
          (∀ k, (k < off_v.toNat ∨ end_v.toNat ≤ k) → wstk_c[k]? = st.core.wstk[k]?) ∧
          (FullMem c { st with core := { st.core with wstk := wstk_c } } ⋆ R) m2)
        (fun (p_c, _, ()) _ => end_v.toNat - p_c.toNat)
        (fun L2 hL2 => by
          fp_head_steps
          exact hL2 (p_v, q_v, ()) mb ⟨st.core.wstk, hwstk_len, Nat.le_refl _, hp_le, by omega,
            fun _ _ _ => rfl, fun _ hk => by omega, fun _ _ _ => rfl, fun _ _ => rfl, hmb⟩)
        (fun L2 (p_c, q_c, ()) m2 ⟨wstk_c, hwl2, hp_ge, hp_le2, hqc_eq,
            hpre, hsuf, hrem, hout, hm2⟩ ih2 => ?_)
      fp_head_steps
      · have hp_lt : p_c.toNat < end_v.toNat := hc
        have hstep := propLit_loop2_step hq_ge hq_le hp_ge hp_lt (by omega) (by omega)
          hpre hsuf hrem hout
        have hpc_add : (p_c + (1 : BitVec 64)).toNat = p_c.toNat + 1 := bv64_add1_toNat (by omega)
        have hqc_add : (q_c + (1 : BitVec 64)).toNat =
            q_v.toNat + ((p_c + (1 : BitVec 64)).toNat - p_v.toNat) := by
          rw [bv64_add1_toNat (by omega), hpc_add]; omega
        refine ih2 (p_c + (1 : BitVec 64), q_c + (1 : BitVec 64), ()) m (by dsimp only; omega)
          ⟨wstk_c.set q_c.toNat (wstk_c[p_c.toNat]'(by omega)), by simp [hwl2],
            by omega, by omega, hqc_add, ?_, ?_, ?_, ?_, hm⟩
        · simpa only [← hqc_eq] using hstep.1
        · rw [hpc_add]; simpa only [← hqc_eq] using hstep.2.1
        · rw [hpc_add]; simpa only [← hqc_eq] using hstep.2.2.1
        · simpa only [← hqc_eq] using hstep.2.2.2
      · have hpc_eq : p_c.toNat = end_v.toNat := by omega
        have hqfin_eq : q_c.toNat = q_fin := by dsimp [q_fin]; omega
        -- Loop 3: `k = q; while (k < end) { wstk[k] = 0xFFFFFFFFu; k++; }`
        refine wp_loop_inv
          (fun (k_c, ()) m3 => ∃ wstk_k : List (BitVec 32),
            wstk_k.length = c.wcap ∧ q_fin ≤ k_c.toNat ∧ k_c.toNat ≤ end_v.toNat ∧
            (∀ i, (i < q_fin ∨ end_v.toNat ≤ i) → wstk_k[i]? = wstk_c[i]?) ∧
            (FullMem c { st with core := { st.core with wstk := wstk_k } } ⋆ R) m3)
          (fun (k_c, ()) _ => end_v.toNat - k_c.toNat)
          (fun L3 hL3 => by
            fp_head_steps
            exact hL3 (q_c, ()) m2 ⟨wstk_c, hwl2, by omega, by omega, fun _ _ => rfl, hm2⟩)
          (fun L3 (k_c, ()) m3 ⟨wstk_k, hwl3, hk_ge, hk_le, hkeep, hm3⟩ ih3 => ?_)
        fp_head_steps
        · have hk_lt : k_c.toNat < end_v.toNat := hc
          have hk_add : (k_c + 1#64).toNat = k_c.toNat + 1 := bv64_add1_toNat (by omega)
          refine ih3 (k_c + 1#64, ()) m (by dsimp only; omega)
            ⟨wstk_k.set k_c.toNat 0xFFFFFFFF#32, by simp [hwl3], by omega, by omega,
              propLit_loop3_step hk_ge hk_lt hkeep, hm⟩
        · have ⟨hl_f, hw_f, hag_f, htr_f, hperm_f, hsc_f, hcf_f', hoom_f, hm_f⟩ :=
            propLit_finish (ctype0 := s.core.confl_type) hpi hdense0 hnot_st hwl3 hqfin_eq hidx1
              hpre (fun k hk => hsuf k (by omega)) hout hkeep hcf_f hcf_t hm
          exact hret_st (!confl_v) _ m hl_f hw_f hag_f htr_f hperm_f hsc_f hoom_f hcf_f' hm_f
    · -- Main loop body `L`: `while (p < end)`
      rintro B L rem ⟨off_v, p_v, q_v, end_v, ⟨⟩⟩ ml hB ih ⟨st, rfl, hpi, hoom_st, hct_st, hml⟩
      have hcv_eq : st.core.cur_vars = s.core.cur_vars := hpi.cur_vars_eq
      have hnot_st : not_lit.toNat < 2 * st.core.cur_vars := hcv_eq.symm ▸ hnot_lt
      clear hc hret_noop hvl0 hwv0 hoff0_eq hsz0_eq hsz0_pos hpi0 hlen_st0 st0 hnot_f0 hm hw0 hlen0
        hoom0 hidx1 hret_st hQ hwat0 hdense0
      have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_st
      have hq_ge := hpi.sw.q_ge; have hq_le := hpi.sw.q_le_p; have hp_le := hpi.sw.p_le_end
      have hwstk_len := hpi.len.core_ok.wstk_len_arr; have hvals_len := hpi.len.core_ok.vals_len
      have haren_len := hpi.len.core_ok.arena_len_arr; have halen_le := hpi.len.core_ok.arena_len_le
      have hwvec_len := hpi.len.core_ok.wvec_len; have hlvl_len := hpi.len.core_ok.lvl_len
      have h1_64 : ((1 : BitVec 64)).toNat = 1 := rfl
      have hp1_pre : (p_v + (1 : BitVec 64)).toNat = p_v.toNat + 1 := bv64_add1_toNat (by omega)
      fp_head_steps
      · -- Binary watch, `other >= nlits` (dead!)
        have hp_lt : p_v.toNat < end_v.toNat := by assumption
        have hw0_get : st.core.wstk[p_v.toNat]? = some (st.core.wstk[p_v.toNat]'(by omega)) :=
          List.getElem?_eq_getElem (by omega)
        have hflag : (st.core.wstk[p_v.toNat]'(by omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
        have ⟨hother_lt, _, _⟩ := watchSlice_inv_bin hpi.sw.rem_slice (by omega) hw0_get hflag
        have hge : 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 ≤
            (st.core.wstk[p_v.toNat]'(by omega) &&& 0x7FFFFFFF#32).toNat := hc
        rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hge
        omega
      · -- Binary watch, `ov > 0`: keep watch & continue
        have hp_lt : p_v.toNat < end_v.toNat := by assumption
        have hw0_get : st.core.wstk[p_v.toNat]? = some (st.core.wstk[p_v.toNat]'(by omega)) :=
          List.getElem?_eq_getElem (by omega)
        have hflag : (st.core.wstk[p_v.toNat]'(by omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
        have ⟨hother_lt, hent, hrem1⟩ :=
          watchSlice_inv_bin hpi.sw.rem_slice (by omega) hw0_get hflag
        have hsw1 := (hpi.sw.advance_rem (p' := p_v.toNat + 1) (by omega) (by omega)
          (by simpa [Nat.sub_sub] using hrem1)).write_bin (c := c) (by omega) hnot_st hq_le
          (by omega) hflag hother_lt hent
        let st1 : FullState :=
          { st with core := { st.core with
              wstk := st.core.wstk.set q_v.toNat (st.core.wstk[p_v.toNat]'(by omega)) } }
        have hlen1 : st1.LengthsOk c :=
          ⟨{ hpi.len.core_ok with wstk_len_arr := by simp [st1, hwstk_len] }, hpi.len.scratch_ok⟩
        have hp1 : (p_v + 1#64).toNat = p_v.toNat + 1 := bv64_add1_toNat (by omega)
        have hq1 : (q_v + 1#64).toNat = q_v.toNat + 1 := bv64_add1_toNat (by omega)
        refine ih (end_v.toNat - (p_v + 1#64).toNat) (off_v, p_v + 1#64, q_v + 1#64, end_v, ()) m
          (by omega) ⟨st1, rfl, ?_, hoom_st, hct_st, hm⟩
        exact
          { len := hlen1
            nw := fullWitnessInv_nw_congr hlen1.core_ok.cur_vars_le hpi.nw
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            sw := by rwa [hp1, hq1]
            ag := hpi.ag.update (fun k => { k with wstk := st1.core.wstk })
            tr := hpi.tr.congr rfl rfl rfl, perm := hpi.perm
            sc_eq := hpi.sc_eq, not_f := hpi.not_f }
      · -- Binary watch, `ov < 0`: record binary conflict & break
        have hp_lt : p_v.toNat < end_v.toNat := by assumption
        have hw0_get : st.core.wstk[p_v.toNat]? = some (st.core.wstk[p_v.toNat]'(by omega)) :=
          List.getElem?_eq_getElem (by omega)
        have hflag : (st.core.wstk[p_v.toNat]'(by omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
        have ⟨hother_lt, hent, hrem1⟩ :=
          watchSlice_inv_bin hpi.sw.rem_slice (by omega) hw0_get hflag
        have hsw1 := (hpi.sw.advance_rem (p' := p_v.toNat + 1) (by omega) (by omega)
          (by simpa [Nat.sub_sub] using hrem1)).write_bin (c := c) (by omega) hnot_st hq_le
          (by omega) hflag hother_lt hent
        have hov_f := propLit_vals_neg hpi.nw hother_lt (by omega) hc
        have ⟨hpi_c, hcf_c⟩ := propLit_bin_confl (ignore_ref := ignore_ref) hpi hsw1 hnot_st
          hother_lt hent hov_f (bv64_add1_toNat (by omega)) (bv64_add1_toNat (by omega))
        exact hB (off_v, p_v + 1#64, q_v + 1#64, end_v, true, ()) m
          ⟨_, hpi_c, by simp, fun _ => hcf_c, hm⟩
      · -- Binary watch, `ov == 0`: `full_assign_lvl(h, other, bin_rsn, lvl[not_lit >> 1])`
        have hp_lt : p_v.toNat < end_v.toNat := by assumption
        have hw0_get : st.core.wstk[p_v.toNat]? = some (st.core.wstk[p_v.toNat]'(by omega)) :=
          List.getElem?_eq_getElem (by omega)
        have hflag : (st.core.wstk[p_v.toNat]'(by omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
        have ⟨hother_lt, hent, hrem1⟩ :=
          watchSlice_inv_bin hpi.sw.rem_slice (by omega) hw0_get hflag
        have hsw1 := (hpi.sw.advance_rem (p' := p_v.toNat + 1) (by omega) (by omega)
          (by simpa [Nat.sub_sub] using hrem1)).write_bin (c := c) (by omega) hnot_st hq_le
          (by omega) hflag hother_lt hent
        let w0 := st.core.wstk[p_v.toNat]'(by omega)
        let other := w0 &&& 0x7FFFFFFF#32
        have hother_lt' : other.toNat < 2 * st.core.cur_vars := hother_lt
        let st1 : FullState :=
          { st with core := { st.core with wstk := st.core.wstk.set q_v.toNat w0 } }
        have hlen1 : st1.LengthsOk c :=
          ⟨{ hpi.len.core_ok with wstk_len_arr := by simp [st1, hwstk_len] }, hpi.len.scratch_ok⟩
        have hnw1 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st1.core) :=
          fullWitnessInv_nw_congr hlen1.core_ok.cur_vars_le hpi.nw
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        have hov_un : st1.core.vals[other.toNat]?.getD 0#8 = 0#8 :=
          propLit_vals_un hnw1 hother_lt' (by simp [st1]; omega) (by assumption) hc
        have hte_lt : st1.core.trail_end < st1.core.cur_vars :=
          hnw1.trail_end_lt_of_unassigned hother_lt' hov_un
        have hst1_cv : st1.core.cur_vars = st.core.cur_vars := rfl
        have hst1_cv_le : st1.core.cur_vars ≤ c.max_vars := hlen1.core_ok.cur_vars_le
        have hng_guard :
            ¬ (st1.core.cur_vars ≤ (st.core.wstk[p_v.toNat]'(by omega) &&&
                (2147483647 : BitVec 32)).toNat / 2 ∨ c.max_vars ≤ st1.core.trail_end ∨
              st1.core.vals[(st.core.wstk[p_v.toNat]'(by omega) &&&
                (2147483647 : BitVec 32)).toNat]?.getD 0#8 ≠ 0#8) := by
          change ¬ (st1.core.cur_vars ≤ other.toNat / 2 ∨ c.max_vars ≤ st1.core.trail_end ∨
            st1.core.vals[other.toNat]?.getD 0#8 ≠ 0#8)
          simp only [hov_un, ne_eq, not_true_eq_false, or_false]; omega
        have hix_not : (BitVec.setWidth 64 ((lit ^^^ (1 : BitVec 32)) >>> (1 : Nat))).toNat =
            not_lit.toNat / 2 := by
          rw [bv_c0_zext32_64, bv32_lshr_1, bv32_xor_1, hnot_xor]
        have halvl_eq : st1.core.lvl[(BitVec.setWidth 64 ((lit ^^^ (1 : BitVec 32)) >>>
            (1 : Nat))).toNat]'(by
              rw [hix_not]; change _ < st.core.lvl.length; omega) =
            st1.core.lvl[not_lit.toNat / 2]?.getD 0#32 := by
          rw [List.getElem?_eq_getElem (by change not_lit.toNat / 2 < st.core.lvl.length; omega),
            Option.getD_some]
          congr 1
        c0_call hAssignLvl
        refine ⟨c, st1, R, rfl, hlen1, hm, ?_⟩
        simp only [hng_guard, ↓reduceIte]
        intro flags' unas' unfl' phases' m_as hfl_len hph_len hm_as
        rw [halvl_eq] at hm_as
        let alvl := st1.core.lvl[not_lit.toNat / 2]?.getD 0#32
        let bin_rsn := (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32
        let st2 : FullState :=
          { core :=
              { st1.core with
                vals := (st1.core.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
                flags := flags', lvl := st1.core.lvl.set (other.toNat / 2) alvl
                rsns := st1.core.rsns.set (other.toNat / 2)
                  (if alvl = 0#32 then 0xFFFFFFFF#32 else bin_rsn)
                trl := st1.core.trl.set st1.core.trail_end other
                trail_pos := st1.core.trail_pos.set (other.toNat / 2)
                  (BitVec.ofNat 32 st1.core.trail_end)
                trail_end := st1.core.trail_end + 1
                unassigned := unas', unflushed := unfl' }
            scratch := { st1.scratch with phases := phases' } }
        have hlen2 : st2.LengthsOk c :=
          ⟨{ hlen1.core_ok with
              vals_len := by simp [st2, st1, hvals_len], flags_len := hfl_len,
              lvl_len := by simp [st2, st1, hlvl_len],
              rsns_len := by simp [st2, hlen1.core_ok.rsns_len],
              trl_len := by simp [st2, hlen1.core_ok.trl_len],
              trail_pos_len := by simp [st2, hlen1.core_ok.trail_pos_len],
              trail_end_le := by dsimp [st2]; omega,
              propagated_le := by have := hlen1.core_ok.propagated_le; dsimp [st2]; omega },
           { hlen1.scratch_ok with phases_len := hph_len }⟩
        have ⟨hnw2, hnot_f2, htr12⟩ := full_bin_assign_nw_step hlen1.core_ok hnw1 hnot_st
          hother_lt' hov_un hpi.not_f hent (flags' := flags') (unas' := unas') (unfl' := unfl')
        have hp1 : (p_v + 1#64).toNat = p_v.toNat + 1 := bv64_add1_toNat (by omega)
        have hq1 : (q_v + 1#64).toNat = q_v.toNat + 1 := bv64_add1_toNat (by omega)
        fp_head_steps
        refine ih (end_v.toNat - (p_v + 1#64).toNat) (off_v, p_v + 1#64, q_v + 1#64, end_v, ())
          m_as (by omega) ⟨st2, rfl, ?_, hoom_st, hct_st, hm_as⟩
        exact
          { len := hlen2, nw := hnw2
            sw := by rw [hp1, hq1]; exact hsw1.with_nonwatch rfl rfl rfl rfl rfl
            ag := hpi.ag.update (fun k => { k with
              vals := st2.core.vals, flags := flags', lvl := st2.core.lvl, rsns := st2.core.rsns,
              trl := st2.core.trl, trail_pos := st2.core.trail_pos, trail_end := st2.core.trail_end,
              unassigned := unas', unflushed := unfl', wstk := st1.core.wstk })
            tr := (hpi.tr.congr (k2 := st1.core) rfl rfl rfl).trans htr12
            perm := hpi.perm, sc_eq := by dsimp only [st2, st1]; rw [hpi.sc_eq]
            not_f := hnot_f2 }
      · -- Large watch, `p + 1 >= end` (dead!)
        have hp_lt : p_v.toNat < end_v.toNat := by assumption
        have hw0_get : st.core.wstk[p_v.toNat]? = some (st.core.wstk[p_v.toNat]'(by omega)) :=
          List.getElem?_eq_getElem (by omega)
        have hflag : (st.core.wstk[p_v.toNat]'(by omega) &&& 0x80000000#32) = 0#32 := by assumption
        have ⟨h2le, _⟩ := watchSlice_inv_large hpi.sw.rem_slice (by omega) hw0_get hflag
        have hge : end_v.toNat ≤ (p_v.toNat + 1) % 2 ^ 64 := hc
        rw [Nat.mod_eq_of_lt (by omega : p_v.toNat + 1 < 2 ^ 64)] at hge
        omega
      · -- Large watch, `p + 1 < end`: `cref = wstk[p + 1]`, `p2 = p + 2`, then join `Js_2`
        have hp_lt : p_v.toNat < end_v.toNat := by assumption
        have hw0_get : st.core.wstk[p_v.toNat]? = some (st.core.wstk[p_v.toNat]'(by omega)) :=
          List.getElem?_eq_getElem (by omega)
        have hflag : (st.core.wstk[p_v.toNat]'(by omega) &&& 0x80000000#32) = 0#32 := by assumption
        have ⟨h2le, cref0, hcr_get, hcr_lt, hcr_ref, hrem2⟩ :=
          watchSlice_inv_large hpi.sw.rem_slice (by omega) hw0_get hflag
        have hp1_nat : (p_v + (1 : BitVec 64)).toNat = p_v.toNat + 1 := bv64_add1_toNat (by omega)
        have hp2_nat : (p_v + (1 : BitVec 64) + (1 : BitVec 64)).toNat = p_v.toNat + 2 := by
          rw [bv64_add1_toNat (by omega), hp1_nat]
        have hq1_nat : (q_v + (1 : BitVec 64)).toNat = q_v.toNat + 1 := bv64_add1_toNat (by omega)
        have hq2_nat : (q_v + (2 : BitVec 64)).toNat = q_v.toNat + 2 := bv64_add2_toNat (by omega)
        have hcr_idx_lt : (p_v + (1 : BitVec 64)).toNat < st.core.wstk.length := by omega
        have hcr_eq : st.core.wstk[(p_v + (1 : BitVec 64)).toNat]'hcr_idx_lt = cref0 := by
          have h1 : st.core.wstk[p_v.toNat + 1]? =
              some (st.core.wstk[(p_v + (1 : BitVec 64)).toNat]'hcr_idx_lt) := by
            rw [← hp1_nat]; exact List.getElem?_eq_getElem hcr_idx_lt
          exact Option.some.inj (h1.symm.trans hcr_get)
        generalize hcr_gen :
          st.core.wstk[(p_v + (1 : BitVec 64)).toNat]'hcr_idx_lt = cref at hcr_eq ⊢
        generalize hw0_gen : st.core.wstk[p_v.toNat]'(by omega) = w0 at hflag ⊢
        rw [← hcr_eq] at hcr_lt hcr_ref
        have hsw_drop : SplitWatchesInv F_cur st.core not_lit.toNat off_v.toNat q_v.toNat
            (p_v.toNat + 2) end_v.toNat :=
          hpi.sw.advance_rem (p' := p_v.toNat + 2) (by omega) (by omega)
            (by simpa [Nat.sub_sub] using hrem2)
        -- Join `Js_2`: blocking literal did NOT satisfy clause
        refine wp_join_group (fun () m1 => m1 = ml) ?_ ?_
        · rintro _ ⟨⟩ m1 rfl
          have hcr_wf := hpi.nw.arena.refs_wf cref.toNat hcr_ref
          have hcr3_le : cref.toNat + 3 ≤ st.core.arena_len := hcr_wf.1
          have hcsz3 : 3 ≤ fullArenaClauseSizeCore st.core cref.toNat := hcr_wf.2.1
          have hcr_next : cref.toNat + 3 + fullArenaClauseSizeCore st.core cref.toNat ≤
              fullArenaNextOff st.core.arena st.core.arena_len cref.toNat := hcr_wf.2.2.1
          have hnext_le : fullArenaNextOff st.core.arena st.core.arena_len cref.toNat ≤
              st.core.arena_len := hcr_wf.2.2.2.1
          have hcr_fit : cref.toNat + 3 + fullArenaClauseSizeCore st.core cref.toNat ≤
              st.core.arena_len := by omega
          have hcr64 : (cref.setWidth 64).toNat = cref.toNat := bv_c0_zext32_64 cref
          have h2_idx : (cref.setWidth 64 + (2 : BitVec 64)).toNat = cref.toNat + 2 := by
            rw [bv64_add2_toNat (by omega), hcr64]
          have h3_idx : (cref.setWidth 64 + (3 : BitVec 64)).toNat = cref.toNat + 3 := by
            rw [bv64_add3_toNat (by omega), hcr64]
          have h4_idx : (cref.setWidth 64 + (4 : BitVec 64)).toNat = cref.toNat + 4 := by
            rw [bv64_add4_toNat (by omega), hcr64]
          fp_head_steps
          · have hgt : st.core.arena_len % 2 ^ 64 < (cref.toNat + 3) % 2 ^ 64 := hc
            rw [Nat.mod_eq_of_lt (by omega : st.core.arena_len < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : cref.toNat + 3 < 2 ^ 64)] at hgt; omega
          · exact ih _ (off_v, p_v + (1 : BitVec 64) + (1 : BitVec 64), q_v, end_v, ()) m
              (by omega) ⟨_, rfl, propLit_inv_drop
                (ticks' := st.scratch.search_ticks + (1 : BitVec 64)) hpi hsw_drop hp2_nat,
                hoom_st, hct_st, hm⟩
          · exact ih _ (off_v, p_v + (1 : BitVec 64) + (1 : BitVec 64), q_v, end_v, ()) m
              (by omega) ⟨_, rfl, propLit_inv_drop
                (ticks' := st.scratch.search_ticks + (1 : BitVec 64)) hpi hsw_drop hp2_nat,
                hoom_st, hct_st, hm⟩
          · exact ih _ (off_v, p_v + (1 : BitVec 64) + (1 : BitVec 64), q_v, end_v, ()) m
              (by omega) ⟨_, rfl, propLit_inv_drop
                (ticks' := st.scratch.search_ticks + (1 : BitVec 64)) hpi hsw_drop hp2_nat,
                hoom_st, hct_st, hm⟩
          · -- Live clause: `l0 = ar[cref+3]`, `l1 = ar[cref+4]`, then join `Js_3`
            let st_t : FullState :=
              { st with scratch :=
                { st.scratch with search_ticks := st.scratch.search_ticks + 1#64 } }
            have hlen_t : st_t.LengthsOk c :=
              ⟨hpi.len.core_ok, hpi.len.scratch_ok.with_ticks _⟩
            have hng_t : fullArenaClauseGarbCore st_t.core cref.toNat = false := by
              unfold fullArenaClauseGarbCore fullArenaHdrCore
              have hget : st_t.core.arena[cref.toNat]? =
                  some (st.core.arena[cref.toNat]'(by omega)) := by
                change st.core.arena[cref.toNat]? = _; exact List.getElem?_eq_getElem (by omega)
              rw [hget, Option.getD_some]
              have h0 : (st.core.arena[cref.toNat]'(by omega) &&& 0x00080000#32) = 0#32 := by
                assumption
              rw [h0]; rfl
            try clear hc; try clear hc; try clear hc; try clear hc
            have hsc_t : st_t.scratch = { s.scratch with
                search_ticks := st_t.scratch.search_ticks, wsort := st_t.scratch.wsort,
                phases := st_t.scratch.phases } := by dsimp only [st_t]; rw [hpi.sc_eq]
            -- Join `Js_3`: `(other, ())` where `ar[cref+3] = other ∧ ar[cref+4] = not_lit`
            refine wp_join_group
              (fun (other, ()) mj => ∃ st1 : FullState,
                PropLitInv c F0 F_cur s st1 not_lit.toNat off_v.toNat q_v.toNat (p_v.toNat + 2)
                  end_v.toNat ∧ st1.core.oom = 0#64 ∧
                st1.core.confl_type = s.core.confl_type ∧ st1.core.arena_len = st.core.arena_len ∧
                cref.toNat ∈ fullArenaClauseRefsCore st1.core ∧
                fullArenaClauseGarbCore st1.core cref.toNat = false ∧
                fullArenaClauseSizeCore st1.core cref.toNat =
                  fullArenaClauseSizeCore st.core cref.toNat ∧
                st1.core.arena[cref.toNat + 3]? = some other ∧
                st1.core.arena[cref.toNat + 4]? = some not_lit ∧ (FullMem c st1 ⋆ R) mj) ?_ ?_
            · rintro _ ⟨other, ⟨⟩⟩ mj ⟨st1, hpi1, hoom1, hct1, halen1, hcr_ref1, hng1, hcsz1,
                har3, har4, hmj⟩
              have haren1 := hpi1.len.core_ok.arena_len_arr
              have halen1_le := hpi1.len.core_ok.arena_len_le
              have hvals1 := hpi1.len.core_ok.vals_len
              have hwstk1 := hpi1.len.core_ok.wstk_len_arr
              have hwvec1 := hpi1.len.core_ok.wvec_len; have hcv1_eq := hpi1.cur_vars_eq
              have hnot_st1 : not_lit.toNat < 2 * st1.core.cur_vars := hcv1_eq.symm ▸ hnot_lt
              have hother_mem : other.toNat ∈ fullArenaClauseLitsCore st1.core cref.toNat := by
                refine (mem_fullArenaClauseLitsCore_iff (by omega)).mpr ⟨0, by omega, ?_⟩
                exact congrArg BitVec.toNat (Option.some.inj
                  ((List.getElem?_eq_getElem (by omega)).symm.trans har3))
              have hother_lt : other.toNat < 2 * st1.core.cur_vars :=
                hpi1.nw.arena.lits_lt cref.toNat hcr_ref1 hng1 other.toNat hother_mem
              fp_head_steps
              · have hge : 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 ≤ other.toNat := hc
                rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
                  Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hge
                omega
              · -- `vals[other] > 0`: keep large watch with blocking lit `other & 0x7FFFFFFF`
                exact ih _ (off_v, p_v + (1 : BitVec 64) + (1 : BitVec 64), q_v + (2 : BitVec 64),
                    end_v, ()) m (by omega)
                  ⟨_, rfl, propLit_inv_keep_large hpi1 hpi1.sw hnot_st1 hq1_nat hq2_nat hp2_nat
                    (by omega) (by omega) (bv32_mask7f_flag0 other) hcr_lt hcr_ref1,
                    hoom1, hct1, hm⟩
              · -- `vals[other] ≤ 0`: call `full_find_repl(h, (u64)cref)`
                have hov_np : (0#32).slt ((st1.core.vals[other.toNat]'(by omega)).signExtend 32) =
                    false := hc
                try clear hc; try clear hc
                c0_call hFind
                refine ⟨c, st1, R, rfl, hpi1.len, by rw [hcr64]; omega,
                  by change 3 ≤ fullArenaClauseSizeCore st1.core _; rw [hcr64]; omega,
                  by change _ + fullArenaClauseSizeCore st1.core _ ≤ _; rw [hcr64]; omega,
                  hmj, ?_, ?_⟩
                · -- Case B2: `full_find_repl` returned `0xFFFFFFFFULL` (no replacement)
                  intro hfind_bad
                  have hunit := propLit_hunit hpi1.nw hcr_ref1 hng1 (by omega) har3 har4
                    hpi1.not_f hfind_bad
                  fp_head_steps
                  · -- `(u64)cref == ignore_ref`: keep watch & continue!
                    exact ih _ (off_v, p_v + (1 : BitVec 64) + (1 : BitVec 64),
                        q_v + (2 : BitVec 64), end_v, ()) m (by omega)
                      ⟨_, rfl, propLit_inv_keep_large hpi1 hpi1.sw hnot_st1 hq1_nat hq2_nat
                        hp2_nat (by omega) (by omega) (bv32_mask7f_flag0 other) hcr_lt hcr_ref1,
                        hoom1, hct1, hm⟩
                  · -- `(u64)cref ≠ ignore_ref` and `ov < 0`: large clause conflict & break
                    have hne_ign : cref.setWidth 64 ≠ ignore_ref := by assumption
                    have hov_f := propLit_vals_neg hpi1.nw hother_lt (by omega) hc
                    have ⟨hpi_c, hcf_c⟩ := propLit_large_confl hpi1 hnot_st1 hq_le hq1_nat hq2_nat
                      hp2_nat hcr_lt hcr_ref1 hng1 hne_ign hov_f hunit
                    exact hB (off_v, p_v + (1 : BitVec 64) + (1 : BitVec 64),
                      q_v + (2 : BitVec 64), end_v, true, ()) m
                      ⟨_, hpi_c, by simp, fun _ => hcf_c, hm⟩
                  · -- `(u64)cref ≠ ignore_ref`, `ov == 0`: `full_assign_level` + `full_assign_lvl`
                    have hov_un := propLit_vals_un hpi1.nw hother_lt (by omega) hov_np hc
                    have hsw2 := hpi1.sw.write_large hnot_st1 hq_le (by omega) (by omega)
                      (bv32_mask7f_flag0 other) hcr_lt hcr_ref1
                    let st2 : FullState :=
                      { st1 with core :=
                        { st1.core with
                          wstk := (st1.core.wstk.set q_v.toNat (other &&& 0x7FFFFFFF#32)).set
                            (q_v + (1 : BitVec 64)).toNat cref } }
                    have hlen2 : st2.LengthsOk c :=
                      ⟨{ hpi1.len.core_ok with wstk_len_arr := by simp [st2, hwstk1] },
                       hpi1.len.scratch_ok⟩
                    have hnw2 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st2.core) :=
                      fullWitnessInv_nw_congr hlen2.core_ok.cur_vars_le hpi1.nw
                        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                    c0_call hAssignLevel
                    refine ⟨c, st2, R, rfl, hlen2, by dsimp [st2]; omega,
                      by change _ + fullArenaClauseSizeCore st1.core _ ≤ st1.core.arena_len; omega,
                      fun l hl _ => by
                        have hlt : l < 2 * st2.core.cur_vars :=
                          hnw2.arena.lits_lt cref.toNat hcr_ref1 hng1 l hl
                        have hcv2 : st2.core.cur_vars ≤ c.max_vars := hlen2.core_ok.cur_vars_le
                        omega,
                      hm, fun alvl hmax_ge hmax_att => ?_⟩
                    have hte_lt : st2.core.trail_end < st2.core.cur_vars :=
                      hnw2.trail_end_lt_of_unassigned hother_lt hov_un
                    have hst2_te : st2.core.trail_end = st1.core.trail_end := rfl
                    have hst2_cv : st2.core.cur_vars = st1.core.cur_vars := rfl
                    have hcv1_le : st1.core.cur_vars ≤ c.max_vars := hpi1.len.core_ok.cur_vars_le
                    have hng_guard : ¬ (st2.core.cur_vars ≤ other.toNat / 2 ∨
                        c.max_vars ≤ st2.core.trail_end ∨
                        st2.core.vals[other.toNat]?.getD 0#8 ≠ 0#8) := by
                      change ¬ (st1.core.cur_vars ≤ other.toNat / 2 ∨
                        c.max_vars ≤ st1.core.trail_end ∨
                        st1.core.vals[other.toNat]?.getD 0#8 ≠ 0#8)
                      simp only [hov_un, ne_eq, not_true_eq_false, or_false]; omega
                    fp_head_steps
                    c0_call hAssignLvl
                    refine ⟨c, st2, R, rfl, hlen2, hm, ?_⟩
                    simp only [hng_guard, ↓reduceIte]
                    intro flags' unas' unfl' phases' m_as hfl_len hph_len hm_as
                    let st3 : FullState :=
                      { core :=
                          { st2.core with
                            vals := (st2.core.vals.set other.toNat 1#8).set
                              (other.toNat ^^^ 1) 0xFF#8
                            flags := flags', lvl := st2.core.lvl.set (other.toNat / 2) alvl
                            rsns := st2.core.rsns.set (other.toNat / 2)
                              (if alvl = 0#32 then 0xFFFFFFFF#32 else cref)
                            trl := st2.core.trl.set st2.core.trail_end other
                            trail_pos := st2.core.trail_pos.set (other.toNat / 2)
                              (BitVec.ofNat 32 st2.core.trail_end)
                            trail_end := st2.core.trail_end + 1
                            unassigned := unas', unflushed := unfl' }
                        scratch := { st2.scratch with phases := phases' } }
                    have hlen3 : st3.LengthsOk c :=
                      ⟨{ hlen2.core_ok with
                          vals_len := by simp [st3, st2, hvals1], flags_len := hfl_len,
                          lvl_len := by simp [st3, st2, hlen2.core_ok.lvl_len],
                          rsns_len := by simp [st3, st2, hlen2.core_ok.rsns_len],
                          trl_len := by simp [st3, st2, hlen2.core_ok.trl_len],
                          trail_pos_len := by simp [st3, st2, hlen2.core_ok.trail_pos_len],
                          trail_end_le := by dsimp [st3]; omega,
                          propagated_le := by
                            have := hlen2.core_ok.propagated_le; dsimp [st3]; omega },
                       { hlen2.scratch_ok with phases_len := hph_len }⟩
                    have ⟨hnw3, hnot_f3, htr23⟩ := full_large_assign_nw_step hlen2.core_ok hnw2
                      hcr_lt hcr_ref1 hng1 hother_lt hov_un hnot_st1 hpi1.not_f hother_mem hunit
                      hmax_ge hmax_att (flags' := flags') (unas' := unas') (unfl' := unfl')
                    fp_head_steps
                    refine ih _ (off_v, p_v + (1 : BitVec 64) + (1 : BitVec 64),
                      q_v + (2 : BitVec 64), end_v, ()) m_as (by omega)
                      ⟨st3, rfl, ?_, hoom1, hct1, hm_as⟩
                    exact
                      { len := hlen3, nw := hnw3
                        sw := by
                          rw [hp2_nat, hq2_nat]
                          exact hsw2.with_nonwatch rfl rfl (by simp only [st3, st2, hq1_nat])
                            rfl rfl
                        ag := hpi1.ag.update (fun k => { k with
                          vals := st3.core.vals, flags := flags', lvl := st3.core.lvl,
                          rsns := st3.core.rsns, trl := st3.core.trl,
                          trail_pos := st3.core.trail_pos, trail_end := st3.core.trail_end,
                          unassigned := unas', unflushed := unfl', wstk := st2.core.wstk })
                        tr := (hpi1.tr.congr (k2 := st2.core) rfl rfl rfl).trans htr23
                        perm := hpi1.perm
                        sc_eq := by dsimp only [st3, st2]; rw [hpi1.sc_eq]
                        not_f := hnot_f3 }
                · -- Case B1: `full_find_repl` found replacement at `2 ≤ r < sz`
                  intro r m_f hr2 hr_lt hcand hm_f
                  change r < fullArenaClauseSizeCore st1.core (cref.setWidth 64).toNat at hr_lt
                  rw [hcr64] at hr_lt hcand hm_f
                  have hri_ne : BitVec.ofNat 64 r ≠ 0xFFFFFFFF#64 := fun h => by
                    have h1 : (BitVec.ofNat 64 r).toNat = r := bv64_ofNat_toNat (by omega)
                    have h2 : (0xFFFFFFFF#64).toNat = 0xFFFFFFFF := by decide
                    rw [h] at h1; omega
                  have hri_idx : (cref.setWidth 64 + (3 : BitVec 64) + BitVec.ofNat 64 r).toNat =
                      cref.toNat + 3 + r := by
                    rw [bv64_add_toNat (by rw [h3_idx, bv64_ofNat_toNat (by omega)]; omega),
                      h3_idx, bv64_ofNat_toNat (by omega)]
                  fp_head_steps
                  · let repl := (st1.core.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r))[(
                        cref.setWidth 64 + (3 : BitVec 64) + BitVec.ofNat 64 r).toNat]'(
                        by simp; omega)
                    let st3 : FullState :=
                      { st1 with core := { st1.core with
                          arena := ((st1.core.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r)).set
                            (cref.toNat + 4) repl).set (cref.toNat + 3 + r) not_lit } }
                    have ⟨hlen3, hnw3, hsw3, hperm13, hcr_ref3, hcsz3, hrepl_lt, hrepl_ne_not,
                        hw0_ne_ff, hcr_ne_ff, hm3⟩ := propLit_b1_swap (other := other) hpi1
                      (by omega) hcr_ref1 (by omega) har4 hr2 hr_lt h4_idx hri_idx rfl hcand hm
                    c0_call hPush
                    refine ⟨c, st3, R, rfl, hlen3, hsw3.layout, fun h => absurd h (by decide),
                      fun _ => ⟨hw0_ne_ff, hcr_ne_ff⟩, hm3,
                      fun pok wvec' wstk' wlen' wu' wsort' m_p hlen_p hlay_p hpres_o hpok_t
                        hpok_f hm_p => ?_⟩
                    let st4 : FullState :=
                      { core := { st3.core with
                          wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
                        scratch := { st3.scratch with wsort := wsort' } }
                    change (FullMem c st4 ⋆ R) m_p at hm_p
                    unfold fullWatchSize fullWatchOff at hpres_o hpok_t hpok_f
                    have hnw4 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st4.core) :=
                      fullWitnessInv_nw_congr hlen_p.core_ok.cur_vars_le hnw3
                        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                    have hwlen4_le : st4.core.wlen ≤ c.wcap := hlen_p.core_ok.wlen_le
                    have hwvec'_len : st4.core.wvec.length = 4 * c.max_vars :=
                      hlen_p.core_ok.wvec_len
                    have hwstk'_len : st4.core.wstk.length = c.wcap := hlen_p.core_ok.wstk_len_arr
                    have hst3_alen : st3.core.arena.length = c.arena_cap :=
                      hlen3.core_ok.arena_len_arr
                    have hst4_alen : st4.core.arena.length = c.arena_cap :=
                      hlen_p.core_ok.arena_len_arr
                    have ⟨hoff4_bd, hoff4_nat, hp4_nat, hq4_nat, hend4_nat, hq4_1, hq4_2,
                        hsw4'⟩ := propLit_b1_after_push (st3 := st3) (st4 := st4) hidx0 rfl hnot_st1
                      hlen_p hlay_p hsw3 rfl hrepl_lt hrepl_ne_not hcr_lt hcr_ref3 hp2_nat hq_le
                      hpres_o
                      (fun ht => by
                        obtain ⟨_, _, hsz, hpre, hw0, hw1⟩ := hpok_t ht
                        exact ⟨hsz, hpre, hw0, hw1 rfl⟩)
                      (fun hf => hpok_f hf hrepl_lt)
                    let off4_v : BitVec 64 := (st4.core.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64
                      <<< (1 : BitVec 64)).toNat]'(by omega)).setWidth 64
                    let q4_v := off4_v + (q_v - off_v)
                    have hoff4_bd' : fullWatchOffCore st4.core not_lit.toNat +
                        (end_v.toNat - off_v.toNat) ≤ st4.core.wlen := hoff4_bd
                    have hq4_nat_raw : ((st4.core.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<<
                        (1 : Nat)).toNat]'(by rw [bv64_shl1_u32_nat, bv32_xor_1]; omega)).setWidth
                        64 + (q_v - off_v)).toNat =
                        fullWatchOffCore st4.core not_lit.toNat + (q_v.toNat - off_v.toNat) :=
                      hq4_nat
                    have hq4_1_raw : ((st4.core.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<<
                        (1 : Nat)).toNat]'(by rw [bv64_shl1_u32_nat, bv32_xor_1]; omega)).setWidth
                        64 + (q_v - off_v) + (1 : BitVec 64)).toNat =
                        fullWatchOffCore st4.core not_lit.toNat + (q_v.toNat - off_v.toNat) + 1 :=
                      by change (q4_v + (1 : BitVec 64)).toNat = _; rw [hq4_1, hq4_nat]
                    have hag4 : AgreesExcept propLitCoreMask s.core st4.core :=
                      hpi1.ag.update (fun k => { k with
                        arena := st4.core.arena, wvec := wvec', wstk := wstk', wlen := wlen',
                        wusable := wu' })
                    have hperm4 : FullArenaPermEq s.core st4.core := hpi1.perm.trans hperm13
                    have hsc4 : st4.scratch = { s.scratch with
                        search_ticks := st4.scratch.search_ticks, wsort := st4.scratch.wsort,
                        phases := st4.scratch.phases } := by
                      dsimp only [st4, st3]; rw [hpi1.sc_eq]
                    dsimp (config := { zeta := false }) only
                    fp_head_steps
                    · -- `pok = true`: continue loop at relocated `(off4, p4, q4, end4)`
                      have hp4_o :
                          (off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v)).toNat =
                            fullWatchOffCore st4.core not_lit.toNat +
                              (p_v.toNat + 2 - off_v.toNat) := hp4_nat
                      have hend4_o : (off4_v + (end_v - off_v)).toNat =
                          fullWatchOffCore st4.core not_lit.toNat + (end_v.toNat - off_v.toNat) :=
                        hend4_nat
                      exact ih _ (off4_v,
                        off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v),
                        q4_v, off4_v + (end_v - off_v), ()) m_p
                        (by rw [hend4_o, hp4_o]
                            exact propLit_measure_lt (Nat.le_trans hpi1.sw.q_ge hq_le)
                              hpi1.sw.p_le_end)
                        ⟨st4, rfl, ⟨hlen_p, hnw4, hsw4', hag4, hpi1.tr.congr rfl rfl rfl, hperm4,
                          hsc4, hpi1.not_f⟩, hoom1, hct1, hm_p⟩
                    · -- `pok = false` (OOM): swap back, keep watch, set `oom = 1` & break
                      have hfit4 : cref.toNat + 3 + fullArenaClauseSizeCore st4.core cref.toNat ≤
                          st1.core.arena_len := by
                        change _ + fullArenaClauseSizeCore st3.core _ ≤ _; rw [hcsz3]; omega
                      have hr_lt4 : r < fullArenaClauseSizeCore st4.core cref.toNat := by
                        change r < fullArenaClauseSizeCore st3.core _; rw [hcsz3]; omega
                      have ⟨hpi6, hm6⟩ := propLit_b1_oom hpi1 hlen_p hnw4 hsw4' hperm4 rfl rfl hag4
                        (hpi1.tr.congr rfl rfl rfl) hsc4 hpi1.not_f hnot_st1 hq_le hcr_lt hcr_ref3
                        hflag hfit4 hr2 hr_lt4 h4_idx hri_idx hq4_nat hp4_nat hend4_nat hq4_1
                        hq4_2 hm
                      exact hB (off4_v, off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v),
                        q4_v + (2 : BitVec 64), off4_v + (end_v - off_v), true, ()) m
                        ⟨_, hpi6, by simp, fun _ => Or.inl (by show (1 : BitVec 64) ≠ 0#64; decide),
                          hm6⟩
                  · exact absurd (by assumption) hri_ne
                  · exact absurd (by assumption) hri_ne
                  · exact absurd (by assumption) hri_ne
            · intro J3 hJ3; fp_head_steps
              · let l1 := st.core.arena[(cref.setWidth 64 + (4 : BitVec 64)).toNat]'(by omega)
                have ⟨hpi1, href1, hng1, hcsz1, har3, har4, hm1⟩ := propLit_js3_swap hlen_t hpi.nw
                  hsw_drop hpi.ag hpi.tr hpi.perm hsc_t hpi.not_f hcr_ref hng_t hcsz3 hcr_fit
                  h3_idx h4_idx
                  (by change st.core.arena[cref.toNat + 3]'_ = not_lit
                      rw [← (by assumption :
                        st.core.arena[(cref.setWidth 64 + (3 : BitVec 64)).toNat]'(by omega) =
                          not_lit)]
                      congr 1; exact h3_idx.symm)
                  (by change st.core.arena[cref.toNat + 4]'_ = l1; dsimp only [l1]; congr 1
                      exact h4_idx.symm) hm
                exact hJ3 (l1, ()) m ⟨_, hpi1, hoom_st, hct_st, rfl, href1, hng1, hcsz1, har3,
                  har4, hm1⟩
              · exact ih _ (off_v, p_v + (1 : BitVec 64) + (1 : BitVec 64), q_v, end_v, ()) m
                  (by omega) ⟨st_t, rfl, ⟨hlen_t, hpi.nw, by rw [hp2_nat]; exact hsw_drop, hpi.ag,
                    hpi.tr, hpi.perm, hsc_t, hpi.not_f⟩, hoom_st, hct_st, hm⟩
              · let l0 := st.core.arena[(cref.setWidth 64 + (3 : BitVec 64)).toNat]'(by omega)
                have hl1_not : st.core.arena[(cref.setWidth 64 + (4 : BitVec 64)).toNat]'(
                    by omega) = not_lit := hc
                exact hJ3 (l0, ()) m ⟨st_t, ⟨hlen_t, hpi.nw, hsw_drop, hpi.ag,
                    hpi.tr, hpi.perm, hsc_t, hpi.not_f⟩,
                  hoom_st, hct_st, rfl, hcr_ref, hng_t, rfl,
                  by change st.core.arena[cref.toNat + 3]? = some l0
                     rw [← h3_idx]; exact List.getElem?_eq_getElem (by omega),
                  by change st.core.arena[cref.toNat + 4]? = some not_lit
                     rw [← hl1_not, ← h4_idx]; exact List.getElem?_eq_getElem (by omega), hm⟩
        · intro J2 hJ2; fp_head_steps
          · exact ih _ (off_v, p_v + (1 : BitVec 64) + (1 : BitVec 64), q_v + (2 : BitVec 64),
                end_v, ()) m (by omega)
              ⟨_, rfl, propLit_inv_keep_large hpi hsw_drop hnot_st hq1_nat hq2_nat hp2_nat
                (by omega) (by omega) hflag hcr_lt hcr_ref, hoom_st, hct_st, hm⟩
          · exact hJ2 () ml rfl
          · exact hJ2 () ml rfl
      · exact hB (off_v, p_v, q_v, end_v, false, ()) ml
          ⟨st, hpi, fun _ => ⟨hoom_st, hct_st⟩, by simp, hml⟩
    · intro _ L _ hL; fp_head_steps
      have hoff_bd := hwat0.layout.bounds not_lit.toNat hnot_lt
      have hwlen_le := hlen0.core_ok.wlen_le
      have hoff_nat : ((s.core.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<<
          (1 : BitVec 64)).toNat]'(by omega)).setWidth 64).toNat =
          fullWatchOffCore s.core not_lit.toNat := by
        rw [bv_c0_zext32_64, hoff0_eq]
      have hsz_nat : ((s.core.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
          (1 : BitVec 64)).toNat]'(by omega)).setWidth 64).toNat =
          fullWatchSizeCore s.core not_lit.toNat := by
        rw [bv_c0_zext32_64, hsz0_eq]
      have hend_nat : ((s.core.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<<
            (1 : BitVec 64)).toNat]'(by omega)).setWidth 64 +
          (s.core.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
            (1 : BitVec 64)).toNat]'(by omega)).setWidth 64).toNat =
          fullWatchOffCore s.core not_lit.toNat + fullWatchSizeCore s.core not_lit.toNat := by
        rw [bv64_add_toNat (by omega), hoff_nat, hsz_nat]
      have hoff_g : ∀ h, ((s.core.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<<
          (1 : Nat)).toNat]'h).setWidth 64).toNat = fullWatchOffCore s.core not_lit.toNat :=
        fun _ => hoff_nat
      have hend_g : ∀ h1 h2, ((s.core.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<<
            (1 : Nat)).toNat]'h1).setWidth 64 +
          (s.core.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)) +
            (1 : BitVec 64)).toNat]'h2).setWidth 64).toNat =
          fullWatchOffCore s.core not_lit.toNat + fullWatchSizeCore s.core not_lit.toNat :=
        fun _ _ => hend_nat
      refine hL _ _ m ⟨st0, rfl, ?_, hoom0, rfl, hm⟩; rw [hend_g, hoff_g]; exact hpi0

end LeanQbe.T.Examples.Kissat.Full
