module

public import LeanQbe.T.Examples.Kissat.CorePlusSpec
public import LeanQbe.T.Logic.C0Step
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat `CorePlus` Mark-Clearing, `min_mark`, and DFS Frame Infrastructure

Provides specialized `CorePlusMem` `c0_load`/`c0_store` adapters, the fast `cp_steps` tactic,
and proofs/invariants for the first two minimization functions in `CorePlus.lean`:
1. `kissat_clear_marks` (`corePlusClearMarksSpec`, `kissat_clear_marks_wp`).
2. `kissat_min_mark` (`corePlusMinMarkSpec`, `kissat_min_mark_wp`).
3. `MinMark` and `MinFrameOk` infrastructure shared with `CorePlusMinimizeLemmas`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.CorePlus

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat

/-! ## 1. Specialized `CorePlusMem` `c0_load`/`c0_store` adapters, `MinTactics`, and `cp_steps` -/

theorem bv64_toNat_one : (1 : BitVec 64).toNat = 1 := rfl
theorem bv64_toNat_zero : (0 : BitVec 64).toNat = 0 := rfl
theorem bv64_toNat_4 : (4 : BitVec 64).toNat = 4 := rfl
theorem bv64_toNat_64 : (64 : BitVec 64).toNat = 64 := rfl
theorem bv32_toNat_one : (1 : BitVec 32).toNat = 1 := rfl
theorem bv32_toNat_zero : (0 : BitVec 32).toNat = 0 := rfl
theorem bv8_toNat_zero : (0 : BitVec 8).toNat = 0 := rfl

theorem bv64_shl_one (x : BitVec 64) :
    (x <<< (1 : BitVec 64)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft]; omega

theorem bv64_shl_nat1 (x : BitVec 64) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft]; omega

theorem bv64_shl_ofNat1 (x : BitVec 64) :
    (x <<< BitVec.ofNat 64 1).toNat = (2 * x.toNat) % 2 ^ 64 :=
  bv64_shl_one x

theorem min_bv32_mod64 (x : BitVec 32) : x.toNat % 2 ^ 64 = x.toNat :=
  Nat.mod_eq_of_lt (lt_trans x.isLt (by decide))

theorem bv_c0_zext32_zero_eq (b : BitVec 8) :
    (b.setWidth 32 = (0 : BitVec 32)) = (b = 0#8) := propext (bv8_zext32_eq_zero b)

abbrev withMinFields (s : CorePlusState) (mrk' : List (BitVec 8))
    (mstk' mclr' : List (BitVec 32)) (mcl' : Nat) (mcf' : BitVec 64) : CorePlusState :=
  { s with
    mrk := mrk', min_stk := mstk', min_clr := mclr',
    min_clr_len := mcl', min_clr_full := mcf' }

theorem withMinFields_mrk (s : CorePlusState) a b c d e : (withMinFields s a b c d e).mrk = a := rfl
theorem withMinFields_min_stk (s : CorePlusState) a b c d e :
    (withMinFields s a b c d e).min_stk = b := rfl
theorem withMinFields_min_clr (s : CorePlusState) a b c d e :
    (withMinFields s a b c d e).min_clr = c := rfl
theorem withMinFields_min_clr_len (s : CorePlusState) a b c d e :
    (withMinFields s a b c d e).min_clr_len = d := rfl
theorem withMinFields_min_clr_full (s : CorePlusState) a b c d e :
    (withMinFields s a b c d e).min_clr_full = e := rfl
theorem withMinFields_tmp (s : CorePlusState) a b c d e :
    (withMinFields s a b c d e).tmp = s.tmp := rfl

theorem withMinFields_upd (s : CorePlusState) a b c d e a' c' d' e' :
    { withMinFields s a b c d e with
      mrk := a', min_clr := c', min_clr_len := d', min_clr_full := e' } =
      withMinFields s a' b c' d' e' := rfl

abbrev withMinTmp (s : CorePlusState) (tmp' : List (BitVec 32))
    (mrk' : List (BitVec 8)) (mstk' mclr' : List (BitVec 32))
    (mcl' : Nat) (mcf' : BitVec 64) : CorePlusState :=
  { s with
    tmp := tmp', mrk := mrk', min_stk := mstk', min_clr := mclr',
    min_clr_len := mcl', min_clr_full := mcf' }

theorem withMinTmp_tmp (s : CorePlusState) t a b c d e : (withMinTmp s t a b c d e).tmp = t := rfl
theorem withMinTmp_mrk (s : CorePlusState) t a b c d e : (withMinTmp s t a b c d e).mrk = a := rfl
theorem withMinTmp_min_stk (s : CorePlusState) t a b c d e :
    (withMinTmp s t a b c d e).min_stk = b := rfl
theorem withMinTmp_min_clr (s : CorePlusState) t a b c d e :
    (withMinTmp s t a b c d e).min_clr = c := rfl
theorem withMinTmp_min_clr_len (s : CorePlusState) t a b c d e :
    (withMinTmp s t a b c d e).min_clr_len = d := rfl
theorem withMinTmp_min_clr_full (s : CorePlusState) t a b c d e :
    (withMinTmp s t a b c d e).min_clr_full = e := rfl

theorem withMinTmp_upd (s : CorePlusState) t a b c d e a' b' c' d' e' :
    { withMinTmp s t a b c d e with
      mrk := a', min_stk := b', min_clr := c', min_clr_len := d', min_clr_full := e' } =
      withMinTmp s t a' b' c' d' e' := rfl

section CpMemAdapters
variable {c : CorePlusCfg} {s : CorePlusState} {R : Mem 64 → Prop} {m : Mem 64}

private theorem eq_mul16_toNat (i : BitVec 64) :
    i * (16 : BitVec 64) = BitVec.ofNat 64 (4 * (4 * i.toNat)) := by
  rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, c0_mul_ofNat]; congr 1; omega

theorem cp_load_tmp0 (hm : (CorePlusMem c s ⋆ R) m) (hi : 0 < s.tmp.length) :
    loadVal m i32 c.pTmp = some (s.tmp[0]'hi) := by
  have h := load_arena_tmp hi hm; simpa using h

theorem cp_store_tmp0 (v : BitVec 32) (hm : (CorePlusMem c s ⋆ R) m) (hi : 0 < s.tmp.length) :
    storeOk m i32 c.pTmp ∧ (CorePlusMem c { s with tmp := s.tmp.set 0 v } ⋆ R)
      (storeMem m i32 c.pTmp v) := by
  have h := store_arena_tmp v hi hm; simpa using h

theorem cp_store_min_stk0 (v : BitVec 32) (hm : (CorePlusMem c s ⋆ R) m)
    (hi : 0 < s.min_stk.length) :
    storeOk m i32 c.pMinStk ∧ (CorePlusMem c { s with min_stk := s.min_stk.set 0 v } ⋆ R)
      (storeMem m i32 c.pMinStk v) := by
  have h := store_arena_min_stk v hi hm; simpa using h

theorem cp_store_min_stk1 (v : BitVec 32) (hm : (CorePlusMem c s ⋆ R) m)
    (hi : 1 < s.min_stk.length) :
    storeOk m i32 (c.pMinStk + 4) ∧ (CorePlusMem c { s with min_stk := s.min_stk.set 1 v } ⋆ R)
      (storeMem m i32 (c.pMinStk + 4) v) := by
  have h := store_arena_min_stk v hi hm; simpa using h

theorem cp_store_min_stk1_nat (v : BitVec 32) (hm : (CorePlusMem c s ⋆ R) m)
    (hi : 1 < s.min_stk.length) :
    storeOk m i32 (c.pMinStk + BitVec.ofNat 64 4) ∧
      (CorePlusMem c { s with min_stk := s.min_stk.set 1 v } ⋆ R)
        (storeMem m i32 (c.pMinStk + BitVec.ofNat 64 4) v) :=
  cp_store_min_stk1 v hm hi

theorem cp_load_cls_off {cid : BitVec 64} (hm : (CorePlusMem c s ⋆ R) m)
    (hi : 4 * cid.toNat < s.cls.length) :
    loadVal m i32 (c.pClauses + cid * 16) = some (s.cls[4 * cid.toNat]'hi) := by
  rw [eq_mul16_toNat]; exact load_arena_cls hi hm

theorem cp_load_cls_sz {cid : BitVec 64} (hm : (CorePlusMem c s ⋆ R) m)
    (hi : 4 * cid.toNat + 1 < s.cls.length) :
    loadVal m i32 (c.pClauses + cid * 16 + 4) = some (s.cls[4 * cid.toNat + 1]'hi) := by
  rw [eq_mul16_toNat, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ptr_add_ofNat,
    show 4 * (4 * cid.toNat) + 4 = 4 * (4 * cid.toNat + 1) by omega]
  exact load_arena_cls hi hm

theorem cp_load_lpool2 {off pos : BitVec 64} (hm : (CorePlusMem c s ⋆ R) m)
    (ho : off.toNat + pos.toNat < s.lpool.length) (_hov : off.toNat + pos.toNat < 2 ^ 64) :
    loadVal m i32 (c.pLpool + off * 4 + pos * 4) =
      some (s.lpool[off.toNat + pos.toNat]'ho) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat off, c0_mul_ofNat pos,
    ptr_add_ofNat, ← Nat.mul_add]
  exact load_arena_lpool ho hm

end CpMemAdapters

namespace MinTactics
open Lean Meta Elab Tactic

attribute [scoped bv_c0] bv32_zext64_eq bv32_lshr_1 bv32_xor_1 bv32_and_1 bv8_zext32_eq_zero
  BitVec.toNat_ofNat List.length_set
  bv64_toNat_one bv64_toNat_zero bv64_toNat_4 bv64_toNat_64
  bv32_toNat_one bv32_toNat_zero bv8_toNat_zero
  bv64_shl_one bv64_shl_nat1 bv64_shl_ofNat1 bv_c0_zext32_zero_eq
  withMinFields_mrk withMinFields_min_stk withMinFields_min_clr withMinFields_min_clr_len
  withMinFields_min_clr_full withMinFields_tmp withMinTmp_tmp withMinTmp_mrk
  withMinTmp_min_stk withMinTmp_min_clr withMinTmp_min_clr_len withMinTmp_min_clr_full

attribute [scoped c0_load] cp_load_tmp0 cp_load_cls_off cp_load_cls_sz cp_load_lpool2
attribute [scoped c0_store] cp_store_tmp0 cp_store_min_stk0 cp_store_min_stk1 cp_store_min_stk1_nat

private meta def mkCpSimp : TacticM (Simp.Context × Simp.Methods) := do
  let stx ← `(tactic| simp only [
    LeanQbe.T.op1_eq_mk, LeanQbe.T.op2_eq_mk, LeanQbe.T.op3_eq_mk,
    LeanQbe.T.wp_let_copy_eq, LeanQbe.T.wp_let_add_eq, LeanQbe.T.wp_let_sub_eq,
    LeanQbe.T.wp_let_mul_eq, LeanQbe.T.wp_let_neg_eq, LeanQbe.T.wp_let_and_eq,
    LeanQbe.T.wp_let_or_eq, LeanQbe.T.wp_let_xor_eq, LeanQbe.T.wp_let_not_eq,
    LeanQbe.T.wp_let_shl_eq, LeanQbe.T.wp_let_lshr_eq, LeanQbe.T.wp_let_ashr_eq,
    LeanQbe.T.wp_let_rotl_eq, LeanQbe.T.wp_let_rotr_eq,
    LeanQbe.T.wp_let_clz_eq, LeanQbe.T.wp_let_cls_eq, LeanQbe.T.wp_let_rbit_eq,
    LeanQbe.T.wp_let_ctz_eq, LeanQbe.T.wp_let_popcnt_eq,
    LeanQbe.T.wp_let_cmp_eq, LeanQbe.T.wp_let_select_eq, LeanQbe.T.wp_let_zext_eq,
    LeanQbe.T.wp_let_sext_eq, LeanQbe.T.wp_let_trunc_eq, LeanQbe.T.wp_let_ofBool_eq,
    LeanQbe.T.wp_let_udiv0_eq, LeanQbe.T.wp_let_sdiv0_eq, LeanQbe.T.wp_let_mkpair_eq,
    LeanQbe.T.wp_let_unpair_eq, LeanQbe.T.wp_let_bitcast_eq,
    LeanQbe.T.wp_let_udiv_eq, LeanQbe.T.wp_let_urem_eq,
    LeanQbe.T.wp_jump, LeanQbe.T.wp_ret, LeanQbe.T.wp_exit,
    LeanQbe.T.OpCode.eq, LeanQbe.T.OpCode.ne, LeanQbe.T.OpCode.ult, LeanQbe.T.OpCode.ule,
    LeanQbe.T.OpCode.ugt, LeanQbe.T.OpCode.uge, LeanQbe.T.OpCode.slt, LeanQbe.T.OpCode.sle,
    LeanQbe.T.OpCode.sgt, LeanQbe.T.OpCode.sge,
    LeanQbe.T.vals_nil, LeanQbe.T.vals_cons, LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
    LeanQbe.T.Blocks.get_here, LeanQbe.T.Blocks.get_there,
    LeanQbe.T.Ty.hasFloat_vec, LeanQbe.T.Ty.hasFloat, LeanQbe.T.Ty.isFloatTree,
    LeanQbe.T.evalBits_eq_beq, LeanQbe.T.evalBits_ne_bne, LeanQbe.T.evalBits_ult_eq,
    LeanQbe.T.evalBits_ule_eq, LeanQbe.T.evalBits_ugt_eq, LeanQbe.T.evalBits_uge_eq,
    LeanQbe.T.evalBits_slt_eq, LeanQbe.T.evalBits_sle_eq, LeanQbe.T.evalBits_sgt_eq,
    LeanQbe.T.evalBits_sge_eq, LeanQbe.T.evalBool_eq_beq, LeanQbe.T.evalBool_ne_bne,
    LeanQbe.T.lift1, LeanQbe.T.lift2, LeanQbe.T.lift3, LeanQbe.T.liftCmp,
    LeanQbe.T.shl_three, cast_eq, ite_self, ite_true, ite_false,
    Bool.false_eq_true, Bool.true_eq_false, BitVec.add_zero, BitVec.zero_add,
    BitVec.reduceToNat, Nat.reduceMod, Nat.reduceLeDiff, true_and, and_true,
    BitVec.reduceSignExtend, BitVec.reduceSetWidth, BitVec.reduceAdd, BitVec.reduceMul])
  let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := false)
  let m0 := Simp.mkDefaultMethodsCore simprocs
  let methods : Simp.Methods := { m0 with
    pre := fun sub => do
      if sub.isAppOf ``LeanQbe.T.Expr.group || sub.isAppOf ``LeanQbe.T.Expr.load ||
         sub.isAppOf ``LeanQbe.T.Expr.store || sub.isAppOf ``LeanQbe.T.Expr.jnz ||
         sub.isAppOf ``LeanQbe.T.Expr.call then
        return .done { expr := sub }
      m0.pre sub }
  return (ctx, methods)

private meta def cpLetSimpWith (ctx : Simp.Context) (methods : Simp.Methods) : TacticM Unit :=
  withMainContext do
    let g ← getMainGoal
    let r := (← Simp.main (← instantiateMVars (← g.getType)) ctx (methods := methods)).1
    replaceMainGoal [← g.replaceTargetEq r.expr (← r.getProof)]

/-- Unfold straight-line `wp` skipping nested `Expr` subtrees. -/
meta def cpLetSimp : TacticM Unit := do
  let (ctx, methods) ← mkCpSimp; cpLetSimpWith ctx methods

scoped elab "cp_let_simp" : tactic => cpLetSimp

scoped macro "cp_call" h:term : tactic =>
  `(tactic| (refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_); try cp_let_simp))

private meta def cpSimpHypWith (ctx : Simp.Context) (methods : Simp.Methods)
    (name : Name) : TacticM Unit := withMainContext do
  let some d := (← getLCtx).findFromUserName? name | return
  let r := (← Simp.main (← instantiateMVars d.type) ctx (methods := methods)).1
  let g ← getMainGoal
  let res ← g.replaceLocalDecl d.fvarId r.expr (← r.getProof)
  replaceMainGoal [res.mvarId]

private meta def cpIsJoin (bodies : Lean.Expr) : Bool :=
  match bodies with | .lam _ _ b _ => !b.hasLooseBVars | _ => false

private meta def cpFindJoinHyp (J : FVarId) : TacticM (Option Lean.Expr) := withMainContext do
  for d in (← getLCtx).decls.toArray.reverse do
    let some d := d | continue
    let ok ← forallTelescopeReducing d.type fun xs concl => do
      if xs.size < 1 then return false
      return concl.getAppFn.isFVarOf J && (← inferType xs[xs.size - 1]!).isAppOf ``LeanQbe.T.wp
    if ok then return some d.toExpr
  return none

private meta def cpClearStale (m0 : Lean.Expr) : TacticM Unit := withMainContext do
  let .fvar mId := m0 | return
  for d in (← getLCtx).decls.toArray.reverse do
    let some d := d | continue
    let t ← instantiateMVars d.type
    if t.isAppOf ``Std.ExtHashMap.sep && t.appArg! == m0 then
      try liftMetaTactic1 fun g => some <$> g.clear d.fvarId catch _ => pure ()
  try liftMetaTactic1 fun g => some <$> g.clear mId catch _ => pure ()

private meta def cpCloseWith (g : MVarId) (tac : TSyntax `tactic) : TacticM Bool := do
  if ← g.isAssigned then return true
  let s ← saveState
  try
    setGoals [g]; evalTactic tac
    if (← getUnsolvedGoals).isEmpty then return true
    s.restore; return false
  catch _ => s.restore; return false

scoped macro "cp_bound1" : tactic => `(tactic| first | assumption | rfl | decide | omega)
scoped macro "cp_bound2" : tactic => `(tactic| first
  | assumption | rfl | omega
  | (simp only [bv_c0]; omega)
  | (simp only [bv_c0, Nat.reducePow, Nat.reduceMod]; omega)
  | (simp only [bv_c0, Nat.reducePow, Nat.reduceMod] at *; omega))

private meta def cpTryMemLemma (ctx : Simp.Context) (methods : Simp.Methods)
    (g : MVarId) (nm : Name) : TacticM Bool := do
  let s ← saveState
  try
    let gs ← withReducible <| g.apply (← mkConstWithFreshMVarLevels nm)
    for g' in gs do
      let ty ← instantiateMVars (← g'.getType)
      if ty.isAppOf ``Std.ExtHashMap.sep then
        unless ← withReducible (cpCloseWith g' (← `(tactic| c0_frame))) do throwError "frame"
    for g' in gs do
      if ← g'.isAssigned then continue
      if ← isProp (← g'.getType) then
        if !(← cpCloseWith g' (← `(tactic| cp_bound1))) then
          let ok2 ← do
            let s2 ← saveState
            try
              setGoals [g']; try cpLetSimpWith ctx methods catch _ => pure ()
              let g'' ← getMainGoal
              let r := (← Simp.main (← instantiateMVars (← g''.getType)) ctx (methods := methods)).1
              replaceMainGoal [← g''.replaceTargetEq r.expr (← r.getProof)]
              evalTactic (← `(tactic| cp_bound2))
              if (← getUnsolvedGoals).isEmpty then pure true
              else do s2.restore; pure false
            catch _ => s2.restore; pure false
          unless ok2 do throwError "side"
    for g' in gs do
      unless ← g'.isAssigned do throwError "unassigned"
    return true
  catch _ => s.restore; return false

private meta def cpMemSolve (ctx : Simp.Context) (methods : Simp.Methods)
    (isLoad : Bool) (g : MVarId) : TacticM Unit := do
  setGoals [g]
  try cpLetSimpWith ctx methods catch _ => pure ()
  let g ← getMainGoal
  let env ← getEnv
  for nm in C0Step.c0MemLemmas env isLoad ``CorePlusMem do
    if ← cpTryMemLemma ctx methods g nm then return
  throwError "cpMemSolve failed on: {indentExpr (← g.getType)}"

/-- Single symbolic-execution step that skips unstepped nested `Expr` blocks. -/
meta def cpStepOnceWith (ctx : Simp.Context) (methods : Simp.Methods)
    (pruneDead : Bool) : TacticM Bool := withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let g ← if ty.isMData then g.change ty.consumeMData (checkDefEq := false) else pure g
  setGoals [g]
  let ty := (← instantiateMVars (← g.getType)).headBeta
  if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
    let e := (ty.getArg! 4).headBeta
    match e.getAppFn.constName? with
    | some ``LeanQbe.T.Expr.let_ | some ``LeanQbe.T.Expr.jump | some ``LeanQbe.T.Expr.ret
    | some ``LeanQbe.T.Blocks.get =>
      cpLetSimpWith ctx methods; return true
    | some ``LeanQbe.T.Expr.load =>
      let [hl, hk] := (← g.apply (← mkConstWithFreshMVarLevels ``LeanQbe.T.wp_load_of)).take 2
        | return false
      cpMemSolve ctx methods true hl
      setGoals [hk]; try cpLetSimpWith ctx methods catch _ => pure ()
      return true
    | some ``LeanQbe.T.Expr.store =>
      let m0 := ty.getArg! 5
      let [hs, hk] := (← g.apply (← mkConstWithFreshMVarLevels ``LeanQbe.T.wp_store_sep)).take 2
        | return false
      cpMemSolve ctx methods false hs; setGoals [hk]
      let mId := mkIdent `m; let hmId := mkIdent `hm
      evalTactic (← `(tactic| intro $mId:ident $hmId:ident))
      evalTactic (← `(tactic| try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
        Std.ExtHashMap.sep_emp] at $hmId:ident))
      cpClearStale m0; try cpLetSimpWith ctx methods catch _ => pure ()
      return true
    | some ``LeanQbe.T.Expr.jnz =>
      let hc := mkIdent `hc
      evalTactic (← `(tactic|
        refine LeanQbe.T.wp_jnz_of (fun $hc:ident => ?_) (fun $hc:ident => ?_)))
      let mut out : Array MVarId := #[]
      for g' in ← getUnsolvedGoals do
        if ← g'.isAssigned then continue
        setGoals [g']; cpSimpHypWith ctx methods `hc
        evalTactic (← `(tactic| c0_cond $hc))
        if pruneDead then
          evalTactic (← `(tactic| try (exfalso; c0_bound)))
        for g'' in ← getUnsolvedGoals do
          if ← g''.isAssigned then continue
          setGoals [g'']; try cpLetSimpWith ctx methods catch _ => pure ()
          out := out ++ (← getUnsolvedGoals)
      setGoals out.toList; return true
    | some ``LeanQbe.T.Expr.group =>
      if e.getAppNumArgs == 6 && cpIsJoin (e.getArg! 4) then
        let J := mkIdent `J; let hJ := mkIdent `hJ
        evalTactic (← `(tactic| refine LeanQbe.T.wp_unroll_group fun $J:ident $hJ:ident => ?_))
        try cpLetSimpWith ctx methods catch _ => pure ()
        return true
      return false
    | _ => return false
  if let .fvar J := ty.getAppFn then
    if let some h ← cpFindJoinHyp J then
      setGoals (← g.apply h); try cpLetSimpWith ctx methods catch _ => pure ()
      return true
  return false

private meta partial def cpStepsRec (ctx : Simp.Context) (methods : Simp.Methods)
    (pruneDead : Bool) (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then return
  let mut out : Array MVarId := #[]
  for g in ← getUnsolvedGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    if ← cpStepOnceWith ctx methods pruneDead then
      cpStepsRec ctx methods pruneDead (fuel - 1)
    out := out ++ (← getUnsolvedGoals)
  setGoals out.toList

/-- Symbolic execution for `CorePlus` C0 bodies (cached simplifier; fast without dead-branch
`omega` guessing). -/
scoped elab "cp_steps" : tactic => do
  let (ctx, methods) ← mkCpSimp; cpStepsRec ctx methods false 10000

/-- Symbolic execution for `CorePlus` C0 bodies with dead `jnz` pruning via `c0_bound`. -/
scoped elab "cp_steps!" : tactic => do
  let (ctx, methods) ← mkCpSimp; cpStepsRec ctx methods true 10000

end MinTactics

section
open scoped MinTactics

/-! ## 2. Small `mrk` and bitvector helpers -/

theorem bv_get_eq {α : Type _} {xs : List α} {i j : Nat} {d : α}
    (hi : i < xs.length) (h : i = j) : xs[i]'hi = xs[j]?.getD d := by
  subst h; rw [List.getElem?_eq_getElem hi, Option.getD_some]

theorem bv32_shr1_zext64 (x : BitVec 32) : ((x >>> 1).setWidth 64).toNat = x.toNat / 2 := by
  have hx := x.isLt
  rw [bv32_zext64_eq, bv32_lshr_1, bv64_ofNat_toNat (by omega)]

theorem mrk_set_zero_pres {mrk : List (BitVec 8)} {v w : Nat}
    (hw : mrk[w]?.getD 0#8 = 0#8) : (mrk.set v 0#8)[w]?.getD 0#8 = 0#8 := by
  by_cases hwe : w = v
  · subst hwe
    by_cases hlt : w < mrk.length
    · rw [List.getElem?_set_self hlt]; rfl
    · rw [List.getElem?_eq_none (by simp; omega)]; rfl
  · rw [List.getElem?_set_ne (Ne.symm hwe)]; exact hw

theorem mrk_set_zero_idx {mrk : List (BitVec 8)} (f : Nat → Nat) (i : Nat) {k v : Nat}
    (hl : v < mrk.length) (hpres : k ≠ i → mrk[f k]?.getD 0#8 = 0#8) (heq : k = i → f k = v) :
    (mrk.set v 0#8)[f k]?.getD 0#8 = 0#8 := by
  by_cases h : k = i
  · rw [heq h, List.getElem?_set_self hl]; rfl
  · exact mrk_set_zero_pres (hpres h)

/-! ## 3. `kissat_clear_marks` (`corePlusClearMarksSpec`) -/

private structure ClearTmpInv (c : CorePlusCfg) (s : CorePlusState) (i : Nat)
    (mrk : List (BitVec 8)) : Prop where
  hi1 : 1 ≤ i
  hile : i ≤ max 1 s.tmp_len
  len : mrk.length = c.mv
  pres : ∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk[v]?.getD 0#8 = 0#8
  clr : ∀ k, 1 ≤ k → k < i → k < s.tmp_len → (s.tmp[k]?.getD 0#32).toNat / 2 < c.mv →
    mrk[(s.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8

private structure ClearTrlInv (c : CorePlusCfg) (s : CorePlusState) (tf j : Nat)
    (mrk : List (BitVec 8)) : Prop where
  hjlo : tf ≤ j
  hjle : j ≤ max tf s.trail_end
  len : mrk.length = c.mv
  pres : ∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk[v]?.getD 0#8 = 0#8
  clrt : ∀ k, 1 ≤ k → k < s.tmp_len → (s.tmp[k]?.getD 0#32).toNat / 2 < c.mv →
    mrk[(s.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8
  clrr : ∀ k, tf ≤ k → k < j → k < s.trail_end → (s.trl[k]?.getD 0#32).toNat / 2 < c.mv →
    mrk[(s.trl[k]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8

/-- Specification proof for `kissat_clear_marks(h, trail_from)`. -/
theorem kissat_clear_marks_wp (Γ : Env) :
    ∀ a m Q X, corePlusClearMarksSpec a m Q X → Func.wp Γ kissat_clear_marks_body a m Q X := by
  rintro ⟨h, trail_from, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, htl_mv, hm, hQ⟩
  unfold Func.wp kissat_clear_marks_body
  have hmv : c.mv < 2 ^ 28 := c.hmv
  have htl_arr := hlen.tmp_len_arr; have htrl_arr := hlen.trl_len
  have hte_le := hlen.trail_end_le; have htf64 := trail_from.isLt
  cp_steps
  refine wp_loop_inv (fun v ml => ∃ mrk1, ClearTmpInv c s v.1.toNat mrk1 ∧
      (CorePlusMem c { s with mrk := mrk1 } ⋆ R) ml)
    (fun v _ => max 1 s.tmp_len - v.1.toNat) (fun L ih => by
      cp_steps; exact ih _ _ ⟨s.mrk, ⟨by c0_bound, by c0_bound, hlen.mrk_len,
        fun _ _ h => h, fun k _ hk2 => by simp only [bv_c0] at hk2; omega⟩, hm⟩)
    (fun L v ml ⟨mrk1, inv1, hml⟩ ih => ?_)
  have hm1l := inv1.len; have hi1 := inv1.hi1; have hile := inv1.hile
  cp_steps
  · have hlt : v.1.toNat < s.tmp_len := by c0_bound
    have hidx : v.1.toNat < s.tmp.length := by omega
    have hvn := bv32_shr1_zext64 (s.tmp[v.1.toNat]'hidx)
    have hv_lt : ((s.tmp[v.1.toNat]'hidx >>> 1).setWidth 64).toNat < c.mv := by
      simp only [bv_c0, Nat.reducePow] at hc; omega
    refine ih _ _ (by c0_bound) ⟨mrk1.set ((s.tmp[v.1.toNat]'hidx).toNat / 2) 0#8,
      ⟨by c0_bound, by c0_bound, by simp [hm1l],
        fun w hw hz => mrk_set_zero_pres (inv1.pres w hw hz),
        fun k hk1 hki hkt hkv => by
          simp only [bv_c0, Nat.reducePow] at hki
          exact mrk_set_zero_idx (fun j => (s.tmp[j]?.getD 0#32).toNat / 2) v.1.toNat (by omega)
            (fun hne => inv1.clr k hk1 (by omega) hkt hkv)
            fun hke => by subst hke; rw [List.getElem?_eq_getElem hidx, Option.getD_some]⟩,
      by rw [← hvn]; exact hm⟩
  · have hlt : v.1.toNat < s.tmp_len := by c0_bound
    have hidx : v.1.toNat < s.tmp.length := by omega
    refine ih _ _ (by c0_bound) ⟨mrk1, ⟨by c0_bound, by c0_bound, hm1l, inv1.pres,
      fun k hk1 hki hkt hkv => by
        simp only [bv_c0, Nat.reducePow] at hki hc
        by_cases hke : k = v.1.toNat
        · subst hke; rw [List.getElem?_eq_getElem hidx, Option.getD_some] at hkv; omega
        · exact inv1.clr k hk1 (by omega) hkt hkv⟩, hml⟩
  · have hclr_all : ∀ k, 1 ≤ k → k < s.tmp_len → (s.tmp[k]?.getD 0#32).toNat / 2 < c.mv →
        mrk1[(s.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8 :=
      fun k hk1 hkt hkv => inv1.clr k hk1 (by c0_bound) hkt hkv
    refine wp_loop_inv (fun w m2 => ∃ mrk2, ClearTrlInv c s trail_from.toNat w.1.toNat mrk2 ∧
        (CorePlusMem c { s with mrk := mrk2 } ⋆ R) m2)
      (fun w _ => max trail_from.toNat s.trail_end - w.1.toNat)
      (fun L2 ih2 => by cp_steps; exact ih2 _ _ ⟨mrk1, ⟨le_refl _, Nat.le_max_left _ _,
        hm1l, inv1.pres, hclr_all, fun _ _ h2 => by dsimp at h2; omega⟩, hml⟩)
      (fun L2 w m2 ⟨mrk2, inv2, hm2⟩ ih2 => ?_)
    have hm2l := inv2.len; have hjlo := inv2.hjlo; have hjle := inv2.hjle
    cp_steps
    · have hwlt : w.1.toNat < s.trail_end := by c0_bound
      have hidx : w.1.toNat < s.trl.length := by omega
      have htvn := bv32_shr1_zext64 (s.trl[w.1.toNat]'hidx)
      have htv_lt : ((s.trl[w.1.toNat]'hidx >>> 1).setWidth 64).toNat < c.mv := by
        simp only [bv_c0, Nat.reducePow] at hc; omega
      refine ih2 _ _ (by c0_bound) ⟨mrk2.set ((s.trl[w.1.toNat]'hidx).toNat / 2) 0#8,
        ⟨by c0_bound, by c0_bound, by simp [hm2l],
          fun u hu hz => mrk_set_zero_pres (inv2.pres u hu hz),
          fun k hk1 hkt hkv => mrk_set_zero_pres (inv2.clrt k hk1 hkt hkv),
          fun k hklo hkj hkt hkv => by
            simp only [bv_c0, Nat.reducePow] at hkj
            exact mrk_set_zero_idx (fun j => (s.trl[j]?.getD 0#32).toNat / 2) w.1.toNat
              (by omega) (fun hne => inv2.clrr k hklo (by omega) hkt hkv)
              fun hke => by subst hke; rw [List.getElem?_eq_getElem hidx, Option.getD_some]⟩,
        by rw [← htvn]; exact hm⟩
    · have hwlt : w.1.toNat < s.trail_end := by c0_bound
      have hidx : w.1.toNat < s.trl.length := by omega
      refine ih2 _ _ (by c0_bound) ⟨mrk2, ⟨by c0_bound, by c0_bound, hm2l, inv2.pres, inv2.clrt,
        fun k hklo hkj hkt hkv => by
          simp only [bv_c0, Nat.reducePow] at hkj hc
          by_cases hke : k = w.1.toNat
          · subst hke; rw [List.getElem?_eq_getElem hidx, Option.getD_some] at hkv; omega
          · exact inv2.clrr k hklo (by omega) hkt hkv⟩, hm2⟩
    · exact hQ mrk2 m2 hm2l inv2.pres inv2.clrt
        (fun k hklo hkt hkv => inv2.clrr k hklo (by c0_bound) hkt hkv) hm2

/-! ## 4. `kissat_min_mark` (`corePlusMinMarkSpec`) -/

/-- Specification proof for `kissat_min_mark(h, v, tag)`. -/
theorem kissat_min_mark_wp (Γ : Env) :
    ∀ a m Q X, corePlusMinMarkSpec a m Q X → Func.wp Γ kissat_min_mark_body a m Q X := by
  rintro ⟨h, v, tag, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  unfold Func.wp kissat_min_mark_body
  have hmv : c.mv < 2 ^ 28 := c.hmv
  have hml := hlen.mrk_len; have hmcl := hlen.min_clr_len_arr; have hmc_le := hlen.min_clr_len_le
  have hv64 : (v.setWidth 64).toNat = v.toNat := by
    rw [bv32_zext64_eq, BitVec.toNat_ofNat, min_bv32_mod64]
  have hv_mod : v.toNat % 2 ^ 64 = v.toNat := min_bv32_mod64 v
  cp_steps
  · simp only [show c.mv ≤ v.toNat by c0_bound, true_or, ↓reduceIte] at hQ; exact hQ
  · have hnz : s.mrk[v.toNat]?.getD 0#8 ≠ 0#8 := by
      rw [List.getElem?_eq_getElem (by c0_bound), Option.getD_some]
      simp only [bv_c0, Nat.reducePow, hv_mod] at hc; exact hc
    split at hQ; · exact hQ
    · simp [hnz] at *
  · rename_i hc_mv hc_mrk
    have hz : s.mrk[v.toNat]?.getD 0#8 = 0#8 := by
      rw [List.getElem?_eq_getElem (by c0_bound), Option.getD_some]
      simp only [bv_c0, Nat.reducePow, hv_mod] at hc_mrk; exact hc_mrk
    have hnot : ¬(c.mv ≤ v.toNat ∨ s.mrk[v.toNat]?.getD 0#8 ≠ 0#8) := by c0_bound
    have hlt : s.min_clr_len < c.mv := by c0_bound
    simp only [hnot, hlt, ↓reduceIte] at hQ
    have hlen_eq : (BitVec.ofNat 64 s.min_clr_len + 1).toNat = s.min_clr_len + 1 := by
      simp [bv_c0]; omega
    exact hQ _ (by rwa [hv64, hlen_eq, show (BitVec.ofNat 64 s.min_clr_len).toNat =
      s.min_clr_len by simp [bv_c0]; omega] at hm)
  · rename_i hc_mv hc_mrk
    have hz : s.mrk[v.toNat]?.getD 0#8 = 0#8 := by
      rw [List.getElem?_eq_getElem (by c0_bound), Option.getD_some]
      simp only [bv_c0, Nat.reducePow, hv_mod] at hc_mrk; exact hc_mrk
    have hnot : ¬(c.mv ≤ v.toNat ∨ s.mrk[v.toNat]?.getD 0#8 ≠ 0#8) := by c0_bound
    have hge : ¬s.min_clr_len < c.mv := by c0_bound
    simp only [hnot, hge, ↓reduceIte] at hQ
    exact hQ _ (by rwa [hv64] at hm)

/-! ## 5. Shared `withMinFields`, `minMark`, and `MinFrameOk` infrastructure -/

theorem mrk_dom_cases {b : BitVec 8} (hb : b = 0#8 ∨ b = 2#8 ∨ b = 4#8) :
    ((b &&& 2#8) ≠ 0#8 → b = 2#8) ∧
    ((b &&& 4#8) ≠ 0#8 → b = 4#8) ∧
    ((b &&& 2#8) = 0#8 → (b &&& 4#8) = 0#8 → b = 0#8) := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem CorePlusCoreInv.of_minFields {c : CorePlusCfg} {F0 : CNF Nat}
    {s : CorePlusState} (hc : CorePlusCoreInv c F0 s) {mrk' : List (BitVec 8)}
    {mstk' mclr' : List (BitVec 32)} {mcl' : Nat} {mcf' : BitVec 64}
    (h1 : mrk'.length = c.mv) (h2 : mstk'.length = 2 * c.minDepth)
    (h3 : mclr'.length = c.mv) (h4 : mcl' ≤ c.mv) :
    CorePlusCoreInv c F0 (withMinFields s mrk' mstk' mclr' mcl' mcf') :=
  { hc with
    lengths :=
      { hc.lengths with
        mrk_len := h1, min_stk_len := h2,
        min_clr_len_arr := h3, min_clr_len_le := h4 }
    clauses := { hc.clauses with bounds := hc.clauses.bounds } }

theorem minMarkInv_set_stk {c : CorePlusCfg} {s : CorePlusState} {keep : List Nat}
    (h : MinMarkInv c s keep) (mstk' : List (BitVec 32)) :
    MinMarkInv c { s with min_stk := mstk' } keep :=
  ⟨h.mrk_dom, h.clr_cov, h.rem_sound⟩

theorem minMarkState_facts {c : CorePlusCfg} {s : CorePlusState} (hlen : s.LengthsOk c)
    {v : Nat} (hv : v < c.mv) (hz : s.mrk[v]?.getD 0#8 = 0#8) (tag : BitVec 8) :
    let st := minMarkState c s v tag
    st.mrk.length = c.mv ∧ st.min_clr.length = c.mv ∧ st.min_clr_len ≤ c.mv ∧
    st.mrk[v]?.getD 0#8 = tag ∧
    (∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → st.mrk[w]?.getD 0#8 = 2#8) ∧
    (tag ≠ 4#8 → ∀ w < c.mv, s.mrk[w]?.getD 0#8 ≠ 4#8 → st.mrk[w]?.getD 0#8 ≠ 4#8) := by
  have hm := hlen.mrk_len; have hca := hlen.min_clr_len_arr; have hcl := hlen.min_clr_len_le
  have hlen3 : (minMarkState c s v tag).mrk.length = c.mv ∧
      (minMarkState c s v tag).min_clr.length = c.mv ∧
      (minMarkState c s v tag).min_clr_len ≤ c.mv := by
    dsimp only [minMarkState]; by_cases h : s.min_clr_len < c.mv <;> simp [h, hm, hca] <;> omega
  refine ⟨hlen3.1, hlen3.2.1, hlen3.2.2, ?_, fun w _ hw => ?_, fun hnt w _ hw => ?_⟩
  · dsimp only [minMarkState]; rw [List.getElem?_set_self (by omega), Option.getD_some]
  · dsimp only [minMarkState]
    by_cases hwe : w = v
    · subst hwe; rw [hz] at hw; cases hw
    · rwa [List.getElem?_set_ne (Ne.symm hwe)]
  · dsimp only [minMarkState]
    by_cases hwe : w = v
    · subst hwe; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hnt
    · rwa [List.getElem?_set_ne (Ne.symm hwe)]

theorem minMark_poison_post {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {keep : List Nat} (hcore : CorePlusCoreInv c F0 s) (hmin : MinMarkInv c s keep)
    (v : BitVec 32) {mrk' : List (BitVec 8)} {mclr' : List (BitVec 32)}
    {mcl' : Nat} {mcf' : BitVec 64}
    (hbranch : if c.mv ≤ v.toNat ∨ s.mrk[v.toNat]?.getD 0#8 ≠ 0#8 then
        mrk' = s.mrk ∧ mclr' = s.min_clr ∧ mcl' = s.min_clr_len ∧ mcf' = s.min_clr_full
      else let st' := minMarkState c s v.toNat 4#8
        mrk' = st'.mrk ∧ mclr' = st'.min_clr ∧ mcl' = st'.min_clr_len ∧ mcf' = st'.min_clr_full) :
    let s' : CorePlusState :=
      { s with mrk := mrk', min_clr := mclr', min_clr_len := mcl', min_clr_full := mcf' }
    mrk'.length = c.mv ∧ mclr'.length = c.mv ∧ mcl' ≤ c.mv ∧
    (∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → mrk'[w]?.getD 0#8 = 2#8) ∧
    MinMarkInv c s' keep := by
  by_cases hskip : c.mv ≤ v.toNat ∨ s.mrk[v.toNat]?.getD 0#8 ≠ 0#8
  · simp only [hskip, ↓reduceIte] at hbranch; rcases hbranch with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨hcore.lengths.mrk_len, hcore.lengths.min_clr_len_arr,
      hcore.lengths.min_clr_len_le, fun _ _ hw => hw, hmin⟩
  · simp only [hskip, ↓reduceIte] at hbranch; rcases hbranch with ⟨rfl, rfl, rfl, rfl⟩
    have hz : s.mrk[v.toNat]?.getD 0#8 = 0#8 := Classical.not_not.mp fun hn => hskip (Or.inr hn)
    have hf := minMarkState_facts hcore.lengths (by omega) hz 4#8
    exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.2.1, minMarkInv_poison hcore hmin (by omega) hz⟩

theorem minMark_pop_post {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {keep : List Nat} (hcore : CorePlusCoreInv c F0 s) (hmin : MinMarkInv c s keep)
    {idx0 : Nat} (hi0 : idx0 < s.trail_end) (v : BitVec 32)
    (hv_eq : (s.trl[idx0]?.getD 0#32).toNat / 2 = v.toNat)
    (hn4 : s.mrk[v.toNat]?.getD 0#8 ≠ 4#8)
    (hrsn : let p0 := (s.trl[idx0]?.getD 0#32).toNat
      let rsn := s.rsns[p0 / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 ∧ rsn.toNat < s.num_clauses ∧
      ∀ q ∈ clauseLits s rsn.toNat,
        q = p0 ∨ ∃ k < idx0, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
          ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ s.mrk[q / 2]?.getD 0#8 = 2#8))
    {mrk' : List (BitVec 8)} {mclr' : List (BitVec 32)} {mcl' : Nat} {mcf' : BitVec 64}
    (hbranch : if c.mv ≤ v.toNat ∨ s.mrk[v.toNat]?.getD 0#8 ≠ 0#8 then
        mrk' = s.mrk ∧ mclr' = s.min_clr ∧ mcl' = s.min_clr_len ∧ mcf' = s.min_clr_full
      else let st' := minMarkState c s v.toNat 2#8
        mrk' = st'.mrk ∧ mclr' = st'.min_clr ∧ mcl' = st'.min_clr_len ∧ mcf' = st'.min_clr_full) :
    let s' : CorePlusState :=
      { s with mrk := mrk', min_clr := mclr', min_clr_len := mcl', min_clr_full := mcf' }
    mrk'.length = c.mv ∧ mclr'.length = c.mv ∧ mcl' ≤ c.mv ∧
    mrk'[v.toNat]?.getD 0#8 = 2#8 ∧
    (∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → mrk'[w]?.getD 0#8 = 2#8) ∧
    (∀ w < c.mv, s.mrk[w]?.getD 0#8 ≠ 4#8 → mrk'[w]?.getD 0#8 ≠ 4#8) ∧
    MinMarkInv c s' keep := by
  have hv : v.toNat < c.mv := by have := hcore.trail_lits_lt idx0 hi0; omega
  by_cases hskip : c.mv ≤ v.toNat ∨ s.mrk[v.toNat]?.getD 0#8 ≠ 0#8
  · simp only [hskip, ↓reduceIte] at hbranch; rcases hbranch with ⟨rfl, rfl, rfl, rfl⟩
    have hm2 : s.mrk[v.toNat]?.getD 0#8 = 2#8 := by
      rcases hmin.mrk_dom v.toNat hv with h0 | h2 | h4
      · rcases hskip with hge | hne
        · omega
        · exact absurd h0 hne
      · exact h2
      · exact absurd h4 hn4
    exact ⟨hcore.lengths.mrk_len, hcore.lengths.min_clr_len_arr,
      hcore.lengths.min_clr_len_le, hm2, fun _ _ hw => hw, fun _ _ hw => hw, hmin⟩
  · simp only [hskip, ↓reduceIte] at hbranch; rcases hbranch with ⟨rfl, rfl, rfl, rfl⟩
    have hz : s.mrk[v.toNat]?.getD 0#8 = 0#8 := Classical.not_not.mp fun hn => hskip (Or.inr hn)
    have hf := minMarkState_facts hcore.lengths hv hz 2#8
    have hinv' := minMarkInv_mark_rem hcore hmin hi0 (by rw [hv_eq]; exact hz) hrsn
    rw [hv_eq] at hinv'
    exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2 (by decide), hinv'⟩

theorem minMark_wp_of_spec {Γ : Env}
    (hMm : ∀ a m Q X, corePlusMinMarkSpec a m Q X →
      Γ "kissat_min_mark" [i64, i32, i8] [] a m Q X)
    {c : CorePlusCfg} {s : CorePlusState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 32) (tag : BitVec 8) {Q : Post []} {X : XPost}
    (hlen : s.LengthsOk c) (hm : (CorePlusMem c s ⋆ R) m)
    (hcont : ∀ mrk' mclr' mcl' mcf' m',
      (if c.mv ≤ v.toNat ∨ s.mrk[v.toNat]?.getD 0#8 ≠ 0#8 then
          mrk' = s.mrk ∧ mclr' = s.min_clr ∧ mcl' = s.min_clr_len ∧ mcf' = s.min_clr_full
        else let st' := minMarkState c s v.toNat tag
          mrk' = st'.mrk ∧ mclr' = st'.min_clr ∧ mcl' = st'.min_clr_len ∧
          mcf' = st'.min_clr_full) →
      (CorePlusMem c
        { s with mrk := mrk', min_clr := mclr', min_clr_len := mcl', min_clr_full := mcf' } ⋆
        R) m' → Q () m') :
    Γ "kissat_min_mark" [i64, i32, i8] [] (c.hdr, v, tag, ()) m Q X := by
  refine hMm _ m Q X ⟨c, s, R, rfl, hlen, hm, ?_⟩
  by_cases hskip : c.mv ≤ v.toNat ∨ s.mrk[v.toNat]?.getD 0#8 ≠ 0#8
  · simp only [hskip, ↓reduceIte]; exact hcont _ _ _ _ _ (by simp [hskip]) hm
  · by_cases hclr : s.min_clr_len < c.mv <;> simp only [hskip, hclr, ↓reduceIte] <;>
      exact fun m' hm' => hcont _ _ _ _ _ (by simp [hskip, hclr, minMarkState, bv_ofNat_toNat_eq v])
        hm'

/-- Stack frame invariant for `0 ..= sp` in `kissat_minimize_lit`. -/
structure MinFrameOk (c : CorePlusCfg) (s : CorePlusState)
    (mrk : List (BitVec 8)) (mstk : List (BitVec 32))
    (root_lit : Nat) (idx0 sp : Nat) : Prop where
  sp_lt : sp < c.minDepth
  mrk_len : mrk.length = c.mv
  stk_len : mstk.length = 2 * c.minDepth
  idx : ∀ j ≤ sp, ∃ idx_j < s.trail_end,
    let v_j := (mstk[2 * j]?.getD 0#32).toNat
    v_j < c.mv ∧ (s.trl[idx_j]?.getD 0#32).toNat / 2 = v_j ∧
    (j = 0 → idx_j = idx0) ∧ mrk[v_j]?.getD 0#8 ≠ 4#8 ∧
    let rcid := s.rsns[v_j]?.getD 0xFFFFFFFF#32
    rcid ≠ 0xFFFFFFFF#32 ∧ rcid.toNat < s.num_clauses ∧
    let pos_j := (mstk[2 * j + 1]?.getD 0#32).toNat
    ∀ t < min pos_j (clauseSize s rcid.toNat),
      let q := (s.lpool[clauseOff s rcid.toNat + t]?.getD 0#32).toNat
      q = (s.trl[idx_j]?.getD 0#32).toNat ∨
      ∃ k < idx_j, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
        ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ mrk[q / 2]?.getD 0#8 = 2#8 ∨
         (j < sp ∧ t + 1 = pos_j ∧ q / 2 = (mstk[2 * (j + 1)]?.getD 0#32).toNat))

theorem min_lit_child_rel {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    (hcore : CorePlusCoreInv c F0 s) {idx_sp pos : Nat} (hidx_sp : idx_sp < s.trail_end)
    {rcid : BitVec 32}
    (hrsn : s.rsns[(s.trl[idx_sp]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = rcid)
    (hne : rcid ≠ 0xFFFFFFFF#32) (hpos : pos < clauseSize s rcid.toNat) :
    let q := (s.lpool[clauseOff s rcid.toNat + pos]?.getD 0#32).toNat
    q / 2 = (s.trl[idx_sp]?.getD 0#32).toNat / 2 ∧ q = (s.trl[idx_sp]?.getD 0#32).toNat ∨
    q / 2 ≠ (s.trl[idx_sp]?.getD 0#32).toNat / 2 ∧
      ∃ k < idx_sp, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 := by
  have ⟨hrc_lt, hall⟩ := hcore.reason_inv idx_sp hidx_sp (by rwa [hrsn])
  rw [hrsn] at hrc_lt hall
  have hclb := hcore.clauses.bounds rcid.toNat hrc_lt
  have hlplen : clauseOff s rcid.toNat + clauseSize s rcid.toNat ≤ s.lpool.length := by
    rw [hcore.lengths.lpool_len]; have := hcore.lengths.lit_len_le; omega
  have hmem : (s.lpool[clauseOff s rcid.toNat + pos]?.getD 0#32).toNat ∈
      clauseLits s rcid.toNat := by
    rw [mem_clauseLits_iff hlplen]; refine ⟨pos, hpos, ?_⟩
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  rcases hall _ hmem with heq | ⟨k, hk, hkeq⟩
  · exact Or.inl ⟨congrArg (· / 2) heq, heq⟩
  · refine Or.inr ⟨fun hveq => ?_, k, hk, hkeq⟩
    have hkd : (s.trl[k]?.getD 0#32).toNat / 2 = (s.trl[idx_sp]?.getD 0#32).toNat / 2 := by
      rw [hkeq]; exact (litVar_litNeg _).trans hveq
    exact Nat.ne_of_lt hk (hcore.trail_vars_nodup k idx_sp (Nat.lt_trans hk hidx_sp) hidx_sp hkd)

theorem minFrameOk_skip {c : CorePlusCfg} {s : CorePlusState}
    {mrk : List (BitVec 8)} {mstk : List (BitVec 32)} {root_lit idx0 sp pos : Nat}
    (hf : MinFrameOk c s mrk mstk root_lit idx0 sp)
    (hpos_eq : (mstk[2 * sp + 1]?.getD 0#32).toNat = pos) (hpos_u32 : pos + 1 < 2 ^ 32)
    (hnew : ∀ idx_sp < s.trail_end,
      (s.trl[idx_sp]?.getD 0#32).toNat / 2 = (mstk[2 * sp]?.getD 0#32).toNat →
      let rcid := s.rsns[(mstk[2 * sp]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32
      let q := (s.lpool[clauseOff s rcid.toNat + pos]?.getD 0#32).toNat
      q = (s.trl[idx_sp]?.getD 0#32).toNat ∨
      ∃ k < idx_sp, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
        ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ mrk[q / 2]?.getD 0#8 = 2#8)) :
    MinFrameOk c s mrk (mstk.set (2 * sp + 1) (BitVec.ofNat 32 (pos + 1))) root_lit idx0 sp := by
  have hlen := hf.stk_len
  refine ⟨hf.sp_lt, hf.mrk_len, by simp [hlen], fun j hj => ?_⟩
  obtain ⟨idx_j, hidx_j, hv_lt, htr, hj0, hn4, hrc1, hrc2, hslots⟩ := hf.idx j hj
  have hv_same : (mstk.set (2 * sp + 1) (BitVec.ofNat 32 (pos + 1)))[2 * j]?.getD 0#32 =
      mstk[2 * j]?.getD 0#32 := by rw [List.getElem?_set_ne (by omega)]
  refine ⟨idx_j, hidx_j, by simpa [hv_same] using hv_lt, by simpa [hv_same] using htr, hj0,
    by simpa [hv_same] using hn4, by simpa [hv_same] using hrc1, by simpa [hv_same] using hrc2,
    fun t ht => ?_⟩
  simp only [hv_same] at ht ⊢
  by_cases hjsp : j = sp
  · subst hjsp
    have hset_self : ((mstk.set (2 * j + 1) (BitVec.ofNat 32 (pos + 1)))[2 * j + 1]?.getD
        0#32).toNat = pos + 1 := by
      rw [List.getElem?_set_self (by have := hf.sp_lt; omega), Option.getD_some,
        bv32_ofNat_toNat hpos_u32]
    rw [hset_self] at ht
    by_cases ht_lt : t < pos
    · rcases hslots t (by omega) with heq | ⟨k, hk, hkeq, hc⟩
      · exact Or.inl heq
      · rcases hc with hl0 | hm2 | ⟨hlt, _⟩ <;> first
          | exact Or.inr ⟨k, hk, hkeq, Or.inl hl0⟩
          | exact Or.inr ⟨k, hk, hkeq, Or.inr (Or.inl hm2)⟩
          | omega
    · obtain rfl : t = pos := by omega
      rcases hnew idx_j hidx_j htr with heq | ⟨k, hk, hkeq, hl_or_m⟩
      · exact Or.inl heq
      · exact Or.inr ⟨k, hk, hkeq, hl_or_m.elim Or.inl (fun hm2 => Or.inr (Or.inl hm2))⟩
  · have h1 : (mstk.set (2 * sp + 1) (BitVec.ofNat 32 (pos + 1)))[2 * j + 1]?.getD 0#32 =
        mstk[2 * j + 1]?.getD 0#32 := by rw [List.getElem?_set_ne (by omega)]
    have h2 : (mstk.set (2 * sp + 1) (BitVec.ofNat 32 (pos + 1)))[2 * (j + 1)]?.getD 0#32 =
        mstk[2 * (j + 1)]?.getD 0#32 := by rw [List.getElem?_set_ne (by omega)]
    rw [h1] at ht ⊢; rw [h2]; exact hslots t ht

def pushMinStk (mstk : List (BitVec 32)) (sp pos : Nat) (u : BitVec 32) :
    List (BitVec 32) :=
  ((mstk.set (2 * sp + 1) (BitVec.ofNat 32 (pos + 1))).set (2 * (sp + 1)) u).set
    (2 * (sp + 1) + 1) 0#32

theorem pushMinStk_len {mstk : List (BitVec 32)} {sp pos D : Nat} {u : BitVec 32}
    (hl : mstk.length = 2 * D) : (pushMinStk mstk sp pos u).length = 2 * D := by
  simp [pushMinStk, hl]

private theorem pushMinStk_get_v {mstk : List (BitVec 32)} {sp pos : Nat} {u : BitVec 32}
    (h : 2 * (sp + 1) + 1 < mstk.length) :
    (pushMinStk mstk sp pos u)[2 * (sp + 1)]?.getD 0#32 = u := by
  unfold pushMinStk; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega),
    Option.getD_some]

private theorem pushMinStk_get_p0 {mstk : List (BitVec 32)} {sp pos : Nat} {u : BitVec 32}
    (h : 2 * (sp + 1) + 1 < mstk.length) :
    ((pushMinStk mstk sp pos u)[2 * (sp + 1) + 1]?.getD 0#32).toNat = 0 := by
  unfold pushMinStk; rw [List.getElem?_set_self (by simp; omega), Option.getD_some]; rfl

private theorem pushMinStk_get_pos {mstk : List (BitVec 32)} {sp pos : Nat} {u : BitVec 32}
    (h : 2 * sp + 1 < mstk.length) (hu : pos + 1 < 2 ^ 32) :
    ((pushMinStk mstk sp pos u)[2 * sp + 1]?.getD 0#32).toNat = pos + 1 := by
  unfold pushMinStk
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
    List.getElem?_set_self h, Option.getD_some, bv32_ofNat_toNat hu]

private theorem pushMinStk_get_old {mstk : List (BitVec 32)} {sp pos k : Nat} {u : BitVec 32}
    (hk : k < 2 * sp + 1) : (pushMinStk mstk sp pos u)[k]?.getD 0#32 = mstk[k]?.getD 0#32 := by
  unfold pushMinStk
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
    List.getElem?_set_ne (by omega)]

theorem minFrameOk_push {c : CorePlusCfg} {s : CorePlusState}
    {mrk : List (BitVec 8)} {mstk : List (BitVec 32)} {root_lit idx0 sp pos : Nat}
    {u ur : BitVec 32} (hf : MinFrameOk c s mrk mstk root_lit idx0 sp) (hsp1 : sp + 1 < c.minDepth)
    (hpos_eq : (mstk[2 * sp + 1]?.getD 0#32).toNat = pos)
    (hpos_u32 : pos + 1 < 2 ^ 32) (hu_lt : u.toNat < c.mv) (hn4 : mrk[u.toNat]?.getD 0#8 ≠ 4#8)
    (hur_eq : s.rsns[u.toNat]?.getD 0xFFFFFFFF#32 = ur)
    (hur1 : ur ≠ 0xFFFFFFFF#32) (hur2 : ur.toNat < s.num_clauses)
    (hnew : ∀ idx_sp < s.trail_end,
      (s.trl[idx_sp]?.getD 0#32).toNat / 2 = (mstk[2 * sp]?.getD 0#32).toNat →
      let rcid := s.rsns[(mstk[2 * sp]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32
      let q := (s.lpool[clauseOff s rcid.toNat + pos]?.getD 0#32).toNat
      q / 2 = u.toNat ∧ ∃ k < idx_sp, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1) :
    MinFrameOk c s mrk (pushMinStk mstk sp pos u) root_lit idx0 (sp + 1) := by
  have hlen := hf.stk_len
  have hvu := pushMinStk_get_v (mstk := mstk) (sp := sp) (pos := pos) (u := u) (by omega)
  refine ⟨hsp1, hf.mrk_len, pushMinStk_len hlen, fun j hj => ?_⟩
  by_cases hjt : j = sp + 1
  · subst hjt
    obtain ⟨idx_sp, hidx_sp, _, htr_sp, _, _, _, _, _⟩ := hf.idx sp (le_refl _)
    obtain ⟨hqd_u, idx_u, hku, hueq⟩ := hnew idx_sp hidx_sp htr_sp
    have hp0 := pushMinStk_get_p0 (mstk := mstk) (sp := sp) (pos := pos) (u := u) (by omega)
    refine ⟨idx_u, Nat.lt_trans hku hidx_sp, by rw [hvu]; exact hu_lt,
      by rw [hvu, hueq]; exact (litVar_litNeg _).trans hqd_u, fun h => by omega,
      by rw [hvu]; exact hn4, by rw [hvu, hur_eq]; exact hur1,
      by rw [hvu, hur_eq]; exact hur2, fun t ht => by rw [hp0] at ht; omega⟩
  · obtain ⟨idx_j, hidx_j, hv_lt, htr, hj0, hn4_j, hrc1, hrc2, hslots⟩ := hf.idx j (by omega)
    have hv_same := pushMinStk_get_old (mstk := mstk) (sp := sp) (pos := pos) (u := u)
      (by omega : 2 * j < 2 * sp + 1)
    refine ⟨idx_j, hidx_j, by simpa [hv_same] using hv_lt, by simpa [hv_same] using htr, hj0,
      by simpa [hv_same] using hn4_j, by simpa [hv_same] using hrc1, by simpa [hv_same] using hrc2,
      fun t ht => ?_⟩
    rw [hv_same] at ht ⊢
    by_cases hjsp : j = sp
    · subst hjsp
      rw [pushMinStk_get_pos (by omega) hpos_u32] at ht ⊢; rw [hvu]
      by_cases ht_lt : t < pos
      · rcases hslots t (by omega) with heq | ⟨k, hk, hkeq, hc⟩
        · exact Or.inl heq
        · rcases hc with hl0 | hm2 | ⟨hlt, _⟩ <;> first
            | exact Or.inr ⟨k, hk, hkeq, Or.inl hl0⟩
            | exact Or.inr ⟨k, hk, hkeq, Or.inr (Or.inl hm2)⟩
            | omega
      · obtain rfl : t = pos := by omega
        obtain ⟨hqd, k, hk, hkeq⟩ := hnew idx_j hidx_j htr
        exact Or.inr ⟨k, hk, hkeq, Or.inr (Or.inr ⟨by omega, rfl, hqd⟩)⟩
    · rw [pushMinStk_get_old (by omega : 2 * j + 1 < 2 * sp + 1)] at ht ⊢
      rw [pushMinStk_get_old (by omega : 2 * (j + 1) < 2 * sp + 1)]
      rcases hslots t ht with heq | ⟨k, hk, hkeq, hc⟩
      · exact Or.inl heq
      · rcases hc with hl0 | hm2 | ⟨hlt, htp, hqv⟩ <;> first
          | exact Or.inr ⟨k, hk, hkeq, Or.inl hl0⟩
          | exact Or.inr ⟨k, hk, hkeq, Or.inr (Or.inl hm2)⟩
          | exact Or.inr ⟨k, hk, hkeq, Or.inr (Or.inr ⟨by omega, htp, hqv⟩)⟩

theorem minFrameOk_pop {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {mrk mrk' : List (BitVec 8)} {mstk : List (BitVec 32)} {root_lit idx0 sp : Nat}
    (hcore : CorePlusCoreInv c F0 s) (hf : MinFrameOk c s mrk mstk root_lit idx0 sp) (hsp : 0 < sp)
    (hm'_len : mrk'.length = c.mv)
    (hpres : ∀ w < c.mv, mrk[w]?.getD 0#8 = 2#8 → mrk'[w]?.getD 0#8 = 2#8)
    (hpres4 : ∀ w < c.mv, mrk[w]?.getD 0#8 ≠ 4#8 → mrk'[w]?.getD 0#8 ≠ 4#8)
    (hm_top : mrk'[(mstk[2 * sp]?.getD 0#32).toNat]?.getD 0#8 = 2#8) :
    MinFrameOk c s mrk' mstk root_lit idx0 (sp - 1) := by
  refine ⟨by have := hf.sp_lt; omega, hm'_len, hf.stk_len, fun j hj => ?_⟩
  obtain ⟨idx_j, hidx_j, hv_lt, htr, hj0, hn4, hrc1, hrc2, hslots⟩ := hf.idx j (by omega)
  refine ⟨idx_j, hidx_j, hv_lt, htr, hj0, hpres4 _ hv_lt hn4, hrc1, hrc2, fun t ht => ?_⟩
  rcases hslots t ht with heq | ⟨k, hk, hkeq, hc⟩
  · exact Or.inl heq
  · refine Or.inr ⟨k, hk, hkeq, ?_⟩
    rcases hc with hl0 | hm2 | ⟨hlt, htp, hqv⟩
    · exact Or.inl hl0
    · refine Or.inr (Or.inl (hpres _ ?_ hm2))
      have hkl := hcore.trail_lits_lt k (Nat.lt_trans hk hidx_j)
      have hdiv := litVar_litNeg (s.lpool[clauseOff s (s.rsns[(mstk[2 * j]?.getD 0#32).toNat]?.getD
        0xFFFFFFFF#32).toNat + t]?.getD 0#32).toNat
      dsimp only [litVar, litNeg] at hdiv; rw [hkeq] at hkl; omega
    · by_cases hjtop : j = sp - 1
      · subst hjtop; rw [show sp - 1 + 1 = sp by omega] at hqv; exact Or.inr (Or.inl (hqv ▸ hm_top))
      · exact Or.inr (Or.inr ⟨by omega, htp, hqv⟩)

theorem minFrameOk_top_done {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {mrk : List (BitVec 8)} {mstk : List (BitVec 32)} {root_lit idx0 sp : Nat}
    (hcore : CorePlusCoreInv c F0 s) (hf : MinFrameOk c s mrk mstk root_lit idx0 sp)
    (hdone : clauseSize s (s.rsns[(mstk[2 * sp]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat ≤
      (mstk[2 * sp + 1]?.getD 0#32).toNat) :
    ∃ idx_sp < s.trail_end,
      let v_sp := (mstk[2 * sp]?.getD 0#32).toNat
      let p_sp := (s.trl[idx_sp]?.getD 0#32).toNat
      let rsn := s.rsns[p_sp / 2]?.getD 0xFFFFFFFF#32
      p_sp / 2 = v_sp ∧ (sp = 0 → idx_sp = idx0) ∧ mrk[v_sp]?.getD 0#8 ≠ 4#8 ∧
      rsn ≠ 0xFFFFFFFF#32 ∧ rsn.toNat < s.num_clauses ∧
      ∀ q ∈ clauseLits s rsn.toNat,
        q = p_sp ∨ ∃ k < idx_sp, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
          ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ mrk[q / 2]?.getD 0#8 = 2#8) := by
  obtain ⟨idx_sp, hidx_sp, _, htr, hj0, hn4, hrc1, hrc2, hslots⟩ := hf.idx sp (le_refl _)
  have hlplen : clauseOff s (s.rsns[(mstk[2 * sp]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat +
      clauseSize s (s.rsns[(mstk[2 * sp]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat ≤
      s.lpool.length := by
    have := hcore.clauses.bounds _ hrc2; rw [hcore.lengths.lpool_len]
    have := hcore.lengths.lit_len_le; omega
  refine ⟨idx_sp, hidx_sp, htr, hj0, hn4, ?_⟩
  rw [htr]; refine ⟨hrc1, hrc2, fun q hq => ?_⟩
  obtain ⟨t, ht, hqt⟩ := (mem_clauseLits_iff hlplen).mp hq
  have hlt_lp : clauseOff s (s.rsns[(mstk[2 * sp]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat +
      t < s.lpool.length := Nat.lt_of_lt_of_le (Nat.add_lt_add_left ht _) hlplen
  have hge := congrArg BitVec.toNat (congrArg (Option.getD · 0#32)
    (List.getElem?_eq_getElem hlt_lp).symm)
  dsimp only [Option.getD_some] at hge; rw [← hqt, hge]
  rcases hslots t (by omega) with heq | ⟨k, hk, hkeq, hc⟩
  · exact Or.inl heq
  · refine Or.inr ⟨k, hk, hkeq, ?_⟩
    rcases hc with hl0 | hm2 | ⟨hlt, _⟩ <;> first
      | exact Or.inl hl0
      | exact Or.inr hm2
      | omega

/-! ## 4. Shared pure invariants for `kissat_minimize_clause` -/

theorem HeurState.LengthsOk.with_stats {c : CorePlusCfg} {h : HeurState}
    (hok : h.LengthsOk c) (c' ll' mr' : BitVec 64) :
    ({ h with conflicts := c', learned_lits := ll', min_removed := mr' } :
      HeurState).LengthsOk c :=
  ⟨hok.heap_len_arr, hok.pos_len, hok.score_len, hok.phases_len, hok.heap_len_le⟩

theorem CorePlusCoreInv.of_minTmp {c : CorePlusCfg} {F0 : CNF Nat}
    {s : CorePlusState} (hc : CorePlusCoreInv c F0 s) {tmp' : List (BitVec 32)}
    {mrk' : List (BitVec 8)} {mstk' mclr' : List (BitVec 32)} {mcl' : Nat} {mcf' : BitVec 64}
    (ht : tmp'.length = c.mv) (h1 : mrk'.length = c.mv) (h2 : mstk'.length = 2 * c.minDepth)
    (h3 : mclr'.length = c.mv) (h4 : mcl' ≤ c.mv) :
    CorePlusCoreInv c F0 (withMinTmp s tmp' mrk' mstk' mclr' mcl' mcf') :=
  { hc with
    lengths :=
      { hc.lengths with
        tmp_len_arr := ht, mrk_len := h1, min_stk_len := h2,
        min_clr_len_arr := h3, min_clr_len_le := h4 }
    clauses := { hc.clauses with bounds := hc.clauses.bounds } }

theorem minMarkInv_set_tmp {c : CorePlusCfg} {s : CorePlusState} {keep : List Nat}
    (h : MinMarkInv c s keep) (tmp' : List (BitVec 32)) :
    MinMarkInv c { s with tmp := tmp' } keep :=
  ⟨h.mrk_dom, h.clr_cov, h.rem_sound⟩

theorem minMarkInv_keep_mono {c : CorePlusCfg} {s : CorePlusState}
    {keep1 keep2 : List Nat} (h : MinMarkInv c s keep1) (hsub : ∀ l ∈ keep1, l ∈ keep2) :
    MinMarkInv c s keep2 :=
  ⟨h.mrk_dom, h.clr_cov, fun idx hi hm => (h.rem_sound idx hi hm).imp_left (hsub _)⟩

def mcKeepSet (origTmp : List (BitVec 32)) (tlen : Nat)
    (tmp : List (BitVec 32)) (keep k : Nat) : List Nat :=
  (tmp.take keep).map BitVec.toNat ++ ((origTmp.take tlen).drop k).map BitVec.toNat

theorem mcKeepSet_init {origTmp : List (BitVec 32)} {tlen : Nat}
    (h1 : 1 ≤ tlen) (_hle : tlen ≤ origTmp.length) :
    mcKeepSet origTmp tlen origTmp 1 1 = (origTmp.take tlen).map BitVec.toNat := by
  unfold mcKeepSet; rw [← List.map_append]
  congr 1
  rw [← show (origTmp.take tlen).take 1 = origTmp.take 1 by
    rw [List.take_take, Nat.min_eq_left h1], List.take_append_drop]

theorem mcKeepSet_drop_head {origTmp tmp : List (BitVec 32)} {tlen keep k : Nat}
    (hk : k < tlen) (hle : tlen ≤ origTmp.length) :
    ∀ l ∈ mcKeepSet origTmp tlen tmp keep k,
      l = (origTmp[k]?.getD 0#32).toNat ∨ l ∈ mcKeepSet origTmp tlen tmp keep (k + 1) := by
  have hk_take : k < (origTmp.take tlen).length := by simp [List.length_take]; omega
  have hhead : (origTmp.take tlen)[k]'hk_take = origTmp[k]?.getD 0#32 := by
    rw [List.getElem_take, List.getElem?_eq_getElem (by omega), Option.getD_some]
  intro l hl
  simp only [mcKeepSet, List.mem_append, List.mem_map] at hl ⊢
  rcases hl with hL | ⟨x, hx, rfl⟩
  · exact Or.inr (Or.inl hL)
  · rw [List.drop_eq_getElem_cons hk_take, hhead, List.mem_cons] at hx
    rcases hx with rfl | hx'
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨x, hx', rfl⟩)

theorem mcKeepSet_push_mono {origTmp tmp : List (BitVec 32)} {tlen keep k : Nat}
    (hk : k < tlen) (hle : tlen ≤ origTmp.length) (hkeep : keep < tmp.length)
    {lit : BitVec 32} (hlit : lit = origTmp[k]?.getD 0#32) :
    ∀ l ∈ mcKeepSet origTmp tlen tmp keep k,
      l ∈ mcKeepSet origTmp tlen (tmp.set keep lit) (keep + 1) (k + 1) := by
  have htk : (tmp.set keep lit).take (keep + 1) = tmp.take keep ++ [lit] := by
    rw [List.take_add_one, List.getElem?_set_self hkeep, Option.toList_some]
    congr 1; exact List.take_set_of_le (le_refl _)
  have hk_take : k < (origTmp.take tlen).length := by simp [List.length_take]; omega
  have hhead : (origTmp.take tlen)[k]'hk_take = lit := by
    rw [List.getElem_take, hlit, List.getElem?_eq_getElem (by omega), Option.getD_some]
  intro l hl
  simp only [mcKeepSet, List.mem_append, List.mem_map, htk, List.map_append] at hl ⊢
  rcases hl with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
  · exact Or.inl (Or.inl ⟨x, hx, rfl⟩)
  · rw [List.drop_eq_getElem_cons hk_take, hhead, List.mem_cons] at hx
    rcases hx with rfl | hx'
    · exact Or.inl (Or.inr (by simp))
    · exact Or.inr ⟨x, hx', rfl⟩

structure SeedInv (c : CorePlusCfg) (s0 : CorePlusState) (orig : List Nat)
    (i : Nat) (mrk : List (BitVec 8)) (mclr : List (BitVec 32))
    (mcl : Nat) (mcf : BitVec 64) : Prop where
  ile : i ≤ s0.tmp_len
  mrk_len : mrk.length = c.mv
  clr_len : mclr.length = c.mv
  clr_le : mcl ≤ c.mv
  no4 : ∀ w < c.mv, mrk[w]?.getD 0#8 ≠ 4#8
  marked : ∀ k < i, mrk[(s0.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#8 = 2#8
  hmin : MinMarkInv c (withMinFields s0 mrk s0.min_stk mclr mcl mcf) orig

theorem min_clause_seed_step {c : CorePlusCfg} {F0 : CNF Nat} {s0 : CorePlusState}
    {orig : List Nat} {i : Nat} {mrk : List (BitVec 8)} {mclr : List (BitVec 32)}
    {mcl : Nat} {mcf : BitVec 64}
    (hcore : CorePlusCoreInv c F0 s0) (hlt : i < s0.tmp_len) (hi_arr : i < s0.tmp.length)
    (horig : orig = (s0.tmp.take s0.tmp_len).map BitVec.toNat)
    (htmp_all : ∀ k < s0.tmp_len, (s0.tmp[k]?.getD 0#32).toNat < 2 * c.mv)
    (htmp_v : s0.vals[(s0.tmp[i]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8)
    (inv : SeedInv c s0 orig i mrk mclr mcl mcf)
    {mrk' : List (BitVec 8)} {mclr' : List (BitVec 32)} {mcl' : Nat} {mcf' : BitVec 64}
    (hbr : let v := s0.tmp[i]'hi_arr >>> 1
      if c.mv ≤ v.toNat ∨ mrk[v.toNat]?.getD 0#8 ≠ 0#8 then
        mrk' = mrk ∧ mclr' = mclr ∧ mcl' = mcl ∧ mcf' = mcf
      else let st' := minMarkState c (withMinFields s0 mrk s0.min_stk mclr mcl mcf) v.toNat 2#8
        mrk' = st'.mrk ∧ mclr' = st'.min_clr ∧ mcl' = st'.min_clr_len ∧ mcf' = st'.min_clr_full) :
    SeedInv c s0 orig (i + 1) mrk' mclr' mcl' mcf' := by
  have hcore_c := hcore.of_minFields (mcf' := mcf) inv.mrk_len hcore.lengths.min_stk_len
    inv.clr_len inv.clr_le
  have hget : s0.tmp[i]'hi_arr = s0.tmp[i]?.getD 0#32 := by
    rw [List.getElem?_eq_getElem hi_arr, Option.getD_some]
  have hv_eq : (s0.tmp[i]'hi_arr >>> 1).toNat = (s0.tmp[i]?.getD 0#32).toNat / 2 := by
    rw [bv32_lshr_1, hget]
  have htmp_l : (s0.tmp[i]?.getD 0#32).toNat < 2 * c.mv := htmp_all i hlt
  have hv_lt : (s0.tmp[i]'hi_arr >>> 1).toNat < c.mv := by omega
  by_cases hskip : c.mv ≤ (s0.tmp[i]'hi_arr >>> 1).toNat ∨
      mrk[(s0.tmp[i]'hi_arr >>> 1).toNat]?.getD 0#8 ≠ 0#8
  · simp only [hskip, ↓reduceIte] at hbr; rcases hbr with ⟨rfl, rfl, rfl, rfl⟩
    have hm2 : mrk'[(s0.tmp[i]?.getD 0#32).toNat / 2]?.getD 0#8 = 2#8 := by
      rcases inv.hmin.mrk_dom _ (by omega : (s0.tmp[i]?.getD 0#32).toNat / 2 < c.mv) with
          h0 | h2 | h4
      · exfalso; rcases hskip with hge | hne
        · omega
        · exact hne (by rw [hv_eq]; exact h0)
      · exact h2
      · exact absurd h4 (inv.no4 _ (by omega))
    refine ⟨hlt, inv.mrk_len, inv.clr_len, inv.clr_le, inv.no4, fun k hk => ?_, inv.hmin⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt' | rfl
    · exact inv.marked k hlt'
    · exact hm2
  · simp only [hskip, ↓reduceIte] at hbr; rcases hbr with ⟨rfl, rfl, rfl, rfl⟩
    have hz : mrk[(s0.tmp[i]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8 :=
      Classical.not_not.mp fun hn => hskip (Or.inr (by rw [hv_eq]; exact hn))
    have hf := minMarkState_facts hcore_c.lengths hv_lt (by rw [hv_eq]; exact hz) 2#8
    have hmem : (s0.tmp[i]?.getD 0#32).toNat ∈ orig := by
      rw [horig, List.mem_map]
      refine ⟨s0.tmp[i]'hi_arr, ?_, congrArg BitVec.toNat hget⟩
      have hi_tk : i < (s0.tmp.take s0.tmp_len).length := by simp [List.length_take]; omega
      rw [← List.getElem_take (i := i) (h := hi_tk)]
      exact List.getElem_mem hi_tk
    have hinv' := minMarkInv_mark_keep hcore_c inv.hmin htmp_l hmem htmp_v hz
    rw [← hv_eq] at hinv'
    refine ⟨hlt, hf.1, hf.2.1, hf.2.2.1, fun w hw => hf.2.2.2.2.2 (by decide) w hw (inv.no4 w hw),
      fun k hk => ?_, hinv'⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt' | rfl
    · have := htmp_all k (Nat.lt_trans hlt' hlt)
      exact hf.2.2.2.2.1 _ (by omega) (inv.marked k hlt')
    · rw [← hv_eq]; exact hf.2.2.2.1

structure FilterInv (c : CorePlusCfg) (s0 : CorePlusState) (keep k : Nat)
    (tmp : List (BitVec 32)) (mrk : List (BitVec 8)) (mstk mclr : List (BitVec 32))
    (mcl : Nat) (mcf : BitVec 64) : Prop where
  hk1 : 1 ≤ keep
  hkle : keep ≤ k
  hk_le : k ≤ s0.tmp_len
  tmp_len : tmp.length = c.mv
  mrk_len : mrk.length = c.mv
  stk_len : mstk.length = 2 * c.minDepth
  clr_len : mclr.length = c.mv
  clr_le : mcl ≤ c.mv
  tmp0 : tmp[0]? = s0.tmp[0]?
  kept : ∀ j, 1 ≤ j → j < keep → ∃ i, 1 ≤ i ∧ i < k ∧ tmp[j]? = s0.tmp[i]?
  tail : ∀ j, k ≤ j → j < s0.tmp_len → tmp[j]? = s0.tmp[j]?
  mrk2 : ∀ j < s0.tmp_len, mrk[(s0.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 2#8
  hmin : MinMarkInv c (withMinTmp s0 tmp mrk mstk mclr mcl mcf)
    (mcKeepSet s0.tmp s0.tmp_len tmp keep k)

theorem min_clause_filter_drop {c : CorePlusCfg} {s0 : CorePlusState} {keep k : Nat}
    {tmp : List (BitVec 32)} {mrk mrk2 : List (BitVec 8)}
    {mstk mstk2 mclr mclr2 : List (BitVec 32)} {mcl mcl2 : Nat} {mcf mcf2 : BitVec 64}
    (inv : FilterInv c s0 keep k tmp mrk mstk mclr mcl mcf)
    (hk_lt : k < s0.tmp_len) (hs0_arr : s0.tmp_len ≤ s0.tmp.length)
    (htmp_all : ∀ j < s0.tmp_len, (s0.tmp[j]?.getD 0#32).toNat < 2 * c.mv)
    (hm2 : mrk2.length = c.mv) (hs2 : mstk2.length = 2 * c.minDepth)
    (hc2 : mclr2.length = c.mv) (hcl2 : mcl2 ≤ c.mv)
    (hp2 : ∀ v < c.mv, mrk[v]?.getD 0#8 = 2#8 → mrk2[v]?.getD 0#8 = 2#8)
    (hok : ∀ keep' : List Nat,
      (∀ l ∈ mcKeepSet s0.tmp s0.tmp_len tmp keep k,
        l = (s0.tmp[k]?.getD 0#32).toNat ∨ l ∈ keep') →
      MinMarkInv c (withMinTmp s0 tmp mrk2 mstk2 mclr2 mcl2 mcf2) keep') :
    FilterInv c s0 keep (k + 1) tmp mrk2 mstk2 mclr2 mcl2 mcf2 := by
  refine ⟨inv.hk1, by have := inv.hkle; omega, hk_lt, inv.tmp_len, hm2, hs2, hc2, hcl2, inv.tmp0,
    fun j hj1 hjk => ?_, fun j hjk hjl => inv.tail j (by omega) hjl,
    fun j hj => ?_, hok _ (mcKeepSet_drop_head hk_lt hs0_arr)⟩
  · obtain ⟨i, hi1, hik, hie⟩ := inv.kept j hj1 hjk; exact ⟨i, hi1, by omega, hie⟩
  · exact hp2 _ (by have := htmp_all j hj; omega) (inv.mrk2 j hj)

theorem min_clause_filter_keep {c : CorePlusCfg} {s0 : CorePlusState} {keep k : Nat}
    {tmp : List (BitVec 32)} {mrk mrk2 : List (BitVec 8)}
    {mstk mstk2 mclr mclr2 : List (BitVec 32)} {mcl mcl2 : Nat} {mcf mcf2 : BitVec 64}
    (inv : FilterInv c s0 keep k tmp mrk mstk mclr mcl mcf)
    (hk_lt : k < s0.tmp_len) (hs0_arr : s0.tmp_len ≤ s0.tmp.length)
    (htlmv : s0.tmp_len ≤ c.mv)
    (htmp_all : ∀ j < s0.tmp_len, (s0.tmp[j]?.getD 0#32).toNat < 2 * c.mv)
    (hm2 : mrk2.length = c.mv) (hs2 : mstk2.length = 2 * c.minDepth)
    (hc2 : mclr2.length = c.mv) (hcl2 : mcl2 ≤ c.mv)
    (hp2 : ∀ v < c.mv, mrk[v]?.getD 0#8 = 2#8 → mrk2[v]?.getD 0#8 = 2#8)
    (hmin2 : MinMarkInv c (withMinTmp s0 tmp mrk2 mstk2 mclr2 mcl2 mcf2)
      (mcKeepSet s0.tmp s0.tmp_len tmp keep k))
    {lit : BitVec 32} (hlit : lit = s0.tmp[k]?.getD 0#32) :
    FilterInv c s0 (keep + 1) (k + 1) (tmp.set keep lit) mrk2 mstk2 mclr2 mcl2 mcf2 := by
  have hk_keep : keep < tmp.length := by have := inv.tmp_len; have := inv.hkle; omega
  have hk_ne0 : 0 ≠ keep := by have := inv.hk1; omega
  refine ⟨by omega, by have := inv.hkle; omega, hk_lt, by simp [inv.tmp_len], hm2, hs2, hc2, hcl2,
    by rw [List.getElem?_set_ne hk_ne0.symm, inv.tmp0], fun j hj1 hjk => ?_,
    fun j hjk hjl => ?_, fun j hj => hp2 _ (by have := htmp_all j hj; omega) (inv.mrk2 j hj), ?_⟩
  · by_cases hje : j = keep
    · subst hje
      exact ⟨k, by have := inv.hk1; have := inv.hkle; omega, by omega,
        by rw [List.getElem?_set_self hk_keep, hlit, List.getElem?_eq_getElem (by omega),
             Option.getD_some]⟩
    · obtain ⟨i, hi1, hik, hie⟩ := inv.kept j hj1 (by omega)
      exact ⟨i, hi1, by omega, by rw [List.getElem?_set_ne (Ne.symm hje), hie]⟩
  · have hne : keep ≠ j := by have := inv.hkle; omega
    rw [List.getElem?_set_ne hne]; exact inv.tail j (by omega) hjl
  · exact minMarkInv_keep_mono (minMarkInv_set_tmp hmin2 (tmp.set keep lit))
      (mcKeepSet_push_mono hk_lt hs0_arr hk_keep hlit)

theorem min_clause_entails {c : CorePlusCfg} {F0 : CNF Nat} {s0 : CorePlusState}
    {keep : Nat} {tmp : List (BitVec 32)} {mrk : List (BitVec 8)}
    {mstk mclr : List (BitVec 32)} {mcl : Nat} {mcf : BitVec 64}
    (hcore : CorePlusCoreInv c F0 (withMinTmp s0 tmp mrk mstk mclr mcl mcf))
    (hs0_arr : s0.tmp_len ≤ s0.tmp.length)
    (horig : F0.EntailsClause (cnfClause ((s0.tmp.take s0.tmp_len).map BitVec.toNat)))
    (htmp_all : ∀ k < s0.tmp_len,
      (s0.tmp[k]?.getD 0#32).toNat < 2 * c.mv ∧
      s0.vals[(s0.tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8)
    (inv : FilterInv c s0 keep s0.tmp_len tmp mrk mstk mclr mcl mcf) :
    F0.EntailsClause (cnfClause ((tmp.take keep).map BitVec.toNat)) := by
  have hkeep_eq : mcKeepSet s0.tmp s0.tmp_len tmp keep s0.tmp_len =
      (tmp.take keep).map BitVec.toNat := by
    unfold mcKeepSet; simp
  have hmin' := inv.hmin
  rw [hkeep_eq] at hmin'
  refine entails_of_minMarkInv hcore hmin' horig fun l hl => ?_
  rw [List.mem_map] at hl
  obtain ⟨x, hx, rfl⟩ := hl
  obtain ⟨j, hj_len, hj_eq⟩ := List.mem_iff_getElem.mp hx
  have hj_tl : j < s0.tmp_len := by simp [List.length_take] at hj_len; omega
  have hxeq : x = s0.tmp[j]?.getD 0#32 := by
    rw [← hj_eq, List.getElem_take, List.getElem?_eq_getElem (by omega), Option.getD_some]
  obtain ⟨hl_lt, hv_ff⟩ := htmp_all j hj_tl
  exact ⟨by rw [hxeq]; exact hl_lt, by rw [hxeq]; exact hv_ff,
    Or.inr (by rw [hxeq]; exact inv.mrk2 j hj_tl)⟩

structure ClearListInv (c : CorePlusCfg) (mrk0 mrk : List (BitVec 8))
    (mclr : List (BitVec 32)) (z mcl : Nat) : Prop where
  zle : z ≤ mcl
  len : mrk.length = c.mv
  pres : ∀ w < c.mv, mrk0[w]?.getD 0#8 = 0#8 → mrk[w]?.getD 0#8 = 0#8
  clrr : ∀ j < z, (mclr[j]?.getD 0#32).toNat < c.mv →
    mrk[(mclr[j]?.getD 0#32).toNat]?.getD 0#8 = 0#8

theorem ClearListInv.step_clr {c : CorePlusCfg} {mrk0 mrk : List (BitVec 8)}
    {mclr : List (BitVec 32)} {z mcl : Nat} (inv : ClearListInv c mrk0 mrk mclr z mcl)
    (hz : z < mcl) (hzi : z < mclr.length) (hcv : (mclr[z]'hzi).toNat < c.mv) :
    ClearListInv c mrk0 (mrk.set (mclr[z]'hzi).toNat 0#8) mclr (z + 1) mcl :=
  ⟨hz, by simp [inv.len], fun u hu hz0 => mrk_set_zero_pres (inv.pres u hu hz0),
   fun j hj hjm => mrk_set_zero_idx (fun q => (mclr[q]?.getD 0#32).toNat) z
     (by have := inv.len; omega)
     (fun hne => inv.clrr j (by omega) hjm)
     fun hje => by subst hje; rw [List.getElem?_eq_getElem hzi, Option.getD_some]⟩

theorem ClearListInv.step_skip {c : CorePlusCfg} {mrk0 mrk : List (BitVec 8)}
    {mclr : List (BitVec 32)} {z mcl : Nat} (inv : ClearListInv c mrk0 mrk mclr z mcl)
    (hz : z < mcl) (hzi : z < mclr.length) (hge : ¬ (mclr[z]'hzi).toNat < c.mv) :
    ClearListInv c mrk0 mrk mclr (z + 1) mcl :=
  ⟨hz, inv.len, inv.pres, fun j hj hjm => by
    by_cases hje : j = z
    · subst hje; rw [List.getElem?_eq_getElem hzi, Option.getD_some] at hjm; exact absurd hjm hge
    · exact inv.clrr j (by omega) hjm⟩

theorem min_clause_clr_clear {c : CorePlusCfg} {mrk0 mrk : List (BitVec 8)}
    {mclr : List (BitVec 32)} {mcl : Nat}
    (inv : ClearListInv c mrk0 mrk mclr mcl mcl)
    (hcov : ∀ w < c.mv, mrk0[w]?.getD 0#8 ≠ 0#8 → ∃ j < mcl, (mclr[j]?.getD 0#32).toNat = w) :
    ∀ w < c.mv, mrk[w]?.getD 0#8 = 0#8 := by
  intro w hw
  by_cases hz : mrk0[w]?.getD 0#8 = 0#8
  · exact inv.pres w hw hz
  · obtain ⟨j, hj, hje⟩ := hcov w hw hz
    rw [← hje]; exact inv.clrr j hj (by rw [hje]; exact hw)

end

end LeanQbe.T.Examples.Kissat.CorePlus
