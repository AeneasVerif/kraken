module

public import LeanQbe.T.Examples.Kissat.Full3
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step
public meta import LeanQbe.T.Logic.Rules

/-!
# Kissat `D-Full` Probing / HBR / Transitive Reduction Helpers (`Stage 4`, Part 1)

Provides:
1. Strictly file-local `FullProbeTransTactics` (`open scoped FullArenaTactics`) with
   context-clearing `ptMemSolve`, `pt_steps`, `pt_steps_nogrp`, `pt_bound`, `pt_call`, and BV
   arithmetic helpers.
2. `FullProbeTransSpecs`: canonical shared Stage-4 invariants (`FullMrkZero`, `FullLitMarksClear`,
   `FullArenaVarsNodup`, `FullLastLearnedWf`, `FullExtScratchOk`, `FullSparseProbeInv`,
   `FullSparseInv`), callee `Spec`s (`9` callees), and target `Spec`s (`6` probing fns in `Full3`).
3. Pure `HbrDomHelpers` (`hbrMarkInv`, `markedTrailCount`, `domReach`,
   `entails_bin_hbr_of_domReach`) and `WatchSliceHelpers`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Strictly scoped tactics and bitvector arithmetic helpers -/

namespace FullProbeTransTactics

open scoped FullArenaTactics

theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_wp {Γ rs Q X e m} (h : wp (rs := rs) Γ Q X e m) : wp Γ Q X e m := h
theorem strip_fwp {as rs Γ f args m Q X}
    (h : Func.wp (as := as) (rs := rs) Γ f args m Q X) : Func.wp Γ f args m Q X := h
theorem pt_wp_head_eq {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {e1 e2 : Expr Val Cont rs} (h : e1 = e2) (hk : wp Γ Q X e2 m) :
    wp Γ Q X e1 m := h ▸ hk
theorem pt_wp_let_head {Γ : Env} {rs sig ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : OpCode sig ts} {args : Tup (Arg Val) sig} {k : Tup Val ts → Expr Val Cont rs}
    {r : Tup Val ts} (hr : ∀ P, P r → c.wp (vals args) P) (hk : wp Γ Q X (k r) m) :
    wp Γ Q X (.let_ (Op.mk c args) k) m := hr _ hk
theorem pt_wp_blocks_here {Γ : Env} {rs ts : List Ty} {sig : List (List Ty)}
    {Q : Post rs} {X : XPost} {m : Mem 64}
    {b : Tup Val ts → Expr Val Cont rs} {bs : Blocks Val Cont rs sig} {xs : Tup Val ts}
    (h : wp Γ Q X (b xs) m) : wp Γ Q X (Blocks.get (Blocks.cons b bs) .here xs) m := h
theorem pt_wp_ret_head {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {xs : Tup (Arg Val) rs} (h : Q (vals xs) m) : wp Γ Q X (.ret xs) m := h
theorem pt_wp_jump_head {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {J : Cont ts} {xs : Tup (Arg Val) ts} (h : J (vals xs) m) : wp Γ Q X (.jump J xs) m := h

scoped macro "pt_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)

scoped macro "pt_head_let" : tactic =>
  `(tactic| (
    apply pt_wp_let_head
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
      try dsimp (config := { zeta := false }) only
      try refine ⟨by decide, ?_⟩
      exact hP))

public meta def ptReduceProjOnce (e : Lean.Expr) : Lean.Expr :=
  e.replace fun sub =>
    match sub with
    | .proj ``Prod 0 arg => if arg.isAppOfArity ``Prod.mk 4 then some (arg.getArg! 2) else none
    | .proj ``Prod 1 arg => if arg.isAppOfArity ``Prod.mk 4 then some (arg.getArg! 3) else none
    | _ =>
      if sub.isAppOfArity ``Prod.fst 3 && sub.appArg!.isAppOfArity ``Prod.mk 4 then
        some (sub.appArg!.getArg! 2)
      else if sub.isAppOfArity ``Prod.snd 3 && sub.appArg!.isAppOfArity ``Prod.mk 4 then
        some (sub.appArg!.getArg! 3)
      else if sub.isAppOf ``Arg.val && sub.getAppNumArgs ≥ 1 then
        let arg := sub.appArg!
        if (arg.isAppOf ``Arg.var || arg.isAppOf ``Arg.imm) && arg.getAppNumArgs ≥ 1 then
          some arg.appArg!
        else none
      else none

public meta def ptNormWpGoal (g : Lean.MVarId) : Lean.Elab.Tactic.TacticM Lean.MVarId := do
  let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData.headBeta
  if ty.isAppOf ``wp && ty.getAppNumArgs == 6 then
    let e := ty.getArg! 4
    let e' := ptReduceProjOnce (ptReduceProjOnce e.headBeta)
    if e' != e then
      let mvar ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar
        (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e'))
      g.assign (← Lean.Meta.mkAppM ``pt_wp_head_eq #[← Lean.Meta.mkEqRefl e', mvar])
      return mvar.mvarId!
  return g

public meta def ptClearStale (m0 : Lean.Expr) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let .fvar mId := m0 | return
    for d in (← Lean.getLCtx).decls.toArray.reverse do
      let some d := d | continue
      let t ← Lean.instantiateMVars d.type
      if t.isAppOf ``Std.ExtHashMap.sep && t.appArg! == m0 then
        try Lean.Elab.Tactic.liftMetaTactic1 fun g => some <$> g.clear d.fvarId catch _ => pure ()
    try Lean.Elab.Tactic.liftMetaTactic1 fun g => some <$> g.clear mId catch _ => pure ()

public meta partial def ptCollectSep (e : Lean.Expr) : Array Lean.Name :=
  if e.isAppOf ``Std.ExtHashMap.sep && e.getAppNumArgs ≥ 2 then
    ptCollectSep (e.getArg! (e.getAppNumArgs - 2)) ++
      ptCollectSep (e.getArg! (e.getAppNumArgs - 1))
  else if let some k := e.getAppFn.constName? then #[k] else #[]

public meta def ptFootprints : Lean.Elab.Tactic.TacticM (Array Lean.Name) :=
  Lean.Elab.Tactic.withMainContext do
    let mut keys : Array Lean.Name := #[]
    for d in (← Lean.getLCtx).decls.toArray.reverse do
      let some d := d | continue
      if d.isImplementationDetail then continue
      let t ← Lean.instantiateMVars d.type
      if t.isAppOf ``Std.ExtHashMap.sep && t.getAppNumArgs ≥ 3 then
        for k in ptCollectSep t.appFn! do
          unless keys.contains k do keys := keys.push k
    return keys

public meta def ptClearBig (g : Lean.MVarId) : Lean.Meta.MetaM Lean.MVarId := do
  let keepHeads : Array Lean.Name := #[
    ``Eq, ``Ne, ``Not, ``LT.lt, ``LE.le, ``GT.gt, ``GE.ge, ``And, ``Or, ``Iff, ``False
  ]
  let toClear ← g.withContext do
    let mut ids : Array Lean.FVarId := #[]
    for d in (← Lean.getLCtx).decls do
      let some d := d | continue
      if d.isAuxDecl || d.isLet then continue
      if ← Lean.Meta.isProp d.type then
        let ty := d.type.consumeMData
        let keep :=
          if ty.isForall then ty.bindingBody!.consumeMData.isConstOf ``False
          else match ty.getAppFn.constName? with
            | some n => keepHeads.contains n
            | none => false
        if !keep then ids := ids.push d.fvarId
    pure ids
  g.tryClearMany toClear

public meta def ptFastFull (isLoad : Bool) (e : Lean.Expr) : Array Lean.Name :=
  let fa (s : String) := Lean.Name.mkStr (``FullArenaTactics.load_full_arena).getPrefix s
  let tbl : Array (Lean.Name × String) := #[
    (``FullCfg.pArena, "full_arena"), (``FullCfg.pMark, "full_mrk"),
    (``FullCfg.pLevel, "full_lvl"), (``FullCfg.pReason, "full_rsns"),
    (``FullCfg.pTrail, "full_trl"), (``FullCfg.pMinClr, "full_min_clr"),
    (``FullCfg.pVals, "full_vals"), (``FullCfg.pWvec, "full_wvec"),
    (``FullCfg.pWstk, "full_wstk"), (``FullCfg.pWorkStk1, "full_work_stk1"),
    (``FullCfg.pWorkStk2, "full_work_stk2"), (``FullCfg.pFlags, "full_flags"),
    (``FullCfg.pLitMark, "full_lit_mark"), (``FullCfg.pTmp, "full_tmp"),
    (``FullCfg.pFrameTrail, "full_frame_trail"), (``FullCfg.pFrameDec, "full_frame_dec")]
  let pre := if isLoad then "load_" else "store_"
  match tbl.find? (fun (c, _) => (e.find? (·.isConstOf c)).isSome) with
  | some (_, suf) => #[fa ("c0_" ++ pre ++ suf), fa (pre ++ suf)]
  | none =>
    if (e.find? (·.isConstOf ``FullCfg.hdr)).isSome then
      let htbl : Array (Nat × String) :=
        if isLoad then #[
          (48, "load_full_arena_len"), (64, "load_full_values_ptr"), (72, "load_full_mark_ptr"),
          (80, "load_full_level_ptr"), (88, "load_full_reason_ptr"), (96, "load_full_trail_ptr"),
          (104, "load_full_watch_vec_ptr"), (112, "load_full_arena_ptr"),
          (120, "load_full_watch_stk_ptr"), (136, "load_full_tmp_lits_ptr"),
          (144, "load_full_trail_end"), (152, "load_full_propagated"),
          (160, "load_full_cur_level"), (168, "load_full_fuel"), (176, "load_full_confl_ref"),
          (184, "load_full_tmp_cnt"), (464, "load_full_wusable"), (520, "load_full_probing"),
          (528, "load_full_confl_type"), (536, "load_full_confl_lit0"),
          (544, "load_full_confl_lit1"), (760, "load_full_oom"), (776, "load_full_cur_vars"),
          (800, "load_full_flags_ptr"), (808, "load_full_lit_mark_ptr"),
          (832, "load_full_frame_trail_ptr"), (840, "load_full_frame_dec_ptr"),
          (848, "load_full_work_stk1_ptr"), (856, "load_full_work_stk2_ptr"),
          (1040, "load_full_hbr_cnt")]
        else #[
          (152, "c0_store_full_propagated"), (160, "c0_store_full_cur_level"),
          (168, "store_full_fuel"), (176, "store_full_confl_ref"), (184, "c0_store_full_tmp_cnt"),
          (464, "store_full_wusable"), (520, "store_full_probing"), (528, "store_full_confl_type"),
          (536, "store_full_confl_lit0"), (544, "store_full_confl_lit1"),
          (760, "store_full_oom"), (1040, "store_full_hbr_cnt")]
      match htbl.find? (fun (n, _) => (e.find? (·.rawNatLit? == some n)).isSome) with
      | some (_, nm) => #[fa nm]
      | none => #[]
    else #[]

public meta def ptTryMemLemma (nm : Lean.Name) (g : Lean.MVarId) :
    Lean.Elab.Tactic.TacticM Bool := do
  let s ← Lean.Elab.Tactic.saveState
  let ok ← try
    let sub ← Lean.Meta.withReducible <|
      g.apply (← Lean.Meta.mkConstWithFreshMVarLevels nm)
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
        Lean.Elab.Tactic.evalTactic
          (← `(tactic| first | rfl | assumption | decide | skip))
        if (← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then continue
        let g' ← ptClearBig (← Lean.Elab.Tactic.getMainGoal)
        Lean.Elab.Tactic.setGoals [g']
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          ((try simp only [List.length_set])
           first | assumption | rfl | decide | omega
                 | (simp only [bv_c0, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv,
                      BitVec.reduceToNat] at *;
                    first | omega | bv_omega | done)
                 | bv_omega)))
        if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then allOk := false
    for g' in sub do if !(← g'.isAssigned) then allOk := false
    pure allOk
  catch _ => pure false
  unless ok do s.restore
  return ok

public meta def ptMemSolve (isLoad : Bool) (g : Lean.MVarId) : Lean.Elab.Tactic.TacticM Unit := do
  Lean.Elab.Tactic.setGoals [g]
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    (try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm])))
  let g ← Lean.Elab.Tactic.getMainGoal
  let ty ← Lean.instantiateMVars (← g.getType)
  let fast := ptFastFull isLoad ty
  for nm in fast do
    if ← ptTryMemLemma nm g then return
  let keys ← ptFootprints
  let env ← Lean.getEnv
  for k in keys do
    for nm in LeanQbe.T.C0Step.c0MemLemmas env isLoad k do
      if ← ptTryMemLemma nm g then return
  throwError "ptMemSolve: failed on {← Lean.Meta.ppExpr ty}"

public meta def ptFindJoinHyp (J : Lean.FVarId) :
    Lean.Elab.Tactic.TacticM (Option Lean.Expr) :=
  Lean.Elab.Tactic.withMainContext do
    for d in (← Lean.getLCtx).decls.toArray.reverse do
      let some d := d | continue
      let ok ← Lean.Meta.forallTelescopeReducing d.type fun xs concl => do
        if xs.size < 1 then return false
        return concl.getAppFn.isFVarOf J && (← Lean.Meta.inferType xs[xs.size - 1]!).isAppOf ``wp
      if ok then return some d.toExpr
    return none

public meta def ptStepOnce (unrollGroup : Bool := true) : Lean.Elab.Tactic.TacticM Bool :=
  Lean.Elab.Tactic.withMainContext do
    let g ← Lean.Elab.Tactic.getMainGoal
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData.headBeta
    if ty.isAppOf ``Func.wp && ty.getAppNumArgs ≥ 4 then
      let f := ty.getArg! 3
      let some c := f.getAppFn.constName? | return false
      Lean.Elab.Tactic.evalTactic
        (← `(tactic| unfold LeanQbe.T.Func.wp $(Lean.mkIdent c):ident))
      return true
    if ty.isAppOf ``wp && ty.getAppNumArgs == 6 then
      let e := (ty.getArg! 4).consumeMData.headBeta
      match e.getAppFn.constName? with
      | some ``Expr.let_ =>
        if e.getAppNumArgs != 6 then return false
        let s ← Lean.Elab.Tactic.saveState
        try
          Lean.Elab.Tactic.evalTactic (← `(tactic| pt_head_let))
          return true
        catch _ => s.restore; return false
      | some ``Expr.load =>
        let g ← ptNormWpGoal g
        Lean.Elab.Tactic.setGoals [g]
        let s ← Lean.Elab.Tactic.saveState
        try
          let [hl, hk] := (← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``wp_load_of)).take 2
            | s.restore; return false
          ptMemSolve true hl
          Lean.Elab.Tactic.setGoals [hk]; return true
        catch _ => s.restore; return false
      | some ``Expr.store =>
        let g ← ptNormWpGoal g
        Lean.Elab.Tactic.setGoals [g]
        let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData.headBeta
        let s ← Lean.Elab.Tactic.saveState
        try
          let m0 := ty.getArg! 5
          let [hs, hk] :=
            (← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``wp_store_sep)).take 2
            | s.restore; return false
          ptMemSolve false hs; Lean.Elab.Tactic.setGoals [hk]
          let mId := Lean.mkIdent `m; let hmId := Lean.mkIdent `hm
          Lean.Elab.Tactic.evalTactic (← `(tactic| intro $mId:ident $hmId:ident;
            try simp only [Arg.val_var, Arg.val_imm, Std.ExtHashMap.sep_emp] at $hmId:ident))
          ptClearStale m0; return true
        catch _ => s.restore; return false
      | some ``Expr.jnz =>
        let g ← ptNormWpGoal g
        Lean.Elab.Tactic.setGoals [g]
        let hc := Lean.mkIdent `hc
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          (refine wp_jnz_of (fun $hc:ident => ?_) (fun $hc:ident => ?_)) <;> (
            try simp only [Arg.val_var, Arg.val_imm] at $hc:ident; c0_cond $hc
            try simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceDiv,
              BitVec.reduceToNat] at $hc:ident
            try (first | exact ($hc).elim | exact absurd rfl $hc | exact $hc rfl
                       | exact absurd trivial $hc))))
        return true
      | some ``Expr.ret =>
        let g ← ptNormWpGoal g
        Lean.Elab.Tactic.setGoals [g]
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          (apply pt_wp_ret_head; simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm])))
        return true
      | some ``Expr.jump =>
        let g ← ptNormWpGoal g
        Lean.Elab.Tactic.setGoals [g]
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          (apply pt_wp_jump_head; simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm])))
        return true
      | some ``Expr.group =>
        if unrollGroup && e.getAppNumArgs == 6 then
          if let .lam _ _ b _ := e.getArg! 4 then
            if !b.hasLooseBVars then
              let J := Lean.mkIdent `J; let hJ := Lean.mkIdent `hJ
              Lean.Elab.Tactic.evalTactic (← `(tactic|
                refine wp_unroll_group fun $J:ident $hJ:ident => ?_))
              return true
        return false
      | some ``Blocks.get =>
        let s ← Lean.Elab.Tactic.saveState
        try
          Lean.Elab.Tactic.evalTactic (← `(tactic| apply pt_wp_blocks_here))
          return true
        catch _ => s.restore; return false
      | _ => return false
    if let .fvar J := ty.getAppFn then
      if let some h ← ptFindJoinHyp J then
        Lean.Elab.Tactic.setGoals (← (← g.apply h).mapM ptNormWpGoal)
        return true
    return false

public meta partial def ptStepsLoop (unrollGroup : Bool) (fuel : Nat) :
    Lean.Elab.Tactic.TacticM Unit := do
  if fuel = 0 then return
  let mut out : Array Lean.MVarId := #[]
  for g in (← Lean.Elab.Tactic.getUnsolvedGoals) do
    if ← g.isAssigned then continue
    Lean.Elab.Tactic.setGoals [g]
    if ← ptStepOnce unrollGroup then ptStepsLoop unrollGroup (fuel - 1)
    out := out ++ (← Lean.Elab.Tactic.getUnsolvedGoals)
  Lean.Elab.Tactic.setGoals out.toList

scoped elab "pt_steps" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| try (first | refine strip_fwp ?_ | refine strip_wp ?_)))
  ptStepsLoop true 2000

scoped elab "pt_steps_nogrp" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| try (first | refine strip_fwp ?_ | refine strip_wp ?_)))
  ptStepsLoop false 2000

scoped elab "pt_step" : tactic => do
  unless ← ptStepOnce true do throwError "pt_step: no step applies"

scoped elab "pt_bound" : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| first | assumption | rfl | decide | skip))
  if (← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then return
  let g' ← ptClearBig (← Lean.Elab.Tactic.getMainGoal)
  Lean.Elab.Tactic.setGoals [g']
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    ((try simp only [List.length_set])
     first | assumption | rfl | decide | omega
           | (simp only [bv_c0, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv,
                BitVec.reduceToNat] at *;
              first | assumption | rfl | decide | omega | bv_omega | done)
           | bv_omega)))

scoped elab "pt_clear_big" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic1 fun g => some <$> ptClearBig g

scoped macro "pt_call" h:term : tactic =>
  `(tactic| (refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_)))

end FullProbeTransTactics

namespace FullProbeTransHelpers

section Helpers

theorem bv32_sle0_eq_not_slt0 (x : BitVec 32) : (0#32).sle x = !(x.slt 0#32) := by
  simp only [BitVec.sle, BitVec.slt]
  change decide (0 ≤ x.toInt) = !decide (x.toInt < 0)
  by_cases h : x.toInt < 0 <;> simp [h, show (0 ≤ x.toInt) ↔ ¬(x.toInt < 0) by omega]

theorem bv64_sub1_toNat {f : BitVec 64} (hf : f ≠ 0#64) :
    (f - 1#64).toNat = f.toNat - 1 := by
  have hpos : 0 < f.toNat := Nat.pos_of_ne_zero fun h0 =>
    hf (BitVec.eq_of_toNat_eq (by simpa using h0))
  bv_omega

theorem bv64_add1_toNat {f : BitVec 64} (hf : f.toNat + 1 < 2 ^ 64) :
    (f + 1#64).toNat = f.toNat + 1 := by bv_omega

theorem bv32_add1_toNat {f : BitVec 32} (hf : f.toNat + 1 < 2 ^ 32) :
    (f + 1#32).toNat = f.toNat + 1 := by bv_omega

theorem bv32_toNat_lshr1 (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv32_toNat_xor1 (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by
  simp [BitVec.toNat_xor]

theorem bv32_mask7f_toNat_lt {x : BitVec 32} (hx : x.toNat < 0x80000000) :
    (x &&& 0x7FFFFFFF#32).toNat = x.toNat := by
  have h : x &&& 0x7FFFFFFF#32 = x := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  rw [h]

theorem bv32_mask7f_msb_zero (x : BitVec 32) :
    ((x &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 := by
  ext i hi
  have hm : (0x7FFFFFFF#32 &&& 0x80000000#32 : BitVec 32) = 0#32 := by decide
  have hi_m := congrArg (·[i]) hm
  simp only [BitVec.getElem_and, BitVec.getElem_zero] at hi_m ⊢
  cases h7 : (0x7FFFFFFF#32)[i] <;> cases h8 : (0x80000000#32)[i] <;> simp_all

private theorem bv32_msb_true : (0x80000000#32)[31] = true := by decide
private theorem bv32_mask7f_msb : (0x7FFFFFFF#32)[31] = false := by decide

theorem bv32_set_bin_watch_spec {l : BitVec 32} (hl : l.toNat < 0x7FFFFFFF) :
    let w := (l &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    (w &&& 0x80000000#32) ≠ 0#32 ∧ w ≠ 0xFFFFFFFF#32 ∧
    (w &&& 0x7FFFFFFF#32).toNat = l.toNat := by
  have hm : (l &&& 0x7FFFFFFF#32) = l := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have h1 : ((l ||| 0x80000000#32) &&& 0x80000000#32) ≠ 0#32 := by
    intro hc; have hb := congrArg (·[31]) hc; revert hb; simp [bv32_msb_true]
  have h2 : (l ||| 0x80000000#32) &&& 0x7FFFFFFF#32 = l := by
    ext i hi
    by_cases hi31 : i = 31
    · subst hi31
      have hl31 : l[31] = false := by
        rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq,
          Nat.div_eq_of_lt (by omega)]
        simp
      simp [hl31, bv32_mask7f_msb]
    · have hm0 : (0x80000000#32)[i] = false := by
        rw [BitVec.getElem_eq_testBit_toNat,
          show (0x80000000#32).toNat = 2 ^ 31 from rfl, Nat.testBit_two_pow]
        exact decide_eq_false (Ne.symm hi31)
      have hm1 : (0x7FFFFFFF#32)[i] = true := by
        rw [BitVec.getElem_eq_testBit_toNat,
          show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl, Nat.testBit_two_pow_sub_one]
        exact decide_eq_true (by omega)
      simp [hm0, hm1]
  have h3 : l ||| 0x80000000#32 ≠ 0xFFFFFFFF#32 := by
    intro heq
    have hlo : ((l ||| 0x80000000#32) &&& 0x7FFFFFFF#32) =
        (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32) := congrArg (· &&& 0x7FFFFFFF#32) heq
    rw [h2] at hlo
    have hv := congrArg BitVec.toNat hlo
    have hff : (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat = 0x7FFFFFFF := rfl
    omega
  simpa [hm] using ⟨h1, h3, congrArg BitVec.toNat h2⟩

theorem bv64_shl1_toNat {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mod_eq_of_lt hx]

theorem i8_vals_slt0 {x : BitVec 8} (hx : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (x.signExtend 32).slt 0#32 = true ↔ x = 0xFF#8 := by
  rcases hx with rfl | rfl | rfl <;> decide

theorem i8_vals_sgt0 {x : BitVec 8} (hx : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (0#32).slt (x.signExtend 32) = true ↔ x = 1#8 := by
  rcases hx with rfl | rfl | rfl <;> decide

theorem i8_vals_sge0 {x : BitVec 8} (hx : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (0#32).sle (x.signExtend 32) = true ↔ x ≠ 0xFF#8 := by
  rcases hx with rfl | rfl | rfl <;> decide

end Helpers

end FullProbeTransHelpers

/-! ## 2. Canonical Stage-4 invariants and `FullProbeTransSpecs` -/

namespace FullProbeTransSpecs

/-- Variable marks (`mrk[0 ..< max_vars]`) are cleared to `0#8`. -/
@[expose] def FullMrkZero (c : FullCfg) (s : FullState) : Prop :=
  ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8

/-- Both variable marks (`mrk`) and literal marks (`lit_mark`) are cleared to `0#8`. -/
@[expose] def FullLitMarksClear (c : FullCfg) (s : FullState) : Prop :=
  FullMrkZero c s ∧ (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)

/-- Every non-garbage clause in `arena` has distinct variable indices. -/
@[expose] def FullArenaVarsNodup (s : FullState) : Prop :=
  ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false →
    ((fullArenaClauseLits s r).map (· / 2)).Nodup

/-- Every non-sentinel slot of `scratch.last_learned[0..8)` points to a valid clause block. -/
@[expose] def FullLastLearnedWf (s : FullState) : Prop :=
  ∀ i < 8, let cr := s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32
    cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ fullArenaClauseRefs s

/-- Combined `last_learned` + `extend_len` scratch side-conditions. -/
@[expose] def FullExtScratchOk (c : FullCfg) (s : FullState) : Prop :=
  FullLastLearnedWf s ∧ s.scratch.extend_len ≤ c.extend_cap

/-- Scratch-level equality predicate preserving `last_learned` and `extend_len`. -/
@[expose] def FullExtScratchPres (s s' : FullState) : Prop :=
  s'.scratch.last_learned = s.scratch.last_learned ∧
  s'.scratch.extend_len = s.scratch.extend_len

/-- Extended scratch-frame predicate preserved by `full_backtrack`, `full_propagate*`,
and `full_add_unit` for probing and transitive callers. -/
@[expose] def FullProbeScratchPres (s s' : FullState) : Prop :=
  FullExtScratchPres s s' ∧
  s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
  s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
  s'.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
  s'.scratch.ant_sz = s.scratch.ant_sz ∧
  s'.scratch.res_sz = s.scratch.res_sz ∧
  s'.scratch.sim_sig = s.scratch.sim_sig

/-- Sparse probing invariant allowing temporary `lit_mark` marks during `assume_pair`. -/
@[expose] def FullSparseProbeInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullMrkZero c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

/-- Canonical Stage-4 sparse 2WL solver invariant (`dense_mode = 0`). -/
@[expose] def FullSparseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

/-- Explicit-witness sparse-mode invariant (`FullSparseInv c F0 s ↔ ∃ F_cur, ...`). -/
@[expose]
def FullSparseInvW (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
  FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

/-- Trail-prefix and assigned-level preservation across BCP (`full_propagate`). -/
@[expose] def FullTrailExt (k k' : FullCoreState) : Prop :=
  k.trail_end ≤ k'.trail_end ∧
  (∀ i < k.trail_end, k'.trl[i]? = k.trl[i]?) ∧
  (∀ i < k.trail_end,
    k'.lvl[(k.trl[i]?.getD 0#32).toNat / 2]? = k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?)

/-- Arena clause-ref and literal-permutation preservation (`full_propagate`). -/
@[expose] def FullArenaPermEq (k k' : FullCoreState) : Prop :=
  k'.arena_len = k.arena_len ∧
  fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
  ∀ r ∈ fullArenaClauseRefsCore k,
    fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
    fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
    (fullArenaClauseLitsCore k' r).Perm (fullArenaClauseLitsCore k r)

/-- Transitive trail-extension witness on `FullCoreState`. -/
structure TrailExtCore (k k' : FullCoreState) : Prop where
  te_ge : k.trail_end ≤ k'.trail_end
  trl_pref : ∀ i < k.trail_end, k'.trl[i]? = k.trl[i]?
  lvl_pres : ∀ i < k.trail_end,
    k'.lvl[(k.trl[i]?.getD 0#32).toNat / 2]? = k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?
  new_lvl : ∀ i, k.trail_end ≤ i → i < k'.trail_end →
    (k'.lvl[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level

theorem TrailExtCore.refl (k : FullCoreState) : TrailExtCore k k :=
  ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl, fun _ h1 h2 => by omega⟩

theorem TrailExtCore.trans {k k1 k2 : FullCoreState}
    (h1 : TrailExtCore k k1) (h2 : TrailExtCore k1 k2) (hcl : k1.cur_level = k.cur_level) :
    TrailExtCore k k2 := by
  refine ⟨Nat.le_trans h1.te_ge h2.te_ge,
    fun i hi => (h2.trl_pref i (by have := h1.te_ge; omega)).trans (h1.trl_pref i hi),
    fun i hi => ?_, fun i hi1 hi2 => ?_⟩
  · have hlt1 : i < k1.trail_end := by have := h1.te_ge; omega
    have htr := h1.trl_pref i hi
    have h2l := h2.lvl_pres i hlt1
    rw [htr] at h2l
    exact h2l.trans (h1.lvl_pres i hi)
  · by_cases hi : i < k1.trail_end
    · rw [h2.trl_pref i hi, h2.lvl_pres i hi]
      exact h1.new_lvl i hi1 hi
    · rw [← hcl]; exact h2.new_lvl i (by omega) hi2

/-- HBR binary pairs buffered in `work_stk2[0 ..< 2 * n)` during level-1 probing. -/
@[expose] def FullHbrBufOkW (F_cur : List (List Nat)) (s : FullState) (n : Nat) : Prop :=
  n ≤ s.core.cur_vars ∧
  ∀ i < n,
    let a := (s.scratch.work_stk2[2 * i]?.getD 0#32).toNat
    let b := (s.scratch.work_stk2[2 * i + 1]?.getD 0#32).toNat
    a < 2 * s.core.cur_vars ∧ b < 2 * s.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [a, b])

/-- Explicit-witness conflict predicate (`FullConflictOkW F_cur s`). -/
@[expose] def FullConflictOkW (F_cur : List (List Nat)) (s : FullState) : Prop :=
  (s.core.confl_type = 1#64 ∧
    s.core.confl_lit0.toNat < 2 * s.core.cur_vars ∧
    s.core.confl_lit1.toNat < 2 * s.core.cur_vars ∧
    s.core.vals[s.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
    s.core.vals[s.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8 ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [s.core.confl_lit0.toNat, s.core.confl_lit1.toNat])) ∨
  (s.core.confl_type = 2#64 ∧
    s.core.confl_ref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s s.core.confl_ref.toNat = false ∧
    ∀ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8)

/-- Relaxed `FullWitnessInv` allowing OTFS-modified `rsns` at `cur_level` before level-0 BT. -/
structure FullOtfsWitnessInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (k : FullCoreState) : Prop where
  ext_sound : ExtUnsatSound F0 k.cur_vars F_cur
  inconsistent_sound : k.inconsistent ≠ 0#64 → (cnfOfClauses F_cur).Unsat
  arena : FullArenaClausesInv c F_cur k
  watches : ModeWatchesInv F_cur k
  cur_level_le : k.cur_level ≤ k.trail_end
  trail_lits_lt : ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat < 2 * k.cur_vars
  trail_vars_nodup : ∀ i j, i < k.trail_end → j < k.trail_end →
    (k.trl[i]?.getD 0#32).toNat / 2 = (k.trl[j]?.getD 0#32).toNat / 2 → i = j
  vals_domain : ∀ l < 2 * k.cur_vars,
    k.vals[l]?.getD 0#8 = 0#8 ∨ k.vals[l]?.getD 0#8 = 1#8 ∨ k.vals[l]?.getD 0#8 = 0xFF#8
  vals_true_iff : ∀ l < 2 * k.cur_vars,
    k.vals[l]?.getD 0#8 = 1#8 ↔ ∃ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat = l
  vals_false_iff : ∀ l < 2 * k.cur_vars,
    k.vals[l]?.getD 0#8 = 0xFF#8 ↔ ∃ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat = l ^^^ 1
  lvl_le : ∀ i < k.trail_end,
    (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ k.cur_level
  dec_earliest : ∀ i j, i < k.trail_end → j < k.trail_end →
    (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
      (k.lvl[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
    0 < (k.lvl[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
    k.rsns[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 → j ≤ i
  levels_inhabited : ∀ L, 1 ≤ L → L ≤ k.cur_level →
    ∃ i < k.trail_end, (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L
  level0_sound : ∀ i < k.trail_end,
    (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
    (cnfOfClauses F_cur).EntailsClause (cnfClause [(k.trl[i]?.getD 0#32).toNat])
  trail_pos_inv : ∀ i < k.trail_end,
    (k.trail_pos[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = i
  level0_rsn_none : ∀ idx < k.trail_end,
    (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
    k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
  frame_trail_lt : ∀ L ≤ k.cur_level, (k.frame_trail[L]?.getD 0#32).toNat ≤ k.trail_end
  frame_trail_mono : ∀ L1 L2, L1 ≤ L2 → L2 ≤ k.cur_level →
    (k.frame_trail[L1]?.getD 0#32).toNat ≤ (k.frame_trail[L2]?.getD 0#32).toNat
  frame_trail_before_lt : ∀ L, 1 ≤ L → L ≤ k.cur_level →
    ∀ i < (k.frame_trail[L]?.getD 0#32).toNat,
      (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < L
  frame_dec_lt : ∀ L, 1 ≤ L → L ≤ k.cur_level →
    (k.frame_dec[L]?.getD 0#32).toNat < 2 * k.cur_vars
  reason_inv_below : ∀ idx < k.trail_end,
    let p := (k.trl[idx]?.getD 0#32).toNat
    let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
    (k.lvl[p / 2]?.getD 0#32).toNat < k.cur_level →
    rsn ≠ 0xFFFFFFFF#32 →
    if (rsn &&& 0x80000000#32) ≠ 0#32 then
      let ot := (rsn &&& 0x7FFFFFFF#32).toNat
      ot < 2 * k.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [p, ot]) ∧
      ∃ m < idx, (k.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
        (k.lvl[ot / 2]?.getD 0#32).toNat ≤ (k.lvl[p / 2]?.getD 0#32).toNat
    else
      rsn.toNat ∈ fullArenaClauseRefsCore k ∧ fullArenaClauseGarbCore k rsn.toNat = false ∧
      ∀ q ∈ fullArenaClauseLitsCore k rsn.toNat,
        q = p ∨ ∃ m < idx, (k.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
          (k.lvl[q / 2]?.getD 0#32).toNat ≤ (k.lvl[p / 2]?.getD 0#32).toNat
  reason_lit_mem_below : ∀ idx < k.trail_end,
    let p := (k.trl[idx]?.getD 0#32).toNat
    let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
    (k.lvl[p / 2]?.getD 0#32).toNat < k.cur_level →
    rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
    p ∈ fullArenaClauseLitsCore k rsn.toNat

/-- Explicit-witness OTFS invariant (`FullSparseInvW.toOtfs`). -/
@[expose]
def FullOtfsInvW (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullOtfsWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
  FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

theorem FullWitnessInv.toOtfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullWitnessInv c F0 F_cur k) : FullOtfsWitnessInv c F0 F_cur k :=
  { ext_sound := h.ext_sound, inconsistent_sound := h.inconsistent_sound, arena := h.arena
    watches := h.watches, cur_level_le := h.cur_level_le, trail_lits_lt := h.trail_lits_lt
    trail_vars_nodup := h.trail_vars_nodup, vals_domain := h.vals_domain
    vals_true_iff := h.vals_true_iff, vals_false_iff := h.vals_false_iff, lvl_le := h.lvl_le
    dec_earliest := h.dec_earliest, levels_inhabited := h.levels_inhabited
    level0_sound := h.level0_sound, trail_pos_inv := h.trail_pos_inv
    level0_rsn_none := h.level0_rsn_none, frame_trail_lt := h.frame_trail_lt
    frame_trail_mono := h.frame_trail_mono, frame_trail_before_lt := h.frame_trail_before_lt
    frame_dec_lt := h.frame_dec_lt
    reason_inv_below := fun idx hi _ hne => h.reason_inv idx hi hne
    reason_lit_mem_below := fun idx hi _ hne hlg => h.reason_lit_mem idx hi hne hlg }

theorem FullOtfsWitnessInv.toWitness_of_level0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (h : FullOtfsWitnessInv c F0 F_cur k)
    (hl0 : k.cur_level = 0) : FullWitnessInv c F0 F_cur k :=
  { ext_sound := h.ext_sound, inconsistent_sound := h.inconsistent_sound, arena := h.arena
    watches := h.watches, cur_level_le := h.cur_level_le, trail_lits_lt := h.trail_lits_lt
    trail_vars_nodup := h.trail_vars_nodup, vals_domain := h.vals_domain
    vals_true_iff := h.vals_true_iff, vals_false_iff := h.vals_false_iff, lvl_le := h.lvl_le
    dec_earliest := h.dec_earliest, levels_inhabited := h.levels_inhabited
    level0_sound := h.level0_sound, trail_pos_inv := h.trail_pos_inv
    level0_rsn_none := h.level0_rsn_none, frame_trail_lt := h.frame_trail_lt
    frame_trail_mono := h.frame_trail_mono, frame_trail_before_lt := h.frame_trail_before_lt
    frame_dec_lt := h.frame_dec_lt
    reason_inv := fun idx hi hne =>
      absurd (h.level0_rsn_none idx hi (by have := h.lvl_le idx hi; omega)) hne
    reason_lit_mem := fun idx hi hne _ =>
      absurd (h.level0_rsn_none idx hi (by have := h.lvl_le idx hi; omega)) hne }

theorem FullOtfsInvW.toSparse_of_level0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullOtfsInvW c F0 F_cur s) (hl0 : s.core.cur_level = 0) :
    FullSparseInvW c F0 F_cur s :=
  ⟨h.1, h.2.1.toWitness_of_level0 hl0, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem level0_unsat_of_conflict_okW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hl0 : s.core.cur_level = 0)
    (hc : FullConflictOkW F_cur s) : F0.Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine hw.ext_sound.2 (unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    right; rcases hl with rfl | rfl
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hl0 := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
      simpa [litNeg, heq, Nat.xor_assoc] using hl0
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hl0 := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
      simpa [litNeg, heq, Nat.xor_assoc] using hl0
  · refine hw.ext_sound.2
      (unsat_of_entails_nil (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => ?_))
    right
    obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l (hw.arena.lits_lt _ href hng l hl)).mp (hfals l hl)
    simpa [litNeg, heq, Nat.xor_assoc] using hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)

/-! ### 2.1 Callee `Spec` contracts (`9` callees) -/

@[expose] def fullFindReplSpec : Spec [i64, i64] [i64] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ cref.toNat + 3 ≤ s.core.arena_len ∧
    3 ≤ fullArenaClauseSize s cref.toNat ∧
    cref.toNat + 3 + fullArenaClauseSize s cref.toNat ≤ s.core.arena_len ∧
    (FullMem c s ⋆ R) m ∧
    ((∀ k, 2 ≤ k → k < fullArenaClauseSize s cref.toNat →
        let cand := (s.core.arena[cref.toNat + 3 + k]?.getD 0#32).toNat
        2 * s.core.cur_vars ≤ cand ∨
        ((s.core.vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = true) →
      Q (0xFFFFFFFF#64, ()) m) ∧
    (∀ (r : Nat) (m' : Mem 64),
      2 ≤ r → r < fullArenaClauseSize s cref.toNat →
      (let cand := (s.core.arena[cref.toNat + 3 + r]?.getD 0#32).toNat
       cand < 2 * s.core.cur_vars ∧
       ((s.core.vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = false) →
      (FullMem c
        { s with core := { s.core with
          arena := s.core.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r) } } ⋆ R) m' →
      Q (BitVec.ofNat 64 r, ()) m')

@[expose] def fullWatchPushSpec : Spec [i64, i32, i32, i32, i32] [.bool] :=
  fun (h, lit, w0, w1, cnt, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧
      (cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32) ∧
      (cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) wvec' wstk' wlen' wusable' wsort' m',
        let s' : FullState :=
          { s with
            core := { s.core with
              wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
            scratch := { s.scratch with wsort := wsort' } }
        s'.LengthsOk c → WatchStackLayout s'.core →
        (∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
          fullWatchSize s' l = fullWatchSize s l ∧
          ∀ k < fullWatchSize s l,
            s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
        (ok = true →
          lit.toNat < 2 * s.core.cur_vars ∧ (cnt.toNat = 1 ∨ cnt.toNat = 2) ∧
          fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat + cnt.toNat ∧
          (∀ k < fullWatchSize s lit.toNat,
            s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
              s.core.wstk[fullWatchOff s lit.toNat + k]?) ∧
          s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat]? = some w0 ∧
          (cnt.toNat = 2 →
            s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat + 1]? = some w1)) →
        (ok = false →
          (lit.toNat < 2 * s.core.cur_vars →
            fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat ∧
            ∀ k < fullWatchSize s lit.toNat,
              s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
                s.core.wstk[fullWatchOff s lit.toNat + k]?) ∧
          (2 * s.core.cur_vars ≤ lit.toNat ∨ (cnt.toNat ≠ 1 ∧ cnt.toNat ≠ 2) ∨
            s' = s ∨ wusable' = 0#64)) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullAssignLvlSpec : Spec [i64, i32, i32, i32] [] :=
  fun (h, lit, rsn, alvl, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      if s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
          s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8 then
        Q () m
      else
        let v := lit.toNat / 2
        let rsn' := if alvl = 0#32 then 0xFFFFFFFF#32 else rsn
        let unfl' := if alvl = 0#32 then s.core.unflushed + 1#64 else s.core.unflushed
        ∀ flags' unass' phases' m',
          flags'.length = c.max_vars → phases'.length = c.max_vars →
          let s' : FullState :=
            { s with
              core := { s.core with
                vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                flags := flags', lvl := s.core.lvl.set v alvl, rsns := s.core.rsns.set v rsn'
                trl := s.core.trl.set s.core.trail_end lit
                trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
                trail_end := s.core.trail_end + 1
                unassigned := unass', unflushed := unfl' }
              scratch := { s.scratch with phases := phases' } }
          (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullAssignSpec : Spec [i64, i32, i32] [] := fun (h, lit, rsn, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level < 2 ^ 32 ∧ (FullMem c s ⋆ R) m ∧
    if s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
        s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8 then
      Q () m
    else
      let v := lit.toNat / 2
      let rsn' := if s.core.cur_level = 0 then 0xFFFFFFFF#32 else rsn
      let unfl' := if s.core.cur_level = 0 then s.core.unflushed + 1#64 else s.core.unflushed
      ∀ flags' unass' phases' m',
        flags'.length = c.max_vars → phases'.length = c.max_vars →
        let s' : FullState :=
          { s with
            core := { s.core with
              vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
              flags := flags', lvl := s.core.lvl.set v (BitVec.ofNat 32 s.core.cur_level)
              rsns := s.core.rsns.set v rsn', trl := s.core.trl.set s.core.trail_end lit
              trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
              trail_end := s.core.trail_end + 1
              unassigned := unass', unflushed := unfl' }
            scratch := { s.scratch with phases := phases' } }
        (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullBacktrackSpec : Spec [i64, i64] [] := fun (h, target_lvl, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level < 2 ^ 64 ∧
    (target_lvl.toNat < s.core.cur_level → target_lvl.toNat < c.max_vars) ∧
    (∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with
            vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
            trail_end := te', propagated := prop', cur_level := cl', unassigned := unass' }
          scratch := sc' }
      s'.LengthsOk c → te' ≤ s.core.trail_end → prop' ≤ te' →
      cl' = min s.core.cur_level target_lvl.toNat → FullProbeScratchPres s s' →
      sc'.shrink_stk = s.scratch.shrink_stk →
      (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      ((∃ F0 F_cur, FullWitnessInv c F0 F_cur s.core ∨ FullOtfsWitnessInv c F0 F_cur s.core) →
        (∀ l < 2 * s.core.cur_vars,
          vals'[l]?.getD 0#8 =
            if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat then
              s.core.vals[l]?.getD 0#8 else 0#8) ∧
        (∀ i < s.core.trail_end, let v := (s.core.trl[i]?.getD 0#32).toNat / 2
          lvl'[v]?.getD 0#32 =
            if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat then
              s.core.lvl[v]?.getD 0#32 else 0#32)) →
      (∀ F0 F_cur, FullWitnessInv c F0 F_cur s.core → target_lvl.toNat ≤ s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (∀ F0 F_cur, FullOtfsWitnessInv c F0 F_cur s.core → target_lvl.toNat < s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullPropagateSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m',
      let s' : FullState :=
        { s with
          core := { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
            unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
            wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
          scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                      phases := phases' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s') →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullAnalyzeSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ FullConflictOkW F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullAnalyze20Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ FullConflictOkW F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s') →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullAddBinSpec : Spec [i64, i32, i32] [i64] := fun (h, a, b, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ s.core.cur_level = 0 ∧
    (a.toNat < 2 * s.core.cur_vars → b.toNat < 2 * s.core.cur_vars →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat])) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb' oom' inc'
      phases' wsort' m',
      let s' : FullState :=
        { s with
          core := { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
            wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
            oom := oom', inconsistent := inc' }
          scratch := { s.scratch with phases := phases', wsort := wsort' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat ∧ inc' ≠ 0#64) →
      (r = 2#64 → oom' ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullAddUnitSpec : Spec [i64, i32] [.bool] := fun (h, lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    (lit.toNat < 2 * s.core.cur_vars →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat])) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
      phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m',
      let s' : FullState :=
        { s with
          core := { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', propagated := prop', cur_level := cl',
            unassigned := unass', unflushed := unfl', inconsistent := inc' }
          scratch := { s.scratch with phases := phases', target_assigned := ta',
                                      best_assigned := ba', phases_target := pt',
                                      phases_best := pb', heap := hp', pos := ps',
                                      heap_len := hl', q_search_idx := qsi',
                                      q_search_stamp := qss' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → cl' = 0 →
      (lit.toNat < 2 * s.core.cur_vars → ok = false → F0.Unsat ∧ inc' ≠ 0#64) →
      (ok = false → 2 * s.core.cur_vars ≤ lit.toNat ∨ (F0.Unsat ∧ inc' ≠ 0#64)) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-! ### 2.2 Target `Spec` contracts for the `6` shard functions (`Full3` #10–15) -/

@[expose] def fullHbrDomSpec : Spec [i64, i32, i32] [i32] := fun (h, cref, implied, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧
    (∃ wv ws wl, FullWitnessInv c F0 F_cur { s.core with wvec := wv, wstk := ws, wlen := wl }) ∧
    FullMrkZero c s ∧ s.core.cur_level = 1 ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s cref.toNat = false ∧ implied.toNat ∈ fullArenaClauseLits s cref.toNat ∧
    (∀ l ∈ fullArenaClauseLits s cref.toNat,
      l ≠ implied.toNat → s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ dom mrk' mclr' m',
      let s' : FullState := { s with core := { s.core with mrk := mrk', min_clr := mclr' } }
      s'.LengthsOk c → FullMrkZero c s' →
      (dom = 0xFFFFFFFF#32 ∨ (dom.toNat < 2 * s.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [dom.toNat ^^^ 1, implied.toNat]))) →
      (FullMem c s' ⋆ R) m' → Q (dom, ()) m'

@[expose] def fullProbePropLitSpec : Spec [i64, i32] [.bool] := fun (h, _lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullMrkZero c s ∧
    FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64 ∧
    s.core.cur_level = 1 ∧ s.core.oom = 0#64 ∧ FullHbrBufOkW F_cur s s.core.tmp_cnt ∧
    (FullMem c s ⋆ R) m ∧ ∀ (ok : Bool) s' m',
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullMrkZero c s' →
      FullArenaVarsNodup s' → FullExtScratchOk c s' → s'.core.dense_mode = 0#64 →
      s'.core.cur_level = 1 → s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.core.lit_mark = s.core.lit_mark → s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s.core.trail_end ≤ s'.core.trail_end → FullHbrBufOkW F_cur s' s'.core.tmp_cnt →
      (ok = false → s'.core.oom ≠ 0#64 ∨ FullConflictOkW F_cur s') →
      (ok = true → s'.core.oom = 0#64) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullProbePropSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullMrkZero c s ∧
    FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64 ∧
    s.core.cur_level = 1 ∧ FullHbrBufOkW F_cur s s.core.tmp_cnt ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m', s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullMrkZero c s' →
      FullArenaVarsNodup s' → FullExtScratchOk c s' → s'.core.dense_mode = 0#64 →
      s'.core.cur_level = 1 → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.lit_mark = s.core.lit_mark →
      s'.scratch.work_stk1 = s.scratch.work_stk1 → FullHbrBufOkW F_cur s' s'.core.tmp_cnt →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) → (r = 1#64 → FullConflictOkW F_cur s') →
      (r = 0#64 → s'.core.propagated = s'.core.trail_end) → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullProbeFlushHbrSpec : Spec [i64, i64] [i64] := fun (h, hbr_n, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullMrkZero c s ∧
    FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64 ∧
    s.core.cur_level = 0 ∧ FullHbrBufOkW F_cur s hbr_n.toNat ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m', s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullMrkZero c s' →
      FullArenaVarsNodup s' → FullExtScratchOk c s' → s'.core.dense_mode = 0#64 →
      s'.core.cur_level = 0 → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.lit_mark = s.core.lit_mark →
      s'.scratch.work_stk1 = s.scratch.work_stk1 → (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullProbeAssumePairSpec : Spec [i64, i32] [i64] := fun (h, lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ lit.toNat < 2 * s.core.cur_vars ∧
    s.core.vals[lit.toNat]?.getD 0#8 = 0#8 ∧ (FullMem c s ⋆ R) m ∧ ∀ r s' m',
      (r = 1#64 ∨ r = 2#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (r = 20#64 → F0.Unsat ∧ ∃ F_cur, FullOtfsInvW c F0 F_cur s') →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullProbeRunSpec : Spec [i64, i64] [i64] := fun (h, _budget, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧ ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 → s'.core.probing = 0#64 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def FullTrailRsnsExt (k k' : FullCoreState) : Prop :=
  FullTrailExt k k' ∧ ∀ i < k.trail_end,
    k'.rsns[(k.trl[i]?.getD 0#32).toNat / 2]? = k.rsns[(k.trl[i]?.getD 0#32).toNat / 2]?

@[expose] def fullProbePropLitExtSpec : Spec [i64, i32] [.bool] := fun (h, _lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullMrkZero c s ∧
    FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64 ∧
    s.core.cur_level = 1 ∧ s.core.oom = 0#64 ∧ FullHbrBufOkW F_cur s s.core.tmp_cnt ∧
    (FullMem c s ⋆ R) m ∧ ∀ (ok : Bool) s' m',
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullMrkZero c s' →
      FullArenaVarsNodup s' → FullExtScratchOk c s' → s'.core.dense_mode = 0#64 →
      s'.core.cur_level = 1 → s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.core.lit_mark = s.core.lit_mark → s'.scratch.work_stk1 = s.scratch.work_stk1 →
      FullTrailRsnsExt s.core s'.core → FullHbrBufOkW F_cur s' s'.core.tmp_cnt →
      (ok = false → s'.core.oom ≠ 0#64 ∨ FullConflictOkW F_cur s') →
      (ok = true → s'.core.oom = 0#64) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullProbePropExtSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullMrkZero c s ∧
    FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64 ∧
    s.core.cur_level = 1 ∧ FullHbrBufOkW F_cur s s.core.tmp_cnt ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m', s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullMrkZero c s' →
      FullArenaVarsNodup s' → FullExtScratchOk c s' → s'.core.dense_mode = 0#64 →
      s'.core.cur_level = 1 → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.lit_mark = s.core.lit_mark →
      s'.scratch.work_stk1 = s.scratch.work_stk1 → FullTrailRsnsExt s.core s'.core →
      FullHbrBufOkW F_cur s' s'.core.tmp_cnt → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 1#64 → FullConflictOkW F_cur s') →
      (r = 0#64 → s'.core.propagated = s'.core.trail_end) → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

end FullProbeTransSpecs

open FullProbeTransSpecs

/-! ## 3. Pure hyper-binary dominator helpers (`HbrDomHelpers`) -/

namespace FullProbeTransHelpers

section HbrDomHelpers

@[expose] def hbrMarkInv (cv clen : Nat) (mrk0 mrk : List (BitVec 8)) (clr : List (BitVec 32)) :
    Prop :=
  mrk.length = mrk0.length ∧ clen ≤ cv ∧
  (∀ w, cv ≤ w → w < mrk0.length → mrk[w]? = mrk0[w]?) ∧
  ((clr.take clen).map BitVec.toNat).Nodup ∧
  (∀ t < clen, (clr[t]?.getD 0#32).toNat < cv) ∧
  (∀ w < cv, mrk[w]?.getD 0#8 ≠ 0#8 ↔ ∃ t < clen, (clr[t]?.getD 0#32).toNat = w)

theorem hbrMarkInv_init {cv : Nat} {m0 : List (BitVec 8)} {clr : List (BitVec 32)}
    (hm : ∀ w < cv, m0[w]?.getD 0#8 = 0#8) :
    hbrMarkInv cv 0 m0 m0 clr :=
  ⟨rfl, Nat.zero_le _, fun _ _ _ => rfl, by simp, fun _ ht => by omega,
    fun w hw => ⟨fun hne => absurd (hm w hw) hne, fun ⟨t, ht, _⟩ => by omega⟩⟩

theorem hbrMarkInv_clen_lt {cv clen ov : Nat} {mrk0 mrk : List (BitVec 8)}
    {clr : List (BitVec 32)} (h : hbrMarkInv cv clen mrk0 mrk clr) (hclr : cv ≤ clr.length)
    (hov : ov < cv) (h0 : mrk[ov]?.getD 0#8 = 0#8) : clen < cv := by
  have hle_clr : clen ≤ clr.length := Nat.le_trans h.2.1 hclr
  have hlen_take : ((clr.take clen).map BitVec.toNat).length = clen := by
    simp [List.length_map, List.length_take, Nat.min_eq_left hle_clr]
  have hnot_mem : ov ∉ (clr.take clen).map BitVec.toNat := by
    intro hm; obtain ⟨t, ht, hteq⟩ := List.mem_iff_getElem.mp hm
    have htc : t < clen := by simp only [hlen_take] at ht; omega
    have htl : t < clr.length := by omega
    rw [List.getElem_map, List.getElem_take] at hteq
    exact (h.2.2.2.2.2 ov hov).mpr ⟨t, htc, by
      rw [List.getElem?_eq_getElem htl, Option.getD_some]; exact hteq⟩ h0
  exact inj_lt_of_missing (k := clen) (n := cv) (v := ov)
    (fun i => (clr[i]?.getD 0#32).toNat)
    (fun i j hi hj heq => by
      have hi' : i < ((clr.take clen).map BitVec.toNat).length := by rw [hlen_take]; exact hi
      have hj' : j < ((clr.take clen).map BitVec.toNat).length := by rw [hlen_take]; exact hj
      have hpw := List.pairwise_iff_getElem.mp h.2.2.2.1
      have hget : ∀ a (ha : a < clen),
          ((clr.take clen).map BitVec.toNat)[a]'(by rw [hlen_take]; exact ha) =
            (clr[a]?.getD 0#32).toNat := fun a ha => by
        simp only [List.getElem_map, List.getElem_take]
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      rcases Nat.lt_trichotomy i j with hij | rfl | hji
      · exact absurd (by rw [hget i hi, hget j hj]; exact heq) (hpw i j hi' hj' hij)
      · rfl
      · exact absurd (by rw [hget j hj, hget i hi]; exact heq.symm) (hpw j i hj' hi' hji))
    (fun i hi => h.2.2.2.2.1 i hi) hov
    (fun i hi heq => hnot_mem (List.mem_iff_getElem.mpr ⟨i, by rw [hlen_take]; exact hi, by
      simp only [List.getElem_map, List.getElem_take]
      simpa [List.getElem?_eq_getElem (by omega : i < clr.length)] using heq⟩))

theorem hbrMarkInv_set {cv clen ov : Nat} {mrk0 mrk : List (BitVec 8)}
    {clr : List (BitVec 32)} (h : hbrMarkInv cv clen mrk0 mrk clr)
    (hcv_clr : cv ≤ clr.length) (hcv_mrk : cv ≤ mrk0.length) (hcv32 : cv < 2 ^ 32)
    (hov : ov < cv) (h0 : mrk[ov]?.getD 0#8 = 0#8) :
    hbrMarkInv cv (clen + 1) mrk0 (mrk.set ov 1#8) (clr.set clen (BitVec.ofNat 32 ov)) := by
  have hcl_lt : clen < cv := hbrMarkInv_clen_lt h hcv_clr hov h0
  have hcl_clr : clen < clr.length := by omega
  have hov_mrk : ov < mrk.length := by rw [h.1]; omega
  have hov32 : ov < 2 ^ 32 := by omega
  have htake : ((clr.set clen (BitVec.ofNat 32 ov)).take (clen + 1)) =
      clr.take clen ++ [BitVec.ofNat 32 ov] := by
    apply List.ext_getElem (by simp [List.length_take, Nat.min_eq_left (by omega : clen + 1 ≤
      clr.length), Nat.min_eq_left (by omega : clen ≤ clr.length)])
    intro j hj1 _; simp only [List.length_take, List.length_set,
      Nat.min_eq_left (by omega : clen + 1 ≤ clr.length)] at hj1
    have hlen_t : (clr.take clen).length = clen := List.length_take_of_le (by omega)
    by_cases hjc : j = clen
    · simp only [List.getElem_take]; rw [List.getElem_append_right (by omega)]
      simp only [hlen_t, hjc, Nat.sub_self, List.getElem_singleton]
      exact List.getElem_set_self (a := BitVec.ofNat 32 ov) (by simpa using hcl_clr)
    · rw [List.getElem_take, List.getElem_set_ne (Ne.symm hjc),
        List.getElem_append_left (by omega), List.getElem_take]
  have hnot_ov : ov ∉ (clr.take clen).map BitVec.toNat := by
    intro hm; obtain ⟨t, ht, hteq⟩ := List.mem_iff_getElem.mp hm
    have htl : t < clen := by simp only [List.length_map, List.length_take] at ht; omega
    rw [List.getElem_map, List.getElem_take] at hteq
    exact (h.2.2.2.2.2 ov hov).mpr ⟨t, htl, by
      rw [List.getElem?_eq_getElem (by omega : t < clr.length), Option.getD_some]; exact hteq⟩ h0
  refine ⟨by simp [h.1], by omega, fun w hw1 hw2 => ?_, ?_, fun t ht => ?_, fun w hw => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact h.2.2.1 w hw1 hw2
  · rw [htake, List.map_append, List.map_singleton, bv32_ofNat_toNat hov32]
    exact List.nodup_append.mpr ⟨h.2.2.2.1, List.nodup_cons.mpr ⟨by simp, .nil⟩,
      fun a ha b hb => by simp only [List.mem_singleton] at hb; subst hb
                          exact fun heq => absurd (heq ▸ ha) hnot_ov⟩
  · by_cases htc : t = clen
    · subst htc; rw [List.getElem?_set_self hcl_clr, Option.getD_some, bv32_ofNat_toNat hov32]
      exact hov
    · rw [List.getElem?_set_ne (Ne.symm htc)]; exact h.2.2.2.2.1 t (by omega)
  · by_cases hwv : w = ov
    · subst hwv; rw [List.getElem?_set_self hov_mrk, Option.getD_some]
      exact ⟨fun _ => ⟨clen, by omega, by
        rw [List.getElem?_set_self hcl_clr, Option.getD_some, bv32_ofNat_toNat hov32]⟩,
        fun _ => by decide⟩
    · rw [List.getElem?_set_ne (Ne.symm hwv)]; constructor
      · intro hne; obtain ⟨t, ht, hteq⟩ := (h.2.2.2.2.2 w hw).mp hne
        exact ⟨t, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hteq⟩
      · rintro ⟨t, ht, hteq⟩; by_cases htc : t = clen
        · subst htc; rw [List.getElem?_set_self hcl_clr, Option.getD_some,
            bv32_ofNat_toNat hov32] at hteq; exact absurd hteq.symm hwv
        · rw [List.getElem?_set_ne (Ne.symm htc)] at hteq
          exact (h.2.2.2.2.2 w hw).mpr ⟨t, by omega, hteq⟩

@[expose] def markedTrailCount (mrk : List (BitVec 8)) (trl : List (BitVec 32)) (idx : Nat) : Nat :=
  ((List.range idx).filter fun t =>
    decide (mrk[(trl[t]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)).length

theorem markedTrailCount_le (mrk : List (BitVec 8)) (trl : List (BitVec 32)) (idx : Nat) :
    markedTrailCount mrk trl idx ≤ idx := by
  unfold markedTrailCount
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem markedTrailCount_succ (mrk : List (BitVec 8)) (trl : List (BitVec 32)) (idx : Nat) :
    markedTrailCount mrk trl (idx + 1) =
      markedTrailCount mrk trl idx +
        if mrk[(trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 then 1 else 0 := by
  unfold markedTrailCount
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : mrk[(trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 <;> simp [h]

theorem markedTrailCount_set {mrk : List (BitVec 8)} {trl : List (BitVec 32)}
    {te n ov : Nat} (hn : n ≤ te) (hov_lt : ov < mrk.length) (h0 : mrk[ov]?.getD 0#8 = 0#8)
    (hnod : ∀ i j, i < te → j < te →
      (trl[i]?.getD 0#32).toNat / 2 = (trl[j]?.getD 0#32).toNat / 2 → i = j) :
    markedTrailCount (mrk.set ov 1#8) trl n =
      markedTrailCount mrk trl n +
        if ∃ m < n, (trl[m]?.getD 0#32).toNat / 2 = ov then 1 else 0 := by
  induction n with
  | zero => simp [markedTrailCount]
  | succ k ih =>
    have ih' := ih (by omega)
    rw [markedTrailCount_succ, markedTrailCount_succ, ih']
    by_cases hkv : (trl[k]?.getD 0#32).toNat / 2 = ov
    · have hno : ¬ ∃ m < k, (trl[m]?.getD 0#32).toNat / 2 = ov := by
        rintro ⟨m, hm, hmv⟩; have := hnod m k (by omega) (by omega) (hmv.trans hkv.symm); omega
      have hyes : ∃ m < k + 1, (trl[m]?.getD 0#32).toNat / 2 = ov := ⟨k, by omega, hkv⟩
      rw [hkv, List.getElem?_set_self hov_lt, Option.getD_some, h0]
      simp [hno, hyes]
    · have heq : (∃ m < k + 1, (trl[m]?.getD 0#32).toNat / 2 = ov) ↔
          (∃ m < k, (trl[m]?.getD 0#32).toNat / 2 = ov) :=
        ⟨fun ⟨m, hm, hmv⟩ => ⟨m, by
          by_cases hmk : m = k; · subst hmk; exact absurd hmv hkv
          · omega, hmv⟩, fun ⟨m, hm, hmv⟩ => ⟨m, by omega, hmv⟩⟩
      rw [List.getElem?_set_ne (Ne.symm hkv)]
      by_cases hex : ∃ m < k, (trl[m]?.getD 0#32).toNat / 2 = ov
      · simp [hex, heq.mpr hex]; omega
      · simp [hex, show ¬ ∃ m < k + 1, (trl[m]?.getD 0#32).toNat / 2 = ov from
          fun h => hex (heq.mp h)]

theorem markedTrailCount_eq_zero_iff {mrk : List (BitVec 8)} {trl : List (BitVec 32)}
    {idx : Nat} (hz : markedTrailCount mrk trl idx = 0) :
    ∀ t < idx, mrk[(trl[t]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8 := by
  intro t ht
  by_cases hzero : mrk[(trl[t]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8
  · exact hzero
  · exfalso
    have hmem : t ∈ (List.range idx).filter fun t =>
        decide (mrk[(trl[t]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8) :=
      List.mem_filter.mpr ⟨List.mem_range.mpr ht, decide_eq_true hzero⟩
    have hpos : 0 < markedTrailCount mrk trl idx := List.length_pos_iff_exists_mem.mpr ⟨t, hmem⟩
    omega

@[expose] def domReach (k : FullCoreState) (mrk : List (BitVec 8)) (idx : Nat) (α : Nat → Bool) :
    Prop :=
  ∃ t < idx, mrk[(k.trl[t]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
    α (litVar (k.trl[t]?.getD 0#32).toNat) = litSign (k.trl[t]?.getD 0#32).toNat

theorem entails_bin_hbr_of_domReach {F_cur : List (List Nat)} {k : FullCoreState}
    {mrk : List (BitVec 8)} {idx implied : Nat}
    (hopen0 : markedTrailCount mrk k.trl idx = 0)
    (hreach : ∀ α, (cnfOfClauses F_cur).Sat α →
      α (litVar implied) = litSign implied → domReach k mrk (idx + 1) α) :
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(k.trl[idx]?.getD 0#32).toNat ^^^ 1, implied]) := by
  rw [CNF.entails_clause_def]
  intro α hα
  by_cases him : α (litVar implied) = !(litSign implied)
  · exact (clause_sat_cnfClause_iff α _).mpr ⟨implied, by simp, him⟩
  · have himf : α (litVar implied) = litSign implied := by
      cases hs : litSign implied <;> cases ha : α (litVar implied) <;> simp_all
    obtain ⟨t, ht, hmt, hfal⟩ := hreach α hα himf
    have hteq : t = idx := by
      by_cases hlt : t < idx
      · exact absurd (markedTrailCount_eq_zero_iff hopen0 t hlt) hmt
      · omega
    subst hteq
    refine (clause_sat_cnfClause_iff α _).mpr
      ⟨(k.trl[t]?.getD 0#32).toNat ^^^ 1, by simp, ?_⟩
    change α (litVar (litNeg (k.trl[t]?.getD 0#32).toNat)) =
      !(litSign (litNeg (k.trl[t]?.getD 0#32).toNat))
    rw [litVar_litNeg, litSign_litNeg, Bool.not_not]; exact hfal

end HbrDomHelpers

section WatchSliceHelpers

theorem watchSlice_append {F_cur : List (List Nat)} {k : FullCoreState} {lit p len1 len2 : Nat}
    (h1 : WatchSliceOk F_cur k lit p len1) (h2 : WatchSliceOk F_cur k lit (p + len1) len2) :
    WatchSliceOk F_cur k lit p (len1 + len2) := by
  induction h1 with
  | empty => simpa using h2
  | @bin p rem w0 h0 hf hn hl he _ ih =>
    have hadd : p + (rem + 1) = (p + 1) + rem := by omega
    rw [hadd] at h2
    have hres := ih h2
    rw [show rem + 1 + len2 = (rem + len2) + 1 by omega]
    exact .bin h0 hf hn hl he hres
  | @large p rem w0 cr h0 h1 hf hl hr _ ih =>
    have hadd : p + (rem + 2) = (p + 2) + rem := by omega
    rw [hadd] at h2
    have hres := ih h2
    rw [show rem + 2 + len2 = (rem + len2) + 2 by omega]
    exact .large h0 h1 hf hl hr hres

theorem watchSlice_relocate {F F' : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat}
    (hF : (cnfOfClauses F').Entails (cnfOfClauses F)) (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F k lit p rem) : WatchSliceOk F' k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hflag hne (by omega)
      (CNF.entails_clause_trans hF hent)
      (ih (p' := p' + 1) fun idx hi => by
        rw [show p' + 1 + idx = p' + (idx + 1) by omega,
          show p + 1 + idx = p + (idx + 1) by omega]
        exact hwstk (idx + 1) (by omega))
  | @large p rem w0 cr hp hp1 hflag hlt href _ ih =>
    exact .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1)
      hflag hlt (hsub _ href)
      (ih (p' := p' + 2) fun idx hi => by
        rw [show p' + 2 + idx = p' + (idx + 2) by omega,
          show p + 2 + idx = p + (idx + 2) by omega]
        exact hwstk (idx + 2) (by omega))

theorem watchSlice_append_bin {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' len : Nat} {w0 : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < len, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h1 : WatchSliceOk F_cur k lit p len)
    (hp0 : k'.wstk[p' + len]? = some w0) (hflag : (w0 &&& 0x80000000#32) ≠ 0#32)
    (hne : w0 ≠ 0xFFFFFFFF#32) (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    WatchSliceOk F_cur k' lit p' (len + 1) :=
  watchSlice_append (watchSlice_relocate (by rw [CNF.entails_def]; exact fun _ h => h) hvars hsub
    hwstk h1) (.bin hp0 hflag hne hlt hent .empty)

theorem watchSlice_append_large {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' len : Nat} {w0 cref : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < len, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h1 : WatchSliceOk F_cur k lit p len)
    (hp0 : k'.wstk[p' + len]? = some w0) (hp1 : k'.wstk[p' + len + 1]? = some cref)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hlt : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ fullArenaClauseRefsCore k') : WatchSliceOk F_cur k' lit p' (len + 2) :=
  watchSlice_append (watchSlice_relocate (by rw [CNF.entails_def]; exact fun _ h => h) hvars hsub
    hwstk h1) (.large hp0 hp1 hflag hlt href .empty)

theorem watchSlice_inv_bin {F_cur : List (List Nat)} {k : FullCoreState} {lit p len : Nat}
    {w0 : BitVec 32} (h : WatchSliceOk F_cur k lit p len) (_hlen : 0 < len)
    (hget : k.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) :
    w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
    WatchSliceOk F_cur k lit (p + 1) (len - 1) := by
  cases h with
  | empty => omega
  | bin h0 _ hne hlt hent hrest =>
    have hw := Option.some.inj (h0.symm.trans hget); subst hw; exact ⟨hne, hlt, hent, by simpa⟩
  | large h0 _ hf _ _ _ =>
    have hw := Option.some.inj (h0.symm.trans hget); subst hw; exact absurd hf hflag

theorem watchSlice_inv_large {F_cur : List (List Nat)} {k : FullCoreState} {lit p len : Nat}
    {w0 : BitVec 32} (h : WatchSliceOk F_cur k lit p len) (_hlen : 0 < len)
    (hget : k.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) = 0#32) :
    2 ≤ len ∧ ∃ cref : BitVec 32, k.wstk[p + 1]? = some cref ∧
      cref.toNat < 0x80000000 ∧ cref.toNat ∈ fullArenaClauseRefsCore k ∧
      WatchSliceOk F_cur k lit (p + 2) (len - 2) := by
  cases h with
  | empty => omega
  | bin h0 hf _ _ _ =>
    have hw := Option.some.inj (h0.symm.trans hget); subst hw; exact absurd hflag hf
  | large h0 h1 _ hlt href hrest => exact ⟨by omega, _, h1, hlt, href, by simpa⟩

end WatchSliceHelpers

end FullProbeTransHelpers

end LeanQbe.T.Examples.Kissat.Full

