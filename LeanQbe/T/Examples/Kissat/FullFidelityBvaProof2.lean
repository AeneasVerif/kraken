/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof2b0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof1
import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity BVA Proofs — Part 2 (`full_bva_try_lit`)

Parametric `(Γ : Env)` `Func.wp` soundness proofs (`public section`, `0` banned tokens,
`XPost`-polymorphic) for `FullFidelityBva`:
1. `full_bva_try_lit_fid_wp` against `fidBvaTryLitSpec`.
2. `full_bva_try_lit_heap_wp` against canonical `FullBvaHeap.fullBvaTryLitHeapSpec`
   (via `fidBvaTryLitSpec_weaken`).
-/

set_option autoImplicit false

namespace FidFast
open Lean Meta Elab Tactic LeanQbe.T.C0Step LeanQbe.T.C0HeadStep

private meta partial def fidSepClauses (e : Lean.Expr) : List Lean.Expr :=
  let e := e.consumeMData
  if e.isAppOf ``Std.ExtHashMap.sep && e.getAppNumArgs ≥ 2 then
    fidSepClauses (e.getArg! (e.getAppNumArgs - 2)) ++
      fidSepClauses (e.getArg! (e.getAppNumArgs - 1))
  else [e]

private meta def fidFootprints : TacticM (Array Name) := withMainContext do
  let mut keys : Array Name := #[]
  for d in (← getLCtx).decls.toArray.reverse do
    let some d := d | continue
    if d.isImplementationDetail then continue
    let t := (← instantiateMVars d.type).consumeMData
    if t.isAppOf ``Std.ExtHashMap.sep && t.getAppNumArgs ≥ 3 then
      for c in fidSepClauses t.appFn! do
        if let some k := c.getAppFn.consumeMData.constName? then
          unless keys.contains k do keys := keys.push k
  return keys

private meta def fidTryMemFast (useBound : Bool) (g : MVarId) (nm : Name) : TacticM Bool := do
  let s ← saveState
  let gs ← try withReducible <| g.apply (← mkConstWithFreshMVarLevels nm)
    catch _ => s.restore; return false
  for g' in gs do
    let ty ← instantiateMVars (← g'.getType)
    if ty.isAppOf ``Std.ExtHashMap.sep then
      let ok ← try withReducible g'.assumption; pure true catch _ => pure false
      unless ok do
        let s2 ← saveState
        let ok2 ← try
          setGoals [g']; evalTactic (← `(tactic| c0_frame))
          pure (← getUnsolvedGoals).isEmpty
        catch _ => pure false
        unless ok2 do s2.restore; s.restore; return false
  for g' in gs do
    if ← g'.isAssigned then continue
    if ← isProp (← g'.getType) then
      let ok ← try g'.assumption; pure true
        catch _ => try g'.refl; pure true
        catch _ =>
          if useBound then
            try
              setGoals [g']
              evalTactic (← `(tactic| c0_bound))
              pure (← getUnsolvedGoals).isEmpty
            catch _ => pure false
          else pure false
      unless ok do s.restore; return false
  for g' in gs do
    unless ← g'.isAssigned do s.restore; return false
  return true

private meta def fidMemFast (useBound : Bool) (isLoad : Bool) (g : MVarId)
    (addr : Lean.Expr) : TacticM Bool := do
  setGoals [g]
  let keys ← fidFootprints
  let env ← getEnv
  let mut tried : NameSet := {}
  for k in keys do
    for nm in LeanQbe.T.C0Step.c0MemLemmasForAddr env isLoad k addr do
      if tried.contains nm then continue
      tried := tried.insert nm
      if ← fidTryMemFast useBound g nm then return true
  for k in keys do
    for nm in LeanQbe.T.C0Step.c0MemLemmas env isLoad k do
      if tried.contains nm then continue
      tried := tried.insert nm
      if ← fidTryMemFast useBound g nm then return true
  return false

private meta def fidStepOnceFast (useBound : Bool) (cfg : HeadStepConfig) :
    TacticM Bool := withMainContext do
  let g ← getMainGoal
  let ty := (← instantiateMVars (← g.getType)).consumeMData.headBeta
  if ty.isAppOfArity ``LeanQbe.T.wp 6 then
    let wpArgs := ty.getAppArgs
    let e0 := (peelBlocksGet wpArgs[4]!).consumeMData.headBeta
    let e ← if e0.isAppOf ``LeanQbe.T.Expr.let_ || e0.isAppOf ``LeanQbe.T.Expr.load ||
               e0.isAppOf ``LeanQbe.T.Expr.store || e0.isAppOf ``LeanQbe.T.Expr.jnz ||
               e0.isAppOf ``LeanQbe.T.Expr.jump || e0.isAppOf ``LeanQbe.T.Expr.ret ||
               e0.isAppOf ``LeanQbe.T.Expr.exit || e0.isAppOf ``LeanQbe.T.Expr.group ||
               e0.isAppOf ``LeanQbe.T.Expr.call
             then pure e0 else (peelBlocksGet <$> whnfCore e0)
    if e.isAppOf ``LeanQbe.T.Expr.load && e.getAppNumArgs == 6 then
      let t := e.getArg! 3; let a := e.getArg! 4; let k := e.getArg! 5
      let addr := reduceSmall (Lean.mkApp2 (Lean.mkConst ``LeanQbe.T.Arg.val)
        (Lean.mkConst ``LeanQbe.T.i64) a)
      let vMVar ← mkFreshExprMVar (some (Lean.mkApp (Lean.mkConst ``LeanQbe.T.Val) t))
      let s ← saveState
      try
        let lemInfo ← getConstInfo ``head_wp_load
        let pfx : Array Lean.Expr := #[wpArgs[0]!, wpArgs[1]!, wpArgs[2]!, wpArgs[3]!,
          wpArgs[5]!, t, a, addr, k, vMVar,
          Lean.mkApp2 (Lean.mkConst ``Eq.refl [Level.succ Level.zero])
            (Lean.mkApp (Lean.mkConst ``BitVec) (Lean.mkNatLit 64)) addr]
        let .forallE _ sTy body1 _ ← instantiateForall lemInfo.type pfx
          | s.restore; return false
        let hl ← mkFreshExprSyntheticOpaqueMVar sTy
        let .forallE _ hkTy _ _ := body1.instantiate1 hl | s.restore; return false
        let hk ← mkFreshExprSyntheticOpaqueMVar hkTy
        g.assign (Lean.mkAppN (Lean.mkConst ``head_wp_load) ((pfx.push hl).push hk))
        if ← fidMemFast useBound true hl.mvarId! addr then setGoals [hk.mvarId!]; return true
        s.restore; return false
      catch _ => s.restore; return false
    if e.isAppOf ``LeanQbe.T.Expr.store && e.getAppNumArgs == 7 then
      let t := e.getArg! 3; let v := e.getArg! 4; let a := e.getArg! 5; let k := e.getArg! 6
      let val := reduceSmall (Lean.mkApp2 (Lean.mkConst ``LeanQbe.T.Arg.val) t v)
      let addr := reduceSmall (Lean.mkApp2 (Lean.mkConst ``LeanQbe.T.Arg.val)
        (Lean.mkConst ``LeanQbe.T.i64) a)
      let memTy ← inferType wpArgs[5]!
      let memPredTy := Lean.Expr.forallE `m memTy (.sort Level.zero) .default
      let pMVar ← mkFreshExprMVar (some memPredTy)
      let rMVar ← mkFreshExprMVar (some memPredTy)
      let s ← saveState
      try
        let lemInfo ← getConstInfo ``head_wp_store
        let pfx : Array Lean.Expr := #[wpArgs[0]!, wpArgs[1]!, wpArgs[2]!, wpArgs[3]!,
          wpArgs[5]!, t, v, a, val, addr, k, pMVar, rMVar,
          Lean.mkApp2 (Lean.mkConst ``Eq.refl [Level.succ Level.zero])
            (Lean.mkApp (Lean.mkConst ``LeanQbe.T.Val) t) val,
          Lean.mkApp2 (Lean.mkConst ``Eq.refl [Level.succ Level.zero])
            (Lean.mkApp (Lean.mkConst ``BitVec) (Lean.mkNatLit 64)) addr]
        let .forallE _ sTy body1 _ ← instantiateForall lemInfo.type pfx
          | s.restore; return false
        let hs ← mkFreshExprSyntheticOpaqueMVar sTy
        let .forallE _ hkTy _ _ := body1.instantiate1 hs | s.restore; return false
        let hk ← mkFreshExprSyntheticOpaqueMVar hkTy
        g.assign (Lean.mkAppN (Lean.mkConst ``head_wp_store) ((pfx.push hs).push hk))
        if ← fidMemFast useBound false hs.mvarId! addr then
          let (_, hk') ← hk.mvarId!.intro `m
          let (_, hk'') ← hk'.intro `hm
          setGoals [hk'']
          let hIdent := mkIdent `hm
          evalTactic (← `(tactic| try simp only [Std.ExtHashMap.sep_emp] at $hIdent:ident))
          let .fvar mId := wpArgs[5]! | return true
          for d in (← getLCtx).decls.toArray.reverse do
            let some d := d | continue
            let dt ← instantiateMVars d.type
            if dt.isAppOf ``Std.ExtHashMap.sep && dt.appArg! == wpArgs[5]! then
              try liftMetaTactic1 fun g => some <$> g.clear d.fvarId catch _ => pure ()
          try liftMetaTactic1 fun g => some <$> g.clear mId catch _ => pure ()
          return true
        s.restore; return false
      catch _ => s.restore; return false
    if e.isAppOf ``LeanQbe.T.Expr.jnz && e.getAppNumArgs == 6 then
      if !cfg.splitJnz then return false
      let c := e.getArg! 3; let e1 := e.getArg! 4; let e2 := e.getArg! 5
      let vc := reduceSmall (Lean.mkApp2 (Lean.mkConst ``LeanQbe.T.Arg.val)
        (Lean.mkConst ``LeanQbe.T.Ty.bool) c)
      let s ← saveState
      try
        let lemInfo ← getConstInfo ``head_wp_jnz
        let pfx : Array Lean.Expr := #[wpArgs[0]!, wpArgs[1]!, wpArgs[2]!, wpArgs[3]!,
          wpArgs[5]!, c, vc, e1, e2,
          Lean.mkApp2 (Lean.mkConst ``Eq.refl [Level.succ Level.zero])
            (Lean.mkConst ``Bool) vc]
        let .forallE _ sTy body1 _ ← instantiateForall lemInfo.type pfx
          | s.restore; return false
        let h1 ← mkFreshExprSyntheticOpaqueMVar sTy
        let .forallE _ hkTy _ _ := body1.instantiate1 h1 | s.restore; return false
        let h2 ← mkFreshExprSyntheticOpaqueMVar hkTy
        g.assign (Lean.mkAppN (Lean.mkConst ``head_wp_jnz) ((pfx.push h1).push h2))
        let processArm (arm : MVarId) : TacticM (Option MVarId) := do
          let (_, arm') ← arm.intro `hc
          setGoals [arm']
          let hc := mkIdent `hc
          evalTactic (← `(tactic| c0_cond $hc))
          if cfg.pruneJnz then
            evalTactic (← `(tactic| try (first
              | exact ($hc).elim | exact absurd rfl $hc | exact $hc rfl
              | exact absurd trivial $hc | (exfalso; c0_bound))))
          return (← getUnsolvedGoals).head?
        let mut out : Array MVarId := #[]
        if let some a1 ← processArm h1.mvarId! then out := out.push a1
        if let some a2 ← processArm h2.mvarId! then out := out.push a2
        setGoals out.toList
        return true
      catch _ => s.restore; return false
  match ← headStepOnceRes cfg with
  | .progressed => return true
  | _ => return false

private meta partial def fidHeadSteps (useBound : Bool) (cfg : HeadStepConfig)
    (fuel : Nat := 10000) : TacticM Unit := do
  if fuel = 0 then return
  let mut out : Array MVarId := #[]
  for g in ← getUnsolvedGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    if ← fidStepOnceFast useBound cfg then
      fidHeadSteps useBound cfg (fuel - 1)
      out := out ++ (← getUnsolvedGoals)
    else
      let ty0 ← instantiateMVars (← g.getType)
      let ty := ty0.consumeMData.headBeta
      if ty.isAppOfArity ``LeanQbe.T.wp 6 then
        let e := ty.getArg! 4
        let e' := peelBlocksGet (← whnfCore (peelBlocksGet e))
        let g' ← if e' != e || ty != ty0 then
          g.change (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e')) (checkDefEq := false)
        else pure g
        out := out.push g'
      else out := out.push g
  setGoals out.toList

end FidFast

local elab "c0_hfast" : tactic => FidFast.fidHeadSteps false { pruneJnz := false } 10000
local elab "c0_hfast_b" : tactic => FidFast.fidHeadSteps true { pruneJnz := false } 10000
local elab "c0_hfast_nogrp" : tactic =>
  FidFast.fidHeadSteps false { unrollGroup := false, pruneJnz := false } 10000
local elab "c0_hfast_nogrp_b" : tactic =>
  FidFast.fidHeadSteps true { unrollGroup := false, pruneJnz := false } 10000
local elab "c0_hsteps" : tactic => FidFast.fidHeadSteps true { pruneJnz := true } 10000
local elab "c0_hsteps_nogrp" : tactic =>
  FidFast.fidHeadSteps true { unrollGroup := false, pruneJnz := true } 10000

local macro "fid_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBva

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapTactics
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapScanHelpers
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.Full.FullBvaFwdHelpers
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullBvaHeapTactics FullBvaFwdTactics

private theorem fid_try_lit_step_loop_wp (Γ : Env)
    (hScan : ∀ a m Q X, fidBvaScanCandsSpec a m Q X →
      Γ "full_bva_scan_cands" [i64, i32, i32, i64] [i32] a m Q X)
    (hPick : ∀ a m Q X, FullBvaHeap.fullBvaPickCandSpec a m Q X →
      Γ "full_bva_pick_cand" [i64, i32, i32] [i32] a m Q X)
    (hFilter : ∀ a m Q X, fidBvaFilterRowSpec a m Q X →
      Γ "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32] a m Q X)
    {Q : Post [Ty.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st1 : FullState} {R : Mem 64 → Prop}
    {f0 r0n bump0 : BitVec 32} {init_cv0 init_lits : BitVec 64}
    {m : Mem 64}
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hf0_lt : f0.toNat < 2 * s.core.cur_vars)
    (hinit_lits : init_lits.toNat ≤ 2 * s.core.cur_vars)
    (hsc_pos : 0 < fidStepsCap c.scratch_cap)
    (hsc_le : fidStepsCap c.scratch_cap ≤ 256)
    (hinv1 : StepInvBody c F0 F_cur s R (fidStepsCap c.scratch_cap)
      1#32 r0n 0#32 bump0.toNat st1 m)
    (Jexit : Cont [i32, i32, i32, i32, i64])
    (hJexit : ∀ (st : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 64)
        (ml : Mem 64),
      (∃ stl, StepExitBody c F0 F_cur s R (fidStepsCap c.scratch_cap)
        st.2.1 st.2.2.2.1 st.1.toNat stl ml) →
      Jexit (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2, ()) ml) :
    wp Γ Q X
      (Expr.group
        (fidTryLitStepBlock Val Cont
          (BitVec.ofNat 32 (fidStepsCap c.scratch_cap), ())
          (c.hdr, f0, init_cv0, ()) c.pScratchBuf (init_lits, ())
          (Jexit, ()) (BitVec.ofNat 64 c.scratch_cap)
          c.pLitMark s.scratch.elim_bound)
        (fun Js => Expr.jump Js.fst
          (Arg.var bump0, Arg.imm 1, Arg.var r0n, Arg.imm 0, Arg.imm 0, ())))
      m := by
  let sc_n := fidStepsCap c.scratch_cap
  have hsc_pos' : 0 < sc_n := hsc_pos
  have hscap := c.hscr
  unfold dimacsBound at hscap
  unfold fidTryLitStepBlock
  refine wp_loop_inv (ts := [i32, i32, i32, i32, i64])
    (fun (bump, step, cur_qn, best_k, best_red, ()) ml =>
      ∃ stl, StepInvBody c F0 F_cur s R sc_n step cur_qn best_k bump.toNat stl ml)
    (fun (_, step, _, _, _, _) _ => sc_n - step.toNat)
    (fun Jst hJst => by
      c0_hfast
      exact hJst (bump0, 1#32, r0n, 0#32, 0#64, ()) m ⟨st1, hinv1⟩)
    (fun Jst (bump, step, cur_qn, best_k, best_red, ()) ml ⟨stl, hinvl⟩ ihst => ?_)
  have hinvl_cp := hinvl
  obtain ⟨hml, hlenl, hwl, hndl, hextl, hlv0l, hdml, hcvl, hfuell, harl, hall,
          hmrkl, html, htrl, hst1, hst_sc, hbump_ge, hbump_le, hqn_eq, hmatl,
          hbkl, hlml_hi, hlml_set, hlml_only⟩ := hinvl
  c0_hsplit
  · c0_hsplit
    · c0_hsplit
      · have hst_lt : step.toNat < sc_n := by omega
        have hqn_ge2 : 2 ≤ cur_qn.toNat := by
          have h1 : BitVec.toNat (2 : BitVec 32) ≤ cur_qn.toNat := by assumption
          simpa only [show BitVec.toNat (2 : BitVec 32) = 2 from rfl] using h1
        have hant_pos : 0 < stl.scratch.ant_sz.toNat := by
          have h1 : BitVec.toNat (0 : BitVec 64) < stl.scratch.ant_sz.toNat := by
            assumption
          simpa only [show BitVec.toNat (0 : BitVec 64) = 0 from rfl] using h1
        have hstep_sb : (BitVec.ofNat 32 sc_n + step - 1#32).toNat <
            stl.scratch.scratch_buf.length := by
          rw [fid_bv32_sc_add_step_sub1 hsc_le hst1 hst_sc,
            hlenl.scratch_ok.scratch_buf_len]
          have := hmatl.1; omega
        have hstep_sb_w : (BitVec.setWidth 64
            (BitVec.ofNat 32 sc_n + step - 1#32)).toNat <
            stl.scratch.scratch_buf.length := by
          rw [fid_bv64_32]; exact hstep_sb
        c0_hfast_nogrp
        let row_off := stl.scratch.scratch_buf[(BitVec.setWidth 64
          (BitVec.ofNat 32 sc_n + step - 1#32)).toNat]'hstep_sb_w
        have hrow_off_nat : row_off.toNat =
            (stl.scratch.scratch_buf[sc_n + (step.toNat - 1)]?.getD 0#32).toNat := by
          have hidx_eq : (BitVec.setWidth 64
              (BitVec.ofNat 32 sc_n + step - 1#32)).toNat =
              sc_n + (step.toNat - 1) := by
            rw [fid_bv64_32, fid_bv32_sc_add_step_sub1 hsc_le hst1 hst_sc]
          have hget : stl.scratch.scratch_buf[(BitVec.setWidth 64
              (BitVec.ofNat 32 sc_n + step - 1#32)).toNat]? = some row_off :=
            List.getElem?_eq_getElem hstep_sb_w
          rw [hidx_eq] at hget
          rw [hget, Option.getD_some]
        have hrow_off_c : (stl.scratch.scratch_buf[(BitVec.setWidth 64
            (BitVec.ofNat 32 (fidStepsCap c.scratch_cap) + step - 1)).toNat]'
            (by change (BitVec.setWidth 64
                  (BitVec.ofNat 32 sc_n + step - 1#32)).toNat < _
                exact hstep_sb_w)).toNat =
            (stl.scratch.scratch_buf[sc_n + (step.toNat - 1)]?.getD 0#32).toNat :=
          hrow_off_nat
        obtain ⟨_, hro_ge, _, hro_le, _, hrows⟩ :=
          hmatl.2.2.2.2.2 (step.toNat - 1) (by omega)
        fid_call hScan
        refine ⟨c, F0, F_cur, stl, R, rfl, hlenl, hwl, hndl, hextl, hlv0l, hdml,
          by dsimp only [Arg.val]; rw [hcvl]; exact hinit_lits, hlml_hi,
          by dsimp only [Arg.val]; rw [hrow_off_c, hqn_eq]
             exact Nat.le_trans hro_le hbump_le,
          fun qi hqi => by
            dsimp only [Arg.val] at hqi ⊢
            rw [hqn_eq] at hqi
            obtain ⟨res, _, _, hok, _⟩ := hrows qi hqi
            unfold FidBvaRowEntryOk at hok
            by_cases hbin : (stl.scratch.scratch_buf[(stl.scratch.scratch_buf[
                sc_n + (step.toNat - 1)]?.getD 0#32).toNat + qi]?.getD 0#32 &&&
                0x80000000#32) ≠ 0#32
            · rw [ite_eq_left hbin] at hok; rw [hrow_off_c]; rw [ite_eq_left hbin]
              exact hok.1
            · rw [ite_eq_right hbin] at hok; rw [hrow_off_c]; rw [ite_eq_right hbin]
              exact ⟨hok.1, hok.2.1⟩,
          hml, ?_⟩
        intro ncntd wsort' ws1' ws2' ant1 m1
        dsimp only
        intro hlen1 hncntd_le hcntd_ok hm1
        let scl := stl.scratch
        let s1 : FullState :=
          { stl with scratch :=
            { scl with wsort := wsort', work_stk1 := ws1', work_stk2 := ws2',
                       ant_sz := ant1 } }
        have hmat1_scan : FidBvaMatrixInv c F_cur s1 step.toNat bump.toNat :=
          fidBvaMatrixInv_congr rfl rfl rfl rfl hmatl
        have hinv1_nl : FullDenseInvNoLm c F0 F_cur s1 :=
          ⟨hlen1, hwl, hndl, hextl, hlv0l, hdml⟩
        c0_hfast_nogrp
        fid_call hPick
        refine ⟨c, F0, F_cur, s1, R, rfl, hinv1_nl, by rw [hcvl]; exact hf0_lt,
          by dsimp only [Arg.val] at hncntd_le ⊢
             change ncntd.toNat ≤ 2 * stl.core.cur_vars
             rw [hcvl]; exact Nat.le_trans hncntd_le hinit_lits,
          by dsimp only [Arg.val] at hcntd_ok ⊢
             intro i hi
             change (s1.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * stl.core.cur_vars
             rw [hcvl]; exact Nat.lt_of_lt_of_le (hcntd_ok i hi) hinit_lits,
          hm1, ?_⟩
        intro best_lit repr2 mc2 tc2 tl2 ws2 ant2 sim2 shr2 m2
        dsimp only
        intro hinv2 hbl_opt hm2
        let co1 := s1.core
        let sc1 := s1.scratch
        let s2 : FullState :=
          { core := { co1 with repr := repr2, min_clr := mc2,
                               tmp_cnt := tc2, tmp_len := tl2 },
            scratch := { sc1 with wsort := ws2, ant_sz := ant2,
                                  sim_sig := sim2, shrink_stk := shr2 } }
        have hmat2 : FidBvaMatrixInv c F_cur s2 step.toNat bump.toNat :=
          fidBvaMatrixInv_congr rfl rfl rfl rfl hmat1_scan
        have hlen2 : s2.LengthsOk c := hinv2.1
        have hw2 : FullWitnessInv c F0 F_cur s2.core :=
          { hwl with
            arena := { hwl.arena with len_ok := hwl.arena.len_ok }
            watches := hwl.watches.with_wstk rfl rfl rfl rfl rfl
              (fun _ hr => hr) }
        c0_hsplit
        · c0_hfast_nogrp
          exact hJexit (bump, step, cur_qn, best_k, best_red) m2
            ⟨s2, hm2, hlen2, hw2, hndl, hextl, hlv0l, hdml, hcvl, hfuell, harl,
             hall, hmrkl, html, htrl, hst1, hst_sc, hbump_ge, hbump_le,
             hmat2, hbkl, hlml_hi, hlml_set, hlml_only⟩
        · have hbest_lt : best_lit.toNat < 2 * s.core.cur_vars := by
            rcases hbl_opt with rfl | hbl
            · contradiction
            · rw [← hcvl]; exact hbl
          c0_hsplit
          · c0_hfast_nogrp
            exact hJexit (bump, step, cur_qn, best_k, best_red) m2
              ⟨s2, hm2, hlen2, hw2, hndl, hextl, hlv0l, hdml, hcvl, hfuell,
               harl, hall, hmrkl, html, htrl, hst1, hst_sc, hbump_ge, hbump_le,
               hmat2, hbkl, hlml_hi, hlml_set, hlml_only⟩
          · c0_hfast_nogrp
            refine wp_join_state (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
              (fun max_new mf => max_new.toNat ≤ cur_qn.toNat ∧
                max_new.toNat ≤ (c.scratch_cap - bump.toNat) / 2 ∧ mf = m2)
              (fun _ max_new mf ⟨hmn_le, hmn_rem, hmf⟩ => ?_)
              (fun Jmn hJmn => ?_)
            · subst mf
              c0_hfast_nogrp
              c0_hsplit
              · c0_hfast_nogrp
                exact hJexit (bump, step, cur_qn, best_k, best_red) m2
                  ⟨s2, hm2, hlen2, hw2, hndl, hextl, hlv0l, hdml, hcvl, hfuell,
                   harl, hall, hmrkl, html, htrl, hst1, hst_sc, hbump_ge, hbump_le,
                   hmat2, hbkl, hlml_hi, hlml_set, hlml_only⟩
              · let nrow_off := bump
                let par_off := bump + max_new
                have hpar_off_nat : par_off.toNat = bump.toNat + max_new.toNat := by
                  dsimp only [par_off]; simp only [bv_c0]
                  rw [Nat.mod_eq_of_lt (by omega)]
                have hnrow_eq_bump : nrow_off.toNat = bump.toNat := rfl
                have hpar_off_cap :
                    par_off.toNat + (par_off.toNat - nrow_off.toNat) ≤
                      c.scratch_cap := by
                  dsimp only [nrow_off]; rw [hpar_off_nat]; omega
                c0_hfast_nogrp
                fid_call hFilter
                refine ⟨c, F0, F_cur, s2, R, step.toNat, bump.toNat, rfl,
                  hlen2, hw2, hndl, hextl, hlv0l, hdml, hsc_pos', hst1, hst_lt,
                  by dsimp only [Arg.val]; exact hrow_off_c,
                  by dsimp only [Arg.val]; exact hqn_eq,
                  rfl,
                  by dsimp only [Arg.val]; rw [hpar_off_nat]; omega,
                  by change par_off.toNat + (par_off.toNat - nrow_off.toNat) ≤
                      c.scratch_cap
                     exact hpar_off_cap,
                  by dsimp only [Arg.val]
                     change best_lit.toNat < 2 * stl.core.cur_vars
                     rw [hcvl]; exact hbest_lt,
                  hmat2, hlml_hi, hlml_set, hm2, ?_⟩
                intro new_qn sb3 ant3 m3
                dsimp only
                intro hlen3 hnq_max hpres3 hnew3 hm3
                try dsimp only [Arg.val] at hnq_max hpres3 hnew3
                have hnq_le_max : new_qn.toNat ≤ max_new.toNat := by
                  rw [show (bump + max_new).toNat = par_off.toNat from rfl,
                    hpar_off_nat] at hnq_max
                  omega
                have hpres3' : ∀ idx < c.scratch_cap,
                    ¬(bump.toNat ≤ idx ∧ idx < bump.toNat + max_new.toNat) →
                    ¬(par_off.toNat ≤ idx ∧ idx < par_off.toNat + max_new.toNat) →
                    sb3[idx]? = s2.scratch.scratch_buf[idx]? := fun idx hi h1 h2 => by
                  apply hpres3 idx hi
                  · rw [show (bump + max_new).toNat = par_off.toNat from rfl,
                      hpar_off_nat]
                    omega
                  · rw [show (bump + max_new).toNat = par_off.toNat from rfl,
                      hpar_off_nat]
                    omega
                let sc2 := s2.scratch
                let s3 : FullState :=
                  { s2 with scratch :=
                    { sc2 with scratch_buf := sb3, ant_sz := ant3 } }
                c0_hsplit
                · have hmat3_pres := fidBvaMatrixInv_of_filter_pres hmat2 rfl
                    (by rw [hpar_off_nat]; omega)
                    hpres3'
                  have hsb3_lt_bump : ∀ idx < bump.toNat,
                      sb3[idx]? = stl.scratch.scratch_buf[idx]? := fun idx hi =>
                    hpres3' idx (by omega) (by omega) (by rw [hpar_off_nat]; omega)
                  c0_hfast_nogrp
                  exact hJexit (bump, step, new_qn, best_k, best_red) m3
                    ⟨s3, hm3, hlen3, hw2, hndl, hextl, hlv0l, hdml, hcvl, hfuell,
                     harl, hall, hmrkl, html, htrl, hst1, hst_sc, hbump_ge,
                     hbump_le, hmat3_pres, hbkl, hlml_hi,
                     fun (r : Nat) (hr : r < step.toNat) => by
                       dsimp only [s3]; rw [hsb3_lt_bump r (by omega)]
                       exact hlml_set r hr,
                     fun l hl hne => by
                       dsimp only [s3] at hne ⊢
                       obtain ⟨r, hr, heq⟩ := hlml_only l hl hne
                       exact ⟨r, hr, by rw [hsb3_lt_bump r (by omega)]; exact heq⟩⟩
                · have hnq_ge2 : 2 ≤ new_qn.toNat := by
                    have h1 : ¬ new_qn.toNat < BitVec.toNat (2 : BitVec 32) := by
                      assumption
                    simp only [show BitVec.toNat (2 : BitVec 32) = 2 from rfl]
                      at h1
                    omega
                  have hsb3_l : sb3.length = c.scratch_cap :=
                    hlen3.scratch_ok.scratch_buf_len
                  have hlm3_l : s3.core.lit_mark.length = 2 * c.max_vars :=
                    hlen3.core_ok.lit_mark_len
                  have hstep_sb3 : (BitVec.setWidth 64 step).toNat < sb3.length := by
                    rw [fid_bv64_32, hsb3_l]; omega
                  have hsc_step_nat :
                      (BitVec.setWidth 64
                        (BitVec.ofNat 32 (fidStepsCap c.scratch_cap) + step)).toNat =
                        sc_n + step.toNat := by
                    rw [fid_bv64_32,
                      show BitVec.ofNat 32 (fidStepsCap c.scratch_cap) + step =
                          BitVec.ofNat 32 (1 * sc_n) + step from by
                        simp only [Nat.one_mul]; rfl,
                      fid_bv32_ksc_add_step (k := 1) (sc := sc_n)
                        (by omega) hsc_le (by omega),
                      Nat.one_mul]
                  have hsc_step_sb3 :
                      (BitVec.setWidth 64
                        (BitVec.ofNat 32 (fidStepsCap c.scratch_cap) + step)).toNat <
                        sb3.length := by
                    rw [hsc_step_nat, hsb3_l]; omega
                  have h2sc_step_nat :
                      (BitVec.setWidth 64
                        (2 * BitVec.ofNat 32 (fidStepsCap c.scratch_cap) +
                          step)).toNat =
                        2 * sc_n + step.toNat := by
                    rw [fid_bv64_32, show (2 : BitVec 32) = BitVec.ofNat 32 2 from rfl]
                    exact fid_bv32_mul_sc_add_step (k := 2) (sc := sc_n)
                      (by omega) hsc_le (by omega)
                  have h2sc_step_sb3 :
                      (BitVec.setWidth 64
                        (2 * BitVec.ofNat 32 (fidStepsCap c.scratch_cap) +
                          step)).toNat <
                        sb3.length := by
                    rw [h2sc_step_nat, hsb3_l]; omega
                  have h3sc_step_nat :
                      (BitVec.setWidth 64
                        (3 * BitVec.ofNat 32 (fidStepsCap c.scratch_cap) +
                          step)).toNat =
                        3 * sc_n + step.toNat := by
                    rw [fid_bv64_32, show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl]
                    exact fid_bv32_mul_sc_add_step (k := 3) (sc := sc_n)
                      (by omega) hsc_le (by omega)
                  have h3sc_step_sb3 :
                      (BitVec.setWidth 64
                        (3 * BitVec.ofNat 32 (fidStepsCap c.scratch_cap) +
                          step)).toNat <
                        sb3.length := by
                    rw [h3sc_step_nat, hsb3_l]; omega
                  have hbest_lm :
                      (BitVec.setWidth 64 best_lit).toNat <
                        s3.core.lit_mark.length := by
                    rw [fid_bv64_32, hlm3_l]; omega
                  have hbest_lm_s2 :
                      (BitVec.setWidth 64 best_lit).toNat <
                        s2.core.lit_mark.length := hbest_lm
                  have hsc_step_sb3_1 :
                      (BitVec.setWidth 64
                        (BitVec.ofNat 32 (fidStepsCap c.scratch_cap) + step)).toNat <
                        (sb3.set (BitVec.setWidth 64 step).toNat best_lit).length := by
                    rw [List.length_set]; exact hsc_step_sb3
                  have h2sc_step_sb3_2 :
                      (BitVec.setWidth 64
                        (2 * BitVec.ofNat 32 (fidStepsCap c.scratch_cap) +
                          step)).toNat <
                        ((sb3.set (BitVec.setWidth 64 step).toNat best_lit).set
                          (BitVec.setWidth 64 (BitVec.ofNat 32 (fidStepsCap c.scratch_cap) +
                            step)).toNat nrow_off).length := by
                    rw [List.length_set, List.length_set]; exact h2sc_step_sb3
                  have h3sc_step_sb3_3 :
                      (BitVec.setWidth 64
                        (3 * BitVec.ofNat 32 (fidStepsCap c.scratch_cap) +
                          step)).toNat <
                        (((sb3.set (BitVec.setWidth 64 step).toNat best_lit).set
                          (BitVec.setWidth 64 (BitVec.ofNat 32 (fidStepsCap c.scratch_cap) +
                            step)).toNat nrow_off).set
                          (BitVec.setWidth 64 (2 *
                            BitVec.ofNat 32 (fidStepsCap c.scratch_cap) +
                            step)).toNat new_qn).length := by
                    rw [List.length_set, List.length_set, List.length_set]
                    exact h3sc_step_sb3
                  c0_hfast_nogrp
                  let bump' := par_off + new_qn
                  have hbump'_nat : bump'.toNat = par_off.toNat + new_qn.toNat := by
                    dsimp only [bump']; simp only [bv_c0]
                    rw [Nat.mod_eq_of_lt (by omega)]
                  let sb4 := (((sb3.set step.toNat best_lit).set
                    (sc_n + step.toNat) nrow_off).set
                    (2 * sc_n + step.toNat) new_qn).set
                    (3 * sc_n + step.toNat) par_off
                  let lm4 := s3.core.lit_mark.set best_lit.toNat 1#8
                  let co3 := s3.core
                  let sc3 := s3.scratch
                  let st4 : FullState :=
                    { core := { co3 with lit_mark := lm4 },
                      scratch := { sc3 with scratch_buf := sb4 } }
                  have hsb4_l : sb4.length = c.scratch_cap := by
                    dsimp only [sb4]
                    rw [List.length_set, List.length_set, List.length_set,
                      List.length_set]
                    exact hlen3.scratch_ok.scratch_buf_len
                  have hlm4_l : lm4.length = 2 * c.max_vars := by
                    dsimp only [lm4, s3, co3]
                    rw [List.length_set]
                    exact hlen3.core_ok.lit_mark_len
                  have hnew3' : ∀ nm < new_qn.toNat,
                      let pi := (sb3[par_off.toNat + nm]?.getD 0#32).toNat
                      pi < (s2.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap +
                          (step.toNat - 1)]?.getD 0#32).toNat ∧
                        ∃ res, (∀ x ∈ res, x < 2 * s2.core.cur_vars) ∧
                          (res.map (· / 2)).Nodup ∧
                          FidBvaRowEntryOk F_cur s2
                            (s2.scratch.scratch_buf[step.toNat - 1]?.getD 0#32).toNat
                            (s2.scratch.scratch_buf[(s2.scratch.scratch_buf[
                              fidStepsCap c.scratch_cap + (step.toNat - 1)]?.getD
                              0#32).toNat + pi]?.getD 0#32) res ∧
                          FidBvaRowEntryOk F_cur s2 best_lit.toNat
                            (sb3[bump.toNat + nm]?.getD 0#32) res ∧
                          (∀ t < step.toNat, (cnfOfClauses F_cur).EntailsClause
                            (cnfClause ((s2.scratch.scratch_buf[t]?.getD
                              0#32).toNat :: res))) ∧
                          (cnfOfClauses F_cur).EntailsClause
                            (cnfClause (best_lit.toNat :: res)) := by
                    intro nm hnm
                    obtain ⟨hpi, res, hr1, hr2, hr3, hr4, hr5, hr6⟩ := hnew3 nm hnm
                    have hpi' : (sb3[par_off.toNat + nm]?.getD 0#32).toNat <
                        (s2.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap +
                          (step.toNat - 1)]?.getD 0#32).toNat := by
                      change _ < (stl.scratch.scratch_buf[2 * sc_n +
                        (step.toNat - 1)]?.getD 0#32).toNat
                      rw [← hqn_eq]; exact hpi
                    refine ⟨hpi', res, hr1, hr2, ?_, hr4, hr5, hr6⟩
                    change FidBvaRowEntryOk F_cur s2 _
                      (stl.scratch.scratch_buf[(stl.scratch.scratch_buf[
                        sc_n + (step.toNat - 1)]?.getD 0#32).toNat + _]?.getD
                        0#32) res
                    rw [← hrow_off_c]; exact hr3
                  have hmat4 := fidBvaMatrixInv_extend_step (s := s2) (sb' := sb3)
                    (best_lit := best_lit)
                    rfl hst1 hst_lt hmat2 hlen3.scratch_ok.scratch_buf_len
                    (by rw [hcvl]; exact hbest_lt) rfl hpar_off_nat
                    (by rw [hpar_off_nat]; omega) hnq_le_max hnq_ge2
                    hpres3' hnew3'
                  have ⟨hlm4_hi, hlm4_set, hlm4_only⟩ := fid_bva_try_lit_extend_lm
                    (bl := best_lit) (new_qn := new_qn)
                    hsc_pos' hst_lt hlen3.core_ok.lit_mark_len
                    hlen3.scratch_ok.scratch_buf_len
                    (Nat.lt_of_lt_of_le hbest_lt (Nat.mul_le_mul_left 2 hcv_le))
                    rfl hpar_off_nat
                    hbump_ge (by rw [hpar_off_nat]; omega) hpres3' hlml_hi hlml_set
                    hlml_only
                  have hw4 : FullWitnessInv c F0 F_cur st4.core :=
                    { hwl with
                      arena := { hwl.arena with len_ok := hwl.arena.len_ok }
                      watches := hwl.watches.with_wstk rfl rfl rfl rfl rfl
                        (fun _ hr => hr) }
                  have hstep1_n : (step + 1#32).toNat = step.toNat + 1 :=
                    fid_bv32_add1_n (by omega)
                  refine wp_join_state (α := BitVec 32 × BitVec 64)
                    (fun ⟨bk', br'⟩ => (bk', br', ()))
                    (fun ⟨bk', _⟩ mf4 =>
                      (bk' = 0#32 ∨ (1 ≤ bk'.toNat ∧ bk'.toNat < step.toNat + 1)) ∧
                        mf4 = m)
                    (fun _ ⟨bk', br'⟩ mf4 ⟨hbk', hmf4⟩ => ?_)
                    (fun Jbk hJbk => ?_)
                  · rcases hmf4 with rfl
                    c0_hfast_nogrp
                    exact ihst (bump', step + 1#32, new_qn, bk', br', ()) _
                      (by dsimp only; rw [hstep1_n]; omega)
                      ⟨st4, by
                        dsimp only [st4, sb4, lm4, co3, sc3]
                        have hsc_step_bv :
                            (BitVec.ofNat 32 (fidStepsCap c.scratch_cap) +
                              step).toNat = sc_n + step.toNat := by
                          rw [← fid_bv64_32]; exact hsc_step_nat
                        have h2sc_step_bv :
                            (2 * BitVec.ofNat 32 (fidStepsCap c.scratch_cap) +
                              step).toNat = 2 * sc_n + step.toNat := by
                          rw [← fid_bv64_32]; exact h2sc_step_nat
                        have h3sc_step_bv :
                            (3 * BitVec.ofNat 32 (fidStepsCap c.scratch_cap) +
                              step).toNat = 3 * sc_n + step.toNat := by
                          rw [← fid_bv64_32]; exact h3sc_step_nat
                        have hbv8_1 :
                            BitVec.ofNat (OfNat.ofNat 8) (OfNat.ofNat 1) =
                              (1#8 : BitVec 8) := rfl
                        have hpar_eq : bump + max_new = par_off := rfl
                        simp only [fid_bv64_32, hsc_step_bv, h2sc_step_bv,
                          h3sc_step_bv, hbv8_1, hpar_eq] at hm
                        exact hm,
                       ⟨{ hlen3.core_ok with lit_mark_len := hlm4_l },
                        { hlen3.scratch_ok with scratch_buf_len := hsb4_l }⟩,
                       hw4, hndl, by dsimp only [st4, sc3, s3, sc2]; exact hextl,
                       hlv0l, hdml, hcvl, hfuell, harl, hall, hmrkl, html, htrl,
                       by rw [hstep1_n]; omega, by rw [hstep1_n]; exact hst_lt,
                       by rw [hbump'_nat, hpar_off_nat]; omega,
                       by rw [hbump'_nat, hpar_off_nat]; omega,
                       by
                         have hidx_eq : 2 * sc_n + ((step + 1#32).toNat - 1) =
                             2 * sc_n + step.toNat := by
                           rw [hstep1_n, Nat.add_sub_cancel]
                         dsimp only [st4, sb4]; rw [hidx_eq]
                         rw [List.getElem?_set_ne (by omega),
                           List.getElem?_set_self
                             (by rw [List.length_set, List.length_set,
                               hlen3.scratch_ok.scratch_buf_len]; omega),
                           Option.getD_some],
                       by
                         rw [hstep1_n, hbump'_nat]
                         exact fidBvaMatrixInv_congr (s' := st4)
                           rfl rfl rfl rfl hmat4,
                       by rw [hstep1_n]; exact hbk',
                       hlm4_hi, by rw [hstep1_n]; exact hlm4_set,
                       by rw [hstep1_n]; exact hlm4_only⟩
                  · c0_hfast
                    · have hstp1_sub : step + 1 - 1 = step := by
                        change step + 1#32 - 1#32 = step
                        apply BitVec.eq_of_toNat_eq
                        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                          rw [show (1#32 : BitVec 32).toNat = 1 from rfl, hstep1_n]
                          omega)), hstep1_n]
                        show step.toNat + 1 - 1 = step.toNat; omega
                      rw [hstp1_sub]
                      exact hJbk (step, _) m ⟨Or.inr ⟨hst1, Nat.lt_succ_self step.toNat⟩, rfl⟩
                    all_goals
                      exact hJbk ⟨best_k, best_red⟩ m
                        ⟨hbkl.imp id (fun ⟨h1, h2⟩ => ⟨h1, Nat.lt_succ_of_lt h2⟩),
                         rfl⟩
            · have hrem_simp : (2 ^ 64 - bump.toNat + c.scratch_cap) % 2 ^ 64 %
                  2 ^ 32 / 2 = (c.scratch_cap - bump.toNat) / 2 := by
                rw [show (2 ^ 64 - bump.toNat + c.scratch_cap) % 2 ^ 64 =
                    c.scratch_cap - bump.toNat by omega,
                  Nat.mod_eq_of_lt (by omega)]
              have hrem32 : (BitVec.setWidth 32 (BitVec.ofNat 64 c.scratch_cap -
                  BitVec.setWidth 64 bump) >>> (1 : Nat)).toNat =
                  (c.scratch_cap - bump.toNat) / 2 := by
                have hsub : (BitVec.ofNat 64 c.scratch_cap -
                    BitVec.setWidth 64 bump).toNat =
                    c.scratch_cap - bump.toNat := by
                  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                    rw [fid_bv64_32, BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega)]; omega))]
                  rw [fid_bv64_32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, hsub,
                  Nat.shiftRight_eq_div_pow, Nat.pow_one,
                  Nat.mod_eq_of_lt (by omega)]
              c0_hfast
              · exact hJmn _ _
                  ⟨Nat.le_refl _, by rw [hrem_simp] at hc; omega, rfl⟩
              · refine hJmn _ _ ⟨?_, ?_, rfl⟩
                · change (BitVec.setWidth 32 (BitVec.ofNat 64 c.scratch_cap -
                    BitVec.setWidth 64 bump) >>> (1 : Nat)).toNat ≤ _
                  rw [hrem32]; rw [hrem_simp] at hc; omega
                · change (BitVec.setWidth 32 (BitVec.ofNat 64 c.scratch_cap -
                    BitVec.setWidth 64 bump) >>> (1 : Nat)).toNat ≤ _
                  rw [hrem32]; exact Nat.le_refl _
      · c0_hfast_nogrp
        exact hJexit (bump, step, cur_qn, best_k, best_red) ml
          ⟨stl, stepExitBody_of_inv hinvl_cp⟩
    · c0_hfast_nogrp
      exact hJexit (bump, step, cur_qn, best_k, best_red) ml
        ⟨stl, stepExitBody_of_inv hinvl_cp⟩
  · c0_hfast_nogrp
    exact hJexit (bump, step, cur_qn, best_k, best_red) ml
      ⟨stl, stepExitBody_of_inv hinvl_cp⟩


private theorem fid_try_lit_exit_phase_wp (Γ : Env)
    (hCommit : ∀ a m Q X, fidBvaCommitSpec a m Q X →
      Γ "full_bva_commit" [i64, i32] [.bool] a m Q X)
    {Q : Post [Ty.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s stl : FullState} {R : Mem 64 → Prop}
    {f0 bump step cur_qn best_k : BitVec 32} {init_cv0 best_red : BitVec 64}
    {ml : Mem 64}
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hlm : FullLitMarksClear c s)
    (hexit : StepExitBody c F0 F_cur s R (fidStepsCap c.scratch_cap)
      step best_k bump.toNat stl ml)
    (hQ : ∀ (ok : Bool) s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) →
      s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X
      (Blocks.get
        (fidTryLitExitBlock Val Cont c.pScratchBuf c.pLitMark
          (c.hdr, f0, init_cv0, ())
          (BitVec.ofNat 32 (fidStepsCap c.scratch_cap), ()) c.pArena
          ((fun _ _ => False), ()))
        .here (bump, step, cur_qn, best_k, best_red, ()))
      ml := by
  let sc_n := fidStepsCap c.scratch_cap
  have hmx : c.max_vars < 2 * 2 ^ 28 := by
    simpa only [dimacsBound] using c.hmaxv
  have hsc_le : sc_n ≤ 256 := fidStepsCap_le_256 c.scratch_cap
  obtain ⟨hml, hlenl, hwl, hndl, hextl, hlv0l, hdml, hcvl, hfuell, harl,
          hall, hmrkl, html, htrl, hst1, hst_sc, hbump_ge, hbump_le,
          hmatl, hbkl, hlml_hi, hlml_set, hlml_only⟩ := hexit
  dsimp only [fidTryLitExitBlock, Blocks.get]
  refine wp_loop_inv (ts := [i32])
    (fun (ci, ()) mc => ∃ lmi : List (BitVec 8),
      let stc : FullState :=
        { stl with core := { stl.core with lit_mark := lmi } }
      (FullMem c stc ⋆ R) mc ∧ lmi.length = 2 * c.max_vars ∧
      ci.toNat ≤ step.toNat ∧
      (∀ l < 2 * c.max_vars, (lmi[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
      (∀ l < 2 * c.max_vars, (lmi[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
        ∃ r, ci.toNat ≤ r ∧ r < step.toNat ∧
          (stl.scratch.scratch_buf[r]?.getD 0#32).toNat = l))
    (fun (ci, _) _ => step.toNat - ci.toNat)
    (fun Jci hJci => hJci (0#32, ()) ml
      ⟨stl.core.lit_mark, hml, hlenl.core_ok.lit_mark_len, Nat.zero_le _,
       hlml_hi, fun l hl hne => by
         obtain ⟨r, hr, heq⟩ := hlml_only l hl hne
         exact ⟨r, Nat.zero_le _, hr, heq⟩⟩)
    (fun Jci (ci, ()) mc ⟨lmi, hmc, hlmi_l, hci_le, hlmi_hi, hlmi_only⟩ ihci => ?_)
  c0_hsplit
  · have hci_lt : ci.toNat < step.toNat := by assumption
    have hci_sb :
        (BitVec.setWidth 64 ci).toNat < stl.scratch.scratch_buf.length := by
      rw [bv64_setWidth_32, hlenl.scratch_ok.scratch_buf_len]; omega
    have hci_sb' : ci.toNat < stl.scratch.scratch_buf.length := by
      simpa only [bv64_setWidth_32] using hci_sb
    have hci_lm : (BitVec.setWidth 64
        (stl.scratch.scratch_buf[(BitVec.setWidth 64 ci).toNat]'hci_sb)).toNat <
        lmi.length := by
      have hr_lt := (hmatl.2.2.2.2.2 ci.toNat hci_lt).1
      rw [List.getElem?_eq_getElem hci_sb', Option.getD_some] at hr_lt
      rw [bv64_setWidth_32, hlmi_l]
      exact Nat.lt_of_lt_of_le hr_lt
        (Nat.mul_le_mul_left 2 (by rw [hcvl]; exact hcv_le))
    have hci1 : (ci + 1#32).toNat = ci.toNat + 1 :=
      fid_bv32_add1_n (by omega)
    c0_hfast_nogrp
    exact ihci (ci + 1#32, ()) m
      (by dsimp only; rw [hci1]; omega)
      ⟨lmi.set (stl.scratch.scratch_buf[ci.toNat]'(by
          simpa only [bv64_setWidth_32] using hci_sb)).toNat 0#8,
       by simpa only [bv64_setWidth_32] using hm,
       by rw [List.length_set, hlmi_l], by rw [hci1]; exact hci_lt,
       fun l hl => by
         by_cases he : l = (stl.scratch.scratch_buf[ci.toNat]'(by
             simpa only [bv64_setWidth_32] using hci_sb)).toNat
         · subst he; rw [List.getElem?_set_self (by omega), Option.getD_some]
           decide
         · rw [List.getElem?_set_ne (Ne.symm he)]; exact hlmi_hi l hl,
       fun l hl hne => by
         by_cases he : l = (stl.scratch.scratch_buf[ci.toNat]'(by
             simpa only [bv64_setWidth_32] using hci_sb)).toNat
         · subst he; rw [List.getElem?_set_self (by omega), Option.getD_some]
             at hne
           exact absurd rfl hne
         · rw [List.getElem?_set_ne (Ne.symm he)] at hne
           obtain ⟨r, hr1, hr2, heq⟩ := hlmi_only l hl hne
           have hner : r ≠ ci.toNat := fun h => by
             subst h; rw [List.getElem?_eq_getElem (by
               simpa only [bv64_setWidth_32] using hci_sb), Option.getD_some]
               at heq
             exact he heq.symm
           exact ⟨r, by rw [hci1]; omega, hr2, heq⟩⟩
  · have hlm_clr_done : FullLitMarksClear c
        { stl with core := { stl.core with lit_mark := lmi } } := by
      refine fid_bva_try_lit_clear_lm_done (stepf := step.toNat)
        (fun v hv => by have := hlm.1 v hv; rwa [hmrkl]) hlmi_hi
        (fun l hl hne => ?_)
      obtain ⟨r, hr1, hr2, heq⟩ := hlmi_only l hl hne
      have hci_eq : ci.toNat = step.toNat := by
        have h1 : ¬ ci.toNat < step.toNat := by assumption
        omega
      rw [hci_eq] at hr1; exact ⟨r, hr1, hr2, heq⟩
    let stc : FullState :=
      { stl with core := { stl.core with lit_mark := lmi } }
    have hinv_clr : FullDenseInvW c F0 F_cur stc :=
      ⟨⟨{ hlenl.core_ok with lit_mark_len := hlmi_l }, hlenl.scratch_ok⟩,
       { hwl with
         arena := { hwl.arena with len_ok := hwl.arena.len_ok }
         watches := hwl.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
       hlm_clr_done, hndl, hextl, hlv0l, hdml⟩
    have hmat_c : FidBvaMatrixInv c F_cur stc step.toNat bump.toNat :=
      fidBvaMatrixInv_congr (s := stl) (s' := stc) rfl rfl rfl rfl hmatl
    c0_hsplit
    · exact hQ false stc mc hinv_clr.toDense (hcvl ▸ Nat.le_refl _)
        (fun h => by contradiction) (by dsimp only [stc]; exact hfuell)
        (by dsimp only [stc]; exact html) (by dsimp only [stc]; exact htrl) hmc
    · have hbk1 : 1 ≤ best_k.toNat := by
        rcases hbkl with rfl | ⟨h1, _⟩
        · exact absurd rfl (by assumption)
        · exact h1
      have hbk_lt_sc : best_k.toNat < sc_n := by
        rcases hbkl with rfl | ⟨_, h2⟩
        · exact absurd rfl (by assumption)
        · exact Nat.lt_of_lt_of_le h2 hst_sc
      have hbk_lt_st : best_k.toNat < step.toNat := by
        rcases hbkl with rfl | ⟨_, h2⟩
        · exact absurd rfl (by assumption)
        · exact h2
      have hcore_c : stc.core.fuel = stl.core.fuel := rfl
      have hcv_c_le : stc.core.cur_vars ≤ c.max_vars :=
        hinv_clr.1.core_ok.cur_vars_le
      have hcv_c : stc.core.cur_vars = s.core.cur_vars := hcvl
      have har_c : stc.core.arena = s.core.arena := harl
      have halen_c : stc.core.arena_len ≤ stc.core.arena.length := by
        rw [hinv_clr.1.core_ok.arena_len_arr]; exact hinv_clr.1.core_ok.arena_len_le
      have hbf_end_n : (best_k + 1#32).toNat = best_k.toNat + 1 :=
        fid_bv32_add1_n (by omega)
      have h2cv_c : (stc.core.cur_vars <<< 1) % 2 ^ 64 = 2 * stc.core.cur_vars := by
        rw [Nat.shiftLeft_eq, Nat.pow_one]; omega
      c0_hfast_nogrp
      refine wp_loop_inv
        (fun (nt1, fi, ()) mfi => ∃ stfi : FullState,
          fi.toNat ≤ best_k.toNat + 1 ∧ FidBvaTouchedInv c stc R nt1 stfi mfi)
        (fun (_, fi, _) _ => best_k.toNat + 1 - fi.toNat)
        (fun Jfi hJfi => hJfi (0#64, 0#32, ()) mc
          ⟨stc, Nat.zero_le _, rfl, rfl, rfl, rfl, rfl, rfl,
           hinv_clr.1.scratch_ok, Nat.zero_le _,
           fun _ hk => absurd hk (Nat.not_lt_zero _), hmc⟩)
        (fun Jfi (nt1, fi, ()) mfi ⟨stfi, hfi_le, hcore1, hsb1, htm1, htr1, hll1,
            hel1, hscl1, hnt1_le, hws2_ok1, hmfi⟩ ihfi => ?_)
      c0_hsplit
      · have hfi_lt : fi.toNat < best_k.toNat + 1 := by
          simpa only [hbf_end_n] using
            (by assumption : fi.toNat < (best_k + 1#32).toNat)
        have hfi1 : (fi + 1#32).toNat = fi.toNat + 1 :=
          fid_bv32_add1_n (by omega)
        have hfi_sb :
            (BitVec.setWidth 64 fi).toNat < stfi.scratch.scratch_buf.length := by
          rw [bv64_setWidth_32, hscl1.scratch_buf_len]; omega
        have hfi_sb' : fi.toNat < stfi.scratch.scratch_buf.length := by
          simpa only [bv64_setWidth_32] using hfi_sb
        have hfl_lt : (stfi.scratch.scratch_buf[fi.toNat]'hfi_sb').toNat <
            2 * stc.core.cur_vars := by
          have h1 := (hmat_c.2.2.2.2.2 fi.toNat (by omega)).1
          have hfi_c : fi.toNat < stc.scratch.scratch_buf.length := by
            rwa [← hsb1]
          rw [List.getElem?_eq_getElem hfi_c, Option.getD_some] at h1
          simpa only [hsb1, hcore1] using h1
        have hfl_ws : (BitVec.setWidth 64
            (stfi.scratch.scratch_buf[(BitVec.setWidth 64 fi).toNat]'hfi_sb)).toNat <
            stfi.scratch.wsort.length := by
          rw [bv64_setWidth_32, hscl1.wsort_len]
          exact Nat.lt_of_lt_of_le hfl_lt (Nat.mul_le_mul_left 2 hcv_c_le)
        c0_hfast_nogrp
        refine wp_join_state (α := BitVec 64 × FullState) (fun x => (x.1, ()))
          (fun ⟨nt1a, st1a⟩ m1a => FidBvaTouchedInv c stc R nt1a st1a m1a)
          (fun _ ⟨nt1a, st1a⟩ m1a ⟨hca, hsba, htma, htra, hlla, hela, hscla,
              hnt1a_le, hws2a_ok, hm1a⟩ => ?_)
          (fun Ja hJa => ?_)
        · have heq_fi :
              stfi.scratch.scratch_buf[(BitVec.setWidth 64 fi).toNat]'hfi_sb =
                stfi.scratch.scratch_buf[fi.toNat]'hfi_sb' := by
            simp only [bv64_setWidth_32]
          have hneg_lt_fi : (stfi.scratch.scratch_buf[fi.toNat]'hfi_sb' ^^^
              1#32).toNat < 2 * stc.core.cur_vars := by
            rw [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl]
            exact litNeg_lt_two_mul hfl_lt
          have hneg_lt :
              (stfi.scratch.scratch_buf[(BitVec.setWidth 64 fi).toNat]'hfi_sb ^^^
                1#32).toNat < 2 * stc.core.cur_vars := by
            rw [heq_fi]; exact hneg_lt_fi
          have hneg_ws : (BitVec.setWidth 64
              ((stfi.scratch.scratch_buf[
                (BitVec.setWidth 64 fi).toNat]'hfi_sb) ^^^
                1#32)).toNat < st1a.scratch.wsort.length := by
            rw [bv64_setWidth_32, hscla.wsort_len]
            exact Nat.lt_of_lt_of_le hneg_lt (Nat.mul_le_mul_left 2 hcv_c_le)
          refine wp_join_state (α := BitVec 64 × FullState) (fun x => (x.1, ()))
            (fun ⟨nt1b, st1b⟩ m1b => FidBvaTouchedInv c stc R nt1b st1b m1b)
            (fun _ ⟨nt1b, st1b⟩ m1b hinv1b =>
              ihfi (nt1b, fi + 1#32, ()) m1b
                (by dsimp only; rw [hfi1]; omega)
                ⟨st1b, by rw [hfi1]; exact hfi_lt, hinv1b⟩)
            (fun Jb hJb => ?_)
          c0_hsplit
          · c0_hsplit
            · have hnt1a_lt : nt1a.toNat < 2 * stc.core.cur_vars := by
                rw [show 2 * stc.core.cur_vars =
                    2 * (stl.core.cur_vars % 2 ^ 64) % 2 ^ 64 by omega]
                assumption
              have hnt1a_ws2 : nt1a.toNat < st1a.scratch.work_stk2.length := by
                rw [hscla.work_stk2_len]
                exact Nat.lt_of_lt_of_le hnt1a_lt
                  (Nat.mul_le_mul_left 2 hcv_c_le)
              c0_hfast_nogrp; try dsimp only at hm
              exact hJb ⟨nt1a + 1#64, _⟩ m
                (fid_bva_touched_push hcv_c_le hmx hnt1a_lt hneg_lt hca hsba htma
                  htra hlla hela hscla hws2a_ok hm)
            · exact hJb ⟨nt1a, st1a⟩ m1a
                ⟨hca, hsba, htma, htra, hlla, hela, hscla, hnt1a_le, hws2a_ok,
                 hm1a⟩
          · exact hJb ⟨nt1a, st1a⟩ m1a
              ⟨hca, hsba, htma, htra, hlla, hela, hscla, hnt1a_le, hws2a_ok, hm1a⟩
        · c0_hsplit
          · c0_hsplit
            · have hnt1_lt : nt1.toNat < 2 * stc.core.cur_vars := by
                rw [show 2 * stc.core.cur_vars =
                    2 * (stl.core.cur_vars % 2 ^ 64) % 2 ^ 64 by omega]
                assumption
              have hnt1_ws2 : nt1.toNat < stfi.scratch.work_stk2.length := by
                rw [hscl1.work_stk2_len]
                exact Nat.lt_of_lt_of_le hnt1_lt (Nat.mul_le_mul_left 2 hcv_c_le)
              c0_hfast_nogrp; try dsimp only at hm
              exact hJa ⟨nt1 + 1#64, _⟩ m
                (fid_bva_touched_push hcv_c_le hmx hnt1_lt hfl_lt hcore1 hsb1 htm1
                  htr1 hll1 hel1 hscl1 hws2_ok1 hm)
            · exact hJa ⟨nt1, stfi⟩ mfi
                ⟨hcore1, hsb1, htm1, htr1, hll1, hel1, hscl1, hnt1_le, hws2_ok1,
                 hmfi⟩
          · exact hJa ⟨nt1, stfi⟩ mfi
              ⟨hcore1, hsb1, htm1, htr1, hll1, hel1, hscl1, hnt1_le, hws2_ok1,
               hmfi⟩
      · obtain ⟨_, _, hqn_best2, hqn_best_le, _, hrow_best⟩ :=
          hmat_c.2.2.2.2.2 best_k.toNat hbk_lt_st
        have h2sc_bk_nat :
            ((BitVec.ofNat 32 2) * BitVec.ofNat 32 sc_n + best_k).toNat =
              2 * sc_n + best_k.toNat :=
          fid_bv32_mul_sc_add_step (by omega) hsc_le (by omega)
        have h2sc_bk_sb : (BitVec.setWidth 64
            ((BitVec.ofNat 32 2) * BitVec.ofNat 32 sc_n + best_k)).toNat <
            stfi.scratch.scratch_buf.length := by
          rw [fid_bv64_32, h2sc_bk_nat, hscl1.scratch_buf_len]; omega
        have hbk_sb : (BitVec.setWidth 64 best_k).toNat <
            stfi.scratch.scratch_buf.length := by
          rw [fid_bv64_32, hscl1.scratch_buf_len]; omega
        have hsc_bk_nat : (BitVec.ofNat 32 sc_n + best_k).toNat =
            sc_n + best_k.toNat := by
          simpa only [Nat.one_mul] using
            fid_bv32_ksc_add_step (k := 1) (sc := sc_n)
              (by omega) hsc_le (by omega)
        have hsc_bk_sb : (BitVec.setWidth 64
            (BitVec.ofNat 32 sc_n + best_k)).toNat <
            stfi.scratch.scratch_buf.length := by
          rw [fid_bv64_32, hsc_bk_nat, hscl1.scratch_buf_len]; omega
        c0_hfast_nogrp
        let qn_best := stc.scratch.scratch_buf[2 * sc_n + best_k.toNat]'(by
          rw [hinv_clr.1.scratch_ok.scratch_buf_len]; omega)
        let bkey := stc.scratch.scratch_buf[best_k.toNat]'(by
          rw [hinv_clr.1.scratch_ok.scratch_buf_len]; omega)
        let brow_off := stc.scratch.scratch_buf[sc_n + best_k.toNat]'(by
          rw [hinv_clr.1.scratch_ok.scratch_buf_len]; omega)
        have hstc_sb_len : stc.scratch.scratch_buf.length = c.scratch_cap :=
          hinv_clr.1.scratch_ok.scratch_buf_len
        have hqn_best_len :
            fidStepsCap c.scratch_cap * 2 + best_k.toNat <
              stc.scratch.scratch_buf.length := by
          rw [hstc_sb_len]; change sc_n * 2 + best_k.toNat < _; omega
        have h2sc_bk_stc : 2 * sc_n + best_k.toNat <
            stc.scratch.scratch_buf.length := by
          rw [hstc_sb_len]; omega
        have hsc_bk_stc : sc_n + best_k.toNat <
            stc.scratch.scratch_buf.length := by
          rw [hstc_sb_len]; omega
        have hqn_best_getD :
            stc.scratch.scratch_buf[
              2 * fidStepsCap c.scratch_cap + best_k.toNat]?.getD 0#32 =
              qn_best := by
          dsimp only [qn_best]
          change stc.scratch.scratch_buf[2 * sc_n + best_k.toNat]?.getD 0#32 = _
          rw [List.getElem?_eq_getElem h2sc_bk_stc, Option.getD_some]
        have hbrow_getD :
            stc.scratch.scratch_buf[
              fidStepsCap c.scratch_cap + best_k.toNat]?.getD 0#32 =
              brow_off := by
          dsimp only [brow_off]
          change stc.scratch.scratch_buf[sc_n + best_k.toNat]?.getD 0#32 = _
          rw [List.getElem?_eq_getElem hsc_bk_stc, Option.getD_some]
        rw [hqn_best_getD, hbrow_getD] at hqn_best_le
        rw [hqn_best_getD] at hqn_best2
        refine wp_loop_inv
          (fun (ntm, qim, ()) mtm => ∃ stm : FullState,
            qim.toNat ≤ qn_best.toNat ∧ FidBvaTouchedInv c stc R ntm stm mtm)
          (fun (_, qim, _) _ => qn_best.toNat - qim.toNat)
          (fun Jtm hJtm => hJtm (nt1, 0#32, ()) mfi
            ⟨stfi, Nat.zero_le _, hcore1, hsb1, htm1, htr1, hll1, hel1, hscl1,
             hnt1_le, hws2_ok1, hmfi⟩)
          (fun Jtm (ntm, qim, ()) mtm ⟨stm, hqim_le, hcorem, hsbm, htmm, htrm,
              hllm, helm, hsclm, hntm_le, hws2m_ok, hmtm⟩ ihtm => ?_)
        c0_hsplit
        · have hqim_lt : qim.toNat < qn_best.toNat := by
            have hidx_hc :
                (BitVec.toNat (2 : BitVec 32) *
                  (fidStepsCap c.scratch_cap % 2 ^ 32) +
                  best_k.toNat) % 2 ^ 32 = 2 * sc_n + best_k.toNat := by
              rw [show BitVec.toNat (2 : BitVec 32) = 2 from rfl,
                Nat.mod_eq_of_lt (by omega : fidStepsCap c.scratch_cap < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega)]
            have h1_lt : 2 * sc_n + best_k.toNat < c.scratch_cap := by omega
            have h1_bd : (BitVec.toNat (2 : BitVec 32) *
                (fidStepsCap c.scratch_cap % 2 ^ 32) +
                best_k.toNat) % 2 ^ 32 < stfi.scratch.scratch_buf.length := by
              rw [hidx_hc, hscl1.scratch_buf_len]; exact h1_lt
            have h1 : qim.toNat <
                (stfi.scratch.scratch_buf[
                  (BitVec.toNat (2 : BitVec 32) *
                    (fidStepsCap c.scratch_cap % 2 ^ 32) +
                    best_k.toNat) % 2 ^ 32]'h1_bd).toNat := by
              assumption
            simp only [hidx_hc] at h1
            dsimp only [qn_best]
            simpa only [← hsb1] using h1
          have hqim1 : (qim + 1#32).toNat = qim.toNat + 1 :=
            fid_bv32_add1_n (by omega)
          have hrow_idx_nat : (brow_off + qim).toNat =
              brow_off.toNat + qim.toNat := by
            simp only [bv_c0]; rw [Nat.mod_eq_of_lt (by omega)]
          have hrow_idx_sb :
              (BitVec.setWidth 64 (brow_off + qim)).toNat <
                stm.scratch.scratch_buf.length := by
            rw [fid_bv64_32, hrow_idx_nat, hsclm.scratch_buf_len]; omega
          have hqim_lt_row : qim.toNat <
              (stc.scratch.scratch_buf[
                2 * sc_n + best_k.toNat]?.getD 0#32).toNat := by
            rw [hqn_best_getD]; exact hqim_lt
          obtain ⟨res_t, _, _, hct_ok, _, _⟩ :=
            hrow_best qim.toNat hqim_lt_row
          let ct := stc.scratch.scratch_buf[brow_off.toNat + qim.toNat]'(by
            rw [hinv_clr.1.scratch_ok.scratch_buf_len]; omega)
          have hct_getD :
              stc.scratch.scratch_buf[brow_off.toNat + qim.toNat]?.getD 0#32 =
                ct := by
            dsimp only [ct]
            rw [List.getElem?_eq_getElem
                (by rw [hinv_clr.1.scratch_ok.scratch_buf_len]; omega),
              Option.getD_some]
          rw [hbrow_getD, hct_getD] at hct_ok
          have hct_eq_m :
              stm.scratch.scratch_buf[
                (BitVec.setWidth 64 (brow_off + qim)).toNat]'hrow_idx_sb = ct := by
            dsimp only [ct]
            simp only [hsbm, fid_bv64_32, hrow_idx_nat]
          have hbrow_stfi_eq :
              stfi.scratch.scratch_buf[(BitVec.setWidth 64
                (BitVec.ofNat 32 (fidStepsCap c.scratch_cap) + best_k)).toNat]'hsc_bk_sb =
                brow_off := by
            apply Option.some.inj
            rw [← List.getElem?_eq_getElem hsc_bk_sb]
            dsimp only [brow_off, sc_n]
            rw [hsb1, fid_bv64_32, hsc_bk_nat, List.getElem?_eq_getElem hsc_bk_stc]
          have hrow_idx_stfi : (BitVec.setWidth 64
              (stfi.scratch.scratch_buf[(BitVec.setWidth 64
                (BitVec.ofNat 32 (fidStepsCap c.scratch_cap) + best_k)).toNat]'hsc_bk_sb +
                qim)).toNat < stm.scratch.scratch_buf.length := by
            simpa only [hbrow_stfi_eq] using hrow_idx_sb
          have hct_eq_m_stfi :
              stm.scratch.scratch_buf[(BitVec.setWidth 64
                (stfi.scratch.scratch_buf[(BitVec.setWidth 64
                  (BitVec.ofNat 32 (fidStepsCap c.scratch_cap) + best_k)).toNat]'hsc_bk_sb +
                  qim)).toNat]'hrow_idx_stfi = ct := by
            apply Option.some.inj
            rw [← List.getElem?_eq_getElem hrow_idx_stfi, hbrow_stfi_eq,
              List.getElem?_eq_getElem hrow_idx_sb, hct_eq_m]
          c0_hfast_nogrp
          refine wp_join_state1 (t := i64) (α := BitVec 64 × FullState)
            (fun x => x.1)
            (fun ⟨nt1b, st1b⟩ mb => FidBvaTouchedInv c stc R nt1b st1b mb)
            (fun _ ⟨nt1b, st1b⟩ mb hinv1b => by
              c0_hfast_nogrp
              exact ihtm (nt1b, qim + 1#32, ()) mb (by dsimp only; rw [hqim1]; omega)
                ⟨st1b, by rw [hqim1]; exact hqim_lt, hinv1b⟩)
            (fun Jct hJct => ?_)
          have hsc_mod_eq :
              (fidStepsCap c.scratch_cap + best_k.toNat) % 2 ^ 32 =
                sc_n + best_k.toNat := by
            dsimp only [sc_n]; exact Nat.mod_eq_of_lt (by omega)
          have hrow_mod_eq :
              (brow_off.toNat + qim.toNat) % 2 ^ 32 =
                brow_off.toNat + qim.toNat := Nat.mod_eq_of_lt (by omega)
          have hstfi_eq_raw :
              stfi.scratch.scratch_buf[sc_n + best_k.toNat]'(by
                rw [hsb1, hstc_sb_len]; omega) = brow_off := by
            apply Option.some.inj
            rw [← List.getElem?_eq_getElem (by rw [hsb1, hstc_sb_len]; omega)]
            dsimp only [brow_off]; rw [hsb1, List.getElem?_eq_getElem hsc_bk_stc]
          have hct_sim :
              stm.scratch.scratch_buf[brow_off.toNat + qim.toNat]'(by
                rw [hsbm, hstc_sb_len]; omega) = ct := by
            dsimp only [ct]; apply Option.some.inj
            rw [← List.getElem?_eq_getElem (by rw [hsbm, hstc_sb_len]; omega),
              hsbm, List.getElem?_eq_getElem (by rw [hstc_sb_len]; omega)]
          c0_hsplit
          · have hbin_ct : (ct &&& 0x80000000#32) ≠ 0#32 := by
              have hc_cp := hc
              simp only [hsc_mod_eq, hstfi_eq_raw, hrow_mod_eq, hct_sim] at hc_cp
              simpa only [show (2147483648 : BitVec 32) = 0x80000000#32 from rfl,
                show (0 : BitVec 32) = 0#32 from rfl] using hc_cp
            unfold FidBvaRowEntryOk at hct_ok
            rw [ite_eq_left hbin_ct] at hct_ok
            have hot_lt : (ct &&& 0x7FFFFFFF#32).toNat <
                2 * stc.core.cur_vars := hct_ok.1
            have hot_ws : (BitVec.setWidth 64 (ct &&& 0x7FFFFFFF#32)).toNat <
                stm.scratch.wsort.length := by
              rw [bv64_setWidth_32, hsclm.wsort_len]
              exact Nat.lt_of_lt_of_le hot_lt (Nat.mul_le_mul_left 2 hcv_c_le)
            have hot_ws_stfi : (BitVec.setWidth 64
                ((stm.scratch.scratch_buf[(BitVec.setWidth 64
                  (stfi.scratch.scratch_buf[(BitVec.setWidth 64
                    (BitVec.ofNat 32 (fidStepsCap c.scratch_cap) + best_k)).toNat]'hsc_bk_sb +
                    qim)).toNat]'hrow_idx_stfi) &&& 0x7FFFFFFF#32)).toNat <
                stm.scratch.wsort.length := by
              rw [hct_eq_m_stfi]; exact hot_ws
            c0_hfast_nogrp
            refine wp_join_state1 (t := i64) (α := BitVec 64 × FullState)
              (fun x => x.1)
              (fun ⟨nt1a, st1a⟩ ma => FidBvaTouchedInv c stc R nt1a st1a ma)
              (fun _ ⟨nt1a, st1a⟩ ma hinv1a => hJct ⟨nt1a, st1a⟩ ma hinv1a)
              (fun Jct0 hJct0 => ?_)
            c0_hsplit
            · c0_hsplit
              · have hntm_lt : ntm.toNat < 2 * stc.core.cur_vars := by
                  rw [show 2 * stc.core.cur_vars =
                      2 * (stl.core.cur_vars % 2 ^ 64) % 2 ^ 64 by omega]
                  assumption
                have hntm_ws2 : ntm.toNat < stm.scratch.work_stk2.length := by
                  rw [hsclm.work_stk2_len]
                  exact Nat.lt_of_lt_of_le hntm_lt
                    (Nat.mul_le_mul_left 2 hcv_c_le)
                c0_hfast_nogrp; try dsimp only at hm
                exact hJct0 ⟨ntm + 1#64, _⟩ m
                  (fid_bva_touched_push hcv_c_le hmx hntm_lt hot_lt
                    hcorem hsbm htmm htrm hllm helm hsclm hws2m_ok
                    (by rw [← hct_eq_m_stfi]; exact hm))
              · c0_hfast_nogrp
                exact hJct0 ⟨ntm, stm⟩ mtm
                  ⟨hcorem, hsbm, htmm, htrm, hllm, helm, hsclm, hntm_le, hws2m_ok, hmtm⟩
            · c0_hfast_nogrp
              exact hJct0 ⟨ntm, stm⟩ mtm
                ⟨hcorem, hsbm, htmm, htrm, hllm, helm, hsclm, hntm_le, hws2m_ok, hmtm⟩
          · have hbin_ct : (ct &&& 0x80000000#32) = 0#32 := by
              have hc_cp := hc
              simp only [hsc_mod_eq, hstfi_eq_raw, hrow_mod_eq, hct_sim] at hc_cp
              simpa only [show (2147483648 : BitVec 32) = 0x80000000#32 from rfl,
                show (0 : BitVec 32) = 0#32 from rfl] using hc_cp
            unfold FidBvaRowEntryOk at hct_ok
            rw [ite_eq_right (fun h' => h' hbin_ct)] at hct_ok
            obtain ⟨hct_ref, hct_ng, _, hct_sz5, _, _, _⟩ := hct_ok
            have hct_wf := hinv_clr.2.1.arena.refs_wf ct.toNat hct_ref
            have hct2_n : (BitVec.setWidth 64 ct + 2).toNat = ct.toNat + 2 :=
              fid_bv64_add2_n
            have hct2_lt_c : ct.toNat + 2 < stc.core.arena.length := by
              have := hct_wf.1; exact Nat.lt_of_lt_of_le (by omega) halen_c
            have hct2_ar : (BitVec.setWidth 64 ct + 2).toNat <
                stm.core.arena.length := by
              rw [hct2_n, hcorem]; exact hct2_lt_c
            have hct2_ar_stfi : (BitVec.setWidth 64
                (stm.scratch.scratch_buf[(BitVec.setWidth 64
                  (stfi.scratch.scratch_buf[(BitVec.setWidth 64
                    (BitVec.ofNat 32 (fidStepsCap c.scratch_cap) + best_k)).toNat]'hsc_bk_sb +
                    qim)).toNat]'hrow_idx_stfi) + 2).toNat < stm.core.arena.length := by
              rw [hct_eq_m_stfi]; exact hct2_ar
            have hct_sz_eq : (stc.core.arena[ct.toNat + 2]'hct2_lt_c).toNat =
                fullArenaClauseSizeCore stc.core ct.toNat := by
              unfold fullArenaClauseSizeCore
              rw [List.getElem?_eq_getElem hct2_lt_c, Option.getD_some]
            let csz_t := stc.core.arena[ct.toNat + 2]'hct2_lt_c
            have hcsz_5 : csz_t.toNat ≤ 5 := by
              dsimp only [csz_t]; rw [hct_sz_eq]; exact hct_sz5
            have hct_end_ar :
                ct.toNat + 3 + csz_t.toNat ≤ stc.core.arena.length := by
              dsimp only [csz_t]; rw [hct_sz_eq]
              exact Nat.le_trans hct_wf.2.2.1
                (Nat.le_trans hct_wf.2.2.2.1 halen_c)
            c0_hfast_nogrp
            refine wp_loop_inv
              (fun (ntj, tj, ()) mtj => ∃ stj : FullState,
                tj.toNat ≤ csz_t.toNat ∧ FidBvaTouchedInv c stc R ntj stj mtj)
              (fun (_, tj, _) _ => csz_t.toNat - tj.toNat)
              (fun Jtj hJtj => hJtj (ntm, 0#32, ()) mtm
                ⟨stm, Nat.zero_le _, hcorem, hsbm, htmm, htrm, hllm, helm, hsclm,
                 hntm_le, hws2m_ok, hmtm⟩)
              (fun Jtj (ntj, tj, ()) mtj ⟨stj, htj_le, hcorej, hsbj, htmj, htrj,
                  hllj, helj, hsclj, hntj_le, hws2j_ok, hmtj⟩ ihtj => ?_)
            c0_hsplit
            · have htj_lt : tj.toNat < csz_t.toNat := by
                have hc_cp := hc
                have hmod2 :
                    (ct.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
                      ct.toNat + 2 := fid_bv64_add2_mod
                simp only [hsc_mod_eq, hstfi_eq_raw, hrow_mod_eq, hct_sim,
                  hmod2, hcorem] at hc_cp
                simpa only [csz_t] using hc_cp
              have htj1 : (tj + 1#32).toNat = tj.toNat + 1 :=
                fid_bv32_add1_n (by omega)
              have hctj_n :
                  (BitVec.setWidth 64 ct + 3 + BitVec.setWidth 64 tj).toNat =
                    ct.toNat + 3 + tj.toNat := fid_bv64_add3_n
              have hctj_ar_c : ct.toNat + 3 + tj.toNat < stc.core.arena.length :=
                Nat.lt_of_lt_of_le
                  (Nat.add_lt_add_left htj_lt (ct.toNat + 3)) hct_end_ar
              have hctj_ar_bv :
                  (BitVec.setWidth 64 ct + 3 + BitVec.setWidth 64 tj).toNat <
                    stj.core.arena.length := by
                rw [hctj_n, hcorej]; exact hctj_ar_c
              have hql_mem :
                  (stc.core.arena[ct.toNat + 3 + tj.toNat]'hctj_ar_c).toNat ∈
                    fullArenaClauseLitsCore stc.core ct.toNat :=
                List.mem_of_getElem?
                  (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem
                    (k := stc.core) (r := ct.toNat) (j := tj.toNat)
                    (by rw [← hct_sz_eq]; exact htj_lt) hctj_ar_c)
              have hql_lt :
                  (stc.core.arena[ct.toNat + 3 + tj.toNat]'hctj_ar_c).toNat <
                    2 * stc.core.cur_vars :=
                hinv_clr.2.1.arena.lits_lt ct.toNat hct_ref hct_ng _ hql_mem
              have hql_lt_bv :
                  (stj.core.arena[(BitVec.setWidth 64 ct + 3 +
                    BitVec.setWidth 64 tj).toNat]'hctj_ar_bv).toNat <
                    2 * stc.core.cur_vars := by
                simpa only [hctj_n, hcorej] using hql_lt
              have hql_ws_bv : (BitVec.setWidth 64
                  (stj.core.arena[(BitVec.setWidth 64 ct + 3 +
                    BitVec.setWidth 64 tj).toNat]'hctj_ar_bv)).toNat <
                  stj.scratch.wsort.length := by
                rw [bv64_setWidth_32, hsclj.wsort_len]
                exact Nat.lt_of_lt_of_le hql_lt_bv
                  (Nat.mul_le_mul_left 2 hcv_c_le)
              let ct_m := stm.scratch.scratch_buf[(BitVec.setWidth 64
                (stfi.scratch.scratch_buf[(BitVec.setWidth 64
                  (BitVec.ofNat 32 (fidStepsCap c.scratch_cap) +
                    best_k)).toNat]'hsc_bk_sb +
                  qim)).toNat]'hrow_idx_stfi
              have hctj_ar_m :
                  (BitVec.setWidth 64 ct_m + 3 + BitVec.setWidth 64 tj).toNat <
                    stj.core.arena.length := by
                dsimp only [ct_m]; rw [hct_eq_m_stfi]; exact hctj_ar_bv
              have hql_lt_m :
                  (stj.core.arena[(BitVec.setWidth 64 ct_m + 3 +
                    BitVec.setWidth 64 tj).toNat]'hctj_ar_m).toNat <
                    2 * stc.core.cur_vars := by
                dsimp only [ct_m]; simpa only [hct_eq_m_stfi] using hql_lt_bv
              have hql_ws_m : (BitVec.setWidth 64
                  (stj.core.arena[(BitVec.setWidth 64 ct_m + 3 +
                    BitVec.setWidth 64 tj).toNat]'hctj_ar_m)).toNat <
                  stj.scratch.wsort.length := by
                rw [bv64_setWidth_32, hsclj.wsort_len]
                exact Nat.lt_of_lt_of_le hql_lt_m
                  (Nat.mul_le_mul_left 2 hcv_c_le)
              c0_hfast_nogrp
              refine wp_join_state1 (t := i64) (α := BitVec 64 × FullState)
                (fun x => x.1)
                (fun ⟨ntj1, stj1⟩ mj1 => FidBvaTouchedInv c stc R ntj1 stj1 mj1)
                (fun _ ⟨ntj1, stj1⟩ mj1 hinvj => by
                  c0_hfast_nogrp
                  exact ihtj (ntj1, tj + 1#32, ()) mj1
                    (by dsimp only; rw [htj1]; omega)
                    ⟨stj1, by rw [htj1]; exact htj_lt, hinvj⟩)
                (fun Jq1 hJq1 => ?_)
              c0_hsplit
              · c0_hsplit
                · c0_hsplit
                  · have hntj_lt : ntj.toNat < 2 * stc.core.cur_vars := by
                      rw [show 2 * stc.core.cur_vars =
                          2 * (stl.core.cur_vars % 2 ^ 64) % 2 ^ 64 by omega]
                      assumption
                    have hntj_ws2 : ntj.toNat < stj.scratch.work_stk2.length := by
                      rw [hsclj.work_stk2_len]
                      exact Nat.lt_of_lt_of_le hntj_lt
                        (Nat.mul_le_mul_left 2 hcv_c_le)
                    c0_hfast_nogrp; try dsimp only at hm
                    exact hJq1 ⟨ntj + 1#64, _⟩ m
                      (fid_bva_touched_push hcv_c_le hmx hntj_lt hql_lt_m
                        hcorej hsbj htmj htrj hllj helj hsclj hws2j_ok
                        (by simp only [bv64_setWidth_32] at hm; exact hm))
                  · exact hJq1 ⟨ntj, stj⟩ mtj
                      ⟨hcorej, hsbj, htmj, htrj, hllj, helj, hsclj, hntj_le,
                       hws2j_ok, hmtj⟩
                · exact hJq1 ⟨ntj, stj⟩ mtj
                    ⟨hcorej, hsbj, htmj, htrj, hllj, helj, hsclj, hntj_le,
                     hws2j_ok, hmtj⟩
              · exact hJq1 ⟨ntj, stj⟩ mtj
                  ⟨hcorej, hsbj, htmj, htrj, hllj, helj, hsclj, hntj_le,
                   hws2j_ok, hmtj⟩
            · c0_hfast_nogrp
              exact hJct ⟨ntj, stj⟩ mtj
                ⟨hcorej, hsbj, htmj, htrj, hllj, helj, hsclj, hntj_le,
                 hws2j_ok, hmtj⟩
        · -- Loop 3: clear tmark[touched[tz]] = 0
          c0_hfast_nogrp
          refine wp_loop_inv
            (fun (tz, ()) mtz => ∃ stz : FullState,
              tz.toNat ≤ ntm.toNat ∧ stz.core = stc.core ∧
              stz.scratch.scratch_buf = stc.scratch.scratch_buf ∧
              stz.scratch.tarjan_mark = stc.scratch.tarjan_mark ∧
              stz.scratch.tarjan_reach = stc.scratch.tarjan_reach ∧
              stz.scratch.last_learned = stc.scratch.last_learned ∧
              stz.scratch.extend_len = stc.scratch.extend_len ∧
              stz.scratch.work_stk2 = stm.scratch.work_stk2 ∧
              stz.scratch.LengthsOk c ∧ (FullMem c stz ⋆ R) mtz)
            (fun (tz, _) _ => ntm.toNat - tz.toNat)
            (fun Jtz hJtz => hJtz (0#64, ()) mtm
              ⟨stm, Nat.zero_le _, hcorem, hsbm, htmm, htrm, hllm, helm, rfl,
               hsclm, hmtm⟩)
            (fun Jtz (tz, ()) mtz ⟨stz, htz_le, hcorez, hsbz, htmz, htrz, hllz,
                helz, hws2z, hsclz, hmtz⟩ ihtz => ?_)
          c0_hsplit
          · have htz_lt : tz.toNat < ntm.toNat := by assumption
            have htz_max : tz.toNat < 2 * c.max_vars :=
              Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le htz_lt hntm_le)
                (Nat.mul_le_mul_left 2 hcv_c_le)
            have htz1 : (tz + 1#64).toNat = tz.toNat + 1 :=
              fid_bv64_add1_n (by omega)
            have htz_ws2 : tz.toNat < stz.scratch.work_stk2.length := by
              rw [hsclz.work_stk2_len]; exact htz_max
            have htl_lt : (stz.scratch.work_stk2[tz.toNat]'htz_ws2).toNat <
                2 * stc.core.cur_vars := by
              have h1 := hws2m_ok tz.toNat htz_lt
              have htz_m : tz.toNat < stm.scratch.work_stk2.length := by
                rwa [← hws2z]
              rw [List.getElem?_eq_getElem htz_m, Option.getD_some] at h1
              simpa only [hws2z] using h1
            have htl_wsz : (BitVec.setWidth 64
                (stz.scratch.work_stk2[tz.toNat]'htz_ws2)).toNat <
                stz.scratch.wsort.length := by
              rw [bv64_setWidth_32, hsclz.wsort_len]
              exact Nat.lt_of_lt_of_le htl_lt (Nat.mul_le_mul_left 2 hcv_c_le)
            c0_hfast_nogrp; try dsimp only at hm
            exact ihtz (tz + 1#64, ()) m
              (by dsimp only; rw [htz1]; omega)
              (fid_bva_touched_clear_step htz_lt htz1 hcorez hsbz htmz htrz
                hllz helz hws2z hsclz hm)
          · c0_hfast
            let st_tc : FullState :=
              { stz with scratch := { stz.scratch with res_sz := ntm } }
            have hinv_tc : FullDenseInvW c F0 F_cur st_tc := by
              have htc_eq : st_tc = { stc with scratch := st_tc.scratch } := by
                dsimp only [st_tc]
                exact congrArg
                  (fun k => ({ core := k,
                               scratch := { stz.scratch with res_sz := ntm } } :
                    FullState))
                  hcorez
              rw [htc_eq]
              exact fullDenseInv_with_core_aux (tc' := stc.core.tmp_cnt)
                (tl' := stc.core.tmp_len) (sc' := st_tc.scratch) hinv_clr
                hinv_clr.1.core_ok.repr_len hinv_clr.1.core_ok.min_clr_len_arr
                hinv_clr.1.core_ok.tmp_len_arr hinv_clr.1.core_ok.flags_len
                hinv_clr.1.core_ok.tmp_len_le
                { hsclz with wsort_len := hsclz.wsort_len } hllz helz
            have hmat_wk :
                FidBvaMatrixInv c F_cur stc (best_k.toNat + 1) bump.toNat :=
              fid_bva_matrixInv_substep (k := best_k.toNat + 1) (by omega)
                (by omega) hmat_c
            have hmat_tc :
                FidBvaMatrixInv c F_cur st_tc (best_k.toNat + 1) bump.toNat :=
              fidBvaMatrixInv_congr
                (by dsimp only [st_tc]; exact congrArg (·.cur_vars) hcorez)
                (by dsimp only [st_tc]; exact congrArg (·.arena) hcorez)
                (by dsimp only [st_tc]; exact congrArg (·.arena_len) hcorez)
                (by dsimp only [st_tc]; exact hsbz)
                hmat_wk
            refine wp_call_of_spec _ _ (hCommit _ _ _ _ ?_)
            refine ⟨c, F0, F_cur, st_tc, R, bump.toNat, rfl, hinv_tc, hbk1,
              hbk_lt_sc, hmat_tc, hm,
              fun ok s' m' hinv' hcv' hcv_inc hfuel' htm' htr' hm' =>
                hQ ok s' m' hinv' (by rw [← hcv_c, ← hcorez]; exact hcv')
                  (by intro hok; rw [← hcv_c, ← hcorez]; exact hcv_inc hok)
                  (hfuel'.trans (by rw [hcorez, hcore_c]; exact hfuell))
                  (htm'.trans (htmz.trans html))
                  (htr'.trans (htrz.trans htrl)) hm'⟩

theorem full_bva_try_lit_fid_wp (Γ : Env)
    (hSteps : ∀ a m Q X, fidBvaStepsCapSpec a m Q X →
      Γ "full_bva_steps_cap_fid" [i64] [i32] a m Q X)
    (hScan : ∀ a m Q X, fidBvaScanCandsSpec a m Q X →
      Γ "full_bva_scan_cands" [i64, i32, i32, i64] [i32] a m Q X)
    (hPick : ∀ a m Q X, FullBvaHeap.fullBvaPickCandSpec a m Q X →
      Γ "full_bva_pick_cand" [i64, i32, i32] [i32] a m Q X)
    (hFilter : ∀ a m Q X, fidBvaFilterRowSpec a m Q X →
      Γ "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32] a m Q X)
    (hCommit : ∀ a m Q X, fidBvaCommitSpec a m Q X →
      Γ "full_bva_commit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fidBvaTryLitSpec a m Q X →
      Func.wp Γ full_bva_try_lit_body a m Q X := by
  rintro ⟨h, f0, init_cv0, ⟨⟩⟩ m Q X ⟨c, F0, s, R, hh, hinv0, hf0_lt, hm, hQ⟩
  subst hh
  obtain ⟨F_cur, hdw0⟩ := hinv0.exists_witness
  obtain ⟨hlen, hw, hlm, hnd, hext, hlv0, hdm⟩ := hdw0
  have hinv : FullDenseInvW c F0 F_cur s := ⟨hlen, hw, hlm, hnd, hext, hlv0, hdm⟩
  have hclen := hlen.core_ok; have hslen := hlen.scratch_ok
  have hcv_le := hclen.cur_vars_le
  have hmx : c.max_vars < 2 * 2 ^ 28 := by simpa only [dimacsBound] using c.hmaxv
  have h2cv : 2 * s.core.cur_vars < 2 ^ 64 := by omega
  have hvals_f0 : (BitVec.setWidth 64 f0).toNat < s.core.vals.length := by
    rw [bv64_setWidth_32, hclen.vals_len]; omega
  have hscr_u64 : c.scratch_cap < 2 ^ 64 := by
    have := c.hscr; unfold dimacsBound at this; omega
  have hsc_eq : (BitVec.ofNat 64 c.scratch_cap).toNat = c.scratch_cap := by
    simp only [bv_c0]; omega
  unfold Func.wp full_bva_try_lit_body; dsimp only
  c0_hfast_nogrp
  refine fid_wp_call_steps_cap Γ hSteps ?_
  rw [hsc_eq]
  c0_hsplit
  · c0_hfast_nogrp
    exact hQ false s m hinv.toDense (Nat.le_refl _) (fun h => by contradiction) rfl rfl rfl hm
  · c0_hsplit
    · c0_hfast_nogrp
      exact hQ false s m hinv.toDense (Nat.le_refl _) (fun h => by contradiction) rfl rfl rfl hm
    · have hsc_nz : (BitVec.ofNat 32 (fidStepsCap c.scratch_cap)) ≠ 0#32 := by assumption
      have hsc_pos : 0 < fidStepsCap c.scratch_cap := fid_sc_pos_of_ne_zero hsc_nz
      have hsc_le : fidStepsCap c.scratch_cap ≤ 256 := fidStepsCap_le_256 c.scratch_cap
      have hcv_lt : s.core.cur_vars < c.max_vars := by
        have h1 : ¬ c.max_vars % 2 ^ 64 ≤ s.core.cur_vars % 2 ^ 64 := by assumption
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1; omega
      c0_hfast_nogrp
      c0_hsplit
      · c0_hfast_nogrp
        exact hQ false s m hinv.toDense (Nat.le_refl _) (fun h => by contradiction) rfl rfl rfl hm
      · c0_hfast_nogrp
        refine wp_join_state (α := BitVec 64) (fun x => (x, ()))
          (fun icv mf => icv.toNat ≤ 2 * s.core.cur_vars ∧ mf = m)
          (fun _ init_lits mf ⟨hinit_lits, hmf⟩ => ?_)
          (fun Jicv hJicv => ?_)
        · subst mf
          c0_hfast_nogrp
          c0_hsplit
          · c0_hfast_nogrp
            exact hQ false s m hinv.toDense (Nat.le_refl _)
              (fun h => by contradiction) rfl rfl rfl hm
          · let sc_n := fidStepsCap c.scratch_cap
            have h4sc_cap : 4 * sc_n ≤ c.scratch_cap := fidStepsCap_mul4_le c.scratch_cap
            let row0_max_n := (c.scratch_cap - 4 * sc_n) / 3
            have hr0_max_ge2 : 2 ≤ row0_max_n := by
              have hc_raw : ¬ ((BitVec.ofNat 64 c.scratch_cap -
                  BitVec.setWidth 64 (BitVec.ofNat 32 sc_n <<<
                    (2 : BitVec 32))) / 3).toNat % 2 ^ 32 < (2 : BitVec 32).toNat := by assumption
              have hsub := fid_bv64_sub_shl2 hscr_u64 h4sc_cap hsc_le
              have hdiv := fid_bv64_div3 (BitVec.ofNat 64 c.scratch_cap -
                BitVec.setWidth 64 (BitVec.ofNat 32 sc_n <<< (2 : BitVec 32)))
              rw [hdiv, hsub] at hc_raw
              have hscap := c.hscr; unfold dimacsBound at hscap
              have hmod : (c.scratch_cap - 4 * sc_n) / 3 < 2 ^ 32 := by omega
              rw [Nat.mod_eq_of_lt hmod] at hc_raw
              have h2n : (2 : BitVec 32).toNat = 2 := rfl
              rw [h2n] at hc_raw
              dsimp only [row0_max_n]
              omega
            have h2f0 : (BitVec.setWidth 64 f0 <<< 1#64).toNat = 2 * f0.toNat :=
              bv64_shl1_lit_toNat f0
            have h2f1 : ((BitVec.setWidth 64 f0 <<< 1#64) + 1#64).toNat = 2 * f0.toNat + 1 :=
              bv64_shl1_lit_add1_toNat f0
            have h2f0_l : (BitVec.setWidth 64 f0 <<< 1#64).toNat < s.core.wvec.length := by
              rw [h2f0, hclen.wvec_len]; omega
            have h2f1_l : ((BitVec.setWidth 64 f0 <<< 1#64) + 1#64).toNat <
                s.core.wvec.length := by
              rw [h2f1, hclen.wvec_len]; omega
            c0_hfast_nogrp
            let off0 := s.core.wvec[2 * f0.toNat]' (by rw [hclen.wvec_len]; omega)
            let sz0 := s.core.wvec[2 * f0.toNat + 1]' (by rw [hclen.wvec_len]; omega)
            have hwatches : DenseWatchesInv F_cur s.core := by
              have hw := hinv.2.1.watches
              unfold ModeWatchesInv at hw
              simpa [hdm] using hw
            have hslice0 := hwatches.slices f0.toNat (by omega)
            have hoff_sz0 := hwatches.layout.bounds f0.toNat (by omega)
            have hws_cap := hclen.wlen_le
            have hwlen_bd := c.hwcap
            dsimp only [fullWatchOffCore, fullWatchSizeCore] at hslice0 hoff_sz0
            rw [List.getElem?_eq_getElem (by rw [hclen.wvec_len]; omega), Option.getD_some]
              at hslice0 hoff_sz0
            rw [List.getElem?_eq_getElem (by rw [hclen.wvec_len]; omega), Option.getD_some]
              at hslice0 hoff_sz0
            refine wp_loop_inv (ts := [i64, i32, i64])
              (fun (wi, r0n, fticks, ()) mw => ∃ sbr : List (BitVec 32),
                let stw : FullState := { s with scratch := { s.scratch with scratch_buf := sbr } }
                (FullMem c stw ⋆ R) mw ∧ sbr.length = c.scratch_cap ∧
                wi.toNat ≤ sz0.toNat ∧ r0n.toNat ≤ row0_max_n ∧
                fticks.toNat ≤ wi.toNat ∧
                DenseWatchSliceOk F_cur s.core f0.toNat (off0.toNat + wi.toNat)
                  (sz0.toNat - wi.toNat) ∧
                ∀ qm < r0n.toNat, ∃ res : List Nat,
                  (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
                  FidBvaRowEntryOk F_cur s f0.toNat (sbr[4 * sc_n + qm]?.getD 0#32) res ∧
                  (cnfOfClauses F_cur).EntailsClause (cnfClause (f0.toNat :: res)))
              (fun (wi, _, _, _) _ => sz0.toNat - wi.toNat)
              (fun Jw hJw => by
                exact hJw (0#64, 0#32, 0#64, ()) m
                  ⟨s.scratch.scratch_buf, hm, hslen.scratch_buf_len, Nat.zero_le _, Nat.zero_le _,
                   Nat.zero_le _, by simpa using hslice0, fun _ hq => by simp at hq⟩)
              (fun Jw (wi, r0n, fticks, ()) mw
                  ⟨sbr, hmw, hsbr_l, hwi_le, hr0n_le, hft_le, hslicew, hrow⟩ ihw => ?_)
            c0_hfast_nogrp
            refine wp_join_state0 (fun (_ : Unit) mf => mf = mw)
              (fun Js _ mf hmf => ?_)
              (fun Js hJs => ?_)
            rotate_left 1
            · c0_hfast_nogrp
              rotate_left 1
              · try c0_hfast_nogrp
                exact hJs () mw rfl
              · try c0_hfast_nogrp
                exact hJs () mw rfl
              have h2f1_idx : (2 * f0.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 <
                  s.core.wvec.length := by
                rw [show ((1 : BitVec 64)).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega), hclen.wvec_len]; omega
              have hwi_hc : wi.toNat <
                  (s.core.wvec[(2 * f0.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'h2f1_idx).toNat :=
                by assumption
              have hwi_lt : wi.toNat < sz0.toNat := by
                dsimp [sz0]
                simpa only [show ((1 : BitVec 64)).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega : 2 * f0.toNat + 1 < 2 ^ 64)] using hwi_hc
              have hr0n_hc : r0n.toNat <
                  ((c.scratch_cap - 4 * sc_n) / 3) % 2 ^ 32 := by
                have h1 : r0n.toNat <
                    ((BitVec.ofNat 64 c.scratch_cap -
                        BitVec.setWidth 64 (BitVec.ofNat 32 sc_n <<<
                          (2 : BitVec 32))) / 3).toNat % 2 ^ 32 := by assumption
                have hsub := fid_bv64_sub_shl2 hscr_u64 h4sc_cap hsc_le
                have hdiv := fid_bv64_div3 (BitVec.ofNat 64 c.scratch_cap -
                  BitVec.setWidth 64 (BitVec.ofNat 32 sc_n <<< (2 : BitVec 32)))
                rwa [hdiv, hsub] at h1
              have hr0n_lt : r0n.toNat < row0_max_n := by
                dsimp only [row0_max_n] at hr0n_hc ⊢
                have hscap := c.hscr; unfold dimacsBound at hscap
                have hmod : (c.scratch_cap - 4 * sc_n) / 3 < 2 ^ 32 := by omega
                rwa [Nat.mod_eq_of_lt hmod] at hr0n_hc
              have hoff_wi_n : (BitVec.setWidth 64 off0 + wi).toNat = off0.toNat + wi.toNat := by
                simp only [bv_c0]
                have hmod : (off0.toNat + wi.toNat) % 2 ^ 64 = off0.toNat + wi.toNat := by
                  have := hoff_sz0; unfold dimacsBound at hwlen_bd; omega
                exact hmod
              have hwi_ws : (BitVec.setWidth 64 off0 + wi).toNat < s.core.wstk.length := by
                dsimp only [off0] at hoff_wi_n
                rw [hoff_wi_n, hclen.wstk_len_arr]
                dsimp only [sz0] at hwi_lt; omega
              have h2f0_nat : (BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat = 2 * f0.toNat := by
                simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
              have h2f0_nat_l : (BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat <
                  s.core.wvec.length := by
                rw [h2f0_nat, hclen.wvec_len]; omega
              have hwi_ws_raw : (BitVec.setWidth 64
                  (s.core.wvec[(BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat]'h2f0_nat_l) +
                  wi).toNat < s.core.wstk.length := by
                simpa only [h2f0_nat, off0] using hwi_ws
              have hwi1_n : (wi + 1#64).toNat = wi.toNat + 1 := by
                simp only [bv_c0]; have := hoff_sz0; unfold dimacsBound at hwlen_bd; omega
              have hr0n1_n : (r0n + 1#32).toNat = r0n.toNat + 1 :=
                fid_bv32_add1_n (by have hscap := c.hscr; unfold dimacsBound at hscap; omega)
              have hft1_n : (fticks + 1#64).toNat = fticks.toNat + 1 :=
                fid_bv64_add1_n (by have := hoff_sz0; unfold dimacsBound at hwlen_bd; omega)
              have hhdr_sz_n : (BitVec.ofNat 32 sc_n <<< 2#32).toNat = 4 * sc_n := by
                simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
                have : sc_n * 4 < 2 ^ 32 := by omega
                rw [Nat.mod_eq_of_lt this, Nat.mul_comm]
              have h4sc_r0_n : (BitVec.ofNat 32 sc_n <<< 2#32 + r0n).toNat =
                  4 * sc_n + r0n.toNat := by
                simp only [bv_c0]
                have hscap := c.hscr; unfold dimacsBound at hscap
                rw [hhdr_sz_n, Nat.mod_eq_of_lt (by omega)]
              have h4sc_r0_n' : (BitVec.setWidth 64 (BitVec.ofNat 32 sc_n <<< 2#32 + r0n)).toNat =
                  4 * sc_n + r0n.toNat := by
                rw [bv64_setWidth_32, h4sc_r0_n]
              have h4sc_r0_sb : (BitVec.setWidth 64 (BitVec.ofNat 32 sc_n <<< 2#32 + r0n)).toNat <
                  sbr.length := by
                rw [h4sc_r0_n', hsbr_l]
                have hscap := c.hscr; unfold dimacsBound at hscap; omega
              c0_hfast_nogrp
              let Loop1ContInv : (BitVec 64 × BitVec 32 × BitVec 64) → Mem 64 → Prop :=
                fun (wi', r0n', fticks') mh => wi'.toNat ≤ sz0.toNat ∧
                  r0n'.toNat ≤ row0_max_n ∧
                  fticks'.toNat ≤ wi'.toNat ∧
                  sz0.toNat - wi'.toNat < sz0.toNat - wi.toNat ∧
                  ∃ sbr' : List (BitVec 32),
                    let stw' : FullState :=
                      { s with scratch := { s.scratch with scratch_buf := sbr' } }
                    (FullMem c stw' ⋆ R) mh ∧ sbr'.length = c.scratch_cap ∧
                    DenseWatchSliceOk F_cur s.core f0.toNat (off0.toNat + wi'.toNat)
                      (sz0.toNat - wi'.toNat) ∧
                    ∀ qm < r0n'.toNat, ∃ res : List Nat,
                      (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
                      FidBvaRowEntryOk F_cur s f0.toNat
                        (sbr'[4 * sc_n + qm]?.getD 0#32) res ∧
                      (cnfOfClauses F_cur).EntailsClause (cnfClause (f0.toNat :: res))
              refine wp_join_state (α := BitVec 64 × BitVec 32 × BitVec 64)
                (fun p => (p.1, p.2.1, p.2.2, ()))
                Loop1ContInv
                (fun _ (wi', r0n', fticks') mh
                    ⟨h1, h2, hft', hdec, sbr', hmh', hsbrl', hslice', hrow'⟩ => by
                  c0_hfast_nogrp
                  exact ihw (wi', r0n', fticks', ()) mh hdec
                    ⟨sbr', hmh', hsbrl', h1, h2, hft', hslice', hrow'⟩)
                (fun Js hJs => ?_)
              c0_hfast_nogrp
              · have hbin_w0 : (s.core.wstk[off0.toNat + wi.toNat]'(by omega) &&&
                    0x80000000#32) ≠ 0#32 := by
                  have h1 : (s.core.wstk[(BitVec.setWidth 64
                      (s.core.wvec[(BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat]'h2f0_nat_l) +
                      wi).toNat]'hwi_ws_raw &&& (2147483648 : BitVec 32)) ≠ (0 : BitVec 32) := by
                    assumption
                  simpa only [h2f0_nat, off0, hoff_wi_n,
                    show (2147483648 : BitVec 32) = 0x80000000#32 from rfl,
                    show (0 : BitVec 32) = 0#32 from rfl] using h1
                obtain ⟨hot_lt, hent_ot, hslice_next⟩ :=
                  bva_slice_bin_info hslicew (by omega) (by omega) hbin_w0
                have hot_eq : (BitVec.setWidth 64
                    (s.core.wstk[(BitVec.setWidth 64 off0 + wi).toNat]'hwi_ws &&&
                      0x7FFFFFFF#32)).toNat =
                    (s.core.wstk[off0.toNat + wi.toNat]'(by omega) &&& 0x7FFFFFFF#32).toNat := by
                  simp only [hoff_wi_n, bv64_setWidth_32]
                have hot_vals : (BitVec.setWidth 64
                    (s.core.wstk[(BitVec.setWidth 64 off0 + wi).toNat]'hwi_ws &&&
                      0x7FFFFFFF#32)).toNat < s.core.vals.length := by
                  rw [hot_eq, hclen.vals_len]; omega
                have hot_vals_raw : (BitVec.setWidth 64
                    (s.core.wstk[(BitVec.setWidth 64
                      (s.core.wvec[(BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat]'h2f0_nat_l) +
                      wi).toNat]'hwi_ws_raw &&&
                      (2147483647 : BitVec 32))).toNat < s.core.vals.length := by
                  simpa only [h2f0_nat, off0,
                    show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl] using hot_vals
                refine wp_join_state1 (t := i32) (α := BitVec 32) (fun r => r)
                  (fun r0n' mj => r0n'.toNat ≤ row0_max_n ∧ ∃ sbr' : List (BitVec 32),
                    let stw' : FullState :=
                      { s with scratch := { s.scratch with scratch_buf := sbr' } }
                    (FullMem c stw' ⋆ R) mj ∧ sbr'.length = c.scratch_cap ∧
                    ∀ qm < r0n'.toNat, ∃ res : List Nat,
                      (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
                      FidBvaRowEntryOk F_cur s f0.toNat (sbr'[4 * sc_n + qm]?.getD 0#32) res ∧
                      (cnfOfClauses F_cur).EntailsClause (cnfClause (f0.toNat :: res)))
                  (fun _ r0n' mj ⟨hr0n', sbr', hmj', hsbrl', hrow'⟩ => by
                    c0_hfast_nogrp
                    exact hJs (wi + 1#64, r0n', fticks + 1#64) mj
                      ⟨by rw [hwi1_n]; omega, hr0n', by rw [hwi1_n, hft1_n]; omega,
                       by rw [hwi1_n]; omega,
                       sbr', hmj', hsbrl',
                       by rw [hwi1_n, show off0.toNat + (wi.toNat + 1) = off0.toNat + wi.toNat + 1
                            by omega,
                          show sz0.toNat - (wi.toNat + 1) = sz0.toNat - wi.toNat - 1 by omega]
                          exact hslice_next,
                       hrow'⟩)
                  (fun Js1 hJs1 => ?_)
                c0_hfast_nogrp
                · let w0v := s.core.wstk[(BitVec.setWidth 64
                      (s.core.wvec[(BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat]'h2f0_nat_l) +
                      wi).toNat]'hwi_ws_raw
                  have hw0v_eq : w0v = s.core.wstk[off0.toNat + wi.toNat]'(by omega) := by
                    dsimp only [w0v, off0]
                    congr 1
                    simp only [h2f0_nat]
                    exact hoff_wi_n
                  let ot := (s.core.wstk[off0.toNat + wi.toNat]'(by omega)) &&& 0x7FFFFFFF#32
                  refine hJs1 (r0n + 1#32) m ⟨by rw [hr0n1_n]; omega,
                    sbr.set (4 * sc_n + r0n.toNat) w0v,
                    by dsimp only [sc_n, w0v]; rw [← h4sc_r0_n']; exact hm,
                    by simp [hsbr_l], fun qm hqm => ?_⟩
                  rw [hr0n1_n] at hqm
                  by_cases hqe : qm = r0n.toNat
                  · subst hqe
                    rw [List.getElem?_set_self (by omega), Option.getD_some, hw0v_eq]
                    refine ⟨[ot.toNat], fun x hx => by simp at hx; subst hx; exact hot_lt,
                      by simp, ?_, hent_ot⟩
                    unfold FidBvaRowEntryOk; rw [ite_eq_left hbin_w0]
                    exact ⟨hot_lt, rfl, hent_ot⟩
                  · rw [List.getElem?_set_ne (by omega)]
                    exact hrow qm (by omega)
                · exact hJs1 r0n mw ⟨hr0n_le, sbr, hmw, hsbr_l, hrow⟩
              · have hnbin_w0 : (s.core.wstk[off0.toNat + wi.toNat]'(by omega) &&&
                    0x80000000#32) = 0#32 := by
                  have hno : (s.core.wstk[(BitVec.setWidth 64
                      (s.core.wvec[(BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat]'h2f0_nat_l) +
                      wi).toNat]'hwi_ws_raw &&&
                      (2147483648 : BitVec 32)) = (0 : BitVec 32) := by assumption
                  simpa only [h2f0_nat, off0, hoff_wi_n,
                    show (2147483648 : BitVec 32) = 0x80000000#32 from rfl,
                    show (0 : BitVec 32) = 0#32 from rfl] using hno
                obtain ⟨_hrem2, hslice_next⟩ :=
                  bva_slice_occ_info hslicew (by omega) (by omega) hnbin_w0
                have hwi_next_lt : (wi + 1#64).toNat < sz0.toNat := by rw [hwi1_n]; omega
                rcases denseWatchSliceOk_step hslicew (by omega) with
                  ⟨_, hw0s, hbin_ne, _, _, _, _⟩ |
                  ⟨_, cr, _, _, hcrs, _, _, _, hcr_ref, _⟩
                · exfalso
                  rw [List.getElem?_eq_getElem (by omega)] at hw0s
                  exact absurd (Option.some.inj hw0s ▸ hnbin_w0) hbin_ne
                have hoff_wi1_n :
                    (BitVec.setWidth 64 off0 + (wi + (1 : BitVec 64))).toNat =
                      off0.toNat + wi.toNat + 1 := by
                  change (BitVec.setWidth 64 off0 + (wi + 1#64)).toNat = _
                  simp only [bv_c0, hwi1_n]
                  have := hoff_sz0; unfold dimacsBound at hwlen_bd; omega
                have hwi1_ws : (BitVec.setWidth 64 off0 + (wi + (1 : BitVec 64))).toNat <
                    s.core.wstk.length := by
                  dsimp only [off0] at hoff_wi1_n
                  rw [hoff_wi1_n, hclen.wstk_len_arr]
                  dsimp only [sz0] at hwi_next_lt; omega
                have hwi1_ws_raw : (BitVec.setWidth 64
                    (s.core.wvec[(BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat]'h2f0_nat_l) +
                    (wi + (1 : BitVec 64))).toNat < s.core.wstk.length := by
                  simpa only [h2f0_nat, off0] using hwi1_ws
                have hcr_val :
                    s.core.wstk[(BitVec.setWidth 64 off0 + (wi + (1 : BitVec 64))).toNat]'hwi1_ws =
                    cr := by
                  have h1 : s.core.wstk[off0.toNat + wi.toNat + 1]'(by
                      rw [← hoff_wi1_n]; exact hwi1_ws) = cr :=
                    Option.some.inj (by
                      rw [← List.getElem?_eq_getElem (by rw [← hoff_wi1_n]; exact hwi1_ws)]
                      exact hcrs)
                  simpa only [hoff_wi1_n] using h1
                have hcr_val_raw : s.core.wstk[(BitVec.setWidth 64
                    (s.core.wvec[(BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat]'h2f0_nat_l) +
                    (wi + (1 : BitVec 64))).toNat]'hwi1_ws_raw = cr := by
                  simpa only [h2f0_nat, off0] using hcr_val
                have hcr_wf := hinv.2.1.arena.refs_wf cr.toNat hcr_ref
                have halen_le := hclen.arena_len_le
                have har_bd := c.harena; unfold dimacsBound at har_bd
                have har_arr := hclen.arena_len_arr
                have hcr2_n : (BitVec.setWidth 64 cr + 2#64).toNat = cr.toNat + 2 :=
                  bv64_add_toNat (by
                    rw [bv64_setWidth_32, show (2#64).toNat = 2 from rfl]
                    have := hcr_wf.1; have := halen_le; omega)
                have hcr2_n_of : (BitVec.setWidth 64 cr + (2 : BitVec 64)).toNat = cr.toNat + 2 :=
                  hcr2_n
                have hcr0_ar : (BitVec.setWidth 64 cr).toNat < s.core.arena.length := by
                  rw [bv64_setWidth_32]; have := hcr_wf.1; have := halen_le; rw [har_arr]; omega
                have hcr2_ar : (BitVec.setWidth 64 cr + 2#64).toNat < s.core.arena.length := by
                  rw [hcr2_n]; have := hcr_wf.1; have := halen_le; rw [har_arr]; omega
                have hcr0_ar_raw : (BitVec.setWidth 64
                    (s.core.wstk[(BitVec.setWidth 64
                      (s.core.wvec[(BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat]'h2f0_nat_l) +
                      (wi + (1 : BitVec 64))).toNat]'hwi1_ws_raw)).toNat <
                    s.core.arena.length := by
                  rw [hcr_val_raw]; exact hcr0_ar
                have hcr2_ar_raw : (BitVec.setWidth 64
                    (s.core.wstk[(BitVec.setWidth 64
                      (s.core.wvec[(BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat]'h2f0_nat_l) +
                      (wi + (1 : BitVec 64))).toNat]'hwi1_ws_raw) + (2 : BitVec 64)).toNat <
                    s.core.arena.length := by
                  rw [hcr_val_raw]; exact hcr2_ar
                have hwi2_n : (wi + 1#64 + 1#64).toNat = wi.toNat + 2 := by
                  simp only [bv_c0]; have := hoff_sz0; unfold dimacsBound at hwlen_bd; omega
                refine wp_join_state (α := BitVec 64 × BitVec 32 × BitVec 64)
                  (fun p => (p.1, p.2.1, p.2.2, ()))
                  Loop1ContInv
                  (fun _ (wi', r0n', fticks') mh hinv' => by
                    c0_hfast_nogrp; exact hJs (wi', r0n', fticks') mh hinv')
                  (fun Js1 hJs1 => ?_)
                c0_hfast_nogrp
                rotate_left 1
                · exfalso
                  have hno_raw : ¬ (wi + (1 : BitVec 64)).toNat <
                      (BitVec.setWidth 64 (s.core.wvec[(2 * f0.toNat + (1 : BitVec 64).toNat) %
                        2 ^ 64]'h2f1_idx)).toNat := by assumption
                  have hno : ¬ (wi + (1 : BitVec 64)).toNat < sz0.toNat := by
                    simpa only [bv64_setWidth_32, show ((1 : BitVec 64)).toNat = 1 from rfl,
                      Nat.mod_eq_of_lt (by omega : 2 * f0.toNat + 1 < 2 ^ 64), sz0] using hno_raw
                  exact hno hwi_next_lt
                dsimp only; simp only [hcr_val_raw]
                refine wp_join_state1 (t := i32) (α := BitVec 32) (fun r => r)
                  (fun r0n' mj => r0n'.toNat ≤ row0_max_n ∧ ∃ sbr' : List (BitVec 32),
                    let stw' : FullState :=
                      { s with scratch := { s.scratch with scratch_buf := sbr' } }
                    (FullMem c stw' ⋆ R) mj ∧ sbr'.length = c.scratch_cap ∧
                    ∀ qm < r0n'.toNat, ∃ res : List Nat,
                      (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
                      FidBvaRowEntryOk F_cur s f0.toNat (sbr'[4 * sc_n + qm]?.getD 0#32) res ∧
                      (cnfOfClauses F_cur).EntailsClause (cnfClause (f0.toNat :: res)))
                  (fun _ r0n' mj ⟨hr0n', sbr', hmj', hsbrl', hrow'⟩ => by
                    c0_hfast_nogrp
                    exact hJs1 (wi + 1#64 + 1#64, r0n', fticks + 1#64) mj
                      ⟨by rw [hwi2_n]; omega, hr0n', by rw [hwi2_n, hft1_n]; omega,
                       by rw [hwi2_n]; omega,
                       sbr', hmj', hsbrl',
                       by rw [hwi2_n, show off0.toNat + (wi.toNat + 2) = off0.toNat + wi.toNat + 2
                            by omega,
                          show sz0.toNat - (wi.toNat + 2) = sz0.toNat - wi.toNat - 2 by omega]
                          exact hslice_next,
                       hrow'⟩)
                  (fun Js2 hJs2 => ?_)
                c0_hfast_nogrp
                · have hcfl_z : (s.core.arena[cr.toNat]'(by omega) &&& 0x00480000#32) = 0#32 := by
                    have h1 :
                        (s.core.arena[cr.toNat]'(by omega) &&& ((524288 : BitVec 32) ||| 4194304)) =
                          (0 : BitVec 32) := by assumption
                    simpa only [
                      show ((524288 : BitVec 32) ||| 4194304) = 0x00480000#32 from by decide,
                      show (0 : BitVec 32) = 0#32 from rfl] using h1
                  have hcr2_mod : (cr.toNat + (2 : BitVec 64).toNat) % 2 ^ 64 = cr.toNat + 2 := by
                    rw [show (2 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
                  have hcsz3 : 3 ≤ (s.core.arena[cr.toNat + 2]'(by omega)).toNat := by
                    have h1 : (3 : BitVec 32).toNat ≤
                        (s.core.arena[(cr.toNat + (2 : BitVec 64).toNat) % 2 ^ 64]'(by
                          rw [hcr2_mod]; omega)).toNat := by assumption
                    simp only [hcr2_mod] at h1
                    exact Nat.le_trans (by decide) h1
                  have hcsz5 : (s.core.arena[cr.toNat + 2]'(by omega)).toNat ≤ 5 := by
                    have h1 :
                        (s.core.arena[(cr.toNat + (2 : BitVec 64).toNat) % 2 ^ 64]'(by
                          rw [hcr2_mod]; omega)).toNat ≤ (5 : BitVec 32).toNat := by assumption
                    simp only [hcr2_mod] at h1
                    exact Nat.le_trans h1 (by decide)
                  let csz := s.core.arena[cr.toNat + 2]'(by omega)
                  have hcsz_eq : csz.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
                    unfold fullArenaClauseSizeCore
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  have hcr_ng : fullArenaClauseGarbCore s.core cr.toNat = false := by
                    unfold fullArenaClauseGarbCore fullArenaHdrCore
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                    have hbit : (s.core.arena[cr.toNat]'(by omega) &&& 524288#32) = 0#32 := by
                      have hsub : (524288#32 : BitVec 32) = 0x00480000#32 &&& 524288#32 := by decide
                      rw [hsub, ← BitVec.and_assoc, hcfl_z, BitVec.zero_and]
                    simp [hbit]
                  have hcr_end_ar : cr.toNat + 3 + csz.toNat ≤ s.core.arena.length := by
                    rw [hcsz_eq]
                    exact Nat.le_trans hcr_wf.2.2.1 (Nat.le_trans hcr_wf.2.2.2.1 (by omega))
                  refine wp_join_state (α := BitVec 32 × Bool × Bool)
                    (fun ⟨j', hf0, sat⟩ => (j', hf0, sat, ()))
                    (fun ⟨_, hf0, sat⟩ mf => mf = mw ∧ (sat = false → hf0 = true →
                      f0.toNat ∈ fullArenaClauseLitsCore s.core cr.toNat))
                    (fun _ ⟨_, has_f0, sat⟩ mf ⟨hmf, hmem⟩ => ?_)
                    (fun Jj hJj => ?_)
                  · subst mf
                    let Js2Inv : BitVec 32 → Mem 64 → Prop := fun st m' =>
                      st.toNat ≤ row0_max_n ∧ ∃ sbr',
                        let stw' := { s with scratch := { s.scratch with scratch_buf := sbr' } }
                        (FullMem c stw' ⋆ R) m' ∧ sbr'.length = c.scratch_cap ∧
                          ∀ qm : Nat, qm < st.toNat → ∃ res,
                            (∀ x, x ∈ res → x < 2 * s.core.cur_vars) ∧
                            (List.map (fun x => x / 2) res).Nodup ∧
                            FidBvaRowEntryOk F_cur s f0.toNat
                              (sbr'[4 * sc_n + qm]?.getD 0#32) res ∧
                            (cnfOfClauses F_cur).EntailsClause (cnfClause (f0.toNat :: res))
                    refine wp_join_state1 (fun r : BitVec 32 => r) Js2Inv
                      (fun _ st m' h => by c0_hfast_nogrp; exact hJs2 st m' h)
                      (fun Js hJs => ?_)
                    c0_hfast_nogrp
                    · exact hJs r0n mw ⟨hr0n_le, sbr, hmw, hsbr_l, hrow⟩
                    · have hok_f0 : f0.toNat ∈ fullArenaClauseLitsCore s.core cr.toNat :=
                        hmem (by cases sat <;> first | contradiction | rfl)
                          (by cases has_f0 <;> first | contradiction | rfl)
                      obtain ⟨res, hres_lt, hres_nd, hok, hent⟩ :=
                        fidBvaRowEntryOk_of_large_f0 hinv hcr_ref hcr_ng
                          (by rw [← hcsz_eq]; exact hcsz3) (by rw [← hcsz_eq]; exact hcsz5)
                          hok_f0
                      refine hJs (r0n + 1#32) m ⟨by rw [hr0n1_n]; omega,
                        sbr.set (4 * sc_n + r0n.toNat) cr,
                        by dsimp only [sc_n]; rw [← h4sc_r0_n']; exact hm,
                        by simp [hsbr_l], fun qm hqm => ?_⟩
                      rw [hr0n1_n] at hqm
                      by_cases hqe : qm = r0n.toNat
                      · subst hqe
                        rw [List.getElem?_set_self (by omega), Option.getD_some]
                        exact ⟨res, hres_lt, hres_nd, hok, hent⟩
                      · rw [List.getElem?_set_ne (by omega)]
                        exact hrow qm (by omega)
                    · exact hJs r0n mw ⟨hr0n_le, sbr, hmw, hsbr_l, hrow⟩
                  · refine wp_loop_inv
                      (fun (j, hf0, ()) mj => mj = mw ∧ j.toNat ≤ csz.toNat ∧
                        (hf0 = true → f0.toNat ∈ fullArenaClauseLitsCore s.core cr.toNat))
                      (fun (j, _, ()) _ => csz.toNat - j.toNat)
                      (fun Jl hJl => hJl (0#32, false, ()) mw
                        ⟨rfl, Nat.zero_le _, Bool.noConfusion⟩)
                      (fun Jl (j, hf0, ()) mj ⟨hmj, hj_le, hmem⟩ ihj => ?_)
                    subst mj
                    c0_hsplit
                    · have hj_lt : j.toNat < csz.toNat := by
                        have h1 : j.toNat <
                            (s.core.arena[(BitVec.setWidth 64 cr +
                              (2 : BitVec 64)).toNat]'hcr2_ar).toNat
                            := by assumption
                        simpa only [hcr2_n_of] using h1
                      have hj1 : (j + 1#32).toNat = j.toNat + 1 :=
                        fid_bv32_add1_n (by omega)
                      have hcrj_n : (BitVec.setWidth 64 cr + 3#64 + BitVec.setWidth 64 j).toNat =
                          cr.toNat + 3 + j.toNat := fid_bv64_add3_n
                      have hcrj_ar :
                          (BitVec.setWidth 64 cr + 3#64 + BitVec.setWidth 64 j).toNat <
                            s.core.arena.length := by
                        rw [hcrj_n]; omega
                      have hl_mem : (s.core.arena[cr.toNat + 3 + j.toNat]'(by omega)).toNat ∈
                          fullArenaClauseLitsCore s.core cr.toNat :=
                        List.mem_of_getElem? (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem
                          (k := s.core) (r := cr.toNat) (j := j.toNat)
                          (by rw [← hcsz_eq]; exact hj_lt) (by omega))
                      have hl_lt : (s.core.arena[cr.toNat + 3 + j.toNat]'(by omega)).toNat <
                          2 * s.core.cur_vars :=
                        hinv.2.1.arena.lits_lt cr.toNat hcr_ref hcr_ng _ hl_mem
                      have hl_vals : (BitVec.setWidth 64
                          (s.core.arena[(BitVec.setWidth 64 cr + 3#64 +
                            BitVec.setWidth 64 j).toNat]'hcrj_ar)).toNat <
                          s.core.vals.length := by
                        simp only [bv64_setWidth_32, hcrj_n, hclen.vals_len]
                        exact Nat.lt_of_lt_of_le hl_lt (Nat.mul_le_mul_left 2 hcv_le)
                      c0_hfast_nogrp
                      · exact hJj (j, hf0, true) mw ⟨rfl, fun h _ => Bool.noConfusion h⟩
                      · refine wp_join_state1 (fun b : Bool => b)
                          (fun hf0' m' => m' = mw ∧
                            (hf0' = true → f0.toNat ∈ fullArenaClauseLitsCore s.core cr.toNat))
                          (fun _ hf0' m' ⟨hm', hmem'⟩ => by
                            subst m'
                            c0_hstep
                            exact ihj (j + 1#32, hf0', ()) mw
                              (by dsimp only; rw [hj1]
                                  exact Nat.sub_lt_sub_left hj_lt (Nat.lt_succ_self _))
                              ⟨rfl, by rw [hj1]; exact hj_lt, hmem'⟩)
                          (fun Jhf0 hJhf0 => ?_)
                        c0_hsplit
                        · c0_hstep
                          have hcrj_mod :
                              (cr.toNat + (3 : BitVec 64).toNat + j.toNat) % 2 ^ 64 =
                                cr.toNat + 3 + j.toNat := by
                            rw [show (3 : BitVec 64).toNat = 3 from rfl,
                              Nat.mod_eq_of_lt (by omega)]
                          have heq : s.core.arena[cr.toNat + 3 + j.toNat]'(by omega) = f0 := by
                            have h1 :
                                s.core.arena[(cr.toNat + (3 : BitVec 64).toNat +
                                  j.toNat) % 2 ^ 64]'(by rw [hcrj_mod]; omega) = f0 := by
                              assumption
                            simpa only [hcrj_mod] using h1
                          exact hJhf0 true mw ⟨rfl, fun _ => heq ▸ hl_mem⟩
                        · c0_hstep
                          exact hJhf0 hf0 mw ⟨rfl, hmem⟩
                    · exact hJj (j, hf0, false) mw ⟨rfl, fun _ hf => hmem hf⟩
                · exact hJs2 r0n mw ⟨hr0n_le, sbr, hmw, hsbr_l, hrow⟩
                · exact hJs2 r0n mw ⟨hr0n_le, sbr, hmw, hsbr_l, hrow⟩
                · exact hJs2 r0n mw ⟨hr0n_le, sbr, hmw, hsbr_l, hrow⟩
            · subst mf
              let stw : FullState := { s with scratch := { s.scratch with scratch_buf := sbr } }
              have hinvw : FullDenseInvW c F0 F_cur stw :=
                ⟨⟨hclen, { hslen with scratch_buf_len := hsbr_l }⟩,
                 { hinv.2.1 with
                   arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
                   watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
                 hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩
              c0_hfast_nogrp
              refine wp_join_state (α := BitVec 64) (fun x => (x, ()))
                (fun ant' mj => mj = mw)
                (fun _ ant' mj hmj => ?_)
                (fun Jant hJant => ?_)
              · subst hmj
                c0_hfast_nogrp
                let stwa : FullState :=
                  ⟨s.core, { s.scratch with scratch_buf := sbr, ant_sz := ant' }⟩
                have hinva : FullDenseInvW c F0 F_cur stwa :=
                  ⟨⟨hclen, { hslen with scratch_buf_len := hsbr_l }⟩,
                   { hinv.2.1 with
                     arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
                     watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
                   hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩
                c0_hsplit
                · c0_hfast_nogrp
                  exact hQ false stwa _ hinva.toDense (Nat.le_refl _)
                    (fun h => by contradiction) rfl rfl rfl (by assumption)
                · have hsc_pos' : 0 < sc_n := hsc_pos
                  have h4sc_cap' : 4 * sc_n ≤ c.scratch_cap := h4sc_cap
                  have hscap := c.hscr; unfold dimacsBound at hscap
                  let hdr_sz := BitVec.ofNat 32 sc_n <<< 2#32
                  have hhdr_sz_nat : hdr_sz.toNat = 4 * sc_n := by
                    dsimp only [hdr_sz]
                    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
                    have : sc_n * 4 < 2 ^ 32 := by omega
                    rw [Nat.mod_eq_of_lt this, Nat.mul_comm]
                  have h0_sb : (0 : BitVec 64).toNat < sbr.length := by
                    rw [hsbr_l, show (0 : BitVec 64).toNat = 0 from rfl]; omega
                  have hsc_nat_simp : (BitVec.setWidth 64 (BitVec.ofNat 32
                      (fidStepsCap c.scratch_cap))).toNat = sc_n := by
                    dsimp only [sc_n]
                    rw [fid_bv64_32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                  have hsc_sb : (BitVec.setWidth 64 (BitVec.ofNat 32
                      (fidStepsCap c.scratch_cap))).toNat < sbr.length := by
                    rw [hsc_nat_simp, hsbr_l]; omega
                  have h2sc_nat : (BitVec.setWidth 64 ((BitVec.ofNat 32 2) * BitVec.ofNat 32
                      (fidStepsCap c.scratch_cap))).toNat = 2 * sc_n := by
                    dsimp only [sc_n]; rw [fid_bv64_32]
                    have hsc_mod : (BitVec.ofNat 32 (fidStepsCap c.scratch_cap)).toNat =
                        fidStepsCap c.scratch_cap := by
                      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                    exact fid_bv32_mul_n hsc_mod (by omega) (by omega)
                  have h2sc_sb : (BitVec.setWidth 64 ((BitVec.ofNat 32 2) * BitVec.ofNat 32
                      (fidStepsCap c.scratch_cap))).toNat < sbr.length := by
                    rw [h2sc_nat, hsbr_l]; omega
                  have h3sc_nat : (BitVec.setWidth 64 ((BitVec.ofNat 32 3) * BitVec.ofNat 32
                      (fidStepsCap c.scratch_cap))).toNat = 3 * sc_n := by
                    dsimp only [sc_n]; rw [fid_bv64_32]
                    have hsc_mod : (BitVec.ofNat 32 (fidStepsCap c.scratch_cap)).toNat =
                        fidStepsCap c.scratch_cap := by
                      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                    exact fid_bv32_mul_n hsc_mod (by omega) (by omega)
                  have h3sc_sb : (BitVec.setWidth 64 ((BitVec.ofNat 32 3) * BitVec.ofNat 32
                      (fidStepsCap c.scratch_cap))).toNat < sbr.length := by
                    rw [h3sc_nat, hsbr_l]; omega
                  have hf0_lm : (BitVec.setWidth 64 f0).toNat < s.core.lit_mark.length := by
                    rw [fid_bv64_32, hclen.lit_mark_len]; omega
                  c0_hfast_nogrp_b
                  let sb1 := (((sbr.set 0 f0).set sc_n hdr_sz).set (2 * sc_n) r0n).set
                    (3 * sc_n) hdr_sz
                  let lm1 := s.core.lit_mark.set f0.toNat 1#8
                  let bump0 := hdr_sz + r0n
                  let st1 : FullState :=
                    ⟨{ s.core with lit_mark := lm1 },
                     { s.scratch with scratch_buf := sb1, ant_sz := ant' }⟩
                  have hsb1_l : sb1.length = c.scratch_cap := by dsimp only [sb1]; simp [hsbr_l]
                  have hlm1_l : lm1.length = 2 * c.max_vars := by
                    dsimp only [lm1]; simp [hclen.lit_mark_len]
                  have hr0n_ge2 : 2 ≤ r0n.toNat := by
                    have h1 : ¬ r0n.toNat < 2 := by assumption
                    omega
                  have hr0n_cap : 4 * sc_n + r0n.toNat ≤ c.scratch_cap := by
                    have := hr0n_le; dsimp [row0_max_n] at this; omega
                  have hhdr_eq : hdr_sz = BitVec.ofNat 32 (4 * sc_n) := by
                    apply BitVec.eq_of_toNat_eq
                    rw [hhdr_sz_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                  have hmat1_base : FidBvaMatrixInv c F_cur
                      { s with scratch := { s.scratch with scratch_buf := sb1 } } 1
                      (4 * sc_n + r0n.toNat) := by
                    simpa only [← hhdr_eq] using
                      fidBvaMatrixInv_step1 (sc := sc_n) rfl hsc_pos hsc_le hsbr_l hf0_lt
                        hr0n_ge2 hr0n_cap hrow
                  have hmat1 : FidBvaMatrixInv c F_cur st1 1 (4 * sc_n + r0n.toNat) :=
                    fidBvaMatrixInv_congr rfl rfl rfl rfl hmat1_base
                  have hf0_maxv : f0.toNat < 2 * c.max_vars :=
                    Nat.lt_of_lt_of_le hf0_lt (Nat.mul_le_mul_left 2 hcv_le)
                  have ⟨hlm1_hi, hlm1_set, hlm1_only⟩ :=
                    fid_bva_try_lit_lm1_init (f0 := f0) (qn := r0n) (hdr_sz := hdr_sz)
                      hsc_pos h4sc_cap hsbr_l hclen.lit_mark_len hf0_maxv hlm.2
                  have hlen1 : st1.LengthsOk c :=
                    ⟨{ hclen with lit_mark_len := hlm1_l },
                     { hslen with scratch_buf_len := hsb1_l }⟩
                  have hw1 : FullWitnessInv c F0 F_cur st1.core :=
                    { hw with
                      arena := { hw.arena with len_ok := hw.arena.len_ok }
                      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
                  have hnd1 : FullArenaVarsNodup st1 := hnd
                  have hext1 : FullExtScratchOk c st1 := hext
                  have hbump0_nat : bump0.toNat = 4 * sc_n + r0n.toNat := by
                    dsimp only [bump0]
                    rw [BitVec.toNat_add, hhdr_sz_nat]
                    have h1 : 4 * sc_n + r0n.toNat < 2 ^ 32 := by omega
                    rw [Nat.mod_eq_of_lt h1]
                  have hsb1_2sc : (st1.scratch.scratch_buf[2 * sc_n + (1 - 1)]?.getD 0#32).toNat =
                      r0n.toNat := by
                    dsimp only [st1, sb1]
                    rw [show 2 * sc_n + (1 - 1) = 2 * sc_n by omega]
                    rw [List.getElem?_set_ne (by omega),
                      List.getElem?_set_self
                        (by rw [List.length_set, List.length_set, hsbr_l]; omega),
                      Option.getD_some]
                  have hf0_nat_simp : (BitVec.setWidth 64 f0).toNat = f0.toNat := fid_bv64_32 f0
                  have hm1 : (FullMem c st1 ⋆ R) m := by
                    have hbv0 : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat = 0 := by
                      decide
                    have hbv8_1 : BitVec.ofNat (OfNat.ofNat 8) (OfNat.ofNat 1) = 1#8 := rfl
                    have hsc_bv : (BitVec.ofNat 32 (fidStepsCap c.scratch_cap)).toNat = sc_n := by
                      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                    have h2sc_bv :
                        (2 * BitVec.ofNat 32 (fidStepsCap c.scratch_cap)).toNat = 2 * sc_n := by
                      rw [BitVec.toNat_mul, show (2 : BitVec 32).toNat = 2 from rfl, hsc_bv,
                        Nat.mod_eq_of_lt (by omega)]
                    have h3sc_bv :
                        (3 * BitVec.ofNat 32 (fidStepsCap c.scratch_cap)).toNat = 3 * sc_n := by
                      rw [BitVec.toNat_mul, show (3 : BitVec 32).toNat = 3 from rfl, hsc_bv,
                        Nat.mod_eq_of_lt (by omega)]
                    have hshl_hdr :
                        (BitVec.ofNat 32 (fidStepsCap c.scratch_cap) <<< OfNat.ofNat 2) =
                          hdr_sz := by
                      apply BitVec.eq_of_toNat_eq
                      change (BitVec.ofNat 32 (fidStepsCap c.scratch_cap) <<< (2 : Nat)).toNat =
                        hdr_sz.toNat
                      rw [BitVec.toNat_shiftLeft, hsc_bv, hhdr_sz_nat, Nat.shiftLeft_eq,
                        Nat.mod_eq_of_lt (by omega)]
                      omega
                    dsimp only [st1, sb1, lm1]
                    simp only [hbv0, hbv8_1, hf0_nat_simp, fid_bv64_32,
                      hsc_bv, h2sc_bv, h3sc_bv, hshl_hdr] at hm
                    exact hm
                  refine wp_join_state
                    (α := BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 64)
                    (fun (a, b, c, d, e) => (a, b, c, d, e, ()))
                    (fun (bump, step, cur_qn, best_k, best_red) ml =>
                      ∃ stl, StepExitBody c F0 F_cur s R sc_n step best_k bump.toNat stl ml)
                    (fun _ (bump, step, cur_qn, best_k, best_red) ml
                        ⟨stl, hml, hlenl, hwl, hndl, hextl, hlv0l, hdml, hcvl, hfuell, harl,
                         hall, hmrkl, html, htrl, hst1, hst_sc, hbump_ge, hbump_le,
                         hmatl, hbkl, hlml_hi, hlml_set, hlml_only⟩ => ?_)
                    (fun Jexit hJexit => ?_)
                  rotate_left 1
                  · have hbump0_c :
                        (BitVec.ofNat 32 (fidStepsCap c.scratch_cap) <<< OfNat.ofNat 2 +
                          r0n, ()).fst.toNat = 4 * sc_n + r0n.toNat := hbump0_nat
                    refine fid_try_lit_step_loop_wp (bump0 := (BitVec.ofNat 32
                      (fidStepsCap c.scratch_cap) <<< OfNat.ofNat 2 + r0n, ()).fst)
                      (init_cv0 := init_cv0)
                      Γ hScan hPick hFilter hcv_le hf0_lt hinit_lits hsc_pos hsc_le
                      ⟨hm1, hlen1, hw1, hnd1, hext1, hlv0, hdm, rfl, rfl, rfl, rfl,
                       rfl, rfl, rfl, Nat.le_refl 1, hsc_pos,
                       by rw [hbump0_c]; omega, by rw [hbump0_c]; exact hr0n_cap,
                       by rw [show (1#32 : BitVec 32).toNat = 1 from rfl, hsb1_2sc],
                       by rw [hbump0_c]; exact hmat1,
                       Or.inl rfl, hlm1_hi, hlm1_set, hlm1_only⟩
                      Jexit (fun st ml h => hJexit st ml h)
                  · -- Exit of step loop:
                    exact fid_try_lit_exit_phase_wp (X := X) (f0 := f0) (init_cv0 := init_cv0)
                      (cur_qn := cur_qn) (best_red := best_red)
                      Γ hCommit hcv_le hlm
                      ⟨hml, hlenl, hwl, hndl, hextl, hlv0l, hdml, hcvl, hfuell, harl,
                       hall, hmrkl, html, htrl, hst1, hst_sc, hbump_ge, hbump_le,
                       hmatl, hbkl, hlml_hi, hlml_set, hlml_only⟩
                      hQ
              · c0_hfast
                · exact hJant _ _ rfl
                · exact hJant _ _ rfl
        · c0_hfast
          · exact hJicv _ m ⟨by simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega, rfl⟩
          · exact hJicv _ m ⟨by simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega, rfl⟩
theorem full_bva_try_lit_heap_wp (Γ : Env)
    (hSteps : ∀ a m Q X, fidBvaStepsCapSpec a m Q X →
      Γ "full_bva_steps_cap_fid" [i64] [i32] a m Q X)
    (hScan : ∀ a m Q X, fidBvaScanCandsSpec a m Q X →
      Γ "full_bva_scan_cands" [i64, i32, i32, i64] [i32] a m Q X)
    (hPick : ∀ a m Q X, FullBvaHeap.fullBvaPickCandSpec a m Q X →
      Γ "full_bva_pick_cand" [i64, i32, i32] [i32] a m Q X)
    (hFilter : ∀ a m Q X, fidBvaFilterRowSpec a m Q X →
      Γ "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32] a m Q X)
    (hCommit : ∀ a m Q X, fidBvaCommitSpec a m Q X →
      Γ "full_bva_commit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullBvaHeap.fullBvaTryLitHeapSpec a m Q X →
      Func.wp Γ full_bva_try_lit_body a m Q X :=
  fun a m Q X h => full_bva_try_lit_fid_wp Γ hSteps hScan hPick hFilter hCommit a m Q X
    (fidBvaTryLitSpec_weaken a m Q X h)

end LeanQbe.T.Examples.Kissat.FullFidelityBva
