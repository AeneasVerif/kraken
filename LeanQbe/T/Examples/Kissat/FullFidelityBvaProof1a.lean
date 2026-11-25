/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof0
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
# Kissat Fidelity BVA Proofs — Part 1a (`full_bva_scan_cands`)

M1-clean UNSAT-only specifications and parametric `Func.wp` proofs (`public section`,
zero meta-workarounds, `XPost`-polymorphic) for
`full_bva_scan_cands_fid_wp` certifying `fidBvaScanCandsSpec` for `full_bva_scan_cands_body`.
-/

set_option autoImplicit false

public section

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapTactics
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapScanHelpers
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.Full.FullBvaFwdHelpers
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open Kraken.Bedrock2.Test

namespace LeanQbe.T.Examples.Kissat.FullFidelityBva

open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open scoped FullArenaTactics FullBvaHeapTactics

@[local bv_c0] private theorem bv64_one_toNat : (1 : BitVec 64).toNat = 1 := rfl
@[local bv_c0] private theorem bv32_one_toNat : (1 : BitVec 32).toNat = 1 := rfl
@[local bv_c0] private theorem bv64_two_toNat : (2 : BitVec 64).toNat = 2 := rfl
@[local bv_c0] private theorem bv64_three_toNat : (3 : BitVec 64).toNat = 3 := rfl

namespace FidFast
open Lean Meta Elab Tactic LeanQbe.T.C0HeadStep

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
        catch _ => try
          setGoals [g']
          evalTactic (← `(tactic| first | omega | (simp only [bv_c0] at *; omega)))
          pure (← getUnsolvedGoals).isEmpty
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
    for nm in C0Step.c0MemLemmasForAddr env isLoad k addr do
      if tried.contains nm then continue
      tried := tried.insert nm
      if ← fidTryMemFast useBound g nm then return true
  for k in keys do
    for nm in C0Step.c0MemLemmas env isLoad k do
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
          evalTactic (← `(tactic| try simp only [LeanQbe.T.bv_c0_ult_true,
            LeanQbe.T.bv_c0_ult_false, LeanQbe.T.bv_c0_ule_true,
            LeanQbe.T.bv_c0_ule_false, LeanQbe.T.bv_c0_beq_true,
            LeanQbe.T.bv_c0_beq_false, LeanQbe.T.bv_c0_bne_true,
            LeanQbe.T.bv_c0_bne_false, LeanQbe.T.bv_c0_lt,
            LeanQbe.T.bv_c0_le, LeanQbe.T.bv_c0_zext32_64,
            LeanQbe.T.bv_c0_zext8_64, LeanQbe.T.bv_c0_zext16_64,
            FullArenaTactics.bv64_shl1_nat,
            bv64_one_toNat, bv32_one_toNat, bv64_two_toNat, bv64_three_toNat,
            BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat,
            decide_eq_true_eq, decide_eq_false_iff_not,
            Bool.not_eq_true, Bool.not_eq_false, beq_iff_eq, bne_iff_ne, ne_eq,
            beq_eq_false_iff_ne, bne_eq_false_iff_eq] at $hc:ident))
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

private meta def fidHSplitOnce : TacticM Unit := do
  focus do
    fidHeadSteps false { unrollGroup := false, splitJnz := false, pruneJnz := false } 2000
    let _ ← fidStepOnceFast false { unrollGroup := false, splitJnz := true, pruneJnz := false }

private meta def fidHStepOnce : TacticM Unit := do
  focus do
    let _ ← fidStepOnceFast false { unrollGroup := true, splitJnz := false, pruneJnz := false }

end FidFast

local elab "fid_hfast" : tactic => FidFast.fidHeadSteps false { pruneJnz := false } 10000
local elab "fid_hfast_split_nogrp" : tactic =>
  FidFast.fidHeadSteps false { unrollGroup := false, pruneJnz := false } 10000
local elab "fid_hfast_nogrp" : tactic =>
  FidFast.fidHeadSteps false { unrollGroup := false, splitJnz := false, pruneJnz := false } 10000
local elab "fid_hsplit" : tactic => FidFast.fidHSplitOnce
local elab "fid_hstep" : tactic => FidFast.fidHStepOnce

local macro "c0_hstep" : tactic => `(tactic| fid_hstep)
local macro "c0_hsplit" : tactic => `(tactic| fid_hsplit)
local macro "c0_hsplit_nogrp" : tactic => `(tactic| fid_hfast_split_nogrp)
local macro "c0_hsteps_nogrp" : tactic => `(tactic| fid_hfast_nogrp)
local macro "c0_hsteps" : tactic => `(tactic| fid_hfast)
local macro "c0_hfast" : tactic => `(tactic| fid_hfast)
local macro "c0_hfast_nogrp" : tactic => `(tactic| fid_hfast_nogrp)

local macro "fid_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. BitVec & Array Helper Lemmas -/

private theorem fid_bv32_garb_zero_of_and_02480000 {x : BitVec 32}
    (h : (x &&& 0x02480000#32) = 0#32) : (x &&& 0x00080000#32) = 0#32 := by
  have h1 := congrArg (· &&& 0x00080000#32) h
  rw [BitVec.and_assoc, show (0x02480000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl,
    BitVec.zero_and] at h1
  exact h1

private theorem fid_bv32_bvaq_zero_of_and_02480000 {x : BitVec 32}
    (h : (x &&& 0x02480000#32) = 0#32) : (x &&& 0x02000000#32) = 0#32 := by
  have h1 := congrArg (· &&& 0x02000000#32) h
  rw [BitVec.and_assoc, show (0x02480000#32 &&& 0x02000000#32) = 0x02000000#32 from rfl,
    BitVec.zero_and] at h1
  exact h1

private theorem fid_bv32_or_bvaq_garb (x : BitVec 32) :
    ((x ||| 0x02000000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) := by
  rw [BitVec.and_or_distrib_right,
    show (0x02000000#32 &&& 0x00080000#32) = 0#32 from rfl, BitVec.or_zero]

private theorem fid_bv32_or_bvaq_shrk (x : BitVec 32) :
    ((x ||| 0x02000000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  rw [BitVec.and_or_distrib_right,
    show (0x02000000#32 &&& 0x00800000#32) = 0#32 from rfl, BitVec.or_zero]

private theorem fid_bv32_bvaq_roundtrip {x : BitVec 32} (h : (x &&& 0x02000000#32) = 0#32) :
    ((x ||| 0x02000000#32) &&& ~~~0x02000000#32) = x := by
  rw [BitVec.and_or_distrib_right,
    show (0x02000000#32 &&& ~~~0x02000000#32) = 0#32 from rfl, BitVec.or_zero]
  have h1 : x = x &&& (~~~0x02000000#32 ||| 0x02000000#32) := by
    rw [show (~~~0x02000000#32 ||| 0x02000000#32) = BitVec.allOnes 32 from rfl, BitVec.and_allOnes]
  conv => rhs; rw [h1, BitVec.and_or_distrib_left, h, BitVec.or_zero]

private theorem fid_bv32_clear_bvaq_of_zero {x : BitVec 32} (hx : (x &&& 0x02000000#32) = 0#32) :
    (x &&& ~~~0x02000000#32) = x := by
  have h1 : x = x &&& (~~~0x02000000#32 ||| 0x02000000#32) := by
    rw [show (~~~0x02000000#32 ||| 0x02000000#32) = BitVec.allOnes 32 from rfl, BitVec.and_allOnes]
  conv => rhs; rw [h1, BitVec.and_or_distrib_left, hx, BitVec.or_zero]

private theorem fid_list_eq_of_getElem?_eq {α : Type} {l1 l2 : List α}
    (hlen : l1.length = l2.length) (hget : ∀ i < l1.length, l1[i]? = l2[i]?) : l1 = l2 := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < l1.length
  · exact hget i hi
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

private theorem fidArBvaq_congr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {ar : List (BitVec 32)}
    (hpt : ∀ i < c.arena_cap, ar[i]? = s.core.arena[i]? ∨ (i ∈ fullArenaClauseRefsCore s.core ∧
        ar[i]? = some (s.core.arena[i]?.getD 0#32 ||| 0x02000000#32))) :
    fullArenaClauseRefsCore { s.core with arena := ar } = fullArenaClauseRefsCore s.core ∧
    (∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore { s.core with arena := ar } r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseSizeCore { s.core with arena := ar } r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseLitsCore { s.core with arena := ar } r =
        fullArenaClauseLitsCore s.core r) := by
  have hal_le := hcl.arena_len_le
  have hgt_eq : ∀ r ∈ fullArenaClauseRefsCore s.core, ∀ i,
      r < i → i < fullArenaNextOff s.core.arena s.core.arena_len r →
      ar[i]? = s.core.arena[i]? := by
    intro r hr i hgt hlt
    have hwf := hw.arena.refs_wf r hr
    rcases hpt i (by omega) with heq | ⟨hi_ref, _⟩
    · exact heq
    · exfalso; have := fullArenaScanRefs_disjoint hr hi_ref hgt; omega
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core, fullArenaNextOff ar s.core.arena_len r =
      fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr
    have hwf := hw.arena.refs_wf r hr
    have h2eq : ar[r + 2]? = s.core.arena[r + 2]? := hgt_eq r hr (r + 2) (by omega) (by omega)
    rcases hpt r (by omega) with heq | ⟨_, hset_r⟩
    · exact fullArenaNextOff_congr_block heq h2eq fun i hi1 hi2 => hgt_eq r hr i (by omega) hi2
    · have h1 : ¬ (r + 3 > s.core.arena_len) := by omega
      have h2 : ¬ (r + 3 + (s.core.arena[r + 2]?.getD 0#32).toNat > s.core.arena_len) := by
        unfold fullArenaClauseSizeCore at hwf; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2, hset_r, Option.getD_some, fid_bv32_or_bvaq_shrk]
      split
      · rename_i hshrk
        have hnxt_eq : fullArenaNextOff s.core.arena s.core.arena_len r =
            fullArenaSkipShrk s.core.arena s.core.arena_len
              (r + 3 + (s.core.arena[r + 2]?.getD 0#32).toNat)
              (s.core.arena_len - (r + 3 + (s.core.arena[r + 2]?.getD 0#32).toNat)) := by
          unfold fullArenaNextOff; simp only [h1, ↓reduceIte, h2]; rw [ite_eq_left hshrk]
        exact fullArenaSkipShrk_congr fun i hi1 hi2 =>
          hgt_eq r hr i (by omega) (by rw [hnxt_eq]; exact hi2)
      · rfl
  refine ⟨fullArenaClauseRefsCore_congr rfl hnxt, fun r hr => ?_⟩
  have hwf := hw.arena.refs_wf r hr
  have h2eq : ar[r + 2]? = s.core.arena[r + 2]? := hgt_eq r hr (r + 2) (by omega) (by omega)
  have hsz : fullArenaClauseSizeCore { s.core with arena := ar } r =
      fullArenaClauseSizeCore s.core r := by unfold fullArenaClauseSizeCore; rw [h2eq]
  refine ⟨?_, hsz, ?_⟩
  · unfold fullArenaClauseGarbCore fullArenaHdrCore
    rcases hpt r (by omega) with heq | ⟨_, hset_r⟩
    · rw [heq]
    · rw [hset_r, Option.getD_some, fid_bv32_or_bvaq_garb]
  · exact fullArenaClauseLitsCore_congr hsz fun j hj =>
      hgt_eq r hr (r + 3 + j) (by omega) (by omega)

/-! ## 2. Scan Candidate Invariants -/

private def FidScanArBvaqInv (c : FullCfg) (s : FullState) (ar ql : List (BitVec 32))
    (lo hi : Nat) : Prop :=
  ar.length = c.arena_cap ∧ ql.length = 2 * c.max_vars ∧ hi ≤ c.max_vars ∧
  (∀ t, lo ≤ t → t < hi → (ql[t]?.getD 0#32).toNat ∈ fullArenaClauseRefsCore s.core ∧
    (s.core.arena[(ql[t]?.getD 0#32).toNat]?.getD 0#32 &&& 0x02000000#32) = 0#32) ∧
  (∀ idx < c.arena_cap, ar[idx]? = s.core.arena[idx]? ∨
    (∃ t, lo ≤ t ∧ t < hi ∧ (ql[t]?.getD 0#32).toNat = idx ∧
      (s.core.arena[idx]?.getD 0#32 &&& 0x02000000#32) = 0#32 ∧
      ar[idx]? = some (s.core.arena[idx]?.getD 0#32 ||| 0x02000000#32)))

private theorem fidScanArBvaqInv_init {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c) :
    FidScanArBvaqInv c s s.core.arena s.scratch.work_stk2 0 0 :=
  ⟨hlen.core_ok.arena_len_arr, hlen.scratch_ok.work_stk2_len, Nat.zero_le _,
   fun _ _ h => by omega, fun _ _ => Or.inl rfl⟩

private theorem fidScanArBvaqInv_set_ql_hi {c : FullCfg} {s : FullState} {ar ql : List (BitVec 32)}
    {nql : Nat} (h : FidScanArBvaqInv c s ar ql 0 nql) {idx : Nat} (hidx : c.max_vars ≤ idx)
    (v : BitVec 32) : FidScanArBvaqInv c s ar (ql.set idx v) 0 nql := by
  obtain ⟨har, hql, hhi, hdom, hall⟩ := h
  refine ⟨har, by simp [hql], hhi, fun t h0 ht => ?_, fun i hi => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hdom t h0 ht
  · rcases hall i hi with heq | ⟨t, h0, ht, hqt, h0v, hset⟩
    · exact Or.inl heq
    · exact Or.inr ⟨t, h0, ht, by rw [List.getElem?_set_ne (by omega)]; exact hqt, h0v, hset⟩

private theorem fidScanArBvaqInv_push {c : FullCfg} {s : FullState} {ar ql : List (BitVec 32)}
    {nql : Nat} (h : FidScanArBvaqInv c s ar ql 0 nql) {dr : BitVec 32}
    (hnql_lt : nql < c.max_vars) (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hdr_lt : dr.toNat < c.arena_cap)
    (hdr_nbvaq : (ar[dr.toNat]'(by rw [h.1]; exact hdr_lt) &&& 0x02000000#32) = 0#32) :
    (s.core.arena[dr.toNat]?.getD 0#32 &&& 0x02000000#32) = 0#32 ∧ FidScanArBvaqInv c s
      (ar.set dr.toNat ((ar[dr.toNat]'(by rw [h.1]; exact hdr_lt)) ||| 0x02000000#32))
      (ql.set nql dr) 0 (nql + 1) := by
  obtain ⟨har, hql, hhi, hdom, hall⟩ := h
  have horig : ar[dr.toNat]? = s.core.arena[dr.toNat]? := by
    rcases hall dr.toNat hdr_lt with heq | ⟨_, _, _, _, h0v, hset⟩
    · exact heq
    · rw [List.getElem?_eq_getElem (by omega)] at hset
      have hval := Option.some.inj hset
      have h1 : ((s.core.arena[dr.toNat]?.getD 0#32 ||| 0x02000000#32) &&& 0x02000000#32) =
          0x02000000#32 := by
        rw [BitVec.and_or_distrib_right,
          show (0x02000000#32 &&& 0x02000000#32) = 0x02000000#32 from rfl, h0v, BitVec.zero_or]
      rw [hval] at hdr_nbvaq; exact absurd (hdr_nbvaq.symm.trans h1) (by decide)
  have hs_nbvaq : (s.core.arena[dr.toNat]?.getD 0#32 &&& 0x02000000#32) = 0#32 := by
    rw [← horig, List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hdr_nbvaq
  refine ⟨hs_nbvaq, by simp [har], by simp [hql], by omega, fun t h0 ht => ?_, fun i hi => ?_⟩
  · by_cases htn : t = nql
    · subst htn; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact ⟨hdr_ref, hs_nbvaq⟩
    · rw [List.getElem?_set_ne (Ne.symm htn)]; exact hdom t h0 (by omega)
  · by_cases hid : i = dr.toNat
    · subst hid
      refine Or.inr ⟨nql, Nat.zero_le _, by omega,
        by rw [List.getElem?_set_self (by omega), Option.getD_some], hs_nbvaq, ?_⟩
      rw [List.getElem?_set_self (by omega)]
      have har_eq : ar[dr.toNat]'(by omega) = s.core.arena[dr.toNat]?.getD 0#32 := by
        rw [← horig, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [har_eq]
    · rw [List.getElem?_set_ne (Ne.symm hid)]
      rcases hall i hi with heq | ⟨t, h0, ht, hqt, h0v, hset⟩
      · exact Or.inl heq
      · exact Or.inr ⟨t, h0, by omega,
          by rw [List.getElem?_set_ne (by omega)]; exact hqt, h0v, hset⟩

private theorem fidScanArBvaqInv_clear_step {c : FullCfg} {s : FullState}
    {ar ql : List (BitVec 32)} {ci nql : Nat} (_hs_ar : s.core.arena.length = c.arena_cap)
    (h : FidScanArBvaqInv c s ar ql ci nql) (hci : ci < nql)
    (hidx_lt : (ql[ci]'(by rw [h.2.1]; have := h.2.2.1; omega)).toNat < c.arena_cap) :
    let idx := (ql[ci]'(by rw [h.2.1]; have := h.2.2.1; omega)).toNat
    FidScanArBvaqInv c s
      (ar.set idx ((ar[idx]'(by rw [h.1]; exact hidx_lt)) &&& ~~~0x02000000#32))
      ql (ci + 1) nql := by
  obtain ⟨har, hql, hhi, hdom, hall⟩ := h
  intro idx
  have hidx_eq : (ql[ci]?.getD 0#32).toNat = idx := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hidx_s0 : (s.core.arena[idx]?.getD 0#32 &&& 0x02000000#32) = 0#32 := by
    have := (hdom ci (Nat.le_refl _) hci).2; rwa [hidx_eq] at this
  have har_idx_clr :
      ((ar[idx]'(by omega)) &&& ~~~0x02000000#32) = s.core.arena[idx]?.getD 0#32 := by
    rcases hall idx hidx_lt with heq | ⟨_, _, _, _, _, hset⟩
    · have : ar[idx]'(by omega) = s.core.arena[idx]?.getD 0#32 := by
        rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [this]; exact fid_bv32_clear_bvaq_of_zero hidx_s0
    · rw [List.getElem?_eq_getElem (by omega)] at hset
      rw [Option.some.inj hset]; exact fid_bv32_bvaq_roundtrip hidx_s0
  refine ⟨by simp [har], hql, hhi, fun t ht1 ht2 => hdom t (by omega) ht2, fun i hi => ?_⟩
  by_cases hid : i = idx
  · subst hid; left
    rw [List.getElem?_set_self (by omega), har_idx_clr,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  · rw [List.getElem?_set_ne (Ne.symm hid)]
    rcases hall i hi with heq | ⟨t, ht1, ht2, hqt, h0v, hset⟩
    · exact Or.inl heq
    · have htne : t ≠ ci := fun h => by subst h; rw [hidx_eq] at hqt; exact hid hqt.symm
      exact Or.inr ⟨t, by omega, ht2, hqt, h0v, hset⟩

private theorem fidScanArBvaqInv_done {c : FullCfg} {s : FullState} {ar ql : List (BitVec 32)}
    {nql : Nat} (hs_ar : s.core.arena.length = c.arena_cap)
    (h : FidScanArBvaqInv c s ar ql nql nql) : ar = s.core.arena := by
  have har_l := h.1
  apply fid_list_eq_of_getElem?_eq (by rw [har_l, hs_ar])
  intro i hi
  rcases h.2.2.2.2 i (by omega) with heq | ⟨t, ht1, ht2, _⟩
  · exact heq
  · omega

private def FidLmBit4Inv (c : FullCfg) (lm1 : List (BitVec 8)) (ql : List (BitVec 32))
    (lo hi : Nat) (lm : List (BitVec 8)) : Prop :=
  lm.length = 2 * c.max_vars ∧ hi ≤ c.max_vars ∧
  (∀ t, lo ≤ t → t < hi → (ql[c.max_vars + t]?.getD 0#32).toNat < 2 * c.max_vars) ∧
  ∀ l < 2 * c.max_vars, lm[l]? = lm1[l]? ∨
    (∃ t, lo ≤ t ∧ t < hi ∧ (ql[c.max_vars + t]?.getD 0#32).toNat = l ∧
      lm[l]? = some (lm1[l]?.getD 0#8 ||| 4#8))

private theorem fidLmBit4Inv_init {c : FullCfg} {lm1 : List (BitVec 8)} {ql : List (BitVec 32)}
    (hlm1 : lm1.length = 2 * c.max_vars) : FidLmBit4Inv c lm1 ql 0 0 lm1 :=
  ⟨hlm1, Nat.zero_le _, fun _ _ h => by omega, fun _ _ => Or.inl rfl⟩

private theorem fidLmBit4Inv_set_ql_lo {c : FullCfg} {lm1 lm : List (BitVec 8)}
    {ql : List (BitVec 32)} {hi idx : Nat} (h : FidLmBit4Inv c lm1 ql 0 hi lm)
    (hidx : idx < c.max_vars) (v : BitVec 32) : FidLmBit4Inv c lm1 (ql.set idx v) 0 hi lm := by
  obtain ⟨hlm, hhi, hdom, hall⟩ := h
  refine ⟨hlm, hhi, fun t h0 ht => ?_, fun l hl => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hdom t h0 ht
  · rcases hall l hl with heq | ⟨t, h0, ht, hqt, hset⟩
    · exact Or.inl heq
    · exact Or.inr ⟨t, h0, ht, by rw [List.getElem?_set_ne (by omega)]; exact hqt, hset⟩

private theorem fidLmBit4Inv_push {c : FullCfg} {lm1 lm : List (BitVec 8)} {ql : List (BitVec 32)}
    {nnou : Nat} (hql : ql.length = 2 * c.max_vars) (h : FidLmBit4Inv c lm1 ql 0 nnou lm)
    {cand : BitVec 32} (hnn : nnou < c.max_vars) (hc_lt : cand.toNat < 2 * c.max_vars) :
    FidLmBit4Inv c lm1 (ql.set (c.max_vars + nnou) cand) 0 (nnou + 1)
      (lm.set cand.toNat ((lm[cand.toNat]'(by rw [h.1]; exact hc_lt)) ||| 4#8)) := by
  obtain ⟨hlm, hhi, hdom, hall⟩ := h
  refine ⟨by simp [hlm], by omega, fun t h0 ht => ?_, fun l hl => ?_⟩
  · by_cases htn : t = nnou
    · subst htn; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hc_lt
    · rw [List.getElem?_set_ne (by omega)]; exact hdom t h0 (by omega)
  · by_cases hlc : l = cand.toNat
    · subst hlc
      refine Or.inr ⟨nnou, Nat.zero_le _, by omega,
        by rw [List.getElem?_set_self (by omega), Option.getD_some], ?_⟩
      rw [List.getElem?_set_self (by omega)]
      rcases hall cand.toNat hc_lt with heq | ⟨_, _, _, _, hset⟩
      · have : lm[cand.toNat]'(by omega) = lm1[cand.toNat]?.getD 0#8 := by
          rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [this]
      · rw [List.getElem?_eq_getElem (by omega)] at hset
        rw [Option.some.inj hset, bv8_or4_idem]
    · rw [List.getElem?_set_ne (Ne.symm hlc)]
      rcases hall l hl with heq | ⟨t, h0, ht, hqt, hset⟩
      · exact Or.inl heq
      · exact Or.inr ⟨t, h0, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hqt, hset⟩

private theorem fidLmBit4Inv_clear_step {c : FullCfg} {lm1 lm : List (BitVec 8)}
    {ql : List (BitVec 32)} {j nnou : Nat} (hlm1 : lm1.length = 2 * c.max_vars)
    (_hql : ql.length = 2 * c.max_vars)
    (hlm1_b2 : ∀ l < 2 * c.max_vars, (lm1[l]?.getD 0#8 &&& 4#8) = 0#8)
    (h : FidLmBit4Inv c lm1 ql j nnou lm) (hj : j < nnou) :
    let cl := (ql[c.max_vars + j]'(by have := h.2.1; omega)).toNat
    cl < 2 * c.max_vars ∧ FidLmBit4Inv c lm1 ql (j + 1) nnou
      (lm.set cl ((lm[cl]'(by
        have hdom := h.2.2.1 j (Nat.le_refl _) hj
        rw [List.getElem?_eq_getElem (by have := h.2.1; omega), Option.getD_some] at hdom
        rw [h.1]; exact hdom)) &&& 0xFB#8)) := by
  obtain ⟨hlm, hhi, hdom, hall⟩ := h
  intro cl
  have hcl_eq : (ql[c.max_vars + j]?.getD 0#32).toNat = cl := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hcl_lt : cl < 2 * c.max_vars := by have := hdom j (Nat.le_refl _) hj; rwa [hcl_eq] at this
  have hclr : ((lm[cl]'(by omega)) &&& 0xFB#8) = lm1[cl]?.getD 0#8 := by
    apply bv8_clear_bit2_eq_of_or4 (hlm1_b2 cl hcl_lt)
    rcases hall cl hcl_lt with heq | ⟨_, _, _, _, hset⟩
    · left; rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]
    · right; rw [List.getElem?_eq_getElem (by omega)] at hset; exact Option.some.inj hset
  refine ⟨hcl_lt, by simp [hlm], hhi, fun t ht1 ht2 => hdom t (by omega) ht2, fun i hi => ?_⟩
  by_cases hic : i = cl
  · subst hic; left
    rw [List.getElem?_set_self (by omega), hclr,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  · rw [List.getElem?_set_ne (Ne.symm hic)]
    rcases hall i hi with heq | ⟨t, ht1, ht2, hqt, hset⟩
    · exact Or.inl heq
    · have htne : t ≠ j := fun h => by subst h; rw [hcl_eq] at hqt; exact hic hqt.symm
      exact Or.inr ⟨t, by omega, ht2, hqt, hset⟩

private theorem fidLmBit4Inv_done {c : FullCfg} {lm1 lm : List (BitVec 8)} {ql : List (BitVec 32)}
    {nnou : Nat} (hlm1 : lm1.length = 2 * c.max_vars)
    (h : FidLmBit4Inv c lm1 ql nnou nnou lm) : lm = lm1 := by
  have hlm_l := h.1
  apply fid_list_eq_of_getElem?_eq (by rw [hlm_l, hlm1])
  intro i hi
  rcases h.2.2.2 i (by omega) with heq | ⟨t, ht1, ht2, _⟩
  · exact heq
  · omega

private theorem fid_scan_cands_ar_lits_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {ar ql : List (BitVec 32)} {nql : Nat}
    (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hbvaq : FidScanArBvaqInv c s ar ql 0 nql) {r : Nat} (hr : r ∈ fullArenaClauseRefsCore s.core) :
    ar[r + 2]? = s.core.arena[r + 2]? ∧
    (∀ j < fullArenaClauseSizeCore s.core r, ar[r + 3 + j]? = s.core.arena[r + 3 + j]?) := by
  have hwf := hw.arena.refs_wf r hr; have hal := hcl.arena_len_le
  constructor
  · rcases hbvaq.2.2.2.2 (r + 2) (by omega) with heq | ⟨t, _, ht, hqt, _, _⟩
    · exact heq
    · exfalso
      have ht_ref := (hbvaq.2.2.2.1 t (Nat.zero_le _) ht).1; rw [hqt] at ht_ref
      rcases Nat.lt_or_gt_of_ne (by omega : r ≠ r + 2) with hlt | hgt
      · have := fullArenaScanRefs_disjoint hr ht_ref hlt; omega
      · omega
  · intro j hj
    rcases hbvaq.2.2.2.2 (r + 3 + j) (by omega) with heq | ⟨t, _, ht, hqt, _, _⟩
    · exact heq
    · exfalso
      have ht_ref := (hbvaq.2.2.2.1 t (Nat.zero_le _) ht).1; rw [hqt] at ht_ref
      have := fullArenaScanRefs_disjoint hr ht_ref (by omega); omega

private theorem fid_scan_cands_dr_info {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {arp qlp : List (BitVec 32)} {nqlp : Nat} {dr csz_bv : BitVec 32}
    (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hbvaqp : FidScanArBvaqInv c s arp qlp 0 nqlp)
    (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hdr_lt : dr.toNat + 3 ≤ arp.length)
    (hdr_0248 : (arp[dr.toNat]'(by omega) &&& 0x02480000#32) = 0#32)
    (hdr_sz_ar : arp[dr.toNat + 2]'(by omega) = csz_bv) :
    (arp[dr.toNat]'(by omega) &&& 0x02000000#32) = 0#32 ∧
    fullArenaClauseGarbCore s.core dr.toNat = false ∧
    fullArenaClauseSizeCore s.core dr.toNat = csz_bv.toNat := by
  have harp_l := hbvaqp.1
  have hdr_nbvaq := fid_bv32_bvaq_zero_of_and_02480000 hdr_0248
  have hdr_ng_ar := fid_bv32_garb_zero_of_and_02480000 hdr_0248
  refine ⟨hdr_nbvaq, ?_, ?_⟩
  · unfold fullArenaClauseGarbCore fullArenaHdrCore
    rcases hbvaqp.2.2.2.2 dr.toNat (by omega) with heq | ⟨_, _, _, _, _, hset'⟩
    · rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]; simp [hdr_ng_ar]
    · rw [List.getElem?_eq_getElem (by omega)] at hset'
      rw [Option.some.inj hset', fid_bv32_or_bvaq_garb] at hdr_ng_ar; simp [hdr_ng_ar]
  · have h2 := (fid_scan_cands_ar_lits_eq hcl hw hbvaqp hdr_ref).1
    unfold fullArenaClauseSizeCore
    rw [← h2, List.getElem?_eq_getElem (by omega), Option.getD_some, hdr_sz_ar]

private theorem fid_scan_cands_stepB_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {arp qlA : List (BitVec 32)} {lm1 lmA : List (BitVec 8)}
    {nqlp nn1 : Nat} {dr : BitVec 32}
    (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hwp : FullWitnessInv c F0 F_cur { s.core with arena := arp }) (hl0 : s.core.cur_level = 0)
    (hbvaqA : FidScanArBvaqInv c s arp qlA 0 nqlp) (hlm4A : FidLmBit4Inv c lm1 qlA 0 nn1 lmA)
    (hnq_lt : nqlp < c.max_vars) (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hdr_lt : dr.toNat < c.arena_cap)
    (hdr_nbvaq : (arp[dr.toNat]'(by rw [hbvaqA.1]; exact hdr_lt) &&& 0x02000000#32) = 0#32) :
    let ar1 := arp.set dr.toNat ((arp[dr.toNat]'(by rw [hbvaqA.1]; exact hdr_lt)) ||| 0x02000000#32)
    FidScanArBvaqInv c s ar1 (qlA.set nqlp dr) 0 (nqlp + 1) ∧
    FidLmBit4Inv c lm1 (qlA.set nqlp dr) 0 nn1 lmA ∧
    FullWitnessInv c F0 F_cur { s.core with arena := ar1 } := by
  have harp_l := hbvaqA.1
  have hcl_ar : ({ s.core with arena := arp }).LengthsOk c := { hcl with arena_len_arr := harp_l }
  have ⟨_, hbvaq_next⟩ := fidScanArBvaqInv_push hbvaqA hnq_lt hdr_ref hdr_lt hdr_nbvaq
  have hlm4_next := fidLmBit4Inv_set_ql_lo hlm4A hnq_lt dr
  have hwp_refs : dr.toNat ∈ fullArenaClauseRefsCore { s.core with arena := arp } := by
    have h1 := (fidArBvaq_congr hcl hw fun i hi => by
      rcases hbvaqA.2.2.2.2 i hi with heq | ⟨t, h0, ht, hqt, _, hset'⟩
      · exact Or.inl heq
      · have ht_ref := (hbvaqA.2.2.2.1 t h0 ht).1; rw [hqt] at ht_ref
        exact Or.inr ⟨ht_ref, hset'⟩).1
    rw [h1]; exact hdr_ref
  have ⟨_, _, hw_next, _⟩ := fullWitnessInv_set_hdr_bit20 hcl_ar hwp hl0 hwp_refs
    ((arp[dr.toNat]'(by omega)) ||| 0x02000000#32)
    (by unfold fullArenaHdrCore; dsimp only
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact fid_bv32_or_bvaq_garb _)
    (by unfold fullArenaHdrCore; dsimp only
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact fid_bv32_or_bvaq_shrk _)
  exact ⟨hbvaq_next, hlm4_next, hw_next⟩

private theorem fid_scan_cands_lmj_lift {c : FullCfg} {ar : List (BitVec 32)}
    {lm0 lmj : List (BitVec 8)} {qw j csz : Nat}
    (h : LmBit2Inv c ar lm0 qw 0 j lmj) (_hj : j ≤ csz) :
    LmBit2Inv c ar lm0 qw 0 csz lmj :=
  ⟨h.1, fun l hl => by
    rcases h.2 l hl with heq | ⟨k, h0, hk, har', hset'⟩
    · exact Or.inl heq
    · exact Or.inr ⟨k, h0, by omega, har', hset'⟩⟩

private def sDummyVal : (t : Ty) → Val t
  | .bits _ => 0 | .bool => true | .float _ => 0 | .pair a b => (sDummyVal a, sDummyVal b)
private def sDummyTup : (ts : List Ty) → Tup Val ts
  | [] => () | t :: ts => (sDummyVal t, sDummyTup ts)

private def sStep {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := ts) _ k => k (sDummyTup ts)
  | .load t _ k => k (sDummyVal t)
  | .store _ _ k => k
  | .call (bs := bs) _ _ k => k (sDummyTup bs)
  | _ => .hlt
private def sSteps {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e | n + 1, e => sSteps n (sStep e)
private def sStepZ {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (Op.mk (.zext _ m) (a, ())) k => k (BitVec.setWidth m a.val, ())
  | .let_ (Op.mk (.add (.bits 64)) (a, b, ())) k => k (a.val + b.val, ())
  | e => sStep e
private def sStepsZ {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e | n + 1, e => sStepsZ n (sStepZ e)
private def sLd64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 64) _ k => k v | _ => .hlt
private def sLd32 {rs : List Ty} (v : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 32) _ k => k v | _ => .hlt
private def sCall64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .call (bs := [.bits 64]) _ _ k => k (v, ()) | _ => .hlt
private def sThen {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ t _ => t | _ => .hlt
private def sElse {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ _ e => e | _ => .hlt
private def sGrpK4q {rs : List Ty} (J : Cont [.bits 32, .bits 32, .bits 32, .bits 64]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 32, .bits 64]]) _ k => k (J, ()) | _ => .hlt
private def sGrpB4q {rs : List Ty} (v : Tup Val [.bits 32, .bits 32, .bits 32, .bits 64])
    (J : Cont [.bits 32, .bits 32, .bits 32, .bits 64]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 32, .bits 64]]) bs _ =>
    match bs (J, ()) with | .cons f .nil => f v
  | _ => .hlt
private def sGrpK3s {rs : List Ty} (J : Cont [.bits 32, .bits 32, .bits 64]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 64]]) _ k => k (J, ()) | _ => .hlt
private def sGrpB4m {rs : List Ty} (v : Tup Val [.bits 32, .bits 32, .bits 32, .bits 32])
    (J : Cont [.bits 32, .bits 32, .bits 32, .bits 32]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 32, .bits 32]]) bs _ =>
    match bs (J, ()) with | .cons f .nil => f v
  | _ => .hlt
private def sGrpK4c {rs : List Ty} (J : Cont [.bits 32, .bits 32, .bits 64, .bits 32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 64, .bits 32]]) _ k => k (J, ()) | _ => .hlt
private def sGrpK5mp {rs : List Ty} (J : Cont [.bits 32, .bits 32, .bits 64, .bits 64, .bits 32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 64, .bits 64, .bits 32]]) _ k => k (J, ())
  | _ => .hlt

private def fidScanHdr (row_off cur_qn : Val i32) (h64 init_lits : Val i64)
    (pVals pWv pWs pAr pLm pScr pCnt pCntd pFl pQl pDeg r_clines : Val i64)
    (J Jq : Cont [i32, i32, i32, i64])
    (nql ncntd qi : Val i32) (ticks : Val i64) (qw : Val i32)
    (Js : Cont [i32, i32, i64]) : Expr Val Cont [i32] :=
  full_bva_scan_cands_body Val Cont (h64, row_off, cur_qn, init_lits, ())
    |> sStep |> sLd64 pVals |> sStep |> sLd64 pWv |> sStep |> sLd64 pWs
    |> sStep |> sLd64 pAr |> sStep |> sLd64 pLm |> sStep |> sLd64 pScr
    |> sStep |> sLd64 pCnt |> sStep |> sLd64 pCntd |> sStep |> sLd64 pFl
    |> sStep |> sLd64 pQl |> sStep |> sLd64 pDeg |> sStep |> sCall64 r_clines
    |> sStep |> sGrpK4q J |> sGrpB4q (nql, ncntd, qi, ticks, ()) Jq
    |> sStep |> sThen |> sSteps 4 |> sLd32 qw |> sGrpK3s Js

private def fidScanBin (row_off cur_qn : Val i32) (h64 init_lits : Val i64)
    (pVals pWv pWs pAr pLm pScr pCnt pCntd pFl pQl pDeg r_clines : Val i64)
    (J Jq : Cont [i32, i32, i32, i64]) (nql ncntd qi : Val i32) (ticks : Val i64)
    (qw : Val i32) (Js : Cont [i32, i32, i64]) : Expr Val Cont [i32] :=
  fidScanHdr row_off cur_qn h64 init_lits pVals pWv pWs pAr pLm pScr pCnt pCntd pFl pQl pDeg
    r_clines J Jq nql ncntd qi ticks qw Js |> sSteps 2 |> sThen

private def fidScanLarge (row_off cur_qn : Val i32) (h64 init_lits : Val i64)
    (pVals pWv pWs pAr pLm pScr pCnt pCntd pFl pQl pDeg r_clines : Val i64)
    (J Jq : Cont [i32, i32, i32, i64]) (nql ncntd qi : Val i32) (ticks : Val i64)
    (qw : Val i32) (Js : Cont [i32, i32, i64]) : Expr Val Cont [i32] :=
  fidScanHdr row_off cur_qn h64 init_lits pVals pWv pWs pAr pLm pScr pCnt pCntd pFl pQl pDeg
    r_clines J Jq nql ncntd qi ticks qw Js |> sStepsZ 2 |> sElse

private def fidScanMp (row_off cur_qn : Val i32) (h64 init_lits : Val i64)
    (pVals pWv pWs pAr pLm pScr pCnt pCntd pFl pQl pDeg r_clines : Val i64)
    (J Jq : Cont [i32, i32, i32, i64]) (nql ncntd qi : Val i32) (ticks : Val i64)
    (qw : Val i32) (Js : Cont [i32, i32, i64]) (csz : Val i32) (Jm : Cont [i32, i32, i32, i32])
    (min_l min_d fc jf : Val i32) (Jc_join : Cont [i32, i32, i64, i32])
    (moff msz : Val i32) (mxv r_clines_min : Val i64)
    (Jmp : Cont [i32, i32, i64, i64, i32]) : Expr Val Cont [i32] :=
  fidScanLarge row_off cur_qn h64 init_lits pVals pWv pWs pAr pLm pScr pCnt pCntd pFl pQl pDeg
    r_clines J Jq nql ncntd qi ticks qw Js
    |> sStepsZ 4 |> sLd32 csz |> sStepZ
    |> sGrpB4m (min_l, min_d, fc, jf, ()) Jm
    |> sGrpK4c Jc_join |> sStepZ |> sThen |> sStepZ |> sThen
    |> sStepsZ 5 |> sLd32 moff |> sStepsZ 7 |> sLd32 msz |> sStepsZ 3
    |> sLd64 mxv |> sStepsZ 2 |> sCall64 r_clines_min |> sStepZ
    |> sGrpK5mp Jmp

private theorem fid_scan_cands_bin_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    (hClines : ∀ a m Q X, fidBvaClinesSpec a m Q X → Γ "full_bva_clines_fid" [i64] [i64] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {row_off cur_qn : Val i32} {init_lits : Val i64} {J Jq : Cont [i32, i32, i32, i64]}
    {nql ncntd qi : Val i32} {ticks r_clines : Val i64} {qw : Val i32}
    {Js : Cont [i32, i32, i64]} {ar ws ws1 ws2 : List (BitVec 32)} {ant : BitVec 64} {ml : Mem 64}
    (hslen : s.LengthsOk c) (_hw : FullWitnessInv c F0 F_cur s.core)
    (hdw : DenseWatchesInv F_cur s.core) (hil_le : init_lits.toNat ≤ 2 * s.core.cur_vars)
    (hws_l : ws.length = 2 * c.max_vars) (hws1_l : ws1.length = 2 * c.max_vars)
    (_hws2_l : ws2.length = 2 * c.max_vars) (_har_l : ar.length = c.arena_cap)
    (hnc_le : ncntd.toNat ≤ init_lits.toNat)
    (hcntd_ok : ∀ i < ncntd.toNat, (ws1[i]?.getD 0#32).toNat < init_lits.toNat)
    (hq_lt : (qw &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars)
    (hml : (FullMem c
      { core := { s.core with arena := ar },
        scratch :=
          { s.scratch with wsort := ws, work_stk1 := ws1, work_stk2 := ws2, ant_sz := ant } } ⋆
      R) ml)
    (hExit : ∀ (nc' : BitVec 32) (ticks' : BitVec 64) wsp ws1p mlp,
      nc'.toNat ≤ init_lits.toNat → wsp.length = 2 * c.max_vars → ws1p.length = 2 * c.max_vars →
      (∀ i < nc'.toNat, (ws1p[i]?.getD 0#32).toNat < init_lits.toNat) →
      (FullMem c
        { core := { s.core with arena := ar },
          scratch :=
            { s.scratch with
              wsort := wsp, work_stk1 := ws1p, work_stk2 := ws2, ant_sz := ant } } ⋆ R) mlp →
      Js (nql, nc', ticks', ()) mlp) :
    wp Γ Q X (fidScanBin row_off cur_qn c.hdr init_lits c.pVals c.pWvec c.pWstk c.pArena
      c.pLitMark c.pScratchBuf c.pWsort c.pWorkStk1 c.pFlags c.pWorkStk2 c.pRepr r_clines
      J Jq nql ncntd qi ticks qw Js) ml := by
  have hmx := c.hmaxv; have har_b := c.harena; unfold dimacsBound at hmx har_b
  have hcl := hslen.core_ok; have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len
  have hws_len := hcl.wstk_len_arr; have hwlen_le := hcl.wlen_le
  have hlm_len := hcl.lit_mark_len; have hvals_len := hcl.vals_len
  have hfl_len := hcl.flags_len; have hrepr_len := hcl.repr_len
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  let q := qw &&& 0x7FFFFFFF#32
  have hq_lt' : q.toNat < 2 * s.core.cur_vars := hq_lt
  have h2q_n : (BitVec.setWidth 64 q <<< (1 : Nat)).toNat = 2 * q.toNat := by c0_bound
  have h2q1_n : ((BitVec.setWidth 64 q <<< (1 : Nat)) + 1).toNat = 2 * q.toNat + 1 := by
    change ((BitVec.setWidth 64 q <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
  have hq_bd := hdw.layout.bounds q.toNat hq_lt; have hq_sl := hdw.slices q.toNat hq_lt
  have hoff_eq : (s.core.wvec[2 * q.toNat]'(by omega)).toNat = fullWatchOffCore s.core q.toNat := by
    unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hsz_eq : (s.core.wvec[2 * q.toNat + 1]'(by omega)).toNat =
      fullWatchSizeCore s.core q.toNat := by
    unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  let qoff0 := fullWatchOffCore s.core q.toNat
  let qsz0 := fullWatchSizeCore s.core q.toNat
  have h2147 : (2147483647 : BitVec 32) = 0x7FFFFFFF#32 := rfl
  have hq_ast : qw &&& (2147483647 : BitVec 32) = q := by rw [h2147]
  have h2q_wv : (BitVec.setWidth 64 (qw &&& (2147483647 : BitVec 32)) <<< (1 : Nat)).toNat <
      s.core.wvec.length := by rw [hq_ast, h2q_n]; omega
  have h2q1_wv : ((BitVec.setWidth 64 (qw &&& (2147483647 : BitVec 32)) <<< (1 : Nat)) +
      1).toNat < s.core.wvec.length := by rw [hq_ast, h2q1_n]; omega
  have hq_repr : (BitVec.setWidth 64 (qw &&& (2147483647 : BitVec 32))).toNat <
      s.core.repr.length := by rw [hq_ast, bv64_setWidth_32, hrepr_len]; have := hq_lt; omega
  dsimp only [fidScanBin, fidScanHdr, sStep, sSteps, sStepZ, sStepsZ, sLd64, sLd32, sCall64,
    sThen, sElse, sGrpK4q, sGrpB4q, sGrpK3s, sGrpB4m, sGrpK4c, sGrpK5mp, sDummyVal, sDummyTup,
    full_bva_scan_cands_body]
  fid_hfast_nogrp
  fid_call hClines
  intro r_clines_bin
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (nc, qp, ()) mlp => ∃ wsp ws1p,
      qoff0 ≤ qp.toNat ∧ qp.toNat ≤ qoff0 + qsz0 ∧ nc.toNat ≤ init_lits.toNat ∧
      wsp.length = 2 * c.max_vars ∧ ws1p.length = 2 * c.max_vars ∧
      DenseWatchSliceOk F_cur s.core q.toNat qp.toNat (qoff0 + qsz0 - qp.toNat) ∧
      (∀ i < nc.toNat, (ws1p[i]?.getD 0#32).toNat < init_lits.toNat) ∧
      (FullMem c
        { core := { s.core with arena := ar },
          scratch :=
            { s.scratch with
              wsort := wsp, work_stk1 := ws1p, work_stk2 := ws2, ant_sz := ant } } ⋆ R) mlp)
    (fun (_, qp, _) _ => qoff0 + qsz0 - qp.toNat)
    (fun Jp hJp => by
      fid_hfast
      have h1 : (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64
          (qw &&& (2147483647 : BitVec 32)) <<< (1 : Nat)).toNat]'(by
          rw [hq_ast, h2q_n]; omega))).toNat = qoff0 := by
        simp only [hq_ast, h2q_n, hset, hoff_eq]; rfl
      dsimp only; refine hJp (ncntd, _, ()) ml ⟨ws, ws1, by rw [h1]; exact Nat.le_refl _,
        by rw [h1]; omega, hnc_le, hws_l, hws1_l,
        by simpa only [h1, Nat.add_sub_cancel_left] using hq_sl, hcntd_ok, hml⟩)
    (fun Jp (nc, qp, ()) mlp
        ⟨wsp, ws1p, hqp_ge, hqp_le, hncp_le, hwsp_l, hws1p_l, hrem, hcntdp, hmlp⟩ ihp => ?_)
  clear hml
  c0_hsplit
  · have hqp_lt_raw := hc; clear hc
    have hqp_lt : qp.toNat < qoff0 + qsz0 := by
      have h2q_mod : 2 * q.toNat % 2 ^ 64 = 2 * q.toNat := Nat.mod_eq_of_lt (by omega)
      have hqend_mod : ((s.core.wvec[2 * q.toNat % 2 ^ 64]'(by rw [h2q_mod]; omega)).toNat +
          (s.core.wvec[(2 * q.toNat % 2 ^ 64 + 1) % 2 ^ 64]'(by
            rw [h2q_mod, Nat.mod_eq_of_lt (by omega : 2 * q.toNat + 1 < 2 ^ 64)]; omega)).toNat) %
          2 ^ 64 = qoff0 + qsz0 := by
        simp only [h2q_mod, Nat.mod_eq_of_lt (by omega : 2 * q.toNat + 1 < 2 ^ 64),
          hoff_eq, hsz_eq]
        exact Nat.mod_eq_of_lt (by omega)
      rw [← hqend_mod]; simpa only [h2147, show (qw &&& 0x7FFFFFFF#32) = q from rfl] using
        hqp_lt_raw
    have hqp_ws : qp.toNat < s.core.wstk.length := by omega
    have hqp1_n : (qp + 1#64).toNat = qp.toNat + 1 := by simp only [bv_c0]; omega
    c0_hsteps_nogrp; c0_hstep; c0_hsplit
    · have ⟨hc_lt2, _, hrem_next⟩ :=
        FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hqp_ws (by assumption)
      let cand := s.core.wstk[qp.toNat]'hqp_ws &&& 0x7FFFFFFF#32
      have hcand_lt : cand.toNat < 2 * s.core.cur_vars := hc_lt2
      have hcand_shr : (cand >>> (1 : Nat)).toNat < c.max_vars := by rw [bv32_lshr1_nat]; omega
      have hcand_ws : (BitVec.setWidth 64 cand).toNat < wsp.length := by rw [hset, hwsp_l]; omega
      c0_hsteps_nogrp
      refine wp_join_state1 (t := i32)
        (α := BitVec 32 × List (BitVec 32) × List (BitVec 32)) (fun st => st.1)
        (fun ⟨nc1, wsp1, ws1p1⟩ mf =>
          nc1.toNat ≤ init_lits.toNat ∧ wsp1.length = 2 * c.max_vars ∧
          ws1p1.length = 2 * c.max_vars ∧
          (∀ i < nc1.toNat, (ws1p1[i]?.getD 0#32).toNat < init_lits.toNat) ∧
          (FullMem c
            { core := { s.core with arena := ar },
              scratch :=
                { s.scratch with
                  wsort := wsp1, work_stk1 := ws1p1, work_stk2 := ws2, ant_sz := ant } } ⋆ R) mf)
        (fun _ ⟨nc1, wsp1, ws1p1⟩ mf ⟨hnc1, hwsp1, hws1p1, hcntd1, hmf⟩ => by
          fid_hfast
          exact ihp (nc1, qp + 1#64, ()) mf (by dsimp only; rw [hqp1_n]; omega)
            ⟨wsp1, ws1p1, by rw [hqp1_n]; omega, by rw [hqp1_n]; omega, hnc1, hwsp1, hws1p1,
             by rw [hqp1_n, show qoff0 + qsz0 - (qp.toNat + 1) = qoff0 + qsz0 - qp.toNat - 1
                  by omega]; exact hrem_next, hcntd1, hmf⟩)
        (fun Jc hJc => ?_)
      have hil_u32 : init_lits.toNat < 2 ^ 32 := by omega
      have hcand_lm : (BitVec.setWidth 64 (s.core.wstk[qp.toNat]'hqp_ws &&&
          (2147483647 : BitVec 32))).toNat < s.core.lit_mark.length := by
        rw [h2147, bv64_setWidth_32, hlm_len]; omega
      have hcand_fl : (BitVec.setWidth 64 (((s.core.wstk[qp.toNat]'hqp_ws &&&
          (2147483647 : BitVec 32))) >>> (1 : BitVec 32))).toNat < s.core.flags.length := by
        rw [h2147, bv64_setWidth_32, hfl_len]
        have hshr : ∀ x : BitVec 32, (x >>> (1 : BitVec 32)).toNat = x.toNat / 2 :=
          fun x => by simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        rw [hshr]; omega
      have hcand_v : (BitVec.setWidth 64 (s.core.wstk[qp.toNat]'hqp_ws &&&
          (2147483647 : BitVec 32))).toNat < s.core.vals.length := by
        rw [h2147, bv64_setWidth_32, hvals_len]; omega
      have hcand_ws' : (BitVec.setWidth 64 (s.core.wstk[qp.toNat]'hqp_ws &&&
          (2147483647 : BitVec 32))).toNat < wsp.length := by
        rw [h2147, bv64_setWidth_32, hwsp_l]; omega
      fid_hfast
      all_goals
        first
        | exact hJc ⟨nc, wsp, ws1p⟩ mlp ⟨hncp_le, hwsp_l, hws1p_l, hcntdp, hmlp⟩
        | (refine hJc ⟨_, _, _⟩ _ ⟨?_, ?_, ?_, ?_, by assumption⟩
           · first
             | exact hncp_le
             | (simp only [show (1 : BitVec 32) = 1#32 from rfl, bv_c0] at *; omega)
           · (try simp only [List.length_set]); exact hwsp_l
           · (try simp only [List.length_set]); exact hws1p_l
           · intro i hi
             first
             | exact hcntdp i hi
             | (have hcand_il : (s.core.wstk[qp.toNat]'hqp_ws &&&
                    (2147483647 : BitVec 32)).toNat < init_lits.toNat := by
                  simp only [bv_c0] at *; omega
                have hnc1 : (nc + (1 : BitVec 32)).toNat = nc.toNat + 1 := by
                  simp only [show (1 : BitVec 32) = 1#32 from rfl, bv_c0] at *; omega
                rw [hnc1] at hi
                by_cases hie : i = nc.toNat
                · subst hie; rw [hset, List.getElem?_set_self (by rw [hws1p_l]; omega),
                    Option.getD_some]
                  exact hcand_il
                · rw [hset, List.getElem?_set_ne (Ne.symm hie)]; exact hcntdp i (by omega)))
    · have ⟨h2le, hrem_next⟩ :=
        FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hqp_ws (by assumption)
      have hqp2_n : (qp + 2#64).toNat = qp.toNat + 2 := by simp only [bv_c0]; omega
      fid_hfast
      exact ihp (nc, qp + 2#64, ()) mlp (by dsimp only; rw [hqp2_n]; omega)
        ⟨wsp, ws1p, by rw [hqp2_n]; omega, by rw [hqp2_n]; omega, hncp_le, hwsp_l, hws1p_l,
         by rw [hqp2_n, show qoff0 + qsz0 - (qp.toNat + 2) = qoff0 + qsz0 - qp.toNat - 2
              by omega]; exact hrem_next, hcntdp, hmlp⟩
  · c0_hsteps_nogrp
    exact hExit nc _ wsp ws1p mlp hncp_le hwsp_l hws1p_l hcntdp hmlp

private theorem fid_scan_cands_mp_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {row_off cur_qn : Val i32} {init_lits : Val i64} {J Jq : Cont [i32, i32, i32, i64]}
    {nql ncntd qi : Val i32} {ticks r_clines : Val i64} {qw : Val i32}
    {Js : Cont [i32, i32, i64]} {csz_bv : Val i32} {Jm : Cont [i32, i32, i32, i32]}
    {min_l min_d fc jf : Val i32} {Jc_join : Cont [i32, i32, i64, i32]}
    {moff msz : Val i32} {r_clines_min : Val i64} {Jmp : Cont [i32, i32, i64, i64, i32]}
    {ar ws ws1 ws2 : List (BitVec 32)} {lm1 : List (BitVec 8)} {ant : BitVec 64} {mf : Mem 64}
    (hslen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hdw : DenseWatchesInv F_cur s.core) (hcl0 : s.core.cur_level = 0)
    (hil_le : init_lits.toNat ≤ 2 * s.core.cur_vars)
    (_hqw_lits0 : ∀ x ∈ fullArenaClauseLitsCore s.core qw.toNat,
      (s.core.lit_mark[x]?.getD 0#8 &&& 1#8) ≠ 0#8 ∨ x < 2 * s.core.cur_vars)
    (_hlm_clr : ∀ l < 2 * s.core.cur_vars, (s.core.lit_mark[l]?.getD 0#8 &&& 6#8) = 0#8)
    (hqw_ref : qw.toNat ∈ fullArenaClauseRefsCore s.core)
    (hcsz_nat : csz_bv.toNat = fullArenaClauseSizeCore s.core qw.toNat)
    (hlm1_inv : LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 csz_bv.toNat lm1)
    (hml_lt : min_l.toNat < 2 * s.core.cur_vars)
    (hmoff_eq : moff.toNat = fullWatchOffCore s.core min_l.toNat)
    (hmsz_eq : msz.toNat = fullWatchSizeCore s.core min_l.toNat)
    (hnc_le : ncntd.toNat ≤ init_lits.toNat)
    (hws_l : ws.length = 2 * c.max_vars) (hws1_l : ws1.length = 2 * c.max_vars)
    (hbvaq : FidScanArBvaqInv c s ar ws2 0 nql.toNat)
    (hw_ar : FullWitnessInv c F0 F_cur { s.core with arena := ar })
    (hcntd_ok : ∀ i < ncntd.toNat, (ws1[i]?.getD 0#32).toNat < init_lits.toNat)
    (hmf : (FullMem c
      { core := { s.core with arena := ar, lit_mark := lm1 },
        scratch :=
          { s.scratch with wsort := ws, work_stk1 := ws1, work_stk2 := ws2, ant_sz := ant } } ⋆
      R) mf)
    (hJmp : ∀ (nql2 nc2 : BitVec 32) (ticks2 mp2 : BitVec 64) (nnou2 : BitVec 32)
      ar2 lm2 ws2' ws12 ql2 mmp,
      nc2.toNat ≤ init_lits.toNat → ws2'.length = 2 * c.max_vars →
      ws12.length = 2 * c.max_vars → FidScanArBvaqInv c s ar2 ql2 0 nql2.toNat →
      FidLmBit4Inv c lm1 ql2 0 nnou2.toNat lm2 →
      FullWitnessInv c F0 F_cur { s.core with arena := ar2 } →
      (∀ i < nc2.toNat, (ws12[i]?.getD 0#32).toNat < init_lits.toNat) →
      (FullMem c
        { core := { s.core with arena := ar2, lit_mark := lm2 },
          scratch :=
            { s.scratch with
              wsort := ws2', work_stk1 := ws12, work_stk2 := ql2, ant_sz := ant } } ⋆ R) mmp →
      Jmp (nql2, nc2, ticks2, mp2, nnou2, ()) mmp) :
    wp Γ Q X (fidScanMp row_off cur_qn c.hdr init_lits c.pVals c.pWvec c.pWstk c.pArena
      c.pLitMark c.pScratchBuf c.pWsort c.pWorkStk1 c.pFlags c.pWorkStk2 c.pRepr r_clines
      J Jq nql ncntd qi ticks qw Js csz_bv Jm min_l min_d fc jf Jc_join moff msz
      (BitVec.ofNat 64 c.max_vars) r_clines_min Jmp) mf := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena
  unfold dimacsBound at hmx hwcap har_b
  have hcl := hslen.core_ok; have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len
  have hws_len := hcl.wstk_len_arr; have har_len := hcl.arena_len_arr
  have hal_le := hcl.arena_len_le; have hwlen_le := hcl.wlen_le
  have hlm_len := hcl.lit_mark_len; have hvals_len := hcl.vals_len
  have hfl_len := hcl.flags_len
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  have hml_bd := hdw.layout.bounds min_l.toNat hml_lt
  have hml_sl := hdw.slices min_l.toNat hml_lt
  let moff0 := fullWatchOffCore s.core min_l.toNat
  let msz0 := fullWatchSizeCore s.core min_l.toNat
  have hqw_wf := hw.arena.refs_wf qw.toNat hqw_ref
  have har_l := hbvaq.1; have hws2_l := hbvaq.2.1
  let mkSt (arx : List (BitVec 32)) (lmx : List (BitVec 8))
      (wsx ws1x qlx : List (BitVec 32)) : FullState :=
    { core := { s.core with arena := arx, lit_mark := lmx },
      scratch :=
        { s.scratch with wsort := wsx, work_stk1 := ws1x, work_stk2 := qlx, ant_sz := ant } }
  dsimp only [fidScanMp, fidScanHdr, sStep, sSteps, sStepZ, sStepsZ, sLd64, sLd32, sCall64,
    sThen, sElse, sGrpK4q, sGrpB4q, sGrpK3s, sGrpB4m, sGrpK4c, sGrpK5mp, sDummyVal, sDummyTup,
    full_bva_scan_cands_body]
  refine wp_loop_inv
    (fun (nqlp, ncp, ticks_p, mp, nnoup, ()) mlm => ∃ arp lmp wsp ws1p qlp,
      moff0 ≤ mp.toNat ∧ mp.toNat ≤ moff0 + msz0 ∧ ncp.toNat ≤ init_lits.toNat ∧
      wsp.length = 2 * c.max_vars ∧ ws1p.length = 2 * c.max_vars ∧
      FidScanArBvaqInv c s arp qlp 0 nqlp.toNat ∧
      FidLmBit4Inv c lm1 qlp 0 nnoup.toNat lmp ∧
      FullWitnessInv c F0 F_cur { s.core with arena := arp } ∧
      DenseWatchSliceOk F_cur s.core min_l.toNat mp.toNat (moff0 + msz0 - mp.toNat) ∧
      (∀ i < ncp.toNat, (ws1p[i]?.getD 0#32).toNat < init_lits.toNat) ∧
      (FullMem c (mkSt arp lmp wsp ws1p qlp) ⋆ R) mlm)
    (fun (_, _, _, mp, _, ()) _ => moff0 + msz0 - mp.toNat)
    (fun JmpL hJmpL => by
      fid_hfast
      have h1 : (BitVec.setWidth 64 moff).toNat = moff0 := by
        simp only [hset, hmoff_eq]; rfl
      exact hJmpL (nql, ncntd, _, _, 0#32, ()) mf
        ⟨ar, lm1, ws, ws1, ws2, by rw [h1]; exact Nat.le_refl _, by rw [h1]; omega,
         hnc_le, hws_l, hws1_l, hbvaq, fidLmBit4Inv_init hlm1_inv.1, hw_ar,
         by simpa only [h1, Nat.add_sub_cancel_left] using hml_sl, hcntd_ok, hmf⟩)
    (fun JmpL (nqlp, ncp, ticks_p, mp, nnoup, ()) mlm
        ⟨arp, lmp, wsp, ws1p, qlp, hmp_ge, hmp_le, hncp_le, hwsp_l, hws1p_l, hbvaqp,
         hlm4p, hwp, hrem, hcntdp, hmlm⟩ ihmp => ?_)
  dsimp only [mkSt] at hmlm
  have harp_l := hbvaqp.1; have hqlp_l := hbvaqp.2.1; have hnqlp_le := hbvaqp.2.2.1
  have hlmp_l := hlm4p.1; have hnnoup_le := hlm4p.2.1
  have hm_end_mod : (BitVec.setWidth 64 moff + BitVec.setWidth 64 msz).toNat = moff0 + msz0 := by
    rw [BitVec.toNat_add, hset, hset, hmoff_eq, hmsz_eq]; exact Nat.mod_eq_of_lt (by omega)
  c0_hsplit
  · have hmp_lt : mp.toNat < moff0 + msz0 := by rw [← hm_end_mod]; assumption
    have hmp_ws : mp.toNat < s.core.wstk.length := by omega
    have hmp1_n : (mp + 1#64).toNat = mp.toNat + 1 := by simp only [bv_c0]; omega
    c0_hsplit
    · have ⟨_, _, hrem_next⟩ :=
        FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hmp_ws (by assumption)
      c0_hfast
      exact ihmp (nqlp, ncp, ticks_p, mp + 1#64, nnoup, ()) mlm
        (by dsimp only; rw [hmp1_n]; omega)
        ⟨arp, lmp, wsp, ws1p, qlp, by rw [hmp1_n]; omega, by rw [hmp1_n]; omega,
         hncp_le, hwsp_l, hws1p_l, hbvaqp, hlm4p, hwp,
         by rw [hmp1_n, show moff0 + msz0 - (mp.toNat + 1) =
              moff0 + msz0 - mp.toNat - 1 by omega]; exact hrem_next,
         hcntdp, hmlm⟩
    · c0_hsplit
      · c0_hfast
        exact hJmp nqlp ncp ticks_p (mp + 1#64) nnoup arp lmp wsp ws1p qlp mlm
          hncp_le hwsp_l hws1p_l hbvaqp hlm4p hwp hcntdp hmlm
      · have ⟨h2le, hrem_next⟩ :=
          FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hmp_ws (by assumption)
        have hmp1_ws : mp.toNat + 1 < s.core.wstk.length := by omega
        have hmp1_mod : (mp.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
            mp.toNat + 1 := by
          rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
        have ⟨_, hdr_ref, _⟩ :=
          FullBvaFwdHelpers.fwd_slice_occ_info hrem (by omega) hmp_ws hmp1_ws (by assumption)
        have hdr_wf := hw.arena.refs_wf _ hdr_ref
        have hmp2_n : (mp + 1#64 + 1#64).toNat = mp.toNat + 2 := by simp only [bv_c0]; omega
        let dr := s.core.wstk[mp.toNat + 1]'hmp1_ws
        have hdr_lt_ar : dr.toNat + 3 ≤ arp.length := by
          dsimp only [dr]; have := hdr_wf.1; have := hcl.arena_len_le; omega
        have hdr_eq : s.core.wstk[(mp + 1#64).toNat]'(by rw [hmp1_n]; exact hmp1_ws) = dr := by
          dsimp only [dr]; simp only [hmp1_n]
        have hdr_mod : s.core.wstk[(mp.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(
            by rw [hmp1_mod]; exact hmp1_ws) = dr := by
          dsimp only [dr]; simp only [hmp1_mod]
        have hdr2_n : (BitVec.setWidth 64 dr + 2).toNat = dr.toNat + 2 := by
          change (BitVec.setWidth 64 dr + 2#64).toNat = _; simp only [bv_c0]; omega
        have hdr0_ar : (BitVec.setWidth 64 (s.core.wstk[(mp.toNat +
            BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
              rw [hmp1_mod]; exact hmp1_ws))).toNat < arp.length := by
          rw [hdr_mod, hset]; omega
        have hdr2_ar : (BitVec.setWidth 64 (s.core.wstk[(mp.toNat +
            BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
              rw [hmp1_mod]; exact hmp1_ws)) + 2).toNat < arp.length := by
          rw [hdr_mod, hdr2_n]; omega
        have hdr0_ar' : (BitVec.setWidth 64 (s.core.wstk[(mp + 1#64).toNat]'(by
            rw [hmp1_n]; exact hmp1_ws))).toNat < arp.length := by
          rw [hdr_eq, hset]; omega
        have hdr2_ar' : (BitVec.setWidth 64 (s.core.wstk[(mp + 1#64).toNat]'(by
            rw [hmp1_n]; exact hmp1_ws)) + 2).toNat < arp.length := by
          rw [hdr_eq, hdr2_n]; omega
        c0_hsplit
        · exact ihmp (nqlp, ncp, ticks_p, mp + 1#64 + 1#64, nnoup, ()) mlm
            (by dsimp only; rw [hmp2_n]; omega)
            ⟨arp, lmp, wsp, ws1p, qlp, by rw [hmp2_n]; omega,
             by rw [hmp2_n]; omega, hncp_le, hwsp_l, hws1p_l, hbvaqp, hlm4p, hwp,
             by rw [hmp2_n, show moff0 + msz0 - (mp.toNat + 2) =
                  moff0 + msz0 - mp.toNat - 2 by omega]; exact hrem_next,
             hcntdp, hmlm⟩
        · c0_hsplit_nogrp
          · exact ihmp (nqlp, ncp, ticks_p + 1#64, mp + 1#64 + 1#64, nnoup, ()) mlm
              (by dsimp only; rw [hmp2_n]; omega)
              ⟨arp, lmp, wsp, ws1p, qlp, by rw [hmp2_n]; omega,
               by rw [hmp2_n]; omega, hncp_le, hwsp_l, hws1p_l, hbvaqp, hlm4p, hwp,
               by rw [hmp2_n, show moff0 + msz0 - (mp.toNat + 2) =
                    moff0 + msz0 - mp.toNat - 2 by omega]; exact hrem_next,
               hcntdp, hmlm⟩
          · exact ihmp (nqlp, ncp, ticks_p + 1#64, mp + 1#64 + 1#64, nnoup, ()) mlm
              (by dsimp only; rw [hmp2_n]; omega)
              ⟨arp, lmp, wsp, ws1p, qlp, by rw [hmp2_n]; omega,
               by rw [hmp2_n]; omega, hncp_le, hwsp_l, hws1p_l, hbvaqp, hlm4p, hwp,
               by rw [hmp2_n, show moff0 + msz0 - (mp.toNat + 2) =
                    moff0 + msz0 - mp.toNat - 2 by omega]; exact hrem_next,
               hcntdp, hmlm⟩
          · have hdr_0248 : (arp[dr.toNat]'(by omega) &&& 0x02480000#32) = 0#32 := by
              have h1 : (arp[(BitVec.setWidth 64 (s.core.wstk[(mp.toNat +
                  BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                    rw [hmp1_mod]; exact hmp1_ws))).toNat]'(by
                      rw [hdr_mod, hset]; omega) &&& (38273024 : BitVec 32)) = 0#32 := by
                simpa only [← hdr_mod] using (by assumption : _)
              simp only [hdr_mod] at h1
              simpa only [hset, show (38273024 : BitVec 32) = 0x02480000#32 from rfl] using h1
            have hdr_sz_ar : arp[dr.toNat + 2]'(by omega) = csz_bv := by
              have hst1 : s.core.wstk[(BitVec.toNat mp + 1) % 2 ^ 64]'(by
                  rw [Nat.mod_eq_of_lt (by change mp.toNat + 1 < 2 ^ 64; omega)]
                  exact hmp1_ws) = dr := by
                have hmpe : (BitVec.toNat mp + 1) % 2 ^ 64 =
                    (mp.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 := rfl
                simp only [hmpe]; exact hdr_mod
              have heq1 : dr.toNat + 2 =
                  ((s.core.wstk[(BitVec.toNat mp + 1) % 2 ^ 64]'(by
                    rw [Nat.mod_eq_of_lt (by change mp.toNat + 1 < 2 ^ 64; omega)]
                    exact hmp1_ws)).toNat + 2) % 2 ^ 64 := by
                rw [hst1]; exact (Nat.mod_eq_of_lt (by omega : dr.toNat + 2 < 2 ^ 64)).symm
              have h1 := congrArg (fun k => arp[k]?) heq1
              rw [List.getElem?_eq_getElem (by omega),
                List.getElem?_eq_getElem (by rw [← heq1]; omega)] at h1
              exact Option.some.inj (h1.trans (congrArg some (by assumption)))
            have ⟨hdr_nbvaq, hdr_ng_s, hdr_sz_eq⟩ :=
              fid_scan_cands_dr_info hcl hw hbvaqp hdr_ref hdr_lt_ar hdr_0248 hdr_sz_ar
            c0_hsteps_nogrp
            refine wp_join_state (α := BitVec 32 × Bool × BitVec 32)
              (fun ⟨cand, ok, djf⟩ => (cand, ok, djf, ()))
              (fun _ mdj => mdj = mlm)
              (fun _ ⟨cand, ok, _djf⟩ mdj hmdj => ?_)
              (fun Jdj hJdj => ?_)
            · subst mdj
              refine wp_join_state
                (α := BitVec 32 × BitVec 32 × BitVec 32 × List (BitVec 32) ×
                  List (BitVec 8) × List (BitVec 32) × List (BitVec 32) × List (BitVec 32))
                (fun ⟨nq1, nc1, nn1, _, _, _, _, _⟩ => (nq1, nc1, nn1, ()))
                (fun ⟨nq1, nc1, nn1, arB, lmB, wsB, ws1B, qlB⟩ mB =>
                  nc1.toNat ≤ init_lits.toNat ∧ wsB.length = 2 * c.max_vars ∧
                  ws1B.length = 2 * c.max_vars ∧
                  FidScanArBvaqInv c s arB qlB 0 nq1.toNat ∧
                  FidLmBit4Inv c lm1 qlB 0 nn1.toNat lmB ∧
                  FullWitnessInv c F0 F_cur { s.core with arena := arB } ∧
                  (∀ i < nc1.toNat, (ws1B[i]?.getD 0#32).toNat < init_lits.toNat) ∧
                  (FullMem c (mkSt arB lmB wsB ws1B qlB) ⋆ R) mB)
                (fun _ ⟨nq1, nc1, nn1, arB, lmB, wsB, ws1B, qlB⟩ mB
                    ⟨hnc1, hwsB_l, hws1B_l, hbvaqB, hlm4B, hwB, hcntdB, hmB⟩ => by
                  dsimp only [mkSt] at hmB
                  fid_hfast
                  exact ihmp (nq1, nc1, ticks_p + 1#64, mp + 1#64 + 1#64, nn1, ()) mB
                    (by dsimp only; rw [hmp2_n]; omega)
                    ⟨arB, lmB, wsB, ws1B, qlB, by rw [hmp2_n]; omega,
                     by rw [hmp2_n]; omega, hnc1, hwsB_l, hws1B_l, hbvaqB, hlm4B, hwB,
                     by rw [hmp2_n, show moff0 + msz0 - (mp.toNat + 2) =
                          moff0 + msz0 - mp.toNat - 2 by omega]; exact hrem_next,
                     hcntdB, hmB⟩)
                (fun Jcont hJcont => ?_)
              c0_hsplit
              · c0_hsplit
                · c0_hsplit
                  · have hcand_il : cand.toNat < init_lits.toNat := by
                      simp only [bv_c0] at *; omega
                    have hcand_lt : cand.toNat < 2 * c.max_vars := by omega
                    have hcand_fl : (BitVec.setWidth 64 (cand >>> (1 : BitVec 32))).toNat <
                        s.core.flags.length := by
                      rw [hset, bv32_lshr1_bv, hfl_len]; omega
                    c0_hsplit
                    · have hcand_v : (BitVec.setWidth 64 cand).toNat < s.core.vals.length := by
                        rw [hset, hvals_len]; omega
                      c0_hsplit
                      · refine wp_join_state
                          (α := BitVec 32 × List (BitVec 8) × List (BitVec 32))
                          (fun ⟨nn1, _, _⟩ => (nn1, ()))
                          (fun ⟨nn1, lmA, qlA⟩ mA =>
                            FidScanArBvaqInv c s arp qlA 0 nqlp.toNat ∧
                            FidLmBit4Inv c lm1 qlA 0 nn1.toNat lmA ∧
                            (FullMem c (mkSt arp lmA wsp ws1p qlA) ⋆ R) mA)
                          (fun _ ⟨nn1, lmA, qlA⟩ mA ⟨hbvaqA, hlm4A, hmA⟩ => ?_)
                          (fun Ja hJa => ?_)
                        · dsimp only [mkSt] at hmA
                          have hqlA_l := hbvaqA.2.1
                          c0_hsteps_nogrp
                          refine wp_join_state
                            (α := BitVec 32 × List (BitVec 32) × List (BitVec 32))
                            (fun ⟨nq1, _, _⟩ => (nq1, ()))
                            (fun ⟨nq1, arB, qlB⟩ mB =>
                              FidScanArBvaqInv c s arB qlB 0 nq1.toNat ∧
                              FidLmBit4Inv c lm1 qlB 0 nn1.toNat lmA ∧
                              FullWitnessInv c F0 F_cur { s.core with arena := arB } ∧
                              (FullMem c (mkSt arB lmA wsp ws1p qlB) ⋆ R) mB)
                            (fun _ ⟨nq1, arB, qlB⟩ mB ⟨hbvaqB, hlm4B, hwB, hmB⟩ => ?_)
                            (fun Jb hJb => ?_)
                          · clear hmA
                            dsimp only [mkSt] at hmB
                            have hcand_ws : (BitVec.setWidth 64 cand).toNat < wsp.length := by
                              rw [hset, hwsp_l]; omega
                            c0_hsteps_nogrp
                            refine wp_join_state1 (t := i32)
                              (α := BitVec 32 × List (BitVec 32))
                              (fun st => st.1)
                              (fun ⟨nc1, ws1C⟩ mC =>
                                nc1.toNat ≤ init_lits.toNat ∧ ws1C.length = 2 * c.max_vars ∧
                                (∀ i < nc1.toNat,
                                  (ws1C[i]?.getD 0#32).toNat < init_lits.toNat) ∧
                                (FullMem c (mkSt arB lmA wsp ws1C qlB) ⋆ R) mC)
                              (fun _ ⟨nc1, ws1C⟩ mC ⟨hnc1, hws1C_l, hcntdC, hmC⟩ => ?_)
                              (fun Jc1 hJc1 => ?_)
                            · clear hmB
                              dsimp only [mkSt] at hmC; fid_hfast
                              · exact hJcont ⟨nq1, nc1, nn1, arB, lmA, _, ws1C, qlB⟩ m
                                  ⟨hnc1, by simp [hwsp_l], hws1C_l, hbvaqB, hlm4B, hwB, hcntdC, hm⟩
                              · exact hJcont ⟨nq1, nc1, nn1, arB, lmA, wsp, ws1C, qlB⟩ mC
                                  ⟨hnc1, hwsp_l, hws1C_l, hbvaqB, hlm4B, hwB, hcntdC, hmC⟩
                            · fid_hfast
                              · have hnc1_n : (ncp + 1#32).toNat = ncp.toNat + 1 := by
                                  simp only [bv_c0] at *; omega
                                refine hJc1 ⟨ncp + 1#32, _⟩ m ⟨by rw [hnc1_n]; omega,
                                  by simp [hws1p_l], fun i hi => ?_, hm⟩
                                rw [hnc1_n] at hi
                                by_cases hie : i = ncp.toNat
                                · subst hie
                                  rw [hset, List.getElem?_set_self (by rw [hws1p_l]; omega),
                                    Option.getD_some]
                                  exact hcand_il
                                · rw [hset, List.getElem?_set_ne (Ne.symm hie)]
                                  exact hcntdp i (by omega)
                              · exact hJc1 ⟨ncp, ws1p⟩ mB ⟨hncp_le, hws1p_l, hcntdp, hmB⟩
                              · exact hJc1 ⟨ncp, ws1p⟩ mB ⟨hncp_le, hws1p_l, hcntdp, hmB⟩
                          · c0_hsplit
                            · have hnq_lt : nqlp.toNat < c.max_vars := by
                                simp only [bv_c0] at *; omega
                              have hnq1 : (nqlp + 1#32).toNat = nqlp.toNat + 1 := by
                                simp only [bv_c0]; omega
                              have hnq_ql : (BitVec.setWidth 64 nqlp).toNat < qlA.length := by
                                rw [hset, hqlA_l]; omega
                              have hdr_ar_b : (BitVec.setWidth 64 dr).toNat < arp.length := by
                                rw [hset]; omega
                              fid_hfast
                              have ⟨hbvaq_next, hlm4_next, hw_next⟩ :=
                                fid_scan_cands_stepB_inv hcl hw hwp hcl0 hbvaqA hlm4A hnq_lt
                                  hdr_ref (by omega) hdr_nbvaq
                              simp only [show (1 : BitVec 64) = 1#64 from rfl, hdr_eq, hset,
                                show (33554432 : BitVec 32) = 0x02000000#32 from rfl] at hm
                              exact hJb ⟨nqlp + 1#32, _, _⟩ m
                                ⟨by rw [hnq1]; exact hbvaq_next, hlm4_next, hw_next, hm⟩
                            · fid_hfast
                              exact hJb ⟨nqlp, arp, qlA⟩ mA ⟨hbvaqA, hlm4A, hwp, hmA⟩
                        · c0_hsplit
                          · have hnn_lt : nnoup.toNat < c.max_vars := by
                              simp only [bv_c0] at *; omega
                            have hnn1 : (nnoup + 1#32).toNat = nnoup.toNat + 1 := by
                              simp only [bv_c0]; omega
                            have hmxnn :
                                (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 nnoup).toNat =
                                  c.max_vars + nnoup.toNat := by simp only [bv_c0]; omega
                            have hmxnn_ql : (BitVec.ofNat 64 c.max_vars +
                                BitVec.setWidth 64 nnoup).toNat < qlp.length := by
                              rw [hmxnn, hqlp_l]; omega
                            have hcand_lm : (BitVec.setWidth 64 cand).toNat < lmp.length := by
                              rw [hset, hlmp_l]; omega
                            fid_hfast
                            simp only [hmxnn] at hm; simp only [hset] at hm
                            try simp only [bv8_trunc_or_4] at hm
                            exact hJa ⟨nnoup + 1#32, _, _⟩ _
                              ⟨fidScanArBvaqInv_set_ql_hi hbvaqp
                                 (idx := c.max_vars + nnoup.toNat) (by omega) cand,
                               by rw [hnn1]; exact (fidLmBit4Inv_push hqlp_l hlm4p hnn_lt
                                 hcand_lt), hm⟩
                          · fid_hfast; exact hJa ⟨nnoup, lmp, qlp⟩ mlm ⟨hbvaqp, hlm4p, hmlm⟩
                      · exact hJcont ⟨nqlp, ncp, nnoup, arp, lmp, wsp, ws1p, qlp⟩ mlm
                          ⟨hncp_le, hwsp_l, hws1p_l, hbvaqp, hlm4p, hwp, hcntdp, hmlm⟩
                    · exact hJcont ⟨nqlp, ncp, nnoup, arp, lmp, wsp, ws1p, qlp⟩ mlm
                        ⟨hncp_le, hwsp_l, hws1p_l, hbvaqp, hlm4p, hwp, hcntdp, hmlm⟩
                  · exact hJcont ⟨nqlp, ncp, nnoup, arp, lmp, wsp, ws1p, qlp⟩ mlm
                      ⟨hncp_le, hwsp_l, hws1p_l, hbvaqp, hlm4p, hwp, hcntdp, hmlm⟩
                · exact hJcont ⟨nqlp, ncp, nnoup, arp, lmp, wsp, ws1p, qlp⟩ mlm
                    ⟨hncp_le, hwsp_l, hws1p_l, hbvaqp, hlm4p, hwp, hcntdp, hmlm⟩
              · exact hJcont ⟨nqlp, ncp, nnoup, arp, lmp, wsp, ws1p, qlp⟩ mlm
                  ⟨hncp_le, hwsp_l, hws1p_l, hbvaqp, hlm4p, hwp, hcntdp, hmlm⟩
            · refine wp_loop_inv
                (fun (cand, dj, ()) mdj => mdj = mlm ∧ dj.toNat ≤ csz_bv.toNat)
                (fun (_, dj, _) _ => csz_bv.toNat - dj.toNat)
                (fun Jd hJd => by
                  fid_hfast; exact hJd (0xFFFFFFFF#32, 0#32, ()) mlm ⟨rfl, Nat.zero_le _⟩)
                (fun Jd (cand, dj, ()) mdj ⟨hmdj, hdj_le⟩ ihd => ?_)
              rcases hmdj with rfl
              c0_hsplit
              · have hdj_lt : dj.toNat < csz_bv.toNat := by assumption
                have hdj1 : (dj + 1#32).toNat = dj.toNat + 1 := by simp only [bv_c0]; omega
                have hdr_end : dr.toNat + 3 + csz_bv.toNat ≤ s.core.arena_len := by
                  dsimp only [dr]; have := hdr_wf.2.2.1; have := hdr_wf.2.2.2.1; omega
                have hdj_sz : dj.toNat < fullArenaClauseSizeCore s.core dr.toNat := by
                  rw [hdr_sz_eq]; exact hdj_lt
                have hdrj_n : (BitVec.setWidth 64 dr + 3 + BitVec.setWidth 64 dj).toNat =
                    dr.toNat + 3 + dj.toNat := by
                  change (BitVec.setWidth 64 dr + 3#64 + BitVec.setWidth 64 dj).toNat = _
                  simp only [bv_c0]; omega
                have hdl_eq : arp[dr.toNat + 3 + dj.toNat]'(by omega) =
                    s.core.arena[dr.toNat + 3 + dj.toNat]'(by omega) := by
                  have h1 := (fid_scan_cands_ar_lits_eq hcl hw hbvaqp hdr_ref).2 dj.toNat hdj_sz
                  rw [List.getElem?_eq_getElem (by omega),
                    List.getElem?_eq_getElem (by omega)] at h1
                  exact Option.some.inj h1
                have hdl_lt : (arp[dr.toNat + 3 + dj.toNat]'(by omega)).toNat <
                    2 * s.core.cur_vars := by
                  rw [hdl_eq]
                  exact hw.arena.lits_lt dr.toNat hdr_ref hdr_ng_s _ (List.mem_of_getElem?
                    (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem hdj_sz (by omega)))
                have hdrj_ar : (BitVec.setWidth 64 (s.core.wstk[(mp.toNat +
                    BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                      rw [hmp1_mod]; exact hmp1_ws)) + 3 + BitVec.setWidth 64 dj).toNat <
                    arp.length := by rw [hdr_mod, hdrj_n, harp_l]; dsimp only [dr]; omega
                have hdl_lm : (BitVec.setWidth 64 (arp[(BitVec.setWidth 64
                    (s.core.wstk[(mp.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                      rw [hmp1_mod]; exact hmp1_ws)) + 3 +
                    BitVec.setWidth 64 dj).toNat]'hdrj_ar)).toNat < lmp.length := by
                  simp only [hdr_mod]; simp only [hdrj_n, hset]; omega
                have hdrj_ar' : (BitVec.setWidth 64 (s.core.wstk[(mp + 1#64).toNat]'(by
                    rw [hmp1_n]; exact hmp1_ws)) + 3 + BitVec.setWidth 64 dj).toNat <
                    arp.length := by rw [hdr_eq, hdrj_n, harp_l]; dsimp only [dr]; omega
                have hdl_lm' : (BitVec.setWidth 64 (arp[(BitVec.setWidth 64
                    (s.core.wstk[(mp + 1#64).toNat]'(by rw [hmp1_n]; exact hmp1_ws)) + 3 +
                    BitVec.setWidth 64 dj).toNat]'hdrj_ar')).toNat < lmp.length := by
                  simp only [hdr_eq]; simp only [hdrj_n, hset]; omega
                fid_hfast
                · exact hJdj ⟨cand, false, dj⟩ mdj rfl
                · exact hJdj ⟨cand, false, dj⟩ mdj rfl
                · exact ihd (_, dj + 1#32, ()) mdj (by dsimp only; rw [hdj1]; omega)
                    ⟨rfl, by rw [hdj1]; omega⟩
                · exact ihd (cand, dj + 1#32, ()) mdj (by dsimp only; rw [hdj1]; omega)
                    ⟨rfl, by rw [hdj1]; omega⟩
              · fid_hfast; exact hJdj ⟨cand, true, dj⟩ mdj rfl
  · fid_hfast
    exact hJmp nqlp ncp ticks_p mp nnoup arp lmp wsp ws1p qlp mlm
      hncp_le hwsp_l hws1p_l hbvaqp hlm4p hwp hcntdp hmlm

private theorem fid_scan_cands_large_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    (hClines : ∀ a m Q X, fidBvaClinesSpec a m Q X → Γ "full_bva_clines_fid" [i64] [i64] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {row_off cur_qn : Val i32} {init_lits : Val i64} {J Jq : Cont [i32, i32, i32, i64]}
    {nql ncntd qi : Val i32} {ticks r_clines : Val i64} {qw : Val i32}
    {Js : Cont [i32, i32, i64]} {ar ws ws1 ws2 : List (BitVec 32)} {ant : BitVec 64} {ml : Mem 64}
    (hslen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hdw : DenseWatchesInv F_cur s.core) (hcl0 : s.core.cur_level = 0)
    (hil_le : init_lits.toNat ≤ 2 * s.core.cur_vars)
    (hlm_clr : ∀ l < 2 * c.max_vars, (s.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8)
    (hqw_ref : qw.toNat ∈ fullArenaClauseRefsCore s.core)
    (hqw_ng : fullArenaClauseGarb s qw.toNat = false)
    (hws_l : ws.length = 2 * c.max_vars) (hws1_l : ws1.length = 2 * c.max_vars)
    (har_l : ar.length = c.arena_cap) (hnc_le : ncntd.toNat ≤ init_lits.toNat)
    (hbvaq : FidScanArBvaqInv c s ar ws2 0 nql.toNat)
    (hw_ar : FullWitnessInv c F0 F_cur { s.core with arena := ar })
    (hcntd_ok : ∀ i < ncntd.toNat, (ws1[i]?.getD 0#32).toNat < init_lits.toNat)
    (hml : (FullMem c
      { core := { s.core with arena := ar },
        scratch :=
          { s.scratch with wsort := ws, work_stk1 := ws1, work_stk2 := ws2, ant_sz := ant } } ⋆
      R) ml)
    (hExit : ∀ (nql_j nc_j : BitVec 32) (ticks_j : BitVec 64) ar_j ws_j ws1_j ql_j mj,
      nc_j.toNat ≤ init_lits.toNat → ws_j.length = 2 * c.max_vars → ws1_j.length = 2 * c.max_vars →
      FidScanArBvaqInv c s ar_j ql_j 0 nql_j.toNat →
      FullWitnessInv c F0 F_cur { s.core with arena := ar_j } →
      (∀ i < nc_j.toNat, (ws1_j[i]?.getD 0#32).toNat < init_lits.toNat) →
      (FullMem c
        { core := { s.core with arena := ar_j },
          scratch :=
            { s.scratch with wsort := ws_j, work_stk1 := ws1_j, work_stk2 := ql_j, ant_sz := ant } }
        ⋆ R) mj →
      Js (nql_j, nc_j, ticks_j, ()) mj) :
    wp Γ Q X (fidScanLarge row_off cur_qn c.hdr init_lits c.pVals c.pWvec c.pWstk c.pArena
      c.pLitMark c.pScratchBuf c.pWsort c.pWorkStk1 c.pFlags c.pWorkStk2 c.pRepr r_clines
      J Jq nql ncntd qi ticks qw Js) ml := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcl := hslen.core_ok
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr
  have har_len := hcl.arena_len_arr; have hal_le := hcl.arena_len_le; have hwlen_le := hcl.wlen_le
  have hlm_len := hcl.lit_mark_len; have hvals_len := hcl.vals_len; have hfl_len := hcl.flags_len
  have hrepr_len := hcl.repr_len
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  let mkSt (ar' : List (BitVec 32)) (lm : List (BitVec 8)) (ws' ws1' ws2' : List (BitVec 32))
      (ant' : BitVec 64) : FullState :=
    { core := { s.core with arena := ar', lit_mark := lm }
      scratch :=
        { s.scratch with wsort := ws', work_stk1 := ws1', work_stk2 := ws2', ant_sz := ant' } }
  dsimp only [mkSt] at hml
  have hqw_wf := hw.arena.refs_wf qw.toNat hqw_ref
  have hqw_sz_s : (s.core.arena[qw.toNat + 2]'(by omega)).toNat =
      fullArenaClauseSizeCore s.core qw.toNat := by
    unfold fullArenaClauseSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have har_lits_eq := fid_scan_cands_ar_lits_eq hcl hw hbvaq hqw_ref
  have hqw_sz_eq : (ar[qw.toNat + 2]'(by omega)).toNat =
      fullArenaClauseSizeCore s.core qw.toNat := by
    have h1 := har_lits_eq.1
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
    rw [Option.some.inj h1]; exact hqw_sz_s
  have hqw2_n : (BitVec.setWidth 64 qw + 2).toNat = qw.toNat + 2 := by
    change (BitVec.setWidth 64 qw + 2#64).toNat = _; simp only [bv_c0]; omega
  have hqw2_mod : (qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = qw.toNat + 2 := by
    rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
  have hqw2_ar : (BitVec.setWidth 64 qw + 2).toNat < ar.length := by
    rw [hqw2_n, har_l]; have := hqw_wf.1; omega
  let csz_bv := ar[(BitVec.setWidth 64 qw + 2).toNat]'hqw2_ar
  have hcsz_nat : csz_bv.toNat = fullArenaClauseSizeCore s.core qw.toNat := by
    dsimp only [csz_bv]; simp only [hqw2_n]; exact hqw_sz_eq
  have hcsz_mod : csz_bv = ar[(qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
      rw [hqw2_mod]; omega) := by
    dsimp only [csz_bv]; simp only [hqw2_n, hqw2_mod]
  dsimp only [fidScanLarge, fidScanHdr, sStep, sSteps, sStepZ, sStepsZ, sLd64, sLd32, sCall64,
    sThen, sElse, sGrpK4q, sGrpB4q, sGrpK3s, sGrpB4m, sGrpK4c, sGrpK5mp, sDummyVal, sDummyTup,
    full_bva_scan_cands_body]
  c0_hsteps_nogrp
  refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × List (BitVec 8))
    (fun ⟨min_l, min_d, fc, jf, _⟩ => (min_l, min_d, fc, jf, ()))
    (fun ⟨min_l, _min_d, _, _, lm1⟩ _mf =>
      LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 csz_bv.toNat lm1 ∧
      (min_l ≠ 0xFFFFFFFF#32 → min_l.toNat < 2 * s.core.cur_vars) ∧
      (FullMem c (mkSt ar lm1 ws ws1 ws2 ant) ⋆ R) _mf)
    (fun _ ⟨min_l, min_d, fc, _jf, lm1⟩ mf ⟨hlm1_inv, hmin_ok, hmf⟩ => ?_)
    (fun Jm hJm => ?_)
  · dsimp only [mkSt] at hmf
    fid_hfast_nogrp
    refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 64 × BitVec 32 ×
        List (BitVec 32) × List (BitVec 32) × List (BitVec 32) × List (BitVec 32))
      (fun ⟨nql_j, nc_j, ticks_j, jf_j, _, _, _, _⟩ => (nql_j, nc_j, ticks_j, jf_j, ()))
      (fun ⟨nql_j, nc_j, _ticks_j, _jf_j, ar_j, ws_j, ws1_j, ql_j⟩ mj =>
        nc_j.toNat ≤ init_lits.toNat ∧
        ws_j.length = 2 * c.max_vars ∧
        ws1_j.length = 2 * c.max_vars ∧
        FidScanArBvaqInv c s ar_j ql_j 0 nql_j.toNat ∧
        FullWitnessInv c F0 F_cur { s.core with arena := ar_j } ∧
        (∀ i < nc_j.toNat, (ws1_j[i]?.getD 0#32).toNat < init_lits.toNat) ∧
        (FullMem c (mkSt ar_j lm1 ws_j ws1_j ql_j ant) ⋆ R) mj)
      (fun _ ⟨nql_j, nc_j, ticks_j, _jf_j, ar_j, ws_j, ws1_j, ql_j⟩ mj
        ⟨hnc_j, hws_j_l, hws1_j_l, hbvaq_j, hw_j, hcntd_j, hmj⟩ => ?_)
      (fun Jc_join hJc_join => ?_)
    · clear hmf
      dsimp only [mkSt] at hmj
      have har_lits := (fid_scan_cands_ar_lits_eq hcl hw hbvaq_j hqw_ref).2
      have har_j_l := hbvaq_j.1
      c0_hsteps_nogrp
      refine wp_loop_inv
        (fun (j, ()) mj => ∃ lmj, j.toNat ≤ csz_bv.toNat ∧
          LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat j.toNat csz_bv.toNat lmj ∧
          (FullMem c (mkSt ar_j lmj ws_j ws1_j ql_j ant) ⋆ R) mj)
        (fun (j, ()) _ => csz_bv.toNat - j.toNat)
        (fun Jc2 hJc2 => by
          fid_hfast; exact hJc2 (0#32, ()) _ ⟨lm1, Nat.zero_le _, hlm1_inv, hmj⟩)
        (fun Jc2 (j, ()) mj ⟨lmj, hj_le, hlmj_inv_j, hmj_c2⟩ ihc2 => ?_)
      clear hmj; dsimp only [mkSt] at hmj_c2
      have hlmj_l := hlmj_inv_j.1
      c0_hsplit
      · have hj_lt : j.toNat < csz_bv.toNat := by
          rw [hcsz_mod]; simpa only [] using (by assumption : _)
        have hcj_eq : ar_j[qw.toNat + 3 + j.toNat]'(by omega) =
            s.core.arena[qw.toNat + 3 + j.toNat]'(by omega) := by
          have h1 := har_lits j.toNat (by omega)
          rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
          exact Option.some.inj h1
        have hcj_lt : (s.core.arena[qw.toNat + 3 + j.toNat]'(by omega)).toNat <
            2 * s.core.cur_vars :=
          hw.arena.lits_lt qw.toNat hqw_ref hqw_ng _ (List.mem_of_getElem?
            (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (by omega) (by omega)))
        have hj1 : (j + 1#32).toNat = j.toNat + 1 := by simp only [bv_c0]; omega
        have hidx_n : (BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat =
            qw.toNat + 3 + j.toNat := by
          change (BitVec.setWidth 64 qw + 3#64 + BitVec.setWidth 64 j).toNat = _
          simp only [bv_c0]; omega
        have hidx_ar : (BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat <
            ar_j.length := by rw [hidx_n, har_j_l]; omega
        have hcj_lm : (BitVec.setWidth 64
            (ar_j[(BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat]'hidx_ar)).toNat <
            lmj.length := by simp only [hidx_n, hset, hcj_eq]; omega
        fid_hfast
        simp only [hidx_n, hset] at hm
        try simp only [bv8_trunc_and_fd] at hm
        have hstep : LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat (j.toNat + 1)
            csz_bv.toNat (lmj.set (ar_j[qw.toNat + 3 + j.toNat]'(by omega)).toNat
              ((lmj[(ar_j[qw.toNat + 3 + j.toNat]'(by omega)).toNat]'(by
                rw [hcj_eq]; omega)) &&& 0xFD#8)) := by
          have h0 := lmBit2Inv_clear_step hlm_len
            (fun l hl => (bv8_bit_zero_of_and_fe (hlm_clr l hl)).1)
            hlmj_inv_j hj_lt (by omega) (by omega)
          simpa only [← hcj_eq] using h0
        exact ihc2 (j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
          ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep, hm⟩
      · have hj_eq : j.toNat = csz_bv.toNat := by
          rw [hcsz_mod] at hj_le ⊢
          have h1 : ¬ j.toNat < (ar[(qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
            rw [hqw2_mod]; omega)).toNat := by simpa only [] using (by assumption : _)
          omega
        rw [hj_eq] at hlmj_inv_j
        have hlm_rest : lmj = s.core.lit_mark := lmBit2Inv_done hlm_len hlmj_inv_j
        rw [hlm_rest] at hmj_c2; fid_hfast
        exact hExit nql_j nc_j ticks_j ar_j ws_j ws1_j ql_j mj
          hnc_j hws_j_l hws1_j_l hbvaq_j hw_j hcntd_j hmj_c2
    · c0_hsplit
      · c0_hsplit
        · dsimp only
          have hmin_ne : min_l ≠ 0xFFFFFFFF#32 := hc; clear hc
          have hml_lt : min_l.toNat < 2 * s.core.cur_vars := hmin_ok hmin_ne
          have hml_bd := hdw.layout.bounds min_l.toNat hml_lt
          have hml_sl := hdw.slices min_l.toNat hml_lt
          have h2ml_n : (BitVec.setWidth 64 min_l <<< (1 : Nat)).toNat = 2 * min_l.toNat := by
            simp only [bv_c0]; omega
          have h2ml_mod : 2 * min_l.toNat % 2 ^ 64 = 2 * min_l.toNat :=
            Nat.mod_eq_of_lt (by omega)
          have hmoff_eq : (s.core.wvec[2 * min_l.toNat]'(by omega)).toNat =
              fullWatchOffCore s.core min_l.toNat := by
            unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hmsz_eq : (s.core.wvec[2 * min_l.toNat + 1]'(by omega)).toNat =
              fullWatchSizeCore s.core min_l.toNat := by
            unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          let moff0 := fullWatchOffCore s.core min_l.toNat
          let msz0 := fullWatchSizeCore s.core min_l.toNat
          have h2ml_wv : (BitVec.setWidth 64 min_l <<< (1 : Nat)).toNat <
              s.core.wvec.length := by rw [h2ml_n]; omega
          have h2ml1_wv : ((BitVec.setWidth 64 min_l <<< (1 : Nat)) + 1).toNat <
              s.core.wvec.length := by
            change ((BitVec.setWidth 64 min_l <<< (1 : Nat)) + 1#64).toNat < _
            simp only [bv_c0]; omega
          have hmd_repr : (BitVec.setWidth 64 min_d).toNat < 2 ^ 64 := by omega
          have hml_repr_w : (BitVec.setWidth 64 min_l).toNat < s.core.repr.length := by
            rw [hset, hrepr_len]; omega
          fid_hfast_nogrp
          fid_call hClines
          intro r_clines_min
          c0_hsteps_nogrp
          refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 64 × BitVec 64 × BitVec 32 ×
              List (BitVec 32) × List (BitVec 8) × List (BitVec 32) × List (BitVec 32) ×
              List (BitVec 32))
            (fun ⟨nql2, nc2, ticks2, mp2, nnou2, _, _, _, _, _⟩ =>
              (nql2, nc2, ticks2, mp2, nnou2, ()))
            (fun ⟨nql2, nc2, _, _, nnou2, ar2, lm2, ws2', ws12, ql2⟩ mmp =>
              nc2.toNat ≤ init_lits.toNat ∧ ws2'.length = 2 * c.max_vars ∧
              ws12.length = 2 * c.max_vars ∧ FidScanArBvaqInv c s ar2 ql2 0 nql2.toNat ∧
              FidLmBit4Inv c lm1 ql2 0 nnou2.toNat lm2 ∧
              FullWitnessInv c F0 F_cur { s.core with arena := ar2 } ∧
              (∀ i < nc2.toNat, (ws12[i]?.getD 0#32).toNat < init_lits.toNat) ∧
              (FullMem c (mkSt ar2 lm2 ws2' ws12 ql2 ant) ⋆ R) mmp)
            (fun _ ⟨nql2, nc2, ticks2, _mp2, nnou2, ar2, lm2, ws2', ws12, ql2⟩ mmp
                ⟨hnc2, hws2'_l, hws12_l, hbvaq2, hlm4_2, hw2, hcntd2, hmmp⟩ => ?_)
            (fun Jmp hJmp => ?_)
          · clear hmf
            dsimp only [mkSt] at hmmp
            have hql2_l := hbvaq2.2.1
            refine wp_loop_inv
              (fun (j, ()) mj4 => ∃ lmj4,
                j.toNat ≤ nnou2.toNat ∧ FidLmBit4Inv c lm1 ql2 j.toNat nnou2.toNat lmj4 ∧
                (FullMem c (mkSt ar2 lmj4 ws2' ws12 ql2 ant) ⋆ R) mj4)
              (fun (j, ()) _ => nnou2.toNat - j.toNat)
              (fun Jc4 hJc4 => by
                fid_hfast; exact hJc4 (0#32, ()) mmp ⟨lm2, Nat.zero_le _, hlm4_2, hmmp⟩)
              (fun Jc4 (j, ()) mj4 ⟨lmj4, hj4_le, hlmj4, hmj4⟩ ihc4 => ?_)
            clear hmmp; dsimp only [mkSt] at hmj4
            have hlmj4_l := hlmj4.1; have hnn2_le := hlmj4.2.1
            c0_hsplit
            · have hj4_lt : j.toNat < nnou2.toNat := by assumption
              have hj4_1 : (j + 1#32).toNat = j.toNat + 1 := by simp only [bv_c0]; omega
              have hmxj : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 j).toNat =
                  c.max_vars + j.toNat := by simp only [bv_c0]; omega
              have hmxj_ql : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 j).toNat <
                  ql2.length := by rw [hmxj, hql2_l]; omega
              have ⟨hcl_lt, hstep4⟩ := fidLmBit4Inv_clear_step hlm1_inv.1 hql2_l
                (fun l hl => by
                  rw [lmBit2Inv_preserves_bit2 hlm1_inv hl]
                  exact (bv8_bit_zero_of_and_fe (hlm_clr l hl)).2)
                hlmj4 hj4_lt
              have hcl_lm : (BitVec.setWidth 64 (ql2[(BitVec.ofNat 64 c.max_vars +
                  BitVec.setWidth 64 j).toNat]'hmxj_ql)).toNat < lmj4.length := by
                simp only [hmxj, hset]; omega
              fid_hfast
              simp only [hmxj] at hm; simp only [hset] at hm
              try simp only [bv8_trunc_and_fb] at hm
              exact ihc4 (j + 1#32, ()) m (by dsimp only; rw [hj4_1]; omega)
                ⟨_, by rw [hj4_1]; omega, by rw [hj4_1]; exact hstep4, hm⟩
            · have hj4_eq : j.toNat = nnou2.toNat := by omega
              rw [hj4_eq] at hlmj4
              have hlm_eq1 : lmj4 = lm1 := fidLmBit4Inv_done hlm1_inv.1 hlmj4
              rw [hlm_eq1] at hmj4
              fid_hfast
              exact hJc_join ⟨nql2, nc2, ticks2, j, ar2, ws2', ws12, ql2⟩ _
                ⟨hnc2, hws2'_l, hws12_l, hbvaq2, hw2, hcntd2, hmj4⟩
          · have h21 : ((BitVec.setWidth 64 min_l <<< (1 : Nat)) + 1).toNat =
                2 * min_l.toNat + 1 := by
              change ((BitVec.setWidth 64 min_l <<< (1 : Nat)) + 1#64).toNat = _
              simp only [bv_c0]; omega
            have hmp := fid_scan_cands_mp_wp (Γ := Γ) (Q := Q) (X := X) (c := c) (F0 := F0)
              (F_cur := F_cur) (s := s) (R := R) (row_off := row_off) (cur_qn := cur_qn)
              (init_lits := init_lits) (J := fun _ _ => False) (Jq := fun _ _ => False)
              (nql := nql) (ncntd := ncntd) (qi := qi) (ticks := ticks) (r_clines := r_clines)
              (qw := qw) (Js := Js) (csz_bv := csz_bv) (Jm := fun _ _ => False)
              (min_l := min_l) (min_d := min_d) (fc := fc) (jf := 0#32) (Jc_join := Jc_join)
              (moff := s.core.wvec[(BitVec.setWidth 64 min_l <<< (1 : Nat)).toNat]'h2ml_wv)
              (msz := s.core.wvec[((BitVec.setWidth 64 min_l <<< (1 : Nat)) +
                1).toNat]'h2ml1_wv)
              (r_clines_min := r_clines_min) (Jmp := Jmp)
              hslen hw hdw hcl0 hil_le
                (fun x hx => Or.inr (hw.arena.lits_lt qw.toNat hqw_ref hqw_ng x hx))
                (fun l hl => by
                  have h1 := congrArg (· &&& 6#8) (hlm_clr l (by omega))
                  rwa [BitVec.and_assoc, show (0xFE#8 &&& 6#8) = 6#8 from rfl,
                    BitVec.zero_and] at h1)
                hqw_ref hcsz_nat hlm1_inv
                hml_lt (by simpa only [h2ml_n] using hmoff_eq)
                (by simpa only [h21] using hmsz_eq)
                hnc_le hws_l hws1_l hbvaq hw_ar hcntd_ok hmf
              (fun nql2 nc2 ticks2 mp2 nnou2 ar2 lm2 ws2' ws12 ql2 mmp
                hnc2 hws2' hws12 hbvaq2 hlm42 hw2 hcntd2 hmmp =>
                hJmp ⟨nql2, nc2, ticks2, mp2, nnou2, ar2, lm2, ws2', ws12, ql2⟩ mmp
                  ⟨hnc2, hws2', hws12, hbvaq2, hlm42, hw2, hcntd2, hmmp⟩)
            dsimp only [fidScanMp, fidScanLarge, fidScanHdr, sStep, sSteps, sStepZ, sStepsZ,
              sLd64, sLd32, sCall64, sThen, sElse, sGrpK4q, sGrpB4q, sGrpK3s, sGrpB4m,
              sGrpK4c, sGrpK5mp, sDummyVal, sDummyTup, full_bva_scan_cands_body] at hmp
            exact hmp
        · have hmin_eq : min_l = 0xFFFFFFFF#32 := hc; clear hc
          fid_hfast
          exact hJc_join ⟨nql, ncntd, ticks + 1#64, _, ar, ws, ws1, ws2⟩ mf
            ⟨hnc_le, hws_l, hws1_l, hbvaq, hw_ar, hcntd_ok, hmf⟩
      · have hfc_ne : fc ≠ 1#32 := hc; clear hc
        fid_hfast
        exact hJc_join ⟨nql, ncntd, ticks + 1#64, _, ar, ws, ws1, ws2⟩ mf
          ⟨hnc_le, hws_l, hws1_l, hbvaq, hw_ar, hcntd_ok, hmf⟩
  · refine wp_loop_inv
      (fun (min_l, min_d, fc, j, ()) mj => ∃ lmj, j.toNat ≤ csz_bv.toNat ∧
        LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 j.toNat lmj ∧
        (min_l ≠ 0xFFFFFFFF#32 → min_l.toNat < 2 * s.core.cur_vars) ∧
        (FullMem c (mkSt ar lmj ws ws1 ws2 ant) ⋆ R) mj)
      (fun (_, _, _, j, _) _ => csz_bv.toNat - j.toNat)
      (fun JmL hJmL => by
        fid_hfast; exact hJmL (0xFFFFFFFF#32, 0xFFFFFFFF#32, 0#32, 0#32, ()) ml
          ⟨s.core.lit_mark, Nat.zero_le _, lmBit2Inv_init hlm_len,
           fun h => absurd rfl h, hml⟩)
      (fun JmL (min_l, min_d, fc, j, ()) mj ⟨lmj, hj_le, hlmj_inv, hmin_ok, hmj⟩ ihm => ?_)
    clear hml; dsimp only [mkSt] at hmj
    have hlmj_l := hlmj_inv.1
    c0_hsplit
    · have hj_lt : j.toNat < csz_bv.toNat := by
        rw [hcsz_mod]; simpa only [] using (by assumption : _)
      have hj_sz : j.toNat < fullArenaClauseSizeCore s.core qw.toNat := by
        rw [← hcsz_nat]; exact hj_lt
      have hj1 : (j + 1#32).toNat = j.toNat + 1 := by simp only [bv_c0]; omega
      have hqwj_n : (BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat =
          qw.toNat + 3 + j.toNat := by
        change (BitVec.setWidth 64 qw + 3#64 + BitVec.setWidth 64 j).toNat = _
        simp only [bv_c0]; omega
      have hl_eq : ar[qw.toNat + 3 + j.toNat]'(by omega) =
          s.core.arena[qw.toNat + 3 + j.toNat]'(by omega) := by
        have h1 := har_lits_eq.2 j.toNat hj_sz
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
        exact Option.some.inj h1
      have hl_lt : (ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
        rw [hl_eq]; exact hw.arena.lits_lt qw.toNat hqw_ref hqw_ng _ (List.mem_of_getElem?
          (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem hj_sz (by omega)))
      have h2l1_n : ((BitVec.setWidth 64 (ar[qw.toNat + 3 + j.toNat]'(by omega)) <<<
          (1 : Nat)) + 1).toNat = 2 * (ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat + 1 := by
        let x := ar[qw.toNat + 3 + j.toNat]'(by omega)
        change ((BitVec.setWidth 64 x <<< (1 : Nat)) + 1#64).toNat = 2 * x.toNat + 1
        have hx : x.toNat < 2 ^ 32 := x.isLt
        rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 64),
          show (1#64).toNat = 1 from rfl, Nat.shiftLeft_eq, Nat.pow_one,
          Nat.mod_eq_of_lt (by omega : x.toNat * 2 < 2 ^ 64)]
        exact (Nat.mod_eq_of_lt (by omega : x.toNat * 2 + 1 < 2 ^ 64)).trans (by omega)
      have hqwj_ar : (BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat <
          ar.length := by rw [hqwj_n, har_l]; omega
      have hl_lm : (BitVec.setWidth 64
          (ar[(BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat]'hqwj_ar)).toNat <
          lmj.length := by simp only [hqwj_n, hset]; omega
      have h2l1_wv : ((BitVec.setWidth 64
          (ar[(BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat]'hqwj_ar) <<<
          (1 : Nat)) + 1).toNat < s.core.wvec.length := by
        simp only [hqwj_n, h2l1_n]; omega
      have hl_repr : (BitVec.setWidth 64
          (ar[(BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat]'hqwj_ar)).toNat <
          s.core.repr.length := by rw [hrepr_len]; omega
      have hlmj_lift := fid_scan_cands_lmj_lift hlmj_inv hj_le
      have hl_lt_s : (s.core.arena[qw.toNat + 3 + j.toNat]'(by omega)).toNat <
          2 * c.max_vars := by rw [← hl_eq]; omega
      have hstep2_base : LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 (j.toNat + 1)
          (lmj.set (ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat
            ((lmj[(ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat]'(by omega)) ||| 2#8)) := by
        have h0 := lmBit2Inv_or2 hlm_len hlmj_inv (by omega) hl_lt_s
        simpa only [← hl_eq] using h0
      fid_hfast
      · exact hJm ⟨min_l, min_d, fc + 1#32, j, lmj⟩ mj ⟨hlmj_lift, hmin_ok, hmj⟩
      · exact ihm (min_l, min_d, fc + 1#32, j + 1#32, ()) mj (by dsimp only; rw [hj1]; omega)
          ⟨lmj, by rw [hj1]; omega, by rw [hj1]; exact lmBit2Inv_skip hlmj_inv, hmin_ok, hmj⟩
      · refine ihm (_, _, fc, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
          ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep2_base,
           fun _ => by simp only [hqwj_n]; exact hl_lt, ?_⟩
        simp only [hqwj_n, hset] at hm; try simp only [bv8_trunc_or_2] at hm
        exact hm
      · refine ihm (_, _, fc, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
          ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep2_base,
           fun _ => by simp only [hqwj_n]; exact hl_lt, ?_⟩
        simp only [hqwj_n, hset] at hm; try simp only [bv8_trunc_or_2] at hm
        exact hm
      · refine ihm (min_l, min_d, fc, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
          ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep2_base, hmin_ok, ?_⟩
        simp only [hqwj_n, hset] at hm; try simp only [bv8_trunc_or_2] at hm
        exact hm
    · have hj_eq : j.toNat = csz_bv.toNat := by
        rw [hcsz_mod] at hj_le ⊢
        have h1 : ¬ j.toNat < (ar[(qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
          rw [hqw2_mod]; omega)).toNat := by simpa only [] using (by assumption : _)
        omega
      rw [hj_eq] at hlmj_inv; fid_hfast
      exact hJm ⟨min_l, min_d, fc, j, lmj⟩ mj ⟨hlmj_inv, hmin_ok, hmj⟩

theorem full_bva_scan_cands_fid_wp (Γ : Env)
    (hClines : ∀ a m Q X, fidBvaClinesSpec a m Q X → Γ "full_bva_clines_fid" [i64] [i64] a m Q X) :
    ∀ a m Q X, fidBvaScanCandsSpec a m Q X → Func.wp Γ full_bva_scan_cands_body a m Q X := by
  rintro ⟨h, row_off, cur_qn, init_lits, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hslen, hw, hnodup, hext, hl0, hdm, hil_le, hlm_clr, hrow_bd,
     hrow_ok, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcl := hslen.core_ok; have hsc := hslen.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr
  have har_len := hcl.arena_len_arr; have hal_le := hcl.arena_len_le; have hwlen_le := hcl.wlen_le
  have hlm_len := hcl.lit_mark_len; have hvals_len := hcl.vals_len; have hfl_len := hcl.flags_len
  have hrepr_len := hcl.repr_len
  have hsb_len := hsc.scratch_buf_len; have hwsort_len := hsc.wsort_len
  have hws1_len := hsc.work_stk1_len; have hws2_len := hsc.work_stk2_len
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  have hdw : DenseWatchesInv F_cur s.core := by
    have h1 := hw.watches; unfold ModeWatchesInv at h1; rwa [ite_eq_right hdm] at h1
  let mkSt (ar : List (BitVec 32)) (lm : List (BitVec 8)) (ws ws1 ws2 : List (BitVec 32))
      (ant : BitVec 64) : FullState :=
    { core := { s.core with arena := ar, lit_mark := lm }
      scratch := { s.scratch with wsort := ws, work_stk1 := ws1, work_stk2 := ws2, ant_sz := ant } }
  unfold Func.wp full_bva_scan_cands_body
  fid_hfast_nogrp
  fid_call hClines
  intro r_clines
  dsimp only [Arg.val]
  c0_hsteps
  refine wp_loop_inv
    (fun (nql, ncntd, qi, ticks, ()) ml => ∃ ar ws ws1 ws2 ant,
      qi.toNat ≤ cur_qn.toNat ∧ ncntd.toNat ≤ init_lits.toNat ∧
      ws.length = 2 * c.max_vars ∧ ws1.length = 2 * c.max_vars ∧
      FidScanArBvaqInv c s ar ws2 0 nql.toNat ∧
      FullWitnessInv c F0 F_cur { s.core with arena := ar } ∧
      (∀ i < ncntd.toNat, (ws1[i]?.getD 0#32).toNat < init_lits.toNat) ∧
      (FullMem c (mkSt ar s.core.lit_mark ws ws1 ws2 ant) ⋆ R) ml)
    (fun (_, _, qi, _, _) _ => cur_qn.toNat - qi.toNat)
    (fun Jq hJq => by
      c0_hsteps; exact hJq (0#32, 0#32, 0#32, _, ()) m
        ⟨s.core.arena, s.scratch.wsort, s.scratch.work_stk1, s.scratch.work_stk2, s.scratch.ant_sz,
         Nat.zero_le _, Nat.zero_le _, hwsort_len, hws1_len, fidScanArBvaqInv_init hslen,
         hw, fun _ h => by simp only [bv_c0] at h; omega, hm⟩)
    (fun Jq (nql, ncntd, qi, ticks, ()) ml hstate ihq => ?_)
  obtain ⟨ar, ws, ws1, ws2, ant, hqi_le, hnc_le, hws_l, hws1_l, hbvaq, hw_ar, hcntd_ok, hml⟩ :=
    hstate
  dsimp only [mkSt] at hml
  have har_l := hbvaq.1; have hws2_l := hbvaq.2.1; have hnql_le := hbvaq.2.2.1
  c0_hsplit
  · have hqi_lt := hc; clear hc
    have hqi1 : (qi + 1#32).toNat = qi.toNat + 1 := by c0_bound
    have hrqi : (row_off + qi).toNat = row_off.toNat + qi.toNat := by c0_bound
    have hrqi_sb : (BitVec.setWidth 64 (row_off + qi)).toNat < s.scratch.scratch_buf.length := by
      rw [bv64_setWidth_32, hrqi, hsb_len]; omega
    have hqw_ok := hrow_ok qi.toNat hqi_lt
    let qw := s.scratch.scratch_buf[row_off.toNat + qi.toNat]'(by omega)
    have hrqi_mod : (row_off.toNat + qi.toNat) % 2 ^ 32 = row_off.toNat + qi.toNat :=
      Nat.mod_eq_of_lt (by omega)
    have hqw_mod : s.scratch.scratch_buf[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by
        rw [hrqi_mod]; omega) = qw := by dsimp only [qw]; simp only [hrqi_mod]
    have hqw_getD : s.scratch.scratch_buf[row_off.toNat + qi.toNat]?.getD 0#32 = qw := by
      dsimp only [qw]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [hqw_getD] at hqw_ok
    fid_hfast_nogrp
    refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 64 ×
        List (BitVec 32) × List (BitVec 32) × List (BitVec 32) × List (BitVec 32) × BitVec 64)
      (fun ⟨nql_s, nc_s, ticks_s, _, _, _, _, _⟩ => (nql_s, nc_s, ticks_s, ()))
      (fun ⟨nql_s, nc_s, _ticks_s, ar_s, ws_s, ws1_s, ql_s, ant_s⟩ ms =>
        nc_s.toNat ≤ init_lits.toNat ∧ ws_s.length = 2 * c.max_vars ∧
        ws1_s.length = 2 * c.max_vars ∧ FidScanArBvaqInv c s ar_s ql_s 0 nql_s.toNat ∧
        FullWitnessInv c F0 F_cur { s.core with arena := ar_s } ∧
        (∀ i < nc_s.toNat, (ws1_s[i]?.getD 0#32).toNat < init_lits.toNat) ∧
        (FullMem c (mkSt ar_s s.core.lit_mark ws_s ws1_s ql_s ant_s) ⋆ R) ms)
      (fun _ ⟨nql_s, nc_s, _ticks_s, ar_s, ws_s, ws1_s, ql_s, ant_s⟩ ms
          ⟨hnc_s, hws_s_l, hws1_s_l, hbvaq_s, hw_s, hcntd_s, hms⟩ => ?_)
      (fun Js hJs => ?_)
    · clear hml
      dsimp only [mkSt] at hms
      have hql_s_l := hbvaq_s.2.1; have hnql_s_le := hbvaq_s.2.2.1
      fid_hfast
      · refine wp_loop_inv
          (fun (ci, ()) mci => ∃ arci,
            ci.toNat ≤ nql_s.toNat ∧ FidScanArBvaqInv c s arci ql_s ci.toNat nql_s.toNat ∧
            ∃ ant', (FullMem c (mkSt arci s.core.lit_mark ws_s ws1_s ql_s ant') ⋆ R) mci)
          (fun (ci, ()) _ => nql_s.toNat - ci.toNat)
          (fun Jc hJc => by
            fid_hfast; exact hJc (0#32, ()) m ⟨ar_s, Nat.zero_le _, hbvaq_s, _, hm⟩)
          (fun Jc (ci, ()) mci ⟨arci, hci_le, hbvaq_ci, ant', hmci⟩ ihc => ?_)
        clear hm; dsimp only [mkSt] at hmci
        have harci_l := hbvaq_ci.1
        c0_hsplit
        · have hci_lt : ci.toNat < nql_s.toNat := by assumption
          have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by simp only [bv_c0]; omega
          have hidx_ref := (hbvaq_ci.2.2.2.1 ci.toNat (Nat.le_refl _) hci_lt).1
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hidx_ref
          have hidx_wf := hw.arena.refs_wf _ hidx_ref
          have hstep := fidScanArBvaqInv_clear_step har_len hbvaq_ci hci_lt (by omega)
          have hci_ql : (BitVec.setWidth 64 ci).toNat < ql_s.length := by
            rw [hset, hql_s_l]; omega
          have hidx_ar : (BitVec.setWidth 64 (ql_s[(BitVec.setWidth 64 ci).toNat]'hci_ql)).toNat <
              arci.length := by
            simp only [hset]; have := hidx_wf.1; rw [harci_l]; have := hcl.arena_len_le; omega
          fid_hfast
          refine ihc (ci + 1#32, ()) m (by dsimp only; rw [hci1]; omega)
            ⟨_, by rw [hci1]; omega, by rw [hci1]; exact hstep, ant', ?_⟩
          simp only [hset] at hm; exact hm
        · have hci_eq : ci.toNat = nql_s.toNat := by omega
          rw [hci_eq] at hbvaq_ci
          have har_rest : arci = s.core.arena := fidScanArBvaqInv_done har_len hbvaq_ci
          rw [har_rest] at hmci; fid_hfast; exact hQ nc_s ws_s ws1_s ql_s ant' _
            ⟨hcl, { hsc with
              wsort_len := hws_s_l, work_stk1_len := hws1_s_l, work_stk2_len := hql_s_l }⟩
            hnc_s hcntd_s hmci
      · refine ihq (nql_s, nc_s, qi + 1#32, 0#64, ()) m (by dsimp only; rw [hqi1]; omega) ?_
        dsimp only [mkSt]
        exact ⟨ar_s, ws_s, ws1_s, ql_s, _, by rw [hqi1]; omega, hnc_s, hws_s_l, hws1_s_l,
          hbvaq_s, hw_s, hcntd_s, hm⟩
      · refine wp_loop_inv
          (fun (ci, ()) mci => ∃ arci,
            ci.toNat ≤ nql_s.toNat ∧ FidScanArBvaqInv c s arci ql_s ci.toNat nql_s.toNat ∧
            ∃ ant', (FullMem c (mkSt arci s.core.lit_mark ws_s ws1_s ql_s ant') ⋆ R) mci)
          (fun (ci, ()) _ => nql_s.toNat - ci.toNat)
          (fun Jc hJc => by
            fid_hfast; exact hJc (0#32, ()) m ⟨ar_s, Nat.zero_le _, hbvaq_s, _, hm⟩)
          (fun Jc (ci, ()) mci ⟨arci, hci_le, hbvaq_ci, ant', hmci⟩ ihc => ?_)
        clear hm; dsimp only [mkSt] at hmci
        have harci_l := hbvaq_ci.1
        c0_hsplit
        · have hci_lt : ci.toNat < nql_s.toNat := by assumption
          have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by simp only [bv_c0]; omega
          have hidx_ref := (hbvaq_ci.2.2.2.1 ci.toNat (Nat.le_refl _) hci_lt).1
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hidx_ref
          have hidx_wf := hw.arena.refs_wf _ hidx_ref
          have hstep := fidScanArBvaqInv_clear_step har_len hbvaq_ci hci_lt (by omega)
          have hci_ql : (BitVec.setWidth 64 ci).toNat < ql_s.length := by
            rw [hset, hql_s_l]; omega
          have hidx_ar : (BitVec.setWidth 64 (ql_s[(BitVec.setWidth 64 ci).toNat]'hci_ql)).toNat <
              arci.length := by
            simp only [hset]; have := hidx_wf.1; rw [harci_l]; have := hcl.arena_len_le; omega
          fid_hfast
          refine ihc (ci + 1#32, ()) m (by dsimp only; rw [hci1]; omega)
            ⟨_, by rw [hci1]; omega, by rw [hci1]; exact hstep, ant', ?_⟩
          simp only [hset] at hm; exact hm
        · have hci_eq : ci.toNat = nql_s.toNat := by omega
          rw [hci_eq] at hbvaq_ci
          have har_rest : arci = s.core.arena := fidScanArBvaqInv_done har_len hbvaq_ci
          rw [har_rest] at hmci; fid_hfast; exact hQ nc_s ws_s ws1_s ql_s ant' _
            ⟨hcl, { hsc with
              wsort_len := hws_s_l, work_stk1_len := hws1_s_l, work_stk2_len := hql_s_l }⟩
            hnc_s hcntd_s hmci
      · exact False.elim (hc trivial)
    · c0_hsplit
      · have hbin_ne : (qw &&& 0x80000000#32) ≠ 0#32 := by
          intro h; apply hc; rwa [← hqw_mod] at h
        clear hc
        rw [ite_eq_left hbin_ne] at hqw_ok
        let q := qw &&& 0x7FFFFFFF#32
        have hq_lt : q.toNat < 2 * s.core.cur_vars := hqw_ok
        have hbin := fid_scan_cands_bin_wp (Γ := Γ) (Q := Q) (X := X) hClines hslen hw hdw hil_le
          hws_l hws1_l hws2_l har_l hnc_le hcntd_ok
          (row_off := row_off) (cur_qn := cur_qn) (J := J) (Jq := Jq)
          (nql := nql) (ncntd := ncntd) (qi := qi) (ticks := ticks) (r_clines := r_clines)
          (qw := s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
            rw [hset, hrqi]; omega))
          (Js := Js)
          (by dsimp only [q] at hq_lt; simp only [hset, hrqi]; exact hq_lt)
          hml
          (fun nc ticks_b wsp ws1p mlp hncp_le hwsp_l hws1p_l hcntdp hmlp =>
            hJs ⟨nql, nc, ticks_b, ar, wsp, ws1p, ws2, ant⟩ mlp
              ⟨hncp_le, hwsp_l, hws1p_l, hbvaq, hw_ar, hcntdp, hmlp⟩)
        dsimp only [fidScanBin, fidScanHdr, sStep, sSteps, sStepZ, sStepsZ, sLd64, sLd32, sCall64,
          sThen, sElse, sGrpK4q, sGrpB4q, sGrpK3s, sGrpB4m, sGrpK4c, sGrpK5mp, sDummyVal, sDummyTup,
          full_bva_scan_cands_body] at hbin
        exact hbin
      · have hbin_eq : (qw &&& 0x80000000#32) = 0#32 := by
          have h1 : s.scratch.scratch_buf[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by
            rw [hrqi_mod]; omega) &&& 0x80000000#32 = 0#32 := hc
          rwa [hqw_mod] at h1
        rw [ite_eq_right (fun h' => h' hbin_eq)] at hqw_ok
        obtain ⟨hqw_ref, hqw_ng⟩ := hqw_ok
        clear hc
        have hqw_eq : s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
            rw [hset, hrqi]; omega) = qw := by dsimp only [qw]; simp only [hset, hrqi]
        have hlg := fid_scan_cands_large_wp (Γ := Γ) (Q := Q) (X := X) hClines hslen hw hdw hl0
          hil_le hlm_clr
          (row_off := row_off) (cur_qn := cur_qn)
          (J := fun _ _ => False) (Jq := fun _ _ => False)
          (nql := nql) (ncntd := ncntd) (qi := qi) (ticks := ticks) (r_clines := r_clines)
          (qw := s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
            rw [hset, hrqi]; omega))
          (Js := Js)
          (by simpa only [hqw_eq] using hqw_ref)
          (by simpa only [hqw_eq] using hqw_ng)
          hws_l hws1_l har_l hnc_le hbvaq hw_ar hcntd_ok hml
          (fun nql_j nc_j ticks_j ar_j ws_j ws1_j ql_j mj
              hnc_j hws_j_l hws1_j_l hbvaq_j hw_j hcntd_j hmj =>
            hJs ⟨nql_j, nc_j, ticks_j, ar_j, ws_j, ws1_j, ql_j, ant⟩ mj
              ⟨hnc_j, hws_j_l, hws1_j_l, hbvaq_j, hw_j, hcntd_j, hmj⟩)
        dsimp only [fidScanLarge, fidScanHdr, sStep, sSteps, sStepZ, sStepsZ, sLd64, sLd32, sCall64,
          sThen, sElse, sGrpK4q, sGrpB4q, sGrpK3s, sGrpB4m, sGrpK4c, sGrpK5mp, sDummyVal, sDummyTup,
          full_bva_scan_cands_body] at hlg
        exact hlg
  · clear hm
    c0_hsteps_nogrp
    refine wp_loop_inv
      (fun (ci, ()) mci => ∃ arci,
        ci.toNat ≤ nql.toNat ∧ FidScanArBvaqInv c s arci ws2 ci.toNat nql.toNat ∧
        (FullMem c (mkSt arci s.core.lit_mark ws ws1 ws2 ant) ⋆ R) mci)
      (fun (ci, ()) _ => nql.toNat - ci.toNat)
      (fun Jc hJc => by fid_hfast; exact hJc (0#32, ()) ml ⟨ar, Nat.zero_le _, hbvaq, hml⟩)
      (fun Jc (ci, ()) mci ⟨arci, hci_le, hbvaq_ci, hmci⟩ ihc => ?_)
    clear hml; dsimp only [mkSt] at hmci
    have harci_l := hbvaq_ci.1
    c0_hsplit
    · have hci_lt : ci.toNat < nql.toNat := by assumption
      have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by simp only [bv_c0]; omega
      have hidx_ref := (hbvaq_ci.2.2.2.1 ci.toNat (Nat.le_refl _) hci_lt).1
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hidx_ref
      have hidx_wf := hw.arena.refs_wf _ hidx_ref
      have hstep := fidScanArBvaqInv_clear_step har_len hbvaq_ci hci_lt (by omega)
      have hci_ws2 : (BitVec.setWidth 64 ci).toNat < ws2.length := by rw [hset, hws2_l]; omega
      have hidx_ar : (BitVec.setWidth 64 (ws2[(BitVec.setWidth 64 ci).toNat]'hci_ws2)).toNat <
          arci.length := by
        simp only [hset]; have := hidx_wf.1; rw [harci_l]; have := hcl.arena_len_le; omega
      fid_hfast
      refine ihc (ci + 1#32, ()) m (by dsimp only; rw [hci1]; omega)
        ⟨_, by rw [hci1]; omega, by rw [hci1]; exact hstep, ?_⟩
      simp only [hset] at hm; exact hm
    · have hci_eq : ci.toNat = nql.toNat := by omega
      rw [hci_eq] at hbvaq_ci
      have har_rest : arci = s.core.arena := fidScanArBvaqInv_done har_len hbvaq_ci
      rw [har_rest] at hmci; fid_hfast; exact hQ ncntd ws ws1 ws2 ant _
        ⟨hcl, { hsc with wsort_len := hws_l, work_stk1_len := hws1_l, work_stk2_len := hws2_l }⟩
        hnc_le hcntd_ok hmci

end LeanQbe.T.Examples.Kissat.FullFidelityBva
