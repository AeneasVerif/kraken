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

set_option autoImplicit false

local macro "fid_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

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

/-! ## 1. `FidFilterArBvaqInv` & Pure Row-Update Helpers -/

private theorem bva_bin_swap_entails {F_cur : List (List Nat)} {a b : Nat}
    (h : (cnfOfClauses F_cur).EntailsClause (cnfClause [a, b])) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [b, a]) :=
  clause_entails_of_perm (List.Perm.swap b a []) h

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

/-- `PH_BVA_Q` tracking invariant for `full_bva_filter_row` on `sb[nrow_off+lo ..< nrow_off+hi)`. -/
private def FidFilterArBvaqInv (c : FullCfg) (s : FullState) (ar sb : List (BitVec 32))
    (nrow_off lo hi max_new : Nat) : Prop :=
  ar.length = c.arena_cap ∧ sb.length = c.scratch_cap ∧ hi ≤ max_new ∧
  (∀ nm, lo ≤ nm → nm < hi →
    let dr := sb[nrow_off + nm]?.getD 0#32
    (dr &&& 0x80000000#32) = 0#32 →
      dr.toNat ∈ fullArenaClauseRefsCore s.core ∧
      (s.core.arena[dr.toNat]?.getD 0#32 &&& 0x02000000#32) = 0#32) ∧
  ∀ i < c.arena_cap, ar[i]? = s.core.arena[i]? ∨
    (∃ nm, lo ≤ nm ∧ nm < hi ∧
      let dr := sb[nrow_off + nm]?.getD 0#32
      (dr &&& 0x80000000#32) = 0#32 ∧ dr.toNat = i ∧
      (s.core.arena[i]?.getD 0#32 &&& 0x02000000#32) = 0#32 ∧
      ar[i]? = some (s.core.arena[i]?.getD 0#32 ||| 0x02000000#32))

private theorem fidFilterArBvaqInv_init {c : FullCfg} {s : FullState} (hslen : s.LengthsOk c)
    (nrow_off max_new : Nat) :
        FidFilterArBvaqInv c s s.core.arena s.scratch.scratch_buf nrow_off 0 0 max_new :=
  ⟨hslen.core_ok.arena_len_arr, hslen.scratch_ok.scratch_buf_len, Nat.zero_le _,
   fun _ _ h => by omega, fun _ _ => Or.inl rfl⟩

private theorem fidFilterArBvaqInv_congr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {ar sb : List (BitVec 32)} {nrow_off lo hi max_new : Nat}
    (h : FidFilterArBvaqInv c s ar sb nrow_off lo hi max_new) :
    fullArenaClauseRefsCore { s.core with arena := ar } = fullArenaClauseRefsCore s.core ∧
    (∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore { s.core with arena := ar } r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseSizeCore { s.core with arena := ar } r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseLitsCore { s.core with arena := ar } r = fullArenaClauseLitsCore s.core r) :=
  fidArBvaq_congr hcl hw fun i hi => by
    rcases h.2.2.2.2 i hi with heq | ⟨nm, hlo, hhi, hbin, hidx, _, hset⟩
    · exact Or.inl heq
    · have href := (h.2.2.2.1 nm hlo hhi hbin).1
      rw [hidx] at href; exact Or.inr ⟨href, hset⟩

private theorem fid_filter_row_ar_lits_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {ar sb : List (BitVec 32)} {nrow_off nqn max_new : Nat}
    (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hbvaq : FidFilterArBvaqInv c s ar sb nrow_off 0 nqn max_new)
    {r : Nat} (hr : r ∈ fullArenaClauseRefsCore s.core) :
    ∀ j < fullArenaClauseSizeCore s.core r, ar[r + 3 + j]? = s.core.arena[r + 3 + j]? := by
  intro j hj
  have hwf := hw.arena.refs_wf r hr; have hal := hcl.arena_len_le
  rcases hbvaq.2.2.2.2 (r + 3 + j) (by omega) with heq | ⟨nm, h0, hnm, h0b, hidx, _, _⟩
  · exact heq
  · exfalso
    have hnm_ref := (hbvaq.2.2.2.1 nm h0 hnm h0b).1
    rw [hidx] at hnm_ref
    have := fullArenaScanRefs_disjoint hr hnm_ref (by omega); omega

private theorem fidFilterArBvaqInv_push_bin {c : FullCfg} {s : FullState} {ar sb : List (BitVec 32)}
    {nrow_off par_off nqn max_new : Nat} (h : FidFilterArBvaqInv c s ar sb nrow_off 0 nqn max_new)
    (hnqn : nqn < max_new) (hdisj : nrow_off + max_new ≤ par_off)
      (hpar : par_off + max_new ≤ c.scratch_cap)
    {qw qi : BitVec 32} (hbin : (qw &&& 0x80000000#32) ≠ 0#32) :
    FidFilterArBvaqInv c s ar ((sb.set (nrow_off + nqn) qw).set (par_off + nqn) qi)
      nrow_off 0 (nqn + 1) max_new := by
  obtain ⟨har, hsb, hhi, hdom, hall⟩ := h
  refine ⟨har, by simp [hsb], by omega, fun nm h0 hnm => ?_, fun i hi => ?_⟩
  · dsimp only; intro h0b
    by_cases hne : nm = nqn
    · subst hne
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
        Option.getD_some] at h0b
      exact absurd h0b hbin
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)] at h0b ⊢
      exact hdom nm h0 (by omega) h0b
  · rcases hall i hi with heq | ⟨nm, h0, hnm, h0b, hidx, h0v, hset⟩
    · exact Or.inl heq
    · refine Or.inr ⟨nm, h0, by omega, ?_, ?_, h0v, hset⟩
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact h0b
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hidx

private theorem fidFilterArBvaqInv_push_large {c : FullCfg} {s : FullState} {ar sb :
    List (BitVec 32)}
    {nrow_off par_off nqn max_new : Nat} (h : FidFilterArBvaqInv c s ar sb nrow_off 0 nqn max_new)
    (hnqn : nqn < max_new) (hdisj : nrow_off + max_new ≤ par_off)
      (hpar : par_off + max_new ≤ c.scratch_cap)
    {dr qi : BitVec 32} (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hdr_lt : dr.toNat < c.arena_cap) (hdr_bin : (dr &&& 0x80000000#32) = 0#32)
    (hdr_nbvaq : (ar[dr.toNat]'(by rw [h.1]; exact hdr_lt) &&& 0x02000000#32) = 0#32) :
    FidFilterArBvaqInv c s
      (ar.set dr.toNat ((ar[dr.toNat]'(by rw [h.1]; exact hdr_lt)) ||| 0x02000000#32))
      ((sb.set (nrow_off + nqn) dr).set (par_off + nqn) qi)
      nrow_off 0 (nqn + 1) max_new := by
  obtain ⟨har, hsb, hhi, hdom, hall⟩ := h
  have horig : ar[dr.toNat]? = s.core.arena[dr.toNat]? := by
    rcases hall dr.toNat hdr_lt with heq | ⟨_, _, _, _, _, h0v, hset⟩
    · exact heq
    · rw [List.getElem?_eq_getElem (by omega)] at hset
      have hval := Option.some.inj hset
      have h1 : ((s.core.arena[dr.toNat]?.getD 0#32 ||| 0x02000000#32) &&& 0x02000000#32) =
          0x02000000#32 := by
        rw [BitVec.and_or_distrib_right,
          show (0x02000000#32 &&& 0x02000000#32) = 0x02000000#32 from rfl, h0v, BitVec.zero_or]
      rw [hval] at hdr_nbvaq
      exact absurd (hdr_nbvaq.symm.trans h1) (by decide)
  have hs_nbvaq : (s.core.arena[dr.toNat]?.getD 0#32 &&& 0x02000000#32) = 0#32 := by
    rw [← horig, List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hdr_nbvaq
  refine ⟨by simp [har], by simp [hsb], by omega, fun nm h0 hnm => ?_, fun i hi => ?_⟩
  · dsimp only; intro h0b
    by_cases hne : nm = nqn
    · subst hne
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
      exact ⟨hdr_ref, hs_nbvaq⟩
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)] at h0b ⊢
      exact hdom nm h0 (by omega) h0b
  · by_cases hid : i = dr.toNat
    · subst hid
      refine Or.inr ⟨nqn, Nat.zero_le _, by omega, ?_, ?_, hs_nbvaq, ?_⟩
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
        exact hdr_bin
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
      · rw [List.getElem?_set_self (by omega)]
        have har_eq : ar[dr.toNat]'(by omega) = s.core.arena[dr.toNat]?.getD 0#32 := by
          rw [← horig, List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [har_eq]
    · rw [List.getElem?_set_ne (Ne.symm hid)]
      rcases hall i hi with heq | ⟨nm, h0, hnm, h0b, hidx, h0v, hset⟩
      · exact Or.inl heq
      · refine Or.inr ⟨nm, h0, by omega, ?_, ?_, h0v, hset⟩
        · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact h0b
        · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hidx

private theorem fidFilterArBvaqInv_clear_bin {c : FullCfg} {s : FullState} {ar sb :
    List (BitVec 32)}
    {nrow_off qi nqn max_new : Nat} (h : FidFilterArBvaqInv c s ar sb nrow_off qi nqn max_new)
      (hqi : qi < nqn)
    (hbin : (sb[nrow_off + qi]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32) :
    FidFilterArBvaqInv c s ar sb nrow_off (qi + 1) nqn max_new := by
  obtain ⟨har, hsb, hhi, hdom, hall⟩ := h
  refine ⟨har, hsb, hhi, fun nm h1 h2 => hdom nm (by omega) h2, fun i hi => ?_⟩
  rcases hall i hi with heq | ⟨nm, h1, h2, h0b, hidx, h0v, hset⟩
  · exact Or.inl heq
  · have hne : nm ≠ qi := fun he => by subst he; exact hbin h0b
    exact Or.inr ⟨nm, by omega, h2, h0b, hidx, h0v, hset⟩

private theorem fidFilterArBvaqInv_clear_large {c : FullCfg} {s : FullState} {ar sb :
    List (BitVec 32)}
    {nrow_off qi nqn max_new : Nat} (hs_ar : s.core.arena.length = c.arena_cap)
    (h : FidFilterArBvaqInv c s ar sb nrow_off qi nqn max_new) (hqi : qi < nqn)
    (hqr : nrow_off + qi < sb.length)
    (h0b : (sb[nrow_off + qi]'hqr &&& 0x80000000#32) = 0#32)
    (hdr_lt : (sb[nrow_off + qi]'hqr).toNat < c.arena_cap) :
    let dr := (sb[nrow_off + qi]'hqr).toNat
    FidFilterArBvaqInv c s
      (ar.set dr ((ar[dr]'(by rw [h.1]; exact hdr_lt)) &&& ~~~0x02000000#32))
      sb nrow_off (qi + 1) nqn max_new := by
  obtain ⟨har, hsb, hhi, hdom, hall⟩ := h
  intro dr
  have hdr_eq : (sb[nrow_off + qi]?.getD 0#32).toNat = dr := by
    rw [List.getElem?_eq_getElem hqr, Option.getD_some]
  have h0b' : (sb[nrow_off + qi]?.getD 0#32 &&& 0x80000000#32) = 0#32 := by
    rw [List.getElem?_eq_getElem hqr, Option.getD_some]; exact h0b
  have hdr_s0 : (s.core.arena[dr]?.getD 0#32 &&& 0x02000000#32) = 0#32 := by
    have := (hdom qi (Nat.le_refl _) hqi h0b').2; rwa [hdr_eq] at this
  have har_clr : ((ar[dr]'(by omega)) &&& ~~~0x02000000#32) = s.core.arena[dr]?.getD 0#32 := by
    rcases hall dr hdr_lt with heq | ⟨_, _, _, _, _, _, hset⟩
    · have : ar[dr]'(by omega) = s.core.arena[dr]?.getD 0#32 := by
        rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [this]; exact fid_bv32_clear_bvaq_of_zero hdr_s0
    · rw [List.getElem?_eq_getElem (by omega)] at hset
      rw [Option.some.inj hset]; exact fid_bv32_bvaq_roundtrip hdr_s0
  refine ⟨by simp [har], hsb, hhi, fun nm h1 h2 => hdom nm (by omega) h2, fun i hi => ?_⟩
  by_cases hid : i = dr
  · subst hid; left
    rw [List.getElem?_set_self (by omega), har_clr,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  · rw [List.getElem?_set_ne (Ne.symm hid)]
    rcases hall i hi with heq | ⟨nm, h1, h2, hnb, hidx, h0v, hset⟩
    · exact Or.inl heq
    · have hne : nm ≠ qi := fun he => by subst he; rw [hdr_eq] at hidx; exact hid hidx.symm
      exact Or.inr ⟨nm, by omega, h2, hnb, hidx, h0v, hset⟩

private theorem fidFilterArBvaqInv_done {c : FullCfg} {s : FullState} {ar sb : List (BitVec 32)}
    {nrow_off nqn max_new : Nat} (hs_ar : s.core.arena.length = c.arena_cap)
    (h : FidFilterArBvaqInv c s ar sb nrow_off nqn nqn max_new) : ar = s.core.arena := by
  apply list_eq_of_getElem?_eq (by rw [h.1, hs_ar])
  intro i hi
  rcases h.2.2.2.2 i (by omega) with heq | ⟨nm, h1, h2, _⟩
  · exact heq
  · omega

private theorem fid_scan_cands_lmj_lift {c : FullCfg} {ar : List (BitVec 32)}
    {lm0 lmj : List (BitVec 8)} {qw j csz : Nat}
    (h : LmBit2Inv c ar lm0 qw 0 j lmj) (_hj : j ≤ csz) :
    LmBit2Inv c ar lm0 qw 0 csz lmj :=
  ⟨h.1, fun l hl => by
    rcases h.2 l hl with heq | ⟨k, h0, hk, har', hset'⟩
    · exact Or.inl heq
    · exact Or.inr ⟨k, h0, by omega, har', hset'⟩⟩

private theorem fid_filter_row_bin_upd {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {ar sb : List (BitVec 32)}
    {row_off nrow_off par_off cur_qn nqn qi qw best_lit : BitVec 32}
    {res : List Nat} {step max_new : Nat}
    (hsb_l : sb.length = c.scratch_cap)
    (hbvaq : FidFilterArBvaqInv c s ar sb nrow_off.toNat 0 nqn.toNat max_new)
    (hnqn_lt : nqn.toNat < max_new)
    (_hnr_bd : nrow_off.toNat + max_new ≤ c.scratch_cap)
    (hpr_bd : par_off.toNat + max_new ≤ c.scratch_cap)
    (hdisj : nrow_off.toNat + max_new ≤ par_off.toNat)
    (hbin_ne : (qw &&& 0x80000000#32) ≠ 0#32)
    (hq_lt : (qw &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars)
    (hres_eq : res = [(qw &&& 0x7FFFFFFF#32).toNat])
    (hfr_q : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat,
        (qw &&& 0x7FFFFFFF#32).toNat]))
    (hbl_q_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [best_lit.toNat, (qw &&& 0x7FFFFFFF#32).toNat]))
    (hqi_lt : qi.toNat < cur_qn.toNat)
    (hres_lt : ∀ x ∈ res, x < 2 * s.core.cur_vars)
    (hres_nd : (res.map (· / 2)).Nodup)
    (hres_ent : ∀ t < step, (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res)))
    (hqw_getD : s.scratch.scratch_buf[row_off.toNat + qi.toNat]?.getD 0#32 = qw)
    (hfr_sb : ∀ idx < c.scratch_cap,
      ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + max_new) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + max_new) →
      sb[idx]? = s.scratch.scratch_buf[idx]?)
    (hent : ∀ nm < nqn.toNat,
      let pi := (sb[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧ ∃ res' : List Nat,
        (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
        FidBvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
        FidBvaRowEntryOk F_cur s best_lit.toNat (sb[nrow_off.toNat + nm]?.getD 0#32) res' ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res'))) :
    let sb1 := (sb.set (nrow_off.toNat + nqn.toNat) qw).set (par_off.toNat + nqn.toNat) qi
    FidFilterArBvaqInv c s ar sb1 nrow_off.toNat 0 (nqn.toNat + 1) max_new ∧
    (∀ idx < c.scratch_cap,
      ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + max_new) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + max_new) →
      sb1[idx]? = s.scratch.scratch_buf[idx]?) ∧
    (∀ nm < nqn.toNat + 1,
      let pi := (sb1[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧ ∃ res' : List Nat,
        (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
        FidBvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
        FidBvaRowEntryOk F_cur s best_lit.toNat (sb1[nrow_off.toNat + nm]?.getD 0#32) res' ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res'))) := by
  let sb1 := (sb.set (nrow_off.toNat + nqn.toNat) qw).set (par_off.toNat + nqn.toNat) qi
  refine ⟨fidFilterArBvaqInv_push_bin hbvaq hnqn_lt hdisj hpr_bd hbin_ne, ?_, ?_⟩
  · intro idx hidx hnot1 hnot2
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hfr_sb idx hidx hnot1 hnot2
  · intro nm hnm
    by_cases hne : nm = nqn.toNat
    · subst hne
      have hpi_eq : (sb1[par_off.toNat + nqn.toNat]?.getD 0#32).toNat = qi.toNat := by
        dsimp only [sb1]; rw [List.getElem?_set_self (by simp [hsb_l]; omega)]; rfl
      have hnr_eq : sb1[nrow_off.toNat + nqn.toNat]?.getD 0#32 = qw := by
        dsimp only [sb1]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
      refine ⟨by rw [hpi_eq]; exact hqi_lt, res, hres_lt, hres_nd, ?_, ?_, hres_ent, ?_⟩
      · rw [hpi_eq, hqw_getD]; unfold FidBvaRowEntryOk; rw [ite_eq_left hbin_ne]
        exact ⟨hq_lt, hres_eq, hfr_q⟩
      · rw [hnr_eq]; unfold FidBvaRowEntryOk; rw [ite_eq_left hbin_ne]
        exact ⟨hq_lt, hres_eq, hbl_q_ent⟩
      · rw [hres_eq]; exact hbl_q_ent
    · have hpi_eq : sb1[par_off.toNat + nm]? = sb[par_off.toNat + nm]? := by
        dsimp only [sb1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      have hnr_eq : sb1[nrow_off.toNat + nm]? = sb[nrow_off.toNat + nm]? := by
        dsimp only [sb1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      dsimp only; rw [hpi_eq, hnr_eq]; exact hent nm (by omega)

private theorem fid_filter_row_mark_step {c : FullCfg} {s : FullState}
    {ar : List (BitVec 32)} {lmj : List (BitVec 8)} {qw j : BitVec 32}
    {res : List Nat} {step : Nat}
    (hlm_len : s.core.lit_mark.length = 2 * c.max_vars)
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hfr_b0 : (s.core.lit_mark[(s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat]?.getD 0#8 &&&
      1#8) ≠ 0#8)
    (hres_perm_f : res.Perm ((fullArenaClauseLitsCore s.core qw.toNat).filter
      (· != (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat)))
    (hlmj_inv : LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 j.toNat lmj)
    (hlmj_res : ∀ l < 2 * s.core.cur_vars, (lmj[l]?.getD 0#8 &&& 2#8) ≠ 0#8 → l ∈ res)
    (hqwj_ar : qw.toNat + 3 + j.toNat < ar.length)
    (hqwj_s : qw.toNat + 3 + j.toNat < s.core.arena.length)
    (hl_eq : ar[qw.toNat + 3 + j.toNat]'hqwj_ar = s.core.arena[qw.toNat + 3 + j.toNat]'hqwj_s)
    (hl_mem : (s.core.arena[qw.toNat + 3 + j.toNat]'hqwj_s).toNat ∈
      fullArenaClauseLitsCore s.core qw.toNat)
    (hl_lt : (ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat < 2 * s.core.cur_vars)
    (hb0_32 : (BitVec.setWidth 32 (lmj[(ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat]'(by
      rw [hlmj_inv.1]; omega)) &&& BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 1)) =
      BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0)) :
    let l := (ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat
    let lm1 := lmj.set l ((lmj[l]'(by rw [hlmj_inv.1]; omega)) ||| 2#8)
    LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 (j.toNat + 1) lm1 ∧
    (∀ x < 2 * s.core.cur_vars, (lm1[x]?.getD 0#8 &&& 2#8) ≠ 0#8 → x ∈ res) := by
  have hlmj_l := hlmj_inv.1
  have hl_b0_zero :
      (s.core.lit_mark[(ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat]?.getD 0#8 &&& 1#8) = 0#8 := by
    rw [← lmBit2Inv_preserves_bit0 hlmj_inv (by omega),
      List.getElem?_eq_getElem (by omega), Option.getD_some]
    apply BitVec.eq_of_toNat_eq
    have h0' := congrArg BitVec.toNat hb0_32; simp only [BitVec.toNat_and, BitVec.toNat_setWidth,
      show (BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 1)).toNat = 1 from rfl,
      show (BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0)).toNat = 0 from rfl,
      show (1#8 : BitVec 8).toNat = 1 from rfl, show (0#8 : BitVec 8).toNat = 0 from rfl] at h0' ⊢
    have hlt8 := (lmj[(ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat]'(by omega)).isLt
    rwa [Nat.mod_eq_of_lt (Nat.lt_trans hlt8 (by decide))] at h0'
  have hl_ne_fr : (ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat ≠
      (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat := fun heq => by
    rw [heq] at hl_b0_zero; exact hfr_b0 hl_b0_zero
  have hl_in_res : (ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat ∈ res := by
    apply hres_perm_f.mem_iff.mpr; rw [List.mem_filter]
    exact ⟨by rw [hl_eq]; exact hl_mem, bne_iff_ne.mpr hl_ne_fr⟩
  have hl_lt_s : (s.core.arena[qw.toNat + 3 + j.toNat]'hqwj_s).toNat < 2 * c.max_vars := by
    rw [← hl_eq]; omega
  have hstep2 : LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 (j.toNat + 1)
      (lmj.set (ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat
        ((lmj[(ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat]'(by omega)) ||| 2#8)) := by
    have h0 := lmBit2Inv_or2 hlm_len hlmj_inv hqwj_s hl_lt_s
    simpa only [← hl_eq] using h0
  refine ⟨hstep2, fun x hx hne => ?_⟩
  by_cases hle : x = (ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat
  · rw [hle]; exact hl_in_res
  · rw [List.getElem?_set_ne (Ne.symm hle)] at hne; exact hlmj_res x hx hne

private theorem fid_filter_row_large_upd {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {ar sb : List (BitVec 32)} {lmj : List (BitVec 8)}
    {row_off nrow_off par_off cur_qn nqn qi qw dr best_lit : BitVec 32}
    {res : List Nat} {step max_new : Nat}
    (hcl : s.core.LengthsOk c) (har_l : ar.length = c.arena_cap)
    (hsb_l : sb.length = c.scratch_cap)
    (hw_ar : FullWitnessInv c F0 F_cur { s.core with arena := ar })
    (hnd_ar : FullArenaVarsNodup
      (FullState.mk { s.core with arena := ar } { s.scratch with scratch_buf := sb }))
    (hl0 : s.core.cur_level = 0)
    (hbvaq : FidFilterArBvaqInv c s ar sb nrow_off.toNat 0 nqn.toNat max_new)
    (hnqn_lt : nqn.toNat < max_new)
    (_hnr_bd : nrow_off.toNat + max_new ≤ c.scratch_cap)
    (hpr_bd : par_off.toNat + max_new ≤ c.scratch_cap)
    (hdisj : nrow_off.toNat + max_new ≤ par_off.toNat)
    (hrefs_ar : fullArenaClauseRefsCore { s.core with arena := ar } =
      fullArenaClauseRefsCore s.core)
    (hqw_ref : qw.toNat ∈ fullArenaClauseRefsCore s.core)
    (hqw_ng : fullArenaClauseGarbCore s.core qw.toNat = false)
    (hqw_sz3 : 3 ≤ fullArenaClauseSizeCore s.core qw.toNat)
    (hqw_sz5 : fullArenaClauseSizeCore s.core qw.toNat ≤ 5)
    (hqw_sz_ar : fullArenaClauseSizeCore { s.core with arena := ar } qw.toNat =
      fullArenaClauseSizeCore s.core qw.toNat)
    (hfr_mem : (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat ∈
      fullArenaClauseLitsCore s.core qw.toNat)
    (hres_perm_f : res.Perm ((fullArenaClauseLitsCore s.core qw.toNat).filter
      (· != (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat)))
    (hqw_perm : (fullArenaClauseLits s qw.toNat).Perm
      ((s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat :: res))
    (hbin_eq : (qw &&& 0x80000000#32) = 0#32)
    (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hdr_lt_ar : dr.toNat + 3 ≤ ar.length)
    (hdr_ng_s : fullArenaClauseGarbCore { s.core with arena := ar } dr.toNat =
      fullArenaClauseGarbCore s.core dr.toNat)
    (hdr_sz_s : fullArenaClauseSizeCore { s.core with arena := ar } dr.toNat =
      fullArenaClauseSizeCore s.core dr.toNat)
    (hdr_lits_s : fullArenaClauseLitsCore { s.core with arena := ar } dr.toNat =
      fullArenaClauseLitsCore s.core dr.toNat)
    (hdr_ng_ar : fullArenaClauseGarb
      (FullState.mk { s.core with arena := ar, lit_mark := lmj }
        { s.scratch with scratch_buf := sb }) dr.toNat = false)
    (hdr_nbvaq_h : (fullArenaHdr
      (FullState.mk { s.core with arena := ar, lit_mark := lmj }
        { s.scratch with scratch_buf := sb }) dr.toNat &&& 0x02000000#32) = 0#32)
    (hdr_sz_eq_ar : fullArenaClauseSize
      (FullState.mk { s.core with arena := ar, lit_mark := lmj }
        { s.scratch with scratch_buf := sb }) dr.toNat =
      fullArenaClauseSize
      (FullState.mk { s.core with arena := ar, lit_mark := lmj }
        { s.scratch with scratch_buf := sb }) qw.toNat)
    (hbl_mem_ar : best_lit.toNat ∈ fullArenaClauseLits
      (FullState.mk { s.core with arena := ar, lit_mark := lmj }
        { s.scratch with scratch_buf := sb }) dr.toNat)
    (hdr_perm_ar : (fullArenaClauseLits
      (FullState.mk { s.core with arena := ar, lit_mark := lmj }
        { s.scratch with scratch_buf := sb }) dr.toNat).Perm (best_lit.toNat :: res))
    (hdr_filt_ar : ((fullArenaClauseLits
      (FullState.mk { s.core with arena := ar, lit_mark := lmj }
        { s.scratch with scratch_buf := sb }) dr.toNat).filter
      (· != best_lit.toNat)).Perm res)
    (hbl_res_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res)))
    (hqi_lt : qi.toNat < cur_qn.toNat)
    (hres_lt : ∀ x ∈ res, x < 2 * s.core.cur_vars)
    (hres_nd : (res.map (· / 2)).Nodup)
    (hres_ent : ∀ t < step, (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res)))
    (hqw_getD : s.scratch.scratch_buf[row_off.toNat + qi.toNat]?.getD 0#32 = qw)
    (hfr_sb : ∀ idx < c.scratch_cap,
      ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + max_new) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + max_new) →
      sb[idx]? = s.scratch.scratch_buf[idx]?)
    (hent : ∀ nm < nqn.toNat,
      let pi := (sb[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧ ∃ res' : List Nat,
        (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
        FidBvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
        FidBvaRowEntryOk F_cur s best_lit.toNat (sb[nrow_off.toNat + nm]?.getD 0#32) res' ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res')))
    (hhar_b : c.arena_cap < 2 * dimacsBound) :
    let ar1 := ar.set dr.toNat ((ar[dr.toNat]'(by omega)) ||| 0x02000000#32)
    let sb1 := (sb.set (nrow_off.toNat + nqn.toNat) dr).set (par_off.toNat + nqn.toNat) qi
    FidFilterArBvaqInv c s ar1 sb1 nrow_off.toNat 0 (nqn.toNat + 1) max_new ∧
    FullWitnessInv c F0 F_cur { s.core with arena := ar1 } ∧
    FullArenaVarsNodup
      (FullState.mk { s.core with arena := ar1 } { s.scratch with scratch_buf := sb1 }) ∧
    (∀ idx < c.scratch_cap,
      ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + max_new) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + max_new) →
      sb1[idx]? = s.scratch.scratch_buf[idx]?) ∧
    (∀ nm < nqn.toNat + 1,
      let pi := (sb1[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧ ∃ res' : List Nat,
        (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
        FidBvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
        FidBvaRowEntryOk F_cur s best_lit.toNat (sb1[nrow_off.toNat + nm]?.getD 0#32) res' ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res'))) := by
  unfold dimacsBound at hhar_b
  have hcl_ar : ({ s.core with arena := ar }).LengthsOk c := { hcl with arena_len_arr := har_l }
  have hdr_nbvaq_ar : (ar[dr.toNat]'(by omega) &&& 0x02000000#32) = 0#32 := by
    change (fullArenaHdrCore { s.core with arena := ar } dr.toNat &&& 0x02000000#32) = 0#32
      at hdr_nbvaq_h
    unfold fullArenaHdrCore at hdr_nbvaq_h
    dsimp only at hdr_nbvaq_h
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdr_nbvaq_h
  have hdr_bin : (dr &&& 0x80000000#32) = 0#32 := fid_bv32_bin_flag_zero_of_lt (by omega)
  let ar1 := ar.set dr.toNat ((ar[dr.toNat]'(by omega)) ||| 0x02000000#32)
  let sb1 := (sb.set (nrow_off.toNat + nqn.toNat) dr).set (par_off.toNat + nqn.toNat) qi
  have hbvaq1 : FidFilterArBvaqInv c s ar1 sb1 nrow_off.toNat 0 (nqn.toNat + 1) max_new :=
    fidFilterArBvaqInv_push_large hbvaq hnqn_lt (by omega) (by omega)
      hdr_ref (by omega) hdr_bin hdr_nbvaq_ar
  have hdr_ref_ar : dr.toNat ∈ fullArenaClauseRefsCore { s.core with arena := ar } := by
    rw [hrefs_ar]; exact hdr_ref
  have ⟨_, _, hw1, _⟩ := fullWitnessInv_set_hdr_bit20
    hcl_ar hw_ar hl0 hdr_ref_ar
    ((ar[dr.toNat]'(by omega)) ||| 0x02000000#32)
    (by unfold fullArenaHdrCore; dsimp only
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact fid_bv32_or_bvaq_garb _)
    (by unfold fullArenaHdrCore; dsimp only
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact fid_bv32_or_bvaq_shrk _)
  have hnd1 : FullArenaVarsNodup
      (FullState.mk { s.core with arena := ar1 } { s.scratch with scratch_buf := sb1 }) :=
    fullArenaVarsNodup_of_bit20
      (s := FullState.mk { s.core with arena := ar } { s.scratch with scratch_buf := sb1 })
      hcl_ar hw_ar hl0 hnd_ar hdr_ref_ar
      (by unfold fullArenaHdrCore; dsimp only
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact fid_bv32_or_bvaq_garb _)
      (by unfold fullArenaHdrCore; dsimp only
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact fid_bv32_or_bvaq_shrk _)
  refine ⟨hbvaq1, hw1, hnd1, ?_, ?_⟩
  · intro idx hidx hnot1 hnot2
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hfr_sb idx hidx hnot1 hnot2
  · intro nm hnm
    by_cases hne : nm = nqn.toNat
    · subst hne
      have hpi_eq : (sb1[par_off.toNat + nqn.toNat]?.getD 0#32).toNat = qi.toNat := by
        dsimp only [sb1]; rw [List.getElem?_set_self (by simp [hsb_l]; omega)]; rfl
      have hnr_eq : sb1[nrow_off.toNat + nqn.toNat]?.getD 0#32 = dr := by
        dsimp only [sb1]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
      refine ⟨by rw [hpi_eq]; exact hqi_lt, res, hres_lt, hres_nd, ?_, ?_, hres_ent, hbl_res_ent⟩
      · rw [hpi_eq, hqw_getD]; unfold FidBvaRowEntryOk
        rw [ite_eq_right (fun h' => h' hbin_eq)]
        exact ⟨hqw_ref, hqw_ng, hqw_sz3, hqw_sz5, hfr_mem, hres_perm_f, hqw_perm⟩
      · rw [hnr_eq]; unfold FidBvaRowEntryOk; rw [ite_eq_right (fun h' => h' hdr_bin)]
        change fullArenaClauseGarbCore { s.core with arena := ar } dr.toNat = false at hdr_ng_ar
        change fullArenaClauseSizeCore { s.core with arena := ar } dr.toNat =
          fullArenaClauseSizeCore { s.core with arena := ar } qw.toNat at hdr_sz_eq_ar
        change best_lit.toNat ∈ fullArenaClauseLitsCore { s.core with arena := ar } dr.toNat
          at hbl_mem_ar
        change (fullArenaClauseLitsCore { s.core with arena := ar } dr.toNat).Perm _ at hdr_perm_ar
        change ((fullArenaClauseLitsCore { s.core with arena := ar } dr.toNat).filter _).Perm _
          at hdr_filt_ar
        rw [hdr_ng_s] at hdr_ng_ar
        rw [hdr_sz_s, hqw_sz_ar] at hdr_sz_eq_ar
        rw [hdr_lits_s] at hbl_mem_ar hdr_perm_ar hdr_filt_ar
        unfold fullArenaClauseSize
        exact ⟨hdr_ref, hdr_ng_ar, by omega, by omega, hbl_mem_ar, hdr_filt_ar.symm, hdr_perm_ar⟩
    · have hpi_eq : sb1[par_off.toNat + nm]? = sb[par_off.toNat + nm]? := by
        dsimp only [sb1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      have hnr_eq : sb1[nrow_off.toNat + nm]? = sb[nrow_off.toNat + nm]? := by
        dsimp only [sb1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      dsimp only; rw [hpi_eq, hnr_eq]; exact hent nm (by omega)

/-! ## 2. `full_bva_filter_row_fid_wp` Proof -/

public theorem full_bva_filter_row_fid_wp (Γ : Env)
    (hClines : ∀ a m Q X, fidBvaClinesSpec a m Q X →
      Γ "full_bva_clines_fid" [i64] [i64] a m Q X)
    (hMatchLarge : ∀ a m Q X, fidBvaMatchLargeBvaSpec a m Q X →
      Γ "full_bva_match_large_bva_fid" [i64, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fidBvaFilterRowSpec a m Q X →
      Func.wp Γ full_bva_filter_row_body a m Q X := by
  rintro ⟨h, row_off, nrow_off, par_off, cur_qn, best_lit, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, step, bump, rfl, hslen, hw, hnodup, hext, hl0, hdm,
     hsc_pos, hstep1, hstep_sc, hrow_eq, hqn_eq, hnrow_eq, hnr_le_pr, hpr_cap,
     hbl_lt, hmat, hlm_clr, hlm_b0, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcl := hslen.core_ok; have hsc := hslen.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr
  have har_len := hcl.arena_len_arr; have hal_le := hcl.arena_len_le; have hwlen_le := hcl.wlen_le
  have hlm_len := hcl.lit_mark_len; have hsb_len := hsc.scratch_buf_len
  have hrepr_len := hcl.repr_len
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  have hdw : DenseWatchesInv F_cur s.core := by
    have h1 := hw.watches; unfold ModeWatchesInv at h1; rwa [ite_eq_right hdm] at h1
  let sc := fidStepsCap c.scratch_cap
  have hstep_prev := hmat.2.2.2.2.2 (step - 1) (by omega)
  obtain ⟨hfr_lt, hro_ge, hqn_ge, hro_qn_le, _, hrow_entries⟩ := hstep_prev
  have hfr_b0 :
      (s.core.lit_mark[(s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat]?.getD 0#8 &&& 1#8) ≠
      0#8 := hlm_b0 (step - 1) (by omega)
  let mkSt (ar : List (BitVec 32)) (lm : List (BitVec 8)) (sb : List (BitVec 32)) : FullState :=
    { core := { s.core with arena := ar, lit_mark := lm }
      scratch := { s.scratch with scratch_buf := sb } }
  let max_new := par_off.toNat - nrow_off.toNat
  have hmn_bv : (par_off - nrow_off).toNat = max_new := by
    simp only [bv_c0]; omega
  have hnr_bd : nrow_off.toNat + max_new ≤ c.scratch_cap := by omega
  have hpr_bd : par_off.toNat + max_new ≤ c.scratch_cap := hpr_cap
  have hdisj : nrow_off.toNat + max_new ≤ par_off.toNat := by omega
  let FilterEntryOk (sb : List (BitVec 32)) (nqn : Nat) : Prop :=
    ∀ nm < nqn,
      let pi := (sb[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧
      ∃ res : List Nat,
        (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
        FidBvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res ∧
        FidBvaRowEntryOk F_cur s best_lit.toNat (sb[nrow_off.toNat + nm]?.getD 0#32) res ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res))
  let SbFrame (sb : List (BitVec 32)) : Prop :=
    ∀ idx < c.scratch_cap,
      ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + max_new) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + max_new) →
      sb[idx]? = s.scratch.scratch_buf[idx]?
  unfold Func.wp full_bva_filter_row_body
  c0_hfast_nogrp
  fid_call hClines
  intro r_clines
  dsimp only [Arg.val]
  c0_hsteps
  refine wp_loop_inv
    (fun (nqn, qi, ticks, ()) ml => ∃ ar sb,
      qi.toNat ≤ cur_qn.toNat ∧ nqn.toNat ≤ max_new ∧
      FidFilterArBvaqInv c s ar sb nrow_off.toNat 0 nqn.toNat max_new ∧
      FullWitnessInv c F0 F_cur { s.core with arena := ar } ∧
      FullArenaVarsNodup (mkSt ar s.core.lit_mark sb) ∧
      SbFrame sb ∧ FilterEntryOk sb nqn.toNat ∧
      (FullMem c (mkSt ar s.core.lit_mark sb) ⋆ R) ml)
    (fun (_, qi, _, _) _ => cur_qn.toNat - qi.toNat)
    (fun Jq hJq => by
      c0_hsteps
      exact hJq (0#32, 0#32, _, ()) m
        ⟨s.core.arena, s.scratch.scratch_buf, Nat.zero_le _, Nat.zero_le _,
         fidFilterArBvaqInv_init hslen nrow_off.toNat max_new, hw, hnodup,
         fun _ _ _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _), hm⟩)
    (fun Jq (nqn, qi, ticks, ()) ml ⟨ar, sb, hqi_le, hnqn_le, hbvaq, hw_ar, hnd_ar, hfr_sb, hent,
      hml⟩ ihq => ?_)
  dsimp only [mkSt] at hml
  have har_l := hbvaq.1
  have hsb_l := hbvaq.2.1
  c0_hsteps_nogrp
  refine wp_join_state0 (α := Unit)
    (fun _ mf => mf = ml)
    (fun _ _ mf hmf => ?_)
    (fun Jend hJend => ?_)
  · rcases hmf with rfl
    refine wp_loop_inv
      (fun (ci, ()) mci => ∃ arci,
        ci.toNat ≤ nqn.toNat ∧
        FidFilterArBvaqInv c s arci sb nrow_off.toNat ci.toNat nqn.toNat max_new ∧
        (FullMem c (mkSt arci s.core.lit_mark sb) ⋆ R) mci)
      (fun (ci, ()) _ => nqn.toNat - ci.toNat)
      (fun Jc hJc => by c0_hfast; exact hJc (0#32, ()) _ ⟨ar, Nat.zero_le _, hbvaq, hml⟩)
      (fun Jc (ci, ()) mci ⟨arci, hci_le, hbvaq_ci, hmci⟩ ihc => ?_)
    clear hm hml
    dsimp only [mkSt] at hmci
    have harci_l := hbvaq_ci.1
    c0_hsteps_nogrp
    · have hci_lt : ci.toNat < nqn.toNat := by assumption
      have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by simp only [bv_c0]; omega
      have hnrci : (nrow_off + ci).toNat = nrow_off.toNat + ci.toNat := by simp only [bv_c0]; omega
      have hrci_lt : nrow_off.toNat + ci.toNat < sb.length := by rw [hsb_l]; omega
      let dr := sb[nrow_off.toNat + ci.toNat]'hrci_lt
      have hdr_eq : sb[(BitVec.setWidth 64 (nrow_off + ci)).toNat]'(by
          rw [hset, hnrci]; exact hrci_lt) = dr := by dsimp only [dr]; simp only [hset, hnrci]
      c0_hstep; c0_hsplit
      · have h0b : (dr &&& 0x80000000#32) = 0#32 := by
          have h1 : (sb[(BitVec.setWidth 64 (nrow_off + ci)).toNat]'(by
            rw [hset, hnrci]; exact hrci_lt) &&& 0x80000000#32) = 0#32 := by assumption
          rwa [hdr_eq] at h1
        have hdr_ref := (hbvaq_ci.2.2.2.1 ci.toNat (Nat.le_refl _) hci_lt (by
          rw [List.getElem?_eq_getElem hrci_lt, Option.getD_some]; exact h0b)).1
        rw [List.getElem?_eq_getElem hrci_lt, Option.getD_some] at hdr_ref
        have hdr_wf := hw.arena.refs_wf _ hdr_ref
        have hstep := fidFilterArBvaqInv_clear_large har_len hbvaq_ci hci_lt hrci_lt h0b (by
          have := hdr_wf.1; have := hcl.arena_len_le; omega)
        have hdr_ar_b : (BitVec.setWidth 64 (sb[(BitVec.setWidth 64 (nrow_off + ci)).toNat]'(by
            rw [hset, hnrci]; exact hrci_lt))).toNat < arci.length := by
          rw [hdr_eq, hset]; dsimp only [dr]; have := hdr_wf.1; have := hcl.arena_len_le; omega
        c0_hfast
        refine ihc (ci + 1#32, ()) m (by dsimp only; rw [hci1]; omega)
          ⟨_, by rw [hci1]; omega, by rw [hci1]; exact hstep, ?_⟩
        simp only [hset, hnrci] at hm; exact hm
      · have hbin : (sb[nrow_off.toNat + ci.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
          rw [List.getElem?_eq_getElem hrci_lt, Option.getD_some]
          have h1 : (sb[(BitVec.setWidth 64 (nrow_off + ci)).toNat]'(by
            rw [hset, hnrci]; exact hrci_lt) &&& 0x80000000#32) ≠ 0#32 := by assumption
          rwa [hdr_eq] at h1
        c0_hfast
        exact ihc (ci + 1#32, ()) mci (by dsimp only; rw [hci1]; omega)
          ⟨arci, by rw [hci1]; omega,
           by rw [hci1]; exact fidFilterArBvaqInv_clear_bin hbvaq_ci hci_lt hbin, hmci⟩
    · have hci_eq : ci.toNat = nqn.toNat := by omega
      rw [hci_eq] at hbvaq_ci
      have har_rest := fidFilterArBvaqInv_done har_len hbvaq_ci
      rw [har_rest] at hmci
      c0_hsteps
      · refine hQ nqn sb (s.scratch.ant_sz - ticks) _
          ⟨hcl, { hsc with scratch_buf_len := hsb_l }⟩ hnqn_le hfr_sb hent hm
      · refine hQ nqn sb 0#64 _
          ⟨hcl, { hsc with scratch_buf_len := hsb_l }⟩ hnqn_le hfr_sb hent hm
  · c0_hsplit
    · have hqi_lt : qi.toNat < cur_qn.toNat := by assumption
      c0_hsplit
      · have hnqn_lt : nqn.toNat < max_new := by
          have h1 : nqn.toNat < (par_off - nrow_off).toNat := by assumption
          rwa [hmn_bv] at h1
        have hqi1 : (qi + 1#32).toNat = qi.toNat + 1 := by simp only [bv_c0]; omega
        have hrqi : (row_off + qi).toNat = row_off.toNat + qi.toNat := by simp only [bv_c0]; omega
        have hnrnq : (nrow_off + nqn).toNat = nrow_off.toNat + nqn.toNat := by
          simp only [bv_c0]; omega
        have hprnq : (par_off + nqn).toNat = par_off.toNat + nqn.toNat := by
          simp only [bv_c0]; omega
        have hnqn1 : (nqn + 1#32).toNat = nqn.toNat + 1 := by simp only [bv_c0]; omega
        have hqw_sb_eq : sb[row_off.toNat + qi.toNat]? = s.scratch.scratch_buf[row_off.toNat +
          qi.toNat]? :=
          hfr_sb (row_off.toNat + qi.toNat) (by omega) (by omega) (by omega)
        have hrqi_lt : row_off.toNat + qi.toNat < sb.length := by rw [hsb_l]; omega
        let qw := s.scratch.scratch_buf[row_off.toNat + qi.toNat]'(by omega)
        have hqw_eq : sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
            rw [hset, hrqi]; exact hrqi_lt) = qw := by
          have h1 : sb[row_off.toNat + qi.toNat]? = some qw := by
            rw [hqw_sb_eq, List.getElem?_eq_getElem (by omega)]
          rw [List.getElem?_eq_getElem (by omega)] at h1
          have h2 := Option.some.inj h1; simpa only [hset, hrqi] using h2
        have hrqi_mod : (row_off.toNat + qi.toNat) % 2 ^ 32 = row_off.toNat + qi.toNat :=
          Nat.mod_eq_of_lt (by omega)
        have hqw_mod : sb[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by
            rw [hrqi_mod]; exact hrqi_lt) = qw := by
          have h1 : sb[row_off.toNat + qi.toNat]? = some qw := by
            rw [hqw_sb_eq, List.getElem?_eq_getElem (by omega)]
          rw [List.getElem?_eq_getElem (by omega)] at h1
          have h2 := Option.some.inj h1; simpa only [hrqi_mod] using h2
        have hqi_lt_mat : qi.toNat < (s.scratch.scratch_buf[2 * sc +
          (step - 1)]?.getD 0#32).toNat := by
          rw [← hqn_eq]; exact hqi_lt
        obtain ⟨res, hres_lt, hres_nd, hqw_ent, hres_ent, _⟩ := hrow_entries qi.toNat hqi_lt_mat
        rw [← hrow_eq] at hqw_ent
        have hqw_getD : s.scratch.scratch_buf[row_off.toNat + qi.toNat]?.getD 0#32 = qw := by
          dsimp only [qw]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [hqw_getD] at hqw_ent
        c0_hsteps_nogrp
        refine wp_join_state (ts := [i32, i64])
          (α := BitVec 32 × BitVec 64 × List (BitVec 32) × List (BitVec 32))
            (fun st => (st.1, st.2.1, ()))
          (fun ⟨nqn', ticks', ar', sb'⟩ mf =>
            nqn'.toNat ≤ max_new ∧
            FidFilterArBvaqInv c s ar' sb' nrow_off.toNat 0 nqn'.toNat max_new ∧
            FullWitnessInv c F0 F_cur { s.core with arena := ar' } ∧
            FullArenaVarsNodup (mkSt ar' s.core.lit_mark sb') ∧
            SbFrame sb' ∧ FilterEntryOk sb' nqn'.toNat ∧
            (FullMem c (mkSt ar' s.core.lit_mark sb') ⋆ R) mf)
          (fun _ ⟨nqn', ticks', ar', sb'⟩ mf ⟨hnqn', hbvaq', hw', hnd', hfr', hent', hmf⟩ => by
            c0_hfast
            exact ihq (nqn', qi + 1#32, ticks', ()) mf (by dsimp only; rw [hqi1]; omega)
              ⟨ar', sb', by rw [hqi1]; omega, hnqn', hbvaq', hw', hnd', hfr', hent', hmf⟩)
          (fun Jbr hJbr => ?_)
        c0_hsplit
        · -- Binary watch branch
          have hbin_ne : (qw &&& 0x80000000#32) ≠ 0#32 := by
            have h1 : (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
              rw [hset, hrqi]; exact hrqi_lt) &&& 0x80000000#32) ≠ 0#32 := by assumption
            rwa [hqw_eq] at h1
          unfold FidBvaRowEntryOk at hqw_ent; rw [ite_eq_left hbin_ne] at hqw_ent
          obtain ⟨hq_lt0, hres_eq, hfr_q⟩ := hqw_ent
          let q := qw &&& 0x7FFFFFFF#32
          have hq_lt : q.toNat < 2 * s.core.cur_vars := hq_lt0
          have hq_eq : sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
              rw [hset, hrqi]; exact hrqi_lt) &&& 0x7FFFFFFF#32 = q := by rw [hqw_eq]
          have hq_mod : sb[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by
              rw [hrqi_mod]; exact hrqi_lt) &&&
              (2147483647 : BitVec 32) = q := by rw [hqw_mod]; rfl
          have h2q_mod : 2 * q.toNat % 2 ^ 64 = 2 * q.toNat := Nat.mod_eq_of_lt (by omega)
          have h2q_n : (BitVec.setWidth 64 q <<< (1 : Nat)).toNat = 2 * q.toNat := by c0_bound
          have h2q1_n : ((BitVec.setWidth 64 q <<< (1 : Nat)) + 1).toNat = 2 * q.toNat + 1 := by
            change ((BitVec.setWidth 64 q <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
          have hq_bd := hdw.layout.bounds q.toNat hq_lt
          have hq_sl := hdw.slices q.toNat hq_lt
          have hoff_eq : (s.core.wvec[2 * q.toNat]'(by omega)).toNat =
              fullWatchOffCore s.core q.toNat := by
            unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hsz_eq : (s.core.wvec[2 * q.toNat + 1]'(by omega)).toNat =
              fullWatchSizeCore s.core q.toNat := by
            unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          let qoff0 := fullWatchOffCore s.core q.toNat
          let qsz0 := fullWatchSizeCore s.core q.toNat
          have h2q_wvec : (BitVec.setWidth 64 (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
              rw [hset, hrqi]; exact hrqi_lt) &&& 0x7FFFFFFF#32) <<< (1 : Nat)).toNat <
              s.core.wvec.length := by rw [hq_eq, h2q_n]; omega
          have h2q1_wvec : ((BitVec.setWidth 64 (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
              rw [hset, hrqi]; exact hrqi_lt) &&& 0x7FFFFFFF#32) <<< (1 : Nat)) + 1).toNat <
              s.core.wvec.length := by rw [hq_eq, h2q1_n]; omega
          have hq_repr : (BitVec.setWidth 64 (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
              rw [hset, hrqi]; exact hrqi_lt) &&& 0x7FFFFFFF#32)).toNat < s.core.repr.length := by
            rw [hq_eq, hset, hrepr_len]; omega
          c0_hfast_nogrp
          fid_call hClines
          intro r_clines_q
          dsimp only [Arg.val]
          c0_hsteps_nogrp
          refine wp_join_state
            (α := BitVec 32 × BitVec 64 × List (BitVec 32)) (fun st => (st.1, st.2.1, ()))
            (fun ⟨nqn', _qp', sb'⟩ mf =>
              nqn'.toNat ≤ max_new ∧
                FidFilterArBvaqInv c s ar sb' nrow_off.toNat 0 nqn'.toNat max_new ∧
              SbFrame sb' ∧ FilterEntryOk sb' nqn'.toNat ∧
              (FullMem c (mkSt ar s.core.lit_mark sb') ⋆ R) mf)
            (fun _ ⟨nqn', _qp', sb'⟩ mf ⟨hnqn', hbvaq', hfr', hent', hmf⟩ => by
              c0_hfast
              exact hJbr ⟨nqn', _, ar, sb'⟩ mf ⟨hnqn', hbvaq', hw_ar, hnd_ar, hfr', hent', hmf⟩)
            (fun Jqp hJqp => ?_)
          refine wp_loop_inv
            (fun (qp, ()) mlp =>
              qoff0 ≤ qp.toNat ∧ qp.toNat ≤ qoff0 + qsz0 ∧ mlp = ml ∧
              DenseWatchSliceOk F_cur s.core q.toNat qp.toNat (qoff0 + qsz0 - qp.toNat))
            (fun (qp, ()) _ => qoff0 + qsz0 - qp.toNat)
            (fun Jp hJp => by
              c0_hfast
              have h1 : (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64
                  (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
                    rw [hset, hrqi]
                    exact hrqi_lt) &&& (2147483647 : BitVec 32)) <<< (1 : Nat)).toNat]'(by
                  rw [show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl, hq_eq, h2q_n]
                  omega))).toNat = qoff0 := by
                simp only [show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl, hq_eq]
                simp only [h2q_n, hset, hoff_eq]; rfl
              exact hJp (_, ()) ml ⟨by rw [h1]; exact Nat.le_refl _, by rw [h1]; omega, rfl,
                by simpa only [h1, Nat.add_sub_cancel_left] using hq_sl⟩)
            (fun Jp (qp, ()) mlp ⟨hqp_ge, hqp_le, hmlp, hrem⟩ ihp => ?_)
          subst hmlp
          clear hm
          c0_hsplit
          · have hqp_lt : qp.toNat < qoff0 + qsz0 := by
              have hqend_mod : ((s.core.wvec[2 * q.toNat % 2 ^ 64]'(by rw [h2q_mod]; omega)).toNat +
                  (s.core.wvec[(2 * q.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                    rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega)).toNat) % 2 ^ 64 =
                  qoff0 + qsz0 := by
                simp only [h2q_mod, show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega : 2 * q.toNat + 1 < 2 ^ 64), hoff_eq, hsz_eq]
                exact Nat.mod_eq_of_lt (by omega)
              rw [← hqend_mod]
              simpa only [← hq_mod] using (by assumption : _)
            have hqp_ws : qp.toNat < s.core.wstk.length := by omega
            have hqp1_n : (qp + 1#64).toNat = qp.toNat + 1 := by simp only [bv_c0]; omega
            have hnrnq_sb : (BitVec.setWidth 64 (nrow_off + nqn)).toNat < sb.length := by
              rw [hset, hnrnq, hsb_l]; omega
            have hprnq_sb : (BitVec.setWidth 64 (par_off + nqn)).toNat <
                (sb.set (BitVec.setWidth 64 (nrow_off + nqn)).toNat qw).length := by
              rw [List.length_set, hset, hprnq, hsb_l]; omega
            c0_hfast_b
            · have ⟨_, hq_bl_ent, _⟩ :=
                FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hqp_ws (by assumption)
              have hnw_bl : (s.core.wstk[qp.toNat]'hqp_ws &&& 0x7FFFFFFF#32) = best_lit := by
                assumption
              rw [hnw_bl] at hq_bl_ent
              have hbl_q_ent : (cnfOfClauses F_cur).EntailsClause
                  (cnfClause [best_lit.toNat, q.toNat]) := bva_bin_swap_entails hq_bl_ent
              have ⟨hbvaq1, hfr1, hent1⟩ := fid_filter_row_bin_upd hsb_l hbvaq hnqn_lt hnr_bd
                hpr_bd hdisj hbin_ne hq_lt hres_eq hfr_q hbl_q_ent hqi_lt hres_lt hres_nd
                (fun t ht => hres_ent t (by omega)) hqw_getD hfr_sb hent
              let sb1 := (sb.set (nrow_off.toNat + nqn.toNat) qw).set (par_off.toNat + nqn.toNat) qi
              have hm1 : (FullMem c (mkSt ar s.core.lit_mark sb1) ⋆ R) m := by
                dsimp only [mkSt, sb1]
                simp only [hqw_eq] at hm; simp only [hset, hnrnq, hprnq] at hm; exact hm
              exact hJqp ⟨nqn + 1#32, qp, sb1⟩ m
                ⟨by rw [hnqn1]; omega, by rw [hnqn1]; exact hbvaq1, hfr1,
                 by rw [hnqn1]; exact hent1, hm1⟩
            · have ⟨_, _, hrem_next⟩ :=
                FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hqp_ws (by assumption)
              exact ihp (qp + 1#64, ()) mlp (by dsimp only; rw [hqp1_n]; omega)
                ⟨by rw [hqp1_n]; omega, by rw [hqp1_n]; omega, rfl,
                 by rw [hqp1_n, show qoff0 + qsz0 - (qp.toNat + 1) = qoff0 +
                   qsz0 - qp.toNat - 1 by omega]; exact hrem_next⟩
            · have ⟨h2le, hrem_next⟩ :=
                FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hqp_ws (by assumption)
              have hqp2_n : (qp + 2#64).toNat = qp.toNat + 2 := by simp only [bv_c0]; omega
              exact ihp (qp + 2#64, ()) mlp (by dsimp only; rw [hqp2_n]; omega)
                ⟨by rw [hqp2_n]; omega, by rw [hqp2_n]; omega, rfl,
                 by rw [hqp2_n, show qoff0 + qsz0 - (qp.toNat + 2) = qoff0 +
                   qsz0 - qp.toNat - 2 by omega]; exact hrem_next⟩
          · c0_hfast
            exact hJqp ⟨nqn, qp, sb⟩ mlp ⟨hnqn_le, hbvaq, hfr_sb, hent, hml⟩
        · -- Large clause branch
          have hbin_eq : (qw &&& 0x80000000#32) = 0#32 := by
            have h1 : (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
              rw [hset, hrqi]; exact hrqi_lt) &&& 0x80000000#32) = 0#32 := by assumption
            rwa [hqw_eq] at h1
          unfold FidBvaRowEntryOk at hqw_ent; rw [ite_eq_right (fun h' => h' hbin_eq)] at hqw_ent
          obtain ⟨hqw_ref, hqw_ng, hqw_sz3, hqw_sz5, hfr_mem, hres_perm_f, hqw_perm⟩ := hqw_ent
          have hqw_wf := hw.arena.refs_wf qw.toNat hqw_ref
          have ⟨hrefs_ar, hcl_ar⟩ := fidFilterArBvaqInv_congr hcl hw hbvaq
          have ⟨hqw_ng_ar, hqw_sz_ar, hqw_lits_ar⟩ := hcl_ar qw.toNat hqw_ref
          have hqw2_lt : qw.toNat + 2 < ar.length := by have := hqw_wf.1; omega
          have hqw_sz_eq : (ar[qw.toNat +
            2]'hqw2_lt).toNat = fullArenaClauseSizeCore s.core qw.toNat := by
            rw [← hqw_sz_ar]; unfold fullArenaClauseSizeCore
            rw [List.getElem?_eq_getElem hqw2_lt, Option.getD_some]
          let csz_bv := ar[qw.toNat + 2]'hqw2_lt
          have hcsz_nat : csz_bv.toNat = fullArenaClauseSizeCore s.core qw.toNat := hqw_sz_eq
          have hqw2_n : (BitVec.setWidth 64 qw + 2).toNat = qw.toNat + 2 := by
            change (BitVec.setWidth 64 qw + 2#64).toNat = _; simp only [bv_c0]; omega
          have hqw2_mod : (qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = qw.toNat + 2 := by
            rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
          have hcsz_mod : csz_bv = ar[(qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
              rw [hqw2_mod]; exact hqw2_lt) := by dsimp only [csz_bv]; simp only [hqw2_mod]
          have hqw2_ar : (BitVec.setWidth 64 (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
              rw [hset, hrqi]; exact hrqi_lt)) + 2).toNat < ar.length := by
            rw [hqw_eq, hqw2_n, har_l]; have := hqw_wf.1; omega
          have hqw_lits_eq := fid_filter_row_ar_lits_eq hcl hw hbvaq hqw_ref
          c0_hsteps_nogrp
          refine wp_join_state (ts := [i32, i32, i32, i32])
            (α := BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × List (BitVec 8))
            (fun ⟨min_l, min_d, fc, jf, _⟩ => (min_l, min_d, fc, jf, ()))
            (fun ⟨min_l, min_d, fc, _, lm1⟩ mf =>
              LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 csz_bv.toNat lm1 ∧
              (fc.toNat ≤ 1 → ∀ l < 2 * s.core.cur_vars, (lm1[l]?.getD 0#8 &&& 2#8) ≠ 0#8 →
                l ∈ res) ∧
              (min_l ≠ 0xFFFFFFFF#32 → min_l.toNat < 2 * s.core.cur_vars) ∧
              (FullMem c (mkSt ar lm1 sb) ⋆ R) mf)
            (fun _ ⟨min_l, min_d, fc, _jf, lm1⟩ mf ⟨hlm1_inv, hlm1_res, hmin_ok, hmf⟩ => ?_)
            (fun JmL hJmL => ?_)
          · -- Goal 1 of JmL: Match block + unmarking loop
            c0_hsteps_nogrp
            refine wp_join_state (ts := [i32, i64])
              (α := BitVec 32 × BitVec 64 × List (BitVec 32) × List (BitVec 32) × List (BitVec 8))
              (fun st => (st.1, st.2.1, ()))
              (fun ⟨nqn2, ticks2, ar2, sb2, lm2⟩ mf2 =>
                nqn2.toNat ≤ max_new ∧
                  FidFilterArBvaqInv c s ar2 sb2 nrow_off.toNat 0 nqn2.toNat max_new ∧
                FullWitnessInv c F0 F_cur { s.core with arena := ar2 } ∧
                FullArenaVarsNodup (mkSt ar2 s.core.lit_mark sb2) ∧
                SbFrame sb2 ∧ FilterEntryOk sb2 nqn2.toNat ∧
                LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 csz_bv.toNat lm2 ∧
                (FullMem c (mkSt ar2 lm2 sb2) ⋆ R) mf2)
              (fun _ ⟨nqn2, ticks2, ar2, sb2, lm2⟩ mf2 ⟨hnqn2, hbvaq2, hw2, hnd2, hfr2, hent2,
                hlm2_inv, hmf2⟩ => ?_)
              (fun Jm2 hJm2 => ?_)
            · -- Goal 1 of Jm2: Unmarking loop (restores lit_mark)
              clear hrow_entries hmat hlm_b0 hqw_lits_eq hqw_lits_ar
              try clear hm
              dsimp only [mkSt] at hmf2
              have har2_l := hbvaq2.1
              have hsb2_l := hbvaq2.2.1
              have hrqi_lt2 : row_off.toNat + qi.toNat < sb2.length := by rw [hsb2_l]; omega
              have hqw_eq2 : sb2[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
                  rw [hset, hrqi]; exact hrqi_lt2) = qw := by
                have h1 : sb2[row_off.toNat + qi.toNat]? = some qw := by
                  rw [hfr2 (row_off.toNat + qi.toNat) (by omega) (by omega) (by omega),
                      List.getElem?_eq_getElem (by omega)]
                rw [List.getElem?_eq_getElem hrqi_lt2] at h1
                have h2 := Option.some.inj h1; simpa only [hset, hrqi] using h2
              have hqw_eq2_mod : sb2[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by
                  rw [hrqi_mod]; exact hrqi_lt2) = qw := by
                have h1 : sb2[row_off.toNat + qi.toNat]? = some qw := by
                  rw [hfr2 (row_off.toNat + qi.toNat) (by omega) (by omega) (by omega),
                      List.getElem?_eq_getElem (by omega)]
                rw [List.getElem?_eq_getElem hrqi_lt2] at h1
                have h2 := Option.some.inj h1; simpa only [hrqi_mod] using h2
              have har2_lits := fid_filter_row_ar_lits_eq hcl hw hbvaq2 hqw_ref
              refine wp_loop_inv
                (fun (k, ()) mk => ∃ lmk, k.toNat ≤ csz_bv.toNat ∧
                  LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat k.toNat csz_bv.toNat lmk ∧
                  (FullMem c (mkSt ar2 lmk sb2) ⋆ R) mk)
                (fun (k, ()) _ => csz_bv.toNat - k.toNat)
                (fun Jc2 hJc2 => by
                  c0_hfast; exact hJc2 (0#32, ()) mf2 ⟨lm2, Nat.zero_le _, hlm2_inv, hmf2⟩)
                (fun Jc2 (k, ()) mk ⟨lmk, hk_le, hlmk_inv, hmk⟩ ihc2 => ?_)
              clear hmf2; dsimp only [mkSt] at hmk
              have hlmk_l := hlmk_inv.1
              c0_hsplit
              · have hk_lt : k.toNat < csz_bv.toNat := by
                  rw [hcsz_mod]
                  simpa only [← hqw_mod] using (by assumption : _)
                have hqwk_lt : qw.toNat + 3 + k.toNat < s.core.arena.length := by
                  have := hqw_wf.2.2.1; have := hqw_wf.2.2.2.1; omega
                have hck_eq : ar2[qw.toNat + 3 + k.toNat]'(by omega) =
                    s.core.arena[qw.toNat + 3 + k.toNat]'hqwk_lt := by
                  have h1 := har2_lits k.toNat (by omega)
                  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hqwk_lt] at h1
                  exact Option.some.inj h1
                have hck_lt : (s.core.arena[qw.toNat + 3 + k.toNat]'hqwk_lt).toNat <
                    2 * s.core.cur_vars :=
                  hw.arena.lits_lt qw.toNat hqw_ref hqw_ng _ (List.mem_of_getElem?
                    (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (by omega) (by omega)))
                have hk1 : (k + 1#32).toNat = k.toNat + 1 := by simp only [bv_c0]; omega
                have hidx_n : (BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 k).toNat =
                    qw.toNat + 3 + k.toNat := by
                  change (BitVec.setWidth 64 qw + 3#64 + BitVec.setWidth 64 k).toNat = _
                  simp only [bv_c0]; omega
                have hidx_ar : (BitVec.setWidth 64 (sb[(BitVec.setWidth 64
                    (row_off + qi)).toNat]'(by rw [hset, hrqi]; exact hrqi_lt)) + 3 +
                    BitVec.setWidth 64 k).toNat < ar2.length := by
                  rw [hqw_eq, hidx_n, har2_l]; omega
                have hck_lm : (BitVec.setWidth 64 (ar2[(BitVec.setWidth 64
                    (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
                      rw [hset, hrqi]
                      exact hrqi_lt)) + 3 + BitVec.setWidth 64 k).toNat]'hidx_ar)).toNat <
                    lmk.length := by simp only [hqw_eq]; simp only [hidx_n, hset, hck_eq]; omega
                c0_hfast
                try simp only [hqw_eq] at hm
                try simp only [hidx_n, hset] at hm
                try simp only [bv8_trunc_and_fd] at hm
                try simp only [bv8_trunc_and_w] at hm
                have hstep : LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat (k.toNat + 1)
                    csz_bv.toNat (lmk.set (ar2[qw.toNat + 3 + k.toNat]'(by omega)).toNat
                      ((lmk[(ar2[qw.toNat + 3 + k.toNat]'(by omega)).toNat]'(by
                        rw [hck_eq]; omega)) &&& 0xFD#8)) := by
                  have h0 := lmBit2Inv_clear_step hlm_len
                    (fun l hl => (bv8_bit_zero_of_and_fe (hlm_clr l hl)).1)
                    hlmk_inv hk_lt hqwk_lt (by omega)
                  simpa only [← hck_eq] using h0
                exact ihc2 (k + 1#32, ()) m (by dsimp only; rw [hk1]; omega)
                  ⟨_, by rw [hk1]; omega, by rw [hk1]; exact hstep, hm⟩
              · have hk_eq : k.toNat = csz_bv.toNat := by
                  rw [hcsz_mod] at hk_le ⊢
                  have h1 : ¬ k.toNat < (ar[(qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                    rw [hqw2_mod]; exact hqw2_lt)).toNat := by
                    simpa only [← hqw_mod] using (by assumption : _)
                  omega
                rw [hk_eq] at hlmk_inv
                have hlm_rest : lmk = s.core.lit_mark := lmBit2Inv_done hlm_len hlmk_inv
                rw [hlm_rest] at hmk; c0_hfast
                exact hJbr ⟨nqn2, ticks2, ar2, sb2⟩ mk ⟨hnqn2, hbvaq2, hw2, hnd2, hfr2, hent2, hmk⟩
            · -- Goal 2 of Jm2: Match block
              clear hm hml
              dsimp only [mkSt] at hmf
              have hlm1_l := hlm1_inv.1
              c0_hstep; c0_hsplit
              · -- fc == 1
                have hfc1 : fc.toNat ≤ 1 := by
                  have : fc = 1#32 := by assumption
                  rw [this]; decide
                have hlm1_res' := hlm1_res hfc1
                c0_hsplit
                · -- min_l != 0xFFFFFFFF
                  have hmin_ne : min_l ≠ 0xFFFFFFFF#32 := hc
                  have hml_lt := hmin_ok hmin_ne
                  have hml_bd := hdw.layout.bounds min_l.toNat hml_lt
                  have hml_sl := hdw.slices min_l.toNat hml_lt
                  have h2ml_n : (BitVec.setWidth 64 min_l <<< (1 : Nat)).toNat = 2 * min_l.toNat :=
                    by
                    simp only [bv_c0]; omega
                  have h2ml_mod : 2 * min_l.toNat % 2 ^ 64 = 2 * min_l.toNat :=
                    Nat.mod_eq_of_lt (by omega)
                  have hmoff_eq : (s.core.wvec[2 * min_l.toNat]'(by omega)).toNat =
                      fullWatchOffCore s.core min_l.toNat := by
                    unfold fullWatchOffCore
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  have hmsz_eq : (s.core.wvec[2 * min_l.toNat + 1]'(by omega)).toNat =
                      fullWatchSizeCore s.core min_l.toNat := by
                    unfold fullWatchSizeCore
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  let moff0 := fullWatchOffCore s.core min_l.toNat
                  let msz0 := fullWatchSizeCore s.core min_l.toNat
                  have h2ml_wv : (BitVec.setWidth 64 min_l <<< (1 :
                      Nat)).toNat < s.core.wvec.length := by
                    rw [h2ml_n]; omega
                  have h2ml1_wv : ((BitVec.setWidth 64 min_l <<< (1 : Nat)) + 1).toNat <
                      s.core.wvec.length := by
                    change ((BitVec.setWidth 64 min_l <<< (1 : Nat)) + 1#64).toNat < _
                    simp only [bv_c0]; omega
                  c0_hfast_nogrp
                  fid_call hClines
                  intro r_clines_min
                  dsimp only [Arg.val]
                  c0_hsteps_nogrp
                  refine wp_join_state (ts := [i32, i64, i64])
                    (α := BitVec 32 × BitVec 64 × BitVec 64 × List (BitVec 32) × List (BitVec 32))
                    (fun st => (st.1, st.2.1, st.2.2.1, ()))
                    (fun ⟨nqn2, ticks2, _mp2, ar2, sb2⟩ mf2 =>
                      nqn2.toNat ≤ max_new ∧
                      FidFilterArBvaqInv c s ar2 sb2 nrow_off.toNat 0 nqn2.toNat max_new ∧
                      FullWitnessInv c F0 F_cur { s.core with arena := ar2 } ∧
                      FullArenaVarsNodup (mkSt ar2 s.core.lit_mark sb2) ∧
                      SbFrame sb2 ∧ FilterEntryOk sb2 nqn2.toNat ∧
                      (FullMem c (mkSt ar2 lm1 sb2) ⋆ R) mf2)
                    (fun _ ⟨nqn2, ticks2, _mp2, ar2, sb2⟩ mf2
                        ⟨hnqn2, hbvaq2, hw2, hnd2, hfr2, hent2, hmf2⟩ => by
                      c0_hfast
                      exact hJm2 ⟨nqn2, ticks2, ar2, sb2, lm1⟩ mf2
                        ⟨hnqn2, hbvaq2, hw2, hnd2, hfr2, hent2, hlm1_inv, hmf2⟩)
                    (fun Jmp hJmp => ?_)
                  refine wp_loop_inv (ts := [i64, i64])
                    (fun (ticks_m, mp, ()) mlp =>
                      moff0 ≤ mp.toNat ∧ mp.toNat ≤ moff0 + msz0 ∧ mlp = mf ∧
                      DenseWatchSliceOk F_cur s.core min_l.toNat mp.toNat (moff0 + msz0 - mp.toNat))
                    (fun (_, mp, ()) _ => moff0 + msz0 - mp.toNat)
                    (fun Jp hJp => by
                      c0_hfast
                      have h1 : (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 min_l <<< (1 :
                          Nat)).toNat]'(by
                          rw [h2ml_n]; omega))).toNat = moff0 := by
                        simp only [h2ml_n, hset, hmoff_eq]; rfl
                      simpa only [show OfNat.ofNat (1 : Nat) = (1 : Nat) from rfl] using
                        hJp (_, BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 min_l <<< (1 :
                            Nat)).toNat]'(by
                          rw [h2ml_n]; omega)), ()) mf
                        ⟨by rw [h1]; exact Nat.le_refl _, by rw [h1]; omega, rfl,
                         by simpa only [h1, Nat.add_sub_cancel_left] using hml_sl⟩)
                    (fun Jp (ticks_m, mp, ()) mlp ⟨hmp_ge, hmp_le, hmlp, hrem⟩ ihp => ?_)
                  subst hmlp
                  c0_hsplit
                  · have hmp_lt : mp.toNat < moff0 + msz0 := by
                      have hmend_mod : ((s.core.wvec[2 * min_l.toNat % 2 ^ 64]'(by
                          rw [h2ml_mod]; omega)).toNat +
                          (s.core.wvec[(2 * min_l.toNat +
                            BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                            rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
                            omega)).toNat) % 2 ^ 64 =
                          moff0 + msz0 := by
                        simp only [h2ml_mod, show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
                          Nat.mod_eq_of_lt (by omega : 2 * min_l.toNat + 1 < 2 ^ 64), hmoff_eq,
                            hmsz_eq]
                        exact Nat.mod_eq_of_lt (by omega)
                      rw [← hmend_mod]
                      simpa only [show OfNat.ofNat (1 : Nat) = (1 : Nat) from rfl] using (by
                          assumption : _)
                    have hmp_ws : mp.toNat < s.core.wstk.length := by omega
                    have hmp1_n : (mp + 1#64).toNat = mp.toNat + 1 := by simp only [bv_c0]; omega
                    c0_hfast_nogrp
                    · -- binary watch: continue
                      have ⟨_, _, hrem_next⟩ :=
                        FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hmp_ws (by assumption)
                      exact ihp (ticks_m, mp + 1#64, ()) mlp (by dsimp only; rw [hmp1_n]; omega)
                        ⟨by rw [hmp1_n]; omega, by rw [hmp1_n]; omega, rfl,
                         by rw [hmp1_n,
                           show moff0 + msz0 - (mp.toNat + 1) = moff0 + msz0 - mp.toNat - 1
                              by omega]; exact hrem_next⟩
                    · -- large watch: mp + 1 >= mend -> break
                      c0_hfast
                      exact hJmp ⟨nqn, _, _, ar, sb⟩ mlp ⟨hnqn_le, hbvaq, hw_ar, hnd_ar, hfr_sb,
                        hent, hmf⟩
                    · -- large watch: mp + 1 < mend -> inspect dr
                      have hmp1_lt : mp.toNat + 1 < moff0 + msz0 := by
                        have hmend_mod : ((s.core.wvec[2 * min_l.toNat % 2 ^ 64]'(by
                            rw [h2ml_mod]; omega)).toNat +
                            (s.core.wvec[(2 * min_l.toNat +
                              BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                              rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
                              omega)).toNat) % 2 ^ 64 =
                            moff0 + msz0 := by
                          simp only [h2ml_mod, show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
                            Nat.mod_eq_of_lt (by omega : 2 * min_l.toNat + 1 < 2 ^ 64), hmoff_eq,
                              hmsz_eq]
                          exact Nat.mod_eq_of_lt (by omega)
                        have hnge : ¬ moff0 + msz0 ≤ (mp.toNat + 1) % 2 ^ 64 := by
                          rw [← hmend_mod]; simp only [h2ml_mod]
                          have hhc := hc
                          simp only [FullArenaTactics.bv64_shl1_nat, hset, h2ml_mod,
                            show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
                            show OfNat.ofNat (1 : Nat) = (1 : Nat) from rfl] at hhc
                          simpa only [show BitVec.toNat (1 : BitVec 64) = 1 from rfl] using hhc
                        have hmod1 : (mp.toNat + 1) % 2 ^ 64 = mp.toNat + 1 :=
                          Nat.mod_eq_of_lt (by omega)
                        rw [hmod1] at hnge; omega
                      have hmp1_ws : mp.toNat + 1 < s.core.wstk.length := by omega
                      have hmp2_n : (mp + 2#64).toNat = mp.toNat + 2 := by
                        change (mp + 2#64).toNat = _; simp only [bv_c0]; omega
                      let dr := s.core.wstk[mp.toNat + 1]'hmp1_ws
                      have ⟨hdr_ref, hdr_rem⟩ :
                          dr.toNat ∈ fullArenaClauseRefsCore s.core ∧
                          DenseWatchSliceOk F_cur s.core min_l.toNat (mp.toNat + 2)
                            (moff0 + msz0 - mp.toNat - 2) := by
                        rcases denseWatchSliceOk_step hrem (by omega) with
                          ⟨w0, hw0_s, hbin_ne, _⟩ |
                          ⟨w0, cr, _, _, hcr_s, _, _, _, hdr_ref, hdr_rem⟩
                        · have hmp_eq : s.core.wstk[mp.toNat]'hmp_ws = w0 := by
                            rw [List.getElem?_eq_getElem hmp_ws] at hw0_s
                            exact Option.some.inj hw0_s
                          exact absurd (hmp_eq ▸ (by assumption : _)) hbin_ne
                        · have hcr_eq : dr = cr := by
                            dsimp only [dr]
                            rw [List.getElem?_eq_getElem hmp1_ws] at hcr_s
                            exact Option.some.inj hcr_s
                          rw [hcr_eq]
                          exact ⟨hdr_ref, by simpa only [Nat.sub_sub] using hdr_rem⟩
                      have hmp12_n : (mp + 1#64 + 1#64).toNat = mp.toNat + 2 := by
                        simp only [bv_c0]; omega
                      c0_hfast_nogrp_b
                      · -- dr == qw: continue
                        exact ihp (ticks_m, mp + 1#64 + 1#64, ()) mlp
                          (by dsimp only; rw [hmp12_n]; omega)
                          ⟨by rw [hmp12_n]; omega, by rw [hmp12_n]; omega, rfl,
                           by rw [hmp12_n, show moff0 + msz0 - (mp.toNat + 2) =
                                moff0 + msz0 - mp.toNat - 2 by omega]; exact hdr_rem⟩
                      · -- dr != qw: call hMatchLarge
                        have hdr_ref_s : dr.toNat ∈ fullArenaClauseRefsCore s.core := hdr_ref
                        have hdr_lt_ar : dr.toNat + 3 ≤ ar.length := by
                          have hwf := hw.arena.refs_wf dr.toNat hdr_ref_s; rw [har_l]; omega
                        have ⟨hdr_ng_s, hdr_sz_s, hdr_lits_s⟩ := hcl_ar dr.toNat hdr_ref_s
                        have hres_nd_l : res.Nodup := nodup_of_map_div2 hres_nd
                        have hqw_sz_res : fullArenaClauseSize
                            (FullState.mk { s.core with arena := ar, lit_mark := lm1 }
                              { s.scratch with scratch_buf := sb }) qw.toNat = res.length + 1 := by
                          change fullArenaClauseSizeCore { s.core with arena := ar } qw.toNat = _
                          rw [hqw_sz_ar]
                          have h1 := FullBvaFwdHelpers.fullArenaClauseLitsCore_length (k := s.core)
                            (r := qw.toNat) (by have := hqw_wf.2.2.1; have := hqw_wf.2.2.2.1; omega)
                          have h2 := hqw_perm.length_eq
                          unfold fullArenaClauseLits at h2; simp only [List.length_cons] at h2
                          omega
                        have hdr_eq : s.core.wstk[(mp + 1#64).toNat]'(by
                            rw [hmp1_n]; exact hmp1_ws) = dr := by
                          dsimp only [dr]; simp only [hmp1_n]
                        c0_hsteps_nogrp
                        fid_call hMatchLarge
                        · refine ⟨c, F0, F_cur,
                            FullState.mk { s.core with arena := ar, lit_mark := lm1 }
                              { s.scratch with scratch_buf := sb },
                            R, res, rfl,
                            ⟨{ hcl with arena_len_arr := har_l, lit_mark_len := hlm1_l },
                             { hsc with scratch_buf_len := hsb_l }⟩,
                            fullWitnessInv_with_litMark hw_ar lm1, hnd_ar, hl0, hdm,
                            by dsimp only [Arg.val]; rw [hqw_eq]
                               change qw.toNat ∈ fullArenaClauseRefsCore { s.core with arena := ar }
                               rw [hrefs_ar]; exact hqw_ref,
                            by dsimp only [Arg.val]; rw [hqw_eq]
                               change fullArenaClauseGarbCore { s.core with arena := ar }
                                 qw.toNat = false
                               rw [hqw_ng_ar]; exact hqw_ng,
                            by dsimp only [Arg.val]
                               change (s.core.wstk[(mp + 1#64).toNat]'_).toNat ∈ _
                               rw [hdr_eq]
                               change dr.toNat ∈ fullArenaClauseRefsCore { s.core with arena := ar }
                               rw [hrefs_ar]; exact hdr_ref_s,
                            hres_nd_l, hres_lt,
                            by dsimp only [Arg.val]; rw [hqw_eq]; exact hqw_sz_res,
                            hlm1_res', hmf, ?_⟩
                          · intro ok hok
                            c0_hsplit
                            · -- match ok = true
                              have ⟨hdr_ng_ar, hdr_nbvaq_h, hdr_sz_eq_ar, hbl_mem_ar, hdr_perm_ar,
                                hdr_filt_ar, hbl_res_ent⟩ :=
                                hok (by assumption)
                              try simp only [show (1 : BitVec 64) = 1#64 from rfl] at hdr_ng_ar
                              try simp only [show (1 : BitVec 64) = 1#64 from rfl] at hdr_nbvaq_h
                              try simp only [show (1 : BitVec 64) = 1#64 from rfl] at hdr_sz_eq_ar
                              try simp only [show (1 : BitVec 64) = 1#64 from rfl] at hbl_mem_ar
                              try simp only [show (1 : BitVec 64) = 1#64 from rfl] at hdr_perm_ar
                              try simp only [show (1 : BitVec 64) = 1#64 from rfl] at hdr_filt_ar
                              try rw [hdr_eq] at hdr_ng_ar
                              try rw [hdr_eq] at hdr_nbvaq_h
                              try rw [hdr_eq] at hdr_sz_eq_ar
                              try rw [hdr_eq] at hbl_mem_ar
                              try rw [hdr_eq] at hdr_perm_ar
                              try rw [hdr_eq] at hdr_filt_ar
                              try rw [hqw_eq] at hdr_sz_eq_ar
                              have ⟨hbvaq1, hw1, hnd1, hfr1, hent1⟩ := fid_filter_row_large_upd
                                (lmj := lm1) hcl har_l hsb_l hw_ar hnd_ar hl0 hbvaq hnqn_lt
                                hnr_bd hpr_bd hdisj
                                hrefs_ar hqw_ref hqw_ng hqw_sz3 hqw_sz5 hqw_sz_ar hfr_mem
                                    hres_perm_f
                                hqw_perm hbin_eq hdr_ref_s hdr_lt_ar hdr_ng_s hdr_sz_s hdr_lits_s
                                hdr_ng_ar hdr_nbvaq_h hdr_sz_eq_ar hbl_mem_ar hdr_perm_ar
                                    hdr_filt_ar
                                hbl_res_ent hqi_lt hres_lt hres_nd (fun t ht =>
                                  hres_ent t (by omega))
                                hqw_getD hfr_sb hent (by unfold dimacsBound; omega)
                              dsimp only
                              try simp only [show (1 : BitVec 64) = 1#64 from rfl, hdr_eq]
                              have hdr_ar_w : (BitVec.setWidth 64 dr).toNat < ar.length := by
                                rw [hset, har_l]; omega
                              have hnrnq_sb : (BitVec.setWidth 64 (nrow_off +
                                nqn)).toNat < sb.length := by
                                rw [hset, hnrnq, hsb_l]; omega
                              have hprnq_sb : (BitVec.setWidth 64 (par_off + nqn)).toNat <
                                  (sb.set (BitVec.setWidth 64 (nrow_off + nqn)).toNat dr).length :=
                                    by
                                rw [List.length_set, hset, hprnq, hsb_l]; omega
                              have hprnq_sb2 : (BitVec.setWidth 64 (par_off + nqn)).toNat <
                                  (sb.set (nrow_off.toNat + nqn.toNat) dr).length := by
                                rw [List.length_set, hset, hprnq, hsb_l]; omega
                              c0_hfast_nogrp
                              let ar1 := ar.set dr.toNat ((ar[dr.toNat]'(by
                                  omega)) ||| 0x02000000#32)
                              let sb1 := (sb.set (nrow_off.toNat +
                                nqn.toNat) dr).set (par_off.toNat + nqn.toNat) qi
                              have hm1 : (FullMem c
                                  { core := { s.core with arena := ar1, lit_mark := lm1 }
                                    scratch := { s.scratch with scratch_buf := sb1 } } ⋆
                                  R) m := by
                                dsimp only [ar1, sb1]
                                simp only [hset, hnrnq, hprnq] at hm; exact hm
                              exact hJmp ⟨nqn + 1#32, _, _, ar1, sb1⟩ m
                                ⟨by rw [hnqn1]; omega, by rw [hnqn1]; exact hbvaq1, hw1, hnd1,
                                 hfr1, by rw [hnqn1]; exact hent1, hm1⟩
                            · -- match ok = false: continue
                              c0_hfast
                              exact ihp (ticks_m + 1#64, mp + 1#64 + 1#64, ()) mlp
                                (by dsimp only; rw [hmp12_n]; omega)
                                ⟨by rw [hmp12_n]; omega, by rw [hmp12_n]; omega, rfl,
                                 by rw [hmp12_n, show moff0 + msz0 - (mp.toNat + 2) =
                                      moff0 + msz0 - mp.toNat - 2 by omega]; exact hdr_rem⟩
                  · -- mp >= mend: break
                    c0_hfast
                    exact hJmp ⟨nqn, _, _, ar, sb⟩ mlp ⟨hnqn_le, hbvaq, hw_ar, hnd_ar, hfr_sb,
                      hent, hmf⟩
                · -- min_l == 0xFFFFFFFF: skip to unmarking
                  c0_hfast
                  exact hJm2 ⟨nqn, _, ar, sb, lm1⟩ mf ⟨hnqn_le, hbvaq, hw_ar, hnd_ar, hfr_sb, hent,
                    hlm1_inv, hmf⟩
              · -- fc != 1: skip to unmarking
                c0_hfast
                exact hJm2 ⟨nqn, _, ar, sb, lm1⟩ mf ⟨hnqn_le, hbvaq, hw_ar, hnd_ar, hfr_sb, hent,
                  hlm1_inv, hmf⟩
          · -- Goal 2 of JmL: Marking loop
            refine wp_loop_inv
              (fun (min_l, min_d, fc, j, ()) mj => ∃ lmj, j.toNat ≤ csz_bv.toNat ∧ fc.toNat ≤ 1 ∧
                LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 j.toNat lmj ∧
                (fc.toNat ≤ 1 → ∀ l < 2 * s.core.cur_vars, (lmj[l]?.getD 0#8 &&& 2#8) ≠ 0#8 →
                  l ∈ res) ∧
                (min_l ≠ 0xFFFFFFFF#32 → min_l.toNat < 2 * s.core.cur_vars) ∧
                (FullMem c (mkSt ar lmj sb) ⋆ R) mj)
              (fun (_, _, _, j, _) _ => csz_bv.toNat - j.toNat)
              (fun JmL hJmL => by
                c0_hfast; exact hJmL (0xFFFFFFFF#32, 0xFFFFFFFF#32, 0#32, 0#32, ()) ml
                  ⟨s.core.lit_mark, Nat.zero_le _, by decide, lmBit2Inv_init hlm_len,
                   fun _ l hl hne => absurd (bv8_bit_zero_of_and_fe (hlm_clr l (by omega))).1 hne,
                   fun h => absurd rfl h, hml⟩)
              (fun JmL (min_l, min_d, fc, j, ()) mj ⟨lmj, hj_le, hfc_le, hlmj_inv, hlmj_res,
                hmin_ok, hmj⟩ ihm => ?_)
            try clear hm
            clear hml; dsimp only [mkSt] at hmj
            have hlmj_l := hlmj_inv.1
            c0_hsplit
            · have hj_lt : j.toNat < csz_bv.toNat := by
                rw [hcsz_mod]
                simpa only [← hqw_mod] using (by assumption : _)
              have hj1 : (j + 1#32).toNat = j.toNat + 1 := by simp only [bv_c0]; omega
              have hqwj_n : (BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat =
                  qw.toNat + 3 + j.toNat := by
                change (BitVec.setWidth 64 qw + 3#64 + BitVec.setWidth 64 j).toNat = _
                simp only [bv_c0]; omega
              have hqwj_mod : (qw.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64 =
                  qw.toNat + 3 + j.toNat := by
                rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]
                exact Nat.mod_eq_of_lt (Nat.lt_trans
                  (Nat.add_lt_add (Nat.add_lt_add_right qw.isLt 3) j.isLt) (by decide))
              have hj_lt_sz : j.toNat < fullArenaClauseSizeCore s.core qw.toNat :=
                hcsz_nat ▸ hj_lt
              have hqwj_lt : qw.toNat + 3 + j.toNat < s.core.arena.length := by
                rw [hcl.arena_len_arr]
                exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj_lt_sz _)
                  (Nat.le_trans hqw_wf.2.2.1 (Nat.le_trans hqw_wf.2.2.2.1 hcl.arena_len_le))
              have hqwj_ar_lt : qw.toNat + 3 + j.toNat < ar.length := by
                rw [har_l, ← hcl.arena_len_arr]; exact hqwj_lt
              have hl_eq : ar[qw.toNat + 3 + j.toNat]'hqwj_ar_lt =
                  s.core.arena[qw.toNat + 3 + j.toNat]'hqwj_lt := by
                have h1 := hqw_lits_eq j.toNat hj_lt_sz
                rw [List.getElem?_eq_getElem hqwj_ar_lt,
                  List.getElem?_eq_getElem hqwj_lt] at h1
                exact Option.some.inj h1
              have hl_mem : (s.core.arena[qw.toNat + 3 + j.toNat]'hqwj_lt).toNat ∈
                  fullArenaClauseLitsCore s.core qw.toNat :=
                List.mem_of_getElem? (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem
                  hj_lt_sz hqwj_lt)
              have hl_lt : (ar[qw.toNat + 3 + j.toNat]'hqwj_ar_lt).toNat <
                  2 * s.core.cur_vars := by
                rw [hl_eq]; exact hw.arena.lits_lt qw.toNat hqw_ref hqw_ng _ hl_mem
              have hqwj_ar : (BitVec.setWidth 64 (sb[(BitVec.setWidth 64
                  (row_off + qi)).toNat]'(by rw [hset, hrqi]; exact hrqi_lt)) + 3 +
                  BitVec.setWidth 64 j).toNat < ar.length := by rw [hqw_eq, hqwj_n, har_l]; omega
              have hl_lm : (BitVec.setWidth 64 (ar[(BitVec.setWidth 64
                  (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
                    rw [hset, hrqi]
                    exact hrqi_lt)) + 3 + BitVec.setWidth 64 j).toNat]'hqwj_ar)).toNat <
                  lmj.length := by simp only [hqw_eq]; simp only [hqwj_n, hset]; omega
              have hl_repr : (BitVec.setWidth 64 (ar[(BitVec.setWidth 64
                  (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
                    rw [hset, hrqi]
                    exact hrqi_lt)) + 3 + BitVec.setWidth 64 j).toNat]'hqwj_ar)).toNat <
                  s.core.repr.length := by
                rw [hrepr_len]; omega
              have hlmj_lift := fid_scan_cands_lmj_lift hlmj_inv hj_le
              have hl_lmj_lt : (ar[qw.toNat + 3 + j.toNat]'hqwj_ar_lt).toNat < lmj.length := by
                rw [hlmj_l]; exact Nat.lt_of_lt_of_le hl_lt (Nat.mul_le_mul_left 2 hcv_le)
              c0_hfast
              · have hgt : BitVec.toNat (1 : BitVec 32) < (fc + 1#32).toNat := by assumption
                rw [show BitVec.toNat (1 : BitVec 32) = 1 from rfl] at hgt
                exact hJmL ⟨min_l, min_d, fc + 1#32, j, lmj⟩ mj
                  ⟨hlmj_lift, fun h => absurd h (Nat.not_le_of_gt hgt), hmin_ok, hmj⟩
              · exact ihm (min_l, min_d, fc + 1#32, j + 1#32, ()) mj
                  (by dsimp only; rw [hj1]; omega)
                  ⟨lmj, by rw [hj1]; omega, by
                    have hngt : ¬ (1 : BitVec 32) < fc + 1#32 := by assumption
                    have hfc1_n : (fc + 1#32).toNat = fc.toNat + 1 := by simp only [bv_c0]; omega
                    have : ¬ 1 < (fc + 1#32).toNat := fun h =>
                      hngt (by change (1 : BitVec 32).toNat < (fc + 1#32).toNat; exact h)
                    omega, by rw [hj1]; exact lmBit2Inv_skip hlmj_inv,
                   fun _ => hlmj_res hfc_le, hmin_ok, hmj⟩
              · have hb0_32 : (BitVec.setWidth 32
                    (lmj[(ar[qw.toNat + 3 + j.toNat]'hqwj_ar_lt).toNat]'hl_lmj_lt) &&&
                    BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 1)) =
                    BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0) := by
                  have hqw3_mod : (qw.toNat + BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 =
                      qw.toNat + 3 := by
                    rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]
                    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.add_lt_add_right qw.isLt 3)
                      (by decide))
                  have hqwj_mod2 : (qw.toNat + 3 + j.toNat) % 2 ^ 64 = qw.toNat + 3 + j.toNat :=
                    Nat.mod_eq_of_lt (Nat.lt_trans
                      (Nat.add_lt_add (Nat.add_lt_add_right qw.isLt 3) j.isLt) (by decide))
                  have hidx_nat : qw.toNat + 3 + j.toNat =
                      (((sb[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by
                        rw [hrqi_mod]; exact hrqi_lt)).toNat +
                        BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 + j.toNat) % 2 ^ 64 := by
                    rw [hqw_mod, hqw3_mod, hqwj_mod2]
                  have hl_idx_eq : (ar[qw.toNat + 3 + j.toNat]'hqwj_ar_lt).toNat =
                      (ar[(((sb[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by
                        rw [hrqi_mod]; exact hrqi_lt)).toNat +
                        BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 + j.toNat) % 2 ^ 64]'(by
                        rw [← hidx_nat]; exact hqwj_ar_lt)).toNat := by
                    simp only [← hidx_nat]
                  simp only [hl_idx_eq]; assumption
                have ⟨hstep2, hres_next⟩ :=
                  fid_filter_row_mark_step hlm_len hcv_le hfr_b0 hres_perm_f
                  hlmj_inv (hlmj_res hfc_le) hqwj_ar_lt hqwj_lt hl_eq hl_mem hl_lt hb0_32
                refine ihm (_, _, fc, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
                  ⟨_, by rw [hj1]; omega, hfc_le, by rw [hj1]; exact hstep2,
                    fun _ => hres_next, fun _ => ?_, ?_⟩
                · simp only [hqw_eq, hqwj_n]; exact hl_lt
                · simp only [hqw_eq] at hm; simp only [hqwj_n, hset] at hm
                  try simp only [bv8_trunc_or_2] at hm
                  try simp only [bv8_trunc_or_w] at hm
                  exact hm
              · have hb0_32 : (BitVec.setWidth 32
                    (lmj[(ar[qw.toNat + 3 + j.toNat]'hqwj_ar_lt).toNat]'hl_lmj_lt) &&&
                    BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 1)) =
                    BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0) := by
                  have hqw3_mod : (qw.toNat + BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 =
                      qw.toNat + 3 := by
                    rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]
                    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.add_lt_add_right qw.isLt 3)
                      (by decide))
                  have hqwj_mod2 : (qw.toNat + 3 + j.toNat) % 2 ^ 64 = qw.toNat + 3 + j.toNat :=
                    Nat.mod_eq_of_lt (Nat.lt_trans
                      (Nat.add_lt_add (Nat.add_lt_add_right qw.isLt 3) j.isLt) (by decide))
                  have hidx_nat : qw.toNat + 3 + j.toNat =
                      (((sb[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by
                        rw [hrqi_mod]; exact hrqi_lt)).toNat +
                        BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 + j.toNat) % 2 ^ 64 := by
                    rw [hqw_mod, hqw3_mod, hqwj_mod2]
                  have hl_idx_eq : (ar[qw.toNat + 3 + j.toNat]'hqwj_ar_lt).toNat =
                      (ar[(((sb[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by
                        rw [hrqi_mod]; exact hrqi_lt)).toNat +
                        BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 + j.toNat) % 2 ^ 64]'(by
                        rw [← hidx_nat]; exact hqwj_ar_lt)).toNat := by
                    simp only [← hidx_nat]
                  simp only [hl_idx_eq]; assumption
                have ⟨hstep2, hres_next⟩ :=
                  fid_filter_row_mark_step hlm_len hcv_le hfr_b0 hres_perm_f
                  hlmj_inv (hlmj_res hfc_le) hqwj_ar_lt hqwj_lt hl_eq hl_mem hl_lt hb0_32
                refine ihm (_, _, fc, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
                  ⟨_, by rw [hj1]; omega, hfc_le, by rw [hj1]; exact hstep2,
                    fun _ => hres_next, fun _ => ?_, ?_⟩
                · simp only [hqw_eq, hqwj_n]; exact hl_lt
                · simp only [hqw_eq] at hm; simp only [hqwj_n, hset] at hm
                  try simp only [bv8_trunc_or_2] at hm
                  try simp only [bv8_trunc_or_w] at hm
                  exact hm
              · have hb0_32 : (BitVec.setWidth 32
                    (lmj[(ar[qw.toNat + 3 + j.toNat]'hqwj_ar_lt).toNat]'hl_lmj_lt) &&&
                    BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 1)) =
                    BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0) := by
                  have hqw3_mod : (qw.toNat + BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 =
                      qw.toNat + 3 := by
                    rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]
                    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.add_lt_add_right qw.isLt 3)
                      (by decide))
                  have hqwj_mod2 : (qw.toNat + 3 + j.toNat) % 2 ^ 64 = qw.toNat + 3 + j.toNat :=
                    Nat.mod_eq_of_lt (Nat.lt_trans
                      (Nat.add_lt_add (Nat.add_lt_add_right qw.isLt 3) j.isLt) (by decide))
                  have hidx_nat : qw.toNat + 3 + j.toNat =
                      (((sb[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by
                        rw [hrqi_mod]; exact hrqi_lt)).toNat +
                        BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 + j.toNat) % 2 ^ 64 := by
                    rw [hqw_mod, hqw3_mod, hqwj_mod2]
                  have hl_idx_eq : (ar[qw.toNat + 3 + j.toNat]'hqwj_ar_lt).toNat =
                      (ar[(((sb[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by
                        rw [hrqi_mod]; exact hrqi_lt)).toNat +
                        BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 + j.toNat) % 2 ^ 64]'(by
                        rw [← hidx_nat]; exact hqwj_ar_lt)).toNat := by
                    simp only [← hidx_nat]
                  simp only [hl_idx_eq]; assumption
                have ⟨hstep2, hres_next⟩ :=
                  fid_filter_row_mark_step hlm_len hcv_le hfr_b0 hres_perm_f
                  hlmj_inv (hlmj_res hfc_le) hqwj_ar_lt hqwj_lt hl_eq hl_mem hl_lt hb0_32
                refine ihm (min_l, min_d, fc, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
                  ⟨_, by rw [hj1]; omega, hfc_le, by rw [hj1]; exact hstep2,
                    fun _ => hres_next, hmin_ok, ?_⟩
                · simp only [hqw_eq] at hm; simp only [hqwj_n, hset] at hm
                  try simp only [bv8_trunc_or_2] at hm
                  try simp only [bv8_trunc_or_w] at hm
                  exact hm
            · have hj_eq : j.toNat = csz_bv.toNat := by
                apply Nat.le_antisymm hj_le
                apply Classical.byContradiction; intro hj_lt_c
                have hj_lt_w : j.toNat < (ar[(qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                    rw [hqw2_mod]; exact hqw2_lt)).toNat := by
                  rw [← hcsz_mod]; omega
                have hc_neg : ¬ j.toNat < (ar[((sb[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by
                    rw [hrqi_mod]; exact hrqi_lt)).toNat +
                      BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'_).toNat := ‹_›
                simp only [hqw_mod] at hc_neg
                exact hc_neg hj_lt_w
              rw [hj_eq] at hlmj_inv
              c0_hfast
              exact hJmL ⟨min_l, min_d, fc, j, lmj⟩ mj ⟨hlmj_inv, hlmj_res, hmin_ok, hmj⟩
      · exact hJend () ml rfl
    · exact hJend () ml rfl

end LeanQbe.T.Examples.Kissat.FullFidelityBva
