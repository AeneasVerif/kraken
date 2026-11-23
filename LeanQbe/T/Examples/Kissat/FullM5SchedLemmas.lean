module

public import LeanQbe.T.Examples.Kissat.FullM5Sched
public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Stage-3 M5 Scheduler Parity v2 `Func.wp` Proofs (`FullM5SchedLemmas`, UNSAT-Only)

Proves `Func.wp` for all `6` C0 functions in `FullM5Sched.lean` directly
against canonical `FullSpec` / `FullFastSched`-compatible contracts (strictly UNSAT-only, ZERO
SAT/model proofs):
1. `full_log10_q16_wp` against `m5Log10Q16Spec` (pure, `Mem`-preserving, `< 20 * 65536`,
   `10 ≤ x → 65536 ≤ r`).
2. `full_scale_delta_m5_wp` against `m5ScaleDeltaSpec` (matches
   `FullFastSched.schedScaleDeltaSpec`).
3. `full_ema_update_wp` against `Full.fullEmaUpdateSpec` (`Q32` precision + `Q24` init promotion).
4. `full_rephase_wp` against `m5RephaseSpec` (focused `stable == 0` guard above `full_backtrack`,
   reducing to `Full.fullRephaseSpec` whenever `stable ≠ 0`).
5. `full_switch_mode_wp` against `Full.fullSwitchModeSpec` (`NLOG4N` focused interval, `rel_*`
   and `Q32` EMA reset, no `dticks < 1000` floor).
6. `full_restart_due_wp` against `Full.fullRestartDueSpec` (`conflicts < restart_limit` before
   `stable`, exact `Q32` ratio comparison, `restarts + 1`).
7. Closed `10`-row `m5SchedSpecTable`, `m5SchedEnv`, `m5Sched_tableImpl`, and `m5Sched_moduleOk`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5Sched

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full hiding
  full_ema_update_body full_ema_update_wf
  full_rephase_body full_rephase_wf
  full_switch_mode_body full_switch_mode_wf
  full_restart_due_body full_restart_due_wf
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open Kraken.Bedrock2.Test

/-! ## 1. Specs & Pure Helpers -/

/-- Pure fixed-point `Q16` `log10(x)` contract (`< 20 * 65536`, and `≥ 65536` when `10 ≤ x`). -/
def m5Log10Q16Spec : Spec [i64] [i64] := fun (x, ()) m Q _ =>
  ∀ r : BitVec 64, r.toNat < 20 * 65536 → (10 ≤ x.toNat → 65536 ≤ r.toNat) → Q (r, ()) m

/-- Pure `full_scale_delta_m5` contract matching `FullFastSched.schedScaleDeltaSpec`. -/
def m5ScaleDeltaSpec : Spec [i64, i64] [i64] := fun (h, _delta, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧ ∀ r : BitVec 64, Q (r, ()) m

/-- M5 `full_rephase` contract: matches `Full.fullRephaseSpec` when `stable ≠ 0#64`, and allows
early return without `full_backtrack(h, 0ULL)` when `stable = 0#64`. -/
def m5RephaseSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ vals' lvl' rsns' trl' tp' te' prop' cl' unass' fuel' sc' m',
      let s' : FullState :=
        { core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                                trail_pos := tp', trail_end := te', propagated := prop',
                                cur_level := cl', unassigned := unass', fuel := fuel' }
          scratch := sc' }
      FullCoreInv c F0 s' → (s.scratch.stable ≠ 0#64 → cl' = 0) →
      cl' ≤ s.core.cur_level → fuel'.toNat ≤ s.core.fuel.toNat →
      FullExtScratchPres s s' → (FullMem c s' ⋆ R) m' → Q () m'

/-- When `s.scratch.stable ≠ 0#64`, `m5RephaseSpec` coincides with `Full.fullRephaseSpec`. -/
theorem m5RephaseSpec_of_stable {h : BitVec 64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hc : ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.scratch.stable ≠ 0#64 ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
      ∀ vals' lvl' rsns' trl' tp' te' prop' unass' fuel' sc' m',
        let s' : FullState :=
          { core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                                  trail_pos := tp', trail_end := te', propagated := prop',
                                  cur_level := 0, unassigned := unass', fuel := fuel' }
            scratch := sc' }
        FullCoreInv c F0 s' → fuel'.toNat ≤ s.core.fuel.toNat → FullExtScratchPres s s' →
        (FullMem c s' ⋆ R) m' → Q () m') :
    m5RephaseSpec (h, ()) m Q X := by
  rcases hc with ⟨c, F0, s, R, rfl, hst, hinv, hm, hQ⟩
  refine ⟨c, F0, s, R, rfl, hinv, hm, fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' fuel' sc'
      m' hinv' hcl _ hfu' hpres' hm' => ?_⟩
  have hcl0 : cl' = 0 := hcl hst
  subst hcl0
  exact hQ vals' lvl' rsns' trl' tp' te' prop' unass' fuel' sc' m' hinv' hfu' hpres' hm'

private theorem pow10_lt_64 {d : Nat} (hd : d ≤ 19) : 10 ^ d < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hd) (by decide)

private theorem wp_let_add64_m {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a b : Arg Val i64} {k : Tup Val [i64] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i64, i64], code := .add i64, args := (a, b, ()) } k) m =
      wp Γ Q X (k (a.val + b.val, ())) m := by
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, lift2] using
    @wp_let_add_eq Γ rs Q X m i64 (a, b, ()) k

private theorem wp_let_mul64_m {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a b : Arg Val i64} {k : Tup Val [i64] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i64, i64], code := .mul i64, args := (a, b, ()) } k) m =
      wp Γ Q X (k (a.val * b.val, ())) m := by
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, lift2] using
    @wp_let_mul_eq Γ rs Q X m i64 (a, b, ()) k

private theorem wp_let_ugt64_m {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {hm : Ty.bool = Ty.mask i64} {a b : Arg Val i64}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    wp Γ Q X
        (.let_ { sig := [i64, i64], code := .cmp .ugt i64 .bool hm, args := (a, b, ()) } k) m =
      wp Γ Q X (k (BitVec.ult b.val a.val, ())) m := by
  have hc := @wp_let_cmp_eq Γ rs Q X m .ugt i64 .bool hm (a, b, ()) k
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, liftCmp,
    evalBits_ugt_eq, cast_eq] using hc

private theorem wp_let_ult64_m {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {hm : Ty.bool = Ty.mask i64} {a b : Arg Val i64}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult i64 .bool hm) (a, b, ())) k) m =
      wp Γ Q X (k (BitVec.ult a.val b.val, ())) m := by
  have hc := @wp_let_cmp_eq Γ rs Q X m .ult i64 .bool hm (a, b, ()) k
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, liftCmp,
    evalBits_ult_eq, cast_eq] using hc

private theorem probePres_refl (s : Full.FullState) : Full.FullProbeScratchPres s s :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem probePres_trans {s₁ s₂ s₃ : Full.FullState}
    (h12 : Full.FullProbeScratchPres s₁ s₂) (h23 : Full.FullProbeScratchPres s₂ s₃) :
    Full.FullProbeScratchPres s₁ s₃ :=
  ⟨⟨h23.1.1.trans h12.1.1, h23.1.2.trans h12.1.2⟩, h23.2.1.trans h12.2.1,
   h23.2.2.1.trans h12.2.2.1, h23.2.2.2.1.trans h12.2.2.2.1,
   h23.2.2.2.2.1.trans h12.2.2.2.2.1, h23.2.2.2.2.2.1.trans h12.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.trans h12.2.2.2.2.2.2.2⟩

private theorem bv64_add1_toNat {k : BitVec 64} (hk : k.toNat + 1 < 2 ^ 64) :
    (k + 1#64).toNat = k.toNat + 1 := by
  bv_omega

section M5SchedTactics

open Lean Elab Tactic in
/-- Step straight-line `C0Step` ops, stopping at `Expr.group` instead of inlining join points. -/
local elab "m5_to_group" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let rawTy ← Lean.instantiateMVars (← g.getType)
      let ty := rawTy.consumeMData
      if rawTy.isMData then
        let g' ← g.change ty (checkDefEq := false)
        setGoals [g']
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out ++ (← getUnsolvedGoals)
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out ++ (← getUnsolvedGoals)
    setGoals out.toList
  go 500

open Lean Elab Tactic in
/-- Step straight-line `C0Step` ops on the main goal until `Expr.jnz`, then split it once. -/
local elab "m5_split" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let g ← getMainGoal
    let rawTy ← Lean.instantiateMVars (← g.getType)
    let ty := rawTy.consumeMData
    if rawTy.isMData then
      let g' ← g.change ty (checkDefEq := false)
      replaceMainGoal [g']
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← LeanQbe.T.C0Step.stepOnce; return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  go 100

open Lean Elab Tactic in
/-- Step all `C0Step` goals up to `Expr.jnz` (without splitting `jnz`). -/
local elab "m5_to_jnz" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let rawTy ← Lean.instantiateMVars (← g.getType)
      let ty := rawTy.consumeMData
      if rawTy.isMData then
        let g' ← g.change ty (checkDefEq := false)
        setGoals [g']
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
        out := out ++ (← getUnsolvedGoals)
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out ++ (← getUnsolvedGoals)
    setGoals out.toList
  go 500

open Lean Elab Tactic in
/-- Step straight-line `C0Step` ops until `OpCode.udiv`, `Expr.jnz`, or `Expr.group`. -/
local elab "m5_to_udiv" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let g ← getMainGoal
    let rawTy ← Lean.instantiateMVars (← g.getType)
    let ty := rawTy.consumeMData
    if rawTy.isMData then
      let g' ← g.change ty (checkDefEq := false)
      replaceMainGoal [g']
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
      let e := (ty.getArg! 4).headBeta
      if e.isAppOf ``LeanQbe.T.Expr.group || e.isAppOf ``LeanQbe.T.Expr.jnz then return
      let st ← saveState
      let isDiv ← try
        evalTactic (← `(tactic| refine wp_udiv_of ?_ ?_))
        pure true
      catch _ => pure false
      st.restore
      if isDiv then return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  go 100

local macro "solve_log10_tail" x:ident d:ident p:ident hp:ident hd10:ident m:ident hQ:ident :
    tactic => `(tactic| (
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64, i64])
    (fun (_, pm', ()) m2 => $m = m2 ∧ 1 ≤ pm'.toNat) ?_ ?_
  · rintro _ ⟨xm', pm', ⟨⟩⟩ m2 ⟨hm2, hpm⟩
    subst m2
    have hpm_ne : pm' ≠ 0#64 := by
      intro h0; subst h0; simp at hpm
    c0_hsteps_nogrp
    all_goals try exact hpm_ne
    refine wp_loop_inv (ts := [i64, i64, i64])
      (fun (_mv, frac, i, ()) m3 =>
        $m = m3 ∧ i.toNat ≤ 16 ∧ frac.toNat < 2 ^ i.toNat)
      (fun (_, _, i, ()) _ => 16 - i.toNat) ?_ ?_
    · intro J2 hJ2
      c0_hsteps; exact hJ2 (_, 0#64, 0#64, ()) $m ⟨Eq.refl _, by decide, by decide⟩
    · rintro J2 ⟨mv, frac, i, ⟨⟩⟩ m3 ⟨hm3, hi16, hfl⟩ hJ2
      subst m3
      c0_hsteps
      · have hi_lt : i.toNat < 16 := by c0_bound
        have hf_lt : frac.toNat < 2 ^ 15 :=
          Nat.lt_of_lt_of_le hfl (Nat.pow_le_pow_right (by omega) (by omega))
        have hf_sh : (frac <<< (1 : Nat)).toNat = 2 * frac.toNat := by
          rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
        have hf2_lt : 2 * frac.toNat < 2 ^ (i.toNat + 1) := by
          rw [Nat.pow_succ]; omega
        have hi1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
        have h16pow : 2 ^ (i.toNat + 1) ≤ 2 ^ 16 :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hf2p1 : (frac <<< (1 : Nat) + 1#64).toNat = 2 * frac.toNat + 1 := by bv_omega
        have hf2p1_lt : 2 * frac.toNat + 1 < 2 ^ (i.toNat + 1) := by
          rw [Nat.pow_succ]; omega
        exact hJ2 (_, (frac <<< (1 : Nat)) + 1#64, i + 1#64, ()) $m
          (by dsimp only; omega)
          ⟨Eq.refl _, by omega, by rw [hi1, hf2p1]; exact hf2p1_lt⟩
      · have hi_lt : i.toNat < 16 := by c0_bound
        have hf_lt : frac.toNat < 2 ^ 15 :=
          Nat.lt_of_lt_of_le hfl (Nat.pow_le_pow_right (by omega) (by omega))
        have hf_sh : (frac <<< (1 : Nat)).toNat = 2 * frac.toNat := by
          rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
        have hf2_lt : 2 * frac.toNat < 2 ^ (i.toNat + 1) := by
          rw [Nat.pow_succ]; omega
        have hi1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
        exact hJ2 (_, frac <<< (1 : Nat), i + 1#64, ()) $m
          (by dsimp only; omega)
          ⟨Eq.refl _, by omega, by rw [hi1, hf_sh]; exact hf2_lt⟩
      · have hflt : frac.toNat < 65536 :=
          Nat.lt_of_lt_of_le hfl (Nat.pow_le_pow_right (by omega) hi16)
        have hd_sh : (($d) <<< (16 : Nat)).toNat = ($d).toNat * 65536 := by
          rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
        have hres_lt : ((($d) <<< (16 : Nat)) + frac).toNat < 20 * 65536 := by
          have hsum : ($d).toNat * 65536 + frac.toNat < 20 * 65536 := by omega
          have h64 : ($d).toNat * 65536 + frac.toNat < 2 ^ 64 := by omega
          rw [BitVec.toNat_add, hd_sh, Nat.mod_eq_of_lt h64]; exact hsum
        have hres_ge : 10 ≤ ($x).toNat →
            65536 ≤ ((($d) <<< (16 : Nat)) + frac).toNat := by
          intro hx10
          have hd1 := $hd10 hx10
          have hsum : 65536 ≤ ($d).toNat * 65536 + frac.toNat := by omega
          have h64 : ($d).toNat * 65536 + frac.toNat < 2 ^ 64 := by omega
          rw [BitVec.toNat_add, hd_sh, Nat.mod_eq_of_lt h64]; exact hsum
        exact $hQ ((($d) <<< (16 : Nat)) + frac) hres_lt hres_ge
  · intro _ hJm
    c0_hsteps_nogrp
    · have hpm_gt : 100000000 < ($p).toNat := by c0_bound
      intro h0
      have ht := congrArg BitVec.toNat h0
      change ($p).toNat / 100000000 = 0 at ht
      have hpos : 0 < ($p).toNat / 100000000 :=
        Nat.div_pos (Nat.le_of_lt hpm_gt) (by decide)
      omega
    · exact hJm ($x / ($p / 100000000#64), 100000000#64, ()) $m ⟨Eq.refl _, by decide⟩
    · exact hJm ($x, $p, ()) $m ⟨Eq.refl _, $hp⟩))

/-! ## 2. `full_log10_q16` & `full_scale_delta_m5` `Func.wp` Proofs -/

theorem full_log10_q16_wp (Γ : Env) :
    ∀ a m Q X, m5Log10Q16Spec a m Q X → Func.wp Γ full_log10_q16_body a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  c0_hsteps_nogrp
  · have hx1 : x.toNat ≤ 1 := by c0_bound
    exact hQ 0#64 (by decide) (fun hx10 => by omega)
  · refine wp_loop_inv (ts := [i64, i64])
      (fun (d, pow10, ()) m1 =>
        m = m1 ∧ d.toNat ≤ 19 ∧ 1 ≤ pow10.toNat ∧ pow10.toNat ≤ 10 ^ d.toNat ∧
        (d.toNat = 0 → pow10.toNat = 1))
      (fun (d, _, ()) _ => 19 - d.toNat) ?_ ?_
    · intro J hJ
      c0_hsteps; exact hJ (0#64, 1#64, ()) m ⟨rfl, by decide, by decide, by decide, fun _ => rfl⟩
    · rintro J ⟨d, pow10, ⟨⟩⟩ _ ⟨rfl, hd19, hp1, hple, hd0p⟩ hJ
      refine wp_join_group (ts := []) (fun _ m1 => m = m1 ∧ (10 ≤ x.toNat → 1 ≤ d.toNat))
        ?_ ?_
      · rintro _ ⟨⟩ _ ⟨rfl, hd10⟩
        solve_log10_tail x d pow10 hp1 hd10 m hQ
      · intro _ hJexit
        c0_hsteps_nogrp
        · have hd_lt : d.toNat < 19 := by c0_bound
          have hpow_10 : pow10.toNat * 10 ≤ 10 ^ (d.toNat + 1) := by
            rw [Nat.pow_succ]; exact Nat.mul_le_mul_right 10 hple
          have hpow_lt64 : pow10.toNat * 10 < 2 ^ 64 :=
            Nat.lt_of_le_of_lt hpow_10 (pow10_lt_64 (by omega))
          have hd1 : (d + 1#64).toNat = d.toNat + 1 := by bv_omega
          have hp10' : (pow10 * 10#64).toNat = pow10.toNat * 10 := by
            rw [BitVec.toNat_mul, show (10#64).toNat = 10 from rfl,
              Nat.mod_eq_of_lt hpow_lt64]
          exact hJ (d + 1#64, pow10 * 10#64, ()) m (by dsimp only; omega)
            ⟨rfl, by omega, by omega, by rw [hd1, hp10']; exact hpow_10,
             fun h0 => by rw [hd1] at h0; omega⟩
        · have hge : 19 ≤ d.toNat := by c0_bound
          exact hJexit () m ⟨rfl, fun _ => by omega⟩
        · have hlt : x.toNat / 10 < pow10.toNat := by
            have hdiv : (x / 10#64).toNat < pow10.toNat := by c0_bound
            have hmod : (x / 10#64).toNat = x.toNat / 10 := by bv_omega
            omega
          refine hJexit () m ⟨rfl, fun hx10 => ?_⟩
          rcases Nat.eq_zero_or_pos d.toNat with hd0 | hdpos
          · have hp1' := hd0p hd0; omega
          · exact hdpos

theorem full_scale_delta_m5_wp (Γ : Env)
    (hLog : ∀ a m Q X, m5Log10Q16Spec a m Q X → Γ "full_log10_q16" [i64] [i64] a m Q X) :
    ∀ a m Q X, m5ScaleDeltaSpec a m Q X → Func.wp Γ full_scale_delta_m5_body a m Q X := by
  rintro ⟨h, delta, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, _, hm, hQ⟩
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun _ m1 => m = m1) ?_ ?_
  · rintro _ ⟨_cx, ⟨⟩⟩ _ rfl
    c0_hsteps_nogrp
    c0_call hLog
    intro q _ _
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m2 => m = m2) ?_ ?_
    · rintro _ ⟨_diff, ⟨⟩⟩ _ rfl
      c0_hsteps
      · exact hQ _
      · exact hQ _
    · intro _ hJd; c0_hsteps
      · exact hJd _ m rfl
      · exact hJd _ m rfl
  · intro _ hJc; c0_hsteps
    · exact hJc _ m rfl
    · exact hJc _ m rfl

/-! ## 3. `full_ema_update` `Func.wp` Proof -/

theorem full_ema_update_wp (Γ : Env) :
    ∀ a m Q X, Full.fullEmaUpdateSpec a m Q X → Func.wp Γ full_ema_update_body a m Q X := by
  rintro ⟨h, glue, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [Full.fullSafetySlice] at hm hlen hQ
  c0_hsteps_nogrp
  · exact hQ () s m rfl hlen (probePres_refl s) hm
  · refine wp_join_group (ts := [i64]) (fun _ m1 => m = m1) (fun _ _ _ hm1 => ?_) ?_
    · rcases hm1 with rfl; c0_hsteps_nogrp
      refine wp_join_group (ts := [i64, i64]) (fun _ m2 => m = m2)
        (fun _ (fe, se, ()) _ hm2 => ?_) ?_
      · rcases hm2 with rfl; c0_hsteps_nogrp
        refine wp_join_group (ts := [i64]) (fun _ m3 => m = m3) (fun _ (fb, ()) _ hm3 => ?_) ?_
        · rcases hm3 with rfl; c0_hsteps_nogrp
          refine wp_join_group (ts := [])
            (fun _ m4 => ∃ s1 : Full.FullState, PreservesCoreSlice Full.FullState.core s s1 ∧
              s1.LengthsOk c ∧ Full.FullProbeScratchPres s s1 ∧ (Full.FullMem c s1 ⋆ R) m4)
            (fun _ _ m4 ⟨s1, hcore1, hlen1, hpres1, hm4⟩ => ?_) ?_
          · clear hm
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64]) (fun _ m5 => m4 = m5)
              (fun _ (sb, ()) _ hm5 => ?_) ?_
            · rcases hm5 with rfl; c0_hsteps
              all_goals
                refine hQ () _ m ?_ ?_ ?_ hm
                · exact hcore1
                · exact hlen1.with_scratch
                    { hlen1.scratch_ok with walk_vals_len := hlen1.scratch_ok.walk_vals_len }
                · exact ⟨hpres1.1, hpres1.2.1, hpres1.2.2.1, hpres1.2.2.2.1, hpres1.2.2.2.2.1,
                    hpres1.2.2.2.2.2.1, hpres1.2.2.2.2.2.2.1, hpres1.2.2.2.2.2.2.2⟩
            · intro _ hJsb; c0_hsteps <;> exact hJsb _ m4 rfl
          · intro _ hJfe
            c0_hsteps
            all_goals
              refine hJfe () m ⟨_, ?_, ?_, ?_, hm⟩
              · exact rfl
              · exact hlen.with_scratch
                  { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len }
              · exact probePres_refl s
        · intro _ hJfb; c0_hsteps <;> exact hJfb _ m rfl
      · intro _ hJfe; c0_hsteps <;> exact hJfe _ m rfl
    · intro _ hJg; c0_hsteps <;> exact hJg _ m rfl

/-! ## 4. `full_restart_due` `Func.wp` Proof -/

private theorem fullState_lengths_with_restart_limit {c : Full.FullCfg} {s : Full.FullState}
    (h : s.LengthsOk c) (v : BitVec 64) :
    ({ s with scratch := { s.scratch with restart_limit := v } } : Full.FullState).LengthsOk c :=
  h.with_scratch { h.scratch_ok with walk_vals_len := h.scratch_ok.walk_vals_len }

theorem full_restart_due_wp (Γ : Env)
    (hIlog : ∀ a m Q X, Full.fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullRestartDueSpec a m Q X → Func.wp Γ full_restart_due_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_coreProj,
    Full.fullSafetySlice_safe] at hlen hm hQ
  c0_step; m5_split
  · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm
  · m5_split
    · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm
    · m5_split
      · m5_split
        · c0_steps
          let sc' : Full.FullScratch := { s.scratch with rel_trigger := 0#64 }
          have hlen' : ({ s with scratch := sc' } : Full.FullState).LengthsOk c :=
            hlen.with_scratch
              { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len }
          exact hQ (1#64, ()) { s with scratch := sc' } _ rfl hlen' ⟨Or.inr rfl, rfl, rfl⟩ hm
        · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm
      · m5_to_jnz
        refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
        · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm
        · m5_to_jnz
          refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
          · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm
          · m5_to_jnz
            refine wp_jnz_of (fun _ => ?_) (fun hfd_ne => ?_)
            · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm
            · m5_to_jnz
              refine wp_jnz_of (fun _ => ?_) (fun hsd_ne => ?_)
              · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm
              · simp only [Arg.val_var] at hfd_ne hsd_ne
                c0_cond hfd_ne
                c0_cond hsd_ne
                have hfd_nz : (1#64 <<< 32 - s.scratch.ema_fast_exp) ≠ 0#64 := hfd_ne
                have hsd_nz : (1#64 <<< 32 - s.scratch.ema_slow_exp) ≠ 0#64 := hsd_ne
                m5_to_group
                refine wp_join_group (ts := [i64]) (fun _ m1 => m = m1)
                  (fun _ (fbc, ()) _ hm1 => ?_) ?_
                · rcases hm1 with rfl; m5_to_group
                  refine wp_join_group (ts := [i64]) (fun _ m2 => m = m2)
                    (fun _ (sbc, ()) _ hm2 => ?_) ?_
                  · rcases hm2 with rfl
                    m5_to_udiv
                    refine wp_udiv_of
                      (by simp only [Arg.val_var]; exact hfd_nz) ?_
                    m5_to_udiv
                    refine wp_udiv_of
                      (by simp only [Arg.val_var]; exact hsd_nz) ?_
                    m5_to_group
                    refine wp_join_group (ts := [i64]) (fun _ m3 => m = m3)
                      (fun _ (fval, ()) _ hm3 => ?_) ?_
                    · rcases hm3 with rfl
                      m5_to_group
                      refine wp_join_group (ts := [i64]) (fun _ m4 => m = m4)
                        (fun _ (sval, ()) _ hm4 => ?_) ?_
                      · rcases hm4 with rfl
                        m5_to_jnz
                        refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
                        · m5_to_group
                          refine wp_join_group (ts := [i64]) (fun _ m5 => m = m5)
                            (fun _ (rst, ()) _ hm5 => ?_) ?_
                          · rcases hm5 with rfl
                            m5_to_group
                            c0_call hIlog
                            intro d10 _ _
                            m5_to_group
                            refine wp_join_group (ts := [i64]) (fun _ m6 => m = m6)
                              (fun _ (delta, ()) _ hm6 => ?_) ?_
                            · rcases hm6 with rfl
                              c0_steps
                              let sc' : Full.FullScratch :=
                                { s.scratch with restart_limit := s.scratch.conflicts + delta }
                              exact hQ (1#64, ()) { s with scratch := sc' } _ rfl
                                (fullState_lengths_with_restart_limit hlen _)
                                ⟨Or.inr rfl, rfl, rfl⟩ hm
                            · intro _ hJd; c0_steps
                              · exact hJd (d10 - 1#64, ()) m rfl
                              · exact hJd (1#64, ()) m rfl
                          · intro _ hJrc; c0_steps
                            · exact hJrc (s.scratch.restarts + 1#64, ()) m rfl
                            · exact hJrc (1000000000000#64, ()) m rfl
                        · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm
                      · intro _ hJs; c0_steps
                        · exact hJs (1#64 <<< 32, ()) m rfl
                        · exact hJs (_, ()) m rfl
                    · intro _ hJf; c0_steps
                      · exact hJf (1#64 <<< 32, ()) m rfl
                      · exact hJf (_, ()) m rfl
                  · intro _ hJsb; c0_steps
                    · exact hJsb (16384#64 <<< 32, ()) m rfl
                    · exact hJsb (s.scratch.ema_slow_biased, ()) m rfl
                · intro _ hJfb; c0_steps
                  · exact hJfb (16384#64 <<< 32, ()) m rfl
                  · exact hJfb (s.scratch.ema_fast_biased, ()) m rfl

/-! ## 5. `full_switch_mode` `Func.wp` Proof -/

theorem full_switch_mode_wp (Γ : Env)
    (hDown : ∀ a m Q X, Full.fullHeapDownSpec a m Q X → Γ "full_heap_down" [i64, i32] [] a m Q X)
    (hLog : ∀ a m Q X, m5Log10Q16Spec a m Q X → Γ "full_log10_q16" [i64] [i64] a m Q X)
    (hIlog : ∀ a m Q X, Full.fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullSwitchModeSpec a m Q X → Func.wp Γ full_switch_mode_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_coreProj,
    Full.fullSafetySlice_safe] at hlen hm hQ
  obtain hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  obtain hcv_le := hlen.core_ok.cur_vars_le
  m5_to_group
  refine wp_join_safety_slice (Full.fullSafetySlice c) s R (fun _ => True) trivial
    (fun s1 _ => Full.FullProbeScratchPres s s1)
    (fun J_out s1 _ m1 hcore1 hs1 _ hpres1 hm1 => ?_) (fun J_out hJ_out => ?_)
  · dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_coreProj,
      Full.fullSafetySlice_safe] at hs1 hm1
    clear hm
    let s1a : Full.FullState :=
      { s1 with scratch :=
        { s1.scratch with
          switched := s1.scratch.switched + 1#64
          mode_count := s1.scratch.mode_count + 1#64
          ema_fast_biased := 0#64
          ema_fast_exp := 1#64 <<< 32
          ema_slow_biased := 0#64
          ema_slow_exp := 1#64 <<< 32 } }
    c0_hsteps_nogrp
    refine wp_unroll_group fun Jret hJret => ?_
    c0_hsteps_nogrp
    · refine wp_join_group (ts := [i64]) (fun _ m2 => (Full.FullMem c s1a ⋆ R) m2)
        (fun _ (delta, ()) m2 hm2 => ?_) ?_
      · try clear hm
        c0_hsteps
        try (apply hJret; rw [Blocks.get_here]; c0_hsteps)
        let s2 : Full.FullState :=
          { s1a with scratch :=
            { s1a.scratch with restart_limit := s1a.scratch.conflicts + delta } }
        exact hQ () s2 _ hcore1
          (hs1.with_scratch
            { hs1.scratch_ok with walk_vals_len := hs1.scratch_ok.walk_vals_len })
          hpres1 hm
      · intro _ hJd
        c0_hsteps_nogrp
        · refine wp_join_group (ts := [i64]) (fun _ m2 => (Full.FullMem c s1a ⋆ R) m2)
            (fun _ (rc, ()) m2 hm2 => ?_) ?_
          · try clear hm
            c0_hsteps_nogrp
            c0_call hIlog
            intro d10 _ _
            c0_hsteps
            · exact hJd (d10 - 1#64, ()) _ hm2
            · exact hJd (1#64, ()) _ hm2
          · intro _ hJrc; c0_hsteps
            · exact hJrc (s1a.scratch.restarts, ()) _ hm
            · exact hJrc (1000000000000#64, ()) _ hm
        · exact hJd (1#64, ()) _ hm
    · try (apply hJret; rw [Blocks.get_here]; c0_hsteps)
      exact hQ () s1a _ hcore1
        (hs1.with_scratch { hs1.scratch_ok with walk_vals_len := hs1.scratch_ok.walk_vals_len })
        hpres1 hm
  · m5_split
    · m5_split
      · c0_steps; exact hQ () s m rfl hlen (probePres_refl s) hm
      · clear hQ
        m5_to_group
        refine wp_join_safety_slice (Full.fullSafetySlice c)
          { s with scratch := { s.scratch with stable := 1#64 } } R (fun _ => True) trivial
          (fun s1 _ => Full.FullProbeScratchPres s s1)
          (fun Jrp s1 ((rp : BitVec 64), ()) m1 hcore1 hs1 _ hpres1 hm1 => ?_)
          (fun Jrp hJrp => ?_)
        · clear hm hlen
          dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_coreProj,
            Full.fullSafetySlice_safe] at hs1 hm1
          have heq1 := Full.fullCoreState_agrees_with_scratch hcore1
          c0_hsteps_nogrp
          let s1' : Full.FullState :=
            { s1 with scratch :=
              { s1.scratch with
                rel_wait := rp
                rel_u := 1#64
                rel_v := 1#64
                rel_trigger := 0#64 } }
          refine wp_loop_safety_slice (ts := [i64, i64]) (Full.fullSafetySlice c) s1' R
            (fun _ => True) trivial
            (fun s2 ((n : BitVec 64), (v : BitVec 64), ()) => n.toNat ≤ v.toNat ∧
              v.toNat ≤ s.core.cur_vars ∧ Full.FullProbeScratchPres s s2)
            (fun (_, (v : BitVec 64), ()) => s.core.cur_vars - v.toNat)
            (fun Jl hJl => ?_)
            (fun Jl s2 ((n : BitVec 64), (v : BitVec 64), ()) m2 hcore2 hs2 _
                ⟨hnle, hvle, hpres2⟩ hm2 hJl => ?_)
          · c0_steps
            refine hJl _ (0#64, 0#64, ()) m hm rfl ?_ ⟨by simp, by simp, hpres1⟩
            exact hs1.with_scratch
              { hs1.scratch_ok with walk_vals_len := hs1.scratch_ok.walk_vals_len }
          · dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_coreProj,
              Full.fullSafetySlice_safe] at hs2 hm2
            have heq2 := Full.fullCoreState_agrees_with_scratch hcore2
            obtain hfl2 := hs2.core_ok.flags_len
            obtain hvl2 := hs2.core_ok.vals_len
            obtain hhl2 := hs2.scratch_ok.heap_len_arr
            obtain hpl2 := hs2.scratch_ok.pos_len
            repeat clear hc
            clear hm
            rw [Blocks.get_here]; dsimp only
            rw [wp_let_ult64_m]
            refine wp_jnz_of (fun hc => ?_) (fun hc => ?_)
            · simp only [Arg.val_var] at hc; c0_cond hc
              have hv_lt : v.toNat < s.core.cur_vars := by
                rw [heq1] at hc
                first | exact hc | {
                  have hc_v' : v.toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by
                    simpa using hc
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc_v'
                  exact hc_v' }
              have hv_fl : v.toNat < s2.core.flags.length := by rw [hfl2]; omega
              have hv1 : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
              refine wp_join_safety_slice (ts := [i64]) (Full.fullSafetySlice c) s2 R
                (fun _ => True) trivial
                (fun s2' ((n' : BitVec 64), ()) =>
                  n'.toNat ≤ v.toNat + 1 ∧ Full.FullProbeScratchPres s s2')
                (fun Js s2' ((n' : BitVec 64), ()) m2' hcore2' hs2' _ ⟨hn'le, hpres2'⟩
                    hm2' => ?_)
                (fun Js hJs => ?_)
              · dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_coreProj,
                  Full.fullSafetySlice_safe] at hs2' hm2'
                c0_steps
                exact hJl s2' (n', v + 1#64, ()) m2' hm2' (by dsimp only; rw [hv1]; omega)
                  hcore2' hs2' ⟨by rw [hv1]; omega, by rw [hv1]; omega, hpres2'⟩
              · refine wp_join_safety_slice (ts := []) (Full.fullSafetySlice c) s2 R
                  (fun _ => True) trivial
                  (fun s2' _ => Full.FullProbeScratchPres s s2')
                  (fun Js1 s2' _ m2' hcore2' hs2' _ hpres2' hm2' => ?_)
                  (fun Js1 hJs1 => ?_)
                · dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_coreProj,
                    Full.fullSafetySlice_safe] at hs2' hm2'
                  have hv_pos : v.toNat < s2'.scratch.pos.length := by
                    rw [hs2'.scratch_ok.pos_len]; omega
                  rw [Blocks.get_here]; dsimp only
                  c0_steps
                  refine wp_store_sep (FullArenaTactics.c0_store_full_pos _ hv_pos hm2')
                    fun m hm => ?_
                  c0_steps
                  exact hJs _ (n, ()) _ hm hcore2'
                    (hs2'.with_scratch { hs2'.scratch_ok with
                      pos_len := by simp [hs2'.scratch_ok.pos_len] })
                    ⟨by omega, hpres2'⟩
                · m5_split
                  · have hv2 : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
                      rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
                    have hv2_lt : (v <<< (1 : Nat)).toNat < s2.core.vals.length := by
                      rw [hvl2, hv2]; omega
                    refine wp_load_of (FullArenaTactics.c0_load_full_vals hv2_lt hm2) ?_
                    m5_split
                    · have hn_lt : n.toNat < s2.scratch.heap.length := by rw [hhl2]; omega
                      have hv_pos : v.toNat < s2.scratch.pos.length := by rw [hpl2]; omega
                      have hn1 : (n + 1#64).toNat = n.toNat + 1 := by bv_omega
                      c0_steps
                      refine wp_store_sep (FullArenaTactics.c0_store_full_heap _ hn_lt hm2)
                        fun m_h hm_h => ?_
                      clear hm2
                      c0_steps
                      exact hJs _ (n + 1#64, ()) _ hm rfl
                        (hs2.with_scratch { hs2.scratch_ok with
                          heap_len_arr := by simp [hhl2], pos_len := by simp [hpl2] })
                        ⟨by rw [hn1]; omega, hpres2⟩
                    · exact hJs1 s2 () m2 hm2 rfl hs2 hpres2
                  · exact hJs1 s2 () m2 hm2 rfl hs2 hpres2
            · clear hJl
              c0_steps
              refine wp_loop_safety_slice (Full.fullSafetySlice c)
                { s2 with scratch := { s2.scratch with heap_len := n.toNat } } R
                (fun _ => True) trivial
                (fun s3 ((sp : BitVec 64), ()) => sp.toNat ≤ c.max_vars ∧
                  Full.FullProbeScratchPres s s3)
                (fun ((sp : BitVec 64), ()) => sp.toNat)
                (fun Js hJs => ?_)
                (fun Js s3 ((sp : BitVec 64), ()) m3 hcore3 hs3 _ ⟨hsple, hpres3⟩ hm3
                    hJs => ?_)
              · c0_steps
                refine hJs _ (n >>> (1 : Nat), ()) _ hm rfl
                  (hs2.with_scratch { hs2.scratch_ok with
                    walk_vals_len := hs2.scratch_ok.walk_vals_len })
                  ⟨by rw [BitVec.toNat_ushiftRight]; simp [Nat.shiftRight_eq_div_pow]; omega,
                    hpres2⟩
              · dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_coreProj,
                  Full.fullSafetySlice_safe] at hs3 hm3
                obtain hhl3 := hs3.scratch_ok.heap_len_arr
                c0_steps
                · have hsp_pos : 0 < sp.toNat := by omega
                  have hsm1 : (sp - 1#64).toNat < sp.toNat := by bv_omega
                  c0_call hDown
                  refine ⟨c, s3, R, rfl, hs3, hm3, ?_⟩
                  intro _ s4 m4 hcore4 hs4 ⟨_, hpres34⟩ hm4
                  exact hJs s4 (sp - 1#64, ()) m4 hm4 hsm1 hcore4 hs4
                    ⟨by omega, probePres_trans hpres3 hpres34⟩
                · exact hJ_out s3 () m3 hm3 (hcore1.trans (hcore2.trans hcore3)) hs3 hpres3
        · c0_steps
          · exact hJrp _ (s.scratch.rel_limit, ()) _ hm rfl
              (hlen.with_scratch
                { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len })
              (probePres_refl s)
          · exact hJrp _ (s.scratch.rel_period, ()) _ hm rfl
              (hlen.with_scratch
                { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len })
              (probePres_refl s)
          · exact hJrp _ (s.scratch.rel_period, ()) _ hm rfl
              (hlen.with_scratch
                { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len })
              (probePres_refl s)
    · m5_split
      · c0_steps; exact hQ () s m rfl hlen (probePres_refl s) hm
      · clear hQ
        obtain hqsl := hlen.scratch_ok.q_stamp_len
        let s0 : Full.FullState := { s with scratch := { s.scratch with stable := 0#64 } }
        m5_to_group
        refine wp_join_group (ts := [i64]) (fun _ m1 => (Full.FullMem c s0 ⋆ R) m1)
          (fun _ (cc, ()) m1 hm1 => ?_) ?_
        · clear hm
          m5_to_group
          c0_call hLog
          intro q _ _
          m5_to_group
          refine wp_join_group (ts := [i64]) (fun _ m2 => (Full.FullMem c s0 ⋆ R) m2)
            (fun _ (scaled, ()) m2 hm2 => ?_) ?_
          · clear hm1
            c0_steps
            · refine wp_load_of (FullArenaTactics.c0_load_full_q_stamp ?_ hm) ?_
              · dsimp only [s0] at hc ⊢; rw [hqsl]; bv_omega
              c0_steps
              refine hJ_out _ () m hm ?_ ?_ ?_
              · exact rfl
              · exact hlen.with_scratch
                  { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len }
              · exact probePres_refl s
            · c0_steps
              refine hJ_out _ () m hm ?_ ?_ ?_
              · exact rfl
              · exact hlen.with_scratch
                  { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len }
              · exact probePres_refl s
          · intro _ hJsc
            m5_split
            · c0_steps; exact hJsc (_, ()) m1 hm1
            · m5_to_group
              refine wp_join_group (ts := [i64]) (fun _ m2 => m1 = m2)
                (fun _ (clim, ()) _ hm2 => ?_) ?_
              · rcases hm2 with rfl; c0_steps; exact hJsc (_, ()) m1 hm1
              · intro _ hJcl; c0_steps
                · exact hJcl (100000000#64, ()) m1 rfl
                · exact hJcl (_, ()) m1 rfl
        · intro _ hJcc; c0_steps
          · exact hJcc (_, ()) _ (by assumption)
          · exact hJcc (1000000000000#64, ()) _ (by assumption)

/-! ## 6. `full_rephase` `Func.wp` Proof -/

theorem full_rephase_wp (Γ : Env)
    (hBt : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hWalk : ∀ a m Q X, Full.fullWalkSpec a m Q X → Γ "full_walk" [i64] [] a m Q X)
    (hLog : ∀ a m Q X, m5Log10Q16Spec a m Q X →
      Γ "full_log10_q16" [i64] [i64] a m Q X) :
    ∀ a m Q X, m5RephaseSpec a m Q X → Func.wp Γ full_rephase_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  obtain ⟨F_cur, hw0⟩ := hinv.witness
  have hco0 := hinv.lengths.core_ok
  have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
    have := hw0.cur_level_le; have := hco0.trail_end_le; have := hco0.cur_vars_le; omega
  have hmaxv_pos : (0 : BitVec 64).toNat < s.core.cur_level →
      (0 : BitVec 64).toNat < c.max_vars := by
    intro _; have := hw0.cur_level_le; have := hco0.trail_end_le
    have := hco0.cur_vars_le; omega
  c0_hsplit
  · c0_hsteps
    let sc_early : Full.FullScratch := { s.scratch with rephase_limit := s.scratch.mode_confl_lim }
    have hsc_early : sc_early.LengthsOk c :=
      { hinv.lengths.scratch_ok with walk_vals_len := hinv.lengths.scratch_ok.walk_vals_len }
    have hinv_e : Full.FullCoreInv c F0
        { core := { s.core with fuel := s.core.fuel }, scratch := sc_early } :=
      hinv.with_fuel_scratch_spec ⟨hinv.lengths.core_ok, hsc_early⟩ rfl
    exact hQ s.core.vals s.core.lvl s.core.rsns s.core.trl s.core.trail_pos s.core.trail_end
      s.core.propagated s.core.cur_level s.core.unassigned s.core.fuel sc_early _
      hinv_e (fun hst => absurd hc hst) (Nat.le_refl _) (Nat.le_refl _) ⟨rfl, rfl⟩ hm
  · c0_hsteps_nogrp
    c0_call hBt
    refine ⟨c, s, R, rfl, hinv.lengths, hcl_lt64, hmaxv_pos, hw0.trail_lits_lt, hm,
      fun vals' lvl' rsns' trl' tp' te' prop' cl' unas' sc1 m1
        hlen1 _ _ hcl' hpres1 _ _ _ hwinv1 _ hm1 => ?_⟩
    have hw1 : Full.FullWitnessInv c F0 F_cur
        { s.core with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', propagated := prop', cur_level := cl', unassigned := unas' } :=
      hwinv1 F0 F_cur hw0 (Nat.zero_le _)
    have hcl'0 : cl' = 0 := by rw [hcl']; exact Nat.min_zero _
    subst hcl'0
    let st1 : Full.FullState :=
      { core := { s.core with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', propagated := prop', cur_level := 0,
          unassigned := unas' }
        scratch := sc1 }
    have hinv1 : Full.FullCoreInv c F0 st1 := ⟨hlen1, F_cur, hw1⟩
    have hcv_le : s.core.cur_vars ≤ c.max_vars := hinv1.lengths.core_ok.cur_vars_le
    have hll1 : sc1.last_learned = s.scratch.last_learned := hpres1.1.1
    have hext1 : sc1.extend_len = s.scratch.extend_len := hpres1.1.2
    clear hm
    c0_hsteps_nogrp
    let sc2 : Full.FullScratch := { sc1 with rephased := sc1.rephased + 1#64 }
    have hsc2_ok : sc2.LengthsOk c :=
      { hinv1.lengths.scratch_ok with walk_vals_len := hinv1.lengths.scratch_ok.walk_vals_len }
    let st2 : Full.FullState := { st1 with scratch := sc2 }
    have hinv2 : Full.FullCoreInv c F0 st2 :=
      hinv1.with_fuel_scratch_spec ⟨hinv1.lengths.core_ok, hsc2_ok⟩ rfl
    refine wp_join_group (fun (_k, ()) m2 => ∃ (fuel' : BitVec 64) (sc3 : Full.FullScratch),
      sc3.LengthsOk c ∧ fuel'.toNat ≤ s.core.fuel.toNat ∧
      sc3.last_learned = s.scratch.last_learned ∧ sc3.extend_len = s.scratch.extend_len ∧
      (Full.FullMem c { core := { st1.core with fuel := fuel' }, scratch := sc3 } ⋆ R) m2) ?_ ?_
    · rintro _ ⟨_k, ⟨⟩⟩ m2 ⟨fuel', sc3, hsc3, hfl3, hll3, hext3, hm2⟩
      try clear hm hm1
      refine wp_loop_inv
        (fun (k, ()) m3 => ∃ ptgt' : List (BitVec 8),
          k.toNat ≤ s.core.cur_vars ∧ ptgt'.length = c.max_vars ∧
          (Full.FullMem c
            { core := { st1.core with fuel := fuel' }
              scratch := { sc3 with phases_target := ptgt' } } ⋆ R) m3)
        (fun (k, ()) _ => s.core.cur_vars - k.toNat)
        (fun L hL => by
          c0_steps
          exact hL (0#64, ()) m2 ⟨sc3.phases_target, Nat.zero_le _, hsc3.phases_target_len, hm2⟩)
        (fun L (k, ()) m3 ⟨ptgt', hk_le, hpt_len, hm3⟩ ih => ?_)
      clear hm2
      have hph3 := hsc3.phases_len
      m5_to_group
      · have hk_lt : k.toNat < s.core.cur_vars := by c0_bound
        have hk1 : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
        exact ih (k + 1#64, ()) _ (by dsimp only; omega)
          ⟨ptgt'.set k.toNat (sc3.phases[k.toNat]'(by omega)), by omega, by simp [hpt_len], hm⟩
      · let st3 : Full.FullState :=
          { core := { st1.core with fuel := fuel' }
            scratch := { sc3 with phases_target := ptgt', target_assigned := 0#64 } }
        refine wp_join_group (ts := [i64]) (fun _ m4 => (Full.FullMem c st3 ⋆ R) m4)
          (fun _ (nc, ()) m4 hm4 => ?_) ?_
        · try clear hm3 hm
          m5_to_group
          c0_call hLog
          intro q _ _
          refine wp_join_group (ts := [i64]) (fun _ m5 => (Full.FullMem c st3 ⋆ R) m5)
            (fun _ (sc_val, ()) m5 hm5 => ?_) ?_
          · try clear hm4
            c0_steps
            let sc4 : Full.FullScratch := { sc3 with
              phases_target := ptgt', target_assigned := 0#64,
              rephase_limit := sc3.conflicts + sc_val }
            have hsc4 : sc4.LengthsOk c := { hsc3 with phases_target_len := hpt_len }
            have hco4 : Full.FullCoreState.LengthsOk c { st1.core with fuel := fuel' } :=
              { hinv1.lengths.core_ok with vals_len := hinv1.lengths.core_ok.vals_len }
            have hinv4 : Full.FullCoreInv c F0
                { core := { st1.core with fuel := fuel' }, scratch := sc4 } :=
              hinv1.with_fuel_scratch_spec ⟨hco4, hsc4⟩ rfl
            refine hQ vals' lvl' rsns' trl' tp' te' prop' 0 unas' fuel' sc4 _ ?_
              (fun _ => rfl) (Nat.zero_le _) hfl3 ⟨hll3, hext3⟩ ?_
            · simpa only [st1] using hinv4
            · exact (show ∀ {s₁ s₂ : Full.FullState}, s₁ = s₂ →
                  (Full.FullMem c s₁ ⋆ R) _ → (Full.FullMem c s₂ ⋆ R) _
                from fun h hm' => h ▸ hm')
                (by dsimp only [st1, st3, sc4]; try rfl) (by assumption)
          · intro _ hJsc
            m5_split
            · c0_steps; exact hJsc (_, ()) m4 hm4
            · m5_to_group
              refine wp_join_group (ts := [i64]) (fun _ m5 => m4 = m5)
                (fun _ (nlim, ()) _ hm5 => ?_) ?_
              · rcases hm5 with rfl; c0_steps; exact hJsc (_, ()) m4 hm4
              · intro _ hJn; c0_steps
                · exact hJn (100000000#64, ()) m4 rfl
                · exact hJn (_, ()) m4 rfl
        · intro _ hJnc; c0_steps
          · exact hJnc _ _ hm
          · exact hJnc _ _ hm
    · intro Jsel hJsel
      refine wp_join_group (fun () m0 => m = m0) ?_ ?_
      · rintro _ ⟨⟩ _ rfl
        refine wp_loop_inv
          (fun (k, ()) m3 => ∃ ph' : List (BitVec 8),
            k.toNat ≤ s.core.cur_vars ∧ ph'.length = c.max_vars ∧
            (Full.FullMem c { st2 with scratch := { sc2 with phases := ph' } } ⋆ R) m3)
          (fun (k, ()) _ => s.core.cur_vars - k.toNat)
          (fun L hL => by
            c0_hsteps; refine hL (0#64, ()) m
              ⟨sc2.phases, Nat.zero_le _, hsc2_ok.phases_len, ?_⟩
            dsimp only [st2, sc2]; exact hm)
          (fun L (k, ()) m3 ⟨ph', hk_le, hph_l, hm3⟩ ih => ?_)
        have hpb_l := hsc2_ok.phases_best_len
        c0_hsteps
        · have hk_lt : k.toNat < s.core.cur_vars := by c0_bound
          have hk1 : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
          exact ih (k + 1#64, ()) m (by dsimp only; omega)
            ⟨ph'.set k.toNat (sc2.phases_best[k.toNat]'(by omega)),
              by omega, by simp [hph_l], hm⟩
        · have hk_lt : k.toNat < s.core.cur_vars := by c0_bound
          have hk1 : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
          exact ih (k + 1#64, ()) m3 (by dsimp only; omega) ⟨ph', by omega, hph_l, hm3⟩
        · refine hJsel (_, ()) m ⟨s.core.fuel, { sc2 with phases := ph', best_assigned := 0#64 },
            { hsc2_ok with phases_len := hph_l }, Nat.le_refl _, hll1, hext1, ?_⟩
          dsimp only [st2, sc2]; exact hm
      · intro Jbest hJbest
        c0_hsteps_nogrp
        · exact hJbest () m rfl
        · exact hJbest () m rfl
        · apply wp_unroll_group; intro _ hJelse1
          refine wp_join_group (fun () m0 => m = m0) ?_ ?_
          · rintro _ ⟨⟩ _ rfl
            c0_call hWalk
            refine ⟨c, F0, st2, R, rfl, hinv2, by dsimp only [st2, sc2]; exact hm,
              fun fuel' sc3 m3 hlen3 hfl3 hpres3 hm3 => ?_⟩
            c0_hsteps
            exact hJsel (_, ()) m3 ⟨fuel', sc3, hlen3.scratch_ok, hfl3,
              hpres3.1.trans hll1, hpres3.2.trans hext1, hm3⟩
          · intro Jwalk hJwalk
            c0_hsteps_nogrp
            · exact hJwalk () m rfl
            · exact hJwalk () m rfl
            · apply wp_unroll_group; intro _ hJelse2
              c0_hsteps_nogrp
              · refine wp_loop_inv
                  (fun (k, ()) m3 => ∃ ph' : List (BitVec 8),
                    k.toNat ≤ s.core.cur_vars ∧ ph'.length = c.max_vars ∧
                    (Full.FullMem c { st2 with scratch := { sc2 with phases := ph' } } ⋆ R) m3)
                  (fun (k, ()) _ => s.core.cur_vars - k.toNat)
                  (fun L hL => by
                    c0_hsteps; refine hL (0#64, ()) m
                      ⟨sc2.phases, Nat.zero_le _, hsc2_ok.phases_len, ?_⟩
                    dsimp only [st2, sc2]; exact hm)
                  (fun L (k, ()) m3 ⟨ph', hk_le, hph_l, hm3⟩ ih => ?_)
                c0_hsteps
                · have hk_lt : k.toNat < s.core.cur_vars := by c0_bound
                  have hk1 : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
                  exact ih (k + 1#64, ()) m (by dsimp only; omega)
                    ⟨ph'.set k.toNat _, by omega, by simp [hph_l], hm⟩
                · c0_hsteps
                  refine hJsel (_, ()) m3 ⟨s.core.fuel, { sc2 with phases := ph' },
                    { hsc2_ok with phases_len := hph_l }, Nat.le_refl _, hll1, hext1, ?_⟩
                  dsimp only [st2, sc2]; exact hm3
              · refine wp_loop_inv
                  (fun (k, ()) m3 => ∃ ph' : List (BitVec 8),
                    k.toNat ≤ s.core.cur_vars ∧ ph'.length = c.max_vars ∧
                    (Full.FullMem c { st2 with scratch := { sc2 with phases := ph' } } ⋆ R) m3)
                  (fun (k, ()) _ => s.core.cur_vars - k.toNat)
                  (fun L hL => by
                    c0_hsteps; refine hL (0#64, ()) m
                      ⟨sc2.phases, Nat.zero_le _, hsc2_ok.phases_len, ?_⟩
                    dsimp only [st2, sc2]; exact hm)
                  (fun L (k, ()) m3 ⟨ph', hk_le, hph_l, hm3⟩ ih => ?_)
                c0_hsteps
                · have hk_lt : k.toNat < s.core.cur_vars := by c0_bound
                  have hk1 : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
                  exact ih (k + 1#64, ()) m (by dsimp only; omega)
                    ⟨ph'.set k.toNat _, by omega, by simp [hph_l], hm⟩
                · c0_hsteps
                  refine hJsel (_, ()) m3 ⟨s.core.fuel, { sc2 with phases := ph' },
                    { hsc2_ok with phases_len := hph_l }, Nat.le_refl _, hll1, hext1, ?_⟩
                  dsimp only [st2, sc2]; exact hm3

end M5SchedTactics

/-! ## 7. Closed Standalone `m5SchedModule` `ModuleOk` -/

/-- Canonical `FullSpec` / `FullFastSched`-compatible specification table covering `m5Sched_fns`
plus externs (`10` rows). -/
def m5SchedSpecTable : List SpecEntry :=
  [ ⟨"full_log10_q16", [i64], [i64], m5Log10Q16Spec, true⟩
  , ⟨"full_scale_delta_m5", [i64, i64], [i64], m5ScaleDeltaSpec, true⟩
  , ⟨"full_ema_update", [i64, i64], [], Full.fullEmaUpdateSpec, true⟩
  , ⟨"full_rephase", [i64], [], m5RephaseSpec, true⟩
  , ⟨"full_switch_mode", [i64], [], Full.fullSwitchModeSpec, true⟩
  , ⟨"full_restart_due", [i64], [i64], Full.fullRestartDueSpec, true⟩
  , ⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩
  , ⟨"full_heap_down", [i64, i32], [], Full.fullHeapDownSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  , ⟨"full_walk", [i64], [], Full.fullWalkSpec, true⟩
  ]

/-- Specification environment induced by `m5SchedSpecTable`. -/
def m5SchedEnv : Env := Env.ofTable m5SchedSpecTable

theorem m5SchedSpecTable_noExit : ∀ e ∈ m5SchedSpecTable, e.noExit = true := by
  intro e he
  have hall : m5SchedSpecTable.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem m5Sched_noExit :
    ∀ f as bs xs m Q X X',
      m5SchedEnv f as bs xs m Q X → m5SchedEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m5SchedSpecTable_noExit

private theorem m5SchedSpecTable_nodup : (m5SchedSpecTable.map SpecEntry.name).Nodup := by
  show (["full_log10_q16", "full_scale_delta_m5", "full_ema_update", "full_rephase",
    "full_switch_mode", "full_restart_due", "full_ilog10", "full_heap_down", "full_backtrack",
    "full_walk"] : List String).Nodup
  decide

private theorem m5SchedEnv_row_at (i : Nat) (e : SpecEntry)
    (hi : m5SchedSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → m5SchedEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) m5SchedSpecTable_nodup (hno xs m Q X h)

/-- Row-by-row `TableImpl` for `m5Sched_fns` against `m5SchedSpecTable`. -/
theorem m5Sched_tableImpl :
    TableImpl m5SchedEnv m5Sched_fns m5SchedSpecTable := by
  let hLog := m5SchedEnv_row_at 0 ⟨"full_log10_q16", [i64], [i64], m5Log10Q16Spec, true⟩
  let hIlog := m5SchedEnv_row_at 6 ⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩
  let hDown := m5SchedEnv_row_at 7 ⟨"full_heap_down", [i64, i32], [], Full.fullHeapDownSpec, true⟩
  let hBt := m5SchedEnv_row_at 8 ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  let hWalk := m5SchedEnv_row_at 9 ⟨"full_walk", [i64], [], Full.fullWalkSpec, true⟩
  exact ⟨.of (full_log10_q16_wp m5SchedEnv),
    ⟨.of (full_scale_delta_m5_wp m5SchedEnv hLog),
    ⟨.of (full_ema_update_wp m5SchedEnv),
    ⟨.of (full_rephase_wp m5SchedEnv hBt hWalk hLog),
    ⟨.of (full_switch_mode_wp m5SchedEnv hDown hLog hIlog),
    ⟨.of (full_restart_due_wp m5SchedEnv hIlog), trivial⟩⟩⟩⟩⟩⟩

/-- Closed `ModuleOk` for standalone `m5SchedModule` under canonical `m5SchedEnv`. -/
theorem m5Sched_moduleOk : ModuleOk m5SchedEnv m5SchedModule :=
  Env.ofTable_moduleOk m5Sched_acyclic
    ⟨full_log10_q16_wf, full_scale_delta_m5_wf, full_ema_update_wf, full_rephase_wf,
      full_switch_mode_wf, full_restart_due_wf, trivial⟩
    m5Sched_tableImpl

end LeanQbe.T.Examples.Kissat.FullM5Sched
