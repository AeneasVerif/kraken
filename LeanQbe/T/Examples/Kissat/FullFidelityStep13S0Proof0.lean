/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S0
public import LeanQbe.T.Logic.CanonicalEnv
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb
public import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.WPLemmas
import LeanQbe.T.Logic.BitVec
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step-13 Shard `S0` Proofs — Part 0 (`FullFidelityStep13S0Proof0`)

Canonical UNSAT-soundness specifications and `XPost`-polymorphic `Func.wp` proofs (`<= std3`,
`0` `@[expose]` on theorems/lemmas, `0` `import all`) for the `12` pure `S0` soft-float helpers:
`f64u_msb64`, `f64u_round_pack`, `f64u_add`, `f64u_sub`, `f64u_mul`, `f64u_div`,
`f64u_inv_u64`, `f64u_from_u64`, `f64u_to_u64`, `u64_mul128`, `f64u_log10_u64`, `f64u_nlogpown`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S0

open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofKit

/-! ## 1. Canonical Pure `S0` Specifications (`@[expose]`) -/

@[expose] public section

/-- Canonical pure 1-arg soft-float spec (`XFree`, memory-preserving, return-value oblivious). -/
def f64uPure1Spec : Spec [i64] [i64] :=
  fun _ m Q _ => ∀ r : BitVec 64, Q (r, ()) m

/-- Canonical pure 2-arg soft-float spec (`XFree`, memory-preserving, return-value oblivious). -/
def f64uPure2Spec : Spec [i64, i64] [i64] :=
  fun _ m Q _ => ∀ r : BitVec 64, Q (r, ()) m

/-- Strong `f64u_msb64` spec exposing exact `2^r <= x < 2^(r+1)` bounds for `f64u_inv_u64`
division safety (`d ≠ 0`). Strengthens cleanly from `f64uPure1Spec`. -/
def f64uMsb64Spec : Spec [i64] [i64] :=
  fun (x, ()) m Q _ =>
    ∀ r : BitVec 64,
      (x ≠ 0#64 → r.toNat < 64 ∧ 2 ^ r.toNat ≤ x.toNat ∧ x.toNat < 2 ^ (r.toNat + 1)) →
      Q (r, ()) m

/-- Pure 2-result spec for C0 multi-return `u64_mul128(a, b) -> (lo, hi)`. -/
def u64Mul128Spec : Spec [i64, i64] [i64, i64] :=
  fun _ m Q _ => ∀ lo hi : BitVec 64, Q (lo, hi, ()) m

end

/-! ## 2. Pure Spec Adapters & `BitVec 64` Arithmetic Helpers (`public section`) -/

public section

theorem f64uPure1Spec_eq (a : Tup Val [i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost) :
    f64uPure1Spec a m Q X = (∀ r : BitVec 64, Q (r, ()) m) := rfl

theorem f64uPure2Spec_eq (a : Tup Val [i64, i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost) :
    f64uPure2Spec a m Q X = (∀ r : BitVec 64, Q (r, ()) m) := rfl

theorem f64uMsb64Spec_eq (a : Tup Val [i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost) :
    f64uMsb64Spec a m Q X =
      (∀ r : BitVec 64,
        (a.1 ≠ 0#64 → r.toNat < 64 ∧ 2 ^ r.toNat ≤ a.1.toNat ∧
          a.1.toNat < 2 ^ (r.toNat + 1)) →
        Q (r, ()) m) := rfl

theorem u64Mul128Spec_eq (a : Tup Val [i64, i64]) (m : Mem 64)
    (Q : Post [i64, i64]) (X : XPost) :
    u64Mul128Spec a m Q X = (∀ lo hi : BitVec 64, Q (lo, hi, ()) m) := rfl

theorem f64uPure1Spec_to_msb64 {a : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : f64uPure1Spec a m Q X) : f64uMsb64Spec a m Q X :=
  fun r _ => h r

theorem f64uPure1Spec_le_msb64 : f64uPure1Spec.Le f64uMsb64Spec :=
  fun _ _ _ _ h => f64uPure1Spec_to_msb64 h

theorem has_f64uMsb64_to_pure {Γ : Env} (h : Γ.Has "f64u_msb64" f64uMsb64Spec) :
    Γ.Has "f64u_msb64" f64uPure1Spec :=
  Env.Has.of_le h f64uPure1Spec_le_msb64

theorem f64uPure1Spec_xfree : f64uPure1Spec.XFree := by xfree
theorem f64uPure2Spec_xfree : f64uPure2Spec.XFree := by xfree
theorem f64uMsb64Spec_xfree : f64uMsb64Spec.XFree := by xfree
theorem u64Mul128Spec_xfree : u64Mul128Spec.XFree := by xfree

private def MsbInv (W : Nat) (x0 xc r : BitVec 64) : Prop :=
  x0 ≠ 0#64 →
    xc ≠ 0#64 ∧ xc.toNat < 2 ^ W ∧ r.toNat + W ≤ 64 ∧
    xc.toNat * 2 ^ r.toNat ≤ x0.toNat ∧ x0.toNat < (xc.toNat + 1) * 2 ^ r.toNat

private theorem bv64_ne_of_toNat_pos {x : BitVec 64} (h : 0 < x.toNat) : x ≠ 0#64 := by
  intro heq; subst heq; simp at h

private theorem bv64_toNat_pos_of_ne {x : BitVec 64} (h : x ≠ 0#64) : 0 < x.toNat :=
  Nat.pos_of_ne_zero fun h0 => h (BitVec.eq_of_toNat_eq (by simpa using h0))

private theorem msb_step_taken (k : Nat) {x0 xc r : BitVec 64}
    (hk : 0 < k) (h2k : 2 * k ≤ 64) (hinv : MsbInv (2 * k) x0 xc r)
    (hle : (1#64 <<< k) ≤ xc) :
    MsbInv k x0 (xc >>> k) (r + BitVec.ofNat 64 k) := by
  intro h0
  obtain ⟨_, hxc_lt, hr_le, hlo, hhi⟩ := hinv h0
  have h1shl : (1#64 <<< k).toNat = 2 ^ k := by
    rw [BitVec.toNat_shiftLeft, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  have hge : 2 ^ k ≤ xc.toNat := h1shl ▸ BitVec.le_def.mp hle
  have hdiv : (xc >>> k).toNat = xc.toNat / 2 ^ k := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hp_pos : 0 < 2 ^ k := Nat.pow_pos (by decide)
  have hpow2 : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by rw [Nat.two_mul, Nat.pow_add]
  have hxc_div_pos : 0 < xc.toNat / 2 ^ k := Nat.div_pos hge hp_pos
  have hxc_div_lt : xc.toNat / 2 ^ k < 2 ^ k :=
    Nat.div_lt_of_lt_mul (by rw [← hpow2]; exact hxc_lt)
  have hk_lt64 : k < 2 ^ 64 := Nat.lt_of_le_of_lt (show k ≤ 64 by omega) (by decide)
  have hrk_lt : r.toNat + k < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (show r.toNat + k ≤ 64 by omega) (by decide)
  have hr_eq : (r + BitVec.ofNat 64 k).toNat = r.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk_lt64, Nat.mod_eq_of_lt hrk_lt]
  have hpr : 2 ^ (r.toNat + k) = 2 ^ k * 2 ^ r.toNat := by rw [Nat.pow_add, Nat.mul_comm]
  refine ⟨bv64_ne_of_toNat_pos (hdiv ▸ hxc_div_pos), hdiv ▸ hxc_div_lt, by omega, ?_, ?_⟩
  · rw [hdiv, hr_eq, hpr, ← Nat.mul_assoc]
    exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)) hlo
  · rw [hdiv, hr_eq, hpr, ← Nat.mul_assoc]
    have hmod : xc.toNat + 1 ≤ (xc.toNat / 2 ^ k + 1) * 2 ^ k := by
      have hdm := Nat.div_add_mod xc.toNat (2 ^ k)
      rw [Nat.mul_comm (2 ^ k)] at hdm
      have hltm := Nat.mod_lt xc.toNat hp_pos
      rw [Nat.add_mul, Nat.one_mul]
      omega
    exact Nat.lt_of_lt_of_le hhi (Nat.mul_le_mul_right _ hmod)

private theorem msb_step_skip (k : Nat) {x0 xc r : BitVec 64}
    (hinv : MsbInv (2 * k) x0 xc r) (hlt : xc < (1#64 <<< k)) :
    MsbInv k x0 xc r := by
  intro h0
  obtain ⟨hne, _, hr_le, hlo, hhi⟩ := hinv h0
  have hlt' : xc.toNat < (1#64 <<< k).toNat := BitVec.lt_def.mp hlt
  have h1le : (1#64 <<< k).toNat ≤ 2 ^ k := by
    rw [BitVec.toNat_shiftLeft, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_le _ _
  exact ⟨hne, Nat.lt_of_lt_of_le hlt' h1le, by omega, hlo, hhi⟩

private theorem msb_final_taken {x0 xc r : BitVec 64}
    (hinv : MsbInv 2 x0 xc r) (hle : 2#64 ≤ xc) (h0 : x0 ≠ 0#64) :
    let r' := r + 1#64
    r'.toNat < 64 ∧ 2 ^ r'.toNat ≤ x0.toNat ∧ x0.toNat < 2 ^ (r'.toNat + 1) := by
  obtain ⟨_, hxc_lt, hr_le, hlo, hhi⟩ := hinv h0
  have h2le : 2 ≤ xc.toNat := BitVec.le_def.mp hle
  have hr_eq : (r + 1#64).toNat = r.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hpow1 : 2 ^ (r.toNat + 1) = 2 * 2 ^ r.toNat := by rw [Nat.pow_succ, Nat.mul_comm]
  have hpow2 : 2 ^ (r.toNat + 2) = 4 * 2 ^ r.toNat := by
    rw [show r.toNat + 2 = (r.toNat + 1) + 1 from rfl, Nat.pow_succ, hpow1]; omega
  refine ⟨by omega, ?_, ?_⟩
  · rw [hr_eq, hpow1]; exact Nat.le_trans (Nat.mul_le_mul_right _ h2le) hlo
  · rw [hr_eq, show r.toNat + 1 + 1 = r.toNat + 2 from rfl, hpow2]
    have hxc3 : xc.toNat + 1 ≤ 4 := by omega
    exact Nat.lt_of_lt_of_le hhi (Nat.mul_le_mul_right _ hxc3)

private theorem msb_final_skip {x0 xc r : BitVec 64}
    (hinv : MsbInv 2 x0 xc r) (hlt : xc < 2#64) (h0 : x0 ≠ 0#64) :
    r.toNat < 64 ∧ 2 ^ r.toNat ≤ x0.toNat ∧ x0.toNat < 2 ^ (r.toNat + 1) := by
  obtain ⟨hne, _, hr_le, hlo, hhi⟩ := hinv h0
  have hx1 : xc.toNat = 1 := by
    have hp := bv64_toNat_pos_of_ne hne
    have hl : xc.toNat < 2 := by simpa [BitVec.lt_def] using hlt
    omega
  refine ⟨by omega, ?_, ?_⟩
  · simpa [hx1] using hlo
  · rw [Nat.pow_succ, Nat.mul_comm]; simpa [hx1] using hhi

private theorem msb_inv_init (x : BitVec 64) : MsbInv 64 x x 0#64 := fun h0 => by
  refine ⟨h0, BitVec.isLt x, by decide, ?_, ?_⟩
  · simp
  · simp

private theorem shl_uge_le (k : Nat) {xc : BitVec 64}
    (hc : BitVec.toNat (1 : BitVec 64) * 2 ^ k % 2 ^ 64 ≤ xc.toNat) :
    (1#64 <<< k) ≤ xc := by
  rw [BitVec.le_def, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  simpa using hc

private theorem shl_uge_lt (k : Nat) {xc : BitVec 64}
    (hc : ¬ BitVec.toNat (1 : BitVec 64) * 2 ^ k % 2 ^ 64 ≤ xc.toNat) :
    xc < (1#64 <<< k) := by
  rw [BitVec.lt_def, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  exact Nat.lt_of_not_le (by simpa using hc)

private theorem pure_wp_join_group {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (hbody : ∀ (J : Cont ts) xs, wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) m)
    (hentry : ∀ (J : Cont ts), (∀ xs, J xs m) → wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_join_group (fun _ m' => m' = m)
    (fun J xs _ hm' => hm' ▸ hbody J xs)
    (fun J hJ => hentry J fun xs => hJ xs m rfl)

private theorem pure_wp_join_seq {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (hentry : ∀ (J : Cont ts), (∀ xs, J xs m) → wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) xs, wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  pure_wp_join_group hbody hentry

/-! ## 3. Pure Helper Proofs (`12` Functions) -/

section PureHelpers

private theorem msb_join_step {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [[i64, i64]] → Blocks Val Cont rs [[i64, i64]]}
    {entry : Tup Cont [[i64, i64]] → Expr Val Cont rs}
    (W : Nat) (x0 : BitVec 64)
    (hbody : ∀ (J : Cont [i64, i64]) (xc r : BitVec 64),
      MsbInv W x0 xc r → wp Γ Q X (Blocks.get (bodies (J, ())) .here (xc, r, ())) m)
    (hentry : ∀ (J : Cont [i64, i64]),
      (∀ xc r : BitVec 64, MsbInv W x0 xc r → J (xc, r, ()) m) →
      wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [[i64, i64]]) bodies entry) m :=
  wp_join_state (fun p : BitVec 64 × BitVec 64 => (p.1, p.2, ()))
    (fun p m' => MsbInv W x0 p.1 p.2 ∧ m' = m)
    (fun J p _ ⟨hi, rfl⟩ => hbody J p.1 p.2 hi)
    (fun J hJ => hentry J fun xc r hi => hJ (xc, r) m ⟨hi, rfl⟩)

theorem f64u_msb64_wp (Γ : Env) :
    ∀ a m Q X, f64uMsb64Spec a m Q X → Func.wp Γ f64u_msb64_body a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  unfold Func.wp f64u_msb64_body
  c0_hsteps_nogrp
  have h0 : MsbInv 64 x x 0#64 := msb_inv_init x
  refine msb_join_step 32 x (fun J32 xc r h32 => ?_) (fun J32 hJ32 => ?_)
  · c0_hsteps_nogrp
    refine msb_join_step 16 x (fun J16 xc1 r1 h16 => ?_) (fun J16 hJ16 => ?_)
    · c0_hsteps_nogrp
      refine msb_join_step 8 x (fun J8 xc2 r2 h8 => ?_) (fun J8 hJ8 => ?_)
      · c0_hsteps_nogrp
        refine msb_join_step 4 x (fun J4 xc3 r3 h4 => ?_) (fun J4 hJ4 => ?_)
        · c0_hsteps_nogrp
          refine msb_join_step 2 x (fun J2 xc4 r4 h2 => ?_) (fun J2 hJ2 => ?_)
          · c0_hsteps_nogrp
            refine wp_join_state1 (fun r5 : BitVec 64 => r5)
              (fun r5 m' => (x ≠ 0#64 → r5.toNat < 64 ∧ 2 ^ r5.toNat ≤ x.toNat ∧
                x.toNat < 2 ^ (r5.toNat + 1)) ∧ m' = m)
              (fun _ r5 _ ⟨hp, rfl⟩ => by c0_hsteps_nogrp; exact hQ r5 hp)
              (fun J1 hJ1 => by
                c0_hsteps_nogrp; c0_hsplit <;> c0_hsteps_nogrp
                · exact hJ1 (r4 + 1#64) m ⟨fun hx0 =>
                    msb_final_taken h2 (BitVec.le_def.mpr hc) hx0, rfl⟩
                · exact hJ1 r4 m ⟨fun hx0 =>
                    msb_final_skip h2 (BitVec.lt_def.mpr (Nat.lt_of_not_le hc)) hx0, rfl⟩)
          · c0_hsteps_nogrp; c0_hsplit <;> c0_hsteps_nogrp
            · exact hJ2 (xc3 >>> (2 : Nat)) (r3 + 2#64)
                (msb_step_taken 2 (by decide) (by decide) h4 (shl_uge_le 2 hc))
            · exact hJ2 xc3 r3 (msb_step_skip 2 h4 (shl_uge_lt 2 hc))
        · c0_hsteps_nogrp; c0_hsplit <;> c0_hsteps_nogrp
          · exact hJ4 (xc2 >>> (4 : Nat)) (r2 + 4#64)
              (msb_step_taken 4 (by decide) (by decide) h8 (shl_uge_le 4 hc))
          · exact hJ4 xc2 r2 (msb_step_skip 4 h8 (shl_uge_lt 4 hc))
      · c0_hsteps_nogrp; c0_hsplit <;> c0_hsteps_nogrp
        · exact hJ8 (xc1 >>> (8 : Nat)) (r1 + 8#64)
            (msb_step_taken 8 (by decide) (by decide) h16 (shl_uge_le 8 hc))
        · exact hJ8 xc1 r1 (msb_step_skip 8 h16 (shl_uge_lt 8 hc))
    · c0_hsteps_nogrp; c0_hsplit <;> c0_hsteps_nogrp
      · exact hJ16 (xc >>> (16 : Nat)) (r + 16#64)
          (msb_step_taken 16 (by decide) (by decide) h32 (shl_uge_le 16 hc))
      · exact hJ16 xc r (msb_step_skip 16 h32 (shl_uge_lt 16 hc))
  · c0_hsteps_nogrp; c0_hsplit <;> c0_hsteps_nogrp
    · exact hJ32 (x >>> (32 : Nat)) (0#64 + 32#64)
        (msb_step_taken 32 (by decide) (by decide) h0 (shl_uge_le 32 hc))
    · exact hJ32 x 0#64 (msb_step_skip 32 h0 (shl_uge_lt 32 hc))

local elab "close_pure_leaf" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let tgt ← g.getType
    let lctx ← Lean.getLCtx
    for decl in lctx do
      if decl.isImplementationDetail then continue
      let dty ← Lean.Meta.whnf decl.type
      unless dty.isForall do continue
      let s ← Lean.Meta.saveState
      let (mvars, _, body) ← Lean.Meta.forallMetaTelescopeReducing dty
      if mvars.size ≥ 1 && mvars.size ≤ 2 then
        if ← Lean.Meta.isDefEq body tgt then
          let prf ← Lean.instantiateMVars (Lean.mkAppN decl.toExpr mvars)
          let tgt' ← Lean.instantiateMVars tgt
          if (← Lean.Meta.getMVars prf).isEmpty && (← Lean.Meta.getMVars tgt').isEmpty then
            g.assign prf
            Lean.Elab.Tactic.replaceMainGoal []
            return
      s.restore
    throwError "close_pure_leaf failed"

local elab "pure_acyclic_join" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let ty := (← Lean.instantiateMVars (← g.getType)).headBeta.consumeMData
  guard (ty.isAppOfArity ``LeanQbe.T.wp 6)
  let e := (ty.getArg! 4).consumeMData.headBeta.consumeMData
  guard (e.isAppOfArity ``LeanQbe.T.Expr.group 6)
  let bodies := (e.getArg! 4).consumeMData
  let .lam _ _ bs _ := bodies | throwError "not lam"
  let bs := bs.consumeMData
  guard (bs.isAppOfArity ``LeanQbe.T.Blocks.cons 7)
  let b := (bs.getArg! 5).consumeMData
  let .lam _ _ bbody _ := b | throwError "not block lam"
  if bbody.hasLooseBVar 1 then
    throwError "loop group (self-referential Js)"
  Lean.Elab.Tactic.evalTactic (← `(tactic| focus (apply pure_wp_join_seq <;> intro _ _)))

local elab "intro_call_res" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro _))
  let g ← Lean.Elab.Tactic.getMainGoal
  let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
  if ty.isForall then
    Lean.Elab.Tactic.evalTactic (← `(tactic| intro _))

local elab "hfast_step" : tactic => do
  let gs0 ← Lean.Elab.Tactic.getUnsolvedGoals
  let some g0 := gs0.head? | throwError "no goals"
  let ty0 := (← Lean.instantiateMVars (← g0.getType)).headBeta.consumeMData
  if ty0.isAppOfArity ``LeanQbe.T.wp 6 then
    let e0 := (ty0.getArg! 4).consumeMData.headBeta.consumeMData
    if e0.isAppOf ``LeanQbe.T.Expr.group || e0.isAppOf ``LeanQbe.T.Expr.call then
      throwError "at group or call"
  Lean.Elab.Tactic.evalTactic (← `(tactic| focus c0_hfast_nogrp))
  let gs1 ← Lean.Elab.Tactic.getUnsolvedGoals
  if let some g1 := gs1.head? then
    let ty1 := (← Lean.instantiateMVars (← g1.getType)).headBeta.consumeMData
    if g1 == g0 || ty1 == ty0 then
      throwError "no progress"

local elab "solve_f64u_with" cs:term,* : tactic => do
  let callTacs ← cs.getElems.mapM fun c =>
    `(tactic| focus (c0_hcall $c; intro_call_res))
  let stepTacs := #[
    ← `(tactic| close_pure_leaf),
    ← `(tactic| pure_acyclic_join)] ++ callTacs ++ #[
    ← `(tactic| hfast_step)]
  for _ in [:512] do
    if (← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then break
    let mut stepped := false
    for t in stepTacs do
      if ← Lean.Elab.Tactic.tryTactic (Lean.Elab.Tactic.evalTactic t) then
        stepped := true
        break
    if !stepped then break

local macro "solve_f64u_pure" : tactic =>
  `(tactic| solve_f64u_with)

theorem f64u_round_pack_wp (Γ : Env)
    (hMsb : Γ.Has "f64u_msb64" f64uPure1Spec) :
    ∀ a m Q X, f64uPure2Spec a m Q X → Func.wp Γ f64u_round_pack_body a m Q X := by
  rintro ⟨exp, sig55, ⟨⟩⟩ m Q X hQ
  unfold Func.wp f64u_round_pack_body
  solve_f64u_with hMsb

theorem f64u_add_wp (Γ : Env)
    (hPack : Γ.Has "f64u_round_pack" f64uPure2Spec) :
    ∀ a m Q X, f64uPure2Spec a m Q X → Func.wp Γ f64u_add_body a m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X hQ
  unfold Func.wp f64u_add_body
  solve_f64u_with hPack

theorem f64u_sub_wp (Γ : Env)
    (hPack : Γ.Has "f64u_round_pack" f64uPure2Spec) :
    ∀ a m Q X, f64uPure2Spec a m Q X → Func.wp Γ f64u_sub_body a m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X hQ
  unfold Func.wp f64u_sub_body
  solve_f64u_with hPack

theorem f64u_mul_wp (Γ : Env)
    (hMsb : Γ.Has "f64u_msb64" f64uPure1Spec)
    (hPack : Γ.Has "f64u_round_pack" f64uPure2Spec) :
    ∀ a m Q X, f64uPure2Spec a m Q X → Func.wp Γ f64u_mul_body a m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X hQ
  unfold Func.wp f64u_mul_body
  solve_f64u_with hMsb, hPack

theorem f64u_from_u64_wp (Γ : Env)
    (hMsb : Γ.Has "f64u_msb64" f64uPure1Spec) :
    ∀ a m Q X, f64uPure1Spec a m Q X → Func.wp Γ f64u_from_u64_body a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  unfold Func.wp f64u_from_u64_body
  solve_f64u_with hMsb

theorem f64u_to_u64_wp (Γ : Env) :
    ∀ a m Q X, f64uPure1Spec a m Q X → Func.wp Γ f64u_to_u64_body a m Q X := by
  rintro ⟨a, ⟨⟩⟩ m Q X hQ
  unfold Func.wp f64u_to_u64_body
  solve_f64u_pure

theorem u64_mul128_wp (Γ : Env) :
    ∀ a m Q X, u64Mul128Spec a m Q X → Func.wp Γ u64_mul128_body a m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X hQ
  unfold Func.wp u64_mul128_body
  c0_hsteps_nogrp
  exact hQ _ _

theorem f64u_div_wp (Γ : Env)
    (hMsb : Γ.Has "f64u_msb64" f64uPure1Spec)
    (hPack : Γ.Has "f64u_round_pack" f64uPure2Spec) :
    ∀ a m Q X, f64uPure2Spec a m Q X → Func.wp Γ f64u_div_body a m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X hQ
  unfold Func.wp f64u_div_body
  solve_f64u_with hMsb
  refine wp_while_state_pure (α := BitVec 64 × BitVec 64 × BitVec 64)
    (fun st => (st.1, st.2.1, st.2.2, ())) (fun st => 56 - st.2.2.toNat)
    (fun st => st.2.2.toNat ≤ 56) (fun Jlp hJlp => ?_) (fun Jlp st hst ih => ?_)
  · exact hJlp (0#64, _, 0#64) (by dsimp only; decide)
  · rcases st with ⟨q, r, i⟩; dsimp only at hst ⊢
    c0_hsteps_nogrp
    · have hi56 : i.toNat < 56 := by simpa [BitVec.ult] using hc
      have hi1 : (i + 1#64).toNat = i.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      solve_f64u_pure
      · exact ih (_, _, i + 1#64) (by dsimp only; rw [hi1]; omega) (by dsimp only; rw [hi1]; omega)
    · solve_f64u_with hPack

private theorem inv_u64_m_range {k msb : BitVec 64}
    (hmsb_lt : msb.toNat < 64)
    (hlo : 2 ^ msb.toNat ≤ k.toNat) (hhi : k.toNat < 2 ^ (msb.toNat + 1))
    (h52 : 52 < msb.toNat) :
    let sh := msb - 52#64
    let m := k >>> (sh.toNat % 64)
    2 ^ 52 ≤ m.toNat ∧ m.toNat < 2 ^ 53 := by
  intro sh m
  have hsh : sh.toNat % 64 = msb.toNat - 52 := by
    have hlt : sh.toNat = msb.toNat - 52 := by
      dsimp only [sh]
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
        rw [show (52#64 : BitVec 64).toNat = 52 from rfl]; omega)),
        show (52#64 : BitVec 64).toNat = 52 from rfl]
    rw [hlt, Nat.mod_eq_of_lt (by omega)]
  have hm_eq : m.toNat = k.toNat / 2 ^ (sh.toNat % 64) := by
    simp [m, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hp_pos : 0 < 2 ^ (msb.toNat - 52) := Nat.pow_pos (by decide)
  have h52p : 2 ^ msb.toNat = 2 ^ 52 * 2 ^ (msb.toNat - 52) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)]
  have h53p : 2 ^ (msb.toNat + 1) = 2 ^ (msb.toNat - 52) * 2 ^ 53 := by
    rw [← Nat.pow_add, show (msb.toNat - 52) + 53 = msb.toNat + 1 by omega]
  rw [hm_eq, hsh]
  exact ⟨Nat.le_div_iff_mul_le hp_pos |>.mpr (h52p ▸ hlo),
         Nat.div_lt_of_lt_mul (h53p ▸ hhi)⟩

theorem f64u_inv_u64_wp (Γ : Env)
    (hMsb : Γ.Has "f64u_msb64" f64uMsb64Spec)
    (hPack : Γ.Has "f64u_round_pack" f64uPure2Spec) :
    ∀ a m Q X, f64uPure1Spec a m Q X → Func.wp Γ f64u_inv_u64_body a m Q X := by
  rintro ⟨k, ⟨⟩⟩ m Q X hQ
  unfold Func.wp f64u_inv_u64_body
  c0_hsteps_nogrp
  · exact hQ _
  · exact hQ _
  have hk0' : k ≠ 0#64 := fun h => by simp [h] at *
  have hk1' : k ≠ 1#64 := fun h => by simp [h] at *
  have hk_ge2 : 2 ≤ k.toNat := by
    have hp := bv64_toNat_pos_of_ne hk0'
    have hn1 : k.toNat ≠ 1 := fun h => hk1' (BitVec.eq_of_toNat_eq (by simpa using h))
    omega
  c0_hcall hMsb
  intro msb hmsb_raw
  obtain ⟨hmsb_lt, hmsb_lo, hmsb_hi⟩ := hmsb_raw hk0'
  have hmsb_ne : msb.toNat ≠ 0 := by
    intro h0
    rw [h0, Nat.zero_add, Nat.pow_one] at hmsb_hi
    omega
  have hmsb_ge1 : 1 ≤ msb.toNat := Nat.pos_of_ne_zero hmsb_ne
  c0_hsteps_nogrp
  · exact hQ _
  refine wp_join_state (α := BitVec 64 × BitVec 64 × BitVec 64)
    (fun st => (st.1, st.2.1, st.2.2, ()))
    (fun st m' => m' = m ∧ st.2.1 ≠ 0#64 ∧ 1 ≤ st.2.2.toNat ∧ st.2.2.toNat ≤ 52)
    (fun J0 st m' ⟨hm', hd0, hdm1, hdm52⟩ => ?_) (fun J0 hJ0 => ?_)
  · cases hm'; rcases st with ⟨msb', d, d_msb⟩; dsimp only at hd0 hdm1 hdm52 ⊢
    c0_hsteps_nogrp
    · solve_f64u_with hPack
    · solve_f64u_with hPack
    · have hdm_gt8 : 8 < d_msb.toNat := by
        simp only [show BitVec.toNat (8 : BitVec 64) = 8 from rfl] at *
        omega
      have hs2_init : (d_msb - 8#64).toNat ≤ 44 := by
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by simp; omega)),
          show (8#64 : BitVec 64).toNat = 8 from rfl]
        omega
      refine wp_while_state_pure (α := BitVec 64 × BitVec 64 × BitVec 64)
        (fun st => (st.1, st.2.1, st.2.2, ())) (fun st => st.1.toNat)
        (fun st => st.1.toNat ≤ 44) (fun Jlp hJlp => ?_)
        (fun Jlp st hst ih => ?_)
      · exact hJlp (d_msb - 8#64, _, _) hs2_init
      · rcases st with ⟨s2, q, rem⟩; dsimp only at hst ⊢
        c0_hsteps_nogrp
        · have hs2_pos : 0 < s2.toNat := by simpa [BitVec.ult] using hc
          refine wp_join_state1 (fun st : BitVec 64 => st)
            (fun st_v m'' => m'' = m ∧ 1 ≤ st_v.toNat ∧ st_v.toNat ≤ s2.toNat)
            (fun _ st_v m'' ⟨hm'', hst1, hsts2⟩ => ?_) (fun Jst hJst => ?_)
          · cases hm''
            c0_hsteps_nogrp
            have hsub : (s2 - st_v).toNat = s2.toNat - st_v.toNat :=
              BitVec.toNat_sub_of_le (BitVec.le_def.mpr hsts2)
            exact ih (s2 - st_v, _, _) (by dsimp only; rw [hsub]; omega)
              (by dsimp only; rw [hsub]; omega)
          · c0_hsteps_nogrp
            · exact hJst 11#64 m ⟨rfl, by decide, by
                have : 11 < s2.toNat := by simpa [BitVec.ult] using hc
                rw [show (11#64 : BitVec 64).toNat = 11 from rfl]; omega⟩
            · exact hJst s2 m ⟨rfl, hs2_pos, Nat.le_refl _⟩
        · solve_f64u_with hPack
  · c0_hsteps_nogrp
    · have h52_lt : 52 < msb.toNat := by simpa [BitVec.ult] using hc
      have hm_rng := inv_u64_m_range hmsb_lt hmsb_lo hmsb_hi h52_lt
      c0_hsteps_nogrp
      refine wp_join_state (α := BitVec 64 × BitVec 64) (fun p => (p.1, p.2, ()))
        (fun p m' => m' = m ∧ 2 ^ 52 ≤ p.2.toNat ∧ p.2.toNat < 2 ^ 53)
        (fun Jm p m' ⟨hm', hmlo, hmhi⟩ => ?_) (fun Jm hJm => ?_)
      · c0_hsteps_nogrp
        have hd_ne : p.2 ≠ 0#64 := bv64_ne_of_toNat_pos (Nat.lt_of_lt_of_le (by decide) hmlo)
        exact hJ0 (p.1, p.2, 52#64) m' ⟨hm', hd_ne, by show 1 ≤ 52; decide, by show 52 ≤ 52; decide⟩
      · c0_hsteps_nogrp
        refine pure_wp_join_seq (fun Jthen hJthen => ?_) (fun Jthen _ => ?_)
        · c0_hsteps_nogrp <;>
            first
            | exact hJthen ()
            | exact hJm (msb, _) m ⟨rfl, hm_rng.1, hm_rng.2⟩
        · have hmsb_gt52 : 52 < msb.toNat := by simpa [BitVec.ult] using hc
          c0_hsteps_nogrp
          let m0 := k >>> ((msb - 52#64).toNat % 64)
          have hm1_lt53 : (m0 + 1#64).toNat = m0.toNat + 1 := by
            dsimp only [m0]
            rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by have := hm_rng.2; omega)]
          have hm1_rng : 2 ^ 52 ≤ (m0 + 1#64).toNat ∧ (m0 + 1#64).toNat ≤ 2 ^ 53 := by
            dsimp only [m0] at hm1_lt53 ⊢
            have := hm_rng.1; have := hm_rng.2; omega
          refine wp_join_state (α := BitVec 64 × BitVec 64) (fun p => (p.1, p.2, ()))
            (fun p m' => m' = m ∧ 2 ^ 52 ≤ p.2.toNat ∧ p.2.toNat < 2 ^ 53)
            (fun Jr p m' ⟨hm', hp1, hp2⟩ => by
              cases hm'; c0_hsteps_nogrp; exact hJm p m ⟨rfl, hp1, hp2⟩)
            (fun Jr hJr => by
              have hsub_nat : (msb - 52#64).toNat = msb.toNat - 52 :=
                BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                  rw [show (52#64 : BitVec 64).toNat = 52 from rfl]; omega))
              have hmod64 : (msb.toNat - 52) % 64 = msb.toNat - 52 := by omega
              have hm0_div : (m0 + 1#64).toNat =
                  (k.toNat / 2 ^ (msb.toNat - 52) + 1) % 2 ^ 64 := by
                dsimp only [m0]
                rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
                  BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hsub_nat, hmod64]
              have h184 : (18446744073709551564 + msb.toNat) % 18446744073709551616 =
                  msb.toNat - 52 := by
                have := msb.isLt; omega
              c0_hsteps_nogrp
              · have hc_le : 2 ^ 53 ≤ (m0 + 1#64).toNat := by
                  have hc' := hc
                  simp at hc'
                  rw [h184] at hc'
                  rw [hm0_div]
                  exact Nat.le_trans (by decide) hc'
                have hm1_eq : (m0 + 1#64).toNat = 2 ^ 53 := by
                  have := hm1_rng.2; omega
                have hdiv : ((m0 + 1#64) >>> (1 : Nat)).toNat = 2 ^ 52 := by
                  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hm1_eq]
                exact hJr (msb + 1#64, _) m ⟨rfl, hdiv ▸ Nat.le_refl _, hdiv ▸ by decide⟩
              · have hc_lt : (m0 + 1#64).toNat < 2 ^ 53 := by
                  have hc' := hc
                  simp at hc'
                  rw [h184] at hc'
                  rw [hm0_div]
                  exact Nat.lt_of_lt_of_le hc' (by decide)
                exact hJr (msb, _) m ⟨rfl, hm1_rng.1, hc_lt⟩)
    · have h52_nat : msb.toNat ≤ 52 := by
        have : ¬ (52 < msb.toNat) := by simpa [BitVec.ult] using hc
        omega
      exact hJ0 (msb, k, msb) m ⟨rfl, hk0', hmsb_ge1, h52_nat⟩

theorem f64u_log10_u64_wp (Γ : Env)
    (hMsb : Γ.Has "f64u_msb64" f64uPure1Spec)
    (hPack : Γ.Has "f64u_round_pack" f64uPure2Spec)
    (hMul128 : Γ.Has "u64_mul128" u64Mul128Spec) :
    ∀ a m Q X, f64uPure1Spec a m Q X → Func.wp Γ f64u_log10_u64_body a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  unfold Func.wp f64u_log10_u64_body
  solve_f64u_with hMsb
  refine wp_while_state_pure (α := BitVec 64 × BitVec 64 × BitVec 64)
    (fun st => (st.1, st.2.1, st.2.2, ())) (fun st => 64 - st.2.2.toNat)
    (fun st => st.2.2.toNat ≤ 64) (fun Jlp hJlp => ?_) (fun Jlp st hst ih => ?_)
  · exact hJlp (_, 0#64, 0#64) (by dsimp only; decide)
  · rcases st with ⟨m_v, frac, i⟩; dsimp only at hst ⊢
    c0_hsteps_nogrp
    · have hi64 : i.toNat < 64 := by simpa [BitVec.ult] using hc
      have hi1 : (i + 1#64).toNat = i.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      solve_f64u_with hMul128
      all_goals
        exact ih (_, _, i + 1#64) (by dsimp only; rw [hi1]; omega) (by dsimp only; rw [hi1]; omega)
    · solve_f64u_with hMul128, hMsb, hPack

theorem f64u_nlogpown_wp (Γ : Env)
    (hLog : Γ.Has "f64u_log10_u64" f64uPure1Spec)
    (hMul : Γ.Has "f64u_mul" f64uPure2Spec)
    (hFrom : Γ.Has "f64u_from_u64" f64uPure1Spec) :
    ∀ a m Q X, f64uPure2Spec a m Q X → Func.wp Γ f64u_nlogpown_body a m Q X := by
  rintro ⟨count, exponent, ⟨⟩⟩ m Q X hQ
  unfold Func.wp f64u_nlogpown_body
  solve_f64u_with hLog
  refine wp_while_state_pure (α := BitVec 64 × BitVec 64)
    (fun st => (st.1, st.2, ())) (fun st => exponent.toNat - st.2.toNat)
    (fun st => st.2.toNat ≤ exponent.toNat) (fun Jlp hJlp => ?_) (fun Jlp st hst ih => ?_)
  · exact hJlp (0x3FF0000000000000#64, 0#64) (Nat.zero_le _)
  · rcases st with ⟨factor, i⟩; dsimp only at hst ⊢
    c0_hsteps_nogrp
    · c0_hcall hMul
      intro factor'
      c0_hsteps_nogrp
      have hexp : i.toNat < exponent.toNat := by simpa [BitVec.ult] using hc
      have hi1 : (i + 1#64).toNat = i.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by have := exponent.isLt; omega)]
      exact ih (factor', i + 1#64) (by dsimp only; rw [hi1]; omega) (by dsimp only; rw [hi1]; omega)
    · solve_f64u_with hFrom, hMul

end PureHelpers

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S0
