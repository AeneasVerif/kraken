/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Src.Float64
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
meta import Lean.Elab.Tactic
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# WP Proofs for `Kissat.Src.Float64` Part 0 (`Wp0`)

Canonical `Func.wp` proofs for the first `9` functions of `Src.Float64.fns`:
`f64u_msb64`, `f64u_round_pack`, `f64u_add`, `f64u_sub`, `f64u_mul`, `f64u_div`,
`f64u_from_u64`, `f64u_to_u64`, `u64_mul128`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Float64

open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat.Src.Float64
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec

local macro "f64_hsteps_nogrp" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps_nogrp))

private theorem wp_pure_group {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (hbody : ∀ (J : Cont ts) xs, wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) m)
    (hentry : ∀ (J : Cont ts), (∀ xs, J xs m) → wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_join_group (fun _ m1 => m1 = m) (fun J xs _ hm => hm ▸ hbody J xs)
    (fun J hJ => hentry J (fun xs => hJ xs m rfl))

private def MsbInv (k : Nat) (x0 x r : BitVec 64) : Prop :=
  x0 ≠ 0#64 →
    r.toNat + k ≤ 64 ∧ x ≠ 0#64 ∧ x.toNat < 2 ^ k ∧
    2 ^ r.toNat * x.toNat ≤ x0.toNat ∧ x0.toNat < 2 ^ r.toNat * (x.toNat + 1)

private theorem msb_inv_init (x0 : BitVec 64) : MsbInv 64 x0 x0 0#64 := fun hx0 =>
  ⟨by decide, hx0, x0.isLt, by simp, by simp⟩

private theorem msb_step_ge {h : Nat} {x0 x r : BitVec 64} (hh : 0 < h) (h2 : 2 * h ≤ 64)
    (hinv : MsbInv (2 * h) x0 x r) (hge : (1#64 <<< h).toNat ≤ x.toNat) :
    MsbInv h x0 (x >>> h) (r + BitVec.ofNat 64 h) := by
  intro hx0
  obtain ⟨hr, _, hxlt, hlo, hhi⟩ := hinv hx0
  have hhlt : h < 64 := by omega
  have h1s : (1#64 <<< h).toNat = 2 ^ h := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.one_mod, Nat.one_shiftLeft,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hhlt)]
  rw [h1s] at hge
  have hxshr : (x >>> h).toNat = x.toNat / 2 ^ h := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hpos2 : 0 < 2 ^ h := Nat.pow_pos (by omega)
  have hdiv_pos : 1 ≤ x.toNat / 2 ^ h := (Nat.le_div_iff_mul_le hpos2).mpr (by simpa using hge)
  have hdiv_lt : x.toNat / 2 ^ h < 2 ^ h :=
    (Nat.div_lt_iff_lt_mul hpos2).mpr
      (by rw [← Nat.pow_add, show h + h = 2 * h by omega]; exact hxlt)
  have hne : x >>> h ≠ 0#64 := fun he => by
    have := congrArg BitVec.toNat he
    rw [hxshr, BitVec.toNat_ofNat] at this; omega
  have hr1 : (r + BitVec.ofNat 64 h).toNat = r.toNat + h := by
    have h64 : 64 < 2 ^ 64 := by decide
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hmul_le : 2 ^ h * (x.toNat / 2 ^ h) ≤ x.toNat := Nat.mul_div_le x.toNat (2 ^ h)
  have hlt_mul : x.toNat + 1 ≤ 2 ^ h * (x.toNat / 2 ^ h + 1) := by
    have hmod := Nat.div_add_mod x.toNat (2 ^ h)
    have hmodlt := Nat.mod_lt x.toNat hpos2
    rw [Nat.mul_add, Nat.mul_one]
    omega
  refine ⟨by omega, hne, by rw [hxshr]; exact hdiv_lt, ?_, ?_⟩
  · rw [hr1, hxshr, Nat.pow_add, Nat.mul_assoc]
    exact Nat.le_trans (Nat.mul_le_mul_left _ hmul_le) hlo
  · rw [hr1, hxshr, Nat.pow_add, Nat.mul_assoc]
    exact Nat.lt_of_lt_of_le hhi (Nat.mul_le_mul_left _ hlt_mul)

private theorem msb_step_lt {h : Nat} {x0 x r : BitVec 64}
    (hinv : MsbInv (2 * h) x0 x r) (hlt : ¬ (1#64 <<< h).toNat ≤ x.toNat) :
    MsbInv h x0 x r := by
  intro hx0
  obtain ⟨hr, hx, hxlt, hlo, hhi⟩ := hinv hx0
  have hhlt : h < 64 := by omega
  have h1s : (1#64 <<< h).toNat = 2 ^ h := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.one_mod, Nat.one_shiftLeft,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hhlt)]
  rw [h1s] at hlt
  exact ⟨by omega, hx, by omega, hlo, hhi⟩

private theorem msb_step_final_ge {x0 x r : BitVec 64} (hinv : MsbInv 2 x0 x r)
    (hge : 2 ≤ x.toNat) :
    x0 ≠ 0#64 → (r + 1#64).toNat < 64 ∧ 2 ^ (r + 1#64).toNat ≤ x0.toNat ∧
      x0.toNat < 2 ^ ((r + 1#64).toNat + 1) := by
  intro hx0
  obtain ⟨hr, _, hxlt, hlo, hhi⟩ := hinv hx0
  have hr1 : (r + 1#64).toNat = r.toNat + 1 := by
    have h64 : 64 < 2 ^ 64 := by decide
    rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hxlt4 : x.toNat < 4 := by simpa using hxlt
  have h1 : 2 ^ (r.toNat + 1) ≤ 2 ^ r.toNat * x.toNat := by
    rw [Nat.pow_succ]; exact Nat.mul_le_mul_left _ hge
  have h2 : 2 ^ r.toNat * (x.toNat + 1) ≤ 2 ^ (r.toNat + 2) := by
    rw [show 2 ^ (r.toNat + 2) = 2 ^ r.toNat * 4 by rw [Nat.pow_add]]
    exact Nat.mul_le_mul_left _ (by omega)
  exact ⟨by omega, by rw [hr1]; exact Nat.le_trans h1 hlo,
    by rw [hr1]; exact Nat.lt_of_lt_of_le hhi h2⟩

private theorem msb_step_final_lt {x0 x r : BitVec 64} (hinv : MsbInv 2 x0 x r)
    (hlt : ¬ 2 ≤ x.toNat) :
    x0 ≠ 0#64 → r.toNat < 64 ∧ 2 ^ r.toNat ≤ x0.toNat ∧ x0.toNat < 2 ^ (r.toNat + 1) := by
  intro hx0
  obtain ⟨hr, hxne, _, hlo, hhi⟩ := hinv hx0
  have hxpos : 1 ≤ x.toNat :=
    Nat.pos_of_ne_zero fun h0 => hxne (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
  have hx1 : x.toNat = 1 := by omega
  rw [hx1] at hlo hhi
  rw [Nat.mul_one] at hlo
  have hr2 : 2 ^ r.toNat * (1 + 1) = 2 ^ (r.toNat + 1) := by rw [Nat.pow_succ]
  rw [hr2] at hhi
  exact ⟨by omega, hlo, hhi⟩

private theorem msb_join_stage {Γ : Env} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [[i64, i64]] → Blocks Val Cont [i64] [[i64, i64]]}
    {entry : Tup Cont [[i64, i64]] → Expr Val Cont [i64]} (k : Nat) (x0 : BitVec 64)
    (hbody : ∀ (J : Cont [i64, i64]) (x r : BitVec 64), MsbInv k x0 x r →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (x, r, ())) m)
    (hentry : ∀ (J : Cont [i64, i64]),
      (∀ x r : BitVec 64, MsbInv k x0 x r → J (x, r, ()) m) →
      wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [[i64, i64]]) bodies entry) m :=
  wp_join_group (fun (x, r, ()) m1 => m1 = m ∧ MsbInv k x0 x r)
    (fun J ⟨x, r, ⟨⟩⟩ _ ⟨hm, hinv⟩ => hm ▸ hbody J x r hinv)
    (fun J hJ => hentry J (fun x r hinv => hJ (x, r, ()) m ⟨rfl, hinv⟩))

local macro "f64_pure_step" : tactic =>
  `(tactic| (
    f64_hsteps_nogrp
    all_goals try first
      | (apply_assumption; done)
      | refine wp_pure_group (fun _ _ => ?_) (fun _ _ => ?_)
      | c0_hsplit))

local macro "f64_pure_acyclic" : tactic =>
  `(tactic| (
    f64_pure_step; f64_pure_step; f64_pure_step; f64_pure_step
    f64_pure_step; f64_pure_step; f64_pure_step; f64_pure_step
    f64_pure_step; f64_pure_step; f64_pure_step; f64_pure_step))

theorem f64u_msb64_wp (Γ : Env) :
    ∀ a m Q X, f64uMsb64Spec a m Q X → Func.wp Γ f64u_msb64_body a m Q X := by
  rintro ⟨x0, ⟨⟩⟩ m Q X hQ
  unfold Func.wp f64u_msb64_body
  f64_hsteps_nogrp
  have h0 := msb_inv_init x0
  refine msb_join_stage 32 x0 (fun _ x r hinv => ?_) (fun J hJ => ?_)
  · f64_hsteps_nogrp
    refine msb_join_stage 16 x0 (fun _ x r hinv => ?_) (fun J hJ => ?_)
    · f64_hsteps_nogrp
      refine msb_join_stage 8 x0 (fun _ x r hinv => ?_) (fun J hJ => ?_)
      · f64_hsteps_nogrp
        refine msb_join_stage 4 x0 (fun _ x r hinv => ?_) (fun J hJ => ?_)
        · f64_hsteps_nogrp
          refine msb_join_stage 2 x0 (fun _ x r hinv => ?_) (fun J hJ => ?_)
          · f64_hsteps_nogrp
            refine wp_join_group
              (fun (r', ()) m1 => m1 = m ∧
                (x0 ≠ 0#64 → r'.toNat < 64 ∧ 2 ^ r'.toNat ≤ x0.toNat ∧
                  x0.toNat < 2 ^ (r'.toNat + 1)))
              (fun _ ⟨r', ⟨⟩⟩ _ ⟨hm, hout⟩ => by
                subst hm; f64_hsteps_nogrp; exact hQ r' hout)
              (fun J hJ => by
                c0_hsplit <;> f64_hsteps_nogrp
                · exact hJ (r + 1#64, ()) m ⟨rfl, msb_step_final_ge hinv (by c0_bound)⟩
                · exact hJ (r, ()) m ⟨rfl, msb_step_final_lt hinv (by c0_bound)⟩)
          · c0_hsplit <;> f64_hsteps_nogrp
            · exact hJ _ _ (msb_step_ge (by omega) (by omega) hinv (by c0_bound))
            · exact hJ _ _ (msb_step_lt hinv (by c0_bound))
        · c0_hsplit <;> f64_hsteps_nogrp
          · exact hJ _ _ (msb_step_ge (by omega) (by omega) hinv (by c0_bound))
          · exact hJ _ _ (msb_step_lt hinv (by c0_bound))
      · c0_hsplit <;> f64_hsteps_nogrp
        · exact hJ _ _ (msb_step_ge (by omega) (by omega) hinv (by c0_bound))
        · exact hJ _ _ (msb_step_lt hinv (by c0_bound))
    · c0_hsplit <;> f64_hsteps_nogrp
      · exact hJ _ _ (msb_step_ge (by omega) (by omega) hinv (by c0_bound))
      · exact hJ _ _ (msb_step_lt hinv (by c0_bound))
  · c0_hsplit <;> f64_hsteps_nogrp
    · exact hJ _ _ (msb_step_ge (by omega) (by omega) h0 (by c0_bound))
    · exact hJ _ _ (msb_step_lt h0 (by c0_bound))

theorem f64u_round_pack_wp (Γ : Env)
    (hMsb : Γ.Has "f64u_msb64" f64uPure1Spec) :
    ∀ a m Q X, f64uPure2Spec a m Q X → Func.wp Γ f64u_round_pack_body a m Q X := by
  rintro ⟨exp, sig55, ⟨⟩⟩ m Q X hQ
  dsimp only [f64uPure2Spec] at hQ
  unfold Func.wp f64u_round_pack_body
  f64_pure_acyclic
  all_goals (c0_call hMsb; intro _; f64_pure_acyclic)

theorem f64u_add_wp (Γ : Env)
    (hPack : Γ.Has "f64u_round_pack" f64uPure2Spec) :
    ∀ a m Q X, f64uPure2Spec a m Q X → Func.wp Γ f64u_add_body a m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X hQ
  dsimp only [f64uPure2Spec] at hQ
  unfold Func.wp f64u_add_body
  f64_pure_acyclic
  all_goals (c0_call hPack; intro _; f64_pure_acyclic)

theorem f64u_sub_wp (Γ : Env)
    (hPack : Γ.Has "f64u_round_pack" f64uPure2Spec) :
    ∀ a m Q X, f64uPure2Spec a m Q X → Func.wp Γ f64u_sub_body a m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X hQ
  dsimp only [f64uPure2Spec] at hQ
  unfold Func.wp f64u_sub_body
  f64_pure_acyclic
  all_goals (c0_call hPack; intro _; f64_pure_acyclic)

theorem f64u_mul_wp (Γ : Env)
    (hMsb : Γ.Has "f64u_msb64" f64uPure1Spec)
    (hPack : Γ.Has "f64u_round_pack" f64uPure2Spec) :
    ∀ a m Q X, f64uPure2Spec a m Q X → Func.wp Γ f64u_mul_body a m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X hQ
  dsimp only [f64uPure2Spec] at hQ
  unfold Func.wp f64u_mul_body
  f64_pure_acyclic
  all_goals
    first
    | (c0_call hPack; intro _; f64_pure_acyclic)
    | (c0_call hMsb; intro _; f64_pure_acyclic;
        all_goals try (c0_call hPack; intro _; f64_pure_acyclic))

theorem f64u_div_wp (Γ : Env)
    (hMsb : Γ.Has "f64u_msb64" f64uPure1Spec)
    (hPack : Γ.Has "f64u_round_pack" f64uPure2Spec) :
    ∀ a m Q X, f64uPure2Spec a m Q X → Func.wp Γ f64u_div_body a m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X hQ
  dsimp only [f64uPure2Spec] at hQ
  unfold Func.wp f64u_div_body
  f64_hsteps_nogrp
  · exact hQ _
  · exact hQ _
  · refine wp_pure_group (fun _ _ => ?_) (fun _ _ => by f64_pure_acyclic)
    f64_hsteps_nogrp
    refine wp_pure_group (fun _ _ => ?_) (fun _ _ => by f64_pure_acyclic)
    f64_hsteps_nogrp
    refine wp_pure_group (fun _ _ => ?_) (fun _ _ => by f64_pure_acyclic)
    f64_hsteps_nogrp
    refine wp_pure_group (fun _ _ => ?_) (fun _ _ => by f64_pure_acyclic)
    f64_hsteps_nogrp
    -- if (ea == 0ULL) { ... f64u_msb64 ... }
    refine wp_pure_group (fun _ _ => ?_) (fun _ _ => by
      c0_hsplit
      · f64_hsteps_nogrp; c0_call hMsb; intro _; f64_pure_acyclic
      · f64_pure_acyclic)
    f64_hsteps_nogrp
    -- if (eb == 0ULL) { ... f64u_msb64 ... }
    refine wp_pure_group (fun _ _ => ?_) (fun _ _ => by
      c0_hsplit
      · f64_hsteps_nogrp; c0_call hMsb; intro _; f64_pure_acyclic
      · f64_pure_acyclic)
    f64_hsteps_nogrp
    -- if (ma < mb) { ... }
    refine wp_pure_group (fun _ _ => ?_) (fun _ _ => by f64_pure_acyclic)
    f64_hsteps_nogrp
    -- while (i < 56ULL)
    refine wp_loop_inv
      (fun (st : Tup Val [i64, i64, i64]) ml => ml = m ∧ st.2.2.1.toNat ≤ 56)
      (fun (st : Tup Val [i64, i64, i64]) _ => 56 - st.2.2.1.toNat)
      (fun J hJ => by f64_hsteps_nogrp; exact hJ _ m ⟨rfl, by dsimp only; decide⟩)
      (fun J ⟨q, r, i, ⟨⟩⟩ ml ⟨hm_eq, hi⟩ hJ => ?_)
    subst hm_eq
    f64_hsteps_nogrp
    · have hilt : i.toNat < 56 := by c0_bound
      refine wp_pure_group (fun _ _ => ?_) (fun _ _ => by f64_pure_acyclic)
      f64_hsteps_nogrp
      exact hJ (_, _, i + 1#64, ()) ml
        (by dsimp; rw [Nat.mod_eq_of_lt (by have := i.isLt; omega)]; omega)
        ⟨rfl, by dsimp; rw [Nat.mod_eq_of_lt (by have := i.isLt; omega)]; omega⟩
    · f64_pure_acyclic
      all_goals
        first
        | (c0_call hPack; intro _; f64_pure_acyclic)
        | (c0_call hMsb; intro _; f64_pure_acyclic;
            all_goals try (c0_call hPack; intro _; f64_pure_acyclic))

theorem f64u_from_u64_wp (Γ : Env)
    (hMsb : Γ.Has "f64u_msb64" f64uPure1Spec) :
    ∀ a m Q X, f64uPure1Spec a m Q X → Func.wp Γ f64u_from_u64_body a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  dsimp only [f64uPure1Spec] at hQ
  unfold Func.wp f64u_from_u64_body
  f64_hsteps_nogrp
  · exact hQ _
  · c0_call hMsb; intro _
    f64_pure_acyclic

theorem f64u_to_u64_wp (Γ : Env) :
    ∀ a m Q X, f64uPure1Spec a m Q X → Func.wp Γ f64u_to_u64_body a m Q X := by
  rintro ⟨a, ⟨⟩⟩ m Q X hQ
  dsimp only [f64uPure1Spec] at hQ
  unfold Func.wp f64u_to_u64_body
  f64_pure_acyclic

theorem u64_mul128_wp (Γ : Env) :
    ∀ a m Q X, u64Mul128Spec a m Q X → Func.wp Γ u64_mul128_body a m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X hQ
  dsimp only [u64Mul128Spec] at hQ
  unfold Func.wp u64_mul128_body
  f64_pure_acyclic

end LeanQbe.T.Examples.Kissat.Proof.Float64
