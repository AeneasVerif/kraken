module

public import LeanQbe.T.Examples.Kissat.FullM7BvaV5Fix
public import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
public import LeanQbe.T.Examples.Kissat.FullM6SatSound
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof2
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof
public import LeanQbe.T.Examples.Kissat.FullM6CompactFlushProof1
public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof3
public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof6
public import LeanQbe.T.Examples.Kissat.FullM4SweepProof
public import LeanQbe.T.Examples.Kissat.FullParseInitLemmas1
public import LeanQbe.T.Examples.Kissat.FullSpec1
public import LeanQbe.T.Examples.Kissat.FullSpec2
public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Examples.Kissat.FullM3BackboneLemmas1
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas1
public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas1
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullBvaFwdSpec
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.WPLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `D-Full` M7 `V5_BVA` Parity + `P1-3` Fix Proofs (`FullM7BvaV5FixProof`)

M1-clean UNSAT-only proofs (`public section`, `0` `@[expose]`, `0` `import all`, `0` SAT proofs):
1. `full_calc_max_v_m7v5_wp`: certifies `Full.fullCalcMaxVSpec` with `cand = 4096ULL`.
2. `full_probe_m7v5_wp`: certifies `m6ProbeSpec` (verbatim match to `FullM6OrchProof1.lean`)
   with `(initial || h->num_irred <= 4096ULL || h->eliminations > 0ULL)` factor gate and
   `fbud = full_min_u64(initial ? (cv * 4 + 1024) : (128 + (dticks >> 8)), 8192)`.
3. `full_forward_sub_m7v5_wp`: certifies `FullFastBveBudgets.fullForwardSubFastSpec` with `P1-3`
   `FL_SUBSUME` cleanup/re-arming on `rr[i..ncand)` even on early budget exit.
4. `full_eliminate_m7v5_wp`: certifies `FullFastSched.schedEliminateSpec` with `NLOG2N` scaling
   (`500ULL * h->eliminations * loge * loge`) and `saved_eb` save/zero/restore around `full_factor`.
5. Closed `32`-row `m7BvaV5FixSpecTable`, `m7BvaV5FixEnv`, `m7BvaV5Fix_moduleOk`, and drop-in
   `SpecEntry.Impl` bridges.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7BvaV5Fix

open Std Std.Sat Std.ExtHashMap LeanQbe.T.Examples.LratBytes
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics
open Kraken.Bedrock2.Test

local macro "m7v5_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. `full_calc_max_v_m7v5` (`Full.fullCalcMaxVSpec`) -/

section CalcMaxVProof

private abbrev fullBvaCapV5 (avail mv nc f0 : Nat) : Nat :=
  if 2 ≤ mv ∧ nc * 48 + 8192 < avail - f0 then
    min 4096 (((avail - f0) - nc * 48 - 4096) / 2688)
  else 0

private def fullCalcMaxVV5 (avail mv nc f0 : Nat) : Nat :=
  let max_v := mv + fullBvaCapV5 avail mv nc f0
  let fixed := fullFixedBytes max_v
  if avail < fixed ∨ avail - fixed < nc * 40 + 136 then mv else max_v

private theorem fullBvaCapV5_le (avail mv nc f0 : Nat) :
    fullBvaCapV5 avail mv nc f0 ≤ 4096 := by
  unfold fullBvaCapV5; split <;> omega

private theorem fullCalcMaxVV5_ge {avail mv nc : Nat} :
    mv ≤ fullCalcMaxVV5 avail mv nc (fullFixedBytes mv) := by
  unfold fullCalcMaxVV5; dsimp only; split <;> omega

private theorem fullCalcMaxVV5_lt {avail mv nc f0 : Nat} (hmv : mv < dimacsBound) :
    fullCalcMaxVV5 avail mv nc f0 < 2 * dimacsBound := by
  have := fullBvaCapV5_le avail mv nc f0
  unfold fullCalcMaxVV5 dimacsBound at *; dsimp only at *; split <;> omega

private theorem fullCalcMaxVV5_fits {avail mv nc : Nat}
    (hfit : fullFixedBytes mv + nc * 40 + 136 ≤ avail) :
    fullFixedBytes (fullCalcMaxVV5 avail mv nc (fullFixedBytes mv)) + nc * 40 + 136 ≤ avail := by
  unfold fullCalcMaxVV5; dsimp only; split <;> omega

private theorem v5_bv64_ofNat_toNat {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem v5_bv64_add_ofNat {a b : Nat} (hab : a + b < 2 ^ 64) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, v5_bv64_ofNat_toNat (by omega), v5_bv64_ofNat_toNat (by omega),
    v5_bv64_ofNat_toNat hab, Nat.mod_eq_of_lt hab]

private theorem v5_bv64_mul_nat (x : BitVec 64) (k : Nat) :
    x * BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat * k) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_mod]

private theorem v5_bv64_ult_eq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, v5_bv64_ofNat_toNat ha, v5_bv64_ofNat_toNat hb]

private theorem v5_bv64_sub_of_le {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  have ha := a.isLt; rw [BitVec.toNat_sub]; omega

private theorem v5_fixed_lt {mv : Nat} (hmv : mv < 2 * dimacsBound) :
    fullFixedBytes mv < 2 ^ 64 := by
  have := fullFixedBytes_lt hmv; omega

private theorem fullCalcMaxVV5_eq1 {avail mv nc f0 : Nat}
    (hlt : avail < fullFixedBytes (mv + fullBvaCapV5 avail mv nc f0)) :
    fullCalcMaxVV5 avail mv nc f0 = mv := by
  unfold fullCalcMaxVV5; dsimp only
  exact ite_eq_left_iff.mpr fun h => absurd (Or.inl hlt) h

private theorem fullCalcMaxVV5_eq2 {avail mv nc f0 : Nat}
    (hlt : avail - fullFixedBytes (mv + fullBvaCapV5 avail mv nc f0) < nc * 40 + 136) :
    fullCalcMaxVV5 avail mv nc f0 = mv := by
  unfold fullCalcMaxVV5; dsimp only
  exact ite_eq_left_iff.mpr fun h => absurd (Or.inr hlt) h

private theorem fullCalcMaxVV5_eq3 {avail mv nc f0 : Nat}
    (h1 : ¬ avail < fullFixedBytes (mv + fullBvaCapV5 avail mv nc f0))
    (h2 : ¬ avail - fullFixedBytes (mv + fullBvaCapV5 avail mv nc f0) < nc * 40 + 136) :
    fullCalcMaxVV5 avail mv nc f0 = mv + fullBvaCapV5 avail mv nc f0 := by
  unfold fullCalcMaxVV5; dsimp only
  exact ite_eq_right_iff.mpr fun h => absurd h (by omega)

private theorem full_calc_max_v_m7v5_post_wp (Γ : Env)
    (hFixed : ∀ a m Q X, Full.fullFixedBytesSpec a m Q X →
      Γ "full_fixed_bytes" [i64] [i64] a m Q X)
    {avail mv nc f0 : Val i64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hmv : mv.toNat < dimacsBound) (hnc : nc.toNat < dimacsBound)
    (hQ : Q (BitVec.ofNat 64 (fullCalcMaxVV5 avail.toNat mv.toNat nc.toNat f0.toNat), ()) m) :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var mv,
        Arg.var (BitVec.ofNat 64 (fullBvaCapV5 avail.toNat mv.toNat nc.toNat f0.toNat)), ()))
        fun p =>
      Expr.call "full_fixed_bytes" (as := [i64]) (bs := [i64]) (Arg.var p.fst, ()) fun p_1 =>
      Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var avail, Arg.var p_1.fst, ())) fun p_2 =>
      Expr.jnz (Arg.var p_2.fst) (Expr.ret (Arg.var mv, ()))
        (Expr.let_ (Op.mk (.sub i64) (Arg.var avail, Arg.var p_1.fst, ())) fun p_2 =>
          Expr.let_ (Op.mk (.mul i64) (Arg.var nc, Arg.imm 40, ())) fun p_3 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var p_3.fst, Arg.imm 136, ())) fun p_4 =>
          Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl)
            (Arg.var p_2.fst, Arg.var p_4.fst, ())) fun p_2 =>
          Expr.jnz (Arg.var p_2.fst) (Expr.ret (Arg.var mv, ()))
            (Expr.ret (Arg.var p.fst, ())))) m := by
  let bva := fullBvaCapV5 avail.toNat mv.toNat nc.toNat f0.toNat
  have hbva_le : bva ≤ 4096 := fullBvaCapV5_le _ _ _ _
  have hmv_b := hmv; have hnc_b := hnc; unfold dimacsBound at hmv_b hnc_b
  let max_v := mv.toNat + bva
  have hmax_bd : max_v < 2 * dimacsBound := by unfold dimacsBound; omega
  have hfx_lt := v5_fixed_lt hmax_bd
  have hmv_add : mv + BitVec.ofNat 64 bva = BitVec.ofNat 64 max_v := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, v5_bv64_ofNat_toNat (by omega), v5_bv64_ofNat_toNat (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  c0_hsteps_nogrp
  rw [hmv_add]
  refine wp_call_of_spec _ _ (hFixed _ _ _ _ ⟨?_, ?_⟩)
  · dsimp only [Arg.val_var]; rw [v5_bv64_ofNat_toNat (by omega)]; exact hmax_bd
  · dsimp only [Arg.val_var]; rw [v5_bv64_ofNat_toNat (by omega)]
    have hav_lt := avail.isLt
    c0_hsteps_nogrp
    · have hlt1 : avail.toNat < fullFixedBytes max_v := by
        rwa [Nat.mod_eq_of_lt hfx_lt] at hc
      rw [fullCalcMaxVV5_eq1 hlt1, BitVec.ofNat_toNat] at hQ; exact hQ
    · rename_i hge1; rw [Nat.mod_eq_of_lt hfx_lt] at hge1
      have hlt2 : avail.toNat - fullFixedBytes max_v < nc.toNat * 40 + 136 := by
        have hfx_mod : (2 ^ 64 - fullFixedBytes max_v + avail.toNat) % 2 ^ 64 =
            avail.toNat - fullFixedBytes max_v := by omega
        have hnc_mod : (nc.toNat * 40 + 136) % 2 ^ 64 = nc.toNat * 40 + 136 :=
          Nat.mod_eq_of_lt (by omega)
        simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfx_lt, hfx_mod, hnc_mod] using hc
      rw [fullCalcMaxVV5_eq2 hlt2, BitVec.ofNat_toNat] at hQ; exact hQ
    · rename_i hge1; rw [Nat.mod_eq_of_lt hfx_lt] at hge1
      have hge2 : ¬ avail.toNat - fullFixedBytes max_v < nc.toNat * 40 + 136 := by
        have hfx_mod : (2 ^ 64 - fullFixedBytes max_v + avail.toNat) % 2 ^ 64 =
            avail.toNat - fullFixedBytes max_v := by omega
        have hnc_mod : (nc.toNat * 40 + 136) % 2 ^ 64 = nc.toNat * 40 + 136 :=
          Nat.mod_eq_of_lt (by omega)
        simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfx_lt, hfx_mod, hnc_mod] using hc
      rw [fullCalcMaxVV5_eq3 hge1 hge2] at hQ; exact hQ

open FullParseInitTactics in
private theorem v5_bva_ult_eq (avail f0 nc : Val i64) (hfle : f0.toNat ≤ avail.toNat)
    (hnc : nc.toNat < dimacsBound) :
    ((nc * (48 : BitVec 64) + 8192).ult (avail - f0)) =
      decide (nc.toNat * 48 + 8192 < avail.toNat - f0.toNat) := by
  have hnc_b := hnc; unfold dimacsBound at hnc_b
  have hav_lt := avail.isLt
  have hrem_eq : avail - f0 = BitVec.ofNat 64 (avail.toNat - f0.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [v5_bv64_sub_of_le hfle, v5_bv64_ofNat_toNat (by omega)]
  have hnc48 : nc * (48 : BitVec 64) + (8192 : BitVec 64) =
      BitVec.ofNat 64 (nc.toNat * 48 + 8192) := by
    rw [show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl, v5_bv64_mul_nat]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, v5_bv64_ofNat_toNat (by omega),
      show (8192 : BitVec 64).toNat = 8192 from rfl, v5_bv64_ofNat_toNat (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hrem_eq, hnc48, v5_bv64_ult_eq (by omega) (by omega)]

open FullParseInitTactics in
private theorem full_calc_bva_min_m7v5_wp (Γ : Env)
    {avail mv nc f0 : Val i64} {m : Mem 64} {Q : Post [i64]} {X : XPost} {J : Cont [i64]}
    (hmv_ge : 2 ≤ mv.toNat) (hnc : nc.toNat < dimacsBound)
    (hfle : f0.toNat ≤ avail.toNat)
    (hgt : nc.toNat * 48 + 8192 < avail.toNat - f0.toNat)
    (hJ : ∀ xs m_1, xs.1 = BitVec.ofNat 64 (fullBvaCapV5 avail.toNat mv.toNat nc.toNat f0.toNat) ∧
      m_1 = m → J xs m_1) :
    wp Γ Q X (Expr.let_ (Op.mk (.mul i64) (Arg.var nc, Arg.imm 48, ())) fun p_4 =>
      Expr.let_ (Op.mk (.sub i64) (Arg.var (BitVec.ofNat 64 (avail.toNat - f0.toNat)),
          Arg.var p_4.fst, ())) fun p_5 =>
      Expr.let_ (Op.mk (.sub i64) (Arg.var p_5.fst, Arg.imm 4096, ())) fun p_6 =>
      Expr.let_ (Op.mk (.udiv 64) (Arg.var p_6.fst, Arg.imm 2688, ())) fun p_7 =>
      Expr.group (sig := [[i64]])
        (fun _Js => Blocks.cons (fun p_8 => Expr.jump J (Arg.var p_8.fst, ())) Blocks.nil)
        fun Js =>
          Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl)
            (Arg.imm 4096, Arg.var p_7.fst, ())) fun p_8 =>
          Expr.jnz (Arg.var p_8.fst) (Expr.jump Js.fst (Arg.imm 4096, ()))
            (Expr.jump Js.fst (Arg.var p_7.fst, ()))) m := by
  have hnc_b := hnc; unfold dimacsBound at hnc_b
  have hav_lt := avail.isLt
  let rem0 := avail.toNat - f0.toNat
  let max_bva := (rem0 - nc.toNat * 48 - 4096) / 2688
  fp_head_steps
  have h48 : (nc * (48 : BitVec 64)).toNat = nc.toNat * 48 := by
    rw [show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl, v5_bv64_mul_nat,
      v5_bv64_ofNat_toNat (by omega)]
  have hsub1 : (BitVec.ofNat 64 rem0 - nc * (48 : BitVec 64)).toNat =
      rem0 - nc.toNat * 48 := by
    rw [v5_bv64_sub_of_le (by
        rw [v5_bv64_ofNat_toNat (by dsimp [rem0]; omega), h48]
        dsimp [rem0]; omega),
      v5_bv64_ofNat_toNat (by dsimp [rem0]; omega), h48]
  have hsub3 : BitVec.ofNat 64 rem0 - nc * (48 : BitVec 64) - (4096 : BitVec 64) =
      BitVec.ofNat 64 (rem0 - nc.toNat * 48 - 4096) := by
    apply BitVec.eq_of_toNat_eq
    have h4096 : (4096 : BitVec 64).toNat = 4096 := rfl
    rw [v5_bv64_sub_of_le (by rw [hsub1, h4096]; dsimp [rem0]; omega), hsub1, h4096,
      v5_bv64_ofNat_toNat (by dsimp [rem0]; omega)]
  rw [hsub3]
  apply wp_udiv_of
  · dsimp only [Arg.val_imm]; intro h; have := congrArg BitVec.toNat h; simp at this
  · dsimp only [Arg.val_var, Arg.val_imm]
    have hmb64 : max_bva < 2 ^ 64 := by
      dsimp [max_bva]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by dsimp [rem0]; omega)
    have hdiv_eq : BitVec.ofNat 64 (rem0 - nc.toNat * 48 - 4096) / (2688 : BitVec 64) =
        BitVec.ofNat 64 max_bva := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_udiv, v5_bv64_ofNat_toNat (by dsimp [rem0]; omega),
        show (2688 : BitVec 64).toNat = 2688 from rfl, v5_bv64_ofNat_toNat hmb64]
    rw [hdiv_eq]
    refine wp_join_group (ts := [i64]) (fun v mx =>
      v.1 = BitVec.ofNat 64 (fullBvaCapV5 avail.toNat mv.toNat nc.toNat f0.toNat) ∧ mx = m)
      ?_ ?_
    · rintro _ ⟨bx_v, ⟨⟩⟩ mx ⟨rfl, rfl⟩
      simp only [Blocks.get_here]; fp_head_steps; exact hJ (_, ()) _ ⟨rfl, rfl⟩
    · intro Jm hJm
      fp_head_steps
      rw [show (4096 : BitVec 64) = BitVec.ofNat 64 4096 from rfl,
        v5_bv64_ult_eq (by omega) hmb64]
      refine wp_jnz_of (fun hclt => ?_) (fun hcge => ?_)
      · dsimp only [Arg.val_var] at hclt; rw [decide_eq_true_eq] at hclt; fp_head_steps
        refine hJm (_, ()) m ⟨?_, rfl⟩
        unfold fullBvaCapV5
        rw [ite_eq_left_iff.mpr fun h => absurd (And.intro hmv_ge hgt) h]
        exact congrArg (BitVec.ofNat 64) (Nat.min_eq_left (Nat.le_of_lt hclt)).symm
      · dsimp only [Arg.val_var] at hcge; rw [decide_eq_false_iff_not] at hcge; fp_head_steps
        refine hJm (_, ()) m ⟨?_, rfl⟩
        unfold fullBvaCapV5
        rw [ite_eq_left_iff.mpr fun h => absurd (And.intro hmv_ge hgt) h]
        exact congrArg (BitVec.ofNat 64) (Nat.min_eq_right (Nat.le_of_not_gt hcge)).symm

private def fullCalcMaxVV5ExactSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (avail, mv, nc, f0, ()) m Q _ =>
    mv.toNat < dimacsBound ∧ nc.toNat < dimacsBound ∧
    f0.toNat = fullFixedBytes mv.toNat ∧ fullFixedBytes mv.toNat ≤ avail.toNat ∧
    Q (BitVec.ofNat 64 (fullCalcMaxVV5 avail.toNat mv.toNat nc.toNat f0.toNat), ()) m

open FullParseInitTactics in
private theorem full_calc_max_v_m7v5_bva_wp (Γ : Env)
    {avail mv nc f0 : Val i64} {m : Mem 64} {Q : Post [i64]} {X : XPost} {J : Cont [i64]}
    (_hmv : mv.toNat < dimacsBound) (hnc : nc.toNat < dimacsBound)
    (hfle : f0.toNat ≤ avail.toNat)
    (hJ : ∀ xs m_1, xs.1 = BitVec.ofNat 64 (fullBvaCapV5 avail.toNat mv.toNat nc.toNat f0.toNat) ∧
      m_1 = m → J xs m_1) :
    wp Γ Q X (Expr.let_ (Op.mk (.cmp .uge i64 Ty.bool rfl) (Arg.var mv, Arg.imm 2, ())) fun p =>
      Expr.jnz (Arg.var p.fst)
        (Expr.let_ (Op.mk (.mul i64) (Arg.var nc, Arg.imm 48, ())) fun p_1 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var p_1.fst, Arg.imm 8192, ())) fun p_2 =>
          Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var (avail - f0), Arg.var p_2.fst, ()))
            fun p_3 =>
            Expr.jnz (Arg.var p_3.fst)
              (Expr.let_ (Op.mk (.mul i64) (Arg.var nc, Arg.imm 48, ())) fun p_4 =>
                Expr.let_ (Op.mk (.sub i64) (Arg.var (avail - f0), Arg.var p_4.fst, ()))
                  fun p_5 =>
                Expr.let_ (Op.mk (.sub i64) (Arg.var p_5.fst, Arg.imm 4096, ())) fun p_6 =>
                Expr.let_ (Op.mk (.udiv 64) (Arg.var p_6.fst, Arg.imm 2688, ())) fun p_7 =>
                Expr.group (sig := [[i64]])
                  (fun _Js => Blocks.cons (fun p_8 => Expr.jump J (Arg.var p_8.fst, ())) Blocks.nil)
                  fun Js =>
                    Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl)
                      (Arg.imm 4096, Arg.var p_7.fst, ())) fun p_8 =>
                    Expr.jnz (Arg.var p_8.fst) (Expr.jump Js.fst (Arg.imm 4096, ()))
                      (Expr.jump Js.fst (Arg.var p_7.fst, ())))
              (Expr.jump J (Arg.imm 0, ())))
        (Expr.jump J (Arg.imm 0, ()))) m := by
  have hav_lt := avail.isLt
  have hrem_eq : avail - f0 = BitVec.ofNat 64 (avail.toNat - f0.toNat) := by
    apply BitVec.eq_of_toNat_eq; rw [v5_bv64_sub_of_le hfle, v5_bv64_ofNat_toNat (by omega)]
  fp_head_steps
  have hule2 : ((2 : BitVec 64).ule mv) = decide (2 ≤ mv.toNat) := by
    simp [BitVec.ule]
  rw [hule2]
  refine wp_jnz_of (fun hmv_ge => ?_) (fun hmv_lt => ?_)
  · dsimp only [Arg.val_var] at hmv_ge; rw [decide_eq_true_eq] at hmv_ge; fp_head_steps
    rw [v5_bva_ult_eq avail f0 nc hfle hnc]
    refine wp_jnz_of (fun hgt => ?_) (fun hle => ?_)
    · dsimp only [Arg.val_var] at hgt; rw [decide_eq_true_eq] at hgt; fp_head_steps
      rw [hrem_eq]
      exact full_calc_bva_min_m7v5_wp Γ hmv_ge hnc hfle hgt hJ
    · dsimp only [Arg.val_var] at hle; rw [decide_eq_false_iff_not] at hle; fp_head_steps
      refine hJ (0#64, ()) m ⟨?_, rfl⟩
      unfold fullBvaCapV5; rw [ite_eq_right_iff.mpr fun h => absurd h.2 hle]
  · dsimp only [Arg.val_var] at hmv_lt; rw [decide_eq_false_iff_not] at hmv_lt; fp_head_steps
    refine hJ (0#64, ()) m ⟨?_, rfl⟩
    unfold fullBvaCapV5; rw [ite_eq_right_iff.mpr fun h => absurd h.1 hmv_lt]

private theorem full_calc_max_v_m7v5_exact_wp (Γ : Env)
    (hFixed : ∀ a m Q X, Full.fullFixedBytesSpec a m Q X →
      Γ "full_fixed_bytes" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullCalcMaxVV5ExactSpec a m Q X →
      Func.wp Γ full_calc_max_v_m7v5_body a m Q X := by
  rintro ⟨avail, mv, nc, f0, ⟨⟩⟩ m Q X ⟨hmv, hnc, hf0, hfx, hQ⟩
  have hfle : f0.toNat ≤ avail.toNat := by omega
  unfold Func.wp full_calc_max_v_m7v5_body
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun v mb =>
    v.1 = BitVec.ofNat 64 (fullBvaCapV5 avail.toNat mv.toNat nc.toNat f0.toNat) ∧ mb = m)
    ?_ ?_
  · rintro _ ⟨bv_v, ⟨⟩⟩ mb ⟨rfl, rfl⟩
    simp only [Blocks.get_here]
    exact full_calc_max_v_m7v5_post_wp Γ hFixed hmv hnc hQ
  · intro J hJ
    exact full_calc_max_v_m7v5_bva_wp Γ hmv hnc hfle hJ

/-- Parametric `Func.wp` proof for `full_calc_max_v_m7v5` against `Full.fullCalcMaxVSpec`. -/
theorem full_calc_max_v_m7v5_wp (Γ : Env)
    (hFixed : ∀ a m Q X, Full.fullFixedBytesSpec a m Q X →
      Γ "full_fixed_bytes" [i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullCalcMaxVSpec a m Q X →
      Func.wp Γ full_calc_max_v_m7v5_body a m Q X := by
  rintro ⟨avail, mv, nc, f0, ⟨⟩⟩ m Q X ⟨hmv, hnc, hf0, hfx, hQ⟩
  have hret_lt : fullCalcMaxVV5 avail.toNat mv.toNat nc.toNat f0.toNat < 2 * dimacsBound :=
    fullCalcMaxVV5_lt hmv
  have hret64 : fullCalcMaxVV5 avail.toNat mv.toNat nc.toNat f0.toNat < 2 ^ 64 := by
    unfold dimacsBound at hret_lt; omega
  have hret_toNat :
      (BitVec.ofNat 64 (fullCalcMaxVV5 avail.toNat mv.toNat nc.toNat f0.toNat)).toNat =
        fullCalcMaxVV5 avail.toNat mv.toNat nc.toNat f0.toNat := v5_bv64_ofNat_toNat hret64
  refine full_calc_max_v_m7v5_exact_wp Γ hFixed _ m Q X ⟨hmv, hnc, hf0, by omega, ?_⟩
  refine hQ _ ?_ (by rw [hret_toNat]; exact hret_lt) ?_
  · rw [hret_toNat, hf0]; exact fullCalcMaxVV5_ge
  · rw [hret_toNat, hf0]; exact fullCalcMaxVV5_fits (by omega)

end CalcMaxVProof

/-! ## 2. `full_probe_m7v5` (`m6ProbeSpec`, matching `FullM6OrchProof1.lean`) -/

section ProbeProof

/-- Tail probing specification matching `FullM6OrchProof1.m6ProbeTailSpec` verbatim. -/
def m6ProbeTailSpec : Spec [i64, i64] [i64] := fun (h, _dticks, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0 ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem m6ProbeTailSpec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {dticks : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hcl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    m6ProbeTailSpec (c.hdr, dticks, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩

theorem m6ProbeTailSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : m6ProbeTailSpec xs m Q X) : m6ProbeTailSpec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

/-- Probing specification matching `FullM6OrchProof1.m6ProbeSpec` verbatim (`rfl`-unifiable). -/
def m6ProbeSpec : Spec [i64, .bool] [i64] := fun (h, _initial, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0 ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem m6ProbeSpec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {initial : Bool} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hcl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    m6ProbeSpec (c.hdr, initial, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩

theorem m6ProbeSpec_elim {h : BitVec 64} {initial : Bool} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hs : m6ProbeSpec (h, initial, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0 ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' := hs

theorem m6ProbeSpec_monoX {xs : Tup Val [i64, .bool]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : m6ProbeSpec xs m Q X) : m6ProbeSpec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

private theorem v5_probe_ret_wm {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s0 s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {r : BitVec 64} {Q : Post [i64]} {X : XPost}
    {args : Tup (Arg Val) [i64, i64, i64]}
    {k : Tup Val [] → Expr Val Cont [i64]}
    (hk_ret : k () = .ret (Arg.imm r, ()))
    (hargs : vals args = (c.hdr, 0#64, BitVec.ofNat 64 s.scratch.search_ticks.toNat, ()) ∨
      vals args = (c.hdr, 0#64, s.scratch.search_ticks, ()))
    (hSetWm : ∀ a m' Q' X', m6HdrW2aSpec [i64, i64] [] a m' Q' X' →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m' Q' X')
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hfu : s.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hr : r = 1#64 ∨ r = 20#64) (hu : r = 20#64 → F0.Unsat)
    (h1 : r = 1#64 → FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (.call "m6_hdr_set_watermark" (as := [i64, i64, i64]) (bs := []) args k) m := by
  have hargs' : ∃ v, vals args = (c.hdr, 0#64, v, ()) :=
    hargs.elim (fun h => ⟨_, h⟩) (fun h => ⟨_, h⟩)
  obtain ⟨v, hv⟩ := hargs'
  refine m6Hdr_call_m6HdrW2a hv (fun _ _ h => hSetWm _ _ _ _ h) hcfg hext hlen hm
    fun _ ext' s' m' hc' hlen' hms' hext' _ hm' => ?_
  rw [hk_ret]; c0_hsteps_nogrp
  exact hQ ext' s' m' hlen' hext' (by rw [hc']; exact hfu) hr hu
    (fun h => let ⟨hi, hcl⟩ := h1 h
      ⟨fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hi hlen' hc' hms') hext',
        by rw [hc']; exact hcl⟩) hm'

/-- Parametric `Func.wp` proof for `full_probe_m7v5` against `m6ProbeSpec`. -/
theorem full_probe_m7v5_wp (Γ : Env)
    (hDticks : ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Γ "full_probe_dticks_m6_hdr" [i64, .bool] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hCong : ∀ a m Q X, FullM3CongBva.m3CongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (hRebuild : ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hRedD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hBumpD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hSweep : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense_m6" [i64, i64, i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, Full.fullSubstituteSpec a m Q X →
      Γ "full_substitute" [i64] [i64] a m Q X)
    (hTail : ∀ a m Q X, m6ProbeTailSpec a m Q X →
      Γ "full_probe_tail_m6" [i64, i64] [i64] a m Q X)
    (hBackbone : ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFactor : ∀ a m Q X, FullM3CongBva.fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6ProbeSpec a m Q X →
      Func.wp Γ full_probe_m7v5_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X hs
  rcases m6ProbeSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_probe_m7v5_body
  c0_hsteps_nogrp
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDticks _ _ _ _ h)
    hinv.cfgOk hinv.extOk hinv.sparse.lengths hm
    fun ⟨dticks, ⟨⟩⟩ ext0 s0 m0 hc0 hlen0 hms0 hext0 _ hm0 => ?_
  have hinv0 := fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hinv hlen0 hc0 hms0) hext0
  have hcl0' : s0.core.cur_level = 0 := by rw [hc0]; exact hcl0
  refine wp_join_group (ts := []) (fun _ m1 => ∃ ext1 s1, FullM6HdrInv c F0 ext1 s1 ∧
      s1.core.cur_level = 0 ∧ s1.core.fuel = s.core.fuel ∧ (FullM6HdrMem c ext1 s1 ⋆ R) m1) ?_ ?_
  · rintro _ _ m1 ⟨ext1, s1, hinv1, hcl1, hfu1, hm1⟩
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ mW => ∃ extW sW, FullM6HdrInv c F0 extW sW ∧
        sW.core.cur_level = 0 ∧ sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c extW sW ⋆ R) mW) ?_ ?_
    · rintro _ ⟨_, ⟨⟩⟩ mW ⟨extW, sW, hinvW, hclW, hfuW, hmW⟩
      c0_hsteps_nogrp
      refine wp_join_group (ts := []) (fun _ mT => ∃ extT sT, FullM6HdrInv c F0 extT sT ∧
          sT.core.cur_level = 0 ∧ sT.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          (FullM6HdrMem c extT sT ⋆ R) mT) ?_ ?_
      · rintro _ _ mT ⟨extT, sT, hinvT, hclT, hfuT, hmT⟩
        c0_hsteps_nogrp
        refine wp_join_group (ts := []) (fun _ mRet => ∃ extRet sRet,
            FullM6HdrInv c F0 extRet sRet ∧ sRet.core.cur_level = 0 ∧
            sRet.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extRet sRet ⋆ R) mRet)
          ?_ ?_
        · rintro _ _ mRet ⟨extRet, sRet, hinvRet, hclRet, hfuRet, hmRet⟩
          refine wp_m6Hdr_focus_frame hmRet fun hmRetf => ?_
          c0_hsteps_nogrp
          exact v5_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvRet.cfgOk hinvRet.extOk
            hinvRet.sparse.lengths hfuRet (Or.inl rfl) (fun h => by cases h)
            (fun _ => ⟨hinvRet, hclRet⟩) (fullM6HdrMem_unfocus hmRetf) (hQ 1#64)
        · intro Jret hJret; c0_hsteps_nogrp
          refine wp_join_group (ts := []) (fun _ mInc => ∃ extInc sInc,
              FullM6HdrInv c F0 extInc sInc ∧ sInc.core.cur_level = 0 ∧
              sInc.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extInc sInc ⋆ R) mInc)
            ?_ ?_
          · rintro _ _ mInc ⟨extInc, sInc, hinvInc, hclInc, hfuInc, hmInc⟩
            refine wp_m6Hdr_focus_frame hmInc fun hmIncf => ?_
            c0_hsteps_nogrp
            · exact v5_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvInc.cfgOk hinvInc.extOk
                hinvInc.sparse.lengths hfuInc (Or.inr rfl)
                (fun _ => fullM6HdrInv_inconsistent_unsat hinvInc ‹_›)
                (fun h => by cases h) (fullM6HdrMem_unfocus hmIncf) (hQ 20#64)
            · exact hJret () mInc
                ⟨extInc, sInc, hinvInc, hclInc, hfuInc, fullM6HdrMem_unfocus hmIncf⟩
          · intro Jinc hJinc; c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun _ mF0 => ∃ extF0 sF0,
                FullM6HdrInv c F0 extF0 sF0 ∧ sF0.core.cur_level = 0 ∧
                sF0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extF0 sF0 ⋆ R) mF0)
              ?_ ?_
            · rintro _ _ mF0 ⟨extF0, sF0, hinvF0, hclF0, hfuF0, hmF0⟩
              refine wp_m6Hdr_focus_frame hmF0 fun hmTf => ?_
              c0_hsteps_nogrp
              · c0_call hEnter
                refine ⟨c, F0, sF0, m6ExtMem (m6ExtAddr c.hdr) extF0 ⋆ R, rfl, hinvF0.sparse,
                  hmTf, fun ok sF mF hclF hfuF hdenF hspF hmF => ?_⟩
                have hmF' := fullM6HdrMem_unfocus hmF
                c0_hsteps_nogrp
                · have hdenF' := hdenF ‹_›
                  refine wp_join_group (ts := [i64]) (fun _ mB => mB = mF)
                    (fun _ ⟨fbud0, ⟨⟩⟩ mB hmB => by
                      subst hmB
                      c0_hsteps_nogrp; c0_call hMin; intro fbud _; c0_hsteps_nogrp
                      c0_call hFactor
                      refine ⟨c, F0, sF, m6ExtMem (m6ExtAddr c.hdr) extF0 ⋆ R, rfl, hdenF',
                        hmF, fun _ sFc mFc hdenFc _ hfuFc _ hmFc => ?_⟩
                      c0_hsteps_nogrp; c0_call hRebuild
                      refine ⟨c, F0, sFc, m6ExtMem (m6ExtAddr c.hdr) extF0 ⋆ R, rfl, hdenFc,
                        hmFc, fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                      have hinvR := FullM6HdrInv.mk_inv hinvF0.cfgOk hinvF0.extOk hspR
                      have hmR' := fullM6HdrMem_unfocus hmR
                      have hfuR' : sR.core.fuel.toNat ≤ s.core.fuel.toNat := by
                        rw [hfuFc] at hfuR; exact Nat.le_trans hfuR (Nat.le_trans hfuF hfuF0)
                      c0_hsteps_nogrp
                      · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                        c0_hsteps_nogrp
                        exact v5_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                          hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                          (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                      · exact hJret () mR ⟨extF0, sR, hinvR, hclR, hfuR', hmR'⟩)
                    (fun _ hJ0 => by c0_hsteps_nogrp <;> exact hJ0 (_, ()) mF rfl)
                · have hinvF := FullM6HdrInv.mk_inv hinvF0.cfgOk hinvF0.extOk (hspF ‹_›)
                  exact hJinc () mF ⟨extF0, sF, hinvF, hclF, Nat.le_trans hfuF hfuF0, hmF'⟩
            · intro Jfact hJfact
              refine wp_m6Hdr_focus_frame hmT fun hmTf => ?_
              c0_hsteps_nogrp
              · exact hJfact () mT ⟨extT, sT, hinvT, hclT, hfuT, fullM6HdrMem_unfocus hmTf⟩
              · exact hJfact () mT ⟨extT, sT, hinvT, hclT, hfuT, fullM6HdrMem_unfocus hmTf⟩
              · exact hJfact () mT ⟨extT, sT, hinvT, hclT, hfuT, fullM6HdrMem_unfocus hmTf⟩
              · exact hJinc () mT ⟨extT, sT, hinvT, hclT, hfuT, fullM6HdrMem_unfocus hmTf⟩
      · intro JT hJT; c0_hsteps_nogrp
        · refine wp_m6Hdr_focus_frame hmW fun hmWf => ?_
          c0_hsteps_nogrp
          · c0_call hBackbone
            refine ⟨c, F0, sW, m6ExtMem (m6ExtAddr c.hdr) extW ⋆ R, rfl, hinvW.sparse, hmWf,
              fun rB sB mB hspB hclB _ hfuB hdB huB hmB => ?_⟩
            have hinvB := FullM6HdrInv.mk_inv hinvW.cfgOk hinvW.extOk hspB
            have hmB' := fullM6HdrMem_unfocus hmB
            c0_hsteps_nogrp
            · refine wp_m6Hdr_focus_frame hmB' fun hmBf => ?_
              c0_hsteps_nogrp
              exact v5_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvB.cfgOk hinvB.extOk
                hinvB.sparse.lengths (Nat.le_trans hfuB hfuW) (Or.inr rfl)
                (fun _ => huB ‹_›) (fun h => by cases h) (fullM6HdrMem_unfocus hmBf) (hQ 20#64)
            · exact hJT () mB ⟨extW, sB, hinvB, hclB, Nat.le_trans hfuB hfuW, hmB'⟩
          · exact hJT () mW ⟨extW, sW, hinvW, hclW, hfuW, fullM6HdrMem_unfocus hmWf⟩
        · c0_call hTail
          refine m6ProbeTailSpec_of hinvW hclW hmW
            fun rT extT sT mT hlT heT hfuT hdT huT h1T hmT => ?_
          c0_hsteps_nogrp
          · refine wp_m6Hdr_focus_frame hmT fun hmTf => ?_
            c0_hsteps_nogrp
            exact v5_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvW.cfgOk heT hlT
              (Nat.le_trans hfuT hfuW) (Or.inr rfl) (fun _ => huT ‹_›)
              (fun h => by cases h) (fullM6HdrMem_unfocus hmTf) (hQ 20#64)
          · exact hJT () mT ⟨extT, sT, (h1T (hdT.resolve_right ‹_›)).1,
              (h1T (hdT.resolve_right ‹_›)).2, Nat.le_trans hfuT hfuW, hmT⟩
    · intro JW hJW; c0_hsteps_nogrp
      refine wp_loop_inv (fun (round, ()) mL => round.toNat ≤ 2 ∧
          ∃ extL sL, FullM6HdrInv c F0 extL sL ∧ sL.core.cur_level = 0 ∧
            sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extL sL ⋆ R) mL)
        (fun (round, ()) _ => 2 - round.toNat)
        (fun JL hJL => by
          c0_hsteps_nogrp
          exact hJL (0#64, ()) m1 ⟨Nat.zero_le _, ext1, s1, hinv1, hcl1,
            by rw [hfu1]; exact Nat.le_refl _, hm1⟩)
        (fun JL (round, ()) mL ⟨hnd_le, extL, sL, hinvL, hclL, hfuL, hmL⟩ hJL => ?_)
      · refine wp_m6Hdr_focus_frame hmL fun hmLf => ?_
        c0_hsteps_nogrp
        · have hnd_lt : round.toNat < 2 := BitVec.lt_def.mp ‹_›
          have hnd1 : (round + 1#64).toNat = round.toNat + 1 := by bv_omega
          refine wp_join_group (ts := []) (fun _ mD => ∃ extD sD, FullM6HdrInv c F0 extD sD ∧
              sD.core.cur_level = 0 ∧ sD.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullM6HdrMem c extD sD ⋆ R) mD) ?_ ?_
          · rintro _ _ mD ⟨extD, sD, hinvD, hclD, hfuD, hmD⟩
            c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun _ mS => ∃ extS sS, FullM6HdrInv c F0 extS sS ∧
                sS.core.cur_level = 0 ∧ sS.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                (FullM6HdrMem c extS sS ⋆ R) mS) ?_ ?_
            · rintro _ _ mS ⟨extS, sS, hinvS, hclS, hfuS, hmS⟩
              refine wp_m6Hdr_focus_frame hmS fun hmSf => ?_
              c0_hsteps_nogrp
              · exact hJW (round, ()) mS ⟨extS, sS, hinvS, hclS, hfuS, fullM6HdrMem_unfocus hmSf⟩
              · exact hJL (round + 1#64, ()) mS (by dsimp only; omega)
                  ⟨by omega, extS, sS, hinvS, hclS, hfuS, fullM6HdrMem_unfocus hmSf⟩
            · intro JS hJS; refine wp_m6Hdr_focus_frame hmD fun hmDf => ?_
              c0_hsteps_nogrp
              · c0_call hSubst
                refine ⟨c, F0, sD, m6ExtMem (m6ExtAddr c.hdr) extD ⋆ R, rfl, hinvD.sparse, hmDf,
                  fun rS sS mS hspS hclS hfuS hdS huS hmS => ?_⟩
                have hinvS := FullM6HdrInv.mk_inv hinvD.cfgOk hinvD.extOk hspS
                have hmS' := fullM6HdrMem_unfocus hmS
                c0_hsteps_nogrp
                · refine wp_m6Hdr_focus_frame hmS' fun hmSf => ?_
                  c0_hsteps_nogrp
                  exact v5_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvS.cfgOk hinvS.extOk
                    hinvS.sparse.lengths (Nat.le_trans hfuS hfuD) (Or.inr rfl)
                    (fun _ => huS ‹_›) (fun h => by cases h) (fullM6HdrMem_unfocus hmSf) (hQ 20#64)
                · exact hJS () mS ⟨extD, sS, hinvS, hclS, Nat.le_trans hfuS hfuD, hmS'⟩
              · exact hJS () mD ⟨extD, sD, hinvD, hclD, hfuD, fullM6HdrMem_unfocus hmDf⟩
          · intro JD hJD
            c0_hsteps_nogrp; c0_call hEnter
            refine ⟨c, F0, sL, m6ExtMem (m6ExtAddr c.hdr) extL ⋆ R, rfl, hinvL.sparse, hmLf,
              fun ok sE mE hclE hfuE hdenE hspE hmE => ?_⟩
            have hmE' := fullM6HdrMem_unfocus hmE
            c0_hsteps_nogrp
            · have hdenE' := hdenE ‹_›
              refine wp_join_group (ts := []) (fun _ mC => ∃ extC sC,
                  FullM6HdrCfgOk c ∧ M6HdrExtOk extC ∧ FullDenseInv c F0 sC ∧
                  sC.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  (FullM6HdrMem c extC sC ⋆ R) mC) ?_ ?_
              · rintro _ _ mC ⟨extC, sC, _, hextC, hdenC, hfuC, hmC⟩
                c0_hsteps_nogrp
                refine wp_join_group (ts := []) (fun _ mW2 => ∃ extW2 sW2,
                    FullM6HdrCfgOk c ∧ M6HdrExtOk extW2 ∧ FullDenseInv c F0 sW2 ∧
                    sW2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    (FullM6HdrMem c extW2 sW2 ⋆ R) mW2) ?_ ?_
                · rintro _ _ mW2 ⟨extW2, sW2, _, hextW2, hdenW2, hfuW2, hmW2⟩
                  refine wp_m6Hdr_focus_frame hmW2 fun hmW2f => ?_
                  c0_hsteps_nogrp; c0_call hRebuild
                  refine ⟨c, F0, sW2, m6ExtMem (m6ExtAddr c.hdr) extW2 ⋆ R, rfl, hdenW2, hmW2f,
                    fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                  have hinvR := FullM6HdrInv.mk_inv hinvL.cfgOk hextW2 hspR
                  have hmR' := fullM6HdrMem_unfocus hmR
                  have hfuR' := Nat.le_trans hfuR hfuW2
                  c0_hsteps_nogrp
                  · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                    c0_hsteps_nogrp
                    exact v5_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                      hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                      (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                  · exact hJD () mR ⟨extW2, sR, hinvR, hclR, hfuR', hmR'⟩
                · intro JW2 hJW2
                  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDelay _ _ _ _ h)
                    hinvL.cfgOk hextC hdenC.lengths hmC
                    fun ⟨del2, ⟨⟩⟩ extCd sCd mCd hcCd hlCd hmsCd hextCd _ hmCd => ?_
                  have hdenCd := fullDenseInv_of_core_eq hdenC hlCd hcCd hmsCd.extPres
                  have hfuCd : sCd.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcCd]; exact hfuC
                  c0_hsteps_nogrp
                  · exact hJW2 () mCd ⟨extCd, sCd, hinvL.cfgOk, hextCd, hdenCd, hfuCd, hmCd⟩
                  · refine wp_m6Hdr_focus_frame hmCd fun hmCdf => ?_
                    c0_hsteps_nogrp; c0_call hSweep
                    refine ⟨c, F0, sCd, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenCd,
                      hmCdf, fun rS sS mS hdenS _ hfuS _ huS hmS => ?_⟩
                    have hfuS' := Nat.le_trans hfuS hfuCd
                    c0_hsteps_nogrp
                    · c0_call hRebuild
                      refine ⟨c, F0, sS, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenS, hmS,
                        fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                      have hinvR := FullM6HdrInv.mk_inv hinvL.cfgOk hextCd hspR
                      have hmR' := fullM6HdrMem_unfocus hmR
                      refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                      c0_hsteps_nogrp
                      exact v5_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                        hinvR.sparse.lengths (Nat.le_trans hfuR hfuS') (Or.inr rfl)
                        (fun _ => huS ‹_›) (fun h => by cases h)
                        (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                    · have hmS' := fullM6HdrMem_unfocus hmS
                      refine wp_join_group (ts := []) (fun _ mSd => ∃ extSd sSd,
                          M6HdrExtOk extSd ∧ FullDenseInv c F0 sSd ∧
                          sSd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c extSd sSd ⋆ R) mSd)
                        (fun _ _ mSd ⟨extSd, sSd, hextSd, hdenSd, hfuSd, hmSd⟩ =>
                          hJW2 () mSd ⟨extSd, sSd, hinvL.cfgOk, hextSd, hdenSd, hfuSd, hmSd⟩) ?_
                      intro JSd hJSd; c0_hsteps_nogrp
                      refine wp_join_group (ts := []) (fun _ mSd => ∃ extSd sSd,
                          M6HdrExtOk extSd ∧ FullDenseInv c F0 sSd ∧
                          sSd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c extSd sSd ⋆ R) mSd)
                        (fun _ _ mSd ⟨extSd, sSd, hextSd, hdenSd, hfuSd, hmSd⟩ => by
                          refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hBumpD _ _ _ _ h)
                            hinvL.cfgOk hextSd hdenSd.lengths hmSd
                            fun _ extSd' sSd' mSd' hcSd hlSd hmsSd hextSd' _ hmSd' => ?_
                          exact hJSd () mSd' ⟨extSd', sSd', hextSd',
                            fullDenseInv_of_core_eq hdenSd hlSd hcSd hmsSd.extPres,
                            by rw [hcSd]; exact hfuSd, hmSd'⟩) ?_
                      intro JSdb hJSdb
                      refine wp_m6Hdr_focus_frame hmS' fun hmSf => ?_
                      c0_hsteps_nogrp
                      · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRedD _ _ _ _ h)
                          hinvL.cfgOk hextCd hdenS.lengths (fullM6HdrMem_unfocus hmSf)
                          fun _ extSd sSd mSd hcSd hlSd hmsSd hextSd _ hmSd => ?_
                        exact hJSd () mSd ⟨extSd, sSd, hextSd,
                          fullDenseInv_of_core_eq hdenS hlSd hcSd hmsSd.extPres,
                          by rw [hcSd]; exact hfuS', hmSd⟩
                      · exact hJSdb () mS
                          ⟨extCd, sS, hextCd, hdenS, hfuS', fullM6HdrMem_unfocus hmSf⟩
                      · exact hJSdb () mS
                          ⟨extCd, sS, hextCd, hdenS, hfuS', fullM6HdrMem_unfocus hmSf⟩
              · intro JC hJC
                refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDelay _ _ _ _ h)
                  hinvL.cfgOk hinvL.extOk hdenE'.lengths hmE'
                  fun ⟨del1, ⟨⟩⟩ extEd sEd mEd hcEd hlEd hmsEd hextEd _ hmEd => ?_
                have hdenEd := fullDenseInv_of_core_eq hdenE' hlEd hcEd hmsEd.extPres
                have hfuEd : sEd.core.fuel.toNat ≤ s.core.fuel.toNat := by
                  rw [hcEd]; exact Nat.le_trans hfuE hfuL
                c0_hsteps_nogrp
                · exact hJC () mEd ⟨extEd, sEd, hinvL.cfgOk, hextEd, hdenEd, hfuEd, hmEd⟩
                · refine wp_m6Hdr_focus_frame hmEd fun hmEdf => ?_
                  c0_hsteps_nogrp; c0_call hCong
                  refine ⟨c, F0, sEd, m6ExtMem (m6ExtAddr c.hdr) extEd ⋆ R, rfl, hdenEd, hmEdf,
                    fun rC sC mC hdenC _ hfuC hdomC huC hmC => ?_⟩
                  have hfuC' : sC.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hfuC]; exact hfuEd
                  c0_hsteps_nogrp
                  · c0_call hRebuild
                    refine ⟨c, F0, sC, m6ExtMem (m6ExtAddr c.hdr) extEd ⋆ R, rfl, hdenC, hmC,
                      fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                    have hinvR := FullM6HdrInv.mk_inv hinvL.cfgOk hextEd hspR
                    have hmR' := fullM6HdrMem_unfocus hmR
                    refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                    c0_hsteps_nogrp
                    exact v5_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                      hinvR.sparse.lengths (Nat.le_trans hfuR hfuC') (Or.inr rfl)
                      (fun _ => huC ‹_›) (fun h => by cases h)
                      (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                  · have hmC' := fullM6HdrMem_unfocus hmC
                    refine wp_join_group (ts := []) (fun _ mCd => ∃ extCd sCd,
                        M6HdrExtOk extCd ∧ FullDenseInv c F0 sCd ∧
                        sCd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullM6HdrMem c extCd sCd ⋆ R) mCd)
                      (fun _ _ mCd ⟨extCd, sCd, hextCd, hdenCd, hfuCd, hmCd⟩ =>
                        hJC () mCd ⟨extCd, sCd, hinvL.cfgOk, hextCd, hdenCd, hfuCd, hmCd⟩) ?_
                    intro JCd hJCd; c0_hsteps_nogrp
                    refine wp_join_group (ts := []) (fun _ mCd => ∃ extCd sCd,
                        M6HdrExtOk extCd ∧ FullDenseInv c F0 sCd ∧
                        sCd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullM6HdrMem c extCd sCd ⋆ R) mCd)
                      (fun _ _ mCd ⟨extCd, sCd, hextCd, hdenCd, hfuCd, hmCd⟩ => by
                        refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hBumpD _ _ _ _ h)
                          hinvL.cfgOk hextCd hdenCd.lengths hmCd
                          fun _ extCd' sCd' mCd' hcCd hlCd hmsCd hextCd' _ hmCd' => ?_
                        exact hJCd () mCd' ⟨extCd', sCd', hextCd',
                          fullDenseInv_of_core_eq hdenCd hlCd hcCd hmsCd.extPres,
                          by rw [hcCd]; exact hfuCd, hmCd'⟩) ?_
                    intro JCdb hJCdb
                    refine wp_m6Hdr_focus_frame hmC' fun hmCf => ?_
                    c0_hsteps_nogrp
                    · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRedD _ _ _ _ h)
                        hinvL.cfgOk hextEd hdenC.lengths (fullM6HdrMem_unfocus hmCf)
                        fun _ extCd sCd mCd hcCd hlCd hmsCd hextCd _ hmCd => ?_
                      exact hJCd () mCd ⟨extCd, sCd, hextCd,
                        fullDenseInv_of_core_eq hdenC hlCd hcCd hmsCd.extPres,
                        by rw [hcCd]; exact hfuC', hmCd⟩
                    · exact hJCdb () mC ⟨extEd, sC, hextEd, hdenC, hfuC', fullM6HdrMem_unfocus hmCf⟩
                    · exact hJCdb () mC ⟨extEd, sC, hextEd, hdenC, hfuC', fullM6HdrMem_unfocus hmCf⟩
            · have hinvE := FullM6HdrInv.mk_inv hinvL.cfgOk hinvL.extOk (hspE ‹_›)
              refine wp_m6Hdr_focus_frame hmE' fun hmEf => ?_
              c0_hsteps_nogrp
              exact v5_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvE.cfgOk hinvE.extOk
                hinvE.sparse.lengths (Nat.le_trans hfuE hfuL) (Or.inr rfl)
                (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›)
                (fun h => by cases h) (fullM6HdrMem_unfocus hmEf) (hQ 20#64)
            · have hinvE := FullM6HdrInv.mk_inv hinvL.cfgOk hinvL.extOk (hspE ‹_›)
              exact hJD () mE ⟨extL, sE, hinvE, hclE, Nat.le_trans hfuE hfuL, hmE'⟩
        · exact hJW (round, ()) mL ⟨extL, sL, hinvL, hclL, hfuL, fullM6HdrMem_unfocus hmLf⟩
  · intro J1 hJ1; c0_hsteps_nogrp
    · exact hJ1 () m0 ⟨ext0, s0, hinv0, hcl0', hc0 ▸ rfl, hm0⟩
    · refine wp_m6Hdr_focus_frame hm0 fun hm0f => ?_
      c0_hsteps_nogrp; c0_call hIlog; intro logp _ _
      c0_hsteps_nogrp; c0_call hScale
      refine ⟨c, _, m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R, rfl,
        (fullState_upd_probe_step hinv0.sparse.lengths s0.scratch.probe_limit
          (s0.scratch.probings + 1#64)).1, by assumption, fun sd => ?_⟩
      c0_hsteps_nogrp
      have hst1 := fullState_upd_probe_step hinv0.sparse.lengths
        (s0.scratch.conflicts + sd) (s0.scratch.probings + 1#64)
      have hinv1 := fullM6HdrInv_of_probeStep hinv0 hst1
      exact hJ1 () _ ⟨ext0, _, hinv1, hst1.2.1 ▸ hcl0',
        by rw [hst1.2.1, hc0], fullM6HdrMem_unfocus (by assumption)⟩

end ProbeProof

/-! ## 3. `full_forward_sub_m7v5` (`FullFastBveBudgets.fullForwardSubFastSpec`) -/

section ForwardSubProof

private theorem v5_zero_mem_arenaRefs3 {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k) (hpos : 0 < k.arena_len) :
    0 ∈ fullArenaClauseRefsCore k := by
  rcases ha.len_ok with hz | h3
  · omega
  · unfold fullArenaClauseRefsCore
    cases hal : k.arena_len with
    | zero => omega
    | succ n =>
      rw [fullArenaScanRefs]
      simp only [show 0 + 3 ≤ n + 1 by omega, ↓reduceIte]
      exact List.mem_cons_self

/-- Forward check-clause contract matching `FullM6BveFwdProof3.fullFwdCheckClM6Spec` verbatim. -/
def m7v5FwdCheckClSpec : Spec [i64, i32] [.bool] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.red_refs = s.scratch.red_refs →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem m7v5FwdCheckClSpec_noExit :
    ∀ xs m Q X, m7v5FwdCheckClSpec xs m Q X →
      m7v5FwdCheckClSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

/-- Parametric `Func.wp` proof for `full_forward_sub_m7v5`, certifying canonical
`FullFastBveBudgets.fullForwardSubFastSpec`. -/
theorem full_forward_sub_m7v5_wp (Γ : Env)
    (hDedup : ∀ a m Q X, fullFwdDedupBinsSpec a m Q X →
      Γ "full_fwd_dedup_bins" [i64] [.bool] a m Q X)
    (hFlushUnits : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X)
    (hCollectSort : ∀ a m Q X, fullFwdCollectSortM6Spec a m Q X →
      Γ "full_fwd_collect_sort_m7" [i64] [i64] a m Q X)
    (hFlushLarge : ∀ a m Q X, fullFwdFlushLargeM6Spec a m Q X →
      Γ "full_fwd_flush_large_m7" [i64] [] a m Q X)
    (hCheckCl : ∀ a m Q X, m7v5FwdCheckClSpec a m Q X →
      Γ "full_fwd_check_cl_m7" [i64, i32] [.bool] a m Q X)
    (hConnectSub : ∀ a m Q X, fullFwdConnectSubsumerM6Spec a m Q X →
      Γ "full_fwd_connect_subsumer_m7" [i64, i32] [] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hReconnect : ∀ a m Q X, fullFwdReconnectIrredM6Spec a m Q X →
      Γ "full_fwd_reconnect_irred_m7" [i64] [] a m Q X) :
    ∀ a m Q X, fullForwardSubFastSpec a m Q X →
      Func.wp Γ full_forward_sub_m7v5_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hd0, hm0, hQ⟩
  have hmx := c.hmaxv; have harc := c.harena; have hrc := c.hred
  unfold dimacsBound at hmx harc hrc
  obtain ⟨F_cur, hw0⟩ := hd0.exists_witness
  unfold Func.wp full_forward_sub_m7v5_body
  c0_hsplit
  · c0_hsteps!; exact hQ 1#64 s0 m0 hd0 rfl rfl (Or.inl rfl) (by simp) hm0
  · c0_hsteps_nogrp
    m7v5_call hDedup
    refine ⟨c, F0, F_cur, s0, R, rfl, hw0, hm0, ?_⟩
    intro ok1 s1 m1 hdw1 hcv1 hfl1 hf1 hm1
    c0_hsplit
    · c0_hsteps_nogrp
      m7v5_call hFlushUnits
      refine fullDenseFlushUnitsM6Spec_intro rfl hdw1 hm1 ?_
      intro ok2 s2 m2 hdw2 hcv2 _ hfl2 _ _ _ _ _ _ _ hf2 hm2
      c0_hsplit
      · c0_hsteps_nogrp
        m7v5_call hCollectSort
        refine fullFwdCollectSortM6Spec_intro rfl hdw2 hm2 ?_
        intro ncand s3 m3 hdw3 hcv3 hal3 hfl3 _ _ _ hnc_le hrr3 hm3
        c0_hsplit
        · c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun r => (r, ()))
            (fun r => (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat))
            (fun _ r ⟨hr_disj, hr20⟩ => by
              c0_hsteps!
              exact hQ r s3 m3 hdw3.toDense (hcv3.trans (hcv2.trans hcv1))
                (hfl3.trans (hfl2.trans hfl1)) hr_disj hr20 hm3)
            (fun J7 hJ7 => by
              c0_hsplit
              · c0_hsteps!
                exact hJ7 20#64 ⟨Or.inr rfl, fun _ =>
                  hdw3.2.1.ext_sound.2 (hdw3.2.1.inconsistent_sound hc)⟩
              · c0_hsteps!; exact hJ7 1#64 ⟨Or.inl rfl, by simp⟩)
        · c0_hsteps_nogrp
          m7v5_call hFlushLarge
          refine fullFwdFlushLargeM6Spec_intro rfl hdw3 hm3 ?_
          intro s4 m4 hdw4 hcv4 har4 hal4 hfl4 _ _ _ hrr4 _ _ _ _ hm4
          have hrr4_ok : ∀ k < ncand.toNat,
              (s4.scratch.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s4 := by
            intro k hk; rw [hrr4]
            have hrefs4 : fullArenaClauseRefs s4 = fullArenaClauseRefs s3 := by
              unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har4, hal4]
            rw [hrefs4]; exact hrr3 k hk
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i64, i64])
            (fun r_lp (i, rem, ()) ml => ∃ sl : FullState,
              i.toNat ≤ ncand.toNat ∧ r_lp = ncand.toNat - i.toNat ∧
              FullDenseInvW c F0 F_cur sl ∧
              sl.core.cur_vars = s0.core.cur_vars ∧ sl.core.fuel = s0.core.fuel ∧
              fullArenaClauseRefs sl = fullArenaClauseRefs s4 ∧
              sl.scratch.red_refs = s4.scratch.red_refs ∧
              (FullMem c sl ⋆ R) ml)
            ?_ ?_
          · rintro L r_lp ⟨i, rem, ⟨⟩⟩ ml hL
              ⟨sl, hi_le, rfl, hdwl, hcvl, hfll, hrefsl, hrrl, hml⟩
            refine wp_join0 (P := fun mb => mb = ml)
              (fun _ mb hmb => by
                rcases hmb.symm with rfl
                refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
                  (fun sf mf =>
                    FullDenseInvW c F0 F_cur sf ∧
                    sf.core.cur_vars = s0.core.cur_vars ∧ sf.core.fuel = s0.core.fuel ∧
                    (FullMem c sf ⋆ R) mf)
                  (fun _ sf mf ⟨hdwf, hcvf, hflf, hmf⟩ => by
                    c0_hsteps_nogrp
                    c0_hsplit
                    · c0_hsteps!
                      exact hQ 20#64 sf mf hdwf.toDense hcvf hflf (Or.inr rfl)
                        (fun _ => hdwf.2.1.ext_sound.2 (hdwf.2.1.inconsistent_sound hc)) hmf
                    · c0_hsteps_nogrp
                      m7v5_call hFlushUnits
                      refine fullDenseFlushUnitsM6Spec_intro rfl hdwf hmf ?_
                      intro ok_f s5 m5 hdw5 hcv5 _ hfl5 _ _ _ _ _ _ _ hf5 hm5
                      c0_hsplit
                      · c0_hsteps_nogrp
                        m7v5_call hReconnect
                        refine fullFwdReconnectIrredM6Spec_intro rfl hdw5 hm5 ?_
                        intro s6 m6 hdw6 hcv6 _ hfl6 _ _ hm6
                        c0_hsplit
                        · c0_hsteps_nogrp
                          refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                            (fun r => (r, ()))
                            (fun r => (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat))
                            (fun _ r ⟨hr_disj, hr20⟩ => by
                              c0_hsteps!
                              exact hQ r s6 m6 hdw6.toDense (hcv6.trans (hcv5.trans hcvf))
                                (hfl6.trans (hfl5.trans hflf)) hr_disj hr20 hm6)
                            (fun J20 hJ20 => by
                              c0_hsplit
                              · c0_hsteps!
                                exact hJ20 20#64 ⟨Or.inr rfl, fun _ =>
                                  hdw6.2.1.ext_sound.2 (hdw6.2.1.inconsistent_sound hc)⟩
                              · c0_hsteps!; exact hJ20 1#64 ⟨Or.inl rfl, by simp⟩)
                      · c0_hsteps!
                        exact hQ 20#64 s5 m5 hdw5.toDense (hcv5.trans hcvf) (hfl5.trans hflf)
                          (Or.inr rfl) (fun _ => hf5 (by simpa using hc)) hm5)
                  (fun Jc hJc => by
                    c0_hsplit
                    · c0_hsplit
                      · have hcvl_le := hdwl.1.core_ok.cur_vars_le
                        c0_hsteps_nogrp
                        -- Loop 1: clear `FL_SUBSUME` on `0 ..< cv`
                        refine wp_loop_group (ts := [i64])
                          (fun rem_v (v, ()) mv => ∃ fl_v : List (BitVec 32),
                            let sv : FullState :=
                              { sl with core := { sl.core with flags := fl_v } }
                            fl_v.length = c.max_vars ∧ v.toNat ≤ sl.core.cur_vars ∧
                            rem_v = sl.core.cur_vars - v.toNat ∧ (FullMem c sv ⋆ R) mv)
                          ?_ ?_
                        · rintro Lv rem_v ⟨v, ⟨⟩⟩ mv hLv ⟨fl_v, hflv, hv_le, rfl, hmv⟩
                          c0_hsplit
                          · have hv_lt : v.toNat < sl.core.cur_vars := by
                              rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                            have hv_fl : v.toNat < fl_v.length := by omega
                            have hv1 : (v + 1#64).toNat = v.toNat + 1 := by c0_bound
                            c0_hsteps!
                            exact hLv (sl.core.cur_vars - (v + 1#64).toNat) (v + 1#64, ()) _
                              (by omega) ⟨_, by simp [hflv], by omega, rfl, hm⟩
                          · -- Loop 2 (`P1-3`): re-arm `FL_SUBSUME` on remaining `rr[i ..< ncand)`
                            let sv0 : FullState :=
                              { sl with core := { sl.core with flags := fl_v } }
                            have hdw_v0 : FullDenseInvW c F0 F_cur sv0 :=
                              m6_fullDenseInvW_with_flags hdwl hflv
                            c0_hsteps_nogrp
                            refine wp_loop_group (ts := [i64])
                              (fun rem_ri (ri, ()) mri => ∃ fl_r : List (BitVec 32),
                                let sr : FullState :=
                                  { sv0 with core := { sv0.core with flags := fl_r } }
                                fl_r.length = c.max_vars ∧ ri.toNat ≤ ncand.toNat ∧
                                rem_ri = ncand.toNat - ri.toNat ∧ (FullMem c sr ⋆ R) mri)
                              ?_ ?_
                            · rintro Lri rem_ri ⟨ri, ⟨⟩⟩ mri hLri
                                ⟨fl_r, hflr, hri_le, rfl, hmri⟩
                              c0_hsplit
                              · have hri_lt : ri.toNat < ncand.toNat := hc
                                have hri_rr : ri.toNat < sv0.scratch.red_refs.length := by
                                  rw [hdw_v0.1.scratch_ok.red_refs_len]; omega
                                have hrcr_ref : (sv0.scratch.red_refs[ri.toNat]'hri_rr).toNat ∈
                                    fullArenaClauseRefs sv0 := by
                                  change _ ∈ fullArenaClauseRefs sl
                                  rw [hrefsl]
                                  have h0 := hrr4_ok ri.toNat hri_lt
                                  rw [← hrrl, List.getElem?_eq_getElem hri_rr,
                                    Option.getD_some] at h0
                                  exact h0
                                let rcr := sv0.scratch.red_refs[ri.toNat]'hri_rr
                                have hrcr_wf := hdw_v0.2.1.arena.refs_wf rcr.toNat hrcr_ref
                                have hal_r := hdw_v0.1.core_ok.arena_len_le
                                have har_len := hdw_v0.1.core_ok.arena_len_arr
                                have hrcr_ar : (rcr.setWidth 64).toNat < sv0.core.arena.length := by
                                  rw [har_len, m6_zext32_toNat]; omega
                                have hri1 : (ri + 1#64).toNat = ri.toNat + 1 := by c0_bound
                                c0_hsteps_nogrp
                                refine wp_join0 (P := fun mj => ∃ fl' : List (BitVec 32),
                                    fl'.length = c.max_vars ∧
                                    (FullMem c { sv0 with core := { sv0.core with
                                      flags := fl' } } ⋆ R) mj)
                                  (fun _ mj ⟨fl', hfl', hmj⟩ => by
                                    c0_hsteps!
                                    exact hLri (ncand.toNat - (ri + 1#64).toNat) (ri + 1#64, ()) mj
                                      (by omega) ⟨fl', hfl', by omega, rfl, hmj⟩)
                                  (fun Jri hJri => by
                                    c0_hsplit
                                    · have hrcr2_ar : (rcr.setWidth 64 + 2#64).toNat <
                                          sv0.core.arena.length := by
                                        rw [har_len]; c0_bound
                                      let rsz := sv0.core.arena[(rcr.setWidth 64 + 2#64).toNat]'
                                        hrcr2_ar
                                      have hrsz_eq : rsz.toNat =
                                          fullArenaClauseSizeCore sv0.core rcr.toNat := by
                                        unfold rsz fullArenaClauseSizeCore
                                        rw [List.getElem?_eq_getElem (by rw [har_len]; omega),
                                          Option.getD_some]
                                        exact congrArg BitVec.toNat (m6_getElem_congr
                                          (by rw [BitVec.toNat_add, m6_zext32_toNat,
                                            show (2#64 : BitVec 64).toNat = 2 from rfl,
                                            Nat.mod_eq_of_lt (by omega)]) _ _)
                                      c0_hsteps_nogrp
                                      refine wp_loop_group (ts := [i32])
                                        (fun rem_rk (rk, ()) mrk =>
                                          ∃ fl_rk : List (BitVec 32),
                                            let srk : FullState :=
                                              { sv0 with core := { sv0.core with flags := fl_rk } }
                                            fl_rk.length = c.max_vars ∧ rk.toNat ≤ rsz.toNat ∧
                                            rem_rk = rsz.toNat - rk.toNat ∧
                                            (FullMem c srk ⋆ R) mrk)
                                        ?_ ?_
                                      · rintro Lrk rem_rk ⟨rk, ⟨⟩⟩ mrk hLrk
                                          ⟨fl_rk, hflrk, hrk_le, rfl, hmrk⟩
                                        c0_hsplit
                                        · have hrk_lt : rk.toNat < rsz.toNat := hc
                                          have hpi_ar : (rcr.setWidth 64 + 3#64 +
                                                rk.setWidth 64).toNat <
                                              sv0.core.arena.length := by
                                            rw [har_len]; c0_bound
                                          have hrk1 : (rk + 1#32).toNat = rk.toNat + 1 := by
                                            c0_bound
                                          c0_hsteps_nogrp
                                          refine wp_join0 (P := fun mj =>
                                              ∃ fl' : List (BitVec 32), fl'.length = c.max_vars ∧
                                              (FullMem c { sv0 with core := { sv0.core with
                                                flags := fl' } } ⋆ R) mj)
                                            (fun _ mj ⟨fl', hfl', hmj⟩ => by
                                              c0_hsteps!
                                              exact hLrk (rsz.toNat - (rk + 1#32).toNat)
                                                (rk + 1#32, ()) mj (by omega)
                                                ⟨fl', hfl', by omega, rfl, hmj⟩)
                                            (fun Jrk hJrk => by
                                              c0_hsplit
                                              · have hlv_lt : ((sv0.core.arena[(rcr.setWidth 64 +
                                                    3#64 + rk.setWidth 64).toNat]'hpi_ar >>>
                                                    (1 : Nat)).setWidth 64).toNat <
                                                    fl_rk.length := by
                                                  have hpi_mod : (rcr.toNat + BitVec.toNat 3#64 +
                                                      rk.toNat) % 2 ^ 64 =
                                                      (rcr.setWidth 64 + 3#64 +
                                                        rk.setWidth 64).toNat := by
                                                    rw [BitVec.toNat_add, BitVec.toNat_add,
                                                      m6_zext32_toNat, m6_zext32_toNat,
                                                      show (3#64 : BitVec 64).toNat = 3 from rfl,
                                                      Nat.mod_eq_of_lt (by omega),
                                                      Nat.mod_eq_of_lt (by omega),
                                                      Nat.mod_eq_of_lt (by omega)]
                                                  have har_eq : sv0.core.arena[(rcr.toNat +
                                                      BitVec.toNat 3#64 + rk.toNat) % 2 ^ 64]'(by
                                                        rw [hpi_mod]; exact hpi_ar) =
                                                      sv0.core.arena[(rcr.setWidth 64 + 3#64 +
                                                        rk.setWidth 64).toNat]'hpi_ar :=
                                                    m6_getElem_congr hpi_mod _ _
                                                  have hcv_mod :
                                                      sl.core.cur_vars % 2 ^ 64 =
                                                        sl.core.cur_vars :=
                                                    Nat.mod_eq_of_lt (by omega)
                                                  rw [hcv_mod] at hc
                                                  have hdiv_lt : (sv0.core.arena[(rcr.setWidth 64 +
                                                      3#64 + rk.setWidth 64).toNat]'
                                                      hpi_ar).toNat / 2 < sl.core.cur_vars := by
                                                    simpa [har_eq] using hc
                                                  have hsh1 :
                                                      ((sv0.core.arena[(rcr.setWidth 64 + 3#64 +
                                                            rk.setWidth 64).toNat]'hpi_ar
                                                          >>> (1 : Nat)) : BitVec 32).toNat =
                                                      (sv0.core.arena[(rcr.setWidth 64 + 3#64 +
                                                          rk.setWidth 64).toNat]'
                                                          hpi_ar).toNat / 2 := by
                                                    rw [BitVec.toNat_ushiftRight,
                                                      Nat.shiftRight_eq_div_pow]
                                                  rw [hflrk, m6_zext32_toNat, hsh1]; omega
                                                c0_hsteps!
                                                exact hJrk _ ⟨_, by simp [hflrk], hm⟩
                                              · c0_hsteps!; exact hJrk mrk ⟨fl_rk, hflrk, hmrk⟩)
                                        · c0_hsteps!; exact hJri mrk ⟨fl_rk, hflrk, hmrk⟩
                                      · intro Lrk hLrk; c0_hsteps!
                                        exact hLrk rsz.toNat (0#32, ()) mri
                                          ⟨fl_r, hflr, Nat.zero_le _, by simp, hmri⟩
                                    · c0_hsteps!; exact hJri mri ⟨fl_r, hflr, hmri⟩)
                              · -- Loop 3: arena scan for `PH_SUBSUME`
                                let sv1 : FullState :=
                                  { sv0 with core := { sv0.core with flags := fl_r } }
                                have hdw_v1 : FullDenseInvW c F0 F_cur sv1 :=
                                  m6_fullDenseInvW_with_flags hdw_v0 hflr
                                c0_hsteps_nogrp
                                refine wp_loop_group (ts := [i64])
                                  (fun rem_p (p, ()) mp => ∃ sp : FullState,
                                    p.toNat ≤ sp.core.arena_len ∧
                                    rem_p = sp.core.arena_len - p.toNat ∧
                                    (p.toNat = sp.core.arena_len ∨
                                      p.toNat ∈ fullArenaClauseRefs sp) ∧
                                    FullDenseInvW c F0 F_cur sp ∧
                                    sp.core.cur_vars = s0.core.cur_vars ∧
                                    sp.core.arena_len = sl.core.arena_len ∧
                                    sp.core.fuel = s0.core.fuel ∧
                                    (FullMem c sp ⋆ R) mp)
                                  ?_ ?_
                                · rintro Lp rem_p ⟨p, ⟨⟩⟩ mp hLp
                                    ⟨sp, hp_le, rfl, hp_mem, hdwp, hcvp, halp, hflp, hmp⟩
                                  have hal_p := hdwp.1.core_ok.arena_len_le
                                  c0_hsplit
                                  · have hp_lt : p.toNat < sp.core.arena_len := by
                                      rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                                    have hp_ref : p.toNat ∈ fullArenaClauseRefs sp :=
                                      hp_mem.resolve_left (by omega)
                                    have hwf_p := hdwp.2.1.arena.refs_wf p.toNat hp_ref
                                    have hp_ar : p.toNat < sp.core.arena.length := by
                                      rw [hdwp.1.core_ok.arena_len_arr]; omega
                                    have hp2_ar : (p + 2#64).toNat < sp.core.arena.length := by
                                      rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
                                    have hp32 : (p.setWidth 32).toNat = p.toNat := by
                                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                                    let hdr_p := sp.core.arena[p.toNat]'hp_ar
                                    let sz_p := sp.core.arena[(p + 2#64).toNat]'hp2_ar
                                    have hsz_p :
                                        sz_p.toNat = fullArenaClauseSizeCore sp.core p.toNat := by
                                      unfold sz_p fullArenaClauseSizeCore
                                      rw [List.getElem?_eq_getElem (by
                                        rw [hdwp.1.core_ok.arena_len_arr]; omega), Option.getD_some]
                                      exact congrArg BitVec.toNat
                                        (m6_getElem_congr (by c0_bound) _ _)
                                    c0_hsteps_nogrp
                                    m7v5_call hArenaNext
                                    dsimp only [vals, Arg.val]
                                    refine ⟨c, sp, R, rfl, hdwp.1, hmp, ?_⟩
                                    have hnb := fullArenaNextOff_bounds (ar := sp.core.arena)
                                      (alen := sp.core.arena_len) (cref := p.toNat) hwf_p.1
                                    have hnp_mem :=
                                      FullDenseWatchHelpers.fullArenaClauseRefs_next_mem
                                        hdwp.2.1.arena hp_ref
                                    let np := (BitVec.ofNat 32 (fullArenaNextOff sp.core.arena
                                      sp.core.arena_len (p.setWidth 32).toNat)).setWidth 64
                                    have hnp_toNat : np.toNat =
                                        fullArenaNextOff sp.core.arena
                                          sp.core.arena_len p.toNat := by
                                      dsimp only [np]
                                      rw [hp32, m6_zext32_toNat, BitVec.toNat_ofNat,
                                        Nat.mod_eq_of_lt (by omega)]
                                    c0_hsteps_nogrp
                                    refine wp_join0 (P := fun mj => ∃ sj : FullState,
                                        FullDenseInvW c F0 F_cur sj ∧
                                        sj.core.cur_vars = s0.core.cur_vars ∧
                                        sj.core.arena_len = sl.core.arena_len ∧
                                        sj.core.fuel = s0.core.fuel ∧
                                        fullArenaClauseRefs sj = fullArenaClauseRefs sp ∧
                                        (FullMem c sj ⋆ R) mj)
                                      (fun _ mj ⟨sj, hdwj, hcvj, halj, hflj, hrefsj, hmj⟩ => by
                                        c0_hsteps!
                                        exact hLp (sj.core.arena_len - np.toNat) (np, ()) mj
                                          (by omega) ⟨sj, by omega, rfl, by
                                            rw [hnp_toNat, halj, ← halp, hrefsj]; exact hnp_mem,
                                           hdwj, hcvj, halj, hflj, hmj⟩)
                                      (fun Jp hJp => by
                                        c0_hsplit
                                        · c0_hsteps_nogrp
                                          let v' := hdr_p &&& ~~~0x01000000#32
                                          let sc : FullState :=
                                            { sp with core := { sp.core with
                                              arena := sp.core.arena.set p.toNat v' } }
                                          have hhdr_eq : hdr_p = fullArenaHdr sp p.toNat := by
                                            unfold hdr_p fullArenaHdr fullArenaHdrCore
                                            rw [List.getElem?_eq_getElem hp_ar, Option.getD_some]
                                          have hcb := m6_bit24_clear_pres hdr_p
                                          have hset := m6_fullDenseInvW_set_hdr_bit24 hdwp hp_ref
                                            (v' := v') (by rw [← hhdr_eq]; exact hcb.1)
                                            (by rw [← hhdr_eq]; exact hcb.2)
                                          refine wp_join0 (P := fun mj => ∃ sj : FullState,
                                              FullDenseInvW c F0 F_cur sj ∧
                                              sj.core.cur_vars = s0.core.cur_vars ∧
                                              sj.core.arena_len = sl.core.arena_len ∧
                                              sj.core.fuel = s0.core.fuel ∧
                                              fullArenaClauseRefs sj = fullArenaClauseRefs sp ∧
                                              (FullMem c sj ⋆ R) mj)
                                            (fun _ mj hmj => hJp mj hmj)
                                            (fun J52 hJ52 => by
                                              c0_hsplit
                                              · c0_hsteps_nogrp
                                                refine wp_loop_group (ts := [i32])
                                                  (fun rem_k (k, ()) mk =>
                                                    ∃ fl_k : List (BitVec 32),
                                                      let sk : FullState :=
                                                        { sc with core := { sc.core with
                                                          flags := fl_k } }
                                                      fl_k.length = c.max_vars ∧
                                                      k.toNat ≤ sz_p.toNat ∧
                                                      rem_k = sz_p.toNat - k.toNat ∧
                                                      (FullMem c sk ⋆ R) mk)
                                                  ?_ ?_
                                                · rintro Lk rem_k ⟨k, ⟨⟩⟩ mk hLk
                                                    ⟨fl_k, hflk, hk_le, rfl, hmk⟩
                                                  c0_hsplit
                                                  · have hk_lt : k.toNat < sz_p.toNat := hc
                                                    have hpi_ar : (p + 3#64 + k.setWidth 64).toNat <
                                                        sc.core.arena.length := by
                                                      rw [hset.1.1.core_ok.arena_len_arr]; c0_bound
                                                    have hk1 : (k + 1#32).toNat = k.toNat + 1 := by
                                                      c0_bound
                                                    c0_hsteps_nogrp
                                                    refine wp_join0 (P := fun mj => ∃ fl' : List
                                                        (BitVec 32),
                                                        fl'.length = c.max_vars ∧
                                                        (FullMem c { sc with core := { sc.core with
                                                          flags := fl' } } ⋆ R) mj)
                                                      (fun _ mj ⟨fl', hfl', hmj⟩ => by
                                                        c0_hsteps!
                                                        exact hLk (sz_p.toNat - (k + 1#32).toNat)
                                                          (k + 1#32, ()) mj (by omega)
                                                          ⟨fl', hfl', by omega, rfl, hmj⟩)
                                                      (fun J65 hJ65 => by
                                                        c0_hsplit
                                                        · have hlv_lt : ((sc.core.arena[(p + 3#64 +
                                                              k.setWidth 64).toNat]'hpi_ar >>>
                                                              (1 : Nat)).setWidth 64).toNat <
                                                              fl_k.length := by
                                                            have hpi_mod : (p + 3#64 +
                                                                k.setWidth 64).toNat =
                                                                (p.toNat + BitVec.toNat 3#64 +
                                                                  k.toNat) % 2 ^ 64 := by
                                                              rw [BitVec.toNat_add,
                                                                BitVec.toNat_add,
                                                                m6_zext32_toNat]
                                                              simp only [BitVec.toNat_ofNat]
                                                              c0_bound
                                                            have har_eq : sc.core.arena[(p.toNat +
                                                                BitVec.toNat 3#64 +
                                                                k.toNat) % 2 ^ 64]'(by
                                                                  rw [hset.1.1.core_ok
                                                                    |>.arena_len_arr]
                                                                  c0_bound) =
                                                                sc.core.arena[(p + 3#64 +
                                                                  k.setWidth 64).toNat]'hpi_ar :=
                                                              m6_getElem_congr hpi_mod.symm _ _
                                                            have hcv_mod :
                                                                sl.core.cur_vars % 2 ^ 64 =
                                                                sl.core.cur_vars :=
                                                              Nat.mod_eq_of_lt (by
                                                                rw [hcvl]; have :=
                                                                  hset.1.1.core_ok.cur_vars_le
                                                                omega)
                                                            rw [hcv_mod] at hc
                                                            have hdiv_lt : (sc.core.arena[(p +
                                                                3#64 +
                                                                k.setWidth 64).toNat]'hpi_ar).toNat
                                                                / 2 < sl.core.cur_vars := by
                                                              simpa [har_eq] using hc
                                                            have hsh1 :
                                                                ((sc.core.arena[(p + 3#64 +
                                                                      k.setWidth 64).toNat]'hpi_ar
                                                                    >>> (1 : Nat)) :
                                                                  BitVec 32).toNat =
                                                                (sc.core.arena[(p + 3#64 +
                                                                    k.setWidth 64).toNat]'
                                                                    hpi_ar).toNat / 2 := by
                                                              rw [BitVec.toNat_ushiftRight,
                                                                Nat.shiftRight_eq_div_pow]
                                                            rw [hflk, m6_zext32_toNat, hsh1]
                                                            have := hset.1.1.core_ok.cur_vars_le
                                                            omega
                                                          c0_hsteps!
                                                          exact hJ65 _ ⟨_, by simp [hflk], hm⟩
                                                        · c0_hsteps!
                                                          exact hJ65 mk ⟨fl_k, hflk, hmk⟩)
                                                  · c0_hsteps!
                                                    exact hJ52 mk ⟨{ sc with core := { sc.core with
                                                      flags := fl_k } },
                                                      m6_fullDenseInvW_with_flags hset.1 hflk,
                                                      hcvp, halp, hflp, hset.2.1, hmk⟩
                                                · intro Lk hLk; c0_hsteps!
                                                  exact hLk sz_p.toNat (0#32, ()) m
                                                    ⟨sc.core.flags, hset.1.1.core_ok.flags_len,
                                                     Nat.zero_le _, by simp, hm⟩
                                              · refine wp_join0 (P := fun mj => ∃ sj : FullState,
                                                    FullDenseInvW c F0 F_cur sj ∧
                                                    sj.core.cur_vars = s0.core.cur_vars ∧
                                                    sj.core.arena_len = sl.core.arena_len ∧
                                                    sj.core.fuel = s0.core.fuel ∧
                                                    fullArenaClauseRefs sj =
                                                      fullArenaClauseRefs sp ∧
                                                    (FullMem c sj ⋆ R) mj)
                                                  (fun _ mj hmj => hJ52 mj hmj)
                                                  (fun J55p hJ55p => by
                                                    c0_hsplit
                                                    · have hsz2 : 2 ≤ sz_p.toNat := hc
                                                      have hp3_ar : (p + 3#64).toNat <
                                                          sc.core.arena.length := by
                                                        rw [hset.1.1.core_ok.arena_len_arr]
                                                        c0_bound
                                                      have hp4_ar : (p + 4#64).toNat <
                                                          sc.core.arena.length := by
                                                        rw [hset.1.1.core_ok.arena_len_arr]
                                                        c0_bound
                                                      c0_hsteps_nogrp
                                                      refine wp_join_state (ts := [])
                                                        (α := List (BitVec 32)) (fun _ => ())
                                                        (fun fl1 m1 => fl1.length = c.max_vars ∧
                                                          (FullMem c { sc with
                                                            core := { sc.core with
                                                              flags := fl1 } } ⋆ R) m1)
                                                        (fun _ fl1 m1 ⟨hfl1, hm1⟩ => by
                                                          c0_hsteps_nogrp
                                                          refine wp_join_state (ts := [])
                                                            (α := List (BitVec 32)) (fun _ => ())
                                                            (fun fl2 m2 => fl2.length = c.max_vars ∧
                                                              (FullMem c { sc with core :=
                                                                { sc.core with flags := fl2 } } ⋆ R)
                                                                m2)
                                                            (fun _ fl2 m2 ⟨hfl2, hm2⟩ => by
                                                              c0_hsteps!
                                                              let s_fl2 : FullState :=
                                                                { sc with core := { sc.core with
                                                                  flags := fl2 } }
                                                              have hdw_fl2 :
                                                                  FullDenseInvW c F0 F_cur s_fl2 :=
                                                                m6_fullDenseInvW_with_flags hset.1
                                                                  hfl2
                                                              exact hJ55p m2 ⟨s_fl2, hdw_fl2,
                                                                hcvp, halp, hflp, hset.2.1, hm2⟩)
                                                            (fun J68 hJ68 => by
                                                              c0_hsplit
                                                              · have hv1_lt :
                                                                    ((sc.core.arena[(p +
                                                                      4#64).toNat]'hp4_ar >>>
                                                                      (1 : Nat)).setWidth 64).toNat
                                                                      < fl1.length := by
                                                                  have hp4_mod : (p + 4#64).toNat =
                                                                      (p.toNat +
                                                                        BitVec.toNat 4#64) %
                                                                        2 ^ 64 := BitVec.toNat_add
                                                                          _ _
                                                                  have hsp_len :
                                                                      sp.core.arena.length =
                                                                        c.arena_cap := by
                                                                    have h0 :=
                                                                      hset.1.1.core_ok.arena_len_arr
                                                                    simpa [sc] using h0
                                                                  have hcv_mod : sl.core.cur_vars %
                                                                      2 ^ 64 = sl.core.cur_vars :=
                                                                    Nat.mod_eq_of_lt (by
                                                                      rw [hcvl]; have :=
                                                                        hset.1.1.core_ok.cur_vars_le
                                                                      omega)
                                                                  rw [hcv_mod] at hc
                                                                  have hne4 : p.toNat ≠
                                                                      (p.toNat +
                                                                        BitVec.toNat 4#64) %
                                                                        2 ^ 64 := by
                                                                    rw [← hp4_mod]; c0_bound
                                                                  have hset_ne1 :
                                                                      (sp.core.arena.set p.toNat
                                                                        (sp.core.arena[p.toNat]'(by
                                                                          rw [hsp_len]
                                                                          c0_bound) &&&
                                                                          ~~~(16777216 :
                                                                            BitVec 32)))[
                                                                          (p.toNat +
                                                                          BitVec.toNat 4#64) %
                                                                          2 ^ 64]'(by
                                                                            rw [List.length_set,
                                                                              hsp_len]
                                                                            c0_bound) =
                                                                        sp.core.arena[(p +
                                                                          4#64).toNat]'(by
                                                                            rw [hsp_len]
                                                                            c0_bound) :=
                                                                    (List.getElem_set_ne hne4
                                                                      _).trans (m6_getElem_congr
                                                                        hp4_mod.symm _ _)
                                                                  have hset_ne2 :
                                                                      sc.core.arena[(p +
                                                                        4#64).toNat]'hp4_ar =
                                                                        sp.core.arena[(p +
                                                                          4#64).toNat]'(by
                                                                            rw [hsp_len]
                                                                            c0_bound) :=
                                                                    by
                                                                    dsimp only [sc]
                                                                    exact List.getElem_set_ne
                                                                      (by c0_bound) _
                                                                  have hdiv_lt : (sc.core.arena[(p +
                                                                      4#64).toNat]'hp4_ar).toNat / 2
                                                                      < sl.core.cur_vars := by
                                                                    have hc' :
                                                                        ((sp.core.arena.set p.toNat
                                                                          (sp.core.arena[p.toNat]'(
                                                                            by rw [hsp_len]
                                                                               c0_bound)
                                                                            &&& ~~~(16777216 :
                                                                              BitVec 32)))[(p.toNat
                                                                              + BitVec.toNat 4#64) %
                                                                            2 ^ 64]'(by
                                                                              rw [List.length_set,
                                                                                hsp_len]
                                                                              c0_bound)).toNat / 2 <
                                                                          sl.core.cur_vars := hc
                                                                    rw [hset_ne1] at hc'
                                                                    rw [hset_ne2]; exact hc'
                                                                  have hsh1 : ((sc.core.arena[(p +
                                                                      4#64).toNat]'hp4_ar >>>
                                                                      (1 : Nat)) : BitVec 32).toNat
                                                                      = (sc.core.arena[(p +
                                                                        4#64).toNat]'hp4_ar).toNat /
                                                                        2 := by
                                                                    rw [BitVec.toNat_ushiftRight,
                                                                      Nat.shiftRight_eq_div_pow]
                                                                  rw [hfl1, m6_zext32_toNat, hsh1]
                                                                  have :=
                                                                    hset.1.1.core_ok.cur_vars_le
                                                                  omega
                                                                c0_hsteps!
                                                                exact hJ68 _ _ ⟨by simp [hfl1], hm⟩
                                                              · c0_hsteps!
                                                                exact hJ68 fl1 m1 ⟨hfl1, hm1⟩))
                                                        (fun J67 hJ67 => by
                                                          c0_hsplit
                                                          · have hv0_lt :
                                                                ((sc.core.arena[(p + 3#64).toNat]'
                                                                  hp3_ar >>> (1 : Nat)).setWidth
                                                                  64).toNat <
                                                                  sc.core.flags.length :=
                                                              by
                                                                have hp3_mod : (p + 3#64).toNat =
                                                                    (p.toNat + BitVec.toNat 3#64) %
                                                                      2 ^ 64 := BitVec.toNat_add _ _
                                                                have hsp_len :
                                                                    sp.core.arena.length =
                                                                      c.arena_cap := by
                                                                  have h0 :=
                                                                    hset.1.1.core_ok.arena_len_arr
                                                                  simpa [sc] using h0
                                                                have hcv_mod : sl.core.cur_vars %
                                                                    2 ^ 64 = sl.core.cur_vars :=
                                                                  Nat.mod_eq_of_lt (by
                                                                    rw [hcvl]; have :=
                                                                      hset.1.1.core_ok.cur_vars_le
                                                                    omega)
                                                                rw [hcv_mod] at hc
                                                                have hne3 : p.toNat ≠
                                                                    (p.toNat + BitVec.toNat 3#64) %
                                                                      2 ^ 64 := by
                                                                  rw [← hp3_mod]; c0_bound
                                                                have hset_ne1 :
                                                                    (sp.core.arena.set p.toNat
                                                                      (sp.core.arena[p.toNat]'(by
                                                                        rw [hsp_len]; c0_bound) &&&
                                                                        ~~~(16777216 : BitVec 32)))[
                                                                        (p.toNat +
                                                                        BitVec.toNat 3#64) %
                                                                        2 ^ 64]'(by
                                                                          rw [List.length_set,
                                                                            hsp_len]
                                                                          c0_bound) =
                                                                      sp.core.arena[(p +
                                                                        3#64).toNat]'(by
                                                                          rw [hsp_len]; c0_bound) :=
                                                                  (List.getElem_set_ne hne3 _).trans
                                                                    (m6_getElem_congr hp3_mod.symm _
                                                                      _)
                                                                have hset_ne2 :
                                                                    sc.core.arena[(p +
                                                                      3#64).toNat]'hp3_ar =
                                                                      sp.core.arena[(p +
                                                                        3#64).toNat]'(by
                                                                          rw [hsp_len]; c0_bound) :=
                                                                  by
                                                                  dsimp only [sc]
                                                                  exact List.getElem_set_ne
                                                                    (by c0_bound) _
                                                                have hdiv_lt : (sc.core.arena[(p +
                                                                    3#64).toNat]'hp3_ar).toNat / 2 <
                                                                    sl.core.cur_vars := by
                                                                  have hc' :
                                                                      ((sp.core.arena.set p.toNat
                                                                        (sp.core.arena[p.toNat]'(by
                                                                          rw [hsp_len]
                                                                          c0_bound) &&&
                                                                          ~~~(16777216 :
                                                                            BitVec 32)))[
                                                                          (p.toNat +
                                                                          BitVec.toNat 3#64) %
                                                                          2 ^ 64]'(by
                                                                            rw [List.length_set,
                                                                              hsp_len]
                                                                            c0_bound)).toNat / 2 <
                                                                        sl.core.cur_vars := hc
                                                                  rw [hset_ne1] at hc'
                                                                  rw [hset_ne2]; exact hc'
                                                                have hsh1 : ((sc.core.arena[(p +
                                                                    3#64).toNat]'hp3_ar >>>
                                                                    (1 : Nat)) : BitVec 32).toNat =
                                                                    (sc.core.arena[(p +
                                                                      3#64).toNat]'hp3_ar).toNat /
                                                                      2 := by
                                                                  rw [BitVec.toNat_ushiftRight,
                                                                    Nat.shiftRight_eq_div_pow]
                                                                rw [hset.1.1.core_ok.flags_len,
                                                                  m6_zext32_toNat, hsh1]
                                                                have := hset.1.1.core_ok.cur_vars_le
                                                                omega
                                                            c0_hsteps!
                                                            exact hJ67 _ _
                                                              ⟨by simp [hset.1.1.core_ok.flags_len],
                                                               hm⟩
                                                          · c0_hsteps!
                                                            exact hJ67 sc.core.flags m
                                                              ⟨hset.1.1.core_ok.flags_len, hm⟩)
                                                    · c0_hsteps!
                                                      exact hJ55p m ⟨sc, hset.1, hcvp, halp, hflp,
                                                        hset.2.1, hm⟩))
                                        · c0_hsteps!
                                          exact hJp mp ⟨sp, hdwp, hcvp, halp, hflp, rfl, hmp⟩)
                                  · c0_hsteps!; exact hJc sp mp ⟨hdwp, hcvp, hflp, hmp⟩
                                · intro Lp hLp; c0_hsteps!
                                  exact hLp sv1.core.arena_len (0#64, ()) mri
                                    ⟨sv1, Nat.zero_le _, by simp, by
                                      by_cases hz : sv1.core.arena_len = 0
                                      · exact Or.inl hz.symm
                                      · exact Or.inr (v5_zero_mem_arenaRefs3 hdw_v1.2.1.arena
                                          (Nat.pos_of_ne_zero hz)),
                                     hdw_v1, hcvl, rfl, hfll, hmri⟩
                            · intro Lri hLri; c0_hsteps!
                              exact hLri (ncand.toNat - i.toNat) (i, ()) mv
                                ⟨fl_v, hflv, hi_le, rfl, hmv⟩
                        · intro Lv hLv; c0_hsteps!
                          exact hLv sl.core.cur_vars (0#64, ()) ml
                            ⟨sl.core.flags, hdwl.1.core_ok.flags_len, Nat.zero_le _, by simp, hml⟩
                      · c0_hsteps!; exact hJc sl ml ⟨hdwl, hcvl, hfll, hml⟩
                    · c0_hsteps!; exact hJc sl ml ⟨hdwl, hcvl, hfll, hml⟩))
              (fun B hB => by
                c0_hsplit
                · have hi_lt : i.toNat < ncand.toNat := hc
                  c0_hsplit
                  · c0_hsplit
                    · c0_hsplit
                      · have hi_rr : i.toNat < sl.scratch.red_refs.length := by
                          rw [hdwl.1.scratch_ok.red_refs_len]; omega
                        have hcr_ref : (sl.scratch.red_refs[i.toNat]'hi_rr).toNat ∈
                            fullArenaClauseRefs sl := by
                          rw [hrefsl]
                          have h0 := hrr4_ok i.toNat hi_lt
                          rw [← hrrl, List.getElem?_eq_getElem hi_rr, Option.getD_some] at h0
                          exact h0
                        have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
                        c0_hsteps_nogrp
                        m7v5_call hCheckCl
                        refine ⟨c, F0, F_cur, sl, R, rfl, hdwl, hcr_ref, hml, ?_⟩
                        intro ok_c sc mc hdwc hcvc _ hflc hrefsc _ hrrc hfc hmc
                        c0_hsplit
                        · have hcr_ref_c : (sl.scratch.red_refs[i.toNat]'hi_rr).toNat ∈
                              fullArenaClauseRefs sc := hrefsc.symm ▸ hcr_ref
                          refine wp_join0 (P := fun mj => ∃ sj : FullState,
                              FullDenseInvW c F0 F_cur sj ∧
                              sj.core.cur_vars = s0.core.cur_vars ∧ sj.core.fuel = s0.core.fuel ∧
                              fullArenaClauseRefs sj = fullArenaClauseRefs s4 ∧
                              sj.scratch.red_refs = s4.scratch.red_refs ∧
                              (FullMem c sj ⋆ R) mj)
                            (fun _ mj ⟨sj, hdwj, hcvj, hflj, hrefsj, hrrj, hmj⟩ => by
                              c0_hsteps!
                              exact hL (ncand.toNat - (i + 1#64).toNat)
                                (i + 1#64, rem - 1#64, ()) mj (by omega)
                                ⟨sj, by omega, rfl, hdwj, hcvj, hflj, hrefsj, hrrj, hmj⟩)
                            (fun Jcon hJcon => by
                              c0_hsplit
                              · c0_hsplit
                                · have hcr_ar :
                                      ((sl.scratch.red_refs[i.toNat]'hi_rr).setWidth 64).toNat <
                                        sc.core.arena.length := by
                                    have hwf_c := hdwc.2.1.arena.refs_wf _ hcr_ref_c
                                    have := hdwc.1.core_ok.arena_len_le
                                    rw [hdwc.1.core_ok.arena_len_arr, m6_zext32_toNat]; omega
                                  c0_hsplit
                                  · c0_hsteps_nogrp
                                    m7v5_call hConnectSub
                                    refine fullFwdConnectSubsumerM6Spec_intro rfl hdwc hcr_ref_c
                                      hmc ?_
                                    intro s_con m_con hdw_con hcv_con har_con hal_con hfl_con _ _
                                      hrr_con hm_con
                                    have hrefs_con : fullArenaClauseRefs s_con =
                                        fullArenaClauseRefs sc := by
                                      unfold fullArenaClauseRefs fullArenaClauseRefsCore
                                      rw [har_con, hal_con]
                                    c0_hsteps!
                                    exact hJcon m_con ⟨s_con, hdw_con,
                                      hcv_con.trans (hcvc.trans hcvl),
                                      hfl_con.trans (hflc.trans hfll),
                                      hrefs_con.trans (hrefsc.trans hrefsl),
                                      hrr_con.trans (hrrc.trans hrrl), hm_con⟩
                                  · c0_hsteps!
                                    exact hJcon mc ⟨sc, hdwc, hcvc.trans hcvl, hflc.trans hfll,
                                      hrefsc.trans hrefsl, hrrc.trans hrrl, hmc⟩
                                · c0_hsteps!
                                  exact hJcon mc ⟨sc, hdwc, hcvc.trans hcvl, hflc.trans hfll,
                                    hrefsc.trans hrefsl, hrrc.trans hrrl, hmc⟩
                              · c0_hsteps!
                                exact hJcon mc ⟨sc, hdwc, hcvc.trans hcvl, hflc.trans hfll,
                                  hrefsc.trans hrefsl, hrrc.trans hrrl, hmc⟩)
                        · c0_hsteps!
                          exact hQ 20#64 sc mc hdwc.toDense (hcvc.trans hcvl) (hflc.trans hfll)
                            (Or.inr rfl) (fun _ => hfc (by simpa using hc)) hmc
                      · c0_hsteps!; exact hB ml rfl
                    · c0_hsteps!; exact hB ml rfl
                  · c0_hsteps!; exact hB ml rfl
                · c0_hsteps!; exact hB ml rfl)
          · intro L hL; c0_hsteps!
            exact hL ncand.toNat (0#64, budget, ()) m4
              ⟨s4, Nat.zero_le _, by simp, hdw4,
               hcv4.trans (hcv3.trans (hcv2.trans hcv1)),
               hfl4.trans (hfl3.trans (hfl2.trans hfl1)), rfl, rfl, hm4⟩
      · c0_hsteps!
        exact hQ 20#64 s2 m2 hdw2.toDense (hcv2.trans hcv1) (hfl2.trans hfl1) (Or.inr rfl)
          (fun _ => hf2 (by simpa using hc)) hm2
    · c0_hsteps!
      exact hQ 20#64 s1 m1 hdw1.toDense hcv1 hfl1 (Or.inr rfl)
        (fun _ => hf1 (by simpa using hc)) hm1

end ForwardSubProof

/-! ## 4. `full_eliminate_m7v5` (`FullFastSched.schedEliminateSpec`) -/

section EliminateProof

private theorem v5_denseInv_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {scr' : FullScratch}
    (hok : scr'.LengthsOk c) (hll : scr'.last_learned = s.scratch.last_learned)
    (hel : scr'.extend_len = s.scratch.extend_len) :
    FullDenseInv c F0 { s with scratch := scr' } :=
  fullDenseInv_with_scratch_keep h hok hll hel

private theorem v5_sparseInv_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {scr' : FullScratch}
    (hok : scr'.LengthsOk c) (hll : scr'.last_learned = s.scratch.last_learned)
    (hel : scr'.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 { s with scratch := scr' } :=
  fullSparseInv_with_scratch_keep h hok hll hel

private theorem v5_tmkZero_of_init {s : FullState} {tmki : List (BitVec 32)}
    (hinit : ∀ k < s.core.cur_vars, tmki[k]?.getD 0#32 = 0#32) :
    TmkZero { s with scratch := { s.scratch with tarjan_mark := tmki } } :=
  fun v hv => hinit v hv

/-- Parametric `Func.wp` proof for `full_eliminate_m7v5`, certifying canonical
`FullFastSched.schedEliminateSpec`. -/
theorem full_eliminate_m7v5_wp (Γ : Env)
    (hDticks : ∀ a m Q X, schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X → Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFwd : ∀ a m Q X, fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub_m7v5" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, m3ElimBveSpec a m Q X →
      Γ "full_elim_bve_m7" [i64, i64] [i64] a m Q X)
    (hFact : ∀ a m Q X, fullFactorHeapSpec a m Q X → Γ "full_factor" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, schedEliminateSpec a m Q X →
      Func.wp Γ full_eliminate_m7v5_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hinv0, hcl0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  unfold Func.wp full_eliminate_m7v5_body
  c0_hsteps_nogrp
  m7v5_call hDticks
  refine ⟨c, s0, R, rfl, hinv0.lengths, hm0, ?_⟩
  intro dticks
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ s1 m1 ⟨hinv1, _, hfu1, hm1⟩ => by
      c0_hsteps_nogrp
      m7v5_call hEnter
      refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
      intro ok s2 m2 hcl2 hfu2 hok_d hfail_s hm2
      c0_hsplit
      · have hden2 : FullDenseInv c F0 s2 := hok_d hc
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun b => (b, ())) (fun _ => True)
          (fun _ _ _ => by
            c0_hsteps_nogrp
            m7v5_call hMin; intro fbud _
            c0_hsteps_nogrp
            m7v5_call hFwd
            refine ⟨c, F0, s2, R, rfl, hden2, hm2, ?_⟩
            intro fs s3 m3 hden3 hcv3 hfu3 _ huf3 hm3
            have hcv2_le := hden2.lengths.core_ok.cur_vars_le
            let s3r : FullState :=
              { s3 with scratch := { s3.scratch with fwd_sub_cnt := s2.scratch.fwd_sub_cnt } }
            have hden3r : FullDenseInv c F0 s3r :=
              v5_denseInv_with_scratch_keep hden3
                { hden3.lengths.scratch_ok with
                  walk_vals_len := hden3.lengths.scratch_ok.walk_vals_len } rfl rfl
            have hfu3r : s3r.core.fuel.toNat ≤ s0.core.fuel.toNat := by
              change s3.core.fuel.toNat ≤ s0.core.fuel.toNat; rw [hfu3]; omega
            c0_hsplit
            · c0_hsteps_nogrp
              m7v5_call hReb
              refine ⟨c, F0, s3r, R, rfl, hden3r, hm, ?_⟩
              intro _ s4 m4 hsp4 hcl4 hfu4 _ _ hm4
              c0_hsteps!
              exact hQ 20#64 s4 m4 hsp4 hcl4 (by omega) (Or.inr rfl) (fun _ => huf3 hc) hm4
            · let cv3 := s3r.core.cur_vars
              have hcv3_le : cv3 ≤ c.max_vars := hden3r.lengths.core_ok.cur_vars_le
              have htl3 := hden3r.lengths.scratch_ok.tarjan_mark_len
              c0_hsteps_nogrp
              refine wp_loop_group (ts := [i64])
                (fun rem_t (ti, ()) mt => ∃ tmki : List (BitVec 32),
                  tmki.length = 2 * c.max_vars ∧ ti.toNat ≤ cv3 ∧ rem_t = cv3 - ti.toNat ∧
                  (∀ k < ti.toNat, tmki[k]?.getD 0#32 = 0#32) ∧
                  (FullMem c { s3r with scratch := { s3r.scratch with tarjan_mark := tmki } } ⋆
                    R) mt)
                ?_ ?_
              · rintro Lt rem_t ⟨ti, ⟨⟩⟩ mt hLt ⟨tmki, htli, hti_le, rfl, hinit, hmt⟩
                c0_hsplit
                · have hti_lt : ti.toNat < cv3 := by
                    rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                  have hti_b : ti.toNat < tmki.length := by omega
                  have hti1 : (ti + 1#64).toNat = ti.toNat + 1 := by c0_bound
                  c0_hsteps!
                  exact hLt (cv3 - (ti + 1#64).toNat) (ti + 1#64, ()) _ (by omega)
                    ⟨tmki.set ti.toNat 0#32, by simp [htli], by omega, rfl, fun k hk => by
                       rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hti1 ▸ hk)) with h | h
                       · rw [List.getElem?_set_ne (by omega)]; exact hinit k h
                       · subst h; rw [List.getElem?_set_self hti_b, Option.getD_some], hm⟩
                · have hti_eq : ti.toNat = cv3 := by
                    rw [Nat.mod_eq_of_lt (by omega)] at hc
                    change ¬ti.toNat < cv3 at hc
                    omega
                  rw [hti_eq] at hinit
                  let s3t : FullState :=
                    { s3r with scratch := { s3r.scratch with tarjan_mark := tmki } }
                  have hden3t : FullDenseInv c F0 s3t :=
                    v5_denseInv_with_scratch_keep hden3r
                      { hden3r.lengths.scratch_ok with tarjan_mark_len := htli } rfl rfl
                  have htmk3t : TmkZero s3t := v5_tmkZero_of_init hinit
                  c0_hsteps_nogrp
                  refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                    (fun b => (b, ())) (fun _ => True)
                    (fun _ bve_lim _ => by
                      c0_hsteps_nogrp
                      m7v5_call hBve
                      refine ⟨c, F0, s3t, R, rfl, hden3t, htmk3t, hmt, ?_⟩
                      intro res s4 m4 hden4 _ hfu4 _ hres_u hm4
                      have hfu4' : s4.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                        dsimp only [s3t, s3r] at hfu4
                        have hfu3' : s3.core.fuel.toNat ≤ s0.core.fuel.toNat := hfu3r
                        omega
                      c0_hsteps_nogrp
                      refine wp_join_state0 (α := FullState)
                        (fun sf mf => FullDenseInv c F0 sf ∧
                          sf.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sf ⋆ R) mf)
                        (fun _ sf mf ⟨hdenf, hfuf, hmf⟩ => by
                          c0_hsteps_nogrp
                          m7v5_call hReb
                          refine ⟨c, F0, sf, R, rfl, hdenf, hmf, ?_⟩
                          intro rr se me hspe hcle hfue _ hue hme
                          let se' : FullState :=
                            { se with scratch :=
                              { se.scratch with fwd_str_cnt := se.scratch.search_ticks } }
                          have hspe' : FullSparseInv c F0 se' :=
                            v5_sparseInv_with_scratch_keep hspe
                              { hspe.lengths.scratch_ok with
                                walk_vals_len := hspe.lengths.scratch_ok.walk_vals_len } rfl rfl
                          have hfue' : se'.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                            change se.core.fuel.toNat ≤ s0.core.fuel.toNat; omega
                          c0_hsteps!
                          · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                              (fun _ => hres_u hc) hm
                          · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                              (fun _ => hue hc) hm
                          · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                              (fun _ => hspe'.inconsistent_unsat hc) hm
                          · exact hQ 1#64 se' _ hspe' hcle hfue' (Or.inl rfl)
                              (fun h => by cases h) hm)
                        (fun Jf hJf => by
                          c0_hsplit
                          · c0_hsteps_nogrp
                            refine wp_join_state0 (α := FullState)
                              (fun sg mg => FullDenseInv c F0 sg ∧
                                sg.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sg ⋆ R) mg)
                              (fun _ sg mg ⟨hdeng, hfug, hmg⟩ => by
                                c0_hsteps_nogrp
                                refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                                  (fun b => (b, ())) (fun _ => True)
                                  (fun _ _ _ => by
                                    c0_hsteps_nogrp
                                    m7v5_call hMin; intro fact_bud _
                                    c0_hsteps_nogrp
                                    let sg0 : FullState :=
                                      { sg with scratch := { sg.scratch with elim_bound := 0#64 } }
                                    have hdeng0 : FullDenseInv c F0 sg0 :=
                                      v5_denseInv_with_scratch_keep hdeng
                                        { hdeng.lengths.scratch_ok with
                                          walk_vals_len := hdeng.lengths.scratch_ok.walk_vals_len }
                                        rfl rfl
                                    m7v5_call hFact
                                    refine ⟨c, F0, sg0, R, rfl, hdeng0, hm, ?_⟩
                                    intro _ sf0 mf0 hdenf0 _ hfuf0 _ hmf0
                                    c0_hsteps!
                                    let sf1 : FullState :=
                                      { sf0 with scratch :=
                                        { sf0.scratch with elim_bound := sg.scratch.elim_bound } }
                                    have hdenf1 : FullDenseInv c F0 sf1 :=
                                      v5_denseInv_with_scratch_keep hdenf0
                                        { hdenf0.lengths.scratch_ok with
                                          walk_vals_len :=
                                            hdenf0.lengths.scratch_ok.walk_vals_len }
                                        rfl rfl
                                    exact hJf sf1 _ ⟨hdenf1, by
                                      change sf0.core.fuel.toNat ≤ s0.core.fuel.toNat
                                      rw [hfuf0]; exact hfug, hm⟩)
                                  (fun Jfb hJfb => by
                                    c0_hsplit <;> (c0_hsteps!; exact hJfb _ trivial)))
                              (fun Jdo hJdo => by
                                c0_hsteps!
                                · exact hJdo s4 m4 ⟨hden4, hfu4', hm4⟩
                                · exact hJdo s4 m4 ⟨hden4, hfu4', hm4⟩
                                · exact hJf s4 m4 ⟨hden4, hfu4', hm4⟩)
                          · c0_hsteps!; exact hJf s4 m4 ⟨hden4, hfu4', hm4⟩))
                    (fun Jb hJb => by
                      c0_hsplit
                      · c0_hsteps!; exact hJb _ trivial
                      · c0_hsteps_nogrp; m7v5_call hMin; intro b _; c0_hsteps!; exact hJb b trivial)
              · intro Lt hLt; c0_hsteps!
                exact hLt cv3 (0#64, ()) _
                  ⟨s3r.scratch.tarjan_mark, htl3, Nat.zero_le _, by simp,
                   fun _ h => by simp at h, hm⟩)
          (fun Jfb hJfb => by c0_hsplit <;> (c0_hsteps!; exact hJfb _ trivial))
      · have hsp2 : FullSparseInv c F0 s2 := hfail_s hc
        let s2' : FullState :=
          { s2 with scratch := { s2.scratch with fwd_str_cnt := s2.scratch.search_ticks } }
        have hsp2' : FullSparseInv c F0 s2' :=
          v5_sparseInv_with_scratch_keep hsp2
            { hsp2.lengths.scratch_ok with
              walk_vals_len := hsp2.lengths.scratch_ok.walk_vals_len } rfl rfl
        have hfu2' : s2'.core.fuel.toNat ≤ s0.core.fuel.toNat := by
          change s2.core.fuel.toNat ≤ s0.core.fuel.toNat; omega
        c0_hsteps!
        · exact hQ 20#64 s2' _ hsp2' hcl2 hfu2' (Or.inr rfl)
            (fun _ => hsp2'.inconsistent_unsat hc) hm
        · exact hQ 1#64 s2' _ hsp2' hcl2 hfu2' (Or.inl rfl) (fun h => by cases h) hm)
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps!; exact hJ1 s0 m0 ⟨hinv0, hcl0, Nat.le_refl _, hm0⟩
      · c0_hsteps_nogrp
        let s0a : FullState :=
          { s0 with scratch := { s0.scratch with eliminations := s0.scratch.eliminations + 1#64 } }
        have hlen0a : s0a.LengthsOk c :=
          ⟨hinv0.lengths.core_ok,
           { hinv0.lengths.scratch_ok with
             walk_vals_len := hinv0.lengths.scratch_ok.walk_vals_len }⟩
        m7v5_call hIlog; intro loge0 _ _
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun b => (b, ())) (fun _ => True)
          (fun _ loge _ => by
            c0_hsteps_nogrp
            m7v5_call hScale; refine ⟨c, s0a, R, rfl, hlen0a, hm, ?_⟩
            intro delta
            c0_hsteps!
            let s0b : FullState :=
              { s0a with
                scratch := { s0a.scratch with elim_limit := s0a.scratch.conflicts + delta } }
            have hinv0b : FullSparseInv c F0 s0b :=
              v5_sparseInv_with_scratch_keep hinv0
                { hinv0.lengths.scratch_ok with
                  walk_vals_len := hinv0.lengths.scratch_ok.walk_vals_len } rfl rfl
            exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩)
          (fun Jl hJl => by c0_hsplit <;> (c0_hsteps!; exact hJl _ trivial)))

end EliminateProof

/-! ## 5. Closed `32`-Row `m7BvaV5FixSpecTable`, `m7BvaV5FixEnv`, `ModuleOk`, & `Fn` Bridges -/

section ModuleOkSection

/-- Closed `32`-row specification table for `m7BvaV5FixModule` (`4` M7 fixes + `28` externs). -/
def m7BvaV5FixSpecTable : List SpecEntry :=
  [ ⟨"full_calc_max_v_m7v5", [i64, i64, i64, i64], [i64], Full.fullCalcMaxVSpec, true⟩
  , ⟨"full_probe_m7v5", [i64, .bool], [i64], m6ProbeSpec, true⟩
  , ⟨"full_forward_sub_m7v5", [i64, i64], [i64], fullForwardSubFastSpec, true⟩
  , ⟨"full_eliminate_m7v5", [i64, .bool], [i64], schedEliminateSpec, true⟩
  , ⟨"full_fixed_bytes", [i64], [i64], Full.fullFixedBytesSpec, true⟩
  , ⟨"full_probe_dticks_m6_hdr", [i64, .bool], [i64], m6HdrW2aSpec [.bool] [i64], true⟩
  , ⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩
  , ⟨"full_scale_delta_m5", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], schedEnterDenseSpec, true⟩
  , ⟨"m6_hdr_delaying", [i64, i64], [.bool], m6HdrW2aSpec [i64] [.bool], true⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64], m3CongruenceDenseSpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], Full.fullRebuildWatchesSpec, true⟩
  , ⟨"m6_hdr_set_watermark", [i64, i64, i64], [], m6HdrW2aSpec [i64, i64] [], true⟩
  , ⟨"m6_hdr_reduce_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_bump_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"full_sweep_dense_m6", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec, true⟩
  , ⟨"full_substitute", [i64], [i64], Full.fullSubstituteSpec, true⟩
  , ⟨"full_probe_tail_m6", [i64, i64], [i64], m6ProbeTailSpec, true⟩
  , ⟨"full_backbone_m6", [i64, i64], [i64], FullM3Backbone.fullBackboneSpec, true⟩
  , ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
  , ⟨"full_factor", [i64, i64], [i64], fullFactorHeapSpec, true⟩
  , ⟨"full_fwd_dedup_bins", [i64], [.bool], Full.fullFwdDedupBinsSpec, true⟩
  , ⟨"full_dense_flush_units_m7", [i64], [.bool], fullDenseFlushUnitsM6Spec, true⟩
  , ⟨"full_fwd_collect_sort_m7", [i64], [i64], fullFwdCollectSortM6Spec, true⟩
  , ⟨"full_fwd_flush_large_m7", [i64], [], fullFwdFlushLargeM6Spec, true⟩
  , ⟨"full_fwd_check_cl_m7", [i64, i32], [.bool], m7v5FwdCheckClSpec, true⟩
  , ⟨"full_fwd_connect_subsumer_m7", [i64, i32], [], fullFwdConnectSubsumerM6Spec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩
  , ⟨"full_fwd_reconnect_irred_m7", [i64], [], fullFwdReconnectIrredM6Spec, true⟩
  , ⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩
  , ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  , ⟨"full_elim_bve_m7", [i64, i64], [i64], m3ElimBveSpec, true⟩ ]

theorem m7BvaV5FixSpecTable_length : m7BvaV5FixSpecTable.length = 32 := by t_kernel_rfl

theorem m7BvaV5FixSpecTable_nodup : (m7BvaV5FixSpecTable.map SpecEntry.name).Nodup := by decide

theorem m7BvaV5FixSpecTable_noExit : ∀ e ∈ m7BvaV5FixSpecTable, e.noExit = true := by
  intro e he
  simp only [m7BvaV5FixSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Closed environment induced by `m7BvaV5FixSpecTable`. -/
def m7BvaV5FixEnv : Env := Env.ofTable m7BvaV5FixSpecTable

theorem m7BvaV5FixEnv_noExit : ∀ f as bs xs m Q X X',
    m7BvaV5FixEnv f as bs xs m Q X → m7BvaV5FixEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m7BvaV5FixSpecTable_noExit

private theorem m7v5Env_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7BvaV5FixSpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → m7BvaV5FixEnv nm as bs xs m Q X := fun xs m Q X hs =>
  Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) hmem m7BvaV5FixSpecTable_nodup (hno xs m Q X hs)

private theorem m7v5_calc_max_v_env_wp : ∀ a m Q X, Full.fullCalcMaxVSpec a m Q X →
    Func.wp m7BvaV5FixEnv full_calc_max_v_m7v5_body a m Q X :=
  full_calc_max_v_m7v5_wp m7BvaV5FixEnv
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fun _ _ _ _ h => h)

private theorem m7v5_probe_env_wp : ∀ a m Q X, m6ProbeSpec a m Q X →
    Func.wp m7BvaV5FixEnv full_probe_m7v5_body a m Q X := by
  refine full_probe_m7v5_wp m7BvaV5FixEnv
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fun _ _ _ _ h => h)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fun _ _ _ _ h => h)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fun _ _ _ _ h => h)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fun _ _ _ _ h => h)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fun _ _ _ _ h => h)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fun _ _ _ _ h => h)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fun _ _ _ _ h => h)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fun _ _ _ _ h => m6ProbeTailSpec_monoX h)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fun _ _ _ _ h => h)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fun _ _ _ _ h => h)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fun _ _ _ _ h => h)

private theorem m7v5_forward_sub_env_wp : ∀ a m Q X, fullForwardSubFastSpec a m Q X →
    Func.wp m7BvaV5FixEnv full_forward_sub_m7v5_body a m Q X := by
  refine full_forward_sub_m7v5_wp m7BvaV5FixEnv
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fun _ _ _ _ h => h)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fullDenseFlushUnitsM6Spec_noExit)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fullFwdCollectSortM6Spec_noExit)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fullFwdFlushLargeM6Spec_noExit)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) m7v5FwdCheckClSpec_noExit)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fullFwdConnectSubsumerM6Spec_noExit)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fun _ _ _ _ h => h)
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fullFwdReconnectIrredM6Spec_noExit)

private theorem m7v5_eliminate_env_wp : ∀ a m Q X, schedEliminateSpec a m Q X →
    Func.wp m7BvaV5FixEnv full_eliminate_m7v5_body a m Q X := by
  refine full_eliminate_m7v5_wp m7BvaV5FixEnv ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fun _ _ _ _ h => h

theorem m7v5_calc_max_v_impl : SpecEntry.Impl m7BvaV5FixEnv
    ⟨"full_calc_max_v_m7v5", [i64, i64, i64, i64], [i64], full_calc_max_v_m7v5_body⟩
    ⟨"full_calc_max_v_m7v5", [i64, i64, i64, i64], [i64], Full.fullCalcMaxVSpec, true⟩ :=
  SpecEntry.Impl.of m7v5_calc_max_v_env_wp

theorem m7v5_probe_impl : SpecEntry.Impl m7BvaV5FixEnv
    ⟨"full_probe_m7v5", [i64, .bool], [i64], full_probe_m7v5_body⟩
    ⟨"full_probe_m7v5", [i64, .bool], [i64], m6ProbeSpec, true⟩ :=
  SpecEntry.Impl.of m7v5_probe_env_wp

theorem m7v5_forward_sub_impl : SpecEntry.Impl m7BvaV5FixEnv
    ⟨"full_forward_sub_m7v5", [i64, i64], [i64], full_forward_sub_m7v5_body⟩
    ⟨"full_forward_sub_m7v5", [i64, i64], [i64], fullForwardSubFastSpec, true⟩ :=
  SpecEntry.Impl.of m7v5_forward_sub_env_wp

theorem m7v5_eliminate_impl : SpecEntry.Impl m7BvaV5FixEnv
    ⟨"full_eliminate_m7v5", [i64, .bool], [i64], full_eliminate_m7v5_body⟩
    ⟨"full_eliminate_m7v5", [i64, .bool], [i64], schedEliminateSpec, true⟩ :=
  SpecEntry.Impl.of m7v5_eliminate_env_wp

theorem m7v5CalcMaxVFn_impl : SpecEntry.Impl m7BvaV5FixEnv m7v5CalcMaxVFn
    ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], Full.fullCalcMaxVSpec, true⟩ :=
  SpecEntry.Impl.of m7v5_calc_max_v_env_wp

theorem m7v5ProbeFn_impl : SpecEntry.Impl m7BvaV5FixEnv m7v5ProbeFn
    ⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩ :=
  SpecEntry.Impl.of m7v5_probe_env_wp

theorem m7v5ForwardSubFn_impl : SpecEntry.Impl m7BvaV5FixEnv m7v5ForwardSubFn
    ⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩ :=
  SpecEntry.Impl.of m7v5_forward_sub_env_wp

theorem m7v5EliminateFn_impl : SpecEntry.Impl m7BvaV5FixEnv m7v5EliminateFn
    ⟨"full_eliminate_m6", [i64, .bool], [i64], schedEliminateSpec, true⟩ :=
  SpecEntry.Impl.of m7v5_eliminate_env_wp

theorem m7BvaV5Fix_allFns_wf : AllFns Fn.Wf m7BvaV5FixModule.fns :=
  ⟨full_calc_max_v_m7v5_wf, full_probe_m7v5_wf,
   full_forward_sub_m7v5_wf, full_eliminate_m7v5_wf, trivial⟩

theorem m7BvaV5Fix_tableImpl :
    TableImpl m7BvaV5FixEnv m7BvaV5FixModule.fns m7BvaV5FixSpecTable :=
  ⟨m7v5_calc_max_v_impl, m7v5_probe_impl, m7v5_forward_sub_impl, m7v5_eliminate_impl, trivial⟩

/-- Closed `ModuleOk` certifying `m7BvaV5FixModule` under `m7BvaV5FixEnv` (`0` exits). -/
theorem m7BvaV5Fix_moduleOk : ModuleOk m7BvaV5FixEnv m7BvaV5FixModule :=
  Env.ofTable_moduleOk m7BvaV5Fix_acyclic m7BvaV5Fix_allFns_wf m7BvaV5Fix_tableImpl

end ModuleOkSection

/-! ## 6. Concrete `Mem 64` Non-Bailout UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

section ConcreteUnsatNv

/-- Concrete `full_calc_max_v_m7v5` non-vacuity (`XPost := False`): with `32 MiB` budget and
`mv = 2`, `bva_cap` reaches `4096` (`r = 4098#64 > 19#64` old `(mv >> 1) + 16 + mv`). -/
theorem nv_m7v5_calc_max_v :
    Func.wp m7BvaV5FixEnv full_calc_max_v_m7v5_body
      (33554432#64, 2#64, 1#64, BitVec.ofNat 64 (fullFixedBytes 2), ())
      (∅ : Mem 64)
      (fun (r, ()) m' => r = 4098#64 ∧ m' = (∅ : Mem 64))
      (fun _ _ _ _ => False) := by
  refine full_calc_max_v_m7v5_exact_wp m7BvaV5FixEnv
    (m7v5Env_row (by simp [m7BvaV5FixSpecTable]) fun _ _ _ _ h => h) _ _ _ _
    ⟨by unfold dimacsBound; decide, by unfold dimacsBound; decide,
     by unfold fullFixedBytes valsBytes markBytes u32FullBytes fullMinDepthOf; decide,
     by unfold fullFixedBytes valsBytes markBytes u32FullBytes fullMinDepthOf; decide,
     ⟨by unfold fullCalcMaxVV5 fullBvaCapV5 fullFixedBytes valsBytes markBytes
           u32FullBytes fullMinDepthOf; decide, rfl⟩⟩

/-- Concrete `100060`-byte `Mem 64` UNSAT non-vacuity (`XPost := False`) for
`full_forward_sub_m7v5` on `FullM4Sweep.nvM4SweepMem`. -/
theorem nv_m7v5_forward_sub :
    Func.wp m7BvaV5FixEnv full_forward_sub_m7v5_body
      (FullM4Sweep.nvM4SweepCfg.hdr, 10#64, ()) FullM4Sweep.nvM4SweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv FullM4Sweep.nvM4SweepCfg nvOneLitF0 s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg FullM4Sweep.nvM4SweepState ⋆ emp)
      FullM4Sweep.nvM4SweepMem := by
    rw [sep_emp]; exact FullM4Sweep.nvM4SweepMem_ok
  exact m7v5_forward_sub_impl.2 _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, nvOneLitF0, FullM4Sweep.nvM4SweepState, emp, rfl,
     FullM4Sweep.nvM4Sweep_invW.toDense, hm, fun _ s' _ hd _ _ hdom _ hm' => by
       rw [sep_emp] at hm'; exact ⟨s', hd, hdom, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩⟩

/-- Concrete `100060`-byte `Mem 64` UNSAT non-vacuity (`XPost := False`) for
`full_eliminate_m7v5` on `FullM4Sweep.nvM4SweepSparseMem`. -/
theorem nv_m7v5_eliminate :
    Func.wp m7BvaV5FixEnv full_eliminate_m7v5_body
      (FullM4Sweep.nvM4SweepCfg.hdr, true, ()) FullM4Sweep.nvM4SweepSparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv FullM4Sweep.nvM4SweepCfg nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem FullM4Sweep.nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullM4Sweep.nvM4SweepCfg FullM4Sweep.nvM4SweepSparseState ⋆ emp)
      FullM4Sweep.nvM4SweepSparseMem := by
    rw [sep_emp]; exact FullM4Sweep.nvM4SweepSparseMem_ok
  exact m7v5_eliminate_impl.2 _ _ _ _
    ⟨FullM4Sweep.nvM4SweepCfg, nvOneLitF0, FullM4Sweep.nvM4SweepSparseState, emp, rfl,
     FullM4Sweep.nvM4SweepSparse_inv, rfl, hm, fun _ s' _ hsp hlvl _ hdom _ hm' => by
       rw [sep_emp] at hm'; exact ⟨s', hsp, hlvl, hdom, FullM4Sweep.nvM4SweepF0_unsat, hm'⟩⟩

end ConcreteUnsatNv

end LeanQbe.T.Examples.Kissat.FullM7BvaV5Fix
