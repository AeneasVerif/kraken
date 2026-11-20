module

public import LeanQbe.T.Examples.Kissat.FullParseInitLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Sizing, Header Setup, Zeroing & State Init Proofs (Part 2, `Stage 4`)

Proves parametric `(Γ : Env)` `Func.wp` theorems for:
1. Pure sizing & layout: `full_fixed_bytes`, `full_calc_max_v`, `full_calc_ext_cap`,
   `full_calc_scr_cap`
2. Header initialization: `full_init_ptrs`, `full_init_hdr`, `full_init_arenas`
3. Array zeroing & state construction: `full_zero_tables1`, `full_zero_tables2`, `full_init_state`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
  LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open FullParseInitSpecs FullParseInitHelpers
open scoped FullArenaTactics FullParseInitTactics

/-! ## 1. Arithmetic helpers for `Full1.lean` sizing & header setup -/

private theorem bv64_shr1_eq (x : BitVec 64) : x >>> (1 : Nat) = x >>> 1#64 := rfl
private theorem bv64_shl28_val :
    (1 : BitVec 64) <<< (((28 : BitVec 32).signExtend 64).toNat % 64) = (1#64 <<< 28) := rfl
private theorem bv64_shl24_val :
    (1 : BitVec 64) <<< (((24 : BitVec 32).signExtend 64).toNat % 64) = (1#64 <<< 24) := rfl

private theorem bv64_shl_sext1_nat (x : BitVec 64) :
    x <<< (((1 : BitVec 32).signExtend 64).toNat % 64) = x <<< (1 : Nat) := rfl

private theorem bv64_shl_sext3_eq {n : Nat} :
    BitVec.ofNat 64 n <<< (((3 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (8 * n) := fp_shl_sext3

private theorem bv64_shl_sext6_eq {n : Nat} :
    BitVec.ofNat 64 n <<< (((6 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (64 * n) := fp_shl_sext6

private theorem bv64_ule_nat {a b : BitVec 64} :
    a.ule b = decide (a.toNat ≤ b.toNat) := by
  simp [BitVec.ule]

private theorem bv64_ult_nat {a b : BitVec 64} :
    a.ult b = decide (a.toNat < b.toNat) := by
  simp [BitVec.ult]

private theorem bv64_mul_nat (x : BitVec 64) (k : Nat) :
    x * BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat * k) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_mod]

private theorem full_fixed_bv_ofNat {mx : Nat} (hmx : mx < 2 * dimacsBound) :
    (1152 : BitVec 64) + (320 : BitVec 64) +
      (((BitVec.ofNat 64 mx <<< (((1 : BitVec 32).signExtend 64).toNat % 64) + 7) &&& ~~~7) *
        (3 : BitVec 64)) +
      (((BitVec.ofNat 64 mx + 7) &&& ~~~7) * (5 : BitVec 64)) +
      ((((BitVec.ofNat 64 mx + 1) <<< (((2 : BitVec 32).signExtend 64).toNat % 64) + 7) &&& ~~~7) *
        (15 : BitVec 64)) +
      ((BitVec.ofNat 64 mx <<< (((1 : BitVec 32).signExtend 64).toNat % 64)) <<<
        (((3 : BitVec 32).signExtend 64).toNat % 64)) +
      (BitVec.ofNat 64 mx <<< (((6 : BitVec 32).signExtend 64).toNat % 64)) +
      (BitVec.ofNat 64 (fullMinDepthOf mx) <<< (((3 : BitVec 32).signExtend 64).toNat % 64)) =
      BitVec.ofNat 64 (fullFixedBytes mx) := by
  have hmx' := hmx; unfold dimacsBound at hmx'
  have hmd := fullMinDepthOf_le mx
  rw [fp_vb_eq hmx, fp_mb_eq hmx, fp_ub_eq hmx, Kissat.bv_shl_sext1, fp_shl_sext3,
    fp_shl_sext3, fp_shl_sext6,
    show (3 : BitVec 64) = BitVec.ofNat 64 3 from rfl,
    show (5 : BitVec 64) = BitVec.ofNat 64 5 from rfl,
    show (15 : BitVec 64) = BitVec.ofNat 64 15 from rfl,
    fp_mul_nat, fp_mul_nat, fp_mul_nat,
    show (1152 : BitVec 64) + (320 : BitVec 64) = BitVec.ofNat 64 1472 from rfl]
  repeat rw [bv_add_ofNat]
  unfold fullFixedBytes
  congr 1
  omega

private theorem fp_shr1_bv (x : BitVec 64) :
    x >>> (((1 : BitVec 32).signExtend 64).toNat % 64) = BitVec.ofNat 64 (x.toNat / 2) := by
  have h := fp_shr_sext1 x.isLt; rwa [bv_ofNat_toNat_eq x] at h

private theorem fp_shr3_bv (x : BitVec 64) :
    x >>> (((3 : BitVec 32).signExtend 64).toNat % 64) = BitVec.ofNat 64 (x.toNat / 8) := by
  have h := fp_shr_sext3 x.isLt; rwa [bv_ofNat_toNat_eq x] at h

private theorem fp_shr4_bv (x : BitVec 64) :
    x >>> (((4 : BitVec 32).signExtend 64).toNat % 64) = BitVec.ofNat 64 (x.toNat / 16) := by
  have h := fp_shr_sext4 x.isLt; rwa [bv_ofNat_toNat_eq x] at h

private theorem fp_shr5_bv (x : BitVec 64) :
    x >>> (((5 : BitVec 32).signExtend 64).toNat % 64) = BitVec.ofNat 64 (x.toNat / 32) := by
  have h := fp_shr_sext5 x.isLt; rwa [bv_ofNat_toNat_eq x] at h

private theorem fp_shl1_bv (x : BitVec 64) :
    x <<< (((1 : BitVec 32).signExtend 64).toNat % 64) = BitVec.ofNat 64 (2 * x.toNat) := by
  have h := Kissat.bv_shl_sext1 (n := x.toNat); rwa [bv_ofNat_toNat_eq x] at h

private theorem fp_shl3_bv (x : BitVec 64) :
    x <<< (((3 : BitVec 32).signExtend 64).toNat % 64) = BitVec.ofNat 64 (8 * x.toNat) := by
  have h := fp_shl_sext3 (n := x.toNat); rwa [bv_ofNat_toNat_eq x] at h

private theorem fp_vb_bv {mx : BitVec 64} (hmx : mx.toNat < 2 * dimacsBound) :
    (mx <<< (((1 : BitVec 32).signExtend 64).toNat % 64) + 7) &&& ~~~7 =
      BitVec.ofNat 64 (valsBytes mx.toNat) := by
  have h := fp_vb_eq hmx; rwa [bv_ofNat_toNat_eq mx] at h

private theorem fp_mb_bv {mx : BitVec 64} (hmx : mx.toNat < 2 * dimacsBound) :
    (mx + 7) &&& ~~~7 = BitVec.ofNat 64 (markBytes mx.toNat) := by
  have h := fp_mb_eq hmx; rwa [bv_ofNat_toNat_eq mx] at h

private theorem fp_ub_bv {mx : BitVec 64} (hmx : mx.toNat < 2 * dimacsBound) :
    ((mx + 1) <<< (((2 : BitVec 32).signExtend 64).toNat % 64) + 7) &&& ~~~7 =
      BitVec.ofNat 64 (u32FullBytes mx.toNat) := by
  have h := fp_ub_eq hmx; rwa [bv_ofNat_toNat_eq mx] at h

private theorem full_fixed_bv_eq {mx : BitVec 64} (hmx : mx.toNat < 2 * dimacsBound) :
    (1152 : BitVec 64) + (320 : BitVec 64) +
      (((mx <<< (((1 : BitVec 32).signExtend 64).toNat % 64) + 7) &&& ~~~7) * (3 : BitVec 64)) +
      (((mx + 7) &&& ~~~7) * (5 : BitVec 64)) +
      ((((mx + 1) <<< (((2 : BitVec 32).signExtend 64).toNat % 64) + 7) &&& ~~~7) *
        (15 : BitVec 64)) +
      ((mx <<< (((1 : BitVec 32).signExtend 64).toNat % 64)) <<<
        (((3 : BitVec 32).signExtend 64).toNat % 64)) +
      (mx <<< (((6 : BitVec 32).signExtend 64).toNat % 64)) +
      (BitVec.ofNat 64 (fullMinDepthOf mx.toNat) <<< (((3 : BitVec 32).signExtend 64).toNat % 64)) =
      BitVec.ofNat 64 (fullFixedBytes mx.toNat) := by
  have h := full_fixed_bv_ofNat hmx; rwa [bv_ofNat_toNat_eq mx] at h

local macro "fp_jnz_t" h:ident : tactic => `(tactic|
  (dsimp only [Arg.val_var] at $h:ident; rw [decide_eq_true_eq] at $h:ident; fp_head_steps))
local macro "fp_jnz_f" h:ident : tactic => `(tactic|
  (dsimp only [Arg.val_var] at $h:ident; rw [decide_eq_false_iff_not] at $h:ident; fp_head_steps))

/-! ## 2. Sizing & pure layout proofs (`full_fixed_bytes`, `full_calc_*`) -/

theorem full_fixed_bytes_wp (Γ : Env) :
    ∀ a m Q X, fullFixedBytesSpec a m Q X → Func.wp Γ full_fixed_bytes_body a m Q X := by
  rintro ⟨mx, ⟨⟩⟩ m Q X ⟨hmx, hQ⟩
  have hmx' := hmx; unfold dimacsBound at hmx'
  unfold Func.wp full_fixed_bytes_body
  fp_head_steps
  refine wp_join_group
    (fun (v : Tup Val [i64]) m_md => v.1 = BitVec.ofNat 64 (fullMinDepthOf mx.toNat) ∧ m_md = m)
    ?_ ?_
  · rintro _ ⟨md_v, ⟨⟩⟩ m_md ⟨rfl, rfl⟩
    simp only [Blocks.get_here]; fp_head_steps
    rw [full_fixed_bv_eq hmx]
    exact hQ
  · intro J hJ; fp_head_steps
    have hadd1 : mx + (1 : BitVec 64) = BitVec.ofNat 64 (mx.toNat + 1) := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [hadd1, show (1000 : BitVec 64) = BitVec.ofNat 64 1000 from rfl,
      bv_ult_eq (by omega) (by decide)]
    refine wp_jnz_of (fun hlt => ?_) (fun hge => ?_)
    · fp_jnz_t hlt; exact hJ (_, ()) m ⟨by rw [hadd1]; simp [fullMinDepthOf, hlt], rfl⟩
    · fp_jnz_f hge; exact hJ (_, ()) m ⟨by simp [fullMinDepthOf, hge], rfl⟩

private def fullCalcExtCapExactSpec : Spec [i64] [i64] := fun (rem, ()) m Q _ =>
  Q (BitVec.ofNat 64 (fullCalcExtCap rem.toNat), ()) m

private theorem full_calc_ext_cap_exact_wp (Γ : Env) :
    ∀ a m Q X, fullCalcExtCapExactSpec a m Q X → Func.wp Γ full_calc_ext_cap_body a m Q X := by
  rintro ⟨rem, ⟨⟩⟩ m Q X hQ
  dsimp only [fullCalcExtCapExactSpec] at hQ
  unfold Func.wp full_calc_ext_cap_body
  fp_head_steps
  have hult8 : rem.ult (8192 : BitVec 64) = decide (rem.toNat < 8192) := by
    rw [bv64_ult_nat]; rfl
  rw [hult8]
  refine wp_jnz_of (fun hlt => ?_) (fun hge => ?_)
  · fp_jnz_t hlt
    have heq : fullCalcExtCap rem.toNat = 0 := by unfold fullCalcExtCap; simp [hlt]
    rw [heq] at hQ; exact hQ
  · fp_jnz_f hge
    fp_head_steps
    rw [fp_shr5_bv rem]
    refine wp_join_group
      (fun (v : Tup Val [i64]) mc => v.1 = BitVec.ofNat 64 (min (rem.toNat / 32) 131072) ∧ mc = m)
      ?_ ?_
    · rintro _ ⟨cv, ⟨⟩⟩ mc ⟨rfl, rfl⟩
      simp only [Blocks.get_here]; fp_head_steps
      rw [fp_and_not1, bv64_ofNat_toNat (by omega)]
      have heq : fullCalcExtCap rem.toNat = (min (rem.toNat / 32) 131072 / 2) * 2 := by
        unfold fullCalcExtCap; simp [hge]
      rw [heq] at hQ; exact hQ
    · intro J hJ; fp_head_steps
      rw [show (131072 : BitVec 64) = BitVec.ofNat 64 131072 from rfl,
        bv_ult_eq (by decide) (by have := rem.isLt; omega)]
      refine wp_jnz_of (fun hgt => ?_) (fun hle => ?_)
      · fp_jnz_t hgt; refine hJ (_, ()) m ⟨?_, rfl⟩
        rw [Nat.min_eq_right (by omega)]
      · fp_jnz_f hle; refine hJ (_, ()) m ⟨?_, rfl⟩
        rw [Nat.min_eq_left (by omega)]

theorem full_calc_ext_cap_wp (Γ : Env) :
    ∀ a m Q X, fullCalcExtCapSpec a m Q X → Func.wp Γ full_calc_ext_cap_body a m Q X := by
  rintro ⟨rem, ⟨⟩⟩ m Q X hQ
  refine full_calc_ext_cap_exact_wp Γ (rem, ()) m Q X ?_
  have hlt : fullCalcExtCap rem.toNat ≤ 131072 := by unfold fullCalcExtCap; split <;> omega
  have hdv : 4 * fullCalcExtCap rem.toNat ≤ rem.toNat / 8 := by
    unfold fullCalcExtCap; split <;> omega
  refine hQ (BitVec.ofNat 64 (fullCalcExtCap rem.toNat)) ?_ (fun hlt8 => ?_) ?_
  · rw [bv64_ofNat_toNat (by omega)]; exact hlt
  · unfold fullCalcExtCap; simp [hlt8]
  · rw [bv64_ofNat_toNat (by omega)]; exact hdv

private def fullCalcScrCapExactSpec : Spec [i64] [i64] := fun (rem, ()) m Q _ =>
  Q (BitVec.ofNat 64 (fullCalcScrCap rem.toNat), ()) m

private theorem full_calc_scr_cap_exact_wp (Γ : Env) :
    ∀ a m Q X, fullCalcScrCapExactSpec a m Q X → Func.wp Γ full_calc_scr_cap_body a m Q X := by
  rintro ⟨rem, ⟨⟩⟩ m Q X hQ
  dsimp only [fullCalcScrCapExactSpec] at hQ
  unfold Func.wp full_calc_scr_cap_body
  fp_head_steps
  have hult8 : rem.ult (8192 : BitVec 64) = decide (rem.toNat < 8192) := by
    rw [bv64_ult_nat]; rfl
  rw [hult8]
  refine wp_jnz_of (fun hlt => ?_) (fun hge => ?_)
  · fp_jnz_t hlt
    have heq : fullCalcScrCap rem.toNat = 0 := by unfold fullCalcScrCap; simp [hlt]
    rw [heq] at hQ; exact hQ
  · fp_jnz_f hge
    refine wp_join_group (fun (v : Tup Val [i64]) mc0 =>
      v.1 = BitVec.ofNat 64 (if 16384 ≤ rem.toNat then rem.toNat / 16 else rem.toNat / 32) ∧
        mc0 = m) ?_ ?_
    · rintro _ ⟨c0, ⟨⟩⟩ mc0 ⟨rfl, rfl⟩
      simp only [Blocks.get_here]; fp_head_steps
      let raw := if 16384 ≤ rem.toNat then rem.toNat / 16 else rem.toNat / 32
      have hraw64 : raw < 2 ^ 64 := by dsimp [raw]; have := rem.isLt; split <;> omega
      refine wp_join_group
        (fun (v : Tup Val [i64]) mc1 => v.1 = BitVec.ofNat 64 (min raw 32768) ∧ mc1 = mc0) ?_ ?_
      · rintro _ ⟨c1, ⟨⟩⟩ mc1 ⟨rfl, rfl⟩
        simp only [Blocks.get_here]; fp_head_steps
        rw [fp_and_not1, bv64_ofNat_toNat (by omega)]
        have heq : fullCalcScrCap rem.toNat = (min raw 32768 / 2) * 2 := by
          unfold fullCalcScrCap; simp [hge]; rfl
        rw [heq] at hQ; exact hQ
      · intro J1 hJ1; fp_head_steps
        rw [show (32768 : BitVec 64) = BitVec.ofNat 64 32768 from rfl,
          bv_ult_eq (by decide) hraw64]
        refine wp_jnz_of (fun hgt => ?_) (fun hle => ?_)
        · fp_jnz_t hgt; refine hJ1 (_, ()) mc0 ⟨?_, rfl⟩
          rw [Nat.min_eq_right (by omega)]
        · fp_jnz_f hle; refine hJ1 (_, ()) mc0 ⟨?_, rfl⟩
          rw [Nat.min_eq_left (by omega)]
    · intro J0 hJ0; fp_head_steps
      have hule16 : (16384 : BitVec 64).ule rem = decide (16384 ≤ rem.toNat) := by
        rw [bv64_ule_nat]; rfl
      rw [hule16]
      refine wp_jnz_of (fun hge2 => ?_) (fun hlt2 => ?_)
      · fp_jnz_t hge2; rw [fp_shr4_bv rem]
        exact hJ0 (_, ()) m ⟨by simp [hge2], rfl⟩
      · fp_jnz_f hlt2; rw [fp_shr5_bv rem]
        exact hJ0 (_, ()) m ⟨by simp [hlt2], rfl⟩

theorem full_calc_scr_cap_wp (Γ : Env) :
    ∀ a m Q X, fullCalcScrCapSpec a m Q X → Func.wp Γ full_calc_scr_cap_body a m Q X := by
  rintro ⟨rem, ⟨⟩⟩ m Q X hQ
  refine full_calc_scr_cap_exact_wp Γ (rem, ()) m Q X ?_
  have hlt : fullCalcScrCap rem.toNat ≤ 32768 := by
    unfold fullCalcScrCap; split; omega; dsimp only; split <;> omega
  have hdv : 4 * fullCalcScrCap rem.toNat ≤ rem.toNat / 4 := by
    unfold fullCalcScrCap; split; omega; dsimp only; split <;> omega
  refine hQ (BitVec.ofNat 64 (fullCalcScrCap rem.toNat)) ?_ (fun hlt8 => ?_) ?_
  · rw [bv64_ofNat_toNat (by omega)]; exact hlt
  · unfold fullCalcScrCap; simp [hlt8]
  · rw [bv64_ofNat_toNat (by omega)]; exact hdv

private abbrev fullBvaCap (avail mv nc f0 : Nat) : Nat :=
  if 2 ≤ mv ∧ nc * 48 + 8192 < avail - f0 then
    min (min (mv / 2 + 16) 4096) (((avail - f0) - nc * 48 - 4096) / 2688)
  else 0

private theorem fullBvaCap_le (avail mv nc f0 : Nat) : fullBvaCap avail mv nc f0 ≤ 4096 := by
  unfold fullBvaCap; split <;> omega

private theorem fullCalcMaxV_eq1 {avail mv nc f0 : Nat}
    (hlt : avail < fullFixedBytes (mv + fullBvaCap avail mv nc f0)) :
    fullCalcMaxV avail mv nc f0 = mv := by
  unfold fullCalcMaxV fullBvaCap at *; dsimp only at *
  rw [ite_eq_left_iff.mpr fun h => absurd (Or.inl hlt) h]

private theorem fullCalcMaxV_eq2 {avail mv nc f0 : Nat}
    (hlt : avail - fullFixedBytes (mv + fullBvaCap avail mv nc f0) < nc * 40 + 136) :
    fullCalcMaxV avail mv nc f0 = mv := by
  unfold fullCalcMaxV fullBvaCap at *; dsimp only at *
  rw [ite_eq_left_iff.mpr fun h => absurd (Or.inr hlt) h]

private theorem fullCalcMaxV_eq3 {avail mv nc f0 : Nat}
    (h1 : ¬ avail < fullFixedBytes (mv + fullBvaCap avail mv nc f0))
    (h2 : ¬ avail - fullFixedBytes (mv + fullBvaCap avail mv nc f0) < nc * 40 + 136) :
    fullCalcMaxV avail mv nc f0 = mv + fullBvaCap avail mv nc f0 := by
  unfold fullCalcMaxV fullBvaCap at *; dsimp only at *
  rw [ite_eq_right_iff.mpr fun h => absurd h (by omega)]

private theorem full_calc_max_v_post_wp (Γ : Env)
    (hFixed : ∀ a m Q X, fullFixedBytesSpec a m Q X →
      Γ "full_fixed_bytes" [i64] [i64] a m Q X)
    {avail mv nc f0 : Val i64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hmv : mv.toNat < dimacsBound) (hnc : nc.toNat < dimacsBound)
    (hQ : Q (BitVec.ofNat 64 (fullCalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat), ()) m) :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var mv,
        Arg.var (BitVec.ofNat 64 (fullBvaCap avail.toNat mv.toNat nc.toNat f0.toNat)), ())) fun p =>
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
  let bva := fullBvaCap avail.toNat mv.toNat nc.toNat f0.toNat
  have hbva_le : bva ≤ 4096 := fullBvaCap_le _ _ _ _
  have hmv_b := hmv; have hnc_b := hnc; unfold dimacsBound at hmv_b hnc_b
  fp_head_steps
  have hmv_add : mv + BitVec.ofNat 64 bva = BitVec.ofNat 64 (mv.toNat + bva) := by
    apply BitVec.eq_of_toNat_eq; have := mv.isLt
    simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  let max_v := mv.toNat + bva
  have hmax_bd : max_v < 2 * dimacsBound := by unfold dimacsBound; omega
  rw [hmv_add]
  have hmax_v_toNat : (BitVec.ofNat 64 max_v).toNat = max_v := bv64_ofNat_toNat (by omega)
  apply wp_call_of_spec; apply hFixed
  refine ⟨?_, ?_⟩
  · dsimp only [Arg.val_var]; rw [hmax_v_toNat]; exact hmax_bd
  dsimp only [Arg.val_var]; rw [hmax_v_toNat]
  have hfx_m_lt := fullFixedBytes_lt hmax_bd
  have hnc40 : nc * (40 : BitVec 64) + 136 = BitVec.ofNat 64 (nc.toNat * 40 + 136) := by
    apply BitVec.eq_of_toNat_eq; have := nc.isLt
    simp [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  fp_head_steps
  have hult_av : avail.ult (BitVec.ofNat 64 (fullFixedBytes max_v)) =
      decide (avail.toNat < fullFixedBytes max_v) := by
    rw [bv64_ult_nat, bv64_ofNat_toNat (by omega)]
  rw [hult_av]
  refine wp_jnz_of (fun hlt => ?_) (fun hge => ?_)
  · fp_jnz_t hlt
    rw [fullCalcMaxV_eq1 hlt, bv_ofNat_toNat_eq mv] at hQ; exact hQ
  · fp_jnz_f hge; fp_head_steps
    have hsub_fx : avail - BitVec.ofNat 64 (fullFixedBytes max_v) =
        BitVec.ofNat 64 (avail.toNat - fullFixedBytes max_v) := by
      apply BitVec.eq_of_toNat_eq; have := avail.isLt
      simp [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    rw [hsub_fx, hnc40, bv_ult_eq (by have := avail.isLt; omega) (by omega)]
    refine wp_jnz_of (fun hlt2 => ?_) (fun hge2 => ?_)
    · fp_jnz_t hlt2
      rw [fullCalcMaxV_eq2 hlt2, bv_ofNat_toNat_eq mv] at hQ; exact hQ
    · fp_jnz_f hge2
      rw [fullCalcMaxV_eq3 hge hge2] at hQ; exact hQ

private theorem full_calc_bva_min_wp (Γ : Env)
    {avail mv nc f0 cand : Val i64} {m : Mem 64} {Q : Post [i64]} {X : XPost} {J : Cont [i64]}
    (hmv_ge : 2 ≤ mv.toNat) (hnc : nc.toNat < dimacsBound)
    (hrem64 : avail.toNat - f0.toNat < 2 ^ 64)
    (hgt : nc.toNat * 48 + 8192 < avail.toNat - f0.toNat)
    (hcand : cand = BitVec.ofNat 64 (min (mv.toNat / 2 + 16) 4096))
    (hJ : ∀ xs m_1, xs.1 = BitVec.ofNat 64 (fullBvaCap avail.toNat mv.toNat nc.toNat f0.toNat) ∧
      m_1 = m → J xs m_1) :
    wp Γ Q X (Expr.let_ (Op.mk (.mul i64) (Arg.var nc, Arg.imm 48, ())) fun p_1 =>
      Expr.let_ (Op.mk (.sub i64) (Arg.var (BitVec.ofNat 64 (avail.toNat - f0.toNat)),
          Arg.var p_1.fst, ())) fun p_2 =>
      Expr.let_ (Op.mk (.sub i64) (Arg.var p_2.fst, Arg.imm 4096, ())) fun p_3 =>
      Expr.let_ (Op.mk (.udiv 64) (Arg.var p_3.fst, Arg.imm 2688, ())) fun p_4 =>
      Expr.group (sig := [[i64]])
        (fun _Js => Blocks.cons (fun p => Expr.jump J (Arg.var p.fst, ())) Blocks.nil)
        fun Js =>
          Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var cand, Arg.var p_4.fst, ()))
            fun p_5 =>
            Expr.jnz (Arg.var p_5.fst) (Expr.jump Js.fst (Arg.var cand, ()))
              (Expr.jump Js.fst (Arg.var p_4.fst, ()))) m := by
  subst hcand
  let rem0 := avail.toNat - f0.toNat
  have hnc_b := hnc; unfold dimacsBound at hnc_b
  fp_head_steps
  have hsub48 : BitVec.ofNat 64 rem0 - nc * (48 : BitVec 64) - (4096 : BitVec 64) =
      BitVec.ofNat 64 (rem0 - nc.toNat * 48 - 4096) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat]
    have := nc.isLt; omega
  rw [hsub48]
  apply wp_udiv_of
  · dsimp only [Arg.val_imm]; intro h; have := congrArg BitVec.toNat h; simp at this
  · dsimp only [Arg.val_var, Arg.val_imm]
    have hdiv_eq : BitVec.ofNat 64 (rem0 - nc.toNat * 48 - 4096) / (2688 : BitVec 64) =
        BitVec.ofNat 64 ((rem0 - nc.toNat * 48 - 4096) / 2688) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_udiv, Nat.mod_eq_of_lt (show rem0 - nc.toNat * 48 - 4096 < 2 ^ 64
        by omega), Nat.mod_eq_of_lt (show (rem0 - nc.toNat * 48 - 4096) / 2688 < 2 ^ 64
        by omega)]
    rw [hdiv_eq]
    refine wp_join_group
      (fun (v : Tup Val [i64]) mx =>
        v.1 = BitVec.ofNat 64 (fullBvaCap avail.toNat mv.toNat nc.toNat f0.toNat) ∧
          mx = m) ?_ ?_
    · rintro _ ⟨bx_v, ⟨⟩⟩ mx ⟨rfl, hmc⟩
      subst mx; simp only [Blocks.get_here]; fp_head_steps; exact hJ (_, ()) m ⟨rfl, rfl⟩
    · intro Jm hJm
      let max_bva := (rem0 - nc.toNat * 48 - 4096) / 2688
      have hmb64 : max_bva < 2 ^ 64 := by
        dsimp [max_bva]
        exact Nat.lt_of_le_of_lt
          (Nat.le_trans (Nat.div_le_self _ _) (Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)))
          hrem64
      have hc64 : min (mv.toNat / 2 + 16) 4096 < 2 ^ 64 := by omega
      have hult := bv_ult_eq hc64 hmb64; dsimp only [max_bva] at hult
      fp_head_steps; rw [hult]
      refine wp_jnz_of (fun hclt => ?_) (fun hcge => ?_)
      · fp_jnz_t hclt; refine hJm (_, ()) m ⟨?_, rfl⟩
        unfold fullBvaCap
        rw [ite_eq_left_iff.mpr fun h => absurd (And.intro hmv_ge hgt) h]
        exact congrArg (BitVec.ofNat 64) (Nat.min_eq_left (Nat.le_of_lt hclt)).symm
      · fp_jnz_f hcge; refine hJm (_, ()) m ⟨?_, rfl⟩
        unfold fullBvaCap
        rw [ite_eq_left_iff.mpr fun h => absurd (And.intro hmv_ge hgt) h]
        exact congrArg (BitVec.ofNat 64) (Nat.min_eq_right (Nat.le_of_not_gt hcge)).symm

private theorem full_calc_bva_cand_wp (Γ : Env)
    {mv : Val i64} {m : Mem 64} {Q : Post [i64]} {X : XPost} {Jc : Cont [i64]}
    (hmv : mv.toNat < dimacsBound)
    (hJc : ∀ xs m_1, xs.1 = BitVec.ofNat 64 (min (mv.toNat / 2 + 16) 4096) ∧ m_1 = m → Jc xs m_1) :
    wp Γ Q X (Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl)
        (Arg.var (mv >>> (((1 : BitVec 32).signExtend 64).toNat % 64) + 16), Arg.imm 4096, ()))
        fun p_6 =>
      Expr.jnz (Arg.var p_6.fst) (Expr.jump Jc (Arg.imm 4096, ()))
        (Expr.jump Jc (Arg.var (mv >>> (((1 : BitVec 32).signExtend 64).toNat % 64) + 16), ())))
      m := by
  have hmv_b : mv.toNat < 2 ^ 28 := hmv
  have hlt36 : (2 ^ 36 : Nat) < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by decide)
  fp_head_steps
  have hadd16 : mv >>> (((1 : BitVec 32).signExtend 64).toNat % 64) + (16 : BitVec 64) =
      BitVec.ofNat 64 (mv.toNat / 2 + 16) := by
    rw [fp_shr1_bv mv, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, bv_add_ofNat]
  have h4096_64 : 4096 < 2 ^ 64 := Nat.lt_trans (by decide) hlt36
  have hadd16_64 : mv.toNat / 2 + 16 < 2 ^ 64 := Nat.lt_trans (by omega) hlt36
  rw [hadd16, show (4096 : BitVec 64) = BitVec.ofNat 64 4096 from rfl,
    bv_ult_eq h4096_64 hadd16_64]
  refine wp_jnz_of (fun hcgt => ?_) (fun hcle => ?_)
  · fp_jnz_t hcgt; refine hJc ((4096 : BitVec 64), ()) m ⟨?_, rfl⟩
    rw [Nat.min_eq_right (Nat.le_of_lt hcgt)]; rfl
  · fp_jnz_f hcle; refine hJc (_, ()) m ⟨?_, rfl⟩
    rw [Nat.min_eq_left (Nat.le_of_not_gt hcle)]

private theorem full_calc_bva_ult (avail f0 nc : Val i64) (hfle : f0.toNat ≤ avail.toNat)
    (hnc : nc.toNat < dimacsBound) :
    ((nc * (48 : BitVec 64) + 8192).ult (avail - f0)) =
      decide (nc.toNat * 48 + 8192 < avail.toNat - f0.toNat) := by
  have hnc_b : nc.toNat < 2 ^ 28 := hnc
  have hrem_eq : avail - f0 = BitVec.ofNat 64 (avail.toNat - f0.toNat) := by
    have h := bv_sub_ofNat hfle avail.isLt
    rwa [bv_ofNat_toNat_eq avail, bv_ofNat_toNat_eq f0] at h
  have hrem64 : avail.toNat - f0.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) avail.isLt
  have hnc48 : nc * (48 : BitVec 64) + (8192 : BitVec 64) =
      BitVec.ofNat 64 (nc.toNat * 48 + 8192) := by
    rw [show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl,
      show (8192 : BitVec 64) = BitVec.ofNat 64 8192 from rfl, bv64_mul_nat, bv_add_ofNat]
  have hlt36 : nc.toNat * 48 + 8192 < 2 ^ 36 := by omega
  have hnc48_64 : nc.toNat * 48 + 8192 < 2 ^ 64 :=
    Nat.lt_trans hlt36 (Nat.pow_lt_pow_right (by decide) (by decide))
  rw [hrem_eq, hnc48, bv_ult_eq hnc48_64 hrem64]

private theorem full_calc_max_v_bva_wp (Γ : Env)
    {avail mv nc f0 : Val i64} {m : Mem 64} {Q : Post [i64]} {X : XPost} {J : Cont [i64]}
    (hmv : mv.toNat < dimacsBound) (hnc : nc.toNat < dimacsBound)
    (hfle : f0.toNat ≤ avail.toNat)
    (hJ : ∀ xs m_1, xs.1 = BitVec.ofNat 64 (fullBvaCap avail.toNat mv.toNat nc.toNat f0.toNat) ∧
      m_1 = m → J xs m_1) :
    wp Γ Q X (Expr.let_ (Op.mk (.cmp .uge i64 Ty.bool rfl) (Arg.var mv, Arg.imm 2, ())) fun p =>
      Expr.jnz (Arg.var p.fst)
        (Expr.let_ (Op.mk (.mul i64) (Arg.var nc, Arg.imm 48, ())) fun p_1 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var p_1.fst, Arg.imm 8192, ())) fun p_2 =>
          Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var (avail - f0), Arg.var p_2.fst, ()))
            fun p_3 =>
            Expr.jnz (Arg.var p_3.fst)
              (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun p_4 =>
                Expr.let_ (Op.mk (.lshr i64) (Arg.var mv, Arg.var p_4.fst, ())) fun p_5 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var p_5.fst, Arg.imm 16, ())) fun cand =>
                Expr.group (sig := [[i64]])
                  (fun _Js => Blocks.cons (fun c =>
                    Expr.let_ (Op.mk (.mul i64) (Arg.var nc, Arg.imm 48, ())) fun p_6 =>
                    Expr.let_ (Op.mk (.sub i64) (Arg.var (avail - f0), Arg.var p_6.fst, ()))
                      fun p_7 =>
                    Expr.let_ (Op.mk (.sub i64) (Arg.var p_7.fst, Arg.imm 4096, ())) fun p_8 =>
                    Expr.let_ (Op.mk (.udiv 64) (Arg.var p_8.fst, Arg.imm 2688, ())) fun p_9 =>
                    Expr.group (sig := [[i64]])
                      (fun _Js_1 => Blocks.cons (fun p_10 =>
                        Expr.jump J (Arg.var p_10.fst, ())) Blocks.nil)
                      fun Js_1 =>
                        Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl)
                          (Arg.var c.fst, Arg.var p_9.fst, ())) fun p_10 =>
                        Expr.jnz (Arg.var p_10.fst) (Expr.jump Js_1.fst (Arg.var c.fst, ()))
                          (Expr.jump Js_1.fst (Arg.var p_9.fst, ()))) Blocks.nil)
                  fun Js =>
                    Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl)
                      (Arg.var cand.fst, Arg.imm 4096, ())) fun p_6 =>
                    Expr.jnz (Arg.var p_6.fst) (Expr.jump Js.fst (Arg.imm 4096, ()))
                      (Expr.jump Js.fst (Arg.var cand.fst, ())))
              (Expr.jump J (Arg.imm 0, ())))
        (Expr.jump J (Arg.imm 0, ()))) m := by
  have hrem_eq : avail - f0 = BitVec.ofNat 64 (avail.toNat - f0.toNat) := by
    have h := bv_sub_ofNat hfle avail.isLt
    rwa [bv_ofNat_toNat_eq avail, bv_ofNat_toNat_eq f0] at h
  have hrem64 : avail.toNat - f0.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) avail.isLt
  fp_head_steps
  have hule2 : (2 : BitVec 64).ule mv = decide (2 ≤ mv.toNat) := by rw [bv64_ule_nat]; rfl
  rw [hule2]
  refine wp_jnz_of (fun hmv_ge => ?_) (fun hmv_lt => ?_)
  · fp_jnz_t hmv_ge; fp_head_steps
    conv => arg 4; arg 1; arg 1; rw [full_calc_bva_ult avail f0 nc hfle hnc]
    refine wp_jnz_of (fun hgt => ?_) (fun hle => ?_)
    · fp_jnz_t hgt
      refine wp_join_group (fun (v : Tup Val [i64]) mc =>
        v.1 = BitVec.ofNat 64 (min (mv.toNat / 2 + 16) 4096) ∧ mc = m) ?_ ?_
      · rintro _ ⟨cand_v, ⟨⟩⟩ mc ⟨hcand, rfl⟩
        simp only [Blocks.get_here]; rw [hrem_eq]
        exact full_calc_bva_min_wp Γ hmv_ge hnc hrem64 hgt hcand hJ
      · intro Jc hJc; exact full_calc_bva_cand_wp Γ hmv hJc
    · fp_jnz_f hle
      refine hJ (0#64, ()) m ⟨?_, rfl⟩
      unfold fullBvaCap
      rw [ite_eq_right_iff.mpr (fun h => absurd h.2 hle)]
  · fp_jnz_f hmv_lt
    refine hJ (0#64, ()) m ⟨?_, rfl⟩
    unfold fullBvaCap
    rw [ite_eq_right_iff.mpr (fun h => absurd h.1 hmv_lt)]

private def fullCalcMaxVExactSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (avail, mv, nc, f0, ()) m Q _ =>
    mv.toNat < dimacsBound ∧ nc.toNat < dimacsBound ∧
    f0.toNat = fullFixedBytes mv.toNat ∧ fullFixedBytes mv.toNat ≤ avail.toNat ∧
    Q (BitVec.ofNat 64 (fullCalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat), ()) m

private theorem full_calc_max_v_exact_wp (Γ : Env)
    (hFixed : ∀ a m Q X, fullFixedBytesSpec a m Q X →
      Γ "full_fixed_bytes" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullCalcMaxVExactSpec a m Q X → Func.wp Γ full_calc_max_v_body a m Q X := by
  rintro ⟨avail, mv, nc, f0, ⟨⟩⟩ m Q X ⟨hmv, hnc, hf0, hfx, hQ⟩
  unfold Func.wp full_calc_max_v_body
  fp_head_steps
  refine wp_join_group (fun (v : Tup Val [i64]) m_b =>
    v.1 = BitVec.ofNat 64 (fullBvaCap avail.toNat mv.toNat nc.toNat f0.toNat) ∧ m_b = m) ?_ ?_
  · rintro _ ⟨bv_v, ⟨⟩⟩ m_b ⟨rfl, rfl⟩
    simp only [Blocks.get_here]
    exact full_calc_max_v_post_wp Γ hFixed hmv hnc hQ
  · intro J hJ
    exact full_calc_max_v_bva_wp Γ hmv hnc (by rw [hf0]; exact hfx) hJ

theorem full_calc_max_v_wp (Γ : Env)
    (hFixed : ∀ a m Q X, fullFixedBytesSpec a m Q X →
      Γ "full_fixed_bytes" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullCalcMaxVSpec a m Q X → Func.wp Γ full_calc_max_v_body a m Q X := by
  rintro ⟨avail, mv, nc, f0, ⟨⟩⟩ m Q X ⟨hmv, hnc, hf0, hfx, hQ⟩
  refine full_calc_max_v_exact_wp Γ hFixed _ m Q X ⟨hmv, hnc, hf0, by omega, ?_⟩
  have hlt : fullCalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat < 2 * dimacsBound :=
    fullCalcMaxV_lt hmv
  have h64 : fullCalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat < 2 ^ 64 := by
    unfold dimacsBound at hlt; omega
  have hto : (BitVec.ofNat 64 (fullCalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat)).toNat =
      fullCalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat := bv64_ofNat_toNat h64
  refine hQ _ ?_ (by rw [hto]; exact hlt) ?_
  · rw [hto, hf0]; exact fullCalcMaxV_ge
  · rw [hto, hf0]; exact fullCalcMaxV_fits (by omega)

/-! ## 3. Header init proofs (`full_init_ptrs`, `full_init_hdr`, `full_init_arenas`) -/

private theorem len_cons10 {α} (xs : List α) (n : Nat) (h : xs.length = n + 10) :
    ∃ a b c d e f g h1 i j ys, ys.length = n ∧
      xs = a :: b :: c :: d :: e :: f :: g :: h1 :: i :: j :: ys := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h1, _ | ⟨i, _ |
    ⟨j, ys⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨a, b, c, d, e, f, g, h1, i, j, ys, h, rfl⟩

private theorem decompose35 {α} (xs : List α) (h : xs.length = 35) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 d0 d1 d2 d3 d4 : α,
      xs = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9,
            b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
            c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4] := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, xs1, h1, rfl⟩ := len_cons10 xs 25 h
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, xs2, h2, rfl⟩ := len_cons10 xs1 15 h1
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, xs3, h3, rfl⟩ := len_cons10 xs2 5 h2
  rcases xs3 with _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, _ | ⟨d3, _ | ⟨d4, _ | _⟩⟩⟩⟩⟩ <;> simp at h3
  exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩

private def fullInitPtrs4Spec : Spec [i64, i64, i64] [] := fun (h, hdr_addr, max_v, ()) m Q _ =>
  ∃ (w0 w1 w2 w3 : List (BitVec 64)) (R : Mem 64 → Prop),
    max_v.toNat < 2 * dimacsBound ∧ (hdrTail4 h w0 w1 w2 w3 ⋆ R) m ∧
    ∀ m',
      (hdrTail4 h (ptrsW0 hdr_addr max_v.toNat w0) (ptrsW1 hdr_addr max_v.toNat w1)
        (ptrsW2 hdr_addr max_v.toNat w2) (ptrsW3 hdr_addr max_v.toNat w3) ⋆ R) m' →
      Q () m'

private theorem full_init_ptrs4_wp (Γ : Env) :
    ∀ a m Q X, fullInitPtrs4Spec a m Q X → Func.wp Γ full_init_ptrs_body a m Q X := by
  rintro ⟨h, hdr_addr, max_v, ⟨⟩⟩ m Q X ⟨w0, w1, w2, w3, R, hmx, hm, hQ⟩
  have hmx' := hmx; unfold dimacsBound at hmx'
  unfold Func.wp full_init_ptrs_body
  fp_head_steps
  refine wp_join_group
    (fun (v : Tup Val [i64]) m_md =>
      v.1 = BitVec.ofNat 64 (fullMinDepthOf max_v.toNat) ∧ m_md = m) ?_ ?_
  · rintro _ ⟨md_v, ⟨⟩⟩ m_md ⟨rfl, rfl⟩
    simp only [Blocks.get_here]; fp_head_steps
    have hsh1_3 : BitVec.ofNat 64 (2 * max_v.toNat) <<<
        (((3 : BitVec 32).signExtend 64).toNat % 64) =
        BitVec.ofNat 64 (8 * (2 * max_v.toNat)) := fp_shl_sext3
    have hsh_md : BitVec.ofNat 64 (fullMinDepthOf max_v.toNat) <<<
        (((3 : BitVec 32).signExtend 64).toNat % 64) =
        BitVec.ofNat 64 (8 * fullMinDepthOf max_v.toNat) := fp_shl_sext3
    rw [fp_vb_bv hmx, fp_mb_bv hmx, fp_ub_bv hmx, fp_shl1_bv max_v, fp_shl3_bv max_v,
      hsh1_3, hsh_md, show 8 * (2 * max_v.toNat) = 16 * max_v.toNat by omega] at hm
    rw [show (1152 : BitVec 64) = BitVec.ofNat 64 1152 from rfl,
      show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl,
      show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl] at hm
    rw [← fullPVals.eq_1 hdr_addr max_v.toNat, ← fullPWalkVals.eq_1, ← fullPLitMark.eq_1,
      ← fullPMark.eq_1, ← fullPPhases.eq_1, ← fullPPhasesTarget.eq_1, ← fullPPhasesBest.eq_1,
      ← fullPWalkBest.eq_1, ← fullPFlags.eq_1, ← fullPLevel.eq_1, ← fullPReason.eq_1,
      ← fullPTrail.eq_1, ← fullPTrailPos.eq_1, ← fullPTmp.eq_1, ← fullPHeap.eq_1,
      ← fullPPos.eq_1, ← fullPMinClr.eq_1, ← fullPShrinkStk.eq_1, ← fullPQPrev.eq_1,
      ← fullPQNext.eq_1, ← fullPQStamp.eq_1, ← fullPFrameTrail.eq_1, ← fullPFrameDec.eq_1,
      ← fullPWvec.eq_1, ← fullPRepr.eq_1, ← fullPWsort.eq_1, ← fullPWorkStk1.eq_1,
      ← fullPWorkStk2.eq_1, ← fullPTarjanMark.eq_1, ← fullPTarjanReach.eq_1, ← fullPScore.eq_1,
      ← fullPSimSig.eq_1, ← fullPMinStk.eq_1, ← fullPGlueUsed.eq_1, ← fullPLastLearned.eq_1,
      ← fullPArena.eq_1] at hm
    exact hQ m hm
  · intro J hJ; fp_head_steps
    have hadd1 : max_v + (1 : BitVec 64) = BitVec.ofNat 64 (max_v.toNat + 1) := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [hadd1, show (1000 : BitVec 64) = BitVec.ofNat 64 1000 from rfl,
      bv_ult_eq (by omega) (by decide)]
    refine wp_jnz_of (fun hlt => ?_) (fun hge => ?_)
    · fp_jnz_t hlt; exact hJ (_, ()) m ⟨by rw [hadd1]; simp [fullMinDepthOf, hlt], rfl⟩
    · fp_jnz_f hge; exact hJ (_, ()) m ⟨by simp [fullMinDepthOf, hge], rfl⟩

private theorem ptrsW0_slots (hdr : BitVec 64) (mx : Nat) (w0 : List (BitVec 64))
    (h0 : w0.length = 35) :
    let p := ptrsW0 hdr mx w0
    p[0]? = w0[0]? ∧ p[1]? = w0[1]? ∧ p[11]? = w0[11]? ∧ p[12]? = w0[12]? ∧
    p[4]? = some (fullPVals hdr mx) ∧ p[5]? = some (fullPMark hdr mx) ∧
    p[6]? = some (fullPLevel hdr mx) ∧ p[7]? = some (fullPReason hdr mx) ∧
    p[8]? = some (fullPTrail hdr mx) ∧ p[9]? = some (fullPWvec hdr mx) ∧
    p[10]? = some (fullPArena hdr mx) ∧ p[13]? = some (fullPTmp hdr mx) ∧
    p[21]? = some (fullPHeap hdr mx) ∧ p[22]? = some (fullPPos hdr mx) ∧
    p[23]? = some (fullPScore hdr mx) ∧ p[24]? = some (fullPPhases hdr mx) ∧
    p[25]? = some (fullPMinStk hdr mx) ∧ p[26]? = some (fullPMinClr hdr mx) ∧
    p[29]? = some (BitVec.ofNat 64 (fullMinDepthOf mx)) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35 w0 h0
  simp [ptrsW0]

private theorem ptrsW1_slots (hdr : BitVec 64) (mx : Nat) (w1 : List (BitVec 64))
    (h1 : w1.length = 35) :
    let p := ptrsW1 hdr mx w1
    p[14]? = w1[14]? ∧ p[16]? = w1[16]? ∧ p[17]? = w1[17]? ∧
    p[6]? = some (fullPTrailPos hdr mx) ∧ p[7]? = some (fullPQPrev hdr mx) ∧
    p[8]? = some (fullPQNext hdr mx) ∧ p[9]? = some (fullPQStamp hdr mx) ∧
    p[10]? = some (fullPPhasesTarget hdr mx) ∧ p[11]? = some (fullPPhasesBest hdr mx) ∧
    p[12]? = some (fullPWsort hdr mx) ∧ p[13]? = some (fullPShrinkStk hdr mx) ∧
    p[15]? = some (fullPGlueUsed hdr mx) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35 w1 h1
  simp [ptrsW1]

private theorem ptrsW2_slots (hdr : BitVec 64) (mx : Nat) (w2 : List (BitVec 64))
    (h2 : w2.length = 35) :
    let p := ptrsW2 hdr mx w2
    p[26]? = some (fullPFlags hdr mx) ∧ p[27]? = some (fullPLitMark hdr mx) ∧
    p[28]? = some (fullPRepr hdr mx) ∧ p[29]? = some (fullPSimSig hdr mx) ∧
    p[30]? = some (fullPFrameTrail hdr mx) ∧ p[31]? = some (fullPFrameDec hdr mx) ∧
    p[32]? = some (fullPWorkStk1 hdr mx) ∧ p[33]? = some (fullPWorkStk2 hdr mx) ∧
    p[34]? = some (fullPTarjanMark hdr mx) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35 w2 h2
  simp [ptrsW2]

private theorem ptrsW3_slots (hdr : BitVec 64) (mx : Nat) (w3 : List (BitVec 64))
    (h3 : w3.length = 35) :
    let p := ptrsW3 hdr mx w3
    p[3]? = w3[3]? ∧ p[4]? = w3[4]? ∧ p[6]? = w3[6]? ∧ p[7]? = w3[7]? ∧
    p[0]? = some (fullPTarjanReach hdr mx) ∧ p[1]? = some (fullPWalkVals hdr mx) ∧
    p[2]? = some (fullPWalkBest hdr mx) ∧ p[8]? = some (fullPLastLearned hdr mx) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35 w3 h3
  simp [ptrsW3]

theorem full_init_ptrs_wp (Γ : Env) :
    ∀ a m Q X, fullInitPtrsSpec a m Q X → Func.wp Γ full_init_ptrs_body a m Q X := by
  rintro ⟨h, hdr_addr, max_v, ⟨⟩⟩ m Q X ⟨ws, R, hhdr, hw, hmx, _hfit, hm, hQ⟩
  rw [hhdr]; clear hhdr h
  let w0 := ws.take 35; let w1 := (ws.drop 35).take 35
  let w2 := (ws.drop 70).take 35; let w3 := (ws.drop 105).take 35
  have h0 : w0.length = 35 := by simp [w0, hw]
  have h1 : w1.length = 35 := by simp [w1, hw]
  have h2 : w2.length = 35 := by simp [w2, hw]
  have h3 : w3.length = 35 := by simp [w3, hw]
  refine full_init_ptrs4_wp Γ _ m Q X
    ⟨w0, w1, w2, w3, R, hmx, array64_to_hdrTail4 hw hm, fun m' hm' => ?_⟩
  let pw0 := ptrsW0 hdr_addr max_v.toNat w0
  let pw1 := ptrsW1 hdr_addr max_v.toNat w1
  let pw2 := ptrsW2 hdr_addr max_v.toNat w2
  let pw3 := ptrsW3 hdr_addr max_v.toNat w3
  have hp0 : pw0.length = 35 := by simp [pw0, h0]
  have hp1 : pw1.length = 35 := by simp [pw1, h1]
  have hp2 : pw2.length = 35 := by simp [pw2, h2]
  have hp3 : pw3.length = 35 := by simp [pw3, h3]
  let ws' := pw0 ++ pw1 ++ pw2 ++ pw3
  have hws'_len : ws'.length = 140 := by simp [ws', hp0, hp1, hp2, hp3]
  have hm'_arr : (array64 (hdr_addr + 32) ws' ⋆ R) m' := by
    rwa [hdrTail4_eq_array64 hp0 hp1 hp2 hp3] at hm'
  have s0 := ptrsW0_slots hdr_addr max_v.toNat w0 h0
  have s1 := ptrsW1_slots hdr_addr max_v.toNat w1 h1
  have s2 := ptrsW2_slots hdr_addr max_v.toNat w2 h2
  have s3 := ptrsW3_slots hdr_addr max_v.toNat w3 h3
  have a0 := fun i (hi : i < 35) => append4_getElem?_0 (w1 := pw1) (w2 := pw2) (w3 := pw3) hp0 hi
  have a1 := fun i (hi0 : 35 ≤ i) (hi1 : i < 70) =>
    append4_getElem?_1 (w2 := pw2) (w3 := pw3) hp0 hp1 hi0 hi1
  have a2 := fun i (hi0 : 70 ≤ i) (hi1 : i < 105) =>
    append4_getElem?_2 (w3 := pw3) hp0 hp1 hp2 hi0 hi1
  have a3 := fun i (hi0 : 105 ≤ i) => append4_getElem?_3 (w3 := pw3) hp0 hp1 hp2 hi0
  refine hQ ws' m' hws'_len (fun c hch hmx_eq => ?_) (fun i hi => ?_) hm'_arr
  · have ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18,
      p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34, p35, p36,
      p37⟩ :
        c.pVals = fullPVals hdr_addr max_v.toNat ∧ c.pMark = fullPMark hdr_addr max_v.toNat ∧
        c.pLevel = fullPLevel hdr_addr max_v.toNat ∧ c.pReason = fullPReason hdr_addr max_v.toNat ∧
        c.pTrail = fullPTrail hdr_addr max_v.toNat ∧ c.pWvec = fullPWvec hdr_addr max_v.toNat ∧
        c.pArena = fullPArena hdr_addr max_v.toNat ∧ c.pTmp = fullPTmp hdr_addr max_v.toNat ∧
        c.pHeap = fullPHeap hdr_addr max_v.toNat ∧ c.pPos = fullPPos hdr_addr max_v.toNat ∧
        c.pScore = fullPScore hdr_addr max_v.toNat ∧ c.pPhases = fullPPhases hdr_addr max_v.toNat ∧
        c.pMinStk = fullPMinStk hdr_addr max_v.toNat ∧
        c.pMinClr = fullPMinClr hdr_addr max_v.toNat ∧
        c.minDepth = fullMinDepthOf max_v.toNat ∧
        c.pTrailPos = fullPTrailPos hdr_addr max_v.toNat ∧
        c.pQPrev = fullPQPrev hdr_addr max_v.toNat ∧
        c.pQNext = fullPQNext hdr_addr max_v.toNat ∧
        c.pQStamp = fullPQStamp hdr_addr max_v.toNat ∧
        c.pPhasesTarget = fullPPhasesTarget hdr_addr max_v.toNat ∧
        c.pPhasesBest = fullPPhasesBest hdr_addr max_v.toNat ∧
        c.pWsort = fullPWsort hdr_addr max_v.toNat ∧
        c.pShrinkStk = fullPShrinkStk hdr_addr max_v.toNat ∧
        c.pGlueUsed = fullPGlueUsed hdr_addr max_v.toNat ∧
        c.pFlags = fullPFlags hdr_addr max_v.toNat ∧
        c.pLitMark = fullPLitMark hdr_addr max_v.toNat ∧
        c.pRepr = fullPRepr hdr_addr max_v.toNat ∧
        c.pSimSig = fullPSimSig hdr_addr max_v.toNat ∧
        c.pFrameTrail = fullPFrameTrail hdr_addr max_v.toNat ∧
        c.pFrameDec = fullPFrameDec hdr_addr max_v.toNat ∧
        c.pWorkStk1 = fullPWorkStk1 hdr_addr max_v.toNat ∧
        c.pWorkStk2 = fullPWorkStk2 hdr_addr max_v.toNat ∧
        c.pTarjanMark = fullPTarjanMark hdr_addr max_v.toNat ∧
        c.pTarjanReach = fullPTarjanReach hdr_addr max_v.toNat ∧
        c.pWalkVals = fullPWalkVals hdr_addr max_v.toNat ∧
        c.pWalkBest = fullPWalkBest hdr_addr max_v.toNat ∧
        c.pLastLearned = fullPLastLearned hdr_addr max_v.toNat := by
      unfold FullCfg.pArena FullCfg.pLastLearned FullCfg.pGlueUsed FullCfg.pMinStk FullCfg.pSimSig
        FullCfg.pScore FullCfg.pTarjanReach FullCfg.pTarjanMark FullCfg.pWorkStk2 FullCfg.pWorkStk1
        FullCfg.pWsort FullCfg.pRepr FullCfg.pWvec FullCfg.pFrameDec FullCfg.pFrameTrail
        FullCfg.pQStamp FullCfg.pQNext FullCfg.pQPrev FullCfg.pShrinkStk FullCfg.pMinClr
        FullCfg.pPos FullCfg.pHeap FullCfg.pTmp FullCfg.pTrailPos FullCfg.pTrail FullCfg.pReason
        FullCfg.pLevel FullCfg.pFlags FullCfg.pWalkBest FullCfg.pPhasesBest FullCfg.pPhasesTarget
        FullCfg.pPhases FullCfg.pMark FullCfg.pLitMark FullCfg.pWalkVals FullCfg.pVals
        FullCfg.minDepth fullPArena fullPLastLearned fullPGlueUsed fullPMinStk fullPSimSig
        fullPScore fullPTarjanReach fullPTarjanMark fullPWorkStk2 fullPWorkStk1 fullPWsort fullPRepr
        fullPWvec fullPFrameDec fullPFrameTrail fullPQStamp fullPQNext fullPQPrev fullPShrinkStk
        fullPMinClr fullPPos fullPHeap fullPTmp fullPTrailPos fullPTrail fullPReason fullPLevel
        fullPFlags fullPWalkBest fullPPhasesBest fullPPhasesTarget fullPPhases fullPMark
        fullPLitMark fullPWalkVals fullPVals
      simp only [hch, hmx_eq]
      repeat' first | apply And.intro | rfl | trivial
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [a0 4 (by decide), s0.2.2.2.2.1, p1]
    · rw [a0 5 (by decide), s0.2.2.2.2.2.1, p2]
    · rw [a0 6 (by decide), s0.2.2.2.2.2.2.1, p3]
    · rw [a0 7 (by decide), s0.2.2.2.2.2.2.2.1, p4]
    · rw [a0 8 (by decide), s0.2.2.2.2.2.2.2.2.1, p5]
    · rw [a0 9 (by decide), s0.2.2.2.2.2.2.2.2.2.1, p6]
    · rw [a0 10 (by decide), s0.2.2.2.2.2.2.2.2.2.2.1, p7]
    · rw [a0 13 (by decide), s0.2.2.2.2.2.2.2.2.2.2.2.1, p8]
    · rw [a0 21 (by decide), s0.2.2.2.2.2.2.2.2.2.2.2.2.1, p9]
    · rw [a0 22 (by decide), s0.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p10]
    · rw [a0 23 (by decide), s0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p11]
    · rw [a0 24 (by decide), s0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p12]
    · rw [a0 25 (by decide), s0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p13]
    · rw [a0 26 (by decide), s0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p14]
    · rw [a0 29 (by decide), s0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, p15]
    · rw [a1 41 (by decide) (by decide), s1.2.2.2.1, p16]
    · rw [a1 42 (by decide) (by decide), s1.2.2.2.2.1, p17]
    · rw [a1 43 (by decide) (by decide), s1.2.2.2.2.2.1, p18]
    · rw [a1 44 (by decide) (by decide), s1.2.2.2.2.2.2.1, p19]
    · rw [a1 45 (by decide) (by decide), s1.2.2.2.2.2.2.2.1, p20]
    · rw [a1 46 (by decide) (by decide), s1.2.2.2.2.2.2.2.2.1, p21]
    · rw [a1 47 (by decide) (by decide), s1.2.2.2.2.2.2.2.2.2.1, p22]
    · rw [a1 48 (by decide) (by decide), s1.2.2.2.2.2.2.2.2.2.2.1, p23]
    · rw [a1 50 (by decide) (by decide), s1.2.2.2.2.2.2.2.2.2.2.2, p24]
    · rw [a2 96 (by decide) (by decide), s2.1, p25]
    · rw [a2 97 (by decide) (by decide), s2.2.1, p26]
    · rw [a2 98 (by decide) (by decide), s2.2.2.1, p27]
    · rw [a2 99 (by decide) (by decide), s2.2.2.2.1, p28]
    · rw [a2 100 (by decide) (by decide), s2.2.2.2.2.1, p29]
    · rw [a2 101 (by decide) (by decide), s2.2.2.2.2.2.1, p30]
    · rw [a2 102 (by decide) (by decide), s2.2.2.2.2.2.2.1, p31]
    · rw [a2 103 (by decide) (by decide), s2.2.2.2.2.2.2.2.1, p32]
    · rw [a2 104 (by decide) (by decide), s2.2.2.2.2.2.2.2.2, p33]
    · rw [a3 105 (by decide), s3.2.2.2.2.1, p34]
    · rw [a3 106 (by decide), s3.2.2.2.2.2.1, p35]
    · rw [a3 107 (by decide), s3.2.2.2.2.2.2.1, p36]
    · rw [a3 113 (by decide), s3.2.2.2.2.2.2.2, p37]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [a0 0 (by decide), s0.1]; dsimp only [w0]; rw [List.getElem?_take_of_lt (by decide)]
    · rw [a0 1 (by decide), s0.2.1]; dsimp only [w0]; rw [List.getElem?_take_of_lt (by decide)]
    · rw [a0 11 (by decide), s0.2.2.1]; dsimp only [w0]; rw [List.getElem?_take_of_lt (by decide)]
    · rw [a0 12 (by decide), s0.2.2.2.1]; dsimp only [w0]; rw [List.getElem?_take_of_lt (by decide)]
    · rw [a1 49 (by decide) (by decide), s1.1, drop_take_getElem? ws 35 35 14 (by decide)]
    · rw [a1 51 (by decide) (by decide), s1.2.1, drop_take_getElem? ws 35 35 16 (by decide)]
    · rw [a1 52 (by decide) (by decide), s1.2.2.1, drop_take_getElem? ws 35 35 17 (by decide)]
    · rw [a3 108 (by decide), s3.1, drop_take_getElem? ws 105 35 3 (by decide)]
    · rw [a3 109 (by decide), s3.2.1, drop_take_getElem? ws 105 35 4 (by decide)]
    · rw [a3 111 (by decide), s3.2.2.1, drop_take_getElem? ws 105 35 6 (by decide)]
    · rw [a3 112 (by decide), s3.2.2.2.1, drop_take_getElem? ws 105 35 7 (by decide)]

private def fullInitHdr4Spec : Spec [i64, i64, i64, i64] [] :=
  fun (h, mv, max_v, fuel, ()) m Q _ =>
    ∃ (w0 w1 w2 w3 : List (BitVec 64)) (R : Mem 64 → Prop),
      mv.toNat ≤ max_v.toNat ∧ max_v.toNat < 2 * dimacsBound ∧
      (hdrTail4 h w0 w1 w2 w3 ⋆ R) m ∧
      ∀ m',
        (hdrTail4 h (hdrW0 mv.toNat fuel w0) (hdrW1 w1)
          (hdrW2 mv.toNat max_v.toNat w2) (hdrW3 mv.toNat w3) ⋆ R) m' →
        Q () m'

private theorem full_init_hdr4_wp (Γ : Env) :
    ∀ a m Q X, fullInitHdr4Spec a m Q X → Func.wp Γ full_init_hdr_body a m Q X := by
  rintro ⟨h, mv, max_v, fuel, ⟨⟩⟩ m Q X ⟨w0, w1, w2, w3, R, hle, hmx, hm, hQ⟩
  have hmx' := hmx; unfold dimacsBound at hmx'
  let q0 := if mv.toNat = 0 then 0xFFFFFFFF#64 else 0#64
  let ql := if mv.toNat = 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (mv.toNat - 1)
  have hmv0 : (mv == (0 : BitVec 64)) = decide (mv.toNat = 0) := by
    by_cases hz : mv.toNat = 0
    · have he : mv = 0#64 := BitVec.eq_of_toNat_eq hz; simp [he]
    · have hne : mv ≠ 0#64 := fun h => hz (by simp [h]); simp [hz, hne]
  have hsub_bva : max_v - mv = BitVec.ofNat 64 (max_v.toNat - mv.toNat) := by
    apply BitVec.eq_of_toNat_eq; have := max_v.isLt; have := mv.isLt
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsub_mv1 : mv.toNat ≠ 0 → mv - 1#64 = BitVec.ofNat 64 (mv.toNat - 1) := fun hnz => by
    apply BitVec.eq_of_toNat_eq; have := mv.isLt
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  unfold Func.wp full_init_hdr_body
  fp_head_steps
  refine wp_join_group
    (fun (v : Tup Val [i64]) mqf => v.1 = q0 ∧ mqf = m) ?_ ?_
  · rintro _ ⟨qf, ⟨⟩⟩ mqf ⟨rfl, rfl⟩
    simp only [Blocks.get_here]; fp_head_steps
    refine wp_join_group (fun (v : Tup Val [i64]) mql => v.1 = ql ∧ mql = m) ?_ ?_
    · rintro _ ⟨qlv, ⟨⟩⟩ mql ⟨rfl, rfl⟩
      simp only [Blocks.get_here]; fp_head_steps
      refine wp_join_group (fun (v : Tup Val [i64]) mqsi => v.1 = ql ∧ mqsi = m) ?_ ?_
      · rintro _ ⟨qsi, ⟨⟩⟩ mqsi ⟨rfl, rfl⟩
        simp only [Blocks.get_here]; fp_head_steps
        have hmv_bv : mv = BitVec.ofNat 64 mv.toNat := (bv_ofNat_toNat_eq mv).symm
        have hmx_bv : max_v = BitVec.ofNat 64 max_v.toNat := (bv_ofNat_toNat_eq max_v).symm
        rw [hsub_bva, bv64_shl28_val, bv64_shl24_val] at hm
        unfold hdrW0 hdrW1 hdrW2 hdrW3 at hQ
        rw [bv_ofNat_toNat_eq mv, bv_ofNat_toNat_eq max_v] at hQ
        exact hQ m hm
      · intro J3 hJ3; fp_head_steps; rw [hmv0]
        refine wp_jnz_of (fun ht => ?_) (fun hf => ?_)
        · fp_jnz_t ht; exact hJ3 (_, ()) m ⟨by dsimp [ql]; simp only [ht, ↓reduceIte], rfl⟩
        · fp_jnz_f hf; refine hJ3 (_, ()) m ⟨?_, rfl⟩
          dsimp [ql]; rw [ite_eq_right_iff.mpr (fun h => absurd h hf), hsub_mv1 hf]
    · intro J2 hJ2; fp_head_steps; rw [hmv0]
      refine wp_jnz_of (fun ht => ?_) (fun hf => ?_)
      · fp_jnz_t ht; exact hJ2 (_, ()) m ⟨by dsimp [ql]; simp only [ht, ↓reduceIte], rfl⟩
      · fp_jnz_f hf; refine hJ2 (_, ()) m ⟨?_, rfl⟩
        dsimp [ql]; rw [ite_eq_right_iff.mpr (fun h => absurd h hf), hsub_mv1 hf]
  · intro J1 hJ1; fp_head_steps; rw [hmv0]
    refine wp_jnz_of (fun ht => ?_) (fun hf => ?_)
    · fp_jnz_t ht; exact hJ1 (_, ()) m ⟨by dsimp [q0]; simp only [ht, ↓reduceIte], rfl⟩
    · fp_jnz_f hf; exact hJ1 (_, ()) m ⟨by
        dsimp [q0]; rw [ite_eq_right_iff.mpr (fun h => absurd h hf)], rfl⟩

private def initHdrWitness (c : FullCfg) (fuel : BitVec 64) : FullState :=
  { core :=
      { d_cur := 0#64, d_val := 0#64, cur_vars := c.mv, unassigned := BitVec.ofNat 64 c.mv
        arena_len := 0, wlen := 1, wusable := 0#64, arena_garbage := 0#64
        first_reducible := 0xFFFFFFFF#64, num_irred := 0#64, num_redundant := 0#64,
        num_binary := 0#64
        unflushed := 0#64, probing := 0#64, trail_end := 0, propagated := 0, cur_level := 0
        fuel := fuel, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64, confl_lit0 := 0#64
        confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0, min_clr_len := 0, min_clr_full := 0#64
        oom := 0#64, dense_mode := 0#64, inconsistent := 0#64
        vals := [], lit_mark := [], mrk := [], flags := [], lvl := [], rsns := [], trl := []
        trail_pos := [], tmp := [], min_clr := [], frame_trail := [], frame_dec := [], wvec := []
        repr := [], min_stk := [], arena := [], wstk := [] }
    scratch :=
      { heap_len := c.mv, scinc := 1#64 <<< 28, rel_period := 1024#64
        rel_limit := 1048576#64, rel_wait := 1024#64, rel_u := 1#64, rel_v := 1#64
        rel_trigger := 0#64, conflicts := 0#64, learned_lits := 0#64, min_removed := 0#64
        delayed_len := 0, stable := 0#64, switched := 0#64, mode_count := 0#64
        mode_confl_lim := 1000#64, mode_tick_lim := 0#64, mode_saved_ticks := 0#64
        search_ticks := 0#64
        q_first := if c.mv = 0 then 0xFFFFFFFF#64 else 0#64
        q_last := if c.mv = 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (c.mv - 1)
        q_search_idx := if c.mv = 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (c.mv - 1)
        q_search_stamp := BitVec.ofNat 64 c.mv, q_cur_stamp := BitVec.ofNat 64 c.mv
        target_assigned := 0#64, best_assigned := 0#64, rephase_limit := 1000#64
        rephased := 0#64, reduce_limit := 1000#64, reductions := 0#64, tier1 := 2#64
        tier2 := 6#64, restarts := 0#64, restart_limit := 1#64, ema_fast_biased := 0#64
        ema_fast_exp := 1#64 <<< 24, ema_slow_biased := 0#64, ema_slow_exp := 1#64 <<< 24
        extend_len := 0, rng_state := 0x9E3779B97F4A7C15#64 ^^^ (BitVec.ofNat 64 c.mv + 1#64)
        chrono_levels := 100#64, otfs_cnt := 0#64, eager_sub_cnt := 0#64, probe_limit := 500#64
        probings := 0#64, elim_limit := 1500#64, eliminations := 0#64, elim_bound := 0#64
        iterating := 0#64, hbr_cnt := 0#64, trans_cnt := 0#64, viv_cnt := 0#64, subst_cnt := 0#64
        cong_cnt := 0#64, sweep_cnt := 0#64, bve_cnt := 0#64, bce_cnt := 0#64, bva_cnt := 0#64
        walk_cnt_stat := 0#64, fwd_sub_cnt := 0#64, fwd_str_cnt := 0#64, ant_sz := 0#64
        res_sz := 0#64, walk_vals := [], phases := [], phases_target := [], phases_best := []
        walk_best := [], heap := [], pos := [], shrink_stk := [], q_prev := [], q_next := []
        q_stamp := [], wsort := [], work_stk1 := [], work_stk2 := [], tarjan_mark := []
        tarjan_reach := [], score := [], sim_sig := [], glue_used := [], last_learned := []
        delayed := [], red_refs := [], extend_stk := [], scratch_buf := [] } }

private theorem hdrW0_eq (c : FullCfg) (fuel : BitVec 64) (w0 : List (BitVec 64))
    (h0 : w0.length = 35)
    (hw : ∀ i ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29],
      w0[i]? = (hdrTailWords0 c (initHdrWitness c fuel))[i]?) :
    hdrW0 c.mv fuel w0 = hdrTailWords0 c (initHdrWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35 w0 h0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e0 := hw 0 (by simp); have e1 := hw 1 (by simp); have e4 := hw 4 (by simp)
  have e5 := hw 5 (by simp); have e6 := hw 6 (by simp); have e7 := hw 7 (by simp)
  have e8 := hw 8 (by simp); have e9 := hw 9 (by simp); have e10 := hw 10 (by simp)
  have e11 := hw 11 (by simp); have e12 := hw 12 (by simp); have e13 := hw 13 (by simp)
  have e21 := hw 21 (by simp); have e22 := hw 22 (by simp); have e23 := hw 23 (by simp)
  have e24 := hw 24 (by simp); have e25 := hw 25 (by simp); have e26 := hw 26 (by simp)
  have e29 := hw 29 (by simp)
  simp only [hdrTailWords0, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
    at e0 e1 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e21 e22 e23 e24 e25 e26 e29
  simp [hdrW0, hdrTailWords0, initHdrWitness, e0, e1, e4, e5, e6, e7, e8, e9, e10, e11, e12,
    e13, e21, e22, e23, e24, e25, e26, e29]

private theorem hdrW1_eq (c : FullCfg) (fuel : BitVec 64) (w1 : List (BitVec 64))
    (h1 : w1.length = 35)
    (hw : ∀ i ∈ [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
      w1[i]? = (hdrTailWords1 c (initHdrWitness c fuel))[i]?) :
    hdrW1 w1 = hdrTailWords1 c (initHdrWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35 w1 h1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e6 := hw 6 (by simp); have e7 := hw 7 (by simp); have e8 := hw 8 (by simp)
  have e9 := hw 9 (by simp); have e10 := hw 10 (by simp); have e11 := hw 11 (by simp)
  have e12 := hw 12 (by simp); have e13 := hw 13 (by simp); have e14 := hw 14 (by simp)
  have e15 := hw 15 (by simp); have e16 := hw 16 (by simp); have e17 := hw 17 (by simp)
  simp only [hdrTailWords1, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
    at e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
  simp [hdrW1, hdrTailWords1, initHdrWitness, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15,
    e16, e17]

private theorem hdrW2_eq (c : FullCfg) (fuel : BitVec 64) (w2 : List (BitVec 64))
    (h2 : w2.length = 35)
    (hw : ∀ i ∈ [26, 27, 28, 29, 30, 31, 32, 33, 34],
      w2[i]? = (hdrTailWords2 c (initHdrWitness c fuel))[i]?) :
    hdrW2 c.mv c.max_vars w2 = hdrTailWords2 c (initHdrWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35 w2 h2
  have hbva : c.max_vars - c.mv = c.bva_cap := by have := c.hbva; omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e26 := hw 26 (by simp); have e27 := hw 27 (by simp); have e28 := hw 28 (by simp)
  have e29 := hw 29 (by simp); have e30 := hw 30 (by simp); have e31 := hw 31 (by simp)
  have e32 := hw 32 (by simp); have e33 := hw 33 (by simp); have e34 := hw 34 (by simp)
  simp only [hdrTailWords2, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
    at e26 e27 e28 e29 e30 e31 e32 e33 e34
  simp [hdrW2, hdrTailWords2, initHdrWitness, hbva, e26, e27, e28, e29, e30, e31, e32, e33, e34]

private theorem hdrW3_eq (c : FullCfg) (fuel : BitVec 64) (w3 : List (BitVec 64))
    (h3 : w3.length = 35)
    (hw : ∀ i ∈ [0, 1, 2, 3, 4, 6, 7, 8],
      w3[i]? = (hdrTailWords3 c (initHdrWitness c fuel))[i]?) :
    hdrW3 c.mv w3 = hdrTailWords3 c (initHdrWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35 w3 h3
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e0 := hw 0 (by simp); have e1 := hw 1 (by simp); have e2 := hw 2 (by simp)
  have e3 := hw 3 (by simp); have e4 := hw 4 (by simp); have e6 := hw 6 (by simp)
  have e7 := hw 7 (by simp); have e8 := hw 8 (by simp)
  simp only [hdrTailWords3, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
    at e0 e1 e2 e3 e4 e6 e7 e8
  simp [hdrW3, hdrTailWords3, initHdrWitness, e0, e1, e2, e3, e4, e6, e7, e8]

theorem full_init_hdr_wp (Γ : Env) :
    ∀ a m Q X, fullInitHdrSpec a m Q X → Func.wp Γ full_init_hdr_body a m Q X := by
  rintro ⟨h, mv, max_v, fuel, ⟨⟩⟩ m Q X ⟨c, ws, R, rfl, rfl, rfl, hw, hws, hm, hQ⟩
  let s0 := initHdrWitness c fuel
  have hws0 := hws s0
  have hmv' := c.hmv; have hmx' := c.hmaxv; unfold dimacsBound at hmv' hmx'
  have hmv_to : (BitVec.ofNat 64 c.mv).toNat = c.mv := bv64_ofNat_toNat (by omega)
  have hmx_to : (BitVec.ofNat 64 c.max_vars).toNat = c.max_vars := bv64_ofNat_toNat (by omega)
  let w0 := ws.take 35; let w1 := (ws.drop 35).take 35
  let w2 := (ws.drop 70).take 35; let w3 := (ws.drop 105).take 35
  have h0l : w0.length = 35 := by simp [w0, hw]
  have h1l : w1.length = 35 := by simp [w1, hw]
  have h2l : w2.length = 35 := by simp [w2, hw]
  have h3l : w3.length = 35 := by simp [w3, hw]
  have hw_len0 : (hdrTailWords0 c s0).length = 35 := by simp [hdrTailWords0]
  have hw_len1 : (hdrTailWords1 c s0).length = 35 := by simp [hdrTailWords1]
  have hw_len2 : (hdrTailWords2 c s0).length = 35 := by simp [hdrTailWords2]
  refine full_init_hdr4_wp Γ _ m Q X
    ⟨w0, w1, w2, w3, R, by rw [hmv_to, hmx_to]; have := c.hbva; omega,
      by rw [hmx_to]; exact c.hmaxv, array64_to_hdrTail4 hw hm, fun m' hm' => ?_⟩
  rw [hmv_to, hmx_to] at hm'
  have hm_arr : (array64 (c.hdr + 32) (hdrW0 c.mv fuel w0 ++ hdrW1 w1 ++
      hdrW2 c.mv c.max_vars w2 ++ hdrW3 c.mv w3) ⋆ R) m' := by
    rwa [hdrTail4_eq_array64 (by simp [h0l]) (by simp [h1l]) (by simp [h2l]) (by simp [h3l])]
      at hm'
  have hi0 : ∀ j ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29],
      j < 35 ∧ j ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have hi1 : ∀ j ∈ [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
      j < 35 ∧ (35 + j) ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have hi2 : ∀ j ∈ [26, 27, 28, 29, 30, 31, 32, 33, 34],
      j < 35 ∧ (70 + j) ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have hi3 : ∀ j ∈ [0, 1, 2, 3, 4, 6, 7, 8],
      j < 35 ∧ (105 + j) ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have heq0 : hdrW0 c.mv fuel w0 = hdrTailWords0 c s0 := hdrW0_eq c fuel w0 h0l fun i hi => by
    have ⟨hi', hm'⟩ := hi0 i hi
    have hgi := hws0 i hm'
    dsimp only [w0]; rw [List.getElem?_take_of_lt hi', hgi]
    unfold hdrTailWords; exact append4_getElem?_0 hw_len0 hi'
  have heq1 : hdrW1 w1 = hdrTailWords1 c s0 := hdrW1_eq c fuel w1 h1l fun i hi => by
    have ⟨hi35, hm'⟩ := hi1 i hi
    have hgi := hws0 (35 + i) hm'
    dsimp only [w1]; rw [drop_take_getElem? ws 35 35 i hi35, hgi]
    unfold hdrTailWords
    rw [append4_getElem?_1 hw_len0 hw_len1 (by omega) (by omega), show 35 + i - 35 = i by omega]
  have heq2 : hdrW2 c.mv c.max_vars w2 = hdrTailWords2 c s0 :=
    hdrW2_eq c fuel w2 h2l fun i hi => by
      have ⟨hi35, hm'⟩ := hi2 i hi
      have hgi := hws0 (70 + i) hm'
      dsimp only [w2]; rw [drop_take_getElem? ws 70 35 i hi35, hgi]
      unfold hdrTailWords
      rw [append4_getElem?_2 hw_len0 hw_len1 hw_len2 (by omega) (by omega),
        show 70 + i - 70 = i by omega]
  have heq3 : hdrW3 c.mv w3 = hdrTailWords3 c s0 := hdrW3_eq c fuel w3 h3l fun i hi => by
    have ⟨hi35, hm'⟩ := hi3 i hi
    have hgi := hws0 (105 + i) hm'
    dsimp only [w3]; rw [drop_take_getElem? ws 105 35 i hi35, hgi]
    unfold hdrTailWords
    rw [append4_getElem?_3 hw_len0 hw_len1 hw_len2 (by omega), show 105 + i - 105 = i by omega]
  rw [heq0, heq1, heq2, heq3] at hm_arr
  change (array64 (c.hdr + 32) (hdrTailWords c s0) ⋆ R) m' at hm_arr
  exact hQ s0 m' rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hm_arr

private def ptrs_dummy_cfg {hdr_addr : BitVec 64} {max_v : Nat}
    (hmx : max_v < 2 * dimacsBound) (hfit : hdr_addr.toNat + fullFixedBytes max_v < 2 ^ 64) :
    FullCfg :=
  { hdr := hdr_addr, avail := fullFixedBytes max_v, mv := 0, max_vars := max_v, bva_cap := max_v
    nc := 0, arena_cap := 0, wcap := 0, delayed_cap := 0, red_cap := 0, extend_cap := 0
    scratch_cap := 0, hbva := by omega, hmv := by unfold dimacsBound; omega, hmaxv := hmx
    hnc := by unfold dimacsBound; omega, harena := by unfold dimacsBound; omega
    hwcap := by unfold dimacsBound; omega, hdel := by unfold dimacsBound; omega
    hred := by unfold dimacsBound; omega, hext := by unfold dimacsBound; omega
    hscr := by unfold dimacsBound; omega, havail_fit := hfit, hsize := Nat.le_refl _ }

private theorem aw0_pres (w0 : List (BitVec 64)) (v11 v12 v0 v1 : BitVec 64)
    {i : Nat} (h : i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 11 ∧ i ≠ 12) :
    ((((w0.set 11 v11).set 12 v12).set 0 v0).set 1 v1)[i]? = w0[i]? := by
  simp only [List.getElem?_set_ne (Ne.symm h.2.1), List.getElem?_set_ne (Ne.symm h.1),
    List.getElem?_set_ne (Ne.symm h.2.2.2), List.getElem?_set_ne (Ne.symm h.2.2.1)]

private theorem aw1_pres (w1 : List (BitVec 64)) (v14 v16 : BitVec 64)
    {i : Nat} (h : i ≠ 14 ∧ i ≠ 16) :
    ((w1.set 14 v14).set 16 v16)[i]? = w1[i]? := by
  simp only [List.getElem?_set_ne (Ne.symm h.2), List.getElem?_set_ne (Ne.symm h.1)]

private theorem aw3_pres (w3 : List (BitVec 64)) (v3 v6 : BitVec 64)
    {i : Nat} (h : i ≠ 3 ∧ i ≠ 6) :
    ((w3.set 3 v3).set 6 v6)[i]? = w3[i]? := by
  simp only [List.getElem?_set_ne (Ne.symm h.2), List.getElem?_set_ne (Ne.symm h.1)]

theorem full_init_arenas_wp (Γ : Env)
    (hPtrs : ∀ a m Q X, fullInitPtrsSpec a m Q X →
      Γ "full_init_ptrs" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullInitArenasSpec a m Q X → Func.wp Γ full_init_arenas_body a m Q X := by
  rintro ⟨h, hdr_addr, max_v, adyn, ⟨⟩⟩ m Q X
    ⟨ws, dcap, ecap, scap, R, hhdr, hw, hmx, hdel, hext, hscr, h52, h109, h112, hfit, hm, hQ⟩
  rw [hhdr]; clear hhdr h
  have hmx' := hmx; have hdel' := hdel; have hext' := hext; have hscr' := hscr
  unfold dimacsBound at hmx' hdel' hext' hscr'
  have hadyn := adyn.isLt
  have htp_lt : adyn.toNat / 8 < 2 ^ 61 := by omega
  have hap3_lt : ((adyn.toNat / 8) * 3) < 2 ^ 64 := by omega
  let ap := fullInitAp adyn.toNat
  let rp := fullInitRp adyn.toNat
  let wp_c := fullInitWp adyn.toNat
  have hap_lt : ap ≤ 134217727 := by dsimp [ap]; unfold fullInitAp; omega
  have hrp_lt : rp ≤ 22369622 := by dsimp [rp]; unfold fullInitRp; omega
  have hwp_lt : wp_c ≤ 134217727 := by dsimp [wp_c]; unfold fullInitWp; omega
  have hap_rp := fullInitAp_add_rp_le adyn.toNat
  let w0 := ws.take 35; let w1 := (ws.drop 35).take 35
  let w2 := (ws.drop 70).take 35; let w3 := (ws.drop 105).take 35
  have hm4 : (hdrTail4 hdr_addr w0 w1 w2 w3 ⋆ R) m := array64_to_hdrTail4 hw hm
  have hdel_at : w1[((448 : BitVec 64).toNat - 312) / 8]?.getD 0#64 = BitVec.ofNat 64 dcap := by
    dsimp only [w1]
    rw [show ((448 : BitVec 64).toNat - 312) / 8 = 17 from rfl,
      drop_take_getElem? ws 35 35 17 (by decide), h52]; rfl
  have hext_at : w3[((904 : BitVec 64).toNat - 872) / 8]?.getD 0#64 = BitVec.ofNat 64 ecap := by
    dsimp only [w3]
    rw [show ((904 : BitVec 64).toNat - 872) / 8 = 4 from rfl,
      drop_take_getElem? ws 105 35 4 (by decide), h109]; rfl
  unfold Func.wp full_init_arenas_body
  fp_head_steps
  clear hm4
  rw [hdel_at, hext_at, fp_shr3_bv adyn]
  have hap3 : BitVec.ofNat 64 (adyn.toNat / 8) * (3 : BitVec 64) =
      BitVec.ofNat 64 ((adyn.toNat / 8) * 3) := by
    rw [show (3 : BitVec 64) = BitVec.ofNat 64 3 from rfl, fp_mul_nat]
  rw [hap3]
  apply wp_udiv_of
  · dsimp only [Arg.val_imm]; decide
  · dsimp only [Arg.val_var, Arg.val_imm]
    have hap_div : BitVec.ofNat 64 ((adyn.toNat / 8) * 3) / (5 : BitVec 64) =
        BitVec.ofNat 64 (((adyn.toNat / 8) * 3) / 5) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_udiv, Nat.mod_eq_of_lt hap3_lt,
        Nat.mod_eq_of_lt (show ((adyn.toNat / 8) * 3) / 5 < 2 ^ 64 by omega)]
    rw [hap_div]
    refine wp_join_group
      (fun (v : Tup Val [i64]) ma => v.1 = BitVec.ofNat 64 ap ∧ ma = m) ?_ ?_
    · rintro _ ⟨ap_v, ⟨⟩⟩ ma ⟨rfl, hma⟩
      subst ma
      simp only [Blocks.get_here]; fp_head_steps
      have hap5 : BitVec.ofNat 64 ap + (5 : BitVec 64) = BitVec.ofNat 64 (ap + 5) := by
        rw [show (5 : BitVec 64) = BitVec.ofNat 64 5 from rfl, bv_add_ofNat]
      rw [hap5]
      apply wp_udiv_of
      · dsimp only [Arg.val_imm]; decide
      · dsimp only [Arg.val_var, Arg.val_imm]
        have hrp_div : BitVec.ofNat 64 (ap + 5) / (6 : BitVec 64) = BitVec.ofNat 64 rp := by
          apply BitVec.eq_of_toNat_eq
          simp [rp, fullInitRp, ap, BitVec.toNat_udiv,
            Nat.mod_eq_of_lt (show ap + 5 < 2 ^ 64 by omega),
            Nat.mod_eq_of_lt (show (ap + 5) / 6 < 2 ^ 64 by omega)]
        rw [hrp_div]
        have hsub_wp : BitVec.ofNat 64 (adyn.toNat / 8) -
            BitVec.ofNat 64 ap - BitVec.ofNat 64 rp =
            BitVec.ofNat 64 (adyn.toNat / 8 - ap - rp) := by
          rw [bv_sub_ofNat (by omega) (by omega), bv_sub_ofNat (by omega) (by omega)]
        fp_head_steps; rw [hsub_wp]
        refine wp_join_group
          (fun (v : Tup Val [i64]) mw => v.1 = BitVec.ofNat 64 wp_c ∧ mw = m) ?_ ?_
        · rintro _ ⟨wp_v, ⟨⟩⟩ mw ⟨rfl, hmw⟩
          subst mw
          simp only [Blocks.get_here]
          apply wp_call_of_spec; apply hPtrs
          change fullInitPtrsSpec (hdr_addr, hdr_addr, max_v, ()) m _ _
          refine ⟨ws, R, rfl, hw, hmx, by omega, hm, fun ws' m0 hw' hptrs hpres hm0 => ?_⟩
          let c0 := ptrs_dummy_cfg (hdr_addr := hdr_addr) hmx (by omega)
          have h0c := hptrs c0 rfl rfl
          have har_ws' : ws'[10]? = some (fullPArena hdr_addr max_v.toNat) := by
            have := h0c.2.2.2.2.2.2.1; exact this
          have hm0' := array64_to_hdrTail4 hw' hm0
          clear hm m hm0
          dsimp only [Arg.val_var] at hm0' ⊢
          let w0' := ws'.take 35; let w1' := (ws'.drop 35).take 35
          let w2' := (ws'.drop 70).take 35; let w3' := (ws'.drop 105).take 35
          have h0l : w0'.length = 35 := by simp [w0', hw']
          have h1l : w1'.length = 35 := by simp [w1', hw']
          have h2l : w2'.length = 35 := by simp [w2', hw']
          have h3l : w3'.length = 35 := by simp [w3', hw']
          have har_get : w0'[((112 : BitVec 64).toNat - 32) / 8]?.getD 0#64 =
              fullPArena hdr_addr max_v.toNat := by
            dsimp only [w0']
            rw [show ((112 : BitVec 64).toNat - 32) / 8 = 10 from rfl,
              List.getElem?_take_of_lt (by decide), har_ws']; rfl
          fp_head_steps
          have h52' : ws'[52]? = some (BitVec.ofNat 64 dcap) :=
            (hpres 52 (by decide)).trans h52
          have h109' : ws'[109]? = some (BitVec.ofNat 64 ecap) :=
            (hpres 109 (by decide)).trans h109
          have h112' : ws'[112]? = some (BitVec.ofNat 64 scap) :=
            (hpres 112 (by decide)).trans h112
          have hdel_mul : BitVec.ofNat 64 dcap * (12 : BitVec 64) =
              BitVec.ofNat 64 (12 * dcap) := by
            rw [show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl, fp_mul_nat, Nat.mul_comm]
          have hshl3_a : BitVec.ofNat 64 ap <<< (((3 : BitVec 32).signExtend 64).toNat % 64) =
              BitVec.ofNat 64 (8 * ap) := fp_shl_sext3
          have hshl3_w : BitVec.ofNat 64 wp_c <<< (((3 : BitVec 32).signExtend 64).toNat % 64) =
              BitVec.ofNat 64 (8 * wp_c) := fp_shl_sext3
          have hshl3_r : BitVec.ofNat 64 rp <<< (((3 : BitVec 32).signExtend 64).toNat % 64) =
              BitVec.ofNat 64 (8 * rp) := fp_shl_sext3
          have hshl2_e : BitVec.ofNat 64 ecap <<< (((2 : BitVec 32).signExtend 64).toNat % 64) =
              BitVec.ofNat 64 (4 * ecap) := Kissat.bv_shl_sext2
          have hshl1_a : BitVec.ofNat 64 ap <<< (((1 : BitVec 32).signExtend 64).toNat % 64) =
              BitVec.ofNat 64 (2 * ap) := Kissat.bv_shl_sext1
          have hshl1_w : BitVec.ofNat 64 wp_c <<< (((1 : BitVec 32).signExtend 64).toNat % 64) =
              BitVec.ofNat 64 (2 * wp_c) := Kissat.bv_shl_sext1
          have hshl1_r : BitVec.ofNat 64 rp <<< (((1 : BitVec 32).signExtend 64).toNat % 64) =
              BitVec.ofNat 64 (2 * rp) := Kissat.bv_shl_sext1
          rw [har_get, hdel_mul, hshl3_a, hshl3_w, hshl3_r, hshl2_e,
            hshl1_a, hshl1_w, hshl1_r] at hm
          let pWstk_v := fullPArena hdr_addr max_v.toNat + BitVec.ofNat 64 (8 * ap)
          let pDel_v := pWstk_v + BitVec.ofNat 64 (8 * wp_c)
          let pRed_v := pDel_v + BitVec.ofNat 64 (12 * dcap)
          let pExt_v := pRed_v + BitVec.ofNat 64 (8 * rp)
          let pScr_v := pExt_v + BitVec.ofNat 64 (4 * ecap)
          let aw0 := (((w0'.set 11 pWstk_v).set 12 pDel_v).set 0 (BitVec.ofNat 64 (2 * ap))).set 1
            (BitVec.ofNat 64 (2 * wp_c))
          let aw1 := (w1'.set 14 pRed_v).set 16 (BitVec.ofNat 64 (2 * rp))
          let aw3 := (w3'.set 3 pExt_v).set 6 pScr_v
          have haw0_len : aw0.length = 35 := by simp [aw0, h0l]
          have haw1_len : aw1.length = 35 := by simp [aw1, h1l]
          have haw3_len : aw3.length = 35 := by simp [aw3, h3l]
          let ws'' := aw0 ++ aw1 ++ w2' ++ aw3
          have hws''_len : ws''.length = 140 := by simp [ws'', haw0_len, haw1_len, h2l, haw3_len]
          have hm_arr : (array64 (hdr_addr + 32) ws'' ⋆ R) m := by
            rwa [hdrTail4_eq_array64 haw0_len haw1_len h2l haw3_len] at hm
          have hbd_a : 2 * ap < 2 * dimacsBound := fullInitAp_lt
          have hbd_w : 2 * wp_c < 2 * dimacsBound := fullInitWp_lt
          have hbd_r : 2 * rp < 2 * dimacsBound := fullInitRp_lt
          have hsum : 4 * (2 * ap) + 4 * (2 * wp_c) + 4 * (2 * rp) ≤ adyn.toNat := by
            dsimp [ap, rp, wp_c]; unfold fullInitWp; omega
          have hwpos : 40 ≤ adyn.toNat → 1 ≤ 2 * wp_c := fun h40 => by
            dsimp [wp_c]; unfold fullInitWp fullInitRp fullInitAp; omega
          refine hQ (2 * ap) (2 * wp_c) (2 * rp) ws'' m hws''_len hbd_a hbd_w hbd_r hsum hwpos
            (fun c hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 => ?_) hm_arr
          have hcpt := hptrs c hc1 hc2
          have ga0 := fun i (hi : i < 35) =>
            append4_getElem?_0 (w1 := aw1) (w2 := w2') (w3 := aw3) haw0_len hi
          have ga1 := fun i (hi0 : 35 ≤ i) (hi1 : i < 70) =>
            append4_getElem?_1 (w2 := w2') (w3 := aw3) haw0_len haw1_len hi0 hi1
          have ga2 := fun i (hi0 : 70 ≤ i) (hi1 : i < 105) =>
            append4_getElem?_2 (w3 := aw3) haw0_len haw1_len h2l hi0 hi1
          have ga3 := fun i (hi0 : 105 ≤ i) =>
            append4_getElem?_3 (w3 := aw3) haw0_len haw1_len h2l hi0
          have pr0 : ∀ i, i < 35 → i ≠ 0 → i ≠ 1 → i ≠ 11 → i ≠ 12 → ws''[i]? = ws'[i]? :=
            fun i hi h0n h1n h11n h12n => by
              rw [ga0 i hi, aw0_pres w0' _ _ _ _ ⟨h0n, h1n, h11n, h12n⟩]
              dsimp only [w0']; rw [List.getElem?_take_of_lt hi]
          have pr1 : ∀ i, 35 ≤ i → i < 70 → i ≠ 49 → i ≠ 51 → ws''[i]? = ws'[i]? :=
            fun i hi0 hi1 h49n h51n => by
              rw [ga1 i hi0 hi1, aw1_pres w1' _ _ ⟨by omega, by omega⟩,
                drop_take_getElem? ws' 35 35 (i - 35) (by omega),
                show 35 + (i - 35) = i by omega]
          have pr2 : ∀ i, 70 ≤ i → i < 105 → ws''[i]? = ws'[i]? := fun i hi0 hi1 => by
            rw [ga2 i hi0 hi1, drop_take_getElem? ws' 70 35 (i - 70) (by omega),
              show 70 + (i - 70) = i by omega]
          have pr3 : ∀ i, 105 ≤ i → i < 140 → i ≠ 108 → i ≠ 111 → ws''[i]? = ws'[i]? :=
            fun i hi0 hi1 h108n h111n => by
              rw [ga3 i hi0, aw3_pres w3' _ _ ⟨by omega, by omega⟩,
                drop_take_getElem? ws' 105 35 (i - 105) (by omega),
                show 105 + (i - 105) = i by omega]
          have hp_a : c.pArena = fullPArena hdr_addr max_v.toNat :=
            Option.some.inj (hcpt.2.2.2.2.2.2.1.symm.trans har_ws')
          have hp_w : c.pWstk = pWstk_v := by
            unfold FullCfg.pWstk; rw [hp_a, hc3, show 4 * (2 * ap) = 8 * ap by omega]
          have hp_d : c.pDelayed = pDel_v := by
            unfold FullCfg.pDelayed; rw [hp_w, hc4, show 4 * (2 * wp_c) = 8 * wp_c by omega]
          have hp_r : c.pRedRefs = pRed_v := by
            unfold FullCfg.pRedRefs; rw [hp_d, hc5]
          have hp_e : c.pExtendStk = pExt_v := by
            unfold FullCfg.pExtendStk; rw [hp_r, hc6, show 4 * (2 * rp) = 8 * rp by omega]
          have hp_s : c.pScratchBuf = pScr_v := by
            unfold FullCfg.pScratchBuf; rw [hp_e, hc7]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [ga0 0 (by decide)]; dsimp [aw0]
            rw [List.getElem?_set_ne (by decide), List.getElem?_set_self, hc3]; simp [h0l]
          · rw [ga0 1 (by decide)]; dsimp [aw0]
            rw [List.getElem?_set_self, hc4]; simp [h0l]
          · rw [pr0 4 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hcpt.1
          · rw [pr0 5 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hcpt.2.1
          · rw [pr0 6 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hcpt.2.2.1
          · rw [pr0 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.1
          · rw [pr0 8 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.1
          · rw [pr0 9 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.1
          · rw [pr0 10 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.1
          · rw [ga0 11 (by decide)]; dsimp [aw0]
            rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
              List.getElem?_set_ne (by decide), List.getElem?_set_self, hp_w]; simp [h0l]
          · rw [ga0 12 (by decide)]; dsimp [aw0]
            rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
              List.getElem?_set_self, hp_d]; simp [h0l]
          · rw [pr0 13 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.1
          · rw [pr0 21 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.1
          · rw [pr0 22 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.1
          · rw [pr0 23 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr0 24 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr0 25 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr0 26 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr0 29 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr1 41 (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr1 42 (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr1 43 (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr1 44 (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr1 45 (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr1 46 (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr1 47 (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr1 48 (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [ga1 49 (by decide) (by decide)]; dsimp [aw1]
            rw [List.getElem?_set_ne (by decide), List.getElem?_set_self, hp_r]; simp [h1l]
          · rw [pr1 50 (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [ga1 51 (by decide) (by decide)]; dsimp [aw1]
            rw [List.getElem?_set_self, hc6]; simp [h1l]
          · rw [pr1 52 (by decide) (by decide) (by decide) (by decide), h52', hc5]
          · rw [pr2 96 (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr2 97 (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr2 98 (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr2 99 (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr2 100 (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr2 101 (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr2 102 (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr2 103 (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr2 104 (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr3 105 (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr3 106 (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [pr3 107 (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · rw [ga3 108 (by decide)]; dsimp [aw3]
            rw [List.getElem?_set_ne (by decide), List.getElem?_set_self, hp_e]; simp [h3l]
          · rw [pr3 109 (by decide) (by decide) (by decide) (by decide), h109', hc7]
          · rw [ga3 111 (by decide)]; dsimp [aw3]
            rw [List.getElem?_set_self, hp_s]; simp [h3l]
          · rw [pr3 112 (by decide) (by decide) (by decide) (by decide), h112', hc8]
          · rw [pr3 113 (by decide) (by decide) (by decide) (by decide)]
            exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        · intro Jw hJw; fp_head_steps
          rw [show (134217727 : BitVec 64) = BitVec.ofNat 64 134217727 from rfl,
            bv_ult_eq (by decide) (by omega)]
          refine wp_jnz_of (fun hwgt => ?_) (fun hwle => ?_)
          · fp_jnz_t hwgt; refine hJw (_, ()) m ⟨?_, rfl⟩
            simp [wp_c, fullInitWp]; rw [Nat.min_eq_right (by omega)] <;> rfl
          · fp_jnz_f hwle; refine hJw (_, ()) m ⟨?_, rfl⟩
            simp [wp_c, fullInitWp]; rw [Nat.min_eq_left (by omega)]
    · intro Ja hJa; fp_head_steps
      rw [show (134217727 : BitVec 64) = BitVec.ofNat 64 134217727 from rfl,
        bv_ult_eq (by decide) (by omega)]
      refine wp_jnz_of (fun hagt => ?_) (fun hale => ?_)
      · fp_jnz_t hagt; refine hJa (_, ()) m ⟨?_, rfl⟩
        simp [ap, fullInitAp]; rw [Nat.min_eq_right (by omega)] <;> rfl
      · fp_jnz_f hale; refine hJa (_, ()) m ⟨?_, rfl⟩
        simp [ap, fullInitAp]; rw [Nat.min_eq_left (by omega)]

end LeanQbe.T.Examples.Kissat.Full
