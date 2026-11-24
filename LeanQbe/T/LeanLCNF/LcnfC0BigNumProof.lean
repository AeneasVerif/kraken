module

public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof1
public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof2
public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof3
public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof4
public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof5
public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof6
public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof7
public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof8
import all Kraken.Mem
import all Kraken.Separation

/-!
# Top-Level `LcnfC0BigNum` `ModuleOk`, Soundness & Concrete `Mem 64` Non-Vacuity (`Milestone R1`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open BigNumRt

local macro "sep_ac" : tactic =>
  `(tactic| exact sep_cast_ac (by assumption) (by ac_rfl))

local macro "sep_use " t:term : tactic =>
  `(tactic| exact sep_cast_ac $t (by ac_rfl))

theorem lcnf_int_op_wp :
    ∀ xs m Q X, lcnfIntOpSpec xs m Q X → Func.wp rtR1Env lcnf_int_op.body xs m Q X := by
  rintro ⟨rt, op, a, b, ⟨⟩⟩ m Q X ⟨st, scr, scrLimbs, objs, R, hwf, hm, hspec⟩
  change wp rtR1Env Q X (lcnf_int_op_body Val Cont (rt, op, a, b, ())) m
  by_cases hop_conv : op.toNat ∈ [1, 2, 3, 9, 13, 16]
  · simp only [hop_conv, ↓reduceIte] at hspec
    refine wp_join_group
      (fun _ m0 => lcnfIntConvSpec (rt, op, a, ()) m0 Q (fun _ _ _ _ => False)) ?_ ?_
    · rintro _ ⟨⟩ m0 hc
      dsimp only [Blocks.get]
      refine wp_mono (fun _ _ h => h) (fun _ _ _ _ h => False.elim h) _ _ ?_
      refine wp_call_ret1 _ _ (fun res m' => Q (res, ()) m') ?_ ?_
      · exact rtR1Env_lcnf_int_conv hc
      · intro r m' hq; rw [wp_ret]; exact hq
    · intro J hJ
      c0_let_simp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop_conv
      have hconv_lt : op.toNat < 2 ^ 64 := op.isLt
      rcases hop_conv with h1 | h2 | h3 | h9 | h13 | h16
      · have heq : (op == 1#64) = true := by
          simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h1)
        refine jnz_true heq ?_; rw [wp_jump]; exact hJ () m hspec
      · have hne1 : (op == 1#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 1); subst h
          decide
        have heq2 : (op == 2#64) = true := by
          simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h2)
        refine jnz_false hne1 ?_; c0_let_simp; refine jnz_true heq2 ?_
        rw [wp_jump]; exact hJ () m hspec
      · have hne1 : (op == 1#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 1); subst h
          decide
        have hne2 : (op == 2#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 2); subst h
          decide
        have heq3 : (op == 3#64) = true := by
          simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h3)
        refine jnz_false hne1 ?_; c0_let_simp; refine jnz_false hne2 ?_; c0_let_simp
        refine jnz_true heq3 ?_; rw [wp_jump]; exact hJ () m hspec
      · have hne1 : (op == 1#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 1); subst h
          decide
        have hne2 : (op == 2#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 2); subst h
          decide
        have hne3 : (op == 3#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 3); subst h
          decide
        have heq9 : (op == 9#64) = true := by
          simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h9)
        refine jnz_false hne1 ?_; c0_let_simp; refine jnz_false hne2 ?_; c0_let_simp
        refine jnz_false hne3 ?_; c0_let_simp; refine jnz_true heq9 ?_; rw [wp_jump]
        exact hJ () m hspec
      · have hne1 : (op == 1#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 1); subst h
          decide
        have hne2 : (op == 2#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 2); subst h
          decide
        have hne3 : (op == 3#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 3); subst h
          decide
        have hne9 : (op == 9#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 9); subst h
          decide
        have heq13 : (op == 13#64) = true := by
          simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h13)
        refine jnz_false hne1 ?_; c0_let_simp; refine jnz_false hne2 ?_; c0_let_simp
        refine jnz_false hne3 ?_; c0_let_simp; refine jnz_false hne9 ?_; c0_let_simp
        refine jnz_true heq13 ?_; rw [wp_jump]; exact hJ () m hspec
      · have hne1 : (op == 1#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 1); subst h
          decide
        have hne2 : (op == 2#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 2); subst h
          decide
        have hne3 : (op == 3#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 3); subst h
          decide
        have hne9 : (op == 9#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 9); subst h
          decide
        have hne13 : (op == 13#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 13); subst h
          decide
        have heq16 : (op == 16#64) = true := by
          simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h16)
        refine jnz_false hne1 ?_; c0_let_simp; refine jnz_false hne2 ?_; c0_let_simp
        refine jnz_false hne3 ?_; c0_let_simp; refine jnz_false hne9 ?_; c0_let_simp
        refine jnz_false hne13 ?_; c0_let_simp; refine jnz_true heq16 ?_; rw [wp_jump]
        exact hJ () m hspec
  · simp only [hop_conv, ↓reduceIte] at hspec
    refine wp_join_group (fun _ _ => False) ?_ ?_
    · intro _ _ _ hF; exact False.elim hF
    · intro _ _
      c0_let_simp
      have hne_c : ∀ k, k ∈ [1, 2, 3, 9, 13, 16] → (op == BitVec.ofNat 64 k) = false := by
        intro k hk
        simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply hop_conv; subst h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      refine jnz_false (hne_c 1 (by decide)) ?_; c0_let_simp
      refine jnz_false (hne_c 2 (by decide)) ?_; c0_let_simp
      refine jnz_false (hne_c 3 (by decide)) ?_; c0_let_simp
      refine jnz_false (hne_c 9 (by decide)) ?_; c0_let_simp
      refine jnz_false (hne_c 13 (by decide)) ?_; c0_let_simp
      refine jnz_false (hne_c 16 (by decide)) ?_
      by_cases hop_as : op.toNat ∈ [4, 5, 10, 11, 12]
      · simp only [hop_as, ↓reduceIte] at hspec
        refine wp_join_group
          (fun _ m0 => lcnfIntAddSubCmpSpec (rt, op, a, b, ()) m0 Q (fun _ _ _ _ => False)) ?_ ?_
        · rintro _ ⟨⟩ m0 hc
          rw [Blocks.get.eq_1]
          refine wp_mono (fun _ _ h => h) (fun _ _ _ _ h => False.elim h) _ _ ?_
          refine wp_call_ret1 _ _ (fun res m' => Q (res, ()) m') ?_ ?_
          · exact rtR1Env_lcnf_int_addsub_cmp hc
          · intro r m' hq; rw [wp_ret]; exact hq
        · intro J hJ
          c0_let_simp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hop_as
          rcases hop_as with h4 | h5 | h10 | h11 | h12
          · have heq4 : (op == 4#64) = true := by
              simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h4)
            refine jnz_true heq4 ?_; rw [wp_jump]; exact hJ () m hspec
          · have hne4 : (op == 4#64) = false := by
              simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 4)
              subst h; decide
            have heq5 : (op == 5#64) = true := by
              simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h5)
            refine jnz_false hne4 ?_; c0_let_simp; refine jnz_true heq5 ?_
            rw [wp_jump]; exact hJ () m hspec
          · have hne4 : (op == 4#64) = false := by
              simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 4)
              subst h; decide
            have hne5 : (op == 5#64) = false := by
              simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 5)
              subst h; decide
            refine jnz_false hne4 ?_; c0_let_simp; refine jnz_false hne5 ?_
            refine wp_join_group (fun _ _ => False) ?_ ?_
            · intro _ _ _ hF; exact False.elim hF
            · intro _ _
              c0_let_simp
              have huge : BitVec.ule 10#64 op = true := by
                simp only [BitVec.ule, decide_eq_true_eq]
                have : (10#64 : BitVec 64).toNat = 10 := by decide
                omega
              have hule : BitVec.ule op 12#64 = true := by
                simp only [BitVec.ule, decide_eq_true_eq]
                have : (12#64 : BitVec 64).toNat = 12 := by decide
                omega
              refine jnz_true huge ?_; c0_let_simp; refine jnz_true hule ?_
              rw [wp_jump]; exact hJ () m hspec
          · have hne4 : (op == 4#64) = false := by
              simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 4)
              subst h; decide
            have hne5 : (op == 5#64) = false := by
              simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 5)
              subst h; decide
            refine jnz_false hne4 ?_; c0_let_simp; refine jnz_false hne5 ?_
            refine wp_join_group (fun _ _ => False) ?_ ?_
            · intro _ _ _ hF; exact False.elim hF
            · intro _ _
              c0_let_simp
              have huge : BitVec.ule 10#64 op = true := by
                simp only [BitVec.ule, decide_eq_true_eq]
                have : (10#64 : BitVec 64).toNat = 10 := by decide
                omega
              have hule : BitVec.ule op 12#64 = true := by
                simp only [BitVec.ule, decide_eq_true_eq]
                have : (12#64 : BitVec 64).toNat = 12 := by decide
                omega
              refine jnz_true huge ?_; c0_let_simp; refine jnz_true hule ?_
              rw [wp_jump]; exact hJ () m hspec
          · have hne4 : (op == 4#64) = false := by
              simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 4)
              subst h; decide
            have hne5 : (op == 5#64) = false := by
              simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 5)
              subst h; decide
            refine jnz_false hne4 ?_; c0_let_simp; refine jnz_false hne5 ?_
            refine wp_join_group (fun _ _ => False) ?_ ?_
            · intro _ _ _ hF; exact False.elim hF
            · intro _ _
              c0_let_simp
              have huge : BitVec.ule 10#64 op = true := by
                simp only [BitVec.ule, decide_eq_true_eq]
                have : (10#64 : BitVec 64).toNat = 10 := by decide
                omega
              have hule : BitVec.ule op 12#64 = true := by
                simp only [BitVec.ule, decide_eq_true_eq]
                have : (12#64 : BitVec 64).toNat = 12 := by decide
                omega
              refine jnz_true huge ?_; c0_let_simp; refine jnz_true hule ?_
              rw [wp_jump]; exact hJ () m hspec
      · simp only [hop_as, ↓reduceIte] at hspec
        by_cases hop_dm : op.toNat ∈ [6, 7, 8, 14, 15]
        · simp only [hop_dm, ↓reduceIte] at hspec
          refine wp_join_group (fun _ _ => False) ?_ ?_
          · intro _ _ _ hF; exact False.elim hF
          · intro _ _
            c0_let_simp
            have hne_45 : ∀ k, k ∈ [4, 5] → (op == BitVec.ofNat 64 k) = false := by
              intro k hk; simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply hop_as; subst h
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
              rcases hk with rfl | rfl <;> decide
            refine jnz_false (hne_45 4 (by decide)) ?_; c0_let_simp
            refine jnz_false (hne_45 5 (by decide)) ?_
            refine wp_join_group (fun _ m0 => m0 = m) ?_ ?_
            · rintro _ ⟨⟩ m0 hm0
              subst m0
              rw [Blocks.get.eq_1]
              refine wp_join_group
                (fun _ m1 => lcnfIntMulDivSpec (rt, op, a, b, ()) m1 Q (fun _ _ _ _ => False)) ?_ ?_
              · rintro _ ⟨⟩ m1 hc
                rw [Blocks.get.eq_1]
                refine wp_mono (fun _ _ h => h) (fun _ _ _ _ h => False.elim h) _ _ ?_
                refine wp_call_ret1 _ _ (fun res m' => Q (res, ()) m') ?_ ?_
                · exact rtR1Env_lcnf_int_muldiv hc
                · intro r m' hq; rw [wp_ret]; exact hq
              · intro J2 hJ2
                c0_let_simp
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hop_dm
                rcases hop_dm with h6 | h7 | h8 | h14 | h15
                · have heq6 : (op == 6#64) = true := by
                    simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h6)
                  refine jnz_true heq6 ?_; rw [wp_jump]; exact hJ2 () m hspec
                · have hne6 : (op == 6#64) = false := by
                    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 6)
                    subst h; decide
                  have heq7 : (op == 7#64) = true := by
                    simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h7)
                  refine jnz_false hne6 ?_; c0_let_simp; refine jnz_true heq7 ?_
                  rw [wp_jump]; exact hJ2 () m hspec
                · have hne6 : (op == 6#64) = false := by
                    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 6)
                    subst h; decide
                  have hne7 : (op == 7#64) = false := by
                    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 7)
                    subst h; decide
                  have heq8 : (op == 8#64) = true := by
                    simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h8)
                  refine jnz_false hne6 ?_; c0_let_simp; refine jnz_false hne7 ?_; c0_let_simp
                  refine jnz_true heq8 ?_; rw [wp_jump]; exact hJ2 () m hspec
                · have hne6 : (op == 6#64) = false := by
                    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 6)
                    subst h; decide
                  have hne7 : (op == 7#64) = false := by
                    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 7)
                    subst h; decide
                  have hne8 : (op == 8#64) = false := by
                    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 8)
                    subst h; decide
                  have heq14 : (op == 14#64) = true := by
                    simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h14)
                  refine jnz_false hne6 ?_; c0_let_simp; refine jnz_false hne7 ?_; c0_let_simp
                  refine jnz_false hne8 ?_; c0_let_simp; refine jnz_true heq14 ?_
                  rw [wp_jump]; exact hJ2 () m hspec
                · have hne6 : (op == 6#64) = false := by
                    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 6)
                    subst h; decide
                  have hne7 : (op == 7#64) = false := by
                    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 7)
                    subst h; decide
                  have hne8 : (op == 8#64) = false := by
                    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 8)
                    subst h; decide
                  have hne14 : (op == 14#64) = false := by
                    simp only [beq_eq_false_iff_ne, ne_eq]; intro h
                    apply (by omega : op.toNat ≠ 14); subst h; decide
                  have heq15 : (op == 15#64) = true := by
                    simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h15)
                  refine jnz_false hne6 ?_; c0_let_simp; refine jnz_false hne7 ?_; c0_let_simp
                  refine jnz_false hne8 ?_; c0_let_simp; refine jnz_false hne14 ?_; c0_let_simp
                  refine jnz_true heq15 ?_; rw [wp_jump]; exact hJ2 () m hspec
            · intro J1 hJ1
              c0_let_simp
              have hnot_10_12 : ¬(10 ≤ op.toNat ∧ op.toNat ≤ 12) := by
                intro h; apply hop_as; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
              by_cases hge10 : 10 ≤ op.toNat
              · have huge : BitVec.ule 10#64 op = true := by
                  simp only [BitVec.ule, decide_eq_true_eq]
                  have : (10#64 : BitVec 64).toNat = 10 := by decide
                  omega
                have hnule : BitVec.ule op 12#64 = false := by
                  simp only [BitVec.ule, decide_eq_false_iff_not]
                  have : (12#64 : BitVec 64).toNat = 12 := by decide
                  omega
                refine jnz_true huge ?_; c0_let_simp; refine jnz_false hnule ?_
                rw [wp_jump]; exact hJ1 () m rfl
              · have hnuge : BitVec.ule 10#64 op = false := by
                  simp only [BitVec.ule, decide_eq_false_iff_not]
                  have : (10#64 : BitVec 64).toNat = 10 := by decide
                  omega
                refine jnz_false hnuge ?_; rw [wp_jump]; exact hJ1 () m rfl
        · simp only [hop_dm, ↓reduceIte] at hspec

theorem rtR1Mod_tableImpl : TableImpl rtR1Env rtR1Mod.fns rtR1SpecEntries := by
  dsimp only [rtR1Mod, rtR1_fns, rtR1SpecEntries, TableImpl]
  refine ⟨SpecEntry.Impl.of rt_scratch_wp, SpecEntry.Impl.of rt_scratch_cap_wp,
    SpecEntry.Impl.of lcnf_nat_alloc_wp, SpecEntry.Impl.of bn_dec_nat_wp,
    SpecEntry.Impl.of bn_require_scratch_wp, SpecEntry.Impl.of bn_trim_wp,
    SpecEntry.Impl.of bn_copy_wp, SpecEntry.Impl.of bn_zero_wp,
    SpecEntry.Impl.of bn_nat_from_limbs_wp, SpecEntry.Impl.of bn_int_from_limbs_wp,
    SpecEntry.Impl.of bn_nat_len_wp, SpecEntry.Impl.of bn_int_len_wp,
    SpecEntry.Impl.of bn_load_nat_wp, SpecEntry.Impl.of bn_load_int_wp,
    SpecEntry.Impl.of bn_cmp_fixed_wp, SpecEntry.Impl.of bn_cmp_wp,
    SpecEntry.Impl.of bn_add_wp, SpecEntry.Impl.of bn_add_one_wp,
    SpecEntry.Impl.of bn_sub_wp, SpecEntry.Impl.of bn_sub_one_wp,
    SpecEntry.Impl.of bn_mul_wp, SpecEntry.Impl.of bn_bitwise_wp,
    SpecEntry.Impl.of bn_shl_wp, SpecEntry.Impl.of bn_shr_wp,
    SpecEntry.Impl.of bn_divmod_wp, SpecEntry.Impl.of bn_nat_pow_wp,
    SpecEntry.Impl.of bn_nat_gcd_wp, SpecEntry.Impl.of lcnf_nat_arith_wp,
    SpecEntry.Impl.of lcnf_nat_bits_wp, SpecEntry.Impl.of lcnf_nat_slow_wp,
    SpecEntry.Impl.of lcnf_int_conv_wp, SpecEntry.Impl.of lcnf_int_addsub_cmp_wp,
    SpecEntry.Impl.of lcnf_int_muldiv_wp, SpecEntry.Impl.of lcnf_int_op_wp, trivial⟩

theorem rtR1Mod_moduleOk : ModuleOk rtR1Env rtR1Mod :=
  Env.ofTable_moduleOk rtR1_checkAcyclic (allFns_of_mem _ rtR1_fns_wf) rtR1Mod_tableImpl

/-- Headline R1 soundness theorem: `lcnf_nat_alloc` satisfies `lcnfNatAllocSpec`. -/
theorem lcnf_nat_alloc_sound :
    ∀ xs m Q X, lcnfNatAllocSpec xs m Q X → Func.wp rtR1Env lcnf_nat_alloc.body xs m Q X :=
  lcnf_nat_alloc_wp

/-- Headline R1 soundness theorem: `lcnf_nat_slow` satisfies `lcnfNatSlowSpec` against `Nat`. -/
theorem lcnf_nat_slow_sound :
    ∀ xs m Q X, lcnfNatSlowSpec xs m Q X → Func.wp rtR1Env lcnf_nat_slow.body xs m Q X :=
  lcnf_nat_slow_wp

/-- Headline R1 soundness theorem: `lcnf_int_op` satisfies `lcnfIntOpSpec` against `Int`. -/
theorem lcnf_int_op_sound :
    ∀ xs m Q X, lcnfIntOpSpec xs m Q X → Func.wp rtR1Env lcnf_int_op.body xs m Q X :=
  lcnf_int_op_wp

/-! ## Concrete `Mem 64` Multi-Limb BigNum Non-Vacuity (`XPost := False`) -/

def nvBnRtBase : BitVec 64 := 0x100000#64
def nvBnWorkCap : Nat := 8
def nvBnRem : Nat := 256
def nvBnScrCap : Nat := 32

def nvBnScr : BitVec 64 := nvBnRtBase + 34008#64
def nvBnScrLimbs : List (BitVec 64) := List.replicate nvBnScrCap 0#64
def nvBnHeapBase : BitVec 64 := nvBnRtBase + 34264#64

def nvBnAddrNatA : BitVec 64 := nvBnHeapBase
def nvBnAddrNatB : BitVec 64 := nvBnHeapBase + 32#64
def nvBnAddrIntNegA : BitVec 64 := nvBnHeapBase + 64#64
def nvBnAddrIntPosB : BitVec 64 := nvBnHeapBase + 96#64

/-- Concrete initial `BigNumRt.RtC0State` with `workBuf` placed after `LcnfC0BigNumRt`
(`+33688`), followed by a `256B` bump arena (`[+33752, +34008)`). -/
def nvBnRtState : RtC0State where
  extraArgs := List.replicate rtExtraSlots 0#64
  globals := List.replicate rtGlobalSlots 0#64
  freeList := List.replicate rtNumClasses 0#64
  hdr :=
    { s_large_free := 0#64
      s_ba_empty := 0#64
      s_cur := nvBnRtBase + 33752#64
      s_end := nvBnRtBase + 34008#64
      s_work := nvBnRtBase + 33688#64
      s_work_cap := BitVec.ofNat 64 nvBnWorkCap
      s_chunks := 0#64
      s_nchunks := 0#64
      s_chunks_cap := 0#64
      s_st_allocs := 0#64
      s_st_frees := 0#64
      s_st_live := 0#64
      s_st_peak_live := 0#64
      s_st_persistent := 0#64
      s_st_reused := 0#64
      s_st_cold_decs := 0#64
      s_st_bytes := 0#64 }
  workBuf := List.replicate nvBnWorkCap 0#64
  smallPools := fun _ => []
  largeNodes := []
  extraLen := List.length_replicate
  globalsLen := List.length_replicate
  freeListLen := List.length_replicate
  workLen := by decide
  curLeEnd := by decide
  arenaAlign := by decide
  curNz := by decide

/-- 2-limb `Nat` `3 * 2^64 - 1` (`[0xffffffffffffffff, 2]`). -/
def nvValNatA : Nat := 3 * 2 ^ 64 - 1

/-- 2-limb `Nat` `2^64 + 5` (`[5, 1]`). -/
def nvValNatB : Nat := 2 ^ 64 + 5

/-- Negative 2-limb `Int` `-(3 * 2^64 - 1)`. -/
def nvValIntNegA : Int := -(nvValNatA : Int)

/-- Positive 2-limb `Int` `2^64 + 5`. -/
def nvValIntPosB : Int := (nvValNatB : Int)

def nvBnNatA : LcnfObj :=
  { addr := nvBnAddrNatA, rc := 1#32, csSz := 32, other := 0, tag := mpzTag,
    cap := 2, arrSize := 2, limbs := [0xffffffffffffffff#64, 2#64] }

def nvBnNatB : LcnfObj :=
  { addr := nvBnAddrNatB, rc := 1#32, csSz := 32, other := 0, tag := mpzTag,
    cap := 2, arrSize := 2, limbs := [5#64, 1#64] }

def nvBnIntNegA : LcnfObj :=
  { addr := nvBnAddrIntNegA, rc := 1#32, csSz := 32, other := 1, tag := mpzTag,
    cap := 2, arrSize := 2, limbs := [0xffffffffffffffff#64, 2#64] }

def nvBnIntPosB : LcnfObj :=
  { addr := nvBnAddrIntPosB, rc := 1#32, csSz := 32, other := 0, tag := mpzTag,
    cap := 2, arrSize := 2, limbs := [5#64, 1#64] }

def nvBnObjs : List LcnfObj := [nvBnNatA, nvBnNatB, nvBnIntNegA, nvBnIntPosB]

def nvBnHdrWords (h : LcnfC0BaseRt) : List (BitVec 64) :=
  [ h.s_large_free, h.s_ba_empty, h.s_cur, h.s_end, h.s_work, h.s_work_cap,
    h.s_chunks, h.s_nchunks, h.s_chunks_cap, h.s_st_allocs, h.s_st_frees,
    h.s_st_live, h.s_st_peak_live, h.s_st_persistent, h.s_st_reused,
    h.s_st_cold_decs, h.s_st_bytes ]

def nvBnRtBytes : List UInt8 :=
  bytes64 nvBnRtState.extraArgs ++ bytes64 nvBnRtState.globals ++
  bytes64 nvBnRtState.freeList ++ bytes64 (nvBnHdrWords nvBnRtState.hdr) ++
  bytes64 [nvBnScr, BitVec.ofNat 64 nvBnScrCap] ++ bytes64 nvBnRtState.workBuf ++
  List.replicate nvBnRem 0 ++ bytes64 nvBnScrLimbs

def nvBnObjBytes (o : LcnfObj) : List UInt8 :=
  bytes64 (o.header :: o.mpzMeta :: o.limbs)

def nvBnHeapBytes : List UInt8 :=
  nvBnObjBytes nvBnNatA ++ nvBnObjBytes nvBnNatB ++
  nvBnObjBytes nvBnIntNegA ++ nvBnObjBytes nvBnIntPosB

/-- Concrete `Mem 64` image packing `LcnfC0BigNumRt` + `workBuf` + `256B` bump arena + `32`-limb
scratch buffer (`34264B`) and `4` multi-limb `MPZ` objects (`128B`). -/
def nvBnMem : Mem 64 := (nvBnRtBytes ++ nvBnHeapBytes).At nvBnRtBase

private theorem nvBn_sep_append {P Q : Mem 64 → Prop} {a : BitVec 64}
    {bs1 bs2 : List UInt8} {n1 n2 : Nat}
    (h1 : bs1.length = n1) (h2 : bs2.length = n2) (hfit : n1 + n2 ≤ 2 ^ 64)
    (hp : P (bs1.At a)) (hq : Q (bs2.At (a + BitVec.ofNat 64 n1))) :
    (P ⋆ Q) ((bs1 ++ bs2).At a) := by
  have hs := congrFun (Mem.At_append_sep bs1 bs2 a (by omega)) ((bs1 ++ bs2).At a)
  obtain ⟨m1, m2, hu, hd, rfl, rfl⟩ := hs.mp rfl
  refine ⟨bs1.At a, bs2.At (a + BitVec.ofNat 64 bs1.length), hu, hd, hp, ?_⟩
  rwa [h1]

private theorem array64_baseHdrWords_to_At (rt : BitVec 64) (h : LcnfC0BaseRt) {m : Mem 64}
    (hm : array64 (rt + 33536#64) (nvBnHdrWords h) m) : LcnfC0BaseRt.At rt h m := by
  unfold nvBnHdrWords at hm
  simp only [array64, cell64_eq_cell, sep_emp, BitVec.add_assoc] at hm
  unfold LcnfC0BaseRt.At
  exact sep_cast hm (by ac_rfl)

private theorem nvBnSmallPools_emp (n : Nat) :
    smallPoolsAt (List.replicate rtNumClasses 0#64) (fun _ => []) n = emp := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have heq : (List.replicate rtNumClasses 0#64).getD n 0#64 = 0#64 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl
    have hslot : smallPoolSlot n 0#64 [] = emp := by
      funext m
      unfold smallPoolSlot
      split <;> simp [smallFreeList]
    simp only [smallPoolsAt, ih, heq, hslot, sep_emp]

private theorem array64_mpz_to_objMem {o : LcnfObj} (ht : o.tag = mpzTag) {m : Mem 64}
    (hm : array64 o.addr (o.header :: o.mpzMeta :: o.limbs) m) : lcnfObjMem o m := by
  unfold lcnfObjMem
  simp only [ht, show mpzTag ≠ closureTag by decide, show mpzTag ≠ arrayTag by decide,
    show mpzTag ≠ sarrayTag by decide, show mpzTag ≠ stringTag by decide, ↓reduceIte]
  simp only [array64, BitVec.add_assoc] at hm
  exact sep_cast hm (by ac_rfl)

private theorem nvBnRtBytes_ok :
    nvBnRtBytes.length = 34264 ∧
    bigNumRtInv nvBnRtBase nvBnRtState nvBnScr nvBnScrLimbs (nvBnRtBytes.At nvBnRtBase) := by
  let b0 := bytes64 nvBnRtState.extraArgs
  let b1 := bytes64 nvBnRtState.globals
  let b2 := bytes64 nvBnRtState.freeList
  let b3 := bytes64 (nvBnHdrWords nvBnRtState.hdr)
  let bMeta := bytes64 [nvBnScr, BitVec.ofNat 64 nvBnScrCap]
  let b4 := bytes64 nvBnRtState.workBuf
  let b5 := List.replicate nvBnRem (0 : UInt8)
  let b6 := bytes64 nvBnScrLimbs
  have hl0 : b0.length = 256 := by
    dsimp only [b0]; rw [bytes64_length, nvBnRtState.extraLen]; decide
  have hl1 : b1.length = 32768 := by
    dsimp only [b1]; rw [bytes64_length, nvBnRtState.globalsLen]; decide
  have hl2 : b2.length = 512 := by
    dsimp only [b2]; rw [bytes64_length, nvBnRtState.freeListLen]; decide
  have hl3 : b3.length = 136 := by
    dsimp only [b3]; rw [bytes64_length]; decide
  have hlMeta : bMeta.length = 16 := by
    dsimp only [bMeta]; rw [bytes64_length]; decide
  have hl4 : b4.length = 64 := by
    dsimp only [b4]; rw [bytes64_length, nvBnRtState.workLen]; decide
  have hl5 : b5.length = 256 := by
    dsimp only [b5]; rw [List.length_replicate]; rfl
  have hl6 : b6.length = 256 := by
    dsimp only [b6]; rw [bytes64_length, show nvBnScrLimbs.length = 32 from List.length_replicate]
  have htot : nvBnRtBytes.length = 34264 := by
    change (((((((b0 ++ b1) ++ b2) ++ b3) ++ bMeta) ++ b4) ++ b5) ++ b6).length = 34264
    simp only [List.length_append, hl0, hl1, hl2, hl3, hlMeta, hl4, hl5, hl6]
  refine ⟨htot, ?_⟩
  have h0 : array64 nvBnRtBase nvBnRtState.extraArgs (b0.At nvBnRtBase) :=
    array64_bytes nvBnRtBase nvBnRtState.extraArgs (by rw [nvBnRtState.extraLen]; decide)
  have h1 : array64 (nvBnRtBase + BitVec.ofNat 64 rtGlobalsOff) nvBnRtState.globals
      (b1.At (nvBnRtBase + BitVec.ofNat 64 256)) :=
    array64_bytes (nvBnRtBase + BitVec.ofNat 64 rtGlobalsOff) nvBnRtState.globals
      (by rw [nvBnRtState.globalsLen]; decide)
  have h2 : array64 (nvBnRtBase + 33024#64) nvBnRtState.freeList
      (b2.At (nvBnRtBase + BitVec.ofNat 64 33024)) :=
    array64_bytes (nvBnRtBase + 33024#64) nvBnRtState.freeList
      (by rw [nvBnRtState.freeListLen]; decide)
  have h3 : LcnfC0BaseRt.At nvBnRtBase nvBnRtState.hdr
      (b3.At (nvBnRtBase + BitVec.ofNat 64 33536)) :=
    array64_baseHdrWords_to_At nvBnRtBase nvBnRtState.hdr
      (array64_bytes (nvBnRtBase + 33536#64) (nvBnHdrWords nvBnRtState.hdr) (by decide))
  have hMeta :
      (cell64 (nvBnRtBase + 33672#64) nvBnScr ⋆
        cell64 (nvBnRtBase + 33680#64) (BitVec.ofNat 64 nvBnScrLimbs.length))
      (bMeta.At (nvBnRtBase + BitVec.ofNat 64 33672)) := by
    have ha := array64_bytes (nvBnRtBase + 33672#64) [nvBnScr, BitVec.ofNat 64 nvBnScrCap]
      (by decide)
    have hlen : nvBnScrLimbs.length = nvBnScrCap := List.length_replicate
    rw [hlen]
    simpa [array64, sep_emp, BitVec.add_assoc] using ha
  have h4 : array64 nvBnRtState.hdr.s_work nvBnRtState.workBuf
      (b4.At (nvBnRtBase + BitVec.ofNat 64 33688)) := by
    have hs : nvBnRtState.hdr.s_work = nvBnRtBase + BitVec.ofNat 64 33688 := rfl
    rw [hs]
    exact array64_bytes _ nvBnRtState.workBuf (by rw [nvBnRtState.workLen]; decide)
  have h5 : region nvBnRtState.hdr.s_cur nvBnRtState.rem
      (b5.At (nvBnRtBase + BitVec.ofNat 64 33752)) := by
    have hc : nvBnRtState.hdr.s_cur = nvBnRtBase + BitVec.ofNat 64 33752 := rfl
    have hr : nvBnRtState.rem = nvBnRem := by decide
    rw [hc, hr]
    exact ⟨b5, hl5, rfl⟩
  have h6 : array64 nvBnScr nvBnScrLimbs (b6.At (nvBnRtBase + BitVec.ofNat 64 34008)) := by
    have hs : nvBnScr = nvBnRtBase + BitVec.ofNat 64 34008 := rfl
    rw [hs]
    exact array64_bytes _ nvBnScrLimbs
      (by rw [show nvBnScrLimbs.length = 32 from List.length_replicate]; decide)
  have h01 := nvBn_sep_append hl0 hl1 (by decide) h0 h1
  have h012 := nvBn_sep_append (by simp [hl0, hl1] : (b0 ++ b1).length = 33024)
    hl2 (by decide) h01 h2
  have h0123 := nvBn_sep_append (by simp [hl0, hl1, hl2] : ((b0 ++ b1) ++ b2).length = 33536)
    hl3 (by decide) h012 h3
  have h0123m := nvBn_sep_append
    (by simp [hl0, hl1, hl2, hl3] : (((b0 ++ b1) ++ b2) ++ b3).length = 33672)
    hlMeta (by decide) h0123 hMeta
  have h0123m4 := nvBn_sep_append
    (by simp [hl0, hl1, hl2, hl3, hlMeta] :
      ((((b0 ++ b1) ++ b2) ++ b3) ++ bMeta).length = 33688)
    hl4 (by decide) h0123m h4
  have h0123m45 := nvBn_sep_append
    (by simp [hl0, hl1, hl2, hl3, hlMeta, hl4] :
      (((((b0 ++ b1) ++ b2) ++ b3) ++ bMeta) ++ b4).length = 33752)
    hl5 (by decide) h0123m4 h5
  have hAll := nvBn_sep_append
    (by simp [hl0, hl1, hl2, hl3, hlMeta, hl4, hl5] :
      ((((((b0 ++ b1) ++ b2) ++ b3) ++ bMeta) ++ b4) ++ b5).length = 34008)
    hl6 (by decide) h0123m45 h6
  have hsm : smallPoolsAt nvBnRtState.freeList nvBnRtState.smallPools rtNumClasses = emp :=
    nvBnSmallPools_emp rtNumClasses
  have hlg : largeFreeList nvBnRtState.hdr.s_large_free nvBnRtState.largeNodes = emp := by
    funext m'; simp [largeFreeList, largeSeg, nvBnRtState]
  dsimp only [bigNumRtInv, rtC0Inv]
  rw [hsm, hlg, sep_emp, sep_emp]
  exact sep_cast_ac hAll (by ac_rfl)

private theorem nvBnHeapBytes_ok :
    nvBnHeapBytes.length = 128 ∧ lcnfHeap nvBnObjs (nvBnHeapBytes.At nvBnHeapBase) := by
  have hlA : (nvBnObjBytes nvBnNatA).length = 32 := by
    simp [nvBnObjBytes, nvBnNatA, bytes64_length]
  have hlB : (nvBnObjBytes nvBnNatB).length = 32 := by
    simp [nvBnObjBytes, nvBnNatB, bytes64_length]
  have hlC : (nvBnObjBytes nvBnIntNegA).length = 32 := by
    simp [nvBnObjBytes, nvBnIntNegA, bytes64_length]
  have hlD : (nvBnObjBytes nvBnIntPosB).length = 32 := by
    simp [nvBnObjBytes, nvBnIntPosB, bytes64_length]
  have htot : nvBnHeapBytes.length = 128 := by simp [nvBnHeapBytes, hlA, hlB, hlC, hlD]
  refine ⟨htot, ?_⟩
  have hA : lcnfObjMem nvBnNatA ((nvBnObjBytes nvBnNatA).At nvBnHeapBase) :=
    array64_mpz_to_objMem rfl (array64_bytes nvBnAddrNatA _ (by decide))
  have hB : lcnfObjMem nvBnNatB ((nvBnObjBytes nvBnNatB).At (nvBnHeapBase + BitVec.ofNat 64 32)) :=
    array64_mpz_to_objMem rfl (array64_bytes nvBnAddrNatB _ (by decide))
  have hC : lcnfObjMem nvBnIntNegA
      ((nvBnObjBytes nvBnIntNegA).At (nvBnHeapBase + BitVec.ofNat 64 64)) :=
    array64_mpz_to_objMem rfl (array64_bytes nvBnAddrIntNegA _ (by decide))
  have hD : lcnfObjMem nvBnIntPosB
      ((nvBnObjBytes nvBnIntPosB).At (nvBnHeapBase + BitVec.ofNat 64 96)) :=
    array64_mpz_to_objMem rfl (array64_bytes nvBnAddrIntPosB _ (by decide))
  have hAB := nvBn_sep_append hlA hlB (by decide) hA hB
  have hABC := nvBn_sep_append
    (by simp [hlA, hlB] : (nvBnObjBytes nvBnNatA ++ nvBnObjBytes nvBnNatB).length = 64)
    hlC (by decide) hAB hC
  have hABCD := nvBn_sep_append
    (by simp [hlA, hlB, hlC] :
      ((nvBnObjBytes nvBnNatA ++ nvBnObjBytes nvBnNatB) ++ nvBnObjBytes nvBnIntNegA).length = 96)
    hlD (by decide) hABC hD
  simp only [nvBnObjs, lcnfHeap, sep_emp]
  exact sep_cast_ac hABCD (by ac_rfl)

/-- Concrete `Mem 64` separation-logic satisfiability of `bigNumRtInv ⋆ lcnfHeap` with 4
multi-limb `MPZ` objects (`nvBnNatA`, `nvBnNatB`, `nvBnIntNegA`, `nvBnIntPosB`). -/
theorem nvBnMem_ok :
    (bigNumRtInv nvBnRtBase nvBnRtState nvBnScr nvBnScrLimbs ⋆ lcnfHeap nvBnObjs) nvBnMem := by
  have ⟨hlRt, hRt⟩ := nvBnRtBytes_ok
  have ⟨hlH, hH⟩ := nvBnHeapBytes_ok
  exact nvBn_sep_append hlRt hlH (by decide) hRt hH

private theorem nvBnRtWf : BigNumRtWf nvBnRtBase nvBnRtState nvBnScr nvBnScrLimbs := by
  have hlen : nvBnScrLimbs.length = 32 := List.length_replicate
  refine ⟨show nvBnRtState.hdr.s_end.toNat < 2 ^ 48 by decide,
    by decide, by decide, by decide, by rw [hlen]; decide, by rw [hlen]; decide⟩

private theorem nvBnNatA_rep : natRep nvBnAddrNatA nvValNatA nvBnObjs := by
  have hge : ¬(nvValNatA < 2 ^ 63) := by decide
  simp only [natRep, hge, ↓reduceIte]
  refine ⟨by decide, nvBnNatA, by simp [nvBnObjs], rfl,
    by unfold LcnfObj.Wf LcnfObj.totalBytes; decide, rfl, rfl, rfl,
    by decide, by decide, by decide, ?_, by decide⟩
  simp [nvBnNatA, limbsVal, nvValNatA]

private theorem nvBnNatB_rep : natRep nvBnAddrNatB nvValNatB nvBnObjs := by
  have hge : ¬(nvValNatB < 2 ^ 63) := by decide
  simp only [natRep, hge, ↓reduceIte]
  refine ⟨by decide, nvBnNatB, by simp [nvBnObjs], rfl,
    by unfold LcnfObj.Wf LcnfObj.totalBytes; decide, rfl, rfl, rfl,
    by decide, by decide, by decide, ?_, by decide⟩
  simp [nvBnNatB, limbsVal, nvValNatB]

private theorem nvBnIntNegA_rep : intRep nvBnAddrIntNegA nvValIntNegA nvBnObjs := by
  have hbig : ¬(-(2 ^ 62 : Int) ≤ nvValIntNegA ∧ nvValIntNegA < (2 ^ 62 : Int)) := by decide
  simp only [intRep, hbig, ↓reduceIte]
  refine ⟨by decide, nvBnIntNegA, by simp [nvBnObjs], rfl,
    by unfold LcnfObj.Wf LcnfObj.totalBytes; decide, rfl, Or.inr rfl, rfl,
    by decide, by decide, by decide, ?_, by decide, by decide⟩
  simp [nvBnIntNegA, limbsVal, nvValIntNegA, nvValNatA]

private theorem nvBnIntPosB_rep : intRep nvBnAddrIntPosB nvValIntPosB nvBnObjs := by
  have hbig : ¬(-(2 ^ 62 : Int) ≤ nvValIntPosB ∧ nvValIntPosB < (2 ^ 62 : Int)) := by decide
  simp only [intRep, hbig, ↓reduceIte]
  refine ⟨by decide, nvBnIntPosB, by simp [nvBnObjs], rfl,
    by unfold LcnfObj.Wf LcnfObj.totalBytes; decide, rfl, Or.inl rfl, rfl,
    by decide, by decide, by decide, ?_, by decide, by decide⟩
  simp [nvBnIntPosB, limbsVal, nvValIntPosB, nvValNatB]

private theorem limbs_eq_two {xs : List (BitVec 64)} {a b : BitVec 64}
    (hne : xs ≠ []) (hlast : xs.getLast! ≠ 0#64) (hb : b ≠ 0#64)
    (hval : limbsVal xs = a.toNat + 2 ^ 64 * b.toNat) : xs = [a, b] := by
  have hlen : xs.length = 2 := by
    rw [← limbLenNat_eq_length_of_trimmed hne hlast, hval]
    have hbnz : 0 < b.toNat := bv64_toNat_pos_of_ne hb
    have hpos : a.toNat + 2 ^ 64 * b.toNat ≠ 0 := by omega
    have ha : a.toNat < 2 ^ 64 := a.isLt
    have hb' : b.toNat < 2 ^ 64 := b.isLt
    have hlb : 64 ≤ (a.toNat + 2 ^ 64 * b.toNat).log2 := (Nat.le_log2 hpos).mpr (by omega)
    have hub : (a.toNat + 2 ^ 64 * b.toNat).log2 < 128 := (Nat.log2_lt hpos).mpr (by omega)
    unfold limbLenNat; simp only [hpos, ↓reduceIte]; omega
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | _⟩⟩ <;> simp at hlen
  simp only [limbsVal] at hval
  have hx0 : x0.toNat < 2 ^ 64 := x0.isLt
  have ha : a.toNat < 2 ^ 64 := a.isLt
  have h0 : x0 = a := BitVec.eq_of_toNat_eq (by omega)
  have h1 : x1 = b := BitVec.eq_of_toNat_eq (by omega)
  rw [h0, h1]

private theorem limbs_eq_three {xs : List (BitVec 64)} {a b c : BitVec 64}
    (hne : xs ≠ []) (hlast : xs.getLast! ≠ 0#64) (hc : c ≠ 0#64)
    (hval : limbsVal xs = a.toNat + 2 ^ 64 * (b.toNat + 2 ^ 64 * c.toNat)) : xs = [a, b, c] := by
  have hlen : xs.length = 3 := by
    rw [← limbLenNat_eq_length_of_trimmed hne hlast, hval]
    have hcnz : 0 < c.toNat := bv64_toNat_pos_of_ne hc
    have hpos : a.toNat + 2 ^ 64 * (b.toNat + 2 ^ 64 * c.toNat) ≠ 0 := by omega
    have ha : a.toNat < 2 ^ 64 := a.isLt
    have hb : b.toNat < 2 ^ 64 := b.isLt
    have hc' : c.toNat < 2 ^ 64 := c.isLt
    have hlb : 128 ≤ (a.toNat + 2 ^ 64 * (b.toNat + 2 ^ 64 * c.toNat)).log2 :=
      (Nat.le_log2 hpos).mpr (by omega)
    have hub : (a.toNat + 2 ^ 64 * (b.toNat + 2 ^ 64 * c.toNat)).log2 < 192 :=
      (Nat.log2_lt hpos).mpr (by omega)
    unfold limbLenNat; simp only [hpos, ↓reduceIte]; omega
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | _⟩⟩⟩ <;> simp at hlen
  simp only [limbsVal] at hval
  have hx0 : x0.toNat < 2 ^ 64 := x0.isLt
  have hx1 : x1.toNat < 2 ^ 64 := x1.isLt
  have ha : a.toNat < 2 ^ 64 := a.isLt
  have hb : b.toNat < 2 ^ 64 := b.isLt
  have h0 : x0 = a := BitVec.eq_of_toNat_eq (by omega)
  have h1 : x1 = b := BitVec.eq_of_toNat_eq (by omega)
  have h2 : x2 = c := BitVec.eq_of_toNat_eq (by omega)
  rw [h0, h1, h2]

/-- Concrete `XPost := False` NV: multi-limb `Nat` carry addition
`(3 * 2^64 - 1) + (2^64 + 5) = 4 * 2^64 + 4` yields exact 2-limb MPZ `[4, 4]`. -/
theorem nv_bn_nat_add_carry :
    Func.wp rtR1Env lcnf_nat_slow.body
      (nvBnRtBase, 1#64, nvBnAddrNatA, nvBnAddrNatB, ()) nvBnMem
      (fun r m' =>
        ∃ st' scrLimbs' objs' obj,
          (r.1 &&& 1#64) = 0#64 ∧ obj ∈ objs' ∧ obj.addr = r.1 ∧
          obj.tag = mpzTag ∧ obj.other = 0 ∧ obj.arrSize = 2 ∧
          obj.limbs = [4#64, 4#64] ∧
          (bigNumRtInv nvBnRtBase st' nvBnScr scrLimbs' ⋆ lcnfHeap objs') m')
      (fun _ _ _ _ => False) := by
  refine lcnf_nat_slow_sound _ _ _ _ ?_
  refine ⟨nvBnRtState, nvBnScr, nvBnScrLimbs, nvBnObjs, emp, nvBnRtWf,
    by rw [sep_emp]; exact nvBnMem_ok, ?_⟩
  have hmem : (1#64 : BitVec 64).toNat ∈ [1, 2, 3, 4, 5, 6, 7, 8, 17] := by decide
  simp only [hmem, ↓reduceIte]
  refine ⟨nvValNatA, nvValNatB, nvBnNatA_rep, Or.inr nvBnNatB_rep, ?_, ?_⟩
  · refine by
      dsimp only [natArithOk, natArithRes]
      have hcap : nvBnScrLimbs.length = 32 := by simp [nvBnScrLimbs, nvBnScrCap]
      rw [hcap]
      refine ⟨by decide, by decide, fun _ => Or.inr (by decide)⟩
  · intro res st' scrLimbs' objs' m' _ _ _ hpost hm'
    rw [sep_emp] at hm'
    have hrep : natRep res (nvValNatA + nvValNatB) objs' := by
      simpa [natArithPost, natArithRes] using hpost.1
    have hbig : ¬(nvValNatA + nvValNatB < 2 ^ 63) := by decide
    simp only [natRep, hbig, ↓reduceIte] at hrep
    rcases hrep with ⟨halign, obj, hobjMem, hobjAddr,
      _, htag, hoth, harr, h1, _, hlast, hval, _⟩
    have hne : obj.limbs ≠ [] := by intro h; simp [h] at h1
    have hlimbs : obj.limbs = [4#64, 4#64] :=
      limbs_eq_two hne hlast (by decide) (by rw [hval]; decide)
    exact ⟨st', scrLimbs', objs', obj, halign, hobjMem, hobjAddr, htag, hoth,
      by rw [harr, hlimbs]; rfl, hlimbs, hm'⟩

/-- Concrete `XPost := False` NV: 2×2-limb `Nat` multiplication
`(3 * 2^64 - 1) * (2^64 + 5) = 3 * 2^128 + 13 * 2^64 + (2^64 - 5)` yields exact 3-limb MPZ
`[0xfffffffffffffffb, 13, 3]`. -/
theorem nv_bn_nat_mul_2x2 :
    Func.wp rtR1Env lcnf_nat_slow.body
      (nvBnRtBase, 3#64, nvBnAddrNatA, nvBnAddrNatB, ()) nvBnMem
      (fun r m' =>
        ∃ st' scrLimbs' objs' obj,
          (r.1 &&& 1#64) = 0#64 ∧ obj ∈ objs' ∧ obj.addr = r.1 ∧
          obj.tag = mpzTag ∧ obj.other = 0 ∧ obj.arrSize = 3 ∧
          obj.limbs = [0xfffffffffffffffb#64, 13#64, 3#64] ∧
          (bigNumRtInv nvBnRtBase st' nvBnScr scrLimbs' ⋆ lcnfHeap objs') m')
      (fun _ _ _ _ => False) := by
  refine lcnf_nat_slow_sound _ _ _ _ ?_
  refine ⟨nvBnRtState, nvBnScr, nvBnScrLimbs, nvBnObjs, emp, nvBnRtWf,
    by rw [sep_emp]; exact nvBnMem_ok, ?_⟩
  have hmem : (3#64 : BitVec 64).toNat ∈ [1, 2, 3, 4, 5, 6, 7, 8, 17] := by decide
  simp only [hmem, ↓reduceIte]
  refine ⟨nvValNatA, nvValNatB, nvBnNatA_rep, Or.inr nvBnNatB_rep, ?_, ?_⟩
  · dsimp only [natArithOk, natArithRes]
    have hcap : nvBnScrLimbs.length = 32 := by simp [nvBnScrLimbs, nvBnScrCap]
    rw [hcap]
    exact ⟨by decide, by decide, fun _ => Or.inr (by decide)⟩
  · intro res st' scrLimbs' objs' m' _ _ _ hpost hm'
    rw [sep_emp] at hm'
    have hrep : natRep res (nvValNatA * nvValNatB) objs' := by
      simpa [natArithPost, natArithRes] using hpost.1
    have hbig : ¬(nvValNatA * nvValNatB < 2 ^ 63) := by decide
    simp only [natRep, hbig, ↓reduceIte] at hrep
    rcases hrep with ⟨halign, obj, hobjMem, hobjAddr,
      _, htag, hoth, harr, h1, _, hlast, hval, _⟩
    have hne : obj.limbs ≠ [] := by intro h; simp [h] at h1
    have hlimbs : obj.limbs = [0xfffffffffffffffb#64, 13#64, 3#64] :=
      limbs_eq_three hne hlast (by decide) (by rw [hval]; decide)
    exact ⟨st', scrLimbs', objs', obj, halign, hobjMem, hobjAddr, htag, hoth,
      by rw [harr, hlimbs]; rfl, hlimbs, hm'⟩

/-- Concrete `XPost := False` NV: opposite-sign multi-limb `Int` addition
`-(3 * 2^64 - 1) + (2^64 + 5) = -(2 * 2^64 - 6)` yields exact negative (`other = 1`) 2-limb MPZ
`[0xfffffffffffffffa, 1]`. -/
theorem nv_bn_int_add_opp_sign :
    Func.wp rtR1Env lcnf_int_op.body
      (nvBnRtBase, 4#64, nvBnAddrIntNegA, nvBnAddrIntPosB, ()) nvBnMem
      (fun r m' =>
        ∃ st' scrLimbs' objs' obj,
          (r.1 &&& 1#64) = 0#64 ∧ obj ∈ objs' ∧ obj.addr = r.1 ∧
          obj.tag = mpzTag ∧ obj.other = 1 ∧ obj.arrSize = 2 ∧
          obj.limbs = [0xfffffffffffffffa#64, 1#64] ∧
          (bigNumRtInv nvBnRtBase st' nvBnScr scrLimbs' ⋆ lcnfHeap objs') m')
      (fun _ _ _ _ => False) := by
  refine lcnf_int_op_sound _ _ _ _ ?_
  refine ⟨nvBnRtState, nvBnScr, nvBnScrLimbs, nvBnObjs, emp, nvBnRtWf,
    by rw [sep_emp]; exact nvBnMem_ok, ?_⟩
  have hnconv : ¬((4#64 : BitVec 64).toNat ∈ [1, 2, 3, 9, 13, 16]) := by decide
  have has : (4#64 : BitVec 64).toNat ∈ [4, 5, 10, 11, 12] := by decide
  simp only [hnconv, has, ↓reduceIte]
  refine ⟨nvBnRtState, nvBnScr, nvBnScrLimbs, nvBnObjs, nvValIntNegA, nvValIntPosB, emp,
    nvBnRtWf, nvBnIntNegA_rep, nvBnIntPosB_rep, ?_, by decide, ?_,
    by rw [sep_emp]; exact nvBnMem_ok, ?_⟩
  · have hcap : nvBnScrLimbs.length = 32 := by simp [nvBnScrLimbs, nvBnScrCap]
    rw [hcap]; decide
  · intro _
    exact ⟨by decide, fun _ => Or.inr (by decide)⟩
  · intro res st' scrLimbs' objs' m' _ _ _ hpost hm'
    rw [sep_emp] at hm'
    have hrep : intRep res (nvValIntNegA + nvValIntPosB) objs' := by simpa using hpost.1
    have hbig : ¬(-(2 ^ 62 : Int) ≤ nvValIntNegA + nvValIntPosB ∧
        nvValIntNegA + nvValIntPosB < (2 ^ 62 : Int)) := by decide
    simp only [intRep, hbig, ↓reduceIte] at hrep
    rcases hrep with ⟨halign, obj, hobjMem, hobjAddr,
      _, htag, _, harr, h1, _, hlast, hval, hneg, _⟩
    have hne : obj.limbs ≠ [] := by intro h; simp [h] at h1
    have hoth : obj.other = 1 := hneg.mpr (by decide)
    have hlimbs : obj.limbs = [0xfffffffffffffffa#64, 1#64] :=
      limbs_eq_two hne hlast (by decide) (by rw [hval]; decide)
    exact ⟨st', scrLimbs', objs', obj, halign, hobjMem, hobjAddr, htag, hoth,
      by rw [harr, hlimbs]; rfl, hlimbs, hm'⟩

/-- Concrete `XPost := False` NV: negative multi-limb Euclidean division
`-(3 * 2^64 - 1) / (2^64 + 5) = -3` yields exact tagged scalar `BitVec.ofInt 64 (-5)`. -/
theorem nv_bn_int_ediv_neg :
    Func.wp rtR1Env lcnf_int_op.body
      (nvBnRtBase, 7#64, nvBnAddrIntNegA, nvBnAddrIntPosB, ()) nvBnMem
      (fun r m' =>
        r.1 = BitVec.ofInt 64 (-5) ∧
        ∃ st' scrLimbs' objs',
          (bigNumRtInv nvBnRtBase st' nvBnScr scrLimbs' ⋆ lcnfHeap objs') m')
      (fun _ _ _ _ => False) := by
  refine lcnf_int_op_sound _ _ _ _ ?_
  refine ⟨nvBnRtState, nvBnScr, nvBnScrLimbs, nvBnObjs, emp, nvBnRtWf,
    by rw [sep_emp]; exact nvBnMem_ok, ?_⟩
  have hnconv : ¬((7#64 : BitVec 64).toNat ∈ [1, 2, 3, 9, 13, 16]) := by decide
  have hnas : ¬((7#64 : BitVec 64).toNat ∈ [4, 5, 10, 11, 12]) := by decide
  have hmd : (7#64 : BitVec 64).toNat ∈ [6, 7, 8, 14, 15] := by decide
  simp only [hnconv, hnas, hmd, ↓reduceIte]
  refine ⟨nvBnRtState, nvBnScr, nvBnScrLimbs, nvBnObjs, nvValIntNegA, nvValIntPosB, emp,
    nvBnRtWf, nvBnIntNegA_rep, nvBnIntPosB_rep, by decide, ?_, by decide,
    fun _ => Or.inr (by decide), by rw [sep_emp]; exact nvBnMem_ok, ?_⟩
  · have hcap : nvBnScrLimbs.length = 32 := by simp [nvBnScrLimbs, nvBnScrCap]
    rw [hcap]; decide
  · intro res st' scrLimbs' objs' m' _ _ _ hrep _ hm'
    rw [sep_emp] at hm'
    have hval : intMulDivRes (7#64 : BitVec 64).toNat nvValIntNegA nvValIntPosB = -3 := by decide
    rw [hval] at hrep
    have hsm : -(2 ^ 62 : Int) ≤ (-3 : Int) ∧ (-3 : Int) < (2 ^ 62 : Int) := by decide
    simp only [intRep, hsm] at hrep
    exact ⟨hrep, st', scrLimbs', objs', hm'⟩

/-- Concrete `XPost := False` NV: negative multi-limb Euclidean remainder
`-(3 * 2^64 - 1) % (2^64 + 5) = 16` yields exact tagged scalar `33#64`. -/
theorem nv_bn_int_emod_neg :
    Func.wp rtR1Env lcnf_int_op.body
      (nvBnRtBase, 8#64, nvBnAddrIntNegA, nvBnAddrIntPosB, ()) nvBnMem
      (fun r m' =>
        r.1 = 33#64 ∧
        ∃ st' scrLimbs' objs',
          (bigNumRtInv nvBnRtBase st' nvBnScr scrLimbs' ⋆ lcnfHeap objs') m')
      (fun _ _ _ _ => False) := by
  refine lcnf_int_op_sound _ _ _ _ ?_
  refine ⟨nvBnRtState, nvBnScr, nvBnScrLimbs, nvBnObjs, emp, nvBnRtWf,
    by rw [sep_emp]; exact nvBnMem_ok, ?_⟩
  have hnconv : ¬((8#64 : BitVec 64).toNat ∈ [1, 2, 3, 9, 13, 16]) := by decide
  have hnas : ¬((8#64 : BitVec 64).toNat ∈ [4, 5, 10, 11, 12]) := by decide
  have hmd : (8#64 : BitVec 64).toNat ∈ [6, 7, 8, 14, 15] := by decide
  simp only [hnconv, hnas, hmd, ↓reduceIte]
  refine ⟨nvBnRtState, nvBnScr, nvBnScrLimbs, nvBnObjs, nvValIntNegA, nvValIntPosB, emp,
    nvBnRtWf, nvBnIntNegA_rep, nvBnIntPosB_rep, by decide, ?_, by decide,
    fun _ => Or.inr (by decide), by rw [sep_emp]; exact nvBnMem_ok, ?_⟩
  · have hcap : nvBnScrLimbs.length = 32 := by simp [nvBnScrLimbs, nvBnScrCap]
    rw [hcap]; decide
  · intro res st' scrLimbs' objs' m' _ _ _ hrep _ hm'
    rw [sep_emp] at hm'
    have hval : intMulDivRes (8#64 : BitVec 64).toNat nvValIntNegA nvValIntPosB = 16 := by decide
    rw [hval] at hrep
    have hsm : -(2 ^ 62 : Int) ≤ (16 : Int) ∧ (16 : Int) < (2 ^ 62 : Int) := by decide
    simp only [intRep, hsm] at hrep
    exact ⟨hrep, st', scrLimbs', objs', hm'⟩

end LeanQbe.T.LeanLCNF
