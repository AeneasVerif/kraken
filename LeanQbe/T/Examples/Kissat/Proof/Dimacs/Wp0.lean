/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Dimacs.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
public import LeanQbe.T.Examples.Kissat.Src.Dimacs
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep

/-!
# Soundness Proofs for `Kissat.Src.Dimacs` Lexer (`Proof.Dimacs.Wp0`)

Proves parametric `(Γ : Env)` `Func.wp` theorems for the first `5` lexer primitives in
`Src.Dimacs.fns`:
1. `kissat_is_ws_wp`
2. `kissat_is_digit_wp`
3. `kissat_skip_ws_comments_wp`
4. `kissat_skip_ws1_wp`
5. `kissat_read_nat_wp`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Dimacs

open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Dimacs
open Kraken.Bedrock2.Test

private theorem u8_zext64_ofNat (b : UInt8) :
    (BitVec.ofNat 8 b.toNat).setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hb := b.toNat_lt
  omega

private theorem wp_load_bytes_at {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {base p : BitVec 64} {bs : List UInt8} {i : Nat} {R : Mem 64 → Prop}
    {k : Val i8 → Expr Val Cont rs}
    (hp : p = base + BitVec.ofNat 64 i) (hi : i < bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m)
    (hk : wp Γ Q X (k (BitVec.ofNat 8 bs[i].toNat)) m) :
    wp Γ Q X (.load i8 (Arg.var p) k) m := by
  subst hp
  exact wp_load_of (load_bytes_at hi hlen hm) hk

private theorem bv64_add1_eq_add_succ {ptr : BitVec 64} {k : Nat} :
    ptr + BitVec.ofNat 64 k + 1 = ptr + BitVec.ofNat 64 (k + 1) := by
  rw [BitVec.add_assoc, show BitVec.ofNat 64 k + (1 : BitVec 64) =
    BitVec.ofNat 64 (k + 1) from (BitVec.ofNat_add k 1).symm]

private theorem isWsWord_true_of (b : BitVec 64)
    (h : b = 32#64 ∨ (9 ≤ b.toNat ∧ b.toNat ≤ 13)) : isWsWord b = true := by
  unfold isWsWord BitVec.ule
  rcases h with rfl | ⟨h9, h13⟩
  · decide
  · simp [h9, h13]

private theorem isWsWord_false_of (b : BitVec 64)
    (h1 : b ≠ 32#64) (h2 : ¬ (9 ≤ b.toNat ∧ b.toNat ≤ 13)) : isWsWord b = false := by
  unfold isWsWord BitVec.ule
  simp [h1]; omega

private theorem isDigitWord_true_of (b : BitVec 64) (h1 : 48 ≤ b.toNat) (h2 : b.toNat ≤ 57) :
    isDigitWord b = true := by
  unfold isDigitWord BitVec.ule
  simp [h1, h2]

private theorem isDigitWord_false_of (b : BitVec 64) (h : ¬ (48 ≤ b.toNat ∧ b.toNat ≤ 57)) :
    isDigitWord b = false := by
  unfold isDigitWord BitVec.ule
  simp; omega

/-- Soundness proof for `kissat_is_ws`. -/
theorem kissat_is_ws_wp (Γ : Env) :
    ∀ a m Q X, Spec.kissatIsWsSpec a m Q X → Func.wp Γ kissat_is_ws_body a m Q X := by
  rintro ⟨b, ⟨⟩⟩ m Q X hQ
  unfold Func.wp kissat_is_ws_body
  c0_hsteps_nogrp
  refine wp_join_group (ts := [.bool])
    (fun (r, ()) mr => r = isWsWord b ∧ mr = m) ?_ ?_
  · rintro _ ⟨r, ⟨⟩⟩ mr ⟨rfl, rfl⟩
    rw [Blocks.get_here]; dsimp only
    c0_hsteps_nogrp
    exact hQ
  · intro J hJ
    c0_hsteps_nogrp
    · exact hJ (true, ()) m ⟨(isWsWord_true_of b (Or.inl (by assumption))).symm, rfl⟩
    · exact hJ (true, ()) m
        ⟨(isWsWord_true_of b (Or.inr ⟨by c0_bound, by c0_bound⟩)).symm, rfl⟩
    · exact hJ (false, ()) m
        ⟨(isWsWord_false_of b (by assumption) (fun ⟨_, _⟩ => by c0_bound)).symm, rfl⟩
    · exact hJ (false, ()) m
        ⟨(isWsWord_false_of b (by assumption) (fun ⟨_, _⟩ => by c0_bound)).symm, rfl⟩

/-- Soundness proof for `kissat_is_digit`. -/
theorem kissat_is_digit_wp (Γ : Env) :
    ∀ a m Q X, Spec.kissatIsDigitSpec a m Q X → Func.wp Γ kissat_is_digit_body a m Q X := by
  rintro ⟨b, ⟨⟩⟩ m Q X hQ
  unfold Func.wp kissat_is_digit_body
  refine wp_join_group (ts := [.bool])
    (fun (r, ()) mr => r = isDigitWord b ∧ mr = m) ?_ ?_
  · rintro _ ⟨r, ⟨⟩⟩ mr ⟨rfl, rfl⟩
    rw [Blocks.get_here]; dsimp only
    c0_hsteps_nogrp
    exact hQ
  · intro J hJ
    c0_hsteps_nogrp
    · exact hJ (true, ()) m ⟨(isDigitWord_true_of b (by c0_bound) (by c0_bound)).symm, rfl⟩
    · refine hJ (false, ()) m ⟨(isDigitWord_false_of b (fun ⟨_, _⟩ => by c0_bound)).symm, rfl⟩
    · refine hJ (false, ()) m ⟨(isDigitWord_false_of b (fun ⟨_, _⟩ => by c0_bound)).symm, rfl⟩

private theorem skipWsCommentsAux_false_cons (b : UInt8) (bs : List UInt8) :
    skipWsCommentsAux false (b :: bs) =
      if isDimacsWs b then skipWsCommentsAux false bs
      else if b == 99 then skipWsCommentsAux true bs else b :: bs := rfl

private theorem skipWsComments_drop_ws {bs : List UInt8} {k : Nat}
    (hk : k < bs.length) (hws : isDimacsWs bs[k] = true) :
    skipWsComments (bs.drop (k + 1)) = skipWsComments (bs.drop k) := by
  rw [List.drop_eq_getElem_cons hk]
  simp only [skipWsComments, skipWsCommentsAux_false_cons, hws, ↓reduceIte]

private theorem skipWsComments_drop_comment {bs : List UInt8} {k : Nat}
    (hk : k < bs.length) (hc : bs[k] = 99) :
    skipWsCommentsAux true (bs.drop (k + 1)) = skipWsComments (bs.drop k) := by
  rw [List.drop_eq_getElem_cons hk]
  have hnw : isDimacsWs 99 = false := by decide
  simp only [skipWsComments, skipWsCommentsAux_false_cons, hc, hnw, beq_self_eq_true,
    Bool.false_eq_true, ↓reduceIte]

private theorem skipWsComments_drop_stop {bs : List UInt8} {k : Nat}
    (hk : k < bs.length) (hnw : isDimacsWs bs[k] = false) (hnc : bs[k] ≠ 99) :
    skipWsComments (bs.drop k) = bs.drop k := by
  unfold skipWsComments
  rw [List.drop_eq_getElem_cons hk, skipWsCommentsAux_false_cons, hnw]
  simp [hnc]

private theorem skipWsCommentsAux_true_step {bs : List UInt8} {k : Nat}
    (hk : k < bs.length) :
    (if bs[k] = 10 then skipWsComments (bs.drop (k + 1))
      else skipWsCommentsAux true (bs.drop (k + 1))) =
    skipWsCommentsAux true (bs.drop k) := by
  rw [List.drop_eq_getElem_cons hk]
  by_cases h10 : bs[k] = 10
  · simp only [h10, ↓reduceIte]
    rfl
  · simp only [h10, ↓reduceIte]
    symm
    exact skipWsCommentsAux.eq_3 _ _ h10

private theorem skipWsCommentsAux_true_eof {bs : List UInt8} {k : Nat}
    (hk : k = bs.length) :
    skipWsCommentsAux true (bs.drop k) = [] := by
  subst hk; simp [skipWsCommentsAux]

private theorem skipWsComments_eof {bs : List UInt8} {k : Nat}
    (hk : k = bs.length) :
    skipWsComments (bs.drop k) = [] := by
  subst hk; simp [skipWsComments, skipWsCommentsAux]

private theorem drop_succ_eq_self_drop {bs : List UInt8} {k : Nat} (hk : k < bs.length) :
    bs.drop (k + 1) = (bs.drop k).tail := by
  rw [List.drop_eq_getElem_cons hk, List.tail_cons]

/-- Soundness proof for `kissat_skip_ws_comments`. -/
theorem kissat_skip_ws_comments_wp (Γ : Env)
    (hWs : Γ.Has "kissat_is_ws" Spec.kissatIsWsSpec) :
    ∀ a m Q X, Spec.kissatSkipWsCommentsSpec a m Q X →
      Func.wp Γ kissat_skip_ws_comments_body a m Q X := by
  rintro ⟨p, cend, ⟨⟩⟩ m Q X ⟨ptr, bs, i0, R, rfl, rfl, hbound, hi0, hm, hQ⟩
  unfold Func.wp kissat_skip_ws_comments_body
  c0_hsteps
  refine wp_loop_inv (ts := [i64])
    (fun (q, ()) mL =>
      ∃ k, i0 ≤ k ∧ k ≤ bs.length ∧ q = ptr + BitVec.ofNat 64 k ∧
      skipWsComments (bs.drop k) = skipWsComments (bs.drop i0) ∧ mL = m)
    (fun (q, ()) _ => ((ptr + BitVec.ofNat 64 bs.length) - q).toNat)
    (fun J hLoop => ?_)
    (fun J (q, ()) mL ⟨k, hik, hkl, hq_eq, hdrop, hmL⟩ hLoop => ?_)
  · c0_hsteps
    exact hLoop (ptr + BitVec.ofNat 64 i0, ()) m ⟨i0, Nat.le_refl _, hi0, rfl, rfl, rfl⟩
  · subst hq_eq; subst mL
    rw [Blocks.get_here]; dsimp only
    c0_hstep
    rw [cursor_ult_eq (by omega) hkl]
    c0_hsteps_nogrp
    · have hk_lt : k < bs.length := by c0_bound
      refine wp_load_bytes_at rfl hk_lt (by omega) hm ?_
      c0_hsteps_nogrp
      rw [u8_zext64_ofNat]
      refine wp_join_group (ts := [i64])
        (fun (q', ()) m' =>
          ∃ k', k < k' ∧ k' ≤ bs.length ∧ q' = ptr + BitVec.ofNat 64 k' ∧
          skipWsComments (bs.drop k') = skipWsComments (bs.drop i0) ∧ m' = m) ?_ ?_
      · rintro _ ⟨q', ⟨⟩⟩ m' ⟨k', hkk', hk'l, rfl, hdrop', hm'⟩
        subst m'
        rw [Blocks.get_here]; dsimp only
        c0_hsteps
        refine hLoop (ptr + BitVec.ofNat 64 k', ()) m ?_
          ⟨k', by omega, hk'l, rfl, hdrop', rfl⟩
        dsimp only
        rw [cursor_sub_eq hbound hk'l, cursor_sub_eq hbound (Nat.le_of_lt hk_lt)]
        bv_omega
      · intro Jc hJc
        c0_call hWs
        refine ?_
        · show Spec.kissatIsWsSpec (BitVec.ofNat 64 bs[k].toNat, ()) m _ _
          simp only [Spec.kissatIsWsSpec]
          c0_hsteps_nogrp
          · have hws : isDimacsWs bs[k] = true :=
              (isWsWord_ofUInt8 bs[k]).symm.trans (by assumption)
            c0_hsteps
            refine hJc (ptr + BitVec.ofNat 64 k + 1, ()) m
              ⟨k + 1, Nat.lt_succ_self _, hk_lt, bv64_add1_eq_add_succ, ?_, rfl⟩
            rw [skipWsComments_drop_ws hk_lt hws, hdrop]
          · have hnw : isDimacsWs bs[k] = false :=
              (isWsWord_ofUInt8 bs[k]).symm.trans (by assumption)
            have hc99 : bs[k] = 99 := by
              have hb : BitVec.ofNat 64 bs[k].toNat = 99#64 := by assumption
              exact bv64_u8_eq.mp hb
            refine wp_join_group (ts := [i64])
              (fun (q', ()) m' =>
                ∃ k', k < k' ∧ k' ≤ bs.length ∧ q' = ptr + BitVec.ofNat 64 k' ∧
                skipWsComments (bs.drop k') = skipWsComments (bs.drop i0) ∧ m' = m) ?_ ?_
            · rintro _ ⟨q', ⟨⟩⟩ m' hinv'
              rw [Blocks.get_here]; dsimp only
              c0_hsteps
              exact hJc (q', ()) m' hinv'
            · intro Jd hJd
              refine wp_loop_inv (ts := [i64])
                (fun (r, ()) mr =>
                  ∃ k', k + 1 ≤ k' ∧ k' ≤ bs.length ∧ r = ptr + BitVec.ofNat 64 k' ∧
                  skipWsCommentsAux true (bs.drop k') = skipWsComments (bs.drop i0) ∧ mr = m)
                (fun (r, ()) _ => ((ptr + BitVec.ofNat 64 bs.length) - r).toNat)
                (fun Jcm hLcm => ?_)
                (fun Jcm (r, ()) mr ⟨k', hk'1, hk'l, hr_eq, hdrop', hmr⟩ hLcm => ?_)
              · c0_hsteps
                refine hLcm (ptr + BitVec.ofNat 64 k + 1, ()) m
                  ⟨k + 1, Nat.le_refl _, hk_lt, bv64_add1_eq_add_succ, ?_, rfl⟩
                rw [skipWsComments_drop_comment hk_lt hc99, hdrop]
              · subst hr_eq; subst mr
                rw [Blocks.get_here]; dsimp only
                c0_hstep
                rw [cursor_ult_eq (by omega) hk'l]
                c0_hsteps_nogrp
                · have hk'_lt : k' < bs.length := by c0_bound
                  refine wp_load_bytes_at rfl hk'_lt (by omega) hm ?_
                  c0_hsteps_nogrp
                  · have hc10 : bs[k'] = 10 := by
                      have hb : (BitVec.ofNat 8 bs[k'].toNat).setWidth 64 = 10#64 := by assumption
                      rw [u8_zext64_ofNat] at hb
                      exact bv64_u8_eq.mp hb
                    c0_hsteps
                    refine hJd (ptr + BitVec.ofNat 64 k' + 1, ()) m
                      ⟨k' + 1, by omega, hk'_lt, bv64_add1_eq_add_succ, ?_, rfl⟩
                    have hs := skipWsCommentsAux_true_step hk'_lt
                    simp only [hc10, ↓reduceIte] at hs
                    rw [hs, hdrop']
                  · have hne10 : bs[k'] ≠ 10 := fun h => by
                      have hb : (BitVec.ofNat 8 bs[k'].toNat).setWidth 64 = 10#64 := by
                        rw [u8_zext64_ofNat, h]; rfl
                      exact (by assumption :
                        (BitVec.ofNat 8 bs[k'].toNat).setWidth 64 ≠ 10#64) hb
                    c0_hsteps
                    refine hLcm (ptr + BitVec.ofNat 64 k' + 1, ()) m ?_
                      ⟨k' + 1, by omega, hk'_lt, bv64_add1_eq_add_succ, ?_, rfl⟩
                    · dsimp only
                      rw [bv64_add1_eq_add_succ, cursor_sub_eq hbound hk'_lt,
                        cursor_sub_eq hbound (Nat.le_of_lt hk'_lt)]
                      bv_omega
                    · have hs := skipWsCommentsAux_true_step hk'_lt
                      simp only [hne10, ↓reduceIte] at hs
                      rw [hs, hdrop']
                · have hk'_eq : k' = bs.length := by c0_bound
                  c0_hsteps
                  refine hJd (ptr + BitVec.ofNat 64 k', ()) m
                    ⟨k', by omega, hk'l, rfl, ?_, rfl⟩
                  rw [skipWsComments_eof hk'_eq, ← hdrop', skipWsCommentsAux_true_eof hk'_eq]
          · have hnw : isDimacsWs bs[k] = false :=
              (isWsWord_ofUInt8 bs[k]).symm.trans (by assumption)
            have hnc99 : bs[k] ≠ 99 := fun h => by
              have hb : BitVec.ofNat 64 bs[k].toNat = 99#64 := by rw [h]; rfl
              exact (by assumption : BitVec.ofNat 64 bs[k].toNat ≠ 99#64) hb
            c0_hsteps
            refine hQ k hik hkl ?_
            rw [← hdrop, skipWsComments_drop_stop hk_lt hnw hnc99]
    · have hk_eq : k = bs.length := by c0_bound
      c0_hsteps
      refine hQ k hik hkl ?_
      rw [← hdrop, skipWsComments_eof hk_eq, hk_eq, List.drop_length]

open Std.ExtHashMap in
private theorem sep_mid_to_front {P Q R : Mem 64 → Prop} {m : Mem 64}
    (h : (P ⋆ Q ⋆ R) m) : (Q ⋆ (P ⋆ R)) m := by
  rw [sep_comm P Q, sep_assoc] at h
  exact h

open Std.ExtHashMap in
private theorem sep_front_to_mid {P Q R : Mem 64 → Prop} {m : Mem 64}
    (h : (Q ⋆ (P ⋆ R)) m) : (P ⋆ Q ⋆ R) m := by
  rw [← sep_assoc, sep_comm Q P] at h
  exact h

private theorem wp_load_d_cur {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {cnf_ptr : BitVec 64} {d mv nc cur val : Val i64} {bs : List UInt8} {R : Mem 64 → Prop}
    {k : Val i64 → Expr Val Cont rs}
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m)
    (hk : wp Γ Q X (k cur) m) :
    wp Γ Q X (.load i64 (Arg.var (d + 16)) k) m := by
  refine wp_load_of ?_ hk
  simpa only [Arg.val_var] using load_dimacs_cur (sep_mid_to_front hm)

private theorem wp_store_d_cur {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {cnf_ptr : BitVec 64} {d mv nc cur val cur' : Val i64} {bs : List UInt8} {R : Mem 64 → Prop}
    {k : Expr Val Cont rs}
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m)
    (hk : ∀ m', (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur' val ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store (Arg.var cur') (Arg.var (d + 16)) k) m := by
  refine wp_store_sep ?_ fun m' hm' => hk m' (sep_front_to_mid hm')
  simpa only [Arg.val_var] using store_dimacs_cur cur' (sep_mid_to_front hm)

private theorem wp_store_d_val {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {cnf_ptr : BitVec 64} {d mv nc cur val val' : Val i64} {bs : List UInt8} {R : Mem 64 → Prop}
    {k : Expr Val Cont rs}
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m)
    (hk : ∀ m', (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val' ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store (Arg.var val') (Arg.var (d + 24)) k) m := by
  refine wp_store_sep ?_ fun m' hm' => hk m' (sep_front_to_mid hm')
  simpa only [Arg.val_var] using store_dimacs_val val' (sep_mid_to_front hm)

private theorem skipWs_drop_ws {bs : List UInt8} {k : Nat}
    (hk : k < bs.length) (hws : isDimacsWs bs[k] = true) :
    skipWs (bs.drop (k + 1)) = skipWs (bs.drop k) := by
  rw [List.drop_eq_getElem_cons hk]
  simp only [skipWs, hws, ↓reduceIte]

private theorem skipWs_drop_stop {bs : List UInt8} {k : Nat}
    (hk : k < bs.length) (hnw : isDimacsWs bs[k] = false) :
    skipWs (bs.drop k) = bs.drop k := by
  rw [List.drop_eq_getElem_cons hk]
  simp [skipWs, hnw]

private theorem skipWs_eof {bs : List UInt8} {k : Nat} (hk : k = bs.length) :
    skipWs (bs.drop k) = [] := by
  subst hk; simp [skipWs]

private theorem skipWs1_cons_ws {bs : List UInt8} {i0 : Nat}
    (hi : i0 < bs.length) (hws : isDimacsWs bs[i0] = true) :
    skipWs1 (bs.drop i0) = some (skipWs (bs.drop (i0 + 1))) := by
  rw [List.drop_eq_getElem_cons hi]
  simp [skipWs1, hws]

private theorem skipWs1_cons_nonws {bs : List UInt8} {i0 : Nat}
    (hi : i0 < bs.length) (hnw : isDimacsWs bs[i0] = false) :
    skipWs1 (bs.drop i0) = none := by
  rw [List.drop_eq_getElem_cons hi]
  simp [skipWs1, hnw]

private theorem skipWs1_eof {bs : List UInt8} {i0 : Nat} (hi : i0 = bs.length) :
    skipWs1 (bs.drop i0) = none := by
  subst hi; simp [skipWs1]

/-- Soundness proof for `kissat_skip_ws1`. -/
theorem kissat_skip_ws1_wp (Γ : Env)
    (hWs : Γ.Has "kissat_is_ws" Spec.kissatIsWsSpec) :
    ∀ a m Q X, Spec.kissatSkipWs1Spec a m Q X → Func.wp Γ kissat_skip_ws1_body a m Q X := by
  rintro ⟨cend, d, ⟨⟩⟩ m Q X ⟨cnf_ptr, mv, nc, val, bs, i0, R, rfl, hbound, hi0, hm, hQ⟩
  unfold Func.wp kissat_skip_ws1_body
  c0_hsteps_nogrp
  refine wp_load_d_cur hm ?_
  c0_hstep
  rw [cursor_ule_rev_eq hbound hi0]
  c0_hsteps_nogrp
  · have hi0_eq : i0 = bs.length := by c0_bound
    rw [skipWs1_eof hi0_eq] at hQ
    c0_hsteps
    exact hQ
  · have hi0_lt : i0 < bs.length := by c0_bound
    refine wp_load_bytes_at rfl hi0_lt (by omega)
      (by simpa only [Std.ExtHashMap.sep_assoc] using hm) ?_
    c0_hsteps_nogrp
    rw [u8_zext64_ofNat]
    c0_call hWs
    simp only [Spec.kissatIsWsSpec]
    c0_hsteps_nogrp
    · have hws0 : isDimacsWs bs[i0] = true :=
        (isWsWord_ofUInt8 bs[i0]).symm.trans (by assumption)
      rw [skipWs1_cons_ws hi0_lt hws0] at hQ
      dsimp only at hQ
      c0_hsteps
      refine wp_loop_inv (ts := [i64])
        (fun (q, ()) mL =>
          ∃ k, i0 + 1 ≤ k ∧ k ≤ bs.length ∧ q = cnf_ptr + BitVec.ofNat 64 k ∧
          skipWs (bs.drop k) = skipWs (bs.drop (i0 + 1)) ∧ mL = m)
        (fun (q, ()) _ => ((cnf_ptr + BitVec.ofNat 64 bs.length) - q).toNat)
        (fun J hLoop => ?_)
        (fun J (q, ()) mL ⟨k, hik, hkl, hq_eq, hdrop, hmL⟩ hLoop => ?_)
      · c0_hsteps
        exact hLoop (cnf_ptr + BitVec.ofNat 64 i0 + 1, ()) m
          ⟨i0 + 1, Nat.le_refl _, hi0_lt, bv64_add1_eq_add_succ, rfl, rfl⟩
      · subst hq_eq; subst mL
        rw [Blocks.get_here]; dsimp only
        c0_hstep
        rw [cursor_ult_eq hbound hkl]
        c0_hsteps_nogrp
        · have hk_lt : k < bs.length := by c0_bound
          refine wp_load_bytes_at rfl hk_lt (by omega)
            (by simpa only [Std.ExtHashMap.sep_assoc] using hm) ?_
          c0_hsteps_nogrp
          rw [u8_zext64_ofNat]
          c0_call hWs
          simp only [Spec.kissatIsWsSpec]
          c0_hsteps_nogrp
          · have hws : isDimacsWs bs[k] = true :=
              (isWsWord_ofUInt8 bs[k]).symm.trans (by assumption)
            c0_hsteps
            refine hLoop (cnf_ptr + BitVec.ofNat 64 k + 1, ()) m ?_
              ⟨k + 1, by omega, hk_lt, bv64_add1_eq_add_succ, ?_, rfl⟩
            · dsimp only
              rw [bv64_add1_eq_add_succ, cursor_sub_eq hbound hk_lt,
                cursor_sub_eq hbound (Nat.le_of_lt hk_lt)]
              bv_omega
            · rw [skipWs_drop_ws hk_lt hws, hdrop]
          · have hnw : isDimacsWs bs[k] = false :=
              (isWsWord_ofUInt8 bs[k]).symm.trans (by assumption)
            try c0_hstraight
            refine wp_store_d_cur hm fun m' hm' => ?_
            c0_hsteps
            refine hQ k m' (by omega) hkl ?_ hm'
            rw [← hdrop, skipWs_drop_stop hk_lt hnw]
        · have hk_eq : k = bs.length := by c0_bound
          try c0_hstraight
          refine wp_store_d_cur hm fun m' hm' => ?_
          c0_hsteps
          refine hQ k m' (by omega) hkl ?_ hm'
          rw [← hdrop, skipWs_eof hk_eq, hk_eq, List.drop_length]
    · have hnw0 : isDimacsWs bs[i0] = false :=
        (isWsWord_ofUInt8 bs[i0]).symm.trans (by assumption)
      rw [skipWs1_cons_nonws hi0_lt hnw0] at hQ
      c0_hsteps
      exact hQ

private theorem parseDigitsAux_step_digit {bs : List UInt8} {k acc : Nat}
    (hk : k < bs.length) (hd : isDimacsDigit bs[k] = true)
    (hacc : acc * 10 + (bs[k].toNat - 48) < dimacsBound) :
    parseDigitsAux (acc * 10 + (bs[k].toNat - 48)) (bs.drop (k + 1)) =
      parseDigitsAux acc (bs.drop k) := by
  rw [List.drop_eq_getElem_cons hk]
  simp only [parseDigitsAux, hd, hacc, ↓reduceIte]

private theorem parseDigitsAux_step_overflow {bs : List UInt8} {k acc : Nat}
    (hk : k < bs.length) (hd : isDimacsDigit bs[k] = true)
    (hov : ¬ acc * 10 + (bs[k].toNat - 48) < dimacsBound) :
    parseDigitsAux acc (bs.drop k) = none := by
  rw [List.drop_eq_getElem_cons hk]
  simp only [parseDigitsAux, hd, hov, ↓reduceIte]

private theorem parseDigitsAux_step_ws {bs : List UInt8} {k acc : Nat}
    (hk : k < bs.length) (hnd : isDimacsDigit bs[k] = false) (hws : isDimacsWs bs[k] = true) :
    parseDigitsAux acc (bs.drop k) = some (acc, bs.drop k) := by
  rw [List.drop_eq_getElem_cons hk]
  simp [parseDigitsAux, hnd, hws]

private theorem parseDigitsAux_step_err {bs : List UInt8} {k acc : Nat}
    (hk : k < bs.length) (hnd : isDimacsDigit bs[k] = false) (hnw : isDimacsWs bs[k] = false) :
    parseDigitsAux acc (bs.drop k) = none := by
  rw [List.drop_eq_getElem_cons hk]
  simp [parseDigitsAux, hnd, hnw]

private theorem parseDigitsAux_eof {bs : List UInt8} {k acc : Nat} (hk : k = bs.length) :
    parseDigitsAux acc (bs.drop k) = some (acc, []) := by
  subst hk; simp [parseDigitsAux]

private theorem parseNat_cons_digit {bs : List UInt8} {i0 : Nat}
    (hi : i0 < bs.length) (hd : isDimacsDigit bs[i0] = true) :
    parseNat (bs.drop i0) = parseDigitsAux (bs[i0].toNat - 48) (bs.drop (i0 + 1)) := by
  rw [List.drop_eq_getElem_cons hi]
  simp [parseNat, hd]

private theorem parseNat_cons_nondigit {bs : List UInt8} {i0 : Nat}
    (hi : i0 < bs.length) (hnd : isDimacsDigit bs[i0] = false) :
    parseNat (bs.drop i0) = none := by
  rw [List.drop_eq_getElem_cons hi]
  simp [parseNat, hnd]

private theorem parseNat_eof {bs : List UInt8} {i0 : Nat} (hi : i0 = bs.length) :
    parseNat (bs.drop i0) = none := by
  subst hi; simp [parseNat]

private theorem parseNat_digit_val_bv64 (b : UInt8) (hd : isDimacsDigit b = true) :
    BitVec.ofNat 64 b.toNat - 48#64 = BitVec.ofNat 64 (b.toNat - 48) := by
  have hb48 : 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by
    unfold isDimacsDigit at hd; grind
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      have := b.toNat_lt; omega),
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := b.toNat_lt
  omega

private theorem parseNat_acc_step_bv64 {acc : Nat} {b : UInt8}
    (hd : isDimacsDigit b = true) :
    BitVec.ofNat 64 acc * 10#64 + (BitVec.ofNat 64 b.toNat - 48#64) =
      BitVec.ofNat 64 (acc * 10 + (b.toNat - 48)) := by
  rw [parseNat_digit_val_bv64 b hd]
  have hb : b.toNat - 48 < 10 := by unfold isDimacsDigit at hd; grind
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

/-- Soundness proof for `kissat_read_nat`. -/
theorem kissat_read_nat_wp (Γ : Env)
    (hWs : Γ.Has "kissat_is_ws" Spec.kissatIsWsSpec)
    (hDig : Γ.Has "kissat_is_digit" Spec.kissatIsDigitSpec) :
    ∀ a m Q X, Spec.kissatReadNatSpec a m Q X → Func.wp Γ kissat_read_nat_body a m Q X := by
  rintro ⟨cend, d, ⟨⟩⟩ m Q X ⟨cnf_ptr, mv, nc, val, bs, i0, R, rfl, hbound, hi0, hm, hQ⟩
  unfold Func.wp kissat_read_nat_body
  c0_hsteps_nogrp
  refine wp_load_d_cur hm ?_
  c0_hstep
  rw [cursor_ule_rev_eq hbound hi0]
  c0_hsteps_nogrp
  · have hi0_eq : i0 = bs.length := by c0_bound
    rw [parseNat_eof hi0_eq] at hQ
    c0_hsteps
    exact hQ
  · have hi0_lt : i0 < bs.length := by c0_bound
    refine wp_load_bytes_at rfl hi0_lt (by omega)
      (by simpa only [Std.ExtHashMap.sep_assoc] using hm) ?_
    c0_hsteps_nogrp
    rw [u8_zext64_ofNat]
    c0_call hDig
    simp only [Spec.kissatIsDigitSpec]
    c0_hsteps_nogrp
    · have hd0 : isDimacsDigit bs[i0] = true :=
        (isDigitWord_ofUInt8 bs[i0]).symm.trans (by assumption)
      have hb0_lt : bs[i0].toNat - 48 < dimacsBound := by
        unfold isDimacsDigit at hd0; unfold dimacsBound; grind
      rw [parseNat_cons_digit hi0_lt hd0] at hQ
      c0_hsteps
      refine wp_loop_inv (ts := [i64, i64])
        (fun (q, acc_bv, ()) mL =>
          ∃ k acc, i0 + 1 ≤ k ∧ k ≤ bs.length ∧ q = cnf_ptr + BitVec.ofNat 64 k ∧
          acc < dimacsBound ∧ acc_bv = BitVec.ofNat 64 acc ∧
          parseDigitsAux acc (bs.drop k) = parseDigitsAux (bs[i0].toNat - 48) (bs.drop (i0 + 1)) ∧
          mL = m)
        (fun (q, _, ()) _ => ((cnf_ptr + BitVec.ofNat 64 bs.length) - q).toNat)
        (fun J hLoop => ?_)
        (fun J (q, acc_bv, ()) mL
            ⟨k, acc, hik, hkl, hq_eq, hacc_lt, hacc_bv, hparse, hmL⟩ hLoop => ?_)
      · c0_hsteps
        change J (cnf_ptr + BitVec.ofNat 64 i0 + 1, BitVec.ofNat 64 (bs[i0].toNat) - 48#64, ()) m
        rw [parseNat_digit_val_bv64 bs[i0] hd0]
        exact hLoop (cnf_ptr + BitVec.ofNat 64 i0 + 1, BitVec.ofNat 64 (bs[i0].toNat - 48), ()) m
          ⟨i0 + 1, bs[i0].toNat - 48, Nat.le_refl _, hi0_lt, bv64_add1_eq_add_succ,
            hb0_lt, rfl, rfl, rfl⟩
      · subst hq_eq; subst hacc_bv; subst mL
        rw [Blocks.get_here]; dsimp only
        c0_hstep
        rw [cursor_ult_eq hbound hkl]
        c0_hsteps_nogrp
        · have hk_lt : k < bs.length := by c0_bound
          refine wp_load_bytes_at rfl hk_lt (by omega)
            (by simpa only [Std.ExtHashMap.sep_assoc] using hm) ?_
          c0_hsteps_nogrp
          rw [u8_zext64_ofNat]
          c0_call hDig
          simp only [Spec.kissatIsDigitSpec]
          c0_hsteps_nogrp
          · have hdk : isDimacsDigit bs[k] = true :=
              (isDigitWord_ofUInt8 bs[k]).symm.trans (by assumption)
            have hb48 : 48 ≤ bs[k].toNat ∧ bs[k].toNat ≤ 57 := by
              unfold isDimacsDigit at hdk; grind
            have hov : ¬ acc * 10 + (bs[k].toNat - 48) < dimacsBound := by
              have hbnd : dimacsBound = 2 ^ 28 := rfl
              have hc' : BitVec.toNat (268435456 : BitVec 64) ≤
                  (acc % 2 ^ 64 * BitVec.toNat (10 : BitVec 64) +
                    (2 ^ 64 - BitVec.toNat (48 : BitVec 64) + bs[k].toNat)) % 2 ^ 64 := by
                assumption
              rw [show BitVec.toNat (268435456 : BitVec 64) = 268435456 from rfl,
                show BitVec.toNat (10 : BitVec 64) = 10 from rfl,
                show BitVec.toNat (48 : BitVec 64) = 48 from rfl] at hc'
              omega
            rw [← hparse, parseDigitsAux_step_overflow hk_lt hdk hov] at hQ
            exact hQ
          · have hdk : isDimacsDigit bs[k] = true :=
              (isDigitWord_ofUInt8 bs[k]).symm.trans (by assumption)
            have hb48 : 48 ≤ bs[k].toNat ∧ bs[k].toNat ≤ 57 := by
              unfold isDimacsDigit at hdk; grind
            have hfit : acc * 10 + (bs[k].toNat - 48) < dimacsBound := by
              have hbnd : dimacsBound = 2 ^ 28 := rfl
              have hc' : ¬ BitVec.toNat (268435456 : BitVec 64) ≤
                  (acc % 2 ^ 64 * BitVec.toNat (10 : BitVec 64) +
                    (2 ^ 64 - BitVec.toNat (48 : BitVec 64) + bs[k].toNat)) % 2 ^ 64 := by
                assumption
              rw [show BitVec.toNat (268435456 : BitVec 64) = 268435456 from rfl,
                show BitVec.toNat (10 : BitVec 64) = 10 from rfl,
                show BitVec.toNat (48 : BitVec 64) = 48 from rfl] at hc'
              omega
            have hstep_bv : BitVec.ofNat 64 acc * 10 + (BitVec.ofNat 64 bs[k].toNat - 48) =
                BitVec.ofNat 64 (acc * 10 + (bs[k].toNat - 48)) := by
              simpa using parseNat_acc_step_bv64 hdk
            rw [bv64_add1_eq_add_succ, hstep_bv]
            refine hLoop (cnf_ptr + BitVec.ofNat 64 (k + 1),
                BitVec.ofNat 64 (acc * 10 + (bs[k].toNat - 48)), ()) m ?_
              ⟨k + 1, acc * 10 + (bs[k].toNat - 48), by omega, hk_lt, rfl, hfit, rfl, ?_, rfl⟩
            · dsimp only
              rw [cursor_sub_eq hbound hk_lt, cursor_sub_eq hbound (Nat.le_of_lt hk_lt)]
              bv_omega
            · rw [parseDigitsAux_step_digit hk_lt hdk hfit, hparse]
          · have hndk : isDimacsDigit bs[k] = false :=
              (isDigitWord_ofUInt8 bs[k]).symm.trans (by assumption)
            c0_call hWs
            simp only [Spec.kissatIsWsSpec]
            c0_hsteps_nogrp
            · have hwk : isDimacsWs bs[k] = true :=
                (isWsWord_ofUInt8 bs[k]).symm.trans (by assumption)
              rw [← hparse, parseDigitsAux_step_ws hk_lt hndk hwk] at hQ
              dsimp only at hQ
              try c0_hstraight
              refine wp_store_d_cur hm fun m1 hm1 => ?_
              try c0_hstraight
              refine wp_store_d_val hm1 fun m2 hm2 => ?_
              c0_hsteps
              exact hQ k m2 hacc_lt (by omega) hkl rfl hm2
            · have hnw : isDimacsWs bs[k] = false :=
                (isWsWord_ofUInt8 bs[k]).symm.trans (by assumption)
              rw [← hparse, parseDigitsAux_step_err hk_lt hndk hnw] at hQ
              c0_hsteps
              exact hQ
        · have hk_eq : k = bs.length := by c0_bound
          rw [← hparse, parseDigitsAux_eof hk_eq] at hQ
          dsimp only at hQ
          try c0_hstraight
          refine wp_store_d_cur hm fun m1 hm1 => ?_
          try c0_hstraight
          refine wp_store_d_val hm1 fun m2 hm2 => ?_
          c0_hsteps
          exact hQ k m2 hacc_lt (by omega) hkl (by rw [hk_eq, List.drop_length]) hm2
    · have hnd0 : isDimacsDigit bs[i0] = false :=
        (isDigitWord_ofUInt8 bs[i0]).symm.trans (by assumption)
      rw [parseNat_cons_nondigit hi0_lt hnd0] at hQ
      c0_hsteps
      exact hQ

end LeanQbe.T.Examples.Kissat.Proof.Dimacs
