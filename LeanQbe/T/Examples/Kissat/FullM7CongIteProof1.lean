module

public import LeanQbe.T.Examples.Kissat.FullM7CongIteProof0

/-!
# Verification of Kissat 4.0.4 Conditional Equivalence Merge (`FullM7CongIteProof1`)

Proves conditional-equivalence extraction, two-pointer merge, top-level
`full_cong_extract_ite_all_m7_wp`, closed `ModuleOk`, and concrete `Mem 64`
UNSAT non-vacuity (`m7_cong_extract_ite_all_nv`) under M1-clean module rules.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7CongIte

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM5CongFix
open LeanQbe.T.Examples.Kissat.FullM6CongSubst (M6GateSeqOk)
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullCongTactics
open Kraken.Bedrock2.Test

attribute [local c0_load] c0_load_arr64 c0_load_arr64_0 c0_load_arr64_zext0
  load_noWks3_arena_len load_noWks3_vals_ptr load_noWks3_wvec_ptr
  load_noWks3_arena_ptr load_noWks3_wstk_ptr load_noWks3_flags_ptr
  load_noWks3_work_stk1_ptr load_noWks3_work_stk2_ptr
  load_noWks3_scratch_buf_ptr load_noWks3_scratch_cap
  c0_load_noWks3_vals c0_load_noWks3_flags c0_load_noWks3_wvec
  c0_load_noWks3_wstk c0_load_noWks3_arena
attribute [local c0_store] c0_store_arr64 c0_store_arr64_0 c0_store_arr64_zext0
  c0_store_noWks3_scratch_buf

/-! ## 4. Conditional Equivalence Extraction (`full_cong_extract_condeq_m7`) -/

def m7ExtractCondeqSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (cb, m, ceq, cap, ()) mem0 Q _ =>
    ∃ (F_cur : List (List Nat)) (cur_vars lit : Nat)
      (cb_xs ceq0 : List (BitVec 64)) (R : Mem 64 → Prop),
      m.toNat ≤ cb_xs.length ∧ cb_xs.length < 2 ^ 61 ∧
      SortedRange64 cb_xs 0 m.toNat ∧
      (∀ k < m.toNat, CondBinElemOk F_cur cur_vars lit (cb_xs[k]?.getD 0#64)) ∧
      ceq0.length = cap.toNat ∧ cap.toNat < 2 ^ 61 ∧
      (array64 cb cb_xs ⋆ array64 ceq ceq0 ⋆ R) mem0 ∧
      ∀ (u : BitVec 64) (ceq' : List (BitVec 64)) mem',
        ceq'.length = cap.toNat → u.toNat ≤ cap.toNat →
        (∀ k < u.toNat, CondEqElemOk F_cur cur_vars lit (ceq'[k]?.getD 0#64)) →
        (array64 cb cb_xs ⋆ array64 ceq ceq' ⋆ R) mem' →
        Q (u, ()) mem'

theorem full_cong_extract_condeq_m7_wp (Γ : Env)
    (hSort : ∀ a m Q X, m7U64SortSpec a m Q X →
      Γ "full_cong_u64_sort_m7" [i64, i64] [] a m Q X)
    (hBsearch : ∀ a m Q X, m7BsearchU64Spec a m Q X →
      Γ "full_cong_bsearch_u64_m7" [i64, i64, i64, i64] [.bool] a m Q X) :
    ∀ args m Q X, m7ExtractCondeqSpec args m Q X →
      Func.wp Γ full_cong_extract_condeq_m7_body args m Q X := by
  rintro ⟨cb, m, ceq, cap, ⟨⟩⟩ mem0 Q X
    ⟨F_cur, cur_vars, lit, cb_xs, ceq0, R, hm_le, hcb_bd, hcb_sort, hcb_ok,
      hceq_len, hcap_bd, hmem0, hQ⟩
  unfold Func.wp full_cong_extract_condeq_m7_body
  -- Main outer loop over cb[0..m) (post-loop sort/dedup lives in the !(i < m) branch)
  refine wp_loop_inv (ts := [i64, i64])
    (fun (d, i, ()) ml => ∃ ceql : List (BitVec 64),
      ceql.length = cap.toNat ∧ d.toNat ≤ cap.toNat ∧ i.toNat ≤ m.toNat ∧
      (∀ k < d.toNat, CondEqElemOk F_cur cur_vars lit (ceql[k]?.getD 0#64)) ∧
      (array64 cb cb_xs ⋆ array64 ceq ceql ⋆ R) ml)
    (fun (_, i, ()) _ => m.toNat - i.toNat)
    (fun J1 hJ1 => by
      fc_steps
      exact hJ1 (0#64, 0#64, ()) mem0 ⟨ceq0, hceq_len, Nat.zero_le _, Nat.zero_le _,
        fun k hk => by simp at hk, hmem0⟩)
    (fun J1 ⟨d, i, ⟨⟩⟩ ml ⟨ceql, hcl_len, hd_le, hi_le, hceql_ok, hml⟩ ih1 => ?_)
  fc_split_fast
  · have hi_lt : i.toNat < m.toNat := by
      simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
    have hi_arr : i.toNat < cb_xs.length := by omega
    have hip1_n : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
    fc_steps
    fc_split_fast
    · -- Odd `a`: advance `j`
      refine wp_loop_inv (ts := [i64])
        (fun (j, ()) mj => i.toNat < j.toNat ∧ j.toNat ≤ m.toNat ∧ mj = ml)
        (fun (j, ()) _ => m.toNat - j.toNat)
        (fun Jj hJj => by fc_steps; exact hJj (i + 1#64, ()) ml ⟨by omega, by omega, rfl⟩)
        (fun Jj ⟨j, ⟨⟩⟩ mj ⟨hij, hjm, hmj⟩ ihj => ?_)
      subst mj
      fc_split_fast
      · have hj_lt : j.toNat < m.toNat := by
          simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
        clear hc
        have hj_arr : j.toNat < cb_xs.length := by omega
        have hjp1_n : (j + 1#64).toNat = j.toNat + 1 := by bv_omega
        fc_steps
        fc_split_fast
        · fc_steps; exact ihj (j + 1#64, ()) ml (by dsimp only; omega) ⟨by omega, by omega, rfl⟩
        · fc_steps
          exact ih1 (d, j, ()) ml (by dsimp only; omega)
            ⟨ceql, hcl_len, hd_le, hjm, hceql_ok, hml⟩
      · fc_steps
        exact ih1 (d, j, ()) ml (by dsimp only; omega)
          ⟨ceql, hcl_len, hd_le, hjm, hceql_ok, hml⟩
    · -- Even `a`
      obtain ⟨a, ha_def⟩ : ∃ a : BitVec 32,
          a = (cb_xs[i.toNat]'hi_arr >>> (32 : Nat)).setWidth 32 := ⟨_, rfl⟩
      have ha_even : a &&& 1#32 = 0#32 := by
        rw [ha_def]; exact beq_iff_eq.mp (by simpa using hc)
      clear hc
      have hopp_eq : (a ||| 1#32) = (a ^^^ 1#32) := bv32_lit_xor1_even_or' ha_even
      fc_to_group
      refine wp_loop_inv (ts := [i64])
        (fun (pe, ()) mp => i.toNat < pe.toNat ∧ pe.toNat ≤ m.toNat ∧
          (∀ p, i.toNat ≤ p → p < pe.toNat →
            (cb_xs[p]?.getD 0#64 >>> (32 : Nat)).setWidth 32 = a) ∧ mp = ml)
        (fun (pe, ()) _ => m.toNat - pe.toNat)
        (fun Jpe hJpe => by
          fc_steps
          refine hJpe (i + 1#64, ()) ml ⟨by omega, by omega, fun p hp1 hp2 => ?_, rfl⟩
          rw [hip1_n] at hp2
          obtain rfl : p = i.toNat := by omega
          rw [List.getElem?_eq_getElem hi_arr, Option.getD_some, ha_def])
        (fun Jpe ⟨pe, ⟨⟩⟩ mp ⟨hipe, hpem, hpe_a, hmp⟩ ihpe => ?_)
      subst mp
      refine wp_join_group (ts := [])
        (fun _ m_ap => m_ap = ml)
        (fun _ _ m_ap hm_ap => ?_)
        (fun Jap hJap => ?_)
      · subst m_ap
        fc_steps
        refine wp_loop_inv (ts := [i64])
          (fun (ne, ()) mn => pe.toNat ≤ ne.toNat ∧ ne.toNat ≤ m.toNat ∧
            (∀ p, pe.toNat ≤ p → p < ne.toNat →
              (cb_xs[p]?.getD 0#64 >>> (32 : Nat)).setWidth 32 = (a ||| 1#32)) ∧ mn = ml)
          (fun (ne, ()) _ => m.toNat - ne.toNat)
          (fun Jne hJne => by
            fc_steps
            exact hJne (pe, ()) ml ⟨Nat.le_refl _, hpem, fun _ h1 h2 => by omega, rfl⟩)
          (fun Jne ⟨ne, ⟨⟩⟩ mn ⟨hpne, hnem, hne_a, hmn⟩ ihne => ?_)
        subst mn
        refine wp_join_group (ts := [])
          (fun _ m_an => m_an = ml)
          (fun _ _ m_an hm_an => ?_)
          (fun Jan hJan => ?_)
        · subst m_an
          fc_to_group
          refine wp_join_group (ts := [i64])
            (fun (dn, ()) mn => ∃ ceqn : List (BitVec 64),
              ceqn.length = cap.toNat ∧ dn.toNat ≤ cap.toNat ∧
              (∀ k < dn.toNat, CondEqElemOk F_cur cur_vars lit (ceqn[k]?.getD 0#64)) ∧
              (array64 cb cb_xs ⋆ array64 ceq ceqn ⋆ R) mn)
            (fun _ ⟨dn, ⟨⟩⟩ mn ⟨ceqn, hcn_len, hdn_le, hcn_ok, hmn⟩ => ?_)
            (fun Jdn0 hJdn0 => ?_)
          · fc_steps
            exact ih1 (dn, ne, ()) mn (by dsimp only; omega)
              ⟨ceqn, hcn_len, hdn_le, hnem, hcn_ok, hmn⟩
          · fc_split_fast
            · clear hc -- `nneg > 0`
              refine wp_join_group (ts := [i64])
                (fun (dn, ()) mn => ∃ ceqn : List (BitVec 64),
                  ceqn.length = cap.toNat ∧ dn.toNat ≤ cap.toNat ∧
                  (∀ k < dn.toNat, CondEqElemOk F_cur cur_vars lit (ceqn[k]?.getD 0#64)) ∧
                  (array64 cb cb_xs ⋆ array64 ceq ceqn ⋆ R) mn)
                (fun _ ⟨dn, ⟨⟩⟩ mn ⟨ceqn, hcn_len, hdn_le, hcn_ok, hmn⟩ => ?_)
                (fun Jdn hJdn => ?_)
              · fc_steps
                exact hJdn0 (dn, ()) mn ⟨ceqn, hcn_len, hdn_le, hcn_ok, hmn⟩
              · fc_split_fast
                · clear hc -- `npos <= nneg`: scan k in [i, pe), bsearch [pe, ne)
                  refine wp_loop_inv (ts := [i64, i64])
                    (fun (dk, k, ()) mk => ∃ ceqk : List (BitVec 64),
                      ceqk.length = cap.toNat ∧ dk.toNat ≤ cap.toNat ∧
                      i.toNat ≤ k.toNat ∧ k.toNat ≤ pe.toNat ∧
                      (∀ r < dk.toNat, CondEqElemOk F_cur cur_vars lit (ceqk[r]?.getD 0#64)) ∧
                      (array64 cb cb_xs ⋆ array64 ceq ceqk ⋆ R) mk)
                    (fun (_, k, ()) _ => pe.toNat - k.toNat)
                    (fun Jk hJk => by
                      fc_steps
                      exact hJk (d, i, ()) ml ⟨ceql, hcl_len, hd_le, Nat.le_refl _, by omega,
                        hceql_ok, hml⟩)
                    (fun Jk ⟨dk, k, ⟨⟩⟩ mk
                      ⟨ceqk, hck_len, hdk_le, hik, hkpe, hck_ok, hmk⟩ ihk => ?_)
                  fc_split_fast
                  · have hk_lt : k.toNat < pe.toNat := by
                      simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                    clear hc
                    have hk_arr : k.toNat < cb_xs.length := by omega
                    have hkp1_n : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
                    fc_steps
                    try rw [← ha_def]
                    let wk := cb_xs[k.toNat]'hk_arr
                    let b := wk.setWidth 32
                    let not_b := b ^^^ 1#32
                    let key := ((a ||| 1#32).setWidth 64 <<< 32#64) ||| not_b.setWidth 64
                    have hkey_def :
                        key = ((a ||| 1#32).setWidth 64 <<< 32#64) ||| not_b.setWidth 64 :=
                      rfl
                    refine wp_call_of_spec _ _ (hBsearch (cb, pe, ne, _, ()) mk _ X
                      (m7BsearchU64Spec_mk cb_xs (array64 ceq ceqk ⋆ R) hpne (by omega) (by omega)
                        (sortedRange64_sub hcb_sort (by omega) (by omega)) (sep_ac hmk)
                        fun found hfound => ?_))
                    have hnext_ok : ∀ ceq' (dk' : BitVec 64) m',
                        ceq'.length = cap.toNat → dk'.toNat ≤ cap.toNat →
                        (∀ r < dk'.toNat, CondEqElemOk F_cur cur_vars lit (ceq'[r]?.getD 0#64)) →
                        (array64 cb cb_xs ⋆ array64 ceq ceq' ⋆ R) m' →
                        Jk (dk', k + 1#64, ()) m' := fun ceq' dk' m' hl hd hok hm' =>
                      ihk (dk', k + 1#64, ()) m' (by dsimp only; omega)
                        ⟨ceq', hl, hd, by omega, by omega, hok, hm'⟩
                    fc_split_fast
                    · obtain ⟨idx, hid1, hid2, hid_get⟩ := hfound.mp (by simpa using hc)
                      clear hc
                      have hid_get_k : cb_xs[idx]? = some key := by
                        simpa [key, wk, b, not_b, ← ha_def] using hid_get
                      have hcbk := hcb_ok k.toNat (by omega)
                      rw [List.getElem?_eq_getElem hk_arr, Option.getD_some] at hcbk
                      have hcb_idx := hcb_ok idx (by omega)
                      rw [hid_get_k, Option.getD_some] at hcb_idx
                      have hwk_hi : (wk >>> 32).toNat = a.toNat := by
                        have hpa := hpe_a k.toNat hik hk_lt
                        rw [List.getElem?_eq_getElem hk_arr, Option.getD_some] at hpa
                        rw [← u64_trunc32_hi_eq wk]; exact congrArg BitVec.toNat hpa
                      have hwk_lo : (wk &&& 0xFFFFFFFF#64).toNat = b.toNat :=
                        (u64_trunc32_lo_eq wk).symm
                      have hkey_hi : (key >>> 32).toNat = litNeg a.toNat := by
                        dsimp only [key]; rw [packU64_hi, hopp_eq, bv32_xor1_eq_litNeg]
                      have hkey_lo : (key &&& 0xFFFFFFFF#64).toNat = litNeg b.toNat := by
                        dsimp only [key]; rw [packU64_lo]; exact bv32_xor1_eq_litNeg b
                      obtain ⟨hc1, hc2, hc3⟩ :=
                        condEq_of_condBin_hi_lo hcbk hcb_idx hwk_hi hwk_lo hkey_hi hkey_lo
                      fc_split_fast
                      · have hdk2 : dk.toNat + 2 ≤ cap.toNat := by
                          simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                        clear hc
                        have hdk_arr0 : dk.toNat < ceqk.length := by omega
                        have hdk_arr1 : (dk + 1#64).toNat < ceqk.length := by bv_omega
                        have hdk1_n : (dk + 1#64).toNat = dk.toNat + 1 := by bv_omega
                        have hdk2_n : (dk + 2#64).toNat = dk.toNat + 2 := by bv_omega
                        fc_to_group
                        refine wp_join_group (ts := [i32])
                          (fun (inv_l, ()) mt => mt = mk ∧
                            (not_b &&& 1#32 ≠ 0#32 → inv_l = b) ∧
                            (not_b &&& 1#32 = 0#32 → inv_l = not_b))
                          (fun _ ⟨inv_l, ⟨⟩⟩ mt ⟨hmt, hl1, hl0⟩ => ?_)
                          (fun Jl hJl => ?_)
                        · subst mt; fc_to_group
                          refine wp_join_group (ts := [i32])
                            (fun (inv_r, ()) mt2 => mt2 = mk ∧
                              CondEqElemOk F_cur cur_vars lit
                                ((inv_l.setWidth 64 <<< 32#64) ||| inv_r.setWidth 64))
                            (fun _ ⟨inv_r, ⟨⟩⟩ mt2 ⟨hmt2, hinv_ok⟩ => ?_)
                            (fun Jr hJr => ?_)
                          · subst mt2
                            have hmk_c : (array64 ceq ceqk ⋆ (array64 cb cb_xs ⋆ R)) mk :=
                              sep_ac hmk
                            fc_steps
                            have hswap : ∀ {xs : List (BitVec 64)},
                                (array64 ceq xs ⋆ (array64 cb cb_xs ⋆ R)) m →
                                (array64 cb cb_xs ⋆ array64 ceq xs ⋆ R) m := fun h => sep_ac h
                            refine hnext_ok _ (dk + 2#64) m ?_ (by omega) (fun r hr => ?_)
                              (hswap hm)
                            · rw [List.length_set, List.length_set, hck_len]
                            · rw [hdk2_n] at hr
                              try rw [show (dk + (1 : BitVec 64)).toNat = dk.toNat + 1 from hdk1_n]
                              by_cases hr1 : r = dk.toNat + 1
                              · subst hr1
                                rw [List.getElem?_set_self (by rw [List.length_set]; omega),
                                  Option.getD_some]
                                exact hinv_ok
                              · by_cases hr0 : r = dk.toNat
                                · subst hr0
                                  rw [List.getElem?_set_ne (by omega),
                                    List.getElem?_set_self (by omega), Option.getD_some]
                                  exact hc1
                                · rw [List.getElem?_set_ne (by omega),
                                    List.getElem?_set_ne (by omega)]
                                  exact hck_ok r (by omega)
                          · fc_split_fast
                            · have hne : not_b &&& 1#32 ≠ 0#32 := by simpa [wk, b, not_b] using hc
                              clear hc; fc_steps
                              exact hJr (a ||| 1#32, ()) mk ⟨rfl, by
                                try rw [show (1 : BitVec 32) = 1#32 from rfl]
                                rw [hl1 hne, hopp_eq]; exact hc2⟩
                            · have h0 : not_b &&& 1#32 = 0#32 := by simpa [wk, b, not_b] using hc
                              clear hc; fc_steps
                              exact hJr (a, ()) mk ⟨rfl, by rw [hl0 h0]; exact hc3⟩
                        · fc_split_fast
                          · have hne : not_b &&& 1#32 ≠ 0#32 := by simpa [wk, b, not_b] using hc
                            clear hc; fc_steps
                            exact hJl (b, ()) mk ⟨rfl, fun _ => rfl, fun h => absurd h hne⟩
                          · have h0 : not_b &&& 1#32 = 0#32 := by simpa [wk, b, not_b] using hc
                            clear hc; fc_steps
                            exact hJl (not_b, ()) mk ⟨rfl, fun h => absurd h0 h, fun _ => rfl⟩
                      · fc_steps; exact hnext_ok ceqk dk mk hck_len hdk_le hck_ok hmk
                    · fc_steps; exact hnext_ok ceqk dk mk hck_len hdk_le hck_ok hmk
                  · fc_steps; exact hJdn (dk, ()) mk ⟨ceqk, hck_len, hdk_le, hck_ok, hmk⟩
                · clear hc -- `nneg < npos`: scan k in [pe, ne), bsearch [i, pe)
                  refine wp_loop_inv (ts := [i64, i64])
                    (fun (dk, k, ()) mk => ∃ ceqk : List (BitVec 64),
                      ceqk.length = cap.toNat ∧ dk.toNat ≤ cap.toNat ∧
                      pe.toNat ≤ k.toNat ∧ k.toNat ≤ ne.toNat ∧
                      (∀ r < dk.toNat, CondEqElemOk F_cur cur_vars lit (ceqk[r]?.getD 0#64)) ∧
                      (array64 cb cb_xs ⋆ array64 ceq ceqk ⋆ R) mk)
                    (fun (_, k, ()) _ => ne.toNat - k.toNat)
                    (fun Jk hJk => by
                      fc_steps
                      exact hJk (d, pe, ()) ml ⟨ceql, hcl_len, hd_le, Nat.le_refl _, hpne,
                        hceql_ok, hml⟩)
                    (fun Jk ⟨dk, k, ⟨⟩⟩ mk
                      ⟨ceqk, hck_len, hdk_le, hpek, hkne, hck_ok, hmk⟩ ihk => ?_)
                  fc_split_fast
                  · have hk_lt : k.toNat < ne.toNat := by
                      simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                    clear hc
                    have hk_arr : k.toNat < cb_xs.length := by omega
                    have hkp1_n : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
                    fc_steps
                    try rw [← ha_def]
                    let wk := cb_xs[k.toNat]'hk_arr
                    let b := wk.setWidth 32
                    let not_b := b ^^^ 1#32
                    let key := (a.setWidth 64 <<< 32#64) ||| not_b.setWidth 64
                    refine wp_call_of_spec _ _ (hBsearch (cb, i, pe, _, ()) mk _ X
                      (m7BsearchU64Spec_mk cb_xs (array64 ceq ceqk ⋆ R) (by omega) (by omega)
                        (by omega) (sortedRange64_sub hcb_sort (by omega) (by omega)) (sep_ac hmk)
                        fun found hfound => ?_))
                    have hnext_ok : ∀ ceq' (dk' : BitVec 64) m',
                        ceq'.length = cap.toNat → dk'.toNat ≤ cap.toNat →
                        (∀ r < dk'.toNat, CondEqElemOk F_cur cur_vars lit (ceq'[r]?.getD 0#64)) →
                        (array64 cb cb_xs ⋆ array64 ceq ceq' ⋆ R) m' →
                        Jk (dk', k + 1#64, ()) m' := fun ceq' dk' m' hl hd hok hm' =>
                      ihk (dk', k + 1#64, ()) m' (by dsimp only; omega)
                        ⟨ceq', hl, hd, by omega, by omega, hok, hm'⟩
                    fc_split_fast
                    · obtain ⟨idx, hid1, hid2, hid_get⟩ := hfound.mp (by simpa using hc)
                      clear hc
                      have hid_get_k : cb_xs[idx]? = some key := by
                        simpa [key, wk, b, not_b, ← ha_def] using hid_get
                      have hcb_idx := hcb_ok idx (by omega)
                      rw [hid_get_k, Option.getD_some] at hcb_idx
                      have hcbk := hcb_ok k.toNat (by omega)
                      rw [List.getElem?_eq_getElem hk_arr, Option.getD_some] at hcbk
                      have hkey_hi : (key >>> 32).toNat = a.toNat := packU64_hi _ _
                      have hkey_lo : (key &&& 0xFFFFFFFF#64).toNat = not_b.toNat := packU64_lo _ _
                      have hwk_hi : (wk >>> 32).toNat = litNeg a.toNat := by
                        have hna := hne_a k.toNat hpek hk_lt
                        rw [List.getElem?_eq_getElem hk_arr, Option.getD_some] at hna
                        rw [← u64_trunc32_hi_eq wk]
                        dsimp only [wk]
                        rw [show (cb_xs[k.toNat] >>> 32#64) = cb_xs[k.toNat] >>> 32 from rfl,
                          hna, hopp_eq, bv32_xor1_eq_litNeg]
                      have hwk_lo : (wk &&& 0xFFFFFFFF#64).toNat = litNeg not_b.toNat := by
                        rw [← u64_trunc32_lo_eq wk]
                        show b.toNat = litNeg (b ^^^ 1#32).toNat
                        rw [← bv32_xor1_eq_litNeg, bv32_litNeg_double]
                      obtain ⟨hc1, hc2, hc3⟩ :=
                        condEq_of_condBin_hi_lo hcb_idx hcbk hkey_hi hkey_lo hwk_hi hwk_lo
                      have hdb : not_b ^^^ 1#32 = b := bv32_litNeg_double b
                      rw [hdb] at hc1 hc3
                      fc_split_fast
                      · have hdk2 : dk.toNat + 2 ≤ cap.toNat := by
                          simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                        clear hc
                        have hdk_arr0 : dk.toNat < ceqk.length := by omega
                        have hdk_arr1 : (dk + 1#64).toNat < ceqk.length := by bv_omega
                        have hdk1_n : (dk + 1#64).toNat = dk.toNat + 1 := by bv_omega
                        have hdk2_n : (dk + 2#64).toNat = dk.toNat + 2 := by bv_omega
                        fc_to_group
                        refine wp_join_group (ts := [i32])
                          (fun (inv_l, ()) mt => mt = mk ∧
                            (b &&& 1#32 ≠ 0#32 → inv_l = not_b) ∧
                            (b &&& 1#32 = 0#32 → inv_l = b))
                          (fun _ ⟨inv_l, ⟨⟩⟩ mt ⟨hmt, hl1, hl0⟩ => ?_)
                          (fun Jl hJl => ?_)
                        · subst mt; fc_to_group
                          refine wp_join_group (ts := [i32])
                            (fun (inv_r, ()) mt2 => mt2 = mk ∧
                              CondEqElemOk F_cur cur_vars lit
                                ((inv_l.setWidth 64 <<< 32#64) ||| inv_r.setWidth 64))
                            (fun _ ⟨inv_r, ⟨⟩⟩ mt2 ⟨hmt2, hinv_ok⟩ => ?_)
                            (fun Jr hJr => ?_)
                          · subst mt2
                            have hmk_c : (array64 ceq ceqk ⋆ (array64 cb cb_xs ⋆ R)) mk :=
                              sep_ac hmk
                            fc_steps
                            have hswap : ∀ {xs : List (BitVec 64)},
                                (array64 ceq xs ⋆ (array64 cb cb_xs ⋆ R)) m →
                                (array64 cb cb_xs ⋆ array64 ceq xs ⋆ R) m := fun h => sep_ac h
                            refine hnext_ok _ (dk + 2#64) m ?_ (by omega) (fun r hr => ?_)
                              (hswap hm)
                            · rw [List.length_set, List.length_set, hck_len]
                            · rw [hdk2_n] at hr
                              try rw [show (dk + (1 : BitVec 64)).toNat = dk.toNat + 1 from hdk1_n]
                              by_cases hr1 : r = dk.toNat + 1
                              · subst hr1
                                rw [List.getElem?_set_self (by rw [List.length_set]; omega),
                                  Option.getD_some]
                                exact hinv_ok
                              · by_cases hr0 : r = dk.toNat
                                · subst hr0
                                  rw [List.getElem?_set_ne (by omega),
                                    List.getElem?_set_self (by omega), Option.getD_some]
                                  exact hc1
                                · rw [List.getElem?_set_ne (by omega),
                                    List.getElem?_set_ne (by omega)]
                                  exact hck_ok r (by omega)
                          · fc_split_fast
                            · have hne : b &&& 1#32 ≠ 0#32 := by simpa [wk, b] using hc
                              clear hc; fc_steps
                              exact hJr (a ||| 1#32, ()) mk ⟨rfl, by
                                try rw [show (1 : BitVec 32) = 1#32 from rfl]
                                rw [hl1 hne, hopp_eq]; exact hc2⟩
                            · have h0 : b &&& 1#32 = 0#32 := by simpa [wk, b] using hc
                              clear hc; fc_steps
                              exact hJr (a, ()) mk ⟨rfl, by rw [hl0 h0]; exact hc3⟩
                        · fc_split_fast
                          · have hne : b &&& 1#32 ≠ 0#32 := by simpa [wk, b] using hc
                            clear hc; fc_steps
                            exact hJl (not_b, ()) mk ⟨rfl, fun _ => rfl, fun h => absurd h hne⟩
                          · have h0 : b &&& 1#32 = 0#32 := by simpa [wk, b] using hc
                            clear hc; fc_steps
                            exact hJl (b, ()) mk ⟨rfl, fun h => absurd h0 h, fun _ => rfl⟩
                      · fc_steps; exact hnext_ok ceqk dk mk hck_len hdk_le hck_ok hmk
                    · fc_steps; exact hnext_ok ceqk dk mk hck_len hdk_le hck_ok hmk
                  · fc_steps; exact hJdn (dk, ()) mk ⟨ceqk, hck_len, hdk_le, hck_ok, hmk⟩
            · fc_steps
              exact hJdn0 (d, ()) ml ⟨ceql, hcl_len, hd_le, hceql_ok, hml⟩
        · -- `ne` loop body (`while (ne < m)`)
          fc_split_fast
          · have hne_lt : ne.toNat < m.toNat := by
              simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
            clear hc
            have hne_arr : ne.toNat < cb_xs.length := by omega
            have hnep1_n : (ne + 1#64).toNat = ne.toNat + 1 := by bv_omega
            fc_steps
            fc_split_fast
            · have hne_eq : (cb_xs[ne.toNat]?.getD 0#64 >>> (32 : Nat)).setWidth 32 =
                  (a ||| 1#32) := by
                rw [List.getElem?_eq_getElem hne_arr, Option.getD_some, ha_def]
                exact beq_iff_eq.mp (by simpa using hc)
              clear hc
              fc_steps
              refine ihne (ne + 1#64, ()) ml (by dsimp only; omega)
                ⟨by omega, by omega, fun p hp1 hp2 => ?_, rfl⟩
              rw [hnep1_n] at hp2
              by_cases hpn : p = ne.toNat
              · subst hpn; exact hne_eq
              · exact hne_a p hp1 (by omega)
            · fc_steps; exact hJan () ml rfl
          · fc_steps; exact hJan () ml rfl
      · -- `pe` loop body (`while (pe < m)`)
        fc_split_fast
        · have hpe_lt : pe.toNat < m.toNat := by
            simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
          clear hc
          have hpe_arr : pe.toNat < cb_xs.length := by omega
          have hpep1_n : (pe + 1#64).toNat = pe.toNat + 1 := by bv_omega
          fc_steps
          fc_split_fast
          · have hpe_eq : (cb_xs[pe.toNat]?.getD 0#64 >>> (32 : Nat)).setWidth 32 = a := by
              rw [List.getElem?_eq_getElem hpe_arr, Option.getD_some, ha_def]
              exact beq_iff_eq.mp (by simpa using hc)
            clear hc
            fc_steps
            refine ihpe (pe + 1#64, ()) ml (by dsimp only; omega)
              ⟨by omega, by omega, fun p hp1 hp2 => ?_, rfl⟩
            rw [hpep1_n] at hp2
            by_cases hpp : p = pe.toNat
            · subst hpp; exact hpe_eq
            · exact hpe_a p hp1 (by omega)
          · fc_steps; exact hJap () ml rfl
        · fc_steps; exact hJap () ml rfl
  · -- Post scan (`!(i < m)`): if d ≤ 1 return d; else sort & dedup
    have hi_ge : m.toNat ≤ i.toNat := by
      simp only [BitVec.ult, decide_eq_false_iff_not, not_lt] at hc; exact hc
    clear hc
    fc_steps
    fc_split_fast
    · have hd1 : d.toNat ≤ 1 := hc
      clear hc
      fc_steps
      exact hQ d ceql ml hcl_len hd_le hceql_ok hml
    · have hd_gt1 : 1 < d.toNat := by bv_omega
      clear hc
      have hml_s : (array64 ceq ceql ⋆ (array64 cb cb_xs ⋆ R)) ml := sep_ac hml
      fc_steps
      refine wp_call_of_spec _ _ (hSort (ceq, d, ()) ml _ X
        (m7U64SortSpec_mk ceql (array64 cb cb_xs ⋆ R) (by omega) (by omega) hml_s
          fun ceq_s m_s hcs_len _ hcs_sub _ hm_s => ?_))
      have hcs_ok : ∀ k < d.toNat, CondEqElemOk F_cur cur_vars lit (ceq_s[k]?.getD 0#64) := by
        intro k hk; obtain ⟨j, hj, hget⟩ := hcs_sub k hk
        have hj_ok := hceql_ok j hj; rwa [← hget] at hj_ok
      fc_to_group
      refine wp_loop_inv (ts := [i64, i64])
        (fun (u, idx, ()) md2 => ∃ ceq_d : List (BitVec 64),
          1 ≤ u.toNat ∧ u.toNat ≤ idx.toNat ∧ idx.toNat ≤ d.toNat ∧
          ceq_d.length = cap.toNat ∧
          (∀ k, idx.toNat ≤ k → k < d.toNat → ceq_d[k]? = ceq_s[k]?) ∧
          (∀ k < u.toNat, CondEqElemOk F_cur cur_vars lit (ceq_d[k]?.getD 0#64)) ∧
          (array64 ceq ceq_d ⋆ (array64 cb cb_xs ⋆ R)) md2)
        (fun (_, idx, ()) _ => d.toNat - idx.toNat)
        (fun Jd hJd => by
          fc_steps
          exact hJd (1#64, 1#64, ()) m_s ⟨ceq_s, Nat.le_refl _, Nat.le_refl _, by bv_omega,
            by omega, fun _ _ _ => rfl, fun k hk => hcs_ok k (by bv_omega), hm_s⟩)
        (fun Jd ⟨u, idx, ⟨⟩⟩ md2 ⟨ceq_d, hu1, hui, hid, hcd2_len, htail, hok_d, hmd2⟩ ihd => ?_)
      fc_split_fast
      · have hidx_lt : idx.toNat < d.toNat := by
          simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
        have hum1_n : (u - 1#64).toNat = u.toNat - 1 := by bv_omega
        have hidx_arr : idx.toNat < ceq_d.length := by omega
        have hum1_arr : (u - 1#64).toNat < ceq_d.length := by omega
        have hu_arr : u.toNat < ceq_d.length := by omega
        have hip1_n : (idx + 1#64).toNat = idx.toNat + 1 := by bv_omega
        fc_to_group
        refine wp_join_group (ts := [i64])
          (fun (u2, ()) md3 => ∃ ceq_d2 : List (BitVec 64),
            1 ≤ u2.toNat ∧ u2.toNat ≤ idx.toNat + 1 ∧ ceq_d2.length = cap.toNat ∧
            (∀ k, idx.toNat + 1 ≤ k → k < d.toNat → ceq_d2[k]? = ceq_s[k]?) ∧
            (∀ k < u2.toNat, CondEqElemOk F_cur cur_vars lit (ceq_d2[k]?.getD 0#64)) ∧
            (array64 ceq ceq_d2 ⋆ (array64 cb cb_xs ⋆ R)) md3)
          (fun _ ⟨u2, ⟨⟩⟩ md3 ⟨ceq_d2, hu2_1, hu2_le, hlen3, ht3, ho3, hm3⟩ => ?_)
          (fun Jd2 hJd2 => ?_)
        · fc_steps
          exact ihd (u2, idx + 1#64, ()) md3 (by dsimp only; omega)
            ⟨ceq_d2, hu2_1, by omega, by omega, hlen3, fun k hk1 hk2 => ht3 k (by omega) hk2,
              ho3, hm3⟩
        · fc_split_fast
          · have hup1_n : (u + 1#64).toNat = u.toNat + 1 := by bv_omega
            fc_steps
            let vi := ceq_d[idx.toNat]'hidx_arr
            let ceq_d2 := ceq_d.set u.toNat vi
            have hvi_eq : ceq_s[idx.toNat]? = some vi := by
              rw [← htail idx.toNat (Nat.le_refl _) hidx_lt, List.getElem?_eq_getElem hidx_arr]
            have hvi_ok : CondEqElemOk F_cur cur_vars lit vi := by
              have h := hcs_ok idx.toNat hidx_lt; rwa [hvi_eq, Option.getD_some] at h
            refine hJd2 (u + 1#64, ()) m ⟨ceq_d2, by omega, by omega, by simp [ceq_d2, hcd2_len],
              fun k hk1 hk2 => by
                dsimp [ceq_d2]; rw [List.getElem?_set_ne (by omega)]; exact htail k (by omega) hk2,
              fun k hk => ?_, hm⟩
            rw [hup1_n] at hk
            by_cases hku : k = u.toNat
            · subst hku; dsimp [ceq_d2]; rw [List.getElem?_set_self (by omega), Option.getD_some]
              exact hvi_ok
            · dsimp [ceq_d2]; rw [List.getElem?_set_ne (Ne.symm hku)]
              exact hok_d k (by omega)
          · fc_steps
            exact hJd2 (u, ()) md2 ⟨ceq_d, hu1, by omega, hcd2_len,
              fun k hk1 hk2 => htail k (by omega) hk2, hok_d, hmd2⟩
      · have hidx_ge : d.toNat ≤ idx.toNat := by
          simp only [BitVec.ult, decide_eq_false_iff_not, not_lt] at hc; exact hc
        fc_steps
        exact hQ u ceq_d md2 hcd2_len (by omega) hok_d (sep_ac hmd2)


/-! ## 5. Conditional Equivalence Merge (`full_cong_merge_condeq_m7`) -/

def m7MergeCondeqGenSpec
    (GateSeq : List (List Nat) → Nat → List (BitVec 32) → Nat → Nat → Prop) :
    Spec [i64, i32, i64, i64, i32, i32] [i32] :=
  fun (h, cond, pos_n, neg_n, g_len, g_cap, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (wk1 wk2 : List (BitVec 64)) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      3 ≤ s.core.cur_vars ∧ cond.toNat < 2 * s.core.cur_vars ∧
      g_cap.toNat ≤ c.scratch_cap ∧
      pos_n.toNat ≤ wk1.length ∧ neg_n.toNat ≤ wk2.length ∧
      wk1.length < 2 ^ 61 ∧ wk2.length < 2 ^ 61 ∧
      (∀ k < pos_n.toNat,
        CondEqElemOk F_cur s.core.cur_vars (litNeg cond.toNat) (wk1[k]?.getD 0#64)) ∧
      (∀ k < neg_n.toNat,
        CondEqElemOk F_cur s.core.cur_vars cond.toNat (wk2[k]?.getD 0#64)) ∧
      GateSeq F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (FullMemNoWks3 c s ⋆ array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R) m ∧
      ∀ (g_len' : BitVec 32) (scr' : List (BitVec 32)) m',
        scr'.length = s.scratch.scratch_buf.length →
        (g_len.toNat ≤ g_cap.toNat →
          g_len.toNat ≤ g_len'.toNat ∧ g_len'.toNat ≤ g_cap.toNat) →
        (∀ idx < g_len.toNat, scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        GateSeq F_cur s.core.cur_vars scr' g_len'.toNat 0 →
        (FullMemNoWks3 c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆
          array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R) m' →
        Q (g_len', ()) m'

def m7MergeCondeqSpec : Spec [i64, i32, i64, i64, i32, i32] [i32] :=
  m7MergeCondeqGenSpec GateSeqOk32

def m7MergeCondeqM6Spec : Spec [i64, i32, i64, i64, i32, i32] [i32] :=
  m7MergeCondeqGenSpec M6GateSeqOk

theorem m7ExtractCondeqSpec_noExit {xs m Q X} :
    m7ExtractCondeqSpec xs m Q X → m7ExtractCondeqSpec xs m Q (fun _ _ _ _ => False) := id

theorem m7MergeCondeqSpec_noExit {xs m Q X} :
    m7MergeCondeqSpec xs m Q X → m7MergeCondeqSpec xs m Q (fun _ _ _ _ => False) := id

theorem m7MergeCondeqM6Spec_noExit {xs m Q X} :
    m7MergeCondeqM6Spec xs m Q X → m7MergeCondeqM6Spec xs m Q (fun _ _ _ _ => False) := id

private theorem full_cong_merge_condeq_m7_gen_wp (Γ : Env)
    (GateSeq : List (List Nat) → Nat → List (BitVec 32) → Nat → Nat → Prop)
    (hGateStep : ∀ {F_cur : List (List Nat)} {cur_vars : Nat}
      {scr scr1 : List (BitVec 32)} {g_len cond : Nat} {pv nv : BitVec 64}
      {y t e yy tt ee : BitVec 32},
      3 ≤ cur_vars → cond < 2 * cur_vars →
      CondEqElemOk F_cur cur_vars (litNeg cond) pv →
      CondEqElemOk F_cur cur_vars cond nv →
      y = (pv >>> (32 : Nat)).setWidth 32 → t = pv.setWidth 32 → e = nv.setWidth 32 →
      (nv >>> (32 : Nat)).setWidth 32 = y →
      ((t &&& 1#32 = 0#32 → yy = y ∧ tt = t ∧ ee = e) ∧
       (t &&& 1#32 ≠ 0#32 → yy = y ^^^ 1#32 ∧ tt = t ^^^ 1#32 ∧ ee = e ^^^ 1#32)) →
      cond < 2 ^ 32 → g_len + 5 ≤ scr.length →
      scr1 = ((((scr.set g_len yy).set (g_len + 1)
        ((2#32 <<< 28#32) ||| 3#32)).set (g_len + 2) (BitVec.ofNat 32 cond)).set
        (g_len + 3) tt).set (g_len + 4) ee →
      GateSeq F_cur cur_vars scr g_len 0 →
      scr1.length = scr.length ∧ (∀ idx < g_len, scr1[idx]? = scr[idx]?) ∧
      GateSeq F_cur cur_vars scr1 (g_len + 5) 0) :
    ∀ args m Q X, m7MergeCondeqGenSpec GateSeq args m Q X →
      Func.wp Γ full_cong_merge_condeq_m7_body args m Q X := by
  rintro ⟨h, cond, pos_n, neg_n, g_len, g_cap, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, wk1, wk2, R, rfl, hsl, hw, hcv3, hcond_lt, hcap_le,
      hpn_le, hnn_le, hwk1_bd, hwk2_bd, hpos_ok, hneg_ok, hseq0, hm0, hQ⟩
  unfold Func.wp full_cong_merge_condeq_m7_body
  have sep_wk1_head : ∀ {s0 : FullState} {mx : Mem 64},
      (FullMemNoWks3 c s0 ⋆ array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R) mx →
      (array64 c.pWorkStk1 wk1 ⋆
        (FullMemNoWks3 c s0 ⋆ array64 c.pWorkStk2 wk2 ⋆ R)) mx := fun mx_h => sep_ac mx_h
  have sep_wk2_head : ∀ {s0 : FullState} {mx : Mem 64},
      (FullMemNoWks3 c s0 ⋆ array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R) mx →
      (array64 c.pWorkStk2 wk2 ⋆
        (FullMemNoWks3 c s0 ⋆ array64 c.pWorkStk1 wk1 ⋆ R)) mx := fun mx_h => sep_ac mx_h
  have hscr_len := hsl.scratch_ok.scratch_buf_len
  fc_split_fast
  · fc_steps
    exact hQ g_len s.scratch.scratch_buf m0 rfl (fun hg => ⟨Nat.le_refl _, hg⟩)
      (fun _ _ => rfl) hseq0 hm0
  · fc_split_fast
    · fc_steps
      exact hQ g_len s.scratch.scratch_buf m0 rfl (fun hg => ⟨Nat.le_refl _, hg⟩)
        (fun _ _ => rfl) hseq0 hm0
    · fc_split_fast
      · have hgt : g_cap.toNat < g_len.toNat := by
          simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
        fc_steps
        exact hQ g_len s.scratch.scratch_buf m0 rfl (fun hle => by omega)
          (fun _ _ => rfl) hseq0 hm0
      · have hg_le_cap : g_len.toNat ≤ g_cap.toNat := by
          simp only [BitVec.ult, decide_eq_false_iff_not, not_lt] at hc; exact hc
        clear hc
        c0_steps
        fc_split_fast
        · have hscr_bd := c.hscr; unfold dimacsBound at hscr_bd
          have hbad : c.scratch_cap < g_cap.toNat := by
            simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
              bv_zext32_toNat] at hc
            rw [Nat.mod_eq_of_lt (by omega)] at hc
            exact hc
          omega
        · clear hc; fc_steps
          refine wp_loop_inv (ts := [i32, i64, i64])
            (fun (gl, p, q, ()) ml => ∃ scr : List (BitVec 32),
              scr.length = s.scratch.scratch_buf.length ∧
              g_len.toNat ≤ gl.toNat ∧ gl.toNat ≤ g_cap.toNat ∧
              p.toNat ≤ pos_n.toNat ∧ q.toNat ≤ neg_n.toNat ∧
              (∀ idx < g_len.toNat, scr[idx]? = s.scratch.scratch_buf[idx]?) ∧
              GateSeq F_cur s.core.cur_vars scr gl.toNat 0 ∧
              (FullMemNoWks3 c { s with scratch := { s.scratch with scratch_buf := scr } } ⋆
                array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R) ml)
            (fun (_, p, q, ()) _ => (pos_n.toNat - p.toNat) + (neg_n.toNat - q.toNat))
            (fun J0 hJ0 => by
              fc_steps
              exact hJ0 (g_len, 0#64, 0#64, ()) m0 ⟨s.scratch.scratch_buf, rfl, Nat.le_refl _,
                hg_le_cap, Nat.zero_le _, Nat.zero_le _, fun _ _ => rfl, hseq0, hm0⟩)
            (fun J0 ⟨gl, p, q, ⟨⟩⟩ ml ⟨scr, hsl_l, hgl_ge, hgl_le, hp_le, hq_le, hpref,
              hseq, hml⟩ ih0 => ?_)
          fc_split_fast
          · have hp_lt : p.toNat < pos_n.toNat := by
              simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
            clear hc
            fc_split_fast
            · have hq_lt : q.toNat < neg_n.toNat := by
                simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
              clear hc
              fc_split_fast
              · have hgl5 : gl.toNat + 5 ≤ g_cap.toNat := by
                  simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                clear hc
                have hp_arr : p.toNat < wk1.length := by omega
                have hq_arr : q.toNat < wk2.length := by omega
                let sl : FullState := { s with scratch := { s.scratch with scratch_buf := scr } }
                have hml1 : (array64 c.pWorkStk1 wk1 ⋆
                    (FullMemNoWks3 c sl ⋆ array64 c.pWorkStk2 wk2 ⋆ R)) ml := sep_wk1_head hml
                c0_steps
                let pv := wk1[p.toNat]'hp_arr
                let lhs_p := (pv >>> (32 : Nat)).setWidth 32
                have hml2 : (array64 c.pWorkStk2 wk2 ⋆
                    (FullMemNoWks3 c sl ⋆ array64 c.pWorkStk1 wk1 ⋆ R)) ml := sep_wk2_head hml
                c0_steps
                let qv := wk2[q.toNat]'hq_arr
                let lhs_n := (qv >>> (32 : Nat)).setWidth 32
                have hpp1_n : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
                have hqp1_n : (q + 1#64).toNat = q.toNat + 1 := by bv_omega
                fc_split_fast
                · clear hc; fc_steps
                  exact ih0 (gl, p + 1#64, q, ()) ml (by dsimp only; omega)
                    ⟨scr, hsl_l, hgl_ge, hgl_le, by omega, hq_le, hpref, hseq, hml⟩
                · have h1 : lhs_n.toNat ≤ lhs_p.toNat := by
                    simp only [BitVec.ult, decide_eq_false_iff_not, not_lt] at hc; exact hc
                  clear hc
                  fc_split_fast
                  · clear hc; fc_steps
                    exact ih0 (gl, p, q + 1#64, ()) ml (by dsimp only; omega)
                      ⟨scr, hsl_l, hgl_ge, hgl_le, hp_le, by omega, hpref, hseq, hml⟩
                  · have h2 : lhs_p.toNat ≤ lhs_n.toNat := by
                      simp only [BitVec.ult, decide_eq_false_iff_not, not_lt] at hc; exact hc
                    clear hc
                    have hlhs_eq : lhs_n = lhs_p := BitVec.eq_of_toNat_eq (by omega)
                    fc_to_group
                    refine wp_join_group (ts := [i32, i64])
                      (fun (gl2, _q2, ()) mn => ∃ scr2 : List (BitVec 32),
                        scr2.length = s.scratch.scratch_buf.length ∧
                        gl.toNat ≤ gl2.toNat ∧ gl2.toNat ≤ g_cap.toNat ∧
                        (∀ idx < gl.toNat, scr2[idx]? = scr[idx]?) ∧
                        GateSeq F_cur s.core.cur_vars scr2 gl2.toNat 0 ∧
                        (FullMemNoWks3 c
                          { s with scratch := { s.scratch with scratch_buf := scr2 } } ⋆
                          array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R) mn)
                      (fun _ ⟨gl2, _q2, ⟨⟩⟩ mn ⟨scr2, hsl2, hgl2_ge, hgl2_le, hp2, hsq2, hmn⟩ => ?_)
                      (fun Jq hJq => ?_)
                    · fc_steps
                      exact ih0 (gl2, p + 1#64, q, ()) mn (by dsimp only; omega)
                        ⟨scr2, hsl2, by omega, hgl2_le, by omega, hq_le,
                          fun idx hi => (hp2 idx (by omega)).trans (hpref idx hi), hsq2, hmn⟩
                    · refine wp_loop_inv (ts := [i32, i64])
                        (fun (gl2, q2, ()) mn => ∃ scr2 : List (BitVec 32),
                          scr2.length = s.scratch.scratch_buf.length ∧
                          gl.toNat ≤ gl2.toNat ∧ gl2.toNat ≤ g_cap.toNat ∧
                          q.toNat ≤ q2.toNat ∧ q2.toNat ≤ neg_n.toNat ∧
                          (∀ idx < gl.toNat, scr2[idx]? = scr[idx]?) ∧
                          GateSeq F_cur s.core.cur_vars scr2 gl2.toNat 0 ∧
                          (FullMemNoWks3 c
                            { s with scratch := { s.scratch with scratch_buf := scr2 } } ⋆
                            array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R) mn)
                        (fun (_, q2, ()) _ => neg_n.toNat - q2.toNat)
                        (fun J2 hJ2 => by
                          fc_steps
                          exact hJ2 (gl, q, ()) ml ⟨scr, hsl_l, Nat.le_refl _, hgl_le,
                            Nat.le_refl _, hq_le, fun _ _ => rfl, hseq, hml⟩)
                        (fun J2 ⟨gl2, q2, ⟨⟩⟩ mn
                          ⟨scr2, hsl2, hgl2_ge, hgl2_le, hqq2, hq2_le, hp2, hsq2, hmn⟩ ih2 => ?_)
                      fc_split_fast
                      · have hq2_lt : q2.toNat < neg_n.toNat := by
                          simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                        clear hc
                        fc_split_fast
                        · have hgl2_5 : gl2.toNat + 5 ≤ g_cap.toNat := by
                            simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                          clear hc
                          have hq2_arr : q2.toNat < wk2.length := by omega
                          have hq2p1_n : (q2 + 1#64).toNat = q2.toNat + 1 := by bv_omega
                          let sl2 : FullState :=
                            { s with scratch := { s.scratch with scratch_buf := scr2 } }
                          have hmn2 : (array64 c.pWorkStk2 wk2 ⋆
                              (FullMemNoWks3 c sl2 ⋆ array64 c.pWorkStk1 wk1 ⋆ R)) mn :=
                            sep_wk2_head hmn
                          c0_steps
                          let nv := wk2[q2.toNat]'hq2_arr
                          fc_split_fast
                          · clear hc; fc_steps
                            exact hJq (gl2, q2, ()) mn
                              ⟨scr2, hsl2, hgl2_ge, hgl2_le, hp2, hsq2, hmn⟩
                          · have hnv_eq : (nv >>> (32 : Nat)).setWidth 32 = lhs_p := by
                              simpa [nv, lhs_p, pv] using hc
                            clear hc
                            fc_to_group
                            refine wp_join_group (ts := [i32])
                              (fun (gl3, ()) mp => ∃ scr3 : List (BitVec 32),
                                scr3.length = s.scratch.scratch_buf.length ∧
                                gl2.toNat ≤ gl3.toNat ∧ gl3.toNat ≤ g_cap.toNat ∧
                                (∀ idx < gl2.toNat, scr3[idx]? = scr2[idx]?) ∧
                                GateSeq F_cur s.core.cur_vars scr3 gl3.toNat 0 ∧
                                (FullMemNoWks3 c
                                  { s with scratch := { s.scratch with scratch_buf := scr3 } } ⋆
                                  array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R) mp)
                              (fun _ ⟨gl3, ⟨⟩⟩ mp
                                ⟨scr3, hsl3, hgl3_ge, hgl3_le, hp3, hsq3, hmp⟩ => ?_)
                              (fun J3 hJ3 => ?_)
                            · fc_steps
                              exact ih2 (gl3, q2 + 1#64, ()) mp (by dsimp only; omega)
                                ⟨scr3, hsl3, by omega, hgl3_le, by omega, by omega,
                                  fun idx hi => (hp3 idx (by omega)).trans (hp2 idx hi),
                                  hsq3, hmp⟩
                            · let t := pv.setWidth 32
                              let e := nv.setWidth 32
                              fc_split_fast
                              · clear hc; fc_split_fast
                                · clear hc; fc_to_group
                                  refine wp_join_group (ts := [i32, i32, i32])
                                    (fun (yy, tt, ee, ()) mr => mr = mn ∧
                                      (t &&& 1#32 = 0#32 → yy = lhs_p ∧ tt = t ∧ ee = e) ∧
                                      (t &&& 1#32 ≠ 0#32 →
                                        yy = lhs_p ^^^ 1#32 ∧ tt = t ^^^ 1#32 ∧ ee = e ^^^ 1#32))
                                    (fun _ ⟨yy, tt, ee, ⟨⟩⟩ mr ⟨hmr, hfl0, hfl1⟩ => ?_)
                                    (fun J4 hJ4 => ?_)
                                  · subst mr
                                    have hgl2_n0 : gl2.toNat < scr2.length := by omega
                                    have hgl2_z0 : (gl2.setWidth 64).toNat < scr2.length := by
                                      rw [bv_zext32_toNat]; omega
                                    have hgl2_n1 :
                                        (gl2.setWidth 64 + 1#64).toNat < scr2.length := by
                                      rw [BitVec.toNat_add, bv_zext32_toNat]; bv_omega
                                    have hgl2_n2 :
                                        (gl2.setWidth 64 + 2#64).toNat < scr2.length := by
                                      rw [BitVec.toNat_add, bv_zext32_toNat]; bv_omega
                                    have hgl2_n3 :
                                        (gl2.setWidth 64 + 3#64).toNat < scr2.length := by
                                      rw [BitVec.toNat_add, bv_zext32_toNat]; bv_omega
                                    have hgl2_n4 :
                                        (gl2.setWidth 64 + 4#64).toNat < scr2.length := by
                                      rw [BitVec.toNat_add, bv_zext32_toNat]; bv_omega
                                    have hgl2_5_n : (gl2 + 5#32).toNat = gl2.toNat + 5 := by
                                      bv_omega
                                    fc_steps
                                    let scr3 := ((((scr2.set gl2.toNat yy).set (gl2.toNat + 1)
                                      ((2#32 <<< 28#32) ||| 3#32)).set (gl2.toNat + 2) cond).set
                                      (gl2.toNat + 3) tt).set (gl2.toNat + 4) ee
                                    have hw1_p := hpos_ok p.toNat hp_lt
                                    rw [List.getElem?_eq_getElem hp_arr, Option.getD_some] at hw1_p
                                    have hw2_q := hneg_ok q2.toNat hq2_lt
                                    rw [List.getElem?_eq_getElem hq2_arr, Option.getD_some] at hw2_q
                                    obtain ⟨hs3_l, hs3_p, hs3_ok⟩ := hGateStep hcv3
                                      hcond_lt hw1_p hw2_q rfl rfl rfl hnv_eq ⟨hfl0, hfl1⟩
                                      (BitVec.isLt cond) (by omega) rfl hsq2
                                    have hcond32 : BitVec.ofNat 32 cond.toNat = cond :=
                                      BitVec.eq_of_toNat_eq (by
                                        rw [BitVec.toNat_ofNat]
                                        exact Nat.mod_eq_of_lt (BitVec.isLt cond))
                                    rw [hcond32] at hs3_l hs3_p hs3_ok
                                    dsimp only [sl2] at hm
                                    try rw [show ((2 : BitVec 32) <<< (28 : Nat) ||| 3) =
                                      (2#32 <<< 28#32 ||| 3#32) from rfl] at hm
                                    try rw [show ((2 : BitVec 32) <<< (28 : BitVec 32) ||| 3) =
                                      (2#32 <<< 28#32 ||| 3#32) from rfl] at hm
                                    have heq_scr : ((((scr2.set
                                          (gl2.setWidth 64).toNat yy).set
                                          (gl2.setWidth 64 + 1).toNat (2#32 <<< 28#32 ||| 3#32)).set
                                          (gl2.setWidth 64 + 2).toNat cond).set
                                          (gl2.setWidth 64 + 3).toNat tt).set
                                          (gl2.setWidth 64 + 4).toNat ee = scr3 := by
                                      dsimp only [scr3]
                                      congr 1; congr 1; congr 1; congr 1
                                      all_goals first
                                        | rfl
                                        | rw [bv_zext32_toNat]
                                        | (rw [BitVec.toNat_add, bv_zext32_toNat]; bv_omega)
                                    rw [heq_scr] at hm
                                    refine hJ3 (gl2 + 5#32, ()) m ⟨scr3, hs3_l.trans hsl2,
                                      by rw [hgl2_5_n]; exact Nat.le_add_right _ _,
                                      by rw [hgl2_5_n]; exact hgl2_5,
                                      hs3_p, by rwa [hgl2_5_n], ?_⟩
                                    exact sep_ac hm
                                  · fc_split_fast
                                    · have hne : t &&& 1#32 ≠ 0#32 := by simpa [t] using hc
                                      clear hc; fc_steps
                                      exact hJ4 (lhs_p ^^^ 1#32, t ^^^ 1#32, e ^^^ 1#32, ()) mn
                                        ⟨rfl, fun h => absurd h hne, fun _ => ⟨rfl, rfl, rfl⟩⟩
                                    · have h0 : t &&& 1#32 = 0#32 := by simpa [t] using hc
                                      clear hc; fc_steps
                                      exact hJ4 (lhs_p, t, e, ()) mn
                                        ⟨rfl, fun _ => ⟨rfl, rfl, rfl⟩, fun h => absurd h0 h⟩
                                · clear hc; fc_steps
                                  exact hJ3 (gl2, ()) mn ⟨scr2, hsl2, Nat.le_refl _, hgl2_le,
                                    fun _ _ => rfl, hsq2, hmn⟩
                              · clear hc; fc_steps
                                exact hJ3 (gl2, ()) mn ⟨scr2, hsl2, Nat.le_refl _, hgl2_le,
                                  fun _ _ => rfl, hsq2, hmn⟩
                        · clear hc; fc_steps
                          exact hJq (gl2, q2, ()) mn ⟨scr2, hsl2, hgl2_ge, hgl2_le, hp2, hsq2, hmn⟩
                      · clear hc; fc_steps
                        exact hJq (gl2, q2, ()) mn ⟨scr2, hsl2, hgl2_ge, hgl2_le, hp2, hsq2, hmn⟩
              · fc_steps; exact hQ gl scr ml hsl_l (fun _ => ⟨hgl_ge, hgl_le⟩) hpref hseq hml
            · fc_steps; exact hQ gl scr ml hsl_l (fun _ => ⟨hgl_ge, hgl_le⟩) hpref hseq hml
          · fc_steps; exact hQ gl scr ml hsl_l (fun _ => ⟨hgl_ge, hgl_le⟩) hpref hseq hml

theorem full_cong_merge_condeq_m7_wp (Γ : Env) :
    ∀ args m Q X, m7MergeCondeqSpec args m Q X →
      Func.wp Γ full_cong_merge_condeq_m7_body args m Q X :=
  full_cong_merge_condeq_m7_gen_wp Γ GateSeqOk32 @merge_condeq_gate_ok

theorem full_cong_merge_condeq_m7_m6_wp (Γ : Env) :
    ∀ args m Q X, m7MergeCondeqM6Spec args m Q X →
      Func.wp Γ full_cong_merge_condeq_m7_body args m Q X :=
  full_cong_merge_condeq_m7_gen_wp Γ M6GateSeqOk @merge_condeq_m6gate_ok

/-! ## 6. Top-Level ITE Gate Extraction (`full_cong_extract_ite_all_m7`) -/

/-- Contract for `full_cong_extract_ite_all_m7(h, g_len, g_cap, tick_lim)`: preserves `s.core`,
`last_learned`, `extend_len`, and `scratch_buf[0 .. g_len)`, while appending only sound ITE gates
`GateSeq F_cur s.core.cur_vars s'.scratch.scratch_buf ret.toNat 0`. -/
private def m7AllInvGen
    (GateSeq : List (List Nat) → Nat → List (BitVec 32) → Nat → Nat → Prop)
    (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (g_len g_cap : BitVec 32) (R : Mem 64 → Prop) (gl : BitVec 32) (m : Mem 64) : Prop :=
  ∃ (s_cur : FullState) (ws wk1 wk2 : List (BitVec 64)),
    s_cur.LengthsOk c ∧ s_cur.core = s.core ∧
    s_cur.scratch.last_learned = s.scratch.last_learned ∧
    s_cur.scratch.extend_len = s.scratch.extend_len ∧
    ws.length = c.max_vars ∧ wk1.length = c.max_vars ∧ wk2.length = c.max_vars ∧
    g_len.toNat ≤ gl.toNat ∧ gl.toNat ≤ g_cap.toNat ∧
    (∀ idx < g_len.toNat, s_cur.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) ∧
    GateSeq F_cur s.core.cur_vars s_cur.scratch.scratch_buf gl.toNat 0 ∧
    (FullMemNoWks3 c s_cur ⋆
      array64 c.pWsort ws ⋆ array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R) m

def m7ExtractIteAllGenSpec
    (GateSeq : List (List Nat) → Nat → List (BitVec 32) → Nat → Nat → Prop) :
    Spec [i64, i32, i32, i64] [i32] :=
  fun (h, g_len, g_cap, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      s.core.dense_mode ≠ 0#64 ∧
      g_len.toNat ≤ g_cap.toNat ∧ g_cap.toNat ≤ c.scratch_cap ∧
      GateSeq F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 32) (s' : FullState) (m' : Mem 64),
        s'.LengthsOk c → s'.core = s.core →
        s'.scratch.last_learned = s.scratch.last_learned →
        s'.scratch.extend_len = s.scratch.extend_len →
        g_len.toNat ≤ ret.toNat → ret.toNat ≤ g_cap.toNat →
        (∀ idx < g_len.toNat, s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) →
        GateSeq F_cur s.core.cur_vars s'.scratch.scratch_buf ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

def m7ExtractIteAllSpec : Spec [i64, i32, i32, i64] [i32] :=
  m7ExtractIteAllGenSpec GateSeqOk32

def m7ExtractIteAllM6Spec : Spec [i64, i32, i32, i64] [i32] :=
  m7ExtractIteAllGenSpec M6GateSeqOk

theorem m7ExtractIteAllM6Spec_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {g_len g_cap : BitVec 32}
    {tick_lim : BitVec 64} {Q : Post [i32]} {X : XPost}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hdm : s.core.dense_mode ≠ 0#64) (hgl : g_len.toNat ≤ g_cap.toNat)
    (hcap : g_cap.toNat ≤ c.scratch_cap)
    (hseq : M6GateSeqOk F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ret : BitVec 32) (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → s'.core = s.core →
      s'.scratch.last_learned = s.scratch.last_learned →
      s'.scratch.extend_len = s.scratch.extend_len →
      g_len.toNat ≤ ret.toNat → ret.toNat ≤ g_cap.toNat →
      (∀ idx < g_len.toNat, s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) →
      M6GateSeqOk F_cur s.core.cur_vars s'.scratch.scratch_buf ret.toNat 0 →
      (FullMem c s' ⋆ R) m' → Q (ret, ()) m') :
    m7ExtractIteAllM6Spec (c.hdr, g_len, g_cap, tick_lim, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hgl, hcap, hseq, hm, hQ⟩

theorem m7ExtractIteAllM6Spec_monoX {xs : Tup Val [i64, i32, i32, i64]} {m : Mem 64}
    {Q : Post [i32]} {X X' : XPost} (h : m7ExtractIteAllM6Spec xs m Q X) :
    m7ExtractIteAllM6Spec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, ⟨⟩⟩; exact h

private theorem full_cong_extract_ite_all_m7_gen_wp (Γ : Env)
    (GateSeq : List (List Nat) → Nat → List (BitVec 32) → Nat → Nat → Prop)
    (hCopy : ∀ a m Q X, m7CopyCondbinSpec a m Q X →
      Γ "full_cong_copy_condbin_m7" [i64, i32, i64, i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, m7ExtractCondeqSpec a m Q X →
      Γ "full_cong_extract_condeq_m7" [i64, i64, i64, i64] [i64] a m Q X)
    (hMerge : ∀ a m Q X, m7MergeCondeqGenSpec GateSeq a m Q X →
      Γ "full_cong_merge_condeq_m7" [i64, i32, i64, i64, i32, i32] [i32] a m Q X) :
    ∀ args m Q X, m7ExtractIteAllGenSpec GateSeq args m Q X →
      Func.wp Γ full_cong_extract_ite_all_m7_body args m Q X := by
  rintro ⟨h, g_len, g_cap, tick_lim, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hgl_le, hcap_sc, hseq0, hm0, hQ⟩
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have hmv_max : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmv_max
  have hsc_lt : c.scratch_cap < dimacsBound := c.hscr
  unfold dimacsBound at hsc_lt
  have hmv_u64 : (BitVec.ofNat 64 c.max_vars).toNat = c.max_vars := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmv_lt61 : c.max_vars < 2 ^ 61 := by omega
  have hmv_u64_lt61 : (BitVec.ofNat 64 c.max_vars).toNat < 2 ^ 61 :=
    hmv_u64.symm ▸ hmv_lt61
  have hcv_lt : s.core.cur_vars < 2 ^ 64 := by omega
  fc_split_fast
  · have hgt : g_cap.toNat < g_len.toNat := by
      simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
    omega
  · clear hc; fc_split_fast
    · simp only [BitVec.ult, decide_eq_true_eq, bv_zext32_toNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64)] at hc; omega
    · clear hc; fc_split_fast
      · fc_steps
        exact hQ g_len s m0 hlen rfl rfl rfl (Nat.le_refl _) hgl_le (fun _ _ => rfl) hseq0 hm0
      · have hcv3 : 3 ≤ s.core.cur_vars := by
          have h3n : (3 : BitVec 64).toNat = 3 := rfl
          simp only [BitVec.ult, decide_eq_false_iff_not, not_lt, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt hcv_lt, h3n] at hc
          exact hc
        clear hc; fc_split_fast
        · simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : c.max_vars < 2 ^ 64),
            Nat.mod_eq_of_lt hcv_lt] at hc; omega
        · clear hc; fc_split_fast
          · fc_steps
            exact hQ g_len s m0 hlen rfl rfl rfl (Nat.le_refl _) hgl_le
              (fun _ _ => rfl) hseq0 hm0
          · clear hc
            obtain ⟨ws0, wk1_0, wk2_0, hws0_l, hwk1_0_l, hwk2_0_l, hm_wks⟩ :=
              focus_full_wks3_u64 hlen hm0
            let LoopInv : Tup Val [i64, i64, i32] → Mem 64 → Prop :=
              fun (v, _, gl, ()) ml =>
                v.toNat ≤ s.core.cur_vars ∧ m7AllInvGen GateSeq c F_cur s g_len g_cap R gl ml
            fc_steps; fc_to_group
            refine wp_loop_inv (ts := [i64, i64, i32]) LoopInv
              (fun (v, _, _) _ => s.core.cur_vars - v.toNat)
              (fun Jlp hJlp => by
                fc_steps
                exact hJlp (0#64, 0#64, g_len, ()) m0 ⟨Nat.zero_le _,
                  ⟨s, ws0, wk1_0, wk2_0, hlen, rfl, rfl, rfl, hws0_l, hwk1_0_l, hwk2_0_l,
                    Nat.le_refl _, hgl_le, fun _ _ => rfl, hseq0, hm_wks⟩⟩)
              (fun Jlp ⟨v, ticks, gl, ⟨⟩⟩ ml ⟨hv_le, hm_all⟩ ih => ?_)
            rcases hm_all with
              ⟨s_cur, ws, wk1, wk2, hlen_cur, hsc_core, hsc_ll, hsc_el,
                hwsl, hwk1l, hwk2l, hgl_ge, hgl_le', hpref, hseq, hml⟩
            have hret_exit : wp Γ Q X (.ret (.var gl, ())) ml := by
              obtain ⟨ws32, k1, k2, hws32l, hk1l, hk2l, hm'⟩ :=
                unfocus_full_wks3_u64 hwsl hwk1l hwk2l hml
              let s' : FullState := { s_cur with scratch :=
                { s_cur.scratch with wsort := ws32, work_stk1 := k1, work_stk2 := k2 } }
              have hs'_len : s'.LengthsOk c :=
                ⟨hlen_cur.core_ok, { hlen_cur.scratch_ok with
                  wsort_len := hws32l, work_stk1_len := hk1l, work_stk2_len := hk2l }⟩
              fc_steps
              exact hQ gl s' ml hs'_len hsc_core hsc_ll hsc_el hgl_ge hgl_le' hpref hseq hm'
            fc_split_fast
            · have hv_lt : v.toNat < s.core.cur_vars := by
                simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt hcv_lt] at hc; exact hc
              have hv_bd : v.toNat < 2 ^ 30 := by omega
              clear hc; fc_split_fast
              · clear hc; fc_split_fast
                · clear hc
                  have hfl_len : s_cur.core.flags.length = c.max_vars := by
                    have h := hlen_cur.core_ok.flags_len; omega
                  have hv_fl : v.toNat < s_cur.core.flags.length := by omega
                  have hv2_bd : (v <<< (1 : BitVec 64)).toNat < s_cur.core.vals.length := by
                    have hvl := hlen_cur.core_ok.vals_len
                    rw [bv64_shl1_bv_toNat]; omega
                  have hvp1_n : (v + 1#64).toNat = v.toNat + 1 := by
                    have h1n : (1#64 : BitVec 64).toNat = 1 := rfl
                    rw [BitVec.toNat_add, h1n, Nat.mod_eq_of_lt (by omega)]
                  let StepInv : Tup Val [i64, i32] → Mem 64 → Prop :=
                    fun (_, gn, ()) mn => m7AllInvGen GateSeq c F_cur s g_len g_cap R gn mn
                  fc_to_group
                  refine wp_join_group (ts := [i64, i32]) StepInv
                    (fun _ ⟨tn, gn, ⟨⟩⟩ mn hmn => by
                      fc_steps
                      exact ih (v + 1#64, tn, gn, ()) mn (by dsimp only; omega) ⟨by omega, hmn⟩)
                    (fun Jstep hJstep => ?_)
                  have hStep0 : StepInv (ticks, gl, ()) ml :=
                    ⟨s_cur, ws, wk1, wk2, hlen_cur, hsc_core, hsc_ll, hsc_el,
                      hwsl, hwk1l, hwk2l, hgl_ge, hgl_le', hpref, hseq, hml⟩
                  fc_split_fast
                  · clear hc; fc_split_fast
                    · clear hc
                      let lit0 := (v <<< (1 : BitVec 64)).setWidth 32
                      let lit1 := lit0 ||| 1#32
                      have hlit0_n : lit0.toNat = 2 * v.toNat := bv64_lit0_toNat hv_bd
                      have hlit1_n : lit1.toNat = 2 * v.toNat + 1 := bv64_lit1_toNat hv_bd
                      have hlit0_lt : lit0.toNat < 2 * s.core.cur_vars := by omega
                      have hlit1_lt : lit1.toNat < 2 * s.core.cur_vars := by omega
                      have hlit0_opp : litNeg lit0.toNat = lit1.toNat := by
                        unfold litNeg; change lit0.toNat ^^^ (1#32).toNat = lit1.toNat
                        rw [← BitVec.toNat_xor, bv64_lit0_xor1]
                      have hlit1_opp : litNeg lit1.toNat = lit0.toNat := by
                        unfold litNeg; change lit1.toNat ^^^ (1#32).toNat = lit0.toNat
                        rw [← BitVec.toNat_xor, bv64_lit1_xor1]
                      have hwv0_bd :
                          ((lit0.setWidth 64 <<< (1 : BitVec 64)) + 1#64).toNat <
                            s_cur.core.wvec.length := by
                        have hwl := hlen_cur.core_ok.wvec_len
                        rw [bv32_zext64_shl1_add1_toNat (by omega)]; omega
                      have hwv1_bd :
                          ((lit1.setWidth 64 <<< (1 : BitVec 64)) + 1#64).toNat <
                            s_cur.core.wvec.length := by
                        have hwl := hlen_cur.core_ok.wvec_len
                        rw [bv32_zext64_shl1_add1_toNat (by omega)]; omega
                      fc_to_group
                      refine wp_join_group (ts := [i64, i32]) StepInv
                        (fun _ ⟨tn, gn, ⟨⟩⟩ mn hst => by
                          fc_steps; exact hJstep (tn, gn, ()) mn hst)
                        (fun Jskip hJskip => ?_)
                      fc_to_group
                      refine wp_join_group (ts := []) (fun _ mn => mn = ml)
                        (fun _ _ mn hmn => by
                          subst mn; fc_steps; exact hJskip (ticks + 1#64, gl, ()) ml hStep0)
                        (fun Jsk hJsk => ?_)
                      fc_split_fast
                      · fc_steps; exact hJsk () ml rfl
                      · clear hc; fc_split_fast
                        · fc_steps; exact hJsk () ml rfl
                        · clear hc
                          let ticks' := ticks + 1#64 +
                            (s_cur.core.wvec[((lit0.setWidth 64 <<< (1 : BitVec 64)) +
                              1#64).toNat]'hwv0_bd).setWidth 64 +
                            (s_cur.core.wvec[((lit1.setWidth 64 <<< (1 : BitVec 64)) +
                              1#64).toNat]'hwv1_bd).setWidth 64
                          let FlipInv (sl ll : BitVec 32) (d0 d1 : BitVec 64)
                              (flp : Bool) : Prop :=
                            sl.toNat < 2 * s.core.cur_vars ∧ ll.toNat < 2 * s.core.cur_vars ∧
                            (flp = true → sl = lit1 ∧ ll = lit0 ∧
                              d0 = c.pWorkStk1 ∧ d1 = c.pWorkStk2) ∧
                            (flp = false → sl = lit0 ∧ ll = lit1 ∧
                              d0 = c.pWorkStk2 ∧ d1 = c.pWorkStk1)
                          fc_to_group
                          refine wp_join_group (ts := [i32, i32, i64, i64, .bool])
                            (fun (sl, ll, d0, d1, flp, ()) mf =>
                              mf = ml ∧ FlipInv sl ll d0 d1 flp)
                            (fun _ ⟨sl, ll, d0, d1, flp, ⟨⟩⟩ mf
                              ⟨hmf, hsl_lt, hll_lt, hft, hff⟩ => ?_)
                            (fun Jfl hJfl => ?_)
                          · subst mf
                            have hw_cur : FullWitnessInv c F0 F_cur s_cur.core := by
                              rw [hsc_core]; exact hw
                            have hdm_cur : s_cur.core.dense_mode ≠ 0#64 := by
                              rw [hsc_core]; exact hdm
                            have hsl_lt' : sl.toNat < 2 * s_cur.core.cur_vars := by
                              rw [hsc_core]; exact hsl_lt
                            have hll_lt' : ll.toNat < 2 * s_cur.core.cur_vars := by
                              rw [hsc_core]; exact hll_lt
                            have hcv3' : 3 ≤ s_cur.core.cur_vars := by
                              rw [hsc_core]; exact hcv3
                            have hlit0_lt' : lit0.toNat < 2 * s_cur.core.cur_vars := by
                              rw [hsc_core]; exact hlit0_lt
                            have hm_unswap : ∀ {wsx : List (BitVec 64)} {mx : Mem 64},
                                (FullMemNoWks3 c s_cur ⋆ array64 c.pWsort wsx ⋆
                                  (array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R)) mx →
                                (array64 c.pWsort wsx ⋆
                                  array64 d0 (if flp then wk1 else wk2) ⋆
                                  (FullMemNoWks3 c s_cur ⋆
                                    array64 d1 (if flp then wk2 else wk1) ⋆ R)) mx := by
                              intro wsx mx hmx
                              cases flp with
                              | true =>
                                have hq := hft rfl; rw [hq.2.2.1, hq.2.2.2]; dsimp
                                exact sep_ac hmx
                              | false =>
                                have hq := hff rfl; rw [hq.2.2.1, hq.2.2.2]; dsimp
                                exact sep_ac hmx
                            have hm_swap : ∀ {wsx x y : List (BitVec 64)} {scx : FullState}
                                {mx : Mem 64},
                                (FullMemNoWks3 c scx ⋆ array64 c.pWsort wsx ⋆
                                  array64 d0 x ⋆ array64 d1 y ⋆ R) mx →
                                (FullMemNoWks3 c scx ⋆
                                  array64 c.pWorkStk1 (if flp then x else y) ⋆
                                  array64 c.pWorkStk2 (if flp then y else x) ⋆
                                  (array64 c.pWsort wsx ⋆ R)) mx := by
                              intro wsx x y scx mx hmx
                              cases flp with
                              | true =>
                                have hq := hft rfl; rw [hq.2.2.1, hq.2.2.2] at hmx; dsimp
                                exact sep_ac hmx
                              | false =>
                                have hq := hff rfl; rw [hq.2.2.1, hq.2.2.2] at hmx; dsimp
                                exact sep_ac hmx
                            have mkInv : ∀ {ws' wk1' wk2' : List (BitVec 64)} {mx},
                                ws'.length = c.max_vars → wk1'.length = c.max_vars →
                                wk2'.length = c.max_vars →
                                (FullMemNoWks3 c s_cur ⋆ array64 c.pWsort ws' ⋆
                                  array64 c.pWorkStk1 wk1' ⋆
                                  array64 c.pWorkStk2 wk2' ⋆ R) mx →
                                m7AllInvGen GateSeq c F_cur s g_len g_cap R gl mx :=
                              fun hws hk1 hk2 hmx =>
                                ⟨s_cur, _, _, _, hlen_cur, hsc_core, hsc_ll, hsc_el, hws, hk1, hk2,
                                  hgl_ge, hgl_le', hpref, hseq, hmx⟩
                            fc_steps; c0_call hCopy
                            refine m7CopyCondbinSpec_mk ws
                              (array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R)
                              hlen_cur hw_cur hdm_cur hsl_lt' (hwsl.trans hmv_u64.symm)
                              hmv_u64_lt61 (sep_ac hml)
                              fun m0c ws1 m1c hws1_l hm0_le hcb0_sort hcb0_ok hm1c => ?_
                            fc_to_group
                            refine wp_join_group (ts := [i32])
                              (fun (g5, ()) m5 => m7AllInvGen GateSeq c F_cur s g_len g_cap R g5 m5)
                              (fun _ ⟨g5, ⟨⟩⟩ m5 h5 => by
                                fc_steps; exact hJskip (ticks', g5, ()) m5 h5)
                              (fun J5 hJ5 => ?_)
                            fc_split_fast
                            · clear hc
                              have hd0_l : (if flp then wk1 else wk2).length = c.max_vars := by
                                cases flp <;> simp [hwk1l, hwk2l]
                              fc_steps; c0_call hExt
                              refine ⟨F_cur, s_cur.core.cur_vars, sl.toNat, ws1,
                                if flp then wk1 else wk2,
                                FullMemNoWks3 c s_cur ⋆
                                  array64 d1 (if flp then wk2 else wk1) ⋆ R,
                                Nat.le_trans hm0_le (Nat.le_of_eq hws1_l.symm),
                                hws1_l ▸ hmv_u64_lt61,
                                hcb0_sort, hcb0_ok, hd0_l.trans hmv_u64.symm, hmv_u64_lt61,
                                hm_unswap (sep_ac hm1c),
                                fun n0 d0_1 m2c hd01_l hn0_le hceq0_ok hm2c => ?_⟩
                              fc_to_group
                              refine wp_join_group (ts := [i32])
                                (fun (g6, ()) m6 =>
                                  m7AllInvGen GateSeq c F_cur s g_len g_cap R g6 m6)
                                (fun _ ⟨g6, ⟨⟩⟩ m6 h6 => by fc_steps; exact hJ5 (g6, ()) m6 h6)
                                (fun J6 hJ6 => ?_)
                              fc_split_fast
                              · clear hc
                                fc_steps; c0_call hCopy
                                refine m7CopyCondbinSpec_mk ws1
                                  (array64 d0 d0_1 ⋆
                                    array64 d1 (if flp then wk2 else wk1) ⋆ R)
                                  hlen_cur hw_cur hdm_cur hll_lt' hws1_l
                                  (hws1_l ▸ hmv_u64_lt61) (sep_ac hm2c)
                                  fun m1c' ws2 m3c hws2_l hm1_le hcb1_sort hcb1_ok hm3c => ?_
                                fc_to_group
                                refine wp_join_group (ts := [i32])
                                  (fun (g7, ()) m7 =>
                                    m7AllInvGen GateSeq c F_cur s g_len g_cap R g7 m7)
                                  (fun _ ⟨g7, ⟨⟩⟩ m7 h7 => by fc_steps; exact hJ6 (g7, ()) m7 h7)
                                  (fun J7 hJ7 => ?_)
                                fc_split_fast
                                · clear hc
                                  have hd1_l :
                                      (if flp then wk2 else wk1).length = c.max_vars := by
                                    cases flp <;> simp [hwk1l, hwk2l]
                                  fc_steps; c0_call hExt
                                  refine ⟨F_cur, s_cur.core.cur_vars, ll.toNat, ws2,
                                    if flp then wk2 else wk1,
                                    FullMemNoWks3 c s_cur ⋆ array64 d0 d0_1 ⋆ R,
                                    Nat.le_trans hm1_le (Nat.le_of_eq hws2_l.symm),
                                    hws2_l ▸ hmv_u64_lt61,
                                    hcb1_sort, hcb1_ok, hd1_l.trans hmv_u64.symm, hmv_u64_lt61,
                                    sep_ac hm3c,
                                    fun n1 d1_1 m4c hd11_l hn1_le hceq1_ok hm4c => ?_⟩
                                  fc_to_group
                                  refine wp_join_group (ts := [i32])
                                    (fun (g8, ()) m8 =>
                                      m7AllInvGen GateSeq c F_cur s g_len g_cap R g8 m8)
                                    (fun _ ⟨g8, ⟨⟩⟩ m8 h8 => by
                                      fc_steps; exact hJ7 (g8, ()) m8 h8)
                                    (fun J8 hJ8 => ?_)
                                  fc_split_fast
                                  · clear hc
                                    fc_to_group
                                    refine wp_join_group (ts := [i32])
                                      (fun (g9, ()) m9 =>
                                        m7AllInvGen GateSeq c F_cur s g_len g_cap R g9 m9)
                                      (fun _ ⟨g9, ⟨⟩⟩ m9 h9 => by
                                        fc_steps; exact hJ8 (g9, ()) m9 h9)
                                      (fun J9 hJ9 => ?_)
                                    let w1f := if flp then d0_1 else d1_1
                                    let w2f := if flp then d1_1 else d0_1
                                    have hw1f_l : w1f.length = c.max_vars := by
                                      cases flp <;> simp [w1f, hd01_l, hd11_l, hmv_u64]
                                    have hw2f_l : w2f.length = c.max_vars := by
                                      cases flp <;> simp [w2f, hd01_l, hd11_l, hmv_u64]
                                    have hm4c_w :
                                        (FullMemNoWks3 c s_cur ⋆ array64 c.pWorkStk1 w1f ⋆
                                          array64 c.pWorkStk2 w2f ⋆
                                          (array64 c.pWsort ws2 ⋆ R)) m4c :=
                                      hm_swap (sep_ac hm4c)
                                    have hMPost : ∀ {gl' scr' m5c},
                                        scr'.length = s_cur.scratch.scratch_buf.length →
                                        g_len.toNat ≤ gl'.toNat → gl'.toNat ≤ g_cap.toNat →
                                        (∀ idx < gl.toNat,
                                          scr'[idx]? = s_cur.scratch.scratch_buf[idx]?) →
                                        GateSeq F_cur s_cur.core.cur_vars scr' gl'.toNat 0 →
                                        (FullMemNoWks3 c
                                          { s_cur with scratch :=
                                            { s_cur.scratch with scratch_buf := scr' } } ⋆
                                          array64 c.pWorkStk1 w1f ⋆ array64 c.pWorkStk2 w2f ⋆
                                          (array64 c.pWsort ws2 ⋆ R)) m5c →
                                        wp Γ Q X (.jump J9 (.var gl', ())) m5c := by
                                      intro gl' scr' m5c hs'_l hg1 hg2 hp' hsq' hm5c
                                      obtain ⟨s_nxt, hs_nxt⟩ : ∃ s_nxt : FullState,
                                          s_nxt = { s_cur with scratch :=
                                            { s_cur.scratch with scratch_buf := scr' } } := ⟨_, rfl⟩
                                      have hn_len : s_nxt.LengthsOk c := by
                                        rw [hs_nxt]
                                        exact ⟨hlen_cur.core_ok, { hlen_cur.scratch_ok with
                                          scratch_buf_len :=
                                            hs'_l.trans hlen_cur.scratch_ok.scratch_buf_len }⟩
                                      have hn_core : s_nxt.core = s.core := by
                                        rw [hs_nxt]; exact hsc_core
                                      have hn_ll :
                                          s_nxt.scratch.last_learned = s.scratch.last_learned := by
                                        rw [hs_nxt]; exact hsc_ll
                                      have hn_el :
                                          s_nxt.scratch.extend_len = s.scratch.extend_len := by
                                        rw [hs_nxt]; exact hsc_el
                                      have hn_sb : s_nxt.scratch.scratch_buf = scr' := by
                                        rw [hs_nxt]
                                      rw [← hs_nxt] at hm5c; clear hs_nxt
                                      fc_steps
                                      exact hJ9 (gl', ()) m5c ⟨s_nxt, ws2, w1f, w2f, hn_len,
                                        hn_core, hn_ll, hn_el, hws2_l.trans hmv_u64, hw1f_l, hw2f_l,
                                        hg1, hg2, fun idx hidx => by
                                          rw [hn_sb]
                                          exact (hp' idx (Nat.lt_of_lt_of_le hidx hgl_ge)).trans
                                            (hpref idx hidx),
                                        by rw [hn_sb, ← hsc_core]; exact hsq', sep_ac hm5c⟩
                                    fc_split_fast
                                    · have hfl_t : flp = true := hc
                                      have hq := hft hfl_t
                                      have hw1_t : w1f = d0_1 := by simp [w1f, hfl_t]
                                      have hw2_t : w2f = d1_1 := by simp [w2f, hfl_t]
                                      fc_steps; c0_call hMerge
                                      exact ⟨c, F0, F_cur, s_cur, w1f, w2f,
                                        array64 c.pWsort ws2 ⋆ R, rfl, hlen_cur, hw_cur, hcv3',
                                        hlit0_lt', hcap_sc,
                                        hw1_t ▸ Nat.le_trans hn0_le (Nat.le_of_eq hd01_l.symm),
                                        hw2_t ▸ Nat.le_trans hn1_le (Nat.le_of_eq hd11_l.symm),
                                        hw1f_l.symm ▸ hmv_lt61, hw2f_l.symm ▸ hmv_lt61,
                                        fun idx hidx => by
                                          have heq : litNeg (BitVec.setWidth 32 (v <<< 1)).toNat =
                                              sl.toNat := by
                                            change litNeg lit0.toNat = sl.toNat
                                            rw [hlit0_opp, hq.1]
                                          rw [hw1_t, heq]; exact hceq0_ok idx hidx,
                                        fun idx hidx => by
                                          have heq : (BitVec.setWidth 32 (v <<< 1)).toNat =
                                              ll.toNat :=
                                            congrArg BitVec.toNat hq.2.1.symm
                                          rw [hw2_t, heq]; exact hceq1_ok idx hidx,
                                        by rw [hsc_core]; exact hseq, hm4c_w,
                                        fun _ _ _ hs'_l hgl_b =>
                                          hMPost hs'_l (Nat.le_trans hgl_ge (hgl_b hgl_le').1)
                                            (hgl_b hgl_le').2⟩
                                    · have hfl_f : flp = false := hc
                                      have hq := hff hfl_f
                                      have hw1_f : w1f = d1_1 := by simp [w1f, hfl_f]
                                      have hw2_f : w2f = d0_1 := by simp [w2f, hfl_f]
                                      fc_steps; c0_call hMerge
                                      exact ⟨c, F0, F_cur, s_cur, w1f, w2f,
                                        array64 c.pWsort ws2 ⋆ R, rfl, hlen_cur, hw_cur, hcv3',
                                        hlit0_lt', hcap_sc,
                                        hw1_f ▸ Nat.le_trans hn1_le (Nat.le_of_eq hd11_l.symm),
                                        hw2_f ▸ Nat.le_trans hn0_le (Nat.le_of_eq hd01_l.symm),
                                        hw1f_l.symm ▸ hmv_lt61, hw2f_l.symm ▸ hmv_lt61,
                                        fun idx hidx => by
                                          have heq : litNeg (BitVec.setWidth 32 (v <<< 1)).toNat =
                                              ll.toNat := by
                                            change litNeg lit0.toNat = ll.toNat
                                            rw [hlit0_opp, hq.2.1]
                                          rw [hw1_f, heq]; exact hceq1_ok idx hidx,
                                        fun idx hidx => by
                                          have heq : (BitVec.setWidth 32 (v <<< 1)).toNat =
                                              sl.toNat :=
                                            congrArg BitVec.toNat hq.1.symm
                                          rw [hw2_f, heq]; exact hceq0_ok idx hidx,
                                        by rw [hsc_core]; exact hseq, hm4c_w,
                                        fun _ _ _ hs'_l hgl_b =>
                                          hMPost hs'_l (Nat.le_trans hgl_ge (hgl_b hgl_le').1)
                                            (hgl_b hgl_le').2⟩
                                  · fc_steps
                                    have h1l : (if flp then d0_1 else d1_1).length =
                                        c.max_vars := by
                                      cases flp <;> simp [hd01_l, hd11_l, hmv_u64]
                                    have h2l : (if flp then d1_1 else d0_1).length =
                                        c.max_vars := by
                                      cases flp <;> simp [hd01_l, hd11_l, hmv_u64]
                                    exact hJ8 (gl, ()) m4c (mkInv (hws2_l.trans hmv_u64)
                                      h1l h2l (sep_ac (hm_swap (sep_ac hm4c))))
                                · fc_steps
                                  have hxl : (if flp then d0_1 else
                                      if flp then wk2 else wk1).length = c.max_vars := by
                                    cases flp <;> simp [hd01_l, hwk1l, hmv_u64]
                                  have hyl : (if flp then (if flp then wk2 else wk1) else
                                      d0_1).length = c.max_vars := by
                                    cases flp <;> simp [hd01_l, hwk2l, hmv_u64]
                                  exact hJ7 (gl, ()) m3c (mkInv (hws2_l.trans hmv_u64)
                                    hxl hyl (sep_ac (hm_swap (sep_ac hm3c))))
                              · fc_steps
                                have hxl : (if flp then d0_1 else
                                    if flp then wk2 else wk1).length = c.max_vars := by
                                  cases flp <;> simp [hd01_l, hwk1l, hmv_u64]
                                have hyl : (if flp then (if flp then wk2 else wk1) else
                                    d0_1).length = c.max_vars := by
                                  cases flp <;> simp [hd01_l, hwk2l, hmv_u64]
                                exact hJ6 (gl, ()) m2c (mkInv (hws1_l.trans hmv_u64)
                                  hxl hyl (sep_ac (hm_swap (sep_ac hm2c))))
                            · fc_steps
                              exact hJ5 (gl, ()) m1c
                                (mkInv (hws1_l.trans hmv_u64) hwk1l hwk2l (sep_ac hm1c))
                          · fc_split_fast
                            · fc_steps
                              exact hJfl (lit1, lit0, c.pWorkStk1, c.pWorkStk2, true, ()) ml
                                ⟨rfl, hlit1_lt, hlit0_lt, fun _ => ⟨rfl, rfl, rfl, rfl⟩,
                                  fun h => False.elim (Bool.noConfusion h)⟩
                            · fc_steps
                              exact hJfl (lit0, lit1, c.pWorkStk2, c.pWorkStk1, false, ()) ml
                                ⟨rfl, hlit0_lt, hlit1_lt,
                                  fun h => False.elim (Bool.noConfusion h),
                                  fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩
                    · fc_steps; exact hJstep (ticks, gl, ()) ml hStep0
                  · fc_steps; exact hJstep (ticks, gl, ()) ml hStep0
                · exact hret_exit
              · exact hret_exit
            · exact hret_exit

theorem full_cong_extract_ite_all_m7_wp (Γ : Env)
    (hCopy : ∀ a m Q X, m7CopyCondbinSpec a m Q X →
      Γ "full_cong_copy_condbin_m7" [i64, i32, i64, i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, m7ExtractCondeqSpec a m Q X →
      Γ "full_cong_extract_condeq_m7" [i64, i64, i64, i64] [i64] a m Q X)
    (hMerge : ∀ a m Q X, m7MergeCondeqSpec a m Q X →
      Γ "full_cong_merge_condeq_m7" [i64, i32, i64, i64, i32, i32] [i32] a m Q X) :
    ∀ args m Q X, m7ExtractIteAllSpec args m Q X →
      Func.wp Γ full_cong_extract_ite_all_m7_body args m Q X :=
  full_cong_extract_ite_all_m7_gen_wp Γ GateSeqOk32 hCopy hExt hMerge

theorem full_cong_extract_ite_all_m7_m6_wp (Γ : Env)
    (hCopy : ∀ a m Q X, m7CopyCondbinSpec a m Q X →
      Γ "full_cong_copy_condbin_m7" [i64, i32, i64, i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, m7ExtractCondeqSpec a m Q X →
      Γ "full_cong_extract_condeq_m7" [i64, i64, i64, i64] [i64] a m Q X)
    (hMerge : ∀ a m Q X, m7MergeCondeqM6Spec a m Q X →
      Γ "full_cong_merge_condeq_m7" [i64, i32, i64, i64, i32, i32] [i32] a m Q X) :
    ∀ args m Q X, m7ExtractIteAllM6Spec args m Q X →
      Func.wp Γ full_cong_extract_ite_all_m7_body args m Q X :=
  full_cong_extract_ite_all_m7_gen_wp Γ M6GateSeqOk hCopy hExt hMerge

/-- `FullDenseInv`-preserving wrapper for `full_cong_extract_ite_all_m7`. -/
theorem full_cong_extract_ite_all_m7_dense_wp (Γ : Env)
    (hCopy : ∀ a m Q X, m7CopyCondbinSpec a m Q X →
      Γ "full_cong_copy_condbin_m7" [i64, i32, i64, i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, m7ExtractCondeqSpec a m Q X →
      Γ "full_cong_extract_condeq_m7" [i64, i64, i64, i64] [i64] a m Q X)
    (hMerge : ∀ a m Q X, m7MergeCondeqSpec a m Q X →
      Γ "full_cong_merge_condeq_m7" [i64, i32, i64, i64, i32, i32] [i32] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m0 : Mem 64} {g_len g_cap : BitVec 32} {tick_lim : BitVec 64}
    {Q : Post [i32]} {X : XPost}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hden : FullDenseInv c F0 s) (hgl : g_len.toNat ≤ g_cap.toNat)
    (hcap : g_cap.toNat ≤ c.scratch_cap)
    (hseq : GateSeqOk32 F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0)
    (hm : (FullMem c s ⋆ R) m0)
    (hQ : ∀ (ret : BitVec 32) (s' : FullState) (m' : Mem 64),
      FullDenseInv c F0 s' → FullWitnessInv c F0 F_cur s'.core → s'.core = s.core →
      g_len.toNat ≤ ret.toNat → ret.toNat ≤ g_cap.toNat →
      (∀ idx < g_len.toNat, s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) →
      GateSeqOk32 F_cur s.core.cur_vars s'.scratch.scratch_buf ret.toNat 0 →
      (FullMem c s' ⋆ R) m' → Q (ret, ()) m') :
    Func.wp Γ full_cong_extract_ite_all_m7_body (c.hdr, g_len, g_cap, tick_lim, ()) m0 Q X := by
  refine full_cong_extract_ite_all_m7_wp Γ hCopy hExt hMerge
    (c.hdr, g_len, g_cap, tick_lim, ()) m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hden.2.2.2.2.2, hgl, hcap, hseq, hm,
      fun ret s' m' hs'_len hs'_core hs'_ll hs'_el hg1 hg2 hpref hseq' hm' => ?_⟩
  have hw' : FullWitnessInv c F0 F_cur s'.core := by simpa only [hs'_core] using hw
  have hmk' : FullLitMarksClear c s' :=
    fullLitMarksClear_of_eq hden.2.1 (congrArg FullCoreState.mrk hs'_core)
      (congrArg FullCoreState.lit_mark hs'_core)
  have hnd' : FullArenaVarsNodup s' :=
    fullArenaVarsNodup_of_eq hden.2.2.1 (congrArg FullCoreState.arena hs'_core)
      (congrArg FullCoreState.arena_len hs'_core)
  have hext' : FullExtScratchOk c s' :=
    fullExtScratchOk_of_eq hden.2.2.2.1 (congrArg FullCoreState.arena hs'_core)
      (congrArg FullCoreState.arena_len hs'_core) hs'_ll hs'_el
  exact hQ ret s' m' ⟨⟨hs'_len, F_cur, hw'⟩, hmk', hnd', hext',
    by rw [hs'_core]; exact hden.2.2.2.2.1, by rw [hs'_core]; exact hden.2.2.2.2.2⟩
    hw' hs'_core hg1 hg2 hpref hseq' hm'

/-! ## 8. Closed `ModuleOk` & Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`) -/

/-- Closed `7`-row specification table matching `m7CongIteModule.fns` (`0` externs, `0` exits). -/
def m7CongIteSpecTable : List SpecEntry :=
  [ ⟨"full_cong_u64_sift_m7", [i64, i64, i64], [], m7U64SiftSpec, true⟩
  , ⟨"full_cong_u64_sort_m7", [i64, i64], [], m7U64SortSpec, true⟩
  , ⟨"full_cong_bsearch_u64_m7", [i64, i64, i64, i64], [.bool], m7BsearchU64Spec, true⟩
  , ⟨"full_cong_copy_condbin_m7", [i64, i32, i64, i64], [i64], m7CopyCondbinSpec, true⟩
  , ⟨"full_cong_extract_condeq_m7", [i64, i64, i64, i64], [i64], m7ExtractCondeqSpec, true⟩
  , ⟨"full_cong_merge_condeq_m7", [i64, i32, i64, i64, i32, i32], [i32],
      m7MergeCondeqSpec, true⟩
  , ⟨"full_cong_extract_ite_all_m7", [i64, i32, i32, i64], [i32], m7ExtractIteAllSpec, true⟩
  ]

/-- Closed specification environment for `m7CongIteModule`. -/
def m7CongIteEnv : Env := Env.ofTable m7CongIteSpecTable

theorem m7CongIteSpecTable_sigs :
    m7CongIteSpecTable.map (fun e => (e.name, e.as, e.rs)) = m7CongIteModule.sigs := by
  t_kernel_rfl

theorem m7CongIteSpecTable_noExit : ∀ e ∈ m7CongIteSpecTable, e.noExit = true := by
  intro e he
  simp only [m7CongIteSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem m7CongIteSpecTable_nodup : (m7CongIteSpecTable.map SpecEntry.name).Nodup := by
  have hchk := m7CongIte_acyclic
  simp only [m7CongIteModule, Module.checkAcyclic, Bool.and_eq_true] at hchk
  have hnd := Module.namesNodup_of_checkNamesNodup hchk.1
  have hnames : m7CongIteSpecTable.map SpecEntry.name = m7CongIteModule.names := by
    have hm := congrArg (List.map Prod.fst) m7CongIteSpecTable_sigs
    simpa only [List.map_map, Function.comp_def, Module.sigs, Module.names, Fn.sig, Extern.sig,
      List.map_append] using hm
  rw [hnames]; exact hnd

private theorem m7Env_row (i : Nat) (e : SpecEntry)
    (hi : m7CongIteSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → m7CongIteEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) m7CongIteSpecTable_nodup (hno xs m Q X h)

private theorem m7_allFns_of_forall {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | _ :: _, h =>
    ⟨h _ List.mem_cons_self, m7_allFns_of_forall fun f hf => h f (List.mem_cons_of_mem _ hf)⟩

theorem m7CongIte_tableImpl :
    TableImpl m7CongIteEnv m7CongIteModule.fns m7CongIteSpecTable := by
  have r0 := m7Env_row 0 ⟨"full_cong_u64_sift_m7", [i64, i64, i64], [], m7U64SiftSpec, true⟩
    (hno := fun _ _ _ _ h => m7U64SiftSpec_noExit h)
  have r1 := m7Env_row 1 ⟨"full_cong_u64_sort_m7", [i64, i64], [], m7U64SortSpec, true⟩
    (hno := fun _ _ _ _ h => m7U64SortSpec_noExit h)
  have r2 := m7Env_row 2
    ⟨"full_cong_bsearch_u64_m7", [i64, i64, i64, i64], [.bool], m7BsearchU64Spec, true⟩
    (hno := fun _ _ _ _ h => m7BsearchU64Spec_noExit h)
  have r3 := m7Env_row 3
    ⟨"full_cong_copy_condbin_m7", [i64, i32, i64, i64], [i64], m7CopyCondbinSpec, true⟩
    (hno := fun _ _ _ _ h => m7CopyCondbinSpec_noExit h)
  have r4 := m7Env_row 4
    ⟨"full_cong_extract_condeq_m7", [i64, i64, i64, i64], [i64], m7ExtractCondeqSpec, true⟩
  have r5 := m7Env_row 5
    ⟨"full_cong_merge_condeq_m7", [i64, i32, i64, i64, i32, i32], [i32],
      m7MergeCondeqSpec, true⟩
  exact ⟨
    .of (full_cong_u64_sift_m7_wp m7CongIteEnv),
    .of (full_cong_u64_sort_m7_wp m7CongIteEnv r0),
    .of (full_cong_bsearch_u64_m7_wp m7CongIteEnv),
    .of (full_cong_copy_condbin_m7_wp m7CongIteEnv r1),
    .of (full_cong_extract_condeq_m7_wp m7CongIteEnv r1 r2),
    .of (full_cong_merge_condeq_m7_wp m7CongIteEnv),
    .of (full_cong_extract_ite_all_m7_wp m7CongIteEnv r3 r4 r5),
    trivial⟩

/-- Closed `ModuleOk` for `m7CongIteModule` under `m7CongIteEnv`. -/
theorem m7CongIte_moduleOk : ModuleOk m7CongIteEnv m7CongIteModule :=
  Env.ofTable_moduleOk m7CongIte_acyclic (m7_allFns_of_forall m7CongIteFns_wf)
    m7CongIte_tableImpl

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_cong_extract_ite_all_m7`
under closed `m7CongIteEnv` (`FullDefSweep.nvDefSweepCfg`, `nvDefSweepState`, `nvDefSweepMem`). -/
theorem m7_cong_extract_ite_all_nv :
    Func.wp m7CongIteEnv full_cong_extract_ite_all_m7_body
      (FullDefSweep.nvDefSweepCfg.hdr, 0#32, 128#32, 1024#64, ()) FullDefSweep.nvDefSweepMem
      (fun (ret, ()) m' => ∃ s' : FullState,
        FullDenseInv FullDefSweep.nvDefSweepCfg nvOneLitF0 s' ∧
        nvOneLitF0.Unsat ∧ ret.toNat ≤ 128 ∧
        GateSeqOk32 [[0], [1]] 1 s'.scratch.scratch_buf ret.toNat 0 ∧
        FullMem FullDefSweep.nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullDefSweep.nvDefSweepCfg FullDefSweep.nvDefSweepState ⋆ emp)
      FullDefSweep.nvDefSweepMem := by
    rw [sep_emp]; exact FullDefSweep.nvDefSweepMem_ok
  have hcv1 : FullDefSweep.nvDefSweepState.core.cur_vars = 1 := rfl
  exact full_cong_extract_ite_all_m7_dense_wp m7CongIteEnv
    (m7Env_row 3
      ⟨"full_cong_copy_condbin_m7", [i64, i32, i64, i64], [i64], m7CopyCondbinSpec, true⟩
      (hno := fun _ _ _ _ h => m7CopyCondbinSpec_noExit h))
    (m7Env_row 4
      ⟨"full_cong_extract_condeq_m7", [i64, i64, i64, i64], [i64], m7ExtractCondeqSpec, true⟩)
    (m7Env_row 5
      ⟨"full_cong_merge_condeq_m7", [i64, i32, i64, i64, i32, i32], [i32],
        m7MergeCondeqSpec, true⟩)
    FullDefSweep.nvDefSweepState_lengths FullDefSweep.nvDefSweep_invW.2.1
    FullDefSweep.nvDefSweep_invW.toDense (by decide) (by decide) .done hm
    fun ret s' m' hd _ hcore _ hle _ hseq hm' =>
      ⟨s', hd, FullDefSweep.nvDefSweepF0_unsat, hle,
        by simpa [hcore, hcv1] using hseq, by rwa [sep_emp] at hm'⟩

end LeanQbe.T.Examples.Kissat.FullM7CongIte
