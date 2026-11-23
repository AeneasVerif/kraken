module

public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof4a
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave-4E (`FullM7BveGates`) Proofs — Part 4b (`K6` Prop, Analyze, Solve)

M1-clean proof module (`public section`, `0` `@[expose]`, `0` `import all`, `private` helpers):
- `full_k6_prop_m7_wp`: certifies `fullK6PropM7Spec`.
- `full_k6_analyze_m7_wp`: certifies `fullK6AnalyzeM7Spec`.
- `full_k6_solve_m7_wp`: certifies `fullK6SolveM7Spec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7BveGates

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

open scoped K6Tactics

local macro "m7_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. Pure Frame & Arithmetic Helpers -/

private theorem k6b_get_eq {kb : List (BitVec 32)} {i : Nat} (hi : i < kb.length) :
    kb[i]?.getD 0#32 = kb[i]'hi := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some]

private theorem k6b_get_congr {α : Type} {xs : List α} {i j : Nat}
    (h : i = j) (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

private theorem k6b_set_congr {α : Type} {xs : List α} {i j : Nat} {a b : α}
    (hi : i = j) (ha : a = b) : xs.set i a = xs.set j b := by
  subst hi ha; rfl

private theorem k6b_elem_of_opt {xs ys : List (BitVec 32)} {i : Nat}
    (h : xs[i]? = ys[i]?) (hx : i < xs.length) (hy : i < ys.length) :
    xs[i]'hx = ys[i]'hy := by
  rw [List.getElem?_eq_getElem hx, List.getElem?_eq_getElem hy] at h
  exact Option.some.inj h

private theorem k6b_add1_toNat {a : BitVec 32} {lim : Nat} (ha : a.toNat < lim)
    (hl : lim < 2 ^ 32) : (a + 1#32).toNat = a.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega)]

private theorem k6b_sub1_toNat {a : BitVec 32} (ha : 0 < a.toNat) :
    (a - 1#32).toNat = a.toNat - 1 := by
  rw [BitVec.toNat_sub, show (1#32 : BitVec 32).toNat = 1 from rfl]
  have := a.isLt; omega

private theorem k6b_bv64_sub1_toNat {a : BitVec 64} (ha : 0 < a.toNat) :
    (a - 1#64).toNat = a.toNat - 1 := by
  rw [BitVec.toNat_sub, show (1#64 : BitVec 64).toNat = 1 from rfl]
  have := a.isLt; omega

private theorem k6b_off_sz_nowarp {o s acap len : Nat} (hos : o + s ≤ acap)
    (hle : 2912 + acap ≤ len) (hlt : len < 2 ^ 28) : o + s < 2 ^ 32 := by
  omega

private theorem k6b_slot_xor1_lt {w : BitVec 32} :
    ((w &&& 1#32) ^^^ 1#32).toNat < 2 := by
  have hlt : (w &&& 1#32).toNat < 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl]
    have := Nat.and_le_right (n := w.toNat) (m := 1); omega
  have h : (w &&& 1#32) = 0#32 ∨ (w &&& 1#32) = 1#32 := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h0 | h1
    · left; apply BitVec.eq_of_toNat_eq
      rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega
    · right; apply BitVec.eq_of_toNat_eq
      rw [show (1#32 : BitVec 32).toNat = 1 from rfl]; exact h1
  rcases h with h0 | h1
  · rw [h0]; decide
  · rw [h1]; decide

private theorem k6b_slot_lt {w : BitVec 32} : (w &&& 1#32).toNat < 2 := by
  rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl]
  have h1 : w.toNat &&& 1 ≤ 1 := Nat.and_le_right
  omega

/-- Frame invariant preserving `K6BufOk` plus `[0, 1, 2, 14, 15]` and all `[1888..2656)` clause
metadata across `prop` and the analysis phase prior to incrementing `k[KH_NC]`. -/
private def PropKeep (kbuf kb : List (BitVec 32)) : Prop :=
  K6BufOk kb ∧ kb.length = kbuf.length ∧
  kb[0]? = kbuf[0]? ∧ kb[1]? = kbuf[1]? ∧ kb[2]? = kbuf[2]? ∧
  kb[14]? = kbuf[14]? ∧ kb[15]? = kbuf[15]? ∧
  (∀ cid < 256, kb[1888 + cid]? = kbuf[1888 + cid]? ∧
    kb[2144 + cid]? = kbuf[2144 + cid]? ∧
    kb[2400 + cid]? = kbuf[2400 + cid]?)

private theorem propKeep_refl {kbuf : List (BitVec 32)} (h : K6BufOk kbuf) :
    PropKeep kbuf kbuf :=
  ⟨h, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl, rfl⟩⟩

private theorem propKeep_of_frame {kbuf kb kb' : List (BitVec 32)} (hk : PropKeep kbuf kb)
    (hlen : kb'.length = kb.length)
    (h0 : kb'[0]? = kb[0]?) (h1 : kb'[1]? = kb[1]?) (h2 : kb'[2]? = kb[2]?)
    (h14 : kb'[14]? = kb[14]?) (h15 : kb'[15]? = kb[15]?)
    (hmet : ∀ k, 1888 ≤ k → k < 2656 → kb'[k]? = kb[k]?) :
    PropKeep kbuf kb' := by
  have hb := hk.1.base_ge
  have hok := k6BufOk_of_frame hk.1 hlen fun idx _ hor => by
    rcases hor with rfl | rfl | rfl | ⟨ha, hb⟩
    · exact h1
    · exact h14
    · exact h15
    · exact hmet idx ha hb
  refine ⟨hok, hlen.trans hk.2.1, h0.trans hk.2.2.1, h1.trans hk.2.2.2.1,
    h2.trans hk.2.2.2.2.1, h14.trans hk.2.2.2.2.2.1, h15.trans hk.2.2.2.2.2.2.1,
    fun cid hcid => ?_⟩
  have hcl := hk.2.2.2.2.2.2.2 cid hcid
  exact ⟨(hmet _ (by omega) (by omega)).trans hcl.1,
    (hmet _ (by omega) (by omega)).trans hcl.2.1,
    (hmet _ (by omega) (by omega)).trans hcl.2.2⟩

private theorem propKeep_set {kbuf kb : List (BitVec 32)} (hk : PropKeep kbuf kb)
    (idx : Nat) (val : BitVec 32)
    (h0 : idx ≠ 0) (h1 : idx ≠ 1) (h2 : idx ≠ 2) (h14 : idx ≠ 14) (h15 : idx ≠ 15)
    (hmet : idx < 1888 ∨ 2656 ≤ idx) :
    PropKeep kbuf (kb.set idx val) :=
  propKeep_of_frame hk List.length_set
    (List.getElem?_set_ne h0) (List.getElem?_set_ne h1)
    (List.getElem?_set_ne h2) (List.getElem?_set_ne h14)
    (List.getElem?_set_ne h15) fun _ hk1 hk2 => List.getElem?_set_ne (by omega)

private theorem propKeep_set_4 {kbuf kb : List (BitVec 32)} (hk : PropKeep kbuf kb)
    (val : BitVec 32) : PropKeep kbuf (kb.set 4 val) :=
  propKeep_set hk 4 val (by decide) (by decide) (by decide) (by decide) (by decide)
    (Or.inl (by decide))

private theorem propKeep_set_12 {kbuf kb : List (BitVec 32)} (hk : PropKeep kbuf kb)
    (val : BitVec 32) : PropKeep kbuf (kb.set 12 val) :=
  propKeep_set hk 12 val (by decide) (by decide) (by decide) (by decide) (by decide)
    (Or.inl (by decide))

private theorem propKeep_set_mid {kbuf kb : List (BitVec 32)} (hk : PropKeep kbuf kb)
    (idx : Nat) (val : BitVec 32) (hlo : 16 ≤ idx) (hhi : idx < 1888) :
    PropKeep kbuf (kb.set idx val) :=
  propKeep_set hk idx val (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inl hhi)

private theorem propKeep_set_hi {kbuf kb : List (BitVec 32)} (hk : PropKeep kbuf kb)
    (idx : Nat) (val : BitVec 32) (hlo : 2656 ≤ idx) :
    PropKeep kbuf (kb.set idx val) :=
  propKeep_set hk idx val (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inr hlo)

private theorem propKeep_of_assign {kbuf kb kb' : List (BitVec 32)} (hk : PropKeep kbuf kb)
    (hlen : kb'.length = kb.length)
    (hkeep : ∀ idx < kb.length, idx ≠ 5 → idx ≠ 6 → (idx < 32 ∨ 480 ≤ idx) →
      (idx < 608 ∨ 736 ≤ idx) → kb'[idx]? = kb[idx]?) :
    PropKeep kbuf kb' := by
  have hb := hk.1.base_ge
  have hk_at : ∀ idx, idx < 32 → idx ≠ 5 → idx ≠ 6 → kb'[idx]? = kb[idx]? :=
    fun idx hi h5 h6 => hkeep idx (by omega) h5 h6 (Or.inl hi) (Or.inl (by omega))
  exact propKeep_of_frame hk hlen
    (hk_at 0 (by decide) (by decide) (by decide))
    (hk_at 1 (by decide) (by decide) (by decide))
    (hk_at 2 (by decide) (by decide) (by decide))
    (hk_at 14 (by decide) (by decide) (by decide))
    (hk_at 15 (by decide) (by decide) (by decide))
    fun k hk1 hk2 => hkeep k (by omega) (by omega) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega))

/-! ## 2. `full_k6_prop_m7_wp` -/

/-- Certifies `fullK6PropM7Spec` for `full_k6_prop_m7`. -/
theorem full_k6_prop_m7_wp (Γ : Env)
    (hAssign : ∀ a m Q X, fullK6AssignM7Spec a m Q X →
      Γ "full_k6_assign_m7" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullK6PropM7Spec a m Q X →
      Func.wp Γ full_k6_prop_m7_body a m Q X := by
  rintro ⟨pk, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨kbuf, R, hok0, hm0, hQ⟩ := fullK6PropM7Spec_elim hSpec
  have hlen := hok0.base_ge
  have hlt28 := hok0.length_lt
  let nc := kbuf[1]'(by omega)
  let nv := kbuf[0]'(by omega)
  let acap := kbuf[15]'(by omega)
  unfold Func.wp full_k6_prop_m7_body
  c0_hsplit
  · c0_hsteps!
    exact hQ 0xFFFFFFFF#32 kbuf m0 hok0 rfl rfl rfl rfl rfl (fun _ _ => ⟨rfl, rfl, rfl⟩) hm0
  · have hnc_le : nc.toNat ≤ 256 := Nat.le_of_not_lt (show ¬256 < nc.toNat from hc)
    clear hc
    c0_hsplit
    · c0_hsteps!
      exact hQ 0xFFFFFFFF#32 kbuf m0 hok0 rfl rfl rfl rfl rfl (fun _ _ => ⟨rfl, rfl, rfl⟩) hm0
    · have hnv_le : nv.toNat ≤ 64 := Nat.le_of_not_lt (show ¬64 < nv.toNat from hc)
      clear hc
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i64])
        (fun rem (ticks, ()) mi => ∃ kbi, PropKeep kbuf kbi ∧
          rem = 64 - (kbi[4]?.getD 0#32).toNat ∧
          (array (t := i32) pk kbi ⋆ R) mi)
        ?_ ?_
      · rintro Lo remo ⟨ticks, ⟨⟩⟩ mi hLo ⟨kbi, hki, rfl, hmi⟩
        have hki_l := hki.2.1
        rw [k6b_get_eq (by omega : 4 < kbi.length)] at hLo
        have hkbi0 : kbi[0]'(by omega) = nv := k6b_elem_of_opt hki.2.2.1 (by omega) (by omega)
        have hkbi1 : kbi[1]'(by omega) = nc := k6b_elem_of_opt hki.2.2.2.1 (by omega) (by omega)
        have hkbi15 : kbi[15]'(by omega) = acap :=
          k6b_elem_of_opt hki.2.2.2.2.2.2.1 (by omega) (by omega)
        c0_hsteps_nogrp
        refine wp_join0 (fun me => ∃ kbe, PropKeep kbuf kbe ∧
            (array (t := i32) pk kbe ⋆ R) me) ?_ ?_
        · intro _ me ⟨kbe, hke, hme⟩
          have hke_l := hke.2.1
          c0_hsteps!
          have hke1 := propKeep_set_12 hke (kbe[12]'(by omega) + ticks.truncate 32)
          exact hQ 0xFFFFFFFF#32 _ m hke1.1 hke1.2.1 hke1.2.2.1 hke1.2.2.2.1
            hke1.2.2.2.2.1 hke1.2.2.2.2.2.2.1 hke1.2.2.2.2.2.2.2 hm
        · intro Jex hJex
          c0_hsplit
          · c0_hsplit
            · have hk4_lt : (kbi[4]'(by omega)).toNat < 64 := hc
              clear hc
              have hpr_bd : 352 + (kbi[4]'(by omega)).toNat < kbi.length := by omega
              let lit := kbi[352 + (kbi[4]'(by omega)).toNat]'hpr_bd
              have h4bd : (BitVec.ofNat (OfNat.ofNat 64)
                  (OfNat.ofNat 4)).toNat < kbi.length := by
                rw [show (BitVec.ofNat (OfNat.ofNat 64)
                  (OfNat.ofNat 4) : BitVec 64).toNat = 4 from rfl]
                omega
              have h4eq : kbi[(BitVec.ofNat (OfNat.ofNat 64)
                  (OfNat.ofNat 4)).toNat]'h4bd = kbi[4]'(by omega) :=
                k6b_get_congr rfl h4bd (by omega)
              have hlit_ar_bd : (BitVec.setWidth 64
                  (352#32 + kbi[(BitVec.ofNat (OfNat.ofNat 64)
                    (OfNat.ofNat 4)).toNat]'h4bd)).toNat < kbi.length := by
                rw [h4eq]; have := hk4_lt; c0_bound
              have hlit_c0 : kbi[(BitVec.setWidth 64
                  (352#32 + kbi[(BitVec.ofNat (OfNat.ofNat 64)
                    (OfNat.ofNat 4)).toNat]'h4bd)).toNat]'hlit_ar_bd = lit :=
                k6b_get_congr (by rw [h4eq]; have := hk4_lt; c0_bound) _ hpr_bd
              have hk4_s : (kbi[4]'(by omega) + 1#32).toNat =
                  (kbi[4]'(by omega)).toNat + 1 := k6b_add1_toNat hk4_lt (by decide)
              c0_hsteps_nogrp
              c0_hsplit
              · c0_hsteps!
                have hki1 := propKeep_set_4 hki (kbi[4]'(by omega) + 1#32)
                let kbi1 := kbi.set 4 (kbi[4]'(by omega) + 1#32)
                have hkbi1_l : kbi1.length = kbuf.length := by
                  dsimp only [kbi1]; rw [List.length_set, hki_l]
                have hkbi1_4 : 4 < kbi1.length := by rw [hkbi1_l]; omega
                have h4_kbi : 4 < kbi.length := by omega
                have hrem1 : 64 - (kbi1[4]'hkbi1_4).toNat <
                    64 - (kbi[4]'h4_kbi).toNat := by
                  have he4 : kbi1[4]'hkbi1_4 = kbi[4]'h4_kbi + 1#32 := by
                    dsimp only [kbi1]
                    exact List.getElem_set_self (by rw [List.length_set]; exact h4_kbi)
                  rw [he4, hk4_s]; omega
                exact hLo (64 - (kbi1[4]'hkbi1_4).toNat) (ticks, ()) m hrem1
                  ⟨kbi1, hki1, by rw [k6b_get_eq hkbi1_4], hm⟩
              · have hk4_4 :
                    (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4)).toNat = 4 := rfl
                let kbi1 := kbi.set (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4)).toNat
                  (kbi[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4)).toNat]'h4bd + 1#32)
                have hki1 : PropKeep kbuf kbi1 := by
                  dsimp only [kbi1]
                  rw [k6b_set_congr hk4_4 (congrArg (· + 1#32) h4eq)]
                  exact propKeep_set_4 hki _
                have hkbi1_l : kbi1.length = kbuf.length := by
                  dsimp only [kbi1]; rw [List.length_set, hki_l]
                have hkbi1_4 : 4 < kbi1.length := by rw [hkbi1_l]; omega
                have h4_kbi : 4 < kbi.length := by omega
                have hrem1 : 64 - (kbi1[4]'hkbi1_4).toNat <
                    64 - (kbi[4]'h4_kbi).toNat := by
                  have he4 : kbi1[4]'hkbi1_4 = kbi[4]'h4_kbi + 1#32 := by
                    dsimp only [kbi1]
                    calc (kbi.set (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4)).toNat
                            (kbi[(BitVec.ofNat (OfNat.ofNat 64)
                              (OfNat.ofNat 4)).toNat]'h4bd + 1#32))[4]'(by
                            rw [List.length_set]; exact h4_kbi)
                      _ = (kbi.set 4 (kbi[4]'h4_kbi + 1#32))[4]'(by
                            rw [List.length_set]; exact h4_kbi) := by
                        congr 1
                      _ = kbi[4]'h4_kbi + 1#32 :=
                        List.getElem_set_self (by rw [List.length_set]; exact h4_kbi)
                  rw [he4, hk4_s]; omega
                have hlit_lt : lit.toNat < 2 * nv.toNat := by
                  have htw : (2 * nv.toNat) % 4294967296 = 2 * nv.toNat := by omega
                  rw [← hlit_c0]
                  exact Nat.lt_of_not_le (by simpa [nv, hkbi0, htw] using hc)
                clear hc
                have hnl_eq : (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 := by
                  rw [BitVec.toNat_xor, show (1#32 : BitVec 32).toNat = 1 from rfl]
                have hnl_lt : (lit ^^^ 1#32).toNat < 2 * nv.toNat := by
                  rw [hnl_eq]; have := fullInv_var_xor1 lit.toNat; omega
                have hlit_ar_bd' : (BitVec.setWidth 64 (352 + kbi[(BitVec.ofNat (OfNat.ofNat 64)
                    (OfNat.ofNat 4)).toNat]'h4bd)).toNat < kbi.length := hlit_ar_bd
                have hlit_c0' : kbi[(BitVec.setWidth 64 (352 + kbi[(BitVec.ofNat (OfNat.ofNat 64)
                    (OfNat.ofNat 4)).toNat]'h4bd)).toNat]'hlit_ar_bd' = lit := hlit_c0
                have hw0_c0_bd : (BitVec.setWidth 64 (736 + (kbi[(BitVec.setWidth 64
                    (352 + kbi[(BitVec.ofNat (OfNat.ofNat 64)
                      (OfNat.ofNat 4)).toNat]'h4bd)).toNat]'hlit_ar_bd' ^^^ 1))).toNat <
                    kbi1.length := by
                  rw [hlit_c0', hkbi1_l]; have := hnl_lt; c0_bound
                have hw0_bd : 736 + (lit ^^^ 1#32).toNat < kbi1.length := by
                  rw [hkbi1_l]; omega
                c0_hsteps_nogrp
                refine wp_loop_group (ts := [i64, i64, i32, i32, i32])
                  (fun remw (t_w, vis_w, prev_w, w_w, wsteps_w, ()) mw =>
                    ∃ kbw, PropKeep kbuf kbw ∧ kbw[4]? = kbi1[4]? ∧
                    wsteps_w.toNat ≤ 512 ∧ remw = 512 - wsteps_w.toNat ∧
                    (array (t := i32) pk kbw ⋆ R) mw)
                  ?_ ?_
                · rintro Li remw ⟨t_w, vis_w, prev_w, w_w, wsteps_w, ⟨⟩⟩ mw hLi
                    ⟨kbw, hkw, hkw4, hws_le, rfl, hmw⟩
                  have hkw_l := hkw.2.1
                  have hkbw0 : kbw[0]'(by omega) = nv :=
                    k6b_elem_of_opt hkw.2.2.1 (by omega) (by omega)
                  have hkbw1 : kbw[1]'(by omega) = nc :=
                    k6b_elem_of_opt hkw.2.2.2.1 (by omega) (by omega)
                  have hkbw15 : kbw[15]'(by omega) = acap :=
                    k6b_elem_of_opt hkw.2.2.2.2.2.2.1 (by omega) (by omega)
                  c0_hsteps_nogrp
                  refine wp_join0 (fun mwi => ∃ kbwi, PropKeep kbuf kbwi ∧
                      kbwi[4]? = kbi1[4]? ∧ (array (t := i32) pk kbwi ⋆ R) mwi) ?_ ?_
                  · intro _ mwi ⟨kbwi, hkwi, hkwi4, hmwi⟩
                    have hkwi_l := hkwi.2.1
                    have h4eqw : kbwi[4]'(by omega) = kbi1[4]'hkbi1_4 :=
                      k6b_elem_of_opt hkwi4 (by omega) hkbi1_4
                    c0_hsteps!
                    exact hLo (64 - (kbwi[4]'(by omega)).toNat)
                      (t_w + (vis_w >>> (7 : Nat)) + 1#64, ()) mwi
                      (by rw [h4eqw]; exact hrem1)
                      ⟨kbwi, hkwi, by rw [k6b_get_eq (by omega)], hmwi⟩
                  · intro Jwex hJwex
                    c0_hsplit
                    · have hw_lt : w_w.toNat < 2 * nc.toNat := by
                        have htw : (2 * nc.toNat) % 2 ^ 32 = 2 * nc.toNat := by omega
                        simpa [nc, hkbw1, htw] using hc
                      clear hc
                      c0_hsplit
                      · have hws_lt : wsteps_w.toNat < 512 := hc
                        clear hc
                        have hws1 : (wsteps_w + 1#32).toNat = wsteps_w.toNat + 1 :=
                          k6b_add1_toNat hws_lt (by decide)
                        have hw_bd : w_w.toNat < 512 := by omega
                        have hnxt_bd : (BitVec.setWidth 64 (864 + w_w)).toNat <
                            kbw.length := by
                          have := hw_bd; c0_bound
                        let nxt := kbw[864 + w_w.toNat]'(by omega)
                        have hnxt_eq :
                            kbw[(BitVec.setWidth 64 (864 + w_w)).toNat]'hnxt_bd = nxt :=
                          k6b_get_congr (by have := hw_bd; c0_bound) _ (by omega)
                        have hwb_bd : (BitVec.setWidth 64 (1376 + w_w)).toNat <
                            kbw.length := by
                          have := hw_bd; c0_bound
                        let wb := kbw[1376 + w_w.toNat]'(by omega)
                        have hwb_eq :
                            kbw[(BitVec.setWidth 64 (1376 + w_w)).toNat]'hwb_bd = wb :=
                          k6b_get_congr (by have := hw_bd; c0_bound) _ (by omega)
                        let bv := wb &&& 2147483647
                        c0_hsplit
                        · c0_hsteps!
                          rw [hnxt_eq]
                          exact hLi (512 - (wsteps_w + 1#32).toNat)
                            (t_w, vis_w + 1#64, w_w, nxt, wsteps_w + 1#32, ()) mw
                            (by omega) ⟨kbw, hkw, hkw4, by omega, rfl, hmw⟩
                        · have hbv_lt : bv.toNat < 2 * nv.toNat := by
                            have htw : (2 * nv.toNat) % 2 ^ 32 = 2 * nv.toNat := by omega
                            have hwb_eq' : kbw[(1376 + w_w.toNat) % 4294967296 %
                                18446744073709551616]'(by omega) = wb :=
                              k6b_get_congr (by omega) _ (by omega)
                            have hbvv_eq : (wb &&& 2147483647).toNat =
                                wb.toNat &&& 2147483647 := by
                              rw [BitVec.toNat_and]; rfl
                            dsimp only [bv]
                            rw [hbvv_eq]
                            exact Nat.lt_of_not_le (by
                              simpa [nv, hkbw0, htw, hwb_eq'] using hc)
                          clear hc
                          have hbvv_c0_bd : (BitVec.setWidth 64 (608 +
                              (kbw[(BitVec.setWidth 64 (1376 + w_w)).toNat]'hwb_bd &&&
                                2147483647))).toNat < kbw.length := by
                            rw [hwb_eq]
                            change (BitVec.setWidth 64 (608 + bv)).toNat < kbw.length
                            have := hbv_lt; c0_bound
                          let bvv := kbw[608 + bv.toNat]'(by omega)
                          c0_hsplit
                          · c0_hsteps!
                            rw [hnxt_eq]
                            exact hLi (512 - (wsteps_w + 1#32).toNat)
                              (t_w, vis_w + 1#64, w_w, nxt, wsteps_w + 1#32, ()) mw
                              (by omega) ⟨kbw, hkw, hkw4, by omega, rfl, hmw⟩
                          · clear hc
                            let cid := w_w >>> (1 : Nat)
                            have hcid_eq : cid.toNat = w_w.toNat / 2 := by
                              dsimp only [cid]
                              rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                            have hcid_lt : cid.toNat < nc.toNat := by omega
                            have hoff_c0_bd : (BitVec.setWidth 64
                                (1888 + (w_w >>> (1 : Nat)))).toNat < kbw.length := by
                              have : (w_w >>> (1 : Nat)).toNat < nc.toNat :=
                                hcid_eq ▸ hcid_lt
                              c0_bound
                            have hcm_c0_bd : (BitVec.setWidth 64
                                (2144 + (w_w >>> (1 : Nat)))).toNat < kbw.length := by
                              have : (w_w >>> (1 : Nat)).toNat < nc.toNat :=
                                hcid_eq ▸ hcid_lt
                              c0_bound
                            c0_hsplit
                            · clear hc
                              c0_hsplit
                              · c0_hsteps!
                                have hkw_fin := propKeep_set_12 hkw
                                  (kbw[12]'(by omega) +
                                    (t_w + ((vis_w + 1#64) >>> (7 : Nat)) + 1#64).truncate 32)
                                exact hQ cid _ m hkw_fin.1 hkw_fin.2.1 hkw_fin.2.2.1
                                  hkw_fin.2.2.2.1 hkw_fin.2.2.2.2.1 hkw_fin.2.2.2.2.2.2.1
                                  hkw_fin.2.2.2.2.2.2.2 hm
                              · c0_hsteps_nogrp
                                refine wp_join0 (fun ma => ∃ kba, PropKeep kbuf kba ∧
                                    kba[4]? = kbi1[4]? ∧ (array (t := i32) pk kba ⋆ R) ma) ?_ ?_
                                · intro _ ma ⟨kba, hka, hka4, hma⟩
                                  c0_hsteps!
                                  rw [hnxt_eq]
                                  exact hLi (512 - (wsteps_w + 1#32).toNat)
                                    (t_w, vis_w + 1#64, w_w, nxt, wsteps_w + 1#32, ()) ma
                                    (by omega) ⟨kba, hka, hka4, by omega, rfl, hma⟩
                                · intro Ja hJa
                                  c0_hsplit
                                  · c0_hsteps_nogrp
                                    m7_call hAssign
                                    try rw [hwb_eq]
                                    refine fullK6AssignM7Spec_intro (by omega) hmw ?_
                                    intro kba ma hlena hkeepa hma
                                    have hka4 : kba[4]? = kbi1[4]? := by
                                      have := hkeepa 4 (by omega) (by decide) (by decide)
                                        (Or.inl (by decide)) (Or.inl (by decide))
                                      exact this.trans hkw4
                                    exact hJa ma ⟨kba, propKeep_of_assign hkw hlena hkeepa,
                                      hka4, hma⟩
                                  · c0_hsteps!
                                    exact hJa mw ⟨kbw, hkw, hkw4, hmw⟩
                            · clear hc
                              let slot := w_w &&& 1
                              have hslot_lt : slot.toNat < 2 := k6b_slot_lt
                              have hslot1_lt : (slot ^^^ 1).toNat < 2 := k6b_slot_xor1_lt
                              let off := kbw[1888 + cid.toNat]'(by omega)
                              have hoff_eq : kbw[(BitVec.setWidth 64
                                  (1888 + (w_w >>> (1 : Nat)))).toNat]'hoff_c0_bd =
                                  off := by
                                refine k6b_get_congr ?_ _ (by omega)
                                change (BitVec.setWidth 64 (1888 + cid)).toNat = 1888 + cid.toNat
                                have := hcid_lt; c0_bound
                              let cm := kbw[2144 + cid.toNat]'(by omega)
                              have hcm_eq : kbw[(BitVec.setWidth 64
                                  (2144 + (w_w >>> (1 : Nat)))).toNat]'hcm_c0_bd =
                                  cm := by
                                refine k6b_get_congr ?_ _ (by omega)
                                change (BitVec.setWidth 64 (2144 + cid)).toNat = 2144 + cid.toNat
                                have := hcid_lt; c0_bound
                              let sz := cm &&& 65535
                              have hcl := hkw.1.clause_ok
                                (by rw [k6b_get_eq (by omega), hkbw1]; exact hcid_lt)
                              rw [k6b_get_eq (by omega : 1888 + cid.toNat < kbw.length),
                                k6b_get_eq (by omega : 2144 + cid.toNat < kbw.length),
                                k6b_get_eq (by omega : 15 < kbw.length), hkbw15] at hcl
                              have hos_le : off.toNat + sz.toNat ≤ acap.toNat := hcl.1
                              have hlt28w := hkw.1.length_lt
                              have hgew := hkw.1.length_ge
                              rw [k6b_get_eq (by omega : 15 < kbw.length), hkbw15] at hgew
                              have hos_nw : off.toNat + sz.toNat < 2 ^ 32 :=
                                k6b_off_sz_nowarp hos_le hgew hlt28w
                              c0_hsplit
                              · c0_hsteps!
                                rw [hnxt_eq]
                                exact hLi (512 - (wsteps_w + 1#32).toNat)
                                  (t_w, vis_w + 1#64, w_w, nxt, wsteps_w + 1#32, ()) mw
                                  (by omega) ⟨kbw, hkw, hkw4, by omega, rfl, hmw⟩
                              · have hcm_eq' : kbw[(BitVec.toNat 2144 + BitVec.toNat w_w / 2) %
                                    2 ^ 32 % 2 ^ 64]'(by
                                    rw [show (BitVec.toNat (2144 : BitVec 32)) = 2144 from rfl,
                                      ← hcid_eq]
                                    have := hcid_lt; omega) = cm :=
                                  k6b_get_congr (by
                                    rw [show (BitVec.toNat (2144 : BitVec 32)) = 2144 from rfl,
                                      ← hcid_eq]
                                    have := hcid_lt; omega) _ (by omega)
                                have hsz_ge : 2 ≤ sz.toNat := by
                                  rw [hcm_eq'] at hc
                                  change ¬(cm &&& 65535).toNat < (2 : BitVec 32).toNat at hc
                                  rw [show (2 : BitVec 32).toNat = 2 from rfl] at hc
                                  exact Nat.le_of_not_lt hc
                                clear hc
                                c0_hsplit
                                · c0_hsteps!
                                  rw [hnxt_eq]
                                  exact hLi (512 - (wsteps_w + 1#32).toNat)
                                    (t_w, vis_w + 1#64, w_w, nxt, wsteps_w + 1#32, ()) mw
                                    (by omega) ⟨kbw, hkw, hkw4, by omega, rfl, hmw⟩
                                · clear hc
                                  have hot_bd : 2912 + off.toNat + (slot ^^^ 1).toNat <
                                      kbw.length := by omega
                                  let other := kbw[2912 + off.toNat + (slot ^^^ 1).toNat]'hot_bd
                                  have hot_c0_bd : (BitVec.setWidth 64 (2912 +
                                      kbw[(BitVec.setWidth 64
                                        (1888 + (w_w >>> (1 : Nat)))).toNat]'hoff_c0_bd +
                                      ((w_w &&& 1) ^^^ 1))).toNat < kbw.length := by
                                    rw [hoff_eq]
                                    change (BitVec.setWidth 64 (2912 + off +
                                      (slot ^^^ 1))).toNat < kbw.length
                                    have := hsz_ge; have := hslot1_lt; c0_bound
                                  have hoeq : kbw[(BitVec.setWidth 64 (2912 +
                                      kbw[(BitVec.setWidth 64
                                        (1888 + (w_w >>> (1 : Nat)))).toNat]'hoff_c0_bd +
                                      ((w_w &&& 1) ^^^ 1))).toNat]'hot_c0_bd = other := by
                                    refine k6b_get_congr ?_ _ hot_bd
                                    rw [hoff_eq]
                                    change (BitVec.setWidth 64 (2912 + off +
                                      (slot ^^^ 1))).toNat = _
                                    have := hsz_ge; have := hslot1_lt; c0_bound
                                  c0_hsplit
                                  · c0_hsteps!
                                    rw [hnxt_eq]
                                    exact hLi (512 - (wsteps_w + 1#32).toNat)
                                      (t_w, vis_w + 1#64, w_w, nxt, wsteps_w + 1#32, ()) mw
                                      (by omega) ⟨kbw, hkw, hkw4, by omega, rfl, hmw⟩
                                  · have hoff_eq' : kbw[(1888 + w_w.toNat / 2) % 4294967296 %
                                        18446744073709551616]'(by
                                        rw [← hcid_eq]; have := hcid_lt; omega) = off :=
                                      k6b_get_congr (by rw [← hcid_eq]; have := hcid_lt; omega) _
                                        (by omega)
                                    have hslot1_eq : (slot ^^^ 1).toNat = w_w.toNat % 2 ^^^ 1 := by
                                      dsimp only [slot]
                                      rw [BitVec.toNat_xor, BitVec.toNat_and,
                                        show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
                                    have hoeq'_bd : (2912 + (kbw[(1888 + w_w.toNat / 2) %
                                        4294967296 % 18446744073709551616]'(by
                                          rw [← hcid_eq]; have := hcid_lt; omega)).toNat +
                                        (w_w.toNat % 2 ^^^ 1)) % 4294967296 %
                                        18446744073709551616 < kbw.length := by
                                      rw [hoff_eq', ← hslot1_eq]
                                      have := hsz_ge; have := hslot1_lt; omega
                                    have hoeq' : kbw[(2912 + (kbw[(1888 + w_w.toNat / 2) %
                                        4294967296 % 18446744073709551616]'(by
                                          rw [← hcid_eq]; have := hcid_lt; omega)).toNat +
                                        (w_w.toNat % 2 ^^^ 1)) % 4294967296 %
                                        18446744073709551616]'hoeq'_bd = other := by
                                      refine k6b_get_congr ?_ _ hot_bd
                                      rw [hoff_eq', ← hslot1_eq]
                                      have := hsz_ge; have := hslot1_lt; omega
                                    have hoth_lt : other.toNat < 2 * nv.toNat := by
                                      have htw : (2 * nv.toNat) % 4294967296 = 2 * nv.toNat := by
                                        omega
                                      simpa [nv, hkbw0, hoeq', htw] using hc
                                    clear hc
                                    have hov_c0_bd : (BitVec.setWidth 64 (608 +
                                        kbw[(BitVec.setWidth 64 (2912 +
                                          kbw[(BitVec.setWidth 64 (1888 +
                                            (w_w >>> (1 : Nat)))).toNat]'hoff_c0_bd +
                                          ((w_w &&& 1) ^^^ 1))).toNat]'hot_c0_bd)).toNat <
                                        kbw.length := by
                                      rw [hoeq]; have := hoth_lt; c0_bound
                                    c0_hsplit
                                    · c0_hsteps!
                                      have hwb_bd_eq : (BitVec.setWidth 64 (1376 + w_w)).toNat =
                                          1376 + w_w.toNat := by
                                        have := hw_bd; c0_bound
                                      rw [hwb_bd_eq, hoeq] at hm
                                      have hkw_wb := propKeep_set_mid hkw (1376 + w_w.toNat) other
                                        (by omega) (by omega)
                                      have h4wb : (kbw.set (1376 + w_w.toNat) other)[4]? =
                                          kbi1[4]? := by
                                        rw [List.getElem?_set_ne (by omega)]; exact hkw4
                                      rw [hnxt_eq]
                                      exact hLi (512 - (wsteps_w + 1#32).toNat)
                                        (t_w, vis_w + 1#64, w_w, nxt, wsteps_w + 1#32, ()) m
                                        (by omega) ⟨_, hkw_wb, h4wb, by omega, rfl, hm⟩
                                    · clear hc
                                      c0_hsteps_nogrp
                                      refine wp_loop_break_group
                                        (brkTs := [i32, i32, i32]) (lpTs := [i32])
                                        (fun (_, ri, repl, ()) mr => mw = mr ∧
                                          (ri = 0xFFFFFFFF#32 ∨
                                            (ri.toNat < sz.toNat ∧ repl.toNat < 2 * nv.toNat)))
                                        (fun remr (r, ()) mr => mw = mr ∧
                                          2 ≤ r.toNat ∧ r.toNat ≤ sz.toNat ∧
                                          remr = sz.toNat - r.toNat)
                                        ?_ ?_ ?_
                                      · rintro _ ⟨_, ri, repl, ⟨⟩⟩ mr ⟨hmr, hri⟩
                                        subst mr
                                        c0_hsplit
                                        · rcases hri with hff | ⟨hri_lt, hrep_lt⟩
                                          · exact absurd hff hc
                                          clear hc
                                          have h1376_ne : 1376 + w_w.toNat ≠ 2912 + off.toNat +
                                              slot.toNat := by omega
                                          have h_nlt : (kbi1.length) = kbw.length := by omega
                                          have hst1_bd : (BitVec.setWidth 64 (2912 +
                                              kbw[(BitVec.setWidth 64 (1888 +
                                                w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                              (w_w &&& 1))).toNat < kbw.length := by
                                            rw [hoff_eq]
                                            change (BitVec.setWidth 64
                                              (2912 + off + slot)).toNat < kbw.length
                                            have := hsz_ge; have := hslot_lt; c0_bound
                                          have hst2_bd : (BitVec.setWidth 64 (2912 +
                                              kbw[(BitVec.setWidth 64 (1888 +
                                                w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                              ri)).toNat <
                                              (kbw.set (BitVec.setWidth 64 (2912 +
                                                kbw[(BitVec.setWidth 64 (1888 +
                                                  w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                                (w_w &&& 1))).toNat repl).length := by
                                            rw [List.length_set, hoff_eq]
                                            have := hri_lt; c0_bound
                                          c0_hsteps_nogrp
                                          refine wp_join0 (fun mpr => ∃ kbp, PropKeep kbuf kbp ∧
                                              kbp[4]? = kbi1[4]? ∧ kbp.length = kbw.length ∧
                                              (array (t := i32) pk kbp ⋆ R) mpr) ?_ ?_
                                          · intro _ mpr ⟨kbp, hkp, hkp4, hkp_l, hmpr⟩
                                            clear hm m
                                            have hkp_1376 : (BitVec.setWidth 64
                                                (1376 + w_w)).toNat < kbp.length := by
                                              rw [hkp_l]; exact hwb_bd
                                            have h1376_eq : (BitVec.setWidth 64
                                                (1376 + w_w)).toNat =
                                                1376 + w_w.toNat := by
                                              have := hw_bd; c0_bound
                                            c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
                                            rw [h1376_eq, hoeq] at hm
                                            have hkp1_736 : (BitVec.setWidth 64
                                                (736 + repl)).toNat <
                                                (kbp.set (1376 + w_w.toNat) other).length := by
                                              rw [List.length_set, hkp_l]
                                              have := hrep_lt; c0_bound
                                            have hkp1_864 : (BitVec.setWidth 64
                                                (864 + w_w)).toNat <
                                                (kbp.set (1376 + w_w.toNat) other).length := by
                                              rw [List.length_set, hkp_l]
                                              have := hw_bd; c0_bound
                                            c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
                                            c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
                                            have h864_lt32 : 864 + w_w.toNat < 2 ^ 32 :=
                                              Nat.lt_trans (Nat.add_lt_add_left hw_bd 864)
                                                (by decide)
                                            have h864_eq : (BitVec.setWidth 64
                                                (864 + w_w)).toNat = 864 + w_w.toNat := by
                                              rw [BitVec.toNat_setWidth, BitVec.toNat_add]
                                              change (864 + w_w.toNat) % 2 ^ 32 % 2 ^ 64 = _
                                              rw [Nat.mod_eq_of_lt h864_lt32, Nat.mod_eq_of_lt
                                                (Nat.lt_trans h864_lt32 (by decide))]
                                            have h736_lt32 : 736 + repl.toNat < 2 ^ 32 :=
                                              Nat.lt_trans (Nat.add_lt_add_left
                                                (Nat.lt_of_lt_of_le hrep_lt
                                                  (Nat.mul_le_mul_left 2 hnv_le)) 736)
                                                (by decide)
                                            have h736_eq : (BitVec.setWidth 64
                                                (736 + repl)).toNat = 736 + repl.toNat := by
                                              rw [BitVec.toNat_setWidth, BitVec.toNat_add]
                                              change (736 + repl.toNat) % 2 ^ 32 % 2 ^ 64 = _
                                              rw [Nat.mod_eq_of_lt h736_lt32, Nat.mod_eq_of_lt
                                                (Nat.lt_trans h736_lt32 (by decide))]
                                            rw [h864_eq] at hm
                                            have hkp2_736 : (BitVec.setWidth 64
                                                (736 + repl)).toNat <
                                                ((kbp.set (1376 + w_w.toNat) other).set
                                                  (864 + w_w.toNat)
                                                  ((kbp.set (1376 + w_w.toNat) other)[
                                                    (BitVec.setWidth 64
                                                      (736 + repl)).toNat]'hkp1_736)).length := by
                                              rw [List.length_set]; exact hkp1_736
                                            c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
                                            have h736_set (xs : List (BitVec 32)) :
                                                xs.set (BitVec.setWidth 64 (736 + repl)).toNat
                                                  w_w = xs.set (736 + repl.toNat) w_w := by
                                              rw [h736_eq]
                                            rw [h736_set] at hm
                                            c0_hfast
                                            have hkp1 := propKeep_set_mid hkp
                                              (1376 + w_w.toNat) other (by omega) (by omega)
                                            have hkp2 (v : BitVec 32) := propKeep_set_mid hkp1
                                              (864 + w_w.toNat) v (by omega) (by omega)
                                            have hkp3 (v : BitVec 32) := propKeep_set_mid (hkp2 v)
                                              (736 + repl.toNat) w_w (by omega) (by omega)
                                            have h4fin (v : BitVec 32) :
                                                (((kbp.set (1376 + w_w.toNat) other).set
                                                  (864 + w_w.toNat) v).set
                                                  (736 + repl.toNat) w_w)[4]? = kbi1[4]? := by
                                              rw [List.getElem?_set_ne (by omega),
                                                List.getElem?_set_ne (by omega),
                                                List.getElem?_set_ne (by omega)]
                                              exact hkp4
                                            rw [hnxt_eq]
                                            exact hLi (512 - (wsteps_w + 1#32).toNat)
                                              (t_w + 1#64, vis_w + 1#64, prev_w, nxt,
                                                wsteps_w + 1#32, ())
                                              m (by omega) ⟨_, hkp3 _, h4fin _, by omega, rfl, hm⟩
                                          · intro Jpr hJpr
                                            have hka1 := propKeep_set_hi hkw
                                              (2912 + off.toNat + slot.toNat) repl (by omega)
                                            have hka2 := propKeep_set_hi hka1
                                              (2912 + off.toNat + ri.toNat) (lit ^^^ 1#32)
                                              (by omega)
                                            have hk4a2 : ((kbw.set (2912 + off.toNat + slot.toNat)
                                                repl).set (2912 + off.toNat + ri.toNat)
                                                (lit ^^^ 1#32))[4]? = kbi1[4]? := by
                                              rw [List.getElem?_set_ne (by omega),
                                                List.getElem?_set_ne (by omega)]
                                              exact hkw4
                                            have hos_lt32 :
                                                2912 + (off.toNat + sz.toNat) < 2 ^ 32 :=
                                              Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.le_trans
                                                (Nat.add_le_add_left hos_le 2912) hgew)
                                                hlt28w) (by decide)
                                            have hst1_lt :
                                                2912 + off.toNat + slot.toNat < 2 ^ 32 := by
                                              refine Nat.lt_trans (Nat.add_lt_add_left
                                                (Nat.lt_of_lt_of_le hslot_lt hsz_ge) _) ?_
                                              rw [Nat.add_assoc]; exact hos_lt32
                                            have hst1_eq : (BitVec.setWidth 64 (2912 +
                                                kbw[(BitVec.setWidth 64 (1888 +
                                                  w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                                (w_w &&& 1))).toNat =
                                                2912 + off.toNat + slot.toNat := by
                                              rw [hoff_eq]
                                              change (BitVec.setWidth 64
                                                (2912 + off + slot)).toNat = _
                                              rw [BitVec.toNat_setWidth, BitVec.toNat_add,
                                                BitVec.toNat_add]
                                              change ((2912 + off.toNat) % 2 ^ 32 +
                                                slot.toNat) % 2 ^ 32 % 2 ^ 64 = _
                                              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
                                                  (Nat.le_add_right _ _) hst1_lt),
                                                Nat.mod_eq_of_lt hst1_lt,
                                                Nat.mod_eq_of_lt
                                                  (Nat.lt_trans hst1_lt (by decide))]
                                            have hst2_lt :
                                                2912 + off.toNat + ri.toNat < 2 ^ 32 := by
                                              refine Nat.lt_trans
                                                (Nat.add_lt_add_left hri_lt _) ?_
                                              rw [Nat.add_assoc]; exact hos_lt32
                                            have hst2_eq : (BitVec.setWidth 64 (2912 +
                                                kbw[(BitVec.setWidth 64 (1888 +
                                                  w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                                ri)).toNat = 2912 + off.toNat + ri.toNat := by
                                              rw [hoff_eq]
                                              rw [BitVec.toNat_setWidth, BitVec.toNat_add,
                                                BitVec.toNat_add]
                                              change ((2912 + off.toNat) % 2 ^ 32 +
                                                ri.toNat) % 2 ^ 32 % 2 ^ 64 = _
                                              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
                                                  (Nat.le_add_right _ _) hst2_lt),
                                                Nat.mod_eq_of_lt hst2_lt,
                                                Nat.mod_eq_of_lt
                                                  (Nat.lt_trans hst2_lt (by decide))]
                                            c0_hsplit
                                            · have hst3a_bd : (BitVec.setWidth 64 (736 +
                                                  (kbi[(BitVec.setWidth 64 (352 +
                                                    kbi[(BitVec.ofNat (OfNat.ofNat 64)
                                                      (OfNat.ofNat 4)).toNat]'h4bd)).toNat]'
                                                      hlit_ar_bd' ^^^ 1))).toNat <
                                                  ((kbw.set (BitVec.setWidth 64 (2912 +
                                                    kbw[(BitVec.setWidth 64 (1888 +
                                                      w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                                    (w_w &&& 1))).toNat repl).set
                                                    (BitVec.setWidth 64 (2912 +
                                                      kbw[(BitVec.setWidth 64 (1888 +
                                                        w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                                      ri)).toNat
                                                    (kbi[(BitVec.setWidth 64 (352 +
                                                      kbi[(BitVec.ofNat (OfNat.ofNat 64)
                                                        (OfNat.ofNat 4)).toNat]'h4bd)).toNat]'
                                                        hlit_ar_bd' ^^^ 1)).length := by
                                                rw [List.length_set, List.length_set, ← h_nlt]
                                                exact hw0_c0_bd
                                              c0_hfast
                                              have hst3a_eq : (BitVec.setWidth 64 (736 +
                                                  (kbi[(BitVec.setWidth 64 (352 +
                                                    kbi[(BitVec.ofNat (OfNat.ofNat 64)
                                                      (OfNat.ofNat 4)).toNat]'h4bd)).toNat]'
                                                      hlit_ar_bd' ^^^ 1))).toNat =
                                                  736 + (lit ^^^ 1#32).toNat := by
                                                rw [hlit_c0']
                                                have h736_lt :
                                                    736 + (lit ^^^ 1#32).toNat < 2 ^ 32 :=
                                                  Nat.lt_trans (Nat.add_lt_add_left
                                                    (Nat.lt_of_lt_of_le hnl_lt
                                                      (Nat.mul_le_mul_left 2 hnv_le)) 736)
                                                    (by decide)
                                                rw [BitVec.toNat_setWidth, BitVec.toNat_add]
                                                change (736 + (lit ^^^ 1#32).toNat) %
                                                  2 ^ 32 % 2 ^ 64 = _
                                                rw [Nat.mod_eq_of_lt h736_lt,
                                                  Nat.mod_eq_of_lt
                                                    (Nat.lt_trans h736_lt (by decide))]
                                              rw [hst1_eq, hst2_eq, hst3a_eq, hlit_c0', hnxt_eq]
                                                at hm
                                              have hka3 := propKeep_set_mid hka2
                                                (736 + (lit ^^^ 1#32).toNat) nxt
                                                (by omega) (by omega)
                                              have hk4a3 : (((kbw.set (2912 + off.toNat +
                                                  slot.toNat) repl).set
                                                  (2912 + off.toNat + ri.toNat) (lit ^^^ 1#32)).set
                                                  (736 + (lit ^^^ 1#32).toNat) nxt)[4]? =
                                                  kbi1[4]? := by
                                                rw [List.getElem?_set_ne (by omega)]; exact hk4a2
                                              exact hJpr m ⟨_, hka3, hk4a3,
                                                by simp only [List.length_set], hm⟩
                                            · have hprev_lt : prev_w.toNat < 2 * nc.toNat := by
                                                have htw : (2 * nc.toNat) % 2 ^ 32 = 2 * nc.toNat :=
                                                  by omega
                                                exact Nat.lt_of_not_le
                                                  (by simpa [nc, hkbw1, htw] using hc)
                                              have hpv_lt512 : prev_w.toNat < 512 :=
                                                Nat.lt_of_lt_of_le hprev_lt
                                                  (Nat.mul_le_mul_left 2 hnc_le)
                                              have h864p_lt : 864 + prev_w.toNat < 2 ^ 32 :=
                                                Nat.lt_trans (Nat.add_lt_add_left hpv_lt512 864)
                                                  (by decide)
                                              have hst3b_eq : (BitVec.setWidth 64
                                                  (864 + prev_w)).toNat = 864 + prev_w.toNat := by
                                                rw [BitVec.toNat_setWidth, BitVec.toNat_add]
                                                change (864 + prev_w.toNat) % 2 ^ 32 % 2 ^ 64 = _
                                                rw [Nat.mod_eq_of_lt h864p_lt, Nat.mod_eq_of_lt
                                                  (Nat.lt_trans h864p_lt (by decide))]
                                              have hst3b_bd : (BitVec.setWidth 64
                                                  (864 + prev_w)).toNat <
                                                  ((kbw.set (BitVec.setWidth 64 (2912 +
                                                    kbw[(BitVec.setWidth 64 (1888 +
                                                      w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                                    (w_w &&& 1))).toNat repl).set
                                                    (BitVec.setWidth 64 (2912 +
                                                      kbw[(BitVec.setWidth 64 (1888 +
                                                        w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                                      ri)).toNat
                                                    (kbi[(BitVec.setWidth 64 (352 +
                                                      kbi[(BitVec.ofNat (OfNat.ofNat 64)
                                                        (OfNat.ofNat 4)).toNat]'h4bd)).toNat]'
                                                        hlit_ar_bd' ^^^ 1)).length := by
                                                rw [List.length_set, List.length_set, hst3b_eq,
                                                  hkw_l]
                                                exact Nat.lt_of_lt_of_le
                                                  (Nat.add_lt_add_left hpv_lt512 864)
                                                  (Nat.le_trans (by decide) hlen)
                                              c0_hfast
                                              rw [hst1_eq, hst2_eq, hst3b_eq, hlit_c0', hnxt_eq]
                                                at hm
                                              have hka3 := propKeep_set_mid hka2
                                                (864 + prev_w.toNat) nxt (by omega) (by omega)
                                              have hk4a3 : (((kbw.set (2912 + off.toNat +
                                                  slot.toNat) repl).set
                                                  (2912 + off.toNat + ri.toNat) (lit ^^^ 1#32)).set
                                                  (864 + prev_w.toNat) nxt)[4]? = kbi1[4]? := by
                                                rw [List.getElem?_set_ne (by omega)]; exact hk4a2
                                              exact hJpr m ⟨_, hka3, hk4a3,
                                                by simp only [List.length_set], hm⟩
                                        · clear hc
                                          have h1376_lt32 : 1376 + w_w.toNat < 2 ^ 32 :=
                                            Nat.lt_trans (Nat.add_lt_add_left hw_bd 1376)
                                              (by decide)
                                          have hwb_bd_eq : (BitVec.setWidth 64
                                              (1376 + w_w)).toNat = 1376 + w_w.toNat := by
                                            rw [BitVec.toNat_setWidth, BitVec.toNat_add]
                                            change (1376 + w_w.toNat) % 2 ^ 32 % 2 ^ 64 = _
                                            rw [Nat.mod_eq_of_lt h1376_lt32, Nat.mod_eq_of_lt
                                              (Nat.lt_trans h1376_lt32 (by decide))]
                                          have hov_lt512 : 608 + other.toNat < 2 ^ 32 :=
                                            Nat.lt_trans (Nat.add_lt_add_left
                                              (Nat.lt_of_lt_of_le hoth_lt
                                                (Nat.mul_le_mul_left 2 hnv_le)) 608) (by decide)
                                          have hov_set_bd : (BitVec.setWidth 64 (608 +
                                              kbw[(BitVec.setWidth 64 (2912 +
                                                kbw[(BitVec.setWidth 64 (1888 +
                                                  w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                                ((w_w &&& 1) ^^^ 1))).toNat]'hot_c0_bd)).toNat <
                                              (kbw.set (BitVec.setWidth 64 (1376 + w_w)).toNat
                                                (kbw[(BitVec.setWidth 64 (2912 +
                                                  kbw[(BitVec.setWidth 64 (1888 +
                                                    w_w >>> (1 : Nat))).toNat]'hoff_c0_bd +
                                                  ((w_w &&& 1) ^^^
                                                    1))).toNat]'hot_c0_bd)).length := by
                                            rw [List.length_set, hoeq, BitVec.toNat_setWidth,
                                              BitVec.toNat_add]
                                            change (608 + other.toNat) % 2 ^ 32 % 2 ^ 64 < _
                                            rw [Nat.mod_eq_of_lt hov_lt512, Nat.mod_eq_of_lt
                                              (Nat.lt_trans hov_lt512 (by decide)), hkw_l]
                                            exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left
                                              (Nat.lt_of_lt_of_le hoth_lt
                                                (Nat.mul_le_mul_left 2 hnv_le)) 608)
                                              (Nat.le_trans (by decide) hlen)
                                          have hkw_wb := propKeep_set_mid hkw (1376 + w_w.toNat)
                                            other (by omega) (by omega)
                                          have h4wb : (kbw.set (1376 + w_w.toNat) other)[4]? =
                                              kbi1[4]? := by
                                            rw [List.getElem?_set_ne (by omega)]; exact hkw4
                                          c0_hsplit
                                          · rw [hwb_bd_eq, hoeq] at hm
                                            clear hAssign hLo hLi hJwex hJex
                                            have h12_bd : (BitVec.ofNat (OfNat.ofNat 64)
                                                (OfNat.ofNat 12)).toNat <
                                                (kbw.set (1376 + w_w.toNat) other).length := by
                                              rw [List.length_set, hkw_l]
                                              exact Nat.lt_of_lt_of_le (by decide) hlen
                                            c0_hfast
                                            have hkw_fin := propKeep_set_12 hkw_wb
                                              ((kbw.set (1376 + w_w.toNat) other)[12]'(by
                                                rw [List.length_set, hkw_l]
                                                exact Nat.lt_of_lt_of_le (by decide) hlen) +
                                                (t_w + 1#64 + ((vis_w + 1#64) >>> (7 : Nat)) +
                                                  1#64).truncate 32)
                                            exact hQ cid _ m hkw_fin.1 hkw_fin.2.1 hkw_fin.2.2.1
                                              hkw_fin.2.2.2.1 hkw_fin.2.2.2.2.1
                                              hkw_fin.2.2.2.2.2.2.1 hkw_fin.2.2.2.2.2.2.2 hm
                                          · rw [hwb_bd_eq, hoeq] at hm
                                            c0_hsteps_nogrp
                                            refine wp_join0 (fun ma => ∃ kba, PropKeep kbuf kba ∧
                                                kba[4]? = kbi1[4]? ∧
                                                (array (t := i32) pk kba ⋆ R) ma) ?_ ?_
                                            · intro _ ma ⟨kba, hka, hka4, hma⟩
                                              c0_hfast
                                              rw [hnxt_eq]
                                              exact hLi (512 - (wsteps_w + 1#32).toNat)
                                                (t_w + 1#64, vis_w + 1#64, w_w, nxt,
                                                  wsteps_w + 1#32, ()) ma (by omega)
                                                ⟨kba, hka, hka4, by omega, rfl, hma⟩
                                            · intro Jao hJao
                                              c0_hsplit
                                              · c0_hsteps_nogrp
                                                m7_call hAssign
                                                try rw [hoeq]
                                                refine fullK6AssignM7Spec_intro
                                                  (by rw [List.length_set, hkw_l]; exact hlen) hm ?_
                                                intro kba ma hlena hkeepa hma
                                                have hka4 : kba[4]? = kbi1[4]? := by
                                                  have := hkeepa 4 (by
                                                      rw [List.length_set, hkw_l]
                                                      exact Nat.lt_of_lt_of_le (by decide) hlen)
                                                    (by decide) (by decide)
                                                    (Or.inl (by decide)) (Or.inl (by decide))
                                                  exact this.trans h4wb
                                                exact hJao ma ⟨kba, propKeep_of_assign hkw_wb
                                                  (by rw [hlena, List.length_set]) hkeepa,
                                                  hka4, hma⟩
                                              · c0_hfast
                                                exact hJao m ⟨_, hkw_wb, h4wb, hm⟩
                                      · rintro Br Lr remr ⟨r, ⟨⟩⟩ mr hBr hLr
                                          ⟨hmr, hr2, hr_le, rfl⟩
                                        subst mr
                                        c0_hsplit
                                        · have hr_lt : r.toNat < sz.toNat := by
                                            rw [hcm_eq'] at hc
                                            change r.toNat < (cm &&& 65535).toNat at hc
                                            exact hc
                                          clear hc
                                          have hca_bd : 2912 + off.toNat + r.toNat < kbw.length :=
                                            by omega
                                          let cand := kbw[2912 + off.toNat + r.toNat]'hca_bd
                                          have hos_lt32' : 2912 + (off.toNat + sz.toNat) < 2 ^ 32 :=
                                            Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.le_trans
                                              (Nat.add_le_add_left hos_le 2912) hgew)
                                              hlt28w) (by decide)
                                          have hca_eq : (BitVec.setWidth 64 (2912 +
                                              kbw[(BitVec.setWidth 64
                                                (1888 + (w_w >>> (1 : Nat)))).toNat]'
                                                  hoff_c0_bd +
                                              r)).toNat = 2912 + off.toNat + r.toNat := by
                                            have hca_lt32 :
                                                2912 + off.toNat + r.toNat < 2 ^ 32 := by
                                              refine Nat.lt_trans (Nat.add_lt_add_left hr_lt _) ?_
                                              rw [Nat.add_assoc]; exact hos_lt32'
                                            rw [hoff_eq, BitVec.toNat_setWidth, BitVec.toNat_add,
                                              BitVec.toNat_add]
                                            change ((2912 + off.toNat) % 2 ^ 32 +
                                              r.toNat) % 2 ^ 32 % 2 ^ 64 = _
                                            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
                                                (Nat.le_add_right _ _) hca_lt32),
                                              Nat.mod_eq_of_lt hca_lt32,
                                              Nat.mod_eq_of_lt (Nat.lt_trans hca_lt32 (by decide))]
                                          have hca_c0_bd : (BitVec.setWidth 64 (2912 +
                                              kbw[(BitVec.setWidth 64
                                                (1888 + (w_w >>> (1 : Nat)))).toNat]'
                                                  hoff_c0_bd +
                                              r)).toNat < kbw.length := by
                                            rw [hca_eq]; exact hca_bd
                                          have hceq : kbw[(BitVec.setWidth 64 (2912 +
                                              kbw[(BitVec.setWidth 64
                                                (1888 + (w_w >>> (1 : Nat)))).toNat]'
                                                  hoff_c0_bd +
                                              r)).toNat]'hca_c0_bd = cand :=
                                            k6b_get_congr hca_eq _ hca_bd
                                          have hr1 : (r + 1#32).toNat = r.toNat + 1 :=
                                            k6b_add1_toNat hr_lt (by omega)
                                          c0_hsteps_nogrp
                                          refine wp_join0 (fun mj => mw = mj) ?_ ?_
                                          · intro _ mj rfl
                                            c0_hfast
                                            exact hLr (sz.toNat - (r + 1#32).toNat)
                                              (r + 1#32, ()) mw (by omega)
                                              ⟨rfl, by omega, by omega, rfl⟩
                                          · intro Jr hJr
                                            c0_hsplit
                                            · have hca_lt : cand.toNat < 2 * nv.toNat := by
                                                have hc_idx : (2912 + (kbw[(1888 + w_w.toNat / 2) %
                                                    4294967296 % 18446744073709551616]'(by
                                                      rw [← hcid_eq]; have := hcid_lt
                                                      omega)).toNat + r.toNat) % 4294967296 %
                                                    18446744073709551616 =
                                                    2912 + off.toNat + r.toNat := by
                                                  rw [hoff_eq']
                                                  have hlt32 :
                                                      2912 + off.toNat + r.toNat < 2 ^ 32 := by
                                                    refine Nat.lt_trans
                                                      (Nat.add_lt_add_left hr_lt _) ?_
                                                    rw [Nat.add_assoc]; exact hos_lt32'
                                                  rw [Nat.mod_eq_of_lt hlt32, Nat.mod_eq_of_lt
                                                    (Nat.lt_trans hlt32 (by decide))]
                                                have hc' :
                                                    cand.toNat < (2 * nv.toNat) % 2 ^ 32 := by
                                                  have heq := k6b_get_congr hc_idx
                                                    (by rw [hc_idx]; exact hca_bd) hca_bd
                                                  dsimp only [cand]; rw [← heq]
                                                  simpa [nv, hkbw0] using hc
                                                rw [Nat.mod_eq_of_lt (by omega)] at hc'
                                                exact hc'
                                              have hcav_c0_bd : (BitVec.setWidth 64 (608 +
                                                  kbw[(BitVec.setWidth 64 (2912 +
                                                    kbw[(BitVec.setWidth 64 (1888 +
                                                      (w_w >>> (1 : Nat)))).toNat]'
                                                        hoff_c0_bd +
                                                    r)).toNat]'hca_c0_bd)).toNat < kbw.length := by
                                                have hcav_lt32 : 608 + cand.toNat < 2 ^ 32 :=
                                                  Nat.lt_trans (Nat.add_lt_add_left
                                                    (Nat.lt_of_lt_of_le hca_lt
                                                      (Nat.mul_le_mul_left 2 hnv_le)) 608)
                                                    (by decide)
                                                rw [hceq, BitVec.toNat_setWidth, BitVec.toNat_add]
                                                change (608 + cand.toNat) % 2 ^ 32 % 2 ^ 64 < _
                                                rw [Nat.mod_eq_of_lt hcav_lt32, Nat.mod_eq_of_lt
                                                  (Nat.lt_trans hcav_lt32 (by decide)), hkw_l]
                                                exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left
                                                  (Nat.lt_of_lt_of_le hca_lt
                                                    (Nat.mul_le_mul_left 2 hnv_le)) 608)
                                                  (Nat.le_trans (by decide) hlen)
                                              c0_hsplit
                                              · c0_hfast
                                                rw [hceq]
                                                exact hBr (r, r, cand, ()) mw
                                                  ⟨rfl, Or.inr ⟨hr_lt, hca_lt⟩⟩
                                              · c0_hfast; exact hJr mw rfl
                                            · c0_hfast; exact hJr mw rfl
                                        · c0_hfast
                                          exact hBr (r, 0xFFFFFFFF#32, 0#32, ()) mw
                                            ⟨rfl, Or.inl rfl⟩
                                      · intro Br Lr _ hLr; c0_hfast
                                        exact hLr (sz.toNat - 2) (2#32, ()) mw
                                          ⟨rfl, by decide, hsz_ge, rfl⟩
                      · c0_hfast; exact hJwex mw ⟨kbw, hkw, hkw4, hmw⟩
                    · c0_hfast; exact hJwex mw ⟨kbw, hkw, hkw4, hmw⟩
                · intro Li hLi
                  have hw0_eq' : (kbi.set
                      (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4)).toNat
                      (kbi[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4)).toNat]'h4bd + 1))[
                      (BitVec.setWidth 64 (736 + (kbi[(BitVec.setWidth 64 (352 +
                        kbi[(BitVec.ofNat (OfNat.ofNat 64)
                          (OfNat.ofNat 4)).toNat]'h4bd)).toNat]'hlit_ar_bd' ^^^
                        1))).toNat]'hw0_c0_bd =
                      kbi1[736 + (lit ^^^ 1#32).toNat]'hw0_bd := by
                    refine k6b_get_congr ?_ _ hw0_bd
                    have hnl32 : 736 + (lit ^^^ 1#32).toNat < 2 ^ 32 :=
                      Nat.lt_trans (Nat.add_lt_add_left
                        (Nat.lt_of_lt_of_le hnl_lt (Nat.mul_le_mul_left 2 hnv_le)) 736)
                        (by decide)
                    rw [hlit_c0', BitVec.toNat_setWidth, BitVec.toNat_add]
                    change (736 + (lit ^^^ 1#32).toNat) % 2 ^ 32 % 2 ^ 64 = _
                    rw [Nat.mod_eq_of_lt hnl32, Nat.mod_eq_of_lt (Nat.lt_trans hnl32 (by decide))]
                  c0_hfast
                  rw [hw0_eq']
                  exact hLi 512
                    (ticks, 0#64, 0xFFFFFFFF#32, kbi1[736 + (lit ^^^ 1#32).toNat]'hw0_bd,
                      0#32, ()) m ⟨kbi1, hki1, rfl, Nat.zero_le _, by simp, hm⟩
            · c0_hfast; exact hJex mi ⟨kbi, hki, hmi⟩
          · c0_hfast; exact hJex mi ⟨kbi, hki, hmi⟩
      · intro Lo hLo; c0_hfast
        exact hLo (64 - (kbuf[4]'(by omega)).toNat) (0#64, ()) m0
          ⟨kbuf, propKeep_refl hok0, by rw [k6b_get_eq (by omega)], hm0⟩

/-! ## 3. Helpers for `full_k6_analyze_m7_wp` and `full_k6_solve_m7_wp` -/

private theorem bv64_add2_lt {a b : BitVec 32} (h : a.toNat + b.toNat < 2 ^ 32) :
    (BitVec.setWidth 64 (a + b)).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (Nat.lt_trans h (by decide))]

private theorem propKeep_of_mtf {kbuf kb kb' : List (BitVec 32)} (hk : PropKeep kbuf kb)
    (hlen : kb'.length = kb.length)
    (hkeep : ∀ idx < kb.length, idx ≠ 8 → idx ≠ 9 → idx ≠ 10 → idx ≠ 11 →
      (idx < 160 ∨ 352 ≤ idx) → kb'[idx]? = kb[idx]?) :
    PropKeep kbuf kb' := by
  have hb := hk.1.base_ge
  have hk_at : ∀ idx, idx < 16 → idx ≠ 8 → idx ≠ 9 → idx ≠ 10 → idx ≠ 11 →
      kb'[idx]? = kb[idx]? :=
    fun idx hi h8 h9 h10 h11 => hkeep idx (by omega) h8 h9 h10 h11 (Or.inl (by omega))
  exact propKeep_of_frame hk hlen
    (hk_at 0 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hk_at 1 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hk_at 2 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hk_at 14 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hk_at 15 (by decide) (by decide) (by decide) (by decide) (by decide))
    fun k hk1 hk2 => hkeep k (by omega) (by omega) (by omega) (by omega) (by omega)
      (Or.inr (by omega))

private theorem propKeep_of_ana_cl {kbuf kb kb' : List (BitVec 32)} (hk : PropKeep kbuf kb)
    (hlen : kb'.length = kb.length)
    (hkeep : ∀ idx < kb.length, idx ≠ 16 → idx ≠ 17 → idx ≠ 18 → idx ≠ 20 →
      (idx < 416 ∨ 608 ≤ idx) → (idx < 2784 ∨ 2912 ≤ idx) → kb'[idx]? = kb[idx]?) :
    PropKeep kbuf kb' := by
  have hb := hk.1.base_ge
  have hk_at : ∀ idx, idx < 16 → kb'[idx]? = kb[idx]? := fun idx hi =>
    hkeep idx (by omega) (by omega) (by omega) (by omega) (by omega)
      (Or.inl (by omega)) (Or.inl (by omega))
  exact propKeep_of_frame hk hlen
    (hk_at 0 (by decide)) (hk_at 1 (by decide)) (hk_at 2 (by decide))
    (hk_at 14 (by decide)) (hk_at 15 (by decide))
    fun k hk1 hk2 => hkeep k (by omega) (by omega) (by omega) (by omega) (by omega)
      (Or.inr (by omega)) (Or.inl (by omega))

private theorem propKeep_of_backtrack {kbuf kb kb' : List (BitVec 32)} (hk : PropKeep kbuf kb)
    (hlen : kb'.length = kb.length)
    (hkeep : ∀ idx < kb.length, idx ≠ 3 → idx ≠ 4 → idx ≠ 5 → idx ≠ 6 → idx ≠ 10 →
      (idx < 32 ∨ 160 ≤ idx) → (idx < 608 ∨ 736 ≤ idx) → kb'[idx]? = kb[idx]?) :
    PropKeep kbuf kb' := by
  have hb := hk.1.base_ge
  have hk_at : ∀ idx, idx < 16 → idx ≠ 3 → idx ≠ 4 → idx ≠ 5 → idx ≠ 6 → idx ≠ 10 →
      kb'[idx]? = kb[idx]? :=
    fun idx hi h3 h4 h5 h6 h10 => hkeep idx (by omega) h3 h4 h5 h6 h10
      (Or.inl (by omega)) (Or.inl (by omega))
  exact propKeep_of_frame hk hlen
    (hk_at 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hk_at 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hk_at 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hk_at 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hk_at 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun k hk1 hk2 => hkeep k (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (Or.inr (by omega)) (Or.inr (by omega))

private theorem analyze_append_k6BufOk {kbuf kb : List (BitVec 32)} (hk : PropKeep kbuf kb)
    {nc_old alen lsz n_ant : BitVec 32}
    (hnc_eq : kb[1]?.getD 0#32 = nc_old) (hnc_lt : nc_old.toNat < 256)
    (hl_le : lsz.toNat ≤ 64) (ha_le : n_ant.toNat ≤ 128)
    (hfit : alen.toNat + lsz.toNat + n_ant.toNat ≤ (kb[15]?.getD 0#32).toNat)
    (hle : kb.length ≥ 2912) :
    let kb1 := kb.set 14 (alen + lsz + n_ant)
    let kb2 := kb1.set (1888 + nc_old.toNat) alen
    let kb3 := kb2.set (2144 + nc_old.toNat) (lsz ||| 0x40000000#32)
    let kb4 := kb3.set (2400 + nc_old.toNat) n_ant
    let kb5 := kb4.set 1 (nc_old + 1#32)
    K6BufOk kb5 ∧ kb5.length = kbuf.length ∧
      kb5[0]? = kbuf[0]? ∧ kb5[2]? = kbuf[2]? ∧ kb5[15]? = kbuf[15]? ∧
      (kbuf[1]?.getD 0#32).toNat ≤ (kb5[1]?.getD 0#32).toNat := by
  intro kb1 kb2 kb3 kb4 kb5
  have hok := hk.1
  have hlen := hk.2.1
  have hnc1 : (nc_old + 1#32).toNat = nc_old.toNat + 1 := k6b_add1_toNat hnc_lt (by omega)
  have hal_lt : alen.toNat + lsz.toNat + n_ant.toNat < 2 ^ 32 := by
    have := hok.length_ge; have := hok.length_lt; omega
  have hal_add : (alen + lsz + n_ant).toNat = alen.toNat + lsz.toNat + n_ant.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hk15 : kb5[15]? = kb[15]? := by
    dsimp only [kb5, kb4, kb3, kb2, kb1]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have hk1 : kb5[1]? = some (nc_old + 1#32) := by
    dsimp only [kb5, kb4, kb3, kb2, kb1]
    apply List.getElem?_set_self
    simp [List.length_set]; omega
  have hk14 : kb5[14]? = some (alen + lsz + n_ant) := by
    dsimp only [kb5, kb4, kb3, kb2, kb1]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    apply List.getElem?_set_self; omega
  have hk0 : kb5[0]? = kb[0]? := by
    dsimp only [kb5, kb4, kb3, kb2, kb1]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have hk2 : kb5[2]? = kb[2]? := by
    dsimp only [kb5, kb4, kb3, kb2, kb1]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have hlen5 : kb5.length = kb.length := by simp [kb5, kb4, kb3, kb2, kb1, List.length_set]
  have hok5 : K6BufOk kb5 := by
    refine K6BufOk.mk_of ?_ ?_ ?_ ?_ ?_
    · rw [hlen5, hk15]; exact hok.length_ge
    · rw [hlen5]; exact hok.length_lt
    · rw [hk1, Option.getD_some, hnc1]; omega
    · rw [hk14, hk15, Option.getD_some, hal_add]; exact hfit
    · intro cid hcid
      rw [hk1, Option.getD_some, hnc1] at hcid
      have hne_cid : ∀ a b, a ≠ b → (1888 + a ≠ 1888 + b ∧ 2144 + a ≠ 2144 + b ∧
          2400 + a ≠ 2400 + b) := fun a b hab => ⟨by omega, by omega, by omega⟩
      by_cases hcur : cid = nc_old.toNat
      · subst hcur
        have ho_c : kb5[1888 + nc_old.toNat]? = some alen := by
          dsimp only [kb5, kb4, kb3, kb2, kb1]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega)]
          apply List.getElem?_set_self; simp [List.length_set]; omega
        have hm_c : kb5[2144 + nc_old.toNat]? = some (lsz ||| 0x40000000#32) := by
          dsimp only [kb5, kb4, kb3, kb2, kb1]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
          apply List.getElem?_set_self; simp [List.length_set]; omega
        have ha_c : kb5[2400 + nc_old.toNat]? = some n_ant := by
          dsimp only [kb5, kb4, kb3, kb2, kb1]
          rw [List.getElem?_set_ne (by omega)]
          apply List.getElem?_set_self; simp [List.length_set]; omega
        have hsz_msk : ((lsz ||| 0x40000000#32) &&& 0xFFFF#32) = lsz := by
          have h65 : ∀ k : Fin 65,
              ((BitVec.ofNat 32 k.1 ||| 0x40000000#32) &&& 0xFFFF#32) =
                BitVec.ofNat 32 k.1 := by decide
          have hlsz : BitVec.ofNat 32 lsz.toNat = lsz := BitVec.eq_of_toNat_eq (by simp)
          simpa [hlsz] using h65 ⟨lsz.toNat, by omega⟩
        rw [ho_c, hm_c, ha_c]
        refine ⟨?_, ?_⟩
        · show alen.toNat + ((lsz ||| 0x40000000#32) &&& 0xFFFF#32).toNat ≤
              (kb5[15]?.getD 0#32).toNat
          rw [hsz_msk, hk15]; omega
        · intro _
          show alen.toNat + ((lsz ||| 0x40000000#32) &&& 0xFFFF#32).toNat + n_ant.toNat ≤
              (kb5[15]?.getD 0#32).toNat
          rw [hsz_msk, hk15]; omega
      · have hcid_lt : cid < (kb[1]?.getD 0#32).toNat := by rw [hnc_eq]; omega
        have hcid256 : cid < 256 := by omega
        have ho_c : kb5[1888 + cid]? = kb[1888 + cid]? := by
          dsimp only [kb5, kb4, kb3, kb2, kb1]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega)]
        have hm_c : kb5[2144 + cid]? = kb[2144 + cid]? := by
          dsimp only [kb5, kb4, kb3, kb2, kb1]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega)]
        have ha_c : kb5[2400 + cid]? = kb[2400 + cid]? := by
          dsimp only [kb5, kb4, kb3, kb2, kb1]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega)]
        rw [ho_c, hm_c, ha_c, hk15]
        exact hok.clause_ok hcid_lt
  refine ⟨hok5, hlen5.trans hlen, hk0.trans hk.2.2.1, hk2.trans hk.2.2.2.2.1,
    hk15.trans hk.2.2.2.2.2.2.1, ?_⟩
  rw [← hk.2.2.2.1, hnc_eq, hk1, Option.getD_some, hnc1]; omega

private theorem propKeep_of_set {kbuf kb : List (BitVec 32)} (hk : PropKeep kbuf kb)
    (idx : Nat) (v : BitVec 32) (h0 : idx ≠ 0) (h1 : idx ≠ 1) (h2 : idx ≠ 2)
    (h14 : idx ≠ 14) (h15 : idx ≠ 15) (hmet : idx < 1888 ∨ 2656 ≤ idx) :
    PropKeep kbuf (kb.set idx v) :=
  propKeep_of_frame hk List.length_set
    (List.getElem?_set_ne h0) (List.getElem?_set_ne h1) (List.getElem?_set_ne h2)
    (List.getElem?_set_ne h14) (List.getElem?_set_ne h15)
    fun k hk1 hk2 => List.getElem?_set_ne (by omega)

/-- Weak solve-loop invariant preserving `K6BufOk`, length, `nv`, monotonic `nc`, `2`, `acap`. -/
private def SolveKeep (kbuf kb : List (BitVec 32)) : Prop :=
  K6BufOk kb ∧ kb.length = kbuf.length ∧ kb[0]? = kbuf[0]? ∧
  (kbuf[1]?.getD 0#32).toNat ≤ (kb[1]?.getD 0#32).toNat ∧
  kb[2]? = kbuf[2]? ∧ kb[15]? = kbuf[15]?

private theorem solveKeep_refl {kbuf : List (BitVec 32)} (h : K6BufOk kbuf) :
    SolveKeep kbuf kbuf :=
  ⟨h, rfl, rfl, Nat.le_refl _, rfl, rfl⟩

private theorem solveKeep_of_set {kbuf kb : List (BitVec 32)} (hs : SolveKeep kbuf kb)
    (idx : Nat) (v : BitVec 32) (h1 : idx ≠ 1) (h14 : idx ≠ 14) (h15 : idx ≠ 15)
    (h0 : idx ≠ 0) (h2 : idx ≠ 2) (hmet : idx < 1888 ∨ 2656 ≤ idx) :
    SolveKeep kbuf (kb.set idx v) := by
  have hok : K6BufOk (kb.set idx v) :=
    k6BufOk_of_frame hs.1 List.length_set fun i _ hor => by
      have hne : idx ≠ i := by rcases hor with rfl | rfl | rfl | ⟨hi1, hi2⟩ <;> omega
      exact List.getElem?_set_ne hne
  refine ⟨hok, List.length_set.trans hs.2.1,
    (List.getElem?_set_ne h0).trans hs.2.2.1, ?_,
    (List.getElem?_set_ne h2).trans hs.2.2.2.2.1,
    (List.getElem?_set_ne h15).trans hs.2.2.2.2.2⟩
  rw [List.getElem?_set_ne h1]; exact hs.2.2.2.1

private theorem solveKeep_of_watch {kbuf kb kb' : List (BitVec 32)} (hs : SolveKeep kbuf kb)
    (hlen : kb'.length = kb.length)
    (hkeep : ∀ idx < kb.length, (idx < 736 ∨ 1888 ≤ idx) → kb'[idx]? = kb[idx]?) :
    SolveKeep kbuf kb' := by
  have hb := hs.1.base_ge
  have hok := k6BufOk_of_frame hs.1 hlen fun idx _ hor => by
    rcases hor with rfl | rfl | rfl | ⟨_, _⟩
    · exact hkeep 1 (by omega) (Or.inl (by decide))
    · exact hkeep 14 (by omega) (Or.inl (by decide))
    · exact hkeep 15 (by omega) (Or.inl (by decide))
    · exact hkeep idx (by omega) (Or.inr (by omega))
  refine ⟨hok, hlen.trans hs.2.1,
    (hkeep 0 (by omega) (Or.inl (by decide))).trans hs.2.2.1, ?_,
    (hkeep 2 (by omega) (Or.inl (by decide))).trans hs.2.2.2.2.1,
    (hkeep 15 (by omega) (Or.inl (by decide))).trans hs.2.2.2.2.2⟩
  rw [hkeep 1 (by omega) (Or.inl (by decide))]; exact hs.2.2.2.1

private theorem solveKeep_of_backtrack {kbuf kb kb' : List (BitVec 32)} (hs : SolveKeep kbuf kb)
    (hlen : kb'.length = kb.length)
    (hkeep : ∀ idx < kb.length, idx ≠ 3 → idx ≠ 4 → idx ≠ 5 → idx ≠ 6 → idx ≠ 10 →
      (idx < 32 ∨ 160 ≤ idx) → (idx < 608 ∨ 736 ≤ idx) → kb'[idx]? = kb[idx]?) :
    SolveKeep kbuf kb' := by
  have hb := hs.1.base_ge
  have hok := k6BufOk_of_frame hs.1 hlen fun idx _ hor => by
    rcases hor with rfl | rfl | rfl | ⟨_, _⟩
    · exact hkeep 1 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide)
        (Or.inl (by decide)) (Or.inl (by decide))
    · exact hkeep 14 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide)
        (Or.inl (by decide)) (Or.inl (by decide))
    · exact hkeep 15 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide)
        (Or.inl (by decide)) (Or.inl (by decide))
    · exact hkeep idx (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (Or.inr (by omega)) (Or.inr (by omega))
  have hk0 := hkeep 0 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Or.inl (by decide)) (Or.inl (by decide))
  have hk1 := hkeep 1 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Or.inl (by decide)) (Or.inl (by decide))
  have hk2 := hkeep 2 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Or.inl (by decide)) (Or.inl (by decide))
  have hk15 := hkeep 15 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Or.inl (by decide)) (Or.inl (by decide))
  refine ⟨hok, hlen.trans hs.2.1, hk0.trans hs.2.2.1, ?_, hk2.trans hs.2.2.2.2.1,
    hk15.trans hs.2.2.2.2.2⟩
  rw [hk1]; exact hs.2.2.2.1

private theorem solveKeep_of_assign {kbuf kb kb' : List (BitVec 32)} (hs : SolveKeep kbuf kb)
    (hlen : kb'.length = kb.length)
    (hkeep : ∀ idx < kb.length, idx ≠ 5 → idx ≠ 6 → (idx < 32 ∨ 480 ≤ idx) →
      (idx < 608 ∨ 736 ≤ idx) → kb'[idx]? = kb[idx]?) :
    SolveKeep kbuf kb' := by
  have hb := hs.1.base_ge
  have hok := k6BufOk_of_frame hs.1 hlen fun idx _ hor => by
    rcases hor with rfl | rfl | rfl | ⟨_, _⟩
    · exact hkeep 1 (by omega) (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide))
    · exact hkeep 14 (by omega) (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide))
    · exact hkeep 15 (by omega) (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide))
    · exact hkeep idx (by omega) (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
  have hk0 := hkeep 0 (by omega) (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide))
  have hk1 := hkeep 1 (by omega) (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide))
  have hk2 := hkeep 2 (by omega) (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide))
  have hk15 := hkeep 15 (by omega) (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide))
  refine ⟨hok, hlen.trans hs.2.1, hk0.trans hs.2.2.1, ?_, hk2.trans hs.2.2.2.2.1,
    hk15.trans hs.2.2.2.2.2⟩
  rw [hk1]; exact hs.2.2.2.1

private theorem solveKeep_of_prop {kbuf kb kb' : List (BitVec 32)} (hs : SolveKeep kbuf kb)
    (hok : K6BufOk kb') (hlen : kb'.length = kb.length)
    (h0 : kb'[0]? = kb[0]?) (h1 : kb'[1]? = kb[1]?) (h2 : kb'[2]? = kb[2]?)
    (h15 : kb'[15]? = kb[15]?) : SolveKeep kbuf kb' :=
  ⟨hok, hlen.trans hs.2.1, h0.trans hs.2.2.1, by rw [h1]; exact hs.2.2.2.1,
    h2.trans hs.2.2.2.2.1, h15.trans hs.2.2.2.2.2⟩

private theorem solveKeep_of_analyze {kbuf kb kb' : List (BitVec 32)} (hs : SolveKeep kbuf kb)
    (hok : K6BufOk kb') (hlen : kb'.length = kb.length)
    (h0 : kb'[0]? = kb[0]?) (h2 : kb'[2]? = kb[2]?) (h15 : kb'[15]? = kb[15]?)
    (h1 : (kb[1]?.getD 0#32).toNat ≤ (kb'[1]?.getD 0#32).toNat) : SolveKeep kbuf kb' :=
  ⟨hok, hlen.trans hs.2.1, h0.trans hs.2.2.1, Nat.le_trans hs.2.2.2.1 h1,
    h2.trans hs.2.2.2.2.1, h15.trans hs.2.2.2.2.2⟩

/-! ## 4. `full_k6_analyze_m7_wp` -/

/-- Certifies `fullK6AnalyzeM7Spec` for `full_k6_analyze_m7`. -/
theorem full_k6_analyze_m7_wp (Γ : Env)
    (hWatch : ∀ a m Q X, fullK6WatchM7Spec a m Q X →
      Γ "full_k6_watch_m7" [i64, i32, i32, i32, i32] [] a m Q X)
    (hAssign : ∀ a m Q X, fullK6AssignM7Spec a m Q X →
      Γ "full_k6_assign_m7" [i64, i32, i32] [] a m Q X)
    (hBacktrack : ∀ a m Q X, fullK6BacktrackM7Spec a m Q X →
      Γ "full_k6_backtrack_m7" [i64, i32] [] a m Q X)
    (hMtf : ∀ a m Q X, fullK6MtfM7Spec a m Q X →
      Γ "full_k6_mtf_m7" [i64, i32] [] a m Q X)
    (hAnaCl : ∀ a m Q X, fullK6AnaClM7Spec a m Q X →
      Γ "full_k6_ana_cl_m7" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullK6AnalyzeM7Spec a m Q X →
      Func.wp Γ full_k6_analyze_m7_body a m Q X := by
  rintro ⟨pk, confl_cid, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨kbuf, R, hok0, hm0, hQ⟩ := fullK6AnalyzeM7Spec_elim hSpec
  have hlen := hok0.base_ge
  have hlt28 := hok0.length_lt
  let nv : BitVec 32 := kbuf[0]'(by omega)
  let nc : BitVec 32 := kbuf[1]'(by omega)
  let acap : BitVec 32 := kbuf[15]'(by omega)
  have hnc_le : nc.toNat ≤ 256 := by
    simpa [nc, k6b_get_eq (by omega : 1 < kbuf.length)] using hok0.nc_le
  unfold Func.wp full_k6_analyze_m7_body
  c0_hsteps_nogrp
  · exact hQ false kbuf m0 hok0 rfl rfl rfl rfl (Nat.le_refl _) hm0
  · have hnv_le : nv.toNat ≤ 64 := Nat.le_of_not_lt (show ¬64 < nv.toNat from hc)
    clear hc
    have h17 : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 17)).toNat = 17 := rfl
    have h16 : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 16)).toNat = 16 := rfl
    have h18 : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 18)).toNat = 18 := rfl
    have h20 : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 20)).toNat = 20 := rfl
    rw [h17] at hm
    have hpk0 := propKeep_of_set (propKeep_refl hok0) 17 1#32 (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inl (by decide))
    have hpk1 := propKeep_of_set hpk0 16 0#32 (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inl (by decide))
    have hpk2 := propKeep_of_set hpk1 18 0#32 (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inl (by decide))
    have hpk3 := propKeep_of_set hpk2 20 0#32 (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inl (by decide))
    have hl0 : 2912 ≤ (kbuf.set 17 1#32).length := by rw [hpk0.2.1]; exact hlen
    c0_hsteps_nogrp
    rw [h16] at hm
    have hl1 : 2912 ≤ ((kbuf.set 17 1#32).set 16 0#32).length := by rw [hpk1.2.1]; exact hlen
    c0_hsteps_nogrp
    rw [h18] at hm
    have hl2 : 2912 ≤ (((kbuf.set 17 1#32).set 16 0#32).set 18 0#32).length := by
      rw [hpk2.2.1]; exact hlen
    c0_hsteps_nogrp
    rw [h20] at hm
    have hok3 : K6BufOk _ := hpk3.1
    m7_call hAnaCl
    dsimp only [vals, Arg.val]
    refine fullK6AnaClM7Spec_intro hok3 hm ?_
    intro kb4 m4 hlen4 hkeep4 hm4
    have hpk4 := propKeep_of_ana_cl hpk3 hlen4 hkeep4
    have hl4 : 2912 ≤ kb4.length := by rw [hpk4.2.1]; exact hlen
    c0_hsteps_nogrp
    let clvl := kb4[3]'(by omega)
    refine wp_join_state1 (t := i32)
      (fun st : BitVec 32 × List (BitVec 32) => (st.1 : Val i32))
      (fun (idx, kb) mi => PropKeep kbuf kb ∧ idx.toNat ≤ 64 ∧ (array (t := i32) pk kb ⋆ R) mi)
      ?_ ?_
    · rintro _ ⟨idx0, kbi0⟩ mi0 ⟨hki0, hidx0_le, hmi0⟩
      refine wp_while_break_state
        (brkTs := [i32, i32]) (lpTs := [i32])
        (fun st : BitVec 32 × BitVec 32 × List (BitVec 32) => (st.1, st.2.1, ()))
        (fun (_, _, kb) mb => PropKeep kbuf kb ∧ (array (t := i32) pk kb ⋆ R) mb)
        (fun st : BitVec 32 × List (BitVec 32) => (st.1, ()))
        (fun st => st.1.toNat)
        (fun (idx, kb) mi => PropKeep kbuf kb ∧ idx.toNat ≤ 64 ∧ (array (t := i32) pk kb ⋆ R) mi)
        ?_ ?_ ?_
      · rintro _ ⟨_, uip, kbb⟩ mb ⟨hkb, hmb⟩
        have hkb_l := hkb.2.1
        have hkb_l2 : 2912 ≤ kbb.length := by rw [hkb_l]; exact hlen
        c0_hsteps_nogrp
        refine wp_join_state1 (t := i32)
          (fun st : BitVec 32 × List (BitVec 32) => (st.1 : Val i32))
          (fun (nana, kb) mn =>
            PropKeep kbuf kb ∧ nana.toNat ≤ 64 ∧ (array (t := i32) pk kb ⋆ R) mn)
          ?_ ?_
        · rintro _ ⟨nana, kbc⟩ mc ⟨hkc, hnana_le, hmc⟩
          refine wp_while_state1 (t := i32)
            (fun st : BitVec 32 × List (BitVec 32) => (st.1 : Val i32))
            (fun st => nana.toNat - st.1.toNat)
            (fun (ai, kb) mi =>
              ai.toNat ≤ nana.toNat ∧ PropKeep kbuf kb ∧ (array (t := i32) pk kb ⋆ R) mi)
            ?_ ?_
          · intro L2 hL2
            c0_hsteps!
            exact hL2 (0#32, kbc) mc ⟨Nat.zero_le _, hkc, hmc⟩
          · rintro _ ⟨ai, kbd⟩ md ⟨hai_le, hkd, hmd⟩ ih2
            have hkd_l := hkd.2.1
            have hkd_l2 : 2912 ≤ kbd.length := by rw [hkd_l]; exact hlen
            have hret_false : Q (false, ()) md := hQ false kbd md hkd.1 hkd.2.1
              hkd.2.2.1 hkd.2.2.2.2.1 hkd.2.2.2.2.2.2.1
              (by rw [k6b_get_eq (by omega : 1 < kbd.length),
                k6b_elem_of_opt hkd.2.2.2.1 (by omega) (by omega),
                k6b_get_eq (by omega : 1 < kbuf.length)]; exact Nat.le_refl _) hmd
            c0_hsteps_nogrp
            · have hai_lt : ai.toNat < nana.toNat := hc
              have hai1_eq : (ai + 1#32).toNat = ai.toNat + 1 := k6b_add1_toNat hai_lt (by omega)
              have h480n : (480#32).toNat = 480 := rfl
              have h480_nat : (BitVec.setWidth 64 (480#32 + ai)).toNat = 480 + ai.toNat := by
                rw [bv64_add2_lt (by rw [h480n]; omega), h480n]
              have h480_bd : (BitVec.setWidth 64 (480#32 + ai)).toNat < kbd.length := by
                rw [h480_nat]; omega
              refine wp_join0 (fun mj => ∃ kbj, PropKeep kbuf kbj ∧
                  (array (t := i32) pk kbj ⋆ R) mj) ?_ ?_
              · intro _ mj ⟨kbj, hkj, hmj⟩
                c0_hsteps!
                exact ih2 (ai + 1#32, kbj) mj (by dsimp only; rw [hai1_eq]; omega)
                  ⟨by rw [hai1_eq]; omega, hkj, hmj⟩
              · intro _ hJ2
                c0_hsplit
                · let av := kbd[(BitVec.setWidth 64 (480#32 + ai)).toNat]'h480_bd
                  have hav_lt : av.toNat < nv.toNat := by
                    have hnv_eq0 : kbuf[(BitVec.ofNat 64 0).toNat]'(by simp; omega) = nv := rfl
                    simpa [av, hnv_eq0] using hc
                  clear hc
                  have h416n : (416#32).toNat = 416 := rfl
                  have h416_nat : (BitVec.setWidth 64 (416#32 + av)).toNat = 416 + av.toNat := by
                    rw [bv64_add2_lt (by rw [h416n]; omega), h416n]
                  have h416_bd : (BitVec.setWidth 64 (416#32 + av)).toNat < kbd.length := by
                    rw [h416_nat]; omega
                  c0_hsteps!
                  exact hJ2 m ⟨_, propKeep_of_set hkd (BitVec.setWidth 64 (416#32 + av)).toNat _
                    (by rw [h416_nat]; omega) (by rw [h416_nat]; omega) (by rw [h416_nat]; omega)
                    (by rw [h416_nat]; omega) (by rw [h416_nat]; omega)
                    (Or.inl (by rw [h416_nat]; omega)), hm⟩
                · clear hc
                  c0_hsteps!
                  exact hJ2 md ⟨kbd, hkd, hmd⟩
            · exact hret_false
            · exact hret_false
            · exact hret_false
            · exact hret_false
            · exact hret_false
            · let nres := kbd[18]'(by omega)
              let nkl := kbd[17]'(by omega)
              have hnres_le : nres.toNat ≤ 128 := by
                have hnot : ¬BitVec.toNat (128 : BitVec 32) <
                    BitVec.toNat (kbd[(BitVec.ofNat 64 18).toNat]'(by
                      rw [show (BitVec.ofNat 64 18).toNat = 18 from rfl]; omega)) := by
                  assumption
                exact Nat.le_of_not_lt (by simpa [nres] using hnot)
              have hnkl_pos : 0 < nkl.toNat := by
                have hnot : ¬(kbd[(BitVec.ofNat 64 17).toNat]'(by
                    rw [show (BitVec.ofNat 64 17).toNat = 17 from rfl]; omega)) = 0 := by
                  assumption
                have hne0 : nkl ≠ 0#32 := fun h => hnot (by simpa [nkl] using h)
                exact Nat.pos_of_ne_zero fun h =>
                  hne0 (BitVec.eq_of_toNat_eq (by simpa using h))
              have hnkl_le : nkl.toNat ≤ 64 := by
                have hnot : ¬BitVec.toNat (64 : BitVec 32) <
                    BitVec.toNat (kbd[(BitVec.ofNat 64 17).toNat]'(by
                      rw [show (BitVec.ofNat 64 17).toNat = 17 from rfl]; omega)) := by
                  assumption
                exact Nat.le_of_not_lt (by simpa [nkl] using hnot)
              have h544_nat :
                  (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 544)).toNat = 544 := rfl
              rw [h544_nat] at hm
              have hpk_kl0 := propKeep_of_set hkd 544 uip (by decide) (by decide)
                (by decide) (by decide) (by decide) (Or.inl (by decide))
              have hkl0_len : 2912 ≤ (kbd.set 544 uip).length := by
                rw [hpk_kl0.2.1]; exact hlen
              focus
                refine wp_while_state_pure
                  (ts := [i32, i32, i32])
                  (fun st : BitVec 32 × BitVec 32 × BitVec 32 => (st.1, st.2.1, st.2.2, ()))
                  (fun st => nkl.toNat - st.2.2.toNat)
                  (fun (jlvl, wi, i) =>
                    1 ≤ wi.toNat ∧ wi.toNat ≤ 64 ∧
                    (wi.toNat < nkl.toNat ∨ (nkl.toNat = 1 ∧ wi = 1#32)) ∧
                    1 ≤ i.toNat ∧ i.toNat ≤ nkl.toNat)
                  ?_ ?_
                · intro L3 hL3
                  c0_hsteps!
                  have hw_disj :
                      (1 : Nat) < nkl.toNat ∨ (nkl.toNat = 1 ∧ (1#32 : BitVec 32) = 1#32) := by
                    rcases Nat.eq_or_lt_of_le hnkl_pos with h1 | hgt
                    · exact Or.inr ⟨h1.symm, rfl⟩
                    · exact Or.inl hgt
                  exact hL3 (0#32, 1#32, 1#32) ⟨by decide, by decide, hw_disj, by decide, hnkl_pos⟩
                · rintro L3 ⟨jlvl, wi, i⟩ ⟨hwi_ge, hwi_64, hwi_disj, hi_ge, hi_le⟩ ih3
                  c0_hsplit
                  · have hi_lt : i.toNat < nkl.toNat := hc
                    clear hc
                    have h544n : (544#32).toNat = 544 := rfl
                    have h544_bd :
                        (BitVec.setWidth 64 (544#32 + i)).toNat < (kbd.set 544 uip).length := by
                      rw [bv64_add2_lt (by rw [h544n]; omega), h544n, hpk_kl0.2.1]; omega
                    have hi1_eq : (i + 1#32).toNat = i.toNat + 1 := k6b_add1_toNat hi_lt (by omega)
                    c0_hsteps_nogrp
                    refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
                      (fun st => (st.1, st.2, ()))
                      (fun (j', w') => 1 ≤ w'.toNat ∧ w'.toNat ≤ 64 ∧
                        (w'.toNat < nkl.toNat ∨ (nkl.toNat = 1 ∧ w' = 1#32)))
                      (fun _ (j', w') hgw => by
                        c0_hsteps!
                        exact ih3 (j', w', i + 1#32) (by dsimp only; rw [hi1_eq]; omega)
                          ⟨hgw.1, hgw.2.1, hgw.2.2, by rw [hi1_eq]; omega, by rw [hi1_eq]; omega⟩)
                      (fun _ hJ3a => by
                        c0_hsplit
                        · have h0n : (BitVec.ofNat 64 0).toNat = 0 := rfl
                          have hkv_lt :
                              _ < (kbuf[(BitVec.ofNat 64 0).toNat]'(by simp; omega)).toNat := hc
                          clear hc
                          let kv := ((kbd.set 544 uip)[(BitVec.setWidth 64
                            (544#32 + i)).toNat]'h544_bd) >>> (1 : Nat)
                          have hkv_bd : kv.toNat < nv.toNat := by
                            simpa [kv, nv, h0n, BitVec.toNat_ushiftRight,
                              Nat.shiftRight_eq_div_pow] using hkv_lt
                          have h32n : (32#32).toNat = 32 := rfl
                          have h32_bd : (BitVec.setWidth 64 (32#32 + kv)).toNat <
                              (kbd.set 544 uip).length := by
                            rw [bv64_add2_lt (by rw [h32n]; omega), h32n, hpk_kl0.2.1]; omega
                          c0_hsteps_nogrp
                          refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
                            (fun st => (st.1, st.2, ()))
                            (fun (j', w') => 1 ≤ w'.toNat ∧ w'.toNat ≤ 64 ∧
                              (w'.toNat < nkl.toNat ∨ (nkl.toNat = 1 ∧ w' = 1#32)))
                            (fun _ (j', w') hgw => by c0_hsteps!; exact hJ3a (j', w') hgw)
                            (fun _ hJ3b => by
                              c0_hsplit
                              · c0_hsteps!; exact hJ3b (_, i) ⟨hi_ge, by omega, Or.inl hi_lt⟩
                              · c0_hsteps!; exact hJ3b (jlvl, wi) ⟨hwi_ge, hwi_64, hwi_disj⟩)
                        · clear hc; c0_hsteps!; exact hJ3a (jlvl, wi) ⟨hwi_ge, hwi_64, hwi_disj⟩)
                  · clear hc
                    refine wp_join0 (fun msw => ∃ kbsw, PropKeep kbuf kbsw ∧
                        (array (t := i32) pk kbsw ⋆ R) msw) ?_ ?_
                    · intro _ msw ⟨kbsw, hksw, hmsw⟩
                      have hksw_l := hksw.2.1
                      have hksw_l2 : 2912 ≤ kbsw.length := by rw [hksw_l]; exact hlen
                      c0_hsteps_nogrp
                      m7_call hBacktrack
                      dsimp only [vals, Arg.val]
                      refine fullK6BacktrackM7Spec_intro (by omega) hmsw ?_
                      intro kbb mbb hlenb hkeepb hmbb
                      have hkpb := propKeep_of_backtrack hksw hlenb hkeepb
                      have hkpb_l := hkpb.2.1
                      have hkpb_l2 : 2912 ≤ kbb.length := by rw [hkpb_l]; exact hlen
                      refine wp_while_state1 (t := i32)
                        (fun st : BitVec 32 × List (BitVec 32) => (st.1 : Val i32))
                        (fun st => nana.toNat - st.1.toNat)
                        (fun (ai, kbm) mm =>
                          ai.toNat ≤ nana.toNat ∧ PropKeep kbuf kbm ∧
                          (array (t := i32) pk kbm ⋆ R) mm)
                        ?_ ?_
                      · intro L4 hL4
                        c0_hsteps!
                        exact hL4 (0#32, kbb) mbb ⟨Nat.zero_le _, hkpb, hmbb⟩
                      · rintro L4 ⟨ai, kbm⟩ mm ⟨hai_le, hkbm, hmm⟩ ih4
                        have hkbm_l := hkbm.2.1
                        have hkbm_l2 : 2912 ≤ kbm.length := by rw [hkbm_l]; exact hlen
                        c0_hsplit
                        · have hai_lt : ai.toNat < nana.toNat := hc
                          clear hc
                          have hai1_eq : (ai + 1#32).toNat = ai.toNat + 1 :=
                            k6b_add1_toNat hai_lt (by omega)
                          have h480n : (480#32).toNat = 480 := rfl
                          have h480_bd : (BitVec.setWidth 64 (480#32 + ai)).toNat < kbm.length := by
                            rw [bv64_add2_lt (by rw [h480n]; omega), h480n]; omega
                          c0_hsteps_nogrp
                          m7_call hMtf
                          dsimp only [vals, Arg.val]
                          refine fullK6MtfM7Spec_intro (by omega) hmm ?_
                          intro kbm' mm' hlenm hkeepm hmm'
                          c0_hsteps!
                          exact ih4 (ai + 1#32, kbm') mm' (by dsimp only; rw [hai1_eq]; omega)
                            ⟨by rw [hai1_eq]; omega, propKeep_of_mtf hkbm hlenm hkeepm, hmm'⟩
                        · clear hc
                          have hkbm_ok := hkbm.1
                          have hbm_ge := hkbm_ok.base_ge
                          have hbm_lt28 := hkbm_ok.length_lt
                          have hkbm15 : kbm[15]'(by omega) = acap :=
                            k6b_elem_of_opt hkbm.2.2.2.2.2.2.1 (by omega) (by omega)
                          have hkbm1 : kbm[1]'(by omega) = nc :=
                            k6b_elem_of_opt hkbm.2.2.2.1 (by omega) (by omega)
                          have hbm_cap : 2912 + acap.toNat ≤ kbm.length := by
                            simpa [hkbm15, k6b_get_eq (by omega : 15 < kbm.length)] using
                              hkbm_ok.length_ge
                          let alen_m := kbm[14]'(by omega)
                          have halen_le : alen_m.toNat ≤ acap.toNat := by
                            simpa [alen_m, hkbm15, k6b_get_eq (by omega : 14 < kbm.length),
                              k6b_get_eq (by omega : 15 < kbm.length)] using hkbm_ok.alen_le
                          have hret_false_m : Q (false, ()) mm := hQ false kbm mm hkbm.1 hkbm.2.1
                            hkbm.2.2.1 hkbm.2.2.2.2.1 hkbm.2.2.2.2.2.2.1
                            (by rw [k6b_get_eq (by omega : 1 < kbm.length), hkbm1,
                              k6b_get_eq (by omega : 1 < kbuf.length)]; exact Nat.le_refl _) hmm
                          c0_hsplit
                          · c0_hsteps!
                            exact hret_false_m
                          · have hnc_lt256 : (kbm[1]'(by omega)).toNat < 256 := by
                              have h256n : (256#32 : BitVec 32).toNat = 256 := rfl
                              have hnot : ¬(256#32 : BitVec 32).toNat ≤ (kbm[1]'(by omega)).toNat :=
                                hc
                              omega
                            clear hc
                            c0_hsplit
                            · c0_hsteps!
                              exact hret_false_m
                            · have hfit : alen_m.toNat + nkl.toNat + nres.toNat ≤ acap.toNat := by
                                have hlt_a : alen_m.toNat + nkl.toNat + nres.toNat < 2 ^ 32 := by
                                  omega
                                have hle :
                                    ((kbm[14]'(by omega)).toNat + (kbd[17]'(by omega)).toNat +
                                      (kbd[18]'(by omega)).toNat) % 2 ^ 32 ≤
                                      (kbm[15]'(by omega)).toNat := by
                                  simpa [BitVec.toNat_add] using hc
                                rw [Nat.mod_eq_of_lt hlt_a, hkbm15] at hle
                                exact hle
                              clear hc
                              c0_hsteps_nogrp
                              refine wp_while_state1 (t := i32)
                                (fun st : BitVec 32 × List (BitVec 32) => (st.1 : Val i32))
                                (fun st => nkl.toNat - st.1.toNat)
                                (fun (ci, kbc5) mc5 =>
                                  ci.toNat ≤ nkl.toNat ∧ PropKeep kbuf kbc5 ∧
                                  (array (t := i32) pk kbc5 ⋆ R) mc5)
                                ?_ ?_
                              · intro L5 hL5
                                c0_hsteps!
                                exact hL5 (0#32, kbm) mm ⟨Nat.zero_le _, hkbm, hmm⟩
                              · rintro L5 ⟨ci, kbc5⟩ mc5 ⟨hci_le, hkc5, hmc5⟩ ih5
                                have hkc5_l := hkc5.2.1
                                have hkc5_l2 : 2912 ≤ kbc5.length := by rw [hkc5_l]; exact hlen
                                c0_hsplit
                                · have hci_lt : ci.toNat < nkl.toNat := hc
                                  clear hc
                                  have hci1_eq : (ci + 1#32).toNat = ci.toNat + 1 :=
                                    k6b_add1_toNat hci_lt (by omega)
                                  have h544n : (544 : BitVec 32).toNat = 544 := rfl
                                  have h544_bd :
                                      (BitVec.setWidth 64 ((544 : BitVec 32) + ci)).toNat <
                                      kbc5.length := by
                                    rw [bv64_add2_lt (by rw [h544n]; omega), h544n]; omega
                                  have h2912n : (2912 : BitVec 32).toNat = 2912 := rfl
                                  have h2912_a : ((2912 : BitVec 32) + alen_m).toNat =
                                      2912 + alen_m.toNat := by
                                    rw [BitVec.toNat_add, h2912n, Nat.mod_eq_of_lt (by omega)]
                                  have hdst_nat :
                                      (BitVec.setWidth 64
                                        ((2912 : BitVec 32) + alen_m + ci)).toNat =
                                      2912 + alen_m.toNat + ci.toNat := by
                                    rw [bv64_add2_lt (by rw [h2912_a]; omega), h2912_a]
                                  have hdst_bd :
                                      (BitVec.setWidth 64
                                        ((2912 : BitVec 32) + alen_m + ci)).toNat <
                                      kbc5.length := by
                                    rw [hdst_nat]; omega
                                  c0_hsteps!
                                  have h14_lit :
                                      (BitVec.ofNat (OfNat.ofNat 64)
                                        (OfNat.ofNat 14)).toNat = 14 := rfl
                                  have h14_kbm :
                                      kbm[(BitVec.ofNat (OfNat.ofNat 64)
                                        (OfNat.ofNat 14)).toNat]'(by rw [h14_lit]; omega) =
                                        alen_m := by
                                    simp [alen_m, h14_lit]
                                  rw [h14_kbm] at hm
                                  let v5 := kbc5[(BitVec.setWidth 64
                                    ((544 : BitVec 32) + ci)).toNat]'h544_bd
                                  have hkc5' := propKeep_of_set hkc5
                                    (BitVec.setWidth 64
                                      ((2912 : BitVec 32) + alen_m + ci)).toNat v5
                                    (by rw [hdst_nat]; omega) (by rw [hdst_nat]; omega)
                                    (by rw [hdst_nat]; omega) (by rw [hdst_nat]; omega)
                                    (by rw [hdst_nat]; omega) (Or.inr (by rw [hdst_nat]; omega))
                                  exact ih5 (ci + 1#32, _) m (by dsimp only; rw [hci1_eq]; omega)
                                    ⟨by rw [hci1_eq]; omega, hkc5', hm⟩
                                · clear hc
                                  refine wp_while_state1 (t := i32)
                                    (fun st : BitVec 32 × List (BitVec 32) => (st.1 : Val i32))
                                    (fun st => nres.toNat - st.1.toNat)
                                    (fun (ri, kbc6) mc6 =>
                                      ri.toNat ≤ nres.toNat ∧ PropKeep kbuf kbc6 ∧
                                      (array (t := i32) pk kbc6 ⋆ R) mc6)
                                    ?_ ?_
                                  · intro L6 hL6
                                    c0_hsteps!
                                    exact hL6 (0#32, kbc5) mc5 ⟨Nat.zero_le _, hkc5, hmc5⟩
                                  · rintro L6 ⟨ri, kbc6⟩ mc6 ⟨hri_le, hkc6, hmc6⟩ ih6
                                    have hkc6_l := hkc6.2.1
                                    have hkc6_l2 : 2912 ≤ kbc6.length := by rw [hkc6_l]; exact hlen
                                    c0_hsplit
                                    · have hri_lt : ri.toNat < nres.toNat := hc
                                      clear hc
                                      have hri1_eq : (ri + 1#32).toNat = ri.toNat + 1 :=
                                        k6b_add1_toNat hri_lt (by omega)
                                      have h2784n : (2784 : BitVec 32).toNat = 2784 := rfl
                                      have h2784_bd :
                                          (BitVec.setWidth 64 ((2784 : BitVec 32) + ri)).toNat <
                                          kbc6.length := by
                                        rw [bv64_add2_lt (by rw [h2784n]; omega), h2784n]; omega
                                      have h2912n : (2912#32).toNat = 2912 := rfl
                                      have h2912_a : (2912#32 + alen_m).toNat =
                                          2912 + alen_m.toNat := by
                                        rw [BitVec.toNat_add, h2912n, Nat.mod_eq_of_lt (by omega)]
                                      have h2912_b : (2912#32 + alen_m + nkl).toNat =
                                          2912 + alen_m.toNat + nkl.toNat := by
                                        rw [BitVec.toNat_add, h2912_a, Nat.mod_eq_of_lt (by omega)]
                                      have hdst_nat : (BitVec.setWidth 64
                                          (2912#32 + alen_m + nkl + ri)).toNat =
                                          2912 + alen_m.toNat + nkl.toNat + ri.toNat := by
                                        rw [bv64_add2_lt (by rw [h2912_b]; omega), h2912_b]
                                      have hdst_bd : (BitVec.setWidth 64
                                          (2912#32 + alen_m + nkl + ri)).toNat < kbc6.length := by
                                        rw [hdst_nat]; omega
                                      c0_hsteps!
                                      have h14_lit :
                                          (BitVec.ofNat (OfNat.ofNat 64)
                                            (OfNat.ofNat 14)).toNat = 14 := rfl
                                      have h14_kbm :
                                          kbm[(BitVec.ofNat (OfNat.ofNat 64)
                                            (OfNat.ofNat 14)).toNat]'(by rw [h14_lit]; omega) =
                                            alen_m := by
                                        simp [alen_m, h14_lit]
                                      have h17_kbd :
                                          kbd[(BitVec.ofNat (OfNat.ofNat 64)
                                            (OfNat.ofNat 17)).toNat]'(by rw [h17]; omega) =
                                            nkl := by
                                        simp [nkl, h17]
                                      have hdst_nat2 :
                                          (BitVec.setWidth 64
                                            ((2912 : BitVec 32) + alen_m + nkl + ri)).toNat =
                                          2912 + alen_m.toNat + nkl.toNat + ri.toNat := hdst_nat
                                      rw [h14_kbm, h17_kbd] at hm
                                      let v6 := kbc6[(BitVec.setWidth 64
                                        ((2784 : BitVec 32) + ri)).toNat]'h2784_bd
                                      have hkc6' := propKeep_of_set hkc6
                                        (BitVec.setWidth 64
                                          ((2912 : BitVec 32) + alen_m + nkl + ri)).toNat v6
                                        (by rw [hdst_nat2]; omega) (by rw [hdst_nat2]; omega)
                                        (by rw [hdst_nat2]; omega) (by rw [hdst_nat2]; omega)
                                        (by rw [hdst_nat2]; omega)
                                        (Or.inr (by rw [hdst_nat2]; omega))
                                      exact ih6 (ri + 1#32, _) m
                                        (by dsimp only; rw [hri1_eq]; omega)
                                        ⟨by rw [hri1_eq]; omega, hkc6', hm⟩
                                    · clear hc
                                      have hk15_c6 : kbc6[15]?.getD 0#32 = acap := by
                                        rw [hkc6.2.2.2.2.2.2.1]; exact k6b_get_eq (by omega)
                                      have hk1_c6 : kbc6[1]?.getD 0#32 = nc := by
                                        rw [hkc6.2.2.2.1]; exact k6b_get_eq (by omega)
                                      have happ := analyze_append_k6BufOk hkc6 hk1_c6
                                        (by rw [← hkbm1]; exact hnc_lt256)
                                        hnkl_le hnres_le (by rw [hk15_c6]; exact hfit) (by omega)
                                      let kb1 := kbc6.set 14 (alen_m + nkl + nres)
                                      let kb2 := kb1.set (1888 + nc.toNat) alen_m
                                      let kb3 := kb2.set (2144 + nc.toNat) (nkl ||| 1073741824#32)
                                      let kb4 := kb3.set (2400 + nc.toNat) nres
                                      let kb5 := kb4.set 1 (nc + 1#32)
                                      have hs_app : SolveKeep kbuf kb5 :=
                                        ⟨happ.1, happ.2.1, happ.2.2.1, happ.2.2.2.2.2,
                                          happ.2.2.2.1, happ.2.2.2.2.1⟩
                                      have h1888n : (1888 : BitVec 32).toNat = 1888 := rfl
                                      have h2144n : (2144 : BitVec 32).toNat = 2144 := rfl
                                      have h2400n : (2400 : BitVec 32).toNat = 2400 := rfl
                                      have h14_nat : (BitVec.ofNat (OfNat.ofNat 64)
                                          (OfNat.ofNat 14)).toNat = 14 := rfl
                                      have h1_nat : (BitVec.ofNat (OfNat.ofNat 64)
                                          (OfNat.ofNat 1)).toNat = 1 := rfl
                                      have h1888_nat :
                                          (BitVec.setWidth 64 ((1888 : BitVec 32) + nc)).toNat =
                                          1888 + nc.toNat := by
                                        rw [bv64_add2_lt (by rw [h1888n]; omega), h1888n]
                                      have h2144_nat :
                                          (BitVec.setWidth 64 ((2144 : BitVec 32) + nc)).toNat =
                                          2144 + nc.toNat := by
                                        rw [bv64_add2_lt (by rw [h2144n]; omega), h2144n]
                                      have h2400_nat :
                                          (BitVec.setWidth 64 ((2400 : BitVec 32) + nc)).toNat =
                                          2400 + nc.toNat := by
                                        rw [bv64_add2_lt (by rw [h2400n]; omega), h2400n]
                                      have hkbm1_64 :
                                          kbm[(BitVec.ofNat (OfNat.ofNat 64)
                                            (OfNat.ofNat 1)).toNat]'(by rw [h1_nat]; omega) = nc :=
                                        by simpa [h1_nat] using hkbm1
                                      have hk14_eq :
                                          kbm[(BitVec.ofNat (OfNat.ofNat 64)
                                            (OfNat.ofNat 14)).toNat]'(by rw [h14_nat]; omega) =
                                            alen_m := by
                                        simp [alen_m, h14_nat]
                                      have hk17_eq :
                                          kbd[(BitVec.ofNat (OfNat.ofNat 64)
                                            (OfNat.ofNat 17)).toNat]'(by rw [h17]; omega) =
                                            nkl := by
                                        simp [nkl, h17]
                                      have hk18_eq :
                                          kbd[(BitVec.ofNat (OfNat.ofNat 64)
                                            (OfNat.ofNat 18)).toNat]'(by rw [h18]; omega) =
                                            nres := by
                                        simp [nres, h18]
                                      have h1888_kbm : (BitVec.setWidth 64 ((1888 : BitVec 32) +
                                          kbm[(BitVec.ofNat 64 1).toNat]'(by
                                            rw [h1_nat]; omega))).toNat = 1888 + nc.toNat := by
                                        rw [hkbm1_64]; exact h1888_nat
                                      have h2144_kbm : (BitVec.setWidth 64 ((2144 : BitVec 32) +
                                          kbm[(BitVec.ofNat 64 1).toNat]'(by
                                            rw [h1_nat]; omega))).toNat = 2144 + nc.toNat := by
                                        rw [hkbm1_64]; exact h2144_nat
                                      have h2400_kbm : (BitVec.setWidth 64 ((2400 : BitVec 32) +
                                          kbm[(BitVec.ofNat 64 1).toNat]'(by
                                            rw [h1_nat]; omega))).toNat = 2400 + nc.toNat := by
                                        rw [hkbm1_64]; exact h2400_nat
                                      have array_len_set :
                                          ∀ {xs : List (BitVec 32)} {i v} {m' : Mem 64},
                                            (array (t := i32) pk (xs.set i v) ⋆ R) m' →
                                            2912 ≤ xs.length → 2912 ≤ (xs.set i v).length :=
                                        fun _ h => by rw [List.length_set]; exact h
                                      have hl_s0 : 2912 ≤ kbc6.length := by omega
                                      have h544_lit : (BitVec.ofNat (OfNat.ofNat 64)
                                          (OfNat.ofNat 544)).toNat = 544 := rfl
                                      have h545_lit : (BitVec.ofNat (OfNat.ofNat 64)
                                          (OfNat.ofNat 545)).toNat = 545 := rfl
                                      have hlen_kb5 : 2912 ≤ kb5.length := by
                                        rw [hs_app.2.1]; exact hlen
                                      try clear ih2 ih3 ih4 ih5 ih6 hm4 hmbb hmb hmc hmi0
                                      try clear hmsw hkb hkc hki0 hksw hret_false
                                      try clear hret_false_m
                                      rw [hk14_eq, hkbm1_64, hk17_eq, hk18_eq]
                                      iterate 6 c0_hstep
                                      have hl_s1 := array_len_set hm hl_s0; clear hl_s0
                                      iterate 5 c0_hstep
                                      have hl_s2 := array_len_set hm hl_s1; clear hl_s1
                                      iterate 6 c0_hstep
                                      have hl_s3 := array_len_set hm hl_s2; clear hl_s2
                                      iterate 5 c0_hstep
                                      have hl_s4 := array_len_set hm hl_s3; clear hl_s3
                                      iterate 5 c0_hstep
                                      have hl_s5 := array_len_set hm hl_s4; clear hl_s4
                                      c0_hsteps_nogrp
                                      · rw [h14_nat, h1_nat, h1888_nat, h2144_nat,
                                          h2400_nat] at hm
                                        m7_call hAssign
                                        dsimp only [vals, Arg.val]
                                        refine fullK6AssignM7Spec_intro hlen_kb5 hm ?_
                                        intro kbf mf hlenf hkeepf hmf
                                        have hs_f := solveKeep_of_assign hs_app hlenf hkeepf
                                        c0_hsteps!
                                        exact hQ true kbf mf hs_f.1 hs_f.2.1 hs_f.2.2.1
                                          hs_f.2.2.2.2.1 hs_f.2.2.2.2.2 hs_f.2.2.2.1 hmf
                                      · rw [h14_nat, h1_nat, h1888_nat, h2144_nat,
                                          h2400_nat] at hm
                                        m7_call hWatch
                                        dsimp only [vals, Arg.val]
                                        refine fullK6WatchM7Spec_intro hlen_kb5 hm ?_
                                        intro kbw mw hlenw hkeepw hmw
                                        have hs_w := solveKeep_of_watch hs_app hlenw hkeepw
                                        have hlen_kbw : 2912 ≤ kbw.length := by
                                          rw [hs_w.2.1]; exact hlen
                                        m7_call hAssign
                                        dsimp only [vals, Arg.val]
                                        refine fullK6AssignM7Spec_intro hlen_kbw hmw ?_
                                        intro kbf mf hlenf hkeepf hmf
                                        have hs_f := solveKeep_of_assign hs_w hlenf hkeepf
                                        c0_hsteps!
                                        exact hQ true kbf mf hs_f.1 hs_f.2.1 hs_f.2.2.1
                                          hs_f.2.2.2.2.1 hs_f.2.2.2.2.2 hs_f.2.2.2.1 hmf
                    · intro Jsw hJsw
                      c0_hsplit
                      · c0_hsplit
                        · have h544n : (544 : BitVec 32).toNat = 544 := rfl
                          have h545_add :
                              (BitVec.setWidth 64 ((544 : BitVec 32) + 1)).toNat = 545 := rfl
                          have h545_bd : 545 < (kbd.set 544 uip).length := by
                            rw [hpk_kl0.2.1]; omega
                          have h544w_bd :
                              (BitVec.setWidth 64 ((544 : BitVec 32) + wi)).toNat <
                                (kbd.set 544 uip).length := by
                            rw [bv64_add2_lt (by rw [h544n]; omega), h544n, hpk_kl0.2.1]; omega
                          have h544w_nat :
                              (BitVec.setWidth 64 ((544 : BitVec 32) + wi)).toNat =
                                544 + wi.toNat := by
                            rw [bv64_add2_lt (by rw [h544n]; omega), h544n]
                          let wlit := (kbd.set 544 uip)[(BitVec.setWidth 64
                            ((544 : BitVec 32) + wi)).toNat]'h544w_bd
                          let tlit := (kbd.set 544 uip)[545]'h545_bd
                          have hpk_s1 := propKeep_of_set hpk_kl0 545 wlit (by decide) (by decide)
                            (by decide) (by decide) (by decide) (Or.inl (by decide))
                          have hs1_len : 2912 ≤ ((kbd.set 544 uip).set 545 wlit).length := by
                            rw [hpk_s1.2.1]; exact hlen
                          c0_hsteps_nogrp
                          have h545_val : ∀ h, (kbd.set 544 uip)[(BitVec.setWidth 64
                              ((544 : BitVec 32) + 1)).toNat]'h = tlit := fun _ => by
                            simp only [tlit, h545_add]
                          rw [h545_val, h545_add] at hm
                          have hpk_s2 := propKeep_of_set hpk_s1 (544 + wi.toNat) tlit
                            (by omega) (by omega) (by omega) (by omega) (by omega)
                            (Or.inl (by omega))
                          rw [← h544w_nat] at hpk_s2
                          exact hJsw m ⟨_, hpk_s2, hm⟩
                        · c0_hsteps!; exact hJsw _ ⟨_, hpk_kl0, hm⟩
                      · c0_hsteps!; exact hJsw _ ⟨_, hpk_kl0, hm⟩
        · intro Jn hJn
          c0_hsplit
          · c0_hsteps!; exact hJn (64#32, kbb) mb ⟨hkb, by decide, hmb⟩
          · c0_hsteps!
            have hk16_le : (kbb[16]'(by omega)).toNat ≤ 64 := by
              have hnot : ¬64 < (kbb[16]'(by omega)).toNat := by simpa using hc
              exact Nat.le_of_not_lt hnot
            exact hJn (kbb[16]'(by omega), kbb) mb ⟨hkb, hk16_le, hmb⟩
      · rintro B L ⟨idx, kbi⟩ mi hB ih1 ⟨hki, hidx_le, hmi⟩
        have hki_l := hki.2.1
        have hki_l2 : 2912 ≤ kbi.length := by rw [hki_l]; exact hlen
        c0_hsplit
        · clear hc
          c0_hsplit
          · c0_hsteps!
            exact hB (idx, 0xFFFFFFFF#32, kbi) mi ⟨hki, hmi⟩
          · have hidx_pos : 0 < idx.toNat :=
              Nat.pos_of_ne_zero fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
            clear hc
            have hidx1_eq : (idx - 1#32).toNat = idx.toNat - 1 := by
              rw [BitVec.toNat_sub]; simp; omega
            have h352n : (352#32).toNat = 352 := rfl
            have h352_bd : (BitVec.setWidth 64 (352#32 + (idx - 1#32))).toNat < kbi.length := by
              rw [bv64_add2_lt (by rw [h352n]; omega), h352n]; omega
            c0_hsteps_nogrp
            let p := kbi[(BitVec.setWidth 64 (352#32 + (idx - 1#32))).toNat]'h352_bd
            let pv := p >>> (1 : Nat)
            refine wp_join_group
              (fun _ mj => ∃ kbj, PropKeep kbuf kbj ∧ (array (t := i32) pk kbj ⋆ R) mj)
              ?_ ?_
            · rintro _ _ mj ⟨kbj, hkj, hmj⟩
              c0_hsteps!
              exact ih1 (idx - 1#32, kbj) mj (by dsimp only; rw [hidx1_eq]; omega)
                ⟨hkj, by rw [hidx1_eq]; omega, hmj⟩
            · intro J1 hJ1
              c0_hsplit
              · have hpv_lt : pv.toNat < nv.toNat := by
                  simpa [pv, p, hki.2.2.1, BitVec.toNat_ushiftRight,
                    Nat.shiftRight_eq_div_pow] using hc
                clear hc
                have h416n : (416#32).toNat = 416 := rfl
                have h416_bd : (BitVec.setWidth 64 (416#32 + pv)).toNat < kbi.length := by
                  rw [bv64_add2_lt (by rw [h416n]; omega), h416n]; omega
                c0_hsplit
                · clear hc
                  have h32n : (32#32).toNat = 32 := rfl
                  have h32_bd : (BitVec.setWidth 64 (32#32 + pv)).toNat < kbi.length := by
                    rw [bv64_add2_lt (by rw [h32n]; omega), h32n]; omega
                  c0_hsplit
                  · clear hc
                    have h20n : (BitVec.ofNat 64 20).toNat = 20 := rfl
                    have h20_bd : (BitVec.ofNat 64 20).toNat < kbi.length := by rw [h20n]; omega
                    let decv := kbi[(BitVec.ofNat 64 20).toNat]'h20_bd - 1#32
                    have hkbi20_len :
                        2912 ≤ (kbi.set (BitVec.ofNat 64 20).toNat decv).length := by
                      rw [List.length_set]; exact hki_l2
                    have hpk_dec := propKeep_of_set hki (BitVec.ofNat 64 20).toNat decv
                      (by rw [h20n]; decide) (by rw [h20n]; decide) (by rw [h20n]; decide)
                      (by rw [h20n]; decide) (by rw [h20n]; decide)
                      (Or.inl (by rw [h20n]; decide))
                    c0_hsplit
                    · c0_hsteps!
                      exact hB (idx - 1#32, p ^^^ 1#32, _) m ⟨hpk_dec, hm⟩
                    · clear hc
                      have h96n : (96#32).toNat = 96 := rfl
                      have h96_bd : (BitVec.setWidth 64 (96#32 + pv)).toNat <
                          (kbi.set (BitVec.ofNat 64 20).toNat decv).length := by
                        rw [bv64_add2_lt (by rw [h96n]; omega), h96n]; omega
                      c0_hsplit
                      · c0_hsteps!
                        exact hB (idx - 1#32, p ^^^ 1#32, _) m ⟨hpk_dec, hm⟩
                      · clear hc
                        m7_call hAnaCl
                        dsimp only [vals, Arg.val]
                        refine fullK6AnaClM7Spec_intro hpk_dec.1 hm ?_
                        intro kba ma hlena hkeepa hma
                        c0_hsteps!
                        exact hJ1 _ ma ⟨kba, propKeep_of_ana_cl hpk_dec hlena hkeepa, hma⟩
                  · clear hc; c0_hsteps!; exact hJ1 _ mi ⟨kbi, hki, hmi⟩
                · clear hc; c0_hsteps!; exact hJ1 _ mi ⟨kbi, hki, hmi⟩
              · clear hc; c0_hsteps!; exact hJ1 _ mi ⟨kbi, hki, hmi⟩
        · clear hc
          c0_hsteps!
          exact hB (idx, 0xFFFFFFFF#32, kbi) mi ⟨hki, hmi⟩
      · intro B L _ hL
        c0_hsteps!
        exact hL (idx0, kbi0) mi0 ⟨hki0, hidx0_le, hmi0⟩
    · intro J hJ
      c0_hsplit
      · c0_hsteps!
        exact hJ (64#32, kb4) m4 ⟨hpk4, by decide, hm4⟩
      · c0_hsteps!
        have hk5_le : (kb4[5]'(by omega)).toNat ≤ 64 := by
          have hnot : ¬64 < (kb4[5]'(by omega)).toNat := by simpa using hc
          exact Nat.le_of_not_lt hnot
        exact hJ (kb4[5]'(by omega), kb4) m4 ⟨hpk4, hk5_le, hm4⟩

/-! ## 5. `full_k6_solve_m7_wp` -/

private theorem k6_fuel_addr_ofnat (h : BitVec 64) :
    h + (168 : BitVec 64) = (h + 32) + BitVec.ofNat 64 (8 * 17) := by
  rw [BitVec.add_assoc]; congr 1

private theorem k6_fuel_addr_bv (h : BitVec 64) :
    h + 168#64 = (h + 32) + BitVec.ofNat 64 (8 * 17) := by
  rw [BitVec.add_assoc]; congr 1

namespace K6FuelTactics

@[scoped c0_load] theorem c0_load_k6_fuel_ofnat {h : BitVec 64} {hdr : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (hh : 17 < hdr.length)
    (hm : (array64 (h + 32) hdr ⋆ R) m) :
    loadVal m i64 (h + (168 : BitVec 64)) = some hdr[17] := by
  rw [k6_fuel_addr_ofnat]; exact loadVal_array64 hh hm

@[scoped c0_store] theorem c0_store_k6_fuel_ofnat {h : BitVec 64} {hdr : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64) (hh : 17 < hdr.length)
    (hm : (array64 (h + 32) hdr ⋆ R) m) :
    storeOk m i64 (h + (168 : BitVec 64)) ∧
      (array64 (h + 32) (hdr.set 17 v) ⋆ R)
        (storeMem m i64 (h + (168 : BitVec 64)) v) := by
  rw [k6_fuel_addr_ofnat]; exact store_array64 v hh hm

@[scoped c0_load] theorem c0_load_k6_fuel_bv {h : BitVec 64} {hdr : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (hh : 17 < hdr.length)
    (hm : (array64 (h + 32) hdr ⋆ R) m) :
    loadVal m i64 (h + 168#64) = some hdr[17] := by
  rw [k6_fuel_addr_bv]; exact loadVal_array64 hh hm

@[scoped c0_store] theorem c0_store_k6_fuel_bv {h : BitVec 64} {hdr : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64) (hh : 17 < hdr.length)
    (hm : (array64 (h + 32) hdr ⋆ R) m) :
    storeOk m i64 (h + 168#64) ∧
      (array64 (h + 32) (hdr.set 17 v) ⋆ R) (storeMem m i64 (h + 168#64) v) := by
  rw [k6_fuel_addr_bv]; exact store_array64 v hh hm

end K6FuelTactics

section
open scoped K6Tactics K6FuelTactics

private theorem k6_pick_bounds {kb : List (BitVec 32)} {nv cur : BitVec 32}
    (hlen : 2912 ≤ kb.length) (hnv : nv.toNat ≤ 64) (hcur : cur.toNat < nv.toNat) :
    (BitVec.setWidth 64 ((608 : BitVec 32) + (cur <<< (1 : Nat)))).toNat < kb.length ∧
    (BitVec.setWidth 64 ((160 : BitVec 32) + cur)).toNat < kb.length := by
  have hsh : (cur <<< (1 : Nat)).toNat = 2 * cur.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  have h608n : (608 : BitVec 32).toNat = 608 := rfl
  have h160n : (160 : BitVec 32).toNat = 160 := rfl
  constructor
  · rw [bv64_add2_lt (by rw [h608n, hsh]; omega), h608n, hsh]; omega
  · rw [bv64_add2_lt (by rw [h160n]; omega), h160n]; omega

private theorem k6_sep_swap (p q r : Mem 64 → Prop) : (p ⋆ q ⋆ r) = (q ⋆ (p ⋆ r)) := by
  rw [sep_assoc, sep_comm_l]

/-- Certifies `fullK6SolveM7Spec` for `full_k6_solve_m7`. -/
theorem full_k6_solve_m7_wp (Γ : Env)
    (hProp : ∀ a m Q X, fullK6PropM7Spec a m Q X →
      Γ "full_k6_prop_m7" [i64] [i32] a m Q X)
    (hAssign : ∀ a m Q X, fullK6AssignM7Spec a m Q X →
      Γ "full_k6_assign_m7" [i64, i32, i32] [] a m Q X)
    (hBacktrack : ∀ a m Q X, fullK6BacktrackM7Spec a m Q X →
      Γ "full_k6_backtrack_m7" [i64, i32] [] a m Q X)
    (hAnalyze : ∀ a m Q X, fullK6AnalyzeM7Spec a m Q X →
      Γ "full_k6_analyze_m7" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullK6SolveM7Spec a m Q X →
      Func.wp Γ full_k6_solve_m7_body a m Q X := by
  rintro ⟨hp, pk, tick_lim, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨hdr, kbuf, R, hhdr, hok0, hm0, hQ⟩ := fullK6SolveM7Spec_elim hSpec
  have hlen := hok0.base_ge
  let fuel0 : BitVec 64 := hdr[17]'(by omega)
  have hfuel0_le : fuel0.toNat ≤ (hdr[17]?.getD 0#64).toNat := by
    simp [fuel0, List.getElem?_eq_getElem (by omega : 17 < hdr.length)]
  have hhdr_self : hdr.set 17 fuel0 = hdr := List.set_getElem_self (by omega : 17 < hdr.length)
  have retQ : ∀ (r fuel' : BitVec 64) (kb' : List (BitVec 32)) {m' : Mem 64},
      fuel'.toNat ≤ (hdr[17]?.getD 0#64).toNat → SolveKeep kbuf kb' →
      (array (t := i32) pk kb' ⋆ (array64 (hp + 32) (hdr.set 17 fuel') ⋆ R)) m' →
      Q (r, ()) m' := fun r fuel' kb' m' hfl' hsk' hm' =>
    hQ r fuel' kb' m' hfl' hsk'.1 hsk'.2.1 hsk'.2.2.1 hsk'.2.2.2.1 hsk'.2.2.2.2.1
      hsk'.2.2.2.2.2 ((k6_sep_swap (array64 (hp + 32) (hdr.set 17 fuel'))
        (array (t := i32) pk kb') R) ▸ hm')
  have hm0' : (array (t := i32) pk kbuf ⋆ (array64 (hp + 32) hdr ⋆ R)) m0 :=
    (k6_sep_swap (array64 (hp + 32) hdr) (array (t := i32) pk kbuf) R) ▸ hm0
  unfold Func.wp full_k6_solve_m7_body
  m7_call hBacktrack
  dsimp only [vals, Arg.val]
  refine fullK6BacktrackM7Spec_intro hlen hm0' ?_
  intro kb1 m1 hlen1 hkeep1 hm1
  have hs1 := solveKeep_of_backtrack (solveKeep_refl hok0) hlen1 hkeep1
  have hs1_l : 2912 ≤ kb1.length := by rw [hs1.2.1]; exact hlen
  c0_hsplit
  · c0_hsteps!
    exact retQ 20#64 fuel0 kb1 hfuel0_le hs1 (by rw [hhdr_self]; exact hm1)
  · clear hc
    have h13n : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 13)).toNat = 13 := rfl
    have h12n : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 12)).toNat = 12 := rfl
    have hkb1_13l : 2912 ≤ (kb1.set (BitVec.ofNat (OfNat.ofNat 64)
        (OfNat.ofNat 13)).toNat tick_lim).length := by rw [List.length_set]; exact hs1_l
    c0_hsteps_nogrp
    rw [h13n, h12n] at hm
    let kb2 := (kb1.set 13 tick_lim).set 12 0#32
    have hs2' := solveKeep_of_set hs1 13 tick_lim (by decide) (by decide) (by decide)
      (by decide) (by decide) (Or.inl (by decide))
    have hs2 := solveKeep_of_set hs2' 12 0#32 (by decide) (by decide) (by decide)
      (by decide) (by decide) (Or.inl (by decide))
    have hs2_l : 2912 ≤ kb2.length := by rw [hs2.2.1]; exact hlen
    let nv := kb2[0]'(by omega)
    let nc := kb2[1]'(by omega)
    let acap := kb2[15]'(by omega)
    let nunits := kb2[19]'(by omega)
    c0_hsplit
    · c0_hsteps!
      exact retQ 0#64 fuel0 kb2 hfuel0_le hs2 (by rw [hhdr_self]; exact hm)
    · have hnv_le : nv.toNat ≤ 64 := Nat.le_of_not_lt (show ¬64 < nv.toNat from hc)
      clear hc
      c0_hsplit
      · c0_hsteps!
        exact retQ 0#64 fuel0 kb2 hfuel0_le hs2 (by rw [hhdr_self]; exact hm)
      · have hnc_le : nc.toNat ≤ 256 := Nat.le_of_not_lt (show ¬256 < nc.toNat from hc)
        clear hc
        c0_hsplit
        · c0_hsteps!
          exact retQ 0#64 fuel0 kb2 hfuel0_le hs2 (by rw [hhdr_self]; exact hm)
        · have hnu_le : nunits.toNat ≤ 128 := Nat.le_of_not_lt (show ¬128 < nunits.toNat from hc)
          clear hc
          refine wp_while_state (ts := [i32])
            (fun st : BitVec 32 × List (BitVec 32) => (st.1, ()))
            (fun st => nunits.toNat - st.1.toNat)
            (fun (ui, kb) mi => ui.toNat ≤ nunits.toNat ∧ SolveKeep kbuf kb ∧
              (array (t := i32) pk kb ⋆ (array64 (hp + 32) hdr ⋆ R)) mi)
            ?_ ?_
          · intro J1 hJ1
            c0_hsteps!
            exact hJ1 (0#32, kb2) m ⟨Nat.zero_le _, hs2, hm⟩
          · rintro J1 ⟨ui, kb⟩ mi ⟨hui_le, hsk, hmi⟩ ih1
            have hkb_l : 2912 ≤ kb.length := by rw [hsk.2.1]; exact hlen
            c0_hsplit
            · have hui_lt : ui.toNat < nunits.toNat := hc
              clear hc
              have hui1_eq : (ui + 1#32).toNat = ui.toNat + 1 := by
                rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega)]
              have h2656n : (2656 : BitVec 32).toNat = 2656 := rfl
              have h2656_bd : (BitVec.setWidth 64 ((2656 : BitVec 32) + ui)).toNat <
                  kb.length := by
                rw [bv64_add2_lt (by rw [h2656n]; omega), h2656n]; omega
              have h2656_mod : ((2656 : BitVec 32).toNat + ui.toNat) % 2 ^ 32 % 2 ^ 64 =
                  (BitVec.setWidth 64 ((2656 : BitVec 32) + ui)).toNat := by
                simp [BitVec.toNat_setWidth, BitVec.toNat_add]
              let ucid := kb[(BitVec.setWidth 64 ((2656 : BitVec 32) + ui)).toNat]'h2656_bd
              have hucid_c0 : kb[((2656 : BitVec 32).toNat + ui.toNat) % 2 ^ 32 % 2 ^ 64]'(by
                  rw [h2656_mod]; exact h2656_bd) = ucid :=
                k6b_get_congr h2656_mod _ h2656_bd
              c0_hsteps_nogrp
              refine wp_join0
                (fun mj => ∃ kbj, SolveKeep kbuf kbj ∧
                  (array (t := i32) pk kbj ⋆ (array64 (hp + 32) hdr ⋆ R)) mj)
                ?_ ?_
              · intro _ mj ⟨kbj, hskj, hmj⟩
                c0_hsteps!
                exact ih1 (ui + 1#32, kbj) mj (by dsimp only; rw [hui1_eq]; omega)
                  ⟨by rw [hui1_eq]; omega, hskj, hmj⟩
              · intro Ju1 hJu1
                c0_hsplit
                · have hnc_c0 : kb2[OfNat.ofNat 1 % 2 ^ 64]'(by simp; omega) = nc :=
                    k6b_get_congr (by simp) _ _
                  have hucid_lt : ucid.toNat < nc.toNat := by
                    rw [← hucid_c0, ← hnc_c0]; exact hc
                  clear hc
                  have h1888n : (1888 : BitVec 32).toNat = 1888 := rfl
                  have h1888_bd : (BitVec.setWidth 64 ((1888 : BitVec 32) + ucid)).toNat <
                      kb.length := by
                    rw [bv64_add2_lt (by rw [h1888n]; omega), h1888n]; omega
                  let off := kb[(BitVec.setWidth 64 ((1888 : BitVec 32) + ucid)).toNat]'h1888_bd
                  have h1888_mod : ((1888 : BitVec 32).toNat + (kb[((2656 : BitVec 32).toNat +
                      ui.toNat) % 2 ^ 32 % 2 ^ 64]'(by
                        rw [h2656_mod]; exact h2656_bd)).toNat) % 2 ^ 32 % 2 ^ 64 =
                      (BitVec.setWidth 64 ((1888 : BitVec 32) + ucid)).toNat := by
                    rw [hucid_c0]; simp [BitVec.toNat_setWidth, BitVec.toNat_add]
                  have hoff_c0 : kb[((1888 : BitVec 32).toNat + (kb[((2656 : BitVec 32).toNat +
                      ui.toNat) % 2 ^ 32 % 2 ^ 64]'(by
                        rw [h2656_mod]; exact h2656_bd)).toNat) % 2 ^ 32 % 2 ^ 64]'(by
                        rw [h1888_mod]; exact h1888_bd) = off :=
                    k6b_get_congr h1888_mod _ h1888_bd
                  c0_hsteps_nogrp
                  refine wp_join0
                    (fun mj => ∃ kbj, SolveKeep kbuf kbj ∧
                      (array (t := i32) pk kbj ⋆ (array64 (hp + 32) hdr ⋆ R)) mj)
                    ?_ ?_
                  · intro _ mj ⟨kbj, hskj, hmj⟩; c0_hsteps!; exact hJu1 mj ⟨kbj, hskj, hmj⟩
                  · intro Ju2 hJu2
                    c0_hsplit
                    · have h15m : (OfNat.ofNat 15 : Nat) % 2 ^ 64 = 15 := rfl
                      have hacap_c0 : kb2[OfNat.ofNat 15 % 2 ^ 64]'(by rw [h15m]; omega) = acap :=
                        k6b_get_congr h15m _ _
                      have hoff_lt : off.toNat < acap.toNat := by
                        rw [← hoff_c0, ← hacap_c0]; exact hc
                      clear hc
                      have hkb_lt28 := hsk.1.length_lt
                      have ⟨_, _, _, _, _, hk15_kb⟩ := hsk
                      have ⟨_, _, _, _, _, hk15_2⟩ := hs2
                      have hk15_eq : kb[15]? = kb2[15]? := hk15_kb.trans hk15_2.symm
                      have hkb_cap : 2912 + acap.toNat ≤ kb.length := by
                        have h := hsk.1.length_ge
                        rw [hk15_eq, k6b_get_eq (by omega : 15 < kb2.length)] at h
                        exact h
                      have h2912n : (2912 : BitVec 32).toNat = 2912 := rfl
                      have h2912_bd : (BitVec.setWidth 64 ((2912 : BitVec 32) + off)).toNat <
                          kb.length := by
                        rw [bv64_add2_lt (by rw [h2912n]; omega), h2912n]; omega
                      let ul := kb[(BitVec.setWidth 64
                        ((2912 : BitVec 32) + off)).toNat]'h2912_bd
                      have h2912_mod : ((2912 : BitVec 32).toNat + (kb[((1888 : BitVec 32).toNat +
                          (kb[((2656 : BitVec 32).toNat + ui.toNat) % 2 ^ 32 % 2 ^ 64]'(by
                            rw [h2656_mod]; exact h2656_bd)).toNat) %
                            2 ^ 32 % 2 ^ 64]'(by
                              rw [h1888_mod]; exact h1888_bd)).toNat) % 2 ^ 32 % 2 ^ 64 =
                          (BitVec.setWidth 64 ((2912 : BitVec 32) + off)).toNat := by
                        rw [hoff_c0]; simp [BitVec.toNat_setWidth, BitVec.toNat_add]
                      have hul_c0 : kb[((2912 : BitVec 32).toNat + (kb[((1888 : BitVec 32).toNat +
                          (kb[((2656 : BitVec 32).toNat + ui.toNat) % 2 ^ 32 % 2 ^ 64]'(by
                            rw [h2656_mod]; exact h2656_bd)).toNat) %
                            2 ^ 32 % 2 ^ 64]'(by
                              rw [h1888_mod]; exact h1888_bd)).toNat) % 2 ^ 32 % 2 ^ 64]'(by
                          rw [h2912_mod]; exact h2912_bd) = ul :=
                        k6b_get_congr h2912_mod _ h2912_bd
                      c0_hsteps_nogrp
                      refine wp_join0
                        (fun mj => ∃ kbj, SolveKeep kbuf kbj ∧
                          (array (t := i32) pk kbj ⋆ (array64 (hp + 32) hdr ⋆ R)) mj)
                        ?_ ?_
                      · intro _ mj ⟨kbj, hskj, hmj⟩; c0_hsteps!; exact hJu2 mj ⟨kbj, hskj, hmj⟩
                      · intro Ju3 hJu3
                        c0_hsplit
                        · have h0m : (OfNat.ofNat 0 : Nat) % 2 ^ 64 = 0 := rfl
                          have hnv_c0 :
                              ((kb1.set 13 tick_lim).set 12 0#32)[OfNat.ofNat 0 % 2 ^ 64]'(by
                                rw [h0m]; omega) = nv := k6b_get_congr h0m _ _
                          have hul_lt : ul.toNat < 2 * nv.toNat := by
                            have hmod : 2 * nv.toNat % 2 ^ 32 = 2 * nv.toNat :=
                              Nat.mod_eq_of_lt (by omega)
                            have hc' : (kb[(BitVec.toNat (2912 : BitVec 32) +
                                BitVec.toNat kb[(BitVec.toNat (1888 : BitVec 32) +
                                  BitVec.toNat kb[(BitVec.toNat (2656 : BitVec 32) + ui.toNat) %
                                    2 ^ 32 % 2 ^ 64]) % 2 ^ 32 % 2 ^ 64]) %
                                2 ^ 32 % 2 ^ 64]'(by rw [h2912_mod]; exact h2912_bd)).toNat <
                                2 * (((kb1.set 13 tick_lim).set 12 0#32)[OfNat.ofNat 0 % 2 ^ 64]'(by
                                  rw [h0m]; omega)).toNat % 2 ^ 32 := hc
                            rw [hul_c0, hnv_c0, hmod] at hc'
                            exact hc'
                          clear hc
                          have h608n : (608 : BitVec 32).toNat = 608 := rfl
                          have h608_bd : (BitVec.setWidth 64 ((608 : BitVec 32) + ul)).toNat <
                              kb.length := by
                            rw [bv64_add2_lt (by rw [h608n]; omega), h608n]; omega
                          c0_hsplit
                          · have h7n : (BitVec.ofNat (OfNat.ofNat 64)
                                (OfNat.ofNat 7)).toNat = 7 := rfl
                            c0_hsteps_nogrp
                            rw [h7n] at hm
                            have hsk7 := solveKeep_of_set hsk 7 ucid (by decide) (by decide)
                              (by decide) (by decide) (by decide) (Or.inl (by decide))
                            exact retQ 20#64 fuel0 (kb.set 7 ucid) hfuel0_le hsk7
                              (by rw [hhdr_self]; exact hm)
                          · clear hc
                            refine wp_join0
                              (fun mj => ∃ kbj, SolveKeep kbuf kbj ∧
                                (array (t := i32) pk kbj ⋆ (array64 (hp + 32) hdr ⋆ R)) mj)
                              ?_ ?_
                            · intro _ mj ⟨kbj, hskj, hmj⟩
                              c0_hsteps!; exact hJu3 mj ⟨kbj, hskj, hmj⟩
                            · intro Ju4 hJu4
                              c0_hsplit
                              · m7_call hAssign
                                dsimp only [vals, Arg.val]
                                refine fullK6AssignM7Spec_intro hkb_l hmi ?_
                                intro kba ma hlena hkeepa hma
                                c0_hsteps!
                                exact hJu4 ma ⟨kba, solveKeep_of_assign hsk hlena hkeepa, hma⟩
                              · c0_hsteps!; exact hJu4 mi ⟨kb, hsk, hmi⟩
                        · c0_hsteps!; exact hJu3 mi ⟨kb, hsk, hmi⟩
                    · c0_hsteps!; exact hJu2 mi ⟨kb, hsk, hmi⟩
                · c0_hsteps!; exact hJu1 mi ⟨kb, hsk, hmi⟩
            · clear hc
              m7_call hProp
              dsimp only [vals, Arg.val]
              refine fullK6PropM7Spec_intro hsk.1 hmi ?_
              intro confl kbp mp hokp hlenp hp0 hp1 hp2 hp15 _ hmp
              have hskp := solveKeep_of_prop hsk hokp hlenp hp0 hp1 hp2 hp15
              have hkp_l : 2912 ≤ kbp.length := by rw [hskp.2.1]; exact hlen
              c0_hsplit
              · have h7n : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 7)).toNat = 7 := rfl
                c0_hsteps_nogrp
                rw [h7n] at hm
                have hskp7 := solveKeep_of_set hskp 7 confl (by decide) (by decide) (by decide)
                  (by decide) (by decide) (Or.inl (by decide))
                exact retQ 20#64 fuel0 (kbp.set 7 confl) hfuel0_le hskp7
                  (by rw [hhdr_self]; exact hm)
              · clear hc
                refine wp_while_state (ts := [i32])
                  (fun st : BitVec 32 × BitVec 64 × List (BitVec 32) => (st.1, ()))
                  (fun st => st.2.1.toNat)
                  (fun (cf, fl, kb) mi =>
                    fl.toNat ≤ (hdr[17]?.getD 0#64).toNat ∧ SolveKeep kbuf kb ∧
                    (array (t := i32) pk kb ⋆ (array64 (hp + 32) (hdr.set 17 fl) ⋆ R)) mi)
                  ?_ ?_
                · intro Jo hJo
                  c0_hsteps!
                  exact hJo (confl, fuel0, kbp) mp ⟨hfuel0_le, hskp, by rw [hhdr_self]; exact hmp⟩
                · rintro Jo ⟨cf, fl, kb⟩ mi ⟨hfl_le, hsk, hmi⟩ ih
                  have hkb_l : 2912 ≤ kb.length := by rw [hsk.2.1]; exact hlen
                  c0_hsplit
                  · clear hc
                    have h17_hdr : 17 < (hdr.set 17 fl).length := by simp [hhdr]
                    c0_hsplit
                    · have hfl_pos : 0 < fl.toNat := by
                        simpa [List.getElem_set_self h17_hdr] using hc
                      clear hc
                      let fl1 := fl - 1#64
                      have hfl1_eq : fl1.toNat = fl.toNat - 1 := by
                        dsimp only [fl1]; rw [BitVec.toNat_sub]
                        simp only [BitVec.toNat_ofNat]; omega
                      have hfl1_lt : fl1.toNat < fl.toNat := by omega
                      have hfl1_le : fl1.toNat ≤ (hdr[17]?.getD 0#64).toNat := by omega
                      have hfl_val : (hdr.set 17 fl)[17]'h17_hdr - (1 : BitVec 64) = fl1 := by
                        rw [List.getElem_set_self h17_hdr]; rfl
                      c0_hsplit
                      · clear hc
                        rw [hfl_val, List.set_set, sep_comm_l] at hm
                        try rw [sep_emp] at hm
                        c0_hsplit
                        · have h7n : (BitVec.ofNat (OfNat.ofNat 64)
                              (OfNat.ofNat 7)).toNat = 7 := rfl
                          c0_hsteps_nogrp
                          rw [h7n] at hm
                          try rw [sep_emp] at hm
                          have hsk7 := solveKeep_of_set hsk 7 cf (by decide) (by decide)
                            (by decide) (by decide) (by decide) (Or.inl (by decide))
                          exact retQ 20#64 fl1 (kb.set 7 cf) hfl1_le hsk7 hm
                        · clear hc
                          m7_call hAnalyze
                          dsimp only [vals, Arg.val]
                          refine fullK6AnalyzeM7Spec_intro hsk.1 hm ?_
                          intro oka kba ma hoka hlena ha0 ha2 ha15 ha1_le hma
                          have hska := solveKeep_of_analyze hsk hoka hlena ha0 ha2 ha15 ha1_le
                          c0_hsplit
                          · m7_call hProp
                            dsimp only [vals, Arg.val]
                            refine fullK6PropM7Spec_intro hska.1 hma ?_
                            intro cf' kbp' mp' hokp' hlenp' hp0' hp1' hp2' hp15' _ hmp'
                            have hskp' := solveKeep_of_prop hska hokp' hlenp' hp0' hp1' hp2' hp15'
                            c0_hsteps!
                            exact ih (cf', fl1, kbp') mp' hfl1_lt ⟨hfl1_le, hskp', hmp'⟩
                          · c0_hsteps!; exact retQ 0#64 fl1 kba hfl1_le hska hma
                      · clear hc
                        rw [hfl_val, List.set_set, sep_comm_l] at hm
                        try rw [sep_emp] at hm
                        c0_hsplit
                        · c0_hsteps!; exact retQ 10#64 fl1 kb hfl1_le hsk hm
                        · clear hc
                          c0_hsteps_nogrp
                          refine wp_while_break_state
                            (brkTs := [i32, i32, i32]) (lpTs := [i32, i32])
                            (fun st : BitVec 32 × BitVec 32 × BitVec 32 =>
                              (st.1, st.2.1, st.2.2, ()))
                            (fun st mp =>
                              (st.2.1 = 0xFFFFFFFF#32 ∨ st.2.1.toNat < nv.toNat) ∧ mp = m)
                            (fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
                            (fun st => nv.toNat - st.2.toNat)
                            (fun st mp => st.2.toNat ≤ nv.toNat ∧ mp = m)
                            ?_ ?_ ?_
                          · rintro _ ⟨cur1, pk1, stp1⟩ mp1 ⟨hpk1, hmp1⟩
                            subst mp1
                            c0_hsteps_nogrp
                            refine wp_join_state (ts := [i32, i32, i32])
                              (α := BitVec 32 × BitVec 32 × BitVec 32)
                              (fun st => (st.1, st.2.1, st.2.2, ()))
                              (fun st mp =>
                                (st.2.1 = 0xFFFFFFFF#32 ∨ st.2.1.toNat < nv.toNat) ∧ mp = m)
                              ?_ ?_
                            · intro _ ⟨c2, pk2, stp2⟩ mp2 ⟨hpk2, hmp2⟩
                              subst mp2
                              c0_hsteps_nogrp
                              refine wp_join_state (ts := [i32, i32])
                                (α := BitVec 32 × BitVec 32) (fun st => (st.1, st.2, ()))
                                (fun st mp =>
                                  (st.2 = 0xFFFFFFFF#32 ∨ st.2.toNat < nv.toNat) ∧ mp = m)
                                ?_ ?_
                              · intro _ ⟨c3, pk3⟩ mp3 ⟨hpk3, hmp3⟩
                                subst mp3
                                c0_hsplit
                                · c0_hsteps!; exact retQ 10#64 fl1 kb hfl1_le hsk hm
                                · have hpk3_lt : pk3.toNat < nv.toNat := by
                                    rcases hpk3 with rfl | hlt
                                    · exact absurd rfl hc
                                    · exact hlt
                                  have h10n : (BitVec.ofNat (OfNat.ofNat 64)
                                      (OfNat.ofNat 10)).toNat = 10 := rfl
                                  have h3n : (BitVec.ofNat (OfNat.ofNat 64)
                                      (OfNat.ofNat 3)).toNat = 3 := rfl
                                  have h416n : (416 : BitVec 32).toNat = 416 := rfl
                                  have hkb10_l : 2912 ≤ (kb.set 10 pk3).length := by
                                    rw [List.length_set]; exact hkb_l
                                  have h416_bd : (BitVec.setWidth 64
                                      ((416 : BitVec 32) + pk3)).toNat <
                                      (kb.set 10 pk3).length := by
                                    rw [bv64_add2_lt (by rw [h416n]; have := hnv_le; omega),
                                      h416n, List.length_set]
                                    have := hnv_le; omega
                                  have hsk10 := solveKeep_of_set hsk 10 pk3 (by decide) (by decide)
                                    (by decide) (by decide) (by decide) (Or.inl (by decide))
                                  c0_hsteps!
                                  try rw [h10n] at hm
                                  try rw [h3n] at hm
                                  try rw [sep_emp] at hm
                                  m7_call hAssign
                                  dsimp only [vals, Arg.val]
                                  refine fullK6AssignM7Spec_intro ?_ hm ?_
                                  · rw [List.length_set, List.length_set]; exact hkb_l
                                  · intro kba ma hlena hkeepa hma
                                    have hska := solveKeep_of_assign
                                      (solveKeep_of_set hsk10 3 _ (by decide) (by decide)
                                        (by decide) (by decide) (by decide) (Or.inl (by decide)))
                                      hlena hkeepa
                                    m7_call hProp
                                    dsimp only [vals, Arg.val]
                                    refine fullK6PropM7Spec_intro hska.1 hma ?_
                                    intro cf' kbp' mp' hokp' hlenp' hp0' hp1' hp2' hp15' _ hmp'
                                    have hskp' := solveKeep_of_prop hska hokp' hlenp'
                                      hp0' hp1' hp2' hp15'
                                    c0_hsteps!
                                    exact ih (cf', fl1, kbp') mp' hfl1_lt ⟨hfl1_le, hskp', hmp'⟩
                              · intro J3 hJ3
                                c0_hsplit
                                · c0_hsteps_nogrp
                                  refine wp_while_break_state
                                    (brkTs := [i32, i32]) (lpTs := [i32])
                                    (fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
                                    (fun st mp =>
                                      (st.2 = 0xFFFFFFFF#32 ∨ st.2.toNat < nv.toNat) ∧ mp = m)
                                    (fun c : BitVec 32 => (c, ()))
                                    (fun c => nv.toNat - c.toNat)
                                    (fun c mp => c.toNat ≤ nv.toNat ∧ mp = m)
                                    ?_ ?_ ?_
                                  · rintro _ ⟨c3, pk3⟩ mp3 ⟨hpk3, hmp3⟩
                                    subst mp3
                                    c0_hsteps!; exact hJ3 (c3, pk3) m ⟨hpk3, rfl⟩
                                  · rintro B3 L3 c3 mp3 hB3 ih3 ⟨hc3_le, hmp3⟩
                                    subst mp3
                                    c0_hsplit
                                    · have hc3_lt : c3.toNat < nv.toNat := hc
                                      obtain ⟨h608_bd, _⟩ := k6_pick_bounds hkb_l hnv_le hc3_lt
                                      c0_hsplit
                                      · c0_hsteps!; exact hB3 (c3, c3) m ⟨Or.inr hc3_lt, rfl⟩
                                      · have hc31 : (c3 + 1#32).toNat = c3.toNat + 1 := by
                                          rw [BitVec.toNat_add,
                                            show (1#32 : BitVec 32).toNat = 1 from rfl,
                                            Nat.mod_eq_of_lt (by have := hnv_le; omega)]
                                        c0_hsteps!
                                        exact ih3 (c3 + 1#32) m (by rw [hc31]; omega)
                                          ⟨by rw [hc31]; omega, rfl⟩
                                    · c0_hsteps!; exact hB3 (c3, pk2) m ⟨hpk2, rfl⟩
                                  · intro B3 L3 _ hL3
                                    c0_hsteps!; exact hL3 0#32 m ⟨Nat.zero_le _, rfl⟩
                                · c0_hsteps!; exact hJ3 (c2, pk2) m ⟨hpk2, rfl⟩
                            · intro J2 hJ2
                              c0_hsplit
                              · c0_hsteps_nogrp
                                refine wp_while_break_state
                                  (brkTs := [i32, i32, i32]) (lpTs := [i32, i32])
                                  (fun st : BitVec 32 × BitVec 32 × BitVec 32 =>
                                    (st.1, st.2.1, st.2.2, ()))
                                  (fun st mp =>
                                    (st.2.1 = 0xFFFFFFFF#32 ∨ st.2.1.toNat < nv.toNat) ∧ mp = m)
                                  (fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
                                  (fun st => nv.toNat - st.2.toNat)
                                  (fun st mp => st.2.toNat ≤ nv.toNat ∧ mp = m)
                                  ?_ ?_ ?_
                                · rintro _ ⟨c2, pk2, stp2⟩ mp2 ⟨hpk2, hmp2⟩
                                  subst mp2
                                  c0_hsteps!; exact hJ2 (c2, pk2, stp2) m ⟨hpk2, rfl⟩
                                · rintro B2 L2 ⟨c2, stp2⟩ mp2 hB2 ih2 ⟨hstp2_le, hmp2⟩
                                  subst mp2
                                  c0_hsplit
                                  · have hc2_lt : c2.toNat < nv.toNat := hc
                                    clear hc
                                    c0_hsplit
                                    · have hstp2_lt : stp2.toNat < nv.toNat := hc
                                      obtain ⟨h608_bd, h160_bd⟩ :=
                                        k6_pick_bounds hkb_l hnv_le hc2_lt
                                      c0_hsplit
                                      · c0_hsteps!
                                        exact hB2 (c2, c2, stp2) m ⟨Or.inr hc2_lt, rfl⟩
                                      · have hstp21 : (stp2 + 1#32).toNat = stp2.toNat + 1 := by
                                          rw [BitVec.toNat_add,
                                            show (1#32 : BitVec 32).toNat = 1 from rfl,
                                            Nat.mod_eq_of_lt (by have := hnv_le; omega)]
                                        let nc2 := kb[(BitVec.setWidth 64
                                          ((160 : BitVec 32) + c2)).toNat]'h160_bd
                                        c0_hsteps!
                                        exact ih2 (nc2, stp2 + 1#32) m
                                          (by dsimp only; rw [hstp21]; omega)
                                          ⟨by dsimp only; rw [hstp21]; omega, rfl⟩
                                    · c0_hsteps!; exact hB2 (c2, pk1, stp2) m ⟨hpk1, rfl⟩
                                  · c0_hsteps!; exact hB2 (c2, pk1, stp2) m ⟨hpk1, rfl⟩
                                · intro B2 L2 _ hL2
                                  c0_hsteps!
                                  exact hL2 (_, 0#32) m ⟨Nat.zero_le _, rfl⟩
                              · c0_hsteps!; exact hJ2 (cur1, pk1, stp1) m ⟨hpk1, rfl⟩
                          · rintro B1 L1 ⟨c1, stp1⟩ mp1 hB1 ih1 ⟨hstp1_le, hmp1⟩
                            subst mp1
                            c0_hsplit
                            · have hc1_lt : c1.toNat < nv.toNat := hc
                              clear hc
                              c0_hsplit
                              · have hstp1_lt : stp1.toNat < nv.toNat := hc
                                obtain ⟨h608_bd, h160_bd⟩ := k6_pick_bounds hkb_l hnv_le hc1_lt
                                c0_hsplit
                                · c0_hsteps!
                                  exact hB1 (c1, c1, stp1) m ⟨Or.inr hc1_lt, rfl⟩
                                · have hstp11 : (stp1 + 1#32).toNat = stp1.toNat + 1 := by
                                    rw [BitVec.toNat_add,
                                      show (1#32 : BitVec 32).toNat = 1 from rfl,
                                      Nat.mod_eq_of_lt (by have := hnv_le; omega)]
                                  let nc1 := kb[(BitVec.setWidth 64
                                    ((160 : BitVec 32) + c1)).toNat]'h160_bd
                                  c0_hsteps!
                                  exact ih1 (nc1, stp1 + 1#32) m
                                    (by dsimp only; rw [hstp11]; omega)
                                    ⟨by dsimp only; rw [hstp11]; omega, rfl⟩
                              · c0_hsteps!
                                exact hB1 (c1, 0xFFFFFFFF#32, stp1) m ⟨Or.inl rfl, rfl⟩
                            · c0_hsteps!
                              exact hB1 (c1, 0xFFFFFFFF#32, stp1) m ⟨Or.inl rfl, rfl⟩
                          · intro B1 L1 _ hL1
                            c0_hsteps!
                            exact hL1 (_, 0#32) m ⟨Nat.zero_le _, rfl⟩
                    · c0_hsteps!; exact retQ 0#64 fl kb hfl_le hsk hmi
                  · c0_hsteps!; exact retQ 0#64 fl kb hfl_le hsk hmi

end

end LeanQbe.T.Examples.Kissat.FullM7BveGates
