module

public import LeanQbe.T.Examples.Kissat.FullM7CongHash
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas1
public import LeanQbe.T.Examples.Kissat.FullM7CongHashProof0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullCongLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Agrees
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave-4 Dynamic Congruence Hash Table Proofs (`FullM7CongHashProof`)

M1-clean verification (`public section`, `0` `@[expose]`, `0` `import all`, `0` `maxHeartbeats`,
`0` `bv_decide`):
1. `M7CongHtCtrlOk` / `M7CongHtInv` invariants and bridges to `FullCongSpecs.CongHtInv`.
2. Parametric `(Γ : Env)` `Func.wp` proofs for all `5` functions (`full_cong_ht_hash_ent_m7`,
   `full_cong_ht_init_m7`, `full_cong_ht_grow_m7`, `full_cong_ht_lookup_m7`,
   `full_cong_ht_insert_m7`) preserving `SafetySlice.spec (fullSafetySlice c)` (`FullState.core`
   + `LengthsOk c`), `FullExtScratchPres`, and prefix `scratch_buf`.
3. Closed `5`-row `m7CongHashSpecTable`, `m7CongHashEnv`, `m7CongHash_moduleOk`, and
   `m7CongHashEnv_noExit`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7CongHash

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open Kraken.Bedrock2.Test

/-! ## 2b. Lookup/Insert Specs & Closed `5`-Row Environment -/

section Specs

/-- **#4 (`full_cong_ht_lookup_m7`)**: read-only linear probe for `(htag, harity, tmp[0..<harity])`,
returning `0xFFFFFFFF#32` or a verified matching gate offset in `scr[ht_off ..< ht_off + ht_sz)`. -/
abbrev m7CongHtLookupSpec : Spec [i64, i64, i32, i32] [i32] :=
  fun (h, ctrl_off, htag, harity, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ ret : BitVec 32,
        (ret = 0xFFFFFFFF#32 ∨
          ∃ ht_off ht_sz k mw,
            M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ht_off ht_sz ∧
            harity.toNat ≤ 31 ∧ harity.toNat ≤ c.max_vars ∧
            k < ht_sz ∧ s.scratch.scratch_buf[ht_off + k]? = some ret ∧
            ret.toNat + 2 + harity.toNat ≤ ht_off ∧
            s.scratch.scratch_buf[ret.toNat + 1]? = some mw ∧
            (mw >>> 28) = htag ∧ (mw &&& 0xFF#32) = harity ∧
            ∀ j < harity.toNat,
              s.scratch.scratch_buf[ret.toNat + 2 + j]? = s.core.tmp[j]?) →
        Q (ret, ()) m

theorem m7CongHtLookupSpec_noExit : ∀ a m Q X,
    m7CongHtLookupSpec a m Q X → m7CongHtLookupSpec a m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

/-- **#5 (`full_cong_ht_insert_m7`)**: inserts gate entry `ent` (auto-growing at 75% load),
returning `ent`, an existing equivalent gate entry, or `0xFFFFFFFF#32` when full/invalid,
while preserving `FullState.core`, `LengthsOk c`, `FullExtScratchPres`, and prefix `scratch_buf`. -/
abbrev m7CongHtInsertSpec : Spec [i64, i64, i32] [i32] :=
  fun (h, ctrl_off, ent, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 32) (scr' : List (BitVec 32)) (rsz' : BitVec 64) (m' : Mem 64),
        let s' : FullState :=
          { s with scratch := { s.scratch with scratch_buf := scr', res_sz := rsz' } }
        scr'.length = c.scratch_cap → s'.LengthsOk c →
        PreservesCoreSlice FullState.core s s' → FullExtScratchPres s s' →
        (rsz' = s.scratch.res_sz ∨ rsz' = s.scratch.res_sz + 1#64) →
        (∀ ht_off old_sz,
          M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ht_off old_sz →
          ∃ new_sz,
            M7CongHtCtrlOk c scr' ctrl_off.toNat ht_off new_sz ∧
            (new_sz = old_sz ∨ new_sz = 2 * old_sz) ∧ new_sz ≤ m7CongHashMaxSz ∧
            (∀ idx < ht_off, idx ≠ ctrl_off.toNat + 7 →
              scr'[idx]? = s.scratch.scratch_buf[idx]?) ∧
            (∀ j < new_sz,
              scr'[ht_off + j]? = some 0xFFFFFFFF#32 ∨
              scr'[ht_off + j]? = some ent ∨
              ∃ k0 < old_sz, ∃ raw : BitVec 32,
                s.scratch.scratch_buf[ht_off + k0]? = some raw ∧
                raw ≠ 0xFFFFFFFF#32 ∧
                (scr'[ht_off + j]? = some raw ∨
                  scr'[ht_off + j]? = some (raw &&& 0x7FFFFFFF#32))) ∧
            (ret = 0xFFFFFFFF#32 →
              ∀ mw : BitVec 32, s.scratch.scratch_buf[ent.toNat + 1]? = some mw →
              (mw &&& 0xFF#32).toNat ≤ 31 →
              ent.toNat + 2 + (mw &&& 0xFF#32).toNat ≤ ht_off →
              ∀ j < new_sz, scr'[ht_off + j]? ≠ some 0xFFFFFFFF#32)) →
        (ret = 0xFFFFFFFF#32 ∨ ret = ent ∨
          ∃ ht_off new_sz k,
            M7CongHtCtrlOk c scr' ctrl_off.toNat ht_off new_sz ∧
            k < new_sz ∧ scr'[ht_off + k]? = some ret ∧ ret.toNat < ht_off) →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

theorem m7CongHtInsertSpec_noExit : ∀ a m Q X,
    m7CongHtInsertSpec a m Q X → m7CongHtInsertSpec a m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

/-- Closed `5`-row specification table for `m7CongHashModule`. -/
abbrev m7CongHashSpecTable : List SpecEntry :=
  [ .ofFn full_cong_ht_hash_ent_m7 m7CongHtHashEntSpec true
  , .ofFn full_cong_ht_init_m7 m7CongHtInitSpec true
  , .ofFn full_cong_ht_grow_m7 m7CongHtGrowSpec true
  , .ofFn full_cong_ht_lookup_m7 m7CongHtLookupSpec true
  , .ofFn full_cong_ht_insert_m7 m7CongHtInsertSpec true ]

/-- Specification environment for `m7CongHashModule` (`0` exits). -/
abbrev m7CongHashEnv : Env :=
  Env.ofTable m7CongHashSpecTable

theorem m7CongHashEnv_noExit :
    ∀ f as bs xs m Q X X',
      m7CongHashEnv f as bs xs m Q X → m7CongHashEnv f as bs xs m Q X' :=
  Env.ofTable_noExit fun e he => by
    simp only [m7CongHashSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;> rfl

end Specs

/-! ## 4b. Lookup & Insert `Func.wp` Proofs -/

section WpProofs

open scoped FullArenaTactics

local macro "m7_omega" : tactic =>
  `(tactic| (
    try simp only [bv64_zext32_toNat,
      show BitVec.toNat (0 : BitVec 64) = 0 from rfl,
      show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
      show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
      show BitVec.toNat (6 : BitVec 64) = 6 from rfl,
      show BitVec.toNat (7 : BitVec 64) = 7 from rfl,
      show BitVec.toNat (8 : BitVec 64) = 8 from rfl,
      show BitVec.toNat (16 : BitVec 64) = 16 from rfl,
      show BitVec.toNat (31 : BitVec 64) = 31 from rfl,
      show BitVec.toNat (131072 : BitVec 64) = 131072 from rfl,
      show BitVec.toNat (2147483647 : BitVec 64) = 2147483647 from rfl] at *
    omega))

/-- **#4 (`full_cong_ht_lookup_m7_wp`)**: read-only linear probe over `scr` and `tmp`. -/
theorem full_cong_ht_lookup_m7_wp (Γ : Env) :
    ∀ a m Q X, m7CongHtLookupSpec a m Q X →
      Func.wp Γ full_cong_ht_lookup_m7_body a m Q X := by
  rintro ⟨h, ctrl_off, htag, harity, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  have hscrl := hlen.scratch_ok.scratch_buf_len
  have htmpl := hlen.core_ok.tmp_len_arr
  unfold Func.wp full_cong_ht_lookup_m7_body
  c0_hsplit
  · c0_hsteps; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
  · have hco_le : ctrl_off.toNat ≤ c.scratch_cap := by m7_omega
    clear hc; c0_hsplit
    · c0_hsteps; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
    · have hco8 : ctrl_off.toNat + 8 ≤ c.scratch_cap := by
        have := ctrl_off.isLt; m7_omega
      clear hc; c0_hsplit
      · c0_hsteps; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
      · have hha31 : harity.toNat ≤ 31 := by m7_omega
        clear hc; c0_hsplit
        · c0_hsteps; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
        · have hha_mv : harity.toNat ≤ c.max_vars := by m7_omega
          clear hc
          have h6n : (ctrl_off + 6#64).toNat = ctrl_off.toNat + 6 :=
            bv64_add_ofNat_toNat 6 (by decide) (by omega)
          have h7n : (ctrl_off + 7#64).toNat = ctrl_off.toNat + 7 :=
            bv64_add_ofNat_toNat 7 (by decide) (by omega)
          have hco6_arr : (ctrl_off + 6#64).toNat < s.scratch.scratch_buf.length := by
            rw [h6n]; omega
          have hco7_arr : (ctrl_off + 7#64).toNat < s.scratch.scratch_buf.length := by
            rw [h7n]; omega
          let ht_off_w := s.scratch.scratch_buf[ctrl_off.toNat + 6]'(by omega)
          let ht_sz_w := s.scratch.scratch_buf[ctrl_off.toNat + 7]'(by omega)
          let ht_off : BitVec 64 := ht_off_w.setWidth 64
          let ht_sz : BitVec 64 := ht_sz_w.setWidth 64
          have hht_nat : ht_off_w.toNat = ht_off.toNat := (bv64_zext32_toNat _).symm
          have hsz_nat : ht_sz_w.toNat = ht_sz.toNat := (bv64_zext32_toNat _).symm
          have hho_eq : ht_off =
              (s.scratch.scratch_buf[ctrl_off.toNat + 6]'(by omega)).setWidth 64 := rfl
          have hsz_eq : ht_sz =
              (s.scratch.scratch_buf[ctrl_off.toNat + 7]'(by omega)).setWidth 64 := rfl
          have hs6a : s.scratch.scratch_buf[(BitVec.toNat ctrl_off +
              BitVec.toNat (6 : BitVec 64)) % 2 ^ 64]'(by
              change (ctrl_off.toNat + 6) % 2 ^ 64 < s.scratch.scratch_buf.length
              rw [Nat.mod_eq_of_lt (by omega)]; omega) = ht_off_w :=
            scr_idx_add_imm 6 rfl (by omega) _ _
          have hs6b : s.scratch.scratch_buf[(ctrl_off + (6 : BitVec 64)).toNat]'(by
              change (ctrl_off.toNat + 6) % 2 ^ 64 < s.scratch.scratch_buf.length
              rw [Nat.mod_eq_of_lt (by omega)]; omega) = ht_off_w := hs6a
          have hs7a : s.scratch.scratch_buf[(BitVec.toNat ctrl_off +
              BitVec.toNat (7 : BitVec 64)) % 2 ^ 64]'(by
              change (ctrl_off.toNat + 7) % 2 ^ 64 < s.scratch.scratch_buf.length
              rw [Nat.mod_eq_of_lt (by omega)]; omega) = ht_sz_w :=
            scr_idx_add_imm 7 rfl (by omega) _ _
          have hs7b : s.scratch.scratch_buf[(ctrl_off + (7 : BitVec 64)).toNat]'(by
              change (ctrl_off.toNat + 7) % 2 ^ 64 < s.scratch.scratch_buf.length
              rw [Nat.mod_eq_of_lt (by omega)]; omega) = ht_sz_w := hs7a
          c0_hsplit
          · c0_hsteps; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
          · have h1 : ctrl_off.toNat + 8 ≤ ht_off.toNat := by
              rw [hs6a, hht_nat] at hc
              change ¬ ht_off.toNat < (ctrl_off.toNat + BitVec.toNat 8) % 2 ^ 64 at hc
              m7_omega
            clear hc; c0_hsplit
            · c0_hsteps; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
            · have h2 : ht_off.toNat < c.scratch_cap := by
                rw [hs6a, hht_nat] at hc
                change ¬ c.scratch_cap % 2 ^ 64 ≤ ht_off.toNat at hc; m7_omega
              clear hc; c0_hsplit
              · c0_hsteps; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
              · have h3 : ht_off.toNat ≤ 0x7FFFFFFF := by
                  rw [hs6a, hht_nat] at hc
                  change ¬ BitVec.toNat 2147483647 < ht_off.toNat at hc; m7_omega
                clear hc; c0_hsplit
                · c0_hsteps; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
                · have h4 : 16 ≤ ht_sz.toNat := by
                    rw [hs7a, hsz_nat] at hc
                    change ¬ ht_sz.toNat < BitVec.toNat 16 at hc; m7_omega
                  clear hc; c0_hsplit
                  · c0_hsteps; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
                  · have hmax : ht_sz.toNat ≤ 131072 := by
                      rw [hs7a, hsz_nat] at hc
                      change ¬ BitVec.toNat 131072 < ht_sz.toNat at hc; m7_omega
                    clear hc; c0_hsplit
                    · c0_hsteps; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
                    · have h5 : (ht_sz &&& (ht_sz - 1#64)) = 0#64 := by
                        rw [hs7a] at hc; exact hc
                      clear hc; c0_hsplit
                      · c0_hsteps; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
                      · have h6 : ht_sz.toNat ≤ c.scratch_cap - ht_off.toNat := by
                          rw [hs6a, hht_nat, hs7a, hsz_nat] at hc
                          change ¬ (2 ^ 64 - ht_off.toNat + c.scratch_cap) % 2 ^ 64 <
                            ht_sz.toNat at hc
                          have := ht_off.isLt; m7_omega
                        clear hc
                        have hctrl_ok : M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat
                            ht_off.toNat ht_sz.toNat :=
                          m7CongHtCtrlOk_from_reads hscrl hco8 hho_eq hsz_eq h1 h2 h3 h4 h5 h6 hmax
                        c0_hsteps_nogrp
                        refine wp_loop_inv (ts := [i64, i64])
                          (fun ⟨_, hi, ⟨⟩⟩ mi => mi = m0 ∧ hi.toNat ≤ harity.toNat)
                          (fun ⟨_, hi, ⟨⟩⟩ _ => harity.toNat - hi.toNat)
                          (fun J hJ => by
                            c0_hsteps; exact hJ (_, 0#64, ()) m0 ⟨rfl, Nat.zero_le _⟩)
                          (fun J ⟨hv, hi, ⟨⟩⟩ mi ⟨hmi, hi_le⟩ ih => ?_)
                        subst mi
                        c0_hsplit
                        · have hi_lt : hi.toNat < harity.toNat := by m7_omega
                          have hi_tmp : hi.toNat < s.core.tmp.length := by omega
                          have hi1_n : (hi + 1#64).toNat = hi.toNat + 1 :=
                            bv64_add1_lt hi_lt (by omega)
                          c0_hsteps
                          exact ih (_, hi + 1#64, ()) m0 (by dsimp only; omega) ⟨rfl, by omega⟩
                        · clear hc; c0_hsteps_nogrp
                          refine wp_loop_inv (ts := [i64, i64])
                            (fun ⟨slot, p, ⟨⟩⟩ mp => mp = m0 ∧ slot.toNat < ht_sz.toNat ∧
                              p.toNat ≤ ht_sz.toNat)
                            (fun ⟨_, p, ⟨⟩⟩ _ => ht_sz.toNat - p.toNat)
                            (fun Jp hJp => by
                              c0_hsteps; try simp only [hs7b]
                              exact hJp (hv &&& (ht_sz - 1#64), 0#64, ()) m0
                                ⟨rfl, bv64_and_sub1_lt (by omega), Nat.zero_le _⟩)
                            (fun Jp ⟨slot, p, ⟨⟩⟩ mp ⟨hmp, hslot_lt, hp_le⟩ ihp => ?_)
                          subst mp
                          c0_hsplit
                          · have hp_lt : p.toNat < ht_sz.toNat := by
                              rw [hs7a, hsz_nat] at hc; exact hc
                            have hsl_add_n : (ht_off + slot).toNat =
                                ht_off.toNat + slot.toNat := bv64_add_toNat (by omega)
                            have hsl_arr :
                                (ht_off + slot).toNat < s.scratch.scratch_buf.length := by
                              rw [hsl_add_n]; omega
                            let ent := s.scratch.scratch_buf[(ht_off + slot).toNat]'hsl_arr
                            have hent_get : s.scratch.scratch_buf[ht_off.toNat + slot.toNat]? =
                                some ent := by
                              rw [List.getElem?_eq_getElem (by rw [hscrl]; omega)]
                              congr 1; exact (list_getElem_congr hsl_add_n hsl_arr _).symm
                            have hent_lt : ent.toNat < 2 ^ 32 := ent.isLt
                            clear hc; c0_hsplit
                            · c0_hsteps; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
                            · have hent_ne : ent ≠ 0xFFFFFFFF#32 := by
                                simp only [hs6a, hht_nat] at hc; exact hc
                              clear hc; c0_hsteps_nogrp
                              have hp1_n : (p + 1#64).toNat = p.toNat + 1 :=
                                bv64_add1_lt hp_lt (by omega)
                              refine wp_join0 (fun m2 => m2 = m0)
                                (fun _ m2 hm2 => by
                                  subst m2; c0_hsteps; try simp only [hs7b]
                                  exact ihp ((slot + 1#64) &&& (ht_sz - 1#64), p + 1#64, ()) m0
                                    (by dsimp only; omega)
                                    ⟨rfl, bv64_and_sub1_lt (by omega), by omega⟩)
                                (fun J2 hJ2 => ?_)
                              have hent_hc : s.scratch.scratch_buf[(ht_off.toNat +
                                  BitVec.toNat slot) % 2 ^ 64]'(by
                                  rw [hscrl, Nat.mod_eq_of_lt (by omega)]; omega) = ent := rfl
                              c0_hsplit
                              · have hfit_ent : ent.toNat + 2 + harity.toNat ≤ ht_off.toNat := by
                                  simp only [hs6a, hht_nat, hent_hc] at hc
                                  have h2n : BitVec.toNat (2 : BitVec 64) = 2 := rfl
                                  have hmod : (ent.toNat + BitVec.toNat (2 : BitVec 64) +
                                      harity.toNat) % 2 ^ 64 = ent.toNat + 2 + harity.toNat := by
                                    rw [h2n, Nat.mod_eq_of_lt (by m7_omega)]
                                  rw [hmod] at hc; exact hc
                                have he1_arr : (ent.setWidth 64 + 1#64).toNat <
                                    s.scratch.scratch_buf.length := by
                                  rw [bv64_zext32_add_ofNat ent 1 (by decide), hscrl]; omega
                                let mw :=
                                  s.scratch.scratch_buf[(ent.setWidth 64 + 1#64).toNat]'he1_arr
                                have hmw_get : s.scratch.scratch_buf[ent.toNat + 1]? = some mw := by
                                  rw [List.getElem?_eq_getElem (by rw [hscrl]; omega)]
                                  congr 1; exact (list_getElem_congr
                                    (bv64_zext32_add_ofNat ent 1 (by decide)) he1_arr _).symm
                                have hmw_congr : s.scratch.scratch_buf[(ent.toNat +
                                    BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                                    change (ent.toNat + 1) % 2 ^ 64 < s.scratch.scratch_buf.length
                                    rw [Nat.mod_eq_of_lt (by omega), hscrl]; omega) = mw :=
                                  (scr_idx_zext32_add1 (e := ent) (by rw [hscrl]; omega) _).trans
                                    (list_getElem_congr
                                      (bv64_zext32_add_ofNat ent 1 (by decide)).symm
                                      (by rw [hscrl]; omega) he1_arr)
                                have h6' :
                                    (ctrl_off + (6 : BitVec 64)).toNat = ctrl_off.toNat + 6 :=
                                  h6n
                                have h_ent_raw :
                                    s.scratch.scratch_buf[(BitVec.setWidth 64
                                      (s.scratch.scratch_buf[(ctrl_off + (6 : BitVec 64)).toNat]'
                                        (by rw [hscrl, h6']; omega)) + slot).toNat]'
                                      (by simp only [hs6b]; exact hsl_arr) = ent := by
                                  simp only [hs6b]; rfl
                                clear hc; try rw [h_ent_raw]
                                c0_hsteps_nogrp
                                refine wp_join0 (fun m3 => m3 = m0) ?_ (fun J3 hJ3 => ?_)
                                · rintro _ m3 hm3; subst m3; c0_hsteps; exact hJ2 m0 rfl
                                c0_hsplit
                                · have htag_eq : (mw >>> 28) = htag := by
                                    try simp only [hs6a, hht_nat] at hc
                                    change (s.scratch.scratch_buf[(ent.toNat +
                                        BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                                        change (ent.toNat + 1) % 2 ^ 64 <
                                          s.scratch.scratch_buf.length
                                        rw [Nat.mod_eq_of_lt (by omega), hscrl]; omega) >>>
                                      OfNat.ofNat 28) = htag at hc
                                    rw [hmw_congr] at hc; exact hc
                                  clear hc; c0_hsplit
                                  · have har_eq : (mw &&& 0xFF#32) = harity := by
                                      try simp only [hs6a, hht_nat] at hc
                                      change (s.scratch.scratch_buf[(ent.toNat +
                                          BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                                          change (ent.toNat + 1) % 2 ^ 64 <
                                            s.scratch.scratch_buf.length
                                          rw [Nat.mod_eq_of_lt (by omega), hscrl]; omega) &&&
                                        255#32) = harity at hc
                                      rw [hmw_congr] at hc; exact hc
                                    clear hc; c0_hsteps_nogrp
                                    refine wp_loop_break_group (brkTs := [i32, i64])
                                      (lpTs := [i64])
                                      (fun (eq_b, _kb, ()) mb => mb = m0 ∧
                                        (eq_b ≠ 0#32 → ∀ j < harity.toNat,
                                          s.scratch.scratch_buf[ent.toNat + 2 + j]? =
                                            s.core.tmp[j]?))
                                      (fun rem (k, ()) mk => mk = m0 ∧ k.toNat ≤ harity.toNat ∧
                                        rem = harity.toNat - k.toNat ∧
                                        ∀ j < k.toNat,
                                          s.scratch.scratch_buf[ent.toNat + 2 + j]? =
                                            s.core.tmp[j]?)
                                      ?_ ?_ ?_
                                    · rintro _ ⟨eq_b, kb, ⟨⟩⟩ mb ⟨hmb, heq_ok⟩; subst mb
                                      c0_hsplit
                                      · have hne0 : eq_b ≠ 0#32 := hc
                                        c0_hsteps
                                        exact hQ ent (Or.inr ⟨ht_off.toNat, ht_sz.toNat, slot.toNat,
                                          mw, hctrl_ok, hha31, hha_mv, hslot_lt, hent_get, hfit_ent,
                                          hmw_get, htag_eq, har_eq, heq_ok hne0⟩)
                                      · c0_hsteps; exact hJ3 m0 rfl
                                    · rintro Bk Lk rem ⟨k, ⟨⟩⟩ mk hBk hLk
                                        ⟨hmk, hk_le, rfl, hpre_k⟩; subst mk
                                      c0_hsplit
                                      · have hk_lt : k.toNat < harity.toNat := by m7_omega
                                        have he2k_n : (ent.setWidth 64 + 2#64 + k).toNat =
                                            ent.toNat + 2 + k.toNat := by
                                          have h12 := bv64_zext32_add_ofNat ent 2 (by decide)
                                          rw [bv64_add_toNat (by rw [h12]; omega), h12]
                                        have he2k_arr : (ent.setWidth 64 + 2#64 + k).toNat <
                                            s.scratch.scratch_buf.length := by
                                          rw [he2k_n, hscrl]; omega
                                        have hk_tmp : k.toNat < s.core.tmp.length := by omega
                                        have hk1_n : (k + 1#64).toNat = k.toNat + 1 :=
                                          bv64_add1_lt hk_lt (by omega)
                                        clear hc; c0_hsplit
                                        · c0_hsteps; exact hBk (0#32, k, ()) m0
                                            ⟨rfl, fun h => absurd rfl h⟩
                                        · try simp only [hs6a, hht_nat] at hc
                                          have he2k_mod :
                                              (ent.toNat + BitVec.toNat (2 : BitVec 64) +
                                              k.toNat) % 2 ^ 64 =
                                              (ent.setWidth 64 + 2#64 + k).toNat := by
                                            rw [he2k_n]
                                            have h2n : BitVec.toNat (2 : BitVec 64) = 2 := rfl
                                            rw [h2n, Nat.mod_eq_of_lt (by omega)]
                                          have hsame : s.scratch.scratch_buf[(ent.setWidth 64 +
                                              2#64 + k).toNat]'he2k_arr =
                                              s.core.tmp[k.toNat]'hk_tmp :=
                                            (list_getElem_congr he2k_mod.symm he2k_arr
                                              (by rw [he2k_mod]; exact he2k_arr)).trans hc
                                          c0_hsteps; refine hLk (harity.toNat - (k + 1#64).toNat)
                                            (k + 1#64, ()) m0 (by omega)
                                            ⟨rfl, by omega, rfl, fun j hj => ?_⟩
                                          rw [hk1_n] at hj
                                          by_cases hjk : j = k.toNat
                                          · subst hjk
                                            rw [List.getElem?_eq_getElem (by rw [hscrl]; omega),
                                              List.getElem?_eq_getElem hk_tmp, ← hsame]
                                            congr 1
                                            exact (list_getElem_congr he2k_n he2k_arr
                                              (by rw [hscrl]; omega)).symm
                                          · exact hpre_k j (by omega)
                                      · have hk_eq : k.toNat = harity.toNat := by m7_omega
                                        rw [hk_eq] at hpre_k
                                        c0_hsteps; exact hBk (1#32, k, ()) m0 ⟨rfl, fun _ => hpre_k⟩
                                    · intro _ Lk _ hLk; c0_hsteps
                                      exact hLk harity.toNat (0#64, ()) m0
                                        ⟨rfl, Nat.zero_le _, rfl, fun _ h => by simp at h⟩
                                  · c0_hsteps; exact hJ3 m0 rfl
                                · c0_hsteps; exact hJ3 m0 rfl
                              · c0_hsteps; exact hJ2 m0 rfl
                          · c0_hsteps; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)

/-- **#5 (`full_cong_ht_insert_m7_wp`)**: inserts gate `ent` with auto-grow at 75% load. -/
theorem full_cong_ht_insert_m7_wp (Γ : Env)
    (hGrow : ∀ a m Q X, m7CongHtGrowSpec a m Q X →
      Γ "full_cong_ht_grow_m7" [i64, i64] [i64] a m Q X)
    (hHashEnt : ∀ a m Q X, m7CongHtHashEntSpec a m Q X →
      Γ "full_cong_ht_hash_ent_m7" [i64, i32, i64] [i64] a m Q X) :
    ∀ a m Q X, m7CongHtInsertSpec a m Q X →
      Func.wp Γ full_cong_ht_insert_m7_body a m Q X := by
  rintro ⟨h, ctrl_off, ent, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen, hm0, hQ⟩
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hscrl := hlen.scratch_ok.scratch_buf_len
  have hent_lt : ent.toNat < 2 ^ 32 := ent.isLt
  have hfail_noctrl : (∀ ho os, M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ho os →
      False) →
      Q (0xFFFFFFFF#32, ()) m0 := fun hno =>
    hQ 0xFFFFFFFF#32 s.scratch.scratch_buf s.scratch.res_sz m0 hscrl hlen rfl ⟨rfl, rfl⟩
      (Or.inl rfl) (fun ho os h => False.elim (hno ho os h)) (Or.inl rfl) hm0
  unfold Func.wp full_cong_ht_insert_m7_body
  c0_hsplit
  · c0_hsteps; exact hfail_noctrl (fun _ _ hok => by
      have := hok.2.1; have := hok.2.2.1; m7_omega)
  · have hco_le : ctrl_off.toNat ≤ c.scratch_cap := by m7_omega
    clear hc; c0_hsplit
    · c0_hsteps; exact hfail_noctrl (fun _ _ hok => by
        have := ctrl_off.isLt; have := hok.2.1; have := hok.2.2.1; m7_omega)
    · have hco8 : ctrl_off.toNat + 8 ≤ c.scratch_cap := by
        have := ctrl_off.isLt; m7_omega
      clear hc
      let ht_off_w := s.scratch.scratch_buf[ctrl_off.toNat + 6]'(by omega)
      let old_sz_w := s.scratch.scratch_buf[ctrl_off.toNat + 7]'(by omega)
      let ht_off : BitVec 64 := ht_off_w.setWidth 64
      let old_sz : BitVec 64 := old_sz_w.setWidth 64
      have hht_nat : ht_off_w.toNat = ht_off.toNat := (bv64_zext32_toNat _).symm
      have hos_nat : old_sz_w.toNat = old_sz.toNat := (bv64_zext32_toNat _).symm
      have hho_eq : ht_off =
          (s.scratch.scratch_buf[ctrl_off.toNat + 6]'(by omega)).setWidth 64 := rfl
      have hsz_eq : old_sz =
          (s.scratch.scratch_buf[ctrl_off.toNat + 7]'(by omega)).setWidth 64 := rfl
      have hs6a : s.scratch.scratch_buf[(BitVec.toNat ctrl_off +
          BitVec.toNat (6 : BitVec 64)) % 2 ^ 64]'(by
          change (ctrl_off.toNat + 6) % 2 ^ 64 < s.scratch.scratch_buf.length
          rw [Nat.mod_eq_of_lt (by omega)]; omega) = ht_off_w :=
        scr_idx_add_imm 6 rfl (by omega) _ _
      have hs6b : s.scratch.scratch_buf[(ctrl_off + (6 : BitVec 64)).toNat]'(by
          change (ctrl_off.toNat + 6) % 2 ^ 64 < s.scratch.scratch_buf.length
          rw [Nat.mod_eq_of_lt (by omega)]; omega) = ht_off_w := hs6a
      have hs7a : s.scratch.scratch_buf[(BitVec.toNat ctrl_off +
          BitVec.toNat (7 : BitVec 64)) % 2 ^ 64]'(by
          change (ctrl_off.toNat + 7) % 2 ^ 64 < s.scratch.scratch_buf.length
          rw [Nat.mod_eq_of_lt (by omega)]; omega) = old_sz_w :=
        scr_idx_add_imm 7 rfl (by omega) _ _
      have hs7b : s.scratch.scratch_buf[(ctrl_off + (7 : BitVec 64)).toNat]'(by
          change (ctrl_off.toNat + 7) % 2 ^ 64 < s.scratch.scratch_buf.length
          rw [Nat.mod_eq_of_lt (by omega)]; omega) = old_sz_w := hs7a
      have hbad_ht : ¬ (ctrl_off.toNat + 8 ≤ ht_off.toNat ∧ ht_off.toNat < c.scratch_cap ∧
          ht_off.toNat ≤ 0x7FFFFFFF) →
          ∀ ho os, M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ho os → False :=
        fun hbad ho os hok => by
          apply hbad
          obtain ⟨rfl, rfl⟩ := m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
          exact ⟨hok.2.1, Nat.lt_of_lt_of_le (by
              have ⟨k, _, he⟩ := hok.2.2.2.2.1; have := Nat.two_pow_pos k; omega) hok.2.2.1,
            hok.2.2.2.1⟩
      c0_hsplit
      · c0_hsteps; exact hfail_noctrl (hbad_ht fun ⟨h1, _⟩ => by
          rw [hs6a, hht_nat] at hc
          change ht_off.toNat < (ctrl_off.toNat + BitVec.toNat 8) % 2 ^ 64 at hc; m7_omega)
      · have h1 : ctrl_off.toNat + 8 ≤ ht_off.toNat := by
          rw [hs6a, hht_nat] at hc
          change ¬ ht_off.toNat < (ctrl_off.toNat + BitVec.toNat 8) % 2 ^ 64 at hc; m7_omega
        clear hc; c0_hsplit
        · c0_hsteps; exact hfail_noctrl (hbad_ht fun ⟨_, h2, _⟩ => by
            rw [hs6a, hht_nat] at hc
            change c.scratch_cap % 2 ^ 64 ≤ ht_off.toNat at hc; m7_omega)
        · have h2 : ht_off.toNat < c.scratch_cap := by
            rw [hs6a, hht_nat] at hc
            change ¬ c.scratch_cap % 2 ^ 64 ≤ ht_off.toNat at hc; m7_omega
          clear hc; c0_hsplit
          · c0_hsteps; exact hfail_noctrl (hbad_ht fun ⟨_, _, h3⟩ => by
              rw [hs6a, hht_nat] at hc
              change BitVec.toNat 2147483647 < ht_off.toNat at hc; m7_omega)
          · have h3 : ht_off.toNat ≤ 0x7FFFFFFF := by
              rw [hs6a, hht_nat] at hc
              change ¬ BitVec.toNat 2147483647 < ht_off.toNat at hc; m7_omega
            clear hc
            have hbad_sz : ¬ (16 ≤ old_sz.toNat ∧ old_sz.toNat ≤ 131072 ∧
                (old_sz &&& (old_sz - 1#64)) = 0#64 ∧
                old_sz.toNat ≤ c.scratch_cap - ht_off.toNat) →
                ∀ ho os, M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ho os → False :=
              fun hbad ho os hok => by
                apply hbad
                obtain ⟨rfl, rfl⟩ := m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                obtain ⟨k, hk, he⟩ := hok.2.2.2.2.1
                refine ⟨by rw [he]; have := Nat.two_pow_pos k; omega,
                  by rw [he]; exact pow2_16_mul_le k hk,
                  bv64_pow2_and_sub1_zero hk he,
                  by have := hok.2.2.1; omega⟩
            c0_hsplit
            · c0_hsteps; exact hfail_noctrl (hbad_sz fun ⟨h4, _⟩ => by
                rw [hs7a, hos_nat] at hc
                change old_sz.toNat < BitVec.toNat 16 at hc; m7_omega)
            · have h4 : 16 ≤ old_sz.toNat := by
                rw [hs7a, hos_nat] at hc
                change ¬ old_sz.toNat < BitVec.toNat 16 at hc; m7_omega
              clear hc; c0_hsplit
              · c0_hsteps; exact hfail_noctrl (hbad_sz fun ⟨_, hm, _⟩ => by
                  rw [hs7a, hos_nat] at hc
                  change BitVec.toNat 131072 < old_sz.toNat at hc; m7_omega)
              · have hmax : old_sz.toNat ≤ 131072 := by
                  rw [hs7a, hos_nat] at hc
                  change ¬ BitVec.toNat 131072 < old_sz.toNat at hc; m7_omega
                clear hc; c0_hsplit
                · c0_hsteps; exact hfail_noctrl (hbad_sz fun ⟨_, _, h5, _⟩ => by
                    rw [hs7a] at hc; exact hc h5)
                · have h5 : (old_sz &&& (old_sz - 1#64)) = 0#64 := by
                    rw [hs7a] at hc; exact hc
                  clear hc; c0_hsplit
                  · c0_hsteps; exact hfail_noctrl (hbad_sz fun ⟨_, _, _, h6⟩ => by
                      rw [hs6a, hht_nat, hs7a, hos_nat] at hc
                      change (2 ^ 64 - ht_off.toNat + c.scratch_cap) % 2 ^ 64 <
                        old_sz.toNat at hc
                      have := ht_off.isLt; m7_omega)
                  · have h6 : old_sz.toNat ≤ c.scratch_cap - ht_off.toNat := by
                      rw [hs6a, hht_nat, hs7a, hos_nat] at hc
                      change ¬ (2 ^ 64 - ht_off.toNat + c.scratch_cap) % 2 ^ 64 <
                        old_sz.toNat at hc
                      have := ht_off.isLt; m7_omega
                    clear hc
                    have hok_read : M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat
                        ht_off.toNat old_sz.toNat :=
                      m7CongHtCtrlOk_from_reads hscrl hco8 hho_eq hsz_eq h1 h2 h3 h4 h5 h6 hmax
                    have horig_id : ∀ j < old_sz.toNat,
                        s.scratch.scratch_buf[ht_off.toNat + j]? = some 0xFFFFFFFF#32 ∨
                        s.scratch.scratch_buf[ht_off.toNat + j]? = some ent ∨
                        ∃ k0 < old_sz.toNat, ∃ raw : BitVec 32,
                          s.scratch.scratch_buf[ht_off.toNat + k0]? = some raw ∧
                          raw ≠ 0xFFFFFFFF#32 ∧
                          (s.scratch.scratch_buf[ht_off.toNat + j]? = some raw ∨
                            s.scratch.scratch_buf[ht_off.toNat + j]? =
                              some (raw &&& 0x7FFFFFFF#32)) := by
                      intro j hj
                      by_cases hem : s.scratch.scratch_buf[ht_off.toNat + j]? = some 0xFFFFFFFF#32
                      · left; exact hem
                      · right; right
                        have hlt : ht_off.toNat + j < s.scratch.scratch_buf.length := by omega
                        refine ⟨j, hj, s.scratch.scratch_buf[ht_off.toNat + j]'hlt,
                          List.getElem?_eq_getElem hlt, ?_, Or.inl (List.getElem?_eq_getElem hlt)⟩
                        intro he; apply hem; rw [List.getElem?_eq_getElem hlt, he]
                    c0_hsplit
                    · c0_hsteps; refine hQ 0xFFFFFFFF#32 s.scratch.scratch_buf s.scratch.res_sz m0
                        hscrl hlen rfl ⟨rfl, rfl⟩ (Or.inl rfl) (fun ho os hok => ?_) (Or.inl rfl)
                        hm0
                      obtain ⟨rfl, rfl⟩ := m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                      refine ⟨old_sz.toNat, hok_read, Or.inl rfl, hmax, fun _ _ _ => rfl,
                        horig_id, fun _ _ _ _ hbad => by
                          rw [hs6a, hht_nat] at hc
                          rw [Nat.mod_eq_of_lt (by m7_omega)] at hc; m7_omega⟩
                    · have he2_le : ent.toNat + 2 ≤ ht_off.toNat := by
                        rw [hs6a, hht_nat] at hc
                        rw [Nat.mod_eq_of_lt (by m7_omega)] at hc; m7_omega
                      have he1_arr : (ent.setWidth 64 + 1#64).toNat <
                          s.scratch.scratch_buf.length := by
                        rw [bv64_zext32_add_ofNat ent 1 (by decide)]; omega
                      let mw := s.scratch.scratch_buf[ent.toNat + 1]'(by omega)
                      have hmw_get : s.scratch.scratch_buf[ent.toNat + 1]? = some mw :=
                        List.getElem?_eq_getElem (by omega)
                      have hs_e1 : s.scratch.scratch_buf[(BitVec.toNat ent +
                          BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                          change (ent.toNat + 1) % 2 ^ 64 < s.scratch.scratch_buf.length
                          rw [Nat.mod_eq_of_lt (by omega)]; omega) = mw :=
                        scr_idx_zext32_add1 (by omega) _
                      let etag := mw >>> 28
                      let earity := mw &&& 0xFF#32
                      let ea : BitVec 64 := earity.setWidth 64
                      clear hc; c0_hsplit
                      · c0_hsteps; refine hQ 0xFFFFFFFF#32 s.scratch.scratch_buf s.scratch.res_sz m0
                          hscrl hlen rfl ⟨rfl, rfl⟩ (Or.inl rfl) (fun ho os hok => ?_) (Or.inl rfl)
                          hm0
                        obtain ⟨rfl, rfl⟩ := m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                        refine ⟨old_sz.toNat, hok_read, Or.inl rfl, hmax, fun _ _ _ => rfl,
                          horig_id, fun _ mw' hmw' h31 => by
                            rw [hmw_get, Option.some.injEq] at hmw'; subst hmw'
                            rw [hs_e1] at hc
                            have h255 : (mw &&& (255 : BitVec 32)) = (mw &&& 0xFF#32) := rfl
                            change (31 : Nat) < (mw &&& (255 : BitVec 32)).toNat at hc
                            rw [h255] at hc; omega⟩
                      · have hea31 : ea.toNat ≤ 31 := by
                          rw [hs_e1] at hc
                          have h255 : (mw &&& (255 : BitVec 32)) = (mw &&& 0xFF#32) := rfl
                          have hhc : ¬ (31 : Nat) < (mw &&& (255 : BitVec 32)).toNat := hc
                          rw [h255] at hhc
                          dsimp only [ea, earity]; rw [bv64_zext32_toNat]
                          exact Nat.not_lt.mp hhc
                        clear hc; c0_hsplit
                        · c0_hsteps
                          refine hQ 0xFFFFFFFF#32 s.scratch.scratch_buf s.scratch.res_sz m0
                            hscrl hlen rfl ⟨rfl, rfl⟩ (Or.inl rfl) (fun ho os hok => ?_)
                            (Or.inl rfl) hm0
                          obtain ⟨rfl, rfl⟩ :=
                            m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                          refine ⟨old_sz.toNat, hok_read, Or.inl rfl, hmax, fun _ _ _ => rfl,
                            horig_id, fun _ mw' hmw' _ hbd => by
                              rw [hmw_get, Option.some.injEq] at hmw'; subst hmw'
                              rw [hs6a, hht_nat, hs_e1] at hc
                              have hlt : ht_off.toNat < ent.toNat + 2 + (mw &&& 0xFF#32).toNat := by
                                have h255 : (mw &&& (255 : BitVec 32)) = (mw &&& 0xFF#32) := rfl
                                have h2n : BitVec.toNat (2 : BitVec 64) = 2 := rfl
                                have hmod : (ent.toNat + BitVec.toNat (2 : BitVec 64) +
                                    (mw &&& (255 : BitVec 32)).toNat) % 2 ^ 64 =
                                    ent.toNat + 2 + (mw &&& 0xFF#32).toNat := by
                                  rw [h2n, h255, Nat.mod_eq_of_lt (by omega)]
                                change ht_off.toNat < (ent.toNat + BitVec.toNat (2 : BitVec 64) +
                                    (mw &&& (255 : BitVec 32)).toNat) % 2 ^ 64 at hc
                                rwa [hmod] at hc
                              omega⟩
                        · have hea_fit : ent.toNat + 2 + ea.toNat ≤ ht_off.toNat := by
                            rw [hs6a, hht_nat, hs_e1] at hc
                            have h255 : (mw &&& (255 : BitVec 32)) = (mw &&& 0xFF#32) := rfl
                            have h2n : BitVec.toNat (2 : BitVec 64) = 2 := rfl
                            have hmod : (ent.toNat + BitVec.toNat (2 : BitVec 64) +
                                (mw &&& (255 : BitVec 32)).toNat) % 2 ^ 64 =
                                ent.toNat + 2 + ea.toNat := by
                              dsimp only [ea, earity]; rw [h2n, h255, bv64_zext32_toNat]
                              exact Nat.mod_eq_of_lt (by omega)
                            change ¬ ht_off.toNat < (ent.toNat + BitVec.toNat (2 : BitVec 64) +
                                (mw &&& (255 : BitVec 32)).toNat) % 2 ^ 64 at hc
                            rw [hmod] at hc; exact Nat.not_lt.mp hc
                          clear hc; c0_hsteps_nogrp
                          refine wp_join_group (ts := [i64])
                            (fun (ht_sz1, ()) m1 => ∃ scr1 : List (BitVec 32),
                              scr1.length = c.scratch_cap ∧
                              M7CongHtCtrlOk c scr1 ctrl_off.toNat ht_off.toNat ht_sz1.toNat ∧
                              (ht_sz1.toNat = old_sz.toNat ∨ ht_sz1.toNat = 2 * old_sz.toNat) ∧
                              ht_sz1.toNat ≤ m7CongHashMaxSz ∧
                              (∀ idx < ht_off.toNat, idx ≠ ctrl_off.toNat + 7 →
                                scr1[idx]? = s.scratch.scratch_buf[idx]?) ∧
                              (∀ j < ht_sz1.toNat,
                                scr1[ht_off.toNat + j]? = some 0xFFFFFFFF#32 ∨
                                ∃ k0 < old_sz.toNat, ∃ raw : BitVec 32,
                                  s.scratch.scratch_buf[ht_off.toNat + k0]? = some raw ∧
                                  raw ≠ 0xFFFFFFFF#32 ∧
                                  (scr1[ht_off.toNat + j]? = some raw ∨
                                    scr1[ht_off.toNat + j]? = some (raw &&& 0x7FFFFFFF#32))) ∧
                              (FullMem c { s with scratch :=
                                { s.scratch with scratch_buf := scr1 } } ⋆ R) m1)
                            ?_ ?_
                          · rintro _ ⟨ht_sz1, ⟨⟩⟩ m1
                              ⟨scr1, hscr1l, hctrl1, hsz_cases, hsz1_max, hpre1, hslot1, hm1⟩
                            obtain ⟨k1, hk1, hpow1⟩ := hctrl1.2.2.2.2.1
                            have hfit1 : ht_off.toNat + ht_sz1.toNat ≤ c.scratch_cap :=
                              hctrl1.2.2.1
                            have hpos1 : 0 < ht_sz1.toNat := by
                              rw [hpow1]; have := Nat.two_pow_pos k1; omega
                            have hscr1_6 : scr1[(BitVec.toNat ctrl_off +
                                BitVec.toNat (6 : BitVec 64)) % 2 ^ 64]'(by
                                rw [hscr1l]; change (ctrl_off.toNat + 6) % 2 ^ 64 < c.scratch_cap
                                rw [Nat.mod_eq_of_lt (by omega)]; omega) =
                                BitVec.ofNat 32 ht_off.toNat := by
                              have hg6 := hctrl1.2.2.2.2.2.1
                              rw [List.getElem?_eq_getElem (by rw [hscr1l]; omega),
                                Option.some.injEq] at hg6
                              rw [← hg6]; exact scr_idx_add_imm 6 rfl (by omega) _ _
                            have hscr1_6_nat :
                                (BitVec.ofNat 32 ht_off.toNat).toNat = ht_off.toNat :=
                              bv32_ofNat_toNat_lt (by omega)
                            have hscr1_6b : scr1[(ctrl_off + (6 : BitVec 64)).toNat]'(by
                                rw [hscr1l]; change (ctrl_off.toNat + 6) % 2 ^ 64 < c.scratch_cap
                                rw [Nat.mod_eq_of_lt (by omega)]; omega) =
                                BitVec.ofNat 32 ht_off.toNat := hscr1_6
                            have hof_eq : (BitVec.ofNat 32 ht_off.toNat).setWidth 64 = ht_off := by
                              apply BitVec.eq_of_toNat_eq
                              rw [bv64_zext32_toNat, hscr1_6_nat]
                            let s1 : FullState :=
                              { s with scratch := { s.scratch with scratch_buf := scr1 } }
                            have hs1_scrl : s1.scratch.scratch_buf.length = c.scratch_cap := hscr1l
                            have hs1_len : s1.LengthsOk c :=
                              ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscr1l }⟩
                            change (FullMem c s1 ⋆ R) m1 at hm1
                            c0_hsteps_nogrp
                            c0_call hHashEnt
                            refine ⟨c, s1, R, rfl, hs1_len, hm1, fun hv => ?_⟩
                            c0_hsteps_nogrp
                            refine wp_loop_inv (ts := [i64, i64])
                              (fun ⟨slot, p, ⟨⟩⟩ mp => mp = m1 ∧
                                slot.toNat = (hv.toNat + p.toNat) % ht_sz1.toNat ∧
                                p.toNat ≤ ht_sz1.toNat ∧
                                ∀ q < p.toNat, scr1[ht_off.toNat +
                                  (hv.toNat + q) % ht_sz1.toNat]? ≠ some 0xFFFFFFFF#32)
                              (fun ⟨_, p, ⟨⟩⟩ _ => ht_sz1.toNat - p.toNat)
                              (fun Jp hJp => by
                                c0_hsteps; exact hJp (hv &&& (ht_sz1 - 1#64), 0#64, ()) m1
                                  ⟨rfl, by rw [bv64_and_pow2_mod hk1 hpow1]; simp,
                                    Nat.zero_le _, fun _ h => by simp at h⟩)
                              (fun Jp ⟨slot, p, ⟨⟩⟩ mp ⟨hmp, hslot_mod, hp_le, hnoem⟩ ihp => ?_)
                            subst mp
                            have hslot_lt : slot.toNat < ht_sz1.toNat := by
                              rw [hslot_mod]; exact Nat.mod_lt _ hpos1
                            c0_hsplit
                            · have hp_lt : p.toNat < ht_sz1.toNat := hc
                              have hsl_add_n : (ht_off + slot).toNat =
                                  ht_off.toNat + slot.toNat := bv64_add_toNat (by omega)
                              have hsl_arr : (ht_off + slot).toNat < scr1.length := by
                                rw [hsl_add_n, hscr1l]; omega
                              let cur := scr1[(ht_off + slot).toNat]'hsl_arr
                              have hcur_get : scr1[ht_off.toNat + slot.toNat]? = some cur := by
                                rw [List.getElem?_eq_getElem (by rw [hscr1l]; omega)]
                                congr 1; exact (list_getElem_congr hsl_add_n hsl_arr _).symm
                              have hcur_lt : cur.toNat < 2 ^ 32 := cur.isLt
                              clear hc; c0_hsplit
                              · have hent_ne_ff : ent ≠ 0xFFFFFFFF#32 := fun he => by
                                  have h1 := congrArg BitVec.toNat he
                                  have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 0xFFFFFFFF :=
                                    by decide
                                  omega
                                try simp only [hs6b]
                                c0_hsteps
                                rw [hsl_add_n] at hm
                                let scr2 := scr1.set (ht_off.toNat + slot.toNat) ent
                                have hscr2l : scr2.length = c.scratch_cap := by simp [scr2, hscr1l]
                                have hctrl2 : M7CongHtCtrlOk c scr2 ctrl_off.toNat
                                    ht_off.toNat ht_sz1.toNat := by
                                  have hco1 := hctrl1.2.1
                                  refine ⟨hscr2l, hco1, hctrl1.2.2.1, hctrl1.2.2.2.1,
                                    ⟨k1, hk1, hpow1⟩, ?_, ?_⟩
                                  · rw [List.getElem?_set_ne (by omega)]; exact hctrl1.2.2.2.2.2.1
                                  · rw [List.getElem?_set_ne (by omega)]; exact hctrl1.2.2.2.2.2.2
                                refine hQ ent scr2 (s.scratch.res_sz + 1#64) _ hscr2l
                                  (scr_state_core_pres hlen scr2 hscr2l _).1 rfl ⟨rfl, rfl⟩
                                  (Or.inr rfl) (fun ho os hok => ?_) (Or.inr (Or.inl rfl)) hm
                                obtain ⟨rfl, rfl⟩ :=
                                  m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                                refine ⟨ht_sz1.toNat, hctrl2, hsz_cases, hsz1_max, ?_, ?_,
                                  fun hff => absurd hff hent_ne_ff⟩
                                · intro idx hi hne7
                                  rw [List.getElem?_set_ne (by omega)]
                                  exact hpre1 idx hi hne7
                                · intro j hj
                                  by_cases hjs : j = slot.toNat
                                  · subst hjs; right; left
                                    rw [List.getElem?_set_self (by rw [hscr1l]; omega)]
                                  · rw [List.getElem?_set_ne (by omega)]
                                    rcases hslot1 j hj with hem | ⟨k0, hk0, raw, hg, hne, hor⟩
                                    · exact Or.inl hem
                                    · exact Or.inr (Or.inr ⟨k0, hk0, raw, hg, hne, hor⟩)
                              · have hcur_ne_ff : cur ≠ 0xFFFFFFFF#32 := by
                                  simp only [hs6a, hht_nat] at hc; exact hc
                                clear hc; c0_hsplit
                                · have hcur_ent : cur = ent := by
                                    simp only [hs6a, hht_nat] at hc; exact hc
                                  c0_hsteps
                                  have hent_ne_ff : ent ≠ 0xFFFFFFFF#32 := by
                                    rw [← hcur_ent]; exact hcur_ne_ff
                                  refine hQ ent scr1 s.scratch.res_sz m1 hscr1l
                                    (scr_state_core_pres hlen scr1 hscr1l _).1 rfl ⟨rfl, rfl⟩
                                    (Or.inl rfl) (fun ho os hok => ?_) (Or.inr (Or.inl rfl)) hm1
                                  obtain ⟨rfl, rfl⟩ :=
                                    m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                                  refine ⟨ht_sz1.toNat, hctrl1, hsz_cases, hsz1_max, hpre1, ?_,
                                    fun hff => absurd hff hent_ne_ff⟩
                                  intro j hj
                                  rcases hslot1 j hj with hem | ⟨k0, hk0, raw, hg, hne, hor⟩
                                  · exact Or.inl hem
                                  · exact Or.inr (Or.inr ⟨k0, hk0, raw, hg, hne, hor⟩)
                                · have hcur_ne_ent : cur ≠ ent := by
                                    simp only [hs6a, hht_nat] at hc; exact hc
                                  have hp1_n : (p + 1#64).toNat = p.toNat + 1 :=
                                    bv64_add1_lt hp_lt (by omega)
                                  clear hc; c0_hsteps_nogrp
                                  refine wp_join0 (fun m2 => m2 = m1)
                                    (fun _ m2 hm2 => by
                                      subst m2; c0_hsteps
                                      have hnext_slot :
                                          ((slot + 1#64) &&& (ht_sz1 - 1#64)).toNat =
                                          (hv.toNat + (p + 1#64).toNat) % ht_sz1.toNat := by
                                        rw [bv64_and_pow2_mod hk1 hpow1,
                                          bv64_add_ofNat_toNat 1 (by decide) (by omega),
                                          hp1_n, ← Nat.add_assoc]
                                        exact mod_add_one_eq hslot_mod
                                      refine ihp ((slot + 1#64) &&& (ht_sz1 - 1#64), p + 1#64, ())
                                        m1 (by dsimp only; omega)
                                        ⟨rfl, hnext_slot, by omega, fun q hq => ?_⟩
                                      rw [hp1_n] at hq
                                      by_cases hqp : q = p.toNat
                                      · subst hqp
                                        rw [← hslot_mod, hcur_get]
                                        intro heq; exact hcur_ne_ff (Option.some.inj heq)
                                      · exact hnoem q (by omega))
                                    (fun J2 hJ2 => ?_)
                                  have hcur_hc : s1.scratch.scratch_buf[(ht_off.toNat +
                                      BitVec.toNat slot) % 2 ^ 64]'(by
                                      rw [hs1_scrl, Nat.mod_eq_of_lt (by omega)]
                                      omega) = cur := rfl
                                  c0_hsplit
                                  · have hcur_fit : cur.toNat + 2 + ea.toNat ≤ ht_off.toNat := by
                                      simp only [hs6a, hht_nat, hcur_hc, hs_e1] at hc
                                      dsimp only [ea, earity] at hc ⊢
                                      have h2n : BitVec.toNat (2 : BitVec 64) = 2 := rfl
                                      have h255 : (mw &&& (255 : BitVec 32)) =
                                          (mw &&& 0xFF#32) := rfl
                                      rw [bv64_zext32_toNat]
                                      rw [h2n, h255, Nat.mod_eq_of_lt (by omega)] at hc
                                      exact hc
                                    have hc1_arr : (cur.setWidth 64 + 1#64).toNat <
                                        s1.scratch.scratch_buf.length := by
                                      rw [hs1_scrl, bv64_zext32_add_ofNat cur 1 (by decide)]
                                      omega
                                    clear hc; try simp only [hs6b]
                                    c0_hsteps_nogrp
                                    refine wp_join0 (fun m3 => m3 = m1)
                                      (fun _ m3 hm3 => by subst m3; c0_hsteps; exact hJ2 m1 rfl)
                                      (fun J3 hJ3 => ?_)
                                    c0_hsplit
                                    · clear hc; c0_hsplit
                                      · clear hc; c0_hsteps_nogrp
                                        refine wp_loop_break_group (brkTs := [i32, i64])
                                          (lpTs := [i64])
                                          (fun (_eq, _kb, ()) mb => mb = m1)
                                          (fun rem (k, ()) mk => mk = m1 ∧ k.toNat ≤ ea.toNat ∧
                                            rem = ea.toNat - k.toNat)
                                          ?_ ?_ ?_
                                        · rintro _ ⟨eq_b, kb, ⟨⟩⟩ mb hmb; subst mb
                                          c0_hsplit
                                          · have hcur_ne_ff' : cur ≠ 0xFFFFFFFF#32 := hcur_ne_ff
                                            c0_hsteps
                                            refine hQ cur scr1 s.scratch.res_sz m1 hscr1l
                                              (scr_state_core_pres hlen scr1 hscr1l _).1 rfl
                                              ⟨rfl, rfl⟩ (Or.inl rfl) (fun ho os hok => ?_)
                                              (Or.inr (Or.inr ⟨ht_off.toNat, ht_sz1.toNat,
                                                slot.toNat, hctrl1, hslot_lt, hcur_get, by omega⟩))
                                              hm1
                                            obtain ⟨rfl, rfl⟩ := m7CongHtCtrlOk_match_reads hco8
                                              hscrl hho_eq hsz_eq hok
                                            refine ⟨ht_sz1.toNat, hctrl1, hsz_cases,
                                              hsz1_max, hpre1,
                                              ?_, fun hff => absurd hff hcur_ne_ff'⟩
                                            intro j hj
                                            rcases hslot1 j hj with hem |
                                                ⟨k0, hk0, raw, hg, hne, hor⟩
                                            · exact Or.inl hem
                                            · exact Or.inr (Or.inr ⟨k0, hk0, raw, hg, hne, hor⟩)
                                          · c0_hsteps; exact hJ3 m1 rfl
                                        · rintro Bk Lk rem ⟨k, ⟨⟩⟩ mk hBk hLk ⟨hmk, hk_le, rfl⟩
                                          subst mk
                                          c0_hsplit
                                          · have hk_lt : k.toNat < ea.toNat := by
                                              rw [hs_e1] at hc; dsimp only [ea, earity]
                                              rw [bv64_zext32_toNat]; exact hc
                                            have hc2k_arr :
                                                (cur.setWidth 64 + 2#64 + k).toNat <
                                                s1.scratch.scratch_buf.length := by
                                              have h12 := bv64_zext32_add_ofNat cur 2 (by decide)
                                              rw [bv64_add_toNat (by rw [h12]; omega),
                                                h12, hs1_scrl]
                                              omega
                                            have he2k_arr :
                                                (ent.setWidth 64 + 2#64 + k).toNat <
                                                s1.scratch.scratch_buf.length := by
                                              have h12 := bv64_zext32_add_ofNat ent 2 (by decide)
                                              rw [bv64_add_toNat (by rw [h12]; omega),
                                                h12, hs1_scrl]
                                              omega
                                            have hk1_n : (k + 1#64).toNat = k.toNat + 1 :=
                                              bv64_add1_lt hk_lt (by omega)
                                            clear hc; c0_hsplit
                                            · c0_hsteps; exact hBk (0#32, k, ()) m1 rfl
                                            · c0_hsteps
                                              exact hLk (ea.toNat - (k + 1#64).toNat)
                                                (k + 1#64, ()) m1 (by omega) ⟨rfl, by omega, rfl⟩
                                          · c0_hsteps; exact hBk (1#32, k, ()) m1 rfl
                                        · intro _ Lk _ hLk; c0_hsteps
                                          exact hLk ea.toNat (0#64, ()) m1 ⟨rfl, Nat.zero_le _, rfl⟩
                                      · c0_hsteps; exact hJ3 m1 rfl
                                    · c0_hsteps; exact hJ3 m1 rfl
                                  · c0_hsteps; exact hJ2 m1 rfl
                            · have hp_eq : p.toNat = ht_sz1.toNat := by omega
                              c0_hsteps
                              refine hQ 0xFFFFFFFF#32 scr1 s.scratch.res_sz m1 hscr1l
                                (scr_state_core_pres hlen scr1 hscr1l _).1 rfl ⟨rfl, rfl⟩
                                (Or.inl rfl) (fun ho os hok => ?_) (Or.inl rfl) hm1
                              obtain ⟨rfl, rfl⟩ :=
                                m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                              refine ⟨ht_sz1.toNat, hctrl1, hsz_cases, hsz1_max, hpre1, ?_,
                                fun _ _ _ _ _ j hj => ?_⟩
                              · intro j hj
                                rcases hslot1 j hj with hem | ⟨k0, hk0, raw, hg, hne, hor⟩
                                · exact Or.inl hem
                                · exact Or.inr (Or.inr ⟨k0, hk0, raw, hg, hne, hor⟩)
                              · obtain ⟨q, hq, hmod⟩ := probe_visit_idx (hv := hv.toNat) hj
                                rw [← hmod]; exact hnoem q (by omega)
                          · intro Js hJs; c0_hsplit
                            · clear hc; c0_hsteps_nogrp
                              refine wp_join_group (ts := []) (fun () mg => mg = m0) ?_ ?_
                              · rintro _ ⟨⟩ mg hmg; subst mg
                                c0_hsteps; c0_call hGrow
                                refine ⟨c, s, R, rfl, hlen, hm0,
                                  fun grown scr_g mg' hgl hleng _ _ hok_g _ hmg' => ?_⟩
                                obtain ⟨hg1, hg2⟩ := hok_g ht_off.toNat old_sz.toNat hok_read
                                have hc_g : M7CongHtCtrlOk c scr_g ctrl_off.toNat ht_off.toNat
                                    grown.toNat := by
                                  by_cases hcap : m7CongHashMaxSz ≤ old_sz.toNat ∨
                                      c.scratch_cap < ht_off.toNat + 2 * old_sz.toNat
                                  · obtain ⟨hn, hs⟩ := hg1 hcap
                                    rw [hn, hs]; exact hok_read
                                  · have h1' : old_sz.toNat < m7CongHashMaxSz := by omega
                                    have h2' : ht_off.toNat + 2 * old_sz.toNat ≤ c.scratch_cap := by
                                      omega
                                    obtain ⟨hn, hok', _, _⟩ := hg2 h1' h2'
                                    rw [hn]; exact hok'
                                have hng : grown.toNat = old_sz.toNat ∨
                                    grown.toNat = 2 * old_sz.toNat := by
                                  by_cases hcap : m7CongHashMaxSz ≤ old_sz.toNat ∨
                                      c.scratch_cap < ht_off.toNat + 2 * old_sz.toNat
                                  · exact Or.inl (hg1 hcap).1
                                  · have h1' : old_sz.toNat < m7CongHashMaxSz := by omega
                                    have h2' : ht_off.toNat + 2 * old_sz.toNat ≤ c.scratch_cap := by
                                      omega
                                    exact Or.inr (hg2 h1' h2').1
                                have hmax_g : grown.toNat ≤ m7CongHashMaxSz := by
                                  rcases hc_g.2.2.2.2.1 with ⟨kg, hkg, heqg⟩
                                  rw [heqg]; unfold m7CongHashMaxSz; exact pow2_16_mul_le kg hkg
                                have hpre_g : ∀ idx < ht_off.toNat, idx ≠ ctrl_off.toNat + 7 →
                                    scr_g[idx]? = s.scratch.scratch_buf[idx]? := by
                                  by_cases hcap : m7CongHashMaxSz ≤ old_sz.toNat ∨
                                      c.scratch_cap < ht_off.toNat + 2 * old_sz.toNat
                                  · rw [(hg1 hcap).2]; exact fun _ _ _ => rfl
                                  · exact (hg2 (by omega) (by omega)).2.2.1
                                have hslot_g : ∀ j < grown.toNat,
                                    scr_g[ht_off.toNat + j]? = some 0xFFFFFFFF#32 ∨
                                    ∃ k0 < old_sz.toNat, ∃ raw : BitVec 32,
                                      s.scratch.scratch_buf[ht_off.toNat + k0]? = some raw ∧
                                      raw ≠ 0xFFFFFFFF#32 ∧
                                      (scr_g[ht_off.toNat + j]? = some raw ∨
                                        scr_g[ht_off.toNat + j]? =
                                          some (raw &&& 0x7FFFFFFF#32)) := by
                                  intro j hj
                                  by_cases hcap : m7CongHashMaxSz ≤ old_sz.toNat ∨
                                      c.scratch_cap < ht_off.toNat + 2 * old_sz.toNat
                                  · rw [(hg1 hcap).2]
                                    rw [(hg1 hcap).1] at hj
                                    by_cases hem : s.scratch.scratch_buf[ht_off.toNat + j]? =
                                        some 0xFFFFFFFF#32
                                    · exact Or.inl hem
                                    · right
                                      have hlt :
                                          ht_off.toNat + j < s.scratch.scratch_buf.length := by
                                        omega
                                      refine ⟨j, hj, s.scratch.scratch_buf[ht_off.toNat + j]'hlt,
                                        List.getElem?_eq_getElem hlt, ?_,
                                        Or.inl (List.getElem?_eq_getElem hlt)⟩
                                      intro he; apply hem; rw [List.getElem?_eq_getElem hlt, he]
                                  · have h1' : old_sz.toNat < m7CongHashMaxSz := by omega
                                    have h2' : ht_off.toNat + 2 * old_sz.toNat ≤ c.scratch_cap := by
                                      omega
                                    obtain ⟨hn, _, _, hres⟩ := hg2 h1' h2'
                                    rw [hn] at hj
                                    rcases hres j hj with hem | ⟨k0, hk0, raw, hg0, hne0, heq0⟩
                                    · exact Or.inl hem
                                    · exact Or.inr ⟨k0, hk0, raw, hg0, hne0, Or.inr heq0⟩
                                c0_hsteps_nogrp
                                refine wp_join_group (ts := [i64])
                                  (fun ⟨ht_sz2, ⟨⟩⟩ mg2 =>
                                    ht_sz2.toNat = grown.toNat ∧ mg2 = mg')
                                  (fun _ ⟨ht_sz2, ⟨⟩⟩ mg2 ⟨hn2, hmg2⟩ => by
                                    subst mg2; c0_hsteps
                                    have heq2 : ht_sz2 = grown := BitVec.eq_of_toNat_eq hn2
                                    subst heq2
                                    exact hJs (ht_sz2, ()) mg' ⟨scr_g, hgl, hc_g, hng, hmax_g,
                                      hpre_g, hslot_g, hmg'⟩)
                                  (fun J2 hJ2 => ?_)
                                obtain ⟨kg, hkg, hpowg⟩ := hc_g.2.2.2.2.1
                                have hpow2_pos : 16 ≤ grown.toNat := by
                                  rw [hpowg]; have := Nat.two_pow_pos kg; omega
                                have hcap_g : grown.toNat ≤ c.scratch_cap - ht_off.toNat := by
                                  have := hc_g.2.2.1; omega
                                c0_hsplit
                                · c0_hsplit
                                  · c0_hsplit
                                    · c0_hsteps; exact hJ2 (grown, ()) mg' ⟨rfl, rfl⟩
                                    · exfalso
                                      rw [hs6a, hht_nat, bv64_cap_sub_mod (Nat.le_of_lt h2)
                                        (by omega)] at hc
                                      omega
                                  · exfalso
                                    have hbv : grown = BitVec.ofNat 64 grown.toNat := by
                                      apply BitVec.eq_of_toNat_eq
                                      rw [bv64_ofNat_toNat_lt
                                        (by unfold m7CongHashMaxSz at hmax_g; omega)]
                                    have hz : (grown &&& (grown - 1#64)) = 0#64 := by
                                      rw [hbv]; exact bv64_pow2_and_sub1_zero hkg
                                        (by rw [bv64_ofNat_toNat_lt
                                            (by unfold m7CongHashMaxSz at hmax_g; omega)]
                                            exact hpowg)
                                    exact hc hz
                                · exfalso; m7_omega
                              · intro J1 hJ1
                                c0_hsplit
                                · c0_hsteps; exact hJ1 () m0 rfl
                                · clear hc; c0_hsplit
                                  · c0_hsteps; exact hJ1 () m0 rfl
                                  · c0_hsteps; try simp only [hs7b]
                                    refine hJs (old_sz, ()) m0
                                      ⟨s.scratch.scratch_buf, hscrl, hok_read, Or.inl rfl, hmax,
                                        fun _ _ _ => rfl, fun j hj => ?_, hm0⟩
                                    by_cases hem : s.scratch.scratch_buf[ht_off.toNat + j]? =
                                        some 0xFFFFFFFF#32
                                    · exact Or.inl hem
                                    · right
                                      have hlt :
                                          ht_off.toNat + j < s.scratch.scratch_buf.length := by
                                        omega
                                      refine ⟨j, hj, s.scratch.scratch_buf[ht_off.toNat + j]'hlt,
                                        List.getElem?_eq_getElem hlt, ?_,
                                        Or.inl (List.getElem?_eq_getElem hlt)⟩
                                      intro he; apply hem; rw [List.getElem?_eq_getElem hlt, he]
                            · exfalso; rw [hs7a, hos_nat] at hc; m7_omega

end WpProofs

/-! ## 5. Closed `ModuleOk` (`m7CongHash_moduleOk`) -/

section ModuleVerification

private theorem m7CongHashSpecTable_nodup :
    (m7CongHashSpecTable.map SpecEntry.name).Nodup := by
  show
    ( [ "full_cong_ht_hash_ent_m7", "full_cong_ht_init_m7", "full_cong_ht_grow_m7"
      , "full_cong_ht_lookup_m7", "full_cong_ht_insert_m7" ] : List String).Nodup
  decide

private theorem m7CongHashEnv_row_at (i : Nat) (e : SpecEntry)
    (hi : m7CongHashSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → m7CongHashEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) m7CongHashSpecTable_nodup (hno xs m Q X h)

/-- Row-by-row `TableImpl` for `m7CongHashFns` (`5` functions) against `m7CongHashSpecTable`. -/
theorem m7CongHash_tableImpl :
    TableImpl m7CongHashEnv m7CongHashFns m7CongHashSpecTable := by
  let h0 := m7CongHashEnv_row_at 0 ⟨"full_cong_ht_hash_ent_m7", [i64, i32, i64], [i64],
    m7CongHtHashEntSpec, true⟩
  let h2 := m7CongHashEnv_row_at 2 ⟨"full_cong_ht_grow_m7", [i64, i64], [i64],
    m7CongHtGrowSpec, true⟩
  exact ⟨.of (full_cong_ht_hash_ent_m7_wp m7CongHashEnv),
    ⟨.of (full_cong_ht_init_m7_wp m7CongHashEnv),
    ⟨.of (full_cong_ht_grow_m7_wp m7CongHashEnv h0),
    ⟨.of (full_cong_ht_lookup_m7_wp m7CongHashEnv),
    ⟨.of (full_cong_ht_insert_m7_wp m7CongHashEnv h2 h0), trivial⟩⟩⟩⟩⟩

/-- Closed `ModuleOk` for standalone `m7CongHashModule` under canonical `m7CongHashEnv`. -/
theorem m7CongHash_moduleOk : ModuleOk m7CongHashEnv m7CongHashModule :=
  Env.ofTable_moduleOk m7CongHash_acyclic
    ⟨full_cong_ht_hash_ent_m7_wf, full_cong_ht_init_m7_wf, full_cong_ht_grow_m7_wf,
      full_cong_ht_lookup_m7_wf, full_cong_ht_insert_m7_wf, trivial⟩
    m7CongHash_tableImpl

end ModuleVerification

/-! ## 6. Concrete `Mem 64` Non-Vacuity (`16,448`-Word Buffer, `8192 → 16384`, `XPost := False`) -/

section NonVacuity

private def nvM7CongScrHead : List (BitVec 32) :=
  [0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 64#32, 8192#32, 8#32, 1#32, 0#32] ++
    List.replicate 53 0#32

private theorem nvM7CongScrHead_len : nvM7CongScrHead.length = 64 := by decide

/-- `16,448`-word concrete `scratch_buf`: `ctrl[6]=64`, `ctrl[7]=8192`, gate `ent=8`, `16,384`
empty slots `0xFFFFFFFF#32` (symbolic `List.replicate` -> `O(1)` proofs, `0` `decide` on `16k`). -/
def nvM7CongScrBuf : List (BitVec 32) :=
  nvM7CongScrHead ++ List.replicate 16384 0xFFFFFFFF#32

theorem nvM7CongScrBuf_len : nvM7CongScrBuf.length = 16448 := by
  unfold nvM7CongScrBuf
  rw [List.length_append, List.length_replicate, nvM7CongScrHead_len]

/-- Concrete `FullCfg` with `scratch_cap = 16448` (`avail = 67548`, supporting `>4096` tables). -/
def nvM7CongCfg : FullCfg where
  hdr := 0x1000#64; avail := 67548; mv := 1; max_vars := 1; bva_cap := 0; nc := 0
  arena_cap := 0; wcap := 1; delayed_cap := 0; red_cap := 0; extend_cap := 0
  scratch_cap := 16448
  hbva := rfl; hmv := (by decide); hmaxv := (by decide); hnc := (by decide)
  harena := (by decide); hwcap := (by decide); hdel := (by decide); hred := (by decide)
  hext := (by decide); hscr := (by decide); havail_fit := (by decide); hsize := (by decide)

def nvM7CongScratch : FullScratch where
  heap_len := 0; scinc := 0#64; rel_period := 0#64; rel_limit := 0#64; rel_wait := 0#64
  rel_u := 0#64; rel_v := 0#64; rel_trigger := 0#64; conflicts := 0#64; learned_lits := 0#64
  min_removed := 0#64; delayed_len := 0; stable := 0#64; switched := 0#64; mode_count := 0#64
  mode_confl_lim := 0#64; mode_tick_lim := 0#64; mode_saved_ticks := 0#64; search_ticks := 0#64
  q_first := 0#64; q_last := 0#64; q_search_idx := 0#64; q_search_stamp := 0#64
  q_cur_stamp := 0#64; target_assigned := 0#64; best_assigned := 0#64; rephase_limit := 0#64
  rephased := 0#64; reduce_limit := 0#64; reductions := 0#64; tier1 := 2#64; tier2 := 6#64
  restarts := 0#64; restart_limit := 0#64; ema_fast_biased := 0#64; ema_fast_exp := 0#64
  ema_slow_biased := 0#64; ema_slow_exp := 0#64; extend_len := 0; rng_state := 1#64
  chrono_levels := 0#64; otfs_cnt := 0#64; eager_sub_cnt := 0#64; probe_limit := 0#64
  probings := 0#64; elim_limit := 0#64; eliminations := 0#64; elim_bound := 0#64
  iterating := 0#64; hbr_cnt := 0#64; trans_cnt := 0#64; viv_cnt := 0#64; subst_cnt := 0#64
  cong_cnt := 0#64; sweep_cnt := 0#64; bve_cnt := 0#64; bce_cnt := 0#64; bva_cnt := 0#64
  walk_cnt_stat := 0#64; fwd_sub_cnt := 0#64; fwd_str_cnt := 0#64; ant_sz := 0#64; res_sz := 0#64
  walk_vals := [0#8, 0#8]; phases := [0#8]; phases_target := [0#8]
  phases_best := [0#8]; walk_best := [0#8]; heap := [0#32]; pos := [0xFFFFFFFF#32]
  shrink_stk := [0#32]; q_prev := [0xFFFFFFFF#32]; q_next := [0xFFFFFFFF#32]; q_stamp := [0#32]
  wsort := [0#32, 0#32]; work_stk1 := [0#32, 0#32]; work_stk2 := [0#32, 0#32]
  tarjan_mark := [0#32, 0#32]; tarjan_reach := [0#32, 0#32]; score := [0#64]; sim_sig := [0#64]
  glue_used := List.replicate 64 0#32; last_learned := List.replicate 16 0xFFFFFFFF#32
  delayed := []; red_refs := []; extend_stk := []; scratch_buf := nvM7CongScrBuf

def nvM7CongState : FullState where
  core :=
    { d_cur := 0#64, d_val := 0#64, cur_vars := 1, unassigned := 1#64, arena_len := 0, wlen := 0
      wusable := 0#64, arena_garbage := 0#64, first_reducible := 0#64, num_irred := 0#64
      num_redundant := 0#64, num_binary := 0#64, unflushed := 0#64, probing := 0#64, trail_end := 0
      propagated := 0, cur_level := 0, fuel := 16#64, confl_ref := 0#64, confl_type := 0#64
      confl_lit0 := 0#64, confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0, min_clr_len := 0
      min_clr_full := 0#64, oom := 0#64, dense_mode := 0#64, inconsistent := 0#64
      vals := [0#8, 0#8], lit_mark := [0#8, 0#8], mrk := [0#8], flags := [0#32], lvl := [0#32]
      rsns := [0xFFFFFFFF#32], trl := [0#32], trail_pos := [0#32], tmp := [0#32]
      min_clr := [0#32], frame_trail := [0#32, 0#32], frame_dec := [0#32, 0#32]
      wvec := List.replicate 4 0#32, repr := [0#32, 0#32], min_stk := List.replicate 4 0#32
      arena := [], wstk := [0#32] }
  scratch := nvM7CongScratch

theorem nvM7Cong_lengths : nvM7CongState.LengthsOk nvM7CongCfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, nvM7CongScrBuf_len⟩⟩

private def nvM7BlockHdr : List UInt8 :=
  bytes64 [1#64, 0#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords nvM7CongCfg nvM7CongState)

private def nvM7BlockBytes : List UInt8 :=
  (bytesOf (t := i8) nvM7CongState.core.vals ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvM7CongScratch.walk_vals ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvM7CongState.core.lit_mark ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvM7CongState.core.mrk ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvM7CongScratch.phases ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvM7CongScratch.phases_target ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvM7CongScratch.phases_best ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvM7CongScratch.walk_best ++ List.replicate 7 0)

private def nvM7BlockU32A : List UInt8 :=
  (bytesOf (t := i32) nvM7CongState.core.flags ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM7CongState.core.lvl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM7CongState.core.rsns ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM7CongState.core.trl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM7CongState.core.trail_pos ++ List.replicate 4 0)

private def nvM7BlockU32B : List UInt8 :=
  (bytesOf (t := i32) nvM7CongState.core.tmp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM7CongScratch.heap ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM7CongScratch.pos ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM7CongState.core.min_clr ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM7CongScratch.shrink_stk ++ List.replicate 4 0)

private def nvM7BlockU32C : List UInt8 :=
  (bytesOf (t := i32) nvM7CongScratch.q_prev ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM7CongScratch.q_next ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM7CongScratch.q_stamp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM7CongState.core.frame_trail ++ List.replicate 0 0) ++
  (bytesOf (t := i32) nvM7CongState.core.frame_dec ++ List.replicate 0 0)

private def nvM7BlockWvec : List UInt8 :=
  bytesOf (t := i32) nvM7CongState.core.wvec ++
  bytesOf (t := i32) nvM7CongState.core.repr ++
  bytesOf (t := i32) nvM7CongScratch.wsort ++
  bytesOf (t := i32) nvM7CongScratch.work_stk1 ++
  bytesOf (t := i32) nvM7CongScratch.work_stk2 ++
  bytesOf (t := i32) nvM7CongScratch.tarjan_mark ++
  bytesOf (t := i32) nvM7CongScratch.tarjan_reach ++
  bytes64 nvM7CongScratch.score ++ bytes64 nvM7CongScratch.sim_sig

private def nvM7BlockTail : List UInt8 :=
  bytesOf (t := i32) nvM7CongState.core.min_stk ++
  bytesOf (t := i32) nvM7CongScratch.glue_used ++
  bytesOf (t := i32) nvM7CongScratch.last_learned ++
  bytesOf (t := i32) nvM7CongState.core.arena ++
  bytesOf (t := i32) nvM7CongState.core.wstk ++
  bytesOf (t := i32) nvM7CongScratch.delayed ++
  bytesOf (t := i32) nvM7CongScratch.red_refs ++
  bytesOf (t := i32) nvM7CongScratch.extend_stk ++
  bytesOf (t := i32) nvM7CongScrBuf ++ List.replicate 0 0

/-- Concrete `67,548`-byte `Mem 64` image for `nvM7CongCfg` at `0x1000`. -/
def nvM7CongMem : Mem 64 :=
  (nvM7BlockHdr ++ nvM7BlockBytes ++ nvM7BlockU32A ++ nvM7BlockU32B ++
    nvM7BlockU32C ++ nvM7BlockWvec ++ nvM7BlockTail).At nvM7CongCfg.hdr

private theorem m7_nv_sep_append {P Q : Mem 64 → Prop} {a b : BitVec 64} {bs1 bs2 : List UInt8}
    (hb : b = a + BitVec.ofNat 64 bs1.length) (hlen : bs1.length + bs2.length ≤ 2 ^ 64)
    (h1 : P (bs1.At a)) (h2 : Q (bs2.At b)) : (P ⋆ Q) ((bs1 ++ bs2).At a) := by
  have heq := congrFun (Mem.At_append_sep bs1 bs2 a hlen) ((bs1 ++ bs2).At a)
  rw [← hb] at heq
  exact sep_mono2 (fun _ h => h ▸ h1) (fun _ h => h ▸ h2) _ (heq.mp rfl)

private theorem m7_nv_arr_pad_p {t : Ty} {a : BitVec 64} {xs : List (Val t)} (n pad : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n + pad ≤ 2 ^ 64) :
    (bytesOf xs ++ List.replicate pad 0).length = n + pad ∧
    (array (t := t) a xs ⋆ region (a + BitVec.ofNat 64 n) pad)
      ((bytesOf xs ++ List.replicate pad 0).At a) :=
  ⟨by rw [List.length_append, bytesOf_length, List.length_replicate, hn],
   m7_nv_sep_append (by rw [bytesOf_length, hn])
     (by rw [bytesOf_length, List.length_replicate]; omega)
     (array_bytes a xs (by omega)) ⟨List.replicate pad 0, List.length_replicate, rfl⟩⟩

private theorem m7_nv_arr_p {t : Ty} {a : BitVec 64} {xs : List (Val t)} (n : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytesOf xs).length = n ∧ array (t := t) a xs ((bytesOf xs).At a) :=
  ⟨by rw [bytesOf_length, hn], array_bytes a xs (by omega)⟩

private theorem m7_nv_arr64_p {a : BitVec 64} {xs : List (BitVec 64)} (n : Nat)
    (hn : 8 * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytes64 xs).length = n ∧ array64 a xs ((bytes64 xs).At a) :=
  ⟨by rw [bytes64_length, hn], array64_bytes a xs (by omega)⟩

private theorem m7_nv_join {P Q : Mem 64 → Prop} {a b : BitVec 64} {bs1 bs2 : List UInt8}
    {n1 n2 : Nat} (h1 : bs1.length = n1 ∧ P (bs1.At a))
    (h2 : bs2.length = n2 ∧ Q (bs2.At b))
    (hb : b = a + BitVec.ofNat 64 n1) (hbd : n1 + n2 ≤ 2 ^ 64) :
    (bs1 ++ bs2).length = n1 + n2 ∧ (P ⋆ Q) ((bs1 ++ bs2).At a) :=
  ⟨by rw [List.length_append, h1.1, h2.1], m7_nv_sep_append (h1.1 ▸ hb) (by omega) h1.2 h2.2⟩

private theorem m7_nv_reorg {P Q : Mem 64 → Prop} {bs : List UInt8} {a : BitVec 64} {n : Nat}
    (h : bs.length = n ∧ P (bs.At a)) (himp : ∀ m, P m → Q m) : bs.length = n ∧ Q (bs.At a) :=
  ⟨h.1, himp _ h.2⟩

private theorem m7_nv_zip4 {A1 B1 A2 B2 A3 B3 A4 B4 : Mem 64 → Prop} {m : Mem 64}
    (h : ((((A1 ⋆ B1) ⋆ (A2 ⋆ B2)) ⋆ (A3 ⋆ B3)) ⋆ (A4 ⋆ B4)) m) :
    (((A1 ⋆ A3 ⋆ A4) ⋆ A2) ⋆ (B1 ⋆ B2 ⋆ B3 ⋆ B4)) m := sep_ac h

private theorem m7_nv_zip4_tail {C A2 P1 A5 B5 A6 B6 A7 B7 A8 B8 : Mem 64 → Prop} {m : Mem 64}
    (h : ((((((C ⋆ A2) ⋆ P1) ⋆ (A5 ⋆ B5)) ⋆ (A6 ⋆ B6)) ⋆ (A7 ⋆ B7)) ⋆ (A8 ⋆ B8)) m) :
    (C ⋆ (A2 ⋆ A5 ⋆ A6 ⋆ A7 ⋆ A8) ⋆ (P1 ⋆ B5 ⋆ B6 ⋆ B7 ⋆ B8)) m := sep_ac h

theorem nvM7CongMem_ok : FullMem nvM7CongCfg nvM7CongState nvM7CongMem := by
  let c := nvM7CongCfg; let s := nvM7CongState
  have hvb : valsBytes c.max_vars - 2 * c.max_vars = 6 := by decide
  have hmb : markBytes c.max_vars - c.max_vars = 7 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 0 := by decide
  have hmv1 : BitVec.ofNat 64 c.max_vars = 1#64 := rfl
  have hmv2 : BitVec.ofNat 64 (2 * c.max_vars) = 2#64 := rfl
  have hmv4 : BitVec.ofNat 64 (4 * c.max_vars) = 4#64 := rfl
  have hmv8 : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 8#64 := rfl
  have hHdr : nvM7BlockHdr.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s))
        (nvM7BlockHdr.At c.hdr) :=
    m7_nv_join (m7_nv_arr64_p (a := c.hdr) (xs := [1#64, 0#64, 0#64, 0#64]) 32 rfl (by decide))
      (m7_nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide)) (by decide) (by decide)
  have hBytes : nvM7BlockBytes.length = 64 ∧
      (FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ c.padBytes)
        (nvM7BlockBytes.At c.pVals) := by
    let pB1 : Mem 64 → Prop :=
      region (c.pVals + 2#64) 6 ⋆ region (c.pWalkVals + 2#64) 6 ⋆
      region (c.pLitMark + 2#64) 6 ⋆ region (c.pMark + 1#64) 7
    have h1 := m7_nv_join
      (m7_nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 2 6 rfl (by decide))
      (m7_nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 2 6 rfl
        (by decide)) (by decide) (by decide)
    have h2 := m7_nv_join h1
      (m7_nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 2 6 rfl (by decide))
      (by decide) (by decide)
    have h3 := m7_nv_reorg (m7_nv_join h2
      (m7_nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 1 7 rfl (by decide))
      (by decide) (by decide))
      (Q := (FullCoreByteArrs c s.core ⋆ array (t := i8) c.pWalkVals s.scratch.walk_vals) ⋆ pB1)
      fun _ hm => m7_nv_zip4 hm
    have h4 := m7_nv_join h3
      (m7_nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 1 7 rfl (by decide))
      (by decide) (by decide)
    have h5 := m7_nv_join h4
      (m7_nv_arr_pad_p (t := i8) (a := c.pPhasesTarget) (xs := s.scratch.phases_target) 1 7 rfl
        (by decide)) (by decide) (by decide)
    have h6 := m7_nv_join h5
      (m7_nv_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best) 1 7 rfl
        (by decide)) (by decide) (by decide)
    have h7 := m7_nv_join h6
      (m7_nv_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best) 1 7 rfl
        (by decide)) (by decide) (by decide)
    exact m7_nv_reorg h7 fun _ hm => by
      have hfin := m7_nv_zip4_tail hm
      unfold FullScrByteArrs FullCfg.padBytes; rw [hvb, hmb, hmv2, hmv1]
      simpa only [pB1, sep_assoc] using hfin
  have hU32A : nvM7BlockU32A.length = 40 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        (nvM7BlockU32A.At c.pFlags) := by
    have h1 := m7_nv_join
      (m7_nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 4 4 rfl (by decide))
      (m7_nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 4 4 rfl (by decide))
      (by decide) (by decide)
    have h2 := m7_nv_join h1
      (m7_nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 4 4 rfl (by decide))
      (by decide) (by decide)
    have h3 := m7_nv_join h2
      (m7_nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 4 4 rfl (by decide))
      (by decide) (by decide)
    exact m7_nv_reorg (m7_nv_join h3
      (m7_nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 4 4 rfl (by decide))
      (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu4, hmv4]; exact sep_ac hm
  have hU32B : nvM7BlockU32B.length = 40 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
        (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
         array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        (nvM7BlockU32B.At c.pTmp) := by
    have h1 := m7_nv_join
      (m7_nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 4 4 rfl (by decide))
      (m7_nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 4 4 rfl (by decide))
      (by decide) (by decide)
    have h2 := m7_nv_join h1
      (m7_nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 4 4 rfl (by decide))
      (by decide) (by decide)
    have h3 := m7_nv_join h2
      (m7_nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 4 4 rfl (by decide))
      (by decide) (by decide)
    exact m7_nv_reorg (m7_nv_join h3
      (m7_nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk) 4 4 rfl
        (by decide)) (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu4, hmv4]; exact sep_ac hm
  have hU32C : nvM7BlockU32C.length = 40 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        (nvM7BlockU32C.At c.pQPrev) := by
    have h1 := m7_nv_join
      (m7_nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 4 4 rfl (by decide))
      (m7_nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 4 4 rfl (by decide))
      (by decide) (by decide)
    have h2 := m7_nv_join h1
      (m7_nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 4 4 rfl (by decide))
      (by decide) (by decide)
    have h3 := m7_nv_join h2
      (m7_nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 8 0 rfl
        (by decide)) (by decide) (by decide)
    exact m7_nv_reorg (m7_nv_join h3
      (m7_nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 8 0 rfl (by decide))
      (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu4, hu8, hmv4, hmv8]; exact sep_ac hm
  have hWvec : nvM7BlockWvec.length = 80 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        (nvM7BlockWvec.At c.pWvec) := by
    have h1 := m7_nv_join
      (m7_nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 16 rfl (by decide))
      (m7_nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 8 rfl (by decide))
      (by decide) (by decide)
    have h2 := m7_nv_join h1
      (m7_nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 8 rfl (by decide))
      (by decide) (by decide)
    have h3 := m7_nv_join h2
      (m7_nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 8 rfl (by decide))
      (by decide) (by decide)
    have h4 := m7_nv_join h3
      (m7_nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 8 rfl (by decide))
      (by decide) (by decide)
    have h5 := m7_nv_join h4
      (m7_nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 8 rfl (by decide))
      (by decide) (by decide)
    have h6 := m7_nv_join h5
      (m7_nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 8 rfl
        (by decide)) (by decide) (by decide)
    have h7 := m7_nv_join h6
      (m7_nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 8 rfl (by decide))
      (by decide) (by decide)
    exact m7_nv_reorg (m7_nv_join h7
      (m7_nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 8 rfl (by decide))
      (by decide) (by decide)) fun _ hm => by unfold FullScrWksArrs; exact sep_ac hm
  have hTail : nvM7BlockTail.length = 66132 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        (nvM7BlockTail.At c.pMinStk) := by
    have h1 := m7_nv_join
      (m7_nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 16 rfl (by decide))
      (m7_nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256 rfl (by decide))
      (by decide) (by decide)
    have h2 := m7_nv_join h1
      (m7_nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned) 64 rfl
        (by decide)) (by decide) (by decide)
    have h3 := m7_nv_join h2
      (m7_nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 0 rfl (by decide))
      (by decide) (by decide)
    have h4 := m7_nv_join h3
      (m7_nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 4 rfl (by decide))
      (by decide) (by decide)
    have h5 := m7_nv_join h4
      (m7_nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl (by decide))
      (by decide) (by decide)
    have h6 := m7_nv_join h5
      (m7_nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl (by decide))
      (by decide) (by decide)
    have h7 := m7_nv_join h6
      (m7_nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl (by decide))
      (by decide) (by decide)
    have h8 := m7_nv_join h7
      (m7_nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := nvM7CongScrBuf) 65792
        (by rw [nvM7CongScrBuf_len]; rfl) (by decide)) (by decide) (by decide)
    have h9 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 0).At c.pSlack) :=
      ⟨rfl, ⟨List.replicate 0 0, by decide, rfl⟩⟩
    exact m7_nv_reorg (m7_nv_join h8 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := m7_nv_join hHdr hBytes (by decide) (by decide)
  have h02 := m7_nv_join h01 hU32A (by decide) (by decide)
  have h03 := m7_nv_join h02 hU32B (by decide) (by decide)
  have h04 := m7_nv_join h03 hU32C (by decide) (by decide)
  have h05 := m7_nv_join h04 hWvec (by decide) (by decide)
  exact (m7_nv_reorg (Q := FullMem c s) (m7_nv_join h05 hTail (by decide) (by decide)) fun _ hm =>
    by unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
        FullScrMetaArrs FullCfg.pad; exact sep_ac hm).2

private theorem nvM7CongMem_sep : (FullMem nvM7CongCfg nvM7CongState ⋆ emp) nvM7CongMem := by
  rw [sep_emp]; exact nvM7CongMem_ok

theorem nvM7Cong_ctrl_ok : M7CongHtCtrlOk nvM7CongCfg nvM7CongScrBuf 0 64 8192 :=
  ⟨nvM7CongScrBuf_len, by decide, by decide, by decide, ⟨9, by decide, by decide⟩,
   by unfold nvM7CongScrBuf; rw [List.getElem?_append_left (by decide)]; decide,
   by unfold nvM7CongScrBuf; rw [List.getElem?_append_left (by decide)]; decide⟩

/-- Concrete `Mem 64` NV (`XPost := False`): `full_cong_ht_init_m7` initializes `16,384` buckets
(`4x` past legacy `4096`) cleanly on `nvM7CongMem`. -/
theorem nv_m7_cong_ht_init :
    Func.wp m7CongHashEnv full_cong_ht_init_m7_body
      (nvM7CongCfg.hdr, 0#64, 64#64, 16384#64, ()) nvM7CongMem
      (fun (ret, ()) m' => ∃ s',
        ret = 16384#64 ∧ PreservesCoreSlice FullState.core nvM7CongState s' ∧
        s'.LengthsOk nvM7CongCfg ∧ FullExtScratchPres nvM7CongState s' ∧
        M7CongHtCtrlOk nvM7CongCfg s'.scratch.scratch_buf 0 64 16384 ∧
        FullMem nvM7CongCfg s' m')
      (fun _ _ _ _ => False) :=
  m7CongHash_tableImpl.2.1.2 _ _ _ _
    ⟨nvM7CongCfg, nvM7CongState, emp, rfl, nvM7Cong_lengths, nvM7CongMem_sep,
     fun ret scr' _ m' _ hlen hcore hpres _ hok_nz hok_fit hm' => by
       have htgt : m7CongHtTargetCap nvM7CongCfg (64#64).toNat 16384#64 = 16384 := by decide
       obtain ⟨hctrl, hle, hlt2, _, _, _⟩ := hok_fit (hok_nz (by decide) (by decide) (by decide))
       obtain ⟨k, _, hpow⟩ := hctrl.2.2.2.2.1
       rw [htgt] at hle hlt2
       have hk10 : k = 10 := by
         rcases Nat.lt_trichotomy k 10 with h1 | h2 | h3
         · have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : k ≤ 9)
           have : 2 ^ 9 = 512 := by decide
           omega
         · exact h2
         · have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 11 ≤ k)
           have : 2 ^ 11 = 2048 := by decide
           omega
       have hret_n : ret.toNat = 16384 := by rw [hpow, hk10]
       have hret : ret = 16384#64 := BitVec.eq_of_toNat_eq hret_n
       have hctrl' : M7CongHtCtrlOk nvM7CongCfg scr' 0 64 16384 := by simpa [hret_n] using hctrl
       rw [sep_emp] at hm'
       exact ⟨_, hret, hcore, hlen, hpres, hctrl', hm'⟩⟩

/-- Concrete `Mem 64` NV (`XPost := False`): `full_cong_ht_grow_m7` grows an `8,192`-bucket
table to `16,384` buckets (`4x` past legacy `4096`) on `nvM7CongMem`. -/
theorem nv_m7_cong_ht_grow :
    Func.wp m7CongHashEnv full_cong_ht_grow_m7_body
      (nvM7CongCfg.hdr, 0#64, ()) nvM7CongMem
      (fun (ret, ()) m' => ∃ s',
        ret = 16384#64 ∧ PreservesCoreSlice FullState.core nvM7CongState s' ∧
        s'.LengthsOk nvM7CongCfg ∧ FullExtScratchPres nvM7CongState s' ∧
        M7CongHtCtrlOk nvM7CongCfg s'.scratch.scratch_buf 0 64 16384 ∧
        FullMem nvM7CongCfg s' m')
      (fun _ _ _ _ => False) :=
  m7CongHash_tableImpl.2.2.1.2 _ _ _ _
    ⟨nvM7CongCfg, nvM7CongState, emp, rfl, nvM7Cong_lengths, nvM7CongMem_sep,
     fun ret scr' m' _ hlen hcore hpres hres _ hm' => by
       obtain ⟨hret_n, hctrl, _, _⟩ := (hres 64 8192 nvM7Cong_ctrl_ok).2 (by decide) (by decide)
       have hret : ret = 16384#64 := BitVec.eq_of_toNat_eq (hret_n.trans (by decide))
       have hctrl' : M7CongHtCtrlOk nvM7CongCfg scr' 0 64 16384 := by simpa using hctrl
       rw [sep_emp] at hm'
       exact ⟨_, hret, hcore, hlen, hpres, hctrl', hm'⟩⟩

/-- Concrete `Mem 64` NV (`XPost := False`): `full_cong_ht_insert_m7` inserts gate `ent = 8` into
the `8,192`-bucket `nvM7CongMem` while preserving `FullState.core`, `LengthsOk`, and `FullMem`. -/
theorem nv_m7_cong_ht_insert :
    Func.wp m7CongHashEnv full_cong_ht_insert_m7_body
      (nvM7CongCfg.hdr, 0#64, 8#32, ()) nvM7CongMem
      (fun (ret, ()) m' => ∃ s',
        PreservesCoreSlice FullState.core nvM7CongState s' ∧ s'.LengthsOk nvM7CongCfg ∧
        FullExtScratchPres nvM7CongState s' ∧
        (∃ new_sz, (new_sz = 8192 ∨ new_sz = 16384) ∧
          M7CongHtCtrlOk nvM7CongCfg s'.scratch.scratch_buf 0 64 new_sz) ∧
        (ret = 0xFFFFFFFF#32 ∨ ret = 8#32 ∨ ret.toNat < 64) ∧
        FullMem nvM7CongCfg s' m')
      (fun _ _ _ _ => False) :=
  m7CongHash_tableImpl.2.2.2.2.1.2 _ _ _ _
    ⟨nvM7CongCfg, nvM7CongState, emp, rfl, nvM7Cong_lengths, nvM7CongMem_sep,
     fun ret scr' _ m' _ hlen hcore hpres _ hctrl_all hret hm' => by
       obtain ⟨nsz, hctrl', hsz, _, _, _⟩ := hctrl_all 64 8192 nvM7Cong_ctrl_ok
       have hsz' : nsz = 8192 ∨ nsz = 16384 := by
         rcases hsz with rfl | rfl
         · exact Or.inl rfl
         · exact Or.inr rfl
       have hctrl0 : M7CongHtCtrlOk nvM7CongCfg scr' 0 64 nsz := hctrl'
       rw [sep_emp] at hm'
       have hret' : ret = 0xFFFFFFFF#32 ∨ ret = 8#32 ∨ ret.toNat < 64 := by
         rcases hret with h | h | ⟨ho, _, _, hok, _, _, hlt⟩
         · exact Or.inl h
         · exact Or.inr (Or.inl h)
         · have hm6 := hok.2.2.2.2.2.1; have hc6 := hctrl'.2.2.2.2.2.1
           rw [hm6, Option.some.injEq] at hc6
           have h1 := hok.2.2.2.1
           have h64 : ho = 64 := by
             have htn := congrArg BitVec.toNat hc6
             rwa [bv32_ofNat_toNat_lt (by omega),
               bv32_ofNat_toNat_lt (by have := hctrl'.2.2.2.1; omega)] at htn
           exact Or.inr (Or.inr (h64 ▸ hlt))
       exact ⟨_, hcore, hlen, hpres, ⟨nsz, hsz', hctrl0⟩, hret', hm'⟩⟩

end NonVacuity

end LeanQbe.T.Examples.Kissat.FullM7CongHash
