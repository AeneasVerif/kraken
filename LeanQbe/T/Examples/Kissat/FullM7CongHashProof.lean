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
# Kissat M7 Dynamic Congruence Hash Table Proofs (`FullM7CongHashProof`)

M1-clean verification (`public section`, `0` `@[expose]`, `0` `import all`, `0` `maxHeartbeats`,
`0` `bv_decide`):
1. `M7CongHtCtrlOk` / `M7CongHtInv` invariants and bridges to `FullCongSpecs.CongHtInv`.
2. Parametric `(Γ : Env)` `Func.wp` proofs for all `6` functions (`full_cong_ht_hash_ent_m7`,
   `full_cong_ht_init_m7`, `full_cong_ht_grow_m7`, `full_cong_ht_grow_clear_m7`,
   `full_cong_ht_lookup_m7`, `full_cong_ht_insert_m7`) preserving
   `SafetySlice.spec (fullSafetySlice c)` (`FullState.core` + `LengthsOk c`), `FullExtScratchPres`,
   and prefix `scratch_buf`.
3. Closed `6`-row `m7CongHashSpecTable`, `m7CongHashEnv`, `m7CongHash_moduleOk`, and
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

/-! ## 2b. Lookup/Insert Specs & Closed `6`-Row Environment -/

section Specs

abbrev m7CongHashTmpStep (acc : BitVec 64) (w : BitVec 32) : BitVec 64 :=
  acc * 0x85EBCA77#64 + w.setWidth 64 + 1#64

abbrev m7CongHashTmpGo : Nat → BitVec 64 → Nat → List (BitVec 32) → BitVec 64
  | 0, acc, _, _ => acc
  | n + 1, acc, idx, tmp =>
      m7CongHashTmpGo n (m7CongHashTmpStep acc (tmp[idx]?.getD 0#32)) (idx + 1) tmp

abbrev m7CongHashTmp (htag harity : BitVec 32) (tmp : List (BitVec 32)) : BitVec 64 :=
  m7CongHashTmpGo harity.toNat (htag.setWidth 64 * 0x9E3779B1#64 + harity.setWidth 64) 0 tmp

abbrev m7CongSlotMatch (scr : List (BitVec 32)) (ht_off : Nat)
    (htag harity : BitVec 32) (tmp : List (BitVec 32)) (ent : BitVec 32) : Prop :=
  ent ≠ 0xFFFFFFFF#32 ∧ ent.toNat + 2 + harity.toNat ≤ ht_off ∧
  ∃ mw : BitVec 32, scr[ent.toNat + 1]? = some mw ∧
    (mw >>> 28) = htag ∧ (mw &&& 0xFF#32) = harity ∧
    ∀ j < harity.toNat, scr[ent.toNat + 2 + j]? = tmp[j]?

/-- **#4 (`full_cong_ht_lookup_m7`)**: read-only linear probe for `(htag, harity, tmp[0..<harity])`,
returning `0xFFFFFFFF#32` (with probe-chain completeness along `slot0`) or a verified matching gate
offset in `scr[ht_off ..< ht_off + ht_sz)`. -/
abbrev m7CongHtLookupSpec : Spec [i64, i64, i32, i32] [i32] :=
  fun (h, ctrl_off, htag, harity, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ ret : BitVec 32,
        ((ret = 0xFFFFFFFF#32 ∧
          ∀ ht_off ht_sz,
            M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ht_off ht_sz →
            harity.toNat ≤ 31 → harity.toNat ≤ c.max_vars →
            let slot0 := (m7CongHashTmp htag harity s.core.tmp).toNat % ht_sz
            ∀ kp < ht_sz,
              (∀ m0 ≤ kp,
                s.scratch.scratch_buf[ht_off + (slot0 + m0) % ht_sz]? ≠ some 0xFFFFFFFF#32) →
              ∀ ent, s.scratch.scratch_buf[ht_off + (slot0 + kp) % ht_sz]? = some ent →
                ¬ m7CongSlotMatch s.scratch.scratch_buf ht_off htag harity s.core.tmp ent) ∨
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
while preserving `FullState.core`, `LengthsOk c`, `FullExtScratchPres`, prefix `scratch_buf`,
and all existing table entries. -/
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
            ((∃ mw : BitVec 32, s.scratch.scratch_buf[ent.toNat + 1]? = some mw ∧
                (mw &&& 0xFF#32).toNat ≤ 31 ∧
                ent.toNat + 2 + (mw &&& 0xFF#32).toNat ≤ ht_off) →
              (old_sz ≤ s.scratch.res_sz.toNat ∨ 3 * old_sz ≤ 4 * s.scratch.res_sz.toNat) →
              old_sz < m7CongHashMaxSz → ht_off + 2 * old_sz ≤ c.scratch_cap →
              new_sz = 2 * old_sz) ∧
            (¬ ((old_sz ≤ s.scratch.res_sz.toNat ∨
                3 * old_sz ≤ 4 * s.scratch.res_sz.toNat) ∧
                old_sz < m7CongHashMaxSz ∧ ht_off + 2 * old_sz ≤ c.scratch_cap) →
              new_sz = old_sz) ∧
            (∀ idx < ht_off, idx ≠ ctrl_off.toNat + 7 →
              scr'[idx]? = s.scratch.scratch_buf[idx]?) ∧
            (∀ v : BitVec 32, v.toNat < ht_off →
              (∃ k0 < old_sz, s.scratch.scratch_buf[ht_off + k0]? = some v) →
              ∃ j < new_sz, scr'[ht_off + j]? = some v) ∧
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
              (∀ j < new_sz, scr'[ht_off + j]? ≠ some 0xFFFFFFFF#32) ∧
              (new_sz = old_sz → scr' = s.scratch.scratch_buf) ∧
              ¬ ((old_sz ≤ s.scratch.res_sz.toNat ∨
                  3 * old_sz ≤ 4 * s.scratch.res_sz.toNat) ∧
                  old_sz < m7CongHashMaxSz ∧ ht_off + 2 * old_sz ≤ c.scratch_cap))) →
        (ret = 0xFFFFFFFF#32 ∨ ret = ent ∨
          ∃ ht_off new_sz k mw_e mw_c,
            M7CongHtCtrlOk c scr' ctrl_off.toNat ht_off new_sz ∧
            k < new_sz ∧ scr'[ht_off + k]? = some ret ∧ ret.toNat < ht_off ∧
            s.scratch.scratch_buf[ent.toNat + 1]? = some mw_e ∧
            scr'[ret.toNat + 1]? = some mw_c ∧
            (mw_c >>> 28) = (mw_e >>> 28) ∧ (mw_c &&& 0xFF#32) = (mw_e &&& 0xFF#32) ∧
            ret.toNat + 2 + (mw_e &&& 0xFF#32).toNat ≤ ht_off ∧
            ∀ j < (mw_e &&& 0xFF#32).toNat,
              scr'[ret.toNat + 2 + j]? = scr'[ent.toNat + 2 + j]?) →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

theorem m7CongHtInsertSpec_noExit : ∀ a m Q X,
    m7CongHtInsertSpec a m Q X → m7CongHtInsertSpec a m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

/-- Closed `6`-row specification table for `m7CongHashModule`. -/
abbrev m7CongHashSpecTable : List SpecEntry :=
  [ .ofFn full_cong_ht_hash_ent_m7 m7CongHtHashEntSpec true
  , .ofFn full_cong_ht_init_m7 m7CongHtInitSpec true
  , .ofFn full_cong_ht_grow_m7 m7CongHtGrowSpec true
  , .ofFn full_cong_ht_grow_clear_m7 m7CongHtGrowClearSpec true
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
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

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
  have hfail_no : (∀ ho hs, M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ho hs →
      harity.toNat ≤ 31 → harity.toNat ≤ c.max_vars → False) →
      Q (0xFFFFFFFF#32, ()) m0 := fun hno =>
    hQ 0xFFFFFFFF#32 (Or.inl ⟨rfl, fun ho hs hok h31 hmv =>
      False.elim (hno ho hs hok h31 hmv)⟩)
  unfold Func.wp full_cong_ht_lookup_m7_body
  c0_hsplit
  · c0_hsteps; exact hfail_no (fun _ _ hok _ _ => by
      have := hok.2.1; have := hok.2.2.1; m7_omega)
  · have hco_le : ctrl_off.toNat ≤ c.scratch_cap := by m7_omega
    clear hc; c0_hsplit
    · c0_hsteps; exact hfail_no (fun _ _ hok _ _ => by
        have := ctrl_off.isLt; have := hok.2.1; have := hok.2.2.1; m7_omega)
    · have hco8 : ctrl_off.toNat + 8 ≤ c.scratch_cap := by
        have := ctrl_off.isLt; m7_omega
      clear hc; c0_hsplit
      · c0_hsteps; exact hfail_no (fun _ _ _ h31 _ => by m7_omega)
      · have hha31 : harity.toNat ≤ 31 := by m7_omega
        clear hc; c0_hsplit
        · c0_hsteps; exact hfail_no (fun _ _ _ _ hmv => by m7_omega)
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
          have hbad_ht : ¬ (ctrl_off.toNat + 8 ≤ ht_off.toNat ∧ ht_off.toNat < c.scratch_cap ∧
              ht_off.toNat ≤ 0x7FFFFFFF) →
              ∀ ho hs, M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ho hs → False :=
            fun hbad ho hs hok => by
              apply hbad
              obtain ⟨rfl, rfl⟩ := m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
              exact ⟨hok.2.1, Nat.lt_of_lt_of_le (by
                  have ⟨k, _, he⟩ := hok.2.2.2.2.1; have := Nat.two_pow_pos k; omega) hok.2.2.1,
                hok.2.2.2.1⟩
          c0_hsplit
          · c0_hsteps; exact hfail_no (fun ho hs hok _ _ => hbad_ht (fun ⟨h1, _⟩ => by
              rw [hs6a, hht_nat] at hc
              change ht_off.toNat < (ctrl_off.toNat + BitVec.toNat 8) % 2 ^ 64 at hc
              m7_omega) ho hs hok)
          · have h1 : ctrl_off.toNat + 8 ≤ ht_off.toNat := by
              rw [hs6a, hht_nat] at hc
              change ¬ ht_off.toNat < (ctrl_off.toNat + BitVec.toNat 8) % 2 ^ 64 at hc
              m7_omega
            clear hc; c0_hsplit
            · c0_hsteps; exact hfail_no (fun ho hs hok _ _ => hbad_ht (fun ⟨_, h2, _⟩ => by
                rw [hs6a, hht_nat] at hc
                change c.scratch_cap % 2 ^ 64 ≤ ht_off.toNat at hc; m7_omega) ho hs hok)
            · have h2 : ht_off.toNat < c.scratch_cap := by
                rw [hs6a, hht_nat] at hc
                change ¬ c.scratch_cap % 2 ^ 64 ≤ ht_off.toNat at hc; m7_omega
              clear hc; c0_hsplit
              · c0_hsteps; exact hfail_no (fun ho hs hok _ _ => hbad_ht (fun ⟨_, _, h3⟩ => by
                  rw [hs6a, hht_nat] at hc
                  change BitVec.toNat 2147483647 < ht_off.toNat at hc; m7_omega) ho hs hok)
              · have h3 : ht_off.toNat ≤ 0x7FFFFFFF := by
                  rw [hs6a, hht_nat] at hc
                  change ¬ BitVec.toNat 2147483647 < ht_off.toNat at hc; m7_omega
                clear hc
                have hbad_sz : ¬ (16 ≤ ht_sz.toNat ∧ ht_sz.toNat ≤ 131072 ∧
                    (ht_sz &&& (ht_sz - 1#64)) = 0#64 ∧
                    ht_sz.toNat ≤ c.scratch_cap - ht_off.toNat) →
                    ∀ ho hs, M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ho hs →
                      False :=
                  fun hbad ho hs hok => by
                    apply hbad
                    obtain ⟨rfl, rfl⟩ := m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                    obtain ⟨k, hk, he⟩ := hok.2.2.2.2.1
                    refine ⟨by rw [he]; have := Nat.two_pow_pos k; omega,
                      by rw [he]; exact pow2_16_mul_le k hk,
                      bv64_pow2_and_sub1_zero hk he,
                      by have := hok.2.2.1; omega⟩
                c0_hsplit
                · c0_hsteps; exact hfail_no (fun ho hs hok _ _ => hbad_sz (fun ⟨h4, _⟩ => by
                    rw [hs7a, hsz_nat] at hc
                    change ht_sz.toNat < BitVec.toNat 16 at hc; m7_omega) ho hs hok)
                · have h4 : 16 ≤ ht_sz.toNat := by
                    rw [hs7a, hsz_nat] at hc
                    change ¬ ht_sz.toNat < BitVec.toNat 16 at hc; m7_omega
                  clear hc; c0_hsplit
                  · c0_hsteps; exact hfail_no (fun ho hs hok _ _ => hbad_sz (fun ⟨_, hm, _⟩ => by
                      rw [hs7a, hsz_nat] at hc
                      change BitVec.toNat 131072 < ht_sz.toNat at hc; m7_omega) ho hs hok)
                  · have hmax : ht_sz.toNat ≤ 131072 := by
                      rw [hs7a, hsz_nat] at hc
                      change ¬ BitVec.toNat 131072 < ht_sz.toNat at hc; m7_omega
                    clear hc; c0_hsplit
                    · c0_hsteps; exact hfail_no (fun ho hs hok _ _ => hbad_sz
                        (fun ⟨_, _, h5, _⟩ => by rw [hs7a] at hc; exact hc h5) ho hs hok)
                    · have h5 : (ht_sz &&& (ht_sz - 1#64)) = 0#64 := by
                        rw [hs7a] at hc; exact hc
                      clear hc; c0_hsplit
                      · c0_hsteps; exact hfail_no (fun ho hs hok _ _ => hbad_sz
                          (fun ⟨_, _, _, h6⟩ => by
                            rw [hs6a, hht_nat, hs7a, hsz_nat] at hc
                            change (2 ^ 64 - ht_off.toNat + c.scratch_cap) % 2 ^ 64 <
                              ht_sz.toNat at hc
                            have := ht_off.isLt; m7_omega) ho hs hok)
                      · have h6 : ht_sz.toNat ≤ c.scratch_cap - ht_off.toNat := by
                          rw [hs6a, hht_nat, hs7a, hsz_nat] at hc
                          change ¬ (2 ^ 64 - ht_off.toNat + c.scratch_cap) % 2 ^ 64 <
                            ht_sz.toNat at hc
                          have := ht_off.isLt; m7_omega
                        clear hc
                        have hctrl_ok : M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat
                            ht_off.toNat ht_sz.toNat :=
                          m7CongHtCtrlOk_from_reads hscrl hco8 hho_eq hsz_eq h1 h2 h3 h4 h5 h6 hmax
                        obtain ⟨k_sz, hk_sz, hpow_sz⟩ := hctrl_ok.2.2.2.2.1
                        have hpos_sz : 0 < ht_sz.toNat := by
                          rw [hpow_sz]; have := Nat.two_pow_pos k_sz; omega
                        let hv_fin : BitVec 64 := m7CongHashTmp htag harity s.core.tmp
                        c0_hsteps_nogrp
                        refine wp_loop_inv (ts := [i64, i64])
                          (fun ⟨hv, hi, ⟨⟩⟩ mi => mi = m0 ∧ hi.toNat ≤ harity.toNat ∧
                            m7CongHashTmpGo (harity.toNat - hi.toNat) hv hi.toNat s.core.tmp =
                              hv_fin)
                          (fun ⟨_, hi, ⟨⟩⟩ _ => harity.toNat - hi.toNat)
                          (fun J hJ => by
                            c0_hsteps
                            refine hJ (_, 0#64, ()) m0 ⟨rfl, Nat.zero_le _, ?_⟩
                            simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero]
                            rfl)
                          (fun J ⟨hv, hi, ⟨⟩⟩ mi ⟨hmi, hi_le, hhv⟩ ih => ?_)
                        subst mi
                        c0_hsplit
                        · have hi_lt : hi.toNat < harity.toNat := by m7_omega
                          have hi_tmp : hi.toNat < s.core.tmp.length := by omega
                          have hi1_n : (hi + 1#64).toNat = hi.toNat + 1 :=
                            bv64_add1_lt hi_lt (by omega)
                          have hstep : m7CongHashTmpGo (harity.toNat - (hi + 1#64).toNat)
                              (hv * 0x85EBCA77#64 +
                                (s.core.tmp[hi.toNat]'hi_tmp).setWidth 64 + 1#64)
                              (hi + 1#64).toNat s.core.tmp = hv_fin := by
                            rw [hi1_n, ← hhv]
                            obtain ⟨rem, hrem⟩ : ∃ rem, harity.toNat - hi.toNat = rem + 1 :=
                              ⟨harity.toNat - hi.toNat - 1, by omega⟩
                            have hsub : harity.toNat - (hi.toNat + 1) = rem := by omega
                            rw [hrem, hsub]
                            simp only [m7CongHashTmpGo, m7CongHashTmpStep,
                              List.getElem?_eq_getElem hi_tmp, Option.getD_some]
                          c0_hsteps
                          exact ih (_, hi + 1#64, ()) m0 (by dsimp only; omega)
                            ⟨rfl, by omega, hstep⟩
                        · have hi_eq : hi.toNat = harity.toNat := by m7_omega
                          rw [hi_eq, Nat.sub_self] at hhv
                          dsimp only [m7CongHashTmpGo] at hhv
                          have hv_eq : hv = hv_fin := hhv
                          clear hc; c0_hsteps_nogrp
                          refine wp_loop_inv (ts := [i64, i64])
                            (fun ⟨slot, p, ⟨⟩⟩ mp => mp = m0 ∧ slot.toNat < ht_sz.toNat ∧
                              slot.toNat = (hv_fin.toNat + p.toNat) % ht_sz.toNat ∧
                              p.toNat ≤ ht_sz.toNat ∧
                              (∀ m1 < p.toNat, s.scratch.scratch_buf[ht_off.toNat +
                                (hv_fin.toNat + m1) % ht_sz.toNat]? ≠ some 0xFFFFFFFF#32) ∧
                              ∀ m1 < p.toNat, ∀ e, s.scratch.scratch_buf[ht_off.toNat +
                                (hv_fin.toNat + m1) % ht_sz.toNat]? = some e →
                                ¬ m7CongSlotMatch s.scratch.scratch_buf ht_off.toNat htag harity
                                  s.core.tmp e)
                            (fun ⟨_, p, ⟨⟩⟩ _ => ht_sz.toNat - p.toNat)
                            (fun Jp hJp => by
                              c0_hsteps; try simp only [hs7b]
                              exact hJp (hv &&& (ht_sz - 1#64), 0#64, ()) m0
                                ⟨rfl, bv64_and_sub1_lt (by omega), by
                                  rw [hv_eq, bv64_and_pow2_mod hk_sz hpow_sz]; simp,
                                  Nat.zero_le _, fun _ h => by simp at h,
                                  fun _ h => by simp at h⟩)
                            (fun Jp ⟨slot, p, ⟨⟩⟩ mp
                                ⟨hmp, hslot_lt, hslot_mod, hp_le, hnoem, hnom⟩ ihp => ?_)
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
                            · have hent_eq : ent = 0xFFFFFFFF#32 := by
                                simp only [hs6a, hht_nat] at hc; exact hc
                              c0_hsteps
                              refine hQ 0xFFFFFFFF#32 (Or.inl ⟨rfl,
                                fun ho hs hok _ _ kp hkp hne_kp e he_kp => ?_⟩)
                              obtain ⟨rfl, rfl⟩ :=
                                m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                              have hmod_slot : ∀ x, ((m7CongHashTmp htag harity s.core.tmp).toNat %
                                    ht_sz.toNat + x) % ht_sz.toNat =
                                  (hv_fin.toNat + x) % ht_sz.toNat := fun x => by
                                dsimp only [hv_fin]; rw [Nat.mod_add_mod]
                              rcases Nat.lt_or_ge kp p.toNat with hkp_lt | hge
                              · rw [hmod_slot kp] at he_kp
                                exact hnom kp hkp_lt e he_kp
                              · have hbad := hne_kp p.toNat hge
                                rw [hmod_slot p.toNat, ← hslot_mod, hent_get, hent_eq] at hbad
                                exact False.elim (hbad rfl)
                            · have hent_ne : ent ≠ 0xFFFFFFFF#32 := by
                                simp only [hs6a, hht_nat] at hc; exact hc
                              clear hc; c0_hsteps_nogrp
                              have hp1_n : (p + 1#64).toNat = p.toNat + 1 :=
                                bv64_add1_lt hp_lt (by omega)
                              refine wp_join0 (fun m2 => m2 = m0 ∧
                                ¬ m7CongSlotMatch s.scratch.scratch_buf ht_off.toNat htag harity
                                  s.core.tmp ent)
                                (fun _ m2 ⟨hm2, hno_ent⟩ => by
                                  subst m2; c0_hsteps; try simp only [hs7b]
                                  have hnext_slot :
                                      ((slot + 1#64) &&& (ht_sz - 1#64)).toNat =
                                      (hv_fin.toNat + (p + 1#64).toNat) % ht_sz.toNat := by
                                    rw [bv64_and_pow2_mod hk_sz hpow_sz,
                                      bv64_add1_lt hslot_lt (by omega), hp1_n]
                                    exact mod_add_one_eq hslot_mod
                                  refine ihp ((slot + 1#64) &&& (ht_sz - 1#64), p + 1#64, ()) m0
                                    (by dsimp only; omega)
                                    ⟨rfl, bv64_and_sub1_lt (by omega), hnext_slot, by omega,
                                      fun m1 hm1 => ?_, fun m1 hm1 e he => ?_⟩
                                  · rw [hp1_n] at hm1
                                    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hm1)
                                        with h1 | rfl
                                    · exact hnoem m1 h1
                                    · rw [← hslot_mod, hent_get]
                                      intro heq; exact hent_ne (Option.some.inj heq)
                                  · rw [hp1_n] at hm1
                                    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hm1)
                                        with h1 | rfl
                                    · exact hnom m1 h1 e he
                                    · rw [← hslot_mod, hent_get, Option.some.injEq] at he
                                      subst he; exact hno_ent)
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
                                refine wp_join0 (fun m3 => m3 = m0 ∧
                                  ¬ m7CongSlotMatch s.scratch.scratch_buf ht_off.toNat htag harity
                                    s.core.tmp ent) ?_ (fun J3 hJ3 => ?_)
                                · rintro _ m3 ⟨hm3, hno⟩; subst m3
                                  c0_hsteps; exact hJ2 m0 ⟨rfl, hno⟩
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
                                            s.core.tmp[j]?) ∧
                                        (eq_b = 0#32 → ∃ j < harity.toNat,
                                          s.scratch.scratch_buf[ent.toNat + 2 + j]? ≠
                                            s.core.tmp[j]?))
                                      (fun rem (k, ()) mk => mk = m0 ∧ k.toNat ≤ harity.toNat ∧
                                        rem = harity.toNat - k.toNat ∧
                                        ∀ j < k.toNat,
                                          s.scratch.scratch_buf[ent.toNat + 2 + j]? =
                                            s.core.tmp[j]?)
                                      ?_ ?_ ?_
                                    · rintro _ ⟨eq_b, kb, ⟨⟩⟩ mb ⟨hmb, heq_ok, heq_ne⟩; subst mb
                                      c0_hsplit
                                      · have hne0 : eq_b ≠ 0#32 := hc
                                        c0_hsteps
                                        exact hQ ent (Or.inr ⟨ht_off.toNat, ht_sz.toNat, slot.toNat,
                                          mw, hctrl_ok, hha31, hha_mv, hslot_lt, hent_get, hfit_ent,
                                          hmw_get, htag_eq, har_eq, heq_ok hne0⟩)
                                      · have he0 : eq_b = 0#32 := hc
                                        c0_hsteps
                                        refine hJ3 m0 ⟨rfl, fun hmatch => ?_⟩
                                        obtain ⟨j, hj, hne_j⟩ := heq_ne he0
                                        obtain ⟨_, _, _, _, _, _, htmp⟩ := hmatch
                                        exact hne_j (htmp j hj)
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
                                        · c0_hsteps
                                          refine hBk (0#32, k, ()) m0
                                            ⟨rfl, fun h => absurd rfl h, fun _ => ⟨k.toNat, hk_lt,
                                              fun heq => ?_⟩⟩
                                          have he2k_mod :
                                              (ent.toNat + BitVec.toNat (2 : BitVec 64) +
                                              k.toNat) % 2 ^ 64 =
                                              (ent.setWidth 64 + 2#64 + k).toNat := by
                                            rw [he2k_n]
                                            have h2n : BitVec.toNat (2 : BitVec 64) = 2 := rfl
                                            rw [h2n, Nat.mod_eq_of_lt (by omega)]
                                          rw [List.getElem?_eq_getElem (by rw [hscrl]; omega),
                                            List.getElem?_eq_getElem hk_tmp,
                                            Option.some.injEq] at heq
                                          apply hc
                                          rw [← list_getElem_congr he2k_mod.symm he2k_arr
                                            (by rw [he2k_mod]; exact he2k_arr),
                                            list_getElem_congr he2k_n he2k_arr
                                              (by rw [hscrl]; omega)]
                                          exact heq
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
                                        c0_hsteps; exact hBk (1#32, k, ()) m0
                                          ⟨rfl, fun _ => hpre_k, fun h => absurd h (by decide)⟩
                                    · intro _ Lk _ hLk; c0_hsteps
                                      exact hLk harity.toNat (0#64, ()) m0
                                        ⟨rfl, Nat.zero_le _, rfl, fun _ h => by simp at h⟩
                                  · c0_hsteps; refine hJ3 m0 ⟨rfl, fun hmatch => ?_⟩
                                    obtain ⟨_, _, mw', hmw', _, har', _⟩ := hmatch
                                    rw [hmw_get, Option.some.injEq] at hmw'; subst hmw'
                                    try simp only [hs6a, hht_nat] at hc
                                    rw [hmw_congr] at hc; exact hc har'
                                · c0_hsteps; refine hJ3 m0 ⟨rfl, fun hmatch => ?_⟩
                                  obtain ⟨_, _, mw', hmw', htag', _, _⟩ := hmatch
                                  rw [hmw_get, Option.some.injEq] at hmw'; subst hmw'
                                  try simp only [hs6a, hht_nat] at hc
                                  rw [hmw_congr] at hc; exact hc htag'
                              · c0_hsteps; refine hJ2 m0 ⟨rfl, fun hmatch => ?_⟩
                                have hfit' := hmatch.2.1
                                simp only [hs6a, hht_nat, hent_hc] at hc
                                have h2n : BitVec.toNat (2 : BitVec 64) = 2 := rfl
                                have hmod : (ent.toNat + BitVec.toNat (2 : BitVec 64) +
                                    harity.toNat) % 2 ^ 64 = ent.toNat + 2 + harity.toNat := by
                                  rw [h2n, Nat.mod_eq_of_lt (by m7_omega)]
                                rw [hmod] at hc; omega
                          · have hp_eq : p.toNat = ht_sz.toNat := by
                              rw [hs7a, hsz_nat] at hc
                              exact Nat.le_antisymm hp_le (Nat.not_lt.mp hc)
                            rw [hp_eq] at hnom
                            c0_hsteps
                            refine hQ 0xFFFFFFFF#32 (Or.inl ⟨rfl,
                              fun ho hs hok _ _ kp hkp _ e he_kp => ?_⟩)
                            obtain ⟨rfl, rfl⟩ :=
                              m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                            have hmod_slot : ((m7CongHashTmp htag harity s.core.tmp).toNat %
                                  ht_sz.toNat + kp) % ht_sz.toNat =
                                (hv_fin.toNat + kp) % ht_sz.toNat := by
                              dsimp only [hv_fin]; rw [Nat.mod_add_mod]
                            rw [hmod_slot] at he_kp
                            exact hnom kp hkp e he_kp

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
                    have hkeep_id : ∀ v : BitVec 32, v.toNat < ht_off.toNat →
                        (∃ k0 < old_sz.toNat,
                          s.scratch.scratch_buf[ht_off.toNat + k0]? = some v) →
                        ∃ j < old_sz.toNat,
                          s.scratch.scratch_buf[ht_off.toNat + j]? = some v := fun _ _ h => h
                    c0_hsplit
                    · c0_hsteps; refine hQ 0xFFFFFFFF#32 s.scratch.scratch_buf s.scratch.res_sz m0
                        hscrl hlen rfl ⟨rfl, rfl⟩ (Or.inl rfl) (fun ho os hok => ?_) (Or.inl rfl)
                        hm0
                      obtain ⟨rfl, rfl⟩ := m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                      have hbad : ∀ mw' : BitVec 32,
                          ent.toNat + 2 + (mw' &&& 0xFF#32).toNat ≤ ht_off.toNat → False :=
                        fun _ hbd => by
                          rw [hs6a, hht_nat] at hc
                          rw [Nat.mod_eq_of_lt (by m7_omega)] at hc; m7_omega
                      refine ⟨old_sz.toNat, hok_read, Or.inl rfl, hmax,
                        fun ⟨mw', _, _, hbd⟩ _ _ _ => False.elim (hbad mw' hbd),
                        fun _ => rfl, fun _ _ _ => rfl, hkeep_id, horig_id,
                        fun _ mw' _ _ hbd => ⟨fun _ _ => False.elim (hbad mw' hbd),
                          fun _ => rfl, fun _ => hbad mw' hbd⟩⟩
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
                        have hbad31 : ∀ mw' : BitVec 32,
                            s.scratch.scratch_buf[ent.toNat + 1]? = some mw' →
                            (mw' &&& 0xFF#32).toNat ≤ 31 → False := fun mw' hmw' h31 => by
                          rw [hmw_get, Option.some.injEq] at hmw'; subst hmw'
                          rw [hs_e1] at hc
                          have h255 : (mw &&& (255 : BitVec 32)) = (mw &&& 0xFF#32) := rfl
                          change (31 : Nat) < (mw &&& (255 : BitVec 32)).toNat at hc
                          rw [h255] at hc; omega
                        refine ⟨old_sz.toNat, hok_read, Or.inl rfl, hmax,
                          fun ⟨mw', hmw', h31, _⟩ _ _ _ => False.elim (hbad31 mw' hmw' h31),
                          fun _ => rfl, fun _ _ _ => rfl, hkeep_id, horig_id,
                          fun _ mw' hmw' h31 _ => ⟨fun _ _ => False.elim (hbad31 mw' hmw' h31),
                            fun _ => rfl, fun _ => hbad31 mw' hmw' h31⟩⟩
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
                          have hbad_fit : ∀ mw' : BitVec 32,
                              s.scratch.scratch_buf[ent.toNat + 1]? = some mw' →
                              ent.toNat + 2 + (mw' &&& 0xFF#32).toNat ≤ ht_off.toNat →
                              False := fun mw' hmw' hbd => by
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
                            omega
                          refine ⟨old_sz.toNat, hok_read, Or.inl rfl, hmax,
                            fun ⟨mw', hmw', _, hbd⟩ _ _ _ => False.elim (hbad_fit mw' hmw' hbd),
                            fun _ => rfl, fun _ _ _ => rfl, hkeep_id, horig_id,
                            fun _ mw' hmw' _ hbd => ⟨fun _ _ => False.elim (hbad_fit mw' hmw' hbd),
                              fun _ => rfl, fun _ => hbad_fit mw' hmw' hbd⟩⟩
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
                              ((old_sz.toNat ≤ s.scratch.res_sz.toNat ∨
                                  3 * old_sz.toNat ≤ 4 * s.scratch.res_sz.toNat) →
                                old_sz.toNat < m7CongHashMaxSz →
                                ht_off.toNat + 2 * old_sz.toNat ≤ c.scratch_cap →
                                ht_sz1.toNat = 2 * old_sz.toNat ∧
                                  ∃ j < ht_sz1.toNat, scr1[ht_off.toNat + j]? =
                                    some 0xFFFFFFFF#32) ∧
                              (¬ ((old_sz.toNat ≤ s.scratch.res_sz.toNat ∨
                                  3 * old_sz.toNat ≤ 4 * s.scratch.res_sz.toNat) ∧
                                  old_sz.toNat < m7CongHashMaxSz ∧
                                  ht_off.toNat + 2 * old_sz.toNat ≤ c.scratch_cap) →
                                ht_sz1.toNat = old_sz.toNat ∧ scr1 = s.scratch.scratch_buf) ∧
                              (∀ idx < ht_off.toNat, idx ≠ ctrl_off.toNat + 7 →
                                scr1[idx]? = s.scratch.scratch_buf[idx]?) ∧
                              (∀ v : BitVec 32, v.toNat < ht_off.toNat →
                                (∃ k0 < old_sz.toNat,
                                  s.scratch.scratch_buf[ht_off.toNat + k0]? = some v) →
                                ∃ j < ht_sz1.toNat, scr1[ht_off.toNat + j]? = some v) ∧
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
                              ⟨scr1, hscr1l, hctrl1, hsz_cases, hsz1_max,
                                hgrow1, hnogrow1, hpre1, hkeep1, hslot1, hm1⟩
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
                                refine ⟨ht_sz1.toNat, hctrl2, hsz_cases, hsz1_max,
                                  fun _ hneed hlt hfit => (hgrow1 hneed hlt hfit).1,
                                  fun hnot => (hnogrow1 hnot).1, ?_, ?_, ?_,
                                  fun hff => absurd hff hent_ne_ff⟩
                                · intro idx hi hne7
                                  rw [List.getElem?_set_ne (by omega)]
                                  exact hpre1 idx hi hne7
                                · intro v hv_lt hex
                                  obtain ⟨j, hj, hj_get⟩ := hkeep1 v hv_lt hex
                                  have hj_ne : j ≠ slot.toNat := by
                                    intro hjs; subst hjs
                                    have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 0xFFFFFFFF := by
                                      decide
                                    have hcur_eq : cur = 0xFFFFFFFF#32 := by
                                      simp only [hs6a, hht_nat] at hc; exact hc
                                    rw [hj_get, Option.some.injEq] at hcur_get
                                    rw [hcur_get, hcur_eq, hff] at hv_lt; omega
                                  refine ⟨j, hj, ?_⟩
                                  rw [List.getElem?_set_ne (by omega)]; exact hj_get
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
                                  refine ⟨ht_sz1.toNat, hctrl1, hsz_cases, hsz1_max,
                                    fun _ hneed hlt hfit => (hgrow1 hneed hlt hfit).1,
                                    fun hnot => (hnogrow1 hnot).1, hpre1, hkeep1, ?_,
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
                                    let mw_c := scr1[(cur.setWidth 64 + 1#64).toNat]'hc1_arr
                                    have hmw_c_get : scr1[cur.toNat + 1]? = some mw_c := by
                                      rw [List.getElem?_eq_getElem (by rw [hscr1l]; omega)]
                                      congr 1; exact (list_getElem_congr
                                        (bv64_zext32_add_ofNat cur 1 (by decide)) hc1_arr _).symm
                                    have hmw_c_congr : scr1[(cur.toNat +
                                        BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                                        change (cur.toNat + 1) % 2 ^ 64 < scr1.length
                                        rw [Nat.mod_eq_of_lt (by omega), hscr1l]; omega) = mw_c :=
                                      (scr_idx_zext32_add1 (e := cur)
                                        (by rw [hscr1l]; omega) _).trans
                                        (list_getElem_congr
                                          (bv64_zext32_add_ofNat cur 1 (by decide)).symm
                                          (by rw [hscr1l]; omega) hc1_arr)
                                    have hcur_eq : s1.scratch.scratch_buf[(ht_off.toNat +
                                        BitVec.toNat slot) % 2 ^ 64]'(by
                                        rw [hs1_scrl, Nat.mod_eq_of_lt (by omega)]; omega) = cur :=
                                      rfl
                                    clear hc; try simp only [hs6b]
                                    c0_hsteps_nogrp
                                    refine wp_join0 (fun m3 => m3 = m1)
                                      (fun _ m3 hm3 => by subst m3; c0_hsteps; exact hJ2 m1 rfl)
                                      (fun J3 hJ3 => ?_)
                                    c0_hsplit
                                    · have htag_c : (mw_c >>> 28) = (mw >>> 28) := by
                                        try simp only [hht_nat, hcur_eq] at hc
                                        rw [hmw_c_congr, hs_e1] at hc; exact hc
                                      clear hc; c0_hsplit
                                      · have har_c : (mw_c &&& 0xFF#32) = (mw &&& 0xFF#32) := by
                                          try simp only [hht_nat, hcur_eq] at hc
                                          rw [hmw_c_congr, hs_e1] at hc; exact hc
                                        clear hc; c0_hsteps_nogrp
                                        refine wp_loop_break_group (brkTs := [i32, i64])
                                          (lpTs := [i64])
                                          (fun (eq_b, _kb, ()) mb => mb = m1 ∧
                                            (eq_b ≠ 0#32 → ∀ j < ea.toNat,
                                              scr1[cur.toNat + 2 + j]? =
                                                scr1[ent.toNat + 2 + j]?))
                                          (fun rem (k, ()) mk => mk = m1 ∧ k.toNat ≤ ea.toNat ∧
                                            rem = ea.toNat - k.toNat ∧
                                            ∀ j < k.toNat,
                                              scr1[cur.toNat + 2 + j]? =
                                                scr1[ent.toNat + 2 + j]?)
                                          ?_ ?_ ?_
                                        · rintro _ ⟨eq_b, kb, ⟨⟩⟩ mb ⟨hmb, heq_ok⟩; subst mb
                                          c0_hsplit
                                          · have hcur_ne_ff' : cur ≠ 0xFFFFFFFF#32 := hcur_ne_ff
                                            c0_hsteps
                                            refine hQ cur scr1 s.scratch.res_sz m1 hscr1l
                                              (scr_state_core_pres hlen scr1 hscr1l _).1 rfl
                                              ⟨rfl, rfl⟩ (Or.inl rfl) (fun ho os hok => ?_)
                                              (Or.inr (Or.inr ⟨ht_off.toNat, ht_sz1.toNat,
                                                slot.toNat, mw, mw_c, hctrl1, hslot_lt, hcur_get,
                                                by omega, hmw_get, hmw_c_get, htag_c, har_c,
                                                by dsimp only [ea, earity] at hcur_fit
                                                   rw [bv64_zext32_toNat] at hcur_fit
                                                   exact hcur_fit,
                                                heq_ok hc⟩))
                                              hm1
                                            obtain ⟨rfl, rfl⟩ := m7CongHtCtrlOk_match_reads hco8
                                              hscrl hho_eq hsz_eq hok
                                            refine ⟨ht_sz1.toNat, hctrl1, hsz_cases, hsz1_max,
                                              fun _ hneed hlt hfit => (hgrow1 hneed hlt hfit).1,
                                              fun hnot => (hnogrow1 hnot).1, hpre1, hkeep1,
                                              ?_, fun hff => absurd hff hcur_ne_ff'⟩
                                            intro j hj
                                            rcases hslot1 j hj with hem |
                                                ⟨k0, hk0, raw, hg, hne, hor⟩
                                            · exact Or.inl hem
                                            · exact Or.inr (Or.inr ⟨k0, hk0, raw, hg, hne, hor⟩)
                                          · c0_hsteps; exact hJ3 m1 rfl
                                        · rintro Bk Lk rem ⟨k, ⟨⟩⟩ mk hBk hLk
                                            ⟨hmk, hk_le, rfl, hpre_k⟩
                                          subst mk
                                          c0_hsplit
                                          · have hk_lt : k.toNat < ea.toNat := by
                                              rw [hs_e1] at hc; dsimp only [ea, earity]
                                              rw [bv64_zext32_toNat]; exact hc
                                            have hc2k_n : (cur.setWidth 64 + 2#64 + k).toNat =
                                                cur.toNat + 2 + k.toNat := by
                                              have h12 := bv64_zext32_add_ofNat cur 2 (by decide)
                                              rw [bv64_add_toNat (by rw [h12]; omega), h12]
                                            have hc2k_arr :
                                                (cur.setWidth 64 + 2#64 + k).toNat <
                                                s1.scratch.scratch_buf.length := by
                                              rw [hc2k_n, hs1_scrl]; omega
                                            have he2k_n : (ent.setWidth 64 + 2#64 + k).toNat =
                                                ent.toNat + 2 + k.toNat := by
                                              have h12 := bv64_zext32_add_ofNat ent 2 (by decide)
                                              rw [bv64_add_toNat (by rw [h12]; omega), h12]
                                            have he2k_arr :
                                                (ent.setWidth 64 + 2#64 + k).toNat <
                                                s1.scratch.scratch_buf.length := by
                                              rw [he2k_n, hs1_scrl]; omega
                                            have hk1_n : (k + 1#64).toNat = k.toNat + 1 :=
                                              bv64_add1_lt hk_lt (by omega)
                                            clear hc; c0_hsplit
                                            · c0_hsteps; exact hBk (0#32, k, ()) m1
                                                ⟨rfl, fun h => absurd rfl h⟩
                                            · try simp only [hht_nat, hcur_eq] at hc
                                              have hc2k_mod :
                                                  (cur.toNat + BitVec.toNat (2 : BitVec 64) +
                                                  k.toNat) % 2 ^ 64 =
                                                  (cur.setWidth 64 + 2#64 + k).toNat := by
                                                rw [hc2k_n]
                                                have h2n : BitVec.toNat (2 : BitVec 64) = 2 := rfl
                                                rw [h2n, Nat.mod_eq_of_lt (by omega)]
                                              have he2k_mod :
                                                  (ent.toNat + BitVec.toNat (2 : BitVec 64) +
                                                  k.toNat) % 2 ^ 64 =
                                                  (ent.setWidth 64 + 2#64 + k).toNat := by
                                                rw [he2k_n]
                                                have h2n : BitVec.toNat (2 : BitVec 64) = 2 := rfl
                                                rw [h2n, Nat.mod_eq_of_lt (by omega)]
                                              have he2k_mod_arr :
                                                  (ent.toNat + BitVec.toNat (2 : BitVec 64) +
                                                  k.toNat) % 2 ^ 64 <
                                                  s1.scratch.scratch_buf.length := by
                                                rw [he2k_mod]; exact he2k_arr
                                              have hsame : scr1[(cur.setWidth 64 + 2#64 +
                                                  k).toNat]'hc2k_arr =
                                                  scr1[(ent.setWidth 64 + 2#64 +
                                                  k).toNat]'he2k_arr :=
                                                (list_getElem_congr hc2k_mod.symm hc2k_arr
                                                  (by rw [hc2k_mod]; exact hc2k_arr)).trans
                                                  (hc.trans (list_getElem_congr he2k_mod
                                                    he2k_mod_arr he2k_arr))
                                              c0_hsteps
                                              refine hLk (ea.toNat - (k + 1#64).toNat)
                                                (k + 1#64, ()) m1 (by omega)
                                                ⟨rfl, by omega, rfl, fun j hj => ?_⟩
                                              rw [hk1_n] at hj
                                              by_cases hjk : j = k.toNat
                                              · subst hjk
                                                rw [List.getElem?_eq_getElem
                                                    (by rw [hscr1l]; omega),
                                                  List.getElem?_eq_getElem (by rw [hscr1l]; omega)]
                                                congr 1
                                                exact (list_getElem_congr hc2k_n hc2k_arr
                                                  (by rw [hscr1l]; omega)).symm.trans
                                                  (hsame.trans (list_getElem_congr he2k_n he2k_arr
                                                    (by rw [hscr1l]; omega)))
                                              · exact hpre_k j (by omega)
                                          · have hk_eq : k.toNat = ea.toNat := by
                                              rw [hs_e1] at hc; dsimp only [ea, earity] at hk_le ⊢
                                              rw [bv64_zext32_toNat] at hk_le ⊢
                                              change ¬ k.toNat < (mw &&& 0xFF#32).toNat at hc
                                              omega
                                            rw [hk_eq] at hpre_k
                                            c0_hsteps
                                            exact hBk (1#32, k, ()) m1 ⟨rfl, fun _ => hpre_k⟩
                                        · intro _ Lk _ hLk; c0_hsteps
                                          exact hLk ea.toNat (0#64, ()) m1
                                            ⟨rfl, Nat.zero_le _, rfl, fun _ h => by simp at h⟩
                                      · c0_hsteps; exact hJ3 m1 rfl
                                    · c0_hsteps; exact hJ3 m1 rfl
                                  · c0_hsteps; exact hJ2 m1 rfl
                            · have hp_eq : p.toNat = ht_sz1.toNat := by omega
                              have hfull : ∀ j < ht_sz1.toNat,
                                  scr1[ht_off.toNat + j]? ≠ some 0xFFFFFFFF#32 := fun j hj => by
                                obtain ⟨q, hq, hmod⟩ := probe_visit_idx (hv := hv.toNat) hj
                                rw [← hmod]; exact hnoem q (by omega)
                              c0_hsteps
                              refine hQ 0xFFFFFFFF#32 scr1 s.scratch.res_sz m1 hscr1l
                                (scr_state_core_pres hlen scr1 hscr1l _).1 rfl ⟨rfl, rfl⟩
                                (Or.inl rfl) (fun ho os hok => ?_) (Or.inl rfl) hm1
                              obtain ⟨rfl, rfl⟩ :=
                                m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                              refine ⟨ht_sz1.toNat, hctrl1, hsz_cases, hsz1_max,
                                fun _ hneed hlt hfit => (hgrow1 hneed hlt hfit).1,
                                fun hnot => (hnogrow1 hnot).1, hpre1, hkeep1, ?_,
                                fun _ _ _ _ _ => ⟨hfull, fun _ => ?_, fun ⟨hneed, hlt, hfit⟩ => ?_⟩⟩
                              · intro j hj
                                rcases hslot1 j hj with hem | ⟨k0, hk0, raw, hg, hne, hor⟩
                                · exact Or.inl hem
                                · exact Or.inr (Or.inr ⟨k0, hk0, raw, hg, hne, hor⟩)
                              · by_cases hngf :
                                    (old_sz.toNat ≤ s.scratch.res_sz.toNat ∨
                                      3 * old_sz.toNat ≤ 4 * s.scratch.res_sz.toNat) ∧
                                    old_sz.toNat < m7CongHashMaxSz ∧
                                    ht_off.toNat + 2 * old_sz.toNat ≤ c.scratch_cap
                                · obtain ⟨_, j, hj, hj_e⟩ := hgrow1 hngf.1 hngf.2.1 hngf.2.2
                                  exact False.elim (hfull j hj hj_e)
                                · exact (hnogrow1 hngf).2
                              · obtain ⟨_, j, hj, hj_e⟩ := hgrow1 hneed hlt hfit
                                exact hfull j hj hj_e
                          · intro Js hJs; c0_hsplit
                            · clear hc; c0_hsteps_nogrp
                              refine wp_join_group (ts := []) (fun () mg => mg = m0 ∧
                                (old_sz.toNat ≤ s.scratch.res_sz.toNat ∨
                                  3 * old_sz.toNat ≤ 4 * s.scratch.res_sz.toNat)) ?_ ?_
                              · rintro _ ⟨⟩ mg ⟨hmg, hneed_sz⟩; subst mg
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
                                    obtain ⟨hn, hok', _, _, _, _⟩ := hg2 h1' h2'
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
                                have hgrow_g : (old_sz.toNat ≤ s.scratch.res_sz.toNat ∨
                                      3 * old_sz.toNat ≤ 4 * s.scratch.res_sz.toNat) →
                                    old_sz.toNat < m7CongHashMaxSz →
                                    ht_off.toNat + 2 * old_sz.toNat ≤ c.scratch_cap →
                                    grown.toNat = 2 * old_sz.toNat ∧
                                      ∃ j < grown.toNat, scr_g[ht_off.toNat + j]? =
                                        some 0xFFFFFFFF#32 := by
                                  intro _ h1' h2'
                                  obtain ⟨hn, _, _, ⟨j, hj, hj_e⟩, _, _⟩ := hg2 h1' h2'
                                  exact ⟨hn, j, by omega, hj_e⟩
                                have hnogrow_g : ¬ ((old_sz.toNat ≤ s.scratch.res_sz.toNat ∨
                                      3 * old_sz.toNat ≤ 4 * s.scratch.res_sz.toNat) ∧
                                      old_sz.toNat < m7CongHashMaxSz ∧
                                      ht_off.toNat + 2 * old_sz.toNat ≤ c.scratch_cap) →
                                    grown.toNat = old_sz.toNat ∧
                                      scr_g = s.scratch.scratch_buf := by
                                  intro hnot
                                  have hcap : m7CongHashMaxSz ≤ old_sz.toNat ∨
                                      c.scratch_cap < ht_off.toNat + 2 * old_sz.toNat := by
                                    by_cases hc' : m7CongHashMaxSz ≤ old_sz.toNat ∨
                                        c.scratch_cap < ht_off.toNat + 2 * old_sz.toNat
                                    · exact hc'
                                    · exact False.elim (hnot ⟨hneed_sz, by omega, by omega⟩)
                                  exact hg1 hcap
                                have hpre_g : ∀ idx < ht_off.toNat, idx ≠ ctrl_off.toNat + 7 →
                                    scr_g[idx]? = s.scratch.scratch_buf[idx]? := by
                                  by_cases hcap : m7CongHashMaxSz ≤ old_sz.toNat ∨
                                      c.scratch_cap < ht_off.toNat + 2 * old_sz.toNat
                                  · rw [(hg1 hcap).2]; exact fun _ _ _ => rfl
                                  · exact (hg2 (by omega) (by omega)).2.2.1
                                have hkeep_g : ∀ v : BitVec 32, v.toNat < ht_off.toNat →
                                    (∃ k0 < old_sz.toNat,
                                      s.scratch.scratch_buf[ht_off.toNat + k0]? = some v) →
                                    ∃ j < grown.toNat, scr_g[ht_off.toNat + j]? = some v := by
                                  intro v hv_lt ⟨k0, hk0, hget0⟩
                                  by_cases hcap : m7CongHashMaxSz ≤ old_sz.toNat ∨
                                      c.scratch_cap < ht_off.toNat + 2 * old_sz.toNat
                                  · rw [(hg1 hcap).1, (hg1 hcap).2]
                                    exact ⟨k0, hk0, hget0⟩
                                  · obtain ⟨hn, _, _, _, hkp, _⟩ := hg2 (by omega) (by omega)
                                    obtain ⟨j, hj, hj_e⟩ := hkp v hv_lt ⟨k0, hk0, hget0⟩
                                    exact ⟨j, by omega, hj_e⟩
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
                                    obtain ⟨hn, _, _, _, _, hres⟩ := hg2 h1' h2'
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
                                      hgrow_g, hnogrow_g, hpre_g, hkeep_g, hslot_g, hmg'⟩)
                                  (fun J2 hJ2 => ?_)
                                obtain ⟨kg, hkg, hpowg⟩ := hc_g.2.2.2.2.1
                                have hpow2_pos : 16 ≤ grown.toNat := by
                                  rw [hpowg]; have := Nat.two_pow_pos kg; omega
                                have hcap_g : grown.toNat ≤ c.scratch_cap - ht_off.toNat :=
                                  Nat.le_sub_of_add_le' hc_g.2.2.1
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
                                · c0_hsteps
                                  have hge : old_sz.toNat ≤ s.scratch.res_sz.toNat := by
                                    rw [hs7a, hos_nat] at hc; exact hc
                                  exact hJ1 () m0 ⟨rfl, Or.inl hge⟩
                                · have hrs_lt : s.scratch.res_sz.toNat < old_sz.toNat := by
                                    rw [hs7a, hos_nat] at hc; exact Nat.not_le.mp hc
                                  clear hc; c0_hsplit
                                  · c0_hsteps
                                    have h34 : 3 * old_sz.toNat ≤ 4 * s.scratch.res_sz.toNat := by
                                      rw [hs7a, hos_nat] at hc
                                      have h4n : BitVec.toNat (4 : BitVec 64) = 4 := rfl
                                      have h3n : BitVec.toNat (3 : BitVec 64) = 3 := rfl
                                      rw [h4n, h3n, Nat.mod_eq_of_lt (by omega),
                                        Nat.mod_eq_of_lt (by omega)] at hc
                                      omega
                                    exact hJ1 () m0 ⟨rfl, Or.inr h34⟩
                                  · have h34_lt :
                                        4 * s.scratch.res_sz.toNat < 3 * old_sz.toNat := by
                                      rw [hs7a, hos_nat] at hc
                                      have h4n : BitVec.toNat (4 : BitVec 64) = 4 := rfl
                                      have h3n : BitVec.toNat (3 : BitVec 64) = 3 := rfl
                                      rw [h4n, h3n, Nat.mod_eq_of_lt (by omega),
                                        Nat.mod_eq_of_lt (by omega)] at hc
                                      omega
                                    c0_hsteps; try simp only [hs7b]
                                    refine hJs (old_sz, ()) m0
                                      ⟨s.scratch.scratch_buf, hscrl, hok_read, Or.inl rfl, hmax,
                                        fun hneed _ _ => False.elim (by rcases hneed with h | h <;>
                                          omega),
                                        fun _ => ⟨rfl, rfl⟩,
                                        fun _ _ _ => rfl, hkeep_id, fun j hj => ?_, hm0⟩
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
      , "full_cong_ht_grow_clear_m7", "full_cong_ht_lookup_m7"
      , "full_cong_ht_insert_m7" ] : List String).Nodup
  decide

private theorem m7CongHashEnv_row_at (i : Nat) (e : SpecEntry)
    (hi : m7CongHashSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → m7CongHashEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) m7CongHashSpecTable_nodup (hno xs m Q X h)

/-- Row-by-row `TableImpl` for `m7CongHashFns` (`6` functions) against `m7CongHashSpecTable`. -/
theorem m7CongHash_tableImpl :
    TableImpl m7CongHashEnv m7CongHashFns m7CongHashSpecTable := by
  let h0 := m7CongHashEnv_row_at 0 ⟨"full_cong_ht_hash_ent_m7", [i64, i32, i64], [i64],
    m7CongHtHashEntSpec, true⟩
  let h2 := m7CongHashEnv_row_at 2 ⟨"full_cong_ht_grow_m7", [i64, i64], [i64],
    m7CongHtGrowSpec, true⟩
  exact ⟨.of (full_cong_ht_hash_ent_m7_wp m7CongHashEnv),
    ⟨.of (full_cong_ht_init_m7_wp m7CongHashEnv),
    ⟨.of (full_cong_ht_grow_m7_wp m7CongHashEnv h0),
    ⟨.of (full_cong_ht_grow_clear_m7_wp m7CongHashEnv),
    ⟨.of (full_cong_ht_lookup_m7_wp m7CongHashEnv),
    ⟨.of (full_cong_ht_insert_m7_wp m7CongHashEnv h2 h0), trivial⟩⟩⟩⟩⟩⟩

/-- Closed `ModuleOk` for standalone `m7CongHashModule` under canonical `m7CongHashEnv`. -/
theorem m7CongHash_moduleOk : ModuleOk m7CongHashEnv m7CongHashModule :=
  Env.ofTable_moduleOk m7CongHash_acyclic
    ⟨full_cong_ht_hash_ent_m7_wf, full_cong_ht_init_m7_wf, full_cong_ht_grow_m7_wf,
      full_cong_ht_grow_clear_m7_wf, full_cong_ht_lookup_m7_wf, full_cong_ht_insert_m7_wf,
      trivial⟩
    m7CongHash_tableImpl

end ModuleVerification

/-! ## 6. Concrete `Mem 64` Non-Vacuity (`16,448`-Word Buffer, Colliding Gates, `XPost := False`) -/

section NonVacuity

private def nvM7CongScrHead : List (BitVec 32) :=
  [ 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 64#32, 8192#32
  , 0#32, 0x10000001#32, 14915#32, 0#32, 0#32, 0#32, 0#32, 0#32
  , 0#32, 0x10000001#32, 31299#32, 0#32, 0#32, 0#32, 0#32, 0#32
  , 0#32, 0x10000001#32, 14916#32 ] ++ List.replicate 37 0#32

private theorem nvM7CongScrHead_len : nvM7CongScrHead.length = 64 := by decide

/-- `16,448`-word concrete `scratch_buf`: `ctrl[6]=64`, `ctrl[7]=8192`, colliding gates
`gA@8 (lit0=14915)`, `gB@16 (lit0=31299)`, `gC@24 (lit0=14916)`, live table `ht[2]=24`,
`ht[3]=8` (colliding at slot `2 = hv % 8192`), and `16,380` trailing `0xFFFFFFFF#32` slots. -/
def nvM7CongScrBuf : List (BitVec 32) :=
  nvM7CongScrHead ++ [0xFFFFFFFF#32, 0xFFFFFFFF#32, 24#32, 8#32] ++
    List.replicate 16380 0xFFFFFFFF#32

theorem nvM7CongScrBuf_len : nvM7CongScrBuf.length = 16448 := by
  unfold nvM7CongScrBuf
  rw [List.length_append, List.length_append, List.length_replicate, nvM7CongScrHead_len]
  rfl

private theorem nvM7CongScrBuf_head {idx : Nat} (hidx : idx < 64) :
    nvM7CongScrBuf[idx]? = nvM7CongScrHead[idx]? := by
  unfold nvM7CongScrBuf
  rw [List.append_assoc]
  exact List.getElem?_append_left (by rw [nvM7CongScrHead_len]; exact hidx)

private theorem nvM7CongScrBuf_slot {k : Nat} (hk : k < 8192) :
    nvM7CongScrBuf[64 + k]? =
      if k < 4 then ([0xFFFFFFFF#32, 0xFFFFFFFF#32, 24#32, 8#32] : List (BitVec 32))[k]?
      else some 0xFFFFFFFF#32 := by
  unfold nvM7CongScrBuf
  rw [List.append_assoc,
    List.getElem?_append_right (by rw [nvM7CongScrHead_len]; omega), nvM7CongScrHead_len,
    show 64 + k - 64 = k from by omega]
  by_cases hk4 : k < 4
  · simp only [hk4, ↓reduceIte]
    exact List.getElem?_append_left hk4
  · simp only [hk4, ↓reduceIte]
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_cons, List.length_nil, Nat.zero_add, List.getElem?_replicate]
    split; rfl; omega

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
  walk_cnt_stat := 0#64; fwd_sub_cnt := 0#64; fwd_str_cnt := 0#64; ant_sz := 0#64; res_sz := 2#64
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
      rsns := [0xFFFFFFFF#32], trl := [0#32], trail_pos := [0#32], tmp := [14915#32]
      min_clr := [0#32], frame_trail := [0#32, 0#32], frame_dec := [0#32, 0#32]
      wvec := List.replicate 4 0#32, repr := [0#32, 0#32], min_stk := List.replicate 4 0#32
      arena := [], wstk := [0#32] }
  scratch := nvM7CongScratch

def nvM7CongStateGrow : FullState :=
  { nvM7CongState with scratch := { nvM7CongScratch with res_sz := 6144#64 } }

theorem nvM7Cong_lengths : nvM7CongState.LengthsOk nvM7CongCfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, nvM7CongScrBuf_len⟩⟩

theorem nvM7CongGrow_lengths : nvM7CongStateGrow.LengthsOk nvM7CongCfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, nvM7CongScrBuf_len⟩⟩

private def nvM7BlockHdr : List UInt8 :=
  bytes64 [1#64, 0#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords nvM7CongCfg nvM7CongState)

private def nvM7BlockHdrGrow : List UInt8 :=
  bytes64 [1#64, 0#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords nvM7CongCfg nvM7CongStateGrow)

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

private def nvM7BlockBody : List UInt8 :=
  nvM7BlockBytes ++ nvM7BlockU32A ++ nvM7BlockU32B ++ nvM7BlockU32C ++
  nvM7BlockWvec ++ nvM7BlockTail

/-- Concrete `67,548`-byte `Mem 64` image for `nvM7CongCfg` at `0x1000`. -/
def nvM7CongMem : Mem 64 :=
  (nvM7BlockHdr ++ nvM7BlockBody).At nvM7CongCfg.hdr

/-- Concrete `67,548`-byte `Mem 64` image for `nvM7CongStateGrow` (`res_sz = 6144`) at `0x1000`. -/
def nvM7CongMemGrow : Mem 64 :=
  (nvM7BlockHdrGrow ++ nvM7BlockBody).At nvM7CongCfg.hdr

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

private theorem nvM7CongBody_ok :
    let c := nvM7CongCfg; let s := nvM7CongState
    nvM7BlockBody.length = 66396 ∧
      ((FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ c.padBytes) ⋆
        ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
          array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
          array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A) ⋆
        ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
          (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
           array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B) ⋆
        ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆
          array (t := i32) c.pQNext s.scratch.q_next ⋆
          array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
          (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
           array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C) ⋆
        ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
          FullScrWksArrs c s.scratch ⋆
          (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig)) ⋆
        (array (t := i32) c.pMinStk s.core.min_stk ⋆
          (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
           array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
          FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack))
        (nvM7BlockBody.At c.pVals) := by
  let c := nvM7CongCfg; let s := nvM7CongState
  have hvb : valsBytes c.max_vars - 2 * c.max_vars = 6 := by decide
  have hmb : markBytes c.max_vars - c.max_vars = 7 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 0 := by decide
  have hmv1 : BitVec.ofNat 64 c.max_vars = 1#64 := rfl
  have hmv2 : BitVec.ofNat 64 (2 * c.max_vars) = 2#64 := rfl
  have hmv4 : BitVec.ofNat 64 (4 * c.max_vars) = 4#64 := rfl
  have hmv8 : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 8#64 := rfl
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
  have h1 := m7_nv_join hBytes hU32A (by decide) (by decide)
  have h2 := m7_nv_join h1 hU32B (by decide) (by decide)
  have h3 := m7_nv_join h2 hU32C (by decide) (by decide)
  have h4 := m7_nv_join h3 hWvec (by decide) (by decide)
  exact m7_nv_reorg (m7_nv_join h4 hTail (by decide) (by decide)) fun _ hm => sep_ac hm

theorem nvM7CongMem_ok : FullMem nvM7CongCfg nvM7CongState nvM7CongMem := by
  let c := nvM7CongCfg; let s := nvM7CongState
  have hHdr : nvM7BlockHdr.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s))
        (nvM7BlockHdr.At c.hdr) :=
    m7_nv_join (m7_nv_arr64_p (a := c.hdr) (xs := [1#64, 0#64, 0#64, 0#64]) 32 rfl (by decide))
      (m7_nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide)) (by decide) (by decide)
  exact (m7_nv_reorg (Q := FullMem c s)
    (m7_nv_join hHdr nvM7CongBody_ok (by decide) (by decide)) fun _ hm => by
      unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
        FullScrMetaArrs FullCfg.pad; exact sep_ac hm).2

theorem nvM7CongMemGrow_ok : FullMem nvM7CongCfg nvM7CongStateGrow nvM7CongMemGrow := by
  let c := nvM7CongCfg; let s := nvM7CongStateGrow
  have hHdr : nvM7BlockHdrGrow.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s))
        (nvM7BlockHdrGrow.At c.hdr) :=
    m7_nv_join (m7_nv_arr64_p (a := c.hdr) (xs := [1#64, 0#64, 0#64, 0#64]) 32 rfl (by decide))
      (m7_nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide)) (by decide) (by decide)
  exact (m7_nv_reorg (Q := FullMem c s)
    (m7_nv_join hHdr nvM7CongBody_ok (by decide) (by decide)) fun _ hm => by
      unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
        FullScrMetaArrs FullCfg.pad; exact sep_ac hm).2

private theorem nvM7CongMem_sep : (FullMem nvM7CongCfg nvM7CongState ⋆ emp) nvM7CongMem := by
  rw [sep_emp]; exact nvM7CongMem_ok

private theorem nvM7CongMemGrow_sep :
    (FullMem nvM7CongCfg nvM7CongStateGrow ⋆ emp) nvM7CongMemGrow := by
  rw [sep_emp]; exact nvM7CongMemGrow_ok

theorem nvM7Cong_ctrl_ok : M7CongHtCtrlOk nvM7CongCfg nvM7CongScrBuf 0 64 8192 :=
  ⟨nvM7CongScrBuf_len, by decide, by decide, by decide, ⟨9, by decide, by decide⟩,
   by rw [nvM7CongScrBuf_head (by decide)]; decide,
   by rw [nvM7CongScrBuf_head (by decide)]; decide⟩

private theorem nvM7Cong_no_equiv_16 {scr' : List (BitVec 32)} {ret mw_e mw_c : BitVec 32}
    {ho nsz nsz' k : Nat} (hctrl' : M7CongHtCtrlOk nvM7CongCfg scr' 0 64 nsz)
    (hpre : ∀ idx < 64, idx ≠ 7 → scr'[idx]? = nvM7CongScrBuf[idx]?)
    (hslot : ∀ j < nsz,
      scr'[64 + j]? = some 0xFFFFFFFF#32 ∨ scr'[64 + j]? = some 16#32 ∨
      ∃ k0 < 8192, ∃ raw : BitVec 32,
        nvM7CongScrBuf[64 + k0]? = some raw ∧ raw ≠ 0xFFFFFFFF#32 ∧
        (scr'[64 + j]? = some raw ∨ scr'[64 + j]? = some (raw &&& 0x7FFFFFFF#32)))
    (hok : M7CongHtCtrlOk nvM7CongCfg scr' 0 ho nsz') (hk : k < nsz')
    (hget : scr'[ho + k]? = some ret) (hlt : ret.toNat < ho)
    (hmw_e : nvM7CongScrBuf[17]? = some mw_e)
    (hmw_c : scr'[ret.toNat + 1]? = some mw_c)
    (hlits : ∀ j < (mw_e &&& 0xFF#32).toNat, scr'[ret.toNat + 2 + j]? = scr'[18 + j]?) :
    ret = 16#32 := by
  have hm6 := hok.2.2.2.2.2.1; have hc6 := hctrl'.2.2.2.2.2.1
  rw [hm6, Option.some.injEq] at hc6
  have h64 : ho = 64 := by
    have htn := congrArg BitVec.toNat hc6
    rwa [bv32_ofNat_toNat_lt (by have := hok.2.2.2.1; omega),
      bv32_ofNat_toNat_lt (by have := hctrl'.2.2.2.1; omega)] at htn
  have hm7 := hok.2.2.2.2.2.2; have hc7 := hctrl'.2.2.2.2.2.2
  rw [hm7, Option.some.injEq] at hc7
  have hnsz : nsz' = nsz := by
    have htn := congrArg BitVec.toNat hc7
    have h1 := hok.2.2.2.2.1; obtain ⟨k1, hk1, hk1e⟩ := h1
    have h2 := hctrl'.2.2.2.2.1; obtain ⟨k2, hk2, hk2e⟩ := h2
    have hm1 := pow2_16_mul_le k1 hk1
    have hm2 := pow2_16_mul_le k2 hk2
    rwa [bv32_ofNat_toNat_lt (by omega), bv32_ofNat_toNat_lt (by omega)] at htn
  subst h64; subst hnsz
  have hme_val : mw_e = 0x10000001#32 := by
    rw [nvM7CongScrBuf_head (by decide)] at hmw_e
    have h17 : nvM7CongScrHead[17]? = some 0x10000001#32 := by decide
    rw [h17, Option.some.injEq] at hmw_e
    exact hmw_e.symm
  have hlit0 : scr'[ret.toNat + 2]? = scr'[18]? := by
    have h0 := hlits 0 (by rw [hme_val]; decide); simpa using h0
  rcases hslot k hk with hem | h16 | ⟨k0, hk0, raw, hget0, hne0, hor⟩
  · rw [hget, Option.some.injEq] at hem; subst hem
    have : (0xFFFFFFFF#32 : BitVec 32).toNat < 64 := hlt; contradiction
  · rw [hget, Option.some.injEq] at h16; exact h16
  · rw [nvM7CongScrBuf_slot hk0] at hget0
    by_cases hk4 : k0 < 4
    · simp only [hk4, ↓reduceIte] at hget0
      have hk0_cases : k0 = 0 ∨ k0 = 1 ∨ k0 = 2 ∨ k0 = 3 := by omega
      rcases hk0_cases with rfl | rfl | rfl | rfl
      · exact False.elim (hne0 (Option.some.inj hget0).symm)
      · exact False.elim (hne0 (Option.some.inj hget0).symm)
      · have hraw : raw = 24#32 := (Option.some.inj hget0).symm
        subst hraw
        have hret24 : ret = 24#32 := by
          rw [hget] at hor
          rcases hor with h | h <;> rw [Option.some.injEq] at h
          · exact h
          · exact h.trans (by decide)
        subst hret24
        rw [show (24#32 : BitVec 32).toNat + 2 = 26 from by decide,
          hpre 26 (by decide) (by decide), hpre 18 (by decide) (by decide),
          nvM7CongScrBuf_head (by decide), nvM7CongScrBuf_head (by decide)] at hlit0
        contradiction
      · have hraw : raw = 8#32 := (Option.some.inj hget0).symm
        subst hraw
        have hret8 : ret = 8#32 := by
          rw [hget] at hor
          rcases hor with h | h <;> rw [Option.some.injEq] at h
          · exact h
          · exact h.trans (by decide)
        subst hret8
        rw [show (8#32 : BitVec 32).toNat + 2 = 10 from by decide,
          hpre 10 (by decide) (by decide), hpre 18 (by decide) (by decide),
          nvM7CongScrBuf_head (by decide), nvM7CongScrBuf_head (by decide)] at hlit0
        contradiction
    · simp only [hk4, ↓reduceIte] at hget0
      exact False.elim (hne0 (Option.some.inj hget0).symm)

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
table with live colliding entries (`ht[2]=24`, `ht[3]=8`) to `16,384` buckets (`4x` past legacy
`4096`) on `nvM7CongMem` while migrating and preserving both colliding gates. -/
theorem nv_m7_cong_ht_grow :
    Func.wp m7CongHashEnv full_cong_ht_grow_m7_body
      (nvM7CongCfg.hdr, 0#64, ()) nvM7CongMem
      (fun (ret, ()) m' => ∃ s',
        ret = 16384#64 ∧ PreservesCoreSlice FullState.core nvM7CongState s' ∧
        s'.LengthsOk nvM7CongCfg ∧ FullExtScratchPres nvM7CongState s' ∧
        M7CongHtCtrlOk nvM7CongCfg s'.scratch.scratch_buf 0 64 16384 ∧
        (∃ jC < 16384, s'.scratch.scratch_buf[64 + jC]? = some 24#32) ∧
        (∃ jA < 16384, s'.scratch.scratch_buf[64 + jA]? = some 8#32) ∧
        FullMem nvM7CongCfg s' m')
      (fun _ _ _ _ => False) :=
  m7CongHash_tableImpl.2.2.1.2 _ _ _ _
    ⟨nvM7CongCfg, nvM7CongState, emp, rfl, nvM7Cong_lengths, nvM7CongMem_sep,
     fun ret scr' m' _ hlen hcore hpres hres _ hm' => by
       obtain ⟨hret_n, hctrl, _, _, hkeep, _⟩ :=
         (hres 64 8192 nvM7Cong_ctrl_ok).2 (by decide) (by decide)
       have hret : ret = 16384#64 := BitVec.eq_of_toNat_eq (hret_n.trans (by decide))
       have hctrl' : M7CongHtCtrlOk nvM7CongCfg scr' 0 64 16384 := by simpa using hctrl
       have hkC : ∃ jC < 16384, scr'[64 + jC]? = some 24#32 :=
         hkeep 24#32 (by decide) ⟨2, by decide, by
           dsimp only [nvM7CongState, nvM7CongScratch]
           rw [nvM7CongScrBuf_slot (by decide)]; decide⟩
       have hkA : ∃ jA < 16384, scr'[64 + jA]? = some 8#32 :=
         hkeep 8#32 (by decide) ⟨3, by decide, by
           dsimp only [nvM7CongState, nvM7CongScratch]
           rw [nvM7CongScrBuf_slot (by decide)]; decide⟩
       rw [sep_emp] at hm'
       exact ⟨_, hret, hcore, hlen, hpres, hctrl', hkC, hkA, hm'⟩⟩

/-- Concrete `Mem 64` NV (`XPost := False`): `full_cong_ht_grow_clear_m7` grows an `8,192`-bucket
table to `16,384` buckets, clears all `16,384` slots to `0xFFFFFFFF#32`, and resets `res_sz = 0`. -/
theorem nv_m7_cong_ht_grow_clear :
    Func.wp m7CongHashEnv full_cong_ht_grow_clear_m7_body
      (nvM7CongCfg.hdr, 0#64, ()) nvM7CongMem
      (fun (ret, ()) m' => ∃ s',
        ret = 16384#64 ∧ s'.scratch.res_sz = 0#64 ∧
        PreservesCoreSlice FullState.core nvM7CongState s' ∧
        s'.LengthsOk nvM7CongCfg ∧ FullExtScratchPres nvM7CongState s' ∧
        M7CongHtCtrlOk nvM7CongCfg s'.scratch.scratch_buf 0 64 16384 ∧
        (∀ j < 16384, s'.scratch.scratch_buf[64 + j]? = some 0xFFFFFFFF#32) ∧
        FullMem nvM7CongCfg s' m')
      (fun _ _ _ _ => False) :=
  m7CongHash_tableImpl.2.2.2.1.2 _ _ _ _
    ⟨nvM7CongCfg, nvM7CongState, emp, rfl, nvM7Cong_lengths, nvM7CongMem_sep,
     fun ret scr' _ m' _ hlen hcore hpres hres _ hm' => by
       obtain ⟨hret_n, hctrl, hrsz, _, hclr⟩ :=
         (hres 64 8192 nvM7Cong_ctrl_ok).2 (by decide) (by decide)
       have hret : ret = 16384#64 := BitVec.eq_of_toNat_eq (hret_n.trans (by decide))
       have hctrl' : M7CongHtCtrlOk nvM7CongCfg scr' 0 64 16384 := by simpa using hctrl
       rw [sep_emp] at hm'
       exact ⟨_, hret, hrsz, hcore, hlen, hpres, hctrl', hclr, hm'⟩⟩

/-- Concrete `Mem 64` NV (`XPost := False`): `full_cong_ht_lookup_m7` probes past colliding
entry `ht[2]=24` (`lit0=14916`) on `(tag=1, arity=1, tmp=[14915])` and returns exact `8#32`. -/
theorem nv_m7_cong_ht_lookup :
    Func.wp m7CongHashEnv full_cong_ht_lookup_m7_body
      (nvM7CongCfg.hdr, 0#64, 1#32, 1#32, ()) nvM7CongMem
      (fun (ret, ()) m' => ret = 8#32 ∧ m' = nvM7CongMem)
      (fun _ _ _ _ => False) :=
  m7CongHash_tableImpl.2.2.2.2.1.2 _ _ _ _
    ⟨nvM7CongCfg, nvM7CongState, emp, rfl, nvM7Cong_lengths, nvM7CongMem_sep,
     fun ret hret => by
       rcases hret with ⟨rfl, hmiss⟩ | ⟨ho, hsz, k, _, hctrl, _, _, hk, hget, hfit, _, _, _, htmp⟩
       · exfalso
         have hnm := hmiss 64 8192 nvM7Cong_ctrl_ok (by decide) (by decide)
         have hslot2 : (m7CongHashTmp 1#32 1#32 nvM7CongState.core.tmp).toNat % 8192 = 2 := by
           decide
         have hne_chain : ∀ m0 ≤ 1,
             nvM7CongScrBuf[64 + (2 + m0) % 8192]? ≠ some 0xFFFFFFFF#32 := by
           intro m0 hm0
           rcases (by omega : m0 = 0 ∨ m0 = 1) with rfl | rfl
           · rw [show (2 + 0) % 8192 = 2 from rfl, nvM7CongScrBuf_slot (by decide)]; decide
           · rw [show (2 + 1) % 8192 = 3 from rfl, nvM7CongScrBuf_slot (by decide)]; decide
         have hget8 : nvM7CongScrBuf[64 + (2 + 1) % 8192]? = some 8#32 := by
           rw [show (2 + 1) % 8192 = 3 from rfl, nvM7CongScrBuf_slot (by decide)]
           decide
         have hmatch8 : m7CongSlotMatch nvM7CongScrBuf 64 1#32 1#32 nvM7CongState.core.tmp 8#32 :=
           ⟨by decide, by decide, 0x10000001#32,
            by rw [nvM7CongScrBuf_head (by decide)]; decide, by decide, by decide,
            fun j hj => by
              rw [show (1#32 : BitVec 32).toNat = 1 from rfl] at hj
              obtain rfl : j = 0 := by omega
              rw [nvM7CongScrBuf_head (by decide)]; decide⟩
         rw [hslot2] at hnm
         exact hnm 1 (by decide) hne_chain 8#32 hget8 hmatch8
       · have hm6 := hctrl.2.2.2.2.2.1; have hc6 := nvM7Cong_ctrl_ok.2.2.2.2.2.1
         dsimp only [nvM7CongState, nvM7CongScratch] at hm6
         rw [show (0#64 : BitVec 64).toNat = 0 from rfl] at hm6
         rw [hm6, Option.some.injEq] at hc6
         have h64 : ho = 64 := by
           have htn := congrArg BitVec.toNat hc6
           rwa [bv32_ofNat_toNat_lt (by have := hctrl.2.2.2.1; omega),
             bv32_ofNat_toNat_lt (by decide)] at htn
         have hm7 := hctrl.2.2.2.2.2.2; have hc7 := nvM7Cong_ctrl_ok.2.2.2.2.2.2
         dsimp only [nvM7CongState, nvM7CongScratch] at hm7
         rw [show (0#64 : BitVec 64).toNat = 0 from rfl] at hm7
         rw [hm7, Option.some.injEq] at hc7
         have h8192 : hsz = 8192 := by
           have htn := congrArg BitVec.toNat hc7
           obtain ⟨k1, hk1, hk1e⟩ := hctrl.2.2.2.2.1
           have hm1 := pow2_16_mul_le k1 hk1
           rwa [bv32_ofNat_toNat_lt (by omega), bv32_ofNat_toNat_lt (by decide)] at htn
         subst h64; subst h8192
         dsimp only [nvM7CongState, nvM7CongScratch] at hget
         rw [nvM7CongScrBuf_slot hk] at hget
         by_cases hk4 : k < 4
         · simp only [hk4, ↓reduceIte] at hget
           rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
           · have hret : ret = 0xFFFFFFFF#32 := (Option.some.inj hget).symm
             subst hret; revert hfit; decide
           · have hret : ret = 0xFFFFFFFF#32 := (Option.some.inj hget).symm
             subst hret; revert hfit; decide
           · have hret : ret = 24#32 := (Option.some.inj hget).symm
             subst hret
             have h0 := htmp 0 (by decide)
             dsimp only [nvM7CongState, nvM7CongScratch] at h0
             rw [nvM7CongScrBuf_head (by decide)] at h0
             revert h0; decide
           · have hret : ret = 8#32 := (Option.some.inj hget).symm
             exact ⟨hret, rfl⟩
         · simp only [hk4, ↓reduceIte] at hget
           have hret : ret = 0xFFFFFFFF#32 := (Option.some.inj hget).symm
           subst hret; revert hfit; decide⟩

/-- Concrete `Mem 64` NV (`XPost := False`): `full_cong_ht_insert_m7` inserts colliding gate
`ent = 16#32` (`lit0=31299`) into `nvM7CongMem` (`res_sz=2`, `old_sz=8192`) without spurious match
or resize (`ret = 16#32`, `new_sz = 8192`). -/
theorem nv_m7_cong_ht_insert :
    Func.wp m7CongHashEnv full_cong_ht_insert_m7_body
      (nvM7CongCfg.hdr, 0#64, 16#32, ()) nvM7CongMem
      (fun (ret, ()) m' => ∃ s',
        ret = 16#32 ∧ PreservesCoreSlice FullState.core nvM7CongState s' ∧
        s'.LengthsOk nvM7CongCfg ∧ FullExtScratchPres nvM7CongState s' ∧
        M7CongHtCtrlOk nvM7CongCfg s'.scratch.scratch_buf 0 64 8192 ∧
        FullMem nvM7CongCfg s' m')
      (fun _ _ _ _ => False) :=
  m7CongHash_tableImpl.2.2.2.2.2.1.2 _ _ _ _
    ⟨nvM7CongCfg, nvM7CongState, emp, rfl, nvM7Cong_lengths, nvM7CongMem_sep,
     fun ret scr' _ m' _ hlen hcore hpres _ hctrl_all hret hm' => by
       obtain ⟨nsz, hctrl', _, _, _, hnogrow, hpre, _, hslot, hfull⟩ :=
         hctrl_all 64 8192 nvM7Cong_ctrl_ok
       have hnsz : nsz = 8192 := hnogrow (by decide)
       subst hnsz
       have hret16 : ret = 16#32 := by
         rcases hret with rfl | rfl | ⟨ho, nsz', k, mw_e, mw_c, hok, hk, hget, hlt,
             hmw_e, hmw_c, _, _, _, hlits⟩
         · exfalso
           have hf := hfull rfl 0x10000001#32 (by
             dsimp only [nvM7CongState, nvM7CongScratch]
             rw [show (16#32 : BitVec 32).toNat + 1 = 17 from rfl,
               nvM7CongScrBuf_head (by decide)]; decide) (by decide) (by decide)
           have h4 := hf.1 4 (by decide)
           rw [hf.2.1 rfl] at h4
           dsimp only [nvM7CongState, nvM7CongScratch] at h4
           rw [nvM7CongScrBuf_slot (by decide)] at h4
           exact h4 (by decide)
         · rfl
         · exact nvM7Cong_no_equiv_16 hctrl' hpre hslot hok hk hget hlt hmw_e hmw_c hlits
       rw [sep_emp] at hm'
       exact ⟨_, hret16, hcore, hlen, hpres, hctrl', hm'⟩⟩

/-- Concrete `Mem 64` NV (`XPost := False`): `full_cong_ht_insert_m7` auto-grows `8,192 -> 16,384`
on `nvM7CongMemGrow` (`res_sz = 6144`, `75%` load), inserts `16#32`, and preserves both live
colliding entries (`24#32` and `8#32`). -/
theorem nv_m7_cong_ht_insert_grow :
    Func.wp m7CongHashEnv full_cong_ht_insert_m7_body
      (nvM7CongCfg.hdr, 0#64, 16#32, ()) nvM7CongMemGrow
      (fun (ret, ()) m' => ∃ s',
        ret = 16#32 ∧ PreservesCoreSlice FullState.core nvM7CongStateGrow s' ∧
        s'.LengthsOk nvM7CongCfg ∧ FullExtScratchPres nvM7CongStateGrow s' ∧
        M7CongHtCtrlOk nvM7CongCfg s'.scratch.scratch_buf 0 64 16384 ∧
        (∃ jC < 16384, s'.scratch.scratch_buf[64 + jC]? = some 24#32) ∧
        (∃ jA < 16384, s'.scratch.scratch_buf[64 + jA]? = some 8#32) ∧
        FullMem nvM7CongCfg s' m')
      (fun _ _ _ _ => False) :=
  m7CongHash_tableImpl.2.2.2.2.2.1.2 _ _ _ _
    ⟨nvM7CongCfg, nvM7CongStateGrow, emp, rfl, nvM7CongGrow_lengths, nvM7CongMemGrow_sep,
     fun ret scr' _ m' _ hlen hcore hpres _ hctrl_all hret hm' => by
       obtain ⟨nsz, hctrl', _, _, hgrow, _, hpre, hkeep, hslot, hfull⟩ :=
         hctrl_all 64 8192 nvM7Cong_ctrl_ok
       have hnsz : nsz = 16384 :=
         hgrow ⟨0x10000001#32, by
           dsimp only [nvM7CongStateGrow, nvM7CongState, nvM7CongScratch]
           rw [show (16#32 : BitVec 32).toNat + 1 = 17 from rfl,
             nvM7CongScrBuf_head (by decide)]; decide,
           by decide, by decide⟩ (by decide) (by decide) (by decide)
       subst hnsz
       have hret16 : ret = 16#32 := by
         rcases hret with rfl | rfl | ⟨ho, nsz', k, mw_e, mw_c, hok, hk, hget, hlt,
             hmw_e, hmw_c, _, _, _, hlits⟩
         · exfalso
           have hf := hfull rfl 0x10000001#32 (by
             dsimp only [nvM7CongStateGrow, nvM7CongState, nvM7CongScratch]
             rw [show (16#32 : BitVec 32).toNat + 1 = 17 from rfl,
               nvM7CongScrBuf_head (by decide)]; decide) (by decide) (by decide)
           exact hf.2.2 (by decide)
         · rfl
         · exact nvM7Cong_no_equiv_16 hctrl' hpre hslot hok hk hget hlt hmw_e hmw_c hlits
       have hkC : ∃ jC < 16384, scr'[64 + jC]? = some 24#32 :=
         hkeep 24#32 (by decide) ⟨2, by decide, by
           dsimp only [nvM7CongStateGrow, nvM7CongState, nvM7CongScratch]
           rw [nvM7CongScrBuf_slot (by decide)]; decide⟩
       have hkA : ∃ jA < 16384, scr'[64 + jA]? = some 8#32 :=
         hkeep 8#32 (by decide) ⟨3, by decide, by
           dsimp only [nvM7CongStateGrow, nvM7CongState, nvM7CongScratch]
           rw [nvM7CongScrBuf_slot (by decide)]; decide⟩
       rw [sep_emp] at hm'
       exact ⟨_, hret16, hcore, hlen, hpres, hctrl', hkC, hkA, hm'⟩⟩

end NonVacuity

end LeanQbe.T.Examples.Kissat.FullM7CongHash
