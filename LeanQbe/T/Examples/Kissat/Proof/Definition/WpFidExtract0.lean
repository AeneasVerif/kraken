/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.Inv

/-!
# Fid Extract/Solve Sub-Phase Helpers Part 0 (`Proof.Definition.WpFidExtract0`)

Exports:
- `FidK6cTmkReg`, `fid_k6c_tmkReg_*`, `FidK6cTmkClearInv`, `fid_k6c_tmkClear_*`
- `fid_k6c_mask_widx`, `fid_k6c_add1_toNat`, `fid_k6c_bv32_shl1_add1_lt`, `fid_k6c_eid_bits`
- `fid_k6c_entry_bin_bounds`, `fid_k6c_entry_large_bounds`
- `FidK6cClsOk`, `fid_k6c_clsOk_*`, `fid_k6c_bufOk_*`
- `fid_k6c_watch_solve_wp`, `fid_k6c_copy_clause_wp`, `fid_k6c_scan_large_wp`
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Definition

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FidK6Tactics M8K6bTactics FidK6cTactics

public section

/-! ## 1. Pure arithmetic, `tmk`, mask, entry, and `FidK6BufOk` helpers -/

/-- Bijection between `wsort[0..nv)` and non-zero entries of `tarjan_mark[0..cur_vars)`. -/
@[expose] def FidK6cTmkReg (nv cur_vars : Nat) (exp tmk : List (BitVec 32)) : Prop :=
  nv ≤ 2 * cur_vars ∧
  (∀ i, i < nv → (exp[i]?.getD 0#32).toNat < cur_vars ∧
    (tmk[(exp[i]?.getD 0#32).toNat]?.getD 0#32).toNat = i + 1) ∧
  (∀ v, v < cur_vars → tmk[v]?.getD 0#32 ≠ 0#32 →
    ∃ i, i < nv ∧ (exp[i]?.getD 0#32).toNat = v ∧
      (tmk[v]?.getD 0#32).toNat = i + 1)

theorem fid_k6c_tmkReg_init (cur_vars : Nat) (exp tmk : List (BitVec 32))
    (h0 : ∀ v, v < cur_vars → tmk[v]?.getD 0#32 = 0#32) :
    FidK6cTmkReg 0 cur_vars exp tmk :=
  ⟨Nat.zero_le _, fun _ hi => absurd hi (Nat.not_lt_zero _), fun v hv hne => absurd (h0 v hv) hne⟩

theorem fid_k6c_tmkReg_step {nv cur_vars v : Nat} {exp tmk : List (BitVec 32)}
    (hreg : FidK6cTmkReg nv cur_vars exp tmk) (hnv : nv < 2 * cur_vars)
    (hv : v < cur_vars) (hz : tmk[v]?.getD 0#32 = 0#32)
    (hexp : exp.length = 2 * cur_vars ∨ nv < exp.length) (htmk : v < tmk.length)
    (hcv : 2 * cur_vars < 2 ^ 30) :
    FidK6cTmkReg (nv + 1) cur_vars (exp.set nv (BitVec.ofNat 32 v))
      (tmk.set v (BitVec.ofNat 32 (nv + 1))) := by
  have hexplen : nv < exp.length := by rcases hexp with h | h <;> omega
  have hnv1 : nv + 1 < 2 ^ 32 := by omega
  have hv32 : v < 2 ^ 32 := by omega
  refine ⟨by omega, fun i hi => ?_, fun x hx hnz => ?_⟩
  · by_cases hin : i < nv
    · have hexpi := hreg.2.1 i hin
      have hne : (exp[i]?.getD 0#32).toNat ≠ v := by
        intro heq; have hnz := hexpi.2; rw [heq, hz] at hnz; simp at hnz
      have he1 : ((exp.set nv (BitVec.ofNat 32 v))[i]?.getD 0#32).toNat =
          (exp[i]?.getD 0#32).toNat := by simp [List.getElem?_set_ne (by omega : nv ≠ i)]
      rw [he1]
      have ht1 :
          ((tmk.set v (BitVec.ofNat 32 (nv + 1)))[(exp[i]?.getD 0#32).toNat]?.getD 0#32).toNat =
          (tmk[(exp[i]?.getD 0#32).toNat]?.getD 0#32).toNat := by
        simp [List.getElem?_set_ne (Ne.symm hne)]
      rw [ht1]; exact hexpi
    · have hieq : i = nv := by omega
      subst hieq; simp [hexplen, htmk, Nat.mod_eq_of_lt hv32, Nat.mod_eq_of_lt hnv1, hv]
  · by_cases hxv : x = v
    · subst hxv; exact ⟨nv, by omega, by simp [hexplen, Nat.mod_eq_of_lt hv32],
        by simp [htmk, Nat.mod_eq_of_lt hnv1]⟩
    · have ht1 : (tmk.set v (BitVec.ofNat 32 (nv + 1)))[x]? = tmk[x]? :=
        List.getElem?_set_ne (Ne.symm hxv)
      rw [ht1] at hnz; rcases hreg.2.2 x hx hnz with ⟨i, hi, hexi, hti⟩
      exact ⟨i, by omega, by simpa [List.getElem?_set_ne (by omega : nv ≠ i)] using hexi,
        by simpa [ht1] using hti⟩

theorem fid_k6c_tmkReg_bound {nv cur_vars v : Nat} {exp tmk : List (BitVec 32)}
    (hreg : FidK6cTmkReg nv cur_vars exp tmk) (hv : v < cur_vars)
    (ht : v < tmk.length) (hnz : tmk[v] ≠ 0#32) : ∃ i, i < nv ∧ (tmk[v]).toNat = i + 1 := by
  rcases hreg.2.2 v hv (by simpa [List.getElem?_eq_getElem ht] using hnz) with ⟨i, hi, _, hti⟩
  exact ⟨i, hi, by simpa [List.getElem?_eq_getElem ht] using hti⟩

/-- Partial-clearing invariant for `for (i = k; i < nv; i++) tmk[exp[i]] = 0;`. -/
@[expose] def FidK6cTmkClearInv (k nv cur_vars : Nat) (exp tmk : List (BitVec 32)) : Prop :=
  k ≤ nv ∧
  (∀ i, k ≤ i → i < nv → (exp[i]?.getD 0#32).toNat < cur_vars ∧
    (tmk[(exp[i]?.getD 0#32).toNat]?.getD 0#32).toNat = i + 1) ∧
  (∀ v, v < cur_vars → tmk[v]?.getD 0#32 ≠ 0#32 →
    ∃ i, k ≤ i ∧ i < nv ∧ (exp[i]?.getD 0#32).toNat = v ∧
      (tmk[v]?.getD 0#32).toNat = i + 1)

theorem fid_k6c_tmkClear_init {nv cur_vars : Nat} {exp tmk : List (BitVec 32)}
    (hreg : FidK6cTmkReg nv cur_vars exp tmk) :
    FidK6cTmkClearInv 0 nv cur_vars exp tmk :=
  ⟨Nat.zero_le _, fun i _ hi => hreg.2.1 i hi,
   fun v hv hnz => by
     rcases hreg.2.2 v hv hnz with ⟨i, hi, hx, ht⟩
     exact ⟨i, Nat.zero_le _, hi, hx, ht⟩⟩

theorem fid_k6c_tmkClear_step {k nv cur_vars : Nat} {exp tmk : List (BitVec 32)}
    (hinv : FidK6cTmkClearInv k nv cur_vars exp tmk) (hk : k < nv)
    (hexp : k < exp.length) (htmk : cur_vars ≤ tmk.length) :
    FidK6cTmkClearInv (k + 1) nv cur_vars exp
      (tmk.set (exp[k]).toNat 0#32) := by
  have hkinfo := hinv.2.1 k (Nat.le_refl k) hk
  have hkget : exp[k]?.getD 0#32 = exp[k] := by simp [List.getElem?_eq_getElem hexp]
  rw [hkget] at hkinfo
  have hklt : (exp[k]).toNat < tmk.length := by omega
  refine ⟨by omega, ?_, ?_⟩
  · intro i hki hi
    have hiinfo := hinv.2.1 i (by omega) hi
    refine ⟨hiinfo.1, ?_⟩
    have hne : (exp[k]).toNat ≠ (exp[i]?.getD 0#32).toNat := by
      intro heq; have h2 := hiinfo.2; rw [← heq, hkinfo.2] at h2; omega
    simpa [List.getElem?_set_ne hne] using hiinfo.2
  · intro v hv hnz
    have hnev : (exp[k]).toNat ≠ v := by
      intro heq; subst heq
      have hset : (tmk.set (exp[k]).toNat 0#32)[(exp[k]).toNat]? = some 0#32 :=
        List.getElem?_set_self hklt
      simp [hset] at hnz
    rw [List.getElem?_set_ne hnev] at hnz
    rcases hinv.2.2 v hv hnz with ⟨i, hki, hi, hexi, hti⟩
    have hki' : k + 1 ≤ i := by
      by_cases hkeq : i = k
      · subst hkeq; rw [hkget] at hexi; exact absurd hexi hnev
      · omega
    exact ⟨i, hki', hi, hexi, by simpa [List.getElem?_set_ne hnev] using hti⟩

theorem fid_k6c_tmkClear_done {nv cur_vars : Nat} {exp tmk : List (BitVec 32)}
    (hinv : FidK6cTmkClearInv nv nv cur_vars exp tmk) :
    ∀ v, v < cur_vars → tmk[v]?.getD 0#32 = 0#32 := by
  intro v hv
  by_cases hz : tmk[v]?.getD 0#32 = 0#32
  · exact hz
  · rcases hinv.2.2 v hv hz with ⟨i, h1, h2, _, _⟩; omega

theorem fid_k6c_mask_widx {mbase eid : BitVec 32}
    (hm : mbase = 4002#32 ∨ mbase = 4066#32) (heid : eid.toNat < 2001) :
    let widx := mbase + (eid >>> 5)
    4002 ≤ widx.toNat ∧ widx.toNat < 4130 ∧
      widx.setWidth 64 = BitVec.ofNat 64 widx.toNat := by
  have hsh : (eid >>> 5).toNat = eid.toNat / 32 := by bv_omega
  have h0 : (4002#32 : BitVec 32).toNat = 4002 := rfl
  have h1 : (4066#32 : BitVec 32).toNat = 4066 := rfl
  have hbv : (mbase + (eid >>> 5)).toNat = mbase.toNat + eid.toNat / 32 := by
    rcases hm with rfl | rfl <;> bv_omega
  have hlo : 4002 ≤ (mbase + (eid >>> 5)).toNat := by
    rcases hm with rfl | rfl <;> omega
  have hhi : (mbase + (eid >>> 5)).toNat < 4130 := by
    rcases hm with rfl | rfl <;> omega
  refine ⟨hlo, hhi, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

theorem fid_k6c_add1_toNat {x : BitVec 32} {lim : Nat}
    (hx : x.toNat < lim) (hl : lim < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 :=
  m8_bv32_add1_toNat hx hl

theorem fid_k6c_bv32_shl1_add1_lt {x : BitVec 32} {n : Nat}
    (hx : x.toNat < n) (hn : 2 * n + 1 < 2 ^ 30) :
    (x <<< 1).toNat = 2 * x.toNat ∧
    (x <<< 1 ||| 1#32).toNat = 2 * x.toNat + 1 :=
  ⟨m8_bv32_shl1_toNat (by omega), m8_bv32_shl1_or1_toNat (by omega)⟩

theorem fid_k6c_eid_bits {side eid : BitVec 32}
    (hs : side = 0#32 ∨ side = 1#32) (he : eid.toNat < 2001) :
    let raw := (side <<< 11) ||| eid
    raw.toNat < 4096 ∧
    (raw &&& 2047#32).toNat = eid.toNat ∧
    (raw >>> 11 = 0#32 ↔ side = 0#32) ∧
    (raw &&& 2047#32) = eid := by
  have hlt11 : eid.toNat < 2 ^ 11 := by omega
  have hmask : ∀ r : BitVec 32, (r &&& 2047#32).toNat = r.toNat % 2048 := fun r => by
    rw [BitVec.toNat_and, show (2047#32 : BitVec 32).toNat = 2 ^ 11 - 1 by decide]
    exact Nat.and_two_pow_sub_one_eq_mod r.toNat 11
  have heid_m : eid &&& 2047#32 = eid :=
    BitVec.eq_of_toNat_eq (by rw [hmask, Nat.mod_eq_of_lt hlt11])
  have heid_s : eid >>> 11 = 0#32 := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt11]; rfl)
  rcases hs with rfl | rfl
  · have hz : (0#32 <<< 11 ||| eid) = eid := by simp [BitVec.zero_shiftLeft]
    rw [hz]; exact ⟨by omega, by rw [heid_m], ⟨fun _ => rfl, fun _ => heid_s⟩, heid_m⟩
  · rw [show (1#32 <<< 11) = 2048#32 by decide]
    have hlt4k : (2048#32 ||| eid).toNat < 4096 := by
      rw [BitVec.toNat_or, show (2048#32 : BitVec 32).toNat = 2048 by decide]
      exact Nat.or_lt_two_pow (by decide : 2048 < 2 ^ 12) (by omega : eid.toNat < 2 ^ 12)
    have hm : (2048#32 ||| eid) &&& 2047#32 = eid := by
      rw [BitVec.and_or_distrib_right, show (2048#32 &&& 2047#32) = 0#32 by decide, heid_m,
        BitVec.zero_or]
    have hshr : (2048#32 ||| eid) >>> 11 ≠ 0#32 := by
      have : ((2048#32 ||| eid) >>> 11) = (2048#32 >>> 11) ||| (eid >>> 11) := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ushiftRight, BitVec.toNat_or, BitVec.toNat_or,
          BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight]; exact Nat.shiftRight_or_distrib
      rw [this, heid_s, show (2048#32 >>> 11) = 1#32 by decide]; decide
    exact ⟨hlt4k, by rw [hm], ⟨fun h => absurd h hshr, fun h => by cases h⟩, hm⟩

theorem fid_k6c_entry_bin_bounds {F_cur : List (List Nat)} {s : FullState}
    {lit : Nat} {w : BitVec 32} (he : FullBveEntryOkW F_cur s lit w)
    (hbin : w &&& 2147483648#32 ≠ 0#32) :
    (w &&& 2147483647#32).toNat < 2 * s.core.cur_vars ∧
    (w &&& 2147483647#32).toNat / 2 < s.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w &&& 2147483647#32).toNat]) := by
  rw [FullBveEntryOkW, ite_eq_left_iff.mpr (fun h => absurd hbin h)] at he
  exact ⟨he.1, by omega, he.2⟩

theorem fid_k6c_entry_large_bounds {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {lit : Nat} {w : BitVec 32}
    (hl : s.LengthsOk c) (ha : FullArenaClausesInv c F_cur s.core)
    (he : FullBveEntryOkW F_cur s lit w) (hnbin : w &&& 2147483648#32 = 0#32) :
    w.toNat + 3 ≤ s.core.arena_len ∧ 3 ≤ fullArenaClauseSizeCore s.core w.toNat ∧
    w.toNat + 3 + fullArenaClauseSizeCore s.core w.toNat ≤ s.core.arena_len ∧
    s.core.arena_len ≤ c.arena_cap ∧
    (∀ k, k < fullArenaClauseSizeCore s.core w.toNat → w.toNat + 3 + k < s.core.arena.length ∧
      (s.core.arena[w.toNat + 3 + k]?.getD 0#32).toNat < 2 * s.core.cur_vars) := by
  have hc : ¬ (w &&& 2147483648#32 ≠ 0#32) := by simp [hnbin]
  dsimp only [FullBveEntryOkW] at he; simp only [hc, ite_false] at he
  have hw := ha.refs_wf w.toNat he.1
  have hlits := ha.lits_lt w.toNat he.1 he.2
  have harlen : s.core.arena_len ≤ c.arena_cap := hl.core_ok.arena_len_le
  have harlen2 : s.core.arena.length = c.arena_cap := hl.core_ok.arena_len_arr
  refine ⟨hw.1, hw.2.1, by omega, harlen, fun k hk => ?_⟩
  have hklen : w.toNat + 3 + k < s.core.arena.length := by omega
  refine ⟨hklen, hlits _ ?_⟩
  simp only [fullArenaClauseLitsCore, List.mem_map]
  refine ⟨s.core.arena[w.toNat + 3 + k], ?_, by simp [List.getElem?_eq_getElem hklen]⟩
  have hk' : k < (List.take (fullArenaClauseSizeCore s.core w.toNat)
      (List.drop (w.toNat + 3) s.core.arena)).length := by simp [List.length_take]; omega
  rw [← (by simp [List.getElem_take, List.getElem_drop, Nat.add_assoc] :
    (List.take (fullArenaClauseSizeCore s.core w.toNat)
      (List.drop (w.toNat + 3) s.core.arena))[k] = s.core.arena[w.toNat + 3 + k])]
  exact List.getElem_mem hk'

/-- Clause invariants held in scratch buffer before `init_solve`. -/
@[expose] def FidK6cClsOk (mv_nat nc_n alen_n n_units_n : Nat)
    (scr : List (BitVec 32)) : Prop :=
  nc_n ≤ 4 * mv_nat ∧
  (∀ cid, cid < nc_n →
    let off := (scr[4224 + 29 * mv_nat + cid]?.getD 0#32).toNat
    let cm := scr[4224 + 33 * mv_nat + cid]?.getD 0#32
    let aux := scr[4224 + 37 * mv_nat + cid]?.getD 0#32
    let sz := (cm &&& 65535#32).toNat
    off + sz ≤ alen_n ∧ (cm &&& 1073741824#32) = 0#32 ∧
      aux.toNat < 4096 ∧ (aux &&& 2047#32).toNat < 2001) ∧
  n_units_n ≤ nc_n

theorem fid_k6c_clsOk_empty (mv_nat : Nat) (scr : List (BitVec 32)) :
    FidK6cClsOk mv_nat 0 0 0 scr :=
  ⟨Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _), Nat.le_refl _⟩

theorem fid_k6c_clsOk_frame {mv_nat nc_n alen_n n_units_n : Nat}
    {scr scr' : List (BitVec 32)}
    (h : FidK6cClsOk mv_nat nc_n alen_n n_units_n scr)
    (hpre : ∀ idx, 4224 + 29 * mv_nat ≤ idx → idx < 4224 + 41 * mv_nat →
      scr'[idx]? = scr[idx]?) :
    FidK6cClsOk mv_nat nc_n alen_n n_units_n scr' := by
  refine ⟨h.1, fun cid hcid => ?_, h.2.2⟩
  have hnc_le := h.1
  have hc := h.2.1 cid hcid
  have h1 := hpre (4224 + 29 * mv_nat + cid) (by omega) (by omega)
  have h2 := hpre (4224 + 33 * mv_nat + cid) (by omega) (by omega)
  have h3 := hpre (4224 + 37 * mv_nat + cid) (by omega) (by omega)
  simpa [h1, h2, h3] using hc

theorem fid_k6c_bufOk_of_init {scr : List (BitVec 32)} {mv_s nc alen acap_s : BitVec 32}
    {cap : Nat}
    (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (hcap : 4224 + 45 * mv_s.toNat + acap_s.toNat ≤ scr.length)
    (hlen_lt : scr.length < 2 ^ 30)
    (hscr4193 : scr[4193]? = some nc) (hscr4206 : scr[4206]? = some alen)
    (hscr4207 : scr[4207]? = some acap_s) (hscr4214 : scr[4214]? = some mv_s)
    (hnc : nc.toNat ≤ 4 * mv_s.toNat) (halen : alen.toNat ≤ acap_s.toNat)
    (hcls : FidK6cClsOk mv_s.toNat nc.toNat alen.toNat cap scr) :
    FidK6BufOk scr := by
  dsimp only [FidK6BufOk]
  rw [hscr4214, hscr4193, hscr4206, hscr4207]
  simp only [Option.getD_some]
  refine ⟨hmv_lo, hmv_hi, hcap, hlen_lt, hnc, halen, ?_⟩
  intro cid hcid
  have hc := hcls.2.1 cid hcid
  refine ⟨by omega, fun hlrn => absurd hc.2.1 hlrn⟩

theorem fid_k6c_bufOk_watch_frame {scr scr' : List (BitVec 32)} {mv : Nat}
    (hok : FidK6BufOk scr) (hscr' : scr'.length = scr.length)
    (hmv : mv = (scr[4214]?.getD 0#32).toNat)
    (hagree : ∀ idx, idx < scr.length → idx < 4224 + 11 * mv ∨ 4224 + 29 * mv ≤ idx →
      scr'[idx]? = scr[idx]?) :
    FidK6BufOk scr' := by
  subst hmv
  apply fidK6BufOk_of_frame hok hscr'
  intro idx hidx
  dsimp only
  intro hregion
  have hmv_lo := hok.mv_lo
  apply hagree idx hidx
  rcases hregion with rfl | rfl | rfl | rfl | ⟨h1, _⟩
  · left; omega
  · left; omega
  · left; omega
  · left; omega
  · right; exact h1

/-! ## 2. Sub-phase 1: `watch_solve` (`watch` loop + `solve` + `core` + bitmask) -/

private theorem fid_k6c_post_core_mask_wp {Γ : Env} {c : FullCfg}
    {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m3 : Mem 64} {Q : Post [Ty.bool]} {X : XPost}
    {scr0 scr scr3 : List (BitVec 32)} {nc : BitVec 32} {fuel64 : BitVec 64}
    {mv_s o_cl_meta o_cl_aux : BitVec 32}
    (hinv : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s) (hcap : 16384 ≤ c.scratch_cap)
    (hscr_len : scr.length = c.scratch_cap) (hlen3 : scr3.length = c.scratch_cap)
    (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (hnc_le : nc.toNat ≤ 4 * mv_s.toNat)
    (hoff_meta : o_cl_meta = 4224#32 + 33#32 * mv_s)
    (hoff_aux : o_cl_aux = 4224#32 + 37#32 * mv_s)
    (hok3 : FidK6BufOk scr3)
    (hscr3_4194 : scr3[4194]? = some nc) (hscr3_4214 : scr3[4214]? = some mv_s)
    (hscr3_pre0 : ∀ i, i < 4002 → scr3[i]? = scr0[i]?)
    (hscr3_pre1 : ∀ i, 4132 ≤ i → i < 4192 → scr3[i]? = scr0[i]?)
    (hscr3_aux : ∀ cid, cid < nc.toNat →
      scr3[4224 + 37 * mv_s.toNat + cid]? = scr[4224 + 37 * mv_s.toNat + cid]?)
    (haux_ok : ∀ cid, cid < nc.toNat →
      let raw := scr[4224 + 37 * mv_s.toNat + cid]?.getD 0#32
      raw.toNat < 4096 ∧ (raw &&& 2047#32).toNat < 2001)
    (hfuel2 : fuel64.toNat ≤ s.core.fuel.toNat)
    (hm3' : (FullMem c (FidP6Scr
      { core := { s.core with fuel := fuel64 },
        scratch := { s.scratch with scratch_buf := scr3 } } scr3) ⋆ R) m3)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i, i < 4002 → s'.scratch.scratch_buf[i]? = scr0[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → s'.scratch.scratch_buf[i]? = scr0[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X
      (Expr.group (fun Js_1 : Tup Cont [[i32]] => Blocks.cons (fun pz : Tup Val [i32] =>
        Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pz.fst, Arg.imm 128, ()))
          fun p_3 =>
        Expr.jnz (Arg.var p_3.fst)
          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 4002, Arg.var pz.fst, ())) fun p_4 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_4.fst, ())) fun p_5 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_5.fst, Arg.imm 4, ())) fun p_6 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_6.fst, ()))
            fun p_7 =>
          Expr.store (t := i32) (Arg.imm 0) (Arg.var p_7.fst)
            (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pz.fst, Arg.imm 1, ())) fun p_8 =>
              Expr.jump Js_1.fst (Arg.var p_8.fst, ())))
          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4194, ())) fun p_4 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_4.fst, Arg.imm 4, ())) fun p_5 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_5.fst, ()))
            fun p_6 =>
          Expr.load i32 (Arg.var p_6.fst) fun onc =>
          Expr.group (fun Js_2 : Tup Cont [[i32, Ty.bool]] =>
            Blocks.cons (fun pc : Tup Val [i32, Ty.bool] =>
              Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl)
                (Arg.var pc.fst, Arg.var onc, ())) fun p_7 =>
              Expr.jnz (Arg.var p_7.fst)
                (Expr.group (fun _ : Tup Cont [[Ty.bool]] =>
                  Blocks.cons (fun pn : Tup Val [Ty.bool] =>
                    Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pc.fst, Arg.imm 1, ()))
                      fun p_8 => Expr.jump Js_2.fst (Arg.var p_8.fst, Arg.var pn.fst, ()))
                    Blocks.nil) fun Js_3 =>
                Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_meta, Arg.var pc.fst, ()))
                  fun p_8 =>
                Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_8.fst, ())) fun p_9 =>
                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_9.fst, Arg.imm 4, ()))
                  fun p_10 =>
                Expr.let_ (Op.mk (OpCode.add i64)
                  (Arg.var c.pScratchBuf, Arg.var p_10.fst, ())) fun p_11 =>
                Expr.load i32 (Arg.var p_11.fst) fun cm =>
                Expr.let_ (Op.mk (OpCode.and i32) (Arg.var cm, Arg.imm 2147483648, ()))
                  fun p_12 =>
                Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl)
                  (Arg.var p_12.fst, Arg.imm 0, ())) fun p_13 =>
                Expr.jnz (Arg.var p_13.fst)
                  (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_aux, Arg.var pc.fst, ()))
                    fun p_14 =>
                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_14.fst, ())) fun p_15 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_15.fst, Arg.imm 4, ()))
                    fun p_16 =>
                  Expr.let_ (Op.mk (OpCode.add i64)
                    (Arg.var c.pScratchBuf, Arg.var p_16.fst, ())) fun p_17 =>
                  Expr.load i32 (Arg.var p_17.fst) fun raw =>
                  Expr.let_ (Op.mk (OpCode.and i32) (Arg.var raw, Arg.imm 2047, ()))
                    fun eid =>
                  Expr.group (fun _ : Tup Cont [[i32]] => Blocks.cons (fun pm =>
                    Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var eid.fst, Arg.imm 5, ()))
                      fun p_18 =>
                    Expr.let_ (Op.mk (OpCode.add i32)
                      (Arg.var pm.fst, Arg.var p_18.fst, ())) fun p_19 =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_19.fst, ()))
                      fun p_20 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_20.fst, Arg.imm 4, ()))
                      fun p_21 =>
                    Expr.let_ (Op.mk (OpCode.add i64)
                      (Arg.var c.pScratchBuf, Arg.var p_21.fst, ())) fun p_22 =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_19.fst, ())) fun p_23 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_23.fst, Arg.imm 4, ()))
                      fun p_24 =>
                    Expr.let_ (Op.mk (OpCode.add i64)
                      (Arg.var c.pScratchBuf, Arg.var p_24.fst, ())) fun p_25 =>
                    Expr.load i32 (Arg.var p_25.fst) fun cur =>
                    Expr.let_ (Op.mk (OpCode.and i32) (Arg.var eid.fst, Arg.imm 31, ()))
                      fun p_26 =>
                    Expr.let_ (Op.mk (OpCode.shl i32) (Arg.imm 1, Arg.var p_26.fst, ()))
                      fun p_27 =>
                    Expr.let_ (Op.mk (OpCode.or i32) (Arg.var cur, Arg.var p_27.fst, ()))
                      fun p_28 =>
                    Expr.store (Arg.var p_28.fst) (Arg.var p_22.fst)
                      (Expr.jump Js_3.fst (Arg.imm true, ()))) Blocks.nil)
                  fun Js_4 =>
                  Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var raw, Arg.imm 11, ()))
                    fun p_18 =>
                  Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                    (Arg.var p_18.fst, Arg.imm 0, ())) fun p_19 =>
                  Expr.jnz (Arg.var p_19.fst)
                    (Expr.jump Js_4.fst (Arg.imm 4002, ()))
                    (Expr.jump Js_4.fst (Arg.imm 4066, ())))
                  (Expr.jump Js_3.fst (Arg.var pc.snd.fst, ())))
                (Expr.group (fun _ : Tup Cont [[]] =>
                  Blocks.cons (fun _ => Expr.ret (Arg.var pc.snd.fst, ())) Blocks.nil)
                  fun Js_3 =>
                Expr.jnz (Arg.var pc.snd.fst)
                  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4130, ())) fun p_8 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_8.fst, Arg.imm 4, ()))
                    fun p_9 =>
                  Expr.let_ (Op.mk (OpCode.add i64)
                    (Arg.var c.pScratchBuf, Arg.var p_9.fst, ())) fun p_10 =>
                  Expr.store (t := i32) (Arg.imm 1) (Arg.var p_10.fst)
                    (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4131, ())) fun p_11 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_11.fst, Arg.imm 4, ()))
                      fun p_12 =>
                    Expr.let_ (Op.mk (OpCode.add i64)
                      (Arg.var c.pScratchBuf, Arg.var p_12.fst, ())) fun p_13 =>
                    Expr.store (t := i32) (Arg.imm 1) (Arg.var p_13.fst)
                      (Expr.jump Js_3.fst ())))
                  (Expr.jump Js_3.fst ()))) Blocks.nil)
            fun Js_2 => Expr.jump Js_2.fst (Arg.imm 0, Arg.imm false, ())))
      Blocks.nil) fun Js_1 => Expr.jump Js_1.fst (Arg.imm 0, ())) m3 := by
  let s2 : FullState :=
    { core := { s.core with fuel := fuel64 }
      scratch := { s.scratch with scratch_buf := scr3 } }
  have htmk2 : TmkZero s2 := htmk
  apply wp_loop_inv
    (Inv := fun (pz : BitVec 32 × Unit) mZ => ∃ scrZ : List (BitVec 32),
      pz.1.toNat ≤ 128 ∧ scrZ.length = c.scratch_cap ∧
      (∀ i, i < 4002 ∨ 4130 ≤ i → scrZ[i]? = scr3[i]?) ∧
      (FullMem c (FidP6Scr s2 scrZ) ⋆ R) mZ)
    (μ := fun (pz : BitVec 32 × Unit) _ => 128 - pz.1.toNat)
  · intro Jz hJz
    c0_hsteps
    exact hJz _ _ ⟨scr3, Nat.zero_le _, hlen3, fun _ _ => rfl, hm3'⟩
  · intro Jz pz mZ ⟨scrZ, hz_le, hlenZ, hagZ, hmZ⟩ hcontZ
    dsimp only [Blocks.get, Member.here]
    c0_hsteps
    · have hz_lt : pz.fst.toNat < 128 := by bv_omega
      let idxZ := (BitVec.setWidth 64 (4002#32 + pz.fst)).toNat
      have hidxZ : idxZ = 4002 + pz.fst.toNat := by dsimp only [idxZ]; bv_omega
      have hidxZ_lt : idxZ < scrZ.length := by omega
      c0_hsteps
      refine hcontZ _ _ (by bv_omega) ⟨scrZ.set idxZ 0#32, by bv_omega, by simp [hlenZ],
        fun i hi => by
          have hne : idxZ ≠ i := by omega
          rw [List.getElem?_set_ne hne, hagZ i hi],
        hm⟩
    · have hscrZ_4194 : scrZ[4194]? = some nc := by
        rw [hagZ 4194 (by right; omega), hscr3_4194]
      have hZ_4194 : 4194 < scrZ.length := by omega
      have hscrZ_4194_val : scrZ[OfNat.ofNat 4194 % 2 ^ 64] = nc :=
        (Option.some.inj (by
          simpa [List.getElem?_eq_getElem hZ_4194] using hscrZ_4194.symm)).symm
      c0_hsteps
      apply wp_loop_inv
        (Inv := fun (pc : BitVec 32 × Bool × Unit) mC => ∃ scrC : List (BitVec 32),
          pc.1.toNat ≤ nc.toNat ∧ scrC.length = c.scratch_cap ∧
          (∀ i, i < 4002 ∨ 4130 ≤ i → scrC[i]? = scr3[i]?) ∧
          (FullMem c (FidP6Scr s2 scrC) ⋆ R) mC)
        (μ := fun (pc : BitVec 32 × Bool × Unit) _ => nc.toNat - pc.1.toNat)
      · intro Jc hJc; c0_hsteps; exact hJc _ _ ⟨scrZ, Nat.zero_le _, hlenZ, hagZ, hmZ⟩
      · intro Jc pc mC ⟨scrC, hc_le, hlenC, hagC, hmC⟩ hcontC
        dsimp only [Blocks.get, Member.here]
        c0_hsteps
        · have hc_lt : pc.fst.toNat < nc.toNat := by
            rw [← hscrZ_4194_val]; bv_omega
          have hmbase_C : 4224 + 45 * mv_s.toNat ≤ scrC.length := by
            have := hok3.base_ge; rw [hscr3_4214, hlen3] at this
            simp only [Option.getD_some] at this; omega
          let idxM := (BitVec.setWidth 64 (o_cl_meta + pc.fst)).toNat
          let idxA := (BitVec.setWidth 64 (o_cl_aux + pc.fst)).toNat
          have hidxM : idxM = 4224 + 33 * mv_s.toNat + pc.fst.toNat := by
            dsimp only [idxM]; rw [hoff_meta]
            exact fid_k6_off_add hmv_hi (by omega) (by omega)
          have hidxM_lt : idxM < scrC.length := by omega
          have hidxA : idxA = 4224 + 37 * mv_s.toNat + pc.fst.toNat := by
            dsimp only [idxA]; rw [hoff_aux]
            exact fid_k6_off_add hmv_hi (by omega) (by omega)
          have hidxA_lt : idxA < scrC.length := by omega
          have hraw_eq :
              scrC[idxA] = scr[4224 + 37 * mv_s.toNat + pc.fst.toNat]?.getD 0#32 := by
            have hg2 : scrC[4224 + 37 * mv_s.toNat + pc.fst.toNat]? = some scrC[idxA] := by
              rw [← hidxA]; exact List.getElem?_eq_getElem hidxA_lt
            rw [hagC _ (by right; omega), hscr3_aux pc.fst.toNat hc_lt] at hg2
            exact congrArg (Option.getD · 0#32) hg2.symm
          have hraw_ok := haux_ok pc.fst.toNat hc_lt
          rw [← hraw_eq] at hraw_ok
          c0_hsteps
          · have hwi := fid_k6c_mask_widx (Or.inl rfl) hraw_ok.2
            let widx0 := (BitVec.setWidth 64
              (4002#32 + ((scrC[idxA] &&& 2047#32) >>> 5))).toNat
            have hwi_lt : widx0 < scrC.length := by
              dsimp only [widx0]; rw [hwi.2.2]; simp only [BitVec.toNat_ofNat]; omega
            c0_hsteps
            refine hcontC (pc.fst + 1#32, true, ()) _ (by bv_omega)
              ⟨scrC.set widx0 _, by bv_omega,
                by simp [hlenC], fun i hi => by
                  have hne : widx0 ≠ i := by
                    dsimp only [widx0]
                    rw [hwi.2.2]; simp only [BitVec.toNat_ofNat]; omega
                  rw [List.getElem?_set_ne hne, hagC i hi],
                hm⟩
          · have hwi := fid_k6c_mask_widx (Or.inr rfl) hraw_ok.2
            let widx1 := (BitVec.setWidth 64
              (4066#32 + ((scrC[idxA] &&& 2047#32) >>> 5))).toNat
            have hwi_lt : widx1 < scrC.length := by
              dsimp only [widx1]; rw [hwi.2.2]; simp only [BitVec.toNat_ofNat]; omega
            c0_hsteps
            refine hcontC (pc.fst + 1#32, true, ()) _ (by bv_omega)
              ⟨scrC.set widx1 _, by bv_omega,
                by simp [hlenC], fun i hi => by
                  have hne : widx1 ≠ i := by
                    dsimp only [widx1]
                    rw [hwi.2.2]; simp only [BitVec.toNat_ofNat]; omega
                  rw [List.getElem?_set_ne hne, hagC i hi],
                hm⟩
          · refine hcontC (pc.fst + 1#32, pc.snd.fst, ()) _ (by bv_omega)
              ⟨scrC, by bv_omega, hlenC, hagC, hmC⟩
        · have hlt4130 : (BitVec.setWidth 64 4130#32).toNat < scrC.length := by bv_omega
          have hlt4131 : (BitVec.setWidth 64 4131#32).toNat <
              (scrC.set (BitVec.setWidth 64 4130#32).toNat 1#32).length := by
            simp [hlenC]; omega
          c0_hsteps
          try rw [hc]
          let scrOut := (scrC.set 4130 1#32).set 4131 1#32
          have htmkOut : TmkZero (FidP6Scr s2 scrOut) := htmk2
          have hinvOut : FullDenseInvW c F0 F_cur (FidP6Scr s2 scrOut) :=
            m8_fullDenseInvW_scr_fuel hinv (by simp [scrOut, hlenC]) fuel64
          exact hQ true (FidP6Scr s2 scrOut) _ hinvOut htmkOut rfl rfl rfl hfuel2
            (fun i hi => by
              dsimp only [FidP6Scr, scrOut]
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
              rw [hagC i (Or.inl hi), hscr3_pre0 i hi])
            (fun i h1 h2 => by
              dsimp only [FidP6Scr, scrOut]
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
              rw [hagC i (Or.inr (by omega)), hscr3_pre1 i h1 h2])
            hm
        · try rw [hc]
          exact hQ false (FidP6Scr s2 scrC) _
            (m8_fullDenseInvW_scr_fuel hinv hlenC fuel64)
            htmk2 rfl rfl rfl hfuel2
            (fun i hi => by rw [hagC i (Or.inl hi), hscr3_pre0 i hi])
            (fun i h1 h2 => by rw [hagC i (Or.inr (by omega)), hscr3_pre1 i h1 h2])
            hmC

/-- Watch-solve sub-program theorem for `full_k6_extract_and_solve_fid`. -/
theorem fid_k6c_watch_solve_wp {Γ : Env}
    (hwatch : ∀ a m Q X, fidK6WatchSpec a m Q X →
      Γ "full_k6_watch_fid" [i64, i32, i32, i32, i32] [] a m Q X)
    (hsolve : ∀ a m Q X, fidK6SolveSpec a m Q X →
      Γ "full_k6_solve_fid" [i64, i32] [i64] a m Q X)
    (hcore : ∀ a m Q X, fidK6CoreSpec a m Q X →
      Γ "full_k6_core_fid" [i64] [] a m Q X)
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [Ty.bool]} {X : XPost}
    {scr scr0 : List (BitVec 32)} {nc tick_lim : BitVec 32}
    {mv_s o_cl_off o_cl_meta o_cl_aux o_arena : BitVec 32}
    (hinv : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s) (hcap : 16384 ≤ c.scratch_cap)
    (hscr_len : scr.length = c.scratch_cap)
    (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (hoff_off : o_cl_off = 4224#32 + 29#32 * mv_s)
    (hoff_meta : o_cl_meta = 4224#32 + 33#32 * mv_s)
    (hoff_aux : o_cl_aux = 4224#32 + 37#32 * mv_s)
    (hoff_ar : o_arena = 4224#32 + 45#32 * mv_s)
    (hok : FidK6BufOk scr)
    (hscr4193 : scr[4193]? = some nc) (hscr4194 : scr[4194]? = some nc)
    (hscr4214 : scr[4214]? = some mv_s)
    (haux_ok : ∀ cid, cid < nc.toNat →
      let raw := scr[4224 + 37 * mv_s.toNat + cid]?.getD 0#32
      raw.toNat < 4096 ∧ (raw &&& 2047#32).toNat < 2001)
    (hpre0 : ∀ i, i < 4002 → scr[i]? = scr0[i]?)
    (hpre1 : ∀ i, 4132 ≤ i → i < 4192 → scr[i]? = scr0[i]?)
    (hm : (FullMem c (FidP6Scr s scr) ⋆ R) m)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i, i < 4002 → s'.scratch.scratch_buf[i]? = scr0[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → s'.scratch.scratch_buf[i]? = scr0[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X
      (Expr.group
        (fun Js : Tup Cont [[i32]] => Blocks.cons (fun p : Tup Val [i32] =>
          Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var p.fst, Arg.var nc, ()))
            fun p_1 =>
          Expr.jnz (Arg.var p_1.fst)
            (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_meta, Arg.var p.fst, ())) fun p_2 =>
            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_2.fst, ())) fun p_3 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_3.fst, Arg.imm 4, ())) fun p_4 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_4.fst, ()))
              fun p_5 =>
            Expr.load i32 (Arg.var p_5.fst) fun ld =>
            Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld, Arg.imm 65535, ())) fun p_6 =>
            Expr.group (fun _ : Tup Cont [[]] => Blocks.cons (fun _ =>
              Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p.fst, Arg.imm 1, ())) fun p_7 =>
              Expr.jump Js.fst (Arg.var p_7.fst, ())) Blocks.nil) fun Js_1 =>
            Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl) (Arg.var p_6.fst, Arg.imm 2, ()))
              fun p_7 =>
            Expr.jnz (Arg.var p_7.fst)
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_off, Arg.var p.fst, ())) fun p_8 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_8.fst, ())) fun p_9 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_9.fst, Arg.imm 4, ())) fun p_10 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_10.fst, ()))
                fun p_11 =>
              Expr.load i32 (Arg.var p_11.fst) fun ld_1 =>
              Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_arena, Arg.var ld_1, ())) fun p_12 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_12.fst, ())) fun p_13 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_13.fst, Arg.imm 4, ())) fun p_14 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_14.fst, ()))
                fun p_15 =>
              Expr.load i32 (Arg.var p_15.fst) fun ld_2 =>
              Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_arena, Arg.var ld_1, ())) fun p_16 =>
              Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p_16.fst, Arg.imm 1, ())) fun p_17 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_17.fst, ())) fun p_18 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_18.fst, Arg.imm 4, ())) fun p_19 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_19.fst, ()))
                fun p_20 =>
              Expr.load i32 (Arg.var p_20.fst) fun ld_3 =>
              Expr.call (as := [i64, i32, i32, i32, i32]) (bs := []) "full_k6_watch_fid"
                (Arg.var c.hdr, Arg.var p.fst, Arg.var ld_2, Arg.var ld_3, Arg.var p_6.fst, ())
                fun _ : Tup Val [] => Expr.jump Js_1.fst ())
              (Expr.jump Js_1.fst ()))
            (Expr.call (as := [i64, i32]) (bs := [i64]) "full_k6_solve_fid"
              (Arg.var c.hdr, Arg.var tick_lim, ()) fun ret : Tup Val [i64] =>
            Expr.let_ (Op.mk (OpCode.cmp .ne i64 .bool rfl) (Arg.var ret.fst, Arg.imm 20, ()))
              fun p_2 =>
            Expr.jnz (Arg.var p_2.fst) (Expr.ret (Arg.imm false, ()))
              (Expr.call (as := [i64]) (bs := []) "full_k6_core_fid" (Arg.var c.hdr, ())
                fun _ : Tup Val [] =>
              Expr.group (fun Js_1 : Tup Cont [[i32]] => Blocks.cons (fun pz : Tup Val [i32] =>
                Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pz.fst, Arg.imm 128, ()))
                  fun p_3 =>
                Expr.jnz (Arg.var p_3.fst)
                  (Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 4002, Arg.var pz.fst, ()))
                    fun p_4 =>
                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_4.fst, ())) fun p_5 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_5.fst, Arg.imm 4, ())) fun p_6 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_6.fst, ()))
                    fun p_7 =>
                  Expr.store (t := i32) (Arg.imm 0) (Arg.var p_7.fst)
                    (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pz.fst, Arg.imm 1, ()))
                      fun p_8 => Expr.jump Js_1.fst (Arg.var p_8.fst, ())))
                  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4194, ())) fun p_4 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_4.fst, Arg.imm 4, ())) fun p_5 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_5.fst, ()))
                    fun p_6 =>
                  Expr.load i32 (Arg.var p_6.fst) fun onc =>
                  Expr.group (fun Js_2 : Tup Cont [[i32, Ty.bool]] =>
                    Blocks.cons (fun pc : Tup Val [i32, Ty.bool] =>
                      Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl)
                        (Arg.var pc.fst, Arg.var onc, ())) fun p_7 =>
                      Expr.jnz (Arg.var p_7.fst)
                        (Expr.group (fun _ : Tup Cont [[Ty.bool]] =>
                          Blocks.cons (fun pn : Tup Val [Ty.bool] =>
                            Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pc.fst, Arg.imm 1, ()))
                              fun p_8 => Expr.jump Js_2.fst (Arg.var p_8.fst, Arg.var pn.fst, ()))
                            Blocks.nil) fun Js_3 =>
                        Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_meta, Arg.var pc.fst, ()))
                          fun p_8 =>
                        Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_8.fst, ())) fun p_9 =>
                        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_9.fst, Arg.imm 4, ()))
                          fun p_10 =>
                        Expr.let_ (Op.mk (OpCode.add i64)
                          (Arg.var c.pScratchBuf, Arg.var p_10.fst, ())) fun p_11 =>
                        Expr.load i32 (Arg.var p_11.fst) fun cm =>
                        Expr.let_ (Op.mk (OpCode.and i32) (Arg.var cm, Arg.imm 2147483648, ()))
                          fun p_12 =>
                        Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl)
                          (Arg.var p_12.fst, Arg.imm 0, ())) fun p_13 =>
                        Expr.jnz (Arg.var p_13.fst)
                          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_aux, Arg.var pc.fst, ()))
                            fun p_14 =>
                          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_14.fst, ())) fun p_15 =>
                          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_15.fst, Arg.imm 4, ()))
                            fun p_16 =>
                          Expr.let_ (Op.mk (OpCode.add i64)
                            (Arg.var c.pScratchBuf, Arg.var p_16.fst, ())) fun p_17 =>
                          Expr.load i32 (Arg.var p_17.fst) fun raw =>
                          Expr.let_ (Op.mk (OpCode.and i32) (Arg.var raw, Arg.imm 2047, ()))
                            fun eid =>
                          Expr.group (fun _ : Tup Cont [[i32]] => Blocks.cons (fun pm =>
                            Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var eid.fst, Arg.imm 5, ()))
                              fun p_18 =>
                            Expr.let_ (Op.mk (OpCode.add i32)
                              (Arg.var pm.fst, Arg.var p_18.fst, ())) fun p_19 =>
                            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_19.fst, ()))
                              fun p_20 =>
                            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_20.fst, Arg.imm 4, ()))
                              fun p_21 =>
                            Expr.let_ (Op.mk (OpCode.add i64)
                              (Arg.var c.pScratchBuf, Arg.var p_21.fst, ())) fun p_22 =>
                            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_19.fst, ())) fun p_23 =>
                            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_23.fst, Arg.imm 4, ()))
                              fun p_24 =>
                            Expr.let_ (Op.mk (OpCode.add i64)
                              (Arg.var c.pScratchBuf, Arg.var p_24.fst, ())) fun p_25 =>
                            Expr.load i32 (Arg.var p_25.fst) fun cur =>
                            Expr.let_ (Op.mk (OpCode.and i32) (Arg.var eid.fst, Arg.imm 31, ()))
                              fun p_26 =>
                            Expr.let_ (Op.mk (OpCode.shl i32) (Arg.imm 1, Arg.var p_26.fst, ()))
                              fun p_27 =>
                            Expr.let_ (Op.mk (OpCode.or i32) (Arg.var cur, Arg.var p_27.fst, ()))
                              fun p_28 =>
                            Expr.store (Arg.var p_28.fst) (Arg.var p_22.fst)
                              (Expr.jump Js_3.fst (Arg.imm true, ()))) Blocks.nil)
                          fun Js_4 =>
                          Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var raw, Arg.imm 11, ()))
                            fun p_18 =>
                          Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                            (Arg.var p_18.fst, Arg.imm 0, ())) fun p_19 =>
                          Expr.jnz (Arg.var p_19.fst)
                            (Expr.jump Js_4.fst (Arg.imm 4002, ()))
                            (Expr.jump Js_4.fst (Arg.imm 4066, ())))
                          (Expr.jump Js_3.fst (Arg.var pc.snd.fst, ())))
                        (Expr.group (fun _ : Tup Cont [[]] =>
                          Blocks.cons (fun _ => Expr.ret (Arg.var pc.snd.fst, ())) Blocks.nil)
                          fun Js_3 =>
                        Expr.jnz (Arg.var pc.snd.fst)
                          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4130, ())) fun p_8 =>
                          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_8.fst, Arg.imm 4, ()))
                            fun p_9 =>
                          Expr.let_ (Op.mk (OpCode.add i64)
                            (Arg.var c.pScratchBuf, Arg.var p_9.fst, ())) fun p_10 =>
                          Expr.store (t := i32) (Arg.imm 1) (Arg.var p_10.fst)
                            (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4131, ())) fun p_11 =>
                            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_11.fst, Arg.imm 4, ()))
                              fun p_12 =>
                            Expr.let_ (Op.mk (OpCode.add i64)
                              (Arg.var c.pScratchBuf, Arg.var p_12.fst, ())) fun p_13 =>
                            Expr.store (t := i32) (Arg.imm 1) (Arg.var p_13.fst)
                              (Expr.jump Js_3.fst ())))
                          (Expr.jump Js_3.fst ()))) Blocks.nil)
                    fun Js_2 => Expr.jump Js_2.fst (Arg.imm 0, Arg.imm false, ())))
              Blocks.nil) fun Js_1 => Expr.jump Js_1.fst (Arg.imm 0, ())))) Blocks.nil)
        fun Js => Expr.jump Js.fst (Arg.imm 0, ()))
      m := by
  have hscr_lt := hok.length_lt
  have hnc_le := hok.nc_le
  rw [hscr4193, hscr4214] at hnc_le
  simp only [Option.getD_some] at hnc_le
  have hmv_lt2 : mv_s.toNat < 2 ^ 30 := by omega
  apply wp_loop_inv
    (Inv := fun (p : BitVec 32 × Unit) m1 => ∃ scr1 : List (BitVec 32),
      p.1.toNat ≤ nc.toNat ∧ scr1.length = scr.length ∧ FidK6BufOk scr1 ∧
      (∀ idx, idx < scr.length →
        idx < 4224 + 11 * mv_s.toNat ∨ 4224 + 29 * mv_s.toNat ≤ idx →
        scr1[idx]? = scr[idx]?) ∧
      (FullMem c (FidP6Scr s scr1) ⋆ R) m1)
    (μ := fun (p : BitVec 32 × Unit) _ => nc.toNat - p.1.toNat)
  · intro J hJ
    c0_hsteps
    exact hJ _ _ ⟨scr, Nat.zero_le _, rfl, hok, fun _ _ _ => rfl, hm⟩
  · intro J p m1 ⟨scr1, hp_le, hlen1, hok1, hag1, hm1⟩ hcont
    dsimp only [Blocks.get, Member.here]
    have hscr1_4214 : scr1[4214]? = some mv_s := by
      rw [hag1 4214 (by omega) (by left; omega), hscr4214]
    have hscr1_4193 : scr1[4193]? = some nc := by
      rw [hag1 4193 (by omega) (by left; omega), hscr4193]
    have hscr1_4194 : scr1[4194]? = some nc := by
      rw [hag1 4194 (by omega) (by left; omega), hscr4194]
    have hbase1 : 4224 + 45 * mv_s.toNat ≤ scr1.length := by
      have := hok1.base_ge
      rw [hscr1_4214] at this; simp only [Option.getD_some] at this; exact this
    c0_hsteps
    · have hp_lt : p.fst.toNat < nc.toNat := by bv_omega
      have hp1_toNat : (p.fst + 1#32).toNat = p.fst.toNat + 1 :=
        fid_k6c_add1_toNat hp_lt (by omega)
      let idx_meta := (BitVec.setWidth 64 (o_cl_meta + p.fst)).toNat
      let idx_off := (BitVec.setWidth 64 (o_cl_off + p.fst)).toNat
      have hidx_meta : idx_meta = 4224 + 33 * mv_s.toNat + p.fst.toNat := by
        dsimp only [idx_meta]; rw [hoff_meta]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
      have hidx_meta_lt : idx_meta < scr1.length := by omega
      have hidx_off : idx_off = 4224 + 29 * mv_s.toNat + p.fst.toNat := by
        dsimp only [idx_off]; rw [hoff_off]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
      have hidx_off_lt : idx_off < scr1.length := by omega
      have hscr1_4207 : scr1[4207]? = some (scr1[4207]?.getD 0#32) := by
        have hlt4207 : 4207 < scr1.length := by omega
        simp [List.getElem?_eq_getElem hlt4207]
      have hcl := hok1.clause_ok (cid := p.fst.toNat)
      rw [hscr1_4193, hscr1_4214] at hcl
      simp only [Option.getD_some] at hcl
      have hcl_p := hcl hp_lt
      have hlen_ge1 := hok1.length_ge
      rw [hscr1_4214] at hlen_ge1
      simp only [Option.getD_some] at hlen_ge1
      c0_hsteps
      · have hsz_ge2 : 2 ≤ (scr1[idx_meta] &&& 65535#32).toNat := by
          have heq : idx_meta = (o_cl_meta.toNat + p.fst.toNat) % 2 ^ 32 := by
            dsimp only [idx_meta]; bv_omega
          have hmlt2 : (o_cl_meta.toNat + p.fst.toNat) % 2 ^ 32 < scr1.length := by
            rw [← heq]; exact hidx_meta_lt
          have hel : scr1[idx_meta] = scr1[(o_cl_meta.toNat + p.fst.toNat) % 2 ^ 32] :=
            Option.some.inj (by
              rw [← List.getElem?_eq_getElem hidx_meta_lt, ← List.getElem?_eq_getElem hmlt2, heq])
          have hmod :
              (scr1[(o_cl_meta.toNat + p.fst.toNat) % 2 ^ 32] &&& 65535#32).toNat =
              scr1[(o_cl_meta.toNat + p.fst.toNat) % 2 ^ 32].toNat % 65536 := by
            rw [BitVec.toNat_and, show (65535#32).toNat = 2 ^ 16 - 1 from rfl,
              Nat.and_two_pow_sub_one_eq_mod]
          rw [hel, hmod]
          exact ‹2 ≤ scr1[(o_cl_meta.toNat + p.fst.toNat) % 2 ^ 32].toNat % 65536›
        have hoff_val : scr1[idx_off].toNat +
            (scr1[idx_meta] &&& 65535#32).toNat ≤
            (scr1[4207]?.getD 0#32).toNat := by
          have h1 := hcl_p.1
          rw [← hidx_off, List.getElem?_eq_getElem hidx_off_lt, Option.getD_some,
            ← hidx_meta, List.getElem?_eq_getElem hidx_meta_lt, Option.getD_some] at h1
          exact h1
        have hacap_le : 4224 + 45 * mv_s.toNat + (scr1[4207]?.getD 0#32).toNat ≤ scr1.length :=
          hlen_ge1
        let idx_l0 := (BitVec.setWidth 64 (o_arena + scr1[idx_off])).toNat
        let idx_l1 := (BitVec.setWidth 64 (o_arena + scr1[idx_off] + 1#32)).toNat
        have hl0_idx : idx_l0 = 4224 + 45 * mv_s.toNat + scr1[idx_off].toNat := by
          dsimp only [idx_l0]; rw [hoff_ar]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
        have hl0_lt : idx_l0 < scr1.length := by omega
        have hl1_idx : idx_l1 = 4224 + 45 * mv_s.toNat + scr1[idx_off].toNat + 1 := by
          dsimp only [idx_l1]; rw [hoff_ar]
          exact fid_k6_off_add2 hmv_hi (by omega) (by bv_omega)
        have hl1_lt : idx_l1 < scr1.length := by omega
        c0_hsteps
        fid_call hwatch
        apply fidK6WatchSpec_intro (c := c) (s := FidP6Scr s scr1) (R := R) rfl
          (fidScr_lengthsOk hinv.1 (hlen1.trans hscr_len)) hok1 hm1
        intro scr2 m2 hlen2 hag2 hm2
        have hscr2_len : scr2.length = scr.length := hlen2.trans hscr_len.symm
        have hok2 : FidK6BufOk scr2 := fid_k6c_bufOk_watch_frame (mv := mv_s.toNat) hok1
          (hlen2.trans (hlen1.trans hscr_len).symm)
          (by rw [hscr1_4214]; rfl)
          (fun idx hidx hr => hag2 idx (by omega) (by rw [hscr1_4214]; simpa using hr))
        have hag2' : ∀ idx, idx < scr.length →
            idx < 4224 + 11 * mv_s.toNat ∨ 4224 + 29 * mv_s.toNat ≤ idx →
            scr2[idx]? = scr[idx]? := by
          intro idx hidx hr
          have heq := hag2 idx (by omega) (by rw [hscr1_4214]; simpa using hr)
          exact heq.trans (hag1 idx hidx hr)
        c0_hsteps
        refine hcont _ _ (by bv_omega)
          ⟨scr2, by bv_omega, hscr2_len, hok2, hag2', fid_k6c_scrBuf_split hm2⟩
      · refine hcont _ _ (by bv_omega) ⟨scr1, by bv_omega, hlen1, hok1, hag1, hm1⟩
    · have hp_eq : p.fst.toNat = nc.toNat := by bv_omega
      fid_call hsolve
      apply fidK6SolveSpec_intro (c := c) (s := FidP6Scr s scr1) (R := R) rfl
        (fidScr_lengthsOk hinv.1 (hlen1.trans hscr_len)) hok1
        (by rw [hscr1_4194, hscr1_4193]; exact Nat.le_refl _) hm1
      intro r2 scr2 fuel2 m2; dsimp only
      intro hok2 hlen2 hag2_lt h4194 h4214 hnc2 haux2 hfuel2 hm2
      let s2 : FullState :=
        { core := { s.core with fuel := fuel2 }
          scratch := { s.scratch with scratch_buf := scr2 } }
      have hm2' : (FullMem c (FidP6Scr s2 scr2) ⋆ R) m2 := fid_k6c_scrBuf_split hm2
      have hinv2 : FullDenseInvW c F0 F_cur s2 := m8_fullDenseInvW_scr_fuel hinv hlen2 fuel2
      have hscr2_len : scr2.length = c.scratch_cap := hlen2
      have hscr2_4194 : scr2[4194]? = some nc := by rw [h4194, hscr1_4194]
      have hscr2_4214 : scr2[4214]? = some mv_s := by rw [h4214, hscr1_4214]
      have hscr2_pre0 : ∀ i, i < 4002 → scr2[i]? = scr0[i]? := fun i hi => by
        rw [hag2_lt i (by omega), hag1 i (by omega) (by left; omega), hpre0 i hi]
      have hscr2_pre1 : ∀ i, 4132 ≤ i → i < 4192 → scr2[i]? = scr0[i]? := fun i h1 h2 => by
        rw [hag2_lt i (by omega), hag1 i (by omega) (by left; omega), hpre1 i h1 h2]
      have htmk2 : TmkZero s2 := htmk
      c0_hsteps
      · exact hQ false s2 m2 hinv2 htmk2 rfl rfl rfl hfuel2 hscr2_pre0 hscr2_pre1 hm2
      · fid_call hcore
        apply fidK6CoreSpec_intro (c := c) (s := FidP6Scr s2 scr2) (R := R) rfl
          (fidScr_lengthsOk hinv2.1 hscr2_len) hok2 hm2'
        intro scr3 m3 hlen3 hag3 hok3 hm3
        have hm3' : (FullMem c (FidP6Scr s2 scr3) ⋆ R) m3 := fid_k6c_scrBuf_split hm3
        have hscr3_4194 : scr3[4194]? = some nc := by
          have := hag3 4194 (by omega) (by rw [hscr2_4214]; left; omega)
          rw [this, hscr2_4194]
        have hscr3_4214 : scr3[4214]? = some mv_s := by
          have := hag3 4214 (by omega) (by rw [hscr2_4214]; left; omega)
          rw [this, hscr2_4214]
        have hscr3_pre0 : ∀ i, i < 4002 → scr3[i]? = scr0[i]? := fun i hi => by
          have := hag3 i (by omega) (by rw [hscr2_4214]; left; omega)
          rw [this, hscr2_pre0 i hi]
        have hscr3_pre1 : ∀ i, 4132 ≤ i → i < 4192 → scr3[i]? = scr0[i]? := fun i h1 h2 => by
          have := hag3 i (by omega) (by rw [hscr2_4214]; left; omega)
          rw [this, hscr2_pre1 i h1 h2]
        have hscr3_aux : ∀ cid, cid < nc.toNat →
            scr3[4224 + 37 * mv_s.toNat + cid]? = scr[4224 + 37 * mv_s.toNat + cid]? := by
          intro cid hcid
          have hlt3 : 4224 + 37 * mv_s.toNat + cid < c.scratch_cap := by
            have := hok3.base_ge
            rw [hscr3_4214, hlen3] at this
            simp only [Option.getD_some] at this
            omega
          have h3 := hag3 (4224 + 37 * mv_s.toNat + cid) hlt3
            (by rw [hscr2_4214]; simp only [Option.getD_some]; right; right; omega)
          have h2 := haux2 cid (by rw [hscr1_4194]; exact hcid)
          rw [hscr1_4214] at h2; simp only [Option.getD_some] at h2
          rw [h3, h2, hag1 (4224 + 37 * mv_s.toNat + cid) (by omega) (by right; omega)]
        have hnc_le : nc.toNat ≤ 4 * mv_s.toNat := by
          have h4193 := hag3 4193 (by omega) (by rw [hscr2_4214]; left; omega)
          have hk3 := hok3.nc_le
          rw [hscr3_4214, h4193] at hk3; simp only [Option.getD_some] at hk3
          have h2' := hnc2; rw [hscr1_4194] at h2'; simp only [Option.getD_some] at h2'; omega
        exact fid_k6c_post_core_mask_wp hinv htmk hcap hscr_len hlen3 hmv_lo hmv_hi hnc_le
          hoff_meta hoff_aux hok3 hscr3_4194 hscr3_4214 hscr3_pre0 hscr3_pre1 hscr3_aux haux_ok
          hfuel2 hm3' hQ

/-! ## 3. Sub-phase 2: `copy_clause` (`J428` tmp -> scr arena + metadata + `J453` unit) -/

private theorem fid_k6c_csz_mask {csz : BitVec 32} (h : csz.toNat ≤ 65535) :
    (csz &&& 65535#32) = csz ∧ (csz &&& 1073741824#32) = 0#32 := by
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show (65535#32 : BitVec 32).toNat = 2 ^ 16 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    bv_omega
  · apply BitVec.eq_of_toNat_eq
    apply Nat.eq_of_testBit_eq
    intro i
    rw [BitVec.toNat_and, show (1073741824#32 : BitVec 32).toNat = 2 ^ 30 from rfl,
      Nat.testBit_and, Nat.testBit_two_pow, BitVec.toNat_zero, Nat.zero_testBit]
    by_cases h30 : i = 30
    · subst h30; simp [Nat.testBit_lt_two_pow (by omega : csz.toNat < 2 ^ 30)]
    · simp [Ne.symm h30]

/-- Copy `tmp[0..csz)` into scratch arena and record clause metadata + optional unit index. -/
theorem fid_k6c_copy_clause_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {K_next : Cont [i32, i32, i32, i32, Ty.bool, i32]}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk scr : List (BitVec 32)}
    {mv_s o_cl_off o_cl_meta o_cl_aux o_units o_arena : BitVec 32}
    {nc alen n_units csz trivial_eid eid : BitVec 32} {abort_in : Bool} {acap_n : Nat}
    (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (hcap : 4224 + 45 * mv_s.toNat + acap_n ≤ c.scratch_cap)
    (hscr_lt : scr.length < 2 ^ 30) (hscr_len : scr.length = c.scratch_cap)
    (htmp_len : tmp.length = c.max_vars)
    (hoff_off : o_cl_off = 4224#32 + 29#32 * mv_s)
    (hoff_meta : o_cl_meta = 4224#32 + 33#32 * mv_s)
    (hoff_aux : o_cl_aux = 4224#32 + 37#32 * mv_s)
    (hoff_units : o_units = 4224#32 + 41#32 * mv_s)
    (hoff_ar : o_arena = 4224#32 + 45#32 * mv_s)
    (hcsz_pos : 1 ≤ csz.toNat) (hcsz_max : csz.toNat ≤ c.max_vars) (hcsz_65k : csz.toNat ≤ 65535)
    (hnc_lt : nc.toNat < 2 * mv_s.toNat) (hn_units : n_units.toNat ≤ nc.toNat)
    (halen_le : alen.toNat + csz.toNat ≤ acap_n)
    (heid : eid.toNat < 4096 ∧ (eid &&& 2047#32).toNat < 2001)
    (hcls : FidK6cClsOk mv_s.toNat nc.toNat alen.toNat n_units.toNat scr)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m)
    (hK : ∀ (scr' : List (BitVec 32)) (pu k_out : BitVec 32) (m' : Mem 64),
      scr'.length = c.scratch_cap → (∀ i, i < 4224 + 29 * mv_s.toNat → scr'[i]? = scr[i]?) →
      FidK6cClsOk mv_s.toNat (nc + 1#32).toNat (alen + csz).toNat pu.toNat scr' →
      pu.toNat = (if csz = 1#32 then n_units.toNat + 1 else n_units.toNat) →
      (FullMem c (FidP6Work s tmp wsort tmk scr') ⋆ R) m' →
      K_next (nc + 1#32, alen + csz, pu, trivial_eid, abort_in, k_out, ()) m') :
    wp Γ Q X
      (Expr.group (fun Js : Tup Cont [[i32]] => Blocks.cons (fun p : Tup Val [i32] =>
        Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var p.fst, Arg.var csz, ()))
          fun p_1 =>
        Expr.jnz (Arg.var p_1.fst)
          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_arena, Arg.var alen, ())) fun p_2 =>
          Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p_2.fst, Arg.var p.fst, ())) fun p_3 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_3.fst, ())) fun p_4 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_4.fst, Arg.imm 4, ())) fun p_5 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_5.fst, ()))
            fun p_6 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.fst, ())) fun p_7 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_7.fst, Arg.imm 4, ())) fun p_8 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTmp, Arg.var p_8.fst, ())) fun p_9 =>
          Expr.load i32 (Arg.var p_9.fst) fun ld =>
          Expr.store (Arg.var ld) (Arg.var p_6.fst)
            (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p.fst, Arg.imm 1, ())) fun p_10 =>
            Expr.jump Js.fst (Arg.var p_10.fst, ())))
          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_off, Arg.var nc, ())) fun p_2 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_2.fst, ())) fun p_3 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_3.fst, Arg.imm 4, ())) fun p_4 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_4.fst, ()))
            fun p_5 =>
          Expr.store (t := i32) (Arg.var alen) (Arg.var p_5.fst)
            (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_meta, Arg.var nc, ())) fun p_6 =>
            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_6.fst, ())) fun p_7 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_7.fst, Arg.imm 4, ())) fun p_8 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_8.fst, ()))
              fun p_9 =>
            Expr.store (t := i32) (Arg.var csz) (Arg.var p_9.fst)
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_aux, Arg.var nc, ())) fun p_10 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_10.fst, ())) fun p_11 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_11.fst, Arg.imm 4, ())) fun p_12 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_12.fst, ()))
                fun p_13 =>
              Expr.store (t := i32) (Arg.var eid) (Arg.var p_13.fst)
                (Expr.group (fun _Js_1 : Tup Cont [[i32]] => Blocks.cons (fun pu : Tup Val [i32] =>
                  Expr.let_ (Op.mk (OpCode.add i32) (Arg.var nc, Arg.imm 1, ())) fun p_14 =>
                  Expr.let_ (Op.mk (OpCode.add i32) (Arg.var alen, Arg.var csz, ())) fun p_15 =>
                  Expr.jump K_next (Arg.var p_14.fst, Arg.var p_15.fst, Arg.var pu.fst,
                    Arg.var trivial_eid, Arg.var abort_in, Arg.var p.fst, ())) Blocks.nil)
                  fun Js_1 =>
                Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var csz, Arg.imm 1, ()))
                  fun p_14 =>
                Expr.jnz (Arg.var p_14.fst)
                  (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_units, Arg.var n_units, ()))
                    fun p_15 =>
                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_15.fst, ())) fun p_16 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_16.fst, Arg.imm 4, ())) fun p_17 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_17.fst, ()))
                    fun p_18 =>
                  Expr.store (t := i32) (Arg.var nc) (Arg.var p_18.fst)
                    (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var n_units, Arg.imm 1, ()))
                      fun p_19 =>
                    Expr.jump Js_1.fst (Arg.var p_19.fst, ())))
                  (Expr.jump Js_1.fst (Arg.var n_units, ()))))))) Blocks.nil)
      fun Js => Expr.jump Js.fst (Arg.imm 0, ())) m := by
  have hc65 := fid_k6c_csz_mask hcsz_65k
  have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := fid_k6c_add1_toNat hnc_lt (by omega)
  have hal1 : (alen + csz).toNat = alen.toNat + csz.toNat := by bv_omega
  apply wp_loop_inv
    (Inv := fun (p : BitVec 32 × Unit) m1 => ∃ scr1 : List (BitVec 32),
      p.1.toNat ≤ csz.toNat ∧ scr1.length = c.scratch_cap ∧
      (∀ i, i < 4224 + 29 * mv_s.toNat → scr1[i]? = scr[i]?) ∧
      FidK6cClsOk mv_s.toNat nc.toNat alen.toNat n_units.toNat scr1 ∧
      (FullMem c (FidP6Work s tmp wsort tmk scr1) ⋆ R) m1)
    (μ := fun (p : BitVec 32 × Unit) _ => csz.toNat - p.1.toNat)
  · intro J hJ; c0_hsteps; exact hJ _ _ ⟨scr, Nat.zero_le _, hscr_len, fun _ _ => rfl, hcls, hm⟩
  · intro J p m1 ⟨scr1, hp_le, hlen1, hag1, hc1, hm1⟩ hcont
    dsimp only [Blocks.get, Member.here]
    c0_hsteps
    · have hp_lt : p.fst.toNat < csz.toNat := by bv_omega
      have htm : (BitVec.setWidth 64 p.fst).toNat < tmp.length := by bv_omega
      have hsc : (BitVec.setWidth 64 (o_arena + alen + p.fst)).toNat < scr1.length := by
        have : (BitVec.setWidth 64 (o_arena + alen + p.fst)).toNat =
            4224 + 45 * mv_s.toNat + alen.toNat + p.fst.toNat := by
          rw [hoff_ar]; exact fid_k6_off_add2 hmv_hi (by omega) (by bv_omega)
        omega
      c0_hsteps
      try rw [show (BitVec.setWidth 64 (o_arena + alen + p.fst)).toNat =
          4224 + 45 * mv_s.toNat + alen.toNat + p.fst.toNat by
          rw [hoff_ar]; exact fid_k6_off_add2 hmv_hi (by omega) (by bv_omega)] at hm
      have hp1 : (p.fst + 1#32).toNat = p.fst.toNat + 1 := fid_k6c_add1_toNat hp_lt (by omega)
      refine hcont _ _ (by dsimp only; bv_omega)
        ⟨_, by dsimp only; bv_omega, by simp [hlen1], ?_, ?_, hm⟩
      · intro i hi; rw [List.getElem?_set_ne (by omega)]; exact hag1 i hi
      · exact fid_k6c_clsOk_frame hc1 fun idx h1 _ => List.getElem?_set_ne (by omega)
    · have hp_eq : p.fst.toNat = csz.toNat := by bv_omega
      have hof : (BitVec.setWidth 64 (o_cl_off + nc)).toNat =
          4224 + 29 * mv_s.toNat + nc.toNat := by
        rw [hoff_off]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
      have hmt : (BitVec.setWidth 64 (o_cl_meta + nc)).toNat =
          4224 + 33 * mv_s.toNat + nc.toNat := by
        rw [hoff_meta]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
      have hax : (BitVec.setWidth 64 (o_cl_aux + nc)).toNat =
          4224 + 37 * mv_s.toNat + nc.toNat := by
        rw [hoff_aux]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
      have hlt_of : (BitVec.setWidth 64 (o_cl_off + nc)).toNat < scr1.length := by omega
      have hlt_mt : (BitVec.setWidth 64 (o_cl_meta + nc)).toNat <
          (scr1.set (BitVec.setWidth 64 (o_cl_off + nc)).toNat alen).length := by
        simp only [List.length_set, hlen1]; omega
      have hlt_ax : (BitVec.setWidth 64 (o_cl_aux + nc)).toNat <
          ((scr1.set (BitVec.setWidth 64 (o_cl_off + nc)).toNat alen).set
            (BitVec.setWidth 64 (o_cl_meta + nc)).toNat csz).length := by
        simp only [List.length_set, hlen1]; omega
      c0_hsteps_nogrp
      let scr2 := ((scr1.set (BitVec.setWidth 64 (o_cl_off + nc)).toNat alen).set
        (BitVec.setWidth 64 (o_cl_meta + nc)).toNat csz).set
        (BitVec.setWidth 64 (o_cl_aux + nc)).toNat eid
      have hlen2 : scr2.length = c.scratch_cap := by simp only [scr2, List.length_set, hlen1]
      have hcls2_fn : ∀ sc : List (BitVec 32), sc[4224 + 29 * mv_s.toNat + nc.toNat]? = some alen →
          sc[4224 + 33 * mv_s.toNat + nc.toNat]? = some csz →
          sc[4224 + 37 * mv_s.toNat + nc.toNat]? = some eid →
          (∀ cid, cid < nc.toNat →
            sc[4224 + 29 * mv_s.toNat + cid]? = scr1[4224 + 29 * mv_s.toNat + cid]? ∧
            sc[4224 + 33 * mv_s.toNat + cid]? = scr1[4224 + 33 * mv_s.toNat + cid]? ∧
            sc[4224 + 37 * mv_s.toNat + cid]? = scr1[4224 + 37 * mv_s.toNat + cid]?) →
          ∀ nu' : BitVec 32, nu'.toNat ≤ (nc + 1#32).toNat →
          FidK6cClsOk mv_s.toNat (nc + 1#32).toNat (alen + csz).toNat nu'.toNat sc := by
        intro sc ha hm_ hx hpre nu' hnu'
        rw [hnc1] at hnu'
        dsimp only [FidK6cClsOk]; rw [hnc1, hal1]; refine ⟨by omega, ?_, hnu'⟩
        intro cid hcid; by_cases hclt : cid < nc.toNat
        · have hc := hc1.2.1 cid hclt
          rw [(hpre cid hclt).1, (hpre cid hclt).2.1, (hpre cid hclt).2.2]
          exact ⟨by omega, hc.2.1, hc.2.2⟩
        · have hceq : cid = nc.toNat := by omega
          subst hceq; rw [ha, hm_, hx]; simp only [Option.getD_some, hc65.1, hc65.2]
          exact ⟨Nat.le_refl _, trivial, heid⟩
      apply wp_unroll_group
      intro Js_1 hJs_1
      c0_hsteps
      · have hcsz1 : csz = 1#32 := hc
        have hun : (BitVec.setWidth 64 (o_units + n_units)).toNat =
            4224 + 41 * mv_s.toNat + n_units.toNat := by
          rw [hoff_units]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
        have hlt_un : (BitVec.setWidth 64 (o_units + n_units)).toNat < scr2.length := by omega
        c0_hsteps
        have hnu1 : (n_units + 1#32).toNat = n_units.toNat + 1 :=
          fid_k6c_add1_toNat (by omega : n_units.toNat < 2 * mv_s.toNat) (by omega)
        let scr3 := scr2.set (BitVec.setWidth 64 (o_units + n_units)).toNat nc
        have hcls3 : FidK6cClsOk mv_s.toNat (nc + 1#32).toNat (alen + csz).toNat
            (n_units + 1#32).toNat scr3 := by
          refine hcls2_fn scr3 ?_ ?_ ?_ ?_ (n_units + 1#32) (by omega)
          · dsimp only [scr3, scr2]; (repeat rw [List.getElem?_set_ne (by omega)])
            rw [← hof]; exact List.getElem?_set_self hlt_of
          · dsimp only [scr3, scr2]; (repeat rw [List.getElem?_set_ne (by omega)])
            rw [← hmt]; exact List.getElem?_set_self hlt_mt
          · dsimp only [scr3, scr2]; rw [List.getElem?_set_ne (by omega), ← hax]
            exact List.getElem?_set_self hlt_ax
          · intro cid hlt; dsimp only [scr3, scr2]
            refine ⟨by (repeat rw [List.getElem?_set_ne (by omega)]),
              by (repeat rw [List.getElem?_set_ne (by omega)]),
              by (repeat rw [List.getElem?_set_ne (by omega)])⟩
        try (apply hJs_1; dsimp only [Blocks.get, Member.here]; c0_hsteps)
        simpa only [show (1 : BitVec 32) = 1#32 from rfl] using
          hK scr3 (n_units + 1#32) p.fst _ (by simp only [scr3, List.length_set, hlen2])
            (fun i hi => by
              dsimp only [scr3, scr2]; (repeat rw [List.getElem?_set_ne (by omega)])
              exact hag1 i hi)
            hcls3 (by rw [hnu1, hcsz1]; simp) hm
      · have hne : csz ≠ 1#32 := hc
        have hcls2 : FidK6cClsOk mv_s.toNat (nc + 1#32).toNat (alen + csz).toNat n_units.toNat
            scr2 := by
          refine hcls2_fn scr2 ?_ ?_ ?_ ?_ n_units (by omega)
          · dsimp only [scr2]; (repeat rw [List.getElem?_set_ne (by omega)])
            rw [← hof]; exact List.getElem?_set_self hlt_of
          · dsimp only [scr2]; rw [List.getElem?_set_ne (by omega), ← hmt]
            exact List.getElem?_set_self hlt_mt
          · dsimp only [scr2]; rw [← hax]; exact List.getElem?_set_self hlt_ax
          · intro cid hlt; dsimp only [scr2]
            exact ⟨by (repeat rw [List.getElem?_set_ne (by omega)]),
              by (repeat rw [List.getElem?_set_ne (by omega)]),
              by (repeat rw [List.getElem?_set_ne (by omega)])⟩
        try (apply hJs_1; dsimp only [Blocks.get, Member.here]; c0_hsteps)
        simpa only [show (1 : BitVec 32) = 1#32 from rfl] using hK scr2 n_units p.fst _ hlen2
          (fun i hi => by
            dsimp only [scr2]; (repeat rw [List.getElem?_set_ne (by omega)]); exact hag1 i hi)
          hcls2 (by simp [hne]) hm
/-! ## 4. Sub-phase 3: `scan_large` (`J463` arena lits loop into `wsort`/`tarjan_mark`/`tmp`) -/

private theorem fid_getElem_congr {α : Type} {xs : List α} {i j : Nat} (h : i = j)
    (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by subst h; rfl

private theorem fid_k6c_zext64 {x : BitVec 32} : (BitVec.setWidth 64 x).toNat = x.toNat := by
  bv_omega

private theorem fid_k6c_tmkReg_congr {nv1 nv2 cv : Nat} {e1 e2 t1 t2 : List (BitVec 32)}
    (h : FidK6cTmkReg nv1 cv e1 t1) (hn : nv1 = nv2) (he : e1 = e2) (ht : t1 = t2) :
    FidK6cTmkReg nv2 cv e2 t2 := by subst hn he ht; exact h

/-- Scan all literals of large clause `w`, building `tmp[0..csz)` or aborting/skipping sat. -/
theorem fid_k6c_scan_large_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {Js_ret : Cont [i32, Ty.bool, Ty.bool, i32, i32]}
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)}
    {w lsz lit_cur nv mv_s max_csz : BitVec 32} {abort_in : Bool}
    (hinv : FullDenseInvW c F0 F_cur s) (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (hmax_csz : max_csz.toNat ≤ c.max_vars ∧ max_csz.toNat ≤ 65535)
    (htmp : tmp.length = c.max_vars) (hwsort : wsort.length = 2 * c.max_vars)
    (htmk : tmk.length = 2 * c.max_vars) (hscr : scr.length = c.scratch_cap)
    (hnv_le : nv.toNat ≤ mv_s.toNat) (hnv_cv : nv.toNat ≤ 2 * s.core.cur_vars)
    (hreg : FidK6cTmkReg nv.toNat s.core.cur_vars wsort tmk)
    (hlb : w.toNat + 3 ≤ s.core.arena_len ∧ 3 ≤ fullArenaClauseSizeCore s.core w.toNat ∧
      w.toNat + 3 + fullArenaClauseSizeCore s.core w.toNat ≤ s.core.arena_len ∧
      s.core.arena_len ≤ c.arena_cap ∧ (∀ k, k < fullArenaClauseSizeCore s.core w.toNat →
        w.toNat + 3 + k < s.core.arena.length ∧
        (s.core.arena[w.toNat + 3 + k]?.getD 0#32).toNat < 2 * s.core.cur_vars))
    (hlsz : lsz.toNat = fullArenaClauseSizeCore s.core w.toNat)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m)
    (hRet : ∀ nv' ab' sat' csz' j' tmp' wsort' tmk', tmp'.length = c.max_vars →
      wsort'.length = 2 * c.max_vars → tmk'.length = 2 * c.max_vars → nv'.toNat ≤ mv_s.toNat →
      nv'.toNat ≤ 2 * s.core.cur_vars → csz'.toNat ≤ max_csz.toNat →
      FidK6cTmkReg nv'.toNat s.core.cur_vars wsort' tmk' →
      ∀ m', (FullMem c (FidP6Work s tmp' wsort' tmk' scr) ⋆ R) m' →
      Js_ret (nv', ab', sat', csz', j', ()) m') :
    wp Γ Q X
      (Expr.group (fun Js : Tup Cont [[i32, i32, i32]] =>
        Blocks.cons (fun pl : Tup Val [i32, i32, i32] =>
        Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pl.snd.snd.fst, Arg.var lsz, ()))
          fun p_1 =>
        Expr.jnz (Arg.var p_1.fst)
          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var w, ())) fun p_2 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_2.fst, Arg.imm 3, ())) fun p_3 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pl.snd.snd.fst, ())) fun p_4 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_3.fst, Arg.var p_4.fst, ())) fun p_5 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_5.fst, Arg.imm 4, ())) fun p_6 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pArena, Arg.var p_6.fst, ())) fun p_7 =>
          Expr.load i32 (Arg.var p_7.fst) fun ld =>
          Expr.group (fun _ : Tup Cont [[i32, Ty.bool, Ty.bool, i32]] => Blocks.cons (fun p_8 =>
            Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pl.snd.snd.fst, Arg.imm 1, ())) fun p_9 =>
            Expr.jump Js.fst (Arg.var p_8.fst, Arg.var p_8.snd.snd.snd.fst, Arg.var p_9.fst, ()))
            Blocks.nil) fun Js_1 =>
            Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl) (Arg.var ld, Arg.var lit_cur, ()))
              fun p_8 =>
            Expr.jnz (Arg.var p_8.fst)
              (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld, ())) fun p_9 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pVals, Arg.var p_9.fst, ())) fun p_10 =>
              Expr.load i8 (Arg.var p_10.fst) fun ld_1 =>
              Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p_11 =>
              Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld_1, ())) fun p_12 =>
              Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p_11.fst, ())) fun p_13 =>
              Expr.let_ (Op.mk (OpCode.cmp .sgt i32 .bool rfl)
                (Arg.var p_12.fst, Arg.var p_13.fst, ())) fun p_14 =>
              Expr.jnz (Arg.var p_14.fst)
                (Expr.jump Js_ret (Arg.var pl.fst, Arg.var abort_in, Arg.imm true,
                  Arg.var pl.snd.fst, Arg.var pl.snd.snd.fst, ()))
                (Expr.group (fun _ : Tup Cont [[i32, Ty.bool, i32]] => Blocks.cons (fun p_15 =>
                  Expr.jump Js_1.fst (Arg.var p_15.fst, Arg.var p_15.snd.fst, Arg.imm false,
                    Arg.var p_15.snd.snd.fst, ())) Blocks.nil) fun Js_2 =>
                  Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p_15 =>
                  Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld_1, ())) fun p_16 =>
                  Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p_15.fst, ())) fun p_17 =>
                  Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                    (Arg.var p_16.fst, Arg.var p_17.fst, ())) fun p_18 =>
                  Expr.jnz (Arg.var p_18.fst)
                    (Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var ld, Arg.imm 1, ())) fun p_19 =>
                    Expr.group (fun _ : Tup Cont [[i32, Ty.bool]] =>
                      Blocks.cons (fun p_20 : Tup Val [i32, Ty.bool] =>
                      Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl)
                        (Arg.var pl.snd.fst, Arg.var max_csz, ())) fun p_21 =>
                      Expr.jnz (Arg.var p_21.fst)
                        (Expr.jump Js_ret (Arg.var p_20.fst, Arg.imm true, Arg.imm false,
                          Arg.var pl.snd.fst, Arg.var pl.snd.snd.fst, ()))
                        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pl.snd.fst, ())) fun p_22 =>
                        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_22.fst, Arg.imm 4, ()))
                          fun p_23 =>
                        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTmp, Arg.var p_23.fst, ()))
                          fun p_24 =>
                        Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_19.fst, ())) fun p_25 =>
                        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_25.fst, Arg.imm 4, ()))
                          fun p_26 =>
                        Expr.let_ (Op.mk (OpCode.add i64)
                          (Arg.var c.pTarjanMark, Arg.var p_26.fst, ())) fun p_27 =>
                        Expr.load i32 (Arg.var p_27.fst) fun ld_2 =>
                        Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var ld_2, Arg.imm 1, ())) fun p_28 =>
                        Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var p_28.fst, Arg.imm 1, ()))
                          fun p_29 =>
                        Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld, Arg.imm 1, ())) fun p_30 =>
                        Expr.let_ (Op.mk (OpCode.or i32) (Arg.var p_29.fst, Arg.var p_30.fst, ()))
                          fun p_31 =>
                        Expr.store (Arg.var p_31.fst) (Arg.var p_24.fst)
                          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pl.snd.fst, Arg.imm 1, ()))
                            fun p_32 =>
                          Expr.jump Js_2.fst (Arg.var p_20.fst, Arg.var p_20.snd.fst,
                            Arg.var p_32.fst, ())))) Blocks.nil)
                      fun Js_3 =>
                      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_19.fst, ())) fun p_20 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_20.fst, Arg.imm 4, ()))
                        fun p_21 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pTarjanMark, Arg.var p_21.fst, ())) fun p_22 =>
                      Expr.load i32 (Arg.var p_22.fst) fun ld_2 =>
                      Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var ld_2, Arg.imm 0, ()))
                        fun p_23 =>
                      Expr.jnz (Arg.var p_23.fst)
                        (Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl)
                          (Arg.var pl.fst, Arg.var mv_s, ())) fun p_24 =>
                        Expr.jnz (Arg.var p_24.fst)
                          (Expr.jump Js_ret (Arg.var pl.fst, Arg.imm true, Arg.imm false,
                            Arg.var pl.snd.fst, Arg.var pl.snd.snd.fst, ()))
                          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pl.fst, ())) fun p_25 =>
                          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 776, ()))
                            fun p_26 =>
                          Expr.load i64 (Arg.var p_26.fst) fun ld_3 =>
                          Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 1, ())) fun p_27 =>
                          Expr.let_ (Op.mk (OpCode.shl i64) (Arg.var ld_3, Arg.var p_27.fst, ()))
                            fun p_28 =>
                          Expr.let_ (Op.mk (OpCode.cmp .uge i64 .bool rfl)
                            (Arg.var p_25.fst, Arg.var p_28.fst, ())) fun p_29 =>
                          Expr.jnz (Arg.var p_29.fst)
                            (Expr.jump Js_ret (Arg.var pl.fst, Arg.imm true, Arg.imm false,
                              Arg.var pl.snd.fst, Arg.var pl.snd.snd.fst, ()))
                            (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pl.fst, ())) fun p_30 =>
                            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_30.fst, Arg.imm 4, ()))
                              fun p_31 =>
                            Expr.let_ (Op.mk (OpCode.add i64)
                              (Arg.var c.pWsort, Arg.var p_31.fst, ())) fun p_32 =>
                            Expr.store (Arg.var p_19.fst) (Arg.var p_32.fst)
                              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pl.fst, Arg.imm 1, ()))
                                fun p_33 =>
                              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_19.fst, ()))
                                fun p_34 =>
                              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_34.fst, Arg.imm 4, ()))
                                fun p_35 =>
                              Expr.let_ (Op.mk (OpCode.add i64)
                                (Arg.var c.pTarjanMark, Arg.var p_35.fst, ())) fun p_36 =>
                              Expr.store (Arg.var p_33.fst) (Arg.var p_36.fst)
                                (Expr.jump Js_3.fst (Arg.var p_33.fst, Arg.var abort_in, ()))))))
                        (Expr.jump Js_3.fst (Arg.var pl.fst, Arg.var abort_in, ())))
                    (Expr.jump Js_2.fst (Arg.var pl.fst, Arg.var abort_in,
                      Arg.var pl.snd.fst, ()))))
              (Expr.jump Js_1.fst (Arg.var pl.fst, Arg.var abort_in, Arg.imm false,
                Arg.var pl.snd.fst, ())))
          (Expr.jump Js_ret (Arg.var pl.fst, Arg.var abort_in, Arg.imm false,
            Arg.var pl.snd.fst, Arg.var pl.snd.snd.fst, ()))) Blocks.nil)
      fun Js => Expr.jump Js.fst (Arg.var nv, Arg.imm 0, Arg.imm 0, ())) m := by
  have har_len : s.core.arena_len ≤ c.arena_cap := hlb.2.2.2.1
  have har_arr : s.core.arena.length = c.arena_cap := hinv.1.core_ok.arena_len_arr
  have hcv_mv : s.core.cur_vars ≤ c.max_vars := hinv.1.core_ok.cur_vars_le
  have hvals_len : s.core.vals.length = 2 * c.max_vars := hinv.1.core_ok.vals_len
  have hcv_lt : 2 * s.core.cur_vars < 2 ^ 30 := by
    have := c.hmaxv; simp only [dimacsBound] at this; omega
  have hscr_lt : scr.length < 2 ^ 30 := by
    have := c.hscr; simp only [dimacsBound] at this; omega
  apply wp_loop_inv
    (Inv := fun (pl : Tup Val [i32, i32, i32]) m1 => ∃ tmp1 wsort1 tmk1,
      pl.2.2.1.toNat ≤ lsz.toNat ∧ pl.1.toNat ≤ mv_s.toNat ∧
      pl.1.toNat ≤ 2 * s.core.cur_vars ∧ pl.2.1.toNat ≤ max_csz.toNat ∧
      tmp1.length = c.max_vars ∧ wsort1.length = 2 * c.max_vars ∧ tmk1.length = 2 * c.max_vars ∧
      FidK6cTmkReg pl.1.toNat s.core.cur_vars wsort1 tmk1 ∧
      (FullMem c (FidP6Work s tmp1 wsort1 tmk1 scr) ⋆ R) m1)
    (μ := fun (pl : Tup Val [i32, i32, i32]) _ => lsz.toNat - pl.2.2.1.toNat)
  · intro J hJ; c0_hsteps; exact hJ _ _ ⟨tmp, wsort, tmk, Nat.zero_le _, hnv_le, hnv_cv,
      Nat.zero_le _, htmp, hwsort, htmk, hreg, hm⟩
  · intro J pl m1 ⟨tmp1, wsort1, tmk1, hj_le, hnv1, hnvcv1, hcsz1, htp1, hws1, htm1, hr1, hm1⟩
      hcont
    dsimp only [Blocks.get, Member.here]
    c0_hsteps_nogrp
    · have hj_lt : pl.2.2.1.toNat < lsz.toNat := by bv_omega
      have hl_ar := hlb.2.2.2.2 pl.2.2.1.toNat (by omega)
      have hw_sum : (BitVec.setWidth 64 w + 3#64 + BitVec.setWidth 64 pl.2.2.1).toNat =
          w.toNat + 3 + pl.2.2.1.toNat := by
        have hw0 : w.toNat < 2 ^ 64 := Nat.lt_trans (BitVec.isLt w) (by decide)
        have hj0 : pl.2.2.1.toNat < 2 ^ 64 := Nat.lt_trans (BitVec.isLt _) (by decide)
        simp only [BitVec.toNat_add, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hw0,
          Nat.mod_eq_of_lt hj0, show (3#64 : BitVec 64).toNat = 3 from rfl]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have har_idx_lt : (BitVec.setWidth 64 w + 3#64 + BitVec.setWidth 64 pl.2.2.1).toNat <
          s.core.arena.length := by rw [hw_sum]; exact hl_ar.1
      have hlit_lt : (s.core.arena[(BitVec.setWidth 64 w + 3#64 +
          BitVec.setWidth 64 pl.2.2.1).toNat]'har_idx_lt).toNat < 2 * s.core.cur_vars := by
        have hget := hl_ar.2
        have hg2 : s.core.arena[w.toNat + 3 + pl.2.2.1.toNat]? =
            some (s.core.arena[(BitVec.setWidth 64 w + 3#64 +
              BitVec.setWidth 64 pl.2.2.1).toNat]'har_idx_lt) := by
          rw [← hw_sum]; exact List.getElem?_eq_getElem har_idx_lt
        simpa [hg2] using hget
      have hhj1 : (pl.2.2.1 + 1#32).toNat = pl.2.2.1.toNat + 1 :=
        fid_k6c_add1_toNat hj_lt (by omega)
      apply wp_unroll_group
      intro Js_1 hJs_1
      have hJ1 : ∀ nv' ab' csz' tmp' wsort' tmk' m',
          tmp'.length = c.max_vars → wsort'.length = 2 * c.max_vars → tmk'.length = 2 * c.max_vars →
          nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ 2 * s.core.cur_vars → csz'.toNat ≤ max_csz.toNat →
          FidK6cTmkReg nv'.toNat s.core.cur_vars wsort' tmk' →
          (FullMem c (FidP6Work s tmp' wsort' tmk' scr) ⋆ R) m' →
          Js_1 (nv', ab', false, csz', ()) m' := by
        intro nv' ab' csz' tmp' wsort' tmk' m' ht' hw' hm' h1 h2 h3 hr' hmm
        apply hJs_1; try dsimp only [Blocks.get, Member.here]
        c0_hsteps
        exact hcont (nv', csz', pl.2.2.1 + 1#32, ()) m' (by dsimp only; omega)
          ⟨tmp', wsort', tmk', by dsimp only; omega, h1, h2, h3, ht', hw', hm', hr', hmm⟩
      clear hJs_1
      have hval_lt : (BitVec.setWidth 64 (s.core.arena[(BitVec.setWidth 64 w + 3#64 +
            BitVec.setWidth 64 pl.2.2.1).toNat]'har_idx_lt)).toNat < s.core.vals.length := by
        rw [fid_k6c_zext64]; omega
      c0_hsteps_nogrp
      · exact hRet pl.fst abort_in true pl.snd.fst pl.snd.snd.fst tmp1 wsort1 tmk1
          htp1 hws1 htm1 hnv1 hnvcv1 hcsz1 hr1 m1 hm1
      · apply wp_unroll_group
        intro Js_2 hJs_2
        have hJ2 : ∀ nv' ab' csz' tmp' wsort' tmk' m',
            tmp'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
            tmk'.length = 2 * c.max_vars →
            nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ 2 * s.core.cur_vars →
            csz'.toNat ≤ max_csz.toNat → FidK6cTmkReg nv'.toNat s.core.cur_vars wsort' tmk' →
            (FullMem c (FidP6Work s tmp' wsort' tmk' scr) ⋆ R) m' →
            Js_2 (nv', ab', csz', ()) m' := by
          intro nv' ab' csz' tmp' wsort' tmk' m' ht' hw' hm' h1 h2 h3 hr' hmm
          apply hJs_2; try dsimp only [Blocks.get, Member.here]
          exact hJ1 nv' ab' csz' tmp' wsort' tmk' m' ht' hw' hm' h1 h2 h3 hr' hmm
        clear hJs_2
        c0_hsteps_nogrp
        · have hv_lt : ((s.core.arena[(BitVec.setWidth 64 w + 3#64 +
              BitVec.setWidth 64 pl.2.2.1).toNat]'har_idx_lt) >>> 1).toNat <
              s.core.cur_vars := by
            rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
          have htmk_lt : (BitVec.setWidth 64 ((s.core.arena[(BitVec.setWidth 64 w + 3#64 +
              BitVec.setWidth 64 pl.2.2.1).toNat]'har_idx_lt) >>> 1)).toNat < tmk1.length := by
            rw [fid_k6c_zext64]; omega
          apply wp_unroll_group
          intro Js_3 hJs_3
          have hJ3 : ∀ nv' ab' wsort' tmk' m',
              wsort'.length = 2 * c.max_vars → tmk'.length = 2 * c.max_vars →
              nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ 2 * s.core.cur_vars →
              FidK6cTmkReg nv'.toNat s.core.cur_vars wsort' tmk' →
              (FullMem c (FidP6Work s tmp1 wsort' tmk' scr) ⋆ R) m' →
              Js_3 (nv', ab', ()) m' := by
            intro nv' ab' wsort' tmk' m' hw' hm' h1 h2 hr' hmm
            apply hJs_3; try dsimp only [Blocks.get, Member.here]
            c0_hsteps_nogrp
            · exact hRet nv' true false pl.snd.fst pl.snd.snd.fst tmp1 wsort' tmk'
                htp1 hw' hm' h1 h2 hcsz1 hr' m' hmm
            · have hcsz_lt : pl.snd.fst.toNat < max_csz.toNat := by bv_omega
              have htp_lt : (BitVec.setWidth 64 pl.snd.fst).toNat < tmp1.length := by
                rw [fid_k6c_zext64]; omega
              have htmk_lt' : (BitVec.setWidth 64 ((s.core.arena[(BitVec.setWidth 64 w + 3#64 +
                  BitVec.setWidth 64 pl.2.2.1).toNat]'har_idx_lt) >>> 1)).toNat <
                  tmk'.length := by
                rw [fid_k6c_zext64]; omega
              c0_hsteps
              exact hJ2 nv' ab' (pl.snd.fst + 1#32) _ wsort' tmk' _
                (by simp [htp1]) hw' hm' h1 h2 (by bv_omega) hr' hm
          clear hJs_3
          c0_hsteps
          · exact hRet pl.fst true false pl.snd.fst pl.snd.snd.fst tmp1 wsort1 tmk1
              htp1 hws1 htm1 hnv1 hnvcv1 hcsz1 hr1 m1 hm1
          · exact hRet pl.fst true false pl.snd.fst pl.snd.snd.fst tmp1 wsort1 tmk1
              htp1 hws1 htm1 hnv1 hnvcv1 hcsz1 hr1 m1 hm1
          · have hnv_lt_mv : pl.fst.toNat < mv_s.toNat := by bv_omega
            have hnv_lt_cv : pl.fst.toNat < 2 * s.core.cur_vars := by
              have hc' := hc
              rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc'
              exact Nat.lt_of_not_le hc'
            have hws_lt : (BitVec.setWidth 64 pl.fst).toNat < wsort1.length := by
              rw [fid_k6c_zext64]; omega
            have htmk_lt1 : ((s.core.arena[(BitVec.setWidth 64 w + 3#64 +
                BitVec.setWidth 64 pl.2.2.1).toNat]'har_idx_lt) >>> 1).toNat < tmk1.length := by
              rw [← fid_k6c_zext64]; exact htmk_lt
            have ht0 : tmk1[(s.core.arena[(BitVec.setWidth 64 w + 3#64 +
                BitVec.setWidth 64 pl.2.2.1).toNat]'har_idx_lt >>> 1).toNat]?.getD 0#32 =
                0#32 := by
              rw [List.getElem?_eq_getElem htmk_lt1, Option.getD_some]
              have har_idx_eq : (w.toNat + BitVec.toNat (3 : BitVec 64) + BitVec.toNat pl.2.2.1) %
                  2 ^ 64 = (BitVec.setWidth 64 w + 3#64 + BitVec.setWidth 64 pl.2.2.1).toNat := by
                simp only [show BitVec.toNat (3 : BitVec 64) = 3 from rfl, hw_sum]
                exact Nat.mod_eq_of_lt (by
                  have := BitVec.isLt w; have := BitVec.isLt pl.2.2.1; omega)
              have hlt_ar : (w.toNat + BitVec.toNat (3 : BitVec 64) + BitVec.toNat pl.2.2.1) %
                  2 ^ 64 < (FidP6Work s tmp1 wsort1 tmk1 scr).core.arena.length := by
                dsimp only [FidP6Work]; rw [har_idx_eq]; exact har_idx_lt
              have hidx_eq : (BitVec.setWidth 64 ((FidP6Work s tmp1 wsort1 tmk1 scr).core.arena[
                  (w.toNat + BitVec.toNat (3 : BitVec 64) +
                    BitVec.toNat pl.2.2.1) % 2 ^ 64] >>> 1)).toNat =
                  (s.core.arena[(BitVec.setWidth 64 w + 3#64 +
                    BitVec.setWidth 64 pl.2.2.1).toNat]'har_idx_lt >>> 1).toNat := by
                dsimp only [FidP6Work]
                rw [fid_k6c_zext64, fid_getElem_congr har_idx_eq _ har_idx_lt]
              have hlt_ctx : (BitVec.setWidth 64 ((FidP6Work s tmp1 wsort1 tmk1 scr).core.arena[
                  (w.toNat + BitVec.toNat (3 : BitVec 64) +
                    BitVec.toNat pl.2.2.1) % 2 ^ 64] >>> 1)).toNat < tmk1.length := by
                rw [hidx_eq]; exact htmk_lt1
              have hget := ‹tmk1[(BitVec.setWidth 64 ((FidP6Work s tmp1 wsort1 tmk1 scr).core.arena[
                (w.toNat + BitVec.toNat (3 : BitVec 64) +
                  BitVec.toNat pl.2.2.1) % 2 ^ 64] >>> 1)).toNat] = 0#32›
              exact (fid_getElem_congr hidx_eq _ htmk_lt1).symm.trans hget
            c0_hsteps
            refine hJ3 (pl.fst + 1#32) abort_in _ _ _ (by simp [hws1]) (by simp [htm1])
              (by bv_omega) (by bv_omega) ?_ hm
            have hreg' := fid_k6c_tmkReg_step hr1 hnv_lt_cv hv_lt ht0 (Or.inr (by omega))
              (by omega) hcv_lt
            have he_i : (BitVec.setWidth 64 pl.fst).toNat = pl.fst.toNat := fid_k6c_zext64
            have ht_i : (BitVec.setWidth 64 ((s.core.arena[(BitVec.setWidth 64 w + 3 +
                BitVec.setWidth 64 pl.2.2.1).toNat] >>> OfNat.ofNat 1))).toNat =
                (s.core.arena[(BitVec.setWidth 64 w + 3#64 +
                  BitVec.setWidth 64 pl.2.2.1).toNat]'har_idx_lt >>> 1).toNat := by
              rw [fid_k6c_zext64]; rfl
            have he_v : (s.core.arena[(BitVec.setWidth 64 w + 3 +
                BitVec.setWidth 64 pl.2.2.1).toNat] >>> OfNat.ofNat 1) = BitVec.ofNat 32
                ((s.core.arena[(BitVec.setWidth 64 w + 3#64 +
                  BitVec.setWidth 64 pl.2.2.1).toNat]'har_idx_lt) >>> 1).toNat := by
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]; rfl
            have ht_v : (pl.fst + 1 : BitVec 32) = BitVec.ofNat 32 (pl.fst.toNat + 1) := by
              apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, BitVec.toNat_add,
                show (1 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
            dsimp only [FidP6Work]; rw [he_i, ht_i, he_v, ht_v]
            exact fid_k6c_tmkReg_congr hreg' (by bv_omega) rfl rfl
          · exact hJ3 pl.fst abort_in wsort1 tmk1 m1 hws1 htm1 hnv1 hnvcv1 hr1 hm1
        · exact hJ2 pl.fst abort_in pl.snd.fst tmp1 wsort1 tmk1 m1
            htp1 hws1 htm1 hnv1 hnvcv1 hcsz1 hr1 hm1
      · exact hJ1 pl.fst abort_in pl.snd.fst tmp1 wsort1 tmk1 m1
          htp1 hws1 htm1 hnv1 hnvcv1 hcsz1 hr1 hm1
    · exact hRet pl.fst abort_in false pl.snd.fst pl.snd.snd.fst tmp1 wsort1 tmk1
        htp1 hws1 htm1 hnv1 hnvcv1 hcsz1 hr1 m1 hm1
end
end LeanQbe.T.Examples.Kissat.Proof.Definition
