/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Helpers
public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Spec
public import LeanQbe.T.Examples.Kissat.Src.Eliminate
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat BVE `Func.wp` Proofs — Part 0b (`Wp0b`: `full_bve_resolve_pair_wp`)

Clean `CanonicalEnv` `Func.wp` proof (`0` legacy `Full*` imports, `<= 100` cols,
every decl `<= 450`L) for `full_bve_resolve_pair` (`Spec.fullBveResolvePairSpec`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Eliminate

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Eliminate
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Eliminate.EliminateTactics
open Kraken.Bedrock2.Test

open scoped FullArenaTactics
open scoped EliminateTactics

/-! ## 1. Pure Helpers (`Nodup` bound, Resolution, & `ResInv`) -/

private theorem nodup_lt_len_le :
    ∀ (n : Nat) (xs : List Nat), xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n
  | 0, [], _, _ => Nat.zero_le 0
  | 0, x :: _, _, hlt => absurd (hlt x List.mem_cons_self) (Nat.not_lt_zero _)
  | n + 1, xs, hnd, hlt => by
    by_cases hm : n ∈ xs
    · have hlen := nodup_lt_len_le n (xs.erase n) (hnd.erase n) fun x hx => by
        have hne : x ≠ n := fun heq => by
          subst heq
          exact ((List.Nodup.mem_erase_iff hnd).mp hx).1 rfl
        have := hlt x (List.mem_of_mem_erase hx); omega
      have := List.length_erase_of_mem hm; omega
    · have := nodup_lt_len_le n xs hnd fun x hx => by
        have hne : x ≠ n := fun heq => hm (heq ▸ hx)
        have := hlt x hx; omega
      omega

private theorem resolve_lits_entails {F : CNF Nat} {p : Nat} {R : List Nat}
    (hp : F.EntailsClause (cnfClause (p :: R)))
    (hn : F.EntailsClause (cnfClause ((p ^^^ 1) :: R))) :
    F.EntailsClause (cnfClause R) := by
  rw [CNF.entails_clause_def] at hp hn ⊢
  intro α hα
  have sp := (clause_sat_cnfClause_iff α _).mp (hp α hα)
  have sn := (clause_sat_cnfClause_iff α _).mp (hn α hα)
  rw [clause_sat_cnfClause_iff]
  obtain ⟨lp, hmp, hsp⟩ := sp
  obtain ⟨ln, hmn, hsn⟩ := sn
  rcases List.mem_cons.mp hmp with rfl | hmp
  · rcases List.mem_cons.mp hmn with rfl | hmn
    · exfalso
      simp only [litVar, litSign] at hsp hsn
      rw [fullInv_var_xor1, elim_xor1_mod2] at hsn
      rcases Nat.mod_two_eq_zero_or_one lp with hm0 | hm1
      · cases hv : α (lp / 2) <;> simp [hv, hm0] at hsp hsn
      · cases hv : α (lp / 2) <;> simp [hv, hm1] at hsp hsn
    · exact ⟨ln, hmn, hsn⟩
  · exact ⟨lp, hmp, hsp⟩

private theorem fullDenseInvW_with_tmp_lm {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {tl' : Nat} {lm' : List (BitVec 8)} {tmp' : List (BitVec 32)}
    (htl : tl' ≤ c.max_vars) (hlm_len : lm'.length = 2 * c.max_vars)
    (htmp_len : tmp'.length = c.max_vars)
    (hlm_clr : ∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 = 0#8) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with tmp_len := tl', lit_mark := lm', tmp := tmp' } } :=
  ⟨⟨{ h.1.core_ok with lit_mark_len := hlm_len, tmp_len_arr := htmp_len, tmp_len_le := htl },
    h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   ⟨h.2.2.1.1, hlm_clr⟩, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem fullArenaClauseLits_getElem_eq {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c) (ha : FullArenaClausesInv c F_cur s.core)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) {k : Nat}
    (hk : k < fullArenaClauseSize s cref)
    (hkar : cref + 3 + k < s.core.arena.length) :
    (fullArenaClauseLits s cref)[k]'(by
      have hwf := ha.refs_wf cref href
      have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr
      have hsz_c : fullArenaClauseSize s cref = fullArenaClauseSizeCore s.core cref := rfl
      unfold fullArenaClauseLits fullArenaClauseLitsCore
      simp only [List.length_map, List.length_take, List.length_drop]
      rw [hsz_c] at hk; omega) = (s.core.arena[cref + 3 + k]'hkar).toNat := by
  unfold fullArenaClauseLits fullArenaClauseLitsCore
  simp only [List.getElem_map, List.getElem_take, List.getElem_drop]

private theorem resArena_lit_props {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} (hdw : FullDenseInvW c F0 F_cur s0) {cref : BitVec 32}
    (href : cref.toNat ∈ fullArenaClauseRefs s0) (hng : fullArenaClauseGarb s0 cref.toNat = false)
    {k : BitVec 32} (hk : k.toNat < fullArenaClauseSize s0 cref.toNat)
    (hkar : (cref.setWidth 64 + 3#64 + k.setWidth 64).toNat < s0.core.arena.length) :
    let l := s0.core.arena[(cref.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hkar
    l.toNat = (fullArenaClauseLits s0 cref.toNat)[k.toNat]?.getD 0 ∧
    l.toNat < 2 * s0.core.cur_vars := by
  intro l
  have hwf := hdw.2.1.arena.refs_wf cref.toNat href
  have := hdw.1.core_ok.arena_len_le; have := hdw.1.core_ok.arena_len_arr
  have hsz_c : fullArenaClauseSize s0 cref.toNat = fullArenaClauseSizeCore s0.core cref.toNat := rfl
  have hbd : cref.toNat + 3 + fullArenaClauseSize s0 cref.toNat ≤ s0.core.arena.length := by
    rw [hsz_c]; omega
  have hk_bd : cref.toNat + 3 + k.toNat < s0.core.arena.length := by omega
  have hlen_l : (fullArenaClauseLits s0 cref.toNat).length = fullArenaClauseSize s0 cref.toNat := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    simp only [List.length_map, List.length_take, List.length_drop]; omega
  have hget := fullArenaClauseLits_getElem_eq hdw.1 hdw.2.1.arena href hk hk_bd
  have hl_eq : l.toNat = (fullArenaClauseLits s0 cref.toNat)[k.toNat]?.getD 0 := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]
    exact congrArg BitVec.toNat (elim_getElem_congr (by
      rw [BitVec.toNat_add, BitVec.toNat_add, elim_zext32_toNat, elim_zext32_toNat,
        show (3#64).toNat = 3 from rfl]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]) _ hk_bd)
  refine ⟨hl_eq, ?_⟩
  rw [hl_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact hdw.2.1.arena.lits_lt cref.toNat href hng _ (List.getElem_mem _)

private theorem bveEntry_entails_bin {F_cur : List (List Nat)} {s : FullState}
    {lit : Nat} {w : BitVec 32} (h : FullBveEntryOkW F_cur s lit w)
    (hb : (w &&& 0x80000000#32) ≠ 0#32) :
    (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w &&& 0x7FFFFFFF#32).toNat]) := by
  unfold FullBveEntryOkW at h; rwa [ite_eq_left hb] at h

private theorem bveEntry_large_ok {F_cur : List (List Nat)} {s : FullState}
    {lit : Nat} {w : BitVec 32} (h : FullBveEntryOkW F_cur s lit w)
    (hb : (w &&& 0x80000000#32) = 0#32) :
    w.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s w.toNat = false := by
  unfold FullBveEntryOkW at h; rwa [ite_eq_right (fun hn => hn hb)] at h

private def ResCovered (s0 : FullState) (rlen : Nat) (tmp : List (BitVec 32))
    (exclude l : Nat) : Prop :=
  l = exclude ∨ s0.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
    ∃ j < rlen, (tmp[j]?.getD 0#32).toNat = l

private theorem resCovered_mono {s0 : FullState} {r1 r2 : Nat} {tmp1 tmp2 : List (BitVec 32)}
    {exclude l : Nat} (hle : r1 ≤ r2) (hpre : ∀ j < r1, tmp2[j]? = tmp1[j]?)
    (hc : ResCovered s0 r1 tmp1 exclude l) : ResCovered s0 r2 tmp2 exclude l := by
  rcases hc with rfl | hneg | ⟨j, hj, htj⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl hneg)
  · exact Or.inr (Or.inr ⟨j, by omega, by rw [hpre j hj]; exact htj⟩)

private theorem lit_neg_contradiction {α : Nat → Bool} {l : Nat}
    (hs1 : α (litVar l) = !litSign l) (hs2 : α (litVar (l ^^^ 1)) = !litSign (l ^^^ 1)) :
    False := by
  simp only [litVar, litSign] at hs1 hs2
  rw [fullInv_var_xor1, elim_xor1_mod2] at hs2
  rcases Nat.mod_two_eq_zero_or_one l with hm0 | hm1
  · cases hv : α (l / 2) <;> simp [hv, hm0] at hs1 hs2
  · cases hv : α (l / 2) <;> simp [hv, hm1] at hs1 hs2

private theorem resSide_bin_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} (hdw : FullDenseInvW c F0 F_cur s0) {exclude : Nat} {w : BitVec 32}
    (he : FullBveEntryOkW F_cur s0 exclude w) (hb : (w &&& 0x80000000#32) ≠ 0#32)
    {rlen : Nat} {tmp : List (BitVec 32)} (htmp : rlen ≤ tmp.length)
    (hcov : ResCovered s0 rlen tmp exclude (w &&& 0x7FFFFFFF#32).toNat) :
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause (exclude :: (tmp.take rlen).map BitVec.toNat)) := by
  obtain ⟨hot_lt, hent⟩ := bveEntry_entails_bin he hb
  rw [CNF.entails_clause_def] at hent ⊢
  intro α hα
  have hs := (clause_sat_cnfClause_iff α _).mp (hent α hα)
  rw [clause_sat_cnfClause_iff]
  obtain ⟨l, hl, hsl⟩ := hs
  rcases List.mem_cons.mp hl with rfl | hl
  · exact ⟨l, List.mem_cons_self, hsl⟩
  · rw [List.mem_singleton] at hl; subst hl
    rcases hcov with heq | hneg | ⟨j, hj, htj⟩
    · exact ⟨exclude, List.mem_cons_self, heq ▸ hsl⟩
    · exfalso
      have hnv := elim_vals_neg_entails hdw.2.1 hdw.2.2.2.2.2.1 hot_lt hneg
      have hsn := (clause_sat_cnfClause_iff α _).mp ((CNF.entails_clause_def.mp hnv) α hα)
      obtain ⟨l', hl', hs'⟩ := hsn
      rw [List.mem_singleton] at hl'; subst hl'
      exact lit_neg_contradiction hsl hs'
    · refine ⟨(w &&& 0x7FFFFFFF#32).toNat, List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨tmp[j]'(by omega), ?_, ?_⟩), hsl⟩
      · exact List.mem_take_iff_getElem.mpr ⟨j, by simp [htmp]; exact hj, rfl⟩
      · rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at htj; exact htj

private theorem resSide_large_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} (hdw : FullDenseInvW c F0 F_cur s0) {exclude : Nat} {w : BitVec 32}
    (he : FullBveEntryOkW F_cur s0 exclude w) (hb : (w &&& 0x80000000#32) = 0#32)
    {rlen : Nat} {tmp : List (BitVec 32)} (htmp : rlen ≤ tmp.length)
    (hcov : ∀ k < fullArenaClauseSize s0 w.toNat,
      ResCovered s0 rlen tmp exclude ((fullArenaClauseLits s0 w.toNat)[k]?.getD 0)) :
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause (exclude :: (tmp.take rlen).map BitVec.toNat)) := by
  obtain ⟨href, hng⟩ := bveEntry_large_ok he hb
  have hent := hdw.2.1.arena.entails w.toNat href hng
  rw [CNF.entails_clause_def] at hent ⊢
  intro α hα
  have hs := (clause_sat_cnfClause_iff α _).mp (hent α hα)
  rw [clause_sat_cnfClause_iff]
  obtain ⟨l, hl, hsl⟩ := hs
  have hlt := hdw.2.1.arena.lits_lt w.toNat href hng l hl
  obtain ⟨k, hk_len, hkl⟩ := List.mem_iff_getElem.mp hl
  have hsz_eq : (fullArenaClauseLits s0 w.toNat).length = fullArenaClauseSize s0 w.toNat := by
    have hwf := hdw.2.1.arena.refs_wf w.toNat href
    have := hdw.1.core_ok.arena_len_le; have := hdw.1.core_ok.arena_len_arr
    have hsz_c : fullArenaClauseSize s0 w.toNat = fullArenaClauseSizeCore s0.core w.toNat := rfl
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    simp only [List.length_map, List.length_take, List.length_drop]; rw [hsz_c]; omega
  have hk_sz : k < fullArenaClauseSize s0 w.toNat := hsz_eq ▸ hk_len
  have hck := hcov k hk_sz
  rw [List.getElem?_eq_getElem hk_len, Option.getD_some, hkl] at hck
  rcases hck with rfl | hneg | ⟨j, hj, htj⟩
  · exact ⟨l, List.mem_cons_self, hsl⟩
  · exfalso
    have hnv := elim_vals_neg_entails hdw.2.1 hdw.2.2.2.2.2.1 hlt hneg
    have hsn := (clause_sat_cnfClause_iff α _).mp ((CNF.entails_clause_def.mp hnv) α hα)
    obtain ⟨l', hl', hs'⟩ := hsn
    rw [List.mem_singleton] at hl'; subst hl'
    exact lit_neg_contradiction hsl hs'
  · refine ⟨l, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨tmp[j]'(by omega), ?_, ?_⟩), hsl⟩
    · exact List.mem_take_iff_getElem.mpr ⟨j, by simp [htmp]; exact hj, rfl⟩
    · rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at htj; exact htj

private theorem resSide_pc_entails_mono {F_cur : List (List Nat)} {lit : Nat}
    {r1 r2 : Nat} {tmp1 tmp2 : List (BitVec 32)}
    (hle : r1 ≤ r2) (ht1 : r1 ≤ tmp1.length) (ht2 : r2 ≤ tmp2.length)
    (hpre : ∀ j < r1, tmp2[j]? = tmp1[j]?)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (lit :: (tmp1.take r1).map BitVec.toNat))) :
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause (lit :: (tmp2.take r2).map BitVec.toNat)) := by
  rw [CNF.entails_clause_def] at hent ⊢
  intro α hα
  have hs := (clause_sat_cnfClause_iff α _).mp (hent α hα)
  rw [clause_sat_cnfClause_iff]
  obtain ⟨l, hl, hsl⟩ := hs
  rcases List.mem_cons.mp hl with rfl | hl
  · exact ⟨l, List.mem_cons_self, hsl⟩
  · rw [List.mem_map] at hl
    obtain ⟨x, hx, rfl⟩ := hl
    obtain ⟨j, hj_len, hxj⟩ := List.mem_take_iff_getElem.mp hx
    have hj1 : j < r1 := Nat.lt_of_lt_of_le hj_len (Nat.min_le_left _ _)
    have hj_t1 : j < tmp1.length := by omega
    have hj_t2 : j < tmp2.length := by omega
    have hget : tmp2[j]'hj_t2 = tmp1[j]'hj_t1 := by
      have hp := hpre j hj1
      rw [List.getElem?_eq_getElem hj_t2, List.getElem?_eq_getElem hj_t1] at hp
      exact Option.some.inj hp
    refine ⟨x.toNat, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨tmp2[j]'hj_t2, ?_, ?_⟩), hsl⟩
    · exact List.mem_take_iff_getElem.mpr ⟨j, by simp [ht2]; omega, rfl⟩
    · rw [hget, hxj]

private structure ResInv (c : FullCfg) (s0 : FullState) (rlen : Nat)
    (lm : List (BitVec 8)) (tmp : List (BitVec 32)) : Prop where
  rlen_le : rlen ≤ s0.core.cur_vars
  lm_len : lm.length = 2 * c.max_vars
  tmp_len : tmp.length = c.max_vars
  lits_lt : ∀ k < rlen, (tmp[k]?.getD 0#32).toNat < 2 * s0.core.cur_vars
  lits_unass : ∀ k < rlen, s0.core.vals[(tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 0#8
  nodup_var : ((tmp.take rlen).map (fun x => x.toNat / 2)).Nodup
  lm_iff : ∀ x < 2 * c.max_vars,
    lm[x]?.getD 0#8 ≠ 0#8 ↔ ∃ k < rlen, (tmp[k]?.getD 0#32).toNat = x

private theorem resInv_init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} (hdw : FullDenseInvW c F0 F_cur s0) :
    ResInv c s0 0 s0.core.lit_mark s0.core.tmp :=
  ⟨Nat.zero_le _, hdw.1.core_ok.lit_mark_len, hdw.1.core_ok.tmp_len_arr,
   fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
   by rw [List.take_zero, List.map_nil]; exact List.nodup_nil,
   fun x hx => by
     simp only [Nat.not_lt_zero, false_and, exists_false, iff_false]
     exact fun hne => hne (hdw.2.2.1.2 x hx)⟩

private theorem resInv_add {c : FullCfg} {s0 : FullState} {rlen : Nat}
    {lm : List (BitVec 8)} {tmp : List (BitVec 32)} (hi : ResInv c s0 rlen lm tmp)
    {l : BitVec 32} (hl_lt : l.toNat < 2 * s0.core.cur_vars)
    (hcv_le : s0.core.cur_vars ≤ c.max_vars)
    (hun : s0.core.vals[l.toNat]?.getD 0#8 = 0#8)
    (hlm0 : lm[l.toNat]?.getD 0#8 = 0#8)
    (hlm1 : lm[l.toNat ^^^ 1]?.getD 0#8 = 0#8) :
    rlen < s0.core.cur_vars ∧ rlen < tmp.length ∧ l.toNat < lm.length ∧
    ResInv c s0 (rlen + 1) (lm.set l.toNat 1#8) (tmp.set rlen l) := by
  have hnot_mem : l.toNat / 2 ∉ (tmp.take rlen).map (fun x => x.toNat / 2) := by
    intro hm; rw [List.mem_map] at hm; obtain ⟨w, hw, hdv⟩ := hm
    have hw_idx : ∃ k < rlen, tmp[k]? = some w := by
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hw
      have hk_len : k < (tmp.take rlen).length := (List.getElem?_eq_some_iff.mp hk).1
      rw [List.length_take] at hk_len
      have hk_r : k < rlen := Nat.lt_of_lt_of_le hk_len (Nat.min_le_left _ _)
      refine ⟨k, hk_r, ?_⟩; rwa [List.getElem?_take_of_lt hk_r] at hk
    obtain ⟨k, hk, htk⟩ := hw_idx
    have hweq : (tmp[k]?.getD 0#32).toNat = w.toNat := by simp [htk]
    have hx1 := fullInv_var_xor1 l.toNat; have hx2 := elim_xor1_mod2 l.toNat
    have hwl : w.toNat = l.toNat ∨ w.toNat = l.toNat ^^^ 1 := by omega
    rcases hwl with h | h
    · exact (hi.lm_iff l.toNat (by omega)).mpr ⟨k, hk, hweq.trans h⟩ hlm0
    · exact (hi.lm_iff (l.toNat ^^^ 1) (by omega)).mpr ⟨k, hk, hweq.trans h⟩ hlm1
  have hrlen_lt : rlen < s0.core.cur_vars := by
    have hlen : ((tmp.take rlen).map (fun x => x.toNat / 2)).length = rlen := by
      simp [hi.tmp_len, Nat.min_eq_left (Nat.le_trans hi.rlen_le hcv_le)]
    have hnd1 : (l.toNat / 2 :: (tmp.take rlen).map (fun x => x.toNat / 2)).Nodup :=
      List.nodup_cons.mpr ⟨hnot_mem, hi.nodup_var⟩
    have hle1 := nodup_lt_len_le s0.core.cur_vars _ hnd1 fun v hv => by
      rcases List.mem_cons.mp hv with rfl | hv
      · omega
      · rw [List.mem_map] at hv; obtain ⟨w, hw, rfl⟩ := hv
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hw
        have hk_lt : k < rlen := by
          have := (List.getElem?_eq_some_iff.mp hk).1; rw [List.length_take] at this; omega
        have htk : tmp[k]?.getD 0#32 = w := by rw [List.getElem?_take_of_lt hk_lt] at hk; simp [hk]
        have := hi.lits_lt k hk_lt; rw [← htk]; omega
    simp only [List.length_cons, hlen] at hle1; omega
  have htmpr : rlen < tmp.length := by rw [hi.tmp_len]; omega
  have hlml : l.toNat < lm.length := by rw [hi.lm_len]; omega
  refine ⟨hrlen_lt, htmpr, hlml, by omega, by simp [hi.lm_len],
    by simp [hi.tmp_len], ?_, ?_, ?_, ?_⟩
  · intro k hk; rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hk' | hkeq
    · rw [List.getElem?_set_ne (by omega)]; exact hi.lits_lt k hk'
    · subst hkeq; rw [List.getElem?_set_self htmpr, Option.getD_some]; exact hl_lt
  · intro k hk; rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hk' | hkeq
    · rw [List.getElem?_set_ne (by omega)]; exact hi.lits_unass k hk'
    · subst hkeq; rw [List.getElem?_set_self htmpr, Option.getD_some]; exact hun
  · have htake : (tmp.set rlen l).take (rlen + 1) = tmp.take rlen ++ [l] := by
      apply List.ext_getElem
      · simp [hi.tmp_len, Nat.min_eq_left (by omega : rlen + 1 ≤ c.max_vars),
          Nat.min_eq_left (by omega : rlen ≤ c.max_vars)]
      · intro idx hi1 hi2
        have hilt : idx < rlen + 1 := by
          simp [hi.tmp_len, show rlen + 1 ≤ c.max_vars by omega] at hi1; exact hi1
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hilt) with h | idx_eq
        · rw [List.getElem_take, List.getElem_set_ne (by omega), List.getElem_append_left
            (by simp [hi.tmp_len, show rlen ≤ c.max_vars by omega]; omega), List.getElem_take]
        · have htl : (List.take rlen tmp).length = rlen := by
            rw [List.length_take, Nat.min_eq_left (by omega)]
          rw [List.getElem_take, List.getElem_append_right (by simp [hi.tmp_len]; omega)]
          simp only [idx_eq, htl, Nat.sub_self, List.getElem_cons_zero]
          exact List.getElem_set_self (by simp [htmpr])
    rw [htake, List.map_append, List.map_singleton, List.nodup_append]
    refine ⟨hi.nodup_var, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, fun a ha b hb heq => ?_⟩
    rw [List.mem_singleton] at hb; subst hb; subst heq; exact hnot_mem ha
  · intro x hx; constructor
    · intro hnz
      by_cases hxl : x = l.toNat
      · subst hxl; refine ⟨rlen, Nat.lt_succ_self _, ?_⟩
        rw [List.getElem?_set_self htmpr, Option.getD_some]
      · rw [List.getElem?_set_ne (Ne.symm hxl)] at hnz
        obtain ⟨k, hk, htk⟩ := (hi.lm_iff x hx).mp hnz
        exact ⟨k, Nat.lt_succ_of_lt hk, by rw [List.getElem?_set_ne (by omega)]; exact htk⟩
    · rintro ⟨k, hk, htk⟩
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hk' | hk_eq
      · rw [List.getElem?_set_ne (by omega)] at htk
        by_cases hxl : x = l.toNat
        · subst hxl; exact absurd ((hi.lm_iff _ hx).mpr ⟨k, hk', htk⟩) (fun h => h hlm0)
        · rw [List.getElem?_set_ne (Ne.symm hxl)]; exact (hi.lm_iff x hx).mpr ⟨k, hk', htk⟩
      · rw [hk_eq, List.getElem?_set_self htmpr, Option.getD_some] at htk
        rw [← htk, List.getElem?_set_self hlml, Option.getD_some]; decide

private theorem resUnmark_step {c : FullCfg} {rlen : Nat}
    {lm_k : List (BitVec 8)} {tmp2 : List (BitVec 32)} {k : BitVec 32}
    (hkt : (k.setWidth 64).toNat < tmp2.length)
    (hlm_idx : ((tmp2[(k.setWidth 64).toNat]'hkt).setWidth 64).toNat < lm_k.length)
    (hrem_lm : ∀ x < 2 * c.max_vars, lm_k[x]?.getD 0#8 ≠ 0#8 →
      ∃ j, k.toNat ≤ j ∧ j < rlen ∧ (tmp2[j]?.getD 0#32).toNat = x) :
    ∀ x < 2 * c.max_vars,
      (lm_k.set ((tmp2[(k.setWidth 64).toNat]'hkt).setWidth 64).toNat 0#8)[x]?.getD 0#8 ≠ 0#8 →
      ∃ j, k.toNat + 1 ≤ j ∧ j < rlen ∧ (tmp2[j]?.getD 0#32).toNat = x := by
  intro x hx hnz
  by_cases hxe : x = ((tmp2[(k.setWidth 64).toNat]'hkt).setWidth 64).toNat
  · subst hxe; rw [List.getElem?_set_self hlm_idx, Option.getD_some] at hnz; exact absurd rfl hnz
  · rw [List.getElem?_set_ne (Ne.symm hxe)] at hnz
    obtain ⟨j, hj1, hj2, htj⟩ := hrem_lm x hx hnz
    refine ⟨j, ?_, hj2, htj⟩
    rcases Nat.eq_or_lt_of_le hj1 with rfl | hlt
    · exfalso; apply hxe; rw [elim_zext32_toNat]
      have hk' : (k.setWidth 64).toNat = k.toNat := elim_zext32_toNat k
      have hkt' : k.toNat < tmp2.length := hk' ▸ hkt
      have heq := elim_getElem_congr hk' hkt hkt'
      have hget := List.getElem?_eq_getElem hkt'
      rw [heq, ← Option.getD_some (a := tmp2[k.toNat]'hkt') (b := 0#32), ← hget, htj]
    · omega

private theorem res_vals_eq0 {v : BitVec 8}
    (hvdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (hnotpos : (BitVec.ofNat 32 0).slt (v.signExtend 32) = false)
    (h0 : v.signExtend 32 = 0#32) : v = 0#8 := by
  rcases hvdom with rfl | rfl | rfl
  · rfl
  · simp at hnotpos
  · revert h0; decide

private theorem res_vals_neg {v : BitVec 8}
    (hvdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (hnotpos : (BitVec.ofNat 32 0).slt (v.signExtend 32) = false)
    (hne0 : v.signExtend 32 ≠ 0#32) : v = 0xFF#8 := by
  rcases hvdom with rfl | rfl | rfl
  · exact absurd rfl hne0
  · simp at hnotpos
  · rfl

private theorem zext32_eq0_of {v : BitVec 8} (h : v.setWidth 32 = 0#32) : v = 0#8 := by
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : v.toNat < 2 ^ 32)] at h1
  exact BitVec.eq_of_toNat_eq h1

private theorem zext32_ne0_of {v : BitVec 8} (h : v.setWidth 32 ≠ 0#32) : v ≠ 0#8 :=
  fun h0 => h (by subst h0; decide)

private theorem res_large_hdr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} (hdw0 : FullDenseInvW c F0 F_cur s0)
    {lit : Nat} {cref : BitVec 32}
    (hok : FullBveEntryOkW F_cur s0 lit cref) (hbin : (cref &&& 0x80000000#32) = 0#32) :
    cref.toNat ∈ fullArenaClauseRefs s0 ∧ fullArenaClauseGarb s0 cref.toNat = false ∧
    cref.toNat + 3 + fullArenaClauseSize s0 cref.toNat ≤ s0.core.arena_len ∧
    (cref.setWidth 64 + 2#64).toNat < s0.core.arena.length ∧
    ∀ h : (cref.setWidth 64 + 2#64).toNat < s0.core.arena.length,
      (s0.core.arena[(cref.setWidth 64 + 2#64).toNat]'h).toNat =
        fullArenaClauseSize s0 cref.toNat := by
  obtain ⟨href, hng⟩ := bveEntry_large_ok hok hbin
  have hwf := hdw0.2.1.arena.refs_wf cref.toNat href
  have hal_le := hdw0.1.core_ok.arena_len_le
  have harc := c.harena; unfold dimacsBound at harc
  refine ⟨href, hng, Nat.le_trans hwf.2.2.1 hwf.2.2.2.1,
    by rw [hdw0.1.core_ok.arena_len_arr]; c0_bound, fun h => ?_⟩
  unfold fullArenaClauseSize fullArenaClauseSizeCore
  rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega), Option.getD_some]
  exact congrArg BitVec.toNat (elim_getElem_congr (by c0_bound) _ _)

private theorem resLarge_exit_hk {s0 : FullState} {cref k : BitVec 32}
    (h2 : (cref.setWidth 64 + 2#64).toNat < s0.core.arena.length)
    (hk_le : k.toNat ≤ (s0.core.arena[(cref.setWidth 64 + 2#64).toNat]'h2).toNat)
    {h' : (cref.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 < s0.core.arena.length}
    (hnot : ¬k.toNat <
      (s0.core.arena[(cref.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'h').toNat) :
    k.toNat = (s0.core.arena[(cref.setWidth 64 + 2#64).toNat]'h2).toNat := by
  have hc0 : (cref.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
      (cref.setWidth 64 + 2#64).toNat := by rw [BitVec.toNat_add, elim_zext32_toNat]; rfl
  rw [elim_getElem_congr hc0 h' h2] at hnot; omega

private theorem resLarge_lit_c0 {c : FullCfg} {cref k : BitVec 32}
    (h : cref.toNat + 3 + k.toNat < c.arena_cap) :
    (cref.toNat + 3 + k.toNat) % 2 ^ 64 = (cref.setWidth 64 + 3#64 + k.setWidth 64).toNat := by
  have harc := c.harena; unfold dimacsBound at harc
  rw [BitVec.toNat_add, BitVec.toNat_add, elim_zext32_toNat, elim_zext32_toNat,
    show (3#64 : BitVec 64).toNat = 3 from rfl,
    Nat.mod_eq_of_lt (by omega : cref.toNat + 3 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : cref.toNat + 3 + k.toNat < 2 ^ 64)]

private theorem resUnmark_idx_lt {c : FullCfg} {s0 : FullState} {rlen : Nat}
    {lm2 lm_k : List (BitVec 8)} {tmp2 : List (BitVec 32)} {k : BitVec 32}
    (hri2 : ResInv c s0 rlen lm2 tmp2) (hcv_le : s0.core.cur_vars ≤ c.max_vars)
    (hk_lt : k.toNat < rlen) (hlmk : lm_k.length = 2 * c.max_vars) :
    ∃ (hkt : (k.setWidth 64).toNat < tmp2.length),
      ((tmp2[(k.setWidth 64).toNat]'hkt).setWidth 64).toNat < lm_k.length := by
  have hkt : (k.setWidth 64).toNat < tmp2.length := by
    rw [hri2.tmp_len, elim_zext32_toNat]
    exact Nat.lt_of_lt_of_le hk_lt (Nat.le_trans hri2.rlen_le hcv_le)
  have hl_lt := hri2.lits_lt k.toNat hk_lt
  have hk' := elim_zext32_toNat k
  have hkt' : k.toNat < tmp2.length := hk' ▸ hkt
  rw [List.getElem?_eq_getElem hkt', Option.getD_some] at hl_lt
  refine ⟨hkt, ?_⟩
  rw [hlmk, elim_zext32_toNat, elim_getElem_congr hk' hkt hkt']
  exact Nat.lt_of_lt_of_le hl_lt (by omega)

private theorem res_cov_succ {s0 : FullState} {r0 r1 : Nat} {t0 t1 : List (BitVec 32)}
    {excl l_nat k idx : Nat} {f : Nat → Nat}
    (hle : r0 ≤ r1) (hpre : ∀ j < r0, t1[j]? = t0[j]?)
    (hcov : ∀ i < k, ResCovered s0 r0 t0 excl (f i))
    (hl_eq : l_nat = f k) (hcovl : ResCovered s0 r1 t1 excl l_nat)
    (hidx : idx < k + 1) : ResCovered s0 r1 t1 excl (f idx) := by
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hidx) with hi' | rfl
  · exact resCovered_mono hle hpre (hcov idx hi')
  · exact hl_eq ▸ hcovl

private def resSt (s0 : FullState) (lm : List (BitVec 8)) (tmp : List (BitVec 32)) : FullState :=
  { s0 with core := { s0.core with lit_mark := lm, tmp := tmp } }

private theorem resSt_self (s0 : FullState) : resSt s0 s0.core.lit_mark s0.core.tmp = s0 := by
  cases s0 with | mk core scr => cases core; rfl

private theorem resSt_stores (s0 : FullState) (lm' : List (BitVec 8)) (tmp' : List (BitVec 32)) :
    { ({ s0 with core := { s0.core with lit_mark := lm' } }) with
      core := { ({ s0 with core := { s0.core with lit_mark := lm' } }).core with tmp := tmp' } } =
      resSt s0 lm' tmp' := rfl

private theorem resSt_stores2 (s0 : FullState) (lm1 lm2 : List (BitVec 8))
    (tmp1 tmp2 : List (BitVec 32)) :
    { ({ resSt s0 lm1 tmp1 with
          core := { (resSt s0 lm1 tmp1).core with lit_mark := lm2 } }) with
      core := { ({ resSt s0 lm1 tmp1 with
          core := { (resSt s0 lm1 tmp1).core with lit_mark := lm2 } }).core with tmp := tmp2 } } =
      resSt s0 lm2 tmp2 := rfl

private abbrev ResSideInv (c : FullCfg) (F_cur : List (List Nat)) (s0 : FullState)
    (lit : Nat) (R : Mem 64 → Prop) :
    BitVec 32 × Bool × List (BitVec 8) × List (BitVec 32) → Mem 64 → Prop :=
  fun x mp =>
    ResInv c s0 x.1.toNat x.2.2.1 x.2.2.2 ∧
    (x.2.1 = false → (cnfOfClauses F_cur).EntailsClause
      (cnfClause (lit :: (x.2.2.2.take x.1.toNat).map BitVec.toNat))) ∧
    (FullMem c (resSt s0 x.2.2.1 x.2.2.2) ⋆ R) mp

private abbrev ResBothInv (c : FullCfg) (F_cur : List (List Nat)) (s0 : FullState)
    (v : Nat) (R : Mem 64 → Prop) :
    BitVec 32 × Bool × List (BitVec 8) × List (BitVec 32) → Mem 64 → Prop :=
  fun x mq =>
    ResInv c s0 x.1.toNat x.2.2.1 x.2.2.2 ∧
    (x.2.1 = false →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((2 * v) :: (x.2.2.2.take x.1.toNat).map BitVec.toNat)) ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((2 * v + 1) :: (x.2.2.2.take x.1.toNat).map BitVec.toNat))) ∧
    (FullMem c (resSt s0 x.2.2.1 x.2.2.2) ⋆ R) mq

private abbrev ResStepInv (c : FullCfg) (s0 : FullState) (r0 : Nat) (tmp0 : List (BitVec 32))
    (exclude : Nat) (l : BitVec 32) (R : Mem 64 → Prop) :
    BitVec 32 × List (BitVec 8) × List (BitVec 32) → Mem 64 → Prop :=
  fun x mx =>
    ResInv c s0 x.1.toNat x.2.1 x.2.2 ∧ r0 ≤ x.1.toNat ∧
    (∀ j < r0, x.2.2[j]? = tmp0[j]?) ∧ ResCovered s0 x.1.toNat x.2.2 exclude l.toNat ∧
    (FullMem c (resSt s0 x.2.1 x.2.2) ⋆ R) mx

private abbrev ResLitInv (c : FullCfg) (s0 : FullState) (r0 : Nat) (tmp0 : List (BitVec 32))
    (exclude : Nat) (l : BitVec 32) (R : Mem 64 → Prop) :
    BitVec 32 × Bool × List (BitVec 8) × List (BitVec 32) → Mem 64 → Prop :=
  fun x mx =>
    ResInv c s0 x.1.toNat x.2.2.1 x.2.2.2 ∧ r0 ≤ x.1.toNat ∧
    (∀ j < r0, x.2.2.2[j]? = tmp0[j]?) ∧
    ResCovered s0 x.1.toNat x.2.2.2 exclude l.toNat ∧
    (FullMem c (resSt s0 x.2.2.1 x.2.2.2) ⋆ R) mx

private theorem res_add_step_post {c : FullCfg} {s0 : FullState} {rn : BitVec 32}
    {lmn : List (BitVec 8)} {tmpn : List (BitVec 32)} {exclude : Nat} {l : BitVec 32}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hrin : ResInv c s0 rn.toNat lmn tmpn) (hl_lt : l.toNat < 2 * s0.core.cur_vars)
    (hcv_le : s0.core.cur_vars ≤ c.max_vars)
    (h0 : s0.core.vals[l.toNat]?.getD 0#8 = 0#8)
    (hlm0 : lmn[l.toNat]?.getD 0#8 = 0#8)
    (hlm1 : lmn[l.toNat ^^^ 1]?.getD 0#8 = 0#8)
    (hm : (FullMem c (resSt s0 (lmn.set l.toNat 1#8) (tmpn.set rn.toNat l)) ⋆ R) m) :
    ResStepInv c s0 rn.toNat tmpn exclude l R
      (rn + 1#32, lmn.set l.toNat 1#8, tmpn.set rn.toNat l) m := by
  obtain ⟨hrlt, htmpr, hlml, hri'⟩ := resInv_add hrin hl_lt hcv_le h0 hlm0 hlm1
  have hmx := c.hmaxv; unfold dimacsBound at hmx; have := hrin.rlen_le
  have hr1 : (rn + 1#32).toNat = rn.toNat + 1 := by c0_bound
  refine ⟨by rw [hr1]; exact hri', by rw [hr1]; omega, fun j hj => by
      rw [List.getElem?_set_ne (by omega)],
    Or.inr (Or.inr ⟨rn.toNat, by rw [hr1]; omega, by
      rw [List.getElem?_set_self htmpr, Option.getD_some]⟩), hm⟩

private theorem res_dup_step_post {c : FullCfg} {s0 : FullState} {rn : BitVec 32}
    {lmn : List (BitVec 8)} {tmpn : List (BitVec 32)} {exclude : Nat} {l : BitVec 32}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hrin : ResInv c s0 rn.toNat lmn tmpn) (hl_lt : l.toNat < 2 * c.max_vars)
    (hnz : lmn[l.toNat]?.getD 0#8 ≠ 0#8)
    (hm : (FullMem c (resSt s0 lmn tmpn) ⋆ R) m) :
    ResStepInv c s0 rn.toNat tmpn exclude l R (rn, lmn, tmpn) m := by
  obtain ⟨j, hj, htj⟩ := (hrin.lm_iff l.toNat hl_lt).mp hnz
  exact ⟨hrin, Nat.le_refl _, fun _ _ => rfl, Or.inr (Or.inr ⟨j, hj, htj⟩), hm⟩

private theorem res_final_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {v rlen2 : BitVec 32} {skip2 : Bool}
    {lm_k : List (BitVec 8)} {tmp2 : List (BitVec 32)}
    (hdw0 : FullDenseInvW c F0 F_cur s0)
    (hrlen2_le : rlen2.toNat ≤ s0.core.cur_vars) (htmp2_len : tmp2.length = c.max_vars)
    (hlits_lt : ∀ k < rlen2.toNat, (tmp2[k]?.getD 0#32).toNat < 2 * s0.core.cur_vars)
    (hnodup : ((tmp2.take rlen2.toNat).map (fun x => x.toNat / 2)).Nodup)
    (hcv_le : s0.core.cur_vars ≤ c.max_vars) (hlmk : lm_k.length = 2 * c.max_vars)
    (hrem_lm : ∀ x < 2 * c.max_vars, lm_k[x]?.getD 0#8 ≠ 0#8 →
      ∃ j, rlen2.toNat ≤ j ∧ j < rlen2.toNat ∧ (tmp2[j]?.getD 0#32).toNat = x)
    (hboth_ent : skip2 = false →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((2 * v.toNat) :: (tmp2.take rlen2.toNat).map BitVec.toNat)) ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((2 * v.toNat + 1) :: (tmp2.take rlen2.toNat).map BitVec.toNat))) :
    let tl' := (rlen2.setWidth 64).toNat
    let s' := { s0 with core := { s0.core with tmp_len := tl', lit_mark := lm_k, tmp := tmp2 } }
    FullDenseInvW c F0 F_cur s' ∧ tl' ≤ s0.core.cur_vars ∧
    (!skip2 = true →
      (∀ i < tl', (tmp2[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
      ((tmp2.take tl').map (fun x => x.toNat / 2)).Nodup ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((tmp2.take tl').map BitVec.toNat))) := by
  have hlm_clr : ∀ x < 2 * c.max_vars, lm_k[x]?.getD 0#8 = 0#8 :=
    fun x hx => Classical.byContradiction fun hnz => by
      obtain ⟨j, hj1, hj2, _⟩ := hrem_lm x hx hnz; omega
  have hdw' := fullDenseInvW_with_tmp_lm hdw0 (tl' := (rlen2.setWidth 64).toNat)
    (by rw [elim_zext32_toNat]; omega) hlmk htmp2_len hlm_clr
  refine ⟨hdw', by rw [elim_zext32_toNat]; exact hrlen2_le, fun hnot => ?_⟩
  have hsk : skip2 = false := by revert hnot; cases skip2 <;> simp
  obtain ⟨hp_e, hn_e⟩ := hboth_ent hsk
  rw [elim_zext32_toNat]
  refine ⟨hlits_lt, hnodup, resolve_lits_entails hp_e ?_⟩
  have hx : (2 * v.toNat) ^^^ 1 = 2 * v.toNat + 1 := by
    have := fullInv_var_xor1 (2 * v.toNat); have := elim_xor1_mod2 (2 * v.toNat); omega
  rw [hx]; exact hn_e

/-! ## 2. `full_bve_resolve_pair_wp` -/

private theorem resUnmark_init {c : FullCfg} {s0 : FullState} {rlen : Nat}
    {lm : List (BitVec 8)} {tmp : List (BitVec 32)} (hri : ResInv c s0 rlen lm tmp) :
    lm.length = 2 * c.max_vars ∧ 0 ≤ rlen ∧ rlen = rlen - 0 ∧
    (∀ x < 2 * c.max_vars, lm[x]?.getD 0#8 ≠ 0#8 →
      ∃ j, 0 ≤ j ∧ j < rlen ∧ (tmp[j]?.getD 0#32).toNat = x) :=
  ⟨hri.lm_len, Nat.zero_le _, rfl, fun x hx hnz => by
    obtain ⟨j, hj, htj⟩ := (hri.lm_iff x hx).mp hnz; exact ⟨j, Nat.zero_le _, hj, htj⟩⟩

public theorem full_bve_resolve_pair_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullBveResolvePairSpec a m Q X →
      Func.wp Γ full_bve_resolve_pair_body a m Q X := by
  rintro ⟨h, v, pc, nc, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s0, R, rfl, hdw0, hv_lt, hpc_ok, hnc_ok, hm0, hQ⟩
  have hmx := c.hmaxv; have harc := c.harena; unfold dimacsBound at hmx harc
  have hcv_le := hdw0.1.core_ok.cur_vars_le; have hl0 := hdw0.2.2.2.2.2.1
  obtain ⟨hpl_eq, hnl_eq⟩ := elim_pl_nl_eq v (by omega)
  unfold Func.wp full_bve_resolve_pair_body; elim_steps_nogrp
  refine wp_join_state (ts := [i32, .bool]) (α := BitVec 32 × Bool × List (BitVec 8) ×
    List (BitVec 32)) (fun x => (x.1, x.2.1, ())) (ResSideInv c F_cur s0 (2 * v.toNat) R) ?_ ?_
  · rintro _ ⟨rlen1, skip1, lm1, tmp1⟩ mp ⟨hri1, hpc_ent, hmp⟩
    refine wp_join_state (ts := [i32, .bool]) (α := BitVec 32 × Bool × List (BitVec 8) ×
      List (BitVec 32)) (fun x => (x.1, x.2.1, ())) (ResBothInv c F_cur s0 v.toNat R)
      (fun _ ⟨rlen2, skip2, lm2, tmp2⟩ mq ⟨hri2, hboth_ent, hmq⟩ => by
        elim_steps_nogrp
        refine wp_loop_group (ts := [i32]) (fun rem (k, ()) mk => ∃ lm_k : List (BitVec 8),
          lm_k.length = 2 * c.max_vars ∧ k.toNat ≤ rlen2.toNat ∧ rem = rlen2.toNat - k.toNat ∧
          (∀ x < 2 * c.max_vars, lm_k[x]?.getD 0#8 ≠ 0#8 →
            ∃ j, k.toNat ≤ j ∧ j < rlen2.toNat ∧ (tmp2[j]?.getD 0#32).toNat = x) ∧
          (FullMem c (resSt s0 lm_k tmp2) ⋆ R) mk) ?_ ?_
        · rintro L rem ⟨k, ⟨⟩⟩ mk hL ⟨lm_k, hlmk, hk_le, hrem, hrem_lm, hmk⟩; elim_steps_nogrp
          · have hk_lt : k.toNat < rlen2.toNat := hc
            obtain ⟨hkt, hl_lm⟩ := resUnmark_idx_lt hri2 hcv_le hk_lt hlmk
            have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
            elim_steps!; exact hL (rlen2.toNat - (k + 1#32).toNat) (k + 1#32, ()) _ (by omega)
              ⟨lm_k.set ((tmp2[(k.setWidth 64).toNat]'hkt).setWidth 64).toNat 0#8, by simp [hlmk],
               by omega, rfl, hk1 ▸ resUnmark_step hkt hl_lm hrem_lm, hm⟩
          · have hk_eq : k.toNat = rlen2.toNat := by have := Nat.le_of_not_lt hc; omega
            have hrlen2_le : rlen2.toNat ≤ s0.core.cur_vars := hri2.rlen_le
            have hrlen2_64 : (rlen2.setWidth 64).toNat < 2 ^ 64 := by rw [elim_zext32_toNat]; omega
            elim_steps!
            obtain ⟨hdw', htl', hent'⟩ := res_final_post hdw0 hri2.rlen_le hri2.tmp_len
              hri2.lits_lt hri2.nodup_var hcv_le hlmk (hk_eq ▸ hrem_lm) hboth_ent
            exact hQ (!skip2) lm_k tmp2 (rlen2.setWidth 64).toNat _ hdw' htl' hent' hm
        · intro L hL; elim_steps!; obtain ⟨h1, h2, h3, h4⟩ := resUnmark_init hri2
          exact hL rlen2.toNat (0#32, ()) mq ⟨lm2, h1, h2, h3, h4, hmq⟩)
      (fun J2 hJ2 => by
        elim_steps_nogrp
        · elim_steps!
          simpa [hc] using hJ2 (rlen1, true, lm1, tmp1) mp ⟨hri1, fun h => Bool.noConfusion h, hmp⟩
        · obtain rfl : skip1 = false := by cases skip1 <;> simp_all
          have hpc1 := hpc_ent rfl
          refine wp_join_state (ts := [i32, .bool]) (α := BitVec 32 × Bool × List (BitVec 8) ×
            List (BitVec 32)) (fun x => (x.1, x.2.1, ())) (ResBothInv c F_cur s0 v.toNat R)
            (fun _ x mn hx => by elim_steps!; exact hJ2 x mn hx)
            (fun Jnc hJnc => by
              elim_steps_nogrp
              · have hnc_bin : (nc &&& 0x80000000#32) ≠ 0#32 := hc
                obtain ⟨hot_lt, _⟩ := bveEntry_entails_bin hnc_ok hnc_bin
                let ot := nc &&& 0x7FFFFFFF#32
                have hot_lt' : ot.toNat < 2 * s0.core.cur_vars := hot_lt
                have hot_val' : ot.toNat < s0.core.vals.length := by
                  rw [hdw0.1.core_ok.vals_len]; omega
                have hot_val : (ot.setWidth 64).toNat < s0.core.vals.length := by
                  rwa [elim_zext32_toNat]
                refine wp_join_state (ts := [i32, .bool])
                  (α := BitVec 32 × Bool × List (BitVec 8) × List (BitVec 32))
                  (fun x => (x.1, x.2.1, ())) (ResBothInv c F_cur s0 v.toNat R)
                  (fun _ x mn hx => by elim_steps!; exact hJnc x mn hx)
                  (fun Jnb hJnb => by
                    elim_steps_nogrp
                    · elim_steps!
                      exact hJnb (rlen1, true, lm1, tmp1) mp
                        ⟨hri1, fun h => Bool.noConfusion h, hmp⟩
                    · have hnotpos : (BitVec.ofNat 32 0).slt
                          ((s0.core.vals[ot.toNat]?.getD 0#8).signExtend 32) = false := by
                        rw [List.getElem?_eq_getElem hot_val', Option.getD_some]
                        simpa [ot, resSt, BitVec.toNat_and] using hc
                      have hot_x : ot.toNat ^^^ 1 < lm1.length := by
                        rw [hri1.lm_len]; have := fullInv_var_xor1 ot.toNat; omega
                      have hot_x64 : ((ot ^^^ 1#32).setWidth 64).toNat < lm1.length := by
                        rwa [elim_zext32_toNat, elim_bv32_xor1_toNat]
                      elim_steps_nogrp
                      · elim_steps!
                        exact hJnb (rlen1, true, lm1, tmp1) mp
                          ⟨hri1, fun h => Bool.noConfusion h, hmp⟩
                      · have hlm1_0 : lm1[ot.toNat ^^^ 1]?.getD 0#8 = 0#8 := zext32_eq0_of (by
                          rw [List.getElem?_eq_getElem hot_x, Option.getD_some]
                          simpa [ot, resSt, BitVec.toNat_and] using hc)
                        refine wp_join_state (ts := [i32])
                          (α := BitVec 32 × List (BitVec 8) × List (BitVec 32)) (fun x => (x.1, ()))
                          (ResStepInv c s0 rlen1.toNat tmp1 (2 * v.toNat + 1) ot R)
                          (fun _ ⟨rn, lmn, tmpn⟩ mn ⟨hrin, hle, hpre, hcov, hmn⟩ => by
                            elim_steps!
                            refine hJnb (rn, false, lmn, tmpn) mn ⟨hrin, fun _ => ?_, hmn⟩
                            have ht1 : rlen1.toNat ≤ tmp1.length := by
                              rw [hri1.tmp_len]; exact Nat.le_trans hri1.rlen_le hcv_le
                            have ht2 : rn.toNat ≤ tmpn.length := by
                              rw [hrin.tmp_len]; exact Nat.le_trans hrin.rlen_le hcv_le
                            exact ⟨resSide_pc_entails_mono hle ht1 ht2 hpre hpc1,
                              resSide_bin_entails hdw0 hnc_ok hnc_bin ht2 hcov⟩)
                          (fun Jn1 hJn1 => by
                            have hvdom := hdw0.2.1.vals_domain ot.toNat hot_lt
                            elim_steps_nogrp
                            · have h0 := res_vals_eq0 hvdom hnotpos (by
                                rw [List.getElem?_eq_getElem hot_val', Option.getD_some]
                                simpa [ot, resSt, BitVec.toNat_and] using hc)
                              have hot_lm : ot.toNat < lm1.length := by rw [hri1.lm_len]; omega
                              have hot_lm64 : (ot.setWidth 64).toNat < lm1.length := by
                                rwa [elim_zext32_toNat]
                              elim_steps_nogrp
                              · have hlm0 : lm1[ot.toNat]?.getD 0#8 = 0#8 := zext32_eq0_of (by
                                  rw [List.getElem?_eq_getElem hot_lm, Option.getD_some]
                                  simpa [ot, resSt, BitVec.toNat_and] using hc)
                                obtain ⟨_, htmpr1, _, _⟩ :=
                                  resInv_add hri1 hot_lt hcv_le h0 hlm0 hlm1_0
                                have hr1_tmp : (rlen1.setWidth 64).toNat < tmp1.length :=
                                  elim_zext32_toNat rlen1 ▸ htmpr1
                                elim_steps!; simp only [elim_zext32_toNat] at hm
                                have hm' := (resSt_stores2 s0 lm1 (lm1.set ot.toNat 1#8)
                                  tmp1 (tmp1.set rlen1.toNat ot)).symm ▸ hm
                                exact hJn1 (rlen1 + 1#32, lm1.set ot.toNat 1#8,
                                    tmp1.set rlen1.toNat ot) _
                                  (res_add_step_post hri1 hot_lt hcv_le h0 hlm0 hlm1_0 hm')
                              · have hlmnz : lm1[ot.toNat]?.getD 0#8 ≠ 0#8 := zext32_ne0_of (by
                                  rw [List.getElem?_eq_getElem hot_lm, Option.getD_some]
                                  simpa [ot, resSt, BitVec.toNat_and] using hc)
                                elim_steps!
                                exact hJn1 (rlen1, lm1, tmp1) _
                                  (res_dup_step_post hri1 (by omega) hlmnz hmp)
                            · have hneg := res_vals_neg hvdom hnotpos (by
                                rw [List.getElem?_eq_getElem hot_val', Option.getD_some]
                                simpa [ot, resSt, BitVec.toNat_and] using hc)
                              elim_steps!; exact hJn1 (rlen1, lm1, tmp1) _
                                ⟨hri1, Nat.le_refl _, fun _ _ => rfl, Or.inr (Or.inl hneg), hmp⟩))
              · -- `nc` large clause
                have hnc_bin : (nc &&& 0x80000000#32) = 0#32 := by simpa using hc
                obtain ⟨href_nc, hng_nc, hnc_end, hnc2_ar, hnsz_f⟩ :=
                  res_large_hdr hdw0 hnc_ok hnc_bin
                have hal_le := hdw0.1.core_ok.arena_len_le
                let nsz := s0.core.arena[(nc.setWidth 64 + 2#64).toNat]'hnc2_ar
                have hnsz_eq : nsz.toNat = fullArenaClauseSize s0 nc.toNat := hnsz_f hnc2_ar
                elim_steps_nogrp
                refine wp_loop_break_group (brkTs := [i32, .bool, i32]) (lpTs := [i32, i32])
                  (fun (rn, sn, _k, ()) mn => ∃ lmn tmpn,
                    ResInv c s0 rn.toNat lmn tmpn ∧ rlen1.toNat ≤ rn.toNat ∧
                    (∀ j < rlen1.toNat, tmpn[j]? = tmp1[j]?) ∧
                    (sn = false → (cnfOfClauses F_cur).EntailsClause (cnfClause
                      ((2 * v.toNat + 1) :: (tmpn.take rn.toNat).map BitVec.toNat))) ∧
                    (FullMem c (resSt s0 lmn tmpn) ⋆ R) mn)
                  (fun rem (rn, k, ()) mn => ∃ lmn tmpn,
                    ResInv c s0 rn.toNat lmn tmpn ∧ k.toNat ≤ nsz.toNat ∧
                    rem = nsz.toNat - k.toNat ∧ rlen1.toNat ≤ rn.toNat ∧
                    (∀ j < rlen1.toNat, tmpn[j]? = tmp1[j]?) ∧
                    (∀ idx < k.toNat, ResCovered s0 rn.toNat tmpn (2 * v.toNat + 1)
                      ((fullArenaClauseLits s0 nc.toNat)[idx]?.getD 0)) ∧
                    (FullMem c (resSt s0 lmn tmpn) ⋆ R) mn)
                  (fun _ ⟨rn, sn, _k, ⟨⟩⟩ mn ⟨lmn, tmpn, hrin, hle, hpre, hnc_e, hmn⟩ => by
                    elim_steps!
                    exact hJnc (rn, sn, lmn, tmpn) mn ⟨hrin, fun hsk => ⟨resSide_pc_entails_mono
                      hle (by rw [hri1.tmp_len]; exact Nat.le_trans hri1.rlen_le hcv_le)
                      (by rw [hrin.tmp_len]; exact Nat.le_trans hrin.rlen_le hcv_le) hpre hpc1,
                      hnc_e hsk⟩, hmn⟩)
                  (fun Bn Ln rem ⟨rn, k, ⟨⟩⟩ mn hBn hLn ⟨lmn, tmpn, hrin, hk_le, hrem, hle, hpre,
                      hcov, hmn⟩ => by
                    elim_steps_nogrp
                    · have hk_lt : k.toNat < nsz.toNat := hc
                      have hkar : (nc.setWidth 64 + 3#64 + k.setWidth 64).toNat <
                          s0.core.arena.length := by rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
                      elim_steps_nogrp
                      let l := s0.core.arena[(nc.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hkar
                      obtain ⟨hl_cl, hl_lt⟩ := resArena_lit_props hdw0 href_nc hng_nc
                        (by rw [← hnsz_eq]; exact hk_lt) hkar
                      have hl_lt' : l.toNat < 2 * s0.core.cur_vars := hl_lt
                      have hl_c0 : s0.core.arena[(nc.toNat + 3 + k.toNat) % 2 ^ 64]'(by
                          rw [resLarge_lit_c0 (c := c) (by omega)]; exact hkar) = l :=
                        elim_getElem_congr (resLarge_lit_c0 (c := c) (by omega)) _ hkar
                      have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                      refine wp_join_state (ts := [i32, .bool])
                        (α := BitVec 32 × Bool × List (BitVec 8) × List (BitVec 32))
                        (fun x => (x.1, x.2.1, ()))
                        (ResLitInv c s0 rn.toNat tmpn (2 * v.toNat + 1) l R)
                        (fun _ ⟨rn', _sn', lmn', tmpn'⟩ mx ⟨hrin', hler, hprer, hcovl, hmx⟩ => by
                          elim_steps!; refine hLn (nsz.toNat - (k + 1#32).toNat)
                            (rn', k + 1#32, ()) mx (by rw [hk1]; omega)
                            ⟨lmn', tmpn', hrin', by rw [hk1]; omega, rfl, le_trans hle hler,
                             fun j hj => (hprer j (by omega)).trans (hpre j hj),
                             fun idx hidx => res_cov_succ
                               (f := fun i => (fullArenaClauseLits s0 nc.toNat)[i]?.getD 0)
                               hler hprer hcov hl_cl hcovl (hk1 ▸ hidx), hmx⟩)
                        (fun Jc hJc => by
                          elim_steps_nogrp
                          · have hl_val' : l.toNat < s0.core.vals.length := by
                              rw [hdw0.1.core_ok.vals_len]; omega
                            have hl_val : (l.setWidth 64).toNat < s0.core.vals.length := by
                              rwa [elim_zext32_toNat]
                            elim_steps_nogrp
                            · elim_steps!; exact hBn (rn, true, k, ()) mn ⟨lmn, tmpn, hrin,
                                hle, hpre, fun h => Bool.noConfusion h, hmn⟩
                            · have hnotpos : (BitVec.ofNat 32 0).slt ((s0.core.vals[
                                  l.toNat]?.getD 0#8).signExtend 32) = false := by
                                rw [List.getElem?_eq_getElem hl_val', Option.getD_some]
                                simpa [resSt, hl_c0] using hc
                              have hl_lmx : l.toNat ^^^ 1 < lmn.length := by
                                rw [hrin.lm_len]; have := fullInv_var_xor1 l.toNat; omega
                              have hl_lmx64 : ((l ^^^ 1#32).setWidth 64).toNat < lmn.length := by
                                rwa [elim_zext32_toNat, elim_bv32_xor1_toNat]
                              elim_steps_nogrp
                              · elim_steps!; exact hBn (rn, true, k, ()) mn ⟨lmn, tmpn, hrin,
                                  hle, hpre, fun h => Bool.noConfusion h, hmn⟩
                              · have hlm1_0 : lmn[l.toNat ^^^ 1]?.getD 0#8 = 0#8 :=
                                  zext32_eq0_of (by
                                    rw [List.getElem?_eq_getElem hl_lmx, Option.getD_some]
                                    simpa [resSt, hl_c0] using hc)
                                refine wp_join_state (ts := [i32])
                                  (α := BitVec 32 × List (BitVec 8) × List (BitVec 32))
                                  (fun x => (x.1, ()))
                                  (ResStepInv c s0 rn.toNat tmpn (2 * v.toNat + 1) l R)
                                  (fun _ st mx (hst : ResStepInv c s0 rn.toNat tmpn
                                      (2 * v.toNat + 1) l R st mx) => by
                                    rcases st with ⟨rn', lmn', tmpn'⟩
                                    rcases hst with ⟨hrin', hler, hprer, hcovl, hmx⟩; elim_steps!
                                    exact hJc (rn', false, lmn', tmpn') mx
                                      (by refine ⟨hrin', hler, hprer, hcovl, hmx⟩))
                                  (fun Jd hJd => by
                                    have hvdom := hdw0.2.1.vals_domain l.toNat hl_lt
                                    elim_steps_nogrp
                                    · have h0 := res_vals_eq0 hvdom hnotpos (by
                                        rw [List.getElem?_eq_getElem hl_val', Option.getD_some]
                                        simpa [resSt, hl_c0] using hc)
                                      have hl_lm : l.toNat < lmn.length := by
                                        rw [hrin.lm_len]; omega
                                      have hl_lm64 : (l.setWidth 64).toNat < lmn.length := by
                                        rwa [elim_zext32_toNat]
                                      elim_steps_nogrp
                                      · have hlm0 : lmn[l.toNat]?.getD 0#8 = 0#8 :=
                                          zext32_eq0_of (by
                                            rw [List.getElem?_eq_getElem hl_lm, Option.getD_some]
                                            simpa [resSt, hl_c0] using hc)
                                        obtain ⟨_, htmprn, _, _⟩ :=
                                          resInv_add hrin hl_lt hcv_le h0 hlm0 hlm1_0
                                        have hrn_tmp : (rn.setWidth 64).toNat < tmpn.length :=
                                          elim_zext32_toNat rn ▸ htmprn
                                        elim_steps!; simp only [elim_zext32_toNat] at hm
                                        have hm' := (resSt_stores2 s0 lmn (lmn.set l.toNat 1#8)
                                          tmpn (tmpn.set rn.toNat l)).symm ▸ hm
                                        exact hJd (rn + 1#32, lmn.set l.toNat 1#8,
                                            tmpn.set rn.toNat l) _
                                          (res_add_step_post hrin hl_lt hcv_le h0 hlm0 hlm1_0 hm')
                                      · have hlmnz : lmn[l.toNat]?.getD 0#8 ≠ 0#8 :=
                                          zext32_ne0_of (by
                                            rw [List.getElem?_eq_getElem hl_lm, Option.getD_some]
                                            simpa [resSt, hl_c0] using hc)
                                        elim_steps!; exact hJd (rn, lmn, tmpn) _
                                          (res_dup_step_post hrin (by omega) hlmnz hmn)
                                    · have hneg := res_vals_neg hvdom hnotpos (by
                                        rw [List.getElem?_eq_getElem hl_val', Option.getD_some]
                                        simpa [resSt, hl_c0] using hc)
                                      elim_steps!; exact hJd (rn, lmn, tmpn) _ ⟨hrin, Nat.le_refl _,
                                        fun _ _ => rfl, Or.inr (Or.inl hneg), hmn⟩)
                          · have hl_eq : l.toNat = 2 * v.toNat + 1 := by
                              dsimp only [resSt] at hc
                              have h' := congrArg BitVec.toNat hc
                              simp only [show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                                hl_c0] at h'
                              simpa [hnl_eq] using h'
                            elim_steps!; exact hJc (rn, false, lmn, tmpn) mn
                              ⟨hrin, Nat.le_refl _, fun _ _ => rfl, Or.inl hl_eq, hmn⟩)
                    · dsimp only [resSt] at hc
                      have hk_eq := resLarge_exit_hk hnc2_ar hk_le hc
                      elim_steps!
                      exact hBn (rn, false, k, ()) mn ⟨lmn, tmpn, hrin, hle, hpre, fun _ =>
                        resSide_large_entails hdw0 hnc_ok hnc_bin
                          (by rw [hrin.tmp_len]; exact Nat.le_trans hrin.rlen_le hcv_le)
                          (fun idx hi => hcov idx (by rw [hk_eq, hnsz_eq]; exact hi)), hmn⟩)
                  (fun _ Ln _ hLn => by
                    elim_steps!; exact hLn nsz.toNat (rlen1, 0#32, ()) mp
                      ⟨lm1, tmp1, hri1, Nat.zero_le _, by simp, Nat.le_refl _, fun _ _ => rfl,
                       fun _ h => absurd h (Nat.not_lt_zero _), hmp⟩)))
  · intro J1 hJ1
    elim_steps_nogrp
    · have hpc_bin : (pc &&& 0x80000000#32) ≠ 0#32 := hc
      obtain ⟨hot_lt, _⟩ := bveEntry_entails_bin hpc_ok hpc_bin
      let ot := pc &&& 0x7FFFFFFF#32
      have hot_lt' : ot.toNat < 2 * s0.core.cur_vars := hot_lt
      have hot_val' : ot.toNat < s0.core.vals.length := by rw [hdw0.1.core_ok.vals_len]; omega
      have hot_val : (ot.setWidth 64).toNat < s0.core.vals.length := by rwa [elim_zext32_toNat]
      have hri0 := resInv_init hdw0
      refine wp_join_state (ts := [i32, .bool])
        (α := BitVec 32 × Bool × List (BitVec 8) × List (BitVec 32)) (fun x => (x.1, x.2.1, ()))
        (ResSideInv c F_cur s0 (2 * v.toNat) R) (fun _ x mp hx => by elim_steps!; exact hJ1 x mp hx)
        (fun Jpb hJpb => by
          elim_steps_nogrp
          · elim_steps!
            exact hJpb (0#32, true, s0.core.lit_mark, s0.core.tmp) m0
              ⟨hri0, fun h => Bool.noConfusion h, resSt_self s0 ▸ hm0⟩
          · refine wp_join_state (ts := [i32])
              (α := BitVec 32 × List (BitVec 8) × List (BitVec 32)) (fun x => (x.1, ()))
              (fun x mp => ResInv c s0 x.1.toNat x.2.1 x.2.2 ∧
                ResCovered s0 x.1.toNat x.2.2 (2 * v.toNat) ot.toNat ∧
                (FullMem c (resSt s0 x.2.1 x.2.2) ⋆ R) mp)
              (fun _ ⟨rp, lmp, tmpp⟩ mp ⟨hrip, hcov, hmp⟩ => by
                elim_steps!
                exact hJpb (rp, false, lmp, tmpp) mp ⟨hrip, fun _ =>
                  resSide_bin_entails hdw0 hpc_ok hpc_bin
                    (by rw [hrip.tmp_len]; exact Nat.le_trans hrip.rlen_le hcv_le) hcov, hmp⟩)
              (fun Jp1 hJp1 => by
                have hvdom := hdw0.2.1.vals_domain ot.toNat hot_lt
                have hnotpos : (BitVec.ofNat 32 0).slt
                    ((s0.core.vals[ot.toNat]?.getD 0#8).signExtend 32) = false := by
                  rw [List.getElem?_eq_getElem hot_val', Option.getD_some]
                  simpa [ot, BitVec.toNat_and] using hc
                elim_steps_nogrp
                · have h0 := res_vals_eq0 hvdom hnotpos (by
                    rw [List.getElem?_eq_getElem hot_val', Option.getD_some]
                    simpa [ot, BitVec.toNat_and] using hc)
                  have hlm0 : s0.core.lit_mark[ot.toNat]?.getD 0#8 = 0#8 :=
                    hdw0.2.2.1.2 ot.toNat (by omega)
                  have hlm1 : s0.core.lit_mark[ot.toNat ^^^ 1]?.getD 0#8 = 0#8 :=
                    hdw0.2.2.1.2 (ot.toNat ^^^ 1) (by have := fullInv_var_xor1 ot.toNat; omega)
                  obtain ⟨hrlt, htmpr, hlml, hri'⟩ := resInv_add hri0 hot_lt hcv_le h0 hlm0 hlm1
                  elim_steps!; simp only [elim_zext32_toNat] at hm
                  have hm' := (resSt_stores s0 (s0.core.lit_mark.set ot.toNat 1#8)
                    (s0.core.tmp.set 0 ot)).symm ▸ hm
                  have hri'' : ResInv c s0 (0#32 + 1#32).toNat
                      (s0.core.lit_mark.set ot.toNat 1#8) (s0.core.tmp.set 0 ot) := by
                    rw [show (0#32 + 1#32 : BitVec 32).toNat = 1 from rfl]; exact hri'
                  exact hJp1 (0#32 + 1#32, s0.core.lit_mark.set ot.toNat 1#8,
                      s0.core.tmp.set 0 ot) _
                    ⟨hri'', Or.inr (Or.inr ⟨0, by simp, by
                      rw [List.getElem?_set_self htmpr, Option.getD_some]⟩), hm'⟩
                · have hneg := res_vals_neg hvdom hnotpos (by
                    rw [List.getElem?_eq_getElem hot_val', Option.getD_some]
                    simpa [ot, BitVec.toNat_and] using hc)
                  elim_steps!; exact hJp1 (0#32, s0.core.lit_mark, s0.core.tmp) _
                    ⟨hri0, Or.inr (Or.inl hneg), resSt_self s0 ▸ hm0⟩))
    · -- `pc` large clause
      have hpc_bin : (pc &&& 0x80000000#32) = 0#32 := by simpa using hc
      obtain ⟨href_pc, hng_pc, hpc_end, hpc2_ar, hpsz_f⟩ := res_large_hdr hdw0 hpc_ok hpc_bin
      have hal_le := hdw0.1.core_ok.arena_len_le
      let psz := s0.core.arena[(pc.setWidth 64 + 2#64).toNat]'hpc2_ar
      have hpsz_eq : psz.toNat = fullArenaClauseSize s0 pc.toNat := hpsz_f hpc2_ar
      elim_steps_nogrp
      refine wp_loop_break_group (brkTs := [i32, .bool, i32]) (lpTs := [i32, i32])
        (fun (rp, sp, _k, ()) mp => ∃ lmp tmpp,
          ResInv c s0 rp.toNat lmp tmpp ∧
          (sp = false → (cnfOfClauses F_cur).EntailsClause
            (cnfClause ((2 * v.toNat) :: (tmpp.take rp.toNat).map BitVec.toNat))) ∧
          (FullMem c (resSt s0 lmp tmpp) ⋆ R) mp)
        (fun rem (rp, k, ()) mp => ∃ lmp tmpp,
          ResInv c s0 rp.toNat lmp tmpp ∧ k.toNat ≤ psz.toNat ∧ rem = psz.toNat - k.toNat ∧
          (∀ idx < k.toNat, ResCovered s0 rp.toNat tmpp (2 * v.toNat)
            ((fullArenaClauseLits s0 pc.toNat)[idx]?.getD 0)) ∧
          (FullMem c (resSt s0 lmp tmpp) ⋆ R) mp)
        (fun _ ⟨rp, sp, _k, ⟨⟩⟩ mp ⟨lmp, tmpp, hrip, hpc_e, hmp⟩ => by
          elim_steps!; exact hJ1 (rp, sp, lmp, tmpp) mp ⟨hrip, hpc_e, hmp⟩)
        (fun Bp Lp rem ⟨rp, k, ⟨⟩⟩ mp hBp hLp ⟨lmp, tmpp, hrip, hk_le, hrem, hcov, hmp⟩ => by
          elim_steps_nogrp
          · have hk_lt : k.toNat < psz.toNat := hc
            have hkar : (pc.setWidth 64 + 3#64 + k.setWidth 64).toNat < s0.core.arena.length := by
              rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
            elim_steps_nogrp
            let l := s0.core.arena[(pc.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hkar
            obtain ⟨hl_cl, hl_lt⟩ := resArena_lit_props hdw0 href_pc hng_pc
              (by rw [← hpsz_eq]; exact hk_lt) hkar
            have hl_lt' : l.toNat < 2 * s0.core.cur_vars := hl_lt
            have hl_c0 : s0.core.arena[(pc.toNat + 3 + k.toNat) % 2 ^ 64]'(by
                rw [resLarge_lit_c0 (c := c) (by omega)]; exact hkar) = l :=
              elim_getElem_congr (resLarge_lit_c0 (c := c) (by omega)) _ hkar
            have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
            refine wp_join_state (ts := [i32, .bool])
              (α := BitVec 32 × Bool × List (BitVec 8) × List (BitVec 32))
              (fun x => (x.1, x.2.1, ())) (ResLitInv c s0 rp.toNat tmpp (2 * v.toNat) l R)
              (fun _ ⟨rp', _sp', lmp', tmpp'⟩ mx ⟨hrip', hler, hprer, hcovl, hmx⟩ => by
                elim_steps!; refine hLp (psz.toNat - (k + 1#32).toNat) (rp', k + 1#32, ()) mx
                  (by rw [hk1]; omega) ⟨lmp', tmpp', hrip', by rw [hk1]; omega, rfl,
                    fun idx hidx => res_cov_succ (f := fun i =>
                      (fullArenaClauseLits s0 pc.toNat)[i]?.getD 0)
                      hler hprer hcov hl_cl hcovl (hk1 ▸ hidx), hmx⟩)
              (fun Jc hJc => by
                elim_steps_nogrp
                · have hl_val' : l.toNat < s0.core.vals.length := by
                    rw [hdw0.1.core_ok.vals_len]; omega
                  have hl_val : (l.setWidth 64).toNat < s0.core.vals.length := by
                    rwa [elim_zext32_toNat]
                  elim_steps_nogrp
                  · elim_steps!; exact hBp (rp, true, k, ()) mp ⟨lmp, tmpp, hrip,
                      fun h => Bool.noConfusion h, hmp⟩
                  · have hnotpos : (BitVec.ofNat 32 0).slt ((s0.core.vals[
                          l.toNat]?.getD 0#8).signExtend 32) = false := by
                      rw [List.getElem?_eq_getElem hl_val', Option.getD_some]
                      simpa [resSt, hl_c0] using hc
                    have hl_lmx : l.toNat ^^^ 1 < lmp.length := by
                      rw [hrip.lm_len]; have := fullInv_var_xor1 l.toNat; omega
                    have hl_lmx64 : ((l ^^^ 1#32).setWidth 64).toNat < lmp.length := by
                      rwa [elim_zext32_toNat, elim_bv32_xor1_toNat]
                    elim_steps_nogrp
                    · elim_steps!; exact hBp (rp, true, k, ()) mp ⟨lmp, tmpp, hrip,
                        fun h => Bool.noConfusion h, hmp⟩
                    · have hlm1_0 : lmp[l.toNat ^^^ 1]?.getD 0#8 = 0#8 := zext32_eq0_of (by
                        rw [List.getElem?_eq_getElem hl_lmx, Option.getD_some]
                        simpa [resSt, hl_c0] using hc)
                      refine wp_join_state (ts := [i32])
                        (α := BitVec 32 × List (BitVec 8) × List (BitVec 32))
                        (fun x => (x.1, ())) (ResStepInv c s0 rp.toNat tmpp (2 * v.toNat) l R)
                        (fun _ ⟨rp', lmp', tmpp'⟩ mx ⟨hrip', hler, hprer, hcovl, hmx⟩ => by
                          elim_steps!; exact hJc (rp', false, lmp', tmpp') mx
                            ⟨hrip', hler, hprer, hcovl, hmx⟩)
                        (fun Jd hJd => by
                          have hvdom := hdw0.2.1.vals_domain l.toNat hl_lt
                          elim_steps_nogrp
                          · have h0 := res_vals_eq0 hvdom hnotpos (by
                              rw [List.getElem?_eq_getElem hl_val', Option.getD_some]
                              simpa [resSt, hl_c0] using hc)
                            have hl_lm : l.toNat < lmp.length := by rw [hrip.lm_len]; omega
                            have hl_lm64 : (l.setWidth 64).toNat < lmp.length := by
                              rwa [elim_zext32_toNat]
                            elim_steps_nogrp
                            · have hlm0 : lmp[l.toNat]?.getD 0#8 = 0#8 := zext32_eq0_of (by
                                rw [List.getElem?_eq_getElem hl_lm, Option.getD_some]
                                simpa [resSt, hl_c0] using hc)
                              obtain ⟨_, htmprp, _, _⟩ :=
                                resInv_add hrip hl_lt hcv_le h0 hlm0 hlm1_0
                              have hrp_tmp : (rp.setWidth 64).toNat < tmpp.length :=
                                elim_zext32_toNat rp ▸ htmprp
                              elim_steps!; simp only [elim_zext32_toNat] at hm
                              have hm' := (resSt_stores2 s0 lmp (lmp.set l.toNat 1#8)
                                tmpp (tmpp.set rp.toNat l)).symm ▸ hm
                              exact hJd (rp + 1#32, lmp.set l.toNat 1#8, tmpp.set rp.toNat l) _
                                (res_add_step_post hrip hl_lt hcv_le h0 hlm0 hlm1_0 hm')
                            · have hlmnz : lmp[l.toNat]?.getD 0#8 ≠ 0#8 := zext32_ne0_of (by
                                rw [List.getElem?_eq_getElem hl_lm, Option.getD_some]
                                simpa [resSt, hl_c0] using hc)
                              elim_steps!; exact hJd (rp, lmp, tmpp) _
                                (res_dup_step_post hrip (by omega) hlmnz hmp)
                          · have hneg := res_vals_neg hvdom hnotpos (by
                              rw [List.getElem?_eq_getElem hl_val', Option.getD_some]
                              simpa [resSt, hl_c0] using hc)
                            elim_steps!; exact hJd (rp, lmp, tmpp) _ ⟨hrip, Nat.le_refl _,
                              fun _ _ => rfl, Or.inr (Or.inl hneg), hmp⟩)
                · have hl_eq : l.toNat = 2 * v.toNat := by
                    dsimp only [resSt] at hc
                    have h' := congrArg BitVec.toNat hc
                    simp only [show BitVec.toNat (3 : BitVec 64) = 3 from rfl, hl_c0] at h'
                    rwa [hpl_eq] at h'
                  elim_steps!; exact hJc (rp, false, lmp, tmpp) mp
                    ⟨hrip, Nat.le_refl _, fun _ _ => rfl, Or.inl hl_eq, hmp⟩)
          · have hk_eq := resLarge_exit_hk hpc2_ar hk_le hc
            elim_steps!
            exact hBp (rp, false, k, ()) mp ⟨lmp, tmpp, hrip, fun _ =>
              resSide_large_entails hdw0 hpc_ok hpc_bin
                (by rw [hrip.tmp_len]; exact Nat.le_trans hrip.rlen_le hcv_le)
                (fun idx hi => hcov idx (by rw [hk_eq, hpsz_eq]; exact hi)), hmp⟩)
        (fun _ Lp _ hLp => by
          elim_steps!; exact hLp psz.toNat (0#32, 0#32, ()) m0
            ⟨s0.core.lit_mark, s0.core.tmp, resInv_init hdw0, Nat.zero_le _, by simp,
             fun _ h => absurd h (Nat.not_lt_zero _), resSt_self s0 ▸ hm0⟩)

end LeanQbe.T.Examples.Kissat.Proof.Eliminate
