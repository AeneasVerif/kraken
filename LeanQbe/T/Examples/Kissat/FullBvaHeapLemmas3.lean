module

public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas2
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` 3-Hop BVA & Heap Factoring Proofs — Part 3 (`Filter Row`)

Proves the parametric `(Γ : Env)` `Func.wp` contract for `full_bva_filter_row`
(`full_bva_filter_row_wp` → `fullBvaFilterRowSpec`), maintaining `FilterArVivInv`,
`FullWitnessInv`, `FullArenaVarsNodup`, `BvaRowEntryOk`, and scratch-buffer framing across binary
and large clause filtering plus `PH_VIV` cleanup.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullBvaHeap

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullBvaHeapHelpers FullBvaHeapTactics FullBvaHeapScanHelpers
open scoped FullArenaTactics FullBvaHeapTactics

/-! ## 1. `FilterArVivInv` & Pure Row-Update Helpers -/

private theorem bva_bin_swap_entails {F_cur : List (List Nat)} {a b : Nat}
    (h : (cnfOfClauses F_cur).EntailsClause (cnfClause [a, b])) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [b, a]) :=
  clause_entails_of_perm (List.Perm.swap b a []) h

private theorem bv32_bin_flag_zero_of_lt {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    (x &&& 0x80000000#32) = 0#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x80000000#32).toNat = 2 ^ 31 from rfl,
    show (0#32).toNat = 0 from rfl]
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_two_pow]
  by_cases hk : k = 31
  · subst hk; simp [Nat.testBit_lt_two_pow h]
  · simp [Ne.symm hk]

/-- `PH_VIV` tracking invariant for `full_bva_filter_row` on `sb[nrow_off+lo ..< nrow_off+hi)`. -/
private def FilterArVivInv (c : FullCfg) (s : FullState) (ar sb : List (BitVec 32))
    (nrow_off lo hi : Nat) : Prop :=
  ar.length = c.arena_cap ∧ sb.length = c.scratch_cap ∧ hi ≤ 64 ∧
  (∀ nm, lo ≤ nm → nm < hi →
    let dr := sb[nrow_off + nm]?.getD 0#32
    (dr &&& 0x80000000#32) = 0#32 →
      dr.toNat ∈ fullArenaClauseRefsCore s.core ∧
      (s.core.arena[dr.toNat]?.getD 0#32 &&& 0x00100000#32) = 0#32) ∧
  ∀ i < c.arena_cap, ar[i]? = s.core.arena[i]? ∨
    (∃ nm, lo ≤ nm ∧ nm < hi ∧
      let dr := sb[nrow_off + nm]?.getD 0#32
      (dr &&& 0x80000000#32) = 0#32 ∧ dr.toNat = i ∧
      (s.core.arena[i]?.getD 0#32 &&& 0x00100000#32) = 0#32 ∧
      ar[i]? = some (s.core.arena[i]?.getD 0#32 ||| 0x00100000#32))

private theorem filterArVivInv_init {c : FullCfg} {s : FullState} (hslen : s.LengthsOk c)
    (nrow_off : Nat) : FilterArVivInv c s s.core.arena s.scratch.scratch_buf nrow_off 0 0 :=
  ⟨hslen.core_ok.arena_len_arr, hslen.scratch_ok.scratch_buf_len, Nat.zero_le _,
   fun _ _ h => by omega, fun _ _ => Or.inl rfl⟩

private theorem filterArVivInv_congr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {ar sb : List (BitVec 32)} {nrow_off lo hi : Nat}
    (h : FilterArVivInv c s ar sb nrow_off lo hi) :
    fullArenaClauseRefsCore { s.core with arena := ar } = fullArenaClauseRefsCore s.core ∧
    (∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore { s.core with arena := ar } r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseSizeCore { s.core with arena := ar } r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseLitsCore { s.core with arena := ar } r = fullArenaClauseLitsCore s.core r) :=
  arViv_congr hcl hw fun i hi => by
    rcases h.2.2.2.2 i hi with heq | ⟨nm, hlo, hhi, hbin, hidx, _, hset⟩
    · exact Or.inl heq
    · have href := (h.2.2.2.1 nm hlo hhi hbin).1
      rw [hidx] at href; exact Or.inr ⟨href, hset⟩

private theorem filter_row_ar_lits_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {ar sb : List (BitVec 32)} {nrow_off nqn : Nat}
    (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hviv : FilterArVivInv c s ar sb nrow_off 0 nqn)
    {r : Nat} (hr : r ∈ fullArenaClauseRefsCore s.core) :
    ∀ j < fullArenaClauseSizeCore s.core r, ar[r + 3 + j]? = s.core.arena[r + 3 + j]? := by
  intro j hj
  have hwf := hw.arena.refs_wf r hr; have hal := hcl.arena_len_le
  rcases hviv.2.2.2.2 (r + 3 + j) (by omega) with heq | ⟨nm, h0, hnm, h0b, hidx, _, _⟩
  · exact heq
  · exfalso
    have hnm_ref := (hviv.2.2.2.1 nm h0 hnm h0b).1
    rw [hidx] at hnm_ref
    have := fullArenaScanRefs_disjoint hr hnm_ref (by omega); omega

private theorem filterArVivInv_push_bin {c : FullCfg} {s : FullState} {ar sb : List (BitVec 32)}
    {nrow_off par_off nqn : Nat} (h : FilterArVivInv c s ar sb nrow_off 0 nqn)
    (hnqn : nqn < 64) (hdisj : nrow_off + 64 ≤ par_off) (hpar : par_off + 64 ≤ c.scratch_cap)
    {qw qi : BitVec 32} (hbin : (qw &&& 0x80000000#32) ≠ 0#32) :
    FilterArVivInv c s ar ((sb.set (nrow_off + nqn) qw).set (par_off + nqn) qi)
      nrow_off 0 (nqn + 1) := by
  obtain ⟨har, hsb, hhi, hdom, hall⟩ := h
  refine ⟨har, by simp [hsb], by omega, fun nm h0 hnm => ?_, fun i hi => ?_⟩
  · dsimp only; intro h0b
    by_cases hne : nm = nqn
    · subst hne
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
        Option.getD_some] at h0b
      exact absurd h0b hbin
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)] at h0b ⊢
      exact hdom nm h0 (by omega) h0b
  · rcases hall i hi with heq | ⟨nm, h0, hnm, h0b, hidx, h0v, hset⟩
    · exact Or.inl heq
    · refine Or.inr ⟨nm, h0, by omega, ?_, ?_, h0v, hset⟩
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact h0b
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hidx

private theorem filterArVivInv_push_large {c : FullCfg} {s : FullState} {ar sb : List (BitVec 32)}
    {nrow_off par_off nqn : Nat} (h : FilterArVivInv c s ar sb nrow_off 0 nqn)
    (hnqn : nqn < 64) (hdisj : nrow_off + 64 ≤ par_off) (hpar : par_off + 64 ≤ c.scratch_cap)
    {dr qi : BitVec 32} (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hdr_lt : dr.toNat < c.arena_cap) (hdr_bin : (dr &&& 0x80000000#32) = 0#32)
    (hdr_nviv : (ar[dr.toNat]'(by rw [h.1]; exact hdr_lt) &&& 0x00100000#32) = 0#32) :
    FilterArVivInv c s
      (ar.set dr.toNat ((ar[dr.toNat]'(by rw [h.1]; exact hdr_lt)) ||| 0x00100000#32))
      ((sb.set (nrow_off + nqn) dr).set (par_off + nqn) qi)
      nrow_off 0 (nqn + 1) := by
  obtain ⟨har, hsb, hhi, hdom, hall⟩ := h
  have horig : ar[dr.toNat]? = s.core.arena[dr.toNat]? := by
    rcases hall dr.toNat hdr_lt with heq | ⟨_, _, _, _, _, h0v, hset⟩
    · exact heq
    · rw [List.getElem?_eq_getElem (by omega)] at hset
      have hval := Option.some.inj hset
      have h1 : ((s.core.arena[dr.toNat]?.getD 0#32 ||| 0x00100000#32) &&& 0x00100000#32) =
          0x00100000#32 := by
        rw [BitVec.and_or_distrib_right,
          show (0x00100000#32 &&& 0x00100000#32) = 0x00100000#32 from rfl, h0v, BitVec.zero_or]
      rw [hval] at hdr_nviv
      exact absurd (hdr_nviv.symm.trans h1) (by decide)
  have hs_nviv : (s.core.arena[dr.toNat]?.getD 0#32 &&& 0x00100000#32) = 0#32 := by
    rw [← horig, List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hdr_nviv
  refine ⟨by simp [har], by simp [hsb], by omega, fun nm h0 hnm => ?_, fun i hi => ?_⟩
  · dsimp only; intro h0b
    by_cases hne : nm = nqn
    · subst hne
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
      exact ⟨hdr_ref, hs_nviv⟩
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)] at h0b ⊢
      exact hdom nm h0 (by omega) h0b
  · by_cases hid : i = dr.toNat
    · subst hid
      refine Or.inr ⟨nqn, Nat.zero_le _, by omega, ?_, ?_, hs_nviv, ?_⟩
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
        exact hdr_bin
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
      · rw [List.getElem?_set_self (by omega)]
        have har_eq : ar[dr.toNat]'(by omega) = s.core.arena[dr.toNat]?.getD 0#32 := by
          rw [← horig, List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [har_eq]
    · rw [List.getElem?_set_ne (Ne.symm hid)]
      rcases hall i hi with heq | ⟨nm, h0, hnm, h0b, hidx, h0v, hset⟩
      · exact Or.inl heq
      · refine Or.inr ⟨nm, h0, by omega, ?_, ?_, h0v, hset⟩
        · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact h0b
        · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hidx

private theorem filterArVivInv_clear_bin {c : FullCfg} {s : FullState} {ar sb : List (BitVec 32)}
    {nrow_off qi nqn : Nat} (h : FilterArVivInv c s ar sb nrow_off qi nqn) (hqi : qi < nqn)
    (hbin : (sb[nrow_off + qi]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32) :
    FilterArVivInv c s ar sb nrow_off (qi + 1) nqn := by
  obtain ⟨har, hsb, hhi, hdom, hall⟩ := h
  refine ⟨har, hsb, hhi, fun nm h1 h2 => hdom nm (by omega) h2, fun i hi => ?_⟩
  rcases hall i hi with heq | ⟨nm, h1, h2, h0b, hidx, h0v, hset⟩
  · exact Or.inl heq
  · have hne : nm ≠ qi := fun he => by subst he; exact hbin h0b
    exact Or.inr ⟨nm, by omega, h2, h0b, hidx, h0v, hset⟩

private theorem filterArVivInv_clear_large {c : FullCfg} {s : FullState} {ar sb : List (BitVec 32)}
    {nrow_off qi nqn : Nat} (hs_ar : s.core.arena.length = c.arena_cap)
    (h : FilterArVivInv c s ar sb nrow_off qi nqn) (hqi : qi < nqn)
    (hqr : nrow_off + qi < sb.length)
    (h0b : (sb[nrow_off + qi]'hqr &&& 0x80000000#32) = 0#32)
    (hdr_lt : (sb[nrow_off + qi]'hqr).toNat < c.arena_cap) :
    let dr := (sb[nrow_off + qi]'hqr).toNat
    FilterArVivInv c s
      (ar.set dr ((ar[dr]'(by rw [h.1]; exact hdr_lt)) &&& ~~~0x00100000#32))
      sb nrow_off (qi + 1) nqn := by
  obtain ⟨har, hsb, hhi, hdom, hall⟩ := h
  intro dr
  have hdr_eq : (sb[nrow_off + qi]?.getD 0#32).toNat = dr := by
    rw [List.getElem?_eq_getElem hqr, Option.getD_some]
  have h0b' : (sb[nrow_off + qi]?.getD 0#32 &&& 0x80000000#32) = 0#32 := by
    rw [List.getElem?_eq_getElem hqr, Option.getD_some]; exact h0b
  have hdr_s0 : (s.core.arena[dr]?.getD 0#32 &&& 0x00100000#32) = 0#32 := by
    have := (hdom qi (Nat.le_refl _) hqi h0b').2; rwa [hdr_eq] at this
  have har_clr : ((ar[dr]'(by omega)) &&& ~~~0x00100000#32) = s.core.arena[dr]?.getD 0#32 := by
    rcases hall dr hdr_lt with heq | ⟨_, _, _, _, _, _, hset⟩
    · have : ar[dr]'(by omega) = s.core.arena[dr]?.getD 0#32 := by
        rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [this]; exact bv32_clear_viv_of_zero hdr_s0
    · rw [List.getElem?_eq_getElem (by omega)] at hset
      rw [Option.some.inj hset]; exact bv32_viv_roundtrip hdr_s0
  refine ⟨by simp [har], hsb, hhi, fun nm h1 h2 => hdom nm (by omega) h2, fun i hi => ?_⟩
  by_cases hid : i = dr
  · subst hid; left
    rw [List.getElem?_set_self (by omega), har_clr,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  · rw [List.getElem?_set_ne (Ne.symm hid)]
    rcases hall i hi with heq | ⟨nm, h1, h2, hnb, hidx, h0v, hset⟩
    · exact Or.inl heq
    · have hne : nm ≠ qi := fun he => by subst he; rw [hdr_eq] at hidx; exact hid hidx.symm
      exact Or.inr ⟨nm, by omega, h2, hnb, hidx, h0v, hset⟩

private theorem filterArVivInv_done {c : FullCfg} {s : FullState} {ar sb : List (BitVec 32)}
    {nrow_off nqn : Nat} (hs_ar : s.core.arena.length = c.arena_cap)
    (h : FilterArVivInv c s ar sb nrow_off nqn nqn) : ar = s.core.arena := by
  apply list_eq_of_getElem?_eq (by rw [h.1, hs_ar])
  intro i hi
  rcases h.2.2.2.2 i (by omega) with heq | ⟨nm, h1, h2, _⟩
  · exact heq
  · omega

private theorem filter_row_bin_upd {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {ar sb : List (BitVec 32)}
    {row_off nrow_off par_off cur_qn nqn qi qw best_lit : BitVec 32}
    {res : List Nat} {step : Nat}
    (hsb_l : sb.length = c.scratch_cap)
    (hviv : FilterArVivInv c s ar sb nrow_off.toNat 0 nqn.toNat)
    (hnqn_lt : nqn.toNat < 64)
    (hnr_bd : nrow_off.toNat + 64 ≤ c.scratch_cap)
    (hpr_bd : par_off.toNat + 64 ≤ c.scratch_cap)
    (hdisj : nrow_off.toNat + 64 ≤ par_off.toNat)
    (hbin_ne : (qw &&& 0x80000000#32) ≠ 0#32)
    (hq_lt : (qw &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars)
    (hres_eq : res = [(qw &&& 0x7FFFFFFF#32).toNat])
    (hfr_q : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat,
        (qw &&& 0x7FFFFFFF#32).toNat]))
    (hbl_q_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [best_lit.toNat, (qw &&& 0x7FFFFFFF#32).toNat]))
    (hqi_lt : qi.toNat < cur_qn.toNat)
    (hres_lt : ∀ x ∈ res, x < 2 * s.core.cur_vars)
    (hres_nd : (res.map (· / 2)).Nodup)
    (hres_ent : ∀ t < step, (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res)))
    (hqw_getD : s.scratch.scratch_buf[row_off.toNat + qi.toNat]?.getD 0#32 = qw)
    (hfr_sb : ∀ idx < c.scratch_cap,
      ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 64) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 64) →
      sb[idx]? = s.scratch.scratch_buf[idx]?)
    (hent : ∀ nm < nqn.toNat,
      let pi := (sb[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧ ∃ res' : List Nat,
        (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
        BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
        BvaRowEntryOk F_cur s best_lit.toNat (sb[nrow_off.toNat + nm]?.getD 0#32) res' ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res'))) :
    let sb1 := (sb.set (nrow_off.toNat + nqn.toNat) qw).set (par_off.toNat + nqn.toNat) qi
    FilterArVivInv c s ar sb1 nrow_off.toNat 0 (nqn.toNat + 1) ∧
    (∀ idx < c.scratch_cap,
      ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 64) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 64) →
      sb1[idx]? = s.scratch.scratch_buf[idx]?) ∧
    (∀ nm < nqn.toNat + 1,
      let pi := (sb1[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧ ∃ res' : List Nat,
        (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
        BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
        BvaRowEntryOk F_cur s best_lit.toNat (sb1[nrow_off.toNat + nm]?.getD 0#32) res' ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res'))) := by
  let sb1 := (sb.set (nrow_off.toNat + nqn.toNat) qw).set (par_off.toNat + nqn.toNat) qi
  refine ⟨filterArVivInv_push_bin hviv hnqn_lt hdisj hpr_bd hbin_ne, ?_, ?_⟩
  · intro idx hidx hnot1 hnot2
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hfr_sb idx hidx hnot1 hnot2
  · intro nm hnm
    by_cases hne : nm = nqn.toNat
    · subst hne
      have hpi_eq : (sb1[par_off.toNat + nqn.toNat]?.getD 0#32).toNat = qi.toNat := by
        dsimp only [sb1]; rw [List.getElem?_set_self (by simp [hsb_l]; omega)]; rfl
      have hnr_eq : sb1[nrow_off.toNat + nqn.toNat]?.getD 0#32 = qw := by
        dsimp only [sb1]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
      refine ⟨by rw [hpi_eq]; exact hqi_lt, res, hres_lt, hres_nd, ?_, ?_, hres_ent, ?_⟩
      · rw [hpi_eq, hqw_getD]; unfold BvaRowEntryOk; rw [ite_eq_left hbin_ne]
        exact ⟨hq_lt, hres_eq, hfr_q⟩
      · rw [hnr_eq]; unfold BvaRowEntryOk; rw [ite_eq_left hbin_ne]
        exact ⟨hq_lt, hres_eq, hbl_q_ent⟩
      · rw [hres_eq]; exact hbl_q_ent
    · have hpi_eq : sb1[par_off.toNat + nm]? = sb[par_off.toNat + nm]? := by
        dsimp only [sb1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      have hnr_eq : sb1[nrow_off.toNat + nm]? = sb[nrow_off.toNat + nm]? := by
        dsimp only [sb1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      dsimp only; rw [hpi_eq, hnr_eq]; exact hent nm (by omega)

private theorem filter_row_mark_step {c : FullCfg} {s : FullState}
    {ar : List (BitVec 32)} {lmj : List (BitVec 8)} {qw j : BitVec 32}
    {res : List Nat} {step : Nat}
    (hlm_len : s.core.lit_mark.length = 2 * c.max_vars)
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hfr_b0 : (s.core.lit_mark[(s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat]?.getD 0#8 &&&
      1#8) ≠ 0#8)
    (hres_perm_f : res.Perm ((fullArenaClauseLitsCore s.core qw.toNat).filter
      (· != (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat)))
    (hlmj_inv : LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 j.toNat lmj)
    (hlmj_res : ∀ l < 2 * s.core.cur_vars, (lmj[l]?.getD 0#8 &&& 2#8) ≠ 0#8 → l ∈ res)
    (hqwj_ar : qw.toNat + 3 + j.toNat < ar.length)
    (hqwj_s : qw.toNat + 3 + j.toNat < s.core.arena.length)
    (hl_eq : ar[qw.toNat + 3 + j.toNat]'hqwj_ar = s.core.arena[qw.toNat + 3 + j.toNat]'hqwj_s)
    (hl_mem : (s.core.arena[qw.toNat + 3 + j.toNat]'hqwj_s).toNat ∈
      fullArenaClauseLitsCore s.core qw.toNat)
    (hl_lt : (ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat < 2 * s.core.cur_vars)
    (hb0_32 : (BitVec.setWidth 32 (lmj[(ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat]'(by
      rw [hlmj_inv.1]; omega)) &&& BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 1)) =
      BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0)) :
    let l := (ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat
    let lm1 := lmj.set l ((lmj[l]'(by rw [hlmj_inv.1]; omega)) ||| 2#8)
    LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 (j.toNat + 1) lm1 ∧
    (∀ x < 2 * s.core.cur_vars, (lm1[x]?.getD 0#8 &&& 2#8) ≠ 0#8 → x ∈ res) := by
  have hlmj_l := hlmj_inv.1
  have hl_b0_zero :
      (s.core.lit_mark[(ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat]?.getD 0#8 &&& 1#8) = 0#8 := by
    rw [← lmBit2Inv_preserves_bit0 hlmj_inv (by omega),
      List.getElem?_eq_getElem (by omega), Option.getD_some]
    apply BitVec.eq_of_toNat_eq
    have h0' := congrArg BitVec.toNat hb0_32
    simp only [BitVec.toNat_and, BitVec.toNat_setWidth,
      show (BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 1)).toNat = 1 from rfl,
      show (BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0)).toNat = 0 from rfl,
      show (1#8 : BitVec 8).toNat = 1 from rfl,
      show (0#8 : BitVec 8).toNat = 0 from rfl] at h0' ⊢
    have hlt8 := (lmj[(ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat]'(by omega)).isLt
    rwa [Nat.mod_eq_of_lt (Nat.lt_trans hlt8 (by decide))] at h0'
  have hl_ne_fr : (ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat ≠
      (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat := fun heq => by
    rw [heq] at hl_b0_zero; exact hfr_b0 hl_b0_zero
  have hl_in_res : (ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat ∈ res := by
    apply hres_perm_f.mem_iff.mpr; rw [List.mem_filter]
    exact ⟨by rw [hl_eq]; exact hl_mem, bne_iff_ne.mpr hl_ne_fr⟩
  have hl_lt_s : (s.core.arena[qw.toNat + 3 + j.toNat]'hqwj_s).toNat < 2 * c.max_vars := by
    rw [← hl_eq]; omega
  have hstep2 : LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 (j.toNat + 1)
      (lmj.set (ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat
        ((lmj[(ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat]'(by omega)) ||| 2#8)) := by
    have h0 := lmBit2Inv_or2 hlm_len hlmj_inv hqwj_s hl_lt_s
    simpa only [← hl_eq] using h0
  refine ⟨hstep2, fun x hx hne => ?_⟩
  by_cases hle : x = (ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat
  · rw [hle]; exact hl_in_res
  · rw [List.getElem?_set_ne (Ne.symm hle)] at hne; exact hlmj_res x hx hne

private theorem filter_row_large_upd {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {ar sb : List (BitVec 32)} {lmj : List (BitVec 8)}
    {row_off nrow_off par_off cur_qn nqn qi qw dr best_lit : BitVec 32}
    {res : List Nat} {step : Nat}
    (hcl : s.core.LengthsOk c) (har_l : ar.length = c.arena_cap)
    (hsb_l : sb.length = c.scratch_cap)
    (hw_ar : FullWitnessInv c F0 F_cur { s.core with arena := ar })
    (hnd_ar : FullArenaVarsNodup
      (FullState.mk { s.core with arena := ar } { s.scratch with scratch_buf := sb }))
    (hl0 : s.core.cur_level = 0)
    (hviv : FilterArVivInv c s ar sb nrow_off.toNat 0 nqn.toNat)
    (hnqn_lt : nqn.toNat < 64)
    (hnr_bd : nrow_off.toNat + 64 ≤ c.scratch_cap)
    (hpr_bd : par_off.toNat + 64 ≤ c.scratch_cap)
    (hdisj : nrow_off.toNat + 64 ≤ par_off.toNat)
    (hrefs_ar : fullArenaClauseRefsCore { s.core with arena := ar } =
      fullArenaClauseRefsCore s.core)
    (hqw_ref : qw.toNat ∈ fullArenaClauseRefsCore s.core)
    (hqw_ng : fullArenaClauseGarbCore s.core qw.toNat = false)
    (hqw_sz3 : 3 ≤ fullArenaClauseSizeCore s.core qw.toNat)
    (hqw_sz5 : fullArenaClauseSizeCore s.core qw.toNat ≤ 5)
    (hqw_sz_ar : fullArenaClauseSizeCore { s.core with arena := ar } qw.toNat =
      fullArenaClauseSizeCore s.core qw.toNat)
    (hfr_mem : (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat ∈
      fullArenaClauseLitsCore s.core qw.toNat)
    (hres_perm_f : res.Perm ((fullArenaClauseLitsCore s.core qw.toNat).filter
      (· != (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat)))
    (hqw_perm : (fullArenaClauseLits s qw.toNat).Perm
      ((s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat :: res))
    (hbin_eq : (qw &&& 0x80000000#32) = 0#32)
    (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hdr_lt_ar : dr.toNat + 3 ≤ ar.length)
    (hdr_ng_s : fullArenaClauseGarbCore { s.core with arena := ar } dr.toNat =
      fullArenaClauseGarbCore s.core dr.toNat)
    (hdr_sz_s : fullArenaClauseSizeCore { s.core with arena := ar } dr.toNat =
      fullArenaClauseSizeCore s.core dr.toNat)
    (hdr_lits_s : fullArenaClauseLitsCore { s.core with arena := ar } dr.toNat =
      fullArenaClauseLitsCore s.core dr.toNat)
    (hdr_ng_ar : fullArenaClauseGarb
      (FullState.mk { s.core with arena := ar, lit_mark := lmj }
        { s.scratch with scratch_buf := sb }) dr.toNat = false)
    (hdr_nviv_h : (fullArenaHdr
      (FullState.mk { s.core with arena := ar, lit_mark := lmj }
        { s.scratch with scratch_buf := sb }) dr.toNat &&& 0x00100000#32) = 0#32)
    (hdr_sz_eq_ar : fullArenaClauseSize
      (FullState.mk { s.core with arena := ar, lit_mark := lmj }
        { s.scratch with scratch_buf := sb }) dr.toNat =
      fullArenaClauseSize
      (FullState.mk { s.core with arena := ar, lit_mark := lmj }
        { s.scratch with scratch_buf := sb }) qw.toNat)
    (hbl_mem_ar : best_lit.toNat ∈ fullArenaClauseLits
      (FullState.mk { s.core with arena := ar, lit_mark := lmj }
        { s.scratch with scratch_buf := sb }) dr.toNat)
    (hdr_perm_ar : (fullArenaClauseLits
      (FullState.mk { s.core with arena := ar, lit_mark := lmj }
        { s.scratch with scratch_buf := sb }) dr.toNat).Perm (best_lit.toNat :: res))
    (hdr_filt_ar : ((fullArenaClauseLits
      (FullState.mk { s.core with arena := ar, lit_mark := lmj }
        { s.scratch with scratch_buf := sb }) dr.toNat).filter
      (· != best_lit.toNat)).Perm res)
    (hbl_res_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res)))
    (hqi_lt : qi.toNat < cur_qn.toNat)
    (hres_lt : ∀ x ∈ res, x < 2 * s.core.cur_vars)
    (hres_nd : (res.map (· / 2)).Nodup)
    (hres_ent : ∀ t < step, (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res)))
    (hqw_getD : s.scratch.scratch_buf[row_off.toNat + qi.toNat]?.getD 0#32 = qw)
    (hfr_sb : ∀ idx < c.scratch_cap,
      ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 64) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 64) →
      sb[idx]? = s.scratch.scratch_buf[idx]?)
    (hent : ∀ nm < nqn.toNat,
      let pi := (sb[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧ ∃ res' : List Nat,
        (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
        BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
        BvaRowEntryOk F_cur s best_lit.toNat (sb[nrow_off.toNat + nm]?.getD 0#32) res' ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res')))
    (hhar_b : c.arena_cap < 2 * dimacsBound) :
    let ar1 := ar.set dr.toNat ((ar[dr.toNat]'(by omega)) ||| 0x00100000#32)
    let sb1 := (sb.set (nrow_off.toNat + nqn.toNat) dr).set (par_off.toNat + nqn.toNat) qi
    FilterArVivInv c s ar1 sb1 nrow_off.toNat 0 (nqn.toNat + 1) ∧
    FullWitnessInv c F0 F_cur { s.core with arena := ar1 } ∧
    FullArenaVarsNodup
      (FullState.mk { s.core with arena := ar1 } { s.scratch with scratch_buf := sb1 }) ∧
    (∀ idx < c.scratch_cap,
      ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 64) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 64) →
      sb1[idx]? = s.scratch.scratch_buf[idx]?) ∧
    (∀ nm < nqn.toNat + 1,
      let pi := (sb1[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧ ∃ res' : List Nat,
        (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
        BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
        BvaRowEntryOk F_cur s best_lit.toNat (sb1[nrow_off.toNat + nm]?.getD 0#32) res' ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res'))) := by
  unfold dimacsBound at hhar_b
  have hcl_ar : ({ s.core with arena := ar }).LengthsOk c := { hcl with arena_len_arr := har_l }
  have hdr_nviv_ar : (ar[dr.toNat]'(by omega) &&& 0x00100000#32) = 0#32 := by
    change (fullArenaHdrCore { s.core with arena := ar } dr.toNat &&& 0x00100000#32) = 0#32
      at hdr_nviv_h
    unfold fullArenaHdrCore at hdr_nviv_h
    dsimp only at hdr_nviv_h
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdr_nviv_h
  have hdr_bin : (dr &&& 0x80000000#32) = 0#32 := bv32_bin_flag_zero_of_lt (by omega)
  let ar1 := ar.set dr.toNat ((ar[dr.toNat]'(by omega)) ||| 0x00100000#32)
  let sb1 := (sb.set (nrow_off.toNat + nqn.toNat) dr).set (par_off.toNat + nqn.toNat) qi
  have hviv1 : FilterArVivInv c s ar1 sb1 nrow_off.toNat 0 (nqn.toNat + 1) :=
    filterArVivInv_push_large hviv hnqn_lt (by omega) (by omega)
      hdr_ref (by omega) hdr_bin hdr_nviv_ar
  have hdr_ref_ar : dr.toNat ∈ fullArenaClauseRefsCore { s.core with arena := ar } := by
    rw [hrefs_ar]; exact hdr_ref
  have ⟨_, _, hw1, _⟩ := fullWitnessInv_set_hdr_bit20
    hcl_ar hw_ar hl0 hdr_ref_ar
    ((ar[dr.toNat]'(by omega)) ||| 0x00100000#32)
    (by unfold fullArenaHdrCore; dsimp only
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact bv32_or_viv_garb _)
    (by unfold fullArenaHdrCore; dsimp only
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact bv32_or_viv_shrk _)
  have hnd1 : FullArenaVarsNodup
      (FullState.mk { s.core with arena := ar1 } { s.scratch with scratch_buf := sb1 }) :=
    fullArenaVarsNodup_of_bit20
      (s := FullState.mk { s.core with arena := ar } { s.scratch with scratch_buf := sb1 })
      hcl_ar hw_ar hl0 hnd_ar hdr_ref_ar
      (by unfold fullArenaHdrCore; dsimp only
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact bv32_or_viv_garb _)
      (by unfold fullArenaHdrCore; dsimp only
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact bv32_or_viv_shrk _)
  refine ⟨hviv1, hw1, hnd1, ?_, ?_⟩
  · intro idx hidx hnot1 hnot2
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hfr_sb idx hidx hnot1 hnot2
  · intro nm hnm
    by_cases hne : nm = nqn.toNat
    · subst hne
      have hpi_eq : (sb1[par_off.toNat + nqn.toNat]?.getD 0#32).toNat = qi.toNat := by
        dsimp only [sb1]; rw [List.getElem?_set_self (by simp [hsb_l]; omega)]; rfl
      have hnr_eq : sb1[nrow_off.toNat + nqn.toNat]?.getD 0#32 = dr := by
        dsimp only [sb1]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
      refine ⟨by rw [hpi_eq]; exact hqi_lt, res, hres_lt, hres_nd, ?_, ?_, hres_ent, hbl_res_ent⟩
      · rw [hpi_eq, hqw_getD]; unfold BvaRowEntryOk
        rw [ite_eq_right (fun h' => h' hbin_eq)]
        exact ⟨hqw_ref, hqw_ng, hqw_sz3, hqw_sz5, hfr_mem, hres_perm_f, hqw_perm⟩
      · rw [hnr_eq]; unfold BvaRowEntryOk; rw [ite_eq_right (fun h' => h' hdr_bin)]
        change fullArenaClauseGarbCore { s.core with arena := ar } dr.toNat = false at hdr_ng_ar
        change fullArenaClauseSizeCore { s.core with arena := ar } dr.toNat =
          fullArenaClauseSizeCore { s.core with arena := ar } qw.toNat at hdr_sz_eq_ar
        change best_lit.toNat ∈ fullArenaClauseLitsCore { s.core with arena := ar } dr.toNat
          at hbl_mem_ar
        change (fullArenaClauseLitsCore { s.core with arena := ar } dr.toNat).Perm _ at hdr_perm_ar
        change ((fullArenaClauseLitsCore { s.core with arena := ar } dr.toNat).filter _).Perm _
          at hdr_filt_ar
        rw [hdr_ng_s] at hdr_ng_ar
        rw [hdr_sz_s, hqw_sz_ar] at hdr_sz_eq_ar
        rw [hdr_lits_s] at hbl_mem_ar hdr_perm_ar hdr_filt_ar
        unfold fullArenaClauseSize
        exact ⟨hdr_ref, hdr_ng_ar, by omega, by omega, hbl_mem_ar, hdr_filt_ar.symm, hdr_perm_ar⟩
    · have hpi_eq : sb1[par_off.toNat + nm]? = sb[par_off.toNat + nm]? := by
        dsimp only [sb1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      have hnr_eq : sb1[nrow_off.toNat + nm]? = sb[nrow_off.toNat + nm]? := by
        dsimp only [sb1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      dsimp only; rw [hpi_eq, hnr_eq]; exact hent nm (by omega)

private def eGrp0_2 {rs : List Ty} (J : Cont [i32, i32]) (xs : Tup Val [i32, i32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32]]) bs _ =>
    match bs (J, ()) with | .cons f .nil => f xs
  | _ => .hlt

private def eGrpBody_0 {rs : List Ty} (J : Cont []) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[]]) _ body => body (J, ()) | _ => .hlt

private def eGrpBody_1 {rs : List Ty} (J : Cont [i32]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32]]) _ body => body (J, ()) | _ => .hlt

private def filterRowMpExpr (h pWvec pWstk pAr pLm pScr : Val i64)
    (row_off nrow_off par_off cur_qn best_lit nqn qi qw csz min_l min_d j : Val i32)
    (J : Cont [i32, i32]) (Jend : Cont []) (Jbr : Cont [i32])
    (Jm : Cont [i32, i32, i32]) (Jm2 : Cont [i32]) : Expr Val Cont [i32] :=
  full_bva_filter_row_body Val Cont (h, row_off, nrow_off, par_off, cur_qn, best_lit, ())
    |> eSkip 1 |> eLoad64 pWvec
    |> eSkip 1 |> eLoad64 pWstk
    |> eSkip 1 |> eLoad64 pAr
    |> eSkip 1 |> eLoad64 pLm
    |> eSkip 1 |> eLoad64 pScr
    |> eGrp0_2 J (nqn, qi, ())
    |> eGrpBody_0 Jend
    |> eSkip 1 |> eThen
    |> eSkip 1 |> eThen
    |> eSkip 4 |> eLoad32 qw
    |> eGrpBody_1 Jbr
    |> eSkip 2 |> eElse
    |> eSkip 4 |> eLoad32 csz
    |> eGrp0_3 Jm (min_l, min_d, j, ())
    |> eSkip 1 |> eElse
    |> eGrpBody_1 Jm2

private theorem filter_row_mp_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    (hMatchLarge : ∀ args m Q X, fullBvaMatchLargeSpec args m Q X →
      Γ "full_bva_match_large" [i64, i32, i32, i32] [.bool] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {row_off nrow_off par_off cur_qn best_lit nqn qi qw csz min_l min_d j :
      Val i32}
    {J : Cont [i32, i32]} {Jend : Cont []} {Jbr : Cont [i32]}
    {Jm : Cont [i32, i32, i32]} {Jm2 : Cont [i32]}
    {ar sb : List (BitVec 32)} {lmj : List (BitVec 8)} {res : List Nat} {step : Nat} {mj : Mem 64}
    (hcl : s.core.LengthsOk c) (hsc : s.scratch.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hdw : DenseWatchesInv F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hdm : s.core.dense_mode ≠ 0#64)
    (hstep1 : 1 ≤ step) (hstep16 : step < 16)
    (_hrow_eq : row_off.toNat = 64 + (step - 1) * 64)
    (hnrow_eq : nrow_off.toNat = 64 + step * 64)
    (hpar_eq : par_off.toNat = 1088 + step * 64)
    (hscr2304 : 2304 ≤ c.scratch_cap)
    (har_l : ar.length = c.arena_cap) (hsb_l : sb.length = c.scratch_cap)
    (hlmj_l : lmj.length = 2 * c.max_vars)
    (hqi_lt : qi.toNat < cur_qn.toNat) (hnqn_lt : nqn.toNat < 64)
    (hw_ar : FullWitnessInv c F0 F_cur { s.core with arena := ar })
    (hnd_ar : FullArenaVarsNodup
      (FullState.mk { s.core with arena := ar } { s.scratch with scratch_buf := sb }))
    (hviv : FilterArVivInv c s ar sb nrow_off.toNat 0 nqn.toNat)
    (hqw_ref : qw.toNat ∈ fullArenaClauseRefsCore s.core)
    (hqw_ng : fullArenaClauseGarbCore s.core qw.toNat = false)
    (hqw_sz3 : 3 ≤ fullArenaClauseSize s qw.toNat)
    (hqw_sz5 : fullArenaClauseSize s qw.toNat ≤ 5)
    (hfr_mem : (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat ∈
      fullArenaClauseLits s qw.toNat)
    (hres_perm_f : res.Perm ((fullArenaClauseLits s qw.toNat).filter
      (· != (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat)))
    (hqw_perm : (fullArenaClauseLits s qw.toNat).Perm
      ((s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat :: res))
    (hbin_eq : (qw &&& 0x80000000#32) = 0#32)
    (hres_lt : ∀ x ∈ res, x < 2 * s.core.cur_vars)
    (hres_nd : (res.map (· / 2)).Nodup)
    (hres_ent : ∀ t < step, (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res)))
    (hqw_getD : s.scratch.scratch_buf[row_off.toNat + qi.toNat]?.getD 0#32 = qw)
    (hlmj_res : ∀ l < 2 * s.core.cur_vars, (lmj[l]?.getD 0#8 &&& 2#8) ≠ 0#8 → l ∈ res)
    (hmin_ok : min_l ≠ 0xFFFFFFFF#32 →
      min_l.toNat < 2 * s.core.cur_vars ∧ min_d.toNat = fullWatchSizeCore s.core min_l.toNat)
    (hfr_sb : ∀ idx < c.scratch_cap,
      ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 64) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 64) →
      sb[idx]? = s.scratch.scratch_buf[idx]?)
    (hent : ∀ nm < nqn.toNat,
      let pi := (sb[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧ ∃ res' : List Nat,
        (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
        BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
        BvaRowEntryOk F_cur s best_lit.toNat (sb[nrow_off.toNat + nm]?.getD 0#32) res' ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res')))
    (hmj : (FullMem c (FullState.mk { s.core with arena := ar, lit_mark := lmj }
      { s.scratch with scratch_buf := sb }) ⋆ R) mj)
    (hJm2 : ∀ nqn2 ar2 sb2 mf2,
      nqn2.toNat ≤ 64 → FilterArVivInv c s ar2 sb2 nrow_off.toNat 0 nqn2.toNat →
      FullWitnessInv c F0 F_cur { s.core with arena := ar2 } →
      FullArenaVarsNodup
        (FullState.mk { s.core with arena := ar2 } { s.scratch with scratch_buf := sb2 }) →
      (∀ idx < c.scratch_cap,
        ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 64) →
        ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 64) →
        sb2[idx]? = s.scratch.scratch_buf[idx]?) →
      (∀ nm < nqn2.toNat,
        let pi := (sb2[par_off.toNat + nm]?.getD 0#32).toNat
        pi < cur_qn.toNat ∧ ∃ res' : List Nat,
          (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
          BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
            (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
          BvaRowEntryOk F_cur s best_lit.toNat (sb2[nrow_off.toNat + nm]?.getD 0#32) res' ∧
          (∀ t < step, (cnfOfClauses F_cur).EntailsClause
            (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res'))) →
      (FullMem c (FullState.mk { s.core with arena := ar2, lit_mark := lmj }
        { s.scratch with scratch_buf := sb2 }) ⋆ R) mf2 →
      Jm2 (nqn2, ()) mf2) :
    wp Γ Q X (filterRowMpExpr c.hdr c.pWvec c.pWstk c.pArena c.pLitMark c.pScratchBuf
      row_off nrow_off par_off cur_qn best_lit nqn qi qw csz min_l min_d j J Jend Jbr Jm Jm2)
      mj := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr
  have har_len := hcl.arena_len_arr; have hal_le := hcl.arena_len_le; have hwlen_le := hcl.wlen_le
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  have hnqn1 : (nqn + 1#32).toNat = nqn.toNat + 1 := by simp only [bv_c0]; omega
  have hnrnq : (nrow_off + nqn).toNat = nrow_off.toNat + nqn.toNat := by simp only [bv_c0]; omega
  have hprnq : (par_off + nqn).toNat = par_off.toNat + nqn.toNat := by simp only [bv_c0]; omega
  have hnrnq_lt : (BitVec.setWidth 64 (nrow_off + nqn)).toNat < sb.length := by
    rw [hset, hnrnq, hsb_l]; omega
  have hprnq_lt : (BitVec.setWidth 64 (par_off + nqn)).toNat < sb.length := by
    rw [hset, hprnq, hsb_l]; omega
  have hqw_wf := hw.arena.refs_wf qw.toNat hqw_ref
  have ⟨hrefs_ar, hcl_ar⟩ := filterArVivInv_congr hcl hw hviv
  have ⟨hqw_ng_ar, hqw_sz_ar, _⟩ := hcl_ar qw.toNat hqw_ref
  dsimp only [filterRowMpExpr, eSkip, eLoad64, eLoad32, eGrp0_2, eGrpBody_0, eGrpBody_1,
    eGrp0_3, eThen, eElse, full_bva_filter_row_body]
  c0_hsplit
  · have hmin_ne : min_l ≠ 0xFFFFFFFF#32 := by assumption
    obtain ⟨hml_lt, hmd_eq⟩ := hmin_ok hmin_ne
    have hml_bd := hdw.layout.bounds min_l.toNat hml_lt
    have hml_sl := hdw.slices min_l.toNat hml_lt
    have h2ml_n : (BitVec.setWidth 64 min_l <<< (1 : Nat)).toNat = 2 * min_l.toNat := by
      simp only [bv_c0]; omega
    have h2ml_mod : 2 * min_l.toNat % 2 ^ 64 = 2 * min_l.toNat := Nat.mod_eq_of_lt (by omega)
    have h2ml_wv : (BitVec.setWidth 64 min_l <<< (1 : Nat)).toNat < s.core.wvec.length := by
      rw [h2ml_n]; omega
    have hmoff_eq : (s.core.wvec[2 * min_l.toNat]'(by omega)).toNat =
        fullWatchOffCore s.core min_l.toNat := by
      unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    let moff0 := fullWatchOffCore s.core min_l.toNat
    let msz0 := fullWatchSizeCore s.core min_l.toNat
    have hm_end_mod : ((s.core.wvec[2 * min_l.toNat % 2 ^ 64]'(by
        rw [h2ml_mod]; omega)).toNat + min_d.toNat) % 2 ^ 64 = moff0 + msz0 := by
      simp only [h2ml_mod, hmoff_eq, hmd_eq]; exact Nat.mod_eq_of_lt (by omega)
    c0_hsteps_nogrp
    refine wp_join_state
      (α := BitVec 32 × BitVec 64 × List (BitVec 32) × List (BitVec 32))
      (fun st => (st.1, st.2.1, ()))
      (fun ⟨nqn2, _mp2, ar2, sb2⟩ mf2 =>
        nqn2.toNat ≤ 64 ∧ FilterArVivInv c s ar2 sb2 nrow_off.toNat 0 nqn2.toNat ∧
        FullWitnessInv c F0 F_cur { s.core with arena := ar2 } ∧
        FullArenaVarsNodup
          (FullState.mk { s.core with arena := ar2 } { s.scratch with scratch_buf := sb2 }) ∧
        (∀ idx < c.scratch_cap,
          ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 64) →
          ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 64) →
          sb2[idx]? = s.scratch.scratch_buf[idx]?) ∧
        (∀ nm < nqn2.toNat,
          let pi := (sb2[par_off.toNat + nm]?.getD 0#32).toNat
          pi < cur_qn.toNat ∧ ∃ res' : List Nat,
            (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
            BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
              (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
            BvaRowEntryOk F_cur s best_lit.toNat (sb2[nrow_off.toNat + nm]?.getD 0#32) res' ∧
            (∀ t < step, (cnfOfClauses F_cur).EntailsClause
              (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
            (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res'))) ∧
        (FullMem c (FullState.mk { s.core with arena := ar2, lit_mark := lmj }
          { s.scratch with scratch_buf := sb2 }) ⋆ R) mf2)
      (fun _ ⟨nqn2, _mp2, ar2, sb2⟩ mf2 ⟨h1, h2, h3, h4, h5, h6, h7⟩ => by
        c0_hfast; exact hJm2 nqn2 ar2 sb2 mf2 h1 h2 h3 h4 h5 h6 h7)
      (fun Jmp hJmp => ?_)
    refine wp_loop_inv
      (fun (mp, ()) mmp =>
        moff0 ≤ mp.toNat ∧ mp.toNat ≤ moff0 + msz0 ∧ mmp = mj ∧
        DenseWatchSliceOk F_cur s.core min_l.toNat mp.toNat (moff0 + msz0 - mp.toNat))
      (fun (mp, ()) _ => moff0 + msz0 - mp.toNat)
      (fun JmpL hJmpL => by
        c0_hfast
        have h1 : (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 min_l <<<
            (1 : Nat)).toNat]'h2ml_wv)).toNat = moff0 := by
          simp only [h2ml_n, hset, hmoff_eq]; rfl
        dsimp only
        exact hJmpL (_, ()) mj ⟨by rw [h1]; exact Nat.le_refl _, by rw [h1]; omega, rfl,
          by simpa only [h1, Nat.add_sub_cancel_left] using hml_sl⟩)
      (fun JmpL (mp, ()) mmp ⟨hmp_ge, hmp_le, hmmp, hrem⟩ ihmp => ?_)
    rcases hmmp with rfl
    c0_hsplit
    · have hmp_lt : mp.toNat < moff0 + msz0 := by rw [← hm_end_mod]; assumption
      have hmp_ws : mp.toNat < s.core.wstk.length := by omega
      have hmp1_n : (mp + 1#64).toNat = mp.toNat + 1 := by simp only [bv_c0]; omega
      c0_hfast
      · -- Binary watch `mw`: `continue`
        have ⟨_, _, hrem_next⟩ :=
          FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hmp_ws (by assumption)
        exact ihmp (mp + 1#64, ()) mmp (by dsimp only; rw [hmp1_n]; omega)
          ⟨by rw [hmp1_n]; omega, by rw [hmp1_n]; omega, rfl,
           by rw [hmp1_n, show moff0 + msz0 - (mp.toNat + 1) =
                moff0 + msz0 - mp.toNat - 1 by omega]; exact hrem_next⟩
      · -- `mp >= mend`: `break`
        exact hJmp ⟨nqn, mp + 1#64, ar, sb⟩ mmp
          ⟨by omega, hviv, hw_ar, hnd_ar, hfr_sb, hent, hmj⟩
      · -- Large watch `dr = wstk[mp + 1]`
        have ⟨h2le, hrem_next⟩ :=
          FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hmp_ws (by assumption)
        have hmp1_ws : mp.toNat + 1 < s.core.wstk.length := by omega
        have hmp1_ws' : (mp + 1#64).toNat < s.core.wstk.length := by rw [hmp1_n]; exact hmp1_ws
        have hmp1_mod : (mp.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = mp.toNat + 1 := by
          rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
        have ⟨_, hdr_ref, _⟩ :=
          FullBvaFwdHelpers.fwd_slice_occ_info hrem (by omega) hmp_ws hmp1_ws (by assumption)
        have hdr_wf := hw.arena.refs_wf _ hdr_ref
        have hmp2_n : (mp + 1#64 + 1#64).toNat = mp.toNat + 2 := by simp only [bv_c0]; omega
        let dr := s.core.wstk[mp.toNat + 1]'hmp1_ws
        have hdr_lt_ar : dr.toNat + 3 ≤ ar.length := by
          dsimp only [dr]; have := hdr_wf.1; have := hcl.arena_len_le; omega
        have hdr_eq : s.core.wstk[(mp + 1#64).toNat]'hmp1_ws' = dr := by
          dsimp only [dr]; simp only [hmp1_n]
        have hdr_mod : s.core.wstk[(mp.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(
            by rw [hmp1_mod]; exact hmp1_ws) = dr := by dsimp only [dr]; simp only [hmp1_mod]
        -- `dr != qw`: call `full_bva_match_large(h, qw, best_lit, dr)`
        c0_call hMatchLarge
        have hres_nd_l : res.Nodup := nodup_of_map_div2 hres_nd
        have hqw_sz_res : fullArenaClauseSize
            (FullState.mk { s.core with arena := ar, lit_mark := lmj }
              { s.scratch with scratch_buf := sb }) qw.toNat = res.length + 1 := by
          change fullArenaClauseSizeCore { s.core with arena := ar } qw.toNat = _
          rw [hqw_sz_ar]
          have h1 := FullBvaFwdHelpers.fullArenaClauseLitsCore_length (k := s.core)
            (r := qw.toNat) (by have := hqw_wf.2.2.1; have := hqw_wf.2.2.2.1; omega)
          have h2 := hqw_perm.length_eq
          unfold fullArenaClauseLits at h2; simp only [List.length_cons] at h2; omega
        refine ⟨c, F0, F_cur,
          FullState.mk { s.core with arena := ar, lit_mark := lmj }
            { s.scratch with scratch_buf := sb }, R, res, rfl,
          ⟨{ hcl with arena_len_arr := har_l, lit_mark_len := hlmj_l },
           { hsc with scratch_buf_len := hsb_l }⟩,
          fullWitnessInv_with_litMark hw_ar lmj, hnd_ar, hl0, hdm,
          by change qw.toNat ∈ fullArenaClauseRefsCore { s.core with arena := ar }
             rw [hrefs_ar]; exact hqw_ref,
          by change fullArenaClauseGarbCore { s.core with arena := ar } qw.toNat = false
             rw [hqw_ng_ar]; exact hqw_ng,
          by show (s.core.wstk[(mp + 1#64).toNat]'hmp1_ws').toNat ∈ _
             rw [hdr_eq]
             change dr.toNat ∈ fullArenaClauseRefsCore { s.core with arena := ar }
             rw [hrefs_ar]; exact hdr_ref,
          hres_nd_l, hres_lt, hqw_sz_res, hlmj_res, hmj, fun ok hok => ?_⟩
        c0_hfast
        · -- `ok = true`: set `ar[dr] |= PH_VIV`, store `scr[nrow_off + nqn]`, break
          obtain ⟨hdr_ng_ar, hdr_nviv_h, hdr_sz_eq_ar, hbl_mem_ar, hdr_perm_ar,
            hdr_filt_ar, hbl_res_ent⟩ := hok (by assumption)
          have hdr_eq1 : s.core.wstk[(mp + (1 : BitVec 64)).toNat]'(by
              rw [show (1 : BitVec 64) = 1#64 from rfl, hmp1_n]; exact hmp1_ws) = dr := hdr_eq
          try rw [hdr_mod] at hdr_ng_ar hdr_nviv_h hdr_sz_eq_ar hbl_mem_ar
          try rw [hdr_mod] at hdr_perm_ar hdr_filt_ar
          try rw [hdr_eq1] at hdr_ng_ar hdr_nviv_h hdr_sz_eq_ar hbl_mem_ar
          try rw [hdr_eq1] at hdr_perm_ar hdr_filt_ar
          have ⟨hdr_ng_s, hdr_sz_s, hdr_lits_s⟩ := hcl_ar dr.toNat hdr_ref
          have hdr_ar_b : (BitVec.setWidth 64 (s.core.wstk[(mp.toNat +
              BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                rw [hmp1_mod]; exact hmp1_ws))).toNat < ar.length := by
            rw [hdr_mod, hset]; omega
          have hdr_ar_b' : (BitVec.setWidth 64 (s.core.wstk[(mp + 1#64).toNat]'(by
              rw [hmp1_n]; exact hmp1_ws))).toNat < ar.length := by
            rw [hdr_eq, hset]; omega
          c0_hfast
          have ⟨hviv1, hw1, hnd1, hfr1, hent1⟩ := filter_row_large_upd hcl har_l hsb_l
            hw_ar hnd_ar hl0 hviv hnqn_lt (by omega) (by omega) (by omega) hrefs_ar
            hqw_ref hqw_ng hqw_sz3 hqw_sz5 hqw_sz_ar hfr_mem hres_perm_f hqw_perm
            hbin_eq hdr_ref hdr_lt_ar hdr_ng_s hdr_sz_s hdr_lits_s hdr_ng_ar hdr_nviv_h
            hdr_sz_eq_ar hbl_mem_ar hdr_perm_ar hdr_filt_ar hbl_res_ent hqi_lt hres_lt
            hres_nd hres_ent hqw_getD hfr_sb hent c.harena
          let ar1 := ar.set dr.toNat ((ar[dr.toNat]'(by omega)) ||| 0x00100000#32)
          let sb1 := (sb.set (nrow_off.toNat + nqn.toNat) dr).set (par_off.toNat + nqn.toNat) qi
          have hm1 : (FullMem c (FullState.mk { s.core with arena := ar1, lit_mark := lmj }
              { s.scratch with scratch_buf := sb1 }) ⋆ R) m := by
            dsimp only [ar1, sb1]
            try simp only [hdr_eq1] at hm
            simp only [hset, hnrnq, hprnq] at hm; exact hm
          exact hJmp ⟨nqn + 1#32, mp + 1#64 + 1#64, _, _⟩ m
            ⟨by rw [hnqn1]; omega, by rw [hnqn1]; exact hviv1, hw1, hnd1, hfr1,
             by rw [hnqn1]; exact hent1, hm1⟩
        · -- `ok = false`: continue `mp` loop
          exact ihmp (mp + 1#64 + 1#64, ()) mmp (by dsimp only; rw [hmp2_n]; omega)
            ⟨by rw [hmp2_n]; omega, by rw [hmp2_n]; omega, rfl,
             by rw [hmp2_n, show moff0 + msz0 - (mp.toNat + 2) =
                  moff0 + msz0 - mp.toNat - 2 by omega]; exact hrem_next⟩
      · -- `dr == qw`: continue `mp` loop
        have ⟨h2le, hrem_next⟩ :=
          FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hmp_ws (by assumption)
        have hmp2_n : (mp + 1#64 + 1#64).toNat = mp.toNat + 2 := by simp only [bv_c0]; omega
        exact ihmp (mp + 1#64 + 1#64, ()) mmp (by dsimp only; rw [hmp2_n]; omega)
          ⟨by rw [hmp2_n]; omega, by rw [hmp2_n]; omega, rfl,
           by rw [hmp2_n, show moff0 + msz0 - (mp.toNat + 2) =
                moff0 + msz0 - mp.toNat - 2 by omega]; exact hrem_next⟩
    · c0_hfast
      exact hJmp ⟨nqn, mp, ar, sb⟩ mmp
        ⟨by omega, hviv, hw_ar, hnd_ar, hfr_sb, hent, hmj⟩
  · c0_hfast
    exact hJm2 nqn ar sb mj (by omega) hviv hw_ar hnd_ar hfr_sb hent hmj

/-! ## 2. `full_bva_filter_row_wp` -/

theorem full_bva_filter_row_wp (Γ : Env)
    (hMatchLarge : ∀ args m Q X, fullBvaMatchLargeSpec args m Q X →
      Γ "full_bva_match_large" [i64, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullBvaFilterRowSpec args m Q X →
      Func.wp Γ full_bva_filter_row_body args m Q X := by
  rintro ⟨h, row_off, nrow_off, par_off, cur_qn, best_lit, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, step, rfl, hslen, hw, hnodup, hext, hl0, hdm, hstep1, hstep16, hscr2304,
     hrow_eq, hnrow_eq, hpar_eq, hqn_eq, hbl_lt, hmat, hlm_clr, hlm_b0, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcl := hslen.core_ok; have hsc := hslen.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr
  have har_len := hcl.arena_len_arr; have hal_le := hcl.arena_len_le; have hwlen_le := hcl.wlen_le
  have hlm_len := hcl.lit_mark_len; have hsb_len := hsc.scratch_buf_len
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  have hdw : DenseWatchesInv F_cur s.core := by
    have h1 := hw.watches; unfold ModeWatchesInv at h1; rwa [ite_eq_right hdm] at h1
  have hrow_prev := hmat.2.2.2 (step - 1) (by omega)
  obtain ⟨hfr_lt, hqn_lo, hqn_hi, hrow_entries⟩ := hrow_prev
  rw [← hqn_eq] at hqn_lo hqn_hi hrow_entries
  rw [← hrow_eq] at hrow_entries
  have hfr_b0 :
      (s.core.lit_mark[(s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat]?.getD 0#8 &&& 1#8) ≠
      0#8 := hlm_b0 (step - 1) (by omega)
  let mkSt (ar : List (BitVec 32)) (lm : List (BitVec 8)) (sb : List (BitVec 32)) : FullState :=
    { core := { s.core with arena := ar, lit_mark := lm }
      scratch := { s.scratch with scratch_buf := sb } }
  let FilterEntryOk (sb : List (BitVec 32)) (nqn : Nat) : Prop :=
    ∀ nm < nqn,
      let pi := (sb[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧
      ∃ res : List Nat,
        (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
        BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res ∧
        BvaRowEntryOk F_cur s best_lit.toNat (sb[nrow_off.toNat + nm]?.getD 0#32) res ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res))
  let SbFrame (sb : List (BitVec 32)) : Prop :=
    ∀ idx < c.scratch_cap,
      ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 64) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 64) →
      sb[idx]? = s.scratch.scratch_buf[idx]?
  c0_hsteps
  refine wp_loop_inv
    (fun (nqn, qi, ()) ml => ∃ ar sb,
      qi.toNat ≤ cur_qn.toNat ∧ nqn.toNat ≤ 64 ∧
      FilterArVivInv c s ar sb nrow_off.toNat 0 nqn.toNat ∧
      FullWitnessInv c F0 F_cur { s.core with arena := ar } ∧
      FullArenaVarsNodup (mkSt ar s.core.lit_mark sb) ∧
      SbFrame sb ∧ FilterEntryOk sb nqn.toNat ∧
      (FullMem c (mkSt ar s.core.lit_mark sb) ⋆ R) ml)
    (fun (_, qi, _) _ => cur_qn.toNat - qi.toNat)
    (fun Jq hJq => by
      c0_hsteps
      exact hJq (0#32, 0#32, ()) m
        ⟨s.core.arena, s.scratch.scratch_buf, Nat.zero_le _, Nat.zero_le _,
         filterArVivInv_init hslen nrow_off.toNat, hw, hnodup,
         fun _ _ _ _ => rfl, fun _ h => by simp only [bv_c0] at h; omega, hm⟩)
    (fun Jq (nqn, qi, ()) ml ⟨ar, sb, hqi_le, hnqn_le, hviv, hw_ar, hnd_ar, hfr_sb, hent, hml⟩
        ihq => ?_)
  dsimp only [mkSt] at hml
  have har_l := hviv.1; have hsb_l := hviv.2.1
  c0_hsteps_nogrp
  -- Exit join point `Jend` inside loop body (from `while (qi < cur_qn && new_qn < 64u)`)
  refine wp_join_state0 (α := Unit)
    (fun _ mf => mf = ml)
    (fun _ _ mf hmf => ?_)
    (fun Jend hJend => ?_)
  · -- Cleanup loop `while (qi < new_qn) { dr = scr[nrow_off + qi]; if (large) ar[dr] &= ~VIV; }`
    rcases hmf with rfl
    refine wp_loop_inv
      (fun (ci, ()) mci => ∃ arci,
        ci.toNat ≤ nqn.toNat ∧
        FilterArVivInv c s arci sb nrow_off.toNat ci.toNat nqn.toNat ∧
        (FullMem c (mkSt arci s.core.lit_mark sb) ⋆ R) mci)
      (fun (ci, ()) _ => nqn.toNat - ci.toNat)
      (fun Jc hJc => by c0_hfast; exact hJc (0#32, ()) mf ⟨ar, Nat.zero_le _, hviv, hml⟩)
      (fun Jc (ci, ()) mci ⟨arci, hci_le, hviv_ci, hmci⟩ ihc => ?_)
    clear hm hml
    dsimp only [mkSt] at hmci
    have harci_l := hviv_ci.1
    c0_hsteps_nogrp
    · have hci_lt : ci.toNat < nqn.toNat := by assumption
      have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by simp only [bv_c0]; omega
      have hnrci : (nrow_off + ci).toNat = nrow_off.toNat + ci.toNat := by simp only [bv_c0]; omega
      let dr := sb[nrow_off.toNat + ci.toNat]'(by omega)
      have hdr_eq : sb[(BitVec.setWidth 64 (nrow_off + ci)).toNat]'(by
          rw [hset, hnrci]; omega) = dr := by dsimp only [dr]; simp only [hset, hnrci]
      c0_hstep; c0_hsplit
      · -- Large `dr`: clear `PH_VIV`
        have h0b : (dr &&& 0x80000000#32) = 0#32 := by
          have h1 : (sb[(BitVec.setWidth 64 (nrow_off + ci)).toNat]'(by
            rw [hset, hnrci]; omega) &&& 0x80000000#32) = 0#32 := by assumption
          rwa [hdr_eq] at h1
        have hdr_ref := (hviv_ci.2.2.2.1 ci.toNat (Nat.le_refl _) hci_lt (by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact h0b)).1
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdr_ref
        have hdr_wf := hw.arena.refs_wf _ hdr_ref
        have hstep := filterArVivInv_clear_large har_len hviv_ci hci_lt (by omega) h0b (by omega)
        have hdr_ar_b : (BitVec.setWidth 64 (sb[(BitVec.setWidth 64 (nrow_off + ci)).toNat]'(by
            rw [hset, hnrci]; omega))).toNat < arci.length := by
          rw [hdr_eq, hset]; dsimp only [dr]; have := hdr_wf.1; have := hcl.arena_len_le; omega
        c0_hfast
        refine ihc (ci + 1#32, ()) m (by dsimp only; rw [hci1]; omega)
          ⟨_, by rw [hci1]; omega, by rw [hci1]; exact hstep, ?_⟩
        simp only [hset, hnrci] at hm; exact hm
      · -- Binary `dr`: skip
        have hbin : (sb[nrow_off.toNat + ci.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have h1 : (sb[(BitVec.setWidth 64 (nrow_off + ci)).toNat]'(by
            rw [hset, hnrci]; omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
          rwa [hdr_eq] at h1
        c0_hfast
        exact ihc (ci + 1#32, ()) mci (by dsimp only; rw [hci1]; omega)
          ⟨arci, by rw [hci1]; omega,
           by rw [hci1]; exact filterArVivInv_clear_bin hviv_ci hci_lt hbin, hmci⟩
    · have hci_eq : ci.toNat = nqn.toNat := by omega
      rw [hci_eq] at hviv_ci
      have har_rest : arci = s.core.arena := filterArVivInv_done har_len hviv_ci
      rw [har_rest] at hmci
      exact hQ nqn sb mci ⟨hcl, { hsc with scratch_buf_len := hsb_l }⟩ hnqn_le hfr_sb hent hmci
  · -- Loop condition & body of `while (qi < cur_qn && new_qn < 64u)`
    c0_hsteps_nogrp
    · -- Both `qi < cur_qn` and `nqn < 64` hold
      have hqi_lt : qi.toNat < cur_qn.toNat := by assumption
      have hnqn_lt : nqn.toNat < 64 := by
        have h1 : nqn.toNat < (64 : BitVec 32).toNat := by assumption
        simpa using h1
      have hqi1 : (qi + 1#32).toNat = qi.toNat + 1 := by simp only [bv_c0]; omega
      have hrqi : (row_off + qi).toNat = row_off.toNat + qi.toNat := by simp only [bv_c0]; omega
      have hnrnq : (nrow_off + nqn).toNat = nrow_off.toNat + nqn.toNat := by
        simp only [bv_c0]; omega
      have hprnq : (par_off + nqn).toNat = par_off.toNat + nqn.toNat := by
        simp only [bv_c0]; omega
      have hnqn1 : (nqn + 1#32).toNat = nqn.toNat + 1 := by simp only [bv_c0]; omega
      have hqw_sb_eq : sb[row_off.toNat + qi.toNat]? =
          s.scratch.scratch_buf[row_off.toNat + qi.toNat]? :=
        hfr_sb (row_off.toNat + qi.toNat) (by omega) (by omega) (by omega)
      let qw := s.scratch.scratch_buf[row_off.toNat + qi.toNat]'(by omega)
      have hqw_eq : sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
          rw [hset, hrqi]; omega) = qw := by
        have h1 : sb[row_off.toNat + qi.toNat]? = some qw := by
          rw [hqw_sb_eq, List.getElem?_eq_getElem (by omega)]
        rw [List.getElem?_eq_getElem (by omega)] at h1
        have h2 := Option.some.inj h1; simpa only [hset, hrqi] using h2
      have hrqi_mod : (row_off.toNat + qi.toNat) % 2 ^ 32 = row_off.toNat + qi.toNat :=
        Nat.mod_eq_of_lt (by omega)
      have hqw_mod : sb[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by rw [hrqi_mod]; omega) = qw := by
        have h1 : sb[row_off.toNat + qi.toNat]? = some qw := by
          rw [hqw_sb_eq, List.getElem?_eq_getElem (by omega)]
        rw [List.getElem?_eq_getElem (by omega)] at h1
        have h2 := Option.some.inj h1; simpa only [hrqi_mod] using h2
      obtain ⟨res, hres_lt, hres_nd, hqw_ent, hres_ent, _⟩ := hrow_entries qi.toNat hqi_lt
      have hqw_getD : s.scratch.scratch_buf[row_off.toNat + qi.toNat]?.getD 0#32 = qw := by
        dsimp only [qw]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [hqw_getD] at hqw_ent
      -- Join point `Jbr` after `if ((qw & PW_BIN_FLAG) != 0) { ... } else { ... }`
      refine wp_join_state1 (t := i32)
        (α := BitVec 32 × List (BitVec 32) × List (BitVec 32)) (fun st => st.1)
        (fun ⟨nqn', ar', sb'⟩ mf =>
          nqn'.toNat ≤ 64 ∧ FilterArVivInv c s ar' sb' nrow_off.toNat 0 nqn'.toNat ∧
          FullWitnessInv c F0 F_cur { s.core with arena := ar' } ∧
          FullArenaVarsNodup (mkSt ar' s.core.lit_mark sb') ∧
          SbFrame sb' ∧ FilterEntryOk sb' nqn'.toNat ∧
          (FullMem c (mkSt ar' s.core.lit_mark sb') ⋆ R) mf)
        (fun _ ⟨nqn', ar', sb'⟩ mf ⟨hnqn', hviv', hw', hnd', hfr', hent', hmf⟩ => by
          c0_hfast
          exact ihq (nqn', qi + 1#32, ()) mf (by dsimp only; rw [hqi1]; omega)
            ⟨ar', sb', by rw [hqi1]; omega, hnqn', hviv', hw', hnd', hfr', hent', hmf⟩)
        (fun Jbr hJbr => ?_)
      c0_hsplit
      · -- Branch 1: binary `qw`
        have hbin_ne : (qw &&& 0x80000000#32) ≠ 0#32 := by
          have h1 : (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
            rw [hset, hrqi]; omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
          rwa [hqw_eq] at h1
        unfold BvaRowEntryOk at hqw_ent; rw [ite_eq_left hbin_ne] at hqw_ent
        obtain ⟨hq_lt0, hres_eq, hfr_q⟩ := hqw_ent
        let q := qw &&& 0x7FFFFFFF#32
        have hq_lt : q.toNat < 2 * s.core.cur_vars := hq_lt0
        have hq_eq : sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
            rw [hset, hrqi]; omega) &&& 0x7FFFFFFF#32 = q := by rw [hqw_eq]
        have hq_mod : sb[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by rw [hrqi_mod]; omega) &&&
            (2147483647 : BitVec 32) = q := by rw [hqw_mod]; rfl
        have h2q_mod : 2 * q.toNat % 2 ^ 64 = 2 * q.toNat := Nat.mod_eq_of_lt (by omega)
        have h2q_n : (BitVec.setWidth 64 q <<< (1 : Nat)).toNat = 2 * q.toNat := by c0_bound
        have h2q1_n : ((BitVec.setWidth 64 q <<< (1 : Nat)) + 1).toNat =
            2 * q.toNat + 1 := by
          change ((BitVec.setWidth 64 q <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
        have hq_bd := hdw.layout.bounds q.toNat hq_lt
        have hq_sl := hdw.slices q.toNat hq_lt
        have hoff_eq : (s.core.wvec[2 * q.toNat]'(by omega)).toNat =
            fullWatchOffCore s.core q.toNat := by
          unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        have hsz_eq : (s.core.wvec[2 * q.toNat + 1]'(by omega)).toNat =
            fullWatchSizeCore s.core q.toNat := by
          unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        let qoff0 := fullWatchOffCore s.core q.toNat
        let qsz0 := fullWatchSizeCore s.core q.toNat
        have h2q_wvec : (BitVec.setWidth 64 (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
            rw [hset, hrqi]; omega) &&& 0x7FFFFFFF#32) <<< (1 : Nat)).toNat <
            s.core.wvec.length := by rw [hq_eq, h2q_n]; omega
        have h2q1_wvec : ((BitVec.setWidth 64 (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
            rw [hset, hrqi]; omega) &&& 0x7FFFFFFF#32) <<< (1 : Nat)) + 1).toNat <
            s.core.wvec.length := by rw [hq_eq, h2q1_n]; omega
        c0_hsteps_nogrp
        refine wp_join_state
          (α := BitVec 32 × BitVec 64 × List (BitVec 32)) (fun st => (st.1, st.2.1, ()))
          (fun ⟨nqn', _qp', sb'⟩ mf =>
            nqn'.toNat ≤ 64 ∧ FilterArVivInv c s ar sb' nrow_off.toNat 0 nqn'.toNat ∧
            SbFrame sb' ∧ FilterEntryOk sb' nqn'.toNat ∧
            (FullMem c (mkSt ar s.core.lit_mark sb') ⋆ R) mf)
          (fun _ ⟨nqn', _qp', sb'⟩ mf ⟨hnqn', hviv', hfr', hent', hmf⟩ => by
            c0_hfast
            exact hJbr ⟨nqn', ar, sb'⟩ mf ⟨hnqn', hviv', hw_ar, hnd_ar, hfr', hent', hmf⟩)
          (fun Jqp hJqp => ?_)
        refine wp_loop_inv
          (fun (qp, ()) mlp =>
            qoff0 ≤ qp.toNat ∧ qp.toNat ≤ qoff0 + qsz0 ∧ mlp = ml ∧
            DenseWatchSliceOk F_cur s.core q.toNat qp.toNat (qoff0 + qsz0 - qp.toNat))
          (fun (qp, ()) _ => qoff0 + qsz0 - qp.toNat)
          (fun Jp hJp => by
            c0_hfast
            have h1 : (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64
                (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
                  rw [hset, hrqi]; omega) &&& (2147483647 : BitVec 32)) <<< (1 : Nat)).toNat]'(by
                rw [show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl, hq_eq, h2q_n]
                omega))).toNat = qoff0 := by
              simp only [show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl, hq_eq]
              simp only [h2q_n, hset, hoff_eq]; rfl
            dsimp only
            exact hJp (_, ()) ml ⟨by rw [h1]; exact Nat.le_refl _, by rw [h1]; omega, rfl,
              by simpa only [h1, Nat.add_sub_cancel_left] using hq_sl⟩)
          (fun Jp (qp, ()) mlp ⟨hqp_ge, hqp_le, hmlp, hrem⟩ ihp => ?_)
        rcases hmlp with rfl
        clear hm
        c0_hsplit
        · have hqp_lt : qp.toNat < qoff0 + qsz0 := by
            have hqend_mod : ((s.core.wvec[2 * q.toNat % 2 ^ 64]'(by rw [h2q_mod]; omega)).toNat +
                (s.core.wvec[(2 * q.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                  rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega)).toNat) % 2 ^ 64 =
                qoff0 + qsz0 := by
              simp only [h2q_mod, show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
                Nat.mod_eq_of_lt (by omega : 2 * q.toNat + 1 < 2 ^ 64), hoff_eq, hsz_eq]
              exact Nat.mod_eq_of_lt (by omega)
            rw [← hqend_mod]
            simpa only [← hq_mod] using (by assumption : _)
          have hqp_ws : qp.toNat < s.core.wstk.length := by omega
          have hqp1_n : (qp + 1#64).toNat = qp.toNat + 1 := by simp only [bv_c0]; omega
          c0_hfast
          · -- Binary watch `nw`, `(nw & 0x7FFFFFFF) == best_lit`: write `scr`, `break`
            have ⟨_, hq_bl_ent, _⟩ :=
              FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hqp_ws (by assumption)
            have hnw_bl : (s.core.wstk[qp.toNat]'hqp_ws &&& 0x7FFFFFFF#32) = best_lit := by
              assumption
            rw [hnw_bl] at hq_bl_ent
            have hbl_q_ent : (cnfOfClauses F_cur).EntailsClause
                (cnfClause [best_lit.toNat, q.toNat]) := bva_bin_swap_entails hq_bl_ent
            have ⟨hviv1, hfr1, hent1⟩ := filter_row_bin_upd hsb_l hviv hnqn_lt (by omega)
              (by omega) (by omega) hbin_ne hq_lt hres_eq hfr_q hbl_q_ent hqi_lt hres_lt hres_nd
              (fun t ht => hres_ent t (by omega)) hqw_getD hfr_sb hent
            let sb1 := (sb.set (nrow_off.toNat + nqn.toNat) qw).set (par_off.toNat + nqn.toNat) qi
            have hm1 : (FullMem c (mkSt ar s.core.lit_mark sb1) ⋆ R) m := by
              dsimp only [mkSt, sb1]
              simp only [hqw_eq] at hm; simp only [hset, hnrnq, hprnq] at hm; exact hm
            exact hJqp ⟨nqn + 1#32, qp, sb1⟩ m
              ⟨by rw [hnqn1]; omega, by rw [hnqn1]; exact hviv1, hfr1, by rw [hnqn1]; exact hent1,
               hm1⟩
          · -- Binary watch `nw`, `(nw & 0x7FFFFFFF) != best_lit`: skip 1 word
            have ⟨_, _, hrem_next⟩ :=
              FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hqp_ws (by assumption)
            exact ihp (qp + 1#64, ()) mlp (by dsimp only; rw [hqp1_n]; omega)
              ⟨by rw [hqp1_n]; omega, by rw [hqp1_n]; omega, rfl,
               by rw [hqp1_n, show qoff0 + qsz0 - (qp.toNat + 1) = qoff0 + qsz0 - qp.toNat - 1
                    by omega]; exact hrem_next⟩
          · -- Large watch `nw`: skip 2 words
            have ⟨h2le, hrem_next⟩ :=
              FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hqp_ws (by assumption)
            have hqp2_n : (qp + 2#64).toNat = qp.toNat + 2 := by simp only [bv_c0]; omega
            exact ihp (qp + 2#64, ()) mlp (by dsimp only; rw [hqp2_n]; omega)
              ⟨by rw [hqp2_n]; omega, by rw [hqp2_n]; omega, rfl,
               by rw [hqp2_n, show qoff0 + qsz0 - (qp.toNat + 2) = qoff0 + qsz0 - qp.toNat - 2
                    by omega]; exact hrem_next⟩
        · c0_hfast
          exact hJqp ⟨nqn, qp, sb⟩ mlp ⟨hnqn_le, hviv, hfr_sb, hent, hml⟩
      · -- Branch 2: large clause `qw`
        have hbin_eq : (qw &&& 0x80000000#32) = 0#32 := by
          have h1 : (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
            rw [hset, hrqi]; omega) &&& 0x80000000#32) = 0#32 := by assumption
          rwa [hqw_eq] at h1
        unfold BvaRowEntryOk at hqw_ent; rw [ite_eq_right (fun h' => h' hbin_eq)] at hqw_ent
        obtain ⟨hqw_ref, hqw_ng, hqw_sz3, hqw_sz5, hfr_mem, hres_perm_f, hqw_perm⟩ := hqw_ent
        have hqw_wf := hw.arena.refs_wf qw.toNat hqw_ref
        have ⟨hrefs_ar, hcl_ar⟩ := filterArVivInv_congr hcl hw hviv
        have ⟨hqw_ng_ar, hqw_sz_ar, hqw_lits_ar⟩ := hcl_ar qw.toNat hqw_ref
        have hqw2_lt : qw.toNat + 2 < ar.length := by have := hqw_wf.1; omega
        have hqw_sz_eq : (ar[qw.toNat + 2]'hqw2_lt).toNat =
            fullArenaClauseSizeCore s.core qw.toNat := by
          rw [← hqw_sz_ar]; unfold fullArenaClauseSizeCore
          rw [List.getElem?_eq_getElem hqw2_lt, Option.getD_some]
        let csz_bv := ar[qw.toNat + 2]'hqw2_lt
        have hcsz_nat : csz_bv.toNat = fullArenaClauseSizeCore s.core qw.toNat := hqw_sz_eq
        have hqw2_n : (BitVec.setWidth 64 qw + 2).toNat = qw.toNat + 2 := by
          change (BitVec.setWidth 64 qw + 2#64).toNat = _; simp only [bv_c0]; omega
        have hqw2_mod : (qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = qw.toNat + 2 := by
          rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
        have hcsz_mod : csz_bv = ar[(qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
            rw [hqw2_mod]; exact hqw2_lt) := by dsimp only [csz_bv]; simp only [hqw2_mod]
        have hqw2_ar : (BitVec.setWidth 64 (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
            rw [hset, hrqi]; omega)) + 2).toNat < ar.length := by
          rw [hqw_eq, hqw2_n, har_l]; have := hqw_wf.1; omega
        have hqw_lits_eq := filter_row_ar_lits_eq hcl hw hviv hqw_ref
        c0_hsteps_nogrp
        -- Marking loop `j < csz`: no `break`, sets bit 2 on literals with bit 0 = 0
        refine wp_loop_inv
          (fun (min_l, min_d, j, ()) mj => ∃ lmj,
            j.toNat ≤ csz_bv.toNat ∧
            LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 j.toNat lmj ∧
            (∀ l < 2 * s.core.cur_vars, (lmj[l]?.getD 0#8 &&& 2#8) ≠ 0#8 → l ∈ res) ∧
            (min_l ≠ 0xFFFFFFFF#32 →
              min_l.toNat < 2 * s.core.cur_vars ∧
              min_d.toNat = fullWatchSizeCore s.core min_l.toNat) ∧
            (FullMem c (mkSt ar lmj sb) ⋆ R) mj)
          (fun (_, _, j, _) _ => csz_bv.toNat - j.toNat)
          (fun Jm hJm => by
            c0_hfast
            refine hJm (0xFFFFFFFF#32, 0xFFFFFFFF#32, 0#32, ()) ml
              ⟨s.core.lit_mark, Nat.zero_le _, lmBit2Inv_init hlm_len, fun l hl hne => ?_,
               fun h => absurd rfl h, hml⟩
            exact absurd (bv8_bit_zero_of_and_fe (hlm_clr l (by omega))).1 hne)
          (fun Jm (min_l, min_d, j, ()) mj ⟨lmj, hj_le, hlmj_inv, hlmj_res, hmin_ok, hmj⟩ ihm => ?_)
        clear hm hml
        dsimp only [mkSt] at hmj
        have hlmj_l := hlmj_inv.1
        c0_hsplit
        · -- Marking loop body
          have hj_lt : j.toNat < csz_bv.toNat := by
            rw [hcsz_mod]
            simpa only [← hqw_mod] using (by assumption : _)
          have hj1 : (j + 1#32).toNat = j.toNat + 1 := by simp only [bv_c0]; omega
          have hqwj_n : (BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat =
              qw.toNat + 3 + j.toNat := by
            change (BitVec.setWidth 64 qw + 3#64 + BitVec.setWidth 64 j).toNat = _
            simp only [bv_c0]; omega
          have hqwj_mod : (qw.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64 =
              qw.toNat + 3 + j.toNat := by
            rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
          have hqwj_lt : qw.toNat + 3 + j.toNat < s.core.arena.length := by
            have := hqw_wf.2.2.1; have := hqw_wf.2.2.2.1; omega
          have hl_eq : ar[qw.toNat + 3 + j.toNat]'(by omega) =
              s.core.arena[qw.toNat + 3 + j.toNat]'hqwj_lt := by
            have h1 := hqw_lits_eq j.toNat (by omega)
            rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hqwj_lt] at h1
            exact Option.some.inj h1
          have hl_mem : (s.core.arena[qw.toNat + 3 + j.toNat]'hqwj_lt).toNat ∈
              fullArenaClauseLitsCore s.core qw.toNat :=
            List.mem_of_getElem? (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem
              (by omega) (by omega))
          have hl_lt : (ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
            rw [hl_eq]; exact hw.arena.lits_lt qw.toNat hqw_ref hqw_ng _ hl_mem
          have h2l1_n : ((BitVec.setWidth 64 (ar[qw.toNat + 3 + j.toNat]'(by omega)) <<<
              (1 : Nat)) + 1).toNat =
              2 * (ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat + 1 := by
            change ((BitVec.setWidth 64 _ <<< (1 : Nat)) + 1#64).toNat = _
            simp only [bv_c0]; omega
          have hw_get : (s.core.wvec[2 * (ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat + 1]'(by
              omega)).toNat =
              fullWatchSizeCore s.core (ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat := by
            unfold fullWatchSizeCore
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hqwj_ar : (BitVec.setWidth 64 (sb[(BitVec.setWidth 64
              (row_off + qi)).toNat]'(by rw [hset, hrqi]; omega)) + 3 +
              BitVec.setWidth 64 j).toNat < ar.length := by rw [hqw_eq, hqwj_n, har_l]; omega
          have hl_lm : (BitVec.setWidth 64 (ar[(BitVec.setWidth 64
              (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
                rw [hset, hrqi]; omega)) + 3 + BitVec.setWidth 64 j).toNat]'hqwj_ar)).toNat <
              lmj.length := by simp only [hqw_eq]; simp only [hqwj_n, hset]; omega
          have h2l1_wv : ((BitVec.setWidth 64 (ar[(BitVec.setWidth 64
              (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
                rw [hset, hrqi]; omega)) + 3 + BitVec.setWidth 64 j).toNat]'hqwj_ar) <<<
              (1 : Nat)) + 1).toNat < s.core.wvec.length := by
            simp only [hqw_eq]; simp only [hqwj_n, h2l1_n]; omega
          c0_hfast
          · -- `(lm[l] & 1) == 0`, `min_l == 0xFFFFFFFF`: update `min_l, min_d`
            have ⟨hstep2, hres_next⟩ := filter_row_mark_step hlm_len hcv_le hfr_b0 hres_perm_f
              hlmj_inv hlmj_res (by omega) hqwj_lt hl_eq hl_mem hl_lt (by
                simp only [← hqwj_mod]; simpa only [← hqw_mod] using (by assumption : _))
            dsimp only at hm ⊢
            simp only [hqw_eq] at hm; simp only [hqwj_n, hset] at hm
            try simp only [bv8_trunc_or_2] at hm
            try simp only [bv8_trunc_or_w] at hm
            refine ihm (_, _, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
              ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep2, hres_next, fun _ => ?_, hm⟩
            simp only [hqw_eq]; simp only [hqwj_n, h2l1_n]
            exact ⟨hl_lt, hw_get⟩
          · -- `(lm[l] & 1) == 0`, `d < min_d`: update `min_l, min_d`
            have ⟨hstep2, hres_next⟩ := filter_row_mark_step hlm_len hcv_le hfr_b0 hres_perm_f
              hlmj_inv hlmj_res (by omega) hqwj_lt hl_eq hl_mem hl_lt (by
                simp only [← hqwj_mod]; simpa only [← hqw_mod] using (by assumption : _))
            dsimp only at hm ⊢
            simp only [hqw_eq] at hm; simp only [hqwj_n, hset] at hm
            try simp only [bv8_trunc_or_2] at hm
            try simp only [bv8_trunc_or_w] at hm
            refine ihm (_, _, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
              ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep2, hres_next, fun _ => ?_, hm⟩
            simp only [hqw_eq]; simp only [hqwj_n, h2l1_n]
            exact ⟨hl_lt, hw_get⟩
          · -- `(lm[l] & 1) == 0`, keep `min_l, min_d`
            have ⟨hstep2, hres_next⟩ := filter_row_mark_step hlm_len hcv_le hfr_b0 hres_perm_f
              hlmj_inv hlmj_res (by omega) hqwj_lt hl_eq hl_mem hl_lt (by
                simp only [← hqwj_mod]; simpa only [← hqw_mod] using (by assumption : _))
            dsimp only at hm ⊢
            simp only [hqw_eq] at hm; simp only [hqwj_n, hset] at hm
            try simp only [bv8_trunc_or_2] at hm
            try simp only [bv8_trunc_or_w] at hm
            exact ihm (min_l, min_d, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
              ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep2, hres_next, hmin_ok, hm⟩
          · -- `(lm[l] & 1) != 0`: skip
            exact ihm (min_l, min_d, j + 1#32, ()) mj (by dsimp only; rw [hj1]; omega)
              ⟨lmj, by rw [hj1]; omega, by rw [hj1]; exact lmBit2Inv_skip hlmj_inv, hlmj_res,
               hmin_ok, hmj⟩
        · -- Exit marking loop: optional `if (min_l != 0xFFFFFFFF)`, then clear bit 2 on `qw`
          have hj_eq : j.toNat = csz_bv.toNat := by
            rw [hcsz_mod] at hj_le ⊢
            have h1 : ¬ j.toNat < (ar[(qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
              rw [hqw2_mod]; exact hqw2_lt)).toNat := by
              simpa only [← hqw_mod] using (by assumption : _)
            omega
          rw [hj_eq] at hlmj_inv
          c0_hsteps_nogrp
          refine wp_join_state1 (t := i32)
            (α := BitVec 32 × List (BitVec 32) × List (BitVec 32)) (fun st => st.1)
            (fun ⟨nqn2, ar2, sb2⟩ mf2 =>
              nqn2.toNat ≤ 64 ∧ FilterArVivInv c s ar2 sb2 nrow_off.toNat 0 nqn2.toNat ∧
              FullWitnessInv c F0 F_cur { s.core with arena := ar2 } ∧
              FullArenaVarsNodup (mkSt ar2 s.core.lit_mark sb2) ∧
              SbFrame sb2 ∧ FilterEntryOk sb2 nqn2.toNat ∧
              (FullMem c (mkSt ar2 lmj sb2) ⋆ R) mf2)
            (fun _ ⟨nqn2, ar2, sb2⟩ mf2 ⟨hnqn2, hviv2, hw2, hnd2, hfr2, hent2, hmf2⟩ => ?_)
            (fun Jm2 hJm2 => ?_)
          · -- Clear bit 2 on `qw`
            clear hmj hrow_entries hmat hlmj_res hmin_ok
            dsimp only [mkSt] at hmf2
            have har2_l := hviv2.1
            have har2_lits := filter_row_ar_lits_eq hcl hw hviv2 hqw_ref
            refine wp_loop_inv
              (fun (k, ()) mk => ∃ lmk,
                k.toNat ≤ csz_bv.toNat ∧
                LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat k.toNat csz_bv.toNat lmk ∧
                (FullMem c (mkSt ar2 lmk sb2) ⋆ R) mk)
              (fun (k, ()) _ => csz_bv.toNat - k.toNat)
              (fun Jc2 hJc2 => by
                c0_hfast; exact hJc2 (0#32, ()) mf2 ⟨lmj, Nat.zero_le _, hlmj_inv, hmf2⟩)
              (fun Jc2 (k, ()) mk ⟨lmk, hk_le, hlmk_inv, hmk⟩ ihc2 => ?_)
            clear hmf2
            dsimp only [mkSt] at hmk
            have hlmk_l := hlmk_inv.1
            c0_hsplit
            · have hk_lt : k.toNat < csz_bv.toNat := by
                rw [hcsz_mod]
                simpa only [← hqw_mod] using (by assumption : _)
              have hqwk_lt : qw.toNat + 3 + k.toNat < s.core.arena.length := by
                have := hqw_wf.2.2.1; have := hqw_wf.2.2.2.1; omega
              have hck_eq : ar2[qw.toNat + 3 + k.toNat]'(by omega) =
                  s.core.arena[qw.toNat + 3 + k.toNat]'hqwk_lt := by
                have h1 := har2_lits k.toNat (by omega)
                rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hqwk_lt] at h1
                exact Option.some.inj h1
              have hck_lt : (s.core.arena[qw.toNat + 3 + k.toNat]'hqwk_lt).toNat <
                  2 * s.core.cur_vars :=
                hw.arena.lits_lt qw.toNat hqw_ref hqw_ng _ (List.mem_of_getElem?
                  (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (by omega) (by omega)))
              have hk1 : (k + 1#32).toNat = k.toNat + 1 := by simp only [bv_c0]; omega
              have hidx_n : (BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 k).toNat =
                  qw.toNat + 3 + k.toNat := by
                change (BitVec.setWidth 64 qw + 3#64 + BitVec.setWidth 64 k).toNat = _
                simp only [bv_c0]; omega
              have hidx_ar : (BitVec.setWidth 64 (sb[(BitVec.setWidth 64
                  (row_off + qi)).toNat]'(by rw [hset, hrqi]; omega)) + 3 +
                  BitVec.setWidth 64 k).toNat < ar2.length := by rw [hqw_eq, hidx_n, har2_l]; omega
              have hck_lm : (BitVec.setWidth 64 (ar2[(BitVec.setWidth 64
                  (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
                    rw [hset, hrqi]; omega)) + 3 + BitVec.setWidth 64 k).toNat]'hidx_ar)).toNat <
                  lmk.length := by simp only [hqw_eq]; simp only [hidx_n, hset, hck_eq]; omega
              c0_hfast
              simp only [hqw_eq] at hm; simp only [hidx_n, hset] at hm
              try simp only [bv8_trunc_and_fd] at hm
              try simp only [bv8_trunc_and_w] at hm
              have hstep : LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat (k.toNat + 1)
                  csz_bv.toNat (lmk.set (ar2[qw.toNat + 3 + k.toNat]'(by omega)).toNat
                    ((lmk[(ar2[qw.toNat + 3 + k.toNat]'(by omega)).toNat]'(by
                      rw [hck_eq]; omega)) &&& 0xFD#8)) := by
                have h0 := lmBit2Inv_clear_step hlm_len
                  (fun l hl => (bv8_bit_zero_of_and_fe (hlm_clr l hl)).1)
                  hlmk_inv hk_lt hqwk_lt (by omega)
                simpa only [← hck_eq] using h0
              exact ihc2 (k + 1#32, ()) m (by dsimp only; rw [hk1]; omega)
                ⟨_, by rw [hk1]; omega, by rw [hk1]; exact hstep, hm⟩
            · have hk_eq : k.toNat = csz_bv.toNat := by
                rw [hcsz_mod] at hk_le ⊢
                have h1 : ¬ k.toNat < (ar[(qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                  rw [hqw2_mod]; exact hqw2_lt)).toNat := by
                  simpa only [← hqw_mod] using (by assumption : _)
                omega
              rw [hk_eq] at hlmk_inv
              have hlm_rest : lmk = s.core.lit_mark := lmBit2Inv_done hlm_len hlmk_inv
              rw [hlm_rest] at hmk
              c0_hfast
              exact hJbr ⟨nqn2, ar2, sb2⟩ mk ⟨hnqn2, hviv2, hw2, hnd2, hfr2, hent2, hmk⟩
          · -- `if (min_l != 0xFFFFFFFF)` (delegated to `filter_row_mp_wp`)
            clear hrow_entries hmat hlm_b0 hlm_clr hqw_lits_eq hqw_lits_ar
            dsimp only
            simp only [hqw_eq]
            have hmp := filter_row_mp_wp (Γ := Γ) (Q := Q) (X := X) hMatchLarge
              (J := Jq) (Jend := Jend) (Jbr := Jbr) (Jm := Jm) (Jm2 := Jm2)
              (csz := csz_bv) (j := j)
              hcl hsc hw hdw hl0 hdm hstep1 hstep16 hrow_eq hnrow_eq hpar_eq hscr2304
              har_l hsb_l hlmj_l hqi_lt hnqn_lt hw_ar hnd_ar hviv hqw_ref hqw_ng hqw_sz3 hqw_sz5
              hfr_mem hres_perm_f hqw_perm hbin_eq hres_lt hres_nd
              (fun t ht => hres_ent t (by omega)) hqw_getD hlmj_res hmin_ok hfr_sb hent hmj
              (fun nqn2 ar2 sb2 mf2 h1 h2 h3 h4 h5 h6 h7 =>
                hJm2 ⟨nqn2, ar2, sb2⟩ mf2 ⟨h1, h2, h3, h4, h5, h6, h7⟩)
            dsimp only [filterRowMpExpr, eSkip, eLoad64, eLoad32, eGrp0_2, eGrpBody_0, eGrpBody_1,
              eGrp0_3, eThen, eElse, full_bva_filter_row_body] at hmp
            exact hmp
    · exact hJend () ml rfl
    · exact hJend () ml rfl

end LeanQbe.T.Examples.Kissat.FullBvaHeap
