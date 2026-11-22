module

public import LeanQbe.T.Examples.Kissat.FullM4BvaLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` M4d BVA Proofs — Part 2 (`Filter Row & Multi-Step Try Lit`)

Proves parametric `(Γ : Env)` `Func.wp` contracts for:
1. `FullM4Bva.full_bva_filter_row_body` (`m4_bva_filter_row_wp` → `m4BvaFilterRowSpec`) for the
   `256 × 32` (`16448`-word) matrix and wide clause size bound `sz ∈ [3..256]`.
2. `FullM4Bva.full_bva_try_lit_body` (`m4_bva_try_lit_wp` → `fullBvaTryLitHeapSpec`) with lifted
   row capacity (`qn < 256`), depth (`step < 32`), wide clauses (`sz ≤ 256`), and decoupled
   reduction acceptance (`red > best_red`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4Bva

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapTactics
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapScanHelpers
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullBvaHeapTactics

/-! ## 1. `M4FilterArVivInv` & Pure Row-Update Helpers -/

theorem bv32_bin_flag_zero_of_lt {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
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
private def M4FilterArVivInv (c : FullCfg) (s : FullState) (ar sb : List (BitVec 32))
    (nrow_off lo hi : Nat) : Prop :=
  ar.length = c.arena_cap ∧ sb.length = c.scratch_cap ∧ hi ≤ 256 ∧
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

private theorem m4FilterArVivInv_init {c : FullCfg} {s : FullState} (hslen : s.LengthsOk c)
    (nrow_off : Nat) : M4FilterArVivInv c s s.core.arena s.scratch.scratch_buf nrow_off 0 0 :=
  ⟨hslen.core_ok.arena_len_arr, hslen.scratch_ok.scratch_buf_len, Nat.zero_le _,
   fun _ _ h => by omega, fun _ _ => Or.inl rfl⟩

private theorem m4FilterArVivInv_congr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {ar sb : List (BitVec 32)} {nrow_off lo hi : Nat}
    (h : M4FilterArVivInv c s ar sb nrow_off lo hi) :
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

private theorem m4_filter_row_ar_lits_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {ar sb : List (BitVec 32)} {nrow_off nqn : Nat}
    (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hviv : M4FilterArVivInv c s ar sb nrow_off 0 nqn)
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

private theorem m4FilterArVivInv_push_bin {c : FullCfg} {s : FullState} {ar sb : List (BitVec 32)}
    {nrow_off par_off nqn : Nat} (h : M4FilterArVivInv c s ar sb nrow_off 0 nqn)
    (hnqn : nqn < 256) (hdisj : nrow_off + 256 ≤ par_off) (hpar : par_off + 256 ≤ c.scratch_cap)
    {qw qi : BitVec 32} (hbin : (qw &&& 0x80000000#32) ≠ 0#32) :
    M4FilterArVivInv c s ar ((sb.set (nrow_off + nqn) qw).set (par_off + nqn) qi)
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

private theorem m4FilterArVivInv_push_large {c : FullCfg} {s : FullState} {ar sb : List (BitVec 32)}
    {nrow_off par_off nqn : Nat} (h : M4FilterArVivInv c s ar sb nrow_off 0 nqn)
    (hnqn : nqn < 256) (hdisj : nrow_off + 256 ≤ par_off) (hpar : par_off + 256 ≤ c.scratch_cap)
    {dr qi : BitVec 32} (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hdr_lt : dr.toNat < c.arena_cap) (hdr_bin : (dr &&& 0x80000000#32) = 0#32)
    (hdr_nviv : (ar[dr.toNat]'(by rw [h.1]; exact hdr_lt) &&& 0x00100000#32) = 0#32) :
    M4FilterArVivInv c s
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

private theorem m4FilterArVivInv_clear_bin {c : FullCfg} {s : FullState} {ar sb : List (BitVec 32)}
    {nrow_off qi nqn : Nat} (h : M4FilterArVivInv c s ar sb nrow_off qi nqn) (hqi : qi < nqn)
    (hbin : (sb[nrow_off + qi]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32) :
    M4FilterArVivInv c s ar sb nrow_off (qi + 1) nqn := by
  obtain ⟨har, hsb, hhi, hdom, hall⟩ := h
  refine ⟨har, hsb, hhi, fun nm h1 h2 => hdom nm (by omega) h2, fun i hi => ?_⟩
  rcases hall i hi with heq | ⟨nm, h1, h2, h0b, hidx, h0v, hset⟩
  · exact Or.inl heq
  · have hne : nm ≠ qi := fun he => by subst he; exact hbin h0b
    exact Or.inr ⟨nm, by omega, h2, h0b, hidx, h0v, hset⟩

private theorem m4FilterArVivInv_clear_large {c : FullCfg} {s : FullState}
    {ar sb : List (BitVec 32)}
    {nrow_off qi nqn : Nat} (hs_ar : s.core.arena.length = c.arena_cap)
    (h : M4FilterArVivInv c s ar sb nrow_off qi nqn) (hqi : qi < nqn)
    (hqr : nrow_off + qi < sb.length)
    (h0b : (sb[nrow_off + qi]'hqr &&& 0x80000000#32) = 0#32)
    (hdr_lt : (sb[nrow_off + qi]'hqr).toNat < c.arena_cap) :
    let dr := (sb[nrow_off + qi]'hqr).toNat
    M4FilterArVivInv c s
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

private theorem m4FilterArVivInv_done {c : FullCfg} {s : FullState} {ar sb : List (BitVec 32)}
    {nrow_off nqn : Nat} (hs_ar : s.core.arena.length = c.arena_cap)
    (h : M4FilterArVivInv c s ar sb nrow_off nqn nqn) : ar = s.core.arena := by
  apply list_eq_of_getElem?_eq (by rw [h.1, hs_ar])
  intro i hi
  rcases h.2.2.2.2 i (by omega) with heq | ⟨nm, h1, h2, _⟩
  · exact heq
  · omega

private theorem m4_filter_row_bin_upd {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {ar sb : List (BitVec 32)}
    {row_off nrow_off par_off cur_qn nqn qi qw best_lit : BitVec 32}
    {res : List Nat} {step : Nat}
    (hsb_l : sb.length = c.scratch_cap)
    (hviv : M4FilterArVivInv c s ar sb nrow_off.toNat 0 nqn.toNat)
    (hnqn_lt : nqn.toNat < 256)
    (hnr_bd : nrow_off.toNat + 256 ≤ c.scratch_cap)
    (hpr_bd : par_off.toNat + 256 ≤ c.scratch_cap)
    (hdisj : nrow_off.toNat + 256 ≤ par_off.toNat)
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
      ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 256) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 256) →
      sb[idx]? = s.scratch.scratch_buf[idx]?)
    (hent : ∀ nm < nqn.toNat,
      let pi := (sb[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧ ∃ res' : List Nat,
        (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
        M4BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
        M4BvaRowEntryOk F_cur s best_lit.toNat (sb[nrow_off.toNat + nm]?.getD 0#32) res' ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res'))) :
    let sb1 := (sb.set (nrow_off.toNat + nqn.toNat) qw).set (par_off.toNat + nqn.toNat) qi
    M4FilterArVivInv c s ar sb1 nrow_off.toNat 0 (nqn.toNat + 1) ∧
    (∀ idx < c.scratch_cap,
      ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 256) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 256) →
      sb1[idx]? = s.scratch.scratch_buf[idx]?) ∧
    (∀ nm < nqn.toNat + 1,
      let pi := (sb1[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧ ∃ res' : List Nat,
        (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
        M4BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
        M4BvaRowEntryOk F_cur s best_lit.toNat (sb1[nrow_off.toNat + nm]?.getD 0#32) res' ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res'))) := by
  let sb1 := (sb.set (nrow_off.toNat + nqn.toNat) qw).set (par_off.toNat + nqn.toNat) qi
  refine ⟨m4FilterArVivInv_push_bin hviv hnqn_lt hdisj hpr_bd hbin_ne, ?_, ?_⟩
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
      · rw [hpi_eq, hqw_getD]; unfold M4BvaRowEntryOk; rw [ite_eq_left hbin_ne]
        exact ⟨hq_lt, hres_eq, hfr_q⟩
      · rw [hnr_eq]; unfold M4BvaRowEntryOk; rw [ite_eq_left hbin_ne]
        exact ⟨hq_lt, hres_eq, hbl_q_ent⟩
      · rw [hres_eq]; exact hbl_q_ent
    · have hpi_eq : sb1[par_off.toNat + nm]? = sb[par_off.toNat + nm]? := by
        dsimp only [sb1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      have hnr_eq : sb1[nrow_off.toNat + nm]? = sb[nrow_off.toNat + nm]? := by
        dsimp only [sb1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      dsimp only; rw [hpi_eq, hnr_eq]; exact hent nm (by omega)

private theorem m4_filter_row_mark_step {c : FullCfg} {s : FullState}
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

private theorem m4_filter_row_large_upd {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {ar sb : List (BitVec 32)} {lmj : List (BitVec 8)}
    {row_off nrow_off par_off cur_qn nqn qi qw dr best_lit : BitVec 32}
    {res : List Nat} {step : Nat}
    (hcl : s.core.LengthsOk c) (har_l : ar.length = c.arena_cap)
    (hsb_l : sb.length = c.scratch_cap)
    (hw_ar : FullWitnessInv c F0 F_cur { s.core with arena := ar })
    (hnd_ar : FullArenaVarsNodup
      (FullState.mk { s.core with arena := ar } { s.scratch with scratch_buf := sb }))
    (hl0 : s.core.cur_level = 0)
    (hviv : M4FilterArVivInv c s ar sb nrow_off.toNat 0 nqn.toNat)
    (hnqn_lt : nqn.toNat < 256)
    (hnr_bd : nrow_off.toNat + 256 ≤ c.scratch_cap)
    (hpr_bd : par_off.toNat + 256 ≤ c.scratch_cap)
    (hdisj : nrow_off.toNat + 256 ≤ par_off.toNat)
    (hrefs_ar : fullArenaClauseRefsCore { s.core with arena := ar } =
      fullArenaClauseRefsCore s.core)
    (hqw_ref : qw.toNat ∈ fullArenaClauseRefsCore s.core)
    (hqw_ng : fullArenaClauseGarbCore s.core qw.toNat = false)
    (hqw_sz3 : 3 ≤ fullArenaClauseSizeCore s.core qw.toNat)
    (hqw_sz256 : fullArenaClauseSizeCore s.core qw.toNat ≤ 256)
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
      ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 256) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 256) →
      sb[idx]? = s.scratch.scratch_buf[idx]?)
    (hent : ∀ nm < nqn.toNat,
      let pi := (sb[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧ ∃ res' : List Nat,
        (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
        M4BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
        M4BvaRowEntryOk F_cur s best_lit.toNat (sb[nrow_off.toNat + nm]?.getD 0#32) res' ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res')))
    (hhar_b : c.arena_cap < 2 * dimacsBound) :
    let ar1 := ar.set dr.toNat ((ar[dr.toNat]'(by omega)) ||| 0x00100000#32)
    let sb1 := (sb.set (nrow_off.toNat + nqn.toNat) dr).set (par_off.toNat + nqn.toNat) qi
    M4FilterArVivInv c s ar1 sb1 nrow_off.toNat 0 (nqn.toNat + 1) ∧
    FullWitnessInv c F0 F_cur { s.core with arena := ar1 } ∧
    FullArenaVarsNodup
      (FullState.mk { s.core with arena := ar1 } { s.scratch with scratch_buf := sb1 }) ∧
    (∀ idx < c.scratch_cap,
      ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 256) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 256) →
      sb1[idx]? = s.scratch.scratch_buf[idx]?) ∧
    (∀ nm < nqn.toNat + 1,
      let pi := (sb1[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧ ∃ res' : List Nat,
        (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
        M4BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
        M4BvaRowEntryOk F_cur s best_lit.toNat (sb1[nrow_off.toNat + nm]?.getD 0#32) res' ∧
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
  have hviv1 : M4FilterArVivInv c s ar1 sb1 nrow_off.toNat 0 (nqn.toNat + 1) :=
    m4FilterArVivInv_push_large hviv hnqn_lt (by omega) (by omega)
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
      · rw [hpi_eq, hqw_getD]; unfold M4BvaRowEntryOk
        rw [ite_eq_right (fun h' => h' hbin_eq)]
        exact ⟨hqw_ref, hqw_ng, hqw_sz3, hqw_sz256, hfr_mem, hres_perm_f, hqw_perm⟩
      · rw [hnr_eq]; unfold M4BvaRowEntryOk; rw [ite_eq_right (fun h' => h' hdr_bin)]
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

private def m4EGrp0_2 {rs : List Ty} (J : Cont [i32, i32]) (xs : Tup Val [i32, i32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32]]) bs _ =>
    match bs (J, ()) with | .cons f .nil => f xs
  | _ => .hlt

private def m4EGrpBody_0 {rs : List Ty} (J : Cont []) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[]]) _ body => body (J, ()) | _ => .hlt

private def m4EGrpBody_1 {rs : List Ty} (J : Cont [i32]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32]]) _ body => body (J, ()) | _ => .hlt

private def m4FilterRowMpExpr (h pWvec pWstk pAr pLm pScr : Val i64)
    (row_off nrow_off par_off cur_qn best_lit nqn qi qw csz min_l min_d j : Val i32)
    (J : Cont [i32, i32]) (Jend : Cont []) (Jbr : Cont [i32])
    (Jm : Cont [i32, i32, i32]) (Jm2 : Cont [i32]) : Expr Val Cont [i32] :=
  full_bva_filter_row_body Val Cont (h, row_off, nrow_off, par_off, cur_qn, best_lit, ())
    |> eSkip 1 |> eLoad64 pWvec
    |> eSkip 1 |> eLoad64 pWstk
    |> eSkip 1 |> eLoad64 pAr
    |> eSkip 1 |> eLoad64 pLm
    |> eSkip 1 |> eLoad64 pScr
    |> m4EGrp0_2 J (nqn, qi, ())
    |> m4EGrpBody_0 Jend
    |> eSkip 1 |> eThen
    |> eSkip 1 |> eThen
    |> eSkip 4 |> eLoad32 qw
    |> m4EGrpBody_1 Jbr
    |> eSkip 2 |> eElse
    |> eSkip 4 |> eLoad32 csz
    |> eGrp0_3 Jm (min_l, min_d, j, ())
    |> eSkip 1 |> eElse
    |> m4EGrpBody_1 Jm2

private theorem m4_filter_row_mp_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
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
    (hstep1 : 1 ≤ step) (hstep32 : step < 32)
    (_hrow_eq : row_off.toNat = 64 + (step - 1) * 256)
    (hnrow_eq : nrow_off.toNat = 64 + step * 256)
    (hpar_eq : par_off.toNat = 8256 + step * 256)
    (hscr16448 : 16448 ≤ c.scratch_cap)
    (har_l : ar.length = c.arena_cap) (hsb_l : sb.length = c.scratch_cap)
    (hlmj_l : lmj.length = 2 * c.max_vars)
    (hqi_lt : qi.toNat < cur_qn.toNat) (hnqn_lt : nqn.toNat < 256)
    (hw_ar : FullWitnessInv c F0 F_cur { s.core with arena := ar })
    (hnd_ar : FullArenaVarsNodup
      (FullState.mk { s.core with arena := ar } { s.scratch with scratch_buf := sb }))
    (hviv : M4FilterArVivInv c s ar sb nrow_off.toNat 0 nqn.toNat)
    (hqw_ref : qw.toNat ∈ fullArenaClauseRefsCore s.core)
    (hqw_ng : fullArenaClauseGarbCore s.core qw.toNat = false)
    (hqw_sz3 : 3 ≤ fullArenaClauseSize s qw.toNat)
    (hqw_sz256 : fullArenaClauseSize s qw.toNat ≤ 256)
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
      ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 256) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 256) →
      sb[idx]? = s.scratch.scratch_buf[idx]?)
    (hent : ∀ nm < nqn.toNat,
      let pi := (sb[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧ ∃ res' : List Nat,
        (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
        M4BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
        M4BvaRowEntryOk F_cur s best_lit.toNat (sb[nrow_off.toNat + nm]?.getD 0#32) res' ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res')))
    (hmj : (FullMem c (FullState.mk { s.core with arena := ar, lit_mark := lmj }
      { s.scratch with scratch_buf := sb }) ⋆ R) mj)
    (hJm2 : ∀ nqn2 ar2 sb2 mf2,
      nqn2.toNat ≤ 256 → M4FilterArVivInv c s ar2 sb2 nrow_off.toNat 0 nqn2.toNat →
      FullWitnessInv c F0 F_cur { s.core with arena := ar2 } →
      FullArenaVarsNodup
        (FullState.mk { s.core with arena := ar2 } { s.scratch with scratch_buf := sb2 }) →
      (∀ idx < c.scratch_cap,
        ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 256) →
        ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 256) →
        sb2[idx]? = s.scratch.scratch_buf[idx]?) →
      (∀ nm < nqn2.toNat,
        let pi := (sb2[par_off.toNat + nm]?.getD 0#32).toNat
        pi < cur_qn.toNat ∧ ∃ res' : List Nat,
          (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
          M4BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
            (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
          M4BvaRowEntryOk F_cur s best_lit.toNat (sb2[nrow_off.toNat + nm]?.getD 0#32) res' ∧
          (∀ t < step, (cnfOfClauses F_cur).EntailsClause
            (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res'))) →
      (FullMem c (FullState.mk { s.core with arena := ar2, lit_mark := lmj }
        { s.scratch with scratch_buf := sb2 }) ⋆ R) mf2 →
      Jm2 (nqn2, ()) mf2) :
    wp Γ Q X (m4FilterRowMpExpr c.hdr c.pWvec c.pWstk c.pArena c.pLitMark c.pScratchBuf
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
  have ⟨hrefs_ar, hcl_ar⟩ := m4FilterArVivInv_congr hcl hw hviv
  have ⟨hqw_ng_ar, hqw_sz_ar, _⟩ := hcl_ar qw.toNat hqw_ref
  dsimp only [m4FilterRowMpExpr, eSkip, eLoad64, eLoad32, m4EGrp0_2, m4EGrpBody_0, m4EGrpBody_1,
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
        nqn2.toNat ≤ 256 ∧ M4FilterArVivInv c s ar2 sb2 nrow_off.toNat 0 nqn2.toNat ∧
        FullWitnessInv c F0 F_cur { s.core with arena := ar2 } ∧
        FullArenaVarsNodup
          (FullState.mk { s.core with arena := ar2 } { s.scratch with scratch_buf := sb2 }) ∧
        (∀ idx < c.scratch_cap,
          ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 256) →
          ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 256) →
          sb2[idx]? = s.scratch.scratch_buf[idx]?) ∧
        (∀ nm < nqn2.toNat,
          let pi := (sb2[par_off.toNat + nm]?.getD 0#32).toNat
          pi < cur_qn.toNat ∧ ∃ res' : List Nat,
            (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
            M4BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
              (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
            M4BvaRowEntryOk F_cur s best_lit.toNat (sb2[nrow_off.toNat + nm]?.getD 0#32) res' ∧
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
      · have ⟨_, _, hrem_next⟩ :=
          FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hmp_ws (by assumption)
        exact ihmp (mp + 1#64, ()) mmp (by dsimp only; rw [hmp1_n]; omega)
          ⟨by rw [hmp1_n]; omega, by rw [hmp1_n]; omega, rfl,
           by rw [hmp1_n, show moff0 + msz0 - (mp.toNat + 1) =
                moff0 + msz0 - mp.toNat - 1 by omega]; exact hrem_next⟩
      · exact hJmp ⟨nqn, mp + 1#64, ar, sb⟩ mmp
          ⟨by omega, hviv, hw_ar, hnd_ar, hfr_sb, hent, hmj⟩
      · have ⟨h2le, hrem_next⟩ :=
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
        · obtain ⟨hdr_ng_ar, hdr_nviv_h, hdr_sz_eq_ar, hbl_mem_ar, hdr_perm_ar,
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
          have ⟨hviv1, hw1, hnd1, hfr1, hent1⟩ := m4_filter_row_large_upd hcl har_l hsb_l
            hw_ar hnd_ar hl0 hviv hnqn_lt (by omega) (by omega) (by omega) hrefs_ar
            hqw_ref hqw_ng hqw_sz3 hqw_sz256 hqw_sz_ar hfr_mem hres_perm_f hqw_perm
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
        · exact ihmp (mp + 1#64 + 1#64, ()) mmp (by dsimp only; rw [hmp2_n]; omega)
            ⟨by rw [hmp2_n]; omega, by rw [hmp2_n]; omega, rfl,
             by rw [hmp2_n, show moff0 + msz0 - (mp.toNat + 2) =
                  moff0 + msz0 - mp.toNat - 2 by omega]; exact hrem_next⟩
      · have ⟨h2le, hrem_next⟩ :=
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

/-! ## 2. `m4_bva_filter_row_wp` -/

theorem m4_bva_filter_row_wp (Γ : Env)
    (hMatchLarge : ∀ args m Q X, fullBvaMatchLargeSpec args m Q X →
      Γ "full_bva_match_large" [i64, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, m4BvaFilterRowSpec args m Q X →
      Func.wp Γ full_bva_filter_row_body args m Q X := by
  rintro ⟨h, row_off, nrow_off, par_off, cur_qn, best_lit, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, step, rfl, hslen, hw, hnodup, hext, hl0, hdm, hstep1, hstep32, hscr16448,
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
        M4BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res ∧
        M4BvaRowEntryOk F_cur s best_lit.toNat (sb[nrow_off.toNat + nm]?.getD 0#32) res ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res))
  let SbFrame (sb : List (BitVec 32)) : Prop :=
    ∀ idx < c.scratch_cap,
      ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 256) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 256) →
      sb[idx]? = s.scratch.scratch_buf[idx]?
  c0_hsteps
  refine wp_loop_inv
    (fun (nqn, qi, ()) ml => ∃ ar sb,
      qi.toNat ≤ cur_qn.toNat ∧ nqn.toNat ≤ 256 ∧
      M4FilterArVivInv c s ar sb nrow_off.toNat 0 nqn.toNat ∧
      FullWitnessInv c F0 F_cur { s.core with arena := ar } ∧
      FullArenaVarsNodup (mkSt ar s.core.lit_mark sb) ∧
      SbFrame sb ∧ FilterEntryOk sb nqn.toNat ∧
      (FullMem c (mkSt ar s.core.lit_mark sb) ⋆ R) ml)
    (fun (_, qi, _) _ => cur_qn.toNat - qi.toNat)
    (fun Jq hJq => by
      c0_hsteps
      exact hJq (0#32, 0#32, ()) m
        ⟨s.core.arena, s.scratch.scratch_buf, Nat.zero_le _, Nat.zero_le _,
         m4FilterArVivInv_init hslen nrow_off.toNat, hw, hnodup,
         fun _ _ _ _ => rfl, fun _ h => by simp only [bv_c0] at h; omega, hm⟩)
    (fun Jq (nqn, qi, ()) ml ⟨ar, sb, hqi_le, hnqn_le, hviv, hw_ar, hnd_ar, hfr_sb, hent, hml⟩
        ihq => ?_)
  dsimp only [mkSt] at hml
  have har_l := hviv.1; have hsb_l := hviv.2.1
  c0_hsteps_nogrp
  refine wp_join_state0 (α := Unit)
    (fun _ mf => mf = ml)
    (fun _ _ mf hmf => ?_)
    (fun Jend hJend => ?_)
  · rcases hmf with rfl
    refine wp_loop_inv
      (fun (ci, ()) mci => ∃ arci,
        ci.toNat ≤ nqn.toNat ∧
        M4FilterArVivInv c s arci sb nrow_off.toNat ci.toNat nqn.toNat ∧
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
      · have h0b : (dr &&& 0x80000000#32) = 0#32 := by
          have h1 : (sb[(BitVec.setWidth 64 (nrow_off + ci)).toNat]'(by
            rw [hset, hnrci]; omega) &&& 0x80000000#32) = 0#32 := by assumption
          rwa [hdr_eq] at h1
        have hdr_ref := (hviv_ci.2.2.2.1 ci.toNat (Nat.le_refl _) hci_lt (by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact h0b)).1
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdr_ref
        have hdr_wf := hw.arena.refs_wf _ hdr_ref
        have hstep := m4FilterArVivInv_clear_large har_len hviv_ci hci_lt (by omega) h0b (by omega)
        have hdr_ar_b : (BitVec.setWidth 64 (sb[(BitVec.setWidth 64 (nrow_off + ci)).toNat]'(by
            rw [hset, hnrci]; omega))).toNat < arci.length := by
          rw [hdr_eq, hset]; dsimp only [dr]; have := hdr_wf.1; have := hcl.arena_len_le; omega
        c0_hfast
        refine ihc (ci + 1#32, ()) m (by dsimp only; rw [hci1]; omega)
          ⟨_, by rw [hci1]; omega, by rw [hci1]; exact hstep, ?_⟩
        simp only [hset, hnrci] at hm; exact hm
      · have hbin : (sb[nrow_off.toNat + ci.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have h1 : (sb[(BitVec.setWidth 64 (nrow_off + ci)).toNat]'(by
            rw [hset, hnrci]; omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
          rwa [hdr_eq] at h1
        c0_hfast
        exact ihc (ci + 1#32, ()) mci (by dsimp only; rw [hci1]; omega)
          ⟨arci, by rw [hci1]; omega,
           by rw [hci1]; exact m4FilterArVivInv_clear_bin hviv_ci hci_lt hbin, hmci⟩
    · have hci_eq : ci.toNat = nqn.toNat := by omega
      rw [hci_eq] at hviv_ci
      have har_rest : arci = s.core.arena := m4FilterArVivInv_done har_len hviv_ci
      rw [har_rest] at hmci
      exact hQ nqn sb mci ⟨hcl, { hsc with scratch_buf_len := hsb_l }⟩ hnqn_le hfr_sb hent hmci
  · c0_hsteps_nogrp
    · have hqi_lt : qi.toNat < cur_qn.toNat := by assumption
      have hnqn_lt : nqn.toNat < 256 := by
        have h1 : nqn.toNat < (256 : BitVec 32).toNat := by assumption
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
      refine wp_join_state1 (t := i32)
        (α := BitVec 32 × List (BitVec 32) × List (BitVec 32)) (fun st => st.1)
        (fun ⟨nqn', ar', sb'⟩ mf =>
          nqn'.toNat ≤ 256 ∧ M4FilterArVivInv c s ar' sb' nrow_off.toNat 0 nqn'.toNat ∧
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
      · have hbin_ne : (qw &&& 0x80000000#32) ≠ 0#32 := by
          have h1 : (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
            rw [hset, hrqi]; omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
          rwa [hqw_eq] at h1
        unfold M4BvaRowEntryOk at hqw_ent; rw [ite_eq_left hbin_ne] at hqw_ent
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
            nqn'.toNat ≤ 256 ∧ M4FilterArVivInv c s ar sb' nrow_off.toNat 0 nqn'.toNat ∧
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
          · have ⟨_, hq_bl_ent, _⟩ :=
              FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hqp_ws (by assumption)
            have hnw_bl : (s.core.wstk[qp.toNat]'hqp_ws &&& 0x7FFFFFFF#32) = best_lit := by
              assumption
            rw [hnw_bl] at hq_bl_ent
            have hbl_q_ent : (cnfOfClauses F_cur).EntailsClause
                (cnfClause [best_lit.toNat, q.toNat]) := bva_bin_swap_entails hq_bl_ent
            have ⟨hviv1, hfr1, hent1⟩ := m4_filter_row_bin_upd hsb_l hviv hnqn_lt (by omega)
              (by omega) (by omega) hbin_ne hq_lt hres_eq hfr_q hbl_q_ent hqi_lt hres_lt hres_nd
              (fun t ht => hres_ent t (by omega)) hqw_getD hfr_sb hent
            let sb1 := (sb.set (nrow_off.toNat + nqn.toNat) qw).set (par_off.toNat + nqn.toNat) qi
            have hm1 : (FullMem c (mkSt ar s.core.lit_mark sb1) ⋆ R) m := by
              dsimp only [mkSt, sb1]
              simp only [hqw_eq] at hm; simp only [hset, hnrnq, hprnq] at hm; exact hm
            exact hJqp ⟨nqn + 1#32, qp, sb1⟩ m
              ⟨by rw [hnqn1]; omega, by rw [hnqn1]; exact hviv1, hfr1, by rw [hnqn1]; exact hent1,
               hm1⟩
          · have ⟨_, _, hrem_next⟩ :=
              FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hqp_ws (by assumption)
            exact ihp (qp + 1#64, ()) mlp (by dsimp only; rw [hqp1_n]; omega)
              ⟨by rw [hqp1_n]; omega, by rw [hqp1_n]; omega, rfl,
               by rw [hqp1_n, show qoff0 + qsz0 - (qp.toNat + 1) = qoff0 + qsz0 - qp.toNat - 1
                    by omega]; exact hrem_next⟩
          · have ⟨h2le, hrem_next⟩ :=
              FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hqp_ws (by assumption)
            have hqp2_n : (qp + 2#64).toNat = qp.toNat + 2 := by simp only [bv_c0]; omega
            exact ihp (qp + 2#64, ()) mlp (by dsimp only; rw [hqp2_n]; omega)
              ⟨by rw [hqp2_n]; omega, by rw [hqp2_n]; omega, rfl,
               by rw [hqp2_n, show qoff0 + qsz0 - (qp.toNat + 2) = qoff0 + qsz0 - qp.toNat - 2
                    by omega]; exact hrem_next⟩
        · c0_hfast
          exact hJqp ⟨nqn, qp, sb⟩ mlp ⟨hnqn_le, hviv, hfr_sb, hent, hml⟩
      · have hbin_eq : (qw &&& 0x80000000#32) = 0#32 := by
          have h1 : (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
            rw [hset, hrqi]; omega) &&& 0x80000000#32) = 0#32 := by assumption
          rwa [hqw_eq] at h1
        unfold M4BvaRowEntryOk at hqw_ent; rw [ite_eq_right (fun h' => h' hbin_eq)] at hqw_ent
        obtain ⟨hqw_ref, hqw_ng, hqw_sz3, hqw_sz256, hfr_mem, hres_perm_f, hqw_perm⟩ := hqw_ent
        have hqw_wf := hw.arena.refs_wf qw.toNat hqw_ref
        have ⟨hrefs_ar, hcl_ar⟩ := m4FilterArVivInv_congr hcl hw hviv
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
        have hqw_lits_eq := m4_filter_row_ar_lits_eq hcl hw hviv hqw_ref
        c0_hsteps_nogrp
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
        · have hj_lt : j.toNat < csz_bv.toNat := by
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
          · have ⟨hstep2, hres_next⟩ := m4_filter_row_mark_step hlm_len hcv_le hfr_b0 hres_perm_f
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
          · have ⟨hstep2, hres_next⟩ := m4_filter_row_mark_step hlm_len hcv_le hfr_b0 hres_perm_f
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
          · have ⟨hstep2, hres_next⟩ := m4_filter_row_mark_step hlm_len hcv_le hfr_b0 hres_perm_f
              hlmj_inv hlmj_res (by omega) hqwj_lt hl_eq hl_mem hl_lt (by
                simp only [← hqwj_mod]; simpa only [← hqw_mod] using (by assumption : _))
            dsimp only at hm ⊢
            simp only [hqw_eq] at hm; simp only [hqwj_n, hset] at hm
            try simp only [bv8_trunc_or_2] at hm
            try simp only [bv8_trunc_or_w] at hm
            exact ihm (min_l, min_d, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
              ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep2, hres_next, hmin_ok, hm⟩
          · exact ihm (min_l, min_d, j + 1#32, ()) mj (by dsimp only; rw [hj1]; omega)
              ⟨lmj, by rw [hj1]; omega, by rw [hj1]; exact lmBit2Inv_skip hlmj_inv, hlmj_res,
               hmin_ok, hmj⟩
        · have hj_eq : j.toNat = csz_bv.toNat := by
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
              nqn2.toNat ≤ 256 ∧ M4FilterArVivInv c s ar2 sb2 nrow_off.toNat 0 nqn2.toNat ∧
              FullWitnessInv c F0 F_cur { s.core with arena := ar2 } ∧
              FullArenaVarsNodup (mkSt ar2 s.core.lit_mark sb2) ∧
              SbFrame sb2 ∧ FilterEntryOk sb2 nqn2.toNat ∧
              (FullMem c (mkSt ar2 lmj sb2) ⋆ R) mf2)
            (fun _ ⟨nqn2, ar2, sb2⟩ mf2 ⟨hnqn2, hviv2, hw2, hnd2, hfr2, hent2, hmf2⟩ => ?_)
            (fun Jm2 hJm2 => ?_)
          · clear hmj hrow_entries hmat hlmj_res hmin_ok
            dsimp only [mkSt] at hmf2
            have har2_l := hviv2.1
            have har2_lits := m4_filter_row_ar_lits_eq hcl hw hviv2 hqw_ref
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
          · clear hrow_entries hmat hlm_b0 hlm_clr hqw_lits_eq hqw_lits_ar
            dsimp only
            simp only [hqw_eq]
            have hmp := m4_filter_row_mp_wp (Γ := Γ) (Q := Q) (X := X) hMatchLarge
              (J := Jq) (Jend := Jend) (Jbr := Jbr) (Jm := Jm) (Jm2 := Jm2)
              (csz := csz_bv) (j := j)
              hcl hsc hw hdw hl0 hdm hstep1 hstep32 hrow_eq hnrow_eq hpar_eq hscr16448
              har_l hsb_l hlmj_l hqi_lt hnqn_lt hw_ar hnd_ar hviv hqw_ref hqw_ng hqw_sz3 hqw_sz256
              hfr_mem hres_perm_f hqw_perm hbin_eq hres_lt hres_nd
              (fun t ht => hres_ent t (by omega)) hqw_getD hlmj_res hmin_ok hfr_sb hent hmj
              (fun nqn2 ar2 sb2 mf2 h1 h2 h3 h4 h5 h6 h7 =>
                hJm2 ⟨nqn2, ar2, sb2⟩ mf2 ⟨h1, h2, h3, h4, h5, h6, h7⟩)
            dsimp only [m4FilterRowMpExpr, eSkip, eLoad64, eLoad32, m4EGrp0_2, m4EGrpBody_0,
              m4EGrpBody_1, eGrp0_3, eThen, eElse, full_bva_filter_row_body] at hmp
            exact hmp
    · exact hJend () ml rfl
    · exact hJend () ml rfl

/-! ## 3. Multi-Step BVA Matrix Construction (`m4_bva_try_lit_wp`) -/

section M4BvaTryLitHelpers

private theorem m4BvaMatrixInv_weaken_step {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {step1 step2 : Nat} (h1 : 1 ≤ step1) (h12 : step1 ≤ step2)
    (h : M4BvaMatrixInv c F_cur s step2) : M4BvaMatrixInv c F_cur s step1 :=
  ⟨h.1, h1, Nat.le_trans h12 h.2.2.1, fun r hr => h.2.2.2 r (Nat.lt_of_lt_of_le hr h12)⟩

private theorem m4BvaRowEntryOk_congr {F_cur : List (List Nat)} {s s' : FullState}
    {fr : Nat} {w : BitVec 32} {res : List Nat}
    (hcv : s'.core.cur_vars = s.core.cur_vars)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (h : M4BvaRowEntryOk F_cur s fr w res) : M4BvaRowEntryOk F_cur s' fr w res := by
  unfold M4BvaRowEntryOk at h ⊢
  by_cases hbin : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hbin] at h ⊢; rwa [hcv]
  · rw [ite_eq_right hbin] at h ⊢
    simp only [fullArenaClauseRefs, fullArenaClauseGarb, fullArenaClauseSize,
      fullArenaClauseLits, fullArenaClauseRefsCore, fullArenaClauseGarbCore,
      fullArenaClauseSizeCore, fullArenaClauseLitsCore, fullArenaHdrCore, har, hal] at h ⊢
    exact h

private theorem m4BvaMatrixInv_congr {c : FullCfg} {F_cur : List (List Nat)} {s s' : FullState}
    {step : Nat} (hcv : s'.core.cur_vars = s.core.cur_vars)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (hsb : s'.scratch.scratch_buf = s.scratch.scratch_buf)
    (h : M4BvaMatrixInv c F_cur s step) : M4BvaMatrixInv c F_cur s' step := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun r hr => ?_⟩
  obtain ⟨hfr, hq2, hq256, hm⟩ := h.2.2.2 r hr
  refine ⟨by rw [hsb, hcv]; exact hfr, by rw [hsb]; exact hq2, by rw [hsb]; exact hq256,
    fun m hm_lt => ?_⟩
  rw [hsb] at hm_lt
  obtain ⟨res, hres_lt, hres_nd, hok, hent, hpar⟩ := hm m hm_lt
  refine ⟨res, fun x hx => by rw [hcv]; exact hres_lt x hx, hres_nd, ?_, ?_, ?_⟩
  · rw [hsb]; exact m4BvaRowEntryOk_congr hcv har hal hok
  · intro t ht; rw [hsb]; exact hent t ht
  · intro hr0; rw [hsb]; obtain ⟨hpi, hpok⟩ := hpar hr0
    exact ⟨hpi, m4BvaRowEntryOk_congr hcv har hal hpok⟩

private theorem m4BvaRowEntryOk_of_large_f0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {cr f0 : BitVec 32} (href : cr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hng : fullArenaClauseGarbCore s.core cr.toNat = false)
    (hsz3 : 3 ≤ fullArenaClauseSizeCore s.core cr.toNat)
    (hsz256 : fullArenaClauseSizeCore s.core cr.toNat ≤ 256)
    (hf0_mem : f0.toNat ∈ fullArenaClauseLitsCore s.core cr.toNat) :
    ∃ res : List Nat,
      (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
      M4BvaRowEntryOk F_cur s f0.toNat cr res ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause (f0.toNat :: res)) := by
  let C := fullArenaClauseLitsCore s.core cr.toNat
  let res := C.filter (· != f0.toNat)
  have hC_lt := hinv.2.1.arena.lits_lt cr.toNat href hng
  have hC_nd_vars : (C.map (· / 2)).Nodup := hinv.2.2.2.1 cr.toNat href hng
  have hC_nd : C.Nodup := nodup_of_map_div2 hC_nd_vars
  have hC_ent := hinv.2.1.arena.entails cr.toNat href hng
  have hres_sub : res.Sublist C := List.filter_sublist
  have hres_nd : (res.map (· / 2)).Nodup := hC_nd_vars.sublist (hres_sub.map _)
  have hres_lt : ∀ x ∈ res, x < 2 * s.core.cur_vars := fun x hx => hC_lt x (hres_sub.subset hx)
  have hperm_er : res.Perm (C.erase f0.toNat) := by
    have hp := (List.perm_cons_erase hf0_mem).filter (· != f0.toNat)
    have he : (f0.toNat :: C.erase f0.toNat).filter (· != f0.toNat) = C.erase f0.toNat := by
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact List.filter_eq_self.mpr fun y hy => by
        have hne : y ≠ f0.toNat := fun h => by
          subst h
          exact (List.nodup_cons.mp (hC_nd.perm (List.perm_cons_erase hf0_mem))).1 hy
        simp [hne]
    rwa [he] at hp
  have hC_perm : C.Perm (f0.toNat :: res) :=
    (List.perm_cons_erase hf0_mem).trans (hperm_er.symm.cons f0.toNat)
  have hcr_not_bin : (cr &&& 0x80000000#32) = 0#32 := by
    have hwf := hinv.2.1.arena.refs_wf cr.toNat href
    have hal := hinv.1.core_ok.arena_len_le
    have hab := c.harena; unfold dimacsBound at hab
    exact bv32_bin_flag_zero_of_lt (by omega)
  refine ⟨res, hres_lt, hres_nd, ?_, clause_entails_of_perm hC_perm hC_ent⟩
  unfold M4BvaRowEntryOk; rw [ite_eq_right (fun h' => h' hcr_not_bin)]
  exact ⟨href, hng, hsz3, hsz256, hf0_mem, List.Perm.refl _, hC_perm⟩

private theorem m4BvaMatrixInv_step1 {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {sb : List (BitVec 32)} {f0 qn : BitVec 32}
    (hcap : 16448 ≤ c.scratch_cap) (hsb_len : sb.length = c.scratch_cap)
    (hf0_lt : f0.toNat < 2 * s.core.cur_vars) (hq2 : 2 ≤ qn.toNat) (hq256 : qn.toNat ≤ 256)
    (hrow0 : ∀ m < qn.toNat, ∃ res : List Nat,
      (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
      M4BvaRowEntryOk F_cur s f0.toNat (sb[64 + m]?.getD 0#32) res ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause (f0.toNat :: res))) :
    M4BvaMatrixInv c F_cur
      { s with scratch := { s.scratch with scratch_buf := (sb.set 0 f0).set 32 qn } } 1 := by
  let sb1 := (sb.set 0 f0).set 32 qn
  have h0 : sb1[0]?.getD 0#32 = f0 := by
    dsimp only [sb1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
      Option.getD_some]
  have h32 : sb1[32]?.getD 0#32 = qn := by
    dsimp only [sb1]; rw [List.getElem?_set_self (by simp [hsb_len]; omega), Option.getD_some]
  have h64 : ∀ m < 256, sb1[64 + m]?.getD 0#32 = sb[64 + m]?.getD 0#32 := fun m _ => by
    dsimp only [sb1]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  refine ⟨hcap, Nat.le_refl 1, by omega, fun r hr => ?_⟩
  have hr0 : r = 0 := by omega
  subst hr0; dsimp only; rw [h0, h32]
  refine ⟨hf0_lt, hq2, hq256, fun m hm => ?_⟩
  obtain ⟨res, hres_lt, hres_nd, hok, hent⟩ := hrow0 m hm
  refine ⟨res, hres_lt, hres_nd, ?_, fun t ht => ?_, fun h => by omega⟩
  · rw [show 64 + 0 * 256 + m = 64 + m by omega, h64 m (by omega)]
    exact m4BvaRowEntryOk_congr rfl rfl rfl hok
  · have ht0 : t = 0 := by omega
    subst ht0; rw [h0]; exact hent

private theorem m4BvaMatrixInv_extend_step {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {sb' : List (BitVec 32)} {step : Nat} {best_lit new_qn : BitVec 32}
    (hstep1 : 1 ≤ step) (hstep32 : step < 32)
    (hmat : M4BvaMatrixInv c F_cur s step)
    (hsb'_len : sb'.length = c.scratch_cap)
    (hbest_lt : best_lit.toNat < 2 * s.core.cur_vars)
    (hnq2 : 2 ≤ new_qn.toNat) (hnq256 : new_qn.toNat ≤ 256)
    (hpres : ∀ idx < c.scratch_cap,
      ¬ (64 + step * 256 ≤ idx ∧ idx < 64 + step * 256 + 256) →
      ¬ (8256 + step * 256 ≤ idx ∧ idx < 8256 + step * 256 + 256) →
      sb'[idx]? = s.scratch.scratch_buf[idx]?)
    (hnew : ∀ nm < new_qn.toNat,
      let pi := (sb'[8256 + step * 256 + nm]?.getD 0#32).toNat
      pi < (s.scratch.scratch_buf[32 + (step - 1)]?.getD 0#32).toNat ∧
      ∃ res : List Nat,
        (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
        M4BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[64 + (step - 1) * 256 + pi]?.getD 0#32) res ∧
        M4BvaRowEntryOk F_cur s best_lit.toNat (sb'[64 + step * 256 + nm]?.getD 0#32) res ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res))) :
    M4BvaMatrixInv c F_cur
      { s with scratch := { s.scratch with
          scratch_buf := (sb'.set step best_lit).set (32 + step) new_qn } }
      (step + 1) := by
  have hcap := hmat.1
  let sb2 := (sb'.set step best_lit).set (32 + step) new_qn
  have hget_lt : ∀ idx < c.scratch_cap, idx ≠ step → idx ≠ 32 + step →
      ¬ (64 + step * 256 ≤ idx ∧ idx < 64 + step * 256 + 256) →
      ¬ (8256 + step * 256 ≤ idx ∧ idx < 8256 + step * 256 + 256) →
      sb2[idx]? = s.scratch.scratch_buf[idx]? := fun idx hi h1 h2 h3 h4 => by
    dsimp only [sb2]
    rw [List.getElem?_set_ne (Ne.symm h2), List.getElem?_set_ne (Ne.symm h1)]
    exact hpres idx hi h3 h4
  have hget_step : sb2[step]?.getD 0#32 = best_lit := by
    dsimp only [sb2]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
  have hget_32step : sb2[32 + step]?.getD 0#32 = new_qn := by
    dsimp only [sb2]
    rw [List.getElem?_set_self (by simp [hsb'_len]; omega), Option.getD_some]
  have hget_row : ∀ nm < 256, sb2[64 + step * 256 + nm]? = sb'[64 + step * 256 + nm]? :=
    fun nm _ => by
      dsimp only [sb2]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hget_par : ∀ nm < 256, sb2[8256 + step * 256 + nm]? = sb'[8256 + step * 256 + nm]? :=
    fun nm _ => by
      dsimp only [sb2]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  refine ⟨hcap, by omega, by omega, fun r hr => ?_⟩
  by_cases hre : r < step
  · obtain ⟨hfr, hq2, hq256, hm⟩ := hmat.2.2.2 r hre
    have hfr_eq : sb2[r]? = s.scratch.scratch_buf[r]? :=
      hget_lt r (by omega) (by omega) (by omega) (by omega) (by omega)
    have hqn_eq : sb2[32 + r]? = s.scratch.scratch_buf[32 + r]? :=
      hget_lt (32 + r) (by omega) (by omega) (by omega) (by omega) (by omega)
    dsimp only; rw [hfr_eq, hqn_eq]
    refine ⟨hfr, hq2, hq256, fun m hm_lt => ?_⟩
    obtain ⟨res, hres_lt, hres_nd, hok, hent, hpar⟩ := hm m hm_lt
    have hcell_eq : sb2[64 + r * 256 + m]? = s.scratch.scratch_buf[64 + r * 256 + m]? :=
      hget_lt (64 + r * 256 + m) (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ⟨res, hres_lt, hres_nd, ?_, fun t ht => ?_, fun hr0 => ?_⟩
    · rw [hcell_eq]; exact m4BvaRowEntryOk_congr rfl rfl rfl hok
    · rw [hget_lt t (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hent t ht
    · obtain ⟨hpi, hpok⟩ := hpar hr0
      have hpar_eq : sb2[8256 + r * 256 + m]? = s.scratch.scratch_buf[8256 + r * 256 + m]? :=
        hget_lt (8256 + r * 256 + m) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hqprev_eq : sb2[32 + (r - 1)]? = s.scratch.scratch_buf[32 + (r - 1)]? :=
        hget_lt (32 + (r - 1)) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hfprev_eq : sb2[r - 1]? = s.scratch.scratch_buf[r - 1]? :=
        hget_lt (r - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hcprev_eq : sb2[64 + (r - 1) * 256 + (s.scratch.scratch_buf[8256 + r * 256 + m]?.getD
          0#32).toNat]? = s.scratch.scratch_buf[64 + (r - 1) * 256 +
          (s.scratch.scratch_buf[8256 + r * 256 + m]?.getD 0#32).toNat]? := by
        have hqprev256 := (hmat.2.2.2 (r - 1) (by omega)).2.2.1
        exact hget_lt _ (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hpar_eq, hqprev_eq, hfprev_eq, hcprev_eq]
      exact ⟨hpi, m4BvaRowEntryOk_congr rfl rfl rfl hpok⟩
  · have hreq : r = step := by omega
    subst r; dsimp only; rw [hget_step, hget_32step]
    refine ⟨hbest_lt, hnq2, hnq256, fun nm hnm => ?_⟩
    obtain ⟨hpi, res, hres_lt, hres_nd, hpok, hok, hent_lt, hent_b⟩ := hnew nm hnm
    refine ⟨res, hres_lt, hres_nd, ?_, fun t ht => ?_, fun _ => ?_⟩
    · rw [hget_row nm (by omega)]; exact m4BvaRowEntryOk_congr rfl rfl rfl hok
    · by_cases hte : t < step
      · rw [hget_lt t (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hent_lt t hte
      · have hts : t = step := by omega
        subst hts; rw [hget_step]; exact hent_b
    · have hqprev256 := (hmat.2.2.2 (step - 1) (by omega)).2.2.1
      have hpar_eq := hget_par nm (by omega)
      have hqprev_eq : sb2[32 + (step - 1)]? = s.scratch.scratch_buf[32 + (step - 1)]? :=
        hget_lt (32 + (step - 1)) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hfprev_eq : sb2[step - 1]? = s.scratch.scratch_buf[step - 1]? :=
        hget_lt (step - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hcprev_eq : sb2[64 + (step - 1) * 256 +
          (sb'[8256 + step * 256 + nm]?.getD 0#32).toNat]? =
          s.scratch.scratch_buf[64 + (step - 1) * 256 +
            (sb'[8256 + step * 256 + nm]?.getD 0#32).toNat]? :=
        hget_lt _ (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hpar_eq, hqprev_eq, hfprev_eq, hcprev_eq]
      exact ⟨hpi, m4BvaRowEntryOk_congr rfl rfl rfl hpok⟩

private theorem m4BvaMatrixInv_of_filter_pres {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState}
    {sb' : List (BitVec 32)} {step : Nat} (hstep32 : step < 32)
    (hmat : M4BvaMatrixInv c F_cur s step)
    (hpres : ∀ idx < c.scratch_cap,
      ¬ (64 + step * 256 ≤ idx ∧ idx < 64 + step * 256 + 256) →
      ¬ (8256 + step * 256 ≤ idx ∧ idx < 8256 + step * 256 + 256) →
      sb'[idx]? = s.scratch.scratch_buf[idx]?) :
    M4BvaMatrixInv c F_cur { s with scratch := { s.scratch with scratch_buf := sb' } } step := by
  have hcap := hmat.1
  refine ⟨hcap, hmat.2.1, hmat.2.2.1, fun r hr => ?_⟩
  obtain ⟨hfr, hq2, hq256, hm⟩ := hmat.2.2.2 r hr
  have hr_eq : sb'[r]? = s.scratch.scratch_buf[r]? :=
    hpres r (by omega) (by omega) (by omega)
  have h32_eq : sb'[32 + r]? = s.scratch.scratch_buf[32 + r]? :=
    hpres (32 + r) (by omega) (by omega) (by omega)
  dsimp only; rw [hr_eq, h32_eq]
  refine ⟨hfr, hq2, hq256, fun m hm_lt => ?_⟩
  obtain ⟨res, hres_lt, hres_nd, hok, hent, hpar⟩ := hm m hm_lt
  have hc_eq : sb'[64 + r * 256 + m]? = s.scratch.scratch_buf[64 + r * 256 + m]? :=
    hpres (64 + r * 256 + m) (by omega) (by omega) (by omega)
  refine ⟨res, hres_lt, hres_nd, ?_, fun t ht => ?_, fun hr0 => ?_⟩
  · rw [hc_eq]; exact m4BvaRowEntryOk_congr rfl rfl rfl hok
  · rw [hpres t (by omega) (by omega) (by omega)]; exact hent t ht
  · obtain ⟨hpi, hpok⟩ := hpar hr0
    have hp_eq : sb'[8256 + r * 256 + m]? = s.scratch.scratch_buf[8256 + r * 256 + m]? :=
      hpres (8256 + r * 256 + m) (by omega) (by omega) (by omega)
    have hqprev256 := (hmat.2.2.2 (r - 1) (by omega)).2.2.1
    rw [hp_eq, hpres (32 + (r - 1)) (by omega) (by omega) (by omega),
      hpres (r - 1) (by omega) (by omega) (by omega),
      hpres (64 + (r - 1) * 256 + (s.scratch.scratch_buf[8256 + r * 256 + m]?.getD 0#32).toNat)
        (by omega) (by omega) (by omega)]
    exact ⟨hpi, m4BvaRowEntryOk_congr rfl rfl rfl hpok⟩

private theorem m4_bv8_setWidth_and_fe (x : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x &&& 254#32) = x &&& 0xFE#8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  have hx := x.isLt
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hx)]

private theorem m4_bva_try_lit_clear_lm_step {sb : List (BitVec 32)} {lmi : List (BitVec 8)}
    {maxv si stepf : Nat} (hsi_lt : si < stepf) (hsi_sb : si < sb.length)
    (hlmi_l : lmi.length = 2 * maxv)
    (hxl_lt : (sb[si]'hsi_sb).toNat < 2 * maxv)
    (hlmi_hi : ∀ l < 2 * maxv, (lmi[l]?.getD 0#8 &&& 0xFE#8) = 0#8)
    (hlmi_only : ∀ l < 2 * maxv, (lmi[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
      ∃ r, si ≤ r ∧ r < stepf ∧ (sb[r]?.getD 0#32).toNat = l) :
    let xl := (sb[si]'hsi_sb).toNat
    let lmi' := lmi.set xl ((lmi[xl]'(by omega)) &&& 0xFE#8)
    (∀ l < 2 * maxv, (lmi'[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
    (∀ l < 2 * maxv, (lmi'[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
      ∃ r, si + 1 ≤ r ∧ r < stepf ∧ (sb[r]?.getD 0#32).toNat = l) := by
  intro xl lmi'
  refine ⟨fun l hl => ?_, fun l hl hne => ?_⟩
  · dsimp only [lmi']
    by_cases hlx : l = xl
    · subst hlx; rw [List.getElem?_set_self (by omega), Option.getD_some]
      have h0 := hlmi_hi xl hl
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
      rw [BitVec.and_assoc, show (0xFE#8 &&& 0xFE#8) = 0xFE#8 from by decide]; exact h0
    · rw [List.getElem?_set_ne (Ne.symm hlx)]; exact hlmi_hi l hl
  · dsimp only [lmi'] at hne
    by_cases hlx : l = xl
    · subst hlx; rw [List.getElem?_set_self (by omega), Option.getD_some] at hne
      rw [BitVec.and_assoc, show (0xFE#8 &&& 1#8) = 0#8 from by decide,
        BitVec.and_zero] at hne
      exact absurd rfl hne
    · rw [List.getElem?_set_ne (Ne.symm hlx)] at hne
      obtain ⟨r, hr1, hr2, heq⟩ := hlmi_only l hl hne
      have hne_r : r ≠ si := fun h => by
        subst h; dsimp only [xl] at hlx
        rw [List.getElem?_eq_getElem hsi_sb, Option.getD_some] at heq
        exact hlx heq.symm
      exact ⟨r, by omega, hr2, heq⟩

private theorem m4_bva_try_lit_clear_lm_done {c : FullCfg} {stf : FullState}
    {lmi : List (BitVec 8)} {stepf : Nat}
    (hmrk : ∀ v < c.max_vars, stf.core.mrk[v]?.getD 0#8 = 0#8)
    (hlmi_hi : ∀ l < 2 * c.max_vars, (lmi[l]?.getD 0#8 &&& 0xFE#8) = 0#8)
    (hlmi_only : ∀ l < 2 * c.max_vars, (lmi[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
      ∃ r, stepf ≤ r ∧ r < stepf ∧ (stf.scratch.scratch_buf[r]?.getD 0#32).toNat = l) :
    FullLitMarksClear c { stf with core := { stf.core with lit_mark := lmi } } := by
  refine ⟨hmrk, fun l hl => ?_⟩
  have hhi := hlmi_hi l hl
  have hlo : (lmi[l]?.getD 0#8 &&& 1#8) = 0#8 := by
    apply Classical.byContradiction; intro hne
    obtain ⟨r, hr1, hr2, _⟩ := hlmi_only l hl hne; omega
  have hcomb : (lmi[l]?.getD 0#8 &&& 0xFE#8) ||| (lmi[l]?.getD 0#8 &&& 1#8) =
      lmi[l]?.getD 0#8 := by
    rw [← BitVec.and_or_distrib_left,
      show (0xFE#8 ||| 1#8) = 0xFF#8 from by decide,
      show ∀ x : BitVec 8, x &&& 0xFF#8 = x from fun x => by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_and]
        have := x.isLt; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 8 |>.trans
          (Nat.mod_eq_of_lt this)]
  rw [← hcomb, hhi, hlo]; decide

private theorem m4_bva_try_lit_extend_lm {maxv cap step : Nat}
    {lm : List (BitVec 8)} {sb2 sb3 : List (BitVec 32)} {bl new_qn : BitVec 32}
    (hcap : 16448 ≤ cap) (hstep32 : step < 32)
    (hlm_l : lm.length = 2 * maxv) (hsb3_l : sb3.length = cap)
    (hbl_lt : bl.toNat < 2 * maxv)
    (hpres : ∀ idx < cap,
      ¬ (64 + step * 256 ≤ idx ∧ idx < 64 + step * 256 + 256) →
      ¬ (8256 + step * 256 ≤ idx ∧ idx < 8256 + step * 256 + 256) →
      sb3[idx]? = sb2[idx]?)
    (hhi : ∀ l < 2 * maxv, (lm[l]?.getD 0#8 &&& 0xFE#8) = 0#8)
    (hset : ∀ r < step, (lm[(sb2[r]?.getD 0#32).toNat]?.getD 0#8 &&& 1#8) ≠ 0#8)
    (honly : ∀ l < 2 * maxv, (lm[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
      ∃ r < step, (sb2[r]?.getD 0#32).toNat = l) :
    let lm4 := lm.set bl.toNat 1#8
    let sb4 := (sb3.set step bl).set (32 + step) new_qn
    (∀ l < 2 * maxv, (lm4[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
    (∀ r < step + 1, (lm4[(sb4[r]?.getD 0#32).toNat]?.getD 0#8 &&& 1#8) ≠ 0#8) ∧
    (∀ l < 2 * maxv, (lm4[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
      ∃ r < step + 1, (sb4[r]?.getD 0#32).toNat = l) := by
  intro lm4 sb4
  refine ⟨fun l hl => ?_, fun r hr => ?_, fun l hl hne => ?_⟩
  · dsimp only [lm4]
    by_cases hlb : l = bl.toNat
    · subst hlb; rw [List.getElem?_set_self (by omega), Option.getD_some]; decide
    · rw [List.getElem?_set_ne (Ne.symm hlb)]; exact hhi l hl
  · dsimp only [lm4, sb4]
    by_cases hrs : r < step
    · have hreq : ((sb3.set step bl).set (32 + step) new_qn)[r]? = sb2[r]? := by
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hpres r (by omega) (by omega) (by omega)
      rw [hreq]
      by_cases hlb : (sb2[r]?.getD 0#32).toNat = bl.toNat
      · rw [hlb, List.getElem?_set_self (by omega), Option.getD_some]; decide
      · rw [List.getElem?_set_ne (Ne.symm hlb)]; exact hset r hrs
    · have hr_eq : r = step := by omega
      subst r
      have hsb_st : ((sb3.set step bl).set (32 + step) new_qn)[step]?.getD 0#32 = bl := by
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
      rw [hsb_st, List.getElem?_set_self (by omega), Option.getD_some]; decide
  · dsimp only [lm4, sb4] at hne ⊢
    by_cases hlb : l = bl.toNat
    · subst hlb; refine ⟨step, by omega, ?_⟩
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
    · rw [List.getElem?_set_ne (Ne.symm hlb)] at hne
      obtain ⟨r, hr, heq⟩ := honly l hl hne
      refine ⟨r, by omega, ?_⟩
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        hpres r (by omega) (by omega) (by omega)]
      exact heq

private theorem m4_bva_try_lit_lm1_init {maxv cap : Nat} {sb : List (BitVec 32)}
    {lm : List (BitVec 8)} {f0 qn : BitVec 32}
    (hcap : 16448 ≤ cap) (hsb_l : sb.length = cap) (hlm_l : lm.length = 2 * maxv)
    (hf0_lt : f0.toNat < 2 * maxv)
    (hlm_zero : ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8) :
    let sb1 := (sb.set 0 f0).set 32 qn
    let lm1 := lm.set f0.toNat 1#8
    (∀ l < 2 * maxv, (lm1[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
    (∀ r < 1, (lm1[(sb1[r]?.getD 0#32).toNat]?.getD 0#8 &&& 1#8) ≠ 0#8) ∧
    (∀ l < 2 * maxv, (lm1[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
      ∃ r < 1, (sb1[r]?.getD 0#32).toNat = l) := by
  intro sb1 lm1
  have hs0 : sb1[0]?.getD 0#32 = f0 := by
    dsimp only [sb1]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
  refine ⟨fun l hl => ?_, fun r hr => ?_, fun l hl hne => ?_⟩
  · dsimp only [lm1]
    by_cases hlf : l = f0.toNat
    · subst hlf; rw [List.getElem?_set_self (by omega), Option.getD_some]; decide
    · rw [List.getElem?_set_ne (Ne.symm hlf), hlm_zero l hl]; decide
  · have hr0 : r = 0 := by omega
    subst hr0; rw [hs0]; dsimp only [lm1]
    rw [List.getElem?_set_self (by omega), Option.getD_some]; decide
  · dsimp only [lm1] at hne
    by_cases hlf : l = f0.toNat
    · subst hlf; exact ⟨0, by omega, by rw [hs0]⟩
    · rw [List.getElem?_set_ne (Ne.symm hlf), hlm_zero l hl] at hne; exact absurd rfl hne

private def BvaTouchedInv (c : FullCfg) (stc : FullState) (R : Mem 64 → Prop)
    (nt : BitVec 64) (st : FullState) (m : Mem 64) : Prop :=
  st.core = stc.core ∧
  st.scratch.scratch_buf = stc.scratch.scratch_buf ∧
  st.scratch.tarjan_mark = stc.scratch.tarjan_mark ∧
  st.scratch.tarjan_reach = stc.scratch.tarjan_reach ∧
  st.scratch.last_learned = stc.scratch.last_learned ∧
  st.scratch.extend_len = stc.scratch.extend_len ∧
  st.scratch.LengthsOk c ∧
  nt.toNat ≤ 2 * stc.core.cur_vars ∧
  (∀ k < nt.toNat, (st.scratch.work_stk2[k]?.getD 0#32).toNat < 2 * stc.core.cur_vars) ∧
  (FullMem c st ⋆ R) m

private theorem bva_touched_push {c : FullCfg} {stc st : FullState} {R : Mem 64 → Prop}
    {nt : BitVec 64} {m : Mem 64} {l : BitVec 32} {idx : Nat}
    (hcv_le : stc.core.cur_vars ≤ c.max_vars) (hmx : c.max_vars < 2 * 2 ^ 28)
    (hnt_lt : nt.toNat < 2 * stc.core.cur_vars) (hl_lt : l.toNat < 2 * stc.core.cur_vars)
    (hcore : st.core = stc.core) (hsb : st.scratch.scratch_buf = stc.scratch.scratch_buf)
    (htm : st.scratch.tarjan_mark = stc.scratch.tarjan_mark)
    (htr : st.scratch.tarjan_reach = stc.scratch.tarjan_reach)
    (hll : st.scratch.last_learned = stc.scratch.last_learned)
    (hel : st.scratch.extend_len = stc.scratch.extend_len)
    (hscl : st.scratch.LengthsOk c)
    (hws2_ok : ∀ k < nt.toNat,
      (st.scratch.work_stk2[k]?.getD 0#32).toNat < 2 * stc.core.cur_vars)
    (hm : (FullMem c { st with scratch := { st.scratch with
      wsort := st.scratch.wsort.set idx 1#32,
      work_stk2 := st.scratch.work_stk2.set nt.toNat l } } ⋆ R) m) :
    BvaTouchedInv c stc R (nt + 1#64) { st with scratch := { st.scratch with
      wsort := st.scratch.wsort.set idx 1#32,
      work_stk2 := st.scratch.work_stk2.set nt.toNat l } } m := by
  have hws_l := hscl.wsort_len
  have hws2_l := hscl.work_stk2_len
  have hnt1 : (nt + 1#64).toNat = nt.toNat + 1 := by simp only [bv_c0]; omega
  refine ⟨hcore, hsb, htm, htr, hll, hel,
    { hscl with wsort_len := by simp [hws_l], work_stk2_len := by simp [hws2_l] },
    by omega, fun k hk => ?_, hm⟩
  rw [hnt1] at hk
  by_cases hkn : k = nt.toNat
  · subst hkn; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hl_lt
  · rw [List.getElem?_set_ne (Ne.symm hkn)]; exact hws2_ok k (by omega)

private theorem bva_touched_clear_step {c : FullCfg} {stc stm stz : FullState}
    {R : Mem 64 → Prop} {ntm tz : BitVec 64} {m : Mem 64} {idx : Nat}
    (htz_lt : tz.toNat < ntm.toNat) (htz1 : (tz + 1#64).toNat = tz.toNat + 1)
    (hcorez : stz.core = stc.core) (hsbz : stz.scratch.scratch_buf = stc.scratch.scratch_buf)
    (htmz : stz.scratch.tarjan_mark = stc.scratch.tarjan_mark)
    (htrz : stz.scratch.tarjan_reach = stc.scratch.tarjan_reach)
    (hllz : stz.scratch.last_learned = stc.scratch.last_learned)
    (helz : stz.scratch.extend_len = stc.scratch.extend_len)
    (hws2z : stz.scratch.work_stk2 = stm.scratch.work_stk2)
    (hsclz : stz.scratch.LengthsOk c)
    (hm : (FullMem c { stz with scratch :=
      { stz.scratch with wsort := stz.scratch.wsort.set idx 0#32 } } ⋆ R) m) :
    ∃ stz' : FullState, (tz + 1#64).toNat ≤ ntm.toNat ∧ stz'.core = stc.core ∧
      stz'.scratch.scratch_buf = stc.scratch.scratch_buf ∧
      stz'.scratch.tarjan_mark = stc.scratch.tarjan_mark ∧
      stz'.scratch.tarjan_reach = stc.scratch.tarjan_reach ∧
      stz'.scratch.last_learned = stc.scratch.last_learned ∧
      stz'.scratch.extend_len = stc.scratch.extend_len ∧
      stz'.scratch.work_stk2 = stm.scratch.work_stk2 ∧
      stz'.scratch.LengthsOk c ∧ (FullMem c stz' ⋆ R) m :=
  ⟨{ stz with scratch := { stz.scratch with wsort := stz.scratch.wsort.set idx 0#32 } },
   by rw [htz1]; exact htz_lt, hcorez, hsbz, htmz, htrz, hllz, helz, hws2z,
   { hsclz with wsort_len := by rw [List.length_set, hsclz.wsort_len] }, hm⟩

private theorem bva_bv64_add2_mod {x : BitVec 32} :
    (x.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = x.toNat + 2 := by
  rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega

private theorem bva_bv32_step_row_n {step : BitVec 32} (h1 : 1 ≤ step.toNat)
    (h2 : step.toNat < 32) :
    ((64 : BitVec 32) + (step - 1) * 256).toNat = 64 + (step.toNat - 1) * 256 := by
  simp only [BitVec.toNat_add, BitVec.toNat_mul,
    BitVec.toNat_sub_of_le (show (1 : BitVec 32).toNat ≤ step.toNat from h1),
    show (64 : BitVec 32).toNat = 64 from rfl, show (256 : BitVec 32).toNat = 256 from rfl,
    show (1 : BitVec 32).toNat = 1 from rfl]; omega

private theorem bva_bv32_nrow_n {step : BitVec 32} (h : step.toNat < 32) :
    ((64 : BitVec 32) + step * 256).toNat = 64 + step.toNat * 256 := by
  simp only [BitVec.toNat_add, BitVec.toNat_mul, show (64 : BitVec 32).toNat = 64 from rfl,
    show (256 : BitVec 32).toNat = 256 from rfl]; omega

private theorem bva_bv32_par_n {step : BitVec 32} (h : step.toNat < 32) :
    ((8256 : BitVec 32) + step * 256).toNat = 8256 + step.toNat * 256 := by
  simp only [BitVec.toNat_add, BitVec.toNat_mul, show (8256 : BitVec 32).toNat = 8256 from rfl,
    show (256 : BitVec 32).toNat = 256 from rfl]; omega

private theorem bva_bv32_add1_n {x : BitVec 32} (h : x.toNat < 1000) :
    (x + 1#32).toNat = x.toNat + 1 := by simp only [bv_c0]; omega

private theorem bva_bv32_32add_n {x : BitVec 32} (h : x.toNat < 32) :
    ((32 : BitVec 32) + x).toNat = 32 + x.toNat := by
  change (32#32 + x).toNat = _; simp only [bv_c0]; omega

private theorem bva_bv32_row_idx_n {bk tm : BitVec 32} (hbk : bk.toNat < 32)
    (htm : tm.toNat < 256) :
    (64 + bk * 256 + tm).toNat = 64 + bk.toNat * 256 + tm.toNat := by
  change (64#32 + bk * 256#32 + tm).toNat = _; simp only [bv_c0]; omega

private theorem bva_bv32_row_mod_n {bk tm : BitVec 32} (hbk : bk.toNat < 32)
    (htm : tm.toNat < 256) :
    ((64 : BitVec 32).toNat + bk.toNat * (256 : BitVec 32).toNat + tm.toNat) % 2 ^ 32 =
      64 + bk.toNat * 256 + tm.toNat := by
  change (64 + bk.toNat * 256 + tm.toNat) % 2 ^ 32 = _; omega

private theorem bva_bv64_add2_n {ct : BitVec 32} :
    (BitVec.setWidth 64 ct + 2).toNat = ct.toNat + 2 := by
  change (BitVec.setWidth 64 ct + 2#64).toNat = _; simp only [bv_c0]; omega

private theorem bva_bv64_add3_n {ct tj : BitVec 32} :
    (BitVec.setWidth 64 ct + 3 + BitVec.setWidth 64 tj).toNat = ct.toNat + 3 + tj.toNat := by
  change (BitVec.setWidth 64 ct + 3#64 + BitVec.setWidth 64 tj).toNat = _; simp only [bv_c0]; omega

private theorem bva_bv64_add1_n {tz : BitVec 64} (h : tz.toNat < 4 * 2 ^ 28) :
    (tz + 1#64).toNat = tz.toNat + 1 := by simp only [bv_c0]; omega

end M4BvaTryLitHelpers

theorem m4_bva_try_lit_wp (Γ : Env)
    (hScan : ∀ args m Q X, m4BvaScanCandsSpec args m Q X →
      Γ "full_bva_scan_cands" [i64, i32, i32, i64] [i32] args m Q X)
    (hPick : ∀ args m Q X, fullBvaPickCandSpec args m Q X →
      Γ "full_bva_pick_cand" [i64, i32, i32] [i32] args m Q X)
    (hFilter : ∀ args m Q X, m4BvaFilterRowSpec args m Q X →
      Γ "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32] args m Q X)
    (hCommit : ∀ args m Q X, m4BvaCommitSpec args m Q X →
      Γ "full_bva_commit" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullBvaTryLitHeapSpec args m Q X →
      Func.wp Γ full_bva_try_lit_body args m Q X := by
  rintro ⟨h, f0, init_cv0, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv0, hf0_lt, hm, hQ⟩
  obtain ⟨F_cur, hinv⟩ := hinv0.exists_witness
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len
  have hws_len := hcl.wstk_len_arr; have har_len := hcl.arena_len_arr
  have hwlen_le := hcl.wlen_le; have hal_le := hcl.arena_len_le
  have hsb_len := hsc.scratch_buf_len; have hlm_len := hcl.lit_mark_len
  have hvals_len := hcl.vals_len
  c0_hsteps_nogrp
  · exact hQ false s m hinv.toDense (Nat.le_refl _) rfl rfl rfl hm
  · exact hQ false s m hinv.toDense (Nat.le_refl _) rfl rfl rfl hm
  · exact hQ false s m hinv.toDense (Nat.le_refl _) rfl rfl rfl hm
  · have hcv_lt_mx : s.core.cur_vars < c.max_vars := by
      have h1 : ¬ c.max_vars % 2 ^ 64 ≤ s.core.cur_vars % 2 ^ 64 := by assumption
      omega
    have hcap_ge : 16448 ≤ c.scratch_cap := by
      have h1 : ¬ c.scratch_cap % 2 ^ 64 < (16448 : BitVec 64).toNat := by assumption
      change ¬ c.scratch_cap % 2 ^ 64 < 16448 at h1; omega
    refine wp_join_state1 (t := i64) (α := BitVec 64) (fun x => x)
      (fun icv micv => icv.toNat ≤ s.core.cur_vars ∧ micv = m)
      (fun _ init_cv micv ⟨hicv_le, hmicv⟩ => ?_)
      (fun Jicv hJicv => ?_)
    · rcases hmicv.symm with rfl
      have hdw : DenseWatchesInv F_cur s.core := by
        have h := hinv.2.1.watches; unfold ModeWatchesInv at h
        rwa [ite_eq_right hinv.2.2.2.2.2.2] at h
      have hbd_f0 := hdw.layout.bounds f0.toNat hf0_lt
      have hslice_f0 := hdw.slices f0.toNat hf0_lt
      have h2f0 : (BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat = 2 * f0.toNat := by
        rw [bv64_shl1_nat, bv64_setWidth_32]; omega
      have h2f1 : ((BitVec.setWidth 64 f0 <<< (1 : Nat)) + 1).toNat = 2 * f0.toNat + 1 := by
        change (BitVec.setWidth 64 f0 <<< (1 : Nat) + 1#64).toNat = _
        rw [BitVec.toNat_add, h2f0, show (1#64).toNat = 1 from rfl]; omega
      have hwv_f0 : (BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat < s.core.wvec.length := by
        rw [h2f0]; omega
      have hwv_f1 : ((BitVec.setWidth 64 f0 <<< (1 : Nat)) + 1).toNat <
          s.core.wvec.length := by
        rw [h2f1]; omega
      have hoff_eq : (s.core.wvec[2 * f0.toNat]'(by omega)).toNat =
          fullWatchOffCore s.core f0.toNat := by
        unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hsz_eq : (s.core.wvec[2 * f0.toNat + 1]'(by omega)).toNat =
          fullWatchSizeCore s.core f0.toNat := by
        unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      let off0 := fullWatchOffCore s.core f0.toNat
      let sz0 := fullWatchSizeCore s.core f0.toNat
      have hoff_sz_le : off0 + sz0 ≤ s.core.wlen := hbd_f0
      have hoff_c0 : (BitVec.setWidth 64
          (s.core.wvec[(BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat]'hwv_f0)).toNat = off0 := by
        rw [bv64_setWidth_32]; simp only [h2f0]; exact hoff_eq
      have hmod0 : 2 * f0.toNat % 2 ^ 64 = 2 * f0.toNat := Nat.mod_eq_of_lt (by omega)
      have hmod1 : (2 * f0.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * f0.toNat + 1 := by
        rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
      have hend_mod : ((s.core.wvec[2 * f0.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
          (s.core.wvec[(2 * f0.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
            rw [hmod1]; omega)).toNat) % 2 ^ 64 = off0 + sz0 := by
        simp only [hmod0, hmod1, hoff_eq, hsz_eq]; exact Nat.mod_eq_of_lt (by omega)
      c0_hsteps_nogrp
      -- Row-0 collection loop `while (p < end && qn < 256u)`
      refine wp_loop_inv
        (fun (qn, p, ()) mp => ∃ sb : List (BitVec 32),
          off0 ≤ p.toNat ∧ p.toNat ≤ off0 + sz0 ∧ qn.toNat ≤ 256 ∧
          sb.length = c.scratch_cap ∧
          DenseWatchSliceOk F_cur s.core f0.toNat p.toNat (off0 + sz0 - p.toNat) ∧
          (∀ i < qn.toNat, ∃ res : List Nat,
            (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
            M4BvaRowEntryOk F_cur s f0.toNat (sb[64 + i]?.getD 0#32) res ∧
            (cnfOfClauses F_cur).EntailsClause (cnfClause (f0.toNat :: res))) ∧
          (FullMem c { s with scratch := { s.scratch with scratch_buf := sb } } ⋆ R) mp)
        (fun (_, p, _) _ => off0 + sz0 - p.toNat)
        (fun Jp hJp => by
          c0_hfast
          exact hJp (0#32, _, ()) m ⟨s.scratch.scratch_buf,
            by rw [hoff_c0]; exact Nat.le_refl _, by rw [hoff_c0]; omega, by decide, hsb_len,
            by rw [hoff_c0, Nat.add_sub_cancel_left]; exact hslice_f0,
            fun _ h => by simp only [bv_c0] at h; omega, hm⟩)
        (fun Jp (qn, p, ()) mp ⟨sb, hp_ge, hp_le, hqn_le, hsb_l, hrem, hrow0, hmp⟩ ihp => ?_)
      c0_hsteps_nogrp
      refine wp_join_state0 (α := Unit)
        (fun _ mf => mf = mp)
        (fun _ _ mf hmf => ?_)
        (fun Jend hJend => ?_)
      rotate_left
      · c0_hsplit
        · c0_hsplit
          · have hp_lt : p.toNat < off0 + sz0 := by rw [← hend_mod]; assumption
            have hqn_lt : qn.toNat < 256 := by
              have h1 : qn.toNat < (256 : BitVec 32).toNat := by assumption
              exact h1
            have hp_ws : p.toNat < s.core.wstk.length := by omega
            have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by simp only [bv_c0]; omega
            have hp1_mod : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
              rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
            have hqn1_n : (qn + 1#32).toNat = qn.toNat + 1 := by simp only [bv_c0]; omega
            have h64qn : ((64 : BitVec 32) + qn).toNat = 64 + qn.toNat := by
              simp only [BitVec.toNat_add, show (64 : BitVec 32).toNat = 64 from rfl]; omega
            have h64qn_sb : (BitVec.setWidth 64 ((64 : BitVec 32) + qn)).toNat < sb.length := by
              rw [bv64_setWidth_32, h64qn, hsb_l]; omega
            c0_hsteps_nogrp
            c0_hstep
            c0_hsplit
            · have hbin : (s.core.wstk[p.toNat]'hp_ws &&& 0x80000000#32) ≠ 0#32 := by assumption
              have ⟨hot_lt, hent_ot, hrem_next⟩ :=
                FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hp_ws hbin
              have hot_v : (BitVec.setWidth 64
                  (s.core.wstk[p.toNat]'hp_ws &&& 0x7FFFFFFF#32)).toNat < s.core.vals.length := by
                rw [bv64_setWidth_32]; omega
              c0_hfast
              · refine ihp (qn + 1#32, p + 1#64, ()) _ (by dsimp only; rw [hp1_n]; omega)
                  ⟨sb.set (64 + qn.toNat) (s.core.wstk[p.toNat]'hp_ws),
                   by rw [hp1_n]; omega, by rw [hp1_n]; omega, by rw [hqn1_n]; omega,
                   by simp [hsb_l],
                   by rw [hp1_n, show off0 + sz0 - (p.toNat + 1) = off0 + sz0 - p.toNat - 1
                        by omega]; exact hrem_next, fun i hi => ?_, ?_⟩
                · rw [hqn1_n] at hi
                  by_cases hie : i = qn.toNat
                  · subst hie
                    refine ⟨[(s.core.wstk[p.toNat]'hp_ws &&& 0x7FFFFFFF#32).toNat],
                      fun x hx => by simp at hx; subst hx; exact hot_lt,
                      by simp, ?_, hent_ot⟩
                    rw [List.getElem?_set_self (by omega), Option.getD_some]
                    unfold M4BvaRowEntryOk; rw [ite_eq_left hbin]
                    exact ⟨hot_lt, rfl, hent_ot⟩
                  · rw [List.getElem?_set_ne (by omega)]; exact hrow0 i (by omega)
                · simp only [bv64_setWidth_32, h64qn] at hm; exact hm
              · exact ihp (qn, p + 1#64, ()) mp (by dsimp only; rw [hp1_n]; omega)
                  ⟨sb, by rw [hp1_n]; omega, by rw [hp1_n]; omega, hqn_le, hsb_l,
                   by rw [hp1_n, show off0 + sz0 - (p.toNat + 1) = off0 + sz0 - p.toNat - 1
                        by omega]; exact hrem_next, hrow0, hmp⟩
            · have hbin0 : (s.core.wstk[p.toNat]'hp_ws &&& 0x80000000#32) = 0#32 := by assumption
              have ⟨h2le, hrem_next⟩ :=
                FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws hbin0
              have hp1_ws : p.toNat + 1 < s.core.wstk.length := by omega
              have ⟨_, hcr_ref, _⟩ :=
                FullBvaFwdHelpers.fwd_slice_occ_info hrem (by omega) hp_ws hp1_ws hbin0
              have hcr_wf := hinv.2.1.arena.refs_wf _ hcr_ref
              have hp2_n : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by simp only [bv_c0]; omega
              let cr := s.core.wstk[p.toNat + 1]'hp1_ws
              have hcr_al : cr.toNat + 3 + fullArenaClauseSizeCore s.core cr.toNat ≤
                  s.core.arena_len := by
                have h1 := hcr_wf.2.2.1; have h2 := hcr_wf.2.2.2.1; dsimp only [cr]; omega
              have hcr_eq :
                  s.core.wstk[(p + 1#64).toNat]'(by rw [hp1_n]; exact hp1_ws) = cr := by
                dsimp only [cr]; simp only [hp1_n]
              have hcr_mod :
                  s.core.wstk[(p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                    rw [hp1_mod]; exact hp1_ws) = cr := by dsimp only [cr]; simp only [hp1_mod]
              have hcr_b0 : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1#64).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat <
                  s.core.arena.length := by rw [bv64_setWidth_32, hcr_eq]; omega
              have hcr2_eq : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1#64).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat =
                  cr.toNat + 2 := by
                change (BitVec.setWidth 64 _ + 2#64).toNat = _
                rw [hcr_eq]; simp only [bv_c0]; omega
              have hcr_b2 : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1#64).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat <
                  s.core.arena.length := by rw [hcr2_eq]; omega
              have hsz_cr : (s.core.arena[cr.toNat + 2]'(by omega)).toNat =
                  fullArenaClauseSizeCore s.core cr.toNat := by
                unfold fullArenaClauseSizeCore
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hcr_sz_le : cr.toNat + 3 + (s.core.arena[cr.toNat + 2]'(by omega)).toNat ≤
                  s.core.arena.length := by rw [hsz_cr]; omega
              have hcr2_mod :
                  (cr.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = cr.toNat + 2 := by
                rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
              c0_hsteps_nogrp
              c0_hstep
              c0_hsteps_nogrp
              c0_hstep
              c0_hsteps_nogrp
              · have hng_cr : fullArenaClauseGarbCore s.core cr.toNat = false := by
                  unfold fullArenaClauseGarbCore fullArenaHdrCore
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  have h1 : s.core.arena[(s.core.wstk[(p.toNat +
                      BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                        rw [hp1_mod]; exact hp1_ws)).toNat]'(by rw [hcr_mod]; omega) &&&
                      ((524288 : BitVec 32) ||| 4194304) = 0 := by assumption
                  simp only [hcr_mod] at h1
                  exact FullBvaFwdHelpers.garb_false_of_and_garb_red_eq_zero h1
                have hsz3 : 3 ≤ fullArenaClauseSizeCore s.core cr.toNat := by
                  rw [← hsz_cr]
                  have h1 : (3 : BitVec 32).toNat ≤ (s.core.arena[((s.core.wstk[(p.toNat +
                      BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                        rw [hp1_mod]; exact hp1_ws)).toNat +
                      BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                        rw [hcr_mod, hcr2_mod]; omega)).toNat := by assumption
                  simp only [hcr_mod, hcr2_mod] at h1; exact h1
                have hsz256 : fullArenaClauseSizeCore s.core cr.toNat ≤ 256 := by
                  rw [← hsz_cr]
                  have h1 : (s.core.arena[((s.core.wstk[(p.toNat +
                      BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                        rw [hp1_mod]; exact hp1_ws)).toNat +
                      BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                        rw [hcr_mod, hcr2_mod]; omega)).toNat ≤ (256 : BitVec 32).toNat := by
                    assumption
                  simp only [hcr_mod, hcr2_mod] at h1; exact h1
                refine wp_join_state (α := BitVec 32 × Bool × Bool)
                  (fun ⟨hkf, hf, sf⟩ => (hkf, hf, sf, ()))
                  (fun ⟨_, hf, _⟩ mhf =>
                    (hf = true → f0.toNat ∈ fullArenaClauseLitsCore s.core cr.toNat) ∧ mhf = mp)
                  (fun _ ⟨_, has_f0, sat⟩ mhf ⟨hhf_ok, hmhf⟩ => ?_)
                  (fun Jhf hJhf => ?_)
                · subst mhf
                  c0_hfast
                  · exact ihp (qn, p + 1#64 + 1#64, ()) mp (by dsimp only; rw [hp2_n]; omega)
                      ⟨sb, by rw [hp2_n]; omega, by rw [hp2_n]; omega, hqn_le, hsb_l,
                       by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                            by omega]; exact hrem_next, hrow0, hmp⟩
                  · obtain ⟨res, hres_lt, hres_nd, hok, hent⟩ :=
                      m4BvaRowEntryOk_of_large_f0 hinv hcr_ref hng_cr hsz3 hsz256
                        (hhf_ok (by assumption))
                    refine ihp (qn + 1#32, p + 1#64 + 1#64, ()) _
                      (by dsimp only; rw [hp2_n]; omega)
                      ⟨sb.set (64 + qn.toNat) cr,
                       by rw [hp2_n]; omega, by rw [hp2_n]; omega, by rw [hqn1_n]; omega,
                       by simp [hsb_l],
                       by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                            by omega]; exact hrem_next, fun i hi => ?_, ?_⟩
                    · rw [hqn1_n] at hi
                      by_cases hie : i = qn.toNat
                      · subst hie
                        rw [List.getElem?_set_self (by omega), Option.getD_some]
                        exact ⟨res, hres_lt, hres_nd, hok, hent⟩
                      · rw [List.getElem?_set_ne (by omega)]; exact hrow0 i (by omega)
                    · simp only [bv64_setWidth_32, h64qn, show (1 : BitVec 64) = 1#64 from rfl,
                        hcr_eq] at hm
                      exact hm
                  · exact ihp (qn, p + 1#64 + 1#64, ()) mp (by dsimp only; rw [hp2_n]; omega)
                      ⟨sb, by rw [hp2_n]; omega, by rw [hp2_n]; omega, hqn_le, hsb_l,
                       by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                            by omega]; exact hrem_next, hrow0, hmp⟩
                · clear hQ
                  refine wp_loop_inv
                    (fun (hk, hf, ()) mhk =>
                      hk.toNat ≤ (s.core.arena[cr.toNat + 2]'(by omega)).toNat ∧
                      (hf = true → f0.toNat ∈ fullArenaClauseLitsCore s.core cr.toNat) ∧
                      mhk = mp)
                    (fun (hk, _, _) _ => (s.core.arena[cr.toNat + 2]'(by omega)).toNat - hk.toNat)
                    (fun Jhk hJhk => by
                      c0_hfast
                      exact hJhk (0#32, false, ()) mp
                        ⟨Nat.zero_le _, (fun h => by cases h), rfl⟩)
                    (fun Jhk (hk, hf, ()) mhk ⟨hhk_le, hhf_in, hmhk⟩ ihhk => ?_)
                  subst mhk; c0_hsplit
                  · have hhk_lt : hk.toNat < (s.core.arena[cr.toNat + 2]'(by omega)).toNat := by
                      have h1 : hk.toNat < (s.core.arena[(BitVec.setWidth 64
                          (s.core.wstk[(p + 1#64).toNat]'(by rw [hp1_n]; exact hp1_ws)) +
                          2).toNat]'hcr_b2).toNat := by assumption
                      simpa only [hcr2_eq] using h1
                    have hcrk_eq : (BitVec.setWidth 64
                        (s.core.wstk[(p + 1#64).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 3 +
                        BitVec.setWidth 64 hk).toNat = cr.toNat + 3 + hk.toNat := by
                      change (BitVec.setWidth 64 _ + 3#64 + BitVec.setWidth 64 hk).toNat = _
                      rw [hcr_eq]; simp only [bv_c0]; omega
                    have hcrk_b : (BitVec.setWidth 64
                        (s.core.wstk[(p + 1#64).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 3 +
                        BitVec.setWidth 64 hk).toNat < s.core.arena.length := by
                      rw [hcrk_eq]; omega
                    have hmem_hl : (s.core.arena[cr.toNat + 3 + hk.toNat]'(by omega)).toNat ∈
                        fullArenaClauseLitsCore s.core cr.toNat :=
                      List.mem_of_getElem? (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem
                        (k := s.core) (r := cr.toNat) (j := hk.toNat)
                        (by rw [← hsz_cr]; exact hhk_lt) (by omega))
                    have hhl_lt : (s.core.arena[cr.toNat + 3 + hk.toNat]'(by omega)).toNat <
                        2 * s.core.cur_vars :=
                      hinv.2.1.arena.lits_lt cr.toNat hcr_ref hng_cr _ hmem_hl
                    have hhl_vals : (BitVec.setWidth 64
                        (s.core.arena[(BitVec.setWidth 64
                          (s.core.wstk[(p + 1#64).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 3 +
                          BitVec.setWidth 64 hk).toNat]'hcrk_b)).toNat < s.core.vals.length := by
                      rw [bv64_setWidth_32]; simp only [hcrk_eq]; omega
                    have hhk1 : (hk + 1#32).toNat = hk.toNat + 1 := by simp only [bv_c0]; omega
                    c0_hsplit
                    · c0_hfast; exact hJhf ⟨hk, hf, true⟩ mp ⟨hhf_in, rfl⟩
                    · c0_hfast
                      · refine ihhk (hk + 1#32, true, ()) mp (by dsimp only; rw [hhk1]; omega)
                          ⟨by rw [hhk1]; omega, fun _ => ?_, rfl⟩
                        have hcrk_mod : (cr.toNat + BitVec.toNat (3 : BitVec 64) + hk.toNat) %
                            2 ^ 64 = cr.toNat + 3 + hk.toNat := by
                          rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
                        have heq : s.core.arena[cr.toNat + 3 + hk.toNat]'(by omega) = f0 := by
                          have h1 : s.core.arena[((s.core.wstk[(p.toNat +
                              BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                                rw [hp1_mod]; exact hp1_ws)).toNat +
                              BitVec.toNat (3 : BitVec 64) + hk.toNat) % 2 ^ 64]'(by
                                rw [hcr_mod, hcrk_mod]; omega) = f0 := by assumption
                          simpa only [hcr_mod, hcrk_mod] using h1
                        rwa [heq] at hmem_hl
                      · exact ihhk (hk + 1#32, hf, ()) mp (by dsimp only; rw [hhk1]; omega)
                          ⟨by rw [hhk1]; omega, hhf_in, rfl⟩
                  · c0_hfast; exact hJhf ⟨hk, hf, false⟩ mp ⟨hhf_in, rfl⟩
              all_goals
                exact ihp (qn, p + 1#64 + 1#64, ()) mp (by dsimp only; rw [hp2_n]; omega)
                  ⟨sb, by rw [hp2_n]; omega, by rw [hp2_n]; omega, hqn_le, hsb_l,
                   by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                        by omega]; exact hrem_next, hrow0, hmp⟩
          · exact hJend () mp rfl
        · exact hJend () mp rfl
      · subst mf
        c0_hsplit
        · c0_hfast
          exact hQ false _ mp
            (fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len)
              (sc' := { s.scratch with scratch_buf := sb }) hinv hcl.repr_len hcl.min_clr_len_arr
              hcl.tmp_len_arr hcl.flags_len hcl.tmp_len_le { hsc with scratch_buf_len := hsb_l }
              rfl rfl).toDense (Nat.le_refl _) rfl rfl rfl hmp
        · have hqn2 : 2 ≤ qn.toNat := by
            have h1 : ¬ qn.toNat < (2 : BitVec 32).toNat := by assumption
            change ¬ qn.toNat < 2 at h1; omega
          have hsb0_lt : (BitVec.ofNat 64 0).toNat < sb.length := by
            simp only [BitVec.toNat_ofNat]; rw [hsb_l]; omega
          have hsb32_lt : (BitVec.ofNat 64 32).toNat <
              (sb.set (BitVec.ofNat 64 0).toNat f0).length := by
            rw [List.length_set]; simp only [BitVec.toNat_ofNat]; rw [hsb_l]; omega
          have hlm_f0 : (BitVec.setWidth 64 f0).toNat < s.core.lit_mark.length := by
            rw [bv64_setWidth_32, hlm_len]; omega
          have hinit_lits : (init_cv <<< (1 : Nat)).toNat = 2 * init_cv.toNat := by
            rw [bv64_shl1_nat]; omega
          have hmat1 := m4BvaMatrixInv_step1 hcap_ge hsb_l hf0_lt hqn2 hqn_le hrow0
          let sb1 := (sb.set 0 f0).set 32 qn
          let lm1 := s.core.lit_mark.set f0.toNat 1#8
          have hsb1_l : sb1.length = c.scratch_cap := by simp [sb1, hsb_l]
          have hlm1_l : lm1.length = 2 * c.max_vars := by simp [lm1, hlm_len]
          have ⟨hlm1_hi, hlm1_set, hlm1_only⟩ := m4_bva_try_lit_lm1_init (f0 := f0) (qn := qn)
            hcap_ge hsb_l hlm_len (by omega) hinv.2.2.1.2
          have hinv1_core : FullState.LengthsOk c
              { core := { s.core with lit_mark := lm1 }
                scratch := { s.scratch with scratch_buf := sb1 } } :=
            ⟨{ hcl with lit_mark_len := hlm1_l }, { hsc with scratch_buf_len := hsb1_l }⟩
          c0_hsteps_nogrp
          refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 32 × BitVec 64 × FullState)
            (fun ⟨stepf, cur_qnf, bestkf, best_redf, _⟩ => (stepf, cur_qnf, bestkf, best_redf, ()))
            (fun ⟨stepf, _, bestkf, _, stf⟩ mf =>
              (FullMem c stf ⋆ R) mf ∧
              stf.LengthsOk c ∧ FullWitnessInv c F0 F_cur stf.core ∧
              FullArenaVarsNodup stf ∧ FullExtScratchOk c stf ∧
              stf.core.cur_level = 0 ∧ stf.core.dense_mode ≠ 0#64 ∧
              stf.core.cur_vars = s.core.cur_vars ∧ stf.core.fuel = s.core.fuel ∧
              stf.core.arena = s.core.arena ∧ stf.core.arena_len = s.core.arena_len ∧
              stf.core.mrk = s.core.mrk ∧
              stf.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
              stf.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
              1 ≤ stepf.toNat ∧ stepf.toNat ≤ 32 ∧
              M4BvaMatrixInv c F_cur stf stepf.toNat ∧
              (bestkf = 0#32 ∨ (1 ≤ bestkf.toNat ∧ bestkf.toNat < stepf.toNat)) ∧
              (∀ l < 2 * c.max_vars, (stf.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
              (∀ l < 2 * c.max_vars, (stf.core.lit_mark[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
                ∃ r < stepf.toNat, (stf.scratch.scratch_buf[r]?.getD 0#32).toNat = l))
            (fun _ ⟨stepf, _, bestkf, _, stf⟩ mf ⟨hmf, hlenf, hwf, hndf, hextf, hlv0f, hdmf, hcvf,
                hfuelf, harf, half, hmrkf, htmf, htrf, hst1, hst32, hmatf, hbkf, hlmf_hi,
                hlmf_only⟩ => ?_)
            (fun Jstep hJstep => ?_)
          · have hlmf_l := hlenf.core_ok.lit_mark_len
            have hsbf_l := hlenf.scratch_ok.scratch_buf_len
            refine wp_loop_inv
              (fun (si, ()) msi => ∃ lmi : List (BitVec 8),
                si.toNat ≤ stepf.toNat ∧ lmi.length = 2 * c.max_vars ∧
                (∀ l < 2 * c.max_vars, (lmi[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
                (∀ l < 2 * c.max_vars, (lmi[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
                  ∃ r, si.toNat ≤ r ∧ r < stepf.toNat ∧
                    (stf.scratch.scratch_buf[r]?.getD 0#32).toNat = l) ∧
                (FullMem c { stf with core := { stf.core with lit_mark := lmi } } ⋆ R) msi)
              (fun (si, _) _ => stepf.toNat - si.toNat)
              (fun Jsi hJsi => by
                c0_hfast
                exact hJsi (0#32, ()) mf ⟨stf.core.lit_mark, Nat.zero_le _, hlmf_l, hlmf_hi,
                  fun l hl hne => by
                    obtain ⟨r, hr, heq⟩ := hlmf_only l hl hne; exact ⟨r, Nat.zero_le _, hr, heq⟩,
                  hmf⟩)
              (fun Jsi (si, ()) msi ⟨lmi, hsi_le, hlmi_l, hlmi_hi, hlmi_only, hmsi⟩ ihsi => ?_)
            c0_hsplit
            · have hsi_lt : si.toNat < stepf.toNat := by assumption
              have hsi1 : (si + 1#32).toNat = si.toNat + 1 := by simp only [bv_c0]; omega
              have hscr_si_lt : (stf.scratch.scratch_buf[si.toNat]'(by omega)).toNat <
                  2 * stf.core.cur_vars := by
                have h1 := (hmatf.2.2.2 si.toNat hsi_lt).1
                rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
              have hsi_sb : (BitVec.setWidth 64 si).toNat < stf.scratch.scratch_buf.length := by
                rw [bv64_setWidth_32, hsbf_l]; omega
              have hscr_si_b : (BitVec.setWidth 64 (stf.scratch.scratch_buf[
                  (BitVec.setWidth 64 si).toNat]'hsi_sb)).toNat < lmi.length := by
                simp only [bv64_setWidth_32]; omega
              let xl := (stf.scratch.scratch_buf[si.toNat]'(by omega)).toNat
              c0_hsteps_nogrp
              have ⟨hhi', honly'⟩ := m4_bva_try_lit_clear_lm_step hsi_lt (by omega) hlmi_l
                (by omega) hlmi_hi hlmi_only
              refine ihsi (si + 1#32, ()) m (by dsimp only; rw [hsi1]; omega)
                ⟨lmi.set xl ((lmi[xl]'(by omega)) &&& 0xFE#8),
                 by rw [hsi1]; omega, by simp [hlmi_l], hhi',
                 by simpa only [hsi1] using honly',
                 by simp only [xl, bv64_setWidth_32, m4_bv8_setWidth_and_fe] at hm ⊢; exact hm⟩
            · have hsi_eq : si.toNat = stepf.toNat := by
                have h1 : ¬ si.toNat < stepf.toNat := by assumption
                omega
              have hlm_clr : FullLitMarksClear c
                  { stf with core := { stf.core with lit_mark := lmi } } :=
                m4_bva_try_lit_clear_lm_done
                  (fun v hv => by rw [hmrkf]; exact hinv.2.2.1.1 v hv)
                  hlmi_hi (by simpa only [hsi_eq] using hlmi_only)
              let st_clr : FullState := { stf with core := { stf.core with lit_mark := lmi } }
              have hinv_clr : FullDenseInvW c F0 F_cur st_clr :=
                ⟨⟨{ hlenf.core_ok with lit_mark_len := hlmi_l }, hlenf.scratch_ok⟩,
                 { hwf with
                   arena := { hwf.arena with len_ok := hwf.arena.len_ok }
                   watches := hwf.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
                 hlm_clr, hndf, hextf, hlv0f, hdmf⟩
              c0_hfast
              · exact hQ false st_clr msi hinv_clr.toDense (by dsimp only [st_clr]; omega)
                  hfuelf htmf htrf hmsi
              · rcases hbkf with h0 | ⟨hbk1, hbk_lt⟩
                · exact absurd h0 (by assumption)
                · have hmat_c : M4BvaMatrixInv c F_cur st_clr (bestkf.toNat + 1) :=
                    m4BvaMatrixInv_weaken_step (by omega) (by omega)
                      (m4BvaMatrixInv_congr rfl rfl rfl rfl hmatf)
                  have hbk_lt32 : bestkf.toNat < 32 := by omega
                  have hcv_c : st_clr.core.cur_vars = s.core.cur_vars := hcvf
                  have hcv_c_le : st_clr.core.cur_vars ≤ c.max_vars := hlenf.core_ok.cur_vars_le
                  have h2cv_c : (BitVec.ofNat 64 stf.core.cur_vars <<< (1 : Nat)).toNat =
                      2 * st_clr.core.cur_vars := by
                    rw [bv64_shl1_nat, BitVec.toNat_ofNat]; dsimp only [st_clr]; omega
                  have hdm_n : (bestkf + 1#32).toNat = bestkf.toNat + 1 :=
                    bva_bv32_add1_n (by omega)
                  have hws_l0 : st_clr.scratch.wsort.length = 2 * c.max_vars :=
                    hlenf.scratch_ok.wsort_len
                  have hws2_l0 : st_clr.scratch.work_stk2.length = 2 * c.max_vars :=
                    hlenf.scratch_ok.work_stk2_len
                  have hsb_c : st_clr.scratch.scratch_buf.length = c.scratch_cap := hsbf_l
                  have har_c : st_clr.core.arena.length = c.arena_cap :=
                    hlenf.core_ok.arena_len_arr
                  have halen_c : st_clr.core.arena_len ≤ c.arena_cap := hlenf.core_ok.arena_len_le
                  have hlen_c : st_clr.LengthsOk c := hinv_clr.1
                  have hmsi_c : (FullMem c st_clr ⋆ R) msi := hmsi
                  have hfuel_c : st_clr.core.fuel = s.core.fuel := hfuelf
                  have htm_c : st_clr.scratch.tarjan_mark = s.scratch.tarjan_mark := htmf
                  have htr_c : st_clr.scratch.tarjan_reach = s.scratch.tarjan_reach := htrf
                  obtain ⟨stc, hstc_eq⟩ : ∃ x : FullState, x = st_clr := ⟨st_clr, rfl⟩
                  rw [← hstc_eq] at hinv_clr hmat_c hcv_c hcv_c_le h2cv_c hws_l0 hws2_l0
                  rw [← hstc_eq] at hsb_c har_c halen_c hlen_c hmsi_c hfuel_c htm_c htr_c
                  generalize htcap_eq : (BitVec.ofNat 64 stf.core.cur_vars <<< (1 : Nat)) = tcap
                    at h2cv_c ⊢
                  clear htcap_eq
                  clear hinv1_core hsb1_l hlm1_l sb1 lm1 hend_mod hmod0 hmod1 hoff_c0
                  clear hstc_eq st_clr hmsi hScan hPick hFilter hinv hdw hbd_f0 hslice_f0 h2f0 h2f1
                  clear hoff_eq hsz_eq hoff_sz_le hmat1 hmatf hlmf_hi hlmf_only hlmi_hi hlmi_only
                  clear hlm_clr hsi_eq hsi_le hrow0 hlenf hwf hndf hextf hlv0f hdmf hcvf hmrkf
                  clear hlmi_l hsbf_l hbk_lt hcap_ge hinit_lits hcl hsc hsb_len hlm_len
                  clear hqn2 hqn_le hst1 hst32 hmf harf half hfuelf htmf htrf hrem hp_ge hp_le
                  clear hsb_l lmi
                  -- Loop 1: collect divider literals `scr[0..dm)` and their negations
                  c0_hsteps_nogrp
                  refine wp_loop_inv
                    (fun (nt, ti, ()) mti => ∃ st1 : FullState,
                      ti.toNat ≤ bestkf.toNat + 1 ∧ BvaTouchedInv c stc R nt st1 mti)
                    (fun (_, ti, _) _ => bestkf.toNat + 1 - ti.toNat)
                    (fun Jt1 hJt1 => by
                      exact hJt1 (0#64, 0#32, ()) msi ⟨stc, Nat.zero_le _, rfl, rfl, rfl, rfl, rfl,
                        rfl, hlen_c.scratch_ok, Nat.zero_le _,
                        fun _ h => absurd h (Nat.not_lt_zero _), hmsi_c⟩)
                    (fun Jt1 (nt, ti, ()) mti ⟨st1, hti_le, hcore1, hsb1, htm1, htr1, hll1, hel1,
                        hscl1, hnt_le, hws2_ok, hmti⟩ iht1 => ?_)
                  c0_hsplit
                  · have hti_lt : ti.toNat < bestkf.toNat + 1 := by
                      have h1 : ti.toNat < (bestkf + 1#32).toNat := by assumption
                      rwa [hdm_n] at h1
                    have hti1 : (ti + 1#32).toNat = ti.toNat + 1 :=
                      bva_bv32_add1_n (Nat.lt_trans hti_lt (Nat.lt_trans (Nat.succ_lt_succ hbk_lt32)
                        (by decide)))
                    have hti_sb_lt : ti.toNat < st1.scratch.scratch_buf.length := by
                      rw [hsb1, hsb_c]
                      exact Nat.lt_of_lt_of_le (Nat.lt_trans hti_lt (Nat.succ_lt_succ hbk_lt32))
                        (Nat.le_trans (by decide) hmat_c.1)
                    have hfl_lt : (st1.scratch.scratch_buf[ti.toNat]'hti_sb_lt).toNat <
                        2 * stc.core.cur_vars := by
                      have h1 := (hmat_c.2.2.2 ti.toNat hti_lt).1
                      have hti_sb_c : ti.toNat < stc.scratch.scratch_buf.length := by
                        rwa [← hsb1]
                      rw [List.getElem?_eq_getElem hti_sb_c, Option.getD_some] at h1
                      simpa only [hsb1] using h1
                    have hti_sb : (BitVec.setWidth 64 ti).toNat <
                        st1.scratch.scratch_buf.length := by
                      rw [bv64_setWidth_32]; exact hti_sb_lt
                    let flit := st1.scratch.scratch_buf[(BitVec.setWidth 64 ti).toNat]'hti_sb
                    have hfl_eq : flit = st1.scratch.scratch_buf[ti.toNat]'hti_sb_lt := by
                      simp only [flit, bv64_setWidth_32]
                    have hfl_lt' : flit.toNat < 2 * stc.core.cur_vars := by
                      rw [hfl_eq]; exact hfl_lt
                    have hfl_ws : (BitVec.setWidth 64 flit).toNat < st1.scratch.wsort.length := by
                      rw [bv64_setWidth_32, hscl1.wsort_len]
                      exact Nat.lt_of_lt_of_le hfl_lt' (Nat.mul_le_mul_left 2 hcv_c_le)
                    have hnfl_lt : (flit ^^^ 1#32).toNat < 2 * stc.core.cur_vars := by
                      rw [BitVec.toNat_xor]; exact litNeg_lt_two_mul hfl_lt'
                    c0_hsteps_nogrp
                    refine wp_join_state1 (t := i64) (α := BitVec 64 × FullState) (fun x => x.1)
                      (fun ⟨nt1, sta⟩ m1 => BvaTouchedInv c stc R nt1 sta m1)
                      (fun _ ⟨nt1, sta⟩ m1 ⟨hcorea, hsba, htma, htra, hlla, hela, hscla, hnt1_le,
                          hws2a_ok, hm1⟩ => ?_)
                      (fun Jf1 hJf1 => ?_)
                    · have hnfl_ws : (BitVec.setWidth 64 (flit ^^^ 1#32)).toNat <
                          sta.scratch.wsort.length := by
                        rw [bv64_setWidth_32, hscla.wsort_len]
                        exact Nat.lt_of_lt_of_le hnfl_lt (Nat.mul_le_mul_left 2 hcv_c_le)
                      c0_hsteps_nogrp
                      refine wp_join_state1 (t := i64) (α := BitVec 64 × FullState) (fun x => x.1)
                        (fun ⟨nt2, stb⟩ m2 => BvaTouchedInv c stc R nt2 stb m2)
                        (fun _ ⟨nt2, stb⟩ m2 hinv2 => by
                          c0_hsteps_nogrp
                          exact iht1 (nt2, ti + 1#32, ()) m2
                            (by dsimp only; rw [hti1]
                                exact Nat.sub_lt_sub_left hti_lt (Nat.lt_succ_self _))
                            ⟨stb, by rw [hti1]; exact hti_lt, hinv2⟩)
                        (fun Jf2 hJf2 => ?_)
                      c0_hsplit
                      · c0_hsplit
                        · have hnt1_lt : nt1.toNat < 2 * stc.core.cur_vars := by
                            have h1 : nt1.toNat < tcap.toNat := by assumption
                            rwa [h2cv_c] at h1
                          have hnt1_ws2 : nt1.toNat < sta.scratch.work_stk2.length := by
                            rw [hscla.work_stk2_len]
                            exact Nat.lt_of_lt_of_le hnt1_lt (Nat.mul_le_mul_left 2 hcv_c_le)
                          c0_hsteps_nogrp; dsimp only at hm
                          exact hJf2 ⟨nt1 + 1#64, _⟩ m
                            (bva_touched_push hcv_c_le hmx hnt1_lt hnfl_lt
                              hcorea hsba htma htra hlla hela hscla hws2a_ok hm)
                        · exact hJf2 ⟨nt1, sta⟩ m1
                            ⟨hcorea, hsba, htma, htra, hlla, hela, hscla, hnt1_le, hws2a_ok, hm1⟩
                      · exact hJf2 ⟨nt1, sta⟩ m1
                          ⟨hcorea, hsba, htma, htra, hlla, hela, hscla, hnt1_le, hws2a_ok, hm1⟩
                    · c0_hsplit
                      · c0_hsplit
                        · have hnt_lt : nt.toNat < 2 * stc.core.cur_vars := by
                            have h1 : nt.toNat < tcap.toNat := by assumption
                            rwa [h2cv_c] at h1
                          have hnt_ws2 : nt.toNat < st1.scratch.work_stk2.length := by
                            rw [hscl1.work_stk2_len]
                            exact Nat.lt_of_lt_of_le hnt_lt (Nat.mul_le_mul_left 2 hcv_c_le)
                          c0_hsteps_nogrp; dsimp only at hm
                          exact hJf1 ⟨nt + 1#64, _⟩ m
                            (bva_touched_push hcv_c_le hmx hnt_lt hfl_lt'
                              hcore1 hsb1 htm1 htr1 hll1 hel1 hscl1 hws2_ok hm)
                        · exact hJf1 ⟨nt, st1⟩ mti
                            ⟨hcore1, hsb1, htm1, htr1, hll1, hel1, hscl1, hnt_le, hws2_ok, hmti⟩
                      · exact hJf1 ⟨nt, st1⟩ mti
                          ⟨hcore1, hsb1, htm1, htr1, hll1, hel1, hscl1, hnt_le, hws2_ok, hmti⟩
                  · -- Loop 2: collect quotient literals from top row `scr[64 + best_k*256 + tm]`
                    have h32bk_n : ((32 : BitVec 32) + bestkf).toNat = 32 + bestkf.toNat :=
                      bva_bv32_32add_n hbk_lt32
                    have h32bk_lt_c : 32 + bestkf.toNat < stc.scratch.scratch_buf.length := by
                      rw [hsb_c]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hbk_lt32 32)
                        (Nat.le_trans (by decide) hmat_c.1)
                    have h32bk_sb : (BitVec.setWidth 64 ((32 : BitVec 32) + bestkf)).toNat <
                        st1.scratch.scratch_buf.length := by
                      rw [bv64_setWidth_32, h32bk_n, hsb1]; exact h32bk_lt_c
                    have hbk_sb : (BitVec.setWidth 64 bestkf).toNat <
                        st1.scratch.scratch_buf.length := by
                      rw [bv64_setWidth_32, hsb1, hsb_c]
                      exact Nat.lt_of_lt_of_le hbk_lt32 (Nat.le_trans (by decide) hmat_c.1)
                    let mn_bv := stc.scratch.scratch_buf[32 + bestkf.toNat]'h32bk_lt_c
                    have hmn_row := hmat_c.2.2.2 bestkf.toNat (Nat.lt_succ_self _)
                    have hmn_getD :
                        (stc.scratch.scratch_buf[32 + bestkf.toNat]?.getD 0#32).toNat =
                          mn_bv.toNat := by
                      dsimp only [mn_bv]
                      rw [List.getElem?_eq_getElem h32bk_lt_c, Option.getD_some]
                    have hmn_hi : mn_bv.toNat ≤ 256 := by rw [← hmn_getD]; exact hmn_row.2.2.1
                    have hmn_entries := hmn_row.2.2.2
                    rw [hmn_getD] at hmn_entries
                    c0_hsteps_nogrp
                    refine wp_loop_inv
                      (fun (ntm, tm, ()) mtm => ∃ stm : FullState,
                        tm.toNat ≤ mn_bv.toNat ∧ BvaTouchedInv c stc R ntm stm mtm)
                      (fun (_, tm, _) _ => mn_bv.toNat - tm.toNat)
                      (fun Jt2 hJt2 => by
                        exact hJt2 (nt, 0#32, ()) mti ⟨st1, Nat.zero_le _, hcore1, hsb1, htm1,
                          htr1, hll1, hel1, hscl1, hnt_le, hws2_ok, hmti⟩)
                      (fun Jt2 (ntm, tm, ()) mtm ⟨stm, htm_le, hcorem, hsbm, htmm, htrm, hllm,
                          helm, hsclm, hntm_le, hws2m_ok, hmtm⟩ iht2 => ?_)
                    c0_hsplit
                    · have htm_lt : tm.toNat < mn_bv.toNat := by
                        have h1 : tm.toNat < (st1.scratch.scratch_buf[(BitVec.setWidth 64
                            ((32 : BitVec 32) + bestkf)).toNat]'h32bk_sb).toNat := by assumption
                        simpa only [mn_bv, bv64_setWidth_32, h32bk_n, hsb1] using h1
                      have htm_256 : tm.toNat < 256 := Nat.lt_of_lt_of_le htm_lt hmn_hi
                      have htm1 : (tm + 1#32).toNat = tm.toNat + 1 :=
                        bva_bv32_add1_n (Nat.lt_trans htm_256 (by decide))
                      have hct_idx : (64 + bestkf * 256 + tm).toNat =
                          64 + bestkf.toNat * 256 + tm.toNat :=
                        bva_bv32_row_idx_n hbk_lt32 htm_256
                      have hct_mod := bva_bv32_row_mod_n hbk_lt32 htm_256
                      have hct_lt_c : 64 + bestkf.toNat * 256 + tm.toNat <
                          stc.scratch.scratch_buf.length := by
                        rw [hsb_c]
                        exact Nat.lt_of_lt_of_le (by omega) hmat_c.1
                      have hct_sb : (BitVec.setWidth 64 (64 + bestkf * 256 + tm)).toNat <
                          stm.scratch.scratch_buf.length := by
                        rw [bv64_setWidth_32, hct_idx, hsbm]; exact hct_lt_c
                      let ct_bv := stm.scratch.scratch_buf[
                        (BitVec.setWidth 64 (64 + bestkf * 256 + tm)).toNat]'hct_sb
                      let ct := stm.scratch.scratch_buf[((64 : BitVec 32).toNat +
                        bestkf.toNat * (256 : BitVec 32).toNat + tm.toNat) % 2 ^ 32]'(by
                          rw [hct_mod, hsbm]; exact hct_lt_c)
                      have hct_bv_eq : ct_bv = ct := by
                        dsimp only [ct_bv, ct]; congr 1
                        rw [bv64_setWidth_32, hct_idx, hct_mod]
                      obtain ⟨_, _, _, hct_ok, _, _⟩ := hmn_entries tm.toNat htm_lt
                      have hct_getD :
                          stc.scratch.scratch_buf[64 + bestkf.toNat * 256 + tm.toNat]?.getD
                            0#32 = ct := by
                        dsimp only [ct]; simp only [hct_mod, hsbm]
                        rw [List.getElem?_eq_getElem hct_lt_c, Option.getD_some]
                      rw [hct_getD] at hct_ok
                      c0_hsteps_nogrp
                      refine wp_join_state1 (t := i64) (α := BitVec 64 × FullState) (fun x => x.1)
                        (fun ⟨ntm1, stm1⟩ mm1 => BvaTouchedInv c stc R ntm1 stm1 mm1)
                        (fun _ ⟨ntm1, stm1⟩ mm1 hinv2 => by
                          c0_hsteps_nogrp
                          exact iht2 (ntm1, tm + 1#32, ()) mm1
                            (by dsimp only; rw [htm1]
                                exact Nat.sub_lt_sub_left htm_lt (Nat.lt_succ_self _))
                            ⟨stm1, by rw [htm1]; exact htm_lt, hinv2⟩)
                        (fun Jtm hJtm => ?_)
                      c0_hsplit
                      · have hbin_ct : (ct &&& 0x80000000#32) ≠ 0#32 := by assumption
                        unfold M4BvaRowEntryOk at hct_ok; rw [ite_eq_left hbin_ct] at hct_ok
                        have hql_lt : (ct &&& 0x7FFFFFFF#32).toNat < 2 * stc.core.cur_vars :=
                          hct_ok.1
                        have hql_lt_bv :
                            (ct_bv &&& 0x7FFFFFFF#32).toNat < 2 * stc.core.cur_vars := by
                          rw [hct_bv_eq]; exact hql_lt
                        have hql_ws : (BitVec.setWidth 64 (ct_bv &&& 0x7FFFFFFF#32)).toNat <
                            stm.scratch.wsort.length := by
                          rw [bv64_setWidth_32, hsclm.wsort_len]
                          exact Nat.lt_of_lt_of_le hql_lt_bv (Nat.mul_le_mul_left 2 hcv_c_le)
                        c0_hsteps_nogrp
                        refine wp_join_state1 (t := i64) (α := BitVec 64 × FullState) (fun x => x.1)
                          (fun ⟨ntb, stb⟩ mb => BvaTouchedInv c stc R ntb stb mb)
                          (fun _ ⟨ntb, stb⟩ mb hinvb => by exact hJtm ⟨ntb, stb⟩ mb hinvb)
                          (fun Jql hJql => ?_)
                        c0_hsplit
                        · c0_hsplit
                          · have hntm_lt : ntm.toNat < 2 * stc.core.cur_vars := by
                              have h1 : ntm.toNat < tcap.toNat := by assumption
                              rwa [h2cv_c] at h1
                            have hntm_ws2 : ntm.toNat < stm.scratch.work_stk2.length := by
                              rw [hsclm.work_stk2_len]
                              exact Nat.lt_of_lt_of_le hntm_lt (Nat.mul_le_mul_left 2 hcv_c_le)
                            c0_hsteps_nogrp; dsimp only at hm
                            exact hJql ⟨ntm + 1#64, _⟩ m
                              (bva_touched_push hcv_c_le hmx hntm_lt hql_lt_bv
                                hcorem hsbm htmm htrm hllm helm hsclm hws2m_ok hm)
                          · exact hJql ⟨ntm, stm⟩ mtm
                              ⟨hcorem, hsbm, htmm, htrm, hllm, helm, hsclm, hntm_le, hws2m_ok, hmtm⟩
                        · exact hJql ⟨ntm, stm⟩ mtm
                            ⟨hcorem, hsbm, htmm, htrm, hllm, helm, hsclm, hntm_le, hws2m_ok, hmtm⟩
                      · have hbin_ct : (ct &&& 0x80000000#32) = 0#32 := by assumption
                        unfold M4BvaRowEntryOk at hct_ok
                        rw [ite_eq_right (fun h' => h' hbin_ct)] at hct_ok
                        obtain ⟨hct_ref, hct_ng, _, hct_sz256, _, _, _⟩ := hct_ok
                        have hct_wf := hinv_clr.2.1.arena.refs_wf ct.toNat hct_ref
                        have hct2_n : (BitVec.setWidth 64 ct + 2).toNat = ct.toNat + 2 :=
                          bva_bv64_add2_n
                        have hct2_lt_c : ct.toNat + 2 < stc.core.arena.length := by
                          rw [har_c]; have := hct_wf.1; exact Nat.lt_of_lt_of_le (by omega) halen_c
                        have hct2_ar : (BitVec.setWidth 64 ct_bv + 2).toNat <
                            stm.core.arena.length := by
                          rw [hct_bv_eq, hct2_n, hcorem]; exact hct2_lt_c
                        have hct_sz_eq : (stc.core.arena[ct.toNat + 2]'hct2_lt_c).toNat =
                            fullArenaClauseSizeCore stc.core ct.toNat := by
                          unfold fullArenaClauseSizeCore
                          rw [List.getElem?_eq_getElem hct2_lt_c, Option.getD_some]
                        let csz_t := stc.core.arena[ct.toNat + 2]'hct2_lt_c
                        have hcsz_256 : csz_t.toNat ≤ 256 := by
                          dsimp only [csz_t]; rw [hct_sz_eq]; exact hct_sz256
                        have hct_end_ar : ct.toNat + 3 + csz_t.toNat ≤ stc.core.arena.length := by
                          rw [har_c]; dsimp only [csz_t]; rw [hct_sz_eq]
                          exact Nat.le_trans hct_wf.2.2.1 (Nat.le_trans hct_wf.2.2.2.1 halen_c)
                        c0_hsteps_nogrp
                        refine wp_loop_inv
                          (fun (ntj, tj, ()) mtj => ∃ stj : FullState,
                            tj.toNat ≤ csz_t.toNat ∧ BvaTouchedInv c stc R ntj stj mtj)
                          (fun (_, tj, _) _ => csz_t.toNat - tj.toNat)
                          (fun Jtj hJtj => by
                            exact hJtj (ntm, 0#32, ()) mtm ⟨stm, Nat.zero_le _, hcorem, hsbm,
                              htmm, htrm, hllm, helm, hsclm, hntm_le, hws2m_ok, hmtm⟩)
                          (fun Jtj (ntj, tj, ()) mtj ⟨stj, htj_le, hcorej, hsbj, htmj, htrj, hllj,
                              helj, hsclj, hntj_le, hws2j_ok, hmtj⟩ ihtj => ?_)
                        c0_hsplit
                        · have htj_lt : tj.toNat < csz_t.toNat := by
                            have hmod2 : (ct.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
                                ct.toNat + 2 := bva_bv64_add2_mod
                            have h1 : tj.toNat < (stm.core.arena[
                                (ct.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                                  rw [hmod2, hcorem]; exact hct2_lt_c)).toNat := by assumption
                            simpa only [csz_t, hmod2, hcorem] using h1
                          have htj1 : (tj + 1#32).toNat = tj.toNat + 1 :=
                            bva_bv32_add1_n (Nat.lt_trans (Nat.lt_of_lt_of_le htj_lt hcsz_256)
                              (by decide))
                          have hctj_n : (BitVec.setWidth 64 ct + 3 + BitVec.setWidth 64 tj).toNat =
                              ct.toNat + 3 + tj.toNat := bva_bv64_add3_n
                          have hctj_ar_c : ct.toNat + 3 + tj.toNat < stc.core.arena.length :=
                            Nat.lt_of_lt_of_le
                              (Nat.add_lt_add_left htj_lt (ct.toNat + 3)) hct_end_ar
                          have hctj_ar_bv :
                              (BitVec.setWidth 64 ct_bv + 3 + BitVec.setWidth 64 tj).toNat <
                                stj.core.arena.length := by
                            rw [hct_bv_eq, hctj_n, hcorej]; exact hctj_ar_c
                          have hql_mem : (stc.core.arena[ct.toNat + 3 + tj.toNat]'hctj_ar_c).toNat ∈
                              fullArenaClauseLitsCore stc.core ct.toNat :=
                            List.mem_of_getElem? (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem
                              (k := stc.core) (r := ct.toNat) (j := tj.toNat)
                              (by rw [← hct_sz_eq]; exact htj_lt) hctj_ar_c)
                          have hql_lt : (stc.core.arena[ct.toNat + 3 + tj.toNat]'hctj_ar_c).toNat <
                              2 * stc.core.cur_vars :=
                            hinv_clr.2.1.arena.lits_lt ct.toNat hct_ref hct_ng _ hql_mem
                          have hql_lt_bv :
                              (stj.core.arena[(BitVec.setWidth 64 ct_bv + 3 +
                                BitVec.setWidth 64 tj).toNat]'hctj_ar_bv).toNat <
                                2 * stc.core.cur_vars := by
                            simpa only [hct_bv_eq, hctj_n, hcorej] using hql_lt
                          have hql_ws_bv : (BitVec.setWidth 64
                              (stj.core.arena[(BitVec.setWidth 64 ct_bv + 3 +
                                BitVec.setWidth 64 tj).toNat]'hctj_ar_bv)).toNat <
                              stj.scratch.wsort.length := by
                            rw [bv64_setWidth_32, hsclj.wsort_len]
                            exact Nat.lt_of_lt_of_le hql_lt_bv (Nat.mul_le_mul_left 2 hcv_c_le)
                          c0_hsteps_nogrp
                          refine wp_join_state1 (t := i64) (α := BitVec 64 × FullState)
                            (fun x => x.1)
                            (fun ⟨ntj1, stj1⟩ mj1 => BvaTouchedInv c stc R ntj1 stj1 mj1)
                            (fun _ ⟨ntj1, stj1⟩ mj1 hinvj => by
                              c0_hsteps_nogrp
                              exact ihtj (ntj1, tj + 1#32, ()) mj1
                                (by dsimp only; rw [htj1]
                                    exact Nat.sub_lt_sub_left htj_lt (Nat.lt_succ_self _))
                                ⟨stj1, by rw [htj1]; exact htj_lt, hinvj⟩)
                            (fun Jq1 hJq1 => ?_)
                          c0_hsplit
                          · c0_hsplit
                            · c0_hsplit
                              · have hntj_lt : ntj.toNat < 2 * stc.core.cur_vars := by
                                  have h1 : ntj.toNat < tcap.toNat := by assumption
                                  rwa [h2cv_c] at h1
                                have hntj_ws2 : ntj.toNat < stj.scratch.work_stk2.length := by
                                  rw [hsclj.work_stk2_len]
                                  exact Nat.lt_of_lt_of_le hntj_lt (Nat.mul_le_mul_left 2 hcv_c_le)
                                c0_hsteps_nogrp; dsimp only at hm
                                exact hJq1 ⟨ntj + 1#64, _⟩ m
                                  (bva_touched_push hcv_c_le hmx hntj_lt hql_lt_bv
                                    hcorej hsbj htmj htrj hllj helj hsclj hws2j_ok hm)
                              · exact hJq1 ⟨ntj, stj⟩ mtj
                                  ⟨hcorej, hsbj, htmj, htrj, hllj, helj, hsclj, hntj_le, hws2j_ok,
                                   hmtj⟩
                            · exact hJq1 ⟨ntj, stj⟩ mtj
                                ⟨hcorej, hsbj, htmj, htrj, hllj, helj, hsclj, hntj_le, hws2j_ok,
                                 hmtj⟩
                          · exact hJq1 ⟨ntj, stj⟩ mtj
                              ⟨hcorej, hsbj, htmj, htrj, hllj, helj, hsclj, hntj_le, hws2j_ok, hmtj⟩
                        · exact hJtm ⟨ntj, stj⟩ mtj
                            ⟨hcorej, hsbj, htmj, htrj, hllj, helj, hsclj, hntj_le, hws2j_ok, hmtj⟩
                    · -- Loop 3: clear `tcnt[touched[tz]] = 0`, store `h->res_sz = ntm`, call commit
                      c0_hsteps_nogrp
                      refine wp_loop_inv
                        (fun (tz, ()) mtz => ∃ stz : FullState,
                          tz.toNat ≤ ntm.toNat ∧ stz.core = stc.core ∧
                          stz.scratch.scratch_buf = stc.scratch.scratch_buf ∧
                          stz.scratch.tarjan_mark = stc.scratch.tarjan_mark ∧
                          stz.scratch.tarjan_reach = stc.scratch.tarjan_reach ∧
                          stz.scratch.last_learned = stc.scratch.last_learned ∧
                          stz.scratch.extend_len = stc.scratch.extend_len ∧
                          stz.scratch.work_stk2 = stm.scratch.work_stk2 ∧
                          stz.scratch.LengthsOk c ∧ (FullMem c stz ⋆ R) mtz)
                        (fun (tz, _) _ => ntm.toNat - tz.toNat)
                        (fun Jtz hJtz => by
                          exact hJtz (0#64, ()) mtm ⟨stm, Nat.zero_le _, hcorem, hsbm, htmm, htrm,
                            hllm, helm, rfl, hsclm, hmtm⟩)
                        (fun Jtz (tz, ()) mtz ⟨stz, htz_le, hcorez, hsbz, htmz, htrz, hllz, helz,
                            hws2z, hsclz, hmtz⟩ ihtz => ?_)
                      c0_hsplit
                      · have htz_lt : tz.toNat < ntm.toNat := by assumption
                        have htz_max : tz.toNat < 2 * c.max_vars :=
                          Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le htz_lt hntm_le)
                            (Nat.mul_le_mul_left 2 hcv_c_le)
                        have htz1 : (tz + 1#64).toNat = tz.toNat + 1 :=
                          bva_bv64_add1_n (Nat.lt_trans htz_max (by omega))
                        have htz_ws2 : tz.toNat < stz.scratch.work_stk2.length := by
                          rw [hsclz.work_stk2_len]; exact htz_max
                        have htl_lt : (stz.scratch.work_stk2[tz.toNat]'htz_ws2).toNat <
                            2 * stc.core.cur_vars := by
                          have h1 := hws2m_ok tz.toNat htz_lt
                          have htz_m : tz.toNat < stm.scratch.work_stk2.length := by
                            rwa [← hws2z]
                          rw [List.getElem?_eq_getElem htz_m, Option.getD_some] at h1
                          simpa only [hws2z] using h1
                        have htl_wsz : (BitVec.setWidth 64
                            (stz.scratch.work_stk2[tz.toNat]'htz_ws2)).toNat <
                            stz.scratch.wsort.length := by
                          rw [bv64_setWidth_32, hsclz.wsort_len]
                          exact Nat.lt_of_lt_of_le htl_lt (Nat.mul_le_mul_left 2 hcv_c_le)
                        c0_hsteps_nogrp; dsimp only at hm
                        exact ihtz (tz + 1#64, ()) m
                          (by dsimp only; rw [htz1]
                              exact Nat.sub_lt_sub_left htz_lt (Nat.lt_succ_self _))
                          (bva_touched_clear_step htz_lt htz1 hcorez hsbz htmz htrz hllz helz hws2z
                            hsclz hm)
                      · c0_hsteps
                        let st_tc : FullState :=
                          { stz with scratch := { stz.scratch with res_sz := ntm } }
                        have hinv_tc : FullDenseInvW c F0 F_cur st_tc := by
                          have htc_eq : st_tc = { stc with scratch := st_tc.scratch } := by
                            cases stz; cases stc; dsimp only at hcorez; cases hcorez; rfl
                          rw [htc_eq]
                          exact fullDenseInv_with_core_aux (tc' := stc.core.tmp_cnt)
                            (tl' := stc.core.tmp_len) (sc' := st_tc.scratch) hinv_clr
                            hlen_c.core_ok.repr_len hlen_c.core_ok.min_clr_len_arr
                            hlen_c.core_ok.tmp_len_arr hlen_c.core_ok.flags_len
                            hlen_c.core_ok.tmp_len_le
                            { hsclz with wsort_len := hsclz.wsort_len } hllz helz
                        c0_call hCommit
                        refine ⟨c, F0, F_cur, st_tc, R, rfl, hinv_tc, hbk1, hbk_lt32,
                          m4BvaMatrixInv_congr (by rw [hcorez]) (by rw [hcorez]) (by rw [hcorez])
                            (by exact hsbz) hmat_c, hm,
                          fun ok s' m' hinv' hcv' hfuel' htm' htr' hm' =>
                            hQ ok s' m' hinv' (by rw [← hcv_c, ← hcorez]; exact hcv')
                              (hfuel'.trans (by rw [hcorez]; exact hfuel_c))
                              (htm'.trans (htmz.trans htm_c))
                              (htr'.trans (htrz.trans htr_c)) hm'⟩
          · -- Main `while (step < 32u && cur_qn >= 2u)` loop
            clear hCommit hbd_f0 hslice_f0 h2f0 h2f1 hoff_eq hsz_eq hoff_sz_le hoff_c0
            clear hend_mod hmod0 hmod1 hrow0 hrem hp_ge hp_le hqn2 hqn_le
            refine wp_loop_inv
              (fun (step, cur_qn, best_k, best_red, ()) ml => ∃ stl : FullState,
                (FullMem c stl ⋆ R) ml ∧
                stl.LengthsOk c ∧ FullWitnessInv c F0 F_cur stl.core ∧
                FullArenaVarsNodup stl ∧ FullExtScratchOk c stl ∧
                stl.core.cur_level = 0 ∧ stl.core.dense_mode ≠ 0#64 ∧
                stl.core.cur_vars = s.core.cur_vars ∧ stl.core.fuel = s.core.fuel ∧
                stl.core.arena = s.core.arena ∧ stl.core.arena_len = s.core.arena_len ∧
                stl.core.mrk = s.core.mrk ∧
                stl.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
                stl.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
                1 ≤ step.toNat ∧ step.toNat ≤ 32 ∧
                cur_qn.toNat =
                  (stl.scratch.scratch_buf[32 + (step.toNat - 1)]?.getD 0#32).toNat ∧
                M4BvaMatrixInv c F_cur stl step.toNat ∧
                (best_k = 0#32 ∨ (1 ≤ best_k.toNat ∧ best_k.toNat < step.toNat)) ∧
                (∀ l < 2 * c.max_vars, (stl.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
                (∀ r < step.toNat,
                  (stl.core.lit_mark[(stl.scratch.scratch_buf[r]?.getD 0#32).toNat]?.getD 0#8 &&&
                    1#8) ≠ 0#8) ∧
                (∀ l < 2 * c.max_vars, (stl.core.lit_mark[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
                  ∃ r < step.toNat, (stl.scratch.scratch_buf[r]?.getD 0#32).toNat = l))
              (fun (step, _, _, _, _) _ => 32 - step.toNat)
              (fun Jst hJst => by
                c0_hfast
                refine hJst (1#32, qn, 0#32, 0#64, ()) _
                  ⟨{ core := { s.core with lit_mark := lm1 }
                     scratch := { s.scratch with scratch_buf := sb1 } },
                   by simp only [bv64_setWidth_32] at hm; exact hm,
                   hinv1_core,
                   { hinv.2.1 with
                     arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
                     watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
                   hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2,
                   rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide,
                   by dsimp only [sb1]
                      rw [show 32 + ((1#32).toNat - 1) = 32 from rfl,
                        List.getElem?_set_self (by simp [hsb_l]; omega), Option.getD_some],
                   m4BvaMatrixInv_congr rfl rfl rfl rfl hmat1,
                   Or.inl rfl, hlm1_hi, hlm1_set, hlm1_only⟩)
              (fun Jst (step, cur_qn, best_k, best_red, ()) ml
                  ⟨stl, hml, hlenl, hwl, hndl, hextl, hlv0l, hdml, hcvl, hfuell, harl, hall,
                   hmrkl, html, htrl, hst1, hst32, hcurqn_eq, hmatl, hbkl, hlml_hi, hlml_set,
                   hlml_only⟩ ihst => ?_)
            clear hinv1_core hsb1_l hlm1_l hlm1_hi hlm1_set hlm1_only hmat1 sb1 lm1
            c0_hfast
            · have hst_lt : step.toNat < 32 := by
                have h1 : step.toNat < (32 : BitVec 32).toNat := by assumption
                exact h1
              have hrow_off :
                  ((64 : BitVec 32) + (step - 1) * 256).toNat = 64 + (step.toNat - 1) * 256 :=
                bva_bv32_step_row_n hst1 hst_lt
              have hqn256_l : cur_qn.toNat ≤ 256 := by
                rw [hcurqn_eq]; exact (hmatl.2.2.2 (step.toNat - 1) (by omega)).2.2.1
              c0_call hScan
              refine ⟨c, F0, F_cur, stl, R, rfl, hlenl, hwl, hndl, hextl, hlv0l, hdml,
                by rw [hinit_lits, hcvl]; omega, hlml_hi, by rw [hrow_off]; omega, hqn256_l,
                fun qi hqi => ?_, hml,
                fun ncntd ws' ws1' ws2' m1 hlen1 hnc_le hws1_ok hm1 => ?_⟩
              · rw [hrow_off]
                rw [hcurqn_eq] at hqi
                obtain ⟨res, _, _, hok, _, _⟩ :=
                  (hmatl.2.2.2 (step.toNat - 1) (by omega)).2.2.2 qi hqi
                unfold M4BvaRowEntryOk at hok
                by_cases hbin :
                    (stl.scratch.scratch_buf[64 + (step.toNat - 1) * 256 + qi]?.getD 0#32 &&&
                      0x80000000#32) ≠ 0#32
                · rw [ite_eq_left hbin] at hok ⊢; exact hok.1
                · rw [ite_eq_right hbin] at hok ⊢; exact ⟨hok.1, hok.2.1⟩
              · rw [hinit_lits] at hnc_le hws1_ok
                let st1 : FullState :=
                  { stl with scratch :=
                    { stl.scratch with wsort := ws', work_stk1 := ws1', work_stk2 := ws2' } }
                have hinv1_nl : FullDenseInvNoLm c F0 F_cur st1 :=
                  ⟨hlen1, hwl, hndl, hextl, hlv0l, hdml⟩
                c0_call hPick
                refine ⟨c, F0, F_cur, st1, R, rfl, hinv1_nl, by dsimp only [st1]; omega,
                  by dsimp only [st1]; omega, fun i hi => by
                    have := hws1_ok i hi; dsimp only [st1]; omega,
                  hm1, fun bl rp2 mc2 tc2 tl2 ws2 ant2 sig2 shrk2 m2 hinv2 hbl_ok hm2 => ?_⟩
                let st2 : FullState :=
                  { core := { st1.core with repr := rp2, min_clr := mc2,
                                            tmp_cnt := tc2, tmp_len := tl2 }
                    scratch := { st1.scratch with wsort := ws2, ant_sz := ant2,
                                                  sim_sig := sig2, shrink_stk := shrk2 } }
                have hmat2 : M4BvaMatrixInv c F_cur st2 step.toNat :=
                  m4BvaMatrixInv_congr rfl rfl rfl rfl hmatl
                c0_hfast
                · exact hJstep ⟨step, cur_qn, best_k, best_red, st2⟩ m2 ⟨hm2, hinv2.1, hinv2.2.1,
                    hinv2.2.2.1, hinv2.2.2.2.1, hinv2.2.2.2.2.1, hinv2.2.2.2.2.2, hcvl, hfuell,
                    harl, hall, hmrkl, html, htrl, hst1, hst32, hmat2, hbkl, hlml_hi, hlml_only⟩
                · have hbl_lt : bl.toNat < 2 * s.core.cur_vars := by
                    rcases hbl_ok with hff | hlt
                    · exact absurd hff (by assumption)
                    · dsimp only [st1] at hlt; omega
                  have hnrow_off :
                      ((64 : BitVec 32) + step * 256).toNat = 64 + step.toNat * 256 :=
                    bva_bv32_nrow_n hst_lt
                  have hpar_off :
                      ((8256 : BitVec 32) + step * 256).toNat = 8256 + step.toNat * 256 :=
                    bva_bv32_par_n hst_lt
                  c0_call hFilter
                  refine ⟨c, F0, F_cur, st2, R, step.toNat, rfl, hinv2.1, hinv2.2.1,
                    hinv2.2.2.1, hinv2.2.2.2.1, hinv2.2.2.2.2.1, hinv2.2.2.2.2.2, hst1, hst_lt,
                    hcap_ge, hrow_off, hnrow_off, hpar_off, hcurqn_eq,
                    by dsimp only [st2, st1]; omega, hmat2, hlml_hi, hlml_set, hm2,
                    fun new_qn sb3 m3 hlen3 hnq256 hpres3 hnew3 hm3 => ?_⟩
                  clear hScan hPick hFilter
                  let st3 : FullState :=
                    { st2 with scratch := { st2.scratch with scratch_buf := sb3 } }
                  have hpres3' : ∀ idx < c.scratch_cap,
                      ¬ (64 + step.toNat * 256 ≤ idx ∧ idx < 64 + step.toNat * 256 + 256) →
                      ¬ (8256 + step.toNat * 256 ≤ idx ∧ idx < 8256 + step.toNat * 256 + 256) →
                      sb3[idx]? = st2.scratch.scratch_buf[idx]? := fun idx hi h1 h2 =>
                    hpres3 idx hi (by rw [hnrow_off]; exact h1) (by rw [hpar_off]; exact h2)
                  c0_hsplit
                  · c0_hsteps_nogrp
                    refine hJstep ⟨step, cur_qn, best_k, best_red, st3⟩ m3 ⟨hm3, hlen3, hinv2.2.1,
                      hinv2.2.2.1, hinv2.2.2.2.1, hinv2.2.2.2.2.1, hinv2.2.2.2.2.2, hcvl, hfuell,
                      harl, hall, hmrkl, html, htrl, hst1, hst32,
                      m4BvaMatrixInv_of_filter_pres hst_lt hmat2 hpres3',
                      hbkl, hlml_hi, fun l hl hne => ?_⟩
                    obtain ⟨r, hr, heq⟩ := hlml_only l hl hne
                    refine ⟨r, hr, ?_⟩
                    dsimp only [st3]; rw [hpres3' r (by omega) (by omega) (by omega)]; exact heq
                  · have hnq2 : 2 ≤ new_qn.toNat := by
                      have h1 : ¬ new_qn.toNat < (2 : BitVec 32).toNat := by assumption
                      change ¬ new_qn.toNat < 2 at h1; omega
                    have h32step : ((32 : BitVec 32) + step).toNat = 32 + step.toNat :=
                      bva_bv32_32add_n hst_lt
                    have hstep1_n : (step + 1#32).toNat = step.toNat + 1 :=
                      bva_bv32_add1_n (Nat.lt_trans hst_lt (by decide))
                    let sb4 := (sb3.set step.toNat bl).set (32 + step.toNat) new_qn
                    let lm4 := st2.core.lit_mark.set bl.toNat 1#8
                    have hsb3_l : sb3.length = c.scratch_cap := hlen3.scratch_ok.scratch_buf_len
                    have hlm3_l : st2.core.lit_mark.length = 2 * c.max_vars :=
                      hlen3.core_ok.lit_mark_len
                    have hsb4_l : sb4.length = c.scratch_cap := by
                      dsimp only [sb4]; rw [List.length_set, List.length_set, hsb3_l]
                    have hlm4_l : lm4.length = 2 * c.max_vars := by
                      dsimp only [lm4]; rw [List.length_set, hlm3_l]
                    have hmat4 := m4BvaMatrixInv_extend_step hst1 hst_lt hmat2 hsb3_l
                      (by dsimp only [st2, st1]; rw [hcvl]; exact hbl_lt) hnq2 hnq256 hpres3'
                      (fun nm hnm => by
                        have h1 := hnew3 nm hnm
                        rw [hrow_off, hnrow_off, hpar_off, hcurqn_eq] at h1; exact h1)
                    let st4 : FullState :=
                      { core := { st2.core with lit_mark := lm4 }
                        scratch := { st2.scratch with scratch_buf := sb4 } }
                    have hst_sb : (BitVec.setWidth 64 step).toNat < sb3.length := by
                      rw [bv64_setWidth_32, hsb3_l]; omega
                    have h32st_b : (BitVec.setWidth 64 ((32 : BitVec 32) + step)).toNat <
                        (sb3.set (BitVec.setWidth 64 step).toNat bl).length := by
                      rw [bv64_setWidth_32, h32step, List.length_set, hsb3_l]; omega
                    have hbl_lm : (BitVec.setWidth 64 bl).toNat < st2.core.lit_mark.length := by
                      rw [bv64_setWidth_32, hlm3_l]; omega
                    c0_hsteps_nogrp
                    refine wp_join_state (α := BitVec 32 × BitVec 64)
                      (fun ⟨bk', br'⟩ => (bk', br', ()))
                      (fun ⟨bk', _⟩ mf4 =>
                        (bk' = 0#32 ∨ (1 ≤ bk'.toNat ∧ bk'.toNat < step.toNat + 1)) ∧ mf4 = m)
                      (fun _ ⟨bk', br'⟩ mf4 ⟨hbk', hmf4⟩ => ?_)
                      (fun Jbk hJbk => ?_)
                    · subst mf4
                      c0_hsteps_nogrp
                      have ⟨hlm4_hi, hlm4_set, hlm4_only⟩ := m4_bva_try_lit_extend_lm (bl := bl)
                        (new_qn := new_qn) hcap_ge hst_lt hlm3_l hsb3_l (by omega) hpres3'
                        hlml_hi hlml_set hlml_only
                      refine ihst (step + 1#32, new_qn, bk', br', ()) m
                        (by dsimp only; rw [hstep1_n]
                            exact Nat.sub_lt_sub_left hst_lt (Nat.lt_succ_self _))
                        ⟨st4, by simp only [bv64_setWidth_32, h32step] at hm; exact hm,
                         ⟨{ hlen3.core_ok with lit_mark_len := hlm4_l },
                          { hlen3.scratch_ok with scratch_buf_len := hsb4_l }⟩,
                         { hinv2.2.1 with
                           arena := { hinv2.2.1.arena with len_ok := hinv2.2.1.arena.len_ok }
                           watches := hinv2.2.1.watches.with_wstk rfl rfl rfl rfl rfl
                             (fun _ hr => hr) },
                         hinv2.2.2.1, hinv2.2.2.2.1, hinv2.2.2.2.2.1, hinv2.2.2.2.2.2,
                         hcvl, hfuell, harl, hall, hmrkl, html, htrl,
                         by rw [hstep1_n]; exact Nat.le_trans hst1 (Nat.le_succ _),
                         by rw [hstep1_n]; exact hst_lt,
                         by dsimp only [st4, sb4]
                            rw [hstep1_n, Nat.add_sub_cancel,
                              List.getElem?_set_self (by rw [List.length_set, hsb3_l]; omega),
                              Option.getD_some],
                         by rw [hstep1_n]; exact m4BvaMatrixInv_congr rfl rfl rfl rfl hmat4,
                         by rw [hstep1_n]; exact hbk',
                         hlm4_hi, by rw [hstep1_n]; exact hlm4_set,
                         by rw [hstep1_n]; exact hlm4_only⟩
                    · clear hmat4 hmat2 hmatl hml hm1 hm2 hm hinv2 hlen3 hlenl hwl hndl hextl
                      clear hpres3 hpres3' hnew3 hlml_hi hlml_set hlml_only hst_sb h32st_b hbl_lm
                      clear hsb4_l hlm4_l hsb3_l hlm3_l hinv1_nl hbl_ok st4 st3 st2 st1 sb4 lm4
                      c0_hfast
                      · exact hJbk ⟨step, _⟩ m ⟨Or.inr ⟨hst1, Nat.lt_succ_self _⟩, rfl⟩
                      all_goals
                        exact hJbk ⟨best_k, best_red⟩ m
                          ⟨hbkl.imp id (fun ⟨h1, h2⟩ => ⟨h1, Nat.lt_succ_of_lt h2⟩), rfl⟩
            all_goals
              exact hJstep ⟨step, cur_qn, best_k, best_red, stl⟩ ml ⟨hml, hlenl, hwl, hndl, hextl,
                hlv0l, hdml, hcvl, hfuell, harl, hall, hmrkl, html, htrl, hst1, hst32, hmatl, hbkl,
                hlml_hi, hlml_only⟩
    · c0_hfast
      · exact hJicv _ m ⟨by simp only [bv_c0]; omega, rfl⟩
      · exact hJicv init_cv0 m ⟨by
          have h1 : ¬ s.core.cur_vars % 2 ^ 64 < init_cv0.toNat := by assumption
          omega, rfl⟩

end LeanQbe.T.Examples.Kissat.FullM4Bva
