module

public import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
import LeanQbe.T.Logic.ControlComb
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` 3-Hop BVA — Multi-Step Matrix Construction (Part 5)

Proves `Func.wp` for the multi-step literal factoring function `full_bva_try_lit`
(`full_bva_try_lit_wp` against `fullBvaTryLitHeapSpec`): row-0 collection with `f0`-membership
validation, multi-step `BvaMatrixInv` loop (`full_bva_scan_cands`, `full_bva_pick_cand`,
`full_bva_filter_row`), `lit_mark` restoration, and the final `full_bva_commit` call.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullBvaHeap

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullBvaHeapTactics
open FullBvaHeapHelpers
open FullBvaHeapScanHelpers
open scoped FullArenaTactics FullBvaHeapTactics

/-! ## 3. Multi-Step BVA Matrix Construction (`full_bva_try_lit_wp`) -/

section FullBvaTryLitHelpers

private theorem bvaMatrixInv_weaken_step {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {step1 step2 : Nat} (h1 : 1 ≤ step1) (h12 : step1 ≤ step2)
    (h : BvaMatrixInv c F_cur s step2) : BvaMatrixInv c F_cur s step1 :=
  ⟨h.1, h1, Nat.le_trans h12 h.2.2.1, fun r hr => h.2.2.2 r (Nat.lt_of_lt_of_le hr h12)⟩

private theorem bvaRowEntryOk_congr {F_cur : List (List Nat)} {s s' : FullState}
    {fr : Nat} {w : BitVec 32} {res : List Nat}
    (hcv : s'.core.cur_vars = s.core.cur_vars)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (h : BvaRowEntryOk F_cur s fr w res) : BvaRowEntryOk F_cur s' fr w res := by
  unfold BvaRowEntryOk at h ⊢
  by_cases hbin : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hbin] at h ⊢; rwa [hcv]
  · rw [ite_eq_right hbin] at h ⊢
    simp only [fullArenaClauseRefs, fullArenaClauseGarb, fullArenaClauseSize,
      fullArenaClauseLits, fullArenaClauseRefsCore, fullArenaClauseGarbCore,
      fullArenaClauseSizeCore, fullArenaClauseLitsCore, fullArenaHdrCore, har, hal] at h ⊢
    exact h

private theorem bvaMatrixInv_congr {c : FullCfg} {F_cur : List (List Nat)} {s s' : FullState}
    {step : Nat} (hcv : s'.core.cur_vars = s.core.cur_vars)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (hsb : s'.scratch.scratch_buf = s.scratch.scratch_buf)
    (h : BvaMatrixInv c F_cur s step) : BvaMatrixInv c F_cur s' step := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun r hr => ?_⟩
  obtain ⟨hfr, hq2, hq64, hm⟩ := h.2.2.2 r hr
  refine ⟨by rw [hsb, hcv]; exact hfr, by rw [hsb]; exact hq2, by rw [hsb]; exact hq64,
    fun m hm_lt => ?_⟩
  rw [hsb] at hm_lt
  obtain ⟨res, hres_lt, hres_nd, hok, hent, hpar⟩ := hm m hm_lt
  refine ⟨res, fun x hx => by rw [hcv]; exact hres_lt x hx, hres_nd, ?_, ?_, ?_⟩
  · rw [hsb]; exact bvaRowEntryOk_congr hcv har hal hok
  · intro t ht; rw [hsb]; exact hent t ht
  · intro hr0; rw [hsb]; obtain ⟨hpi, hpok⟩ := hpar hr0
    exact ⟨hpi, bvaRowEntryOk_congr hcv har hal hpok⟩

private theorem bvaRowEntryOk_of_large_f0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {cr f0 : BitVec 32} (href : cr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hng : fullArenaClauseGarbCore s.core cr.toNat = false)
    (hsz3 : 3 ≤ fullArenaClauseSizeCore s.core cr.toNat)
    (hsz5 : fullArenaClauseSizeCore s.core cr.toNat ≤ 5)
    (hf0_mem : f0.toNat ∈ fullArenaClauseLitsCore s.core cr.toNat) :
    ∃ res : List Nat,
      (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
      BvaRowEntryOk F_cur s f0.toNat cr res ∧
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
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x80000000#32).toNat = 2 ^ 31 from rfl,
      show (0#32).toNat = 0 from rfl]
    apply Nat.eq_of_testBit_eq; intro k
    rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_two_pow]
    by_cases hk : k = 31
    · subst hk; simp [Nat.testBit_lt_two_pow (show cr.toNat < 2 ^ 31 by omega)]
    · simp [Ne.symm hk]
  refine ⟨res, hres_lt, hres_nd, ?_, clause_entails_of_perm hC_perm hC_ent⟩
  unfold BvaRowEntryOk; rw [ite_eq_right (fun h' => h' hcr_not_bin)]
  exact ⟨href, hng, hsz3, hsz5, hf0_mem, List.Perm.refl _, hC_perm⟩

private theorem bvaMatrixInv_step1 {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {sb : List (BitVec 32)} {f0 qn : BitVec 32}
    (hcap : 2304 ≤ c.scratch_cap) (hsb_len : sb.length = c.scratch_cap)
    (hf0_lt : f0.toNat < 2 * s.core.cur_vars) (hq2 : 2 ≤ qn.toNat) (hq64 : qn.toNat ≤ 64)
    (hrow0 : ∀ m < qn.toNat, ∃ res : List Nat,
      (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
      BvaRowEntryOk F_cur s f0.toNat (sb[64 + m]?.getD 0#32) res ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause (f0.toNat :: res))) :
    BvaMatrixInv c F_cur
      { s with scratch := { s.scratch with scratch_buf := (sb.set 0 f0).set 16 qn } } 1 := by
  let sb1 := (sb.set 0 f0).set 16 qn
  have h0 : sb1[0]?.getD 0#32 = f0 := by
    dsimp only [sb1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
      Option.getD_some]
  have h16 : sb1[16]?.getD 0#32 = qn := by
    dsimp only [sb1]; rw [List.getElem?_set_self (by simp [hsb_len]; omega), Option.getD_some]
  have h64 : ∀ m < 64, sb1[64 + m]?.getD 0#32 = sb[64 + m]?.getD 0#32 := fun m _ => by
    dsimp only [sb1]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  refine ⟨hcap, Nat.le_refl 1, by omega, fun r hr => ?_⟩
  have hr0 : r = 0 := by omega
  subst hr0; dsimp only; rw [h0, h16]
  refine ⟨hf0_lt, hq2, hq64, fun m hm => ?_⟩
  obtain ⟨res, hres_lt, hres_nd, hok, hent⟩ := hrow0 m hm
  refine ⟨res, hres_lt, hres_nd, ?_, fun t ht => ?_, fun h => by omega⟩
  · rw [show 64 + 0 * 64 + m = 64 + m by omega, h64 m (by omega)]
    exact bvaRowEntryOk_congr rfl rfl rfl hok
  · have ht0 : t = 0 := by omega
    subst ht0; rw [h0]; exact hent

private theorem bvaMatrixInv_extend_step {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {sb' : List (BitVec 32)} {step : Nat} {best_lit new_qn : BitVec 32}
    (hstep1 : 1 ≤ step) (hstep16 : step < 16)
    (hmat : BvaMatrixInv c F_cur s step)
    (hsb'_len : sb'.length = c.scratch_cap)
    (hbest_lt : best_lit.toNat < 2 * s.core.cur_vars)
    (hnq2 : 2 ≤ new_qn.toNat) (hnq64 : new_qn.toNat ≤ 64)
    (hpres : ∀ idx < c.scratch_cap,
      ¬ (64 + step * 64 ≤ idx ∧ idx < 64 + step * 64 + 64) →
      ¬ (1088 + step * 64 ≤ idx ∧ idx < 1088 + step * 64 + 64) →
      sb'[idx]? = s.scratch.scratch_buf[idx]?)
    (hnew : ∀ nm < new_qn.toNat,
      let pi := (sb'[1088 + step * 64 + nm]?.getD 0#32).toNat
      pi < (s.scratch.scratch_buf[16 + (step - 1)]?.getD 0#32).toNat ∧
      ∃ res : List Nat,
        (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
        BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[64 + (step - 1) * 64 + pi]?.getD 0#32) res ∧
        BvaRowEntryOk F_cur s best_lit.toNat (sb'[64 + step * 64 + nm]?.getD 0#32) res ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res))) :
    BvaMatrixInv c F_cur
      { s with scratch := { s.scratch with
          scratch_buf := (sb'.set step best_lit).set (16 + step) new_qn } }
      (step + 1) := by
  have hcap := hmat.1
  let sb2 := (sb'.set step best_lit).set (16 + step) new_qn
  have hget_lt : ∀ idx < c.scratch_cap, idx ≠ step → idx ≠ 16 + step →
      ¬ (64 + step * 64 ≤ idx ∧ idx < 64 + step * 64 + 64) →
      ¬ (1088 + step * 64 ≤ idx ∧ idx < 1088 + step * 64 + 64) →
      sb2[idx]? = s.scratch.scratch_buf[idx]? := fun idx hi h1 h2 h3 h4 => by
    dsimp only [sb2]
    rw [List.getElem?_set_ne (Ne.symm h2), List.getElem?_set_ne (Ne.symm h1)]
    exact hpres idx hi h3 h4
  have hget_step : sb2[step]?.getD 0#32 = best_lit := by
    dsimp only [sb2]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
  have hget_16step : sb2[16 + step]?.getD 0#32 = new_qn := by
    dsimp only [sb2]
    rw [List.getElem?_set_self (by simp [hsb'_len]; omega), Option.getD_some]
  have hget_row : ∀ nm < 64, sb2[64 + step * 64 + nm]? = sb'[64 + step * 64 + nm]? := fun nm _ => by
    dsimp only [sb2]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hget_par : ∀ nm < 64, sb2[1088 + step * 64 + nm]? = sb'[1088 + step * 64 + nm]? :=
    fun nm _ => by
      dsimp only [sb2]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  refine ⟨hcap, by omega, by omega, fun r hr => ?_⟩
  by_cases hre : r < step
  · obtain ⟨hfr, hq2, hq64, hm⟩ := hmat.2.2.2 r hre
    have hfr_eq : sb2[r]? = s.scratch.scratch_buf[r]? :=
      hget_lt r (by omega) (by omega) (by omega) (by omega) (by omega)
    have hqn_eq : sb2[16 + r]? = s.scratch.scratch_buf[16 + r]? :=
      hget_lt (16 + r) (by omega) (by omega) (by omega) (by omega) (by omega)
    dsimp only; rw [hfr_eq, hqn_eq]
    refine ⟨hfr, hq2, hq64, fun m hm_lt => ?_⟩
    obtain ⟨res, hres_lt, hres_nd, hok, hent, hpar⟩ := hm m hm_lt
    have hcell_eq : sb2[64 + r * 64 + m]? = s.scratch.scratch_buf[64 + r * 64 + m]? :=
      hget_lt (64 + r * 64 + m) (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ⟨res, hres_lt, hres_nd, ?_, fun t ht => ?_, fun hr0 => ?_⟩
    · rw [hcell_eq]; exact bvaRowEntryOk_congr rfl rfl rfl hok
    · rw [hget_lt t (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hent t ht
    · obtain ⟨hpi, hpok⟩ := hpar hr0
      have hpar_eq : sb2[1088 + r * 64 + m]? = s.scratch.scratch_buf[1088 + r * 64 + m]? :=
        hget_lt (1088 + r * 64 + m) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hqprev_eq : sb2[16 + (r - 1)]? = s.scratch.scratch_buf[16 + (r - 1)]? :=
        hget_lt (16 + (r - 1)) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hfprev_eq : sb2[r - 1]? = s.scratch.scratch_buf[r - 1]? :=
        hget_lt (r - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hcprev_eq : sb2[64 + (r - 1) * 64 + (s.scratch.scratch_buf[1088 + r * 64 + m]?.getD
          0#32).toNat]? = s.scratch.scratch_buf[64 + (r - 1) * 64 +
          (s.scratch.scratch_buf[1088 + r * 64 + m]?.getD 0#32).toNat]? := by
        have hqprev64 := (hmat.2.2.2 (r - 1) (by omega)).2.2.1
        exact hget_lt _ (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hpar_eq, hqprev_eq, hfprev_eq, hcprev_eq]
      exact ⟨hpi, bvaRowEntryOk_congr rfl rfl rfl hpok⟩
  · have hreq : r = step := by omega
    subst r; dsimp only; rw [hget_step, hget_16step]
    refine ⟨hbest_lt, hnq2, hnq64, fun nm hnm => ?_⟩
    obtain ⟨hpi, res, hres_lt, hres_nd, hpok, hok, hent_lt, hent_b⟩ := hnew nm hnm
    refine ⟨res, hres_lt, hres_nd, ?_, fun t ht => ?_, fun _ => ?_⟩
    · rw [hget_row nm (by omega)]; exact bvaRowEntryOk_congr rfl rfl rfl hok
    · by_cases hte : t < step
      · rw [hget_lt t (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hent_lt t hte
      · have hts : t = step := by omega
        subst hts; rw [hget_step]; exact hent_b
    · have hqprev64 := (hmat.2.2.2 (step - 1) (by omega)).2.2.1
      have hpar_eq := hget_par nm (by omega)
      have hqprev_eq : sb2[16 + (step - 1)]? = s.scratch.scratch_buf[16 + (step - 1)]? :=
        hget_lt (16 + (step - 1)) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hfprev_eq : sb2[step - 1]? = s.scratch.scratch_buf[step - 1]? :=
        hget_lt (step - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hcprev_eq : sb2[64 + (step - 1) * 64 +
          (sb'[1088 + step * 64 + nm]?.getD 0#32).toNat]? =
          s.scratch.scratch_buf[64 + (step - 1) * 64 +
            (sb'[1088 + step * 64 + nm]?.getD 0#32).toNat]? :=
        hget_lt _ (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hpar_eq, hqprev_eq, hfprev_eq, hcprev_eq]
      exact ⟨hpi, bvaRowEntryOk_congr rfl rfl rfl hpok⟩

private theorem bvaMatrixInv_of_filter_pres {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {sb' : List (BitVec 32)} {step : Nat} (hstep16 : step < 16)
    (hmat : BvaMatrixInv c F_cur s step)
    (hpres : ∀ idx < c.scratch_cap,
      ¬ (64 + step * 64 ≤ idx ∧ idx < 64 + step * 64 + 64) →
      ¬ (1088 + step * 64 ≤ idx ∧ idx < 1088 + step * 64 + 64) →
      sb'[idx]? = s.scratch.scratch_buf[idx]?) :
    BvaMatrixInv c F_cur { s with scratch := { s.scratch with scratch_buf := sb' } } step := by
  have hcap := hmat.1
  refine ⟨hcap, hmat.2.1, hmat.2.2.1, fun r hr => ?_⟩
  obtain ⟨hfr, hq2, hq64, hm⟩ := hmat.2.2.2 r hr
  have hr_eq : sb'[r]? = s.scratch.scratch_buf[r]? :=
    hpres r (by omega) (by omega) (by omega)
  have h16_eq : sb'[16 + r]? = s.scratch.scratch_buf[16 + r]? :=
    hpres (16 + r) (by omega) (by omega) (by omega)
  dsimp only; rw [hr_eq, h16_eq]
  refine ⟨hfr, hq2, hq64, fun m hm_lt => ?_⟩
  obtain ⟨res, hres_lt, hres_nd, hok, hent, hpar⟩ := hm m hm_lt
  have hc_eq : sb'[64 + r * 64 + m]? = s.scratch.scratch_buf[64 + r * 64 + m]? :=
    hpres (64 + r * 64 + m) (by omega) (by omega) (by omega)
  refine ⟨res, hres_lt, hres_nd, ?_, fun t ht => ?_, fun hr0 => ?_⟩
  · rw [hc_eq]; exact bvaRowEntryOk_congr rfl rfl rfl hok
  · rw [hpres t (by omega) (by omega) (by omega)]; exact hent t ht
  · obtain ⟨hpi, hpok⟩ := hpar hr0
    have hp_eq : sb'[1088 + r * 64 + m]? = s.scratch.scratch_buf[1088 + r * 64 + m]? :=
      hpres (1088 + r * 64 + m) (by omega) (by omega) (by omega)
    have hqprev64 := (hmat.2.2.2 (r - 1) (by omega)).2.2.1
    rw [hp_eq, hpres (16 + (r - 1)) (by omega) (by omega) (by omega),
      hpres (r - 1) (by omega) (by omega) (by omega),
      hpres (64 + (r - 1) * 64 + (s.scratch.scratch_buf[1088 + r * 64 + m]?.getD 0#32).toNat)
        (by omega) (by omega) (by omega)]
    exact ⟨hpi, bvaRowEntryOk_congr rfl rfl rfl hpok⟩

private theorem bv8_setWidth_and_fe (x : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x &&& 254#32) = x &&& 0xFE#8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  have hx := x.isLt
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hx)]

private theorem bva_try_lit_clear_lm_step {sb : List (BitVec 32)} {lmi : List (BitVec 8)}
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

private theorem bva_try_lit_clear_lm_done {c : FullCfg} {stf : FullState}
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

private theorem bva_try_lit_extend_lm {maxv cap step : Nat}
    {lm : List (BitVec 8)} {sb2 sb3 : List (BitVec 32)} {bl new_qn : BitVec 32}
    (hcap : 2304 ≤ cap) (hstep16 : step < 16)
    (hlm_l : lm.length = 2 * maxv) (hsb3_l : sb3.length = cap)
    (hbl_lt : bl.toNat < 2 * maxv)
    (hpres : ∀ idx < cap,
      ¬ (64 + step * 64 ≤ idx ∧ idx < 64 + step * 64 + 64) →
      ¬ (1088 + step * 64 ≤ idx ∧ idx < 1088 + step * 64 + 64) →
      sb3[idx]? = sb2[idx]?)
    (hhi : ∀ l < 2 * maxv, (lm[l]?.getD 0#8 &&& 0xFE#8) = 0#8)
    (hset : ∀ r < step, (lm[(sb2[r]?.getD 0#32).toNat]?.getD 0#8 &&& 1#8) ≠ 0#8)
    (honly : ∀ l < 2 * maxv, (lm[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
      ∃ r < step, (sb2[r]?.getD 0#32).toNat = l) :
    let lm4 := lm.set bl.toNat 1#8
    let sb4 := (sb3.set step bl).set (16 + step) new_qn
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
    · have hreq : ((sb3.set step bl).set (16 + step) new_qn)[r]? = sb2[r]? := by
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hpres r (by omega) (by omega) (by omega)
      rw [hreq]
      by_cases hlb : (sb2[r]?.getD 0#32).toNat = bl.toNat
      · rw [hlb, List.getElem?_set_self (by omega), Option.getD_some]; decide
      · rw [List.getElem?_set_ne (Ne.symm hlb)]; exact hset r hrs
    · have hr_eq : r = step := by omega
      subst r
      have hsb_st : ((sb3.set step bl).set (16 + step) new_qn)[step]?.getD 0#32 = bl := by
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

private theorem bva_try_lit_lm1_init {maxv cap : Nat} {sb : List (BitVec 32)}
    {lm : List (BitVec 8)} {f0 qn : BitVec 32}
    (hcap : 2304 ≤ cap) (hsb_l : sb.length = cap) (hlm_l : lm.length = 2 * maxv)
    (hf0_lt : f0.toNat < 2 * maxv)
    (hlm_zero : ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8) :
    let sb1 := (sb.set 0 f0).set 16 qn
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

end FullBvaTryLitHelpers

theorem full_bva_try_lit_wp (Γ : Env)
    (hScan : ∀ args m Q X, fullBvaScanCandsSpec args m Q X →
      Γ "full_bva_scan_cands" [i64, i32, i32, i64] [i32] args m Q X)
    (hPick : ∀ args m Q X, fullBvaPickCandSpec args m Q X →
      Γ "full_bva_pick_cand" [i64, i32, i32] [i32] args m Q X)
    (hFilter : ∀ args m Q X, fullBvaFilterRowSpec args m Q X →
      Γ "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32] args m Q X)
    (hCommit : ∀ args m Q X, fullBvaCommitSpec args m Q X →
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
    have hcap_ge : 2304 ≤ c.scratch_cap := by
      have h1 : ¬ c.scratch_cap % 2 ^ 64 < (2304 : BitVec 64).toNat := by assumption
      change ¬ c.scratch_cap % 2 ^ 64 < 2304 at h1; omega
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
      -- Row-0 collection loop `while (p < end && qn < 64u)`
      refine wp_loop_inv
        (fun (qn, p, ()) mp => ∃ sb : List (BitVec 32),
          off0 ≤ p.toNat ∧ p.toNat ≤ off0 + sz0 ∧ qn.toNat ≤ 64 ∧
          sb.length = c.scratch_cap ∧
          DenseWatchSliceOk F_cur s.core f0.toNat p.toNat (off0 + sz0 - p.toNat) ∧
          (∀ i < qn.toNat, ∃ res : List Nat,
            (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
            BvaRowEntryOk F_cur s f0.toNat (sb[64 + i]?.getD 0#32) res ∧
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
      -- Exit join point `Jend` inside loop body (from `while (p < end && qn < 64u)`)
      refine wp_join_state0 (α := Unit)
        (fun _ mf => mf = mp)
        (fun _ _ mf hmf => ?_)
        (fun Jend hJend => ?_)
      rotate_left
      · -- Loop condition & body of `while (p < end && qn < 64u)`
        c0_hsplit
        · c0_hsplit
          · have hp_lt : p.toNat < off0 + sz0 := by rw [← hend_mod]; assumption
            have hqn_lt : qn.toNat < 64 := by
              have h1 : qn.toNat < (64 : BitVec 32).toNat := by assumption
              exact h1
            have hp_ws : p.toNat < s.core.wstk.length := by omega
            have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by simp only [bv_c0]; omega
            have hp1_mod : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
              rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
            have hqn1_n : (qn + 1#32).toNat = qn.toNat + 1 := by simp only [bv_c0]; omega
            have h64qn : ((64 : BitVec 32) + qn).toNat = 64 + qn.toNat := by
              simp only [BitVec.toNat_add, show (64 : BitVec 32).toNat = 64 from rfl]; omega
            c0_hsteps_nogrp
            c0_hstep
            c0_hsplit
            · -- Binary watch `w0`
              have hbin : (s.core.wstk[p.toNat]'hp_ws &&& 0x80000000#32) ≠ 0#32 := by assumption
              have ⟨hot_lt, hent_ot, hrem_next⟩ :=
                FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hp_ws hbin
              have hot_v : (BitVec.setWidth 64
                  (s.core.wstk[p.toNat]'hp_ws &&& 0x7FFFFFFF#32)).toNat < s.core.vals.length := by
                rw [bv64_setWidth_32]; omega
              c0_hfast
              · -- `vals[ot] == 0`: write `sb[64 + qn] = w0`, `qn++`
                refine ihp (qn + 1#32, p + 1#64, ()) _ (by dsimp only; rw [hp1_n]; omega)
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
                    unfold BvaRowEntryOk; rw [ite_eq_left hbin]
                    exact ⟨hot_lt, rfl, hent_ot⟩
                  · rw [List.getElem?_set_ne (by omega)]; exact hrow0 i (by omega)
                · simp only [bv64_setWidth_32, h64qn] at hm; exact hm
              · exact ihp (qn, p + 1#64, ()) mp (by dsimp only; rw [hp1_n]; omega)
                  ⟨sb, by rw [hp1_n]; omega, by rw [hp1_n]; omega, hqn_le, hsb_l,
                   by rw [hp1_n, show off0 + sz0 - (p.toNat + 1) = off0 + sz0 - p.toNat - 1
                        by omega]; exact hrem_next, hrow0, hmp⟩
            · -- Large clause watch `cr`: check `p + 1 < end`
              have hbin0 : (s.core.wstk[p.toNat]'hp_ws &&& 0x80000000#32) = 0#32 := by assumption
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
                have hsz5 : fullArenaClauseSizeCore s.core cr.toNat ≤ 5 := by
                  rw [← hsz_cr]
                  have h1 : (s.core.arena[((s.core.wstk[(p.toNat +
                      BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                        rw [hp1_mod]; exact hp1_ws)).toNat +
                      BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                        rw [hcr_mod, hcr2_mod]; omega)).toNat ≤ (5 : BitVec 32).toNat := by
                    assumption
                  simp only [hcr_mod, hcr2_mod] at h1; exact h1
                -- Inner `hk < sz` loop checking `has_f0` with `break`
                refine wp_join_state (α := BitVec 32 × Bool)
                  (fun ⟨hkf, hf⟩ => (hkf, hf, ()))
                  (fun ⟨_, hf⟩ mhf =>
                    (hf = true → f0.toNat ∈ fullArenaClauseLitsCore s.core cr.toNat) ∧ mhf = mp)
                  (fun _ ⟨_, has_f0⟩ mhf ⟨hhf_ok, hmhf⟩ => ?_)
                  (fun Jhf hJhf => ?_)
                · subst mhf
                  c0_hfast
                  · obtain ⟨res, hres_lt, hres_nd, hok, hent⟩ :=
                      bvaRowEntryOk_of_large_f0 hinv hcr_ref hng_cr hsz3 hsz5
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
                    (fun (hk, ()) mhk =>
                      hk.toNat ≤ (s.core.arena[cr.toNat + 2]'(by omega)).toNat ∧ mhk = mp)
                    (fun (hk, _) _ => (s.core.arena[cr.toNat + 2]'(by omega)).toNat - hk.toNat)
                    (fun Jhk hJhk => by c0_hfast; exact hJhk (0#32, ()) mp ⟨Nat.zero_le _, rfl⟩)
                    (fun Jhk (hk, ()) mhk ⟨hhk_le, hmhk⟩ ihhk => ?_)
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
                    have hhk1 : (hk + 1#32).toNat = hk.toNat + 1 := by simp only [bv_c0]; omega
                    c0_hsplit
                    · c0_hfast
                      refine hJhf ⟨hk, true⟩ mp ⟨fun _ => ?_, rfl⟩
                      have hmem := List.mem_of_getElem?
                        (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem
                          (k := s.core) (r := cr.toNat) (j := hk.toNat)
                          (by rw [← hsz_cr]; exact hhk_lt) (by omega))
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
                      rwa [heq] at hmem
                    · c0_hfast
                      exact ihhk (hk + 1#32, ()) mp (by dsimp only; rw [hhk1]; omega)
                        ⟨by rw [hhk1]; omega, rfl⟩
                  · c0_hfast; exact hJhf ⟨hk, false⟩ mp ⟨(fun h => by cases h), rfl⟩
              all_goals
                exact ihp (qn, p + 1#64 + 1#64, ()) mp (by dsimp only; rw [hp2_n]; omega)
                  ⟨sb, by rw [hp2_n]; omega, by rw [hp2_n]; omega, hqn_le, hsb_l,
                   by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                        by omega]; exact hrem_next, hrow0, hmp⟩
          · exact hJend () mp rfl
        · exact hJend () mp rfl
      · -- Exit Row-0 collection loop (elaborated once!): `if (qn < 2u) return false;`
        subst mf
        c0_hsplit
        · c0_hfast
          exact hQ false _ mp
            (fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len)
              (sc' := { s.scratch with scratch_buf := sb }) hinv hcl.repr_len hcl.min_clr_len_arr
              hcl.tmp_len_arr hcl.flags_len hcl.tmp_len_le { hsc with scratch_buf_len := hsb_l }
              rfl rfl).toDense (Nat.le_refl _) rfl rfl rfl hmp
        · -- `2 ≤ qn`: initialize row 0 in `scr[0]`, `scr[16]`, `lm[f0] = 1`, run `step` loop
          have hqn2 : 2 ≤ qn.toNat := by
            have h1 : ¬ qn.toNat < (2 : BitVec 32).toNat := by assumption
            change ¬ qn.toNat < 2 at h1; omega
          have hsb0_lt : (BitVec.ofNat 64 0).toNat < sb.length := by
            simp only [BitVec.toNat_ofNat]; rw [hsb_l]; omega
          have hsb16_lt : (BitVec.ofNat 64 16).toNat < sb.length := by
            simp only [BitVec.toNat_ofNat]; rw [hsb_l]; omega
          have hlm_f0 : (BitVec.setWidth 64 f0).toNat < s.core.lit_mark.length := by
            rw [bv64_setWidth_32, hlm_len]; omega
          have hinit_lits : (init_cv <<< (1 : Nat)).toNat = 2 * init_cv.toNat := by
            rw [bv64_shl1_nat]; omega
          have hmat1 := bvaMatrixInv_step1 hcap_ge hsb_l hf0_lt hqn2 hqn_le hrow0
          let sb1 := (sb.set 0 f0).set 16 qn
          let lm1 := s.core.lit_mark.set f0.toNat 1#8
          have hsb1_l : sb1.length = c.scratch_cap := by simp [sb1, hsb_l]
          have hlm1_l : lm1.length = 2 * c.max_vars := by simp [lm1, hlm_len]
          have ⟨hlm1_hi, hlm1_set, hlm1_only⟩ := bva_try_lit_lm1_init (f0 := f0) (qn := qn)
            hcap_ge hsb_l hlm_len (by omega) hinv.2.2.1.2
          have hinv1_core : FullState.LengthsOk c
              { core := { s.core with lit_mark := lm1 }
                scratch := { s.scratch with scratch_buf := sb1 } } :=
            ⟨{ hcl with lit_mark_len := hlm1_l }, { hsc with scratch_buf_len := hsb1_l }⟩
          c0_hsteps_nogrp
          -- Join point `Jstep` after `while (step < 16u && cur_qn >= 2u)` (due to `break`s)
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
              1 ≤ stepf.toNat ∧ stepf.toNat ≤ 16 ∧
              BvaMatrixInv c F_cur stf stepf.toNat ∧
              (bestkf = 0#32 ∨ (1 ≤ bestkf.toNat ∧ bestkf.toNat < stepf.toNat)) ∧
              (∀ l < 2 * c.max_vars, (stf.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
              (∀ l < 2 * c.max_vars, (stf.core.lit_mark[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
                ∃ r < stepf.toNat, (stf.scratch.scratch_buf[r]?.getD 0#32).toNat = l))
            (fun _ ⟨stepf, _, bestkf, _, stf⟩ mf ⟨hmf, hlenf, hwf, hndf, hextf, hlv0f, hdmf, hcvf,
                hfuelf, harf, half, hmrkf, htmf, htrf, hst1, hst16, hmatf, hbkf, hlmf_hi,
                hlmf_only⟩ => ?_)
            (fun Jstep hJstep => ?_)
          · -- Cleanup loop `while (si < stepf) { lm[scr[si]] &= 0xFE; }` -> `full_bva_commit`
            have hlmf_l := hlenf.core_ok.lit_mark_len
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
              have hscr_si_b : (BitVec.setWidth 64 (stf.scratch.scratch_buf[
                  (BitVec.setWidth 64 si).toNat]'(by
                    rw [bv64_setWidth_32, hsbf_l]; omega))).toNat < lmi.length := by
                simp only [bv64_setWidth_32]; omega
              let xl := (stf.scratch.scratch_buf[si.toNat]'(by omega)).toNat
              c0_hfast
              have ⟨hhi', honly'⟩ := bva_try_lit_clear_lm_step hsi_lt (by omega) hlmi_l
                (by omega) hlmi_hi hlmi_only
              refine ihsi (si + 1#32, ()) m (by dsimp only; rw [hsi1]; omega)
                ⟨lmi.set xl ((lmi[xl]'(by omega)) &&& 0xFE#8),
                 by rw [hsi1]; omega, by simp [hlmi_l], hhi',
                 by simpa only [hsi1] using honly',
                 by simp only [xl, bv64_setWidth_32, bv8_setWidth_and_fe] at hm ⊢; exact hm⟩
            · -- Exit cleanup loop: `FullLitMarksClear` restored!
              have hsi_eq : si.toNat = stepf.toNat := by
                have h1 : ¬ si.toNat < stepf.toNat := by assumption
                omega
              have hlm_clr : FullLitMarksClear c
                  { stf with core := { stf.core with lit_mark := lmi } } :=
                bva_try_lit_clear_lm_done
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
                · c0_call hCommit
                  refine ⟨c, F0, F_cur, st_clr, R, rfl, hinv_clr, hbk1, by omega,
                    bvaMatrixInv_weaken_step (by omega) (by omega)
                      (bvaMatrixInv_congr rfl rfl rfl rfl hmatf),
                    hmsi, fun ok s' m' hinv' hcv' hfuel' htm' htr' hm' =>
                      hQ ok s' m' hinv' (by dsimp only [st_clr] at hcv'; omega)
                        (hfuel'.trans hfuelf) (htm'.trans htmf) (htr'.trans htrf) hm'⟩
          · -- Main `while (step < 16u && cur_qn >= 2u)` loop
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
                1 ≤ step.toNat ∧ step.toNat ≤ 16 ∧
                cur_qn.toNat =
                  (stl.scratch.scratch_buf[16 + (step.toNat - 1)]?.getD 0#32).toNat ∧
                BvaMatrixInv c F_cur stl step.toNat ∧
                (best_k = 0#32 ∨ (1 ≤ best_k.toNat ∧ best_k.toNat < step.toNat)) ∧
                (∀ l < 2 * c.max_vars, (stl.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
                (∀ r < step.toNat,
                  (stl.core.lit_mark[(stl.scratch.scratch_buf[r]?.getD 0#32).toNat]?.getD 0#8 &&&
                    1#8) ≠ 0#8) ∧
                (∀ l < 2 * c.max_vars, (stl.core.lit_mark[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
                  ∃ r < step.toNat, (stl.scratch.scratch_buf[r]?.getD 0#32).toNat = l))
              (fun (step, _, _, _, _) _ => 16 - step.toNat)
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
                      rw [show 16 + ((1#32).toNat - 1) = 16 from rfl,
                        List.getElem?_set_self (by simp [hsb_l]; omega), Option.getD_some],
                   bvaMatrixInv_congr rfl rfl rfl rfl hmat1,
                   Or.inl rfl, hlm1_hi, hlm1_set, hlm1_only⟩)
              (fun Jst (step, cur_qn, best_k, best_red, ()) ml
                  ⟨stl, hml, hlenl, hwl, hndl, hextl, hlv0l, hdml, hcvl, hfuell, harl, hall,
                   hmrkl, html, htrl, hst1, hst16, hcurqn_eq, hmatl, hbkl, hlml_hi, hlml_set,
                   hlml_only⟩ ihst => ?_)
            c0_hfast
            · -- Body: `scan_cands` -> `pick_cand` -> `filter_row` -> update `scr`/`lm`/`best_k`
              have hst_lt : step.toNat < 16 := by
                have h1 : step.toNat < (16 : BitVec 32).toNat := by assumption
                exact h1
              have hrow_off :
                  ((64 : BitVec 32) + (step - 1) * 64).toNat = 64 + (step.toNat - 1) * 64 := by
                simp only [BitVec.toNat_add, BitVec.toNat_mul,
                  BitVec.toNat_sub_of_le (show (1 : BitVec 32).toNat ≤ step.toNat from hst1),
                  show (64 : BitVec 32).toNat = 64 from rfl,
                  show (1 : BitVec 32).toNat = 1 from rfl]
                omega
              have hqn64_l : cur_qn.toNat ≤ 64 := by
                rw [hcurqn_eq]; exact (hmatl.2.2.2 (step.toNat - 1) (by omega)).2.2.1
              c0_call hScan
              refine ⟨c, F0, F_cur, stl, R, rfl, hlenl, hwl, hndl, hextl, hlv0l, hdml,
                by rw [hinit_lits, hcvl]; omega, hlml_hi, by rw [hrow_off]; omega, hqn64_l,
                fun qi hqi => ?_, hml,
                fun ncntd ws' ws1' ws2' m1 hlen1 hnc_le hws1_ok hm1 => ?_⟩
              · rw [hrow_off]
                rw [hcurqn_eq] at hqi
                obtain ⟨res, _, _, hok, _, _⟩ :=
                  (hmatl.2.2.2 (step.toNat - 1) (by omega)).2.2.2 qi hqi
                unfold BvaRowEntryOk at hok
                by_cases hbin :
                    (stl.scratch.scratch_buf[64 + (step.toNat - 1) * 64 + qi]?.getD 0#32 &&&
                      0x80000000#32) ≠ 0#32
                · rw [ite_eq_left hbin] at hok ⊢; exact hok.1
                · rw [ite_eq_right hbin] at hok ⊢; exact ⟨hok.1, hok.2.1⟩
              · -- After `scan_cands`: call `pick_cand`
                rw [hinit_lits] at hnc_le hws1_ok
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
                have hmat2 : BvaMatrixInv c F_cur st2 step.toNat :=
                  bvaMatrixInv_congr rfl rfl rfl rfl hmatl
                c0_hfast
                · exact hJstep ⟨step, cur_qn, best_k, best_red, st2⟩ m2 ⟨hm2, hinv2.1, hinv2.2.1,
                    hinv2.2.2.1, hinv2.2.2.2.1, hinv2.2.2.2.2.1, hinv2.2.2.2.2.2, hcvl, hfuell,
                    harl, hall, hmrkl, html, htrl, hst1, hst16, hmat2, hbkl, hlml_hi, hlml_only⟩
                · have hbl_lt : bl.toNat < 2 * s.core.cur_vars := by
                    rcases hbl_ok with hff | hlt
                    · exact absurd hff (by assumption)
                    · dsimp only [st1] at hlt; omega
                  have hnrow_off :
                      ((64 : BitVec 32) + step * 64).toNat = 64 + step.toNat * 64 := by
                    simp only [BitVec.toNat_add, BitVec.toNat_mul,
                      show (64 : BitVec 32).toNat = 64 from rfl]
                    omega
                  have hpar_off :
                      ((1088 : BitVec 32) + step * 64).toNat = 1088 + step.toNat * 64 := by
                    simp only [BitVec.toNat_add, BitVec.toNat_mul,
                      show (1088 : BitVec 32).toNat = 1088 from rfl,
                      show (64 : BitVec 32).toNat = 64 from rfl]
                    omega
                  c0_call hFilter
                  refine ⟨c, F0, F_cur, st2, R, step.toNat, rfl, hinv2.1, hinv2.2.1,
                    hinv2.2.2.1, hinv2.2.2.2.1, hinv2.2.2.2.2.1, hinv2.2.2.2.2.2, hst1, hst_lt,
                    hcap_ge, hrow_off, hnrow_off, hpar_off, hcurqn_eq,
                    by dsimp only [st2, st1]; omega, hmat2, hlml_hi, hlml_set, hm2,
                    fun new_qn sb3 m3 hlen3 hnq64 hpres3 hnew3 hm3 => ?_⟩
                  let st3 : FullState :=
                    { st2 with scratch := { st2.scratch with scratch_buf := sb3 } }
                  have hpres3' : ∀ idx < c.scratch_cap,
                      ¬ (64 + step.toNat * 64 ≤ idx ∧ idx < 64 + step.toNat * 64 + 64) →
                      ¬ (1088 + step.toNat * 64 ≤ idx ∧ idx < 1088 + step.toNat * 64 + 64) →
                      sb3[idx]? = st2.scratch.scratch_buf[idx]? := fun idx hi h1 h2 =>
                    hpres3 idx hi (by rw [hnrow_off]; exact h1) (by rw [hpar_off]; exact h2)
                  c0_hsplit
                  · -- `new_qn < 2`: break
                    c0_hfast
                    refine hJstep ⟨step, cur_qn, best_k, best_red, st3⟩ m3 ⟨hm3, hlen3, hinv2.2.1,
                      hinv2.2.2.1, hinv2.2.2.2.1, hinv2.2.2.2.2.1, hinv2.2.2.2.2.2, hcvl, hfuell,
                      harl, hall, hmrkl, html, htrl, hst1, hst16,
                      bvaMatrixInv_of_filter_pres hst_lt hmat2 hpres3',
                      hbkl, hlml_hi, fun l hl hne => ?_⟩
                    obtain ⟨r, hr, heq⟩ := hlml_only l hl hne
                    refine ⟨r, hr, ?_⟩
                    dsimp only [st3]; rw [hpres3' r (by omega) (by omega) (by omega)]; exact heq
                  · -- `2 ≤ new_qn`: store `scr[step] = bl; scr[16 + step] = new_qn; lm[bl] = 1`
                    have hnq2 : 2 ≤ new_qn.toNat := by
                      have h1 : ¬ new_qn.toNat < (2 : BitVec 32).toNat := by assumption
                      change ¬ new_qn.toNat < 2 at h1; omega
                    have h16step : ((16 : BitVec 32) + step).toNat = 16 + step.toNat := by
                      simp only [BitVec.toNat_add, show (16 : BitVec 32).toNat = 16 from rfl]; omega
                    have hstep1_n : (step + 1#32).toNat = step.toNat + 1 := by
                      simp only [BitVec.toNat_add, show (1#32).toNat = 1 from rfl]; omega
                    let sb4 := (sb3.set step.toNat bl).set (16 + step.toNat) new_qn
                    let lm4 := st2.core.lit_mark.set bl.toNat 1#8
                    have hsb3_l : sb3.length = c.scratch_cap := hlen3.scratch_ok.scratch_buf_len
                    have hlm3_l : st2.core.lit_mark.length = 2 * c.max_vars :=
                      hlen3.core_ok.lit_mark_len
                    have hsb4_l : sb4.length = c.scratch_cap := by simp [sb4, hsb3_l]
                    have hlm4_l : lm4.length = 2 * c.max_vars := by simp [lm4, hlm3_l]
                    have hmat4 := bvaMatrixInv_extend_step hst1 hst_lt hmat2 hsb3_l
                      (by dsimp only [st2, st1]; rw [hcvl]; exact hbl_lt) hnq2 hnq64 hpres3'
                      (fun nm hnm => by
                        have h1 := hnew3 nm hnm
                        rw [hrow_off, hnrow_off, hpar_off, hcurqn_eq] at h1; exact h1)
                    let st4 : FullState :=
                      { core := { st2.core with lit_mark := lm4 }
                        scratch := { st2.scratch with scratch_buf := sb4 } }
                    have hbl_lm : (BitVec.setWidth 64 bl).toNat < st2.core.lit_mark.length := by
                      rw [bv64_setWidth_32, hlm3_l]; omega
                    have h16st_b : (BitVec.setWidth 64 ((16 : BitVec 32) + step)).toNat <
                        (sb3.set step.toNat bl).length := by
                      rw [bv64_setWidth_32, h16step, List.length_set, hsb3_l]; omega
                    c0_hsteps_nogrp
                    refine wp_join_state (α := BitVec 32 × BitVec 64)
                      (fun ⟨bk', br'⟩ => (bk', br', ()))
                      (fun ⟨bk', _⟩ mf4 =>
                        (bk' = 0#32 ∨ (1 ≤ bk'.toNat ∧ bk'.toNat < step.toNat + 1)) ∧ mf4 = m)
                      (fun _ ⟨bk', br'⟩ mf4 ⟨hbk', hmf4⟩ => ?_)
                      (fun Jbk hJbk => ?_)
                    · subst mf4
                      c0_hfast
                      have ⟨hlm4_hi, hlm4_set, hlm4_only⟩ := bva_try_lit_extend_lm (bl := bl)
                        (new_qn := new_qn) hcap_ge hst_lt hlm3_l hsb3_l (by omega) hpres3'
                        hlml_hi hlml_set hlml_only
                      refine ihst (step + 1#32, new_qn, bk', br', ()) m
                        (by dsimp only; rw [hstep1_n]; omega)
                        ⟨st4, by simp only [bv64_setWidth_32, h16step] at hm; exact hm,
                         ⟨{ hlen3.core_ok with lit_mark_len := hlm4_l },
                          { hlen3.scratch_ok with scratch_buf_len := hsb4_l }⟩,
                         { hinv2.2.1 with
                           arena := { hinv2.2.1.arena with len_ok := hinv2.2.1.arena.len_ok }
                           watches := hinv2.2.1.watches.with_wstk rfl rfl rfl rfl rfl
                             (fun _ hr => hr) },
                         hinv2.2.2.1, hinv2.2.2.2.1, hinv2.2.2.2.2.1, hinv2.2.2.2.2.2,
                         hcvl, hfuell, harl, hall, hmrkl, html, htrl, by rw [hstep1_n]; omega,
                         by rw [hstep1_n]; omega,
                         by dsimp only [st4, sb4]
                            rw [hstep1_n, Nat.add_sub_cancel,
                              List.getElem?_set_self (by simp [hsb3_l]; omega), Option.getD_some],
                         by rw [hstep1_n]; exact bvaMatrixInv_congr rfl rfl rfl rfl hmat4,
                         by rw [hstep1_n]; exact hbk',
                         hlm4_hi, by rw [hstep1_n]; exact hlm4_set,
                         by rw [hstep1_n]; exact hlm4_only⟩
                    · c0_hfast
                      · exact hJbk ⟨step, _⟩ m ⟨Or.inr ⟨hst1, by omega⟩, rfl⟩
                      all_goals
                        exact hJbk ⟨best_k, best_red⟩ m
                          ⟨hbkl.imp id (fun ⟨h1, h2⟩ => ⟨h1, by omega⟩), rfl⟩
            all_goals
              exact hJstep ⟨step, cur_qn, best_k, best_red, stl⟩ ml ⟨hml, hlenl, hwl, hndl, hextl,
                hlv0l, hdml, hcvl, hfuell, harl, hall, hmrkl, html, htrl, hst1, hst16, hmatl, hbkl,
                hlml_hi, hlml_only⟩
    · c0_hfast
      · exact hJicv _ m ⟨by simp only [bv_c0]; omega, rfl⟩
      · exact hJicv init_cv0 m ⟨by
          have h1 : ¬ s.core.cur_vars % 2 ^ 64 < init_cv0.toNat := by assumption
          omega, rfl⟩


end LeanQbe.T.Examples.Kissat.FullBvaHeap
