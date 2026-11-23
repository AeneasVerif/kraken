module

public import LeanQbe.T.Examples.Kissat.FullM5KittenDefFix
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas1
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat `M5` `full_find_definition_m5` `Func.wp` Proof (`Part 3`)

Proves `full_find_definition_m5_wp` against canonical `FullDefSweep.fullFindDefinitionSpec`:
1. VMTF queue repair (`KH_QLAST`, `KH_QSEARCH`, `KH_QSTAMP`, `KO_QNEXT[nv - 1]`) via
   `KittenInvLawsM5.set_nv_vmtf`.
2. Snapshot of 1st-core `(pmask, nmask)` before `full_kitten_shrink`, preserving the valid UNSAT
   gate core if the 2nd `full_kitten_solve_m5(h, 16384)` times out.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM5KittenDefFix

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullDefSweep hiding
  FullLitMarksClear FullArenaVarsNodup FullExtScratchOk FullSparseInv
  FullDenseInv FullDenseInvW FullBveEntryOkW
open Kraken.Bedrock2.Test
open FullCongSpecs FullCongHelpers
open scoped FullArenaTactics FullCongTactics FullDefSweepTactics

/-! ## 1. `KittenInvLawsM5` & Local Dynamic Store Lemma -/

/-- Extended `KittenInvLaws` supporting the M5 VMTF queue-repair writes
(`KH_QLAST`, `KH_QSEARCH`, `KH_QSTAMP`, `KO_QNEXT[nv' - 1]`) after narrowing `KH_NV := nv'`. -/
structure KittenInvLawsM5
    (KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop)
    extends KittenInvLaws KInv where
  set_nv_vmtf : ∀ {nv nv' cls ta scr},
    KInv nv cls ta .fresh scr → 1 ≤ nv' → nv' ≤ nv →
    (scr[256 + 18]?.getD 0#32).toNat = 0 →
    (∀ c ∈ cls, ∀ l ∈ c.2, l < 2 * nv') →
    let scr' := (((((scr.set 256 (BitVec.ofNat 32 nv')).set 262 (BitVec.ofNat 32 nv')).set
      267 (BitVec.ofNat 32 (nv' - 1))).set 268 (BitVec.ofNat 32 (nv' - 1))).set
      269 (BitVec.ofNat 32 nv')).set (256 + 416 + (nv' - 1)) 0xFFFFFFFF#32
    KInv nv' cls ta .fresh scr'

private theorem store_k_dyn {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : 256 + i.toNat < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 ((c.pScratchBuf + 1024#64) + i * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (256 + i.toNat) v } } ⋆ R)
        (storeMem m i32 ((c.pScratchBuf + 1024#64) + i * 4) v) := by
  have heq : (c.pScratchBuf + 1024#64) + i * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (256 + i.toNat)) := by
    have hmul : i * 4 = BitVec.ofNat 64 (i.toNat * 4) := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul]
    rw [BitVec.add_assoc]; congr 1
    rw [hmul, show (1024#64 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, ← BitVec.ofNat_add,
      show 1024 + i.toNat * 4 = 4 * (256 + i.toNat) by omega]
  rw [heq]; exact FullArenaTactics.store_full_scratch_buf v hi hm

attribute [local c0_store] store_k_dyn


private theorem getElem_eq_getElem?_getD {α : Type _} [Inhabited α]
    (l : List α) (i : Nat) (h : i < l.length) (d : α) :
    l[i]'h = l[i]?.getD d := by
  rw [List.getElem?_eq_getElem h, Option.getD_some]

private theorem fullMem_store_tmp0_add0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 0#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 0#64) v) := by
  rw [BitVec.add_zero]; exact FullDefSweepTactics.store_tmp0 v hi hm

attribute [local c0_store] fullMem_store_tmp0_add0

private def fullDefGlobalLit (exp : List (BitVec 32)) (l : Nat) : Nat :=
  2 * (exp[l / 2]?.getD 0#32).toNat + l % 2

private theorem clause_sat_map_fullDefGlobalLit {α : Nat → Bool} {exp : List (BitVec 32)}
    {cl : List Nat} :
    (cnfClause (cl.map (fullDefGlobalLit exp))).Sat α ↔
      (cnfClause cl).Sat (fun v => α (exp[v]?.getD 0#32).toNat) := by
  simp only [clause_sat_cnfClause_iff, List.mem_map, litVar, litSign]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, hsat⟩
    refine ⟨l, hl, ?_⟩
    have hm : (2 * (exp[l / 2]?.getD 0#32).toNat + l % 2) % 2 = l % 2 := by omega
    have hd : (2 * (exp[l / 2]?.getD 0#32).toNat + l % 2) / 2 =
        (exp[l / 2]?.getD 0#32).toNat := by omega
    simpa [fullDefGlobalLit, hm, hd] using hsat
  · rintro ⟨l, hl, hsat⟩
    refine ⟨fullDefGlobalLit exp l, ⟨l, hl, rfl⟩, ?_⟩
    have hm : (2 * (exp[l / 2]?.getD 0#32).toNat + l % 2) % 2 = l % 2 := by omega
    have hd : (2 * (exp[l / 2]?.getD 0#32).toNat + l % 2) / 2 =
        (exp[l / 2]?.getD 0#32).toNat := by omega
    simpa [fullDefGlobalLit, hm, hd] using hsat

private theorem range_map_nodup {f : Nat → Nat} :
    ∀ n : Nat, (∀ i j, i < n → j < n → f i = f j → i = j) →
      ((List.range n).map f).Nodup
  | 0, _ => by simp
  | n + 1, hinj => by
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.nodup_append]
    refine ⟨range_map_nodup n fun i j hi hj heq => hinj i j (by omega) (by omega) heq,
      List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, fun x hx y hy hxy => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi' := List.mem_range.mp hi
    rcases List.mem_singleton.mp hy with rfl
    exact absurd (hinj i n (Nat.lt_succ_of_lt hi') (Nat.lt_succ_self n) hxy) (by omega)

private def DefExpInv (cv nv : Nat) (exp tmk : List (BitVec 32)) : Prop :=
  nv ≤ 128 ∧
  (∀ i < nv, (exp[i]?.getD 0#32).toNat < cv ∧
    tmk[(exp[i]?.getD 0#32).toNat]?.getD 0#32 = BitVec.ofNat 32 (i + 1)) ∧
  (∀ v < cv, tmk[v]?.getD 0#32 ≠ 0#32 → ∃ i < nv, (exp[i]?.getD 0#32).toNat = v)

private theorem defExpInv_zero {s : FullState} (ht : TmkZero s) :
    DefExpInv s.core.cur_vars 0 s.scratch.wsort s.scratch.tarjan_mark :=
  ⟨by omega, fun _ hi => by simp at hi, fun v hv hne => absurd (ht v hv) hne⟩

private theorem defExpInv_le_cv {cv nv : Nat} {exp tmk : List (BitVec 32)}
    (h : DefExpInv cv nv exp tmk) : nv ≤ cv := by
  let xs := (List.range nv).map fun i => (exp[i]?.getD 0#32).toNat
  have hnd : xs.Nodup := by
    refine range_map_nodup nv fun i j hi hj hij => ?_
    have ht1 := (h.2.1 i hi).2; have ht2 := (h.2.1 j hj).2
    rw [hij, ht2] at ht1
    have hbv := congrArg BitVec.toNat ht1
    simp only [BitVec.toNat_ofNat] at hbv
    have h128 := h.1
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hbv
    omega
  have hlt : ∀ x ∈ xs, x < cv := fun x hx => by
    simp only [xs, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact (h.2.1 i hi).1
  simpa [xs] using FullSweepFwdHelpers.nodup_length_le_of_lt hnd hlt

private theorem defExpInv_get {cv nv : Nat} {exp tmk : List (BitVec 32)}
    (h : DefExpInv cv nv exp tmk) {lv : Nat} (hlv : lv < cv)
    (hne : tmk[lv]?.getD 0#32 ≠ 0#32) :
    let idx := ((tmk[lv]?.getD 0#32) - 1#32).toNat
    idx < nv ∧ (exp[idx]?.getD 0#32).toNat = lv := by
  obtain ⟨i, hi, hei⟩ := h.2.2 lv hlv hne
  have ht := (h.2.1 i hi).2
  rw [hei] at ht
  have h128 := h.1
  have hidx : ((tmk[lv]?.getD 0#32) - 1#32).toNat = i := by
    rw [ht]; bv_omega
  exact ⟨hidx ▸ hi, hidx ▸ hei⟩

private theorem defExpInv_push {cv nv : Nat} {exp tmk : List (BitVec 32)}
    (h : DefExpInv cv nv exp tmk) (hnv : nv < 128) {lv : BitVec 32} (hlv : lv.toNat < cv)
    (hz : tmk[lv.toNat]?.getD 0#32 = 0#32)
    (hexp : nv < exp.length) (htmk : lv.toNat < tmk.length) :
    let exp' := exp.set nv lv
    let tmk' := tmk.set lv.toNat (BitVec.ofNat 32 (nv + 1))
    nv < cv ∧ DefExpInv cv (nv + 1) exp' tmk' ∧ (∀ i < nv, exp'[i]? = exp[i]?) := by
  have hle : nv ≤ cv := defExpInv_le_cv h
  have hne_prev : ∀ i < nv, (exp[i]?.getD 0#32).toNat ≠ lv.toNat := fun i hi heq => by
    have ht := (h.2.1 i hi).2
    rw [heq, hz] at ht
    have := congrArg BitVec.toNat ht
    simp only [BitVec.toNat_ofNat] at this
    have h128 := h.1
    rw [Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hlt_cv : nv < cv := by
    let xs := (List.range nv).map fun i => (exp[i]?.getD 0#32).toNat
    have hnd : (lv.toNat :: xs).Nodup := by
      rw [List.nodup_cons]; refine ⟨fun hmem => ?_, ?_⟩
      · simp only [xs, List.mem_map, List.mem_range] at hmem
        obtain ⟨i, hi, heq⟩ := hmem
        exact hne_prev i hi heq
      · refine range_map_nodup nv fun i j hi hj hij => ?_
        have ht1 := (h.2.1 i hi).2; have ht2 := (h.2.1 j hj).2
        rw [hij, ht2] at ht1
        have hbv := congrArg BitVec.toNat ht1
        simp only [BitVec.toNat_ofNat] at hbv
        have h128 := h.1
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hbv
        omega
    have hlt_all : ∀ x ∈ (lv.toNat :: xs), x < cv := fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact hlv
      · simp only [xs, List.mem_map, List.mem_range] at hmem
        obtain ⟨i, hi, rfl⟩ := hmem; exact (h.2.1 i hi).1
    have hres := FullSweepFwdHelpers.nodup_length_le_of_lt hnd hlt_all
    simp only [List.length_cons, xs, List.length_map, List.length_range] at hres
    omega
  refine ⟨hlt_cv, ⟨by omega, fun i hi => ?_, fun v hv hne => ?_⟩,
    fun i hi => List.getElem?_set_ne (by omega)⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · have hei : ((exp.set nv lv)[i]?.getD 0#32).toNat = (exp[i]?.getD 0#32).toNat := by
        rw [List.getElem?_set_ne (by omega)]
      rw [hei]
      refine ⟨(h.2.1 i hlt).1, ?_⟩
      rw [List.getElem?_set_ne (hne_prev i hlt).symm]
      exact (h.2.1 i hlt).2
    · rw [List.getElem?_set_self hexp, Option.getD_some, List.getElem?_set_self htmk,
        Option.getD_some]
      exact ⟨hlv, rfl⟩
  · by_cases hveq : v = lv.toNat
    · subst hveq
      exact ⟨nv, Nat.lt_succ_self nv, by
        rw [List.getElem?_set_self hexp, Option.getD_some]⟩
    · rw [List.getElem?_set_ne (Ne.symm hveq)] at hne
      obtain ⟨i, hi, hei⟩ := h.2.2 v hv hne
      exact ⟨i, Nat.lt_succ_of_lt hi, by rw [List.getElem?_set_ne (by omega), hei]⟩

private def DefTrivialSideOk (s : FullState) (v np nn : Nat) (ts : BitVec 32) : Prop :=
  ts = 0xFFFFFFFF#32 ∨
  ((ts.toNat < np ∨ (64 ≤ ts.toNat ∧ ts.toNat < 64 + nn)) ∧
    let exc := if ts.toNat < 64 then 2 * v else 2 * v + 1
    (cnfOfClauses (level0ForcedUnits s ++
      [bveOccRestLits s exc (s.scratch.scratch_buf[ts.toNat]?.getD 0#32)])).Unsat)

private def DefClsEntryOk (s0 : FullState) (v np nn : Nat) (exp : List (BitVec 32))
    (e : Nat × List Nat) : Prop :=
  (e.1 < np ∨ (64 ≤ e.1 ∧ e.1 < 64 + nn)) ∧ e.2 ≠ [] ∧
  ∀ l ∈ bveOccRestLits s0 (if e.1 < 64 then 2 * v else 2 * v + 1)
      (s0.scratch.scratch_buf[e.1]?.getD 0#32),
    (l < 2 * s0.core.cur_vars ∧ s0.core.vals[l]?.getD 0#8 = 0xFF#8) ∨
    l ∈ e.2.map (fullDefGlobalLit exp)

private def DefClsInv (s0 : FullState) (v np nn nv : Nat) (exp : List (BitVec 32))
    (cls : List (Nat × List Nat)) : Prop :=
  ∀ e ∈ cls, (∀ l ∈ e.2, l < 2 * nv) ∧ DefClsEntryOk s0 v np nn exp e

private theorem defClsInv_mono {s0 : FullState} {v np nn nv nv' : Nat}
    {exp exp' : List (BitVec 32)} {cls : List (Nat × List Nat)}
    (h : DefClsInv s0 v np nn nv exp cls) (hnv : nv ≤ nv')
    (hexp : ∀ i < nv, exp'[i]? = exp[i]?) : DefClsInv s0 v np nn nv' exp' cls := by
  intro e he
  have ⟨hlts, hent⟩ := h e he
  refine ⟨fun l hl => Nat.lt_of_lt_of_le (hlts l hl) (by omega), hent.1, hent.2.1, fun l hl => ?_⟩
  rcases hent.2.2 l hl with hfalse | hmem
  · exact Or.inl hfalse
  · right
    have hmap : e.2.map (fullDefGlobalLit exp') = e.2.map (fullDefGlobalLit exp) := by
      apply List.map_congr_left; intro x hx
      have hxl := hlts x hx
      unfold fullDefGlobalLit; rw [hexp (x / 2) (by omega)]
    rwa [hmap]

private theorem level0ForcedUnits_mem_of_false {s : FullState} {l : Nat}
    (hlt : l < 2 * s.core.cur_vars) (hfalse : s.core.vals[l]?.getD 0#8 = 0xFF#8) :
    [l ^^^ 1] ∈ level0ForcedUnits s := by
  unfold level0ForcedUnits
  rw [List.mem_filterMap]
  refine ⟨l, List.mem_range.mpr hlt, ?_⟩
  simp [hfalse]

private theorem sat_xor1_false {α : Nat → Bool} {l : Nat}
    (h1 : (cnfClause [l]).Sat α) (h2 : (cnfClause [l ^^^ 1]).Sat α) : False := by
  refine (CNF.unsat_iff_not_sat.mp (unsat_of_unit_pair (l := l))) α ?_
  rw [cnf_sat_cnfOfClauses_iff]; intro cl hcl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl <;> assumption

private theorem def_trivial_side_unsat {s : FullState} {exc : Nat} {w : BitVec 32}
    (hfalse : ∀ l ∈ bveOccRestLits s exc w,
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses (level0ForcedUnits s ++ [bveOccRestLits s exc w])).Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hSat
  have hcl := (cnf_sat_cnfOfClauses_iff α _).mp hSat _ (List.mem_append_right _
    (List.mem_singleton.mpr rfl))
  rw [clause_sat_cnfClause_iff] at hcl
  obtain ⟨l, hl, hsat_l⟩ := hcl
  obtain ⟨hlt, hf⟩ := hfalse l hl
  have hu := (cnf_sat_cnfOfClauses_iff α _).mp hSat _ (List.mem_append_left _
    (level0ForcedUnits_mem_of_false hlt hf))
  exact sat_xor1_false
    ((clause_sat_cnfClause_iff α [l]).mpr ⟨l, List.mem_singleton.mpr rfl, hsat_l⟩) hu

private theorem defGateUnsat_of_trivial {s : FullState} {v np nn : Nat} {ts : BitVec 32}
    (hnp : np ≤ 64) (hnn : nn ≤ 64) (hts : DefTrivialSideOk s v np nn ts)
    (hne : ts ≠ 0xFFFFFFFF#32) :
    let pm : BitVec 64 := if ts.toNat < 64 then 1#64 <<< ts.toNat else 0#64
    let nm : BitVec 64 := if 64 ≤ ts.toNat then 1#64 <<< (ts.toNat - 64) else 0#64
    FullDefGateUnsat s v pm nm np nn := by
  intro pm nm ⟨_, _, _⟩
  rcases hts with rfl | ⟨hbd, huns⟩
  · exact absurd rfl hne
  · by_cases h64 : ts.toNat < 64
    · have hts_np : ts.toNat < np := by omega
      have hpm : pm = 1#64 <<< ts.toNat := ite_eq_left h64
      have hnm : nm = 0#64 := ite_eq_right (by omega)
      have hpm_hi : pm >>> np = 0#64 := by
        rw [hpm]; apply BitVec.eq_of_getLsbD_eq; intro b _; simp; omega
      have hnm_hi : nm >>> nn = 0#64 := by rw [hnm]; simp
      refine ⟨hpm_hi, hnm_hi, unsat_of_subclauses (fun cl hcl => ?_) huns⟩
      rw [List.mem_append] at hcl
      rcases hcl with hu | hsing
      · exact List.mem_append_left _ (List.mem_append_left _ hu)
      · rw [List.mem_singleton] at hsing; subst cl
        refine List.mem_append_left _ (List.mem_append_right _ ?_)
        rw [hpm, maskedOccRestCls_single_bit hts_np hnp, List.mem_singleton, ite_eq_left h64]
        simp
    · have hts64 : 64 ≤ ts.toNat := by omega
      have hts_nn : ts.toNat - 64 < nn := by omega
      have hpm : pm = 0#64 := ite_eq_right h64
      have hnm : nm = 1#64 <<< (ts.toNat - 64) := ite_eq_left hts64
      have hpm_hi : pm >>> np = 0#64 := by rw [hpm]; simp
      have hnm_hi : nm >>> nn = 0#64 := by
        rw [hnm]; apply BitVec.eq_of_getLsbD_eq; intro b _; simp; omega
      refine ⟨hpm_hi, hnm_hi, unsat_of_subclauses (fun cl hcl => ?_) huns⟩
      rw [List.mem_append] at hcl
      rcases hcl with hu | hsing
      · exact List.mem_append_left _ (List.mem_append_left _ hu)
      · rw [List.mem_singleton] at hsing; subst cl
        refine List.mem_append_right _ ?_
        rw [hnm, maskedOccRestCls_single_bit hts_nn hnn, List.mem_singleton, ite_eq_right h64,
          show 64 + (ts.toNat - 64) = ts.toNat by omega]

private theorem defGateUnsat_of_kitten_core {s0 : FullState} {v np nn nv : Nat}
    {exp scr_f : List (BitVec 32)} {cls cls_sh : List (Nat × List Nat)}
    {pmask nmask : BitVec 64}
    (hnp : np ≤ 64) (_hnn : nn ≤ 64) (hcls : DefClsInv s0 v np nn nv exp cls)
    (hsub : ∀ e ∈ cls_sh, e ∈ cls)
    (hcore_u : (cnfOfClauses ((kittenCoreClauses cls_sh scr_f).map Prod.snd)).Unsat)
    (hpm_hi : pmask >>> np = 0#64) (hnm_hi : nmask >>> nn = 0#64)
    (hbits : ∀ e ∈ kittenCoreClauses cls_sh scr_f,
      (e.1 < np → (pmask >>> e.1) &&& 1#64 ≠ 0#64) ∧
      (64 ≤ e.1 → e.1 < 64 + nn → (nmask >>> (e.1 - 64)) &&& 1#64 ≠ 0#64)) :
    FullDefGateUnsat s0 v pmask nmask np nn := by
  rintro ⟨_, _, _⟩
  refine ⟨hpm_hi, hnm_hi, ?_⟩
  rw [CNF.unsat_iff_not_sat]; intro α hSat
  rw [CNF.unsat_iff_not_sat] at hcore_u
  apply hcore_u (fun x => α (exp[x]?.getD 0#32).toNat)
  rw [cnf_sat_cnfOfClauses_iff]; intro cl hcl
  rw [List.mem_map] at hcl
  obtain ⟨e, he_core, rfl⟩ := hcl
  have he_cls : e ∈ cls := hsub e (kittenCoreClauses_mem he_core)
  have ⟨_, he1_bd, _, he_lits⟩ := hcls e he_cls
  have hb := hbits e he_core
  have hmem_occ : bveOccRestLits s0 (if e.1 < 64 then 2 * v else 2 * v + 1)
      (s0.scratch.scratch_buf[e.1]?.getD 0#32) ∈
      level0ForcedUnits s0 ++ maskedOccRestCls s0 (2 * v) 0 np pmask ++
        maskedOccRestCls s0 (2 * v + 1) 64 nn nmask := by
    rcases he1_bd with hlt_np | ⟨hle64, hlt64⟩
    · have hlt64 : e.1 < 64 := by omega
      rw [ite_eq_left hlt64]
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      simpa using maskedOccRestCls_mem (s := s0) (except := 2 * v) (off := 0) (cnt := np)
        (mask := pmask) hlt_np (hb.1 hlt_np)
    · have hnot64 : ¬ e.1 < 64 := by omega
      rw [ite_eq_right hnot64]
      refine List.mem_append_right _ ?_
      have he_eq : 64 + (e.1 - 64) = e.1 := by omega
      have hk_lt : e.1 - 64 < nn := by omega
      simpa only [he_eq] using maskedOccRestCls_mem (s := s0) (except := 2 * v + 1)
        (off := 64) (cnt := nn) (mask := nmask) hk_lt (hb.2 hle64 (by omega))
  have hsat_occ := (cnf_sat_cnfOfClauses_iff α _).mp hSat _ hmem_occ
  rw [clause_sat_cnfClause_iff] at hsat_occ
  obtain ⟨l, hl_mem, hl_sat⟩ := hsat_occ
  rcases he_lits l hl_mem with ⟨hl_cv, hf⟩ | hmap
  · exfalso
    have hmem_u := (cnf_sat_cnfOfClauses_iff α _).mp hSat _
      (List.mem_append_left _ (List.mem_append_left _ (level0ForcedUnits_mem_of_false hl_cv hf)))
    exact sat_xor1_false
      ((clause_sat_cnfClause_iff α [l]).mpr ⟨l, List.mem_singleton.mpr rfl, hl_sat⟩) hmem_u
  · rw [← clause_sat_map_fullDefGlobalLit, clause_sat_cnfClause_iff]
    exact ⟨l, hmap, hl_sat⟩

private def defFindState (s : FullState) (exp tmk scr tmp : List (BitVec 32)) : FullState :=
  { s with
    core := { s.core with tmp := tmp }
    scratch := { s.scratch with wsort := exp, tarjan_mark := tmk, scratch_buf := scr } }

private theorem defFindState_core_tmp (s : FullState) (exp tmk scr tmp : List (BitVec 32)) :
    (defFindState s exp tmk scr tmp).core.tmp = tmp := rfl

private theorem defFindState_core_vals (s : FullState) (exp tmk scr tmp : List (BitVec 32)) :
    (defFindState s exp tmk scr tmp).core.vals = s.core.vals := rfl

private theorem defFindState_core_arena (s : FullState) (exp tmk scr tmp : List (BitVec 32)) :
    (defFindState s exp tmk scr tmp).core.arena = s.core.arena := rfl

private theorem defFindState_core_cur_vars (s : FullState) (exp tmk scr tmp : List (BitVec 32)) :
    (defFindState s exp tmk scr tmp).core.cur_vars = s.core.cur_vars := rfl

private theorem defFindState_scratch_wsort (s : FullState)
    (exp tmk scr tmp : List (BitVec 32)) :
    (defFindState s exp tmk scr tmp).scratch.wsort = exp := rfl

private theorem defFindState_scratch_tmk (s : FullState)
    (exp tmk scr tmp : List (BitVec 32)) :
    (defFindState s exp tmk scr tmp).scratch.tarjan_mark = tmk := rfl

private theorem defFindState_scratch_scr (s : FullState)
    (exp tmk scr tmp : List (BitVec 32)) :
    (defFindState s exp tmk scr tmp).scratch.scratch_buf = scr := rfl

attribute [local bv_c0] defFindState_core_vals defFindState_core_arena
  defFindState_core_cur_vars
attribute [local simp, local bv_c0] defFindState_core_tmp defFindState_scratch_wsort
  defFindState_scratch_tmk defFindState_scratch_scr

private theorem fullDenseInvW_defFindState {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {tmp' exp' tmk' scr' : List (BitVec 32)}
    (htl : tmp'.length = c.max_vars) (hel : exp'.length = 2 * c.max_vars)
    (html : tmk'.length = 2 * c.max_vars) (hscl : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur (defFindState s exp' tmk' scr' tmp') :=
  ⟨⟨{ h.1.core_ok with tmp_len_arr := htl },
    { h.1.scratch_ok with wsort_len := hel, tarjan_mark_len := html, scratch_buf_len := hscl }⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private def FindDefIdxBrkInv
    (KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop)
    (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop)
    (v np nn nv_b : BitVec 32) (ab_b : Bool) (ts_b : BitVec 32) (mb : Mem 64) : Prop :=
  ∃ (cls_b : List (Nat × List Nat)) (exp_b tmk_b scr_b tmp_b : List (BitVec 32)),
    let sb := defFindState s exp_b tmk_b scr_b tmp_b
    FullDenseInvW c F0 F_cur sb ∧
    (∀ i < 256, scr_b[i]? = s.scratch.scratch_buf[i]?) ∧
    scr_b[256 + 18]? = some 0#32 ∧
    KInv 128 cls_b true .fresh scr_b ∧
    DefExpInv s.core.cur_vars nv_b.toNat exp_b tmk_b ∧
    DefTrivialSideOk s v.toNat np.toNat nn.toNat ts_b ∧
    DefClsInv s v.toNat np.toNat nn.toNat nv_b.toNat exp_b cls_b ∧
    (ab_b = true → ts_b = 0xFFFFFFFF#32) ∧
    (FullMem c sb ⋆ R) mb

private def FindDefIdxJoinInv
    (KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop)
    (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop)
    (v np nn ts_o nv_n : BitVec 32) (ab_n : Bool) (mn : Mem 64) : Prop :=
  (ab_n = true → ts_o = 0xFFFFFFFF#32) ∧
  ∃ (cls_n : List (Nat × List Nat)) (exp_n tmk_n scr_n tmp_n : List (BitVec 32)),
    let sn := defFindState s exp_n tmk_n scr_n tmp_n
    FullDenseInvW c F0 F_cur sn ∧
    (∀ i < 256, scr_n[i]? = s.scratch.scratch_buf[i]?) ∧
    scr_n[256 + 18]? = some 0#32 ∧
    KInv 128 cls_n true .fresh scr_n ∧
    DefExpInv s.core.cur_vars nv_n.toNat exp_n tmk_n ∧
    DefClsInv s v.toNat np.toNat nn.toNat nv_n.toNat exp_n cls_n ∧
    (FullMem c sn ⋆ R) mn

private def FindDefKBrkInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (scr_i exp_i : List (BitVec 32))
    (nv_i w exc nv_k : BitVec 32) (ab_k sat_k : Bool) (csz_k : BitVec 32)
    (mk : Mem 64) : Prop :=
  nv_i.toNat ≤ nv_k.toNat ∧
  (ab_k = true → sat_k = false) ∧
  ∃ (exp_k tmk_k tmp_k : List (BitVec 32)),
    let sk := defFindState s exp_k tmk_k scr_i tmp_k
    FullDenseInvW c F0 F_cur sk ∧
    DefExpInv s.core.cur_vars nv_k.toNat exp_k tmk_k ∧
    (∀ j < nv_i.toNat, exp_k[j]? = exp_i[j]?) ∧
    (ab_k = false → sat_k = false →
      csz_k.toNat ≤ 128 ∧ csz_k.toNat ≤ tmp_k.length ∧
      (∀ j < csz_k.toNat, (tmp_k[j]?.getD 0#32).toNat < 2 * nv_k.toNat) ∧
      ∀ l ∈ (fullArenaClauseLits s w.toNat).filter (· != exc.toNat),
        (l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8) ∨
        l ∈ (tmp_k.take csz_k.toNat).map (fun x => fullDefGlobalLit exp_k x.toNat)) ∧
    (FullMem c sk ⋆ R) mk

private def FindDefKLpInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (scr_i exp_i : List (BitVec 32))
    (nv_i w exc sz_cl nv_k csz_k k_k : BitVec 32) (mk : Mem 64) : Prop :=
  k_k.toNat ≤ sz_cl.toNat ∧ nv_i.toNat ≤ nv_k.toNat ∧
  csz_k.toNat ≤ k_k.toNat ∧ csz_k.toNat ≤ s.core.cur_vars ∧
  ∃ (exp_k tmk_k tmp_k : List (BitVec 32)),
    let sk := defFindState s exp_k tmk_k scr_i tmp_k
    FullDenseInvW c F0 F_cur sk ∧
    DefExpInv s.core.cur_vars nv_k.toNat exp_k tmk_k ∧
    (∀ j < nv_i.toNat, exp_k[j]? = exp_i[j]?) ∧
    (∀ j < csz_k.toNat, (tmp_k[j]?.getD 0#32).toNat < 2 * nv_k.toNat) ∧
    ((tmp_k.take csz_k.toNat).map (fun x => x.toNat / 2)).Nodup ∧
    (∀ j < csz_k.toNat, ∃ mi < k_k.toNat,
      (exp_k[(tmp_k[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
        (s.core.arena[w.toNat + 3 + mi]?.getD 0#32).toNat / 2) ∧
    (∀ mi < k_k.toNat,
      let lm := (s.core.arena[w.toNat + 3 + mi]?.getD 0#32).toNat
      lm ≠ exc.toNat →
      s.core.vals[lm]?.getD 0#8 ≠ 1#8 ∧
      ((lm < 2 * s.core.cur_vars ∧ s.core.vals[lm]?.getD 0#8 = 0xFF#8) ∨
        lm ∈ (tmp_k.take csz_k.toNat).map (fun x => fullDefGlobalLit exp_k x.toNat))) ∧
    (FullMem c sk ⋆ R) mk

private theorem fullDenseInvW_with_findDef {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {tmp' : List (BitVec 32)} {fuel' : BitVec 64}
    {exp' tmk' scr' : List (BitVec 32)}
    (htl : tmp'.length = c.max_vars) (hel : exp'.length = 2 * c.max_vars)
    (html : tmk'.length = 2 * c.max_vars) (hscl : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with tmp := tmp', fuel := fuel' }
        scratch := { s.scratch with wsort := exp', tarjan_mark := tmk', scratch_buf := scr' } } :=
  ⟨⟨{ h.1.core_ok with tmp_len_arr := htl },
    { h.1.scratch_ok with wsort_len := hel, tarjan_mark_len := html, scratch_buf_len := hscl }⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem def_tmk_clear_step {cv nv i : Nat} {tmk exp : List (BitVec 32)} {v : BitVec 32}
    (_hi : i < nv) (hexp : (exp[i]?.getD 0#32).toNat = v.toNat) (hv_len : v.toNat < tmk.length)
    (ht : ∀ u < cv, tmk[u]?.getD 0#32 ≠ 0#32 →
      ∃ k, i ≤ k ∧ k < nv ∧ (exp[k]?.getD 0#32).toNat = u) :
    ∀ u < cv, (tmk.set v.toNat 0#32)[u]?.getD 0#32 ≠ 0#32 →
      ∃ k, i + 1 ≤ k ∧ k < nv ∧ (exp[k]?.getD 0#32).toNat = u := by
  intro u hu hne
  by_cases huv : u = v.toNat
  · subst huv; rw [List.getElem?_set_self hv_len, Option.getD_some] at hne
    exact absurd rfl hne
  · rw [List.getElem?_set_ne (Ne.symm huv)] at hne
    obtain ⟨k, hik, hkn, hwk⟩ := ht u hu hne
    have hkne : k ≠ i := fun hke => huv (by rw [← hwk, hke, hexp])
    exact ⟨k, by omega, hkn, hwk⟩

private theorem def_tmk_clear_done {cv nv : Nat} {tmk exp : List (BitVec 32)}
    (ht : ∀ u < cv, tmk[u]?.getD 0#32 ≠ 0#32 →
      ∃ k, nv ≤ k ∧ k < nv ∧ (exp[k]?.getD 0#32).toNat = u) :
    ∀ u < cv, tmk[u]?.getD 0#32 = 0#32 := by
  intro u hu; exact Classical.byContradiction fun hne => by
    obtain ⟨_, h1, h2, _⟩ := ht u hu hne; omega

private theorem def_scr256_spec_ext {c : FullCfg} {scr0 scr1 : List (BitVec 32)}
    (h10240 : 10240 ≤ c.scratch_cap)
    (h256 : ∀ k < 256, k < 128 ∨ 132 ≤ k → scr1[k]? = scr0[k]?) :
    ∀ k < c.scratch_cap,
      k < 128 ∨ (132 ≤ k ∧ (k < 256 ∨ c.scratch_cap < 10240)) → scr1[k]? = scr0[k]? := by
  intro k _ hk
  rcases hk with h | ⟨hle, h | h⟩
  · exact h256 k (by omega) (Or.inl h)
  · exact h256 k h (Or.inr hle)
  · exact absurd h (Nat.not_lt_of_ge h10240)

private theorem def_find_call_add_clause {Γ : Env}
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    (hAddCl : ∀ args m Q X, fullKittenAddClauseSpec KInv args m Q X →
      Γ "full_kitten_add_clause_m5" [i64, i32, i64, i32] [.bool] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {cls : List (Nat × List Nat)} {eid sz : BitVec 32} {aEid aSz : Arg Val i32}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    {k : Tup Val [.bool] → Expr Val Cont []}
    (haEid : aEid.val = eid) (haSz : aSz.val = sz)
    (hdw : FullDenseInvW c F0 F_cur s) (hcap : 10240 ≤ c.scratch_cap)
    (hK : KInv 128 cls true .fresh s.scratch.scratch_buf)
    (hsz_lo : 1 ≤ sz.toNat) (hsz_lt16 : sz.toNat < 2 ^ 16) (hsz_le : sz.toNat ≤ s.core.tmp.length)
    (hlits : ∀ j < sz.toNat, (s.core.tmp[j]?.getD 0#32).toNat < 2 * 128)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (ok : Bool) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < 256, scr'[i]? = s.scratch.scratch_buf[i]?) →
      scr'[256 + 18]? = s.scratch.scratch_buf[256 + 18]? →
      (ok = true →
        KInv 128 (cls ++ [(eid.toNat, (s.core.tmp.take sz.toNat).map BitVec.toNat)])
          true .fresh scr') →
      (ok = false → KInv 128 cls true .fresh scr') →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (ok, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i32, i64, i32]) (bs := [.bool]) "full_kitten_add_clause_m5"
      (Arg.var c.hdr, aEid, Arg.var c.pTmp, aSz, ()) k) m := by
  refine wp_call_of_spec _ k ?_
  simp only [vals, Arg.val_var, haEid, haSz]
  refine hAddCl (c.hdr, eid, c.pTmp, sz, ()) m (fun r m' => wp Γ Q X (k r) m') X
    ⟨c, s, 128, cls, true, s.core.tmp, FullSweepFwdHelpers.fullSweepAddRestTmp c s ⋆ R,
      rfl, hdw.1, hcap, hK, hsz_lo, hsz_lt16, hsz_le, hlits,
      FullSweepFwdHelpers.fullMem_focus_addCl_tmp hm,
      fun ok scr' m' hsl h256 h18 ht hf hm' => ?_⟩
  have hhdr : Full.hdrTailWords c
      { s with scratch := { s.scratch with scratch_buf := scr' } } =
      Full.hdrTailWords c
        { s with scratch := { s.scratch with scratch_buf := scr', res_sz := s.scratch.res_sz } } :=
    rfl
  rw [hhdr] at hm'
  exact hk ok scr' m' hsl h256 h18 ht hf (FullSweepFwdHelpers.fullMem_unfocus_addCl_tmp hm')


private def FindDefOuterInv
    (KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop)
    (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (v np nn nv : BitVec 32) (abort_def : Bool)
    (ts side : BitVec 32) (mo : Mem 64) : Prop :=
  side.toNat ≤ 2 ∧
  ∃ (cls : List (Nat × List Nat)) (exp tmk scr tmp : List (BitVec 32)),
    let s1 : FullState :=
      { s with
        core := { s.core with tmp := tmp }
        scratch := { s.scratch with wsort := exp, tarjan_mark := tmk, scratch_buf := scr } }
    FullDenseInvW c F0 F_cur s1 ∧
    (∀ i < 256, scr[i]? = s.scratch.scratch_buf[i]?) ∧
    scr[256 + 18]? = some 0#32 ∧
    KInv 128 cls true .fresh scr ∧
    DefExpInv s.core.cur_vars nv.toNat exp tmk ∧
    DefTrivialSideOk s v.toNat np.toNat nn.toNat ts ∧
    DefClsInv s v.toNat np.toNat nn.toNat nv.toNat exp cls ∧
    (abort_def = true → ts = 0xFFFFFFFF#32) ∧
    (FullMem c s1 ⋆ R) mo


/-! ## 2. Extracted Helpers for `full_find_definition_m5_wp` -/

private def findDefExtractMasksExpr (kPtr : BitVec 64)
    (kAfter : Tup Val [i32, i64, i64] → Expr Val Cont []) : Expr Val Cont [] :=
  Expr.let_ (Op.mk (.zext 32 64) (Arg.imm 2, ())) fun pa =>
  Expr.let_ (Op.mk (.mul i64) (Arg.var pa.fst, Arg.imm 4, ())) fun pb =>
  Expr.let_ (Op.mk (.add i64) (Arg.var kPtr, Arg.var pb.fst, ())) fun pc =>
  Expr.load i32 (Arg.var pc.fst) fun ld6 =>
  Expr.group (sig := [[i32, i64, i64]])
    (fun Jlp => Blocks.cons (fun (p : Tup Val [i32, i64, i64]) =>
      Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var p.fst, Arg.var ld6, ())) fun p39 =>
      Expr.jnz (Arg.var p39.fst)
        (Expr.group (sig := [[i64, i64]])
          (fun _ => Blocks.cons (fun (p40 : Tup Val [i64, i64]) =>
            Expr.let_ (Op.mk (.add i32) (Arg.var p.fst, Arg.imm 1, ())) fun p1 =>
            Expr.jump Jlp.fst (Arg.var p1.fst, Arg.var p40.fst, Arg.var p40.snd.fst, ()))
            Blocks.nil)
          fun Jnx =>
          Expr.let_ (Op.mk (.add i32) (Arg.imm 6816, Arg.var p.fst, ())) fun p40 =>
          Expr.let_ (Op.mk (.zext 32 64) (Arg.var p40.fst, ())) fun p41 =>
          Expr.let_ (Op.mk (.mul i64) (Arg.var p41.fst, Arg.imm 4, ())) fun p42 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var kPtr, Arg.var p42.fst, ())) fun p43 =>
          Expr.load i32 (Arg.var p43.fst) fun ld =>
          Expr.let_ (Op.mk (.and i32) (Arg.var ld, Arg.imm 65536, ())) fun p44 =>
          Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var p44.fst, Arg.imm 0, ())) fun p45 =>
          Expr.jnz (Arg.var p45.fst)
            (Expr.let_ (Op.mk (.add i32) (Arg.imm 7712, Arg.var p.fst, ())) fun p46 =>
             Expr.let_ (Op.mk (.zext 32 64) (Arg.var p46.fst, ())) fun p47 =>
             Expr.let_ (Op.mk (.mul i64) (Arg.var p47.fst, Arg.imm 4, ())) fun p48 =>
             Expr.let_ (Op.mk (.add i64) (Arg.var kPtr, Arg.var p48.fst, ())) fun p49 =>
             Expr.load i32 (Arg.var p49.fst) fun ld =>
             Expr.group (sig := [[i64, i64]])
               (fun _ => Blocks.cons (fun (pm : Tup Val [i64, i64]) =>
                 Expr.jump Jnx.fst (Arg.var pm.fst, Arg.var pm.snd.fst, ())) Blocks.nil)
               fun J64 =>
               Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var ld, Arg.imm 64, ())) fun p50 =>
               Expr.jnz (Arg.var p50.fst)
                 (Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p51 =>
                  Expr.let_ (Op.mk (.shl i64) (Arg.imm 1, Arg.var p51.fst, ())) fun p52 =>
                  Expr.let_ (Op.mk (.or i64) (Arg.var p.snd.fst, Arg.var p52.fst, ())) fun p53 =>
                  Expr.jump J64.fst (Arg.var p53.fst, Arg.var p.snd.snd.fst, ()))
                 (Expr.group (sig := [[i64]])
                   (fun _ => Blocks.cons (fun (p51 : Tup Val [i64]) =>
                     Expr.jump J64.fst (Arg.var p.snd.fst, Arg.var p51.fst, ())) Blocks.nil)
                   fun J128 =>
                   Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var ld, Arg.imm 128, ()))
                     fun p51 =>
                   Expr.jnz (Arg.var p51.fst)
                     (Expr.let_ (Op.mk (.sub i32) (Arg.var ld, Arg.imm 64, ())) fun p52 =>
                      Expr.let_ (Op.mk (.zext 32 64) (Arg.var p52.fst, ())) fun p53 =>
                      Expr.let_ (Op.mk (.shl i64) (Arg.imm 1, Arg.var p53.fst, ())) fun p54 =>
                      Expr.let_ (Op.mk (.or i64) (Arg.var p.snd.snd.fst, Arg.var p54.fst, ()))
                        fun p55 =>
                      Expr.jump J128.fst (Arg.var p55.fst, ()))
                     (Expr.jump J128.fst (Arg.var p.snd.snd.fst, ()))))
            (Expr.jump Jnx.fst (Arg.var p.snd.fst, Arg.var p.snd.snd.fst, ())))
        (kAfter p))
      Blocks.nil)
    fun Jlp => Expr.jump Jlp.fst (Arg.imm 0, Arg.imm 0, Arg.imm 0, ())

private def findDefWriteMasksExpr (scrPtr pm nm : BitVec 64) : Expr Val Cont [] :=
  Expr.group (sig := [[]])
    (fun _ => Blocks.cons (fun (_ : Tup Val []) => Expr.ret ()) Blocks.nil)
    fun Jret =>
    Expr.group (sig := [[]])
      (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
        Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 128, ())) fun p41 =>
        Expr.let_ (Op.mk (.mul i64) (Arg.var p41.fst, Arg.imm 4, ())) fun p42 =>
        Expr.let_ (Op.mk (.add i64) (Arg.var scrPtr, Arg.var p42.fst, ())) fun p43 =>
        Expr.let_ (Op.mk (.trunc 64 32) (Arg.var pm, ())) fun p44 =>
        Expr.store (t := i32) (Arg.var p44.fst) (Arg.var p43.fst) <|
        Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 129, ())) fun p45 =>
        Expr.let_ (Op.mk (.mul i64) (Arg.var p45.fst, Arg.imm 4, ())) fun p46 =>
        Expr.let_ (Op.mk (.add i64) (Arg.var scrPtr, Arg.var p46.fst, ())) fun p47 =>
        Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 32, ())) fun p48 =>
        Expr.let_ (Op.mk (.lshr i64) (Arg.var pm, Arg.var p48.fst, ())) fun p49 =>
        Expr.let_ (Op.mk (.trunc 64 32) (Arg.var p49.fst, ())) fun p50 =>
        Expr.store (t := i32) (Arg.var p50.fst) (Arg.var p47.fst) <|
        Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 130, ())) fun p51 =>
        Expr.let_ (Op.mk (.mul i64) (Arg.var p51.fst, Arg.imm 4, ())) fun p52 =>
        Expr.let_ (Op.mk (.add i64) (Arg.var scrPtr, Arg.var p52.fst, ())) fun p53 =>
        Expr.let_ (Op.mk (.trunc 64 32) (Arg.var nm, ())) fun p54 =>
        Expr.store (t := i32) (Arg.var p54.fst) (Arg.var p53.fst) <|
        Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 131, ())) fun p55 =>
        Expr.let_ (Op.mk (.mul i64) (Arg.var p55.fst, Arg.imm 4, ())) fun p56 =>
        Expr.let_ (Op.mk (.add i64) (Arg.var scrPtr, Arg.var p56.fst, ())) fun p57 =>
        Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 32, ())) fun p58 =>
        Expr.let_ (Op.mk (.lshr i64) (Arg.var nm, Arg.var p58.fst, ())) fun p59 =>
        Expr.let_ (Op.mk (.trunc 64 32) (Arg.var p59.fst, ())) fun p60 =>
        Expr.store (t := i32) (Arg.var p60.fst) (Arg.var p57.fst) <|
        Expr.jump Jret.fst ()) Blocks.nil)
      fun Jwr =>
      Expr.let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var pm, Arg.imm 0, ())) fun p40 =>
      Expr.jnz (Arg.var p40.fst) (Expr.jump Jwr.fst ())
        (Expr.let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var nm, Arg.imm 0, ())) fun p41 =>
         Expr.jnz (Arg.var p41.fst) (Expr.jump Jwr.fst ()) (Expr.jump Jret.fst ()))

private def findDefKittenCoreM5Expr (hPtr scrPtr : BitVec 64) (nv : BitVec 32) :
    Expr Val Cont [] :=
  Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 256, ())) fun p22 =>
  Expr.let_ (Op.mk (.mul i64) (Arg.var p22.fst, Arg.imm 4, ())) fun p23 =>
  Expr.let_ (Op.mk (.add i64) (Arg.var scrPtr, Arg.var p23.fst, ())) fun p24 =>
  Expr.let_ (Op.mk (.zext 32 64) (Arg.imm 0, ())) fun p25 =>
  Expr.let_ (Op.mk (.mul i64) (Arg.var p25.fst, Arg.imm 4, ())) fun p26 =>
  Expr.let_ (Op.mk (.add i64) (Arg.var p24.fst, Arg.var p26.fst, ())) fun p27 =>
  Expr.store (t := i32) (Arg.var nv) (Arg.var p27.fst) <|
  Expr.let_ (Op.mk (.zext 32 64) (Arg.imm 6, ())) fun p28 =>
  Expr.let_ (Op.mk (.mul i64) (Arg.var p28.fst, Arg.imm 4, ())) fun p29 =>
  Expr.let_ (Op.mk (.add i64) (Arg.var p24.fst, Arg.var p29.fst, ())) fun p30 =>
  Expr.store (t := i32) (Arg.var nv) (Arg.var p30.fst) <|
  Expr.let_ (Op.mk (.zext 32 64) (Arg.imm 18, ())) fun p31 =>
  Expr.let_ (Op.mk (.mul i64) (Arg.var p31.fst, Arg.imm 4, ())) fun p32 =>
  Expr.let_ (Op.mk (.add i64) (Arg.var p24.fst, Arg.var p32.fst, ())) fun p33 =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p33.fst) <|
  Expr.let_ (Op.mk (.zext 32 64) (Arg.imm 11, ())) fun p34 =>
  Expr.let_ (Op.mk (.mul i64) (Arg.var p34.fst, Arg.imm 4, ())) fun p35 =>
  Expr.let_ (Op.mk (.add i64) (Arg.var p24.fst, Arg.var p35.fst, ())) fun p36 =>
  Expr.let_ (Op.mk (.sub i32) (Arg.var nv, Arg.imm 1, ())) fun p37 =>
  Expr.store (t := i32) (Arg.var p37.fst) (Arg.var p36.fst) <|
  Expr.let_ (Op.mk (.zext 32 64) (Arg.imm 12, ())) fun p38 =>
  Expr.let_ (Op.mk (.mul i64) (Arg.var p38.fst, Arg.imm 4, ())) fun p39 =>
  Expr.let_ (Op.mk (.add i64) (Arg.var p24.fst, Arg.var p39.fst, ())) fun p40 =>
  Expr.let_ (Op.mk (.sub i32) (Arg.var nv, Arg.imm 1, ())) fun p41 =>
  Expr.store (t := i32) (Arg.var p41.fst) (Arg.var p40.fst) <|
  Expr.let_ (Op.mk (.zext 32 64) (Arg.imm 13, ())) fun p42 =>
  Expr.let_ (Op.mk (.mul i64) (Arg.var p42.fst, Arg.imm 4, ())) fun p43 =>
  Expr.let_ (Op.mk (.add i64) (Arg.var p24.fst, Arg.var p43.fst, ())) fun p44 =>
  Expr.store (t := i32) (Arg.var nv) (Arg.var p44.fst) <|
  Expr.let_ (Op.mk (.add i32) (Arg.imm 416, Arg.var nv, ())) fun p45 =>
  Expr.let_ (Op.mk (.sub i32) (Arg.var p45.fst, Arg.imm 1, ())) fun p46 =>
  Expr.let_ (Op.mk (.zext 32 64) (Arg.var p46.fst, ())) fun p47 =>
  Expr.let_ (Op.mk (.mul i64) (Arg.var p47.fst, Arg.imm 4, ())) fun p48 =>
  Expr.let_ (Op.mk (.add i64) (Arg.var p24.fst, Arg.var p48.fst, ())) fun p49 =>
  Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p49.fst) <|
  Expr.call (as := [i64, i64]) (bs := [i64]) "full_kitten_solve_m5"
    (Arg.var hPtr, Arg.imm 8192, ()) fun p50 =>
  Expr.let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var p50.fst, Arg.imm 20, ())) fun p51 =>
  Expr.jnz (Arg.var p51.fst) (Expr.ret ()) <|
  Expr.call (as := [i64]) (bs := [i32]) "full_kitten_core_m5" (Arg.var hPtr, ()) fun p52 =>
  Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl) (Arg.var p52.fst, Arg.imm 0, ())) fun p53 =>
  Expr.jnz (Arg.var p53.fst) (Expr.ret ()) <|
  findDefExtractMasksExpr p24.fst fun p57 =>
  Expr.call (as := [i64]) (bs := []) "full_kitten_shrink" (Arg.var hPtr, ()) fun _p59 =>
  Expr.group (sig := [[i32, i32, i64, i64]])
    (fun _ => Blocks.cons (fun (p : Tup Val [i32, i32, i64, i64]) =>
      findDefWriteMasksExpr scrPtr p.snd.snd.fst p.snd.snd.snd.fst) Blocks.nil)
    fun Jif2 =>
    Expr.call (as := [i64, i64]) (bs := [i64]) "full_kitten_solve_m5"
      (Arg.var hPtr, Arg.imm 16384, ()) fun p60 =>
    Expr.let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var p60.fst, Arg.imm 20, ())) fun p61 =>
    Expr.jnz (Arg.var p61.fst)
      (Expr.call (as := [i64]) (bs := [i32]) "full_kitten_core_m5" (Arg.var hPtr, ()) fun pred2 =>
        findDefExtractMasksExpr p24.fst fun p65 =>
        Expr.group (sig := [[i64, i64]])
          (fun _ => Blocks.cons (fun (p67 : Tup Val [i64, i64]) =>
            Expr.jump Jif2.fst
              (Arg.var p65.fst, Arg.var pred2.fst, Arg.var p67.fst, Arg.var p67.snd.fst, ()))
            Blocks.nil)
          fun Ju =>
          Expr.let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var p65.snd.fst, Arg.imm 0, ())) fun p =>
          Expr.jnz (Arg.var p.fst) (Expr.jump Ju.fst (Arg.var p65.snd.fst, Arg.var p65.snd.snd.fst,
            ()))
            (Expr.let_ (Op.mk (.cmp .ne i64 .bool rfl)
                (Arg.var p65.snd.snd.fst, Arg.imm 0, ())) fun p =>
             Expr.jnz (Arg.var p.fst)
               (Expr.jump Ju.fst (Arg.var p65.snd.fst, Arg.var p65.snd.snd.fst, ()))
               (Expr.jump Ju.fst (Arg.var p57.snd.fst, Arg.var p57.snd.snd.fst, ()))))
      (Expr.jump Jif2.fst
        (Arg.var p57.fst, Arg.var p52.fst, Arg.var p57.snd.fst, Arg.var p57.snd.snd.fst, ()))

private theorem def_find_extract_masks_wp {Γ : Env} {Q : Post []} {X : XPost}
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    (hLaws : KittenInvLawsM5 KInv)
    {c : FullCfg} {s s_f : FullState} {R : Mem 64 → Prop} {kPtr : BitVec 64}
    {v np nn nv : Nat} {cls cls_f : List (Nat × List Nat)}
    {exp scr_f : List (BitVec 32)} {mf : Mem 64}
    {kAfter : Tup Val [i32, i64, i64] → Expr Val Cont []}
    (hkPtr : kPtr = c.pScratchBuf + 1024#64)
    (hmf : (FullMem c s_f ⋆ R) mf)
    (hscr_eq : s_f.scratch.scratch_buf = scr_f)
    (h10240 : 10240 ≤ c.scratch_cap) (hscrf_len : scr_f.length = c.scratch_cap)
    (hnp64 : np ≤ 64) (hnn64 : nn ≤ 64)
    (hcls : DefClsInv s v np nn nv exp cls)
    (hsub : ∀ e ∈ cls_f, e ∈ cls)
    (hKf : KInv nv cls_f true .unsatReady scr_f)
    (hcore_u : (cnfOfClauses ((kittenCoreClauses cls_f scr_f).map Prod.snd)).Unsat)
    (hAfter : ∀ ci pm nm, FullDefGateUnsat s v pm nm np nn →
      wp Γ Q X (kAfter (ci, pm, nm, ())) mf) :
    wp Γ Q X (findDefExtractMasksExpr kPtr kAfter) mf := by
  subst hkPtr
  have hsc := c.hscr; unfold dimacsBound at hsc
  have honc_eq : (scr_f[256 + 2]?.getD 0#32).toNat = cls_f.length := hLaws.orig_nc_eq hKf
  have hcls_le : cls_f.length ≤ 512 := (hLaws.cap_ok hKf).2.2.2
  have h258_len : 258 < s_f.scratch.scratch_buf.length := by rw [hscr_eq, hscrf_len]; omega
  unfold findDefExtractMasksExpr
  ds_csteps!
  have honc_len : (s_f.scratch.scratch_buf[256 + 2]'(by omega)).toNat = cls_f.length := by
    rw [← Option.getD_some (a := s_f.scratch.scratch_buf[256 + 2]'_) (b := 0#32),
      ← List.getElem?_eq_getElem (by omega), hscr_eq]
    exact honc_eq
  ds_to_group
  refine wp_loop_inv (ts := [i32, i64, i64])
    (fun (ci, pm, nm, _) mc => mc = mf ∧ ci.toNat ≤ cls_f.length ∧
      pm >>> np = 0#64 ∧ nm >>> nn = 0#64 ∧
      ∀ (j : Nat) (_hj : j < ci.toNat) (hjl : j < cls_f.length),
        (scr_f[256 + 6816 + j]?.getD 0#32 &&& 0x10000#32) ≠ 0#32 →
        ((cls_f[j]'hjl).1 < np → (pm >>> (cls_f[j]'hjl).1) &&& 1#64 ≠ 0#64) ∧
        (64 ≤ (cls_f[j]'hjl).1 → (cls_f[j]'hjl).1 < 64 + nn →
          (nm >>> ((cls_f[j]'hjl).1 - 64)) &&& 1#64 ≠ 0#64))
    (fun (ci, _, _, _) _ => cls_f.length - ci.toNat)
    ?_ ?_
  · intro Jl hJl; ds_steps
    exact hJl (0#32, 0#64, 0#64, ()) mf
      ⟨rfl, Nat.zero_le _, by simp, by simp, fun _ hj => by simp at hj⟩
  · rintro Jl ⟨ci_l, pm_l, nm_l, ⟨⟩⟩ mc_l ⟨hmc_eq, hci_le, hpm_hi, hnm_hi, hbits_l⟩ ih_l
    subst mc_l; (try clear hc); ds_split
    · have hci_lt : ci_l.toNat < cls_f.length := by bv_omega
      have hci1 : (ci_l + 1#32).toNat = ci_l.toNat + 1 := by bv_omega
      have hmeta_idx : 256 + ((6816#32 + ci_l).setWidth 64).toNat = 256 + 6816 + ci_l.toNat := by
        bv_omega
      have haux_idx : 256 + ((7712#32 + ci_l).setWidth 64).toNat = 256 + 7712 + ci_l.toNat := by
        bv_omega
      have hmeta_len :
          256 + ((6816#32 + ci_l).setWidth 64).toNat < s_f.scratch.scratch_buf.length := by
        rw [hscr_eq, hscrf_len]; omega
      have haux_len :
          256 + ((7712#32 + ci_l).setWidth 64).toNat < s_f.scratch.scratch_buf.length := by
        rw [hscr_eq, hscrf_len]; omega
      have heid_bd := (hcls _ (hsub _ (List.getElem_mem hci_lt))).2.1
      have heid_val : (scr_f[256 + 7712 + ci_l.toNat]?.getD 0#32).toNat =
          (cls_f[ci_l.toNat]'hci_lt).1 :=
        hLaws.cl_aux_eq hKf ci_l.toNat hci_lt
      ds_to_group
      refine wp_join_group (ts := [i64, i64])
        (fun (pm', nm', _) mc' => mc' = mf ∧ pm' >>> np = 0#64 ∧ nm' >>> nn = 0#64 ∧
          ∀ (j : Nat) (_hj : j < ci_l.toNat + 1) (hjl : j < cls_f.length),
            (scr_f[256 + 6816 + j]?.getD 0#32 &&& 0x10000#32) ≠ 0#32 →
            ((cls_f[j]'hjl).1 < np → (pm' >>> (cls_f[j]'hjl).1) &&& 1#64 ≠ 0#64) ∧
            (64 ≤ (cls_f[j]'hjl).1 → (cls_f[j]'hjl).1 < 64 + nn →
              (nm' >>> ((cls_f[j]'hjl).1 - 64)) &&& 1#64 ≠ 0#64))
        ?_ ?_
      · rintro _ ⟨pm', nm', ⟨⟩⟩ mc' ⟨hmc', h1, h2, h4⟩
        subst mc'; ds_steps
        exact ih_l (ci_l + 1#32, pm', nm', ()) mf (by bv_omega)
          ⟨rfl, by omega, h1, h2, by rw [hci1]; exact h4⟩
      · intro Jw hJw
        ds_split
        · have haux_bv : 256 + (7712#32 + ci_l).toNat = 256 + 7712 + ci_l.toNat := by bv_omega
          let eid := s_f.scratch.scratch_buf[256 + (7712#32 + ci_l).toNat]'(by
            rw [hscr_eq, hscrf_len]; omega)
          have heid_n : eid.toNat = (cls_f[ci_l.toNat]'hci_lt).1 := by
            dsimp only [eid]
            rw [list_getElem_congr haux_bv _ (by rw [hscr_eq, hscrf_len]; omega),
              ← Option.getD_some
                (a := s_f.scratch.scratch_buf[256 + 7712 + ci_l.toNat]'_) (b := 0#32),
              ← List.getElem?_eq_getElem (by rw [hscr_eq, hscrf_len]; omega), hscr_eq]
            exact heid_val
          ds_to_group
          refine wp_unroll_group fun _ _ => ?_
          ds_split
          · dsimp only [LeanQbe.T.lift2, LeanQbe.T.Arg.val, Prod.fst] at hc
            have heid_lt64 : eid.toNat < 64 := by dsimp only [eid]; bv_omega
            have heid_np : (cls_f[ci_l.toNat]'hci_lt).1 < np := by
              rw [heid_n] at heid_lt64; rcases heid_bd with h1 | ⟨h1, _⟩ <;> omega
            have heid_mod : (eid.setWidth 64).toNat % 64 = (cls_f[ci_l.toNat]'hci_lt).1 := by
              rw [← heid_n]; bv_omega
            ds_steps
            refine hJw (pm_l ||| (1#64 <<< ((eid.setWidth 64).toNat % 64)), nm_l, ()) mf
              ⟨rfl, ?_, hnm_hi, fun j hj hjl hjbit => ?_⟩
            · rw [heid_mod]; apply BitVec.eq_of_getLsbD_eq; intro b _
              have hb0 := congrArg (·.getLsbD b) hpm_hi
              simp at hb0 ⊢; exact ⟨hb0, by omega⟩
            · rw [heid_mod]
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
              · have ⟨hp0, hn0⟩ := hbits_l j hlt hjl hjbit
                exact ⟨fun hnp_j => bv64_or_bit_pres_other (by omega) (hp0 hnp_j), hn0⟩
              · exact ⟨fun _ => bv64_or_shl_testBit_self pm_l (by omega),
                  fun hge64 _ => absurd heid_np (by omega)⟩
          · dsimp only [LeanQbe.T.lift2, LeanQbe.T.Arg.val, Prod.fst] at hc
            have heid_ge64 : ¬ eid.toNat < 64 := by dsimp only [eid]; bv_omega
            have heid_64 : 64 ≤ (cls_f[ci_l.toNat]'hci_lt).1 := by
              rw [heid_n] at heid_ge64; omega
            have heid_nn : (cls_f[ci_l.toNat]'hci_lt).1 < 64 + nn := by
              rcases heid_bd with h1 | ⟨_, h2⟩ <;> omega
            ds_to_group
            refine wp_unroll_group fun _ _ => ?_
            ds_split
            · have heid_mod : ((eid - 64#32).setWidth 64).toNat % 64 =
                  (cls_f[ci_l.toNat]'hci_lt).1 - 64 := by rw [← heid_n]; bv_omega
              ds_steps
              refine hJw (pm_l, nm_l ||| (1#64 <<< (((eid - 64#32).setWidth 64).toNat % 64)), ())
                mf ⟨rfl, hpm_hi, ?_, fun j hj hjl hjbit => ?_⟩
              · rw [heid_mod]; apply BitVec.eq_of_getLsbD_eq; intro b _
                have hb0 := congrArg (·.getLsbD b) hnm_hi
                simp at hb0 ⊢; exact ⟨hb0, by omega⟩
              · rw [heid_mod]
                rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
                · have ⟨hp0, hn0⟩ := hbits_l j hlt hjl hjbit
                  exact ⟨hp0, fun hge hnn_j => bv64_or_bit_pres_other (by omega) (hn0 hge hnn_j)⟩
                · exact ⟨fun hlt_np => absurd hlt_np (by omega),
                    fun _ _ => bv64_or_shl_testBit_self nm_l (by omega)⟩
            · exfalso
              dsimp only [LeanQbe.T.lift2, LeanQbe.T.Arg.val, Prod.fst] at hc
              have heid_nlt128 : ¬ eid.toNat < 128 := by dsimp only [eid]; bv_omega
              have hlt128 : (cls_f[ci_l.toNat]'hci_lt).1 < 128 := by
                rcases heid_bd with h1 | ⟨_, h2⟩ <;> omega
              rw [← heid_n] at hlt128; exact heid_nlt128 hlt128
        · have hz_bit : (scr_f[256 + 6816 + ci_l.toNat]?.getD 0#32 &&& 0x10000#32) = 0#32 := by
            dsimp only [LeanQbe.T.lift2, LeanQbe.T.Arg.val, Prod.fst] at hc
            have hidx2 : 256 + (6816#32 + ci_l).toNat = 256 + 6816 + ci_l.toNat := by bv_omega
            rw [← hscr_eq, List.getElem?_eq_getElem (by rw [hscr_eq, hscrf_len]; omega),
              Option.getD_some, ← list_getElem_congr hidx2 _ (by rw [hscr_eq, hscrf_len]; omega)]
            exact hc
          ds_steps
          refine hJw (pm_l, nm_l, ()) mf ⟨rfl, hpm_hi, hnm_hi, fun j hj hjl hjbit => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
          · exact hbits_l j hlt hjl hjbit
          · exact absurd hz_bit hjbit
    · have hci_eq : ci_l.toNat = cls_f.length := by bv_omega
      rw [hci_eq] at hbits_l
      have hgate : FullDefGateUnsat s v pm_l nm_l np nn := by
        refine defGateUnsat_of_kitten_core hnp64 hnn64 hcls hsub hcore_u hpm_hi hnm_hi
          fun e he => ?_
        unfold kittenCoreClauses at he; rw [List.mem_filterMap] at he
        obtain ⟨j, hj_r, hj_ite⟩ := he
        have hj_lt : j < cls_f.length := List.mem_range.mp hj_r
        split at hj_ite
        · rename_i hbit
          have he_eq : e = cls_f[j]'hj_lt := by
            change cls_f[j]? = some e at hj_ite
            rw [List.getElem?_eq_getElem hj_lt] at hj_ite
            exact (Option.some.inj hj_ite).symm
          rw [he_eq]; exact hbits_l j hj_lt hj_lt hbit
        · cases hj_ite
      exact hAfter ci_l pm_l nm_l hgate

private theorem def_find_write_masks_wp {Γ : Env} {Q : Post []} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s_c : FullState} {R : Mem 64 → Prop} {scrPtr pm_f nm_f fuel_f : BitVec 64}
    {v np nn : BitVec 32} {exp_e tmk_c scr_f tmp_e : List (BitVec 32)} {mf : Mem 64}
    (hscrp : scrPtr = c.pScratchBuf)
    (hsc : s_c = { s with
      core := { s.core with tmp := tmp_e }
      scratch := { s.scratch with wsort := exp_e, tarjan_mark := tmk_c, scratch_buf := scr_f } })
    (hdw : FullDenseInvW c F0 F_cur s) (h10240 : 10240 ≤ c.scratch_cap)
    (htmk_c : TmkZero s_c) (htl : tmp_e.length = c.max_vars)
    (hwl : exp_e.length = 2 * c.max_vars) (html : tmk_c.length = 2 * c.max_vars)
    (hscrf_len : scr_f.length = c.scratch_cap)
    (hfl_f : fuel_f.toNat ≤ s.core.fuel.toNat)
    (hscrf_256 : ∀ k < 256, scr_f[k]? = s.scratch.scratch_buf[k]?)
    (hgate_f : FullDefGateUnsat s v.toNat pm_f nm_f np.toNat nn.toNat)
    (hmf : (FullMem c { s_c with core := { s_c.core with fuel := fuel_f } } ⋆ R) mf)
    (hQ : ∀ (s' : FullState) (m' : Mem 64),
      have scr' := s'.scratch.scratch_buf
      have pmask :=
        (scr'[128]?.getD 0#32).setWidth 64 ||| ((scr'[129]?.getD 0#32).setWidth 64 <<< 32)
      have nmask :=
        (scr'[130]?.getD 0#32).setWidth 64 ||| ((scr'[131]?.getD 0#32).setWidth 64 <<< 32)
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.vals = s.core.vals →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i < c.scratch_cap, i < 128 ∨ (132 ≤ i ∧ (i < 256 ∨ c.scratch_cap < 10240)) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      ((∀ i ∈ [128, 129, 130, 131], scr'[i]? = s.scratch.scratch_buf[i]?) ∨
        FullDefGateUnsat s v.toNat pmask nmask np.toNat nn.toNat) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X (findDefWriteMasksExpr scrPtr pm_f nm_f) mf := by
  subst hscrp hsc
  have hsc := c.hscr; unfold dimacsBound at hsc
  let s_f : FullState :=
    { s with
      core := { s.core with tmp := tmp_e, fuel := fuel_f }
      scratch := { s.scratch with wsort := exp_e, tarjan_mark := tmk_c, scratch_buf := scr_f } }
  have htmk_f : TmkZero s_f := htmk_c.congr rfl rfl
  let scr_w : List (BitVec 32) :=
    (((scr_f.set 128 (pm_f.setWidth 32)).set 129 ((pm_f >>> 32).setWidth 32)).set
      130 (nm_f.setWidth 32)).set 131 ((nm_f >>> 32).setWidth 32)
  unfold findDefWriteMasksExpr
  refine wp_join_group (ts := [])
    (fun () mw => ∃ scr_out : List (BitVec 32),
      scr_out.length = c.scratch_cap ∧
      (∀ k < 256, (k < 128 ∨ 132 ≤ k) → scr_out[k]? = s.scratch.scratch_buf[k]?) ∧
      ((∀ k ∈ [128, 129, 130, 131], scr_out[k]? = s.scratch.scratch_buf[k]?) ∨
        FullDefGateUnsat s v.toNat
          ((scr_out[128]?.getD 0#32).setWidth 64 ||| ((scr_out[129]?.getD 0#32).setWidth 64 <<< 32))
          ((scr_out[130]?.getD 0#32).setWidth 64 ||| ((scr_out[131]?.getD 0#32).setWidth 64 <<< 32))
          np.toNat nn.toNat) ∧
      (FullMem c { s_f with scratch := { s_f.scratch with scratch_buf := scr_out } } ⋆ R) mw)
    ?_ ?_
  · rintro _ ⟨⟩ mw ⟨scr_out, hsout_len, hsout_256, hsout_res, hmw⟩
    ds_steps
    exact hQ _ mw (fullDenseInvW_with_findDef hdw htl hwl html hsout_len)
      htmk_f rfl rfl rfl rfl hfl_f (def_scr256_spec_ext h10240 hsout_256) hsout_res hmw
  · intro J_end hJ_end
    have hs128 : 512 / 4 < scr_f.length := by omega
    have hs129 : 516 / 4 < scr_f.length := by omega
    have hs130 : 520 / 4 < scr_f.length := by omega
    have hs131 : 524 / 4 < scr_f.length := by omega
    have hpost_w : ∀ m_w,
        (FullMem c { s_f with scratch := { s_f.scratch with scratch_buf := scr_w } } ⋆ R) m_w →
        J_end () m_w := fun m_w hmw => by
      have hscrw_len : scr_w.length = c.scratch_cap := by simp [scr_w, hscrf_len]
      have hpm_rec :
          (scr_w[128]?.getD 0#32).setWidth 64 |||
            ((scr_w[129]?.getD 0#32).setWidth 64 <<< 32) = pm_f := by
        have ha : scr_w[128]? = some (pm_f.setWidth 32) := by
          simp only [scr_w]
          rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
            List.getElem?_set_ne (by decide), List.getElem?_set_self (by omega)]
        have hb : scr_w[129]? = some ((pm_f >>> 32).setWidth 32) := by
          simp only [scr_w]
          rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
            List.getElem?_set_self (by simp; omega)]
        rw [ha, hb, Option.getD_some, Option.getD_some, bv64_mask_split_32]
      have hnm_rec :
          (scr_w[130]?.getD 0#32).setWidth 64 |||
            ((scr_w[131]?.getD 0#32).setWidth 64 <<< 32) = nm_f := by
        have hc' : scr_w[130]? = some (nm_f.setWidth 32) := by
          simp only [scr_w]
          rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by simp; omega)]
        have hd' : scr_w[131]? = some ((nm_f >>> 32).setWidth 32) := by
          simp only [scr_w]; rw [List.getElem?_set_self (by simp; omega)]
        rw [hc', hd', Option.getD_some, Option.getD_some, bv64_mask_split_32]
      refine hJ_end () m_w ⟨scr_w, hscrw_len, fun k hk1 hk2 => ?_, ?_, hmw⟩
      · have hne : k ≠ 128 ∧ k ≠ 129 ∧ k ≠ 130 ∧ k ≠ 131 := by rcases hk2 with h | h <;> omega
        simp only [scr_w]
        rw [List.getElem?_set_ne hne.2.2.2.symm, List.getElem?_set_ne hne.2.2.1.symm,
          List.getElem?_set_ne hne.2.1.symm, List.getElem?_set_ne hne.1.symm]
        exact hscrf_256 k hk1
      · right; rw [hpm_rec, hnm_rec]; exact hgate_f
    ds_to_group
    refine wp_unroll_group fun _ _ => ?_
    ds_split
    · ds_csteps!; exact hpost_w _ (by assumption)
    · ds_split
      · ds_csteps!; exact hpost_w _ (by assumption)
      · ds_steps
        refine hJ_end () mf
          ⟨scr_f, hscrf_len, fun k hk _ => hscrf_256 k hk,
            Or.inl fun k hk => hscrf_256 k (by
              simp at hk; rcases hk with rfl | rfl | rfl | rfl <;> omega),
            hmf⟩

private theorem def_find_kitten_solve_core_m5_wp {Γ : Env}
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    (hLaws : KittenInvLawsM5 KInv)
    (hSolve : ∀ args m Q X, fullKittenSolveSpec KInv args m Q X →
      Γ "full_kitten_solve_m5" [i64, i64] [i64] args m Q X)
    (hCore : ∀ args m Q X, fullKittenCoreSpec KInv args m Q X →
      Γ "full_kitten_core_m5" [i64] [i32] args m Q X)
    (hShrink : ∀ args m Q X, fullKittenShrinkSpec KInv args m Q X →
      Γ "full_kitten_shrink" [i64] [] args m Q X)
    {Q : Post []} {X : XPost} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s_c : FullState} {R : Mem 64 → Prop} {hPtr scrPtr : BitVec 64}
    {v np nn nv_o : BitVec 32} {cls_e : List (Nat × List Nat)}
    {exp_e tmk_c scr_e tmp_e : List (BitVec 32)} {mi : Mem 64}
    (hh : hPtr = c.hdr) (hscrp : scrPtr = c.pScratchBuf)
    (hsc : s_c = { s with
      core := { s.core with tmp := tmp_e }
      scratch := { s.scratch with wsort := exp_e, tarjan_mark := tmk_c, scratch_buf := scr_e } })
    (hdw : FullDenseInvW c F0 F_cur s) (hdw_c : FullDenseInvW c F0 F_cur s_c)
    (_h132 : 132 ≤ c.scratch_cap) (h10240 : 10240 ≤ c.scratch_cap) (htmk_c : TmkZero s_c)
    (hnp64 : np.toNat ≤ 64) (hnn64 : nn.toNat ≤ 64)
    (hnv_ge1 : 1 ≤ nv_o.toNat) (hnv_le128 : nv_o.toNat ≤ 128)
    (hK_e : KInv 128 cls_e true .fresh scr_e)
    (hcls_e : DefClsInv s v.toNat np.toNat nn.toNat nv_o.toNat exp_e cls_e)
    (hscr_e256 : ∀ k < 256, scr_e[k]? = s.scratch.scratch_buf[k]?)
    (hscr_e18 : scr_e[256 + 18]? = some 0#32)
    (hmi : (FullMem c s_c ⋆ R) mi)
    (hQ : ∀ (s' : FullState) (m' : Mem 64),
      have scr' := s'.scratch.scratch_buf
      have pmask :=
        (scr'[128]?.getD 0#32).setWidth 64 ||| ((scr'[129]?.getD 0#32).setWidth 64 <<< 32)
      have nmask :=
        (scr'[130]?.getD 0#32).setWidth 64 ||| ((scr'[131]?.getD 0#32).setWidth 64 <<< 32)
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.vals = s.core.vals →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i < c.scratch_cap, i < 128 ∨ (132 ≤ i ∧ (i < 256 ∨ c.scratch_cap < 10240)) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      ((∀ i ∈ [128, 129, 130, 131], scr'[i]? = s.scratch.scratch_buf[i]?) ∨
        FullDefGateUnsat s v.toNat pmask nmask np.toNat nn.toNat) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X (findDefKittenCoreM5Expr hPtr scrPtr nv_o) mi := by
  subst hh hscrp hsc
  have hsc := c.hscr; unfold dimacsBound at hsc
  have htmpl_e : tmp_e.length = c.max_vars := hdw_c.1.core_ok.tmp_len_arr
  have htmkl_e : tmk_c.length = 2 * c.max_vars := hdw_c.1.scratch_ok.tarjan_mark_len
  have hwsl_e : exp_e.length = 2 * c.max_vars := hdw_c.1.scratch_ok.wsort_len
  have hscrl_e : scr_e.length = c.scratch_cap := hdw_c.1.scratch_ok.scratch_buf_len
  let s_c : FullState :=
    { s with
      core := { s.core with tmp := tmp_e }
      scratch := { s.scratch with wsort := exp_e, tarjan_mark := tmk_c, scratch_buf := scr_e } }
  change (FullMem c s_c ⋆ R) mi at hmi
  have h256_len : 256 < scr_e.length := by omega
  have h262_len : 262 < scr_e.length := by omega
  have h267_len : 267 < scr_e.length := by omega
  have h268_len : 268 < scr_e.length := by omega
  have h269_len : 269 < scr_e.length := by omega
  have h274_len : 274 < scr_e.length := by omega
  have hqnext_idx : 256 + ((416#32 + nv_o - 1#32).setWidth 64).toNat =
      256 + 416 + (nv_o.toNat - 1) := by bv_omega
  have hqnext_len : 256 + ((416#32 + nv_o - 1#32).setWidth 64).toNat < scr_e.length := by omega
  unfold findDefKittenCoreM5Expr
  ds_csteps!
  let scr_k :=
    ((((((scr_e.set 256 nv_o).set 262 nv_o).set 274 0#32).set
      267 (nv_o - 1#32)).set 268 (nv_o - 1#32)).set 269 nv_o).set
      (256 + ((416#32 + nv_o - 1#32).setWidth 64).toNat) 0xFFFFFFFF#32
  have hscr_k_eq : scr_k =
      (((((scr_e.set 256 (BitVec.ofNat 32 nv_o.toNat)).set
        262 (BitVec.ofNat 32 nv_o.toNat)).set
        267 (BitVec.ofNat 32 (nv_o.toNat - 1))).set
        268 (BitVec.ofNat 32 (nv_o.toNat - 1))).set
        269 (BitVec.ofNat 32 nv_o.toNat)).set
        (256 + 416 + (nv_o.toNat - 1)) 0xFFFFFFFF#32 := by
    have hnoop : ((scr_e.set 256 nv_o).set 262 nv_o).set 274 0#32 =
        (scr_e.set 256 nv_o).set 262 nv_o := by
      refine list_set_eq_self_of_getElem? ?_
      rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide)]
      exact hscr_e18
    have hnv_m1 : nv_o - 1#32 = BitVec.ofNat 32 (nv_o.toNat - 1) := by bv_omega
    dsimp only [scr_k]
    rw [hnoop, hqnext_idx, hnv_m1, bv_ofNat_toNat_eq]
  have hK_k : KInv nv_o.toNat cls_e true .fresh scr_k := by
    rw [hscr_k_eq]
    exact hLaws.set_nv_vmtf hK_e hnv_ge1 hnv_le128
      (by rw [hscr_e18]; decide) (fun e he l hl => (hcls_e e he).1 l hl)
  have hscr_k_len : scr_k.length = c.scratch_cap := by simp [scr_k, hscrl_e]
  have hscr_k256 : ∀ k < 256, scr_k[k]? = s.scratch.scratch_buf[k]? := fun k hk => by
    simp only [scr_k]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
    exact hscr_e256 k hk
  have hscr_k18 : scr_k[256 + 18]? = some 0#32 := by
    simp only [scr_k]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by decide),
      List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
      List.getElem?_set_self (by simp; omega)]
  let s_k : FullState := { s_c with scratch := { s_c.scratch with scratch_buf := scr_k } }
  have hdw_k : FullDenseInvW c F0 F_cur s_k :=
    fullDenseInvW_with_findDef hdw htmpl_e hwsl_e htmkl_e hscr_k_len
  ds_steps; c0_call hSolve
  refine ⟨c, s_k, nv_o.toNat, cls_e, true, .fresh, R, rfl, hdw_k.1, h10240, hK_k,
    by assumption, fun st1 fuel1 scr1 m1 hscr1_len hfl1 hscr1_256 hscr1_18 hK1 _ _ _ hm1 => ?_⟩
  let s_1 : FullState :=
    { s_c with
      core := { s_c.core with fuel := fuel1 }
      scratch := { s_c.scratch with scratch_buf := scr1 } }
  have hdw_1 : FullDenseInvW c F0 F_cur s_1 :=
    fullDenseInvW_with_findDef hdw htmpl_e hwsl_e htmkl_e hscr1_len
  have htmk_1 : TmkZero s_1 := htmk_c.congr rfl rfl
  have hscr1_256' : ∀ k < 256, scr1[k]? = s.scratch.scratch_buf[k]? :=
    fun k hk => (hscr1_256 k hk).trans (hscr_k256 k hk)
  ds_split
  · ds_steps
    exact hQ s_1 m1 hdw_1 htmk_1 rfl rfl rfl rfl hfl1
      (def_scr256_spec_ext h10240 fun k hk _ => hscr1_256' k hk)
      (Or.inl fun k hk => hscr1_256' k (by
        simp at hk; rcases hk with rfl | rfl | rfl | rfl <;> omega))
      hm1
  · have hst1_20 : st1 = 20#64 := by bv_omega
    have hK1_ur : KInv nv_o.toNat cls_e true .unsatReady scr1 := by
      simpa [hst1_20, show (s_k.scratch.scratch_buf[274]?.getD 0#32).toNat = 0 by
        dsimp only [s_k]; rw [show (274 : Nat) = 256 + 18 from rfl, hscr_k18]; decide] using hK1
    ds_steps; c0_call hCore
    refine ⟨c, s_1, nv_o.toNat, cls_e, R, rfl, hdw_1.1, h10240, hK1_ur, hm1,
      fun red2 scr2 m2 hscr2_len hscr2_256 hscr2_18 hK2 hcore2_u hm2 => ?_⟩
    let s_2 : FullState :=
      { s_c with
        core := { s_c.core with fuel := fuel1 }
        scratch := { s_c.scratch with scratch_buf := scr2 } }
    have hdw_2 : FullDenseInvW c F0 F_cur s_2 :=
      fullDenseInvW_with_findDef hdw htmpl_e hwsl_e htmkl_e hscr2_len
    have htmk_2 : TmkZero s_2 := htmk_c.congr rfl rfl
    have hscr2_256' : ∀ k < 256, scr2[k]? = s.scratch.scratch_buf[k]? :=
      fun k hk => (hscr2_256 k hk).trans (hscr1_256' k hk)
    have hscr2_18' : scr2[256 + 18]? = some 0#32 := by rw [hscr2_18, hscr1_18, hscr_k18]
    ds_split
    · ds_steps
      exact hQ s_2 m2 hdw_2 htmk_2 rfl rfl rfl rfl hfl1
        (def_scr256_spec_ext h10240 fun k hk _ => hscr2_256' k hk)
        (Or.inl fun k hk => hscr2_256' k (by
          simp at hk; rcases hk with rfl | rfl | rfl | rfl <;> omega))
        hm2
    · -- Loop 1: snapshot 1st-core `(pm1, nm1)` BEFORE `full_kitten_shrink`
      refine def_find_extract_masks_wp hLaws (s_f := s_2) rfl hm2 rfl h10240 hscr2_len hnp64 hnn64
        hcls_e (fun _ h => h) hK2 hcore2_u fun ci1 pm1 nm1 hgate1 => ?_
      let cls_sh := kittenCoreClauses cls_e scr2
      ds_steps; c0_call hShrink
      refine ⟨c, s_2, nv_o.toNat, cls_e, true, .unsatReady, R, rfl, hdw_2.1, h10240, hK2, hm2,
        fun scr3 m3 hscr3_len hscr3_256 hscr3_18 hK3 _ hm3 => ?_⟩
      let s_3 : FullState :=
        { s_c with
          core := { s_c.core with fuel := fuel1 }
          scratch := { s_c.scratch with scratch_buf := scr3 } }
      have hdw_3 : FullDenseInvW c F0 F_cur s_3 :=
        fullDenseInvW_with_findDef hdw htmpl_e hwsl_e htmkl_e hscr3_len
      have hscr3_256' : ∀ k < 256, scr3[k]? = s.scratch.scratch_buf[k]? :=
        fun k hk => (hscr3_256 k hk).trans (hscr2_256' k hk)
      have hscr3_18' : scr3[256 + 18]? = some 0#32 := by rw [hscr3_18, hscr2_18']
      ds_to_group
      refine wp_join_group (ts := [i32, i32, i64, i64])
        (fun (_, _, pm_f, nm_f, _) mf => ∃ (fuel_f : BitVec 64) (scr_f : List (BitVec 32)),
          fuel_f.toNat ≤ s.core.fuel.toNat ∧ scr_f.length = c.scratch_cap ∧
          (∀ k < 256, scr_f[k]? = s.scratch.scratch_buf[k]?) ∧
          FullDefGateUnsat s v.toNat pm_f nm_f np.toNat nn.toNat ∧
          (FullMem c
            { s_c with
              core := { s_c.core with fuel := fuel_f }
              scratch := { s_c.scratch with scratch_buf := scr_f } } ⋆ R) mf)
        ?_ ?_
      · rintro _ ⟨_, _, pm_f, nm_f, ⟨⟩⟩ mf
          ⟨fuel_f, scr_f, hfl_f, hscrf_len, hscrf_256, hgate_f, hmf⟩
        exact def_find_write_masks_wp (s_c := { s_c with
            scratch := { s_c.scratch with scratch_buf := scr_f } })
          rfl rfl hdw h10240 (htmk_c.congr rfl rfl) htmpl_e hwsl_e
          htmkl_e hscrf_len hfl_f hscrf_256 hgate_f hmf hQ
      · intro Jif2 hJif2
        ds_steps; c0_call hSolve
        refine ⟨c, s_3, nv_o.toNat, cls_sh, true, .fresh, R, rfl, hdw_3.1, h10240, hK3, hm3,
          fun st4 fuel4 scr4 m4 hscr4_len hfl4 hscr4_256 _ hK4 _ _ _ hm4 => ?_⟩
        let s_4 : FullState :=
          { s_c with
            core := { s_c.core with fuel := fuel4 }
            scratch := { s_c.scratch with scratch_buf := scr4 } }
        have hdw_4 : FullDenseInvW c F0 F_cur s_4 :=
          fullDenseInvW_with_findDef hdw htmpl_e hwsl_e htmkl_e hscr4_len
        have hscr4_256' : ∀ k < 256, scr4[k]? = s.scratch.scratch_buf[k]? :=
          fun k hk => (hscr4_256 k hk).trans (hscr3_256' k hk)
        ds_split
        · have hst4_20 : st4 = 20#64 := by bv_omega
          have hK4_ur : KInv nv_o.toNat cls_sh true .unsatReady scr4 := by
            simpa [hst4_20, show (s_3.scratch.scratch_buf[274]?.getD 0#32).toNat = 0 by
              dsimp only [s_3]; rw [show (274 : Nat) = 256 + 18 from rfl, hscr3_18']; decide]
              using hK4
          ds_steps; c0_call hCore
          refine ⟨c, s_4, nv_o.toNat, cls_sh, R, rfl, hdw_4.1, h10240, hK4_ur, hm4,
            fun red5 scr5 m5 hscr5_len hscr5_256 _ hK5 hcore5_u hm5 => ?_⟩
          let s_5 : FullState :=
            { s_c with
              core := { s_c.core with fuel := fuel4 }
              scratch := { s_c.scratch with scratch_buf := scr5 } }
          have hscr5_256' : ∀ k < 256, scr5[k]? = s.scratch.scratch_buf[k]? :=
            fun k hk => (hscr5_256 k hk).trans (hscr4_256' k hk)
          refine def_find_extract_masks_wp hLaws (s_f := s_5) rfl hm5 rfl h10240 hscr5_len hnp64
            hnn64 hcls_e (fun _ => kittenCoreClauses_mem) hK5 hcore5_u fun ci2 pm2 nm2 hgate2 => ?_
          ds_to_group
          refine wp_join_group (ts := [i64, i64])
            (fun (pm_u, nm_u, _) mu => mu = m5 ∧
              FullDefGateUnsat s v.toNat pm_u nm_u np.toNat nn.toNat)
            ?_ ?_
          · rintro _ ⟨pm_u, nm_u, ⟨⟩⟩ mu ⟨hmu, hgate_u⟩
            subst mu; ds_steps
            exact hJif2 (ci2, red5, pm_u, nm_u, ()) m5
              ⟨fuel4, scr5, le_trans hfl4 hfl1, hscr5_len, hscr5_256', hgate_u, hm5⟩
          · intro Ju hJu
            ds_split
            · ds_steps; exact hJu (pm2, nm2, ()) m5 ⟨rfl, hgate2⟩
            · ds_split
              · ds_steps; exact hJu (pm2, nm2, ()) m5 ⟨rfl, hgate2⟩
              · ds_steps; exact hJu (pm1, nm1, ()) m5 ⟨rfl, hgate1⟩
        · ds_steps
          exact hJif2 (ci1, red2, pm1, nm1, ()) m4
            ⟨fuel4, scr4, le_trans hfl4 hfl1, hscr4_len, hscr4_256', hgate1, hm4⟩


private theorem def_find_tmk_clear_wp {Γ : Env} {Q : Post []} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {nv_o : BitVec 32} {exp_e tmk_e scr_e tmp_e : List (BitVec 32)}
    {pWsort pTmk : BitVec 64} {mc : Mem 64} {cont : Expr Val Cont []}
    (hpws : pWsort = c.pWsort) (hptmk : pTmk = c.pTarjanMark)
    (hnv_le_cv : nv_o.toNat ≤ s.core.cur_vars) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hwsl_e : exp_e.length = 2 * c.max_vars) (htmkl_e : tmk_e.length = 2 * c.max_vars)
    (hexp_bnd : ∀ i < nv_o.toNat, (exp_e[i]?.getD 0#32).toNat < s.core.cur_vars)
    (hexp_rev : ∀ v < s.core.cur_vars, tmk_e[v]?.getD 0#32 ≠ 0#32 →
      ∃ i < nv_o.toNat, (exp_e[i]?.getD 0#32).toNat = v)
    (hmc : (FullMem c
      { s with
        core := { s.core with tmp := tmp_e }
        scratch :=
          { s.scratch with wsort := exp_e, tarjan_mark := tmk_e, scratch_buf := scr_e } } ⋆ R)
      mc)
    (hcont : ∀ tmk_c mi, tmk_c.length = 2 * c.max_vars →
      (∀ u < s.core.cur_vars, tmk_c[u]?.getD 0#32 = 0#32) →
      (FullMem c
        { s with
          core := { s.core with tmp := tmp_e }
          scratch :=
            { s.scratch with wsort := exp_e, tarjan_mark := tmk_c, scratch_buf := scr_e } } ⋆ R)
        mi →
      wp Γ Q X cont mi) :
    wp Γ Q X
      (Expr.group (sig := [[i32]])
        (fun Js =>
          Blocks.cons
            (fun (p : Tup Val [i32]) =>
              Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var p.fst, Arg.var nv_o, ()))
                fun p_2 =>
                Expr.jnz (Arg.var p_2.fst)
                  (Expr.let_ (Op.mk (.zext 32 64) (Arg.var p.fst, ())) fun p_3 =>
                    Expr.let_ (Op.mk (.mul i64) (Arg.var p_3.fst, Arg.imm 4, ())) fun p_4 =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var p_4.fst, ())) fun p_5 =>
                    Expr.load i32 (Arg.var p_5.fst) fun ld =>
                    Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p_6 =>
                    Expr.let_ (Op.mk (.mul i64) (Arg.var p_6.fst, Arg.imm 4, ())) fun p_7 =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var pTmk, Arg.var p_7.fst, ())) fun p_8 =>
                    Expr.store (t := i32) (Arg.imm 0) (Arg.var p_8.fst)
                      (Expr.let_ (Op.mk (.add i32) (Arg.var p.fst, Arg.imm 1, ())) fun p =>
                        Expr.jump Js.fst (Arg.var p.fst, ())))
                  cont)
            Blocks.nil)
        (fun Js => Expr.jump Js.fst (Arg.imm 0, ())))
      mc := by
  subst hpws hptmk
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  refine wp_loop_inv (ts := [i32])
    (fun (ci, _) mi =>
      ci.toNat ≤ nv_o.toNat ∧
      ∃ tmk_c : List (BitVec 32), tmk_c.length = 2 * c.max_vars ∧
      (∀ u < s.core.cur_vars, tmk_c[u]?.getD 0#32 ≠ 0#32 →
        ∃ k, ci.toNat ≤ k ∧ k < nv_o.toNat ∧ (exp_e[k]?.getD 0#32).toNat = u) ∧
      (FullMem c
        { s with
          core := { s.core with tmp := tmp_e }
          scratch :=
            { s.scratch with wsort := exp_e, tarjan_mark := tmk_c, scratch_buf := scr_e } } ⋆ R)
        mi)
    (fun (ci, _) _ => nv_o.toNat - ci.toNat)
    ?_ ?_
  · intro Jc hJc; ds_steps
    refine hJc (0#32, ()) mc ⟨Nat.zero_le _, tmk_e, htmkl_e, fun u hu hne => ?_, hmc⟩
    obtain ⟨k, hk, heq⟩ := hexp_rev u hu hne
    exact ⟨k, Nat.zero_le _, hk, heq⟩
  · rintro Jc ⟨ci, ⟨⟩⟩ mi ⟨hci_le, tmk_c, htmkc_len, htmkc_inv, hmi⟩ ihc
    (try clear hc); ds_split
    · have hci_lt : ci.toNat < nv_o.toNat := by bv_omega
      have hci_ws : (ci.setWidth 64).toNat < exp_e.length := by rw [hwsl_e]; bv_omega
      have hci_exp_lt : ci.toNat < exp_e.length := by omega
      have hexp_ci_lt : (exp_e[ci.toNat]'hci_exp_lt).toNat < s.core.cur_vars := by
        have h1 := hexp_bnd ci.toNat hci_lt
        rwa [List.getElem?_eq_getElem hci_exp_lt, Option.getD_some] at h1
      let lv_ci := exp_e[(ci.setWidth 64).toNat]'hci_ws
      have hlv_eq_raw : lv_ci = exp_e[ci.toNat]'hci_exp_lt :=
        list_getElem_congr (by bv_omega : (ci.setWidth 64).toNat = ci.toNat)
          hci_ws hci_exp_lt
      have hv_tmk : (lv_ci.setWidth 64).toNat < tmk_c.length := by
        rw [bv_c0_zext32_64, htmkc_len, hlv_eq_raw]; omega
      have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by bv_omega
      ds_csteps!
      have hlv_eq : (exp_e[ci.toNat]?.getD 0#32).toNat = lv_ci.toNat := by
        rw [List.getElem?_eq_getElem hci_exp_lt, Option.getD_some, hlv_eq_raw]
      have hbv_idx : (BitVec.setWidth 64 lv_ci).toNat = lv_ci.toNat := by bv_omega
      have htmkc_inv' := def_tmk_clear_step hci_lt hlv_eq
        (by rw [htmkc_len, hlv_eq_raw]; omega) htmkc_inv
      exact ihc (ci + 1#32, ()) _ (by bv_omega)
        ⟨by omega, tmk_c.set lv_ci.toNat 0#32, by simp [htmkc_len],
         by rw [hci1]; simpa [hbv_idx] using htmkc_inv', by assumption⟩
    · have hci_eq : ci.toNat = nv_o.toNat := by bv_omega
      rw [hci_eq] at htmkc_inv
      ds_steps
      exact hcont tmk_c mi htmkc_len (def_tmk_clear_done htmkc_inv) hmi

private def findDefKLoopExpr
    (hPtr arPtr valsPtr tmkPtr expPtr tmpPtr : BitVec 64)
    (wAst szAst exc nv_i : BitVec 32) (ab_i : Bool)
    (kAfter : Tup Val [i32, .bool, .bool, i32, i32] → Expr Val Cont []) :
    Expr Val Cont [] :=
  Expr.group (sig := [[i32, .bool, .bool, i32, i32]])
    (fun _ => Blocks.cons kAfter Blocks.nil)
    fun Js =>
    Expr.group (sig := [[i32, i32, i32]])
      (fun Js_1 =>
        Blocks.cons
          (fun p =>
            Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl)
                (Arg.var p.snd.snd.fst, Arg.var szAst, ())) fun p_1 =>
            Expr.jnz (Arg.var p_1.fst)
              (Expr.let_ (Op.mk (.zext 32 64) (Arg.var wAst, ())) fun p_2 =>
               Expr.let_ (Op.mk (.add i64) (Arg.var p_2.fst, Arg.imm 3, ())) fun p_3 =>
               Expr.let_ (Op.mk (.zext 32 64) (Arg.var p.snd.snd.fst, ())) fun p_4 =>
               Expr.let_ (Op.mk (.add i64) (Arg.var p_3.fst, Arg.var p_4.fst, ())) fun p_5 =>
               Expr.let_ (Op.mk (.mul i64) (Arg.var p_5.fst, Arg.imm 4, ())) fun p_6 =>
               Expr.let_ (Op.mk (.add i64) (Arg.var arPtr, Arg.var p_6.fst, ())) fun p_7 =>
               Expr.load i32 (Arg.var p_7.fst) fun ld =>
               Expr.group (sig := [[i32, .bool, .bool, i32]])
                 (fun _ => Blocks.cons (fun p_8 =>
                   Expr.let_ (Op.mk (.add i32) (Arg.var p.snd.snd.fst, Arg.imm 1, ())) fun p =>
                   Expr.jump Js_1.fst
                     (Arg.var p_8.fst, Arg.var p_8.snd.snd.snd.fst, Arg.var p.fst, ()))
                   Blocks.nil)
                 fun Js_2 =>
                 Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var ld, Arg.var exc, ()))
                   fun p_8 =>
                 Expr.jnz (Arg.var p_8.fst)
                   (Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p_9 =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var valsPtr, Arg.var p_9.fst, ())) fun p_10 =>
                    Expr.load i8 (Arg.var p_10.fst) fun ld_1 =>
                    Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) fun p_11 =>
                    Expr.let_ (Op.mk (.sext 8 32) (Arg.var ld_1, ())) fun p_12 =>
                    Expr.let_ (Op.mk (.sext 8 32) (Arg.var p_11.fst, ())) fun p_13 =>
                    Expr.let_ (Op.mk (.cmp .sgt i32 .bool rfl)
                        (Arg.var p_12.fst, Arg.var p_13.fst, ())) fun p_14 =>
                    Expr.jnz (Arg.var p_14.fst)
                      (Expr.jump Js.fst
                        (Arg.var p.fst, Arg.var ab_i, Arg.imm true, Arg.var p.snd.fst,
                         Arg.var p.snd.snd.fst, ()))
                      (Expr.group (sig := [[i32, .bool, i32]])
                        (fun _ => Blocks.cons (fun p =>
                          Expr.jump Js_2.fst
                            (Arg.var p.fst, Arg.var p.snd.fst, Arg.imm false,
                             Arg.var p.snd.snd.fst, ()))
                          Blocks.nil)
                        fun Js_3 =>
                        Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) fun p_15 =>
                        Expr.let_ (Op.mk (.sext 8 32) (Arg.var ld_1, ())) fun p_16 =>
                        Expr.let_ (Op.mk (.sext 8 32) (Arg.var p_15.fst, ())) fun p_17 =>
                        Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl)
                            (Arg.var p_16.fst, Arg.var p_17.fst, ())) fun p_18 =>
                        Expr.jnz (Arg.var p_18.fst)
                          (Expr.let_ (Op.mk (.lshr i32) (Arg.var ld, Arg.imm 1, ())) fun p_19 =>
                           Expr.group (sig := [[i32, .bool]])
                             (fun _ => Blocks.cons (fun p_20 =>
                               Expr.let_ (Op.mk (.zext 32 64) (Arg.var p.snd.fst, ())) fun p_21 =>
                               Expr.let_ (Op.mk (.add i64) (Arg.var hPtr, Arg.imm 776, ()))
                                 fun p_22 =>
                               Expr.load i64 (Arg.var p_22.fst) fun ld_2 =>
                               Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                   (Arg.var p_21.fst, Arg.var ld_2, ())) fun p_23 =>
                               Expr.jnz (Arg.var p_23.fst)
                                 (Expr.let_ (Op.mk (.zext 32 64) (Arg.var p.snd.fst, ()))
                                    fun p_24 =>
                                  Expr.let_ (Op.mk (.mul i64) (Arg.var p_24.fst, Arg.imm 4, ()))
                                    fun p_25 =>
                                  Expr.let_ (Op.mk (.add i64)
                                      (Arg.var tmpPtr, Arg.var p_25.fst, ()))
                                    fun p_26 =>
                                  Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_19.fst, ())) fun p_27 =>
                                  Expr.let_ (Op.mk (.mul i64) (Arg.var p_27.fst, Arg.imm 4, ()))
                                    fun p_28 =>
                                  Expr.let_ (Op.mk (.add i64)
                                      (Arg.var tmkPtr, Arg.var p_28.fst, ()))
                                    fun p_29 =>
                                  Expr.load i32 (Arg.var p_29.fst) fun ld_3 =>
                                  Expr.let_ (Op.mk (.sub i32) (Arg.var ld_3, Arg.imm 1, ()))
                                    fun p_30 =>
                                  Expr.let_ (Op.mk (.shl i32) (Arg.var p_30.fst, Arg.imm 1, ()))
                                    fun p_31 =>
                                  Expr.let_ (Op.mk (.and i32) (Arg.var ld, Arg.imm 1, ()))
                                    fun p_32 =>
                                  Expr.let_ (Op.mk (.or i32)
                                      (Arg.var p_31.fst, Arg.var p_32.fst, ()))
                                    fun p_33 =>
                                  Expr.store (t := i32) (Arg.var p_33.fst) (Arg.var p_26.fst)
                                    (Expr.let_ (Op.mk (.add i32)
                                        (Arg.var p.snd.fst, Arg.imm 1, ())) fun p =>
                                     Expr.jump Js_3.fst
                                       (Arg.var p_20.fst, Arg.var p_20.snd.fst, Arg.var p.fst, ())))
                                 (Expr.jump Js.fst
                                   (Arg.var p_20.fst, Arg.imm true, Arg.imm false,
                                    Arg.var p.snd.fst, Arg.var p.snd.snd.fst, ())))
                               Blocks.nil)
                             fun Js_4 =>
                             Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_19.fst, ())) fun p_20 =>
                             Expr.let_ (Op.mk (.mul i64) (Arg.var p_20.fst, Arg.imm 4, ()))
                               fun p_21 =>
                             Expr.let_ (Op.mk (.add i64) (Arg.var tmkPtr, Arg.var p_21.fst, ()))
                               fun p_22 =>
                             Expr.load i32 (Arg.var p_22.fst) fun ld =>
                             Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl) (Arg.var ld, Arg.imm 0, ()))
                               fun p_23 =>
                             Expr.jnz (Arg.var p_23.fst)
                               (Expr.let_ (Op.mk (.cmp .uge i32 .bool rfl)
                                   (Arg.var p.fst, Arg.imm 128, ())) fun p_24 =>
                                Expr.jnz (Arg.var p_24.fst)
                                  (Expr.jump Js.fst
                                    (Arg.var p.fst, Arg.imm true, Arg.imm false,
                                     Arg.var p.snd.fst, Arg.var p.snd.snd.fst, ()))
                                  (Expr.let_ (Op.mk (.zext 32 64) (Arg.var p.fst, ())) fun p_25 =>
                                   Expr.let_ (Op.mk (.mul i64) (Arg.var p_25.fst, Arg.imm 4, ()))
                                     fun p_26 =>
                                   Expr.let_ (Op.mk (.add i64)
                                       (Arg.var expPtr, Arg.var p_26.fst, ())) fun p_27 =>
                                   Expr.store (t := i32) (Arg.var p_19.fst) (Arg.var p_27.fst)
                                     (Expr.let_ (Op.mk (.add i32) (Arg.var p.fst, Arg.imm 1, ()))
                                        fun p =>
                                      Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_19.fst, ()))
                                        fun p_28 =>
                                      Expr.let_ (Op.mk (.mul i64) (Arg.var p_28.fst, Arg.imm 4, ()))
                                        fun p_29 =>
                                      Expr.let_ (Op.mk (.add i64)
                                          (Arg.var tmkPtr, Arg.var p_29.fst, ())) fun p_30 =>
                                      Expr.store (t := i32) (Arg.var p.fst) (Arg.var p_30.fst)
                                        (Expr.jump Js_4.fst
                                          (Arg.var p.fst, Arg.var ab_i, ())))))
                               (Expr.jump Js_4.fst (Arg.var p.fst, Arg.var ab_i, ())))
                          (Expr.jump Js_3.fst
                            (Arg.var p.fst, Arg.var ab_i, Arg.var p.snd.fst, ()))))
                   (Expr.jump Js_2.fst
                     (Arg.var p.fst, Arg.var ab_i, Arg.imm false, Arg.var p.snd.fst, ())))
              (Expr.jump Js.fst
                (Arg.var p.fst, Arg.var ab_i, Arg.imm false, Arg.var p.snd.fst,
                 Arg.var p.snd.snd.fst, ())))
          Blocks.nil)
      fun Js => Expr.jump Js.fst (Arg.var nv_i, Arg.imm 0, Arg.imm 0, ())

private theorem def_find_k_loop_wp {Γ : Env} {Q : Post []} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop}
    {hPtr arPtr valsPtr tmkPtr expPtr tmpPtr : BitVec 64}
    {wAst w szAst sz_cl exc nv_i : BitVec 32} {ab_i : Bool}
    {exp_i tmk_i scr_i tmp_i : List (BitVec 32)}
    {mi : Mem 64} {kAfter : Tup Val [i32, .bool, .bool, i32, i32] → Expr Val Cont []}
    (hhPtr : hPtr = c.hdr) (harPtr : arPtr = c.pArena) (hvalsPtr : valsPtr = c.pVals)
    (htmkPtr : tmkPtr = c.pTarjanMark) (hexpPtr : expPtr = c.pWsort) (htmpPtr : tmpPtr = c.pTmp)
    (hwAst : wAst = w) (hszAst : szAst = sz_cl) (hab_i : ab_i = false)
    (hdw : FullDenseInvW c F0 F_cur s)
    (hdw_i : FullDenseInvW c F0 F_cur (defFindState s exp_i tmk_i scr_i tmp_i))
    (hexp_i : DefExpInv s.core.cur_vars nv_i.toNat exp_i tmk_i)
    (href : w.toNat ∈ fullArenaClauseRefs s) (hgarb : fullArenaClauseGarb s w.toNat = false)
    (hsz_cl : sz_cl = s.core.arena[w.toNat + 2]'(by
      have hwf0 := hdw.2.1.arena.refs_wf w.toNat href
      have := hwf0.1; have := hwf0.2.2.1
      have := hdw.1.core_ok.arena_len_le; have := hdw.1.core_ok.arena_len_arr; omega))
    (hmi : (FullMem c (defFindState s exp_i tmk_i scr_i tmp_i) ⋆ R) mi)
    (hAfter : ∀ nv_k ab_k sat_k csz_k k_k mk,
      FindDefKBrkInv c F0 F_cur s R scr_i exp_i nv_i w exc nv_k ab_k sat_k csz_k mk →
      wp Γ Q X (kAfter (nv_k, ab_k, sat_k, csz_k, k_k, ())) mk) :
    wp Γ Q X
      (findDefKLoopExpr hPtr arPtr valsPtr tmkPtr expPtr tmpPtr wAst szAst exc nv_i ab_i kAfter)
      mi := by
  rw [hhPtr, harPtr, hvalsPtr, htmkPtr, hexpPtr, htmpPtr, hwAst, hszAst, hab_i]
  have hmv := c.hmaxv; have harc := c.harena; unfold dimacsBound at hmv harc
  have hw := hdw.2.1
  have hcl := hdw.1.core_ok; have hsl := hdw.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have harl := hcl.arena_len_arr; have harle := hcl.arena_len_le
  have hvl := hcl.vals_len
  have htmpli : tmp_i.length = c.max_vars := hdw_i.1.core_ok.tmp_len_arr
  have htmkl_i : tmk_i.length = 2 * c.max_vars := hdw_i.1.scratch_ok.tarjan_mark_len
  have hwsl_i : exp_i.length = 2 * c.max_vars := hdw_i.1.scratch_ok.wsort_len
  have hscrli : scr_i.length = c.scratch_cap := hdw_i.1.scratch_ok.scratch_buf_len
  have hwf := hw.arena.refs_wf w.toNat href
  have hsz_core : sz_cl.toNat = fullArenaClauseSizeCore s.core w.toNat := by
    unfold fullArenaClauseSizeCore
    rw [hsz_cl, List.getElem?_eq_getElem (l := s.core.arena) (by omega), Option.getD_some]
  have hcl_lits_len : (fullArenaClauseLits s w.toNat).length = sz_cl.toNat := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    rw [List.length_map, List.length_take, List.length_drop, ← hsz_core]
    exact Nat.min_eq_left (by omega)
  refine wp_loop_break_group
    (brkTs := [i32, .bool, .bool, i32, i32]) (lpTs := [i32, i32, i32])
    (fun (nv_k, ab_k, sat_k, csz_k, _k_k, _) mk =>
      FindDefKBrkInv c F0 F_cur s R scr_i exp_i nv_i w exc nv_k ab_k sat_k csz_k mk)
    (fun rem (nv_k, csz_k, k_k, _) mk =>
      rem = sz_cl.toNat - k_k.toNat ∧
      FindDefKLpInv c F0 F_cur s R scr_i exp_i nv_i w exc sz_cl nv_k csz_k k_k mk)
    ?_ ?_ ?_
  · rintro _ ⟨nv_k, ab_k, sat_k, csz_k, k_k, ⟨⟩⟩ mk hBrk
    exact hAfter nv_k ab_k sat_k csz_k k_k mk hBrk
  · rintro Bk Lk _ ⟨nv_k, csz_k, k_k, ⟨⟩⟩ mk hBk hLk
      ⟨rfl, hk_le, hnv_ik, hcsz_le_k, hcsz_cv, exp_k, tmk_k, tmp_k,
       hdw_k, hexp_k, hexp_mono, hlts_k, hnd_k, hback_k, hcov_k, hmk⟩
    let sk := defFindState s exp_k tmk_k scr_i tmp_k
    have htmplk : tmp_k.length = c.max_vars := hdw_k.1.core_ok.tmp_len_arr
    have htmklk : tmk_k.length = 2 * c.max_vars := hdw_k.1.scratch_ok.tarjan_mark_len
    have hwslk : exp_k.length = 2 * c.max_vars := hdw_k.1.scratch_ok.wsort_len
    ds_split; rotate_left 1
    · have hk_eq : k_k.toNat = sz_cl.toNat := by bv_omega
      have hcsz_128 : csz_k.toNat ≤ 128 := by
        have hlen_map : ((tmp_k.take csz_k.toNat).map (fun x => x.toNat / 2)).length =
            csz_k.toNat := by
          rw [List.length_map, List.length_take]; exact Nat.min_eq_left (by omega)
        rw [← hlen_map]
        refine FullSweepFwdHelpers.nodup_length_le_of_lt hnd_k fun u hu => ?_
        rw [List.mem_map] at hu
        obtain ⟨x, hx, rfl⟩ := hu
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
        have hj' : j < csz_k.toNat := by rw [List.length_take] at hj; omega
        have hx_lt := hlts_k j hj'
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hx_lt
        rw [List.getElem_take]
        have h128_e := hexp_k.1
        omega
      ds_steps
      refine hBk (nv_k, false, false, csz_k, k_k, ()) mk
        ⟨hnv_ik, fun h => Bool.noConfusion h, exp_k, tmk_k, tmp_k, hdw_k, hexp_k, hexp_mono,
         fun _ _ => ⟨hcsz_128, by omega, hlts_k, fun l hl => ?_⟩, hmk⟩
      rw [List.mem_filter] at hl
      obtain ⟨hl_cl, hne_exc⟩ := hl
      have hne' : l ≠ exc.toNat := by simpa using hne_exc
      unfold fullArenaClauseLits at hl_cl
      obtain ⟨mi, hmi_sz, rfl⟩ := (mem_fullArenaClauseLitsCore_iff (by omega)).mp hl_cl
      rw [← hsz_core] at hmi_sz
      have hl_ar : (s.core.arena[w.toNat + 3 + mi]?.getD 0#32).toNat =
          (s.core.arena[w.toNat + 3 + mi]'(by omega)).toNat := by
        rw [List.getElem?_eq_getElem (l := s.core.arena) (by omega), Option.getD_some]
      have hcov_mi := hcov_k mi (by omega)
      rw [hl_ar] at hcov_mi
      exact (hcov_mi hne').2
    · have hk_lt : k_k.toNat < sz_cl.toNat := by bv_omega
      have hk1 : (k_k + 1#32).toNat = k_k.toNat + 1 := by bv_omega
      have har_idx_n : (w.setWidth 64 + 3#64 + k_k.setWidth 64).toNat =
          w.toNat + 3 + k_k.toNat := by
        rw [BitVec.toNat_add, BitVec.toNat_add, bv_c0_zext32_64, bv_c0_zext32_64,
          show (3#64 : BitVec 64).toNat = 3 from rfl,
          Nat.mod_eq_of_lt (by have := hwf.1; omega),
          Nat.mod_eq_of_lt (by have := hwf.1; omega)]
      let l_bv := s.core.arena[w.toNat + 3 + k_k.toNat]'(by omega)
      have har_w3k_sk : (w.setWidth 64 + 3#64 + k_k.setWidth 64).toNat < sk.core.arena.length := by
        rw [har_idx_n]; change w.toNat + 3 + k_k.toNat < s.core.arena.length; omega
      have hl_bv_sk :
          sk.core.arena[(w.setWidth 64 + 3#64 + k_k.setWidth 64).toNat]'har_w3k_sk = l_bv := by
        change s.core.arena[_]'_ = s.core.arena[w.toNat + 3 + k_k.toNat]'_
        exact list_getElem_congr har_idx_n _ _
      have hl_lt : l_bv.toNat < 2 * s.core.cur_vars := by
        apply hw.arena.lits_lt w.toNat href hgarb
        exact (mem_fullArenaClauseLitsCore_iff (by omega)).mpr
          ⟨k_k.toNat, by rw [← hsz_core]; exact hk_lt, rfl⟩
      have hl_val_len_sk :
          ((sk.core.arena[(w.setWidth 64 + 3#64 + k_k.setWidth 64).toNat]'har_w3k_sk).setWidth
            64).toNat < sk.core.vals.length := by
        rw [hl_bv_sk]; change (l_bv.setWidth 64).toNat < s.core.vals.length; bv_omega
      ds_to_group
      refine wp_join_group (ts := [i32, .bool, .bool, i32])
        (fun (nv_n, _ab_n, _sat_n, csz_n, _) mn =>
          k_k.toNat + 1 ≤ sz_cl.toNat ∧
          FindDefKLpInv c F0 F_cur s R scr_i exp_i nv_i w exc sz_cl nv_n csz_n (k_k + 1#32) mn)
        ?_ ?_
      · rintro _ ⟨nv_n, _ab_n, _sat_n, csz_n, ⟨⟩⟩ mn
          ⟨hk1_sz, hk1_sz2, hnvn, hcszn, hcszn_cv, exp_n, tmk_n, tmp_n, hdwn, hexpn, hexpmn,
           hltsn, hndn, hbackn, hcovn, hmn⟩
        ds_steps
        exact hLk (sz_cl.toNat - (k_k + 1#32).toNat) (nv_n, csz_n, k_k + 1#32, ()) mn (by omega)
          ⟨by omega, hk1_sz2, hnvn, hcszn, hcszn_cv, exp_n, tmk_n, tmp_n, hdwn, hexpn, hexpmn,
           hltsn, hndn, hbackn, hcovn, hmn⟩
      · intro J_kn hJ_kn
        have hkeep_kn :
            (l_bv.toNat = exc.toNat ∨ s.core.vals[l_bv.toNat]?.getD 0#8 = 0xFF#8) →
              k_k.toNat + 1 ≤ sz_cl.toNat ∧
              FindDefKLpInv c F0 F_cur s R scr_i exp_i nv_i w exc sz_cl nv_k csz_k (k_k + 1#32)
                mk := fun hle_n =>
          ⟨by omega, by omega, hnv_ik, by omega, hcsz_cv, exp_k, tmk_k, tmp_k, hdw_k, hexp_k,
            hexp_mono, hlts_k, hnd_k,
            fun j hj => let ⟨mi, hmi, hme⟩ := hback_k j hj; ⟨mi, by omega, hme⟩,
            fun mi hmi hne => by
              rw [hk1] at hmi
              rcases Nat.lt_succ_iff_lt_or_eq.mp hmi with hlt | rfl
              · exact hcov_k mi hlt hne
              · have hm_eq : (s.core.arena[w.toNat + 3 + k_k.toNat]?.getD 0#32).toNat =
                      l_bv.toNat := by
                  rw [List.getElem?_eq_getElem (l := s.core.arena) (by omega), Option.getD_some]
                rw [hm_eq] at hne ⊢
                rcases hle_n with heq_exc | hf
                · exact absurd heq_exc hne
                · exact ⟨by rw [hf]; decide, Or.inl ⟨hl_lt, hf⟩⟩,
            hmk⟩
        (try clear hc)
        (try dsimp only [LeanQbe.T.lift2, LeanQbe.T.Arg.val, Prod.fst])
        ds_split
        · have hne_exc : l_bv.toNat ≠ exc.toNat := fun h => by
            have hc' := hc
            rw [getElem_eq_getElem?_getD s.core.arena (d := 0#32),
              show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
              show (w.toNat + 3 + k_k.toNat) % 2 ^ 64 = w.toNat + 3 + k_k.toNat from
                Nat.mod_eq_of_lt (by have := hwf.1; omega),
              List.getElem?_eq_getElem (l := s.core.arena)
                (by change w.toNat + 3 + k_k.toNat < s.core.arena.length; omega),
              Option.getD_some] at hc'
            exact hc' (BitVec.eq_of_toNat_eq h)
          have hdom_l := hw.vals_domain l_bv.toNat hl_lt
          (try clear hc); ds_split
          · ds_steps
            exact hBk (nv_k, false, true, csz_k, k_k, ()) mk
              ⟨hnv_ik, fun h => Bool.noConfusion h, exp_k, tmk_k, tmp_k, hdw_k, hexp_k,
               hexp_mono, fun _ h => Bool.noConfusion h, hmk⟩
          · have hnot_pos : s.core.vals[l_bv.toNat]?.getD 0#8 ≠ 1#8 := fun h1 => by
              have hc' := hc
              (try dsimp only [defFindState] at hc')
              rw [getElem_eq_getElem?_getD s.core.vals (d := 0#8),
                getElem_eq_getElem?_getD s.core.arena (d := 0#32),
                show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                show (w.toNat + 3 + k_k.toNat) % 2 ^ 64 = w.toNat + 3 + k_k.toNat from
                  Nat.mod_eq_of_lt (by have := hwf.1; omega),
                List.getElem?_eq_getElem (l := s.core.arena)
                  (by change w.toNat + 3 + k_k.toNat < s.core.arena.length; omega),
                Option.getD_some] at hc'
              change (0#32).slt (BitVec.signExtend 32 (s.core.vals[l_bv.toNat]?.getD 0#8)) =
                false at hc'
              rw [h1] at hc'; exact absurd hc' (by decide)
            (try clear hc); ds_to_group; refine wp_unroll_group fun _ _ => ?_; ds_split
            · have hl_zero : s.core.vals[l_bv.toNat]?.getD 0#8 = 0#8 := by
                have hc' := hc
                (try dsimp only [defFindState] at hc')
                rw [getElem_eq_getElem?_getD s.core.vals (d := 0#8),
                  getElem_eq_getElem?_getD s.core.arena (d := 0#32),
                  show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                  show (w.toNat + 3 + k_k.toNat) % 2 ^ 64 = w.toNat + 3 + k_k.toNat from
                    Nat.mod_eq_of_lt (by have := hwf.1; omega),
                  List.getElem?_eq_getElem (l := s.core.arena)
                    (by change w.toNat + 3 + k_k.toNat < s.core.arena.length; omega),
                  Option.getD_some] at hc'
                change BitVec.signExtend 32 (s.core.vals[l_bv.toNat]?.getD 0#8) = 0#32 at hc'
                rcases hdom_l with h0 | h1 | hf
                · exact h0
                · exact absurd h1 hnot_pos
                · rw [hf] at hc'; exact absurd hc' (by decide)
              have hlv_eq : (l_bv >>> 1#32).toNat = l_bv.toNat / 2 := bv32_shr1_toNat l_bv
              have hlv_lt : (l_bv >>> 1#32).toNat < s.core.cur_vars := by omega
              ds_to_group
              refine wp_join_group (ts := [i32, .bool])
                (fun (nv_p, _ab_p, _) mp =>
                  nv_k.toNat ≤ nv_p.toNat ∧ 1 ≤ nv_p.toNat ∧
                  ∃ (exp_p tmk_p : List (BitVec 32)),
                    let sp := defFindState s exp_p tmk_p scr_i tmp_k
                    exp_p.length = 2 * c.max_vars ∧ tmk_p.length = 2 * c.max_vars ∧
                    DefExpInv s.core.cur_vars nv_p.toNat exp_p tmk_p ∧
                    (∀ i < nv_k.toNat, exp_p[i]? = exp_k[i]?) ∧
                    tmk_p[(l_bv >>> 1#32).toNat]?.getD 0#32 ≠ 0#32 ∧
                    (FullMem c sp ⋆ R) mp)
                ?_ ?_
              · rintro _ ⟨nv_p, _ab_p, ⟨⟩⟩ mp
                  ⟨hnv_p_ge, _hnv_1, exp_p, tmk_p, hexpp_l, htmkp_l, hexpp, hexpp_mono,
                   hnz_lv, hmp⟩
                (try clear hc); ds_split
                · have hcsz_lt : csz_k.toNat < s.core.cur_vars := by bv_omega
                  have hcsz1 : (csz_k + 1#32).toNat = csz_k.toNat + 1 := by bv_omega
                  have hcsz_tmp : (csz_k.setWidth 64).toNat < tmp_k.length := by
                    rw [htmplk, bv_c0_zext32_64]; omega
                  let idx_lv := ((tmk_p[(l_bv >>> 1#32).toNat]?.getD 0#32) - 1#32).toNat
                  obtain ⟨hidx_lv, hexp_lv⟩ := defExpInv_get hexpp hlv_lt hnz_lv
                  let lit_loc :=
                    ((tmk_p[(l_bv >>> 1#32).toNat]?.getD 0#32 - 1#32) <<< 1#32) |||
                      (l_bv &&& 1#32)
                  have hlit_nat : lit_loc.toNat = 2 * idx_lv + l_bv.toNat % 2 := by
                    dsimp only [lit_loc]
                    rw [show (tmk_p[(l_bv >>> 1#32).toNat]?.getD 0#32 - 1#32) <<< 1#32 =
                      (tmk_p[(l_bv >>> 1#32).toNat]?.getD 0#32 - 1#32) <<< (1 : Nat) from rfl]
                    have h128 := hexpp.1
                    exact bv32_lit_shl_or _ l_bv
                      (Nat.lt_trans (Nat.lt_of_lt_of_le hidx_lv h128) (by decide))
                  have hgl_eq : fullDefGlobalLit exp_p lit_loc.toNat = l_bv.toNat := by
                    unfold fullDefGlobalLit
                    rw [hlit_nat, show (2 * idx_lv + l_bv.toNat % 2) / 2 = idx_lv by omega,
                      show (2 * idx_lv + l_bv.toNat % 2) % 2 = l_bv.toNat % 2 by omega, hexp_lv]
                    omega
                  have hl_bv_goal :
                      (defFindState s exp_k tmk_k scr_i tmp_k).core.arena[(BitVec.setWidth 64 w +
                        3 + BitVec.setWidth 64 k_k).toNat]'har_w3k_sk = l_bv := hl_bv_sk
                  rw [hl_bv_goal]
                  clear har_w3k_sk hl_bv_sk hl_val_len_sk hl_bv_goal
                  have hlv_tmk_s :
                      (BitVec.setWidth 64 (l_bv >>> (OfNat.ofNat 1 : Nat))).toNat <
                        tmk_p.length := by
                    rw [show (OfNat.ofNat 1 : Nat) = (1#32).toNat from rfl]
                    change (BitVec.setWidth 64 (l_bv >>> 1#32)).toNat < tmk_p.length
                    rw [bv_c0_zext32_64, htmkp_l]; omega
                  dsimp only [defFindState] at hmp
                  ds_steps_soft
                  simp only [LeanQbe.T.lift2, LeanQbe.T.Arg.val]
                  c0_hstep
                  (try dsimp only [LeanQbe.T.lift2, LeanQbe.T.Arg.val, Prod.fst] at hm)
                  ds_steps
                  let tmp_n := tmp_k.set csz_k.toNat lit_loc
                  have hdw_n : FullDenseInvW c F0 F_cur (defFindState s exp_p tmk_p scr_i tmp_n) :=
                    fullDenseInvW_defFindState hdw (by simp [tmp_n, htmplk]) hexpp_l htmkp_l hscrli
                  have htake_n : (tmp_n.take (csz_k + 1#32).toNat) =
                      tmp_k.take csz_k.toNat ++ [lit_loc] := by
                    rw [hcsz1, show tmp_n = tmp_k.set csz_k.toNat lit_loc from rfl]
                    apply List.ext_getElem
                    · simp [List.length_take, htmplk]; omega
                    · intro j hj1 _
                      have hj : j < csz_k.toNat + 1 := by simp [List.length_take] at hj1; omega
                      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
                      · rw [List.getElem_take, List.getElem_set_ne (by omega),
                          List.getElem_append_left (by simp [List.length_take, htmplk]; omega),
                          List.getElem_take]
                      · have h1 :
                            ((tmp_k.set csz_k.toNat lit_loc).take (csz_k.toNat + 1))[
                              csz_k.toNat]'(by simp [List.length_take, htmplk]; omega) =
                              lit_loc := by
                          rw [List.getElem_take]
                          exact List.getElem_set_self (by simp [htmplk]; omega)
                        have hmin : (tmp_k.take csz_k.toNat).length = csz_k.toNat := by
                          simp [List.length_take, htmplk]; omega
                        have h2 :
                            (tmp_k.take csz_k.toNat ++ [lit_loc])[csz_k.toNat]'(by simp [hmin]) =
                              lit_loc := by
                          rw [List.getElem_append_right (by omega)]
                          simp [hmin]
                        exact h1.trans h2.symm
                  have hlit_div2 : lit_loc.toNat / 2 = idx_lv := by rw [hlit_nat]; omega
                  have hnd_n :
                      ((tmp_n.take (csz_k + 1#32).toNat).map (fun x => x.toNat / 2)).Nodup := by
                    have htake_map :
                        (tmp_n.take (csz_k + 1#32).toNat).map (fun x => x.toNat / 2) =
                        (tmp_k.take csz_k.toNat).map (fun x => x.toNat / 2) ++ [idx_lv] := by
                      rw [htake_n, List.map_append, List.map_cons, List.map_nil, hlit_div2]
                    have hidx_notin :
                        idx_lv ∉ (tmp_k.take csz_k.toNat).map (fun x => x.toNat / 2) := by
                      intro hmem
                      rw [List.mem_map] at hmem
                      obtain ⟨x, hx, hxd⟩ := hmem
                      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
                      have hj_c : j < csz_k.toNat := by simp at hj; omega
                      obtain ⟨mi, hmi_k, hmi_eq⟩ := hback_k j hj_c
                      rw [List.getElem_take] at hxd
                      rw [List.getElem?_eq_getElem (l := tmp_k) (i := j) (by omega),
                        Option.getD_some] at hmi_eq
                      have hj_lt_k := hlts_k j hj_c
                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hj_lt_k
                      have hdiv_lt : (tmp_k[j]'(by omega)).toNat / 2 < nv_k.toNat := by omega
                      have hexp_eq : exp_p[idx_lv]?.getD 0#32 = exp_k[idx_lv]?.getD 0#32 := by
                        rw [← hxd, hexpp_mono _ hdiv_lt]
                      have hl_div :
                          l_bv.toNat / 2 =
                            (s.core.arena[w.toNat + 3 + mi]?.getD 0#32).toNat / 2 := by
                        rw [← hlv_eq, ← hexp_lv, hexp_eq, ← hxd, hmi_eq]
                      have hnd_w := hdw.2.2.2.1 w.toNat href hgarb
                      have hnd_mi := List.pairwise_iff_getElem.mp hnd_w mi k_k.toNat
                        (by simp [fullArenaClauseLits, fullArenaClauseLitsCore, ← hsz_core]; omega)
                        (by simp [fullArenaClauseLits, fullArenaClauseLitsCore, ← hsz_core]; omega)
                        hmi_k
                      simp only [fullArenaClauseLits, fullArenaClauseLitsCore, List.getElem_map,
                        List.getElem_take, List.getElem_drop] at hnd_mi
                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hl_div
                      exact absurd hl_div.symm hnd_mi
                    rw [htake_map, List.nodup_append]
                    exact ⟨hnd_k, by simp, fun _ ha _ hb => by
                      rw [List.mem_singleton.mp hb]; rintro rfl; exact hidx_notin ha⟩
                  refine (show (csz_k + 1#32 : BitVec 32) = csz_k + 1 from rfl) ▸
                    hJ_kn (nv_p, _ab_p, false, csz_k + 1#32, ()) _
                    ⟨by omega, by omega, Nat.le_trans hnv_ik hnv_p_ge, by omega, by omega,
                     exp_p, tmk_p, tmp_n, hdw_n, hexpp,
                     fun j hj => (hexpp_mono j (by omega)).trans (hexp_mono j hj),
                     fun j hj => ?_, hnd_n, fun j hj => ?_, fun mi hmi hne' => ?_, by
                      have hm' := hm
                      (try dsimp only [defFindState] at hm')
                      have hcsz_64 : (BitVec.setWidth 64 csz_k).toNat = csz_k.toNat := by
                        rw [bv_c0_zext32_64]
                      have hsh_64 :
                          (BitVec.setWidth 64 (l_bv >>> (OfNat.ofNat 1 : Nat))).toNat =
                            (l_bv >>> 1#32).toNat := by
                        rw [bv_c0_zext32_64]; rfl
                      have htmk_get : ∀ hpf,
                          tmk_p[(BitVec.setWidth 64
                            (l_bv >>> (OfNat.ofNat 1 : Nat))).toNat]'hpf =
                            tmk_p[(l_bv >>> 1#32).toNat]?.getD 0#32 := fun hpf => by
                        have hlen : (l_bv >>> 1#32).toNat < tmk_p.length := by rwa [← hsh_64]
                        rw [List.getElem?_eq_getElem hlen, Option.getD_some]
                        exact list_getElem_congr hsh_64 _ _
                      simp only [hcsz_64, htmk_get] at hm'
                      have hm_1 : (1 : BitVec 32) = 1#32 := rfl
                      have hm_shl :
                          (tmk_p[(l_bv >>> 1#32).toNat]?.getD 0#32 - 1#32) <<<
                            (OfNat.ofNat 1 : Nat) =
                            (tmk_p[(l_bv >>> 1#32).toNat]?.getD 0#32 - 1#32) <<< 1#32 := rfl
                      rw [hm_1, hm_shl] at hm'
                      exact hm'⟩
                  · rw [hcsz1] at hj; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
                    · dsimp only [tmp_n]; rw [List.getElem?_set_ne (by omega)]
                      exact Nat.lt_of_lt_of_le (hlts_k j hlt) (by omega)
                    · dsimp only [tmp_n]; rw [List.getElem?_set_self (by
                        rw [htmplk]; omega), Option.getD_some]; omega
                  · rw [hcsz1] at hj; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
                    · obtain ⟨mi, hmi_k, hmi_eq⟩ := hback_k j hlt
                      refine ⟨mi, by omega, ?_⟩
                      dsimp only [tmp_n]; rw [List.getElem?_set_ne (by omega)]
                      have hj_lt := hlts_k j hlt
                      have hj_div : (tmp_k[j]?.getD 0#32).toNat / 2 < nv_k.toNat := by omega
                      rw [hexpp_mono _ (by omega)]; exact hmi_eq
                    · refine ⟨k_k.toNat, by omega, ?_⟩
                      dsimp only [tmp_n]; rw [List.getElem?_set_self (by
                          rw [htmplk]; omega), Option.getD_some, hlit_div2, hexp_lv, hlv_eq,
                        List.getElem?_eq_getElem (by omega), Option.getD_some]
                  · rw [hk1] at hmi
                    rcases Nat.lt_succ_iff_lt_or_eq.mp hmi with hlt | rfl
                    · refine ⟨(hcov_k mi hlt hne').1, ?_⟩
                      rcases (hcov_k mi hlt hne').2 with hf | hmap
                      · exact Or.inl hf
                      · right; rw [htake_n, List.map_append]; apply List.mem_append_left
                        rw [List.mem_map] at hmap ⊢
                        obtain ⟨x, hx, hxeq⟩ := hmap
                        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
                        have hj_c : j < csz_k.toNat := by simp at hj; omega
                        have hx_lt := hlts_k j hj_c
                        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hx_lt
                        refine ⟨(tmp_k.take csz_k.toNat)[j], List.getElem_mem _, ?_⟩
                        rw [List.getElem_take] at hxeq ⊢
                        unfold fullDefGlobalLit at hxeq ⊢
                        rw [hexpp_mono _ (by omega)]; exact hxeq
                    · have hm_eq : (s.core.arena[w.toNat + 3 + k_k.toNat]?.getD 0#32).toNat =
                            l_bv.toNat := by
                        rw [List.getElem?_eq_getElem (l := s.core.arena) (by omega),
                          Option.getD_some]
                      refine ⟨by rw [hm_eq]; exact hnot_pos, ?_⟩
                      right; rw [hm_eq, htake_n, List.map_append]
                      exact List.mem_append_right _ (by simp [hgl_eq])
                · have hdw_p : FullDenseInvW c F0 F_cur (defFindState s exp_p tmk_p scr_i tmp_k) :=
                    fullDenseInvW_defFindState hdw htmplk hexpp_l htmkp_l hscrli
                  ds_steps
                  exact hBk (nv_p, true, false, csz_k, k_k, ()) mp
                    ⟨Nat.le_trans hnv_ik hnv_p_ge, fun _ => rfl, exp_p, tmk_p, tmp_k, hdw_p,
                     hexpp, fun j hj => (hexpp_mono j (by omega)).trans (hexp_mono j hj),
                     fun h => Bool.noConfusion h, hmp⟩
              · intro Jp hJp
                have hlv_tmk : ((l_bv >>> 1#32).setWidth 64).toNat < tmk_k.length := by
                  rw [htmklk, bv_c0_zext32_64]; omega
                have hlv_tmk_sk :
                    (((sk.core.arena[(w.setWidth 64 + 3#64 +
                      k_k.setWidth 64).toNat]'har_w3k_sk >>> 1#32).setWidth 64).toNat) <
                      tmk_k.length := by
                  rw [hl_bv_sk]; exact hlv_tmk
                (try clear hc); ds_split
                · have htz : tmk_k[(l_bv >>> 1#32).toNat]?.getD 0#32 = 0#32 := by
                    have hc' := hc
                    rw [getElem_eq_getElem?_getD tmk_k (d := 0#32),
                      getElem_eq_getElem?_getD s.core.arena (d := 0#32),
                      show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                      show (w.toNat + 3 + k_k.toNat) % 2 ^ 64 = w.toNat + 3 + k_k.toNat from
                        Nat.mod_eq_of_lt (by have := hwf.1; omega),
                      List.getElem?_eq_getElem (l := s.core.arena)
                        (by change w.toNat + 3 + k_k.toNat < s.core.arena.length; omega),
                      Option.getD_some, ← hlv_eq] at hc'
                    exact hc'
                  (try clear hc); ds_split
                  · ds_steps
                    exact hBk (nv_k, true, false, csz_k, k_k, ()) mk
                      ⟨hnv_ik, fun _ => rfl, exp_k, tmk_k, tmp_k, hdw_k, hexp_k, hexp_mono,
                       fun h => Bool.noConfusion h, hmk⟩
                  · have hnv128 : nv_k.toNat < 128 := by bv_omega
                    have hnv1 : (nv_k + 1#32).toNat = nv_k.toNat + 1 := by bv_omega
                    have hcv_ex := defExpInv_le_cv hexp_k
                    obtain ⟨_hnv_cv, hexp_p, hexp_mono_p⟩ := defExpInv_push hexp_k hnv128 hlv_lt
                      htz (by rw [hwslk]; omega) (by rw [htmklk]; omega)
                    have hmk' := hmk
                    dsimp only [defFindState] at hmk'
                    have hl_bv_goal :
                        (defFindState s exp_k tmk_k scr_i tmp_k).core.arena[(BitVec.setWidth 64 w +
                          3 + BitVec.setWidth 64 k_k).toNat]'har_w3k_sk = l_bv := hl_bv_sk
                    rw [hl_bv_goal]
                    clear hlv_tmk_sk har_w3k_sk hl_bv_sk hl_val_len_sk hl_bv_goal
                    have hlv_tmk_s :
                        (BitVec.setWidth 64 (l_bv >>> (OfNat.ofNat 1 : Nat))).toNat <
                          tmk_k.length := by
                      rw [show (OfNat.ofNat 1 : Nat) = (1#32).toNat from rfl]
                      change (BitVec.setWidth 64 (l_bv >>> 1#32)).toNat < tmk_k.length
                      rw [bv_c0_zext32_64, htmklk]; omega
                    ds_steps
                    (try dsimp only [LeanQbe.T.lift2, LeanQbe.T.Arg.val, Prod.fst] at hm)
                    have hnz_p :
                        (tmk_k.set (l_bv >>> 1#32).toNat (nv_k + 1#32))[(l_bv >>> 1#32).toNat]?.getD
                          0#32 ≠ 0#32 := by
                      rw [List.getElem?_set_self (by rw [htmklk]; omega), Option.getD_some]
                      intro h; have := congrArg BitVec.toNat h; simp [hnv1] at this
                    refine hJp (nv_k + 1#32, false, ()) _
                      ⟨by omega, by omega, exp_k.set nv_k.toNat (l_bv >>> 1#32),
                       tmk_k.set (l_bv >>> 1#32).toNat (nv_k + 1#32), by simp [hwslk],
                       by simp [htmklk],
                       by rw [hnv1]; simpa [show BitVec.ofNat 32 (nv_k.toNat + 1) = nv_k + 1#32
                         from by bv_omega] using hexp_p,
                       hexp_mono_p, hnz_p, by
                        have hm' := hm
                        (try dsimp only [defFindState] at hm')
                        have hnv_64 : (BitVec.setWidth 64 nv_k).toNat = nv_k.toNat := by
                          rw [bv_c0_zext32_64]
                        have hsh_64 :
                            (BitVec.setWidth 64 (l_bv >>> (OfNat.ofNat 1 : Nat))).toNat =
                              (l_bv >>> 1#32).toNat := by
                          rw [bv_c0_zext32_64]; rfl
                        simp only [hnv_64, hsh_64] at hm'
                        have hm_sh : l_bv >>> (OfNat.ofNat 1 : Nat) = l_bv >>> 1#32 := rfl
                        rw [hm_sh, show (nv_k + 1 : BitVec 32) = nv_k + 1#32 from rfl] at hm'
                        exact hm'⟩
                · have hne_t : tmk_k[(l_bv >>> 1#32).toNat]?.getD 0#32 ≠ 0#32 := by
                    have hc' := hc
                    rw [getElem_eq_getElem?_getD tmk_k (d := 0#32),
                      getElem_eq_getElem?_getD s.core.arena (d := 0#32),
                      show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                      show (w.toNat + 3 + k_k.toNat) % 2 ^ 64 = w.toNat + 3 + k_k.toNat from
                        Nat.mod_eq_of_lt (by have := hwf.1; omega),
                      List.getElem?_eq_getElem (l := s.core.arena)
                        (by change w.toNat + 3 + k_k.toNat < s.core.arena.length; omega),
                      Option.getD_some, ← hlv_eq] at hc'
                    exact hc'
                  have hk_lv := (defExpInv_get hexp_k hlv_lt hne_t).1
                  ds_steps
                  exact hJp (nv_k, false, ()) mk
                    ⟨le_refl _, by omega, exp_k, tmk_k, hwslk, htmklk, hexp_k, fun _ _ => rfl,
                     hne_t, hmk⟩
            · have hfals : s.core.vals[l_bv.toNat]?.getD 0#8 = 0xFF#8 := by
                have hne0 : s.core.vals[l_bv.toNat]?.getD 0#8 ≠ 0#8 := fun h0 => by
                  have hc' := hc
                  (try dsimp only [defFindState] at hc')
                  rw [getElem_eq_getElem?_getD s.core.vals (d := 0#8),
                    getElem_eq_getElem?_getD s.core.arena (d := 0#32),
                    show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                    show (w.toNat + 3 + k_k.toNat) % 2 ^ 64 = w.toNat + 3 + k_k.toNat from
                      Nat.mod_eq_of_lt (by have := hwf.1; omega),
                    List.getElem?_eq_getElem (l := s.core.arena)
                      (by change w.toNat + 3 + k_k.toNat < s.core.arena.length; omega),
                    Option.getD_some] at hc'
                  change ¬BitVec.signExtend 32 (s.core.vals[l_bv.toNat]?.getD 0#8) =
                    BitVec.signExtend 32 (BitVec.setWidth 8 0) at hc'
                  rw [h0] at hc'; exact absurd rfl hc'
                exact (hdom_l.elim (absurd · hne0) (·.elim (absurd · hnot_pos) id))
              ds_steps
              exact hJ_kn (nv_k, false, false, csz_k, ()) mk (hkeep_kn (Or.inr hfals))
        · have heq_exc : l_bv.toNat = exc.toNat := by
            have hc' := hc
            rw [getElem_eq_getElem?_getD s.core.arena (d := 0#32),
              show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
              show (w.toNat + 3 + k_k.toNat) % 2 ^ 64 = w.toNat + 3 + k_k.toNat from
                Nat.mod_eq_of_lt (by have := hwf.1; omega),
              List.getElem?_eq_getElem (l := s.core.arena)
                (by change w.toNat + 3 + k_k.toNat < s.core.arena.length; omega),
              Option.getD_some] at hc'
            exact congrArg BitVec.toNat hc'
          ds_steps
          exact hJ_kn (nv_k, false, false, csz_k, ()) mk (hkeep_kn (Or.inl heq_exc))
  · intro _Bk _Lk _ hLk; ds_steps
    exact hLk sz_cl.toNat (nv_i, 0#32, 0#32, ()) mi
      ⟨rfl, Nat.zero_le _, le_refl _, Nat.zero_le _, Nat.zero_le _, exp_i, tmk_i, tmp_i, hdw_i,
       hexp_i, fun _ _ => rfl, fun _ hj => by simp at hj, by simp, fun _ hj => by simp at hj,
       fun _ hlt => by simp at hlt, hmi⟩


/-- **`full_find_definition_m5`**: M5 drop-in replacement for `full_find_definition` with VMTF
queue repair and 1st-core snapshot before `full_kitten_shrink`, proving
canonical `FullDefSweep.fullFindDefinitionSpec`. -/
theorem full_find_definition_m5_wp (Γ : Env)
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    (hLaws : KittenInvLawsM5 KInv)
    (hInit : ∀ args m Q X, fullKittenInitSpec KInv args m Q X →
      Γ "full_kitten_init" [i64, i32, i32] [] args m Q X)
    (hAddCl : ∀ args m Q X, fullKittenAddClauseSpec KInv args m Q X →
      Γ "full_kitten_add_clause_m5" [i64, i32, i64, i32] [.bool] args m Q X)
    (hSolve : ∀ args m Q X, fullKittenSolveSpec KInv args m Q X →
      Γ "full_kitten_solve_m5" [i64, i64] [i64] args m Q X)
    (hCore : ∀ args m Q X, fullKittenCoreSpec KInv args m Q X →
      Γ "full_kitten_core_m5" [i64] [i32] args m Q X)
    (hShrink : ∀ args m Q X, fullKittenShrinkSpec KInv args m Q X →
      Γ "full_kitten_shrink" [i64] [] args m Q X) :
    ∀ args m Q X, fullFindDefinitionSpec args m Q X →
      Func.wp Γ full_find_definition_m5_body args m Q X := by
  rintro ⟨h, v, np, nn, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hdw, h132, htmk0, hv_lt, hnp64, hnn64, hpos, hneg, hm, hQ⟩
  have hmv := c.hmaxv; have hsc := c.hscr; have harc := c.harena
  unfold dimacsBound at hmv hsc harc
  have hcl := hdw.1.core_ok; have hsl := hdw.1.scratch_ok; have hw := hdw.2.1
  have hcv_le := hcl.cur_vars_le; have hscrl := hsl.scratch_buf_len
  have harl := hcl.arena_len_arr; have harle := hcl.arena_len_le
  have hvl := hcl.vals_len; have htmkl := hsl.tarjan_mark_len
  have hwsl := hsl.wsort_len; have htmpl := hcl.tmp_len_arr
  unfold Func.wp full_find_definition_m5_body
  ds_steps
  ds_split
  · -- `scratch_cap < 10240`: early return
    ds_steps
    exact hQ s m hdw htmk0 rfl rfl rfl rfl (le_refl _) (fun _ _ _ => rfl)
      (Or.inl fun _ _ => rfl) hm
  ds_split
  · -- `np == 0`: early return
    ds_steps
    exact hQ s m hdw htmk0 rfl rfl rfl rfl (le_refl _) (fun _ _ _ => rfl)
      (Or.inl fun _ _ => rfl) hm
  ds_split
  · -- `nn == 0`: early return
    ds_steps
    exact hQ s m hdw htmk0 rfl rfl rfl rfl (le_refl _) (fun _ _ _ => rfl)
      (Or.inl fun _ _ => rfl) hm
  ds_split
  · -- `np + nn < 3`: early return
    ds_steps
    exact hQ s m hdw htmk0 rfl rfl rfl rfl (le_refl _) (fun _ _ _ => rfl)
      (Or.inl fun _ _ => rfl) hm
  have h10240 : 10240 ≤ c.scratch_cap := by bv_omega
  have hnpnn3 : 3 ≤ np.toNat + nn.toNat := by bv_omega
  have hpl_n : (v <<< 1#32).toNat = 2 * v.toNat := by
    rw [show (v <<< 1#32 : BitVec 32) = v <<< (1 : Nat) from rfl,
      FullDefSweepTactics.bv32_shl1_nat]
    omega
  have hnl_n : ((v <<< 1#32) ||| 1#32).toNat = 2 * v.toNat + 1 := by
    simpa [show (1#32 : BitVec 32).toNat = 1 from rfl] using
      FullSweepFwdHelpers.bv32_shl1_or_pol v 1#32 (by omega) (by decide)
  -- Call `full_kitten_init(h, 128, 1)`
  ds_steps; c0_call hInit
  refine ⟨c, s, R, rfl, hdw.1, h10240, by decide, by decide, hm, fun scr_i m_i hsci_len
    hsci_256 hsci_18 hK_init hm_i => ?_⟩
  let s_init : FullState := { s with scratch := { s.scratch with scratch_buf := scr_i } }
  have hdw_init : FullDenseInvW c F0 F_cur s_init :=
    fullDenseInvW_with_findDef hdw htmpl hwsl htmkl hsci_len
  -- Outer loop: `while (side < 2 && !abort_def && trivial_side == 0xFFFFFFFF)`
  have htmk_init : TmkZero s_init := htmk0.congr rfl rfl
  ds_to_group
  refine wp_loop_inv (ts := [i32, .bool, i32, i32])
    (fun (nv, abort_def, ts, side, _) mo =>
      FindDefOuterInv KInv c F0 F_cur s R v np nn nv abort_def ts side mo)
    (fun (_, _, _, side, _) _ => 2 - side.toNat)
    ?_ ?_
  · intro J_o hJ_o; ds_steps
    refine hJ_o (0#32, false, 0xFFFFFFFF#32, 0#32, ()) m_i
      ⟨Nat.zero_le _, [], s.scratch.wsort, s.scratch.tarjan_mark, scr_i, s.core.tmp,
       hdw_init, hsci_256, hsci_18, hK_init, defExpInv_zero htmk_init, Or.inl rfl,
       fun _ hx => by simp at hx, fun h => Bool.noConfusion h, hm_i⟩
  · rintro J_o ⟨nv_o, abort_o, ts_o, side_o, ⟨⟩⟩ mo
      ⟨hside_le, cls_o, exp_o, tmk_o, scr_o, tmp_o, hdw_o, hscr_o256, hscr_o18, hK_o,
       hexp_o, hts_o, hcls_o, hab_ts_o, hmo⟩ ih_o
    try clear hc
    have htmpl_o : tmp_o.length = c.max_vars := hdw_o.1.core_ok.tmp_len_arr
    have htmkl_o : tmk_o.length = 2 * c.max_vars := hdw_o.1.scratch_ok.tarjan_mark_len
    have hwsl_o : exp_o.length = 2 * c.max_vars := hdw_o.1.scratch_ok.wsort_len
    have hscrl_o : scr_o.length = c.scratch_cap := hdw_o.1.scratch_ok.scratch_buf_len
    ds_to_group
    refine wp_join_group (ts := [])
      (fun () mc => FindDefOuterInv KInv c F0 F_cur s R v np nn nv_o abort_o ts_o side_o mc)
      ?_ ?_
    · -- Post-outer-loop exit: clear `tmk`, handle `trivial_side`, `abort || nv == 0`, kitten core
      rintro _ ⟨⟩ mc ⟨_, cls_e, exp_e, tmk_e, scr_e, tmp_e, hdw_e, hscr_e256, hscr_e18,
        hK_e, hexp_e, hts_e, hcls_e, hab_ts_e, hmc⟩
      let s_e : FullState :=
        { s with
          core := { s.core with tmp := tmp_e }
          scratch := { s.scratch with wsort := exp_e, tarjan_mark := tmk_e, scratch_buf := scr_e } }
      have htmpl_e : tmp_e.length = c.max_vars := hdw_e.1.core_ok.tmp_len_arr
      have htmkl_e : tmk_e.length = 2 * c.max_vars := hdw_e.1.scratch_ok.tarjan_mark_len
      have hwsl_e : exp_e.length = 2 * c.max_vars := hdw_e.1.scratch_ok.wsort_len
      have hscrl_e : scr_e.length = c.scratch_cap := hdw_e.1.scratch_ok.scratch_buf_len
      have hnv_le_cv := defExpInv_le_cv hexp_e
      have hnv_le128 := hexp_e.1
      ds_to_group
      -- Clear `tarjan_mark` at `[exp_e[0 ..< nv_o)]`
      refine def_find_tmk_clear_wp rfl rfl hnv_le_cv hcv_le hwsl_e htmkl_e
        (fun i hi => (hexp_e.2.1 i hi).1) hexp_e.2.2 hmc fun tmk_c mi htmkc_len htz_c hmi => ?_
      let s_c : FullState :=
        { s_e with scratch := { s_e.scratch with tarjan_mark := tmk_c } }
      have hdw_c : FullDenseInvW c F0 F_cur s_c :=
        fullDenseInvW_with_findDef hdw htmpl_e hwsl_e htmkc_len hscrl_e
      have htmk_c : TmkZero s_c := htz_c
      ds_split
      · -- `trivial_side != 0xFFFFFFFF`: compute `(pm, nm)`, write `scr[128..131]`, return
        have hts_ne : ts_o ≠ 0xFFFFFFFF#32 := by
          intro h; simp [h] at hc
        try clear hc
        ds_to_group
        refine wp_join_group (ts := [i64])
          (fun (pm, _) mp => mp = mi ∧
            pm = if ts_o.toNat < 64 then 1#64 <<< ts_o.toNat else 0#64)
          ?_ ?_
        · rintro _ ⟨pm, ⟨⟩⟩ mp ⟨hmp, hpm_eq⟩; subst mp
          ds_to_group
          refine wp_join_group (ts := [i64])
            (fun (nm, _) mn => mn = mi ∧
              nm = if 64 ≤ ts_o.toNat then 1#64 <<< (ts_o.toNat - 64) else 0#64)
            ?_ ?_
          · rintro _ ⟨nm, ⟨⟩⟩ mn ⟨hmn, hnm_eq⟩; subst mn
            have hs128 : 512 / 4 < scr_e.length := by omega
            have hs129 : 516 / 4 < scr_e.length := by omega
            have hs130 : 520 / 4 < scr_e.length := by omega
            have hs131 : 524 / 4 < scr_e.length := by omega
            ds_csteps!
            let scr_f : List (BitVec 32) :=
              (((scr_e.set 128 (pm.setWidth 32)).set 129 ((pm >>> 32).setWidth 32)).set
                130 (nm.setWidth 32)).set 131 ((nm >>> 32).setWidth 32)
            have hscr_f_len : scr_f.length = c.scratch_cap := by simp [scr_f, hscrl_e]
            have hdw_f : FullDenseInvW c F0 F_cur
                { s_c with scratch := { s_c.scratch with scratch_buf := scr_f } } :=
              fullDenseInvW_with_findDef hdw htmpl_e hwsl_e htmkc_len hscr_f_len
            have hpm_rec :
                (scr_f[128]?.getD 0#32).setWidth 64 |||
                  ((scr_f[129]?.getD 0#32).setWidth 64 <<< 32) = pm := by
              have ha : scr_f[128]? = some (pm.setWidth 32) := by
                simp only [scr_f]
                rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
                  List.getElem?_set_ne (by decide), List.getElem?_set_self (by omega)]
              have hb : scr_f[129]? = some ((pm >>> 32).setWidth 32) := by
                simp only [scr_f]
                rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
                  List.getElem?_set_self (by simp; omega)]
              rw [ha, hb, Option.getD_some, Option.getD_some, bv64_mask_split_32]
            have hnm_rec :
                (scr_f[130]?.getD 0#32).setWidth 64 |||
                  ((scr_f[131]?.getD 0#32).setWidth 64 <<< 32) = nm := by
              have hc' : scr_f[130]? = some (nm.setWidth 32) := by
                simp only [scr_f]
                rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by simp; omega)]
              have hd' : scr_f[131]? = some ((nm >>> 32).setWidth 32) := by
                simp only [scr_f]
                rw [List.getElem?_set_self (by simp; omega)]
              rw [hc', hd', Option.getD_some, Option.getD_some, bv64_mask_split_32]
            refine hQ _ _ hdw_f htmk_c rfl rfl rfl rfl (le_refl _)
              (def_scr256_spec_ext h10240 fun k hk hk2 => by
                have hne : k ≠ 128 ∧ k ≠ 129 ∧ k ≠ 130 ∧ k ≠ 131 := by
                  rcases hk2 with h | h <;> omega
                simp only [scr_f]
                rw [List.getElem?_set_ne hne.2.2.2.symm, List.getElem?_set_ne hne.2.2.1.symm,
                  List.getElem?_set_ne hne.2.1.symm, List.getElem?_set_ne hne.1.symm]
                exact hscr_e256 k hk)
              ?_ (by assumption)
            right; rw [hpm_rec, hnm_rec, hpm_eq, hnm_eq]
            exact defGateUnsat_of_trivial hnp64 hnn64 hts_e hts_ne
          · intro Jn hJn; ds_split
            · have hge64 : 64 ≤ ts_o.toNat := by bv_omega
              have hsub64 : ((ts_o - 64#32).setWidth 64).toNat % 64 = ts_o.toNat - 64 := by
                rcases hts_e with h | ⟨hbd, _⟩
                · exact absurd h hts_ne
                · bv_omega
              ds_steps
              refine hJn (1#64 <<< (((ts_o - 64#32).setWidth 64).toNat % 64), ()) mi
                ⟨rfl, by rw [hsub64, ite_eq_left hge64]⟩
            · have hlt64 : ts_o.toNat < 64 := by bv_omega
              ds_steps
              exact hJn (0#64, ()) mi ⟨rfl, (ite_eq_right (by omega : ¬ 64 ≤ ts_o.toNat)).symm⟩
        · intro Jp hJp; ds_split
          · have hlt64 : ts_o.toNat < 64 := by bv_omega
            have hmod64 : (ts_o.setWidth 64).toNat % 64 = ts_o.toNat := by bv_omega
            ds_steps
            refine hJp (1#64 <<< ((ts_o.setWidth 64).toNat % 64), ()) mi
              ⟨rfl, by rw [hmod64, ite_eq_left hlt64]⟩
          · have hge64 : 64 ≤ ts_o.toNat := by bv_omega
            ds_steps
            exact hJp (0#64, ()) mi ⟨rfl, (ite_eq_right (by omega : ¬ ts_o.toNat < 64)).symm⟩
      · -- `trivial_side == 0xFFFFFFFF`
        (try clear hc); ds_split
        · -- `abort_def = true`: return (`scr[128..131]` untouched)
          ds_steps
          exact hQ s_c mi hdw_c htmk_c rfl rfl rfl rfl (le_refl _)
            (def_scr256_spec_ext h10240 fun k hk _ => hscr_e256 k hk)
            (Or.inl fun k hk => hscr_e256 k (by
              simp at hk; rcases hk with rfl | rfl | rfl | rfl <;> omega))
            hmi
        · (try clear hc); ds_split
          · -- `nv = 0`: return (`scr[128..131]` untouched)
            ds_steps
            exact hQ s_c mi hdw_c htmk_c rfl rfl rfl rfl (le_refl _)
              (def_scr256_spec_ext h10240 fun k hk _ => hscr_e256 k hk)
              (Or.inl fun k hk => hscr_e256 k (by
                simp at hk; rcases hk with rfl | rfl | rfl | rfl <;> omega))
              hmi
          · -- `abort_def = false ∧ nv ≥ 1`: `k[0]=nv; k[6]=nv; k[18]=0`, solve/core/shrink
            have hnv_ge1 : 1 ≤ nv_o.toNat := by bv_omega
            exact def_find_kitten_solve_core_m5_wp hLaws hSolve hCore hShrink rfl rfl rfl
              hdw hdw_c h132 h10240 htmk_c hnp64 hnn64 hnv_ge1 hnv_le128 hK_e hcls_e
              hscr_e256 hscr_e18 hmi hQ
    · -- Guard check (`side < 2 && !abort_def && trivial_side == 0xFFFFFFFF`) + outer loop body
      intro J_post hJ_post
      ds_split; rotate_left 1
      · ds_steps; exact hJ_post () mo ⟨hside_le, cls_o, exp_o, tmk_o, scr_o, tmp_o, hdw_o,
          hscr_o256, hscr_o18, hK_o, hexp_o, hts_o, hcls_o, hab_ts_o, hmo⟩
      have hside_lt2 : side_o.toNat < 2 := by bv_omega
      ds_split
      · ds_steps; exact hJ_post () mo ⟨hside_le, cls_o, exp_o, tmk_o, scr_o, tmp_o, hdw_o,
          hscr_o256, hscr_o18, hK_o, hexp_o, hts_o, hcls_o, hab_ts_o, hmo⟩
      have hab_false : abort_o = false := by
        cases abort_o <;> first | rfl | exact absurd hc (by decide)
      ds_split; rotate_left 1
      · ds_steps; exact hJ_post () mo ⟨hside_le, cls_o, exp_o, tmk_o, scr_o, tmp_o, hdw_o,
          hscr_o256, hscr_o18, hK_o, hexp_o, hts_o, hcls_o, hab_ts_o, hmo⟩
      subst abort_o
      have hts_ff : ts_o = 0xFFFFFFFF#32 := by bv_omega
      have hside_cases : side_o = 0#32 ∨ side_o = 1#32 := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hside_lt2 with h0 | h1
        · left; apply BitVec.eq_of_toNat_eq; simp; omega
        · right; apply BitVec.eq_of_toNat_eq; simp; omega
      have hside1 : (side_o + 1#32).toNat = side_o.toNat + 1 := by bv_omega
      -- 3 ternary assignments: `cnt`, `off_s`, `except`
      ds_to_group
      refine wp_join_group (ts := [i32])
        (fun (cnt, _) mc => mc = mo ∧ cnt = if side_o = 0#32 then np else nn) ?_ ?_
      rotate_left 1
      · intro Jc hJc; ds_split
        · ds_steps; exact hJc (np, ()) mo ⟨rfl, (ite_eq_left hc).symm⟩
        · ds_steps; exact hJc (nn, ()) mo ⟨rfl, (ite_eq_right hc).symm⟩
      rintro _ ⟨cnt, ⟨⟩⟩ mc ⟨hmc_eq, hcnt_eq⟩; subst mc
      ds_to_group
      refine wp_join_group (ts := [i32])
        (fun (off_s, _) mf => mf = mo ∧ off_s = if side_o = 0#32 then 0#32 else 64#32) ?_ ?_
      rotate_left 1
      · intro Jf hJf; ds_split
        · ds_steps; exact hJf (0#32, ()) mo ⟨rfl, (ite_eq_left hc).symm⟩
        · ds_steps; exact hJf (64#32, ()) mo ⟨rfl, (ite_eq_right hc).symm⟩
      rintro _ ⟨off_s, ⟨⟩⟩ mf ⟨hmf_eq, hoff_eq⟩; subst mf
      ds_to_group
      refine wp_join_group (ts := [i32])
        (fun (exc, _) me =>
          me = mo ∧ exc = if side_o = 0#32 then v <<< 1#32 else (v <<< 1#32) ||| 1#32)
        ?_ ?_
      rotate_left 1
      · intro Je hJe; ds_split
        · ds_steps; exact hJe (v <<< 1#32, ()) mo ⟨rfl, (ite_eq_left hc).symm⟩
        · ds_steps; exact hJe ((v <<< 1#32) ||| 1#32, ()) mo ⟨rfl, (ite_eq_right hc).symm⟩
      rintro _ ⟨exc, ⟨⟩⟩ me ⟨hme_eq, hexc_eq⟩; subst me
      have hcnt64 : cnt.toNat ≤ 64 := by rw [hcnt_eq]; split <;> omega
      have hocc_side : ∀ j < cnt.toNat,
          FullBveEntryOkW F_cur s (if off_s.toNat < 64 then 2 * v.toNat else 2 * v.toNat + 1)
            (s.scratch.scratch_buf[off_s.toNat + j]?.getD 0#32) := by
        intro j hj; rcases hside_cases with rfl | rfl
        · simp only [hcnt_eq, hoff_eq] at hj ⊢; simpa using hpos j hj
        · simp only [hcnt_eq, hoff_eq, show (1#32 : BitVec 32) = 0#32 ↔ False by decide,
            ↓reduceIte, show (64#32 : BitVec 32).toNat = 64 from rfl] at hj ⊢
          exact hneg j hj
      have hexc_n : exc.toNat = if off_s.toNat < 64 then 2 * v.toNat else 2 * v.toNat + 1 := by
        rcases hside_cases with rfl | rfl
        · rw [hoff_eq, hexc_eq, ite_eq_left rfl, ite_eq_left rfl, ite_eq_left (by decide)]
          exact hpl_n
        · rw [hoff_eq, hexc_eq]; simpa [show (1#32 : BitVec 32) = 0#32 ↔ False by decide,
            show (64#32 : BitVec 32).toNat = 64 from rfl] using hnl_n
      have hoff_dom : (off_s = 0#32 ∧ cnt = np) ∨ (off_s = 64#32 ∧ cnt = nn) := by
        rcases hside_cases with rfl | rfl
        · left; simp [hoff_eq, hcnt_eq]
        · right; simp [hoff_eq, hcnt_eq]
      -- Inner `idx` loop (`while (idx < cnt && !abort_def)`) with `break`
      let IdxBrkInv (nv_b : BitVec 32) (ab_b : Bool) (ts_b _idx_b : BitVec 32)
          (mb : Mem 64) : Prop :=
        FindDefIdxBrkInv KInv c F0 F_cur s R v np nn nv_b ab_b ts_b mb
      let IdxLpInv (nv_i : BitVec 32) (ab_i : Bool) (idx_i : BitVec 32)
          (mi : Mem 64) : Prop :=
        idx_i.toNat ≤ cnt.toNat ∧ IdxBrkInv nv_i ab_i ts_o idx_i mi
      clear hsci_len hsci_256 hsci_18 hK_init hm_i hdw_init htmk_init
      ds_to_group
      refine wp_loop_break_group (brkTs := [i32, .bool, i32, i32]) (lpTs := [i32, .bool, i32])
        (fun (nv_b, ab_b, ts_b, idx_b, _) mb => IdxBrkInv nv_b ab_b ts_b idx_b mb)
        (fun rem (nv_i, ab_i, idx_i, _) mi =>
          rem = cnt.toNat - idx_i.toNat ∧ IdxLpInv nv_i ab_i idx_i mi)
        ?_ ?_ ?_
      · rintro _ ⟨nv_b, ab_b, ts_b, _idx_b, ⟨⟩⟩ mb ⟨cls_b, exp_b, tmk_b, scr_b, tmp_b,
          hdwb, h256b, h18b, hKb, hexpb, htsb, hclsb, habb, hmb⟩
        ds_steps
        exact ih_o (nv_b, ab_b, ts_b, side_o + 1#32, ()) mb (by dsimp only; rw [hside1]; omega)
          ⟨by omega, cls_b, exp_b, tmk_b, scr_b, tmp_b, hdwb, h256b, h18b, hKb,
           hexpb, htsb, hclsb, habb, hmb⟩
      · rintro B L _ ⟨nv_i, ab_i, idx_i, ⟨⟩⟩ mi hB hL
          ⟨rfl, hidx_le, cls_i, exp_i, tmk_i, scr_i, tmp_i, hdw_i, h256_i, h18_i, hK_i,
           hexp_i, hts_i, hcls_i, hab_i, hmi⟩
        try clear hc
        let si := defFindState s exp_i tmk_i scr_i tmp_i
        have htmpli : tmp_i.length = c.max_vars := hdw_i.1.core_ok.tmp_len_arr
        have htmkli : tmk_i.length = 2 * c.max_vars := hdw_i.1.scratch_ok.tarjan_mark_len
        have hwsli : exp_i.length = 2 * c.max_vars := hdw_i.1.scratch_ok.wsort_len
        have hscrli : scr_i.length = c.scratch_cap := hdw_i.1.scratch_ok.scratch_buf_len
        ds_split; rotate_left 1
        · ds_steps
          exact hB (nv_i, ab_i, ts_o, idx_i, ()) mi
            ⟨cls_i, exp_i, tmk_i, scr_i, tmp_i, hdw_i, h256_i, h18_i, hK_i,
             hexp_i, hts_i, hcls_i, hab_i, hmi⟩
        have hidx_lt : idx_i.toNat < cnt.toNat := by bv_omega
        ds_split
        · ds_steps
          exact hB (nv_i, ab_i, ts_o, idx_i, ()) mi
            ⟨cls_i, exp_i, tmk_i, scr_i, tmp_i, hdw_i, h256_i, h18_i, hK_i,
             hexp_i, hts_i, hcls_i, hab_i, hmi⟩
        have hab_if : ab_i = false := by
          cases ab_i <;> first | rfl | exact absurd hc (by decide)
        subst ab_i
        have heid_lt : off_s.toNat + idx_i.toNat < 128 := by
          rcases hoff_dom with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp at * <;> omega
        have heid_bv : (off_s + idx_i).toNat = off_s.toNat + idx_i.toNat := by bv_omega
        have heid_64 : ((off_s + idx_i).setWidth 64).toNat = off_s.toNat + idx_i.toNat := by
          bv_omega
        have hidx1 : (idx_i + 1#32).toNat = idx_i.toNat + 1 := by bv_omega
        have hw_eq : scr_i[off_s.toNat + idx_i.toNat]? =
            s.scratch.scratch_buf[off_s.toNat + idx_i.toNat]? :=
          h256_i (off_s.toNat + idx_i.toNat) (by omega)
        have hidx_len : off_s.toNat + idx_i.toNat < scr_i.length := by omega
        let w := s.scratch.scratch_buf[off_s.toNat + idx_i.toNat]?.getD 0#32
        have hw_si :
            si.scratch.scratch_buf[((off_s + idx_i).setWidth 64).toNat]'(by
              change ((off_s + idx_i).setWidth 64).toNat < scr_i.length
              rw [heid_64]; exact hidx_len) = w := by
          have h1 : scr_i[off_s.toNat + idx_i.toNat]? = some w := by
            dsimp only [w]; rw [hw_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]
          change scr_i[((off_s + idx_i).setWidth 64).toNat]'_ = w
          rw [list_getElem_congr heid_64 _ hidx_len]
          exact Option.some.inj (by rw [← List.getElem?_eq_getElem hidx_len, h1])
        have heid_bd : off_s.toNat + idx_i.toNat < np.toNat ∨
            (64 ≤ off_s.toNat + idx_i.toNat ∧ off_s.toNat + idx_i.toNat < 64 + nn.toNat) := by
          rcases hoff_dom with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · left; simpa using hidx_lt
          · right; simp at hidx_lt ⊢; omega
        have heid_if_64 :
            (if off_s.toNat + idx_i.toNat < 64 then 2 * v.toNat else 2 * v.toNat + 1) =
              if off_s.toNat < 64 then 2 * v.toNat else 2 * v.toNat + 1 := by
          rcases hoff_dom with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp at hidx_lt ⊢ <;> omega
        ds_to_group
        (try dsimp only [LeanQbe.T.lift2, LeanQbe.T.Arg.val, Prod.fst])
        ds_to_group
        -- Join group for `idx++`
        refine wp_join_group (ts := [i32, .bool, i32])
          (fun (nv_n, ab_n, _ts_n, _) mn =>
            FindDefIdxJoinInv KInv c F0 F_cur s R v np nn ts_o nv_n ab_n mn)
          ?_ ?_
        · rintro _ ⟨nv_n, ab_n, _ts_n, ⟨⟩⟩ mn ⟨hab_n, cls_n, exp_n, tmk_n, scr_n, tmp_n, hdw_n,
            h256_n, h18_n, hK_n, hexp_n, hcls_n, hmn⟩
          ds_steps
          exact hL (cnt.toNat - (idx_i + 1#32).toNat) (nv_n, ab_n, idx_i + 1#32, ()) mn
            (by omega) ⟨rfl, by omega, cls_n, exp_n, tmk_n, scr_n, tmp_n, hdw_n, h256_n,
              h18_n, hK_n, hexp_n, hts_i, hcls_n, hab_n, hmn⟩
        · intro J_nx hJ_nx
          have hscr_mod_lt : (off_s.toNat + idx_i.toNat) % 2 ^ 32 < scr_i.length := by
            (try clear hc); rw [hscrli]; omega
          have hw_scr_bv :
              scr_i[(off_s.toNat + idx_i.toNat) % 2 ^ 32]'hscr_mod_lt = w := by
            have h1 : (off_s.toNat + idx_i.toNat) % 2 ^ 32 = off_s.toNat + idx_i.toNat := by omega
            rw [list_getElem_congr h1 _ (by omega),
              ← Option.getD_some (a := scr_i[off_s.toNat + idx_i.toNat]'_) (b := 0#32),
              ← List.getElem?_eq_getElem (by omega), hw_eq]
          (try clear hc); ds_split
          · -- Binary watch branch (`(w & PW_BIN_FLAG) != 0`)
            have hbin : (w &&& 0x80000000#32) ≠ 0#32 := by
              simpa [hw_scr_bv] using hc
            have hok_j := hocc_side idx_i.toNat hidx_lt
            unfold FullDefSweep.FullBveEntryOkW Full.FullBveEntryOkW at hok_j
            rw [ite_eq_left hbin] at hok_j
            let l_bv := w &&& 0x7FFFFFFF#32
            let lv_bv := l_bv >>> 1#32
            have hl_lt : l_bv.toNat < 2 * s.core.cur_vars := hok_j.1
            have hlv_eq : lv_bv.toNat = l_bv.toNat / 2 := by
              dsimp only [lv_bv]; exact bv32_shr1_toNat l_bv
            have hlv_lt : lv_bv.toNat < s.core.cur_vars := by omega
            have hl_val_len : (l_bv.setWidth 64).toNat < si.core.vals.length := by
              change (l_bv.setWidth 64).toNat < s.core.vals.length; bv_omega
            have hl_val_len_si :
                ((si.scratch.scratch_buf[(BitVec.setWidth 64 (off_s + idx_i)).toNat]'(by
                  change (BitVec.setWidth 64 (off_s + idx_i)).toNat < scr_i.length
                  rw [heid_64]; exact hidx_len) &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                  si.core.vals.length := by
              rw [hw_si]; exact hl_val_len
            have hl_raw_lt : l_bv.toNat < s.core.vals.length := by bv_omega
            have hl_val_len_s : (l_bv.setWidth 64).toNat < s.core.vals.length := hl_val_len
            have hw_raw : si.core.vals[(l_bv.setWidth 64).toNat]'hl_val_len =
                s.core.vals[l_bv.toNat]?.getD 0#8 := by
              have h1 : (l_bv.setWidth 64).toNat = l_bv.toNat := by bv_omega
              change s.core.vals[(l_bv.setWidth 64).toNat]'hl_val_len_s =
                s.core.vals[l_bv.toNat]?.getD 0#8
              rw [list_getElem_congr h1 hl_val_len_s hl_raw_lt,
                List.getElem?_eq_getElem hl_raw_lt, Option.getD_some]
            have h_idx_l : w.toNat &&& 2147483647 = l_bv.toNat := by
              dsimp only [l_bv]; rw [BitVec.toNat_and]; rfl
            have hdom_l := hw.vals_domain l_bv.toNat hl_lt
            (try clear hc); ds_to_group; refine wp_unroll_group fun _ _ => ?_; ds_split
            · -- `vals[l] == 0#8`
              have hl_zero : s.core.vals[l_bv.toNat]?.getD 0#8 = 0#8 := by
                have hc' := hc; simp only [hw_scr_bv] at hc'
                change BitVec.signExtend 32 (s.core.vals[l_bv.toNat]'hl_raw_lt) = 0#32 at hc'
                rw [← Option.getD_some (a := s.core.vals[l_bv.toNat]'hl_raw_lt) (b := 0#8),
                  ← List.getElem?_eq_getElem hl_raw_lt] at hc'
                rcases hdom_l with h0 | h1 | hf
                · exact h0
                · rw [h1] at hc'; exact absurd hc' (by decide)
                · rw [hf] at hc'; exact absurd hc' (by decide)
              try clear hc
              ds_to_group
              refine wp_join_group (ts := [i32, .bool])
                (fun (nv_p, ab_p, _) mp =>
                  ab_p = false ∧ nv_i.toNat ≤ nv_p.toNat ∧ 1 ≤ nv_p.toNat ∧
                  ∃ (exp_p tmk_p : List (BitVec 32)),
                    let sp := defFindState s exp_p tmk_p scr_i tmp_i
                    exp_p.length = 2 * c.max_vars ∧ tmk_p.length = 2 * c.max_vars ∧
                    DefExpInv s.core.cur_vars nv_p.toNat exp_p tmk_p ∧
                    (∀ i < nv_i.toNat, exp_p[i]? = exp_i[i]?) ∧
                    tmk_p[lv_bv.toNat]?.getD 0#32 ≠ 0#32 ∧
                    (FullMem c sp ⋆ R) mp)
                ?_ ?_
              · rintro _ ⟨nv_p, ab_p, ⟨⟩⟩ mp ⟨rfl, hnv_mono, _hnv_1, exp_p, tmk_p, hexpp_len,
                  htmkp_len, hexpp, hexpp_mono, hnz_lv, hmp⟩
                let idx_lv := ((tmk_p[lv_bv.toNat]?.getD 0#32) - 1#32).toNat
                obtain ⟨hidx_lv_lt, hexp_lv⟩ := defExpInv_get hexpp hlv_lt hnz_lv
                have hcur_pos : 0 < c.max_vars := by
                  have := defExpInv_le_cv hexpp; omega
                have htmp_pos : 0 < tmp_i.length := by omega
                have hexp_all := defClsInv_mono hcls_i hnv_mono hexpp_mono
                let tmk_v := tmk_p[lv_bv.toNat]?.getD 0#32
                let lit_loc := ((tmk_v - 1#32) <<< 1#32) ||| (l_bv &&& 1#32)
                have hlit_loc_nat : lit_loc.toNat = 2 * idx_lv + l_bv.toNat % 2 := by
                  dsimp only [lit_loc, tmk_v]
                  rw [show (tmk_p[lv_bv.toNat]?.getD 0#32 - 1#32) <<< 1#32 =
                    (tmk_p[lv_bv.toNat]?.getD 0#32 - 1#32) <<< (1 : Nat) from rfl]
                  have h128 := hexpp.1
                  exact bv32_lit_shl_or (tmk_p[lv_bv.toNat]?.getD 0#32 - 1#32) l_bv
                    (Nat.lt_trans (Nat.lt_of_lt_of_le hidx_lv_lt h128) (by decide))
                have hlit_loc_lt : lit_loc.toNat < 2 * nv_p.toNat := by omega
                have hlit_loc_128 : lit_loc.toNat < 2 * 128 := by have := hexpp.1; omega
                have hgl_eq : fullDefGlobalLit exp_p lit_loc.toNat = l_bv.toNat := by
                  unfold fullDefGlobalLit
                  rw [hlit_loc_nat, show (2 * idx_lv + l_bv.toNat % 2) / 2 = idx_lv by omega,
                    show (2 * idx_lv + l_bv.toNat % 2) % 2 = l_bv.toNat % 2 by omega, hexp_lv]
                  omega
                have hlv_tmk_sp :
                    (((scr_i[(BitVec.setWidth 64 (off_s + idx_i)).toNat]'(by
                      rw [heid_64]; exact hidx_len) &&& 0x7FFFFFFF#32) >>> 1#32).setWidth
                        64).toNat < tmk_p.length := by
                  have hw_raw_si : scr_i[(BitVec.setWidth 64 (off_s + idx_i)).toNat]'(by
                      rw [heid_64]; exact hidx_len) = w := hw_si
                  rw [hw_raw_si]; change (lv_bv.setWidth 64).toNat < tmk_p.length
                  rw [bv_c0_zext32_64, htmkp_len]; omega
                dsimp only [defFindState] at hmp
                ds_steps_soft
                (try simp only [LeanQbe.T.lift2, LeanQbe.T.Arg.val])
                c0_hstep
                (try dsimp only [LeanQbe.T.lift2, LeanQbe.T.Arg.val, Prod.fst] at hm)
                ds_steps
                let sp_tmp := defFindState s exp_p tmk_p scr_i (tmp_i.set 0 lit_loc)
                have hdw_p_tmp : FullDenseInvW c F0 F_cur sp_tmp :=
                  fullDenseInvW_defFindState hdw (by simp [htmpli]) hexpp_len htmkp_len hscrli
                have htmp_eq_sp : sp_tmp.core.tmp[0]?.getD 0#32 = lit_loc := by
                  dsimp only [sp_tmp]; rw [defFindState_core_tmp, List.getElem?_set_self htmp_pos,
                    Option.getD_some]
                refine def_find_call_add_clause hAddCl (eid := off_s + idx_i) (sz := 1#32)
                  rfl rfl hdw_p_tmp h10240 hK_i (by decide) (by decide)
                  (by simp [sp_tmp, htmpli]; omega)
                  (fun j hj => by
                    rw [show j = 0 by have hj1 : (1#32 : BitVec 32).toNat = 1 := rfl; omega,
                      htmp_eq_sp]
                    exact hlit_loc_128)
                  (by
                    simp only [sp_tmp, defFindState, getElem_eq_getElem?_getD (d := 0#32),
                      bv_c0_zext32_64, heid_bv, hw_eq] at hm ⊢
                    simpa only [w, lit_loc, tmk_v, l_bv, lv_bv,
                      show (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 from rfl,
                      show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl,
                      show (OfNat.ofNat 1 : BitVec 32) = 1#32 from rfl,
                      show ∀ z : BitVec 32, z <<< (1 : Nat) = z <<< 1#32 from fun _ => rfl,
                      show ∀ z : BitVec 32, z >>> (1 : Nat) = z >>> 1#32 from fun _ => rfl]
                      using hm)
                  fun ok scr_a ma hscra_len ha256 ha18 hKt hKf hma => ?_
                have hscr_a256 : ∀ k < 256, scr_a[k]? = s.scratch.scratch_buf[k]? := fun k hk =>
                  (ha256 k hk).trans (h256_i k hk)
                have hscr_a18 : scr_a[256 + 18]? = some 0#32 := by
                  rw [ha18, defFindState_scratch_scr, h18_i]
                have hdw_a : FullDenseInvW c F0 F_cur
                    (defFindState s exp_p tmk_p scr_a (tmp_i.set 0 lit_loc)) :=
                  fullDenseInvW_defFindState hdw (by simp [htmpli]) hexpp_len htmkp_len hscra_len
                have hma' :
                    (FullMem c (defFindState s exp_p tmk_p scr_a (tmp_i.set 0 lit_loc)) ⋆ R) ma :=
                  hma
                ds_split
                · -- `ok = true`: push `(eid, [lit_loc])` into `cls` and jump `J_nx`
                  have hok_true : ok = true := hc
                  have htake1 : ((tmp_i.set 0 lit_loc).take (1#32 : BitVec 32).toNat).map
                      BitVec.toNat = [lit_loc.toNat] := by
                    rw [show (1#32 : BitVec 32).toNat = 1 from rfl, List.take_one,
                      List.head?_eq_getElem?, List.getElem?_set_self htmp_pos]
                    rfl
                  have hKt' := hKt hok_true
                  rw [defFindState_core_tmp, htake1] at hKt'
                  ds_steps
                  refine hJ_nx (nv_p, false, ts_o, ()) ma
                    ⟨fun h => Bool.noConfusion h,
                     cls_i ++ [(off_s.toNat + idx_i.toNat, [lit_loc.toNat])],
                     exp_p, tmk_p, scr_a, tmp_i.set 0 lit_loc, hdw_a, hscr_a256, hscr_a18,
                     by simpa [heid_bv] using hKt', hexpp, fun e he => ?_, hma'⟩
                  rw [List.mem_append, List.mem_singleton] at he
                  rcases he with he_old | rfl
                  · exact hexp_all e he_old
                  · refine ⟨fun x hx => by simp at hx; subst x; exact hlit_loc_lt,
                      heid_bd, (by simp), fun l hl => ?_⟩
                    right
                    rw [heid_if_64, bveOccRestLits] at hl
                    change l ∈ (if (w &&& 0x80000000#32) ≠ 0#32 then
                      [(w &&& 0x7FFFFFFF#32).toNat] else
                      (fullArenaClauseLits s w.toNat).filter (· !=
                        if off_s.toNat < 64 then 2 * v.toNat else 2 * v.toNat + 1)) at hl
                    rw [ite_eq_left hbin, List.mem_singleton] at hl
                    subst l
                    simp [hgl_eq, l_bv]
                · -- `!full_kitten_add_clause`: `abort_def = true; break;`
                  have hok_false : ok = false := by
                    cases ok <;> first | exact absurd hc (by decide) | rfl
                  ds_steps
                  exact hB (nv_p, true, ts_o, idx_i, ()) ma
                    ⟨cls_i, exp_p, tmk_p, scr_a, tmp_i.set 0 lit_loc, hdw_a, hscr_a256,
                     hscr_a18, hKf hok_false, hexpp, hts_i, hexp_all, fun _ => hts_ff, hma'⟩
              · intro Jp hJp
                have hlv_tmk : (lv_bv.setWidth 64).toNat < tmk_i.length := by
                  rw [htmkli, bv_c0_zext32_64]; omega
                have hlv_tmk_si :
                    ((((si.scratch.scratch_buf[(BitVec.setWidth 64 (off_s + idx_i)).toNat]'(by
                      change (BitVec.setWidth 64 (off_s + idx_i)).toNat < scr_i.length
                      rw [heid_64]; exact hidx_len) &&& 0x7FFFFFFF#32) >>> 1#32).setWidth
                        64).toNat) < tmk_i.length := by
                  rw [hw_si]; exact hlv_tmk
                ds_split
                · -- `tmk[lv] == 0`
                  have htz : tmk_i[lv_bv.toNat]?.getD 0#32 = 0#32 := by
                    have hc' := hc
                    rw [getElem_eq_getElem?_getD (d := 0#32), hw_scr_bv] at hc'
                    rw [hlv_eq]
                    simpa only [show (w &&& 0x7FFFFFFF#32) >>> 1#32 = lv_bv from rfl,
                      show (w &&& 2147483647#32) = l_bv from rfl,
                      show (w &&& 2147483647) = l_bv from rfl,
                      show (0 : BitVec 32) = 0#32 from rfl,
                      bv_c0_zext32_64, hlv_eq, h_idx_l] using hc'
                  (try clear hc); ds_split
                  · -- `nv >= 128`: `abort_def = true; break;`
                    ds_steps
                    exact hB (nv_i, true, ts_o, idx_i, ()) mi
                      ⟨cls_i, exp_i, tmk_i, scr_i, tmp_i, hdw_i, h256_i, h18_i, hK_i,
                       hexp_i, hts_i, hcls_i, fun _ => hts_ff, hmi⟩
                  · have hnv128 : nv_i.toNat < 128 := by bv_omega
                    have hnv1 : (nv_i + 1#32).toNat = nv_i.toNat + 1 := by bv_omega
                    have hcv_ex := defExpInv_le_cv hexp_i
                    obtain ⟨_hnv_cv, hexp_p, hexp_mono⟩ := defExpInv_push hexp_i hnv128 hlv_lt htz
                      (by rw [hwsli]; omega) (by rw [htmkli]; omega)
                    have hmi' := hmi
                    dsimp only [defFindState] at hmi'
                    have hw_si_raw :
                        scr_i[(BitVec.setWidth 64 (off_s + idx_i)).toNat]'(by
                          rw [heid_64]; exact hidx_len) = w := hw_si
                    ds_steps
                    (try dsimp only [LeanQbe.T.lift2, LeanQbe.T.Arg.val, Prod.fst] at hm)
                    have hnz_p :
                        (tmk_i.set lv_bv.toNat (nv_i + 1#32))[lv_bv.toNat]?.getD 0#32 ≠
                          0#32 := by
                      rw [List.getElem?_set_self (by rw [htmkli]; omega), Option.getD_some]
                      intro h; have := congrArg BitVec.toNat h; simp [hnv1] at this
                    refine hJp (nv_i + 1#32, false, ()) _
                      ⟨rfl, by omega, by omega, exp_i.set nv_i.toNat lv_bv,
                       tmk_i.set lv_bv.toNat (nv_i + 1#32), by simp [hwsli], by simp [htmkli],
                       by rw [hnv1]; simpa [show BitVec.ofNat 32 (nv_i.toNat + 1) = nv_i + 1#32
                         from by bv_omega] using hexp_p,
                       hexp_mono, hnz_p, by
                        simpa [defFindState, hw_scr_bv, hw_si_raw, bv_c0_zext32_64,
                          show (w &&& 0x7FFFFFFF#32) >>> 1#32 = lv_bv from rfl,
                          show (w &&& 2147483647#32) >>> OfNat.ofNat 1 = lv_bv from rfl,
                          show nv_i.toNat % 18446744073709551616 = nv_i.toNat from
                            Nat.mod_eq_of_lt (by omega),
                          show ((off_s.toNat + idx_i.toNat) % 2 ^ 32) % 18446744073709551616 =
                            (off_s.toNat + idx_i.toNat) % 2 ^ 32 from
                              Nat.mod_eq_of_lt (by omega),
                          show lv_bv.toNat % 18446744073709551616 = lv_bv.toNat from
                            Nat.mod_eq_of_lt (by omega),
                          show nv_i + 1 = nv_i + 1#32 from rfl] using hm⟩
                · -- `tmk[lv] != 0`
                  have hne_t : tmk_i[lv_bv.toNat]?.getD 0#32 ≠ 0#32 := by
                    have hc' := hc
                    rw [getElem_eq_getElem?_getD (d := 0#32), hw_scr_bv] at hc'
                    rw [hlv_eq]
                    simpa only [show (w &&& 0x7FFFFFFF#32) >>> 1#32 = lv_bv from rfl,
                      show (w &&& 2147483647#32) = l_bv from rfl,
                      show (w &&& 2147483647) = l_bv from rfl,
                      show (0 : BitVec 32) = 0#32 from rfl,
                      bv_c0_zext32_64, hlv_eq, h_idx_l] using hc'
                  have hk_lv := (defExpInv_get hexp_i hlv_lt hne_t).1
                  ds_steps
                  exact hJp (nv_i, false, ()) mi
                    ⟨rfl, le_refl _, by omega, exp_i, tmk_i, hwsli, htmkli, hexp_i, fun _ _ => rfl,
                     hne_t, hmi⟩
            · -- `vals[l] != 0#8`
              have hl_raw_lt : l_bv.toNat < s.core.vals.length := by omega
              have hne0 : s.core.vals[l_bv.toNat]?.getD 0#8 ≠ 0#8 := fun h0 => by
                have hc' := hc; simp only [hw_scr_bv] at hc'
                change BitVec.signExtend 32 (s.core.vals[l_bv.toNat]'hl_raw_lt) ≠ 0#32 at hc'
                rw [← Option.getD_some (a := s.core.vals[l_bv.toNat]'hl_raw_lt) (b := 0#8),
                  ← List.getElem?_eq_getElem hl_raw_lt, h0] at hc'
                exact hc' rfl
              (try clear hc); ds_split
              · -- `vals[l] < 0#8` -> `0xFF#8`: `trivial_side = eid; break;`
                have hfals : s.core.vals[l_bv.toNat]?.getD 0#8 = 0xFF#8 := by
                  have hneq1 : s.core.vals[l_bv.toNat]?.getD 0#8 ≠ 1#8 := fun h1 => by
                    have hc' := hc; simp only [hw_scr_bv] at hc'
                    change (BitVec.signExtend 32
                      (s.core.vals[l_bv.toNat]'hl_raw_lt)).slt 0#32 = true at hc'
                    rw [← Option.getD_some (a := s.core.vals[l_bv.toNat]'hl_raw_lt) (b := 0#8),
                      ← List.getElem?_eq_getElem hl_raw_lt, h1] at hc'
                    exact absurd hc' (by decide)
                  exact (hdom_l.elim (absurd · hne0) (·.elim (absurd · hneq1) id))
                ds_steps
                refine hB (nv_i, false, off_s + idx_i, idx_i, ()) mi
                  ⟨cls_i, exp_i, tmk_i, scr_i, tmp_i, hdw_i, h256_i, h18_i, hK_i,
                   hexp_i, Or.inr ⟨?_, def_trivial_side_unsat fun l' hl' => ?_⟩,
                   hcls_i, fun h => Bool.noConfusion h, hmi⟩
                · rwa [heid_bv]
                · rw [heid_bv] at hl'
                  change l' ∈ bveOccRestLits s
                    (if off_s.toNat + idx_i.toNat < 64 then 2 * v.toNat else 2 * v.toNat + 1)
                    w at hl'
                  rw [heid_if_64] at hl'
                  simp only [bveOccRestLits, ite_eq_left hbin, List.mem_singleton] at hl'
                  subst l'; exact ⟨hl_lt, hfals⟩
              · -- `vals[l] > 0#8` (satisfied): continue `idx + 1`
                ds_steps
                exact hJ_nx (nv_i, false, ts_o, ()) mi
                  ⟨fun h => Bool.noConfusion h, cls_i, exp_i, tmk_i, scr_i, tmp_i, hdw_i,
                   h256_i, h18_i, hK_i, hexp_i, hcls_i, hmi⟩
          · -- Long clause branch (`(w & PW_BIN_FLAG) == 0`)
            have hnot_bin : ¬ (w &&& 0x80000000#32) ≠ 0#32 :=
              Classical.not_not.mpr (by simpa [hw_scr_bv] using hc)
            try clear hc
            have hok_j := hocc_side idx_i.toNat hidx_lt
            unfold FullDefSweep.FullBveEntryOkW Full.FullBveEntryOkW at hok_j
            rw [ite_eq_right hnot_bin] at hok_j
            obtain ⟨href, hgarb⟩ := hok_j
            have hwf := hw.arena.refs_wf w.toNat href
            have hw2_nat : (w.setWidth 64 + 2#64).toNat = w.toNat + 2 := by
              rw [BitVec.toNat_add, bv_c0_zext32_64,
                show (2#64 : BitVec 64).toNat = 2 from rfl]
              have hlen_lt : w.toNat + 2 < 2 ^ 64 := by have := hwf.1; omega
              exact Nat.mod_eq_of_lt hlen_lt
            let sz_cl := s.core.arena[w.toNat + 2]'(by omega)
            have har_w2_si :
                ((si.scratch.scratch_buf[(BitVec.setWidth 64 (off_s + idx_i)).toNat]'(by
                  change (BitVec.setWidth 64 (off_s + idx_i)).toNat < scr_i.length
                  rw [heid_64]; exact hidx_len)).setWidth 64 + 2#64).toNat <
                  si.core.arena.length := by
              rw [hw_si, hw2_nat]; change w.toNat + 2 < s.core.arena.length; omega
            have hsz_cl_si :
                si.core.arena[((si.scratch.scratch_buf[(BitVec.setWidth 64
                  (off_s + idx_i)).toNat]'(by
                    change (BitVec.setWidth 64 (off_s + idx_i)).toNat < scr_i.length
                    rw [heid_64]; exact hidx_len)).setWidth 64 + 2#64).toNat]'har_w2_si =
                  sz_cl := by
              change s.core.arena[_]'_ = s.core.arena[w.toNat + 2]'_
              exact list_getElem_congr (by rw [hw_si, hw2_nat]) _ _
            have hsz_core : sz_cl.toNat = fullArenaClauseSizeCore s.core w.toNat := by
              unfold fullArenaClauseSizeCore sz_cl
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            have hcl_lits_len : (fullArenaClauseLits s w.toNat).length = sz_cl.toNat := by
              unfold fullArenaClauseLits fullArenaClauseLitsCore
              rw [List.length_map, List.length_take, List.length_drop, ← hsz_core]
              exact Nat.min_eq_left (by omega)
            -- Inner clause loop: `while (k < sz)` with `break` (`nv`, `abort`, `sat`, `csz`, `k`)
            clear h132 hnpnn3 hpl_n hnl_n
            ds_to_group
            have hsz_cl_eq : sz_cl = s.core.arena[w.toNat + 2]'(by omega) := rfl
            refine def_find_k_loop_wp rfl rfl rfl rfl rfl rfl hw_si hsz_cl_si rfl
              hdw hdw_i hexp_i href hgarb hsz_cl_eq hmi
              fun nv_k ab_k sat_k csz_k _k_k mk
                ⟨hnv_ik, _hab_sat, exp_k, tmk_k, tmp_k, hdw_k, hexp_k, hexp_mono,
                 hres_k, hmk⟩ => ?_
            have hcls_k := defClsInv_mono hcls_i hnv_ik hexp_mono
            ds_split
            · -- `abort_def = true`: break out of `idx` loop
              have hab_kt : ab_k = true := hc
              subst ab_k
              ds_steps
              exact hB (nv_k, true, ts_o, idx_i, ()) mk
                ⟨cls_i, exp_k, tmk_k, scr_i, tmp_k, hdw_k, h256_i, h18_i, hK_i,
                 hexp_k, hts_i, hcls_k, fun _ => hts_ff, hmk⟩
            · have hab_kf : ab_k = false := by
                cases ab_k <;> first | rfl | exact absurd hc (by decide)
              subst ab_k
              (try clear hc); ds_to_group; refine wp_unroll_group fun _ _ => ?_; ds_split
              · -- `sat = true`: skip clause and continue `idx + 1`
                ds_steps
                exact hJ_nx (nv_k, false, ts_o, ()) mk
                  ⟨fun h => Bool.noConfusion h, cls_i, exp_k, tmk_k, scr_i, tmp_k, hdw_k,
                   h256_i, h18_i, hK_i, hexp_k, hcls_k, hmk⟩
              · -- `!sat`: check `csz == 0`
                have hsat_kf : sat_k = false := by
                  cases sat_k <;> first | rfl | exact absurd hc (by decide)
                obtain ⟨hcsz_128, hcsz_le_k, hlts_k, hcov_k⟩ := hres_k rfl hsat_kf
                have hbve_eq :
                    bveOccRestLits s
                      (if off_s.toNat < 64 then 2 * v.toNat else 2 * v.toNat + 1) w =
                      (fullArenaClauseLits s w.toNat).filter (· != exc.toNat) := by
                  unfold bveOccRestLits; rw [ite_eq_right hnot_bin, hexc_n]
                (try clear hc); ds_split
                · -- `csz == 0`: `trivial_side = eid; break;`
                  have hcsz0 : csz_k.toNat = 0 := by bv_omega
                  ds_steps
                  refine hB (nv_k, false, off_s + idx_i, idx_i, ()) mk
                    ⟨cls_i, exp_k, tmk_k, scr_i, tmp_k, hdw_k, h256_i, h18_i, hK_i,
                     hexp_k, Or.inr ⟨?_, def_trivial_side_unsat fun l' hl' => ?_⟩,
                     hcls_k, fun h => Bool.noConfusion h, hmk⟩
                  · rwa [heid_bv]
                  · rw [heid_bv] at hl'
                    change l' ∈ bveOccRestLits s
                      (if off_s.toNat + idx_i.toNat < 64 then 2 * v.toNat else 2 * v.toNat + 1)
                      w at hl'
                    rw [heid_if_64, hbve_eq] at hl'
                    rcases hcov_k l' hl' with hfalse | hmap
                    · exact hfalse
                    · rw [hcsz0, List.take_zero, List.map_nil] at hmap; cases hmap
                · -- `csz > 0`: call `full_kitten_add_clause(h, eid, tmp, csz)`
                  have hcsz_pos : 1 ≤ csz_k.toNat := by bv_omega
                  have hnv128 : nv_k.toNat ≤ 128 := hexp_k.1
                  have hlts_128 : ∀ j < csz_k.toNat, (tmp_k[j]?.getD 0#32).toNat < 2 * 128 :=
                    fun j hj => Nat.lt_of_lt_of_le (hlts_k j hj) (by omega)
                  ds_steps
                  have hmk' : (FullMem c (defFindState s exp_k tmk_k scr_i tmp_k) ⋆ R) mk := hmk
                  refine def_find_call_add_clause hAddCl rfl rfl hdw_k (by omega) hK_i hcsz_pos
                    (by dsimp only [LeanQbe.T.Arg.val]; omega) hcsz_le_k hlts_128 hmk'
                    fun ok scr_a ma hscra_len ha256 ha18 hKt hKf hma => ?_
                  have hscr_a256 : ∀ k < 256, scr_a[k]? = s.scratch.scratch_buf[k]? :=
                    fun k hk => (ha256 k hk).trans (h256_i k hk)
                  have hscr_a18 : scr_a[256 + 18]? = some 0#32 := by
                    rw [ha18, defFindState_scratch_scr, h18_i]
                  have hdw_a :
                      FullDenseInvW c F0 F_cur (defFindState s exp_k tmk_k scr_a tmp_k) :=
                    fullDenseInvW_defFindState hdw hdw_k.1.core_ok.tmp_len_arr
                      hdw_k.1.scratch_ok.wsort_len hdw_k.1.scratch_ok.tarjan_mark_len hscra_len
                  ds_split
                  · -- `ok = true`: push `(eid, tmp[0..csz))`, continue `idx + 1`
                    have hok_true : ok = true := hc
                    let c_loc := (tmp_k.take csz_k.toNat).map BitVec.toNat
                    have htake_ne : c_loc ≠ [] := by
                      intro hnil
                      have hlen := congrArg List.length hnil
                      simp [c_loc, hcsz_le_k] at hlen; omega
                    have htake_bd : ∀ l ∈ c_loc, l < 2 * nv_k.toNat := fun l hl => by
                      rw [List.mem_map] at hl
                      obtain ⟨x, hx, rfl⟩ := hl
                      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
                      have hj' : j < csz_k.toNat := by simp at hj; omega
                      rw [List.getElem_take]
                      have hlt := hlts_k j hj'
                      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hlt
                    have hmap_glob : c_loc.map (fullDefGlobalLit exp_k) =
                        (tmp_k.take csz_k.toNat).map
                          (fun x => fullDefGlobalLit exp_k x.toNat) := by
                      dsimp only [c_loc]; rw [List.map_map]; rfl
                    ds_steps
                    refine hJ_nx (nv_k, false, ts_o, ()) ma
                      ⟨fun h => Bool.noConfusion h,
                       cls_i ++ [(off_s.toNat + idx_i.toNat, c_loc)],
                       exp_k, tmk_k, scr_a, tmp_k, hdw_a, hscr_a256, hscr_a18,
                       by
                         dsimp only [c_loc]
                         have hKt' := hKt hok_true
                         dsimp only [LeanQbe.T.Arg.val, Prod.fst] at hKt'
                         rw [defFindState_core_tmp, heid_bv] at hKt'
                         exact hKt',
                       hexp_k, fun e he => ?_, hma⟩
                    rw [List.mem_append, List.mem_singleton] at he
                    rcases he with he_old | rfl
                    · exact hcls_k e he_old
                    · refine ⟨htake_bd, heid_bd, htake_ne, fun l hl => ?_⟩
                      rw [heid_if_64, hbve_eq] at hl
                      rw [hmap_glob]; exact hcov_k l hl
                  · -- `!ok`: `abort_def = true; break;`
                    have hok_false : ok = false := by
                      cases ok <;> first | exact absurd hc (by decide) | rfl
                    ds_steps
                    exact hB (nv_k, true, ts_o, idx_i, ()) ma
                      ⟨cls_i, exp_k, tmk_k, scr_a, tmp_k, hdw_a, hscr_a256, hscr_a18,
                       hKf hok_false, hexp_k, hts_i, hcls_k, fun _ => hts_ff, hma⟩
      · intro _B _L _ hL; ds_steps; exact hL cnt.toNat (nv_o, false, 0#32, ()) mo
          ⟨rfl, Nat.zero_le _, cls_o, exp_o, tmk_o, scr_o, tmp_o, hdw_o, hscr_o256,
           hscr_o18, hK_o, hexp_o, hts_o, hcls_o, fun h => Bool.noConfusion h, hmo⟩


end LeanQbe.T.Examples.Kissat.FullM5KittenDefFix
