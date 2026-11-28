/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Parse.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Parse.Tumble
public import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1

/-!
# Invariant & Entailment Helpers for `full_ingest_cl` (`Proof.Parse.WpIngestHelpers`)

Pure arithmetic, CNF relabeling/entailment, `FullMem`/`dimacsState` split-join,
pigeonhole bound for `lit_mark` deduplication, and level-0 unit assignment preservation
lemmas supporting `Proof.Parse.WpIngest`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Parse

open Std.Sat
open Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

/-! ## 1. Separation-Logic `dimacsState` Split / Join for `FullMem` -/

theorem fullMem_split_dimacs {c : FullCfg} {s : FullState} {cnf_ptr : BitVec 64}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R) m) :
    (bytes cnf_ptr cnfBytes ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
      ((array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
        FullScratchArrays c s.scratch ⋆ c.pad) ⋆ R)) m := by
  unfold FullMem at hm
  simpa only [sep_assoc] using hm

theorem fullMem_join_dimacs {c : FullCfg} {s : FullState} {cnf_ptr : BitVec 64}
    {cnfBytes : List UInt8} {d_cur' d_val' : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bytes cnf_ptr cnfBytes ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) d_cur' d_val' ⋆
      ((array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
        FullScratchArrays c s.scratch ⋆ c.pad) ⋆ R)) m) :
    (bytes cnf_ptr cnfBytes ⋆
      FullMem c { s with core := { s.core with d_cur := d_cur', d_val := d_val' } } ⋆ R) m := by
  have htail : hdrTailWords c { s with core := { s.core with d_cur := d_cur', d_val := d_val' } } =
      hdrTailWords c s := rfl
  have hca : FullCoreArrays c { s.core with d_cur := d_cur', d_val := d_val' } =
      FullCoreArrays c s.core := rfl
  unfold FullMem
  dsimp only
  rw [htail, hca]
  simpa only [sep_assoc] using hm

theorem fullMem_split_bytes {c : FullCfg} {s : FullState} {cnf_ptr : BitVec 64}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R) m) :
    (FullMem c s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := by
  rw [sep_comm (bytes cnf_ptr cnfBytes) (FullMem c s), sep_assoc] at hm
  exact hm

theorem fullMem_join_bytes {c : FullCfg} {s : FullState} {cnf_ptr : BitVec 64}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m) :
    (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R) m := by
  rw [← sep_assoc, sep_comm (FullMem c s) (bytes cnf_ptr cnfBytes)] at hm
  exact hm

/-! ## 2. Bitvector & Sign-Mark Arithmetic -/

theorem ing_bv32_lshr1_toNat (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  change (x >>> (1 : Nat)).toNat = x.toNat / 2
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]

theorem ing_bv32_and1_toNat (x : BitVec 32) : (x &&& 1#32).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and, show (1#32).toNat = 1 from rfl, Nat.and_one_is_mod]

theorem ing_bv32_shl1_or_and1 {iv l : BitVec 32} (hiv : iv.toNat < 2 ^ 31) :
    ((iv <<< 1#32) ||| (l &&& 1#32)).toNat = 2 * iv.toNat + l.toNat % 2 := by
  have hsh : (iv <<< 1#32).toNat = 2 * iv.toNat := by
    change (iv <<< (1 : Nat)).toNat = 2 * iv.toNat
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]
    omega
  have hand : (l &&& 1#32).toNat = l.toNat % 2 := ing_bv32_and1_toNat l
  rw [BitVec.toNat_or, hsh, hand]
  have hmod : l.toNat % 2 = 0 ∨ l.toNat % 2 = 1 := by omega
  rcases hmod with h0 | h1
  · simp [h0]
  · rw [h1]
    apply Nat.eq_of_testBit_eq
    intro i
    cases i with
    | zero => simp [Nat.testBit_zero]
    | succ j =>
      rw [Nat.testBit_or, show Nat.testBit 1 (j + 1) = false by rw [Nat.testBit_succ]; simp,
        Bool.or_false, Nat.testBit_succ, Nat.testBit_succ]
      have : (2 * iv.toNat + 1) / 2 = iv.toNat := by omega
      have : (2 * iv.toNat) / 2 = iv.toNat := by omega
      simp [*]

theorem ing_sign_mark_eq (x : BitVec 32) :
    BitVec.setWidth 8 ((x &&& 1#32) + 1#32) = if x.toNat % 2 = 0 then 1#8 else 2#8 := by
  have h1 := ing_bv32_and1_toNat x
  apply BitVec.eq_of_toNat_eq
  split <;> rename_i h
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_add, h1, h, BitVec.toNat_ofNat]
  · have hodd : x.toNat % 2 = 1 := by omega
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, h1, hodd, BitVec.toNat_ofNat]

theorem ing_sign_mark_ne_zero (x : BitVec 32) :
    BitVec.setWidth 8 ((x &&& 1#32) + 1#32) ≠ 0#8 := by
  rw [ing_sign_mark_eq]; split <;> decide

theorem ing_bv8_zext32_eq_iff (a b : BitVec 8) :
    a.setWidth 32 = b.setWidth 32 ↔ a = b := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have ht := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth] at ht
    have ha := a.isLt; have hb := b.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at ht
    exact ht
  · intro h; rw [h]

theorem ing_bv8_sext32_sgt0_iff {b : BitVec 8}
    (hd : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8) :
    (0#32 : BitVec 32).slt (b.signExtend 32) = true ↔ b = 1#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

theorem ing_bv8_sext32_eq0_iff {b : BitVec 8}
    (hd : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8) :
    b.signExtend 32 = 0#32 ↔ b = 0#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

theorem ing_bv32_ofNat_lt_of_toNat {a b : BitVec 32} (h : a.toNat < b.toNat) :
    (a + 1#32).toNat = a.toNat + 1 := by
  have hb := b.isLt
  rw [BitVec.toNat_add, show (1#32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]

/-! ## 3. Pigeonhole Lemma for `lit_mark` Deduplication -/

private theorem nodup_length_le_range {xs : List Nat} {n : Nat}
    (hnd : xs.Nodup) (hlt : ∀ x ∈ xs, x < n) : xs.length ≤ n := by
  induction n generalizing xs with
  | zero =>
    cases xs with
    | nil => simp
    | cons a _ => exact absurd (hlt a List.mem_cons_self) (by omega)
  | succ k ih =>
    by_cases hmem : k ∈ xs
    · have hlen_er := List.length_erase_of_mem hmem
      have hnd_er : (xs.erase k).Nodup := hnd.erase k
      have hlt_er : ∀ x ∈ xs.erase k, x < k := by
        intro x hx
        have hmem_x : x ∈ xs := List.mem_of_mem_erase hx
        have hne : x ≠ k := by
          intro heq; subst heq
          exact (List.Nodup.not_mem_erase hnd) hx
        have := hlt x hmem_x; omega
      have := ih hnd_er hlt_er
      omega
    · have hlt_k : ∀ x ∈ xs, x < k := by
        intro x hx
        have := hlt x hx
        have hne : x ≠ k := fun heq => hmem (heq ▸ hx)
        omega
      have := ih hnd hlt_k
      omega

theorem ing_cnt_lt_mv_of_unmarked {mv cnt ivar : Nat} {tmp : List (BitVec 32)}
    {lm : List (BitVec 8)}
    (hcnt_le : cnt ≤ tmp.length)
    (hivar : ivar < mv)
    (hunm : lm[ivar]?.getD 0#8 = 0#8)
    (hnd : ((tmp.take cnt).map fun x => x.toNat / 2).Nodup)
    (hmk : ∀ i < cnt, (tmp[i]?.getD 0#32).toNat < 2 * mv ∧
      lm[(tmp[i]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8) :
    cnt < mv := by
  let vs := (tmp.take cnt).map fun x => x.toNat / 2
  have hnotmem : ivar ∉ vs := by
    intro hmem
    simp only [vs, List.mem_map] at hmem
    obtain ⟨x, hx_take, hdiv⟩ := hmem
    rw [List.mem_iff_getElem] at hx_take
    obtain ⟨i, hi, hget⟩ := hx_take
    have hi_cnt : i < cnt := by simp [List.length_take] at hi; omega
    have hi_tmp : i < tmp.length := by omega
    have hx_eq : tmp[i]?.getD 0#32 = x := by
      rw [List.getElem?_eq_getElem hi_tmp, Option.getD_some]
      simpa [List.getElem_take] using hget
    have hne := (hmk i hi_cnt).2
    rw [hx_eq, hdiv, hunm] at hne
    exact hne rfl
  have hnd' : (ivar :: vs).Nodup := List.nodup_cons.mpr ⟨hnotmem, hnd⟩
  have hlt' : ∀ v ∈ ivar :: vs, v < mv := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hmv
    · exact hivar
    · simp only [vs, List.mem_map] at hmv
      obtain ⟨x, hx_take, rfl⟩ := hmv
      rw [List.mem_iff_getElem] at hx_take
      obtain ⟨i, hi, hget⟩ := hx_take
      have hi_cnt : i < cnt := by simp [List.length_take] at hi; omega
      have hi_tmp : i < tmp.length := by omega
      have hx_eq : tmp[i]?.getD 0#32 = x := by
        rw [List.getElem?_eq_getElem hi_tmp, Option.getD_some]
        simpa [List.getElem_take] using hget
      have := (hmk i hi_cnt).1
      rw [hx_eq] at this; omega
  have hlen := nodup_length_le_range hnd' hlt'
  have hvs_len : vs.length = cnt := by simp [vs, List.length_take, Nat.min_eq_left hcnt_le]
  simp only [List.length_cons, hvs_len] at hlen
  omega

/-! ## 4. CNF Relabeling, Entailment, and `FullWitnessInv` Helpers -/

theorem cnf_relabel_entails_mono {r : Nat → Nat} {f1 f2 : CNF Nat}
    (h : f1.Entails f2) : (CNF.relabel r f1).Entails (CNF.relabel r f2) := by
  rw [CNF.entails_def] at h ⊢
  intro a hsat
  rw [CNF.sat_def, CNF.eval_relabel, ← CNF.sat_def] at hsat ⊢
  exact h (a ∘ r) hsat

theorem cnf_relabel_entailsClause_mono {r : Nat → Nat} {f : CNF Nat} {cl : CNF.Clause Nat}
    (h : f.EntailsClause cl) : (CNF.relabel r f).EntailsClause (CNF.Clause.relabel r cl) := by
  rw [CNF.entails_clause_def] at h ⊢
  intro a hsat
  rw [CNF.sat_def, CNF.eval_relabel, ← CNF.sat_def] at hsat
  rw [CNF.Clause.sat_def, CNF.Clause.eval_relabel, ← CNF.Clause.sat_def]
  exact h (a ∘ r) hsat

theorem cnf_entails_trans {f1 f2 f3 : CNF Nat}
    (h12 : f1.Entails f2) (h23 : f2.Entails f3) : f1.Entails f3 :=
  CNF.entails_trans h12 h23

theorem cnf_entails_clause_of_entails {f1 f2 : CNF Nat} {cl : CNF.Clause Nat}
    (h12 : f1.Entails f2) (hcl : f2.EntailsClause cl) : f1.EntailsClause cl :=
  CNF.entails_clause_trans h12 hcl

theorem cnf_unsat_of_entails {f1 f2 : CNF Nat}
    (h12 : f1.Entails f2) (hu : f2.Unsat) : f1.Unsat :=
  CNF.unsat_of_entails_unsat hu h12

theorem cnfOfClauses_cons_entails {c : List Nat} {F_cur : List (List Nat)} :
    (cnfOfClauses (c :: F_cur)).Entails (cnfOfClauses F_cur) := by
  rw [CNF.entails_iff_all_mem_entails_clause]
  intro cl hcl
  apply CNF.entails_clause_of_mem
  rw [CNF.Internal.mem_iff] at hcl ⊢
  simp only [cnfOfClauses, List.mem_toArray, List.map_cons, List.mem_cons] at hcl ⊢
  exact Or.inr hcl

theorem cnf_entails_cnfOfClauses_cons {F0 : CNF Nat} {c : List Nat} {F_cur : List (List Nat)}
    (hF : F0.Entails (cnfOfClauses F_cur)) (hc : F0.EntailsClause (cnfClause c)) :
    F0.Entails (cnfOfClauses (c :: F_cur)) := by
  rw [CNF.entails_iff_all_mem_entails_clause]
  intro cl hcl
  rw [CNF.Internal.mem_iff] at hcl
  simp only [cnfOfClauses, List.mem_toArray, List.map_cons, List.mem_cons] at hcl
  rcases hcl with rfl | hmem
  · exact hc
  · apply CNF.entails_clause_trans hF
    apply CNF.entails_clause_of_mem
    rw [CNF.Internal.mem_iff]
    simpa only [cnfOfClauses, List.mem_toArray] using hmem

theorem extUnsatSound_of_entails {F0 : CNF Nat} {mv : Nat} {F_cur : List (List Nat)}
    (hvb : VarsBounded mv F_cur) (hent : F0.Entails (cnfOfClauses F_cur)) :
    ExtUnsatSound F0 mv F_cur :=
  ⟨hvb, fun hu => cnf_unsat_of_entails hent hu⟩

theorem varsBounded_cons {mv : Nat} {c : List Nat} {F_cur : List (List Nat)}
    (hc : ∀ l ∈ c, l < 2 * mv) (hF : VarsBounded mv F_cur) :
    VarsBounded mv (c :: F_cur) := by
  intro cl hcl l hl
  rcases List.mem_cons.mp hcl with rfl | hmem
  · have := hc l hl; unfold litVar; omega
  · exact hF cl hmem l hl

theorem ingest_witness_weaken_F0 {c : FullCfg} {F0 F0' : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hent : F0'.Entails F0) :
    FullWitnessInv c F0' F_cur k :=
  { hw with ext_sound := ⟨hw.ext_sound.1, fun hu => cnf_unsat_of_entails hent (hw.ext_sound.2 hu)⟩ }

theorem ingest_witness_add_clause {c : FullCfg} {F0' : CNF Nat} {F_cur : List (List Nat)}
    {cl : List Nat} {k : FullCoreState}
    (hw : FullWitnessInv c F0' F_cur k)
    (hcl_lt : ∀ l ∈ cl, l < 2 * k.cur_vars)
    (hF0_ent : F0'.Entails (cnfOfClauses F_cur))
    (hcl_ent : F0'.EntailsClause (cnfClause cl)) :
    FullWitnessInv c F0' (cl :: F_cur) k :=
  hw.replace_extSound
    (extUnsatSound_of_entails (varsBounded_cons hcl_lt hw.ext_sound.1)
      (cnf_entails_cnfOfClauses_cons hF0_ent hcl_ent))
    cnfOfClauses_cons_entails

theorem ingest_level0_false_entails_neg {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {l : Nat} (hl : l < 2 * k.cur_vars) (hvf : k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg l]) := by
  obtain ⟨i, hi_lt, hi_eq⟩ := (hw.vals_false_iff l hl).mp hvf
  have hlvl0 : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le i hi_lt; omega
  have hent := hw.level0_sound i hi_lt hlvl0
  rwa [hi_eq] at hent

theorem ingest_unsat_of_all_false {c : FullCfg} {tum : Bool} {accCnf : CNF Nat}
    {cl : CNF.Clause Nat} {F_cur : List (List Nat)} {s : FullState}
    {next : Nat} {lits : List Nat}
    (hcl_eq : cl = CNF.Clause.ofLiterals (lits.map kissatLitToDimacsLiteral))
    (hcv : s.core.cur_vars = c.mv) (hcl0 : s.core.cur_level = 0)
    (htm : TumbleInv tum c.mv next s.core.frame_dec)
    (hcov : TumbleCovers tum s.core.frame_dec (shiftDownCnf (accCnf.add cl)))
    (hvb : CnfVarsLt c.mv (shiftDownCnf (accCnf.add cl)))
    (hw : FullWitnessInv c
      (CNF.relabel (tumblePi tum s.core.frame_dec) (shiftDownCnf accCnf)) F_cur s.core)
    (hent : (CNF.relabel (tumblePi tum s.core.frame_dec) (shiftDownCnf accCnf)).Entails
      (cnfOfClauses F_cur))
    (hall : ∀ l ∈ lits,
      let tl := tumbleLit tum s.core.frame_dec l
      tl < 2 * c.mv ∧ s.core.vals[tl]?.getD 0#8 = 0xFF#8) :
    (shiftDownCnf (accCnf.add cl)).Unsat := by
  let π := tumblePi tum s.core.frame_dec
  let F0' := CNF.relabel π (shiftDownCnf (accCnf.add cl))
  have hF0'_F0 : F0'.Entails (CNF.relabel π (shiftDownCnf accCnf)) :=
    cnf_relabel_entails_mono (shiftDownCnf_entails_add accCnf cl)
  have hF0'_cl : F0'.EntailsClause (cnfClause (lits.map (tumbleLit tum s.core.frame_dec))) := by
    have h1 := cnf_relabel_entailsClause_mono (r := π) (shiftDownCnf_entails_added accCnf cl)
    have hcl_rel : CNF.Clause.relabel π (shiftDownClause cl) =
        cnfClause (lits.map (tumbleLit tum s.core.frame_dec)) := by
      rw [hcl_eq]; exact cnfClause_relabel_eq
    rwa [hcl_rel] at h1
  have hnil : F0'.EntailsClause (cnfClause []) := by
    refine entails_of_mem_or_false hF0'_cl fun tl htl => Or.inr ?_
    rw [List.mem_map] at htl
    obtain ⟨l, hl, rfl⟩ := htl
    obtain ⟨htl_lt, hvf⟩ := hall l hl
    have hF_neg := ingest_level0_false_entails_neg hw hcl0 (hcv ▸ htl_lt) hvf
    exact cnf_entails_clause_of_entails (cnf_entails_trans hF0'_F0 hent) hF_neg
  exact cnf_unsat_of_relabel_tumble htm hcov hvb (unsat_of_entails_nil hnil)

/-! ## 5. Preservation Helpers for Loop 0 (`frame_dec`/`extend_len`/`d_cur`/`lit_mark`/`tmp`) -/

theorem ingest_witness_with_fd_dcur_mrk_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {d_cur' d_val' : BitVec 64} {fd' tmp' : List (BitVec 32)} {mrk' : List (BitVec 8)} :
    FullWitnessInv c F0 F_cur
      { k with d_cur := d_cur', d_val := d_val', frame_dec := fd', mrk := mrk', tmp := tmp' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
    frame_dec_lt := fun L hL1 hLle => by change L ≤ k.cur_level at hLle; omega }

/-! ## 6. Level-0 Unit Assignment Preservation for `FullSparseInvW` -/

theorem ingest_sparseInvW_assign_level0 {c : FullCfg} {F0' : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {lit : BitVec 32} {flags' : List (BitVec 32)}
    {unass' : BitVec 64} {phases' : List (BitVec 8)}
    (hsp : FullSparseInvW c F0' F_cur s)
    (hcl0 : s.core.cur_level = 0)
    (hlit : lit.toNat < 2 * s.core.cur_vars)
    (hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hent_lit : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hfl : flags'.length = c.max_vars) (hph : phases'.length = c.max_vars) :
    let v := lit.toNat / 2
    let s' : FullState :=
      { core := { s.core with
          unassigned := unass',
          unflushed := s.core.unflushed + 1#64,
          trail_end := s.core.trail_end + 1,
          vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8,
          flags := flags',
          lvl := s.core.lvl.set v 0#32,
          rsns := s.core.rsns.set v 0xFFFFFFFF#32,
          trl := s.core.trl.set s.core.trail_end lit,
          trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end) }
        scratch := { s.scratch with phases := phases' } }
    FullSparseInvW c F0' F_cur s' := by
  intro v s'
  have hok := hsp.1.core_ok
  have hsok := hsp.1.scratch_ok
  have hw := hsp.2.1
  have hte_lt : s.core.trail_end < s.core.cur_vars :=
    hw.trail_end_lt_of_unassigned hlit hun
  have hv_lt_cv : v < s.core.cur_vars := by omega
  have hv_lt_mx : v < c.max_vars := by have := hok.cur_vars_le; omega
  have hte_lt_mx : s.core.trail_end < c.max_vars := by have := hok.cur_vars_le; omega
  have hln_lt : lit.toNat ^^^ 1 < 2 * s.core.cur_vars := litNeg_lt_two_mul hlit
  have hln_ne : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hvals_len : 2 * s.core.cur_vars ≤ s.core.vals.length := by
    rw [hok.vals_len]; have := hok.cur_vars_le; omega
  have htrl_len : s.core.trail_end < s.core.trl.length := by rw [hok.trl_len]; omega
  have hlvl_len : v < s.core.lvl.length := by rw [hok.lvl_len]; omega
  have hrsns_len : v < s.core.rsns.length := by rw [hok.rsns_len]; omega
  have htp_len : v < s.core.trail_pos.length := by rw [hok.trail_pos_len]; omega
  have hnot_on_trail : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hw.vals_zero_iff hlit).mp hun
  have hlen' : s'.LengthsOk c := by
    refine ⟨{ hok with
      vals_len := by dsimp only [s']; rw [List.length_set, List.length_set, hok.vals_len],
      flags_len := hfl,
      lvl_len := by dsimp only [s']; rw [List.length_set, hok.lvl_len],
      rsns_len := by dsimp only [s']; rw [List.length_set, hok.rsns_len],
      trl_len := by dsimp only [s']; rw [List.length_set, hok.trl_len],
      trail_pos_len := by dsimp only [s']; rw [List.length_set, hok.trail_pos_len],
      trail_end_le := by dsimp only [s']; omega,
      propagated_le := by dsimp only [s']; have := hok.propagated_le; omega },
      { hsok with phases_len := hph }⟩
  have htrl_get : ∀ i < s.core.trail_end + 1,
      (s'.core.trl[i]?.getD 0#32).toNat =
        if i = s.core.trail_end then lit.toNat else (s.core.trl[i]?.getD 0#32).toNat := by
    intro i hi
    dsimp only [s']
    by_cases he : i = s.core.trail_end
    · subst he; rw [List.getElem?_set_self htrl_len]; simp
    · rw [List.getElem?_set_ne (Ne.symm he)]; simp [he]
  have hlvl_all0 : ∀ i < s.core.trail_end + 1,
      (s'.core.lvl[(s'.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    intro i hi
    rw [htrl_get i hi]
    dsimp only [s']
    split <;> rename_i he
    · rw [List.getElem?_set_self hlvl_len]; simp
    · have hi' : i < s.core.trail_end := by omega
      have hne : v ≠ (s.core.trl[i]?.getD 0#32).toNat / 2 := Ne.symm (hnot_on_trail i hi')
      rw [List.getElem?_set_ne hne]
      have := hw.lvl_le i hi'; omega
  have hrsns_allff : ∀ i < s.core.trail_end + 1,
      s'.core.rsns[(s'.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
    intro i hi
    rw [htrl_get i hi]
    dsimp only [s']
    split <;> rename_i he
    · rw [List.getElem?_set_self hrsns_len]; simp
    · have hi' : i < s.core.trail_end := by omega
      have hne : v ≠ (s.core.trl[i]?.getD 0#32).toNat / 2 := Ne.symm (hnot_on_trail i hi')
      rw [List.getElem?_set_ne hne]
      have hl0 : (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
        have := hw.lvl_le i hi'; omega
      exact hw.level0_rsn_none i hi' hl0
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hte' : s'.core.trail_end = s.core.trail_end + 1 := rfl
  have hcv' : s'.core.cur_vars = s.core.cur_vars := rfl
  have hw' : FullWitnessInv c F0' F_cur s'.core :=
    { ext_sound := hw.ext_sound
      inconsistent_sound := hw.inconsistent_sound
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
      cur_level_le := by dsimp only [s']; omega
      trail_lits_lt := fun i hi => by
        rw [htrl_get i hi]; split <;> rename_i he
        · exact hlit
        · exact hw.trail_lits_lt i (by omega)
      trail_vars_nodup := fun i j hi hj hdiv => by
        rw [htrl_get i hi, htrl_get j hj] at hdiv
        by_cases hei : i = s.core.trail_end <;> by_cases hej : j = s.core.trail_end
        · omega
        · simp only [hei, hej, ↓reduceIte] at hdiv
          exact absurd hdiv.symm (hnot_on_trail j (by omega))
        · simp only [hei, hej, ↓reduceIte] at hdiv
          exact absurd hdiv (hnot_on_trail i (by omega))
        · simp only [hei, hej, ↓reduceIte] at hdiv
          exact hw.trail_vars_nodup i j (by omega) (by omega) hdiv
      vals_domain := fun l hl => by
        dsimp only [s']
        by_cases h1 : l = lit.toNat ^^^ 1
        · subst h1; rw [List.getElem?_set_self (by simp; omega)]; right; right; rfl
        · rw [List.getElem?_set_ne (Ne.symm h1)]
          by_cases h2 : l = lit.toNat
          · subst h2; rw [List.getElem?_set_self (by omega)]; right; left; rfl
          · rw [List.getElem?_set_ne (Ne.symm h2)]; exact hw.vals_domain l hl
      vals_true_iff := fun l hl => by
        constructor
        · intro h1
          dsimp only [s'] at h1
          by_cases hln : l = lit.toNat ^^^ 1
          · subst hln; rw [List.getElem?_set_self (by simp; omega)] at h1; cases h1
          · rw [List.getElem?_set_ne (Ne.symm hln)] at h1
            by_cases hl0 : l = lit.toNat
            · exact ⟨s.core.trail_end, by dsimp only [s']; omega, by
                rw [htrl_get s.core.trail_end (by omega)]; simp [hl0]⟩
            · rw [List.getElem?_set_ne (Ne.symm hl0)] at h1
              obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
              exact ⟨i, by dsimp only [s']; omega, by
                rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
        · rintro ⟨i, hi, heq⟩
          rw [htrl_get i hi] at heq
          dsimp only [s']
          by_cases hei : i = s.core.trail_end
          · simp only [hei, ↓reduceIte] at heq
            rw [← heq, List.getElem?_set_ne hln_ne, List.getElem?_set_self (by omega)]; rfl
          · simp only [hei, ↓reduceIte] at heq
            have hi' : i < s.core.trail_end := by omega
            have hne_v : l / 2 ≠ v := by rw [← heq]; exact hnot_on_trail i hi'
            have hne1 : lit.toNat ^^^ 1 ≠ l := by
              intro h; rw [← h, tum_nat_xor1_div2] at hne_v; exact hne_v rfl
            have hne2 : lit.toNat ≠ l := fun h => hne_v (by rw [← h])
            rw [List.getElem?_set_ne hne1, List.getElem?_set_ne hne2]
            exact (hw.vals_true_iff l hl).mpr ⟨i, hi', heq⟩
      vals_false_iff := fun l hl => by
        constructor
        · intro h1
          dsimp only [s'] at h1
          by_cases hln : l = lit.toNat ^^^ 1
          · exact ⟨s.core.trail_end, by dsimp only [s']; omega, by
              rw [htrl_get s.core.trail_end (by omega)]; simp [hln, Nat.xor_assoc]⟩
          · rw [List.getElem?_set_ne (Ne.symm hln)] at h1
            by_cases hl0 : l = lit.toNat
            · subst hl0; rw [List.getElem?_set_self (by omega)] at h1; cases h1
            · rw [List.getElem?_set_ne (Ne.symm hl0)] at h1
              obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h1
              exact ⟨i, by dsimp only [s']; omega, by
                rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
        · rintro ⟨i, hi, heq⟩
          rw [htrl_get i hi] at heq
          dsimp only [s']
          by_cases hei : i = s.core.trail_end
          · simp only [hei, ↓reduceIte] at heq
            have hle : l = lit.toNat ^^^ 1 := by
              have := congrArg (· ^^^ 1) heq
              simpa [Nat.xor_assoc] using this.symm
            rw [hle, List.getElem?_set_self (by simp; omega)]; rfl
          · simp only [hei, ↓reduceIte] at heq
            have hi' : i < s.core.trail_end := by omega
            have hne_v : l / 2 ≠ v := by
              have hdiv := congrArg (· / 2) heq
              rw [tum_nat_xor1_div2] at hdiv
              rw [← hdiv]; exact hnot_on_trail i hi'
            have hne1 : lit.toNat ^^^ 1 ≠ l := by
              intro h; rw [← h, tum_nat_xor1_div2] at hne_v; exact hne_v rfl
            have hne2 : lit.toNat ≠ l := fun h => hne_v (by rw [← h])
            rw [List.getElem?_set_ne hne1, List.getElem?_set_ne hne2]
            exact (hw.vals_false_iff l hl).mpr ⟨i, hi', heq⟩
      lvl_le := fun i hi => by rw [hlvl_all0 i hi]; omega
      dec_earliest := fun i j hi hj _ hpos => by
        rw [hlvl_all0 j hj] at hpos; omega
      levels_inhabited := fun L hL1 hLle => by dsimp only [s'] at hLle; omega
      level0_sound := fun i hi _ => by
        rw [htrl_get i hi]
        split <;> rename_i he
        · exact hent_lit
        · have hi' : i < s.core.trail_end := by omega
          exact hw.level0_sound i hi' (by have := hw.lvl_le i hi'; omega)
      trail_pos_inv := fun i hi => by
        rw [htrl_get i hi]; dsimp only [s']
        split <;> rename_i he
        · rw [List.getElem?_set_self htp_len]; simp [BitVec.toNat_ofNat, he]
          omega
        · have hi' : i < s.core.trail_end := by omega
          have hne : v ≠ (s.core.trl[i]?.getD 0#32).toNat / 2 := Ne.symm (hnot_on_trail i hi')
          rw [List.getElem?_set_ne hne]
          exact hw.trail_pos_inv i hi'
      level0_rsn_none := fun i hi _ => hrsns_allff i hi
      frame_trail_lt := fun L hL => by
        dsimp only [s'] at hL ⊢; have := hw.frame_trail_lt L hL; omega
      frame_trail_mono := hw.frame_trail_mono
      frame_trail_before_lt := fun L hL1 hLle => by dsimp only [s'] at hLle; omega
      frame_dec_lt := fun L hL1 hLle => by dsimp only [s'] at hLle; omega
      reason_inv := fun idx hidx hrsn => absurd (hrsns_allff idx hidx) hrsn
      reason_lit_mem := fun idx hidx hrsn => absurd (hrsns_allff idx hidx) hrsn }
  exact ⟨hlen', hw', hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

end LeanQbe.T.Examples.Kissat.Proof.Parse
