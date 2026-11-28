/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Search.Wp1

/-!
# Verification of `kissat_solve_bytes_seeded` and `kissat_solve_bytes` (`Proof.Search.Wp2`)

Proves `kissat_solve_bytes_seeded_wp` (`Spec.fullM6SolveBytesSeededSpec`) and
`kissat_solve_bytes_wp` (`Proof.Spec.fullM6SolveBytesCoreModelSpec`) in `CanonicalEnv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Search

open Std Std.Sat Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src LeanQbe.T.Examples.Kissat.Src.Search
open LeanQbe.T.Examples.Kissat.Proof LeanQbe.T.Examples.Kissat.Proof.Spec

/-! ## 1. Alignment, Byte Array, and DIMACS Parser Bridges -/

private theorem fullAlignPad_lt8 (p : BitVec 64) : fullAlignPad p < 8 := by
  unfold fullAlignPad
  split <;> omega

private theorem align_pad_bv_eq (p : Val i64) :
    (((8 - (p &&& 7)) &&& 7 : Val i64)) = BitVec.ofNat 64 (fullAlignPad p) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (p &&& 7#64).toNat = p.toNat % 8 := by
    have h7 : (7#64 : BitVec 64).toNat = 2 ^ 3 - 1 := rfl
    rw [BitVec.toNat_and, h7, Nat.and_two_pow_sub_one_eq_mod]
  have h2 : (8#64 - (p &&& 7#64)).toNat = 8 - p.toNat % 8 := by
    rw [BitVec.toNat_sub, h1]
    have : p.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
    have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
    rw [h8]; omega
  have h3 : (((8#64 - (p &&& 7#64)) &&& 7#64)).toNat = (8 - p.toNat % 8) % 8 := by
    have h7 : (7#64 : BitVec 64).toNat = 2 ^ 3 - 1 := rfl
    rw [BitVec.toNat_and, h2, h7, Nat.and_two_pow_sub_one_eq_mod]
  change (((8#64 - (p &&& 7#64)) &&& 7#64)).toNat = (BitVec.ofNat 64 (fullAlignPad p)).toNat
  rw [h3, BitVec.toNat_ofNat]
  unfold fullAlignPad
  split <;> omega

private theorem bv_sub_not0_le {p : BitVec 64} {n : Nat} (h : p.toNat + n < 2 ^ 64) :
    BitVec.ofNat 64 n ≤ ~~~0#64 - p := by
  rw [BitVec.le_def]
  have hmax : (~~~(0#64 : BitVec 64)).toNat = 2 ^ 64 - 1 := by decide
  rw [BitVec.toNat_sub, hmax, BitVec.toNat_ofNat]
  have hp : p.toNat < 2 ^ 64 := p.isLt
  omega

private theorem int_toBytes1_bv8 (v : BitVec 8) :
    Int.toBytes i8.bytes (BitVec.setWidth (8 * i8.bytes) (toBits i8 v)).toInt =
      [UInt8.ofBitVec v] := by
  change Int.toBytes 1 v.toInt = [UInt8.ofBitVec v]
  rw [Int.toBytes.eq_2, Int.toBytes.eq_1]
  congr 1
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  simp [Int.take, BitVec.toInt]
  have hv := v.isLt
  split <;> omega

private theorem bytesOf_i8 (xs : List (BitVec 8)) :
    bytesOf (t := i8) xs = xs.map UInt8.ofBitVec := by
  induction xs with
  | nil => rfl
  | cons v vs ih =>
    unfold bytesOf at ih ⊢
    rw [List.flatMap_cons, List.map_cons, int_toBytes1_bv8, ih]
    rfl

private theorem array_i8_to_bytes {a : BitVec 64} {xs : List (BitVec 8)}
    (hlen : xs.length ≤ 2 ^ 64) {m : Mem 64} (h : array (t := i8) a xs m) :
    bytes a (xs.map UInt8.ofBitVec) m := by
  have hm := array_eq_bytesOf (t := i8) a xs (by change 1 * xs.length ≤ 2 ^ 64; omega) h
  rw [bytesOf_i8] at hm
  exact hm.symm

private theorem parseClauseAux_vars_pos : ∀ (fuel mv : Nat) (acc : List (Literal Nat))
    (bs : List UInt8) (cl : CNF.Clause Nat) (rest : List UInt8),
    (∀ l ∈ acc, 1 ≤ l.1) →
    Ref.parseClauseAux fuel mv acc bs = some (cl, rest) →
    ∀ l ∈ cl.literals, 1 ≤ l.1 := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ h; cases h
  | succ k ih =>
    intro mv acc bs cl rest hacc h
    rw [Ref.parseClauseAux.eq_2] at h
    cases hsk : Ref.skipWsComments bs with
    | nil => simp [hsk] at h
    | cons b bs1 =>
      simp only [hsk] at h
      by_cases hb : b = 45
      · subst hb
        cases hpn : Ref.parseNat bs1 with
        | none => simp [hpn] at h
        | some vr =>
          rcases vr with ⟨v, r1⟩
          simp only [hpn] at h
          split at h
          · rename_i hcnd
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hcnd
            exact ih mv ((v, false) :: acc) r1 cl rest
              (fun l hl => by
                rcases List.mem_cons.mp hl with rfl | hl'
                · exact hcnd.1
                · exact hacc l hl') h
          · cases h
      · have hne : ∀ rest', b :: bs1 ≠ 45 :: rest' := fun _ heq => hb (List.cons.inj heq).1
        split at h
        · cases h
        · rename_i heq
          exact absurd heq (hne _)
        · rename_i heq
          obtain ⟨rfl, rfl⟩ := List.cons.inj heq
          cases hpn : Ref.parseNat (b :: bs1) with
          | none => simp [hpn] at h
          | some vr =>
            rcases vr with ⟨v, r1⟩
            rw [hpn] at h
            cases v with
            | zero =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, _⟩
              intro l hl
              rw [Std.Sat.CNF.Clause.literals_ofLiterals] at hl
              exact hacc l (List.mem_reverse.mp hl)
            | succ v' =>
              simp only at h
              split at h
              · exact ih mv ((v' + 1, true) :: acc) r1 cl rest
                  (fun l hl => by
                    rcases List.mem_cons.mp hl with rfl | hl'
                    · omega
                    · exact hacc l hl') h
              · cases h

private theorem parseClauses_vars_pos : ∀ (nc mv : Nat) (cnf0 : CNF Nat) (bs : List UInt8)
    (cnf : CNF Nat), Ref.CnfVarsPos cnf0 →
    Ref.parseClauses mv nc cnf0 bs = some cnf → Ref.CnfVarsPos cnf := by
  intro nc
  induction nc with
  | zero =>
    intro mv cnf0 bs cnf h0 h
    rw [Ref.parseClauses.eq_1] at h
    split at h
    · cases h; exact h0
    · cases h
  | succ k ih =>
    intro mv cnf0 bs cnf h0 h
    rw [Ref.parseClauses.eq_2] at h
    cases hpc : Ref.parseClause mv bs with
    | none => simp [hpc] at h
    | some cr =>
      rcases cr with ⟨cl, bs'⟩
      simp only [hpc, Bind.bind, Option.bind] at h
      have hcl : ∀ l ∈ cl.literals, 1 ≤ l.1 :=
        parseClauseAux_vars_pos (bs.length + 1) mv [] bs cl bs' (fun _ hl => by cases hl) hpc
      exact ih mv (cnf0.add cl) bs' cnf (Ref.cnfVarsPos_add h0 hcl) h

private theorem parseDimacs_cnfVarsPos {bs : List UInt8} {cnf : CNF Nat}
    (h : Ref.parseDimacs bs = some cnf) : Ref.CnfVarsPos cnf := by
  unfold Ref.parseDimacs at h
  cases hh : Ref.parseHeader bs with
  | none => simp [hh] at h
  | some t =>
    rcases t with ⟨mv, nc, rest⟩
    simp only [hh, Bind.bind, Option.bind] at h
    exact parseClauses_vars_pos nc mv Std.Sat.CNF.empty rest cnf Ref.cnfVarsPos_empty h

private theorem fullFixedBytes_ge_1472 (mv : Nat) : 1472 ≤ fullFixedBytes mv := by
  unfold fullFixedBytes; omega

private theorem cfg_pVals_eq_of_compat {c0 c1 : FullCfg} (hc : FullCfgCompat c0 c1) :
    c1.pVals = c0.pVals := by
  unfold FullCfg.pVals; rw [hc.hdr]

private theorem fullM6HdrMem_load_mv {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    loadVal m i64 c.hdr = some (BitVec.ofNat 64 c.mv) := by
  have hm1 := fullM6HdrMem_focus_full hm
  have hm2 : (array64 c.hdr
      [BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc, s.core.d_cur, s.core.d_val] ⋆
      (array64 (c.hdr + 32#64) (hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
        FullScratchArrays c s.scratch ⋆ c.pad ⋆ m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m := by
    unfold FullMem dimacsState at hm1
    exact sep_cast hm1 (by ac_rfl)
  exact c0_load_array64_zero hm2 (by simp)

/-! ## 2. `L30` SAT Extension & Model Check Tail -/

private abbrev solveBytesL30Expr (cnf_ptr cend h mv0 r : Val i64) : Expr Val Cont [i64] :=
  .let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var r, Arg.imm 10, ())) fun p25 =>
    .jnz (Arg.var p25.fst)
      (.call (as := [i64]) (bs := []) "full_extend" (Arg.var h, ()) fun _ =>
        .store (t := i64) (Arg.var mv0) (Arg.var h)
          (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 768)) fun p27 =>
            .load i64 (Arg.var p27.fst) fun ld1 =>
              .let_ (op2 (.sub i64) (Arg.var ld1) (Arg.var mv0)) fun p28 =>
                .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 784)) fun p29 =>
                  .store (t := i64) (Arg.var p28.fst) (Arg.var p29.fst)
                    (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 64)) fun p30 =>
                      .load i64 (Arg.var p30.fst) fun ld2 =>
                        .call (as := [i64, i64, i64, i64, i64]) (bs := [i64]) "kissat_check_model"
                          (Arg.var cnf_ptr, Arg.var cend, Arg.var h,
                            Arg.var ld2, Arg.var mv0, ()) fun p =>
                          .group (sig := [[i64]])
                            (fun _ => Blocks.cons (fun p => .ret (Arg.var p.fst, ())) .nil)
                            (fun Js =>
                              .let_ (Op.mk (.cmp .eq i64 .bool rfl)
                                (Arg.var p.fst, Arg.imm 1, ())) fun p =>
                                .jnz (Arg.var p.fst) (.jump Js.fst (Arg.imm 10, ()))
                                  (.jump Js.fst (Arg.imm 0, ()))))))
      (.ret (Arg.var r, ()))

private theorem solve_bytes_l30_wp {Γ : Env} (hΓ : Γ.Sat Spec.deps)
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat} {R : Mem 64 → Prop}
    {c0 c1 : FullCfg} {ext1 : List (BitVec 64)} {s1 : FullState} {cnf : CNF Nat} {r : BitVec 64}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hfit_cnf : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hfit_w : fullAlignPad work_ptr + Src.fullM6HdrTotalBytes ≤ wlen)
    (hwlen : wlen ≤ 2 ^ 64)
    (hhdr0 : c0.hdr = fullM6WorkHdr work_ptr)
    (havail0 : c0.avail = wlen - fullAlignPad work_ptr - Src.fullM6ExtBytes)
    (hparse : Ref.parseDimacs cnfBytes = some cnf)
    (hc1 : FullCfgCompat c0 c1) (hlen1 : s1.LengthsOk c1) (hcfg1 : FullM6HdrCfgOk c1)
    (hext1 : M6HdrExtOk ext1) (hr : r = 0#64 ∨ r = 10#64 ∨ r = 20#64)
    (h20 : r = 20#64 → (Ref.shiftDownCnf cnf).Unsat)
    (h10 : r = 10#64 → s1.scratch.extend_len ≤ c1.extend_cap)
    (hm : (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c1 ext1 s1 ⋆
      region work_ptr (fullAlignPad work_ptr) ⋆ R) m)
    (hk : ∀ r' m', (r' = 0#64 ∨ r' = 10#64 ∨ r' = 20#64) →
      (r' = 20#64 → ∃ cnf', Ref.parseDimacs cnfBytes = some cnf' ∧ cnf'.Unsat) →
      (r' = 10#64 → ∃ cnf', Ref.parseDimacs cnfBytes = some cnf' ∧
        ∀ (F : Mem 64 → Prop) (M : Mem 64), (Eq m' ⋆ F) M →
          CNF.Sat (readModelFromWorkM6 M work_ptr) cnf') →
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' → Q (r', ()) m') :
    wp Γ Q X (solveBytesL30Expr cnf_ptr (cnf_ptr + BitVec.ofNat 64 cnfBytes.length)
      c0.hdr (BitVec.ofNat 64 c0.mv) r) m := by
  dsimp only [solveBytesL30Expr]
  c0_hstraight
  refine jnz_bv_eq rfl (fun eq10 => ?_) (fun ne10 => ?_)
  · have hm_ext0 : (FullM6HdrMem c1 ext1 s1 ⋆
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m :=
      sep_cast hm (by ac_rfl)
    refine search_call_extend (by simp [vals, hc1.hdr]) (deps_has_extend hΓ)
      hlen1 (h10 eq10) hm_ext0 fun s2 m2 hlen2 hm2 => ?_
    have hm2_f : (FullMem c1 s2 ⋆ (array64 (c1.hdr - 2304#64) ext1 ⋆
        bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m2 := by
      have ht := (fullM6HdrMem_iff_ext c1 ext1 s2 _ m2).mp hm2
      exact sep_cast ht (by ac_rfl)
    have ⟨hok_mv, hm_mv⟩ := full_store_mv_mid (BitVec.ofNat 64 c0.mv) hm2_f
    rw [wp_store]; refine ⟨hc1.hdr.symm ▸ hok_mv, ?_⟩
    c0_hstraight
    dsimp only [Arg.val]
    have hst1 : storeMem m2 i64 c0.hdr (BitVec.ofNat 64 c0.mv) =
        storeMem m2 i64 c1.hdr (BitVec.ofNat 64 c0.mv) := by rw [hc1.hdr]
    rw [hst1]
    have hld_mv : loadVal (storeMem m2 i64 c1.hdr (BitVec.ofNat 64 c0.mv)) i64
        (c0.hdr + 768#64) = some (BitVec.ofNat 64 c1.max_vars) := by
      rw [← hc1.hdr]
      exact search_sat_load_max_vars _ s2 _ _ hm_mv
    rw [wp_load]; refine ⟨_, hld_mv, ?_⟩
    c0_hstraight
    have hbva_eq : BitVec.ofNat 64 c1.max_vars - BitVec.ofNat 64 c0.mv =
        BitVec.ofNat 64 c0.bva_cap := by
      apply BitVec.eq_of_toNat_eq
      have hmax : c1.max_vars = c0.mv + c0.bva_cap := hc1.max_vars.trans c0.hbva
      have hlt_max : c1.max_vars < 2 ^ 64 := by
        have := c1.hmaxv; unfold Ref.dimacsBound at this; omega
      have hlt_mv : c0.mv < 2 ^ 64 := by omega
      have hlt_bva : c0.bva_cap < 2 ^ 64 := by omega
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    have ⟨hok_bva, hm_bva⟩ := search_sat_store_bva s2 _ _ hc1 hm_mv
    rw [wp_store]; refine ⟨hc1.hdr.symm ▸ hok_bva, ?_⟩
    dsimp only [Arg.val]
    rw [hbva_eq]
    have hst2 : storeMem (storeMem m2 i64 c1.hdr (BitVec.ofNat 64 c0.mv)) i64
        (c0.hdr + 784 : Val i64) (BitVec.ofNat 64 c0.bva_cap) =
        storeMem (storeMem m2 i64 c1.hdr (BitVec.ofNat 64 c0.mv)) i64
        (c1.hdr + 784#64) (BitVec.ofNat 64 c0.bva_cap) := by rw [hc1.hdr]; rfl
    rw [hst2]
    c0_hstraight
    have hm_tw : (array64 (c0.hdr + 32#64) (hdrTailWords c0 s2) ⋆
        (dimacsState c0.hdr (BitVec.ofNat 64 c0.mv) (BitVec.ofNat 64 c0.nc)
          s2.core.d_cur s2.core.d_val ⋆ FullCoreArrays c1 s2.core ⋆
          FullScratchArrays c1 s2.scratch ⋆ c1.pad ⋆ array64 (c1.hdr - 2304#64) ext1 ⋆
          bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) _ :=
      sep_cast hm_bva (by ac_rfl)
    rw [wp_load]; refine ⟨_, search_sat_load_pVals (c0 := c0) s2 _ _ hm_tw, ?_⟩
    have hvals_len_raw : s2.core.vals.length = 2 * c0.max_vars := by
      rw [hlen2.core_ok.vals_len, hc1.max_vars]
    have hvals_raw_le : s2.core.vals.length ≤ 2 ^ 64 := by
      rw [hvals_len_raw]; have := c0.hmaxv; unfold Ref.dimacsBound at this; omega
    have hm_chk_in : (bytes cnf_ptr cnfBytes ⋆
        dimacsState c0.hdr (BitVec.ofNat 64 c0.mv) (BitVec.ofNat 64 c0.nc)
          s2.core.d_cur s2.core.d_val ⋆
        bytes c0.pVals (s2.core.vals.map UInt8.ofBitVec) ⋆
        (array64 (c0.hdr + 32#64) (hdrTailWords c0 s2) ⋆
          array (t := i8) c1.pLitMark s2.core.lit_mark ⋆
          array (t := i8) c1.pMark s2.core.mrk ⋆
          FullCoreU32A c1 s2.core ⋆ FullCoreU32B c1 s2.core ⋆ FullCoreDynArrs c1 s2.core ⋆
          FullScratchArrays c1 s2.scratch ⋆ c1.pad ⋆ array64 (c1.hdr - 2304#64) ext1 ⋆
          region work_ptr (fullAlignPad work_ptr) ⋆ R))
        (storeMem (storeMem m2 i64 c1.hdr (BitVec.ofNat 64 c0.mv)) i64
          (c1.hdr + 784#64) (BitVec.ofNat 64 c0.bva_cap)) := by
      unfold FullCoreArrays FullCoreByteArrs at hm_bva
      rw [cfg_pVals_eq_of_compat hc1] at hm_bva
      have h_arr : (array (t := i8) c0.pVals s2.core.vals ⋆
          (bytes cnf_ptr cnfBytes ⋆
            dimacsState c0.hdr (BitVec.ofNat 64 c0.mv) (BitVec.ofNat 64 c0.nc)
              s2.core.d_cur s2.core.d_val ⋆
            array64 (c0.hdr + 32#64) (hdrTailWords c0 s2) ⋆
            array (t := i8) c1.pLitMark s2.core.lit_mark ⋆
            array (t := i8) c1.pMark s2.core.mrk ⋆
            FullCoreU32A c1 s2.core ⋆ FullCoreU32B c1 s2.core ⋆ FullCoreDynArrs c1 s2.core ⋆
            FullScratchArrays c1 s2.scratch ⋆ c1.pad ⋆ array64 (c1.hdr - 2304#64) ext1 ⋆
            region work_ptr (fullAlignPad work_ptr) ⋆ R)) _ := sep_cast hm_bva (by ac_rfl)
      have h_byt := sep_mono (fun _ ha => array_i8_to_bytes hvals_raw_le ha) h_arr
      have h_byt' : (bytes c0.pVals (s2.core.vals.map UInt8.ofBitVec) ⋆
          (bytes cnf_ptr cnfBytes ⋆
            dimacsState c0.hdr (BitVec.ofNat 64 c0.mv) (BitVec.ofNat 64 c0.nc)
              s2.core.d_cur s2.core.d_val ⋆
            array64 (c0.hdr + 32#64) (hdrTailWords c0 s2) ⋆
            array (t := i8) c1.pLitMark s2.core.lit_mark ⋆
            array (t := i8) c1.pMark s2.core.mrk ⋆
            FullCoreU32A c1 s2.core ⋆ FullCoreU32B c1 s2.core ⋆ FullCoreDynArrs c1 s2.core ⋆
            FullScratchArrays c1 s2.scratch ⋆ c1.pad ⋆ array64 (c1.hdr - 2304#64) ext1 ⋆
            region work_ptr (fullAlignPad work_ptr) ⋆ R))
          (storeMem (storeMem m2 i64 c1.hdr (BitVec.ofNat 64 c0.mv)) i64
            (c1.hdr + 784#64) (BitVec.ofNat 64 c0.bva_cap)) := h_byt
      exact sep_cast h_byt' (by ac_rfl)
    refine wp_call_of_spec _ _ (deps_has_check_model hΓ _ _ _ _ ?_)
    dsimp only [vals, Arg.val]; unfold kissatCheckModelExactSpec
    have hmv_lt : c0.mv < 2 ^ 64 := by
      have := c0.hmv; unfold Ref.dimacsBound at this; omega
    have hvals_len : (s2.core.vals.map UInt8.ofBitVec).length = 2 * c0.max_vars := by
      rw [List.length_map, hvals_len_raw]
    have hvals_ge : 2 * c0.mv ≤ (s2.core.vals.map UInt8.ofBitVec).length := by
      rw [hvals_len, c0.hbva]; omega
    have hvals_le : (s2.core.vals.map UInt8.ofBitVec).length ≤ 2 ^ 64 := by
      rw [hvals_len]; have := c0.hmaxv; unfold Ref.dimacsBound at this; omega
    refine ⟨BitVec.ofNat 64 c0.mv, BitVec.ofNat 64 c0.nc, s2.core.d_cur, s2.core.d_val,
      cnfBytes, s2.core.vals.map UInt8.ofBitVec, c0.mv, _, rfl, rfl, hfit_cnf, hmv_lt,
      hvals_ge, hvals_le, hm_chk_in, ?_⟩
    intro rc mv' nc' cur' val' m_chk hrc hm_chk
    have hm_reg : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m_chk :=
      search_sat_post_to_region hfit_w hwlen hhdr0 havail0 hext1 hc1 hlen2
        (sep_cast hm_chk (by ac_rfl))
    have hm_mod : (array64 (c0.hdr + 32#64) (hdrTailWords c0 s2) ⋆
        bytes c0.pVals (s2.core.vals.map UInt8.ofBitVec) ⋆
        (bytes cnf_ptr cnfBytes ⋆ dimacsState c0.hdr mv' nc' cur' val' ⋆
          array (t := i8) c1.pLitMark s2.core.lit_mark ⋆
          array (t := i8) c1.pMark s2.core.mrk ⋆
          FullCoreU32A c1 s2.core ⋆ FullCoreU32B c1 s2.core ⋆ FullCoreDynArrs c1 s2.core ⋆
          FullScratchArrays c1 s2.scratch ⋆ c1.pad ⋆ array64 (c1.hdr - 2304#64) ext1 ⋆
          region work_ptr (fullAlignPad work_ptr) ⋆ R)) m_chk :=
      sep_cast hm_chk (by ac_rfl)
    refine wp_join_state1 (fun rv : BitVec 64 => rv)
      (fun rv m'' => m'' = m_chk ∧ (rv = 0#64 ∨ (rv = 10#64 ∧
        runKissatCheckModel cnfBytes (s2.core.vals.map UInt8.ofBitVec) c0.mv = true))) ?_ ?_
    · intro _ rv m'' ⟨hm'', hrv⟩
      rw [hm'']
      c0_hstraight
      rcases hrv with rfl | ⟨rfl, hrun⟩
      · exact hk 0#64 m_chk (.inl rfl) (fun h => absurd h (by decide))
          (fun h => absurd h (by decide)) hm_reg
      · exact hk 10#64 m_chk (.inr (.inl rfl)) (fun h => absurd h (by decide))
          (fun _ => search_sat_model_of_check hhdr0 hc1 hlen2 hm_mod hrun) hm_reg
    · intro J hJ
      c0_hstraight
      refine jnz_bv_eq rfl (fun eq1 => ?_) (fun _ => by
        c0_hstraight; exact hJ 0#64 m_chk ⟨rfl, .inl rfl⟩)
      have hrun : runKissatCheckModel cnfBytes (s2.core.vals.map UInt8.ofBitVec) c0.mv = true := by
        rw [eq1] at hrc
        cases hrun' : runKissatCheckModel cnfBytes (s2.core.vals.map UInt8.ofBitVec) c0.mv
        · simp [hrun'] at hrc
        · rfl
      c0_hstraight
      exact hJ 10#64 m_chk ⟨rfl, .inr ⟨rfl, hrun⟩⟩
  · c0_hstraight
    have hm_reg : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m := by
      have hm_s : ((region work_ptr (fullAlignPad work_ptr) ⋆ FullM6HdrMem c1 ext1 s1) ⋆
          (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_cast hm (by ac_rfl)
      have hm_r := sep_mono (fun _ hx => region_work_from_m6_hdrMem hfit_w hwlen
        (hc1.hdr.trans hhdr0) (hc1.avail.trans havail0) hcfg1 hext1 hlen1 hx) hm_s
      exact sep_cast hm_r (by ac_rfl)
    exact hk r m hr
      (fun eq20 => ⟨cnf, hparse, Ref.shiftDownCnf_unsat (parseDimacs_cnfVarsPos hparse) (h20 eq20)⟩)
      (fun eq10 => absurd eq10 ne10) hm_reg

/-! ## 3. `kissat_solve_bytes_seeded_wp` and `kissat_solve_bytes_wp` -/

theorem kissat_solve_bytes_seeded_wp {Γ : Env} (hΓ : Γ.Sat Spec.deps)
    (hPrep : Γ.Has "full_preprocess_m6" Proof.Spec.fullM6PreprocessSpec)
    (hSearch : Γ.Has "full_search_m6" Proof.Spec.fullM6SearchSpec) :
    SpecEntry.Impl Γ kissat_solve_bytes_seeded
      ⟨"kissat_solve_bytes_seeded", [i64, i64, i64, i64, i64, i64], [i64],
        Spec.fullM6SolveBytesSeededSpec, true⟩ := by
  refine ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X hs => ?_⟩
  dsimp only [kissat_solve_bytes_seeded] at xs Q m hs ⊢
  change Spec.fullM6SolveBytesSeededSpec xs m Q X at hs
  rcases xs with ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, seed, ⟨⟩⟩
  obtain ⟨cnfBytes, wlen, R, rfl, rfl, hfit_cnf, hfit_w, hm0, hk⟩ := hs
  dsimp only [Func.wp, kissat_solve_bytes_seeded_body]
  have hwlen_le : wlen ≤ 2 ^ 64 := by omega
  have hpad_lt : fullAlignPad work_ptr < 8 := fullAlignPad_lt8 work_ptr
  have hret0 : ∀ (hno : ∀ mv nc i0, cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
      Src.fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen → i0 ≤ cnfBytes.length →
      Ref.parseHeader cnfBytes = some (mv, nc, List.drop i0 cnfBytes) →
      UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (List.drop i0 cnfBytes) nc → False),
      Q (0#64, ()) m := fun hno =>
    hk 0#64 m (.inl rfl) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun mv nc i0 h1 h2 h3 h4 h5 h6 h7 => False.elim (hno mv nc i0 h1 h2 h3 h4 h5 h6 h7)) hm0
  c0_hstraight
  refine jnz_bv_eq rfl (fun eqf => ?_) (fun nef => ?_)
  · c0_hstraight
    exact hret0 (fun _ _ _ _ _ hf _ _ _ _ => by rw [eqf] at hf; simp at hf)
  c0_hstraight
  refine jnz_bv_eq rfl (fun eqc => ?_) (fun nec => ?_)
  · c0_hstraight
    exact hret0 (fun _ _ _ hc _ _ _ _ _ _ => hc eqc)
  c0_hstraight
  refine jnz_bv_eq rfl (fun eqw => ?_) (fun new => ?_)
  · c0_hstraight
    exact hret0 (fun _ _ _ _ hw _ _ _ _ _ => hw eqw)
  c0_hstraight
  refine jnz_bv_ult rfl
    (fun hlt => absurd (bv_sub_not0_le hfit_cnf) (BitVec.not_le.mpr hlt)) (fun _ => ?_)
  c0_hstraight
  refine jnz_bv_ult rfl
    (fun hlt => absurd (bv_sub_not0_le hfit_w) (BitVec.not_le.mpr hlt)) (fun _ => ?_)
  c0_hstraight
  dsimp only
  rw [align_pad_bv_eq work_ptr]
  have hpad3456_eq : (BitVec.ofNat 64 (fullAlignPad work_ptr) + 3456 : Val i64) =
      BitVec.ofNat 64 (fullAlignPad work_ptr + Src.fullM6HdrTotalBytes) := by
    apply BitVec.eq_of_toNat_eq
    have : Src.fullM6HdrTotalBytes = 3456 := rfl
    change (BitVec.ofNat 64 (fullAlignPad work_ptr) + 3456#64).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, this]
    omega
  rw [hpad3456_eq]
  refine jnz_bv_ult rfl (fun hlt => ?_) (fun hge => ?_)
  · c0_hstraight
    have hw_lt : wlen < fullAlignPad work_ptr + Src.fullM6HdrTotalBytes := by
      rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hlt
      have : Src.fullM6HdrTotalBytes = 3456 := rfl
      omega
    exact hret0 (fun mv _ _ _ _ _ hneed _ _ _ => by
      have hf := fullFixedBytes_ge_1472 mv
      have h1 : Src.fullM6ExtBytes = 2304 := rfl
      have h2 : Src.fullM6HdrTotalBytes = 3456 := rfl
      omega)
  have hfit_hdr : fullAlignPad work_ptr + Src.fullM6HdrTotalBytes ≤ wlen := by
    rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hge
    have : Src.fullM6HdrTotalBytes = 3456 := rfl
    omega
  have hsub_eq : BitVec.ofNat 64 wlen - BitVec.ofNat 64 (fullAlignPad work_ptr) =
      BitVec.ofNat 64 (wlen - fullAlignPad work_ptr) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have hbase_eq : work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) =
      fullM6WorkBase work_ptr := rfl
  have hm_split : (bytes cnf_ptr cnfBytes ⋆
      region (fullM6WorkBase work_ptr) (wlen - fullAlignPad work_ptr) ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m := by
    have hsum : fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr) = wlen := by omega
    have hreg := region_split (a := work_ptr) (n1 := fullAlignPad work_ptr)
      (n2 := wlen - fullAlignPad work_ptr) (by omega)
    rw [hsum, hbase_eq] at hreg
    rw [hreg] at hm0
    exact sep_cast hm0 (by ac_rfl)
  c0_hstraight
  refine wp_call_of_spec _ _ (deps_has_mem_init hΓ _ _ _ _ ?_)
  dsimp only [vals, Arg.val]; unfold Internal.Spec.fullM6MemInitExactSpec
  have havail_toNat : (BitVec.ofNat 64 (wlen - fullAlignPad work_ptr)).toNat =
      wlen - fullAlignPad work_ptr := by
    rw [BitVec.toNat_ofNat]; omega
  have hbase_fit : (fullM6WorkBase work_ptr).toNat + (wlen - fullAlignPad work_ptr) < 2 ^ 64 := by
    rw [← hbase_eq, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨cnfBytes, region work_ptr (fullAlignPad work_ptr) ⋆ R, rfl, hfit_cnf,
    by rw [hsub_eq, havail_toNat]; exact hbase_fit,
    by rw [hsub_eq, havail_toNat]; exact hm_split, ?_, ?_⟩
  · intro m1 hm1 hfail
    c0_hstraight
    refine jnz_bv_eq rfl (fun _ => ?_) (fun hne => absurd rfl hne)
    c0_hstraight
    have hm1_reg : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m1 := by
      rw [hsub_eq, havail_toNat] at hm1
      have h1 : ((region work_ptr (fullAlignPad work_ptr) ⋆
          region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
            (wlen - fullAlignPad work_ptr)) ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m1 :=
        sep_cast hm1 (by ac_rfl)
      rw [region_merge_eq (by omega) hwlen_le] at h1
      exact sep_cast h1 (by ac_rfl)
    refine hk 0#64 m1 (.inl rfl) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun mv nc i0 _ _ _ hneed _ hhdr _ => ?_) hm1_reg
    rw [hsub_eq, havail_toNat] at hfail
    rcases hfail with hsmall | hshort
    · omega
    · have := hshort mv nc (List.drop i0 cnfBytes) hhdr
      have h1 : Src.fullM6ExtBytes = 2304 := rfl
      omega
  · intro c0 ext0 s0 j rest m1 hhdr0 havail0 hcfg0 _ hph0 hj hdrop hinv0 hcv0 hdcur0
      halen0 _ hte0 hpr0 hl0 _ hoom0 hinc0 hprb0 hvals0 hwvec0 hm1
    rw [hsub_eq, havail_toNat] at havail0
    have hhdr_ne0 : c0.hdr ≠ 0#64 := by
      intro h0
      have h1 : Src.fullM6ExtBytes ≤ c0.hdr.toNat := hcfg0
      rw [h0] at h1; simp [Src.fullM6ExtBytes] at h1
    c0_hstraight
    refine jnz_bv_eq rfl (fun h0 => absurd h0 hhdr_ne0) (fun _ => ?_)
    refine wp_call_of_spec _ _ (deps_has_parse_body hΓ _ _ _ _ ?_)
    dsimp only [vals, Arg.val]; unfold Parse.Spec.fullParseBodyM6Spec
    refine ⟨c0, ext0, s0, cnf_ptr, cnfBytes, j, region work_ptr (fullAlignPad work_ptr) ⋆ R,
      rfl, rfl, hfit_cnf, hj, hdrop ▸ hph0, hcv0, hdcur0, hl0, hte0, hpr0, halen0, hoom0, hprb0,
      hinc0, hvals0, hwvec0, hinv0, hm1, ?_⟩
    intro rp ext1 s1 m2 hlen1 hext1 hrp _ _ _ h20p h1p hunit hm2
    have hunit_force : ∀ mv nc i0, cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
        Src.fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen → i0 ≤ cnfBytes.length →
        Ref.parseHeader cnfBytes = some (mv, nc, List.drop i0 cnfBytes) →
        UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (List.drop i0 cnfBytes) nc →
        rp = 20#64 := fun mv nc i0 _ _ _ _ _ hph_u hu => by
      have heq := Option.some.inj ((hdrop ▸ hph0).symm.trans hph_u)
      have hmv_eq : c0.mv = mv := congrArg Prod.fst heq
      have hnc_eq : c0.nc = nc := congrArg (fun x => x.2.1) heq
      have hrest_eq : List.drop j cnfBytes = List.drop i0 cnfBytes :=
        congrArg (fun x => x.2.2) heq
      have htake : List.take (2 * c0.mv) s0.core.vals = List.replicate (2 * c0.mv) 0#8 := by
        rw [hvals0, List.take_replicate]
        congr 1; rw [c0.hbva]; omega
      apply hunit
      rw [htake, hmv_eq, hnc_eq, hrest_eq]
      exact hu
    c0_hstraight
    refine jnz_bv_ne rfl (fun ne1 => ?_) (fun eq1 => ?_)
    · c0_hstraight
      have hm2_reg : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m2 := by
        have h1 : ((region work_ptr (fullAlignPad work_ptr) ⋆ FullM6HdrMem c0 ext1 s1) ⋆
            (bytes cnf_ptr cnfBytes ⋆ R)) m2 := sep_cast hm2 (by ac_rfl)
        have h2 := sep_mono (fun _ hx => region_work_from_m6_hdrMem hfit_hdr hwlen_le
          hhdr0 havail0 hcfg0 hext1 hlen1 hx) h1
        exact sep_cast h2 (by ac_rfl)
      have hrp' : rp = 0#64 ∨ rp = 10#64 ∨ rp = 20#64 := by
        rcases hrp with rfl | rfl | rfl
        · exact .inl rfl
        · exact absurd rfl ne1
        · exact .inr (.inr rfl)
      exact hk rp m2 hrp' h20p
        (fun eq10 => by rcases hrp with rfl | rfl | rfl <;> exact absurd eq10 (by decide))
        hunit_force hm2_reg
    · obtain ⟨cnf, hparse, hinv1, hl1⟩ := h1p eq1
      have hno_unit : ∀ mv nc i0, cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
          Src.fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen →
          i0 ≤ cnfBytes.length →
          Ref.parseHeader cnfBytes = some (mv, nc, List.drop i0 cnfBytes) →
          UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (List.drop i0 cnfBytes) nc → False :=
        fun mv nc i0 h1 h2 h3 h4 h5 h6 h7 => by
          have := hunit_force mv nc i0 h1 h2 h3 h4 h5 h6 h7
          rw [eq1] at this; exact absurd this (by decide)
      have hk' : ∀ r' m', (r' = 0#64 ∨ r' = 10#64 ∨ r' = 20#64) →
          (r' = 20#64 → ∃ cnf', Ref.parseDimacs cnfBytes = some cnf' ∧ cnf'.Unsat) →
          (r' = 10#64 → ∃ cnf', Ref.parseDimacs cnfBytes = some cnf' ∧
            ∀ (F : Mem 64 → Prop) (M : Mem 64), (Eq m' ⋆ F) M →
              CNF.Sat (readModelFromWorkM6 M work_ptr) cnf') →
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' → Q (r', ()) m' :=
        fun r' m' hr' h20' h10' hm' => hk r' m' hr' h20' h10'
          (fun mv nc i0 h1 h2 h3 h4 h5 h6 h7 => False.elim (hno_unit mv nc i0 h1 h2 h3 h4 h5 h6 h7))
          hm'
      have hm2_f : (FullM6HdrMem c0 ext1 s1 ⋆
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m2 :=
        sep_cast hm2 (by ac_rfl)
      rw [wp_load]; refine ⟨_, fullM6HdrMem_load_mv hm2_f, ?_⟩
      refine wp_call_of_spec _ _ (hPrep _ _ _ _ ?_)
      dsimp only [vals, Arg.val]
      refine fullM6PreprocessSpec_of hinv1 hl1 hm2_f ?_
      intro rpp c1 ext2 s2 m3 hc1 hlen2 hcfg2 hext2 hrpp _ h20pp h1pp h10pp hm3
      have hm3' : (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c1 ext2 s2 ⋆
          region work_ptr (fullAlignPad work_ptr) ⋆ R) m3 := sep_cast hm3 (by ac_rfl)
      c0_hstraight
      refine jnz_bv_eq rfl (fun eq20 => ?_) (fun ne20 => ?_)
      · c0_hstraight
        have hm3_reg : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m3 := by
          have h1 : ((region work_ptr (fullAlignPad work_ptr) ⋆ FullM6HdrMem c1 ext2 s2) ⋆
              (bytes cnf_ptr cnfBytes ⋆ R)) m3 := sep_cast hm3 (by ac_rfl)
          have h2 := sep_mono (fun _ hx => region_work_from_m6_hdrMem hfit_hdr hwlen_le
            (hc1.hdr.trans hhdr0) (hc1.avail.trans havail0) hcfg2 hext2 hlen2 hx) h1
          exact sep_cast h2 (by ac_rfl)
        exact hk' 20#64 m3 (.inr (.inr rfl))
          (fun _ => ⟨cnf, hparse,
            Ref.shiftDownCnf_unsat (parseDimacs_cnfVarsPos hparse) (h20pp eq20)⟩)
          (fun h => absurd h (by decide)) hm3_reg
      · refine wp_join_state1 (fun rv : BitVec 64 => rv)
          (fun rv m4 => ∃ c' ext' s', FullCfgCompat c0 c' ∧ s'.LengthsOk c' ∧
            FullM6HdrCfgOk c' ∧ M6HdrExtOk ext' ∧ (rv = 0#64 ∨ rv = 10#64 ∨ rv = 20#64) ∧
            (rv = 20#64 → (Ref.shiftDownCnf cnf).Unsat) ∧
            (rv = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) ∧
            (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c' ext' s' ⋆
              region work_ptr (fullAlignPad work_ptr) ⋆ R) m4) ?_ ?_
        · intro _ rv m4 ⟨c', ext', s', hc', hlen', hcfg', hext', hrv, h20', h10', hm4⟩
          exact solve_bytes_l30_wp hΓ hfit_cnf hfit_hdr hwlen_le hhdr0 havail0 hparse
            hc' hlen' hcfg' hext' hrv h20' h10' hm4 hk'
        · intro JL30 hJL30
          c0_hstraight
          refine jnz_bv_eq rfl (fun eq10 => ?_) (fun ne10 => ?_)
          · c0_hstraight
            exact hJL30 10#64 m3 ⟨c1, ext2, s2, hc1, hlen2, hcfg2, hext2, .inr (.inl rfl),
              fun h => absurd h (by decide), fun _ => h10pp eq10, hm3'⟩
          · refine wp_join_state1 (fun rv : BitVec 64 => rv)
              (fun rv m4 => ∃ c' ext' s', FullCfgCompat c0 c' ∧ s'.LengthsOk c' ∧
                FullM6HdrCfgOk c' ∧ M6HdrExtOk ext' ∧ (rv = 0#64 ∨ rv = 10#64 ∨ rv = 20#64) ∧
                (rv = 20#64 → (Ref.shiftDownCnf cnf).Unsat) ∧
                (rv = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) ∧
                (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c' ext' s' ⋆
                  region work_ptr (fullAlignPad work_ptr) ⋆ R) m4) ?_ ?_
            · intro _ rv m4 hinv4
              c0_hstraight
              exact hJL30 rv m4 hinv4
            · intro Jsub hJsub
              c0_hstraight
              refine jnz_bv_ne rfl (fun ne0 => ?_) (fun _ => ?_)
              · have eq1pp : rpp = 1#64 := by
                  rcases hrpp with rfl | rfl | rfl | rfl
                  · exact absurd rfl ne0
                  · rfl
                  · exact absurd rfl ne10
                  · exact absurd rfl ne20
                have ⟨hinv2, hl2⟩ := h1pp eq1pp
                c0_hstraight
                have ⟨hok_rng, hinv2', hm3_rng⟩ :=
                  m6Hdr_store_scr .rng_state 944 rfl rfl rfl (seed &&& 4294967295#64) hinv2 hm3
                rw [wp_store]; refine ⟨hc1.hdr.symm ▸ hok_rng, ?_⟩
                refine wp_call_of_spec _ _ (hSearch _ _ _ _ ?_)
                dsimp only [vals, Arg.val]
                have hst_rng : storeMem m3 i64 (c0.hdr + 944 : Val i64)
                    (seed &&& 4294967295 : Val i64) =
                    storeMem m3 i64 (c1.hdr + 944#64) (seed &&& 4294967295#64) := by
                  rw [hc1.hdr]; rfl
                rw [hst_rng, ← hc1.hdr]
                refine fullM6SearchSpec_of hinv2' hl2 hm3_rng ?_
                intro rs c2 ext3 s3 m4 hc2 hlen3 hcfg3 hext3 hrs h20s h10s hm4
                c0_hstraight
                exact hJsub rs m4 ⟨c2, ext3, s3, fullCfgCompat_trans hc1 hc2, hlen3, hcfg3,
                  hext3, hrs, h20s, h10s, sep_cast hm4 (by ac_rfl)⟩
              · c0_hstraight
                exact hJsub 0#64 m3 ⟨c1, ext2, s2, hc1, hlen2, hcfg2, hext2, .inl rfl,
                  fun h => absurd h (by decide), fun h => absurd h (by decide), hm3'⟩

theorem kissat_solve_bytes_wp {Γ : Env}
    (hSeeded : Γ.Has "kissat_solve_bytes_seeded" Spec.fullM6SolveBytesSeededSpec) :
    SpecEntry.Impl Γ kissat_solve_bytes
      ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64],
        Proof.Spec.fullM6SolveBytesCoreModelSpec, true⟩ := by
  refine ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X hs => ?_⟩
  dsimp only [kissat_solve_bytes] at xs Q m hs ⊢
  change Proof.Spec.fullM6SolveBytesCoreModelSpec xs m Q X at hs
  rcases xs with ⟨p0, p1, p2, p3, p4, ⟨⟩⟩
  dsimp only [Func.wp, kissat_solve_bytes_body]
  refine wp_call_of_spec _ _ (hSeeded _ _ _ _ ?_)
  change Proof.Spec.fullM6SolveBytesCoreModelSpec (p0, p1, p2, p3, p4, ()) m
    (fun r m' => wp Γ Q X (.ret (Arg.var r.fst, ())) m') X
  unfold Proof.Spec.fullM6SolveBytesCoreModelSpec at hs ⊢
  obtain ⟨cnfBytes, wlen, R, hcl, hwl, hfc, hfw, hm, hk⟩ := hs
  refine ⟨cnfBytes, wlen, R, hcl, hwl, hfc, hfw, hm, fun r m' hr h20 h10 hu hm' => ?_⟩
  c0_hstraight
  exact hk r m' hr h20 h10 hu hm'

end LeanQbe.T.Examples.Kissat.Proof.Search
