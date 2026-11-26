/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.SatNv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header1
public import LeanQbe.T.InlineLemmas
public import LeanQbe.T.Logic.Bytes
public import LeanQbe.T.Logic.MemLemmas
public import Std.Sat.CNF.Basic
public import Kraken.Mem
public import Kraken.Separation

/-!
# Kissat Concrete `8,192 B` UNSAT/SAT Non-Vacuity & Assembly UNSAT Lift (`Proof.Spec.SatNv1`)

1. Concrete `8,192 B` `Mem 64` UNSAT & SAT payloads/witnesses (`nvM6UnsatInitMem`,
   `nvM6SatInitMem`, `nvM6Mem`, `nvM6Mem_sat`), plus `m6NvWorkLen` / `m6NvPayload`.
2. Transparent UNSAT contract `m7FidSolveBytesSpec`, `CommonUnsatSolveReq`, `KissatUnsatPkg`,
   and generic soundness/non-vacuity lifts (`fid_solve_bytes_sound_of_fn`,
   `fid_solve_bytes_host_sound`, `fid_unsat_nv_of_fn`, `moduleCheckAcyclic_of_moduleOk`).
3. Parametric `full_m6_mem_init` concrete execution (`nvM6_unsat_full_m6_mem_init_of`) and
   concrete Tier-3b non-vacuity (`fullM6_unsat_nv`, `fullM6_sat_nv`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Spec

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src
open Kraken.Bedrock2.Test

/-- Concrete UNSAT DIMACS input (`p cnf 1 2\n1 0\n-1 0\n`, 19 bytes). -/
@[expose] def fullNvUnsatBytes : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 49, 32, 50, 10, 49, 32, 48, 10, 45, 49, 32, 48, 10]

/-- Parsed `Std.Sat.CNF Nat` for `fullNvUnsatBytes`. -/
@[expose] def fullNvUnsatCnf : CNF Nat :=
  (CNF.empty.add (CNF.Clause.ofLiterals [(1, true)])).add (CNF.Clause.ofLiterals [(1, false)])

theorem parseDimacs_fullNvUnsatBytes : parseDimacs fullNvUnsatBytes = some fullNvUnsatCnf := rfl


abbrev fullNvCnfPtr : BitVec 64 := 0x1000#64
abbrev fullNvWorkPtr (cnfBytes : List UInt8) : BitVec 64 :=
  fullNvCnfPtr + BitVec.ofNat 64 cnfBytes.length


/-- Concrete `FullCfg` (`max_vars = 1`, `wcap = 1`, `avail = 1756`, `slack = 0`). -/
@[expose] def nvOneLitCfg : FullCfg where
  hdr := 0x1000#64
  avail := 1756
  mv := 1
  max_vars := 1
  bva_cap := 0
  nc := 2
  arena_cap := 0
  wcap := 1
  delayed_cap := 0
  red_cap := 0
  extend_cap := 0
  scratch_cap := 0
  hbva := rfl
  hmv := by decide
  hmaxv := by decide
  hnc := by decide
  harena := by decide
  hwcap := by decide
  hdel := by decide
  hred := by decide
  hext := by decide
  hscr := by decide
  havail_fit := by decide
  hsize := by decide

/-- Zero-initialized concrete `FullScratch` for `nvOneLitCfg` (`last_learned = 0xFFFFFFFF`). -/
@[expose] def nvOneLitScratch : FullScratch where
  heap_len := 0
  scinc := 0#64; rel_period := 0#64; rel_limit := 0#64; rel_wait := 0#64
  rel_u := 0#64; rel_v := 0#64; rel_trigger := 0#64; conflicts := 0#64
  learned_lits := 0#64; min_removed := 0#64; delayed_len := 0; stable := 0#64
  switched := 0#64; mode_count := 0#64; mode_confl_lim := 0#64; mode_tick_lim := 0#64
  mode_saved_ticks := 0#64; search_ticks := 0#64; q_first := 0#64; q_last := 0#64
  q_search_idx := 0#64; q_search_stamp := 0#64; q_cur_stamp := 0#64
  target_assigned := 0#64; best_assigned := 0#64; rephase_limit := 0#64; rephased := 0#64
  reduce_limit := 0#64; reductions := 0#64; tier1 := 0#64; tier2 := 0#64
  restarts := 0#64; restart_limit := 0#64; ema_fast_biased := 0#64; ema_fast_exp := 0#64
  ema_slow_biased := 0#64; ema_slow_exp := 0#64; extend_len := 0; rng_state := 0#64
  chrono_levels := 0#64; otfs_cnt := 0#64; eager_sub_cnt := 0#64; probe_limit := 0#64
  probings := 0#64; elim_limit := 0#64; eliminations := 0#64; elim_bound := 0#64
  iterating := 0#64; hbr_cnt := 0#64; trans_cnt := 0#64; viv_cnt := 0#64
  subst_cnt := 0#64; cong_cnt := 0#64; sweep_cnt := 0#64; bve_cnt := 0#64
  bce_cnt := 0#64; bva_cnt := 0#64; walk_cnt_stat := 0#64; fwd_sub_cnt := 0#64
  fwd_str_cnt := 0#64; ant_sz := 0#64; res_sz := 0#64
  walk_vals := List.replicate 2 0#8
  phases := List.replicate 1 0#8
  phases_target := List.replicate 1 0#8
  phases_best := List.replicate 1 0#8
  walk_best := List.replicate 1 0#8
  heap := List.replicate 1 0#32
  pos := List.replicate 1 0#32
  shrink_stk := List.replicate 1 0#32
  q_prev := List.replicate 1 0#32
  q_next := List.replicate 1 0#32
  q_stamp := List.replicate 1 0#32
  wsort := List.replicate 2 0#32
  work_stk1 := List.replicate 2 0#32
  work_stk2 := List.replicate 2 0#32
  tarjan_mark := List.replicate 2 0#32
  tarjan_reach := List.replicate 2 0#32
  score := List.replicate 1 0#64
  sim_sig := List.replicate 1 0#64
  glue_used := List.replicate 64 0#32
  last_learned := List.replicate 16 0xFFFFFFFF#32
  delayed := []
  red_refs := []
  extend_stk := []
  scratch_buf := []

/-- Concrete level-0 binary-conflict `FullState`: `x0` assigned true at level 0 with falsified
binary conflict `(¬x0 ∨ ¬x0)` entailed by `nvOneLitF0 = {(x0), (¬x0)}`. -/
@[expose] def nvOneLitState : FullState where
  core :=
    { d_cur := 0#64, d_val := 0#64, cur_vars := 1, unassigned := 0#64
      arena_len := 0, wlen := 1, wusable := 0#64, arena_garbage := 0#64
      first_reducible := 0#64, num_irred := 0#64, num_redundant := 0#64, num_binary := 0#64
      unflushed := 0#64, probing := 0#64, trail_end := 1, propagated := 0
      cur_level := 0, fuel := 0#64, confl_ref := 0#64, confl_type := 1#64
      confl_lit0 := 1#64, confl_lit1 := 1#64, tmp_cnt := 0, tmp_len := 0
      min_clr_len := 0, min_clr_full := 0#64, oom := 0#64, dense_mode := 0#64
      inconsistent := 0#64
      vals := [1#8, 0xFF#8]
      lit_mark := [0#8, 0#8]
      mrk := [0#8]
      flags := [0#32]
      lvl := [0#32]
      rsns := [0xFFFFFFFF#32]
      trl := [0#32]
      trail_pos := [0#32]
      tmp := [0#32]
      min_clr := [0#32]
      frame_trail := [0#32, 0#32]
      frame_dec := [0#32, 0#32]
      wvec := [0#32, 0#32, 0#32, 0#32]
      repr := [0#32, 0#32]
      min_stk := [0#32, 0#32, 0#32, 0#32]
      arena := []
      wstk := [0#32] }
  scratch := nvOneLitScratch

theorem nv_arr_pad {t : Ty} {a : BitVec 64} {xs : List (Val t)} {n pad : Nat}
    (hn : t.bytes * xs.length = n) (hbd : n + pad ≤ 2 ^ 64) :
    (array (t := t) a xs ⋆ region (a + BitVec.ofNat 64 n) pad)
      ((bytesOf xs ++ List.replicate pad 0).At a) :=
  nv_sep_append (by rw [bytesOf_length, hn])
    (by rw [bytesOf_length, List.length_replicate]; omega)
    (array_bytes a xs (by omega)) ⟨List.replicate pad 0, List.length_replicate, rfl⟩

theorem nv_arr_pad_p {t : Ty} {a : BitVec 64} {xs : List (Val t)} (n pad : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n + pad ≤ 2 ^ 64) :
    (bytesOf xs ++ List.replicate pad 0).length = n + pad ∧
    (array (t := t) a xs ⋆ region (a + BitVec.ofNat 64 n) pad)
      ((bytesOf xs ++ List.replicate pad 0).At a) :=
  ⟨by rw [List.length_append, bytesOf_length, List.length_replicate, hn],
    nv_arr_pad hn hbd⟩

theorem nv_arr_p {t : Ty} {a : BitVec 64} {xs : List (Val t)} (n : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytesOf xs).length = n ∧ array (t := t) a xs ((bytesOf xs).At a) :=
  ⟨by rw [bytesOf_length, hn], array_bytes a xs (by omega)⟩

theorem nv_arr64_p {a : BitVec 64} {xs : List (BitVec 64)} (n : Nat)
    (hn : 8 * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytes64 xs).length = n ∧ array64 a xs ((bytes64 xs).At a) :=
  ⟨by rw [bytes64_length, hn], array64_bytes a xs (by omega)⟩

theorem nv_join_pair {P Q : Mem 64 → Prop} {a b : BitVec 64} {bs1 bs2 : List UInt8}
    {n1 n2 : Nat} (h1 : bs1.length = n1 ∧ P (bs1.At a))
    (h2 : bs2.length = n2 ∧ Q (bs2.At b))
    (hb : b = a + BitVec.ofNat 64 n1) (hbd : n1 + n2 ≤ 2 ^ 64) :
    (bs1 ++ bs2).length = n1 + n2 ∧ (P ⋆ Q) ((bs1 ++ bs2).At a) :=
  ⟨by rw [List.length_append, h1.1, h2.1], nv_sep_append (h1.1 ▸ hb) (by omega) h1.2 h2.2⟩

theorem nv_sep_reorg {P Q : Mem 64 → Prop} {bs : List UInt8} {a : BitVec 64} {n : Nat}
    (h : bs.length = n ∧ P (bs.At a)) (himp : ∀ m, P m → Q m) : bs.length = n ∧ Q (bs.At a) :=
  ⟨h.1, himp _ h.2⟩

theorem nv_zip4 {A1 B1 A2 B2 A3 B3 A4 B4 : Mem 64 → Prop} {m : Mem 64}
    (h : ((((A1 ⋆ B1) ⋆ (A2 ⋆ B2)) ⋆ (A3 ⋆ B3)) ⋆ (A4 ⋆ B4)) m) :
    (((A1 ⋆ A3 ⋆ A4) ⋆ A2) ⋆ (B1 ⋆ B2 ⋆ B3 ⋆ B4)) m := sep_ac h

theorem nv_zip4_tail {C A2 P1 A5 B5 A6 B6 A7 B7 A8 B8 : Mem 64 → Prop} {m : Mem 64}
    (h : ((((((C ⋆ A2) ⋆ P1) ⋆ (A5 ⋆ B5)) ⋆ (A6 ⋆ B6)) ⋆ (A7 ⋆ B7)) ⋆ (A8 ⋆ B8)) m) :
    (C ⋆ (A2 ⋆ A5 ⋆ A6 ⋆ A7 ⋆ A8) ⋆ (P1 ⋆ B5 ⋆ B6 ⋆ B7 ⋆ B8)) m := sep_ac h


/-! ## 1. Concrete Formulas & `8,192 B` Host Payloads (`UNSAT` & `SAT`) -/

@[expose] def nvM6CnfPtr : BitVec 64 := 0x1000#64

@[expose] def nvM6WorkLen : Nat := 8192

/-- Concrete UNSAT DIMACS `"p cnf 1 2\n1 0\n-1 0\n"` (`(x1) ∧ (~x1)`, `19` bytes). -/
@[expose] def nvM6UnsatBytes : List UInt8 := fullNvUnsatBytes

@[expose] def nvM6UnsatCnf : CNF Nat := fullNvUnsatCnf

@[expose] def nvM6UnsatWorkPtr : BitVec 64 :=
  nvM6CnfPtr + BitVec.ofNat 64 nvM6UnsatBytes.length

/-- Concrete SAT DIMACS `"p cnf 2 1\n1 2 0\n"` (`(x1 ∨ x2)`, `16` bytes). -/
@[expose] def nvM6SatBytes : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 50, 32, 49, 10, 49, 32, 50, 32, 48, 10]

@[expose] def nvM6SatCnf : CNF Nat :=
  CNF.empty.add (CNF.Clause.ofLiterals [(1, true), (2, true)])

@[expose] def nvM6SatWorkPtr : BitVec 64 :=
  nvM6CnfPtr + BitVec.ofNat 64 nvM6SatBytes.length

@[expose] def nvM6UnsatInitMem : Mem 64 :=
  (nvM6UnsatBytes ++ List.replicate nvM6WorkLen 0).At nvM6CnfPtr

@[expose] def nvM6SatInitMem : Mem 64 :=
  (nvM6SatBytes ++ List.replicate nvM6WorkLen 0).At nvM6CnfPtr

theorem nvM6UnsatWorkPtr_eq_fullNvWorkPtr :
    nvM6UnsatWorkPtr = fullNvWorkPtr nvM6UnsatBytes := rfl

theorem nvM6SatWorkPtr_eq_fullNvWorkPtr :
    nvM6SatWorkPtr = fullNvWorkPtr nvM6SatBytes := rfl

theorem nvM6Unsat_pad_eq : fullAlignPad nvM6UnsatWorkPtr = 5 := by decide

theorem nvM6Sat_pad_eq : fullAlignPad nvM6SatWorkPtr = 0 := by decide

theorem nvM6_payload_sep (cnfBytes : List UInt8) (hlen : cnfBytes.length ≤ 4096) :
    (bytes nvM6CnfPtr cnfBytes ⋆ region (fullNvWorkPtr cnfBytes) nvM6WorkLen)
      ((cnfBytes ++ List.replicate nvM6WorkLen 0).At nvM6CnfPtr) :=
  nv_sep_append rfl
    (by unfold nvM6WorkLen; rw [List.length_replicate]; omega)
    rfl ⟨List.replicate nvM6WorkLen 0, List.length_replicate, rfl⟩

theorem nvM6UnsatInitMem_sep :
    (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) nvM6UnsatInitMem := by
  rw [nvM6UnsatWorkPtr_eq_fullNvWorkPtr]
  exact nvM6_payload_sep nvM6UnsatBytes (by decide)

theorem nvM6SatInitMem_sep :
    (bytes nvM6CnfPtr nvM6SatBytes ⋆ region nvM6SatWorkPtr nvM6WorkLen) nvM6SatInitMem := by
  rw [nvM6SatWorkPtr_eq_fullNvWorkPtr]
  exact nvM6_payload_sep nvM6SatBytes (by unfold nvM6SatBytes; decide)

theorem parseDimacs_nvM6UnsatBytes : parseDimacs nvM6UnsatBytes = some nvM6UnsatCnf :=
  parseDimacs_fullNvUnsatBytes

theorem nvM6UnsatCnf_unsat : nvM6UnsatCnf.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hsat
  rw [nvM6UnsatCnf, fullNvUnsatCnf, CNF.sat_add, CNF.sat_add] at hsat
  rcases hsat with ⟨hc2, hc1, _⟩
  rw [CNF.Clause.sat_iff_exists_mem_eq] at hc1 hc2
  obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := hc1; obtain ⟨⟨v2, p2⟩, hm2, he2⟩ := hc2
  rw [← CNF.Clause.mem_literals_iff] at hm1 hm2; simp at hm1 hm2
  rcases hm1 with ⟨rfl, rfl⟩; rcases hm2 with ⟨rfl, rfl⟩; exact nomatch (he1.symm.trans he2)

theorem nvM6Unsat_header :
    parseHeader nvM6UnsatBytes = some (1, 2, nvM6UnsatBytes.drop 9) := rfl

theorem nvM6Unsat_unitTrace :
    UnitUnsatTrace 1 (List.replicate 2 0#8) (nvM6UnsatBytes.drop 9) 2 := by
  have hcl1 : parseClause 1 (nvM6UnsatBytes.drop 9) =
      some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral 0], nvM6UnsatBytes.drop 13) := rfl
  have hcl2 : parseClause 1 (nvM6UnsatBytes.drop 13) =
      some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral 1], nvM6UnsatBytes.drop 18) := rfl
  exact UnitUnsatTrace.step (l := 0) (by decide) hcl1 (by decide)
    (UnitUnsatTrace.conflict (l := 1) (by decide) hcl2 (by decide) ⟨CNF.empty, rfl⟩)

theorem nvM6_unsat_bound :
    fullM6ExtBytes + fullFixedBytes 1 + 2 * 40 + 136 + 8 ≤ nvM6WorkLen := by
  unfold nvM6WorkLen fullM6ExtBytes fullFixedBytes valsBytes markBytes u32FullBytes
    fullMinDepthOf
  decide

theorem parseDimacs_nvM6SatBytes : parseDimacs nvM6SatBytes = some nvM6SatCnf := rfl

theorem nvM6Sat_header :
    parseHeader nvM6SatBytes = some (2, 1, nvM6SatBytes.drop 9) := rfl

theorem nvM6SatCnf_sat : ∃ α, nvM6SatCnf.Sat α := by
  refine ⟨fun v => v == 1, ?_⟩
  rw [nvM6SatCnf, CNF.sat_add]
  refine ⟨?_, CNF.sat_empty⟩
  rw [CNF.Clause.sat_iff_exists_mem_eq]
  exact ⟨(1, true), by rw [← CNF.Clause.mem_literals_iff]; simp, rfl⟩

theorem nvM6SatCnf_not_unsat : ¬ nvM6SatCnf.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  exact fun h => let ⟨α, hα⟩ := nvM6SatCnf_sat; h α hα

/-! ## 2. Concrete `Mem 64` Witness `nvM6Mem` Inhabiting `M6Hdr`'s `3,456 B` Prefix -/

/-- Canonical initialized `288`-word `M6HdrExt` header (`fullM6HdrMagic` at word `0`). -/
@[expose] def nvM6ExtInitWords : List (BitVec 64) :=
  fullM6HdrMagic :: List.replicate 287 0#64

theorem nvM6ExtInitWords_len : nvM6ExtInitWords.length = fullM6ExtWords := by
  rw [nvM6ExtInitWords, List.length_cons, List.length_replicate, fullM6ExtWords]

theorem nvM6ExtInitWords_ok : M6HdrExtOk nvM6ExtInitWords :=
  M6HdrExtOk.of_len (by rw [nvM6ExtInitWords_len]; rfl)

theorem nvM6SatCfg_avail_fit :
    (6416#64 : BitVec 64).toNat + (nvM6WorkLen - fullM6ExtBytes) < 2 ^ 64 := by
  unfold nvM6WorkLen fullM6ExtBytes
  decide

theorem nvM6SatCfg_hsize :
    fullFixedBytes 2 + 4 * 0 + 4 * 1 + 12 * 0 + 4 * 0 + 4 * 0 + 4 * 0 ≤
      nvM6WorkLen - fullM6ExtBytes := by
  have hfb : fullFixedBytes 2 = 1960 := by
    unfold fullFixedBytes valsBytes markBytes u32FullBytes fullMinDepthOf; decide
  rw [hfb]
  unfold nvM6WorkLen fullM6ExtBytes
  omega

/-- Concrete `FullCfg` for `nvM6SatBytes` (`mv = 2, nc = 1`) at `fullM6WorkHdr nvM6SatWorkPtr`. -/
@[expose] def nvM6SatCfg : FullCfg where
  hdr := 6416#64
  avail := nvM6WorkLen - fullM6ExtBytes
  mv := 2
  max_vars := 2
  bva_cap := 0
  nc := 1
  arena_cap := 0
  wcap := 1
  delayed_cap := 0
  red_cap := 0
  extend_cap := 0
  scratch_cap := 0
  hbva := rfl
  hmv := by unfold dimacsBound; omega
  hmaxv := by unfold dimacsBound; omega
  hnc := by unfold dimacsBound; omega
  harena := by unfold dimacsBound; omega
  hwcap := by unfold dimacsBound; omega
  hdel := by unfold dimacsBound; omega
  hred := by unfold dimacsBound; omega
  hext := by unfold dimacsBound; omega
  hscr := by unfold dimacsBound; omega
  havail_fit := nvM6SatCfg_avail_fit
  hsize := nvM6SatCfg_hsize

theorem nvM6SatCfg_hdr_eq : nvM6SatCfg.hdr = fullM6WorkHdr nvM6SatWorkPtr := rfl

theorem nvM6SatCfg_ok : FullM6HdrCfgOk nvM6SatCfg := by
  apply M6HdrCfgOk_of_le
  have h1 : nvM6SatCfg.hdr.toNat = 6416 := rfl
  omega

/-- Concrete solved `FullState` for `(x1 ∨ x2)` with `vals = [1#8, 0xFF#8, 1#8, 0xFF#8]`. -/
@[expose] def nvM6SatState : FullState where
  core :=
    { nvOneLitState.core with
      cur_vars := 2, unassigned := 0#64
      vals := [1#8, 0xFF#8, 1#8, 0xFF#8]
      lit_mark := List.replicate 4 0#8
      mrk := List.replicate 2 0#8
      flags := List.replicate 2 0#32
      lvl := List.replicate 2 0#32
      rsns := List.replicate 2 0xFFFFFFFF#32
      trl := List.replicate 2 0#32
      trail_pos := List.replicate 2 0#32
      tmp := List.replicate 2 0#32
      min_clr := List.replicate 2 0#32
      frame_trail := List.replicate 3 0#32
      frame_dec := List.replicate 3 0#32
      wvec := List.replicate 8 0#32
      repr := List.replicate 4 0#32
      min_stk := List.replicate 6 0#32 }
  scratch :=
    { nvOneLitState.scratch with
      walk_vals := List.replicate 4 0#8
      phases := List.replicate 2 0#8
      phases_target := List.replicate 2 0#8
      phases_best := List.replicate 2 0#8
      walk_best := List.replicate 2 0#8
      heap := List.replicate 2 0#32
      pos := List.replicate 2 0#32
      shrink_stk := List.replicate 2 0#32
      q_prev := List.replicate 2 0#32
      q_next := List.replicate 2 0#32
      q_stamp := List.replicate 2 0#32
      wsort := List.replicate 4 0#32
      work_stk1 := List.replicate 4 0#32
      work_stk2 := List.replicate 4 0#32
      tarjan_mark := List.replicate 4 0#32
      tarjan_reach := List.replicate 4 0#32
      score := List.replicate 2 0#64
      sim_sig := List.replicate 2 0#64 }

theorem nvM6Sat_lengths : nvM6SatState.LengthsOk nvM6SatCfg :=
  ⟨by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [nvM6SatState, nvM6SatCfg, nvOneLitState, FullCfg.minDepth, fullMinDepthOf],
   by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [nvM6SatState, nvM6SatCfg, nvOneLitState, nvOneLitScratch]⟩

@[expose] def nvM6SatBlockHdr : List UInt8 :=
  bytes64 [2#64, 1#64, 0#64, 0#64] ++ bytes64 (hdrTailWords nvM6SatCfg nvM6SatState)

@[expose] def nvM6SatBlockBytes : List UInt8 :=
  (bytesOf (t := i8) nvM6SatState.core.vals ++ List.replicate 4 0) ++
  (bytesOf (t := i8) nvM6SatState.scratch.walk_vals ++ List.replicate 4 0) ++
  (bytesOf (t := i8) nvM6SatState.core.lit_mark ++ List.replicate 4 0) ++
  (bytesOf (t := i8) nvM6SatState.core.mrk ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvM6SatState.scratch.phases ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvM6SatState.scratch.phases_target ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvM6SatState.scratch.phases_best ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvM6SatState.scratch.walk_best ++ List.replicate 6 0)

@[expose] def nvM6SatBlockU32A : List UInt8 :=
  (bytesOf (t := i32) nvM6SatState.core.flags ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.core.lvl ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.core.rsns ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.core.trl ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.core.trail_pos ++ List.replicate 8 0)

@[expose] def nvM6SatBlockU32B : List UInt8 :=
  (bytesOf (t := i32) nvM6SatState.core.tmp ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.scratch.heap ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.scratch.pos ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.core.min_clr ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.scratch.shrink_stk ++ List.replicate 8 0)

@[expose] def nvM6SatBlockU32C : List UInt8 :=
  (bytesOf (t := i32) nvM6SatState.scratch.q_prev ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.scratch.q_next ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.scratch.q_stamp ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvM6SatState.core.frame_trail ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM6SatState.core.frame_dec ++ List.replicate 4 0)

@[expose] def nvM6SatBlockWvec : List UInt8 :=
  bytesOf (t := i32) nvM6SatState.core.wvec ++
  bytesOf (t := i32) nvM6SatState.core.repr ++
  bytesOf (t := i32) nvM6SatState.scratch.wsort ++
  bytesOf (t := i32) nvM6SatState.scratch.work_stk1 ++
  bytesOf (t := i32) nvM6SatState.scratch.work_stk2 ++
  bytesOf (t := i32) nvM6SatState.scratch.tarjan_mark ++
  bytesOf (t := i32) nvM6SatState.scratch.tarjan_reach ++
  bytes64 nvM6SatState.scratch.score ++
  bytes64 nvM6SatState.scratch.sim_sig

@[expose] def nvM6SatBlockTail : List UInt8 :=
  bytesOf (t := i32) nvM6SatState.core.min_stk ++
  bytesOf (t := i32) nvM6SatState.scratch.glue_used ++
  bytesOf (t := i32) nvM6SatState.scratch.last_learned ++
  bytesOf (t := i32) nvM6SatState.core.arena ++
  bytesOf (t := i32) nvM6SatState.core.wstk ++
  bytesOf (t := i32) nvM6SatState.scratch.delayed ++
  bytesOf (t := i32) nvM6SatState.scratch.red_refs ++
  bytesOf (t := i32) nvM6SatState.scratch.extend_stk ++
  bytesOf (t := i32) nvM6SatState.scratch.scratch_buf ++
  List.replicate nvM6SatCfg.slack 0

@[expose] def nvM6SatArenaBytes : List UInt8 :=
  nvM6SatBlockHdr ++ nvM6SatBlockBytes ++ nvM6SatBlockU32A ++ nvM6SatBlockU32B ++
  nvM6SatBlockU32C ++ nvM6SatBlockWvec ++ nvM6SatBlockTail

@[expose] def nvM6MemBytes : List UInt8 :=
  nvM6SatBytes ++ bytes64 nvM6ExtInitWords ++ nvM6SatArenaBytes

/-- Concrete `Mem 64` witness mapped at `nvM6CnfPtr = 0x1000#64` holding `nvM6SatBytes` followed
by `M6Hdr`'s `3,456 B` initialized prefix (`M6HdrExtInitOk` with `fullM6HdrMagic` + `FullHdr`)
and verified SAT model `vals = [1#8, 0xFF#8, 1#8, 0xFF#8]` across an `8,192 B` workspace. -/
@[expose] def nvM6Mem : Mem 64 := nvM6MemBytes.At nvM6CnfPtr

private theorem nvM6SatCfg_slack : nvM6SatCfg.slack = 3924 := by
  unfold FullCfg.slack nvM6SatCfg nvM6WorkLen fullM6ExtBytes fullFixedBytes valsBytes
    markBytes u32FullBytes fullMinDepthOf
  decide

private theorem nvJ {bs1 bs2 : List UInt8} {a1 a2 : BitVec 64} {n1 n2 : Nat}
    {P1 P2 : Mem 64 → Prop} (h1 : bs1.length = n1 ∧ P1 (bs1.At a1))
    (h2 : bs2.length = n2 ∧ P2 (bs2.At a2))
    (ha : a2 = a1 + BitVec.ofNat 64 n1 := by decide)
    (hf : n1 + n2 ≤ 2 ^ 64 := by decide) :
    (bs1 ++ bs2).length = n1 + n2 ∧ (P1 ⋆ P2) ((bs1 ++ bs2).At a1) :=
  nv_join_pair h1 h2 ha hf

private theorem nvAP (t : Ty) (a : BitVec 64) (xs : List (Val t)) (n pad : Nat)
    (hl : t.bytes * xs.length = n := by
      simp [nvM6SatState, nvOneLitState, nvOneLitScratch, Ty.bytes, Ty.size])
    (hf : n + pad ≤ 2 ^ 64 := by decide) :
    (bytesOf (t := t) xs ++ List.replicate pad 0).length = n + pad ∧
      (array (t := t) a xs ⋆ region (a + BitVec.ofNat 64 n) pad)
        ((bytesOf (t := t) xs ++ List.replicate pad 0).At a) :=
  nv_arr_pad_p n pad hl hf

private theorem nvA (t : Ty) (a : BitVec 64) (xs : List (Val t)) (n : Nat)
    (hl : t.bytes * xs.length = n := by
      simp [nvM6SatState, nvOneLitState, nvOneLitScratch, Ty.bytes, Ty.size])
    (hf : n ≤ 2 ^ 64 := by decide) :
    (bytesOf (t := t) xs).length = n ∧ array (t := t) a xs ((bytesOf (t := t) xs).At a) :=
  nv_arr_p n hl hf

private theorem nvM6SatArena_ok :
    nvM6SatArenaBytes.length = nvM6SatCfg.avail ∧
      FullMem nvM6SatCfg nvM6SatState (nvM6SatArenaBytes.At nvM6SatCfg.hdr) := by
  have hvb : valsBytes nvM6SatCfg.max_vars - 2 * nvM6SatCfg.max_vars = 4 := by
    unfold valsBytes nvM6SatCfg; decide
  have hmb : markBytes nvM6SatCfg.max_vars - nvM6SatCfg.max_vars = 6 := by
    unfold markBytes nvM6SatCfg; decide
  have hu4 : u32FullBytes nvM6SatCfg.max_vars - 4 * nvM6SatCfg.max_vars = 8 := by
    unfold u32FullBytes nvM6SatCfg; decide
  have hu8 : u32FullBytes nvM6SatCfg.max_vars - 4 * (nvM6SatCfg.max_vars + 1) = 4 := by
    unfold u32FullBytes nvM6SatCfg; decide
  have hHdr := nvJ
    (nv_arr64_p (a := nvM6SatCfg.hdr) (xs := [2#64, 1#64, 0#64, 0#64]) 32 rfl (by decide))
    (nv_arr64_p (a := nvM6SatCfg.hdr + 32) (xs := hdrTailWords nvM6SatCfg nvM6SatState)
      1120 (by rw [hdrTailWords_length]) (by decide)) rfl
  let pB1 : Mem 64 → Prop :=
    region (nvM6SatCfg.pVals + 4#64) 4 ⋆ region (nvM6SatCfg.pWalkVals + 4#64) 4 ⋆
    region (nvM6SatCfg.pLitMark + 4#64) 4 ⋆ region (nvM6SatCfg.pMark + 2#64) 6
  have h1234 := nv_sep_reorg
    (nvJ (nvJ (nvJ (nvAP i8 nvM6SatCfg.pVals nvM6SatState.core.vals 4 4 rfl)
        (nvAP i8 nvM6SatCfg.pWalkVals nvM6SatState.scratch.walk_vals 4 4))
      (nvAP i8 nvM6SatCfg.pLitMark nvM6SatState.core.lit_mark 4 4))
      (nvAP i8 nvM6SatCfg.pMark nvM6SatState.core.mrk 2 6))
    (Q := (FullCoreByteArrs nvM6SatCfg nvM6SatState.core ⋆
      array (t := i8) nvM6SatCfg.pWalkVals nvM6SatState.scratch.walk_vals) ⋆ pB1)
    fun _ hm => nv_zip4 hm
  have hBytes := nv_sep_reorg
    (nvJ (nvJ (nvJ (nvJ h1234 (nvAP i8 nvM6SatCfg.pPhases nvM6SatState.scratch.phases 2 6))
        (nvAP i8 nvM6SatCfg.pPhasesTarget nvM6SatState.scratch.phases_target 2 6))
      (nvAP i8 nvM6SatCfg.pPhasesBest nvM6SatState.scratch.phases_best 2 6))
      (nvAP i8 nvM6SatCfg.pWalkBest nvM6SatState.scratch.walk_best 2 6))
    (Q := FullCoreByteArrs nvM6SatCfg nvM6SatState.core ⋆
      FullScrByteArrs nvM6SatCfg nvM6SatState.scratch ⋆ nvM6SatCfg.padBytes)
    fun _ hm => by
      have hfin := nv_zip4_tail hm
      unfold FullScrByteArrs FullCfg.padBytes
      rw [hvb, hmb, show BitVec.ofNat 64 (2 * nvM6SatCfg.max_vars) = 4#64 from rfl,
        show BitVec.ofNat 64 nvM6SatCfg.max_vars = 2#64 from rfl]
      simpa only [pB1, sep_assoc] using hfin
  have hU32A := nvJ (nvJ (nvJ (nvJ (nvAP i32 nvM6SatCfg.pFlags nvM6SatState.core.flags 8 8)
      (nvAP i32 nvM6SatCfg.pLevel nvM6SatState.core.lvl 8 8))
    (nvAP i32 nvM6SatCfg.pReason nvM6SatState.core.rsns 8 8))
    (nvAP i32 nvM6SatCfg.pTrail nvM6SatState.core.trl 8 8))
    (nvAP i32 nvM6SatCfg.pTrailPos nvM6SatState.core.trail_pos 8 8)
  have hU32B := nvJ (nvJ (nvJ (nvJ (nvAP i32 nvM6SatCfg.pTmp nvM6SatState.core.tmp 8 8)
      (nvAP i32 nvM6SatCfg.pHeap nvM6SatState.scratch.heap 8 8))
    (nvAP i32 nvM6SatCfg.pPos nvM6SatState.scratch.pos 8 8))
    (nvAP i32 nvM6SatCfg.pMinClr nvM6SatState.core.min_clr 8 8))
    (nvAP i32 nvM6SatCfg.pShrinkStk nvM6SatState.scratch.shrink_stk 8 8)
  have hU32C := nvJ (nvJ (nvJ (nvJ (nvAP i32 nvM6SatCfg.pQPrev nvM6SatState.scratch.q_prev 8 8)
      (nvAP i32 nvM6SatCfg.pQNext nvM6SatState.scratch.q_next 8 8))
    (nvAP i32 nvM6SatCfg.pQStamp nvM6SatState.scratch.q_stamp 8 8))
    (nvAP i32 nvM6SatCfg.pFrameTrail nvM6SatState.core.frame_trail 12 4))
    (nvAP i32 nvM6SatCfg.pFrameDec nvM6SatState.core.frame_dec 12 4)
  have hWvec := nvJ (nvJ (nvJ (nvJ (nvJ (nvJ (nvJ (nvJ
      (nvA i32 nvM6SatCfg.pWvec nvM6SatState.core.wvec 32)
      (nvA i32 nvM6SatCfg.pRepr nvM6SatState.core.repr 16))
    (nvA i32 nvM6SatCfg.pWsort nvM6SatState.scratch.wsort 16))
    (nvA i32 nvM6SatCfg.pWorkStk1 nvM6SatState.scratch.work_stk1 16))
    (nvA i32 nvM6SatCfg.pWorkStk2 nvM6SatState.scratch.work_stk2 16))
    (nvA i32 nvM6SatCfg.pTarjanMark nvM6SatState.scratch.tarjan_mark 16))
    (nvA i32 nvM6SatCfg.pTarjanReach nvM6SatState.scratch.tarjan_reach 16))
    (nv_arr64_p (a := nvM6SatCfg.pScore) (xs := nvM6SatState.scratch.score) 16 rfl (by decide)))
    (nv_arr64_p (a := nvM6SatCfg.pSimSig) (xs := nvM6SatState.scratch.sim_sig) 16 rfl (by decide))
  have hSlack : (List.replicate nvM6SatCfg.slack (0 : UInt8)).length = 3924 ∧
      region nvM6SatCfg.pSlack nvM6SatCfg.slack
        ((List.replicate nvM6SatCfg.slack 0).At nvM6SatCfg.pSlack) :=
    ⟨by rw [List.length_replicate, nvM6SatCfg_slack],
      ⟨List.replicate nvM6SatCfg.slack 0, List.length_replicate, rfl⟩⟩
  have hTail := nvJ (nvJ (nvJ (nvJ (nvJ (nvJ (nvJ (nvJ (nvJ
      (nvA i32 nvM6SatCfg.pMinStk nvM6SatState.core.min_stk 24)
      (nvA i32 nvM6SatCfg.pGlueUsed nvM6SatState.scratch.glue_used 256))
    (nvA i32 nvM6SatCfg.pLastLearned nvM6SatState.scratch.last_learned 64))
    (nvA i32 nvM6SatCfg.pArena nvM6SatState.core.arena 0))
    (nvA i32 nvM6SatCfg.pWstk nvM6SatState.core.wstk 4))
    (nvA i32 nvM6SatCfg.pDelayed nvM6SatState.scratch.delayed 0))
    (nvA i32 nvM6SatCfg.pRedRefs nvM6SatState.scratch.red_refs 0))
    (nvA i32 nvM6SatCfg.pExtendStk nvM6SatState.scratch.extend_stk 0))
    (nvA i32 nvM6SatCfg.pScratchBuf nvM6SatState.scratch.scratch_buf 0)) hSlack
  have h06 := nv_sep_reorg
    (nvJ (nvJ (nvJ (nvJ (nvJ (nvJ hHdr hBytes) hU32A) hU32B) hU32C) hWvec) hTail
      (by decide) (by omega))
    (Q := FullMem nvM6SatCfg nvM6SatState) fun _ hm => by
      unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
        FullScrWksArrs FullCoreDynArrs FullScrDynArrs FullScrMetaArrs FullCfg.pad
        FullCfg.padU32A FullCfg.padU32B FullCfg.padU32C dimacsState
      rw [hu4, hu8, show BitVec.ofNat 64 (4 * nvM6SatCfg.max_vars) = 8#64 from rfl,
        show BitVec.ofNat 64 (4 * (nvM6SatCfg.max_vars + 1)) = 12#64 from rfl]
      exact sep_ac hm
  exact ⟨show nvM6SatArenaBytes.length = nvM6SatCfg.avail from h06.1, h06.2⟩

theorem nvM6Mem_ok :
    (bytes nvM6CnfPtr nvM6SatBytes ⋆
      FullM6HdrMem nvM6SatCfg nvM6ExtInitWords nvM6SatState) nvM6Mem := by
  have hExt := nv_arr64_p (a := nvM6SatWorkPtr) (xs := nvM6ExtInitWords) 2304
    (by rw [nvM6ExtInitWords_len]; rfl) (by decide)
  have hav : nvM6SatCfg.avail = 5888 := rfl
  have hM6 := nv_sep_reorg
    (nvJ hExt nvM6SatArena_ok rfl (by rw [hav]; decide))
    (Q := FullM6HdrMem nvM6SatCfg nvM6ExtInitWords nvM6SatState) fun _ hm =>
      fullM6HdrMem_mk (by rw [show nvM6SatCfg.hdr - 2304 = nvM6SatWorkPtr from rfl]; exact hm)
  exact (nvJ ⟨rfl, rfl⟩ hM6 rfl (by rw [hav]; decide)).2

theorem nvM6Mem_region :
    (bytes nvM6CnfPtr nvM6SatBytes ⋆ region nvM6SatWorkPtr nvM6WorkLen) nvM6Mem := by
  have hm := nvM6Mem_ok
  refine sep_mono_r (fun _ hr => ?_) hm
  have hr_m6 := fullM6HdrMem_to_region nvM6SatCfg_ok nvM6ExtInitWords_ok
    nvM6Sat_lengths hr
  have haddr : m6ExtAddr nvM6SatCfg.hdr = nvM6SatWorkPtr := by
    rw [m6ExtAddr_eq]; rfl
  have hsz : fullM6ExtBytes + nvM6SatCfg.avail = nvM6WorkLen := rfl
  rwa [haddr, hsz] at hr_m6

theorem nvM6Mem_readModel_1 : readModelFromWorkM6 nvM6Mem nvM6SatWorkPtr 1 = true := by
  rw [readModelFromWorkM6_of_vals (c := nvM6SatCfg) (ext := nvM6ExtInitWords) (s := nvM6SatState)
    (R := bytes nvM6CnfPtr nvM6SatBytes) (F := emp) (work_ptr := nvM6SatWorkPtr) rfl
    nvM6Sat_lengths (sep_ac nvM6Mem_ok) (by rw [Std.ExtHashMap.sep_emp]) (v := 1) (by omega)
    (by decide)]; decide

theorem nvM6Mem_readModel_2 : readModelFromWorkM6 nvM6Mem nvM6SatWorkPtr 2 = true := by
  rw [readModelFromWorkM6_of_vals (c := nvM6SatCfg) (ext := nvM6ExtInitWords) (s := nvM6SatState)
    (R := bytes nvM6CnfPtr nvM6SatBytes) (F := emp) (work_ptr := nvM6SatWorkPtr) rfl
    nvM6Sat_lengths (sep_ac nvM6Mem_ok) (by rw [Std.ExtHashMap.sep_emp]) (v := 2) (by omega)
    (by decide)]; decide

theorem nvM6Mem_sat : nvM6SatCnf.Sat (readModelFromWorkM6 nvM6Mem nvM6SatWorkPtr) := by
  rw [nvM6SatCnf, CNF.sat_add]
  refine ⟨?_, CNF.sat_empty⟩
  rw [CNF.Clause.sat_iff_exists_mem_eq]
  exact ⟨(1, true), by rw [← CNF.Clause.mem_literals_iff]; simp, nvM6Mem_readModel_1⟩


@[expose] def m6NvWorkLen : Nat := 6144

theorem m6NvWorkLen_eq : m6NvWorkLen = 6144 := rfl

@[expose] def m6NvPayload (cnfBytes : List UInt8) : List UInt8 :=
  cnfBytes ++ List.replicate m6NvWorkLen 0

theorem m6NvPayload_eq (cnfBytes : List UInt8) :
    m6NvPayload cnfBytes = cnfBytes ++ List.replicate 6144 0 := rfl

theorem m6NvPayload_length (cnfBytes : List UInt8) :
    (m6NvPayload cnfBytes).length = cnfBytes.length + m6NvWorkLen := by
  simp only [m6NvPayload, List.length_append, List.length_replicate]

theorem m6NvPayload_sep (cnfBytes : List UInt8) (hcb : cnfBytes.length ≤ 2048) :
    (bytes nvM6CnfPtr cnfBytes ⋆ region (fullNvWorkPtr cnfBytes) m6NvWorkLen)
      ((m6NvPayload cnfBytes).At nvM6CnfPtr) :=
  nv_sep_append rfl
    (by unfold m6NvWorkLen; rw [List.length_replicate]; omega)
    rfl ⟨List.replicate m6NvWorkLen 0, List.length_replicate, rfl⟩

theorem m6Nv_unsat_bound :
    fullM6ExtBytes + fullFixedBytes 1 + 2 * 40 + 136 + 8 ≤ m6NvWorkLen := by
  unfold m6NvWorkLen fullM6ExtBytes fullFixedBytes valsBytes markBytes
    u32FullBytes fullMinDepthOf
  decide


/-- Canonical UNSAT + deterministic `UnitUnsatTrace` demand for `kissat_solve_bytes`. -/
@[expose] def CommonUnsatSolveReq
    (cnfBytes : List UInt8) (cnf_ptr work_ptr fuel : BitVec 64) (wlen : Nat)
    (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ r m',
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
    (∀ mv nc i0,
      cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
      fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen →
      i0 ≤ cnfBytes.length →
      parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
      UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
      r = 20#64) →
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
    Q (r, ()) m'

/-- Milestone-level arch-free UNSAT solver witness package (provided once per M8+ milestone). -/
structure KissatUnsatPkg where
  mod : Module
  inlPolicy : InlinePolicy
  entryFn : Sym := "kissat_solve_bytes"
  entryFn_fn : Fn
  entryFn_sig : entryFn_fn.name = entryFn ∧ entryFn_fn.as = [i64, i64, i64, i64, i64] ∧
    entryFn_fn.rs = [i64]
  entry_mem : entryFn_fn ∈ mod.fns
  env : Env
  moduleOk : ModuleOk env mod
  noExit : ∀ f ∈ mod.fns, ∀ args m Q X X',
    env f.name f.as f.rs args m Q X → env f.name f.as f.rs args m Q X'
  solve_intro : ∀ {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost},
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 →
    work_ptr.toNat + wlen < 2 ^ 64 →
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m →
    CommonUnsatSolveReq cnfBytes cnf_ptr work_ptr fuel wlen R Q →
    env entryFn [i64, i64, i64, i64, i64] [i64]
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ())
      m Q X


/-- Transparent UNSAT-only `kissat_solve_bytes` contract (`r ∈ {0, 10, 20}`,
`r = 20 → cnf.Unsat`, deterministic `UnitUnsatTrace → r = 20`, frame `R`; zero SAT proofs). -/
@[expose] def m7FidSolveBytesSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (∀ mv nc i0,
          cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
          fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen →
          i0 ≤ cnfBytes.length →
          parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
          r = 20#64) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
        Q (r, ()) m'

theorem m7FidSolveBytesSpec_intro {cnf_ptr work_ptr fuel : BitVec 64}
    {cnfBytes : List UInt8} {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m)
    (hQ : ∀ r m',
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
      (∀ mv nc i0,
        cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
        fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen →
        i0 ≤ cnfBytes.length →
        parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
        UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
        r = 20#64) →
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' → Q (r, ()) m') :
    m7FidSolveBytesSpec
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ())
      m Q X :=
  ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, hQ⟩

theorem m7FidSolveBytesSpec_monoX
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : m7FidSolveBytesSpec xs m Q X) :
    m7FidSolveBytesSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, _, ⟨⟩⟩; exact h

theorem m7FidSolveBytesSpec_to_coreModel
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : m7FidSolveBytesSpec xs m Q X) :
    fullM6SolveBytesCoreModelSpec xs m Q X := by
  rcases xs with ⟨cp, cl, wp_, wl, fu, ⟨⟩⟩
  obtain ⟨cbs, wlen, R, rfl, rfl, hcf, hwf, hm, hQ⟩ := h
  exact fullM6SolveBytesCoreModelSpec_intro hcf hwf hm fun r m' hd hu _ htr hm' =>
    hQ r m' hd hu htr hm'


/-- Generic byte-level UNSAT soundness for any `kissat_solve_bytes` function `body` in `M.fns`
under `ModuleOk Γ M` and `m7FidSolveBytesSpec`. -/
theorem fid_solve_bytes_sound_of_fn {Γ : Env} {M : LeanQbe.T.Module}
    {body : Func [i64, i64, i64, i64, i64] [i64]}
    (hM : ModuleOk Γ M)
    (hMem : (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], body⟩ : Fn) ∈ M.fns)
    (hSb : ∀ a m Q X, m7FidSolveBytesSpec a m Q X →
      Γ "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp Γ body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hMem
  have hfn := (hM.fnsOk pre _ post hsplit).2.2
  refine hfn _ m _ (fun _ _ _ _ => False)
    (hSb _ m _ _ (m7FidSolveBytesSpec_intro hcfit hwfit hm ?_))
  intro r m' hdom h20 _ hm'
  exact ⟨hdom, h20, hm'⟩


/-- Host-framed machine-memory UNSAT lift (`(Eq m' ⋆ F_host) st_dmem`). -/
theorem fid_solve_bytes_host_sound
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hpost :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hhost : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem :=
  ⟨hpost.1, hpost.2.1, sep_mono (fun _ hm0 => by subst hm0; exact hpost.2.2) hhost⟩

/-- Generic concrete `8,192 B` `Mem 64` UNSAT non-vacuity (`r = 20#64`, `XPost := False`) for any
`kissat_solve_bytes` function `body` in `M.fns`. -/
theorem fid_unsat_nv_of_fn {Γ : Env} {M : LeanQbe.T.Module}
    {body : Func [i64, i64, i64, i64, i64] [i64]}
    (hM : ModuleOk Γ M)
    (hMem : (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], body⟩ : Fn) ∈ M.fns)
    (hSb : ∀ a m Q X, m7FidSolveBytesSpec a m Q X →
      Γ "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    Func.wp Γ body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hMem
  have hfn := (hM.fnsOk pre _ post hsplit).2.2
  have hm0 :
      (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen ⋆ emp)
        nvM6UnsatInitMem := by
    rw [Std.ExtHashMap.sep_emp]
    exact nvM6UnsatInitMem_sep
  refine hfn _ nvM6UnsatInitMem _ (fun _ _ _ _ => False)
    (hSb _ nvM6UnsatInitMem _ _ (m7FidSolveBytesSpec_intro (by decide) (by decide) hm0 ?_))
  intro r m' _ _ htr hm'
  have hr20 := htr 1 2 9 (by decide) (by decide) (by decide) nvM6_unsat_bound (by decide)
    nvM6Unsat_header nvM6Unsat_unitTrace
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨hr20, nvM6UnsatCnf_unsat, hm'⟩


/-- Reconstructs `M.checkAcyclic = true` in `O(1)` from `ModuleOk Γ M`. -/
theorem moduleCheckAcyclic_of_moduleOk {Γ : Env} {M : LeanQbe.T.Module}
    (hM : ModuleOk Γ M) : M.checkAcyclic = true := by
  simp only [LeanQbe.T.Module.checkAcyclic, Bool.and_eq_true]
  refine ⟨listNodup_iff.mpr hM.nodup,
    checkFnsCallsOk_of_forall _ _ [] _ fun pre fn post hsp => ?_⟩
  simpa using (hM.fnsOk pre fn post hsp).2.1


private theorem nvM6_mem_init_of (Γ : Env)
    (hinit : ∀ a m Q X, fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hm6 : ∀ a m Q X, m6HdrInitSpec a m Q X → Γ "m6_hdr_init" [i64] [] a m Q X)
    {cnfBytes : List UInt8} {workPtr : BitVec 64} {initMem : Mem 64} {mv nc : Nat}
    (hle : fullAlignPad workPtr + fullM6HdrTotalBytes ≤ nvM6WorkLen)
    (hfit : nvM6WorkLen ≤ 2 ^ 64)
    (hsep : (bytes nvM6CnfPtr cnfBytes ⋆ region workPtr nvM6WorkLen) initMem)
    (hcfit : nvM6CnfPtr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : (fullM6WorkBase workPtr).toNat + (nvM6WorkLen - fullAlignPad workPtr) < 2 ^ 64)
    (hnotsmall : ¬ (nvM6WorkLen - fullAlignPad workPtr <
      fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 + 8))
    (hnothdr : ¬ (nvM6WorkLen - fullAlignPad workPtr < fullM6HdrTotalBytes))
    (hph : parseHeader cnfBytes = some (mv, nc, cnfBytes.drop 9))
    (hlen9 : 9 ≤ cnfBytes.length) :
    Func.wp Γ Src.Internal.full_m6_mem_init_body
      (nvM6CnfPtr, nvM6CnfPtr + BitVec.ofNat 64 cnfBytes.length,
        fullM6WorkBase workPtr,
        BitVec.ofNat 64 (nvM6WorkLen - fullAlignPad workPtr), 16#64, ())
      initMem
      (fun rs m' =>
        match rs with
        | (hdr, ()) =>
          ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState),
            hdr = c.hdr ∧ c.hdr = fullM6WorkHdr workPtr ∧
            c.avail = nvM6WorkLen - fullAlignPad workPtr - fullM6ExtBytes ∧
            c.mv = mv ∧ c.nc = nc ∧
            FullM6HdrCfgOk c ∧ M6HdrExtInitOk ext ∧
            FullM6HdrInv c (shiftDownCnf CNF.empty) ext s ∧
            s.core.cur_vars = c.mv ∧
            s.core.d_cur = nvM6CnfPtr + 9#64 ∧
            s.core.arena_len = 0 ∧ s.core.wlen = 1 ∧ s.core.trail_end = 0 ∧
            s.core.propagated = 0 ∧ s.core.cur_level = 0 ∧ s.core.fuel = 16#64 ∧
            s.core.oom = 0#64 ∧ s.core.inconsistent = 0#64 ∧
            (bytes nvM6CnfPtr cnfBytes ⋆ FullM6HdrMem c ext s ⋆
              region workPtr (fullAlignPad workPtr)) m')
      (fun _ _ _ _ => False) := by
  have hbnat : (BitVec.ofNat 64 (nvM6WorkLen - fullAlignPad workPtr)).toNat =
      nvM6WorkLen - fullAlignPad workPtr := bv64_ofNat_toNat (by unfold nvM6WorkLen; omega)
  have hm : (bytes nvM6CnfPtr cnfBytes ⋆
      region (fullM6WorkBase workPtr) (BitVec.ofNat 64 (nvM6WorkLen - fullAlignPad workPtr)).toNat ⋆
      region workPtr (fullAlignPad workPtr)) initMem := by
    rw [hbnat]
    exact sep_ac (sep_mono_r (fun _ hr => region_work_to_m6_workBase hle hfit hr) hsep)
  refine full_m6_mem_init_wp Γ hinit hm6 _ _ _ _
    (fullM6MemInitSpec_of rfl hcfit (by rwa [hbnat]) hm
      (fun _ _ hfail => by
        rcases hfail with hlt | hsmall
        · rw [hbnat] at hlt; exact absurd hlt hnothdr
        · have h := hsmall mv nc _ hph; rw [hbnat] at h; omega)
      (fun c ext s j rest _ hhdr hav hcfg hext hph' hj hd hinv hcv hdcur hal hw hte hpr hcl
        hfu hoom hinc hm' => by
        rw [hph, Option.some.injEq, Prod.mk.injEq] at hph'
        rcases hph' with ⟨hmv, hncr⟩
        rw [Prod.mk.injEq] at hncr
        rcases hncr with ⟨hnc, hrest⟩
        have hrest_len : (cnfBytes.drop j).length = (cnfBytes.drop 9).length := by rw [hd, hrest]
        have hj9 : j = 9 := by simp only [List.length_drop] at hj hrest_len; omega
        subst hj9
        have hc_avail : c.avail = nvM6WorkLen - fullAlignPad workPtr - fullM6ExtBytes := by
          rw [hav, hbnat]
        exact ⟨c, ext, s, rfl, hhdr.trans rfl, hc_avail, hmv.symm, hnc.symm, hcfg, hext, hinv,
          hcv, hdcur, hal, hw, hte, hpr, hcl, hfu, hoom, hinc, hm'⟩))

/-- Parametric C0 `full_m6_mem_init` execution (`XPost := False`, `0` vacuous hypotheses) on
concrete `8 KiB` `nvM6UnsatInitMem` (`(x1) ∧ (~x1)`, `pad = 5`, `avail = 8187`). -/
theorem nvM6_unsat_full_m6_mem_init_of (Γ : Env)
    (hinit : ∀ a m Q X, fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hm6 : ∀ a m Q X, m6HdrInitSpec a m Q X →
      Γ "m6_hdr_init" [i64] [] a m Q X) :
    Func.wp Γ Src.Internal.full_m6_mem_init_body
      (nvM6CnfPtr, nvM6CnfPtr + BitVec.ofNat 64 nvM6UnsatBytes.length,
        fullM6WorkBase nvM6UnsatWorkPtr,
        BitVec.ofNat 64 (nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr), 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (hdr, ()) =>
          ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState),
            hdr = c.hdr ∧ c.hdr = fullM6WorkHdr nvM6UnsatWorkPtr ∧
            c.avail = nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr - fullM6ExtBytes ∧
            c.mv = 1 ∧ c.nc = 2 ∧
            FullM6HdrCfgOk c ∧ M6HdrExtInitOk ext ∧
            FullM6HdrInv c (shiftDownCnf CNF.empty) ext s ∧
            s.core.cur_vars = c.mv ∧
            s.core.d_cur = nvM6CnfPtr + 9#64 ∧
            s.core.arena_len = 0 ∧ s.core.wlen = 1 ∧ s.core.trail_end = 0 ∧
            s.core.propagated = 0 ∧ s.core.cur_level = 0 ∧ s.core.fuel = 16#64 ∧
            s.core.oom = 0#64 ∧ s.core.inconsistent = 0#64 ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ FullM6HdrMem c ext s ⋆
              region nvM6UnsatWorkPtr (fullAlignPad nvM6UnsatWorkPtr)) m')
      (fun _ _ _ _ => False) :=
  nvM6_mem_init_of Γ hinit hm6 (by decide) (by unfold nvM6WorkLen; omega) nvM6UnsatInitMem_sep
    (by decide) (by decide)
    (by unfold nvM6WorkLen fullM6ExtBytes fullFixedBytes valsBytes markBytes u32FullBytes
          fullMinDepthOf; decide)
    (by decide) nvM6Unsat_header (by decide)


/-! ## 4. Concrete Tier-3b Non-Vacuity Theorems (`fullM6_unsat_nv`, `fullM6_sat_nv`) -/

/-- **Concrete Tier-3b UNSAT Non-Vacuity (`fullM6_unsat_nv`)**:
For ANY `solveBody` satisfying `fullM6SolveBytesCoreModelSpec` on concrete `8,192 B`
`nvM6UnsatInitMem` (`(x1) ∧ (~x1)`, `M6Hdr` `3,456 B` layout, `pad = 5`), all preconditions
are concretely satisfiable (`0` vacuous hypotheses, `XPost := False`), deterministically yielding
`r = 20#64`, `nvM6UnsatCnf.Unsat`, and restored workspace region. -/
theorem fullM6_unsat_nv (Γ : Env) (solveBody : Func [i64, i64, i64, i64, i64] [i64])
    (hwp : ∀ (a : Tup Val [i64, i64, i64, i64, i64]) (m : Mem 64)
      (Q : Post [i64]) (X : XPost),
      fullM6SolveBytesCoreModelSpec a m Q X → Func.wp Γ solveBody a m Q X) :
    Func.wp Γ solveBody
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  have hm0 : (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen ⋆ emp)
      nvM6UnsatInitMem := by
    rw [Std.ExtHashMap.sep_emp]
    exact nvM6UnsatInitMem_sep
  refine hwp _ _ _ _ (fullM6SolveBytesCoreModelSpec_intro (by decide) (by decide) hm0
    fun r m' _ _ _ htr hm' => ?_)
  have hr20 : r = 20#64 := htr 1 2 9 (by decide) (by decide) (by decide) nvM6_unsat_bound
    (by decide) nvM6Unsat_header nvM6Unsat_unitTrace
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨hr20, nvM6UnsatCnf_unsat, hm'⟩

/-- **Concrete Tier-3b SAT Non-Vacuity (`fullM6_sat_nv`)**:
For ANY `solveBody` satisfying `fullM6SolveBytesSpec` on concrete `8,192 B` `nvM6SatInitMem`
(`(x1 ∨ x2)`, `M6Hdr` `3,456 B` layout), all preconditions are concretely satisfiable (`0` vacuous
hypotheses, `XPost := False`): `r = 20#64` is impossible (`¬ nvM6SatCnf.Unsat`), `r ∈ {0, 10}`,
and `r = 10#64` guarantees constructive `nvM6SatCnf.Sat (readModelFromWorkM6 M nvM6SatWorkPtr)`
for every host memory extension `(Eq m' ⋆ F) M`. -/
theorem fullM6_sat_nv (Γ : Env) (solveBody : Func [i64, i64, i64, i64, i64] [i64])
    (hwp : ∀ (a : Tup Val [i64, i64, i64, i64, i64]) (m : Mem 64)
      (Q : Post [i64]) (X : XPost),
      fullM6SolveBytesSpec a m Q X → Func.wp Γ solveBody a m Q X) :
    Func.wp Γ solveBody
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6SatBytes.length,
        nvM6SatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6SatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64) ∧ r ≠ 20#64 ∧
          (r = 10#64 →
            ¬ nvM6SatCnf.Unsat ∧
            (∀ (F : Mem 64 → Prop) (M : Mem 64),
              (Eq m' ⋆ F) M → nvM6SatCnf.Sat (readModelFromWorkM6 M nvM6SatWorkPtr))) ∧
          (bytes nvM6CnfPtr nvM6SatBytes ⋆ region nvM6SatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  have hm0 : (bytes nvM6CnfPtr nvM6SatBytes ⋆ region nvM6SatWorkPtr nvM6WorkLen ⋆ emp)
      nvM6SatInitMem := by
    rw [Std.ExtHashMap.sep_emp]
    exact nvM6SatInitMem_sep
  refine hwp _ _ _ _ (fullM6SolveBytesSpec_intro (by decide) (by decide) hm0 ?_)
  intro r m' hdom h20 h10 hm'
  have hrne20 : r ≠ 20#64 := fun h20eq => by
    obtain ⟨cnf, hp, hu⟩ := h20 h20eq
    rw [parseDimacs_nvM6SatBytes, Option.some.injEq] at hp; subst hp
    exact nvM6SatCnf_not_unsat hu
  have hdom' : r = 0#64 ∨ r = 10#64 := by
    rcases hdom with rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr rfl | exact absurd rfl hrne20
  refine ⟨hdom', hrne20, fun hr10 => ?_, by rwa [Std.ExtHashMap.sep_emp] at hm'⟩
  obtain ⟨cnf, hp, hsat⟩ := h10 hr10
  rw [parseDimacs_nvM6SatBytes, Option.some.injEq] at hp; subst hp
  exact ⟨nvM6SatCnf_not_unsat, hsat⟩


end LeanQbe.T.Examples.Kissat.Proof.Spec
