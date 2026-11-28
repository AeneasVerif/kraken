/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.SatNv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Solver
public import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
public import LeanQbe.T.InlineLemmas
public import LeanQbe.T.Logic.Bytes
public import LeanQbe.T.Logic.MemLemmas
public import Std.Sat.CNF.Basic
public import Kraken.Mem
public import Kraken.Separation

/-!
# Kissat Concrete UNSAT Non-Vacuity & Assembly UNSAT Lift (`Proof.Spec.SatNv1`)

1. Concrete `8,192 B` / `6,144 B` `Mem 64` UNSAT payloads and witnesses (`nvM6UnsatInitMem`,
   `m6NvWorkLen`, `m6NvPayload`) plus shared array-packing helpers (`nvOneLit*`, `nv_arr*`,
   `nv_join_pair`, `nv_sep_reorg`, `nv_zip4*`).
2. `CommonUnsatSolveReq`, `KissatUnsatPkg`, and generic UNSAT soundness / non-vacuity lifts
   (`fid_solve_bytes_sound_of_fn`, `fid_solve_bytes_host_sound`, `fid_unsat_nv_of_fn`,
   `moduleCheckAcyclic_of_moduleOk`, `fullM6_unsat_nv`) backed by canonical
   `Proof.Spec.Solver.solveBytesSpec`.
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


/-! ## 1. Concrete UNSAT Formulas & `8,192 B` / `6,144 B` Host Payloads -/

@[expose] def nvM6CnfPtr : BitVec 64 := 0x1000#64

@[expose] def nvM6WorkLen : Nat := 8192

/-- Concrete UNSAT DIMACS `"p cnf 1 2\n1 0\n-1 0\n"` (`(x1) ∧ (~x1)`, `19` bytes). -/
@[expose] def nvM6UnsatBytes : List UInt8 := fullNvUnsatBytes

@[expose] def nvM6UnsatCnf : CNF Nat := fullNvUnsatCnf

@[expose] def nvM6UnsatWorkPtr : BitVec 64 :=
  nvM6CnfPtr + BitVec.ofNat 64 nvM6UnsatBytes.length

@[expose] def nvM6UnsatInitMem : Mem 64 :=
  (nvM6UnsatBytes ++ List.replicate nvM6WorkLen 0).At nvM6CnfPtr

theorem nvM6UnsatWorkPtr_eq_fullNvWorkPtr :
    nvM6UnsatWorkPtr = fullNvWorkPtr nvM6UnsatBytes := rfl

theorem nvM6Unsat_pad_eq : fullAlignPad nvM6UnsatWorkPtr = 5 := by decide

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


/-! ## 2. Arch-Free `KissatUnsatPkg` & Generic UNSAT Soundness / NV Lifts -/

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

/-- Generic byte-level UNSAT soundness for any `kissat_solve_bytes` function `body` in `M.fns`
under `ModuleOk Γ M` and canonical `Solver.solveBytesSpec`. -/
theorem fid_solve_bytes_sound_of_fn {Γ : Env} {M : LeanQbe.T.Module}
    {body : Func [i64, i64, i64, i64, i64] [i64]}
    (hM : ModuleOk Γ M)
    (hMem : (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], body⟩ : Fn) ∈ M.fns)
    (hSb : ∀ a m Q X, Solver.solveBytesSpec a m Q X →
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
  refine hfn _ m _ (fun _ _ _ _ => False) (hSb _ m _ _ ?_)
  unfold Solver.solveBytesSpec
  refine FnContract.intro (cnfBytes, wlen) R ⟨rfl, rfl, hcfit, hwfit⟩ hm ?_
  rintro ⟨r, ⟨⟩⟩ ⟨⟩ m' ⟨hdom, h20, _⟩ hm'
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
`kissat_solve_bytes` function `body` in `M.fns` backed by `Solver.solveBytesSpec`. -/
theorem fid_unsat_nv_of_fn {Γ : Env} {M : LeanQbe.T.Module}
    {body : Func [i64, i64, i64, i64, i64] [i64]}
    (hM : ModuleOk Γ M)
    (hMem : (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], body⟩ : Fn) ∈ M.fns)
    (hSb : ∀ a m Q X, Solver.solveBytesSpec a m Q X →
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
  refine hfn _ nvM6UnsatInitMem _ (fun _ _ _ _ => False) (hSb _ nvM6UnsatInitMem _ _ ?_)
  unfold Solver.solveBytesSpec
  refine FnContract.intro (nvM6UnsatBytes, nvM6WorkLen) emp ⟨rfl, rfl, by decide, by decide⟩
    hm0 ?_
  rintro ⟨r, ⟨⟩⟩ ⟨⟩ m' ⟨_, _, htr⟩ hm'
  have hr20 := htr ⟨1, 2, 9, by decide, by decide, by decide, nvM6_unsat_bound, by decide,
    nvM6Unsat_header, nvM6Unsat_unitTrace⟩
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨hr20, nvM6UnsatCnf_unsat, hm'⟩

/-- Reconstructs `M.checkAcyclic = true` in `O(1)` from `ModuleOk Γ M`. -/
theorem moduleCheckAcyclic_of_moduleOk {Γ : Env} {M : LeanQbe.T.Module}
    (hM : ModuleOk Γ M) : M.checkAcyclic = true := by
  simp only [LeanQbe.T.Module.checkAcyclic, Bool.and_eq_true]
  refine ⟨listNodup_iff.mpr hM.nodup,
    checkFnsCallsOk_of_forall _ _ [] _ fun pre fn post hsp => ?_⟩
  simpa using (hM.fnsOk pre fn post hsp).2.1

/-- Concrete Tier-3b UNSAT non-vacuity (`fullM6_unsat_nv`):
For ANY `solveBody` satisfying `Solver.solveBytesSpec` on concrete `8,192 B`
`nvM6UnsatInitMem` (`(x1) ∧ (~x1)`), deterministically yields `r = 20#64`, `nvM6UnsatCnf.Unsat`,
and restored workspace region (`XPost := False`, `<= std3`). -/
theorem fullM6_unsat_nv (Γ : Env) (solveBody : Func [i64, i64, i64, i64, i64] [i64])
    (hwp : ∀ (a : Tup Val [i64, i64, i64, i64, i64]) (m : Mem 64)
      (Q : Post [i64]) (X : XPost),
      Solver.solveBytesSpec a m Q X → Func.wp Γ solveBody a m Q X) :
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
  refine hwp _ _ _ _ ?_
  unfold Solver.solveBytesSpec
  refine FnContract.intro (nvM6UnsatBytes, nvM6WorkLen) emp ⟨rfl, rfl, by decide, by decide⟩
    hm0 ?_
  rintro ⟨r, ⟨⟩⟩ ⟨⟩ m' ⟨_, _, htr⟩ hm'
  have hr20 := htr ⟨1, 2, 9, by decide, by decide, by decide, nvM6_unsat_bound, by decide,
    nvM6Unsat_header, nvM6Unsat_unitTrace⟩
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨hr20, nvM6UnsatCnf_unsat, hm'⟩

end LeanQbe.T.Examples.Kissat.Proof.Spec
