/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullSatSound
import LeanQbe.T.Examples.Kissat.FullParseInitLemmas1
import LeanQbe.T.Examples.Kissat.FullParseInitLemmas2
import LeanQbe.T.Examples.Kissat.FullAssignAddLemmas1
import Kraken.Mem
import Kraken.Separation

/-!
# Concrete `Mem 64` SAT Non-Vacuity for Unified Kissat M5 (`FullM5SatNv`)

Proves end-to-end concrete `Mem 64` SAT non-vacuity (`r = 10#64`, `XPost := False`, `std3`) on
the non-empty 1-variable, 1-clause formula `"p cnf 1 1\n1 0\n"` (`fullNvSatBytes`, `14` bytes)
with a `4096`-byte workspace and `fuel = 16`:

1. Generic disjunctive-environment transport `moduleOk_or_env`: transports all `252` untouched
   search/inprocessing/analysis functions verbatim from `FullM5.m5Env_moduleOk` into the closed
   `270`-function environment `m5SatNvEnv`.
2. Lightweight concrete-trace `Func.wp` proofs for the `18` functions executed on
   `"p cnf 1 1\n1 0\n"` (`full_init_hdr`, `full_zero_tables2`, `full_assign_lvl`,
   `full_calc_ext_cap_m5`, `full_calc_scr_cap_m5`, `full_init_state_m5`, `full_ingest_cl`,
   `full_parse_body`, `full_prop_lit_raw`, `full_propagate_ignore`, `full_propagate`,
   `full_sweep_bins`, `full_rewatch_arena`, `full_arena_sweep`, `full_extend`,
   `full_preprocess_m5`, `kissat_solve_bytes_m5`, `kissat_solve_bytes`).
3. Closed `m5SatNvEnv_moduleOk : ModuleOk m5SatNvEnv FullM5.m5Module`, `m5_sat_nonvacuous_m5`,
   and `m5_sat_nonvacuous` certifying `r = 10#64` AND `fullNvSatCnf.Sat (readModelFromWork m'
   (fullNvWorkPtr fullNvSatBytes))` on `(fullPayload fullNvSatBytes).At fullNvCnfPtr`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.Full hiding
  full_init_state_body full_init_state_wf
  full_reduce_body full_reduce_wf
  full_preprocess_body full_preprocess_wf
  full_search_body full_search_wf
  kissat_solve_bytes_body kissat_solve_bytes_full_wf
  full_add_bin_body full_add_bin_wf
  full_propagate_body full_propagate_wf
  full_propagate_ignore_body full_propagate_ignore_wf
  full_extend_body full_extend_wf
open Kraken.Bedrock2.Test

/-! ## 1. Concrete SAT Input `"p cnf 1 1\n1 0\n"` & Pure Decidable Facts -/

/-- Concrete non-empty SAT DIMACS input (`"p cnf 1 1\n1 0\n"`, `14` bytes). -/
def fullNvSatBytes : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 49, 32, 49, 10, 49, 32, 48, 10]

/-- Parsed `Std.Sat.CNF Nat` for `fullNvSatBytes`: single positive unit clause `[+1]`. -/
def fullNvSatCnf : CNF Nat :=
  CNF.empty.add (CNF.Clause.ofLiterals [(1, true)])

theorem fullNvSatBytes_eq :
    fullNvSatBytes = [112, 32, 99, 110, 102, 32, 49, 32, 49, 10, 49, 32, 48, 10] := by rfl

theorem fullNvSatCnf_eq :
    fullNvSatCnf = CNF.empty.add (CNF.Clause.ofLiterals [(1, true)]) := by rfl

private theorem fullNvSat_header :
    parseHeader fullNvSatBytes = some (1, 1, fullNvSatBytes.drop 9) := by decide

private theorem fullNvSat_nextLit_9 :
    nextLitPure 1 (fullNvSatBytes.drop 9) = .lit 0 (fullNvSatBytes.drop 11) := by decide

private theorem fullNvSat_nextLit_11 :
    nextLitPure 1 (fullNvSatBytes.drop 11) = .endClause (fullNvSatBytes.drop 13) := by decide

private theorem fullNvSat_skip_13 :
    skipWsComments (fullNvSatBytes.drop 13) = [] := by decide

theorem parseDimacs_fullNvSatBytes : parseDimacs fullNvSatBytes = some fullNvSatCnf := by
  unfold parseDimacs fullNvSatCnf
  rw [fullNvSat_header]
  dsimp only [Bind.bind, Option.bind]
  unfold parseClauses parseClause
  rw [parseClauseAux_eq_nextLitPure, fullNvSat_nextLit_9]
  dsimp only
  rw [show (fullNvSatBytes.drop 9).length = 5 from rfl]
  rw [parseClauseAux_eq_nextLitPure, fullNvSat_nextLit_11]
  simp [parseClauses, fullNvSat_skip_13, kissatLitToDimacsLiteral, litVar, litSign]

theorem fullNvSatCnf_sat_of_true1 {α : Nat → Bool} (h1 : α 1 = true) :
    fullNvSatCnf.Sat α := by
  unfold fullNvSatCnf
  rw [CNF.sat_add]
  refine ⟨?_, by simp⟩
  rw [CNF.Clause.sat_iff_exists_mem_eq]
  exact ⟨(1, true), by rw [← CNF.Clause.mem_literals_iff]; simp, h1⟩

private theorem fullNvSat_drop_eq_iff {j k : Nat} (hj : j ≤ 14) (hk : k ≤ 14)
    (heq : fullNvSatBytes.drop j = fullNvSatBytes.drop k) : j = k := by
  have hlen := congrArg List.length heq
  simp only [List.length_drop, show fullNvSatBytes.length = 14 from rfl] at hlen
  omega

private theorem runKissatCheckModel_fullNvSatBytes {valsBytes : List UInt8}
    (h0 : valsBytes[0]? = some 1) :
    runKissatCheckModel fullNvSatBytes valsBytes 1 = true := by
  have hd : valsBytes.getD 0 0 = 1 := by
    simp only [List.getD_eq_getElem?_getD, h0, Option.getD_some]
  unfold runKissatCheckModel
  rw [fullNvSat_header]
  simp only [gt_iff_lt, Nat.lt_irrefl, ↓reduceIte, checkClausesVals, checkClauseValsAux]
  rw [show (fullNvSatBytes.drop 9).length = 5 from rfl]
  simp only [checkClauseValsAux, fullNvSat_nextLit_9, fullNvSat_nextLit_11,
    evalLitVals, litVar, litSign, Nat.zero_div, Nat.zero_mod, Nat.mul_zero, hd,
    show i8BytePos 1 = true from by decide, show ((0 : Nat) == 1) = false from rfl,
    Bool.false_eq_true, ↓reduceIte, Bool.false_or, fullNvSat_skip_13, List.isEmpty_nil]

private theorem fullFixedBytes_1_eq : fullFixedBytes 1 = 1752 := by
  unfold fullFixedBytes valsBytes markBytes u32FullBytes fullMinDepthOf; decide

/-! ## 2. Generic Disjunctive-Environment `ModuleOk` Transport -/

/-- Generic disjunctive-environment transport: extending any certified `ModuleOk Γ₀ M` with an
extra specification environment `Γ_extra` certified under `Γ₀ ∨ Γ_extra` yields
`ModuleOk (Γ₀ ∨ Γ_extra) M` while transporting all untouched functions verbatim from `hM₀`. -/
theorem moduleOk_or_env {Γ₀ Γ_extra : Env} {M : Module}
    (hM₀ : ModuleOk Γ₀ M)
    (hExtra : ∀ fn ∈ M.fns, ∀ xs m Q X,
      Γ_extra fn.name fn.as fn.rs xs m Q X →
      Func.wp (fun f as bs ys m' P E => Γ₀ f as bs ys m' P E ∨ Γ_extra f as bs ys m' P E)
        fn.body xs m Q X) :
    ModuleOk (fun f as bs ys m' P E => Γ₀ f as bs ys m' P E ∨ Γ_extra f as bs ys m' P E) M := by
  let Γ₁ : Env := fun f as bs ys m' P E => Γ₀ f as bs ys m' P E ∨ Γ_extra f as bs ys m' P E
  refine ⟨hM₀.nodup, fun pre fn post hfn => ?_⟩
  have ⟨hwf, hcalls, hwp₀⟩ := hM₀.fnsOk pre fn post hfn
  refine ⟨hwf, hcalls, fun xs m Q X hs => ?_⟩
  rcases hs with h₀ | hₑ
  · exact wp_env_agree_of_callsOk
      (hwf Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units fn.as)) hcalls
      (fun _ _ _ _ _ _ _ _ h => Or.inl h) m (hwp₀ xs m Q X h₀)
  · have hmem : fn ∈ M.fns := by rw [hfn]; simp
    exact hExtra fn hmem xs m Q X hₑ

/-! ## 3. Shared Concrete-SAT State & Specialized Specs (`16` Trace Functions) -/

section SatNvProofs

open Full.FullParseInitSpecs
  (hdrTail4 hdrW0 hdrW1 hdrW2 hdrW0_len hdrW1_len hdrW2_len hdrTail4_eq_array64)
open Full.FullParseInitHelpers
open scoped Full.FullArenaTactics Full.FullParseInitTactics

private theorem wp_noExit_lift_nv {Γ : Env} {rs : List Ty} {e : Expr Val Cont rs} {m : Mem 64}
    {Q : Post rs} {X : XPost} (h : wp Γ Q (fun _ _ _ _ => False) e m) : wp Γ Q X e m :=
  wp_mono (fun _ _ hq => hq) (fun _ _ _ _ hf => hf.elim) e m h

/-- Lightweight concrete state predicate threaded across `full_parse_body`, `full_propagate`,
`full_arena_sweep`, `full_preprocess_m5`, and `full_extend` on `"p cnf 1 1\n1 0\n"`. -/
private structure NvSatState (c : FullCfg) (s : FullState)
    (prop te : Nat) (unfl : BitVec 64) : Prop where
  len : s.LengthsOk c
  mv1 : c.mv = 1
  cv1 : s.core.cur_vars = 1
  alen0 : s.core.arena_len = 0
  wlen1 : 1 ≤ s.core.wlen
  te_eq : s.core.trail_end = te
  prop_eq : s.core.propagated = prop
  cl0 : s.core.cur_level = 0
  unass0 : s.core.unassigned = 0#64
  unfl_eq : s.core.unflushed = unfl
  oom0 : s.core.oom = 0#64
  v0 : s.core.vals[0]? = some 1#8
  v1 : s.core.vals[1]? = some 0xFF#8
  trl0 : te = 1 → s.core.trl[0]? = some 0#32
  wsz0 : ∀ l < 2, fullWatchSize s l = 0
  wlay : WatchStackLayout s.core
  ext0 : s.scratch.extend_len = 0

private theorem watchStackLayout_of_zero_wvec {k : FullCoreState} {mx : Nat}
    (hcv : k.cur_vars ≤ mx) (hwv : k.wvec = List.replicate (4 * mx) 0#32) :
    WatchStackLayout k := by
  have hz : ∀ l < 2 * k.cur_vars, fullWatchOffCore k l = 0 ∧ fullWatchSizeCore k l = 0 := by
    intro l hl; unfold fullWatchOffCore fullWatchSizeCore; rw [hwv]
    simp [show 2 * l < 4 * mx by omega, show 2 * l + 1 < 4 * mx by omega]
  exact ⟨fun l hl => by obtain ⟨ho, hs⟩ := hz l hl; omega,
    fun l hl hpos => by obtain ⟨_, hs⟩ := hz l hl; omega,
    fun l1 _ h1 _ _ hp1 _ => by obtain ⟨_, hs⟩ := hz l1 h1; omega,
    fun l hl idx hidx => by obtain ⟨_, hs⟩ := hz l hl; omega⟩

/-- Concrete `full_init_hdr` spec exposing `s.core.unassigned = BitVec.ofNat 64 c.mv`. -/
private def nvInitHdrSpec : Spec [i64, i64, i64, i64] [] :=
  fun (h, mv, max_v, fuel, ()) m Q _ =>
    ∃ (c : FullCfg) (ws : List (BitVec 64)) (R : Mem 64 → Prop),
      h = c.hdr ∧ mv = BitVec.ofNat 64 c.mv ∧ max_v = BitVec.ofNat 64 c.max_vars ∧
      ws.length = 140 ∧
      (∀ (s0 : FullState),
        ∀ i ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
                41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
                102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113],
          ws[i]? = (Full.hdrTailWords c s0)[i]?) ∧
      (array64 (c.hdr + 32) ws ⋆ R) m ∧
      ∀ (s : FullState) m',
        s.core.cur_vars = c.mv → s.core.unassigned = BitVec.ofNat 64 c.mv →
        s.core.arena_len = 0 → s.core.wlen = 1 →
        s.core.trail_end = 0 → s.core.propagated = 0 → s.core.cur_level = 0 →
        s.core.tmp_len = 0 → s.core.fuel = fuel → s.core.unflushed = 0#64 →
        s.core.probing = 0#64 → s.core.min_clr_len = 0 → s.core.min_clr_full = 0#64 →
        s.core.oom = 0#64 → s.core.dense_mode = 0#64 → s.core.inconsistent = 0#64 →
        s.scratch.extend_len = 0 →
        (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ R) m' → Q () m'

/-- Concrete `full_zero_tables2` spec exposing `flags'[0]? = some 2041#32` when `1 ≤ c.mv`. -/
private def nvZeroTables2Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ 1 ≤ c.mv ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ (flags' fdec' : List (BitVec 32)) (sc' : FullScratch) m',
      flags'.length = c.max_vars → fdec'.length = c.max_vars + 1 →
      flags'[0]? = some 2041#32 →
      sc'.LengthsOk c → Full.FullExtScratchPres s { s with scratch := sc' } →
      let s' : FullState :=
        { s with
          core := { s.core with mrk := List.replicate c.max_vars 0#8, flags := flags'
                                lvl := List.replicate c.max_vars 0#32
                                rsns := List.replicate c.max_vars 0xFFFFFFFF#32
                                frame_trail := List.replicate (c.max_vars + 1) 0#32
                                frame_dec := fdec' }
          scratch := sc' }
      (FullMem c s' ⋆ R) m' → Q () m'

/-- Concrete `full_assign_lvl` spec for level-0 assignment of literal `0` (`+1`). -/
private def nvAssignLvlSpec : Spec [i64, i32, i32, i32] [] :=
  fun (h, lit, _rsn, alvl, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ lit = 0#32 ∧ alvl = 0#32 ∧ s.LengthsOk c ∧
      1 ≤ s.core.cur_vars ∧ s.core.trail_end = 0 ∧
      s.core.vals[0]? = some 0#8 ∧ s.core.flags[0]? = some 2041#32 ∧
      s.core.unassigned = 1#64 ∧ (FullMem c s ⋆ R) m ∧
      ∀ flags' phases' m',
        flags'.length = c.max_vars → phases'.length = c.max_vars →
        let s' : FullState :=
          { s with
            core :=
              { s.core with
                vals := (s.core.vals.set 0 1#8).set 1 0xFF#8
                flags := flags', lvl := s.core.lvl.set 0 0#32
                rsns := s.core.rsns.set 0 0xFFFFFFFF#32
                trl := s.core.trl.set 0 0#32
                trail_pos := s.core.trail_pos.set 0 0#32
                trail_end := 1, unassigned := 0#64
                unflushed := s.core.unflushed + 1#64 }
            scratch := { s.scratch with phases := phases' } }
        (FullMem c s' ⋆ R) m' → Q () m'

/-- Concrete `full_init_state_m5` spec on `fullNvSatBytes` (`avail ∈ [4088, 4096]`). -/
private def nvInitStateM5Spec : Spec [i64, i64, i64, i64, i64] [.bool] :=
  fun (cnf_ptr, cend, hdr_addr, avail, fuel, ()) m Q _ =>
    ∃ R : Mem 64 → Prop,
      cend = cnf_ptr + BitVec.ofNat 64 fullNvSatBytes.length ∧
      cnf_ptr.toNat + fullNvSatBytes.length < 2 ^ 64 ∧
      hdr_addr.toNat + avail.toNat < 2 ^ 64 ∧
      4088 ≤ avail.toNat ∧ avail.toNat ≤ 4096 ∧
      (bytes cnf_ptr fullNvSatBytes ⋆ region hdr_addr avail.toNat ⋆ R) m ∧
      ∀ (c : FullCfg) (s : FullState) (m' : Mem 64),
        c.hdr = hdr_addr → c.avail = avail.toNat → c.mv = 1 → c.nc = 1 →
        s.LengthsOk c → s.core.cur_vars = 1 → s.core.d_cur = cnf_ptr + 9#64 →
        s.core.arena_len = 0 → s.core.wlen = 1 → s.core.trail_end = 0 →
        s.core.propagated = 0 → s.core.cur_level = 0 → s.core.fuel = fuel →
        s.core.unassigned = 1#64 → s.core.unflushed = 0#64 → s.core.oom = 0#64 →
        s.core.vals = List.replicate (2 * c.max_vars) 0#8 →
        s.core.wvec = List.replicate (4 * c.max_vars) 0#32 →
        s.core.mrk = List.replicate c.max_vars 0#8 →
        s.core.flags[0]? = some 2041#32 → s.scratch.extend_len = 0 →
        (bytes cnf_ptr fullNvSatBytes ⋆ FullMem c s ⋆ R) m' → Q (true, ()) m'

/-- Concrete `full_ingest_cl` spec on the single unit clause `"1 0\n"` (`i0 = 9 → 13`). -/
private def nvIngestClSpec : Spec [i64, i64] [i64] := fun (h, cend, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (cnf_ptr : BitVec 64) (R : Mem 64 → Prop),
    h = c.hdr ∧ cend = cnf_ptr + 14#64 ∧ cnf_ptr.toNat + 14 < 2 ^ 64 ∧
    c.mv = 1 ∧ c.nc = 1 ∧ s.LengthsOk c ∧ s.core.cur_vars = 1 ∧
    s.core.d_cur = cnf_ptr + 9#64 ∧ s.core.arena_len = 0 ∧ 1 ≤ s.core.wlen ∧
    s.core.trail_end = 0 ∧ s.core.propagated = 0 ∧ s.core.cur_level = 0 ∧
    s.core.unassigned = 1#64 ∧ s.core.unflushed = 0#64 ∧ s.core.oom = 0#64 ∧
    s.core.vals[0]? = some 0#8 ∧ s.core.mrk[0]? = some 0#8 ∧ s.core.flags[0]? = some 2041#32 ∧
    (∀ l < 2, fullWatchSize s l = 0) ∧ WatchStackLayout s.core ∧ s.scratch.extend_len = 0 ∧
    (bytes cnf_ptr fullNvSatBytes ⋆ FullMem c s ⋆ R) m ∧
    ∀ s' m',
      NvSatState c s' 0 1 1#64 → s'.core.d_cur = cnf_ptr + 13#64 →
      s'.core.fuel = s.core.fuel →
      (bytes cnf_ptr fullNvSatBytes ⋆ FullMem c s' ⋆ R) m' → Q (1#64, ()) m'

/-- Concrete `full_parse_body` spec on `fullNvSatBytes` (`nc = 1`, `i0 = 9 → 14`). -/
private def nvParseBodySpec : Spec [i64, i64] [i64] := fun (h, cend, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (cnf_ptr : BitVec 64) (R : Mem 64 → Prop),
    h = c.hdr ∧ cend = cnf_ptr + 14#64 ∧ cnf_ptr.toNat + 14 < 2 ^ 64 ∧
    c.mv = 1 ∧ c.nc = 1 ∧ s.LengthsOk c ∧ s.core.cur_vars = 1 ∧
    s.core.d_cur = cnf_ptr + 9#64 ∧ s.core.arena_len = 0 ∧ 1 ≤ s.core.wlen ∧
    s.core.trail_end = 0 ∧ s.core.propagated = 0 ∧ s.core.cur_level = 0 ∧
    s.core.unassigned = 1#64 ∧ s.core.unflushed = 0#64 ∧ s.core.oom = 0#64 ∧
    s.core.vals[0]? = some 0#8 ∧ s.core.mrk[0]? = some 0#8 ∧ s.core.flags[0]? = some 2041#32 ∧
    (∀ l < 2, fullWatchSize s l = 0) ∧ WatchStackLayout s.core ∧ s.scratch.extend_len = 0 ∧
    (bytes cnf_ptr fullNvSatBytes ⋆ FullMem c s ⋆ R) m ∧
    ∀ s' m',
      NvSatState c s' 0 1 1#64 → s'.core.fuel = s.core.fuel →
      (bytes cnf_ptr fullNvSatBytes ⋆ FullMem c s' ⋆ R) m' → Q (1#64, ()) m'

/-- Concrete `full_prop_lit_raw` spec when `not_lit` has watch size `0` (instant `true`). -/
private def nvPropLitRawSpec : Spec [i64, i32, i64] [.bool] :=
  fun (h, lit, _ignore_ref, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ lit = 0#32 ∧ s.LengthsOk c ∧ s.core.cur_vars = 1 ∧
      fullWatchSize s 1 = 0 ∧ (FullMem c s ⋆ R) m ∧ Q (true, ()) m

/-- Concrete `full_propagate_ignore` spec on `NvSatState c s prop 1 unfl` (`prop ≤ 1`). -/
private def nvPropagateIgnoreSpec : Spec [i64, i64] [i64] :=
  fun (h, _ignore_ref, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (prop : Nat) (unfl : BitVec 64) (R : Mem 64 → Prop),
      h = c.hdr ∧ NvSatState c s prop 1 unfl ∧ prop ≤ 1 ∧ 1 ≤ s.core.fuel.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ s' m',
        NvSatState c s' 1 1 unfl →
        (prop = 1 → s'.core.fuel = s.core.fuel) →
        (prop = 0 → s'.core.fuel = s.core.fuel - 1#64) →
        (FullMem c s' ⋆ R) m' → Q (0#64, ()) m'

/-- Concrete `full_propagate` spec on `NvSatState c s prop 1 unfl` (`prop ≤ 1`). -/
private def nvPropagateSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (prop : Nat) (unfl : BitVec 64) (R : Mem 64 → Prop),
    h = c.hdr ∧ NvSatState c s prop 1 unfl ∧ prop ≤ 1 ∧ 1 ≤ s.core.fuel.toNat ∧
    (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      NvSatState c s' 1 1 unfl →
      (prop = 1 → s'.core.fuel = s.core.fuel) →
      (prop = 0 → s'.core.fuel = s.core.fuel - 1#64) →
      (FullMem c s' ⋆ R) m' → Q (0#64, ()) m'

/-- Concrete `full_sweep_bins` spec on `NvSatState c s 1 1 1#64` (empty watch lists). -/
private def nvSweepBinsSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ NvSatState c s 1 1 1#64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ s' m', NvSatState c s' 1 1 1#64 → s'.core.fuel = s.core.fuel →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- Concrete `full_rewatch_arena` spec when `dst = 0` (0-iteration loop, instant `true`). -/
private def nvRewatchArenaSpec : Spec [i64, i64] [.bool] := fun (h, dst, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ dst = 0#64 ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧ Q (true, ()) m

/-- Concrete `full_arena_sweep` spec on `NvSatState c s 1 1 1#64` (`arena_len = 0`). -/
private def nvArenaSweepSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ NvSatState c s 1 1 1#64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ s' m', NvSatState c s' 1 1 1#64 → s'.core.fuel = s.core.fuel →
      (FullMem c s' ⋆ R) m' → Q (0#64, ()) m'

/-- Concrete `full_extend` spec preserving `vals[0]? = some 1#8` when `extend_len = 0`. -/
private def nvExtendSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ 1 ≤ c.max_vars ∧
    s.core.vals[0]? = some 1#8 ∧ s.scratch.extend_len = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ vals' m',
      vals'.length = 2 * c.max_vars → vals'[0]? = some 1#8 →
      let s' : FullState := { s with core := { s.core with vals := vals' } }
      (FullMem c s' ⋆ R) m' → Q () m'

/-- Concrete `full_preprocess_m5` spec returning `10#64` directly at `unassigned == 0`. -/
private def nvPreprocessM5Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ NvSatState c s 0 1 1#64 ∧ 2 ≤ s.core.fuel.toNat ∧ (FullMem c s ⋆ R) m ∧
    ∀ s' m', NvSatState c s' 1 1 0#64 → (FullMem c s' ⋆ R) m' → Q (10#64, ()) m'

/-- Concrete SAT witness specification (`fullNvSatBytes`, `work_len = 4096`, `fuel = 16`):
certifies `r = 10#64` AND `fullNvSatCnf.Sat (readModelFromWork M work_ptr)` in every framed
superset memory `M` of `m'`. -/
def fullSatWitnessSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q _ =>
    ∃ R : Mem 64 → Prop,
      cnf_ptr ≠ 0#64 ∧ work_ptr ≠ 0#64 ∧
      cnf_len = BitVec.ofNat 64 fullNvSatBytes.length ∧
      work_len = 4096#64 ∧ fuel = 16#64 ∧
      cnf_ptr.toNat + fullNvSatBytes.length < 2 ^ 64 ∧ work_ptr.toNat + 4096 < 2 ^ 64 ∧
      (bytes cnf_ptr fullNvSatBytes ⋆ region work_ptr 4096 ⋆ R) m ∧
      ∀ m',
        (∀ (F : Mem 64 → Prop) (M : Mem 64), (Eq m' ⋆ F) M →
          fullNvSatCnf.Sat (readModelFromWork M work_ptr)) →
        (bytes cnf_ptr fullNvSatBytes ⋆ region work_ptr 4096 ⋆ R) m' →
        Q (10#64, ()) m'

/-! ## 4. Leaf & Init `Func.wp` Proofs (`init_hdr`, `zero_tables2`, `assign_lvl`, `init_state`) -/

private def nvHdrW3 (mv : Nat) (w3 : List (BitVec 64)) : List (BitVec 64) :=
  let rng := 0x9E3779B97F4A7C15#64 ^^^ (BitVec.ofNat 64 mv + 1#64)
  ((((((((((((((((((((((((((w3.set 5 0#64).set 9 rng).set 10 100#64).set 11 0#64).set
    12 0#64).set 13 2000#64).set 14 0#64).set 15 5000#64).set 16 0#64).set 17 0#64).set
    18 0#64).set 19 0#64).set 20 0#64).set 21 0#64).set 22 0#64).set 23 0#64).set
    24 0#64).set 25 0#64).set 26 0#64).set 27 0#64).set 28 0#64).set 29 0#64).set
    30 0#64).set 31 0#64).set 32 0#64).set 33 0#64).set 34 0#64

private theorem nvHdrW3_len {mv : Nat} {w : List (BitVec 64)} :
    (nvHdrW3 mv w).length = w.length := by simp [nvHdrW3]

private theorem nv_len_cons10 {α} (xs : List α) (n : Nat) (h : xs.length = n + 10) :
    ∃ a b c d e f g h1 i j ys, ys.length = n ∧
      xs = a :: b :: c :: d :: e :: f :: g :: h1 :: i :: j :: ys := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h1, _ | ⟨i, _ |
    ⟨j, ys⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨a, b, c, d, e, f, g, h1, i, j, ys, h, rfl⟩

private theorem nv_decompose35 {α} (xs : List α) (h : xs.length = 35) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 d0 d1 d2 d3 d4 : α,
      xs = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9,
            b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
            c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4] := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, xs1, h1, rfl⟩ := nv_len_cons10 xs 25 h
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, xs2, h2, rfl⟩ := nv_len_cons10 xs1 15 h1
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, xs3, h3, rfl⟩ := nv_len_cons10 xs2 5 h2
  rcases xs3 with _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, _ | ⟨d3, _ | ⟨d4, _ | _⟩⟩⟩⟩⟩ <;> simp at h3
  exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩

private def nvInitHdrWitness (c : FullCfg) (fuel : BitVec 64) : FullState :=
  { core :=
      { d_cur := 0#64, d_val := 0#64, cur_vars := c.mv, unassigned := BitVec.ofNat 64 c.mv
        arena_len := 0, wlen := 1, wusable := 0#64, arena_garbage := 0#64
        first_reducible := 0xFFFFFFFF#64, num_irred := 0#64, num_redundant := 0#64
        num_binary := 0#64, unflushed := 0#64, probing := 0#64, trail_end := 0, propagated := 0
        cur_level := 0, fuel := fuel, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64
        confl_lit0 := 0#64, confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0, min_clr_len := 0
        min_clr_full := 0#64, oom := 0#64, dense_mode := 0#64, inconsistent := 0#64
        vals := [], lit_mark := [], mrk := [], flags := [], lvl := [], rsns := [], trl := []
        trail_pos := [], tmp := [], min_clr := [], frame_trail := [], frame_dec := [], wvec := []
        repr := [], min_stk := [], arena := [], wstk := [] }
    scratch :=
      { heap_len := c.mv, scinc := 1#64 <<< 28, rel_period := 1024#64
        rel_limit := 1048576#64, rel_wait := 1024#64, rel_u := 1#64, rel_v := 1#64
        rel_trigger := 0#64, conflicts := 0#64, learned_lits := 0#64, min_removed := 0#64
        delayed_len := 0, stable := 0#64, switched := 0#64, mode_count := 0#64
        mode_confl_lim := 1000#64, mode_tick_lim := 0#64, mode_saved_ticks := 0#64
        search_ticks := 0#64
        q_first := if c.mv = 0 then 0xFFFFFFFF#64 else 0#64
        q_last := if c.mv = 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (c.mv - 1)
        q_search_idx := if c.mv = 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (c.mv - 1)
        q_search_stamp := BitVec.ofNat 64 c.mv, q_cur_stamp := BitVec.ofNat 64 c.mv
        target_assigned := 0#64, best_assigned := 0#64, rephase_limit := 1000#64
        rephased := 0#64, reduce_limit := 1000#64, reductions := 0#64, tier1 := 2#64
        tier2 := 6#64, restarts := 0#64, restart_limit := 1#64, ema_fast_biased := 0#64
        ema_fast_exp := 1#64 <<< 24, ema_slow_biased := 0#64, ema_slow_exp := 1#64 <<< 24
        extend_len := 0, rng_state := 0x9E3779B97F4A7C15#64 ^^^ (BitVec.ofNat 64 c.mv + 1#64)
        chrono_levels := 100#64, otfs_cnt := 0#64, eager_sub_cnt := 0#64, probe_limit := 2000#64
        probings := 0#64, elim_limit := 5000#64, eliminations := 0#64, elim_bound := 0#64
        iterating := 0#64, hbr_cnt := 0#64, trans_cnt := 0#64, viv_cnt := 0#64, subst_cnt := 0#64
        cong_cnt := 0#64, sweep_cnt := 0#64, bve_cnt := 0#64, bce_cnt := 0#64, bva_cnt := 0#64
        walk_cnt_stat := 0#64, fwd_sub_cnt := 0#64, fwd_str_cnt := 0#64, ant_sz := 0#64
        res_sz := 0#64, walk_vals := [], phases := [], phases_target := [], phases_best := []
        walk_best := [], heap := [], pos := [], shrink_stk := [], q_prev := [], q_next := []
        q_stamp := [], wsort := [], work_stk1 := [], work_stk2 := [], tarjan_mark := []
        tarjan_reach := [], score := [], sim_sig := [], glue_used := [], last_learned := []
        delayed := [], red_refs := [], extend_stk := [], scratch_buf := [] } }

local macro "nv_jnz_t" h:ident : tactic => `(tactic|
  (dsimp only [Arg.val_var] at $h:ident; rw [decide_eq_true_eq] at $h:ident; fp_head_steps))
local macro "nv_jnz_f" h:ident : tactic => `(tactic|
  (dsimp only [Arg.val_var] at $h:ident; rw [decide_eq_false_iff_not] at $h:ident; fp_head_steps))
local macro "nv_ult_t" h:ident : tactic => `(tactic|
  (simp only [i64, Ty.hasFloat, liftCmp, CmpOp.evalBits, evalBits_ult_eq, evalBits_ule_eq,
     evalBits_ugt_eq, evalBits_uge_eq, Arg.val_var, Arg.val_imm, BitVec.ult,
     BitVec.ule] at $h:ident
   have $h:ident := of_decide_eq_true $h:ident))
local macro "nv_ult_f" h:ident : tactic => `(tactic|
  (simp only [i64, Ty.hasFloat, liftCmp, CmpOp.evalBits, evalBits_ult_eq, evalBits_ule_eq,
     evalBits_ugt_eq, evalBits_uge_eq, Arg.val_var, Arg.val_imm, BitVec.ult,
     BitVec.ule] at $h:ident
   have $h:ident := of_decide_eq_false $h:ident))

private theorem nv_init_hdr4_wp (Γ : Env) {h mv max_v fuel : BitVec 64}
    {w0 w1 w2 w3 : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hle : mv.toNat ≤ max_v.toNat) (hmx : max_v.toNat < 2 * dimacsBound)
    (hm : (hdrTail4 h w0 w1 w2 w3 ⋆ R) m)
    (hQ : ∀ m', (hdrTail4 h (hdrW0 mv.toNat fuel w0) (hdrW1 w1)
      (hdrW2 mv.toNat max_v.toNat w2) (nvHdrW3 mv.toNat w3) ⋆ R) m' → Q () m') :
    Func.wp Γ FullFastBveBudgets.full_init_hdr_body (h, mv, max_v, fuel, ()) m Q X := by
  have hmx' := hmx; unfold dimacsBound at hmx'
  let q0 := if mv.toNat = 0 then 0xFFFFFFFF#64 else 0#64
  let ql := if mv.toNat = 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (mv.toNat - 1)
  have hmv0 : (mv == (0 : BitVec 64)) = decide (mv.toNat = 0) := by
    by_cases hz : mv.toNat = 0
    · have he : mv = 0#64 := BitVec.eq_of_toNat_eq hz; simp [he]
    · have hne : mv ≠ 0#64 := fun h => hz (by simp [h]); simp [hz, hne]
  have hsub_bva : max_v - mv = BitVec.ofNat 64 (max_v.toNat - mv.toNat) := by
    apply BitVec.eq_of_toNat_eq; have := max_v.isLt; have := mv.isLt
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsub_mv1 : mv.toNat ≠ 0 → mv - 1#64 = BitVec.ofNat 64 (mv.toNat - 1) := fun hnz => by
    apply BitVec.eq_of_toNat_eq; have := mv.isLt
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsh28 : (1 : BitVec 64) <<< (((28 : BitVec 32).signExtend 64).toNat % 64) =
      (1#64 <<< 28) := rfl
  have hsh24 : (1 : BitVec 64) <<< (((24 : BitVec 32).signExtend 64).toNat % 64) =
      (1#64 <<< 24) := rfl
  unfold Func.wp FullFastBveBudgets.full_init_hdr_body
  fp_head_steps
  refine wp_join_group (fun (v : Tup Val [i64]) mqf => v.1 = q0 ∧ mqf = m) ?_ ?_
  · rintro _ ⟨qf, ⟨⟩⟩ mqf ⟨rfl, rfl⟩; simp only [Blocks.get_here]; fp_head_steps
    refine wp_join_group (fun (v : Tup Val [i64]) mql => v.1 = ql ∧ mql = m) ?_ ?_
    · rintro _ ⟨qlv, ⟨⟩⟩ mql ⟨rfl, rfl⟩; simp only [Blocks.get_here]; fp_head_steps
      refine wp_join_group (fun (v : Tup Val [i64]) mqsi => v.1 = ql ∧ mqsi = m) ?_ ?_
      · rintro _ ⟨qsi, ⟨⟩⟩ mqsi ⟨rfl, rfl⟩; simp only [Blocks.get_here]; fp_head_steps
        rw [hsub_bva, hsh28, hsh24] at hm
        unfold hdrW0 hdrW1 hdrW2 nvHdrW3 at hQ
        rw [bv_ofNat_toNat_eq mv, bv_ofNat_toNat_eq max_v] at hQ
        exact hQ m hm
      · intro J3 hJ3; fp_head_steps; rw [hmv0]
        refine wp_jnz_of (fun ht => ?_) (fun hf => ?_)
        · nv_jnz_t ht; exact hJ3 (_, ()) m ⟨by dsimp [ql]; simp only [ht, ↓reduceIte], rfl⟩
        · nv_jnz_f hf; refine hJ3 (_, ()) m ⟨?_, rfl⟩
          dsimp [ql]; rw [ite_eq_right_iff.mpr (fun h => absurd h hf), hsub_mv1 hf]
    · intro J2 hJ2; fp_head_steps; rw [hmv0]
      refine wp_jnz_of (fun ht => ?_) (fun hf => ?_)
      · nv_jnz_t ht; exact hJ2 (_, ()) m ⟨by dsimp [ql]; simp only [ht, ↓reduceIte], rfl⟩
      · nv_jnz_f hf; refine hJ2 (_, ()) m ⟨?_, rfl⟩
        dsimp [ql]; rw [ite_eq_right_iff.mpr (fun h => absurd h hf), hsub_mv1 hf]
  · intro J1 hJ1; fp_head_steps; rw [hmv0]
    refine wp_jnz_of (fun ht => ?_) (fun hf => ?_)
    · nv_jnz_t ht; exact hJ1 (_, ()) m ⟨by dsimp [q0]; simp only [ht, ↓reduceIte], rfl⟩
    · nv_jnz_f hf; exact hJ1 (_, ()) m ⟨by
        dsimp [q0]; rw [ite_eq_right_iff.mpr (fun h => absurd h hf)], rfl⟩

private theorem nv_hdrW0_eq (c : FullCfg) (fuel : BitVec 64) (w0 : List (BitVec 64))
    (h0 : w0.length = 35)
    (hw : ∀ i ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29],
      w0[i]? = (hdrTailWords0 c (nvInitHdrWitness c fuel))[i]?) :
    hdrW0 c.mv fuel w0 = hdrTailWords0 c (nvInitHdrWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := nv_decompose35 w0 h0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e0 := hw 0 (by simp); have e1 := hw 1 (by simp); have e4 := hw 4 (by simp)
  have e5 := hw 5 (by simp); have e6 := hw 6 (by simp); have e7 := hw 7 (by simp)
  have e8 := hw 8 (by simp); have e9 := hw 9 (by simp); have e10 := hw 10 (by simp)
  have e11 := hw 11 (by simp); have e12 := hw 12 (by simp); have e13 := hw 13 (by simp)
  have e21 := hw 21 (by simp); have e22 := hw 22 (by simp); have e23 := hw 23 (by simp)
  have e24 := hw 24 (by simp); have e25 := hw 25 (by simp); have e26 := hw 26 (by simp)
  have e29 := hw 29 (by simp)
  simp only [hdrTailWords0, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
    at e0 e1 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e21 e22 e23 e24 e25 e26 e29
  simp [hdrW0, hdrTailWords0, nvInitHdrWitness, e0, e1, e4, e5, e6, e7, e8, e9, e10, e11, e12,
    e13, e21, e22, e23, e24, e25, e26, e29]

private theorem nv_hdrW1_eq (c : FullCfg) (fuel : BitVec 64) (w1 : List (BitVec 64))
    (h1 : w1.length = 35)
    (hw : ∀ i ∈ [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
      w1[i]? = (hdrTailWords1 c (nvInitHdrWitness c fuel))[i]?) :
    hdrW1 w1 = hdrTailWords1 c (nvInitHdrWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := nv_decompose35 w1 h1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e6 := hw 6 (by simp); have e7 := hw 7 (by simp); have e8 := hw 8 (by simp)
  have e9 := hw 9 (by simp); have e10 := hw 10 (by simp); have e11 := hw 11 (by simp)
  have e12 := hw 12 (by simp); have e13 := hw 13 (by simp); have e14 := hw 14 (by simp)
  have e15 := hw 15 (by simp); have e16 := hw 16 (by simp); have e17 := hw 17 (by simp)
  simp only [hdrTailWords1, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
    at e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
  simp [hdrW1, hdrTailWords1, nvInitHdrWitness, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15,
    e16, e17]

private theorem nv_hdrW2_eq (c : FullCfg) (fuel : BitVec 64) (w2 : List (BitVec 64))
    (h2 : w2.length = 35)
    (hw : ∀ i ∈ [26, 27, 28, 29, 30, 31, 32, 33, 34],
      w2[i]? = (hdrTailWords2 c (nvInitHdrWitness c fuel))[i]?) :
    hdrW2 c.mv c.max_vars w2 = hdrTailWords2 c (nvInitHdrWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := nv_decompose35 w2 h2
  have hbva : c.max_vars - c.mv = c.bva_cap := by have := c.hbva; omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e26 := hw 26 (by simp); have e27 := hw 27 (by simp); have e28 := hw 28 (by simp)
  have e29 := hw 29 (by simp); have e30 := hw 30 (by simp); have e31 := hw 31 (by simp)
  have e32 := hw 32 (by simp); have e33 := hw 33 (by simp); have e34 := hw 34 (by simp)
  simp only [hdrTailWords2, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
    at e26 e27 e28 e29 e30 e31 e32 e33 e34
  simp [hdrW2, hdrTailWords2, nvInitHdrWitness, hbva, e26, e27, e28, e29, e30, e31, e32, e33,
    e34]

private theorem nv_hdrW3_eq (c : FullCfg) (fuel : BitVec 64) (w3 : List (BitVec 64))
    (h3 : w3.length = 35)
    (hw : ∀ i ∈ [0, 1, 2, 3, 4, 6, 7, 8],
      w3[i]? = (hdrTailWords3 c (nvInitHdrWitness c fuel))[i]?) :
    nvHdrW3 c.mv w3 = hdrTailWords3 c (nvInitHdrWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := nv_decompose35 w3 h3
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e0 := hw 0 (by simp); have e1 := hw 1 (by simp); have e2 := hw 2 (by simp)
  have e3 := hw 3 (by simp); have e4 := hw 4 (by simp); have e6 := hw 6 (by simp)
  have e7 := hw 7 (by simp); have e8 := hw 8 (by simp)
  simp only [hdrTailWords3, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
    at e0 e1 e2 e3 e4 e6 e7 e8
  simp [nvHdrW3, hdrTailWords3, nvInitHdrWitness, e0, e1, e2, e3, e4, e6, e7, e8]

private theorem nv_init_hdr_wp (Γ : Env) :
    ∀ a m Q X, nvInitHdrSpec a m Q X → Func.wp Γ FullFastBveBudgets.full_init_hdr_body a m Q X := by
  rintro ⟨h, mv, max_v, fuel, ⟨⟩⟩ m Q X ⟨c, ws, R, rfl, rfl, rfl, hw, hws, hm, hQ⟩
  let s0 := nvInitHdrWitness c fuel
  have hws0 := hws s0
  have hmv' := c.hmv; have hmx' := c.hmaxv; unfold dimacsBound at hmv' hmx'
  have hmv_to : (BitVec.ofNat 64 c.mv).toNat = c.mv := bv64_ofNat_toNat (by omega)
  have hmx_to : (BitVec.ofNat 64 c.max_vars).toNat = c.max_vars := bv64_ofNat_toNat (by omega)
  let w0 := ws.take 35; let w1 := (ws.drop 35).take 35
  let w2 := (ws.drop 70).take 35; let w3 := (ws.drop 105).take 35
  have h0l : w0.length = 35 := by simp [w0, hw]
  have h1l : w1.length = 35 := by simp [w1, hw]
  have h2l : w2.length = 35 := by simp [w2, hw]
  have h3l : w3.length = 35 := by simp [w3, hw]
  have hw_len0 : (hdrTailWords0 c s0).length = 35 := by simp [hdrTailWords0]
  have hw_len1 : (hdrTailWords1 c s0).length = 35 := by simp [hdrTailWords1]
  have hw_len2 : (hdrTailWords2 c s0).length = 35 := by simp [hdrTailWords2]
  refine nv_init_hdr4_wp Γ (by rw [hmv_to, hmx_to]; have := c.hbva; omega)
    (by rw [hmx_to]; exact c.hmaxv) (array64_to_hdrTail4 hw hm) fun m' hm' => ?_
  rw [hmv_to, hmx_to] at hm'
  have hm_arr : (array64 (c.hdr + 32) (hdrW0 c.mv fuel w0 ++ hdrW1 w1 ++
      hdrW2 c.mv c.max_vars w2 ++ nvHdrW3 c.mv w3) ⋆ R) m' := by
    rwa [hdrTail4_eq_array64 (by rw [hdrW0_len]; exact h0l) (by rw [hdrW1_len]; exact h1l)
      (by rw [hdrW2_len]; exact h2l) (by rw [nvHdrW3_len]; exact h3l)] at hm'
  have hi0 : ∀ j ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29],
      j < 35 ∧ j ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have hi1 : ∀ j ∈ [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
      j < 35 ∧ (35 + j) ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have hi2 : ∀ j ∈ [26, 27, 28, 29, 30, 31, 32, 33, 34],
      j < 35 ∧ (70 + j) ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have hi3 : ∀ j ∈ [0, 1, 2, 3, 4, 6, 7, 8],
      j < 35 ∧ (105 + j) ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have heq0 : hdrW0 c.mv fuel w0 = hdrTailWords0 c s0 := nv_hdrW0_eq c fuel w0 h0l fun i hi => by
    have ⟨hi', hm'⟩ := hi0 i hi; have hgi := hws0 i hm'
    dsimp only [w0]; rw [List.getElem?_take_of_lt hi', hgi]
    unfold Full.hdrTailWords; exact append4_getElem?_0 hw_len0 hi'
  have heq1 : hdrW1 w1 = hdrTailWords1 c s0 := nv_hdrW1_eq c fuel w1 h1l fun i hi => by
    have ⟨hi35, hm'⟩ := hi1 i hi; have hgi := hws0 (35 + i) hm'
    dsimp only [w1]; rw [drop_take_getElem? ws 35 35 i hi35, hgi]
    unfold Full.hdrTailWords
    rw [append4_getElem?_1 hw_len0 hw_len1 (by omega) (by omega), show 35 + i - 35 = i by omega]
  have heq2 : hdrW2 c.mv c.max_vars w2 = hdrTailWords2 c s0 :=
    nv_hdrW2_eq c fuel w2 h2l fun i hi => by
      have ⟨hi35, hm'⟩ := hi2 i hi; have hgi := hws0 (70 + i) hm'
      dsimp only [w2]; rw [drop_take_getElem? ws 70 35 i hi35, hgi]
      unfold Full.hdrTailWords
      rw [append4_getElem?_2 hw_len0 hw_len1 hw_len2 (by omega) (by omega),
        show 70 + i - 70 = i by omega]
  have heq3 : nvHdrW3 c.mv w3 = hdrTailWords3 c s0 := nv_hdrW3_eq c fuel w3 h3l fun i hi => by
    have ⟨hi35, hm'⟩ := hi3 i hi; have hgi := hws0 (105 + i) hm'
    dsimp only [w3]; rw [drop_take_getElem? ws 105 35 i hi35, hgi]
    unfold Full.hdrTailWords
    rw [append4_getElem?_3 hw_len0 hw_len1 hw_len2 (by omega), show 105 + i - 105 = i by omega]
  rw [heq0, heq1, heq2, heq3] at hm_arr
  exact hQ s0 m' rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hm_arr

private theorem nv_zero_tables2_wp (Γ : Env) :
    ∀ a m Q X, nvZeroTables2Spec a m Q X → Func.wp Γ Full.full_zero_tables2_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hmv1, hlen, hm, hQ⟩
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hmv : c.mv < dimacsBound := c.hmv
  have hmv_le : c.mv ≤ c.max_vars := by have := c.hbva; omega
  unfold dimacsBound at hmx hmv
  have hmx_to : (BitVec.ofNat 64 c.max_vars).toNat = c.max_vars := bv64_ofNat_toNat (by omega)
  have hmv_to : (BitVec.ofNat 64 c.mv).toNat = c.mv := bv64_ofNat_toNat (by omega)
  unfold Func.wp Full.full_zero_tables2_body
  c0_hsteps_nogrp
  refine wp_while_state
    (fun (p : BitVec 64 × FullState) => (p.1, ()))
    (fun p => c.max_vars - p.1.toNat)
    (fun p ml =>
      p.1.toNat ≤ c.max_vars ∧
      p.2.core = { s.core with
        mrk := p.2.core.mrk, flags := p.2.core.flags, lvl := p.2.core.lvl,
        rsns := p.2.core.rsns, frame_trail := p.2.core.frame_trail,
        frame_dec := p.2.core.frame_dec } ∧
      p.2.LengthsOk c ∧ FullExtScratchPres s p.2 ∧
      (0 < p.1.toNat → p.2.core.flags[0]? = some 2041#32) ∧
      (∀ j < p.1.toNat, p.2.core.mrk[j]? = some 0#8 ∧ p.2.core.lvl[j]? = some 0#32 ∧
        p.2.core.rsns[j]? = some 0xFFFFFFFF#32 ∧ p.2.core.frame_trail[j]? = some 0#32) ∧
      (FullMem c p.2 ⋆ R) ml)
    (fun J hJ => by
      c0_hsteps
      exact hJ (0#64, s) m ⟨Nat.zero_le _, rfl, hlen, ⟨rfl, rfl⟩,
        (fun h0 => by cases h0), (fun _ h0 => by cases h0), hm⟩)
    (fun J ⟨v_v, st⟩ ml ⟨hv_le, hag, hlok, hpres, hfl0, hall, hm⟩ ih => ?_)
  dsimp only at hv_le hag hlok hpres hfl0 hall hm ih ⊢
  have hco := hlok.core_ok; have hs := hlok.scratch_ok
  c0_hsplit
  · have hv_lt : v_v.toNat < c.max_vars := by
      have h1 : v_v.toNat < c.max_vars % 2 ^ 64 := by assumption
      omega
    have hv1 : (v_v + 1#64).toNat = v_v.toNat + 1 := by simp only [bv_c0]; omega
    have hmrk_l : v_v.toNat < st.core.mrk.length := by rw [hco.mrk_len]; exact hv_lt
    have hlvl_l : v_v.toNat < st.core.lvl.length := by rw [hco.lvl_len]; exact hv_lt
    have hrsn_l : v_v.toNat < st.core.rsns.length := by rw [hco.rsns_len]; exact hv_lt
    have hft_l : v_v.toNat < st.core.frame_trail.length := by rw [hco.frame_trail_len]; omega
    have hfd_l : v_v.toNat < st.core.frame_dec.length := by rw [hco.frame_dec_len]; omega
    have hph_l : v_v.toNat < st.scratch.phases.length := by rw [hs.phases_len]; exact hv_lt
    have hpt_l : v_v.toNat < st.scratch.phases_target.length := by
      rw [hs.phases_target_len]; exact hv_lt
    have hpb_l : v_v.toNat < st.scratch.phases_best.length := by
      rw [hs.phases_best_len]; exact hv_lt
    have hwb_l : v_v.toNat < st.scratch.walk_best.length := by rw [hs.walk_best_len]; exact hv_lt
    have hsc_l : v_v.toNat < st.scratch.score.length := by rw [hs.score_len]; exact hv_lt
    have hsg_l : v_v.toNat < st.scratch.sim_sig.length := by rw [hs.sim_sig_len]; exact hv_lt
    have hfl_l : v_v.toNat < st.core.flags.length := by rw [hco.flags_len]; exact hv_lt
    have hhp_l : v_v.toNat < st.scratch.heap.length := by rw [hs.heap_len_arr]; exact hv_lt
    have hps_l : v_v.toNat < st.scratch.pos.length := by rw [hs.pos_len]; exact hv_lt
    have hqp_l : v_v.toNat < st.scratch.q_prev.length := by rw [hs.q_prev_len]; exact hv_lt
    have hqn_l : v_v.toNat < st.scratch.q_next.length := by rw [hs.q_next_len]; exact hv_lt
    have hqs_l : v_v.toNat < st.scratch.q_stamp.length := by rw [hs.q_stamp_len]; exact hv_lt
    c0_hsteps_nogrp
    let st1 : FullState :=
      { core := { st.core with
          mrk := st.core.mrk.set v_v.toNat 0#8, lvl := st.core.lvl.set v_v.toNat 0#32,
          rsns := st.core.rsns.set v_v.toNat 0xFFFFFFFF#32,
          frame_trail := st.core.frame_trail.set v_v.toNat 0#32,
          frame_dec := st.core.frame_dec.set v_v.toNat 0xFFFFFFFF#32 },
        scratch := { st.scratch with
          phases := st.scratch.phases.set v_v.toNat 1#8,
          phases_target := st.scratch.phases_target.set v_v.toNat 0#8,
          phases_best := st.scratch.phases_best.set v_v.toNat 0#8,
          walk_best := st.scratch.walk_best.set v_v.toNat 1#8,
          score := st.scratch.score.set v_v.toNat 0#64,
          sim_sig := st.scratch.sim_sig.set v_v.toNat 0#64 } }
    have hm1 : (FullMem c st1 ⋆ R) m := hm
    clear hm
    refine wp_join_state0 (α := FullState)
      (fun stn mc =>
        stn.core = { s.core with
          mrk := stn.core.mrk, flags := stn.core.flags, lvl := stn.core.lvl,
          rsns := stn.core.rsns, frame_trail := stn.core.frame_trail,
          frame_dec := stn.core.frame_dec } ∧
        stn.LengthsOk c ∧ FullExtScratchPres s stn ∧
        stn.core.flags[0]? = some 2041#32 ∧
        (∀ j < v_v.toNat + 1, stn.core.mrk[j]? = some 0#8 ∧ stn.core.lvl[j]? = some 0#32 ∧
          stn.core.rsns[j]? = some 0xFFFFFFFF#32 ∧ stn.core.frame_trail[j]? = some 0#32) ∧
        (FullMem c stn ⋆ R) mc)
      (fun _ stn mc ⟨hagn, hlokn, hpresn, hfl0n, halln, hmn⟩ => by
        c0_hsteps
        exact ih (v_v + 1#64, stn) mc (by dsimp only; rw [hv1]; omega)
          ⟨by rw [hv1]; omega, hagn, hlokn, hpresn, fun _ => hfl0n,
           by rw [hv1]; exact halln, hmn⟩)
      (fun _ hJif => by
        have mk_ok : ∀ (flags' heap' pos' qp' qn' qs' : List (BitVec 32)) (mc : Mem 64),
            let stn : FullState :=
              { core := { st1.core with flags := flags' },
                scratch := { st1.scratch with
                  heap := heap', pos := pos', q_prev := qp', q_next := qn', q_stamp := qs' } }
            (FullMem c stn ⋆ R) mc →
            flags'.length = c.max_vars → heap'.length = c.max_vars →
            pos'.length = c.max_vars → qp'.length = c.max_vars →
            qn'.length = c.max_vars → qs'.length = c.max_vars →
            flags'[0]? = some 2041#32 →
            stn.core = { s.core with
              mrk := stn.core.mrk, flags := stn.core.flags, lvl := stn.core.lvl,
              rsns := stn.core.rsns, frame_trail := stn.core.frame_trail,
              frame_dec := stn.core.frame_dec } ∧
            stn.LengthsOk c ∧ FullExtScratchPres s stn ∧
            stn.core.flags[0]? = some 2041#32 ∧
            (∀ j < v_v.toNat + 1, stn.core.mrk[j]? = some 0#8 ∧ stn.core.lvl[j]? = some 0#32 ∧
              stn.core.rsns[j]? = some 0xFFFFFFFF#32 ∧ stn.core.frame_trail[j]? = some 0#32) ∧
            (FullMem c stn ⋆ R) mc := by
          intro flags' heap' pos' qp' qn' qs' mc stn hmc hf hh hp hqp hqn hqs hf0
          refine ⟨congrArg (fun x => { x with
              mrk := stn.core.mrk, flags := stn.core.flags, lvl := stn.core.lvl,
              rsns := stn.core.rsns, frame_trail := stn.core.frame_trail,
              frame_dec := stn.core.frame_dec }) hag,
            ⟨{ hco with mrk_len := by simp [stn, st1, hco.mrk_len], flags_len := hf,
                        lvl_len := by simp [stn, st1, hco.lvl_len],
                        rsns_len := by simp [stn, st1, hco.rsns_len],
                        frame_trail_len := by simp [stn, st1, hco.frame_trail_len],
                        frame_dec_len := by simp [stn, st1, hco.frame_dec_len] },
             { hs with phases_len := by simp [stn, st1, hs.phases_len],
                       phases_target_len := by simp [stn, st1, hs.phases_target_len],
                       phases_best_len := by simp [stn, st1, hs.phases_best_len],
                       walk_best_len := by simp [stn, st1, hs.walk_best_len],
                       heap_len_arr := hh, pos_len := hp, q_prev_len := hqp,
                       q_next_len := hqn, q_stamp_len := hqs,
                       score_len := by simp [stn, st1, hs.score_len],
                       sim_sig_len := by simp [stn, st1, hs.sim_sig_len] }⟩,
            hpres, hf0, fun j hj => ?_, hmc⟩
          by_cases hje : j = v_v.toNat
          · subst hje
            exact ⟨List.getElem?_set_self (by omega), List.getElem?_set_self (by omega),
              List.getElem?_set_self (by omega), List.getElem?_set_self (by omega)⟩
          · obtain ⟨a1, a2, a3, a4⟩ := hall j (by omega)
            simp only [stn, st1, List.getElem?_set_ne (Ne.symm hje)]
            exact ⟨a1, a2, a3, a4⟩
        c0_hsplit
        · have hf0_lt : (st1.core.flags.set v_v.toNat 2041#32)[0]? = some 2041#32 := by
            by_cases hz : v_v.toNat = 0
            · rw [hz]; exact List.getElem?_set_self (by rw [hco.flags_len]; omega)
            · rw [List.getElem?_set_ne hz]; exact hfl0 (by omega)
          c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
            (fun _ => True)
            (fun _ _ _ => by
              c0_hsteps_nogrp
              refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
                (fun _ => True)
                (fun _ _ _ => by
                  c0_hsteps
                  exact hJif _ m (mk_ok _ _ _ _ _ _ m hm
                    (by simp [st1, hco.flags_len]) (by simp [st1, hs.heap_len_arr])
                    (by simp [st1, hs.pos_len]) (by simp [st1, hs.q_prev_len])
                    (by simp [st1, hs.q_next_len]) (by simp [st1, hs.q_stamp_len]) hf0_lt))
                (fun _ hJn => by c0_hsteps <;> exact hJn _ trivial))
            (fun _ hJp => by c0_hsteps <;> exact hJp _ trivial)
        · have hv_ge_mv : c.mv ≤ v_v.toNat := by
            have h1 : ¬ (v_v.toNat < c.mv % 2 ^ 64) := by assumption
            rw [Nat.mod_eq_of_lt (by omega)] at h1; omega
          have hf0_ge : (st1.core.flags.set v_v.toNat 0#32)[0]? = some 2041#32 := by
            rw [List.getElem?_set_ne (by omega)]; exact hfl0 (by omega)
          c0_hsteps
          exact hJif _ m (mk_ok _ _ _ _ _ _ m hm
            (by simp [st1, hco.flags_len]) (by simp [st1, hs.heap_len_arr])
            (by simp [st1, hs.pos_len]) (by simp [st1, hs.q_prev_len])
            (by simp [st1, hs.q_next_len]) (by simp [st1, hs.q_stamp_len]) hf0_ge))
  · have hveq : v_v.toNat = c.max_vars := by
      have h1 : ¬ (v_v.toNat < c.max_vars % 2 ^ 64) := by assumption
      rw [Nat.mod_eq_of_lt (by omega)] at h1; omega
    have hft_mx : c.max_vars < st.core.frame_trail.length := by rw [hco.frame_trail_len]; omega
    have hfd_mx : c.max_vars < st.core.frame_dec.length := by rw [hco.frame_dec_len]; omega
    have hfl0_out : st.core.flags[0]? = some 2041#32 := hfl0 (by omega)
    rw [hveq] at hall
    c0_hsteps
    have hmrk : st.core.mrk = List.replicate c.max_vars 0#8 :=
      list_eq_replicate_of_forall hco.mrk_len fun j hj => (hall j hj).1
    have hlvl : st.core.lvl = List.replicate c.max_vars 0#32 :=
      list_eq_replicate_of_forall hco.lvl_len fun j hj => (hall j hj).2.1
    have hrsns : st.core.rsns = List.replicate c.max_vars 0xFFFFFFFF#32 :=
      list_eq_replicate_of_forall hco.rsns_len fun j hj => (hall j hj).2.2.1
    let ftrl' := st.core.frame_trail.set c.max_vars 0#32
    let fdec' := st.core.frame_dec.set c.max_vars 0xFFFFFFFF#32
    have hftrl : ftrl' = List.replicate (c.max_vars + 1) 0#32 := by
      refine list_eq_replicate_of_forall (by simp [ftrl', hco.frame_trail_len]) fun j hj => ?_
      by_cases hje : j = c.max_vars
      · subst hje; exact List.getElem?_set_self hft_mx
      · rw [List.getElem?_set_ne (Ne.symm hje)]
        exact (hall j (by omega)).2.2.2
    have hcore_eq :
        { s.core with
          mrk := List.replicate c.max_vars 0#8, flags := st.core.flags,
          lvl := List.replicate c.max_vars 0#32,
          rsns := List.replicate c.max_vars 0xFFFFFFFF#32,
          frame_trail := List.replicate (c.max_vars + 1) 0#32, frame_dec := fdec' } =
        { st.core with frame_trail := ftrl', frame_dec := fdec' } := by
      rw [hag, hmrk, hlvl, hrsns, ← hftrl]
    have hm_out : (FullMem c { s with
        core := { s.core with
          mrk := List.replicate c.max_vars 0#8, flags := st.core.flags,
          lvl := List.replicate c.max_vars 0#32, rsns := List.replicate c.max_vars 0xFFFFFFFF#32,
          frame_trail := List.replicate (c.max_vars + 1) 0#32, frame_dec := fdec' },
        scratch := st.scratch } ⋆ R) m := by
      rw [hcore_eq]; simpa [ftrl', fdec', hmx_to] using hm
    exact hQ st.core.flags fdec' st.scratch m hco.flags_len
      (by simp [fdec', hco.frame_dec_len]) hfl0_out hs hpres hm_out

private theorem nv_assign_lvl_wp (Γ : Env) :
    ∀ a m Q X, nvAssignLvlSpec a m Q X → Func.wp Γ Full.full_assign_lvl_body a m Q X := by
  rintro ⟨h, lit, rsn, alvl, ⟨⟩⟩ m Q X
    ⟨c, s, R, rfl, rfl, rfl, hlen, hcv1, hte0, hv0, hfl0, hunass1, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hco := hlen.core_ok; have hso := hlen.scratch_ok
  have hmx1 : 1 ≤ c.max_vars := by have := hco.cur_vars_le; omega
  have hvl : 0 < s.core.vals.length := by rw [hco.vals_len]; omega
  have hvl1 : 1 < (s.core.vals.set 0 1#8).length := by rw [List.length_set, hco.vals_len]; omega
  have hfll : 0 < s.core.flags.length := by rw [hco.flags_len]; omega
  have hphl : 0 < s.scratch.phases.length := by rw [hso.phases_len]; omega
  have hll : 0 < s.core.lvl.length := by rw [hco.lvl_len]; omega
  have hrsl : 0 < s.core.rsns.length := by rw [hco.rsns_len]; omega
  have htpl : 0 < s.core.trail_pos.length := by rw [hco.trail_pos_len]; omega
  have htrl : 0 < s.core.trl.length := by rw [hco.trl_len]; omega
  have hv0_get : s.core.vals[0]'hvl = 0#8 := by
    rw [List.getElem?_eq_getElem hvl] at hv0; exact Option.some.inj hv0
  have hfl0_get : s.core.flags[0]'hfll = 2041#32 := by
    rw [List.getElem?_eq_getElem hfll] at hfl0; exact Option.some.inj hfl0
  unfold Func.wp Full.full_assign_lvl_body
  c0_hsteps_nogrp
  · exfalso; have h1 : s.core.cur_vars % 2 ^ 64 ≤ 0 := by assumption
    have := hco.cur_vars_le; rw [Nat.mod_eq_of_lt (by omega)] at h1; omega
  · exfalso; simp [hv0_get] at hc
  have hm0 : (FullMem c { s with core := { s.core with
      vals := (s.core.vals.set 0 1#8).set 1 0xFF#8 } } ⋆ R) m := by
    simpa [show BitVec.setWidth 8 (-1 : BitVec 32) = 0xFF#8 by decide] using hm
  clear hm
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => s1 = { s with core := { s.core with
      vals := (s.core.vals.set 0 1#8).set 1 0xFF#8, unassigned := 0#64 } } ∧
      (FullMem c s1 ⋆ R) m1)
    (fun _ s1 m1 ⟨hs1_eq, hm1⟩ => by
      subst s1
      c0_hsteps_nogrp
      refine wp_join_state0 (α := List (BitVec 8))
        (fun ph' m2 => ph'.length = c.max_vars ∧
          (FullMem c { s with
            core := { s.core with
              vals := (s.core.vals.set 0 1#8).set 1 0xFF#8, unassigned := 0#64 },
            scratch := { s.scratch with phases := ph' } } ⋆ R) m2)
        (fun _ ph' m2 ⟨hph', hm2⟩ => by
          c0_hsteps_nogrp
          refine wp_join_state0 (α := List (BitVec 32))
            (fun fl' m3 => fl'.length = c.max_vars ∧
              (FullMem c { s with
                core := { s.core with
                  vals := (s.core.vals.set 0 1#8).set 1 0xFF#8,
                  flags := fl', lvl := s.core.lvl.set 0 0#32,
                  rsns := s.core.rsns.set 0 0xFFFFFFFF#32,
                  unassigned := 0#64, unflushed := s.core.unflushed + 1#64 },
                scratch := { s.scratch with phases := ph' } } ⋆ R) m3)
            (fun _ fl' m3 ⟨hfl', hm3⟩ => by
              c0_hsteps
              have hfin : (FullMem c { s with
                core := { s.core with
                  vals := (s.core.vals.set 0 1#8).set 1 0xFF#8,
                  flags := fl', lvl := s.core.lvl.set 0 0#32,
                  rsns := s.core.rsns.set 0 0xFFFFFFFF#32,
                  trl := s.core.trl.set 0 0#32,
                  trail_pos := s.core.trail_pos.set 0 0#32,
                  trail_end := 1, unassigned := 0#64,
                  unflushed := s.core.unflushed + 1#64 },
                scratch := { s.scratch with phases := ph' } } ⋆ R) m := by
                simpa [hte0] using hm
              exact hQ fl' ph' m hfl' hph' hfin)
            (fun _ hJ3 => by
              c0_hsteps
              exact hJ3 (s.core.flags.set 0 (s.core.flags[0]'hfll &&& ~~~1#32)) m
                ⟨by simp [hco.flags_len], hm⟩))
        (fun _ hJ2 => by
          c0_hsteps
          · exact hJ2 (s.scratch.phases.set 0 1#8) m ⟨by simp [hso.phases_len], hm⟩
          · exact hJ2 s.scratch.phases m1 ⟨hso.phases_len, hm1⟩))
    (fun _ hJ1 => by
      c0_hsteps
      · exact hJ1 { s with core := { s.core with
          vals := (s.core.vals.set 0 1#8).set 1 0xFF#8, unassigned := 0#64 } } m
          ⟨rfl, by simpa [hunass1] using hm⟩
      · exfalso; simp [hfl0_get] at hc)

/-! ### Region peeling & `nv_init_state_m5_wp` -/

private structure NvInitArrs (c : FullCfg) where
  (vals lit_mark mrk walk_vals phases phases_target phases_best walk_best : List (BitVec 8))
  (flags lvl rsns trl trail_pos tmp min_clr frame_trail frame_dec wvec repr min_stk :
    List (BitVec 32))
  (arena wstk heap pos shrink_stk q_prev q_next q_stamp : List (BitVec 32))
  (wsort work_stk1 work_stk2 tarjan_mark tarjan_reach : List (BitVec 32))
  (score sim_sig : List (BitVec 64))
  (glue_used last_learned delayed red_refs extend_stk scratch_buf : List (BitVec 32))
  ok : vals.length = 2 * c.max_vars ∧ lit_mark.length = 2 * c.max_vars ∧
    mrk.length = c.max_vars ∧ walk_vals.length = 2 * c.max_vars ∧
    phases.length = c.max_vars ∧ phases_target.length = c.max_vars ∧
    phases_best.length = c.max_vars ∧ walk_best.length = c.max_vars ∧
    flags.length = c.max_vars ∧ lvl.length = c.max_vars ∧ rsns.length = c.max_vars ∧
    trl.length = c.max_vars ∧ trail_pos.length = c.max_vars ∧ tmp.length = c.max_vars ∧
    min_clr.length = c.max_vars ∧ frame_trail.length = c.max_vars + 1 ∧
    frame_dec.length = c.max_vars + 1 ∧ wvec.length = 4 * c.max_vars ∧
    repr.length = 2 * c.max_vars ∧ min_stk.length = 2 * c.minDepth ∧
    arena.length = c.arena_cap ∧ wstk.length = c.wcap ∧ heap.length = c.max_vars ∧
    pos.length = c.max_vars ∧ shrink_stk.length = c.max_vars ∧ q_prev.length = c.max_vars ∧
    q_next.length = c.max_vars ∧ q_stamp.length = c.max_vars ∧ wsort.length = 2 * c.max_vars ∧
    work_stk1.length = 2 * c.max_vars ∧ work_stk2.length = 2 * c.max_vars ∧
    tarjan_mark.length = 2 * c.max_vars ∧ tarjan_reach.length = 2 * c.max_vars ∧
    score.length = c.max_vars ∧ sim_sig.length = c.max_vars ∧ glue_used.length = 64 ∧
    last_learned.length = 16 ∧ delayed.length = 3 * c.delayed_cap ∧
    red_refs.length = c.red_cap ∧ extend_stk.length = c.extend_cap ∧
    scratch_buf.length = c.scratch_cap

private def nvInitFullState (c : FullCfg) (s_hdr : FullState) (d_cur d_val : BitVec 64)
    (a : NvInitArrs c) : FullState :=
  { core := { s_hdr.core with
      d_cur := d_cur, d_val := d_val, vals := a.vals, lit_mark := a.lit_mark, mrk := a.mrk,
      flags := a.flags, lvl := a.lvl, rsns := a.rsns, trl := a.trl, trail_pos := a.trail_pos,
      tmp := a.tmp, min_clr := a.min_clr, frame_trail := a.frame_trail,
      frame_dec := a.frame_dec, wvec := a.wvec, repr := a.repr, min_stk := a.min_stk,
      arena := a.arena, wstk := a.wstk }
    scratch := { s_hdr.scratch with
      walk_vals := a.walk_vals, phases := a.phases, phases_target := a.phases_target,
      phases_best := a.phases_best, walk_best := a.walk_best, heap := a.heap, pos := a.pos,
      shrink_stk := a.shrink_stk, q_prev := a.q_prev, q_next := a.q_next, q_stamp := a.q_stamp,
      wsort := a.wsort, work_stk1 := a.work_stk1, work_stk2 := a.work_stk2,
      tarjan_mark := a.tarjan_mark, tarjan_reach := a.tarjan_reach, score := a.score,
      sim_sig := a.sim_sig, glue_used := a.glue_used, last_learned := a.last_learned,
      delayed := a.delayed, red_refs := a.red_refs, extend_stk := a.extend_stk,
      scratch_buf := a.scratch_buf } }

private structure NvBytesBlk where
  (vals wvals lmrk mrk ph ptgt pbst wbst : List (BitVec 8))

private def NvBytesBlkOk (c : FullCfg) (b : NvBytesBlk) : Prop :=
  b.vals.length = 2 * c.max_vars ∧ b.wvals.length = 2 * c.max_vars ∧
    b.lmrk.length = 2 * c.max_vars ∧ b.mrk.length = c.max_vars ∧ b.ph.length = c.max_vars ∧
    b.ptgt.length = c.max_vars ∧ b.pbst.length = c.max_vars ∧ b.wbst.length = c.max_vars

private structure NvU32_5 where
  (x1 x2 x3 x4 x5 : List (BitVec 32))

private def NvU32_5Ok (k1 k2 k3 k4 k5 : Nat) (u : NvU32_5) : Prop :=
  u.x1.length = k1 ∧ u.x2.length = k2 ∧ u.x3.length = k3 ∧ u.x4.length = k4 ∧ u.x5.length = k5

private structure NvTailBlk where
  (wvec repr wsort ws1 ws2 tmk trc : List (BitVec 32))
  (sc sig : List (BitVec 64))
  (mstk gu ll ar wstk del red ext sbuf : List (BitVec 32))

private def NvTailBlkOk (c : FullCfg) (t : NvTailBlk) : Prop :=
  t.wvec.length = 4 * c.max_vars ∧ t.repr.length = 2 * c.max_vars ∧
    t.wsort.length = 2 * c.max_vars ∧ t.ws1.length = 2 * c.max_vars ∧
    t.ws2.length = 2 * c.max_vars ∧ t.tmk.length = 2 * c.max_vars ∧
    t.trc.length = 2 * c.max_vars ∧ t.sc.length = c.max_vars ∧
    t.sig.length = c.max_vars ∧ t.mstk.length = 2 * c.minDepth ∧
    t.gu.length = 64 ∧ t.ll.length = 16 ∧ t.ar.length = c.arena_cap ∧
    t.wstk.length = c.wcap ∧ t.del.length = 3 * c.delayed_cap ∧
    t.red.length = c.red_cap ∧ t.ext.length = c.extend_cap ∧ t.sbuf.length = c.scratch_cap

private theorem nv_peel_bytes_blk (c : FullCfg) {m : Mem 64}
    (hm : region (c.hdr + BitVec.ofNat 64 1152) (c.avail - 1152) m) :
    ∃ b : NvBytesBlk, NvBytesBlkOk c b ∧
      ((((array (t := i8) c.pVals b.vals ⋆ array (t := i8) c.pLitMark b.lmrk ⋆
          array (t := i8) c.pMark b.mrk) ⋆
         (array (t := i8) c.pWalkVals b.wvals ⋆ array (t := i8) c.pPhases b.ph ⋆
          array (t := i8) c.pPhasesTarget b.ptgt ⋆ array (t := i8) c.pPhasesBest b.pbst ⋆
          array (t := i8) c.pWalkBest b.wbst)) ⋆ c.padBytes) ⋆
        region c.pFlags (c.avail - (1152 + 3 * valsBytes c.max_vars +
          5 * markBytes c.max_vars))) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hfit := c.havail_fit; have hsz := c.hsize; have hfx := fullFixedBytes_lt c.hmaxv
  have hv := valsBytes_ge c.max_vars; have hmk := markBytes_ge c.max_vars
  have hfb : fullFixedBytes c.max_vars = 1472 + 3 * valsBytes c.max_vars +
      5 * markBytes c.max_vars + 15 * u32FullBytes c.max_vars + 80 * c.max_vars +
      8 * c.minDepth := rfl
  have h0 : ((emp ⋆ emp) ⋆ region c.pVals (c.avail - 1152)) m := by
    rw [emp_sep, emp_sep]; exact hm
  let vb := valsBytes c.max_vars; let mb := markBytes c.max_vars
  let rem1 := c.avail - 1152 - vb
  obtain ⟨vals, hv1, h1⟩ := peel_step_i8 (b := c.pWalkVals) (2 * c.max_vars) vb rem1
    (c.avail - 1152) h0 (by rfl) (by omega) hv (by omega)
  obtain ⟨wvals, hv2, h2⟩ := peel_step_i8 (b := c.pLitMark) (2 * c.max_vars) vb (rem1 - vb)
    rem1 h1 (by rfl) (by omega) hv (by omega)
  obtain ⟨lmrk, hv3, h3⟩ := peel_step_i8 (b := c.pMark) (2 * c.max_vars) vb (rem1 - 2 * vb)
    (rem1 - vb) h2 (by rfl) (by omega) hv (by omega)
  obtain ⟨mrk, hm1, h4⟩ := peel_step_i8 (b := c.pPhases) c.max_vars mb
    (rem1 - 2 * vb - mb) (rem1 - 2 * vb) h3 (by rfl) (by omega) hmk (by omega)
  obtain ⟨ph, hm2, h5⟩ := peel_step_i8 (b := c.pPhasesTarget) c.max_vars mb
    (rem1 - 2 * vb - 2 * mb) (rem1 - 2 * vb - mb) h4 (by rfl) (by omega) hmk (by omega)
  obtain ⟨ptgt, hm3, h6⟩ := peel_step_i8 (b := c.pPhasesBest) c.max_vars mb
    (rem1 - 2 * vb - 3 * mb) (rem1 - 2 * vb - 2 * mb) h5 (by rfl) (by omega) hmk (by omega)
  obtain ⟨pbst, hm4, h7⟩ := peel_step_i8 (b := c.pWalkBest) c.max_vars mb
    (rem1 - 2 * vb - 4 * mb) (rem1 - 2 * vb - 3 * mb) h6 (by rfl) (by omega) hmk (by omega)
  obtain ⟨wbst, hm5, h8⟩ := peel_step_i8 (b := c.pFlags) c.max_vars mb
    (c.avail - (1152 + 3 * vb + 5 * mb)) (rem1 - 2 * vb - 4 * mb) h7
    (by rfl) (by omega) hmk (by omega)
  simp only [emp_sep] at h8
  refine ⟨⟨vals, wvals, lmrk, mrk, ph, ptgt, pbst, wbst⟩,
    ⟨hv1, hv2, hv3, hm1, hm2, hm3, hm4, hm5⟩, ?_⟩
  unfold FullCfg.padBytes; dsimp only [vb, mb] at h8
  exact sep_mono2 (sep_mono2 (fun _ h => sep_ac h)
    (fun _ h => by simp only [sep_assoc] at h ⊢; exact h)) (fun _ h => h) m h8

private theorem nv_step_u32_5 {Pre : Mem 64 → Prop} (max_v k1 k2 k3 k4 k5 : Nat)
    (a1 a2 a3 a4 a5 b : BitVec 64) {rtot rnext : Nat} {m : Mem 64}
    (ha2 : a2 = a1 + BitVec.ofNat 64 (u32FullBytes max_v))
    (ha3 : a3 = a2 + BitVec.ofNat 64 (u32FullBytes max_v))
    (ha4 : a4 = a3 + BitVec.ofNat 64 (u32FullBytes max_v))
    (ha5 : a5 = a4 + BitVec.ofNat 64 (u32FullBytes max_v))
    (hb : b = a5 + BitVec.ofNat 64 (u32FullBytes max_v))
    (hm : (Pre ⋆ region a1 rtot) m)
    (hk1 : 4 * k1 ≤ u32FullBytes max_v := by omega)
    (hk2 : 4 * k2 ≤ u32FullBytes max_v := by omega)
    (hk3 : 4 * k3 ≤ u32FullBytes max_v := by omega)
    (hk4 : 4 * k4 ≤ u32FullBytes max_v := by omega)
    (hk5 : 4 * k5 ≤ u32FullBytes max_v := by omega)
    (hrem : 5 * u32FullBytes max_v + rnext = rtot := by omega)
    (hle : rtot ≤ 2 ^ 64 := by omega) :
    ∃ u : NvU32_5, NvU32_5Ok k1 k2 k3 k4 k5 u ∧
      ((Pre ⋆ ((array (t := i32) a1 u.x1 ⋆ array (t := i32) a2 u.x2 ⋆
        array (t := i32) a3 u.x3 ⋆ array (t := i32) a4 u.x4 ⋆ array (t := i32) a5 u.x5) ⋆
       (region (a1 + BitVec.ofNat 64 (4 * k1)) (u32FullBytes max_v - 4 * k1) ⋆
        region (a2 + BitVec.ofNat 64 (4 * k2)) (u32FullBytes max_v - 4 * k2) ⋆
        region (a3 + BitVec.ofNat 64 (4 * k3)) (u32FullBytes max_v - 4 * k3) ⋆
        region (a4 + BitVec.ofNat 64 (4 * k4)) (u32FullBytes max_v - 4 * k4) ⋆
        region (a5 + BitVec.ofNat 64 (4 * k5)) (u32FullBytes max_v - 4 * k5)))) ⋆
       region b rnext) m := by
  have hsub : ∀ {m1 : Mem 64}, region a1 rtot m1 →
      ∃ u : NvU32_5, ∃ _ : PLift (NvU32_5Ok k1 k2 k3 k4 k5 u),
      ((array (t := i32) a1 u.x1 ⋆ array (t := i32) a2 u.x2 ⋆
        array (t := i32) a3 u.x3 ⋆ array (t := i32) a4 u.x4 ⋆ array (t := i32) a5 u.x5) ⋆
       (region (a1 + BitVec.ofNat 64 (4 * k1)) (u32FullBytes max_v - 4 * k1) ⋆
        region (a2 + BitVec.ofNat 64 (4 * k2)) (u32FullBytes max_v - 4 * k2) ⋆
        region (a3 + BitVec.ofNat 64 (4 * k3)) (u32FullBytes max_v - 4 * k3) ⋆
        region (a4 + BitVec.ofNat 64 (4 * k4)) (u32FullBytes max_v - 4 * k4) ⋆
        region (a5 + BitVec.ofNat 64 (4 * k5)) (u32FullBytes max_v - 4 * k5)) ⋆
       region b rnext) m1 := fun {m1} hm1 => by
    let ub := u32FullBytes max_v
    have h0 : ((emp ⋆ emp) ⋆ region a1 rtot) m1 := by rw [emp_sep, emp_sep]; exact hm1
    obtain ⟨x1, hx1, h1⟩ := peel_step_i32 (b := a2) k1 ub (4 * ub + rnext) rtot h0
      ha2.symm (by omega) hk1 (by omega)
    obtain ⟨x2, hx2, h2⟩ := peel_step_i32 (b := a3) k2 ub (3 * ub + rnext) (4 * ub + rnext) h1
      ha3.symm (by omega) hk2 (by omega)
    obtain ⟨x3, hx3, h3⟩ := peel_step_i32 (b := a4) k3 ub (2 * ub + rnext) (3 * ub + rnext) h2
      ha4.symm (by omega) hk3 (by omega)
    obtain ⟨x4, hx4, h4⟩ := peel_step_i32 (b := a5) k4 ub (ub + rnext) (2 * ub + rnext) h3
      ha5.symm (by omega) hk4 (by omega)
    obtain ⟨x5, hx5, h5⟩ := peel_step_i32 (b := b) k5 ub rnext (ub + rnext) h4
      hb.symm (by omega) hk5 (by omega)
    simp only [emp_sep] at h5
    exact ⟨⟨x1, x2, x3, x4, x5⟩, ⟨⟨hx1, hx2, hx3, hx4, hx5⟩⟩, sep_ac h5⟩
  obtain ⟨u, h2a⟩ := sep_ex_r.mp (sep_mono_r (fun _ h => hsub h) hm)
  obtain ⟨⟨hu_ok⟩, h2⟩ := sep_ex_r.mp h2a
  have h2' : (Pre ⋆
      ((array (t := i32) a1 u.x1 ⋆ array (t := i32) a2 u.x2 ⋆
        array (t := i32) a3 u.x3 ⋆ array (t := i32) a4 u.x4 ⋆ array (t := i32) a5 u.x5) ⋆
       (region (a1 + BitVec.ofNat 64 (4 * k1)) (u32FullBytes max_v - 4 * k1) ⋆
        region (a2 + BitVec.ofNat 64 (4 * k2)) (u32FullBytes max_v - 4 * k2) ⋆
        region (a3 + BitVec.ofNat 64 (4 * k3)) (u32FullBytes max_v - 4 * k3) ⋆
        region (a4 + BitVec.ofNat 64 (4 * k4)) (u32FullBytes max_v - 4 * k4) ⋆
        region (a5 + BitVec.ofNat 64 (4 * k5)) (u32FullBytes max_v - 4 * k5)) ⋆
       region b rnext)) m := h2
  exact ⟨u, hu_ok, sep_ac h2'⟩

private theorem nv_step_tail {Pre : Mem 64 → Prop} (c : FullCfg) {m : Mem 64}
    (hm : (Pre ⋆ region c.pWvec (c.avail - (1152 + 3 * valsBytes c.max_vars +
      5 * markBytes c.max_vars + 15 * u32FullBytes c.max_vars))) m) :
    ∃ t : NvTailBlk, NvTailBlkOk c t ∧
      (Pre ⋆
       ((array (t := i32) c.pWvec t.wvec ⋆ array (t := i32) c.pRepr t.repr ⋆
         array (t := i32) c.pMinStk t.mstk ⋆
         array (t := i32) c.pArena t.ar ⋆ array (t := i32) c.pWstk t.wstk) ⋆
        ((array (t := i32) c.pWsort t.wsort ⋆ array (t := i32) c.pWorkStk1 t.ws1 ⋆
           array (t := i32) c.pWorkStk2 t.ws2 ⋆ array (t := i32) c.pTarjanMark t.tmk ⋆
           array (t := i32) c.pTarjanReach t.trc) ⋆
         (array64 c.pScore t.sc ⋆ array64 c.pSimSig t.sig ⋆
           array (t := i32) c.pGlueUsed t.gu ⋆ array (t := i32) c.pLastLearned t.ll) ⋆
         (array (t := i32) c.pDelayed t.del ⋆ array (t := i32) c.pRedRefs t.red ⋆
           array (t := i32) c.pExtendStk t.ext ⋆ array (t := i32) c.pScratchBuf t.sbuf)) ⋆
        region c.pSlack c.slack)) m := by
  have hsub : ∀ {m1 : Mem 64}, region c.pWvec (c.avail - (1152 + 3 * valsBytes c.max_vars +
      5 * markBytes c.max_vars + 15 * u32FullBytes c.max_vars)) m1 →
      ∃ t : NvTailBlk, ∃ _ : PLift (NvTailBlkOk c t),
        ((array (t := i32) c.pWvec t.wvec ⋆ array (t := i32) c.pRepr t.repr ⋆
          array (t := i32) c.pMinStk t.mstk ⋆
          array (t := i32) c.pArena t.ar ⋆ array (t := i32) c.pWstk t.wstk) ⋆
         ((array (t := i32) c.pWsort t.wsort ⋆ array (t := i32) c.pWorkStk1 t.ws1 ⋆
            array (t := i32) c.pWorkStk2 t.ws2 ⋆ array (t := i32) c.pTarjanMark t.tmk ⋆
            array (t := i32) c.pTarjanReach t.trc) ⋆
          (array64 c.pScore t.sc ⋆ array64 c.pSimSig t.sig ⋆
            array (t := i32) c.pGlueUsed t.gu ⋆ array (t := i32) c.pLastLearned t.ll) ⋆
          (array (t := i32) c.pDelayed t.del ⋆ array (t := i32) c.pRedRefs t.red ⋆
            array (t := i32) c.pExtendStk t.ext ⋆ array (t := i32) c.pScratchBuf t.sbuf)) ⋆
         region c.pSlack c.slack) m1 := fun {m1} hm1 => by
    have hmx := c.hmaxv; have ha := c.harena; have hw := c.hwcap; have hd := c.hdel
    have hr := c.hred; have he := c.hext; have hs := c.hscr
    unfold dimacsBound at hmx ha hw hd hr he hs
    have hfit := c.havail_fit; have hsz := c.hsize; have hmd := fullMinDepthOf_le c.max_vars
    have hfb : fullFixedBytes c.max_vars = 1472 + 3 * valsBytes c.max_vars +
        5 * markBytes c.max_vars + 15 * u32FullBytes c.max_vars + 80 * c.max_vars +
        8 * c.minDepth := rfl
    have hslk : c.slack = c.avail - (fullFixedBytes c.max_vars + 4 * c.arena_cap + 4 * c.wcap +
        12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap) := rfl
    let r0 := c.avail - (1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars +
      15 * u32FullBytes c.max_vars)
    have h0 : (emp ⋆ region c.pWvec r0) m1 := by rw [emp_sep]; exact hm1
    obtain ⟨wvec, l1, h1⟩ := peel_step_exact_i32 (b := c.pRepr) (4 * c.max_vars)
      (r0 - 16 * c.max_vars) r0 h0 (show c.pWvec + BitVec.ofNat 64 (4 * (4 * c.max_vars)) = c.pRepr
        by unfold FullCfg.pRepr; rw [show 4 * (4 * c.max_vars) = 16 * c.max_vars by omega])
      (by omega) (by omega)
    obtain ⟨repr, l2, h2⟩ := peel_step_exact_i32 (b := c.pWsort) (2 * c.max_vars)
      (r0 - 24 * c.max_vars) (r0 - 16 * c.max_vars) h1
      (show c.pRepr + BitVec.ofNat 64 (4 * (2 * c.max_vars)) = c.pWsort by
        unfold FullCfg.pWsort; rw [show 4 * (2 * c.max_vars) = 8 * c.max_vars by omega])
      (by omega) (by omega)
    obtain ⟨wsort, l3, h3⟩ := peel_step_exact_i32 (b := c.pWorkStk1) (2 * c.max_vars)
      (r0 - 32 * c.max_vars) (r0 - 24 * c.max_vars) h2
      (show c.pWsort + BitVec.ofNat 64 (4 * (2 * c.max_vars)) = c.pWorkStk1 by
        unfold FullCfg.pWorkStk1; rw [show 4 * (2 * c.max_vars) = 8 * c.max_vars by omega])
      (by omega) (by omega)
    obtain ⟨ws1, l4, h4⟩ := peel_step_exact_i32 (b := c.pWorkStk2) (2 * c.max_vars)
      (r0 - 40 * c.max_vars) (r0 - 32 * c.max_vars) h3
      (show c.pWorkStk1 + BitVec.ofNat 64 (4 * (2 * c.max_vars)) = c.pWorkStk2 by
        unfold FullCfg.pWorkStk2; rw [show 4 * (2 * c.max_vars) = 8 * c.max_vars by omega])
      (by omega) (by omega)
    obtain ⟨ws2, l5, h5⟩ := peel_step_exact_i32 (b := c.pTarjanMark) (2 * c.max_vars)
      (r0 - 48 * c.max_vars) (r0 - 40 * c.max_vars) h4
      (show c.pWorkStk2 + BitVec.ofNat 64 (4 * (2 * c.max_vars)) = c.pTarjanMark by
        unfold FullCfg.pTarjanMark; rw [show 4 * (2 * c.max_vars) = 8 * c.max_vars by omega])
      (by omega) (by omega)
    obtain ⟨tmk, l6, h6⟩ := peel_step_exact_i32 (b := c.pTarjanReach) (2 * c.max_vars)
      (r0 - 56 * c.max_vars) (r0 - 48 * c.max_vars) h5
      (show c.pTarjanMark + BitVec.ofNat 64 (4 * (2 * c.max_vars)) = c.pTarjanReach by
        unfold FullCfg.pTarjanReach; rw [show 4 * (2 * c.max_vars) = 8 * c.max_vars by omega])
      (by omega) (by omega)
    obtain ⟨trc, l7, h7⟩ := peel_step_exact_i32 (b := c.pScore) (2 * c.max_vars)
      (r0 - 64 * c.max_vars) (r0 - 56 * c.max_vars) h6
      (show c.pTarjanReach + BitVec.ofNat 64 (4 * (2 * c.max_vars)) = c.pScore by
        unfold FullCfg.pScore; rw [show 4 * (2 * c.max_vars) = 8 * c.max_vars by omega])
      (by omega) (by omega)
    obtain ⟨sc, l8, h8⟩ := peel_step_exact_i64 (b := c.pSimSig) c.max_vars
      (r0 - 72 * c.max_vars) (r0 - 64 * c.max_vars) h7 rfl (by omega) (by omega)
    obtain ⟨sig, l9, h9⟩ := peel_step_exact_i64 (b := c.pMinStk) c.max_vars
      (r0 - 80 * c.max_vars) (r0 - 72 * c.max_vars) h8 rfl (by omega) (by omega)
    let r10 := r0 - 80 * c.max_vars
    obtain ⟨mstk, l10, h10⟩ := peel_step_exact_i32 (b := c.pGlueUsed) (2 * c.minDepth)
      (r10 - 8 * c.minDepth) r10 h9
      (show c.pMinStk + BitVec.ofNat 64 (4 * (2 * c.minDepth)) = c.pGlueUsed by
        unfold FullCfg.pGlueUsed; rw [show 4 * (2 * c.minDepth) = 8 * c.minDepth by omega])
      (by omega) (by omega)
    obtain ⟨gu, l11, h11⟩ := peel_step_exact_i32 (b := c.pLastLearned) 64
      (r10 - 8 * c.minDepth - 256) (r10 - 8 * c.minDepth) h10 rfl (by omega) (by omega)
    obtain ⟨ll, l12, h12⟩ := peel_step_exact_i32 (b := c.pArena) 16
      (r10 - 8 * c.minDepth - 320) (r10 - 8 * c.minDepth - 256) h11 rfl (by omega) (by omega)
    let r13 := r10 - 8 * c.minDepth - 320
    obtain ⟨ar, l13, h13⟩ := peel_step_exact_i32 (b := c.pWstk) c.arena_cap
      (r13 - 4 * c.arena_cap) r13 h12 rfl (by omega) (by omega)
    obtain ⟨wstk, l14, h14⟩ := peel_step_exact_i32 (b := c.pDelayed) c.wcap
      (r13 - 4 * c.arena_cap - 4 * c.wcap) (r13 - 4 * c.arena_cap) h13 rfl (by omega) (by omega)
    obtain ⟨del, l15, h15⟩ := peel_step_exact_i32 (b := c.pRedRefs) (3 * c.delayed_cap)
      (4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap + c.slack)
      (r13 - 4 * c.arena_cap - 4 * c.wcap) h14
      (show c.pDelayed + BitVec.ofNat 64 (4 * (3 * c.delayed_cap)) = c.pRedRefs by
        unfold FullCfg.pRedRefs; rw [show 4 * (3 * c.delayed_cap) = 12 * c.delayed_cap by omega])
      (by omega) (by omega)
    obtain ⟨red, l16, h16⟩ := peel_step_exact_i32 (b := c.pExtendStk) c.red_cap
      (4 * c.extend_cap + 4 * c.scratch_cap + c.slack)
      (4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap + c.slack) h15 rfl (by omega) (by omega)
    obtain ⟨ext, l17, h17⟩ := peel_step_exact_i32 (b := c.pScratchBuf) c.extend_cap
      (4 * c.scratch_cap + c.slack) (4 * c.extend_cap + 4 * c.scratch_cap + c.slack)
      h16 rfl (by omega) (by omega)
    obtain ⟨sbuf, l18, h18⟩ := peel_step_exact_i32 (b := c.pSlack) c.scratch_cap c.slack
      (4 * c.scratch_cap + c.slack) h17 rfl (by omega) (by omega)
    simp only [emp_sep] at h18
    exact ⟨⟨wvec, repr, wsort, ws1, ws2, tmk, trc, sc, sig, mstk, gu, ll, ar, wstk, del, red,
      ext, sbuf⟩,
      ⟨⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18⟩⟩,
      sep_mono2 (fun _ h => sep_ac h) (fun _ h => h) _ h18⟩
  obtain ⟨t, h2a⟩ := sep_ex_r.mp (sep_mono_r (fun _ h => hsub h) hm)
  obtain ⟨⟨ht_ok⟩, h2⟩ := sep_ex_r.mp h2a
  exact ⟨t, ht_ok, h2⟩

private theorem nv_avail_to_arrays (c : FullCfg) (s_hdr : FullState) {m : Mem 64}
    (hm : region (c.hdr + BitVec.ofNat 64 1152) (c.avail - 1152) m) :
    ∃ a : NvInitArrs c, (FullCoreArrays c (nvInitFullState c s_hdr 0#64 0#64 a).core ⋆
      FullScratchArrays c (nvInitFullState c s_hdr 0#64 0#64 a).scratch ⋆ c.pad) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hfit := c.havail_fit; have hsz := c.hsize; have hfx := fullFixedBytes_lt c.hmaxv
  have hu4 := u32FullBytes_ge4 c.max_vars; have hu := u32FullBytes_ge c.max_vars
  have hfb : fullFixedBytes c.max_vars = 1472 + 3 * valsBytes c.max_vars +
      5 * markBytes c.max_vars + 15 * u32FullBytes c.max_vars + 80 * c.max_vars +
      8 * c.minDepth := rfl
  let ub := u32FullBytes c.max_vars
  let r15 := c.avail - (1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars + 15 * ub)
  have h15le : 1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars + 15 * ub ≤ c.avail := by
    dsimp only [ub]; omega
  have hrem0_eq : c.avail - (1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars) =
      15 * ub + r15 := by dsimp only [r15, ub]; omega
  obtain ⟨b, hb_ok, h_0⟩ := nv_peel_bytes_blk c hm
  rw [hrem0_eq] at h_0
  obtain ⟨u1, hu1_ok, h_1⟩ := nv_step_u32_5 c.max_vars c.max_vars c.max_vars c.max_vars c.max_vars
    c.max_vars c.pFlags c.pLevel c.pReason c.pTrail c.pTrailPos c.pTmp (rtot := 15 * ub + r15)
    (rnext := 10 * ub + r15) rfl rfl rfl rfl rfl h_0 hu4 hu4 hu4 hu4 hu4
    (by dsimp only [ub]; omega) (by dsimp only [r15]; omega)
  obtain ⟨u2, hu2_ok, h_2⟩ := nv_step_u32_5 c.max_vars c.max_vars c.max_vars c.max_vars c.max_vars
    c.max_vars c.pTmp c.pHeap c.pPos c.pMinClr c.pShrinkStk c.pQPrev (rtot := 10 * ub + r15)
    (rnext := 5 * ub + r15) rfl rfl rfl rfl rfl h_1 hu4 hu4 hu4 hu4 hu4
    (by dsimp only [ub]; omega) (by omega)
  obtain ⟨u3, hu3_ok, h_3⟩ := nv_step_u32_5 c.max_vars c.max_vars c.max_vars c.max_vars
    (c.max_vars + 1) (c.max_vars + 1) c.pQPrev c.pQNext c.pQStamp c.pFrameTrail c.pFrameDec c.pWvec
    (rtot := 5 * ub + r15) (rnext := r15) rfl rfl rfl rfl rfl h_2 hu4 hu4 hu4 hu hu rfl
    (by omega)
  have h_3r : (_ ⋆ region c.pWvec (c.avail - (1152 + 3 * valsBytes c.max_vars +
      5 * markBytes c.max_vars + 15 * u32FullBytes c.max_vars))) m := h_3
  obtain ⟨tl, htl_ok, h_4⟩ := nv_step_tail c h_3r
  obtain ⟨hv1, hv2, hv3, hm1, hm2, hm3, hm4, hm5⟩ := hb_ok
  obtain ⟨lfl, llv, lrs, ltr, ltp⟩ := hu1_ok
  obtain ⟨ltmp, lhp, lps, lmc, lsh⟩ := hu2_ok
  obtain ⟨lqp, lqn, lqs, lft, lfd⟩ := hu3_ok
  obtain ⟨lwv, lrp, lws, l1, l2, ltm, ltrc, lsc, lsg, lms, lgu, lll, lar, lwk, ldl, lrd,
    lex, lsb⟩ := htl_ok
  let a : NvInitArrs c :=
    ⟨b.vals, b.lmrk, b.mrk, b.wvals, b.ph, b.ptgt, b.pbst, b.wbst, u1.x1, u1.x2, u1.x3, u1.x4,
      u1.x5, u2.x1, u2.x4, u3.x4, u3.x5, tl.wvec, tl.repr, tl.mstk, tl.ar, tl.wstk, u2.x2, u2.x3,
      u2.x5, u3.x1, u3.x2, u3.x3, tl.wsort, tl.ws1, tl.ws2, tl.tmk, tl.trc, tl.sc, tl.sig, tl.gu,
      tl.ll, tl.del, tl.red, tl.ext, tl.sbuf, ⟨hv1, hv3, hm1, hv2, hm2, hm3, hm4, hm5, lfl, llv,
      lrs, ltr, ltp, ltmp, lmc, lft, lfd, lwv, lrp, lms, lar, lwk, lhp, lps, lsh, lqp, lqn, lqs,
      lws, l1, l2, ltm, ltrc, lsc, lsg, lgu, lll, ldl, lrd, lex, lsb⟩⟩
  refine ⟨a, ?_⟩
  dsimp only [nvInitFullState]
  unfold FullCoreArrays FullCoreByteArrs FullCoreU32A FullCoreU32B FullCoreDynArrs
    FullScratchArrays FullScrByteArrs FullScrU32A FullScrWksArrs FullScrMetaArrs
    FullScrDynArrs FullCfg.pad FullCfg.padU32A FullCfg.padU32B FullCfg.padU32C
  exact sep_ac h_4

private theorem nv_init_state_split_tail {hdr_addr cnf_ptr : BitVec 64} {avail j : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (h1152 : 1152 ≤ avail) (hav64 : avail ≤ 2 ^ 64)
    (hm : (bytes cnf_ptr fullNvSatBytes ⋆ dimacsState hdr_addr 1#64 1#64
      (cnf_ptr + BitVec.ofNat 64 j) 1#64 ⋆ region (hdr_addr + 32#64) (avail - 32) ⋆ R) m) :
    ∃ ws : List (BitVec 64), ws.length = 140 ∧
      (hdrTail4 hdr_addr (ws.take 35) ((ws.drop 35).take 35) ((ws.drop 70).take 35)
          ((ws.drop 105).take 35) ⋆
        (region (hdr_addr + 1152#64) (avail - 1152) ⋆ bytes cnf_ptr fullNvSatBytes ⋆
          dimacsState hdr_addr 1#64 1#64 (cnf_ptr + BitVec.ofNat 64 j) 1#64 ⋆ R)) m := by
  have h1 : ((region (hdr_addr + 32#64) 1120 ⋆ region (hdr_addr + 1152#64) (avail - 1152)) ⋆
      (bytes cnf_ptr fullNvSatBytes ⋆ dimacsState hdr_addr 1#64 1#64
        (cnf_ptr + BitVec.ofNat 64 j) 1#64 ⋆ R)) m :=
    sep_mono (fun _ h => reg_peel (b := hdr_addr + 1152#64) (n1 := 1120) (n2 := avail - 1152) h
      (hb := by rw [BitVec.add_assoc]; rfl) (hn := by omega) (hle := by omega))
      (sep_ac hm : (region (hdr_addr + 32#64) (avail - 32) ⋆ (bytes cnf_ptr fullNvSatBytes ⋆
        dimacsState hdr_addr 1#64 1#64 (cnf_ptr + BitVec.ofNat 64 j) 1#64 ⋆ R)) m)
  have h2 := sep_mono (fun _ (h : region (hdr_addr + 32#64) 1120 _) =>
    region_to_array64 140 (by decide) h) (sep_ac h1 : (region (hdr_addr + 32#64) 1120 ⋆
      (region (hdr_addr + 1152#64) (avail - 1152) ⋆ bytes cnf_ptr fullNvSatBytes ⋆
        dimacsState hdr_addr 1#64 1#64 (cnf_ptr + BitVec.ofNat 64 j) 1#64 ⋆ R)) m)
  obtain ⟨ws, h3⟩ := sep_ex_l.mp h2
  obtain ⟨hwl, h4⟩ := sep_pure_l.mp h3
  have h5 := sep_mono (fun _ (h : array64 (hdr_addr + 32#64) ws _) => by
    have ht := array64_to_hdrTail4 hwl (by rwa [sep_emp])
    rwa [sep_emp] at ht) h4
  exact ⟨ws, hwl, sep_ac h5⟩

private def nvCalcZeroCapSpec : Spec [i64] [i64] := fun (rem, ()) m Q _ =>
  rem.toNat < 8192 ∧ Q (0#64, ()) m

private theorem nv_calc_ext_cap_m5_wp (Γ : Env) :
    ∀ a m Q X, nvCalcZeroCapSpec a m Q X →
      Func.wp Γ FullM5Orch.full_calc_ext_cap_m5_body a m Q X := by
  rintro ⟨rem, ⟨⟩⟩ m Q X ⟨hlt, hQ⟩
  unfold Func.wp FullM5Orch.full_calc_ext_cap_m5_body; fp_head_steps
  rw [show rem.ult 8192 = decide (rem.toNat < 8192) from by rw [BitVec.ult]; rfl]
  refine wp_jnz_of (fun _ => by fp_head_steps; exact hQ) (fun hf => by nv_ult_f hf; omega)

private theorem nv_calc_scr_cap_m5_wp (Γ : Env) :
    ∀ a m Q X, nvCalcZeroCapSpec a m Q X →
      Func.wp Γ FullM5Orch.full_calc_scr_cap_m5_body a m Q X := by
  rintro ⟨rem, ⟨⟩⟩ m Q X ⟨hlt, hQ⟩
  unfold Func.wp FullM5Orch.full_calc_scr_cap_m5_body; fp_head_steps
  rw [show rem.ult 8192 = decide (rem.toNat < 8192) from by rw [BitVec.ult]; rfl]
  refine wp_jnz_of (fun _ => by fp_head_steps; exact hQ) (fun hf => by nv_ult_f hf; omega)

private theorem nv_init_state_m5_wp (Γ : Env)
    (hHdr : ∀ a m Q X, kissatParseHeaderSpec a m Q X →
      Γ "kissat_parse_header" [i64, i64, i64] [.bool] a m Q X)
    (hFixed : ∀ a m Q X, fullFixedBytesSpec a m Q X →
      Γ "full_fixed_bytes" [i64] [i64] a m Q X)
    (hMaxV : ∀ a m Q X, fullCalcMaxVSpec a m Q X →
      Γ "full_calc_max_v" [i64, i64, i64, i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, nvCalcZeroCapSpec a m Q X →
      Γ "full_calc_ext_cap_m5" [i64] [i64] a m Q X)
    (hScr : ∀ a m Q X, nvCalcZeroCapSpec a m Q X →
      Γ "full_calc_scr_cap_m5" [i64] [i64] a m Q X)
    (hArenas : ∀ a m Q X, fullInitArenasSpec a m Q X →
      Γ "full_init_arenas" [i64, i64, i64, i64] [] a m Q X)
    (hInitHdr : ∀ a m Q X, nvInitHdrSpec a m Q X →
      Γ "full_init_hdr" [i64, i64, i64, i64] [] a m Q X)
    (hZt1 : ∀ a m Q X, fullZeroTables1Spec a m Q X →
      Γ "full_zero_tables1" [i64] [] a m Q X)
    (hZt2 : ∀ a m Q X, nvZeroTables2Spec a m Q X →
      Γ "full_zero_tables2" [i64] [] a m Q X) :
    ∀ a m Q X, nvInitStateM5Spec a m Q X →
      Func.wp Γ FullM5Orch.full_init_state_m5_body a m Q X := by
  rintro ⟨cnf_ptr, cend, hdr_addr, avail, fuel, ⟨⟩⟩ m Q X
    ⟨R, rfl, hfit, hav_fit, hav_lo, hav_hi, hm_in, hQ⟩
  have hav_le : avail.toNat ≤ 2 ^ 64 := by omega
  have hm0 : (bytes cnf_ptr fullNvSatBytes ⋆ (region hdr_addr 32 ⋆
      region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32)) ⋆ R) m := by
    rw [region_merge_eq (a := hdr_addr) (n1 := 32) (n2 := avail.toNat - 32) (n := avail.toNat)
      (by omega) hav_le]; exact hm_in
  have hm0a := sep_mono (fun _ => Kissat.region32_to_dimacsState)
    (sep_ac hm0 : (region hdr_addr 32 ⋆ (bytes cnf_ptr fullNvSatBytes ⋆
      region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32) ⋆ R)) m)
  obtain ⟨mv0, hm0b⟩ := sep_ex_l.mp hm0a
  obtain ⟨nc0, hm0c⟩ := sep_ex_l.mp hm0b
  obtain ⟨cur0, hm0d⟩ := sep_ex_l.mp hm0c
  obtain ⟨val0, hm_pre⟩ := sep_ex_l.mp hm0d
  unfold Func.wp FullM5Orch.full_init_state_m5_body
  apply wp_call_of_spec; apply hHdr
  change kissatParseHeaderSpec
    (cnf_ptr, cnf_ptr + BitVec.ofNat 64 fullNvSatBytes.length, hdr_addr, ()) m _ _
  refine ⟨mv0, nc0, cur0, val0, fullNvSatBytes,
    region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32) ⋆ R, rfl, hfit, sep_ac hm_pre, ?_⟩
  rw [fullNvSat_header]
  intro j m0 hmv_bd hnc_bd hj hdrop hm0
  have hj9 : j = 9 := fullNvSat_drop_eq_iff (by change j ≤ 14 at hj; exact hj) (by decide) hdrop
  subst hj9
  refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
  fp_head_steps
  apply wp_call_of_spec; apply hFixed
  change fullFixedBytesSpec (1#64, ()) m0 _ _
  refine ⟨by unfold dimacsBound; decide, ?_⟩
  rw [show (1#64 : BitVec 64).toNat = 1 from rfl, fullFixedBytes_1_eq]
  dsimp only; fp_head_steps
  rw [show avail.ult 1752#64 = decide (avail.toNat < 1752) from by rw [BitVec.ult]; rfl]
  refine wp_jnz_of (fun hlt => by nv_ult_t hlt; omega) (fun _ => ?_)
  fp_head_steps
  have hsub_f0 : avail - 1752#64 = BitVec.ofNat 64 (avail.toNat - 1752) := by
    simpa [bv_ofNat_toNat_eq avail] using bv_sub_ofNat (a := avail.toNat) (b := 1752)
      (by omega) avail.isLt
  have h176 : ((1#64 : BitVec 64) * 40 + 136) = 176#64 := rfl
  rw [hsub_f0, h176, bv_ult_eq (by omega) (by decide)]
  refine wp_jnz_of (fun hlt2 => by nv_ult_t hlt2; omega) (fun _ => ?_)
  apply wp_call_of_spec; apply hMaxV
  change fullCalcMaxVSpec (avail, 1#64, 1#64, 1752#64, ()) m0 _ _
  refine ⟨by unfold dimacsBound; decide, by unfold dimacsBound; decide,
    by rw [show (1#64 : BitVec 64).toNat = 1 from rfl, fullFixedBytes_1_eq]; rfl,
    by rw [show (1752#64 : BitVec 64).toNat = 1752 from rfl,
           show (1#64 : BitVec 64).toNat = 1 from rfl]; omega, ?_⟩
  intro max_v hmv_le hmx_bd hmax_fit
  rw [show (1#64 : BitVec 64).toNat = 1 from rfl] at hmv_le hmax_fit
  have hmx_b := hmx_bd; unfold dimacsBound at hmx_b
  have hfx_m_lt := fullFixedBytes_lt hmx_bd
  have hfx_m_ge : 1752 ≤ fullFixedBytes max_v.toNat := by
    unfold fullFixedBytes valsBytes markBytes u32FullBytes fullMinDepthOf; split <;> omega
  fp_head_steps; apply wp_call_of_spec; apply hFixed
  change fullFixedBytesSpec (max_v, ()) m0 _ _
  refine ⟨hmx_bd, ?_⟩; dsimp only; fp_head_steps
  let rem := avail.toNat - fullFixedBytes max_v.toNat
  have hrem_eq : avail - BitVec.ofNat 64 (fullFixedBytes max_v.toNat) = BitVec.ofNat 64 rem := by
    simpa [bv_ofNat_toNat_eq avail] using bv_sub_ofNat (by omega) avail.isLt
  have hrem_to : (BitVec.ofNat 64 rem).toNat = rem := bv64_ofNat_toNat (by omega)
  have hrem_lo : 176 ≤ rem := by omega
  have hrem_hi : rem < 8192 := by omega
  rw [hrem_eq]
  refine wp_join_group (fun (v : Tup Val [i64]) md => v.1 = 8#64 ∧ md = m0) ?_ ?_
  · rintro _ ⟨_, ⟨⟩⟩ md ⟨rfl, rfl⟩; simp only [Blocks.get_here]; fp_head_steps
    apply wp_call_of_spec; apply hExt
    change nvCalcZeroCapSpec (BitVec.ofNat 64 rem, ()) md _ _
    refine ⟨by rw [hrem_to]; exact hrem_hi, ?_⟩; dsimp only; fp_head_steps
    apply wp_call_of_spec; apply hScr
    change nvCalcZeroCapSpec (BitVec.ofNat 64 rem, ()) md _ _
    refine ⟨by rw [hrem_to]; exact hrem_hi, ?_⟩; dsimp only; fp_head_steps
    refine wp_join_group (fun (v : Tup Val [i64, i64, i64]) mg =>
      v.1 = 0#64 ∧ v.2.1 = 0#64 ∧ v.2.2.1 = 96#64 ∧ mg = md) ?_ ?_
    · rintro _ ⟨_, _, _, ⟨⟩⟩ mg ⟨rfl, rfl, rfl, rfl⟩; simp only [Blocks.get_here]
      have hm0_ac : (bytes cnf_ptr fullNvSatBytes ⋆ dimacsState hdr_addr 1#64 1#64
          (cnf_ptr + 9#64) 1#64 ⋆ region (hdr_addr + 32#64) (avail.toNat - 32) ⋆ R) mg :=
        sep_ac hm0
      obtain ⟨ws, hwl, _⟩ := nv_init_state_split_tail (by omega) hav_le hm0_ac
      clear hm_in hm_pre hm0; fp_head_steps
      have hw0l : (ws.take 35).length = 35 := by simp [hwl]
      have hw1l : ((ws.drop 35).take 35).length = 35 := by simp [hwl]
      have hw2l : ((ws.drop 70).take 35).length = 35 := by simp [hwl]
      have hw3l : ((ws.drop 105).take 35).length = 35 := by simp [hwl]
      let ws1 := ws.take 35 ++ ((ws.drop 35).take 35).set 17 8#64 ++
        (ws.drop 70).take 35 ++ (((ws.drop 105).take 35).set 4 0#64).set 7 0#64
      have hm_arr : (array64 (hdr_addr + 32) ws1 ⋆ (region (hdr_addr + 1152#64)
          (avail.toNat - 1152) ⋆ bytes cnf_ptr fullNvSatBytes ⋆
          dimacsState hdr_addr 1#64 1#64 (cnf_ptr + 9#64) 1#64 ⋆ R)) m := by
        rwa [hdrTail4_eq_array64 hw0l (by simp [hw1l]) hw2l (by simp [hw3l])] at hm
      have hws1_len : ws1.length = 140 := by simp [ws1, hw0l, hw1l, hw2l, hw3l]
      have h52 : ws1[52]? = some 8#64 := by
        dsimp only [ws1]; rw [append4_getElem?_1 hw0l (by simp [hw1l]) (by decide) (by decide)]
        simp [hw1l]
      have h109 : ws1[109]? = some 0#64 := by
        dsimp only [ws1]; rw [append4_getElem?_3 hw0l (by simp [hw1l]) hw2l (by decide)]
        simp [hw3l]
      have h112 : ws1[112]? = some 0#64 := by
        dsimp only [ws1]; rw [append4_getElem?_3 hw0l (by simp [hw1l]) hw2l (by decide)]
        simp [hw3l]
      let adyn := rem - 96
      have hsub_dyn : BitVec.ofNat 64 rem - 96#64 = BitVec.ofNat 64 adyn :=
        bv_sub_ofNat (by omega) (by omega)
      have hadyn_to : (BitVec.ofNat 64 adyn).toNat = adyn := bv64_ofNat_toNat (by omega)
      rw [hsub_dyn]
      apply wp_call_of_spec; apply hArenas
      change fullInitArenasSpec (hdr_addr, hdr_addr, max_v, BitVec.ofNat 64 adyn, ()) m _ _
      refine ⟨ws1, 8, 0, 0, _, rfl, hws1_len, hmx_bd, by unfold dimacsBound; decide,
        by unfold dimacsBound; decide, by unfold dimacsBound; decide,
        h52, h109, h112, by rw [hadyn_to]; omega, hm_arr,
        fun acap wcap rcap ws2 m2 hws2l hac hwc hrc hsum hwpos hws2 hm2 => ?_⟩
      rw [hadyn_to] at hsum hwpos
      have hwcap_pos : 1 ≤ wcap := hwpos (by omega)
      let c : FullCfg :=
        { hdr := hdr_addr, avail := avail.toNat, mv := 1, max_vars := max_v.toNat,
          bva_cap := max_v.toNat - 1, nc := 1, arena_cap := acap, wcap := wcap,
          delayed_cap := 8, red_cap := rcap, extend_cap := 0, scratch_cap := 0,
          hbva := by omega, hmv := by unfold dimacsBound; decide, hmaxv := hmx_bd,
          hnc := by unfold dimacsBound; decide, harena := hac, hwcap := hwc,
          hdel := by unfold dimacsBound; decide, hred := hrc,
          hext := by unfold dimacsBound; decide, hscr := by unfold dimacsBound; decide,
          havail_fit := hav_fit, hsize := by omega }
      apply wp_call_of_spec; apply hInitHdr
      change nvInitHdrSpec (hdr_addr, 1#64, max_v, fuel, ()) m2 _ _
      have hws2_c := hws2 c rfl rfl rfl rfl rfl rfl rfl rfl
      refine ⟨c, ws2, _, rfl, rfl, (bv_ofNat_toNat_eq max_v).symm, hws2l,
        fun s0 i hi => ?_, hm2, fun s_hdr m3 hcv hunass hal hwl hte hpr hcl htl hfu hunf hpb
          hmcl hmcf hoom hdm hinc hel hm3 => ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        unfold Full.hdrTailWords hdrTailWords0 hdrTailWords1 hdrTailWords2 hdrTailWords3
        repeat rcases hws2_c with ⟨h_, hws2_c⟩
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;> assumption
      · have h3a := sep_mono (fun _ h => nv_avail_to_arrays c s_hdr h)
          (sep_ac hm3 : (region (c.hdr + BitVec.ofNat 64 1152) (c.avail - 1152) ⋆
            (bytes cnf_ptr fullNvSatBytes ⋆ dimacsState c.hdr 1#64 1#64 (cnf_ptr + 9#64) 1#64 ⋆
              array64 (c.hdr + 32) (Full.hdrTailWords c s_hdr) ⋆ R)) m3)
        obtain ⟨arrs, h3b⟩ := sep_ex_l.mp h3a
        let s_pre := nvInitFullState c s_hdr (cnf_ptr + 9#64) 1#64 arrs
        have h_pre_ht : Full.hdrTailWords c s_pre = Full.hdrTailWords c s_hdr := by
          simp only [Full.hdrTailWords, hdrTailWords0, hdrTailWords1, hdrTailWords2,
            hdrTailWords3, s_pre, nvInitFullState]
        have hm_pre_full : (FullMem c s_pre ⋆ (bytes cnf_ptr fullNvSatBytes ⋆ R)) m3 := by
          unfold FullMem; rw [h_pre_ht]
          exact sep_ac h3b
        obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17,
          o18, o19, o20, o21, o22, o23, o24, o25, o26, o27, o28, o29, o30, o31, o32, o33, o34,
          o35, o36, o37, o38, o39, o40, o41⟩ := arrs.ok
        have hlen_pre : s_pre.LengthsOk c :=
          ⟨⟨o1, o2, o3, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22,
            by simp [s_pre, nvInitFullState, hcv, c],
            by simp [s_pre, nvInitFullState, hcv, c]; omega,
            by simp [s_pre, nvInitFullState, hal],
            by simp [s_pre, nvInitFullState, hwl]; exact hwcap_pos,
            by simp [s_pre, nvInitFullState, hte], by simp [s_pre, nvInitFullState, hpr, hte],
            by simp [s_pre, nvInitFullState, htl], by simp [s_pre, nvInitFullState, hmcl]⟩,
           ⟨o4, o5, o6, o7, o8, o23, o24, o25, o26, o27, o28, o29, o30, o31, o32, o33, o34,
            o35, o36, o37, o38, o39, o40, o41⟩⟩
        apply wp_call_of_spec; apply hZt1
        change fullZeroTables1Spec (c.hdr, ()) m3 _ _
        refine ⟨c, s_pre, bytes cnf_ptr fullNvSatBytes ⋆ R, rfl, hlen_pre, hm_pre_full,
          fun wstk' mstk' repr' sc1 m4 hwstk' hmstk' hrepr' hsc1 hext1 _ hm4 => ?_⟩
        let s_1 : FullState :=
          { s_pre with
            core := { s_pre.core with
              vals := List.replicate (2 * c.max_vars) 0#8,
              lit_mark := List.replicate (2 * c.max_vars) 0#8,
              wvec := List.replicate (4 * c.max_vars) 0#32, wstk := wstk',
              min_stk := mstk', repr := repr' },
            scratch := sc1 }
        have hlen1 : s_1.LengthsOk c :=
          ⟨{ hlen_pre.core_ok with
              vals_len := by simp [s_1], lit_mark_len := by simp [s_1],
              wvec_len := by simp [s_1], repr_len := hrepr', min_stk_len := hmstk',
              wstk_len_arr := hwstk' }, hsc1⟩
        apply wp_call_of_spec; apply hZt2
        change nvZeroTables2Spec (c.hdr, ()) m4 _ _
        refine ⟨c, s_1, bytes cnf_ptr fullNvSatBytes ⋆ R, rfl, Nat.le_refl 1, hlen1, hm4,
          fun flags' fdec' sc2 m5 hfl' hfd' hfl0' hsc2 hpres2 hm5 => ?_⟩
        dsimp only; rw [wp_ret]
        let s_2 : FullState :=
          { s_1 with
            core := { s_1.core with
              mrk := List.replicate c.max_vars 0#8, flags := flags',
              lvl := List.replicate c.max_vars 0#32,
              rsns := List.replicate c.max_vars 0xFFFFFFFF#32,
              frame_trail := List.replicate (c.max_vars + 1) 0#32, frame_dec := fdec' },
            scratch := sc2 }
        have hlen2 : s_2.LengthsOk c :=
          ⟨{ hlen1.core_ok with
              mrk_len := by simp [s_2], flags_len := hfl', lvl_len := by simp [s_2],
              rsns_len := by simp [s_2], frame_trail_len := by simp [s_2],
              frame_dec_len := hfd' }, hsc2⟩
        have hext2 : s_2.scratch.extend_len = 0 := by
          dsimp only [s_2]; rw [hpres2.2, hext1]; exact hel
        exact hQ c s_2 m5 rfl rfl rfl rfl hlen2 hcv rfl hal hwl hte hpr hcl hfu
          hunass hunf hoom rfl rfl rfl hfl0' hext2 (sep_ac hm5)
    · intro Jg hJg; fp_head_steps
      refine wp_jnz_of (fun _ => ?_) (fun _ => ?_) <;>
        (fp_head_steps; exact hJg _ md ⟨rfl, rfl, rfl, rfl⟩)
  · intro Jd hJd; fp_head_steps
    rw [show (524288 : BitVec 64) = BitVec.ofNat 64 524288 from rfl,
      bv_ule_eq (by decide) (by omega)]
    refine wp_jnz_of (fun hbig => by nv_ult_t hbig; omega) (fun _ => ?_)
    fp_head_steps; exact hJd (8#64, ()) m0 ⟨rfl, rfl⟩

/-! ## 5. Parse, BCP, Sweep, Extend, & Preprocess `Func.wp` Proofs -/

private theorem nv_ingest_cl_wp (Γ : Env)
    (hNext : ∀ a m Q X, kissatNextLitSpec a m Q X →
      Γ "kissat_next_lit" [i64, i64] [i64] a m Q X)
    (hAsg : ∀ a m Q X, nvAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, nvIngestClSpec a m Q X → Func.wp Γ Full.full_ingest_cl_body a m Q X := by
  rintro ⟨h, cend, ⟨⟩⟩ m Q X
    ⟨c, s, cnf_ptr, R, rfl, rfl, hcfit, hmv1, hnc1, hlen, hcv1, hdcur, halen0, hwlen1,
      hte0, hpr0, hcl0, hunass1, hunfl0, hoom0, hv0, hmrk0, hfl0, hwsz0, hwlay, hext0, hm, hQ⟩
  have hco := hlen.core_ok
  have hmx1 : 1 ≤ c.max_vars := by have := hco.cur_vars_le; omega
  have hmrk_l : 0 < s.core.mrk.length := by rw [hco.mrk_len]; omega
  have htmp_l : 0 < s.core.tmp.length := by rw [hco.tmp_len_arr]; omega
  have hvl_l : 0 < s.core.vals.length := by rw [hco.vals_len]; omega
  have hvl1 : 1 < (s.core.vals.set 0 1#8).length := by rw [List.length_set, hco.vals_len]; omega
  have hmrk0_get : s.core.mrk[0]'hmrk_l = 0#8 := by
    rw [List.getElem?_eq_getElem hmrk_l] at hmrk0; exact Option.some.inj hmrk0
  have hv0_get : s.core.vals[0]'hvl_l = 0#8 := by
    rw [List.getElem?_eq_getElem hvl_l] at hv0; exact Option.some.inj hv0
  unfold Func.wp Full.full_ingest_cl_body
  c0_hsteps_nogrp
  -- Loop 1: `while (true)` reading `+1` then `0`
  refine wp_while_break_state
    (α := BitVec 32 × Bool × FullState)
    (β := BitVec 32 × Bool × Bool × FullState)
    (fun p => (p.1, p.2.1, p.2.2.1, ()))
    (fun p mb =>
      p.1 = 1#32 ∧ p.2.1 = false ∧ p.2.2.1 = false ∧
      p.2.2.2 = { s with core := { s.core with
        d_cur := cnf_ptr + 13#64, d_val := 0#64,
        mrk := s.core.mrk.set 0 1#8, tmp := s.core.tmp.set 0 0#32 } } ∧
      (bytes cnf_ptr fullNvSatBytes ⋆ FullMem c p.2.2.2 ⋆ R) mb)
    (fun p => (p.1, p.2.1, ()))
    (fun p => if p.1 = 0#32 then 2 else 1)
    (fun p ml =>
      p.2.1 = false ∧
      ((p.1 = 0#32 ∧ p.2.2 = s) ∨
       (p.1 = 1#32 ∧ p.2.2 = { s with core := { s.core with
         d_cur := cnf_ptr + 11#64, d_val := 0#64,
         mrk := s.core.mrk.set 0 1#8, tmp := s.core.tmp.set 0 0#32 } })) ∧
      (bytes cnf_ptr fullNvSatBytes ⋆ FullMem c p.2.2 ⋆ R) ml)
    (fun _ ⟨tlen, taut, err, s1⟩ mb ⟨htlen, htaut, herr, hs1, hmb⟩ => ?_)
    (fun B L ⟨tlen, taut, sl⟩ ml hB hL ⟨htaut, hst, hml⟩ => ?_)
    (fun _ _ _ hL => by
      c0_hsteps; exact hL (0#32, false, s) m ⟨rfl, Or.inl ⟨rfl, rfl⟩, hm⟩)
  · -- After break: `tlen = 1, taut = false, err = false`
    dsimp only at htlen htaut herr hs1 hmb ⊢
    subst htlen htaut herr hs1
    let s1 : FullState := { s with core := { s.core with
      d_cur := cnf_ptr + 13#64, d_val := 0#64,
      mrk := s.core.mrk.set 0 1#8, tmp := s.core.tmp.set 0 0#32 } }
    have hml1 : (FullMem c s1 ⋆ (bytes cnf_ptr fullNvSatBytes ⋆ R)) mb := sep_ac hmb
    -- Clear loop `while (k < 1)`
    c0_hsteps_nogrp
    refine wp_while_state
      (fun (p : BitVec 32 × FullState) => (p.1, ()))
      (fun p => 1 - p.1.toNat)
      (fun p mk =>
        p.1.toNat ≤ 1 ∧
        ((p.1 = 0#32 ∧ p.2 = s1) ∨
         (p.1 = 1#32 ∧ p.2 = { s1 with core := { s1.core with mrk := s.core.mrk } })) ∧
        (FullMem c p.2 ⋆ (bytes cnf_ptr fullNvSatBytes ⋆ R)) mk)
      (fun _ hJk => by
        c0_hsteps; exact hJk (0#32, s1) mb ⟨Nat.zero_le _, Or.inl ⟨rfl, rfl⟩, hml1⟩)
      (fun _ ⟨kv, sk⟩ mk ⟨hkle, hsk, hmk⟩ ihk => ?_)
    dsimp only at hkle hsk hmk ihk ⊢
    c0_hsplit
    · rcases hsk with ⟨rfl, rfl⟩ | ⟨rfl, _⟩
      · have htmp1_l : 0 < s1.core.tmp.length := by simp [s1, hco.tmp_len_arr]; omega
        have hmrk1_l : 0 < s1.core.mrk.length := by simp [s1, hco.mrk_len]; omega
        have htmp1_0 : s1.core.tmp[0]'htmp1_l = 0#32 := by simp [s1]
        have hmrk_rest : (s.core.mrk.set 0 1#8).set 0 0#8 = s.core.mrk := by
          rw [List.set_set, show (0#8 : BitVec 8) = s.core.mrk[0]'hmrk_l from hmrk0_get.symm,
            List.set_getElem_self]
        c0_hsteps
        · have hm_cl : (FullMem c { s1 with core := { s1.core with mrk := s.core.mrk } } ⋆
              (bytes cnf_ptr fullNvSatBytes ⋆ R)) m := by
            simpa [s1, htmp1_0, hmrk_rest] using hm
          exact ihk (1#32, _) m (by simp) ⟨Nat.le_refl _, Or.inr ⟨rfl, rfl⟩, hm_cl⟩
        · exfalso; simp [s1, htmp1_0, hmv1] at hc
      · exfalso; revert hc; decide
    · rcases hsk with ⟨rfl, _⟩ | ⟨rfl, rfl⟩
      · exfalso; revert hc; decide
      let s2 : FullState := { s1 with core := { s1.core with mrk := s.core.mrk } }
      -- Filter loop `while (i < 1)`
      c0_hsteps_nogrp
      refine wp_while_state
        (fun (p : BitVec 32 × BitVec 32 × FullState) => (p.1, p.2.1, ()))
        (fun p => 1 - p.2.1.toNat)
        (fun p mi =>
          ((p.1 = 0#32 ∧ p.2.1 = 0#32 ∧ p.2.2 = s2) ∨
           (p.1 = 1#32 ∧ p.2.1 = 1#32 ∧ p.2.2 = s2)) ∧
          (FullMem c p.2.2 ⋆ (bytes cnf_ptr fullNvSatBytes ⋆ R)) mi)
        (fun _ hLf => by
          c0_hsteps; exact hLf (0#32, 0#32, s2) mk ⟨Or.inl ⟨rfl, rfl, rfl⟩, hmk⟩)
        (fun _ ⟨keep, iv, sf⟩ mi ⟨hsf, hmi⟩ hLf => ?_)
      dsimp only at hsf hmi hLf ⊢
      c0_hsplit
      · rcases hsf with ⟨rfl, rfl, hsf_eq⟩ | ⟨rfl, rfl, _⟩
        · subst sf
          have htmp2_l : 0 < s2.core.tmp.length := by simp [s2, s1, hco.tmp_len_arr]; omega
          have htmp2_0 : s2.core.tmp[0]'htmp2_l = 0#32 := by simp [s2, s1]
          have htmp2_0' : s2.core.tmp[(BitVec.ofNat 64 0).toNat]'htmp2_l = 0#32 := htmp2_0
          have hvl2_l : 0 < s2.core.vals.length := by simp [s2, s1, hco.vals_len]; omega
          have hv2_0 : s2.core.vals[0 % 2 ^ 32]'hvl2_l = 0#8 := hv0_get
          c0_hsteps_nogrp
          rw [htmp2_0']
          c0_hsteps_nogrp
          · exfalso; simp [hv2_0] at hc; revert hc; decide
          refine wp_join_group (ts := [i32]) (fun (kp, ()) m_k =>
            kp = 1#32 ∧ (FullMem c s2 ⋆ (bytes cnf_ptr fullNvSatBytes ⋆ R)) m_k)
            (fun _ ⟨kp, ⟨⟩⟩ m_k hmk => by
              dsimp only at hmk; obtain ⟨rfl, hm_k⟩ := hmk
              simp only [Blocks.get_here]; c0_hsteps
              exact hLf (1#32, 1#32, s2) m_k (by simp) ⟨Or.inr ⟨rfl, rfl, rfl⟩, hm_k⟩)
            (fun _ hJk => by
              c0_hsteps
              · refine hJk (1#32, ()) _ ⟨rfl, ?_⟩
                have hts : (s.core.tmp.set 0 0#32).set 0 0#32 = s.core.tmp.set 0 0#32 := by
                  rw [List.set_set]
                simpa [s2, s1, hts] using hm
              · exfalso; simp [hv2_0] at hc)
        · exfalso; revert hc; decide
      · rcases hsf with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, hsf_eq⟩
        · exfalso; revert hc; decide
        subst sf
        have htmp2_l : 0 < s2.core.tmp.length := by simp [s2, s1, hco.tmp_len_arr]; omega
        have htmp2_0' : s2.core.tmp[(BitVec.ofNat 64 0).toNat]'htmp2_l = 0#32 := by simp [s2, s1]
        have hlen2 : s2.LengthsOk c :=
          ⟨{ hco with tmp_len_arr := by simp [s2, s1, hco.tmp_len_arr] }, hlen.scratch_ok⟩
        c0_hsteps
        rw [htmp2_0']
        c0_call hAsg
        refine ⟨c, s2, bytes cnf_ptr fullNvSatBytes ⋆ R, rfl, rfl, rfl, hlen2,
          by dsimp only [s2, s1]; omega, hte0,
          hv0, hfl0, hunass1, hmi, fun fl' ph' m' hfl' hph' hm' => ?_⟩
        c0_hsteps
        let s3 : FullState :=
          { s2 with
            core := { s2.core with
              vals := (s2.core.vals.set 0 1#8).set 1 0xFF#8,
              flags := fl', lvl := s2.core.lvl.set 0 0#32,
              rsns := s2.core.rsns.set 0 0xFFFFFFFF#32,
              trl := s2.core.trl.set 0 0#32, trail_pos := s2.core.trail_pos.set 0 0#32,
              trail_end := 1, unassigned := 0#64, unflushed := s2.core.unflushed + 1#64 },
            scratch := { s2.scratch with phases := ph' } }
        have htrl_l : 0 < s.core.trl.length := by rw [hco.trl_len]; omega
        have hlen3 : s3.LengthsOk c :=
          ⟨{ hlen2.core_ok with
              vals_len := by simp [s3, s2, s1, hco.vals_len],
              flags_len := hfl', lvl_len := by simp [s3, s2, s1, hco.lvl_len],
              rsns_len := by simp [s3, s2, s1, hco.rsns_len],
              trl_len := by simp [s3, s2, s1, hco.trl_len],
              trail_pos_len := by simp [s3, s2, s1, hco.trail_pos_len],
              trail_end_le := by simp [s3, s2, s1, hcv1],
              propagated_le := by simp [s3, s2, s1, hpr0] },
           { hlen.scratch_ok with phases_len := hph' }⟩
        have hnv3 : NvSatState c s3 0 1 1#64 :=
          ⟨hlen3, hmv1, hcv1, halen0, hwlen1, rfl, hpr0, hcl0, rfl,
           by simp [s3, s2, s1, hunfl0], hoom0,
           by simp [s3, s2, s1, List.getElem?_set_self hvl_l],
           by simp [s3, s2, s1, List.getElem?_set_self hvl1],
           fun _ => by simp [s3, s2, s1, List.getElem?_set_self htrl_l],
           hwsz0, hwlay.with_wstk rfl rfl rfl rfl, hext0⟩
        exact hQ s3 m' hnv3 rfl rfl (sep_ac hm')
  · -- Body of `while (true)`
    dsimp only at htaut hst hml ⊢
    subst htaut
    rcases hst with ⟨rfl, hsl⟩ | ⟨rfl, hsl⟩
    · -- Iter 1: `i0 = 9`, `nextLitPure` returns `.lit 0` (`j = 11`)
      subst sl
      have hml_d : (bytes cnf_ptr fullNvSatBytes ⋆
          dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
            (cnf_ptr + 9#64) s.core.d_val ⋆
          (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
            FullScratchArrays c s.scratch ⋆ c.pad ⋆ R)) ml := by
        rw [← hdcur]; unfold FullMem at hml; exact sep_ac hml
      c0_hsteps_nogrp
      · c0_call hNext
        refine ⟨cnf_ptr, BitVec.ofNat 64 c.nc, s.core.d_val, c.mv, fullNvSatBytes, 9,
          array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
            FullScratchArrays c s.scratch ⋆ c.pad ⋆ R,
          rfl, hcfit, by omega, by decide, hml_d, ?_⟩
        rw [hmv1, fullNvSat_nextLit_9]
        intro j m1 _ _ _ hj hdrop hm1
        have hj11 : j = 11 :=
          fullNvSat_drop_eq_iff (by change j ≤ 14 at hj; exact hj) (by decide) hdrop
        subst hj11
        have hm1_f : (FullMem c { s with core := { s.core with
            d_cur := cnf_ptr + 11#64, d_val := 0#64 } } ⋆
            (bytes cnf_ptr fullNvSatBytes ⋆ R)) m1 := by
          unfold FullMem
          have hht : Full.hdrTailWords c { s with core := { s.core with
              d_cur := cnf_ptr + 11#64, d_val := 0#64 } } = Full.hdrTailWords c s := rfl
          rw [hht, hmv1]; exact sep_ac hm1
        clear hm hml hml_d hm1
        c0_hsteps
        · exfalso; simp [hmv1] at hc
        · exfalso; simp [hmv1] at hc
        · have hm_upd : (bytes cnf_ptr fullNvSatBytes ⋆
              FullMem c { s with core := { s.core with
                d_cur := cnf_ptr + 11#64, d_val := 0#64,
                mrk := s.core.mrk.set 0 1#8, tmp := s.core.tmp.set 0 0#32 } } ⋆ R) m := by
            have hm' : (FullMem c { s with core := { s.core with
                d_cur := cnf_ptr + 11#64, d_val := 0#64,
                mrk := s.core.mrk.set 0 1#8, tmp := s.core.tmp.set 0 0#32 } } ⋆
                (bytes cnf_ptr fullNvSatBytes ⋆ R)) m := by
              simpa using hm
            exact sep_ac hm'
          exact hL (1#32, false, { s with core := { s.core with
            d_cur := cnf_ptr + 11#64, d_val := 0#64,
            mrk := s.core.mrk.set 0 1#8, tmp := s.core.tmp.set 0 0#32 } }) m (by simp)
            ⟨rfl, Or.inr ⟨rfl, rfl⟩, hm_upd⟩
        · exfalso; simp_all
        · exfalso; simp_all
      · exfalso; cases hc
    · -- Iter 2: `i0 = 11`, `nextLitPure` returns `.endClause` (`j = 13`) -> break
      subst sl
      let s_b : FullState := { s with core := { s.core with
        d_cur := cnf_ptr + 11#64, d_val := 0#64,
        mrk := s.core.mrk.set 0 1#8, tmp := s.core.tmp.set 0 0#32 } }
      have hml_d : (bytes cnf_ptr fullNvSatBytes ⋆
          dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
            (cnf_ptr + 11#64) 0#64 ⋆
          (array64 (c.hdr + 32) (Full.hdrTailWords c s_b) ⋆ FullCoreArrays c s_b.core ⋆
            FullScratchArrays c s_b.scratch ⋆ c.pad ⋆ R)) ml := by
        unfold FullMem at hml; exact sep_ac hml
      c0_hsteps_nogrp
      · c0_call hNext
        refine ⟨cnf_ptr, BitVec.ofNat 64 c.nc, 0#64, c.mv, fullNvSatBytes, 11,
          array64 (c.hdr + 32) (Full.hdrTailWords c s_b) ⋆ FullCoreArrays c s_b.core ⋆
            FullScratchArrays c s_b.scratch ⋆ c.pad ⋆ R,
          rfl, hcfit, by omega, by decide, hml_d, ?_⟩
        rw [hmv1, fullNvSat_nextLit_11]
        intro j m1 _ hj hdrop hm1
        have hj13 : j = 13 :=
          fullNvSat_drop_eq_iff (by change j ≤ 14 at hj; exact hj) (by decide) hdrop
        subst hj13
        c0_hsteps
        let s_c : FullState := { s with core := { s.core with
          d_cur := cnf_ptr + 13#64, d_val := 0#64,
          mrk := s.core.mrk.set 0 1#8, tmp := s.core.tmp.set 0 0#32 } }
        have hm1_c : (bytes cnf_ptr fullNvSatBytes ⋆ FullMem c s_c ⋆ R) m1 := by
          unfold FullMem
          have hht : Full.hdrTailWords c s_c = Full.hdrTailWords c s_b := rfl
          rw [hht, hmv1]; exact sep_ac hm1
        exact hB (1#32, false, false, s_c) m1 ⟨rfl, rfl, rfl, rfl, hm1_c⟩
      · exfalso; cases hc

private theorem nv_parse_body_wp (Γ : Env)
    (hIng : ∀ a m Q X, nvIngestClSpec a m Q X →
      Γ "full_ingest_cl" [i64, i64] [i64] a m Q X)
    (hSkip : ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, nvParseBodySpec a m Q X → Func.wp Γ Full.full_parse_body_body a m Q X := by
  rintro ⟨h, cend, ⟨⟩⟩ m Q X
    ⟨c, s, cnf_ptr, R, rfl, rfl, hcfit, hmv1, hnc1, hlen, hcv1, hdcur, halen0, hwlen1,
      hte0, hpr0, hcl0, hunass1, hunfl0, hoom0, hv0, hmrk0, hfl0, hwsz0, hwlay, hext0, hm, hQ⟩
  unfold Func.wp Full.full_parse_body_body
  c0_hsteps_nogrp
  refine wp_while_state
    (fun (p : Bool × Bool × BitVec 64 × FullState) => (p.1, p.2.1, p.2.2.1, ()))
    (fun p => 1 - p.2.2.1.toNat)
    (fun p ml =>
      p.1 = false ∧ p.2.1 = false ∧
      ((p.2.2.1 = 0#64 ∧ p.2.2.2 = s) ∨
       (p.2.2.1 = 1#64 ∧ NvSatState c p.2.2.2 0 1 1#64 ∧
         p.2.2.2.core.d_cur = cnf_ptr + 13#64 ∧ p.2.2.2.core.fuel = s.core.fuel)) ∧
      (bytes cnf_ptr fullNvSatBytes ⋆ FullMem c p.2.2.2 ⋆ R) ml)
    (fun _ hJ => by
      c0_hsteps; exact hJ (false, false, 0#64, s) m ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩, hm⟩)
    (fun _ ⟨us, oom, iv, st⟩ ml ⟨hus, hoom, hst, hml⟩ ih => ?_)
  dsimp only at hus hoom hst hml ih ⊢
  subst hus hoom
  have hml_f : (FullMem c st ⋆ (bytes cnf_ptr fullNvSatBytes ⋆ R)) ml := sep_ac hml
  c0_hsplit
  · rcases hst with ⟨rfl, hsl⟩ | ⟨rfl, _⟩
    · subst st
      c0_hsteps; c0_call hIng
      refine ⟨c, s, cnf_ptr, R, rfl, rfl, hcfit, hmv1, hnc1, hlen, hcv1, hdcur, halen0,
        hwlen1, hte0, hpr0, hcl0, hunass1, hunfl0, hoom0, hv0, hmrk0, hfl0, hwsz0, hwlay,
        hext0, hml, fun s1 m1 hnv1 hd1 hfu1 hm1 => ?_⟩
      c0_hsteps
      exact ih (false, false, 1#64, s1) m1 (by simp)
        ⟨rfl, rfl, Or.inr ⟨rfl, hnv1, hd1, hfu1⟩, hm1⟩
    · exfalso; simp [hnc1] at hc
  · rcases hst with ⟨rfl, _⟩ | ⟨rfl, hnv1, hd1, hfu1⟩
    · exfalso; simp [hnc1] at hc
    c0_hsteps; c0_call hSkip
    refine ⟨cnf_ptr, fullNvSatBytes, 13, FullMem c st ⋆ R, hd1, rfl, hcfit, by decide,
      by simpa [sep_assoc] using hml, fun j _ hj hdrop => ?_⟩
    rw [fullNvSat_skip_13] at hdrop
    have hj_le : j ≤ 14 := hj
    have hj14 : j = 14 := by
      have hlen_d := congrArg List.length hdrop
      simp only [List.length_drop, List.length_nil, show fullNvSatBytes.length = 14 from rfl]
        at hlen_d
      omega
    subst hj14
    c0_hsteps
    let st' : FullState := { st with core := { st.core with d_cur := cnf_ptr + 14#64 } }
    have hnv' : NvSatState c st' 0 1 1#64 :=
      ⟨⟨{ hnv1.len.core_ok with }, hnv1.len.scratch_ok⟩, hnv1.mv1, hnv1.cv1, hnv1.alen0,
       hnv1.wlen1, hnv1.te_eq, hnv1.prop_eq, hnv1.cl0, hnv1.unass0, hnv1.unfl_eq, hnv1.oom0,
       hnv1.v0, hnv1.v1, hnv1.trl0, hnv1.wsz0, hnv1.wlay.with_wstk rfl rfl rfl rfl, hnv1.ext0⟩
    exact hQ st' m hnv' hfu1 (sep_ac hm)

private theorem nv_prop_lit_raw_wp (Γ : Env) :
    ∀ a m Q X, nvPropLitRawSpec a m Q X → Func.wp Γ FullM4Bcp.full_prop_lit_m4_body a m Q X := by
  rintro ⟨h, lit, ignore_ref, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, rfl, hlen, hcv1, hsz1, hm, hQ⟩
  have hco := hlen.core_ok
  have hmx1 : 1 ≤ c.max_vars := by have := hco.cur_vars_le; omega
  have hvl : 1 < s.core.vals.length := by rw [hco.vals_len]; omega
  have hwv2 : 2 < s.core.wvec.length := by rw [hco.wvec_len]; omega
  have hwv3 : 3 < s.core.wvec.length := by rw [hco.wvec_len]; omega
  have hwv3_0 : s.core.wvec[3]'hwv3 = 0#32 := by
    unfold fullWatchSize fullWatchSizeCore at hsz1
    rw [List.getElem?_eq_getElem hwv3, Option.getD_some] at hsz1
    exact BitVec.eq_of_toNat_eq hsz1
  unfold Func.wp FullM4Bcp.full_prop_lit_m4_body
  c0_hsteps
  · exact hQ
  · exact hQ
  · exact hQ
  · exfalso; simp [hwv3_0] at hc

private theorem nv_propagate_ignore_wp (Γ : Env)
    (hRaw : ∀ a m Q X, nvPropLitRawSpec a m Q X →
      Γ "full_prop_lit_raw" [i64, i32, i64] [.bool] a m Q X) :
    ∀ a m Q X, nvPropagateIgnoreSpec a m Q X →
      Func.wp Γ FullM5Otfs.full_propagate_ignore_body a m Q X := by
  rintro ⟨h, ignore_ref, ⟨⟩⟩ m Q X ⟨c, s, prop, unfl, R, rfl, hnv, hple, hfu1, hm, hQ⟩
  have hco := hnv.len.core_ok
  have hmx1 : 1 ≤ c.max_vars := by have := hco.cur_vars_le; have := hnv.cv1; omega
  unfold Func.wp FullM5Otfs.full_propagate_ignore_body
  c0_hsteps_nogrp
  · have hp1 : prop = 1 := by
      have h1 : s.core.trail_end % 2 ^ 64 ≤ s.core.propagated % 2 ^ 64 := by assumption
      rw [hnv.te_eq, hnv.prop_eq] at h1; omega
    subst hp1
    exact hQ s m hnv (fun _ => rfl) (fun h => by cases h) hm
  · exfalso; exact hc hnv.oom0
  have hp0 : prop = 0 := by
    have h1 : ¬ (s.core.trail_end % 2 ^ 64 ≤ s.core.propagated % 2 ^ 64) := by assumption
    rw [hnv.te_eq, hnv.prop_eq] at h1; omega
  subst hp0
  have htrl0_l : 0 < s.core.trl.length := by rw [hco.trl_len]; omega
  have htrl0 : s.core.trl[0]'htrl0_l = 0#32 := by
    have h0 := hnv.trl0 rfl
    rw [List.getElem?_eq_getElem htrl0_l] at h0; exact Option.some.inj h0
  refine wp_while_state
    (fun (p : BitVec 64 × BitVec 64 × FullState) => (p.1, p.2.1, ()))
    (fun p => 1 - p.1.toNat)
    (fun p ml =>
      ((p.1 = 0#64 ∧ p.2.1 = s.core.fuel ∧ p.2.2 = s) ∨
       (p.1 = 1#64 ∧ p.2.1 = s.core.fuel - 1#64 ∧
         p.2.2 = { s with core := { s.core with propagated := 1 } })) ∧
      (FullMem c p.2.2 ⋆ R) ml)
    (fun _ hJ => by
      c0_hsteps
      rw [hnv.prop_eq]
      exact hJ (0#64, s.core.fuel, s) m ⟨Or.inl ⟨rfl, rfl, rfl⟩, hm⟩)
    (fun _ ⟨pv, fv, st⟩ ml ⟨hst, hml⟩ ih => ?_)
  dsimp only at hst hml ih ⊢
  c0_hsplit
  · rcases hst with ⟨rfl, rfl, hst_eq⟩ | ⟨rfl, _, hst_eq⟩
    · subst st
      c0_hsteps_nogrp
      let s1 : FullState := { s with core := { s.core with propagated := 1 } }
      have hlen1 : s1.LengthsOk c :=
        ⟨{ hco with propagated_le := by simp [s1, hnv.te_eq] }, hnv.len.scratch_ok⟩
      refine wp_join_group (ts := [.bool])
        (fun (ok, ()) m1 => ok = true ∧ m1 = m)
        (fun _ ⟨ok, ⟨⟩⟩ m1 hokm => by
          dsimp only at hokm; obtain ⟨rfl, hm1⟩ := hokm; subst m1
          simp only [Blocks.get_here]; c0_hsteps
          all_goals first
            | contradiction
            | exact ih (1#64, s.core.fuel - 1#64, s1) m (by simp)
                ⟨Or.inr ⟨rfl, rfl, rfl⟩, by simpa [s1] using hm⟩)
        (fun _ hJok => by
          c0_hsteps_nogrp
          refine wp_join_state0 (α := Unit) (fun _ m' => m' = m)
            (fun _ _ m' hm' => by
              subst m'; simp only [Blocks.get_here]; c0_hsteps_nogrp
              have htrl0' : s.core.trl[(0#64 : BitVec 64).toNat]'htrl0_l = 0#32 := htrl0
              rw [htrl0']; c0_call hRaw
              refine ⟨c, s1, R, rfl, rfl, hlen1, hnv.cv1, hnv.wsz0 1 (by decide),
                by simpa [s1] using hm, ?_⟩
              c0_hsteps; exact hJok (true, ()) m ⟨rfl, rfl⟩)
            (fun _ hJe => by
              c0_hsteps_nogrp <;>
                first | exact hJe () m rfl | (exfalso; simp_all [hnv.cl0])))
    · exfalso; subst st; have hte := hnv.te_eq; simp_all
  · rcases hst with ⟨rfl, _, hst_eq⟩ | ⟨rfl, rfl, hst_eq⟩
    · exfalso; subst st; have hte := hnv.te_eq; simp_all
    subst st
    c0_hsteps
    let s2 : FullState := { s with core := { s.core with
      propagated := 1, fuel := s.core.fuel - 1#64 } }
    have hlen2 : s2.LengthsOk c :=
      ⟨{ hco with propagated_le := by simp [s2, hnv.te_eq] }, hnv.len.scratch_ok⟩
    have hnv2 : NvSatState c s2 1 1 unfl :=
      ⟨hlen2, hnv.mv1, hnv.cv1, hnv.alen0, hnv.wlen1, hnv.te_eq, rfl, hnv.cl0, hnv.unass0,
       hnv.unfl_eq, hnv.oom0, hnv.v0, hnv.v1, hnv.trl0, hnv.wsz0,
       hnv.wlay.with_wstk rfl rfl rfl rfl, hnv.ext0⟩
    exact hQ s2 m hnv2 (fun h => by cases h) (fun _ => rfl) hm

private theorem nv_propagate_wp (Γ : Env)
    (hIgn : ∀ a m Q X, nvPropagateIgnoreSpec a m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, nvPropagateSpec a m Q X → Func.wp Γ FastCore.full_propagate_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, prop, unfl, R, rfl, hnv, hple, hfu1, hm, hQ⟩
  unfold Func.wp FastCore.full_propagate_body
  c0_hsteps; c0_call hIgn
  exact ⟨c, s, prop, unfl, R, rfl, hnv, hple, hfu1, hm, hQ⟩

private theorem nv_sweep_bins_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X) :
    ∀ a m Q X, nvSweepBinsSpec a m Q X →
      Func.wp Γ FullFastSched.full_sweep_bins_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hnv, hm, hQ⟩
  have hco := hnv.len.core_ok
  have hmx1 : 1 ≤ c.max_vars := by have := hco.cur_vars_le; have := hnv.cv1; omega
  unfold Func.wp FullFastSched.full_sweep_bins_body
  c0_hsteps_nogrp
  refine wp_while_state
    (fun (lv : BitVec 64) => (lv, ()))
    (fun lv => 2 - lv.toNat)
    (fun lv ml => lv.toNat ≤ 2 ∧ ml = m)
    (fun _ hJ => by c0_hsteps; exact hJ 0#64 m ⟨Nat.zero_le _, rfl⟩)
    (fun _ lv ml ⟨hlv, hml_eq⟩ ih => ?_)
  dsimp only at hlv hml_eq ih ⊢
  subst ml
  c0_hsplit
  · have hlt : lv.toNat < 2 := by
      have h1 := hc; simp only [bv_c0, hnv.cv1] at h1; omega
    have hlv1 : (lv + 1#64).toNat = lv.toNat + 1 := by simp only [bv_c0]; omega
    have hwv0 : (lv <<< (1 : Nat)).toNat < s.core.wvec.length := by
      rw [hco.wvec_len, BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
    have hwv1 : ((lv <<< (1 : Nat)) + 1#64).toNat < s.core.wvec.length := by
      rw [hco.wvec_len, BitVec.toNat_add, BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
    have hsz0_lv : s.core.wvec[(lv.toNat * 2 + 1) % 2 ^ 64]'(by rw [hco.wvec_len]; omega) =
        0#32 := by
      have hz := hnv.wsz0 lv.toNat hlt
      unfold fullWatchSize fullWatchSizeCore at hz
      rw [List.getElem?_eq_getElem (by rw [hco.wvec_len]; omega), Option.getD_some] at hz
      have hidx : (lv.toNat * 2 + 1) % 2 ^ 64 = 2 * lv.toNat + 1 := by omega
      apply BitVec.eq_of_toNat_eq; simpa [hidx] using hz
    c0_hsteps
    · exact ih (lv + 1#64) m (by rw [hlv1]; omega) ⟨by rw [hlv1]; omega, rfl⟩
    · exfalso; simp [hsz0_lv] at hc
  · c0_hsteps; c0_call hDefrag
    refine ⟨c, s, R, rfl, hnv.len, hnv.wlay, hm,
      fun wvec' wstk' wlen' wsort' m' hlen' hwlay' hwlen1' hwsz' hm' => ?_⟩
    let s' : FullState :=
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 },
        scratch := { s.scratch with wsort := wsort' } }
    have hnv' : NvSatState c s' 1 1 1#64 :=
      ⟨hlen', hnv.mv1, hnv.cv1, hnv.alen0, hwlen1' hnv.wlen1, hnv.te_eq, hnv.prop_eq, hnv.cl0,
       hnv.unass0, hnv.unfl_eq, hnv.oom0, hnv.v0, hnv.v1, hnv.trl0,
       fun l hl => (hwsz' l (by rw [hnv.cv1]; omega)).1.trans (hnv.wsz0 l hl),
       hwlay', hnv.ext0⟩
    c0_hsteps; exact hQ s' m' hnv' rfl hm'

private theorem nv_rewatch_arena_wp (Γ : Env) :
    ∀ a m Q X, nvRewatchArenaSpec a m Q X → Func.wp Γ Full.full_rewatch_arena_body a m Q X := by
  rintro ⟨h, dst, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, rfl, _, hm, hQ⟩
  unfold Func.wp Full.full_rewatch_arena_body
  c0_hsteps_nogrp
  refine wp_while_state
    (fun (pv : BitVec 64) => (pv, ())) (fun _ => 0)
    (fun pv ml => pv = 0#64 ∧ ml = m)
    (fun _ hJ => by c0_hsteps; exact hJ 0#64 m ⟨rfl, rfl⟩)
    (fun _ pv ml ⟨rfl, hml_eq⟩ _ => by
      subst hml_eq
      c0_hsplit
      · exfalso; simp at hc
      · c0_hsteps; exact hQ)

private theorem nv_arena_sweep_wp (Γ : Env)
    (hBins : ∀ a m Q X, nvSweepBinsSpec a m Q X → Γ "full_sweep_bins" [i64] [] a m Q X)
    (hRew : ∀ a m Q X, nvRewatchArenaSpec a m Q X →
      Γ "full_rewatch_arena" [i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, nvArenaSweepSpec a m Q X → Func.wp Γ Full.full_arena_sweep_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hnv, hm, hQ⟩
  unfold Func.wp Full.full_arena_sweep_body
  c0_hsteps; c0_call hBins
  refine ⟨c, s, R, rfl, hnv, hm, fun s1 m1 hnv1 hfu1 hm1 => ?_⟩
  c0_hsteps_nogrp
  refine wp_while_break_state
    (α := BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × Bool)
    (β := BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × Bool × Bool)
    (fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2, ()))
    (fun p mb => p = (0#64, 0#64, 0xFFFFFFFF#64, 0#64, 0#64, false, false) ∧ mb = m1)
    (fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2, ()))
    (fun _ => 0)
    (fun p ml => p = (0#64, 0#64, 0xFFFFFFFF#64, 0#64, 0#64, false) ∧ ml = m1)
    (fun _ p mb ⟨hp, hmb_eq⟩ => by
      subst hp; subst mb
      c0_hsteps_nogrp
      let s2 : FullState := { s1 with core := { s1.core with
        arena_len := 0, arena_garbage := 0#64, first_reducible := 0xFFFFFFFF#64,
        num_irred := 0#64, num_redundant := 0#64 } }
      refine wp_while_state
        (fun (q : BitVec 64 × List (BitVec 32)) => (q.1, ()))
        (fun q => 16 - q.1.toNat)
        (fun q mll => q.1.toNat ≤ 16 ∧ q.2.length = 16 ∧
          (FullMem c { s2 with scratch := { s2.scratch with last_learned := q.2 } } ⋆ R) mll)
        (fun _ hJl => by
          c0_hsteps
          exact hJl (0#64, s2.scratch.last_learned) m
            ⟨Nat.zero_le _, hnv1.len.scratch_ok.last_learned_len, hm⟩)
        (fun _ ⟨li, ll⟩ mll ⟨hli, hll, hmll⟩ ihl => ?_)
      dsimp only at hli hll hmll ihl ⊢
      c0_hsplit
      · have hli_lt : li.toNat < 16 := by c0_bound
        have hli1 : (li + 1#64).toNat = li.toNat + 1 := by simp only [bv_c0]; omega
        have hli_ll : li.toNat < ll.length := by omega
        c0_hsteps
        exact ihl (li + 1#64, ll.set li.toNat 0xFFFFFFFF#32) _ (by rw [hli1]; omega)
          ⟨by rw [hli1]; omega, by simp [hll], by assumption⟩
      · let s3 : FullState := { s2 with scratch := { s2.scratch with last_learned := ll } }
        have hlen3 : s3.LengthsOk c :=
          ⟨{ hnv1.len.core_ok with arena_len_le := by simp [s3, s2] },
           { hnv1.len.scratch_ok with last_learned_len := hll }⟩
        c0_hsteps
        · exfalso; exact hc hnv1.oom0
        c0_call hRew
        refine ⟨c, s3, R, rfl, rfl, hlen3, hmll, ?_⟩
        c0_hsteps
        · have hnv3 : NvSatState c s3 1 1 1#64 :=
            ⟨hlen3, hnv1.mv1, hnv1.cv1, rfl, hnv1.wlen1, hnv1.te_eq, hnv1.prop_eq, hnv1.cl0,
             hnv1.unass0, hnv1.unfl_eq, hnv1.oom0, hnv1.v0, hnv1.v1, hnv1.trl0, hnv1.wsz0,
             hnv1.wlay.with_wstk rfl rfl rfl rfl, hnv1.ext0⟩
          exact hQ s3 mll hnv3 hfu1 hmll
        · exfalso; cases hc)
    (fun _ _ p ml hB _ ⟨hp, hml_eq⟩ => by
      subst hp; subst ml
      c0_hsplit
      · exfalso; simp [hnv1.alen0] at hc
      · c0_hsteps; exact hB (0#64, 0#64, 0xFFFFFFFF#64, 0#64, 0#64, false, false) m1 ⟨rfl, rfl⟩)
    (fun _ _ _ hL => by c0_hsteps; exact hL _ m1 ⟨rfl, rfl⟩)

private theorem nv_extend_wp (Γ : Env) :
    ∀ a m Q X, nvExtendSpec a m Q X → Func.wp Γ FullM4.full_extend_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hmx1, hv0, hext0, hm, hQ⟩
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  unfold Func.wp FullM4.full_extend_body
  c0_hsteps_nogrp
  refine wp_while_state
    (fun (p : BitVec 64 × List (BitVec 8)) => (p.1, ()))
    (fun p => c.max_vars - p.1.toNat)
    (fun p ml => p.1.toNat ≤ c.max_vars ∧ p.2.length = 2 * c.max_vars ∧
      p.2[0]? = some 1#8 ∧
      (FullMem c { s with core := { s.core with vals := p.2 } } ⋆ R) ml)
    (fun _ hJ => by
      c0_hsteps; exact hJ (0#64, s.core.vals) m ⟨Nat.zero_le _, hlen.core_ok.vals_len, hv0, hm⟩)
    (fun _ ⟨v, vs⟩ ml ⟨hvle, hvlen, hvs0, hml⟩ ih => ?_)
  dsimp only at hvle hvlen hvs0 hml ih ⊢
  c0_hsplit
  · have hv_lt : v.toNat < c.max_vars := by
      have h1 : v.toNat < c.max_vars % 2 ^ 64 := by assumption
      omega
    have hv1 : (v + 1#64).toNat = v.toNat + 1 := by simp only [bv_c0]; omega
    have hfl_v : v.toNat < s.core.flags.length := by rw [hlen.core_ok.flags_len]; exact hv_lt
    have hv_shl : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show 2 ^ 1 = 2 from rfl,
        Nat.mod_eq_of_lt (by omega)]; omega
    have hv_or : ((v <<< (1 : Nat)) ||| 1#64).toNat = 2 * v.toNat + 1 := by
      have h2lor : ∀ n : Nat, (2 * n) ||| 1 = 2 * n + 1 := fun n => by
        apply Nat.eq_of_testBit_eq; intro k
        rw [Nat.testBit_or]
        cases k with
        | zero => simp
        | succ k =>
          have h1 : (2 * n).testBit (k + 1) = n.testBit k := by
            simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.pow_succ',
              ← Nat.div_div_eq_div_mul, show (2 * n) / 2 = n by omega]
          have h2 : (2 * n + 1).testBit (k + 1) = n.testBit k := by
            simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.pow_succ',
              ← Nat.div_div_eq_div_mul, show (2 * n + 1) / 2 = n by omega]
          have h3 : (1 : Nat).testBit (k + 1) = false := by
            simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.pow_succ',
              ← Nat.div_div_eq_div_mul, show (1 : Nat) / 2 = 0 from rfl, Nat.zero_div]
            decide
          rw [h1, h2, h3, Bool.or_false]
      rw [BitVec.toNat_or, hv_shl, show (1#64 : BitVec 64).toNat = 1 from rfl, h2lor]
    have hshl_lt : (v <<< (1 : Nat)).toNat < vs.length := by omega
    have hor_lt : ((v <<< (1 : Nat)) ||| 1#64).toNat <
        (vs.set (v <<< (1 : Nat)).toNat 1#8).length := by rw [List.length_set]; omega
    have hset0 : ((vs.set (v <<< (1 : Nat)).toNat 1#8).set
        ((v <<< (1 : Nat)) ||| 1#64).toNat (BitVec.setWidth 8 (-1#32)))[0]? = some 1#8 := by
      rw [List.getElem?_set_ne (by omega)]
      by_cases hz : v.toNat = 0
      · rw [show (v <<< (1 : Nat)).toNat = 0 by omega]; exact List.getElem?_set_self (by omega)
      · rw [List.getElem?_set_ne (by omega)]; exact hvs0
    c0_hsteps_nogrp
    refine wp_join_state0 (α := List (BitVec 8))
      (fun vs' m' => vs'.length = 2 * c.max_vars ∧ vs'[0]? = some 1#8 ∧
        (FullMem c { s with core := { s.core with vals := vs' } } ⋆ R) m')
      (fun _ vs' m' ⟨hvl', hvs0', hm'⟩ => by
        c0_hsteps
        exact ih (v + 1#64, vs') m' (by rw [hv1]; omega) ⟨by rw [hv1]; omega, hvl', hvs0', hm'⟩)
      (fun _ hJ2 => by
        c0_hsteps
        · exact hJ2 _ m ⟨by simp [hvlen], hset0, hm⟩
        · exact hJ2 _ m ⟨by simp [hvlen], hset0, hm⟩
        · exact hJ2 vs ml ⟨hvlen, hvs0, hml⟩)
  · c0_hsteps_nogrp
    refine wp_while_state
      (fun (ev : BitVec 64) => (ev, ())) (fun _ => 0)
      (fun ev m2 => ev = 0#64 ∧ m2 = ml)
      (fun _ hJe => by c0_hsteps; rw [hext0]; exact hJe 0#64 ml ⟨rfl, rfl⟩)
      (fun _ ev m2 ⟨hev, hm2_eq⟩ _ => by
        subst ev; subst m2
        c0_hsplit
        · exfalso; simp at hc
        · c0_hsteps; exact hQ vs ml hvlen hvs0 hml)

private theorem nv_preprocess_m5_wp (Γ : Env)
    (hProp : ∀ a m Q X, nvPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, nvArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ a m Q X, nvPreprocessM5Spec a m Q X →
      Func.wp Γ FullM5Orch.full_preprocess_m5_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hnv, hfu2, hm, hQ⟩
  unfold Func.wp FullM5Orch.full_preprocess_m5_body
  c0_hsteps; c0_call hProp
  refine ⟨c, s, 0, 1#64, R, rfl, hnv, by decide, by omega, hm, fun s1 m1 hnv1 _ hfu1 hm1 => ?_⟩
  have hfu1_pos : 1 ≤ s1.core.fuel.toNat := by
    rw [hfu1 rfl]; have := s.core.fuel.isLt; bv_omega
  c0_hsteps_nogrp
  · exfalso; exact hc hnv1.oom0
  refine wp_join_state0 (α := FullState)
    (fun s2 m2 => NvSatState c s2 1 1 0#64 ∧ (FullMem c s2 ⋆ R) m2)
    (fun _ s2 m2 ⟨hnv2, hm2⟩ => by
      c0_hsteps
      · exact hQ s2 m2 hnv2 hm2
      · exfalso; exact hc hnv2.unass0)
    (fun _ hJu => by
      c0_hsteps_nogrp
      · c0_call hSweep
        refine ⟨c, s1, R, rfl, hnv1, hm1, fun s1a m1a hnv1a hfu1a hm1a => ?_⟩
        c0_hsteps
        c0_call hProp
        refine ⟨c, s1a, 1, 1#64, R, rfl, hnv1a, by decide, by rw [hfu1a]; omega, hm1a,
          fun s1b m1b hnv1b _ _ hm1b => ?_⟩
        c0_hsteps
        let s1c : FullState := { s1b with core := { s1b.core with unflushed := 0#64 } }
        have hnv1c : NvSatState c s1c 1 1 0#64 :=
          ⟨⟨{ hnv1b.len.core_ok with }, hnv1b.len.scratch_ok⟩, hnv1b.mv1, hnv1b.cv1,
           hnv1b.alen0, hnv1b.wlen1, hnv1b.te_eq, hnv1b.prop_eq, hnv1b.cl0, hnv1b.unass0,
           rfl, hnv1b.oom0, hnv1b.v0, hnv1b.v1, hnv1b.trl0, hnv1b.wsz0,
           hnv1b.wlay.with_wstk rfl rfl rfl rfl, hnv1b.ext0⟩
        exact hJu s1c m ⟨hnv1c, hm⟩
      · exfalso; rw [hnv1.unfl_eq] at hc; revert hc; decide)

/-! ## 6. Top-Level SAT Non-Vacuity (`kissat_solve_bytes_m5`, `m5SatNvEnv_moduleOk`, Headlines) -/

private theorem nv_merge_reg {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hw_ge : fullAlignPad work_ptr + 1152 ≤ wlen)
    (hm : (bytes cnf_ptr cnfBytes ⋆
      region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
        (wlen - fullAlignPad work_ptr) ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m) :
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m := by
  have h1 : ((region work_ptr (fullAlignPad work_ptr) ⋆
      region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
        (wlen - fullAlignPad work_ptr)) ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
  rw [region_merge_eq (a := work_ptr) (n1 := fullAlignPad work_ptr)
    (n2 := wlen - fullAlignPad work_ptr) (n := wlen) (by omega) (by omega)] at h1
  exact sep_ac h1

private theorem nv_solve_bytes_m5_wp (Γ : Env)
    (hInit : ∀ a m Q X, nvInitStateM5Spec a m Q X →
      Γ "full_init_state_m5" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hParse : ∀ a m Q X, nvParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hPre : ∀ a m Q X, nvPreprocessM5Spec a m Q X →
      Γ "full_preprocess_m5" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, nvExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullSatWitnessSpec a m Q X →
      Func.wp Γ FullM5Orch.kissat_solve_bytes_m5_body a m Q X := by
  rintro ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, ⟨⟩⟩ m Q X
    ⟨R, hcp0, hwp0, rfl, rfl, rfl, hcfit, hwfit, hm, hQ⟩
  have hpad_lt : fullAlignPad work_ptr < 8 := fullAlignPad_lt8 work_ptr
  have hw_ge : fullAlignPad work_ptr + 1152 ≤ 4096 := by omega
  have hpad_eq : ((8 : BitVec 64) - (work_ptr &&& 7)) &&& 7 =
      BitVec.ofNat 64 (fullAlignPad work_ptr) := by
    apply BitVec.eq_of_toNat_eq
    rw [show ((8 : BitVec 64) - (work_ptr &&& 7)) &&& 7 = (8#64 - (work_ptr &&& 7#64)) &&& 7#64
      from rfl, fullAlignPad_eq, bv64_ofNat_toNat (by omega)]
  have hav_eq : (4096#64 : BitVec 64) - BitVec.ofNat 64 (fullAlignPad work_ptr) =
      BitVec.ofNat 64 (4096 - fullAlignPad work_ptr) :=
    bv_sub_ofNat (a := 4096) (b := fullAlignPad work_ptr) (by omega) (by decide)
  have hav_to : (BitVec.ofNat 64 (4096 - fullAlignPad work_ptr)).toNat =
      4096 - fullAlignPad work_ptr := bv64_ofNat_toNat (by omega)
  have hnot0 : ~~~(0 : BitVec 64) = 0xFFFFFFFFFFFFFFFF#64 := rfl
  have hugt_c : (0xFFFFFFFFFFFFFFFF#64 - cnf_ptr).ult
      (BitVec.ofNat 64 fullNvSatBytes.length) = false := by
    rw [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_sub]
    have := cnf_ptr.isLt
    rw [show (0xFFFFFFFFFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 64 - 1 from rfl,
      show (BitVec.ofNat 64 fullNvSatBytes.length).toNat = fullNvSatBytes.length from rfl]; omega
  have hugt_w : (0xFFFFFFFFFFFFFFFF#64 - work_ptr).ult 4096#64 = false := by
    rw [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_sub]
    have := work_ptr.isLt
    rw [show (0xFFFFFFFFFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 64 - 1 from rfl,
      show (4096#64 : BitVec 64).toNat = 4096 from rfl]; omega
  unfold Func.wp FullM5Orch.kissat_solve_bytes_m5_body
  wp_unfold
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  refine ⟨(fun h => absurd h hcp0), fun _ => ?_⟩
  refine ⟨(fun h => absurd h hwp0), fun _ => ?_⟩
  rw [hnot0, hugt_c]; refine ⟨(fun h => by cases h), fun _ => ?_⟩
  rw [hugt_w]; refine ⟨(fun h => by cases h), fun _ => ?_⟩
  rw [hpad_eq, show (1152 : BitVec 64) = BitVec.ofNat 64 1152 from rfl, bv_add_ofNat,
    bv_ult_eq (by decide) (by omega)]
  refine ⟨(fun h => by have := of_decide_eq_true h; omega), fun _ => ?_⟩
  rw [hav_eq]
  have hm_sp : (bytes cnf_ptr fullNvSatBytes ⋆
      region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
        (4096 - fullAlignPad work_ptr) ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m := by
    have h1 : (region work_ptr 4096 ⋆ (bytes cnf_ptr fullNvSatBytes ⋆ R)) m := sep_ac hm
    rw [← region_merge_eq (a := work_ptr) (n1 := fullAlignPad work_ptr)
      (n2 := 4096 - fullAlignPad work_ptr) (n := 4096) (by omega) (by decide)] at h1
    exact sep_ac h1
  apply wp_call_of_spec; apply hInit
  change nvInitStateM5Spec (cnf_ptr, cnf_ptr + BitVec.ofNat 64 fullNvSatBytes.length,
    work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr),
    BitVec.ofNat 64 (4096 - fullAlignPad work_ptr), 16#64, ()) m _ _
  refine ⟨region work_ptr (fullAlignPad work_ptr) ⋆ R, rfl, hcfit,
    by rw [hav_to, BitVec.toNat_add, bv64_ofNat_toNat (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega,
    by rw [hav_to]; omega, by rw [hav_to]; omega, by rw [hav_to]; exact hm_sp,
    fun c s0 m0 hch hca hmv1 hnc1 hlen0 hcv1 hdcur0 halen0 hwlen0 hte0 hpr0 hcl0 hfu0 hunass0
      hunfl0 hoom0 hvals0 hwvec0 hmrk0 hfl0 hext0 hm0 => ?_⟩
  have hmx1 : 1 ≤ c.max_vars := by have := hlen0.core_ok.cur_vars_le; omega
  have hv0_0 : s0.core.vals[0]? = some 0#8 := by
    rw [hvals0]; simp [show 0 < 2 * c.max_vars by omega]
  have hmrk0_0 : s0.core.mrk[0]? = some 0#8 := by
    rw [hmrk0]; simp [show 0 < c.max_vars by omega]
  have hwsz0 : ∀ l < 2, fullWatchSize s0 l = 0 := fun l hl => by
    unfold fullWatchSize fullWatchSizeCore; rw [hwvec0]
    simp [show 2 * l + 1 < 4 * c.max_vars by omega]
  have hwlay0 : WatchStackLayout s0.core :=
    watchStackLayout_of_zero_wvec hlen0.core_ok.cur_vars_le hwvec0
  rw [← hch]
  c0_hsteps
  rotate_left
  · exfalso; cases hc
  c0_call hParse
  refine ⟨c, s0, cnf_ptr, region work_ptr (fullAlignPad work_ptr) ⋆ R, rfl, rfl, hcfit,
    hmv1, hnc1, hlen0, hcv1, hdcur0, halen0, by omega, hte0, hpr0, hcl0, hunass0, hunfl0,
    hoom0, hv0_0, hmrk0_0, hfl0, hwsz0, hwlay0, hext0, hm0, fun s1 m1 hnv1 hfu1 hm1 => ?_⟩
  have hm1_f : (FullMem c s1 ⋆
      (bytes cnf_ptr fullNvSatBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m1 :=
    sep_ac hm1
  c0_hsteps
  c0_call hPre
  refine ⟨c, s1, bytes cnf_ptr fullNvSatBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R,
    rfl, hnv1, by rw [hfu1, hfu0]; decide, hm1_f, fun s2 m2 hnv2 hm2 => ?_⟩
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (r_v, ()) m' => r_v = 10#64 ∧ m' = m2)
    (fun _ ⟨_, ⟨⟩⟩ m' ⟨rfl, rfl⟩ => by
      c0_hsteps; c0_call hExt
      refine ⟨c, s2, bytes cnf_ptr fullNvSatBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R,
        rfl, hnv2.len, hmx1, hnv2.v0, hnv2.ext0, hm2, fun vals3 m3 hvlen3 hv0_3 hm3 => ?_⟩
      let s3 : FullState := { s2 with core := { s2.core with vals := vals3 } }
      have hlen3 : s3.LengthsOk c :=
        ⟨{ hnv2.len.core_ok with vals_len := hvlen3 }, hnv2.len.scratch_ok⟩
      refine wp_store_sep (FullM4Compact.full_store_mv_mid (BitVec.ofNat 64 c.mv) hm3) ?_
      intro m3_1 hm3_1
      c0_step
      refine wp_load_of (FullM4Compact.full_load_max_vars_mid hm3_1) ?_
      c0_step
      let bva_bv : BitVec 64 := BitVec.ofNat 64 c.max_vars - BitVec.ofNat 64 c.mv
      have hmx_bd : c.max_vars < 2 * dimacsBound := c.hmaxv
      have hmv_bd := c.hmv; have hbva_bd := c.hbva
      unfold dimacsBound at hmx_bd hmv_bd
      have hbva_eq : (Full.hdrTailWords c s3).set 94 bva_bv = Full.hdrTailWords c s3 := by
        have h94 : (Full.hdrTailWords c s3)[94]'(by rw [Full.hdrTailWords_length]; decide) =
            bva_bv := by
          change BitVec.ofNat 64 c.bva_cap = BitVec.ofNat 64 c.max_vars - BitVec.ofNat 64 c.mv
          rw [bv_sub_ofNat (by omega) (by omega), show c.max_vars - c.mv = c.bva_cap by omega]
        rw [← h94, List.set_getElem_self]
      have hmid_arr : (array64 (c.hdr + 32) (Full.hdrTailWords c s3) ⋆
          (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
              s3.core.d_cur s3.core.d_val ⋆
            FullCoreArrays c s3.core ⋆ FullScratchArrays c s3.scratch ⋆ c.pad ⋆
            (bytes cnf_ptr fullNvSatBytes ⋆
              region work_ptr (fullAlignPad work_ptr) ⋆ R))) m3_1 := by
        unfold FullM4Compact.FullMemShrinkMid at hm3_1; exact sep_ac hm3_1
      obtain ⟨hst_bva, hm3_2⟩ := store_array64 (i := 94) bva_bv
        (by rw [Full.hdrTailWords_length]; decide) hmid_arr
      have hptr784 : c.hdr + 32 + BitVec.ofNat 64 (8 * 94) = c.hdr + 784 := by
        rw [BitVec.add_assoc, show (32 : BitVec 64) + BitVec.ofNat 64 (8 * 94) = 784 by decide]
      rw [hptr784] at hst_bva hm3_2
      rw [hbva_eq] at hm3_2
      refine wp_store_sep ⟨hst_bva, hm3_2⟩ ?_
      intro m3_2 hm3_2
      c0_step
      have hget4 := loadVal_array64 (i := 4)
        (by rw [Full.hdrTailWords_length]; decide) hm3_2
      rw [BitVec.add_assoc, show (32 : BitVec 64) + BitVec.ofNat 64 (8 * 4) = 64 by decide] at hget4
      have hpv4 : (Full.hdrTailWords c s3)[4]'(by rw [Full.hdrTailWords_length]; decide) =
          c.pVals := rfl
      rw [hpv4] at hget4
      refine wp_load_of hget4 ?_
      have hm3_2_b : (bytes cnf_ptr fullNvSatBytes ⋆
          dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
            s3.core.d_cur s3.core.d_val ⋆
          bytes c.pVals (s3.core.vals.map UInt8.ofBitVec) ⋆
          (Full.FullCheckRest c s3 ⋆
            (region work_ptr (fullAlignPad work_ptr) ⋆ R))) m3_2 := by
        have hfm3 : (bytes cnf_ptr fullNvSatBytes ⋆ FullMem c s3 ⋆
            (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m3_2 := by
          unfold FullMem; exact sep_ac hm3_2
        exact Full.fullMem_to_checkModel hlen3 hfm3
      c0_call hCheck
      refine ⟨BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc, s3.core.d_cur, s3.core.d_val,
        fullNvSatBytes, s3.core.vals.map UInt8.ofBitVec, c.mv,
        Full.FullCheckRest c s3 ⋆ (region work_ptr (fullAlignPad work_ptr) ⋆ R),
        rfl, rfl, hcfit, by omega, by simp [s3, hvlen3, hmv1]; omega,
        by simp [s3, hvlen3]; omega, by simpa [sep_assoc] using hm3_2_b, ?_⟩
      intro ok mv' nc' cur' val' m5 hok hm5
      have hmap0 : (s3.core.vals.map UInt8.ofBitVec)[0]? = some 1 := by
        simp [s3, List.getElem?_map, hv0_3]
      have hrun_t : runKissatCheckModel fullNvSatBytes (s3.core.vals.map UInt8.ofBitVec) c.mv =
          true := by
        rw [hmv1]; exact runKissatCheckModel_fullNvSatBytes hmap0
      simp only [hrun_t, ↓reduceIte] at hok
      subst hok
      have hptr_m5 : loadVal m5 i64
          (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) + 64#64) = some c.pVals := by
        have ha64 : (array64 (c.hdr + 32) (Full.hdrTailWords c s3) ⋆
            (bytes cnf_ptr fullNvSatBytes ⋆ dimacsState c.hdr mv' nc' cur' val' ⋆
              bytes c.pVals (s3.core.vals.map UInt8.ofBitVec) ⋆
              array (t := i8) c.pLitMark s3.core.lit_mark ⋆
              array (t := i8) c.pMark s3.core.mrk ⋆
              FullCoreU32A c s3.core ⋆ FullCoreU32B c s3.core ⋆ FullCoreDynArrs c s3.core ⋆
              FullScratchArrays c s3.scratch ⋆ c.pad ⋆
              (region work_ptr (fullAlignPad work_ptr) ⋆ R))) m5 := by
          unfold Full.FullCheckRest at hm5; exact sep_ac hm5
        have hld := loadVal_array64 (i := 4) (by rw [Full.hdrTailWords_length]; decide) ha64
        rw [hch, BitVec.add_assoc, show (32 : BitVec 64) + BitVec.ofNat 64 (8 * 4) = 64#64
          by decide] at hld
        exact hld
      have hb0_m5 : loadVal m5 i8 (c.pVals + BitVec.ofNat 64 (2 * (1 - 1))) = some 1#8 := by
        have hbs : (bytes c.pVals (s3.core.vals.map UInt8.ofBitVec) ⋆
            (bytes cnf_ptr fullNvSatBytes ⋆ dimacsState c.hdr mv' nc' cur' val' ⋆
              Full.FullCheckRest c s3 ⋆ (region work_ptr (fullAlignPad work_ptr) ⋆ R))) m5 :=
          sep_ac hm5
        have hlt0 : 0 < (s3.core.vals.map UInt8.ofBitVec).length := by
          simp [s3, hvlen3]; omega
        have hld := load_bytes_at (i := 0) hlt0 (by simp [s3, hvlen3]; omega) hbs
        have hget0 : (s3.core.vals.map UInt8.ofBitVec)[0]'hlt0 = 1 := by
          rw [List.getElem?_eq_getElem hlt0] at hmap0; exact Option.some.inj hmap0
        rw [hget0] at hld; simpa using hld
      have hsat_frame : ∀ (F : Mem 64 → Prop) (M : Mem 64), (Eq m5 ⋆ F) M →
          fullNvSatCnf.Sat (readModelFromWork M work_ptr) := fun F M hM => by
        refine fullNvSatCnf_sat_of_true1 ?_
        rw [readModelFromWork_frame hM hptr_m5 hb0_m5]; decide
      have hca' : c.avail = 4096 - fullAlignPad work_ptr := hca.trans hav_to
      have hm5_reg : (bytes cnf_ptr fullNvSatBytes ⋆ region work_ptr 4096 ⋆ R) m5 :=
        nv_merge_reg hwfit hw_ge (by
          rw [← hch, ← hca']
          exact Full.checkModel_post_to_region hlen3 hm5)
      refine wp_join_group (ts := [i64]) (fun (res_v, ()) m6 => res_v = 10#64 ∧ m6 = m5)
        (fun _ ⟨res_v, ⟨⟩⟩ m6 h6 => by
          dsimp only at h6; obtain ⟨rfl, hm6⟩ := h6; subst m6
          simp only [Blocks.get_here]; c0_hsteps; exact hQ m5 hsat_frame hm5_reg)
        (fun _ hJr => by c0_hsteps; exact hJr (10#64, ()) m5 ⟨rfl, rfl⟩))
    (fun _ hJ => by c0_hsteps; exact hJ (10#64, ()) m2 ⟨rfl, rfl⟩)

/-! ### Closed `270`-function `m5SatNvEnv` & `m5SatNvEnv_moduleOk` -/

private def m5SatNvExtraTable : List SpecEntry :=
  [ ⟨"full_assign_lvl", [i64, i32, i32, i32], [], nvAssignLvlSpec, true⟩
  , ⟨"full_zero_tables2", [i64], [], nvZeroTables2Spec, true⟩
  , ⟨"full_init_hdr", [i64, i64, i64, i64], [], nvInitHdrSpec, true⟩
  , ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool], nvInitStateM5Spec, true⟩
  , ⟨"full_ingest_cl", [i64, i64], [i64], nvIngestClSpec, true⟩
  , ⟨"full_parse_body", [i64, i64], [i64], nvParseBodySpec, true⟩
  , ⟨"full_prop_lit_raw", [i64, i32, i64], [.bool], nvPropLitRawSpec, true⟩
  , ⟨"full_propagate_ignore", [i64, i64], [i64], nvPropagateIgnoreSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], nvPropagateSpec, true⟩
  , ⟨"full_sweep_bins", [i64], [], nvSweepBinsSpec, true⟩
  , ⟨"full_rewatch_arena", [i64, i64], [.bool], nvRewatchArenaSpec, true⟩
  , ⟨"full_arena_sweep", [i64], [i64], nvArenaSweepSpec, true⟩
  , ⟨"full_extend", [i64], [], nvExtendSpec, true⟩
  , ⟨"full_preprocess_m5", [i64], [i64], nvPreprocessM5Spec, true⟩
  , ⟨"kissat_solve_bytes_m5", [i64, i64, i64, i64, i64], [i64], fullSatWitnessSpec, true⟩
  , ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], fullSatWitnessSpec, true⟩
  , ⟨"full_calc_ext_cap_m5", [i64], [i64], nvCalcZeroCapSpec, true⟩
  , ⟨"full_calc_scr_cap_m5", [i64], [i64], nvCalcZeroCapSpec, true⟩
  ]

private theorem m5SatNvExtraTable_nodup : (m5SatNvExtraTable.map SpecEntry.name).Nodup := by
  decide

private theorem m5SatNvExtraTable_noExit :
    ∀ e ∈ m5SatNvExtraTable, e.noExit = true := by
  intro e he
  have hall : m5SatNvExtraTable.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

/-- Closed `270`-function concrete SAT non-vacuity environment for `FullM5.m5Module`: union of
canonical `FullM5.m5Env` and the `16`-row concrete `"p cnf 1 1\n1 0\n"` trace table. -/
def m5SatNvEnv : Env := fun f as bs xs m Q X =>
  FullM5.m5Env f as bs xs m Q X ∨ Env.ofTable m5SatNvExtraTable f as bs xs m Q X

theorem m5SatNvEnv_noExit :
    ∀ f as bs xs m Q X X', m5SatNvEnv f as bs xs m Q X → m5SatNvEnv f as bs xs m Q X' := by
  intro f as bs xs m Q X X' h
  rcases h with h0 | he
  · exact Or.inl (FullM5.m5Env_noExit f as bs xs m Q X X' h0)
  · exact Or.inr (Env.ofTable_noExit m5SatNvExtraTable_noExit f as bs xs m Q X X' he)

private theorem m5SatNvEnv_extra_row (i : Nat) (e : SpecEntry)
    (hi : m5SatNvExtraTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X :=
      by intro _ _ _ _ h; dsimp only [SpecEntry.eff]; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → m5SatNvEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h => Or.inr
    (Env.ofTable_of_mem (List.mem_of_getElem? hi) m5SatNvExtraTable_nodup (hno xs m Q X h))

private theorem fn_eq_of_mem_nodup_nv {fs : List Fn} (hnd : (fs.map Fn.name).Nodup)
    {f g : Fn} (hf : f ∈ fs) (hg : g ∈ fs) (hnm : f.name = g.name) : f = g := by
  induction fs with
  | nil => nomatch hf
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hf with rfl | hf' <;> rcases List.mem_cons.mp hg with rfl | hg'
    · rfl
    · exact absurd (hnm ▸ List.mem_map_of_mem hg') hnd.1
    · exact absurd (hnm.symm ▸ List.mem_map_of_mem hf') hnd.1
    · exact ih hnd.2 hf' hg'

private theorem m5Fns_nodup_nv : (FullM5.m5Fns.map Fn.name).Nodup :=
  (List.nodup_append.mp FullM5.m5Env_moduleOk.nodup).1

private theorem m5SatNvEnv_m5_row {f : Sym} {as bs : List Ty} {S : Spec as bs}
    (h : ∀ xs m Q X, S xs m Q X → FullM5.m5Env f as bs xs m Q X) :
    ∀ xs m Q X, S xs m Q X → m5SatNvEnv f as bs xs m Q X :=
  fun xs m Q X hs => Or.inl (h xs m Q X hs)

/-- Unconditional closed `ModuleOk` for `m5SatNvEnv` on all `270` functions of `FullM5.m5Module`,
transporting all `254` untouched functions verbatim from `FullM5.m5Env_moduleOk`. -/
theorem m5SatNvEnv_moduleOk : ModuleOk m5SatNvEnv FullM5.m5Module := by
  refine moduleOk_or_env FullM5.m5Env_moduleOk fun fn hfn xs m Q X hs => ?_
  have hmatch : ∀ (idx : Nat) (target : Fn),
      FullM5.m5Fns[idx]? = some target → target.name = fn.name → fn = target :=
    fun _ target hget hnm =>
      fn_eq_of_mem_nodup_nv m5Fns_nodup_nv hfn (List.mem_of_getElem? hget) hnm.symm
  unfold m5SatNvExtraTable Env.ofTable at hs
  rcases hs with ⟨⟨hnm, _, _⟩, he⟩ | ⟨_, hs⟩
  · have hfn_eq := hmatch 29
      ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.full_assign_lvl_body⟩
      (by t_kernel_rfl) hnm
    subst hfn_eq; exact wp_noExit_lift_nv (nv_assign_lvl_wp m5SatNvEnv xs m Q _ he)
  rcases hs with ⟨⟨hnm, _, _⟩, he⟩ | ⟨_, hs⟩
  · have hfn_eq := hmatch 36
      ⟨"full_zero_tables2", [i64], [], Full.full_zero_tables2_body⟩
      (by t_kernel_rfl) hnm
    subst hfn_eq; exact wp_noExit_lift_nv (nv_zero_tables2_wp m5SatNvEnv xs m Q _ he)
  rcases hs with ⟨⟨hnm, _, _⟩, he⟩ | ⟨_, hs⟩
  · have hfn_eq := hmatch 39
      ⟨"full_init_hdr", [i64, i64, i64, i64], [], FullFastBveBudgets.full_init_hdr_body⟩
      (by t_kernel_rfl) hnm
    subst hfn_eq; exact wp_noExit_lift_nv (nv_init_hdr_wp m5SatNvEnv xs m Q _ he)
  rcases hs with ⟨⟨hnm, _, _⟩, he⟩ | ⟨_, hs⟩
  · have hfn_eq := hmatch 44
      ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool],
        FullM5Orch.full_init_state_m5_body⟩
      (by t_kernel_rfl) hnm
    subst hfn_eq
    exact wp_noExit_lift_nv (nv_init_state_m5_wp m5SatNvEnv
      (m5SatNvEnv_m5_row (FullM5.m5Env_eq_mkM5Env ▸ FullM5.mkM5Env_parse_header _))
      (m5SatNvEnv_m5_row (FullM5.m5Env_eq_mkM5Env ▸ FullM5.mkM5Env_fixed_bytes _))
      (m5SatNvEnv_m5_row (FullM5.m5Env_eq_mkM5Env ▸ FullM5.mkM5Env_calc_max_v _))
      (m5SatNvEnv_extra_row 16 ⟨"full_calc_ext_cap_m5", [i64], [i64], nvCalcZeroCapSpec, true⟩)
      (m5SatNvEnv_extra_row 17 ⟨"full_calc_scr_cap_m5", [i64], [i64], nvCalcZeroCapSpec, true⟩)
      (m5SatNvEnv_m5_row (FullM5.m5Env_eq_mkM5Env ▸ FullM5.mkM5Env_init_arenas _))
      (m5SatNvEnv_extra_row 2 ⟨"full_init_hdr", [i64, i64, i64, i64], [], nvInitHdrSpec, true⟩)
      (m5SatNvEnv_m5_row (FullM5.m5Env_eq_mkM5Env ▸ FullM5.mkM5Env_zero_tables1 _))
      (m5SatNvEnv_extra_row 1 ⟨"full_zero_tables2", [i64], [], nvZeroTables2Spec, true⟩)
      xs m Q _ he)
  rcases hs with ⟨⟨hnm, _, _⟩, he⟩ | ⟨_, hs⟩
  · have hfn_eq := hmatch 47
      ⟨"full_ingest_cl", [i64, i64], [i64], Full.full_ingest_cl_body⟩
      (by t_kernel_rfl) hnm
    subst hfn_eq
    exact wp_noExit_lift_nv (nv_ingest_cl_wp m5SatNvEnv
      (m5SatNvEnv_m5_row (FullM5.m5Env_eq_mkM5Env ▸ FullM5.mkM5Env_next_lit _))
      (m5SatNvEnv_extra_row 0 ⟨"full_assign_lvl", [i64, i32, i32, i32], [], nvAssignLvlSpec, true⟩)
      xs m Q _ he)
  rcases hs with ⟨⟨hnm, _, _⟩, he⟩ | ⟨_, hs⟩
  · have hfn_eq := hmatch 48
      ⟨"full_parse_body", [i64, i64], [i64], Full.full_parse_body_body⟩
      (by t_kernel_rfl) hnm
    subst hfn_eq
    exact wp_noExit_lift_nv (nv_parse_body_wp m5SatNvEnv
      (m5SatNvEnv_extra_row 4 ⟨"full_ingest_cl", [i64, i64], [i64], nvIngestClSpec, true⟩)
      (m5SatNvEnv_m5_row (FullM5.m5Env_eq_mkM5Env ▸ FullM5.mkM5Env_skip_ws_comments _))
      xs m Q _ he)
  rcases hs with ⟨⟨hnm, _, _⟩, he⟩ | ⟨_, hs⟩
  · have hfn_eq := hmatch 52
      ⟨"full_prop_lit_raw", [i64, i32, i64], [.bool], FullM4Bcp.full_prop_lit_m4_body⟩
      (by t_kernel_rfl) hnm
    subst hfn_eq; exact wp_noExit_lift_nv (nv_prop_lit_raw_wp m5SatNvEnv xs m Q _ he)
  rcases hs with ⟨⟨hnm, _, _⟩, he⟩ | ⟨_, hs⟩
  · have hfn_eq := hmatch 55
      ⟨"full_propagate_ignore", [i64, i64], [i64], FullM5Otfs.full_propagate_ignore_body⟩
      (by t_kernel_rfl) hnm
    subst hfn_eq
    exact wp_noExit_lift_nv (nv_propagate_ignore_wp m5SatNvEnv
      (m5SatNvEnv_extra_row 6
        ⟨"full_prop_lit_raw", [i64, i32, i64], [.bool], nvPropLitRawSpec, true⟩)
      xs m Q _ he)
  rcases hs with ⟨⟨hnm, _, _⟩, he⟩ | ⟨_, hs⟩
  · have hfn_eq := hmatch 56
      ⟨"full_propagate", [i64], [i64], FastCore.full_propagate_body⟩
      (by t_kernel_rfl) hnm
    subst hfn_eq
    exact wp_noExit_lift_nv (nv_propagate_wp m5SatNvEnv
      (m5SatNvEnv_extra_row 7
        ⟨"full_propagate_ignore", [i64, i64], [i64], nvPropagateIgnoreSpec, true⟩)
      xs m Q _ he)
  rcases hs with ⟨⟨hnm, _, _⟩, he⟩ | ⟨_, hs⟩
  · have hfn_eq := hmatch 63
      ⟨"full_sweep_bins", [i64], [], FullFastSched.full_sweep_bins_body⟩
      (by t_kernel_rfl) hnm
    subst hfn_eq
    exact wp_noExit_lift_nv (nv_sweep_bins_wp m5SatNvEnv
      (m5SatNvEnv_m5_row (FullM5.m5Env_eq_mkM5Env ▸ FullM5.mkM5Env_wstack_defrag _))
      xs m Q _ he)
  rcases hs with ⟨⟨hnm, _, _⟩, he⟩ | ⟨_, hs⟩
  · have hfn_eq := hmatch 65
      ⟨"full_rewatch_arena", [i64, i64], [.bool], Full.full_rewatch_arena_body⟩
      (by t_kernel_rfl) hnm
    subst hfn_eq; exact wp_noExit_lift_nv (nv_rewatch_arena_wp m5SatNvEnv xs m Q _ he)
  rcases hs with ⟨⟨hnm, _, _⟩, he⟩ | ⟨_, hs⟩
  · have hfn_eq := hmatch 66
      ⟨"full_arena_sweep", [i64], [i64], Full.full_arena_sweep_body⟩
      (by t_kernel_rfl) hnm
    subst hfn_eq
    exact wp_noExit_lift_nv (nv_arena_sweep_wp m5SatNvEnv
      (m5SatNvEnv_extra_row 9 ⟨"full_sweep_bins", [i64], [], nvSweepBinsSpec, true⟩)
      (m5SatNvEnv_extra_row 10
        ⟨"full_rewatch_arena", [i64, i64], [.bool], nvRewatchArenaSpec, true⟩)
      xs m Q _ he)
  rcases hs with ⟨⟨hnm, _, _⟩, he⟩ | ⟨_, hs⟩
  · have hfn_eq := hmatch 104
      ⟨"full_extend", [i64], [], FullM4.full_extend_body⟩
      (by t_kernel_rfl) hnm
    subst hfn_eq; exact wp_noExit_lift_nv (nv_extend_wp m5SatNvEnv xs m Q _ he)
  rcases hs with ⟨⟨hnm, _, _⟩, he⟩ | ⟨_, hs⟩
  · have hfn_eq := hmatch 263
      ⟨"full_preprocess_m5", [i64], [i64], FullM5Orch.full_preprocess_m5_body⟩
      (by t_kernel_rfl) hnm
    subst hfn_eq
    exact wp_noExit_lift_nv (nv_preprocess_m5_wp m5SatNvEnv
      (m5SatNvEnv_extra_row 8 ⟨"full_propagate", [i64], [i64], nvPropagateSpec, true⟩)
      (m5SatNvEnv_extra_row 11 ⟨"full_arena_sweep", [i64], [i64], nvArenaSweepSpec, true⟩)
      xs m Q _ he)
  rcases hs with ⟨⟨hnm, _, _⟩, he⟩ | ⟨_, hs⟩
  · have hfn_eq := hmatch 268
      ⟨"kissat_solve_bytes_m5", [i64, i64, i64, i64, i64], [i64],
        FullM5Orch.kissat_solve_bytes_m5_body⟩
      (by t_kernel_rfl) hnm
    subst hfn_eq
    exact wp_noExit_lift_nv (nv_solve_bytes_m5_wp m5SatNvEnv
      (m5SatNvEnv_extra_row 3
        ⟨"full_init_state_m5", [i64, i64, i64, i64, i64], [.bool], nvInitStateM5Spec, true⟩)
      (m5SatNvEnv_extra_row 5 ⟨"full_parse_body", [i64, i64], [i64], nvParseBodySpec, true⟩)
      (m5SatNvEnv_extra_row 13 ⟨"full_preprocess_m5", [i64], [i64], nvPreprocessM5Spec, true⟩)
      (m5SatNvEnv_extra_row 12 ⟨"full_extend", [i64], [], nvExtendSpec, true⟩)
      (m5SatNvEnv_m5_row (FullM5.m5Env_eq_mkM5Env ▸ FullM5.mkM5Env_check_model _))
      xs m Q _ he)
  rcases hs with ⟨⟨hnm, _, _⟩, he⟩ | ⟨_, hs⟩
  · have hfn_eq := hmatch 269 FullM5.m5SolveBytesFwdFn (by t_kernel_rfl) hnm
    subst hfn_eq
    exact wp_noExit_lift_nv (FullM5.m5_solve_bytes_fwd_wp m5SatNvEnv
      (S := fullSatWitnessSpec)
      (m5SatNvEnv_extra_row 14
        ⟨"kissat_solve_bytes_m5", [i64, i64, i64, i64, i64], [i64], fullSatWitnessSpec, true⟩)
      xs m Q _ he)
  rcases hs with ⟨⟨hnm, _, _⟩, he⟩ | ⟨_, hs⟩
  · have hfn_eq := hmatch 41
      ⟨"full_calc_ext_cap_m5", [i64], [i64], FullM5Orch.full_calc_ext_cap_m5_body⟩
      (by t_kernel_rfl) hnm
    subst hfn_eq; exact wp_noExit_lift_nv (nv_calc_ext_cap_m5_wp m5SatNvEnv xs m Q _ he)
  rcases hs with ⟨⟨hnm, _, _⟩, he⟩ | ⟨_, hs⟩
  · have hfn_eq := hmatch 42
      ⟨"full_calc_scr_cap_m5", [i64], [i64], FullM5Orch.full_calc_scr_cap_m5_body⟩
      (by t_kernel_rfl) hnm
    subst hfn_eq; exact wp_noExit_lift_nv (nv_calc_scr_cap_m5_wp m5SatNvEnv xs m Q _ he)
  exact hs.elim

/-- Concrete `Mem 64` SAT non-vacuity (`XPost := False`) for `kissat_solve_bytes_m5` under the
closed `270`-function `m5SatNvEnv`: returns `10#64` and certifies
`fullNvSatCnf.Sat (readModelFromWork m' (fullNvWorkPtr fullNvSatBytes))` on `"p cnf 1 1\n1 0\n"`
with a `4096`-byte workspace and `fuel = 16`. -/
theorem m5_sat_nonvacuous_m5 :
    let m0 : Mem 64 := (fullPayload fullNvSatBytes).At fullNvCnfPtr
    Func.wp m5SatNvEnv FullM5Orch.kissat_solve_bytes_m5_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvSatBytes.length,
        fullNvWorkPtr fullNvSatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 10#64 ∧
        fullNvSatCnf.Sat (readModelFromWork m' (fullNvWorkPtr fullNvSatBytes)) ∧
        (bytes fullNvCnfPtr fullNvSatBytes ⋆
          region (fullNvWorkPtr fullNvSatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) := by
  let fnM5 : Fn :=
    ⟨"kissat_solve_bytes_m5", [i64, i64, i64, i64, i64], [i64],
      FullM5Orch.kissat_solve_bytes_m5_body⟩
  have hsplit : FullM5.m5Module.fns =
      FullM5.m5Fns.take 268 ++ fnM5 :: [FullM5.m5SolveBytesFwdFn] := by
    change FullM5.m5Fns = FullM5.m5Fns.take 268 ++ [fnM5, FullM5.m5SolveBytesFwdFn]
    have hdrop : FullM5.m5Fns.drop 268 = [fnM5, FullM5.m5SolveBytesFwdFn] := by t_kernel_rfl
    rw [← hdrop, List.take_append_drop]
  exact (m5SatNvEnv_moduleOk.fnsOk _ _ _ hsplit).2.2 _ _ _ _
    ((m5SatNvEnv_extra_row 14
      ⟨"kissat_solve_bytes_m5", [i64, i64, i64, i64, i64], [i64], fullSatWitnessSpec, true⟩)
      _ _ _ _
      ⟨emp, by decide, by decide, rfl, rfl, rfl, by decide, by decide,
        by rw [sep_emp]; exact fullPayload_sep fullNvSatBytes (by decide),
        fun m' hsat hm' => ⟨rfl, hsat emp m' (by rw [sep_emp]), hm'⟩⟩)

/-- Concrete `Mem 64` SAT non-vacuity (`XPost := False`) on exported `kissat_solve_bytes` under
the closed `270`-function `m5SatNvEnv`: returns `10#64` and certifies
`fullNvSatCnf.Sat (readModelFromWork m' (fullNvWorkPtr fullNvSatBytes))` on `"p cnf 1 1\n1 0\n"`
with a `4096`-byte workspace and `fuel = 16`. -/
theorem m5_sat_nonvacuous :
    let m0 : Mem 64 := (fullPayload fullNvSatBytes).At fullNvCnfPtr
    Func.wp m5SatNvEnv FullM5.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvSatBytes.length,
        fullNvWorkPtr fullNvSatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 10#64 ∧
        fullNvSatCnf.Sat (readModelFromWork m' (fullNvWorkPtr fullNvSatBytes)) ∧
        (bytes fullNvCnfPtr fullNvSatBytes ⋆
          region (fullNvWorkPtr fullNvSatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) := by
  have hsplit : FullM5.m5Module.fns =
      FullM5.m5Fns.take 269 ++ FullM5.m5SolveBytesFwdFn :: [] := by
    change FullM5.m5Fns = FullM5.m5Fns.take 269 ++ [FullM5.m5SolveBytesFwdFn]
    have hdrop : FullM5.m5Fns.drop 269 = [FullM5.m5SolveBytesFwdFn] := by t_kernel_rfl
    rw [← hdrop, List.take_append_drop]
  exact (m5SatNvEnv_moduleOk.fnsOk _ _ _ hsplit).2.2 _ _ _ _
    ((m5SatNvEnv_extra_row 15
      ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], fullSatWitnessSpec, true⟩)
      _ _ _ _
      ⟨emp, by decide, by decide, rfl, rfl, rfl, by decide, by decide,
        by rw [sep_emp]; exact fullPayload_sep fullNvSatBytes (by decide),
        fun m' hsat hm' => ⟨rfl, hsat emp m' (by rw [sep_emp]), hm'⟩⟩)

end SatNvProofs

end LeanQbe.T.Examples.Kissat
