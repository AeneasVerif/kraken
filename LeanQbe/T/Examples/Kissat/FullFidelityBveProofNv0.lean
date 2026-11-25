/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBve
public import LeanQbe.T.Examples.Kissat.FullFidelityBveProofVar
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas1
import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
import LeanQbe.T.Examples.Kissat.FullM6SweepProofDenseProp
import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
import LeanQbe.T.Examples.Kissat.FullFidelityBveTactics
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.Bytes
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.OpsLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity BVE Parity Parametric `Mem 64` Non-Vacuity (`FullFidelityBveProofNv0`)

Genuine non-bailout concrete `Mem 64` UNSAT non-vacuity proofs (`XPost := False`, strictly `std3`,
`0` `@[expose]`, `0` `*Lemmas*` in `public import`) parameterized over `(Γ : Env)`:
1. `nvFidF0 = {(x1), (x0 ∨ ~x1), (~x0)}` (`nvFidF0_unsat`) and symbolic-`scratch_buf` (`16,384`
   `u32` words) concrete `Mem 64` builders (`nvFidCfg`, `nvFidCertState`, `nvFidSparseState`).
2. `nv_fid_bve_k6_mv_{zero,min,mid,cap}_at`: exact `GAP-BVE-01` dynamic `fidK6MaxV` scaling
   (`0#64`, `256#64`, `896#64`, `8192#64`).
3. `nv_fid_k6_add_ticks_{add,sat}_at`: concrete `Mem 64` saturating `u32` tick accumulation.
4. `nv_fid_certify_unit_direct_at`: direct C0 stepping of `full_bve_certify_unit_fid_body` on
   `nvFidCertMem` (`GAP-BVE-03`), proving exact `ok = true`, `s'.core.trail_end = 2`,
   `s'.core.vals[0]? = some 1#8`, `s'.core.vals[1]? = some 0xFF#8`, `s'.core.trl[1]? = some 0#32`,
   `FullDenseInvW`, `TmkZero`, `nvFidF0.Unsat`, and `FullMem`.
5. `nv_fid_{bve_var_m7,bve_var,elim_bve_m7,eliminate_m6}_at`: concrete `Mem 64` UNSAT witnesses
   across the `GAP-BVE-01..03` BVE pipeline.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBve

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

/-! ## 1. Shared 4-Var / `16,384`-Word Scratch Concrete Heap & UNSAT Fixture -/

private theorem nv_sep_append {P Q : Mem 64 → Prop} {a b : BitVec 64} {bs1 bs2 : List UInt8}
    (hb : b = a + BitVec.ofNat 64 bs1.length) (hlen : bs1.length + bs2.length ≤ 2 ^ 64)
    (h1 : P (bs1.At a)) (h2 : Q (bs2.At b)) : (P ⋆ Q) ((bs1 ++ bs2).At a) := by
  have heq := congrFun (Mem.At_append_sep bs1 bs2 a hlen) ((bs1 ++ bs2).At a)
  rw [← hb] at heq
  exact sep_mono2 (fun _ h => h ▸ h1) (fun _ h => h ▸ h2) _ (heq.mp rfl)

private theorem nv_arr_pad_p {t : Ty} {a : BitVec 64} {xs : List (Val t)} (n pad : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n + pad ≤ 2 ^ 64) :
    (bytesOf xs ++ List.replicate pad 0).length = n + pad ∧
    (array (t := t) a xs ⋆ region (a + BitVec.ofNat 64 n) pad)
      ((bytesOf xs ++ List.replicate pad 0).At a) :=
  ⟨by rw [List.length_append, bytesOf_length, List.length_replicate, hn],
   nv_sep_append (by rw [bytesOf_length, hn])
     (by rw [bytesOf_length, List.length_replicate]; omega)
     (array_bytes a xs (by omega)) ⟨List.replicate pad 0, List.length_replicate, rfl⟩⟩

private theorem nv_arr_p {t : Ty} {a : BitVec 64} {xs : List (Val t)} (n : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytesOf xs).length = n ∧ array (t := t) a xs ((bytesOf xs).At a) :=
  ⟨by rw [bytesOf_length, hn], array_bytes a xs (by omega)⟩

private theorem nv_arr64_p {a : BitVec 64} {xs : List (BitVec 64)} (n : Nat)
    (hn : 8 * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytes64 xs).length = n ∧ array64 a xs ((bytes64 xs).At a) :=
  ⟨by rw [bytes64_length, hn], array64_bytes a xs (by omega)⟩

private theorem nv_join_pair {P Q : Mem 64 → Prop} {a b : BitVec 64} {bs1 bs2 : List UInt8}
    {n1 n2 : Nat} (h1 : bs1.length = n1 ∧ P (bs1.At a))
    (h2 : bs2.length = n2 ∧ Q (bs2.At b))
    (hb : b = a + BitVec.ofNat 64 n1) (hbd : n1 + n2 ≤ 2 ^ 64) :
    (bs1 ++ bs2).length = n1 + n2 ∧ (P ⋆ Q) ((bs1 ++ bs2).At a) :=
  ⟨by rw [List.length_append, h1.1, h2.1], nv_sep_append (h1.1 ▸ hb) (by omega) h1.2 h2.2⟩

private theorem nv_sep_reorg {P Q : Mem 64 → Prop} {bs : List UInt8} {a : BitVec 64} {n : Nat}
    (h : bs.length = n ∧ P (bs.At a)) (himp : ∀ m, P m → Q m) :
    bs.length = n ∧ Q (bs.At a) :=
  ⟨h.1, himp _ h.2⟩

private theorem nv_pad_p (a : BitVec 64) (n : Nat) :
    (List.replicate n (0 : UInt8)).length = n ∧
      region a n ((List.replicate n (0 : UInt8)).At a) :=
  ⟨List.length_replicate, ⟨List.replicate n 0, List.length_replicate, rfl⟩⟩

/-- UNSAT 4-variable base formula `{(x1), (x0 ∨ ~x1), (~x0)}`. -/
def nvFidF0 : CNF Nat := cnfOfClauses [[2], [0, 3], [1]]

/-- Current level-0 formula matching `nvFidF0`. -/
def nvFidFCur : List (List Nat) := [[2], [0, 3], [1]]

theorem nvFidF0_unsat : nvFidF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [2]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [nvFidF0, cnfOfClauses]))
  have h1 : (cnfClause [0, 3]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [nvFidF0, cnfOfClauses]))
  have h2 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [nvFidF0, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1 h2
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0
  obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  obtain ⟨⟨v2, p2⟩, hm2, he2⟩ := h2
  rw [mem_cnfClause_iff] at hm0 hm1 hm2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm0 hm1 hm2
  rcases hm1 with hm1 | hm1
  · cases p1 <;> cases p2 <;> simp [litOfLiteral, mkLit] at hm1 hm2 <;> try omega
    have hv1 : v1 = 0 := by omega
    have hv2 : v2 = 0 := by omega
    subst hv1 hv2; dsimp only at he1 he2; rw [he1] at he2; cases he2
  · cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1 <;> try omega
    have hv0 : v0 = 1 := by omega
    have hv1 : v1 = 1 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1

theorem nvFid_entails_2 : (cnfOfClauses nvFidFCur).EntailsClause (cnfClause [2]) := by
  rw [CNF.entails_clause_def]; intro α hα
  exact (CNF.sat_iff_all_mem_sat.mp hα) _
    (CNF.Internal.mem_iff.mpr (by simp [nvFidFCur, cnfOfClauses]))

theorem nvFid_entails_03 : (cnfOfClauses nvFidFCur).EntailsClause (cnfClause [0, 3]) := by
  rw [CNF.entails_clause_def]; intro α hα
  exact (CNF.sat_iff_all_mem_sat.mp hα) _
    (CNF.Internal.mem_iff.mpr (by simp [nvFidFCur, cnfOfClauses]))

theorem nvFid_entails_0 : (cnfOfClauses nvFidFCur).EntailsClause (cnfClause [0]) := by
  rw [CNF.entails_clause_def]; intro α hα
  have h2 : (cnfClause [2]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [nvFidFCur, cnfOfClauses]))
  have h03 : (cnfClause [0, 3]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [nvFidFCur, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h2 h03
  obtain ⟨⟨v2, p2⟩, hm2, he2⟩ := h2
  obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h03
  rw [mem_cnfClause_iff] at hm2 hm1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2 hm1
  rcases hm1 with hm1 | hm1
  · rw [CNF.Clause.sat_iff_exists_mem_eq]
    refine ⟨(v1, p1), mem_cnfClause_iff.mpr (by simp [hm1]), he1⟩
  · cases p2 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm2 hm1 <;> try omega
    have hv2 : v2 = 1 := by omega
    have hv1 : v1 = 1 := by omega
    subst hv2 hv1; dsimp only at he2 he1; rw [he2] at he1; cases he1

/-- 4-variable arena + `16,384`-word scratch configuration (`hdr = 0x2000`, `avail = 67820`). -/
def nvFidCfg : FullCfg :=
  { hdr := 0x2000#64, avail := 67820, mv := 4, max_vars := 4, bva_cap := 0, nc := 2
    arena_cap := 6, wcap := 1, delayed_cap := 0, red_cap := 0, extend_cap := 0
    scratch_cap := 16384
    hbva := rfl, hmv := by decide, hmaxv := by decide, hnc := by decide, harena := by decide
    hwcap := by decide, hdel := by decide, hred := by decide, hext := by decide
    hscr := by decide, havail_fit := by decide, hsize := by decide }

def nvFidMkScratch (scr : List (BitVec 32)) : FullScratch :=
  { heap_len := 0, scinc := 0#64, rel_period := 0#64, rel_limit := 0#64, rel_wait := 0#64
    rel_u := 0#64, rel_v := 0#64, rel_trigger := 0#64, conflicts := 0#64
    learned_lits := 0#64, min_removed := 0#64, delayed_len := 0, stable := 0#64
    switched := 0#64, mode_count := 0#64, mode_confl_lim := 0#64, mode_tick_lim := 0#64
    mode_saved_ticks := 0#64, search_ticks := 0#64, q_first := 0#64, q_last := 0#64
    q_search_idx := 0#64, q_search_stamp := 0#64, q_cur_stamp := 0#64
    target_assigned := 0#64, best_assigned := 0#64, rephase_limit := 0#64, rephased := 0#64
    reduce_limit := 0#64, reductions := 0#64, tier1 := 2#64, tier2 := 6#64
    restarts := 0#64, restart_limit := 0#64, ema_fast_biased := 0#64, ema_fast_exp := 0#64
    ema_slow_biased := 0#64, ema_slow_exp := 0#64, extend_len := 0, rng_state := 0#64
    chrono_levels := 0#64, otfs_cnt := 0#64, eager_sub_cnt := 0#64, probe_limit := 0#64
    probings := 0#64, elim_limit := 0#64, eliminations := 0#64, elim_bound := 0#64
    iterating := 0#64, hbr_cnt := 0#64, trans_cnt := 0#64, viv_cnt := 0#64
    subst_cnt := 0#64, cong_cnt := 0#64, sweep_cnt := 0#64, bve_cnt := 0#64
    bce_cnt := 0#64, bva_cnt := 0#64, walk_cnt_stat := 0#64, fwd_sub_cnt := 0#64
    fwd_str_cnt := 0#64, ant_sz := 0#64, res_sz := 0#64
    walk_vals := List.replicate 8 0#8, phases := List.replicate 4 0#8
    phases_target := List.replicate 4 0#8, phases_best := List.replicate 4 0#8
    walk_best := List.replicate 4 0#8, heap := List.replicate 4 0#32
    pos := List.replicate 4 0#32, shrink_stk := List.replicate 4 0#32
    q_prev := List.replicate 4 0#32, q_next := List.replicate 4 0#32
    q_stamp := List.replicate 4 0#32, wsort := List.replicate 8 0#32
    work_stk1 := List.replicate 8 0#32, work_stk2 := List.replicate 8 0#32
    tarjan_mark := List.replicate 8 0#32, tarjan_reach := List.replicate 8 0#32
    score := List.replicate 4 0#64, sim_sig := List.replicate 4 0#64
    glue_used := List.replicate 64 0#32, last_learned := List.replicate 16 0xFFFFFFFF#32
    delayed := [], red_refs := [], extend_stk := [], scratch_buf := scr }

def nvFidMkCore (dm : BitVec 64) : FullCoreState :=
  { d_cur := 0#64, d_val := 0#64, cur_vars := 4, unassigned := 3#64
    arena_len := 0, wlen := 1, wusable := 0#64, arena_garbage := 0#64
    first_reducible := 0#64, num_irred := 0#64, num_redundant := 0#64, num_binary := 0#64
    unflushed := 1#64, probing := 0#64, trail_end := 1, propagated := 1
    cur_level := 0, fuel := 1#64, confl_ref := 0#64, confl_type := 0#64
    confl_lit0 := 0#64, confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0
    min_clr_len := 0, min_clr_full := 0#64, oom := 0#64, dense_mode := dm
    inconsistent := 0#64
    vals := [0#8, 0#8, 1#8, 0xFF#8, 0#8, 0#8, 0#8, 0#8]
    lit_mark := List.replicate 8 0#8, mrk := List.replicate 4 0#8
    flags := List.replicate 4 0#32, lvl := List.replicate 4 0#32
    rsns := List.replicate 4 0xFFFFFFFF#32
    trl := [2#32, 0#32, 0#32, 0#32], trail_pos := List.replicate 4 0#32
    tmp := List.replicate 4 0#32, min_clr := List.replicate 4 0#32
    frame_trail := List.replicate 5 0#32, frame_dec := List.replicate 5 0#32
    wvec := List.replicate 16 0#32, repr := List.replicate 8 0#32
    min_stk := List.replicate 10 0#32, arena := List.replicate 6 0#32, wstk := [0#32] }

def nvFidMkState (dm : BitVec 64) (scr : List (BitVec 32)) : FullState :=
  { core := nvFidMkCore dm, scratch := nvFidMkScratch scr }

theorem nvFidMk_lengths {dm : BitVec 64} {scr : List (BitVec 32)} (hscr : scr.length = 16384) :
    (nvFidMkState dm scr).LengthsOk nvFidCfg := by
  dsimp only [nvFidMkState, nvFidMkCore, nvFidMkScratch, nvFidCfg]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl,
    Nat.le_refl _, Nat.le_refl _, show 0 ≤ 6 by decide, show 1 ≤ 1 by decide,
    show 1 ≤ 4 by decide, show 1 ≤ 1 by decide, Nat.zero_le _, Nat.zero_le _⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, by change scr.length = 16384; exact hscr⟩⟩

private def nvFidBlkHdr (dm : BitVec 64) (scr : List (BitVec 32)) : List UInt8 :=
  let c := nvFidCfg; let s := nvFidMkState dm scr
  bytes64 [BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc, s.core.d_cur, s.core.d_val] ++
    bytes64 (Full.hdrTailWords c s)

private def nvFidBlkBytes (k : FullCoreState) (sc : FullScratch) : List UInt8 :=
  (bytesOf (t := i8) k.vals ++ List.replicate 0 0) ++
  (bytesOf (t := i8) sc.walk_vals ++ List.replicate 0 0) ++
  (bytesOf (t := i8) k.lit_mark ++ List.replicate 0 0) ++
  (bytesOf (t := i8) k.mrk ++ List.replicate 4 0) ++
  (bytesOf (t := i8) sc.phases ++ List.replicate 4 0) ++
  (bytesOf (t := i8) sc.phases_target ++ List.replicate 4 0) ++
  (bytesOf (t := i8) sc.phases_best ++ List.replicate 4 0) ++
  (bytesOf (t := i8) sc.walk_best ++ List.replicate 4 0)

private def nvFidBlkU32A (k : FullCoreState) : List UInt8 :=
  (bytesOf (t := i32) k.flags ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.lvl ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.rsns ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.trl ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.trail_pos ++ List.replicate 8 0)

private def nvFidBlkU32B (k : FullCoreState) (sc : FullScratch) : List UInt8 :=
  (bytesOf (t := i32) k.tmp ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.heap ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.pos ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.min_clr ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.shrink_stk ++ List.replicate 8 0)

private def nvFidBlkU32C (k : FullCoreState) (sc : FullScratch) : List UInt8 :=
  (bytesOf (t := i32) sc.q_prev ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.q_next ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.q_stamp ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.frame_trail ++ List.replicate 4 0) ++
  (bytesOf (t := i32) k.frame_dec ++ List.replicate 4 0)

private def nvFidBlkWvec (k : FullCoreState) (sc : FullScratch) : List UInt8 :=
  bytesOf (t := i32) k.wvec ++ bytesOf (t := i32) k.repr ++
  bytesOf (t := i32) sc.wsort ++ bytesOf (t := i32) sc.work_stk1 ++
  bytesOf (t := i32) sc.work_stk2 ++ bytesOf (t := i32) sc.tarjan_mark ++
  bytesOf (t := i32) sc.tarjan_reach ++ bytes64 sc.score ++ bytes64 sc.sim_sig

private def nvFidBlkTail (k : FullCoreState) (sc : FullScratch) : List UInt8 :=
  bytesOf (t := i32) k.min_stk ++ bytesOf (t := i32) sc.glue_used ++
  bytesOf (t := i32) sc.last_learned ++ bytesOf (t := i32) k.arena ++
  bytesOf (t := i32) k.wstk ++ bytesOf (t := i32) sc.delayed ++
  bytesOf (t := i32) sc.red_refs ++ bytesOf (t := i32) sc.extend_stk ++
  bytesOf (t := i32) sc.scratch_buf ++ List.replicate 0 0

def nvFidMkBytes (dm : BitVec 64) (scr : List (BitVec 32)) : List UInt8 :=
  let s := nvFidMkState dm scr
  nvFidBlkHdr dm scr ++ nvFidBlkBytes s.core s.scratch ++
    nvFidBlkU32A s.core ++ nvFidBlkU32B s.core s.scratch ++ nvFidBlkU32C s.core s.scratch ++
    nvFidBlkWvec s.core s.scratch ++ nvFidBlkTail s.core s.scratch

def nvFidMkMem (dm : BitVec 64) (scr : List (BitVec 32)) : Mem 64 :=
  (nvFidMkBytes dm scr).At nvFidCfg.hdr

private theorem nvFidMkMem_ok_pair (dm : BitVec 64) (scr : List (BitVec 32))
    (hscr : scr.length = 16384) :
    (nvFidMkBytes dm scr).length = 67820 ∧
      FullMem nvFidCfg (nvFidMkState dm scr) (nvFidMkMem dm scr) := by
  let c := nvFidCfg; let s := nvFidMkState dm scr
  have hv0 : valsBytes c.max_vars - 2 * c.max_vars = 0 := by decide
  have h2m : 2 * c.max_vars = 8 := by decide
  have hm4 : markBytes c.max_vars - c.max_vars = 4 := by decide
  have hm4v : c.max_vars = 4 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * c.max_vars = 8 := by decide
  have h4m : 4 * c.max_vars = 16 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 4 := by decide
  have h4p : 4 * (c.max_vars + 1) = 20 := by decide
  have hsl : c.slack = 0 := by decide
  have hHdr : (nvFidBlkHdr dm scr).length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        array64 (c.hdr + 32) (Full.hdrTailWords c s))
        ((nvFidBlkHdr dm scr).At c.hdr) :=
    nv_join_pair
      ⟨rfl, dimacsState_bytes c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val⟩
      (nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide))
      rfl (by rw [bytes64_length]; simp only [List.length_cons, List.length_nil]; decide)
  have hBytes : (nvFidBlkBytes s.core s.scratch).length = 64 ∧
      ((array (t := i8) c.pVals s.core.vals ⋆ array (t := i8) c.pLitMark s.core.lit_mark ⋆
          array (t := i8) c.pMark s.core.mrk) ⋆
        FullScrByteArrs c s.scratch ⋆ c.padBytes)
        ((nvFidBlkBytes s.core s.scratch).At c.pVals) := by
    have h1 := nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 8 0 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 8 0
      rfl (by decide)
    have h3 := nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 8 0 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 4 4 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 4 4 rfl (by decide)
    have h6 := nv_arr_pad_p (t := i8) (a := c.pPhasesTarget) (xs := s.scratch.phases_target) 4 4
      rfl (by decide)
    have h7 := nv_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best) 4 4
      rfl (by decide)
    have h8 := nv_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best) 4 4
      rfl (by decide)
    have j12 := nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := nv_join_pair j123 h4 (by decide) (by decide)
    have j12345 := nv_join_pair j1234 h5 (by decide) (by decide)
    have j123456 := nv_join_pair j12345 h6 (by decide) (by decide)
    have j1234567 := nv_join_pair j123456 h7 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair j1234567 h8 (by decide) (by decide)) fun _ hm => by
      have pB : ∀ {A1 A2 A3 A4 A5 A6 A7 A8 P1 P2 P3 P4 P5 P6 P7 P8 : Mem 64 → Prop} {k},
          ((((((((A1 ⋆ P1) ⋆ (A2 ⋆ P2)) ⋆ (A3 ⋆ P3)) ⋆ (A4 ⋆ P4)) ⋆
            (A5 ⋆ P5)) ⋆ (A6 ⋆ P6)) ⋆ (A7 ⋆ P7)) ⋆ (A8 ⋆ P8)) k →
          ((A1 ⋆ A3 ⋆ A4) ⋆ (A2 ⋆ A5 ⋆ A6 ⋆ A7 ⋆ A8) ⋆
            (P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6 ⋆ P7 ⋆ P8)) k := fun x => sep_ac x
      unfold FullScrByteArrs FullCfg.padBytes; rw [hv0, h2m, hm4, hm4v]; exact pB hm
  have hU32A : (nvFidBlkU32A s.core).length = 120 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        ((nvFidBlkU32A s.core).At c.pFlags) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 16 8 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 16 8 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 16 8 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 16 8 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 16 8 rfl
      (by decide)
    have j12 := nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := nv_join_pair j123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair j1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu8, h4m]; exact sep_ac hm
  have hU32B : (nvFidBlkU32B s.core s.scratch).length = 120 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pHeap s.scratch.heap ⋆
        array (t := i32) c.pPos s.scratch.pos ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
        array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        ((nvFidBlkU32B s.core s.scratch).At c.pTmp) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 16 8 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 16 8 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 16 8 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 16 8 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk) 16 8 rfl
      (by decide)
    have j12 := nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := nv_join_pair j123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair j1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu8, h4m]; exact sep_ac hm
  have hU32C : (nvFidBlkU32C s.core s.scratch).length = 120 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        ((nvFidBlkU32C s.core s.scratch).At c.pQPrev) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 16 8 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 16 8 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 16 8 rfl
      (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 20 4 rfl
      (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 20 4 rfl
      (by decide)
    have j12 := nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := nv_join_pair j123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair j1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu8, hu4, h4m, h4p]; exact sep_ac hm
  have hWvec : (nvFidBlkWvec s.core s.scratch).length = 320 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        ((nvFidBlkWvec s.core s.scratch).At c.pWvec) := by
    have h1 := nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 64 rfl (by decide)
    have h2 := nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 32 rfl (by decide)
    have h3 := nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 32 rfl (by decide)
    have h4 := nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 32 rfl (by decide)
    have h5 := nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 32 rfl (by decide)
    have h6 := nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 32 rfl
      (by decide)
    have h7 := nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 32 rfl
      (by decide)
    have h8 := nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 32 rfl (by decide)
    have h9 := nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 32 rfl (by decide)
    have j12 := nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := nv_join_pair j123 h4 (by decide) (by decide)
    have j12345 := nv_join_pair j1234 h5 (by decide) (by decide)
    have j123456 := nv_join_pair j12345 h6 (by decide) (by decide)
    have j1234567 := nv_join_pair j123456 h7 (by decide) (by decide)
    have j12345678 := nv_join_pair j1234567 h8 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair j12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail : (nvFidBlkTail s.core s.scratch).length = 65924 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        ((nvFidBlkTail s.core s.scratch).At c.pMinStk) := by
    have h1 := nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 40 rfl (by decide)
    have h2 := nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256 rfl
      (by decide)
    have h3 := nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned) 64 rfl
      (by decide)
    have h4 := nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 24 rfl (by decide)
    have h5 := nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 4 rfl (by decide)
    have h6 := nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl (by decide)
    have h7 := nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl (by decide)
    have h8 := nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl
      (by decide)
    have h9 := nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 65536
      (by change 4 * scr.length = 65536; rw [hscr]) (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 (0 : UInt8)).At c.pSlack) := by
      rw [hsl]; exact nv_pad_p c.pSlack 0
    have j12 := nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := nv_join_pair j123 h4 (by decide) (by decide)
    have j12345 := nv_join_pair j1234 h5 (by decide) (by decide)
    have j123456 := nv_join_pair j12345 h6 (by decide) (by decide)
    have j1234567 := nv_join_pair j123456 h7 (by decide) (by decide)
    have j12345678 := nv_join_pair j1234567 h8 (by decide) (by decide)
    have j123456789 := nv_join_pair j12345678 h9 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair j123456789 h10 (by decide) (by decide)) fun _ hm => by
      unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := nv_join_pair hHdr hBytes (by decide) (by decide)
  have h02 := nv_join_pair h01 hU32A (by decide) (by decide)
  have h03 := nv_sep_reorg (nv_join_pair h02 hU32B (by decide) (by decide)) fun _ hm => by
    have p1 : ∀ {D H CB SB PB UA PA T Hp Ps Mc Sh PB2 : Mem 64 → Prop} {k},
        (((D ⋆ H) ⋆ (CB ⋆ SB ⋆ PB)) ⋆ (UA ⋆ PA) ⋆ ((T ⋆ Hp ⋆ Ps ⋆ Mc ⋆ Sh) ⋆ PB2)) k →
        ((D ⋆ H) ⋆ ((CB ⋆ (UA ⋆ T ⋆ Mc)) ⋆ (SB ⋆ (Hp ⋆ Ps ⋆ Sh)) ⋆ (PB ⋆ PA ⋆ PB2))) k :=
      fun x => sep_ac x
    exact p1 hm
  have h04 := nv_sep_reorg (nv_join_pair h03 hU32C (by decide) (by decide)) fun _ hm => by
    have p2 : ∀ {DH C1 S1 P1 Qp Qn Qs FTr FDec PC : Mem 64 → Prop} {k},
        ((DH ⋆ (C1 ⋆ S1 ⋆ P1)) ⋆ ((Qp ⋆ Qn ⋆ Qs) ⋆ (FTr ⋆ FDec) ⋆ PC)) k →
        (DH ⋆ ((C1 ⋆ FTr ⋆ FDec) ⋆ (S1 ⋆ (Qp ⋆ Qn ⋆ Qs)) ⋆ (P1 ⋆ PC))) k := fun x => sep_ac x
    exact p2 hm
  have h05 := nv_join_pair h04 hWvec (by decide) (by decide)
  refine nv_sep_reorg (nv_join_pair h05 hTail (by decide) (by decide)) fun _ hm => ?_
  have p3 : ∀ {D H CoreB ScrB P2 Wv Re SW Sc Ss MS Gu Ll CD SD SL : Mem 64 → Prop} {k},
      (((D ⋆ H ⋆ (CoreB ⋆ ScrB ⋆ P2)) ⋆ ((Wv ⋆ Re) ⋆ SW ⋆ (Sc ⋆ Ss))) ⋆
        (MS ⋆ (Gu ⋆ Ll) ⋆ CD ⋆ SD ⋆ SL)) k →
      (D ⋆ H ⋆ (CoreB ⋆ Wv ⋆ Re ⋆ MS ⋆ CD) ⋆ (ScrB ⋆ SW ⋆ Sc ⋆ Ss ⋆ Gu ⋆ Ll ⋆ SD) ⋆ (P2 ⋆ SL)) k :=
    fun x => sep_ac x
  have p4 : ∀ {D H CB UA_T_Mc FTr FDec Wv Re MS CD Scr Pad : Mem 64 → Prop} {k},
      (D ⋆ H ⋆ (((CB ⋆ UA_T_Mc ⋆ FTr ⋆ FDec) ⋆ Wv ⋆ Re ⋆ MS ⋆ CD)) ⋆ Scr ⋆ Pad) k →
      (D ⋆ H ⋆ (CB ⋆ UA_T_Mc ⋆ (FTr ⋆ FDec ⋆ Wv ⋆ Re ⋆ MS) ⋆ CD) ⋆ Scr ⋆ Pad) k :=
    fun x => sep_ac x
  have p5 : ∀ {D H Core SB HpPsSh QpQnQs SW Sc Ss Gu Ll SD Pad : Mem 64 → Prop} {k},
      (D ⋆ H ⋆ Core ⋆ (((SB ⋆ HpPsSh) ⋆ QpQnQs) ⋆ SW ⋆ Sc ⋆ Ss ⋆ Gu ⋆ Ll ⋆ SD) ⋆ Pad) k →
      (D ⋆ H ⋆ Core ⋆ (SB ⋆ (HpPsSh ⋆ QpQnQs) ⋆ SW ⋆ (Sc ⋆ Ss ⋆ Gu ⋆ Ll) ⋆ SD) ⋆ Pad) k :=
    fun x => sep_ac x
  have p6 : ∀ {D H Core Scr PB PA PB2 PC SL : Mem 64 → Prop} {k},
      (D ⋆ H ⋆ Core ⋆ Scr ⋆ (((PB ⋆ PA ⋆ PB2) ⋆ PC) ⋆ SL)) k →
      (D ⋆ H ⋆ Core ⋆ Scr ⋆ (PB ⋆ PA ⋆ PB2 ⋆ PC ⋆ SL)) k := fun x => sep_ac x
  have p7 : ∀ {D H Core SB Hp Ps Sh Qp Qn Qs SW Meta SD Pad : Mem 64 → Prop} {k},
      (D ⋆ H ⋆ Core ⋆ (SB ⋆ ((Hp ⋆ Ps ⋆ Sh) ⋆ (Qp ⋆ Qn ⋆ Qs)) ⋆ SW ⋆ Meta ⋆ SD) ⋆ Pad) k →
      (D ⋆ H ⋆ Core ⋆ (SB ⋆ (Hp ⋆ Ps ⋆ Sh ⋆ Qp ⋆ Qn ⋆ Qs) ⋆ SW ⋆ Meta ⋆ SD) ⋆ Pad) k :=
    fun x => sep_ac x
  unfold FullMem FullCoreArrays FullCoreByteArrs FullCoreU32A FullCoreU32B
    FullScratchArrays FullScrU32A FullScrMetaArrs FullCfg.pad
  exact p7 (p6 (p5 (p4 (p3 hm))))

theorem nvFidMkMem_ok (dm : BitVec 64) {scr : List (BitVec 32)} (hscr : scr.length = 16384) :
    (FullMem nvFidCfg (nvFidMkState dm scr) ⋆ emp) (nvFidMkMem dm scr) := by
  rw [sep_emp]; exact (nvFidMkMem_ok_pair dm scr hscr).2

theorem nvFidBase_witness (dm : BitVec 64) :
    FullWitnessInv nvFidCfg nvFidF0 nvFidFCur (nvFidMkCore dm) := by
  have hrefs : fullArenaClauseRefsCore (nvFidMkCore dm) = [] := rfl
  have hcv : (nvFidMkCore dm).cur_vars = 4 := rfl
  have hte : (nvFidMkCore dm).trail_end = 1 := rfl
  have hcl : (nvFidMkCore dm).cur_level = 0 := rfl
  have hdm : (nvFidMkCore dm).dense_mode = dm := rfl
  have harl : (nvFidMkCore dm).arena_len = 0 := rfl
  have hrsn0 : (nvFidMkCore dm).rsns[((nvFidMkCore dm).trl[0]?.getD 0#32).toNat / 2]?.getD
      0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by dsimp only [nvFidMkCore]; rfl
  have hext : ExtUnsatSound nvFidF0 4 nvFidFCur := by
    refine ⟨(varsBoundedBool_iff 4 nvFidFCur).mp rfl, fun hu => ?_⟩
    simpa [nvFidF0, nvFidFCur] using hu
  have har : FullArenaClausesInv nvFidCfg nvFidFCur (nvFidMkCore dm) := by
    refine ⟨Or.inl harl, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; cases hr
    · intro r hr; rw [hrefs] at hr; cases hr
    · intro r hr; rw [hrefs] at hr; cases hr
    · intro r hr; rw [hrefs] at hr; cases hr
  have hwat : ModeWatchesInv nvFidFCur (nvFidMkCore dm) := by
    have hws0 : ∀ l < 8, fullWatchSizeCore (nvFidMkCore dm) l = 0 := fun l hl => by
      dsimp only [fullWatchSizeCore, nvFidMkCore]
      exact (by decide : ∀ q : Fin 8,
        ((List.replicate 16 (0#32 : BitVec 32))[2 * q.1 + 1]?.getD 0#32).toNat = 0) ⟨l, hl⟩
    have hwo0 : ∀ l < 8, fullWatchOffCore (nvFidMkCore dm) l = 0 := fun l hl => by
      dsimp only [fullWatchOffCore, nvFidMkCore]
      exact (by decide : ∀ q : Fin 8,
        ((List.replicate 16 (0#32 : BitVec 32))[2 * q.1]?.getD 0#32).toNat = 0) ⟨l, hl⟩
    have hwlen : (nvFidMkCore dm).wlen = 1 := rfl
    by_cases hc : dm = 0#64
    · unfold ModeWatchesInv; rw [hdm, ite_eq_left hc]
      refine WatchesInv.of_slices
        (fun l hl => by rw [hcv] at hl; rw [hwo0 l hl, hws0 l hl, hwlen]; decide)
        (fun l hl hp => absurd hp (by rw [hcv] at hl; rw [hws0 l hl]; omega))
        (fun l1 _ h1 _ _ hp => absurd hp (by rw [hcv] at h1; rw [hws0 l1 h1]; omega))
        (fun l hl => by
          rw [hcv] at hl; rw [hwo0 l hl, hws0 l hl]; exact WatchSliceOk.empty)
    · unfold ModeWatchesInv; rw [hdm, ite_eq_right hc]
      refine DenseWatchesInv.of_slices
        (fun l hl => by rw [hcv] at hl; rw [hwo0 l hl, hws0 l hl, hwlen]; decide)
        (fun l hl hp => absurd hp (by rw [hcv] at hl; rw [hws0 l hl]; omega))
        (fun l1 _ h1 _ _ hp => absurd hp (by rw [hcv] at h1; rw [hws0 l1 h1]; omega))
        (fun l hl => by
          rw [hcv] at hl; rw [hwo0 l hl, hws0 l hl]; exact DenseWatchSliceOk.empty)
  exact
    { ext_sound := hext
      inconsistent_sound := fun h => absurd rfl h
      arena := har
      watches := hwat
      cur_level_le := by rw [hcl, hte]; decide
      trail_lits_lt := fun i hi => by
        rw [hte] at hi; have hi0 : i = 0 := by omega
        subst hi0; rw [hcv]; dsimp only [nvFidMkCore]; decide
      trail_vars_nodup := fun i j hi hj _ => by
        rw [hte] at hi hj; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl; dsimp only [nvFidMkCore]
        exact (by decide : ∀ q : Fin 8,
          let v := ([0#8, 0#8, 1#8, 0xFF#8, 0#8, 0#8, 0#8, 0#8] : List (BitVec 8))[q.1]?.getD 0#8
          v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) ⟨l, hl⟩
      vals_true_iff := fun l hl => by
        rw [hcv] at hl
        refine ⟨fun hv => ?_, ?_⟩
        · dsimp only [nvFidMkCore] at hv
          have hc := (by decide : ∀ q : Fin 8,
            ([0#8, 0#8, 1#8, 0xFF#8, 0#8, 0#8, 0#8, 0#8] :
              List (BitVec 8))[q.1]?.getD 0#8 = 1#8 → q.1 = 2) ⟨l, hl⟩ hv
          refine ⟨0, by rw [hte]; decide, hc.symm⟩
        · rintro ⟨i, hi, htr⟩
          rw [hte] at hi; have hi0 : i = 0 := by omega
          subst hi0; rw [← htr]; rfl
      vals_false_iff := fun l hl => by
        rw [hcv] at hl
        refine ⟨fun hv => ?_, ?_⟩
        · dsimp only [nvFidMkCore] at hv
          have hc := (by decide : ∀ q : Fin 8,
            ([0#8, 0#8, 1#8, 0xFF#8, 0#8, 0#8, 0#8, 0#8] :
              List (BitVec 8))[q.1]?.getD 0#8 = 0xFF#8 → q.1 ^^^ 1 = 2) ⟨l, hl⟩ hv
          refine ⟨0, by rw [hte]; decide, hc.symm⟩
        · rintro ⟨i, hi, htr⟩
          rw [hte] at hi; have hi0 : i = 0 := by omega
          subst hi0
          have hl3 : l = 3 := by
            have h2 : ((nvFidMkCore dm).trl[0]?.getD 0#32).toNat = 2 := rfl
            rw [h2] at htr
            exact (by decide : ∀ q : Fin 8, 2 = q.1 ^^^ 1 → q.1 = 3) ⟨l, hl⟩ htr
          subst hl3; rfl
      lvl_le := fun i hi => by
        rw [hte] at hi; have hi0 : i = 0 := by omega
        subst hi0; rw [hcl]; dsimp only [nvFidMkCore]; exact Nat.zero_le _
      dec_earliest := fun i j hi hj _ _ => by rw [hte] at hi hj; omega
      levels_inhabited := fun L h1 h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by
        rw [hte] at hi; have hi0 : i = 0 := by omega
        subst hi0; exact nvFid_entails_2
      trail_pos_inv := fun i hi => by
        rw [hte] at hi; have hi0 : i = 0 := by omega
        subst hi0; dsimp only [nvFidMkCore]; rfl
      level0_rsn_none := fun i hi _ => by
        rw [hte] at hi; have hi0 : i = 0 := by omega
        subst hi0; exact hrsn0
      frame_trail_lt := fun L hL => by
        rw [hcl] at hL; have hL0 : L = 0 := by omega
        subst hL0; rw [hte]; dsimp only [nvFidMkCore]; decide
      frame_trail_mono := fun L1 L2 h12 hL2 => by
        rw [hcl] at hL2; have hL1 : L1 = 0 := by omega
        have hL20 : L2 = 0 := by omega
        subst hL1; subst hL20; exact Nat.le_refl _
      frame_trail_before_lt := fun L _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun L _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun idx hidx hne => by
        rw [hte] at hidx; have hi0 : idx = 0 := by omega
        subst hi0; exact absurd hrsn0 hne
      reason_lit_mem := fun idx hidx hne => by
        rw [hte] at hidx; have hi0 : idx = 0 := by omega
        subst hi0; exact absurd hrsn0 hne }

private theorem nvFid_litMarksClear (dm : BitVec 64) (scr : List (BitVec 32)) :
    FullLitMarksClear nvFidCfg (nvFidMkState dm scr) :=
  ⟨fun v hv => by
    have hv4 : v < 4 := hv
    dsimp only [nvFidMkState, nvFidMkCore]
    exact (by decide : ∀ q : Fin 4,
      (List.replicate 4 (0#8 : BitVec 8))[q.1]?.getD 0#8 = 0#8) ⟨v, hv4⟩,
   fun l hl => by
    have hl8 : l < 8 := hl
    dsimp only [nvFidMkState, nvFidMkCore]
    exact (by decide : ∀ q : Fin 8,
      (List.replicate 8 (0#8 : BitVec 8))[q.1]?.getD 0#8 = 0#8) ⟨l, hl8⟩⟩

private theorem nvFid_extScratchOk (dm : BitVec 64) (scr : List (BitVec 32)) :
    FullExtScratchOk nvFidCfg (nvFidMkState dm scr) :=
  ⟨fun i hi => by
    have hi8 : i < 8 := hi
    dsimp only [nvFidMkState, nvFidMkScratch]
    exact Or.inl ((by decide : ∀ q : Fin 8,
      (List.replicate 16 (0xFFFFFFFF#32 : BitVec 32))[q.1]?.getD 0xFFFFFFFF#32 =
        0xFFFFFFFF#32) ⟨i, hi8⟩),
   Nat.zero_le _⟩

theorem nvFidState_denseInvW {scr : List (BitVec 32)} (hscr : scr.length = 16384) :
    FullDenseInvW nvFidCfg nvFidF0 nvFidFCur (nvFidMkState 1#64 scr) := by
  refine ⟨nvFidMk_lengths hscr, nvFidBase_witness 1#64, nvFid_litMarksClear 1#64 scr,
    ?_, nvFid_extScratchOk 1#64 scr, rfl, by change (1#64 : BitVec 64) ≠ 0#64; decide⟩
  intro r hr _; change r ∈ ([] : List Nat) at hr; cases hr

theorem nvFidState_sparseInv {scr : List (BitVec 32)} (hscr : scr.length = 16384) :
    FullSparseInv nvFidCfg nvFidF0 (nvFidMkState 0#64 scr) := by
  refine ⟨⟨nvFidMk_lengths hscr, nvFidFCur, nvFidBase_witness 0#64⟩,
    nvFid_litMarksClear 0#64 scr, ?_, nvFid_extScratchOk 0#64 scr, rfl⟩
  intro r hr _; change r ∈ ([] : List Nat) at hr; cases hr

theorem nvFidState_tmkZero (dm : BitVec 64) (scr : List (BitVec 32)) :
    TmkZero (nvFidMkState dm scr) := fun v hv => by
  have hv4 : v < 4 := hv
  dsimp only [nvFidMkState, nvFidMkScratch]
  exact (by decide : ∀ q : Fin 4,
    (List.replicate 8 (0#32 : BitVec 32))[q.1]?.getD 0#32 = 0#32) ⟨v, hv4⟩

/-- Scratch buffer for direct unit-certification NV (`scr[0] = 0x80000003` binary `[0, 3]`,
`scr[4002] = 1` positive mask bit 0). -/
def nvFidCertScr : List (BitVec 32) :=
  ((List.replicate 16384 0#32).set 0 0x80000003#32).set 4002 1#32

theorem nvFidCertScr_len : nvFidCertScr.length = 16384 := by
  rw [nvFidCertScr, List.length_set, List.length_set, List.length_replicate]

theorem nvFidCertScr_get0 : nvFidCertScr[0]? = some 0x80000003#32 := by
  rw [nvFidCertScr, List.getElem?_set_ne (by decide), List.getElem?_set_self
    (by rw [List.length_replicate]; decide)]

theorem nvFidCertScr_get4002 : nvFidCertScr[4002]? = some 1#32 := by
  rw [nvFidCertScr, List.getElem?_set_self
    (by rw [List.length_set, List.length_replicate]; decide)]

theorem nvFidCertScr_get4204 : nvFidCertScr[4204]? = some 0#32 := by
  rw [nvFidCertScr, List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
    List.getElem?_replicate]
  simp only [show 4204 < 16384 by decide, ↓reduceIte]

def nvFidCertState : FullState := nvFidMkState 1#64 nvFidCertScr
def nvFidCertMem : Mem 64 := nvFidMkMem 1#64 nvFidCertScr
def nvFidSparseState : FullState := nvFidMkState 0#64 nvFidCertScr
def nvFidSparseMem : Mem 64 := nvFidMkMem 0#64 nvFidCertScr

/-- Saturating tick-addition scratch buffer (`scr[4204] = 0xFFFFFF00`). -/
def nvFidTicksScr : List (BitVec 32) := (List.replicate 16384 0#32).set 4204 0xFFFFFF00#32

theorem nvFidTicksScr_len : nvFidTicksScr.length = 16384 := by
  rw [nvFidTicksScr, List.length_set, List.length_replicate]

theorem nvFidTicksScr_get4204 : nvFidTicksScr[4204]? = some 0xFFFFFF00#32 := by
  rw [nvFidTicksScr, List.getElem?_set_self (by rw [List.length_replicate]; decide)]

def nvFidTicksState : FullState := nvFidMkState 1#64 nvFidTicksScr
def nvFidTicksMem : Mem 64 := nvFidMkMem 1#64 nvFidTicksScr

/-! ## 2. `full_bve_k6_mv_fid` Dynamic Scratch-Scaled `K6` Envelope NV (`GAP-BVE-01`) -/

theorem nv_fid_bve_k6_mv_zero_at (Γ : Env) (m : Mem 64) :
    Func.wp Γ full_bve_k6_mv_fid_body (0#64, ()) m
      (fun (r, ()) m' => r = 0#64 ∧ m' = m) (fun _ _ _ _ => False) := by
  unfold Func.wp full_bve_k6_mv_fid_body
  c0_hsteps!; exact ⟨rfl, rfl⟩

theorem nv_fid_bve_k6_mv_min_at (Γ : Env) (m : Mem 64) :
    Func.wp Γ full_bve_k6_mv_fid_body (16384#64, ()) m
      (fun (r, ()) m' => r = 256#64 ∧ m' = m) (fun _ _ _ _ => False) := by
  unfold Func.wp full_bve_k6_mv_fid_body
  c0_hsplit
  · exfalso; revert hc; decide
  · c0_hsplit
    · exfalso; revert hc; decide
    · c0_hsplit
      · c0_hsteps!; exact ⟨rfl, rfl⟩
      · exfalso; revert hc; decide

theorem nv_fid_bve_k6_mv_mid_at (Γ : Env) (m : Mem 64) :
    Func.wp Γ full_bve_k6_mv_fid_body (65536#64, ()) m
      (fun (r, ()) m' => r = 896#64 ∧ m' = m) (fun _ _ _ _ => False) := by
  unfold Func.wp full_bve_k6_mv_fid_body
  c0_hsteps_nogrp
  all_goals first
    | (c0_hsteps!; exact ⟨by decide, rfl⟩)
    | (exfalso; revert hc; decide)

theorem nv_fid_bve_k6_mv_cap_at (Γ : Env) (m : Mem 64) :
    Func.wp Γ full_bve_k6_mv_fid_body (524288#64, ()) m
      (fun (r, ()) m' => r = 8192#64 ∧ m' = m) (fun _ _ _ _ => False) := by
  unfold Func.wp full_bve_k6_mv_fid_body
  c0_hsteps_nogrp
  all_goals first
    | (c0_hsteps!; exact ⟨by decide, rfl⟩)
    | (exfalso; revert hc; decide)

/-! ## 3. `full_fid_k6_add_ticks` Saturating `u32` Ticks Concrete `Mem 64` NV (`GAP-BVE-01`) -/

private theorem nv_fid_get_4204_bv (xs : List (BitVec 32))
    {h2 : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4204)).toNat < xs.length}
    {cur : BitVec 32} (h1 : 4204 < xs.length) (hcur : xs[4204]? = some cur) :
    xs[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4204)).toNat]'h2 = cur := by
  have heq : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4204)).toNat = 4204 := by decide
  have hget : xs[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4204)).toNat]'h2 = xs[4204]'h1 := by
    congr 1
  rw [hget]
  exact Option.some.inj (by rw [← List.getElem?_eq_getElem h1]; exact hcur)

private theorem nv_fid_k6_add_ticks_exec (Γ : Env) (c : FullCfg) (hsc : c.scratch_cap = 16384)
    (s : FullState) (hlen : s.LengthsOk c) (m0 : Mem 64) (hm0 : (FullMem c s ⋆ emp) m0)
    (delta : BitVec 64) (cur new_tk : BitVec 32)
    (hcur : s.scratch.scratch_buf[4204]? = some cur)
    (hspec : (if delta ≥ 0xFFFFFFFF#64 - cur.setWidth 64
      then 0xFFFFFFFF#32 else BitVec.setWidth 32 (cur.setWidth 64 + delta)) = new_tk) :
    Func.wp Γ full_fid_k6_add_ticks_body (c.hdr, delta, ()) m0
      (fun () m' => ∃ s' : FullState,
        s'.scratch.scratch_buf[4204]? = some new_tk ∧ nvFidF0.Unsat ∧ FullMem c s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem c s ⋆ emp) m0 := hm0
  have hscr_len : s.scratch.scratch_buf.length = 16384 := by
    rw [hlen.scratch_ok.scratch_buf_len, hsc]
  have h15744 : 15744 ≤ s.scratch.scratch_buf.length := by omega
  have h4204_lt : 4204 < s.scratch.scratch_buf.length := by omega
  have h4204_bv : (4204#64 : BitVec 64).toNat < s.scratch.scratch_buf.length := by
    change 4204 < s.scratch.scratch_buf.length; omega
  unfold Func.wp full_fid_k6_add_ticks_body
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
    (fun x => x = new_tk) ?_ ?_
  · rintro _ tk htk
    subst htk
    rw [Blocks.get_here]
    c0_hsteps!
    rw [sep_emp] at hm
    have hidx : (4204#64 : BitVec 64).toNat = 4204 := rfl
    rw [hidx] at hm
    refine ⟨_, ?_, nvFidF0_unsat, hm⟩
    dsimp only; rw [List.getElem?_set_self (by omega)]
  · intro Jtk hJtk
    rw [nv_fid_get_4204_bv s.scratch.scratch_buf h4204_lt hcur]
    have h4294 : (4294967295 : BitVec 64) = 0xFFFFFFFF#64 := rfl
    rw [h4294]
    refine head_wp_cmp_uge (va := delta) (vb := 0xFFFFFFFF#64 - cur.setWidth 64) rfl rfl ?_
    dsimp only
    cases hbr : (0xFFFFFFFF#64 - cur.setWidth 64).ule delta
    · have hge : ¬ delta ≥ 0xFFFFFFFF#64 - cur.setWidth 64 := by
        intro h; have h1 : (0xFFFFFFFF#64 - cur.setWidth 64).ule delta = true := by
          rw [BitVec.ule_eq_decide]; exact decide_eq_true h
        rw [hbr] at h1; cases h1
      have hnw : new_tk = BitVec.setWidth 32 (cur.setWidth 64 + delta) := by
        rw [← hspec, ite_eq_right hge]
      c0_hsteps_nogrp
      exact hJtk _ hnw.symm
    · have hge : delta ≥ 0xFFFFFFFF#64 - cur.setWidth 64 := by
        rw [BitVec.ule_eq_decide, decide_eq_true_eq] at hbr
        exact hbr
      have hnw : new_tk = 0xFFFFFFFF#32 := by rw [← hspec, ite_eq_left hge]
      c0_hsteps_nogrp
      · exact hJtk 0xFFFFFFFF#32 hnw.symm
      · cases hc

theorem nv_fid_k6_add_ticks_add_at (Γ : Env) :
    Func.wp Γ full_fid_k6_add_ticks_body (nvFidCfg.hdr, 1500#64, ()) nvFidCertMem
      (fun () m' => ∃ s' : FullState,
        s'.scratch.scratch_buf[4204]? = some 1500#32 ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvFidCfg nvFidCertState ⋆ emp) nvFidCertMem :=
    nvFidMkMem_ok 1#64 nvFidCertScr_len
  exact nv_fid_k6_add_ticks_exec Γ nvFidCfg rfl nvFidCertState
    (nvFidMk_lengths nvFidCertScr_len) nvFidCertMem hm 1500#64 0#32 1500#32
    nvFidCertScr_get4204 (by decide)

theorem nv_fid_k6_add_ticks_sat_at (Γ : Env) :
    Func.wp Γ full_fid_k6_add_ticks_body (nvFidCfg.hdr, 1000#64, ()) nvFidTicksMem
      (fun () m' => ∃ s' : FullState,
        s'.scratch.scratch_buf[4204]? = some 0xFFFFFFFF#32 ∧ nvFidF0.Unsat ∧
          FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvFidCfg nvFidTicksState ⋆ emp) nvFidTicksMem :=
    nvFidMkMem_ok 1#64 nvFidTicksScr_len
  exact nv_fid_k6_add_ticks_exec Γ nvFidCfg rfl nvFidTicksState
    (nvFidMk_lengths nvFidTicksScr_len) nvFidTicksMem hm 1000#64 0xFFFFFF00#32 0xFFFFFFFF#32
    nvFidTicksScr_get4204 (by decide)

/-! ## 4. `full_bve_certify_unit_fid` Direct Concrete `Mem 64` NV (`GAP-BVE-03`) -/

private def nvFidCertLpInv (c : FullCfg) (s0 : FullState) :
    Nat → Tup Val [i32, .bool, i32] → Mem 64 → Prop :=
  fun n xs m => n = 0 ∧ xs = (0#32, false, 0#32, ()) ∧ (FullMem c s0 ⋆ emp) m

private def nvFidCertBrkPost (c : FullCfg) (s0 : FullState) :
    Tup Val [i32, .bool, .bool, i32] → Mem 64 → Prop :=
  fun xs m => xs = (0#32, true, false, 0#32, ()) ∧ (FullMem c s0 ⋆ emp) m

private theorem nv_fid_m6MaxVSpec_of {a : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : Q (BitVec.ofNat 64 (k6MaxV a.toNat), ()) m) :
    m6MaxVSpec (vals (Arg.var a, ())) m Q X := h

private theorem nv_fid_certify_unit_direct_exec (Γ : Env) (c : FullCfg)
    (hc_mv : c.max_vars = 4) (hc_sc : c.scratch_cap = 16384) (s0 : FullState)
    (hlen : s0.LengthsOk c) (hdw0 : FullDenseInvW c nvFidF0 nvFidFCur s0)
    (htmk0 : TmkZero s0) (m0 : Mem 64) (hm : (FullMem c s0 ⋆ emp) m0)
    (hcv0 : s0.core.cur_vars = 4) (hte0 : s0.core.trail_end = 1)
    (hval0 : s0.core.vals[(0#32 : BitVec 32).toNat]?.getD 0#8 = 0#8)
    (hval3 : s0.core.vals[3]? = some 0xFF#8)
    (hget0 : s0.scratch.scratch_buf[0]? = some 0x80000003#32)
    (hget4002 : s0.scratch.scratch_buf[4002]? = some 1#32)
    (hMaxV : ∀ a m Q X, m6MaxVSpec a m Q X → Γ "full_m6_max_v" [i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X) :
    Func.wp Γ full_bve_certify_unit_fid_body
      (c.hdr, 0#32, 0#32, 0#32, 1#32, 4002#32, ()) m0
      (fun (ok, ()) m' => ∃ s' : FullState,
        ok = true ∧ s'.core.trail_end = 2 ∧ s'.core.vals[0]? = some 1#8 ∧
        s'.core.vals[1]? = some 0xFF#8 ∧ s'.core.trl[1]? = some 0#32 ∧
        FullDenseInvW c nvFidF0 nvFidFCur s' ∧ TmkZero s' ∧
        nvFidF0.Unsat ∧ FullMem c s' m')
      (fun _ _ _ _ => False) := by
  have hscr_len : s0.scratch.scratch_buf.length = 16384 := by
    rw [hlen.scratch_ok.scratch_buf_len, hc_sc]
  have hvl : s0.core.vals.length = 8 := by rw [hlen.core_ok.vals_len, hc_mv]
  have hvl0 : 0 < s0.core.vals.length := by omega
  have hvl0_bv : (0#64 : BitVec 64).toNat < s0.core.vals.length := by
    change 0 < s0.core.vals.length; omega
  have hvl3 : 3 < s0.core.vals.length := by omega
  have hvl3_zw :
      (BitVec.setWidth 64 (2147483651#32 &&& (2147483647 : BitVec 32))).toNat <
        s0.core.vals.length := by
    have hidx : (BitVec.setWidth 64 (2147483651#32 &&& (2147483647 : BitVec 32))).toNat = 3 := by
      decide
    omega
  have htl_len : s0.core.trl.length = 4 := by rw [hlen.core_ok.trl_len, hc_mv]
  have h4002_nat : (((4002#32 : BitVec 32) + (0#32 >>> 5)).setWidth 64).toNat = 4002 := by
    decide
  have h4002_lt : (((4002#32 : BitVec 32) + (0#32 >>> 5)).setWidth 64).toNat <
      s0.scratch.scratch_buf.length := by omega
  have h0_nat : (((0#32 : BitVec 32) + 0#32).setWidth 64).toNat = 0 := by decide
  have h0_lt : (((0#32 : BitVec 32) + 0#32).setWidth 64).toNat <
      s0.scratch.scratch_buf.length := by omega
  have hval0_val : s0.core.vals[0]'hvl0 = 0#8 := by
    have hv := hval0
    change s0.core.vals[0]?.getD 0#8 = 0#8 at hv
    rw [List.getElem?_eq_getElem hvl0, Option.getD_some] at hv
    exact hv
  have hval0_bv : s0.core.vals[(0#64 : BitVec 64).toNat]'hvl0_bv = 0#8 := hval0_val
  have hval3_val : ∀ {h}, s0.core.vals[3]'h = 0xFF#8 := fun {h} =>
    Option.some.inj (by rw [← List.getElem?_eq_getElem h]; exact hval3)
  have hval3_zw :
      ∀ {h},
        s0.core.vals[(BitVec.setWidth 64 (2147483651#32 &&& (2147483647 : BitVec 32))).toNat]'h =
          0xFF#8 := by
    intro h
    have hidx : (BitVec.setWidth 64 (2147483651#32 &&& (2147483647 : BitVec 32))).toNat = 3 := by
      decide
    have hget :
        s0.core.vals[(BitVec.setWidth 64 (2147483651#32 &&& (2147483647 : BitVec 32))).toNat]'h =
          s0.core.vals[3]'hvl3 := by congr 1
    rw [hget]; exact hval3_val
  have h4002_val : ∀ {h}, s0.scratch.scratch_buf[
      (((4002#32 : BitVec 32) + (0#32 >>> 5)).setWidth 64).toNat]'h = 1#32 := by
    intro h; have h1 : 4002 < s0.scratch.scratch_buf.length := by omega
    have hget : s0.scratch.scratch_buf[
        (((4002#32 : BitVec 32) + (0#32 >>> 5)).setWidth 64).toNat]'h =
        s0.scratch.scratch_buf[4002]'h1 := by congr 1
    rw [hget]; exact Option.some.inj (by rw [← List.getElem?_eq_getElem h1]; exact hget4002)
  have h0_val : ∀ {h}, s0.scratch.scratch_buf[
      (((0#32 : BitVec 32) + 0#32).setWidth 64).toNat]'h = 0x80000003#32 := by
    intro h; have h1 : 0 < s0.scratch.scratch_buf.length := by omega
    have hget : s0.scratch.scratch_buf[
        (((0#32 : BitVec 32) + 0#32).setWidth 64).toNat]'h =
        s0.scratch.scratch_buf[0]'h1 := by congr 1
    rw [hget]; exact Option.some.inj (by rw [← List.getElem?_eq_getElem h1]; exact hget0)
  unfold Func.wp full_bve_certify_unit_fid_body
  c0_hsteps_nogrp
  refine wp_call_of_spec _ _ (hMaxV _ _ _ _ (nv_fid_m6MaxVSpec_of ?_))
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
    (fun x => x = 4#32) ?_ ?_
  · intro _ max_csz hcsz
    subst hcsz
    rw [Blocks.get_here]
    refine wp_loop_break_group (nvFidCertBrkPost c s0) (nvFidCertLpInv c s0) ?_ ?_ ?_
    · rintro B ⟨nv_b, de_b, ab_b, idx_b, ⟨⟩⟩ m_b ⟨heq_b, hm_b⟩
      cases heq_b
      rw [Blocks.get_here]
      c0_hsteps_nogrp
      · refine wp_loop_group (ts := [i32])
          (fun _ xs m_c => xs = (0#32, ()) ∧ m_c = m_b) ?_ ?_
        · rintro Lc nc ⟨ci, ⟨⟩⟩ m_c hLc ⟨hci, hm_c⟩
          cases hci; cases hm_c
          rw [Blocks.get_here]
          c0_hsteps_nogrp
          c0_hstep; c0_hstep; c0_hstep
          rw [hval0_val]
          c0_hsteps_nogrp
          · exfalso; revert hc; decide
          · c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun _ m_a =>
              ∃ s' : FullState,
                s'.core.trail_end = 2 ∧ s'.core.vals[0]? = some 1#8 ∧
                s'.core.vals[1]? = some 0xFF#8 ∧ s'.core.trl[1]? = some 0#32 ∧
                FullDenseInvW c nvFidF0 nvFidFCur s' ∧ TmkZero s' ∧
                (FullMem c s' ⋆ emp) m_a) ?_ ?_
            · intro _ _ m_a hs
              rw [Blocks.get_here]
              c0_hsteps!
              obtain ⟨s', hte, hv0, hv1, htl1, hdw', htmk', hm'⟩ := hs
              rw [sep_emp] at hm'
              exact ⟨s', rfl, hte, hv0, hv1, htl1, hdw', htmk', nvFidF0_unsat, hm'⟩
            · intro Ja hJa
              c0_hsteps_nogrp
              c0_hsteps_nogrp
              refine wp_call_of_spec _ _ (hAssign _ _ _ _ ?_)
              change fullAssignLvlSpec (c.hdr, 0#32, 0xFFFFFFFF#32, 0#32, ()) m_b _ _
              refine ⟨c, s0, emp, rfl, hlen, hm_b, ?_⟩
              dsimp only
              have hpre : ¬ (s0.core.cur_vars ≤ (0#32 : BitVec 32).toNat / 2 ∨
                  c.max_vars ≤ s0.core.trail_end ∨
                  s0.core.vals[(0#32 : BitVec 32).toNat]?.getD 0#8 ≠ 0#8) := by
                rw [hc_mv, hcv0, hte0, hval0]; decide
              rw [ite_eq_right hpre]
              intro flags' unass' phases' m' hfll hphl hm'
              have ⟨hdw', hcore_eq⟩ := assignLvl0_preserves_denseInvW (lit := 0#32)
                hdw0 hfll hphl (by rw [hcv0]; decide) hval0 nvFid_entails_0
                (unassigned' := unass') (unflushed' := s0.core.unflushed + 1#64)
              simp only [↓reduceIte] at hm'
              c0_hsteps!
              have htmk' : TmkZero _ := htmk0.congr rfl rfl
              have hv_set : ∀ (xs : List (BitVec 8)) (hxs : xs.length = 8),
                  ((xs.set 0 1#8).set 1 0xFF#8)[0]? = some 1#8 ∧
                  ((xs.set 0 1#8).set 1 0xFF#8)[1]? = some 0xFF#8 := fun xs hxs =>
                ⟨by rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by omega)],
                 by rw [List.getElem?_set_self (by rw [List.length_set]; omega)]⟩
              have hv01 := hv_set s0.core.vals hvl
              have htl1 : (s0.core.trl.set s0.core.trail_end 0#32)[1]? = some 0#32 := by
                rw [hte0, List.getElem?_set_self (by omega)]
              exact hJa () m' ⟨_, by rw [hte0], hv01.1, hv01.2, htl1, hdw', htmk', hm'⟩
        · intro Jc hJc; c0_hsteps!; exact hJc 0 (0#32, ()) m_b ⟨rfl, rfl⟩
      · cases hc
    · rintro B L n ⟨nv_l, de_l, idx_l, ⟨⟩⟩ m_l hB hL ⟨hn0, hxs, hm_l⟩
      cases hn0; cases hxs
      rw [Blocks.get_here]
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i32, .bool, .bool]) (fun _ _ => False)
        (fun _ _ _ h => False.elim h) ?_
      intro Js _
      c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
      rw [h4002_val]
      c0_hsteps_nogrp
      · rw [h0_val]
        refine wp_join_group (ts := [i32, .bool, .bool]) (fun _ _ => False)
          (fun _ _ _ h => False.elim h) ?_
        intro Js1 _
        c0_hsplit
        · c0_hstep; c0_hstep; c0_hstep; c0_hstep
          rw [hval3_zw]
          c0_hsteps_nogrp <;>
            first
            | exact hB (0#32, true, false, 0#32, ()) m_l ⟨rfl, hm_l⟩
            | (exfalso; revert hc; decide)
        · exfalso; revert hc; decide
      · exfalso; revert hc; decide
    · intro B L hB hL
      c0_hsteps_nogrp
      exact hL 0 (0#32, false, 0#32, ()) m0 ⟨rfl, rfl, hm⟩
  · intro Jcs hJcs
    have _ : c.max_vars < 65535 := by rw [hc_mv]; decide
    c0_hsteps_nogrp
    rw [hc_mv]; exact hJcs 4#32 rfl

theorem nv_fid_certify_unit_direct_at (Γ : Env)
    (hMaxV : ∀ a m Q X, m6MaxVSpec a m Q X → Γ "full_m6_max_v" [i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X) :
    Func.wp Γ full_bve_certify_unit_fid_body
      (nvFidCfg.hdr, 0#32, 0#32, 0#32, 1#32, 4002#32, ()) nvFidCertMem
      (fun (ok, ()) m' => ∃ s' : FullState,
        ok = true ∧ s'.core.trail_end = 2 ∧ s'.core.vals[0]? = some 1#8 ∧
        s'.core.vals[1]? = some 0xFF#8 ∧ s'.core.trl[1]? = some 0#32 ∧
        FullDenseInvW nvFidCfg nvFidF0 nvFidFCur s' ∧ TmkZero s' ∧
        nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvFidCfg nvFidCertState ⋆ emp) nvFidCertMem :=
    nvFidMkMem_ok 1#64 nvFidCertScr_len
  exact nv_fid_certify_unit_direct_exec Γ nvFidCfg rfl rfl nvFidCertState
    (nvFidMk_lengths nvFidCertScr_len) (nvFidState_denseInvW nvFidCertScr_len)
    (nvFidState_tmkZero 1#64 nvFidCertScr) nvFidCertMem hm rfl rfl rfl rfl
    nvFidCertScr_get0 nvFidCertScr_get4002 hMaxV hAssign

/-! ## 5. BVE Pipeline Concrete `Mem 64` UNSAT NV (`var_m7`, `var`, `elim_bve_m7`, `elim_m6`) -/

theorem nv_fid_bve_var_m7_at (Γ : Env)
    (hCollect : ∀ a m Q X, fullBveCollectSpec a m Q X →
      Γ "full_bve_collect_m7" [i64, i32, i64, i32] [i32] a m Q X)
    (hExtNeed : ∀ a m Q X, fullBveExtNeedSpec a m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] a m Q X)
    (hWeaken : ∀ a m Q X, fullBveWeakenTmkSpec a m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] a m Q X)
    (hSetInact : ∀ a m Q X, fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X)
    (hGatesFid : ∀ a m Q X, m8BveGatesSpec a m Q X →
      Γ "full_bve_gates_fid" [i64, i32, i32, i32] [] a m Q X)
    (hGatesM7 : ∀ a m Q X, FullM7BveGates.fullBveGatesM7Spec a m Q X →
      Γ "full_bve_gates_m7" [i64, i32, i32, i32] [] a m Q X)
    (hResPair : ∀ a m Q X, fullBveResolvePairSpec a m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hCommit : ∀ a m Q X, fullBveCommitResTmkSpec a m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] a m Q X)
    (hFlushUnits : ∀ a m Q X, FullM6BveFwd.fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X) :
    Func.wp Γ full_bve_var_m7_body (nvFidCfg.hdr, 0#32, ()) nvFidCertMem
      (fun (r, ()) m' => ∃ s' : FullState,
        FullDenseInv nvFidCfg nvFidF0 s' ∧ TmkZero s' ∧ (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧
        nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvFidCfg nvFidCertState ⋆ emp) nvFidCertMem :=
    nvFidMkMem_ok 1#64 nvFidCertScr_len
  refine full_bve_var_m7_fid_wp Γ hCollect hExtNeed hWeaken hSetInact hGatesFid hGatesM7
    hResPair hAssign hDefrag hCommit hFlushUnits (nvFidCfg.hdr, 0#32, ()) nvFidCertMem _ _ ?_
  refine ⟨nvFidCfg, nvFidF0, nvFidCertState, emp, rfl,
    (nvFidState_denseInvW nvFidCertScr_len).toDense, nvFidState_tmkZero 1#64 nvFidCertScr,
    by decide, hm, fun r s' m' hdw' htmk' _ _ hr _ hm' => ?_⟩
  rw [sep_emp] at hm'
  exact ⟨s', hdw', htmk', hr, nvFidF0_unsat, hm'⟩

theorem nv_fid_bve_var_at (Γ : Env)
    (hVarM7 : ∀ a m Q X, fullBveVarDefSpec a m Q X →
      Γ "full_bve_var_m7" [i64, i32] [i64] a m Q X) :
    Func.wp Γ full_bve_var_body (nvFidCfg.hdr, 0#32, ()) nvFidCertMem
      (fun (r, ()) m' => ∃ s' : FullState,
        FullDenseInv nvFidCfg nvFidF0 s' ∧ TmkZero s' ∧ (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧
        nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvFidCfg nvFidCertState ⋆ emp) nvFidCertMem :=
    nvFidMkMem_ok 1#64 nvFidCertScr_len
  refine full_bve_var_fid_wp Γ hVarM7 (nvFidCfg.hdr, 0#32, ()) nvFidCertMem _ _ ?_
  refine ⟨nvFidCfg, nvFidF0, nvFidCertState, emp, rfl,
    (nvFidState_denseInvW nvFidCertScr_len).toDense, nvFidState_tmkZero 1#64 nvFidCertScr,
    by decide, hm, fun r s' m' hdw' htmk' _ _ hr _ hm' => ?_⟩
  rw [sep_emp] at hm'
  exact ⟨s', hdw', htmk', hr, nvFidF0_unsat, hm'⟩

theorem nv_fid_elim_bve_m7_at (Γ : Env)
    (hPop : ∀ a m Q X, FullM6BveFwd.fullBveHeapPopM6Spec a m Q X →
      Γ "full_bve_heap_pop_m7" [i64, i64] [i32] a m Q X)
    (hNbrs : ∀ a m Q X, m3ElimCollectNbrsSpec a m Q X →
      Γ "full_bve_collect_nbrs_m7" [i64, i32] [i64] a m Q X)
    (hVar : ∀ a m Q X, fullBveVarDefSpec a m Q X →
      Γ "full_bve_var_m7" [i64, i32] [i64] a m Q X)
    (hFlush : ∀ a m Q X, FullM6BveFwd.fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X)
    (hPush : ∀ a m Q X, m8BveHeapPushSpec a m Q X →
      Γ "full_bve_heap_push_m7" [i64, i64, i32] [i64] a m Q X) :
    Func.wp Γ full_elim_bve_m7_body (nvFidCfg.hdr, 0#64, ()) nvFidCertMem
      (fun (r, ()) m' => ∃ s' : FullState,
        FullDenseInv nvFidCfg nvFidF0 s' ∧ TmkZero s' ∧ (r = 1#64 ∨ r = 20#64) ∧
        nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvFidCfg nvFidCertState ⋆ emp) nvFidCertMem :=
    nvFidMkMem_ok 1#64 nvFidCertScr_len
  refine full_elim_bve_m7_fid_wp Γ hPop hNbrs hVar hFlush hPush
    (nvFidCfg.hdr, 0#64, ()) nvFidCertMem _ _ ?_
  refine ⟨nvFidCfg, nvFidF0, nvFidCertState, emp, rfl,
    (nvFidState_denseInvW nvFidCertScr_len).toDense, nvFidState_tmkZero 1#64 nvFidCertScr,
    hm, fun r s' m' hdw' htmk' _ hr _ hm' => ?_⟩
  rw [sep_emp] at hm'
  exact ⟨s', hdw', htmk', hr, nvFidF0_unsat, hm'⟩

theorem nv_fid_eliminate_m6_at (Γ : Env)
    (hDticks : ∀ a m Q X, schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hLog : ∀ a m Q X, m7Log10Q16Spec a m Q X →
      Γ "full_log10_q16_m7" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFwd : ∀ a m Q X, fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, m3ElimBveSpec a m Q X →
      Γ "full_elim_bve_m7" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    Func.wp Γ full_eliminate_m6_body (nvFidCfg.hdr, false, ()) nvFidSparseMem
      (fun (r, ()) m' => ∃ s' : FullState,
        FullSparseInv nvFidCfg nvFidF0 s' ∧ s'.core.cur_level = 0 ∧ (r = 1#64 ∨ r = 20#64) ∧
        nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvFidCfg nvFidSparseState ⋆ emp) nvFidSparseMem :=
    nvFidMkMem_ok 0#64 nvFidCertScr_len
  refine full_eliminate_m6_fid_wp Γ hDticks hLog hScale hEnter hMin hFwd hBve hReb
    (nvFidCfg.hdr, false, ()) nvFidSparseMem _ _ ?_
  refine ⟨nvFidCfg, nvFidF0, nvFidSparseState, emp, rfl,
    nvFidState_sparseInv nvFidCertScr_len, rfl, hm, fun r s' m' hsp' hcl0' _ hr _ hm' => ?_⟩
  rw [sep_emp] at hm'
  exact ⟨s', hsp', hcl0', hr, nvFidF0_unsat, hm'⟩

end LeanQbe.T.Examples.Kissat.FullFidelityBve
