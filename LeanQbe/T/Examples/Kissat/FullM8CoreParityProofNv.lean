/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProof
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofSplice
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.Bytes
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.OpsLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M8 Core Parity Concrete `Mem 64` Non-Vacuity (`FullM8CoreParityProofNv`)

Genuine non-bailout concrete `Mem 64` UNSAT non-vacuity proofs (`XPost := False`, `0` SAT model
proofs, zero tautological `b = true ∨ b = false` postconditions) exercising actual Rank `#4/#5/#8`
code paths across `m8CoreParityEnv`, `m8SweepV2CoreParityEnv`, and `nvM8DtEnv`:
1. `nv_m8_bve_var_key_mid`, `nv_m8_bve_var_key_cap` (+ `_sw`): exact priority keys from
   `full_bve_var_key_m7_body`, exercising both score (`stable = 1`) and `q_stamp` + `> 2000` clamp
   (`stable = 0`) branches.
2. `nv_m8_probe_dticks_exact_delta`, `nv_m8_probe_dticks_exact_floor`, `nv_m8_probe_dticks_init`,
   `nv_m8_probe_dticks_noninit` (+ `_sw`): `full_probe_dticks_m6_hdr_body` over `288`-word
   `M6HdrExt` (`ext[0] = fullM6HdrMagic`), pinning exact `25M - 10M = 15M` delta, `10M` floor clamp
   on `25M - 20M`, `initial = true` `10M`, and `10M ≤ r.toNat` on `435`/`471`-fn envs.
3. `nv_m8_min_lit_dfs_large_bin_true` (+ `_sw`): 6-step concrete multi-hop DFS executing
   `full_min_lit_dfs_m8_body` over a 4-var arena + binary reason DAG (`root_lit = 3#32`), calling
   `"full_min_mark"` on child `u = 2`, incrementing `search_ticks` to `1#64` on `!is_bin`, and
   pinning exact `r = true`, `s'.core.mrk = [0#8, 0#8, 2#8, 0#8]`, and `FullWitnessInv`.
4. `nv_m8_min_shrink_m6` (+ `_sw`): concrete 18-var non-bailout (`tmp_len = 18 > 16`)
   `full_min_shrink_m6_body` execution across `m8CoreParityEnv` and `m8SweepV2CoreParityEnv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8CoreParity

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics

/-! ## 1. Shared Concrete Heap & 4-Var Reason-DAG UNSAT Fixture -/

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
    (h : bs.length = n ∧ P (bs.At a)) (himp : ∀ m, P m → Q m) : bs.length = n ∧ Q (bs.At a) :=
  ⟨h.1, himp _ h.2⟩

private theorem nv_pad_p (a : BitVec 64) (n : Nat) :
    (List.replicate n (0 : UInt8)).length = n ∧
      region a n ((List.replicate n (0 : UInt8)).At a) :=
  ⟨List.length_replicate, ⟨List.replicate n 0, List.length_replicate, rfl⟩⟩

/-- UNSAT DIMACS-equivalent 4-variable base formula `{(x0), (~x0)}`. -/
def nvM8F0 : CNF Nat := cnfOfClauses [[0], [1]]

/-- Current clause database adding entailed ternary clause `(x1 ∨ ~x2 ∨ ~x0)`. -/
def nvM8FCur : List (List Nat) := [[0], [1], [2, 5, 1]]

theorem nvM8F0_unsat : nvM8F0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [nvM8F0, cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [nvM8F0, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

/-- 4-variable arena geometry (`hdr = 0x2000`, `avail = 2284`, `arena_cap = 6`, `wcap = 1`). -/
def nvM8Cfg : FullCfg :=
  { hdr := 0x2000#64, avail := 2284, mv := 4, max_vars := 4, bva_cap := 0, nc := 2
    arena_cap := 6, wcap := 1, delayed_cap := 0, red_cap := 0, extend_cap := 0, scratch_cap := 0
    hbva := rfl, hmv := by decide, hmaxv := by decide, hnc := by decide, harena := by decide
    hwcap := by decide, hdel := by decide, hred := by decide, hext := by decide, hscr := by decide
    havail_fit := by decide, hsize := by decide }

theorem nvM8Cfg_hdrOk : FullM6HdrCfgOk nvM8Cfg := M6HdrCfgOk_of_le (by decide)

def nvM8Wvec0 : List (BitVec 32) := List.replicate 16 0#32

def nvM8MkScratch (stable ticks : BitVec 64) (qs : List (BitVec 32))
    (sc : List (BitVec 64)) : FullScratch :=
  { heap_len := 0, scinc := 0#64, rel_period := 0#64, rel_limit := 0#64, rel_wait := 0#64
    rel_u := 0#64, rel_v := 0#64, rel_trigger := 0#64, conflicts := 0#64
    learned_lits := 0#64, min_removed := 0#64, delayed_len := 0, stable := stable
    switched := 0#64, mode_count := 0#64, mode_confl_lim := 0#64, mode_tick_lim := 0#64
    mode_saved_ticks := 0#64, search_ticks := ticks, q_first := 0#64, q_last := 0#64
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
    q_prev := List.replicate 4 0#32, q_next := List.replicate 4 0#32, q_stamp := qs
    wsort := List.replicate 8 0#32, work_stk1 := List.replicate 8 0#32
    work_stk2 := List.replicate 8 0#32, tarjan_mark := List.replicate 8 0#32
    tarjan_reach := List.replicate 8 0#32, score := sc, sim_sig := List.replicate 4 0#64
    glue_used := List.replicate 64 0#32, last_learned := List.replicate 16 0xFFFFFFFF#32
    delayed := [], red_refs := [], extend_stk := [], scratch_buf := [] }

def nvM8MkCore (wvec : List (BitVec 32)) : FullCoreState :=
  { d_cur := 0#64, d_val := 0#64, cur_vars := 4, unassigned := 0#64
    arena_len := 6, wlen := 1, wusable := 0#64, arena_garbage := 0#64
    first_reducible := 0#64, num_irred := 1#64, num_redundant := 0#64, num_binary := 1#64
    unflushed := 0#64, probing := 0#64, trail_end := 4, propagated := 0
    cur_level := 2, fuel := 0#64, confl_ref := 0#64, confl_type := 0#64
    confl_lit0 := 0#64, confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0
    min_clr_len := 0, min_clr_full := 0#64, oom := 0#64, dense_mode := 0#64
    inconsistent := 0#64
    vals := [1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8]
    lit_mark := List.replicate 8 0#8, mrk := List.replicate 4 0#8
    flags := List.replicate 4 0#32, lvl := [0#32, 1#32, 1#32, 2#32]
    rsns := [0xFFFFFFFF#32, 0#32, 0x80000001#32, 0xFFFFFFFF#32]
    trl := [0#32, 4#32, 2#32, 6#32], trail_pos := [0#32, 2#32, 1#32, 3#32]
    tmp := List.replicate 4 0#32, min_clr := List.replicate 4 0#32
    frame_trail := [0#32, 1#32, 3#32, 4#32, 4#32]
    frame_dec := [0#32, 4#32, 6#32, 0#32, 0#32], wvec := wvec
    repr := List.replicate 8 0#32, min_stk := List.replicate 10 0#32
    arena := [0x00200000#32, 0#32, 3#32, 2#32, 5#32, 1#32], wstk := [0#32] }

def nvM8MkState (stable ticks : BitVec 64) (wvec qs : List (BitVec 32))
    (sc : List (BitVec 64)) : FullState :=
  { core := nvM8MkCore wvec, scratch := nvM8MkScratch stable ticks qs sc }

private theorem nvM8Mk_lengths {stable ticks : BitVec 64} {wvec qs : List (BitVec 32)}
    {sc : List (BitVec 64)} (hw : wvec.length = 16) (hqs : qs.length = 4)
    (hsc : sc.length = 4) : (nvM8MkState stable ticks wvec qs sc).LengthsOk nvM8Cfg := by
  dsimp only [nvM8MkState, nvM8MkCore, nvM8MkScratch, nvM8Cfg]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by simpa using hw, rfl, rfl, rfl, rfl,
    Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
    Nat.le_refl _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hqs, rfl, rfl, rfl, rfl, rfl, hsc, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl⟩⟩

private def nvM8BlkHdr (stable ticks : BitVec 64) (wvec qs : List (BitVec 32))
    (sc : List (BitVec 64)) : List UInt8 :=
  let c := nvM8Cfg; let s := nvM8MkState stable ticks wvec qs sc
  bytes64 [BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc, s.core.d_cur, s.core.d_val] ++
    bytes64 (Full.hdrTailWords c s)

private def nvM8BlkBytes (k : FullCoreState) (sc : FullScratch) : List UInt8 :=
  (bytesOf (t := i8) k.vals ++ List.replicate 0 0) ++
  (bytesOf (t := i8) sc.walk_vals ++ List.replicate 0 0) ++
  (bytesOf (t := i8) k.lit_mark ++ List.replicate 0 0) ++
  (bytesOf (t := i8) k.mrk ++ List.replicate 4 0) ++
  (bytesOf (t := i8) sc.phases ++ List.replicate 4 0) ++
  (bytesOf (t := i8) sc.phases_target ++ List.replicate 4 0) ++
  (bytesOf (t := i8) sc.phases_best ++ List.replicate 4 0) ++
  (bytesOf (t := i8) sc.walk_best ++ List.replicate 4 0)

private def nvM8BlkU32A (k : FullCoreState) : List UInt8 :=
  (bytesOf (t := i32) k.flags ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.lvl ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.rsns ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.trl ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.trail_pos ++ List.replicate 8 0)

private def nvM8BlkU32B (k : FullCoreState) (sc : FullScratch) : List UInt8 :=
  (bytesOf (t := i32) k.tmp ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.heap ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.pos ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.min_clr ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.shrink_stk ++ List.replicate 8 0)

private def nvM8BlkU32C (k : FullCoreState) (sc : FullScratch) : List UInt8 :=
  (bytesOf (t := i32) sc.q_prev ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.q_next ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.q_stamp ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.frame_trail ++ List.replicate 4 0) ++
  (bytesOf (t := i32) k.frame_dec ++ List.replicate 4 0)

private def nvM8BlkWvec (k : FullCoreState) (sc : FullScratch) : List UInt8 :=
  bytesOf (t := i32) k.wvec ++ bytesOf (t := i32) k.repr ++
  bytesOf (t := i32) sc.wsort ++ bytesOf (t := i32) sc.work_stk1 ++
  bytesOf (t := i32) sc.work_stk2 ++ bytesOf (t := i32) sc.tarjan_mark ++
  bytesOf (t := i32) sc.tarjan_reach ++ bytes64 sc.score ++ bytes64 sc.sim_sig

private def nvM8BlkTail (k : FullCoreState) (sc : FullScratch) : List UInt8 :=
  bytesOf (t := i32) k.min_stk ++ bytesOf (t := i32) sc.glue_used ++
  bytesOf (t := i32) sc.last_learned ++ bytesOf (t := i32) k.arena ++
  bytesOf (t := i32) k.wstk ++ bytesOf (t := i32) sc.delayed ++
  bytesOf (t := i32) sc.red_refs ++ bytesOf (t := i32) sc.extend_stk ++
  bytesOf (t := i32) sc.scratch_buf ++ List.replicate 0 0

def nvM8MkBytes (stable ticks : BitVec 64) (wvec qs : List (BitVec 32))
    (sc : List (BitVec 64)) : List UInt8 :=
  let s := nvM8MkState stable ticks wvec qs sc
  nvM8BlkHdr stable ticks wvec qs sc ++ nvM8BlkBytes s.core s.scratch ++
    nvM8BlkU32A s.core ++ nvM8BlkU32B s.core s.scratch ++ nvM8BlkU32C s.core s.scratch ++
    nvM8BlkWvec s.core s.scratch ++ nvM8BlkTail s.core s.scratch

def nvM8MkMem (stable ticks : BitVec 64) (wvec qs : List (BitVec 32))
    (sc : List (BitVec 64)) : Mem 64 :=
  (nvM8MkBytes stable ticks wvec qs sc).At nvM8Cfg.hdr

private theorem nvM8MkBytes_len (stable ticks : BitVec 64) (wvec qs : List (BitVec 32))
    (sc : List (BitVec 64)) (hw : wvec.length = 16) (hqs : qs.length = 4)
    (hsc : sc.length = 4) : (nvM8MkBytes stable ticks wvec qs sc).length = 2284 := by
  simp only [nvM8MkBytes, nvM8BlkHdr, nvM8BlkBytes, nvM8BlkU32A, nvM8BlkU32B, nvM8BlkU32C,
    nvM8BlkWvec, nvM8BlkTail, nvM8MkState, nvM8MkCore, nvM8MkScratch, nvM8Cfg, List.length_append,
    bytes64_length, bytesOf_length, Full.hdrTailWords_length, List.length_replicate,
    List.length_cons, List.length_nil, Ty.bytes, Ty.size, i8, i32, hw, hqs, hsc]

private theorem nvM8MkMem_ok_pair (stable ticks : BitVec 64) (wvec qs : List (BitVec 32))
    (sc : List (BitVec 64)) (hw : wvec.length = 16) (hqs : qs.length = 4)
    (hsc : sc.length = 4) :
    (nvM8MkBytes stable ticks wvec qs sc).length = 2284 ∧
      FullMem nvM8Cfg (nvM8MkState stable ticks wvec qs sc)
        (nvM8MkMem stable ticks wvec qs sc) := by
  let c := nvM8Cfg; let s := nvM8MkState stable ticks wvec qs sc
  have hv0 : valsBytes c.max_vars - 2 * c.max_vars = 0 := by decide
  have h2m : 2 * c.max_vars = 8 := by decide
  have hm4 : markBytes c.max_vars - c.max_vars = 4 := by decide
  have hm4v : c.max_vars = 4 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * c.max_vars = 8 := by decide
  have h4m : 4 * c.max_vars = 16 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 4 := by decide
  have h4p : 4 * (c.max_vars + 1) = 20 := by decide
  have hsl : c.slack = 0 := by decide
  have hHdr : (nvM8BlkHdr stable ticks wvec qs sc).length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        array64 (c.hdr + 32) (Full.hdrTailWords c s))
        ((nvM8BlkHdr stable ticks wvec qs sc).At c.hdr) :=
    nv_join_pair
      ⟨rfl, dimacsState_bytes c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val⟩
      (nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide))
      rfl (by rw [bytes64_length]; simp only [List.length_cons, List.length_nil]; decide)
  have hBytes : (nvM8BlkBytes s.core s.scratch).length = 64 ∧
      ((array (t := i8) c.pVals s.core.vals ⋆ array (t := i8) c.pLitMark s.core.lit_mark ⋆
          array (t := i8) c.pMark s.core.mrk) ⋆
        FullScrByteArrs c s.scratch ⋆ c.padBytes)
        ((nvM8BlkBytes s.core s.scratch).At c.pVals) := by
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
  have hU32A : (nvM8BlkU32A s.core).length = 120 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        ((nvM8BlkU32A s.core).At c.pFlags) := by
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
  have hU32B : (nvM8BlkU32B s.core s.scratch).length = 120 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pHeap s.scratch.heap ⋆
        array (t := i32) c.pPos s.scratch.pos ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
        array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        ((nvM8BlkU32B s.core s.scratch).At c.pTmp) := by
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
  have hU32C : (nvM8BlkU32C s.core s.scratch).length = 120 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        ((nvM8BlkU32C s.core s.scratch).At c.pQPrev) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 16 8 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 16 8 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 16 8
      (by change 4 * qs.length = 16; omega) (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 20 4
      rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 20 4
      rfl (by decide)
    have j12 := nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := nv_join_pair j123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair j1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu8, hu4, h4m, h4p]; exact sep_ac hm
  have hWvec : (nvM8BlkWvec s.core s.scratch).length = 320 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        ((nvM8BlkWvec s.core s.scratch).At c.pWvec) := by
    have h1 := nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 64
      (by change 4 * wvec.length = 64; omega) (by decide)
    have h2 := nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 32 rfl (by decide)
    have h3 := nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 32 rfl (by decide)
    have h4 := nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 32 rfl (by decide)
    have h5 := nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 32 rfl (by decide)
    have h6 := nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 32 rfl
      (by decide)
    have h7 := nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 32 rfl
      (by decide)
    have h8 := nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 32
      (by change 8 * sc.length = 32; omega) (by decide)
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
  have hTail : (nvM8BlkTail s.core s.scratch).length = 388 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        ((nvM8BlkTail s.core s.scratch).At c.pMinStk) := by
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
    have h9 := nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 0 rfl
      (by decide)
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

private theorem nvM8MkMem_ok {stable ticks : BitVec 64} {wvec qs : List (BitVec 32)}
    {sc : List (BitVec 64)} (hw : wvec.length = 16) (hqs : qs.length = 4)
    (hsc : sc.length = 4) :
    (FullMem nvM8Cfg (nvM8MkState stable ticks wvec qs sc) ⋆ emp)
      (nvM8MkMem stable ticks wvec qs sc) := by
  rw [sep_emp]; exact (nvM8MkMem_ok_pair stable ticks wvec qs sc hw hqs hsc).2

private theorem nvM8_entails_0 :
    (cnfOfClauses nvM8FCur).EntailsClause (cnfClause [0]) := by
  rw [CNF.entails_clause_def]; intro α hα
  exact (CNF.sat_iff_all_mem_sat.mp hα) _
    (CNF.Internal.mem_iff.mpr (by simp [nvM8FCur, cnfOfClauses]))

private theorem nvM8_entails_251 :
    (cnfOfClauses nvM8FCur).EntailsClause (cnfClause [2, 5, 1]) := by
  rw [CNF.entails_clause_def]; intro α hα
  exact (CNF.sat_iff_all_mem_sat.mp hα) _
    (CNF.Internal.mem_iff.mpr (by simp [nvM8FCur, cnfOfClauses]))

private theorem nvM8_entails_41 :
    (cnfOfClauses nvM8FCur).EntailsClause (cnfClause [4, 1]) := by
  rw [CNF.entails_clause_def]; intro α hα
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [nvM8FCur, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h1 ⊢
  obtain ⟨lit, hm, heq⟩ := h1
  refine ⟨lit, ?_, heq⟩
  rw [mem_cnfClause_iff] at hm ⊢; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
  exact Or.inr hm

private theorem nvM8Base_witness :
    FullWitnessInv nvM8Cfg nvM8F0 nvM8FCur (nvM8MkCore nvM8Wvec0) := by
  have hrefs : fullArenaClauseRefsCore (nvM8MkCore nvM8Wvec0) = [0] := rfl
  have hsz0 : fullArenaClauseSizeCore (nvM8MkCore nvM8Wvec0) 0 = 3 := rfl
  have hgarb0 : fullArenaClauseGarbCore (nvM8MkCore nvM8Wvec0) 0 = false := rfl
  have hlits0 : fullArenaClauseLitsCore (nvM8MkCore nvM8Wvec0) 0 = [2, 5, 1] := rfl
  have hnxt0 : fullArenaNextOff (nvM8MkCore nvM8Wvec0).arena 6 0 = 6 := by decide
  have hcv : (nvM8MkCore nvM8Wvec0).cur_vars = 4 := rfl
  have hte : (nvM8MkCore nvM8Wvec0).trail_end = 4 := rfl
  have hcl : (nvM8MkCore nvM8Wvec0).cur_level = 2 := rfl
  have hdm : (nvM8MkCore nvM8Wvec0).dense_mode = 0#64 := rfl
  have hext : ExtUnsatSound nvM8F0 4 nvM8FCur := by
    refine ⟨(varsBoundedBool_iff 4 nvM8FCur).mp rfl, fun hu => ?_⟩
    rw [CNF.unsat_iff_not_sat] at hu ⊢
    intro α hα
    exact hu α ((cnf_sat_cnfOfClauses_iff α nvM8FCur).mpr fun cl hcl => by
      simp only [nvM8FCur, List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl | rfl
      · exact ((cnf_sat_cnfOfClauses_iff α [[0], [1]]).mp (by simpa [nvM8F0] using hα)) [0]
          List.mem_cons_self
      · exact ((cnf_sat_cnfOfClauses_iff α [[0], [1]]).mp (by simpa [nvM8F0] using hα)) [1]
          (List.mem_cons_of_mem _ List.mem_cons_self)
      · have hs1 := ((cnf_sat_cnfOfClauses_iff α [[0], [1]]).mp (by simpa [nvM8F0] using hα))
          [1] (List.mem_cons_of_mem _ List.mem_cons_self)
        rw [CNF.Clause.sat_iff_exists_mem_eq] at hs1 ⊢
        obtain ⟨lit, hm, he⟩ := hs1
        refine ⟨lit, ?_, he⟩
        rw [mem_cnfClause_iff] at hm ⊢
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
        exact Or.inr (Or.inr hm))
  have har : FullArenaClausesInv nvM8Cfg nvM8FCur (nvM8MkCore nvM8Wvec0) := by
    refine ⟨Or.inr (by decide), fun r hr => ?_, fun r hr hsh => ?_, fun r hr _ l hl => ?_,
      fun r hr _ => ?_⟩
    · have harl : (nvM8MkCore nvM8Wvec0).arena_len = 6 := rfl
      rw [hrefs, List.mem_singleton] at hr; subst hr
      rw [harl, hsz0, hnxt0]; refine ⟨by decide, by decide, by decide, by decide, Or.inl rfl⟩
    · rw [hrefs, List.mem_singleton] at hr; subst hr; exact absurd rfl hsh
    · rw [hrefs, List.mem_singleton] at hr; subst hr; rw [hlits0] at hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl <;> decide
    · rw [hrefs, List.mem_singleton] at hr; subst hr; rw [hlits0]; exact nvM8_entails_251
  have hwat : ModeWatchesInv nvM8FCur (nvM8MkCore nvM8Wvec0) := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices
      (fun l hl => (by decide : ∀ q : Fin 8,
        fullWatchOffCore (nvM8MkCore nvM8Wvec0) q.1 +
        fullWatchSizeCore (nvM8MkCore nvM8Wvec0) q.1 ≤ 1) ⟨l, hl⟩)
      (fun l hl hp => absurd hp (by
        have hz := (by decide : ∀ q : Fin 8,
          fullWatchSizeCore (nvM8MkCore nvM8Wvec0) q.1 = 0) ⟨l, hl⟩
        dsimp only at hz; omega))
      (fun l1 _ h1 _ _ hp => absurd hp (by
        have hz := (by decide : ∀ q : Fin 8,
          fullWatchSizeCore (nvM8MkCore nvM8Wvec0) q.1 = 0) ⟨l1, h1⟩
        dsimp only at hz; omega))
      (fun l hl => by
        have hws : fullWatchSizeCore (nvM8MkCore nvM8Wvec0) l = 0 := (by decide : ∀ q : Fin 8,
          fullWatchSizeCore (nvM8MkCore nvM8Wvec0) q.1 = 0) ⟨l, hl⟩
        have hwo : fullWatchOffCore (nvM8MkCore nvM8Wvec0) l = 0 := (by decide : ∀ q : Fin 8,
          fullWatchOffCore (nvM8MkCore nvM8Wvec0) q.1 = 0) ⟨l, hl⟩
        rw [hwo, hws]; exact WatchSliceOk.empty)
  exact
    { ext_sound := hext
      inconsistent_sound := fun h => absurd rfl h
      arena := har
      watches := hwat
      cur_level_le := by decide
      trail_lits_lt := fun i hi => (by decide : ∀ q : Fin 4,
        ((nvM8MkCore nvM8Wvec0).trl[q.1]?.getD 0#32).toNat < 8) ⟨i, hi⟩
      trail_vars_nodup := fun i j hi hj heq => congrArg Fin.val ((by decide : ∀ a b : Fin 4,
        ((nvM8MkCore nvM8Wvec0).trl[a.1]?.getD 0#32).toNat / 2 =
        ((nvM8MkCore nvM8Wvec0).trl[b.1]?.getD 0#32).toNat / 2 → a = b) ⟨i, hi⟩ ⟨j, hj⟩ heq)
      vals_domain := fun l hl => (by decide : ∀ q : Fin 8,
        let v := (nvM8MkCore nvM8Wvec0).vals[q.1]?.getD 0#8
        v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) ⟨l, hl⟩
      vals_true_iff := fun l hl => by
        refine ⟨fun hv => ?_, ?_⟩
        · have hc := (by decide : ∀ q : Fin 8,
            (nvM8MkCore nvM8Wvec0).vals[q.1]?.getD 0#8 = 1#8 →
            ∃ i : Fin 4, ((nvM8MkCore nvM8Wvec0).trl[i.1]?.getD 0#32).toNat = q.1)
            ⟨l, hl⟩ hv
          exact ⟨hc.choose.1, hc.choose.2, hc.choose_spec⟩
        · rintro ⟨i, hi, htr⟩
          have hc := (by decide : ∀ q : Fin 4,
            (nvM8MkCore nvM8Wvec0).vals[((nvM8MkCore nvM8Wvec0).trl[q.1]?.getD 0#32).toNat]?.getD
              0#8 = 1#8) ⟨i, hi⟩
          rw [← htr]; exact hc
      vals_false_iff := fun l hl => by
        refine ⟨fun hv => ?_, ?_⟩
        · have hc := (by decide : ∀ q : Fin 8,
            (nvM8MkCore nvM8Wvec0).vals[q.1]?.getD 0#8 = 0xFF#8 →
            ∃ i : Fin 4, ((nvM8MkCore nvM8Wvec0).trl[i.1]?.getD 0#32).toNat = q.1 ^^^ 1)
            ⟨l, hl⟩ hv
          exact ⟨hc.choose.1, hc.choose.2, hc.choose_spec⟩
        · rintro ⟨i, hi, htr⟩
          have hc := (by decide : ∀ q : Fin 4,
            (nvM8MkCore nvM8Wvec0).vals[((nvM8MkCore nvM8Wvec0).trl[q.1]?.getD
              0#32).toNat ^^^ 1]?.getD 0#8 = 0xFF#8) ⟨i, hi⟩
          have hl_eq : l = ((nvM8MkCore nvM8Wvec0).trl[i]?.getD 0#32).toNat ^^^ 1 := by
            rw [htr, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
          rw [hl_eq]; exact hc
      lvl_le := fun i hi => (by decide : ∀ q : Fin 4,
        ((nvM8MkCore nvM8Wvec0).lvl[((nvM8MkCore nvM8Wvec0).trl[q.1]?.getD
          0#32).toNat / 2]?.getD 0#32).toNat ≤ 2) ⟨i, hi⟩
      dec_earliest := fun i j hi hj hlv hdec => (by decide : ∀ a b : Fin 4,
        ((nvM8MkCore nvM8Wvec0).lvl[((nvM8MkCore nvM8Wvec0).trl[a.1]?.getD
          0#32).toNat / 2]?.getD 0#32).toNat =
        ((nvM8MkCore nvM8Wvec0).lvl[((nvM8MkCore nvM8Wvec0).trl[b.1]?.getD
          0#32).toNat / 2]?.getD 0#32).toNat →
        0 < ((nvM8MkCore nvM8Wvec0).lvl[((nvM8MkCore nvM8Wvec0).trl[b.1]?.getD
          0#32).toNat / 2]?.getD 0#32).toNat ∧
        (nvM8MkCore nvM8Wvec0).rsns[((nvM8MkCore nvM8Wvec0).trl[b.1]?.getD
          0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 → b.1 ≤ a.1)
        ⟨i, hi⟩ ⟨j, hj⟩ hlv hdec
      levels_inhabited := fun L h1 h2 => by
        have hc := (by decide : ∀ q : Fin 3, 1 ≤ q.1 → q.1 ≤ 2 →
          ∃ i : Fin 4, ((nvM8MkCore nvM8Wvec0).lvl[((nvM8MkCore nvM8Wvec0).trl[i.1]?.getD
            0#32).toNat / 2]?.getD 0#32).toNat = q.1) ⟨L, by omega⟩ h1 h2
        exact ⟨hc.choose.1, hc.choose.2, hc.choose_spec⟩
      level0_sound := fun i hi hl0 => by
        rw [hte] at hi; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
        · exact nvM8_entails_0
        · cases hl0
        · cases hl0
        · cases hl0
      trail_pos_inv := fun i hi => (by decide : ∀ q : Fin 4,
        ((nvM8MkCore nvM8Wvec0).trail_pos[((nvM8MkCore nvM8Wvec0).trl[q.1]?.getD
          0#32).toNat / 2]?.getD 0#32).toNat = q.1) ⟨i, hi⟩
      level0_rsn_none := fun i hi hl0 => (by decide : ∀ q : Fin 4,
        ((nvM8MkCore nvM8Wvec0).lvl[((nvM8MkCore nvM8Wvec0).trl[q.1]?.getD
          0#32).toNat / 2]?.getD 0#32).toNat = 0 →
        (nvM8MkCore nvM8Wvec0).rsns[((nvM8MkCore nvM8Wvec0).trl[q.1]?.getD
          0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ⟨i, hi⟩ hl0
      frame_trail_lt := fun L hL => (by decide : ∀ q : Fin 3,
        ((nvM8MkCore nvM8Wvec0).frame_trail[q.1]?.getD 0#32).toNat ≤ 4) ⟨L, by omega⟩
      frame_trail_mono := fun L1 L2 h12 hL2 => (by decide : ∀ a b : Fin 3, a.1 ≤ b.1 →
        ((nvM8MkCore nvM8Wvec0).frame_trail[a.1]?.getD 0#32).toNat ≤
        ((nvM8MkCore nvM8Wvec0).frame_trail[b.1]?.getD 0#32).toNat)
        ⟨L1, by omega⟩ ⟨L2, by omega⟩ h12
      frame_trail_before_lt := fun L h1 h2 i hi =>
        (by decide : ∀ q : Fin 3, 1 ≤ q.1 → ∀ j : Fin 4,
          j.1 < ((nvM8MkCore nvM8Wvec0).frame_trail[q.1]?.getD 0#32).toNat →
          ((nvM8MkCore nvM8Wvec0).lvl[((nvM8MkCore nvM8Wvec0).trl[j.1]?.getD
            0#32).toNat / 2]?.getD 0#32).toNat < q.1)
          ⟨L, by omega⟩ h1 ⟨i, by
            have hb := (by decide : ∀ q : Fin 3,
              ((nvM8MkCore nvM8Wvec0).frame_trail[q.1]?.getD 0#32).toNat ≤ 4) ⟨L, by omega⟩
            dsimp only at hb; omega⟩ hi
      frame_dec_lt := fun L h1 h2 => (by decide : ∀ q : Fin 3, 1 ≤ q.1 →
        ((nvM8MkCore nvM8Wvec0).frame_dec[q.1]?.getD 0#32).toNat < 8) ⟨L, by omega⟩ h1
      reason_inv := fun idx hidx hne => by
        rw [hte] at hidx
        rcases (by omega : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3) with rfl | rfl | rfl | rfl
        · exact absurd rfl hne
        · refine ⟨by decide, nvM8_entails_41, 0, by decide, rfl, by decide⟩
        · have hb : ¬ ((0#32 : BitVec 32) &&& 0x80000000#32) ≠ 0#32 := by decide
          rw [show (nvM8MkCore nvM8Wvec0).rsns[((nvM8MkCore nvM8Wvec0).trl[2]?.getD 0#32).toNat
            / 2]?.getD 0xFFFFFFFF#32 = 0#32 from rfl, ite_eq_right hb]
          refine ⟨hrefs ▸ List.mem_cons_self, hgarb0, fun q hq => ?_⟩
          rw [show (0#32 : BitVec 32).toNat = 0 from rfl, hlits0] at hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr ⟨1, by decide, rfl, by decide⟩
          · exact Or.inr ⟨0, by decide, rfl, by decide⟩
        · exact absurd rfl hne
      reason_lit_mem := fun idx hidx hne hlg => by
        rw [hte] at hidx
        rcases (by omega : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3) with rfl | rfl | rfl | rfl
        · exact absurd rfl hne
        · exact absurd hlg (by decide)
        · rw [show (nvM8MkCore nvM8Wvec0).rsns[((nvM8MkCore nvM8Wvec0).trl[2]?.getD 0#32).toNat
            / 2]?.getD 0xFFFFFFFF#32 = 0#32 from rfl,
            show (0#32 : BitVec 32).toNat = 0 from rfl, hlits0]
          exact List.mem_cons_self
        · exact absurd rfl hne }

/-! ## 2. `full_bve_var_key_m7` Concrete UNSAT NV (`stable` & `q_stamp` + `> 2000` Clamp) -/

def nvM8KeyMidWvec : List (BitVec 32) := (nvM8Wvec0.set 5 1500#32).set 7 1600#32
def nvM8KeyMidScore : List (BitVec 64) := (List.replicate 4 0#64).set 1 (5#64 <<< 32)
def nvM8KeyMidState : FullState :=
  nvM8MkState 1#64 0#64 nvM8KeyMidWvec (List.replicate 4 0#32) nvM8KeyMidScore
def nvM8KeyMidMem : Mem 64 :=
  nvM8MkMem 1#64 0#64 nvM8KeyMidWvec (List.replicate 4 0#32) nvM8KeyMidScore

def nvM8KeyCapWvec : List (BitVec 32) := (nvM8Wvec0.set 5 2500#32).set 7 2500#32
def nvM8KeyCapQs : List (BitVec 32) := (List.replicate 4 0#32).set 1 7#32
def nvM8KeyCapState : FullState :=
  nvM8MkState 0#64 0#64 nvM8KeyCapWvec nvM8KeyCapQs (List.replicate 4 0#64)
def nvM8KeyCapMem : Mem 64 :=
  nvM8MkMem 0#64 0#64 nvM8KeyCapWvec nvM8KeyCapQs (List.replicate 4 0#64)

private theorem nvM8KeyMid_exec (Γ : Env) :
    Func.wp Γ full_bve_var_key_m7_body (nvM8Cfg.hdr, 1#32, ()) nvM8KeyMidMem
      (fun (r, ()) m' =>
        r = ((1607100#64 <<< 32) ||| 0xFFFFFFFA#64) ∧
        nvM8F0.Unsat ∧ FullMem nvM8Cfg nvM8KeyMidState m')
      (fun _ _ _ _ => False) := by
  have hlen := nvM8Mk_lengths (stable := 1#64) (ticks := 0#64)
    (wvec := nvM8KeyMidWvec) (qs := List.replicate 4 0#32) (sc := nvM8KeyMidScore)
    rfl rfl rfl
  have hm : (FullMem nvM8Cfg nvM8KeyMidState ⋆ emp) nvM8KeyMidMem :=
    nvM8MkMem_ok rfl rfl rfl
  have hwv1 : (((1#32 : BitVec 32).setWidth 64 <<< (2 : Nat)) + 1#64).toNat <
      nvM8KeyMidState.core.wvec.length := by decide
  have hwv3 : (((1#32 : BitVec 32).setWidth 64 <<< (2 : Nat)) + 3#64).toNat <
      nvM8KeyMidState.core.wvec.length := by decide
  have h1sc : ((1#32 : BitVec 32).setWidth 64).toNat < nvM8KeyMidState.scratch.score.length := by
    decide
  have h1qs : ((1#32 : BitVec 32).setWidth 64).toNat < nvM8KeyMidState.scratch.q_stamp.length := by
    decide
  have h_sc1 : ∀ i h, i = (BitVec.ofNat 64 1).toNat →
      nvM8KeyMidState.scratch.score[i]'h >>> 32 = 5#64 := fun i hi heq => by
    subst heq
    have hv : nvM8KeyMidState.scratch.score[(BitVec.ofNat 64 1).toNat]'hi = 5#64 <<< 32 :=
      Option.some.inj (by rw [← List.getElem?_eq_getElem hi]; decide)
    rw [hv]; decide
  have h_wv7 : ∀ i h, i = (BitVec.ofNat 64 1 <<< 2 + 3).toNat →
      BitVec.setWidth 64 (nvM8KeyMidState.core.wvec[i]'h) = 1600#64 := fun i hi heq => by
    subst heq
    have hv : nvM8KeyMidState.core.wvec[(BitVec.ofNat 64 1 <<< 2 + 3).toNat]'hi = 1600#32 :=
      Option.some.inj (by rw [← List.getElem?_eq_getElem hi]; decide)
    rw [hv]; decide
  have h_wv5 : ∀ i h, i = (BitVec.ofNat 64 1 <<< 2 + 1).toNat →
      BitVec.setWidth 64 (nvM8KeyMidState.core.wvec[i]'h) = 1500#64 := fun i hi heq => by
    subst heq
    have hv : nvM8KeyMidState.core.wvec[(BitVec.ofNat 64 1 <<< 2 + 1).toNat]'hi = 1500#32 :=
      Option.some.inj (by rw [← List.getElem?_eq_getElem hi]; decide)
    rw [hv]; decide
  unfold Func.wp full_bve_var_key_m7_body
  c0_hsteps_nogrp
  · exfalso; simp only [nvM8KeyMidState, nvM8MkState, nvM8MkCore] at hc
    revert hc; decide
  · c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
      (fun x => x = 1500#64)
      (fun _ _ hx => by
        subst hx; c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
          (fun x => x = 1600#64)
          (fun _ _ hy => by
            subst hy; c0_hsteps_nogrp
            refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
              (fun x => x = 5#64)
              (fun _ _ hz => by
                subst hz; c0_hsteps!
                rw [sep_emp] at hm
                exact ⟨by decide, nvM8F0_unsat, hm⟩)
              (fun _ hJr => by
                c0_hsplit
                · c0_hsteps!; exact hJr _ (h_sc1 _ _ rfl)
                · exfalso
                  simp only [nvM8KeyMidState, nvM8MkState, nvM8MkScratch] at hc
                  revert hc; decide))
          (fun _ hJn => by
            c0_hsplit
            · exfalso
              have h7 : ∀ h, nvM8KeyMidState.core.wvec[((BitVec.ofNat 64 1 <<< 2).toNat +
                  (3 : BitVec 64).toNat) % 2 ^ 64]'h = 1600#32 := fun _ => rfl
              rw [h7] at hc; revert hc; decide
            · c0_hsteps!; exact hJn _ (h_wv7 _ _ rfl)))
      (fun _ hJp => by
        c0_hsplit
        · exfalso
          have h5 : ∀ h, nvM8KeyMidState.core.wvec[((BitVec.ofNat 64 1 <<< 2).toNat +
              (1 : BitVec 64).toNat) % 2 ^ 64]'h = 1500#32 := fun _ => rfl
          rw [h5] at hc; revert hc; decide
        · c0_hsteps!; exact hJp _ (h_wv5 _ _ rfl))

private theorem nvM8KeyCap_exec (Γ : Env) :
    Func.wp Γ full_bve_var_key_m7_body (nvM8Cfg.hdr, 1#32, ()) nvM8KeyCapMem
      (fun (r, ()) m' =>
        r = ((8000#64 <<< 32) ||| 0xFFFFFFF8#64) ∧
        nvM8F0.Unsat ∧ FullMem nvM8Cfg nvM8KeyCapState m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM8Cfg nvM8KeyCapState ⋆ emp) nvM8KeyCapMem :=
    nvM8MkMem_ok rfl rfl rfl
  have hwv1 : (((1#32 : BitVec 32).setWidth 64 <<< (2 : Nat)) + 1#64).toNat <
      nvM8KeyCapState.core.wvec.length := by decide
  have hwv3 : (((1#32 : BitVec 32).setWidth 64 <<< (2 : Nat)) + 3#64).toNat <
      nvM8KeyCapState.core.wvec.length := by decide
  have h1sc : ((1#32 : BitVec 32).setWidth 64).toNat < nvM8KeyCapState.scratch.score.length := by
    decide
  have h1qs : ((1#32 : BitVec 32).setWidth 64).toNat < nvM8KeyCapState.scratch.q_stamp.length := by
    decide
  have h_qs1 : ∀ i h, i = (BitVec.ofNat 64 1).toNat →
      BitVec.setWidth 64 (nvM8KeyCapState.scratch.q_stamp[i]'h) = 7#64 := fun i hi heq => by
    subst heq
    have hv : nvM8KeyCapState.scratch.q_stamp[(BitVec.ofNat 64 1).toNat]'hi = 7#32 :=
      Option.some.inj (by rw [← List.getElem?_eq_getElem hi]; decide)
    rw [hv]; decide
  unfold Func.wp full_bve_var_key_m7_body
  c0_hsteps_nogrp
  · exfalso; simp only [nvM8KeyCapState, nvM8MkState, nvM8MkCore] at hc
    revert hc; decide
  · c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
      (fun x => x = 2000#64)
      (fun _ _ hx => by
        subst hx; c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
          (fun x => x = 2000#64)
          (fun _ _ hy => by
            subst hy; c0_hsteps_nogrp
            refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
              (fun x => x = 7#64)
              (fun _ _ hz => by
                subst hz; c0_hsteps!
                rw [sep_emp] at hm
                exact ⟨by decide, nvM8F0_unsat, hm⟩)
              (fun _ hJr => by
                c0_hsplit
                · exfalso
                  simp only [nvM8KeyCapState, nvM8MkState, nvM8MkScratch] at hc
                  revert hc; decide
                · c0_hsteps!; exact hJr _ (h_qs1 _ _ rfl)))
          (fun _ hJn => by
            c0_hsplit
            · c0_hsteps!; exact hJn _ rfl
            · exfalso
              have h7 : ∀ h, nvM8KeyCapState.core.wvec[((BitVec.ofNat 64 1 <<< 2).toNat +
                  (3 : BitVec 64).toNat) % 2 ^ 64]'h = 2500#32 := fun _ => rfl
              rw [h7] at hc; revert hc; decide))
      (fun _ hJp => by
        c0_hsplit
        · c0_hsteps!; exact hJp _ rfl
        · exfalso
          have h5 : ∀ h, nvM8KeyCapState.core.wvec[((BitVec.ofNat 64 1 <<< 2).toNat +
              (1 : BitVec 64).toNat) % 2 ^ 64]'h = 2500#32 := fun _ => rfl
          rw [h5] at hc; revert hc; decide)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`): `full_bve_var_key_m7` under `m8CoreParityEnv`
with `stable = 1`, `pos = 1500`, `neg = 1600`, `score[1] = 5 << 32` pins exact key
`(1607100#64 <<< 32) ||| 0xFFFFFFFA#64`. -/
theorem nv_m8_bve_var_key_mid :
    Func.wp m8CoreParityEnv full_bve_var_key_m7_body (nvM8Cfg.hdr, 1#32, ()) nvM8KeyMidMem
      (fun (r, ()) m' =>
        r = ((1607100#64 <<< 32) ||| 0xFFFFFFFA#64) ∧
        nvM8F0.Unsat ∧ FullMem nvM8Cfg nvM8KeyMidState m')
      (fun _ _ _ _ => False) :=
  nvM8KeyMid_exec m8CoreParityEnv

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`): `full_bve_var_key_m7` under `m8CoreParityEnv`
with `stable = 0`, `pos = 2500 > 2000`, `neg = 2500 > 2000`, `q_stamp[1] = 7` pins exact clamped key
`(8000#64 <<< 32) ||| 0xFFFFFFF8#64`. -/
theorem nv_m8_bve_var_key_cap :
    Func.wp m8CoreParityEnv full_bve_var_key_m7_body (nvM8Cfg.hdr, 1#32, ()) nvM8KeyCapMem
      (fun (r, ()) m' =>
        r = ((8000#64 <<< 32) ||| 0xFFFFFFF8#64) ∧
        nvM8F0.Unsat ∧ FullMem nvM8Cfg nvM8KeyCapState m')
      (fun _ _ _ _ => False) :=
  nvM8KeyCap_exec m8CoreParityEnv

theorem nv_m8_bve_var_key_mid_sw :
    Func.wp m8SweepV2CoreParityEnv full_bve_var_key_m7_body (nvM8Cfg.hdr, 1#32, ()) nvM8KeyMidMem
      (fun (r, ()) m' =>
        r = ((1607100#64 <<< 32) ||| 0xFFFFFFFA#64) ∧
        nvM8F0.Unsat ∧ FullMem nvM8Cfg nvM8KeyMidState m')
      (fun _ _ _ _ => False) :=
  nvM8KeyMid_exec m8SweepV2CoreParityEnv

theorem nv_m8_bve_var_key_cap_sw :
    Func.wp m8SweepV2CoreParityEnv full_bve_var_key_m7_body (nvM8Cfg.hdr, 1#32, ()) nvM8KeyCapMem
      (fun (r, ()) m' =>
        r = ((8000#64 <<< 32) ||| 0xFFFFFFF8#64) ∧
        nvM8F0.Unsat ∧ FullMem nvM8Cfg nvM8KeyCapState m')
      (fun _ _ _ _ => False) :=
  nvM8KeyCap_exec m8SweepV2CoreParityEnv

/-! ## 3. `full_probe_dticks_m6_hdr` Concrete UNSAT NV (`10M` Floor & Exact `25M - wm0` Delta) -/

def nvM8DtExt (wm0 : BitVec 64) : List (BitVec 64) :=
  ((List.replicate 288 0#64).set 0 fullM6HdrMagic).set 24 wm0

theorem nvM8DtExt_len (wm0 : BitVec 64) : (nvM8DtExt wm0).length = 288 := by
  rw [nvM8DtExt, List.length_set, List.length_set, List.length_replicate]

theorem nvM8DtExt_ok (wm0 : BitVec 64) : M6HdrExtOk (nvM8DtExt wm0) :=
  M6HdrExtOk.of_len (nvM8DtExt_len wm0)

theorem nvM8DtExt_magic (wm0 : BitVec 64) : (nvM8DtExt wm0)[0]? = some fullM6HdrMagic := by
  rw [nvM8DtExt, List.getElem?_set_ne (by decide : 24 ≠ 0)]
  exact List.getElem?_set_self (by rw [List.length_replicate]; omega)

def nvM8DtState (ticks : BitVec 64) : FullState :=
  nvM8MkState 0#64 ticks nvM8Wvec0 (List.replicate 4 0#32) (List.replicate 4 0#64)

def nvM8DtMem (ticks wm0 : BitVec 64) : Mem 64 :=
  (bytes64 (nvM8DtExt wm0) ++
    nvM8MkBytes 0#64 ticks nvM8Wvec0 (List.replicate 4 0#32) (List.replicate 4 0#64)).At
    (nvM8Cfg.hdr - 2304)

private theorem nvM8DtMem_ok (ticks wm0 : BitVec 64) :
    (FullM6HdrMem nvM8Cfg (nvM8DtExt wm0) (nvM8DtState ticks) ⋆ emp)
      (nvM8DtMem ticks wm0) := by
  have hextLen := nvM8DtExt_len wm0
  have hb64 : (bytes64 (nvM8DtExt wm0)).length = 2304 := by rw [bytes64_length, hextLen]
  have hp := nvM8MkMem_ok_pair 0#64 ticks nvM8Wvec0 (List.replicate 4 0#32) (List.replicate 4 0#64)
    rfl rfl rfl
  rw [sep_emp]
  refine fullM6HdrMem_mk
    (nv_sep_append ?_ ?_ (array64_bytes _ _ (by rw [hextLen]; omega)) hp.2)
  · rw [hb64]; decide
  · rw [hb64, hp.1]; omega

def nvM8DtEnsSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ ext[0]? = some fullM6HdrMagic ∧
    s.LengthsOk c ∧ (FullM6HdrMem c ext s ⋆ R) m ∧ Q () m

private theorem nvM8DtEnsSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : nvM8DtEnsSpec xs m Q X) : nvM8DtEnsSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

def nvM8DtGetWmSpec : Spec [i64, i64] [i64] := fun (h, kind, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ ext[0]? = some fullM6HdrMagic ∧
    s.LengthsOk c ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    (kind.toNat < 8 → Q (ext[24 + kind.toNat]?.getD 0#64, ()) m) ∧
    (8 ≤ kind.toNat → Q (0#64, ()) m)

private theorem nvM8DtGetWmSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : nvM8DtGetWmSpec xs m Q X) : nvM8DtGetWmSpec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

def nvM8DtTable : List SpecEntry :=
  [ ⟨"m6_hdr_init", [i64], [], m6HdrInitSpec, true⟩
  , ⟨"m6_ext_ensure_init", [i64], [], nvM8DtEnsSpec, true⟩
  , ⟨"m6_hdr_get_watermark", [i64, i64], [i64], nvM8DtGetWmSpec, true⟩ ]

def nvM8DtEnv : Env := Env.ofTable nvM8DtTable

def nvM8DtModule : LeanQbe.T.Module :=
  { fns :=
      [ ⟨"m6_hdr_init", [i64], [], m6_hdr_init_body⟩
      , ⟨"m6_ext_ensure_init", [i64], [], m6_ext_ensure_init_body⟩
      , ⟨"m6_hdr_get_watermark", [i64, i64], [i64], m6_hdr_get_watermark_body⟩ ]
    externs := []
    exits := [] }

theorem nvM8Dt_moduleOk : ModuleOk nvM8DtEnv nvM8DtModule := by
  have hnd : (nvM8DtTable.map SpecEntry.name).Nodup := by decide
  have hrow1 : ∀ a m Q X, nvM8DtEnsSpec a m Q X →
      nvM8DtEnv "m6_ext_ensure_init" [i64] [] a m Q X :=
    fun _ _ _ _ h => Env.ofTable_of_mem (List.mem_cons_of_mem _ List.mem_cons_self) hnd
      (nvM8DtEnsSpec_monoX (X' := fun _ _ _ _ => False) h)
  have hens : ∀ a m Q X, nvM8DtEnsSpec a m Q X →
      Func.wp nvM8DtEnv m6_ext_ensure_init_body a m Q X := by
    rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, ext, s, R, rfl, hcfg, hext, hmag, hlen, hm, hQ⟩
    have h0 : 0 < ext.length := by rw [hext.len]; omega
    rw [fullM6HdrMem_iff] at hm
    unfold Func.wp m6_ext_ensure_init_body
    c0_hsteps
    · exfalso; rw [List.getElem?_eq_getElem h0, Option.some.injEq] at hmag
      apply hc; simpa [fullM6HdrMagic] using hmag
    · exact hQ
  have hget : ∀ a m Q X, nvM8DtGetWmSpec a m Q X →
      Func.wp nvM8DtEnv m6_hdr_get_watermark_body a m Q X := by
    rintro ⟨h, kind, ⟨⟩⟩ m Q X ⟨c, ext, s, R, rfl, hcfg, hext, hmag, hlen, hm, hQ1, hQ2⟩
    unfold Func.wp m6_hdr_get_watermark_body
    c0_hsteps_nogrp
    · exact hQ2 (by have h8 : (8 : BitVec 64).toNat = 8 := rfl; omega)
    · have hk8 : kind.toNat < 8 := by have h8 : (8 : BitVec 64).toNat = 8 := rfl; omega
      refine wp_call_of_spec _ _ (hrow1 _ _ _ _
        ⟨c, ext, s, R, rfl, hcfg, hext, hmag, hlen, hm, ?_⟩)
      have hl1 : ext.length = 288 := hext.len
      have hidx_eq : ((24 : BitVec 64) + kind).toNat = 24 + kind.toNat := by
        rw [BitVec.toNat_add, show (24 : BitVec 64).toNat = 24 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      have hidx : ((24 : BitVec 64) + kind).toNat < ext.length := by rw [hl1, hidx_eq]; omega
      rw [fullM6HdrMem_iff] at hm
      c0_hsteps
      have hveq : ext[((24 : BitVec 64) + kind).toNat]'hidx =
          ext[24 + kind.toNat]?.getD 0#64 := by
        rw [List.getElem?_eq_getElem (by rw [hl1]; omega), Option.getD_some]
        congr 1
      rw [hveq]
      exact hQ1 hk8
  have htbl : TableImpl nvM8DtEnv nvM8DtModule.fns nvM8DtTable :=
    ⟨SpecEntry.Impl.of (m6_hdr_init_wp nvM8DtEnv),
     SpecEntry.Impl.of hens, SpecEntry.Impl.of hget, trivial⟩
  exact Env.ofTable_moduleOk (by t_kernel_rfl)
    ⟨m6_hdr_init_wf, m6_ext_ensure_init_wf, m6_hdr_get_watermark_wf, trivial⟩ htbl

private theorem nvM8DtExact_exec (ticks wm0 : BitVec 64) :
    Func.wp nvM8DtEnv full_probe_dticks_m6_hdr_body (nvM8Cfg.hdr, false, ()) (nvM8DtMem ticks wm0)
      (fun (r, ()) m' =>
        r = (if 10000000#64 < (if wm0 < ticks then ticks - wm0 else 0#64)
          then (if wm0 < ticks then ticks - wm0 else 0#64) else 10000000#64) ∧
        nvM8F0.Unsat ∧ FullM6HdrMem nvM8Cfg (nvM8DtExt wm0) (nvM8DtState ticks) m')
      (fun _ _ _ _ => False) := by
  have hnd : (nvM8DtTable.map SpecEntry.name).Nodup := by decide
  have hrow2 : ∀ a m Q X, nvM8DtGetWmSpec a m Q X →
      nvM8DtEnv "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X :=
    fun _ _ _ _ h =>
      Env.ofTable_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        hnd (nvM8DtGetWmSpec_monoX (X' := fun _ _ _ _ => False) h)
  have hlen := nvM8Mk_lengths (stable := 0#64) (ticks := ticks) (wvec := nvM8Wvec0)
    (qs := List.replicate 4 0#32) (sc := List.replicate 4 0#64) rfl rfl rfl
  have hm := nvM8DtMem_ok ticks wm0
  unfold Func.wp full_probe_dticks_m6_hdr_body
  c0_hsteps_nogrp
  refine wp_call_of_spec _ _ (hrow2 _ _ _ _ ?_)
  refine ⟨nvM8Cfg, nvM8DtExt wm0, nvM8DtState ticks, emp, rfl, nvM8Cfg_hdrOk,
    nvM8DtExt_ok wm0, nvM8DtExt_magic wm0, hlen, hm, fun _ => ?_, fun hge => absurd hge (by decide)⟩
  have hl0 : ((List.replicate 288 0#64).set 0 fullM6HdrMagic).length = 288 := by
    rw [List.length_set, List.length_replicate]
  have hwm : (nvM8DtExt wm0)[24]?.getD 0#64 = wm0 := by
    rw [nvM8DtExt, List.getElem?_set_self (by rw [hl0]; omega), Option.getD_some]
  have harg0 : (24 + BitVec.toNat (Arg.imm (t := i64) 0).val) = 24 := rfl
  rw [harg0, hwm]
  have hm1_0 := hm
  rw [fullM6HdrMem_iff] at hm
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
    (fun raw => raw = (if wm0 < ticks then ticks - wm0 else 0#64))
    (fun _ _ hraw => by
      subst hraw
      rw [sep_emp] at hm1_0
      c0_hsteps
      · have hlt : 10000000#64 < (if wm0 < ticks then ticks - wm0 else 0#64) := by
          c0_cond hc; exact BitVec.lt_def.mpr hc
        exact ⟨by simp [hlt], nvM8F0_unsat, hm1_0⟩
      · have hle : ¬ 10000000#64 < (if wm0 < ticks then ticks - wm0 else 0#64) := by
          c0_cond hc; exact fun h => hc (BitVec.lt_def.mp h)
        exact ⟨by simp [hle], nvM8F0_unsat, hm1_0⟩)
    (fun _ hJ => by
      c0_hsteps
      · have hlt : wm0 < ticks := by
          c0_cond hc
          exact BitVec.lt_def.mpr (by simpa [nvM8DtState, nvM8MkState, nvM8MkScratch] using hc)
        exact hJ _ (by simp [hlt]; rfl)
      · have hle : ¬ wm0 < ticks := by
          c0_cond hc
          exact fun h => hc
            (by simpa [nvM8DtState, nvM8MkState, nvM8MkScratch] using BitVec.lt_def.mp h)
        exact hJ _ (by simp [hle]))

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`): `full_probe_dticks_m6_hdr` on closed `nvM8DtEnv`
with `search_ticks = 25M`, `wm0 = 10M` pins exact non-floor delta `r = 15000000#64`. -/
theorem nv_m8_probe_dticks_exact_delta :
    Func.wp nvM8DtEnv full_probe_dticks_m6_hdr_body (nvM8Cfg.hdr, false, ())
      (nvM8DtMem 25000000#64 10000000#64)
      (fun (r, ()) m' => r = 15000000#64 ∧ nvM8F0.Unsat ∧
        FullM6HdrMem nvM8Cfg (nvM8DtExt 10000000#64) (nvM8DtState 25000000#64) m')
      (fun _ _ _ _ => False) :=
  wp_mono (fun (r, ()) m' h => ⟨h.1.trans (by decide), h.2⟩) (fun _ _ _ _ => id)
    (full_probe_dticks_m6_hdr_body Val Cont (nvM8Cfg.hdr, false, ())) _
    (nvM8DtExact_exec 25000000#64 10000000#64)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`): `full_probe_dticks_m6_hdr` on closed `nvM8DtEnv`
with `search_ticks = 25M`, `wm0 = 20M` (`raw = 5M`) pins exact `10M` floor clamp
`r = 10000000#64`. -/
theorem nv_m8_probe_dticks_exact_floor :
    Func.wp nvM8DtEnv full_probe_dticks_m6_hdr_body (nvM8Cfg.hdr, false, ())
      (nvM8DtMem 25000000#64 20000000#64)
      (fun (r, ()) m' => r = 10000000#64 ∧ nvM8F0.Unsat ∧
        FullM6HdrMem nvM8Cfg (nvM8DtExt 20000000#64) (nvM8DtState 25000000#64) m')
      (fun _ _ _ _ => False) :=
  wp_mono (fun (r, ()) m' h => ⟨h.1.trans (by decide), h.2⟩) (fun _ _ _ _ => id)
    (full_probe_dticks_m6_hdr_body Val Cont (nvM8Cfg.hdr, false, ())) _
    (nvM8DtExact_exec 25000000#64 20000000#64)

private theorem nvM8ProbeDticksInit_exec (Γ : Env) :
    Func.wp Γ full_probe_dticks_m6_hdr_body (nvM8Cfg.hdr, true, ())
      (nvM8DtMem 25000000#64 10000000#64)
      (fun (r, ()) m' => r = 10000000#64 ∧ nvM8F0.Unsat ∧
        FullM6HdrMem nvM8Cfg (nvM8DtExt 10000000#64) (nvM8DtState 25000000#64) m')
      (fun _ _ _ _ => False) := by
  have hm := nvM8DtMem_ok 25000000#64 10000000#64
  rw [sep_emp] at hm
  unfold Func.wp full_probe_dticks_m6_hdr_body
  c0_hsteps_nogrp
  · exact ⟨rfl, nvM8F0_unsat, hm⟩
  · cases hc

private theorem nvM8ProbeDticksNoninit_exec (Γ : Env)
    (hGetWm : ∀ a m Q X, m6HdrW2aSpec [i64] [i64] a m Q X →
      Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X) :
    Func.wp Γ full_probe_dticks_m6_hdr_body (nvM8Cfg.hdr, false, ())
      (nvM8DtMem 25000000#64 10000000#64)
      (fun (r, ()) m' => ∃ ext' s',
        10000000 ≤ r.toNat ∧ s'.core = (nvM8DtState 25000000#64).core ∧
        s'.LengthsOk nvM8Cfg ∧ M6HdrScratchPres (nvM8DtState 25000000#64) s' ∧
        M6HdrExtOk ext' ∧ nvM8F0.Unsat ∧ FullM6HdrMem nvM8Cfg ext' s' m')
      (fun _ _ _ _ => False) := by
  have hlen := nvM8Mk_lengths (stable := 0#64) (ticks := 25000000#64) (wvec := nvM8Wvec0)
    (qs := List.replicate 4 0#32) (sc := List.replicate 4 0#64) rfl rfl rfl
  have hm := nvM8DtMem_ok 25000000#64 10000000#64
  unfold Func.wp full_probe_dticks_m6_hdr_body
  c0_hsteps_nogrp
  · refine wp_call_of_spec _ _ (hGetWm _ _ _ _ ?_)
    refine m6HdrW2aSpec_of rfl nvM8Cfg_hdrOk (nvM8DtExt_ok 10000000#64) hlen hm
      fun ⟨_raw, ⟨⟩⟩ ext' s' m' hc' hlen' hms' hext' _ hm' => ?_
    have hm'0 := hm'
    rw [sep_emp] at hm'0
    rw [fullM6HdrMem_iff] at hm'
    c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ())) (fun _ => True)
      (fun _ raw _ => by
        c0_hsteps
        · have hlt : 10000000 < raw.toNat := by c0_cond hc; exact hc
          exact ⟨ext', s', by omega, hc', hlen', hms', hext', nvM8F0_unsat, hm'0⟩
        · exact ⟨ext', s', by decide, hc', hlen', hms', hext', nvM8F0_unsat, hm'0⟩)
      (fun _ hJ => by c0_hsteps <;> exact hJ _ trivial)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`): `full_probe_dticks_m6_hdr` (`initial = true`)
on `m8CoreParityEnv` returns exact `10000000#64`. -/
theorem nv_m8_probe_dticks_init :
    Func.wp m8CoreParityEnv full_probe_dticks_m6_hdr_body (nvM8Cfg.hdr, true, ())
      (nvM8DtMem 25000000#64 10000000#64)
      (fun (r, ()) m' => r = 10000000#64 ∧ nvM8F0.Unsat ∧
        FullM6HdrMem nvM8Cfg (nvM8DtExt 10000000#64) (nvM8DtState 25000000#64) m')
      (fun _ _ _ _ => False) :=
  nvM8ProbeDticksInit_exec m8CoreParityEnv

theorem nv_m8_probe_dticks_init_sw :
    Func.wp m8SweepV2CoreParityEnv full_probe_dticks_m6_hdr_body (nvM8Cfg.hdr, true, ())
      (nvM8DtMem 25000000#64 10000000#64)
      (fun (r, ()) m' => r = 10000000#64 ∧ nvM8F0.Unsat ∧
        FullM6HdrMem nvM8Cfg (nvM8DtExt 10000000#64) (nvM8DtState 25000000#64) m')
      (fun _ _ _ _ => False) :=
  nvM8ProbeDticksInit_exec m8SweepV2CoreParityEnv

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`): `full_probe_dticks_m6_hdr` (`initial = false`)
on `m8CoreParityEnv` proves non-tautological `10000000 ≤ r.toNat`, valid `M6HdrExtOk`,
`s'.core` preservation, and `nvM8F0.Unsat`. -/
theorem nv_m8_probe_dticks_noninit :
    Func.wp m8CoreParityEnv full_probe_dticks_m6_hdr_body (nvM8Cfg.hdr, false, ())
      (nvM8DtMem 25000000#64 10000000#64)
      (fun (r, ()) m' => ∃ ext' s',
        10000000 ≤ r.toNat ∧ s'.core = (nvM8DtState 25000000#64).core ∧
        s'.LengthsOk nvM8Cfg ∧ M6HdrScratchPres (nvM8DtState 25000000#64) s' ∧
        M6HdrExtOk ext' ∧ nvM8F0.Unsat ∧ FullM6HdrMem nvM8Cfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nvM8ProbeDticksNoninit_exec m8CoreParityEnv fun _ _ _ _ hs => m8CoreParityEnv_getWatermark hs

theorem nv_m8_probe_dticks_noninit_sw :
    Func.wp m8SweepV2CoreParityEnv full_probe_dticks_m6_hdr_body (nvM8Cfg.hdr, false, ())
      (nvM8DtMem 25000000#64 10000000#64)
      (fun (r, ()) m' => ∃ ext' s',
        10000000 ≤ r.toNat ∧ s'.core = (nvM8DtState 25000000#64).core ∧
        s'.LengthsOk nvM8Cfg ∧ M6HdrScratchPres (nvM8DtState 25000000#64) s' ∧
        M6HdrExtOk ext' ∧ nvM8F0.Unsat ∧ FullM6HdrMem nvM8Cfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nvM8ProbeDticksNoninit_exec m8SweepV2CoreParityEnv
    fun _ _ _ _ hs => m8SweepV2CoreParityEnv_getWatermark hs

/-! ## 4. `full_min_lit_dfs_m8` Concrete 6-Step Multi-Hop DFS UNSAT NV (`r = true`) -/

def nvM8DfsS0 : FullState :=
  nvM8MkState 0#64 0#64 nvM8Wvec0 (List.replicate 4 0#32) (List.replicate 4 0#64)

def nvM8DfsMem0 : Mem 64 :=
  nvM8MkMem 0#64 0#64 nvM8Wvec0 (List.replicate 4 0#32) (List.replicate 4 0#64)

def nvM8Wsort0 : List (BitVec 32) := ((List.replicate 8 0#32).set 0 1#32).set 1 0#32
def nvM8Wsort1 : List (BitVec 32) := nvM8Wsort0.set 1 1#32
def nvM8Wsort2 : List (BitVec 32) := ((nvM8Wsort1.set 1 2#32).set 2 2#32).set 3 0x80000000#32
def nvM8Wsort3 : List (BitVec 32) := nvM8Wsort2.set 3 0x80000001#32
def nvM8Wsort4 : List (BitVec 32) := nvM8Wsort3.set 1 3#32

def nvM8Mrk3 : List (BitVec 8) := (List.replicate 4 0#8).set 2 2#8
def nvM8Mclr3 : List (BitVec 32) := (List.replicate 4 0#32).set 0 2#32

def nvM8DfsStEnd : FullState :=
  m8MinLitDfsState nvM8DfsS0 nvM8Mrk3 nvM8Wsort4 nvM8Mclr3 1 0#64 1#64

private theorem nvM8DfsStEnd_witness :
    FullWitnessInv nvM8Cfg nvM8F0 nvM8FCur nvM8DfsStEnd.core := by
  have har0 := nvM8Base_witness.arena
  have hdm : nvM8DfsStEnd.core.dense_mode = 0#64 := rfl
  have har : FullArenaClausesInv nvM8Cfg nvM8FCur nvM8DfsStEnd.core :=
    { len_ok := har0.len_ok
      refs_wf := fun r hr => har0.refs_wf r hr
      shrk_term := fun r hr => har0.shrk_term r hr
      lits_lt := fun r hr hg l hl => har0.lits_lt r hr hg l hl
      entails := fun r hr hg => har0.entails r hr hg }
  have hwat : ModeWatchesInv nvM8FCur nvM8DfsStEnd.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices
      (fun l hl => (by decide : ∀ q : Fin 8,
        fullWatchOffCore nvM8DfsStEnd.core q.1 +
        fullWatchSizeCore nvM8DfsStEnd.core q.1 ≤ 1) ⟨l, hl⟩)
      (fun l hl hp => absurd hp (by
        have hz := (by decide : ∀ q : Fin 8,
          fullWatchSizeCore nvM8DfsStEnd.core q.1 = 0) ⟨l, hl⟩
        dsimp only at hz; omega))
      (fun l1 _ h1 _ _ hp => absurd hp (by
        have hz := (by decide : ∀ q : Fin 8,
          fullWatchSizeCore nvM8DfsStEnd.core q.1 = 0) ⟨l1, h1⟩
        dsimp only at hz; omega))
      (fun l hl => by
        have hws : fullWatchSizeCore nvM8DfsStEnd.core l = 0 := (by decide : ∀ q : Fin 8,
          fullWatchSizeCore nvM8DfsStEnd.core q.1 = 0) ⟨l, hl⟩
        have hwo : fullWatchOffCore nvM8DfsStEnd.core l = 0 := (by decide : ∀ q : Fin 8,
          fullWatchOffCore nvM8DfsStEnd.core q.1 = 0) ⟨l, hl⟩
        rw [hwo, hws]; exact WatchSliceOk.empty)
  exact
    { ext_sound := nvM8Base_witness.ext_sound
      inconsistent_sound := nvM8Base_witness.inconsistent_sound
      arena := har
      watches := hwat
      cur_level_le := nvM8Base_witness.cur_level_le
      trail_lits_lt := nvM8Base_witness.trail_lits_lt
      trail_vars_nodup := nvM8Base_witness.trail_vars_nodup
      vals_domain := nvM8Base_witness.vals_domain
      vals_true_iff := nvM8Base_witness.vals_true_iff
      vals_false_iff := nvM8Base_witness.vals_false_iff
      lvl_le := nvM8Base_witness.lvl_le
      dec_earliest := nvM8Base_witness.dec_earliest
      levels_inhabited := nvM8Base_witness.levels_inhabited
      level0_sound := nvM8Base_witness.level0_sound
      trail_pos_inv := nvM8Base_witness.trail_pos_inv
      level0_rsn_none := nvM8Base_witness.level0_rsn_none
      frame_trail_lt := nvM8Base_witness.frame_trail_lt
      frame_trail_mono := nvM8Base_witness.frame_trail_mono
      frame_trail_before_lt := nvM8Base_witness.frame_trail_before_lt
      frame_dec_lt := nvM8Base_witness.frame_dec_lt
      reason_inv := nvM8Base_witness.reason_inv
      reason_lit_mem := nvM8Base_witness.reason_lit_mem }

private theorem nvM8DfsState_lengths {mrk : List (BitVec 8)} {wsort mclr : List (BitVec 32)}
    {mcl : Nat} {mcf ticks : BitVec 64} (hmrk : mrk.length = 4) (hws : wsort.length = 8)
    (hmclr : mclr.length = 4) (hmcl : mcl ≤ 4) :
    (m8MinLitDfsState nvM8DfsS0 mrk wsort mclr mcl mcf ticks).LengthsOk nvM8Cfg :=
  have hb := nvM8Mk_lengths (stable := 0#64) (ticks := 0#64) (wvec := nvM8Wvec0)
    (qs := List.replicate 4 0#32) (sc := List.replicate 4 0#64) rfl rfl rfl
  ⟨{ hb.core_ok with
      mrk_len := hmrk, min_clr_len_arr := hmclr,
      min_clr_len_le := by simpa [nvM8Cfg] using hmcl },
   { hb.scratch_ok with wsort_len := hws }⟩

private theorem nvM8DfsStEnd_lengths : nvM8DfsStEnd.LengthsOk nvM8Cfg :=
  nvM8DfsState_lengths rfl rfl rfl (by decide)

private def nvM8DfsSt0 : FullState :=
  m8MinLitDfsState nvM8DfsS0 (List.replicate 4 0#8) nvM8Wsort0 (List.replicate 4 0#32) 0 0#64 0#64

private def nvM8DfsSt0t : FullState :=
  m8MinLitDfsState nvM8DfsS0 (List.replicate 4 0#8) nvM8Wsort0 (List.replicate 4 0#32) 0 0#64 1#64

private def nvM8DfsSt1 : FullState :=
  m8MinLitDfsState nvM8DfsS0 (List.replicate 4 0#8) nvM8Wsort1 (List.replicate 4 0#32) 0 0#64 1#64

private def nvM8DfsSt1a : FullState :=
  m8MinLitDfsState nvM8DfsS0 (List.replicate 4 0#8) (nvM8Wsort1.set 1 2#32)
    (List.replicate 4 0#32) 0 0#64 1#64

private def nvM8DfsSt2 : FullState :=
  m8MinLitDfsState nvM8DfsS0 (List.replicate 4 0#8) nvM8Wsort2 (List.replicate 4 0#32) 0 0#64 1#64

private def nvM8DfsSt3 : FullState :=
  m8MinLitDfsState nvM8DfsS0 (List.replicate 4 0#8) nvM8Wsort3 (List.replicate 4 0#32) 0 0#64 1#64

private def nvM8DfsSt4 : FullState :=
  m8MinLitDfsState nvM8DfsS0 nvM8Mrk3 nvM8Wsort3 nvM8Mclr3 1 0#64 1#64

private def nvM8DfsLpInv (n : Nat) (xs : Tup Val [i64, i64, i64]) (m : Mem 64) : Prop :=
  (n = 0 ∧ xs = (0#64, 0#64, 5#64, ()) ∧ (FullMem nvM8Cfg nvM8DfsStEnd ⋆ emp) m) ∨
  (n = 1 ∧ xs = (0#64, 0#64, 4#64, ()) ∧ (FullMem nvM8Cfg nvM8DfsSt4 ⋆ emp) m) ∨
  (n = 2 ∧ xs = (1#64, 1#64, 3#64, ()) ∧ (FullMem nvM8Cfg nvM8DfsSt3 ⋆ emp) m) ∨
  (n = 3 ∧ xs = (1#64, 1#64, 2#64, ()) ∧ (FullMem nvM8Cfg nvM8DfsSt2 ⋆ emp) m) ∨
  (n = 4 ∧ xs = (0#64, 0#64, 1#64, ()) ∧ (FullMem nvM8Cfg nvM8DfsSt1 ⋆ emp) m) ∨
  (n = 5 ∧ xs = (0#64, 0#64, 0#64, ()) ∧ (FullMem nvM8Cfg nvM8DfsSt0 ⋆ emp) m)

private def nvM8DfsBrkPost : Tup Val [i64, i64, .bool, i64] → Mem 64 → Prop :=
  fun (sp, cd, ok, steps, ()) m =>
    sp = 0#64 ∧ cd = 0#64 ∧ ok = true ∧ steps = 6#64 ∧
    (FullMem nvM8Cfg nvM8DfsStEnd ⋆ emp) m

private theorem nv_getElem_eq_getD {α : Type _} [Inhabited α] {xs : List α} {i : Nat}
    (hi : i < xs.length) : xs[i]'hi = xs[i]?.getD default := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some]

private theorem nvM8DfsS0_entry_store_eq {ws1 ws2 : List (BitVec 32)}
    (h : ws2 = nvM8Wsort0) :
    ({ { nvM8DfsS0 with scratch := { nvM8DfsS0.scratch with wsort := ws1 } } with
       scratch :=
         { ({ nvM8DfsS0 with scratch := { nvM8DfsS0.scratch with wsort := ws1 } } :
             FullState).scratch with wsort := ws2 } } : FullState) = nvM8DfsSt0 := by
  subst h; rfl

private theorem nvM8Dfs_mem_cast {s s' : FullState} {m : Mem 64}
    (hm : (FullMem nvM8Cfg s ⋆ emp) m) (h : s = s') :
    (FullMem nvM8Cfg s' ⋆ emp) m := h ▸ hm

private theorem nvM8Dfs_wsort_rw {st st' : FullState} {mrk : List (BitVec 8)}
    {ws0 ws1 ws2 mclr : List (BitVec 32)} {mcl : Nat} {mcf ticks : BitVec 64}
    (hst : st = m8MinLitDfsState nvM8DfsS0 mrk ws0 mclr mcl mcf ticks)
    (hst' : st' = m8MinLitDfsState nvM8DfsS0 mrk ws2 mclr mcl mcf ticks) (h : ws1 = ws2) :
    ({ st with scratch := { st.scratch with wsort := ws1 } } : FullState) = st' := by
  subst hst; subst hst'; subst h; rfl

private theorem nvM8Dfs_wsort2_rw {st st' : FullState} {mrk : List (BitVec 8)}
    {ws0 ws1 ws2 ws3 mclr : List (BitVec 32)} {mcl : Nat} {mcf ticks : BitVec 64}
    (hst : st = m8MinLitDfsState nvM8DfsS0 mrk ws0 mclr mcl mcf ticks)
    (hst' : st' = m8MinLitDfsState nvM8DfsS0 mrk ws3 mclr mcl mcf ticks) (h : ws2 = ws3) :
    let st1 : FullState := { st with scratch := { st.scratch with wsort := ws1 } }
    ({ st1 with scratch := { st1.scratch with wsort := ws2 } } : FullState) = st' := by
  subst hst; subst hst'; subst h; rfl

private theorem nvM8Dfs_ticks_rw {st st' : FullState} {mrk : List (BitVec 8)}
    {ws mclr : List (BitVec 32)} {mcl : Nat} {mcf ticks ticks' : BitVec 64}
    (hst : st = m8MinLitDfsState nvM8DfsS0 mrk ws mclr mcl mcf ticks)
    (hst' : st' = m8MinLitDfsState nvM8DfsS0 mrk ws mclr mcl mcf ticks')
    (h : ticks' = ticks + 1#64) :
    ({ st with
       scratch := { st.scratch with search_ticks := st.scratch.search_ticks + 1#64 } } :
      FullState) = st' := by
  subst hst; subst hst'; subst h; rfl

local macro "nv_dfs_step" : tactic =>
  `(tactic| (c0_hsplit <;>
    first
    | (exfalso; rename_i hc; simp only [nv_getElem_eq_getD] at hc; revert hc; decide)
    | (exfalso; rename_i hc; revert hc; decide)
    | skip))

private theorem nvM8MinLitDfs_exec (Γ : Env)
    (hMm : ∀ a m Q X, Full.fullMinMarkSpec a m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] a m Q X) :
    Func.wp Γ full_min_lit_dfs_m8_body (nvM8Cfg.hdr, 3#32, false, false, ()) nvM8DfsMem0
      (fun (r, ()) m' =>
        r = true ∧ nvM8DfsStEnd.scratch.search_ticks = 1#64 ∧
        nvM8DfsStEnd.core.mrk = [0#8, 0#8, 2#8, 0#8] ∧ nvM8DfsStEnd.LengthsOk nvM8Cfg ∧
        FullWitnessInv nvM8Cfg nvM8F0 nvM8FCur nvM8DfsStEnd.core ∧ nvM8F0.Unsat ∧
        FullMem nvM8Cfg nvM8DfsStEnd m')
      (fun _ _ _ _ => False) := by
  have hm0 : (FullMem nvM8Cfg nvM8DfsS0 ⋆ emp) nvM8DfsMem0 := nvM8MkMem_ok rfl rfl rfl
  have h1r : (((3#32 : BitVec 32) >>> 1).setWidth 64).toNat < nvM8DfsS0.core.rsns.length := by
    decide
  have h1l : (((3#32 : BitVec 32) >>> 1).setWidth 64).toNat < nvM8DfsS0.core.lvl.length := by
    decide
  have hws0 : (BitVec.signExtend 64 (0#32 : BitVec 32)).toNat < nvM8DfsS0.scratch.wsort.length := by
    decide
  have hws1 : (BitVec.signExtend 64 (1#32 : BitVec 32)).toNat <
      (nvM8DfsS0.scratch.wsort.set 0 1#32).length := by decide
  unfold Func.wp full_min_lit_dfs_m8_body
  c0_hsteps_nogrp
  · exfalso; simp only [nvM8DfsS0, nvM8MkState, nvM8MkCore] at hc; revert hc; decide
  · exfalso; revert hc; decide
  · exfalso
    have hc' := congrArg Option.some hc
    rw [← List.getElem?_eq_getElem] at hc'
    revert hc'; decide
  · refine wp_join_group (ts := []) (fun _ m0 => m0 = nvM8DfsMem0) ?_
      (fun J0 hJ0 => by
        dsimp only
        refine wp_jnz_false rfl ?_
        exact hJ0 () nvM8DfsMem0 rfl)
    rintro _ ⟨⟩ m0 rfl
    rw [Blocks.get_here]
    c0_hsteps_nogrp
    have hws0_eq :
        (nvM8DfsS0.scratch.wsort.set (BitVec.ofNat 64 0).toNat (3#32 >>> 1)).set
          (BitVec.ofNat 64 1).toNat 0 = nvM8Wsort0 := by decide
    rw [nvM8DfsS0_entry_store_eq hws0_eq] at hm
    have hm0_lp := hm
    clear hm
    refine wp_loop_break_group nvM8DfsBrkPost nvM8DfsLpInv ?_ ?_ ?_
    · rintro B ⟨sp_b, cd_b, ok_b, steps_b, ⟨⟩⟩ m_b ⟨rfl, rfl, rfl, rfl, hB⟩
      rw [Blocks.get_here]
      refine wp_jnz_true rfl ?_
      dsimp only [wp]
      rw [sep_emp] at hB
      exact ⟨rfl, rfl, rfl, nvM8DfsStEnd_lengths, nvM8DfsStEnd_witness, nvM8F0_unsat, hB⟩
    · rintro B L n ⟨sp, cd, steps, ⟨⟩⟩ m_l hB hL hinv
      rcases hinv with ⟨rfl, hxs, hm_in⟩ | ⟨rfl, hxs, hm_in⟩ | ⟨rfl, hxs, hm_in⟩ |
        ⟨rfl, hxs, hm_in⟩ | ⟨rfl, hxs, hm_in⟩ | ⟨rfl, hxs, hm_in⟩
      · -- n = 0: steps = 5, sp = 0, cd = 0 -> !(pos < 3), sp == 0 -> ok := true; break
        rcases hxs with ⟨rfl, rfl, rfl⟩
        have hsp0 : (0#64 : BitVec 64).toNat < nvM8DfsStEnd.scratch.wsort.length := by decide
        have hws_ev : ((0#64 : BitVec 64) <<< ((BitVec.signExtend 64 1#32).toNat % 64)).toNat <
            nvM8DfsStEnd.scratch.wsort.length := by decide
        have hws_od : (((0#64 : BitVec 64) <<< ((BitVec.signExtend 64 1#32).toNat % 64)) +
            1#64).toNat < nvM8DfsStEnd.scratch.wsort.length := by decide
        have hrsn1 : ((1#32 : BitVec 32).setWidth 64).toNat < nvM8DfsStEnd.core.rsns.length := by
          decide
        have ha2 : ((0#32 : BitVec 32).setWidth 64 + 2#64).toNat <
            nvM8DfsStEnd.core.arena.length := by decide
        rw [Blocks.get_here]
        iterate 7 nv_dfs_step
        refine wp_join_group (ts := []) (fun _ m_tk =>
            (FullMem nvM8Cfg nvM8DfsStEnd ⋆ emp) m_tk) ?_ ?_
        · rintro _ ⟨⟩ m_tk hm_tk; rw [Blocks.get_here]
          iterate 2 nv_dfs_step
          exact hB (0#64, 0#64, true, 6#64, ()) m_tk ⟨rfl, rfl, rfl, rfl, hm_tk⟩
        · intro Jtk hJtk; nv_dfs_step; exact hJtk () m_l hm_in
      · -- n = 1: steps = 4, sp = 0, cd = 0 -> pos=2, l=1, u=0, ul=0 -> continue
        rcases hxs with ⟨rfl, rfl, rfl⟩
        have hws_ev : ((0#64 : BitVec 64) <<< ((BitVec.signExtend 64 1#32).toNat % 64)).toNat <
            nvM8DfsSt4.scratch.wsort.length := by decide
        have hws_od : (((0#64 : BitVec 64) <<< ((BitVec.signExtend 64 1#32).toNat % 64)) +
            1#64).toNat < nvM8DfsSt4.scratch.wsort.length := by decide
        have hrsn1 : ((1#32 : BitVec 32).setWidth 64).toNat < nvM8DfsSt4.core.rsns.length := by
          decide
        have ha2 : ((0#32 : BitVec 32).setWidth 64 + 2#64).toNat <
            nvM8DfsSt4.core.arena.length := by decide
        have ha_lit : ((0#32 : BitVec 32).setWidth 64 + 3#64 +
            (((2#32 : BitVec 32) &&& 0x7FFFFFFF#32).setWidth 64)).toNat <
            nvM8DfsStEnd.core.arena.length := by decide
        have hlvl0 : (((1#32 : BitVec 32) >>> 1).setWidth 64).toNat <
            nvM8DfsStEnd.core.lvl.length := by decide
        rw [Blocks.get_here]
        iterate 7 nv_dfs_step
        refine wp_join_group (ts := []) (fun _ m_tk =>
            (FullMem nvM8Cfg nvM8DfsSt4 ⋆ emp) m_tk) ?_ ?_
        · rintro _ ⟨⟩ m_tk hm_tk; rw [Blocks.get_here]
          nv_dfs_step
          iterate 9 c0_hstep
          replace hm := nvM8Dfs_mem_cast hm
            (nvM8Dfs_wsort_rw (st := nvM8DfsSt4) (st' := nvM8DfsStEnd) rfl rfl
              (by first | (simp only [nv_getElem_eq_getD]; decide) | decide))
          nv_dfs_step
          simp only [nv_getElem_eq_getD]
          rw [show nvM8DfsStEnd.core.arena[(BitVec.setWidth 64
              (nvM8DfsSt4.core.rsns[(BitVec.setWidth 64
                (nvM8DfsSt4.scratch.wsort[(0#64 <<< OfNat.ofNat 1).toNat]?.getD
                  default)).toNat]?.getD default) + (3 : BitVec 64) +
              BitVec.setWidth 64
                ((nvM8DfsSt4.scratch.wsort[(0#64 <<< OfNat.ofNat 1 + 1).toNat]?.getD
                  default) &&& 2147483647)).toNat]?.getD default = 1#32 from by decide]
          iterate 2 nv_dfs_step
          exact hL 0 (0#64, 0#64, 5#64, ()) _ (by omega) (Or.inl ⟨rfl, rfl, hm⟩)
        · intro Jtk hJtk; nv_dfs_step; exact hJtk () m_l hm_in
      · -- n = 2: steps = 3, sp = 1, cd = 1 -> is_bin, pos=1 -> full_min_mark 2 2, pop
        rcases hxs with ⟨rfl, rfl, rfl⟩
        have hws_ev : ((1#64 : BitVec 64) <<< ((BitVec.signExtend 64 1#32).toNat % 64)).toNat <
            nvM8DfsSt3.scratch.wsort.length := by decide
        have hws_od : (((1#64 : BitVec 64) <<< ((BitVec.signExtend 64 1#32).toNat % 64)) +
            1#64).toNat < nvM8DfsSt3.scratch.wsort.length := by decide
        have hrsn2 : ((2#32 : BitVec 32).setWidth 64).toNat < nvM8DfsSt3.core.rsns.length := by
          decide
        rw [Blocks.get_here]
        iterate 6 nv_dfs_step
        c0_hsteps_nogrp
        refine wp_call_of_spec _ _ (hMm _ _ _ _ ?_)
        refine ⟨nvM8Cfg, nvM8DfsSt3, emp, rfl,
          nvM8DfsState_lengths rfl rfl rfl (by decide), hm_in, ?_⟩
        · dsimp only [Arg.val]
          rw [nv_getElem_eq_getD]
          have hv2 :
              nvM8DfsSt3.scratch.wsort[(1#64 <<< OfNat.ofNat 1).toNat]?.getD default = 2#32 := by
            decide
          have hchk :
              ¬ (nvM8DfsSt3.core.cur_vars ≤ (2#32 : BitVec 32).toNat ∨
                nvM8DfsSt3.core.mrk[(2#32 : BitVec 32).toNat]?.getD 0#8 &&&
                  BitVec.ofNat 8 2 ≠ 0#8) := by decide
          simp only [hv2, eq_false hchk, ↓reduceIte]
          intro m4 hm4
          have hst_eq :
              fullMinMarkState nvM8DfsSt3 (2#32 : BitVec 32).toNat
                (BitVec.ofNat 8 2) = nvM8DfsSt4 := by
            unfold fullMinMarkState fullMinMarkCore nvM8DfsSt3 nvM8DfsSt4 m8MinLitDfsState
            have hz : ((List.replicate 4 (0#8 : BitVec 8))[(2#32 : BitVec 32).toNat]?.getD
                0#8 = 0#8) := by decide
            have hc3 : (0 : Nat) < nvM8DfsS0.core.cur_vars := by decide
            simp only [hz, eq_true hc3, and_self, and_false, not_true_eq_false, ↓reduceIte]
            rw [show (List.replicate 4 (0#8 : BitVec 8)).set (2#32 : BitVec 32).toNat
                (0#8 ||| BitVec.ofNat 8 2) = nvM8Mrk3 from by decide,
              show (List.replicate 4 (0#32 : BitVec 32)).set 0
                (BitVec.ofNat 32 (2#32 : BitVec 32).toNat) = nvM8Mclr3 from by decide]
          rw [hst_eq] at hm4
          refine wp_join_group (ts := [i64])
            (fun (cd', ()) m_c => cd' = 0#64 ∧ m_c = m4)
            (fun _ ⟨cd', ⟨⟩⟩ m_c ⟨hcd', hm_eq⟩ => by
              subst hcd'; subst hm_eq; rw [Blocks.get_here]; c0_hsteps_nogrp
              exact hL 1 (0#64, 0#64, 4#64, ()) _ (by omega)
                (Or.inr (Or.inl ⟨rfl, rfl, hm4⟩)))
            (fun Jcd hJcd => by
              nv_dfs_step; c0_hsteps_nogrp; exact hJcd (0#64, ()) m4 ⟨rfl, rfl⟩)
      · -- n = 3: steps = 2, sp = 1, cd = 1 -> is_bin, pos=0, u=0, ul=0 -> continue
        rcases hxs with ⟨rfl, rfl, rfl⟩
        have hws_ev : ((1#64 : BitVec 64) <<< ((BitVec.signExtend 64 1#32).toNat % 64)).toNat <
            nvM8DfsSt2.scratch.wsort.length := by decide
        have hws_od : (((1#64 : BitVec 64) <<< ((BitVec.signExtend 64 1#32).toNat % 64)) +
            1#64).toNat < nvM8DfsSt2.scratch.wsort.length := by decide
        have hrsn2 : ((2#32 : BitVec 32).setWidth 64).toNat < nvM8DfsSt2.core.rsns.length := by
          decide
        have hlvl0 :
            ((((0x80000001#32 : BitVec 32) &&& 0x7FFFFFFF#32) >>> 1).setWidth 64).toNat <
            nvM8DfsSt3.core.lvl.length := by decide
        rw [Blocks.get_here]
        iterate 6 nv_dfs_step
        replace hm := nvM8Dfs_mem_cast hm
          (nvM8Dfs_wsort_rw (st := nvM8DfsSt2) (st' := nvM8DfsSt3) rfl rfl
            (by first | (simp only [nv_getElem_eq_getD]; decide) | decide))
        iterate 2 nv_dfs_step
        exact hL 2 (1#64, 1#64, 3#64, ()) _ (by omega)
          (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hm⟩)))
      · -- n = 4: steps = 1, sp = 0, cd = 0 -> !is_bin, pos=1, l=5, u=2 -> push sp=1, cd=1
        rcases hxs with ⟨rfl, rfl, rfl⟩
        have hws_ev : ((0#64 : BitVec 64) <<< ((BitVec.signExtend 64 1#32).toNat % 64)).toNat <
            nvM8DfsSt1.scratch.wsort.length := by decide
        have hws_od : (((0#64 : BitVec 64) <<< ((BitVec.signExtend 64 1#32).toNat % 64)) +
            1#64).toNat < nvM8DfsSt1.scratch.wsort.length := by decide
        have hrsn1 : ((1#32 : BitVec 32).setWidth 64).toNat < nvM8DfsSt1.core.rsns.length := by
          decide
        have ha2 : ((0#32 : BitVec 32).setWidth 64 + 2#64).toNat <
            nvM8DfsSt1.core.arena.length := by decide
        have ha_lit : ((0#32 : BitVec 32).setWidth 64 + 3#64 +
            (((1#32 : BitVec 32) &&& 0x7FFFFFFF#32).setWidth 64)).toNat <
            nvM8DfsSt1a.core.arena.length := by decide
        have hlvl2 : (((5#32 : BitVec 32) >>> 1).setWidth 64).toNat <
            nvM8DfsSt1a.core.lvl.length := by decide
        have hmrk2 : (((5#32 : BitVec 32) >>> 1).setWidth 64).toNat <
            nvM8DfsSt1a.core.mrk.length := by decide
        have hrsn2 : (((5#32 : BitVec 32) >>> 1).setWidth 64).toNat <
            nvM8DfsSt1a.core.rsns.length := by decide
        rw [Blocks.get_here]
        iterate 7 nv_dfs_step
        refine wp_join_group (ts := []) (fun _ m_tk =>
            (FullMem nvM8Cfg nvM8DfsSt1 ⋆ emp) m_tk) ?_ ?_
        · rintro _ ⟨⟩ m_tk hm_tk; rw [Blocks.get_here]
          nv_dfs_step
          iterate 9 c0_hstep
          replace hm := nvM8Dfs_mem_cast hm
            (nvM8Dfs_wsort_rw (st := nvM8DfsSt1) (st' := nvM8DfsSt1a) rfl rfl
              (by first | (simp only [nv_getElem_eq_getD]; decide) | decide))
          nv_dfs_step
          simp only [nv_getElem_eq_getD]
          rw [show nvM8DfsSt1a.core.arena[(BitVec.setWidth 64
              (nvM8DfsSt1.core.rsns[(BitVec.setWidth 64
                (nvM8DfsSt1.scratch.wsort[(0#64 <<< OfNat.ofNat 1).toNat]?.getD
                  default)).toNat]?.getD default) + (3 : BitVec 64) +
              BitVec.setWidth 64
                ((nvM8DfsSt1.scratch.wsort[(0#64 <<< OfNat.ofNat 1 + 1).toNat]?.getD
                  default) &&& 2147483647)).toNat]?.getD default = 5#32 from by decide]
          iterate 5 nv_dfs_step
          refine wp_join_group (ts := [])
            (fun _ m_cu => (FullMem nvM8Cfg nvM8DfsSt1a ⋆ emp) m_cu) ?_ ?_
          · rintro _ ⟨⟩ m_cu hm_cu; rw [Blocks.get_here]
            have hws_e2 : (((0#64 + 1#64) <<<
                ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64))).toNat <
                nvM8DfsSt1a.scratch.wsort.length := by decide
            have hws_o2 : ((((0#64 + 1#64) <<<
                ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)) + 1#64)).toNat <
                (nvM8DfsSt1a.scratch.wsort.set 2 2#32).length := by decide
            clear hm; iterate 2 nv_dfs_step; c0_hsteps_nogrp
            replace hm := nvM8Dfs_mem_cast hm
              (nvM8Dfs_wsort2_rw (st := nvM8DfsSt1a) (st' := nvM8DfsSt2) rfl rfl (by decide))
            exact hL 3 (1#64, 1#64, 2#64, ()) _ (by omega)
              (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hm⟩))))
          · intro Jcu hJcu; nv_dfs_step; exact hJcu () _ hm
        · intro Jtk hJtk; nv_dfs_step; exact hJtk () m_l hm_in
      · -- n = 5: steps = 0, sp = 0, cd = 0 -> !is_bin, pos=0 -> search_ticks+=1, l=2, u=1=v -> L
        rcases hxs with ⟨rfl, rfl, rfl⟩
        have hws_ev : ((0#64 : BitVec 64) <<< ((BitVec.signExtend 64 1#32).toNat % 64)).toNat <
            nvM8DfsSt0.scratch.wsort.length := by decide
        have hws_od : (((0#64 : BitVec 64) <<< ((BitVec.signExtend 64 1#32).toNat % 64)) +
            1#64).toNat < nvM8DfsSt0.scratch.wsort.length := by decide
        have hrsn1 : ((1#32 : BitVec 32).setWidth 64).toNat < nvM8DfsSt0.core.rsns.length := by
          decide
        have ha2 : ((0#32 : BitVec 32).setWidth 64 + 2#64).toNat <
            nvM8DfsSt0.core.arena.length := by decide
        rw [Blocks.get_here]
        iterate 7 nv_dfs_step
        refine wp_join_group (ts := []) (fun _ m_tk =>
            (FullMem nvM8Cfg nvM8DfsSt0t ⋆ emp) m_tk) ?_ ?_
        · rintro _ ⟨⟩ m_tk hm_tk; rw [Blocks.get_here]
          have ha_lit : ((0#32 : BitVec 32).setWidth 64 + 3#64 +
              (((0#32 : BitVec 32) &&& 0x7FFFFFFF#32).setWidth 64)).toNat <
              nvM8DfsSt1.core.arena.length := by decide
          have hlvl1 : (((2#32 : BitVec 32) >>> 1).setWidth 64).toNat <
              nvM8DfsSt1.core.lvl.length := by decide
          nv_dfs_step
          iterate 9 c0_hstep
          replace hm := nvM8Dfs_mem_cast hm
            (nvM8Dfs_wsort_rw (st := nvM8DfsSt0t) (st' := nvM8DfsSt1) rfl rfl
              (by first | (simp only [nv_getElem_eq_getD]; decide) | decide))
          nv_dfs_step
          simp only [nv_getElem_eq_getD]
          rw [show nvM8DfsSt1.core.arena[(BitVec.setWidth 64
              (nvM8DfsSt0.core.rsns[(BitVec.setWidth 64
                (nvM8DfsSt0.scratch.wsort[(0#64 <<< OfNat.ofNat 1).toNat]?.getD
                  default)).toNat]?.getD default) + (3 : BitVec 64) +
              BitVec.setWidth 64
                ((nvM8DfsSt0.scratch.wsort[(0#64 <<< OfNat.ofNat 1 + 1).toNat]?.getD
                  default) &&& 2147483647)).toNat]?.getD default = 2#32 from by decide]
          nv_dfs_step
          exact hL 4 (0#64, 0#64, 1#64, ()) _ (by omega)
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hm⟩)))))
        · intro Jtk hJtk
          nv_dfs_step
          c0_hsteps_nogrp
          replace hm := nvM8Dfs_mem_cast hm
            (nvM8Dfs_ticks_rw (st := nvM8DfsSt0) (st' := nvM8DfsSt0t) rfl rfl rfl)
          exact hJtk () _ hm
    · rintro B L hB hL
      c0_hsteps_nogrp
      exact hL 5 (0#64, 0#64, 0#64, ()) _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨rfl, rfl, hm0_lp⟩)))))

/-- Concrete `Mem 64` 6-step UNSAT NV (`XPost := False`): `full_min_lit_dfs_m8` under
`m8CoreParityEnv` traverses ternary reason clause `[2, 5, 1]` and binary reason `u = 2`,
calls `"full_min_mark"` on `u = 2`, increments `search_ticks` to `1#64`, and pins exact
`r = true`, `s'.core.mrk = [0#8, 0#8, 2#8, 0#8]`, `FullWitnessInv`, and `nvM8F0.Unsat`. -/
theorem nv_m8_min_lit_dfs_large_bin_true :
    Func.wp m8CoreParityEnv full_min_lit_dfs_m8_body (nvM8Cfg.hdr, 3#32, false, false, ())
      nvM8DfsMem0
      (fun (r, ()) m' =>
        r = true ∧ nvM8DfsStEnd.scratch.search_ticks = 1#64 ∧
        nvM8DfsStEnd.core.mrk = [0#8, 0#8, 2#8, 0#8] ∧ nvM8DfsStEnd.LengthsOk nvM8Cfg ∧
        FullWitnessInv nvM8Cfg nvM8F0 nvM8FCur nvM8DfsStEnd.core ∧ nvM8F0.Unsat ∧
        FullMem nvM8Cfg nvM8DfsStEnd m')
      (fun _ _ _ _ => False) :=
  nvM8MinLitDfs_exec m8CoreParityEnv fun _ _ _ _ hs => m8CoreParityEnv_minMark hs

theorem nv_m8_min_lit_dfs_large_bin_true_sw :
    Func.wp m8SweepV2CoreParityEnv full_min_lit_dfs_m8_body
      (nvM8Cfg.hdr, 3#32, false, false, ()) nvM8DfsMem0
      (fun (r, ()) m' =>
        r = true ∧ nvM8DfsStEnd.scratch.search_ticks = 1#64 ∧
        nvM8DfsStEnd.core.mrk = [0#8, 0#8, 2#8, 0#8] ∧ nvM8DfsStEnd.LengthsOk nvM8Cfg ∧
        FullWitnessInv nvM8Cfg nvM8F0 nvM8FCur nvM8DfsStEnd.core ∧ nvM8F0.Unsat ∧
        FullMem nvM8Cfg nvM8DfsStEnd m')
      (fun _ _ _ _ => False) :=
  nvM8MinLitDfs_exec m8SweepV2CoreParityEnv
    fun _ _ _ _ hs => m8SweepV2CoreParityEnv_minMark hs

/-! ## 5. `full_min_shrink_m6` Concrete 18-Var Non-Bailout UNSAT NV (`tmp_len = 18 > 16`) -/

def nvM8Min18Cfg : FullCfg :=
  { hdr := 0x1000#64, avail := 4508, mv := 18, max_vars := 18, bva_cap := 0, nc := 1
    arena_cap := 0, wcap := 1, delayed_cap := 0, red_cap := 0, extend_cap := 0, scratch_cap := 0
    hbva := rfl, hmv := by decide, hmaxv := by decide, hnc := by decide, harena := by decide
    hwcap := by decide, hdel := by decide, hred := by decide, hext := by decide, hscr := by decide
    havail_fit := by decide, hsize := by decide }

def nvM8Min18Vals : List (BitVec 8) :=
  [ 1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8,
    1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8,
    1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8, 1#8, 0xFF#8 ]

def nvM8Min18Lvl : List (BitVec 32) :=
  [ 1#32, 2#32, 3#32, 4#32, 5#32, 6#32, 7#32, 8#32, 9#32,
    10#32, 11#32, 12#32, 13#32, 14#32, 15#32, 16#32, 17#32, 18#32 ]

def nvM8Min18Trl : List (BitVec 32) :=
  [ 0#32, 2#32, 4#32, 6#32, 8#32, 10#32, 12#32, 14#32, 16#32,
    18#32, 20#32, 22#32, 24#32, 26#32, 28#32, 30#32, 32#32, 34#32 ]

def nvM8Min18Tpos : List (BitVec 32) :=
  [ 0#32, 1#32, 2#32, 3#32, 4#32, 5#32, 6#32, 7#32, 8#32,
    9#32, 10#32, 11#32, 12#32, 13#32, 14#32, 15#32, 16#32, 17#32 ]

def nvM8Min18FTrl : List (BitVec 32) :=
  [ 0#32, 0#32, 1#32, 2#32, 3#32, 4#32, 5#32, 6#32, 7#32, 8#32,
    9#32, 10#32, 11#32, 12#32, 13#32, 14#32, 15#32, 16#32, 17#32 ]

def nvM8Min18FDec : List (BitVec 32) :=
  [ 0#32, 0#32, 2#32, 4#32, 6#32, 8#32, 10#32, 12#32, 14#32, 16#32,
    18#32, 20#32, 22#32, 24#32, 26#32, 28#32, 30#32, 32#32, 34#32 ]

def nvM8Min18Tmp : List (BitVec 32) :=
  [ 35#32, 33#32, 31#32, 29#32, 27#32, 25#32, 23#32, 21#32, 19#32,
    17#32, 15#32, 13#32, 11#32, 9#32, 7#32, 5#32, 3#32, 1#32 ]

def nvM8Min18Scratch : FullScratch :=
  { heap_len := 0, scinc := 0#64, rel_period := 0#64, rel_limit := 0#64, rel_wait := 0#64
    rel_u := 0#64, rel_v := 0#64, rel_trigger := 0#64, conflicts := 0#64
    learned_lits := 0#64, min_removed := 0#64, delayed_len := 0, stable := 0#64
    switched := 0#64, mode_count := 0#64, mode_confl_lim := 0#64, mode_tick_lim := 0#64
    mode_saved_ticks := 0#64, search_ticks := 0#64, q_first := 0#64, q_last := 0#64
    q_search_idx := 0#64, q_search_stamp := 0#64, q_cur_stamp := 0#64
    target_assigned := 0#64, best_assigned := 0#64, rephase_limit := 0#64
    rephased := 0#64, reduce_limit := 0#64, reductions := 0#64, tier1 := 0#64
    tier2 := 0#64, restarts := 0#64, restart_limit := 0#64, ema_fast_biased := 0#64
    ema_fast_exp := 0#64, ema_slow_biased := 0#64, ema_slow_exp := 0#64, extend_len := 0
    rng_state := 0#64, chrono_levels := 0#64, otfs_cnt := 0#64, eager_sub_cnt := 0#64
    probe_limit := 0#64, probings := 0#64, elim_limit := 0#64, eliminations := 0#64
    elim_bound := 0#64, iterating := 0#64, hbr_cnt := 0#64, trans_cnt := 0#64
    viv_cnt := 0#64, subst_cnt := 0#64, cong_cnt := 0#64, sweep_cnt := 0#64
    bve_cnt := 0#64, bce_cnt := 0#64, bva_cnt := 0#64, walk_cnt_stat := 0#64
    fwd_sub_cnt := 0#64, fwd_str_cnt := 0#64, ant_sz := 0#64, res_sz := 0#64
    walk_vals := List.replicate 36 0#8, phases := List.replicate 18 0#8
    phases_target := List.replicate 18 0#8, phases_best := List.replicate 18 0#8
    walk_best := List.replicate 18 0#8, heap := List.replicate 18 0#32
    pos := List.replicate 18 0#32, shrink_stk := List.replicate 18 0#32
    q_prev := List.replicate 18 0#32, q_next := List.replicate 18 0#32
    q_stamp := List.replicate 18 0#32, wsort := List.replicate 36 0#32
    work_stk1 := List.replicate 36 0#32, work_stk2 := List.replicate 36 0#32
    tarjan_mark := List.replicate 36 0#32, tarjan_reach := List.replicate 36 0#32
    score := List.replicate 18 0#64, sim_sig := List.replicate 18 0#64
    glue_used := List.replicate 64 0#32, last_learned := List.replicate 16 0#32
    delayed := [], red_refs := [], extend_stk := [], scratch_buf := [] }

/-- `18`-variable state (`tmp_len = 18 > 16`, `cur_level = 18`) for non-bailout M8 `min_shrink`. -/
def nvM8Min18State : FullState :=
  { core :=
      { d_cur := 0#64, d_val := 0#64, cur_vars := 18, unassigned := 0#64
        arena_len := 0, wlen := 1, wusable := 0#64, arena_garbage := 0#64
        first_reducible := 0#64, num_irred := 0#64, num_redundant := 0#64
        num_binary := 0#64, unflushed := 0#64, probing := 0#64
        trail_end := 18, propagated := 0, cur_level := 18, fuel := 0#64
        confl_ref := 0#64, confl_type := 1#64, confl_lit0 := 1#64, confl_lit1 := 1#64
        tmp_cnt := 0, tmp_len := 18, min_clr_len := 0, min_clr_full := 0#64
        oom := 0#64, dense_mode := 0#64, inconsistent := 0#64
        vals := nvM8Min18Vals, lit_mark := List.replicate 36 0#8
        mrk := List.replicate 18 0#8, flags := List.replicate 18 0#32
        lvl := nvM8Min18Lvl, rsns := List.replicate 18 0xFFFFFFFF#32
        trl := nvM8Min18Trl, trail_pos := nvM8Min18Tpos
        tmp := nvM8Min18Tmp, min_clr := List.replicate 18 0#32
        frame_trail := nvM8Min18FTrl, frame_dec := nvM8Min18FDec
        wvec := List.replicate 72 0#32, repr := List.replicate 36 0#32
        min_stk := List.replicate 38 0#32, arena := [], wstk := [0#32] }
    scratch := nvM8Min18Scratch }

private def nvM8Min18BlkHdr : List UInt8 :=
  let c := nvM8Min18Cfg; let s := nvM8Min18State
  bytes64 [BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc, s.core.d_cur, s.core.d_val] ++
    bytes64 (Full.hdrTailWords c s)

private def nvM8Min18BlkBytes : List UInt8 :=
  let sc := nvM8Min18State.scratch; let k := nvM8Min18State.core
  (bytesOf (t := i8) k.vals ++ List.replicate 4 0) ++
  (bytesOf (t := i8) sc.walk_vals ++ List.replicate 4 0) ++
  (bytesOf (t := i8) k.lit_mark ++ List.replicate 4 0) ++
  (bytesOf (t := i8) k.mrk ++ List.replicate 6 0) ++
  (bytesOf (t := i8) sc.phases ++ List.replicate 6 0) ++
  (bytesOf (t := i8) sc.phases_target ++ List.replicate 6 0) ++
  (bytesOf (t := i8) sc.phases_best ++ List.replicate 6 0) ++
  (bytesOf (t := i8) sc.walk_best ++ List.replicate 6 0)

private def nvM8Min18BlkU32A : List UInt8 :=
  let k := nvM8Min18State.core
  (bytesOf (t := i32) k.flags ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.lvl ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.rsns ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.trl ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.trail_pos ++ List.replicate 8 0)

private def nvM8Min18BlkU32B : List UInt8 :=
  let k := nvM8Min18State.core; let sc := nvM8Min18State.scratch
  (bytesOf (t := i32) k.tmp ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.heap ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.pos ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.min_clr ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.shrink_stk ++ List.replicate 8 0)

private def nvM8Min18BlkU32C : List UInt8 :=
  let k := nvM8Min18State.core; let sc := nvM8Min18State.scratch
  (bytesOf (t := i32) sc.q_prev ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.q_next ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.q_stamp ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.frame_trail ++ List.replicate 4 0) ++
  (bytesOf (t := i32) k.frame_dec ++ List.replicate 4 0)

private def nvM8Min18BlkWvec : List UInt8 :=
  let k := nvM8Min18State.core; let sc := nvM8Min18State.scratch
  bytesOf (t := i32) k.wvec ++ bytesOf (t := i32) k.repr ++
  bytesOf (t := i32) sc.wsort ++ bytesOf (t := i32) sc.work_stk1 ++
  bytesOf (t := i32) sc.work_stk2 ++ bytesOf (t := i32) sc.tarjan_mark ++
  bytesOf (t := i32) sc.tarjan_reach ++ bytes64 sc.score ++ bytes64 sc.sim_sig

private def nvM8Min18BlkTail : List UInt8 :=
  let k := nvM8Min18State.core; let sc := nvM8Min18State.scratch
  bytesOf (t := i32) k.min_stk ++ bytesOf (t := i32) sc.glue_used ++
  bytesOf (t := i32) sc.last_learned ++ bytesOf (t := i32) k.arena ++
  bytesOf (t := i32) k.wstk ++ bytesOf (t := i32) sc.delayed ++
  bytesOf (t := i32) sc.red_refs ++ bytesOf (t := i32) sc.extend_stk ++
  bytesOf (t := i32) sc.scratch_buf ++ List.replicate 0 0

def nvM8Min18Mem : Mem 64 :=
  (nvM8Min18BlkHdr ++ nvM8Min18BlkBytes ++ nvM8Min18BlkU32A ++ nvM8Min18BlkU32B ++
    nvM8Min18BlkU32C ++ nvM8Min18BlkWvec ++ nvM8Min18BlkTail).At nvM8Min18Cfg.hdr

private theorem nvM8Min18_lengths : nvM8Min18State.LengthsOk nvM8Min18Cfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem nvM8Min18Mem_ok : (FullMem nvM8Min18Cfg nvM8Min18State ⋆ emp) nvM8Min18Mem := by
  let c := nvM8Min18Cfg; let s := nvM8Min18State
  have hv4 : valsBytes c.max_vars - 2 * c.max_vars = 4 := by decide
  have h2m : 2 * c.max_vars = 36 := by decide
  have hm6 : markBytes c.max_vars - c.max_vars = 6 := by decide
  have hm18 : c.max_vars = 18 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * c.max_vars = 8 := by decide
  have h4m : 4 * c.max_vars = 72 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 4 := by decide
  have h4p : 4 * (c.max_vars + 1) = 76 := by decide
  have hsl : c.slack = 0 := by decide
  have hHdr : nvM8Min18BlkHdr.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        array64 (c.hdr + 32) (Full.hdrTailWords c s)) (nvM8Min18BlkHdr.At c.hdr) :=
    nv_join_pair
      ⟨rfl, dimacsState_bytes c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val⟩
      (nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide))
      rfl (by rw [bytes64_length]; simp only [List.length_cons, List.length_nil]; decide)
  have hBytes : nvM8Min18BlkBytes.length = 240 ∧
      ((array (t := i8) c.pVals s.core.vals ⋆ array (t := i8) c.pLitMark s.core.lit_mark ⋆
          array (t := i8) c.pMark s.core.mrk) ⋆
        FullScrByteArrs c s.scratch ⋆ c.padBytes) (nvM8Min18BlkBytes.At c.pVals) := by
    have h1 := nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 36 4 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 36 4 rfl
      (by decide)
    have h3 := nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 36 4 rfl
      (by decide)
    have h4 := nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 18 6 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 18 6 rfl (by decide)
    have h6 := nv_arr_pad_p (t := i8) (a := c.pPhasesTarget) (xs := s.scratch.phases_target) 18 6
      rfl (by decide)
    have h7 := nv_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best) 18 6 rfl
      (by decide)
    have h8 := nv_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best) 18 6 rfl
      (by decide)
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
      unfold FullScrByteArrs FullCfg.padBytes
      rw [hv4, h2m, hm6, hm18]; exact pB hm
  have hU32A : nvM8Min18BlkU32A.length = 400 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        (nvM8Min18BlkU32A.At c.pFlags) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 72 8 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 72 8 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 72 8 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 72 8 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 72 8 rfl
      (by decide)
    have j12 := nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := nv_join_pair j123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair j1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu8, h4m]; exact sep_ac hm
  have hU32B : nvM8Min18BlkU32B.length = 400 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pHeap s.scratch.heap ⋆
        array (t := i32) c.pPos s.scratch.pos ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
        array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        (nvM8Min18BlkU32B.At c.pTmp) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 72 8 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 72 8 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 72 8 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 72 8 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk) 72 8 rfl
      (by decide)
    have j12 := nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := nv_join_pair j123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair j1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu8, h4m]; exact sep_ac hm
  have hU32C : nvM8Min18BlkU32C.length = 400 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        (nvM8Min18BlkU32C.At c.pQPrev) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 72 8 rfl
      (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 72 8 rfl
      (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 72 8 rfl
      (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 76 4 rfl
      (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 76 4 rfl
      (by decide)
    have j12 := nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := nv_join_pair j123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair j1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu8, hu4, h4m, h4p]; exact sep_ac hm
  have hWvec : nvM8Min18BlkWvec.length = 1440 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        (nvM8Min18BlkWvec.At c.pWvec) := by
    have h1 := nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 288 rfl (by decide)
    have h2 := nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 144 rfl (by decide)
    have h3 := nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 144 rfl (by decide)
    have h4 := nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 144 rfl
      (by decide)
    have h5 := nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 144 rfl
      (by decide)
    have h6 := nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 144 rfl
      (by decide)
    have h7 := nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 144 rfl
      (by decide)
    have h8 := nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 144 rfl (by decide)
    have h9 := nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 144 rfl (by decide)
    have j12 := nv_join_pair h1 h2 (by decide) (by decide)
    have j123 := nv_join_pair j12 h3 (by decide) (by decide)
    have j1234 := nv_join_pair j123 h4 (by decide) (by decide)
    have j12345 := nv_join_pair j1234 h5 (by decide) (by decide)
    have j123456 := nv_join_pair j12345 h6 (by decide) (by decide)
    have j1234567 := nv_join_pair j123456 h7 (by decide) (by decide)
    have j12345678 := nv_join_pair j1234567 h8 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair j12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail : nvM8Min18BlkTail.length = 476 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        (nvM8Min18BlkTail.At c.pMinStk) := by
    have h1 := nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 152 rfl (by decide)
    have h2 := nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256 rfl
      (by decide)
    have h3 := nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned) 64 rfl
      (by decide)
    have h4 := nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 0 rfl (by decide)
    have h5 := nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 4 rfl (by decide)
    have h6 := nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl (by decide)
    have h7 := nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl (by decide)
    have h8 := nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl
      (by decide)
    have h9 := nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 0 rfl
      (by decide)
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
  have h06 : (nvM8Min18BlkHdr ++ nvM8Min18BlkBytes ++ nvM8Min18BlkU32A ++ nvM8Min18BlkU32B ++
      nvM8Min18BlkU32C ++ nvM8Min18BlkWvec ++ nvM8Min18BlkTail).length = 4508 ∧
      FullMem c s ((nvM8Min18BlkHdr ++ nvM8Min18BlkBytes ++ nvM8Min18BlkU32A ++
        nvM8Min18BlkU32B ++ nvM8Min18BlkU32C ++ nvM8Min18BlkWvec ++ nvM8Min18BlkTail).At
        c.hdr) := by
    refine nv_sep_reorg (nv_join_pair h05 hTail (by decide) (by decide)) fun _ hm => ?_
    have p3 : ∀ {D H CoreB ScrB P2 Wv Re SW Sc Ss MS Gu Ll CD SD SL : Mem 64 → Prop} {k},
        (((D ⋆ H ⋆ (CoreB ⋆ ScrB ⋆ P2)) ⋆ ((Wv ⋆ Re) ⋆ SW ⋆ (Sc ⋆ Ss))) ⋆
          (MS ⋆ (Gu ⋆ Ll) ⋆ CD ⋆ SD ⋆ SL)) k →
        (D ⋆ H ⋆ (CoreB ⋆ Wv ⋆ Re ⋆ MS ⋆ CD) ⋆ (ScrB ⋆ SW ⋆ Sc ⋆ Ss ⋆ Gu ⋆ Ll ⋆ SD) ⋆
          (P2 ⋆ SL)) k := fun x => sep_ac x
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
  rw [sep_emp]; exact h06.2

private theorem nvM8Min18_witness :
    FullWitnessInv nvM8Min18Cfg nvM8F0 [[0], [1]] nvM8Min18State.core := by
  have hrefs : fullArenaClauseRefsCore nvM8Min18State.core = [] := rfl
  have hcv : nvM8Min18State.core.cur_vars = 18 := rfl
  have hte : nvM8Min18State.core.trail_end = 18 := rfl
  have hcl : nvM8Min18State.core.cur_level = 18 := rfl
  have hdm : nvM8Min18State.core.dense_mode = 0#64 := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvM8Min18State.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices
      (fun l hl => (by decide : ∀ q : Fin 36,
        fullWatchOffCore nvM8Min18State.core q.1 +
        fullWatchSizeCore nvM8Min18State.core q.1 ≤ nvM8Min18State.core.wlen) ⟨l, by omega⟩)
      (fun l hl hp => absurd hp (by
        have hz := (by decide : ∀ q : Fin 36,
          fullWatchSizeCore nvM8Min18State.core q.1 = 0) ⟨l, by omega⟩
        dsimp only at hz; omega))
      (fun l1 _ h1 _ _ hp => absurd hp (by
        have hz := (by decide : ∀ q : Fin 36,
          fullWatchSizeCore nvM8Min18State.core q.1 = 0) ⟨l1, by omega⟩
        dsimp only at hz; omega))
      (fun l hl => by
        have hws : fullWatchSizeCore nvM8Min18State.core l = 0 := (by decide : ∀ q : Fin 36,
          fullWatchSizeCore nvM8Min18State.core q.1 = 0) ⟨l, by omega⟩
        have hwo : fullWatchOffCore nvM8Min18State.core l = 0 := (by decide : ∀ q : Fin 36,
          fullWatchOffCore nvM8Min18State.core q.1 = 0) ⟨l, by omega⟩
        rw [hwo, hws]; exact WatchSliceOk.empty)
  exact
    { ext_sound := ⟨(varsBoundedBool_iff 18 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩
      watches := hwat
      cur_level_le := Nat.le_refl _
      trail_lits_lt := fun i hi => (by decide : ∀ q : Fin 18,
        (nvM8Min18State.core.trl[q.1]?.getD 0#32).toNat < 36) ⟨i, by omega⟩
      trail_vars_nodup := fun i j hi hj heq => congrArg Fin.val ((by decide : ∀ a b : Fin 18,
        (nvM8Min18State.core.trl[a.1]?.getD 0#32).toNat / 2 =
        (nvM8Min18State.core.trl[b.1]?.getD 0#32).toNat / 2 → a = b) ⟨i, by omega⟩ ⟨j, by omega⟩
        heq)
      vals_domain := fun l hl => (by decide : ∀ q : Fin 36,
        let v := nvM8Min18State.core.vals[q.1]?.getD 0#8
        v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) ⟨l, by omega⟩
      vals_true_iff := fun l hl => by
        refine ⟨fun hv => ?_, ?_⟩
        · have hc := (by decide : ∀ q : Fin 36,
            nvM8Min18State.core.vals[q.1]?.getD 0#8 = 1#8 →
            q.1 / 2 < 18 ∧ (nvM8Min18State.core.trl[q.1 / 2]?.getD 0#32).toNat = q.1)
            ⟨l, by omega⟩ hv
          exact ⟨l / 2, by omega, hc.2⟩
        · rintro ⟨i, hi, htr⟩
          have hc := (by decide : ∀ q : Fin 18,
            nvM8Min18State.core.vals[(nvM8Min18State.core.trl[q.1]?.getD 0#32).toNat]?.getD
              0#8 = 1#8) ⟨i, by omega⟩
          rw [← htr]; exact hc
      vals_false_iff := fun l hl => by
        refine ⟨fun hv => ?_, ?_⟩
        · have hc := (by decide : ∀ q : Fin 36,
            nvM8Min18State.core.vals[q.1]?.getD 0#8 = 0xFF#8 →
            q.1 / 2 < 18 ∧ (nvM8Min18State.core.trl[q.1 / 2]?.getD 0#32).toNat = q.1 ^^^ 1)
            ⟨l, by omega⟩ hv
          exact ⟨l / 2, by omega, hc.2⟩
        · rintro ⟨i, hi, htr⟩
          have hc := (by decide : ∀ q : Fin 18,
            nvM8Min18State.core.vals[(nvM8Min18State.core.trl[q.1]?.getD 0#32).toNat ^^^ 1]?.getD
              0#8 = 0xFF#8) ⟨i, by omega⟩
          have hl_eq : l = (nvM8Min18State.core.trl[i]?.getD 0#32).toNat ^^^ 1 := by
            rw [htr, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
          rw [hl_eq]; exact hc
      lvl_le := fun i hi => (by decide : ∀ q : Fin 18,
        (nvM8Min18State.core.lvl[(nvM8Min18State.core.trl[q.1]?.getD 0#32).toNat / 2]?.getD
          0#32).toNat ≤ 18) ⟨i, by omega⟩
      dec_earliest := fun i j hi hj hlv _ => by
        have heq := (by decide : ∀ a b : Fin 18,
          (nvM8Min18State.core.lvl[(nvM8Min18State.core.trl[a.1]?.getD 0#32).toNat / 2]?.getD
            0#32).toNat =
          (nvM8Min18State.core.lvl[(nvM8Min18State.core.trl[b.1]?.getD 0#32).toNat / 2]?.getD
            0#32).toNat → a.1 = b.1) ⟨i, by omega⟩ ⟨j, by omega⟩ hlv
        dsimp only at heq; omega
      levels_inhabited := fun L h1 h2 =>
        ⟨L - 1, by omega, (by decide : ∀ q : Fin 19, 1 ≤ q.1 → q.1 ≤ 18 →
          (nvM8Min18State.core.lvl[(nvM8Min18State.core.trl[q.1 - 1]?.getD 0#32).toNat / 2]?.getD
            0#32).toNat = q.1) ⟨L, by omega⟩ h1 (by omega)⟩
      level0_sound := fun i hi hlv => absurd hlv ((by decide : ∀ q : Fin 18,
        (nvM8Min18State.core.lvl[(nvM8Min18State.core.trl[q.1]?.getD 0#32).toNat / 2]?.getD
          0#32).toNat ≠ 0) ⟨i, by omega⟩)
      trail_pos_inv := fun i hi => (by decide : ∀ q : Fin 18,
        (nvM8Min18State.core.trail_pos[(nvM8Min18State.core.trl[q.1]?.getD 0#32).toNat / 2]?.getD
          0#32).toNat = q.1) ⟨i, by omega⟩
      level0_rsn_none := fun i hi _ => (by decide : ∀ q : Fin 18,
        nvM8Min18State.core.rsns[(nvM8Min18State.core.trl[q.1]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 = 0xFFFFFFFF#32) ⟨i, by omega⟩
      frame_trail_lt := fun L hL => (by decide : ∀ q : Fin 19,
        (nvM8Min18State.core.frame_trail[q.1]?.getD 0#32).toNat ≤ 18) ⟨L, by omega⟩
      frame_trail_mono := fun L1 L2 h12 hL2 => (by decide : ∀ a b : Fin 19, a.1 ≤ b.1 →
        (nvM8Min18State.core.frame_trail[a.1]?.getD 0#32).toNat ≤
        (nvM8Min18State.core.frame_trail[b.1]?.getD 0#32).toNat) ⟨L1, by omega⟩ ⟨L2, by omega⟩
        h12
      frame_trail_before_lt := fun L h1 h2 i hi =>
        (by decide : ∀ q : Fin 19, 1 ≤ q.1 → ∀ j : Fin 18,
          j.1 < (nvM8Min18State.core.frame_trail[q.1]?.getD 0#32).toNat →
          (nvM8Min18State.core.lvl[(nvM8Min18State.core.trl[j.1]?.getD 0#32).toNat / 2]?.getD
            0#32).toNat < q.1)
          ⟨L, by omega⟩ h1 ⟨i, by
            have hb := (by decide : ∀ q : Fin 19,
              (nvM8Min18State.core.frame_trail[q.1]?.getD 0#32).toNat ≤ 18) ⟨L, by omega⟩
            dsimp only at hb; omega⟩ hi
      frame_dec_lt := fun L h1 h2 => (by decide : ∀ q : Fin 19, 1 ≤ q.1 →
        (nvM8Min18State.core.frame_dec[q.1]?.getD 0#32).toNat < 36) ⟨L, by omega⟩ h1
      reason_inv := fun i hi hne => absurd ((by decide : ∀ q : Fin 18,
        nvM8Min18State.core.rsns[(nvM8Min18State.core.trl[q.1]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 = 0xFFFFFFFF#32) ⟨i, by omega⟩) hne
      reason_lit_mem := fun i hi hne => absurd ((by decide : ∀ q : Fin 18,
        nvM8Min18State.core.rsns[(nvM8Min18State.core.trl[q.1]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 = 0xFFFFFFFF#32) ⟨i, by omega⟩) hne }

private theorem nvM8Min18_marksClear : FullLitMarksClear nvM8Min18Cfg nvM8Min18State :=
  ⟨fun v hv => (by decide : ∀ q : Fin 18, nvM8Min18State.core.mrk[q.1]?.getD 0#8 = 0#8) ⟨v, hv⟩,
   fun l hl =>
     (by decide : ∀ q : Fin 36, nvM8Min18State.core.lit_mark[q.1]?.getD 0#8 = 0#8) ⟨l, hl⟩⟩

private theorem nvM8Min18_spec_inst {X : XPost} :
    m8MinShrinkSpec (nvM8Min18Cfg.hdr, ()) nvM8Min18Mem
      (fun () m' => ∃ (F_cur : List (List Nat)) (s' : FullState),
        s'.LengthsOk nvM8Min18Cfg ∧ 1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ 18 ∧
        s'.core.tmp[0]? = some 35#32 ∧ FullOtfsWitnessInv nvM8Min18Cfg nvM8F0 F_cur s'.core ∧
        nvM8F0.Unsat ∧ FullMem nvM8Min18Cfg s' m')
      X := by
  have hent : (cnfOfClauses [[0], [1]]).EntailsClause
      (cnfClause
        ((nvM8Min18State.core.tmp.take nvM8Min18State.core.tmp_len).map BitVec.toNat)) := by
    rw [CNF.entails_clause_def]; intro α hα; exfalso
    exact CNF.unsat_iff_not_sat.mp nvM8F0_unsat α (by simpa [nvM8F0] using hα)
  refine m8MinShrinkSpec_of nvM8Min18_lengths nvM8Min18_witness.toOtfs nvM8Min18_marksClear
    (by decide) (by decide) (by decide) hent
    (fun k hk => (by decide : ∀ q : Fin 18,
      let l := (nvM8Min18State.core.tmp[q.1]?.getD 0#32).toNat
      l < 36 ∧ nvM8Min18State.core.vals[l]?.getD 0#8 = 0xFF#8) ⟨k, hk⟩)
    (fun k hk1 hk2 => (by decide : ∀ q : Fin 18, 1 ≤ q.1 →
      let lv := (nvM8Min18State.core.lvl[(nvM8Min18State.core.tmp[q.1]?.getD 0#32).toNat / 2]?.getD
        0#32).toNat
      0 < lv ∧ lv < 18) ⟨k, hk2⟩ hk1)
    rfl nvM8Min18Mem_ok ?_
  intro tmp' tl' mrk' mclr' sstk' wsort' mcl' mcf' conf' llits' mrem' ticks' m'
    _s' hlen' hw' _ h1' hle' h0' _ _ _ hm'
  rw [sep_emp] at hm'
  exact ⟨[[0], [1]], _, hlen', h1', hle', h0', hw', nvM8F0_unsat, hm'⟩

/-- Concrete `Mem 64` 18-variable non-bailout UNSAT NV (`tmp_len = 18 > 16`, `XPost := False`):
`full_min_shrink_m6` under `m8CoreParityEnv` runs `full_sort_tmp`, `full_min_mark`,
`full_min_lit_dfs_m8`, `full_shrink_blk_bool_m8` preserving `FullOtfsWitnessInv`, `tmp[0] = 35#32`,
`1 ≤ tmp_len ≤ 18`, and `nvM8F0.Unsat`. -/
theorem nv_m8_min_shrink_m6 :
    Func.wp m8CoreParityEnv full_min_shrink_m6_body (nvM8Min18Cfg.hdr, ()) nvM8Min18Mem
      (fun () m' => ∃ (F_cur : List (List Nat)) (s' : FullState),
        s'.LengthsOk nvM8Min18Cfg ∧ 1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ 18 ∧
        s'.core.tmp[0]? = some 35#32 ∧ FullOtfsWitnessInv nvM8Min18Cfg nvM8F0 F_cur s'.core ∧
        nvM8F0.Unsat ∧ FullMem nvM8Min18Cfg s' m')
      (fun _ _ _ _ => False) :=
  m8CoreParityEnv_minShrinkM6_wp _ _ _ _ nvM8Min18_spec_inst

theorem nv_m8_min_shrink_m6_sw :
    Func.wp m8SweepV2CoreParityEnv full_min_shrink_m6_body (nvM8Min18Cfg.hdr, ()) nvM8Min18Mem
      (fun () m' => ∃ (F_cur : List (List Nat)) (s' : FullState),
        s'.LengthsOk nvM8Min18Cfg ∧ 1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ 18 ∧
        s'.core.tmp[0]? = some 35#32 ∧ FullOtfsWitnessInv nvM8Min18Cfg nvM8F0 F_cur s'.core ∧
        nvM8F0.Unsat ∧ FullMem nvM8Min18Cfg s' m')
      (fun _ _ _ _ => False) :=
  m8SweepV2CoreParityEnv_minShrinkM6_wp _ _ _ _ nvM8Min18_spec_inst

end LeanQbe.T.Examples.Kissat.FullM8CoreParity

end
