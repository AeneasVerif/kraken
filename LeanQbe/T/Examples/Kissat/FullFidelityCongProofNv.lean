/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityCong
public import LeanQbe.T.Examples.Kissat.FullFidelityCongProofSplice
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullCongLemmas1
import LeanQbe.T.Examples.Kissat.FullCongLemmas2
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.Bytes
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.OpsLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat 4.0.4 Congruence Parity Concrete `Mem 64` Non-Vacuity (`FullFidelityCongProofNv`)

Genuine non-bailout concrete `Mem 64` UNSAT non-vacuity proofs (`XPost := False`, `0` SAT model
proofs, zero disjunctive `b = true ∨ b = false` postconditions) exercising all four upstream
`congruence.c` parity fixes (`GAP-CONG-01..04`) and `BUG-CONG-00` under closed `fidCongEnv`
(`474` fns):
1. `nv_fid_cong_emit_xor4` (`GAP-CONG-02`): 4-literal XOR normalizer + 3-element sorting network.
2. `nv_fid_cong_and_match_wide33` (`GAP-CONG-01`): 33-input (`> 31`) AND matching with exact
   `r = true`.
3. `nv_fid_cong_ht_grow_clear_256k` (`GAP-CONG-03`): dynamic scratch HT scaling to `262,144`
   (`> 131,072`) buckets with symbolic `O(1)` memory framing.
4. `nv_fid_cong_sift_pairs` & `nv_fid_cong_sort_pairs` (`BUG-CONG-00`): equal-key pair heapsort
   ref tie-breaking (`[10, 1, 10, 2] → [10, 2, 10, 1]`) and `FidPairsOk` sorting.
5. `nv_fid_cong_merge_condeq_trivial_ite` (`GAP-CONG-04`): two-pointer conditional equivalence
   merge emitting trivial `e == t` ITE gate (`r = 5#32`).
6. `nv_fid_cong_eval_gate_xor_selfcancel` (`GAP-CONG-02` + UNSAT): XOR LHS self-cancellation to
   constant `false`, asserting `inconsistent = 1#64` and returning `r = 2#64`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityCong

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open LeanQbe.T.Examples.Kissat.FullM7CongIte
open Kraken.Bedrock2.Test
open scoped FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6CongSubst.M6HeadTactics

/-! ## 1. Shared Concrete Heap Builders & UNSAT Fixture (`nvFidF0`) -/

section Helpers

private theorem arrGetI32 {a : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop} {i : Nat}
    {m : Mem 64} (hi : i < xs.length) (h : (array (t := i32) a xs ⋆ F) m) :
    loadVal m i32 (a + BitVec.ofNat 64 (4 * i)) = some xs[i] :=
  loadVal_array (t := i32) (by decide) hi h

private theorem arrPutI32 {a : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop} {i : Nat}
    {m : Mem 64} (v : BitVec 32) (hi : i < xs.length) (h : (array (t := i32) a xs ⋆ F) m) :
    storeOk m i32 (a + BitVec.ofNat 64 (4 * i)) ∧
      (array (t := i32) a (xs.set i v) ⋆ F) (storeMem m i32 (a + BitVec.ofNat 64 (4 * i)) v) :=
  store_array (t := i32) v (by decide) hi h

private theorem c0_ld_arr32_m4 {a : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop}
    {i : BitVec 64} {m : Mem 64} (hi : i.toNat < xs.length)
    (h : (array (t := i32) a xs ⋆ F) m) :
    loadVal m i32 (a + i * 4) = some xs[i.toNat] := by
  rw [show a + i * 4 = a + BitVec.ofNat 64 (4 * i.toNat) by
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]]
  exact arrGetI32 hi h

private theorem c0_ld_arr32_add_m4 {a : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop}
    {i k : BitVec 64} {m : Mem 64} (hik : (i + k).toNat < xs.length)
    (h : (array (t := i32) a xs ⋆ F) m) :
    loadVal m i32 (a + (i + k) * 4) = some xs[(i + k).toNat] := by
  rw [show a + (i + k) * 4 = a + BitVec.ofNat 64 (4 * (i + k).toNat) by
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]]
  exact arrGetI32 hik h

private theorem c0_ld_arr32_0 {a : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop}
    {m : Mem 64} (h0 : 0 < xs.length) (h : (array (t := i32) a xs ⋆ F) m) :
    loadVal m i32 (a + 0) = some xs[0] := by
  simpa using arrGetI32 h0 h

private theorem c0_st_arr32_m4 {a : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop}
    {i : BitVec 64} {m : Mem 64} (v : BitVec 32) (hi : i.toNat < xs.length)
    (h : (array (t := i32) a xs ⋆ F) m) :
    storeOk m i32 (a + i * 4) ∧
      (array (t := i32) a (xs.set i.toNat v) ⋆ F) (storeMem m i32 (a + i * 4) v) := by
  rw [show a + i * 4 = a + BitVec.ofNat 64 (4 * i.toNat) by
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]]
  exact arrPutI32 v hi h

private theorem c0_st_arr32_zext0 {a : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (h0 : 0 < xs.length)
    (h : (array (t := i32) a xs ⋆ F) m) :
    storeOk m i32 (a + (0#32).setWidth 64 * 4) ∧
      (array (t := i32) a (xs.set 0 v) ⋆ F)
        (storeMem m i32 (a + (0#32).setWidth 64 * 4) v) := by
  simpa using arrPutI32 v h0 h

private theorem c0_st_arr32_0 {a : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (h0 : 0 < xs.length) (h : (array (t := i32) a xs ⋆ F) m) :
    storeOk m i32 (a + 0) ∧
      (array (t := i32) a (xs.set 0 v) ⋆ F) (storeMem m i32 (a + 0) v) := by
  simpa using arrPutI32 v h0 h

attribute [local c0_load] c0_ld_arr32_m4 c0_ld_arr32_add_m4 c0_ld_arr32_0
attribute [local c0_store] c0_st_arr32_m4 c0_st_arr32_zext0 c0_st_arr32_0

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

private theorem nv_array_eq_bytes {t : Ty} (a : BitVec 64) (xs : List (Val t))
    (h : t.bytes * xs.length ≤ 2 ^ 64) :
    array (t := t) a xs = Eq ((bytesOf xs).At a) := by
  induction xs generalizing a with
  | nil => rw [array_nil]; exact eq_nil_At a
  | cons x xs ih =>
    have hb : bytesOf (x :: xs) =
        Int.toBytes t.bytes ((toBits t x).setWidth (8 * t.bytes)).toInt ++ bytesOf xs := rfl
    have hl : (Int.toBytes t.bytes ((toBits t x).setWidth (8 * t.bytes)).toInt).length =
        t.bytes := @Int.toBytes_length _ _
    have hmul : t.bytes * (x :: xs).length = t.bytes + t.bytes * xs.length := by
      rw [List.length_cons, Nat.mul_succ, Nat.add_comm]
    rw [hmul] at h
    rw [array_cons, ih (a + BitVec.ofNat 64 t.bytes) (by omega), hb]
    have hcb : cell (t := t) a x =
        Eq ((Int.toBytes t.bytes ((toBits t x).setWidth (8 * t.bytes)).toInt).At a) := rfl
    rw [hcb, eq_append_At a _ _ (by rw [hl, bytesOf_length]; omega), hl]

private theorem nv_litEquiv_refl (F : CNF Nat) (l : Nat) : LitEquiv F l l := by
  constructor <;> rw [CNF.entails_clause_def] <;> intro α _ <;>
    rw [← clauseEvalVal_iff, clauseEvalVal] <;>
    simp only [List.any_cons, List.any_nil, Bool.or_false, evalLitVal_litNeg] <;>
    cases evalLitVal α l <;> rfl

private theorem litEquiv_empty_eq {l r : Nat} (h : LitEquiv (cnfOfClauses []) l r) : l = r := by
  have hsat : ∀ α : Nat → Bool, (cnfOfClauses []).Sat α := fun α =>
    (cnf_sat_cnfOfClauses_iff α []).mpr fun _ hc => nomatch hc
  have h0 := litEquiv_eval (hsat fun _ => false) h
  have h1 := litEquiv_eval (hsat fun k => decide (k = l / 2)) h
  have hev : ∀ α n, evalLitVal α n = (α (n / 2) != decide (n % 2 = 1)) := fun α n => by
    simp [evalLitVal, litVar, litSign]
    rcases Nat.mod_two_eq_zero_or_one n with hm | hm <;> simp [hm]
  rw [hev, hev] at h0 h1
  by_cases hdv : l / 2 = r / 2
  · rcases Nat.mod_two_eq_zero_or_one l with hl | hl <;>
      rcases Nat.mod_two_eq_zero_or_one r with hr | hr <;>
      simp [hl, hr] at h0 <;> omega
  · have hdl : decide (l / 2 = l / 2) = true := decide_eq_true rfl
    have hdr : decide (r / 2 = l / 2) = false := decide_eq_false (Ne.symm hdv)
    rw [hdl, hdr] at h1
    cases h1' : decide (l % 2 = 1) <;> cases h2' : decide (r % 2 = 1) <;>
      simp_all

private theorem nv_witness_empty {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hext : ExtUnsatSound F0 k.cur_vars F_cur)
    (hinc : k.inconsistent = 0#64) (hal : k.arena_len = 0)
    (hwvec : ∀ l < 2 * k.cur_vars, fullWatchOffCore k l = 0 ∧ fullWatchSizeCore k l = 0)
    (hte : k.trail_end = 0) (hcl : k.cur_level = 0)
    (hft0 : (k.frame_trail[0]?.getD 0#32).toNat = 0)
    (hvals : ∀ l < 2 * k.cur_vars, k.vals[l]?.getD 0#8 = 0#8) :
    FullWitnessInv c F0 F_cur k :=
  Full.fullWitnessInv_empty hext hinc hal hwvec hte hcl hft0 hvals

end Helpers

/-- UNSAT 4-variable base formula `{(x0), (~x0)}`. -/
def nvFidF0 : CNF Nat := cnfOfClauses [[0], [1]]

theorem nvFidF0_unsat : nvFidF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [nvFidF0, cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [nvFidF0, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

/-- Symbolic 4-variable arena geometry supporting any `sc < dimacsBound` scratch buffer. -/
def nvFidMkCfg4 (sc : Nat) (hsc : sc < dimacsBound) : FullCfg :=
  { hdr := 0x10000#64, avail := 2260 + 4 * sc, mv := 4, max_vars := 4, bva_cap := 0, nc := 1
    arena_cap := 0, wcap := 1, delayed_cap := 0, red_cap := 0, extend_cap := 0, scratch_cap := sc
    hbva := rfl, hmv := by decide, hmaxv := by decide, hnc := by decide, harena := by decide
    hwcap := by decide, hdel := by decide, hred := by decide, hext := by decide, hscr := hsc
    havail_fit := by
      change (0x10000#64 : BitVec 64).toNat + (2260 + 4 * sc) < 2 ^ 64
      rw [show (0x10000#64 : BitVec 64).toNat = 0x10000 by decide]
      unfold dimacsBound at hsc; omega
    hsize := by
      unfold fullFixedBytes valsBytes markBytes u32FullBytes fullMinDepthOf; split <;> omega }

def nvFidMkScratch4 (res_sz : BitVec 64) (wk1 wk2 scr : List (BitVec 32)) : FullScratch :=
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
    fwd_str_cnt := 0#64, ant_sz := 0#64, res_sz := res_sz
    walk_vals := List.replicate 8 0#8, phases := List.replicate 4 0#8
    phases_target := List.replicate 4 0#8, phases_best := List.replicate 4 0#8
    walk_best := List.replicate 4 0#8, heap := List.replicate 4 0#32
    pos := List.replicate 4 0#32, shrink_stk := List.replicate 4 0#32
    q_prev := List.replicate 4 0#32, q_next := List.replicate 4 0#32
    q_stamp := List.replicate 4 0#32, wsort := List.replicate 8 0#32
    work_stk1 := wk1, work_stk2 := wk2, tarjan_mark := List.replicate 8 0#32
    tarjan_reach := List.replicate 8 0#32, score := List.replicate 4 0#64
    sim_sig := List.replicate 4 0#64, glue_used := List.replicate 64 0#32
    last_learned := List.replicate 16 0xFFFFFFFF#32, delayed := [], red_refs := []
    extend_stk := [], scratch_buf := scr }

def nvFidMkCore4 (dm inc : BitVec 64) (te : Nat) (vals : List (BitVec 8))
    (trl repr tmp : List (BitVec 32)) : FullCoreState :=
  { d_cur := 0#64, d_val := 0#64, cur_vars := 4, unassigned := 0#64
    arena_len := 0, wlen := 0, wusable := 0#64, arena_garbage := 0#64
    first_reducible := 0#64, num_irred := 0#64, num_redundant := 0#64, num_binary := 0#64
    unflushed := 0#64, probing := 0#64, trail_end := te, propagated := 0
    cur_level := 0, fuel := 0#64, confl_ref := 0#64, confl_type := 0#64
    confl_lit0 := 0#64, confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0
    min_clr_len := 0, min_clr_full := 0#64, oom := 0#64, dense_mode := dm
    inconsistent := inc, vals := vals, lit_mark := List.replicate 8 0#8
    mrk := List.replicate 4 0#8, flags := List.replicate 4 0#32, lvl := List.replicate 4 0#32
    rsns := List.replicate 4 0xFFFFFFFF#32, trl := trl, trail_pos := List.replicate 4 0#32
    tmp := tmp, min_clr := List.replicate 4 0#32, frame_trail := List.replicate 5 0#32
    frame_dec := List.replicate 5 0#32, wvec := List.replicate 16 0#32, repr := repr
    min_stk := List.replicate 10 0#32, arena := [], wstk := [0#32] }

def nvFidMkState4 (dm inc res_sz : BitVec 64) (te : Nat) (vals : List (BitVec 8))
    (trl repr tmp wk1 wk2 scr : List (BitVec 32)) : FullState :=
  { core := nvFidMkCore4 dm inc te vals trl repr tmp
    scratch := nvFidMkScratch4 res_sz wk1 wk2 scr }

theorem nvFidMkState4_lengths {sc : Nat} {hsc : sc < dimacsBound} (dm inc res_sz : BitVec 64)
    (te : Nat) (vals : List (BitVec 8)) (trl repr tmp wk1 wk2 scr : List (BitVec 32))
    (hte : te ≤ 4) (hv : vals.length = 8) (htrl : trl.length = 4) (hr : repr.length = 8)
    (htmp : tmp.length = 4) (hw1 : wk1.length = 8) (hw2 : wk2.length = 8)
    (hscr : scr.length = sc) :
    (nvFidMkState4 dm inc res_sz te vals trl repr tmp wk1 wk2 scr).LengthsOk
      (nvFidMkCfg4 sc hsc) := by
  dsimp only [nvFidMkState4, nvFidMkCore4, nvFidMkScratch4, nvFidMkCfg4]
  refine ⟨⟨hv, rfl, rfl, rfl, rfl, rfl, htrl, rfl, htmp, rfl, rfl, rfl,
    by rw [List.length_replicate]; rfl, hr,
    by unfold FullCfg.minDepth fullMinDepthOf; rw [List.length_replicate]; rfl, rfl, rfl,
    Nat.le_refl _, Nat.le_refl _, Nat.zero_le _, Nat.zero_le _, hte, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hw1, hw2, rfl, rfl, rfl, rfl,
    by rw [List.length_replicate], by rw [List.length_replicate], rfl, rfl, rfl, hscr⟩⟩

private def nvFidBlkHdr4 (c : FullCfg) (s : FullState) : List UInt8 :=
  bytes64 [BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc, s.core.d_cur, s.core.d_val] ++
    bytes64 (Full.hdrTailWords c s)

private def nvFidBlkBytes4 (k : FullCoreState) (sc : FullScratch) : List UInt8 :=
  bytesOf (t := i8) k.vals ++ bytesOf (t := i8) sc.walk_vals ++ bytesOf (t := i8) k.lit_mark ++
  (bytesOf (t := i8) k.mrk ++ List.replicate 4 0) ++
  (bytesOf (t := i8) sc.phases ++ List.replicate 4 0) ++
  (bytesOf (t := i8) sc.phases_target ++ List.replicate 4 0) ++
  (bytesOf (t := i8) sc.phases_best ++ List.replicate 4 0) ++
  (bytesOf (t := i8) sc.walk_best ++ List.replicate 4 0)

private def nvFidBlkU32A4 (k : FullCoreState) : List UInt8 :=
  (bytesOf (t := i32) k.flags ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.lvl ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.rsns ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.trl ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.trail_pos ++ List.replicate 8 0)

private def nvFidBlkU32B4 (k : FullCoreState) (sc : FullScratch) : List UInt8 :=
  (bytesOf (t := i32) k.tmp ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.heap ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.pos ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.min_clr ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.shrink_stk ++ List.replicate 8 0)

private def nvFidBlkU32C4 (k : FullCoreState) (sc : FullScratch) : List UInt8 :=
  (bytesOf (t := i32) sc.q_prev ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.q_next ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.q_stamp ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.frame_trail ++ List.replicate 4 0) ++
  (bytesOf (t := i32) k.frame_dec ++ List.replicate 4 0)

private def nvFidBlkWvec4 (k : FullCoreState) (sc : FullScratch) : List UInt8 :=
  bytesOf (t := i32) k.wvec ++ bytesOf (t := i32) k.repr ++
  bytesOf (t := i32) sc.wsort ++ bytesOf (t := i32) sc.work_stk1 ++
  bytesOf (t := i32) sc.work_stk2 ++ bytesOf (t := i32) sc.tarjan_mark ++
  bytesOf (t := i32) sc.tarjan_reach ++ bytes64 sc.score ++ bytes64 sc.sim_sig

private def nvFidBlkTail4 (k : FullCoreState) (sc : FullScratch) : List UInt8 :=
  bytesOf (t := i32) k.min_stk ++ bytesOf (t := i32) sc.glue_used ++
  bytesOf (t := i32) sc.last_learned ++ bytesOf (t := i32) k.arena ++
  bytesOf (t := i32) k.wstk ++ bytesOf (t := i32) sc.delayed ++
  bytesOf (t := i32) sc.red_refs ++ bytesOf (t := i32) sc.extend_stk ++
  bytesOf (t := i32) sc.scratch_buf

def nvFidMkBytes4 (sc : Nat) (hsc : sc < dimacsBound) (dm inc res_sz : BitVec 64)
    (te : Nat) (vals : List (BitVec 8)) (trl repr tmp wk1 wk2 scr : List (BitVec 32)) :
    List UInt8 :=
  let c := nvFidMkCfg4 sc hsc
  let s := nvFidMkState4 dm inc res_sz te vals trl repr tmp wk1 wk2 scr
  nvFidBlkHdr4 c s ++ nvFidBlkBytes4 s.core s.scratch ++ nvFidBlkU32A4 s.core ++
    nvFidBlkU32B4 s.core s.scratch ++ nvFidBlkU32C4 s.core s.scratch ++
    nvFidBlkWvec4 s.core s.scratch ++ nvFidBlkTail4 s.core s.scratch

def nvFidMkMem4 (sc : Nat) (hsc : sc < dimacsBound) (dm inc res_sz : BitVec 64) (te : Nat)
    (vals : List (BitVec 8)) (trl repr tmp wk1 wk2 scr : List (BitVec 32)) : Mem 64 :=
  (nvFidMkBytes4 sc hsc dm inc res_sz te vals trl repr tmp wk1 wk2 scr).At 0x10000#64

private theorem nv_ptr2 (p : BitVec 64) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) :=
  ptr_add_ofNat p a b

theorem nvFidMkMem4_ok {sc : Nat} {hsc : sc < dimacsBound} (dm inc res_sz : BitVec 64) (te : Nat)
    (vals : List (BitVec 8)) (trl repr tmp wk1 wk2 scr : List (BitVec 32))
    (hv : vals.length = 8) (htrl : trl.length = 4) (hr : repr.length = 8)
    (htmp : tmp.length = 4) (hw1 : wk1.length = 8) (hw2 : wk2.length = 8)
    (hscr : scr.length = sc) :
    (FullMem (nvFidMkCfg4 sc hsc) (nvFidMkState4 dm inc res_sz te vals trl repr tmp wk1 wk2 scr) ⋆
      emp) (nvFidMkMem4 sc hsc dm inc res_sz te vals trl repr tmp wk1 wk2 scr) := by
  rw [sep_emp]
  let c := nvFidMkCfg4 sc hsc
  let s := nvFidMkState4 dm inc res_sz te vals trl repr tmp wk1 wk2 scr
  have hd_sc := hsc; unfold dimacsBound at hd_sc
  have hm4v : c.max_vars = 4 := rfl
  have hv0 : valsBytes c.max_vars - 2 * c.max_vars = 0 := by rw [hm4v]; decide
  have h2m : 2 * c.max_vars = 8 := by rw [hm4v]
  have hm4 : markBytes c.max_vars - c.max_vars = 4 := by rw [hm4v]; decide
  have hu8 : u32FullBytes c.max_vars - 4 * c.max_vars = 8 := by rw [hm4v]; decide
  have h4m : 4 * c.max_vars = 16 := by rw [hm4v]
  have hu4 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 4 := by rw [hm4v]; decide
  have h4p : 4 * (c.max_vars + 1) = 20 := by rw [hm4v]
  have hvb : valsBytes c.max_vars = 8 := by rw [hm4v]; decide
  have hmkb : markBytes c.max_vars = 8 := by rw [hm4v]; decide
  have hu32b : u32FullBytes c.max_vars = 24 := by rw [hm4v]; decide
  have hmd : c.minDepth = 5 := by unfold FullCfg.minDepth fullMinDepthOf; rw [hm4v]; decide
  have harc : c.arena_cap = 0 := rfl
  have hwc : c.wcap = 1 := rfl
  have hdc : c.delayed_cap = 0 := rfl
  have hrc : c.red_cap = 0 := rfl
  have hec : c.extend_cap = 0 := rfl
  have hsl : c.slack = 0 := by
    dsimp only [c, nvFidMkCfg4, FullCfg.slack]
    unfold fullFixedBytes valsBytes markBytes u32FullBytes fullMinDepthOf; split <;> omega
  have hp_sl : c.pSlack = c.pScratchBuf + BitVec.ofNat 64 (4 * sc) := rfl
  have hHdr : (nvFidBlkHdr4 c s).length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        array64 (c.hdr + 32) (Full.hdrTailWords c s)) ((nvFidBlkHdr4 c s).At c.hdr) :=
    nv_join_pair
      ⟨rfl, dimacsState_bytes c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val⟩
      (nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide))
      rfl (by rw [bytes64_length]; simp only [List.length_cons, List.length_nil]; decide)
  have hBytes : (nvFidBlkBytes4 s.core s.scratch).length = 64 ∧
      ((array (t := i8) c.pVals s.core.vals ⋆ array (t := i8) c.pLitMark s.core.lit_mark ⋆
          array (t := i8) c.pMark s.core.mrk) ⋆
        FullScrByteArrs c s.scratch ⋆ c.padBytes)
        ((nvFidBlkBytes4 s.core s.scratch).At c.pVals) := by
    have h1 := nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 8 0
      (by change 1 * vals.length = 8; omega) (by decide)
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
    have h1' : (bytesOf (t := i8) s.core.vals).length = 8 ∧
        (array (t := i8) c.pVals s.core.vals ⋆
          region (c.pVals + BitVec.ofNat 64 8) 0) ((bytesOf (t := i8) s.core.vals).At c.pVals) := by
      simpa using h1
    have h2' : (bytesOf (t := i8) s.scratch.walk_vals).length = 8 ∧
        (array (t := i8) c.pWalkVals s.scratch.walk_vals ⋆
          region (c.pWalkVals + BitVec.ofNat 64 8) 0)
          ((bytesOf (t := i8) s.scratch.walk_vals).At c.pWalkVals) := by
      simpa using h2
    have h3' : (bytesOf (t := i8) s.core.lit_mark).length = 8 ∧
        (array (t := i8) c.pLitMark s.core.lit_mark ⋆
          region (c.pLitMark + BitVec.ofNat 64 8) 0)
          ((bytesOf (t := i8) s.core.lit_mark).At c.pLitMark) := by
      simpa using h3
    have j12 := nv_join_pair h1' h2' (by rw [FullCfg.pWalkVals, hvb]) (by decide)
    have j123 := nv_join_pair j12 h3' (by rw [FullCfg.pLitMark, FullCfg.pWalkVals, hvb, nv_ptr2])
      (by decide)
    have j1234 := nv_join_pair j123 h4
      (by rw [FullCfg.pMark, FullCfg.pLitMark, FullCfg.pWalkVals, hvb, nv_ptr2, nv_ptr2])
      (by decide)
    have j12345 := nv_join_pair j1234 h5
      (by rw [FullCfg.pPhases, FullCfg.pMark, FullCfg.pLitMark, FullCfg.pWalkVals, hvb, hmkb,
        nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    have j123456 := nv_join_pair j12345 h6
      (by rw [FullCfg.pPhasesTarget, FullCfg.pPhases, FullCfg.pMark, FullCfg.pLitMark,
        FullCfg.pWalkVals, hvb, hmkb, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    have j1234567 := nv_join_pair j123456 h7
      (by rw [FullCfg.pPhasesBest, FullCfg.pPhasesTarget, FullCfg.pPhases, FullCfg.pMark,
        FullCfg.pLitMark, FullCfg.pWalkVals, hvb, hmkb, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2,
        nv_ptr2]) (by decide)
    have j12345678 := nv_join_pair j1234567 h8
      (by rw [FullCfg.pWalkBest, FullCfg.pPhasesBest, FullCfg.pPhasesTarget, FullCfg.pPhases,
        FullCfg.pMark, FullCfg.pLitMark, FullCfg.pWalkVals, hvb, hmkb, nv_ptr2, nv_ptr2, nv_ptr2,
        nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    exact nv_sep_reorg j12345678 fun _ hm => by
      have pB : ∀ {A1 A2 A3 A4 A5 A6 A7 A8 P1 P2 P3 P4 P5 P6 P7 P8 : Mem 64 → Prop} {k},
          ((((((((A1 ⋆ P1) ⋆ (A2 ⋆ P2)) ⋆ (A3 ⋆ P3)) ⋆ (A4 ⋆ P4)) ⋆
            (A5 ⋆ P5)) ⋆ (A6 ⋆ P6)) ⋆ (A7 ⋆ P7)) ⋆ (A8 ⋆ P8)) k →
          ((A1 ⋆ A3 ⋆ A4) ⋆ (A2 ⋆ A5 ⋆ A6 ⋆ A7 ⋆ A8) ⋆
            (P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6 ⋆ P7 ⋆ P8)) k := fun x => sep_ac x
      unfold FullScrByteArrs FullCfg.padBytes; rw [hv0, h2m, hm4, hm4v]; exact pB hm
  have hU32A : (nvFidBlkU32A4 s.core).length = 120 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        ((nvFidBlkU32A4 s.core).At c.pFlags) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 16 8 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 16 8 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 16 8 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 16 8
      (by change 4 * trl.length = 16; omega) (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 16 8
      rfl (by decide)
    have j12 := nv_join_pair h1 h2 (by rw [FullCfg.pLevel, hu32b]) (by decide)
    have j123 := nv_join_pair j12 h3 (by rw [FullCfg.pReason, FullCfg.pLevel, hu32b, nv_ptr2])
      (by decide)
    have j1234 := nv_join_pair j123 h4
      (by rw [FullCfg.pTrail, FullCfg.pReason, FullCfg.pLevel, hu32b, nv_ptr2, nv_ptr2]) (by decide)
    have j12345 := nv_join_pair j1234 h5
      (by rw [FullCfg.pTrailPos, FullCfg.pTrail, FullCfg.pReason, FullCfg.pLevel, hu32b,
        nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    exact nv_sep_reorg j12345 fun _ hm => by
      unfold FullCfg.padU32A; rw [hu8, h4m]; exact sep_ac hm
  have hU32B : (nvFidBlkU32B4 s.core s.scratch).length = 120 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pHeap s.scratch.heap ⋆
        array (t := i32) c.pPos s.scratch.pos ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
        array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        ((nvFidBlkU32B4 s.core s.scratch).At c.pTmp) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 16 8
      (by change 4 * tmp.length = 16; omega) (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 16 8 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 16 8 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 16 8 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk) 16 8
      rfl (by decide)
    have j12 := nv_join_pair h1 h2 (by rw [FullCfg.pHeap, hu32b]) (by decide)
    have j123 := nv_join_pair j12 h3 (by rw [FullCfg.pPos, FullCfg.pHeap, hu32b, nv_ptr2])
      (by decide)
    have j1234 := nv_join_pair j123 h4
      (by rw [FullCfg.pMinClr, FullCfg.pPos, FullCfg.pHeap, hu32b, nv_ptr2, nv_ptr2]) (by decide)
    have j12345 := nv_join_pair j1234 h5
      (by rw [FullCfg.pShrinkStk, FullCfg.pMinClr, FullCfg.pPos, FullCfg.pHeap, hu32b,
        nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    exact nv_sep_reorg j12345 fun _ hm => by
      unfold FullCfg.padU32B; rw [hu8, h4m]; exact sep_ac hm
  have hU32C : (nvFidBlkU32C4 s.core s.scratch).length = 120 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        ((nvFidBlkU32C4 s.core s.scratch).At c.pQPrev) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 16 8 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 16 8 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 16 8
      rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 20 4
      rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 20 4
      rfl (by decide)
    have j12 := nv_join_pair h1 h2 (by rw [FullCfg.pQNext, hu32b]) (by decide)
    have j123 := nv_join_pair j12 h3 (by rw [FullCfg.pQStamp, FullCfg.pQNext, hu32b, nv_ptr2])
      (by decide)
    have j1234 := nv_join_pair j123 h4
      (by rw [FullCfg.pFrameTrail, FullCfg.pQStamp, FullCfg.pQNext, hu32b, nv_ptr2, nv_ptr2])
      (by decide)
    have j12345 := nv_join_pair j1234 h5
      (by rw [FullCfg.pFrameDec, FullCfg.pFrameTrail, FullCfg.pQStamp, FullCfg.pQNext, hu32b,
        nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    exact nv_sep_reorg j12345 fun _ hm => by
      unfold FullCfg.padU32C; rw [hu8, hu4, h4m, h4p]; exact sep_ac hm
  have hWvec : (nvFidBlkWvec4 s.core s.scratch).length = 320 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        ((nvFidBlkWvec4 s.core s.scratch).At c.pWvec) := by
    have h1 := nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 64
      (by change 4 * (List.replicate 16 (0#32 : BitVec 32)).length = 64; rw [List.length_replicate])
      (by decide)
    have h2 := nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 32
      (by change 4 * repr.length = 32; omega) (by decide)
    have h3 := nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 32 rfl (by decide)
    have h4 := nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 32
      (by change 4 * wk1.length = 32; omega) (by decide)
    have h5 := nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 32
      (by change 4 * wk2.length = 32; omega) (by decide)
    have h6 := nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 32
      rfl (by decide)
    have h7 := nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 32
      rfl (by decide)
    have h8 := nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 32 rfl (by decide)
    have h9 := nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 32 rfl (by decide)
    have j12 := nv_join_pair h1 h2 (by rw [FullCfg.pRepr, hm4v]) (by decide)
    have j123 := nv_join_pair j12 h3 (by rw [FullCfg.pWsort, FullCfg.pRepr, hm4v, nv_ptr2])
      (by decide)
    have j1234 := nv_join_pair j123 h4
      (by rw [FullCfg.pWorkStk1, FullCfg.pWsort, FullCfg.pRepr, hm4v, nv_ptr2, nv_ptr2]) (by decide)
    have j12345 := nv_join_pair j1234 h5
      (by rw [FullCfg.pWorkStk2, FullCfg.pWorkStk1, FullCfg.pWsort, FullCfg.pRepr, hm4v,
        nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    have j123456 := nv_join_pair j12345 h6
      (by rw [FullCfg.pTarjanMark, FullCfg.pWorkStk2, FullCfg.pWorkStk1, FullCfg.pWsort,
        FullCfg.pRepr, hm4v, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    have j1234567 := nv_join_pair j123456 h7
      (by rw [FullCfg.pTarjanReach, FullCfg.pTarjanMark, FullCfg.pWorkStk2, FullCfg.pWorkStk1,
        FullCfg.pWsort, FullCfg.pRepr, hm4v, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2])
      (by decide)
    have j12345678 := nv_join_pair j1234567 h8
      (by rw [FullCfg.pScore, FullCfg.pTarjanReach, FullCfg.pTarjanMark, FullCfg.pWorkStk2,
        FullCfg.pWorkStk1, FullCfg.pWsort, FullCfg.pRepr, hm4v, nv_ptr2, nv_ptr2, nv_ptr2,
        nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    have j123456789 := nv_join_pair j12345678 h9
      (by rw [FullCfg.pSimSig, FullCfg.pScore, FullCfg.pTarjanReach, FullCfg.pTarjanMark,
        FullCfg.pWorkStk2, FullCfg.pWorkStk1, FullCfg.pWsort, FullCfg.pRepr, hm4v, nv_ptr2,
        nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    exact nv_sep_reorg j123456789 fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail : (nvFidBlkTail4 s.core s.scratch).length = 364 + 4 * sc ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        ((nvFidBlkTail4 s.core s.scratch).At c.pMinStk) := by
    have h1 := nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 40
      (by change 4 * (List.replicate 10 (0#32 : BitVec 32)).length = 40; rw [List.length_replicate])
      (by decide)
    have h2 := nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256
      (by change 4 * (List.replicate 64 (0#32 : BitVec 32)).length = 256
          rw [List.length_replicate])
      (by decide)
    have h3 := nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned) 64
      (by change 4 * (List.replicate 16 (0xFFFFFFFF#32 : BitVec 32)).length = 64
          rw [List.length_replicate])
      (by decide)
    have h4 := nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 0 rfl (by decide)
    have h5 := nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 4 rfl (by decide)
    have h6 := nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl (by decide)
    have h7 := nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl (by decide)
    have h8 := nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl
      (by decide)
    have h9 := nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) (4 * sc)
      (by change 4 * scr.length = 4 * sc; omega) (by omega)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 (0 : UInt8)).At c.pSlack) := by
      rw [hsl]; exact nv_pad_p c.pSlack 0
    have j12 := nv_join_pair h1 h2 (by rw [FullCfg.pGlueUsed, hmd]) (by decide)
    have j123 := nv_join_pair j12 h3 (by rw [FullCfg.pLastLearned, FullCfg.pGlueUsed, hmd, nv_ptr2])
      (by decide)
    have j1234 := nv_join_pair j123 h4
      (by rw [FullCfg.pArena, FullCfg.pLastLearned, FullCfg.pGlueUsed, hmd, nv_ptr2, nv_ptr2])
      (by decide)
    have j12345 := nv_join_pair j1234 h5
      (by rw [FullCfg.pWstk, FullCfg.pArena, FullCfg.pLastLearned, FullCfg.pGlueUsed, hmd, harc,
        nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    have j123456 := nv_join_pair j12345 h6
      (by rw [FullCfg.pDelayed, FullCfg.pWstk, FullCfg.pArena, FullCfg.pLastLearned,
        FullCfg.pGlueUsed, hmd, harc, hwc, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    have j1234567 := nv_join_pair j123456 h7
      (by rw [FullCfg.pRedRefs, FullCfg.pDelayed, FullCfg.pWstk, FullCfg.pArena,
        FullCfg.pLastLearned, FullCfg.pGlueUsed, hmd, harc, hwc, hdc, nv_ptr2, nv_ptr2, nv_ptr2,
        nv_ptr2, nv_ptr2]) (by decide)
    have j12345678 := nv_join_pair j1234567 h8
      (by rw [FullCfg.pExtendStk, FullCfg.pRedRefs, FullCfg.pDelayed, FullCfg.pWstk, FullCfg.pArena,
        FullCfg.pLastLearned, FullCfg.pGlueUsed, hmd, harc, hwc, hdc, hrc, nv_ptr2, nv_ptr2,
        nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    have j123456789 := nv_join_pair j12345678 h9
      (by rw [FullCfg.pScratchBuf, FullCfg.pExtendStk, FullCfg.pRedRefs, FullCfg.pDelayed,
        FullCfg.pWstk, FullCfg.pArena, FullCfg.pLastLearned, FullCfg.pGlueUsed, hmd, harc, hwc,
        hdc, hrc, hec, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2]) (by omega)
    have j123456789' : (nvFidBlkTail4 s.core s.scratch).length = 364 + 4 * sc ∧
        (((((((((array (t := i32) c.pMinStk s.core.min_stk ⋆
          array (t := i32) c.pGlueUsed s.scratch.glue_used) ⋆
          array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
          array (t := i32) c.pArena s.core.arena) ⋆ array (t := i32) c.pWstk s.core.wstk) ⋆
          array (t := i32) c.pDelayed s.scratch.delayed) ⋆
          array (t := i32) c.pRedRefs s.scratch.red_refs) ⋆
          array (t := i32) c.pExtendStk s.scratch.extend_stk) ⋆
          array (t := i32) c.pScratchBuf s.scratch.scratch_buf))
          ((nvFidBlkTail4 s.core s.scratch).At c.pMinStk) :=
      ⟨by have hlen := j123456789.1; dsimp [nvFidBlkTail4] at hlen ⊢; omega, j123456789.2⟩
    have j10 : (nvFidBlkTail4 s.core s.scratch ++ List.replicate 0 (0 : UInt8)).length =
        (364 + 4 * sc) + 0 ∧
        ((((((((((array (t := i32) c.pMinStk s.core.min_stk ⋆
          array (t := i32) c.pGlueUsed s.scratch.glue_used) ⋆
          array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
          array (t := i32) c.pArena s.core.arena) ⋆ array (t := i32) c.pWstk s.core.wstk) ⋆
          array (t := i32) c.pDelayed s.scratch.delayed) ⋆
          array (t := i32) c.pRedRefs s.scratch.red_refs) ⋆
          array (t := i32) c.pExtendStk s.scratch.extend_stk) ⋆
          array (t := i32) c.pScratchBuf s.scratch.scratch_buf) ⋆
          region c.pSlack c.slack))
          ((nvFidBlkTail4 s.core s.scratch ++ List.replicate 0 (0 : UInt8)).At c.pMinStk) :=
      nv_join_pair j123456789' h10
        (by rw [hp_sl, FullCfg.pScratchBuf, FullCfg.pExtendStk, FullCfg.pRedRefs, FullCfg.pDelayed,
          FullCfg.pWstk, FullCfg.pArena, FullCfg.pLastLearned, FullCfg.pGlueUsed, hmd, harc, hwc,
          hdc, hrc, hec]; repeat rw [nv_ptr2]
            exact congrArg (c.pMinStk + BitVec.ofNat 64 ·) (by omega)) (by omega)
    have j10' : (nvFidBlkTail4 s.core s.scratch).length = 364 + 4 * sc ∧
        ((((((((((array (t := i32) c.pMinStk s.core.min_stk ⋆
          array (t := i32) c.pGlueUsed s.scratch.glue_used) ⋆
          array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
          array (t := i32) c.pArena s.core.arena) ⋆ array (t := i32) c.pWstk s.core.wstk) ⋆
          array (t := i32) c.pDelayed s.scratch.delayed) ⋆
          array (t := i32) c.pRedRefs s.scratch.red_refs) ⋆
          array (t := i32) c.pExtendStk s.scratch.extend_stk) ⋆
          array (t := i32) c.pScratchBuf s.scratch.scratch_buf) ⋆
          region c.pSlack c.slack)) ((nvFidBlkTail4 s.core s.scratch).At c.pMinStk) := by
      simpa using j10
    exact nv_sep_reorg j10' fun _ hm => by
      unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := nv_join_pair hHdr hBytes (rfl) (by decide)
  have h02 := nv_join_pair h01 hU32A
    (by rw [FullCfg.pFlags, FullCfg.pWalkBest, FullCfg.pPhasesBest, FullCfg.pPhasesTarget,
      FullCfg.pPhases, FullCfg.pMark, FullCfg.pLitMark, FullCfg.pWalkVals, FullCfg.pVals,
      hvb, hmkb]; repeat rw [nv_ptr2]) (by decide)
  have h03 := nv_sep_reorg (nv_join_pair h02 hU32B
    (by rw [FullCfg.pTmp, FullCfg.pTrailPos, FullCfg.pTrail, FullCfg.pReason, FullCfg.pLevel,
      FullCfg.pFlags, FullCfg.pWalkBest, FullCfg.pPhasesBest, FullCfg.pPhasesTarget,
      FullCfg.pPhases, FullCfg.pMark, FullCfg.pLitMark, FullCfg.pWalkVals, FullCfg.pVals,
      hvb, hmkb, hu32b]; repeat rw [nv_ptr2]) (by decide)) fun _ hm => by
    have p1 : ∀ {D H CB SB PB UA PA T Hp Ps Mc Sh PB2 : Mem 64 → Prop} {k},
        (((D ⋆ H) ⋆ (CB ⋆ SB ⋆ PB)) ⋆ (UA ⋆ PA) ⋆ ((T ⋆ Hp ⋆ Ps ⋆ Mc ⋆ Sh) ⋆ PB2)) k →
        ((D ⋆ H) ⋆ ((CB ⋆ (UA ⋆ T ⋆ Mc)) ⋆ (SB ⋆ (Hp ⋆ Ps ⋆ Sh)) ⋆ (PB ⋆ PA ⋆ PB2))) k :=
      fun x => sep_ac x
    exact p1 hm
  have h04 := nv_sep_reorg (nv_join_pair h03 hU32C
    (by rw [FullCfg.pQPrev, FullCfg.pShrinkStk, FullCfg.pMinClr, FullCfg.pPos, FullCfg.pHeap,
      FullCfg.pTmp, FullCfg.pTrailPos, FullCfg.pTrail, FullCfg.pReason, FullCfg.pLevel,
      FullCfg.pFlags, FullCfg.pWalkBest, FullCfg.pPhasesBest, FullCfg.pPhasesTarget,
      FullCfg.pPhases, FullCfg.pMark, FullCfg.pLitMark, FullCfg.pWalkVals, FullCfg.pVals,
      hvb, hmkb, hu32b]; repeat rw [nv_ptr2]) (by decide)) fun _ hm => by
    have p2 : ∀ {DH C1 S1 P1 Qp Qn Qs FTr FDec PC : Mem 64 → Prop} {k},
        ((DH ⋆ (C1 ⋆ S1 ⋆ P1)) ⋆ ((Qp ⋆ Qn ⋆ Qs) ⋆ (FTr ⋆ FDec) ⋆ PC)) k →
        (DH ⋆ ((C1 ⋆ FTr ⋆ FDec) ⋆ (S1 ⋆ (Qp ⋆ Qn ⋆ Qs)) ⋆ (P1 ⋆ PC))) k := fun x => sep_ac x
    exact p2 hm
  have h05 := nv_join_pair h04 hWvec
    (by rw [FullCfg.pWvec, FullCfg.pFrameDec, FullCfg.pFrameTrail, FullCfg.pQStamp, FullCfg.pQNext,
      FullCfg.pQPrev, FullCfg.pShrinkStk, FullCfg.pMinClr, FullCfg.pPos, FullCfg.pHeap,
      FullCfg.pTmp, FullCfg.pTrailPos, FullCfg.pTrail, FullCfg.pReason, FullCfg.pLevel,
      FullCfg.pFlags, FullCfg.pWalkBest, FullCfg.pPhasesBest, FullCfg.pPhasesTarget,
      FullCfg.pPhases, FullCfg.pMark, FullCfg.pLitMark, FullCfg.pWalkVals, FullCfg.pVals,
      hvb, hmkb, hu32b]; repeat rw [nv_ptr2]) (by decide)
  have h06 := nv_join_pair h05 hTail
    (by rw [FullCfg.pMinStk, FullCfg.pSimSig, FullCfg.pScore, FullCfg.pTarjanReach,
      FullCfg.pTarjanMark, FullCfg.pWorkStk2, FullCfg.pWorkStk1, FullCfg.pWsort, FullCfg.pRepr,
      FullCfg.pWvec, FullCfg.pFrameDec, FullCfg.pFrameTrail, FullCfg.pQStamp, FullCfg.pQNext,
      FullCfg.pQPrev, FullCfg.pShrinkStk, FullCfg.pMinClr, FullCfg.pPos, FullCfg.pHeap,
      FullCfg.pTmp, FullCfg.pTrailPos, FullCfg.pTrail, FullCfg.pReason, FullCfg.pLevel,
      FullCfg.pFlags, FullCfg.pWalkBest, FullCfg.pPhasesBest, FullCfg.pPhasesTarget,
      FullCfg.pPhases, FullCfg.pMark, FullCfg.pLitMark, FullCfg.pWalkVals, FullCfg.pVals,
      hvb, hmkb, hu32b, hm4v]; repeat rw [nv_ptr2]) (by omega)
  exact (nv_sep_reorg h06 fun _ hm => by
    have p3 : ∀ {D H CoreB ScrB P2 Wv Re SW Sc Ss MS Gu Ll CD SD SL : Mem 64 → Prop} {k},
        (((D ⋆ H ⋆ (CoreB ⋆ ScrB ⋆ P2)) ⋆ ((Wv ⋆ Re) ⋆ SW ⋆ (Sc ⋆ Ss))) ⋆
          (MS ⋆ (Gu ⋆ Ll) ⋆ CD ⋆ SD ⋆ SL)) k →
        (D ⋆ H ⋆ (CoreB ⋆ Wv ⋆ Re ⋆ MS ⋆ CD) ⋆
          (ScrB ⋆ SW ⋆ Sc ⋆ Ss ⋆ Gu ⋆ Ll ⋆ SD) ⋆ (P2 ⋆ SL)) k :=
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
    exact p7 (p6 (p5 (p4 (p3 hm))))).2

private theorem nvFidMk4_witness_empty {sc : Nat} {hsc : sc < dimacsBound}
    {dm res_sz : BitVec 64} {trl repr tmp wk1 wk2 scr : List (BitVec 32)} :
    FullWitnessInv (nvFidMkCfg4 sc hsc) nvFidF0 []
      (nvFidMkState4 dm 0#64 res_sz 0 (List.replicate 8 0#8) trl repr tmp wk1 wk2 scr).core :=
  nv_witness_empty
    ⟨(fun _ h => nomatch h), fun hu => False.elim (by
      rw [CNF.unsat_iff_not_sat] at hu
      exact hu (fun _ => false)
        ((cnf_sat_cnfOfClauses_iff (fun _ => false) []).mpr fun _ hc => nomatch hc))⟩
    rfl rfl (fun l hl => by
      have hcv : (nvFidMkState4 dm 0#64 res_sz 0 (List.replicate 8 0#8) trl repr tmp
          wk1 wk2 scr).core.cur_vars = 4 := rfl
      rw [hcv] at hl
      have hwv : (nvFidMkState4 dm 0#64 res_sz 0 (List.replicate 8 0#8) trl repr tmp
          wk1 wk2 scr).core.wvec = List.replicate 16 0#32 := rfl
      unfold fullWatchOffCore fullWatchSizeCore; rw [hwv]
      simp only [List.getElem?_replicate, show 2 * l < 16 by omega, show 2 * l + 1 < 16 by omega,
        ↓reduceIte, Option.getD_some]
      exact ⟨rfl, rfl⟩)
    rfl rfl rfl (fun l hl => by
      have hcv : (nvFidMkState4 dm 0#64 res_sz 0 (List.replicate 8 0#8) trl repr tmp
          wk1 wk2 scr).core.cur_vars = 4 := rfl
      rw [hcv] at hl
      have hv : (nvFidMkState4 dm 0#64 res_sz 0 (List.replicate 8 0#8) trl repr tmp
          wk1 wk2 scr).core.vals = List.replicate 8 0#8 := rfl
      rw [hv]
      simp only [List.getElem?_replicate, show l < 8 by omega, ↓reduceIte, Option.getD_some])

/-! ## 2. `full_cong_emit_xor4` Concrete 4-Lit XOR NV (`GAP-CONG-02`) -/

def nvFidXor4Cfg : FullCfg := nvFidMkCfg4 5 (by decide)

def nvFidXor4StEnd : FullState :=
  nvFidMkState4 0#64 0#64 0#64 0 (List.replicate 8 0#8) (List.replicate 4 0#32)
    (List.replicate 8 0#32) (List.replicate 4 0#32) (List.replicate 8 0#32) (List.replicate 8 0#32)
    [5#32, (1#32 <<< 28#32) ||| 3#32, 0#32, 2#32, 6#32]

def nvFidXor4Mem0 : Mem 64 :=
  nvFidMkMem4 5 (by decide) 0#64 0#64 0#64 0 (List.replicate 8 0#8) (List.replicate 4 0#32)
    (List.replicate 8 0#32) (List.replicate 4 0#32) (List.replicate 8 0#32) (List.replicate 8 0#32)
    (List.replicate 5 0#32)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`): `full_cong_emit_xor4` under `fidCongEnv`
normalizes parity sign (`4#32 → 5#32`) and executes all three swaps of the 3-input sorting
network (`6#32, 2#32, 0#32 → 0#32, 2#32, 6#32`). -/
theorem nv_fid_cong_emit_xor4 :
    Func.wp fidCongEnv full_cong_emit_xor4_body
      (nvFidXor4Cfg.pScratchBuf, 0#64, 4#32, 6#32, 2#32, 0#32, ()) nvFidXor4Mem0
      (fun (r, ()) m' =>
        r = 5#64 ∧
        nvFidXor4StEnd.scratch.scratch_buf =
          [5#32, (1#32 <<< 28#32) ||| 3#32, 0#32, 2#32, 6#32] ∧
        nvFidXor4StEnd.LengthsOk nvFidXor4Cfg ∧
        FullWitnessInv nvFidXor4Cfg nvFidF0 [] nvFidXor4StEnd.core ∧
        nvFidF0.Unsat ∧ FullMem nvFidXor4Cfg nvFidXor4StEnd m')
      (fun _ _ _ _ => False) := by
  let st0 := nvFidMkState4 0#64 0#64 0#64 0 (List.replicate 8 0#8) (List.replicate 4 0#32)
    (List.replicate 8 0#32) (List.replicate 4 0#32) (List.replicate 8 0#32) (List.replicate 8 0#32)
    (List.replicate 5 0#32)
  have hm0 := focus_full_scratch_buf (nvFidMkMem4_ok (sc := 5) (hsc := by decide)
    0#64 0#64 0#64 0 (List.replicate 8 0#8) (List.replicate 4 0#32) (List.replicate 8 0#32)
    (List.replicate 4 0#32) (List.replicate 8 0#32) (List.replicate 8 0#32)
    (List.replicate 5 0#32) rfl rfl rfl rfl rfl rfl rfl)
  change (array (t := i32) nvFidXor4Cfg.pScratchBuf st0.scratch.scratch_buf ⋆
    (FullScrBufRest nvFidXor4Cfg st0 ⋆ emp)) nvFidXor4Mem0 at hm0
  unfold Func.wp full_cong_emit_xor4_body
  m6_to_group
  refine wp_join_group (ts := [i32, i32])
    (fun (a, b, ()) m => m = nvFidXor4Mem0 ∧ a = 2#32 ∧ b = 6#32)
    (fun _ ⟨_, _, ⟨⟩⟩ m ⟨hme, ha, hb⟩ => by
      subst m ha hb; m6_to_group
      refine wp_join_group (ts := [i32, i32])
        (fun (a, b, ()) m => m = nvFidXor4Mem0 ∧ a = 0#32 ∧ b = 6#32)
        (fun _ ⟨_, _, ⟨⟩⟩ m ⟨hme, ha, hb⟩ => by
          subst m ha hb; m6_to_group
          refine wp_join_group (ts := [i32, i32])
            (fun (a, b, ()) m => m = nvFidXor4Mem0 ∧ a = 0#32 ∧ b = 2#32)
            (fun _ ⟨_, _, ⟨⟩⟩ m ⟨hme, ha, hb⟩ => by
              subst m ha hb; m6_steps
              rw [show (array (t := i32) nvFidXor4Cfg.pScratchBuf _) =
                  array (t := i32) nvFidXor4Cfg.pScratchBuf
                    [5#32, (1#32 <<< 28#32) ||| 3#32, 0#32, 2#32, 6#32] from
                congrArg _ (by decide)] at hm
              have hm' := unfocus_full_scratch_buf hm
              rw [sep_emp] at hm'
              exact ⟨rfl, rfl,
                nvFidMkState4_lengths 0#64 0#64 0#64 0 (List.replicate 8 0#8)
                  (List.replicate 4 0#32) (List.replicate 8 0#32) (List.replicate 4 0#32)
                  (List.replicate 8 0#32) (List.replicate 8 0#32)
                  [5#32, (1#32 <<< 28#32) ||| 3#32, 0#32, 2#32, 6#32]
                  (Nat.zero_le _) rfl rfl rfl rfl rfl rfl rfl,
                nvFidMk4_witness_empty, nvFidF0_unsat, hm'⟩)
            (fun _ hJ3 => by
              m6_split_fast
              · m6_steps; exact hJ3 (0#32, 2#32, ()) nvFidXor4Mem0 ⟨rfl, rfl, rfl⟩
              · exfalso; revert hc; dsimp only; decide))
        (fun _ hJ2 => by
          m6_split_fast
          · m6_steps; exact hJ2 (0#32, 6#32, ()) nvFidXor4Mem0 ⟨rfl, rfl, rfl⟩
          · exfalso; revert hc; decide))
    (fun _ hJ1 => by
      m6_split_fast
      · m6_steps; exact hJ1 (2#32, 6#32, ()) nvFidXor4Mem0 ⟨rfl, rfl, rfl⟩
      · exfalso; revert hc; decide)

/-! ## 3. `full_cong_and_match` Concrete Wide-33 (`> 31`) UNSAT NV (`GAP-CONG-01`) -/

def nvFidCfg34 : FullCfg :=
  { hdr := 0x10000#64, avail := 7188, mv := 34, max_vars := 34, bva_cap := 0, nc := 1
    arena_cap := 0, wcap := 0, delayed_cap := 0, red_cap := 0, extend_cap := 0, scratch_cap := 35
    hbva := rfl, hmv := by decide, hmaxv := by decide, hnc := by decide, harena := by decide
    hwcap := by decide, hdel := by decide, hred := by decide, hext := by decide, hscr := by decide
    havail_fit := by decide, hsize := by decide }

def nvFid34Tmp : List (BitVec 32) :=
  (List.range 33).map (fun j => BitVec.ofNat 32 (2 + 2 * j)) ++ [0#32]

def nvFid34Repr0 : List (BitVec 32) :=
  (List.range 68).map (fun l => BitVec.ofNat 32 l)

def nvFid34Scr0 : List (BitVec 32) :=
  [0#32, 33#32] ++ (List.range 33).map (fun j => BitVec.ofNat 32 (2 + 2 * j))

private theorem nvFid34Tmp_len : nvFid34Tmp.length = 34 := by simp [nvFid34Tmp]
private theorem nvFid34Repr0_len : nvFid34Repr0.length = 68 := by simp [nvFid34Repr0]
private theorem nvFid34Scr0_len : nvFid34Scr0.length = 35 := by simp [nvFid34Scr0]

def nvFid34MkState (tmp repr scr : List (BitVec 32)) : FullState :=
  { core :=
      { d_cur := 0#64, d_val := 0#64, cur_vars := 34, unassigned := 0#64
        arena_len := 0, wlen := 0, wusable := 0#64, arena_garbage := 0#64
        first_reducible := 0#64, num_irred := 0#64, num_redundant := 0#64, num_binary := 0#64
        unflushed := 0#64, probing := 0#64, trail_end := 0, propagated := 0
        cur_level := 0, fuel := 0#64, confl_ref := 0#64, confl_type := 0#64
        confl_lit0 := 0#64, confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0
        min_clr_len := 0, min_clr_full := 0#64, oom := 0#64, dense_mode := 0#64
        inconsistent := 0#64, vals := List.replicate 68 0#8, lit_mark := List.replicate 68 0#8
        mrk := List.replicate 34 0#8, flags := List.replicate 34 0#32
        lvl := List.replicate 34 0#32, rsns := List.replicate 34 0xFFFFFFFF#32
        trl := List.replicate 34 0#32, trail_pos := List.replicate 34 0#32
        tmp := tmp, min_clr := List.replicate 34 0#32, frame_trail := List.replicate 35 0#32
        frame_dec := List.replicate 35 0#32, wvec := List.replicate 136 0#32, repr := repr
        min_stk := List.replicate 70 0#32, arena := [], wstk := [] }
    scratch :=
      { heap_len := 0, scinc := 0#64, rel_period := 0#64, rel_limit := 0#64, rel_wait := 0#64
        rel_u := 0#64, rel_v := 0#64, rel_trigger := 0#64, conflicts := 0#64
        learned_lits := 0#64, min_removed := 0#64, delayed_len := 0, stable := 0#64
        switched := 0#64, mode_count := 0#64, mode_confl_lim := 0#64, mode_tick_lim := 0#64
        mode_saved_ticks := 0#64, search_ticks := 0#64, q_first := 0#64, q_last := 0#64
        q_search_idx := 0#64, q_search_stamp := 0#64, q_cur_stamp := 0#64
        target_assigned := 0#64, best_assigned := 0#64, rephase_limit := 0#64
        rephased := 0#64, reduce_limit := 0#64, reductions := 0#64, tier1 := 2#64
        tier2 := 6#64, restarts := 0#64, restart_limit := 0#64, ema_fast_biased := 0#64
        ema_fast_exp := 0#64, ema_slow_biased := 0#64, ema_slow_exp := 0#64, extend_len := 0
        rng_state := 0#64, chrono_levels := 0#64, otfs_cnt := 0#64, eager_sub_cnt := 0#64
        probe_limit := 0#64, probings := 0#64, elim_limit := 0#64, eliminations := 0#64
        elim_bound := 0#64, iterating := 0#64, hbr_cnt := 0#64, trans_cnt := 0#64
        viv_cnt := 0#64, subst_cnt := 0#64, cong_cnt := 0#64, sweep_cnt := 0#64
        bve_cnt := 0#64, bce_cnt := 0#64, bva_cnt := 0#64, walk_cnt_stat := 0#64
        fwd_sub_cnt := 0#64, fwd_str_cnt := 0#64, ant_sz := 0#64, res_sz := 0#64
        walk_vals := List.replicate 68 0#8, phases := List.replicate 34 0#8
        phases_target := List.replicate 34 0#8, phases_best := List.replicate 34 0#8
        walk_best := List.replicate 34 0#8, heap := List.replicate 34 0#32
        pos := List.replicate 34 0#32, shrink_stk := List.replicate 34 0#32
        q_prev := List.replicate 34 0#32, q_next := List.replicate 34 0#32
        q_stamp := List.replicate 34 0#32, wsort := List.replicate 68 0#32
        work_stk1 := List.replicate 68 0#32, work_stk2 := List.replicate 68 0#32
        tarjan_mark := List.replicate 68 0#32, tarjan_reach := List.replicate 68 0#32
        score := List.replicate 34 0#64, sim_sig := List.replicate 34 0#64
        glue_used := List.replicate 64 0#32, last_learned := List.replicate 16 0xFFFFFFFF#32
        delayed := [], red_refs := [], extend_stk := [], scratch_buf := scr } }

def nvFid34St0 : FullState := nvFid34MkState nvFid34Tmp nvFid34Repr0 nvFid34Scr0

theorem nvFid34_lengths (tmp repr scr : List (BitVec 32))
    (ht : tmp.length = 34) (hr : repr.length = 68) (hs : scr.length = 35) :
    (nvFid34MkState tmp repr scr).LengthsOk nvFidCfg34 := by
  dsimp only [nvFid34MkState, nvFidCfg34]
  refine ⟨⟨by rw [List.length_replicate]; rfl, by rw [List.length_replicate]; rfl,
    by rw [List.length_replicate], by rw [List.length_replicate], by rw [List.length_replicate],
    by rw [List.length_replicate], by rw [List.length_replicate], by rw [List.length_replicate], ht,
    by rw [List.length_replicate], by rw [List.length_replicate], by rw [List.length_replicate],
    by rw [List.length_replicate]; rfl, hr,
    by unfold FullCfg.minDepth fullMinDepthOf; rw [List.length_replicate]; rfl, rfl, rfl,
    Nat.le_refl _, Nat.le_refl _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _⟩,
   ⟨by rw [List.length_replicate]; rfl, by rw [List.length_replicate],
    by rw [List.length_replicate], by rw [List.length_replicate], by rw [List.length_replicate],
    by rw [List.length_replicate], by rw [List.length_replicate], by rw [List.length_replicate],
    by rw [List.length_replicate], by rw [List.length_replicate], by rw [List.length_replicate],
    by rw [List.length_replicate]; rfl, by rw [List.length_replicate]; rfl,
    by rw [List.length_replicate]; rfl, by rw [List.length_replicate]; rfl,
    by rw [List.length_replicate]; rfl, by rw [List.length_replicate],
    by rw [List.length_replicate], by rw [List.length_replicate],
    by rw [List.length_replicate], rfl, rfl, rfl, hs⟩⟩

private def nvFid34BlkHdr (s : FullState) : List UInt8 :=
  let c := nvFidCfg34
  bytes64 [BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc, s.core.d_cur, s.core.d_val] ++
    bytes64 (Full.hdrTailWords c s)

private def nvFid34BlkBytes (k : FullCoreState) (sc : FullScratch) : List UInt8 :=
  (bytesOf (t := i8) k.vals ++ List.replicate 4 0) ++
  (bytesOf (t := i8) sc.walk_vals ++ List.replicate 4 0) ++
  (bytesOf (t := i8) k.lit_mark ++ List.replicate 4 0) ++
  (bytesOf (t := i8) k.mrk ++ List.replicate 6 0) ++
  (bytesOf (t := i8) sc.phases ++ List.replicate 6 0) ++
  (bytesOf (t := i8) sc.phases_target ++ List.replicate 6 0) ++
  (bytesOf (t := i8) sc.phases_best ++ List.replicate 6 0) ++
  (bytesOf (t := i8) sc.walk_best ++ List.replicate 6 0)

private def nvFid34BlkU32A (k : FullCoreState) : List UInt8 :=
  (bytesOf (t := i32) k.flags ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.lvl ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.rsns ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.trl ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.trail_pos ++ List.replicate 8 0)

private def nvFid34BlkU32B (k : FullCoreState) (sc : FullScratch) : List UInt8 :=
  (bytesOf (t := i32) k.tmp ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.heap ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.pos ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.min_clr ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.shrink_stk ++ List.replicate 8 0)

private def nvFid34BlkU32C (k : FullCoreState) (sc : FullScratch) : List UInt8 :=
  (bytesOf (t := i32) sc.q_prev ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.q_next ++ List.replicate 8 0) ++
  (bytesOf (t := i32) sc.q_stamp ++ List.replicate 8 0) ++
  (bytesOf (t := i32) k.frame_trail ++ List.replicate 4 0) ++
  (bytesOf (t := i32) k.frame_dec ++ List.replicate 4 0)

private def nvFid34BlkWvec (k : FullCoreState) (sc : FullScratch) : List UInt8 :=
  bytesOf (t := i32) k.wvec ++ bytesOf (t := i32) k.repr ++
  bytesOf (t := i32) sc.wsort ++ bytesOf (t := i32) sc.work_stk1 ++
  bytesOf (t := i32) sc.work_stk2 ++ bytesOf (t := i32) sc.tarjan_mark ++
  bytesOf (t := i32) sc.tarjan_reach ++ bytes64 sc.score ++ bytes64 sc.sim_sig

private def nvFid34BlkTail (k : FullCoreState) (sc : FullScratch) : List UInt8 :=
  bytesOf (t := i32) k.min_stk ++ bytesOf (t := i32) sc.glue_used ++
  bytesOf (t := i32) sc.last_learned ++ bytesOf (t := i32) k.arena ++
  bytesOf (t := i32) k.wstk ++ bytesOf (t := i32) sc.delayed ++
  bytesOf (t := i32) sc.red_refs ++ bytesOf (t := i32) sc.extend_stk ++
  bytesOf (t := i32) sc.scratch_buf ++ List.replicate 0 0

def nvFid34Mem0 : Mem 64 :=
  let s := nvFid34St0
  (nvFid34BlkHdr s ++ nvFid34BlkBytes s.core s.scratch ++ nvFid34BlkU32A s.core ++
    nvFid34BlkU32B s.core s.scratch ++ nvFid34BlkU32C s.core s.scratch ++
    nvFid34BlkWvec s.core s.scratch ++ nvFid34BlkTail s.core s.scratch).At nvFidCfg34.hdr

private theorem nvFid34Mem0_ok : (FullMem nvFidCfg34 nvFid34St0 ⋆ emp) nvFid34Mem0 := by
  rw [sep_emp]
  let c := nvFidCfg34; let s := nvFid34St0
  have hm34 : c.max_vars = 34 := rfl
  have hv4 : valsBytes c.max_vars - 2 * c.max_vars = 4 := by decide
  have h2m : 2 * c.max_vars = 68 := by decide
  have hm6 : markBytes c.max_vars - c.max_vars = 6 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * c.max_vars = 8 := by decide
  have h4m : 4 * c.max_vars = 136 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 4 := by decide
  have h4p : 4 * (c.max_vars + 1) = 140 := by decide
  have hvb : valsBytes c.max_vars = 72 := by decide
  have hmkb : markBytes c.max_vars = 40 := by decide
  have hu32b : u32FullBytes c.max_vars = 144 := by decide
  have hmd : c.minDepth = 35 := by decide
  have harc : c.arena_cap = 0 := rfl
  have hwc : c.wcap = 0 := rfl
  have hdc : c.delayed_cap = 0 := rfl
  have hrc : c.red_cap = 0 := rfl
  have hec : c.extend_cap = 0 := rfl
  have hsl : c.slack = 0 := by decide
  have hHdr : (nvFid34BlkHdr s).length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        array64 (c.hdr + 32) (Full.hdrTailWords c s)) ((nvFid34BlkHdr s).At c.hdr) :=
    nv_join_pair
      ⟨rfl, dimacsState_bytes c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val⟩
      (nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide))
      rfl (by rw [bytes64_length]; simp only [List.length_cons, List.length_nil]; decide)
  have hBytes : (nvFid34BlkBytes s.core s.scratch).length = 416 ∧
      ((array (t := i8) c.pVals s.core.vals ⋆ array (t := i8) c.pLitMark s.core.lit_mark ⋆
          array (t := i8) c.pMark s.core.mrk) ⋆
        FullScrByteArrs c s.scratch ⋆ c.padBytes)
        ((nvFid34BlkBytes s.core s.scratch).At c.pVals) := by
    have h1 := nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 68 4
      (by change 1 * (List.replicate 68 (0#8 : BitVec 8)).length = 68
          rw [List.length_replicate]) (by decide)
    have h2 := nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 68 4
      (by change 1 * (List.replicate 68 (0#8 : BitVec 8)).length = 68
          rw [List.length_replicate]) (by decide)
    have h3 := nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 68 4
      (by change 1 * (List.replicate 68 (0#8 : BitVec 8)).length = 68
          rw [List.length_replicate]) (by decide)
    have h4 := nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 34 6
      (by change 1 * (List.replicate 34 (0#8 : BitVec 8)).length = 34
          rw [List.length_replicate]) (by decide)
    have h5 := nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 34 6
      (by change 1 * (List.replicate 34 (0#8 : BitVec 8)).length = 34
          rw [List.length_replicate]) (by decide)
    have h6 := nv_arr_pad_p (t := i8) (a := c.pPhasesTarget) (xs := s.scratch.phases_target) 34 6
      (by change 1 * (List.replicate 34 (0#8 : BitVec 8)).length = 34
          rw [List.length_replicate]) (by decide)
    have h7 := nv_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best) 34 6
      (by change 1 * (List.replicate 34 (0#8 : BitVec 8)).length = 34
          rw [List.length_replicate]) (by decide)
    have h8 := nv_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best) 34 6
      (by change 1 * (List.replicate 34 (0#8 : BitVec 8)).length = 34
          rw [List.length_replicate]) (by decide)
    have j12 := nv_join_pair h1 h2 (by rw [FullCfg.pWalkVals, hvb]) (by decide)
    have j123 := nv_join_pair j12 h3 (by rw [FullCfg.pLitMark, FullCfg.pWalkVals, hvb, nv_ptr2])
      (by decide)
    have j1234 := nv_join_pair j123 h4
      (by rw [FullCfg.pMark, FullCfg.pLitMark, FullCfg.pWalkVals, hvb, nv_ptr2, nv_ptr2])
      (by decide)
    have j12345 := nv_join_pair j1234 h5
      (by rw [FullCfg.pPhases, FullCfg.pMark, FullCfg.pLitMark, FullCfg.pWalkVals, hvb, hmkb,
        nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    have j123456 := nv_join_pair j12345 h6
      (by rw [FullCfg.pPhasesTarget, FullCfg.pPhases, FullCfg.pMark, FullCfg.pLitMark,
        FullCfg.pWalkVals, hvb, hmkb, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    have j1234567 := nv_join_pair j123456 h7
      (by rw [FullCfg.pPhasesBest, FullCfg.pPhasesTarget, FullCfg.pPhases, FullCfg.pMark,
        FullCfg.pLitMark, FullCfg.pWalkVals, hvb, hmkb, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2,
        nv_ptr2]) (by decide)
    exact nv_sep_reorg (nv_join_pair j1234567 h8
      (by rw [FullCfg.pWalkBest, FullCfg.pPhasesBest, FullCfg.pPhasesTarget, FullCfg.pPhases,
        FullCfg.pMark, FullCfg.pLitMark, FullCfg.pWalkVals, hvb, hmkb, nv_ptr2, nv_ptr2, nv_ptr2,
        nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)) fun _ hm => by
      have pB : ∀ {A1 A2 A3 A4 A5 A6 A7 A8 P1 P2 P3 P4 P5 P6 P7 P8 : Mem 64 → Prop} {k},
          ((((((((A1 ⋆ P1) ⋆ (A2 ⋆ P2)) ⋆ (A3 ⋆ P3)) ⋆ (A4 ⋆ P4)) ⋆
            (A5 ⋆ P5)) ⋆ (A6 ⋆ P6)) ⋆ (A7 ⋆ P7)) ⋆ (A8 ⋆ P8)) k →
          ((A1 ⋆ A3 ⋆ A4) ⋆ (A2 ⋆ A5 ⋆ A6 ⋆ A7 ⋆ A8) ⋆
            (P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6 ⋆ P7 ⋆ P8)) k := fun x => sep_ac x
      unfold FullScrByteArrs FullCfg.padBytes; rw [hv4, h2m, hm6, hm34]; exact pB hm
  have hU32A : (nvFid34BlkU32A s.core).length = 720 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        ((nvFid34BlkU32A s.core).At c.pFlags) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 136 8
      (by change 4 * (List.replicate 34 (0#32 : BitVec 32)).length = 136
          rw [List.length_replicate]) (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 136 8
      (by change 4 * (List.replicate 34 (0#32 : BitVec 32)).length = 136
          rw [List.length_replicate]) (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 136 8
      (by change 4 * (List.replicate 34 (0xFFFFFFFF#32 : BitVec 32)).length = 136
          rw [List.length_replicate]) (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 136 8
      (by change 4 * (List.replicate 34 (0#32 : BitVec 32)).length = 136
          rw [List.length_replicate]) (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 136 8
      (by change 4 * (List.replicate 34 (0#32 : BitVec 32)).length = 136
          rw [List.length_replicate]) (by decide)
    have j12 := nv_join_pair h1 h2 (by rw [FullCfg.pLevel, hu32b]) (by decide)
    have j123 := nv_join_pair j12 h3 (by rw [FullCfg.pReason, FullCfg.pLevel, hu32b, nv_ptr2])
      (by decide)
    have j1234 := nv_join_pair j123 h4
      (by rw [FullCfg.pTrail, FullCfg.pReason, FullCfg.pLevel, hu32b, nv_ptr2, nv_ptr2]) (by decide)
    exact nv_sep_reorg (nv_join_pair j1234 h5
      (by rw [FullCfg.pTrailPos, FullCfg.pTrail, FullCfg.pReason, FullCfg.pLevel, hu32b,
        nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu8, h4m]; exact sep_ac hm
  have hU32B : (nvFid34BlkU32B s.core s.scratch).length = 720 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pHeap s.scratch.heap ⋆
        array (t := i32) c.pPos s.scratch.pos ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
        array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        ((nvFid34BlkU32B s.core s.scratch).At c.pTmp) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 136 8
      (by have ht := nvFid34Tmp_len; change 4 * nvFid34Tmp.length = 136; omega) (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 136 8
      (by change 4 * (List.replicate 34 (0#32 : BitVec 32)).length = 136
          rw [List.length_replicate]) (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 136 8
      (by change 4 * (List.replicate 34 (0#32 : BitVec 32)).length = 136
          rw [List.length_replicate]) (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 136 8
      (by change 4 * (List.replicate 34 (0#32 : BitVec 32)).length = 136
          rw [List.length_replicate]) (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk) 136 8
      (by change 4 * (List.replicate 34 (0#32 : BitVec 32)).length = 136
          rw [List.length_replicate]) (by decide)
    have j12 := nv_join_pair h1 h2 (by rw [FullCfg.pHeap, hu32b]) (by decide)
    have j123 := nv_join_pair j12 h3 (by rw [FullCfg.pPos, FullCfg.pHeap, hu32b, nv_ptr2])
      (by decide)
    have j1234 := nv_join_pair j123 h4
      (by rw [FullCfg.pMinClr, FullCfg.pPos, FullCfg.pHeap, hu32b, nv_ptr2, nv_ptr2]) (by decide)
    exact nv_sep_reorg (nv_join_pair j1234 h5
      (by rw [FullCfg.pShrinkStk, FullCfg.pMinClr, FullCfg.pPos, FullCfg.pHeap, hu32b,
        nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu8, h4m]; exact sep_ac hm
  have hU32C : (nvFid34BlkU32C s.core s.scratch).length = 720 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        ((nvFid34BlkU32C s.core s.scratch).At c.pQPrev) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 136 8
      (by change 4 * (List.replicate 34 (0#32 : BitVec 32)).length = 136
          rw [List.length_replicate]) (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 136 8
      (by change 4 * (List.replicate 34 (0#32 : BitVec 32)).length = 136
          rw [List.length_replicate]) (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 136 8
      (by change 4 * (List.replicate 34 (0#32 : BitVec 32)).length = 136
          rw [List.length_replicate]) (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 140 4
      (by change 4 * (List.replicate 35 (0#32 : BitVec 32)).length = 140
          rw [List.length_replicate]) (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 140 4
      (by change 4 * (List.replicate 35 (0#32 : BitVec 32)).length = 140
          rw [List.length_replicate]) (by decide)
    have j12 := nv_join_pair h1 h2 (by rw [FullCfg.pQNext, hu32b]) (by decide)
    have j123 := nv_join_pair j12 h3 (by rw [FullCfg.pQStamp, FullCfg.pQNext, hu32b, nv_ptr2])
      (by decide)
    have j1234 := nv_join_pair j123 h4
      (by rw [FullCfg.pFrameTrail, FullCfg.pQStamp, FullCfg.pQNext, hu32b, nv_ptr2, nv_ptr2])
      (by decide)
    exact nv_sep_reorg (nv_join_pair j1234 h5
      (by rw [FullCfg.pFrameDec, FullCfg.pFrameTrail, FullCfg.pQStamp, FullCfg.pQNext, hu32b,
        nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu8, hu4, h4m, h4p]; exact sep_ac hm
  have hWvec : (nvFid34BlkWvec s.core s.scratch).length = 2720 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        ((nvFid34BlkWvec s.core s.scratch).At c.pWvec) := by
    have h1 := nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 544
      (by change 4 * (List.replicate 136 (0#32 : BitVec 32)).length = 544
          rw [List.length_replicate]) (by decide)
    have h2 := nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 272
      (by have hr := nvFid34Repr0_len; change 4 * nvFid34Repr0.length = 272; omega) (by decide)
    have h3 := nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 272
      (by change 4 * (List.replicate 68 (0#32 : BitVec 32)).length = 272
          rw [List.length_replicate]) (by decide)
    have h4 := nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 272
      (by change 4 * (List.replicate 68 (0#32 : BitVec 32)).length = 272
          rw [List.length_replicate]) (by decide)
    have h5 := nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 272
      (by change 4 * (List.replicate 68 (0#32 : BitVec 32)).length = 272
          rw [List.length_replicate]) (by decide)
    have h6 := nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 272
      (by change 4 * (List.replicate 68 (0#32 : BitVec 32)).length = 272
          rw [List.length_replicate]) (by decide)
    have h7 := nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 272
      (by change 4 * (List.replicate 68 (0#32 : BitVec 32)).length = 272
          rw [List.length_replicate]) (by decide)
    have h8 := nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 272
      (by change 8 * (List.replicate 34 (0#64 : BitVec 64)).length = 272
          rw [List.length_replicate]) (by decide)
    have h9 := nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 272
      (by change 8 * (List.replicate 34 (0#64 : BitVec 64)).length = 272
          rw [List.length_replicate]) (by decide)
    have j12 := nv_join_pair h1 h2 (by rw [FullCfg.pRepr, hm34]) (by decide)
    have j123 := nv_join_pair j12 h3 (by rw [FullCfg.pWsort, FullCfg.pRepr, hm34, nv_ptr2])
      (by decide)
    have j1234 := nv_join_pair j123 h4
      (by rw [FullCfg.pWorkStk1, FullCfg.pWsort, FullCfg.pRepr, hm34, nv_ptr2, nv_ptr2]) (by decide)
    have j12345 := nv_join_pair j1234 h5
      (by rw [FullCfg.pWorkStk2, FullCfg.pWorkStk1, FullCfg.pWsort, FullCfg.pRepr, hm34,
        nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    have j123456 := nv_join_pair j12345 h6
      (by rw [FullCfg.pTarjanMark, FullCfg.pWorkStk2, FullCfg.pWorkStk1, FullCfg.pWsort,
        FullCfg.pRepr, hm34, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    have j1234567 := nv_join_pair j123456 h7
      (by rw [FullCfg.pTarjanReach, FullCfg.pTarjanMark, FullCfg.pWorkStk2, FullCfg.pWorkStk1,
        FullCfg.pWsort, FullCfg.pRepr, hm34, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2])
      (by decide)
    have j12345678 := nv_join_pair j1234567 h8
      (by rw [FullCfg.pScore, FullCfg.pTarjanReach, FullCfg.pTarjanMark, FullCfg.pWorkStk2,
        FullCfg.pWorkStk1, FullCfg.pWsort, FullCfg.pRepr, hm34, nv_ptr2, nv_ptr2, nv_ptr2,
        nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    exact nv_sep_reorg (nv_join_pair j12345678 h9
      (by rw [FullCfg.pSimSig, FullCfg.pScore, FullCfg.pTarjanReach, FullCfg.pTarjanMark,
        FullCfg.pWorkStk2, FullCfg.pWorkStk1, FullCfg.pWsort, FullCfg.pRepr, hm34, nv_ptr2,
        nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail : (nvFid34BlkTail s.core s.scratch).length = 740 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        ((nvFid34BlkTail s.core s.scratch).At c.pMinStk) := by
    have h1 := nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 280
      (by change 4 * (List.replicate 70 (0#32 : BitVec 32)).length = 280
          rw [List.length_replicate]) (by decide)
    have h2 := nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256
      (by change 4 * (List.replicate 64 (0#32 : BitVec 32)).length = 256
          rw [List.length_replicate]) (by decide)
    have h3 := nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned) 64
      (by change 4 * (List.replicate 16 (0xFFFFFFFF#32 : BitVec 32)).length = 64
          rw [List.length_replicate]) (by decide)
    have h4 := nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 0 rfl (by decide)
    have h5 := nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 0 rfl (by decide)
    have h6 := nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl (by decide)
    have h7 := nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl (by decide)
    have h8 := nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl
      (by decide)
    have h9 := nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 140
      (by have hs := nvFid34Scr0_len; change 4 * nvFid34Scr0.length = 140; omega) (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 (0 : UInt8)).At c.pSlack) := by
      rw [hsl]; exact nv_pad_p c.pSlack 0
    have j12 := nv_join_pair h1 h2 (by rw [FullCfg.pGlueUsed, hmd]) (by decide)
    have j123 := nv_join_pair j12 h3 (by rw [FullCfg.pLastLearned, FullCfg.pGlueUsed, hmd, nv_ptr2])
      (by decide)
    have j1234 := nv_join_pair j123 h4
      (by rw [FullCfg.pArena, FullCfg.pLastLearned, FullCfg.pGlueUsed, hmd, nv_ptr2, nv_ptr2])
      (by decide)
    have j12345 := nv_join_pair j1234 h5
      (by rw [FullCfg.pWstk, FullCfg.pArena, FullCfg.pLastLearned, FullCfg.pGlueUsed, hmd, harc,
        nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    have j123456 := nv_join_pair j12345 h6
      (by rw [FullCfg.pDelayed, FullCfg.pWstk, FullCfg.pArena, FullCfg.pLastLearned,
        FullCfg.pGlueUsed, hmd, harc, hwc, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    have j1234567 := nv_join_pair j123456 h7
      (by rw [FullCfg.pRedRefs, FullCfg.pDelayed, FullCfg.pWstk, FullCfg.pArena,
        FullCfg.pLastLearned, FullCfg.pGlueUsed, hmd, harc, hwc, hdc, nv_ptr2, nv_ptr2, nv_ptr2,
        nv_ptr2, nv_ptr2]) (by decide)
    have j12345678 := nv_join_pair j1234567 h8
      (by rw [FullCfg.pExtendStk, FullCfg.pRedRefs, FullCfg.pDelayed, FullCfg.pWstk, FullCfg.pArena,
        FullCfg.pLastLearned, FullCfg.pGlueUsed, hmd, harc, hwc, hdc, hrc, nv_ptr2, nv_ptr2,
        nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    have j123456789 := nv_join_pair j12345678 h9
      (by rw [FullCfg.pScratchBuf, FullCfg.pExtendStk, FullCfg.pRedRefs, FullCfg.pDelayed,
        FullCfg.pWstk, FullCfg.pArena, FullCfg.pLastLearned, FullCfg.pGlueUsed, hmd, harc, hwc,
        hdc, hrc, hec, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2]) (by decide)
    exact nv_sep_reorg (nv_join_pair j123456789 h10
      (by rw [FullCfg.pSlack, FullCfg.pScratchBuf, FullCfg.pExtendStk, FullCfg.pRedRefs,
        FullCfg.pDelayed, FullCfg.pWstk, FullCfg.pArena, FullCfg.pLastLearned, FullCfg.pGlueUsed,
        hmd, harc, hwc, hdc, hrc, hec, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2, nv_ptr2,
        nv_ptr2, nv_ptr2]; rfl) (by decide)) fun _ hm => by
      unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := nv_join_pair hHdr hBytes rfl (by decide)
  have h02 := nv_join_pair h01 hU32A
    (by rw [FullCfg.pFlags, FullCfg.pWalkBest, FullCfg.pPhasesBest, FullCfg.pPhasesTarget,
      FullCfg.pPhases, FullCfg.pMark, FullCfg.pLitMark, FullCfg.pWalkVals, FullCfg.pVals,
      hvb, hmkb]; repeat rw [nv_ptr2]) (by decide)
  have h03 := nv_sep_reorg (nv_join_pair h02 hU32B
    (by rw [FullCfg.pTmp, FullCfg.pTrailPos, FullCfg.pTrail, FullCfg.pReason, FullCfg.pLevel,
      FullCfg.pFlags, FullCfg.pWalkBest, FullCfg.pPhasesBest, FullCfg.pPhasesTarget,
      FullCfg.pPhases, FullCfg.pMark, FullCfg.pLitMark, FullCfg.pWalkVals, FullCfg.pVals,
      hvb, hmkb, hu32b]; repeat rw [nv_ptr2]) (by decide)) fun _ hm => by
    have p1 : ∀ {D H CB SB PB UA PA T Hp Ps Mc Sh PB2 : Mem 64 → Prop} {k},
        (((D ⋆ H) ⋆ (CB ⋆ SB ⋆ PB)) ⋆ (UA ⋆ PA) ⋆ ((T ⋆ Hp ⋆ Ps ⋆ Mc ⋆ Sh) ⋆ PB2)) k →
        ((D ⋆ H) ⋆ ((CB ⋆ (UA ⋆ T ⋆ Mc)) ⋆ (SB ⋆ (Hp ⋆ Ps ⋆ Sh)) ⋆ (PB ⋆ PA ⋆ PB2))) k :=
      fun x => sep_ac x
    exact p1 hm
  have h04 := nv_sep_reorg (nv_join_pair h03 hU32C
    (by rw [FullCfg.pQPrev, FullCfg.pShrinkStk, FullCfg.pMinClr, FullCfg.pPos, FullCfg.pHeap,
      FullCfg.pTmp, FullCfg.pTrailPos, FullCfg.pTrail, FullCfg.pReason, FullCfg.pLevel,
      FullCfg.pFlags, FullCfg.pWalkBest, FullCfg.pPhasesBest, FullCfg.pPhasesTarget,
      FullCfg.pPhases, FullCfg.pMark, FullCfg.pLitMark, FullCfg.pWalkVals, FullCfg.pVals,
      hvb, hmkb, hu32b]; repeat rw [nv_ptr2]) (by decide)) fun _ hm => by
    have p2 : ∀ {DH C1 S1 P1 Qp Qn Qs FTr FDec PC : Mem 64 → Prop} {k},
        ((DH ⋆ (C1 ⋆ S1 ⋆ P1)) ⋆ ((Qp ⋆ Qn ⋆ Qs) ⋆ (FTr ⋆ FDec) ⋆ PC)) k →
        (DH ⋆ ((C1 ⋆ FTr ⋆ FDec) ⋆ (S1 ⋆ (Qp ⋆ Qn ⋆ Qs)) ⋆ (P1 ⋆ PC))) k := fun x => sep_ac x
    exact p2 hm
  have h05 := nv_join_pair h04 hWvec
    (by rw [FullCfg.pWvec, FullCfg.pFrameDec, FullCfg.pFrameTrail, FullCfg.pQStamp, FullCfg.pQNext,
      FullCfg.pQPrev, FullCfg.pShrinkStk, FullCfg.pMinClr, FullCfg.pPos, FullCfg.pHeap,
      FullCfg.pTmp, FullCfg.pTrailPos, FullCfg.pTrail, FullCfg.pReason, FullCfg.pLevel,
      FullCfg.pFlags, FullCfg.pWalkBest, FullCfg.pPhasesBest, FullCfg.pPhasesTarget,
      FullCfg.pPhases, FullCfg.pMark, FullCfg.pLitMark, FullCfg.pWalkVals, FullCfg.pVals,
      hvb, hmkb, hu32b]; repeat rw [nv_ptr2]) (by decide)
  exact (nv_sep_reorg (nv_join_pair h05 hTail
    (by rw [FullCfg.pMinStk, FullCfg.pSimSig, FullCfg.pScore, FullCfg.pTarjanReach,
      FullCfg.pTarjanMark, FullCfg.pWorkStk2, FullCfg.pWorkStk1, FullCfg.pWsort, FullCfg.pRepr,
      FullCfg.pWvec, FullCfg.pFrameDec, FullCfg.pFrameTrail, FullCfg.pQStamp, FullCfg.pQNext,
      FullCfg.pQPrev, FullCfg.pShrinkStk, FullCfg.pMinClr, FullCfg.pPos, FullCfg.pHeap,
      FullCfg.pTmp, FullCfg.pTrailPos, FullCfg.pTrail, FullCfg.pReason, FullCfg.pLevel,
      FullCfg.pFlags, FullCfg.pWalkBest, FullCfg.pPhasesBest, FullCfg.pPhasesTarget,
      FullCfg.pPhases, FullCfg.pMark, FullCfg.pLitMark, FullCfg.pWalkVals, FullCfg.pVals,
      hvb, hmkb, hu32b, hm34]; repeat rw [nv_ptr2]) (by decide)) fun _ hm => by
    have p3 : ∀ {D H CoreB ScrB P2 Wv Re SW Sc Ss MS Gu Ll CD SD SL : Mem 64 → Prop} {k},
        (((D ⋆ H ⋆ (CoreB ⋆ ScrB ⋆ P2)) ⋆ ((Wv ⋆ Re) ⋆ SW ⋆ (Sc ⋆ Ss))) ⋆
          (MS ⋆ (Gu ⋆ Ll) ⋆ CD ⋆ SD ⋆ SL)) k →
        (D ⋆ H ⋆ (CoreB ⋆ Wv ⋆ Re ⋆ MS ⋆ CD) ⋆
          (ScrB ⋆ SW ⋆ Sc ⋆ Ss ⋆ Gu ⋆ Ll ⋆ SD) ⋆ (P2 ⋆ SL)) k :=
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
    exact p7 (p6 (p5 (p4 (p3 hm))))).2

private theorem nvFid34_repr0_inv : FullCongReprInv [] 68 nvFid34Repr0 := by
  refine ⟨⟨nvFid34Repr0_len ▸ Nat.le_refl _, fun l hl => ?_⟩, fun l hl => ?_⟩
  · have hget : (nvFid34Repr0[l]?.getD 0#32).toNat = l := by
      simp [nvFid34Repr0, hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : l < 2 ^ 32)]
    omega
  · have hget : (nvFid34Repr0[l]?.getD 0#32).toNat = l := by
      simp [nvFid34Repr0, hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : l < 2 ^ 32)]
    rw [hget]; exact nv_litEquiv_refl _ _

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`): `full_cong_and_match` under `fidCongEnv` with
wide arity `ua = 33#32` (`> 31`) matches every literal cleanly and returns exact `r = true`. -/
theorem nv_fid_cong_and_match_wide33 :
    Func.wp fidCongEnv full_cong_and_match_body (nvFidCfg34.hdr, 0#32, 33#32, ()) nvFid34Mem0
      (fun (r, ()) m' => ∃ repr' : List (BitVec 32),
        r = true ∧ repr'.length = 68 ∧ FullCongReprInv [] 68 repr' ∧ nvFidF0.Unsat ∧
        FullMem nvFidCfg34 { nvFid34St0 with core := { nvFid34St0.core with repr := repr' } } m')
      (fun _ _ _ _ => False) := by
  have hm0 := nvFid34Mem0_ok
  have hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      fidCongEnv "full_cong_find" [i64, i32] [i32] a m Q X := fun _ _ _ _ => fidCongEnv_find
  unfold Func.wp full_cong_and_match_body
  m6_split_fast
  · exfalso; revert hc; decide
  · m6_split_fast
    · exfalso; revert hc; decide
    · m6_steps
      refine wp_loop_inv (ts := [i64, i32])
        (fun (mask, j, ()) mj => ∃ reprj : List (BitVec 32),
          reprj.length = 68 ∧ j.toNat ≤ 33 ∧ FullCongReprInv [] 68 reprj ∧
          (∀ b < 64, mask.toNat.testBit b = true ↔ b < j.toNat) ∧
          (FullMem nvFidCfg34
            { nvFid34St0 with core := { nvFid34St0.core with repr := reprj } } ⋆ emp) mj)
        (fun (_, j, ()) _ => 33 - j.toNat)
        (fun J hJ => by
          m6_let
          exact hJ (0#64, 0#32, ()) nvFid34Mem0 ⟨nvFid34Repr0, nvFid34Repr0_len, Nat.zero_le _,
            nvFid34_repr0_inv, fun b hb => by simp, hm0⟩)
        (fun J (mask, j, ()) mj ⟨reprj, hrlj, hj_le, hreprj, hmb, hmj⟩ ihj => ?_)
      let stj : FullState := { nvFid34St0 with core := { nvFid34St0.core with repr := reprj } }
      m6_split_fast
      · have hj_lt : j.toNat < 33 := by
          simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
        have hj1 : (j + 1#32).toNat = j.toNat + 1 := by
          rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        have hscr_j : ((BitVec.ofNat 64 0) + 2 + j.setWidth 64).toNat = 2 + j.toNat := by
          rw [BitVec.toNat_add, BitVec.toNat_add, bv_zext32_toNat,
            show (BitVec.ofNat 64 0).toNat = 0 from rfl, show (2 : BitVec 64).toNat = 2 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        have hscr_arr : ((BitVec.ofNat 64 0) + 2 + j.setWidth 64).toNat <
            stj.scratch.scratch_buf.length := by
          have hsl := nvFid34Scr0_len
          rw [hscr_j]; dsimp [stj, nvFid34St0, nvFid34MkState]; omega
        have hscr_val : stj.scratch.scratch_buf[((BitVec.ofNat 64 0) + 2 +
            j.setWidth 64).toNat]'hscr_arr = BitVec.ofNat 32 (2 + 2 * j.toNat) := by
          simp only [hscr_j, stj, nvFid34St0, nvFid34MkState, nvFid34Scr0]
          rw [List.getElem_append_right (by simp)]
          simp
        m6_steps; m6_call hFind
        refine ⟨[], 68, reprj, FullReprRest nvFidCfg34 stj ⋆ emp, hreprj,
          by simp only [stj] at hscr_val ⊢
             rw [hscr_val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega,
          focus_full_repr hmj,
          fun er repr_e me hrl_e hrepr_e _ _ her_eqv hme => ?_⟩
        have her_eq : er = BitVec.ofNat 32 (2 + 2 * j.toNat) := by
          simp only [stj] at hscr_val
          rw [hscr_val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at her_eqv
          have h32n : (BitVec.ofNat 32 (2 + 2 * j.toNat)).toNat = 2 + 2 * j.toNat := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          exact BitVec.eq_of_toNat_eq ((litEquiv_empty_eq her_eqv).symm.trans h32n.symm)
        let ste : FullState := { nvFid34St0 with core := { nvFid34St0.core with repr := repr_e } }
        have hme' : (FullMem nvFidCfg34 ste ⋆ emp) me := unfocus_full_repr hme
        have her_vals : (er.setWidth 64).toNat < ste.core.vals.length := by
          rw [bv_zext32_toNat, her_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          dsimp [ste, nvFid34St0, nvFid34MkState]; omega
        have hev_z : ste.core.vals[(er.setWidth 64).toNat]'her_vals = 0#8 := by
          simp only [ste, nvFid34St0, nvFid34MkState, List.getElem_replicate]
        m6_split_fast
        · exfalso; rw [hev_z] at hc; revert hc; decide
        · m6_split_fast
          · m6_to_group
            refine wp_loop_break_group (brkTs := [i64, .bool, i32]) (lpTs := [i32])
              (fun (mask_b, found, _, ()) mb => mb = me ∧ found = true ∧
                ∀ b < 64, mask_b.toNat.testBit b = true ↔ b < j.toNat + 1)
              (fun rem (k, ()) mk => mk = me ∧ k.toNat ≤ j.toNat ∧ rem = j.toNat - k.toNat)
              ?_ ?_ ?_
            · rintro _ ⟨mask_b, found, _, ⟨⟩⟩ mb ⟨hme_eq, rfl, hmb'⟩
              subst mb; m6_split_fast
              · m6_steps
                exact ihj (mask_b, j + 1#32, ()) me (by dsimp only; rw [hj1]; omega)
                  ⟨repr_e, hrl_e.trans hrlj, by rw [hj1]; exact hj_lt, hrepr_e,
                   by rw [hj1]; exact hmb', hme'⟩
              · exfalso; revert hc; dsimp only; decide
            · rintro Bk Lk rem ⟨k, ⟨⟩⟩ mk hBk hLk ⟨hmk_eq, hk_le, rfl⟩
              subst mk; m6_split_fast
              · have hk_lt : k.toNat < 33 := by omega
                have hkz : (k.setWidth 64).toNat = k.toNat := bv_zext32_toNat k
                have hk_tmp : (k.setWidth 64).toNat < ste.core.tmp.length := by
                  have htl := nvFid34Tmp_len
                  rw [hkz]; dsimp [ste, nvFid34St0, nvFid34MkState]; omega
                have htmp_val : ste.core.tmp[(k.setWidth 64).toNat]'hk_tmp =
                    BitVec.ofNat 32 (2 + 2 * k.toNat) := by
                  simp only [hkz, ste, nvFid34St0, nvFid34MkState, nvFid34Tmp]
                  rw [List.getElem_append_left (by simp; omega), List.getElem_map,
                    List.getElem_range]
                have hk1 : (k + 1#32).toNat = k.toNat + 1 := by
                  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                    Nat.mod_eq_of_lt (by omega)]
                m6_split_fast
                · have hkj : k.toNat = j.toNat := by
                    have heq := beq_iff_eq.mp hc
                    rw [htmp_val, her_eq] at heq
                    have hn := congrArg BitVec.toNat heq
                    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hn
                    omega
                  have hk_64 : k.toNat < 64 := by omega
                  m6_steps
                  have hkm : (1 : BitVec 64) <<< ((k.setWidth 64).toNat % 64) =
                      1#64 <<< BitVec.ofNat 64 j.toNat := by
                    rw [hkz, hkj, Nat.mod_eq_of_lt (by omega : j.toNat < 64)]
                    change (1#64 : BitVec 64) <<< j.toNat =
                      (1#64 : BitVec 64) <<< (BitVec.ofNat 64 j.toNat).toNat
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                  rw [hkm]
                  refine hBk (mask ||| (1#64 <<< BitVec.ofNat 64 j.toNat), true, k, ()) me
                    ⟨rfl, rfl, fun b hb => ?_⟩
                  rw [bv64_or_shl_testBit mask (by omega : j.toNat < 64) b]
                  simp [Bool.or_eq_true, hmb b hb]; omega
                · have hk_ne : k.toNat ≠ j.toNat := by
                    intro he
                    have hne := beq_eq_false_iff_ne.mp hc
                    exact hne (by rw [htmp_val, her_eq, he])
                  m6_steps
                  exact hLk (j.toNat - (k + 1#32).toNat) (k + 1#32, ()) me (by omega)
                    ⟨rfl, by omega, rfl⟩
              · exfalso; simp only [BitVec.ult, decide_eq_false_iff_not] at hc
                change ¬ k.toNat < 33 at hc; omega
            · intro _ Lk _ hLk; m6_let
              exact hLk j.toNat (0#32, ()) me ⟨rfl, Nat.zero_le _, rfl⟩
          · exfalso; rw [hev_z] at hc; revert hc; decide
      · have hj_eq : j.toNat = 33 := by
          simp only [BitVec.ult, decide_eq_false_iff_not] at hc
          change ¬ j.toNat < 33 at hc; omega
        rw [hj_eq] at hmb
        m6_to_group
        refine wp_join_group (ts := [i64]) (fun (fm, ()) mf => mf = mj ∧ fm = mask)
          (fun _ ⟨_, ⟨⟩⟩ mf ⟨hmf, hfm⟩ => by
            subst mf hfm; m6_steps
            rw [beq_self_eq_true]
            rw [sep_emp] at hmj
            exact ⟨reprj, rfl, hrlj, hreprj, nvFidF0_unsat, hmj⟩)
          ?_
        intro Jf hJf; m6_split_fast
        · exfalso; revert hc; decide
        · m6_let
          have hfm_eq : ((1#64 : BitVec 64) <<< (((33#32 : BitVec 32).setWidth 64).toNat % 64) -
              1#64) = mask := by
            apply BitVec.eq_of_toNat_eq; apply Nat.eq_of_testBit_eq; intro b
            have hpow33 : (((1#64 : BitVec 64) <<< (((33#32 : BitVec 32).setWidth 64).toNat % 64) -
                1#64) : BitVec 64).toNat = 2 ^ 33 - 1 := by decide
            rw [hpow33, Nat.testBit_two_pow_sub_one]
            by_cases hb64 : b < 64
            · exact Bool.eq_iff_iff.mpr (by simp [hmb b hb64])
            · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le mask.isLt
                (Nat.pow_le_pow_right (by decide) (by omega)))]
              simp; omega
          exact hJf (((1#64 : BitVec 64) <<< (((33#32 : BitVec 32).setWidth 64).toNat % 64) -
            1#64, ()) ) mj ⟨rfl, hfm_eq⟩

/-! ## 4. `full_cong_ht_grow_clear_m7` Concrete 256K (`> 131072`) UNSAT NV (`GAP-CONG-03`) -/

def nvFidHt256Cfg : FullCfg := nvFidMkCfg4 262152 (by decide)
def nvFidHt256Scr0 : List (BitVec 32) :=
  ((List.replicate 262152 0xFFFFFFFF#32).set 6 8#32).set 7 131072#32
def nvFidHt256St0 : FullState :=
  nvFidMkState4 0#64 0#64 17#64 0 (List.replicate 8 0#8) (List.replicate 4 0#32)
    (List.replicate 8 0#32) (List.replicate 4 0#32) (List.replicate 8 0#32) (List.replicate 8 0#32)
    nvFidHt256Scr0
private theorem nvFidHt256Scr0_len : nvFidHt256Scr0.length = 262152 := by
  simp only [nvFidHt256Scr0, List.length_set, List.length_replicate]
def nvFidHt256Mem0 : Mem 64 :=
  nvFidMkMem4 262152 (by decide) 0#64 0#64 17#64 0 (List.replicate 8 0#8) (List.replicate 4 0#32)
    (List.replicate 8 0#32) (List.replicate 4 0#32) (List.replicate 8 0#32) (List.replicate 8 0#32)
    nvFidHt256Scr0

private theorem nvFidHt256CtrlOk0 :
    FidCongHtCtrlOk nvFidHt256Cfg nvFidHt256Scr0 0 8 131072 := by
  refine ⟨nvFidHt256Scr0_len, by decide, by decide, by decide, ⟨13, by decide, by decide⟩, ?_, ?_⟩
  · have hlen1 : (List.replicate 262152 (0xFFFFFFFF#32 : BitVec 32)).length = 262152 :=
      List.length_replicate
    dsimp only [nvFidHt256Scr0]
    rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by omega)]
  · have hlen2 : ((List.replicate 262152 (0xFFFFFFFF#32 : BitVec 32)).set 6 8#32).length = 262152 :=
      by rw [List.length_set, List.length_replicate]
    dsimp only [nvFidHt256Scr0]
    rw [List.getElem?_set_self (by omega)]

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`): `full_cong_ht_grow_clear_m7` under `fidCongEnv`
grows the dynamic scratch hash table from `131,072` to `262,144` (`> 131,072`) buckets, zeroes
`res_sz := 0#64`, and clears all `262,144` slots to `0xFFFFFFFF#32` (`O(1)` symbolic proof). -/
theorem nv_fid_cong_ht_grow_clear_256k :
    Func.wp fidCongEnv full_cong_ht_grow_clear_m7_body (nvFidHt256Cfg.hdr, 0#64, ()) nvFidHt256Mem0
      (fun (r, ()) m' => ∃ (scr' : List (BitVec 32)) (rsz' : BitVec 64),
        let s' : FullState :=
          { nvFidHt256St0 with scratch := { nvFidHt256St0.scratch with
            scratch_buf := scr', res_sz := rsz' } }
        r = 262144#64 ∧ rsz' = 0#64 ∧
        FidCongHtCtrlOk nvFidHt256Cfg scr' 0 8 262144 ∧
        (∀ j < 262144, scr'[8 + j]? = some 0xFFFFFFFF#32) ∧
        s'.LengthsOk nvFidHt256Cfg ∧
        FullWitnessInv nvFidHt256Cfg nvFidF0 [] s'.core ∧
        nvFidF0.Unsat ∧ FullMem nvFidHt256Cfg s' m')
      (fun _ _ _ _ => False) := by
  have hlen0 := nvFidMkState4_lengths (sc := 262152) (hsc := by decide) 0#64 0#64 17#64 0
    (List.replicate 8 0#8) (List.replicate 4 0#32) (List.replicate 8 0#32)
    (List.replicate 4 0#32) (List.replicate 8 0#32) (List.replicate 8 0#32) nvFidHt256Scr0
    (Nat.zero_le _) rfl rfl rfl rfl rfl rfl nvFidHt256Scr0_len
  have hm0 := nvFidMkMem4_ok (sc := 262152) (hsc := by decide) 0#64 0#64 17#64 0
    (List.replicate 8 0#8) (List.replicate 4 0#32) (List.replicate 8 0#32)
    (List.replicate 4 0#32) (List.replicate 8 0#32) (List.replicate 8 0#32) nvFidHt256Scr0
    rfl rfl rfl rfl rfl rfl nvFidHt256Scr0_len
  refine fidCongEnv_htGrowClear_wp _ _ _ _
    ⟨nvFidHt256Cfg, nvFidHt256St0, emp, rfl, hlen0, hm0,
      fun ret scr' rsz' m' hscrl hlen' _ _ hspec hm' => ?_⟩
  obtain ⟨hret, hctrl', hrsz', _, hclr⟩ := hspec 8 131072 nvFidHt256CtrlOk0 (by decide) (by decide)
  have hret_bv : ret = 262144#64 := BitVec.eq_of_toNat_eq (by rw [hret]; decide)
  rw [sep_emp] at hm'
  exact ⟨scr', rsz', hret_bv, hrsz', by simpa using hctrl', fun j hj => hclr j hj, hlen',
    nvFidMk4_witness_empty, nvFidF0_unsat, hm'⟩

/-! ## 5. `full_cong_sift_pairs_fid` & `full_cong_sort_pairs_fid` UNSAT NV (`BUG-CONG-00`) -/

def nvFidPairCfg : FullCfg := nvFidMkCfg4 4 (by decide)
def nvFidPairScr0 : List (BitVec 32) := [10#32, 1#32, 10#32, 2#32]
def nvFidPairScr1 : List (BitVec 32) := [10#32, 2#32, 10#32, 1#32]
def nvFidPairSt0 : FullState :=
  nvFidMkState4 0#64 0#64 0#64 0 (List.replicate 8 0#8) (List.replicate 4 0#32)
    (List.replicate 8 0#32) (List.replicate 4 0#32) (List.replicate 8 0#32) (List.replicate 8 0#32)
    nvFidPairScr0
def nvFidPairSt1 : FullState :=
  nvFidMkState4 0#64 0#64 0#64 0 (List.replicate 8 0#8) (List.replicate 4 0#32)
    (List.replicate 8 0#32) (List.replicate 4 0#32) (List.replicate 8 0#32) (List.replicate 8 0#32)
    nvFidPairScr1
def nvFidPairMem0 : Mem 64 :=
  nvFidMkMem4 4 (by decide) 0#64 0#64 0#64 0 (List.replicate 8 0#8) (List.replicate 4 0#32)
    (List.replicate 8 0#32) (List.replicate 4 0#32) (List.replicate 8 0#32) (List.replicate 8 0#32)
    nvFidPairScr0
def nvFidPairMem1 : Mem 64 :=
  nvFidMkMem4 4 (by decide) 0#64 0#64 0#64 0 (List.replicate 8 0#8) (List.replicate 4 0#32)
    (List.replicate 8 0#32) (List.replicate 4 0#32) (List.replicate 8 0#32) (List.replicate 8 0#32)
    nvFidPairScr1

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`): `full_cong_sift_pairs_fid` under `fidCongEnv`
exercises equal-key tie-breaking (`(10, 1)` vs `(10, 2)`) and swaps them to `[10, 2, 10, 1]`. -/
theorem nv_fid_cong_sift_pairs :
    Func.wp fidCongEnv full_cong_sift_pairs_fid_body (nvFidPairCfg.pScratchBuf, 0#64, 2#64, ())
      nvFidPairMem0
      (fun () m' =>
        nvFidPairSt1.scratch.scratch_buf = [10#32, 2#32, 10#32, 1#32] ∧
        nvFidPairSt1.LengthsOk nvFidPairCfg ∧
        FullWitnessInv nvFidPairCfg nvFidF0 [] nvFidPairSt1.core ∧
        nvFidF0.Unsat ∧ FullMem nvFidPairCfg nvFidPairSt1 m')
      (fun _ _ _ _ => False) := by
  have hm0 := focus_full_scratch_buf (nvFidMkMem4_ok (sc := 4) (hsc := by decide)
    0#64 0#64 0#64 0 (List.replicate 8 0#8) (List.replicate 4 0#32) (List.replicate 8 0#32)
    (List.replicate 4 0#32) (List.replicate 8 0#32) (List.replicate 8 0#32) nvFidPairScr0
    rfl rfl rfl rfl rfl rfl rfl)
  change (array (t := i32) nvFidPairCfg.pScratchBuf nvFidPairScr0 ⋆
    (FullScrBufRest nvFidPairCfg nvFidPairSt0 ⋆ emp)) nvFidPairMem0 at hm0
  unfold Func.wp full_cong_sift_pairs_fid_body
  m6_to_group
  refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
    (fun _ m => ∃ sc : List (BitVec 32), sc = nvFidPairScr1 ∧
      (array (t := i32) nvFidPairCfg.pScratchBuf sc ⋆
        (FullScrBufRest nvFidPairCfg nvFidPairSt0 ⋆ emp)) m)
    (fun rem (root, ()) m =>
      (rem = 1 ∧ root = 0#64 ∧ (array (t := i32) nvFidPairCfg.pScratchBuf nvFidPairScr0 ⋆
        (FullScrBufRest nvFidPairCfg nvFidPairSt0 ⋆ emp)) m) ∨
      (rem = 0 ∧ root = 1#64 ∧ (array (t := i32) nvFidPairCfg.pScratchBuf nvFidPairScr1 ⋆
        (FullScrBufRest nvFidPairCfg nvFidPairSt0 ⋆ emp)) m))
    ?_ ?_ ?_
  · rintro _ _ m ⟨sc, rfl, hmf⟩
    m6_steps
    have hm' := unfocus_full_scratch_buf hmf
    rw [sep_emp] at hm'
    have hst_eq : { nvFidPairSt0 with scratch := { nvFidPairSt0.scratch with
        scratch_buf := nvFidPairScr1 } } = nvFidPairSt1 := rfl
    rw [hst_eq] at hm'
    exact ⟨rfl,
      nvFidMkState4_lengths 0#64 0#64 0#64 0 (List.replicate 8 0#8) (List.replicate 4 0#32)
        (List.replicate 8 0#32) (List.replicate 4 0#32) (List.replicate 8 0#32)
        (List.replicate 8 0#32) nvFidPairScr1 (Nat.zero_le _) rfl rfl rfl rfl rfl rfl rfl,
      nvFidMk4_witness_empty, nvFidF0_unsat, hm'⟩
  · rintro Bk Lk rem ⟨root, ⟨⟩⟩ m hBk hLk (⟨rfl, rfl, hm0_l⟩ | ⟨rfl, rfl, hm1_l⟩)
    · m6_split_fast
      · m6_split_fast
        · exfalso; revert hc; decide
        · m6_to_group
          refine wp_join_group (ts := [i64, i32, i32])
            (fun (sw, sws, swr, ()) m1 => m1 = m ∧ sw = 1#64 ∧ sws = 10#32 ∧ swr = 2#32)
            ?_ ?_
          · rintro _ ⟨sw, sws, swr, ⟨⟩⟩ m1 ⟨hm1, hsw, hss, hsr⟩
            subst m1 hsw hss hsr; m6_to_group
            refine wp_join_group (ts := [i64, i32, i32])
              (fun (sw2, sws2, swr2, ()) m2 => m2 = m ∧ sw2 = 1#64 ∧ sws2 = 10#32 ∧ swr2 = 2#32)
              ?_ ?_
            · rintro _ ⟨sw2, sws2, swr2, ⟨⟩⟩ m2 ⟨hm2, hsw2, hss2, hsr2⟩
              subst m2 hsw2 hss2 hsr2; m6_steps
              m6_split_fast
              · exfalso; revert hc; dsimp only; decide
              · m6_steps
                rw [show (array (t := i32) nvFidPairCfg.pScratchBuf _) =
                    array (t := i32) nvFidPairCfg.pScratchBuf nvFidPairScr1 from
                  congrArg _ (by decide)] at hm
                exact hLk 0 (1#64, ()) _ (by omega) (Or.inr ⟨rfl, rfl, hm⟩)
            · intro J2 hJ2
              m6_split_fast
              · exfalso; revert hc; dsimp only; decide
              · m6_steps; exact hJ2 (1#64, 10#32, 2#32, ()) m ⟨rfl, rfl, rfl, rfl⟩
          · intro J1 hJ1
            m6_split_fast
            · exfalso; revert hc; decide
            · m6_split_fast
              · m6_split_fast
                · m6_steps; exact hJ1 (1#64, 10#32, 2#32, ()) m ⟨rfl, rfl, rfl, rfl⟩
                · exfalso; revert hc; dsimp only; decide
              · exfalso; revert hc; dsimp only; decide
      · exact Bool.noConfusion hc
    · m6_split_fast
      · m6_split_fast
        · m6_steps; exact hBk (1#64, ()) m ⟨nvFidPairScr1, rfl, hm1_l⟩
        · exfalso; revert hc; decide
      · exact Bool.noConfusion hc
  · intro _ Lk _ hLk; m6_let; exact hLk 1 (0#64, ()) nvFidPairMem0 (Or.inl ⟨rfl, rfl, hm0⟩)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`): `full_cong_sort_pairs_fid` under `fidCongEnv`
preserves `FidPairsOk (fun k r => k = 10#32 ∧ (r = 1#32 ∨ r = 2#32))` and `FullMem`. -/
theorem nv_fid_cong_sort_pairs :
    Func.wp fidCongEnv full_cong_sort_pairs_fid_body (nvFidPairCfg.pScratchBuf, 2#64, ())
      nvFidPairMem1
      (fun () m' => ∃ scr' : List (BitVec 32),
        let s' : FullState := { nvFidPairSt1 with scratch := { nvFidPairSt1.scratch with
          scratch_buf := scr' } }
        FidPairsOk (fun k r => k = 10#32 ∧ (r = 1#32 ∨ r = 2#32)) scr' 2 ∧
        s'.LengthsOk nvFidPairCfg ∧
        FullWitnessInv nvFidPairCfg nvFidF0 [] s'.core ∧
        nvFidF0.Unsat ∧ FullMem nvFidPairCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm0 := focus_full_scratch_buf (nvFidMkMem4_ok (sc := 4) (hsc := by decide)
    0#64 0#64 0#64 0 (List.replicate 8 0#8) (List.replicate 4 0#32) (List.replicate 8 0#32)
    (List.replicate 4 0#32) (List.replicate 8 0#32) (List.replicate 8 0#32) nvFidPairScr1
    rfl rfl rfl rfl rfl rfl rfl)
  change (array (t := i32) nvFidPairCfg.pScratchBuf nvFidPairScr1 ⋆
    (FullScrBufRest nvFidPairCfg nvFidPairSt1 ⋆ emp)) nvFidPairMem1 at hm0
  let P : BitVec 32 → BitVec 32 → Prop := fun k r => k = 10#32 ∧ (r = 1#32 ∨ r = 2#32)
  have hpok : FidPairsOk P nvFidPairScr1 2 := fun i hi => by
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> exact ⟨rfl, by decide⟩
  refine fidCongEnv_sortPairs_wp _ _ _ _
    ⟨P, nvFidPairScr1, FullScrBufRest nvFidPairCfg nvFidPairSt1 ⋆ emp, by decide, by decide,
      hpok, hm0, fun scr' m' hsl' hpok' _ hm' => ?_⟩
  have hmf := unfocus_full_scratch_buf hm'
  rw [sep_emp] at hmf
  exact ⟨scr', hpok',
    nvFidMkState4_lengths 0#64 0#64 0#64 0 (List.replicate 8 0#8) (List.replicate 4 0#32)
      (List.replicate 8 0#32) (List.replicate 4 0#32) (List.replicate 8 0#32)
      (List.replicate 8 0#32) scr' (Nat.zero_le _) rfl rfl rfl rfl rfl rfl hsl',
    nvFidMk4_witness_empty, nvFidF0_unsat, hmf⟩

/-! ## 6. `full_cong_merge_condeq_m7` Concrete Trivial-ITE UNSAT NV (`GAP-CONG-04`) -/

def nvFidIteCfg : FullCfg := nvFidMkCfg4 5 (by decide)
def nvFidIteWk32 : List (BitVec 32) := [4#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32]
def nvFidIteWk64 : List (BitVec 64) := [4#64, 0#64, 0#64, 0#64]
def nvFidIteFCur : List (List Nat) := [[1, 4], [0, 5]]
def nvFidIteSt0 : FullState :=
  nvFidMkState4 0#64 0#64 0#64 0 (List.replicate 8 0#8) (List.replicate 4 0#32)
    (List.replicate 8 0#32) (List.replicate 4 0#32) nvFidIteWk32 nvFidIteWk32
    (List.replicate 5 0#32)
def nvFidIteStEnd : FullState :=
  nvFidMkState4 0#64 0#64 0#64 0 (List.replicate 8 0#8) (List.replicate 4 0#32)
    (List.replicate 8 0#32) (List.replicate 4 0#32) nvFidIteWk32 nvFidIteWk32
    [0#32, (2#32 <<< 28#32) ||| 3#32, 2#32, 4#32, 4#32]
def nvFidIteMem0 : Mem 64 :=
  nvFidMkMem4 5 (by decide) 0#64 0#64 0#64 0 (List.replicate 8 0#8) (List.replicate 4 0#32)
    (List.replicate 8 0#32) (List.replicate 4 0#32) nvFidIteWk32 nvFidIteWk32
    (List.replicate 5 0#32)

private theorem nvFidIte_arr_eq (a : BitVec 64) :
    array (t := i32) a nvFidIteWk32 = array64 a nvFidIteWk64 := by
  rw [nv_array_eq_bytes (t := i32) a nvFidIteWk32 (by decide), array64_eq_array,
    nv_array_eq_bytes (t := i64) a nvFidIteWk64 (by decide)]
  have hbytes : bytesOf (t := i32) nvFidIteWk32 = bytesOf (t := i64) nvFidIteWk64 := by decide
  rw [hbytes]

private theorem c0_ld_nvIte_wk1_64 {scr : List (BitVec 32)} {i : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i.toNat < 4)
    (hm : (FullMem nvFidIteCfg
      { nvFidIteSt0 with scratch := { nvFidIteSt0.scratch with scratch_buf := scr } } ⋆ R) m) :
    loadVal m i64 (nvFidIteCfg.pWorkStk1 + i * 8) = some nvFidIteWk64[i.toNat] := by
  let s := { nvFidIteSt0 with scratch := { nvFidIteSt0.scratch with scratch_buf := scr } }
  unfold FullMem FullScratchArrays FullScrWksArrs at hm
  change (dimacsState nvFidIteCfg.hdr (BitVec.ofNat 64 nvFidIteCfg.mv)
      (BitVec.ofNat 64 nvFidIteCfg.nc) s.core.d_cur s.core.d_val ⋆
    array64 (nvFidIteCfg.hdr + 32) (Full.hdrTailWords nvFidIteCfg s) ⋆
    FullCoreArrays nvFidIteCfg s.core ⋆
    (FullScrByteArrs nvFidIteCfg s.scratch ⋆ FullScrU32A nvFidIteCfg s.scratch ⋆
     (array (t := i32) nvFidIteCfg.pWsort s.scratch.wsort ⋆
      array (t := i32) nvFidIteCfg.pWorkStk1 nvFidIteWk32 ⋆
      array (t := i32) nvFidIteCfg.pWorkStk2 s.scratch.work_stk2 ⋆
      array (t := i32) nvFidIteCfg.pTarjanMark s.scratch.tarjan_mark ⋆
      array (t := i32) nvFidIteCfg.pTarjanReach s.scratch.tarjan_reach) ⋆
     FullScrMetaArrs nvFidIteCfg s.scratch ⋆ FullScrDynArrs nvFidIteCfg s.scratch) ⋆
    nvFidIteCfg.pad ⋆ R) m at hm
  rw [nvFidIte_arr_eq] at hm
  rw [show nvFidIteCfg.pWorkStk1 + i * 8 = nvFidIteCfg.pWorkStk1 + BitVec.ofNat 64 (8 * i.toNat) by
    rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_mul_ofNat]]
  have hm_wk : (array64 nvFidIteCfg.pWorkStk1 nvFidIteWk64 ⋆
    (dimacsState nvFidIteCfg.hdr (BitVec.ofNat 64 nvFidIteCfg.mv)
        (BitVec.ofNat 64 nvFidIteCfg.nc) s.core.d_cur s.core.d_val ⋆
      array64 (nvFidIteCfg.hdr + 32) (Full.hdrTailWords nvFidIteCfg s) ⋆
      FullCoreArrays nvFidIteCfg s.core ⋆
      (FullScrByteArrs nvFidIteCfg s.scratch ⋆ FullScrU32A nvFidIteCfg s.scratch ⋆
       (array (t := i32) nvFidIteCfg.pWsort s.scratch.wsort ⋆
        array (t := i32) nvFidIteCfg.pWorkStk2 s.scratch.work_stk2 ⋆
        array (t := i32) nvFidIteCfg.pTarjanMark s.scratch.tarjan_mark ⋆
        array (t := i32) nvFidIteCfg.pTarjanReach s.scratch.tarjan_reach) ⋆
       FullScrMetaArrs nvFidIteCfg s.scratch ⋆ FullScrDynArrs nvFidIteCfg s.scratch) ⋆
      nvFidIteCfg.pad ⋆ R)) m := sep_ac hm
  exact loadVal_array64 hi hm_wk

private theorem c0_ld_nvIte_wk1_0 {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem nvFidIteCfg
      { nvFidIteSt0 with scratch := { nvFidIteSt0.scratch with scratch_buf := scr } } ⋆ R) m) :
    loadVal m i64 (nvFidIteCfg.pWorkStk1 + 0 * 8) = some nvFidIteWk64[0] :=
  c0_ld_nvIte_wk1_64 (i := 0#64) (by decide) hm

private theorem c0_ld_nvIte_wk1_z {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem nvFidIteCfg
      { nvFidIteSt0 with scratch := { nvFidIteSt0.scratch with scratch_buf := scr } } ⋆ R) m) :
    loadVal m i64 (nvFidIteCfg.pWorkStk1 + 0) = some nvFidIteWk64[0] := by
  simpa using c0_ld_nvIte_wk1_0 hm

private theorem c0_ld_nvIte_wk2_64 {scr : List (BitVec 32)} {i : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i.toNat < 4)
    (hm : (FullMem nvFidIteCfg
      { nvFidIteSt0 with scratch := { nvFidIteSt0.scratch with scratch_buf := scr } } ⋆ R) m) :
    loadVal m i64 (nvFidIteCfg.pWorkStk2 + i * 8) = some nvFidIteWk64[i.toNat] := by
  let s := { nvFidIteSt0 with scratch := { nvFidIteSt0.scratch with scratch_buf := scr } }
  unfold FullMem FullScratchArrays FullScrWksArrs at hm
  change (dimacsState nvFidIteCfg.hdr (BitVec.ofNat 64 nvFidIteCfg.mv)
      (BitVec.ofNat 64 nvFidIteCfg.nc) s.core.d_cur s.core.d_val ⋆
    array64 (nvFidIteCfg.hdr + 32) (Full.hdrTailWords nvFidIteCfg s) ⋆
    FullCoreArrays nvFidIteCfg s.core ⋆
    (FullScrByteArrs nvFidIteCfg s.scratch ⋆ FullScrU32A nvFidIteCfg s.scratch ⋆
     (array (t := i32) nvFidIteCfg.pWsort s.scratch.wsort ⋆
      array (t := i32) nvFidIteCfg.pWorkStk1 s.scratch.work_stk1 ⋆
      array (t := i32) nvFidIteCfg.pWorkStk2 nvFidIteWk32 ⋆
      array (t := i32) nvFidIteCfg.pTarjanMark s.scratch.tarjan_mark ⋆
      array (t := i32) nvFidIteCfg.pTarjanReach s.scratch.tarjan_reach) ⋆
     FullScrMetaArrs nvFidIteCfg s.scratch ⋆ FullScrDynArrs nvFidIteCfg s.scratch) ⋆
    nvFidIteCfg.pad ⋆ R) m at hm
  rw [nvFidIte_arr_eq] at hm
  rw [show nvFidIteCfg.pWorkStk2 + i * 8 = nvFidIteCfg.pWorkStk2 + BitVec.ofNat 64 (8 * i.toNat) by
    rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_mul_ofNat]]
  have hm_wk : (array64 nvFidIteCfg.pWorkStk2 nvFidIteWk64 ⋆
    (dimacsState nvFidIteCfg.hdr (BitVec.ofNat 64 nvFidIteCfg.mv)
        (BitVec.ofNat 64 nvFidIteCfg.nc) s.core.d_cur s.core.d_val ⋆
      array64 (nvFidIteCfg.hdr + 32) (Full.hdrTailWords nvFidIteCfg s) ⋆
      FullCoreArrays nvFidIteCfg s.core ⋆
      (FullScrByteArrs nvFidIteCfg s.scratch ⋆ FullScrU32A nvFidIteCfg s.scratch ⋆
       (array (t := i32) nvFidIteCfg.pWsort s.scratch.wsort ⋆
        array (t := i32) nvFidIteCfg.pWorkStk1 s.scratch.work_stk1 ⋆
        array (t := i32) nvFidIteCfg.pTarjanMark s.scratch.tarjan_mark ⋆
        array (t := i32) nvFidIteCfg.pTarjanReach s.scratch.tarjan_reach) ⋆
       FullScrMetaArrs nvFidIteCfg s.scratch ⋆ FullScrDynArrs nvFidIteCfg s.scratch) ⋆
      nvFidIteCfg.pad ⋆ R)) m := sep_ac hm
  exact loadVal_array64 hi hm_wk

private theorem c0_ld_nvIte_wk2_0 {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem nvFidIteCfg
      { nvFidIteSt0 with scratch := { nvFidIteSt0.scratch with scratch_buf := scr } } ⋆ R) m) :
    loadVal m i64 (nvFidIteCfg.pWorkStk2 + 0 * 8) = some nvFidIteWk64[0] :=
  c0_ld_nvIte_wk2_64 (i := 0#64) (by decide) hm

private theorem c0_ld_nvIte_wk2_z {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem nvFidIteCfg
      { nvFidIteSt0 with scratch := { nvFidIteSt0.scratch with scratch_buf := scr } } ⋆ R) m) :
    loadVal m i64 (nvFidIteCfg.pWorkStk2 + 0) = some nvFidIteWk64[0] := by
  simpa using c0_ld_nvIte_wk2_0 hm

attribute [local c0_load] c0_ld_nvIte_wk1_64 c0_ld_nvIte_wk1_0 c0_ld_nvIte_wk1_z
  c0_ld_nvIte_wk2_64 c0_ld_nvIte_wk2_0 c0_ld_nvIte_wk2_z

private theorem nvFidIte_witness :
    FullWitnessInv nvFidIteCfg nvFidF0 nvFidIteFCur nvFidIteStEnd.core :=
  nv_witness_empty
    ⟨(varsBoundedBool_iff 4 nvFidIteFCur).mp rfl, fun hu => False.elim (by
      rw [CNF.unsat_iff_not_sat] at hu
      exact hu (fun _ => true) ((cnf_sat_cnfOfClauses_iff (fun _ => true) nvFidIteFCur).mpr
        fun cl hcl => by
          simp only [nvFidIteFCur, List.mem_cons, List.not_mem_nil, or_false] at hcl
          rcases hcl with rfl | rfl <;> rw [← clauseEvalVal_iff] <;> decide))⟩
    rfl rfl (fun l hl => by
      have hcv : nvFidIteStEnd.core.cur_vars = 4 := rfl
      rw [hcv] at hl
      have hwv : nvFidIteStEnd.core.wvec = List.replicate 16 0#32 := rfl
      unfold fullWatchOffCore fullWatchSizeCore; rw [hwv]
      simp only [List.getElem?_replicate, show 2 * l < 16 by omega, show 2 * l + 1 < 16 by omega,
        ↓reduceIte, Option.getD_some]
      exact ⟨rfl, rfl⟩)
    rfl rfl rfl (fun l hl => by
      have hcv : nvFidIteStEnd.core.cur_vars = 4 := rfl
      rw [hcv] at hl
      have hv : nvFidIteStEnd.core.vals = List.replicate 8 0#8 := rfl
      rw [hv]
      simp only [List.getElem?_replicate, show l < 8 by omega, ↓reduceIte, Option.getD_some])

private theorem nvFidIte_gateSeq :
    FidGateSeqOk 64 nvFidIteFCur 4 [0#32, (2#32 <<< 28#32) ||| 3#32, 2#32, 4#32, 4#32] 5 0 := by
  have hite : IteGateDef (cnfOfClauses nvFidIteFCur) 0 2 4 4 :=
    iteGateDef_of_eval_eq fun α hα => by
      have hc1 := (cnf_sat_cnfOfClauses_iff α nvFidIteFCur).mp hα [1, 4] List.mem_cons_self
      have hc2 := (cnf_sat_cnfOfClauses_iff α nvFidIteFCur).mp hα [0, 5]
        (List.mem_cons_of_mem _ List.mem_cons_self)
      rw [← clauseEvalVal_iff] at hc1 hc2
      have h04 : evalLitVal α 0 = evalLitVal α 4 := by
        cases h0 : α 0 <;> cases h4 : α 2 <;>
          simp_all [clauseEvalVal, evalLitVal, litVar, litSign]
      rw [h04]; cases evalLitVal α 2 <;> rfl
  have hm : (((2#32 : BitVec 32) <<< 28#32 ||| 3#32) &&& 0xFF#32).toNat = 3 := by decide
  refine FidGateSeqOk.step
    ⟨0#32, (2#32 <<< 28#32) ||| 3#32, rfl, rfl, by decide, by rw [hm]; decide,
      by decide, by rw [hm]; decide,
      (fun k hk => by
        rw [hm] at hk
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
          refine ⟨_, rfl, by decide⟩),
      Or.inr (Or.inr ⟨by decide, hm, hite⟩)⟩ .done

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`): `full_cong_merge_condeq_m7` under `fidCongEnv`
merges `pos_eq = [4#64]` and `neg_eq = [4#64]` into a trivial `e == t = 4#32` ITE gate at
`scratch_buf[0..4]`, returning `r = 5#32` and `FidGateSeqOk 64`. -/
theorem nv_fid_cong_merge_condeq_trivial_ite :
    Func.wp fidCongEnv full_cong_merge_condeq_m7_body
      (nvFidIteCfg.hdr, 2#32, 1#64, 1#64, 0#32, 5#32, ()) nvFidIteMem0
      (fun (r, ()) m' =>
        r = 5#32 ∧
        nvFidIteStEnd.scratch.scratch_buf =
          [0#32, (2#32 <<< 28#32) ||| 3#32, 2#32, 4#32, 4#32] ∧
        FidGateSeqOk 64 nvFidIteFCur 4 nvFidIteStEnd.scratch.scratch_buf 5 0 ∧
        nvFidIteStEnd.LengthsOk nvFidIteCfg ∧
        FullWitnessInv nvFidIteCfg nvFidF0 nvFidIteFCur nvFidIteStEnd.core ∧
        nvFidF0.Unsat ∧ FullMem nvFidIteCfg nvFidIteStEnd m')
      (fun _ _ _ _ => False) := by
  have hm0 := nvFidMkMem4_ok (sc := 5) (hsc := by decide) 0#64 0#64 0#64 0
    (List.replicate 8 0#8) (List.replicate 4 0#32) (List.replicate 8 0#32)
    (List.replicate 4 0#32) nvFidIteWk32 nvFidIteWk32 (List.replicate 5 0#32)
    rfl rfl rfl rfl rfl rfl rfl
  change (FullMem nvFidIteCfg nvFidIteSt0 ⋆ emp) nvFidIteMem0 at hm0
  unfold Func.wp full_cong_merge_condeq_m7_body
  m6_split_fast
  · exfalso; revert hc; decide
  · m6_split_fast
    · exfalso; revert hc; decide
    · m6_split_fast
      · exfalso; revert hc; decide
      · m6_split_fast
        · exfalso; revert hc; decide
        · m6_steps
          refine wp_loop_inv (ts := [i32, i64, i64])
            (fun (gl, p, q, ()) m =>
              (gl = 0#32 ∧ p = 0#64 ∧ q = 0#64 ∧ (FullMem nvFidIteCfg nvFidIteSt0 ⋆ emp) m) ∨
              (gl = 5#32 ∧ p = 1#64 ∧ q = 0#64 ∧ (FullMem nvFidIteCfg nvFidIteStEnd ⋆ emp) m))
            (fun (_, p, _, ()) _ => 1 - p.toNat)
            (fun J hJ => by
              m6_steps
              exact hJ (0#32, 0#64, 0#64, ()) nvFidIteMem0 (Or.inl ⟨rfl, rfl, rfl, hm0⟩))
            (fun J (gl, p, q, ()) m hloop ih => ?_)
          rcases hloop with ⟨rfl, rfl, rfl, hm_0⟩ | ⟨rfl, rfl, rfl, hm_end⟩
          · m6_split_fast
            · m6_split_fast
              · m6_split_fast
                · m6_steps; m6_split_fast
                  · exfalso; revert hc; dsimp only; decide
                  · m6_split_fast
                    · exfalso; revert hc; dsimp only; decide
                    · m6_to_group
                      refine wp_join_group (ts := [i32, i64])
                        (fun (gl2, _q2, ()) m2 => gl2 = 5#32 ∧
                          (FullMem nvFidIteCfg nvFidIteStEnd ⋆ emp) m2)
                        (fun _ ⟨gl2, _q2, ⟨⟩⟩ m2 ⟨hgl2, hm2⟩ => by
                          subst gl2; m6_steps
                          exact ih (5#32, 1#64, 0#64, ()) m2 (by decide)
                            (Or.inr ⟨rfl, rfl, rfl, hm2⟩))
                        (fun Jq hJq => ?_)
                      refine wp_loop_inv (ts := [i32, i64])
                        (fun (gl2, q2, ()) m2 =>
                          (gl2 = 0#32 ∧ q2 = 0#64 ∧ (FullMem nvFidIteCfg nvFidIteSt0 ⋆ emp) m2) ∨
                          (gl2 = 5#32 ∧ q2 = 1#64 ∧ (FullMem nvFidIteCfg nvFidIteStEnd ⋆ emp) m2))
                        (fun (_, q2, ()) _ => 1 - q2.toNat)
                        (fun Jq2 hJq2 => by
                          m6_steps
                          exact hJq2 (0#32, 0#64, ()) m (Or.inl ⟨rfl, rfl, hm_0⟩))
                        (fun Jq2 (gl2, q2, ()) m2 hq2 ihq2 => ?_)
                      rcases hq2 with ⟨rfl, rfl, hm2_0⟩ | ⟨rfl, rfl, hm2_end⟩
                      · m6_split_fast
                        · m6_split_fast
                          · m6_steps; m6_split_fast
                            · exfalso; revert hc; dsimp only; decide
                            · m6_to_group
                              refine wp_join_group (ts := [i32])
                                (fun (gl3, ()) m3 => gl3 = 5#32 ∧
                                  (FullMem nvFidIteCfg nvFidIteStEnd ⋆ emp) m3)
                                (fun _ ⟨gl3, ⟨⟩⟩ m3 ⟨hgl3, hm3⟩ => by
                                  subst gl3; m6_steps
                                  exact ihq2 (5#32, 1#64, ()) m3 (by decide)
                                    (Or.inr ⟨rfl, rfl, hm3⟩))
                                (fun J3 hJ3 => ?_)
                              m6_split_fast
                              · m6_to_group
                                refine wp_join_group (ts := [i32, i32, i32])
                                  (fun (yy, tt, ee, ()) mr => mr = m2 ∧
                                    yy = 0#32 ∧ tt = 4#32 ∧ ee = 4#32)
                                  ?_ ?_
                                · rintro _ ⟨yy, tt, ee, ⟨⟩⟩ mr ⟨hmr, hyy, htt, hee⟩
                                  subst mr hyy htt hee
                                  have hb0 : ((0#32 : BitVec 32).setWidth 64).toNat <
                                      nvFidIteSt0.scratch.scratch_buf.length := by decide
                                  have hb1 : ((0#32 : BitVec 32).setWidth 64 + 1#64).toNat <
                                      nvFidIteSt0.scratch.scratch_buf.length := by decide
                                  have hb2 : ((0#32 : BitVec 32).setWidth 64 + 2#64).toNat <
                                      nvFidIteSt0.scratch.scratch_buf.length := by decide
                                  have hb3 : ((0#32 : BitVec 32).setWidth 64 + 3#64).toNat <
                                      nvFidIteSt0.scratch.scratch_buf.length := by decide
                                  have hb4 : ((0#32 : BitVec 32).setWidth 64 + 4#64).toNat <
                                      nvFidIteSt0.scratch.scratch_buf.length := by decide
                                  m6_steps
                                  have hm_f := focus_full_scratch_buf hm
                                  rw [show (array (t := i32) nvFidIteCfg.pScratchBuf _) =
                                      array (t := i32) nvFidIteCfg.pScratchBuf
                                        nvFidIteStEnd.scratch.scratch_buf from
                                    congrArg _ (by decide)] at hm_f
                                  change (array (t := i32) nvFidIteCfg.pScratchBuf
                                      nvFidIteStEnd.scratch.scratch_buf ⋆
                                    (FullScrBufRest nvFidIteCfg nvFidIteSt0 ⋆ emp)) _ at hm_f
                                  have hm_u : (FullMem nvFidIteCfg nvFidIteStEnd ⋆ emp) m :=
                                    unfocus_full_scratch_buf hm_f
                                  exact hJ3 (5#32, ()) _ ⟨rfl, hm_u⟩
                                · intro J4 hJ4
                                  m6_split_fast
                                  · exfalso; revert hc; dsimp only; decide
                                  · m6_steps
                                    exact hJ4 (0#32, 4#32, 4#32, ()) m2 ⟨rfl, rfl, rfl, rfl⟩
                              · exfalso; revert hc; dsimp only; decide
                          · exfalso; revert hc; dsimp only; decide
                        · exfalso; revert hc; dsimp only; decide
                      · m6_split_fast
                        · exfalso; revert hc; dsimp only; decide
                        · m6_steps; exact hJq (5#32, 1#64, ()) m2 ⟨rfl, hm2_end⟩
                · exfalso; revert hc; dsimp only; decide
              · exfalso; revert hc; dsimp only; decide
            · exfalso; revert hc; decide
          · m6_split_fast
            · exfalso; revert hc; decide
            · m6_steps
              rw [sep_emp] at hm_end
              exact ⟨rfl, rfl, nvFidIte_gateSeq,
                nvFidMkState4_lengths 0#64 0#64 0#64 0 (List.replicate 8 0#8)
                  (List.replicate 4 0#32) (List.replicate 8 0#32) (List.replicate 4 0#32)
                  nvFidIteWk32 nvFidIteWk32 [0#32, (2#32 <<< 28#32) ||| 3#32, 2#32, 4#32, 4#32]
                  (Nat.zero_le _) rfl rfl rfl rfl rfl rfl rfl,
                nvFidIte_witness, nvFidF0_unsat, hm_end⟩

/-! ## 7. `full_cong_eval_gate` XOR Self-Cancellation UNSAT NV (`GAP-CONG-02` + UNSAT) -/

def nvFidEvalCfg : FullCfg := nvFidMkCfg4 4 (by decide)
def nvFidEvalFCur : List (List Nat) := [[3]]
def nvFidEvalVals0 : List (BitVec 8) := [0#8, 0#8, 0xFF#8, 1#8, 0#8, 0#8, 0#8, 0#8]
def nvFidEvalTrl0 : List (BitVec 32) := [3#32, 0#32, 0#32, 0#32]
def nvFidEvalRepr0 : List (BitVec 32) := (List.range 8).map (fun l => BitVec.ofNat 32 l)
def nvFidEvalScr0 : List (BitVec 32) := [0#32, (1#32 <<< 28#32) ||| 2#32, 0#32, 3#32]
def nvFidEvalSt0 : FullState :=
  nvFidMkState4 1#64 0#64 0#64 1 nvFidEvalVals0 nvFidEvalTrl0 nvFidEvalRepr0
    (List.replicate 4 0#32) (List.replicate 8 0#32) (List.replicate 8 0#32) nvFidEvalScr0
def nvFidEvalMem0 : Mem 64 :=
  nvFidMkMem4 4 (by decide) 1#64 0#64 0#64 1 nvFidEvalVals0 nvFidEvalTrl0 nvFidEvalRepr0
    (List.replicate 4 0#32) (List.replicate 8 0#32) (List.replicate 8 0#32) nvFidEvalScr0

private theorem nvFidEval_repr0_inv : FullCongReprInv nvFidEvalFCur 8 nvFidEvalRepr0 := by
  have hrl : nvFidEvalRepr0.length = 8 := by decide
  refine ⟨⟨by omega, fun l hl => ?_⟩, fun l hl => ?_⟩
  · have hget : (nvFidEvalRepr0[l]?.getD 0#32).toNat = l := by
      simp [nvFidEvalRepr0, hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : l < 2 ^ 32)]
    omega
  · have hget : (nvFidEvalRepr0[l]?.getD 0#32).toNat = l := by
      simp [nvFidEvalRepr0, hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : l < 2 ^ 32)]
    rw [hget]; exact nv_litEquiv_refl _ _

private theorem nvFidEval_witness0 :
    FullWitnessInv nvFidEvalCfg nvFidF0 nvFidEvalFCur nvFidEvalSt0.core := by
  let k := nvFidEvalSt0.core
  have hte : k.trail_end = 1 := rfl
  have hcl : k.cur_level = 0 := rfl
  have hdm : k.dense_mode = 1#64 := rfl
  have hwlen : k.wlen = 0 := rfl
  have hext : ExtUnsatSound nvFidF0 4 nvFidEvalFCur :=
    ⟨(varsBoundedBool_iff 4 nvFidEvalFCur).mp rfl, fun hu => False.elim (by
      rw [CNF.unsat_iff_not_sat] at hu
      exact hu (fun _ => false)
        ((cnf_sat_cnfOfClauses_iff (fun _ => false) nvFidEvalFCur).mpr fun cl hcl => by
          simp only [nvFidEvalFCur, List.mem_singleton] at hcl; subst hcl
          rw [← clauseEvalVal_iff]; decide))⟩
  have har : FullArenaClausesInv nvFidEvalCfg nvFidEvalFCur k :=
    ⟨Or.inl rfl, fun r hr => by simp [fullArenaClauseRefsCore, k, nvFidEvalSt0,
        nvFidMkState4, nvFidMkCore4, fullArenaScanRefs] at hr,
      fun r hr => by simp [fullArenaClauseRefsCore, k, nvFidEvalSt0,
        nvFidMkState4, nvFidMkCore4, fullArenaScanRefs] at hr,
      fun r hr => by simp [fullArenaClauseRefsCore, k, nvFidEvalSt0,
        nvFidMkState4, nvFidMkCore4, fullArenaScanRefs] at hr,
      fun r hr => by simp [fullArenaClauseRefsCore, k, nvFidEvalSt0,
        nvFidMkState4, nvFidMkCore4, fullArenaScanRefs] at hr⟩
  have hwat : ModeWatchesInv nvFidEvalFCur k := by
    unfold ModeWatchesInv
    have hne : ¬ (k.dense_mode = 0#64) := by decide
    rw [ite_eq_right hne]
    exact DenseWatchesInv.of_slices
      (fun l hl => by
        rw [hwlen]
        exact (by decide : ∀ q : Fin 8,
          fullWatchOffCore k q.1 + fullWatchSizeCore k q.1 ≤ 0) ⟨l, hl⟩)
      (fun l hl hp => absurd hp (by
        have hz := (by decide : ∀ q : Fin 8, fullWatchSizeCore k q.1 = 0) ⟨l, hl⟩
        dsimp only at hz; omega))
      (fun l1 _ h1 _ _ hp => absurd hp (by
        have hz := (by decide : ∀ q : Fin 8, fullWatchSizeCore k q.1 = 0) ⟨l1, h1⟩
        dsimp only at hz; omega))
      (fun l hl => by
        have hws : fullWatchSizeCore k l = 0 :=
          (by decide : ∀ q : Fin 8, fullWatchSizeCore k q.1 = 0) ⟨l, hl⟩
        have hwo : fullWatchOffCore k l = 0 :=
          (by decide : ∀ q : Fin 8, fullWatchOffCore k q.1 = 0) ⟨l, hl⟩
        rw [hwo, hws]; exact .empty)
  exact
    { ext_sound := hext
      inconsistent_sound := fun h => absurd rfl h
      arena := har
      watches := hwat
      cur_level_le := by decide
      trail_lits_lt := fun i hi => (by decide : ∀ q : Fin 1,
        (k.trl[q.1]?.getD 0#32).toNat < 8) ⟨i, hi⟩
      trail_vars_nodup := fun i j hi hj heq => congrArg Fin.val ((by decide : ∀ a b : Fin 1,
        (k.trl[a.1]?.getD 0#32).toNat / 2 = (k.trl[b.1]?.getD 0#32).toNat / 2 → a = b)
          ⟨i, hi⟩ ⟨j, hj⟩ heq)
      vals_domain := fun l hl => (by decide : ∀ q : Fin 8,
        let v := k.vals[q.1]?.getD 0#8
        v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) ⟨l, hl⟩
      vals_true_iff := fun l hl => by
        refine ⟨fun hv => ?_, ?_⟩
        · have hc := (by decide : ∀ q : Fin 8,
            k.vals[q.1]?.getD 0#8 = 1#8 →
            ∃ i : Fin 1, (k.trl[i.1]?.getD 0#32).toNat = q.1) ⟨l, hl⟩ hv
          exact ⟨hc.choose.1, hc.choose.2, hc.choose_spec⟩
        · rintro ⟨i, hi, htr⟩
          have hc := (by decide : ∀ q : Fin 1,
            k.vals[(k.trl[q.1]?.getD 0#32).toNat]?.getD 0#8 = 1#8) ⟨i, hi⟩
          rw [← htr]; exact hc
      vals_false_iff := fun l hl => by
        refine ⟨fun hv => ?_, ?_⟩
        · have hc := (by decide : ∀ q : Fin 8,
            k.vals[q.1]?.getD 0#8 = 0xFF#8 →
            ∃ i : Fin 1, (k.trl[i.1]?.getD 0#32).toNat = q.1 ^^^ 1) ⟨l, hl⟩ hv
          exact ⟨hc.choose.1, hc.choose.2, hc.choose_spec⟩
        · rintro ⟨i, hi, htr⟩
          have hc := (by decide : ∀ q : Fin 1,
            k.vals[(k.trl[q.1]?.getD 0#32).toNat ^^^ 1]?.getD 0#8 = 0xFF#8) ⟨i, hi⟩
          have hl_eq : l = (k.trl[i]?.getD 0#32).toNat ^^^ 1 := by
            rw [htr, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
          rw [hl_eq]; exact hc
      lvl_le := fun i hi => (by decide : ∀ q : Fin 1,
        (k.lvl[(k.trl[q.1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ 0) ⟨i, hi⟩
      dec_earliest := fun i j hi hj hlv => by
        rw [hte] at hj
        have hj0 : j = 0 := by omega
        subst hj0
        have hv : (k.lvl[(k.trl[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by decide
        omega
      levels_inhabited := fun L h1 h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by
        rw [hte] at hi; have hi0 : i = 0 := by omega
        subst hi0
        have htr0 : (k.trl[0]?.getD 0#32).toNat = 3 := by decide
        rw [htr0, CNF.entails_clause_def]; intro α hα
        exact (CNF.sat_iff_all_mem_sat.mp hα) _
          (CNF.Internal.mem_iff.mpr (by simp [nvFidEvalFCur, cnfOfClauses]))
      trail_pos_inv := fun i hi => (by decide : ∀ q : Fin 1,
        (k.trail_pos[(k.trl[q.1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = q.1) ⟨i, hi⟩
      level0_rsn_none := fun i hi _ => (by decide : ∀ q : Fin 1,
        k.rsns[(k.trl[q.1]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ⟨i, hi⟩
      frame_trail_lt := fun L hL => by rw [hcl] at hL; have h0 : L = 0 := by omega
                                       subst h0; decide
      frame_trail_mono := fun L1 L2 h12 hL2 => by
        rw [hcl] at hL2; have h1 : L1 = 0 := by omega
        have h2 : L2 = 0 := by omega
        subst h1 h2; exact Nat.le_refl _
      frame_trail_before_lt := fun L h1 h2 _ => by rw [hcl] at h2; omega
      frame_dec_lt := fun L h1 h2 => by rw [hcl] at h2; omega
      reason_inv := fun idx hidx hne => absurd (by
        rw [hte] at hidx; have hi0 : idx = 0 := by omega
        subst hi0; rfl) hne
      reason_lit_mem := fun idx hidx hne => absurd (by
        rw [hte] at hidx; have hi0 : idx = 0 := by omega
        subst hi0; rfl) hne }

private theorem litEquiv_eval3_3 {r : Nat} (h : LitEquiv (cnfOfClauses nvFidEvalFCur) 3 r)
    (hle : r ≤ 3) : r = 3 := by
  have hs1 : (cnfOfClauses nvFidEvalFCur).Sat (fun _ => false) :=
    (cnf_sat_cnfOfClauses_iff _ nvFidEvalFCur).mpr fun cl hcl => by
      simp only [nvFidEvalFCur, List.mem_singleton] at hcl; subst hcl
      rw [← clauseEvalVal_iff]; decide
  have hs2 : (cnfOfClauses nvFidEvalFCur).Sat (fun k => decide (k = 0)) :=
    (cnf_sat_cnfOfClauses_iff _ nvFidEvalFCur).mpr fun cl hcl => by
      simp only [nvFidEvalFCur, List.mem_singleton] at hcl; subst hcl
      rw [← clauseEvalVal_iff]; decide
  have e1 := litEquiv_eval hs1 h
  have e2 := litEquiv_eval hs2 h
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl
  · revert e1; decide
  · revert e2; decide
  · revert e1; decide
  · rfl

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`): `full_cong_eval_gate` under `fidCongEnv`
evaluates 2-input XOR gate `x0 = x0 ⊕ ~x1` with `~x1` fixed true at level 0 (`vals[3] = 1#8`),
cancels `x0` against the LHS (`self_i = 0`, `ua' = 0`, `lsign = 1`), writes
`h->inconsistent := 1#64`, and returns `r = 2#64`. -/
theorem nv_fid_cong_eval_gate_xor_selfcancel :
    Func.wp fidCongEnv full_cong_eval_gate_body
      (nvFidEvalCfg.hdr, 0#64, 4#64, 16#64, 0#32, 4#64, ()) nvFidEvalMem0
      (fun (r, ()) m' => ∃ s' : FullState,
        r = 2#64 ∧
        s'.core.inconsistent = 1#64 ∧
        s'.LengthsOk nvFidEvalCfg ∧
        FullCongReprInv nvFidEvalFCur 8 s'.core.repr ∧
        nvFidF0.Unsat ∧ FullMem nvFidEvalCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm0 := nvFidMkMem4_ok (sc := 4) (hsc := by decide) 1#64 0#64 0#64 1
    nvFidEvalVals0 nvFidEvalTrl0 nvFidEvalRepr0 (List.replicate 4 0#32)
    (List.replicate 8 0#32) (List.replicate 8 0#32) nvFidEvalScr0
    rfl rfl rfl rfl rfl rfl rfl
  change (FullMem nvFidEvalCfg nvFidEvalSt0 ⋆ emp) nvFidEvalMem0 at hm0
  have hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      fidCongEnv "full_cong_find" [i64, i32] [i32] a m Q X := fun _ _ _ _ => fidCongEnv_find
  unfold Func.wp full_cong_eval_gate_body
  m6_split_fast
  · exfalso; revert hc; decide
  · m6_split_fast
    · exfalso; revert hc; decide
    · m6_split_fast
      · exfalso; revert hc; decide
      · m6_steps; m6_call hFind
        refine ⟨nvFidEvalFCur, 8, nvFidEvalRepr0, FullReprRest nvFidEvalCfg nvFidEvalSt0 ⋆ emp,
          nvFidEval_repr0_inv,
          by have h0n : nvFidEvalScr0[(0#64 : BitVec 64).toNat]?.getD 0#32 = 0#32 := rfl
             have h0s : nvFidEvalSt0.scratch.scratch_buf[(0#64 : BitVec 64).toNat] = 0#32 := rfl
             rw [h0s]; decide,
          focus_full_repr hm0,
          fun lhs repr1 m1 hrl1 hrepr1 hlhs_le _ hlhs_eqv hm1 => ?_⟩
        have hlhs_z : lhs = 0#32 := BitVec.eq_of_toNat_eq (by
          change lhs.toNat ≤ 0 at hlhs_le
          rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega)
        subst hlhs_z
        let st1 : FullState :=
          { nvFidEvalSt0 with core := { nvFidEvalSt0.core with repr := repr1 } }
        have hm1' : (FullMem nvFidEvalCfg st1 ⋆ emp) m1 := unfocus_full_repr hm1
        m6_steps
        refine wp_loop_inv (ts := [i32])
          (fun (i, ()) mi =>
            (i = 0#32 ∧ ∃ ri : List (BitVec 32), ri.length = 8 ∧
              FullCongReprInv nvFidEvalFCur 8 ri ∧
              (FullMem nvFidEvalCfg { nvFidEvalSt0 with core :=
                { nvFidEvalSt0.core with repr := ri } } ⋆ emp) mi) ∨
            (i = 1#32 ∧ ∃ ri : List (BitVec 32), ri.length = 8 ∧
              FullCongReprInv nvFidEvalFCur 8 ri ∧
              (FullMem nvFidEvalCfg { nvFidEvalSt0 with core :=
                { nvFidEvalSt0.core with repr := ri, tmp := [0#32, 0#32, 0#32, 0#32] } } ⋆ emp)
                mi) ∨
            (i = 2#32 ∧ ∃ ri : List (BitVec 32), ri.length = 8 ∧
              FullCongReprInv nvFidEvalFCur 8 ri ∧
              (FullMem nvFidEvalCfg { nvFidEvalSt0 with core :=
                { nvFidEvalSt0.core with repr := ri, tmp := [0#32, 3#32, 0#32, 0#32] } } ⋆ emp)
                mi))
          (fun (i, ()) _ => 2 - i.toNat)
          (fun J1 hJ1 => by
            m6_let
            exact hJ1 (0#32, ()) m1 (Or.inl ⟨rfl, repr1, hrl1, hrepr1, hm1'⟩))
          (fun J1 (i, ()) mi hi ih1 => ?_)
        · rcases hi with ⟨rfl, ri, hrli, hrepri, hmi⟩ | ⟨rfl, ri, hrli, hrepri, hmi⟩ |
            ⟨rfl, ri, hrli, hrepri, hmi⟩
          · m6_split_fast
            · let st_i0 : FullState := { nvFidEvalSt0 with core := { nvFidEvalSt0.core with
                  repr := ri } }
              have hscr0_arr : ((0#64 : BitVec 64) + 2 + BitVec.ofNat 64 0).toNat <
                  st_i0.scratch.scratch_buf.length :=
                by change ((0#64 : BitVec 64) + 2 + BitVec.ofNat 64 0).toNat <
                    nvFidEvalScr0.length
                   decide
              m6_steps; m6_call hFind
              refine ⟨nvFidEvalFCur, 8, ri, FullReprRest nvFidEvalCfg _ ⋆ emp, hrepri,
                by have h2s : nvFidEvalSt0.scratch.scratch_buf[
                      ((0#64 : BitVec 64) + 2 + BitVec.ofNat 64 0).toNat] = 0#32 := rfl
                   rw [h2s]; decide,
                focus_full_repr hmi,
                fun r0 r0_repr m0 hrl0 hrepr0 hr0_le _ _ hm0_ => ?_⟩
              have hr0_z : r0 = 0#32 := BitVec.eq_of_toNat_eq (by
                change r0.toNat ≤ 0 at hr0_le
                rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega)
              subst hr0_z
              have hm0_un := unfocus_full_repr hm0_
              let st_r0 : FullState := { nvFidEvalSt0 with core := { nvFidEvalSt0.core with
                  repr := r0_repr } }
              have htmp0 : ((0#32 : BitVec 32).setWidth 64).toNat < st_r0.core.tmp.length := by
                rw [show st_r0.core.tmp.length = 4 from List.length_replicate]; decide
              m6_steps
              exact ih1 (1#32, ()) _ (by decide)
                (Or.inr (Or.inl ⟨rfl, r0_repr, hrl0.trans hrli, hrepr0, hm⟩))
            · exfalso; revert hc; decide
          · m6_split_fast
            · let st_i1 : FullState := { nvFidEvalSt0 with core := { nvFidEvalSt0.core with
                  repr := ri, tmp := [0#32, 0#32, 0#32, 0#32] } }
              have hscr1_arr : ((0#64 : BitVec 64) + 2 + BitVec.ofNat 64 1).toNat <
                  st_i1.scratch.scratch_buf.length :=
                by change ((0#64 : BitVec 64) + 2 + BitVec.ofNat 64 1).toNat <
                    nvFidEvalScr0.length
                   decide
              m6_steps; m6_call hFind
              refine ⟨nvFidEvalFCur, 8, ri, FullReprRest nvFidEvalCfg _ ⋆ emp, hrepri,
                by have h3s : nvFidEvalSt0.scratch.scratch_buf[
                      ((0#64 : BitVec 64) + 2 + BitVec.ofNat 64 1).toNat] = 3#32 := rfl
                   rw [h3s]; decide,
                focus_full_repr hmi,
                fun r1 r1_repr m1_ hrl1_ hrepr1_ hr1_le _ hr1_eqv hm1_ => ?_⟩
              have hr1_eq : r1 = 3#32 := by
                change LitEquiv (cnfOfClauses nvFidEvalFCur) 3 r1.toNat at hr1_eqv
                change r1.toNat ≤ 3 at hr1_le
                exact BitVec.eq_of_toNat_eq (litEquiv_eval3_3 hr1_eqv hr1_le)
              subst hr1_eq
              have hm1_un := unfocus_full_repr hm1_
              let st_r1 : FullState := { nvFidEvalSt0 with core := { nvFidEvalSt0.core with
                  repr := r1_repr, tmp := [0#32, 0#32, 0#32, 0#32] } }
              have htmp1 : ((1#32 : BitVec 32).setWidth 64).toNat < st_r1.core.tmp.length :=
                by change ((1#32 : BitVec 32).setWidth 64).toNat <
                    ([0#32, 0#32, 0#32, 0#32] : List (BitVec 32)).length
                   decide
              m6_steps
              exact ih1 (2#32, ()) _ (by decide)
                (Or.inr (Or.inr ⟨rfl, r1_repr, hrl1_.trans hrli, hrepr1_, hm⟩))
            · exfalso; revert hc; decide
          · m6_split_fast
            · exfalso; revert hc; decide
            · m6_split_fast
              · exfalso; revert hc; dsimp only; decide
              · m6_split_fast
                · m6_split_fast
                  · m6_split_fast
                    · m6_steps
                      let invSt : FullState :=
                        { nvFidEvalSt0 with core :=
                          { nvFidEvalSt0.core with repr := ri, tmp := [0#32, 3#32, 0#32, 0#32] } }
                      have htp0 : ((0#32 : BitVec 32).setWidth 64).toNat <
                          invSt.core.tmp.length := by
                        dsimp [invSt, nvFidEvalSt0, nvFidMkState4, nvFidMkCore4]; decide
                      have htp1 : ((1#32 : BitVec 32).setWidth 64).toNat <
                          invSt.core.tmp.length := by
                        dsimp [invSt, nvFidEvalSt0, nvFidMkState4, nvFidMkCore4]; decide
                      have hvl0 : ((0#32 : BitVec 32).setWidth 64).toNat <
                          invSt.core.vals.length := by
                        dsimp [invSt, nvFidEvalSt0, nvFidMkState4, nvFidMkCore4, nvFidEvalVals0]
                        decide
                      have hvl3 : ((3#32 : BitVec 32).setWidth 64).toNat <
                          invSt.core.vals.length := by
                        dsimp [invSt, nvFidEvalSt0, nvFidMkState4, nvFidMkCore4, nvFidEvalVals0]
                        decide
                      refine wp_loop_inv (ts := [i32, i32, i32])
                        (fun (ii, flp, na, ()) m_lp =>
                          (ii = 0#32 ∧ flp = 0#32 ∧ na = 0#32 ∧
                            (FullMem nvFidEvalCfg invSt ⋆ emp) m_lp) ∨
                          (ii = 1#32 ∧ flp = 0#32 ∧ na = 1#32 ∧
                            (FullMem nvFidEvalCfg invSt ⋆ emp) m_lp) ∨
                          (ii = 2#32 ∧ flp = 1#32 ∧ na = 1#32 ∧
                            (FullMem nvFidEvalCfg invSt ⋆ emp) m_lp))
                        (fun (ii, _, _, ()) _ => 2 - ii.toNat)
                        (fun Jl hJl => by
                          m6_let
                          exact hJl (0#32, 0#32, 0#32, ()) mi (Or.inl ⟨rfl, rfl, rfl, hmi⟩))
                        (fun Jl (ii, flp, na, ()) m_lp hlp ihl => ?_)
                      rcases hlp with ⟨rfl, rfl, rfl, hm_lp⟩ | ⟨rfl, rfl, rfl, hm_lp⟩ |
                          ⟨rfl, rfl, rfl, hm_lp⟩
                      · m6_split_fast
                        · m6_steps
                          m6_split_fast
                          · exfalso
                            change (BitVec.signExtend 32 0#8 != BitVec.ofNat 32 0) = true at hc
                            revert hc; decide
                          · m6_steps
                            have htmp_id : invSt.core.tmp.set (BitVec.ofNat 64 0).toNat
                                (invSt.core.tmp[(BitVec.ofNat 64 0).toNat] &&& ~~~1) =
                                invSt.core.tmp := by
                              have h0t : invSt.core.tmp[(BitVec.ofNat 64 0).toNat] = 0#32 := rfl
                              rw [h0t, show (~~~1 : BitVec 32) = ~~~1#32 from rfl, BitVec.zero_and]
                              rfl
                            have hflp0 : (0#32 ^^^
                                invSt.core.tmp[(BitVec.ofNat 64 0).toNat] &&& 1) = 0#32 := by
                              have h0t : invSt.core.tmp[(BitVec.ofNat 64 0).toNat] = 0#32 := rfl
                              rw [h0t, BitVec.zero_and, BitVec.zero_xor]
                            rw [htmp_id] at hm; rw [hflp0]
                            exact ihl (1#32, 0#32, 1#32, ()) _ (by decide)
                              (Or.inr (Or.inl ⟨rfl, rfl, rfl, hm⟩))
                        · exfalso; revert hc; dsimp only; decide
                      · m6_split_fast
                        · m6_steps
                          m6_split_fast
                          · m6_split_fast
                            · m6_steps
                              exact ihl (2#32, 1#32, 1#32, ()) m_lp (by decide)
                                (Or.inr (Or.inr ⟨rfl, rfl, rfl, hm_lp⟩))
                            · exfalso
                              change ((0#32 : BitVec 32).slt (BitVec.signExtend 32 1#8)) =
                                false at hc
                              revert hc; decide
                          · exfalso
                            change (BitVec.signExtend 32 1#8 != BitVec.ofNat 32 0) = false at hc
                            revert hc; decide
                        · exfalso; revert hc; dsimp only; decide
                      · m6_split_fast
                        · exfalso; revert hc; dsimp only; decide
                        · m6_to_group
                          refine wp_join_group (ts := [])
                            (fun () m_s => (FullMem nvFidEvalCfg invSt ⋆ emp) m_s) ?_
                            (fun Js hJs => by
                              m6_split_fast
                              · exfalso; revert hc; dsimp only; decide
                              · m6_steps; exact hJs () m_lp hm_lp)
                          rintro _ ⟨⟩ m_s hm_s; m6_steps
                          refine wp_loop_inv (ts := [i32, i32])
                            (fun (jd, ua, ()) m_d =>
                              (jd = 0#32 ∧ ua = 0#32 ∧
                                (FullMem nvFidEvalCfg invSt ⋆ emp) m_d) ∨
                              (jd = 1#32 ∧ ua = 1#32 ∧
                                (FullMem nvFidEvalCfg invSt ⋆ emp) m_d))
                            (fun (jd, _, ()) _ => 1 - jd.toNat)
                            (fun Jd hJd => by
                              m6_let; exact hJd (0#32, 0#32, ()) m_s (Or.inl ⟨rfl, rfl, hm_s⟩))
                            (fun Jd (jd, ua, ()) m_d hd ihd => ?_)
                          rcases hd with ⟨rfl, rfl, hm_d⟩ | ⟨rfl, rfl, hm_d⟩
                          · m6_split_fast
                            · m6_split_fast
                              · exfalso; revert hc; dsimp only; decide
                              · m6_steps
                                have htmp_id2 : invSt.core.tmp.set (BitVec.ofNat 64 0).toNat
                                    (invSt.core.tmp[(BitVec.ofNat 64 0).toNat]) =
                                    invSt.core.tmp := rfl
                                rw [htmp_id2] at hm
                                exact ihd (1#32, 1#32, ()) _ (by decide)
                                  (Or.inr ⟨rfl, rfl, hm⟩)
                            · exfalso; revert hc; dsimp only; decide
                          · m6_split_fast
                            · exfalso; revert hc; dsimp only; decide
                            · m6_split_fast
                              · m6_to_group
                                refine wp_join_group (ts := [i32, i32])
                                  (fun (io, si, ()) m_b => io = 0#32 ∧ si = 0#32 ∧
                                    (FullMem nvFidEvalCfg invSt ⋆ emp) m_b)
                                  ?_ (fun Jbrk hJbrk => by
                                    m6_steps
                                    refine wp_loop_inv (ts := [i32])
                                      (fun (i3, ()) m_b => i3 = 0#32 ∧
                                        (FullMem nvFidEvalCfg invSt ⋆ emp) m_b)
                                      (fun (i3, ()) _ => 1 - i3.toNat)
                                      (fun Js hJs => by
                                        m6_let
                                        exact hJs (0#32, ()) m_d ⟨rfl, hm_d⟩)
                                      (fun Js xi3 m_b h3 ih3 => ?_)
                                    rcases xi3 with ⟨i3, ⟨⟩⟩
                                    rcases h3 with ⟨rfl, hm_b⟩
                                    m6_split_fast
                                    · m6_steps; m6_split_fast
                                      · m6_steps
                                        exact hJbrk (0#32, 0#32, ()) m_b ⟨rfl, rfl, hm_b⟩
                                      · exfalso
                                        change (0#32 ==
                                            ((0#32 ^^^ 1#32) &&& 4294967294#32)) = false at hc
                                        revert hc; decide
                                    · exfalso; revert hc; dsimp only; decide)
                                rintro _ xsi m_b hmb_
                                rcases xsi with ⟨io, si, ⟨⟩⟩
                                rcases hmb_ with ⟨rfl, rfl, hm_b⟩
                                m6_split_fast
                                · m6_to_group
                                  refine wp_loop_inv (ts := [i32])
                                    (fun (jj, ()) m_j => jj = 0#32 ∧
                                      (FullMem nvFidEvalCfg invSt ⋆ emp) m_j)
                                    (fun _ _ => 0)
                                    (fun Jsh hJsh => by
                                      m6_let; exact hJsh (0#32, ()) m_b ⟨rfl, hm_b⟩)
                                    (fun Jsh xjj m_j hj _ => ?_)
                                  rcases xjj with ⟨jj, ⟨⟩⟩; rcases hj with ⟨rfl, hm_j⟩
                                  m6_split_fast
                                  · exfalso; revert hc; dsimp only; decide
                                  · m6_split_fast
                                    · m6_split_fast
                                      · m6_steps
                                        let stf : FullState := nvFidMkState4 1#64 1#64 0#64 1
                                          nvFidEvalVals0 nvFidEvalTrl0 ri [0#32, 3#32, 0#32, 0#32]
                                          (List.replicate 8 0#32) (List.replicate 8 0#32)
                                          nvFidEvalScr0
                                        have hlen : stf.LengthsOk nvFidEvalCfg :=
                                          nvFidMkState4_lengths (sc := 4) (hsc := nvFidEvalCfg.hscr)
                                            1#64 1#64 0#64 1 nvFidEvalVals0 nvFidEvalTrl0 ri
                                            [0#32, 3#32, 0#32, 0#32] (List.replicate 8 0#32)
                                            (List.replicate 8 0#32) nvFidEvalScr0
                                            (by decide) rfl rfl hrli rfl rfl rfl rfl
                                        rw [sep_emp] at hm
                                        exact ⟨stf, rfl, rfl, hlen, hrepri, nvFidF0_unsat, hm⟩
                                      · exfalso; revert hc; dsimp only; decide
                                    · exfalso; revert hc; dsimp only; decide
                                · exfalso; revert hc; dsimp only; decide
                              · exfalso; revert hc; dsimp only; decide
                    · exfalso; revert hc; dsimp only; decide
                  · exfalso; revert hc; dsimp only; decide
                · exfalso; revert hc; dsimp only; decide

end LeanQbe.T.Examples.Kissat.FullFidelityCong

end
