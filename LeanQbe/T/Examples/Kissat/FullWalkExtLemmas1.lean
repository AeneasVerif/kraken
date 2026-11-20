module

public import LeanQbe.T.Examples.Kissat.Full2
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Logic.C0Agrees
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Walk, Mode, Restart & Extend `Func.wp` Proofs — Part 1 (`Stage 4`)

Defines `FullWalkExtSpecs` (canonical Stage-4 `FullLitMarksClear`, `FullArenaVarsNodup`,
`FullLastLearnedWf`, `FullExtScratchOk`, `FullSparseInv`, `FullWalkEntryOk`, callee specs, and
the 11 `Full2` specs for this shard), scoped tactics (`FullWalkExtTactics`), and proves
`full_restart_due_wp`, `full_extend_push2_wp`, `full_extend_push_cl_wp`, `full_extend_wp`, and
`full_switch_mode_wp`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 0. Canonical Stage-4 specs (`FullWalkExtSpecs`) & invariant preservation helpers -/

namespace FullWalkExtSpecs

def FullLitMarksClear (c : FullCfg) (s : FullState) : Prop :=
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
  (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)

def FullArenaVarsNodup (s : FullState) : Prop :=
  ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false →
    ((fullArenaClauseLits s r).map (· / 2)).Nodup

def FullLastLearnedWf (s : FullState) : Prop :=
  ∀ i < 8, let cr := s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32
    cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ fullArenaClauseRefs s

def FullExtScratchOk (c : FullCfg) (s : FullState) : Prop :=
  FullLastLearnedWf s ∧ s.scratch.extend_len ≤ c.extend_cap

def FullSparseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

def FullWalkEntryOk (s : FullState) (idx : Nat) : Prop :=
  let w0 := s.scratch.scratch_buf[2 * idx]?.getD 0#32
  if (w0 &&& 0x80000000#32) ≠ 0#32 then
    (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars ∧
    (s.scratch.scratch_buf[2 * idx + 1]?.getD 0#32).toNat < 2 * s.core.cur_vars
  else
    w0.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s w0.toNat = false

def FullWalkEntriesOk (s : FullState) (n : Nat) : Prop :=
  ∀ idx < n, FullWalkEntryOk s idx

def FullExtScratchPres (s s' : FullState) : Prop :=
  s'.scratch.last_learned = s.scratch.last_learned ∧
  s'.scratch.extend_len = s.scratch.extend_len

def FullProbeScratchPres (s s' : FullState) : Prop :=
  FullExtScratchPres s s' ∧
  s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
  s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
  s'.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
  s'.scratch.ant_sz = s.scratch.ant_sz ∧
  s'.scratch.res_sz = s.scratch.res_sz ∧
  s'.scratch.sim_sig = s.scratch.sim_sig

def FullAnaMarksCov (c : FullCfg) (s : FullState) : Prop :=
  s.core.min_clr_len ≤ s.core.cur_vars ∧
  ((s.scratch.work_stk1.take s.core.min_clr_len).map BitVec.toNat).Nodup ∧
  (∀ k < s.core.min_clr_len,
    (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars ∧
    s.core.mrk[(s.scratch.work_stk1[k]?.getD 0#32).toNat]?.getD 0#8 ≠ 0#8) ∧
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
    ∃ i < s.core.min_clr_len, (s.scratch.work_stk1[i]?.getD 0#32).toNat = v)

/-! ### Internal callee `Spec` contracts -/

def fullRngNextSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => s'.scratch = { s.scratch with rng_state := s'.scratch.rng_state })

def fullArenaNextSpec : Spec [i64, i32] [i32] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    Q (BitVec.ofNat 32 (fullArenaNextOff s.core.arena s.core.arena_len cref.toNat), ()) m

def fullIlog10Spec : Spec [i64] [i64] := fun (_x, ()) m Q _ =>
  ∀ r : BitVec 64, 1 ≤ r.toNat → r.toNat ≤ 19 → Q (r, ()) m

def fullHeapDownSpec : Spec [i64, i32] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _v, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => s'.scratch.heap_len = s.scratch.heap_len ∧ FullProbeScratchPres s s')

def fullHeapPopSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ (r, ()) s s' =>
      (r = 0xFFFFFFFF#64 ∨ r.toNat < s.core.cur_vars) ∧
      (0 < s.scratch.heap_len ∧ s.scratch.heap_len ≤ s.core.cur_vars →
        s'.scratch.heap_len = s.scratch.heap_len - 1) ∧
      FullProbeScratchPres s s')

def fullBumpVarSpec : Spec [i64, i32] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _v, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullProbeScratchPres s s')

def fullQueueMtfSpec : Spec [i64, i32] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _v, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullProbeScratchPres s s')

def fullBumpDecaySpec : Spec [i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullProbeScratchPres s s')

/-! ### Owned `Full2` function `Spec` contracts (`11` fns) -/

def fullBumpAnalyzedSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullAnaMarksCov c s ∧ (FullMem c s ⋆ R) m ∧
    ∀ mrk' mcl' sc' m',
      let s' : FullState :=
        { s with core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
      s'.LengthsOk c → FullAnaMarksCov c s' → FullExtScratchPres s s' →
      sc'.work_stk2 = s.scratch.work_stk2 →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullNextDecVarSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ (r, ()) s s' =>
      FullExtScratchPres s s' ∧
      (r = 0xFFFFFFFFFFFFFFFF#64 ∨
        (r.toNat < s.core.cur_vars ∧ s.core.vals[2 * r.toNat]?.getD 0#8 = 0#8)))

def fullWalkCollectSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) s => h = c.hdr ∧ ∃ F0, FullCoreInv c F0 s)
    (fun c _ (r, ()) s s' =>
      FullExtScratchPres s s' ∧ r.toNat ≤ c.scratch_cap / 2 ∧ FullWalkEntriesOk s' r.toNat)

def fullWalkClSatSpec : Spec [i64, i64, i64] [.bool] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, scr, idx, ()) s =>
      h = c.hdr ∧ scr = c.pScratchBuf ∧ (∃ F0, FullCoreInv c F0 s) ∧
      idx.toNat < c.scratch_cap / 2 ∧ FullWalkEntryOk s idx.toNat)
    (fun _ _ _ s s' => s' = s)

def fullWalkPickLitSpec : Spec [i64, i64, i64] [i32] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, scr, idx, ()) s =>
      h = c.hdr ∧ scr = c.pScratchBuf ∧ (∃ F0, FullCoreInv c F0 s) ∧
      idx.toNat < c.scratch_cap / 2 ∧ FullWalkEntryOk s idx.toNat)
    (fun _ _ (r, ()) s s' =>
      FullExtScratchPres s s' ∧ s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
      (r = 0xFFFFFFFF#32 ∨ r.toNat < 2 * s.core.cur_vars))

def fullWalkSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ fuel' sc' m',
      let s' : FullState :=
        { s with core := { s.core with fuel := fuel' }, scratch := sc' }
      s'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat → FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullSwitchModeSpec : Spec [i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullProbeScratchPres s s')

def fullRestartDueSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ (r, ()) s s' => (r = 0#64 ∨ r = 1#64) ∧ FullExtScratchPres s s')

def fullExtendPush2Spec : Spec [i64, i32, i32] [.bool] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _blk, _ot, ()) s => h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap)
    (fun c _ _ s s' =>
      s'.scratch.last_learned = s.scratch.last_learned ∧ s'.scratch.extend_len ≤ c.extend_cap ∧
      s'.scratch.scratch_buf = s.scratch.scratch_buf)

def fullExtendPushClSpec : Spec [i64, i32, i32] [.bool] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _blk, _cref, ()) s => h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap)
    (fun c _ _ s s' =>
      s'.scratch.last_learned = s.scratch.last_learned ∧ s'.scratch.extend_len ≤ c.extend_cap ∧
      s'.scratch.scratch_buf = s.scratch.scratch_buf)

def fullExtendSpec : Spec [i64] [] :=
  SafetySlice.spec fullExtendSlice
    (fun c (h, ()) s => h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap)
    (fun _ _ _ _ _ => True)

end FullWalkExtSpecs

open FullWalkExtSpecs

/-! ### Invariant transport lemmas across `FullWalkExt` updates -/

theorem FullCoreInv.walkExt_with_fuel_scratch {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullCoreInv c F0 s) {fuel' : BitVec 64} {scratch' : FullScratch}
    (hok : scratch'.LengthsOk c) :
    FullCoreInv c F0 { core := { s.core with fuel := fuel' }, scratch := scratch' } := by
  obtain ⟨F_cur, hw⟩ := h.witness
  refine ⟨⟨{ h.lengths.core_ok with vals_len := h.lengths.core_ok.vals_len }, hok⟩, F_cur,
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }⟩

theorem FullCoreInv.walkExt_with_mrk_mcl_scratch {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullCoreInv c F0 s) {mrk' : List (BitVec 8)} {mcl' : Nat} {scratch' : FullScratch}
    (hmrk : mrk'.length = c.max_vars) (hmcl : mcl' ≤ c.max_vars) (hok : scratch'.LengthsOk c) :
    FullCoreInv c F0
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := scratch' } := by
  obtain ⟨F_cur, hw⟩ := h.witness
  refine ⟨⟨{ h.lengths.core_ok with mrk_len := hmrk, min_clr_len_le := hmcl }, hok⟩, F_cur,
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }⟩

theorem FullSparseInv.walkExt_with_scratch {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullSparseInv c F0 s) (hlen' : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hel : s'.scratch.extend_len = s.scratch.extend_len) : FullSparseInv c F0 s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  refine ⟨h.1.with_scratch hlen' hcore, ?_, ?_, ?_, ?_⟩
  · unfold FullLitMarksClear; rw [heq]; exact h.2.1
  · dsimp only [FullArenaVarsNodup, fullArenaClauseRefs, fullArenaClauseRefsCore,
      fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdr, fullArenaHdrCore,
      fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSize, fullArenaClauseSizeCore]
    rw [heq]; exact h.2.2.1
  · refine ⟨fun i hi => ?_, hel ▸ h.2.2.2.1.2⟩
    have := h.2.2.2.1.1 i hi; dsimp only [fullArenaClauseRefs, fullArenaClauseRefsCore] at this ⊢
    rw [hll, heq]; exact this
  · rw [heq]; exact h.2.2.2.2

theorem FullSparseInv.walkExt_with_fuel_scratch {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {fuel' : BitVec 64} {scratch' : FullScratch}
    (hok : scratch'.LengthsOk c) (hll : scratch'.last_learned = s.scratch.last_learned)
    (hel : scratch'.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 { core := { s.core with fuel := fuel' }, scratch := scratch' } :=
  ⟨h.1.walkExt_with_fuel_scratch hok, h.2.1, h.2.2.1,
    ⟨fun i hi => by have := h.2.2.2.1.1 i hi; dsimp only at this ⊢; rw [hll]; exact this,
     hel ▸ h.2.2.2.1.2⟩,
    h.2.2.2.2⟩

/-! ## 1. Scoped automation & `BitVec` helper lemmas (`FullWalkExtTactics`) -/

namespace FullWalkExtHelpers

theorem bv64_shl1_or_1_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 63) :
    ((v <<< (1 : Nat)) ||| 1#64).toNat = 2 * v.toNat + 1 := by
  have hs : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
    rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_or, hs, h1]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ i =>
    simp [Nat.testBit_succ, show (2 * v.toNat + 1) / 2 = v.toNat by omega,
      show (2 * v.toNat) / 2 = v.toNat by omega]

theorem bv32_xor1_lt {x : BitVec 32} {n : Nat} (hx : x.toNat / 2 < n) :
    (x ^^^ 1#32).toNat < 2 * n := by
  have h1 : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := rfl
  rw [h1]
  exact litNeg_lt_two_mul (by omega : x.toNat < 2 * n)

theorem bv32_and_mask_toNat {w : BitVec 32} :
    (w &&& 0x7FFFFFFF#32).toNat = w.toNat % 2 ^ 31 := by
  rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl]
  exact Nat.and_two_pow_sub_one_eq_mod w.toNat 31

theorem bv32_or_ext_blk_flag {x : BitVec 32} :
    ((x ||| 0x80000000#32) &&& 0x80000000#32) ≠ 0#32 := by
  intro h
  have h31 := congrArg (·[31]) h
  revert h31; simp [show (0x80000000#32 : BitVec 32)[31] = true from rfl]

theorem bv32_and_ext_mask_lt {x : BitVec 32} :
    (x &&& 0x7FFFFFFF#32).toNat < 2 ^ 31 := by
  rw [bv32_and_mask_toNat]; exact Nat.mod_lt _ (by decide)

theorem bv64_eq_of_not_pos {x : BitVec 64} (h : ¬ (0 < x.toNat)) : x = 0#64 :=
  BitVec.eq_of_toNat_eq (by simp; omega)

theorem bv64_ofNat_sub1 {n : Nat} (hn : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n - 1).toNat = n - 1 := by
  have h1 : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  bv_omega

theorem bv64_ofNat_add1 {n : Nat} (hlt : n + 1 < 2 ^ 64) :
    (BitVec.ofNat 64 n + 1).toNat = n + 1 := by
  have h1 : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  bv_omega

theorem FullMem_with_heap_len_mod (c : FullCfg) (s : FullState) :
    FullMem c { s with scratch := { s.scratch with heap_len := s.scratch.heap_len % 2 ^ 64 } } =
      FullMem c s := by
  have hhl : BitVec.ofNat 64 (s.scratch.heap_len % 2 ^ 64) =
      BitVec.ofNat 64 s.scratch.heap_len := BitVec.eq_of_toNat_eq (by simp)
  unfold FullMem hdrTailWords hdrTailWords0 hdrTailWords1 hdrTailWords2 hdrTailWords3
    FullScratchArrays FullScrByteArrs FullScrU32A FullScrWksArrs FullScrMetaArrs FullScrDynArrs
  dsimp only; rw [hhl]

theorem list_take_set_succ {α : Type} {xs : List α} {n : Nat} {v : α} (hn : n < xs.length) :
    (xs.set n v).take (n + 1) = xs.take n ++ [v] := by
  refine List.ext_getElem (by simp; omega) fun i h1 _ => ?_
  rw [List.getElem_take, List.getElem_set]
  split
  · rename_i heq; subst heq
    rw [List.getElem_append_right (by simp; omega)]
    simp [Nat.min_eq_left (Nat.le_of_lt hn)]
  · have hlt : i < n := by simp at h1; omega
    rw [List.getElem_append_left (by simp; omega), List.getElem_take]

theorem nodup_map_take_append {xs : List (BitVec 32)} {n : Nat} {v : BitVec 32}
    (hn : n < xs.length) (hnd : ((xs.take n).map BitVec.toNat).Nodup)
    (hnot : ∀ k < n, (xs[k]?.getD 0#32).toNat ≠ v.toNat) :
    (((xs.set n v).take (n + 1)).map BitVec.toNat).Nodup := by
  rw [list_take_set_succ hn, List.map_append, List.map_singleton, List.nodup_append]
  refine ⟨hnd, by simp, fun a ha b hb => ?_⟩
  simp only [List.mem_singleton] at hb; subst hb
  rw [List.mem_map] at ha; obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨k, hk, hxk⟩ := List.mem_iff_getElem.mp hx
  simp only [List.length_take, Nat.lt_min] at hk
  rw [List.getElem_take] at hxk
  have hne := hnot k hk.1
  rwa [List.getElem?_eq_getElem hk.2, Option.getD_some, hxk] at hne

theorem nodup_map_take_sub1 {xs : List (BitVec 32)} {n : Nat}
    (hnd : ((xs.take n).map BitVec.toNat).Nodup) :
    ((xs.take (n - 1)).map BitVec.toNat).Nodup := by
  have hsub : xs.take (n - 1) = (xs.take n).take (n - 1) := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  rw [hsub, List.map_take]; exact hnd.sublist (List.take_sublist _ _)

theorem nodup_map_take_ne {xs : List (BitVec 32)} {n k : Nat}
    (hn : n ≤ xs.length) (hnd : ((xs.take n).map BitVec.toNat).Nodup) (hk : k < n - 1) :
    (xs[k]?.getD 0#32).toNat ≠ (xs[n - 1]?.getD 0#32).toNat := by
  have hp := List.pairwise_iff_getElem.mp hnd
  have hlen : ((xs.take n).map BitVec.toNat).length = n := by simp; omega
  have hne := hp k (n - 1) (by omega) (by omega) (by omega)
  simp only [List.getElem_map, List.getElem_take] at hne
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
  exact hne

theorem sext32_eq_zero {x : BitVec 8} (h : BitVec.signExtend 32 x = 0#32) : x = 0#8 := by
  ext i hi
  have h1 := congrArg (·[i]) h
  simpa [BitVec.getElem_signExtend, hi, show i < 32 by omega] using h1

theorem wp_let_add64_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a b : Arg Val i64} {k : Tup Val [i64] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i64, i64], code := .add i64, args := (a, b, ()) } k) m =
      wp Γ Q X (k (a.val + b.val, ())) m := by
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, lift2] using
    @wp_let_add_eq Γ rs Q X m i64 (a, b, ()) k

theorem wp_let_add32_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a b : Arg Val i32} {k : Tup Val [i32] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i32, i32], code := .add i32, args := (a, b, ()) } k) m =
      wp Γ Q X (k (a.val + b.val, ())) m := by
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, lift2] using
    @wp_let_add_eq Γ rs Q X m i32 (a, b, ()) k

theorem wp_let_mul64_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a b : Arg Val i64} {k : Tup Val [i64] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i64, i64], code := .mul i64, args := (a, b, ()) } k) m =
      wp Γ Q X (k (a.val * b.val, ())) m := by
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, lift2] using
    @wp_let_mul_eq Γ rs Q X m i64 (a, b, ()) k

theorem wp_let_shl64_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a b : Arg Val i64} {k : Tup Val [i64] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i64, i64], code := .shl i64, args := (a, b, ()) } k) m =
      wp Γ Q X (k (a.val <<< (b.val.toNat % 64), ())) m := by
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, lift2] using
    @wp_let_shl_eq Γ rs Q X m i64 (a, b, ()) k

theorem wp_let_lshr32_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a b : Arg Val i32} {k : Tup Val [i32] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i32, i32], code := .lshr i32, args := (a, b, ()) } k) m =
      wp Γ Q X (k (a.val >>> (b.val.toNat % 32), ())) m := by
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, lift2] using
    @wp_let_lshr_eq Γ rs Q X m i32 (a, b, ()) k

theorem wp_let_and32_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a b : Arg Val i32} {k : Tup Val [i32] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i32, i32], code := .and i32, args := (a, b, ()) } k) m =
      wp Γ Q X (k (a.val &&& b.val, ())) m := by
  simpa only [lift2] using @wp_let_and_eq Γ rs Q X m i32 (a, b, ()) k

theorem wp_let_zext32_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a : Arg Val (.bits 32)} {k : Tup Val [.bits 64] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i32], code := .zext 32 64, args := (a, ()) } k) m =
      wp Γ Q X (k (a.val.setWidth 64, ())) m := by
  simpa using @wp_let_zext_eq Γ rs Q X m 32 64 (a, ()) k

theorem wp_let_sext32_64_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a : Arg Val (.bits 32)} {k : Tup Val [.bits 64] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i32], code := .sext 32 64, args := (a, ()) } k) m =
      wp Γ Q X (k (a.val.signExtend 64, ())) m := by
  simpa using @wp_let_sext_eq Γ rs Q X m 32 64 (a, ()) k

theorem wp_let_sext8_32_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a : Arg Val (.bits 8)} {k : Tup Val [.bits 32] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i8], code := .sext 8 32, args := (a, ()) } k) m =
      wp Γ Q X (k (a.val.signExtend 32, ())) m := by
  simpa using @wp_let_sext_eq Γ rs Q X m 8 32 (a, ()) k

theorem wp_let_trunc32_8_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a : Arg Val (.bits 32)} {k : Tup Val [.bits 8] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i32], code := .trunc 32 8, args := (a, ()) } k) m =
      wp Γ Q X (k (a.val.setWidth 8, ())) m := by
  simpa using @wp_let_trunc_eq Γ rs Q X m 32 8 (a, ()) k

theorem wp_let_urem64_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a b : Arg Val i64} (hb : b.val ≠ 0)
    {k : Tup Val [i64] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i64, i64], code := .urem 64, args := (a, b, ()) } k) m =
      wp Γ Q X (k (a.val % b.val, ())) m := by
  exact (@wp_let_urem_eq Γ rs Q X m 64 (a, b, ()) k).trans
    (propext ⟨fun h1 => h1.2, fun h2 => ⟨hb, h2⟩⟩)

theorem wp_let_eq32_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {hm : Ty.bool = Ty.mask i32} {a b : Arg Val i32}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    wp Γ Q X
        (.let_ { sig := [i32, i32], code := .cmp .eq i32 .bool hm, args := (a, b, ()) } k) m =
      wp Γ Q X (k (a.val == b.val, ())) m := by
  have hc := @wp_let_cmp_eq Γ rs Q X m .eq i32 .bool hm (a, b, ()) k
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, liftCmp,
    evalBits_eq_beq, cast_eq] using hc

theorem wp_let_ne32_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {hm : Ty.bool = Ty.mask i32} {a b : Arg Val i32}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    wp Γ Q X
        (.let_ { sig := [i32, i32], code := .cmp .ne i32 .bool hm, args := (a, b, ()) } k) m =
      wp Γ Q X (k (a.val != b.val, ())) m := by
  have hc := @wp_let_cmp_eq Γ rs Q X m .ne i32 .bool hm (a, b, ()) k
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, liftCmp,
    evalBits_ne_bne, cast_eq] using hc

theorem wp_let_eq64_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {hm : Ty.bool = Ty.mask i64} {a b : Arg Val i64}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    wp Γ Q X
        (.let_ { sig := [i64, i64], code := .cmp .eq i64 .bool hm, args := (a, b, ()) } k) m =
      wp Γ Q X (k (a.val == b.val, ())) m := by
  have hc := @wp_let_cmp_eq Γ rs Q X m .eq i64 .bool hm (a, b, ()) k
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, liftCmp,
    evalBits_eq_beq, cast_eq] using hc

theorem wp_let_ugt64_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {hm : Ty.bool = Ty.mask i64} {a b : Arg Val i64}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    wp Γ Q X
        (.let_ { sig := [i64, i64], code := .cmp .ugt i64 .bool hm, args := (a, b, ()) } k) m =
      wp Γ Q X (k (BitVec.ult b.val a.val, ())) m := by
  have hc := @wp_let_cmp_eq Γ rs Q X m .ugt i64 .bool hm (a, b, ()) k
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, liftCmp,
    evalBits_ugt_eq, cast_eq] using hc

theorem wp_let_ule64_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {hm : Ty.bool = Ty.mask i64} {a b : Arg Val i64}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    wp Γ Q X
        (.let_ { sig := [i64, i64], code := .cmp .ule i64 .bool hm, args := (a, b, ()) } k) m =
      wp Γ Q X (k (BitVec.ule a.val b.val, ())) m := by
  have hc := @wp_let_cmp_eq Γ rs Q X m .ule i64 .bool hm (a, b, ()) k
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, liftCmp,
    evalBits_ule_eq, cast_eq] using hc

theorem wp_let_uge64_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {hm : Ty.bool = Ty.mask i64} {a b : Arg Val i64}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    wp Γ Q X
        (.let_ { sig := [i64, i64], code := .cmp .uge i64 .bool hm, args := (a, b, ()) } k) m =
      wp Γ Q X (k (BitVec.ule b.val a.val, ())) m := by
  have hc := @wp_let_cmp_eq Γ rs Q X m .uge i64 .bool hm (a, b, ()) k
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, liftCmp,
    evalBits_uge_eq, cast_eq] using hc

theorem wp_let_ult64_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {hm : Ty.bool = Ty.mask i64} {a b : Arg Val i64}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult i64 .bool hm) (a, b, ())) k) m =
      wp Γ Q X (k (BitVec.ult a.val b.val, ())) m := by
  have hc := @wp_let_cmp_eq Γ rs Q X m .ult i64 .bool hm (a, b, ()) k
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, liftCmp,
    evalBits_ult_eq, cast_eq] using hc

theorem wp_let_zext8_32_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a : Arg Val (.bits 8)} {k : Tup Val [.bits 32] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i8], code := .zext 8 32, args := (a, ()) } k) m =
      wp Γ Q X (k (a.val.setWidth 32, ())) m := by
  simpa using @wp_let_zext_eq Γ rs Q X m 8 32 (a, ()) k

theorem wp_let_ugt32_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {hm : Ty.bool = Ty.mask i32} {a b : Arg Val i32}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ugt i32 .bool hm) (a, b, ())) k) m =
      wp Γ Q X (k (BitVec.ult b.val a.val, ())) m := by
  have hc := @wp_let_cmp_eq Γ rs Q X m .ugt i32 .bool hm (a, b, ()) k
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, liftCmp,
    evalBits_ugt_eq, cast_eq] using hc

theorem wp_let_ult32_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {hm : Ty.bool = Ty.mask i32} {a b : Arg Val i32}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult i32 .bool hm) (a, b, ())) k) m =
      wp Γ Q X (k (BitVec.ult a.val b.val, ())) m := by
  have hc := @wp_let_cmp_eq Γ rs Q X m .ult i32 .bool hm (a, b, ()) k
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, liftCmp,
    evalBits_ult_eq, cast_eq] using hc

theorem wp_let_sub64_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a b : Arg Val i64} {k : Tup Val [i64] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i64, i64], code := .sub i64, args := (a, b, ()) } k) m =
      wp Γ Q X (k (a.val - b.val, ())) m := by
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, lift2] using
    @wp_let_sub_eq Γ rs Q X m i64 (a, b, ()) k

theorem walk_entry_bin_bounds {s : FullState} {idx : Nat}
    (hok : FullWalkEntryOk s idx)
    (hbin : (s.scratch.scratch_buf[2 * idx]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32) :
    ((s.scratch.scratch_buf[2 * idx]?.getD 0#32) &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars ∧
    (s.scratch.scratch_buf[2 * idx + 1]?.getD 0#32).toNat < 2 * s.core.cur_vars := by
  unfold FullWalkEntryOk at hok; simp only [hbin, ne_eq, not_false_eq_true, ↓reduceIte] at hok
  exact hok

end FullWalkExtHelpers

open FullWalkExtHelpers

namespace FullWalkExtTactics

attribute [scoped bv_c0] List.length_set

open Lean Elab Tactic in
/-- Step all goals like `c0_steps`, stopping at `Expr.group` instead of inlining join points. -/
scoped elab "c0_to_group" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let ty := (← Lean.instantiateMVars (← g.getType)).headBeta
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push g
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out.push g
    setGoals out.toList
  go 500

open Lean Elab Tactic in
/-- Step all goals like `c0_steps`, stopping at `Expr.jnz`. -/
scoped elab "c0_to_jnz" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let ty := (← Lean.instantiateMVars (← g.getType)).headBeta
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
        out := out.push g
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out.push g
    setGoals out.toList
  go 500

open Lean Elab Tactic in
/-- Step straight-line ops on the main goal until the next `Expr.jnz`, then split it once. -/
scoped elab "c0_split" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let ty := (← Lean.instantiateMVars (← (← getMainGoal).getType)).headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← LeanQbe.T.C0Step.stepOnce; return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  go 100

end FullWalkExtTactics

open scoped FullArenaTactics
open scoped FullWalkExtTactics

/-! ## 2. `full_restart_due`, `full_extend_push2`, `full_extend_push_cl`,
`full_extend`, `full_switch_mode` -/

private theorem bv64_shr8_ne_zero {x : BitVec 64} (hx : 256 < x.toNat) :
    x >>> (8 : Nat) ≠ (0 : BitVec 64) := by
  intro h
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (0 : BitVec 64).toNat = 0 from rfl] at h1
  change x.toNat / 256 = 0 at h1
  omega

private theorem bv64_256_toNat : BitVec.toNat (256 : BitVec 64) = 256 := rfl

private theorem wp_let_add64_s {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a b : Arg Val i64} {k : Tup Val [i64] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i64, i64], code := .add i64, args := (a, b, ()) } k) m =
      wp Γ Q X (k (a.val + b.val, ())) m := by
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, lift2] using
    @wp_let_add_eq Γ rs Q X m i64 (a, b, ()) k

private theorem wp_let_mul64_s {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a b : Arg Val i64} {k : Tup Val [i64] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i64, i64], code := .mul i64, args := (a, b, ()) } k) m =
      wp Γ Q X (k (a.val * b.val, ())) m := by
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, lift2] using
    @wp_let_mul_eq Γ rs Q X m i64 (a, b, ()) k

private theorem wp_let_ugt64_s {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {hm : Ty.bool = Ty.mask i64} {a b : Arg Val i64}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    wp Γ Q X
        (.let_ { sig := [i64, i64], code := .cmp .ugt i64 .bool hm, args := (a, b, ()) } k) m =
      wp Γ Q X (k (BitVec.ult b.val a.val, ())) m := by
  have hc := @wp_let_cmp_eq Γ rs Q X m .ugt i64 .bool hm (a, b, ()) k
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, liftCmp,
    evalBits_ugt_eq, cast_eq] using hc

private theorem scratch_lengths_with_restart_limit {c : FullCfg} {sc : FullScratch}
    (h : sc.LengthsOk c) (v : BitVec 64) :
    ({ sc with restart_limit := v } : FullScratch).LengthsOk c :=
  ⟨h.walk_vals_len, h.phases_len, h.phases_target_len, h.phases_best_len, h.walk_best_len,
    h.heap_len_arr, h.pos_len, h.shrink_stk_len, h.q_prev_len, h.q_next_len, h.q_stamp_len,
    h.wsort_len, h.work_stk1_len, h.work_stk2_len, h.tarjan_mark_len, h.tarjan_reach_len,
    h.score_len, h.sim_sig_len, h.glue_used_len, h.last_learned_len, h.delayed_len_arr,
    h.red_refs_len, h.extend_stk_len, h.scratch_buf_len⟩

private theorem scratch_lengths_with_ext {c : FullCfg} {sc : FullScratch}
    (h : sc.LengthsOk c) {el : Nat} {es : List (BitVec 32)} (hes : es.length = c.extend_cap) :
    ({ sc with extend_len := el, extend_stk := es } : FullScratch).LengthsOk c :=
  ⟨h.walk_vals_len, h.phases_len, h.phases_target_len, h.phases_best_len, h.walk_best_len,
    h.heap_len_arr, h.pos_len, h.shrink_stk_len, h.q_prev_len, h.q_next_len, h.q_stamp_len,
    h.wsort_len, h.work_stk1_len, h.work_stk2_len, h.tarjan_mark_len, h.tarjan_reach_len,
    h.score_len, h.sim_sig_len, h.glue_used_len, h.last_learned_len, h.delayed_len_arr,
    h.red_refs_len, hes, h.scratch_buf_len⟩

private theorem fullState_lengths_with_restart_limit {c : FullCfg} {s : FullState}
    (h : s.LengthsOk c) (v : BitVec 64) :
    ({ s with scratch := { s.scratch with restart_limit := v } } : FullState).LengthsOk c :=
  ⟨h.core_ok, scratch_lengths_with_restart_limit h.scratch_ok v⟩

private theorem fullState_lengths_with_ext {c : FullCfg} {s : FullState}
    (h : s.LengthsOk c) {el : Nat} {es : List (BitVec 32)} (hes : es.length = c.extend_cap) :
    ({ s with scratch := { s.scratch with extend_len := el, extend_stk := es } } :
      FullState).LengthsOk c :=
  ⟨h.core_ok, scratch_lengths_with_ext h.scratch_ok hes⟩

theorem full_restart_due_wp (Γ : Env) :
    ∀ a m Q X, fullRestartDueSpec a m Q X → Func.wp Γ full_restart_due_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hlen hm hQ
  c0_step; c0_split
  · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm
  · c0_split
    · c0_split
      · c0_steps
        exact hQ (1#64, ()) { s with scratch := { s.scratch with rel_trigger := 0#64 } } _
          rfl ⟨hlen.core_ok,
            { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len }⟩
          ⟨Or.inr rfl, rfl, rfl⟩ hm
      · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm
    · c0_split
      · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm
      · c0_to_jnz
        refine wp_jnz_of (fun _ => ?_) (fun hfd_gt => ?_)
        · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm
        · c0_to_jnz
          refine wp_jnz_of (fun _ => ?_) (fun hsd_gt => ?_)
          · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm
          · simp only [Arg.val_var, BitVec.ule, decide_eq_false_iff_not,
              bv64_256_toNat] at hfd_gt hsd_gt
            have hfd : 256 < ((1 : BitVec 64) <<< 24 - s.scratch.ema_fast_exp).toNat :=
              Nat.lt_of_not_le hfd_gt
            have hsd : 256 < ((1 : BitVec 64) <<< 24 - s.scratch.ema_slow_exp).toNat :=
              Nat.lt_of_not_le hsd_gt
            have hfd_nz := bv64_shr8_ne_zero hfd
            have hsd_nz := bv64_shr8_ne_zero hsd
            clear hfd_gt hsd_gt
            rw [wp_let_add64_s]; c0_step
            refine wp_udiv_of (by simpa only [Arg.val_var] using hfd_nz) ?_
            rw [wp_let_add64_s]; c0_step
            refine wp_udiv_of (by simpa only [Arg.val_var] using hsd_nz) ?_
            rw [wp_let_mul64_s, wp_let_mul64_s, wp_let_ugt64_s]
            refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
            · c0_steps
              exact hQ (1#64, ())
                { s with scratch :=
                  { s.scratch with restart_limit := s.scratch.conflicts + 1 } } _
                rfl (fullState_lengths_with_restart_limit hlen _) ⟨Or.inr rfl, rfl, rfl⟩ hm
            · c0_steps; exact hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, rfl, rfl⟩ hm

theorem full_extend_push2_wp (Γ : Env) :
    ∀ a m Q X, fullExtendPush2Spec a m Q X → Func.wp Γ full_extend_push2_body a m Q X := by
  rintro ⟨h, blk_lit, other, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hel⟩, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hlen hm hQ
  obtain hcap : c.extend_cap < dimacsBound := c.hext
  unfold dimacsBound at hcap
  obtain hesl := hlen.scratch_ok.extend_stk_len
  c0_steps
  · exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl⟩ hm
  · have hfit : s.scratch.extend_len + 2 ≤ c.extend_cap := by bv_omega
    have hi0 : (BitVec.ofNat 64 s.scratch.extend_len).toNat < s.scratch.extend_stk.length := by
      rw [hesl]; bv_omega
    have hi1 : (BitVec.ofNat 64 s.scratch.extend_len + 1).toNat <
        ((s.scratch.extend_stk.set (BitVec.ofNat 64 s.scratch.extend_len).toNat
          (blk_lit ||| 0x80000000#32))).length := by
      rw [List.length_set, hesl]; bv_omega
    have hadd2 : (BitVec.ofNat 64 s.scratch.extend_len + 2).toNat =
        s.scratch.extend_len + 2 := by bv_omega
    have hel' : (BitVec.ofNat 64 s.scratch.extend_len + 2).toNat ≤ c.extend_cap := hadd2 ▸ hfit
    c0_steps
    let s' : FullState :=
      { s with scratch := { s.scratch with
        extend_stk := (s.scratch.extend_stk.set (BitVec.ofNat 64 s.scratch.extend_len).toNat
          (blk_lit ||| 0x80000000#32)).set (BitVec.ofNat 64 s.scratch.extend_len + 1).toNat
          (other &&& 0x7FFFFFFF#32),
        extend_len := (BitVec.ofNat 64 s.scratch.extend_len + 2).toNat } }
    exact hQ (true, ()) s' _ rfl
      (hlen.with_scratch { hlen.scratch_ok with extend_stk_len := by simp [hesl] })
      ⟨rfl, hel', rfl⟩ hm

theorem full_extend_push_cl_wp (Γ : Env) :
    ∀ a m Q X, fullExtendPushClSpec a m Q X → Func.wp Γ full_extend_push_cl_body a m Q X := by
  rintro ⟨h, blk_lit, cref, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hel⟩, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hlen hm hQ
  obtain haca : c.arena_cap < 2 * dimacsBound := c.harena
  obtain heca : c.extend_cap < dimacsBound := c.hext
  unfold dimacsBound at haca heca
  obtain harl := hlen.core_ok.arena_len_arr
  obtain hale := hlen.core_ok.arena_len_le
  obtain hesl := hlen.scratch_ok.extend_stk_len
  c0_steps
  · exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl⟩ hm
  · exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl⟩ hm
  · exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl⟩ hm
  · rename_i h_ar2 h_ar3
    have hcr3 : cref.toNat + 3 ≤ s.core.arena_len := by bv_omega
    have hcr2_eq : (cref.setWidth 64 + 2).toNat = cref.toNat + 2 := by bv_omega
    have hcr2_lt : (cref.setWidth 64 + 2).toNat < s.core.arena.length := by
      rw [hcr2_eq, harl]; omega
    let sz := (s.core.arena[cref.toNat + 2]'(by omega)).toNat
    have hsz32 : sz < 2 ^ 32 := (s.core.arena[cref.toNat + 2]'(by omega)).isLt
    have hc3sz : cref.toNat + 3 + sz ≤ s.core.arena_len := by
      simp only [show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
        show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
        Nat.mod_eq_of_lt (by omega : cref.toNat + 2 < 2 ^ 64)] at h_ar3
      dsimp only [sz]; bv_omega
    have hext1sz : s.scratch.extend_len + 1 + sz ≤ c.extend_cap := by
      simp only [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
        show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
        Nat.mod_eq_of_lt (by omega : cref.toNat + 2 < 2 ^ 64)] at hc
      dsimp only [sz]; bv_omega
    clear hc h_ar3
    have hp0_lt : (BitVec.ofNat 64 s.scratch.extend_len).toNat <
        s.scratch.extend_stk.length := by rw [hesl]; bv_omega
    c0_to_group
    refine wp_loop_inv
      (fun ((p : BitVec 64), (i : BitVec 32), ()) m1 =>
        i.toNat ≤ sz ∧
        p.toNat ≤ s.scratch.extend_len + 1 + i.toNat ∧
        ∃ ext1 : List (BitVec 32), ext1.length = c.extend_cap ∧
          (FullMem c { s with scratch := { s.scratch with extend_stk := ext1 } } ⋆ R) m1)
      (fun ((_ : BitVec 64), (i : BitVec 32), ()) _ => sz - i.toNat) (fun J hLoop => ?_)
      (fun J ((p : BitVec 64), (i : BitVec 32), ()) m1 ⟨hle_sz, hp_ub, ext1, hext1_len, hm1⟩
          hLoop => ?_)
    · c0_steps
      refine hLoop _ _ ⟨by simp, by bv_omega, _, by rw [List.length_set, hesl], hm⟩
    · c0_split
      · simp only [show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
          Nat.mod_eq_of_lt (by omega : cref.toNat + 2 < 2 ^ 64)] at hc
        have hi_lt : i.toNat < sz := hc
        have hli_eq : (cref.setWidth 64 + 3 + i.setWidth 64).toNat = cref.toNat + 3 + i.toNat := by
          bv_omega
        have hli_lt : (cref.setWidth 64 + 3 + i.setWidth 64).toNat < s.core.arena.length := by
          rw [hli_eq, harl]; omega
        refine wp_load_of (FullArenaTactics.c0_load_full_arena
          (s := { s with scratch := { s.scratch with extend_stk := ext1 } }) hli_lt hm1) ?_
        have hi1 : (i + 1).toNat = i.toNat + 1 := by bv_omega
        refine wp_join_group
          (fun (p', ()) m' =>
            p'.toNat ≤ s.scratch.extend_len + 1 + (i.toNat + 1) ∧
            ∃ ext2 : List (BitVec 32), ext2.length = c.extend_cap ∧
              (FullMem c { s with scratch := { s.scratch with extend_stk := ext2 } } ⋆ R) m')
          (fun Js (p', ()) m' ⟨hp'ub, ext2, hext2_len, hm'⟩ => ?_) (fun Js hJs => ?_)
        · c0_steps
          refine hLoop (p', i + 1, ()) m' ?_ ⟨?_, ?_, ext2, hext2_len, hm'⟩
          · dsimp only; rw [hi1]; omega
          · rw [hi1]; omega
          · rw [hi1]; exact hp'ub
        · c0_split
          · have hp_lt_cap : p.toNat < c.extend_cap := by omega
            have hp_lt_ext1 : p.toNat < ext1.length := by rw [hext1_len]; exact hp_lt_cap
            c0_steps
            refine wp_store_sep (FullArenaTactics.c0_store_full_extend_stk _ hp_lt_ext1 hm1)
              fun m hm => ?_
            c0_steps
            have hp1 : (p + 1).toNat = p.toNat + 1 := by bv_omega
            exact hJs (p + 1, ()) m ⟨by omega, _, by rw [List.length_set, hext1_len], hm⟩
          · exact hJs (p, ()) m1 ⟨by omega, ext1, hext1_len, hm1⟩
      · have hcr2_mod : (cref.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = cref.toNat + 2 := by
          rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
        simp only [hcr2_mod] at hc
        have hieq : i.toNat = sz := by dsimp only [sz] at *; omega
        have hp_fin : p.toNat ≤ c.extend_cap := by rw [hieq] at hp_ub; omega
        c0_steps
        refine wp_store_sep (FullArenaTactics.c0_store_full_extend_len p hm1) fun m hm => ?_
        c0_steps
        refine hQ (true, ()) _ _ ?_ ?_ ?_ hm
        · rfl
        · exact fullState_lengths_with_ext hlen hext1_len
        · exact ⟨rfl, hp_fin, rfl⟩

theorem full_extend_wp (Γ : Env) :
    ∀ a m Q X, fullExtendSpec a m Q X → Func.wp Γ full_extend_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hel⟩, hlen, hm, hQ⟩
  dsimp only [fullExtendSlice_mem, fullExtendSlice_coreProj, fullExtendSlice_safe] at hlen hm hQ
  obtain hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  obtain hext : c.extend_cap < dimacsBound := c.hext
  unfold dimacsBound at hmax hext
  obtain hcv_le := hlen.core_ok.cur_vars_le
  obtain hvl := hlen.core_ok.vals_len
  obtain hfll := hlen.core_ok.flags_len
  obtain hesl := hlen.scratch_ok.extend_stk_len
  c0_to_group
  refine wp_loop_safety_slice (fullExtendSlice c) s R (fun _ => True) trivial
    (fun s1 ((v : BitVec 64), ()) => v.toNat ≤ s.core.cur_vars)
    (fun ((v : BitVec 64), ()) => s.core.cur_vars - v.toNat)
    (fun J hJ => ?_) (fun J s1 ((v : BitVec 64), ()) m1 hcore1 hs1 _ hvle hm1 hJ => ?_)
  · c0_steps; exact hJ s (0#64, ()) m hm rfl hlen (by simp)
  · dsimp only [fullExtendSlice_mem, fullExtendSlice_coreProj, fullExtendSlice_safe] at hs1 hm1
    clear hm hlen
    obtain ⟨_, _, _, hcv1, _, _⟩ := fullExtend_preserves_nonVals hcore1
    obtain hvl1 := hs1.core_ok.vals_len
    obtain hfll1 := hs1.core_ok.flags_len
    c0_to_group
    · have hv_lt : v.toNat < s.core.cur_vars := by omega
      have hv_fl : v.toNat < s1.core.flags.length := by rw [hfll1]; omega
      have hv_shl : (v <<< (1 : Nat)).toNat < s1.core.vals.length := by
        rw [hvl1, BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
      refine wp_join_safety_slice (fullExtendSlice c) s1 R (fun _ => True) trivial
        (fun _ _ => True) (fun J2 s2 _ m2 hcore2 hs2 _ _ hm2 => ?_) (fun J2 hJ2 => ?_)
      · dsimp only [fullExtendSlice_mem, fullExtendSlice_coreProj, fullExtendSlice_safe] at hs2 hm2
        have hv1 : (v + 1).toNat = v.toNat + 1 := by bv_omega
        c0_steps; exact hJ s2 (v + 1, ()) m2 hm2 (by dsimp only; omega) hcore2 hs2
          (by dsimp only; omega)
      · clear hQ hJ hv_fl
        c0_steps
        · have hv_or : ((v <<< (1 : Nat)) ||| (1 : BitVec 64)).toNat <
              (s1.core.vals.set (v <<< (1 : Nat)).toNat 1#8).length := by
            rw [List.length_set, hvl1, show (1 : BitVec 64) = 1#64 from rfl,
              bv64_shl1_or_1_toNat (by omega)]
            omega
          refine wp_store_sep
            (FullArenaTactics.c0_store_full_vals (BitVec.setWidth 8 (-1)) hv_or hm)
            fun m hm => ?_
          c0_steps
          refine hJ2 _ () _ hm rfl
            ⟨{ hs1.core_ok with vals_len := by simp [hvl1] }, hs1.scratch_ok⟩ trivial
        · have hv_or : ((v <<< (1 : Nat)) ||| (1 : BitVec 64)).toNat <
              (s1.core.vals.set (v <<< (1 : Nat)).toNat 1#8).length := by
            rw [List.length_set, hvl1, show (1 : BitVec 64) = 1#64 from rfl,
              bv64_shl1_or_1_toNat (by omega)]
            omega
          refine wp_store_sep
            (FullArenaTactics.c0_store_full_vals (BitVec.setWidth 8 (-1)) hv_or hm)
            fun m hm => ?_
          c0_steps
          refine hJ2 _ () _ hm rfl
            ⟨{ hs1.core_ok with vals_len := by simp [hvl1] }, hs1.scratch_ok⟩ trivial
        · exact hJ2 s1 () m1 hm1 rfl hs1 trivial
    · clear hJ
      obtain ⟨_, _, _, hcv1, _, _⟩ := fullExtend_preserves_nonVals hcore1
      c0_steps
      refine wp_loop_safety_slice (fullExtendSlice c) s1 R (fun _ => True) trivial
        (fun _ ((end_v : BitVec 64), ()) => end_v.toNat ≤ c.extend_cap)
        (fun ((end_v : BitVec 64), ()) => end_v.toNat)
        (fun Je hJe => ?_)
        (fun Je s2 ((end_v : BitVec 64), ()) m2 hcore2 hs2 _ hendle hm2 hJe => ?_)
      · c0_steps; exact hJe s1 (BitVec.ofNat 64 s1.scratch.extend_len, ()) m1 hm1
          rfl hs1 (by
            have hsc1 := (fullExtend_preserves_nonVals hcore1).1
            dsimp only; rw [hsc1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hel)
      · dsimp only [fullExtendSlice_mem, fullExtendSlice_coreProj, fullExtendSlice_safe] at hs2 hm2
        clear hm1 hvl1 hfll1
        obtain ⟨hsc2, _, _, hcv2, _, _⟩ := fullExtend_preserves_nonVals hcore2
        c0_to_group
        · have hend_pos : 0 < end_v.toNat := by omega
          have hesl2 : s2.scratch.extend_stk.length = c.extend_cap := hs2.scratch_ok.extend_stk_len
          refine wp_loop_safety_slice_break (brkTs := [i64, .bool, i32]) (lpTs := [i64, .bool])
            (fullExtendSlice c) s2 R (fun _ => True) trivial
            (fun _ ((start_v : BitVec 64), (_sat : Bool), (blk : BitVec 32), ()) =>
              start_v.toNat < end_v.toNat ∧
              (blk = 0xFFFFFFFF#32 ∨ blk.toNat < 2 ^ 31))
            (fun _ ((start_v : BitVec 64), (_sat : Bool), ()) =>
              start_v.toNat ≤ end_v.toNat)
            (fun _ ((start_v : BitVec 64), (_sat : Bool), ()) => start_v.toNat)
            (fun B s3 (start_v, sat, blk, ()) m3 hcore3 hs3 _ ⟨hstart_lt, hblk_dom⟩ hm3 => ?_)
            (fun B L s3 (start_v, sat, ()) m3 hcore3 hs3 _ hstart_le hm3 hB hL => ?_)
            (fun B L _ hL => ?_)
          · dsimp only [fullExtendSlice_mem, fullExtendSlice_coreProj,
              fullExtendSlice_safe] at hs3 hm3
            clear hm2
            obtain ⟨_, _, _, hcv3, _, _⟩ := fullExtend_preserves_nonVals hcore3
            obtain hvl3 := hs3.core_ok.vals_len
            c0_steps
            all_goals
              try
                exact hJe s3 (start_v, ()) m3 hm3 (by dsimp only; exact hstart_lt) hcore3
                  hs3 (by dsimp only; omega)
            have hblk_v : blk.toNat / 2 < s3.core.cur_vars := by omega
            have hblk_xor : ((blk ^^^ 1#32).setWidth 64).toNat <
                (s3.core.vals.set (blk.setWidth 64).toNat 1#8).length := by
              rw [List.length_set, hvl3, zext_toNat _ (by decide)]
              exact Nat.lt_of_lt_of_le (bv32_xor1_lt hblk_v) (by omega)
            refine wp_store_sep (FullArenaTactics.c0_store_full_vals _ hblk_xor hm) fun m hm => ?_
            c0_steps
            refine hJe _ (start_v, ()) _ hm (by dsimp only; exact hstart_lt)
              (hcore3.trans rfl)
              ⟨{ hs3.core_ok with vals_len := by simp [hvl3] }, hs3.scratch_ok⟩
              (by omega)
          · dsimp only [fullExtendSlice_mem, fullExtendSlice_coreProj,
              fullExtendSlice_safe] at hs3 hm3
            clear hm2
            obtain ⟨_, _, _, hcv3, _, _⟩ := fullExtend_preserves_nonVals hcore3
            obtain hvl3 := hs3.core_ok.vals_len
            obtain hesl3 := hs3.scratch_ok.extend_stk_len
            c0_split
            · have hs_pos : 0 < start_v.toNat := by omega
              have hsm1 : (start_v - 1).toNat < start_v.toNat := by bv_omega
              have hsm1_cap : (start_v - 1).toNat < s3.scratch.extend_stk.length := by omega
              c0_steps
              refine wp_load_of (FullArenaTactics.c0_load_full_extend_stk hsm1_cap hm3) ?_
              c0_to_group
              refine wp_join_group (fun (sat', ()) m' => m' = m3)
                (fun Js (sat', ()) m' hm' => ?_) (fun Js hJs => ?_)
              · subst m'
                c0_steps
                all_goals first
                  | exact hB s3 (start_v - 1, _,
                      (s3.scratch.extend_stk[(start_v - 1).toNat]'(by omega)) &&& 0x7FFFFFFF#32, ())
                      m3 hm3 rfl hs3
                      ⟨by dsimp only at hstart_le; omega, Or.inr bv32_and_ext_mask_lt⟩
                  | exact hL s3 (start_v - 1, _, ()) m3 hm3 hsm1 rfl hs3
                      (by dsimp only at hstart_le; omega)
              · c0_steps
                all_goals exact hJs _ m3 rfl
            · c0_steps
              exact hB s3 (start_v, sat, 0xFFFFFFFF#32, ()) m3 hm3 rfl hs3
                ⟨by dsimp only at hstart_le; omega, Or.inl rfl⟩
          · c0_steps
            exact hL s2 (end_v, false, ()) m2 hm2 rfl hs2 (Nat.le_refl _)
        · exact hQ () s2 m2 (hcore1.trans hcore2) hs2 trivial hm2

private theorem wp_let_add64 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a b : Arg Val i64} {k : Tup Val [i64] → Expr Val Cont rs} :
    wp Γ Q X (.let_ (Op.mk (.add i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val + b.val, ())) m := by
  simpa [Ty.hasFloat, Ty.isFloatTree, lift2] using @wp_let_add_eq Γ rs Q X m i64 (a, b, ()) k

private theorem wp_let_ult64 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {hm : Ty.bool = Ty.mask i64} {a b : Arg Val i64}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult i64 .bool hm) (a, b, ())) k) m =
      wp Γ Q X (k (BitVec.ult a.val b.val, ())) m := by
  have hc := @wp_let_cmp_eq Γ rs Q X m .ult i64 .bool hm (a, b, ()) k
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, liftCmp,
    evalBits_ult_eq, cast_eq] using hc

private theorem probePres_refl (s : FullState) : FullProbeScratchPres s s :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem probePres_trans {s₁ s₂ s₃ : FullState}
    (h12 : FullProbeScratchPres s₁ s₂) (h23 : FullProbeScratchPres s₂ s₃) :
    FullProbeScratchPres s₁ s₃ :=
  ⟨⟨h23.1.1.trans h12.1.1, h23.1.2.trans h12.1.2⟩, h23.2.1.trans h12.2.1,
   h23.2.2.1.trans h12.2.2.1, h23.2.2.2.1.trans h12.2.2.2.1,
   h23.2.2.2.2.1.trans h12.2.2.2.2.1, h23.2.2.2.2.2.1.trans h12.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.trans h12.2.2.2.2.2.2.2⟩

theorem full_switch_mode_wp (Γ : Env)
    (hDown : ∀ a m Q X, fullHeapDownSpec a m Q X → Γ "full_heap_down" [i64, i32] [] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullSwitchModeSpec a m Q X → Func.wp Γ full_switch_mode_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hlen hm hQ
  obtain hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  obtain hcv_le := hlen.core_ok.cur_vars_le
  c0_to_group
  refine wp_join_safety_slice (fullSafetySlice c) s R (fun _ => True) trivial
    (fun s1 _ => FullProbeScratchPres s s1)
    (fun J_out s1 _ m1 hcore1 hs1 _ hpres1 hm1 => ?_) (fun J_out hJ_out => ?_)
  · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hs1 hm1
    c0_steps
    let s2 : FullState :=
      { s1 with scratch :=
        { s1.scratch with
          switched := s1.scratch.switched + 1
          mode_count := s1.scratch.mode_count + 1
          ema_fast_biased := 0#64
          ema_fast_exp := (1#64 <<< (24 : Nat))
          ema_slow_biased := 0#64
          ema_slow_exp := (1#64 <<< (24 : Nat))
          restart_limit := s1.scratch.conflicts + 1 } }
    exact hQ () s2 _ hcore1
      ⟨hs1.core_ok, { hs1.scratch_ok with walk_vals_len := hs1.scratch_ok.walk_vals_len }⟩
      hpres1 hm
  · c0_split
    · c0_split
      · c0_steps; exact hQ () s m rfl hlen (probePres_refl s) hm
      · clear hQ
        c0_to_group
        refine wp_join_safety_slice (fullSafetySlice c)
          { s with scratch := { s.scratch with stable := 1#64 } } R (fun _ => True) trivial
          (fun s1 _ => FullProbeScratchPres s s1)
          (fun Jd s1 ((dticks : BitVec 64), ()) m1 hcore1 hs1 _ hpres1 hm1 => ?_)
          (fun Jd hJd => ?_)
        · clear hm hlen
          dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
            fullSafetySlice_safe] at hs1 hm1
          have heq1 := fullCoreState_agrees_with_scratch hcore1
          rw [Blocks.get_here]
          repeat (first
            | rw [wp_let_add64]
            | (rw [LeanQbe.T.op2_eq_mk]; rw [wp_let_add64])
            | c0_step)
          let s1' : FullState :=
            { s1 with scratch :=
              { s1.scratch with
                mode_tick_lim := s1.scratch.search_ticks + dticks
                mode_saved_ticks := s1.scratch.search_ticks } }
          refine wp_loop_safety_slice (ts := [i64, i64]) (fullSafetySlice c) s1' R
            (fun _ => True) trivial
            (fun s2 ((n : BitVec 64), (v : BitVec 64), ()) => n.toNat ≤ v.toNat ∧
              v.toNat ≤ s.core.cur_vars ∧ FullProbeScratchPres s s2)
            (fun (_, (v : BitVec 64), ()) => s.core.cur_vars - v.toNat)
            (fun Jl hJl => ?_)
            (fun Jl s2 ((n : BitVec 64), (v : BitVec 64), ()) m2 hcore2 hs2 _
                ⟨hnle, hvle, hpres2⟩ hm2 hJl => ?_)
          · c0_steps
            refine hJl _ (0#64, 0#64, ()) m hm rfl ?_ ⟨by simp, by simp, hpres1⟩
            exact ⟨hs1.core_ok,
              { hs1.scratch_ok with walk_vals_len := hs1.scratch_ok.walk_vals_len }⟩
          · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
              fullSafetySlice_safe] at hs2 hm2
            have heq2 := fullCoreState_agrees_with_scratch hcore2
            obtain hfl2 := hs2.core_ok.flags_len
            obtain hvl2 := hs2.core_ok.vals_len
            obtain hhl2 := hs2.scratch_ok.heap_len_arr
            obtain hpl2 := hs2.scratch_ok.pos_len
            repeat clear hc
            clear hm
            rw [Blocks.get_here]; dsimp only
            rw [wp_let_ult64]
            refine wp_jnz_of (fun hc => ?_) (fun hc => ?_)
            · simp only [Arg.val_var] at hc; c0_cond hc
              have hv_lt : v.toNat < s.core.cur_vars := by
                rw [heq1] at hc
                first | exact hc | {
                  have hc_v' : v.toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by
                    simpa using hc
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc_v'
                  exact hc_v' }
              have hv_fl : v.toNat < s2.core.flags.length := by rw [hfl2]; omega
              have hv1 : (v + 1).toNat = v.toNat + 1 := by bv_omega
              refine wp_join_safety_slice (ts := [i64]) (fullSafetySlice c) s2 R
                (fun _ => True) trivial
                (fun s2' ((n' : BitVec 64), ()) =>
                  n'.toNat ≤ v.toNat + 1 ∧ FullProbeScratchPres s s2')
                (fun Js s2' ((n' : BitVec 64), ()) m2' hcore2' hs2' _ ⟨hn'le, hpres2'⟩
                    hm2' => ?_)
                (fun Js hJs => ?_)
              · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                  fullSafetySlice_safe] at hs2' hm2'
                c0_steps
                exact hJl s2' (n', v + 1, ()) m2' hm2' (by dsimp only; rw [hv1]; omega) hcore2'
                  hs2' ⟨by rw [hv1]; omega, by rw [hv1]; omega, hpres2'⟩
              · refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s2 R
                  (fun _ => True) trivial
                  (fun s2' _ => FullProbeScratchPres s s2')
                  (fun Js1 s2' _ m2' hcore2' hs2' _ hpres2' hm2' => ?_)
                  (fun Js1 hJs1 => ?_)
                · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                    fullSafetySlice_safe] at hs2' hm2'
                  have hv_pos : v.toNat < s2'.scratch.pos.length := by
                    rw [hs2'.scratch_ok.pos_len]; omega
                  rw [Blocks.get_here]; dsimp only
                  c0_steps
                  refine wp_store_sep (FullArenaTactics.c0_store_full_pos _ hv_pos hm2')
                    fun m hm => ?_
                  c0_steps
                  exact hJs _ (n, ()) _ hm hcore2'
                    ⟨hs2'.core_ok,
                      { hs2'.scratch_ok with pos_len := by simp [hs2'.scratch_ok.pos_len] }⟩
                    ⟨by omega, hpres2'⟩
                · c0_split
                  · have hv2 : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
                      rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
                    have hv2_lt : (v <<< (1 : Nat)).toNat < s2.core.vals.length := by
                      rw [hvl2, hv2]; omega
                    refine wp_load_of (FullArenaTactics.c0_load_full_vals hv2_lt hm2) ?_
                    c0_split
                    · have hn_lt : n.toNat < s2.scratch.heap.length := by rw [hhl2]; omega
                      have hv_pos : v.toNat < s2.scratch.pos.length := by rw [hpl2]; omega
                      have hn1 : (n + 1).toNat = n.toNat + 1 := by bv_omega
                      c0_steps
                      refine wp_store_sep (FullArenaTactics.c0_store_full_heap _ hn_lt hm2)
                        fun m_h hm_h => ?_
                      clear hm2
                      c0_steps
                      exact hJs _ (n + 1, ()) _ hm rfl
                        ⟨hs2.core_ok, { hs2.scratch_ok with
                          heap_len_arr := by simp [hhl2], pos_len := by simp [hpl2] }⟩
                        ⟨by rw [hn1]; omega, hpres2⟩
                    · exact hJs1 s2 () m2 hm2 rfl hs2 hpres2
                  · exact hJs1 s2 () m2 hm2 rfl hs2 hpres2
            · clear hJl
              c0_steps
              refine wp_loop_safety_slice (fullSafetySlice c)
                { s2 with scratch := { s2.scratch with heap_len := n.toNat } } R
                (fun _ => True) trivial
                (fun s3 ((sp : BitVec 64), ()) => sp.toNat ≤ c.max_vars ∧
                  FullProbeScratchPres s s3)
                (fun ((sp : BitVec 64), ()) => sp.toNat)
                (fun Js hJs => ?_)
                (fun Js s3 ((sp : BitVec 64), ()) m3 hcore3 hs3 _ ⟨hsple, hpres3⟩ hm3
                    hJs => ?_)
              · c0_steps
                refine hJs _ (n >>> (1 : Nat), ()) _ hm rfl
                  ⟨hs2.core_ok,
                    { hs2.scratch_ok with walk_vals_len := hs2.scratch_ok.walk_vals_len }⟩
                  ⟨by rw [BitVec.toNat_ushiftRight]; simp [Nat.shiftRight_eq_div_pow]; omega,
                    hpres2⟩
              · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                  fullSafetySlice_safe] at hs3 hm3
                obtain hhl3 := hs3.scratch_ok.heap_len_arr
                c0_steps
                · have hsp_pos : 0 < sp.toNat := by omega
                  have hsm1 : (sp - 1).toNat < sp.toNat := by bv_omega
                  c0_call hDown
                  refine ⟨c, s3, R, rfl, hs3, hm3, ?_⟩
                  intro _ s4 m4 hcore4 hs4 ⟨_, hpres34⟩ hm4
                  exact hJs s4 (sp - 1, ()) m4 hm4 hsm1 hcore4 hs4
                    ⟨by omega, probePres_trans hpres3 hpres34⟩
                · exact hJ_out s3 () m3 hm3 (hcore1.trans (hcore2.trans hcore3)) hs3 hpres3
        · c0_steps
          · exact hJd _ (1000#64, ()) _ hm rfl
              ⟨hlen.core_ok,
                { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len }⟩
              (probePres_refl s)
          · exact hJd _ (s.scratch.search_ticks - s.scratch.mode_saved_ticks, ()) _ hm rfl
              ⟨hlen.core_ok,
                { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len }⟩
              (probePres_refl s)
    · c0_split
      · c0_steps; exact hQ () s m rfl hlen (probePres_refl s) hm
      · clear hQ
        obtain hqsl := hlen.scratch_ok.q_stamp_len
        c0_steps
        c0_call hIlog
        intro r hr1 hr19
        c0_split
        · have hql_lt : s.scratch.q_last.toNat < s.scratch.q_stamp.length := by
            rw [hqsl]; bv_omega
          refine wp_load_of (FullArenaTactics.load_full_q_stamp_ptr hm) ?_
          c0_steps
          refine hJ_out _ () _ hm rfl
            ⟨hlen.core_ok, { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len }⟩
            (probePres_refl s)
        · c0_steps
          refine hJ_out _ () _ hm rfl
            ⟨hlen.core_ok, { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len }⟩
            (probePres_refl s)

theorem full_walk_cl_sat_wp (Γ : Env) :
    ∀ a m Q X, fullWalkClSatSpec a m Q X → Func.wp Γ full_walk_cl_sat_body a m Q X := by
  rintro ⟨h, scr, idx, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, rfl, ⟨F0, hinv⟩, hidx, hok⟩, hlen, hm, hQ⟩
  obtain ⟨F_cur, hw_inv⟩ := hinv.witness
  obtain ha := hw_inv.arena
  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hlen hm hQ
  c0_steps
  obtain hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  obtain haca : c.arena_cap < 2 * dimacsBound := c.harena
  obtain hsca : c.scratch_cap < dimacsBound := c.hscr
  unfold dimacsBound at hmax haca hsca
  obtain hcv_le := hlen.core_ok.cur_vars_le
  obtain hvl0 := hlen.core_ok.vals_len
  obtain hfl0 := hlen.core_ok.flags_len
  obtain hvl := hlen.core_ok.vals_len
  obtain harl := hlen.core_ok.arena_len_arr
  obtain hale := hlen.core_ok.arena_len_le
  obtain hwvl := hlen.scratch_ok.walk_vals_len
  obtain hsbl := hlen.scratch_ok.scratch_buf_len
  have hi2 : (idx <<< (1 : Nat)).toNat = 2 * idx.toNat := by
    rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
  have hi2p1 : ((idx <<< (1 : Nat)) + 1).toNat = 2 * idx.toNat + 1 := by
    rw [BitVec.toNat_add, hi2]; simp; omega
  have hi2_lt : (idx <<< (1 : Nat)).toNat < s.scratch.scratch_buf.length := by rw [hsbl, hi2]; omega
  have hi2p1_lt : ((idx <<< (1 : Nat)) + 1).toNat < s.scratch.scratch_buf.length := by
    rw [hsbl, hi2p1]; omega
  refine wp_load_of (FullArenaTactics.c0_load_full_scratch_buf hi2_lt hm) ?_
  c0_split
  · have hbin' :
        (s.scratch.scratch_buf[2 * idx.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
      simpa [hi2, Nat.mod_eq_of_lt (by omega : 2 * idx.toNat < 2 ^ 64),
        List.getElem?_eq_getElem (by omega : 2 * idx.toNat < s.scratch.scratch_buf.length)]
        using hc
    clear hc
    obtain ⟨ha_lt, hb_lt⟩ := walk_entry_bin_bounds hok hbin'
    have hwa_lt : (s.scratch.scratch_buf[2 * idx.toNat]'(by omega) &&& 0x7FFFFFFF#32).toNat <
        2 * s.core.cur_vars := by
      simpa [List.getElem?_eq_getElem (by omega : 2 * idx.toNat < s.scratch.scratch_buf.length)]
        using ha_lt
    have hwb_lt : (s.scratch.scratch_buf[2 * idx.toNat + 1]'(by omega)).toNat <
        2 * s.core.cur_vars := by
      simpa [List.getElem?_eq_getElem (by omega : 2 * idx.toNat + 1 < s.scratch.scratch_buf.length)]
        using hb_lt
    have hwa_vals :
        ((s.scratch.scratch_buf[(idx <<< (1 : Nat)).toNat]'hi2_lt &&& 0x7FFFFFFF#32).setWidth
          64).toNat < s.core.vals.length := by
      rw [hvl, zext_toNat _ (by decide)]; simp only [hi2]; omega
    have hwa_wv :
        ((s.scratch.scratch_buf[(idx <<< (1 : Nat)).toNat]'hi2_lt &&& 0x7FFFFFFF#32).setWidth
          64).toNat < s.scratch.walk_vals.length := by
      rw [hwvl, zext_toNat _ (by decide)]; simp only [hi2]; omega
    have hwb_vals :
        ((s.scratch.scratch_buf[((idx <<< (1 : Nat)) + 1).toNat]'hi2p1_lt).setWidth 64).toNat <
          s.core.vals.length := by
      rw [hvl, zext_toNat _ (by decide)]; simp only [hi2p1]; omega
    have hwb_wv :
        ((s.scratch.scratch_buf[((idx <<< (1 : Nat)) + 1).toNat]'hi2p1_lt).setWidth 64).toNat <
          s.scratch.walk_vals.length := by
      rw [hwvl, zext_toNat _ (by decide)]; simp only [hi2p1]; omega
    refine wp_load_of (FullArenaTactics.c0_load_full_scratch_buf hi2p1_lt hm) ?_
    refine wp_join_group (fun _ m' => m' = m)
      (fun Js _ m' heqm => by subst heqm; c0_steps; exact hQ _ s _ rfl hlen rfl hm)
      (fun Js hJs => ?_)
    c0_steps
    all_goals (try c0_split)
    all_goals (try c0_steps)
    all_goals (try c0_split)
    all_goals (try c0_steps)
    all_goals (try c0_split)
    all_goals exact hJs _ _ rfl
  · have hlrg' :
        (s.scratch.scratch_buf[2 * idx.toNat]?.getD 0#32 &&& 0x80000000#32) = 0#32 := by
      simpa [hi2, Nat.mod_eq_of_lt (by omega : 2 * idx.toNat < 2 ^ 64),
        List.getElem?_eq_getElem (by omega : 2 * idx.toNat < s.scratch.scratch_buf.length)]
        using hc
    clear hc
    let w0 := s.scratch.scratch_buf[2 * idx.toNat]'(by omega)
    have hw0_ref : w0.toNat ∈ fullArenaClauseRefs s := by
      unfold FullWalkEntryOk at hok
      simp only [hlrg', ne_eq, not_true_eq_false, ↓reduceIte] at hok
      simpa [w0, List.getElem?_eq_getElem (by omega : 2 * idx.toNat < s.scratch.scratch_buf.length)]
        using hok.1
    have hw0_ng : fullArenaClauseGarb s w0.toNat = false := by
      unfold FullWalkEntryOk at hok
      simp only [hlrg', ne_eq, not_true_eq_false, ↓reduceIte] at hok
      simpa [w0, List.getElem?_eq_getElem (by omega : 2 * idx.toNat < s.scratch.scratch_buf.length)]
        using hok.2
    have hwf := ha.refs_wf w0.toNat hw0_ref
    have hw0_2_lt : (w0.setWidth 64 + 2).toNat < s.core.arena.length := by c0_bound
    have hw0_2_lt' :
        ((s.scratch.scratch_buf[(idx <<< (1 : Nat)).toNat]'hi2_lt).setWidth 64 + 2).toNat <
          s.core.arena.length := by
      simpa [w0, hi2] using hw0_2_lt
    refine wp_load_of (FullArenaTactics.c0_load_full_arena hw0_2_lt' hm) ?_
    let sz := s.core.arena[(w0.setWidth 64 + 2).toNat]'hw0_2_lt
    have hsz_eq : sz.toNat = fullArenaClauseSize s w0.toNat := by
      unfold fullArenaClauseSize fullArenaClauseSizeCore
      have hw2 : (w0.setWidth 64 + 2).toNat = w0.toNat + 2 := by c0_bound
      simp only [sz, hw2, List.getElem?_eq_getElem (by omega : w0.toNat + 2 < s.core.arena.length),
        Option.getD_some]
    have hw0_bd' :
        w0.toNat + 3 + fullArenaClauseSizeCore s.core w0.toNat ≤ s.core.arena.length := by
      have hle := Nat.le_trans hwf.2.2.1 hwf.2.2.2.1; omega
    have hw0_bd : w0.toNat + 3 + sz.toNat ≤ s.core.arena.length := by
      unfold fullArenaClauseSize at hsz_eq; dsimp only [sz] at hsz_eq ⊢; rw [hsz_eq]; exact hw0_bd'
    refine wp_loop_inv
      (fun (i, ()) m1 => m1 = m ∧ i.toNat ≤ sz.toNat)
      (fun (i, ()) _ => sz.toNat - i.toNat) (fun J hLoop => ?_)
      (fun J (i, ()) m1 ⟨rfl, hile⟩ hLoop => ?_)
    · c0_steps; exact hLoop _ _ ⟨rfl, by simp⟩
    · rw [Blocks.get_here]; dsimp only
      c0_split
      · have hw0_eq_sb : s.scratch.scratch_buf[(idx <<< (1 : Nat)).toNat]'hi2_lt = w0 := by
          dsimp only [w0]; congr 1
        have hw2_mod : (w0.toNat + 2) % 2 ^ 64 = w0.toNat + 2 := Nat.mod_eq_of_lt (by omega)
        have hi_lt : i.toNat < sz.toNat := by
          simpa [sz, w0, hi2, Nat.mod_eq_of_lt (by omega : 2 * idx.toNat < 2 ^ 64), hw2_mod]
            using hc
        have hli_eq : (w0.setWidth 64 + 3 + i.setWidth 64).toNat = w0.toNat + 3 + i.toNat := by
          c0_bound
        have hli_ar : (w0.setWidth 64 + 3 + i.setWidth 64).toNat < s.core.arena.length := by omega
        have hli_ar' :
            ((s.scratch.scratch_buf[(idx <<< (1 : Nat)).toNat]'hi2_lt).setWidth 64 + 3 +
              i.setWidth 64).toNat < s.core.arena.length := by
          rw [hw0_eq_sb]; exact hli_ar
        have hlit_mem : (s.core.arena[w0.toNat + 3 + i.toNat]'(by omega)).toNat ∈
            fullArenaClauseLits s w0.toNat :=
          (mem_fullArenaClauseLitsCore_iff hw0_bd').mpr
            ⟨i.toNat, by unfold fullArenaClauseSize at hsz_eq; rw [← hsz_eq]; exact hi_lt, rfl⟩
        have hlit_lt : (s.core.arena[w0.toNat + 3 + i.toNat]'(by omega)).toNat <
            2 * s.core.cur_vars := ha.lits_lt w0.toNat hw0_ref hw0_ng _ hlit_mem
        have hli_el :
            s.core.arena[((s.scratch.scratch_buf[(idx <<< (1 : Nat)).toNat]'hi2_lt).setWidth 64 +
              3 + i.setWidth 64).toNat]'hli_ar' =
            s.core.arena[w0.toNat + 3 + i.toNat]'(by omega) := by
          simp only [hw0_eq_sb, hli_eq]
        have hlit_vals :
            ((s.core.arena[((s.scratch.scratch_buf[(idx <<< (1 : Nat)).toNat]'hi2_lt).setWidth 64 +
              3 + i.setWidth 64).toNat]'hli_ar').setWidth 64).toNat < s.core.vals.length := by
          rw [hvl, zext_toNat _ (by decide), hli_el]; omega
        have hlit_wv :
            ((s.core.arena[((s.scratch.scratch_buf[(idx <<< (1 : Nat)).toNat]'hi2_lt).setWidth 64 +
              3 + i.setWidth 64).toNat]'hli_ar').setWidth 64).toNat <
              s.scratch.walk_vals.length := by
          rw [hwvl, zext_toNat _ (by decide), hli_el]; omega
        have hi1 : (i + 1).toNat = i.toNat + 1 := by
          have hsz_lt := sz.isLt; bv_omega
        refine wp_load_of (FullArenaTactics.c0_load_full_arena (s := s) hli_ar' hm) ?_
        c0_steps
        · exact hQ (true, ()) s _ rfl hlen rfl hm
        · exact hQ (true, ()) s _ rfl hlen rfl hm
        · exact hLoop _ _ (by dsimp only; rw [hi1]; omega) ⟨rfl, by rw [hi1]; omega⟩
      · exact hQ (false, ()) s _ rfl hlen rfl hm
