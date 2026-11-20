module

public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.Full3
public import LeanQbe.T.Logic.C0Step

/-!
# Kissat `D-Full` Dense/Watch/Reduce Specs & Pure Preservation Lemmas (`Stage 4`, Part 1)

Defines local canonical Stage-4 invariants and contracts inside `namespace FullDenseWatchSpecs`
for the `full_reduce`, `full_enter_dense`, and `full_rebuild_watches` shard, plus pure
preservation lemmas:
1. `DenseWatchSliceOk` → `WatchSliceOk` coercion, relocation, append, and
   `fullWatchPush_preserves_denseWatchesInv`.
2. Arena block-chain stepping (`fullArenaClauseRefs_zero_mem`, `fullArenaClauseRefs_next_mem`).
3. Witness-preserving arena header updates: used-counter decrement (`updateUsed_preserves_*`)
   and non-reason garbage marking (`markGarb_preserves_fullWitnessInv`,
   `markGarb_preserves_arenaVarsNodup`, `markGarb_preserves_reasonsMarked`).
4. Mode-flip (`dense_mode` `0 ↔ 1`) and `FullConflictInv` level-0 UNSAT refutation helpers.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Canonical Stage-4 invariants and specs (`namespace FullDenseWatchSpecs`) -/

namespace FullDenseWatchSpecs

def FullLitMarksClear (c : FullCfg) (s : FullState) : Prop :=
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
  (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)

def FullArenaVarsNodup (s : FullState) : Prop :=
  ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false →
    ((fullArenaClauseLits s r).map (· / 2)).Nodup

def FullLastLearnedWf (s : FullState) : Prop :=
  ∀ i < 8,
    let cr := s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32
    cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ fullArenaClauseRefs s

def FullExtScratchOk (c : FullCfg) (s : FullState) : Prop :=
  FullLastLearnedWf s ∧ s.scratch.extend_len ≤ c.extend_cap

def FullSparseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

def FullDenseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64

/-- Every large arena reason referenced by a positive-level trail literal has `PH_RSN`
(`0x00200000#32`) set in its header word. -/
def FullReasonsMarked (s : FullState) : Prop :=
  ∀ idx < s.core.trail_end,
    let v := (s.core.trl[idx]?.getD 0#32).toNat / 2
    let rsn := s.core.rsns[v]?.getD 0xFFFFFFFF#32
    0 < (s.core.lvl[v]?.getD 0#32).toNat →
    (rsn &&& 0x80000000#32) = 0#32 →
    (fullArenaHdr s rsn.toNat &&& 0x00200000#32) ≠ 0#32

/-- Falsified conflict clause reported by `full_propagate` when returning `1#64`. -/
def FullConflictInv (_c : FullCfg) (_F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) : Prop :=
  (s.core.confl_type = 1#64 ∧
    s.core.confl_lit0.toNat < 2 * s.core.cur_vars ∧
    s.core.confl_lit1.toNat < 2 * s.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [s.core.confl_lit0.toNat, s.core.confl_lit1.toNat]) ∧
    s.core.vals[s.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
    s.core.vals[s.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8) ∨
  (s.core.confl_type = 2#64 ∧
    s.core.confl_ref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s s.core.confl_ref.toNat = false ∧
    ∀ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8)

/-! ### Callee contracts (`11` callees across `Full1` & `Full2`) -/

def fullIsqrtSpec : Spec [i64] [i64] := fun (x, ()) m Q _ =>
  ∀ r : BitVec 64, r.toNat ≤ x.toNat → Q (r, ()) m

def fullIlog10Spec : Spec [i64] [i64] := fun (_x, ()) m Q _ =>
  ∀ r : BitVec 64, 1 ≤ r.toNat → r.toNat ≤ 19 → Q (r, ()) m

def fullArenaNextSpec : Spec [i64, i32] [i32] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    Q (BitVec.ofNat 32 (fullArenaNextOff s.core.arena s.core.arena_len cref.toNat), ()) m

def fullRecomputeTiersSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ sc' m', sc'.LengthsOk c →
      sc'.last_learned = s.scratch.last_learned →
      sc'.extend_len = s.scratch.extend_len →
      sc'.work_stk2 = s.scratch.work_stk2 →
      (FullMem c { s with scratch := sc' } ⋆ R) m' → Q () m'

def fullMarkReasonsSpec : Spec [i64, .bool] [] := fun (h, set_flag, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ arena' m',
      let s' : FullState := { s with core := { s.core with arena := arena' } }
      s'.LengthsOk c →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s,
        fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
        fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
        fullArenaClauseLits s' r = fullArenaClauseLits s r) →
      (set_flag = true → FullReasonsMarked s') →
      FullWitnessInv c F0 F_cur s'.core →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullSortRedsSpec : Spec [i64, i64] [] := fun (h, n, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ n.toNat ≤ c.red_cap ∧
    (∀ k < n.toNat, (s.scratch.red_refs[k]?.getD 0#32).toNat + 2 < c.arena_cap) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ sc' m', sc'.LengthsOk c →
      sc'.last_learned = s.scratch.last_learned →
      sc'.extend_len = s.scratch.extend_len →
      sc'.work_stk2 = s.scratch.work_stk2 →
      (∀ k < n.toNat, ∃ j < n.toNat, sc'.red_refs[k]? = s.scratch.red_refs[j]?) →
      (FullMem c { s with scratch := sc' } ⋆ R) m' → Q () m'

def fullBacktrackSpec : Spec [i64, i64] [] := fun (h, target_lvl, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    target_lvl.toNat ≤ s.core.cur_level ∧ (FullMem c s ⋆ R) m ∧
    ∀ vals' lvl' rsns' trl' tp' te' prop' unass' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with
            vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
            trail_end := te', propagated := prop', cur_level := target_lvl.toNat,
            unassigned := unass' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      sc'.last_learned = s.scratch.last_learned →
      sc'.extend_len = s.scratch.extend_len →
      sc'.work_stk2 = s.scratch.work_stk2 →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullPropagateSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullArenaVarsNodup s ∧ s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
            unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
            wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullArenaVarsNodup s' →
      (∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s') →
      sc'.last_learned = s.scratch.last_learned →
      sc'.extend_len = s.scratch.extend_len →
      sc'.work_stk2 = s.scratch.work_stk2 →
      s.core.trail_end ≤ te' → fuel'.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → s.core.oom = 0#64 → oom' = 0#64) →
      (r = 1#64 → FullConflictInv c F0 F_cur s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullSweepBinsSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wlen' nb' wsort' m',
      let s' : FullState :=
        { s with
          core := { s.core with
            wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64, num_binary := nb' }
          scratch := { s.scratch with wsort := wsort' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      DenseWatchesInv F_cur s'.core →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullWatchPushSpec : Spec [i64, i32, i32, i32, i32] [.bool] :=
  fun (h, lit, w0, w1, cnt, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧
      (cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32) ∧
      (cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) wvec' wstk' wlen' wu' wsort' m',
        let s' : FullState :=
          { s with
            core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
            scratch := { s.scratch with wsort := wsort' } }
        s'.LengthsOk c → WatchStackLayout s'.core →
        (∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
          fullWatchSize s' l = fullWatchSize s l ∧
          ∀ k < fullWatchSize s l,
            s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
        (ok = true →
          lit.toNat < 2 * s.core.cur_vars ∧ (cnt.toNat = 1 ∨ cnt.toNat = 2) ∧
          fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat + cnt.toNat ∧
          (∀ k < fullWatchSize s lit.toNat,
            s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
              s.core.wstk[fullWatchOff s lit.toNat + k]?) ∧
          s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat]? = some w0 ∧
          (cnt.toNat = 2 →
            s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat + 1]? =
              some w1)) →
        (ok = false →
          lit.toNat < 2 * s.core.cur_vars →
          fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat ∧
          ∀ k < fullWatchSize s lit.toNat,
            s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
              s.core.wstk[fullWatchOff s lit.toNat + k]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullArenaSweepSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullArenaVarsNodup s ∧ s.core.dense_mode = 0#64 ∧
    (0 < s.core.cur_level → FullReasonsMarked s) ∧ (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen' wu'
      fred' ni' nr' nb' oom' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
            wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
            wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
            num_redundant := nr', num_binary := nb', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullArenaVarsNodup s' → FullLastLearnedWf s' →
      sc'.extend_len = s.scratch.extend_len →
      sc'.work_stk2 = s.scratch.work_stk2 →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 3#64) →
      (r = 0#64 ∨ r = 1#64 → oom' = 0#64) →
      (0 < s.core.cur_level →
        r ≠ 1#64 ∧ r ≠ 2#64 ∧
        vals' = s.core.vals ∧ lvl' = s.core.lvl ∧ trl' = s.core.trl ∧
        tp' = s.core.trail_pos ∧ te' = s.core.trail_end) →
      (r = 1#64 → s.core.cur_level = 0 ∧ s.core.trail_end < te') →
      (r = 2#64 → s.core.cur_level = 0 ∧ F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ### Owned contracts (`full_reduce`, `full_enter_dense`, `full_rebuild_watches`) -/

def fullReduceSpec : Spec [i64, .bool] [i64] := fun (h, _force, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
    s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullSparseInv c F0 s' →
      FullWitnessInv c F0 F_cur s'.core →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64) →
      s'.core.cur_level ≤ s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.cur_vars = s.core.cur_vars →
      s'.core.tmp = s.core.tmp →
      s'.core.tmp_len = s.core.tmp_len →
      s'.core.frame_trail = s.core.frame_trail →
      s'.core.frame_dec = s.core.frame_dec →
      s'.core.inconsistent = s.core.inconsistent →
      s'.core.d_cur = s.core.d_cur →
      s'.core.d_val = s.core.d_val →
      s'.scratch.extend_len = s.scratch.extend_len →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (0 < s'.core.cur_level →
        s'.core.cur_level = s.core.cur_level ∧ s'.core.vals = s.core.vals ∧
        s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
        s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullEnterDenseSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c →
      FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' →
      FullArenaVarsNodup s' →
      FullExtScratchOk c s' →
      s'.core.cur_level = 0 →
      s'.core.fuel = s.core.fuel →
      s'.core.cur_vars = s.core.cur_vars →
      s'.core.inconsistent = s.core.inconsistent →
      s'.core.d_cur = s.core.d_cur →
      s'.core.d_val = s.core.d_val →
      s'.scratch.extend_len = s.scratch.extend_len →
      (ok = true → FullDenseInv c F0 s') →
      (ok = false → FullSparseInv c F0 s') →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullRebuildWatchesSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
    s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullSparseInv c F0 s' →
      FullWitnessInv c F0 F_cur s'.core →
      s'.core.cur_level = 0 →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.cur_vars = s.core.cur_vars →
      s'.core.inconsistent = s.core.inconsistent →
      s'.core.d_cur = s.core.d_cur →
      s'.core.d_val = s.core.d_val →
      s'.scratch.extend_len = s.scratch.extend_len →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

end FullDenseWatchSpecs

open FullDenseWatchSpecs

namespace FullDenseWatchHelpers

/-! ## 2. BitVec, mode-watch, and `DenseWatchSliceOk` lemmas -/

theorem bv32_used_upd_bits (hdr : BitVec 32) (u : BitVec 32) :
    let h' := (hdr &&& 0x07FFFFFF#32) ||| (u <<< (27 : Nat))
    (h' &&& 0x00080000#32) = (hdr &&& 0x00080000#32) ∧
    (h' &&& 0x00200000#32) = (hdr &&& 0x00200000#32) ∧
    (h' &&& 0x00800000#32) = (hdr &&& 0x00800000#32) := by
  intro h'
  have hmask : ∀ mask : BitVec 32,
      (mask &&& 0x07FFFFFF#32) = mask → (mask &&& 0xF8000000#32) = 0#32 →
      (h' &&& mask) = (hdr &&& mask) := fun mask hm1 hm2 => by
    ext i hi
    simp only [h', BitVec.getElem_and, BitVec.getElem_or]
    have h1 := congrArg (·[i]) hm1
    have h2 := congrArg (·[i]) hm2
    simp only [BitVec.getElem_and, BitVec.getElem_zero] at h1 h2
    by_cases hmi : mask[i] = true
    · rw [hmi, Bool.true_and] at h1 h2
      rw [hmi, Bool.and_true, Bool.and_true]
      have hlt : i < 27 := Classical.byContradiction fun hge => by
        have hhi : (0xF8000000#32 : BitVec 32)[i] = true := by
          rw [BitVec.getElem_eq_testBit_toNat]
          have : i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
          rcases this with rfl | rfl | rfl | rfl | rfl <;> decide
        rw [hhi] at h2; cases h2
      have hsh : (u <<< (27 : Nat))[i] = false := by
        simp [BitVec.getElem_shiftLeft, hlt]
      rw [h1, Bool.and_true, hsh, Bool.or_false]
    · simp [hmi]
  exact ⟨hmask 0x00080000#32 (by decide) (by decide),
    hmask 0x00200000#32 (by decide) (by decide),
    hmask 0x00800000#32 (by decide) (by decide)⟩

theorem bv32_or_garb_bits (hdr : BitVec 32) :
    let h' := hdr ||| 0x00080000#32
    (h' &&& 0x00080000#32) ≠ 0#32 ∧
    (h' &&& 0x00200000#32) = (hdr &&& 0x00200000#32) ∧
    (h' &&& 0x00800000#32) = (hdr &&& 0x00800000#32) := by
  intro h'
  have h19 : (h' &&& 0x00080000#32) ≠ 0#32 := by
    intro h0; have := congrArg (·[19]) h0
    revert this; simp [h', show (0x00080000#32)[19] = true from rfl]
  have hdisj : ∀ mask : BitVec 32, (0x00080000#32 &&& mask) = 0#32 →
      (h' &&& mask) = (hdr &&& mask) := fun mask hm => by
    ext i hi
    have hi0 := congrArg (·[i]) hm
    simp only [BitVec.getElem_and, BitVec.getElem_zero] at hi0
    simp only [h', BitVec.getElem_and, BitVec.getElem_or]
    rw [Bool.and_or_distrib_right, hi0, Bool.or_false]
  exact ⟨h19, hdisj 0x00200000#32 (by decide), hdisj 0x00800000#32 (by decide)⟩

theorem bv32_and_garb_red_eq_zero {hdr : BitVec 32}
    (h : (hdr &&& 0x00480000#32) = 0#32) : (hdr &&& 0x00080000#32) = 0#32 := by
  ext i hi
  have hi0 := congrArg (·[i]) h
  simp only [BitVec.getElem_and, BitVec.getElem_zero] at hi0 ⊢
  by_cases h19 : i = 19
  · subst h19
    have h48 : (0x00480000#32 : BitVec 32).toNat.testBit 19 = true := by decide
    have h08 : (0x00080000#32 : BitVec 32).toNat.testBit 19 = true := by decide
    rw [BitVec.getElem_eq_testBit_toNat, BitVec.getElem_eq_testBit_toNat, h48, Bool.and_true] at hi0
    rw [BitVec.getElem_eq_testBit_toNat, BitVec.getElem_eq_testBit_toNat, h08, Bool.and_true]
    exact hi0
  · have hz : (0x00080000#32 : BitVec 32)[i] = false := by
      have hmask : (0x00080000#32).toNat = 2 ^ 19 := by decide
      rw [BitVec.getElem_eq_testBit_toNat, hmask, Nat.testBit_two_pow]
      simp [Ne.symm h19]
    rw [hz, Bool.and_false]

theorem bv32_mask_7fffffff_props {sz : BitVec 32} (hge : 3 ≤ sz.toNat) (hlt : sz.toNat < 2 ^ 31) :
    ((sz &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 ∧
    (sz &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 ∧
    3 ≤ (sz &&& 0x7FFFFFFF#32).toNat := by
  have hbit : ((sz &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 := by
    rw [BitVec.and_assoc, show (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 by decide,
      BitVec.and_zero]
  have hne : (sz &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 := by
    intro heq; rw [heq] at hbit; revert hbit; decide
  have hto : (sz &&& 0x7FFFFFFF#32).toNat = sz.toNat := by
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]
  exact ⟨hbit, hne, by omega⟩

theorem denseWatchSliceOk_toWatchSliceOk {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : DenseWatchSliceOk F_cur k lit p rem) :
    WatchSliceOk F_cur k lit p rem := by
  induction h with
  | empty => exact .empty
  | bin h1 h2 h3 h4 h5 _ ih => exact .bin h1 h2 h3 h4 h5 ih
  | occ h1 h2 h3 _ h5 h6 _ ih => exact .large h1 h2 h3 h5 h6 ih

theorem denseWatchesInv_toWatchesInv {F_cur : List (List Nat)} {k : FullCoreState}
    (h : DenseWatchesInv F_cur k) : WatchesInv F_cur k :=
  ⟨h.layout, fun l hl => denseWatchSliceOk_toWatchSliceOk (h.slices l hl)⟩

theorem denseWatchSliceOk_relocate {F0 F1 : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hF : (cnfOfClauses F1).Entails (cnfOfClauses F0))
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ i < rem, k'.wstk[p' + i]? = k.wstk[p + i]?)
    (h : DenseWatchSliceOk F0 k lit p rem) : DenseWatchSliceOk F1 k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hflag hne (by omega)
      (CNF.entails_clause_trans hF hent)
      (ih (p' := p' + 1) fun i hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (i + 1) (by omega))
  | @occ p rem w0 cref hp hp1 hflag hsz hlt href _ ih =>
    refine .occ (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hflag hsz hlt (hsub _ href)
      (ih (p' := p' + 2) fun i hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (i + 2) (by omega))

theorem denseWatchSliceOk_append_occ {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 cref : BitVec 32}
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ i < rem, k'.wstk[p' + i]? = k.wstk[p + i]?)
    (h : DenseWatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0) (hw1 : k'.wstk[p' + rem + 1]? = some cref)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hsz : 3 ≤ w0.toNat)
    (hlt : cref.toNat < 0x80000000) (href : cref.toNat ∈ fullArenaClauseRefsCore k') :
    DenseWatchSliceOk F_cur k' lit p' (rem + 2) := by
  induction h generalizing p' with
  | empty => exact .occ (by simpa using hw0) (by simpa using hw1) hflag hsz hlt href .empty
  | @bin p rem w hp hf hne hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hne (by omega) he ?_
    exact ih (p' := p' + 1)
      (fun i hi => by simpa [show p' + 1 + i = p' + (i + 1) by omega,
        show p + 1 + i = p + (i + 1) by omega] using hwstk (i + 1) (by omega))
      (by simpa [show p' + 1 + rem = p' + (rem + 1) by omega] using hw0)
      (by simpa [show p' + 1 + rem + 1 = p' + (rem + 1) + 1 by omega] using hw1)
  | @occ p rem w cr hp hp1 hf hs hl hr _ ih =>
    refine .occ (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hs hl (hsub _ hr) ?_
    exact ih (p' := p' + 2)
      (fun i hi => by simpa [show p' + 2 + i = p' + (i + 2) by omega,
        show p + 2 + i = p + (i + 2) by omega] using hwstk (i + 2) (by omega))
      (by simpa [show p' + 2 + rem = p' + (rem + 2) by omega] using hw0)
      (by simpa [show p' + 2 + rem + 1 = p' + (rem + 2) + 1 by omega] using hw1)

theorem fullWatchPush_preserves_denseWatchesInv {F_cur : List (List Nat)} {s s' : FullState}
    {lit w0 w1 : BitVec 32} {ok : Bool}
    (hw : DenseWatchesInv F_cur s.core) (hlay : WatchStackLayout s'.core)
    (hvars : s'.core.cur_vars = s.core.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore s.core, r ∈ fullArenaClauseRefsCore s'.core)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hsz : 3 ≤ w0.toNat)
    (hlt : w1.toNat < 0x80000000) (href : w1.toNat ∈ fullArenaClauseRefsCore s'.core)
    (hother : ∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
      fullWatchSize s' l = fullWatchSize s l ∧
      ∀ i < fullWatchSize s l,
        s'.core.wstk[fullWatchOff s' l + i]? = s.core.wstk[fullWatchOff s l + i]?)
    (hok_true : ok = true →
      lit.toNat < 2 * s.core.cur_vars ∧
      fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat + 2 ∧
      (∀ i < fullWatchSize s lit.toNat,
        s'.core.wstk[fullWatchOff s' lit.toNat + i]? =
          s.core.wstk[fullWatchOff s lit.toNat + i]?) ∧
      s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat]? = some w0 ∧
      s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat + 1]? = some w1)
    (hok_false : ok = false → lit.toNat < 2 * s.core.cur_vars →
      fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat ∧
      ∀ i < fullWatchSize s lit.toNat,
        s'.core.wstk[fullWatchOff s' lit.toNat + i]? =
          s.core.wstk[fullWatchOff s lit.toNat + i]?) :
    DenseWatchesInv F_cur s'.core := by
  refine ⟨hlay, fun l hl => ?_⟩
  have hl0 : l < 2 * s.core.cur_vars := hvars ▸ hl
  have hent_refl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  by_cases hle : l = lit.toNat
  · subst hle
    cases ok with
    | false =>
      obtain ⟨hs, hslice⟩ := hok_false rfl hl0
      change DenseWatchSliceOk F_cur s'.core lit.toNat (fullWatchOff s' lit.toNat)
        (fullWatchSize s' lit.toNat)
      rw [hs]
      exact denseWatchSliceOk_relocate hent_refl (by omega) hsub hslice (hw.slices _ hl0)
    | true =>
      obtain ⟨_, hs, hpre, hw0, hw1⟩ := hok_true rfl
      change DenseWatchSliceOk F_cur s'.core lit.toNat (fullWatchOff s' lit.toNat)
        (fullWatchSize s' lit.toNat)
      rw [hs]
      exact denseWatchSliceOk_append_occ (by omega) hsub hpre (hw.slices _ hl0) hw0 hw1 hflag
        hsz hlt href
  · obtain ⟨hs, hslice⟩ := hother l hl0 hle
    change DenseWatchSliceOk F_cur s'.core l (fullWatchOff s' l) (fullWatchSize s' l)
    rw [hs]
    exact denseWatchSliceOk_relocate hent_refl (by omega) hsub hslice (hw.slices l hl0)

/-! ## 3. Arena block-chain stepping and header-update preservation lemmas -/

theorem fullArenaScanRefs_next_mem {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos r : Nat}, alen - pos ≤ fuel →
      r ∈ fullArenaScanRefs ar alen pos fuel →
      (∀ x ∈ fullArenaScanRefs ar alen pos fuel,
        fullArenaNextOff ar alen x = alen ∨ fullArenaNextOff ar alen x + 3 ≤ alen) →
      fullArenaNextOff ar alen r = alen ∨
        fullArenaNextOff ar alen r ∈ fullArenaScanRefs ar alen pos fuel
  | 0, _, _, _, hr, _ => by simp [fullArenaScanRefs] at hr
  | fuel + 1, pos, r, hfl, hr, hchain => by
    unfold fullArenaScanRefs at hr hchain ⊢; split at hr
    · rename_i hle
      simp only [hle, ↓reduceIte, List.mem_cons] at hr hchain ⊢
      have hb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      rcases hr with rfl | hrest
      · rcases hchain r (Or.inl rfl) with hend | hmore
        · exact Or.inl hend
        · right; right
          cases fuel with
          | zero => omega
          | succ f' => unfold fullArenaScanRefs; simp [hmore]
      · rcases fullArenaScanRefs_next_mem (fuel := fuel) (pos := fullArenaNextOff ar alen pos)
            (r := r) (by omega) hrest (fun x hx => hchain x (Or.inr hx)) with hend | hmem
        · exact Or.inl hend
        · exact Or.inr (Or.inr hmem)
    · simp at hr

theorem fullArenaClauseRefs_zero_mem {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (ha : FullArenaClausesInv c F_cur k) (hpos : 0 < k.arena_len) :
    0 ∈ fullArenaClauseRefsCore k := by
  have h3 : 3 ≤ k.arena_len := ha.len_ok.resolve_left (by omega)
  unfold fullArenaClauseRefsCore
  cases h : k.arena_len with
  | zero => omega
  | succ f => unfold fullArenaScanRefs; simp [← h, h3]

theorem fullArenaClauseRefs_next_mem {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (ha : FullArenaClausesInv c F_cur k) {r : Nat} (hr : r ∈ fullArenaClauseRefsCore k) :
    fullArenaNextOff k.arena k.arena_len r = k.arena_len ∨
      fullArenaNextOff k.arena k.arena_len r ∈ fullArenaClauseRefsCore k :=
  fullArenaScanRefs_next_mem (by omega) hr fun x hx => (ha.refs_wf x hx).2.2.2.2

/-- Updating bits `27..31` (the `used` counter) of `arena[cref]` preserves `fullArenaClauseRefs`,
all clause sizes/garbage/literals, `FullWitnessInv`, `FullArenaVarsNodup`, and
`FullReasonsMarked`. -/
theorem updateUsed_preserves_fullWitnessInv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (u : BitVec 32) :
    let v' := (fullArenaHdr s cref &&& 0x07FFFFFF#32) ||| (u <<< (27 : Nat))
    let s' : FullState := { s with core := { s.core with arena := s.core.arena.set cref v' } }
    s'.LengthsOk c ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r ∧
      (fullArenaHdr s' r &&& 0x00200000#32) = (fullArenaHdr s r &&& 0x00200000#32)) ∧
    FullWitnessInv c F0 F_cur s'.core := by
  intro v' s'
  have hcl := hlen.core_ok
  have hcref_wf := hw.arena.refs_wf cref href
  have har_len : cref < s.core.arena.length := by
    have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
  have hget_cref : s.core.arena[cref]? = some (fullArenaHdr s cref) := by
    unfold fullArenaHdr fullArenaHdrCore
    rw [List.getElem?_eq_getElem har_len, Option.getD_some]
  have ha_cref : s'.core.arena[cref]? = some v' := List.getElem?_set_self har_len
  have hbits := bv32_used_upd_bits (fullArenaHdr s cref) u
  have hne_outside : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len r ≤ cref) ∨
      (cref + 3 ≤ fullArenaNextOff s.core.arena s.core.arena_len cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len cref ≤ r) := by
    intro r hr hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨by have := fullArenaScanRefs_disjoint hr href hlt
                       have := (hw.arena.refs_wf r hr).2.2.1; omega,
        fullArenaScanRefs_disjoint hr href hlt⟩
    · exact Or.inr ⟨by omega, fullArenaScanRefs_disjoint href hr hgt⟩
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff s'.core.arena s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r
      have h2eq : s'.core.arena[cref + 2]? = s.core.arena[cref + 2]? :=
        List.getElem?_set_ne (by omega)
      have h1 : ¬ (cref + 3 > s.core.arena_len) := by omega
      have h2 : ¬ (cref + 3 + (s.core.arena[cref + 2]?.getD 0#32).toNat > s.core.arena_len) := by
        unfold fullArenaClauseSizeCore at hcref_wf; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2, ha_cref, Option.getD_some]
      rw [hbits.2.2, show fullArenaHdr s cref = s.core.arena[cref]?.getD 0#32 from rfl]
      split
      · exact fullArenaSkipShrk_congr fun i hi _ => List.getElem?_set_ne (by omega)
      · rfl
    · refine fullArenaNextOff_congr_block (List.getElem?_set_ne (Ne.symm hrc)) ?_ ?_
      · rcases hne_outside r hr hrc with ⟨hlt, _⟩ | ⟨h3, hgt⟩
        · have := (hw.arena.refs_wf r hr).2.1; exact List.getElem?_set_ne (by omega)
        · exact List.getElem?_set_ne (by omega)
      · intro i hi1 _
        rcases hne_outside r hr hrc with ⟨_, hle⟩ | ⟨h3, hgt⟩
        · exact List.getElem?_set_ne (by omega)
        · have := (hw.arena.refs_wf r hr).2.2.1; exact List.getElem?_set_ne (by omega)
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hper : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r ∧
      (fullArenaHdrCore s'.core r &&& 0x00200000#32) =
        (fullArenaHdrCore s.core r &&& 0x00200000#32) := by
    intro r hr
    have hwf := hw.arena.refs_wf r hr
    have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
    by_cases hrc : r = cref
    · subst r
      have hsz : fullArenaClauseSizeCore s'.core cref = fullArenaClauseSizeCore s.core cref := by
        unfold fullArenaClauseSizeCore; dsimp only [s']
        rw [List.getElem?_set_ne (by omega)]
      have hlits : fullArenaClauseLitsCore s'.core cref = fullArenaClauseLitsCore s.core cref :=
        fullArenaClauseLitsCore_eq_of_hold hbd (by simp [s', hbd]) hsz fun j hj =>
          List.getElem?_set_ne (by omega)
      have hgarb : fullArenaClauseGarbCore s'.core cref = fullArenaClauseGarbCore s.core cref := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore
        dsimp only [s']; rw [List.getElem?_set_self har_len, Option.getD_some, hbits.1]
        rfl
      have hrsn : (fullArenaHdrCore s'.core cref &&& 0x00200000#32) =
          (fullArenaHdrCore s.core cref &&& 0x00200000#32) := by
        unfold fullArenaHdrCore; dsimp only [s']
        rw [List.getElem?_set_self har_len, Option.getD_some]; exact hbits.2.1
      exact ⟨hsz, hgarb, hlits, hrsn⟩
    · have hout : r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∨ cref + 3 ≤ r := by
        rcases hne_outside r hr hrc with ⟨h1, _⟩ | ⟨h3, h2⟩ <;> omega
      have hlo := fullArenaClauseLitsCore_set_outside (v := v') hbd hout
      have hhdr : fullArenaHdrCore s'.core r = fullArenaHdrCore s.core r := by
        unfold fullArenaHdrCore; dsimp only [s']
        rw [List.getElem?_set_ne (Ne.symm hrc)]
      have hgarb : fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := by
        unfold fullArenaClauseGarbCore
        exact congrArg (fun x => (x &&& 0x00080000#32) != 0#32) hhdr
      exact ⟨hlo.1, hgarb, hlo.2, by rw [hhdr]⟩
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with arena_len_arr := by simp [s', hcl.arena_len_arr] }, hlen.scratch_ok⟩
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := hw.arena.refs_wf r hr
      dsimp only [s'] at hnxt ⊢; rw [hnxt r hr, (hper r hr).1]; exact hwf
    · intro r hr hsh; rw [hrefs] at hr
      have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
        by_cases hrc : r = cref
        · subst r; unfold fullArenaHdrCore at hsh ⊢
          rw [ha_cref, Option.getD_some] at hsh
          rw [hget_cref, Option.getD_some]
          have hb3 : (v' &&& 0x00800000#32) = (fullArenaHdr s cref &&& 0x00800000#32) := hbits.2.2
          rwa [hb3] at hsh
        · unfold fullArenaHdrCore at hsh ⊢
          simpa [s', List.getElem?_set_ne (Ne.symm hrc)] using hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
      have hget_r : s.core.arena[r]? = some (fullArenaHdrCore s.core r) := by
        have hr3 := (hw.arena.refs_wf r hr).1
        have : r < s.core.arena.length := by
          have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      have hsh_ar : (s.core.arena[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
        rw [hget_r, Option.getD_some]; exact hsh0
      obtain ⟨t0, ht0_lo, _, ht0_nxt, ht0_sent⟩ :=
        fullArenaNextOff_hits_sentinel (hw.arena.refs_wf r hr).1 hsh_ar ht1 ht2 hsent
      have ht0_ne : t0 ≠ cref := by
        by_cases hrc : r = cref
        · subst r; have := (hw.arena.refs_wf cref hr).2.1; omega
        · rcases hne_outside r hr hrc with ⟨_, hle⟩ | ⟨h3, hgt⟩
          · omega
          · have := (hw.arena.refs_wf r hr).2.1; omega
      have hnxt_le := (hw.arena.refs_wf r hr).2.2.2.1
      refine ⟨t0, by rw [(hper r hr).1]; exact ht0_lo, by dsimp only [s']; omega, ?_⟩
      dsimp only [s']; rw [List.getElem?_set_ne ht0_ne.symm]; exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [(hper r hr).2.1] at hng; rw [(hper r hr).2.2.1] at hl
      exact hw.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      rw [(hper r hr).2.1] at hng; rw [(hper r hr).2.2.1]
      exact hw.arena.entails r hr hng
  refine ⟨hlen', hrefs, hper, { hw with
    arena := harena'
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
    reason_inv := fun idx hidx hne => by
      have hrs := hw.reason_inv idx hidx hne
      rw [show s'.core.trl = s.core.trl from rfl, show s'.core.rsns = s.core.rsns from rfl,
        show s'.core.cur_vars = s.core.cur_vars from rfl, show s'.core.lvl = s.core.lvl from rfl]
      by_cases hb : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hb] at hrs ⊢; exact hrs
      · rw [ite_eq_right hb] at hrs ⊢
        have hp := hper _ hrs.1
        exact ⟨hrefs ▸ hrs.1, hp.2.1.trans hrs.2.1, fun q hq => hrs.2.2 q (hp.2.2.1 ▸ hq)⟩
    reason_lit_mem := fun idx hidx hne hlg => by
      have hrs := hw.reason_inv idx hidx hne
      have hb : ¬ (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
      rw [ite_eq_right hb] at hrs
      rw [show s'.core.trl = s.core.trl from rfl, show s'.core.rsns = s.core.rsns from rfl]
      exact (hper _ hrs.1).2.2.1 ▸ hw.reason_lit_mem idx hidx hne hlg }⟩

/-- `FullReasonsMarked` + `(fullArenaHdr s cref &&& PH_RSN) = 0` implies `cref` is not an active
trail reason (for any `cur_level ≥ 0`). -/
theorem markGarb_nonact_of_reasonsMarked {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hrm : FullReasonsMarked s)
    {cref : Nat} (hno : (fullArenaHdr s cref &&& 0x00200000#32) = 0#32) :
    ∀ idx < s.core.trail_end,
      let rsn := s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cref := by
  intro idx hidx rsn hne hlg heq
  have hlpos : 0 < (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat :=
    Classical.byContradiction fun h0 => hne (hw.level0_rsn_none idx hidx (by omega))
  have hmarked := hrm idx hidx hlpos hlg
  rw [heq] at hmarked; exact hmarked hno

/-- Setting `PH_GARB` on non-active `cref` preserves `FullWitnessInv` (for the SAME `F_cur`),
`fullArenaClauseRefs`, `FullArenaVarsNodup`, `FullReasonsMarked`, and `PH_RSN` bits on all refs. -/
theorem markGarb_preserves_fullWitnessInv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (ag' : BitVec 64)
    (hnonact : ∀ idx < s.core.trail_end,
      let rsn := s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cref) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    s'.LengthsOk c ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    FullWitnessInv c F0 F_cur s'.core ∧
    (∀ r ∈ fullArenaClauseRefs s,
      (fullArenaHdr s' r &&& 0x00200000#32) = (fullArenaHdr s r &&& 0x00200000#32)) ∧
    (FullArenaVarsNodup s → FullArenaVarsNodup s') := by
  intro s'
  have hcl := hlen.core_ok
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with arena_len_arr := by simp [s', hcl.arena_len_arr] }, hlen.scratch_ok⟩
  have hmg := hw.arena.markGarb hcl href ag'
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core := hmg.1
  have har_len : cref < s.core.arena.length := by
    have := (hw.arena.refs_wf cref href).1
    have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
  have hdisj_lits : ∀ {r : Nat}, r ∈ fullArenaClauseRefsCore s.core → r ≠ cref →
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun {r} hr hne => by
    have hdisj : r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∨ cref + 3 ≤ r := by
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl (hw.arena.disjoint hr href hlt)
      · exact Or.inr (by have := hw.arena.disjoint href hr hgt; omega)
    have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have := (hw.arena.refs_wf r hr).2.2.1; have := (hw.arena.refs_wf r hr).2.2.2.1
      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
    exact (fullArenaClauseLitsCore_set_outside hbd hdisj).2
  have hbits := bv32_or_garb_bits (fullArenaHdr s cref)
  have hrsn_eq : ∀ r ∈ fullArenaClauseRefs s,
      (fullArenaHdr s' r &&& 0x00200000#32) = (fullArenaHdr s r &&& 0x00200000#32) := by
    intro r _; by_cases hrc : r = cref
    · subst r; unfold fullArenaHdr fullArenaHdrCore; dsimp only [s']
      rw [List.getElem?_set_self har_len, Option.getD_some]; exact hbits.2.1
    · unfold fullArenaHdr fullArenaHdrCore; dsimp only [s']
      rw [List.getElem?_set_ne (Ne.symm hrc)]
  have hnodup : FullArenaVarsNodup s → FullArenaVarsNodup s' := by
    intro hnd r hr hng; change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs] at hr
    have hne : r ≠ cref := by
      rintro rfl; unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng
      dsimp only [s'] at hng; rw [List.getElem?_set_self har_len, Option.getD_some] at hng
      simp [hbits.1] at hng
    have hng0 : fullArenaClauseGarb s r = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢
      simpa [s', List.getElem?_set_ne (Ne.symm hne)] using hng
    rw [show fullArenaClauseLits s' r = fullArenaClauseLits s r from hdisj_lits hr hne]
    exact hnd r hr hng0
  refine ⟨hlen', hrefs, { hw with
    arena := hmg.2
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
    reason_inv := fun idx hidx hne => by
      have hrs := hw.reason_inv idx hidx hne
      rw [show s'.core.trl = s.core.trl from rfl, show s'.core.rsns = s.core.rsns from rfl,
        show s'.core.cur_vars = s.core.cur_vars from rfl, show s'.core.lvl = s.core.lvl from rfl]
      by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hbin] at hrs ⊢; exact hrs
      · have hlg' : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32 :=
          Classical.byContradiction fun hn => hbin hn
        rw [ite_eq_right hbin] at hrs ⊢
        have hne_cref := hnonact idx hidx hne hlg'
        have hgarb' : fullArenaClauseGarbCore s'.core
            (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat =
            false := by
          unfold fullArenaClauseGarbCore fullArenaHdrCore
          dsimp only [s']; rw [List.getElem?_set_ne hne_cref.symm]; exact hrs.2.1
        have hlits_eq := hdisj_lits hrs.1 hne_cref
        exact ⟨hrefs ▸ hrs.1, hgarb', fun q hq => hrs.2.2 q (hlits_eq ▸ hq)⟩
    reason_lit_mem := fun idx hidx hne hlg => by
      have hrs := hw.reason_inv idx hidx hne
      have hb : ¬ (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
      rw [ite_eq_right hb] at hrs
      rw [show s'.core.trl = s.core.trl from rfl, show s'.core.rsns = s.core.rsns from rfl]
      exact hdisj_lits hrs.1 (hnonact idx hidx hne hlg) ▸ hw.reason_lit_mem idx hidx hne hlg },
    hrsn_eq, hnodup⟩

/-! ## 4. Mode-flip, scratch/scalar preservation, and conflict UNSAT helpers -/

theorem fullWitnessInv_with_dense_mode_zero {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) :
    FullWitnessInv c F0 F_cur { k with dense_mode := 0#64 } := by
  have hwat : ModeWatchesInv F_cur { k with dense_mode := 0#64 } := by
    simp only [ModeWatchesInv, ↓reduceIte]
    have h0 := hw.watches
    by_cases hc : k.dense_mode = 0#64
    · simp only [ModeWatchesInv, hc, ↓reduceIte] at h0
      refine ⟨h0.layout.with_wstk rfl rfl rfl rfl, fun l hl => ?_⟩
      simpa [fullWatchOffCore, fullWatchSizeCore] using
        (h0.slices l hl).mono (k := k) (k' := { k with dense_mode := 0#64 })
          (by rw [CNF.entails_def]; exact fun _ p => p)
          (Nat.le_refl k.cur_vars) (fun _ r => r) (fun _ _ _ => rfl)
    · simp only [ModeWatchesInv, hc, ↓reduceIte] at h0
      have hw0 := denseWatchesInv_toWatchesInv h0
      refine ⟨hw0.layout.with_wstk rfl rfl rfl rfl, fun l hl => ?_⟩
      simpa [fullWatchOffCore, fullWatchSizeCore] using
        (hw0.slices l hl).mono (k := k) (k' := { k with dense_mode := 0#64 })
          (by rw [CNF.entails_def]; exact fun _ p => p)
          (Nat.le_refl k.cur_vars) (fun _ r => r) (fun _ _ _ => rfl)
  exact { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat }

theorem fullWitnessInv_with_dense_mode_nz {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (hd : DenseWatchesInv F_cur k) {dm : BitVec 64} (hdm : dm ≠ 0#64) :
    FullWitnessInv c F0 F_cur { k with dense_mode := dm } := by
  have hwat : ModeWatchesInv F_cur { k with dense_mode := dm } := by
    simp only [ModeWatchesInv, hdm, ↓reduceIte]
    refine ⟨hd.layout.with_wstk rfl rfl rfl rfl, fun l hl => ?_⟩
    simpa [fullWatchOffCore, fullWatchSizeCore] using
      (hd.slices l hl).mono (k := k) (k' := { k with dense_mode := dm })
        (by rw [CNF.entails_def]; exact fun _ p => p)
        (Nat.le_refl k.cur_vars) (fun _ r => r) (fun _ _ _ => rfl)
  exact { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat }

theorem fullWitnessInv_with_unflushed {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (u' : BitVec 64) :
    FullWitnessInv c F0 F_cur { k with unflushed := u' } :=
  { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
            watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

theorem fullWitnessInv_with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (o' : BitVec 64) :
    FullWitnessInv c F0 F_cur { k with oom := o' } :=
  { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
            watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

theorem fullConflictInv_level0_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hl0 : s.core.cur_level = 0)
    (hc : FullConflictInv c F0 F_cur s) : F0.Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hent, hf0, hf1⟩ | ⟨_, href, hg, hfals⟩
  · refine hw.ext_sound.2
      (unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => Or.inr ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
  · refine hw.ext_sound.2 (unsat_of_entails_nil
      (entails_of_mem_or_false (hw.arena.entails _ href hg) fun l hl => Or.inr ?_))
    obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l (hw.arena.lits_lt _ href hg l hl)).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs

end FullDenseWatchHelpers

end LeanQbe.T.Examples.Kissat.Full
