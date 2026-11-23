module

public import LeanQbe.T.Examples.Kissat.FullM6ProofUtil

/-!
# Soundness-Boundary Proof Tiering Kit for M7 Policy / Heuristic Functions (`PolicyFrame`)

Purely additive helper library (`0` edits to existing C0 or proofs). Decision heuristics,
restart / rephase / mode-switch schedules, EMA updates, `randec`, `tumble`, `luckylate`, `walk`,
`bump`, sorting, watch-reordering, and clause deletions (`reduce`) cannot falsify UNSAT soundness
as long as they preserve memory safety (`FullMem` / `FullM6HdrMem` + `LengthsOk` + disjointness)
and either leave clause/soundness state untouched (Tiers P0/P1) or never introduce unsound clauses
(`ArenaClauseSubset`, Tier P2).

Contents:
1. **Tier P0/P1 State & Frame (`PolicyCore`, `policySlice`, `PolicyStep`, `m6PolicySlice`)**:
   - `PolicyCore` isolates the `25` `FullCoreState` bookkeeping fields never read by
     `FullWitnessInv` / `FullSparseInv` / `FullDenseInv` / `FullM6HdrInv`.
   - `PolicyStep s s'` (`policyView` equality) holds whenever `s'` differs from `s` only in
     `FullScratch` (outside `last_learned`, `extend_len`) and `PolicyCore`.
   - `LengthsOk` record-update helpers + `MemSafe`/disjoint region collapse helpers.
2. **Invariant Transport Across `PolicyStep`**:
   - Preserves `FullCoreInv`, `FullInv`, `FullSparseInv`/`W`, `FullDenseInv`/`W`,
     `FullM6HdrInv`/`W`/`CoreInv`, and UNSAT soundness (`policyStep_unsat_sound`).
3. **`PolicyFrameSpec` & `M6PolicyFrameSpec` Builders + Combinators**:
   - `PolicyFrameSpec` (`SafetySlice.spec policySlice`) & `M6PolicyFrameSpec`
     (`SafetySlice.spec m6PolicySlice`), with `mono`, `noExit`, `frame`, `weaken`, and one-line
     lifts from landed `fullSafetySlice` contracts (`fullSafetyVoidSpec`, etc.).
4. **WP Composition, Policy Loops, Callee Transport & `TableImpl` Helpers**:
   - `wp_policy_call`, `wp_policy_call_safety`, `wp_policy_call_m6HdrInv`,
     `wp_policy_loop`, `wp_policy_for`, `wp_policy_loop_break`, `wp_policy_join`,
     plus `M6PolicyFrameSpec` loop/call counterparts and `SpecEntry`/`TableImpl` helpers.
5. **Tier P2 Deletion & Watch-Reordering Frame (`ArenaClauseSubset`, `PolicyDeleteSpec`)**:
   - `FullArenaLayoutOk`, `ArenaClauseSubset`, `ArenaClauseEntailed`, `WatchSliceFrame`,
     `PolicyDeleteStep`, and `PolicyDeleteSpec`, proving `FullWitnessInv`, `FullSparseInv`,
     `FullM6HdrInv`, and `F0.Unsat` preservation across clause deletions & watch reordering.

See `PolicyFrameExample.lean` for a kernel-checked working example on landed M7 policy code.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.PolicyFrame

open Std Std.Sat
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open Kraken.Bedrock2.Test

/-! ## 1. Policy-owned core fields, `PolicyStep`, `LengthsOk`, and region safety -/

/-- The `25` `FullCoreState` bookkeeping fields never read by `FullWitnessInv`, `FullSparseInv`,
`FullDenseInv`, or `FullM6HdrInv` (they are only constrained by `LengthsOk`). -/
structure PolicyCore where
  unassigned : BitVec 64
  wusable : BitVec 64
  arena_garbage : BitVec 64
  first_reducible : BitVec 64
  num_irred : BitVec 64
  num_redundant : BitVec 64
  num_binary : BitVec 64
  unflushed : BitVec 64
  probing : BitVec 64
  propagated : Nat
  fuel : BitVec 64
  confl_ref : BitVec 64
  confl_type : BitVec 64
  confl_lit0 : BitVec 64
  confl_lit1 : BitVec 64
  tmp_cnt : Nat
  tmp_len : Nat
  min_clr_len : Nat
  min_clr_full : BitVec 64
  oom : BitVec 64
  flags : List (BitVec 32)
  tmp : List (BitVec 32)
  min_clr : List (BitVec 32)
  repr : List (BitVec 32)
  min_stk : List (BitVec 32)

/-- Projection of the policy-owned fields of a core state. -/
@[expose] def policyPart (k : FullCoreState) : PolicyCore where
  unassigned := k.unassigned
  wusable := k.wusable
  arena_garbage := k.arena_garbage
  first_reducible := k.first_reducible
  num_irred := k.num_irred
  num_redundant := k.num_redundant
  num_binary := k.num_binary
  unflushed := k.unflushed
  probing := k.probing
  propagated := k.propagated
  fuel := k.fuel
  confl_ref := k.confl_ref
  confl_type := k.confl_type
  confl_lit0 := k.confl_lit0
  confl_lit1 := k.confl_lit1
  tmp_cnt := k.tmp_cnt
  tmp_len := k.tmp_len
  min_clr_len := k.min_clr_len
  min_clr_full := k.min_clr_full
  oom := k.oom
  flags := k.flags
  tmp := k.tmp
  min_clr := k.min_clr
  repr := k.repr
  min_stk := k.min_stk

/-- Overwrite exactly the policy-owned fields of `k` with `p`. -/
@[expose] def policyUpd (k : FullCoreState) (p : PolicyCore) : FullCoreState :=
  { k with
    unassigned := p.unassigned, wusable := p.wusable, arena_garbage := p.arena_garbage
    first_reducible := p.first_reducible, num_irred := p.num_irred
    num_redundant := p.num_redundant, num_binary := p.num_binary, unflushed := p.unflushed
    probing := p.probing, propagated := p.propagated, fuel := p.fuel, confl_ref := p.confl_ref
    confl_type := p.confl_type, confl_lit0 := p.confl_lit0, confl_lit1 := p.confl_lit1
    tmp_cnt := p.tmp_cnt, tmp_len := p.tmp_len, min_clr_len := p.min_clr_len
    min_clr_full := p.min_clr_full, oom := p.oom, flags := p.flags, tmp := p.tmp
    min_clr := p.min_clr, repr := p.repr, min_stk := p.min_stk }

/-- Canonical all-zero policy part. -/
@[expose] def PolicyCore.zero : PolicyCore :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, [], [], [], [], []⟩

/-- Soundness-relevant core view: policy-owned fields erased. -/
@[expose] def soundMask (k : FullCoreState) : FullCoreState := policyUpd k PolicyCore.zero

/-- Everything a policy function must leave untouched: the sound core view plus the two
soundness-adjacent scratch fields (`last_learned`, `extend_len`) of `FullExtScratchOk`. -/
abbrev PolicyView : Type := FullCoreState × List (BitVec 32) × Nat

@[expose] def policyView (s : FullState) : PolicyView :=
  (soundMask s.core, s.scratch.last_learned, s.scratch.extend_len)

/-- Policy tier `SafetySlice`: `FullMem` footprint, `policyView` frame, `LengthsOk` safety. -/
@[expose] def policySlice (c : FullCfg) : SafetySlice FullState PolicyView where
  mem := FullMem c
  coreProj := policyView
  safe := FullState.LengthsOk c

/-- `s → s'` is a pure policy step (definitionally `PreservesCoreSlice (policySlice c).coreProj`).
-/
abbrev PolicyStep (s s' : FullState) : Prop := PreservesCoreSlice policyView s s'

@[scoped simp] theorem policySlice_mem (c : FullCfg) : (policySlice c).mem = FullMem c := rfl
@[scoped simp] theorem policySlice_coreProj (c : FullCfg) :
    (policySlice c).coreProj = policyView := rfl
@[scoped simp] theorem policySlice_safe (c : FullCfg) :
    (policySlice c).safe = FullState.LengthsOk c := rfl

theorem policyUpd_policyPart (k : FullCoreState) : policyUpd k (policyPart k) = k := rfl

theorem soundMask_policyUpd (k : FullCoreState) (p : PolicyCore) :
    soundMask (policyUpd k p) = soundMask k := rfl

/-- Any core with the same sound view is a policy update of the original. -/
theorem eq_policyUpd_of_soundMask {k k' : FullCoreState} (h : soundMask k' = soundMask k) :
    k' = policyUpd k (policyPart k') :=
  calc k' = policyUpd (soundMask k') (policyPart k') := rfl
    _ = policyUpd (soundMask k) (policyPart k') := by rw [h]
    _ = policyUpd k (policyPart k') := rfl

namespace PolicyStep

theorem refl (s : FullState) : PolicyStep s s := rfl

theorem trans {s1 s2 s3 : FullState} (h1 : PolicyStep s1 s2) (h2 : PolicyStep s2 s3) :
    PolicyStep s1 s3 :=
  PreservesCoreSlice.trans h1 h2

theorem soundMask_eq {s s' : FullState} (h : PolicyStep s s') :
    soundMask s'.core = soundMask s.core :=
  congrArg Prod.fst h

theorem extPres {s s' : FullState} (h : PolicyStep s s') : FullExtScratchPres s s' :=
  ⟨congrArg (fun v : PolicyView => v.2.1) h, congrArg (fun v : PolicyView => v.2.2) h⟩

theorem core_eq_policyUpd {s s' : FullState} (h : PolicyStep s s') :
    s'.core = policyUpd s.core (policyPart s'.core) :=
  eq_policyUpd_of_soundMask h.soundMask_eq

/-- Every `PolicyStep` is (up to scratch) a `policyUpd` of the source core. -/
theorem state_eq {s s' : FullState} (h : PolicyStep s s') :
    s' = { core := policyUpd s.core (policyPart s'.core), scratch := s'.scratch } := by
  have hc := h.core_eq_policyUpd
  cases s' with
  | mk k sc => simp only at hc; rw [← hc]

/-- P0 → P1: any `fullSafetySlice` step with `FullExtScratchPres` is a policy step. -/
theorem of_core_eq {s s' : FullState} (hc : s'.core = s.core) (hx : FullExtScratchPres s s') :
    PolicyStep s s' := by
  unfold PolicyStep PreservesCoreSlice policyView
  rw [hc, hx.1, hx.2]

theorem of_safety {c : FullCfg} {s s' : FullState}
    (hc : PreservesCoreSlice (fullSafetySlice c).coreProj s s') (hx : FullExtScratchPres s s') :
    PolicyStep s s' :=
  of_core_eq hc hx

/-- Updating scratch outside `last_learned` / `extend_len` is a policy step. -/
theorem with_scratch {s0 s : FullState} (h : PolicyStep s0 s) {sc' : FullScratch}
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hel : sc'.extend_len = s.scratch.extend_len) :
    PolicyStep s0 { s with scratch := sc' } :=
  h.trans (of_core_eq rfl ⟨hll, hel⟩)

/-- Updating policy-owned core fields is a policy step. -/
theorem with_policyUpd {s0 s : FullState} (h : PolicyStep s0 s) (p : PolicyCore) :
    PolicyStep s0 { s with core := policyUpd s.core p } :=
  h.trans rfl

end PolicyStep

/-- Opaque `FullCoreState.LengthsOk` update for policy-owned array mutations (`flags`, `tmp`,
`min_clr`, `repr`, `min_stk`), avoiding unfolding unrelated fields. -/
theorem fullCore_lengthsOk_of_policyUpd {c : FullCfg} {k : FullCoreState}
    (h : k.LengthsOk c) {p : PolicyCore}
    (hfl : p.flags.length = k.flags.length)
    (htmp : p.tmp.length = k.tmp.length)
    (hmc : p.min_clr.length = k.min_clr.length)
    (hrep : p.repr.length = k.repr.length)
    (hmst : p.min_stk.length = k.min_stk.length)
    (hprop : p.propagated ≤ k.trail_end)
    (htl : p.tmp_len ≤ c.max_vars)
    (hmcl : p.min_clr_len ≤ c.max_vars) :
    (policyUpd k p).LengthsOk c :=
  { vals_len := h.vals_len
    lit_mark_len := h.lit_mark_len
    mrk_len := h.mrk_len
    flags_len := hfl.trans h.flags_len
    lvl_len := h.lvl_len
    rsns_len := h.rsns_len
    trl_len := h.trl_len
    trail_pos_len := h.trail_pos_len
    tmp_len_arr := htmp.trans h.tmp_len_arr
    min_clr_len_arr := hmc.trans h.min_clr_len_arr
    frame_trail_len := h.frame_trail_len
    frame_dec_len := h.frame_dec_len
    wvec_len := h.wvec_len
    repr_len := hrep.trans h.repr_len
    min_stk_len := hmst.trans h.min_stk_len
    arena_len_arr := h.arena_len_arr
    wstk_len_arr := h.wstk_len_arr
    cur_vars_ge := h.cur_vars_ge
    cur_vars_le := h.cur_vars_le
    arena_len_le := h.arena_len_le
    wlen_le := h.wlen_le
    trail_end_le := h.trail_end_le
    propagated_le := hprop
    tmp_len_le := htl
    min_clr_len_le := hmcl }

/-- Collapse `FullMem c s ⋆ R` to the single disjoint workspace region `region c.hdr c.avail ⋆ R`.
-/
theorem fullMem_to_region_frame {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m) :
    (region c.hdr c.avail ⋆ R) m :=
  sep_mono (fun _ hf => FullArenaInv.to_region ⟨hlen, hf⟩) hm

/-- Collapse `FullM6HdrMem c ext s ⋆ R` to the contiguous workspace region
`region (m6ExtAddr c.hdr) (fullM6ExtBytes + c.avail) ⋆ R`. -/
theorem m6HdrMem_to_region_frame {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext)
    (hlen : s.LengthsOk c) (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    (region (m6ExtAddr c.hdr) (fullM6ExtBytes + c.avail) ⋆ R) m :=
  sep_mono (fun _ hf => fullM6HdrMem_to_region hcfg hext hlen hf) hm

/-! ## 2. Invariant transport across `PolicyStep` (UNSAT soundness preserved verbatim) -/

/-- `FullWitnessInv` never reads policy-owned fields. -/
theorem fullWitnessInv_policyUpd {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (p : PolicyCore) :
    FullWitnessInv c F0 F_cur (policyUpd k p) :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem fullWitnessInv_of_soundMask {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k k' : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (h : soundMask k' = soundMask k) :
    FullWitnessInv c F0 F_cur k' := by
  rw [eq_policyUpd_of_soundMask h]; exact fullWitnessInv_policyUpd hw _

theorem fullCoreInv_of_policyStep {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullCoreInv c F0 s) (hlen : s'.LengthsOk c) (hp : PolicyStep s s') :
    FullCoreInv c F0 s' :=
  let ⟨F_cur, hw⟩ := h.witness
  ⟨hlen, F_cur, fullWitnessInv_of_soundMask hw hp.soundMask_eq⟩

theorem fullInv_of_policyStep {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullInv c F0 s) (hlen : s'.LengthsOk c) (hp : PolicyStep s s') : FullInv c F0 s' := by
  refine ⟨fullCoreInv_of_policyStep h.core hlen hp, ?_⟩
  rw [hp.state_eq]; exact h.marks

theorem fullLitMarksClear_of_policyStep {c : FullCfg} {s s' : FullState}
    (h : FullLitMarksClear c s) (hp : PolicyStep s s') : FullLitMarksClear c s' := by
  rw [hp.state_eq]; exact h

theorem fullArenaVarsNodup_of_policyStep {s s' : FullState}
    (h : FullArenaVarsNodup s) (hp : PolicyStep s s') : FullArenaVarsNodup s' := by
  rw [hp.state_eq]; exact h

theorem fullArenaClauseRefs_of_policyStep {s s' : FullState} (hp : PolicyStep s s') :
    fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  rw [hp.state_eq]; rfl

theorem dense_mode_of_policyStep {s s' : FullState} (hp : PolicyStep s s') :
    s'.core.dense_mode = s.core.dense_mode := by
  rw [hp.state_eq]; rfl

theorem cur_level_of_policyStep {s s' : FullState} (hp : PolicyStep s s') :
    s'.core.cur_level = s.core.cur_level := by
  rw [hp.state_eq]; rfl

theorem inconsistent_of_policyStep {s s' : FullState} (hp : PolicyStep s s') :
    s'.core.inconsistent = s.core.inconsistent := by
  rw [hp.state_eq]; rfl

theorem fullExtScratchOk_of_policyStep {c : FullCfg} {s s' : FullState}
    (h : FullExtScratchOk c s) (hp : PolicyStep s s') : FullExtScratchOk c s' :=
  FullExtScratchOk.of_pres h hp.extPres
    (fun _ hr => (fullArenaClauseRefs_of_policyStep hp).symm ▸ hr)

theorem fullSparseInv_of_policyStep {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullSparseInv c F0 s) (hlen : s'.LengthsOk c) (hp : PolicyStep s s') :
    FullSparseInv c F0 s' :=
  ⟨fullCoreInv_of_policyStep h.1 hlen hp, fullLitMarksClear_of_policyStep h.2.1 hp,
    fullArenaVarsNodup_of_policyStep h.2.2.1 hp, fullExtScratchOk_of_policyStep h.2.2.2.1 hp,
    (dense_mode_of_policyStep hp).trans h.2.2.2.2⟩

theorem fullSparseInvW_of_policyStep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullSparseInvW c F0 F_cur s) (hlen : s'.LengthsOk c)
    (hp : PolicyStep s s') : FullSparseInvW c F0 F_cur s' :=
  ⟨hlen, fullWitnessInv_of_soundMask h.2.1 hp.soundMask_eq,
    fullLitMarksClear_of_policyStep h.2.2.1 hp, fullArenaVarsNodup_of_policyStep h.2.2.2.1 hp,
    fullExtScratchOk_of_policyStep h.2.2.2.2.1 hp,
    (dense_mode_of_policyStep hp).trans h.2.2.2.2.2⟩

theorem fullDenseInv_of_policyStep {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullDenseInv c F0 s) (hlen : s'.LengthsOk c) (hp : PolicyStep s s') :
    FullDenseInv c F0 s' :=
  ⟨fullCoreInv_of_policyStep h.1 hlen hp, fullLitMarksClear_of_policyStep h.2.1 hp,
    fullArenaVarsNodup_of_policyStep h.2.2.1 hp, fullExtScratchOk_of_policyStep h.2.2.2.1 hp,
    (cur_level_of_policyStep hp).trans h.2.2.2.2.1,
    (dense_mode_of_policyStep hp).symm ▸ h.2.2.2.2.2⟩

theorem fullDenseInvW_of_policyStep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullDenseInvW c F0 F_cur s) (hlen : s'.LengthsOk c)
    (hp : PolicyStep s s') : FullDenseInvW c F0 F_cur s' :=
  ⟨hlen, fullWitnessInv_of_soundMask h.2.1 hp.soundMask_eq,
    fullLitMarksClear_of_policyStep h.2.2.1 hp, fullArenaVarsNodup_of_policyStep h.2.2.2.1 hp,
    fullExtScratchOk_of_policyStep h.2.2.2.2.1 hp,
    (cur_level_of_policyStep hp).trans h.2.2.2.2.2.1,
    (dense_mode_of_policyStep hp).symm ▸ h.2.2.2.2.2.2⟩

theorem fullM6HdrInv_of_policyStep {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s s' : FullState} (h : FullM6HdrInv c F0 ext s) (hlen : s'.LengthsOk c)
    (hp : PolicyStep s s') : FullM6HdrInv c F0 ext s' :=
  FullM6HdrInv.mk_inv h.cfgOk h.extOk (fullSparseInv_of_policyStep h.sparse hlen hp)

theorem fullM6HdrInvW_of_policyStep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s s' : FullState} (h : FullM6HdrInvW c F0 F_cur ext s)
    (hlen : s'.LengthsOk c) (hp : PolicyStep s s') : FullM6HdrInvW c F0 F_cur ext s' :=
  FullM6HdrInvW.mk_inv h.cfgOk h.extOk (fullSparseInvW_of_policyStep h.sparseW hlen hp)

theorem fullM6HdrCoreInv_of_policyStep {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s s' : FullState} (h : FullM6HdrCoreInv c F0 ext s) (hlen : s'.LengthsOk c)
    (hp : PolicyStep s s') : FullM6HdrCoreInv c F0 ext s' :=
  FullM6HdrCoreInv.mk_inv h.cfgOk h.extOk (fullCoreInv_of_policyStep h.coreInv hlen hp)

/-- **UNSAT soundness is invariant under policy steps**: if the solver reports UNSAT after any
sequence of memory-safe policy steps from a `FullM6HdrInv` state, `F0` is UNSAT. -/
theorem policyStep_unsat_sound {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s s' : FullState} (h : FullM6HdrInv c F0 ext s) (hlen : s'.LengthsOk c)
    (hp : PolicyStep s s') (hinc : s'.core.inconsistent ≠ 0#64) : F0.Unsat :=
  fullM6HdrInv_inconsistent_unsat (fullM6HdrInv_of_policyStep h hlen hp) hinc

theorem dependsOnCoreAndSafe_sparse (c : FullCfg) (F0 : CNF Nat) :
    DependsOnCoreAndSafe (policySlice c).coreProj (policySlice c).safe (FullSparseInv c F0) :=
  fun _ _ hp hlen h => fullSparseInv_of_policyStep h hlen hp

theorem dependsOnCoreAndSafe_coreInv (c : FullCfg) (F0 : CNF Nat) :
    DependsOnCoreAndSafe (policySlice c).coreProj (policySlice c).safe (FullCoreInv c F0) :=
  fun _ _ hp hlen h => fullCoreInv_of_policyStep h hlen hp

theorem dependsOnCoreAndSafe_m6Hdr (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) :
    DependsOnCoreAndSafe (policySlice c).coreProj (policySlice c).safe (FullM6HdrInv c F0 ext) :=
  fun _ _ hp hlen h => fullM6HdrInv_of_policyStep h hlen hp

theorem dependsOnCoreAndSafe_m6HdrW (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (ext : List (BitVec 64)) :
    DependsOnCoreAndSafe (policySlice c).coreProj (policySlice c).safe
      (FullM6HdrInvW c F0 F_cur ext) :=
  fun _ _ hp hlen h => fullM6HdrInvW_of_policyStep h hlen hp

/-! ## 3. `PolicyFrameSpec` & `M6PolicyFrameSpec` builders and lifts -/

/-- Tier-P1 specification builder (`PolicyFrameSpec Pre Post`):
certifies `FullMem c s ⋆ R` memory safety + region disjointness, `FullState.LengthsOk c`,
`PolicyStep s s'` (sound core + `last_learned`/`extend_len` untouched), optional bounded `Post`,
and `NoExit` (`X` ignored), while leaving all policy-owned counters and scratch arrays
abstractly bounded rather than functionally specified. -/
@[expose] def PolicyFrameSpec {as rs : List Ty}
    (Pre : FullCfg → Tup Val as → FullState → Prop)
    (Post : FullCfg → Tup Val as → Tup Val rs → FullState → FullState → Prop :=
      fun _ _ _ _ _ => True) : Spec as rs :=
  SafetySlice.spec policySlice Pre Post

/-- Canonical `(FullHdr *h) -> void` policy specification (`PolicyFrameSpec`). -/
@[expose] def PolicyVoidSpec : Spec [i64] [] :=
  PolicyFrameSpec (fun c (h, ()) _ => h = c.hdr)

/-- Canonical `(FullHdr *h) -> u64` policy specification (`PolicyFrameSpec`) with bounded `Post`.
-/
@[expose] def PolicyU64Spec
    (Post : FullCfg → BitVec 64 → FullState → FullState → Prop := fun _ _ _ _ => True) :
    Spec [i64] [i64] :=
  PolicyFrameSpec (fun c (h, ()) _ => h = c.hdr) (fun c _ (r, ()) s s' => Post c r s s')

/-- Combined M6 extended-header + base state for policy functions reading/writing `M6HdrExt`. -/
abbrev M6PolicyState : Type := List (BitVec 64) × FullState

/-- `M6Hdr`-aware policy `SafetySlice`: `FullM6HdrMem c ext s` footprint, `policyView s` core
frame (preserving soundness-bearing fields + `last_learned`/`extend_len`), and
`FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c` safety. -/
@[expose] def m6PolicySlice (c : FullCfg) : SafetySlice M6PolicyState PolicyView where
  mem := fun p => FullM6HdrMem c p.1 p.2
  coreProj := fun p => policyView p.2
  safe := fun p => FullM6HdrCfgOk c ∧ M6HdrExtOk p.1 ∧ p.2.LengthsOk c

@[scoped simp] theorem m6PolicySlice_mem (c : FullCfg) (p : M6PolicyState) :
    (m6PolicySlice c).mem p = FullM6HdrMem c p.1 p.2 := rfl
@[scoped simp] theorem m6PolicySlice_coreProj (c : FullCfg) (p : M6PolicyState) :
    (m6PolicySlice c).coreProj p = policyView p.2 := rfl
@[scoped simp] theorem m6PolicySlice_safe (c : FullCfg) (p : M6PolicyState) :
    (m6PolicySlice c).safe p = (FullM6HdrCfgOk c ∧ M6HdrExtOk p.1 ∧ p.2.LengthsOk c) := rfl

/-- `M6Hdr`-aware policy spec (`PolicyFrameSpec` generalized to mutate `M6HdrExt` safely). -/
@[expose] def M6PolicyFrameSpec {as rs : List Ty}
    (Pre : FullCfg → Tup Val as → List (BitVec 64) → FullState → Prop)
    (Post : FullCfg → Tup Val as → Tup Val rs →
      List (BitVec 64) → FullState → List (BitVec 64) → FullState → Prop :=
      fun _ _ _ _ _ _ _ => True) : Spec as rs :=
  SafetySlice.spec m6PolicySlice (fun c xs p => Pre c xs p.1 p.2)
    (fun c xs r p p' => Post c xs r p.1 p.2 p'.1 p'.2)

namespace PolicyFrameSpec

theorem mono {as rs : List Ty}
    {Pre : FullCfg → Tup Val as → FullState → Prop}
    {PostFn : FullCfg → Tup Val as → Tup Val rs → FullState → FullState → Prop} :
    (PolicyFrameSpec Pre PostFn).Mono :=
  SafetySlice.spec_mono policySlice Pre PostFn

theorem noExit {as rs : List Ty}
    {Pre : FullCfg → Tup Val as → FullState → Prop}
    {PostFn : FullCfg → Tup Val as → Tup Val rs → FullState → FullState → Prop}
    {xs : Tup Val as} {m : Mem 64} {Q : LeanQbe.T.Post rs} {X X' : XPost}
    (h : PolicyFrameSpec Pre PostFn xs m Q X) :
    PolicyFrameSpec Pre PostFn xs m Q X' :=
  SafetySlice.spec_noExit h

theorem frame {as rs : List Ty}
    {Pre : FullCfg → Tup Val as → FullState → Prop}
    {PostFn : FullCfg → Tup Val as → Tup Val rs → FullState → FullState → Prop}
    {xs : Tup Val as} {m : Mem 64} {Q : LeanQbe.T.Post rs} {X : XPost} {F : Mem 64 → Prop}
    (h : ((fun m₁ => PolicyFrameSpec Pre PostFn xs m₁ Q X) ⋆ F) m) :
    PolicyFrameSpec Pre PostFn xs m (fun r m' => (Q r ⋆ F) m') X :=
  SafetySlice.spec_frame h

theorem weaken {as rs : List Ty}
    {Pre₁ Pre₂ : FullCfg → Tup Val as → FullState → Prop}
    {Post₁ Post₂ : FullCfg → Tup Val as → Tup Val rs → FullState → FullState → Prop}
    (hPre : ∀ c xs s, Pre₁ c xs s → Pre₂ c xs s)
    (hPost : ∀ c xs r s s', Pre₁ c xs s → PolicyStep s s' → s'.LengthsOk c →
      Post₂ c xs r s s' → Post₁ c xs r s s')
    {xs : Tup Val as} {m : Mem 64} {Q : LeanQbe.T.Post rs} {X : XPost}
    (h : PolicyFrameSpec Pre₁ Post₁ xs m Q X) :
    PolicyFrameSpec Pre₂ Post₂ xs m Q X :=
  SafetySlice.spec_weaken hPre hPost h

/-- Any `SafetySlice.spec fullSafetySlice` contract whose `Post` preserves `FullExtScratchPres`
implies `PolicyFrameSpec` in one step (bridges all landed P0 specs into `PolicyFrame`). -/
theorem of_safetySlice {as rs : List Ty}
    {Pre : FullCfg → Tup Val as → FullState → Prop}
    {PostFn : FullCfg → Tup Val as → Tup Val rs → FullState → FullState → Prop}
    (hext : ∀ c xs r s s', Pre c xs s → s'.core = s.core → s'.LengthsOk c →
      PostFn c xs r s s' → FullExtScratchPres s s')
    {xs : Tup Val as} {m : Mem 64} {Q : LeanQbe.T.Post rs} {X : XPost}
    (h : PolicyFrameSpec Pre PostFn xs m Q X) :
    SafetySlice.spec fullSafetySlice Pre PostFn xs m Q X := by
  rcases h with ⟨c, s, R, hpre, hlen, hm, hk⟩
  refine ⟨c, s, R, hpre, hlen, hm, fun r s' m' hc hlen' hpost hm' => ?_⟩
  exact hk r s' m' (PolicyStep.of_safety hc (hext c xs r s s' hpre hc hlen' hpost))
    hlen' hpost hm'

/-- Lift `fullSafetyVoidSpec` directly into `PolicyVoidSpec`. -/
theorem of_safetyVoid {xs : Tup Val [i64]} {m : Mem 64} {Q : LeanQbe.T.Post []} {X : XPost}
    (h : PolicyVoidSpec xs m Q X) : fullSafetyVoidSpec xs m Q X := by
  rcases h with ⟨c, s, R, hpre, hlen, hm, hk⟩
  refine ⟨c, s, R, hpre, hlen, hm, fun r s' m' hc hlen' hp hm' => ?_⟩
  exact hk r s' m' (PolicyStep.of_safety hc hp.1) hlen' trivial hm'

/-- Lift `PolicyFrameSpec` into `M6PolicyFrameSpec` (framing `m6ExtMem` untouched). -/
theorem to_m6 {as rs : List Ty}
    {Pre : FullCfg → Tup Val as → FullState → Prop}
    {PostFn : FullCfg → Tup Val as → Tup Val rs → FullState → FullState → Prop}
    {xs : Tup Val as} {m : Mem 64} {Q : LeanQbe.T.Post rs} {X : XPost}
    (h : M6PolicyFrameSpec (fun c xs _ s => Pre c xs s)
      (fun c xs r _ s ext' s' => ext' = ext' ∧ PostFn c xs r s s') xs m Q X) :
    PolicyFrameSpec Pre PostFn xs m Q X := by
  rcases h with ⟨c, ⟨ext, s⟩, R, hpre, ⟨hcfg, hext, hlen⟩, hm, hk⟩
  exact ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, hpre, hlen, fullM6HdrMem_focus_full hm,
    fun r s' m' hp hlen' hpost hm' =>
      hk r (ext, s') m' hp ⟨hcfg, hext, hlen'⟩ ⟨rfl, hpost⟩ (fullM6HdrMem_unfocus_full hm')⟩

/-- Lift any `PolicyFrameSpec` contract over `FullM6HdrMem` while preserving `FullM6HdrInv`. -/
theorem frame_m6HdrInv {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {as rs : List Ty}
    {Pre : FullCfg → Tup Val as → FullState → Prop}
    {PostFn : FullCfg → Tup Val as → Tup Val rs → FullState → FullState → Prop}
    {xs : Tup Val as} {Q : LeanQbe.T.Post rs} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hpre : Pre c xs s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r s' m', FullM6HdrInv c F0 ext s' → PolicyStep s s' → PostFn c xs r s s' →
      (FullM6HdrMem c ext s' ⋆ R) m' → Q r m') :
    PolicyFrameSpec Pre PostFn xs m Q X :=
  ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, hpre, hinv.sparse.lengths,
    fullM6HdrMem_focus_full hm, fun r s' m' hp hlen' hpost hm' =>
      hk r s' m' (fullM6HdrInv_of_policyStep hinv hlen' hp) hp hpost
        (fullM6HdrMem_unfocus_full hm')⟩

/-- Lift any `PolicyFrameSpec` contract over `FullM6HdrMem` while preserving `FullM6HdrInvW`. -/
theorem frame_m6HdrInvW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {as rs : List Ty}
    {Pre : FullCfg → Tup Val as → FullState → Prop}
    {PostFn : FullCfg → Tup Val as → Tup Val rs → FullState → FullState → Prop}
    {xs : Tup Val as} {Q : LeanQbe.T.Post rs} {X : XPost}
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hpre : Pre c xs s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r s' m', FullM6HdrInvW c F0 F_cur ext s' → PolicyStep s s' → PostFn c xs r s s' →
      (FullM6HdrMem c ext s' ⋆ R) m' → Q r m') :
    PolicyFrameSpec Pre PostFn xs m Q X :=
  ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, hpre, hinv.sparseW.1,
    fullM6HdrMem_focus_full hm, fun r s' m' hp hlen' hpost hm' =>
      hk r s' m' (fullM6HdrInvW_of_policyStep hinv hlen' hp) hp hpost
        (fullM6HdrMem_unfocus_full hm')⟩

end PolicyFrameSpec

namespace M6PolicyFrameSpec

theorem mono {as rs : List Ty}
    {Pre : FullCfg → Tup Val as → List (BitVec 64) → FullState → Prop}
    {PostFn : FullCfg → Tup Val as → Tup Val rs →
      List (BitVec 64) → FullState → List (BitVec 64) → FullState → Prop} :
    (M6PolicyFrameSpec Pre PostFn).Mono :=
  SafetySlice.spec_mono m6PolicySlice _ _

theorem noExit {as rs : List Ty}
    {Pre : FullCfg → Tup Val as → List (BitVec 64) → FullState → Prop}
    {PostFn : FullCfg → Tup Val as → Tup Val rs →
      List (BitVec 64) → FullState → List (BitVec 64) → FullState → Prop}
    {xs : Tup Val as} {m : Mem 64} {Q : LeanQbe.T.Post rs} {X X' : XPost}
    (h : M6PolicyFrameSpec Pre PostFn xs m Q X) :
    M6PolicyFrameSpec Pre PostFn xs m Q X' :=
  SafetySlice.spec_noExit h

theorem frame {as rs : List Ty}
    {Pre : FullCfg → Tup Val as → List (BitVec 64) → FullState → Prop}
    {PostFn : FullCfg → Tup Val as → Tup Val rs →
      List (BitVec 64) → FullState → List (BitVec 64) → FullState → Prop}
    {xs : Tup Val as} {m : Mem 64} {Q : LeanQbe.T.Post rs} {X : XPost} {F : Mem 64 → Prop}
    (h : ((fun m₁ => M6PolicyFrameSpec Pre PostFn xs m₁ Q X) ⋆ F) m) :
    M6PolicyFrameSpec Pre PostFn xs m (fun r m' => (Q r ⋆ F) m') X :=
  SafetySlice.spec_frame h

theorem frame_m6HdrInv {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {as rs : List Ty}
    {Pre : FullCfg → Tup Val as → List (BitVec 64) → FullState → Prop}
    {PostFn : FullCfg → Tup Val as → Tup Val rs →
      List (BitVec 64) → FullState → List (BitVec 64) → FullState → Prop}
    {xs : Tup Val as} {Q : LeanQbe.T.Post rs} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hpre : Pre c xs ext s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r ext' s' m', FullM6HdrInv c F0 ext' s' → PolicyStep s s' →
      PostFn c xs r ext s ext' s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q r m') :
    M6PolicyFrameSpec Pre PostFn xs m Q X :=
  ⟨c, (ext, s), R, hpre, ⟨hinv.cfgOk, hinv.extOk, hinv.sparse.lengths⟩, hm,
    fun r ⟨ext', s'⟩ m' hp ⟨_, hext', hlen'⟩ hpost hm' =>
      hk r ext' s' m'
        (FullM6HdrInv.mk_inv hinv.cfgOk hext' (fullSparseInv_of_policyStep hinv.sparse hlen' hp))
        hp hpost hm'⟩

end M6PolicyFrameSpec

/-! ## 4. WP composition, policy loop combinators, callee transport & `TableImpl` -/

section PolicyWP

variable {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}

/-- Entry helper for proving `∀ xs m Q X, PolicyFrameSpec Pre Post xs m Q X → Func.wp ...`:
unpacks `c`, `s`, `R`, `Pre`, `s.LengthsOk c`, `(FullMem c s ⋆ R) m`, and the return callback. -/
theorem wp_policy_intro {as : List Ty} {body : Func as rs}
    {Pre : FullCfg → Tup Val as → FullState → Prop}
    {Post : FullCfg → Tup Val as → Tup Val rs → FullState → FullState → Prop}
    (h : ∀ c xs s R m Q X, Pre c xs s → s.LengthsOk c → (FullMem c s ⋆ R) m →
      (∀ r s' m', PolicyStep s s' → s'.LengthsOk c → Post c xs r s s' →
        (FullMem c s' ⋆ R) m' → Q r m') →
      Func.wp Γ body xs m Q X) :
    ∀ xs m Q X, PolicyFrameSpec Pre Post xs m Q X → Func.wp Γ body xs m Q X :=
  fun xs m Q X ⟨c, s, R, hpre, hlen, hm, hk⟩ => h c xs s R m Q X hpre hlen hm hk

/-- Entry helper for `M6PolicyFrameSpec`. -/
theorem wp_m6_policy_intro {as : List Ty} {body : Func as rs}
    {Pre : FullCfg → Tup Val as → List (BitVec 64) → FullState → Prop}
    {Post : FullCfg → Tup Val as → Tup Val rs →
      List (BitVec 64) → FullState → List (BitVec 64) → FullState → Prop}
    (h : ∀ c xs ext s R m Q X, Pre c xs ext s →
      FullM6HdrCfgOk c → M6HdrExtOk ext → s.LengthsOk c → (FullM6HdrMem c ext s ⋆ R) m →
      (∀ r ext' s' m', PolicyStep s s' → M6HdrExtOk ext' → s'.LengthsOk c →
        Post c xs r ext s ext' s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q r m') →
      Func.wp Γ body xs m Q X) :
    ∀ xs m Q X, M6PolicyFrameSpec Pre Post xs m Q X → Func.wp Γ body xs m Q X :=
  fun xs m Q X ⟨c, ⟨ext, s⟩, R, hpre, ⟨hcfg, hext, hlen⟩, hm, hk⟩ =>
    h c xs ext s R m Q X hpre hcfg hext hlen hm fun r ext' s' m' hp hext' hlen' hpost hm' =>
      hk r (ext', s') m' hp ⟨hcfg, hext', hlen'⟩ hpost hm'

/-- Call a `PolicyFrameSpec` callee from a `PolicyStep` context and automatically compose
`PolicyStep s0 s'`. -/
theorem wp_policy_call {f : Sym} {as bs : List Ty}
    {args : Tup (Arg Val) as} {k : Tup Val bs → Expr Val Cont rs} {m : Mem 64}
    {Pre : FullCfg → Tup Val as → FullState → Prop}
    {Post : FullCfg → Tup Val as → Tup Val bs → FullState → FullState → Prop}
    (hCallee : ∀ xs m Q X, PolicyFrameSpec Pre Post xs m Q X → Γ f as bs xs m Q X)
    {c : FullCfg} {s0 s : FullState} {R : Mem 64 → Prop}
    (hstep : PolicyStep s0 s) (hpre : Pre c (vals args) s) (hlen : s.LengthsOk c)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m', PolicyStep s0 s' → PolicyStep s s' → s'.LengthsOk c →
      Post c (vals args) r s s' → (FullMem c s' ⋆ R) m' → wp Γ Q X (k r) m') :
    wp Γ Q X (.call f args k) m :=
  wp_call_of_spec args k (hCallee _ m _ X ⟨c, s, R, hpre, hlen, hm,
    fun r s' m' hs hlen' hpost hm' => hk r s' m' (hstep.trans hs) hs hlen' hpost hm'⟩)

/-- Call a `SafetySlice.spec fullSafetySlice` callee (`fullSafetyVoidSpec`, `fullRngNextSpec`,
`fullBumpVarSpec`, `fullQueueMtfSpec`, etc.) inside a policy proof and automatically chain
`PolicyStep s0 s'`. -/
theorem wp_policy_call_safety {f : Sym} {as bs : List Ty}
    {args : Tup (Arg Val) as} {k : Tup Val bs → Expr Val Cont rs} {m : Mem 64}
    {Pre : FullCfg → Tup Val as → FullState → Prop}
    {Post : FullCfg → Tup Val as → Tup Val bs → FullState → FullState → Prop}
    (hCallee : ∀ xs m Q X, SafetySlice.spec fullSafetySlice Pre Post xs m Q X → Γ f as bs xs m Q X)
    (hext : ∀ c r s s', Pre c (vals args) s → s'.core = s.core → s'.LengthsOk c →
      Post c (vals args) r s s' → FullExtScratchPres s s')
    {c : FullCfg} {s0 s : FullState} {R : Mem 64 → Prop}
    (hstep : PolicyStep s0 s) (hpre : Pre c (vals args) s) (hlen : s.LengthsOk c)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m', PolicyStep s0 s' → s'.core = s.core → s'.LengthsOk c →
      Post c (vals args) r s s' → (FullMem c s' ⋆ R) m' → wp Γ Q X (k r) m') :
    wp Γ Q X (.call f args k) m :=
  wp_call_of_spec args k (hCallee _ m _ X ⟨c, s, R, hpre, hlen, hm,
    fun r s' m' hc hlen' hpost hm' =>
      let hs := PolicyStep.of_safety hc (hext c r s s' hpre hc hlen' hpost)
      hk r s' m' (hstep.trans hs) hc hlen' hpost hm'⟩)

/-- Call a `PolicyFrameSpec` callee directly under `FullM6HdrInv`, transporting `FullM6HdrInv`
in one step. -/
theorem wp_policy_call_m6HdrInv {f : Sym} {as bs : List Ty}
    {args : Tup (Arg Val) as} {k : Tup Val bs → Expr Val Cont rs} {m : Mem 64}
    {Pre : FullCfg → Tup Val as → FullState → Prop}
    {Post : FullCfg → Tup Val as → Tup Val bs → FullState → FullState → Prop}
    (hCallee : ∀ xs m Q X, PolicyFrameSpec Pre Post xs m Q X → Γ f as bs xs m Q X)
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop}
    (hinv : FullM6HdrInv c F0 ext s) (hpre : Pre c (vals args) s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r s' m', FullM6HdrInv c F0 ext s' → PolicyStep s s' →
      Post c (vals args) r s s' → (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k r) m') :
    wp Γ Q X (.call f args k) m :=
  wp_call_of_spec args k (hCallee _ m _ X (PolicyFrameSpec.frame_m6HdrInv hinv hpre hm hk))

/-- Call an `M6PolicyFrameSpec` callee directly under `FullM6HdrInv`, transporting `FullM6HdrInv`.
-/
theorem wp_m6_policy_call_m6HdrInv {f : Sym} {as bs : List Ty}
    {args : Tup (Arg Val) as} {k : Tup Val bs → Expr Val Cont rs} {m : Mem 64}
    {Pre : FullCfg → Tup Val as → List (BitVec 64) → FullState → Prop}
    {Post : FullCfg → Tup Val as → Tup Val bs →
      List (BitVec 64) → FullState → List (BitVec 64) → FullState → Prop}
    (hCallee : ∀ xs m Q X, M6PolicyFrameSpec Pre Post xs m Q X → Γ f as bs xs m Q X)
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop}
    (hinv : FullM6HdrInv c F0 ext s) (hpre : Pre c (vals args) ext s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r ext' s' m', FullM6HdrInv c F0 ext' s' → PolicyStep s s' →
      Post c (vals args) r ext s ext' s' → (FullM6HdrMem c ext' s' ⋆ R) m' →
      wp Γ Q X (k r) m') :
    wp Γ Q X (.call f args k) m :=
  wp_call_of_spec args k (hCallee _ m _ X (M6PolicyFrameSpec.frame_m6HdrInv hinv hpre hm hk))

/-- Call a `PolicyFrameSpec` callee directly under `FullSparseInv`, transporting `FullSparseInv`.
-/
theorem wp_policy_call_sparseInv {f : Sym} {as bs : List Ty}
    {args : Tup (Arg Val) as} {k : Tup Val bs → Expr Val Cont rs} {m : Mem 64}
    {Pre : FullCfg → Tup Val as → FullState → Prop}
    {Post : FullCfg → Tup Val as → Tup Val bs → FullState → FullState → Prop}
    (hCallee : ∀ xs m Q X, PolicyFrameSpec Pre Post xs m Q X → Γ f as bs xs m Q X)
    {c : FullCfg} {F0 : CNF Nat} {s : FullState} {R : Mem 64 → Prop}
    (hinv : FullSparseInv c F0 s) (hpre : Pre c (vals args) s) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m', FullSparseInv c F0 s' → PolicyStep s s' →
      Post c (vals args) r s s' → (FullMem c s' ⋆ R) m' → wp Γ Q X (k r) m') :
    wp Γ Q X (.call f args k) m :=
  wp_call_of_spec args k (hCallee _ m _ X ⟨c, s, R, hpre, hinv.lengths, hm,
    fun r s' m' hp hlen' hpost hm' => hk r s' m' (fullSparseInv_of_policyStep hinv hlen' hp)
      hp hpost hm'⟩)

/-- Policy `while` loop rule: automatically carries `(FullMem c s' ⋆ R) ml`, `PolicyStep s0 s'`,
and `s'.LengthsOk c` across every iteration with state-dependent termination measure `μ`. -/
theorem wp_policy_loop {ts : List Ty} {m : Mem 64} (c : FullCfg) (s0 : FullState)
    (R : Mem 64 → Prop)
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (LoopInv : FullState → Tup Val ts → Prop)
    (μ : FullState → Tup Val ts → Nat)
    (hentry : ∀ J : Cont ts,
      (∀ s' xs ml, (FullMem c s' ⋆ R) ml → PolicyStep s0 s' → s'.LengthsOk c →
        LoopInv s' xs → J xs ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) s' xs ml,
      PolicyStep s0 s' → s'.LengthsOk c → LoopInv s' xs → (FullMem c s' ⋆ R) ml →
      (∀ s'' ys ml', (FullMem c s'' ⋆ R) ml' → μ s'' ys < μ s' xs →
        PolicyStep s' s'' → s''.LengthsOk c → LoopInv s'' ys → J ys ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) ml) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_loop_safety_slice_state_pure (policySlice c) s0 R LoopInv μ hentry hbody

/-- Policy `for (i = ...; i < n; i++)` bounded `BitVec 64` loop rule with extra state tuple `ps`:
automatically uses measure `n.toNat - i.toNat` and discharges `i' = i + 1#64` measure drop. -/
theorem wp_policy_for {ps : List Ty} {m : Mem 64} (c : FullCfg) (s0 : FullState) (R : Mem 64 → Prop)
    {bodies : Tup Cont [i64 :: ps] → Blocks Val Cont rs [i64 :: ps]}
    {entry : Tup Cont [i64 :: ps] → Expr Val Cont rs}
    (n : BitVec 64)
    (LoopInv : FullState → BitVec 64 → Tup Val ps → Prop)
    (hentry : ∀ J : Cont (i64 :: ps),
      (∀ s' i rest ml, (FullMem c s' ⋆ R) ml → PolicyStep s0 s' → s'.LengthsOk c →
        i.toNat ≤ n.toNat → LoopInv s' i rest → J (i, rest) ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont (i64 :: ps)) s' i rest ml,
      PolicyStep s0 s' → s'.LengthsOk c → i.toNat ≤ n.toNat → LoopInv s' i rest →
      (FullMem c s' ⋆ R) ml →
      (∀ s'' rest' ml', i.toNat < n.toNat → (FullMem c s'' ⋆ R) ml' →
        PolicyStep s' s'' → s''.LengthsOk c → LoopInv s'' (i + 1#64) rest' →
        J (i + 1#64, rest') ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (i, rest)) ml) :
    wp Γ Q X (.group (sig := [i64 :: ps]) bodies entry) m :=
  wp_policy_loop c s0 R
    (fun s' xs => xs.1.toNat ≤ n.toNat ∧ LoopInv s' xs.1 xs.2)
    (fun _ xs => n.toNat - xs.1.toNat)
    (fun J hJ => hentry J fun s' i rest ml hm hp hlen hle hli =>
      hJ s' (i, rest) ml hm hp hlen ⟨hle, hli⟩)
    (fun J s' (i, rest) ml hp hlen ⟨hle, hli⟩ hm hJ =>
      hbody J s' i rest ml hp hlen hle hli hm fun s'' rest' ml' hlt hm' hp' hlen' hli' =>
        hJ s'' (i + 1#64, rest') ml' hm' (bv64_measure_sub_lt hlt) hp' hlen'
          ⟨by rw [bv64_add1_toNat hlt]; exact hlt, hli'⟩)

/-- Policy loop-with-break rule (`while (true) { ... break; }` / `for` + early `break`). -/
theorem wp_policy_loop_break {brkTs lpTs : List Ty} {m : Mem 64} (c : FullCfg)
    (s0 : FullState) (R : Mem 64 → Prop)
    {outerBodies : Tup Cont [brkTs] → Blocks Val Cont rs [brkTs]}
    {innerBodies : Tup Cont [brkTs] → Tup Cont [lpTs] → Blocks Val Cont rs [lpTs]}
    {innerEntry : Tup Cont [brkTs] → Tup Cont [lpTs] → Expr Val Cont rs}
    (BrkPost : FullState → Tup Val brkTs → Prop)
    (LoopInv : FullState → Tup Val lpTs → Prop)
    (μ : FullState → Tup Val lpTs → Nat)
    (hafter : ∀ (B : Cont brkTs) s' xs ml,
      PolicyStep s0 s' → s'.LengthsOk c → BrkPost s' xs → (FullMem c s' ⋆ R) ml →
      wp Γ Q X (Blocks.get (outerBodies (B, ())) .here xs) ml)
    (hbody : ∀ (B : Cont brkTs) (L : Cont lpTs) s' xs ml,
      PolicyStep s0 s' → s'.LengthsOk c → LoopInv s' xs → (FullMem c s' ⋆ R) ml →
      (∀ s'' r ml', (FullMem c s'' ⋆ R) ml' → PolicyStep s' s'' → s''.LengthsOk c →
        BrkPost s'' r → B r ml') →
      (∀ s'' ys ml', (FullMem c s'' ⋆ R) ml' → μ s'' ys < μ s' xs →
        PolicyStep s' s'' → s''.LengthsOk c → LoopInv s'' ys → L ys ml') →
      wp Γ Q X (Blocks.get (innerBodies (B, ()) (L, ())) .here xs) ml)
    (hentry : ∀ (B : Cont brkTs) (L : Cont lpTs),
      (∀ s' r ml, (FullMem c s' ⋆ R) ml → PolicyStep s0 s' → s'.LengthsOk c →
        BrkPost s' r → B r ml) →
      (∀ s' xs ml, (FullMem c s' ⋆ R) ml → PolicyStep s0 s' → s'.LengthsOk c →
        LoopInv s' xs → L xs ml) →
      wp Γ Q X (innerEntry (B, ()) (L, ())) m) :
    wp Γ Q X (.group (sig := [brkTs]) outerBodies
      (fun oJs => .group (sig := [lpTs]) (innerBodies oJs) (innerEntry oJs))) m :=
  wp_loop_safety_slice_break (policySlice c) s0 R (fun _ => True) trivial
    BrkPost LoopInv μ
    (fun B s' xs ml hp hlen _ hbp hm => hafter B s' xs ml hp hlen hbp hm)
    (fun B L s' xs ml hp hlen _ hli hm hB hL => hbody B L s' xs ml hp hlen hli hm hB hL)
    hentry

/-- Forward control-flow join rule over `policySlice`. -/
theorem wp_policy_join {ts : List Ty} {m : Mem 64} (c : FullCfg) (s0 : FullState)
    (R : Mem 64 → Prop)
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (P : FullState → Tup Val ts → Prop)
    (hbody : ∀ (J : Cont ts) s' xs ml,
      PolicyStep s0 s' → s'.LengthsOk c → P s' xs → (FullMem c s' ⋆ R) ml →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) ml)
    (hentry : ∀ J : Cont ts,
      (∀ s' xs ml, (FullMem c s' ⋆ R) ml → PolicyStep s0 s' → s'.LengthsOk c → P s' xs → J xs ml) →
      wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_join_safety_slice (policySlice c) s0 R (fun _ => True) trivial P
    (fun J s' xs ml hp hlen _ hpx hm => hbody J s' xs ml hp hlen hpx hm) hentry

/-- `M6PolicyFrameSpec` loop rule (`while` / `for`) carrying `FullM6HdrMem` + `M6HdrExtOk`. -/
theorem wp_m6_policy_loop {ts : List Ty} {m : Mem 64} (c : FullCfg)
    (ext0 : List (BitVec 64)) (s0 : FullState) (R : Mem 64 → Prop)
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (LoopInv : List (BitVec 64) → FullState → Tup Val ts → Prop)
    (μ : List (BitVec 64) → FullState → Tup Val ts → Nat)
    (hentry : ∀ J : Cont ts,
      (∀ ext' s' xs ml, (FullM6HdrMem c ext' s' ⋆ R) ml → PolicyStep s0 s' →
        FullM6HdrCfgOk c → M6HdrExtOk ext' → s'.LengthsOk c → LoopInv ext' s' xs → J xs ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) ext' s' xs ml,
      PolicyStep s0 s' → FullM6HdrCfgOk c → M6HdrExtOk ext' → s'.LengthsOk c →
      LoopInv ext' s' xs → (FullM6HdrMem c ext' s' ⋆ R) ml →
      (∀ ext'' s'' ys ml', (FullM6HdrMem c ext'' s'' ⋆ R) ml' → μ ext'' s'' ys < μ ext' s' xs →
        PolicyStep s' s'' → FullM6HdrCfgOk c → M6HdrExtOk ext'' → s''.LengthsOk c →
        LoopInv ext'' s'' ys → J ys ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) ml) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_loop_safety_slice_state_pure (m6PolicySlice c) (ext0, s0) R
    (fun p xs => LoopInv p.1 p.2 xs) (fun p xs => μ p.1 p.2 xs)
    (fun J hJ => hentry J fun ext' s' xs ml hm hp hcfg hext hlen hli =>
      hJ (ext', s') xs ml hm hp ⟨hcfg, hext, hlen⟩ hli)
    (fun J ⟨ext', s'⟩ xs ml hp ⟨hcfg, hext, hlen⟩ hli hm hJ =>
      hbody J ext' s' xs ml hp hcfg hext hlen hli hm
        fun ext'' s'' ys ml' hm' hlt hp' hcfg' hext' hlen' hli' =>
          hJ (ext'', s'') ys ml' hm' hlt hp' ⟨hcfg', hext', hlen'⟩ hli')

end PolicyWP

section PolicyTableHelpers

/-- Build a `noExit := true` `SpecEntry` from a `PolicyFrameSpec` contract. -/
@[expose] def PolicyFrameSpec.specEntry (fn : Fn)
    (Pre : FullCfg → Tup Val fn.as → FullState → Prop)
    (Post : FullCfg → Tup Val fn.as → Tup Val fn.rs → FullState → FullState → Prop :=
      fun _ _ _ _ _ => True) : SpecEntry :=
  .ofFn fn (PolicyFrameSpec Pre Post) true

/-- Build a `noExit := true` `SpecEntry` from an `M6PolicyFrameSpec` contract. -/
@[expose] def M6PolicyFrameSpec.specEntry (fn : Fn)
    (Pre : FullCfg → Tup Val fn.as → List (BitVec 64) → FullState → Prop)
    (Post : FullCfg → Tup Val fn.as → Tup Val fn.rs →
      List (BitVec 64) → FullState → List (BitVec 64) → FullState → Prop :=
      fun _ _ _ _ _ _ _ => True) : SpecEntry :=
  .ofFn fn (M6PolicyFrameSpec Pre Post) true

/-- Discharge `SpecEntry.Impl Γ fn (PolicyFrameSpec.specEntry fn Pre Post)` directly from a
`PolicyFrameSpec` WP theorem (`noExit = true` handled automatically). -/
theorem PolicyFrameSpec.tableImpl_of {Γ : Env} {fn : Fn}
    {Pre : FullCfg → Tup Val fn.as → FullState → Prop}
    {Post : FullCfg → Tup Val fn.as → Tup Val fn.rs → FullState → FullState → Prop}
    (hwp : ∀ xs m Q X, PolicyFrameSpec Pre Post xs m Q X → Func.wp Γ fn.body xs m Q X) :
    SpecEntry.Impl Γ fn (PolicyFrameSpec.specEntry fn Pre Post) :=
  .of hwp

/-- Discharge `SpecEntry.Impl` for an `M6PolicyFrameSpec` row. -/
theorem M6PolicyFrameSpec.tableImpl_of {Γ : Env} {fn : Fn}
    {Pre : FullCfg → Tup Val fn.as → List (BitVec 64) → FullState → Prop}
    {Post : FullCfg → Tup Val fn.as → Tup Val fn.rs →
      List (BitVec 64) → FullState → List (BitVec 64) → FullState → Prop}
    (hwp : ∀ xs m Q X, M6PolicyFrameSpec Pre Post xs m Q X → Func.wp Γ fn.body xs m Q X) :
    SpecEntry.Impl Γ fn (M6PolicyFrameSpec.specEntry fn Pre Post) :=
  .of hwp

/-- Look up a `PolicyFrameSpec` row in `Env.ofTable tbl` by index (`noExit = true` automatic). -/
theorem policy_table_row_at {tbl : List SpecEntry} {idx : Nat} {fn : Fn}
    {Pre : FullCfg → Tup Val fn.as → FullState → Prop}
    {Post : FullCfg → Tup Val fn.as → Tup Val fn.rs → FullState → FullState → Prop}
    (hget : tbl[idx]? = some (PolicyFrameSpec.specEntry fn Pre Post))
    (hnd : (tbl.map SpecEntry.name).Nodup) :
    ∀ xs m Q X, PolicyFrameSpec Pre Post xs m Q X →
      Env.ofTable tbl fn.name fn.as fn.rs xs m Q X :=
  fun xs m Q X h => env_ofTable_row_at hget hnd
    (by simpa only [PolicyFrameSpec.specEntry, SpecEntry.eff, ite_true] using
      PolicyFrameSpec.noExit h)

/-- Look up an `M6PolicyFrameSpec` row in `Env.ofTable tbl` by index (`noExit = true` automatic).
-/
theorem m6_policy_table_row_at {tbl : List SpecEntry} {idx : Nat} {fn : Fn}
    {Pre : FullCfg → Tup Val fn.as → List (BitVec 64) → FullState → Prop}
    {Post : FullCfg → Tup Val fn.as → Tup Val fn.rs →
      List (BitVec 64) → FullState → List (BitVec 64) → FullState → Prop}
    (hget : tbl[idx]? = some (M6PolicyFrameSpec.specEntry fn Pre Post))
    (hnd : (tbl.map SpecEntry.name).Nodup) :
    ∀ xs m Q X, M6PolicyFrameSpec Pre Post xs m Q X →
      Env.ofTable tbl fn.name fn.as fn.rs xs m Q X :=
  fun xs m Q X h => env_ofTable_row_at hget hnd
    (by simpa only [M6PolicyFrameSpec.specEntry, SpecEntry.eff, ite_true] using
      M6PolicyFrameSpec.noExit h)

/-- Convert any `SafetySlice.spec fullSafetySlice` callee lookup into a `PolicyFrameSpec` callee
hypothesis (`hext` discharges `FullExtScratchPres`). -/
theorem policy_callee_of_safety {Γ : Env} {f : Sym} {as bs : List Ty}
    {Pre : FullCfg → Tup Val as → FullState → Prop}
    {Post : FullCfg → Tup Val as → Tup Val bs → FullState → FullState → Prop}
    (hΓ : ∀ xs m Q X, SafetySlice.spec fullSafetySlice Pre Post xs m Q X → Γ f as bs xs m Q X)
    (hext : ∀ c xs r s s', Pre c xs s → s'.core = s.core → s'.LengthsOk c →
      Post c xs r s s' → FullExtScratchPres s s') :
    ∀ xs m Q X, PolicyFrameSpec Pre Post xs m Q X → Γ f as bs xs m Q X :=
  fun _ _ _ _ h => hΓ _ _ _ _ (PolicyFrameSpec.of_safetySlice hext h)

/-- Transport a `PolicyFrameSpec` proof from `Γ₁` to `Γ₂` using `Fn.callsOk` and pointwise
agreement on allowed callees (thin wrapper around `wp_env_agree_of_callsOk`). -/
theorem policy_wp_transport {Γ₁ Γ₂ : Env} {fn : Fn}
    {Pre : FullCfg → Tup Val fn.as → FullState → Prop}
    {Post : FullCfg → Tup Val fn.as → Tup Val fn.rs → FullState → FullState → Prop}
    {allowed : List SigEntry} {exits : List Sym}
    (hwf : fn.Wf) (hcalls : fn.checkCallsOk allowed exits = true)
    (hagree : ∀ f as bs, (f, as, bs) ∈ allowed →
      ∀ xs m Q X, Γ₁ f as bs xs m Q X → Γ₂ f as bs xs m Q X)
    (hwp : ∀ xs m Q X, PolicyFrameSpec Pre Post xs m Q X → Func.wp Γ₁ fn.body xs m Q X) :
    ∀ xs m Q X, PolicyFrameSpec Pre Post xs m Q X → Func.wp Γ₂ fn.body xs m Q X := by
  intro xs m Q X hs
  exact wp_env_agree_of_callsOk
    (hwf Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units _))
    (Fn.callsOk_of_checkCallsOk hcalls) hagree m (hwp xs m Q X hs)

end PolicyTableHelpers

/-! ## 5. Tier P2: `ArenaClauseSubset`, `WatchSliceFrame`, & `PolicyDeleteSpec` -/

/-- Structural `PH_SHRK`-aware arena layout invariant (independent of formula `F_cur`):
block bounds, `fullArenaNextOff` chaining, and `0xFFFFFFFF` shrink terminators. -/
structure FullArenaLayoutOk (k : FullCoreState) : Prop where
  len_ok : k.arena_len = 0 ∨ 3 ≤ k.arena_len
  refs_wf : ∀ r ∈ fullArenaClauseRefsCore k,
    r + 3 ≤ k.arena_len ∧ 3 ≤ fullArenaClauseSizeCore k r ∧
    r + 3 + fullArenaClauseSizeCore k r ≤ fullArenaNextOff k.arena k.arena_len r ∧
    fullArenaNextOff k.arena k.arena_len r ≤ k.arena_len ∧
    (fullArenaNextOff k.arena k.arena_len r = k.arena_len ∨
     fullArenaNextOff k.arena k.arena_len r + 3 ≤ k.arena_len)
  shrk_term : ∀ r ∈ fullArenaClauseRefsCore k,
    (fullArenaHdrCore k r &&& 0x00800000#32) ≠ 0#32 →
    ∃ t, r + 3 + fullArenaClauseSizeCore k r ≤ t ∧ t < k.arena_len ∧
      k.arena[t]? = some 0xFFFFFFFF#32

/-- **Clause-database deletion frame (`ArenaClauseSubset`)**: every remaining live clause in
`k'` (`garb = false`) was an already-live clause in `k` with the exact same literal sequence. -/
@[expose] def ArenaClauseSubset (k k' : FullCoreState) : Prop :=
  ∀ r ∈ fullArenaClauseRefsCore k', fullArenaClauseGarbCore k' r = false →
    r ∈ fullArenaClauseRefsCore k ∧
    fullArenaClauseGarbCore k r = false ∧
    fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r

/-- Generalized clause-database frame permitting either unchanged live clauses from `k` OR new
clauses explicitly entailed by `F_cur` with bounded literals and `Nodup` variables. -/
@[expose] def ArenaClauseEntailed (F_cur : List (List Nat)) (k k' : FullCoreState) : Prop :=
  ∀ r ∈ fullArenaClauseRefsCore k', fullArenaClauseGarbCore k' r = false →
    (r ∈ fullArenaClauseRefsCore k ∧
      fullArenaClauseGarbCore k r = false ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) ∨
    ((∀ l ∈ fullArenaClauseLitsCore k' r, l < 2 * k'.cur_vars) ∧
      ((fullArenaClauseLitsCore k' r).map (· / 2)).Nodup ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause (fullArenaClauseLitsCore k' r)))

theorem ArenaClauseSubset.toEntailed {F_cur : List (List Nat)} {k k' : FullCoreState}
    (h : ArenaClauseSubset k k') : ArenaClauseEntailed F_cur k k' :=
  fun r hr hg => Or.inl (h r hr hg)

theorem ArenaClauseSubset.refl (k : FullCoreState) : ArenaClauseSubset k k :=
  fun _ hr hg => ⟨hr, hg, rfl⟩

theorem ArenaClauseSubset.trans {k1 k2 k3 : FullCoreState}
    (h12 : ArenaClauseSubset k1 k2) (h23 : ArenaClauseSubset k2 k3) :
    ArenaClauseSubset k1 k3 := by
  intro r hr3 hg3
  obtain ⟨hr2, hg2, hl23⟩ := h23 r hr3 hg3
  obtain ⟨hr1, hg1, hl12⟩ := h12 r hr2 hg2
  exact ⟨hr1, hg1, hl23.trans hl12⟩

theorem fullArenaClausesInv_of_entailed {c : FullCfg} {F_cur : List (List Nat)}
    {k k' : FullCoreState} (ha : FullArenaClausesInv c F_cur k) (hlay : FullArenaLayoutOk k')
    (hvars : k'.cur_vars = k.cur_vars) (hent : ArenaClauseEntailed F_cur k k') :
    FullArenaClausesInv c F_cur k' := by
  refine ⟨hlay.len_ok, hlay.refs_wf, hlay.shrk_term, ?_, ?_⟩
  · intro r hr hg l hl
    rcases hent r hr hg with ⟨hr0, hg0, hleq⟩ | ⟨hlt, _, _⟩
    · rw [hvars]; exact ha.lits_lt r hr0 hg0 l (hleq ▸ hl)
    · exact hlt l hl
  · intro r hr hg
    rcases hent r hr hg with ⟨hr0, hg0, hleq⟩ | ⟨_, _, he⟩
    · rw [hleq]; exact ha.entails r hr0 hg0
    · exact he

theorem fullArenaClausesInv_of_subset {c : FullCfg} {F_cur : List (List Nat)}
    {k k' : FullCoreState} (ha : FullArenaClausesInv c F_cur k) (hlay : FullArenaLayoutOk k')
    (hvars : k'.cur_vars = k.cur_vars) (hsub : ArenaClauseSubset k k') :
    FullArenaClausesInv c F_cur k' :=
  fullArenaClausesInv_of_entailed ha hlay hvars hsub.toEntailed

theorem fullArenaVarsNodup_of_entailed {F_cur : List (List Nat)} {s s' : FullState}
    (hnd : FullArenaVarsNodup s) (hent : ArenaClauseEntailed F_cur s.core s'.core) :
    FullArenaVarsNodup s' := by
  intro r hr hg
  rcases hent r hr hg with ⟨hr0, hg0, hleq⟩ | ⟨_, hnd', _⟩
  · simpa [fullArenaClauseLits, hleq] using hnd r hr0 hg0
  · exact hnd'

theorem fullArenaVarsNodup_of_subset {s s' : FullState}
    (hnd : FullArenaVarsNodup s) (hsub : ArenaClauseSubset s.core s'.core) :
    FullArenaVarsNodup s' := by
  intro r hr hg
  obtain ⟨hr0, hg0, hleq⟩ := hsub r hr hg
  simpa [fullArenaClauseLits, hleq] using hnd r hr0 hg0

private theorem bit31_zero_of_lt {w : BitVec 32} (hw : w.toNat < 0x80000000) :
    (w &&& 0x80000000#32) = 0#32 := by
  have hbit31 : w[31] = false := by
    have hlt : w.toNat < 2 ^ 31 := by omega
    simpa [BitVec.getElem_eq_testBit_toNat] using Nat.testBit_lt_two_pow hlt
  have hmask : ∀ (i : Nat) (hi : i < 32), i ≠ 31 → (0x80000000#32 : BitVec 32)[i] = false := by
    decide
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_zero]
  by_cases h31 : i = 31
  · subst h31; simp [hbit31]
  · simp [hmask i hi h31]

theorem watchSliceOk_bin_mem {F_cur : List (List Nat)} {k : FullCoreState} {lit p rem q : Nat}
    {w0 : BitVec 32} (h : WatchSliceOk F_cur k lit p rem)
    (hpq : p ≤ q) (hq : q < p + rem) (hw : k.wstk[q]? = some w0)
    (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) :
    w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) := by
  induction h generalizing q with
  | empty => omega
  | @bin p rem w_p hp hflag hne hlt hent _ ih =>
    by_cases hqp : q = p
    · subst hqp; rw [hp] at hw; cases hw; exact ⟨hne, hlt, hent⟩
    · exact ih (by omega) (by omega) hw
  | @large p rem w_p cref hp hp1 hflag hlt _ _ ih =>
    by_cases hqp : q = p
    · subst hqp; rw [hp] at hw; cases hw; exact absurd hflag hbin
    · by_cases hqp1 : q = p + 1
      · subst hqp1; rw [hp1] at hw; cases hw
        exact absurd (bit31_zero_of_lt hlt) hbin
      · exact ih (by omega) (by omega) hw

theorem denseWatchSliceOk_bin_mem {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem q : Nat} {w0 : BitVec 32} (h : DenseWatchSliceOk F_cur k lit p rem)
    (hpq : p ≤ q) (hq : q < p + rem) (hw : k.wstk[q]? = some w0)
    (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) :
    w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) := by
  induction h generalizing q with
  | empty => omega
  | @bin p rem w_p hp hflag hne hlt hent _ ih =>
    by_cases hqp : q = p
    · subst hqp; rw [hp] at hw; cases hw; exact ⟨hne, hlt, hent⟩
    · exact ih (by omega) (by omega) hw
  | @occ p rem w_p cref hp hp1 hflag _ hlt _ _ ih =>
    by_cases hqp : q = p
    · subst hqp; rw [hp] at hw; cases hw; exact absurd hflag hbin
    · by_cases hqp1 : q = p + 1
      · subst hqp1; rw [hp1] at hw; cases hw
        exact absurd (bit31_zero_of_lt hlt) hbin
      · exact ih (by omega) (by omega) hw

/-- Structural watch-slice frame for deletion (`reduce`) and watch reordering (`tumble`):
every binary watch in `k'`'s slice for `lit` appeared in `k`'s slice, and every large/occ
watch `(w0, cref)` has valid `cref ∈ fullArenaClauseRefsCore k'`. -/
inductive WatchSliceFrame (k k' : FullCoreState) (lit : Nat) : Nat → Nat → Prop where
  | empty {p} : WatchSliceFrame k k' lit p 0
  | bin {p rem w0} :
      k'.wstk[p]? = some w0 → (w0 &&& 0x80000000#32) ≠ 0#32 →
      (∃ q, fullWatchOffCore k lit ≤ q ∧ q < fullWatchOffCore k lit + fullWatchSizeCore k lit ∧
        k.wstk[q]? = some w0) →
      WatchSliceFrame k k' lit (p + 1) rem →
      WatchSliceFrame k k' lit p (rem + 1)
  | large {p rem w0 cref} :
      k'.wstk[p]? = some w0 → k'.wstk[p + 1]? = some cref →
      (w0 &&& 0x80000000#32) = 0#32 → cref.toNat < 0x80000000 →
      (k'.dense_mode ≠ 0#64 → 3 ≤ w0.toNat) →
      cref.toNat ∈ fullArenaClauseRefsCore k' →
      WatchSliceFrame k k' lit (p + 2) rem →
      WatchSliceFrame k k' lit p (rem + 2)

theorem watchSliceOk_of_frame {F_cur : List (List Nat)} {k k' : FullCoreState} {lit p rem : Nat}
    (hdm : k.dense_mode = 0#64) (_hdm' : k'.dense_mode = 0#64) (hvars : k'.cur_vars = k.cur_vars)
    (hw_old : ModeWatchesInv F_cur k) (hlit : lit < 2 * k.cur_vars)
    (hf : WatchSliceFrame k k' lit p rem) : WatchSliceOk F_cur k' lit p rem := by
  have hs_old : WatchSliceOk F_cur k lit (fullWatchOffCore k lit) (fullWatchSizeCore k lit) := by
    simp only [ModeWatchesInv, hdm, ↓reduceIte] at hw_old
    exact hw_old.slices lit hlit
  induction hf with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hq _ ih =>
    obtain ⟨q, hq1, hq2, hqw⟩ := hq
    obtain ⟨hne, hlt, hent⟩ := watchSliceOk_bin_mem hs_old hq1 hq2 hqw hflag
    exact .bin hp hflag hne (hvars ▸ hlt) hent ih
  | @large p rem w0 cref hp hp1 hflag hlt _ href _ ih =>
    exact .large hp hp1 hflag hlt href ih

theorem denseWatchSliceOk_of_frame {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p rem : Nat} (hdm : k.dense_mode ≠ 0#64) (hdm' : k'.dense_mode ≠ 0#64)
    (hvars : k'.cur_vars = k.cur_vars) (hw_old : ModeWatchesInv F_cur k)
    (hlit : lit < 2 * k.cur_vars)
    (hf : WatchSliceFrame k k' lit p rem) : DenseWatchSliceOk F_cur k' lit p rem := by
  have hs_old : DenseWatchSliceOk F_cur k lit
      (fullWatchOffCore k lit) (fullWatchSizeCore k lit) := by
    simp only [ModeWatchesInv, ite_eq_right hdm] at hw_old
    exact hw_old.slices lit hlit
  induction hf with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hq _ ih =>
    obtain ⟨q, hq1, hq2, hqw⟩ := hq
    obtain ⟨hne, hlt, hent⟩ := denseWatchSliceOk_bin_mem hs_old hq1 hq2 hqw hflag
    exact .bin hp hflag hne (hvars ▸ hlt) hent ih
  | @large p rem w0 cref hp hp1 hflag hlt h3 href _ ih =>
    exact .occ hp hp1 hflag (h3 hdm') hlt href ih

/-- Combined watch-frame condition for clause deletion / watch-reordering: either the watch
vectors/stack are untouched (with `refs` subset, e.g. `markGarb`), or `WatchStackLayout k'` and
`WatchSliceFrame k k' lit` hold for every literal `< 2 * k'.cur_vars`. -/
@[expose] def WatchesFrameOk (k k' : FullCoreState) : Prop :=
  (k'.wvec = k.wvec ∧ k'.wstk = k.wstk ∧ k'.wlen = k.wlen ∧
    ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k') ∨
  (WatchStackLayout k' ∧
    ∀ lit < 2 * k'.cur_vars,
      WatchSliceFrame k k' lit (fullWatchOffCore k' lit) (fullWatchSizeCore k' lit))

theorem modeWatchesInv_of_frame {F_cur : List (List Nat)} {k k' : FullCoreState}
    (hw : ModeWatchesInv F_cur k) (hdm : k'.dense_mode = k.dense_mode)
    (hvars : k'.cur_vars = k.cur_vars) (hf : WatchesFrameOk k k') :
    ModeWatchesInv F_cur k' := by
  rcases hf with ⟨hwv, hws, hwl, hrefs⟩ | ⟨hlay, hsf⟩
  · exact hw.with_wstk hdm hvars hwv hws hwl hrefs
  · by_cases hc : k.dense_mode = 0#64
    · have hc' : k'.dense_mode = 0#64 := hdm.trans hc
      simp only [ModeWatchesInv, hc', ↓reduceIte]
      exact ⟨hlay, fun l hl =>
        watchSliceOk_of_frame hc hc' hvars hw (hvars ▸ hl) (hsf l hl)⟩
    · have hc' : k'.dense_mode ≠ 0#64 := fun h => hc (hdm.symm.trans h)
      simp only [ModeWatchesInv, ite_eq_right hc']
      exact ⟨hlay, fun l hl =>
        denseWatchSliceOk_of_frame hc hc' hvars hw (hvars ▸ hl) (hsf l hl)⟩

/-- Erase policy fields AND clause-database / watch fields (`arena`, `arena_len`, `wvec`, `wstk`,
`wlen`) to verify trail/assignment/level/reason/mark invariance across Tier-P2 deletions. -/
@[expose] def soundDeleteMask (k : FullCoreState) : FullCoreState :=
  { policyUpd k PolicyCore.zero with
    arena := [], arena_len := 0, wvec := [], wstk := [], wlen := 0 }

/-- Active trail large reasons remain live and unaltered in `k'`. -/
@[expose] def ActiveReasonsPres (k k' : FullCoreState) : Prop :=
  ∀ idx < k.trail_end,
    let p := (k.trl[idx]?.getD 0#32).toNat
    let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
    rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
      rsn.toNat ∈ fullArenaClauseRefsCore k' ∧
      fullArenaClauseGarbCore k' rsn.toNat = false ∧
      fullArenaClauseLitsCore k' rsn.toNat = fullArenaClauseLitsCore k rsn.toNat

/-- `last_learned[0 ..< 8]` slots stay `0xFFFFFFFF#32` or valid refs in `s'`. -/
@[expose] def LastLearnedSub (_s s' : FullState) : Prop :=
  ∀ i < 8,
    let cr := s'.scratch.last_learned[i]?.getD 0xFFFFFFFF#32
    cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ fullArenaClauseRefs s'

/-- Tier-P2 clause-deletion / watch-reordering transition predicate. -/
structure PolicyDeleteStep (s s' : FullState) : Prop where
  mask_eq : soundDeleteMask s'.core = soundDeleteMask s.core
  extend_len_eq : s'.scratch.extend_len = s.scratch.extend_len
  last_learned_sub : LastLearnedSub s s'
  arena_layout : FullArenaLayoutOk s'.core
  arena_subset : ArenaClauseSubset s.core s'.core
  active_reasons : ActiveReasonsPres s.core s'.core
  watches_ok : WatchesFrameOk s.core s'.core

private theorem soundDeleteMask_fields {k k' : FullCoreState}
    (h : soundDeleteMask k' = soundDeleteMask k) :
    k'.cur_vars = k.cur_vars ∧ k'.inconsistent = k.inconsistent ∧
    k'.dense_mode = k.dense_mode ∧ k'.cur_level = k.cur_level ∧
    k'.trail_end = k.trail_end ∧ k'.vals = k.vals ∧ k'.lit_mark = k.lit_mark ∧
    k'.mrk = k.mrk ∧ k'.lvl = k.lvl ∧ k'.rsns = k.rsns ∧ k'.trl = k.trl ∧
    k'.trail_pos = k.trail_pos ∧ k'.frame_trail = k.frame_trail ∧ k'.frame_dec = k.frame_dec := by
  have hc := congrArg FullCoreState.cur_vars h
  have hi := congrArg FullCoreState.inconsistent h
  have hd := congrArg FullCoreState.dense_mode h
  have hl := congrArg FullCoreState.cur_level h
  have ht := congrArg FullCoreState.trail_end h
  have hv := congrArg FullCoreState.vals h
  have hm := congrArg FullCoreState.lit_mark h
  have hk := congrArg FullCoreState.mrk h
  have hv2 := congrArg FullCoreState.lvl h
  have hr := congrArg FullCoreState.rsns h
  have hl2 := congrArg FullCoreState.trl h
  have hp := congrArg FullCoreState.trail_pos h
  have hft := congrArg FullCoreState.frame_trail h
  have hfd := congrArg FullCoreState.frame_dec h
  dsimp only [soundDeleteMask, policyUpd] at hc hi hd hl ht hv hm hk hv2 hr hl2 hp hft hfd
  exact ⟨hc, hi, hd, hl, ht, hv, hm, hk, hv2, hr, hl2, hp, hft, hfd⟩

/-- Every `PolicyStep` (Tiers P0/P1) from a `FullSparseInv` state induces a `PolicyDeleteStep`
(Tier P2). -/
theorem PolicyDeleteStep.of_policyStep {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullSparseInv c F0 s) (hp : PolicyStep s s') : PolicyDeleteStep s s' := by
  obtain ⟨_, hw⟩ := h.1.witness
  have hcore := hp.core_eq_policyUpd
  have hll_wf := h.2.2.2.1.1
  refine ⟨?_, hp.extPres.2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcore]; rfl
  · intro i hi
    have hll_i := hll_wf i hi
    have hget : s'.scratch.last_learned[i]? = s.scratch.last_learned[i]? :=
      congrArg (·[i]?) hp.extPres.1
    dsimp only at hll_i ⊢
    rw [hget]
    rcases hll_i with hsent | href
    · exact Or.inl hsent
    · exact Or.inr ((fullArenaClauseRefs_of_policyStep hp).symm ▸ href)
  · rw [hcore]; exact ⟨hw.arena.len_ok, hw.arena.refs_wf, hw.arena.shrk_term⟩
  · rw [hcore]; exact ArenaClauseSubset.refl _
  · intro idx hidx; dsimp only; intro hne hlg
    have hrs := hw.reason_inv idx hidx hne
    dsimp only at hrs
    rw [ite_eq_right (fun hf => absurd hlg hf)] at hrs
    rw [hcore]
    exact ⟨hrs.1, hrs.2.1, rfl⟩
  · rw [hcore]; exact Or.inl ⟨rfl, rfl, rfl, fun _ hr => hr⟩

private theorem fullWitnessInv_of_delete_entailed {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k k' : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (hmask : soundDeleteMask k' = soundDeleteMask k) (hlay : FullArenaLayoutOk k')
    (hent : ArenaClauseEntailed F_cur k k') (hact : ActiveReasonsPres k k')
    (hwat : WatchesFrameOk k k') :
    FullWitnessInv c F0 F_cur k' := by
  obtain ⟨hcv, hinc, hdm, hcl, hte, hvals, hlm, hmrk, hlvl, hrsns, htrl, htp, hft, hfd⟩ :=
    soundDeleteMask_fields hmask
  refine
    { ext_sound := hcv ▸ hw.ext_sound
      inconsistent_sound := hinc ▸ hw.inconsistent_sound
      arena := fullArenaClausesInv_of_entailed hw.arena hlay hcv hent
      watches := modeWatchesInv_of_frame hw.watches hdm hcv hwat
      cur_level_le := hcl ▸ hte ▸ hw.cur_level_le
      trail_lits_lt := hcv ▸ hte ▸ htrl ▸ hw.trail_lits_lt
      trail_vars_nodup := hte ▸ htrl ▸ hw.trail_vars_nodup
      vals_domain := hcv ▸ hvals ▸ hw.vals_domain
      vals_true_iff := hcv ▸ hte ▸ hvals ▸ htrl ▸ hw.vals_true_iff
      vals_false_iff := hcv ▸ hte ▸ hvals ▸ htrl ▸ hw.vals_false_iff
      lvl_le := hcl ▸ hte ▸ hlvl ▸ htrl ▸ hw.lvl_le
      dec_earliest := hte ▸ hlvl ▸ hrsns ▸ htrl ▸ hw.dec_earliest
      levels_inhabited := hcl ▸ hte ▸ hlvl ▸ htrl ▸ hw.levels_inhabited
      level0_sound := hte ▸ hlvl ▸ htrl ▸ hw.level0_sound
      trail_pos_inv := hte ▸ htrl ▸ htp ▸ hw.trail_pos_inv
      level0_rsn_none := hte ▸ hlvl ▸ hrsns ▸ htrl ▸ hw.level0_rsn_none
      frame_trail_lt := hcl ▸ hte ▸ hft ▸ hw.frame_trail_lt
      frame_trail_mono := hcl ▸ hft ▸ hw.frame_trail_mono
      frame_trail_before_lt := hcl ▸ hlvl ▸ htrl ▸ hft ▸ hw.frame_trail_before_lt
      frame_dec_lt := hcv ▸ hcl ▸ hfd ▸ hw.frame_dec_lt
      reason_inv := ?_
      reason_lit_mem := ?_ }
  · intro idx hidx; dsimp only; intro hne
    have hidx0 : idx < k.trail_end := hte ▸ hidx
    have hne0 : k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      simpa [htrl, hrsns] using hne
    have hrs := hw.reason_inv idx hidx0 hne0
    dsimp only at hrs
    rw [htrl, hrsns, hcv, hlvl]
    by_cases hbin : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
    · rw [ite_eq_left hbin] at hrs ⊢; exact hrs
    · have hlg : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32 :=
        Classical.byContradiction fun hn => hbin hn
      rw [ite_eq_right hbin] at hrs ⊢
      obtain ⟨href', hgarb', hlits'⟩ := hact idx hidx0 hne0 hlg
      exact ⟨href', hgarb', fun q hq => hrs.2.2 q (hlits' ▸ hq)⟩
  · intro idx hidx; dsimp only; intro hne hlg
    have hidx0 : idx < k.trail_end := hte ▸ hidx
    have hne0 : k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      simpa [htrl, hrsns] using hne
    have hlg0 : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32 := by
      simpa [htrl, hrsns] using hlg
    obtain ⟨_, _, hlits'⟩ := hact idx hidx0 hne0 hlg0
    rw [htrl, hrsns, hlits']
    exact hw.reason_lit_mem idx hidx0 hne0 hlg0

theorem fullWitnessInv_of_policyDeleteStep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hd : PolicyDeleteStep s s') :
    FullWitnessInv c F0 F_cur s'.core :=
  fullWitnessInv_of_delete_entailed hw hd.mask_eq hd.arena_layout hd.arena_subset.toEntailed
    hd.active_reasons hd.watches_ok

theorem fullCoreInv_of_policyDeleteStep {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullCoreInv c F0 s) (hlen : s'.LengthsOk c) (hd : PolicyDeleteStep s s') :
    FullCoreInv c F0 s' :=
  let ⟨F_cur, hw⟩ := h.witness
  ⟨hlen, F_cur, fullWitnessInv_of_policyDeleteStep hw hd⟩

theorem fullSparseInv_of_policyDeleteStep {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullSparseInv c F0 s) (hlen : s'.LengthsOk c) (hd : PolicyDeleteStep s s') :
    FullSparseInv c F0 s' := by
  obtain ⟨_, _, _, _, _, _, hlm, hmrk, _, _, _, _, _, _⟩ := soundDeleteMask_fields hd.mask_eq
  refine ⟨fullCoreInv_of_policyDeleteStep h.1 hlen hd, ?_,
    fullArenaVarsNodup_of_subset h.2.2.1 hd.arena_subset, ?_, ?_⟩
  · refine ⟨fun v hv => ?_, fun l hl => ?_⟩
    · rw [hmrk]; exact h.2.1.1 v hv
    · rw [hlm]; exact h.2.1.2 l hl
  · exact ⟨fun i hi => hd.last_learned_sub i hi, hd.extend_len_eq ▸ h.2.2.2.1.2⟩
  · have hdm := (soundDeleteMask_fields hd.mask_eq).2.2.1
    exact hdm.trans h.2.2.2.2

theorem fullSparseInvW_of_policyDeleteStep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullSparseInvW c F0 F_cur s) (hlen : s'.LengthsOk c)
    (hd : PolicyDeleteStep s s') : FullSparseInvW c F0 F_cur s' := by
  obtain ⟨_, _, hdm, _, _, _, hlm, hmrk, _, _, _, _, _, _⟩ := soundDeleteMask_fields hd.mask_eq
  refine ⟨hlen, fullWitnessInv_of_policyDeleteStep h.2.1 hd, ?_,
    fullArenaVarsNodup_of_subset h.2.2.2.1 hd.arena_subset,
    ⟨fun i hi => hd.last_learned_sub i hi, hd.extend_len_eq ▸ h.2.2.2.2.1.2⟩,
    hdm.trans h.2.2.2.2.2⟩
  refine ⟨fun v hv => ?_, fun l hl => ?_⟩
  · rw [hmrk]; exact h.2.2.1.1 v hv
  · rw [hlm]; exact h.2.2.1.2 l hl

theorem fullM6HdrInv_of_policyDeleteStep {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s s' : FullState} (h : FullM6HdrInv c F0 ext s) (hlen : s'.LengthsOk c)
    (hd : PolicyDeleteStep s s') : FullM6HdrInv c F0 ext s' :=
  FullM6HdrInv.mk_inv h.cfgOk h.extOk (fullSparseInv_of_policyDeleteStep h.sparse hlen hd)

theorem fullM6HdrInvW_of_policyDeleteStep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s s' : FullState} (h : FullM6HdrInvW c F0 F_cur ext s)
    (hlen : s'.LengthsOk c) (hd : PolicyDeleteStep s s') : FullM6HdrInvW c F0 F_cur ext s' :=
  FullM6HdrInvW.mk_inv h.cfgOk h.extOk (fullSparseInvW_of_policyDeleteStep h.sparseW hlen hd)

/-- **UNSAT soundness is invariant under clause deletions & watch reordering (`PolicyDeleteStep`)**.
-/
theorem policyDeleteStep_unsat_sound {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s s' : FullState} (h : FullM6HdrInv c F0 ext s) (hlen : s'.LengthsOk c)
    (hd : PolicyDeleteStep s s') (hinc : s'.core.inconsistent ≠ 0#64) : F0.Unsat :=
  fullM6HdrInv_inconsistent_unsat (fullM6HdrInv_of_policyDeleteStep h hlen hd) hinc

/-- Tier-P2 specification builder (`PolicyDeleteSpec Pre Post`) for clause deletion / reduction /
watch-reordering functions (`reduce`, `tumble`, `arena_sweep`, etc.). -/
@[expose] def PolicyDeleteSpec {as rs : List Ty}
    (Pre : FullCfg → Tup Val as → FullState → Prop)
    (Post : FullCfg → Tup Val as → Tup Val rs → FullState → FullState → Prop :=
      fun _ _ _ _ _ => True) : Spec as rs :=
  fun xs m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      Pre c xs s ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ (r : Tup Val rs) (s' : FullState) (m' : Mem 64),
        PolicyDeleteStep s s' → s'.LengthsOk c → Post c xs r s s' →
        (FullMem c s' ⋆ R) m' → Q r m'

namespace PolicyDeleteSpec

theorem mono {as rs : List Ty}
    {Pre : FullCfg → Tup Val as → FullState → Prop}
    {PostFn : FullCfg → Tup Val as → Tup Val rs → FullState → FullState → Prop} :
    (PolicyDeleteSpec Pre PostFn).Mono := by
  rintro xs m Q Q' X X' hQ _ ⟨c, s, R, hpre, hlen, hm, hk⟩
  exact ⟨c, s, R, hpre, hlen, hm, fun r s' m' hd hs' hp hm' => hQ r m' (hk r s' m' hd hs' hp hm')⟩

theorem noExit {as rs : List Ty}
    {Pre : FullCfg → Tup Val as → FullState → Prop}
    {PostFn : FullCfg → Tup Val as → Tup Val rs → FullState → FullState → Prop}
    {xs : Tup Val as} {m : Mem 64} {Q : LeanQbe.T.Post rs} {X X' : XPost}
    (h : PolicyDeleteSpec Pre PostFn xs m Q X) :
    PolicyDeleteSpec Pre PostFn xs m Q X' :=
  h

theorem frame {as rs : List Ty}
    {Pre : FullCfg → Tup Val as → FullState → Prop}
    {PostFn : FullCfg → Tup Val as → Tup Val rs → FullState → FullState → Prop}
    {xs : Tup Val as} {m : Mem 64} {Q : LeanQbe.T.Post rs} {X : XPost} {F : Mem 64 → Prop}
    (h : ((fun m₁ => PolicyDeleteSpec Pre PostFn xs m₁ Q X) ⋆ F) m) :
    PolicyDeleteSpec Pre PostFn xs m (fun r m' => (Q r ⋆ F) m') X := by
  unfold PolicyDeleteSpec at h ⊢
  obtain ⟨c, h⟩ := sep_ex_l.mp h
  obtain ⟨s, h⟩ := sep_ex_l.mp h
  obtain ⟨R, h⟩ := sep_ex_l.mp h
  obtain ⟨hpre, h⟩ := sep_pure_l.mp h
  obtain ⟨hlen, h⟩ := sep_pure_l.mp h
  obtain ⟨hk, hmF⟩ := sep_pure_l.mp (sep_mono (fun _ hx => ⟨hx.2, hx.1⟩) h)
  refine ⟨c, s, R ⋆ F, hpre, hlen, by ecancel, fun r s' m' hd hs' hp hm' => ?_⟩
  have hm'' : ((FullMem c s' ⋆ R) ⋆ F) m' := by ecancel
  exact sep_mono (fun _ hsm' => hk r s' _ hd hs' hp hsm') hm''

theorem weaken {as rs : List Ty}
    {Pre₁ Pre₂ : FullCfg → Tup Val as → FullState → Prop}
    {Post₁ Post₂ : FullCfg → Tup Val as → Tup Val rs → FullState → FullState → Prop}
    (hPre : ∀ c xs s, Pre₁ c xs s → Pre₂ c xs s)
    (hPost : ∀ c xs r s s', Pre₁ c xs s → PolicyDeleteStep s s' → s'.LengthsOk c →
      Post₂ c xs r s s' → Post₁ c xs r s s')
    {xs : Tup Val as} {m : Mem 64} {Q : LeanQbe.T.Post rs} {X : XPost}
    (h : PolicyDeleteSpec Pre₁ Post₁ xs m Q X) :
    PolicyDeleteSpec Pre₂ Post₂ xs m Q X := by
  rcases h with ⟨c, s, R, hpre, hlen, hm, hk⟩
  exact ⟨c, s, R, hPre c xs s hpre, hlen, hm, fun r s' m' hd hlen' hp2 hm' =>
    hk r s' m' hd hlen' (hPost c xs r s s' hpre hd hlen' hp2) hm'⟩

theorem frame_m6HdrInv {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {as rs : List Ty}
    {Pre : FullCfg → Tup Val as → FullState → Prop}
    {PostFn : FullCfg → Tup Val as → Tup Val rs → FullState → FullState → Prop}
    {xs : Tup Val as} {Q : LeanQbe.T.Post rs} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hpre : Pre c xs s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r s' m', FullM6HdrInv c F0 ext s' → PolicyDeleteStep s s' → PostFn c xs r s s' →
      (FullM6HdrMem c ext s' ⋆ R) m' → Q r m') :
    PolicyDeleteSpec Pre PostFn xs m Q X :=
  ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, hpre, hinv.sparse.lengths,
    fullM6HdrMem_focus_full hm, fun r s' m' hd hlen' hpost hm' =>
      hk r s' m' (fullM6HdrInv_of_policyDeleteStep hinv hlen' hd) hd hpost
        (fullM6HdrMem_unfocus_full hm')⟩

end PolicyDeleteSpec

/-- Call a `PolicyDeleteSpec` callee directly under `FullM6HdrInv`, transporting `FullM6HdrInv`.
-/
theorem wp_policyDelete_call_m6HdrInv {Γ : Env} {f : Sym} {as bs ret : List Ty}
    {args : Tup (Arg Val) as} {k : Tup Val bs → Expr Val Cont ret} {m : Mem 64}
    {Pre : FullCfg → Tup Val as → FullState → Prop}
    {PostFn : FullCfg → Tup Val as → Tup Val bs → FullState → FullState → Prop}
    (hCallee : ∀ xs m Q X, PolicyDeleteSpec Pre PostFn xs m Q X → Γ f as bs xs m Q X)
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop}
    {Q : LeanQbe.T.Post ret} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hpre : Pre c (vals args) s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r s' m', FullM6HdrInv c F0 ext s' → PolicyDeleteStep s s' →
      PostFn c (vals args) r s s' → (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k r) m') :
    wp Γ Q X (.call f args k) m :=
  wp_call_of_spec args k (hCallee _ m _ X (PolicyDeleteSpec.frame_m6HdrInv hinv hpre hm hk))

end LeanQbe.T.Examples.Kissat.PolicyFrame
