module

public import LeanQbe.T.Examples.Kissat.FullM6BcpS15
public import LeanQbe.T.Examples.Kissat.FullFastCoreBcpLemmas1

/-!
# Kissat M6 `S1.5` Delayed-Watch BCP Specifications & Overflow Proof (`FullM6BcpS15Proof1`)

Defines the `S1.5` delayed-watch BCP specifications (`fullPropLitOvfS15Spec`,
`fullPropLitS15Spec`, `fullPropagateIgnoreS15Spec`, `fullBcpS15Spec`), in-place sentinel/end
watch-append layout lemmas, delayed-watch flush invariants, and proves `full_prop_lit_ovf_s15_wp`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6BcpS15

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FastCore
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Full hiding
  full_prop_lit_body full_prop_lit_wf full_prop_lit_wp
  full_propagate_ignore_body full_propagate_ignore_wf full_propagate_ignore_wp
  full_propagate_body full_propagate_wf full_propagate_wp
open LeanQbe.T.Examples.Kissat.Full.FullPropDecSpecs hiding
  fullPropLitSpec fullPropagateIgnoreSpec fullPropagateSpec fullWatchPushSpec
  FullTrailExt FullArenaPermEq
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

attribute [local irreducible] fastPropMem

local macro "s15_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

local elab "s15_head_steps" : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)))
  fcHeadRun false

local elab "s15_head_split" : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)))
  fcHeadRun true

/-! ## 1. `S1.5` Specifications & Delayed-Watch Invariant -/

/-- Valid pending delayed-watch entries `del[0 ..< 3 * dlen)`: each triple `(repl, w0, cref)`
targets a distinct literal `repl ≠ skip_lit` within `2 * cur_vars` with valid large-watch words. -/
@[expose] def DelayedWatchesOk (k : FullCoreState) (del : List (BitVec 32))
    (dlen skip_lit : Nat) : Prop :=
  ∀ j < dlen,
    let repl := (del[3 * j]?.getD 0#32).toNat
    let w0 := del[3 * j + 1]?.getD 0#32
    let cref := del[3 * j + 2]?.getD 0#32
    repl < 2 * k.cur_vars ∧ repl ≠ skip_lit ∧
    (w0 &&& 0x80000000#32) = 0#32 ∧ cref.toNat < 0x80000000 ∧
    cref.toNat ∈ fullArenaClauseRefsCore k

/-- Contract for cold overflow handler `full_prop_lit_ovf_s15`: flushes `del[0 ..< di)` and
finishes scanning `[off + pr ..< off + sz)` without modifying `h->delayed`. -/
@[expose] def fullPropLitOvfS15Spec :
    Spec [i64, i32, i64, i64, i64, i64] [.bool] :=
  fun (h, not_lit, ignore_ref, pr, qr, di, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop)
      (dlen : Nat),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur (withEmptyWatchesCore c s.core) ∧
      s.core.dense_mode = 0#64 ∧ s.core.oom = 0#64 ∧
      not_lit.toNat < 2 * s.core.cur_vars ∧
      s.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 ∧
      SplitWatchesInv F_cur s.core not_lit.toNat
        (fullWatchOffCore s.core not_lit.toNat)
        (fullWatchOffCore s.core not_lit.toNat + qr.toNat)
        (fullWatchOffCore s.core not_lit.toNat + pr.toNat)
        (fullWatchOffCore s.core not_lit.toNat + fullWatchSizeCore s.core not_lit.toNat) ∧
      di.toNat = 3 * dlen ∧ dlen ≤ c.delayed_cap ∧
      DelayedWatchesOk s.core s.scratch.delayed dlen not_lit.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' arena' wstk' wlen' wu'
        ctype' cref' c0' c1' oom' ticks' wsort' phases' m',
        let s' : FullState :=
          { s with
            core :=
              { s.core with
                vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                confl_type := ctype', confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                oom := oom' }
            scratch :=
              { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } }
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
        (ok = false → oom' ≠ 0#64 ∨
          (FullConflictOkW F_cur s' ∧ (ctype' = 2#64 → cref' ≠ ignore_ref))) →
        (ok = true → oom' = 0#64 ∧ ctype' = s.core.confl_type) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- `S1.5` contract for `full_prop_lit_raw_s15`: identical to `Full.fullPropLitSpec` except
permitting updates to `s'.scratch.delayed` (while leaving `h->delayed_len` and all other scratch
fields untouched, and leaving `delayed` unchanged whenever `c.delayed_cap = 0`). -/
@[expose] def fullPropLitS15Spec : Spec [i64, i32, i64] [.bool] :=
  fun (h, _lit, ignore_ref, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      s.core.dense_mode = 0#64 ∧ s.core.oom = 0#64 ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' arena' wstk' wlen' wu'
        ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m',
        let s' : FullState :=
          { s with
            core :=
              { s.core with
                vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                confl_type := ctype', confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                oom := oom' }
            scratch :=
              { s.scratch with
                search_ticks := ticks', wsort := wsort', phases := phases', delayed := delayed' } }
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
        (c.delayed_cap = 0 → delayed' = s.scratch.delayed) →
        (ok = false → oom' ≠ 0#64 ∨
          (FullConflictOkW F_cur s' ∧ (ctype' = 2#64 → cref' ≠ ignore_ref))) →
        (ok = true → oom' = 0#64 ∧ ctype' = s.core.confl_type) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- `S1.5` contract for `full_propagate_ignore_s15`: identical to `Full.fullPropagateIgnoreSpec`
except permitting `s'.scratch.delayed` scratch-buffer updates (`c.delayed_cap = 0 → unchanged`). -/
@[expose] def fullPropagateIgnoreS15Spec : Spec [i64, i64] [i64] :=
  fun (h, ignore_ref, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
      ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
        fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m',
        let s' : FullState :=
          { s with
            core :=
              { s.core with
                vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
                unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
                confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
            scratch :=
              { s.scratch with
                search_ticks := ticks', wsort := wsort', phases := phases', delayed := delayed' } }
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
        (c.delayed_cap = 0 → delayed' = s.scratch.delayed) →
        fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
        (r = 0#64 → prop' = te' ∧ ctype' = s.core.confl_type ∧
          (s.core.oom = 0#64 → oom' = 0#64) ∧
          (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
        (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s' ∧
          (ctype' = 2#64 → cref' ≠ ignore_ref)) →
        (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
        (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `S1.5` contract for `full_bcp_s15`: identical to `Full.fullPropagateSpec` except permitting
`s'.scratch.delayed` scratch-buffer updates (`c.delayed_cap = 0 → unchanged`). -/
@[expose] def fullBcpS15Spec : Spec [i64] [i64] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
      ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
        fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m',
        let s' : FullState :=
          { s with
            core :=
              { s.core with
                vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
                unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
                confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
            scratch :=
              { s.scratch with
                search_ticks := ticks', wsort := wsort', phases := phases', delayed := delayed' } }
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
        (c.delayed_cap = 0 → delayed' = s.scratch.delayed) →
        fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
        (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
          (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
        (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s') →
        (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
        (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ## 2. `fastPropMem`, Delayed-Buffer, & In-Place Watch-Append Layout Lemmas -/

theorem fastPropMem_delayed (s0 sem : FullState) :
    (fastPropMem s0 sem).scratch.delayed = sem.scratch.delayed := by
  rw [fastPropMem_def]

theorem fastPropMem_with_delayed (s0 sem : FullState) (d' : List (BitVec 32)) :
    { fastPropMem s0 sem with scratch := { (fastPropMem s0 sem).scratch with delayed := d' } } =
      fastPropMem s0 { sem with scratch := { sem.scratch with delayed := d' } } := by
  rw [fastPropMem_def, fastPropMem_def]

theorem fastPropMem_with_wvec_wstk_wu (s0 sem : FullState)
    (ar' ws' wv' : List (BitVec 32)) (wu' : BitVec 64) :
    { fastPropMem s0 sem with
      core := { (fastPropMem s0 sem).core with
        arena := ar', wstk := ws', wvec := wv', wusable := wu' } } =
      fastPropMem s0 { sem with
        core := { sem.core with arena := ar', wstk := ws', wvec := wv', wusable := wu' } } := by
  rw [fastPropMem_def, fastPropMem_def]

theorem fastPropMem_with_wvec_wstk_wl (s0 sem : FullState)
    (ar' ws' wv' : List (BitVec 32)) (wl' : Nat) :
    { fastPropMem s0 sem with
      core := { (fastPropMem s0 sem).core with
        arena := ar', wstk := ws', wvec := wv', wlen := wl' } } =
      fastPropMem s0 { sem with
        core := { sem.core with arena := ar', wstk := ws', wvec := wv', wlen := wl' } } := by
  rw [fastPropMem_def, fastPropMem_def]

theorem fastPropMem_sync_eq (s0 sem : FullState) (ticks' : BitVec 64) :
    FullState.mk
      { (fastPropMem s0 sem).core with
        trail_end := sem.core.trail_end, unassigned := sem.core.unassigned,
        unflushed := sem.core.unflushed }
      { (fastPropMem s0 sem).scratch with search_ticks := ticks' } =
      { sem with scratch := { sem.scratch with search_ticks := ticks' } } := by
  rw [fastPropMem_def]

theorem fastPropMem_s_delayed_irrel (s0 sem : FullState) (d' : List (BitVec 32)) :
    fastPropMem { s0 with scratch := { s0.scratch with delayed := d' } } sem =
      fastPropMem s0 sem := by
  rw [fastPropMem_def, fastPropMem_def]

theorem delayedWatchesOk_congr {k1 k2 : FullCoreState} {del : List (BitVec 32)}
    {dlen skip : Nat} (hcv : k2.cur_vars = k1.cur_vars)
    (href : fullArenaClauseRefsCore k2 = fullArenaClauseRefsCore k1)
    (h : DelayedWatchesOk k1 del dlen skip) : DelayedWatchesOk k2 del dlen skip := by
  intro j hj
  obtain ⟨h1, h2, h3, h4, h5⟩ := h j hj
  exact ⟨hcv ▸ h1, h2, h3, h4, href ▸ h5⟩

theorem delayedWatchesOk_push {k : FullCoreState} {del : List (BitVec 32)}
    {dlen skip : Nat} {repl w0 cref : BitVec 32}
    (h : DelayedWatchesOk k del dlen skip) (hfit : 3 * dlen + 2 < del.length)
    (hrepl : repl.toNat < 2 * k.cur_vars) (hne : repl.toNat ≠ skip)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hcr_lt : cref.toNat < 0x80000000)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore k) :
    DelayedWatchesOk k
      (((del.set (3 * dlen) repl).set (3 * dlen + 1) w0).set (3 * dlen + 2) cref)
      (dlen + 1) skip := by
  intro j hj
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
  · have h0 : (((del.set (3 * dlen) repl).set (3 * dlen + 1) w0).set (3 * dlen + 2) cref)[
        3 * j]? = del[3 * j]? := by
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega)]
    have h1 : (((del.set (3 * dlen) repl).set (3 * dlen + 1) w0).set (3 * dlen + 2) cref)[
        3 * j + 1]? = del[3 * j + 1]? := by
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega)]
    have h2 : (((del.set (3 * dlen) repl).set (3 * dlen + 1) w0).set (3 * dlen + 2) cref)[
        3 * j + 2]? = del[3 * j + 2]? := by
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega)]
    dsimp only; rw [h0, h1, h2]; exact h j hlt
  · subst j
    have h0 : (((del.set (3 * dlen) repl).set (3 * dlen + 1) w0).set (3 * dlen + 2) cref)[
        3 * dlen]? = some repl := by
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by omega)]
    have h1 : (((del.set (3 * dlen) repl).set (3 * dlen + 1) w0).set (3 * dlen + 2) cref)[
        3 * dlen + 1]? = some w0 := by
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
    have h2 : (((del.set (3 * dlen) repl).set (3 * dlen + 1) w0).set (3 * dlen + 2) cref)[
        3 * dlen + 2]? = some cref := by
      rw [List.getElem?_set_self (by simp; omega)]
    dsimp only; rw [h0, h1, h2, Option.getD_some, Option.getD_some, Option.getD_some]
    exact ⟨hrepl, hne, hflag, hcr_lt, hcr_ref⟩

theorem s15_flush_step_preserves {F_cur : List (List Nat)}
    {k k' : FullCoreState} {lit w0 cref : BitVec 32} {skip_lit : Nat}
    (hvars : k'.cur_vars = k.cur_vars)
    (href_eq : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k)
    (hlay' : WatchStackLayout k')
    (hlit : lit.toNat < 2 * k.cur_vars)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hcr_lt : cref.toNat < 0x80000000)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore k)
    (hpres_other : ∀ l < 2 * k.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + idx]? = k.wstk[fullWatchOffCore k l + idx]?)
    (hpok_t :
      fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat + 2 ∧
      (∀ idx < fullWatchSizeCore k lit.toNat,
        k'.wstk[fullWatchOffCore k' lit.toNat + idx]? =
          k.wstk[fullWatchOffCore k lit.toNat + idx]?) ∧
      k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat]? = some w0 ∧
      k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat + 1]? = some cref) :
    (WatchesInv F_cur k → WatchesInv F_cur k') ∧
    (lit.toNat ≠ skip_lit → skip_lit < 2 * k.cur_vars →
      ∀ off q p end_v, SplitWatchesInv F_cur k skip_lit off q p end_v →
        let off' := fullWatchOffCore k' skip_lit
        SplitWatchesInv F_cur k' skip_lit off'
          (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) := by
  have hF : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  have hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k' :=
    fun _ hr => href_eq ▸ hr
  refine ⟨fun hw => ?_, fun hne hsk off q p end_v hsw => ?_⟩
  · refine ⟨hlay', fun l hl => ?_⟩
    have hl0 : l < 2 * k.cur_vars := hvars ▸ hl
    by_cases hll : l = lit.toNat
    · subst hll; rw [hpok_t.1]
      exact fullWatchSlice_append_large (by omega) hsub hpok_t.2.1 (hw.slices _ hl0)
        hpok_t.2.2.1 hpok_t.2.2.2 hflag hcr_lt (hsub _ hcr_ref)
    · obtain ⟨hsz, hget⟩ := hpres_other l hl0 hll
      rw [hsz]
      exact fullWatchSlice_relocate hF (by omega) hsub hget (hw.slices l hl0)
  · exact hsw.after_push (k' := k') (repl := lit.toNat) (w0 := w0) (cref := cref) (pok := true)
      hvars hsk hlit hne href_eq hlay' hflag hcr_lt hcr_ref hpres_other
      (fun _ => hpok_t) (fun h => by cases h)

theorem s15_flush_step_false_preserves {F_cur : List (List Nat)}
    {k k' : FullCoreState} {lit : BitVec 32} {skip_lit : Nat}
    (hvars : k'.cur_vars = k.cur_vars)
    (href_eq : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k)
    (hlay' : WatchStackLayout k')
    (hpres_other : ∀ l < 2 * k.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + idx]? = k.wstk[fullWatchOffCore k l + idx]?)
    (hpres_self : lit.toNat < 2 * k.cur_vars →
      fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat ∧
      ∀ idx < fullWatchSizeCore k lit.toNat,
        k'.wstk[fullWatchOffCore k' lit.toNat + idx]? =
          k.wstk[fullWatchOffCore k lit.toNat + idx]?) :
    (WatchesInv F_cur k → WatchesInv F_cur k') ∧
    (skip_lit < 2 * k.cur_vars →
      ∀ off q p end_v, SplitWatchesInv F_cur k skip_lit off q p end_v →
        let off' := fullWatchOffCore k' skip_lit
        SplitWatchesInv F_cur k' skip_lit off'
          (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) := by
  have hF : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  have hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k' :=
    fun _ hr => href_eq ▸ hr
  have hall : ∀ l < 2 * k.cur_vars,
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + idx]? = k.wstk[fullWatchOffCore k l + idx]? := by
    intro l hl; by_cases hll : l = lit.toNat
    · subst hll; exact hpres_self hl
    · exact hpres_other l hl hll
  refine ⟨fun hw => ⟨hlay', fun l hl => ?_⟩, fun hsk off q p end_v hsw => ?_⟩
  · obtain ⟨hsz, hget⟩ := hall l (hvars ▸ hl); rw [hsz]
    exact fullWatchSlice_relocate hF (by omega) hsub hget (hw.slices l (hvars ▸ hl))
  · obtain ⟨hsz, hget⟩ := hall skip_lit hsk
    let off' := fullWatchOffCore k' skip_lit
    have hq_ge := hsw.q_ge; have hq_le := hsw.q_le_p; have hp_le := hsw.p_le_end
    rw [hsw.off_eq, hsw.sz_eq] at hget
    exact
      { layout := hlay', off_eq := rfl, sz_eq := by rw [hsz, hsw.sz_eq]; omega
        sz_pos := by have := hsw.sz_pos; omega
        q_ge := by omega, q_le_p := by omega, p_le_end := by omega
        other_slices := fun l hl hln => by
          obtain ⟨hsz_l, hget_l⟩ := hall l (hvars ▸ hl); rw [hsz_l]
          exact fullWatchSlice_relocate hF (by omega) hsub hget_l
            (hsw.other_slices l (hvars ▸ hl) hln)
        kept_slice := by
          rw [show off' + (q - off) - off' = q - off by omega]
          exact fullWatchSlice_relocate hF (by omega) hsub
            (fun j hj => hget j (by omega)) hsw.kept_slice
        rem_slice := by
          rw [show off' + (end_v - off) - (off' + (p - off)) = end_v - p by omega]
          exact fullWatchSlice_relocate hF (by omega) hsub (fun j hj => by
            have := hget ((p - off) + j) (by omega)
            rwa [show off' + (p - off + j) = off' + (p - off) + j by omega,
              show off + (p - off + j) = p + j by omega] at this) hsw.rem_slice }

theorem s15_append_end_layout {c : FullCfg} {k : FullCoreState}
    (hlay : WatchStackLayout k) (hlen : k.LengthsOk c) {lit w0 cref : BitVec 32}
    (hlit : lit.toNat < 2 * k.cur_vars)
    (hoff_pos : 0 < fullWatchOffCore k lit.toNat)
    (hend_wlen : fullWatchOffCore k lit.toNat + fullWatchSizeCore k lit.toNat = k.wlen)
    (hfit2 : k.wlen + 2 ≤ c.wcap)
    (hw0_f : (w0 &&& 0x80000000#32) = 0#32) (hcr_lt : cref.toNat < 0x80000000) :
    let off := fullWatchOffCore k lit.toNat
    let sz := fullWatchSizeCore k lit.toNat
    let wend := off + sz
    let k' : FullCoreState :=
      { k with
        wstk := (k.wstk.set wend w0).set (wend + 1) cref
        wvec := k.wvec.set (2 * lit.toNat + 1) (BitVec.ofNat 32 (sz + 2))
        wlen := wend + 2 }
    k'.LengthsOk c ∧ WatchStackLayout k' ∧
    (∀ l, fullWatchOffCore k' l = fullWatchOffCore k l) ∧
    (∀ l < 2 * k.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + idx]? = k.wstk[fullWatchOffCore k l + idx]?) ∧
    fullWatchSizeCore k' lit.toNat = sz + 2 ∧
    (∀ idx < sz, k'.wstk[fullWatchOffCore k' lit.toNat + idx]? = k.wstk[off + idx]?) ∧
    k'.wstk[fullWatchOffCore k' lit.toNat + sz]? = some w0 ∧
    k'.wstk[fullWatchOffCore k' lit.toNat + sz + 1]? = some cref := by
  intro off sz wend k'
  have hwc := c.hwcap; unfold dimacsBound at hwc
  have hcv := hlen.cur_vars_le; have hwv := hlen.wvec_len; have hws := hlen.wstk_len_arr
  have hw0_ne : w0 ≠ 0xFFFFFFFF#32 := fun h => by rw [h] at hw0_f; exact absurd hw0_f (by decide)
  have hcr_ne : cref ≠ 0xFFFFFFFF#32 := fun h => by rw [h] at hcr_lt; revert hcr_lt; decide
  have hsz2_32 : sz + 2 < 2 ^ 32 := by omega
  have hwo : ∀ l, fullWatchOffCore k' l = fullWatchOffCore k l := fun l => by
    unfold fullWatchOffCore; dsimp only [k']; rw [List.getElem?_set_ne (by omega)]
  have hwsz_ne : ∀ l ≠ lit.toNat, fullWatchSizeCore k' l = fullWatchSizeCore k l := fun l h => by
    unfold fullWatchSizeCore; dsimp only [k']; rw [List.getElem?_set_ne (by omega)]
  have hwsz_self : fullWatchSizeCore k' lit.toNat = sz + 2 := by
    unfold fullWatchSizeCore; dsimp only [k']
    rw [List.getElem?_set_self (by omega), Option.getD_some, bv32_ofNat_toNat hsz2_32]
  have hlay' : WatchStackLayout k' := by
    refine ⟨fun l hl => ?_, fun l hl hp => ?_, fun l1 l2 h1 h2 hne hp1 hp2 => ?_,
      fun l hl idx hidx => ?_⟩
    · rw [hwo]; by_cases hll : l = lit.toNat
      · subst hll; rw [hwsz_self]; dsimp only [k']; omega
      · rw [hwsz_ne l hll]; have := hlay.bounds l hl; dsimp only [k']; omega
    · rw [hwo]; by_cases hll : l = lit.toNat
      · subst hll; omega
      · rw [hwsz_ne l hll] at hp; exact hlay.pos_off l hl hp
    · rw [hwo, hwo]; by_cases h1l : l1 = lit.toNat
      · subst h1l
        rw [hwsz_self] at hp1
        rw [hwsz_ne l2 (Ne.symm hne)] at hp2
        rw [hwsz_self, hwsz_ne l2 (Ne.symm hne)]
        have hb2 := hlay.bounds l2 h2
        by_cases hsz0 : sz = 0
        · right; dsimp only [sz, wend] at *; omega
        · have hd := hlay.disjoint _ l2 h1 h2 hne (by omega) hp2
          rcases hd with hd1 | hd2
          · exact absurd (by omega : k.wlen < fullWatchOffCore k l2 + fullWatchSizeCore k l2)
              (Nat.not_lt.mpr hb2)
          · exact Or.inr hd2
      · by_cases h2l : l2 = lit.toNat
        · subst h2l
          rw [hwsz_self] at hp2
          rw [hwsz_ne l1 h1l] at hp1
          rw [hwsz_self, hwsz_ne l1 h1l]
          have hb1 := hlay.bounds l1 h1
          by_cases hsz0 : sz = 0
          · left; dsimp only [sz, wend] at *; omega
          · have hd := hlay.disjoint l1 _ h1 h2 hne hp1 (by omega)
            rcases hd with hd1 | hd2
            · exact Or.inl hd1
            · exact absurd (by omega : k.wlen < fullWatchOffCore k l1 + fullWatchSizeCore k l1)
                (Nat.not_lt.mpr hb1)
        · rw [hwsz_ne l1 h1l] at hp1
          rw [hwsz_ne l2 h2l] at hp2
          rw [hwsz_ne l1 h1l, hwsz_ne l2 h2l]
          exact hlay.disjoint l1 l2 h1 h2 hne hp1 hp2
    · rw [hwo]; by_cases hll : l = lit.toNat
      · subst hll; rw [hwsz_self] at hidx; dsimp only [k']
        by_cases hi1 : idx = sz + 1
        · subst hi1; rw [show off + (sz + 1) = wend + 1 by omega,
            List.getElem?_set_self (by simp [hws]; omega)]
          simp [hcr_ne]
        · by_cases hi0 : idx = sz
          · subst hi0; rw [show off + sz = wend by rfl,
              List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
            simp [hw0_ne]
          · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
            exact hlay.no_sentinel _ hl idx (by omega)
      · rw [hwsz_ne l hll] at hidx
        have hb := hlay.bounds l hl
        dsimp only [k']
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hlay.no_sentinel l hl idx hidx
  have hlen' : k'.LengthsOk c :=
    { hlen with
      wstk_len_arr := (by simp [k', hws])
      wvec_len := (by simp [k', hwv])
      wlen_le := (by dsimp [k']; omega) }
  refine ⟨hlen', hlay', hwo, fun l hl hne => ⟨hwsz_ne l hne, fun idx hidx => ?_⟩,
      hwsz_self, fun idx hidx => ?_, ?_, ?_⟩
  · rw [hwo l]; have hb := hlay.bounds l hl; dsimp only [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  · rw [hwo lit.toNat]; dsimp only [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  · rw [hwo lit.toNat]; dsimp only [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
  · rw [hwo lit.toNat, show off + sz + 1 = wend + 1 by omega]; dsimp only [k']
    rw [List.getElem?_set_self (by simp [hws]; omega)]

theorem s15_append_sentinel_layout {c : FullCfg} {k : FullCoreState}
    (hlay : WatchStackLayout k) (hlen : k.LengthsOk c) {lit w0 cref : BitVec 32}
    {wu' : BitVec 64} (hlit : lit.toNat < 2 * k.cur_vars)
    (hoff_pos : 0 < fullWatchOffCore k lit.toNat)
    (hend2_le : fullWatchOffCore k lit.toNat + fullWatchSizeCore k lit.toNat + 2 ≤ k.wlen)
    (hsent0 : k.wstk[fullWatchOffCore k lit.toNat + fullWatchSizeCore k lit.toNat]? =
      some 0xFFFFFFFF#32)
    (hsent1 : k.wstk[fullWatchOffCore k lit.toNat + fullWatchSizeCore k lit.toNat + 1]? =
      some 0xFFFFFFFF#32)
    (hw0_f : (w0 &&& 0x80000000#32) = 0#32) (hcr_lt : cref.toNat < 0x80000000) :
    let off := fullWatchOffCore k lit.toNat
    let sz := fullWatchSizeCore k lit.toNat
    let wend := off + sz
    let k' : FullCoreState :=
      { k with
        wstk := (k.wstk.set wend w0).set (wend + 1) cref
        wvec := k.wvec.set (2 * lit.toNat + 1) (BitVec.ofNat 32 (sz + 2))
        wusable := wu' }
    k'.LengthsOk c ∧ WatchStackLayout k' ∧
    (∀ l, fullWatchOffCore k' l = fullWatchOffCore k l) ∧
    (∀ l < 2 * k.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + idx]? = k.wstk[fullWatchOffCore k l + idx]?) ∧
    fullWatchSizeCore k' lit.toNat = sz + 2 ∧
    (∀ idx < sz, k'.wstk[fullWatchOffCore k' lit.toNat + idx]? = k.wstk[off + idx]?) ∧
    k'.wstk[fullWatchOffCore k' lit.toNat + sz]? = some w0 ∧
    k'.wstk[fullWatchOffCore k' lit.toNat + sz + 1]? = some cref := by
  intro off sz wend k'
  have hwc := c.hwcap; unfold dimacsBound at hwc
  have hcv := hlen.cur_vars_le; have hwv := hlen.wvec_len; have hws := hlen.wstk_len_arr
  have hwlen := hlen.wlen_le
  have hw0_ne : w0 ≠ 0xFFFFFFFF#32 := fun h => by rw [h] at hw0_f; exact absurd hw0_f (by decide)
  have hcr_ne : cref ≠ 0xFFFFFFFF#32 := fun h => by rw [h] at hcr_lt; revert hcr_lt; decide
  have hsz2_32 : sz + 2 < 2 ^ 32 := by omega
  have hwo : ∀ l, fullWatchOffCore k' l = fullWatchOffCore k l := fun l => by
    unfold fullWatchOffCore; dsimp only [k']; rw [List.getElem?_set_ne (by omega)]
  have hwsz_ne : ∀ l ≠ lit.toNat, fullWatchSizeCore k' l = fullWatchSizeCore k l := fun l h => by
    unfold fullWatchSizeCore; dsimp only [k']; rw [List.getElem?_set_ne (by omega)]
  have hwsz_self : fullWatchSizeCore k' lit.toNat = sz + 2 := by
    unfold fullWatchSizeCore; dsimp only [k']
    rw [List.getElem?_set_self (by omega), Option.getD_some, bv32_ofNat_toNat hsz2_32]
  have hdisj_wend : ∀ l < 2 * k.cur_vars, l ≠ lit.toNat → 0 < fullWatchSizeCore k l →
      fullWatchOffCore k l + fullWatchSizeCore k l ≤ off ∨
      wend + 2 ≤ fullWatchOffCore k l := by
    intro l hl hne hp
    have hnot_s0 : ¬ (fullWatchOffCore k l ≤ wend ∧ wend < fullWatchOffCore k l +
        fullWatchSizeCore k l) := fun h => by
      have hn := hlay.no_sentinel l hl (wend - fullWatchOffCore k l) (by omega)
      rw [show fullWatchOffCore k l + (wend - fullWatchOffCore k l) = wend by omega] at hn
      exact hn hsent0
    have hnot_s1 : ¬ (fullWatchOffCore k l ≤ wend + 1 ∧ wend + 1 < fullWatchOffCore k l +
        fullWatchSizeCore k l) := fun h => by
      have hn := hlay.no_sentinel l hl (wend + 1 - fullWatchOffCore k l) (by omega)
      rw [show fullWatchOffCore k l + (wend + 1 - fullWatchOffCore k l) = wend + 1 by omega] at hn
      exact hn hsent1
    by_cases hsz0 : sz = 0
    · have hw_off : wend = off := Nat.add_zero off ▸ congrArg (off + ·) hsz0
      rw [hw_off] at hnot_s0 hnot_s1 ⊢; omega
    · have hd := hlay.disjoint l lit.toNat hl hlit hne hp (by omega)
      rcases hd with h1 | h2
      · exact Or.inl h1
      · right; change wend ≤ fullWatchOffCore k l at h2; omega
  have hlay' : WatchStackLayout k' := by
    refine ⟨fun l hl => ?_, fun l hl hp => ?_, fun l1 l2 h1 h2 hne hp1 hp2 => ?_,
      fun l hl idx hidx => ?_⟩
    · rw [hwo]; by_cases hll : l = lit.toNat
      · subst hll; rw [hwsz_self]; exact hend2_le
      · rw [hwsz_ne l hll]; exact hlay.bounds l hl
    · rw [hwo]; by_cases hll : l = lit.toNat
      · subst hll; exact hoff_pos
      · rw [hwsz_ne l hll] at hp; exact hlay.pos_off l hl hp
    · rw [hwo, hwo]; by_cases h1l : l1 = lit.toNat
      · subst h1l
        rw [hwsz_self] at hp1
        rw [hwsz_ne l2 (Ne.symm hne)] at hp2
        rw [hwsz_self, hwsz_ne l2 (Ne.symm hne)]
        rcases hdisj_wend l2 h2 (Ne.symm hne) hp2 with ha | hb
        · exact Or.inr ha
        · exact Or.inl hb
      · by_cases h2l : l2 = lit.toNat
        · subst h2l
          rw [hwsz_self] at hp2
          rw [hwsz_ne l1 h1l] at hp1
          rw [hwsz_self, hwsz_ne l1 h1l]
          exact hdisj_wend l1 h1 h1l hp1
        · rw [hwsz_ne l1 h1l] at hp1
          rw [hwsz_ne l2 h2l] at hp2
          rw [hwsz_ne l1 h1l, hwsz_ne l2 h2l]
          exact hlay.disjoint l1 l2 h1 h2 hne hp1 hp2
    · rw [hwo]; by_cases hll : l = lit.toNat
      · subst hll; rw [hwsz_self] at hidx; dsimp only [k']
        by_cases hi1 : idx = sz + 1
        · subst hi1; rw [show off + (sz + 1) = wend + 1 by omega,
            List.getElem?_set_self (by simp [hws]; omega)]
          simp [hcr_ne]
        · by_cases hi0 : idx = sz
          · subst hi0; rw [show off + sz = wend by rfl,
              List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
            simp [hw0_ne]
          · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
            exact hlay.no_sentinel _ hl idx (by omega)
      · rw [hwsz_ne l hll] at hidx
        rcases hdisj_wend l hl hll (by omega) with ha | hb <;> dsimp only [k'] <;>
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)] <;>
          exact hlay.no_sentinel l hl idx hidx
  have hlen' : k'.LengthsOk c :=
    { hlen with
      wstk_len_arr := (by simp [k', hws])
      wvec_len := (by simp [k', hwv]) }
  refine ⟨hlen', hlay', hwo, fun l hl hne => ⟨hwsz_ne l hne, fun idx hidx => ?_⟩,
      hwsz_self, fun idx hidx => ?_, ?_, ?_⟩
  · rw [hwo l]
    rcases hdisj_wend l hl hne (by omega) with ha | hb <;> dsimp only [k'] <;>
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  · rw [hwo lit.toNat]; dsimp only [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  · rw [hwo lit.toNat]; dsimp only [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
  · rw [hwo lit.toNat, show off + sz + 1 = wend + 1 by omega]; dsimp only [k']
    rw [List.getElem?_set_self (by simp [hws]; omega)]

/-! ## 3. Shared Replacement-Search, Push, and Finish `wp` Helpers -/

/-- Two-pass replacement search (`[srch .. csz)` then `[2 .. srch)`) shared by
`full_prop_lit_ovf_s15` and `full_prop_lit_raw_s15`. -/
@[expose] def s15ReplSearchExpr (srch_v csz : Val i32) (nlits cbase ar_p vals_p : Val i64)
    (j6_body : Tup Val [i32, i32, i32] → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  .group (sig := [[i32, i32, i32]])
    (fun L10 => .cons (fun p1 =>
      .group (sig := [[i32, i32, i32]])
        (fun L11 => .cons (fun pf => j6_body pf) .nil)
        (fun L11 =>
          .let_ (Op.mk (.cmp .eq i32) (.var p1.1, (.imm (4294967295 : BitVec 32), ())))
            fun ceq =>
          .jnz (.var ceq.1) (
            .group (sig := [[i32, i32, i32]])
              (fun L21 => .cons (fun p2 =>
                .jump L11.1 (.var p2.1, (.var p2.2.1, (.var p2.2.2.1, ())))
              ) .nil)
              (fun L21 =>
                .group (sig := [[i32]])
                  (fun L22 => .cons (fun r2 =>
                    .let_ (Op.mk (.cmp .ult i32) (.var r2.1, (.var srch_v, ()))) fun clt =>
                    .jnz (.var clt.1) (
                      .let_ (Op.mk (.zext 32 64) (.var r2.1, ())) fun r64 =>
                      .let_ (Op.mk (.add i64) (.var cbase, (.var r64.1, ()))) fun idx0 =>
                      .let_ (Op.mk (.mul i64) (.var idx0.1, (.imm (4 : BitVec 64), ())))
                        fun off4 =>
                      .let_ (Op.mk (.add i64) (.var ar_p, (.var off4.1, ()))) fun par =>
                      .load i32 (.var par.1) fun cand =>
                      .group (sig := [[]])
                        (fun L23 => .cons (fun _ =>
                          .let_ (Op.mk (.add i32) (.var r2.1, (.imm (1 : BitVec 32), ())))
                            fun r2' =>
                          .jump L22.1 (.var r2'.1, ())
                        ) .nil)
                        (fun L23 =>
                          .let_ (Op.mk (.zext 32 64) (.var cand, ())) fun c64 =>
                          .let_ (Op.mk (.cmp .ult i64) (.var c64.1, (.var nlits, ())))
                            fun cb =>
                          .jnz (.var cb.1) (
                            .let_ (Op.mk (.zext 32 64) (.var cand, ())) fun c64' =>
                            .let_ (Op.mk (.add i64) (.var vals_p, (.var c64'.1, ()))) fun pv =>
                            .load i8 (.var pv.1) fun cv =>
                            .let_ (Op.mk (.trunc 32 8) (.imm (0 : BitVec 32), ())) fun z8 =>
                            .let_ (Op.mk (.sext 8 32) (.var cv, ())) fun cv32 =>
                            .let_ (Op.mk (.sext 8 32) (.var z8.1, ())) fun z32 =>
                            .let_ (Op.mk (.cmp .sge i32) (.var cv32.1, (.var z32.1, ())))
                              fun csge =>
                            .jnz (.var csge.1)
                              (.jump L21.1 (.var r2.1, (.var cand, (.var r2.1, ()))))
                              (.jump L23.1 ())
                          ) (.jump L23.1 ())
                        )
                    ) (.jump L21.1 (.var p1.1, (.var p1.2.1, (.var r2.1, ()))))
                  ) .nil)
                  (fun L22 => .jump L22.1 (.imm (2 : BitVec 32), ()))
              )
          ) (.jump L11.1 (.var p1.1, (.var p1.2.1, (.var p1.2.2.1, ()))))
        )
    ) .nil)
    (fun L10 =>
      .group (sig := [[i32]])
        (fun L24 => .cons (fun r1 =>
          .let_ (Op.mk (.cmp .ult i32) (.var r1.1, (.var csz, ()))) fun clt =>
          .jnz (.var clt.1) (
            .let_ (Op.mk (.zext 32 64) (.var r1.1, ())) fun r64 =>
            .let_ (Op.mk (.add i64) (.var cbase, (.var r64.1, ()))) fun idx0 =>
            .let_ (Op.mk (.mul i64) (.var idx0.1, (.imm (4 : BitVec 64), ()))) fun off4 =>
            .let_ (Op.mk (.add i64) (.var ar_p, (.var off4.1, ()))) fun par =>
            .load i32 (.var par.1) fun cand =>
            .group (sig := [[]])
              (fun L25 => .cons (fun _ =>
                .let_ (Op.mk (.add i32) (.var r1.1, (.imm (1 : BitVec 32), ()))) fun r1' =>
                .jump L24.1 (.var r1'.1, ())
              ) .nil)
              (fun L25 =>
                .let_ (Op.mk (.zext 32 64) (.var cand, ())) fun c64 =>
                .let_ (Op.mk (.cmp .ult i64) (.var c64.1, (.var nlits, ()))) fun cb =>
                .jnz (.var cb.1) (
                  .let_ (Op.mk (.zext 32 64) (.var cand, ())) fun c64' =>
                  .let_ (Op.mk (.add i64) (.var vals_p, (.var c64'.1, ()))) fun pv =>
                  .load i8 (.var pv.1) fun cv =>
                  .let_ (Op.mk (.trunc 32 8) (.imm (0 : BitVec 32), ())) fun z8 =>
                  .let_ (Op.mk (.sext 8 32) (.var cv, ())) fun cv32 =>
                  .let_ (Op.mk (.sext 8 32) (.var z8.1, ())) fun z32 =>
                  .let_ (Op.mk (.cmp .sge i32) (.var cv32.1, (.var z32.1, ()))) fun csge =>
                  .jnz (.var csge.1)
                    (.jump L10.1 (.var r1.1, (.var cand, (.var r1.1, ()))))
                    (.jump L25.1 ())
                ) (.jump L25.1 ())
              )
          ) (.jump L10.1 (.imm (4294967295 : BitVec 32), (.imm (0 : BitVec 32), (.var r1.1, ()))))
        ) .nil)
        (fun L24 => .jump L24.1 (.var srch_v, ()))
    )

theorem s15_repl_search_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sem1 : FullState} {not_lit cref srch_v csz32 : BitVec 32}
    {nlits off_v p_v q_v end_v : BitVec 64} {R : Mem 64 → Prop} {mj : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    {j6_body : Tup Val [i32, i32, i32] → Expr Val Cont [.bool]}
    (hmaxv : c.max_vars < 2 * dimacsBound) (har : c.arena_cap < 2 * dimacsBound)
    (hcv0 : s.core.cur_vars ≤ c.max_vars)
    (hnlits_eq : nlits.toNat = 2 * s.core.cur_vars)
    (hpi1 : PropLitInv c F0 F_cur s sem1 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hlen1_mem : (fastPropMem s sem1).LengthsOk c)
    (hfit1 : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (h3_idx : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (hcsz32_nat : csz32.toNat = fullArenaClauseSizeCore sem1.core cref.toNat)
    (hsrch2 : 2 ≤ srch_v.toNat)
    (hsrch_lt : srch_v.toNat < fullArenaClauseSizeCore sem1.core cref.toNat)
    (hm : (FullMem c (fastPropMem s sem1) ⋆ R) mj)
    (hj6 : ∀ ri_f repl_f _rf : BitVec 32,
      ((ri_f = 0xFFFFFFFF#32 ∧ ∀ k, 2 ≤ k → k < fullArenaClauseSizeCore sem1.core cref.toNat →
          fullFindReplBad sem1 cref.toNat k) ∨
       (ri_f ≠ 0xFFFFFFFF#32 ∧ 2 ≤ ri_f.toNat ∧
          ∃ hr_lt : ri_f.toNat < fullArenaClauseSizeCore sem1.core cref.toNat,
          repl_f = sem1.core.arena[cref.toNat + 3 + ri_f.toNat]'(by
            rw [hpi1.len.core_ok.arena_len_arr]
            exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hr_lt _)
              (Nat.le_trans hfit1 hpi1.len.core_ok.arena_len_le)) ∧
          repl_f.toNat < 2 * sem1.core.cur_vars ∧
          ((sem1.core.vals[repl_f.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false)) →
      wp Γ Q X (j6_body (ri_f, repl_f, _rf, ())) mj) :
    wp Γ Q X (s15ReplSearchExpr srch_v csz32 nlits
      (cref.setWidth 64 + 3#64) c.pArena c.pVals j6_body) mj := by
  unfold dimacsBound at hmaxv har
  have haren1 := hpi1.len.core_ok.arena_len_arr
  have halen1_le := hpi1.len.core_ok.arena_len_le
  have hvals1 := hpi1.len.core_ok.vals_len
  have hm1_aren := hlen1_mem.core_ok.arena_len_arr
  have hm1_vals := hlen1_mem.core_ok.vals_len
  have hfit_csz : cref.toNat + 3 + csz32.toNat ≤ c.arena_cap := by
    rw [hcsz32_nat]; exact Nat.le_trans hfit1 halen1_le
  have h2cv_le : 2 * s.core.cur_vars ≤ 2 * c.max_vars := Nat.mul_le_mul_left 2 hcv0
  have hcv1_eq := hpi1.cur_vars_eq
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hcv0 (Nat.lt_trans hmaxv (by decide))
  have h2cv_lt64 : 2 * s.core.cur_vars < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 hcv0)
      (Nat.lt_trans (Nat.mul_lt_mul_of_pos_left hmaxv (by decide)) (by decide))
  have hfit1_ar : ∀ {r}, r < fullArenaClauseSizeCore sem1.core cref.toNat →
      cref.toNat + 3 + r < sem1.core.arena.length := fun hr => by
    rw [haren1]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hr _) (Nat.le_trans hfit1 halen1_le)
  have hcsz_lt32 : fullArenaClauseSizeCore sem1.core cref.toNat < 2 ^ 32 :=
    hcsz32_nat ▸ csz32.isLt
  have hcsz_lt_ff : fullArenaClauseSizeCore sem1.core cref.toNat < 0xFFFFFFFF :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left _ _) hfit1)
      (Nat.lt_of_le_of_lt halen1_le (Nat.lt_trans har (by decide)))
  refine wp_loop_break_group
    (brkTs := [i32, i32, i32]) (lpTs := [i32])
    (fun (ri1, repl1, r1, ()) mb1 => mb1 = mj ∧
      ((ri1 = 0xFFFFFFFF#32 ∧ ∀ k, srch_v.toNat ≤ k →
          k < fullArenaClauseSizeCore sem1.core cref.toNat → fullFindReplBad sem1 cref.toNat k) ∨
       (ri1 ≠ 0xFFFFFFFF#32 ∧ 2 ≤ ri1.toNat ∧
          ∃ hr_lt : ri1.toNat < fullArenaClauseSizeCore sem1.core cref.toNat,
          repl1 = sem1.core.arena[cref.toNat + 3 + ri1.toNat]'(hfit1_ar hr_lt) ∧
          repl1.toNat < 2 * sem1.core.cur_vars ∧
          ((sem1.core.vals[repl1.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false)))
    (fun rem1 (r1, ()) ml1 => rem1 = csz32.toNat - r1.toNat ∧
      srch_v.toNat ≤ r1.toNat ∧ r1.toNat ≤ csz32.toNat ∧ ml1 = mj ∧
      ∀ k, srch_v.toNat ≤ k → k < r1.toNat → fullFindReplBad sem1 cref.toNat k) ?_ ?_ ?_
  · rintro _ ⟨ri1, repl1, r1, ⟨⟩⟩ mb1 ⟨hmb1, hres1⟩
    subst mb1
    refine wp_join_group (fun (ri_f, repl_f, rf, ()) mf => mf = mj ∧
        ((ri_f = 0xFFFFFFFF#32 ∧ ∀ k, 2 ≤ k → k < fullArenaClauseSizeCore sem1.core cref.toNat →
            fullFindReplBad sem1 cref.toNat k) ∨
         (ri_f ≠ 0xFFFFFFFF#32 ∧ 2 ≤ ri_f.toNat ∧
            ∃ hr_lt : ri_f.toNat < fullArenaClauseSizeCore sem1.core cref.toNat,
            repl_f = sem1.core.arena[cref.toNat + 3 + ri_f.toNat]'(hfit1_ar hr_lt) ∧
            repl_f.toNat < 2 * sem1.core.cur_vars ∧
            ((sem1.core.vals[repl_f.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false))) ?_ ?_
    · rintro _ ⟨ri_f, repl_f, rf, ⟨⟩⟩ mf ⟨hmf, hfin⟩
      subst mf
      exact hj6 ri_f repl_f rf hfin
    · intro Jri hJri; s15_head_steps
      · have hri1 : ri1 = 0xFFFFFFFF#32 := hc
        have hnone1 : ∀ k, srch_v.toNat ≤ k →
            k < fullArenaClauseSizeCore sem1.core cref.toNat → fullFindReplBad sem1 cref.toNat k :=
          hres1.elim And.right fun h => absurd hri1 h.1
        refine wp_loop_break_group
          (brkTs := [i32, i32, i32]) (lpTs := [i32])
          (fun (ri2, repl2, r2, ()) mb2 => mb2 = mj ∧
            ((ri2 = 0xFFFFFFFF#32 ∧ ∀ k, 2 ≤ k →
                k < fullArenaClauseSizeCore sem1.core cref.toNat →
                fullFindReplBad sem1 cref.toNat k) ∨
             (ri2 ≠ 0xFFFFFFFF#32 ∧ 2 ≤ ri2.toNat ∧
                ∃ hr_lt : ri2.toNat < fullArenaClauseSizeCore sem1.core cref.toNat,
                repl2 = sem1.core.arena[cref.toNat + 3 + ri2.toNat]'(hfit1_ar hr_lt) ∧
                repl2.toNat < 2 * sem1.core.cur_vars ∧
                ((sem1.core.vals[repl2.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false)))
          (fun rem2 (r2, ()) ml2 => rem2 = srch_v.toNat - r2.toNat ∧
            2 ≤ r2.toNat ∧ r2.toNat ≤ srch_v.toNat ∧ ml2 = mj ∧
            ∀ k, 2 ≤ k → k < r2.toNat → fullFindReplBad sem1 cref.toNat k) ?_ ?_ ?_
        · rintro _ ⟨ri2, repl2, r2, ⟨⟩⟩ mb2 ⟨hmb2, hres2⟩
          subst mb2
          s15_head_steps; exact hJri (ri2, repl2, r2, ()) mj ⟨rfl, hres2⟩
        · rintro B2 L2 _ ⟨r2, ⟨⟩⟩ ml2 hB2 ih2 ⟨rfl, hr2_ge, hr2_le, hml2, hseen2⟩
          subst ml2
          s15_head_split
          · have hr2_lt : r2.toNat < srch_v.toNat := by assumption
            have hr2_csz : r2.toNat < fullArenaClauseSizeCore sem1.core cref.toNat :=
              Nat.lt_trans hr2_lt hsrch_lt
            have hidx_r2 : (cref.setWidth 64 + 3#64 + r2.setWidth 64).toNat =
                cref.toNat + 3 + r2.toNat := by
              rw [bv64_add_toNat (by
                rw [h3_idx, bv_c0_zext32_64]
                exact Nat.lt_of_lt_of_le (hfit1_ar hr2_csz) (Nat.le_trans
                  (Nat.le_of_eq haren1) (Nat.le_of_lt (Nat.lt_trans har (by decide))))),
                h3_idx, bv_c0_zext32_64]
            have hidx_r2_lt : (cref.setWidth 64 + 3#64 + r2.setWidth 64).toNat < c.arena_cap := by
              rw [hidx_r2]; omega
            have hr2_1 : (r2 + (1 : BitVec 32)).toNat = r2.toNat + 1 := by
              rw [BitVec.toNat_add]
              exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hr2_csz) hcsz_lt32)
            s15_head_steps
            refine wp_join_group (fun () m23 => m23 = mj ∧ fullFindReplBad sem1 cref.toNat r2.toNat)
              ?_ ?_
            · rintro _ ⟨⟩ m23 ⟨hm23, hbad⟩
              subst m23
              s15_head_steps
              exact ih2 _ _ mj (by
                  rw [show (1 : BitVec 32) = (1 : BitVec 32) from rfl, hr2_1]
                  exact Nat.sub_lt (Nat.sub_pos_of_lt hr2_lt) Nat.zero_lt_one)
                ⟨rfl, by rw [hr2_1]; exact Nat.le_trans hr2_ge (Nat.le_succ _),
                 by rw [hr2_1]; exact Nat.succ_le_of_lt hr2_lt, rfl,
                 fun k hk1 hk2 => by
                   rw [hr2_1] at hk2
                   rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk2) with hk' | hkr
                   · exact hseen2 k hk1 hk'
                   · subst hkr; exact hbad⟩
            · intro J23 hJ23; s15_head_split
              · have hidx_r2_ar : (cref.setWidth 64 + 3#64 + r2.setWidth 64).toNat <
                    sem1.core.arena.length := by
                  rw [hidx_r2]; exact hfit1_ar hr2_csz
                have hcand_cv : (sem1.core.arena[(cref.setWidth 64 + 3#64 + r2.setWidth 64).toNat]'
                    hidx_r2_ar).toNat < 2 * sem1.core.cur_vars := by
                  have hlt : (sem1.core.arena[cref.toNat + 3 + r2.toNat]'(hfit1_ar hr2_csz)).toNat <
                      nlits.toNat := by
                    have hc' := hc
                    simp only [fastPropMem_arena,
                      Nat.mod_eq_of_lt (by omega : cref.toNat + 3 + r2.toNat < 2 ^ 64)] at hc'
                    exact hc'
                  rw [hnlits_eq, ← hcv1_eq] at hlt
                  simpa only [hidx_r2] using hlt
                have hcand_cv_raw : (sem1.core.arena[cref.toNat + 3 + r2.toNat]'(
                    hfit1_ar hr2_csz)).toNat < 2 * sem1.core.cur_vars := by
                  simpa only [hidx_r2] using hcand_cv
                have hcand_max : (sem1.core.arena[(cref.setWidth 64 + 3#64 + r2.setWidth 64).toNat]'
                    hidx_r2_ar).toNat < 2 * c.max_vars :=
                  Nat.lt_of_lt_of_le hcand_cv (Nat.mul_le_mul_left 2 (hcv1_eq ▸ hcv0))
                have hcand_max_raw : (sem1.core.arena[cref.toNat + 3 + r2.toNat]'(
                    hfit1_ar hr2_csz)).toNat < 2 * c.max_vars := by
                  simpa only [hidx_r2] using hcand_max
                have hidx_r2_mod : (cref.toNat + 3 + r2.toNat) % 2 ^ 64 =
                    cref.toNat + 3 + r2.toNat :=
                  Nat.mod_eq_of_lt (by omega)
                let cand2_m := (fastPropMem s sem1).core.arena[(cref.setWidth 64 + 3#64 +
                  r2.setWidth 64).toNat]'(by rw [fastPropMem_arena]; exact hidx_r2_ar)
                have hcand2_eq : cand2_m = sem1.core.arena[cref.toNat + 3 + r2.toNat]'(
                    hfit1_ar hr2_csz) :=
                  (fc_getElem_arena s sem1).trans
                    (fc_getElem_eq_of_idx hidx_r2 _ (hfit1_ar hr2_csz))
                s15_head_steps
                · have hok := fastProp_findRepl_ok (st := sem1) (cref := cref.toNat) (r := r2.toNat)
                    (hi_lt := hfit1_ar hr2_csz) (hj_lt := hvals1 ▸ Nat.lt_of_lt_of_le
                      hcand_cv_raw (Nat.mul_le_mul_left 2 hpi1.len.core_ok.cur_vars_le))
                    hcand_cv_raw
                    (by simpa only [fastPropMem_arena, fastPropMem_vals, hidx_r2_mod] using hc)
                  have hr2_ne : r2 ≠ 0xFFFFFFFF#32 := fun heq => by
                    have heq' : r2.toNat = 0xFFFFFFFF := by rw [heq]; decide
                    exact absurd (heq' ▸ hr2_csz) (Nat.not_lt.mpr (Nat.le_of_lt hcsz_lt_ff))
                  exact hB2 (r2, cand2_m, r2, ()) mj ⟨rfl, Or.inr ⟨hr2_ne, hr2_ge, hr2_csz,
                    hcand2_eq, by simpa only [hcand2_eq,
                      List.getElem?_eq_getElem (hfit1_ar hr2_csz), Option.getD_some] using hok⟩⟩
                · exact hJ23 () mj ⟨rfl, fastProp_findRepl_bad_slt (st := sem1) (cref := cref.toNat)
                    (r := r2.toNat) (hi_lt := hfit1_ar hr2_csz)
                    (hj_lt := hvals1 ▸ Nat.lt_of_lt_of_le hcand_cv_raw
                      (Nat.mul_le_mul_left 2 hpi1.len.core_ok.cur_vars_le))
                    (by simpa only [fastPropMem_arena, fastPropMem_vals, hidx_r2_mod] using hc)⟩
              · have hge_mod : nlits.toNat ≤
                    (sem1.core.arena[(cref.toNat + 3 + r2.toNat) % 2 ^ 64]'(
                      by rw [Nat.mod_eq_of_lt (by omega)]; exact hfit1_ar hr2_csz)).toNat :=
                  Nat.le_of_not_lt (by simpa only [fastPropMem_arena] using hc)
                have hcand_ge : ¬ (sem1.core.arena[cref.toNat + 3 + r2.toNat]'(
                    hfit1_ar hr2_csz)).toNat < 2 * sem1.core.cur_vars := by
                  have hge : nlits.toNat ≤ (sem1.core.arena[cref.toNat + 3 + r2.toNat]'(
                      hfit1_ar hr2_csz)).toNat := by
                    simpa only [Nat.mod_eq_of_lt (by omega : cref.toNat + 3 + r2.toNat < 2 ^ 64)]
                      using hge_mod
                  rw [hnlits_eq, ← hcv1_eq] at hge
                  exact Nat.not_lt.mpr hge
                s15_head_steps
                exact hJ23 () mj ⟨rfl, fastProp_findRepl_bad_oob (st := sem1) (cref := cref.toNat)
                  (r := r2.toNat) (hi_lt := hfit1_ar hr2_csz) hcand_ge⟩
          · have hr2_eq : r2.toNat = srch_v.toNat := Nat.le_antisymm hr2_le (Nat.le_of_not_lt hc)
            s15_head_steps
            exact hB2 (ri1, repl1, r2, ()) mj ⟨rfl, Or.inl ⟨hri1,
              fun k hk2 hksz => if hks : k < srch_v.toNat then hseen2 k hk2 (hr2_eq ▸ hks)
                else hnone1 k (Nat.le_of_not_lt hks) hksz⟩⟩
        · intro B2 L2 _ hL2; s15_head_steps
          exact hL2 _ (2#32, ()) mj ⟨rfl, by decide, hsrch2, rfl,
            fun _ hk1 hk2 => absurd (Nat.lt_of_le_of_lt hk1 hk2) (by decide)⟩
      · exact hJri (ri1, repl1, r1, ()) mj ⟨rfl, Or.inr (hres1.resolve_left (fun h => hc h.1))⟩
  · rintro B1 L1 _ ⟨r1, ⟨⟩⟩ ml1 hB1 ih1 ⟨rfl, hr1_ge, hr1_le, hml1, hseen1⟩
    subst ml1
    s15_head_split
    · have hr1_lt : r1.toNat < csz32.toNat := by assumption
      have hr1_csz : r1.toNat < fullArenaClauseSizeCore sem1.core cref.toNat := hcsz32_nat ▸ hr1_lt
      have hidx_r1 : (cref.setWidth 64 + 3#64 + r1.setWidth 64).toNat =
          cref.toNat + 3 + r1.toNat := by
        rw [bv64_add_toNat (by
          rw [h3_idx, bv_c0_zext32_64]
          exact Nat.lt_of_lt_of_le (hfit1_ar hr1_csz) (Nat.le_trans
            (Nat.le_of_eq haren1) (Nat.le_of_lt (Nat.lt_trans har (by decide))))),
          h3_idx, bv_c0_zext32_64]
      have hidx_r1_lt : (cref.setWidth 64 + 3#64 + r1.setWidth 64).toNat < c.arena_cap := by
        rw [hidx_r1]; omega
      have hr1_1 : (r1 + (1 : BitVec 32)).toNat = r1.toNat + 1 := by
        rw [BitVec.toNat_add]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hr1_csz) hcsz_lt32)
      s15_head_steps
      refine wp_join_group (fun () m25 => m25 = mj ∧ fullFindReplBad sem1 cref.toNat r1.toNat)
        ?_ ?_
      · rintro _ ⟨⟩ m25 ⟨hm25, hbad⟩
        subst m25
        s15_head_steps
        exact ih1 _ _ mj (by
            rw [hr1_1]
            exact Nat.sub_lt (Nat.sub_pos_of_lt hr1_lt) Nat.zero_lt_one)
          ⟨rfl, by rw [hr1_1]; exact Nat.le_trans hr1_ge (Nat.le_succ _),
           by rw [hr1_1]; exact Nat.succ_le_of_lt hr1_lt, rfl,
           fun k hk1 hk2 => by
             rw [hr1_1] at hk2
             rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk2) with hk' | hkr
             · exact hseen1 k hk1 hk'
             · subst hkr; exact hbad⟩
      · intro J25 hJ25; s15_head_split
        · have hidx_r1_ar : (cref.setWidth 64 + 3#64 + r1.setWidth 64).toNat <
              sem1.core.arena.length := by
            rw [hidx_r1]; exact hfit1_ar hr1_csz
          have hcand_cv : (sem1.core.arena[(cref.setWidth 64 + 3#64 + r1.setWidth 64).toNat]'
              hidx_r1_ar).toNat < 2 * sem1.core.cur_vars := by
            have hlt : (sem1.core.arena[cref.toNat + 3 + r1.toNat]'(hfit1_ar hr1_csz)).toNat <
                nlits.toNat := by
              have hc' := hc
              simp only [fastPropMem_arena,
                Nat.mod_eq_of_lt (by omega : cref.toNat + 3 + r1.toNat < 2 ^ 64)] at hc'
              exact hc'
            rw [hnlits_eq, ← hcv1_eq] at hlt
            simpa only [hidx_r1] using hlt
          have hcand_cv_raw : (sem1.core.arena[cref.toNat + 3 + r1.toNat]'(
              hfit1_ar hr1_csz)).toNat < 2 * sem1.core.cur_vars := by
            simpa only [hidx_r1] using hcand_cv
          have hcand_max : (sem1.core.arena[(cref.setWidth 64 + 3#64 + r1.setWidth 64).toNat]'
              hidx_r1_ar).toNat < 2 * c.max_vars :=
            Nat.lt_of_lt_of_le hcand_cv (Nat.mul_le_mul_left 2 (hcv1_eq ▸ hcv0))
          have hcand_max_raw : (sem1.core.arena[cref.toNat + 3 + r1.toNat]'(
              hfit1_ar hr1_csz)).toNat < 2 * c.max_vars := by
            simpa only [hidx_r1] using hcand_max
          have hidx_r1_mod : (cref.toNat + 3 + r1.toNat) % 2 ^ 64 = cref.toNat + 3 + r1.toNat :=
            Nat.mod_eq_of_lt (by omega)
          let cand1_m := (fastPropMem s sem1).core.arena[(cref.setWidth 64 + 3#64 +
            r1.setWidth 64).toNat]'(by rw [fastPropMem_arena]; exact hidx_r1_ar)
          have hcand1_eq : cand1_m = sem1.core.arena[cref.toNat + 3 + r1.toNat]'(
              hfit1_ar hr1_csz) :=
            (fc_getElem_arena s sem1).trans (fc_getElem_eq_of_idx hidx_r1 _ (hfit1_ar hr1_csz))
          s15_head_steps
          · have hok := fastProp_findRepl_ok (st := sem1) (cref := cref.toNat) (r := r1.toNat)
              (hi_lt := hfit1_ar hr1_csz) (hj_lt := hvals1 ▸ Nat.lt_of_lt_of_le
                hcand_cv_raw (Nat.mul_le_mul_left 2 hpi1.len.core_ok.cur_vars_le))
              hcand_cv_raw
              (by simpa only [fastPropMem_arena, fastPropMem_vals, hidx_r1_mod] using hc)
            have hr1_ne : r1 ≠ 0xFFFFFFFF#32 := fun heq => by
              have heq' : r1.toNat = 0xFFFFFFFF := by rw [heq]; decide
              exact absurd (heq' ▸ hr1_csz) (Nat.not_lt.mpr (Nat.le_of_lt hcsz_lt_ff))
            exact hB1 (r1, cand1_m, r1, ()) mj ⟨rfl, Or.inr ⟨hr1_ne, Nat.le_trans hsrch2 hr1_ge,
              hr1_csz, hcand1_eq, by simpa only [hcand1_eq,
                List.getElem?_eq_getElem (hfit1_ar hr1_csz), Option.getD_some] using hok⟩⟩
          · exact hJ25 () mj ⟨rfl, fastProp_findRepl_bad_slt (st := sem1) (cref := cref.toNat)
              (r := r1.toNat) (hi_lt := hfit1_ar hr1_csz)
              (hj_lt := hvals1 ▸ Nat.lt_of_lt_of_le hcand_cv_raw
                (Nat.mul_le_mul_left 2 hpi1.len.core_ok.cur_vars_le))
              (by simpa only [fastPropMem_arena, fastPropMem_vals, hidx_r1_mod] using hc)⟩
        · have hge_mod : nlits.toNat ≤ (sem1.core.arena[(cref.toNat + 3 + r1.toNat) % 2 ^ 64]'(
              by rw [Nat.mod_eq_of_lt (by omega)]; exact hfit1_ar hr1_csz)).toNat :=
            Nat.le_of_not_lt (by simpa only [fastPropMem_arena] using hc)
          have hcand_ge : ¬ (sem1.core.arena[cref.toNat + 3 + r1.toNat]'(
              hfit1_ar hr1_csz)).toNat < 2 * sem1.core.cur_vars := by
            have hge : nlits.toNat ≤ (sem1.core.arena[cref.toNat + 3 + r1.toNat]'(
                hfit1_ar hr1_csz)).toNat := by
              simpa only [Nat.mod_eq_of_lt (by omega : cref.toNat + 3 + r1.toNat < 2 ^ 64)]
                using hge_mod
            rw [hnlits_eq, ← hcv1_eq] at hge
            exact Nat.not_lt.mpr hge
          s15_head_steps
          exact hJ25 () mj ⟨rfl, fastProp_findRepl_bad_oob (st := sem1) (cref := cref.toNat)
            (r := r1.toNat) (hi_lt := hfit1_ar hr1_csz) hcand_ge⟩
    · have hr1_eq : r1.toNat = csz32.toNat := Nat.le_antisymm hr1_le (Nat.le_of_not_lt hc)
      s15_head_steps
      exact hB1 (0xFFFFFFFF#32, 0#32, r1, ()) mj ⟨rfl, Or.inl ⟨rfl, fun k hk1 hk2 => by
        rw [← hcsz32_nat, ← hr1_eq] at hk2; exact hseen1 k hk1 hk2⟩⟩
  · intro B1 L1 _ hL1; s15_head_steps
    exact hL1 _ (srch_v, ()) mj ⟨rfl, Nat.le_refl _, hcsz32_nat ▸ Nat.le_of_lt hsrch_lt, rfl,
      fun _ hk1 hk2 => absurd hk1 (Nat.not_le.mpr hk2)⟩

private def s15LargePushExpr (h_p cbase pAr pWvec pWstk off_v p2_v q_v end_v : Val i64)
    (ri_f repl_f cref not_lit other w0 : Val i32)
    (k_ok k_oom : Val i64 → Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  .let_ (Op.mk (.zext 32 64) (.var cref, ())) fun x166 =>
  .let_ (Op.mk (.add i64) (.var x166.1, (.imm (1 : BitVec 64), ()))) fun x167 =>
  .let_ (Op.mk (.mul i64) (.var x167.1, (.imm (4 : BitVec 64), ()))) fun x168 =>
  .let_ (Op.mk (.add i64) (.var pAr, (.var x168.1, ()))) fun x169 =>
  .store (.var ri_f) (.var x169.1) (
    .let_ (Op.mk (.add i64) (.var cbase, (.imm (1 : BitVec 64), ()))) fun x170 =>
    .let_ (Op.mk (.mul i64) (.var x170.1, (.imm (4 : BitVec 64), ()))) fun x171 =>
    .let_ (Op.mk (.add i64) (.var pAr, (.var x171.1, ()))) fun x172 =>
    .store (.var repl_f) (.var x172.1) (
      .let_ (Op.mk (.zext 32 64) (.var ri_f, ())) fun x173 =>
      .let_ (Op.mk (.add i64) (.var cbase, (.var x173.1, ()))) fun x174 =>
      .let_ (Op.mk (.mul i64) (.var x174.1, (.imm (4 : BitVec 64), ()))) fun x175 =>
      .let_ (Op.mk (.add i64) (.var pAr, (.var x175.1, ()))) fun x176 =>
      .store (.var not_lit) (.var x176.1) (
        .let_ (Op.mk (.sub i64) (.var p2_v, (.var off_v, ()))) fun x177 =>
        .let_ (Op.mk (.sub i64) (.var q_v, (.var off_v, ()))) fun x178 =>
        .let_ (Op.mk (.sub i64) (.var end_v, (.var off_v, ()))) fun x179 =>
        .let_ (Op.mk (.and i32) (.var other, (.imm (2147483647 : BitVec 32), ()))) fun x180 =>
        .call "full_watch_push" (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
          (.var h_p, (.var repl_f, (.var x180.1, (.var cref, (.imm (2 : BitVec 32), ())))))
          fun x181 =>
        .let_ (Op.mk (.zext 32 64) (.var not_lit, ())) fun x182 =>
        .let_ (Op.mk (.sext 32 64) (.imm (1 : BitVec 32), ())) fun x183 =>
        .let_ (Op.mk (.shl i64) (.var x182.1, (.var x183.1, ()))) fun x184 =>
        .let_ (Op.mk (.mul i64) (.var x184.1, (.imm (4 : BitVec 64), ()))) fun x185 =>
        .let_ (Op.mk (.add i64) (.var pWvec, (.var x185.1, ()))) fun x186 =>
        .load i32 (.var x186.1) fun x187 =>
        .let_ (Op.mk (.zext 32 64) (.var x187, ())) fun x188 =>
        .let_ (Op.mk (.add i64) (.var x188.1, (.var x177.1, ()))) fun x189 =>
        .let_ (Op.mk (.add i64) (.var x188.1, (.var x178.1, ()))) fun x190 =>
        .let_ (Op.mk (.add i64) (.var x188.1, (.var x179.1, ()))) fun x191 =>
        .jnz (.var x181.1)
          (k_ok x188.1 x189.1 x190.1 x191.1) (
          .let_ (Op.mk (.add i64) (.var cbase, (.imm (1 : BitVec 64), ()))) fun x192 =>
          .let_ (Op.mk (.mul i64) (.var x192.1, (.imm (4 : BitVec 64), ()))) fun x193 =>
          .let_ (Op.mk (.add i64) (.var pAr, (.var x193.1, ()))) fun x194 =>
          .store (.var not_lit) (.var x194.1) (
            .let_ (Op.mk (.zext 32 64) (.var ri_f, ())) fun x195 =>
            .let_ (Op.mk (.add i64) (.var cbase, (.var x195.1, ()))) fun x196 =>
            .let_ (Op.mk (.mul i64) (.var x196.1, (.imm (4 : BitVec 64), ()))) fun x197 =>
            .let_ (Op.mk (.add i64) (.var pAr, (.var x197.1, ()))) fun x198 =>
            .store (.var repl_f) (.var x198.1) (
              .let_ (Op.mk (.mul i64) (.var x190.1, (.imm (4 : BitVec 64), ()))) fun x199 =>
              .let_ (Op.mk (.add i64) (.var pWstk, (.var x199.1, ()))) fun x200 =>
              .store (.var w0) (.var x200.1) (
                .let_ (Op.mk (.add i64) (.var x190.1, (.imm (1 : BitVec 64), ()))) fun x201 =>
                .let_ (Op.mk (.mul i64) (.var x201.1, (.imm (4 : BitVec 64), ()))) fun x202 =>
                .let_ (Op.mk (.add i64) (.var pWstk, (.var x202.1, ()))) fun x203 =>
                .store (.var cref) (.var x203.1) (
                  .let_ (Op.mk (.add i64) (.var x190.1, (.imm (2 : BitVec 64), ()))) fun x204 =>
                  .let_ (Op.mk (.add i64) (.var h_p, (.imm (760 : BitVec 64), ()))) fun x205 =>
                  .store (t := i64) (.imm (1 : BitVec 64)) (.var x205.1)
                    (k_oom x188.1 x189.1 x204.1 x191.1)
                )
              )
            )
          )
        )
      )
    )
  )

private theorem s15_large_push_wp {Γ : Env}
    (hPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sem1 : FullState}
    {not_lit w0 other cref ri_f repl_f : BitVec 32}
    {off_v p_v q_v end_v tend_v unass_v unfl_v : BitVec 64}
    {nl_lvl0 : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    {k_ok k_oom : Val i64 → Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]}
    (_hmaxv : c.max_vars < 2 * dimacsBound) (har : c.arena_cap < 2 * dimacsBound)
    (hlen0 : s.LengthsOk c) (_hcv0 : s.core.cur_vars ≤ c.max_vars)
    (hpi1 : PropLitInv c F0 F_cur s sem1 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hlen1_mem : (fastPropMem s sem1).LengthsOk c)
    (hcr_lt : cref.toNat < 0x80000000)
    (hcr_ref1 : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    (hfit1 : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (har4 : sem1.core.arena[cref.toNat + 4]? = some not_lit)
    (hnot_st1 : not_lit.toNat < 2 * sem1.core.cur_vars)
    (_hother_lt : other.toNat < 2 * sem1.core.cur_vars)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hr2 : 2 ≤ ri_f.toNat) (hr_lt : ri_f.toNat < fullArenaClauseSizeCore sem1.core cref.toNat)
    (hrepl_def : repl_f = sem1.core.arena[cref.toNat + 3 + ri_f.toNat]'(by
      rw [hpi1.len.core_ok.arena_len_arr]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hr_lt _)
        (Nat.le_trans hfit1 hpi1.len.core_ok.arena_len_le)))
    (hcand : repl_f.toNat < 2 * sem1.core.cur_vars ∧
      ((sem1.core.vals[repl_f.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false)
    (h1_idx : (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1)
    (h3_idx : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (h4_idx : (cref.setWidth 64 + 3#64 + 1#64).toNat = cref.toNat + 4)
    (htend1_eq : tend_v.toNat = sem1.core.trail_end) (hunass1_eq : unass_v = sem1.core.unassigned)
    (hunfl1_eq : unfl_v = sem1.core.unflushed)
    (hnl1 : sem1.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0)
    (hoom1 : sem1.core.oom = 0#64) (hct1 : sem1.core.confl_type = s.core.confl_type)
    (hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2) (hq_le : q_v.toNat ≤ p_v.toNat)
    (hq_lt : q_v.toNat < c.wcap)
    (hm : (FullMem c (fastPropMem s sem1) ⋆ R) m)
    (hk_ok : ∀ (st4 : FullState) (off4_v : BitVec 64) (m_p : Mem 64),
      (off4_v + (end_v - off_v)).toNat -
        (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat < end_v.toNat - p_v.toNat →
      PropLitInv c F0 F_cur s st4 not_lit.toNat off4_v.toNat
        (off4_v + (q_v - off_v)).toNat (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat
        (off4_v + (end_v - off_v)).toNat →
      tend_v.toNat = st4.core.trail_end → unass_v = st4.core.unassigned →
      unfl_v = st4.core.unflushed → st4.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 →
      st4.core.oom = 0#64 → st4.core.confl_type = s.core.confl_type →
      (FullMem c (fastPropMem s st4) ⋆ R) m_p →
      wp Γ Q X (k_ok off4_v (off4_v + (p_v + 1#64 + 1#64 - off_v)) (off4_v + (q_v - off_v))
        (off4_v + (end_v - off_v))) m_p)
    (hk_oom : ∀ (st6 : FullState) (off4_v : BitVec 64) (m_f : Mem 64),
      PropLitInv c F0 F_cur s st6 not_lit.toNat off4_v.toNat
        (off4_v + (q_v - off_v) + 2#64).toNat (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat
        (off4_v + (end_v - off_v)).toNat →
      tend_v.toNat = st6.core.trail_end → unass_v = st6.core.unassigned →
      unfl_v = st6.core.unflushed → st6.core.oom ≠ 0#64 →
      (FullMem c (fastPropMem s st6) ⋆ R) m_f →
      wp Γ Q X (k_oom off4_v (off4_v + (p_v + 1#64 + 1#64 - off_v))
        (off4_v + (q_v - off_v) + 2#64) (off4_v + (end_v - off_v))) m_f) :
    wp Γ Q X (s15LargePushExpr c.hdr (cref.setWidth 64 + 3#64) c.pArena c.pWvec c.pWstk
      off_v (p_v + 1#64 + 1#64) q_v end_v ri_f repl_f cref not_lit other w0 k_ok k_oom) m := by
  unfold dimacsBound at har
  have haren1 := hpi1.len.core_ok.arena_len_arr
  have halen1_le := hpi1.len.core_ok.arena_len_le
  have _hm1_aren := hlen1_mem.core_ok.arena_len_arr
  have _hm1_wvec := hlen1_mem.core_ok.wvec_len
  have hfit1_ar : ∀ {r}, r < fullArenaClauseSizeCore sem1.core cref.toNat →
      cref.toNat + 3 + r < sem1.core.arena.length := fun hr => by
    rw [haren1]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hr _) (Nat.le_trans hfit1 halen1_le)
  have h3r_idx : (cref.setWidth 64 + 3#64 + ri_f.setWidth 64).toNat =
      cref.toNat + 3 + ri_f.toNat := by
    rw [bv64_add_toNat (by
      rw [h3_idx, bv_c0_zext32_64]
      exact Nat.lt_of_lt_of_le (hfit1_ar hr_lt) (Nat.le_trans
        (Nat.le_of_eq haren1) (Nat.le_of_lt (Nat.lt_trans har (by decide))))),
      h3_idx, bv_c0_zext32_64]
  have h1_lt_ar : cref.toNat + 1 < c.arena_cap := by
    have := Nat.lt_of_lt_of_le (hfit1_ar hr_lt) (Nat.le_of_eq haren1); omega
  have h4_lt_ar : cref.toNat + 4 < c.arena_cap := by
    have := Nat.lt_of_lt_of_le (hfit1_ar hr_lt) (Nat.le_of_eq haren1); omega
  have h3r_lt_ar : cref.toNat + 3 + ri_f.toNat < c.arena_cap :=
    Nat.lt_of_lt_of_le (hfit1_ar hr_lt) (Nat.le_of_eq haren1)
  have hcr_lt_alen1 : cref.toNat < sem1.core.arena_len := by omega
  unfold s15LargePushExpr
  s15_head_steps
  let st3 : FullState :=
    { sem1 with core := { sem1.core with
        arena := ((sem1.core.arena.set (cref.toNat + 1) (BitVec.ofNat 32 ri_f.toNat)).set
          (cref.toNat + 4) repl_f).set (cref.toNat + 3 + ri_f.toNat) not_lit } }
  have h3r_ne1 : cref.toNat + 1 ≠ cref.toNat + 3 + ri_f.toNat := by omega
  have hrepl_set1 : repl_f = (sem1.core.arena.set (cref.toNat + 1)
      (BitVec.ofNat 32 ri_f.toNat))[cref.toNat + 3 + ri_f.toNat]'(by
        simp [hfit1_ar hr_lt]) := by
    rw [List.getElem_set_ne h3r_ne1]; exact hrepl_def
  have ⟨hlen3, hnw3, hsw3, hperm13, hcr_ref3, hcsz3, hrepl_lt,
      hrepl_ne_not, hw0_ne_ff, hcr_ne_ff⟩ :=
    fastProp_b1_swap (other := other) (r := ri_f.toNat) hpi1 hcr_lt_alen1
      hcr_ref1 hfit1 har4 hr2 hr_lt hrepl_set1
      (by simpa only [List.getElem?_eq_getElem (hfit1_ar hr_lt), Option.getD_some,
        ← hrepl_def] using hcand)
  have hri32 : BitVec.setWidth 32 ri_f = ri_f := by apply BitVec.eq_of_toNat_eq; simp
  have hm3 : (FullMem c (fastPropMem s st3) ⋆ R) m := by
    simpa only [st3, fastPropMem_arena, BitVec.ofNat_eq_ofNat, BitVec.ofNat_toNat, hri32,
      h1_idx, h4_idx, h3r_idx, fastPropMem_with_arena] using hm
  c0_call hPush
  refine ⟨c, fastPropMem s st3, R, rfl,
    fastPropMem_lengthsOk hlen0 hlen3 (hpi1.ag.get FullCoreState.cur_vars)
      (hpi1.ag.get FullCoreState.propagated) rfl,
    fastPropMem_watchLayout hsw3.layout rfl,
    fun h => absurd h (by decide), fun _ => ⟨hw0_ne_ff, hcr_ne_ff⟩,
    hm3, fun pok wvec' wstk' wlen' wu' wsort' m_p hlen_p hlay_p hpres_o
      hpok_t hpok_f hm_p => ?_⟩
  let st4 : FullState :=
    { st3 with
      core := { st3.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
      scratch := { st3.scratch with wsort := wsort' } }
  have hs4_eq :
      { fastPropMem s st3 with
        core := { (fastPropMem s st3).core with
          wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        scratch := { (fastPropMem s st3).scratch with wsort := wsort' } } =
      fastPropMem s st4 :=
    fastPropMem_with_push_rec s st3 wvec' wstk' wlen' wu' wsort'
  rw [hs4_eq] at hpres_o hpok_t hpok_f hm_p
  unfold fullWatchSize fullWatchOff at hpres_o hpok_t hpok_f
  simp only [fastPropMem_watchSize, fastPropMem_watchOff, fastPropMem_wstk,
    fastPropMem_cur_vars] at hpres_o hpok_t hpok_f
  have hlen4 : st4.LengthsOk c :=
    ⟨{ hlen3.core_ok with
        wvec_len := by simpa only [st4, fastPropMem_wvec] using hlen_p.core_ok.wvec_len
        wstk_len_arr := by
          simpa only [st4, fastPropMem_wstk] using hlen_p.core_ok.wstk_len_arr
        wlen_le := by simpa only [st4, fastPropMem_wlen] using hlen_p.core_ok.wlen_le },
     { hlen3.scratch_ok with
        wsort_len := by simpa only [st4, fastPropMem_wsort] using hlen_p.scratch_ok.wsort_len }⟩
  have hnw4 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st4.core) :=
    fullWitnessInv_nw_congr hlen4.core_ok.cur_vars_le hnw3
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hst4_alen := hlen4.core_ok.arena_len_arr
  have hwvec'_len := hlen4.core_ok.wvec_len
  have hwstk'_len := hlen4.core_ok.wstk_len_arr
  have hidx0_nat : (not_lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * not_lit.toNat :=
    fc_bv64_shl1_u32_nat not_lit
  have hnl_eq_xor : (not_lit ^^^ 1#32) ^^^ 1#32 = not_lit := by
    rw [BitVec.xor_assoc, show (1#32 ^^^ 1#32 : BitVec 32) = 0#32 from by decide,
      BitVec.xor_zero]
  have hlay4 : WatchStackLayout st4.core :=
    hlay_p.with_wstk (by dsimp only [st4]; exact (fastPropMem_cur_vars s st3).symm) rfl rfl rfl
  have ⟨hoff4_bd, hoff4_nat, hp4_nat, hq4_nat, hend4_nat, hq4_1, hq4_2,
      hsw4'⟩ := propLit_b1_after_push (c := c) (F_cur := F_cur) (lit := not_lit ^^^ 1#32)
    (st3 := st3) (st4 := st4) (other := other) (pok := pok) (off_v := off_v) (p_v := p_v)
    (q_v := q_v) (end_v := end_v) (idx0 := (not_lit.setWidth 64 <<< (1 : Nat)).toNat)
    (by rw [hidx0_nat, hnl_eq_xor]) rfl
    (by rw [hnl_eq_xor]; exact hnot_st1) hlen4 hlay4
    (by rw [hnl_eq_xor]; exact hsw3) rfl hrepl_lt
    (by rw [hnl_eq_xor]; exact hrepl_ne_not) hcr_lt hcr_ref3 hp2_nat hq_le
    (fun l hl hne => hpres_o l hl hne)
    (fun ht => let ⟨_, _, hsz, hpre, hw0, hw1⟩ := hpok_t ht; ⟨hsz, hpre, hw0, hw1 rfl⟩)
    (fun hf => (hpok_f hf).1 hrepl_lt)
  simp only [hnl_eq_xor] at hoff4_bd hoff4_nat hp4_nat hq4_nat hend4_nat hsw4'
  have hnot_max4 : not_lit.toNat < 2 * c.max_vars :=
    Nat.lt_of_lt_of_le hnot_st1 (Nat.mul_le_mul_left 2 hlen4.core_ok.cur_vars_le)
  have hidx0_lt4 : (not_lit.setWidth 64 <<< (1 : Nat)).toNat < st4.core.wvec.length := by
    rw [hidx0_nat, hwvec'_len, show 4 * c.max_vars = 2 * (2 * c.max_vars) from by omega]
    exact Nat.mul_lt_mul_of_pos_left hnot_max4 (by decide)
  have hm4_mem_len := fastPropMem_lengthsOk hlen0 hlen4
    (by dsimp [st4, st3]; exact hpi1.cur_vars_eq)
    (by dsimp [st4, st3]; exact hpi1.ag.get FullCoreState.propagated) rfl
  have hm4_wvec := hm4_mem_len.core_ok.wvec_len
  let off4_v : BitVec 64 := (st4.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
    hidx0_lt4).setWidth 64
  let q4_v := off4_v + (q_v - off_v)
  have hq4_lt_c : q4_v.toNat < c.wcap := by
    rw [hq4_nat]; have := hoff4_bd; have := hpi1.sw.q_ge; have := hpi1.sw.p_le_end
    have := hlen4.core_ok.wlen_le; omega
  have hq4_1_lt_c : (q4_v + (1 : BitVec 64)).toNat < c.wcap := by
    rw [hq4_1, hq4_nat]; have := hoff4_bd; have := hpi1.sw.q_ge; have := hpi1.sw.p_le_end
    have := hlen4.core_ok.wlen_le; omega
  have hidx0_lt4_m :
      (not_lit.setWidth 64 <<< (1 : Nat)).toNat < (fastPropMem s st4).core.wvec.length := by
    rw [hm4_wvec, hidx0_nat]; omega
  have hoff4_mem_eq :
      ((fastPropMem s st4).core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
        hidx0_lt4_m).setWidth 64 = off4_v :=
    congrArg (BitVec.setWidth 64) (fc_getElem_wvec s st4)
  have hq4_mem_lt_c :
      (BitVec.setWidth 64 ((fastPropMem s st4).core.wvec[
        (not_lit.setWidth 64 <<< (1 : Nat)).toNat]'hidx0_lt4_m) + (q_v - off_v)).toNat <
        c.wcap := by
    rw [hoff4_mem_eq]; exact hq4_lt_c
  have hq4_1_mem_lt_c :
      (BitVec.setWidth 64 ((fastPropMem s st4).core.wvec[
        (not_lit.setWidth 64 <<< (1 : Nat)).toNat]'hidx0_lt4_m) + (q_v - off_v) +
        (1 : BitVec 64)).toNat < c.wcap := by
    rw [hoff4_mem_eq]; exact hq4_1_lt_c
  have hidx0_lt4_2 : 2 * not_lit.toNat < st4.core.wvec.length := by
    rw [← hidx0_nat]; exact hidx0_lt4
  have hoff4_eq_2 :
      (st4.core.wvec[2 * not_lit.toNat]'hidx0_lt4_2).setWidth 64 = off4_v :=
    congrArg (BitVec.setWidth 64) (fc_getElem_eq_of_idx hidx0_nat hidx0_lt4 hidx0_lt4_2).symm
  have hq4_2_lt_c :
      (BitVec.setWidth 64 (st4.core.wvec[2 * not_lit.toNat]'hidx0_lt4_2) +
        (q_v - off_v)).toNat < c.wcap := by
    rw [hoff4_eq_2]; exact hq4_lt_c
  have hq4_1_2_lt_c :
      (BitVec.setWidth 64 (st4.core.wvec[2 * not_lit.toNat]'hidx0_lt4_2) +
        (q_v - off_v) + (1 : BitVec 64)).toNat < c.wcap := by
    rw [hoff4_eq_2]; exact hq4_1_lt_c
  have hag4 : AgreesExcept propLitCoreMask s.core st4.core :=
    hpi1.ag.update (fun k => { k with
      arena := st4.core.arena, wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' })
  have hperm4 : FullPropDecSpecs.FullArenaPermEq s.core st4.core := hpi1.perm.trans hperm13
  have hsc4 : st4.scratch = { s.scratch with
      search_ticks := st4.scratch.search_ticks, wsort := st4.scratch.wsort,
      phases := st4.scratch.phases } := by
    dsimp only [st4, st3]; rw [hpi1.sc_eq]
  have hnl4 : st4.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 := hnl1
  have hm4_aren := hm4_mem_len.core_ok.arena_len_arr
  have hm4_wstk := hm4_mem_len.core_ok.wstk_len_arr
  s15_head_steps
  · dsimp only
    simp only [hoff4_mem_eq]
    exact hk_ok st4 off4_v m_p (by
      have he4 : (off4_v + (end_v - off_v)).toNat =
          fullWatchOffCore st4.core not_lit.toNat + (end_v.toNat - off_v.toNat) := hend4_nat
      have hp4 : (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat =
          fullWatchOffCore st4.core not_lit.toNat + (p_v.toNat + 2 - off_v.toNat) := by
        simpa only [BitVec.ofNat_eq_ofNat] using hp4_nat
      rw [he4, hp4]
      exact propLit_measure_lt (Nat.le_trans hpi1.sw.q_ge hq_le) hpi1.sw.p_le_end)
      ⟨hlen4, hnw4, hsw4', hag4, hpi1.tr.congr rfl rfl rfl, hperm4, hsc4, hpi1.not_f⟩
      htend1_eq hunass1_eq hunfl1_eq hnl4 hoom1 hct1 hm_p
  · have hfit4 : cref.toNat + 3 + fullArenaClauseSizeCore st4.core cref.toNat ≤
        sem1.core.arena_len := by
      change _ + fullArenaClauseSizeCore st3.core _ ≤ _; rw [hcsz3]; exact hfit1
    have hr_lt4 : ri_f.toNat < fullArenaClauseSizeCore st4.core cref.toNat := by
      change ri_f.toNat < fullArenaClauseSizeCore st3.core _; rw [hcsz3]; exact hr_lt
    have hpi6 := fastProp_b1_oom (off4_v := off4_v) hpi1 hlen4 hnw4
      hsw4' hperm4 rfl rfl hag4 (hpi1.tr.congr rfl rfl rfl) hsc4 hpi1.not_f
      hnot_st1 hq_le hcr_lt hcr_ref3 hflag hfit4 hr2 hr_lt4 hq4_nat
      hp4_nat hq4_2
    have hq4_1_off : (off4_v + (q_v - off_v) + 1#64).toNat =
        (off4_v + (q_v - off_v)).toNat + 1 := by
      simpa only [BitVec.ofNat_eq_ofNat] using hq4_1
    have hm6 : (FullMem c (fastPropMem s { st4 with core := { st4.core with
        arena := (st4.core.arena.set (cref.toNat + 4) not_lit).set
          (cref.toNat + 3 + ri_f.toNat) repl_f,
        wstk := (st4.core.wstk.set q4_v.toNat w0).set (q4_v.toNat + 1) cref,
        oom := 1#64 } }) ⋆ R) m := by
      simp only [BitVec.ofNat_eq_ofNat, hoff4_mem_eq, fastPropMem_arena, fastPropMem_wstk] at hm
      rw [h4_idx, h3r_idx, hq4_1_off] at hm
      rw [← fastPropMem_with_oom_revert]
      exact hm
    dsimp only
    simp only [hoff4_mem_eq, BitVec.ofNat_eq_ofNat]
    exact hk_oom _ off4_v m hpi6 htend1_eq hunass1_eq hunfl1_eq
      (by show (1 : BitVec 64) ≠ 0#64; decide) hm6

private def s15OvfFinishExpr (h_p pWvec pWstk : Val i64) (not_lit : Val i32)
    (off_v tend_v unass_v unfl_v ticks_v p_v q_v end_v : Val i64) (confl_v : Val .bool) :
    Expr Val Cont [.bool] :=
  .group (sig := [[i64, i64]])
    (fun L1 => .cons (fun q =>
      .let_ (Op.mk (.cmp .ult i64) (.var q.1, (.var end_v, ()))) fun v88 =>
      .jnz (.var v88.1) (
        .let_ (Op.mk (.mul i64) (.var q.2.1, (.imm (4 : BitVec 64), ()))) fun v89 =>
        .let_ (Op.mk (.add i64) (.var pWstk, (.var v89.1, ()))) fun v90 =>
        .let_ (Op.mk (.mul i64) (.var q.1, (.imm (4 : BitVec 64), ()))) fun v91 =>
        .let_ (Op.mk (.add i64) (.var pWstk, (.var v91.1, ()))) fun v92 =>
        .load i32 (.var v92.1) fun v93 =>
        .store (.var v93) (.var v90.1) (
          .let_ (Op.mk (.add i64) (.var q.2.1, (.imm (1 : BitVec 64), ()))) fun v94 =>
          .let_ (Op.mk (.add i64) (.var q.1, (.imm (1 : BitVec 64), ()))) fun v95 =>
          .jump L1.1 (.var v95.1, (.var v94.1, ()))
        )
      ) (
        .group (sig := [[i64]])
          (fun L3 => .cons (fun k =>
            .let_ (Op.mk (.cmp .ult i64) (.var k.1, (.var end_v, ()))) fun c3 =>
            .jnz (.var c3.1) (
              .let_ (Op.mk (.mul i64) (.var k.1, (.imm (4 : BitVec 64), ()))) fun o4 =>
              .let_ (Op.mk (.add i64) (.var pWstk, (.var o4.1, ()))) fun pk =>
              .store (t := i32) (.imm 0xFFFFFFFF#32) (.var pk.1) (
                .let_ (Op.mk (.add i64) (.var k.1, (.imm (1 : BitVec 64), ()))) fun k1 =>
                .jump L3.1 (.var k1.1, ())
              )
            ) (
              .let_ (Op.mk (.zext 32 64) (.var not_lit, ())) fun v89 =>
              .let_ (Op.mk (.sext 32 64) (.imm (1 : BitVec 32), ())) fun v90 =>
              .let_ (Op.mk (.shl i64) (.var v89.1, (.var v90.1, ()))) fun v91 =>
              .let_ (Op.mk (.add i64) (.var v91.1, (.imm (1 : BitVec 64), ()))) fun v92 =>
              .let_ (Op.mk (.mul i64) (.var v92.1, (.imm (4 : BitVec 64), ()))) fun v93 =>
              .let_ (Op.mk (.add i64) (.var pWvec, (.var v93.1, ()))) fun v94 =>
              .let_ (Op.mk (.sub i64) (.var q.2.1, (.var off_v, ()))) fun v95 =>
              .let_ (Op.mk (.trunc 64 32) (.var v95.1, ())) fun v96 =>
              .store (.var v96.1) (.var v94.1) (
                .let_ (Op.mk (.add i64) (.var h_p, (.imm (464 : BitVec 64), ()))) fun v97 =>
                .load i64 (.var v97.1) fun v98 =>
                .let_ (Op.mk (.sub i64) (.var end_v, (.var q.2.1, ()))) fun v99 =>
                .let_ (Op.mk (.add i64) (.var v98, (.var v99.1, ()))) fun v100 =>
                .let_ (Op.mk (.add i64) (.var h_p, (.imm (464 : BitVec 64), ()))) fun v101 =>
                .store (.var v100.1) (.var v101.1) (
                  .let_ (Op.mk (.add i64) (.var h_p, (.imm (144 : BitVec 64), ()))) fun v102 =>
                  .store (.var tend_v) (.var v102.1) (
                    .let_ (Op.mk (.add i64) (.var h_p, (.imm (792 : BitVec 64), ()))) fun v103 =>
                    .store (.var unass_v) (.var v103.1) (
                      .let_ (Op.mk (.add i64) (.var h_p, (.imm (512 : BitVec 64), ()))) fun v104 =>
                      .store (.var unfl_v) (.var v104.1) (
                        .group (sig := [[]])
                          (fun L4 => .cons (fun _ =>
                            .let_ (Op.mk (.not .bool) (.var confl_v, ())) fun v109 =>
                            .ret (.var v109.1, ())
                          ) .nil)
                          (fun L4 =>
                            .let_ (Op.mk (.add i64) (.var h_p, (.imm (520 : BitVec 64), ())))
                              fun vp0 =>
                            .load i64 (.var vp0.1) fun vp1 =>
                            .let_ (Op.mk (.cmp .eq i64) (.var vp1, (.imm (0 : BitVec 64), ())))
                              fun vp2 =>
                            .jnz (.var vp2.1) (
                              .let_ (Op.mk (.add i64) (.var h_p, (.imm (600 : BitVec 64), ())))
                                fun v105 =>
                              .load i64 (.var v105.1) fun v106 =>
                              .let_ (Op.mk (.add i64) (.var v106, (.var ticks_v, ()))) fun v107 =>
                              .let_ (Op.mk (.add i64) (.var h_p, (.imm (600 : BitVec 64), ())))
                                fun v108 =>
                              .store (.var v107.1) (.var v108.1) (
                                .jump L4.1 ()
                              )
                            ) (.jump L4.1 ())
                          )
                      )
                    )
                  )
                )
              )
            )
          ) .nil)
          (fun L3 => .jump L3.1 (.var q.2.1, ()))
      )
    ) .nil)
    (fun L1 => .jump L1.1 (.var p_v, (.var q_v, ())))

private theorem s15_ovf_finish_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sem : FullState} {not_lit : BitVec 32}
    {off_v tend_v unass_v unfl_v ticks_v p_v q_v end_v ignore_ref : BitVec 64}
    {confl_v : Bool} {R : Mem 64 → Prop} {mb : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hwc : c.wcap < 2 * dimacsBound) (_hcv0 : s.core.cur_vars ≤ c.max_vars)
    (hdense0 : s.core.dense_mode = 0#64) (hnot_lt : not_lit.toNat < 2 * s.core.cur_vars)
    (hpi : PropLitInv c F0 F_cur s sem not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat)
    (htend_eq : tend_v.toNat = sem.core.trail_end) (hunass_eq : unass_v = sem.core.unassigned)
    (hunfl_eq : unfl_v = sem.core.unflushed)
    (hcf_f : confl_v = false → sem.core.oom = 0#64 ∧ sem.core.confl_type = s.core.confl_type)
    (hcf_t : confl_v = true → PropLitConfl F_cur ignore_ref sem.core)
    (hmb : (FullMem c (fastPropMem s sem) ⋆ R) mb)
    (hret_st : ∀ (ok : Bool) (st : FullState) (ml : Mem 64),
      st.LengthsOk c → FullWitnessInv c F0 F_cur st.core →
      AgreesExcept propLitCoreMask s.core st.core →
      FullPropDecSpecs.FullTrailExt s.core st.core →
      FullPropDecSpecs.FullArenaPermEq s.core st.core →
      st.scratch = { s.scratch with
        search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
        phases := st.scratch.phases } →
      (ok = false → PropLitConfl F_cur ignore_ref st.core) →
      (ok = true → st.core.oom = 0#64 ∧ st.core.confl_type = s.core.confl_type) →
      (FullMem c st ⋆ R) ml → Q (ok, ()) ml) :
    wp Γ Q X (s15OvfFinishExpr c.hdr c.pWvec c.pWstk not_lit off_v tend_v unass_v unfl_v
      ticks_v p_v q_v end_v confl_v) mb := by
  have hnot_st : not_lit.toNat < 2 * sem.core.cur_vars := hpi.cur_vars_eq.symm ▸ hnot_lt
  have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_st
  have hend_wcap : end_v.toNat ≤ c.wcap := Nat.le_trans hend_le hwlen_le
  unfold dimacsBound at hwc
  have hwc64 : c.wcap + 1 < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_right hwc 1) (by decide)
  have hq_ge := hpi.sw.q_ge; have hq_le := hpi.sw.q_le_p; have hp_le := hpi.sw.p_le_end
  have hwstk_len := hpi.len.core_ok.wstk_len_arr; have hwvec_len := hpi.len.core_ok.wvec_len
  have hwvec_mem : (fastPropMem s sem).core.wvec.length = 4 * c.max_vars := by
    rw [fastPropMem_wvec]; exact hwvec_len
  have hidx1_nat :
      ((not_lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * not_lit.toNat + 1 :=
    fc_bv64_shl1_add1_nat not_lit
  let q_fin : Nat := q_v.toNat + (end_v.toNat - p_v.toNat)
  unfold s15OvfFinishExpr
  refine wp_loop_inv
    (fun (p_c, q_c, ()) m2 => ∃ wstk_c : List (BitVec 32),
      wstk_c.length = c.wcap ∧ p_v.toNat ≤ p_c.toNat ∧ p_c.toNat ≤ end_v.toNat ∧
      q_c.toNat = q_v.toNat + (p_c.toNat - p_v.toNat) ∧
      (∀ k, off_v.toNat ≤ k → k < q_v.toNat → wstk_c[k]? = sem.core.wstk[k]?) ∧
      (∀ k < p_c.toNat - p_v.toNat, wstk_c[q_v.toNat + k]? = sem.core.wstk[p_v.toNat + k]?) ∧
      (∀ k, p_c.toNat ≤ k → k < end_v.toNat → wstk_c[k]? = sem.core.wstk[k]?) ∧
      (∀ k, (k < off_v.toNat ∨ end_v.toNat ≤ k) → wstk_c[k]? = sem.core.wstk[k]?) ∧
      (FullMem c (fastPropMem s { sem with core := { sem.core with wstk := wstk_c } }) ⋆ R) m2)
    (fun (p_c, _, ()) _ => end_v.toNat - p_c.toNat)
    (fun L2 hL2 => by
      s15_head_steps
      exact hL2 (p_v, q_v, ()) mb ⟨sem.core.wstk, hwstk_len, Nat.le_refl _, hp_le, by omega,
        fun _ _ _ => rfl, fun _ hk => by omega, fun _ _ _ => rfl, fun _ _ => rfl, hmb⟩)
    (fun L2 (p_c, q_c, ()) m2 ⟨wstk_c, hwl2, hp_ge, hp_le2, hqc_eq,
        hpre, hsuf, hrem, hout, hm2⟩ ih2 => ?_)
  s15_head_steps
  · have hp_lt : p_c.toNat < end_v.toNat := hc
    have hstep := propLit_loop2_step hq_ge hq_le hp_ge hp_lt (by omega) (by omega)
      hpre hsuf hrem hout
    have hpc_add : (p_c + (1 : BitVec 64)).toNat = p_c.toNat + 1 := bv64_add1_toNat (by omega)
    have hqc_add : (q_c + (1 : BitVec 64)).toNat =
        q_v.toNat + ((p_c + (1 : BitVec 64)).toNat - p_v.toNat) := by
      rw [bv64_add1_toNat (by omega), hpc_add]; omega
    refine ih2 (p_c + (1 : BitVec 64), q_c + (1 : BitVec 64), ()) m (by dsimp only; omega)
      ⟨wstk_c.set q_c.toNat (wstk_c[p_c.toNat]'(by omega)), by simp [hwl2],
        by omega, by omega, hqc_add, ?_, ?_, ?_, ?_, by
          simpa only [fastPropMem_wstk, fastPropMem_with_wstk] using hm⟩
    · simpa only [← hqc_eq] using hstep.1
    · rw [hpc_add]; simpa only [← hqc_eq] using hstep.2.1
    · rw [hpc_add]; simpa only [← hqc_eq] using hstep.2.2.1
    · simpa only [← hqc_eq] using hstep.2.2.2
  · have hpc_eq : p_c.toNat = end_v.toNat := by c0_bound
    have hqfin_eq : q_c.toNat = q_fin := by dsimp [q_fin]; omega
    refine wp_loop_inv
      (fun (k_c, ()) m3 => ∃ wstk_k : List (BitVec 32),
        wstk_k.length = c.wcap ∧ q_fin ≤ k_c.toNat ∧ k_c.toNat ≤ end_v.toNat ∧
        (∀ i, (i < q_fin ∨ end_v.toNat ≤ i) → wstk_k[i]? = wstk_c[i]?) ∧
        (FullMem c (fastPropMem s { sem with core := { sem.core with wstk := wstk_k } }) ⋆ R) m3)
      (fun (k_c, ()) _ => end_v.toNat - k_c.toNat)
      (fun L3 hL3 => by
        s15_head_steps
        exact hL3 (q_c, ()) m2 ⟨wstk_c, hwl2, by omega, by omega, fun _ _ => rfl, hm2⟩)
      (fun L3 (k_c, ()) m3 ⟨wstk_k, hwl3, hk_ge, hk_le, hkeep, hm3⟩ ih3 => ?_)
    s15_head_steps
    · have hk_lt : k_c.toNat < end_v.toNat := hc
      have hk_add : (k_c + (1 : BitVec 64)).toNat = k_c.toNat + 1 :=
        bv64_add1_toNat (by omega)
      refine ih3 (k_c + (1 : BitVec 64), ()) m (by dsimp only; omega)
        ⟨wstk_k.set k_c.toNat 0xFFFFFFFF#32, by simp [hwl3], by omega, by omega,
          propLit_loop3_step hk_ge hk_lt hkeep, by
            simpa only [fastPropMem_wstk, fastPropMem_with_wstk] using hm⟩
    · have hk_eq : k_c.toNat = end_v.toNat := by c0_bound
      refine wp_join_group (ts := [])
        (fun () m4 => ∃ ticks_fin : BitVec 64,
          let sem' : FullState :=
            { sem with scratch := { sem.scratch with search_ticks := ticks_fin } }
          PropLitInv c F0 F_cur s sem' not_lit.toNat off_v.toNat q_v.toNat p_v.toNat
            end_v.toNat ∧
          (FullMem c { sem' with core := { sem'.core with
              wstk := wstk_k
              wvec := sem'.core.wvec.set (2 * not_lit.toNat + 1) ((q_c - off_v).setWidth 32)
              wusable := sem'.core.wusable + (end_v - q_c) } } ⋆ R) m4)
        ?_ ?_
      · rintro _ ⟨⟩ m4 ⟨ticks_fin, hpi', hm_rew⟩
        s15_head_steps
        have ⟨hl_f, hw_f, hag_f, htr_f, hperm_f, hsc_f, hcf_f', hoom_f, hm_f⟩ :=
          propLit_finish (ctype0 := s.core.confl_type) hpi' hdense0 hnot_st hwl3 hqfin_eq rfl
            hpre (fun k hk => hsuf k (by omega)) hout hkeep hcf_f hcf_t hm_rew
        exact hret_st (!confl_v) _ m4 hl_f hw_f hag_f htr_f hperm_f hsc_f hcf_f' hoom_f hm_f
      · intro L4 hL4
        s15_head_steps
        · let sem' : FullState :=
            { sem with scratch :=
                { sem.scratch with search_ticks := s.scratch.search_ticks + ticks_v } }
          have hpi' : PropLitInv c F0 F_cur s sem' not_lit.toNat off_v.toNat q_v.toNat p_v.toNat
              end_v.toNat :=
            { len := ⟨hpi.len.core_ok, hpi.len.scratch_ok.with_ticks _⟩
              nw := hpi.nw, sw := hpi.sw, ag := hpi.ag, tr := hpi.tr, perm := hpi.perm
              sc_eq := by dsimp only [sem']; rw [hpi.sc_eq]
              not_f := hpi.not_f }
          have hm_rew :
              (FullMem c { sem' with core := { sem'.core with
                  wstk := wstk_k
                  wvec := sem'.core.wvec.set (2 * not_lit.toNat + 1) ((q_c - off_v).setWidth 32)
                  wusable := sem'.core.wusable + (end_v - q_c) } } ⋆ R) m := by
            simp only [hidx1_nat, fastPropMem_wvec, fastPropMem_wusable,
              fastPropMem_search_ticks] at hm
            rw [htend_eq, hunass_eq, hunfl_eq] at hm
            rw [fastPropMem_finish_eq] at hm
            exact hm
          exact hL4 () m ⟨s.scratch.search_ticks + ticks_v, hpi', hm_rew⟩
        · let sem' : FullState :=
            { sem with scratch := { sem.scratch with search_ticks := s.scratch.search_ticks } }
          have hpi' : PropLitInv c F0 F_cur s sem' not_lit.toNat off_v.toNat q_v.toNat p_v.toNat
              end_v.toNat :=
            { len := ⟨hpi.len.core_ok, hpi.len.scratch_ok.with_ticks _⟩
              nw := hpi.nw, sw := hpi.sw, ag := hpi.ag, tr := hpi.tr, perm := hpi.perm
              sc_eq := by dsimp only [sem']; rw [hpi.sc_eq]
              not_f := hpi.not_f }
          have hm_rew :
              (FullMem c { sem' with core := { sem'.core with
                  wstk := wstk_k
                  wvec := sem'.core.wvec.set (2 * not_lit.toNat + 1) ((q_c - off_v).setWidth 32)
                  wusable := sem'.core.wusable + (end_v - q_c) } } ⋆ R) m := by
            simp only [hidx1_nat, fastPropMem_wvec, fastPropMem_wusable] at hm
            rw [htend_eq, hunass_eq, hunfl_eq, fastPropMem_def] at hm
            exact hm
          exact hL4 () m ⟨s.scratch.search_ticks, hpi', hm_rew⟩

private def s15OvfOomCompactExpr (h_p pWvec pWstk : Val i64) (not_lit : Val i32)
    (off_f pf qf ef : Val i64) : Expr Val Cont [.bool] :=
  .group (sig := [[i64, i64]])
    (fun L1 => .cons (fun q =>
      .let_ (Op.mk (.cmp .ult i64) (.var q.1, (.var ef, ()))) fun v88 =>
      .jnz (.var v88.1) (
        .let_ (Op.mk (.mul i64) (.var q.2.1, (.imm (4 : BitVec 64), ()))) fun v89 =>
        .let_ (Op.mk (.add i64) (.var pWstk, (.var v89.1, ()))) fun v90 =>
        .let_ (Op.mk (.mul i64) (.var q.1, (.imm (4 : BitVec 64), ()))) fun v91 =>
        .let_ (Op.mk (.add i64) (.var pWstk, (.var v91.1, ()))) fun v92 =>
        .load i32 (.var v92.1) fun v93 =>
        .store (.var v93) (.var v90.1) (
          .let_ (Op.mk (.add i64) (.var q.2.1, (.imm (1 : BitVec 64), ()))) fun v94 =>
          .let_ (Op.mk (.add i64) (.var q.1, (.imm (1 : BitVec 64), ()))) fun v95 =>
          .jump L1.1 (.var v95.1, (.var v94.1, ()))
        )
      ) (
        .group (sig := [[i64]])
          (fun L3 => .cons (fun k =>
            .let_ (Op.mk (.cmp .ult i64) (.var k.1, (.var ef, ()))) fun c3 =>
            .jnz (.var c3.1) (
              .let_ (Op.mk (.mul i64) (.var k.1, (.imm (4 : BitVec 64), ()))) fun o4 =>
              .let_ (Op.mk (.add i64) (.var pWstk, (.var o4.1, ()))) fun pk =>
              .store (t := i32) (.imm 0xFFFFFFFF#32) (.var pk.1) (
                .let_ (Op.mk (.add i64) (.var k.1, (.imm (1 : BitVec 64), ()))) fun k1 =>
                .jump L3.1 (.var k1.1, ())
              )
            ) (
              .let_ (Op.mk (.zext 32 64) (.var not_lit, ())) fun v89 =>
              .let_ (Op.mk (.sext 32 64) (.imm (1 : BitVec 32), ())) fun v90 =>
              .let_ (Op.mk (.shl i64) (.var v89.1, (.var v90.1, ()))) fun v91 =>
              .let_ (Op.mk (.add i64) (.var v91.1, (.imm (1 : BitVec 64), ()))) fun v92 =>
              .let_ (Op.mk (.mul i64) (.var v92.1, (.imm (4 : BitVec 64), ()))) fun v93 =>
              .let_ (Op.mk (.add i64) (.var pWvec, (.var v93.1, ()))) fun v94 =>
              .let_ (Op.mk (.sub i64) (.var q.2.1, (.var off_f, ()))) fun v95 =>
              .let_ (Op.mk (.trunc 64 32) (.var v95.1, ())) fun v96 =>
              .store (.var v96.1) (.var v94.1) (
                .let_ (Op.mk (.add i64) (.var h_p, (.imm (464 : BitVec 64), ()))) fun v97 =>
                .load i64 (.var v97.1) fun v98 =>
                .let_ (Op.mk (.sub i64) (.var ef, (.var q.2.1, ()))) fun v99 =>
                .let_ (Op.mk (.add i64) (.var v98, (.var v99.1, ()))) fun v100 =>
                .let_ (Op.mk (.add i64) (.var h_p, (.imm (464 : BitVec 64), ()))) fun v101 =>
                .store (.var v100.1) (.var v101.1) (
                  .let_ (Op.mk (.add i64) (.var h_p, (.imm (760 : BitVec 64), ()))) fun v102 =>
                  .store (t := i64) (.imm (1 : BitVec 64)) (.var v102.1) (
                    .ret (.imm false, ())
                  )
                )
              )
            )
          ) .nil)
          (fun L3 => .jump L3.1 (.var q.2.1, ()))
      )
    ) .nil)
    (fun L1 => .jump L1.1 (.var pf, (.var qf, ())))

private theorem s15_ovf_oom_compact_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s st' : FullState} {not_lit : BitVec 32}
    {off_f pf qf ef ignore_ref : BitVec 64} {R : Mem 64 → Prop} {mp : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hwc : c.wcap < 2 * dimacsBound) (hdense0 : s.core.dense_mode = 0#64)
    (hnot_st : not_lit.toNat < 2 * st'.core.cur_vars)
    (hpi : PropLitInv c F0 F_cur s st' not_lit.toNat off_f.toNat qf.toNat pf.toNat ef.toNat)
    (hmp : (FullMem c st' ⋆ R) mp)
    (hret_st : ∀ (ok : Bool) (st : FullState) (ml : Mem 64),
      st.LengthsOk c → FullWitnessInv c F0 F_cur st.core →
      AgreesExcept propLitCoreMask s.core st.core →
      FullPropDecSpecs.FullTrailExt s.core st.core →
      FullPropDecSpecs.FullArenaPermEq s.core st.core →
      st.scratch = { s.scratch with
        search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
        phases := st.scratch.phases } →
      (ok = false → PropLitConfl F_cur ignore_ref st.core) →
      (ok = true → st.core.oom = 0#64 ∧ st.core.confl_type = s.core.confl_type) →
      (FullMem c st ⋆ R) ml → Q (ok, ()) ml) :
    wp Γ Q X (s15OvfOomCompactExpr c.hdr c.pWvec c.pWstk not_lit off_f pf qf ef) mp := by
  have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_st
  have hend_wcap : ef.toNat ≤ c.wcap := Nat.le_trans hend_le hwlen_le
  unfold dimacsBound at hwc
  have hwc64 : c.wcap + 1 < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_right hwc 1) (by decide)
  have hq_ge := hpi.sw.q_ge; have hq_le := hpi.sw.q_le_p; have hp_le := hpi.sw.p_le_end
  have hwstk_p := hpi.len.core_ok.wstk_len_arr; have hwvec_p := hpi.len.core_ok.wvec_len
  have hcv_p := hpi.len.core_ok.cur_vars_le
  have hidx1_nat :
      ((not_lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * not_lit.toNat + 1 :=
    fc_bv64_shl1_add1_nat not_lit
  let q_fin : Nat := qf.toNat + (ef.toNat - pf.toNat)
  unfold s15OvfOomCompactExpr
  refine wp_loop_inv
    (fun (p_c, q_c, ()) m2 => ∃ wstk_c : List (BitVec 32),
      wstk_c.length = c.wcap ∧ pf.toNat ≤ p_c.toNat ∧ p_c.toNat ≤ ef.toNat ∧
      q_c.toNat = qf.toNat + (p_c.toNat - pf.toNat) ∧
      (∀ k, off_f.toNat ≤ k → k < qf.toNat → wstk_c[k]? = st'.core.wstk[k]?) ∧
      (∀ k < p_c.toNat - pf.toNat, wstk_c[qf.toNat + k]? = st'.core.wstk[pf.toNat + k]?) ∧
      (∀ k, p_c.toNat ≤ k → k < ef.toNat → wstk_c[k]? = st'.core.wstk[k]?) ∧
      (∀ k, (k < off_f.toNat ∨ ef.toNat ≤ k) → wstk_c[k]? = st'.core.wstk[k]?) ∧
      (FullMem c { st' with core := { st'.core with wstk := wstk_c } } ⋆ R) m2)
    (fun (p_c, _, ()) _ => ef.toNat - p_c.toNat)
    (fun L2 hL2 => by
      s15_head_steps
      exact hL2 (pf, qf, ()) mp ⟨st'.core.wstk, hwstk_p, Nat.le_refl _, hp_le, by omega,
        fun _ _ _ => rfl, fun _ hk => by omega, fun _ _ _ => rfl, fun _ _ => rfl, hmp⟩)
    (fun L2 (p_c, q_c, ()) m2 ⟨wstk_c, hwl2, hp_ge, hp_le2, hqc_eq,
        hpre, hsuf, hrem, hout, hm2⟩ ih2 => ?_)
  s15_head_steps
  · have hp_lt : p_c.toNat < ef.toNat := hc
    have hstep := propLit_loop2_step hq_ge hq_le hp_ge hp_lt (by omega) (by omega)
      hpre hsuf hrem hout
    have hpc_add : (p_c + (1 : BitVec 64)).toNat = p_c.toNat + 1 := bv64_add1_toNat (by omega)
    have hqc_add : (q_c + (1 : BitVec 64)).toNat =
        qf.toNat + ((p_c + (1 : BitVec 64)).toNat - pf.toNat) := by
      rw [bv64_add1_toNat (by omega), hpc_add]; omega
    refine ih2 (p_c + (1 : BitVec 64), q_c + (1 : BitVec 64), ()) m (by dsimp only; omega)
      ⟨wstk_c.set q_c.toNat (wstk_c[p_c.toNat]'(by omega)), by simp [hwl2],
        by omega, by omega, hqc_add, ?_, ?_, ?_, ?_, hm⟩
    · simpa only [← hqc_eq] using hstep.1
    · rw [hpc_add]; simpa only [← hqc_eq] using hstep.2.1
    · rw [hpc_add]; simpa only [← hqc_eq] using hstep.2.2.1
    · simpa only [← hqc_eq] using hstep.2.2.2
  · have hpc_eq : p_c.toNat = ef.toNat := by c0_bound
    have hqfin_eq : q_c.toNat = q_fin := by dsimp [q_fin]; omega
    refine wp_loop_inv
      (fun (k_c, ()) m3 => ∃ wstk_k : List (BitVec 32),
        wstk_k.length = c.wcap ∧ q_fin ≤ k_c.toNat ∧ k_c.toNat ≤ ef.toNat ∧
        (∀ i, (i < q_fin ∨ ef.toNat ≤ i) → wstk_k[i]? = wstk_c[i]?) ∧
        (FullMem c { st' with core := { st'.core with wstk := wstk_k } } ⋆ R) m3)
      (fun (k_c, ()) _ => ef.toNat - k_c.toNat)
      (fun L3 hL3 => by
        s15_head_steps
        exact hL3 (q_c, ()) m2 ⟨wstk_c, hwl2, by omega, by omega, fun _ _ => rfl, hm2⟩)
      (fun L3 (k_c, ()) m3 ⟨wstk_k, hwl3, hk_ge, hk_le, hkeep, hm3⟩ ih3 => ?_)
    s15_head_steps
    · have hk_lt : k_c.toNat < ef.toNat := hc
      have hk_add : (k_c + (1 : BitVec 64)).toNat = k_c.toNat + 1 :=
        bv64_add1_toNat (by omega)
      refine ih3 (k_c + (1 : BitVec 64), ()) m (by dsimp only; omega)
        ⟨wstk_k.set k_c.toNat 0xFFFFFFFF#32, by simp [hwl3], by omega, by omega,
          propLit_loop3_step hk_ge hk_lt hkeep, hm⟩
    · have hk_eq : k_c.toNat = ef.toNat := by c0_bound
      s15_head_steps
      let st_oom : FullState := { st' with core := { st'.core with oom := 1#64 } }
      have hpi_oom : PropLitInv c F0 F_cur s st_oom not_lit.toNat off_f.toNat qf.toNat pf.toNat
          ef.toNat :=
        { len := ⟨{ hpi.len.core_ok with wstk_len_arr := hwstk_p }, hpi.len.scratch_ok⟩
          nw := fullWitnessInv_nw_congr hpi.len.core_ok.cur_vars_le hpi.nw
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          sw := hpi.sw.with_nonwatch rfl rfl rfl rfl rfl
          ag := hpi.ag.update (fun k => { k with oom := 1#64 })
          tr := hpi.tr.congr rfl rfl rfl, perm := hpi.perm
          sc_eq := hpi.sc_eq, not_f := hpi.not_f }
      have hm_oom : (FullMem c { st_oom with core := { st_oom.core with
          wstk := wstk_k
          wvec := st_oom.core.wvec.set (2 * not_lit.toNat + 1) ((q_c - off_f).setWidth 32)
          wusable := st_oom.core.wusable + (ef - q_c) } } ⋆ R) m := by
        simp only [st_oom, hidx1_nat] at hm ⊢; exact hm
      have ⟨hl_f, hw_f, hag_f, htr_f, hperm_f, hsc_f, hcf_f', hoom_f, hm_f⟩ :=
        propLit_finish (ctype0 := s.core.confl_type) (confl_v := true)
          (ignore_ref := ignore_ref) hpi_oom hdense0 hnot_st hwl3 hqfin_eq rfl
          hpre (fun k hk => hsuf k (by omega)) hout hkeep
          (by simp) (fun _ => Or.inl (by show (1#64 : BitVec 64) ≠ 0#64; decide)) hm_oom
      exact hret_st false _ m hl_f hw_f hag_f htr_f hperm_f hsc_f hcf_f' hoom_f hm_f

/-! ## 4. Cold Overflow Handler Proof (`full_prop_lit_ovf_s15_wp`) -/

theorem full_prop_lit_ovf_s15_wp (Γ : Env)
    (hPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullPropLitOvfS15Spec args m Q X →
      Func.wp Γ full_prop_lit_ovf_s15_body args m Q X := by
  rintro ⟨h, not_lit, ignore_ref, pr, qr, di, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, dlen, rfl, hlen0, hnw0, hdense0, hoom0, hnot_lt, hnot_f0, hsw0,
      hdi_eq, hdlen_le, hdel0, hm, hQ⟩
  have hmaxv := c.hmaxv; have har := c.harena; have hwc := c.hwcap; have hdelc := c.hdel
  unfold dimacsBound at hmaxv har hwc hdelc
  have hcv0 := hlen0.core_ok.cur_vars_le
  have hret_st : ∀ (ok : Bool) (st : FullState) (ml : Mem 64),
      st.LengthsOk c → FullWitnessInv c F0 F_cur st.core →
      AgreesExcept propLitCoreMask s.core st.core →
      FullPropDecSpecs.FullTrailExt s.core st.core →
      FullPropDecSpecs.FullArenaPermEq s.core st.core →
      st.scratch = { s.scratch with
        search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
        phases := st.scratch.phases } →
      (ok = false → PropLitConfl F_cur ignore_ref st.core) →
      (ok = true → st.core.oom = 0#64 ∧ st.core.confl_type = s.core.confl_type) →
      (FullMem c st ⋆ R) ml → Q (ok, ()) ml := by
    intro ok st ml hst_l hst_w hag htr hperm hsc hcf hok_oom hml
    have hst_eq := propLit_eq_upd hag hsc
    have hst_l' := hst_l; have hst_w' := hst_w
    have htr' : FullTrailExt s.core st.core := ⟨htr.te_ge, htr.trl_pref, htr.lvl_pres⟩
    have hperm' : FullArenaPermEq s.core st.core := ⟨hag.get FullCoreState.arena_len, hperm⟩
    rw [hst_eq] at hst_l' hst_w' htr' hperm' hml
    refine hQ ok st.core.vals st.core.flags st.core.lvl st.core.rsns st.core.trl st.core.trail_pos
      st.core.trail_end st.core.unassigned st.core.unflushed st.core.wvec st.core.arena
      st.core.wstk st.core.wlen st.core.wusable st.core.confl_type st.core.confl_ref
      st.core.confl_lit0 st.core.confl_lit1 st.core.oom st.scratch.search_ticks st.scratch.wsort
      st.scratch.phases ml hst_l' hst_w' htr' hperm' ?_ hok_oom hml
    intro hf; rcases (hcf hf) with ho | ⟨hc1, hc2⟩
    · exact Or.inl ho
    · refine Or.inr ⟨?_, hc2⟩
      have hc1' : FullConflictOkW F_cur st := fullConflOkW_to_fullConflictOkW hc1
      rwa [hst_eq] at hc1'
  have hwv0 := hlen0.core_ok.wvec_len
  have hdel_len0 := hlen0.scratch_ok.delayed_len_arr
  have hclv_lt32 : s.core.cur_level < 2 ^ 32 := by
    have hcl := hnw0.cur_level_le
    change s.core.cur_level ≤ s.core.trail_end at hcl
    have := hlen0.core_ok.trail_end_le; omega
  have hte0_lt64 : s.core.trail_end < 2 ^ 64 := by
    have := hlen0.core_ok.trail_end_le; omega
  have hidx0_nat : (not_lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * not_lit.toNat :=
    fc_bv64_shl1_u32_nat not_lit
  have hidx1_nat :
      ((not_lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * not_lit.toNat + 1 :=
    fc_bv64_shl1_add1_nat not_lit
  have hsz0_eq :
      ((s.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'(by
        rw [hidx1_nat, hwv0]; omega)).setWidth 64).toNat =
      fullWatchSizeCore s.core not_lit.toNat := by
    unfold fullWatchSizeCore; rw [bv_c0_zext32_64]
    exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx hidx1_nat _)
  have hqr_le_pr : qr.toNat ≤ pr.toNat := by have := hsw0.q_le_p; omega
  have hpr_le_sz0 : pr.toNat ≤ fullWatchSizeCore s.core not_lit.toNat := by
    have := hsw0.p_le_end; omega
  unfold Func.wp full_prop_lit_ovf_s15_body
  s15_hsteps
  refine wp_loop_group
    (fun rem (j_v, ()) mj => ∃ (st : FullState) (idx : Nat),
      rem = dlen - idx ∧ j_v.toNat = 3 * idx ∧ idx ≤ dlen ∧
      st.LengthsOk c ∧ FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st.core) ∧
      SplitWatchesInv F_cur st.core not_lit.toNat
        (fullWatchOffCore st.core not_lit.toNat)
        (fullWatchOffCore st.core not_lit.toNat + qr.toNat)
        (fullWatchOffCore st.core not_lit.toNat + pr.toNat)
        (fullWatchOffCore st.core not_lit.toNat + fullWatchSizeCore s.core not_lit.toNat) ∧
      AgreesExcept propLitCoreMask s.core st.core ∧
      FullPropDecSpecs.FullTrailExt s.core st.core ∧
      FullPropDecSpecs.FullArenaPermEq s.core st.core ∧
      st.scratch = { s.scratch with
        search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
        phases := st.scratch.phases } ∧
      st.scratch.search_ticks = s.scratch.search_ticks ∧
      st.core.vals = s.core.vals ∧ st.core.lvl = s.core.lvl ∧
      st.core.trail_end = s.core.trail_end ∧ st.core.unassigned = s.core.unassigned ∧
      st.core.unflushed = s.core.unflushed ∧ st.core.oom = 0#64 ∧
      st.core.confl_type = s.core.confl_type ∧
      (FullMem c st ⋆ R) mj) ?_ ?_
  · rintro L rem ⟨j_v, ⟨⟩⟩ mj ih
      ⟨st, idx, rfl, hj_eq, hidx_le, hst_l, hst_nw, hst_sw, hag_st, htr_st, hperm_st,
        hsc_st, hticks_eq, hvals_eq, hlvl_eq, hte_eq, hun_eq, huf_eq, hoom_st, hct_st, hmj⟩
    have hcv_st : st.core.cur_vars = s.core.cur_vars := hag_st.get FullCoreState.cur_vars
    have halen_st : st.core.arena_len = s.core.arena_len := hag_st.get FullCoreState.arena_len
    have hcl_st : st.core.cur_level = s.core.cur_level := hag_st.get FullCoreState.cur_level
    have hnot_st : not_lit.toNat < 2 * st.core.cur_vars := hcv_st.symm ▸ hnot_lt
    have hdel_len_st : st.scratch.delayed.length = 3 * c.delayed_cap :=
      hst_l.scratch_ok.delayed_len_arr
    have hdel_eq_st : st.scratch.delayed = s.scratch.delayed := by rw [hsc_st]
    have hhref_st : fullArenaClauseRefsCore st.core = fullArenaClauseRefsCore s.core :=
      hperm_st.1
    have hnot_f_st : st.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 := hvals_eq ▸ hnot_f0
    s15_hsteps
    · have hlt_j : j_v.toNat < di.toNat := hc
      have hidx_lt : idx < dlen := by omega
      have h3i_lt : 3 * idx + 2 < st.scratch.delayed.length := by omega
      have hj1_nat : (j_v + 1#64).toNat = 3 * idx + 1 := by
        rw [BitVec.toNat_add, hj_eq]
        change (3 * idx + 1) % 2 ^ 64 = 3 * idx + 1
        exact Nat.mod_eq_of_lt (by omega)
      have hj2_nat : (j_v + 2#64).toNat = 3 * idx + 2 := by
        rw [BitVec.toNat_add, hj_eq]
        change (3 * idx + 2) % 2 ^ 64 = 3 * idx + 2
        exact Nat.mod_eq_of_lt (by omega)
      have hj3_nat : (j_v + 3#64).toNat = 3 * (idx + 1) := by
        rw [BitVec.toNat_add, hj_eq]
        change (3 * idx + 3) % 2 ^ 64 = 3 * (idx + 1)
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      obtain ⟨hrlit_lt, hrlit_ne, hrw0_f, hrcr_lt, hrcr_ref⟩ := hdel0 idx hidx_lt
      have hrlit_get : st.scratch.delayed[j_v.toNat]'(by omega) =
          s.scratch.delayed[3 * idx]?.getD 0#32 := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        simp only [hdel_eq_st, hj_eq]
      have hrw0_get : st.scratch.delayed[(j_v + 1#64).toNat]'(by rw [hj1_nat]; omega) =
          s.scratch.delayed[3 * idx + 1]?.getD 0#32 := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        simp only [hdel_eq_st, hj1_nat]
      have hrcr_get : st.scratch.delayed[(j_v + 2#64).toNat]'(by rw [hj2_nat]; omega) =
          s.scratch.delayed[3 * idx + 2]?.getD 0#32 := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        simp only [hdel_eq_st, hj2_nat]
      let rlit_v := st.scratch.delayed[j_v.toNat]'(by omega)
      let rw0_v := st.scratch.delayed[(j_v + 1#64).toNat]'(by rw [hj1_nat]; omega)
      let rcr_v := st.scratch.delayed[(j_v + 2#64).toNat]'(by rw [hj2_nat]; omega)
      have hrlit_lt_st : rlit_v.toNat < 2 * st.core.cur_vars := by
        dsimp only [rlit_v]; rw [hrlit_get, hcv_st]; exact hrlit_lt
      have hrlit_ne_st : rlit_v.toNat ≠ not_lit.toNat := by
        dsimp only [rlit_v]; rw [hrlit_get]; exact hrlit_ne
      have hrw0_f_st : (rw0_v &&& 0x80000000#32) = 0#32 := by
        dsimp only [rw0_v]; rw [hrw0_get]; exact hrw0_f
      have hrcr_lt_st : rcr_v.toNat < 0x80000000 := by
        dsimp only [rcr_v]; rw [hrcr_get]; exact hrcr_lt
      have hrcr_ref_st : rcr_v.toNat ∈ fullArenaClauseRefsCore st.core := by
        dsimp only [rcr_v]; rw [hrcr_get, hhref_st]; exact hrcr_ref
      have hrw0_ne : rw0_v ≠ 0xFFFFFFFF#32 := fun heq => by
        rw [heq] at hrw0_f_st; exact absurd hrw0_f_st (by decide)
      have hrcr_ne : rcr_v ≠ 0xFFFFFFFF#32 := fun heq => by
        rw [heq] at hrcr_lt_st; revert hrcr_lt_st; decide
      c0_call hPush
      refine ⟨c, st, R, rfl, hst_l, hst_sw.layout, fun h => absurd h (by decide),
        fun _ => ⟨hrw0_ne, hrcr_ne⟩, hmj,
        fun pok wvec' wstk' wlen' wu' wsort' mp hlen_p hlay_p hpres_o hpok_t hpok_f hmp => ?_⟩
      let st' : FullState :=
        { st with
          core := { st.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
          scratch := { st.scratch with wsort := wsort' } }
      have hnw_p : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st'.core) :=
        fullWitnessInv_nw_congr hlen_p.core_ok.cur_vars_le hst_nw
          rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      have hag_p : AgreesExcept propLitCoreMask s.core st'.core :=
        hag_st.update (fun k => { k with
          wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' })
      have hsc_p : st'.scratch = { s.scratch with
          search_ticks := st'.scratch.search_ticks, wsort := st'.scratch.wsort,
          phases := st'.scratch.phases } := by dsimp only [st']; rw [hsc_st]
      unfold fullWatchSize fullWatchOff at hpres_o hpok_t hpok_f
      s15_head_split
      · have hpok_eq : pok = true := hc
        have ⟨_, _, hsz_p, hpre_p, hw0_p, hw1_p⟩ := hpok_t hpok_eq
        have hsw_p := (s15_flush_step_preserves (k := st.core) (k' := st'.core) (lit := rlit_v)
          (w0 := rw0_v) (cref := rcr_v) (skip_lit := not_lit.toNat) rfl rfl hlay_p hrlit_lt_st
          hrw0_f_st hrcr_lt_st hrcr_ref_st hpres_o ⟨hsz_p, hpre_p, hw0_p, hw1_p rfl⟩).2
          hrlit_ne_st hnot_st _ _ _ _ hst_sw
        simp only [Nat.add_sub_cancel_left] at hsw_p
        exact ih (dlen - (idx + 1)) (j_v + 3#64, ()) mp (by omega)
          ⟨st', idx + 1, rfl, hj3_nat, by omega, hlen_p, hnw_p, hsw_p, hag_p,
            htr_st.congr rfl rfl rfl, hperm_st, hsc_p, hticks_eq, hvals_eq, hlvl_eq, hte_eq,
            hun_eq, huf_eq, hoom_st, hct_st, hmp⟩
      · have hpok_eq : pok = false := hc
        have hsw_p := (s15_flush_step_false_preserves (k := st.core) (k' := st'.core)
          (lit := rlit_v) (skip_lit := not_lit.toNat) rfl rfl hlay_p hpres_o
          (hpok_f hpok_eq).1).2 hnot_st _ _ _ _ hst_sw
        simp only [Nat.add_sub_cancel_left] at hsw_p
        have hwvec_p := hlen_p.core_ok.wvec_len
        have hwstk_p := hlen_p.core_ok.wstk_len_arr
        have hwlen_p := hlen_p.core_ok.wlen_le
        have hbd_p := hlay_p.bounds not_lit.toNat hnot_st
        rw [hsw_p.off_eq, hsw_p.sz_eq] at hbd_p
        have hwc64 : c.wcap + 1 < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_right hwc 1) (by decide)
        have hoff_p_nat : ((st'.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'(by
            rw [hidx0_nat, hwvec_p]; omega)).setWidth 64).toNat =
            fullWatchOffCore st'.core not_lit.toNat := by
          unfold fullWatchOffCore; rw [bv_c0_zext32_64]
          exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx hidx0_nat _)
        s15_head_steps
        let off_f := (st'.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'(by
            rw [hidx0_nat, hwvec_p]; omega)).setWidth 64
        let er_v := (s.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'(by
            rw [hidx1_nat, hwv0]; omega)).setWidth 64
        have hpf_nat : (off_f + pr).toNat = fullWatchOffCore st'.core not_lit.toNat + pr.toNat := by
          rw [bv64_add_toNat (by rw [hoff_p_nat]; omega), hoff_p_nat]
        have hqf_nat : (off_f + qr).toNat = fullWatchOffCore st'.core not_lit.toNat + qr.toNat := by
          rw [bv64_add_toNat (by rw [hoff_p_nat]; omega), hoff_p_nat]
        have hef_nat : (off_f + er_v).toNat =
            fullWatchOffCore st'.core not_lit.toNat + fullWatchSizeCore s.core not_lit.toNat := by
          rw [bv64_add_toNat (by rw [hoff_p_nat, hsz0_eq]; omega), hoff_p_nat, hsz0_eq]
        have hpi_oom0 : PropLitInv c F0 F_cur s st' not_lit.toNat off_f.toNat (off_f + qr).toNat
            (off_f + pr).toNat (off_f + er_v).toNat :=
          { len := hlen_p, nw := hnw_p
            sw := by rw [hoff_p_nat, hqf_nat, hpf_nat, hef_nat]; exact hsw_p
            ag := hag_p, tr := htr_st.congr rfl rfl rfl, perm := hperm_st
            sc_eq := hsc_p, not_f := hnot_f_st }
        refine s15_ovf_oom_compact_wp (st' := st') c.hwcap hdense0 hnot_st ?_ hmp hret_st
        simpa only [off_f, er_v, BitVec.ofNat_eq_ofNat] using hpi_oom0
    · -- Flush loop finished: `j_v >= di`; now run the standard watch loop from `[off + pr .. end)`
      have hst_len := hst_l.core_ok
      have hwv_st := hst_len.wvec_len
      have hlvl_st := hst_len.lvl_len
      have hwlen_st := hst_len.wlen_le
      have hbd_st := hst_sw.layout.bounds not_lit.toNat hnot_st
      rw [hst_sw.off_eq, hst_sw.sz_eq, Nat.add_sub_cancel_left] at hbd_st
      have hpi0 : PropLitInv c F0 F_cur s st not_lit.toNat
          (fullWatchOffCore st.core not_lit.toNat)
          (fullWatchOffCore st.core not_lit.toNat + qr.toNat)
          (fullWatchOffCore st.core not_lit.toNat + pr.toNat)
          (fullWatchOffCore st.core not_lit.toNat + fullWatchSizeCore s.core not_lit.toNat) :=
        { len := hst_l, nw := hst_nw, sw := hst_sw, ag := hag_st, tr := htr_st,
          perm := hperm_st, sc_eq := hsc_st, not_f := hnot_f_st }
      have hnl_lvl_idx : (BitVec.setWidth 64 (not_lit >>> (1 : Nat))).toNat <
          st.core.lvl.length := by
        rw [bv_c0_zext32_64, bv32_lshr_1, hlvl_st]; omega
      let nl_lvl0 := st.core.lvl[(BitVec.setWidth 64 (not_lit >>> (1 : Nat))).toNat]'hnl_lvl_idx
      have hnl_eq0 : st.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 := by
        have hidx : (BitVec.setWidth 64 (not_lit >>> (1 : Nat))).toNat = not_lit.toNat / 2 := by
          rw [bv_c0_zext32_64, bv32_lshr_1]
        rw [← hidx, List.getElem?_eq_getElem hnl_lvl_idx, Option.getD_some]
      clear hc
      s15_head_steps
      refine wp_loop_break_group
        (brkTs := [i64, i64, i64, i64, i64, i64, i64, i64, .bool])
        (lpTs := [i64, i64, i64, i64, i64, i64, i64, i64])
        (fun (off_v, tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, end_v, confl_v, ()) mb =>
          ∃ sem : FullState,
            PropLitInv c F0 F_cur s sem not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat ∧
            tend_v.toNat = sem.core.trail_end ∧ unass_v = sem.core.unassigned ∧
            unfl_v = sem.core.unflushed ∧
            (confl_v = false → sem.core.oom = 0#64 ∧ sem.core.confl_type = s.core.confl_type) ∧
            (confl_v = true → PropLitConfl F_cur ignore_ref sem.core) ∧
            (FullMem c (fastPropMem s sem) ⋆ R) mb)
        (fun rem (off_v, tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, end_v, ()) ml =>
          ∃ sem : FullState,
            rem = end_v.toNat - p_v.toNat ∧
            PropLitInv c F0 F_cur s sem not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat ∧
            tend_v.toNat = sem.core.trail_end ∧ unass_v = sem.core.unassigned ∧
            unfl_v = sem.core.unflushed ∧
            sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 ∧
            sem.core.oom = 0#64 ∧ sem.core.confl_type = s.core.confl_type ∧
            (FullMem c (fastPropMem s sem) ⋆ R) ml) ?_ ?_ ?_
      · rintro _ ⟨off_v, tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, end_v, confl_v, ⟨⟩⟩ mb
          ⟨sem, hpi, htend_eq, hunass_eq, hunfl_eq, hcf_f, hcf_t, hmb⟩
        exact s15_ovf_finish_wp c.hwcap hcv0 hdense0 hnot_lt hpi htend_eq hunass_eq
          hunfl_eq hcf_f hcf_t hmb fun ok st2 ml hl hw hag htr hperm hsc hcf hoom hml =>
          hret_st ok st2 ml hl hw hag htr hperm hsc hcf hoom hml
      · rintro B L2 rem ⟨off_v, tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, end_v, ⟨⟩⟩ ml hB ih2
          ⟨sem, rfl, hpi, htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_sem, hct_sem, hml⟩
        clear hsw0 hdel0 hm hnw0 hnot_f0 hst_sw hst_nw hag_st htr_st hperm_st hsc_st hpi0 hmj ih
          hbd_st hst_l hst_len hticks_eq hvals_eq hlvl_eq hte_eq hun_eq huf_eq hoom_st hct_st
          hdel_len_st hdel_eq_st hhref_st hnot_f_st hnl_eq0 hqr_le_pr hpr_le_sz0 hsz0_eq
          hdi_eq hdlen_le hdel_len0 hidx0_nat hidx1_nat hj_eq hidx_le
        have hcv_eq : sem.core.cur_vars = s.core.cur_vars := hpi.cur_vars_eq
        have hnot_sem : not_lit.toNat < 2 * sem.core.cur_vars := hcv_eq.symm ▸ hnot_lt
        have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_sem
        have hend_wcap : end_v.toNat ≤ c.wcap := Nat.le_trans hend_le hwlen_le
        have hwc64 : c.wcap + 1 < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_right hwc 1) (by decide)
        have hwc64_2 : c.wcap + 2 < 2 ^ 64 :=
          Nat.lt_trans (Nat.add_lt_add_right hwc 2) (by decide)
        have hq_ge := hpi.sw.q_ge; have hq_le := hpi.sw.q_le_p; have hp_le := hpi.sw.p_le_end
        have hpr_eq_sem : sem.core.propagated = s.core.propagated :=
          hpi.ag.get FullCoreState.propagated
        have hlen_mem := fastPropMem_lengthsOk hlen0 hpi.len hcv_eq hpr_eq_sem rfl
        have hm_wstk := hlen_mem.core_ok.wstk_len_arr; have hm_vals := hlen_mem.core_ok.vals_len
        have hm_aren := hlen_mem.core_ok.arena_len_arr
        have hm_alen := hlen_mem.core_ok.arena_len_le
        have hm_wvec := hlen_mem.core_ok.wvec_len; have hm_lvl := hlen_mem.core_ok.lvl_len
        have hm_fl := hlen_mem.core_ok.flags_len; have hm_trl := hlen_mem.core_ok.trl_len
        have hm_tp := hlen_mem.core_ok.trail_pos_len; have hm_rsn := hlen_mem.core_ok.rsns_len
        have hm_ph := hlen_mem.scratch_ok.phases_len
        have hwstk_len := hpi.len.core_ok.wstk_len_arr; have hvals_len := hpi.len.core_ok.vals_len
        have hwstk_mem : (fastPropMem s sem).core.wstk.length = c.wcap := by
          rw [fastPropMem_wstk]; exact hwstk_len
        have haren_len := hpi.len.core_ok.arena_len_arr
        have halen_le := hpi.len.core_ok.arena_len_le
        have hwvec_len := hpi.len.core_ok.wvec_len; have hlvl_len := hpi.len.core_ok.lvl_len
        have hfl_len := hpi.len.core_ok.flags_len; have htrl_len := hpi.len.core_ok.trl_len
        have htp_len := hpi.len.core_ok.trail_pos_len; have hrsn_len := hpi.len.core_ok.rsns_len
        have hph_len := hpi.len.scratch_ok.phases_len
        have hcv_lt64 : s.core.cur_vars < 2 ^ 64 :=
          Nat.lt_of_le_of_lt hcv0 (Nat.lt_trans hmaxv (by decide))
        have h2cv_lt64 : 2 * s.core.cur_vars < 2 ^ 64 :=
          Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 hcv0)
            (Nat.lt_trans (Nat.mul_lt_mul_of_pos_left hmaxv (by decide)) (by decide))
        have hp1_pre : (p_v + (1 : BitVec 64)).toNat = p_v.toNat + 1 :=
          bv64_add1_toNat (Nat.lt_of_le_of_lt
            (Nat.add_le_add_right (Nat.le_trans hp_le hend_wcap) 1) hwc64)
        s15_head_split
        · have hp_lt : p_v.toNat < end_v.toNat := by assumption
          have hp_lt_w : p_v.toNat < sem.core.wstk.length :=
            hwstk_len ▸ Nat.lt_of_lt_of_le hp_lt hend_wcap
          have hp_rem_pos : 0 < end_v.toNat - p_v.toNat := Nat.sub_pos_of_lt hp_lt
          have hp1_nat : (p_v + 1#64).toNat = p_v.toNat + 1 := hp1_pre
          have hq1_nat : (q_v + 1#64).toNat = q_v.toNat + 1 :=
            bv64_add1_toNat (Nat.lt_of_le_of_lt
              (Nat.add_le_add_right (Nat.le_trans hq_le (Nat.le_trans hp_le hend_wcap)) 1) hwc64)
          have hq_lt_ws : q_v.toNat < sem.core.wstk.length :=
            hwstk_len ▸ Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hq_le hp_lt) hend_wcap
          let w0_v := sem.core.wstk[p_v.toNat]'hp_lt_w
          have hw0_get : sem.core.wstk[p_v.toNat]? = some w0_v := List.getElem?_eq_getElem hp_lt_w
          s15_head_steps
          refine wp_join_group (ts := [])
            (fun () m1 => m1 = ml ∧
              ∀ hlt : (w0_v &&& 0x7FFFFFFF#32).toNat < 2 * sem.core.cur_vars,
                (0#32).slt ((sem.core.vals[(w0_v &&& 0x7FFFFFFF#32).toNat]'(fastProp_lt_vals
                  hpi.len.core_ok hlt)).signExtend 32) = false)
            ?_ ?_
          · rintro _ ⟨⟩ ml1 ⟨hml1, hblk_nsgt⟩
            subst ml1
            s15_head_split
            · have hflag : (w0_v &&& 0x80000000#32) ≠ 0#32 := by
                simpa only [ne_eq, ← BitVec.ofNat_eq_ofNat, fc_getElem_wstk, fastPropMem_wstk]
                  using hc
              obtain ⟨hother_lt, hent, hrem1⟩ :=
                watchSlice_inv_bin hpi.sw.rem_slice hp_rem_pos hw0_get hflag
              have hsw1 := (hpi.sw.advance_rem (p' := p_v.toNat + 1) (Nat.le_succ _) hp_lt
                (by simpa [Nat.sub_sub] using hrem1)).write_bin
                (c := c) hpi.len.core_ok.cur_vars_le hnot_sem hq_le hq_lt_ws hflag hother_lt hent
              let other := w0_v &&& 0x7FFFFFFF#32
              let wstk1 := sem.core.wstk.set q_v.toNat w0_v
              let sem1 : FullState := { sem with core := { sem.core with wstk := wstk1 } }
              have hlen1 : sem1.LengthsOk c :=
                ⟨{ hpi.len.core_ok with wstk_len_arr := by simp [sem1, wstk1, hwstk_len] },
                 hpi.len.scratch_ok⟩
              have hnw1 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem1.core) :=
                fullWitnessInv_nw_congr hlen1.core_ok.cur_vars_le hpi.nw
                  rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
              have hother_vals1 : (w0_v &&& 2147483647#32).toNat < sem1.core.vals.length :=
                fastProp_lt_vals hlen1.core_ok hother_lt
              have hother_vals0 : (w0_v &&& 2147483647#32).toNat < sem.core.vals.length :=
                fastProp_lt_vals hpi.len.core_ok hother_lt
              have hov_nsgt : (0#32).slt
                  ((sem1.core.vals[other.toNat]'hother_vals1).signExtend 32) = false :=
                hblk_nsgt hother_lt
              have hq_lt_mem : q_v.toNat < (fastPropMem s sem).core.wstk.length := by
                rw [fastPropMem_wstk]; exact hq_lt_ws
              have hother_vals_mem : (BitVec.setWidth 64
                  ((fastPropMem s sem).core.wstk[p_v.toNat]'(fastPropMem_wstk s sem ▸ hp_lt_w) &&&
                    2147483647)).toNat <
                  ({ fastPropMem s sem with core := { (fastPropMem s sem).core with
                    wstk := (fastPropMem s sem).core.wstk.set q_v.toNat
                      ((fastPropMem s sem).core.wstk[p_v.toNat]'(fastPropMem_wstk s sem ▸
                        hp_lt_w)) } }).core.vals.length := by
                dsimp only [w0_v] at hother_vals0
                simp only [bv_c0_zext32_64, fc_getElem_wstk, fastPropMem_vals]
                exact hother_vals0
              s15_head_steps
              · have hge : 2 * s.core.cur_vars ≤ other.toNat := by
                  dsimp only [other, w0_v]
                  simpa only [← BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, hcv_st,
                    Nat.mod_eq_of_lt hcv_lt64, Nat.mod_eq_of_lt h2cv_lt64,
                    fc_getElem_wstk, fastPropMem_wstk] using hc
                exact absurd hother_lt (Nat.not_lt.mpr (hcv_eq.symm ▸ hge))
              · have hov_f := propLit_vals_neg hpi.nw hother_lt
                  (fastProp_lt_vals hpi.len.core_ok hother_lt)
                  (by simpa only [BitVec.ofNat_eq_ofNat, fastPropMem_wstk,
                    fastPropMem_vals] using hc)
                have ⟨hpi_c, hcf_c⟩ := propLit_bin_confl (ignore_ref := ignore_ref) hpi hsw1
                  hnot_sem hother_lt hent hov_f hp1_nat hq1_nat
                let sem_c : FullState :=
                  { sem with core :=
                      { sem.core with
                        wstk := wstk1, confl_type := 1#64,
                        confl_lit0 := not_lit.setWidth 64, confl_lit1 := other.setWidth 64,
                        confl_ref := 0xFFFFFFFF#64 } }
                exact hB (off_v, tend_v, unass_v, unfl_v, ticks_v, p_v + 1#64, q_v + 1#64, end_v,
                  true, ()) m ⟨sem_c, hpi_c, htend_eq, hunass_eq, hunfl_eq, by simp, fun _ => hcf_c,
                  by simpa only [sem_c, wstk1, other, BitVec.ofNat_eq_ofNat,
                    fastPropMem_wstk, fastPropMem_with_bin_confl_wstk] using hm⟩
              · have hov_un : sem1.core.vals[other.toNat]?.getD 0#8 = 0#8 :=
                  propLit_vals_un hnw1 hother_lt hother_vals1 hov_nsgt
                    (by simpa only [other, BitVec.ofNat_eq_ofNat, fastPropMem_wstk,
                      fastPropMem_vals] using hc)
                have hte_lt : sem.core.trail_end < sem.core.cur_vars :=
                  hnw1.trail_end_lt_of_unassigned hother_lt hov_un
                have hlen1_mem := fastPropMem_lengthsOk hlen0 hlen1 hcv_eq
                  (hpi.ag.get FullCoreState.propagated) rfl
                rw [show ((fastPropMem s sem).core.wstk[p_v.toNat]'(by
                      rw [fastPropMem_wstk]; exact hp_lt_w) &&& (2147483647 : BitVec 32)) =
                    other from by
                  rw [show (2147483647 : BitVec 32) = 2147483647#32 from rfl, fc_getElem_wstk]]
                dsimp only
                refine fastProp_assign_wp (k_next := fun tn un uf => .jump L2 (.var off_v, (.var tn,
                  (.var un, (.var uf, (.var (ticks_v + 1#64), (.var (p_v + 1#64),
                  (.var (q_v + 1#64), (.var end_v, ())))))))))
                  hmaxv hcv0 hlen1_mem hpi.cur_vars_eq hother_lt hte_lt
                  htend_eq (by simpa only [BitVec.ofNat_eq_ofNat, fastPropMem_wstk,
                    fastPropMem_with_wstk] using hm) ?_
                intro flags' ph' unass_n unfl_n m' hfl' hph' hm'
                dsimp only at hm'
                simp only [BitVec.ofNat_eq_ofNat] at hm'
                rw [fastPropMem_assign_eq (te' := sem.core.trail_end + 1)
                  (un' := unass_n) (uf' := unfl_n)] at hm'
                have hassign := full_bin_assign_nw_step hlen1.core_ok hnw1 hnot_sem hother_lt hov_un
                  hpi.not_f hent (flags' := flags') (unas' := unass_n) (unfl' := unfl_n)
                rw [show sem1.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 from hnl_eq]
                  at hassign
                have ⟨hlen2, hnw2, hsw2, hag2, htr2, hperm2, hsc2, hnot_f2, hnl2⟩ :=
                  fastPropMem_eq_of_eq hpi hsw1 (by simp [hwstk_len]) hfl' hph' hnot_sem
                    hother_lt hov_un hnl_eq hassign
                have hmv64 : c.max_vars + 1 < 2 ^ 64 :=
                  Nat.lt_trans (Nat.add_lt_add_right hmaxv 1) (by decide)
                have htend_max : tend_v.toNat < c.max_vars := by
                  rw [htend_eq]; exact Nat.lt_of_lt_of_le hte_lt hpi.len.core_ok.cur_vars_le
                have ht1_lt : tend_v.toNat + 1 < 2 ^ 64 :=
                  Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.le_of_lt htend_max) 1) hmv64
                have htend1 : (tend_v + 1#64).toNat = sem.core.trail_end + 1 := by
                  rw [BitVec.toNat_add, htend_eq]
                  change (sem.core.trail_end + 1) % 2 ^ 64 = sem.core.trail_end + 1
                  exact Nat.mod_eq_of_lt (htend_eq ▸ ht1_lt)
                exact ih2 (end_v.toNat - (p_v.toNat + 1)) (off_v, tend_v + 1#64, unass_n, unfl_n,
                  ticks_v + 1#64, p_v + 1#64, q_v + 1#64, end_v, ()) m'
                  (Nat.sub_lt hp_rem_pos Nat.zero_lt_one)
                  ⟨_, by rw [hp1_nat], ⟨hlen2, hnw2, (by rw [hp1_nat, hq1_nat]; exact hsw2),
                    hag2, htr2, hperm2, hsc2, hnot_f2⟩, htend1, rfl, rfl, hnl2, hoom_sem,
                    hct_sem, hm'⟩
            · have hflag : (w0_v &&& 0x80000000#32) = 0#32 := by
                simpa only [← BitVec.ofNat_eq_ofNat, fc_getElem_wstk, fastPropMem_wstk] using hc
              have ⟨h2le, cref0, hcr_get, hcr_lt, hcr_ref, hrem2⟩ :=
                watchSlice_inv_large hpi.sw.rem_slice hp_rem_pos hw0_get hflag
              s15_head_split
              · have hge : end_v.toNat ≤ (p_v + (1 : BitVec 64)).toNat := hc
                rw [hp1_pre] at hge
                have h2_le_end : p_v.toNat + 2 ≤ end_v.toNat :=
                  Nat.add_sub_cancel' hp_le ▸ Nat.add_le_add_left h2le p_v.toNat
                exact absurd hge (Nat.not_le.mpr (Nat.lt_of_succ_le h2_le_end))
              · s15_head_split
                · have halen_eq : sem.core.arena_len = s.core.arena_len :=
                    hpi.ag.get FullCoreState.arena_len
                  have h2_le_end : p_v.toNat + 2 ≤ end_v.toNat :=
                    Nat.add_sub_cancel' hp_le ▸ Nat.add_le_add_left h2le p_v.toNat
                  have hcr_idx0 : (p_v + 1#64).toNat < sem.core.wstk.length := by
                    rw [hp1_nat, hwstk_len]; exact Nat.lt_of_lt_of_le (by omega) hend_wcap
                  have hc_alen : sem.core.arena_len % 2 ^ 64 <
                      ((sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx0).toNat + 3) % 2 ^ 64 := by
                    have hp1_mod : (p_v.toNat + 1) % 2 ^ 64 = (p_v + 1#64).toNat := by
                      rw [hp1_nat]
                      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega)
                        (Nat.lt_trans hwc (by decide)))
                    have hc' := hc
                    simp only [fastPropMem_wstk, BitVec.reduceToNat, halen_st] at hc'
                    rw [← halen_eq] at hc'
                    simp only [hp1_mod] at hc'
                    exact hc'
                  have hcr_eq0 : sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx0 = cref0 := by
                    have h1 : sem.core.wstk[p_v.toNat + 1]? =
                        some (sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx0) := by
                      rw [← hp1_nat]; exact List.getElem?_eq_getElem hcr_idx0
                    exact Option.some.inj (h1.symm.trans hcr_get)
                  have hwf0 := hpi.nw.arena.refs_wf cref0.toNat hcr_ref
                  have hal_lt64 : sem.core.arena_len < 2 ^ 64 :=
                    Nat.lt_of_le_of_lt hpi.len.core_ok.arena_len_le (Nat.lt_trans har (by decide))
                  have hcr3_lt64 : cref0.toNat + 3 < 2 ^ 64 :=
                    Nat.lt_of_le_of_lt hwf0.1 hal_lt64
                  rw [hcr_eq0, Nat.mod_eq_of_lt hal_lt64, Nat.mod_eq_of_lt hcr3_lt64] at hc_alen
                  exact absurd hc_alen (Nat.not_lt.mpr hwf0.1)
                have h2_le_end : p_v.toNat + 2 ≤ end_v.toNat :=
                  Nat.add_sub_cancel' hp_le ▸ Nat.add_le_add_left h2le p_v.toNat
                have hrem_dec : end_v.toNat - (p_v.toNat + 2) < end_v.toNat - p_v.toNat :=
                  fc_rem2_lt h2_le_end
                have hp2_wcap : p_v.toNat + 2 ≤ c.wcap := Nat.le_trans h2_le_end hend_wcap
                have hp2_64 : p_v.toNat + 2 < 2 ^ 64 :=
                  Nat.lt_of_le_of_lt hp2_wcap (Nat.lt_trans hwc (by decide))
                have hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2 := by
                  rw [bv64_add_toNat (a := p_v + 1#64) (b := 1#64) (by rw [hp1_nat]; exact hp2_64),
                    hp1_nat]; rfl
                have hq2_nat : (q_v + 2#64).toNat = q_v.toNat + 2 :=
                  bv64_add2_toNat (a := q_v) (Nat.lt_of_le_of_lt
                    (Nat.add_le_add_right (Nat.le_trans hq_le (Nat.le_trans hp_le hend_wcap)) 2)
                    hwc64_2)
                have hq_lt_ws2 : q_v.toNat < sem.core.wstk.length :=
                  hwstk_len ▸ Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hq_le
                    (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 2)) h2_le_end))
                    hend_wcap
                have hq1_lt_ws2 : q_v.toNat + 1 < sem.core.wstk.length :=
                  hwstk_len ▸ Nat.lt_of_lt_of_le
                    (Nat.lt_of_le_of_lt (Nat.add_le_add_right hq_le 1)
                      (Nat.lt_of_lt_of_le (Nat.lt_succ_self (p_v.toNat + 1)) h2_le_end)) hend_wcap
                have hcr_idx_lt : (p_v + 1#64).toNat < sem.core.wstk.length := by
                  rw [hp1_nat, hwstk_len]
                  exact Nat.lt_of_lt_of_le (Nat.lt_of_succ_le h2_le_end) hend_wcap
                have hcr_eq : sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx_lt = cref0 := by
                  have h1 : sem.core.wstk[p_v.toNat + 1]? =
                      some (sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx_lt) := by
                    rw [← hp1_nat]; exact List.getElem?_eq_getElem hcr_idx_lt
                  exact Option.some.inj (h1.symm.trans hcr_get)
                simp only [← BitVec.ofNat_eq_ofNat, fastPropMem_wstk]
                generalize hcr_gen :
                  sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx_lt = cref at hcr_eq ⊢
                rw [← hcr_eq] at hcr_lt hcr_ref
                have hsw_drop : SplitWatchesInv F_cur sem.core not_lit.toNat off_v.toNat q_v.toNat
                    (p_v.toNat + 2) end_v.toNat :=
                  hpi.sw.advance_rem (p' := p_v.toNat + 2) (by omega) h2_le_end
                    (by simpa [Nat.sub_sub] using hrem2)
                have hcr_wf := hpi.nw.arena.refs_wf cref.toNat hcr_ref
                have hcr3_le : cref.toNat + 3 ≤ sem.core.arena_len := hcr_wf.1
                have hcsz3 : 3 ≤ fullArenaClauseSizeCore sem.core cref.toNat := hcr_wf.2.1
                have hcr_next : cref.toNat + 3 + fullArenaClauseSizeCore sem.core cref.toNat ≤
                    fullArenaNextOff sem.core.arena sem.core.arena_len cref.toNat := hcr_wf.2.2.1
                have hnext_le : fullArenaNextOff sem.core.arena sem.core.arena_len cref.toNat ≤
                    sem.core.arena_len := hcr_wf.2.2.2.1
                have hcr_fit : cref.toNat + 3 + fullArenaClauseSizeCore sem.core cref.toNat ≤
                    sem.core.arena_len := Nat.le_trans hcr_next hnext_le
                have ⟨hcr0_lt_ar, hcr2_lt_ar, hcr3_lt_ar, hcr4_lt_ar, hcr3_lt64, hal_lt64⟩ :=
                  fc_cref_bounds hpi.len.core_ok (Nat.lt_trans har (by decide)) hcsz3 hcr_fit
                have hcr64 : (cref.setWidth 64).toNat = cref.toNat := bv_c0_zext32_64 cref
                have hcr_u64 : (cref.setWidth 64).toNat + 4 < 2 ^ 64 := by
                  rw [hcr64]; exact Nat.lt_trans (Nat.add_lt_add_right cref.isLt 4) (by decide)
                have h1_idx : (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1 := by
                  rw [bv64_add_toNat (a := cref.setWidth 64) (b := 1#64)
                    (Nat.lt_trans (Nat.add_lt_add_left (by decide) _) hcr_u64), hcr64]; rfl
                have h2_idx : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by
                  rw [bv64_add_toNat (a := cref.setWidth 64) (b := 2#64)
                    (Nat.lt_trans (Nat.add_lt_add_left (by decide) _) hcr_u64), hcr64]; rfl
                have h3_idx : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3 := by
                  rw [bv64_add_toNat (a := cref.setWidth 64) (b := 3#64)
                    (Nat.lt_trans (Nat.add_lt_add_left (by decide) _) hcr_u64), hcr64]; rfl
                have h4_idx : (cref.setWidth 64 + 4#64).toNat = cref.toNat + 4 := by
                  rw [bv64_add_toNat (a := cref.setWidth 64) (b := 4#64) hcr_u64, hcr64]; rfl
                s15_head_steps
                · exact ih2 _ (off_v, tend_v, unass_v, unfl_v, ticks_v + 1#64, p_v + 1#64 + 1#64,
                    q_v, end_v, ()) ml hrem_dec
                    ⟨sem, by rw [hp2_nat], propLit_inv_drop (ticks' := sem.scratch.search_ticks) hpi
                      hsw_drop hp2_nat, htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_sem, hct_sem,
                      hml⟩
                · exact ih2 _ (off_v, tend_v, unass_v, unfl_v, ticks_v + 1#64, p_v + 1#64 + 1#64,
                    q_v, end_v, ()) ml hrem_dec
                    ⟨sem, by rw [hp2_nat], propLit_inv_drop (ticks' := sem.scratch.search_ticks) hpi
                      hsw_drop hp2_nat, htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_sem, hct_sem,
                      hml⟩
                · exact ih2 _ (off_v, tend_v, unass_v, unfl_v, ticks_v + 1#64, p_v + 1#64 + 1#64,
                    q_v, end_v, ()) ml hrem_dec
                    ⟨sem, by rw [hp2_nat], propLit_inv_drop (ticks' := sem.scratch.search_ticks) hpi
                      hsw_drop hp2_nat, htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_sem, hct_sem,
                      hml⟩
                · have hng_t : fullArenaClauseGarbCore sem.core cref.toNat = false := by
                    unfold fullArenaClauseGarbCore fullArenaHdrCore
                    have hget : sem.core.arena[cref.toNat]? =
                        some (sem.core.arena[cref.toNat]'hcr0_lt_ar) :=
                      List.getElem?_eq_getElem hcr0_lt_ar
                    rw [hget, Option.getD_some]
                    have hh : ((fastPropMem s sem).core.arena[(cref.setWidth 64).toNat]'
                        (by rw [fastPropMem_arena, hcr64]; exact hcr0_lt_ar) &&&
                          0x00080000#32) = 0#32 := by assumption
                    have h0 : (sem.core.arena[cref.toNat]'hcr0_lt_ar &&& 0x00080000#32) = 0#32 := by
                      have hh' := hh
                      simp only [← BitVec.ofNat_eq_ofNat, fastPropMem_arena, hcr64] at hh'
                      exact hh'
                    rw [h0]; rfl
                  try clear hc; try clear hc; try clear hc; try clear hc
                  refine wp_join_group
                    (fun (other, ()) mj2 => ∃ sem1 : FullState,
                      PropLitInv c F0 F_cur s sem1 not_lit.toNat off_v.toNat q_v.toNat
                        (p_v.toNat + 2) end_v.toNat ∧
                      sem1.core.oom = 0#64 ∧ sem1.core.confl_type = s.core.confl_type ∧
                      sem1.core.arena_len = sem.core.arena_len ∧
                      sem1.core.trail_end = sem.core.trail_end ∧
                      sem1.core.unassigned = sem.core.unassigned ∧
                      sem1.core.unflushed = sem.core.unflushed ∧
                      sem1.core.cur_level = sem.core.cur_level ∧
                      sem1.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 ∧
                      cref.toNat ∈ fullArenaClauseRefsCore sem1.core ∧
                      fullArenaClauseGarbCore sem1.core cref.toNat = false ∧
                      fullArenaClauseSizeCore sem1.core cref.toNat =
                        fullArenaClauseSizeCore sem.core cref.toNat ∧
                      sem1.core.arena[cref.toNat + 3]? = some other ∧
                      sem1.core.arena[cref.toNat + 4]? = some not_lit ∧
                      (FullMem c (fastPropMem s sem1) ⋆ R) mj2) ?_ ?_
                  · rintro _ ⟨other, ⟨⟩⟩ mj2 ⟨sem1, hpi1, hoom1, hct1, halen1, hte1_eq, hun1_eq,
                      huf1_eq, hcl1_eq, hnl1, hcr_ref1, hng1, hcsz1, har3, har4, hmj2⟩
                    have htend1_eq : tend_v.toNat = sem1.core.trail_end :=
                      htend_eq.trans hte1_eq.symm
                    have hunass1_eq : unass_v = sem1.core.unassigned := hunass_eq.trans hun1_eq.symm
                    have hunfl1_eq : unfl_v = sem1.core.unflushed := hunfl_eq.trans huf1_eq.symm
                    have hlen1_mem := fastPropMem_lengthsOk hlen0 hpi1.len hpi1.cur_vars_eq
                      (hpi1.ag.get FullCoreState.propagated) rfl
                    have hm1_aren := hlen1_mem.core_ok.arena_len_arr
                    have hm1_alen := hlen1_mem.core_ok.arena_len_le
                    have hm1_vals := hlen1_mem.core_ok.vals_len
                    have haren1 := hpi1.len.core_ok.arena_len_arr
                    have halen1_le := hpi1.len.core_ok.arena_len_le
                    have hvals1 := hpi1.len.core_ok.vals_len
                    have hwstk1 := hpi1.len.core_ok.wstk_len_arr
                    have hwvec1 := hpi1.len.core_ok.wvec_len
                    have hlvl1 := hpi1.len.core_ok.lvl_len
                    have hfl1 := hpi1.len.core_ok.flags_len
                    have htrl1 := hpi1.len.core_ok.trl_len
                    have htp1 := hpi1.len.core_ok.trail_pos_len
                    have hrsn1 := hpi1.len.core_ok.rsns_len
                    have hph1 := hpi1.len.scratch_ok.phases_len
                    have hcv1_eq := hpi1.cur_vars_eq
                    have hnot_st1 : not_lit.toNat < 2 * sem1.core.cur_vars :=
                      hcv1_eq.symm ▸ hnot_lt
                    have hcsz3_1 : 3 ≤ fullArenaClauseSizeCore sem1.core cref.toNat :=
                      hcsz1.symm ▸ hcsz3
                    have hfit1 : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤
                        sem1.core.arena_len := by rw [hcsz1, halen1]; exact hcr_fit
                    have hcr3_le1 : cref.toNat + 3 ≤ sem1.core.arena_len :=
                      Nat.le_trans (Nat.le_add_right _ _) hfit1
                    have hcr_lt_alen1 : cref.toNat < sem1.core.arena_len :=
                      Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 3)) hcr3_le1
                    have ⟨_, hcr2_lt_ar1, hcr3_lt_ar1, hcr4_lt_ar1, _, _⟩ :=
                      fc_cref_bounds hpi1.len.core_ok (Nat.lt_trans har (by decide)) hcsz3_1 hfit1
                    have hother_mem : other.toNat ∈ fullArenaClauseLitsCore sem1.core cref.toNat :=
                      by
                      refine (mem_fullArenaClauseLitsCore_iff (haren1 ▸ Nat.le_trans hfit1
                        halen1_le)).mpr ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 3) hcsz3_1, ?_⟩
                      exact congrArg BitVec.toNat (Option.some.inj
                        ((List.getElem?_eq_getElem hcr3_lt_ar1).symm.trans har3))
                    have hother_lt : other.toNat < 2 * sem1.core.cur_vars :=
                      hpi1.nw.arena.lits_lt cref.toNat hcr_ref1 hng1 other.toNat hother_mem
                    have hother_lt1_vals : other.toNat < sem1.core.vals.length :=
                      fastProp_lt_vals hpi1.len.core_ok hother_lt
                    have hq_lt_ws1 : q_v.toNat < sem1.core.wstk.length := by
                      rw [hwstk1, ← hwstk_len]; exact hq_lt_ws2
                    have hq1_lt_ws1 : q_v.toNat + 1 < sem1.core.wstk.length := by
                      rw [hwstk1, ← hwstk_len]; exact hq1_lt_ws2
                    s15_head_steps
                    · have hge : 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 ≤ other.toNat := by
                        have hcu_bv : BitVec.toNat (OfNat.ofNat s.core.cur_vars : BitVec 64) =
                            s.core.cur_vars % 2 ^ 64 := @BitVec.toNat_ofNat s.core.cur_vars 64
                        have hc' := hc
                        rw [hcv_st, hcu_bv] at hc'
                        exact hc'
                      rw [Nat.mod_eq_of_lt hcv_lt64, Nat.mod_eq_of_lt h2cv_lt64] at hge
                      exact absurd (hcv1_eq ▸ hother_lt) (Nat.not_lt.mpr hge)
                    · exact ih2 _ (off_v, tend_v, unass_v, unfl_v, ticks_v + 1#64,
                          p_v + 1#64 + 1#64, q_v + 2#64, end_v, ()) m hrem_dec
                        ⟨_, by rw [hp2_nat], propLit_inv_keep_large hpi1 hpi1.sw hnot_st1 hq1_nat
                          hq2_nat hp2_nat (Nat.add_le_add_right hq_le 2)
                          hpi1.sw.p_le_end (bv32_mask7f_flag0 other) hcr_lt hcr_ref1,
                          htend1_eq, hunass1_eq, hunfl1_eq, hnl1, hoom1, hct1, by
                            simpa only [← BitVec.ofNat_eq_ofNat, fastPropMem_wstk,
                              fastPropMem_with_wstk] using hm⟩
                    · have hov_np :
                          (0#32).slt ((sem1.core.vals[other.toNat]'hother_lt1_vals).signExtend 32) =
                            false := by simpa only [fastPropMem_vals] using hc
                      try clear hc; try clear hc
                      refine wp_join_group (fun (srch_v, ()) ms =>
                          2 ≤ srch_v.toNat ∧
                          srch_v.toNat < fullArenaClauseSizeCore sem1.core cref.toNat ∧
                          ms = mj2) ?_ ?_
                      · rintro _ ⟨srch_v, ⟨⟩⟩ ms ⟨hsrch2, hsrch_lt, hms⟩
                        subst ms
                        have hm0_aren := hlen_mem.core_ok.arena_len_arr
                        let csz32 := (fastPropMem s sem).core.arena[
                          (cref.setWidth 64 + 2#64).toNat]'(by
                            rw [hm0_aren, ← haren_len, h2_idx]; exact hcr2_lt_ar)
                        have hcsz32_nat :
                            csz32.toNat = fullArenaClauseSizeCore sem1.core cref.toNat := by
                          rw [hcsz1]
                          have h1 := congrArg BitVec.toNat
                            ((fc_getElem_arena s sem (hi := (by
                                rw [hm0_aren, ← haren_len, h2_idx]; exact hcr2_lt_ar))).trans
                              (fc_getElem_eq_of_idx h2_idx (h2_idx ▸ hcr2_lt_ar) hcr2_lt_ar))
                          have h2 : (sem.core.arena[cref.toNat + 2]'hcr2_lt_ar).toNat =
                              fullArenaClauseSizeCore sem.core cref.toNat := by
                            unfold fullArenaClauseSizeCore
                            rw [List.getElem?_eq_getElem hcr2_lt_ar, Option.getD_some]
                          exact h1.trans h2
                        s15_head_steps
                        refine s15_repl_search_wp
                          (nlits := BitVec.ofNat 64 st.core.cur_vars <<< (1 : Nat))
                          c.hmaxv c.harena hcv0 ?_ hpi1 hlen1_mem hfit1
                          h3_idx hcsz32_nat hsrch2 hsrch_lt hmj2 ?_
                        · rw [hcv_st, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt hcv_lt64, Nat.shiftLeft_eq, Nat.pow_one,
                            Nat.mul_comm, Nat.mod_eq_of_lt h2cv_lt64]
                        · rintro ri_f repl_f _rf hres_f
                          rcases hres_f with
                            ⟨rfl, hfind_bad⟩ | ⟨hri_ne, hr2, hr_lt, hrepl_def, hcand⟩
                          · have hunit := propLit_hunit hpi1.nw hcr_ref1 hng1
                              (haren1 ▸ Nat.le_trans hfit1 halen1_le) har3 har4
                              hpi1.not_f fun k hk1 hk2 => by
                                change k < fullArenaClauseSizeCore sem1.core cref.toNat at hk2
                                have hb := hfind_bad k hk1 (by rwa [← hcr64] at hk2)
                                unfold fullFindReplBad at hb ⊢; rwa [hcr64]
                            have hnot_mem : not_lit.toNat ∈
                                fullArenaClauseLitsCore sem1.core cref.toNat := by
                              refine (mem_fullArenaClauseLitsCore_iff
                                (haren1 ▸ Nat.le_trans hfit1 halen1_le)).mpr
                                  ⟨1, Nat.lt_of_lt_of_le (by decide : 1 < 3) hcsz3_1, ?_⟩
                              exact congrArg BitVec.toNat (Option.some.inj
                                ((List.getElem?_eq_getElem hcr4_lt_ar1).symm.trans har4))
                            have hcur_eq1 :
                                (BitVec.ofNat 64 s.core.cur_level).setWidth 32 =
                                  BitVec.ofNat 32 s.core.cur_level := by
                              apply BitVec.eq_of_toNat_eq
                              have hcl64 : s.core.cur_level < 2 ^ 64 :=
                                Nat.lt_trans hclv_lt32 (by decide)
                              rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                                Nat.mod_eq_of_lt hcl64, Nat.mod_eq_of_lt hclv_lt32,
                                BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt32]
                            have hsw2 := hpi1.sw.write_large hnot_st1 hq_le
                              hq_lt_ws1 hq1_lt_ws1 (bv32_mask7f_flag0 other) hcr_lt hcr_ref1
                            let wstk2 := (sem1.core.wstk.set q_v.toNat
                              (other &&& 0x7FFFFFFF#32)).set (q_v.toNat + 1) cref
                            let sem2 : FullState :=
                              { sem1 with core := { sem1.core with wstk := wstk2 } }
                            have hlen2 : sem2.LengthsOk c :=
                              ⟨{ hpi1.len.core_ok with
                                   wstk_len_arr := by simp [sem2, wstk2, hwstk1] },
                               hpi1.len.scratch_ok⟩
                            have hlen2_mem := fastPropMem_lengthsOk hlen0 hlen2 hpi1.cur_vars_eq
                              (hpi1.ag.get FullCoreState.propagated) rfl
                            have hnw2 :
                                FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem2.core) :=
                              fullWitnessInv_nw_congr hlen2.core_ok.cur_vars_le hpi1.nw
                                rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                            have hpi2 : PropLitInv c F0 F_cur s sem2 not_lit.toNat off_v.toNat
                                (q_v + 2#64).toNat (p_v.toNat + 2) end_v.toNat :=
                              { len := hlen2, nw := hnw2, sw := by rw [hq2_nat]; exact hsw2
                                ag := hpi1.ag.update (fun k => { k with wstk := wstk2 })
                                tr := hpi1.tr.congr rfl rfl rfl, perm := hpi1.perm,
                                sc_eq := hpi1.sc_eq, not_f := hpi1.not_f }
                            have hclv_sem2 : sem2.core.cur_level < 2 ^ 32 := by
                              rw [hpi2.ag.get FullCoreState.cur_level]; exact hclv_lt32
                            have hcur_eq2 : (BitVec.ofNat 64 st.core.cur_level).setWidth 32 =
                                BitVec.ofNat 32 sem2.core.cur_level := by
                              rw [hcl_st, hcur_eq1, hpi2.ag.get FullCoreState.cur_level]
                            s15_head_steps
                            · have hinv2 := propLit_inv_keep_large hpi1 hpi1.sw hnot_st1 hq1_nat
                                hq2_nat hp2_nat (Nat.add_le_add_right hq_le 2) hpi1.sw.p_le_end
                                (bv32_mask7f_flag0 other) hcr_lt hcr_ref1
                              simp only [BitVec.ofNat_eq_ofNat, hp2_nat] at hinv2
                              exact ih2 _ (off_v, tend_v, unass_v, unfl_v, ticks_v + 1#64,
                                p_v + 1#64 + 1#64, q_v + 2#64, end_v, ()) m hrem_dec
                                ⟨sem2, by rw [hp2_nat], by rwa [hp2_nat], htend1_eq, hunass1_eq,
                                  hunfl1_eq, hnl1, hoom1, hct1, by
                                    simpa only [sem2, wstk2, BitVec.ofNat_eq_ofNat, hq1_nat,
                                      fastPropMem_wstk, fastPropMem_with_wstk] using hm⟩
                            · have hne_ign : cref.setWidth 64 ≠ ignore_ref := by assumption
                              have hov_f := propLit_vals_neg hpi1.nw hother_lt hother_lt1_vals
                                (by simpa only [fastPropMem_vals] using hc)
                              have ⟨hpi_c, hcf_c⟩ := propLit_large_confl hpi1 hnot_st1 hq_le
                                hq1_nat hq2_nat hp2_nat hcr_lt hcr_ref1 hng1 hne_ign hov_f hunit
                              let sem_c : FullState :=
                                { sem1 with core :=
                                    { sem1.core with
                                      wstk := wstk2, confl_type := 2#64,
                                      confl_ref := cref.setWidth 64 } }
                              simp only [BitVec.ofNat_eq_ofNat, hp2_nat] at hpi_c
                              have hm_c : (FullMem c (fastPropMem s sem_c) ⋆ R) m := by
                                simpa only [sem_c, wstk2,
                                  show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl,
                                  show (1 : BitVec 64) = 1#64 from rfl,
                                  show (2 : BitVec 64) = 2#64 from rfl, hq1_nat,
                                  fastPropMem_wstk, fastPropMem_with_large_confl_wstk] using hm
                              exact hB (off_v, tend_v, unass_v, unfl_v, ticks_v + 1#64,
                                p_v + 1#64 + 1#64, q_v + 2#64, end_v, true, ()) m
                                ⟨sem_c, by simpa only [hq1_nat, hp2_nat, hq2_nat] using hpi_c,
                                  htend1_eq, hunass1_eq, hunfl1_eq, by simp, fun _ => hcf_c, hm_c⟩
                            · have hov_un := propLit_vals_un hpi1.nw hother_lt hother_lt1_vals
                                hov_np (by simpa only [fastPropMem_vals] using hc)
                              dsimp only
                              have hm2 : (FullMem c (fastPropMem s sem2) ⋆ R) m := by
                                simpa only [sem2, wstk2,
                                  show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl,
                                  show (1 : BitVec 64) = 1#64 from rfl,
                                  hq1_nat, fastPropMem_wstk, fastPropMem_with_wstk] using hm
                              refine fastProp_large_assign_wp (k_next := fun tn un uf => .jump L2
                                (.var off_v, (.var tn, (.var un, (.var uf,
                                (.var (ticks_v + 1#64 + 1#64), (.var (p_v + 1#64 + 1#64),
                                (.var (q_v + 2#64), (.var end_v, ())))))))))
                                hmaxv har hcv0 hpi2 hlen2_mem hcr_lt
                                hcr_ref1 hng1 hfit1 hother_lt hov_un hnot_st1 hother_mem hnot_mem
                                hunit hnl1 hcur_eq2 hclv_sem2 hcsz32_nat h3_idx htend1_eq hoom1 hct1
                                hm2 ?_
                              intro sem3 tend_n unass_n unfl_n m' hpi3 ht3 hu3 huf3 hnl3 hoom3
                                hct3 hm'
                              exact ih2 _ (off_v, tend_n, unass_n, unfl_n, ticks_v + 1#64 + 1#64,
                                p_v + 1#64 + 1#64, q_v + 2#64, end_v, ()) m' hrem_dec
                                ⟨sem3, by rw [hp2_nat], by rwa [hp2_nat], ht3, hu3, huf3, hnl3,
                                  hoom3, hct3, hm'⟩
                          · have hri_ne : ri_f ≠ 0xFFFFFFFF#32 := hri_ne
                            have h3_1_idx : (cref.setWidth 64 + 3#64 + 1#64).toNat =
                                cref.toNat + 4 := by
                              rw [bv64_add_toNat (by
                                rw [h3_idx, ← hcr64, show (1#64).toNat = 1 from rfl]
                                exact hcr_u64), h3_idx]; rfl
                            s15_head_split
                            · refine s15_large_push_wp hPush (nl_lvl0 := nl_lvl0)
                                (k_ok := fun o4 pn qn en => .jump L2 (.var o4, (.var tend_v,
                                  (.var unass_v, (.var unfl_v, (.var (ticks_v + 1#64 + 1#64),
                                  (.var pn, (.var qn, (.var en, ())))))))))
                                (k_oom := fun o4 pn qn en => .jump B (.var o4, (.var tend_v,
                                  (.var unass_v, (.var unfl_v, (.var (ticks_v + 1#64 + 1#64),
                                  (.var pn, (.var qn, (.var en, (.imm true, ()))))))))))
                                c.hmaxv c.harena hlen0 hcv0
                                hpi1 hlen1_mem hcr_lt hcr_ref1 hfit1 har4 hnot_st1 hother_lt
                                hflag hr2 hr_lt hrepl_def hcand h1_idx h3_idx h3_1_idx
                                htend1_eq hunass1_eq hunfl1_eq hnl1 hoom1 hct1 hp2_nat hq_le
                                (hwstk1 ▸ hq_lt_ws1) hmj2 ?_ ?_
                              · intro st4 off4_v m_p hdec4 hpi4 ht4 hu4 huf4 hnl4 hoom4 hct4 hm4
                                exact ih2 _ (off4_v, tend_v, unass_v, unfl_v, ticks_v + 1#64 + 1#64,
                                  off4_v + (p_v + 1#64 + 1#64 - off_v), off4_v + (q_v - off_v),
                                  off4_v + (end_v - off_v), ()) m_p hdec4
                                  ⟨st4, rfl, hpi4, ht4, hu4, huf4, hnl4, hoom4, hct4, hm4⟩
                              · intro st6 off4_v m_f hpi6 ht6 hu6 huf6 hoom6 hm6
                                exact hB (off4_v, tend_v, unass_v, unfl_v, ticks_v + 1#64 + 1#64,
                                  off4_v + (p_v + 1#64 + 1#64 - off_v),
                                  off4_v + (q_v - off_v) + 2#64,
                                  off4_v + (end_v - off_v), true, ()) m_f
                                  ⟨_, hpi6, ht6, hu6, huf6, by simp, fun _ => Or.inl hoom6, hm6⟩
                            · exact absurd hc hri_ne
                      · intro Jsrch hJsrch; s15_head_steps
                        · exact hJsrch (2#32, ()) mj2
                            ⟨by decide,
                             Nat.lt_of_lt_of_le (by decide : (2#32).toNat < 3) hcsz3_1, rfl⟩
                        · exact hJsrch (2#32, ()) mj2
                            ⟨by decide,
                             Nat.lt_of_lt_of_le (by decide : (2#32).toNat < 3) hcsz3_1, rfl⟩
                        · have h1_mod : (cref.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 =
                              cref.toNat + 1 := by
                            simp only [BitVec.reduceToNat]; exact Nat.mod_eq_of_lt (by omega)
                          have h2_mod : (cref.toNat + (2 : BitVec 64).toNat) % 2 ^ 64 =
                              cref.toNat + 2 := by
                            simp only [BitVec.reduceToNat]; exact Nat.mod_eq_of_lt (by omega)
                          have hnot_le_srch :
                              ¬ fullArenaClauseSizeCore sem1.core cref.toNat ≤
                                (sem1.core.arena[cref.toNat + 1]'(by rw [haren1]; omega)).toNat :=
                            by
                            have hh : ¬ (sem.core.arena[(cref.toNat + (2 : BitVec 64).toNat) %
                                    2 ^ 64]'(by rw [h2_mod]; exact hcr2_lt_ar)).toNat ≤
                                (sem1.core.arena[(cref.toNat + (1 : BitVec 64).toNat) %
                                    2 ^ 64]'(by rw [h1_mod, haren1]; omega)).toNat := by
                              simpa only [fc_getElem_arena, fastPropMem_arena] using hc
                            have hcsz_0 : (sem.core.arena[cref.toNat + 2]'hcr2_lt_ar).toNat =
                                fullArenaClauseSizeCore sem1.core cref.toNat := by
                              rw [hcsz1]; unfold fullArenaClauseSizeCore
                              rw [List.getElem?_eq_getElem hcr2_lt_ar, Option.getD_some]
                            simp only [fc_getElem_eq_of_idx h2_mod _ hcr2_lt_ar, hcsz_0,
                              fc_getElem_eq_of_idx h1_mod _ (by rw [haren1]; omega)] at hh
                            exact hh
                          have h1_mod' : (cref.toNat + 1) % 2 ^ 64 = cref.toNat + 1 :=
                            Nat.mod_eq_of_lt (by omega)
                          have hnot_lt_2 :
                              ¬ (sem1.core.arena[cref.toNat + 1]'(by rw [haren1]; omega)).toNat < 2
                            := by
                            have hh : ¬ ((fastPropMem s sem1).core.arena[(cref.toNat +
                                  (1 : BitVec 64).toNat) % 2 ^ 64]'(by
                                rw [fastPropMem_arena, h1_mod, haren1]; omega)).toNat <
                                (2 : BitVec 32).toNat := by assumption
                            simpa only [fc_getElem_arena, fastPropMem_arena, BitVec.reduceToNat,
                              h1_mod'] using hh
                          have hsrch_mem :
                              (fastPropMem s sem1).core.arena[(cref.setWidth 64 + 1).toNat]'(by
                                rw [show (1 : BitVec 64) = 1#64 from rfl, fastPropMem_arena,
                                  h1_idx, haren1]; omega) =
                              sem1.core.arena[cref.toNat + 1]'(by rw [haren1]; omega) := by
                            rw [fc_getElem_arena]
                            exact fc_getElem_eq_of_idx
                              (by rw [show (1 : BitVec 64) = 1#64 from rfl]; exact h1_idx) _ _
                          refine hJsrch _ mj2
                            ⟨by simpa only [hsrch_mem] using Nat.le_of_not_lt hnot_lt_2,
                             by simpa only [hsrch_mem] using Nat.lt_of_not_le hnot_le_srch, rfl⟩
                  · intro J3 hJ3; s15_head_steps
                    · let l1 := sem.core.arena[(cref.setWidth 64 + 4#64).toNat]'(h4_idx ▸
                        hcr4_lt_ar)
                      have h3_mod : (cref.toNat + BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 =
                          cref.toNat + 3 := by
                        simp only [BitVec.reduceToNat]; exact Nat.mod_eq_of_lt hcr3_lt64
                      have hl0_is_not : sem.core.arena[cref.toNat + 3]'hcr3_lt_ar = not_lit :=
                        (fc_getElem_eq_of_idx h3_mod _ _).symm.trans
                          ((fc_getElem_arena s sem).symm.trans hc)
                      have hpi_drop : PropLitInv c F0 F_cur s sem not_lit.toNat off_v.toNat
                          q_v.toNat (p_v.toNat + 2) end_v.toNat :=
                        ⟨hpi.len, hpi.nw, hsw_drop, hpi.ag, hpi.tr, hpi.perm, hpi.sc_eq,
                         hpi.not_f⟩
                      have ⟨hpi1, href1, hng1, hcsz1, har3, har4⟩ := fastProp_js3_swap hpi_drop
                        hcr_ref hng_t hcsz3 hcr_fit hl0_is_not
                        (fc_getElem_eq_of_idx h4_idx.symm hcr4_lt_ar (h4_idx ▸ hcr4_lt_ar))
                      have h3_1_idx : (cref.setWidth 64 + 3#64 + 1#64).toNat = cref.toNat + 4 := by
                        rw [bv64_add_toNat (by
                          rw [h3_idx, ← hcr64, show (1#64).toNat = 1 from rfl]; exact hcr_u64),
                          h3_idx]; rfl
                      have hl1_mem_eq :
                          (fastPropMem s sem).core.arena[
                            (cref.setWidth 64 + 3#64 + 1#64).toNat]'(by
                              rw [fastPropMem_arena, h3_1_idx]; exact hcr4_lt_ar) = l1 := by
                        rw [fc_getElem_arena]
                        exact (fc_getElem_eq_of_idx h3_1_idx _ hcr4_lt_ar).trans
                          (fc_getElem_eq_of_idx h4_idx.symm hcr4_lt_ar (h4_idx ▸ hcr4_lt_ar))
                      have hm1 : (FullMem c (fastPropMem s { sem with core := { sem.core with
                          arena := (sem.core.arena.set (cref.toNat + 3) l1).set
                            (cref.toNat + 4) not_lit } }) ⋆ R) m := by
                        simp only [BitVec.ofNat_eq_ofNat, fastPropMem_arena,
                          h3_idx, h3_1_idx] at hm
                        have hl1_idx : sem.core.arena[cref.toNat + 4]'hcr4_lt_ar = l1 :=
                          fc_getElem_eq_of_idx h4_idx.symm hcr4_lt_ar (h4_idx ▸ hcr4_lt_ar)
                        rw [hl1_idx] at hm
                        simpa only [← fastPropMem_with_arena] using hm
                      simp only [BitVec.ofNat_eq_ofNat]
                      rw [hl1_mem_eq]
                      exact hJ3 (l1, ()) m ⟨_, hpi1, hoom_sem, hct_sem, rfl, rfl, rfl, rfl, rfl,
                        hnl_eq, href1, hng1, hcsz1, har3, har4, hm1⟩
                    · exact ih2 _ (off_v, tend_v, unass_v, unfl_v, ticks_v + 1#64,
                        p_v + 1#64 + 1#64, q_v, end_v, ()) ml hrem_dec
                        ⟨sem, by rw [hp2_nat], propLit_inv_drop (ticks' := sem.scratch.search_ticks)
                          hpi hsw_drop hp2_nat, htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_sem,
                          hct_sem, hml⟩
                    · have h4_mod :
                          (cref.toNat + BitVec.toNat (3 : BitVec 64) +
                            BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = cref.toNat + 4 := by
                        simp only [BitVec.reduceToNat]; exact Nat.mod_eq_of_lt (by omega)
                      have hl1_eq4 : sem.core.arena[cref.toNat + 4]'(hcr4_lt_ar) = not_lit :=
                        (fc_getElem_eq_of_idx h4_mod _ _).symm.trans
                          ((fc_getElem_arena s sem).symm.trans hc)
                      exact hJ3 (_, ()) ml ⟨sem, ⟨hpi.len, hpi.nw, hsw_drop, hpi.ag, hpi.tr,
                          hpi.perm, hpi.sc_eq, hpi.not_f⟩, hoom_sem, hct_sem, rfl, rfl, rfl, rfl,
                        rfl, hnl_eq, hcr_ref, hng_t, rfl,
                        by rw [fc_getElem_arena, List.getElem?_eq_getElem hcr3_lt_ar]
                           exact congrArg some
                             (fc_getElem_eq_of_idx
                               (by rw [show (3 : BitVec 64) = 3#64 from rfl]; exact h3_idx.symm)
                               hcr3_lt_ar _),
                        by change sem.core.arena[cref.toNat + 4]? = some not_lit
                           rw [← hl1_eq4]; exact List.getElem?_eq_getElem hcr4_lt_ar,
                        hml⟩
          · intro J2 hJ2
            s15_head_split
            · have hblk_lt_2cv : (w0_v &&& 2147483647#32).toNat < 2 * sem.core.cur_vars := by
                rw [hcv_eq]
                have hc' := hc
                simp only [fastPropMem_wstk, hcv_st] at hc'
                rw [Nat.mod_eq_of_lt hcv_lt64, Nat.mod_eq_of_lt h2cv_lt64] at hc'
                exact hc'
              have hblk_vals_lt : (w0_v &&& 2147483647#32).toNat < sem.core.vals.length :=
                fastProp_lt_vals hpi.len.core_ok hblk_lt_2cv
              have hblk_vals_mem : (BitVec.setWidth 64
                  ((fastPropMem s sem).core.wstk[p_v.toNat]'(fastPropMem_wstk s sem ▸ hp_lt_w) &&&
                    2147483647)).toNat < (fastPropMem s sem).core.vals.length := by
                dsimp only [w0_v] at hblk_vals_lt
                simp only [bv_c0_zext32_64, fc_getElem_wstk, fastPropMem_vals]
                exact hblk_vals_lt
              s15_head_split
              · s15_head_split
                · have hflag : (w0_v &&& 0x80000000#32) ≠ 0#32 := by
                    simpa only [ne_eq, ← BitVec.ofNat_eq_ofNat, fc_getElem_wstk, fastPropMem_wstk]
                      using hc
                  obtain ⟨hother_lt, hent, hrem1⟩ :=
                    watchSlice_inv_bin hpi.sw.rem_slice hp_rem_pos hw0_get hflag
                  have hsw1 := (hpi.sw.advance_rem (p' := p_v.toNat + 1) (Nat.le_succ _) hp_lt
                    (by simpa [Nat.sub_sub] using hrem1)).write_bin
                    (c := c) hpi.len.core_ok.cur_vars_le hnot_sem hq_le hq_lt_ws hflag hother_lt
                    hent
                  let wstk1 := sem.core.wstk.set q_v.toNat w0_v
                  let sem1 : FullState := { sem with core := { sem.core with wstk := wstk1 } }
                  have hlen1 : sem1.LengthsOk c :=
                    ⟨{ hpi.len.core_ok with wstk_len_arr := by simp [sem1, wstk1, hwstk_len] },
                     hpi.len.scratch_ok⟩
                  have hnw1 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem1.core) :=
                    fullWitnessInv_nw_congr hlen1.core_ok.cur_vars_le hpi.nw
                      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                  have hsw1_rw : SplitWatchesInv F_cur sem1.core not_lit.toNat off_v.toNat
                      (q_v + 1#64).toNat (p_v.toNat + 1) end_v.toNat := by
                    rw [hq1_nat]; exact hsw1
                  have hpi1 : PropLitInv c F0 F_cur s sem1 not_lit.toNat off_v.toNat
                      (q_v + 1#64).toNat (p_v + 1#64).toNat end_v.toNat := by
                    rw [hp1_nat]
                    exact ⟨hlen1, hnw1, hsw1_rw,
                      hpi.ag.update (fun k => { k with wstk := wstk1 }),
                      hpi.tr.congr rfl rfl rfl, hpi.perm, hpi.sc_eq, hpi.not_f⟩
                  have hq_lt_mem : q_v.toNat < (fastPropMem s sem).core.wstk.length := by
                    rw [fastPropMem_wstk]; exact hq_lt_ws
                  s15_head_steps
                  exact ih2 (end_v.toNat - (p_v.toNat + 1)) (off_v, tend_v, unass_v, unfl_v,
                    ticks_v, p_v + 1#64, q_v + 1#64, end_v, ()) m
                    (Nat.sub_lt hp_rem_pos Nat.zero_lt_one)
                    ⟨sem1, by rw [hp1_nat], hpi1, htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_sem,
                      hct_sem, by simpa only [BitVec.ofNat_eq_ofNat, fastPropMem_wstk,
                        fastPropMem_with_wstk] using hm⟩
                · have hflag : (w0_v &&& 0x80000000#32) = 0#32 := by
                    simpa only [← BitVec.ofNat_eq_ofNat, fc_getElem_wstk, fastPropMem_wstk] using hc
                  have ⟨h2le, cref0, hcr_get, hcr_lt, hcr_ref, hrem2⟩ :=
                    watchSlice_inv_large hpi.sw.rem_slice hp_rem_pos hw0_get hflag
                  s15_head_split
                  · have hp1_lt : (p_v + (1 : BitVec 64)).toNat < end_v.toNat := hc
                    have h2_le_end : p_v.toNat + 2 ≤ end_v.toNat :=
                      Nat.add_sub_cancel' hp_le ▸ Nat.add_le_add_left h2le p_v.toNat
                    have hp2_wcap : p_v.toNat + 2 ≤ c.wcap := Nat.le_trans h2_le_end hend_wcap
                    have hp2_64 : p_v.toNat + 2 < 2 ^ 64 :=
                      Nat.lt_of_le_of_lt hp2_wcap (Nat.lt_trans hwc (by decide))
                    have hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2 := by
                      rw [bv64_add_toNat (a := p_v + 1#64) (b := 1#64)
                        (by rw [hp1_nat]; exact hp2_64), hp1_nat]; rfl
                    have hq2_nat : (q_v + 2#64).toNat = q_v.toNat + 2 :=
                      bv64_add2_toNat (a := q_v) (Nat.lt_of_le_of_lt
                        (Nat.add_le_add_right (Nat.le_trans hq_le (Nat.le_trans hp_le hend_wcap)) 2)
                        hwc64_2)
                    have hcr_idx_lt : (p_v + 1#64).toNat < sem.core.wstk.length := by
                      rw [hp1_nat, hwstk_len]
                      exact Nat.lt_of_lt_of_le (Nat.lt_of_succ_le h2_le_end) hend_wcap
                    have hcr_eq : sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx_lt = cref0 := by
                      have h1 : sem.core.wstk[p_v.toNat + 1]? =
                          some (sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx_lt) := by
                        rw [← hp1_nat]; exact List.getElem?_eq_getElem hcr_idx_lt
                      exact Option.some.inj (h1.symm.trans hcr_get)
                    have hsw_drop : SplitWatchesInv F_cur sem.core not_lit.toNat off_v.toNat
                        q_v.toNat (p_v.toNat + 2) end_v.toNat :=
                      hpi.sw.advance_rem (p' := p_v.toNat + 2) (by omega) h2_le_end
                        (by simpa [Nat.sub_sub] using hrem2)
                    have hcr_eq_c0 : sem.core.wstk[(p_v + 1).toNat]'(by
                        rw [show (1 : BitVec 64) = 1#64 from rfl]; exact hcr_idx_lt) = cref0 :=
                      hcr_eq
                    s15_head_steps
                    exact ih2 (end_v.toNat - (p_v.toNat + 2)) (off_v, tend_v, unass_v, unfl_v,
                      ticks_v, p_v + 1#64 + 1#64, q_v + 2#64, end_v, ()) m (fc_rem2_lt h2_le_end)
                      ⟨_, by rw [hp2_nat], propLit_inv_keep_large hpi hsw_drop hnot_sem hq1_nat
                        hq2_nat hp2_nat (Nat.add_le_add_right hq_le 2) h2_le_end hflag hcr_lt
                        (hcr_eq ▸ hcr_ref),
                        htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_sem, hct_sem, by
                          dsimp only [w0_v]
                          simpa only [hq1_nat, hcr_eq_c0, fc_getElem_wstk,
                            fastPropMem_wstk, fastPropMem_with_wstk] using hm⟩
                  · have hge : end_v.toNat ≤ (p_v + (1 : BitVec 64)).toNat := by
                      have hc' : ¬ (p_v.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 < end_v.toNat := hc
                      rw [show (1 : BitVec 64).toNat = 1 from rfl,
                        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.add_le_add_right hp_le 1)
                          (Nat.lt_of_le_of_lt (Nat.add_le_add_right hend_wcap 1) hwc64)),
                        ← hp1_pre] at hc'
                      exact Nat.not_lt.mp hc'
                    rw [hp1_pre] at hge
                    have h2_le_end : p_v.toNat + 2 ≤ end_v.toNat :=
                      Nat.add_sub_cancel' hp_le ▸ Nat.add_le_add_left h2le p_v.toNat
                    exact absurd hge (Nat.not_le.mpr (Nat.lt_of_succ_le h2_le_end))
              · s15_head_steps
                exact hJ2 () ml ⟨rfl, fun hlt => by
                  dsimp only [w0_v]
                  simpa only [← BitVec.ofNat_eq_ofNat, fc_getElem_wstk, fastPropMem_wstk,
                    fc_getElem_vals, fastPropMem_vals] using hc⟩
            · s15_head_steps
              exact hJ2 () ml ⟨rfl, fun hlt => by
                have hc' := hc
                simp only [fastPropMem_wstk, hcv_st] at hc'
                rw [Nat.mod_eq_of_lt hcv_lt64, Nat.mod_eq_of_lt h2cv_lt64] at hc'
                dsimp only [w0_v]
                exact absurd (hcv_eq ▸ hlt) hc'⟩
        · exact hB (off_v, tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, end_v, false, ()) ml
            ⟨sem, hpi, htend_eq, hunass_eq, hunfl_eq, fun _ => ⟨hoom_sem, hct_sem⟩, by simp, hml⟩
      · intro B L2 _ hL2; s15_head_steps
        have hwc_64 : c.wcap < 2 ^ 64 := Nat.lt_trans hwc (by decide)
        have hoff_sz_lt64 : fullWatchOffCore st.core not_lit.toNat +
            fullWatchSizeCore s.core not_lit.toNat < 2 ^ 64 :=
          Nat.lt_of_le_of_lt (Nat.le_trans hbd_st hwlen_st) hwc_64
        have hoff_nat :
            ((st.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'(by
              rw [hidx0_nat, hwv_st]; omega)).setWidth 64).toNat =
            fullWatchOffCore st.core not_lit.toNat := by
          unfold fullWatchOffCore; rw [bv_c0_zext32_64]
          exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx hidx0_nat _)
        have hpr_nat :
            ((st.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'(by
              rw [hidx0_nat, hwv_st]; omega)).setWidth 64 + pr).toNat =
            fullWatchOffCore st.core not_lit.toNat + pr.toNat := by
          rw [bv64_add_toNat (by
            rw [hoff_nat]
            exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hpr_le_sz0 _) hoff_sz_lt64), hoff_nat]
        have hqr_nat :
            ((st.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'(by
              rw [hidx0_nat, hwv_st]; omega)).setWidth 64 + qr).toNat =
            fullWatchOffCore st.core not_lit.toNat + qr.toNat := by
          rw [bv64_add_toNat (by
            rw [hoff_nat]
            exact Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_trans hqr_le_pr hpr_le_sz0) _)
              hoff_sz_lt64), hoff_nat]
        have hend_nat :
            ((st.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'(by
              rw [hidx0_nat, hwv_st]; omega)).setWidth 64 +
            (s.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'(by
              rw [hidx1_nat, hwv0]; omega)).setWidth 64).toNat =
            fullWatchOffCore st.core not_lit.toNat + fullWatchSizeCore s.core not_lit.toNat := by
          rw [bv64_add_toNat (by rw [hoff_nat, hsz0_eq]; exact hoff_sz_lt64), hoff_nat, hsz0_eq]
        have htend0 : (BitVec.ofNat 64 st.core.trail_end).toNat = st.core.trail_end := by
          rw [hte_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hte0_lt64]
        have hst_fpm : fastPropMem s st = st := by
          rw [fastPropMem_def]
          cases st with | mk stc stsc =>
          dsimp only at hte_eq hun_eq huf_eq hticks_eq
          cases stc; cases stsc; simp only at *; subst_vars; rfl
        refine hL2 _ _ mj ⟨st, rfl, ?_, htend0, rfl, rfl, hnl_eq0, hoom_st, hct_st, ?_⟩
        · rw [hoff_nat, hqr_nat, hpr_nat, hend_nat]; exact hpi0
        · rw [hst_fpm]; exact hmj
  · intro L hL; s15_hsteps
    exact hL dlen (0#64, ()) m ⟨s, 0, by omega, by decide, Nat.zero_le _, hlen0, hnw0, hsw0,
      .refl _ _, .refl _, .refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hoom0, rfl, hm⟩

end LeanQbe.T.Examples.Kissat.FullM6BcpS15
