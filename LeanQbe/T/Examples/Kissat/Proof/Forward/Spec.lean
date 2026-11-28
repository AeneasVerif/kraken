/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Forward
public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specification Table for `Kissat.Src.Forward` (`Proof.Forward.Spec`)

Canonical flat-`Env` (`SegCert`) UNSAT-sound `Spec` definitions, `deps`, `Spec.XFree`
proofs, `specs` table matching `Src.Forward.fns` `1:1` (`noExit := true`, `9` rows),
table invariants, `_intro`/`_elim` wrappers, and `Env.Sat.has` projections (`0` legacy
imports, `0` `@[expose]` on theorems, lemmas, or sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Forward.Spec

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

/-! ## 1. External Dependency Table (`deps`) -/

/-- Canonical upstream specification table covering all `extern` callees of
`Kissat.Src.Forward` (`Arena`, `Watch`, `Clause`, `Collect`, `Dense`). -/
@[expose] def deps : List SpecEntry :=
  Proof.Arena.Spec.specs ++ Proof.Watch.Spec.specs ++ Proof.Clause.Spec.specs ++
  Proof.Collect.Spec.specs ++ Proof.Dense.Spec.specs

/-! ## 2. Function `Spec` Contracts (`9` fns in `Src.Forward.fns`) -/

/-- `full_fwd_dedup_bins`: deduplicates binary watches in dense mode, returning `false`
only on level-0 unsatisfiability (`F0.Unsat`). -/
@[expose] def fullFwdDedupBinsSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → (ok = false → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- `full_fwd_flush_large_m7`: flushes all large-clause occurrence entries from watches
in both sparse and dense modes (`FullWitnessInv`), keeping binary watches intact. -/
@[expose] def fullFwdFlushLargeM7Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.dense_mode = s.core.dense_mode →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.vals = s.core.vals → s'.core.lvl = s.core.lvl → s'.core.flags = s.core.flags →
      s'.core.fuel = s.core.fuel → s'.core.oom = s.core.oom →
      s'.core.inconsistent = s.core.inconsistent →
      s'.core.d_cur = s.core.d_cur → s'.core.d_val = s.core.d_val →
      s'.core.num_binary = s.core.num_binary →
      s'.core.frame_trail = s.core.frame_trail → s'.core.frame_dec = s.core.frame_dec →
      s'.core.trail_end = s.core.trail_end → s'.core.propagated = s.core.propagated →
      s'.core.probing = s.core.probing →
      s'.scratch.last_learned = s.scratch.last_learned →
      s'.scratch.extend_len = s.scratch.extend_len →
      s'.scratch.walk_vals = s.scratch.walk_vals →
      s'.scratch.walk_best = s.scratch.walk_best →
      s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.sim_sig = s.scratch.sim_sig →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- `full_dense_bin_roundtrip_fid`: flushes watches, sweeps binary clauses, and
rebuilds binary watches in both sparse (`Walk`) and dense (`Probe`) modes. -/
@[expose] def fullDenseBinRoundtripFidSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.dense_mode = s.core.dense_mode →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.vals = s.core.vals → s'.core.lvl = s.core.lvl → s'.core.flags = s.core.flags →
      s'.core.fuel = s.core.fuel → s'.core.inconsistent = s.core.inconsistent →
      s'.core.d_cur = s.core.d_cur → s'.core.d_val = s.core.d_val →
      s'.core.frame_trail = s.core.frame_trail → s'.core.frame_dec = s.core.frame_dec →
      s'.core.trail_end = s.core.trail_end → s'.core.propagated = s.core.propagated →
      s'.core.probing = s.core.probing → FullArenaPermEq s.core s'.core →
      s'.scratch.extend_len = s.scratch.extend_len →
      s'.scratch.walk_vals = s.scratch.walk_vals →
      s'.scratch.walk_best = s.scratch.walk_best →
      s'.scratch.last_learned = s.scratch.last_learned →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- `full_fwd_reconnect_irred_m7`: flushes large occurrences and reconnects unsatisfied
irredundant large clauses into dense watch lists. -/
@[expose] def fullFwdReconnectIrredM7Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      s'.core.inconsistent = s.core.inconsistent →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- `full_fwd_scan_lit_m7`: read-only forward subsumption/strengthening scan of dense
watch occurrences of `scan_lit` against the marked clause at `cref`. -/
@[expose] def fullFwdScanLitM7Spec : Spec [i64, i32, i32, i32, .bool] [i32] :=
  fun (h, cref, sz, scan_lit, check_bins, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧ FullArenaVarsNodup s ∧
      cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
      sz.toNat = fullArenaClauseSize s cref.toNat ∧
      scan_lit.toNat < 2 * s.core.cur_vars ∧
      (check_bins = true → scan_lit.toNat ∈ fullArenaClauseLits s cref.toNat) ∧
      (∀ x < 2 * s.core.cur_vars,
        s.core.lit_mark[x]?.getD 0#8 ≠ 0#8 ↔ x ∈ fullArenaClauseLits s cref.toNat) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r : BitVec 32,
        (r = 0xFFFFFFFF#32 ∨ r = 0xFFFFFFFE#32 ∨
          (r.toNat ∈ fullArenaClauseLits s cref.toNat ∧
            (cnfOfClauses F_cur).EntailsClause
              (cnfClause ((fullArenaClauseLits s cref.toNat).filter (· != r.toNat))))) →
        Q (r, ()) m

/-- `full_fwd_check_cl_m7`: tests candidate clause `cref` for forward subsumption or
self-subsuming resolution strengthening, returning `false` only on `F0.Unsat`. -/
@[expose] def fullFwdCheckClM7Spec : Spec [i64, i32] [.bool] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.red_refs = s.scratch.red_refs →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- `full_fwd_connect_subsumer_m7`: connects surviving candidate clause `cref` on the
least-occurring literal in dense watches. -/
@[expose] def fullFwdConnectSubsumerM7Spec : Spec [i64, i32] [] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.fuel = s.core.fuel → s'.core.inconsistent = s.core.inconsistent →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.red_refs = s.scratch.red_refs →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- `full_fwd_collect_sort_m7`: collects candidate irredundant large clauses into
`red_refs[0 ..< ncand)` and bucket-sorts ascending by length. -/
@[expose] def fullFwdCollectSortM7Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ ncand s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      s'.core.oom = s.core.oom → s'.core.inconsistent = s.core.inconsistent →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      ncand.toNat ≤ c.red_cap / 2 →
      (∀ i < ncand.toNat,
        (s'.scratch.red_refs[i]?.getD 0#32).toNat ∈ fullArenaClauseRefs s') →
      (FullMem c s' ⋆ R) m' → Q (ncand, ()) m'

/-- `full_forward_sub_m7`: bounded forward subsumption and self-subsuming resolution pass
preserving `FullDenseInv`, returning `20#64` only on `F0.Unsat`. -/
@[expose] def fullForwardSubM7Spec : Spec [i64, i64] [i64] := fun (h, _budget, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ## 3. Canonical `SpecEntry` Table, Invariants & `Env.Sat.has` Projections -/

/-- Canonical `SpecEntry` table matching `Src.Forward.fns` `1:1` (`9` rows). -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_fwd_dedup_bins", [i64], [.bool], Forward.Spec.fullFwdDedupBinsSpec, true⟩
  , ⟨"full_fwd_flush_large_m7", [i64], [], fullFwdFlushLargeM7Spec, true⟩
  , ⟨"full_dense_bin_roundtrip_fid", [i64], [], fullDenseBinRoundtripFidSpec, true⟩
  , ⟨"full_fwd_reconnect_irred_m7", [i64], [], fullFwdReconnectIrredM7Spec, true⟩
  , ⟨"full_fwd_scan_lit_m7", [i64, i32, i32, i32, .bool], [i32],
      fullFwdScanLitM7Spec, true⟩
  , ⟨"full_fwd_check_cl_m7", [i64, i32], [.bool], fullFwdCheckClM7Spec, true⟩
  , ⟨"full_fwd_connect_subsumer_m7", [i64, i32], [], fullFwdConnectSubsumerM7Spec, true⟩
  , ⟨"full_fwd_collect_sort_m7", [i64], [i64], fullFwdCollectSortM7Spec, true⟩
  , ⟨"full_forward_sub_m7", [i64, i64], [i64], fullForwardSubM7Spec, true⟩ ]

theorem fullFwdDedupBinsSpec_xfree :
    Spec.XFree Forward.Spec.fullFwdDedupBinsSpec := by xfree

theorem fullFwdFlushLargeM7Spec_xfree : Spec.XFree fullFwdFlushLargeM7Spec := by xfree

theorem fullDenseBinRoundtripFidSpec_xfree :
    Spec.XFree fullDenseBinRoundtripFidSpec := by xfree

theorem fullFwdReconnectIrredM7Spec_xfree : Spec.XFree fullFwdReconnectIrredM7Spec := by xfree

theorem fullFwdScanLitM7Spec_xfree : Spec.XFree fullFwdScanLitM7Spec := by xfree

theorem fullFwdCheckClM7Spec_xfree : Spec.XFree fullFwdCheckClM7Spec := by xfree

theorem fullFwdConnectSubsumerM7Spec_xfree :
    Spec.XFree fullFwdConnectSubsumerM7Spec := by xfree

theorem fullFwdCollectSortM7Spec_xfree : Spec.XFree fullFwdCollectSortM7Spec := by xfree

theorem fullForwardSubM7Spec_xfree : Spec.XFree fullForwardSubM7Spec := by xfree

theorem specs_sigs :
    specs.map SpecEntry.sig = Src.Forward.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem specs_xfree : ∀ e ∈ specs, Spec.XFree e.spec := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fullFwdDedupBinsSpec_xfree
  · exact fullFwdFlushLargeM7Spec_xfree
  · exact fullDenseBinRoundtripFidSpec_xfree
  · exact fullFwdReconnectIrredM7Spec_xfree
  · exact fullFwdScanLitM7Spec_xfree
  · exact fullFwdCheckClM7Spec_xfree
  · exact fullFwdConnectSubsumerM7Spec_xfree
  · exact fullFwdCollectSortM7Spec_xfree
  · exact fullForwardSubM7Spec_xfree

theorem has_full_fwd_dedup_bins {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_fwd_dedup_bins" Forward.Spec.fullFwdDedupBinsSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 0) (by decide))
    fullFwdDedupBinsSpec_xfree

theorem has_full_fwd_flush_large_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_fwd_flush_large_m7" fullFwdFlushLargeM7Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 1) (by decide))
    fullFwdFlushLargeM7Spec_xfree

theorem has_full_dense_bin_roundtrip_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_dense_bin_roundtrip_fid" fullDenseBinRoundtripFidSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 2) (by decide))
    fullDenseBinRoundtripFidSpec_xfree

theorem has_full_fwd_reconnect_irred_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_fwd_reconnect_irred_m7" fullFwdReconnectIrredM7Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 3) (by decide))
    fullFwdReconnectIrredM7Spec_xfree

theorem has_full_fwd_scan_lit_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_fwd_scan_lit_m7" fullFwdScanLitM7Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 4) (by decide))
    fullFwdScanLitM7Spec_xfree

theorem has_full_fwd_check_cl_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_fwd_check_cl_m7" fullFwdCheckClM7Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 5) (by decide))
    fullFwdCheckClM7Spec_xfree

theorem has_full_fwd_connect_subsumer_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_fwd_connect_subsumer_m7" fullFwdConnectSubsumerM7Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 6) (by decide))
    fullFwdConnectSubsumerM7Spec_xfree

theorem has_full_fwd_collect_sort_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_fwd_collect_sort_m7" fullFwdCollectSortM7Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 7) (by decide))
    fullFwdCollectSortM7Spec_xfree

theorem has_full_forward_sub_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_forward_sub_m7" fullForwardSubM7Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 8) (by decide))
    fullForwardSubM7Spec_xfree

/-! ## 4. `_intro` / `_elim` Wrappers (`0` `@[expose]` on theorems) -/

theorem fullFwdDedupBinsSpec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → (ok = false → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Forward.Spec.fullFwdDedupBinsSpec (h, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hm, hQ⟩

theorem fullFwdDedupBinsSpec_elim {a m Q X}
    (h : Forward.Spec.fullFwdDedupBinsSpec a m Q X) :
    let (hp, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) s' m',
        FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.fuel = s.core.fuel → (ok = false → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, ⟨⟩⟩; exact h

theorem fullFwdFlushLargeM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {m : Mem 64}
    {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hlm : FullLitMarksClear c s) (hnd : FullArenaVarsNodup s) (hext : FullExtScratchOk c s)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ s' m',
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.dense_mode = s.core.dense_mode →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.vals = s.core.vals → s'.core.lvl = s.core.lvl → s'.core.flags = s.core.flags →
      s'.core.fuel = s.core.fuel → s'.core.oom = s.core.oom →
      s'.core.inconsistent = s.core.inconsistent →
      s'.core.d_cur = s.core.d_cur → s'.core.d_val = s.core.d_val →
      s'.core.num_binary = s.core.num_binary →
      s'.core.frame_trail = s.core.frame_trail → s'.core.frame_dec = s.core.frame_dec →
      s'.core.trail_end = s.core.trail_end → s'.core.propagated = s.core.propagated →
      s'.core.probing = s.core.probing →
      s'.scratch.last_learned = s.scratch.last_learned →
      s'.scratch.extend_len = s.scratch.extend_len →
      s'.scratch.walk_vals = s.scratch.walk_vals →
      s'.scratch.walk_best = s.scratch.walk_best →
      s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.sim_sig = s.scratch.sim_sig →
      (FullMem c s' ⋆ R) m' → Q () m') :
    fullFwdFlushLargeM7Spec (h, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hlen, hw, hlm, hnd, hext, hm, hQ⟩

theorem fullFwdFlushLargeM7Spec_elim {a m Q X} (h : fullFwdFlushLargeM7Spec a m Q X) :
    let (hp, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
      (FullMem c s ⋆ R) m ∧
      ∀ s' m',
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
        s'.core.dense_mode = s.core.dense_mode →
        s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
        s'.core.vals = s.core.vals → s'.core.lvl = s.core.lvl → s'.core.flags = s.core.flags →
        s'.core.fuel = s.core.fuel → s'.core.oom = s.core.oom →
        s'.core.inconsistent = s.core.inconsistent →
        s'.core.d_cur = s.core.d_cur → s'.core.d_val = s.core.d_val →
        s'.core.num_binary = s.core.num_binary →
        s'.core.frame_trail = s.core.frame_trail → s'.core.frame_dec = s.core.frame_dec →
        s'.core.trail_end = s.core.trail_end → s'.core.propagated = s.core.propagated →
        s'.core.probing = s.core.probing →
        s'.scratch.last_learned = s.scratch.last_learned →
        s'.scratch.extend_len = s.scratch.extend_len →
        s'.scratch.walk_vals = s.scratch.walk_vals →
        s'.scratch.walk_best = s.scratch.walk_best →
        s'.scratch.red_refs = s.scratch.red_refs →
        s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
        s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
        s'.scratch.scratch_buf = s.scratch.scratch_buf →
        s'.scratch.work_stk1 = s.scratch.work_stk1 →
        s'.scratch.work_stk2 = s.scratch.work_stk2 →
        s'.scratch.sim_sig = s.scratch.sim_sig →
        (FullMem c s' ⋆ R) m' → Q () m' := by
  rcases a with ⟨hp, ⟨⟩⟩; exact h

theorem fullDenseBinRoundtripFidSpec_intro {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64}
    {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hlm : FullLitMarksClear c s) (hnd : FullArenaVarsNodup s) (hext : FullExtScratchOk c s)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.dense_mode = s.core.dense_mode →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.vals = s.core.vals → s'.core.lvl = s.core.lvl → s'.core.flags = s.core.flags →
      s'.core.fuel = s.core.fuel → s'.core.inconsistent = s.core.inconsistent →
      s'.core.d_cur = s.core.d_cur → s'.core.d_val = s.core.d_val →
      s'.core.frame_trail = s.core.frame_trail → s'.core.frame_dec = s.core.frame_dec →
      s'.core.trail_end = s.core.trail_end → s'.core.propagated = s.core.propagated →
      s'.core.probing = s.core.probing → FullArenaPermEq s.core s'.core →
      s'.scratch.extend_len = s.scratch.extend_len →
      s'.scratch.walk_vals = s.scratch.walk_vals →
      s'.scratch.walk_best = s.scratch.walk_best →
      s'.scratch.last_learned = s.scratch.last_learned →
      (FullMem c s' ⋆ R) m' → Q () m') :
    fullDenseBinRoundtripFidSpec (h, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hlen, hw, hlm, hnd, hext, hm, hQ⟩

theorem fullDenseBinRoundtripFidSpec_elim {a m Q X}
    (h : fullDenseBinRoundtripFidSpec a m Q X) :
    let (hp, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (s' : FullState) (m' : Mem 64),
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
        s'.core.dense_mode = s.core.dense_mode →
        s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
        s'.core.vals = s.core.vals → s'.core.lvl = s.core.lvl → s'.core.flags = s.core.flags →
        s'.core.fuel = s.core.fuel → s'.core.inconsistent = s.core.inconsistent →
        s'.core.d_cur = s.core.d_cur → s'.core.d_val = s.core.d_val →
        s'.core.frame_trail = s.core.frame_trail → s'.core.frame_dec = s.core.frame_dec →
        s'.core.trail_end = s.core.trail_end → s'.core.propagated = s.core.propagated →
        s'.core.probing = s.core.probing → FullArenaPermEq s.core s'.core →
        s'.scratch.extend_len = s.scratch.extend_len →
        s'.scratch.walk_vals = s.scratch.walk_vals →
        s'.scratch.walk_best = s.scratch.walk_best →
        s'.scratch.last_learned = s.scratch.last_learned →
        (FullMem c s' ⋆ R) m' → Q () m' := by
  rcases a with ⟨hp, ⟨⟩⟩; exact h

theorem fullFwdReconnectIrredM7Spec_intro {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64}
    {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      s'.core.inconsistent = s.core.inconsistent →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      (FullMem c s' ⋆ R) m' → Q () m') :
    fullFwdReconnectIrredM7Spec (h, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hm, hQ⟩

theorem fullFwdReconnectIrredM7Spec_elim {a m Q X}
    (h : fullFwdReconnectIrredM7Spec a m Q X) :
    let (hp, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
      ∀ s' m',
        FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
        s'.core.inconsistent = s.core.inconsistent →
        s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
        (FullMem c s' ⋆ R) m' → Q () m' := by
  rcases a with ⟨hp, ⟨⟩⟩; exact h

theorem fullFwdScanLitM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {cref sz scan_lit : BitVec 32}
    {check_bins : Bool} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hdn : s.core.dense_mode ≠ 0#64) (hnd : FullArenaVarsNodup s)
    (href : cref.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref.toNat = false)
    (hsz : sz.toNat = fullArenaClauseSize s cref.toNat)
    (hsl : scan_lit.toNat < 2 * s.core.cur_vars)
    (hmem : check_bins = true → scan_lit.toNat ∈ fullArenaClauseLits s cref.toNat)
    (hlm : ∀ x < 2 * s.core.cur_vars,
      s.core.lit_mark[x]?.getD 0#8 ≠ 0#8 ↔ x ∈ fullArenaClauseLits s cref.toNat)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ r : BitVec 32,
      (r = 0xFFFFFFFF#32 ∨ r = 0xFFFFFFFE#32 ∨
        (r.toNat ∈ fullArenaClauseLits s cref.toNat ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause ((fullArenaClauseLits s cref.toNat).filter (· != r.toNat))))) →
      Q (r, ()) m) :
    fullFwdScanLitM7Spec (h, cref, sz, scan_lit, check_bins, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hlen, hw, hl0, hdn, hnd, href, hng, hsz, hsl, hmem, hlm, hm, hQ⟩

theorem fullFwdScanLitM7Spec_elim {a m Q X} (h : fullFwdScanLitM7Spec a m Q X) :
    let (hp, cref, sz, scan_lit, check_bins, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧ FullArenaVarsNodup s ∧
      cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
      sz.toNat = fullArenaClauseSize s cref.toNat ∧
      scan_lit.toNat < 2 * s.core.cur_vars ∧
      (check_bins = true → scan_lit.toNat ∈ fullArenaClauseLits s cref.toNat) ∧
      (∀ x < 2 * s.core.cur_vars,
        s.core.lit_mark[x]?.getD 0#8 ≠ 0#8 ↔ x ∈ fullArenaClauseLits s cref.toNat) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r : BitVec 32,
        (r = 0xFFFFFFFF#32 ∨ r = 0xFFFFFFFE#32 ∨
          (r.toNat ∈ fullArenaClauseLits s cref.toNat ∧
            (cnfOfClauses F_cur).EntailsClause
              (cnfClause ((fullArenaClauseLits s cref.toNat).filter (· != r.toNat))))) →
        Q (r, ()) m := by
  rcases a with ⟨hp, cref, sz, scan_lit, check_bins, ⟨⟩⟩; exact h

theorem fullFwdCheckClM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {cref : BitVec 32} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s)
    (href : cref.toNat ∈ fullArenaClauseRefs s) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.red_refs = s.scratch.red_refs →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    fullFwdCheckClM7Spec (h, cref, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, href, hm, hQ⟩

theorem fullFwdCheckClM7Spec_elim {a m Q X} (h : fullFwdCheckClM7Spec a m Q X) :
    let (hp, cref, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) s' m',
        FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
        s'.scratch.red_refs = s.scratch.red_refs →
        (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, cref, ⟨⟩⟩; exact h

theorem fullFwdConnectSubsumerM7Spec_intro {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64}
    {cref : BitVec 32} {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s)
    (href : cref.toNat ∈ fullArenaClauseRefs s) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.fuel = s.core.fuel → s'.core.inconsistent = s.core.inconsistent →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.red_refs = s.scratch.red_refs →
      (FullMem c s' ⋆ R) m' → Q () m') :
    fullFwdConnectSubsumerM7Spec (h, cref, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, href, hm, hQ⟩

theorem fullFwdConnectSubsumerM7Spec_elim {a m Q X}
    (h : fullFwdConnectSubsumerM7Spec a m Q X) :
    let (hp, cref, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
      (FullMem c s ⋆ R) m ∧
      ∀ s' m',
        FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
        s'.core.fuel = s.core.fuel → s'.core.inconsistent = s.core.inconsistent →
        s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
        s'.scratch.red_refs = s.scratch.red_refs →
        (FullMem c s' ⋆ R) m' → Q () m' := by
  rcases a with ⟨hp, cref, ⟨⟩⟩; exact h

theorem fullFwdCollectSortM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ ncand s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      s'.core.oom = s.core.oom → s'.core.inconsistent = s.core.inconsistent →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      ncand.toNat ≤ c.red_cap / 2 →
      (∀ i < ncand.toNat,
        (s'.scratch.red_refs[i]?.getD 0#32).toNat ∈ fullArenaClauseRefs s') →
      (FullMem c s' ⋆ R) m' → Q (ncand, ()) m') :
    fullFwdCollectSortM7Spec (h, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hm, hQ⟩

theorem fullFwdCollectSortM7Spec_elim {a m Q X}
    (h : fullFwdCollectSortM7Spec a m Q X) :
    let (hp, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
      ∀ ncand s' m',
        FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
        s'.core.oom = s.core.oom → s'.core.inconsistent = s.core.inconsistent →
        s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
        ncand.toNat ≤ c.red_cap / 2 →
        (∀ i < ncand.toNat,
          (s'.scratch.red_refs[i]?.getD 0#32).toNat ∈ fullArenaClauseRefs s') →
        (FullMem c s' ⋆ R) m' → Q (ncand, ()) m' := by
  rcases a with ⟨hp, ⟨⟩⟩; exact h

theorem fullForwardSubM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {h budget : BitVec 64} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hh : h = c.hdr) (hd : FullDenseInv c F0 s) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ r s' m',
      FullDenseInv c F0 s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    fullForwardSubM7Spec (h, budget, ()) m Q X :=
  ⟨c, F0, s, R, hh, hd, hm, hQ⟩

theorem fullForwardSubM7Spec_elim {a m Q X} (h : fullForwardSubM7Spec a m Q X) :
    let (hp, _budget, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullDenseInv c F0 s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.fuel = s.core.fuel → (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m' := by
  rcases a with ⟨hp, _budget, ⟨⟩⟩; exact h

end LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
