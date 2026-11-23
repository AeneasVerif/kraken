module

public import LeanQbe.T.Examples.Kissat.FullM6Orch
public import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullSpec1
public import LeanQbe.T.Examples.Kissat.FullSpec2
public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Examples.Kissat.FullM4Proof1
public import LeanQbe.T.Examples.Kissat.FullM4TernaryProof
public import LeanQbe.T.Examples.Kissat.FullM5SchedLemmas
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas1
public import LeanQbe.T.Examples.Kissat.FullWalkExtLemmas1

import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas2
import LeanQbe.T.Examples.Kissat.FullDeduce1UipLemmas1
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Examples.Kissat.FullM6MinShrinkProof3a
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Flat
import LeanQbe.T.FlatLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.WPLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M6 Orchestration Proofs Part 0 (`FullM6OrchProof0`)

M1-clean proof module (plain public section, opaque specs):
Proves parametric `(Γ : Env)` `Func.wp` contracts for the `20` Group-0 `FullM6Orch` functions:
- `13` inner forwarding shims (`full_wstack_defrag` .. `full_sweep_dense_m6`)
- `full_reorder_m6` (`stable == 0` guard over `full_reorder_queue_m7`)
- `full_ema_swap_m6` (`glue_used[36..55]`) and `full_switch_mode_m6`
- `full_reduce_m6` (`m6_hdr_recompute_tiers` + `FullM6BcpS15.fullBcpS15Spec` + watermarks)
- `full_analyze_rsn_m6_hdr`, `full_deduce_1uip_m6_hdr`, `full_analyze_core_m6`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Orch

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics

/-! ### Exported Orchestrator & Adapter Specs (`_of` / `_elim` / `_monoX`) -/

def m6ReorderSliceSpec : Spec [i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _budget, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullExtScratchPres s s')

theorem m6ReorderSliceSpec_of {c : FullCfg} {budget : BitVec 64} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    m6ReorderSliceSpec (c.hdr, budget, ()) m Q X :=
  ⟨c, s, R, rfl, hlen, hm, fun ⟨r, ⟨⟩⟩ s' m' hc hl hp hm' =>
    hQ r s' m' hc hl hp hm'⟩

theorem m6ReorderSliceSpec_elim {h budget : BitVec 64} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hs : m6ReorderSliceSpec (h, budget, ()) m Q X) :
    ∃ c s R, h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
        s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m' := by
  rcases hs with ⟨c, s, R, rfl, hlen, hm, hQ⟩
  exact ⟨c, s, R, rfl, hlen, hm, fun r s' m' hc hl hp hm' =>
    hQ (r, ()) s' m' hc hl hp hm'⟩

theorem m6ReorderSliceSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : m6ReorderSliceSpec xs m Q X) :
    m6ReorderSliceSpec xs m Q X' := by
  rcases xs with ⟨h0, budget, ⟨⟩⟩; exact h

def m6ReorderSpec : Spec [i64, i64] [i64] :=
  fun (h, _budget, ()) m Q _ =>
    ∃ c F0 ext s R,
      h = c.hdr ∧
      FullM6HdrInv c F0 ext s ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
        FullM6HdrInv c F0 ext s' →
        FullArenaPermEq s.core s'.core →
        s'.core.cur_level = s.core.cur_level →
        s'.core.fuel = s.core.fuel →
        FullExtScratchPres s s' →
        (FullM6HdrMem c ext s' ⋆ R) m' → Q (r, ()) m'

theorem m6ReorderSpec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {budget : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' →
      FullArenaPermEq s.core s'.core →
      s'.core.cur_level = s.core.cur_level →
      s'.core.fuel = s.core.fuel →
      FullExtScratchPres s s' →
      (FullM6HdrMem c ext s' ⋆ R) m' → Q (r, ()) m') :
    m6ReorderSpec (c.hdr, budget, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩

theorem m6ReorderSpec_elim {h budget : BitVec 64} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hs : m6ReorderSpec (h, budget, ()) m Q X) :
    ∃ c F0 ext s R, h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
        FullM6HdrInv c F0 ext s' →
        FullArenaPermEq s.core s'.core →
        s'.core.cur_level = s.core.cur_level →
        s'.core.fuel = s.core.fuel →
        FullExtScratchPres s s' →
        (FullM6HdrMem c ext s' ⋆ R) m' → Q (r, ()) m' := hs

theorem m6ReorderSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : m6ReorderSpec xs m Q X) :
    m6ReorderSpec xs m Q X' := by
  rcases xs with ⟨h0, budget, ⟨⟩⟩; exact h

def m6EmaSwapSpec : Spec [i64, i64, i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _old, _new, ()) _ => h = c.hdr)
    (fun _ _ _ s s' =>
      FullProbeScratchPres s s' ∧
      s'.scratch.delayed_len = s.scratch.delayed_len ∧
      s'.scratch.delayed = s.scratch.delayed)

theorem m6EmaSwapSpec_of {c : FullCfg} {oldM newM : BitVec 64} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (s' : FullState) (m' : Mem 64),
      s'.core = s.core → s'.LengthsOk c →
      (FullProbeScratchPres s s' ∧
        s'.scratch.delayed_len = s.scratch.delayed_len ∧
        s'.scratch.delayed = s.scratch.delayed) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    m6EmaSwapSpec (c.hdr, oldM, newM, ()) m Q X :=
  ⟨c, s, R, rfl, hlen, hm, fun ⟨⟩ s' m' hc hl hp hm' => hQ s' m' hc hl hp hm'⟩

theorem m6EmaSwapSpec_elim {h oldM newM : BitVec 64} {m : Mem 64}
    {Q : Post []} {X : XPost}
    (hs : m6EmaSwapSpec (h, oldM, newM, ()) m Q X) :
    ∃ c s R, h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ (s' : FullState) (m' : Mem 64),
        s'.core = s.core → s'.LengthsOk c →
        (FullProbeScratchPres s s' ∧
          s'.scratch.delayed_len = s.scratch.delayed_len ∧
          s'.scratch.delayed = s.scratch.delayed) →
        (FullMem c s' ⋆ R) m' → Q () m' := by
  rcases hs with ⟨c, s, R, rfl, hlen, hm, hQ⟩
  exact ⟨c, s, R, rfl, hlen, hm, fun s' m' hc hl hp hm' => hQ () s' m' hc hl hp hm'⟩

theorem m6EmaSwapSpec_monoX {xs : Tup Val [i64, i64, i64]} {m : Mem 64}
    {Q : Post []} {X X' : XPost} (h : m6EmaSwapSpec xs m Q X) :
    m6EmaSwapSpec xs m Q X' := by
  rcases xs with ⟨h0, oldM, newM, ⟨⟩⟩; exact h

def m6SwitchModeSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ c ext s R, h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' → M6HdrExtOk ext' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

theorem m6SwitchModeSpec_of {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' → M6HdrExtOk ext' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    m6SwitchModeSpec (c.hdr, ()) m Q X := ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩

theorem m6SwitchModeSpec_elim {h : BitVec 64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hs : m6SwitchModeSpec (h, ()) m Q X) :
    ∃ c ext s R, h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
        s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' → M6HdrExtOk ext' →
        (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m' := hs

theorem m6SwitchModeSpec_monoX {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post []} {X X' : XPost} (h : m6SwitchModeSpec xs m Q X) :
    m6SwitchModeSpec xs m Q X' := by rcases xs with ⟨h0, ⟨⟩⟩; exact h

def m6ReduceSpec : Spec [i64, .bool] [i64] := fun (h, _force, ()) m Q _ =>
  ∃ c F0 F_cur ext s R,
    h = c.hdr ∧ FullM6HdrInvW c F0 F_cur ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext' s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_level ≤ s.core.cur_level → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.cur_vars = s.core.cur_vars → s'.core.tmp = s.core.tmp →
      s'.core.tmp_len = s.core.tmp_len → s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64) →
      (r = 1#64 → 0 < s'.core.cur_level →
        s'.core.cur_level = s.core.cur_level ∧ s'.core.vals = s.core.vals ∧
        s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
        s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem m6ReduceSpec_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState} {force : Bool}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext' s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_level ≤ s.core.cur_level → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.cur_vars = s.core.cur_vars → s'.core.tmp = s.core.tmp →
      s'.core.tmp_len = s.core.tmp_len → s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64) →
      (r = 1#64 → 0 < s'.core.cur_level →
        s'.core.cur_level = s.core.cur_level ∧ s'.core.vals = s.core.vals ∧
        s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
        s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    m6ReduceSpec (c.hdr, force, ()) m Q X := ⟨c, F0, F_cur, ext, s, R, rfl, hinv, hm, hQ⟩

theorem m6ReduceSpec_elim {h : BitVec 64} {force : Bool} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hs : m6ReduceSpec (h, force, ()) m Q X) :
    ∃ c F0 F_cur ext s R,
      h = c.hdr ∧ FullM6HdrInvW c F0 F_cur ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
        FullM6HdrInvW c F0 F_cur ext' s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
        s'.core.cur_level ≤ s.core.cur_level → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        s'.core.cur_vars = s.core.cur_vars → s'.core.tmp = s.core.tmp →
        s'.core.tmp_len = s.core.tmp_len → s'.scratch.work_stk2 = s.scratch.work_stk2 →
        (r = 20#64 → F0.Unsat) → (r = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64) →
        (r = 1#64 → 0 < s'.core.cur_level →
          s'.core.cur_level = s.core.cur_level ∧ s'.core.vals = s.core.vals ∧
          s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
          s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' := hs

theorem m6ReduceSpec_monoX {xs : Tup Val [i64, .bool]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : m6ReduceSpec xs m Q X) :
    m6ReduceSpec xs m Q X' := by rcases xs with ⟨h0, force, ⟨⟩⟩; exact h

def m6RestoreBumpAnaHdrSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ c ext s R, h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ (mrk' : List (BitVec 8)) (mcl' : Nat) (sc' : FullScratch)
      (ext' : List (BitVec 64)) (m' : Mem 64),
      let s' : FullState := {
        core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
      s'.LengthsOk c → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
      (s.core.probing = 0#64 → mcl' = 0) →
      (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 → M6HdrExtOk ext' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ ext' = ext) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

theorem m6RestoreBumpAnaHdrSpec_of {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hmz : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ (mrk' : List (BitVec 8)) (mcl' : Nat) (sc' : FullScratch)
      (ext' : List (BitVec 64)) (m' : Mem 64),
      let s' : FullState := {
        core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
      s'.LengthsOk c → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
      (s.core.probing = 0#64 → mcl' = 0) →
      (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 → M6HdrExtOk ext' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ ext' = ext) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    m6RestoreBumpAnaHdrSpec (c.hdr, ()) m Q X := ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hmz, hm, hQ⟩

theorem m6RestoreBumpAnaHdrSpec_elim {h : BitVec 64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hs : m6RestoreBumpAnaHdrSpec (h, ()) m Q X) :
    ∃ c ext s R, h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (mrk' : List (BitVec 8)) (mcl' : Nat) (sc' : FullScratch)
        (ext' : List (BitVec 64)) (m' : Mem 64),
        let s' : FullState := {
          core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
        s'.LengthsOk c → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
        (s.core.probing = 0#64 → mcl' = 0) →
        (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
        FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 → M6HdrExtOk ext' →
        (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ ext' = ext) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m' := hs

theorem m6RestoreBumpAnaHdrSpec_monoX {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post []} {X X' : XPost} (h : m6RestoreBumpAnaHdrSpec xs m Q X) :
    m6RestoreBumpAnaHdrSpec xs m Q X' := by rcases xs with ⟨h0, ⟨⟩⟩; exact h

def m6AnaFailedLitHdrSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ c F0 F_cur cut ext s R, h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
    FullCutInvW c F0 F_cur cut s ∧ 0 < s.core.cur_level ∧ FullConflictOkCut F_cur cut s ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ ext' = ext) →
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem m6AnaFailedLitHdrSpec_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hcut : FullCutInvW c F0 F_cur cut s)
    (hlvl : 0 < s.core.cur_level) (hcf : FullConflictOkCut F_cur cut s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ ext' = ext) →
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    m6AnaFailedLitHdrSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, F_cur, cut, ext, s, R, rfl, hcfg, hext, hcut, hlvl, hcf, hm, hQ⟩

theorem m6AnaFailedLitHdrSpec_elim {h : BitVec 64} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hs : m6AnaFailedLitHdrSpec (h, ()) m Q X) :
    ∃ c F0 F_cur cut ext s R, h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
      FullCutInvW c F0 F_cur cut s ∧ 0 < s.core.cur_level ∧ FullConflictOkCut F_cur cut s ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ ext' = ext) →
        s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.scratch.work_stk2 = s.scratch.work_stk2 →
        (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
          s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
        (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
        (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' := hs

theorem m6AnaFailedLitHdrSpec_monoX {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : m6AnaFailedLitHdrSpec xs m Q X) :
    m6AnaFailedLitHdrSpec xs m Q X' := by rcases xs with ⟨h0, ⟨⟩⟩; exact h

def m6AnalyzeRsnHdrSpec : Spec [i64, i32, i32] [.bool] := fun (h, rsn, skip_var, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat)
    (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    FullWitnessCutInv c F0 F_cur cut s.core ∧ FullAnaMarksCov c s ∧
    s.core.tmp_len ≤ s.core.cur_vars ∧ s.core.tmp_cnt + s.core.cur_vars + 1 < 2 ^ 64 ∧
    (rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ∈ fullArenaClauseRefs s) ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' tmp' tc' tl' mcl' arena' sc' ext' m',
      let s' : FullState := { s with
        core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                              min_clr_len := mcl', arena := arena' }
        scratch := sc' }
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6ExtW2bPres ext ext') →
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s'.core → FullAnaMarksCov c s' →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      s.core.tmp_len ≤ tl' → tl' ≤ s.core.cur_vars → s.core.tmp_cnt ≤ tc' →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
        fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
        fullArenaClauseLits s' r = fullArenaClauseLits s r) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
        mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) →
      (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
        ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
          0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
          (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) →
      (∀ j, s.core.tmp_len ≤ j → j < tl' → let l := (tmp'[j]?.getD 0#32).toNat
        l ∈ fullRsnLits s rsn ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
        s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8) →
      (∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
        (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2) →
      (tc' - s.core.tmp_cnt = ((List.range s.core.cur_vars).filter fun w =>
        decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
        decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length) →
      (sc'.res_sz = s.scratch.res_sz + BitVec.ofNat 64 ((List.range s.core.cur_vars).filter fun w =>
        decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length) →
      (ok = true → rsn ≠ 0xFFFFFFFF#32 ∧
        sc'.ant_sz = s.scratch.ant_sz + BitVec.ofNat 64 ((fullRsnLits s rsn).countP fun l =>
          decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)) ∧
        ∀ l ∈ fullRsnLits s rsn, l / 2 < s.core.cur_vars ∧ (l / 2 ≠ skip_var.toNat →
          (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
          (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
            (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
              (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
              ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (ok, ()) m'

theorem m6AnalyzeRsnHdrSpec_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {rsn skip_var : BitVec 32} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hcut : FullWitnessCutInv c F0 F_cur cut s.core) (hcov : FullAnaMarksCov c s)
    (htl : s.core.tmp_len ≤ s.core.cur_vars) (htc : s.core.tmp_cnt + s.core.cur_vars + 1 < 2 ^ 64)
    (href : rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
      rsn.toNat ∈ fullArenaClauseRefs s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ (ok : Bool) mrk' tmp' tc' tl' mcl' arena' sc' ext' m',
      let s' : FullState := { s with
        core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                              min_clr_len := mcl', arena := arena' }
        scratch := sc' }
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6ExtW2bPres ext ext') →
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s'.core → FullAnaMarksCov c s' →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      s.core.tmp_len ≤ tl' → tl' ≤ s.core.cur_vars → s.core.tmp_cnt ≤ tc' →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
        fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
        fullArenaClauseLits s' r = fullArenaClauseLits s r) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
        mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) →
      (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
        ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
          0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
          (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) →
      (∀ j, s.core.tmp_len ≤ j → j < tl' → let l := (tmp'[j]?.getD 0#32).toNat
        l ∈ fullRsnLits s rsn ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
        s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8) →
      (∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
        (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2) →
      (tc' - s.core.tmp_cnt = ((List.range s.core.cur_vars).filter fun w =>
        decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
        decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length) →
      (sc'.res_sz = s.scratch.res_sz + BitVec.ofNat 64 ((List.range s.core.cur_vars).filter fun w =>
        decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length) →
      (ok = true → rsn ≠ 0xFFFFFFFF#32 ∧
        sc'.ant_sz = s.scratch.ant_sz + BitVec.ofNat 64 ((fullRsnLits s rsn).countP fun l =>
          decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)) ∧
        ∀ l ∈ fullRsnLits s rsn, l / 2 < s.core.cur_vars ∧ (l / 2 ≠ skip_var.toNat →
          (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
          (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
            (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
              (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
              ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (ok, ()) m') :
    m6AnalyzeRsnHdrSpec (c.hdr, rsn, skip_var, ()) m Q X :=
  ⟨c, F0, F_cur, cut, ext, s, R, rfl, hcfg, hext, hlen, hcut, hcov, htl, htc, href, hm, hQ⟩

theorem m6AnalyzeRsnHdrSpec_elim {h : BitVec 64} {rsn skip_var : BitVec 32} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost} (hs : m6AnalyzeRsnHdrSpec (h, rsn, skip_var, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat)
      (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      FullWitnessCutInv c F0 F_cur cut s.core ∧ FullAnaMarksCov c s ∧
      s.core.tmp_len ≤ s.core.cur_vars ∧ s.core.tmp_cnt + s.core.cur_vars + 1 < 2 ^ 64 ∧
      (rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ∈ fullArenaClauseRefs s) ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (ok : Bool) mrk' tmp' tc' tl' mcl' arena' sc' ext' m',
        let s' : FullState := { s with
          core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                min_clr_len := mcl', arena := arena' }
          scratch := sc' }
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6ExtW2bPres ext ext') →
        s'.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s'.core → FullAnaMarksCov c s' →
        FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
        s.core.tmp_len ≤ tl' → tl' ≤ s.core.cur_vars → s.core.tmp_cnt ≤ tc' →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
          fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
          fullArenaClauseLits s' r = fullArenaClauseLits s r) →
        (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
          mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) →
        (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) →
        (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
          ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
            0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
            (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) →
        (∀ j, s.core.tmp_len ≤ j → j < tl' → let l := (tmp'[j]?.getD 0#32).toNat
          l ∈ fullRsnLits s rsn ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
          s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
          (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8) →
        (∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
          (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2) →
        (tc' - s.core.tmp_cnt = ((List.range s.core.cur_vars).filter fun w =>
          decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
          decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length) →
        (sc'.res_sz = s.scratch.res_sz + BitVec.ofNat 64
          ((List.range s.core.cur_vars).filter fun w =>
            decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length) →
        (ok = true → rsn ≠ 0xFFFFFFFF#32 ∧
          sc'.ant_sz = s.scratch.ant_sz + BitVec.ofNat 64 ((fullRsnLits s rsn).countP fun l =>
            decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
              (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)) ∧
          ∀ l ∈ fullRsnLits s rsn, l / 2 < s.core.cur_vars ∧ (l / 2 ≠ skip_var.toNat →
            (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
            (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
              (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
              (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
                (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
                ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (ok, ()) m' := hs

theorem m6AnalyzeRsnHdrSpec_monoX {xs : Tup Val [i64, i32, i32]} {m : Mem 64}
    {Q : Post [.bool]} {X X' : XPost} (h : m6AnalyzeRsnHdrSpec xs m Q X) :
    m6AnalyzeRsnHdrSpec xs m Q X' := by rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

def m6Deduce1uipHdrSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ c F0 F_cur cut ext s R, h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
    FullCutInvW c F0 F_cur cut s ∧ 0 < s.core.cur_level ∧ FullConflictOkCut F_cur cut s ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
        (List.map (fun x => x.toNat / 2) (List.take s'.core.tmp_len s'.core.tmp)).Nodup ∧
        (∀ k, k < s'.core.tmp_len → let l := (s'.core.tmp[k]?.getD 0#32).toNat
          l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 255#8) ∧
        (∀ k, 1 ≤ k → k < s'.core.tmp_len →
          let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
          0 < lv ∧ lv < s'.core.cur_level) ∧
        (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s'.core.cur_level ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause (List.map BitVec.toNat (List.take s'.core.tmp_len s'.core.tmp)))) →
      (r = 2#64 → ∃ cut', cut' ≤ s'.core.trail_end ∧ FullCutInvW c F0 F_cur cut' s' ∧
        s'.core.cur_level = s.core.cur_level ∧ FullConflictOkCut F_cur cut' s') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem m6Deduce1uipHdrSpec_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hcut : FullCutInvW c F0 F_cur cut s)
    (hlvl : 0 < s.core.cur_level) (hcf : FullConflictOkCut F_cur cut s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
        (List.map (fun x => x.toNat / 2) (List.take s'.core.tmp_len s'.core.tmp)).Nodup ∧
        (∀ k, k < s'.core.tmp_len → let l := (s'.core.tmp[k]?.getD 0#32).toNat
          l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 255#8) ∧
        (∀ k, 1 ≤ k → k < s'.core.tmp_len →
          let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
          0 < lv ∧ lv < s'.core.cur_level) ∧
        (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s'.core.cur_level ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause (List.map BitVec.toNat (List.take s'.core.tmp_len s'.core.tmp)))) →
      (r = 2#64 → ∃ cut', cut' ≤ s'.core.trail_end ∧ FullCutInvW c F0 F_cur cut' s' ∧
        s'.core.cur_level = s.core.cur_level ∧ FullConflictOkCut F_cur cut' s') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    m6Deduce1uipHdrSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, F_cur, cut, ext, s, R, rfl, hcfg, hext, hcut, hlvl, hcf, hm, hQ⟩

theorem m6Deduce1uipHdrSpec_elim {h : BitVec 64} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hs : m6Deduce1uipHdrSpec (h, ()) m Q X) :
    ∃ c F0 F_cur cut ext s R, h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
      FullCutInvW c F0 F_cur cut s ∧ 0 < s.core.cur_level ∧ FullConflictOkCut F_cur cut s ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
        M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.scratch.work_stk2 = s.scratch.work_stk2 →
        (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
          s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
        (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
        (r = 1#64 → FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
          1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
          (List.map (fun x => x.toNat / 2) (List.take s'.core.tmp_len s'.core.tmp)).Nodup ∧
          (∀ k, k < s'.core.tmp_len → let l := (s'.core.tmp[k]?.getD 0#32).toNat
            l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 255#8) ∧
          (∀ k, 1 ≤ k → k < s'.core.tmp_len →
            let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
            0 < lv ∧ lv < s'.core.cur_level) ∧
          (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
            s'.core.cur_level ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause (List.map BitVec.toNat (List.take s'.core.tmp_len s'.core.tmp)))) →
        (r = 2#64 → ∃ cut', cut' ≤ s'.core.trail_end ∧ FullCutInvW c F0 F_cur cut' s' ∧
          s'.core.cur_level = s.core.cur_level ∧ FullConflictOkCut F_cur cut' s') →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' := hs

theorem m6Deduce1uipHdrSpec_monoX {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : m6Deduce1uipHdrSpec xs m Q X) :
    m6Deduce1uipHdrSpec xs m Q X' := by rcases xs with ⟨h0, ⟨⟩⟩; exact h

/-! ### Private Helpers -/

private theorem m6o_arenaPermEq_refl (k : FullCoreState) : FullArenaPermEq k k :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩

private theorem fullSparseInv_of_extScratch {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (hsp : FullSparseInv c F0 s) (hlen : s'.LengthsOk c) (hcore : s'.core = s.core)
    (hpres : FullExtScratchPres s s') : FullSparseInv c F0 s' :=
  hsp.of_safetySlice hlen hcore hpres

private def m6oUpdGu (s : FullState) (gu' : List (BitVec 32)) : FullState :=
  { s with scratch := { s.scratch with glue_used := gu' } }

private def M6oProbeStep (s0 s : FullState) : Prop :=
  FullProbeScratchPres s0 s ∧
  s.scratch.delayed_len = s0.scratch.delayed_len ∧
  s.scratch.delayed = s0.scratch.delayed

private theorem m6oProbeStep_refl (s : FullState) : M6oProbeStep s s :=
  ⟨⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

private theorem m6oProbeStep_trans {s0 s1 s2 : FullState}
    (h1 : M6oProbeStep s0 s1) (h2 : M6oProbeStep s1 s2) : M6oProbeStep s0 s2 :=
  ⟨⟨⟨h2.1.1.1.trans h1.1.1.1, h2.1.1.2.trans h1.1.1.2⟩,
    h2.1.2.1.trans h1.1.2.1, h2.1.2.2.1.trans h1.1.2.2.1,
    h2.1.2.2.2.1.trans h1.1.2.2.2.1, h2.1.2.2.2.2.1.trans h1.1.2.2.2.2.1,
    h2.1.2.2.2.2.2.1.trans h1.1.2.2.2.2.2.1, h2.1.2.2.2.2.2.2.1.trans h1.1.2.2.2.2.2.2.1,
    h2.1.2.2.2.2.2.2.2.trans h1.1.2.2.2.2.2.2.2⟩,
    h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

private theorem m6oUpdGu_step {c : FullCfg} {s s0 : FullState} (hs : s.LengthsOk c)
    (hcore : s.core = s0.core) (hp : M6oProbeStep s0 s)
    {gu' : List (BitVec 32)} (hgu : gu'.length = s.scratch.glue_used.length) :
    (m6oUpdGu s gu').LengthsOk c ∧ (m6oUpdGu s gu').core = s0.core ∧
      M6oProbeStep s0 (m6oUpdGu s gu') := by
  have hst := fullState_upd_glue_used_step hs hgu
  exact ⟨hst.1, hst.2.1.trans hcore, m6oProbeStep_trans hp hst.2.2⟩

private theorem m6o_wp_load_gu_bv {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} {a : Arg Val i64} {k : Val i32 → Expr Val Cont rs}
    (ha : a.val = c.pGlueUsed + i * 4)
    (hi : i.toNat < 64) (hm : (FullMem c s ⋆ R) m) (hgu : s.scratch.glue_used.length = 64)
    (hk : wp Γ Q X (k (s.scratch.glue_used[i.toNat]'(by rw [hgu]; exact hi))) m) :
    wp Γ Q X (.load i32 a k) m :=
  head_wp_load ha (c0_load_full_glue_used (by rw [hgu]; exact hi) hm) hk

private theorem m6o_wp_load_gu_imm {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {n : Nat} {a : Arg Val i64} {k : Val i32 → Expr Val Cont rs}
    (ha : a.val = c.pGlueUsed + BitVec.ofNat (OfNat.ofNat 64) n * 4)
    (hn : n < 64) (hgu : s.scratch.glue_used.length = 64) (hm : (FullMem c s ⋆ R) m)
    (hk : wp Γ Q X (k (s.scratch.glue_used[n]'(by rw [hgu]; exact hn))) m) :
    wp Γ Q X (.load i32 a k) m := by
  have hi : (BitVec.ofNat 64 n).toNat < 64 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hn
  refine m6o_wp_load_gu_bv ha hi hm hgu ?_
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)] using hk

private theorem m6o_wp_store_gu_bv {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {s0 : FullState} {gu : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} {a : Arg Val i64} {v : Arg Val i32} {vv : BitVec 32} {k : Expr Val Cont rs}
    (hv : v.val = vv) (ha : a.val = c.pGlueUsed + i * 4)
    (hi : i.toNat < 64) (hgu : gu.length = 64) (hm : (FullMem c (m6oUpdGu s0 gu) ⋆ R) m)
    (hk : ∀ gu' m', gu'.length = 64 → (FullMem c (m6oUpdGu s0 gu') ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store v a k) m := by
  have hst := c0_store_full_glue_used vv (show i.toNat < (m6oUpdGu s0 gu).scratch.glue_used.length
    from by change i.toNat < gu.length; rw [hgu]; exact hi) hm
  exact @head_wp_store Γ rs Q X m i32 v a vv _ k (FullMem c (m6oUpdGu s0 (gu.set i.toNat vv))) R
    hv ha (by simpa [m6oUpdGu] using hst) fun _ hm' => hk _ _ (by simpa using hgu) hm'

private theorem m6o_wp_store_gu_imm {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {s0 : FullState} {gu : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {n : Nat} {a : Arg Val i64} {v : Arg Val i32} {vv : BitVec 32} {k : Expr Val Cont rs}
    (hv : v.val = vv) (ha : a.val = c.pGlueUsed + BitVec.ofNat (OfNat.ofNat 64) n * 4)
    (hn : n < 64) (hgu : gu.length = 64) (hm : (FullMem c (m6oUpdGu s0 gu) ⋆ R) m)
    (hk : ∀ gu' m', gu'.length = 64 → (FullMem c (m6oUpdGu s0 gu') ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store v a k) m :=
  m6o_wp_store_gu_bv hv ha (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hn)
    hgu hm hk

private theorem m6o_gu_step {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {s0 : FullState} {gu : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {n : Nat} {a : Arg Val i64} {v : Arg Val i32} {vv : BitVec 32} {k : Expr Val Cont rs}
    (hm : (FullMem c (m6oUpdGu s0 gu) ⋆ R) m) (hgu : gu.length = 64)
    (hv : v.val = vv) (ha : a.val = c.pGlueUsed + BitVec.ofNat (OfNat.ofNat 64) n * 4)
    (hn : n < 64)
    (hk : ∀ gu' m', gu'.length = 64 → (FullMem c (m6oUpdGu s0 gu') ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store v a k) m := m6o_wp_store_gu_imm hv ha hn hgu hm hk

private theorem m6o_gu_finish {c : FullCfg} {s : FullState} {gu : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hgu0 : s.scratch.glue_used.length = 64)
    (hm : (FullMem c (m6oUpdGu s gu) ⋆ R) m) (hgu : gu.length = 64) :
    (m6oUpdGu s gu).LengthsOk c ∧ (m6oUpdGu s gu).core = s.core ∧
      M6oProbeStep s (m6oUpdGu s gu) ∧ (FullMem c (m6oUpdGu s gu) ⋆ R) m :=
  let h := m6oUpdGu_step hlen rfl (m6oProbeStep_refl s) (hgu.trans hgu0.symm)
  ⟨h.1, h.2.1, h.2.2, hm⟩

private theorem m6oProbeStep_upd_ema {c : FullCfg} {s s0 : FullState}
    (hlen : s.LengthsOk c) (hcore : s.core = s0.core) (hp : M6oProbeStep s0 s)
    (efb efe esb ese : BitVec 64) :
    let s' : FullState := { core := s.core, scratch := { s.scratch with
      ema_fast_biased := efb, ema_fast_exp := efe,
      ema_slow_biased := esb, ema_slow_exp := ese } }
    s'.LengthsOk c ∧ s'.core = s0.core ∧ M6oProbeStep s0 s' :=
  let hst := fullState_upd_ema_step hlen efb efe esb ese
  ⟨hst.1, hst.2.1.trans hcore, m6oProbeStep_trans hp hst.2.2⟩

private theorem m6oProbeStep_upd_ema_pack {c : FullCfg} {s s0 : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hcore : s.core = s0.core) (hp : M6oProbeStep s0 s)
    {efb efe esb ese : BitVec 64}
    (hm : (FullMem c { core := s.core, scratch := { s.scratch with
      ema_fast_biased := efb, ema_fast_exp := efe,
      ema_slow_biased := esb, ema_slow_exp := ese } } ⋆ R) m) :
    let s' : FullState := { core := s.core, scratch := { s.scratch with
      ema_fast_biased := efb, ema_fast_exp := efe,
      ema_slow_biased := esb, ema_slow_exp := ese } }
    s'.LengthsOk c ∧ s'.core = s0.core ∧ M6oProbeStep s0 s' ∧ (FullMem c s' ⋆ R) m :=
  let hst := m6oProbeStep_upd_ema hlen hcore hp efb efe esb ese
  ⟨hst.1, hst.2.1, hst.2.2, hm⟩

/-! ### 13 Inner Forwarding Shims -/

private theorem m6o_fwd0 {Q : Post []} : (fun (_ : Tup Val []) m' => Q () m') = Q :=
  funext fun r => by cases r; rfl

private theorem m6o_fwd1 {t : Ty} {Q : Post [t]} :
    (fun (r : Tup Val [t]) m' => Q (r.fst, ()) m') = Q := funext fun ⟨_, ⟨⟩⟩ => rfl

theorem full_wstack_defrag_wp (Γ : Env) (hSub : ∀ a m Q X, fullWstackDefragSpec a m Q X →
    Γ "full_wstack_defrag_m6" [i64] [] a m Q X) : ∀ a m Q X, fullWstackDefragSpec a m Q X →
    Func.wp Γ FullM6Orch.full_wstack_defrag_body a m Q X := by
  intro ⟨_, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_wstack_defrag_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd0]

theorem full_watch_push_wp (Γ : Env) (hSub : ∀ a m Q X, fullWatchPushSpec a m Q X →
    Γ "full_watch_push_m6" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullWatchPushSpec a m Q X → Func.wp Γ FullM6Orch.full_watch_push_body a m Q X := by
  intro ⟨_, _, _, _, _, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_watch_push_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd1]

theorem full_rescale_wp (Γ : Env) (hSub : ∀ a m Q X, fullRescaleSpec a m Q X →
    Γ "full_rescale_m6" [i64] [] a m Q X) : ∀ a m Q X, fullRescaleSpec a m Q X →
    Func.wp Γ FullM6Orch.full_rescale_body a m Q X := by
  intro ⟨_, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_rescale_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd0]

theorem full_parse_body_wp (Γ : Env) (hSub : ∀ a m Q X, fullParseBodySpec a m Q X →
    Γ "full_parse_body_m6" [i64, i64] [i64] a m Q X) : ∀ a m Q X, fullParseBodySpec a m Q X →
    Func.wp Γ FullM6Orch.full_parse_body_body a m Q X := by
  intro ⟨_, _, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_parse_body_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd1]

theorem full_lit_rank_wp (Γ : Env) (hSub : ∀ a m Q X, fullLitRankSpec a m Q X →
    Γ "full_lit_rank_m6" [i64, i64, i32] [i64] a m Q X) : ∀ a m Q X, fullLitRankSpec a m Q X →
    Func.wp Γ FullM6Orch.full_lit_rank_body a m Q X := by
  intro ⟨_, _, _, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_lit_rank_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd1]

theorem full_sweep_bins_wp (Γ : Env) (hSub : ∀ a m Q X, fullSweepBinsSpec a m Q X →
    Γ "full_sweep_bins_m6cf" [i64] [] a m Q X) : ∀ a m Q X, fullSweepBinsSpec a m Q X →
    Func.wp Γ FullM6Orch.full_sweep_bins_body a m Q X := by
  intro ⟨_, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_sweep_bins_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd0]

theorem full_rewatch_arena_wp (Γ : Env) (hSub : ∀ a m Q X, fullRewatchArenaSpec a m Q X →
    Γ "full_rewatch_arena_m6" [i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullRewatchArenaSpec a m Q X →
      Func.wp Γ FullM6Orch.full_rewatch_arena_body a m Q X := by
  intro ⟨_, _, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_rewatch_arena_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd1]

theorem full_arena_sweep_wp (Γ : Env) (hSub : ∀ a m Q X, fullArenaSweepSpec a m Q X →
    Γ "full_arena_sweep_m6" [i64] [i64] a m Q X) : ∀ a m Q X, fullArenaSweepSpec a m Q X →
    Func.wp Γ FullM6Orch.full_arena_sweep_body a m Q X := by
  intro ⟨_, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_arena_sweep_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd1]

theorem full_mark_reasons_wp (Γ : Env) (hSub : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
    Γ "full_mark_reasons_m6" [i64, .bool] [] a m Q X) : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
    Func.wp Γ FullM6Orch.full_mark_reasons_body a m Q X := by
  intro ⟨_, _, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_mark_reasons_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd0]

theorem full_min_shrink_wp (Γ : Env) (hSub : ∀ a m Q X, fullMinShrinkSpec a m Q X →
    Γ "full_min_shrink_m6" [i64] [] a m Q X) : ∀ a m Q X, fullMinShrinkSpec a m Q X →
    Func.wp Γ FullM6Orch.full_min_shrink_body a m Q X := by
  intro ⟨_, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_min_shrink_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd0]

theorem full_deduce_1uip_wp (Γ : Env) (hSub : ∀ a m Q X, fullDeduce1uipSpec a m Q X →
    Γ "full_deduce_1uip_m6" [i64] [i64] a m Q X) : ∀ a m Q X, fullDeduce1uipSpec a m Q X →
    Func.wp Γ FullM6Orch.full_deduce_1uip_body a m Q X := by
  intro ⟨_, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_deduce_1uip_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd1]

theorem full_walk_wp (Γ : Env) (hSub : ∀ a m Q X, fullWarmupSpec a m Q X →
    Γ "full_walk_m6" [i64] [] a m Q X) : ∀ a m Q X, fullWarmupSpec a m Q X →
    Func.wp Γ FullM6Orch.full_walk_body a m Q X := by
  intro ⟨_, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_walk_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd0]

theorem full_sweep_dense_m6_wp (Γ : Env)
    (hSub : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense_m5" [i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      Func.wp Γ full_sweep_dense_m6_body a m Q X := by
  intro ⟨_, _, _, ⟨⟩⟩ _ _ _ hs; unfold Func.wp full_sweep_dense_m6_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd1]

/-! ### `full_reorder_m6` (Stable Guard -> `full_reorder_queue_m7`) -/

theorem full_reorder_m6_slice_wp (Γ : Env)
    (hQueue : ∀ a m Q X, FullM4Ternary.fullReorderQueueSpec a m Q X →
      Γ "full_reorder_queue_m7" [i64] [i64] a m Q X) :
    ∀ a m Q X, m6ReorderSliceSpec a m Q X →
      Func.wp Γ full_reorder_m6_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m Q X hs
  rcases m6ReorderSliceSpec_elim hs with ⟨c, s, R, rfl, hlen, hm, hQ⟩
  unfold Func.wp full_reorder_m6_body
  c0_hsteps
  · exact hQ 0#64 s m rfl hlen ⟨rfl, rfl⟩ hm
  · c0_call hQueue
    refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
    rintro ⟨r, ⟨⟩⟩ s1 m1 hc1 hlen1 hpres1 hm1
    have hce1 : s1.core = s.core := fullCoreState_agrees_with_scratch hc1
    c0_hsteps
    exact hQ r s1 m1 hce1 hlen1 hpres1 hm1

theorem full_reorder_m6_wp (Γ : Env)
    (hQueue : ∀ a m Q X, FullM4Ternary.fullReorderQueueSpec a m Q X →
      Γ "full_reorder_queue_m7" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullM4.m4ReorderSpec a m Q X →
      Func.wp Γ full_reorder_m6_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
  refine full_reorder_m6_slice_wp Γ hQueue (c.hdr, budget, ()) m Q X ?_
  refine m6ReorderSliceSpec_of hsp.lengths hm ?_
  intro r s1 m1 hce1 hlen1 hpres1 hm1
  have hsp1 := fullSparseInv_of_extScratch hsp hlen1 hce1 hpres1
  exact hQ r s1 m1 hsp1 (hce1 ▸ m6o_arenaPermEq_refl s.core) (by rw [hce1]) (by rw [hce1]) hm1

theorem full_reorder_m6_hdr_wp (Γ : Env)
    (hQueue : ∀ a m Q X, FullM4Ternary.fullReorderQueueSpec a m Q X →
      Γ "full_reorder_queue_m7" [i64] [i64] a m Q X) :
    ∀ a m Q X, m6ReorderSpec a m Q X →
      Func.wp Γ full_reorder_m6_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m Q X hs
  rcases m6ReorderSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩
  refine wp_m6Hdr_focus_frame hm fun hm' => ?_
  refine full_reorder_m6_slice_wp Γ hQueue (c.hdr, budget, ()) m Q X ?_
  refine m6ReorderSliceSpec_of hinv.sparse.lengths hm' ?_
  intro r s1 m1 hce1 hlen1 hpres1 hm1
  have hinv1 := fullM6HdrInv_of_core_eq hinv hlen1 hce1 hpres1
  have hm1' := fullM6HdrMem_unfocus hm1
  exact hQ r s1 m1 hinv1 (hce1 ▸ m6o_arenaPermEq_refl s.core) (by rw [hce1]) (by rw [hce1])
    hpres1 hm1'

/-! ### `full_ema_swap_m6` (`glue_used[36..55]`) -/

theorem full_ema_swap_m6_wp (Γ : Env) :
    ∀ a m Q X, m6EmaSwapSpec a m Q X →
      Func.wp Γ full_ema_swap_m6_body a m Q X := by
  rintro ⟨h, oldM, newM, ⟨⟩⟩ m Q X hs
  rcases m6EmaSwapSpec_elim hs with ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hgu := hlen.scratch_ok.glue_used_len
  unfold Func.wp full_ema_swap_m6_body
  c0_hsteps_nogrp
  apply m6o_wp_load_gu_imm rfl (by decide) hgu hm; c0_hsteps_nogrp
  apply m6o_wp_load_gu_imm rfl (by decide) hgu hm; c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState) (fun st m' =>
    st.LengthsOk c ∧ st.core = s.core ∧ M6oProbeStep s st ∧ (FullMem c st ⋆ R) m') ?_ ?_
  · rintro J s1 m1 ⟨hlen1, hce1, hpres1, hm1⟩
    have hgu1 := hlen1.scratch_ok.glue_used_len
    c0_hsteps_nogrp
    refine wp_join_state1 (α := FullState × BitVec 64) (fun p => p.2) (fun p m' =>
      p.1.LengthsOk c ∧ p.1.core = s.core ∧ M6oProbeStep s p.1 ∧
      (p.2 = 40#64 ∨ p.2 = 48#64) ∧ (FullMem c p.1 ⋆ R) m') ?_ ?_
    · rintro J2 ⟨s2, ob⟩ m2 ⟨hlen2, hce2, hpres2, hob, hm2⟩
      have hgu2 := hlen2.scratch_ok.glue_used_len
      have hob_hi : ∀ k : Nat, k ≤ 7 → (ob + BitVec.ofNat 64 k).toNat < 64 := by
        intro k hk
        rcases hob with rfl | rfl <;> (simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      have hob0 : ob.toNat < 64 := by rcases hob with rfl | rfl <;> decide
      change (FullMem c (m6oUpdGu s2 s2.scratch.glue_used) ⋆ R) m2 at hm2
      c0_hsteps_nogrp
      apply m6o_wp_store_gu_bv rfl rfl hob0 hgu2 hm2
      intro gu1 m1 hgu1 hm1; c0_hsteps_nogrp
      apply m6o_wp_store_gu_bv rfl rfl (hob_hi 1 (by omega)) hgu1 hm1
      intro gu2 m2 hgu2 hm2; c0_hsteps_nogrp
      apply m6o_wp_store_gu_bv rfl rfl (hob_hi 2 (by omega)) hgu2 hm2
      intro gu3 m3 hgu3 hm3; c0_hsteps_nogrp
      apply m6o_wp_store_gu_bv rfl rfl (hob_hi 3 (by omega)) hgu3 hm3
      intro gu4 m4 hgu4 hm4; c0_hsteps_nogrp
      apply m6o_wp_store_gu_bv rfl rfl (hob_hi 4 (by omega)) hgu4 hm4
      intro gu5 m5 hgu5 hm5; c0_hsteps_nogrp
      apply m6o_wp_store_gu_bv rfl rfl (hob_hi 5 (by omega)) hgu5 hm5
      intro gu6 m6 hgu6 hm6; c0_hsteps_nogrp
      apply m6o_wp_store_gu_bv rfl rfl (hob_hi 6 (by omega)) hgu6 hm6
      intro gu7 m7 hgu7 hm7; c0_hsteps_nogrp
      apply m6o_wp_store_gu_bv rfl rfl (hob_hi 7 (by omega)) hgu7 hm7
      intro gu8 m8 hgu8 hm8; c0_hsteps_nogrp
      have ⟨hlen28, hce28, hp28⟩ :=
        m6oUpdGu_step hlen2 hce2 hpres2 (hgu8.trans hlen2.scratch_ok.glue_used_len.symm)
      generalize m6oUpdGu s2 gu8 = s28 at *
      have hgu28 := hlen28.scratch_ok.glue_used_len
      apply m6o_wp_load_gu_imm rfl (by decide) hgu28 hm8; c0_hsteps_nogrp
      apply m6o_wp_load_gu_imm rfl (by decide) hgu28 hm8; c0_hsteps_nogrp
      refine wp_join_state1 (α := FullState × BitVec 64) (fun p => p.2) (fun p m' =>
        p.1.LengthsOk c ∧ p.1.core = s.core ∧ M6oProbeStep s p.1 ∧
        (p.2 = 40#64 ∨ p.2 = 48#64) ∧ (FullMem c p.1 ⋆ R) m') ?_ ?_
      · rintro J3 ⟨s3b, nb⟩ m3b ⟨hlen3, hce3, hp3, hnb, hm3b⟩
        dsimp only at hlen3 hce3 hp3 hnb hm3b
        have hgu3b := hlen3.scratch_ok.glue_used_len
        have hnb_hi : ∀ k : Nat, k ≤ 7 → (nb + BitVec.ofNat 64 k).toNat < 64 := by
          intro k hk
          rcases hnb with rfl | rfl <;> (simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
        have hnb0 : nb.toNat < 64 := by rcases hnb with rfl | rfl <;> decide
        c0_hsteps_nogrp
        refine wp_join_state1 (α := FullState × BitVec 64) (fun p => p.2) (fun p m' =>
          p.1.LengthsOk c ∧ p.1.core = s.core ∧ M6oProbeStep s p.1 ∧
          (FullMem c p.1 ⋆ R) m') ?_ ?_
        · rintro J4 ⟨s4, msk⟩ m4 ⟨hlen4, hce4, hp4, hm4⟩
          dsimp only at hlen4 hce4 hp4 hm4
          have hgu4 := hlen4.scratch_ok.glue_used_len
          change (FullMem c (m6oUpdGu s4 s4.scratch.glue_used) ⋆ R) m4 at hm4
          c0_hsteps_nogrp
          apply m6o_wp_store_gu_imm rfl rfl (by decide) hgu4 hm4
          intro gu41 m41 hgu41 hm41; c0_hsteps_nogrp
          apply m6o_wp_store_gu_imm rfl rfl (by decide) hgu41 hm41
          intro gu42 m42 hgu42 hm42; c0_hsteps_nogrp
          have ⟨hlen5, hce5, hp5⟩ := m6oUpdGu_step hlen4 hce4 hp4 (hgu42.trans hgu4.symm)
          exact hQ _ m42 hce5 hlen5 hp5 hm42
        · intro J4 hJ4
          c0_hsteps_nogrp
          · apply m6o_wp_load_gu_bv rfl (hnb_hi 2 (by omega)) hm hgu3b; c0_hsteps_nogrp
            apply m6o_wp_load_gu_bv rfl (hnb_hi 3 (by omega)) hm hgu3b; c0_hsteps_nogrp
            apply m6o_wp_load_gu_bv rfl (hnb_hi 4 (by omega)) hm hgu3b; c0_hsteps_nogrp
            apply m6o_wp_load_gu_bv rfl (hnb_hi 5 (by omega)) hm hgu3b; c0_hsteps_nogrp
            apply m6o_wp_load_gu_bv rfl (hnb_hi 6 (by omega)) hm hgu3b; c0_hsteps_nogrp
            apply m6o_wp_load_gu_bv rfl (hnb_hi 7 (by omega)) hm hgu3b; c0_hsteps_nogrp
            dsimp only at hm
            exact hJ4 (_, _) _ (m6oProbeStep_upd_ema_pack hlen3 hce3 hp3 hm)
          · dsimp only at hm
            exact hJ4 (_, _) _ (m6oProbeStep_upd_ema_pack hlen3 hce3 hp3 hm)
      · intro J3 hJ3
        c0_hsteps_nogrp
        · exact hJ3 (s28, 40#64) m8 ⟨hlen28, hce28, hp28, Or.inl rfl, hm8⟩
        · exact hJ3 (s28, 48#64) m8 ⟨hlen28, hce28, hp28, Or.inr rfl, hm8⟩
    · intro J2 hJ2
      c0_hsteps_nogrp
      · exact hJ2 (s1, 40#64) m1 ⟨hlen1, hce1, hpres1, Or.inl rfl, hm1⟩
      · exact hJ2 (s1, 48#64) m1 ⟨hlen1, hce1, hpres1, Or.inr rfl, hm1⟩
  · intro J hJ; c0_hsteps_nogrp
    · change (FullMem c (m6oUpdGu s s.scratch.glue_used) ⋆ R) m at hm
      repeat (apply m6o_gu_step (by assumption) (by assumption) rfl rfl (by decide)
              intro _ _ _ _; c0_hsteps_nogrp)
      exact hJ _ _ (m6o_gu_finish hlen hgu (by assumption) (by assumption))
    · exact hJ s m ⟨hlen, rfl, m6oProbeStep_refl s, hm⟩

/-! ### Additional Local Helpers (`switch_mode`, `reduce`, `TFlat` Lifting) -/

private theorem m6oProbePres_refl (s : FullState) : FullProbeScratchPres s s :=
  (m6oProbeStep_refl s).1

private theorem m6oProbePres_trans {s0 s1 s2 : FullState}
    (h1 : FullProbeScratchPres s0 s1) (h2 : FullProbeScratchPres s1 s2) :
    FullProbeScratchPres s0 s2 :=
  ⟨⟨h2.1.1.trans h1.1.1, h2.1.2.trans h1.1.2⟩,
    h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
    h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
    h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2.2⟩

private theorem m6o_wp_let_ult64 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {hm : Ty.bool = Ty.mask i64} {a b : Arg Val i64}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult i64 .bool hm) (a, b, ())) k) m =
      wp Γ Q X (k (BitVec.ult a.val b.val, ())) m := by
  have hc := @wp_let_cmp_eq Γ rs Q X m .ult i64 .bool hm (a, b, ()) k
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, liftCmp,
    evalBits_ult_eq, cast_eq] using hc

private theorem m6o_call_emaSwap {Γ : Env} {ret : List Ty}
    {oldM newM : BitVec 64} {args : Tup (Arg Val) [i64, i64, i64]}
    {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, oldM, newM, ()))
    (hΓ : ∀ a m' Q' X', m6EmaSwapSpec a m' Q' X' →
      Γ "full_ema_swap_m6" [i64, i64, i64] [] a m' Q' X')
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ s' m', s'.core = s.core → s'.LengthsOk c →
      FullProbeScratchPres s s' → (FullM6HdrMem c ext s' ⋆ R) m' →
      wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_ema_swap_m6" (as := [i64, i64, i64]) (bs := []) args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  exact hΓ _ _ _ X (fullM6Hdr_frame_safetySlice hcfg hext hlen (by exact rfl) hm
    (fun () s' m' hs' hc hp _ _ hm' =>
      hk s' m' (fullCoreState_agrees_with_scratch hc) hs' hp.1 hm'))

private theorem m6o_call_heapDown {Γ : Env} {ret : List Ty}
    {idx : BitVec 32} {args : Tup (Arg Val) [i64, i32]}
    {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, idx, ()))
    (hΓ : ∀ a m' Q' X', Full.fullHeapDownSpec a m' Q' X' →
      Γ "full_heap_down" [i64, i32] [] a m' Q' X')
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ s' m', s'.core = s.core → s'.LengthsOk c →
      s'.scratch.heap_len = s.scratch.heap_len → FullProbeScratchPres s s' →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_heap_down" (as := [i64, i32]) (bs := []) args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  exact hΓ _ _ _ X (fullM6Hdr_frame_safetySlice hcfg hext hlen (by exact rfl) hm
    (fun () s' m' hs' hc hp _ _ hm' =>
      hk s' m' (fullCoreState_agrees_with_scratch hc) hs' hp.1 hp.2 hm'))

private theorem m6o_arenaVarsNodup_perm {s s' : FullState}
    (hap : FullArenaPermEq s.core s'.core) (hnd : FullArenaVarsNodup s) :
    FullArenaVarsNodup s' := by
  intro r hr hgb
  change r ∈ fullArenaClauseRefs s' at hr
  have hmem : r ∈ fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs at hr ⊢; rw [hap.2.1] at hr; exact hr
  have hperm := hap.2.2 r hmem
  unfold fullArenaClauseGarb at hgb
  rw [hperm.2.1] at hgb
  exact (List.Perm.map (fun x => x / 2) hperm.2.2).nodup_iff.mpr (hnd r hmem hgb)

theorem m6o_call_fullBcpS15_invW {Γ : Env} {f : Sym} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ a m' Q' X', FullM6BcpS15.fullBcpS15Spec a m' Q' X' →
      Γ f [i64] [i64] a m' Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hdense : s.core.dense_mode = 0#64)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r s' m', FullM6HdrInvW c F0 F_cur ext s' →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → s'.core.propagated = s'.core.trail_end ∧
        (s.core.oom = 0#64 → s'.core.oom = 0#64) ∧
        (s.core.propagated < s.core.trail_end → s'.core.fuel.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → s'.core.fuel.toNat < s.core.fuel.toNat ∧
        s'.core.oom = 0#64 ∧ FullConflictOkW F_cur s') →
      (r = 2#64 → s'.core.oom ≠ 0#64 ∨ s'.core.fuel = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s'.core = s.core) →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call f (as := [i64]) (bs := [i64]) args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  refine hΓ _ _ _ X ⟨c, F0, F_cur, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl,
    hinv.sparseW.1, hinv.sparseW.2.1, hdense, fullM6HdrMem_focus_full hm, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' s'
    hs' hw' hte hap _hdel hfu hr h0 h1 h2 hno hm'
  have hspW' : FullSparseInvW c F0 F_cur s' :=
    ⟨hs', hw', hinv.sparseW.2.2.1, m6o_arenaVarsNodup_perm hap hinv.sparseW.2.2.2.1,
     FullExtScratchOk.of_pres hinv.sparseW.2.2.2.2.1 ⟨rfl, rfl⟩ fun _ hr =>
       by unfold fullArenaClauseRefs at hr ⊢; rwa [hap.2.1],
     hdense⟩
  exact hk r s' m' (FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk hspW') hte hap hfu hr h0 h1 h2
    (fun heq => ⟨(hno heq).1, congrArg FullState.core (hno heq).2⟩)
    (fullM6HdrMem_unfocus_full hm')

/-! ### `TFlat` `"full_analyze_rsn"` -> `"full_analyze_rsn_m6_hdr"` Frame Lifter
  and `full_deduce_1uip_m6_hdr` -/

private def arsnLiftEnv : Env := fun f as bs xs m Q X =>
  match f, as, bs, xs, Q with
  | "full_analyze_rsn", [.bits 64, .bits 32, .bits 32], [.bool], xs, Q =>
    Full.fullAnalyzeRsnSpec xs m Q X
  | "full_analyze_lit", [.bits 64, .bits 32, .bits 32], [.bool], xs, Q =>
    Full.fullAnalyzeLitSpec xs m Q X
  | "full_clear_ana", [.bits 64], [], xs, Q =>
    Full.fullClearAnaSpec xs m Q X
  | "full_otfs_large", [.bits 64, .bits 32, .bits 32], [.bool], xs, Q =>
    Full.fullOtfsLargeSpec xs m Q X
  | "full_otfs_bin", [.bits 64, .bits 32, .bits 32], [.bool], xs, Q =>
    Full.fullOtfsBinSpec xs m Q X
  | "full_otfs_subsume", [.bits 64, .bits 32, .bits 64, .bits 64, .bool], [], xs, Q =>
    Full.fullOtfsSubsumeSpec xs m Q X
  | _, _, _, _, _ => False

private def tflatMapArsnCall {as : List Ty} (bs : List Ty) (args : Tup (Arg K) as) (nv : Nat) :
    Option (Arg K i64) :=
  match as, bs, args with
  | [.bits 64, .bits 32, .bits 32], [.bool], (a0, _, _, ()) =>
    match a0 with
    | .var i => if decide (0 < nv ∧ i = nv - 1) then some a0 else none
    | _ => none
  | _, _, _ => none

mutual
private def tflatMapArsn {rs : List Ty} (nv : Nat) : TFlat rs → Option (TFlat rs)
  | .let_ (ts := ts) op k => (tflatMapArsn (nv + ts.length) k).map (.let_ op)
  | .load t a k => (tflatMapArsn (nv + 1) k).map (.load t a)
  | .store v a k => (tflatMapArsn nv k).map (.store v a)
  | .call f bs args k =>
    if f = "full_analyze_rsn" then
      match tflatMapArsnCall bs args nv with
      | some _ => (tflatMapArsn (nv + bs.length) k).map (.call "full_analyze_rsn_m6_hdr" bs args)
      | none => none
    else (tflatMapArsn (nv + bs.length) k).map (.call f bs args)
  | .jnz c t e =>
    match tflatMapArsn nv t, tflatMapArsn nv e with
    | some t', some e' => some (.jnz c t' e')
    | _, _ => none
  | .jump j args => some (.jump j args)
  | .ret vs => some (.ret vs)
  | .exit f args => some (.exit f args)
  | .hlt => some .hlt
  | .group bodies k =>
    match tblocksMapArsn nv bodies, tflatMapArsn nv k with
    | some bodies', some k' => some (.group bodies' k')
    | _, _ => none

private def tblocksMapArsn {rs : List Ty} (nv : Nat) :
    {sig : List (List Ty)} → TBlocks rs sig → Option (TBlocks rs sig)
  | _, .nil => some .nil
  | _, .cons (ts := ts) b bs =>
    match tflatMapArsn (nv + ts.length) b, tblocksMapArsn nv bs with
    | some b', some bs' => some (.cons b' bs')
    | _, _ => none
end

private theorem listGet?_cons_last {α : Type _} (x : α) (xs : List α) (hle : 0 < xs.length) :
    listGet? (x :: xs) ((x :: xs).length - 1) = listGet? xs (xs.length - 1) := by
  rw [show (x :: xs).length - 1 = (xs.length - 1) + 1 from by simp; omega]; rfl

private theorem listGet?_pushTup_last {ts : List Ty} (xs : Tup Val ts)
    (vs : List ((t : Ty) × Val t)) (hle : 0 < vs.length) :
    listGet? (pushTup xs vs) ((pushTup xs vs).length - 1) = listGet? vs (vs.length - 1) := by
  induction ts generalizing vs with
  | nil => cases xs; rfl
  | cons t ts ih =>
    rcases xs with ⟨x, xs⟩
    exact (ih xs (⟨t, x⟩ :: vs) (by simp)).trans (listGet?_cons_last ⟨t, x⟩ vs hle)

private def liftContHdr {ts : List Ty} (c : FullCfg) (J₂ : Cont ts) : Cont ts :=
  fun xs m_s => ∀ ext m_f, M6HdrExtOk ext →
    (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m_f → J₂ xs m_f

private def liftTupContHdr (c : FullCfg) :
    {sig : List (List Ty)} → Tup Cont sig → Tup Cont sig
  | [], () => ()
  | _ :: _, (J, Js) => (liftContHdr c J, liftTupContHdr c Js)

private def LabelsLiftRel (c : FullCfg)
    (ls₁ ls₂ : List ((ts : List Ty) × Cont ts)) : Prop :=
  (∀ (ts : List Ty) (idx : Nat), (lookupL ls₁ ts idx).isSome = (lookupL ls₂ ts idx).isSome) ∧
  ∀ (ts : List Ty) (idx : Nat) (j₁ j₂ : Cont ts),
    lookupL ls₁ ts idx = some j₁ → lookupL ls₂ ts idx = some j₂ →
    ∀ xs m_s m_f ext, M6HdrExtOk ext →
      (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m_f → j₁ xs m_s → j₂ xs m_f

private theorem labelsLiftRel_cons {c : FullCfg} {ts : List Ty}
    {ls₁ ls₂ : List ((us : List Ty) × Cont us)} {J₂ : Cont ts}
    (h : LabelsLiftRel c ls₁ ls₂) :
    LabelsLiftRel c (⟨ts, liftContHdr c J₂⟩ :: ls₁) (⟨ts, J₂⟩ :: ls₂) := by
  refine ⟨fun ts' idx => ?_, fun ts' idx j₁ j₂ hj₁ hj₂ => ?_⟩
  · cases idx with
    | zero => dsimp only [lookupL, listGet?, castListTy]; cases listTyDecEq ts ts' <;> rfl
    | succ k => exact h.1 ts' k
  · cases idx with
    | succ k => exact h.2 ts' k j₁ j₂ hj₁ hj₂
    | zero =>
      dsimp only [lookupL, listGet?, castListTy] at hj₁ hj₂
      cases hdec : listTyDecEq ts ts' with
      | isFalse _ => simp [hdec] at hj₁
      | isTrue heq =>
        subst heq; simp only [hdec, Option.some.injEq] at hj₁ hj₂; subst hj₁ hj₂
        exact fun _ _ _ _ hext hsep hJ => hJ _ _ hext hsep

private theorem labelsLiftRel_pushTup {c : FullCfg} :
    {sig : List (List Ty)} → (Js₂ : Tup Cont sig) →
    {ls₁ ls₂ : List ((ts : List Ty) × Cont ts)} → LabelsLiftRel c ls₁ ls₂ →
    LabelsLiftRel c (pushTup (liftTupContHdr c Js₂) ls₁) (pushTup Js₂ ls₂)
  | [], (), _, _, h => h
  | _ :: _, (_J, Js), _, _, h => labelsLiftRel_pushTup Js (labelsLiftRel_cons h)

private theorem sep_extract_eq {A B : Mem 64 → Prop} {m : Mem 64} (h : (A ⋆ B) m) :
    ∃ m_b, B m_b ∧ (Eq m_b ⋆ A) m := by
  have hB : B = (fun m' => ∃ m_b, B m_b ∧ Eq m_b m') :=
    funext fun m' => propext ⟨fun hb => ⟨m', hb, rfl⟩, fun ⟨_, hb, heq⟩ => heq ▸ hb⟩
  have h1 : (A ⋆ (fun m' => ∃ m_b, B m_b ∧ Eq m_b m')) m := hB ▸ h
  rw [sep_ex_r] at h1; rcases h1 with ⟨m_b, h2⟩; rw [sep_pure_r, sep_comm] at h2; exact ⟨m_b, h2⟩

private theorem sep_join_eq {A P : Mem 64 → Prop} {m_b m : Mem 64}
    (hp : P m_b) (h : (Eq m_b ⋆ A) m) : (A ⋆ P) m := by
  rw [sep_comm]; exact sep_mono (fun _ heq => heq ▸ hp) h

private theorem sep_frame_enter {E M R : Mem 64 → Prop} {m_s m_f : Mem 64}
    (hm : (M ⋆ R) m_s) (hsep : (Eq m_s ⋆ E) m_f) : (M ⋆ (E ⋆ R)) m_f := by
  have h1 : (E ⋆ (M ⋆ R)) m_f := sep_join_eq hm hsep
  rwa [← sep_assoc, sep_comm E M, sep_assoc] at h1

private theorem sep_frame_exit {E M R : Mem 64 → Prop} {m_f : Mem 64}
    (hm : (M ⋆ (E ⋆ R)) m_f) : ∃ m_s, (M ⋆ R) m_s ∧ (Eq m_s ⋆ E) m_f := by
  rw [← sep_assoc, sep_comm M E, sep_assoc] at hm; exact sep_extract_eq hm

private theorem m6o_sep_split_ext {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    ∃ m_s, (FullMem c s ⋆ R) m_s ∧ (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m :=
  sep_extract_eq (fullM6HdrMem_ext_focus hm)

private theorem m6o_sep_join_fullM6Hdr {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m_s m_f : Mem 64}
    (hs : (FullMem c s ⋆ R) m_s) (hsep : (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m_f) :
    (FullM6HdrMem c ext s ⋆ R) m_f := fullM6HdrMem_ext_unfocus (sep_join_eq hs hsep)

private structure ArsnLiftHyps (Γ : Env) : Prop where
  alit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
    Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X
  arsn : ∀ a m Q X, m6AnalyzeRsnHdrSpec a m Q X →
    Γ "full_analyze_rsn_m6_hdr" [i64, i32, i32] [.bool] a m Q X
  clear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X
  otfsLarge : ∀ a m Q X, Full.fullOtfsLargeSpec a m Q X →
    Γ "full_otfs_large" [i64, i32, i32] [.bool] a m Q X
  otfsBin : ∀ a m Q X, Full.fullOtfsBinSpec a m Q X →
    Γ "full_otfs_bin" [i64, i32, i32] [.bool] a m Q X
  otfsSub : ∀ a m Q X, Full.fullOtfsSubsumeSpec a m Q X →
    Γ "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X

private theorem m6o_frame_unchanged_call {Γ : Env} (hΓ : ArsnLiftHyps Γ)
    {c : FullCfg} {ext : List (BitVec 64)} {rs : List Ty}
    {f : String} {as bs : List Ty} (hf_ne : f ≠ "full_analyze_rsn")
    (args' : Tup (Arg Val) as) (k₂ : Tup Val bs → Expr Val Cont rs)
    {m_s m_f : Mem 64} {P : Post bs} {Q₂ : Post rs}
    (hG : arsnLiftEnv f as bs (vals args') m_s P (fun _ _ _ _ => False))
    (hk : ∀ rv m_s' m_f', P rv m_s' → (Eq m_s' ⋆ array64 (c.hdr - 2304) ext) m_f' →
      wp Γ Q₂ (fun _ _ _ _ => False) (k₂ rv) m_f')
    (hsep : (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m_f) :
    wp Γ Q₂ (fun _ _ _ _ => False) (.call f (as := as) (bs := bs) args' k₂) m_f := by
  let E := array64 (c.hdr - 2304) ext
  by_cases h2 : f = "full_analyze_lit" ∧ as = [i64, i32, i32] ∧ bs = [.bool]
  · rcases h2 with ⟨rfl, rfl, rfl⟩; dsimp only [arsnLiftEnv] at hG
    rcases hG with ⟨c', s', R', hc, h1, h2, h3, h4, h5, hm_s, hP'⟩
    rcases args' with ⟨a0, a1, a2, ⟨⟩⟩; dsimp only [vals] at hc
    refine wp_call_of_spec (as := [i64, i32, i32]) (bs := [.bool]) (a0, a1, a2, ()) k₂ ?_
    dsimp only [vals]; rw [hc]
    refine hΓ.alit (c'.hdr, a1.val, a2.val, ()) m_f _ _
      ⟨c', s', E ⋆ R', rfl, h1, h2, h3, h4, h5, sep_frame_enter hm_s hsep,
        fun ok mrk' tmp' tc' tl' mcl' ws1' ant' res' m_f'
          a b d e f g h i j k l n o p hm_f' => ?_⟩
    rcases sep_frame_exit hm_f' with ⟨m_s', hm_s', hsep'⟩
    exact hk (ok, ()) m_s' m_f' (hP' ok mrk' tmp' tc' tl' mcl' ws1' ant' res' m_s'
      a b d e f g h i j k l n o p hm_s') hsep'
  · by_cases h3 : f = "full_clear_ana" ∧ as = [i64] ∧ bs = []
    · rcases h3 with ⟨rfl, rfl, rfl⟩; dsimp only [arsnLiftEnv] at hG
      rcases hG with ⟨c', s', R', hc, hlen', hm_s, hP'⟩
      rcases args' with ⟨a0, ⟨⟩⟩; dsimp only [vals] at hc
      refine wp_call_of_spec (as := [i64]) (bs := []) (a0, ()) k₂ ?_
      dsimp only [vals]; rw [hc]
      refine hΓ.clear (c'.hdr, ()) m_f _ _
        ⟨c', s', E ⋆ R', rfl, hlen', sep_frame_enter hm_s hsep, fun mrk' m_f' a b d e hm_f' => ?_⟩
      rcases sep_frame_exit hm_f' with ⟨m_s', hm_s', hsep'⟩
      exact hk () m_s' m_f' (hP' mrk' m_s' a b d e hm_s') hsep'
    · by_cases h4 : f = "full_otfs_large" ∧ as = [i64, i32, i32] ∧ bs = [.bool]
      · rcases h4 with ⟨rfl, rfl, rfl⟩; dsimp only [arsnLiftEnv] at hG
        rcases hG with ⟨c', F0', F_cur', cut', idx_u', s', R', hc, a, b, d, e, f, g, h, i,
          j, k, l, n, hm_s, hP'⟩
        rcases args' with ⟨a0, a1, a2, ⟨⟩⟩; dsimp only [vals] at hc
        refine wp_call_of_spec (as := [i64, i32, i32]) (bs := [.bool]) (a0, a1, a2, ()) k₂ ?_
        dsimp only [vals]; rw [hc]
        refine hΓ.otfsLarge (c'.hdr, a1.val, a2.val, ()) m_f _ _
          ⟨c', F0', F_cur', cut', idx_u', s', E ⋆ R', rfl, a, b, d, e, f, g, h, i, j, k, l, n,
            sep_frame_enter hm_s hsep, fun ok ar' wv' ws' wl' wu' oom' sc' m_f'
              p1 p2 p3 p4 p5 p6 p7 p8 p9 hm_f' => ?_⟩
        rcases sep_frame_exit hm_f' with ⟨m_s', hm_s', hsep'⟩
        exact hk (ok, ()) m_s' m_f'
          (hP' ok ar' wv' ws' wl' wu' oom' sc' m_s' p1 p2 p3 p4 p5 p6 p7 p8 p9 hm_s') hsep'
      · by_cases h5 : f = "full_otfs_bin" ∧ as = [i64, i32, i32] ∧ bs = [.bool]
        · rcases h5 with ⟨rfl, rfl, rfl⟩; dsimp only [arsnLiftEnv] at hG
          rcases hG with ⟨c', F0', F_cur', cut', idx_u', s', R', hc, a, b, d, e, f, g, h, i,
            j, k, l, n, hm_s, hP'⟩
          rcases args' with ⟨a0, a1, a2, ⟨⟩⟩; dsimp only [vals] at hc
          refine wp_call_of_spec (as := [i64, i32, i32]) (bs := [.bool]) (a0, a1, a2, ()) k₂ ?_
          dsimp only [vals]; rw [hc]
          refine hΓ.otfsBin (c'.hdr, a1.val, a2.val, ()) m_f _ _
            ⟨c', F0', F_cur', cut', idx_u', s', E ⋆ R', rfl, a, b, d, e, f, g, h, i, j, k, l, n,
              sep_frame_enter hm_s hsep,
              fun ok ar' ag' wv' ws' wl' wu' nb' ct' cr' c0' c1' oom' sc' m_f'
                p1 p2 p3 p4 p5 p6 p7 p8 p9 hm_f' => ?_⟩
          rcases sep_frame_exit hm_f' with ⟨m_s', hm_s', hsep'⟩
          exact hk (ok, ()) m_s' m_f' (hP' ok ar' ag' wv' ws' wl' wu' nb' ct' cr' c0' c1'
            oom' sc' m_s' p1 p2 p3 p4 p5 p6 p7 p8 p9 hm_s') hsep'
        · by_cases h6 : f = "full_otfs_subsume" ∧ as = [i64, i32, i64, i64, .bool] ∧ bs = []
          · rcases h6 with ⟨rfl, rfl, rfl⟩; dsimp only [arsnLiftEnv] at hG
            rcases hG with ⟨c', F0', F_cur', cut', s', R', hc, a, b, d, e, hm_s, hP'⟩
            rcases args' with ⟨a0, a1, a2, a3, a4, ⟨⟩⟩; dsimp only [vals] at hc
            refine wp_call_of_spec (as := [i64, i32, i64, i64, .bool]) (bs := [])
              (a0, a1, a2, a3, a4, ()) k₂ ?_
            dsimp only [vals]; rw [hc]
            refine hΓ.otfsSub (c'.hdr, a1.val, a2.val, a3.val, a4.val, ()) m_f _ _
              ⟨c', F0', F_cur', cut', s', E ⋆ R', rfl, a, b, d, e, sep_frame_enter hm_s hsep,
                fun ar' ag' ni' nr' m_f' p1 p2 p3 p4 p5 hm_f' => ?_⟩
            rcases sep_frame_exit hm_f' with ⟨m_s', hm_s', hsep'⟩
            exact hk () m_s' m_f' (hP' ar' ag' ni' nr' m_s' p1 p2 p3 p4 p5 hm_s') hsep'
          · dsimp only [arsnLiftEnv] at hG; split at hG
            · exact absurd rfl hf_ne
            · exact absurd ⟨rfl, rfl, rfl⟩ h2
            · exact absurd ⟨rfl, rfl, rfl⟩ h3
            · exact absurd ⟨rfl, rfl, rfl⟩ h4
            · exact absurd ⟨rfl, rfl, rfl⟩ h5
            · exact absurd ⟨rfl, rfl, rfl⟩ h6
            · exact False.elim hG

private theorem denoteArgs3_inv {t0 t1 t2 : Ty} {vs : List ((t : Ty) × Val t)}
    {a0 : Arg K t0} {a1 : Arg K t1} {a2 : Arg K t2} {args' : Tup (Arg Val) [t0, t1, t2]}
    (hd : denoteArgs (ts := [t0, t1, t2]) vs (a0, a1, a2, ()) = some args') :
    ∃ a0' a1' a2', denoteArg vs a0 = some a0' ∧ denoteArg vs a1 = some a1' ∧
      denoteArg vs a2 = some a2' ∧ args' = (a0', a1', a2', ()) := by
  simp only [denoteArgs] at hd
  cases h0 : denoteArg vs a0 with | none => simp [h0] at hd | some x0 =>
  cases h1 : denoteArg vs a1 with | none => simp [h0, h1] at hd | some x1 =>
  cases h2 : denoteArg vs a2 with | none => simp [h0, h1, h2] at hd | some x2 =>
  simp [h0, h1, h2] at hd; subst hd; exact ⟨x0, x1, x2, rfl, rfl, rfl, rfl⟩

mutual
private theorem denote_wp_arsn_lift {Γ : Env} (hΓ : ArsnLiftHyps Γ)
    {c : FullCfg} (hcfg : FullM6HdrCfgOk c) {rs : List Ty} :
    ∀ (tf₁ tf₂ : TFlat rs)
      (vs : List ((t : Ty) × Val t)) (ls₁ ls₂ : List ((ts : List Ty) × Cont ts)),
      0 < vs.length → listGet? vs (vs.length - 1) = some ⟨i64, c.hdr⟩ →
      LabelsLiftRel c ls₁ ls₂ → tflatMapArsn vs.length tf₁ = some tf₂ →
      ∀ (Q₁ Q₂ : Post rs),
        (∀ rv m_s ext m_f, M6HdrExtOk ext →
          (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m_f → Q₁ rv m_s → Q₂ rv m_f) →
        ∀ m_s ext m_f, M6HdrExtOk ext → (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m_f →
          wp arsnLiftEnv Q₁ (fun _ _ _ _ => False) (denote Val Cont tf₁ vs ls₁) m_s →
          wp Γ Q₂ (fun _ _ _ _ => False) (denote Val Cont tf₂ vs ls₂) m_f
  | .let_ (ts := ts) op k, tf₂, vs, ls₁, ls₂, hv_pos, hlast, hls, hmap, Q₁, Q₂, hQ,
      m_s, ext, m_f, hext, hsep, hwp => by
    simp only [tflatMapArsn] at hmap
    cases hk_eq : tflatMapArsn (vs.length + ts.length) k with
    | none => simp [hk_eq] at hmap | some k' =>
    simp only [hk_eq, Option.map_some, Option.some.injEq] at hmap; subst tf₂
    dsimp only [denote] at hwp ⊢
    cases hd : denoteArgs vs op.args with | none => rw [hd] at hwp; cases hwp | some args' =>
    rw [hd] at hwp; dsimp only at hwp ⊢; dsimp only [wp] at hwp ⊢
    refine OpCode.wp_mono op.code _ (fun r h => ?_) hwp
    have hp := pushTup_length r vs
    exact denote_wp_arsn_lift hΓ hcfg k k' (pushTup r vs) ls₁ ls₂ (by rw [hp]; omega)
      (by simpa using (listGet?_pushTup_last r vs hv_pos).trans hlast) hls
      (by rw [hp]; exact hk_eq) Q₁ Q₂ hQ m_s ext m_f hext hsep h
  | .load t a k, tf₂, vs, ls₁, ls₂, hv_pos, hlast, hls, hmap, Q₁, Q₂, hQ,
      m_s, ext, m_f, hext, hsep, hwp => by
    simp only [tflatMapArsn] at hmap
    cases hk_eq : tflatMapArsn (vs.length + 1) k with | none => simp [hk_eq] at hmap | some k' =>
    simp only [hk_eq, Option.map_some, Option.some.injEq] at hmap; subst tf₂
    dsimp only [denote] at hwp ⊢
    cases hd : denoteArg vs a with | none => rw [hd] at hwp; cases hwp | some a' =>
    rw [hd] at hwp; dsimp only at hwp ⊢; rcases hwp with ⟨v, hld, hwp⟩
    exact ⟨v, loadVal_frame hsep hld, denote_wp_arsn_lift hΓ hcfg k k' (⟨t, v⟩ :: vs) ls₁ ls₂
      (by simp) ((listGet?_cons_last ⟨t, v⟩ vs hv_pos).trans hlast) hls hk_eq Q₁ Q₂ hQ m_s ext m_f
      hext hsep hwp⟩
  | .store v a k, tf₂, vs, ls₁, ls₂, hv_pos, hlast, hls, hmap, Q₁, Q₂, hQ,
      m_s, ext, m_f, hext, hsep, hwp => by
    simp only [tflatMapArsn] at hmap
    cases hk_eq : tflatMapArsn vs.length k with | none => simp [hk_eq] at hmap | some k' =>
    simp only [hk_eq, Option.map_some, Option.some.injEq] at hmap; subst tf₂
    dsimp only [denote] at hwp ⊢
    cases hv : denoteArg vs v with | none => rw [hv] at hwp; cases hwp | some v' =>
    cases ha : denoteArg vs a with | none => rw [hv, ha] at hwp; cases hwp | some a' =>
    rw [hv, ha] at hwp; dsimp only at hwp ⊢; rcases hwp with ⟨hok, hwp⟩
    exact ⟨storeOk_frame hsep hok, denote_wp_arsn_lift hΓ hcfg k k' vs ls₁ ls₂
      hv_pos hlast hls hk_eq Q₁ Q₂ hQ _ ext _ hext (storeMem_frame hsep hok v'.val) hwp⟩
  | .call f bs args k, tf₂, vs, ls₁, ls₂, hv_pos, hlast, hls, hmap, Q₁, Q₂, hQ,
      m_s, ext, m_f, hext, hsep, hwp => by
    simp only [tflatMapArsn] at hmap
    by_cases hf_arsn : f = "full_analyze_rsn"
    · subst hf_arsn; simp only [↓reduceIte] at hmap
      cases ht_eq : tflatMapArsnCall bs args vs.length with
      | none => simp [ht_eq] at hmap | some a0 =>
      cases hk_eq : tflatMapArsn (vs.length + bs.length) k with
      | none => simp [ht_eq, hk_eq] at hmap
      | some k' =>
        simp only [ht_eq, hk_eq, Option.map_some, Option.some.injEq] at hmap; subst tf₂
        dsimp only [tflatMapArsnCall] at ht_eq
        split at ht_eq <;> try cases ht_eq
        rename_i _i a1 a2; split at ht_eq <;> try cases ht_eq
        rename_i _iv idx; split at ht_eq <;> try cases ht_eq
        rename_i hdec
        have hiv : idx = vs.length - 1 := by rw [decide_eq_true_eq] at hdec; exact hdec.2
        subst hiv; dsimp only [denote] at hwp ⊢
        cases hd : denoteArgs (ts := [i64, i32, i32]) vs
            (Arg.var (vs.length - 1), a1, a2, ()) with
        | none => rw [hd] at hwp; cases hwp
        | some args' =>
          rw [hd] at hwp; dsimp only at hwp ⊢; rcases hwp with ⟨P, _E, hG, hP, _hE⟩
          have hspec : Full.fullAnalyzeRsnSpec (vals args') m_s P (fun _ _ _ _ => False) := hG
          rcases denoteArgs3_inv hd with ⟨a0', a1', a2', ha0, _ha1, _ha2, h_eq⟩
          have ha0_eq : a0' = .var c.hdr := by
            simpa only [denoteArg, lookupV, hlast, castTy, ↓reduceDIte,
              Option.some.injEq] using ha0.symm
          have hargs_v : vals args' = (c.hdr, a1'.val, a2'.val, ()) := by rw [h_eq, ha0_eq]; rfl
          rw [hargs_v] at hspec
          rcases hspec with ⟨c', F0', F_cur', cut', s', R', hc'_eq, hlen', hcut', hcov',
            htl', htc', href', hm_s, hP'⟩
          have hcfg' := M6HdrCfgOk_of_le (hc'_eq ▸ M6HdrCfgOk_le hcfg)
          rw [hc'_eq] at hargs_v; refine wp_call_of_spec args' _ ?_; rw [hargs_v]
          refine hΓ.arsn (c'.hdr, a1'.val, a2'.val, ()) m_f _ _ (m6AnalyzeRsnHdrSpec_of
            hcfg' hext hlen' hcut' hcov' htl' htc' href'
            (m6o_sep_join_fullM6Hdr hm_s (by rwa [← hc'_eq]))
            fun ok mrk' tmp' tc' tl' mcl' arena' sc' ext' m_f' hext' _ hlen2 hcut2 hcov2 hpre2
              hws2 htl2 htl_cv htc2 hrefs2 har2 hmrk2 htmp2 hnew2 hjok2 hjnodup2 hdiff2 hres2 hok2
              hm_f' => ?_)
          rcases m6o_sep_split_ext hm_f' with ⟨m_s', hm_s', hsep'⟩
          have hp_ok := hP' ok mrk' tmp' tc' tl' mcl' arena' sc' m_s' hlen2 hcut2 hcov2 hpre2 hws2
            htl2 htl_cv htc2 hrefs2 har2 hmrk2 htmp2 hnew2 hjok2 hjnodup2 hdiff2 hres2 hok2 hm_s'
          have hlen_p := pushTup_length (as := [.bool]) (ok, ()) vs
          exact denote_wp_arsn_lift hΓ hcfg k k'
            (pushTup (as := [.bool]) (f := Val) (ok, ()) vs) ls₁ ls₂ (by rw [hlen_p]; omega)
            ((listGet?_pushTup_last (ts := [.bool]) (ok, ()) vs hv_pos).trans hlast) hls
            (by simpa [hlen_p] using hk_eq) Q₁ Q₂ hQ m_s' ext' m_f' hext' (by rwa [hc'_eq])
            (hP ((ok, ()) : Tup Val [.bool]) m_s' hp_ok)
    · simp only [hf_arsn, ↓reduceIte] at hmap
      cases hk_eq : tflatMapArsn (vs.length + bs.length) k with
      | none => simp [hk_eq] at hmap
      | some k' =>
        simp only [hk_eq, Option.map_some, Option.some.injEq] at hmap; subst tf₂
        dsimp only [denote] at hwp ⊢
        cases hd : denoteArgs vs args with | none => rw [hd] at hwp; cases hwp | some args' =>
        rw [hd] at hwp; dsimp only at hwp ⊢; rcases hwp with ⟨P, _E, hG, hP, _hE⟩
        refine m6o_frame_unchanged_call hΓ hf_arsn args'
          (fun rv => denote Val Cont k' (pushTup rv vs) ls₂) hG
          (fun rv m_s' m_f' hp hsep' => ?_) hsep
        have hlen_p := pushTup_length rv vs
        exact denote_wp_arsn_lift hΓ hcfg k k' (pushTup rv vs) ls₁ ls₂ (by rw [hlen_p]; omega)
          ((listGet?_pushTup_last rv vs hv_pos).trans hlast) hls (by rw [hlen_p]; exact hk_eq)
          Q₁ Q₂ hQ m_s' ext m_f' hext hsep' (hP rv m_s' hp)
  | .jnz cd t e, tf₂, vs, ls₁, ls₂, hv_pos, hlast, hls, hmap, Q₁, Q₂, hQ,
      m_s, ext, m_f, hext, hsep, hwp => by
    simp only [tflatMapArsn] at hmap
    cases ht_eq : tflatMapArsn vs.length t with | none => simp [ht_eq] at hmap | some t' =>
    cases he_eq : tflatMapArsn vs.length e with | none => simp [ht_eq, he_eq] at hmap | some e' =>
    simp only [ht_eq, he_eq, Option.some.injEq] at hmap; subst tf₂; dsimp only [denote] at hwp ⊢
    cases hd : denoteArg vs cd with | none => rw [hd] at hwp; cases hwp | some c' =>
    rw [hd] at hwp; dsimp only at hwp ⊢
    exact ⟨fun hc => denote_wp_arsn_lift hΓ hcfg t t' vs ls₁ ls₂ hv_pos hlast hls ht_eq
        Q₁ Q₂ hQ m_s ext m_f hext hsep (hwp.1 hc),
      fun hc => denote_wp_arsn_lift hΓ hcfg e e' vs ls₁ ls₂ hv_pos hlast hls he_eq
        Q₁ Q₂ hQ m_s ext m_f hext hsep (hwp.2 hc)⟩
  | .jump (ts := ts) j args, tf₂, vs, ls₁, ls₂, _, _, hls, hmap, _, _, _,
      m_s, ext, m_f, hext, hsep, hwp => by
    simp only [tflatMapArsn] at hmap; injection hmap with hmap'; subst tf₂
    dsimp only [denote] at hwp ⊢
    cases hj1 : lookupL ls₁ ts j with | none => rw [hj1] at hwp; cases hwp | some j₁ =>
    cases hj2 : lookupL ls₂ ts j with
    | none => have hs := hls.1 ts j; rw [hj1, hj2] at hs; simp at hs
    | some j₂ =>
      cases ha : denoteArgs vs args with | none => rw [hj1, ha] at hwp; cases hwp | some args' =>
      rw [hj1, ha] at hwp; dsimp only at hwp ⊢
      exact hls.2 ts j j₁ j₂ hj1 hj2 (vals args') m_s m_f ext hext hsep hwp
  | .ret vs', tf₂, vs, _, _, _, _, _, hmap, Q₁, Q₂, hQ, m_s, ext, m_f, hext, hsep, hwp => by
    simp only [tflatMapArsn] at hmap; injection hmap with hmap'; subst tf₂
    dsimp only [denote] at hwp ⊢
    cases ha : denoteArgs vs vs' with | none => rw [ha] at hwp; cases hwp | some vs'' =>
    rw [ha] at hwp; dsimp only at hwp ⊢; exact hQ (vals vs'') m_s ext m_f hext hsep hwp
  | .exit _ args, tf₂, vs, _, _, _, _, _, hmap, _, _, _, _, _, _, _, _, hwp => by
    simp only [tflatMapArsn] at hmap; injection hmap with hmap'; subst tf₂
    dsimp only [denote] at hwp ⊢
    cases ha : denoteArgs vs args <;> (rw [ha] at hwp; cases hwp)
  | .hlt, tf₂, _, _, _, _, _, _, hmap, _, _, _, _, _, _, _, _, hwp => by
    simp only [tflatMapArsn] at hmap; injection hmap with hmap'; subst tf₂; exact hwp
  | .group bodies k, tf₂, vs, ls₁, ls₂, hv_pos, hlast, hls, hmap, Q₁, Q₂, hQ,
      m_s, ext, m_f, hext, hsep, hwp => by
    simp only [tflatMapArsn] at hmap
    cases hb_eq : tblocksMapArsn vs.length bodies with
    | none => simp [hb_eq] at hmap | some bodies' =>
    cases hk_eq : tflatMapArsn vs.length k with
    | none => simp [hb_eq, hk_eq] at hmap
    | some k' =>
      simp only [hb_eq, hk_eq, Option.some.injEq] at hmap; subst tf₂
      dsimp only [denote, wp] at hwp ⊢
      intro Js₂ hc₂; let Js₁ := liftTupContHdr c Js₂; have hls' := labelsLiftRel_pushTup Js₂ hls
      exact denote_wp_arsn_lift hΓ hcfg k k' vs (pushTup Js₁ ls₁) (pushTup Js₂ ls₂)
        hv_pos hlast hls' hk_eq Q₁ Q₂ hQ m_s ext m_f hext hsep (hwp Js₁ (denoteB_wp_arsn_lift
          hΓ hcfg bodies bodies' vs (pushTup Js₁ ls₁) (pushTup Js₂ ls₂)
          hv_pos hlast hls' hb_eq Q₁ Q₂ hQ Js₂ hc₂))

private theorem denoteB_wp_arsn_lift {Γ : Env} (hΓ : ArsnLiftHyps Γ)
    {c : FullCfg} (hcfg : FullM6HdrCfgOk c) {rs : List Ty} :
    {sig : List (List Ty)} → (tb₁ tb₂ : TBlocks rs sig) →
      (vs : List ((t : Ty) × Val t)) → (ls₁ ls₂ : List ((ts : List Ty) × Cont ts)) →
      0 < vs.length → listGet? vs (vs.length - 1) = some ⟨i64, c.hdr⟩ →
      LabelsLiftRel c ls₁ ls₂ → tblocksMapArsn vs.length tb₁ = some tb₂ →
      ∀ (Q₁ Q₂ : Post rs),
        (∀ rv m_s ext m_f, M6HdrExtOk ext →
          (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m_f → Q₁ rv m_s → Q₂ rv m_f) →
        ∀ (Js₂ : Tup Cont sig),
          Closed Γ Q₂ (fun _ _ _ _ => False) (denoteB Val Cont tb₂ vs ls₂) Js₂ →
          Closed arsnLiftEnv Q₁ (fun _ _ _ _ => False) (denoteB Val Cont tb₁ vs ls₁)
            (liftTupContHdr c Js₂)
  | [], .nil, tb₂, _, _, _, _, _, _, hmap, _, _, _, (), _ => by
    simp only [tblocksMapArsn] at hmap; injection hmap with hmap'; subst tb₂; trivial
  | _, .cons (ts := ts) b bs, tb₂, vs, ls₁, ls₂, hv_pos, hlast, hls, hmap, Q₁, Q₂, hQ,
      (J, Js), hc => by
    simp only [tblocksMapArsn] at hmap
    cases hb_eq : tflatMapArsn (vs.length + ts.length) b with
    | none => simp [hb_eq] at hmap
    | some b' =>
      cases hbs_eq : tblocksMapArsn vs.length bs with
      | none => simp [hb_eq, hbs_eq] at hmap
      | some bs' =>
        simp only [hb_eq, hbs_eq, Option.some.injEq] at hmap; subst tb₂
        dsimp only [denoteB, Closed] at hc ⊢
        refine ⟨fun xs m_s hb ext m_f hext hsep => ?_,
          denoteB_wp_arsn_lift hΓ hcfg bs bs' vs ls₁ ls₂ hv_pos hlast hls hbs_eq Q₁ Q₂ hQ Js hc.2⟩
        have hp := pushTup_length xs vs
        exact hc.1 xs m_f (denote_wp_arsn_lift hΓ hcfg b b' (pushTup xs vs) ls₁ ls₂
          (by rw [hp]; omega) ((listGet?_pushTup_last xs vs hv_pos).trans hlast) hls
          (by rw [hp]; exact hb_eq) Q₁ Q₂ hQ m_s ext m_f hext hsep hb)
end

theorem full_deduce_1uip_m6_hdr_wp (Γ : Env)
    (hAlit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X)
    (hArsn : ∀ a m Q X, m6AnalyzeRsnHdrSpec a m Q X →
      Γ "full_analyze_rsn_m6_hdr" [i64, i32, i32] [.bool] a m Q X)
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X)
    (hOtfsLarge : ∀ a m Q X, Full.fullOtfsLargeSpec a m Q X →
      Γ "full_otfs_large" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsBin : ∀ a m Q X, Full.fullOtfsBinSpec a m Q X →
      Γ "full_otfs_bin" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsSub : ∀ a m Q X, Full.fullOtfsSubsumeSpec a m Q X →
      Γ "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X) :
    ∀ a m Q X, m6Deduce1uipHdrSpec a m Q X →
      Func.wp Γ full_deduce_1uip_m6_hdr_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases m6Deduce1uipHdrSpec_elim hs with
    ⟨c, F0, F_cur, cut, ext, s, R, rfl, hcfg, hext, hcut, hlvl, hcf, hm, hQ⟩
  have hmap : tflatMapArsn 1 (reifyFunc FullM6MinShrink.full_deduce_1uip_m6_body) =
      some (reifyFunc full_deduce_1uip_m6_hdr_body) := by t_kernel_rfl
  rcases m6o_sep_split_ext hm with ⟨m_s, hm_s, hsep⟩
  let Q_s : Post [i64] := fun (r, ()) m_s' => ∀ ext' m_f', M6HdrExtOk ext' →
    (Eq m_s' ⋆ array64 (c.hdr - 2304) ext') m_f' → Q (r, ()) m_f'
  have hwp_old : Func.wp arsnLiftEnv FullM6MinShrink.full_deduce_1uip_m6_body
      (c.hdr, ()) m_s Q_s (fun _ _ _ _ => False) :=
    FullM6MinShrink.full_deduce_1uip_m6_wp arsnLiftEnv (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (c.hdr, ()) m_s Q_s (fun _ _ _ _ => False) ⟨c, F0, F_cur, cut, s, R, rfl, hcut, hlvl, hcf,
        hm_s, fun r s' m_s' h1 h2 h3 h4 h5 h6 h7 h8 h9 hm_s' ext' m_f' hext' hsep' =>
          hQ r ext' s' m_f' hext' h1 h2 h3 h4 h5 h6 h7 h8 h9 (m6o_sep_join_fullM6Hdr hm_s' hsep')⟩
  have hden_old : wp arsnLiftEnv Q_s (fun _ _ _ _ => False)
      (denote Val Cont (reifyFunc FullM6MinShrink.full_deduce_1uip_m6_body)
        [⟨i64, c.hdr⟩] []) m_s :=
    Func.renorm_spec FullM6MinShrink.full_deduce_1uip_m6_wf hwp_old
  have hden_new : wp Γ Q (fun _ _ _ _ => False)
      (denote Val Cont (reifyFunc full_deduce_1uip_m6_hdr_body) [⟨i64, c.hdr⟩] []) m :=
    denote_wp_arsn_lift ⟨hAlit, hArsn, hClear, hOtfsLarge, hOtfsBin, hOtfsSub⟩ hcfg
      (reifyFunc FullM6MinShrink.full_deduce_1uip_m6_body)
      (reifyFunc full_deduce_1uip_m6_hdr_body)
      [⟨i64, c.hdr⟩] [] [] (by simp) rfl ⟨fun _ _ => rfl, fun _ _ _ _ hj => by cases hj⟩ hmap
      Q_s Q (fun (r, ()) m_s' ext' m_f' hext' hsep' hq => hq ext' m_f' hext' hsep')
      m_s ext m hext hsep hden_old
  have hren_hdr : Func.renorm full_deduce_1uip_m6_hdr_body = full_deduce_1uip_m6_hdr_body := by
    t_kernel_rfl
  exact wp_mono (fun _ _ h => h) (fun _ _ _ _ h => False.elim h) _ _
    (by rw [← hren_hdr]; exact hden_new)

section AnalyzeCoreAndSwitchMode

open LeanQbe.T.Examples.LratBytes
open scoped FullArenaTactics

private theorem m6o_upd_heap_pos {c : FullCfg} {s s0 : FullState}
    (hs : s.LengthsOk c) (hc : s.core = s0.core) (hp : FullExtScratchPres s0 s)
    {hp' ps' : List (BitVec 32)} {hl' : Nat}
    (hhp : hp'.length = c.max_vars) (hps : ps'.length = c.max_vars) :
    let s' : FullState := { s with scratch := { s.scratch with
      heap := hp', pos := ps', heap_len := hl' } }
    s'.LengthsOk c ∧ s'.core = s0.core ∧ FullExtScratchPres s0 s' :=
  ⟨⟨hs.1, fullScratch_lengthsOk_of_arr_len hs.2 rfl rfl rfl rfl rfl
    (hhp.trans hs.2.heap_len_arr.symm) (hps.trans hs.2.pos_len.symm)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩,
    hc, ⟨hp.1, hp.2⟩⟩

private theorem m6o_cut_with_conflicts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} (h : FullCutInvW c F0 F_cur cut s)
    (hcf : FullConflictOkCut F_cur cut s) (k' : BitVec 64) :
    let s' : FullState := { s with scratch := { s.scratch with conflicts := k' } }
    FullCutInvW c F0 F_cur cut s' ∧ FullConflictOkCut F_cur cut s' :=
  ⟨⟨⟨h.1.core_ok, fullScratch_lengthsOk_of_arr_len h.1.scratch_ok rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩,
    h.2.1, h.2.2.1, h.2.2.2.1,
    FullExtScratchOk.of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => hr), h.2.2.2.2.2⟩, hcf⟩

private theorem m6o_cut_with_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} (h : FullCutInvW c F0 F_cur cut s)
    (hcf : FullConflictOkCut F_cur cut s) {tmp' : List (BitVec 32)} {tl' : Nat}
    (htarr : tmp'.length = c.max_vars) (htle : tl' ≤ c.max_vars) :
    let s' : FullState := { s with core := { s.core with tmp := tmp', tmp_len := tl' } }
    FullCutInvW c F0 F_cur cut s' ∧ FullConflictOkCut F_cur cut s' :=
  ⟨⟨⟨{ h.1.core_ok with tmp_len_arr := htarr, tmp_len_le := htle }, h.1.scratch_ok⟩,
    deduce_same_core_cut h.2.1 s.core.mrk tmp' s.core.tmp_cnt tl' s.core.min_clr_len,
    h.2.2.1, h.2.2.2.1,
    FullExtScratchOk.of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => hr), h.2.2.2.2.2⟩, hcf⟩

private theorem m6o_cut_of_restoreBump {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} (h : FullCutInvW c F0 F_cur cut s)
    (hcf : FullConflictOkCut F_cur cut s) {mrk' : List (BitVec 8)} {mcl' : Nat} {sc' : FullScratch}
    (hlen' : ({ core := { s.core with mrk := mrk', min_clr_len := mcl' },
                 scratch := sc' } : FullState).LengthsOk c)
    (hmrk0' : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8)
    (hpres : FullExtScratchPres s
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }) :
    let s' : FullState :=
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
    FullCutInvW c F0 F_cur cut s' ∧ FullConflictOkCut F_cur cut s' := by
  let s' : FullState :=
    { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
  refine ⟨⟨hlen', deduce_same_core_cut h.2.1 mrk' s.core.tmp s.core.tmp_cnt s.core.tmp_len mcl',
    ⟨hmrk0', h.2.2.1.2⟩, h.2.2.2.1,
    FullExtScratchOk.of_pres h.2.2.2.2.1 hpres (fun _ hr => hr), h.2.2.2.2.2⟩, ?_⟩
  unfold FullConflictOkCut FullConflictOkW fullArenaClauseLits fullArenaClauseLitsCore at hcf ⊢
  exact hcf

private theorem m6o_otfs_of_restoreBump {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullOtfsInvW c F0 F_cur s)
    {mrk' : List (BitVec 8)} {mcl' : Nat} {sc' : FullScratch}
    (hlen' : ({ core := { s.core with mrk := mrk', min_clr_len := mcl' },
                 scratch := sc' } : FullState).LengthsOk c)
    (hmrk0' : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8)
    (hpres : FullExtScratchPres s
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }) :
    FullOtfsInvW c F0 F_cur
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' } :=
  ⟨hlen', { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
    ⟨hmrk0', h.2.2.1.2⟩, h.2.2.2.1,
    FullExtScratchOk.of_pres h.2.2.2.2.1 hpres (fun _ hr => hr), h.2.2.2.2.2⟩

private theorem m6o_otfs_of_safetySlice {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullOtfsInvW c F0 F_cur s) (hlen' : s'.LengthsOk c)
    (hcore : s'.core = s.core) (hpres : FullExtScratchPres s s') :
    FullOtfsInvW c F0 F_cur s' :=
  ⟨hlen', hcore ▸ h.2.1, by unfold FullLitMarksClear FullMrkZero; rw [hcore]; exact h.2.2.1,
    by unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
       rw [hcore]; exact h.2.2.2.1,
    fullExtScratchOk_of_core_eq h.2.2.2.2.1 hpres hcore, hcore ▸ h.2.2.2.2.2⟩

private def CoreLoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (iter_lim : BitVec 64)
    (st : BitVec 64 × FullState × List (BitVec 64)) (m' : Mem 64) : Prop :=
  ∃ cut', cut' ≤ st.2.1.core.trail_end ∧ FullCutInvW c F0 F_cur cut' st.2.1 ∧
    FullConflictOkCut F_cur cut' st.2.1 ∧ M6HdrExtOk st.2.2 ∧
    st.2.1.core.cur_vars = s.core.cur_vars ∧ st.2.1.core.fuel = s.core.fuel ∧
    st.2.1.core.cur_level ≤ s.core.cur_level ∧ st.2.1.scratch.work_stk2 = s.scratch.work_stk2 ∧
    st.1.toNat ≤ iter_lim.toNat ∧
    (FullMem c st.2.1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) st.2.2 ⋆ R)) m'

private def CoreShrinkPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (s' : FullState) : Prop :=
  FullOtfsInvW c F0 F_cur s' ∧ 0 < s'.core.cur_level ∧
  1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
  (List.map (fun x => x.toNat / 2) (List.take s'.core.tmp_len s'.core.tmp)).Nodup ∧
  (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
    l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 255#8) ∧
  (∀ k, 1 ≤ k → k < s'.core.tmp_len →
    let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
    0 < lv ∧ lv < s'.core.cur_level ∧
    lv ≤ (s'.core.lvl[(s'.core.tmp[s'.core.tmp_len - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
  (cnfOfClauses F_cur).EntailsClause
    (cnfClause (List.map BitVec.toNat (List.take s'.core.tmp_len s'.core.tmp))) ∧
  s'.core.cur_vars = s.core.cur_vars ∧ s'.core.fuel = s.core.fuel ∧
  s'.core.cur_level ≤ s.core.cur_level ∧ s'.scratch.work_stk2 = s.scratch.work_stk2

private def CoreCutJoin (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cut : Nat) (s : FullState) (st : FullState) : Prop :=
  cut ≤ st.core.trail_end ∧ FullCutInvW c F0 F_cur cut st ∧ FullConflictOkCut F_cur cut st ∧
  st.core.cur_vars = s.core.cur_vars ∧ st.core.fuel = s.core.fuel ∧
  st.core.cur_level ≤ s.core.cur_level ∧ st.scratch.work_stk2 = s.scratch.work_stk2

theorem full_analyze_core_m6_wp (Γ : Env)
    (hOneLit : ∀ a m Q X, Full.fullOneLitConflSpec a m Q X →
      Γ "full_one_lit_confl" [i64] [i64] a m Q X)
    (hFailed : ∀ a m Q X, m6AnaFailedLitHdrSpec a m Q X →
      Γ "full_ana_failed_lit_m6_hdr" [i64] [i64] a m Q X)
    (hDeduce : ∀ a m Q X, m6Deduce1uipHdrSpec a m Q X →
      Γ "full_deduce_1uip_m6_hdr" [i64] [i64] a m Q X)
    (hRestore : ∀ a m Q X, m6RestoreBumpAnaHdrSpec a m Q X →
      Γ "full_restore_bump_ana_m6_hdr" [i64] [] a m Q X)
    (hMinShrink : ∀ a m Q X, Full.fullMinShrinkSpec a m Q X →
      Γ "full_min_shrink_m6" [i64] [] a m Q X)
    (hTick : ∀ a m Q X, Full.fullTickRelSpec a m Q X → Γ "full_tick_rel" [i64] [] a m Q X)
    (hEma : ∀ a m Q X, Full.fullEmaUpdateSpec a m Q X →
      Γ "full_ema_update" [i64, i64] [] a m Q X)
    (hLearn : ∀ a m Q X, Full.fullLearnClauseSpec a m Q X →
      Γ "full_learn_clause" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullM6Hdr.m6HdrAnalyzeSpec a m Q X →
      Func.wp Γ full_analyze_core_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases m6HdrAnalyzeSpec_elim hs with ⟨c, F0, F_cur, ext, s, R, rfl, hinv, hcf, hm, hQ⟩
  have hmaxv := c.hmaxv; have har_cap := c.harena; unfold dimacsBound at hmaxv har_cap
  have hcv_le := hinv.sparseW.1.core_ok.cur_vars_le
  let iter_lim : BitVec 64 := BitVec.ofNat 64 s.core.cur_vars + 64#64
  have hil_val : iter_lim.toNat = s.core.cur_vars + 64 := by
    change (BitVec.ofNat 64 s.core.cur_vars + 64#64).toNat = _
    rw [bv64_add_small_eq] <;> simp [BitVec.toNat_ofNat] <;> omega
  unfold Func.wp full_analyze_core_m6_body
  refine wp_m6Hdr_focus_frame hm fun hm' => ?_; c0_hsteps_nogrp
  refine wp_while_state1 (α := BitVec 64 × FullState × List (BitVec 64)) (fun st => st.1)
    (fun st => iter_lim.toNat - st.1.toNat) (CoreLoopInv c F0 F_cur s R iter_lim) ?_ ?_
  · intro J hJ; refine hJ (0#64, s, ext) m ⟨s.core.trail_end, Nat.le_refl _, hinv.sparseW.toCut,
      hcf.toCut hinv.sparseW.2.1, hinv.extOk, rfl, rfl, Nat.le_refl _, rfl, by simp, hm'⟩
  · intro J ⟨iter, s1, ext1⟩ m1
      ⟨cut1, hcut1_le, hcut1, hcf1, hext1, hcv1, hfu1, hcl1, hws1, hil1, hm1⟩ ih
    dsimp only at hcut1_le hcut1 hcf1 hext1 hcv1 hfu1 hcl1 hws1 hil1 hm1 ⊢
    c0_hsteps_nogrp
    · have hlt : iter.toNat < iter_lim.toNat := by
        simpa [iter_lim, BitVec.toNat_add, BitVec.toNat_ofNat] using hc
      have hcv_fit : (BitVec.ofNat 64 s1.core.cur_vars + 64#64).toNat = s1.core.cur_vars + 64 := by
        rw [hcv1]; exact hil_val
      c0_hsteps_nogrp; c0_call hOneLit
      refine ⟨c, F0, F_cur, cut1, s1, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R,
        rfl, hcut1, hcf1, hm1, ?_⟩
      intro ol s2 m2 hlen2 hol hcv2 hfu2 hws2 h20 h1 h2 h0 hm2
      have hm2' := fullM6HdrMem_unfocus hm2
      rcases hol with rfl | rfl | rfl | rfl
      · rcases h0 rfl with ⟨cut2, hcut2_le, hcut2, hlvl2, hlle2, hcf2⟩
        c0_hsteps_nogrp
        · c0_call hFailed
          refine m6AnaFailedLitHdrSpec_of hinv.cfgOk hext1 hcut2 hlvl2 hcf2 hm2' ?_
          intro r ext3 s3 m3 hext3 _ hlen3 hr hcv3 hfu3 hws3 hr20 hr0 hr1 hm3
          exact hQ r ext3 s3 m3 hext3 hlen3 hr (hcv3.trans (hcv2.trans hcv1))
            (by rw [hfu3, hfu2, hfu1]; exact Nat.le_refl _) ⟨hws3.trans (hws2.trans hws1),
              fun heq => by
                have ⟨_, ho, hcl, _hdm⟩ := hr20 heq
                exact ⟨ho, Nat.le_trans hcl (Nat.le_trans hlle2 hcl1),
                  ho.2.2.2.2.2.trans hinv.sparseW.2.2.2.2.2.symm⟩⟩
            (fun heq => (hr20 heq).1) hr0
            (fun heq => ⟨FullM6HdrInvW.mk_inv hinv.cfgOk hext3 (hr1 heq).1,
              Nat.lt_of_lt_of_le (hr1 heq).2 (Nat.le_trans hlle2 hcl1)⟩) hm3
        · c0_call hDeduce
          refine m6Deduce1uipHdrSpec_of hinv.cfgOk hext1 hcut2 hlvl2 hcf2 hm2' ?_
          intro dst ext3 s3 m3 hext3 hlen3 hdst hcv3 hfu3 hws3 hr20 hr0 hr1 hr2 hm3
          rcases hdst with rfl | rfl | rfl | rfl
          · c0_hsteps_nogrp
            exact hQ 0#64 ext3 s3 m3 hext3 hlen3 (Or.inl rfl) (hcv3.trans (hcv2.trans hcv1))
              (by rw [hfu3, hfu2, hfu1]; exact Nat.le_refl _) ⟨hws3.trans (hws2.trans hws1),
                fun h => by cases h⟩
              (fun h => by cases h) hr0 (fun h => by cases h) hm3
          · rcases hr1 rfl with ⟨ho3, hcl3, htl_ge, htl_le, hnd3, hvals3, hlvl3, _hlvl0, hent3⟩
            refine wp_m6Hdr_focus_frame hm3 fun hm3f => ?_; c0_hsteps_nogrp; c0_call hMinShrink
            refine ⟨c, F0, F_cur, s3, m6ExtMem (m6ExtAddr c.hdr) ext3 ⋆ R, rfl, hlen3,
              ho3.2.1, ho3.2.2.1, htl_ge, htl_le, hnd3, hent3, hvals3, hlvl3, _hlvl0, hm3f, ?_⟩
            intro tmp4 tl4 mrk4 mstk4 mclr4 mcl4 mcf4 conf4 llits4 mrem4 sstk4 m4 _s4
              hlen4 ho4 hmc4 htl4_ge htl4_le htmp04 hnd4 h4lits hent4 hm4
            let s4 : FullState := { s3 with
              core := { s3.core with tmp := tmp4, tmp_len := tl4, mrk := mrk4, min_stk := mstk4,
                                     min_clr := mclr4, min_clr_len := mcl4, min_clr_full := mcf4 }
              scratch := { s3.scratch with conflicts := conf4, learned_lits := llits4,
                                           min_removed := mrem4, shrink_stk := sstk4 } }
            have hotfs4 : FullOtfsInvW c F0 F_cur s4 :=
              ⟨hlen4, ho4, hmc4, ho3.2.2.2.1,
                FullExtScratchOk.of_pres ho3.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => hr),
                ho3.2.2.2.2.2⟩
            have h4v : ∀ k < tl4, let l := (tmp4[k]?.getD 0#32).toNat
                l < 2 * s4.core.cur_vars ∧ s4.core.vals[l]?.getD 0#8 = 255#8 := fun k hk => by
              by_cases hk0 : k = 0
              · subst hk0
                simpa [s4, htmp04] using hvals3 0 (Nat.lt_of_lt_of_le Nat.zero_lt_one htl_ge)
              · exact ⟨(h4lits k (Nat.pos_of_ne_zero hk0) hk).1,
                  (h4lits k (Nat.pos_of_ne_zero hk0) hk).2.1⟩
            have hm4' := fullM6HdrMem_unfocus hm4
            c0_hsteps_nogrp
            refine wp_join_state0 (α := FullState × List (BitVec 64))
              (fun st m' => CoreShrinkPost c F0 F_cur s st.1 ∧ M6HdrExtOk st.2 ∧
                (FullM6HdrMem c st.2 st.1 ⋆ R) m') ?_ ?_
            · rintro J4 ⟨s5, ext5⟩ m5 ⟨⟨ho5, hpos5, htl5_ge, htl5_le, hnd5, hvals5, hlvl5,
                hent5, hcv5, hfu5, hcl5, hws5⟩, hext5, hm5⟩
              dsimp only at ho5 hpos5 htl5_ge htl5_le hnd5 hvals5 hlvl5
              dsimp only at hent5 hcv5 hfu5 hcl5 hws5 hext5 hm5 ⊢
              refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_
              have htl5_arr := ho5.1.core_ok.tmp_len_arr; have hcv5_le := ho5.1.core_ok.cur_vars_le
              have hcv5_b : s5.core.cur_vars < 2 * 2 ^ 28 := Nat.lt_of_le_of_lt hcv5_le hmaxv
              have htl5_max : s5.core.tmp_len < 2 * 2 ^ 28 := Nat.lt_of_le_of_lt htl5_le hcv5_b
              have htl5_fit : s5.core.tmp_len < 2 ^ 64 := by omega
              c0_hsteps_nogrp
              refine wp_while_state_pure (α := BitVec 64 × BitVec 64 × BitVec 32)
                (fun st => (st.2.1, st.2.2, st.1, ())) (fun st => s5.core.tmp_len - st.1.toNat)
                (fun st => 1 ≤ st.1.toNat ∧ st.1.toNat ≤ s5.core.tmp_len) ?_ ?_
              · intro J5 hJ5; exact hJ5 (1#64, 1#64, 0#32) ⟨by decide, htl5_ge⟩
              · intro J5 ⟨gi, glue, llvl⟩ ⟨hgi_lo, hgi_hi⟩ ih5
                dsimp only at hgi_lo hgi_hi ⊢; c0_hsteps_nogrp
                · have hgi_lt : gi.toNat < s5.core.tmp_len := by
                    simpa [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htl5_fit] using hc
                  have hlt_arr : gi.toNat < s5.core.tmp.length := by rw [htl5_arr]; omega
                  have hl_lt : (s5.core.tmp[gi.toNat]'hlt_arr).toNat < 2 * s5.core.cur_vars := by
                    simpa [List.getElem?_eq_getElem hlt_arr] using (hvals5 gi.toNat hgi_lt).1
                  have hv_lt : (BitVec.setWidth 64
                      ((s5.core.tmp[gi.toNat]'hlt_arr) >>> 1#32)).toNat < s5.core.lvl.length := by
                    have hb : ((s5.core.tmp[gi.toNat]'hlt_arr) >>> 1#32).toNat =
                        (s5.core.tmp[gi.toNat]'hlt_arr).toNat / 2 := by
                      simpa using bv32_lshr_1 (s5.core.tmp[gi.toNat]'hlt_arr)
                    rw [ho5.1.core_ok.lvl_len, BitVec.toNat_setWidth, hb]
                    have hdiv : (s5.core.tmp[gi.toNat]'hlt_arr).toNat / 2 < s5.core.cur_vars := by
                      omega
                    rw [Nat.mod_eq_of_lt (by omega : (s5.core.tmp[gi.toNat]'hlt_arr).toNat / 2 <
                      2 ^ 64)]
                    exact Nat.lt_of_lt_of_le hdiv hcv5_le
                  have hgi_add1 : (gi + 1#64).toNat = gi.toNat + 1 :=
                    bv64_add_small_eq (by rw [show (1#64 : BitVec 64).toNat = 1 from rfl]; omega)
                  c0_hsteps
                  · exact ih5 (gi + 1#64, glue + 1#64, s5.core.lvl[(BitVec.setWidth 64
                        ((s5.core.tmp[gi.toNat]'hlt_arr) >>> 1#32)).toNat]'hv_lt)
                      (by dsimp only; rw [hgi_add1]; omega)
                      ⟨by dsimp only; rw [hgi_add1]; omega, by dsimp only; rw [hgi_add1]; omega⟩
                  · exact ih5 (gi + 1#64, glue, llvl) (by dsimp only; rw [hgi_add1]; omega)
                      ⟨by dsimp only; rw [hgi_add1]; omega, by dsimp only; rw [hgi_add1]; omega⟩
                · refine wp_join_state0 (α := FullState)
                    (fun s6 m' => CoreShrinkPost c F0 F_cur s s6 ∧
                      (FullMem c s6 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext5 ⋆ R)) m') ?_ ?_
                  · rintro J6 s6 m6 ⟨⟨ho6, hpos6, htl6_ge, htl6_le, hnd6, hvals6, hlvl6,
                      hent6, hcv6, hfu6, hcl6, hws6⟩, hm6⟩
                    c0_hsteps_nogrp; c0_call hLearn
                    refine ⟨c, F0, F_cur, s6, m6ExtMem (m6ExtAddr c.hdr) ext5 ⋆ R, rfl,
                      ho6, hpos6, htl6_ge, htl6_le, hnd6, hvals6, hlvl6, hent6, hm6, ?_⟩
                    intro r s7 m7 hlen7 hr hcv7 hfu7 hws7 h20_7 h0_7 h1_7 hm7
                    exact hQ r ext5 s7 m7 hext5 hlen7 hr (hcv7.trans hcv6)
                      (Nat.le_trans hfu7 (by rw [hfu6]; exact Nat.le_refl _))
                      ⟨hws7.trans hws6, fun h => let ⟨_, hsp, hcl⟩ := h20_7 h
                        ⟨hsp.toOtfs, Nat.le_trans (Nat.le_of_lt hcl) hcl6,
                          hsp.2.2.2.2.2.trans hinv.sparseW.2.2.2.2.2.symm⟩⟩
                      (fun h => (h20_7 h).1) (fun h => (h0_7 h).toOtfs)
                      (fun h => ⟨FullM6HdrInvW.mk_inv hinv.cfgOk hext5 (h1_7 h).1,
                        Nat.lt_of_lt_of_le (h1_7 h).2 hcl6⟩)
                      (fullM6HdrMem_unfocus hm7)
                  · intro J6 hJ6; c0_hsteps_nogrp
                    · c0_call hEma
                      refine ⟨c, s5, m6ExtMem (m6ExtAddr c.hdr) ext5 ⋆ R, rfl, ho5.1, hm5f, ?_⟩
                      rintro ⟨⟩ s6 m6 hcore6 hlen6 hpres6 hm6
                      have heq6 := fullCoreState_agrees_with_scratch hcore6
                      exact hJ6 s6 m6 ⟨⟨m6o_otfs_of_safetySlice ho5 hlen6 heq6 hpres6.1,
                        by change 0 < s6.core.cur_level; rw [heq6]; exact hpos5,
                        by rw [heq6]; exact htl5_ge, by rw [heq6]; exact htl5_le,
                        by rw [heq6]; exact hnd5, by rw [heq6]; exact hvals5,
                        by rw [heq6]; exact hlvl5, by rw [heq6]; exact hent5,
                        by rw [heq6]; exact hcv5, by rw [heq6]; exact hfu5,
                        by change s6.core.cur_level ≤ _; rw [heq6]; exact hcl5,
                        hpres6.2.2.1.trans hws5⟩, hm6⟩
                    · exact hJ6 s5 m5 ⟨⟨ho5, hpos5, htl5_ge, htl5_le, hnd5, hvals5, hlvl5,
                        hent5, hcv5, hfu5, hcl5, hws5⟩, hm5f⟩
            · intro J4 hJ4; c0_hsteps_nogrp
              · c0_call hRestore
                refine m6RestoreBumpAnaHdrSpec_of hinv.cfgOk hext3 hlen4 hmc4.1 hm4' ?_
                intro mrk5 mcl5 sc5 ext5 m5 _s5 hlen5 hmz5 _ _ hpres5 hws5 hext5 _ hm5
                let s5 : FullState :=
                  { core := { s4.core with mrk := mrk5, min_clr_len := mcl5 }, scratch := sc5 }
                have ho5 := m6o_otfs_of_restoreBump hotfs4 hlen5 hmz5 hpres5
                refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_; c0_hsteps_nogrp; c0_call hTick
                refine ⟨c, s5, m6ExtMem (m6ExtAddr c.hdr) ext5 ⋆ R, rfl, hlen5, hm5f, ?_⟩
                rintro ⟨⟩ s6 m6 hcore6 hlen6 hpres6 hm6
                have heq6 := fullCoreState_agrees_with_scratch hcore6
                exact hJ4 (s6, ext5) m6
                  ⟨⟨m6o_otfs_of_safetySlice ho5 hlen6 heq6 hpres6.1,
                    by change 0 < s6.core.cur_level; rw [heq6]; change 0 < s3.core.cur_level; omega,
                    by rw [heq6]; exact htl4_ge,
                    by rw [heq6]; exact Nat.le_trans htl4_le htl_le,
                    by rw [heq6]; exact hnd4, by rw [heq6]; exact h4v,
                    fun k hk1 hk2 => by rw [heq6] at hk2 ⊢; exact (h4lits k hk1 hk2).2.2,
                    by rw [heq6]; exact hent4,
                    by change s6.core.cur_vars = _; rw [heq6]; exact hcv3.trans (hcv2.trans hcv1),
                    by change s6.core.fuel = _; rw [heq6]; rw [hfu3, hfu2, hfu1],
                    by change s6.core.cur_level ≤ _; rw [heq6, hcl3]
                       exact Nat.le_trans hlle2 hcl1,
                    hpres6.2.2.1.trans (hws5.trans (hws3.trans (hws2.trans hws1)))⟩,
                   hext5, fullM6HdrMem_unfocus hm6⟩
              · exact hJ4 (s4, ext3) m4 ⟨⟨hotfs4, by change 0 < s3.core.cur_level; omega,
                  htl4_ge, Nat.le_trans htl4_le htl_le, hnd4, h4v,
                  fun k hk1 hk2 => (h4lits k hk1 hk2).2.2, hent4,
                  hcv3.trans (hcv2.trans hcv1), by rw [hfu3, hfu2, hfu1],
                  by rw [hcl3]; exact Nat.le_trans hlle2 hcl1,
                  hws3.trans (hws2.trans hws1)⟩, hext3, hm4'⟩
          · rcases hr2 rfl with ⟨cut3, hcut3_le, hcut3, hcl3, hcf3⟩
            refine wp_m6Hdr_focus_frame hm3 fun hm3f => ?_; c0_hsteps_nogrp
            have ⟨hcut3k, hcf3k⟩ := m6o_cut_with_conflicts hcut3 hcf3 (s3.scratch.conflicts + 1#64)
            let s3k : FullState :=
              { s3 with scratch := { s3.scratch with conflicts := s3.scratch.conflicts + 1#64 } }
            refine wp_join_state0 (α := FullState × List (BitVec 64))
              (fun st m' => CoreCutJoin c F0 F_cur cut3 s st.1 ∧ M6HdrExtOk st.2 ∧
                (FullM6HdrMem c st.2 st.1 ⋆ R) m') ?_ ?_
            · rintro J4 ⟨s5, ext5⟩ m5 ⟨⟨hcut5_le, hcut5, hcf5, hcv5, hfu5, hcl5, hws5⟩, hext5, hm5⟩
              dsimp only at hcut5_le hcut5 hcf5 hcv5 hfu5 hcl5 hws5 hext5 hm5 ⊢
              refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_
              c0_hsteps_nogrp
              exact ih (iter + 1#64, s5, ext5) m5 (bv64_measure_sub_lt hlt)
                ⟨cut3, hcut5_le, hcut5, hcf5, hext5, hcv5, hfu5, hcl5, hws5,
                 by rw [bv64_add1_toNat hlt]; exact hlt, hm5f⟩
            · intro J4 hJ4; c0_hsteps_nogrp
              · refine wp_join_state0 (α := FullState)
                  (fun st m' => CoreCutJoin c F0 F_cur cut3 s st ∧
                    (FullMem c st ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext3 ⋆ R)) m') ?_ ?_
                · rintro J5 s4 m4 ⟨⟨hcut4_le, hcut4, hcf4, hcv4, hfu4, hcl4, hws4⟩, hm4⟩
                  c0_hsteps_nogrp; c0_call hRestore
                  refine m6RestoreBumpAnaHdrSpec_of hinv.cfgOk hext3 hcut4.1 hcut4.2.2.1.1
                    (fullM6HdrMem_unfocus hm4) ?_
                  intro mrk5 mcl5 sc5 ext5 m5 _s5 hlen5 hmz5 _ _ hpres5 hws5 hext5 _ hm5
                  let s5 : FullState :=
                    { core := { s4.core with mrk := mrk5, min_clr_len := mcl5 }, scratch := sc5 }
                  have ⟨hcut5, hcf5⟩ := m6o_cut_of_restoreBump hcut4 hcf4 hlen5 hmz5 hpres5
                  exact hJ4 (s5, ext5) m5
                    ⟨⟨hcut4_le, hcut5, hcf5, hcv4, hfu4, hcl4, hws5.trans hws4⟩, hext5, hm5⟩
                · intro J5 hJ5
                  have hJ_s3k : ∀ m',
                      (FullMem c s3k ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext3 ⋆ R)) m' →
                      J5 () m' := fun m' hm' =>
                    hJ5 s3k m' ⟨⟨hcut3_le, hcut3k, hcf3k, hcv3.trans (hcv2.trans hcv1),
                      by rw [hfu3, hfu2, hfu1], by rw [hcl3]; exact Nat.le_trans hlle2 hcl1,
                      hws3.trans (hws2.trans hws1)⟩, hm'⟩
                  c0_hsteps_nogrp
                  · have hpos3 : 0 < s3k.core.cur_vars := by
                      change 0 < s3.core.cur_vars
                      have : s3.core.cur_vars < 2 ^ 64 := by omega
                      simpa [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this] using hc
                    have htl0 : (0#64 : BitVec 64).toNat < s3k.core.tmp.length := by
                      rw [hcut3k.1.core_ok.tmp_len_arr]
                      exact Nat.lt_of_lt_of_le hpos3 (by
                        change s3.core.cur_vars ≤ c.max_vars; rw [hcv3, hcv2, hcv1]; exact hcv_le)
                    have hJ_tmp : ∀ {tp' : List (BitVec 32)} {m'}
                        (htp' : tp'.length = c.max_vars),
                        (FullMem c { s3k with core := { s3k.core with
                          tmp := tp', tmp_len := (1#64 : BitVec 64).toNat } } ⋆
                          (m6ExtMem (m6ExtAddr c.hdr) ext3 ⋆ R)) m' →
                        J5 () m' := by
                      intro tp' m' htp' hm'
                      have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
                      have htw := m6o_cut_with_tmp hcut3k hcf3k htp'
                        (tl' := (1#64 : BitVec 64).toNat) (by rw [h1]; omega)
                      refine hJ5 _ m' ⟨?_, hm'⟩
                      refine ⟨hcut3_le, htw.1, htw.2, ?_, ?_, ?_, ?_⟩
                      · dsimp only; exact hcv3.trans (hcv2.trans hcv1)
                      · dsimp only; rw [hfu3, hfu2, hfu1]
                      · dsimp only; rw [hcl3]; exact Nat.le_trans hlle2 hcl1
                      · dsimp only; exact hws3.trans (hws2.trans hws1)
                    refine wp_unroll_group fun Jlit hJlit => ?_
                    c0_hsteps_nogrp
                    · exact hJ_tmp (by simpa [List.length_set] using hcut3k.1.core_ok.tmp_len_arr)
                        hm
                    · refine wp_unroll_group fun Js hJs => ?_
                      have har_len := hcut3k.1.core_ok.arena_len_arr
                      have har_le := hcut3k.1.core_ok.arena_len_le
                      c0_hsteps_nogrp
                      · rename_i hlt_ar
                        dsimp only [s3k] at har_len har_le
                        have har_le64 : s3.core.arena_len < 2 ^ 64 := by omega
                        have hclt := s3.core.confl_ref.isLt
                        have href_lt : s3.core.confl_ref.toNat < s3.core.arena_len := by
                          simpa [BitVec.lt_def, BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt har_le64] using hlt_ar
                        have hsub_lt : 3 < s3.core.arena_len - s3.core.confl_ref.toNat := by
                          have hc' : 3 < (2 ^ 64 - s3.core.confl_ref.toNat +
                              s3.core.arena_len) % 2 ^ 64 := hc
                          omega
                        have h3 : (3#64 : BitVec 64).toNat = 3 := rfl
                        have har_lt : (s3k.core.confl_ref + 3#64).toNat <
                            s3k.core.arena.length := by
                          dsimp only [s3k]
                          rw [bv64_add_small_eq (by rw [h3]; omega), h3]; omega
                        c0_hsteps_nogrp
                        exact hJ_tmp (by simpa [List.length_set] using hcut3k.1.core_ok.tmp_len_arr)
                          hm
                      · exact hJ_s3k _ (by assumption)
                      · exact hJ_s3k _ (by assumption)
                      · exact hJ_s3k _ (by assumption)
                  · exact hJ_s3k _ (by assumption)
              · exact hJ4 (s3k, ext3) _ ⟨⟨hcut3_le, hcut3k, hcf3k,
                  hcv3.trans (hcv2.trans hcv1), by rw [hfu3, hfu2, hfu1],
                  by rw [hcl3]; exact Nat.le_trans hlle2 hcl1,
                  hws3.trans (hws2.trans hws1)⟩, hext3, fullM6HdrMem_unfocus (by assumption)⟩
          · rcases hr20 rfl with ⟨hu3, ho3, hcl3, _hdm3⟩
            c0_hsteps_nogrp
            exact hQ 20#64 ext3 s3 m3 hext3 hlen3 (Or.inr (Or.inr rfl))
              (hcv3.trans (hcv2.trans hcv1)) (by rw [hfu3, hfu2, hfu1]; exact Nat.le_refl _)
              ⟨hws3.trans (hws2.trans hws1),
                fun _ => ⟨ho3, Nat.le_trans hcl3 (Nat.le_trans hlle2 hcl1),
                  ho3.2.2.2.2.2.trans hinv.sparseW.2.2.2.2.2.symm⟩⟩
              (fun _ => hu3) (fun h => by cases h) (fun h => by cases h) hm3
      · c0_hsteps_nogrp
        exact hQ 1#64 ext1 s2 m2 hext1 hlen2 (Or.inr (Or.inl rfl)) (hcv2.trans hcv1)
          (by rw [hfu2, hfu1]; exact Nat.le_refl _) ⟨hws2.trans hws1, fun h => by cases h⟩
          (fun h => by cases h) (fun h => by cases h)
          (fun _ => ⟨FullM6HdrInvW.mk_inv hinv.cfgOk hext1 (h1 rfl).1,
            Nat.lt_of_lt_of_le (h1 rfl).2 hcl1⟩) hm2'
      · c0_hsteps_nogrp
        exact hQ 0#64 ext1 s2 m2 hext1 hlen2 (Or.inl rfl) (hcv2.trans hcv1)
          (by rw [hfu2, hfu1]; exact Nat.le_refl _) ⟨hws2.trans hws1, fun h => by cases h⟩
          (fun h => by cases h) (fun _ => h2 rfl) (fun h => by cases h) hm2'
      · c0_hsteps_nogrp
        have ⟨hu2, ho2, hcl2, _hdm2⟩ := h20 rfl
        exact hQ 20#64 ext1 s2 m2 hext1 hlen2 (Or.inr (Or.inr rfl)) (hcv2.trans hcv1)
          (by rw [hfu2, hfu1]; exact Nat.le_refl _) ⟨hws2.trans hws1,
            fun _ => ⟨ho2, Nat.le_trans hcl2 hcl1,
              ho2.2.2.2.2.2.trans hinv.sparseW.2.2.2.2.2.symm⟩⟩
          (fun _ => hu2) (fun h => by cases h) (fun h => by cases h) hm2'
    · c0_hsteps_nogrp
      exact hQ 0#64 ext1 s1 m1 hext1 hcut1.1 (Or.inl rfl) hcv1
        (by rw [hfu1]; exact Nat.le_refl _)
        ⟨hws1, fun h => by cases h⟩ (fun h => by cases h)
        (fun _ => hcut1.toOtfs) (fun h => by cases h) (fullM6HdrMem_unfocus hm1)

end AnalyzeCoreAndSwitchMode

end LeanQbe.T.Examples.Kissat.FullM6Orch
