/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7AnalyzeSortProof0
public import LeanQbe.T.Examples.Kissat.FullM7SearchProof0
public import LeanQbe.T.Examples.Kissat.FullM7WalkProof
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `M7` Spec-Wiring Bridges — Part 0: Gap A (`full_rephase_m7` under `fullWarmupSpec`)

Purely additive Gap-A closure (`0` edits to existing `FullM6*` / `FullM7*` modules):
1. `m7RephaseWarmupSpec` + `_of`/`_elim`/`_monoX`: `FullSparseInv`-preserving rephase contract
   allowing `fullWarmupSpec` (`"full_walk" ↦ FullM7Walk.full_walk_warmup_m7_body`) updates to
   `vals..oom` (since `FullSparseInv` guarantees `s.core.dense_mode = 0#64` and `FullArenaPermEq`
   preserves `FullArenaVarsNodup` & `FullExtScratchOk`).
2. `full_rephase_m7_warmup_wp`: parametric `(Γ : Env)` `Func.wp` proof for `m7RephaseFn` under
   `"full_backtrack" ↦ Full.fullBacktrackSpec`, `"full_walk" ↦ Full.fullWarmupSpec`, and
   `"full_log10_q16_m7" ↦ FullM7AnalyzeSort.m7Log10Q16Spec` (= `FullM7Search.m7Log10Q16Spec`).
3. `m7RephaseM6HdrSpec`, `full_rephase_m7_m6hdr_wp`, and `m7Hdr_call_m7Rephase_inv` for direct
   drop-in use inside `FullM7Proof` (`full_search_m6`).
4. Concrete `Mem 64` UNSAT non-vacuity (`nv_m7_rephase_warmup`, `XPost := False`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7SpecBridges

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

/-! ## 1. `FullSparseInv` & `FullArenaPermEq` Closure Helpers -/

theorem fullArenaPermEq_refl (k : FullCoreState) : FullArenaPermEq k k :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩

theorem fullArenaPermEq_trans {k1 k2 k3 : FullCoreState}
    (h12 : FullArenaPermEq k1 k2) (h23 : FullArenaPermEq k2 k3) : FullArenaPermEq k1 k3 := by
  refine ⟨h23.1.trans h12.1, h23.2.1.trans h12.2.1, fun r hr1 => ?_⟩
  have hr2 : r ∈ fullArenaClauseRefsCore k2 := h12.2.1 ▸ hr1
  obtain ⟨s12, g12, p12⟩ := h12.2.2 r hr1
  obtain ⟨s23, g23, p23⟩ := h23.2.2 r hr2
  exact ⟨s23.trans s12, g23.trans g12, p23.trans p12⟩

theorem fullArenaVarsNodup_of_perm {s s' : FullState}
    (hn : FullArenaVarsNodup s) (hp : FullArenaPermEq s.core s'.core) :
    FullArenaVarsNodup s' := by
  intro r hr hng
  have hr0 : r ∈ fullArenaClauseRefs s := by
    change r ∈ fullArenaClauseRefsCore s'.core at hr
    change r ∈ fullArenaClauseRefsCore s.core
    rw [hp.2.1] at hr; exact hr
  obtain ⟨_, hgb, hperm⟩ := hp.2.2 r hr0
  have hng0 : fullArenaClauseGarb s r = false := by
    change fullArenaClauseGarbCore s'.core r = false at hng
    change fullArenaClauseGarbCore s.core r = false
    rw [← hgb]; exact hng
  exact ((hperm.map (· / 2)).nodup_iff).mpr (hn r hr0 hng0)

private theorem fullSparseInv_of_backtrack {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s) {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' cl' : Nat} {unass' : BitVec 64} {sc' : FullScratch}
    (hlen' : ({ core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                                       trail_pos := tp', trail_end := te', propagated := prop',
                                       cur_level := cl', unassigned := unass' },
                scratch := sc' } : FullState).LengthsOk c)
    (hw' : ∀ F_cur, FullWitnessInv c F0 F_cur s.core →
      FullWitnessInv c F0 F_cur
        { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
                      trail_end := te', propagated := prop', cur_level := cl',
                      unassigned := unass' })
    (hpres : sc'.last_learned = s.scratch.last_learned ∧ sc'.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0
      { core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                               trail_pos := tp', trail_end := te', propagated := prop',
                               cur_level := cl', unassigned := unass' },
        scratch := sc' } := by
  obtain ⟨F_cur, hw⟩ := hsp.1.witness
  let s' : FullState :=
    { core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                            trail_pos := tp', trail_end := te', propagated := prop',
                            cur_level := cl', unassigned := unass' },
      scratch := sc' }
  refine ⟨⟨hlen', F_cur, hw' F_cur hw⟩, hsp.2.1, ?_,
    FullExtScratchOk.of_pres hsp.2.2.2.1 hpres (fun _ hr => hr), hsp.2.2.2.2⟩
  unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
  exact hsp.2.2.1

private theorem fullSparseInv_of_warmup {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' ftrl' fdec' : List (BitVec 32)}
    {te' prop' : Nat} {prob' unass' unfl' : BitVec 64}
    {wvec' arena' wstk' : List (BitVec 32)} {wlen' : Nat}
    {wu' fuel' ctype' cref' c0' c1' oom' : BitVec 64} {sc' : FullScratch}
    (hc' : FullCoreInv c F0
      { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', frame_trail := ftrl',
                              frame_dec := fdec', trail_end := te', propagated := prop',
                              probing := prob', unassigned := unass', unflushed := unfl',
                              wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                              wusable := wu', fuel := fuel', confl_type := ctype',
                              confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                              oom := oom' },
        scratch := sc' })
    (hperm : FullArenaPermEq s.core
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', frame_trail := ftrl', frame_dec := fdec', trail_end := te',
                    propagated := prop', probing := prob', unassigned := unass',
                    unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
                    wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
                    confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' })
    (hpres : FullExtScratchPres s
      { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', frame_trail := ftrl',
                              frame_dec := fdec', trail_end := te', propagated := prop',
                              probing := prob', unassigned := unass', unflushed := unfl',
                              wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                              wusable := wu', fuel := fuel', confl_type := ctype',
                              confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                              oom := oom' },
        scratch := sc' }) :
    FullSparseInv c F0
      { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', frame_trail := ftrl',
                              frame_dec := fdec', trail_end := te', propagated := prop',
                              probing := prob', unassigned := unass', unflushed := unfl',
                              wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                              wusable := wu', fuel := fuel', confl_type := ctype',
                              confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                              oom := oom' },
        scratch := sc' } := by
  let s' : FullState :=
    { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                            trail_pos := tp', frame_trail := ftrl', frame_dec := fdec',
                            trail_end := te', propagated := prop', probing := prob',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena',
                            wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                            confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                            confl_lit1 := c1', oom := oom' },
      scratch := sc' }
  refine ⟨hc', hsp.2.1, fullArenaVarsNodup_of_perm hsp.2.2.1 hperm,
    FullExtScratchOk.of_pres hsp.2.2.2.1 hpres ?_, hsp.2.2.2.2⟩
  intro r hr
  change r ∈ fullArenaClauseRefsCore s'.core
  dsimp only [s']
  rw [hperm.2.1]
  exact hr

private theorem fullSparseInv_with_scratch_eq {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s) {sc' : FullScratch} (hsc' : sc'.LengthsOk c)
    (hpres : sc'.last_learned = s.scratch.last_learned ∧ sc'.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 { core := s.core, scratch := sc' } := by
  obtain ⟨F_cur, hw⟩ := hsp.1.witness
  have hlen' : ({ core := s.core, scratch := sc' } : FullState).LengthsOk c :=
    ⟨hsp.1.lengths.core_ok, hsc'⟩
  refine ⟨⟨hlen', F_cur, hw⟩, hsp.2.1, ?_,
    FullExtScratchOk.of_pres hsp.2.2.2.1 hpres (fun _ hr => hr), hsp.2.2.2.2⟩
  unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
  exact hsp.2.2.1

/-! ## 2. Gap-A Specifications (`m7RephaseWarmupSpec`, `m7RephaseM6HdrSpec`) -/

/-- `full_rephase` contract for `FullM7AnalyzeSort.m7RephaseFn` calling `"full_walk"` at
`Full.fullWarmupSpec` (`FullM7.lean:229`). Requires `FullSparseInv c F0 s` (guaranteeing
`s.core.dense_mode = 0#64` for warmup) and preserves `FullSparseInv c F0 s'`, `FullArenaPermEq`,
and `fuel` monotonicity. -/
def m7RephaseWarmupSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' cl' prob' unass' unfl'
      wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m',
      FullSparseInv c F0
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', propagated := prop',
                                cur_level := cl', probing := prob', unassigned := unass',
                                unflushed := unfl', wvec := wvec', arena := arena',
                                wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' },
          scratch := sc' } →
      FullArenaPermEq s.core
        { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                      trl := trl', trail_pos := tp', frame_trail := ftrl',
                      frame_dec := fdec', trail_end := te', propagated := prop',
                      cur_level := cl', probing := prob', unassigned := unass',
                      unflushed := unfl', wvec := wvec', arena := arena',
                      wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                      confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                      confl_lit1 := c1', oom := oom' } →
      (s.scratch.stable ≠ 0#64 → cl' = 0) → cl' ≤ s.core.cur_level →
      fuel'.toNat ≤ s.core.fuel.toNat →
      FullExtScratchPres s
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', propagated := prop',
                                cur_level := cl', probing := prob', unassigned := unass',
                                unflushed := unfl', wvec := wvec', arena := arena',
                                wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' },
          scratch := sc' } →
      (s.core.probing = 0#64 → prob' = 0#64) →
      (FullMem c
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', propagated := prop',
                                cur_level := cl', probing := prob', unassigned := unass',
                                unflushed := unfl', wvec := wvec', arena := arena',
                                wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' },
          scratch := sc' } ⋆ R) m' → Q () m'

theorem m7RephaseWarmupSpec_of {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hsp : FullSparseInv c F0 s) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' cl' prob' unass' unfl'
      wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m',
      FullSparseInv c F0
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', propagated := prop',
                                cur_level := cl', probing := prob', unassigned := unass',
                                unflushed := unfl', wvec := wvec', arena := arena',
                                wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' },
          scratch := sc' } →
      FullArenaPermEq s.core
        { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                      trl := trl', trail_pos := tp', frame_trail := ftrl',
                      frame_dec := fdec', trail_end := te', propagated := prop',
                      cur_level := cl', probing := prob', unassigned := unass',
                      unflushed := unfl', wvec := wvec', arena := arena',
                      wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                      confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                      confl_lit1 := c1', oom := oom' } →
      (s.scratch.stable ≠ 0#64 → cl' = 0) → cl' ≤ s.core.cur_level →
      fuel'.toNat ≤ s.core.fuel.toNat →
      FullExtScratchPres s
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', propagated := prop',
                                cur_level := cl', probing := prob', unassigned := unass',
                                unflushed := unfl', wvec := wvec', arena := arena',
                                wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' },
          scratch := sc' } →
      (s.core.probing = 0#64 → prob' = 0#64) →
      (FullMem c
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', propagated := prop',
                                cur_level := cl', probing := prob', unassigned := unass',
                                unflushed := unfl', wvec := wvec', arena := arena',
                                wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' },
          scratch := sc' } ⋆ R) m' → Q () m') :
    m7RephaseWarmupSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩

theorem m7RephaseWarmupSpec_elim {h : BitVec 64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hs : m7RephaseWarmupSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
      ∀ vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' cl' prob' unass' unfl'
        wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m',
        FullSparseInv c F0
          { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                  trl := trl', trail_pos := tp', frame_trail := ftrl',
                                  frame_dec := fdec', trail_end := te', propagated := prop',
                                  cur_level := cl', probing := prob', unassigned := unass',
                                  unflushed := unfl', wvec := wvec', arena := arena',
                                  wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                  confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                  confl_lit1 := c1', oom := oom' },
            scratch := sc' } →
        FullArenaPermEq s.core
          { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                        trl := trl', trail_pos := tp', frame_trail := ftrl',
                        frame_dec := fdec', trail_end := te', propagated := prop',
                        cur_level := cl', probing := prob', unassigned := unass',
                        unflushed := unfl', wvec := wvec', arena := arena',
                        wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                        confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                        confl_lit1 := c1', oom := oom' } →
        (s.scratch.stable ≠ 0#64 → cl' = 0) → cl' ≤ s.core.cur_level →
        fuel'.toNat ≤ s.core.fuel.toNat →
        FullExtScratchPres s
          { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                  trl := trl', trail_pos := tp', frame_trail := ftrl',
                                  frame_dec := fdec', trail_end := te', propagated := prop',
                                  cur_level := cl', probing := prob', unassigned := unass',
                                  unflushed := unfl', wvec := wvec', arena := arena',
                                  wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                  confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                  confl_lit1 := c1', oom := oom' },
            scratch := sc' } →
        (s.core.probing = 0#64 → prob' = 0#64) →
        (FullMem c
          { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                  trl := trl', trail_pos := tp', frame_trail := ftrl',
                                  frame_dec := fdec', trail_end := te', propagated := prop',
                                  cur_level := cl', probing := prob', unassigned := unass',
                                  unflushed := unfl', wvec := wvec', arena := arena',
                                  wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                  confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                  confl_lit1 := c1', oom := oom' },
            scratch := sc' } ⋆ R) m' → Q () m' := hs

theorem m7RephaseWarmupSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : m7RephaseWarmupSpec xs m Q X) : m7RephaseWarmupSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

/-- `FullM6Hdr`-lifted rephase contract (`ext` untouched by `full_rephase_m7`). -/
def m7RephaseM6HdrSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' cl' prob' unass' unfl'
      wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m',
      FullM6HdrInv c F0 ext
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', propagated := prop',
                                cur_level := cl', probing := prob', unassigned := unass',
                                unflushed := unfl', wvec := wvec', arena := arena',
                                wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' },
          scratch := sc' } →
      FullArenaPermEq s.core
        { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                      trl := trl', trail_pos := tp', frame_trail := ftrl',
                      frame_dec := fdec', trail_end := te', propagated := prop',
                      cur_level := cl', probing := prob', unassigned := unass',
                      unflushed := unfl', wvec := wvec', arena := arena',
                      wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                      confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                      confl_lit1 := c1', oom := oom' } →
      (s.scratch.stable ≠ 0#64 → cl' = 0) → cl' ≤ s.core.cur_level →
      fuel'.toNat ≤ s.core.fuel.toNat →
      FullExtScratchPres s
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', propagated := prop',
                                cur_level := cl', probing := prob', unassigned := unass',
                                unflushed := unfl', wvec := wvec', arena := arena',
                                wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' },
          scratch := sc' } →
      (s.core.probing = 0#64 → prob' = 0#64) →
      (FullM6HdrMem c ext
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', propagated := prop',
                                cur_level := cl', probing := prob', unassigned := unass',
                                unflushed := unfl', wvec := wvec', arena := arena',
                                wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' },
          scratch := sc' } ⋆ R) m' → Q () m'

theorem m7RephaseM6HdrSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : m7RephaseM6HdrSpec xs m Q X) : m7RephaseM6HdrSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

/-! ## 3. Parametric `Func.wp` Proof (`full_rephase_m7_warmup_wp`) -/

private theorem bv64_add1_toNat_reph {k : BitVec 64} {n : Nat}
    (hk : k.toNat < n) (hn : n < 2 ^ 64) : (k + 1#64).toNat = k.toNat + 1 := by
  bv_omega

/-- Discharges `FullM7AnalyzeSort.full_rephase_m7_body` against `m7RephaseWarmupSpec` under
`"full_walk" ↦ Full.fullWarmupSpec` (`FullM7.lean:229`). -/
theorem full_rephase_m7_warmup_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hWalk : ∀ a m Q X, Full.fullWarmupSpec a m Q X →
      Γ "full_walk" [i64] [] a m Q X)
    (hLog : ∀ a m Q X, FullM7AnalyzeSort.m7Log10Q16Spec a m Q X →
      Γ "full_log10_q16_m7" [i64] [i64] a m Q X) :
    ∀ a m Q X, m7RephaseWarmupSpec a m Q X →
      Func.wp Γ full_rephase_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, s, R, rfl, hsp0, hm0, hQ⟩ := m7RephaseWarmupSpec_elim hs
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  obtain ⟨F_cur, hw0⟩ := hsp0.1.witness
  have hco0 := hsp0.1.lengths.core_ok
  have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
    have := hw0.cur_level_le; have := hco0.trail_end_le; have := hco0.cur_vars_le; omega
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := by have := hco0.cur_vars_le; omega
  unfold Func.wp full_rephase_m7_body
  c0_hsteps_nogrp
  · have hst0 : s.scratch.stable = 0#64 := by c0_cond hc; exact hc
    let sc_e : FullScratch := { s.scratch with rephase_limit := s.scratch.mode_confl_lim }
    have hsc_e : sc_e.LengthsOk c :=
      { hsp0.1.lengths.scratch_ok with walk_vals_len := hsp0.1.lengths.scratch_ok.walk_vals_len }
    have hsp_e := fullSparseInv_with_scratch_eq hsp0 hsc_e ⟨rfl, rfl⟩
    exact hQ s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
      s.core.frame_trail s.core.frame_dec s.core.trail_end s.core.propagated s.core.cur_level
      s.core.probing s.core.unassigned s.core.unflushed s.core.wvec s.core.arena s.core.wstk
      s.core.wlen s.core.wusable s.core.fuel s.core.confl_type s.core.confl_ref
      s.core.confl_lit0 s.core.confl_lit1 s.core.oom sc_e _
      hsp_e (fullArenaPermEq_refl _) (fun hst => absurd hst0 hst) (Nat.le_refl _)
      (Nat.le_refl _) ⟨rfl, rfl⟩ id (by assumption)
  · have hst_nz0 : s.scratch.stable ≠ 0#64 := by c0_cond hc; exact hc
    refine wp_join_group (ts := [])
      (fun () m1 => ∃ st1 : FullState,
        FullSparseInv c F0 st1 ∧ FullArenaPermEq s.core st1.core ∧
        st1.core = { s.core with vals := st1.core.vals, lvl := st1.core.lvl,
                                 rsns := st1.core.rsns, trl := st1.core.trl,
                                 trail_pos := st1.core.trail_pos, trail_end := st1.core.trail_end,
                                 propagated := st1.core.propagated, cur_level := 0,
                                 unassigned := st1.core.unassigned } ∧
        FullExtScratchPres s st1 ∧ (FullMem c st1 ⋆ R) m1)
      (fun _ () m1 ⟨st1, hsp1, hpm1, heq1, hpres1, hm1⟩ => ?_)
      (fun _ hJbt => ?_)
    · clear hm0
      have hcv1 : st1.core.cur_vars = s.core.cur_vars := by rw [heq1]
      have hcv_le : st1.core.cur_vars ≤ c.max_vars := hsp1.1.lengths.core_ok.cur_vars_le
      have hcv1_lt64 : st1.core.cur_vars < 2 ^ 64 := by omega
      let sc2 : FullScratch := { st1.scratch with rephased := st1.scratch.rephased + 1#64 }
      have hsc2 : sc2.LengthsOk c :=
        { hsp1.1.lengths.scratch_ok with walk_vals_len := hsp1.1.lengths.scratch_ok.walk_vals_len }
      let st2 : FullState := { core := st1.core, scratch := sc2 }
      have hsp2 := fullSparseInv_with_scratch_eq hsp1 hsc2 ⟨rfl, rfl⟩
      c0_hsteps_nogrp
      let RetP : Tup Val [] → Mem 64 → Prop := fun () m2 => ∃ st3 : FullState,
        FullSparseInv c F0 st3 ∧ FullArenaPermEq s.core st3.core ∧
        st3.core = { s.core with vals := st3.core.vals, flags := st3.core.flags,
                                 lvl := st3.core.lvl, rsns := st3.core.rsns, trl := st3.core.trl,
                                 trail_pos := st3.core.trail_pos,
                                 frame_trail := st3.core.frame_trail,
                                 frame_dec := st3.core.frame_dec, trail_end := st3.core.trail_end,
                                 propagated := st3.core.propagated, cur_level := 0,
                                 probing := st3.core.probing, unassigned := st3.core.unassigned,
                                 unflushed := st3.core.unflushed, wvec := st3.core.wvec,
                                 arena := st3.core.arena, wstk := st3.core.wstk,
                                 wlen := st3.core.wlen, wusable := st3.core.wusable,
                                 fuel := st3.core.fuel, confl_type := st3.core.confl_type,
                                 confl_ref := st3.core.confl_ref, confl_lit0 := st3.core.confl_lit0,
                                 confl_lit1 := st3.core.confl_lit1, oom := st3.core.oom } ∧
        st3.core.fuel.toNat ≤ s.core.fuel.toNat ∧ FullExtScratchPres s st3 ∧
        (s.core.probing = 0#64 → st3.core.probing = 0#64) ∧ (FullMem c st3 ⋆ R) m2
      refine wp_join_group (ts := []) RetP ?_ ?_
      · rintro _ ⟨⟩ m2 ⟨st3, hsp3, hpm3, heq3, hfu3, hpres3, hpr3, hm2⟩
        have hcv3 : st3.core.cur_vars = s.core.cur_vars := by rw [heq3]
        have hcv3_le : st3.core.cur_vars ≤ c.max_vars := hsp3.1.lengths.core_ok.cur_vars_le
        have hcv3_lt64 : st3.core.cur_vars < 2 ^ 64 := by omega
        c0_hsteps_nogrp
        refine wp_loop_inv
          (fun (k, ()) m3 => ∃ ptgt' : List (BitVec 8),
            k.toNat ≤ st3.core.cur_vars ∧ ptgt'.length = c.max_vars ∧
            (FullMem c { core := st3.core,
                         scratch := { st3.scratch with phases_target := ptgt' } } ⋆ R) m3)
          (fun (k, ()) _ => st3.core.cur_vars - k.toNat)
          (fun L hL => by
            c0_steps
            exact hL (0#64, ()) m2
              ⟨st3.scratch.phases_target, Nat.zero_le _,
                hsp3.1.lengths.scratch_ok.phases_target_len, hm2⟩)
          (fun L (k, ()) m3 ⟨ptgt', hk_le, hpt_l, hm3⟩ ih => ?_)
        · clear hm2
          have hph_l := hsp3.1.lengths.scratch_ok.phases_len
          c0_hsteps_nogrp
          · have hk_lt : k.toNat < st3.core.cur_vars := by
              c0_cond hc; rw [hcv1, Nat.mod_eq_of_lt hcv_lt64, ← hcv3] at hc; exact hc
            have hk1 := bv64_add1_toNat_reph hk_lt (by omega)
            exact ih (k + 1#64, ()) _ (by dsimp only; omega)
              ⟨ptgt'.set k.toNat (st3.scratch.phases[k.toNat]'(by omega)),
                by omega, by simp [hpt_l], hm⟩
          · let sc3b : FullScratch :=
              { st3.scratch with phases_target := ptgt', target_assigned := 0#64 }
            have hsc3b : sc3b.LengthsOk c :=
              { hsp3.1.lengths.scratch_ok with phases_target_len := hpt_l }
            let st3b : FullState := { core := st3.core, scratch := sc3b }
            refine wp_join_group (ts := [i64]) (fun _ m4 => (FullMem c st3b ⋆ R) m4)
              (fun _ (nc, ()) m4 hm4 => ?_) ?_
            · c0_hsteps_nogrp; c0_call hLog
              refine FullM7AnalyzeSort.m7Log10Q16Spec_of fun q _ _ => ?_
              c0_hsteps_nogrp
              refine wp_join_group (ts := [i64]) (fun _ m5 => (FullMem c st3b ⋆ R) m5)
                (fun _ (scaled, ()) m5 hm5 => ?_) ?_
              · clear hm4; c0_steps
                let sc4 : FullScratch := { sc3b with rephase_limit := sc3b.conflicts + scaled }
                have hsc4 : sc4.LengthsOk c := { hsc3b with walk_vals_len := hsc3b.walk_vals_len }
                have hsp4 := fullSparseInv_with_scratch_eq hsp3 hsc4 ⟨rfl, rfl⟩
                let st4 : FullState :=
                  { core :=
                      { s.core with vals := st3.core.vals, flags := st3.core.flags,
                                    lvl := st3.core.lvl, rsns := st3.core.rsns,
                                    trl := st3.core.trl, trail_pos := st3.core.trail_pos,
                                    frame_trail := st3.core.frame_trail,
                                    frame_dec := st3.core.frame_dec,
                                    trail_end := st3.core.trail_end,
                                    propagated := st3.core.propagated, cur_level := 0,
                                    probing := st3.core.probing,
                                    unassigned := st3.core.unassigned,
                                    unflushed := st3.core.unflushed, wvec := st3.core.wvec,
                                    arena := st3.core.arena, wstk := st3.core.wstk,
                                    wlen := st3.core.wlen, wusable := st3.core.wusable,
                                    fuel := st3.core.fuel, confl_type := st3.core.confl_type,
                                    confl_ref := st3.core.confl_ref,
                                    confl_lit0 := st3.core.confl_lit0,
                                    confl_lit1 := st3.core.confl_lit1, oom := st3.core.oom },
                    scratch := sc4 }
                have hst4 : ({ core := st3.core, scratch := sc4 } : FullState) = st4 :=
                  congrArg (fun k => ({ core := k, scratch := sc4 } : FullState)) heq3
                have hsp4' : FullSparseInv c F0 st4 := hst4 ▸ hsp4
                have hpm3' : FullArenaPermEq s.core st4.core := by
                  change FullArenaPermEq s.core st4.core
                  dsimp only [st4]; rw [← heq3]; exact hpm3
                have hpres4' : FullExtScratchPres s st4 := hst4 ▸ hpres3
                have hm5' : (FullMem c st4 ⋆ R) m := hst4 ▸ (by simpa [st3b, sc3b] using hm)
                exact hQ st3.core.vals st3.core.flags st3.core.lvl st3.core.rsns st3.core.trl
                  st3.core.trail_pos st3.core.frame_trail st3.core.frame_dec st3.core.trail_end
                  st3.core.propagated 0 st3.core.probing st3.core.unassigned st3.core.unflushed
                  st3.core.wvec st3.core.arena st3.core.wstk st3.core.wlen st3.core.wusable
                  st3.core.fuel st3.core.confl_type st3.core.confl_ref st3.core.confl_lit0
                  st3.core.confl_lit1 st3.core.oom sc4 m
                  hsp4' hpm3' (fun _ => rfl) (Nat.zero_le _) hfu3 hpres4' hpr3 hm5'
              · intro _ hJsc; c0_hsteps_nogrp
                · exact hJsc (_, ()) m4 hm4
                · refine wp_join_group (ts := [i64]) (fun _ m5 => (FullMem c st3b ⋆ R) m5)
                    (fun _ (nlim, ()) m5 hm5 => by c0_steps; exact hJsc (_, ()) m5 hm5) ?_
                  intro _ hJnl; c0_steps
                  · exact hJnl (100000000#64, ()) m4 hm4
                  · exact hJnl (_, ()) m4 hm4
            · intro _ hJnc; c0_steps
              · exact hJnc (_, ()) m hm
              · exact hJnc (1000000000000#64, ()) m hm
      · intro Jsel hJsel
        have hfl1 : st1.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [heq1]; exact Nat.le_refl _
        have heq1_cl0 : st1.core.cur_level = 0 := by rw [heq1]
        have heq1_pr : st1.core.probing = s.core.probing := by rw [heq1]
        have heq1_st3 : st1.core =
            { s.core with vals := st1.core.vals, flags := st1.core.flags, lvl := st1.core.lvl,
                          rsns := st1.core.rsns, trl := st1.core.trl,
                          trail_pos := st1.core.trail_pos, frame_trail := st1.core.frame_trail,
                          frame_dec := st1.core.frame_dec, trail_end := st1.core.trail_end,
                          propagated := st1.core.propagated, cur_level := 0,
                          probing := st1.core.probing, unassigned := st1.core.unassigned,
                          unflushed := st1.core.unflushed, wvec := st1.core.wvec,
                          arena := st1.core.arena, wstk := st1.core.wstk, wlen := st1.core.wlen,
                          wusable := st1.core.wusable, fuel := st1.core.fuel,
                          confl_type := st1.core.confl_type, confl_ref := st1.core.confl_ref,
                          confl_lit0 := st1.core.confl_lit0, confl_lit1 := st1.core.confl_lit1,
                          oom := st1.core.oom } := by
          rw [heq1]
        refine wp_join_group (fun () m_in => m_in = m) ?_ ?_
        · rintro _ ⟨⟩ m_in hm_eq; subst m_in
          have hm_base := hm; clear hm
          refine wp_loop_inv
            (fun (k, ()) m3 => ∃ ph' : List (BitVec 8),
              k.toNat ≤ st1.core.cur_vars ∧ ph'.length = c.max_vars ∧
              (FullMem c { st2 with scratch := { sc2 with phases := ph' } } ⋆ R) m3)
            (fun (k, ()) _ => st1.core.cur_vars - k.toNat)
            (fun L hL => by
              c0_hsteps
              exact hL (0#64, ()) m ⟨sc2.phases, Nat.zero_le _, hsc2.phases_len, hm_base⟩)
            (fun L (k, ()) m3 ⟨ph', hk_le, hph_l, hm3⟩ ih => ?_)
          have hpb_l := hsc2.phases_best_len
          c0_hsteps_nogrp
          · have hk_lt : k.toNat < st1.core.cur_vars := by
              c0_cond hc; rw [Nat.mod_eq_of_lt hcv1_lt64] at hc; exact hc
            have hk1 := bv64_add1_toNat_reph hk_lt (by omega)
            refine wp_join_group (ts := [])
              (fun () m4 => ∃ ph'' : List (BitVec 8), ph''.length = c.max_vars ∧
                (FullMem c { st2 with scratch := { sc2 with phases := ph'' } } ⋆ R) m4) ?_ ?_
            · rintro _ ⟨⟩ m4 ⟨ph'', hph'', hm4⟩
              c0_steps
              exact ih (k + 1#64, ()) m4 (by dsimp only; omega) ⟨ph'', by omega, hph'', hm4⟩
            · intro _ hJif; c0_hsteps_nogrp
              · c0_hsteps
                exact hJif () _ ⟨ph'.set k.toNat (sc2.phases_best[k.toNat]'(by omega)),
                  by simp [hph_l], hm⟩
              · exact hJif () m3 ⟨ph', hph_l, hm3⟩
          · let sc3 : FullScratch := { sc2 with phases := ph', best_assigned := 0#64 }
            have hsc3 : sc3.LengthsOk c := { hsc2 with phases_len := hph_l }
            exact hJsel () _ ⟨{ core := st1.core, scratch := sc3 },
              fullSparseInv_with_scratch_eq hsp1 hsc3 ⟨rfl, rfl⟩, hpm1, heq1_st3, hfl1,
              ⟨hpres1.1, hpres1.2⟩, fun hp => heq1_pr ▸ hp, hm⟩
        · intro Jbest hJbest
          c0_hsteps_nogrp
          · exact hJbest () m rfl
          · exact hJbest () m rfl
          · refine wp_join_group (ts := []) RetP ?_ ?_
            · rintro _ ⟨⟩ m_out hret; c0_steps; exact hJsel () m_out hret
            · intro _ hJ_after
              refine wp_join_group (ts := []) (fun () m_in => m_in = m) ?_ ?_
              · rintro _ ⟨⟩ m_in hm_eq; subst m_in
                c0_call hWalk
                refine ⟨c, F0, st2, R, rfl, hsp2.1, hsp2.2.2.2.2, hm,
                  fun vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' prob' unass' unfl'
                      wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m3
                      hc' hperm_w hfu_w hpres_w hpr_w hm3 => ?_⟩
                have hsp3 := fullSparseInv_of_warmup hsp2 hc' hperm_w hpres_w
                have hpm3 := fullArenaPermEq_trans hpm1 hperm_w
                have heq3_w :
                    { st2.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                    trl := trl', trail_pos := tp', frame_trail := ftrl',
                                    frame_dec := fdec', trail_end := te', propagated := prop',
                                    probing := prob', unassigned := unass', unflushed := unfl',
                                    wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                    wusable := wu', fuel := fuel', confl_type := ctype',
                                    confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                    oom := oom' } =
                    { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                  trl := trl', trail_pos := tp', frame_trail := ftrl',
                                  frame_dec := fdec', trail_end := te', propagated := prop',
                                  cur_level := 0, probing := prob', unassigned := unass',
                                  unflushed := unfl', wvec := wvec', arena := arena',
                                  wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                  confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                  confl_lit1 := c1', oom := oom' } := by
                  dsimp only [st2]; rw [heq1]
                have hfu_w' : fuel'.toNat ≤ s.core.fuel.toNat := by
                  have := hfu_w; change _ ≤ st1.core.fuel.toNat at this; rw [heq1] at this
                  exact this
                have hpr_w' : s.core.probing = 0#64 → prob' = 0#64 := fun hp =>
                  hpr_w (by change st1.core.probing = 0#64; rw [heq1_pr]; exact hp)
                c0_hsteps
                exact hJ_after () m3 ⟨_, hsp3, hpm3, heq3_w, hfu_w',
                  ⟨hpres_w.1.trans hpres1.1, hpres_w.2.trans hpres1.2⟩, hpr_w', hm3⟩
              · intro Jwalk hJwalk
                c0_hsteps_nogrp
                · exact hJwalk () m rfl
                · exact hJwalk () m rfl
                · refine wp_join_group (ts := []) RetP ?_ ?_
                  · rintro _ ⟨⟩ m_out hret; c0_steps; exact hJ_after () m_out hret
                  · intro _ hJ2
                    c0_hsteps_nogrp
                    · refine wp_loop_inv
                        (fun (k, ()) m3 => ∃ ph' : List (BitVec 8),
                          k.toNat ≤ st1.core.cur_vars ∧ ph'.length = c.max_vars ∧
                          (FullMem c { st2 with scratch := { sc2 with phases := ph' } } ⋆ R) m3)
                        (fun (k, ()) _ => st1.core.cur_vars - k.toNat)
                        (fun L hL => by
                          c0_hsteps
                          exact hL (0#64, ()) m ⟨sc2.phases, Nat.zero_le _, hsc2.phases_len, hm⟩)
                        (fun L (k, ()) m3 ⟨ph', hk_le, hph_l, hm3⟩ ih => ?_)
                      c0_hsteps
                      · have hk_lt : k.toNat < st1.core.cur_vars := by
                          c0_cond hc; rw [Nat.mod_eq_of_lt hcv1_lt64] at hc; exact hc
                        have hk1 := bv64_add1_toNat_reph hk_lt (by omega)
                        exact ih (k + 1#64, ()) _ (by dsimp only; omega)
                          ⟨ph'.set k.toNat _, by omega, by simp [hph_l], hm⟩
                      · let sc3 : FullScratch := { sc2 with phases := ph' }
                        have hsc3 : sc3.LengthsOk c := { hsc2 with phases_len := hph_l }
                        exact hJ2 () m3 ⟨{ core := st1.core, scratch := sc3 },
                          fullSparseInv_with_scratch_eq hsp1 hsc3 ⟨rfl, rfl⟩, hpm1, heq1_st3, hfl1,
                          ⟨hpres1.1, hpres1.2⟩, fun hp => heq1_pr ▸ hp, hm3⟩
                    · refine wp_loop_inv
                        (fun (k, ()) m3 => ∃ ph' : List (BitVec 8),
                          k.toNat ≤ st1.core.cur_vars ∧ ph'.length = c.max_vars ∧
                          (FullMem c { st2 with scratch := { sc2 with phases := ph' } } ⋆ R) m3)
                        (fun (k, ()) _ => st1.core.cur_vars - k.toNat)
                        (fun L hL => by
                          c0_hsteps
                          exact hL (0#64, ()) m ⟨sc2.phases, Nat.zero_le _, hsc2.phases_len, hm⟩)
                        (fun L (k, ()) m3 ⟨ph', hk_le, hph_l, hm3⟩ ih => ?_)
                      c0_hsteps
                      · have hk_lt : k.toNat < st1.core.cur_vars := by
                          c0_cond hc; rw [Nat.mod_eq_of_lt hcv1_lt64] at hc; exact hc
                        have hk1 := bv64_add1_toNat_reph hk_lt (by omega)
                        exact ih (k + 1#64, ()) _ (by dsimp only; omega)
                          ⟨ph'.set k.toNat _, by omega, by simp [hph_l], hm⟩
                      · let sc3 : FullScratch := { sc2 with phases := ph' }
                        have hsc3 : sc3.LengthsOk c := { hsc2 with phases_len := hph_l }
                        exact hJ2 () m3 ⟨{ core := st1.core, scratch := sc3 },
                          fullSparseInv_with_scratch_eq hsp1 hsc3 ⟨rfl, rfl⟩, hpm1, heq1_st3, hfl1,
                          ⟨hpres1.1, hpres1.2⟩, fun hp => heq1_pr ▸ hp, hm3⟩
    · c0_hsteps_nogrp
      · have hpos_cl : (0 : BitVec 64).toNat < s.core.cur_level := by
          c0_cond hc; rw [Nat.mod_eq_of_lt hcl_lt64] at hc; exact hc
        have hpos_mv : (0 : BitVec 64).toNat < c.max_vars := by
          have := hw0.cur_level_le; have := hco0.trail_end_le; have := hco0.cur_vars_le; omega
        c0_call hBacktrack
        refine ⟨c, s, R, rfl, hsp0.1.lengths, hcl_lt64, fun _ => hpos_mv, hw0.trail_lits_lt, hm0,
          fun vals1 lvl1 rsns1 trl1 tp1 te1 prop1 cl1 unass1 sc1 m1
              hlen1 _ _ hcl1 _ hsc_eq _ _ hwi1 _ hm1 => ?_⟩
        rcases hsc_eq with ⟨_, _, _, _, _, _, _, _, _, hsc_eq⟩
        have hcl1_eq : cl1 = 0 := by rw [hcl1]; exact Nat.min_zero _
        have hlen1' := hcl1_eq ▸ hlen1
        have hw1 := hwi1 F0 F_cur hw0 (Nat.zero_le _)
        have hw1' : FullWitnessInv c F0 F_cur _ := hcl1_eq ▸ hw1
        have hpres1 : sc1.last_learned = s.scratch.last_learned ∧
            sc1.extend_len = s.scratch.extend_len := ⟨by rw [hsc_eq], by rw [hsc_eq]⟩
        have hsp1 : FullSparseInv c F0 _ := fullSparseInv_of_backtrack hsp0 hlen1'
          (fun F_c hc => hwi1 F0 F_c hc (Nat.zero_le _) |> fun h => hcl1_eq ▸ h) hpres1
        exact hJbt () m1 ⟨_, hsp1, fullArenaPermEq_refl _, hcl1_eq ▸ rfl, hpres1, hcl1_eq ▸ hm1⟩
      · have hcl0 : s.core.cur_level = 0 := by
          c0_cond hc; rw [Nat.mod_eq_of_lt hcl_lt64] at hc; bv_omega
        refine hJbt () m ⟨s, hsp0, fullArenaPermEq_refl _, ?_, ⟨rfl, rfl⟩, hm0⟩
        rcases s with ⟨core, sc⟩; cases core; simp only at hcl0 ⊢; subst hcl0; rfl

/-- Identical-spec specialization using `FullM7Search.m7Log10Q16Spec`. -/
theorem full_rephase_m7_warmup_searchLog_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hWalk : ∀ a m Q X, Full.fullWarmupSpec a m Q X →
      Γ "full_walk" [i64] [] a m Q X)
    (hLog : ∀ a m Q X, FullM7Search.m7Log10Q16Spec a m Q X →
      Γ "full_log10_q16_m7" [i64] [i64] a m Q X) :
    ∀ a m Q X, m7RephaseWarmupSpec a m Q X →
      Func.wp Γ full_rephase_m7_body a m Q X :=
  full_rephase_m7_warmup_wp Γ hBacktrack hWalk fun ⟨x, ⟨⟩⟩ m Q X hs =>
    hLog (x, ()) m Q X (FullM7Search.m7Log10Q16Spec_of fun r hr h10 =>
      FullM7AnalyzeSort.m7Log10Q16Spec_elim hs r hr h10)

/-- Lifts `full_rephase_m7_warmup_wp` automatically over `FullM6HdrMem` (`m7RephaseM6HdrSpec`). -/
theorem full_rephase_m7_m6hdr_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hWalk : ∀ a m Q X, Full.fullWarmupSpec a m Q X →
      Γ "full_walk" [i64] [] a m Q X)
    (hLog : ∀ a m Q X, FullM7AnalyzeSort.m7Log10Q16Spec a m Q X →
      Γ "full_log10_q16_m7" [i64] [i64] a m Q X) :
    ∀ a m Q X, m7RephaseM6HdrSpec a m Q X →
      Func.wp Γ full_rephase_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩
  refine full_rephase_m7_warmup_wp Γ hBacktrack hWalk hLog (c.hdr, ()) m Q X
    ⟨c, F0, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv.sparse,
      fullM6HdrMem_focus_full hm, ?_⟩
  intro vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' cl' prob' unass' unfl'
    wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m'
    hsp' hperm hcl0 hcl_le hfu hpres hpr hm'
  exact hQ vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' cl' prob' unass' unfl'
    wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m'
    (FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk hsp') hperm hcl0 hcl_le hfu hpres hpr
    (fullM6HdrMem_unfocus_full hm')

/-- One-step `FullM6Hdr` call helper for `full_search_m6` (`FullM7.lean:199`) invoking
`"full_rephase"` at `m7RephaseWarmupSpec`. -/
theorem m7Hdr_call_m7Rephase_inv {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', m7RephaseWarmupSpec (c.hdr, ()) m Q' X' →
      Γ "full_rephase" [i64] [] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_rephase" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hΓ _ X ⟨c, F0, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv.sparse,
    fullM6HdrMem_focus_full hm, ?_⟩
  intro vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' cl' prob' unass' unfl'
    wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m'
    hsp' _ _ _ hfu _ _ hm'
  exact hk _ m' (FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk hsp') hfu
    (fullM6HdrMem_unfocus_full hm')

/-! ## 4. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`) -/

def m7RephaseNvTable : List SpecEntry :=
  [ ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  , ⟨"full_walk", [i64], [], Full.fullWarmupSpec, true⟩
  , ⟨"full_log10_q16_m7", [i64], [i64], FullM7AnalyzeSort.m7Log10Q16Spec, true⟩ ]

private theorem m7RephaseNvTable_nodup : (m7RephaseNvTable.map SpecEntry.name).Nodup := by
  decide

def nvBridgesRephaseState : FullState :=
  { nvOneLitState with
    core :=
      { nvOneLitState.core with
        vals := [0#8, 0#8]
        trail_end := 0
        propagated := 0 }
    scratch :=
      { nvOneLitState.scratch with
        stable := 1#64
        rephased := 1#64 } }

def nvBridgesRephaseMem : Mem 64 :=
  storeMem (storeMem (storeMem (storeMem (storeMem (storeMem nvOneLitMem
    i8 (nvOneLitCfg.pVals + 0#64) 0#8)
    i8 (nvOneLitCfg.pVals + 1#64) 0#8)
    i64 (nvOneLitCfg.hdr + 144) 0#64)
    i64 (nvOneLitCfg.hdr + 152) 0#64)
    i64 (nvOneLitCfg.hdr + 552) 1#64)
    i64 (nvOneLitCfg.hdr + 672) 1#64

private theorem nvBridgesRephaseMem_ok :
    (FullMem nvOneLitCfg nvBridgesRephaseState ⋆ emp) nvBridgesRephaseMem := by
  have hm0 : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  have h1 := (Full.FullArenaTactics.store_full_vals (i := 0) (v := 0#8) (by decide) hm0).2
  have h2 := (Full.FullArenaTactics.store_full_vals (i := 1) (v := 0#8) (by decide) h1).2
  have h3 := (Full.FullArenaTactics.store_full_trail_end (v := 0) (by decide) h2).2
  have h4 := (Full.FullArenaTactics.store_full_propagated (v := 0) (by decide) h3).2
  have h5 := (Full.FullArenaTactics.store_full_stable (v := 1#64) h4).2
  have h6 := (Full.FullArenaTactics.store_full_rephased (v := 1#64) h5).2
  simpa only [nvBridgesRephaseState, nvBridgesRephaseMem, nvOneLitState,
    show (([1#8, 0xFF#8] : List (BitVec 8)).set 0 0#8).set 1 0#8 = [0#8, 0#8] from rfl] using h6

private theorem nv_rephase_sparse :
    FullSparseInv nvOneLitCfg nvOneLitF0 nvBridgesRephaseState := by
  have hlen : nvBridgesRephaseState.LengthsOk nvOneLitCfg :=
    ⟨{ nvOneLit_lengths.core_ok with
       vals_len := rfl
       trail_end_le := Nat.zero_le _
       propagated_le := Nat.zero_le _ },
     { nvOneLit_lengths.scratch_ok with }⟩
  have hw : FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvBridgesRephaseState.core :=
    fullWitnessInv_empty
      (hext := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩)
      (hinc := rfl) (hal := rfl)
      (hwvec := fun l hl => by
        have hcv : nvBridgesRephaseState.core.cur_vars = 1 := rfl
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> exact ⟨rfl, rfl⟩)
      (hte := rfl) (hcl := rfl) (hft0 := rfl)
      (hvals := fun l hl => by
        have hcv : nvBridgesRephaseState.core.cur_vars = 1 := rfl
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl)
  have hmv : nvOneLitCfg.max_vars = 1 := rfl
  refine ⟨⟨hlen, [[0], [1]], hw⟩, ?_, ?_, ?_, rfl⟩
  · refine ⟨fun v hv => ?_, fun l hl => ?_⟩
    · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); decide
    · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
  · intro r hr _
    have hrefs : fullArenaClauseRefs nvBridgesRephaseState = [] := by
      simp [nvBridgesRephaseState, nvOneLitState, fullArenaClauseRefs, fullArenaClauseRefsCore,
        fullArenaScanRefs]
    simp [hrefs] at hr
  · refine ⟨FullLastLearnedWf.of_cleared fun i hi => ?_, by decide⟩
    simp only [nvBridgesRephaseState, nvOneLitState, nvOneLitScratch, List.getElem?_replicate,
      show i < 16 by omega, ↓reduceIte, Option.getD_some]

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_rephase_m7_warmup_wp`. -/
theorem nv_m7_rephase_warmup :
    Func.wp (Env.ofTable m7RephaseNvTable) full_rephase_m7_body
      (nvOneLitCfg.hdr, ()) nvBridgesRephaseMem
      (fun () m' => ∃ s' : FullState,
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.fuel.toNat ≤ nvBridgesRephaseState.core.fuel.toNat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hBt : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Env.ofTable m7RephaseNvTable "full_backtrack" [i64, i64] [] a m Q X :=
    fun a m Q X hs => Env.ofTable_of_mem (List.mem_of_getElem? (i := 0) rfl)
      m7RephaseNvTable_nodup (by
        have hs' : Full.fullBacktrackSpec a m Q (fun _ _ _ _ => False) := hs
        simpa [SpecEntry.eff] using hs')
  have hWk : ∀ a m Q X, Full.fullWarmupSpec a m Q X →
      Env.ofTable m7RephaseNvTable "full_walk" [i64] [] a m Q X :=
    fun a m Q X hs => Env.ofTable_of_mem (List.mem_of_getElem? (i := 1) rfl)
      m7RephaseNvTable_nodup (by
        have hs' : Full.fullWarmupSpec a m Q (fun _ _ _ _ => False) := hs
        simpa [SpecEntry.eff] using hs')
  have hLg : ∀ a m Q X, FullM7AnalyzeSort.m7Log10Q16Spec a m Q X →
      Env.ofTable m7RephaseNvTable "full_log10_q16_m7" [i64] [i64] a m Q X :=
    fun a m Q X hs => Env.ofTable_of_mem (List.mem_of_getElem? (i := 2) rfl)
      m7RephaseNvTable_nodup
      (by simpa [SpecEntry.eff] using FullM7AnalyzeSort.m7Log10Q16Spec_monoX hs)
  refine full_rephase_m7_warmup_wp (Env.ofTable m7RephaseNvTable) hBt hWk hLg
    (nvOneLitCfg.hdr, ()) nvBridgesRephaseMem _ _ ?_
  refine m7RephaseWarmupSpec_of nv_rephase_sparse nvBridgesRephaseMem_ok
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' hsp' _ _ _ hfu _ _ hm' => ?_)
  rw [sep_emp] at hm'
  exact ⟨_, hsp', hfu, hm'⟩

end LeanQbe.T.Examples.Kissat.FullM7SpecBridges
