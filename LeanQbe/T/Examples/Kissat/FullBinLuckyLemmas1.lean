module

public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.Full3
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Binary Watch / Unit Helpers & Preservation Lemmas (`Stage 4`, Part 1)

Builds on `FullInv2` and `Full3` to provide:
1. Local `FullBinLuckySpecs` (canonical Stage-4 shared invariants + callee `Spec`s + specs for
   `full_has_bin`, `full_add_bin`, `full_delete_bin_side`, `full_delete_binary`,
   `full_set_inactive`, `full_add_unit`, `full_lucky_scan`, `full_lucky_polar`, `full_lucky`).
2. Mode-indexed binary watch slice append & deletion preservation lemmas (`ModeWatchesInv`
   for both `dense_mode = 0` and `dense_mode ≠ 0`), plus `assignLevel0_preserves_fullCore`.
3. Parametric `(Γ : Env)` `Func.wp` proofs for `full_has_bin`, `full_add_bin`,
   `full_delete_bin_side`, `full_delete_binary`, and `full_set_inactive`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Local Stage-4 shared invariants and `FullBinLuckySpecs` -/

namespace FullBinLuckySpecs

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

def fullArenaNextSpec : Spec [i64, i32] [i32] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    Q (BitVec.ofNat 32 (fullArenaNextOff s.core.arena s.core.arena_len cref.toNat), ()) m

def fullWatchPushSpec : Spec [i64, i32, i32, i32, i32] [.bool] :=
  fun (h, lit, w0, w1, cnt, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧
      (cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32) ∧
      (cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) wvec' wstk' wlen' wusable' wsort' m',
        let s' : FullState :=
          { s with
            core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                  wusable := wusable' }
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
            s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat + 1]? = some w1)) →
        (ok = false →
          (lit.toNat < 2 * s.core.cur_vars →
            fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat ∧
            ∀ k < fullWatchSize s lit.toNat,
              s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
                s.core.wstk[fullWatchOff s lit.toNat + k]?) ∧
          (2 * s.core.cur_vars ≤ lit.toNat ∨ (cnt.toNat ≠ 1 ∧ cnt.toNat ≠ 2) ∨
            s' = s ∨ wusable' = 0#64)) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullAssignLvlSpec : Spec [i64, i32, i32, i32] [] := fun (h, lit, rsn, alvl, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    if s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
        s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8 then
      Q () m
    else
      let v := lit.toNat / 2
      let rsn' := if alvl = 0#32 then 0xFFFFFFFF#32 else rsn
      let unfl' := if alvl = 0#32 then s.core.unflushed + 1#64 else s.core.unflushed
      ∀ flags' unassigned' phases' m',
        flags'.length = c.max_vars → phases'.length = c.max_vars →
        (alvl ≠ 0#32 → flags' = s.core.flags) →
        let s' : FullState :=
          { s with
            core :=
              { s.core with
                vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                flags := flags', lvl := s.core.lvl.set v alvl
                rsns := s.core.rsns.set v rsn', trl := s.core.trl.set s.core.trail_end lit
                trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
                trail_end := s.core.trail_end + 1, unassigned := unassigned', unflushed := unfl' }
            scratch := { s.scratch with phases := phases' } }
        s'.LengthsOk c → (FullMem c s' ⋆ R) m' → Q () m'

def fullAssignSpec : Spec [i64, i32, i32] [] := fun (h, lit, rsn, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level < 2 ^ 32 ∧ (FullMem c s ⋆ R) m ∧
    if s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
        s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8 then
      Q () m
    else
      let v := lit.toNat / 2
      let alvl := BitVec.ofNat 32 s.core.cur_level
      let rsn' := if s.core.cur_level = 0 then 0xFFFFFFFF#32 else rsn
      let unfl' := if s.core.cur_level = 0 then s.core.unflushed + 1#64 else s.core.unflushed
      ∀ flags' unassigned' phases' m',
        flags'.length = c.max_vars → phases'.length = c.max_vars →
        (s.core.cur_level ≠ 0 → flags' = s.core.flags) →
        let s' : FullState :=
          { s with
            core :=
              { s.core with
                vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                flags := flags', lvl := s.core.lvl.set v alvl
                rsns := s.core.rsns.set v rsn', trl := s.core.trl.set s.core.trail_end lit
                trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
                trail_end := s.core.trail_end + 1, unassigned := unassigned', unflushed := unfl' }
            scratch := { s.scratch with phases := phases' } }
        s'.LengthsOk c → (FullMem c s' ⋆ R) m' → Q () m'

def fullBacktrackSpec : Spec [i64, i64] [] := fun (h, target_lvl, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧
    (∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    if s.core.cur_level ≤ target_lvl.toNat then
      Q () m
    else
      ∀ vals' lvl' rsns' trl' tp' te' prop' unassigned' ta' ba' pt' pb' hp' ps' hl' qsi'
        qss' m',
        let s' : FullState :=
          { s with
            core :=
              { s.core with
                vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
                trail_end := te', propagated := prop', cur_level := target_lvl.toNat,
                unassigned := unassigned' }
            scratch :=
              { s.scratch with
                target_assigned := ta', best_assigned := ba', phases_target := pt',
                phases_best := pb', heap := hp', pos := ps', heap_len := hl',
                q_search_idx := qsi', q_search_stamp := qss' } }
        s'.LengthsOk c → te' ≤ s.core.trail_end → prop' ≤ te' →
        (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
        (∀ l < 2 * s.core.cur_vars, vals'[l]?.getD 0#8 =
          if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat then
            s.core.vals[l]?.getD 0#8
          else 0#8) →
        (∀ F0 F_cur, FullWitnessInv c F0 F_cur s.core → FullWitnessInv c F0 F_cur s'.core) →
        (FullMem c s' ⋆ R) m' → Q () m'

def fullPropagateSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ s.core.dense_mode = 0#64 ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r vals' lvl' rsns' trl' tp' te' prop' unfl' wvec' arena' wstk' wlen' wu' fuel' ctype'
      cref' c0' c1' oom' scratch' m',
      let s' : FullState :=
        { s with
          core :=
            { s.core with
              vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
              trail_end := te', propagated := prop', unflushed := unfl', wvec := wvec',
              arena := arena', wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
              confl_type := ctype', confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
              oom := oom' }
          scratch := scratch' }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      s.core.trail_end ≤ te' → fuel'.toNat ≤ s.core.fuel.toNat →
      scratch'.last_learned = s.scratch.last_learned →
      scratch'.extend_len = s.scratch.extend_len →
      (FullArenaVarsNodup s → FullArenaVarsNodup s') →
      (∀ i < s.core.trail_end, trl'[i]? = s.core.trl[i]?) →
      (∀ i < s.core.trail_end,
        lvl'[(s.core.trl[i]?.getD 0#32).toNat / 2]? =
          s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?) →
      (∀ i, s.core.trail_end ≤ i → i < te' →
        (lvl'[(trl'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.core.cur_level) →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64)) →
      (r = 1#64 →
        fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧
        ((ctype' = 1#64 ∧ c0'.toNat < 2 * s.core.cur_vars ∧ c1'.toNat < 2 * s.core.cur_vars ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause [c0'.toNat, c1'.toNat]) ∧
          s'.core.vals[c0'.toNat]?.getD 0#8 = 0xFF#8 ∧
          s'.core.vals[c1'.toNat]?.getD 0#8 = 0xFF#8) ∨
         (ctype' = 2#64 ∧ cref'.toNat ∈ fullArenaClauseRefs s' ∧
          fullArenaClauseGarb s' cref'.toNat = false ∧
          ∀ l ∈ fullArenaClauseLits s' cref'.toNat, s'.core.vals[l]?.getD 0#8 = 0xFF#8))) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullAnalyzeSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
    s.core.dense_mode = 0#64 ∧
    ((s.core.confl_type = 1#64 ∧ s.core.confl_lit0.toNat < 2 * s.core.cur_vars ∧
      s.core.confl_lit1.toNat < 2 * s.core.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [s.core.confl_lit0.toNat, s.core.confl_lit1.toNat]) ∧
      s.core.vals[s.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
      s.core.vals[s.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8) ∨
     (s.core.confl_type ≠ 1#64 ∧ s.core.confl_ref.toNat ∈ fullArenaClauseRefs s ∧
      fullArenaClauseGarb s s.core.confl_ref.toNat = false ∧
      ∀ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r core' scratch' m',
      let s' : FullState := { core := core', scratch := scratch' }
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      core'.cur_vars = s.core.cur_vars →
      (∀ i < core'.trail_end, (core'.trl[i]?.getD 0#32).toNat < 2 * core'.cur_vars) →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 → FullSparseInv c F0 s') →
      (r = 1#64 → FullSparseInv c F0 s' ∧ core'.cur_level < s.core.cur_level) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ### Specifications for the 9 `Full3.lean` Binary/Unit/Lucky functions -/

def fullHasBinSpec : Spec [i64, i32, i32] [.bool] := fun (h, a, b, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r : Bool,
      (r = true →
        a.toNat < 2 * s.core.cur_vars ∧ b.toNat < 2 * s.core.cur_vars ∧
        a ≠ b ∧ a ≠ (b ^^^ 1#32) ∧
        ∀ F_cur, FullWitnessInv c F0 F_cur s.core →
          (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat])) →
      Q (r, ()) m

def fullAddBinSpec : Spec [i64, i32, i32] [i64] := fun (h, a, b, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ s.core.cur_level = 0 ∧
    (a.toNat < 2 * s.core.cur_vars → b.toNat < 2 * s.core.cur_vars →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat])) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' unfl' wvec' wstk' wlen' wu' nb' oom' inc'
      unass' phases' wsort' m',
      let s' : FullState :=
        { s with
          core :=
            { s.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', unflushed := unfl', wvec := wvec',
              wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb', oom := oom',
              inconsistent := inc', unassigned := unass' }
          scratch := { s.scratch with phases := phases', wsort := wsort' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      (r = 0#64 → s' = s) →
      (r = 2#64 → oom' = 1#64) →
      (r = 20#64 → F0.Unsat ∧ inc' = 1#64) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullDeleteBinSideSpec : Spec [i64, i32, i32] [] := fun (h, _lit, _other, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wusable' m',
      let s' : FullState :=
        { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wusable' } }
      s'.LengthsOk c →
      (∀ F_cur, FullWitnessInv c F0 F_cur s.core → FullWitnessInv c F0 F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullDeleteBinarySpec : Spec [i64, i32, i32] [] := fun (h, _a, _b, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wusable' nb' m',
      let s' : FullState :=
        { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wusable',
                                       num_binary := nb' } }
      s'.LengthsOk c →
      (∀ F_cur, FullWitnessInv c F0 F_cur s.core → FullWitnessInv c F0 F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullSetInactiveSpec : Spec [i64, i32, i32] [] := fun (h, v, _flag, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    if s.core.cur_vars ≤ v.toNat then
      Q () m
    else
      ∀ flags' unass' m',
        flags'.length = c.max_vars →
        let s' : FullState :=
          { s with core := { s.core with flags := flags', unassigned := unass' } }
        (FullMem c s' ⋆ R) m' → Q () m'

def fullAddUnitSpec : Spec [i64, i32] [.bool] := fun (h, lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    (lit.toNat / 2 < s.core.cur_vars →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat])) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unfl' inc' unass' phases' ta' ba' pt' pb'
      hp' ps' hl' qsi' qss' m',
      let s' : FullState :=
        { s with
          core :=
            { s.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', propagated := prop', cur_level := cl',
              unflushed := unfl', inconsistent := inc', unassigned := unass' }
          scratch :=
            { s.scratch with
              phases := phases', target_assigned := ta', best_assigned := ba',
              phases_target := pt', phases_best := pb', heap := hp', pos := ps',
              heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → cl' = 0 →
      (ok = false → s.core.cur_vars ≤ lit.toNat / 2 ∨ (F0.Unsat ∧ inc' = 1#64)) →
      (ok = true → lit.toNat / 2 < s.core.cur_vars) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullLuckyPolarSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r : BitVec 64, (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) → Q (r, ()) m

def fullLuckyScanSpec : Spec [i64, .bool, .bool] [i64] := fun (h, _pm, _fwd, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r core' scratch' m',
      let s' : FullState := { core := core', scratch := scratch' }
      s'.LengthsOk c → (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
      scratch'.extend_len = s.scratch.extend_len →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullLuckySpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r core' scratch' m',
      let s' : FullState := { core := core', scratch := scratch' }
      s'.LengthsOk c → core'.probing = 0#64 →
      (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
      scratch'.extend_len = s.scratch.extend_len →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

abbrev EnvSpec (Γ : Env) (name : Sym) {as rs : List Ty} (S : Spec as rs) : Prop :=
  ∀ xs m Q X, S xs m Q X → Γ name as rs xs m Q X

end FullBinLuckySpecs

open FullBinLuckySpecs

/-! ## 2. Scoped tactic helpers (`FullBinLuckyTactics`) -/

namespace FullBinLuckyTactics

theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

scoped macro "fbl_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)
scoped macro "fbl_unmdata" : tactic =>
  `(tactic| first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)
scoped macro "fbl_steps" : tactic =>
  `(tactic| (
      (try fbl_unmdata)
      (repeat fbl_strip)
      c0_steps
      repeat (any_goals (fbl_strip; repeat fbl_strip); c0_steps)))

open Lean Elab Tactic in
/-- Step straight-line ops, branches, and calls like `c0_steps`, stopping at `Expr.group` instead
of inlining join points (prevents exponential code duplication on `?:` before loops). -/
scoped elab "fbl_to_group" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let ty ← Lean.instantiateMVars (← g.getType)
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push g
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out.push g
    setGoals out.toList
  go 500

scoped macro "fbl_group" : tactic =>
  `(tactic| (
      (try fbl_unmdata)
      (repeat fbl_strip)
      fbl_to_group
      repeat (any_goals (fbl_strip; repeat fbl_strip); fbl_to_group)))

end FullBinLuckyTactics

open scoped FullArenaTactics FullBinLuckyTactics

/-! ## 3. Arithmetic & `BitVec` helpers -/

private theorem fbl_mask31_bit : ∀ i : Fin 32, (0x80000000#32)[i.val] = decide (i.val = 31) := by
  decide
private theorem fbl_maskLo31_bit : ∀ i : Fin 32, (0x7FFFFFFF#32)[i.val] = decide (i.val < 31) := by
  decide

theorem fbl_bv32_mask_bin (l : BitVec 32) (hl : l.toNat < 2 ^ 31 - 1) :
    let w : BitVec 32 := (l &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    w ≠ 0xFFFFFFFF#32 ∧ (w &&& 0x80000000#32) ≠ 0#32 ∧
      (w &&& 0x7FFFFFFF#32).toNat = l.toNat := by
  intro w
  have hbit31 : l[31] = false := by
    rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (by omega : l.toNat < 2 ^ 31)]; rfl
  have hand_hi : (w &&& 0x80000000#32) = 0x80000000#32 := by
    ext i hi; simp only [w, BitVec.getElem_and, BitVec.getElem_or, fbl_mask31_bit ⟨i, hi⟩]
    by_cases h31 : i = 31 <;> simp [h31]
  have hand_lo : (w &&& 0x7FFFFFFF#32) = l := by
    ext i hi
    simp only [w, BitVec.getElem_and, BitVec.getElem_or,
      fbl_mask31_bit ⟨i, hi⟩, fbl_maskLo31_bit ⟨i, hi⟩]
    by_cases h31 : i = 31
    · subst h31; simp [hbit31]
    · simp [h31, show i < 31 by omega]
  refine ⟨?_, ?_, congrArg BitVec.toNat hand_lo⟩
  · intro heq
    have := congrArg (fun x => x &&& 0x7FFFFFFF#32) heq
    rw [hand_lo] at this
    have hnat := congrArg BitVec.toNat this
    have hff : (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 := rfl
    rw [hff] at hnat; omega
  · rw [hand_hi]; decide

theorem fbl_bv8_slt0_iff (x : BitVec 8) :
    (x.signExtend 32).slt 0#32 = true ↔ 128 ≤ x.toNat := by
  rw [BitVec.slt, BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_zero, decide_eq_true_eq]
  rw [BitVec.toInt_eq_toNat_cond]; split <;> omega

theorem fbl_bv8_sgt0_iff (x : BitVec 8) :
    (0#32 : BitVec 32).slt (x.signExtend 32) = true ↔ 0 < x.toNat ∧ x.toNat < 128 := by
  rw [BitVec.slt, BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_zero, decide_eq_true_eq]
  rw [BitVec.toInt_eq_toNat_cond]; split <;> omega

theorem fbl_bv8_vals_pos {x : BitVec 8} (hdom : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    ((0#32 : BitVec 32).slt (x.signExtend 32) = true ↔ x = 1#8) ∧
    ((x.signExtend 32).slt 0#32 = true ↔ x = 0xFF#8) := by
  rcases hdom with rfl | rfl | rfl <;> constructor <;> decide

theorem fbl_bv8_vals_ge0 {x : BitVec 8} (hdom : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    ((0#32 : BitVec 32).sle (x.signExtend 32) = true ↔ x ≠ 0xFF#8) := by
  rcases hdom with rfl | rfl | rfl <;> decide

theorem fbl_bv32_xor1_toNat (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by
  simp [BitVec.toNat_xor]

theorem fbl_bv32_shr1_toNat (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [Nat.shiftRight_eq_div_pow]

theorem fbl_bv64_sub1_toNat {f : BitVec 64} (hf : f ≠ 0#64) :
    (f - 1#64).toNat = f.toNat - 1 := by
  have hpos : 0 < f.toNat := Nat.pos_of_ne_zero fun h0 =>
    hf (BitVec.eq_of_toNat_eq (by simpa using h0))
  bv_omega

/-! ## 4. Mode-indexed watch slice lemmas (append, relocate, binary deletion) -/

private theorem fbl_cnfClause_swap2 (a b : Nat) :
    ∀ α : Nat → Bool, (cnfClause [a, b]).Sat α ↔ (cnfClause [b, a]).Sat α := by
  intro α
  simp only [clause_sat_cnfClause_iff, List.mem_cons, List.not_mem_nil, or_false]
  constructor <;> rintro ⟨x, rfl | rfl, hs⟩
  · exact ⟨_, Or.inr rfl, hs⟩
  · exact ⟨_, Or.inl rfl, hs⟩
  · exact ⟨_, Or.inr rfl, hs⟩
  · exact ⟨_, Or.inl rfl, hs⟩

theorem fbl_entailsClause_swap2 {F : CNF Nat} {a b : Nat}
    (h : F.EntailsClause (cnfClause [a, b])) : F.EntailsClause (cnfClause [b, a]) := by
  rw [CNF.entails_clause_def] at h ⊢
  intro α hα; exact (fbl_cnfClause_swap2 a b α).mp (h α hα)

theorem WatchSliceOk.fbl_relocate {F0 F1 : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat}
    (hF : (cnfOfClauses F1).Entails (cnfOfClauses F0)) (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F0 k lit p rem) : WatchSliceOk F1 k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hflag hne (by omega)
      (CNF.entails_clause_trans hF hent)
      (ih (p' := p' + 1) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
  | @large p rem w0 cref hp hp1 hflag hlt href _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1)
      hflag hlt (hsub _ href)
      (ih (p' := p' + 2) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 2) (by omega))

theorem DenseWatchSliceOk.fbl_relocate {F0 F1 : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat}
    (hF : (cnfOfClauses F1).Entails (cnfOfClauses F0)) (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : DenseWatchSliceOk F0 k lit p rem) : DenseWatchSliceOk F1 k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hflag hne (by omega)
      (CNF.entails_clause_trans hF hent)
      (ih (p' := p' + 1) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
  | @occ p rem w0 cref hp hp1 hflag hsz hlt href _ ih =>
    refine .occ (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1)
      hflag hsz hlt (hsub _ href)
      (ih (p' := p' + 2) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 2) (by omega))

theorem WatchSliceOk.fbl_append_bin {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 : BitVec 32}
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    WatchSliceOk F_cur k' lit p' (rem + 1) := by
  induction h generalizing p' with
  | empty => exact .bin (by simpa using hw0) hflag hne hlt hent .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he ?_
    exact ih (p' := p' + 1)
      (fun idx hi => by simpa [show p' + 1 + idx = p' + (idx + 1) by omega,
        show p + 1 + idx = p + (idx + 1) by omega] using hwstk (idx + 1) (by omega))
      (by simpa [show p' + 1 + rem = p' + (rem + 1) by omega] using hw0)
  | @large p rem w cr hp hp1 hf hl hr _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hl (hsub _ hr) ?_
    exact ih (p' := p' + 2)
      (fun idx hi => by simpa [show p' + 2 + idx = p' + (idx + 2) by omega,
        show p + 2 + idx = p + (idx + 2) by omega] using hwstk (idx + 2) (by omega))
      (by simpa [show p' + 2 + rem = p' + (rem + 2) by omega] using hw0)

theorem DenseWatchSliceOk.fbl_append_bin {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 : BitVec 32}
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : DenseWatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    DenseWatchSliceOk F_cur k' lit p' (rem + 1) := by
  induction h generalizing p' with
  | empty => exact .bin (by simpa using hw0) hflag hne hlt hent .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he ?_
    exact ih (p' := p' + 1)
      (fun idx hi => by simpa [show p' + 1 + idx = p' + (idx + 1) by omega,
        show p + 1 + idx = p + (idx + 1) by omega] using hwstk (idx + 1) (by omega))
      (by simpa [show p' + 1 + rem = p' + (rem + 1) by omega] using hw0)
  | @occ p rem w cr hp hp1 hf hsz hl hr _ ih =>
    refine .occ (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hsz hl (hsub _ hr) ?_
    exact ih (p' := p' + 2)
      (fun idx hi => by simpa [show p' + 2 + idx = p' + (idx + 2) by omega,
        show p + 2 + idx = p + (idx + 2) by omega] using hwstk (idx + 2) (by omega))
      (by simpa [show p' + 2 + rem = p' + (rem + 2) by omega] using hw0)

theorem WatchSliceOk.fbl_append_slice {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p l1 l2 : Nat}
    (h1 : WatchSliceOk F_cur k lit p l1) (h2 : WatchSliceOk F_cur k lit (p + l1) l2) :
    WatchSliceOk F_cur k lit p (l1 + l2) := by
  induction h1 with
  | empty => simpa using h2
  | @bin p rem w h0 hf hn hl he _ ih =>
    rw [show p + (rem + 1) = (p + 1) + rem by omega] at h2
    rw [show rem + 1 + l2 = (rem + l2) + 1 by omega]; exact .bin h0 hf hn hl he (ih h2)
  | @large p rem w cr h0 h1 hf hl hr _ ih =>
    rw [show p + (rem + 2) = (p + 2) + rem by omega] at h2
    rw [show rem + 2 + l2 = (rem + l2) + 2 by omega]; exact .large h0 h1 hf hl hr (ih h2)

theorem DenseWatchSliceOk.fbl_append_slice {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p l1 l2 : Nat}
    (h1 : DenseWatchSliceOk F_cur k lit p l1)
    (h2 : DenseWatchSliceOk F_cur k lit (p + l1) l2) :
    DenseWatchSliceOk F_cur k lit p (l1 + l2) := by
  induction h1 with
  | empty => simpa using h2
  | @bin p rem w h0 hf hn hl he _ ih =>
    rw [show p + (rem + 1) = (p + 1) + rem by omega] at h2
    rw [show rem + 1 + l2 = (rem + l2) + 1 by omega]; exact .bin h0 hf hn hl he (ih h2)
  | @occ p rem w cr h0 h1 hf hsz hl hr _ ih =>
    rw [show p + (rem + 2) = (p + 2) + rem by omega] at h2
    rw [show rem + 2 + l2 = (rem + l2) + 2 by omega]; exact .occ h0 h1 hf hsz hl hr (ih h2)

/-- Binary watch push (`fullWatchPushSpec` with `cnt = 1`) preserves `ModeWatchesInv` across
both sparse and dense modes. -/
theorem fbl_watchPush_bin_preserves_modeWatches {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit w0 : BitVec 32} {ok : Bool}
    (hw : ModeWatchesInv F_cur k) (hlay : WatchStackLayout k') (hdm : k'.dense_mode = k.dense_mode)
    (hvars : k'.cur_vars = k.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hbin : (w0 &&& 0x80000000#32) ≠ 0#32 ∧ w0 ≠ 0xFFFFFFFF#32 ∧
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, (w0 &&& 0x7FFFFFFF#32).toNat]))
    (hother : ∀ l < 2 * k.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + idx]? = k.wstk[fullWatchOffCore k l + idx]?)
    (hok_true : ok = true →
      lit.toNat < 2 * k.cur_vars ∧
      fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat + 1 ∧
      (∀ idx < fullWatchSizeCore k lit.toNat,
        k'.wstk[fullWatchOffCore k' lit.toNat + idx]? =
          k.wstk[fullWatchOffCore k lit.toNat + idx]?) ∧
      k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat]? = some w0)
    (hok_false : ok = false → lit.toNat < 2 * k.cur_vars →
      fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat ∧
      ∀ idx < fullWatchSizeCore k lit.toNat,
        k'.wstk[fullWatchOffCore k' lit.toNat + idx]? =
          k.wstk[fullWatchOffCore k lit.toNat + idx]?) :
    ModeWatchesInv F_cur k' := by
  have hent_id : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ p => p
  by_cases hc : k.dense_mode = 0#64 <;> simp only [ModeWatchesInv, hdm, hc, ↓reduceIte] at hw ⊢
  · refine ⟨hlay, fun l hl => ?_⟩
    have hl0 : l < 2 * k.cur_vars := hvars ▸ hl
    by_cases hle : l = lit.toNat
    · subst hle; cases ok with
      | false =>
        obtain ⟨hsz, hslice⟩ := hok_false rfl hl0; rw [hsz]
        exact (hw.slices _ hl0).fbl_relocate hent_id (by omega) hsub hslice
      | true =>
        obtain ⟨_, hsz, hpre, hw0⟩ := hok_true rfl; rw [hsz]
        exact (hw.slices _ hl0).fbl_append_bin (by omega) hsub hpre hw0
          hbin.1 hbin.2.1 hbin.2.2.1 hbin.2.2.2
    · obtain ⟨hsz, hslice⟩ := hother l hl0 hle; rw [hsz]
      exact (hw.slices l hl0).fbl_relocate hent_id (by omega) hsub hslice
  · refine ⟨hlay, fun l hl => ?_⟩
    have hl0 : l < 2 * k.cur_vars := hvars ▸ hl
    by_cases hle : l = lit.toNat
    · subst hle; cases ok with
      | false =>
        obtain ⟨hsz, hslice⟩ := hok_false rfl hl0; rw [hsz]
        exact (hw.slices _ hl0).fbl_relocate hent_id (by omega) hsub hslice
      | true =>
        obtain ⟨_, hsz, hpre, hw0⟩ := hok_true rfl; rw [hsz]
        exact (hw.slices _ hl0).fbl_append_bin (by omega) hsub hpre hw0
          hbin.1 hbin.2.1 hbin.2.2.1 hbin.2.2.2
    · obtain ⟨hsz, hslice⟩ := hother l hl0 hle; rw [hsz]
      exact (hw.slices l hl0).fbl_relocate hent_id (by omega) hsub hslice

/-- Shrinking / compacting literal `lit`'s watch slice in `wstk` (e.g. `full_delete_bin_side`)
preserves `ModeWatchesInv` across both sparse and dense modes. -/
theorem fbl_compactSlice_preserves_modeWatches {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit q : Nat}
    (hw : ModeWatchesInv F_cur k) (hdm : k'.dense_mode = k.dense_mode)
    (hvars : k'.cur_vars = k.cur_vars) (hwl : k'.wlen = k.wlen)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hlit : lit < 2 * k.cur_vars)
    (hq_lo : fullWatchOffCore k lit ≤ q)
    (hq_hi : q ≤ fullWatchOffCore k lit + fullWatchSizeCore k lit)
    (hwvec_self : fullWatchOffCore k' lit = fullWatchOffCore k lit ∧
      fullWatchSizeCore k' lit = q - fullWatchOffCore k lit)
    (hwvec_other : ∀ l < 2 * k.cur_vars, l ≠ lit →
      fullWatchOffCore k' l = fullWatchOffCore k l ∧
      fullWatchSizeCore k' l = fullWatchSizeCore k l)
    (hwstk_other : ∀ idx, (idx < fullWatchOffCore k lit ∨
        fullWatchOffCore k lit + fullWatchSizeCore k lit ≤ idx) →
      k'.wstk[idx]? = k.wstk[idx]?)
    (hslice_new : if k.dense_mode = 0#64 then
        WatchSliceOk F_cur k' lit (fullWatchOffCore k lit) (q - fullWatchOffCore k lit)
      else DenseWatchSliceOk F_cur k' lit (fullWatchOffCore k lit) (q - fullWatchOffCore k lit)) :
    ModeWatchesInv F_cur k' := by
  have hlay_old := hw.layout
  have hlay' : WatchStackLayout k' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro l hl; rw [hvars] at hl
      by_cases hle : l = lit
      · subst hle; rw [hwvec_self.1, hwvec_self.2, hwl]
        have := hlay_old.bounds l hl; omega
      · obtain ⟨ho, hs⟩ := hwvec_other l hl hle; rw [ho, hs, hwl]; exact hlay_old.bounds l hl
    · intro l hl hpos; rw [hvars] at hl
      by_cases hle : l = lit
      · subst hle; rw [hwvec_self.1]; rw [hwvec_self.2] at hpos
        exact hlay_old.pos_off l hl (by omega)
      · obtain ⟨ho, hs⟩ := hwvec_other l hl hle; rw [ho]; rw [hs] at hpos
        exact hlay_old.pos_off l hl hpos
    · intro l1 l2 h1 h2 hne hp1 hp2; rw [hvars] at h1 h2
      by_cases hl1 : l1 = lit
      · subst hl1; obtain ⟨ho2, hs2⟩ := hwvec_other l2 h2 hne.symm
        rw [hwvec_self.1, hwvec_self.2, ho2, hs2]
        rw [hwvec_self.2] at hp1; rw [hs2] at hp2
        rcases hlay_old.disjoint l1 l2 h1 h2 hne (by omega) hp2 with hd | hd
        · left; omega
        · right; omega
      · by_cases hl2 : l2 = lit
        · subst hl2; obtain ⟨ho1, hs1⟩ := hwvec_other l1 h1 hl1
          rw [ho1, hs1, hwvec_self.1, hwvec_self.2]
          rw [hs1] at hp1; rw [hwvec_self.2] at hp2
          rcases hlay_old.disjoint l1 l2 h1 h2 hne hp1 (by omega) with hd | hd
          · left; omega
          · right; omega
        · obtain ⟨ho1, hs1⟩ := hwvec_other l1 h1 hl1; obtain ⟨ho2, hs2⟩ := hwvec_other l2 h2 hl2
          rw [ho1, hs1, ho2, hs2]; rw [hs1] at hp1; rw [hs2] at hp2
          exact hlay_old.disjoint l1 l2 h1 h2 hne hp1 hp2
    · intro l hl idx hidx; rw [hvars] at hl
      by_cases hle : l = lit
      · subst hle; rw [hwvec_self.1]; rw [hwvec_self.2] at hidx
        by_cases hc : k.dense_mode = 0#64
        · simp only [hc, ↓reduceIte] at hslice_new; exact hslice_new.ne_sentinel idx hidx
        · simp only [hc, ↓reduceIte] at hslice_new; exact hslice_new.ne_sentinel idx hidx
      · obtain ⟨ho, hs⟩ := hwvec_other l hl hle; rw [ho]; rw [hs] at hidx
        have hpos_l : 0 < fullWatchSizeCore k l := by omega
        have hout : fullWatchOffCore k l + idx < fullWatchOffCore k lit ∨
            fullWatchOffCore k lit + fullWatchSizeCore k lit ≤ fullWatchOffCore k l + idx := by
          by_cases hsz0 : fullWatchSizeCore k lit = 0
          · omega
          · rcases hlay_old.disjoint l lit hl hlit hle hpos_l (by omega) with hd | hd
            · exact Or.inl (by omega)
            · exact Or.inr (by omega)
        rw [hwstk_other _ hout]
        exact hlay_old.no_sentinel l hl idx hidx
  have hent_id : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ p => p
  have hreloc : ∀ l < 2 * k.cur_vars, l ≠ lit →
      ∀ idx < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + idx]? = k.wstk[fullWatchOffCore k l + idx]? := by
    intro l hl hne idx hidx
    obtain ⟨ho, hs⟩ := hwvec_other l hl hne; rw [ho]
    have hpos_l : 0 < fullWatchSizeCore k l := by omega
    have hout : fullWatchOffCore k l + idx < fullWatchOffCore k lit ∨
        fullWatchOffCore k lit + fullWatchSizeCore k lit ≤ fullWatchOffCore k l + idx := by
      by_cases hsz0 : fullWatchSizeCore k lit = 0
      · omega
      · rcases hlay_old.disjoint l lit hl hlit hne hpos_l (by omega) with hd | hd
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
    exact hwstk_other _ hout
  by_cases hc : k.dense_mode = 0#64 <;>
    simp only [ModeWatchesInv, hdm, hc, ↓reduceIte] at hw hslice_new ⊢
  · refine ⟨hlay', fun l hl => ?_⟩; rw [hvars] at hl
    by_cases hle : l = lit
    · subst hle; rw [hwvec_self.1, hwvec_self.2]; exact hslice_new
    · obtain ⟨ho, hs⟩ := hwvec_other l hl hle; rw [ho, hs]
      exact (hw.slices l hl).fbl_relocate hent_id (by omega) hsub
        (fun idx hi => by simpa [ho] using hreloc l hl hle idx hi)
  · refine ⟨hlay', fun l hl => ?_⟩; rw [hvars] at hl
    by_cases hle : l = lit
    · subst hle; rw [hwvec_self.1, hwvec_self.2]; exact hslice_new
    · obtain ⟨ho, hs⟩ := hwvec_other l hl hle; rw [ho, hs]
      exact (hw.slices l hl).fbl_relocate hent_id (by omega) hsub
        (fun idx hi => by simpa [ho] using hreloc l hl hle idx hi)

theorem fbl_watchPush_fail_preserves_modeWatches {F_cur : List (List Nat)} {k k' : FullCoreState}
    (hw : ModeWatchesInv F_cur k) (hlay' : WatchStackLayout k')
    (hdm : k'.dense_mode = k.dense_mode) (hvars : k'.cur_vars = k.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hall : ∀ l < 2 * k.cur_vars,
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + idx]? = k.wstk[fullWatchOffCore k l + idx]?) :
    ModeWatchesInv F_cur k' := by
  have hent : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ p => p
  by_cases hc : k.dense_mode = 0#64 <;>
    simp only [ModeWatchesInv, hdm, hc, ↓reduceIte] at hw ⊢
  · refine ⟨hlay', fun l hl => ?_⟩; rw [hvars] at hl
    obtain ⟨hs, hr⟩ := hall l hl; rw [hs]
    exact (hw.slices l hl).fbl_relocate hent (by omega) hsub
      (fun idx hi => by rw [hr idx hi])
  · refine ⟨hlay', fun l hl => ?_⟩; rw [hvars] at hl
    obtain ⟨hs, hr⟩ := hall l hl; rw [hs]
    exact (hw.slices l hl).fbl_relocate hent (by omega) hsub
      (fun idx hi => by rw [hr idx hi])

private theorem modeWatchSlice_bin_entails {F_cur : List (List Nat)} {k : FullCoreState}
    {src p rem : Nat} {w0 tgt : BitVec 32}
    (hsl : if k.dense_mode = 0#64 then WatchSliceOk F_cur k src p rem
           else DenseWatchSliceOk F_cur k src p rem)
    (hpos : 0 < rem) (hp : k.wstk[p]? = some w0)
    (hbin : (w0 &&& 0x80000000#32) ≠ 0#32)
    (heq : (w0 &&& 0x7FFFFFFF#32) = tgt) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [src, tgt.toNat]) := by
  by_cases hdm : k.dense_mode = 0#64 <;> simp only [hdm, ↓reduceIte] at hsl
  · cases hsl with
    | empty => omega
    | bin hp0 _ _ _ hent _ =>
      rw [hp] at hp0; cases hp0; rw [heq] at hent; exact hent
    | large hp0 _ hfl _ _ _ =>
      rw [hp] at hp0; cases hp0; exact absurd hfl hbin
  · cases hsl with
    | empty => omega
    | bin hp0 _ _ _ hent _ =>
      rw [hp] at hp0; cases hp0; rw [heq] at hent; exact hent
    | occ hp0 _ hfl _ _ _ _ =>
      rw [hp] at hp0; cases hp0; exact absurd hfl hbin

private theorem modeWatchSlice_bin_tail {F_cur : List (List Nat)} {k : FullCoreState}
    {src p rem : Nat} {w0 : BitVec 32}
    (hsl : if k.dense_mode = 0#64 then WatchSliceOk F_cur k src p rem
           else DenseWatchSliceOk F_cur k src p rem)
    (hpos : 0 < rem) (hp : k.wstk[p]? = some w0)
    (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) :
    if k.dense_mode = 0#64 then WatchSliceOk F_cur k src (p + 1) (rem - 1)
    else DenseWatchSliceOk F_cur k src (p + 1) (rem - 1) := by
  by_cases hdm : k.dense_mode = 0#64 <;> simp only [hdm, ↓reduceIte] at hsl ⊢
  · cases hsl with
    | empty => omega
    | bin _ _ _ _ _ hrest => simpa using hrest
    | large hp0 _ hfl _ _ _ =>
      rw [hp] at hp0; cases hp0; exact absurd hfl hbin
  · cases hsl with
    | empty => omega
    | bin _ _ _ _ _ hrest => simpa using hrest
    | occ hp0 _ hfl _ _ _ _ =>
      rw [hp] at hp0; cases hp0; exact absurd hfl hbin

private theorem modeWatchSlice_large_tail {F_cur : List (List Nat)} {k : FullCoreState}
    {src p rem : Nat} {w0 : BitVec 32}
    (hsl : if k.dense_mode = 0#64 then WatchSliceOk F_cur k src p rem
           else DenseWatchSliceOk F_cur k src p rem)
    (hpos : 0 < rem) (hp : k.wstk[p]? = some w0)
    (hlg : (w0 &&& 0x80000000#32) = 0#32) :
    2 ≤ rem ∧
    (if k.dense_mode = 0#64 then WatchSliceOk F_cur k src (p + 2) (rem - 2)
     else DenseWatchSliceOk F_cur k src (p + 2) (rem - 2)) := by
  by_cases hdm : k.dense_mode = 0#64 <;> simp only [hdm, ↓reduceIte] at hsl ⊢
  · cases hsl with
    | empty => omega
    | bin hp0 hfl _ _ _ _ =>
      rw [hp] at hp0; cases hp0; exact absurd hlg hfl
    | large _ _ _ _ _ hrest => exact ⟨by omega, by simpa using hrest⟩
  · cases hsl with
    | empty => omega
    | bin hp0 hfl _ _ _ _ =>
      rw [hp] at hp0; cases hp0; exact absurd hlg hfl
    | occ _ _ _ _ _ _ hrest => exact ⟨by omega, by simpa using hrest⟩

/-- Assigning `lit` at level `0` (when `s.core.cur_level = 0`, `s.core.vals[lit] = 0#8`, and
`F_cur` entails `[lit]`) preserves `FullWitnessInv` for the same `F_cur`. -/
theorem fbl_assignLevel0_preserves_fullWitness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hcl0 : s.core.cur_level = 0)
    {lit : BitVec 32} {flags' : List (BitVec 32)} {unassigned' : BitVec 64}
    {phases' : List (BitVec 8)}
    (hfll : flags'.length = c.max_vars) (hphl : phases'.length = c.max_vars)
    (hlit : lit.toNat < 2 * s.core.cur_vars)
    (hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hl0 : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat])) :
    let v := lit.toNat / 2
    let s' : FullState :=
      { s with
        core :=
          { s.core with
            vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := s.core.lvl.set v 0#32
            rsns := s.core.rsns.set v 0xFFFFFFFF#32, trl := s.core.trl.set s.core.trail_end lit
            trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
            trail_end := s.core.trail_end + 1, unassigned := unassigned'
            unflushed := s.core.unflushed + 1#64 }
        scratch := { s.scratch with phases := phases' } }
    s'.LengthsOk c ∧ FullWitnessInv c F0 F_cur s'.core := by
  intro v s'
  have hcl := hlen.core_ok
  have hsc := hlen.scratch_ok
  have hcv' : s'.core.cur_vars = s.core.cur_vars := rfl
  have hte' : s'.core.trail_end = s.core.trail_end + 1 := rfl
  have hclv' : s'.core.cur_level = 0 := hcl0
  have hte_lt : s.core.trail_end < s.core.cur_vars := hw.trail_end_lt_of_unassigned hlit hun
  have hnot_var : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hw.vals_zero_iff hlit).mp hun
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hv_lt : v < c.max_vars := by have := hcl.cur_vars_le; omega
  have hte_max : s.core.trail_end < c.max_vars := by have := hcl.cur_vars_le; omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by have := fullInv_max_vars_lt32 c; omega
  have htrl_get : ∀ i < s.core.trail_end + 1,
      (s'.core.trl[i]?.getD 0#32).toNat =
        if i = s.core.trail_end then lit.toNat else (s.core.trl[i]?.getD 0#32).toNat :=
    fun i _ => by
      by_cases he : i = s.core.trail_end
      · subst he; simp [s', List.getElem?_set_self (by rw [hcl.trl_len]; exact hte_max)]
      · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_get : ∀ w < s.core.cur_vars,
      (s'.core.lvl[w]?.getD 0#32).toNat =
        if w = v then 0 else (s.core.lvl[w]?.getD 0#32).toNat := fun w _ => by
    by_cases he : w = v
    · subst he; simp [s', List.getElem?_set_self (by rw [hcl.lvl_len]; exact hv_lt)]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * s.core.cur_vars,
      s'.core.vals[l]?.getD 0#8 =
        if l = lit.toNat ^^^ 1 then 0xFF#8 else if l = lit.toNat then 1#8
        else s.core.vals[l]?.getD 0#8 := fun l hl => by
    have hcm := hcl.cur_vars_le
    by_cases h1 : l = lit.toNat ^^^ 1
    · subst h1; dsimp only [s']; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by simp [hcl.vals_len]; omega)]; rfl
    · dsimp only [s']; simp only [h1, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = lit.toNat
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hcl.vals_len]; omega)]; rfl
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  have hrsn_get : ∀ w < s.core.cur_vars,
      s'.core.rsns[w]?.getD 0xFFFFFFFF#32 =
        if w = v then 0xFFFFFFFF#32 else s.core.rsns[w]?.getD 0xFFFFFFFF#32 := fun w _ => by
    by_cases he : w = v
    · subst he; simp [s', List.getElem?_set_self (by rw [hcl.rsns_len]; exact hv_lt)]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with
      vals_len := by simp [s', hcl.vals_len], flags_len := hfll,
      lvl_len := by simp [s', hcl.lvl_len], rsns_len := by simp [s', hcl.rsns_len],
      trl_len := by simp [s', hcl.trl_len], trail_pos_len := by simp [s', hcl.trail_pos_len],
      trail_end_le := by dsimp [s']; omega,
      propagated_le := by have := hcl.propagated_le; dsimp [s']; omega },
     { hsc with phases_len := hphl }⟩
  refine ⟨hlen', {
    ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
    cur_level_le := by rw [hclv']; exact Nat.zero_le _
    trail_lits_lt := fun i hi => by
      rw [htrl_get i (hte' ▸ hi)]; split
      · exact hlit
      · exact hw.trail_lits_lt i (by rw [hte'] at hi; omega)
    trail_vars_nodup := fun i j hi hj hveq => by
      rw [hte'] at hi hj; rw [htrl_get i hi, htrl_get j hj] at hveq
      split at hveq <;> split at hveq
      · omega
      · exact absurd hveq.symm (hnot_var j (by omega))
      · exact absurd hveq (hnot_var i (by omega))
      · exact hw.trail_vars_nodup i j (by omega) (by omega) hveq
    vals_domain := fun l hl => by
      rw [hcv'] at hl; rw [hvals_get l hl]
      split; · exact Or.inr (Or.inr rfl)
      split; · exact Or.inr (Or.inl rfl)
      exact hw.vals_domain l hl
    vals_true_iff := fun l hl => by
      rw [hcv'] at hl; rw [hvals_get l hl, hte']
      constructor
      · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
        · simp [hneg] at h1
        · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
          · exact ⟨s.core.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hpos]⟩
          · simp only [hpos, ↓reduceIte] at h1
            obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
            exact ⟨i, by omega,
              by rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
      · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
        by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte] at heq; subst heq; simp [Ne.symm hne_lit]
        · simp only [hie, ↓reduceIte] at heq
          have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
          have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
          have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
          simp only [h1, h2, ↓reduceIte]; exact (hw.vals_true_iff l hl).mpr ⟨i, by omega, heq⟩
    vals_false_iff := fun l hl => by
      rw [hcv'] at hl; rw [hvals_get l hl, hte']
      constructor
      · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
        · exact ⟨s.core.trail_end, by omega, by
            rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hneg]; exact (litNeg_litNeg _).symm⟩
        · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
          · simp [hpos] at h1
          · simp only [hpos, ↓reduceIte] at h1
            obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h1
            exact ⟨i, by omega,
              by rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
      · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
        by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte] at heq
          have hl_eq : l = lit.toNat ^^^ 1 := by
            have h := congrArg litNeg heq; have h1 : litNeg (l ^^^ 1) = l := litNeg_litNeg l
            rw [h1] at h; exact h.symm
          simp [hl_eq]
        · simp only [hie, ↓reduceIte] at heq
          have hlv : l / 2 ≠ v := by
            have h := hnot_var i (by omega); rw [heq] at h; rwa [fullInv_var_xor1] at h
          have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
          have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
          simp only [h1, h2, ↓reduceIte]; exact (hw.vals_false_iff l hl).mpr ⟨i, by omega, heq⟩
    lvl_le := fun i hi => by
      rw [hte'] at hi; rw [hclv', htrl_get i hi]
      by_cases hie : i = s.core.trail_end
      · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte]
        rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)]
        simp only [hnot_var i hilt, ↓reduceIte]
        have := hw.lvl_le i hilt; omega
    dec_earliest := fun i j hi hj hleq hdec => by
      have hlj : (s'.core.lvl[(s'.core.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ 0 := by
        rw [hte'] at hj; rw [htrl_get j hj]
        by_cases hje : j = s.core.trail_end
        · simp only [hje, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp
        · have hjlt : j < s.core.trail_end := by omega
          simp only [hje, ↓reduceIte]
          rw [hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega)]
          simp only [hnot_var j hjlt, ↓reduceIte]
          have := hw.lvl_le j hjlt; omega
      omega
    levels_inhabited := fun L hL1 hLle => by rw [hclv'] at hLle; omega
    level0_sound := fun i hi hli => by
      rw [hte'] at hi; rw [htrl_get i hi] at hli ⊢
      by_cases hie : i = s.core.trail_end
      · simp only [hie, ↓reduceIte]; exact hl0
      · have hilt : i < s.core.trail_end := by omega
        rw [ite_eq_right hie] at hli ⊢
        rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)] at hli
        rw [ite_eq_right (hnot_var i hilt)] at hli; exact hw.level0_sound i hilt hli
    trail_pos_inv := fun i hi => by
      rw [hte'] at hi; rw [htrl_get i hi]
      by_cases hie : i = s.core.trail_end
      · subst hie; simp only [↓reduceIte]; dsimp only [s']
        rw [List.getElem?_set_self (by rw [hcl.trail_pos_len]; exact hv_lt),
          Option.getD_some, bv32_ofNat_toNat hte_lt32]
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte]
        have hnv := hnot_var i hilt
        dsimp only [s']; rw [List.getElem?_set_ne (Ne.symm hnv)]; exact hw.trail_pos_inv i hilt
    level0_rsn_none := fun idx hidx hli => by
      rw [hte'] at hidx; rw [htrl_get idx hidx] at hli ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte]
        rw [hrsn_get v (by omega)]; simp
      · have hilt : idx < s.core.trail_end := by omega
        rw [ite_eq_right hie] at hli ⊢
        have hnv := hnot_var idx hilt
        rw [hlvl_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hli
        rw [ite_eq_right hnv] at hli
        rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)]
        simp only [hnv, ↓reduceIte]; exact hw.level0_rsn_none idx hilt hli
    frame_trail_lt := fun L hL => by
      rw [hclv'] at hL
      have hL0 : L = 0 := by omega
      subst hL0
      exact Nat.le_trans (hw.frame_trail_lt 0 (by omega)) (Nat.le_succ _)
    frame_trail_mono := fun L1 L2 _ h2 => by
      rw [hclv'] at h2
      have : L1 = 0 := by omega
      have : L2 = 0 := by omega
      subst_vars; exact Nat.le_refl _
    frame_trail_before_lt := fun L hL1 hLle => by rw [hclv'] at hLle; omega
    frame_dec_lt := fun L hL1 hLle => by rw [hclv'] at hLle; omega
    reason_inv := fun idx hidx hne => by
      rw [hte'] at hidx; rw [htrl_get idx hidx] at hne ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hne
        rw [hrsn_get v (by omega)] at hne; simp at hne
      · have hilt : idx < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte] at hne ⊢
        have hnv := hnot_var idx hilt
        rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hne ⊢
        simp only [hnv, ↓reduceIte] at hne ⊢
        have hrs := hw.reason_inv idx hilt hne
        by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hbin] at hrs ⊢
          obtain ⟨m, hm, hmeq, hlvl_le⟩ := hrs.2.2
          refine ⟨hrs.1, hrs.2.1, m, by omega, ?_, ?_⟩
          · rw [htrl_get m (by omega)]; simp [show m ≠ s.core.trail_end by omega, hmeq]
          · have hot_v : ((s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
                0xFFFFFFFF#32) &&& 0x7FFFFFFF#32).toNat / 2 ≠ v := by
              intro heqv; have hme := hnot_var m (by omega); rw [hmeq] at hme
              exact hme (by simpa [fullInv_var_xor1] using heqv)
            rw [hlvl_get _ (by omega), hlvl_get _ (by have := hw.trail_lits_lt idx hilt; omega)]
            rw [ite_eq_right hot_v, ite_eq_right hnv]; exact hlvl_le
        · rw [ite_eq_right hbin] at hrs ⊢
          refine ⟨hrs.1, hrs.2.1, fun q hq => ?_⟩
          have hq' : q ∈ fullArenaClauseLitsCore s.core
              (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
                0xFFFFFFFF#32).toNat := by
            simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s'] using hq
          refine (hrs.2.2 q hq').elim Or.inl fun ⟨m, hm, hmeq, hlvl_le⟩ =>
            Or.inr ⟨m, by omega, ?_, ?_⟩
          · rw [htrl_get m (by omega)]; simp [show m ≠ s.core.trail_end by omega, hmeq]
          · have hq_lt : q < 2 * s.core.cur_vars := hw.arena.lits_lt _ hrs.1 hrs.2.1 q hq'
            have hqv : q / 2 ≠ v := by
              intro heqv; have hme := hnot_var m (by omega); rw [hmeq] at hme
              exact hme (by simpa [fullInv_var_xor1] using heqv)
            rw [hlvl_get _ (by omega), hlvl_get _ (by have := hw.trail_lits_lt idx hilt; omega)]
            simpa [hnv, hqv] using hlvl_le
    reason_lit_mem := fun idx hidx hne hlg => by
      rw [hte'] at hidx; rw [htrl_get idx hidx] at hne hlg ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hne
        rw [hrsn_get v (by omega)] at hne; simp at hne
      · have hilt : idx < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte] at hne hlg ⊢
        have hnv := hnot_var idx hilt
        rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hne hlg ⊢
        simp only [hnv, ↓reduceIte] at hne hlg ⊢
        simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s'] using
          hw.reason_lit_mem idx hilt hne hlg }⟩

/-! ## 5. `Func.wp` proof for `full_has_bin` -/

theorem full_has_bin_wp (Γ : Env) :
    ∀ args m Q X, fullHasBinSpec args m Q X → Func.wp Γ full_has_bin_body args m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  obtain ⟨F_cur, hw⟩ := hinv.witness
  have hcl := hinv.lengths.core_ok
  have hmx := c.hmaxv; have hwc := c.hwcap; unfold dimacsBound at hmx hwc
  have hcv_le := hcl.cur_vars_le; have hwvl := hcl.wvec_len; have hwl := hcl.wstk_len_arr
  have hwle := hcl.wlen_le
  fbl_group
  · exact hQ false fun hf => by cases hf
  · exact hQ false fun hf => by cases hf
  · exact hQ false fun hf => by cases hf
  · exact hQ false fun hf => by cases hf
  · have ha_lt : a.toNat < 2 * s.core.cur_vars := by c0_bound
    have hb_lt : b.toNat < 2 * s.core.cur_vars := by c0_bound
    have hne_ab : a ≠ b := by c0_bound
    have hne_neg : a ≠ b ^^^ 1#32 := by c0_bound
    have hsa_idx : ((a.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * a.toNat + 1 := by
      have : a.toNat < 2 ^ 30 := by omega
      bv_omega
    have hsb_idx : ((b.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * b.toNat + 1 := by
      have : b.toNat < 2 ^ 30 := by omega
      bv_omega
    fbl_group
    have h1_64 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
    refine wp_join_group
      (fun (src, ()) mJ => mJ = m ∧
        (((s.core.wvec[2 * a.toNat + 1]'(by omega)).toNat ≤
            (s.core.wvec[2 * b.toNat + 1]'(by omega)).toNat ∧ src = a) ∨
         ((s.core.wvec[2 * b.toNat + 1]'(by omega)).toNat <
            (s.core.wvec[2 * a.toNat + 1]'(by omega)).toNat ∧ src = b)))
      ?_ (fun J hJ => by
        fbl_group
        · simp only [h1_64, Nat.mod_eq_of_lt (by omega : 2 * a.toNat + 1 < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : 2 * b.toNat + 1 < 2 ^ 64)] at hc
          exact hJ _ _ ⟨rfl, Or.inl ⟨hc, rfl⟩⟩
        · simp only [h1_64, Nat.mod_eq_of_lt (by omega : 2 * a.toNat + 1 < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : 2 * b.toNat + 1 < 2 ^ 64)] at hc
          exact hJ _ _ ⟨rfl, Or.inr ⟨by omega, rfl⟩⟩)
    rintro _ ⟨src, ⟨⟩⟩ mJ ⟨hmJ, hsrc_spec⟩
    subst hmJ
    fbl_group
    refine wp_join_group
      (fun (tgt, ()) mK => mK = mJ ∧
        (((s.core.wvec[2 * a.toNat + 1]'(by omega)).toNat ≤
            (s.core.wvec[2 * b.toNat + 1]'(by omega)).toNat ∧ tgt = b) ∨
         ((s.core.wvec[2 * b.toNat + 1]'(by omega)).toNat <
            (s.core.wvec[2 * a.toNat + 1]'(by omega)).toNat ∧ tgt = a)))
      ?_ (fun J hJ => by
        fbl_group
        · simp only [h1_64, Nat.mod_eq_of_lt (by omega : 2 * a.toNat + 1 < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : 2 * b.toNat + 1 < 2 ^ 64)] at hc
          exact hJ _ _ ⟨rfl, Or.inl ⟨hc, rfl⟩⟩
        · simp only [h1_64, Nat.mod_eq_of_lt (by omega : 2 * a.toNat + 1 < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : 2 * b.toNat + 1 < 2 ^ 64)] at hc
          exact hJ _ _ ⟨rfl, Or.inr ⟨by omega, rfl⟩⟩)
    rintro _ ⟨tgt, ⟨⟩⟩ mK ⟨hmK, htgt_spec⟩
    subst hmK
    have hsrc_lt : src.toNat < 2 * s.core.cur_vars := by
      rcases hsrc_spec with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption
    have htgt_lt : tgt.toNat < 2 * s.core.cur_vars := by
      rcases htgt_spec with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption
    have hst_ent : ∀ {F1 : List (List Nat)},
        (cnfOfClauses F1).EntailsClause (cnfClause [src.toNat, tgt.toNat]) →
        (cnfOfClauses F1).EntailsClause (cnfClause [a.toNat, b.toNat]) := by
      intro F1 hent
      rcases hsrc_spec with ⟨hle, rfl⟩ | ⟨hle, rfl⟩ <;>
        rcases htgt_spec with ⟨hle', rfl⟩ | ⟨hle', rfl⟩
      · exact hent
      · omega
      · omega
      · exact fbl_entailsClause_swap2 hent
    have hsrc_off_idx : (src.setWidth 64 <<< (1 : Nat)).toNat = 2 * src.toNat := by
      have : src.toNat < 2 ^ 30 := by omega
      bv_omega
    have hsrc_sz_idx : ((src.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * src.toNat + 1 := by
      have : src.toNat < 2 ^ 30 := by omega
      bv_omega
    have hoff_eq : (s.core.wvec[2 * src.toNat]'(by omega)).toNat =
        fullWatchOffCore s.core src.toNat := by
      unfold fullWatchOffCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hsz_eq : (s.core.wvec[2 * src.toNat + 1]'(by omega)).toNat =
        fullWatchSizeCore s.core src.toNat := by
      unfold fullWatchSizeCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hbd_slice : fullWatchOffCore s.core src.toNat + fullWatchSizeCore s.core src.toNat ≤
        s.core.wlen := hw.watches.bounds src.toNat hsrc_lt
    have hs0 : 2 * src.toNat % 2 ^ 64 = 2 * src.toNat := by omega
    have hs1 : (2 * src.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * src.toNat + 1 := by
      rw [h1_64]; omega
    have bv32_lt64 : ∀ x : BitVec 32, x.toNat < 2 ^ 64 :=
      fun x => Nat.lt_trans (BitVec.isLt x) (by decide)
    have hoff_bv : (BitVec.setWidth 64
        (s.core.wvec[2 * src.toNat % 2 ^ 64]'(by omega))).toNat =
        fullWatchOffCore s.core src.toNat := by
      simp only [hs0, BitVec.toNat_setWidth, hoff_eq]
      omega
    have hs_end_eq : (BitVec.setWidth 64
        (s.core.wvec[2 * src.toNat % 2 ^ 64]'(by omega)) +
        BitVec.setWidth 64 (s.core.wvec[(2 * src.toNat + BitVec.toNat (1 : BitVec 64)) %
          2 ^ 64]'(by omega))).toNat =
        fullWatchOffCore s.core src.toNat + fullWatchSizeCore s.core src.toNat := by
      simp only [hs0, hs1, BitVec.toNat_add, BitVec.toNat_setWidth, hoff_eq, hsz_eq]
      omega
    have hbd_wstk : fullWatchOffCore s.core src.toNat +
        fullWatchSizeCore s.core src.toNat ≤ s.core.wstk.length := by omega
    have hend_le_wstk : (BitVec.setWidth 64
        (s.core.wvec[2 * src.toNat % 2 ^ 64]'(by omega)) +
        BitVec.setWidth 64 (s.core.wvec[(2 * src.toNat + BitVec.toNat (1 : BitVec 64)) %
          2 ^ 64]'(by omega))).toNat ≤ s.core.wstk.length := by omega
    fbl_group
    refine wp_loop_inv
      (fun (p, ()) ml => ml = mK ∧
        fullWatchOffCore s.core src.toNat ≤ p.toNat ∧
        p.toNat ≤ fullWatchOffCore s.core src.toNat + fullWatchSizeCore s.core src.toNat ∧
        ∀ F1, FullWitnessInv c F0 F1 s.core →
          if s.core.dense_mode = 0#64 then
            WatchSliceOk F1 s.core src.toNat p.toNat
              (fullWatchOffCore s.core src.toNat + fullWatchSizeCore s.core src.toNat - p.toNat)
          else
            DenseWatchSliceOk F1 s.core src.toNat p.toNat
              (fullWatchOffCore s.core src.toNat + fullWatchSizeCore s.core src.toNat - p.toNat))
      (fun (p, ()) _ =>
        fullWatchOffCore s.core src.toNat + fullWatchSizeCore s.core src.toNat - p.toNat)
      (fun J hJ => by
        fbl_group
        have hp_eq : (BitVec.setWidth 64
            (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat)).toNat]'(by
              rw [hsrc_off_idx]; omega))).toNat = fullWatchOffCore s.core src.toNat := by
          simpa [hsrc_off_idx, hs0] using hoff_bv
        refine hJ _ _ ⟨rfl, hp_eq ▸ Nat.le_refl _, by rw [hp_eq]; omega, fun F1 hw1 => ?_⟩
        rw [hp_eq]
        have heq_sz : fullWatchOffCore s.core src.toNat +
            fullWatchSizeCore s.core src.toNat - fullWatchOffCore s.core src.toNat =
            fullWatchSizeCore s.core src.toNat := by omega
        rw [heq_sz]
        have hw1m := hw1.watches
        by_cases hdm : s.core.dense_mode = 0#64 <;>
          simp only [ModeWatchesInv, hdm, ↓reduceIte] at hw1m ⊢
        · exact hw1m.slices src.toNat hsrc_lt
        · exact hw1m.slices src.toNat hsrc_lt)
      (fun J (p, ()) ml ⟨rfl, hp_lo, hp_hi, hsl⟩ ih => ?_)
    fbl_group
    · have hp_lt : p.toNat < fullWatchOffCore s.core src.toNat +
          fullWatchSizeCore s.core src.toNat := by c0_bound
      have hrem_pos : 0 < fullWatchOffCore s.core src.toNat +
          fullWatchSizeCore s.core src.toNat - p.toNat := by omega
      have hwp_p : s.core.wstk[p.toNat]? = some (s.core.wstk[p.toNat]'(by omega)) :=
        List.getElem?_eq_getElem (by omega)
      refine wp_join_group
        (fun (p', ()) mJ => mJ = ml ∧
          fullWatchOffCore s.core src.toNat ≤ p'.toNat ∧
          p'.toNat ≤ fullWatchOffCore s.core src.toNat + fullWatchSizeCore s.core src.toNat ∧
          p.toNat < p'.toNat ∧
          ∀ F1, FullWitnessInv c F0 F1 s.core →
            if s.core.dense_mode = 0#64 then
              WatchSliceOk F1 s.core src.toNat p'.toNat
                (fullWatchOffCore s.core src.toNat + fullWatchSizeCore s.core src.toNat - p'.toNat)
            else
              DenseWatchSliceOk F1 s.core src.toNat p'.toNat
                (fullWatchOffCore s.core src.toNat + fullWatchSizeCore s.core src.toNat - p'.toNat))
        (by
          rintro _ ⟨p', ⟨⟩⟩ mJ ⟨rfl, hp'_lo, hp'_hi, hp'_gt, hsl'⟩
          fbl_group
          exact ih (p', ()) mJ (by dsimp only; omega) ⟨rfl, hp'_lo, hp'_hi, hsl'⟩)
        (fun J' hJ' => by
          fbl_group
          · exact hQ true fun _ => ⟨ha_lt, hb_lt, hne_ab, hne_neg, fun F1 hw1 =>
              hst_ent (modeWatchSlice_bin_entails (hsl F1 hw1) hrem_pos hwp_p
                (by assumption) (by assumption))⟩
          · have hp1 : (p + 1).toNat = p.toNat + 1 := by bv_omega
            refine hJ' _ _ ⟨rfl, by bv_omega, by bv_omega, by omega, fun F1 hw1 => ?_⟩
            rw [hp1]
            simpa [show fullWatchOffCore s.core src.toNat + fullWatchSizeCore s.core src.toNat -
                (p.toNat + 1) =
                (fullWatchOffCore s.core src.toNat +
                  fullWatchSizeCore s.core src.toNat - p.toNat) - 1
                by omega] using
              modeWatchSlice_bin_tail (hsl F1 hw1) hrem_pos hwp_p (by assumption)
          · have hp2 : (p + 2).toNat = p.toNat + 2 := by bv_omega
            have h2le : p.toNat + 2 ≤ fullWatchOffCore s.core src.toNat +
                fullWatchSizeCore s.core src.toNat :=
              by have := (modeWatchSlice_large_tail (hsl F_cur hw) hrem_pos hwp_p
                   (by assumption)).1
                 omega
            refine hJ' _ _ ⟨rfl, by bv_omega, by bv_omega, by omega, fun F1 hw1 => ?_⟩
            rw [hp2]
            simpa [show fullWatchOffCore s.core src.toNat + fullWatchSizeCore s.core src.toNat -
                (p.toNat + 2) =
                (fullWatchOffCore s.core src.toNat +
                  fullWatchSizeCore s.core src.toNat - p.toNat) - 2
                by omega] using
              (modeWatchSlice_large_tail (hsl F1 hw1) hrem_pos hwp_p (by assumption)).2)
    · exact hQ false fun hf => by cases hf


end LeanQbe.T.Examples.Kissat.Full
