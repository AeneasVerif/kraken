module

public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.Full1
public import LeanQbe.T.Examples.Kissat.Full2
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0Agrees
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Chronological BCP / Decide Specs & Zero-Callee Proofs (`Stage 4`, Part 1)

Provides:
1. Strictly scoped `FullPropDecTactics` (zero global attributes).
2. Collision-free `FullPropDecSpecs` namespace containing shared Stage-4 invariants
   (`FullLitMarksClear`, `FullArenaVarsNodup`, `FullLastLearnedWf`, `FullExtScratchOk`,
   `FullSparseInv`, `FullConflAt`, `FullTrailExt`) and per-function `Spec` contracts
   (callees + all 9 owned functions, aligned with `#966`/`#968`).
3. Core bitvector, `WatchSliceOk`, and `FullWitnessInv` congruence/helper lemmas.
4. Parametric `(Γ : Env)` `Func.wp` proofs for the 2 zero-callee helpers:
   - `full_find_repl` (`full_find_repl_wp`)
   - `full_assign_level` (`full_assign_level_wp`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
  LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test

/-! ## 1. Scoped tactic helpers (`FullPropDecTactics`) -/

namespace FullPropDecTactics

theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

scoped macro "fp_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)
scoped macro "fp_unmdata" : tactic =>
  `(tactic| first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)
scoped macro "fp_step" : tactic => `(tactic| ((try fp_unmdata); (repeat fp_strip); c0_step))
scoped macro "fp_steps" : tactic =>
  `(tactic| (
      (try fp_unmdata)
      (repeat fp_strip)
      c0_steps
      repeat (any_goals (fp_strip; repeat fp_strip); c0_steps)))

end FullPropDecTactics

open scoped FullArenaTactics FullPropDecTactics

/-! ## 2. Collision-free `FullPropDecSpecs` invariants & per-function `Spec` contracts -/

namespace FullPropDecSpecs

/-- Both variable marks (`mrk`) and literal marks (`lit_mark`) are zero across `c.max_vars`. -/
def FullLitMarksClear (c : FullCfg) (s : FullState) : Prop :=
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
  (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)

/-- Every non-garbage arena clause has pairwise distinct variables (`#968`). -/
def FullArenaVarsNodup (s : FullState) : Prop :=
  ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false →
    ((fullArenaClauseLits s r).map (· / 2)).Nodup

/-- Every `last_learned` slot is either `0xFFFFFFFF` or a valid arena clause reference (`#968`). -/
def FullLastLearnedWf (s : FullState) : Prop :=
  ∀ i < 8, let cr := s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32
    cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ fullArenaClauseRefs s

/-- Auxiliary scratch invariants carried across Stage-4 passes (`#968`). -/
def FullExtScratchOk (c : FullCfg) (s : FullState) : Prop :=
  FullLastLearnedWf s ∧ s.scratch.extend_len ≤ c.extend_cap

/-- Canonical sparse-mode (`dense_mode = 0`) Stage-4 UNSAT-only solver invariant (`#968`). -/
def FullSparseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

/-- Conflict witness on `FullCoreState` for fixed `F_cur`: either a falsified `F_cur`-entailed
binary clause (`confl_type = 1`) or a falsified live large arena clause (`confl_type = 2`). -/
def FullConflAt (F_cur : List (List Nat)) (k : FullCoreState) : Prop :=
  (k.confl_type = 1#64 ∧ k.confl_lit0.toNat < 2 * k.cur_vars ∧
    k.confl_lit1.toNat < 2 * k.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [k.confl_lit0.toNat, k.confl_lit1.toNat]) ∧
    k.vals[k.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
    k.vals[k.confl_lit1.toNat]?.getD 0#8 = 0xFF#8) ∨
  (k.confl_type = 2#64 ∧ k.confl_ref.toNat ∈ fullArenaClauseRefsCore k ∧
    fullArenaClauseGarbCore k k.confl_ref.toNat = false ∧
    ∀ l ∈ fullArenaClauseLitsCore k k.confl_ref.toNat, k.vals[l]?.getD 0#8 = 0xFF#8)

/-- Weak conflict witness matching `FullSpec1.FullConflictOkW` (`confl_type = 2#64` for large). -/
def FullConflOkW (F_cur : List (List Nat)) (k : FullCoreState) : Prop :=
  (k.confl_type = 1#64 ∧ k.confl_lit0.toNat < 2 * k.cur_vars ∧
    k.confl_lit1.toNat < 2 * k.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [k.confl_lit0.toNat, k.confl_lit1.toNat]) ∧
    k.vals[k.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
    k.vals[k.confl_lit1.toNat]?.getD 0#8 = 0xFF#8) ∨
  (k.confl_type = 2#64 ∧ k.confl_ref.toNat ∈ fullArenaClauseRefsCore k ∧
    fullArenaClauseGarbCore k k.confl_ref.toNat = false ∧
    ∀ l ∈ fullArenaClauseLitsCore k k.confl_ref.toNat, k.vals[l]?.getD 0#8 = 0xFF#8)

theorem FullConflAt.toOkW {F_cur : List (List Nat)} {k : FullCoreState}
    (h : FullConflAt F_cur k) : FullConflOkW F_cur k :=
  h

/-- Predicate expressing that candidate literal `k` of `cref` is unusable by `full_find_repl`. -/
def fullFindReplBad (s : FullState) (cref k : Nat) : Prop :=
  let cand := (s.core.arena[cref + 3 + k]?.getD 0#32).toNat
  2 * s.core.cur_vars ≤ cand ∨
    ((s.core.vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = true

/-- Trail-extension relation across chronological propagation. -/
structure FullTrailExt (k1 k2 : FullCoreState) : Prop where
  te_ge : k1.trail_end ≤ k2.trail_end
  trl_pref : ∀ i < k1.trail_end, k2.trl[i]? = k1.trl[i]?
  lvl_pres : ∀ i < k1.trail_end,
    k2.lvl[(k1.trl[i]?.getD 0#32).toNat / 2]? = k1.lvl[(k1.trl[i]?.getD 0#32).toNat / 2]?

theorem FullTrailExt.refl (k : FullCoreState) : FullTrailExt k k :=
  ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl⟩

theorem FullTrailExt.trans {k1 k2 k3 : FullCoreState}
    (h1 : FullTrailExt k1 k2) (h2 : FullTrailExt k2 k3) : FullTrailExt k1 k3 :=
  ⟨Nat.le_trans h1.te_ge h2.te_ge,
   fun i hi => (h2.trl_pref i (by have := h1.te_ge; omega)).trans (h1.trl_pref i hi),
   fun i hi => by
     have h2l := h2.lvl_pres i (by have := h1.te_ge; omega)
     rw [h1.trl_pref i hi] at h2l; exact h2l.trans (h1.lvl_pres i hi)⟩

theorem FullTrailExt.congr {k0 k1 k2 : FullCoreState} (h : FullTrailExt k0 k1)
    (hte : k2.trail_end = k1.trail_end) (htrl : k2.trl = k1.trl) (hlvl : k2.lvl = k1.lvl) :
    FullTrailExt k0 k2 :=
  ⟨hte.symm ▸ h.te_ge, fun i hi => htrl ▸ h.trl_pref i hi, fun i hi => hlvl ▸ h.lvl_pres i hi⟩

/-- Arena clause preservation up to per-clause literal permutation (preserves `FullArenaVarsNodup`
and `FullLastLearnedWf`). -/
def FullArenaPermEq (k1 k2 : FullCoreState) : Prop :=
  fullArenaClauseRefsCore k2 = fullArenaClauseRefsCore k1 ∧
  ∀ r ∈ fullArenaClauseRefsCore k1,
    fullArenaClauseSizeCore k2 r = fullArenaClauseSizeCore k1 r ∧
    fullArenaClauseGarbCore k2 r = fullArenaClauseGarbCore k1 r ∧
    (fullArenaClauseLitsCore k2 r).Perm (fullArenaClauseLitsCore k1 r)

theorem FullArenaPermEq.refl (k : FullCoreState) : FullArenaPermEq k k :=
  ⟨rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩

theorem FullArenaPermEq.trans {k1 k2 k3 : FullCoreState}
    (h1 : FullArenaPermEq k1 k2) (h2 : FullArenaPermEq k2 k3) : FullArenaPermEq k1 k3 :=
  ⟨h2.1.trans h1.1, fun r hr =>
    let ⟨s1, g1, p1⟩ := h1.2 r hr
    let ⟨s2, g2, p2⟩ := h2.2 r (h1.1.symm ▸ hr)
    ⟨s2.trans s1, g2.trans g1, p2.trans p1⟩⟩

theorem FullArenaPermEq.preserves_varsNodup {s1 s2 : FullState}
    (hp : FullArenaPermEq s1.core s2.core) (hnd : FullArenaVarsNodup s1) :
    FullArenaVarsNodup s2 := by
  intro r hr hng
  have hr1 : r ∈ fullArenaClauseRefsCore s1.core := hp.1 ▸ hr
  obtain ⟨_, hgb, hperm⟩ := hp.2 r hr1
  exact (hperm.map (· / 2)).nodup_iff.mpr (hnd r hr1 (hgb.symm.trans hng))

theorem FullArenaPermEq.preserves_lastLearnedWf {s1 s2 : FullState}
    (hp : FullArenaPermEq s1.core s2.core)
    (hll : s2.scratch.last_learned = s1.scratch.last_learned)
    (hwf : FullLastLearnedWf s1) : FullLastLearnedWf s2 := by
  intro i hi; dsimp only [fullArenaClauseRefs]; rw [hll, hp.1]; exact hwf i hi

/-! ### Callee specifications -/

def fullWatchPushSpec : Spec [i64, i32, i32, i32, i32] [.bool] :=
  fun (h, lit, w0, w1, cnt, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧
      (cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32) ∧
      (cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) wvec' wstk' wlen' wusable' wsort' m',
        let s' : FullState :=
          { core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
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
          lit.toNat < 2 * s.core.cur_vars →
          fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat ∧
          ∀ k < fullWatchSize s lit.toNat,
            s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
              s.core.wstk[fullWatchOff s lit.toNat + k]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullAssignLvlSpec : Spec [i64, i32, i32, i32] [] :=
  fun (h, lit, rsn, alvl, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      if s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
         s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8 then
        Q () m
      else
        let v := lit.toNat / 2
        let rsn' := if alvl = 0#32 then 0xFFFFFFFF#32 else rsn
        ∀ (flags' : List (BitVec 32)) (unassigned' unflushed' : BitVec 64)
          (phases' : List (BitVec 8)) (m' : Mem 64),
          flags'.length = c.max_vars → phases'.length = c.max_vars →
          let s' : FullState :=
            { core :=
                { s.core with
                  vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                  flags := flags'
                  lvl := s.core.lvl.set v alvl
                  rsns := s.core.rsns.set v rsn'
                  trl := s.core.trl.set s.core.trail_end lit
                  trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
                  trail_end := s.core.trail_end + 1
                  unassigned := unassigned'
                  unflushed := unflushed' }
              scratch := { s.scratch with phases := phases' } }
          (FullMem c s' ⋆ R) m' → Q () m'

def fullAssignSpec : Spec [i64, i32, i32] [] :=
  fun (h, lit, rsn, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level < 2 ^ 32 ∧ (FullMem c s ⋆ R) m ∧
      if s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
         s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8 then
        Q () m
      else
        let v := lit.toNat / 2
        let rsn' := if s.core.cur_level = 0 then 0xFFFFFFFF#32 else rsn
        ∀ (flags' : List (BitVec 32)) (unassigned' unflushed' : BitVec 64)
          (phases' : List (BitVec 8)) (m' : Mem 64),
          flags'.length = c.max_vars → phases'.length = c.max_vars →
          let s' : FullState :=
            { core :=
                { s.core with
                  vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                  flags := flags'
                  lvl := s.core.lvl.set v (BitVec.ofNat 32 s.core.cur_level)
                  rsns := s.core.rsns.set v rsn'
                  trl := s.core.trl.set s.core.trail_end lit
                  trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
                  trail_end := s.core.trail_end + 1
                  unassigned := unassigned'
                  unflushed := unflushed' }
              scratch := { s.scratch with phases := phases' } }
          (FullMem c s' ⋆ R) m' → Q () m'

def fullBacktrackSpec : Spec [i64, i64] [] :=
  fun (h, target_lvl, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
      ∀ (vals' : List (BitVec 8)) (lvl' rsns' trl' tp' : List (BitVec 32))
        (te' prop' : Nat) (unassigned' : BitVec 64) (scratch' : FullScratch) (m' : Mem 64),
        let s' : FullState :=
          { core :=
              { s.core with
                vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
                trail_end := te', propagated := prop',
                cur_level := min s.core.cur_level target_lvl.toNat,
                unassigned := unassigned' }
            scratch := scratch' }
        FullCoreInv c F0 s' →
        scratch'.last_learned = s.scratch.last_learned →
        scratch'.extend_len = s.scratch.extend_len →
        (FullMem c s' ⋆ R) m' → Q () m'

def fullNextDecVarSpec : Spec [i64] [i64] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) (scratch' : FullScratch) (m' : Mem 64),
        scratch'.LengthsOk c →
        scratch'.last_learned = s.scratch.last_learned →
        scratch'.extend_len = s.scratch.extend_len →
        (r = 0xFFFFFFFFFFFFFFFF#64 ∨
          (r.toNat < s.core.cur_vars ∧ s.core.vals[2 * r.toNat]?.getD 0#8 = 0#8)) →
        (FullMem c { s with scratch := scratch' } ⋆ R) m' → Q (r, ()) m'

def fullWalkSpec : Spec [i64] [] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
      ∀ (fuel' : BitVec 64) (scratch' : FullScratch) (m' : Mem 64),
        scratch'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat →
        scratch'.last_learned = s.scratch.last_learned →
        scratch'.extend_len = s.scratch.extend_len →
        (FullMem c { core := { s.core with fuel := fuel' }, scratch := scratch' } ⋆ R) m' →
        Q () m'

def fullIlog10Spec : Spec [i64] [i64] :=
  fun (_x, ()) m Q _ => ∀ r : BitVec 64, 1 ≤ r.toNat → r.toNat ≤ 19 → Q (r, ()) m

/-! ### Exported specifications for the 9 owned functions -/

def fullFindReplSpec : Spec [i64, i64] [i64] :=
  fun (h, cref, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ cref.toNat + 3 ≤ s.core.arena_len ∧
      3 ≤ fullArenaClauseSize s cref.toNat ∧
      cref.toNat + 3 + fullArenaClauseSize s cref.toNat ≤ s.core.arena_len ∧
      (FullMem c s ⋆ R) m ∧
      ((∀ k, 2 ≤ k → k < fullArenaClauseSize s cref.toNat →
          fullFindReplBad s cref.toNat k) →
        Q (0xFFFFFFFF#64, ()) m) ∧
      (∀ (r : Nat) (m' : Mem 64),
        2 ≤ r → r < fullArenaClauseSize s cref.toNat →
        (let cand := (s.core.arena[cref.toNat + 3 + r]?.getD 0#32).toNat
         cand < 2 * s.core.cur_vars ∧
         ((s.core.vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = false) →
        (FullMem c { s with core := { s.core with
          arena := s.core.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r) } } ⋆ R) m' →
        Q (BitVec.ofNat 64 r, ()) m')

def fullAssignLevelSpec : Spec [i64, i32, i32] [i32] :=
  fun (h, cref, forced_lit, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧
      cref.toNat + 3 ≤ s.core.arena_len ∧
      cref.toNat + 3 + fullArenaClauseSize s cref.toNat ≤ s.core.arena_len ∧
      (∀ l ∈ fullArenaClauseLits s cref.toNat, l ≠ forced_lit.toNat → l / 2 < c.max_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ res : BitVec 32,
        (∀ l ∈ fullArenaClauseLits s cref.toNat, l ≠ forced_lit.toNat →
          (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ res.toNat) →
        (res = 0#32 ∨ ∃ l ∈ fullArenaClauseLits s cref.toNat,
          l ≠ forced_lit.toNat ∧ res = s.core.lvl[l / 2]?.getD 0#32) →
        Q (res, ()) m

def fullPropLitSpec : Spec [i64, i32, i64] [.bool] :=
  fun (h, _lit, ignore_ref, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      s.core.dense_mode = 0#64 ∧ s.core.oom = 0#64 ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) vals' flags' lvl' rsns' trl' tp' te' unas' unfl'
        wvec' arena' wstk' wlen' wu' ctype' cref' c0' c1' oom'
        ticks' wsort' phases' m',
        let s' : FullState :=
          { core :=
              { s.core with
                vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                trail_pos := tp', trail_end := te', unassigned := unas', unflushed := unfl',
                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                confl_type := ctype', confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                oom := oom' }
            scratch := { s.scratch with
              search_ticks := ticks', wsort := wsort', phases := phases' } }
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
        (ok = true → oom' = 0#64 ∧ ctype' = s.core.confl_type) →
        (ok = false → oom' ≠ 0#64 ∨
          (FullConflOkW F_cur s'.core ∧ (ctype' = 2#64 → cref' ≠ ignore_ref))) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullPropagateIgnoreSpec : Spec [i64, i64] [i64] :=
  fun (h, ignore_ref, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl'
        wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom'
        ticks' wsort' phases' m',
        let s' : FullState :=
          { core :=
              { s.core with
                vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                trail_pos := tp', trail_end := te', propagated := prop', unassigned := unas',
                unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
                confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
            scratch := { s.scratch with
              search_ticks := ticks', wsort := wsort', phases := phases' } }
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
        fuel'.toNat ≤ s.core.fuel.toNat →
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
        (r = 0#64 → prop' = te' ∧ ctype' = s.core.confl_type ∧
          (s.core.oom = 0#64 → oom' = 0#64) ∧
          (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
        (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧
          FullConflOkW F_cur s'.core ∧ (ctype' = 2#64 → cref' ≠ ignore_ref) ∧
          (s'.core.cur_level = 0 → F0.Unsat)) →
        (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
        (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullPropagateSpec : Spec [i64] [i64] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl'
        wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom'
        ticks' wsort' phases' m',
        let s' : FullState :=
          { core :=
              { s.core with
                vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                trail_pos := tp', trail_end := te', propagated := prop', unassigned := unas',
                unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
                confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
            scratch := { s.scratch with
              search_ticks := ticks', wsort := wsort', phases := phases' } }
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
        (FullArenaVarsNodup s → FullArenaVarsNodup s') →
        fuel'.toNat ≤ s.core.fuel.toNat →
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
        (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
          (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
        (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧
          FullConflOkW F_cur s'.core ∧ (s'.core.cur_level = 0 → F0.Unsat)) →
        (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
        (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullDecideSpec : Spec [i64] [i64] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) vals' flags' lvl' rsns' trl' tp' ftrl' fdec'
        te' cl' unas' unfl' scratch' m',
        let s' : FullState :=
          { core :=
              { s.core with
                vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                trail_pos := tp', frame_trail := ftrl', frame_dec := fdec',
                trail_end := te', cur_level := cl', unassigned := unas', unflushed := unfl' }
            scratch := scratch' }
        FullCoreInv c F0 s' →
        scratch'.last_learned = s.scratch.last_learned →
        scratch'.extend_len = s.scratch.extend_len →
        (r = 0#64 ∨ r = 1#64) →
        (r = 0#64 → cl' = s.core.cur_level ∧ te' = s.core.trail_end) →
        (r = 1#64 → cl' = s.core.cur_level + 1 ∧ te' = s.core.trail_end + 1) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullWarmupSpec : Spec [i64] [] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullCoreInv c F0 s ∧ s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
      ∀ vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' prob' unas' unfl'
        wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' scratch' m',
        let s' : FullState :=
          { core :=
              { s.core with
                vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                trail_pos := tp', frame_trail := ftrl', frame_dec := fdec',
                trail_end := te', propagated := prop', probing := prob', unassigned := unas',
                unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
                confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
            scratch := scratch' }
        FullCoreInv c F0 s' → FullArenaPermEq s.core s'.core →
        fuel'.toNat ≤ s.core.fuel.toNat →
        scratch'.last_learned = s.scratch.last_learned →
        scratch'.extend_len = s.scratch.extend_len →
        (s.core.probing = 0#64 → prob' = 0#64) →
        (FullMem c s' ⋆ R) m' → Q () m'

def fullRephaseSpec : Spec [i64] [] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
      ∀ vals' lvl' rsns' trl' tp' te' prop' unas' fuel' scratch' m',
        let s' : FullState :=
          { core :=
              { s.core with
                vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
                trail_end := te', propagated := prop', cur_level := 0,
                unassigned := unas', fuel := fuel' }
            scratch := scratch' }
        FullCoreInv c F0 s' → fuel'.toNat ≤ s.core.fuel.toNat →
        scratch'.last_learned = s.scratch.last_learned →
        scratch'.extend_len = s.scratch.extend_len →
        (FullMem c s' ⋆ R) m' → Q () m'

def fullRestartSpec : Spec [i64] [] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
      ∀ vals' lvl' rsns' trl' tp' te' prop' cl' unas' scratch' m',
        let s' : FullState :=
          { core :=
              { s.core with
                vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
                trail_end := te', propagated := prop', cur_level := cl', unassigned := unas' }
            scratch := scratch' }
        FullCoreInv c F0 s' → cl' ≤ s.core.cur_level →
        scratch'.last_learned = s.scratch.last_learned →
        scratch'.extend_len = s.scratch.extend_len →
        (FullMem c s' ⋆ R) m' → Q () m'

end FullPropDecSpecs

open FullPropDecSpecs

/-! ## 3. Arithmetic, `WatchSliceOk`, and `FullWitnessInv` helpers -/

theorem bv32_sle0_eq_not_slt0 (x : BitVec 32) : (0#32).sle x = !(x.slt 0#32) := by
  simp only [BitVec.sle, BitVec.slt]; change decide (0 ≤ x.toInt) = !decide (x.toInt < 0)
  by_cases h : x.toInt < 0 <;> simp [h, show (0 ≤ x.toInt) ↔ ¬(x.toInt < 0) by omega]

theorem bv64_sub1_toNat {f : BitVec 64} (hf : f ≠ 0#64) : (f - 1#64).toNat = f.toNat - 1 := by
  have hpos : 0 < f.toNat := Nat.pos_of_ne_zero fun h0 =>
    hf (BitVec.eq_of_toNat_eq (by simpa using h0))
  bv_omega

theorem bv64_add_toNat {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by simp [BitVec.toNat_add, Nat.mod_eq_of_lt h]
theorem bv64_add1_toNat {a : BitVec 64} (h : a.toNat + 1 < 2 ^ 64) :
    (a + (1 : BitVec 64)).toNat = a.toNat + 1 := bv64_add_toNat h
theorem bv64_add2_toNat {a : BitVec 64} (h : a.toNat + 2 < 2 ^ 64) :
    (a + (2 : BitVec 64)).toNat = a.toNat + 2 := bv64_add_toNat h
theorem bv64_add3_toNat {a : BitVec 64} (h : a.toNat + 3 < 2 ^ 64) :
    (a + (3 : BitVec 64)).toNat = a.toNat + 3 := bv64_add_toNat h
theorem bv64_add4_toNat {a : BitVec 64} (h : a.toNat + 4 < 2 ^ 64) :
    (a + (4 : BitVec 64)).toNat = a.toNat + 4 := bv64_add_toNat h
theorem bv64_sub_toNat {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)]
theorem bv64_shl1_u32 (x : BitVec 32) : (x.setWidth 64 <<< 1#64).toNat = 2 * x.toNat := by
  have hx := x.isLt
  have h1 : (x.setWidth 64 <<< 1#64).toNat = ((x.setWidth 64).toNat * 2) % 2 ^ 64 := by
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [h1, bv_c0_zext32_64, Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]

theorem bv32_mask7f_flag0 (x : BitVec 32) : ((x &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_zero]
  have h : (0x7FFFFFFF#32)[i] = false ∨ (0x80000000#32)[i] = false := by revert i hi; decide
  rcases h with h | h <;> simp [h]

theorem bv32_bin_rsn_props {x : BitVec 32} (hx : x.toNat < 2 ^ 31 - 1) :
    let r := (x &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    r ≠ 0xFFFFFFFF#32 ∧ (r &&& 0x80000000#32) ≠ 0#32 ∧ (r &&& 0x7FFFFFFF#32).toNat = x.toNat := by
  intro r
  have hmask : x &&& 0x7FFFFFFF#32 = x := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_and]
    have h7f : (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 := by decide
    rw [h7f, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hr_and_hi : r &&& 0x80000000#32 = 0x80000000#32 := by
    ext i hi; simp only [r, BitVec.getElem_or, BitVec.getElem_and]
    by_cases h : (0x80000000#32)[i] <;> simp [h]
  have hr_and_lo : r &&& 0x7FFFFFFF#32 = x := by
    rw [← hmask]; ext i hi; simp only [r, BitVec.getElem_or, BitVec.getElem_and]
    have h : (0x7FFFFFFF#32)[i] = false ∨ (0x80000000#32)[i] = false := by revert i hi; decide
    rcases h with h | h <;> simp [h]
  refine ⟨fun hff => ?_, by rw [hr_and_hi]; decide, by rw [hr_and_lo]⟩
  have hlo : (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 := by decide
  have hx' : x.toNat = (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat := by rw [← hr_and_lo, hff]
  omega

theorem full_i8_vals_slt0 {v : BitVec 8} (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) :
    (v.signExtend 32).slt 0#32 = true ↔ v = 0xFF#8 := by
  rcases hdom with rfl | rfl | rfl <;> decide

theorem i8_vals_eq0_of_not_pos_neg {v : BitVec 8} (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (hnp : (0#32).slt (v.signExtend 32) = false) (hnn : (v.signExtend 32).slt 0#32 = false) :
    v = 0#8 := by
  rcases hdom with rfl | rfl | rfl
  · rfl
  · exact absurd hnp (by decide)
  · exact absurd hnn (by decide)

theorem i8_vals_ne_of_slt_false {v1 v2 : BitVec 8}
    (h1 : v1 = 0xFF#8) (h2 : (v2.signExtend 32).slt 0#32 = false) : v1 ≠ v2 := by
  intro heq; rw [← heq, h1] at h2; exact absurd h2 (by decide)

theorem cnfClause_swap2 {F0 : CNF Nat} {a b : Nat}
    (h : F0.EntailsClause (cnfClause [a, b])) : F0.EntailsClause (cnfClause [b, a]) :=
  entails_of_mem_or_false h fun l hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
    rcases hl with rfl | rfl <;> simp

theorem WatchSliceOk.relocate {F F' : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat}
    (hF : (cnfOfClauses F').Entails (cnfOfClauses F)) (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F k lit p rem) : WatchSliceOk F' k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    refine .bin ?_ hflag hne (by omega) (CNF.entails_clause_trans hF hent)
      (ih (p' := p' + 1) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm 1 idx] using hwstk (idx + 1) (by omega))
    simpa [Nat.add_zero] using (hwstk 0 (by omega)).trans hp
  | @large p rem w0 cref hp hp1 hflag hlt href _ ih =>
    refine .large ?_ ?_ hflag hlt (hsub _ href)
      (ih (p' := p' + 2) fun idx hi => by
        have h1 : p' + 2 + idx = p' + (idx + 2) := by omega
        have h2 : p + 2 + idx = p + (idx + 2) := by omega
        rw [h1, h2]; exact hwstk (idx + 2) (by omega))
    · simpa [Nat.add_zero] using (hwstk 0 (by omega)).trans hp
    · exact (hwstk 1 (by omega)).trans hp1

theorem watchSlice_append {F_cur : List (List Nat)} {k : FullCoreState} {lit p len1 len2 : Nat}
    (h1 : WatchSliceOk F_cur k lit p len1)
    (h2 : WatchSliceOk F_cur k lit (p + len1) len2) :
    WatchSliceOk F_cur k lit p (len1 + len2) := by
  induction h1 with
  | @empty p => simpa using h2
  | @bin p rem w h0 hf hne hl he _ ih =>
    rw [show p + (rem + 1) = (p + 1) + rem by omega] at h2
    rw [show rem + 1 + len2 = (rem + len2) + 1 by omega]
    exact .bin h0 hf hne hl he (ih h2)
  | @large p rem w cr h0 h1 hf hl hr _ ih =>
    rw [show p + (rem + 2) = (p + 2) + rem by omega] at h2
    rw [show rem + 2 + len2 = (rem + len2) + 2 by omega]
    exact .large h0 h1 hf hl hr (ih h2)

theorem WatchSliceOk.append_bin {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hpre : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F_cur k lit p rem)
    (hat : k'.wstk[p' + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    WatchSliceOk F_cur k' lit p' (rem + 1) :=
  watchSlice_append
    (h.relocate (by rw [CNF.entails_def]; exact fun _ p => p) hvars hsub hpre)
    (.bin hat hflag hne hlt hent .empty)

theorem WatchSliceOk.append_large {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 cref : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hpre : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F_cur k lit p rem)
    (hat0 : k'.wstk[p' + rem]? = some w0) (hat1 : k'.wstk[p' + rem + 1]? = some cref)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hlt : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ fullArenaClauseRefsCore k') :
    WatchSliceOk F_cur k' lit p' (rem + 2) :=
  watchSlice_append
    (h.relocate (by rw [CNF.entails_def]; exact fun _ p => p) hvars hsub hpre)
    (.large hat0 hat1 hflag hlt href .empty)

theorem watchSlice_inv_bin {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p len : Nat} {w0 : BitVec 32}
    (h : WatchSliceOk F_cur k lit p len) (hlen : 0 < len)
    (hget : k.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) :
    (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
    WatchSliceOk F_cur k lit (p + 1) (len - 1) := by
  cases h with
  | empty => omega
  | bin h0 _ _ hlt hent hrest =>
    have hw := Option.some.inj (h0.symm.trans hget); subst hw
    exact ⟨hlt, hent, by simpa using hrest⟩
  | large h0 _ hf _ _ _ =>
    have hw := Option.some.inj (h0.symm.trans hget); subst hw; exact absurd hf hflag

theorem watchSlice_inv_large {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p len : Nat} {w0 : BitVec 32}
    (h : WatchSliceOk F_cur k lit p len) (hlen : 0 < len)
    (hget : k.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) = 0#32) :
    2 ≤ len ∧
    ∃ cref : BitVec 32, k.wstk[p + 1]? = some cref ∧
      cref.toNat < 0x80000000 ∧ cref.toNat ∈ fullArenaClauseRefsCore k ∧
      WatchSliceOk F_cur k lit (p + 2) (len - 2) := by
  cases h with
  | empty => omega
  | bin h0 hf _ _ _ _ =>
    have hw := Option.some.inj (h0.symm.trans hget); subst hw; exact absurd hflag hf
  | large h0 h1 _ hlt href hrest =>
    exact ⟨by omega, _, h1, hlt, href, by simpa using hrest⟩

/-- Clear watches on `FullCoreState` while preserving all non-watch invariants mid-compaction. -/
abbrev withEmptyWatchesCore (c : FullCfg) (k : FullCoreState) : FullCoreState :=
  { k with wvec := List.replicate (4 * c.max_vars) 0#32, wlen := 0, dense_mode := 0#64 }

theorem fullWatchesInv_empty (c : FullCfg) (F_cur : List (List Nat)) (k : FullCoreState)
    (hcv : k.cur_vars ≤ c.max_vars) :
    ModeWatchesInv F_cur (withEmptyWatchesCore c k) := by
  have hw0 : ∀ l < 2 * k.cur_vars,
      fullWatchOffCore (withEmptyWatchesCore c k) l = 0 ∧
      fullWatchSizeCore (withEmptyWatchesCore c k) l = 0 := fun l hl => by
    unfold fullWatchOffCore fullWatchSizeCore withEmptyWatchesCore
    simp [show 2 * l < 4 * c.max_vars by omega, show 2 * l + 1 < 4 * c.max_vars by omega]
  simp only [ModeWatchesInv, withEmptyWatchesCore, ↓reduceIte]
  refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
    (fun l1 _ h1 _ _ hp1 _ => ?_) (fun l hl => ?_)
  · dsimp only at hl ⊢; obtain ⟨ho, hs⟩ := hw0 l hl
    change fullWatchOffCore (withEmptyWatchesCore c k) l +
      fullWatchSizeCore (withEmptyWatchesCore c k) l ≤ 0; omega
  · dsimp only at hl; obtain ⟨_, hs⟩ := hw0 l hl
    change 0 < fullWatchSizeCore (withEmptyWatchesCore c k) l at hp; omega
  · dsimp only at h1; obtain ⟨_, hs⟩ := hw0 l1 h1
    change 0 < fullWatchSizeCore (withEmptyWatchesCore c k) l1 at hp1; omega
  · dsimp only at hl; obtain ⟨ho, hs⟩ := hw0 l hl
    change WatchSliceOk F_cur (withEmptyWatchesCore c k) l
      (fullWatchOffCore (withEmptyWatchesCore c k) l)
      (fullWatchSizeCore (withEmptyWatchesCore c k) l)
    rw [ho, hs]; exact .empty

theorem fullWitnessInv_to_nw {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hcv : k.cur_vars ≤ c.max_vars) (hw : FullWitnessInv c F0 F_cur k) :
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k) :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := fullWatchesInv_empty c F_cur k hcv }

theorem fullWitnessInv_of_nw {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    (hdm : k.dense_mode = 0#64) (hwat : WatchesInv F_cur k) :
    FullWitnessInv c F0 F_cur k :=
  { hnw with
    arena := { hnw.arena with len_ok := hnw.arena.len_ok }
    watches := by simp only [ModeWatchesInv, hdm, ↓reduceIte]; exact hwat }

theorem fullWitnessInv_nw_congr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k k' : FullCoreState} (hcv' : k'.cur_vars ≤ c.max_vars)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    (hcv : k'.cur_vars = k.cur_vars) (hinc : k'.inconsistent = k.inconsistent)
    (hal : k'.arena_len = k.arena_len) (har : k'.arena = k.arena)
    (hte : k'.trail_end = k.trail_end) (hcl : k'.cur_level = k.cur_level)
    (hv : k'.vals = k.vals) (hl : k'.lvl = k.lvl) (hr : k'.rsns = k.rsns)
    (ht : k'.trl = k.trl) (htp : k'.trail_pos = k.trail_pos)
    (hft : k'.frame_trail = k.frame_trail) (hfd : k'.frame_dec = k.frame_dec) :
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') := by
  have href : fullArenaClauseRefsCore (withEmptyWatchesCore c k') =
      fullArenaClauseRefsCore (withEmptyWatchesCore c k) := by
    unfold fullArenaClauseRefsCore withEmptyWatchesCore; rw [hal, har]
  have hsz : ∀ r, fullArenaClauseSizeCore (withEmptyWatchesCore c k') r =
      fullArenaClauseSizeCore (withEmptyWatchesCore c k) r := fun r => by
    unfold fullArenaClauseSizeCore withEmptyWatchesCore; rw [har]
  have hgb : ∀ r, fullArenaClauseGarbCore (withEmptyWatchesCore c k') r =
      fullArenaClauseGarbCore (withEmptyWatchesCore c k) r := fun r => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore withEmptyWatchesCore; rw [har]
  have hlt : ∀ r, fullArenaClauseLitsCore (withEmptyWatchesCore c k') r =
      fullArenaClauseLitsCore (withEmptyWatchesCore c k) r := fun r => by
    unfold fullArenaClauseLitsCore withEmptyWatchesCore; rw [har]
    simp only [fullArenaClauseSizeCore]
  refine
    { ext_sound := hcv.symm ▸ hnw.ext_sound
      inconsistent_sound := fun h => hnw.inconsistent_sound (hinc ▸ h)
      arena :=
        { len_ok := hal.symm ▸ hnw.arena.len_ok
          refs_wf := fun r hmem => by
            have := hnw.arena.refs_wf r (href ▸ hmem)
            rw [hsz r]; simpa only [withEmptyWatchesCore, hal, har] using this
          shrk_term := fun r hmem hsh => by
            have hsh0 :
                (fullArenaHdrCore (withEmptyWatchesCore c k) r &&& 0x00800000#32) ≠ 0#32 := by
              simpa only [fullArenaHdrCore, withEmptyWatchesCore, har] using hsh
            obtain ⟨t, ht1, ht2, hs⟩ := hnw.arena.shrk_term r (href ▸ hmem) hsh0
            exact ⟨t, by rw [hsz r]; exact ht1, hal.symm ▸ ht2,
              by simpa only [withEmptyWatchesCore, har] using hs⟩
          lits_lt := fun r hmem hng l hlm => hcv.symm ▸
            hnw.arena.lits_lt r (href ▸ hmem) (hgb r ▸ hng) l (hlt r ▸ hlm)
          entails := fun r hmem hng => by
            rw [hlt r]; exact hnw.arena.entails r (href ▸ hmem) (hgb r ▸ hng) }
      watches := fullWatchesInv_empty c F_cur k' hcv'
      cur_level_le := by change k'.cur_level ≤ k'.trail_end; rw [hcl, hte]; exact hnw.cur_level_le
      trail_lits_lt := fun i hi => by
        change (k'.trl[i]?.getD 0#32).toNat < 2 * k'.cur_vars; rw [ht, hcv]
        exact hnw.trail_lits_lt i (hte ▸ hi)
      trail_vars_nodup := fun i j hi hj heq =>
        hnw.trail_vars_nodup i j (hte ▸ hi) (hte ▸ hj)
          (by simpa only [withEmptyWatchesCore, ht] using heq)
      vals_domain := fun l hl' => by
        simpa only [withEmptyWatchesCore, hv] using hnw.vals_domain l (hcv ▸ hl')
      vals_true_iff := fun l hl' => by
        simpa only [withEmptyWatchesCore, hv, hte, ht] using hnw.vals_true_iff l (hcv ▸ hl')
      vals_false_iff := fun l hl' => by
        simpa only [withEmptyWatchesCore, hv, hte, ht] using hnw.vals_false_iff l (hcv ▸ hl')
      lvl_le := fun i hi => by
        simpa only [withEmptyWatchesCore, hl, ht, hcl] using hnw.lvl_le i (hte ▸ hi)
      dec_earliest := fun i j hi hj hleq hdec =>
        hnw.dec_earliest i j (hte ▸ hi) (hte ▸ hj)
          (by simpa only [withEmptyWatchesCore, hl, ht] using hleq)
          (by simpa only [withEmptyWatchesCore, hl, ht, hr] using hdec)
      levels_inhabited := fun L hL1 hLle => by
        simpa only [withEmptyWatchesCore, hte, hl, ht] using hnw.levels_inhabited L hL1 (hcl ▸ hLle)
      level0_sound := fun i hi hl0 => by
        simpa only [withEmptyWatchesCore, ht] using
          hnw.level0_sound i (hte ▸ hi) (by simpa only [withEmptyWatchesCore, hl, ht] using hl0)
      trail_pos_inv := fun i hi => by
        simpa only [withEmptyWatchesCore, ht, htp] using hnw.trail_pos_inv i (hte ▸ hi)
      level0_rsn_none := fun idx hidx hl0 => by
        simpa only [withEmptyWatchesCore, ht, hr] using
          hnw.level0_rsn_none idx (hte ▸ hidx)
            (by simpa only [withEmptyWatchesCore, hl, ht] using hl0)
      frame_trail_lt := fun L hL => by
        simpa only [withEmptyWatchesCore, hft, hte] using hnw.frame_trail_lt L (hcl ▸ hL)
      frame_trail_mono := fun L1 L2 h1 h2 => by
        simpa only [withEmptyWatchesCore, hft] using hnw.frame_trail_mono L1 L2 h1 (hcl ▸ h2)
      frame_trail_before_lt := fun L hL1 hLle i hi => by
        simpa only [withEmptyWatchesCore, hl, ht] using
          hnw.frame_trail_before_lt L hL1 (hcl ▸ hLle) i
            (by simpa only [withEmptyWatchesCore, hft] using hi)
      frame_dec_lt := fun L hL1 hLle => by
        simpa only [withEmptyWatchesCore, hfd, hcv] using hnw.frame_dec_lt L hL1 (hcl ▸ hLle)
      reason_inv := fun idx hidx hne => by
        have hri := hnw.reason_inv idx (hte ▸ hidx)
          (by simpa only [withEmptyWatchesCore, ht, hr] using hne)
        dsimp only at hri ⊢
        rw [href]; simp only [hgb, hlt]
        simp only [withEmptyWatchesCore] at hri ⊢
        rw [ht, hr, hcv, hl]; exact hri
      reason_lit_mem := fun idx hidx hne hlg => by
        have hrm := hnw.reason_lit_mem idx (hte ▸ hidx)
          (by simpa only [withEmptyWatchesCore, ht, hr] using hne)
          (by simpa only [withEmptyWatchesCore, ht, hr] using hlg)
        dsimp only at hrm ⊢
        rw [hlt]; simpa only [withEmptyWatchesCore, ht, hr] using hrm }

theorem FullWitnessInv.vals_zero_xor1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {v : Nat} (hv : v < k.cur_vars)
    (hz : k.vals[2 * v]?.getD 0#8 = 0#8) : k.vals[2 * v + 1]?.getD 0#8 = 0#8 := by
  have h1 := (hw.vals_zero_iff (by omega : 2 * v < 2 * k.cur_vars)).mp hz
  exact (hw.vals_zero_iff (by omega : 2 * v + 1 < 2 * k.cur_vars)).mpr fun i hi => by
    have := h1 i hi; omega

theorem FullWitnessInv.level0_unsat_of_conflOkW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (hl0 : k.cur_level = 0) (hc : FullConflOkW F_cur k) : F0.Unsat := by
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

theorem FullWitnessInv.level0_unsat_of_conflAt {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (hl0 : k.cur_level = 0) (hc : FullConflAt F_cur k) : F0.Unsat :=
  hw.level0_unsat_of_conflOkW hl0 hc.toOkW

theorem FullWitnessInv.with_fuel_prop {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (fuel' : BitVec 64) (prop' : Nat) :
    FullWitnessInv c F0 F_cur { k with fuel := fuel', propagated := prop' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem FullCoreInv.with_fuel_scratch {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullCoreInv c F0 s) {fuel' : BitVec 64} {scratch' : FullScratch}
    (hsok : scratch'.LengthsOk c) :
    FullCoreInv c F0 { core := { s.core with fuel := fuel' }, scratch := scratch' } := by
  obtain ⟨F_cur, hw⟩ := h.witness
  exact ⟨⟨{ h.lengths.core_ok with vals_len := h.lengths.core_ok.vals_len }, hsok⟩, F_cur,
    hw.with_fuel_prop fuel' s.core.propagated⟩

theorem FullCoreInv.with_probing {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullCoreInv c F0 s) (prob' : BitVec 64) :
    FullCoreInv c F0 { s with core := { s.core with probing := prob' } } := by
  obtain ⟨F_cur, hw⟩ := h.witness
  exact ⟨⟨{ h.lengths.core_ok with vals_len := h.lengths.core_ok.vals_len }, h.lengths.scratch_ok⟩,
    F_cur, { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
                     watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }⟩

/-! ## 4. Zero-callee `Func.wp` proofs: `full_find_repl` & `full_assign_level` -/

private theorem full_find_repl_ok {s : FullState} {cref r idx : Nat}
    {hi_lt : idx < s.core.arena.length}
    {hj_lt : (s.core.arena[idx]'hi_lt).toNat < s.core.vals.length}
    (hidx : idx = cref + 3 + r) (hcv : (s.core.arena[idx]'hi_lt).toNat < 2 * s.core.cur_vars)
    (hsle :
      (0#32).sle ((s.core.vals[(s.core.arena[idx]'hi_lt).toNat]'hj_lt).signExtend 32) = true) :
    let cand := (s.core.arena[cref + 3 + r]?.getD 0#32).toNat
    cand < 2 * s.core.cur_vars ∧
    ((s.core.vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = false := by
  subst hidx; dsimp only
  rw [List.getElem?_eq_getElem hi_lt, Option.getD_some,
    List.getElem?_eq_getElem hj_lt, Option.getD_some]
  refine ⟨hcv, ?_⟩; rw [bv32_sle0_eq_not_slt0, Bool.not_eq_true'] at hsle; exact hsle

private theorem full_find_repl_bad_slt {s : FullState} {cref r idx : Nat}
    {hi_lt : idx < s.core.arena.length}
    {hj_lt : (s.core.arena[idx]'hi_lt).toNat < s.core.vals.length} (hidx : idx = cref + 3 + r)
    (h : (0#32).sle ((s.core.vals[(s.core.arena[idx]'hi_lt).toNat]'hj_lt).signExtend 32) = false) :
    fullFindReplBad s cref r := by
  subst hidx; unfold fullFindReplBad; refine Or.inr ?_
  rw [List.getElem?_eq_getElem hi_lt, Option.getD_some,
    List.getElem?_eq_getElem hj_lt, Option.getD_some]
  rw [bv32_sle0_eq_not_slt0, Bool.not_eq_false'] at h; exact h

private theorem full_find_repl_bad_oob {s : FullState} {cref r idx nlits : Nat}
    {hi_lt : idx < s.core.arena.length} (hidx : idx = cref + 3 + r)
    (hnl : nlits = 2 * s.core.cur_vars) (h : ¬ (s.core.arena[idx]'hi_lt).toNat < nlits) :
    fullFindReplBad s cref r := by
  subst hidx; unfold fullFindReplBad; refine Or.inl ?_
  rw [List.getElem?_eq_getElem hi_lt, Option.getD_some]; omega

theorem full_find_repl_wp (Γ : Env) :
    ∀ args m Q X, fullFindReplSpec args m Q X →
      Func.wp Γ full_find_repl_body args m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hc3, hsz3, hfit, hm, hNone, hSome⟩
  have hmaxv := c.hmaxv; have har := c.harena; unfold dimacsBound at hmaxv har
  have hcl := hlen.core_ok
  have hcv_le := hcl.cur_vars_le; have hal := hcl.arena_len_arr
  have hale := hcl.arena_len_le; have hvl := hcl.vals_len
  have hc1 : (cref + 1).toNat = cref.toNat + 1 := by bv_omega
  have hc2 : (cref + 2).toNat = cref.toNat + 2 := by bv_omega
  have hc2_lt : (cref + 2).toNat < s.core.arena.length := by omega
  have hc1_lt : (cref + 1).toNat < s.core.arena.length := by omega
  have hsz_eq : (s.core.arena[(cref + 2).toNat]'hc2_lt).toNat =
      fullArenaClauseSize s cref.toNat := by
    unfold fullArenaClauseSize fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (show cref.toNat + 2 < s.core.arena.length by omega),
      Option.getD_some]
    exact congrArg BitVec.toNat (by congr 1)
  fp_step; fp_step; fp_step; fp_step; fp_step; fp_step
  generalize hsz_v : s.core.arena[(cref + 2).toNat]'hc2_lt = sz
  generalize hsr0_v : s.core.arena[(cref + 1).toNat]'hc1_lt = sr0
  have hsz_nat : sz.toNat = fullArenaClauseSize s cref.toNat := by rw [← hsz_v]; exact hsz_eq
  refine wp_join_group
    (fun (srch, ()) mj => 2 ≤ srch.toNat ∧ srch.toNat < sz.toNat ∧ mj = m) ?_ ?_
  · rintro _ ⟨srch, ⟨⟩⟩ mj ⟨hsrch2, hsrch_lt, rfl⟩
    fp_steps
    refine wp_loop_inv
      (fun (r, ()) ml => srch.toNat ≤ r.toNat ∧ r.toNat ≤ sz.toNat ∧ ml = mj ∧
        ∀ k, srch.toNat ≤ k → k < r.toNat → fullFindReplBad s cref.toNat k)
      (fun (r, ()) _ => sz.toNat - r.toNat)
      (fun J hJ => by
        fp_steps; exact hJ _ _ ⟨Nat.le_refl _, by omega, rfl, fun _ _ _ => by omega⟩)
      (fun J (r, ()) ml ⟨hr_ge, hr_le, rfl, hseen1⟩ ih => ?_)
    fp_steps
    · have hok := full_find_repl_ok (cref := cref.toNat) (r := r.toNat)
        (by c0_bound) (by c0_bound) hc
      have hset : { s with core := { s.core with
            arena := s.core.arena.set (cref + 1).toNat r } } =
          { s with core := { s.core with
            arena := s.core.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r.toNat) } } := by
        rw [hc1, bv_ofNat_toNat_eq]
      rw [hset] at hm; rw [bv32_zext64_eq]
      exact hSome r.toNat _ (by omega) (by omega) hok hm
    · refine ih _ _ (by c0_bound) ⟨by c0_bound, by c0_bound, rfl, fun k hk1 hk2 =>
        if hkr : k = r.toNat then
          hkr ▸ full_find_repl_bad_slt (cref := cref.toNat) (r := r.toNat) (by c0_bound) hc
        else hseen1 k hk1 (by c0_bound)⟩
    · refine ih _ _ (by c0_bound) ⟨by c0_bound, by c0_bound, rfl, fun k hk1 hk2 =>
        if hkr : k = r.toNat then
          hkr ▸ full_find_repl_bad_oob (cref := cref.toNat) (r := r.toNat)
            (by c0_bound) (by c0_bound) hc
        else hseen1 k hk1 (by c0_bound)⟩
    · refine wp_loop_inv
        (fun (r2, ()) ml2 => 2 ≤ r2.toNat ∧ r2.toNat ≤ srch.toNat ∧ ml2 = ml ∧
          ∀ k, 2 ≤ k → k < r2.toNat → fullFindReplBad s cref.toNat k)
        (fun (r2, ()) _ => srch.toNat - r2.toNat)
        (fun J2 hJ2 => by
          fp_steps; exact hJ2 _ _ ⟨by decide, by c0_bound, rfl, fun _ _ _ => by c0_bound⟩)
        (fun J2 (r2, ()) ml2 ⟨hr2_ge, hr2_le, rfl, hseen2⟩ ih2 => ?_)
      fp_steps
      · have hok := full_find_repl_ok (cref := cref.toNat) (r := r2.toNat)
          (by c0_bound) (by c0_bound) hc
        have hset : { s with core := { s.core with
              arena := s.core.arena.set (cref + 1).toNat r2 } } =
            { s with core := { s.core with
              arena := s.core.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r2.toNat) } } := by
          rw [hc1, bv_ofNat_toNat_eq]
        rw [hset] at hm; rw [bv32_zext64_eq]
        exact hSome r2.toNat _ hr2_ge (by omega) hok hm
      · refine ih2 _ _ (by c0_bound) ⟨by c0_bound, by c0_bound, rfl, fun k hk1 hk2 =>
          if hkr : k = r2.toNat then
            hkr ▸ full_find_repl_bad_slt (cref := cref.toNat) (r := r2.toNat) (by c0_bound) hc
          else hseen2 k hk1 (by c0_bound)⟩
      · refine ih2 _ _ (by c0_bound) ⟨by c0_bound, by c0_bound, rfl, fun k hk1 hk2 =>
          if hkr : k = r2.toNat then
            hkr ▸ full_find_repl_bad_oob (cref := cref.toNat) (r := r2.toNat)
              (by c0_bound) (by c0_bound) hc
          else hseen2 k hk1 (by c0_bound)⟩
      · refine hNone fun k hk2 hksz =>
          if hks : k < srch.toNat then hseen2 k hk2 (by omega) else hseen1 k (by omega) (by omega)
  · intro J hJ; fp_steps
    · exact hJ (2#32, ()) m ⟨by decide, by c0_bound, rfl⟩
    · exact hJ (2#32, ()) m ⟨by decide, by c0_bound, rfl⟩
    · exact hJ (sr0, ()) m ⟨by c0_bound, by c0_bound, rfl⟩

theorem full_assign_level_wp (Γ : Env) :
    ∀ args m Q X, fullAssignLevelSpec args m Q X →
      Func.wp Γ full_assign_level_body args m Q X := by
  rintro ⟨h, cref, forced_lit, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hc3, hfit, hlits_v, hm, hQ⟩
  have hmaxv := c.hmaxv; have har := c.harena; unfold dimacsBound at hmaxv har
  have hcl := hlen.core_ok
  have hal := hcl.arena_len_arr; have hale := hcl.arena_len_le; have hll := hcl.lvl_len
  have hcr64 : (cref.setWidth 64).toNat = cref.toNat := bv_c0_zext32_64 cref
  have hc2 : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by
    have := bv64_add2_toNat (a := cref.setWidth 64) (by rw [hcr64]; omega)
    simpa [hcr64] using this
  have hc2_lt : (cref.setWidth 64 + 2#64).toNat < s.core.arena.length := by omega
  have hsz_eq : (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hc2_lt).toNat =
      fullArenaClauseSize s cref.toNat := by
    unfold fullArenaClauseSize fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (show cref.toNat + 2 < s.core.arena.length by omega),
      Option.getD_some]
    exact congrArg BitVec.toNat (by congr 1)
  have hbd : cref.toNat + 3 + fullArenaClauseSize s cref.toNat ≤ s.core.arena.length := by omega
  have hl_var : ∀ k (hk : k < fullArenaClauseSize s cref.toNat),
      s.core.arena[cref.toNat + 3 + k]'(by omega) ≠ forced_lit →
      (s.core.arena[cref.toNat + 3 + k]'(by omega)).toNat / 2 < c.max_vars := fun k hk hne =>
    hlits_v _ ((mem_fullArenaClauseLitsCore_iff hbd).mpr ⟨k, hk, rfl⟩)
      (fun heq => hne (BitVec.eq_of_toNat_eq heq))
  fp_step; fp_step; fp_step; fp_step
  generalize hsz_v : s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hc2_lt = sz
  have hsz_nat : sz.toNat = fullArenaClauseSize s cref.toNat := by rw [← hsz_v]; exact hsz_eq
  refine wp_loop_inv
    (fun (res, i, ()) ml => i.toNat ≤ sz.toNat ∧ ml = m ∧
      (∀ k < i.toNat,
        let l := (s.core.arena[cref.toNat + 3 + k]?.getD 0#32).toNat
        l ≠ forced_lit.toNat → (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ res.toNat) ∧
      (res = 0#32 ∨ ∃ k < i.toNat,
        let l := (s.core.arena[cref.toNat + 3 + k]?.getD 0#32).toNat
        l ≠ forced_lit.toNat ∧ res = s.core.lvl[l / 2]?.getD 0#32))
    (fun (_, i, ()) _ => sz.toNat - i.toNat)
    (fun J hJ => by
      fp_steps
      exact hJ _ _ ⟨Nat.zero_le _, rfl, fun _ hk => by simp at hk, Or.inl rfl⟩)
    (fun J (res, i, ()) ml ⟨hi_le, rfl, hge, hatt⟩ ih => ?_)
  have hih_step : ∀ (hi_lt : i.toNat < sz.toNat) (res' : BitVec 32),
      (∀ k < i.toNat + 1,
        let l := (s.core.arena[cref.toNat + 3 + k]?.getD 0#32).toNat
        l ≠ forced_lit.toNat → (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ res'.toNat) →
      (res' = 0#32 ∨ ∃ k < i.toNat + 1,
        let l := (s.core.arena[cref.toNat + 3 + k]?.getD 0#32).toNat
        l ≠ forced_lit.toNat ∧ res' = s.core.lvl[l / 2]?.getD 0#32) →
      J (res', i + (1 : BitVec 32), ()) ml := fun hi_lt res' hge' hatt' => by
    have hi1 : (i + (1 : BitVec 32)).toNat = i.toNat + 1 := by bv_omega
    exact ih _ ml (by dsimp only; omega)
      ⟨by omega, rfl, by rw [hi1]; exact hge', by rw [hi1]; exact hatt'⟩
  have h3_nat : (3 : BitVec 64).toNat = 3 := rfl
  fp_steps
  · have hi_lt : i.toNat < sz.toNat := by assumption
    have hi_idx : (cref.setWidth 64 + (3 : BitVec 64) + i.setWidth 64).toNat =
        cref.toNat + 3 + i.toNat := by bv_omega
    have hi_idx' : (cref.toNat + (3 : BitVec 64).toNat + i.toNat) % 2 ^ 64 =
        cref.toNat + 3 + i.toNat := by omega
    have hli_lt : (cref.setWidth 64 + (3 : BitVec 64) + i.setWidth 64).toNat <
        s.core.arena.length := by omega
    let l := s.core.arena[(cref.setWidth 64 + (3 : BitVec 64) + i.setWidth 64).toNat]'hli_lt
    have hl_eq : l = s.core.arena[cref.toNat + 3 + i.toNat]'(by omega) := by
      dsimp only [l]; congr 1
    have hl_get : (s.core.arena[cref.toNat + 3 + i.toNat]?.getD 0#32).toNat = l.toNat := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hl_eq]
    have hne_l : l ≠ forced_lit := by
      intro heq; apply hc
      have h1 : s.core.arena[(cref.toNat + (3 : BitVec 64).toNat + i.toNat) % 2 ^ 64]'(
          by omega) = l := by dsimp only [l]; congr 1; omega
      rw [h1]; exact heq
    have hlv_nat : l.toNat / 2 < s.core.lvl.length := by
      rw [hll, hl_eq]; exact hl_var i.toNat (by omega) (hl_eq ▸ hne_l)
    have hlv_lt : (BitVec.setWidth 64 (l >>> (1 : Nat))).toNat < s.core.lvl.length := by
      rw [bv_c0_zext32_64, bv32_lshr_1]; exact hlv_nat
    have hlv_eq : s.core.lvl[(BitVec.setWidth 64 (l >>> (1 : Nat))).toNat]'hlv_lt =
        s.core.lvl[l.toNat / 2]?.getD 0#32 := by
      rw [List.getElem?_eq_getElem hlv_nat, Option.getD_some]
      have hidx : (BitVec.setWidth 64 (l >>> (1 : Nat))).toNat = l.toNat / 2 := by
        rw [bv_c0_zext32_64, bv32_lshr_1]
      congr 1
    have hl_eq2 : s.core.arena[(cref.toNat + (3 : BitVec 64).toNat + i.toNat) % 2 ^ 64]'(
        by omega) = l := by dsimp only [l]; congr 1; omega
    have hlv_eq2 : s.core.lvl[(s.core.arena[(cref.toNat + (3 : BitVec 64).toNat + i.toNat) %
        2 ^ 64]'(by omega)).toNat / 2]'(by rw [hl_eq2]; exact hlv_nat) =
        s.core.lvl[l.toNat / 2]?.getD 0#32 := by
      rw [List.getElem?_eq_getElem hlv_nat, Option.getD_some]
      have hidx : (s.core.arena[(cref.toNat + (3 : BitVec 64).toNat + i.toNat) %
          2 ^ 64]'(by omega)).toNat / 2 = l.toNat / 2 := by rw [hl_eq2]
      congr 1
    fp_steps
    · have hgt : res.toNat < (s.core.lvl[l.toNat / 2]?.getD 0#32).toNat := by
        rw [← hlv_eq2]; exact hc
      refine hih_step hi_lt (s.core.lvl[(BitVec.setWidth 64 (l >>> (1 : Nat))).toNat]'hlv_lt)
        (fun k hk hkne => ?_) (Or.inr ⟨i.toNat, by omega,
          by rw [hl_get]; exact fun heq => hne_l (BitVec.eq_of_toNat_eq heq),
          by rw [hl_get, hlv_eq]⟩)
      by_cases hki : k = i.toNat
      · subst hki; rw [hl_get, hlv_eq]; exact Nat.le_refl _
      · exact Nat.le_trans (hge k (by omega) hkne) (by rw [hlv_eq]; omega)
    · have hle : (s.core.lvl[l.toNat / 2]?.getD 0#32).toNat ≤ res.toNat := by
        rw [← hlv_eq2]; omega
      refine hih_step hi_lt res (fun k hk hkne => ?_)
        (hatt.elim Or.inl fun ⟨k, hk, h⟩ => Or.inr ⟨k, by omega, h⟩)
      by_cases hki : k = i.toNat
      · subst hki; rw [hl_get]; exact hle
      · exact hge k (by omega) hkne
  · have hi_lt : i.toNat < sz.toNat := by assumption
    have hi_idx' : (cref.toNat + (3 : BitVec 64).toNat + i.toNat) % 2 ^ 64 =
        cref.toNat + 3 + i.toNat := by omega
    have hl_get : (s.core.arena[cref.toNat + 3 + i.toNat]?.getD 0#32).toNat =
        forced_lit.toNat := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have h1 : s.core.arena[cref.toNat + 3 + i.toNat]'(by omega) =
          s.core.arena[(cref.toNat + (3 : BitVec 64).toNat + i.toNat) % 2 ^ 64]'(by omega) := by
        congr 1; exact hi_idx'.symm
      rw [h1, hc]
    refine hih_step hi_lt res (fun k hk hkne => ?_)
      (hatt.elim Or.inl fun ⟨k, hk, h⟩ => Or.inr ⟨k, by omega, h⟩)
    by_cases hki : k = i.toNat
    · subst hki; rw [hl_get] at hkne; exact absurd rfl hkne
    · exact hge k (by omega) hkne
  · have hi_eq : i.toNat = fullArenaClauseSizeCore s.core cref.toNat := by
      have : fullArenaClauseSize s cref.toNat = fullArenaClauseSizeCore s.core cref.toNat := rfl
      omega
    have hbd' : cref.toNat + 3 + fullArenaClauseSizeCore s.core cref.toNat ≤
        s.core.arena.length := hbd
    refine hQ res (fun l hl hne => ?_) ?_
    · obtain ⟨k, hk, hget⟩ := (mem_fullArenaClauseLitsCore_iff hbd').mp hl
      have hk' := hge k (by omega)
      rw [List.getElem?_eq_getElem (show cref.toNat + 3 + k < s.core.arena.length by omega),
        Option.getD_some, hget] at hk'
      exact hk' hne
    · refine hatt.elim Or.inl fun ⟨k, hk, hne, hres⟩ => ?_
      rw [List.getElem?_eq_getElem (show cref.toNat + 3 + k < s.core.arena.length by omega),
        Option.getD_some] at hne hres
      exact Or.inr ⟨(s.core.arena[cref.toNat + 3 + k]'(by omega)).toNat,
        (mem_fullArenaClauseLitsCore_iff hbd').mpr ⟨k, by omega, rfl⟩, hne, hres⟩

end LeanQbe.T.Examples.Kissat.Full
