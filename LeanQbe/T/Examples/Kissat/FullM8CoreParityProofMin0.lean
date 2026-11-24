/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8CoreParity
import LeanQbe.T.Examples.Kissat.FullMinLemmas3
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M8 Rank #5 Minimization DFS & Shrink-Lower Proofs (`FullM8CoreParityProofMin0`)

UNSAT-only `Func.wp` proofs (`public section`, `0` `@[expose]`, `0` `@[local]`, `XPost := False`)
for Rank #5 helper functions in `FullM8CoreParity.lean`:
1. `full_min_lit_dfs_m8` (`m8MinLitDfsSpec`: DFS stack in `wsort` (`2 * max_vars`),
   depth charged only across `!is_bin` edges, `search_ticks` incremented on `!is_bin` visit).
2. `full_shrink_lower_m8` (`m8ShrinkLowerSpec`).
Also declares `m8ShrinkBlkBoolSpec` and `m8MinShrinkSpec` for `FullM8CoreParityProofMin`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8CoreParity

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full hiding
  FullMinMarkInv fullMinMarkCore fullMinMarkState fullMinMarkSpec
  fullMinLitSpec fullShrinkLowerSpec fullShrinkBlkSpec fullMinShrinkSpec
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Full.FullMinSpecs
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullMinTactics
open Kraken.Bedrock2.Test

/-! ## 1. Rank #5 State Builder & Public Specifications -/

abbrev m8MinLitDfsState (s : FullState) (mrk : List (BitVec 8)) (wsort mclr : List (BitVec 32))
    (mcl : Nat) (mcf ticks : BitVec 64) : FullState :=
  { core := { s.core with
      mrk := mrk, min_clr := mclr, min_clr_len := mcl, min_clr_full := mcf },
    scratch := { s.scratch with wsort := wsort, search_ticks := ticks } }

abbrev m8ShrinkBlkBoolState (s : FullState) (tmp : List (BitVec 32)) (mrk : List (BitVec 8))
    (mclr sstk wsort : List (BitVec 32)) (mcl : Nat) (mcf ticks : BitVec 64) : FullState :=
  { core := { s.core with
      tmp := tmp, mrk := mrk, min_clr := mclr, min_clr_len := mcl, min_clr_full := mcf },
    scratch := { s.scratch with shrink_stk := sstk, wsort := wsort, search_ticks := ticks } }

abbrev m8MinShrinkState (s : FullState) (tmp : List (BitVec 32)) (tl : Nat)
    (mrk : List (BitVec 8)) (mclr sstk wsort : List (BitVec 32)) (mcl : Nat)
    (mcf conf llits mrem ticks : BitVec 64) : FullState :=
  { core := { s.core with
      tmp := tmp, tmp_len := tl, mrk := mrk, min_clr := mclr,
      min_clr_len := mcl, min_clr_full := mcf },
    scratch := { s.scratch with
      conflicts := conf, learned_lits := llits, min_removed := mrem,
      shrink_stk := sstk, wsort := wsort, search_ticks := ticks } }

/-- Rank #5 `full_min_lit_dfs_m8` contract: DFS stack lives in `wsort` and `!is_bin` clause
visits increment `search_ticks`, preserving `min_stk`. -/
def m8MinLitDfsSpec : Spec [i64, i32, .bool, .bool] [.bool] :=
  fun (h, root_lit, _minimizing, _check_used, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (keepSet : List Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullOtfsCoreInv c F0 s ∧ Full.FullMinMarkInv s.core keepSet ∧
      root_lit.toNat < 2 * s.core.cur_vars ∧
      s.core.vals[root_lit.toNat]?.getD 0#8 = 0xFF#8 ∧
      (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat < s.core.cur_level ∧
      (∀ v < s.core.cur_vars,
        (s.core.lvl[v]?.getD 0#32).toNat ≤
          (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat →
        (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) mrk' wsort' mclr' mcl' mcf' ticks' m',
        let s' := m8MinLitDfsState s mrk' wsort' mclr' mcl' mcf' ticks'
        s'.LengthsOk c → (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
        (∀ v < s.core.cur_vars,
          (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
        (∀ v < s.core.cur_vars,
          (mrk'[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)) →
        Full.FullMinMarkInv s'.core keepSet →
        (ok = true →
          (∀ keep', (∀ l ∈ keepSet, l = root_lit.toNat ∨ l ∈ keep') →
            Full.FullMinMarkInv s'.core keep') ∧
          Full.FullMinMarkInv (Full.fullMinMarkCore s'.core (root_lit.toNat / 2) 2#8) keepSet) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem m8MinLitDfsSpec_monoX {xs : Tup Val [i64, i32, .bool, .bool]} {m : Mem 64}
    {Q : Post [.bool]} {X X' : XPost}
    (h : m8MinLitDfsSpec xs m Q X) : m8MinLitDfsSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, ⟨⟩⟩; exact h

theorem m8MinLitDfsSpec_of {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keepSet : List Nat} {root_lit : BitVec 32} {minimizing check_used : Bool}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hcore : FullOtfsCoreInv c F0 s) (hmin : Full.FullMinMarkInv s.core keepSet)
    (hroot : root_lit.toNat < 2 * s.core.cur_vars)
    (hval : s.core.vals[root_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hlvl : (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat < s.core.cur_level)
    (hno8 : ∀ v < s.core.cur_vars,
      (s.core.lvl[v]?.getD 0#32).toNat ≤
        (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat →
      (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) mrk' wsort' mclr' mcl' mcf' ticks' m',
      let s' := m8MinLitDfsState s mrk' wsort' mclr' mcl' mcf' ticks'
      s'.LengthsOk c → (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
      (∀ v < s.core.cur_vars,
        (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (∀ v < s.core.cur_vars,
        (mrk'[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)) →
      Full.FullMinMarkInv s'.core keepSet →
      (ok = true →
        (∀ keep', (∀ l ∈ keepSet, l = root_lit.toNat ∨ l ∈ keep') →
          Full.FullMinMarkInv s'.core keep') ∧
        Full.FullMinMarkInv (Full.fullMinMarkCore s'.core (root_lit.toNat / 2) 2#8) keepSet) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    m8MinLitDfsSpec (c.hdr, root_lit, minimizing, check_used, ()) m Q X :=
  ⟨c, F0, s, keepSet, R, rfl, hcore, hmin, hroot, hval, hlvl, hno8, hm, hQ⟩

theorem m8MinLitDfsSpec_elim {h root_lit minimizing check_used m Q X}
    (hs : m8MinLitDfsSpec (h, root_lit, minimizing, check_used, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (keepSet : List Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullOtfsCoreInv c F0 s ∧ Full.FullMinMarkInv s.core keepSet ∧
      root_lit.toNat < 2 * s.core.cur_vars ∧
      s.core.vals[root_lit.toNat]?.getD 0#8 = 0xFF#8 ∧
      (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat < s.core.cur_level ∧
      (∀ v < s.core.cur_vars,
        (s.core.lvl[v]?.getD 0#32).toNat ≤
          (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat →
        (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) mrk' wsort' mclr' mcl' mcf' ticks' m',
        let s' := m8MinLitDfsState s mrk' wsort' mclr' mcl' mcf' ticks'
        s'.LengthsOk c → (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
        (∀ v < s.core.cur_vars,
          (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
        (∀ v < s.core.cur_vars,
          (mrk'[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)) →
        Full.FullMinMarkInv s'.core keepSet →
        (ok = true →
          (∀ keep', (∀ l ∈ keepSet, l = root_lit.toNat ∨ l ∈ keep') →
            Full.FullMinMarkInv s'.core keep') ∧
          Full.FullMinMarkInv (Full.fullMinMarkCore s'.core (root_lit.toNat / 2) 2#8) keepSet) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := hs

/-- Rank #5 `full_shrink_lower_m8` contract (extends `Full.fullShrinkLowerSpec` with `wsort'` and
`search_ticks'` writes). -/
def m8ShrinkLowerSpec : Spec [i64, i32, i32] [.bool] := fun (h, ot, ov, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (keepSet : List Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullOtfsCoreInv c F0 s ∧ Full.FullMinMarkInv s.core keepSet ∧
    ov.toNat = ot.toNat / 2 ∧ ot.toNat < 2 * s.core.cur_vars ∧
    s.core.vals[ot.toNat]?.getD 0#8 = 0xFF#8 ∧
    (s.core.lvl[ov.toNat]?.getD 0#32).toNat < s.core.cur_level ∧
    (∀ v < s.core.cur_vars,
      (s.core.lvl[v]?.getD 0#32).toNat ≤ (s.core.lvl[ov.toNat]?.getD 0#32).toNat →
      (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' wsort' mclr' mcl' mcf' ticks' m',
      let s' := m8MinLitDfsState s mrk' wsort' mclr' mcl' mcf' ticks'
      s'.LengthsOk c → (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
      (∀ v < s.core.cur_vars,
        (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (∀ v < s.core.cur_vars, (mrk'[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)) →
      Full.FullMinMarkInv s'.core keepSet →
      (ok = true → (mrk'[ov.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem m8ShrinkLowerSpec_monoX {xs : Tup Val [i64, i32, i32]} {m : Mem 64}
    {Q : Post [.bool]} {X X' : XPost}
    (h : m8ShrinkLowerSpec xs m Q X) : m8ShrinkLowerSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

theorem m8ShrinkLowerSpec_of {c : FullCfg} {F0 : CNF Nat} {s : FullState} {keepSet : List Nat}
    {ot ov : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hcore : FullOtfsCoreInv c F0 s) (hmin : Full.FullMinMarkInv s.core keepSet)
    (hov : ov.toNat = ot.toNat / 2) (hot : ot.toNat < 2 * s.core.cur_vars)
    (hval : s.core.vals[ot.toNat]?.getD 0#8 = 0xFF#8)
    (hlvl : (s.core.lvl[ov.toNat]?.getD 0#32).toNat < s.core.cur_level)
    (hno8 : ∀ v < s.core.cur_vars,
      (s.core.lvl[v]?.getD 0#32).toNat ≤ (s.core.lvl[ov.toNat]?.getD 0#32).toNat →
      (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) mrk' wsort' mclr' mcl' mcf' ticks' m',
      let s' := m8MinLitDfsState s mrk' wsort' mclr' mcl' mcf' ticks'
      s'.LengthsOk c → (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
      (∀ v < s.core.cur_vars,
        (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (∀ v < s.core.cur_vars, (mrk'[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)) →
      Full.FullMinMarkInv s'.core keepSet →
      (ok = true → (mrk'[ov.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    m8ShrinkLowerSpec (c.hdr, ot, ov, ()) m Q X :=
  ⟨c, F0, s, keepSet, R, rfl, hcore, hmin, hov, hot, hval, hlvl, hno8, hm, hQ⟩

theorem m8ShrinkLowerSpec_elim {h ot ov m Q X} (hs : m8ShrinkLowerSpec (h, ot, ov, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (keepSet : List Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullOtfsCoreInv c F0 s ∧ Full.FullMinMarkInv s.core keepSet ∧
      ov.toNat = ot.toNat / 2 ∧ ot.toNat < 2 * s.core.cur_vars ∧
      s.core.vals[ot.toNat]?.getD 0#8 = 0xFF#8 ∧
      (s.core.lvl[ov.toNat]?.getD 0#32).toNat < s.core.cur_level ∧
      (∀ v < s.core.cur_vars,
        (s.core.lvl[v]?.getD 0#32).toNat ≤ (s.core.lvl[ov.toNat]?.getD 0#32).toNat →
        (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) mrk' wsort' mclr' mcl' mcf' ticks' m',
        let s' := m8MinLitDfsState s mrk' wsort' mclr' mcl' mcf' ticks'
        s'.LengthsOk c → (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
        (∀ v < s.core.cur_vars,
          (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
        (∀ v < s.core.cur_vars,
          (mrk'[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)) →
        Full.FullMinMarkInv s'.core keepSet →
        (ok = true → (mrk'[ov.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := hs

/-- Rank #5 `full_shrink_blk_bool_m8` contract (extends `m6ShrinkBlkBoolSpec` with `wsort'` and
`search_ticks'` writes). -/
def m8ShrinkBlkBoolSpec : Spec [i64, i64, i64, i32, i64] [.bool] :=
  fun (h, beg, end_b, blvl, max_tr, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (keepLen : Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullOtfsCoreInv c F0 s ∧
      Full.FullMinMarkInv s.core
        (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) ∧
      (∀ v < s.core.cur_vars, (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
      1 ≤ beg.toNat ∧ beg.toNat < end_b.toNat ∧ end_b.toNat ≤ keepLen ∧
      keepLen ≤ s.core.cur_vars ∧ 0 < blvl.toNat ∧ blvl.toNat < s.core.cur_level ∧
      (∀ k, beg.toNat ≤ k → k < end_b.toNat →
        let l := (s.core.tmp[k]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat = blvl.toNat ∧
        (s.core.trail_pos[l / 2]?.getD 0#32).toNat ≤ max_tr.toNat) ∧
      (∀ k < keepLen, s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        let l := (s.core.tmp[k]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        (s.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) tmp' mrk' mclr' sstk' wsort' mcl' mcf' ticks' m',
        let s' := m8ShrinkBlkBoolState s tmp' mrk' mclr' sstk' wsort' mcl' mcf' ticks'
        FullOtfsCoreInv c F0 s' →
        Full.FullMinMarkInv s'.core
          (((tmp'.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) →
        (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
        (∀ v < s.core.cur_vars, (mrk'[v]?.getD 0#8 &&& 8#8) = 0#8) →
        (∀ v < s.core.cur_vars,
          (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
        (ok = false → tmp' = s.core.tmp) →
        (∀ k < keepLen, (k < beg.toNat ∨ end_b.toNat ≤ k) → tmp'[k]? = s.core.tmp[k]?) →
        (∀ k, beg.toNat ≤ k → k < end_b.toNat → tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
          (s.core.lvl[(tmp'[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat) →
        ((((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map
            fun x => x.toNat / 2).Nodup →
          (∀ k < keepLen, (k < beg.toNat ∨ end_b.toNat ≤ k) →
            s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
            (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠ blvl.toNat) →
          (((tmp'.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map
            fun x => x.toNat / 2).Nodup) →
        (∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
          (cnfOfClauses F_cur).EntailsClause (cnfClause
            (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) →
          FullOtfsWitnessInv c F0 F_cur s'.core ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause
            (((tmp'.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))) →
        (∀ k < keepLen, tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
          let l := (tmp'[k]?.getD 0#32).toNat
          l < 2 * s.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
          (mrk'[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem m8ShrinkBlkBoolSpec_elim {h beg end_b blvl max_tr m Q X}
    (hs : m8ShrinkBlkBoolSpec (h, beg, end_b, blvl, max_tr, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (keepLen : Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullOtfsCoreInv c F0 s ∧
      Full.FullMinMarkInv s.core
        (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) ∧
      (∀ v < s.core.cur_vars, (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
      1 ≤ beg.toNat ∧ beg.toNat < end_b.toNat ∧ end_b.toNat ≤ keepLen ∧
      keepLen ≤ s.core.cur_vars ∧ 0 < blvl.toNat ∧ blvl.toNat < s.core.cur_level ∧
      (∀ k, beg.toNat ≤ k → k < end_b.toNat →
        let l := (s.core.tmp[k]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat = blvl.toNat ∧
        (s.core.trail_pos[l / 2]?.getD 0#32).toNat ≤ max_tr.toNat) ∧
      (∀ k < keepLen, s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        let l := (s.core.tmp[k]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        (s.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) tmp' mrk' mclr' sstk' wsort' mcl' mcf' ticks' m',
        let s' := m8ShrinkBlkBoolState s tmp' mrk' mclr' sstk' wsort' mcl' mcf' ticks'
        FullOtfsCoreInv c F0 s' →
        Full.FullMinMarkInv s'.core
          (((tmp'.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) →
        (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
        (∀ v < s.core.cur_vars, (mrk'[v]?.getD 0#8 &&& 8#8) = 0#8) →
        (∀ v < s.core.cur_vars,
          (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
        (ok = false → tmp' = s.core.tmp) →
        (∀ k < keepLen, (k < beg.toNat ∨ end_b.toNat ≤ k) → tmp'[k]? = s.core.tmp[k]?) →
        (∀ k, beg.toNat ≤ k → k < end_b.toNat → tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
          (s.core.lvl[(tmp'[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat) →
        ((((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map
            fun x => x.toNat / 2).Nodup →
          (∀ k < keepLen, (k < beg.toNat ∨ end_b.toNat ≤ k) →
            s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
            (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠ blvl.toNat) →
          (((tmp'.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map
            fun x => x.toNat / 2).Nodup) →
        (∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
          (cnfOfClauses F_cur).EntailsClause (cnfClause
            (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) →
          FullOtfsWitnessInv c F0 F_cur s'.core ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause
            (((tmp'.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))) →
        (∀ k < keepLen, tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
          let l := (tmp'[k]?.getD 0#32).toNat
          l < 2 * s.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
          (mrk'[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := hs

theorem m8ShrinkBlkBoolSpec_monoX {xs : Tup Val [i64, i64, i64, i32, i64]} {m : Mem 64}
    {Q : Post [.bool]} {X X' : XPost}
    (h : m8ShrinkBlkBoolSpec xs m Q X) : m8ShrinkBlkBoolSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, _, ⟨⟩⟩; exact h

theorem m8ShrinkBlkBoolSpec_of {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {beg end_b max_tr : BitVec 64} {blvl : BitVec 32} {keepLen : Nat} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hcore : FullOtfsCoreInv c F0 s)
    (hmin : Full.FullMinMarkInv s.core
      (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hno8 : ∀ v < s.core.cur_vars, (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    (hbeg1 : 1 ≤ beg.toNat) (hbeg_end : beg.toNat < end_b.toNat) (hend_kl : end_b.toNat ≤ keepLen)
    (hkl_cv : keepLen ≤ s.core.cur_vars) (hblvl_pos : 0 < blvl.toNat)
    (hblvl_lt : blvl.toNat < s.core.cur_level)
    (hblk : ∀ k, beg.toNat ≤ k → k < end_b.toNat →
      let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (s.core.lvl[l / 2]?.getD 0#32).toNat = blvl.toNat ∧
      (s.core.trail_pos[l / 2]?.getD 0#32).toNat ≤ max_tr.toNat)
    (hkeep : ∀ k < keepLen, s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (s.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) tmp' mrk' mclr' sstk' wsort' mcl' mcf' ticks' m',
      FullOtfsCoreInv c F0 (m8ShrinkBlkBoolState s tmp' mrk' mclr' sstk' wsort' mcl' mcf' ticks') →
      Full.FullMinMarkInv
        (m8ShrinkBlkBoolState s tmp' mrk' mclr' sstk' wsort' mcl' mcf' ticks').core
        (((tmp'.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) →
      (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
      (∀ v < s.core.cur_vars, (mrk'[v]?.getD 0#8 &&& 8#8) = 0#8) →
      (∀ v < s.core.cur_vars,
        (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (ok = false → tmp' = s.core.tmp) →
      (∀ k < keepLen, (k < beg.toNat ∨ end_b.toNat ≤ k) → tmp'[k]? = s.core.tmp[k]?) →
      (∀ k, beg.toNat ≤ k → k < end_b.toNat → tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        (s.core.lvl[(tmp'[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat) →
      ((((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map
          fun x => x.toNat / 2).Nodup →
        (∀ k < keepLen, (k < beg.toNat ∨ end_b.toNat ≤ k) →
          s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
          (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠ blvl.toNat) →
        (((tmp'.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map
          fun x => x.toNat / 2).Nodup) →
      (∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
        (cnfOfClauses F_cur).EntailsClause (cnfClause
          (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) →
        FullOtfsWitnessInv c F0 F_cur
          (m8ShrinkBlkBoolState s tmp' mrk' mclr' sstk' wsort' mcl' mcf' ticks').core ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause
          (((tmp'.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))) →
      (∀ k < keepLen, tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        let l := (tmp'[k]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧
        (m8ShrinkBlkBoolState s tmp' mrk' mclr' sstk' wsort' mcl' mcf' ticks').core.vals[l]?.getD
          0#8 = 0xFF#8 ∧
        (mrk'[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (FullMem c (m8ShrinkBlkBoolState s tmp' mrk' mclr' sstk' wsort' mcl' mcf' ticks') ⋆ R) m' →
      Q (ok, ()) m') :
    m8ShrinkBlkBoolSpec (c.hdr, beg, end_b, blvl, max_tr, ()) m Q X :=
  ⟨c, F0, s, keepLen, R, rfl, hcore, hmin, hno8, hbeg1, hbeg_end, hend_kl, hkl_cv,
    hblvl_pos, hblvl_lt, hblk, hkeep, hm, hQ⟩

/-- Rank #5 `full_min_shrink_m6` M8 contract (extends `m6MinShrinkWsortSpec` with
`search_ticks'` updates and constant `min_stk`). -/
def m8MinShrinkSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullOtfsWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
    1 ≤ s.core.tmp_len ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
    ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) ∧
    (∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
    (∀ k, 1 ≤ k → k < s.core.tmp_len →
      let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level) ∧
    (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.core.cur_level ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tmp' tl' mrk' mclr' sstk' wsort' mcl' mcf' conf' llits' mrem' ticks' m',
      let s' := m8MinShrinkState s tmp' tl' mrk' mclr' sstk' wsort' mcl' mcf' conf' llits'
        mrem' ticks'
      s'.LengthsOk c → FullOtfsWitnessInv c F0 F_cur s'.core → FullLitMarksClear c s' →
      1 ≤ tl' → tl' ≤ s.core.tmp_len → tmp'[0]? = s.core.tmp[0]? →
      ((tmp'.take tl').map fun x => x.toNat / 2).Nodup →
      (∀ j, 1 ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        0 < lv ∧ lv < s.core.cur_level ∧
        lv ≤ (s.core.lvl[(tmp'[tl' - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat)) →
      (FullMem c s' ⋆ R) m' → Q () m'

theorem m8MinShrinkSpec_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hlen : s.LengthsOk c) (hw : FullOtfsWitnessInv c F0 F_cur s.core)
    (hlm : FullLitMarksClear c s)
    (htl1 : 1 ≤ s.core.tmp_len) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (hnd : ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup)
    (hEnt : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)))
    (hvals : ∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hlvls : ∀ k, 1 ≤ k → k < s.core.tmp_len →
      let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level)
    (h0_lvl : (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
      s.core.cur_level)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ tmp' tl' mrk' mclr' sstk' wsort' mcl' mcf' conf' llits' mrem' ticks' m',
      let s' := m8MinShrinkState s tmp' tl' mrk' mclr' sstk' wsort' mcl' mcf' conf' llits'
        mrem' ticks'
      s'.LengthsOk c → FullOtfsWitnessInv c F0 F_cur s'.core → FullLitMarksClear c s' →
      1 ≤ tl' → tl' ≤ s.core.tmp_len → tmp'[0]? = s.core.tmp[0]? →
      ((tmp'.take tl').map fun x => x.toNat / 2).Nodup →
      (∀ j, 1 ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        0 < lv ∧ lv < s.core.cur_level ∧
        lv ≤ (s.core.lvl[(tmp'[tl' - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat)) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    m8MinShrinkSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, htl1, htl_cv, hnd, hEnt, hvals, hlvls, h0_lvl, hm,
   hQ⟩

theorem m8MinShrinkSpec_elim {h m Q X} (hs : m8MinShrinkSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullOtfsWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
      1 ≤ s.core.tmp_len ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
      ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) ∧
      (∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
      (∀ k, 1 ≤ k → k < s.core.tmp_len →
        let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
        0 < lv ∧ lv < s.core.cur_level) ∧
      (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.core.cur_level ∧
      (FullMem c s ⋆ R) m ∧
      ∀ tmp' tl' mrk' mclr' sstk' wsort' mcl' mcf' conf' llits' mrem' ticks' m',
        let s' := m8MinShrinkState s tmp' tl' mrk' mclr' sstk' wsort' mcl' mcf' conf' llits'
          mrem' ticks'
        s'.LengthsOk c → FullOtfsWitnessInv c F0 F_cur s'.core → FullLitMarksClear c s' →
        1 ≤ tl' → tl' ≤ s.core.tmp_len → tmp'[0]? = s.core.tmp[0]? →
        ((tmp'.take tl').map fun x => x.toNat / 2).Nodup →
        (∀ j, 1 ≤ j → j < tl' →
          let l := (tmp'[j]?.getD 0#32).toNat
          let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
          l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
          0 < lv ∧ lv < s.core.cur_level ∧
          lv ≤ (s.core.lvl[(tmp'[tl' - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
        (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat)) →
        (FullMem c s' ⋆ R) m' → Q () m' := hs

theorem m8MinShrinkSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : m8MinShrinkSpec xs m Q X) : m8MinShrinkSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

/-! ## 2. Combinatorial DFS Invariants (`FrameCov`, `M8MinStkInv`, `M8MinStInv`) -/

theorem m8_toSpecsMinInv {k : FullCoreState} {keep : List Nat}
    (h : Full.FullMinMarkInv k keep) : FullMinMarkInv k keep :=
  ⟨h.mrk_dom, h.clr_cov, h.rem_sound⟩

theorem m8_toFullMinInv {k : FullCoreState} {keep : List Nat}
    (h : FullMinMarkInv k keep) : Full.FullMinMarkInv k keep :=
  ⟨h.mrk_dom, h.clr_cov, h.rem_sound⟩

theorem m8_specs_minMarkSpec_of_full {args m Q X}
    (h : fullMinMarkSpec args m Q X) : Full.fullMinMarkSpec args m Q X := by
  rcases args with ⟨h0, v, tag, ⟨⟩⟩
  rcases h with ⟨c, s, R, rfl, hlen, hm, hrest⟩
  refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
  dsimp only at hrest ⊢
  split
  · simpa only [↓reduceIte, ite_eq_left ‹_›] using hrest
  · rename_i hneg
    simp only [ite_eq_right hneg] at hrest ⊢
    intro m' hm'
    dsimp only [Full.fullMinMarkState, Full.fullMinMarkCore] at hm'
    by_cases hcz : s.core.mrk[v.toNat]?.getD 0#8 = 0#8
    · by_cases hlt : s.core.min_clr_len < s.core.cur_vars
      · simp only [hcz, hlt, ↓reduceIte, not_true_eq_false, and_self, and_false,
          bv_ofNat_toNat_eq] at hrest hm'
        exact hrest m' hm'
      · simp only [hcz, hlt, ↓reduceIte, not_false_eq_true, and_self, and_false] at hrest hm'
        exact hrest m' hm'
    · simp only [hcz, ↓reduceIte, ne_eq, not_false_eq_true, false_and] at hrest hm'
      exact hrest m' hm'

theorem m8_bv32_mask31_hi_eq0 : ((0x80000000#32 : BitVec 32) &&& 0x7FFFFFFF#32).toNat = 0 := by
  decide

theorem m8_bv32_mask31_zero_eq0 : ((0#32 : BitVec 32) &&& 0x7FFFFFFF#32).toNat = 0 := by
  decide

theorem m8_bv32_mask31_or1_eq {pword : BitVec 32} (h : (pword &&& 0x7FFFFFFF#32) = 0#32) :
    ((pword ||| 1#32) &&& 0x7FFFFFFF#32).toNat = 1 := by
  rw [BitVec.and_or_distrib_right, h, BitVec.zero_or]; decide

theorem m8_bv32_mask31_hi_or_add1 (pword y : BitVec 32) (hy : y.toNat < 2 ^ 31) :
    (((pword &&& 0x80000000#32) ||| y) &&& 0x7FFFFFFF#32).toNat = y.toNat := by
  have hz : (pword &&& 0x80000000#32) &&& 0x7FFFFFFF#32 = 0#32 := by
    rw [BitVec.and_assoc, show (0x80000000#32 : BitVec 32) &&& 0x7FFFFFFF#32 = 0#32 from rfl,
      BitVec.and_zero]
  rw [BitVec.and_or_distrib_right, hz, BitVec.zero_or, BitVec.toNat_and,
    show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hy]

theorem m8_bv64_shl1_toNat {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat = 2 * x.toNat := by
  have hs : (BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64 = 1 := rfl
  rw [hs, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, Nat.pow_one,
    Nat.mod_eq_of_lt hx]

theorem m8_bv64_shl1_add1_toNat {x : BitVec 64} (hx : 2 * x.toNat + 1 < 2 ^ 64) :
    (x <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1).toNat = 2 * x.toNat + 1 := by
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_add, m8_bv64_shl1_toNat (by omega), h1, Nat.mod_eq_of_lt hx]

abbrev m8RsnLit (k : FullCoreState) (rsn : BitVec 32) (pos : Nat) : Nat :=
  if (rsn &&& 0x80000000#32) ≠ 0#32 then (rsn &&& 0x7FFFFFFF#32).toNat
  else (k.arena[rsn.toNat + 3 + pos]?.getD 0#32).toNat

abbrev M8FrameCov (k : FullCoreState) (mrk1 : List (BitVec 8)) (idx lim : Nat) : Prop :=
  let p0 := (k.trl[idx]?.getD 0#32).toNat
  let rsn := k.rsns[p0 / 2]?.getD 0xFFFFFFFF#32
  rsn ≠ 0xFFFFFFFF#32 ∧
  if (rsn &&& 0x80000000#32) ≠ 0#32 then
    let ot := (rsn &&& 0x7FFFFFFF#32).toNat
    ot < 2 * k.cur_vars ∧
    (1 ≤ lim →
      ∃ j < idx, (k.trl[j]?.getD 0#32).toNat = ot ^^^ 1 ∧
        ((k.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[ot / 2]?.getD 0#8 &&& 2#8) ≠ 0#8))
  else
    rsn.toNat ∈ fullArenaClauseRefsCore k ∧
    fullArenaClauseGarbCore k rsn.toNat = false ∧
    2 < fullArenaClauseSizeCore k rsn.toNat ∧
    ∀ j < lim, j < fullArenaClauseSizeCore k rsn.toNat →
      let q := (k.arena[rsn.toNat + 3 + j]?.getD 0#32).toNat
      q / 2 = p0 / 2 ∨
      ∃ m < idx, (k.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
        ((k.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)

private theorem m8FrameCov_arena_lits_bd {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {cref : Nat} (href : cref ∈ fullArenaClauseRefsCore s.core) :
    cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length := by
  obtain ⟨_, hw⟩ := hcore.2
  have hwf := hw.arena.refs_wf cref href
  have := hwf.2.2.1; have := hwf.2.2.2.1
  have := hcore.1.core_ok.arena_len_le; have := hcore.1.core_ok.arena_len_arr; omega

theorem m8FrameCov_arena_lits_mem {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {cref pos : Nat}
    (href : cref ∈ fullArenaClauseRefsCore s.core)
    (hp : pos < fullArenaClauseSizeCore s.core cref) :
    (s.core.arena[cref + 3 + pos]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore s.core cref := by
  have hbd := m8FrameCov_arena_lits_bd hcore href
  rw [mem_fullArenaClauseLitsCore_iff hbd]
  exact ⟨pos, hp, by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]⟩

private theorem m8FrameCov_zero {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) (mrk1 : List (BitVec 8)) {idx : Nat}
    (hi : idx < s.core.trail_end)
    (hlvl : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hrsn : s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
      0xFFFFFFFF#32) :
    M8FrameCov s.core mrk1 idx 0 := by
  obtain ⟨_, hw⟩ := hcore.2
  have hrs := hw.reason_inv_below idx hi hlvl hrsn
  dsimp only [M8FrameCov] at hrs ⊢
  refine ⟨hrsn, ?_⟩
  by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
      0x80000000#32) ≠ 0#32
  · simp only [eq_true hbin, ↓reduceIte] at hrs ⊢
    exact ⟨hrs.1, fun h1 => by omega⟩
  · simp only [eq_false hbin, ↓reduceIte] at hrs ⊢
    have hwf := hw.arena.refs_wf _ hrs.1
    exact ⟨hrs.1, hrs.2.1, hwf.2.1, fun _ hj => by omega⟩

private theorem m8FrameCov_mono {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mrk1 mrk2 : List (BitVec 8)} {idx lim : Nat}
    (hmono : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (h : M8FrameCov s.core mrk1 idx lim) : M8FrameCov s.core mrk2 idx lim := by
  obtain ⟨_, hw⟩ := hcore.2
  dsimp only [M8FrameCov] at h ⊢
  rcases h with ⟨hne, hif⟩; refine ⟨hne, ?_⟩
  by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
      0x80000000#32) ≠ 0#32
  · simp only [eq_true hbin, ↓reduceIte] at hif ⊢
    refine ⟨hif.1, fun h1 => ?_⟩
    obtain ⟨j, hj, hjeq, hdep⟩ := hif.2 h1
    refine ⟨j, hj, hjeq, hdep.elim Or.inl fun hm2 => Or.inr (hmono _ (by omega) hm2)⟩
  · simp only [eq_false hbin, ↓reduceIte] at hif ⊢
    refine ⟨hif.1, hif.2.1, hif.2.2.1, fun j hj1 hj2 => ?_⟩
    rcases hif.2.2.2 j hj1 hj2 with hvar | ⟨m, hm, hmeq, hdep⟩
    · exact Or.inl hvar
    · have hl_mem := m8FrameCov_arena_lits_mem hcore hif.1 hj2
      have hlt2 := hw.arena.lits_lt _ hif.1 hif.2.1 _ hl_mem
      exact Or.inr ⟨m, hm, hmeq, hdep.elim Or.inl fun hm2 => Or.inr (hmono _ (by omega) hm2)⟩

theorem m8FrameCov_step {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mrk1 : List (BitVec 8)} {idx pos : Nat}
    (hi : idx < s.core.trail_end)
    (hlvl : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hcov : M8FrameCov s.core mrk1 idx pos)
    (hlt : pos < if (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
        0x80000000#32) ≠ 0#32 then 1 else fullArenaClauseSizeCore s.core
        (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat)
    (hstep :
      let q := m8RsnLit s.core
        (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32) pos
      q / 2 = (s.core.trl[idx]?.getD 0#32).toNat / 2 ∨
      ∃ j < idx, (s.core.trl[j]?.getD 0#32).toNat = q ^^^ 1 ∧
        ((s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)) :
    M8FrameCov s.core mrk1 idx (pos + 1) := by
  obtain ⟨_, hw⟩ := hcore.2
  dsimp only [M8FrameCov] at hcov ⊢
  rcases hcov with ⟨hne, hif⟩
  have hrs := hw.reason_inv_below idx hi hlvl hne
  refine ⟨hne, ?_⟩
  dsimp only [m8RsnLit] at hstep ⊢
  dsimp only at hif hrs hlt hstep ⊢
  by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
      0x80000000#32) ≠ 0#32
  · simp only [eq_true hbin, ↓reduceIte] at hif hrs hlt hstep ⊢
    refine ⟨hif.1, fun _ => ?_⟩
    rcases hstep with hvar | ⟨j, hj, hjeq, hdep⟩
    · obtain ⟨j, hj, hjeq, _⟩ := hrs.2.2
      have hln := litVar_litNeg (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat
      unfold litVar litNeg at hln
      have hjp : j = idx := hw.trail_vars_nodup j idx (by omega) hi (by rw [hjeq, hln]; exact hvar)
      omega
    · exact ⟨j, hj, hjeq, hdep⟩
  · simp only [eq_false hbin, ↓reduceIte] at hif hrs hlt hstep ⊢
    refine ⟨hif.1, hif.2.1, hif.2.2.1, fun j hj1 hj2 => ?_⟩
    by_cases hjp : j < pos
    · exact hif.2.2.2 j hjp hj2
    · have hjeq : j = pos := by omega
      subst hjeq
      rcases hstep with hvar | hok
      · have hmem := m8FrameCov_arena_lits_mem hcore hif.1 hj2
        rcases hrs.2.2 _ hmem with hqeq | ⟨k, hk, hkeq, _⟩
        · exact Or.inl (congrArg (· / 2) hqeq)
        · have hln := litVar_litNeg (s.core.arena[(s.core.rsns[(s.core.trl[idx]?.getD
            0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat + 3 + j]?.getD 0#32).toNat
          unfold litVar litNeg at hln
          have hkp : k = idx := hw.trail_vars_nodup k idx (by omega) hi
            (by rw [hkeq, hln]; exact hvar)
          omega
      · exact Or.inr hok

private theorem m8FrameCov_to_hrsn {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mrk1 : List (BitVec 8)} {idx lim : Nat}
    (hi : idx < s.core.trail_end)
    (hlvl : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hcov : M8FrameCov s.core mrk1 idx lim)
    (hlim : (if (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
        0x80000000#32) ≠ 0#32 then 1 else fullArenaClauseSizeCore s.core
        (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat) ≤ lim) :
    let p0 := (s.core.trl[idx]?.getD 0#32).toNat
    let rsn := s.core.rsns[p0 / 2]?.getD 0xFFFFFFFF#32
    rsn ≠ 0xFFFFFFFF#32 ∧
    if (rsn &&& 0x80000000#32) ≠ 0#32 then
      let ot := (rsn &&& 0x7FFFFFFF#32).toNat
      ot < 2 * s.core.cur_vars ∧
      ∃ j < idx, (s.core.trl[j]?.getD 0#32).toNat = ot ^^^ 1 ∧
        ((s.core.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[ot / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
    else
      rsn.toNat ∈ fullArenaClauseRefsCore s.core ∧
      fullArenaClauseGarbCore s.core rsn.toNat = false ∧
      ∀ q ∈ fullArenaClauseLitsCore s.core rsn.toNat,
        q = p0 ∨ ∃ j < idx, (s.core.trl[j]?.getD 0#32).toNat = q ^^^ 1 ∧
          ((s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) := by
  obtain ⟨_, hw⟩ := hcore.2
  dsimp only [M8FrameCov] at hcov
  rcases hcov with ⟨hne, hif⟩; refine ⟨hne, ?_⟩
  dsimp only at hif hlim ⊢
  by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
      0x80000000#32) ≠ 0#32
  · simp only [eq_true hbin, ↓reduceIte] at hif hlim ⊢
    exact ⟨hif.1, hif.2 (by omega)⟩
  · have hrs := hw.reason_inv_below idx hi hlvl hne
    simp only [eq_false hbin, ↓reduceIte] at hif hrs hlim ⊢
    refine ⟨hif.1, hif.2.1, fun q hq => ?_⟩
    have hbd := m8FrameCov_arena_lits_bd hcore hif.1
    obtain ⟨j, hj, hjeq⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hq
    have hq' := hif.2.2.2 j (by omega) hj
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hjeq] at hq'
    rcases hq' with hdiv | hex
    · rcases hrs.2.2 q hq with hqp | ⟨k, hk, hkeq, _⟩
      · exact Or.inl hqp
      · have hln := litVar_litNeg q
        unfold litVar litNeg at hln
        have hkp := hw.trail_vars_nodup k idx (by omega) hi (by rw [hkeq, hln]; exact hdiv)
        omega
    · exact Or.inr hex

theorem m8FrameCov_edge_exists {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mrk1 : List (BitVec 8)} {idx pos : Nat}
    (hi : idx < s.core.trail_end)
    (hlvl : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hcov : M8FrameCov s.core mrk1 idx pos)
    (hlt : pos < if (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
        0x80000000#32) ≠ 0#32 then 1 else fullArenaClauseSizeCore s.core
        (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat)
    (hneq : m8RsnLit s.core
        (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32) pos / 2 ≠
      (s.core.trl[idx]?.getD 0#32).toNat / 2) :
    let q := m8RsnLit s.core
      (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32) pos
    q < 2 * s.core.cur_vars ∧
    ∃ cidx < idx, (s.core.trl[cidx]?.getD 0#32).toNat = q ^^^ 1 ∧
      (s.core.lvl[q / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
  obtain ⟨_, hw⟩ := hcore.2
  dsimp only [M8FrameCov, m8RsnLit] at hcov hlt hneq ⊢
  rcases hcov with ⟨hne, hif⟩
  have hrs := hw.reason_inv_below idx hi hlvl hne
  dsimp only at hif hrs hlt hneq ⊢
  by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
      0x80000000#32) ≠ 0#32
  · simp only [eq_true hbin, ↓reduceIte] at hif hrs hlt hneq ⊢
    exact ⟨hrs.1, hrs.2.2⟩
  · simp only [eq_false hbin, ↓reduceIte] at hif hrs hlt hneq ⊢
    have hmem := m8FrameCov_arena_lits_mem hcore hif.1 hlt
    have hq_lt := hw.arena.lits_lt _ hif.1 hif.2.1 _ hmem
    rcases hrs.2.2 _ hmem with hqeq | hdep
    · exact absurd (by rw [hqeq]) hneq
    · exact ⟨hq_lt, hdep⟩

abbrev M8EdgeChild (k : FullCoreState) (pidx pos cidx : Nat) : Prop :=
  let rsn := k.rsns[(k.trl[pidx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
  let q := m8RsnLit k rsn pos
  cidx < pidx ∧ (k.trl[cidx]?.getD 0#32).toNat = q ^^^ 1

private theorem m8_dec_chain_lt {idxs : List Nat}
    (hdec : ∀ j (hj : j + 1 < idxs.length), idxs[j + 1] < idxs[j]'(by omega))
    {i j : Nat} (hij : i < j) (hj : j < idxs.length) :
    idxs[j] < idxs[i]'(Nat.lt_trans hij hj) := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hj_lt := hdec j hj
    by_cases heq : i = j
    · subst heq; exact hj_lt
    · exact Nat.lt_trans hj_lt (ih (by omega) (by omega))

structure M8MinStkInv (k : FullCoreState) (wsort1 : List (BitVec 32))
    (mrk1 : List (BitVec 8)) (sp idx0 : Nat) (idxs : List Nat) (reqCov : Bool) : Prop where
  len : idxs.length = sp + 1
  idx0_eq : idxs[0]? = some idx0
  bd : ∀ j (hj : j < idxs.length), idxs[j] < k.trail_end
  dec : ∀ j (hj : j + 1 < idxs.length), idxs[j + 1] < idxs[j]
  lvl_le_root : ∀ j (hj : j < idxs.length),
    (k.lvl[(k.trl[idxs[j]]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (k.lvl[(k.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
  slot : ∀ j (hj : j < idxs.length),
    let vj := (k.trl[idxs[j]]?.getD 0#32).toNat / 2
    (wsort1[2 * j]?.getD 0#32).toNat = vj ∧ (1 ≤ j → mrk1[vj]?.getD 0#8 = 0#8)
  cov : reqCov = true → ∀ j (hj : j < idxs.length),
    let posj := (wsort1[2 * j + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat
    let rsn := k.rsns[(k.trl[idxs[j]]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
    (∀ _hj1 : j + 1 < idxs.length, 1 ≤ posj ∧
      posj ≤ (if (rsn &&& 0x80000000#32) ≠ 0#32 then 1 else fullArenaClauseSizeCore k rsn.toNat) ∧
      M8EdgeChild k idxs[j] (posj - 1) idxs[j + 1]) ∧
    M8FrameCov k mrk1 idxs[j] (if j + 1 = idxs.length then posj else posj - 1)

theorem m8MinStkInv_drop_cov {k : FullCoreState} {wsort1 : List (BitVec 32)}
    {mrk1 : List (BitVec 8)} {sp idx0 : Nat} {idxs : List Nat}
    (h : M8MinStkInv k wsort1 mrk1 sp idx0 idxs true) :
    M8MinStkInv k wsort1 mrk1 sp idx0 idxs false :=
  ⟨h.len, h.idx0_eq, h.bd, h.dec, h.lvl_le_root, h.slot, fun hc => by cases hc⟩

private theorem m8MinStkInv_poison_other {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {wsort1 mclr1 : List (BitVec 32)}
    {mrk1 : List (BitVec 8)} {sp idx0 u_idx mcl1 : Nat} {mcf1 ticks1 : BitVec 64}
    {idxs : List Nat} (h : M8MinStkInv s.core wsort1 mrk1 sp idx0 idxs false)
    (hu_idx : ∀ j (hj : j < idxs.length), u_idx < idxs[j])
    (hmrk_eq : ∀ w < s.core.cur_vars, w ≠ (s.core.trl[u_idx]?.getD 0#32).toNat / 2 →
      mrk1[w]?.getD 0#8 = (fullMinMarkCore
        (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1).core
        ((s.core.trl[u_idx]?.getD 0#32).toNat / 2) 4#8).mrk[w]?.getD 0#8) :
    M8MinStkInv s.core wsort1
      (fullMinMarkCore (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1).core
        ((s.core.trl[u_idx]?.getD 0#32).toNat / 2) 4#8).mrk sp idx0 idxs false := by
  obtain ⟨_, hw⟩ := hcore.2
  refine ⟨h.len, h.idx0_eq, h.bd, h.dec, h.lvl_le_root, fun j hj => ?_, fun hc => by cases hc⟩
  refine ⟨(h.slot j hj).1, fun hj1 => ?_⟩
  have hvj : (s.core.trl[idxs[j]]?.getD 0#32).toNat / 2 < s.core.cur_vars := by
    have := hw.trail_lits_lt idxs[j] (h.bd j hj); omega
  have hne : (s.core.trl[idxs[j]]?.getD 0#32).toNat / 2 ≠
      (s.core.trl[u_idx]?.getD 0#32).toNat / 2 := fun heq => by
    have hlt := hu_idx j hj
    have := hw.trail_vars_nodup idxs[j] u_idx (h.bd j hj) (Nat.lt_trans hlt (h.bd j hj)) heq
    omega
  rw [← hmrk_eq _ hvj hne]
  exact (h.slot j hj).2 hj1

theorem m8MinStkInv_step_top {c : FullCfg} {k : FullCoreState}
    {wsort1 : List (BitVec 32)} {mrk1 : List (BitVec 8)} {sp idx0 : Nat} {idxs : List Nat}
    (h : M8MinStkInv k wsort1 mrk1 sp idx0 idxs true)
    (hw_len : wsort1.length = 2 * c.max_vars) (hsp : sp < c.max_vars) (newPos : BitVec 32)
    (hcov_top : ∀ hk : sp < idxs.length,
      M8FrameCov k mrk1 idxs[sp] (newPos &&& 0x7FFFFFFF#32).toNat) :
    M8MinStkInv k (wsort1.set (2 * sp + 1) newPos) mrk1 sp idx0 idxs true := by
  have hlt_stk : 2 * sp + 1 < wsort1.length := by omega
  refine ⟨h.len, h.idx0_eq, h.bd, h.dec, h.lvl_le_root, fun j hj => ?_, fun _ j hj => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact h.slot j hj
  · have hlen := h.len
    by_cases htop : j = sp
    · subst htop
      rw [List.getElem?_set_self hlt_stk, Option.getD_some]
      refine ⟨fun hk1 => by omega, ?_⟩
      simp only [show j + 1 = idxs.length by omega, ↓reduceIte]
      exact hcov_top hj
    · have hne_len : ¬ (j + 1 = idxs.length) := by omega
      rw [List.getElem?_set_ne (by omega)]
      simpa only [hne_len, ↓reduceIte] using h.cov rfl j hj

private theorem m8MinStkInv_push {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {wsort1 : List (BitVec 32)} {mrk1 : List (BitVec 8)}
    {sp idx0 u_idx : Nat} {idxs : List Nat}
    (h : M8MinStkInv s.core wsort1 mrk1 sp idx0 idxs true)
    (hroot_lvl : (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hw_len : wsort1.length = 2 * c.max_vars) (hsp1 : sp + 1 < c.max_vars)
    {u_bv par_pw ch_pw : BitVec 32}
    (hpos_eq : (par_pw &&& 0x7FFFFFFF#32).toNat =
      (wsort1[2 * sp + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat + 1)
    (hch_eq : (ch_pw &&& 0x7FFFFFFF#32).toNat = 0)
    (hu_bd : u_idx < idxs[sp]'(by have := h.len; omega))
    (hu_eq : u_bv.toNat = (s.core.trl[u_idx]?.getD 0#32).toNat / 2)
    (hu_lvl : (s.core.lvl[(s.core.trl[u_idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hpos_lt : (wsort1[2 * sp + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat <
      (if (s.core.rsns[(s.core.trl[idxs[sp]'(by have := h.len; omega)]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then 1
        else fullArenaClauseSizeCore s.core (s.core.rsns[(s.core.trl[idxs[sp]'(by
          have := h.len; omega)]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat))
    (hmrk_u : mrk1[u_bv.toNat]?.getD 0#8 = 0#8)
    (hrsn_u : s.core.rsns[u_bv.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hedge : M8EdgeChild s.core (idxs[sp]'(by have := h.len; omega))
      (wsort1[2 * sp + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat u_idx) :
    let wsort3 := ((wsort1.set (2 * sp + 1) par_pw).set (2 * (sp + 1)) u_bv).set
      (2 * (sp + 1) + 1) ch_pw
    M8MinStkInv s.core wsort3 mrk1 (sp + 1) idx0 (idxs ++ [u_idx]) true := by
  have hlen := h.len
  have hsp_lt : sp < idxs.length := by omega
  have hbd_sp := h.bd sp hsp_lt
  have hsp_cov := h.cov rfl sp hsp_lt
  simp only [show sp + 1 = idxs.length by omega, ↓reduceIte] at hsp_cov
  refine ⟨by simp [hlen], by rw [List.getElem?_append_left (by omega)]; exact h.idx0_eq,
    fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun _ j hj => ?_⟩
  · by_cases hj_last : j < idxs.length
    · rw [List.getElem_append_left hj_last]; exact h.bd j hj_last
    · have hj_eq : j = idxs.length := by simp at hj; omega
      subst hj_eq; rw [List.getElem_append_right (le_refl _)]; simp; omega
  · by_cases hj_in : j + 1 < idxs.length
    · rw [List.getElem_append_left hj_in, List.getElem_append_left (by omega)]
      exact h.dec j hj_in
    · have hj_eq : j = sp := by simp at hj; omega
      subst hj_eq
      rw [List.getElem_append_right (by omega), List.getElem_append_left hsp_lt]
      simp [hlen]; exact hu_bd
  · by_cases hj_lt : j < idxs.length
    · rw [List.getElem_append_left hj_lt]; exact h.lvl_le_root j hj_lt
    · have hj_eq : j = idxs.length := by simp at hj; omega
      subst hj_eq; rw [List.getElem_append_right (le_refl _)]
      simpa [hlen] using hu_lvl
  · by_cases hj_lt : j < idxs.length
    · rw [List.getElem_append_left hj_lt]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega)]
      exact h.slot j hj_lt
    · have hj_eq : j = sp + 1 := by simp at hj; omega
      subst hj_eq; rw [List.getElem_append_right (by omega)]; simp only [hlen, Nat.sub_self,
        List.getElem_cons_zero]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hw_len]; omega),
        Option.getD_some]
      refine ⟨hu_eq, fun _ => by rw [← hu_eq]; exact hmrk_u⟩
  · have h_len2 : (idxs ++ [u_idx]).length = sp + 2 := by simp [hlen]
    by_cases hj_sp : j = sp
    · subst hj_sp
      rw [List.getElem_append_left hsp_lt]
      have hne_end : ¬ (j + 1 = (idxs ++ [u_idx]).length) := by omega
      simp only [hne_end, ↓reduceIte]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by omega), Option.getD_some, hpos_eq]
      refine ⟨fun _ => ?_, ?_⟩
      · rw [List.getElem_append_right (by omega)]; simp only [hlen, Nat.sub_self,
          List.getElem_cons_zero]
        refine ⟨by omega, hpos_lt, ?_⟩
        simpa [Nat.add_sub_cancel] using hedge
      · simpa only [Nat.add_sub_cancel] using hsp_cov.2
    · by_cases hj_last : j = sp + 1
      · subst hj_last
        rw [List.getElem_append_right (by omega)]
        simp only [hlen, Nat.sub_self, List.getElem_cons_zero, h_len2, ↓reduceIte]
        rw [List.getElem?_set_self (by simp [hw_len]; omega), Option.getD_some, hch_eq]
        refine ⟨fun h1 => by omega, ?_⟩
        exact m8FrameCov_zero hcore mrk1 (Nat.lt_trans hu_bd hbd_sp)
          (Nat.lt_of_le_of_lt hu_lvl hroot_lvl) (by rwa [← hu_eq])
      · have hj_lt : j < sp := by simp at hj; omega
        have hj1_lt : j + 1 < idxs.length := by omega
        have hne1 : ¬ (j + 1 = idxs.length) := by omega
        have hne2 : ¬ (j + 1 = (idxs ++ [u_idx]).length) := by omega
        have hprev := h.cov rfl j (by omega)
        simp only [hne1, ↓reduceIte] at hprev
        simp only [hne2, ↓reduceIte]
        rw [List.getElem_append_left (by omega),
          List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega)]
        refine ⟨fun _ => ?_, hprev.2⟩
        rw [List.getElem_append_left hj1_lt]; exact hprev.1 hj1_lt

private theorem m8MinStkInv_pop {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {wsort1 mclr1 : List (BitVec 32)}
    {mrk1 : List (BitVec 8)} {sp idx0 mcl1 : Nat} {mcf1 ticks1 : BitVec 64} {idxs : List Nat}
    (h : M8MinStkInv s.core wsort1 mrk1 sp idx0 idxs true) (hsp : 0 < sp)
    (hroot_lvl : (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hmrk_len : mrk1.length = c.max_vars)
    (hmrk_eq : ∀ w < s.core.cur_vars, w ≠ (s.core.trl[idxs[sp]'(by have := h.len; omega)]?.getD
        0#32).toNat / 2 →
      mrk1[w]?.getD 0#8 = (fullMinMarkCore
        (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1).core
        ((s.core.trl[idxs[sp]'(by have := h.len; omega)]?.getD 0#32).toNat / 2)
        2#8).mrk[w]?.getD 0#8)
    (hmono : ∀ w < s.core.cur_vars, (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      ((fullMinMarkCore (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1).core
        ((s.core.trl[idxs[sp]'(by have := h.len; omega)]?.getD 0#32).toNat / 2)
        2#8).mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8) :
    let mrk2 := (fullMinMarkCore (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1).core
      ((s.core.trl[idxs[sp]'(by have := h.len; omega)]?.getD 0#32).toNat / 2) 2#8).mrk
    M8MinStkInv s.core wsort1 mrk2 (sp - 1) idx0 (idxs.take sp) true := by
  obtain ⟨_, hw⟩ := hcore.2
  have hlen := h.len
  have hsp_lt : sp < idxs.length := by omega
  have htake_len : (idxs.take sp).length = sp := by rw [List.length_take]; omega
  refine ⟨by omega, by rw [List.getElem?_take_of_lt (by omega)]; exact h.idx0_eq,
    fun j hj => by rw [List.getElem_take]; exact h.bd j (by omega),
    fun j hj => by
      rw [List.getElem_take, List.getElem_take]
      exact h.dec j (by rw [htake_len] at hj; omega),
    fun j hj => by rw [List.getElem_take]; exact h.lvl_le_root j (by omega),
    fun j hj => ?_, fun _ j hj => ?_⟩
  · rw [List.getElem_take]
    have hslot := h.slot j (by omega)
    refine ⟨hslot.1, fun hj1 => ?_⟩
    have hvj : (s.core.trl[idxs[j]]?.getD 0#32).toNat / 2 < s.core.cur_vars := by
      have := hw.trail_lits_lt idxs[j] (h.bd j (by omega)); omega
    have hne : (s.core.trl[idxs[j]]?.getD 0#32).toNat / 2 ≠
        (s.core.trl[idxs[sp]]?.getD 0#32).toNat / 2 := fun heq => by
      have hlt := m8_dec_chain_lt h.dec (by rw [htake_len] at hj; omega : j < sp) hsp_lt
      have := hw.trail_vars_nodup idxs[j] idxs[sp] (h.bd j (by omega)) (h.bd sp hsp_lt) heq
      omega
    rw [← hmrk_eq _ hvj hne]; exact hslot.2 hj1
  · have hne1 : ¬ (j + 1 = idxs.length) := by rw [htake_len] at hj; omega
    have hprev := h.cov rfl j (by omega)
    simp only [hne1, ↓reduceIte] at hprev
    rw [List.getElem_take]
    by_cases htop : j + 1 = (idxs.take sp).length
    · simp only [htop, ↓reduceIte]
      have hj_sp1 : j = sp - 1 := by omega
      subst hj_sp1
      have hchild := hprev.1 (by omega)
      simp only [show sp - 1 + 1 = sp by omega] at hchild
      refine ⟨fun hk => by omega, ?_⟩
      have hcov_step : M8FrameCov s.core
          (fullMinMarkCore (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1).core
            ((s.core.trl[idxs[sp]]?.getD 0#32).toNat / 2) 2#8).mrk
          idxs[sp - 1] ((wsort1[2 * (sp - 1) + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat - 1 + 1) :=
        m8FrameCov_step hcore (h.bd (sp - 1) (by omega))
          (Nat.lt_of_le_of_lt (h.lvl_le_root (sp - 1) (by omega)) hroot_lvl)
          (m8FrameCov_mono hcore hmono hprev.2)
          (by have := hchild.1; have := hchild.2.1; omega)
          (Or.inr ⟨idxs[sp], hchild.2.2.1, hchild.2.2.2, Or.inr (by
            dsimp only [fullMinMarkCore, m8MinLitDfsState]
            have hl := litVar_litNeg (m8RsnLit s.core (s.core.rsns[(s.core.trl[idxs[sp - 1]]?.getD
              0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
              ((wsort1[2 * (sp - 1) + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat - 1))
            unfold litVar litNeg at hl
            have hvar : m8RsnLit s.core (s.core.rsns[(s.core.trl[idxs[sp - 1]]?.getD
                0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
                ((wsort1[2 * (sp - 1) + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat - 1) / 2 =
                (s.core.trl[idxs[sp]]?.getD 0#32).toNat / 2 := by
              rw [← hl, ← hchild.2.2.2]
            have hbd_sp : (s.core.trl[idxs[sp]]?.getD 0#32).toNat / 2 < mrk1.length := by
              have := hw.trail_lits_lt idxs[sp] (h.bd sp hsp_lt)
              have := hcore.1.core_ok.cur_vars_le
              rw [hmrk_len]; omega
            rw [hvar, List.getElem?_set_self hbd_sp, Option.getD_some]
            exact bv8_and2_of_or2 _)⟩)
      have hpos_ge1 := hchild.1
      rwa [Nat.sub_add_cancel hpos_ge1] at hcov_step
    · simp only [htop, ↓reduceIte]
      refine ⟨fun _ => ?_, m8FrameCov_mono hcore hmono hprev.2⟩
      rw [List.getElem_take]; exact hprev.1 (by omega)

structure M8MinStInv (c : FullCfg) (s : FullState) (keepSet : List Nat)
    (mrk1 : List (BitVec 8)) (wsort1 mclr1 : List (BitVec 32))
    (mcl1 : Nat) (mcf1 ticks1 : BitVec 64) : Prop where
  mrk_len : mrk1.length = c.max_vars
  wsort_len : wsort1.length = 2 * c.max_vars
  mclr_len : mclr1.length = c.max_vars
  mcl_le : mcl1 ≤ c.max_vars
  mrk_above : ∀ w, s.core.cur_vars ≤ w → mrk1[w]? = s.core.mrk[w]?
  min_inv : FullMinMarkInv (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1).core keepSet
  mono2 : ∀ w < s.core.cur_vars,
    (s.core.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8
  bit8 : ∀ w < s.core.cur_vars,
    (mrk1[w]?.getD 0#8 &&& 8#8) = (s.core.mrk[w]?.getD 0#8 &&& 8#8)

theorem m8FullOtfsCoreInv_with_state {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {mrk1 : List (BitVec 8)} {wsort1 mclr1 : List (BitVec 32)} {mcl1 : Nat}
    {mcf1 ticks1 : BitVec 64}
    (h : FullOtfsCoreInv c F0 s) (hmrk : mrk1.length = c.max_vars)
    (hw : wsort1.length = 2 * c.max_vars) (hmclr : mclr1.length = c.max_vars)
    (hmcl : mcl1 ≤ c.max_vars) :
    FullOtfsCoreInv c F0 (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1) := by
  have hc := fullOtfsCoreInv_with_min (mcf1 := mcf1) h hmrk h.1.core_ok.min_stk_len hmclr hmcl
  exact ⟨⟨hc.1.core_ok, { hc.1.scratch_ok with wsort_len := hw }⟩, hc.2⟩

theorem M8MinStInv.core {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keepSet : List Nat} {mrk1 : List (BitVec 8)} {wsort1 mclr1 : List (BitVec 32)}
    {mcl1 : Nat} {mcf1 ticks1 : BitVec 64} (hcore : FullOtfsCoreInv c F0 s)
    (h : M8MinStInv c s keepSet mrk1 wsort1 mclr1 mcl1 mcf1 ticks1) :
    FullOtfsCoreInv c F0 (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1) :=
  m8FullOtfsCoreInv_with_state hcore h.mrk_len h.wsort_len h.mclr_len h.mcl_le

theorem m8MinStInv_with_wsort {c : FullCfg} {s : FullState} {keepSet : List Nat}
    {mrk1 : List (BitVec 8)} {wsort1 mclr1 wsort' : List (BitVec 32)} {mcl1 : Nat}
    {mcf1 ticks1 : BitVec 64}
    (h : M8MinStInv c s keepSet mrk1 wsort1 mclr1 mcl1 mcf1 ticks1)
    (hw' : wsort'.length = 2 * c.max_vars) :
    M8MinStInv c s keepSet mrk1 wsort' mclr1 mcl1 mcf1 ticks1 :=
  { h with
    wsort_len := hw'
    min_inv := fullMinMarkInv_with_mstk h.min_inv s.core.min_stk }

theorem m8MinStInv_with_ticks {c : FullCfg} {s : FullState} {keepSet : List Nat}
    {mrk1 : List (BitVec 8)} {wsort1 mclr1 : List (BitVec 32)} {mcl1 : Nat}
    {mcf1 ticks1 ticks' : BitVec 64}
    (h : M8MinStInv c s keepSet mrk1 wsort1 mclr1 mcl1 mcf1 ticks1) :
    M8MinStInv c s keepSet mrk1 wsort1 mclr1 mcl1 mcf1 ticks' :=
  { h with min_inv := h.min_inv }

private theorem m8MinStInv_mark {c : FullCfg} {s : FullState} {keepSet : List Nat}
    {mrk1 : List (BitVec 8)} {wsort1 mclr1 : List (BitVec 32)} {mcl1 : Nat}
    {mcf1 ticks1 : BitVec 64} (hcv : s.core.cur_vars ≤ c.max_vars)
    (hsi : M8MinStInv c s keepSet mrk1 wsort1 mclr1 mcl1 mcf1 ticks1)
    {v : Nat} (hv : v < s.core.cur_vars) (hz : mrk1[v]?.getD 0#8 = 0#8) (tag : BitVec 8)
    (htag : tag = 2#8 ∨ tag = 4#8)
    (hmin' : FullMinMarkInv
      (fullMinMarkCore (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1).core v tag)
      keepSet) :
    let k_p := (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1).core
    let k' := fullMinMarkCore k_p v tag
    M8MinStInv c s keepSet k'.mrk wsort1 k'.min_clr k'.min_clr_len k'.min_clr_full ticks1 ∧
    (∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (k'.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8) := by
  intro k_p k'
  have hv_max : v < c.max_vars := by omega
  have hmono_prev : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (k'.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
    intro w _ hw2; dsimp only [k', fullMinMarkCore]
    by_cases hweq : w = v
    · subst w; rw [hz] at hw2; exact absurd rfl hw2
    · rwa [List.getElem?_set_ne (Ne.symm hweq)]
  have hbit8' : ∀ w < s.core.cur_vars,
      (k'.mrk[w]?.getD 0#8 &&& 8#8) = (s.core.mrk[w]?.getD 0#8 &&& 8#8) := by
    intro w hw; dsimp only [k', fullMinMarkCore]
    by_cases hweq : w = v
    · subst w
      dsimp only [k_p, m8MinLitDfsState]
      rw [List.getElem?_set_self (by rw [hsi.mrk_len]; exact hv_max), Option.getD_some]
      have hz' : mrk1[v]?.getD 0#8 = 0#8 := hz
      rw [hz', ← hsi.bit8 v hv, hz']
      rcases htag with rfl | rfl <;> decide
    · rw [List.getElem?_set_ne (Ne.symm hweq)]; exact hsi.bit8 w hw
  have hab' : ∀ w, s.core.cur_vars ≤ w → k'.mrk[w]? = s.core.mrk[w]? := fun w hw => by
    dsimp only [k', fullMinMarkCore]; rw [List.getElem?_set_ne (by omega)]; exact hsi.mrk_above w hw
  have hmclr' : k'.min_clr.length = c.max_vars := by
    dsimp only [k', k_p, fullMinMarkCore, m8MinLitDfsState]
    by_cases hlt : mcl1 < s.core.cur_vars <;> simp [hz, hlt, hsi.mclr_len]
  have hmcl' : k'.min_clr_len ≤ c.max_vars := by
    have hmcl_le := hsi.mcl_le
    dsimp only [k', k_p, fullMinMarkCore, m8MinLitDfsState]
    by_cases hlt : mcl1 < s.core.cur_vars
    · simp only [hz, hlt, and_self, ↓reduceIte]; omega
    · simp only [hz, hlt, and_false, ↓reduceIte]; omega
  have hmrk' : k'.mrk.length = c.max_vars := by
    dsimp only [k', k_p, fullMinMarkCore]; rw [List.length_set]; exact hsi.mrk_len
  refine ⟨⟨hmrk', hsi.wsort_len, hmclr', hmcl', hab', hmin',
    fun w hw hws => hmono_prev w hw (hsi.mono2 w hw hws), hbit8'⟩, hmono_prev⟩

theorem m8_fullMinMarkSpec_zero_inv {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {mrk1 : List (BitVec 8)} {wsort1 mclr1 : List (BitVec 32)}
    {mcl1 : Nat} {mcf1 ticks1 : BitVec 64} {m1 : Mem 64} {Q' : Post []} {X' : XPost}
    (hcore : FullOtfsCoreInv c F0 s) (hmrk : mrk1.length = c.max_vars)
    (hw : wsort1.length = 2 * c.max_vars) (hmclr : mclr1.length = c.max_vars)
    (hmcl : mcl1 ≤ c.max_vars)
    (hm1 : (FullMem c (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1) ⋆ R) m1)
    {v : BitVec 32} (hv : v.toNat < s.core.cur_vars) (hz : mrk1[v.toNat]?.getD 0#8 = 0#8)
    (tag : BitVec 8)
    (hpost : ∀ m',
      let k1 := (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1).core
      let k2 := fullMinMarkCore k1 v.toNat tag
      (FullMem c (m8MinLitDfsState s k2.mrk wsort1 k2.min_clr k2.min_clr_len k2.min_clr_full
        ticks1) ⋆ R) m' → Q' () m') :
    fullMinMarkSpec (c.hdr, v, tag, ()) m1 Q' X' := by
  let st1 := m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1
  have hlen1 : st1.LengthsOk c := (m8FullOtfsCoreInv_with_state hcore hmrk hw hmclr hmcl).1
  refine ⟨c, st1, R, rfl, hlen1, hm1, ?_⟩
  dsimp only
  have hc1 : ¬ (st1.core.cur_vars ≤ v.toNat ∨ (st1.core.mrk[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8) :=
    fun h => h.elim (fun hle => by dsimp only [st1, m8MinLitDfsState] at hle; omega) fun hne => by
      change (mrk1[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8 at hne; rw [hz] at hne; simp at hne
  have hc2 : ¬ (st1.core.mrk[v.toNat]?.getD 0#8 ≠ 0#8) := fun h => h hz
  simp only [eq_false hc1, eq_false hc2, ↓reduceIte]
  have hzor : (0#8 : BitVec 8) ||| tag = tag := BitVec.zero_or
  by_cases hlt : mcl1 < s.core.cur_vars
  · have hlt' : st1.core.min_clr_len < st1.core.cur_vars := hlt
    simp only [eq_true hlt', ↓reduceIte]
    intro m' hm'; have hp := hpost m'
    dsimp only [fullMinMarkCore, m8MinLitDfsState] at hp ⊢
    have hmcl1' : mcl1 < s.core.cur_vars := hlt
    simp only [hz, hmcl1', and_self, not_true_eq_false, and_false, ↓reduceIte, hzor] at hp
    have hv_eq : BitVec.ofNat 32 v.toNat = v := bv_ofNat_toNat_eq v
    dsimp only [st1, m8MinLitDfsState] at hm'
    rw [hz, hzor] at hm'; rw [hv_eq] at hp; exact hp hm'
  · have hlt' : ¬ st1.core.min_clr_len < st1.core.cur_vars := hlt
    simp only [eq_false hlt', ↓reduceIte]
    intro m' hm'; have hp := hpost m'
    dsimp only [fullMinMarkCore, m8MinLitDfsState] at hp ⊢
    have hmcl1' : ¬ mcl1 < s.core.cur_vars := hlt
    simp only [hz, hmcl1', and_self, and_false, not_false_eq_true, ↓reduceIte, hzor] at hp
    dsimp only [st1, m8MinLitDfsState] at hm'
    rw [hz, hzor] at hm'; exact hp hm'

theorem m8MinLit_state_step {s : FullState} {mrk1 : List (BitVec 8)}
    {wsort1 mclr1 : List (BitVec 32)} {mcl1 : Nat} {mcf1 ticks1 : BitVec 64}
    (v : Nat) (tag : BitVec 8) :
    fullMinMarkStepState (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1) v tag =
      m8MinLitDfsState s
        (fullMinMarkStepState
          (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1) v tag).core.mrk
        wsort1
        (fullMinMarkStepState
          (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1) v tag).core.min_clr
        (fullMinMarkStepState
          (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1) v tag).core.min_clr_len
        (fullMinMarkStepState
          (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1) v tag).core.min_clr_full
        ticks1 := by
  dsimp only [fullMinMarkStepState, fullMinMarkStepCore, fullMinMarkCore, m8MinLitDfsState]
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-! ## 3. Pop/Leaf/Stack Push State Lemmas -/

theorem m8MinLitDfs_ok_res {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {wsort1 : List (BitVec 32)} {mrk1 : List (BitVec 8)}
    {sp idx0 : Nat} {idxs : List Nat}
    (hstk : M8MinStkInv s.core wsort1 mrk1 sp idx0 idxs true)
    (hi0_lvl : (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hw_len : wsort1.length = 2 * c.max_vars) (hsp : sp < c.max_vars)
    (hsp_idxs : sp < idxs.length)
    (newPos : BitVec 32) (hpos_eq : (newPos &&& 0x7FFFFFFF#32).toNat =
      (wsort1[2 * sp + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat + 1)
    (hpos_lt : (wsort1[2 * sp + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat <
      (if (s.core.rsns[(s.core.trl[idxs[sp]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
          0x80000000#32) ≠ 0#32 then 1 else fullArenaClauseSizeCore s.core
        (s.core.rsns[(s.core.trl[idxs[sp]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32).toNat))
    {u_idx : Nat}
    (hok :
      let q := m8RsnLit s.core
        (s.core.rsns[(s.core.trl[idxs[sp]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
        (wsort1[2 * sp + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat
      q / 2 = (s.core.trl[idxs[sp]'hsp_idxs]?.getD 0#32).toNat / 2 ∨
      u_idx < idxs[sp]'hsp_idxs ∧ (s.core.trl[u_idx]?.getD 0#32).toNat = q ^^^ 1 ∧
        ((s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)) :
    M8MinStkInv s.core (wsort1.set (2 * sp + 1) newPos) mrk1 sp idx0 idxs true := by
  refine m8MinStkInv_step_top hstk hw_len hsp newPos fun hk => ?_
  have hcov_sp := (hstk.cov rfl sp hsp_idxs).2
  have hlen := hstk.len
  simp only [show sp + 1 = idxs.length by omega, ↓reduceIte] at hcov_sp
  rw [hpos_eq]
  exact m8FrameCov_step hcore (hstk.bd sp hsp_idxs)
    (Nat.lt_of_le_of_lt (hstk.lvl_le_root sp hsp_idxs) hi0_lvl) hcov_sp hpos_lt
    (hok.elim Or.inl fun ⟨hu, heq, hdep⟩ => Or.inr ⟨u_idx, hu, heq, hdep⟩)

theorem m8MinLitDfs_poison_leaf {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keepSet : List Nat} {mrk1 : List (BitVec 8)} {wsort1 mclr1 : List (BitVec 32)}
    {mcl1 sp idx0 u_idx : Nat} {mcf1 ticks1 : BitVec 64} {idxs : List Nat}
    {R : Mem 64 → Prop} {m1 : Mem 64} {Q' : Post []} {X' : XPost}
    (hcore : FullOtfsCoreInv c F0 s)
    (hsi : M8MinStInv c s keepSet mrk1 wsort1 mclr1 mcl1 mcf1 ticks1)
    (hstk : M8MinStkInv s.core wsort1 mrk1 sp idx0 idxs false)
    (hsp_idxs : sp < idxs.length)
    (hu_bd : u_idx < idxs[sp]'hsp_idxs)
    {u_bv : BitVec 32}
    (hu_eq : u_bv.toNat = (s.core.trl[u_idx]?.getD 0#32).toNat / 2)
    (hu_lt : u_bv.toNat < s.core.cur_vars)
    (hno8_u : (mrk1[u_bv.toNat]?.getD 0#8 &&& 8#8) = 0#8)
    (hno2_u : (mrk1[u_bv.toNat]?.getD 0#8 &&& 2#8) = 0#8)
    (hno4_u : (mrk1[u_bv.toNat]?.getD 0#8 &&& 4#8) = 0#8)
    (hm1 : (FullMem c (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1) ⋆ R) m1)
    (hpost : ∀ (mrk' : List (BitVec 8)) (mclr' : List (BitVec 32)) (mcl' : Nat) (mcf' : BitVec 64)
        (m' : Mem 64),
      let k' := fullMinMarkCore (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1).core
        u_bv.toNat 4#8
      mrk' = k'.mrk → mclr' = k'.min_clr → mcl' = k'.min_clr_len → mcf' = k'.min_clr_full →
      M8MinStInv c s keepSet mrk' wsort1 mclr' mcl' mcf' ticks1 →
      (FullMem c (m8MinLitDfsState s mrk' wsort1 mclr' mcl' mcf' ticks1) ⋆ R) m' →
      M8MinStkInv s.core wsort1 mrk' sp idx0 idxs false → Q' () m') :
    fullMinMarkSpec (c.hdr, u_bv, (4 : BitVec 32).setWidth 8, ()) m1 Q' X' := by
  have hz : mrk1[u_bv.toNat]?.getD 0#8 = 0#8 :=
    bv8_zero_of_masks24 _ (hsi.min_inv.mrk_dom _ hu_lt) hno8_u hno2_u hno4_u
  refine m8_fullMinMarkSpec_zero_inv hcore hsi.mrk_len hsi.wsort_len hsi.mclr_len hsi.mcl_le hm1
    hu_lt hz ((4 : BitVec 32).setWidth 8) fun m' hm' => ?_
  have h4 : (4 : BitVec 32).setWidth 8 = 4#8 := rfl
  rw [h4] at hm'
  have hcv := hcore.1.core_ok.cur_vars_le
  have hmin_p := fullMinMarkInv_step_poison (m8FullOtfsCoreInv_with_state hcore hsi.mrk_len
    hsi.wsort_len hsi.mclr_len hsi.mcl_le) hsi.min_inv hu_lt hno8_u
  have hmin_p' : FullMinMarkInv (fullMinMarkCore
      (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1).core u_bv.toNat 4#8) keepSet := by
    dsimp only [fullMinMarkStepState, fullMinMarkStepCore, m8MinLitDfsState] at hmin_p
    have hlt_neg : ¬ s.core.cur_vars ≤ u_bv.toNat := Nat.not_le.mpr hu_lt
    have hand0 : (mrk1[u_bv.toNat]?.getD 0#8 &&& 4#8) = 0#8 := by rw [hz]; decide
    simp only [hlt_neg, hand0, ne_eq, not_true_eq_false, or_self, ↓reduceIte] at hmin_p
    exact hmin_p
  obtain ⟨hsi', _⟩ := m8MinStInv_mark hcv hsi hu_lt hz 4#8 (Or.inr rfl) hmin_p'
  refine hpost _ _ _ _ m' rfl rfl rfl rfl hsi' hm' ?_
  have hdec : ∀ j (hj : j < idxs.length), u_idx < idxs[j] := fun j hj => by
    have hlen := hstk.len
    by_cases hje : j = sp
    · subst hje; exact hu_bd
    · exact Nat.lt_trans hu_bd (m8_dec_chain_lt hstk.dec (by omega : j < sp) hsp_idxs)
  have hmrk_eq : ∀ w < s.core.cur_vars, w ≠ (s.core.trl[u_idx]?.getD 0#32).toNat / 2 →
      mrk1[w]?.getD 0#8 = (fullMinMarkCore
        (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1).core
        ((s.core.trl[u_idx]?.getD 0#32).toNat / 2) 4#8).mrk[w]?.getD 0#8 := fun w _ hne => by
    dsimp only [fullMinMarkCore, m8MinLitDfsState]
    rw [List.getElem?_set_ne (by omega)]
  have hp := m8MinStkInv_poison_other hcore hstk hdec hmrk_eq
  rwa [← hu_eq] at hp

theorem m8MinLitDfs_pop_state {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keepSet : List Nat} {mrk1 : List (BitVec 8)} {wsort1 mclr1 : List (BitVec 32)}
    {mcl1 sp idx0 : Nat} {mcf1 ticks1 : BitVec 64} {idxs : List Nat}
    {R : Mem 64 → Prop} {m1 : Mem 64} {Q' : Post []} {X' : XPost}
    (hcore : FullOtfsCoreInv c F0 s)
    (hsi : M8MinStInv c s keepSet mrk1 wsort1 mclr1 mcl1 mcf1 ticks1)
    (hstk : M8MinStkInv s.core wsort1 mrk1 sp idx0 idxs true) (hsp : 0 < sp)
    (hsp_idxs : sp < idxs.length)
    (hi0_lvl : (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    {v : BitVec 32} (hv_nat : v.toNat = (s.core.trl[idxs[sp]'hsp_idxs]?.getD 0#32).toNat / 2)
    (hv_lt : v.toNat < s.core.cur_vars) {lim : Nat}
    (hlim : (if (s.core.rsns[(s.core.trl[idxs[sp]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then 1 else fullArenaClauseSizeCore s.core
      (s.core.rsns[(s.core.trl[idxs[sp]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32).toNat) ≤ lim)
    (hcov : M8FrameCov s.core mrk1 (idxs[sp]'hsp_idxs) lim)
    (hm1 : (FullMem c (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1) ⋆ R) m1)
    (hpost : ∀ k' m',
      k' = fullMinMarkCore (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1).core
        v.toNat 2#8 →
      M8MinStInv c s keepSet k'.mrk wsort1 k'.min_clr k'.min_clr_len k'.min_clr_full ticks1 →
      M8MinStkInv s.core wsort1 k'.mrk (sp - 1) idx0 (idxs.take sp) true →
      (FullMem c (m8MinLitDfsState s k'.mrk wsort1 k'.min_clr k'.min_clr_len k'.min_clr_full
        ticks1) ⋆ R) m' → Q' () m') :
    fullMinMarkSpec (c.hdr, v, (2 : BitVec 32).setWidth 8, ()) m1 Q' X' := by
  have hz : mrk1[v.toNat]?.getD 0#8 = 0#8 := by
    rw [hv_nat]; exact (hstk.slot sp hsp_idxs).2 (by omega)
  refine m8_fullMinMarkSpec_zero_inv hcore hsi.mrk_len hsi.wsort_len hsi.mclr_len hsi.mcl_le hm1
    hv_lt hz ((2 : BitVec 32).setWidth 8) fun m' hm' => ?_
  have h2 : (2 : BitVec 32).setWidth 8 = 2#8 := rfl
  rw [h2] at hm'
  have hrs := m8FrameCov_to_hrsn hcore (hstk.bd sp hsp_idxs)
    (Nat.lt_of_le_of_lt (hstk.lvl_le_root sp hsp_idxs) hi0_lvl) hcov hlim
  have hsc := m8FullOtfsCoreInv_with_state (mcf1 := mcf1) (ticks1 := ticks1) hcore
    hsi.mrk_len hsi.wsort_len hsi.mclr_len hsi.mcl_le
  have hno8_v : (mrk1[v.toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
    rw [hz]; decide
  have hmin' := fullMinMarkInv_mark_rem hsc hsi.min_inv (hstk.bd sp hsp_idxs)
    (by dsimp only [m8MinLitDfsState]
        exact Nat.lt_of_le_of_lt (hstk.lvl_le_root sp hsp_idxs) hi0_lvl)
    (by dsimp only [m8MinLitDfsState]; rw [← hv_nat]; exact hno8_v)
    hrs
  change FullMinMarkInv (fullMinMarkCore
    (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1).core
    ((s.core.trl[idxs[sp]'hsp_idxs]?.getD 0#32).toNat / 2) 2#8) keepSet at hmin'
  rw [show (s.core.trl[idxs[sp]'hsp_idxs]?.getD 0#32).toNat / 2 = v.toNat from hv_nat.symm]
    at hmin'
  obtain ⟨hsi', hmono'⟩ := m8MinStInv_mark hcore.1.core_ok.cur_vars_le hsi hv_lt hz 2#8
    (Or.inl rfl) hmin'
  have hmrk_eq : ∀ w < s.core.cur_vars, w ≠ (s.core.trl[idxs[sp]'hsp_idxs]?.getD 0#32).toNat / 2 →
      mrk1[w]?.getD 0#8 = (fullMinMarkCore
        (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1).core
        ((s.core.trl[idxs[sp]'hsp_idxs]?.getD 0#32).toNat / 2) 2#8).mrk[w]?.getD 0#8 :=
    fun w _ hne => by
      dsimp only [fullMinMarkCore, m8MinLitDfsState]; rw [List.getElem?_set_ne (by omega)]
  have hstk' := m8MinStkInv_pop hcore hstk hsp hi0_lvl hsi.mrk_len hmrk_eq
    (fun w hw h2w => by
      simpa only [hv_nat] using hmono' w hw h2w)
  rw [← hv_nat] at hstk'
  exact hpost _ m' rfl hsi' hstk' hm'

theorem m8_store_wsort {c : FullCfg} {s : FullState}
    {mrk : List (BitVec 8)} {wsort mclr : List (BitVec 32)} {mcl : Nat}
    {mcf ticks : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hbi : i.toNat < wsort.length)
    (hm : (FullMem c (m8MinLitDfsState s mrk wsort mclr mcl mcf ticks) ⋆ R) m) :
    storeOk m i32 (c.pWsort + i * 4) ∧
    (FullMem c (m8MinLitDfsState s mrk (wsort.set i.toNat v) mclr mcl mcf ticks) ⋆ R)
      (storeMem m i32 (c.pWsort + i * 4) v) :=
  c0_store_full_wsort (s := m8MinLitDfsState s mrk wsort mclr mcl mcf ticks) (i := i) v hbi hm

theorem m8MinLitDfs_ok_final {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keepSet : List Nat} {mrk1 : List (BitVec 8)} {wsort1 mclr1 : List (BitVec 32)}
    {mcl1 idx0 lim : Nat} {mcf1 ticks1 : BitVec 64} {root_lit : BitVec 32}
    (hcore : FullOtfsCoreInv c F0 s)
    (hsi : M8MinStInv c s keepSet mrk1 wsort1 mclr1 mcl1 mcf1 ticks1)
    (hi0 : idx0 < s.core.trail_end)
    (hi0_eq : (s.core.trl[idx0]?.getD 0#32).toNat = root_lit.toNat ^^^ 1)
    (hrl_lvl : (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat < s.core.cur_level)
    (hno8 : ∀ v < s.core.cur_vars,
      (s.core.lvl[v]?.getD 0#32).toNat ≤ (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat →
      (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    (hlim : (if (s.core.rsns[root_lit.toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      then 1 else fullArenaClauseSizeCore s.core
        (s.core.rsns[root_lit.toNat / 2]?.getD 0xFFFFFFFF#32).toNat) ≤ lim)
    (hcov : M8FrameCov s.core mrk1 idx0 lim) :
    (∀ keep', (∀ l ∈ keepSet, l = root_lit.toNat ∨ l ∈ keep') →
      Full.FullMinMarkInv (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1).core keep') ∧
    Full.FullMinMarkInv (Full.fullMinMarkCore
      (m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1).core
      (root_lit.toNat / 2) 2#8) keepSet := by
  have hcv := hcore.1.core_ok.cur_vars_le
  have hrv : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = root_lit.toNat / 2 := by
    have hl := litVar_litNeg root_lit.toNat; unfold litVar litNeg at hl; rw [hi0_eq, hl]
  have hr_bd : root_lit.toNat / 2 < s.core.cur_vars := by
    have := hcore.2.choose_spec.trail_lits_lt idx0 hi0; omega
  rw [← hrv] at hlim
  have hrs := m8FrameCov_to_hrsn hcore hi0 (by rw [hrv]; exact hrl_lvl) hcov hlim
  have hsc := hsi.core hcore
  have hrs_lit : let rsn := s.core.rsns[(root_lit.toNat ^^^ 1) / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 ∧ if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * s.core.cur_vars ∧ ∃ j < idx0, (s.core.trl[j]?.getD 0#32).toNat = ot ^^^ 1 ∧
          ((s.core.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[ot / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
      else rsn.toNat ∈ fullArenaClauseRefsCore s.core ∧
        fullArenaClauseGarbCore s.core rsn.toNat = false ∧
        ∀ q ∈ fullArenaClauseLitsCore s.core rsn.toNat, q = root_lit.toNat ^^^ 1 ∨
          ∃ j < idx0, (s.core.trl[j]?.getD 0#32).toNat = q ^^^ 1 ∧
            ((s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) := by
    have hl := litVar_litNeg root_lit.toNat; unfold litVar litNeg at hl
    simpa only [← hl, hi0_eq] using hrs
  have hno8_r : (mrk1[root_lit.toNat / 2]?.getD 0#8 &&& 8#8) = 0#8 := by
    rw [hsi.bit8 (root_lit.toNat / 2) hr_bd]; exact hno8 _ hr_bd (le_refl _)
  refine ⟨fun keep' hsub => m8_toFullMinInv (fullMinMarkInv_drop hsc hsi.min_inv hsub hrl_lvl hi0
    hi0_eq hrs_lit), ?_⟩
  have hmr := fullMinMarkInv_mark_rem hsc hsi.min_inv hi0
    (by dsimp only [m8MinLitDfsState]; rw [hrv]; exact hrl_lvl)
    (by dsimp only [m8MinLitDfsState]; rw [hrv]; exact hno8_r) hrs
  have hrv' : ((m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1).core.trl[idx0]?.getD
      0#32).toNat / 2 = root_lit.toNat / 2 := hrv
  rw [hrv'] at hmr; exact m8_toFullMinInv hmr

theorem m8MinLit_unwind_post {c : FullCfg} {F0 : CNF Nat} {F_cur0 : List (List Nat)}
    {s : FullState} {keepSet : List Nat} {mrk_j : List (BitVec 8)}
    {wsort_b mclr_j : List (BitVec 32)} {mcl_j : Nat} {mcf_j ticks_b : BitVec 64}
    {idxs_b : List Nat} {sp_b j_bv : BitVec 64} {idx0 : Nat} {sv : BitVec 32}
    {mrk_b : List (BitVec 8)}
    (hcore : FullOtfsCoreInv c F0 s) (hw0 : FullOtfsWitnessInv c F0 F_cur0 s.core)
    (hsi_j : M8MinStInv c s keepSet mrk_j wsort_b mclr_j mcl_j mcf_j ticks_b)
    (hstk_b : M8MinStkInv s.core wsort_b mrk_b sp_b.toNat idx0 idxs_b false)
    (hj_idxs : j_bv.toNat < idxs_b.length)
    (hsv_nat : sv.toNat = (s.core.trl[idxs_b[j_bv.toNat]'hj_idxs]?.getD 0#32).toNat / 2)
    (hsv_lt : sv.toNat < s.core.cur_vars)
    (hno8_sv : (mrk_j[sv.toNat]?.getD 0#8 &&& 8#8) = 0#8)
    (hz_sv : mrk_j[sv.toNat]?.getD 0#8 = 0#8)
    (hj1_nat : (j_bv + 1#64).toNat = j_bv.toNat + 1)
    (hclr_j : ∀ k, j_bv.toNat ≤ k → ∀ hk : k < idxs_b.length,
      mrk_j[(s.core.trl[idxs_b[k]'hk]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) :
    let k4 := Full.fullMinMarkCore
      (m8MinLitDfsState s mrk_j wsort_b mclr_j mcl_j mcf_j ticks_b).core sv.toNat 4#8
    M8MinStInv c s keepSet k4.mrk wsort_b k4.min_clr k4.min_clr_len k4.min_clr_full ticks_b ∧
    ∀ k, (j_bv + 1#64).toNat ≤ k → ∀ hk : k < idxs_b.length,
      k4.mrk[(s.core.trl[idxs_b[k]'hk]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8 := by
  have hcv_b := hcore.1.core_ok.cur_vars_le
  have hmin_j1 := fullMinMarkInv_step_poison (hsi_j.core hcore) hsi_j.min_inv hsv_lt hno8_sv
  have hmin_j1' : FullMinMarkInv (Full.fullMinMarkCore
      (m8MinLitDfsState s mrk_j wsort_b mclr_j mcl_j mcf_j ticks_b).core sv.toNat 4#8)
      keepSet := by
    dsimp only [fullMinMarkStepState, fullMinMarkStepCore, m8MinLitDfsState] at hmin_j1
    have hlt_neg : ¬ s.core.cur_vars ≤ sv.toNat := Nat.not_le.mpr hsv_lt
    have hand0 : (mrk_j[sv.toNat]?.getD 0#8 &&& 4#8) = 0#8 := by rw [hz_sv]; decide
    simp only [hlt_neg, hand0, ne_eq, not_true_eq_false, or_self, ↓reduceIte] at hmin_j1
    exact hmin_j1
  obtain ⟨hsi_j1, _⟩ := m8MinStInv_mark hcv_b hsi_j hsv_lt hz_sv 4#8 (Or.inr rfl) hmin_j1'
  refine ⟨hsi_j1, fun k hk1 hk2 => ?_⟩
  rw [hj1_nat] at hk1
  have hne_v : (s.core.trl[idxs_b[k]'hk2]?.getD 0#32).toNat / 2 ≠ sv.toNat := by
    rw [hsv_nat]; intro heq
    have hij := hw0.trail_vars_nodup idxs_b[k] idxs_b[j_bv.toNat]
      (hstk_b.bd k hk2) (hstk_b.bd j_bv.toNat hj_idxs) heq
    have := m8_dec_chain_lt hstk_b.dec (by omega : j_bv.toNat < k) hk2
    omega
  dsimp only [Full.fullMinMarkCore, m8MinLitDfsState]
  rw [List.getElem?_set_ne hne_v.symm]; exact hclr_j k (by omega) hk2

theorem m8MinLit_leaf_pre {c : FullCfg} {s : FullState}
    {keepSet : List Nat} {mrk1 : List (BitVec 8)} {wsort1 mclr1 : List (BitVec 32)}
    {mcl1 idx0 u_idx : Nat} {mcf1 ticks1 : BitVec 64}
    {sp : BitVec 64} {idxs : List Nat} {lit : BitVec 32} {root_lit : BitVec 32}
    (hsi : M8MinStInv c s keepSet mrk1 wsort1 mclr1 mcl1 mcf1 ticks1)
    (hstk : M8MinStkInv s.core wsort1 mrk1 sp.toNat idx0 idxs true)
    (hsp_idxs : sp.toNat < idxs.length)
    (hu_idx_eq : (s.core.trl[u_idx]?.getD 0#32).toNat = lit.toNat ^^^ 1)
    (hu_lvl_le : (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hu_bd_lt : (lit >>> 1).toNat < s.core.cur_vars)
    (hno8 : ∀ v < s.core.cur_vars,
      (s.core.lvl[v]?.getD 0#32).toNat ≤ (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat →
      (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    (hrv_root : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = root_lit.toNat / 2) :
    (lit >>> 1).toNat = (s.core.trl[u_idx]?.getD 0#32).toNat / 2 ∧
    (s.core.lvl[(s.core.trl[u_idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
    (mrk1[(lit >>> 1).toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
  have hu_nat_idx : (lit >>> 1).toNat = (s.core.trl[u_idx]?.getD 0#32).toNat / 2 := by
    have hl := litVar_litNeg lit.toNat; unfold litVar litNeg at hl
    rw [bv32_lshr_1, ← hl, ← hu_idx_eq]
  have hu_lvl_root : (s.core.lvl[(s.core.trl[u_idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
    have h1 : (s.core.trl[u_idx]?.getD 0#32).toNat / 2 = lit.toNat / 2 := by
      rw [← hu_nat_idx, bv32_lshr_1]
    rw [h1]; exact Nat.le_trans hu_lvl_le (hstk.lvl_le_root sp.toNat hsp_idxs)
  have hno8_u : (mrk1[(lit >>> 1).toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
    rw [hsi.bit8 _ hu_bd_lt]; refine hno8 _ hu_bd_lt ?_
    rw [hu_nat_idx, ← hrv_root]; exact hu_lvl_root
  exact ⟨hu_nat_idx, hu_lvl_root, hno8_u⟩

theorem m8MinLit_push_stk {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keepSet : List Nat} {mrk1 : List (BitVec 8)} {wsort1 mclr1 : List (BitVec 32)}
    {mcl1 idx0 u_idx : Nat} {mcf1 ticks2 : BitVec 64}
    {sp : BitVec 64} {idxs : List Nat} {rsn lit : BitVec 32} {pos : BitVec 32}
    {par_pw ch_pw : BitVec 32}
    (hcore : FullOtfsCoreInv c F0 s)
    (hsi2 : M8MinStInv c s keepSet mrk1 wsort1 mclr1 mcl1 mcf1 ticks2)
    (hstk : M8MinStkInv s.core wsort1 mrk1 sp.toNat idx0 idxs true)
    (hi0_lvl : (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hsp_idxs : sp.toNat < idxs.length)
    (hsp1_lt : sp.toNat + 1 < c.max_vars)
    (hpar_eq : (par_pw &&& 0x7FFFFFFF#32).toNat =
      (wsort1[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat + 1)
    (hch0 : (ch_pw &&& 0x7FFFFFFF#32).toNat = 0)
    (hpos_nat : pos.toNat = (wsort1[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat)
    (hpos_lt : pos.toNat < if (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
        0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then 1 else
        fullArenaClauseSizeCore s.core (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
          0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat)
    (hu_bd_lt : (lit >>> 1).toNat < s.core.cur_vars)
    (hu_idx_lt : u_idx < idxs[sp.toNat]'hsp_idxs)
    (hu_idx_eq : (s.core.trl[u_idx]?.getD 0#32).toNat = lit.toNat ^^^ 1)
    (hu_nat_idx : (lit >>> 1).toNat = (s.core.trl[u_idx]?.getD 0#32).toNat / 2)
    (hu_lvl_root : (s.core.lvl[(s.core.trl[u_idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hno8_u : (mrk1[(lit >>> 1).toNat]?.getD 0#8 &&& 8#8) = 0#8)
    (h2z : (mrk1[(lit >>> 1).toNat]?.getD 0#8 &&& 2#8) = 0#8)
    (h4z : (mrk1[(lit >>> 1).toNat]?.getD 0#8 &&& 4#8) = 0#8)
    (hrsn_u_ne : s.core.rsns[(lit >>> 1).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hrsn_eq : rsn = s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD
      0xFFFFFFFF#32)
    (hlit_eq : lit.toNat = m8RsnLit s.core rsn pos.toNat) :
    let wsort3 := ((wsort1.set (2 * sp.toNat + 1) par_pw).set (2 * (sp.toNat + 1))
      (lit >>> 1)).set (2 * (sp.toNat + 1) + 1) ch_pw
    M8MinStInv c s keepSet mrk1 wsort3 mclr1 mcl1 mcf1 ticks2 ∧
    M8MinStkInv s.core wsort3 mrk1 (sp.toNat + 1) idx0 (idxs ++ [u_idx]) true := by
  have hz_u : mrk1[(lit >>> 1).toNat]?.getD 0#8 = 0#8 :=
    bv8_zero_of_masks24 _ (hsi2.min_inv.mrk_dom _ hu_bd_lt) hno8_u h2z h4z
  have hstk3 := m8MinStkInv_push hcore hstk hi0_lvl hsi2.wsort_len hsp1_lt (u_bv := lit >>> 1)
    (par_pw := par_pw) (ch_pw := ch_pw) hpar_eq hch0 hu_idx_lt hu_nat_idx hu_lvl_root
    (by rwa [← hpos_nat]) hz_u hrsn_u_ne
    ⟨hu_idx_lt, by rw [← hpos_nat, ← hrsn_eq, ← hlit_eq]; exact hu_idx_eq⟩
  have hw3_len : (((wsort1.set (2 * sp.toNat + 1) par_pw).set (2 * (sp.toNat + 1))
      (lit >>> 1)).set (2 * (sp.toNat + 1) + 1) ch_pw).length = 2 * c.max_vars := by
    simp [hsi2.wsort_len]
  exact ⟨m8MinStInv_with_wsort hsi2 hw3_len, hstk3⟩

theorem m8MinLit_init_stk0 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {idx0 : Nat} {root_lit : BitVec 32}
    (hcore : FullOtfsCoreInv c F0 s)
    (hwl : s.scratch.wsort.length = 2 * c.max_vars)
    (hcv_pos : 0 < s.core.cur_vars)
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hi0 : idx0 < s.core.trail_end)
    (hrv_root : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = root_lit.toNat / 2)
    (hi0_lvl : (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hrsn_ne0 : s.core.rsns[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD
      0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) :
    M8MinStkInv s.core ((s.scratch.wsort.set (BitVec.signExtend 64 (0 : BitVec 32)).toNat
      (root_lit >>> 1)).set (BitVec.signExtend 64 (1 : BitVec 32)).toNat 0#32)
      s.core.mrk 0 idx0 [idx0] true := by
  have h0se : (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 := rfl
  have h1se : (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 := rfl
  refine ⟨rfl, rfl, fun j hj => ?_, fun j hj => by simp at hj, fun j hj => ?_,
    fun j hj => ?_, fun _ j hj => ?_⟩
  · have : j = 0 := by simp at hj; omega
    subst this; exact hi0
  · have : j = 0 := by simp at hj; omega
    subst this; exact le_refl _
  · have : j = 0 := by simp at hj; omega
    subst this; refine ⟨?_, fun h1 => by omega⟩
    rw [h0se, h1se, List.getElem?_set_ne (by decide),
      List.getElem?_set_self (by omega), Option.getD_some, bv32_lshr_1]
    exact hrv_root.symm
  · have : j = 0 := by simp at hj; omega
    subst this; refine ⟨fun h1 => by simp at h1, ?_⟩
    simp only [List.length_cons, List.length_nil, Nat.zero_add, ↓reduceIte]
    have hpos0 : (((s.scratch.wsort.set 0 (root_lit >>> 1)).set 1 0#32)[1]?.getD 0#32 &&&
        0x7FFFFFFF#32).toNat = 0 := by
      rw [List.getElem?_set_self (by rw [List.length_set]; omega), Option.getD_some]; decide
    rw [h0se, h1se, hpos0]
    exact m8FrameCov_zero hcore s.core.mrk hi0 hi0_lvl hrsn_ne0

end LeanQbe.T.Examples.Kissat.FullM8CoreParity
