/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts2
public import LeanQbe.T.Examples.Kissat.Src.Minimize
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Minimize` (`6` Functions)

Defines one canonical `Spec` per function in `Src.Minimize.fns`, proves `Spec.XFree`, provides
`_of`/`_elim`/`_monoX` helpers, and aligns `Spec.specs` 1:1 with `Src.Minimize.fns`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Minimize
open Kraken.Bedrock2.Test

public section

/-- Canonical specification for `full_min_mark`. -/
abbrev fullMinMarkSpec : Spec [i64, i32, i8] [] :=
  Proof.Spec.fullMinMarkSpec

/-- Canonical state projection for `full_min_lit_dfs_m8` and `full_shrink_lower_m8`. -/
abbrev m8MinLitDfsState (s : FullState) (mrk : List (BitVec 8))
    (wsort mclr : List (BitVec 32)) (mcl : Nat) (mcf ticks : BitVec 64) : FullState :=
  { core := { s.core with
      mrk := mrk, min_clr := mclr, min_clr_len := mcl, min_clr_full := mcf },
    scratch := { s.scratch with wsort := wsort, search_ticks := ticks } }

/-- Canonical state projection for `full_shrink_blk_bool_m8`. -/
abbrev m8ShrinkBlkBoolState (s : FullState) (tmp : List (BitVec 32))
    (mrk : List (BitVec 8)) (mclr sstk wsort : List (BitVec 32))
    (mcl : Nat) (mcf ticks : BitVec 64) : FullState :=
  { core := { s.core with
      tmp := tmp, mrk := mrk, min_clr := mclr, min_clr_len := mcl, min_clr_full := mcf },
    scratch := { s.scratch with
      shrink_stk := sstk, wsort := wsort, search_ticks := ticks } }

/-- Block-shrink state projection with `work_stk1` and `res_sz` for `full_min_shrink_m6`. -/
abbrev s13BlkState (s : FullState) (tmp : List (BitVec 32))
    (mrk : List (BitVec 8)) (mclr sstk wsort ws1 : List (BitVec 32))
    (mcl : Nat) (mcf ticks resSz : BitVec 64) : FullState :=
  { core := { s.core with
      tmp := tmp, mrk := mrk, min_clr := mclr, min_clr_len := mcl, min_clr_full := mcf },
    scratch := { s.scratch with
      shrink_stk := sstk, wsort := wsort, search_ticks := ticks,
      work_stk1 := ws1, res_sz := resSz } }

/-- Canonical post-state projection for `full_min_shrink_m6`. -/
abbrev fullMinShrinkState (s : FullState) (tmp : List (BitVec 32)) (tl : Nat)
    (mrk : List (BitVec 8)) (mclr sstk wsort ws1 : List (BitVec 32)) (mcl : Nat)
    (mcf conf llits mrem ticks resSz : BitVec 64) : FullState :=
  { core := { s.core with
      tmp := tmp, tmp_len := tl, mrk := mrk, min_clr := mclr,
      min_clr_len := mcl, min_clr_full := mcf },
    scratch := { s.scratch with
      conflicts := conf, learned_lits := llits, min_removed := mrem,
      shrink_stk := sstk, wsort := wsort, search_ticks := ticks,
      work_stk1 := ws1, res_sz := resSz } }

/-- Canonical specification for level-only `full_sort_tmp`. -/
@[expose] def fullSortTmpSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.tmp_len ≤ c.max_vars ∧
    (∀ k, 1 ≤ k → k < s.core.tmp_len → (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tmp' wsort' m',
      let s' : FullState :=
        { core := { s.core with tmp := tmp' }
          scratch := { s.scratch with wsort := wsort' } }
      s'.LengthsOk c → tmp'.length = c.max_vars →
      (s.core.tmp_len ≤ 32 → wsort' = s.scratch.wsort) →
      (tmp'.take s.core.tmp_len).Perm (s.core.tmp.take s.core.tmp_len) →
      (0 < s.core.tmp_len → tmp'[0]? = s.core.tmp[0]?) →
      (∀ j, 1 ≤ j → j < s.core.tmp_len →
        ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ tmp'[j]? = s.core.tmp[i]?) →
      (∀ i, 1 ≤ i → i < s.core.tmp_len →
        ∃ j, 1 ≤ j ∧ j < s.core.tmp_len ∧ s.core.tmp[i]? = tmp'[j]?) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → Q () m'

theorem fullSortTmpSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : fullSortTmpSpec xs m Q X) : fullSortTmpSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem fullSortTmpSpec_of {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost}
    (hlen : s.LengthsOk c) (htl : s.core.tmp_len ≤ c.max_vars)
    (hbd : ∀ k, 1 ≤ k → k < s.core.tmp_len →
      (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ tmp' wsort' m',
      let s' : FullState :=
        { core := { s.core with tmp := tmp' }
          scratch := { s.scratch with wsort := wsort' } }
      s'.LengthsOk c → tmp'.length = c.max_vars →
      (s.core.tmp_len ≤ 32 → wsort' = s.scratch.wsort) →
      (tmp'.take s.core.tmp_len).Perm (s.core.tmp.take s.core.tmp_len) →
      (0 < s.core.tmp_len → tmp'[0]? = s.core.tmp[0]?) →
      (∀ j, 1 ≤ j → j < s.core.tmp_len →
        ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ tmp'[j]? = s.core.tmp[i]?) →
      (∀ i, 1 ≤ i → i < s.core.tmp_len →
        ∃ j, 1 ≤ j ∧ j < s.core.tmp_len ∧ s.core.tmp[i]? = tmp'[j]?) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → Q () m') :
    fullSortTmpSpec (c.hdr, ()) m Q X :=
  ⟨c, s, R, rfl, hlen, htl, hbd, hm, hQ⟩

/-- Canonical specification for `full_min_lit_dfs_m8`. -/
@[expose] def fullMinLitDfsSpec : Spec [i64, i32, .bool, .bool] [.bool] :=
  fun (h, root_lit, _minimizing, _check_used, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (keepSet : List Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullOtfsCoreInv c F0 s ∧ FullMinMarkInv s.core keepSet ∧
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
        FullMinMarkInv s'.core keepSet →
        (ok = true →
          (∀ keep', (∀ l ∈ keepSet, l = root_lit.toNat ∨ l ∈ keep') →
            FullMinMarkInv s'.core keep') ∧
          FullMinMarkInv (fullMinMarkCore s'.core (root_lit.toNat / 2) 2#8) keepSet) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem fullMinLitDfsSpec_monoX {xs : Tup Val [i64, i32, .bool, .bool]} {m : Mem 64}
    {Q : Post [.bool]} {X X' : XPost}
    (h : fullMinLitDfsSpec xs m Q X) : fullMinLitDfsSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, ⟨⟩⟩; exact h

theorem fullMinLitDfsSpec_of {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keepSet : List Nat} {root_lit : BitVec 32} {minimizing check_used : Bool}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hcore : FullOtfsCoreInv c F0 s) (hmin : FullMinMarkInv s.core keepSet)
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
      FullMinMarkInv s'.core keepSet →
      (ok = true →
        (∀ keep', (∀ l ∈ keepSet, l = root_lit.toNat ∨ l ∈ keep') →
          FullMinMarkInv s'.core keep') ∧
        FullMinMarkInv (fullMinMarkCore s'.core (root_lit.toNat / 2) 2#8) keepSet) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    fullMinLitDfsSpec (c.hdr, root_lit, minimizing, check_used, ()) m Q X :=
  ⟨c, F0, s, keepSet, R, rfl, hcore, hmin, hroot, hval, hlvl, hno8, hm, hQ⟩

theorem fullMinLitDfsSpec_elim {h root_lit minimizing check_used m Q X}
    (hs : fullMinLitDfsSpec (h, root_lit, minimizing, check_used, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (keepSet : List Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullOtfsCoreInv c F0 s ∧ FullMinMarkInv s.core keepSet ∧
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
        FullMinMarkInv s'.core keepSet →
        (ok = true →
          (∀ keep', (∀ l ∈ keepSet, l = root_lit.toNat ∨ l ∈ keep') →
            FullMinMarkInv s'.core keep') ∧
          FullMinMarkInv (fullMinMarkCore s'.core (root_lit.toNat / 2) 2#8) keepSet) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := hs

/-- Canonical specification for `full_shrink_lower_m8`. -/
@[expose] def fullShrinkLowerSpec : Spec [i64, i32, i32] [.bool] := fun (h, ot, ov, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (keepSet : List Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullOtfsCoreInv c F0 s ∧ FullMinMarkInv s.core keepSet ∧
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
      FullMinMarkInv s'.core keepSet →
      (ok = true → (mrk'[ov.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem fullShrinkLowerSpec_monoX {xs : Tup Val [i64, i32, i32]} {m : Mem 64}
    {Q : Post [.bool]} {X X' : XPost}
    (h : fullShrinkLowerSpec xs m Q X) : fullShrinkLowerSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

theorem fullShrinkLowerSpec_of {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keepSet : List Nat} {ot ov : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hcore : FullOtfsCoreInv c F0 s) (hmin : FullMinMarkInv s.core keepSet)
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
      FullMinMarkInv s'.core keepSet →
      (ok = true → (mrk'[ov.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    fullShrinkLowerSpec (c.hdr, ot, ov, ()) m Q X :=
  ⟨c, F0, s, keepSet, R, rfl, hcore, hmin, hov, hot, hval, hlvl, hno8, hm, hQ⟩

theorem fullShrinkLowerSpec_elim {h ot ov m Q X}
    (hs : fullShrinkLowerSpec (h, ot, ov, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (keepSet : List Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullOtfsCoreInv c F0 s ∧ FullMinMarkInv s.core keepSet ∧
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
        FullMinMarkInv s'.core keepSet →
        (ok = true → (mrk'[ov.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := hs

/-- Canonical specification for `full_shrink_blk_bool_m8`. -/
@[expose] def fullShrinkBlkBoolSpec : Spec [i64, i64, i64, i32, i64] [.bool] :=
  fun (h, beg, end_b, blvl, max_tr, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (keepLen : Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullOtfsCoreInv c F0 s ∧
      FullMinMarkInv s.core
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
        FullMinMarkInv s'.core
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

theorem fullShrinkBlkBoolSpec_elim {h beg end_b blvl max_tr m Q X}
    (hs : fullShrinkBlkBoolSpec (h, beg, end_b, blvl, max_tr, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (keepLen : Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullOtfsCoreInv c F0 s ∧
      FullMinMarkInv s.core
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
        FullMinMarkInv s'.core
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

theorem fullShrinkBlkBoolSpec_monoX {xs : Tup Val [i64, i64, i64, i32, i64]} {m : Mem 64}
    {Q : Post [.bool]} {X X' : XPost}
    (h : fullShrinkBlkBoolSpec xs m Q X) : fullShrinkBlkBoolSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, _, ⟨⟩⟩; exact h

theorem fullShrinkBlkBoolSpec_of {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {beg end_b max_tr : BitVec 64} {blvl : BitVec 32} {keepLen : Nat} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hcore : FullOtfsCoreInv c F0 s)
    (hmin : FullMinMarkInv s.core
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
      let s' := m8ShrinkBlkBoolState s tmp' mrk' mclr' sstk' wsort' mcl' mcf' ticks'
      FullOtfsCoreInv c F0 s' →
      FullMinMarkInv s'.core
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
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    fullShrinkBlkBoolSpec (c.hdr, beg, end_b, blvl, max_tr, ()) m Q X :=
  ⟨c, F0, s, keepLen, R, rfl, hcore, hmin, hno8, hbeg1, hbeg_end, hend_kl, hkl_cv,
    hblvl_pos, hblvl_lt, hblk, hkeep, hm, hQ⟩

/-- Canonical specification for `full_min_shrink_m6`. -/
@[expose] def fullMinShrinkSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
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
    ∀ tmp' tl' mrk' mclr' sstk' wsort' ws1' mcl' mcf' conf' llits' mrem' ticks' resSz' m',
      let s' := fullMinShrinkState s tmp' tl' mrk' mclr' sstk' wsort' ws1' mcl' mcf' conf'
        llits' mrem' ticks' resSz'
      s'.LengthsOk c → FullOtfsWitnessInv c F0 F_cur s'.core → FullLitMarksClear c s' →
      1 ≤ tl' → tl' ≤ s.core.tmp_len → tmp'[0]? = s.core.tmp[0]? →
      ((tmp'.take tl').map fun x => x.toNat / 2).Nodup →
      (∀ j, 1 ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        0 < lv ∧ lv < s.core.cur_level) →
      (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat)) →
      (FullMem c s' ⋆ R) m' → Q () m'

theorem fullMinShrinkSpec_monoX {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post []} {X X' : XPost}
    (h : fullMinShrinkSpec xs m Q X) : fullMinShrinkSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem fullMinShrinkSpec_elim {h m Q X}
    (hs : fullMinShrinkSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullOtfsWitnessInv c F0 F_cur s.core ∧
      FullLitMarksClear c s ∧ 1 ≤ s.core.tmp_len ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
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
      ∀ tmp' tl' mrk' mclr' sstk' wsort' ws1' mcl' mcf' conf' llits' mrem' ticks' resSz' m',
        let s' := fullMinShrinkState s tmp' tl' mrk' mclr' sstk' wsort' ws1' mcl' mcf' conf'
          llits' mrem' ticks' resSz'
        s'.LengthsOk c → FullOtfsWitnessInv c F0 F_cur s'.core → FullLitMarksClear c s' →
        1 ≤ tl' → tl' ≤ s.core.tmp_len → tmp'[0]? = s.core.tmp[0]? →
        ((tmp'.take tl').map fun x => x.toNat / 2).Nodup →
        (∀ j, 1 ≤ j → j < tl' →
          let l := (tmp'[j]?.getD 0#32).toNat
          let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
          l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
          0 < lv ∧ lv < s.core.cur_level) →
        (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat)) →
        (FullMem c s' ⋆ R) m' → Q () m' := hs

theorem fullMinMarkSpec_xfree : fullMinMarkSpec.XFree := by xfree
theorem fullSortTmpSpec_xfree : fullSortTmpSpec.XFree := by xfree
theorem fullMinLitDfsSpec_xfree : fullMinLitDfsSpec.XFree := by xfree
theorem fullShrinkLowerSpec_xfree : fullShrinkLowerSpec.XFree := by xfree
theorem fullShrinkBlkBoolSpec_xfree : fullShrinkBlkBoolSpec.XFree := by xfree
theorem fullMinShrinkSpec_xfree : fullMinShrinkSpec.XFree := by xfree

/-- Canonical `SpecEntry` list matching `Src.Minimize.fns` order 1:1. -/
@[expose] def specs : List SpecEntry :=
  [ { name := "full_min_mark", as := [i64, i32, i8], rs := [],
      spec := fullMinMarkSpec, noExit := true }
  , { name := "full_sort_tmp", as := [i64], rs := [],
      spec := fullSortTmpSpec, noExit := true }
  , { name := "full_min_lit_dfs_m8", as := [i64, i32, .bool, .bool], rs := [.bool],
      spec := fullMinLitDfsSpec, noExit := true }
  , { name := "full_shrink_lower_m8", as := [i64, i32, i32], rs := [.bool],
      spec := fullShrinkLowerSpec, noExit := true }
  , { name := "full_shrink_blk_bool_m8", as := [i64, i64, i64, i32, i64], rs := [.bool],
      spec := fullShrinkBlkBoolSpec, noExit := true }
  , { name := "full_min_shrink_m6", as := [i64], rs := [],
      spec := fullMinShrinkSpec, noExit := true } ]

theorem specs_xfree : ∀ e ∈ specs, e.spec.XFree := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact fullMinMarkSpec_xfree
  · exact fullSortTmpSpec_xfree
  · exact fullMinLitDfsSpec_xfree
  · exact fullShrinkLowerSpec_xfree
  · exact fullShrinkBlkBoolSpec_xfree
  · exact fullMinShrinkSpec_xfree

theorem specs_sigs : specs.map SpecEntry.sig = Src.Minimize.fns.map Fn.sig := rfl

end

end LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
