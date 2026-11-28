/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Examples.Kissat.Src.Clause
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Clause` (`Proof.Clause.Spec`)

Canonical per-function specifications and capability extractors for all `4` functions in
`Src.Clause.fns`:
1. `full_add_clause` (`fullAddClauseSpec`, extending `Proof.Spec.fullAddClauseSpec` with
   `flags'` mutation on `len = 2` matching step-13 clause allocation callers).
2. `full_add_bin_m6` (`Proof.Spec.fullAddBinSpec`).
3. `full_add_bin` (`Proof.Spec.fullAddBinSpec`).
4. `full_add_unit` (`Proof.Spec.fullAddUnitSpec`).

`deps = Arena.Spec.specs ++ Backtrack.Spec.specs ++ Watch.Spec.specs`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Clause.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

/-- Step-13 canonical contract for `full_add_clause`: handles `< 2` no-op, `= 2` binary
watch + `flags` + `num_binary` update, and `≥ 3` large arena clause + watch push/rollback. -/
@[expose] def fullAddClauseSpec : Spec [i64, i32, i32, .bool] [i64] :=
  fun (h, len, _glue, _red, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      s.core.dense_mode = 0#64 ∧ len.toNat ≤ c.max_vars ∧
      (2 ≤ len.toNat →
        (∀ l ∈ (s.core.tmp.take len.toNat).map BitVec.toNat, l < 2 * s.core.cur_vars) ∧
        ((s.core.tmp.take len.toNat).map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.core.tmp.take len.toNat).map BitVec.toNat))) ∧
      (FullMem c s ⋆ R) m ∧
      if len.toNat < 2 then Q (0xFFFFFFFF#64, ()) m
      else if len.toNat = 2 then
        ∀ r flags' wvec' wstk' wlen' wusable' nb' wsort' m',
          let s' : FullState :=
            { s with
              core := { s.core with
                flags := flags', wvec := wvec', wstk := wstk',
                wlen := wlen', wusable := wusable', num_binary := nb' }
              scratch := { s.scratch with wsort := wsort' } }
          (r = 0xFFFFFFFF#64 ∨ r = 0xFFFFFFFE#64) →
          s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
          (FullMem c s' ⋆ R) m' → Q (r, ()) m'
      else
        ∀ r arena' alen' wvec' wstk' wlen' wusable' fred' ni' nr' wsort' m',
          let s' : FullState :=
            { s with
              core := { s.core with
                arena := arena', arena_len := alen', wvec := wvec',
                wstk := wstk', wlen := wlen', wusable := wusable',
                first_reducible := fred', num_irred := ni', num_redundant := nr' }
              scratch := { s.scratch with wsort := wsort' } }
          (r = 0xFFFFFFFF#64 ∨ r = BitVec.ofNat 64 s.core.arena_len) →
          s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
          (∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s') →
          (FullArenaVarsNodup s → FullArenaVarsNodup s') →
          (r = BitVec.ofNat 64 s.core.arena_len → alen' = s.core.arena_len + 3 + len.toNat ∧
            s.core.arena_len ∈ fullArenaClauseRefs s' ∧
            fullArenaClauseGarb s' s.core.arena_len = false ∧
            fullArenaClauseLits s' s.core.arena_len =
              (s.core.tmp.take len.toNat).map BitVec.toNat) →
          (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Upstream canonical specification dependencies for `Src.Clause`. -/
@[expose] def deps : List SpecEntry :=
  Arena.Spec.specs ++ Backtrack.Spec.specs ++ Watch.Spec.specs

/-- Canonical specification table for all `4` functions in `Src.Clause.fns`. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], fullAddClauseSpec, true⟩
  , ⟨"full_add_bin_m6", [i64, i32, i32], [i64], Proof.Spec.fullAddBinSpec, true⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64], Proof.Spec.fullAddBinSpec, true⟩
  , ⟨"full_add_unit", [i64, i32], [.bool], Proof.Spec.fullAddUnitSpec, true⟩
  ]

theorem specs_sigs :
    specs.map SpecEntry.sig = LeanQbe.T.Examples.Kissat.Src.Clause.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem fullAddClauseSpec_xfree : fullAddClauseSpec.XFree := by xfree

theorem fullAddBinSpec_xfree : Proof.Spec.fullAddBinSpec.XFree := by xfree

theorem fullAddUnitSpec_xfree : Proof.Spec.fullAddUnitSpec.XFree := by xfree

theorem specs_xfree : ∀ e ∈ specs, e.spec.XFree := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact fullAddClauseSpec_xfree
  · exact fullAddBinSpec_xfree
  · exact fullAddBinSpec_xfree
  · exact fullAddUnitSpec_xfree

theorem has_full_add_clause {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_add_clause" fullAddClauseSpec :=
  h.has (e := ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], fullAddClauseSpec, true⟩)
    (by simp [specs]) fullAddClauseSpec_xfree

theorem has_full_add_bin_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_add_bin_m6" Proof.Spec.fullAddBinSpec :=
  h.has (e := ⟨"full_add_bin_m6", [i64, i32, i32], [i64], Proof.Spec.fullAddBinSpec, true⟩)
    (by simp [specs]) fullAddBinSpec_xfree

theorem has_full_add_bin {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_add_bin" Proof.Spec.fullAddBinSpec :=
  h.has (e := ⟨"full_add_bin", [i64, i32, i32], [i64], Proof.Spec.fullAddBinSpec, true⟩)
    (by simp [specs]) fullAddBinSpec_xfree

theorem has_full_add_unit {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_add_unit" Proof.Spec.fullAddUnitSpec :=
  h.has (e := ⟨"full_add_unit", [i64, i32], [.bool], Proof.Spec.fullAddUnitSpec, true⟩)
    (by simp [specs]) fullAddUnitSpec_xfree

end LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
