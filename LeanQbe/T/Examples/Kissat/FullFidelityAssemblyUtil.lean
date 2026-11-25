/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.KissatCertCommon
public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
public import LeanQbe.T.Examples.Kissat.FullM6Orch
public import LeanQbe.T.Examples.Kissat.FullM6SatNv
public import LeanQbe.T.Examples.Kissat.PatchModule
import Std.Sat.CNF.Basic
import LeanQbe.T.InlineLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Shared Gate-1 `KissatFidelity` Assembly & UNSAT Lifting Utilities (`FullFidelityAssemblyUtil`)

Generic arch-independent UNSAT soundness, host-framed lift, concrete `Mem 64` non-vacuity,
`KissatUnsatPkg` packaging, and `PatchBundle` helper theorems parameterized over any closed
`(Γ : Env) (M : Module)` implementing `"kissat_solve_bytes" : m7FidSolveBytesSpec`.

Once any `PatchBundle` layer (`Sweep`, `BcpHotPush`, `Bve`, `Cong`, `VivK6`, `Bva`) proves
`ModuleOk`, its top-level `solve_bytes_sound`, `solve_bytes_host_sound`, `unsat_nv`, and
`KissatUnsatPkg` follow in under `40` lines with zero duplicated proofs.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.KissatCertCommon
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.PatchModule
open Kraken.Bedrock2.Test

/-! ## 1. Generic Top-Level UNSAT Soundness, Host-Framed Lift & Concrete `Mem 64` NV -/

/-- Generic byte-level UNSAT soundness for any `kissat_solve_bytes` function `body` in `M.fns`
under `ModuleOk Γ M` and `m7FidSolveBytesSpec`. -/
theorem fid_solve_bytes_sound_of_fn {Γ : Env} {M : LeanQbe.T.Module}
    {body : Func [i64, i64, i64, i64, i64] [i64]}
    (hM : ModuleOk Γ M)
    (hMem : (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], body⟩ : Fn) ∈ M.fns)
    (hSb : ∀ a m Q X, m7FidSolveBytesSpec a m Q X →
      Γ "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp Γ body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hMem
  have hfn := (hM.fnsOk pre _ post hsplit).2.2
  refine hfn _ m _ (fun _ _ _ _ => False)
    (hSb _ m _ _ (m7FidSolveBytesSpec_intro hcfit hwfit hm ?_))
  intro r m' hdom h20 _ hm'
  exact ⟨hdom, h20, hm'⟩

/-- Generic byte-level UNSAT soundness specialized to `FullM6Orch.m6oSolveBytesFn`. -/
theorem fid_solve_bytes_sound_of {Γ : Env} {M : LeanQbe.T.Module}
    (hM : ModuleOk Γ M) (hMem : m6oSolveBytesFn ∈ M.fns)
    (hSb : ∀ a m Q X, m7FidSolveBytesSpec a m Q X →
      Γ "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp Γ FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fid_solve_bytes_sound_of_fn hM hMem hSb hcfit hwfit hm

/-- Host-framed machine-memory UNSAT lift (`(Eq m' ⋆ F_host) st_dmem`). -/
theorem fid_solve_bytes_host_sound
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hpost :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hhost : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem :=
  ⟨hpost.1, hpost.2.1, sep_mono (fun _ hm0 => by subst hm0; exact hpost.2.2) hhost⟩

/-- Generic concrete `8,192 B` `Mem 64` UNSAT non-vacuity (`r = 20#64`, `XPost := False`) for any
`kissat_solve_bytes` function `body` in `M.fns`. -/
theorem fid_unsat_nv_of_fn {Γ : Env} {M : LeanQbe.T.Module}
    {body : Func [i64, i64, i64, i64, i64] [i64]}
    (hM : ModuleOk Γ M)
    (hMem : (⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], body⟩ : Fn) ∈ M.fns)
    (hSb : ∀ a m Q X, m7FidSolveBytesSpec a m Q X →
      Γ "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    Func.wp Γ body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hMem
  have hfn := (hM.fnsOk pre _ post hsplit).2.2
  have hm0 :
      (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen ⋆ emp)
        nvM6UnsatInitMem := by
    rw [Std.ExtHashMap.sep_emp]
    exact nvM6UnsatInitMem_sep
  refine hfn _ nvM6UnsatInitMem _ (fun _ _ _ _ => False)
    (hSb _ nvM6UnsatInitMem _ _ (m7FidSolveBytesSpec_intro (by decide) (by decide) hm0 ?_))
  intro r m' _ _ htr hm'
  have hr20 := htr 1 2 9 (by decide) (by decide) (by decide) nvM6_unsat_bound (by decide)
    nvM6Unsat_header nvM6Unsat_unitTrace
  rw [Std.ExtHashMap.sep_emp] at hm'
  exact ⟨hr20, nvM6UnsatCnf_unsat, hm'⟩

/-- Generic concrete `8,192 B` `Mem 64` UNSAT non-vacuity specialized to `m6oSolveBytesFn`. -/
theorem fid_unsat_nv_of {Γ : Env} {M : LeanQbe.T.Module}
    (hM : ModuleOk Γ M) (hMem : m6oSolveBytesFn ∈ M.fns)
    (hSb : ∀ a m Q X, m7FidSolveBytesSpec a m Q X →
      Γ "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    Func.wp Γ FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fid_unsat_nv_of_fn hM hMem hSb

/-! ## 2. `KissatUnsatPkg` & `PatchBundle` Composition Helpers -/

/-- Build a canonical arch-free `KissatUnsatPkg` from `ModuleOk`, `m6oSolveBytesFn ∈ mod.fns`,
`Env` exit-freedom, and `m7FidSolveBytesSpec → env "kissat_solve_bytes" ...`. -/
def mkFidUnsatPkg
    (mod : LeanQbe.T.Module)
    (inlPolicy : InlinePolicy)
    (entry_mem : m6oSolveBytesFn ∈ mod.fns)
    (env : Env)
    (moduleOk : ModuleOk env mod)
    (noExit : ∀ f as bs args m Q X X',
      env f as bs args m Q X → env f as bs args m Q X')
    (solve_intro_m7 : ∀ a m Q X, m7FidSolveBytesSpec a m Q X →
      env "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    KissatUnsatPkg where
  mod := mod
  inlPolicy := inlPolicy
  entryFn := "kissat_solve_bytes"
  entryFn_fn := m6oSolveBytesFn
  entryFn_sig := ⟨rfl, rfl, rfl⟩
  entry_mem := entry_mem
  env := env
  moduleOk := moduleOk
  noExit := fun f _ args m Q X X' h => noExit f.name f.as f.rs args m Q X X' h
  solve_intro := fun hcfit hwfit hm hreq =>
    solve_intro_m7 _ _ _ _ (m7FidSolveBytesSpec_intro hcfit hwfit hm hreq)

/-- `PatchBundle.patchedMod` preserves `exits`. -/
theorem patchBundle_exits_eq (b : PatchBundle) : b.patchedMod.exits = b.baseMod.exits :=
  rfl

/-- `m6oSolveBytesFn` remains in `b.patchedMod.fns` when `b.repls` omits `"kissat_solve_bytes"`. -/
theorem patchBundle_solveBytes_mem (b : PatchBundle)
    (hMem : m6oSolveBytesFn ∈ b.baseMod.fns)
    (hne : ∀ r ∈ b.repls, r.name ≠ "kissat_solve_bytes") :
    m6oSolveBytesFn ∈ b.patchedMod.fns := by
  change m6oSolveBytesFn ∈ patchFns b.repls b.befores b.baseMod.fns
  simp only [patchFns, List.mem_flatMap, List.mem_append, List.mem_singleton]
  refine ⟨m6oSolveBytesFn, hMem, Or.inr ?_⟩
  cases hf : b.repls.find? (·.name == m6oSolveBytesFn.name) with
  | none => rfl
  | some r =>
    have hnm := beq_iff_eq.mp
      (List.find?_some (p := fun y : Fn => y.name == m6oSolveBytesFn.name) hf)
    exact False.elim (hne r (List.mem_of_find?_eq_some hf) hnm)

/-- Lift `Env.ofTable_noExit` across `patchEnv b` when `b.frontTable` and `b.baseTable` are
exit-free. -/
theorem patchEnv_noExit_of (b : PatchBundle)
    (hfront : b.frontTable.all SpecEntry.noExit = true)
    (hbase : b.baseTable.all SpecEntry.noExit = true) :
    ∀ f as bs xs m Q X X', patchEnv b f as bs xs m Q X → patchEnv b f as bs xs m Q X' := by
  refine Env.ofTable_noExit (fun e he => ?_)
  rw [List.mem_append] at he
  rcases he with h1 | h2
  · exact List.all_eq_true.mp hfront e h1
  · exact List.all_eq_true.mp hbase e h2

/-- Lift `"kissat_solve_bytes"` lookup across `patchEnv b` when `b.frontTable` omits it. -/
theorem patchEnv_solveBytes_of (b : PatchBundle)
    (hf : b.frontTable.find? (·.name == "kissat_solve_bytes") = none)
    (hBase : ∀ a m Q X, m7FidSolveBytesSpec a m Q X →
      Env.ofTable b.baseTable "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m7FidSolveBytesSpec a m Q X →
      patchEnv b "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X := by
  intro a m Q X hs
  rw [patchEnv_base_eq b hf]
  exact hBase a m Q X hs

/-- Lift `Env.ofTable pfx` into `Env.ofTable (pfx ++ tbl)`. -/
theorem env_ofTable_append_left {pfx tbl : List SpecEntry} {f : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable pfx f as bs xs m Q X) :
    Env.ofTable (pfx ++ tbl) f as bs xs m Q X := by
  induction pfx with
  | nil => exact False.elim h
  | cons hd tl ih =>
    rw [List.cons_append]
    rcases h with ⟨hsig, hcast⟩ | ⟨hne, htl⟩
    · exact Or.inl ⟨hsig, hcast⟩
    · exact Or.inr ⟨hne, ih htl⟩

/-- Look up a row `e ∈ b.frontTable` in `patchEnv b` when `b.frontTable` has distinct names. -/
theorem patchEnv_of_front_mem (b : PatchBundle)
    (hnd : (b.frontTable.map SpecEntry.name).Nodup)
    {e : SpecEntry} (he : e ∈ b.frontTable)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost}
    (hs : e.eff xs m Q X) :
    patchEnv b e.name e.as e.rs xs m Q X :=
  env_ofTable_append_left (Env.ofTable_of_mem he hnd hs)

/-- Uniqueness of elements with matching key in a `Nodup`-projected list. -/
theorem nodup_name_eq {α : Type _} (key : α → Sym) {xs : List α}
    (hnd : (xs.map key).Nodup) {x y : α} (hx : x ∈ xs) (hy : y ∈ xs)
    (hnm : key x = key y) : x = y := by
  induction xs with
  | nil => nomatch hx
  | cons a t ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · exact absurd (hnm ▸ List.mem_map.mpr ⟨y, hy, rfl⟩) hnd.1
    · exact absurd (hnm.symm ▸ List.mem_map.mpr ⟨x, hx, rfl⟩) hnd.1
    · exact ih hnd.2 hx hy

/-- Agree helper for `patchBundle_moduleOk_sameSpecs` when `b.frontTable` has distinct names and
every entry in `b.frontTable` preserves its `baseTable` specification (`sameSpecs`). -/
theorem patchEnv_agree_of_sameSpecs (b : PatchBundle)
    (hnd : (b.frontTable.map SpecEntry.name).Nodup)
    (hSame : ∀ e ∈ b.frontTable, ∀ xs m P E,
      Env.ofTable b.baseTable e.name e.as e.rs xs m P E → e.eff xs m P E) :
    ∀ s ∈ b.baseMod.sigs, ∀ xs m P E,
      Env.ofTable b.baseTable s.1 s.2.1 s.2.2 xs m P E →
        patchEnv b s.1 s.2.1 s.2.2 xs m P E := by
  intro s _ xs m P E hBase
  cases hf : b.frontTable.find? (·.name == s.1) with
  | none =>
    rw [patchEnv_base_eq b hf]
    exact hBase
  | some e =>
    have he := List.mem_of_find?_eq_some hf
    have hnm : e.name = s.1 :=
      beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == s.1) hf)
    by_cases hsig : e.as = s.2.1 ∧ e.rs = s.2.2
    · obtain ⟨has, hrs⟩ := hsig
      rcases s with ⟨nm, as, rs⟩
      dsimp only at hnm has hrs
      subst hnm; subst has; subst hrs
      exact patchEnv_of_front_mem b hnd he (hSame e he xs m P E hBase)
    · have hne : ∀ e' ∈ b.frontTable, ¬ (e'.name = s.1 ∧ e'.as = s.2.1 ∧ e'.rs = s.2.2) := by
        intro e' he' ⟨hnm', has', hrs'⟩
        have heq : e' = e :=
          nodup_name_eq SpecEntry.name hnd he' he (hnm'.trans hnm.symm)
        subst heq
        exact hsig ⟨has', hrs'⟩
      have hLift : ∀ (pfx : List SpecEntry),
          (∀ e' ∈ pfx, ¬ (e'.name = s.1 ∧ e'.as = s.2.1 ∧ e'.rs = s.2.2)) →
          Env.ofTable (pfx ++ b.baseTable) s.1 s.2.1 s.2.2 xs m P E := by
        intro pfx hpfx
        induction pfx with
        | nil => exact hBase
        | cons x xs ih =>
          rw [List.cons_append]
          refine Or.inr ⟨hpfx x List.mem_cons_self, ?_⟩
          exact ih fun y hy => hpfx y (List.mem_cons_of_mem _ hy)
      exact hLift b.frontTable hne

/-- Eliminates `Env.ofTable tbl e.name as bs xs m Q X` for a known row `e ∈ tbl` when `tbl` has
distinct names. -/
theorem env_ofTable_sig_elim {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup) {e : SpecEntry} (he : e ∈ tbl)
    {as bs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable tbl e.name as bs xs m Q X) :
    ∃ (has : e.as = as) (hrs : e.rs = bs), e.cast has hrs xs m Q X := by
  induction tbl with
  | nil => nomatch he
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp he with rfl | htl
    · dsimp only [Env.ofTable] at h
      rcases h with ⟨⟨_, has, hrs⟩, hcast⟩ | ⟨_, htl'⟩
      · exact ⟨has, hrs, hcast⟩
      · exfalso
        have hmem_elim : ∀ {p : List SpecEntry},
            (∀ e' ∈ p, e'.name ≠ e.name) → Env.ofTable p e.name as bs xs m Q X → False := by
          intro p hp h0
          induction p with
          | nil => exact h0
          | cons x xs ihx =>
            rcases h0 with ⟨⟨hx, _⟩, _⟩ | ⟨_, htlx⟩
            · exact hp x List.mem_cons_self hx
            · exact ihx (fun y hy => hp y (List.mem_cons_of_mem _ hy)) htlx
        exact hmem_elim (fun y hy heq' => hnd.1 ⟨y, hy, heq'⟩) htl'
    · have hne : hd.name ≠ e.name := fun h' => hnd.1 ⟨e, htl, h'.symm⟩
      rw [Env.ofTable_cons_ne hne] at h
      exact ih hnd.2 htl h

/-- `r ∈ patchFns repls befores fs` when `r ∈ repls`, `(repls.map Fn.name).Nodup`, and some
`g ∈ fs` shares `r.name`. -/
theorem mem_patchFns_of_repl {repls fs : List Fn} {befores : List (Sym × List Fn)} {r g : Fn}
    (hrnd : (repls.map Fn.name).Nodup) (hr : r ∈ repls) (hg : g ∈ fs) (hnm : r.name = g.name) :
    r ∈ patchFns repls befores fs := by
  have hf : repls.find? (·.name == g.name) = some r := by
    have hs : (repls.find? (·.name == g.name)).isSome = true :=
      List.find?_isSome.mpr ⟨r, hr, beq_iff_eq.mpr hnm⟩
    cases h : repls.find? (·.name == g.name) with
    | none => simp [h] at hs
    | some r' =>
      have hn' := beq_iff_eq.mp (List.find?_some (p := fun y : Fn => y.name == g.name) h)
      rw [nodup_name_eq Fn.name hrnd (List.mem_of_find?_eq_some h) hr (hn'.trans hnm.symm)]
  simp only [patchFns, List.mem_flatMap, List.mem_append, List.mem_singleton]
  exact ⟨g, hg, Or.inr (by simp [hf])⟩

/-- Reconstructs `M.checkAcyclic = true` in `O(1)` from `ModuleOk Γ M`. -/
theorem moduleCheckAcyclic_of_moduleOk {Γ : Env} {M : LeanQbe.T.Module}
    (hM : ModuleOk Γ M) : M.checkAcyclic = true := by
  simp only [LeanQbe.T.Module.checkAcyclic, Bool.and_eq_true]
  refine ⟨listNodup_iff.mpr hM.nodup,
    checkFnsCallsOk_of_forall _ _ [] _ fun pre fn post hsp => ?_⟩
  simpa using (hM.fnsOk pre fn post hsp).2.1

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyUtil

end
