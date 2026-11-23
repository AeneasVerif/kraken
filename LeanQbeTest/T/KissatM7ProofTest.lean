/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7Proof
public import LeanQbe.T.Examples.Kissat.FullM7Splice
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM7Proof
meta import LeanQbe.T.Examples.Kissat.FullM7Splice
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal
import Kraken.Mem
import Kraken.Separation

/-!
# Verification, Soundness, UNSAT Non-Vacuity & Axiom Audit for Unified Kissat `M7` (`410/410`)

1. Executable `#guard` sanity checks on `m7Fns` (`410` fns), `m7Module.checkAcyclic`, empty
   exits/externs, concrete `M6Hdr` `3,456 B` layout, `PrintCpp`, `PrintQbe`, and 4-ISA
   `Fn.legal` / `isLegal` across `.aarch64`, `.scalar64`, `.x64AVX512`, and `.x64AVX2`.
2. Root-namespace short aliases for single-line `#print axioms` audit (`< 115` chars) covering
   `Func.Wf`, acyclicity, `410`-row table metadata (`m7SpecTable_sigs`, `m7SpecTable_length`,
   `m7SpecTable_nodup`, `m7SpecTable_noExit`), `mkM7Env_moduleOk`, `m7_solve_bytes_unsat_wp`,
   `m7_solve_bytes_sound`, `m7_solve_bytes_m6_sound`, `m7_solve_bytes_host_sound`,
   `m7_unsat_nv`, and `m7_m6_unsat_nv` (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM7ProofTest

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Splice
open LeanQbe.T.Examples.LratBytes

#guard m7Fns.length == 410
#guard m7Module.checkAcyclic == true
#guard m7Module.exits.isEmpty && m7Module.externs.isEmpty
#guard m7Module.sigs.length == 410
#guard m7OrchPfxRows.length == 21
#guard (patchFns m7BvaGuRepls [] m7Fns).map Fn.sig == m7BvaGuFns.map Fn.sig
#guard m7BvaGuModule.checkAcyclic == true
#guard fullM6ExtBytes == 2304 && fullM6HdrTotalBytes == 3456
#guard fullM6ExtBytes + fullFixedBytes 1 + 2 * 40 + 136 + 8 <= nvM6WorkLen
#guard (ppTModule m7Module).isOk
#guard (PrintQbe.module m7Module).isOk
#guard (ppModule (m7Fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7Fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7Fns.map (Fn.legal .x64AVX512))).isOk
#guard (ppModule (m7Fns.map (Fn.legal .x64AVX2))).isOk
#guard m7Fns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard m7Fns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard m7Fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard m7Fns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

end LeanQbeTest.T.KissatM7ProofTest

section AxiomAudit

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Splice

theorem m7_wf_ok : ∀ f ∈ m7Fns, f.Wf := m7Fns_wf

theorem m7_acyclic_ok : m7Module.checkAcyclic = true := m7_acyclic

theorem m7_pfx_impl_ok (tBve : List SpecEntry)
    (s : Spec [i64, i64, i64, i64, i64] [i64])
    (h1 : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (h2 : M7BveAllTblSpecs tBve) :
    TableImpl (mkM7Env tBve s) m7OrchPfxFns m7OrchPfxRows :=
  m7OrchPfx_tableImpl tBve s h1 h2

theorem m7_tbl_sigs_ok (tBve : List SpecEntry)
    (s : Spec [i64, i64, i64, i64, i64] [i64])
    (h2 : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    (m7SpecTable tBve s).map (fun e => (e.name, e.as, e.rs)) = m7Fns.map Fn.sig :=
  m7SpecTable_sigs tBve s h2

theorem m7_tbl_len_ok (tBve : List SpecEntry)
    (s : Spec [i64, i64, i64, i64, i64] [i64])
    (h2 : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    (m7SpecTable tBve s).length = 410 :=
  m7SpecTable_length tBve s h2

theorem m7_tbl_nodup_ok (tBve : List SpecEntry)
    (s : Spec [i64, i64, i64, i64, i64] [i64])
    (h2 : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    ((m7SpecTable tBve s).map SpecEntry.name).Nodup :=
  m7SpecTable_nodup tBve s h2

theorem m7_tbl_noExit_ok (tBve : List SpecEntry)
    (s : Spec [i64, i64, i64, i64, i64] [i64])
    (h2 : tBve.all SpecEntry.noExit = true) :
    (m7SpecTable tBve s).all SpecEntry.noExit = true :=
  m7SpecTable_noExit tBve s h2

theorem m7_mod_ok (tBve : List SpecEntry)
    (s : Spec [i64, i64, i64, i64, i64] [i64])
    (hW : ∀ a m Q X, s a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hX : ∀ a m Q X X', s a m Q X → s a m Q X')
    (hBS : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBN : tBve.all SpecEntry.noExit = true)
    (hBP : M7BveAllTblSpecs tBve)
    (hBO : TableImpl (mkM7Env tBve s) m7BveAllFns tBve) :
    ModuleOk (mkM7Env tBve s) m7Module :=
  mkM7Env_moduleOk tBve s hW hX hBS hBN hBP hBO

theorem m7_unsat_wp_ok (tBve : List SpecEntry)
    (hBS : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBN : tBve.all SpecEntry.noExit = true)
    (hBP : M7BveAllTblSpecs tBve)
    (hBO : TableImpl (mkM7Env tBve fullM6SolveBytesSpec) m7BveAllFns tBve)
    {a : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : fullM6SolveBytesUnsatSpec a m Q X) :
    Func.wp (mkM7Env tBve fullM6SolveBytesSpec) FullM6Orch.kissat_solve_bytes_body
      a m Q X :=
  m7_solve_bytes_unsat_wp tBve hBS hBN hBP hBO hs

theorem m7_sound_ok (tBve : List SpecEntry)
    (hBS : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBN : tBve.all SpecEntry.noExit = true)
    (hBP : M7BveAllTblSpecs tBve)
    (hBO : TableImpl (mkM7Env tBve fullM6SolveBytesSpec) m7BveAllFns tBve)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp (mkM7Env tBve fullM6SolveBytesSpec) FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
            ∀ (F : Mem 64 → Prop) (M' : Mem 64),
              (Eq m' ⋆ F) M' → cnf.Sat (readModelFromWorkM6 M' work_ptr)) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m7_solve_bytes_sound tBve hBS hBN hBP hBO hcfit hwfit hm

theorem m7_m6_sound_ok (tBve : List SpecEntry)
    (hBS : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBN : tBve.all SpecEntry.noExit = true)
    (hBve : M7BveAllTblSpecs tBve)
    (hBO : TableImpl (mkM7Env tBve fullM6SolveBytesSpec) m7BveAllFns tBve)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp (mkM7Env tBve fullM6SolveBytesSpec) kissat_solve_bytes_m6_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
            ∀ (F : Mem 64 → Prop) (M' : Mem 64),
              (Eq m' ⋆ F) M' → cnf.Sat (readModelFromWorkM6 M' work_ptr)) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m7_solve_bytes_m6_sound tBve hBS hBN hBve hBO hcfit hwfit hm

theorem m7_host_ok
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hq :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        ∀ (F : Mem 64 → Prop) (M : Mem 64),
          (Eq m' ⋆ F) M → cnf.Sat (readModelFromWorkM6 M work_ptr)) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hdmem : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
      ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
      cnf.Sat (readModelFromWorkM6 st_dmem work_ptr)) ∧
    ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) ⋆ F_host) st_dmem :=
  m7_solve_bytes_host_sound hq hdmem

theorem m7_nv_unsat_ok (tBve : List SpecEntry)
    (hBS : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBN : tBve.all SpecEntry.noExit = true)
    (hBP : M7BveAllTblSpecs tBve)
    (hBO : TableImpl (mkM7Env tBve fullM6SolveBytesCoreModelSpec) m7BveAllFns tBve) :
    Func.wp (mkM7Env tBve fullM6SolveBytesCoreModelSpec) FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m7_unsat_nv tBve hBS hBN hBP hBO

theorem m7_m6_nv_unsat_ok (tBve : List SpecEntry)
    (hBS : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBN : tBve.all SpecEntry.noExit = true)
    (hBP : M7BveAllTblSpecs tBve)
    (hBO : TableImpl (mkM7Env tBve fullM6SolveBytesCoreModelSpec) m7BveAllFns tBve) :
    Func.wp (mkM7Env tBve fullM6SolveBytesCoreModelSpec) kissat_solve_bytes_m6_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m7_m6_unsat_nv tBve hBS hBN hBP hBO

theorem m7_bva_gu_mod_ok (tBve : List SpecEntry)
    (s : Spec [i64, i64, i64, i64, i64] [i64])
    (hW : ∀ a m Q X, s a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hX : ∀ a m Q X X', s a m Q X → s a m Q X')
    (hBS : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBN : tBve.all SpecEntry.noExit = true)
    (hBP : M7BveAllTblSpecs tBve)
    (hBO : TableImpl (mkM7Env tBve s) m7BveAllFns tBve) :
    ModuleOk (mkM7Env tBve s) m7BvaGuModule :=
  m7BvaGu_moduleOk tBve s hW hX hBS hBN hBP hBO

theorem m7_bva_gu_sound_ok (tBve : List SpecEntry)
    (hBS : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBN : tBve.all SpecEntry.noExit = true)
    (hBP : M7BveAllTblSpecs tBve)
    (hBO : TableImpl (mkM7Env tBve fullM6SolveBytesSpec) m7BveAllFns tBve)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp (mkM7Env tBve fullM6SolveBytesSpec) FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
            ∀ (F : Mem 64 → Prop) (M' : Mem 64),
              (Eq m' ⋆ F) M' → cnf.Sat (readModelFromWorkM6 M' work_ptr)) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  m7BvaGu_solve_bytes_sound tBve hBS hBN hBP hBO hcfit hwfit hm

theorem m7_bva_gu_nv_unsat_ok (tBve : List SpecEntry)
    (hBS : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBN : tBve.all SpecEntry.noExit = true)
    (hBP : M7BveAllTblSpecs tBve)
    (hBO : TableImpl (mkM7Env tBve fullM6SolveBytesCoreModelSpec) m7BveAllFns tBve) :
    Func.wp (mkM7Env tBve fullM6SolveBytesCoreModelSpec) FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m7BvaGu_unsat_nv tBve hBS hBN hBP hBO

theorem m7_patch_acyc_ok {M : LeanQbe.T.Module} {repls : List Fn}
    {befores : List (Sym × List Fn)}
    (hnd : ((patchFns repls befores M.fns).map Fn.name ++ M.externs.map Extern.name).Nodup)
    (hM : M.checkAcyclic = true)
    (hsig : ∀ r ∈ repls, ∀ f ∈ M.fns, r.name = f.name → r.sig = f.sig)
    (hins : ∀ pre f post, M.fns = pre ++ f :: post →
      LeanQbe.T.Module.checkFnsCallsOk M.exits (M.externs.map Extern.sig)
        (pre.map Fn.sig) (patchInsAt befores f) = true)
    (hrepl : ∀ pre f post r, M.fns = pre ++ f :: post → r ∈ repls → r.name = f.name →
      r.checkCallsOk
        (pre.map Fn.sig ++ (patchInsAt befores f).map Fn.sig ++ M.externs.map Extern.sig)
        M.exits = true) :
    ({ M with fns := patchFns repls befores M.fns } : LeanQbe.T.Module).checkAcyclic = true :=
  patchModule_checkAcyclic hnd hM hsig hins hrepl

theorem m7_patch_mod_ok {Γ Γ' : Env} {M : LeanQbe.T.Module}
    (hM : ModuleOk Γ M) {repls : List Fn} {befores : List (Sym × List Fn)}
    (hchk : ({ M with fns := patchFns repls befores M.fns } :
      LeanQbe.T.Module).checkAcyclic = true)
    (hrWf : ∀ r ∈ repls, r.Wf)
    (hiWf : ∀ p ∈ befores, ∀ h ∈ p.2, h.Wf)
    (hCallee : ∀ f as bs xs m Q X, Γ f as bs xs m Q X → Γ' f as bs xs m Q X)
    (hFnWp : ∀ g ∈ M.fns, repls.find? (fun x => x.name == g.name) = none →
      (∀ xs m Q X, Γ' g.name g.as g.rs xs m Q X → Func.wp Γ' g.body xs m Q X) ∨
      (∀ xs m Q X, Γ' g.name g.as g.rs xs m Q X → Γ g.name g.as g.rs xs m Q X))
    (hrWp : ∀ r ∈ repls, ∀ xs m Q X,
      Γ' r.name r.as r.rs xs m Q X → Func.wp Γ' r.body xs m Q X)
    (hiWp : ∀ p ∈ befores, ∀ h ∈ p.2, ∀ xs m Q X,
      Γ' h.name h.as h.rs xs m Q X → Func.wp Γ' h.body xs m Q X) :
    ModuleOk Γ' { M with fns := patchFns repls befores M.fns } :=
  patchModule_moduleOk hM hchk hrWf hiWf hCallee hFnWp hrWp hiWp

theorem m7_patch_rows_sigs {replsR : List SpecEntry} {beforesR : List (Sym × List SpecEntry)}
    {replsF : List Fn} {beforesF : List (Sym × List Fn)}
    (tbl : List SpecEntry) (fs : List Fn)
    (hsig : tbl.map (fun e => (e.name, e.as, e.rs)) = fs.map Fn.sig)
    (hsr : ∀ r ∈ replsR, ∀ e ∈ tbl, r.name = e.name →
      (r.name, r.as, r.rs) = (e.name, e.as, e.rs))
    (hsf : ∀ r ∈ replsF, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig)
    (hins : ∀ e ∈ tbl, ∀ f ∈ fs, e.name = f.name →
      (patchRowInsAt beforesR e).map (fun r => (r.name, r.as, r.rs)) =
        (patchInsAt beforesF f).map Fn.sig) :
    (patchRows replsR beforesR tbl).map (fun e => (e.name, e.as, e.rs)) =
      (patchFns replsF beforesF fs).map Fn.sig :=
  patchRows_sigs tbl fs hsig hsr hsf hins

theorem m7_tBve_mem_ok {tBve : List SpecEntry}
    {solveSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    ∀ e ∈ tBve, e ∈ m7SpecTable tBve solveSpec :=
  m7SpecTable_tBve_mem hBveSigs

#print axioms m7_wf_ok
#print axioms m7_acyclic_ok
#print axioms m7_pfx_impl_ok
#print axioms m7_tbl_sigs_ok
#print axioms m7_tbl_len_ok
#print axioms m7_tbl_nodup_ok
#print axioms m7_tbl_noExit_ok
#print axioms m7_mod_ok
#print axioms m7_unsat_wp_ok
#print axioms m7_sound_ok
#print axioms m7_m6_sound_ok
#print axioms m7_host_ok
#print axioms m7_nv_unsat_ok
#print axioms m7_m6_nv_unsat_ok
#print axioms m7_bva_gu_mod_ok
#print axioms m7_bva_gu_sound_ok
#print axioms m7_bva_gu_nv_unsat_ok
#print axioms m7_patch_acyc_ok
#print axioms m7_patch_mod_ok
#print axioms m7_patch_rows_sigs
#print axioms m7_tBve_mem_ok

end AxiomAudit
