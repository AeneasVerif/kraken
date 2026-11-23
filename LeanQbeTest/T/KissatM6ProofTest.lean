/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM6Proof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM6Proof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal
import Kraken.Mem
import Kraken.Separation

/-!
# Verification, Soundness, UNSAT Non-Vacuity & Axiom Audit for Unified Kissat M6 (`382/382`)

1. Executable `#guard` sanity checks on `m6Fns` (`382` fns), `m6Module.checkAcyclic`, empty
   exits/externs, concrete `M6Hdr` `3,456 B` layout, `PrintCpp`, `PrintQbe`, and 4-ISA
   `Fn.legal` / `isLegal` across `.aarch64`, `.scalar64`, `.x64AVX512`, and `.x64AVX2`.
2. Root-namespace short aliases for single-line `#print axioms` audit (`< 115` chars) covering
   `Func.Wf`, acyclicity, `382`-row table metadata (`m6SpecTable_sigs`, `m6SpecTable_length`,
   `m6SpecTable_nodup`, `m6SpecTable_noExit`), `mkM6Env_moduleOk`, `m6_solve_bytes_sound`,
   `m6_solve_bytes_m6_sound`, `m6_solve_bytes_host_sound`, `m6_unsat_nv`, and `m6_m6_unsat_nv`
   (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM6ProofTest

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Proof
open LeanQbe.T.Examples.LratBytes

#guard m6Fns.length == 382
#guard m6Module.checkAcyclic == true
#guard m6Module.exits.isEmpty && m6Module.externs.isEmpty
#guard m6Module.sigs.length == 382
#guard fullM6ExtBytes == 2304 && fullM6HdrTotalBytes == 3456
#guard fullM6ExtBytes + fullFixedBytes 1 + 2 * 40 + 136 + 8 <= nvM6WorkLen
#guard (ppTModule m6Module).isOk
#guard (PrintQbe.module m6Module).isOk
#guard (ppModule (m6Fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m6Fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m6Fns.map (Fn.legal .x64AVX512))).isOk
#guard (ppModule (m6Fns.map (Fn.legal .x64AVX2))).isOk
#guard m6Fns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard m6Fns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard m6Fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard m6Fns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

end LeanQbeTest.T.KissatM6ProofTest

section AxiomAudit

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6Proof

theorem m6_wf_ok : ∀ f ∈ m6Fns, f.Wf := m6Fns_wf

theorem m6_acyclic_ok : m6Module.checkAcyclic = true := m6_acyclic

theorem m6_tbl_sigs_ok (tPfx : List SpecEntry)
    (s : Spec [i64, i64, i64, i64, i64] [i64])
    (h : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig) :
    (m6SpecTable tPfx s).map (fun e => (e.name, e.as, e.rs)) = m6Fns.map Fn.sig :=
  m6SpecTable_sigs tPfx s h

theorem m6_tbl_len_ok (tPfx : List SpecEntry)
    (s : Spec [i64, i64, i64, i64, i64] [i64])
    (h : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig) :
    (m6SpecTable tPfx s).length = 382 :=
  m6SpecTable_length tPfx s h

theorem m6_tbl_nodup_ok (tPfx : List SpecEntry)
    (s : Spec [i64, i64, i64, i64, i64] [i64])
    (h : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig) :
    ((m6SpecTable tPfx s).map SpecEntry.name).Nodup :=
  m6SpecTable_nodup tPfx s h

theorem m6_tbl_noExit_ok (tPfx : List SpecEntry)
    (s : Spec [i64, i64, i64, i64, i64] [i64])
    (h : tPfx.all SpecEntry.noExit = true) :
    (m6SpecTable tPfx s).all SpecEntry.noExit = true :=
  m6SpecTable_noExit tPfx s h

theorem m6_mod_ok (tPfx : List SpecEntry)
    (s : Spec [i64, i64, i64, i64, i64] [i64])
    (hW : ∀ a m Q X, s a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hX : ∀ a m Q X X', s a m Q X → s a m Q X')
    (hS : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (hP : M6OrchPfxTblSpecs tPfx)
    (hO : TableImpl (mkM6Env tPfx s) (m6Orch_fns.take 24) tPfx)
    (hK : ∀ a m Q X, fullWarmupSpec a m Q X →
      mkM6Env tPfx s "full_walk" [i64] [] a m Q X) :
    ModuleOk (mkM6Env tPfx s) m6Module :=
  mkM6Env_moduleOk tPfx s hW hX hS hP hO hK

theorem m6_sound_ok (tPfx : List SpecEntry)
    (hS : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (hP : M6OrchPfxTblSpecs tPfx)
    (hO : TableImpl (mkM6Env tPfx fullM6SolveBytesSpec) (m6Orch_fns.take 24) tPfx)
    (hK : ∀ a m Q X, fullWarmupSpec a m Q X →
      mkM6Env tPfx fullM6SolveBytesSpec "full_walk" [i64] [] a m Q X)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp (mkM6Env tPfx fullM6SolveBytesSpec) FullM6Orch.kissat_solve_bytes_body
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
  m6_solve_bytes_sound tPfx hS hP hO hK hcfit hwfit hm

theorem m6_m6_sound_ok (tPfx : List SpecEntry)
    (hS : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (hP : M6OrchPfxTblSpecs tPfx)
    (hO : TableImpl (mkM6Env tPfx fullM6SolveBytesSpec) (m6Orch_fns.take 24) tPfx)
    (hK : ∀ a m Q X, fullWarmupSpec a m Q X →
      mkM6Env tPfx fullM6SolveBytesSpec "full_walk" [i64] [] a m Q X)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp (mkM6Env tPfx fullM6SolveBytesSpec) kissat_solve_bytes_m6_body
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
  m6_solve_bytes_m6_sound tPfx hS hP hO hK hcfit hwfit hm

theorem m6_host_ok
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
  m6_solve_bytes_host_sound hq hdmem

theorem m6_nv_unsat_ok (tPfx : List SpecEntry)
    (hS : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (hP : M6OrchPfxTblSpecs tPfx)
    (hO : TableImpl (mkM6Env tPfx fullM6SolveBytesCoreModelSpec) (m6Orch_fns.take 24) tPfx)
    (hK : ∀ a m Q X, fullWarmupSpec a m Q X →
      mkM6Env tPfx fullM6SolveBytesCoreModelSpec "full_walk" [i64] [] a m Q X) :
    Func.wp (mkM6Env tPfx fullM6SolveBytesCoreModelSpec) FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m6_unsat_nv tPfx hS hP hO hK

theorem m6_m6_nv_unsat_ok (tPfx : List SpecEntry)
    (hS : tPfx.map (fun e => (e.name, e.as, e.rs)) = (m6Orch_fns.take 24).map Fn.sig)
    (hP : M6OrchPfxTblSpecs tPfx)
    (hO : TableImpl (mkM6Env tPfx fullM6SolveBytesCoreModelSpec) (m6Orch_fns.take 24) tPfx)
    (hK : ∀ a m Q X, fullWarmupSpec a m Q X →
      mkM6Env tPfx fullM6SolveBytesCoreModelSpec "full_walk" [i64] [] a m Q X) :
    Func.wp (mkM6Env tPfx fullM6SolveBytesCoreModelSpec) kissat_solve_bytes_m6_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  m6_m6_unsat_nv tPfx hS hP hO hK

#print axioms m6_wf_ok
#print axioms m6_acyclic_ok
#print axioms m6_tbl_sigs_ok
#print axioms m6_tbl_len_ok
#print axioms m6_tbl_nodup_ok
#print axioms m6_tbl_noExit_ok
#print axioms m6_mod_ok
#print axioms m6_sound_ok
#print axioms m6_m6_sound_ok
#print axioms m6_host_ok
#print axioms m6_nv_unsat_ok
#print axioms m6_m6_nv_unsat_ok

end AxiomAudit
