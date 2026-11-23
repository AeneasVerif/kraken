module

public import LeanQbe.T.Examples.Kissat.FullM5Hbr
public import LeanQbe.T.Examples.Kissat.FullM5HbrProof
public import LeanQbe.T.Examples.Kissat.FullM5Orch
public import LeanQbe.T.Examples.Kissat.FullM5OrchProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.Kissat.FullM5Hbr
meta import LeanQbe.T.Examples.Kissat.FullM5HbrProof
meta import LeanQbe.T.Examples.Kissat.FullM5Orch
meta import LeanQbe.T.Examples.Kissat.FullM5OrchProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Verification, Compilation Checks, and Axiom Audit for Kissat M5 HBR & Orch (`FullM5Hbr`/`Orch`)

1. Executable `#guard` checks on `m5HbrModule` (`1` fn, `0` externs, `0` exits) and
   `m5OrchModule` (`19` owned `_m5` fns, `51` externs, `0` exits): acyclicity, exact name/arity
   lists, `PrintCpp`, `PrintQbe`, and `Fn.legal` across `.aarch64`, `.scalar64`, `.x64AVX512`, and
   `.x64AVX2`.
2. Restated headline theorems for `m5Hbr_moduleOk`, `nv_m5_hbr_dom`, `m5OrchSpecTable` metadata,
   `m5Orch_moduleOk`, `m5OrchUnsatEnv_moduleOk`, `m5Orch_solve_bytes_correct`, and
   `m5Orch_unsat_nonvacuous` (`XPost := False`, `4096` B workspace, `fuel = 16`, `0` SAT proofs).
3. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM5OrchPrepTest

open LeanQbe.T
open LeanQbe.T.PrintCpp
open LeanQbe.T.Examples.Kissat.FullM5Hbr
open LeanQbe.T.Examples.Kissat.FullM5Orch

/-! ## 1. Static Checks & Backend Compilation / ISA-Legality Guards -/

#guard m5HbrModule.checkAcyclic == true
#guard m5HbrModule.exits.isEmpty
#guard m5HbrModule.externs.isEmpty
#guard m5Hbr_fns.length == 1
#guard m5Hbr_fns.map Fn.name == ["full_hbr_dom_m5"]
#guard (ppTModule m5HbrModule).isOk
#guard (PrintQbe.module m5HbrModule).isOk
#guard (ppModule (m5Hbr_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m5Hbr_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m5Hbr_fns.map (Fn.legal .x64AVX512))).isOk
#guard (ppModule (m5Hbr_fns.map (Fn.legal .x64AVX2))).isOk
#guard m5Hbr_fns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard m5Hbr_fns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard m5Hbr_fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard m5Hbr_fns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

#guard m5OrchModule.checkAcyclic == true
#guard m5OrchModule.exits.isEmpty
#guard m5Orch_fns.length == 19
#guard m5OrchExterns.length == 51
#guard m5OrchModule.sigs.length == 70
#guard m5Orch_fns.map Fn.name ==
  [ "full_calc_ext_cap_m5", "full_calc_scr_cap_m5", "full_init_state_m5"
  , "full_probe_dticks_m5", "full_elim_dticks_m5", "full_trans_lit_m5"
  , "full_transitive_m5", "full_vivify_tier_m5", "full_vivify_m5"
  , "full_sweep_dense_m5", "full_probe_tail_m5", "full_reduce_m5"
  , "full_reorder_m5", "full_probe_m5", "full_eliminate_m5"
  , "full_preprocess_m5", "full_simplify_m5", "full_search_m5"
  , "kissat_solve_bytes_m5" ]
#guard (ppTModule m5OrchModule).isOk
#guard (PrintQbe.module m5OrchModule).isOk
#guard (ppModule (m5Orch_fns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m5Orch_fns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m5Orch_fns.map (Fn.legal .x64AVX512))).isOk
#guard (ppModule (m5Orch_fns.map (Fn.legal .x64AVX2))).isOk
#guard m5Orch_fns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard m5Orch_fns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard m5Orch_fns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard m5Orch_fns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

end LeanQbeTest.T.KissatM5OrchPrepTest

/-! ## 2. Audit-Ready Headline Theorems & Single-Line `#print axioms` -/

section AxiomAudit

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM5Hbr
open LeanQbe.T.Examples.Kissat.FullM5Orch

theorem m5hbr_mod_ok : ModuleOk m5HbrEnv m5HbrModule :=
  m5Hbr_moduleOk

theorem m5hbr_nv :
    Func.wp m5HbrEnv full_hbr_dom_m5_body (nvHbrCfg.hdr, 0#32, 4#32, ()) nvHbrMem
      (fun (dom, ()) _m' =>
        nvHbrF0.Unsat ∧
        (dom = 0xFFFFFFFF#32 ∨ dom.toNat < 2 * nvHbrState.core.cur_vars) ∧
        ∃ mrk' mclr',
          FullMem nvHbrCfg { nvHbrState with core := { nvHbrState.core with
            mrk := mrk', min_clr := mclr' } } _m')
      (fun _ _ _ _ => False) :=
  nv_m5_hbr_dom

theorem m5orch_noExit : ∀ e ∈ m5OrchSpecTable fullSolveBytesSpec, e.noExit = true :=
  m5OrchSpecTable_noExit fullSolveBytesSpec

theorem m5orch_sigs :
    (m5OrchSpecTable fullSolveBytesSpec).map (fun e => (e.name, e.as, e.rs)) =
      m5OrchModule.sigs :=
  m5OrchSpecTable_sigs fullSolveBytesSpec

theorem m5orch_len : (m5OrchSpecTable fullSolveBytesSpec).length = 70 :=
  m5OrchSpecTable_length fullSolveBytesSpec

theorem m5orch_nodup : ((m5OrchSpecTable fullSolveBytesSpec).map SpecEntry.name).Nodup :=
  m5OrchSpecTable_nodup fullSolveBytesSpec

theorem m5orch_mod_ok : ModuleOk m5OrchEnv m5OrchModule :=
  m5Orch_moduleOk

theorem m5orch_unsat_mod_ok : ModuleOk m5OrchUnsatEnv m5OrchModule :=
  m5OrchUnsatEnv_moduleOk

theorem m5orch_solve_ok
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m5OrchEnv kissat_solve_bytes_m5_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  m5Orch_solve_bytes_correct hcfit hwfit hm

theorem m5orch_nv :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp m5OrchUnsatEnv kissat_solve_bytes_m5_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 20#64 ∧ fullNvUnsatCnf.Unsat ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  m5Orch_unsat_nonvacuous

#print axioms m5hbr_mod_ok
#print axioms m5hbr_nv
#print axioms m5orch_noExit
#print axioms m5orch_sigs
#print axioms m5orch_len
#print axioms m5orch_nodup
#print axioms m5orch_mod_ok
#print axioms m5orch_unsat_mod_ok
#print axioms m5orch_solve_ok
#print axioms m5orch_nv

end AxiomAudit
