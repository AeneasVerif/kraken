module

public import LeanQbe.T.Examples.Kissat.FullM4SweepProof
meta import LeanQbe.T.Examples.Kissat.FullM4SweepProof

/-!
# Verification, UNSAT Non-Vacuity, and Axiom Audit for `FullM4Sweep` (`24/24`)

1. Executable `#guard` checks on `fullM4Sweep_fns` (`24` functions), `fullM4SweepExterns`
   (`7` externs), `fullM4SweepModule.checkAcyclic`, `fullM4SweepSpecTable` (`31` rows, all
   `noExit = true`), and concrete `100060`-byte dense/sparse `Mem 64` images.
2. Short root-namespace `m4s_*` audit theorems + single-line `#print axioms` audit.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.KissatM4SweepTest

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullM4Sweep

/-! ## 1. Executable `#guard` sanity checks -/

#guard fullM4Sweep_fns.length == 24
#guard fullM4SweepModule.externs.length == 7
#guard fullM4SweepModule.checkAcyclic == true
#guard fullM4SweepSpecTable.length == 31
#guard (fullM4SweepSpecTable.all fun e => e.noExit) == true
#guard fullM4Sweep_fns.map Fn.name ==
  [ "full_k512_init", "full_k512_watch", "full_k512_assign", "full_k512_add_clause",
    "full_k512_mtf", "full_k512_backtrack", "full_k512_propagate", "full_k512_ana_clause",
    "full_k512_analyze", "full_k512_solve", "full_k512_flip", "full_k512_add_live",
    "full_m4_sweep_cone", "full_m4_sweep_refine_sig", "full_m4_sweep_rand_phases",
    "full_m4_sweep_flip_round", "full_m4_sweep_sim", "full_m4_sweep_rearm",
    "full_m4_sweep_build_pht", "full_m4_sweep_units", "full_m4_sweep_classes",
    "full_m4_sweep_var", "full_m4_sweep_dense", "full_m4_sweep_sat" ]
#guard (fullM4Sweep_fns.map fun f => (f.name, f.as.length, f.rs.length)) ==
  [ ("full_k512_init", 2, 0), ("full_k512_watch", 4, 0), ("full_k512_assign", 3, 0),
    ("full_k512_add_clause", 3, 1), ("full_k512_mtf", 2, 0), ("full_k512_backtrack", 2, 0),
    ("full_k512_propagate", 1, 1), ("full_k512_ana_clause", 3, 0), ("full_k512_analyze", 2, 1),
    ("full_k512_solve", 2, 1), ("full_k512_flip", 2, 1), ("full_k512_add_live", 3, 0),
    ("full_m4_sweep_cone", 2, 1), ("full_m4_sweep_refine_sig", 3, 0),
    ("full_m4_sweep_rand_phases", 2, 0), ("full_m4_sweep_flip_round", 2, 1),
    ("full_m4_sweep_sim", 3, 1), ("full_m4_sweep_rearm", 2, 0),
    ("full_m4_sweep_build_pht", 3, 0), ("full_m4_sweep_units", 4, 1),
    ("full_m4_sweep_classes", 4, 1), ("full_m4_sweep_var", 3, 1),
    ("full_m4_sweep_dense", 3, 1), ("full_m4_sweep_sat", 3, 1) ]
#guard nvM4SweepBytes.length == nvM4SweepCfg.avail
#guard nvM4SweepSparseBytes.length == nvM4SweepCfg.avail

end LeanQbeTest.T.KissatM4SweepTest

/-! ## 2. Short root-namespace audit theorems & single-line `#print axioms` -/

section AxiomAudit

open Std Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM4Sweep

theorem m4s_fns_wf : ∀ f ∈ fullM4Sweep_fns, f.Wf := fullM4Sweep_fns_wf

theorem m4s_acyclic : fullM4SweepModule.checkAcyclic = true := fullM4Sweep_acyclic

theorem m4s_noExit : ∀ e ∈ fullM4SweepSpecTable, e.noExit = true :=
  fullM4SweepSpecTable_noExit

theorem m4s_sigs :
    (fullM4SweepSpecTable.take 24).map (fun e => (e.name, e.as, e.rs)) =
      fullM4Sweep_fns.map (fun f => (f.name, f.as, f.rs)) :=
  fullM4SweepSpecTable_sigs

theorem m4s_ext_sigs :
    (fullM4SweepSpecTable.drop 24).map (fun e => ⟨e.name, e.as, e.rs⟩) = fullM4SweepExterns :=
  fullM4SweepSpecTable_ext_sigs

theorem m4s_env_noExit :
    ∀ f as bs xs m Q X X',
      fullM4SweepEnv f as bs xs m Q X → fullM4SweepEnv f as bs xs m Q X' :=
  fullM4SweepEnv_noExit

theorem m4s_moduleOk : ModuleOk fullM4SweepEnv fullM4SweepModule := fullM4SweepEnv_moduleOk

theorem m4s_sat_sound {c : Full.FullCfg} {F0 : CNF Nat} {s : Full.FullState}
    {R : Mem 64 → Prop} {budget tick_lim : BitVec 64} {m : Mem 64}
    (hinv : Full.FullSparseInv c F0 s) (hm : (Full.FullMem c s ⋆ R) m) :
    Func.wp fullM4SweepEnv full_m4_sweep_sat_body (c.hdr, budget, tick_lim, ()) m
      (fun (r, ()) m' => ∃ s',
        Full.FullSparseInv c F0 s' ∧ s'.core.cur_level = 0 ∧
        s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat) ∧ (Full.FullMem c s' ⋆ R) m')
      (fun _ _ _ _ => False) :=
  full_m4_sweep_sat_unsat_sound hinv hm

theorem m4s_dense_sound {c : Full.FullCfg} {F0 : CNF Nat} {s : Full.FullState}
    {R : Mem 64 → Prop} {budget tick_lim : BitVec 64} {m : Mem 64}
    (hinv : Full.FullDenseInv c F0 s) (hm : (Full.FullMem c s ⋆ R) m) :
    Func.wp fullM4SweepEnv full_m4_sweep_dense_body (c.hdr, budget, tick_lim, ()) m
      (fun (r, ()) m' => ∃ s',
        Full.FullDenseInv c F0 s' ∧ s'.core.cur_vars = s.core.cur_vars ∧
        s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat) ∧ (Full.FullMem c s' ⋆ R) m')
      (fun _ _ _ _ => False) :=
  full_m4_sweep_dense_unsat_sound hinv hm

theorem m4s_nv_mem_ok : Full.FullMem nvM4SweepCfg nvM4SweepState nvM4SweepMem :=
  nvM4SweepMem_ok

theorem m4s_nv_sp_mem_ok :
    Full.FullMem nvM4SweepCfg nvM4SweepSparseState nvM4SweepSparseMem :=
  nvM4SweepSparseMem_ok

theorem m4s_nv_k5_init :
    Func.wp fullM4SweepEnv full_k512_init_body (nvM4SweepCfg.hdr, 1#32, ()) nvM4SweepMem
      (fun () m' => ∃ scr',
        (∀ P, K512ScratchInv P scr') ∧ (k5StateOfScratch scr').nv = 1#32 ∧
        Full.FullMem nvM4SweepCfg
          { nvM4SweepState with scratch := { nvM4SweepState.scratch with scratch_buf := scr' } }
          m')
      (fun _ _ _ _ => False) :=
  nv_m4_k512_init

theorem m4s_nv_k5_solve :
    Func.wp fullM4SweepEnv full_k512_solve_body (nvM4SweepCfg.hdr, 100#64, ()) nvM4SweepMem
      (fun (r, ()) m' => ∃ fuel' scr',
        K512ScratchInv (fun _ => False) scr' ∧ (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        Full.nvOneLitF0.Unsat ∧
        Full.FullMem nvM4SweepCfg
          { nvM4SweepState with
            core := { nvM4SweepState.core with fuel := fuel' }
            scratch := { nvM4SweepState.scratch with scratch_buf := scr' } } m')
      (fun _ _ _ _ => False) :=
  nv_m4_k512_solve

theorem m4s_nv_cone :
    Func.wp fullM4SweepEnv full_m4_sweep_cone_body (nvM4SweepCfg.hdr, 0#32, ()) nvM4SweepMem
      (fun (r, ()) m' => ∃ s',
        Full.FullDenseInvW nvM4SweepCfg Full.nvOneLitF0 [[0], [1]] s' ∧
        M4SweepConeOk [[0], [1]] s' (r &&& 0xFFFF#64).toNat ∧
        Full.nvOneLitF0.Unsat ∧ Full.FullMem nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m4_sweep_cone

theorem m4s_nv_var :
    Func.wp fullM4SweepEnv full_m4_sweep_var_body
      (nvM4SweepCfg.hdr, 0#32, 8192#64, ()) nvM4SweepMem
      (fun (r, ()) m' => ∃ s',
        Full.FullDenseInvW nvM4SweepCfg Full.nvOneLitF0 [[0], [1]] s' ∧
        M4TmkZero s' ∧ (r = 1#64 ∨ r = 20#64) ∧
        Full.nvOneLitF0.Unsat ∧ Full.FullMem nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m4_sweep_var

theorem m4s_nv_dense :
    Func.wp fullM4SweepEnv full_m4_sweep_dense_body
      (nvM4SweepCfg.hdr, 10#64, 8192#64, ()) nvM4SweepMem
      (fun (r, ()) m' => ∃ s',
        Full.FullDenseInv nvM4SweepCfg Full.nvOneLitF0 s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ Full.nvOneLitF0.Unsat ∧ Full.FullMem nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m4_sweep_dense

theorem m4s_nv_sat :
    Func.wp fullM4SweepEnv full_m4_sweep_sat_body
      (nvM4SweepCfg.hdr, 10#64, 8192#64, ()) nvM4SweepSparseMem
      (fun (r, ()) m' => ∃ s',
        Full.FullSparseInv nvM4SweepCfg Full.nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        (r = 1#64 ∨ r = 20#64) ∧ Full.nvOneLitF0.Unsat ∧ Full.FullMem nvM4SweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m4_sweep_sat

#print axioms m4s_fns_wf
#print axioms m4s_acyclic
#print axioms m4s_noExit
#print axioms m4s_sigs
#print axioms m4s_ext_sigs
#print axioms m4s_env_noExit
#print axioms m4s_moduleOk
#print axioms m4s_sat_sound
#print axioms m4s_dense_sound
#print axioms m4s_nv_mem_ok
#print axioms m4s_nv_sp_mem_ok
#print axioms m4s_nv_k5_init
#print axioms m4s_nv_k5_solve
#print axioms m4s_nv_cone
#print axioms m4s_nv_var
#print axioms m4s_nv_dense
#print axioms m4s_nv_sat

end AxiomAudit
