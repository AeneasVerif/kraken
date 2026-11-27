/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
public import LeanQbe.T.Examples.Bitblast.Proof.Specs
import LeanQbe.T.Examples.Bitblast.Proof.Arena
import LeanQbe.T.Examples.Bitblast.Proof.Bvp1
import LeanQbe.T.Examples.Bitblast.Proof.Validate0
import LeanQbe.T.Examples.Bitblast.Proof.ValidateNode
import LeanQbe.T.Examples.Bitblast.Proof.Validate
import LeanQbe.T.Examples.Bitblast.Proof.Aig
import LeanQbe.T.Examples.Bitblast.Proof.Tseitin0
import LeanQbe.T.Examples.Bitblast.Proof.Tseitin
import LeanQbe.T.Examples.Bitblast.Proof.Driver0
import LeanQbe.T.Examples.Bitblast.Proof.Driver1
import LeanQbe.T.Examples.Bitblast.Proof.DriverInit
import LeanQbe.T.Examples.Bitblast.Proof.Driver
import LeanQbe.T.Logic.Bytes
import LeanQbe.T.Logic.MemLemmas

/-!
# End-to-End Bitblast Module Soundness & UNSAT Proof (`Bitblast.Proof.Full`)

Assembles all `30` canonical `Func.wp` proofs into flat `bitblast_moduleOk : ModuleOk bitblastEnv
bitblastModule`, derives top-level `bv_solve_bytes_unsat_wp` with `XPost := False` (given extern
`kissat_solve_bytes` UNSAT spec `r = 20#64 -> ∃ cnf, parseDimacs bs = some cnf ∧ cnf.Unsat`), and
proves concrete `Mem 64` non-vacuity `nv_bv_solve_bytes_unsat` (`<= std3`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open Std Std.Sat Std.ExtHashMap
open Std.Tactic.BVDecide
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Ref.BVProg
open LeanQbe.T.Examples.Bitblast.Src
open LeanQbe.T.Examples.Bitblast.Src.Full

@[expose] public section

/-- Callee prefix before `bv_solve_bytes` inside `bitblastModule.fns`. -/
def bitblastPre : List Fn :=
  Validate.fns ++ Aig.fns ++ Tseitin.fns ++ Driver.fns.take 6

/-- Top-level `bv_solve_bytes` entry function matching the `30`th slot of `bitblastModule.fns`. -/
def bvSolveBytesFn : Fn :=
  ⟨"bv_solve_bytes", [i64, i64, i64, i64, i64], [i64], Driver.bv_solve_bytes_body⟩

/-- Restricted `Env` visible to `bv_solve_bytes` (`29` internal callees + `kissat_solve_bytes`). -/
def bitblastSolvedEnv : Env :=
  Env.restrict bitblastEnv
    (bitblastPre.map Fn.sig ++ bitblastModule.externs.map Extern.sig)

/-- Concrete `BVP1` byte sequence encoding `BCONST false` (`52` bytes = `13` LE `u32` words). -/
def nvProgBytes : List UInt8 :=
  BVProg.wordsToBytesLE [0x31505642, 1, 0, 1, 0, 0, 0, 0, 25, 1, 0, 0, 0]

def nvProgPtr : BitVec 64 := 0x100000#64
def nvProgLen : BitVec 64 := 52#64
def nvWorkPtr : BitVec 64 := 0x100034#64
def nvWorkCap : BitVec 64 := 0x1000#64
def nvFuel : BitVec 64 := 1#64

/-- Concrete `Mem 64` slab holding `nvProgBytes` at `0x100000` plus `0x1000` scratch bytes. -/
def nvMem : Mem 64 :=
  (nvProgBytes ++ List.replicate 0x1000 (0 : UInt8)).At nvProgPtr

end

public section

private theorem bitblastModule_fns_nodup : (bitblastModule.fns.map Fn.name).Nodup := by
  have hchk := bitblastModule_checkAcyclic
  simp only [Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

private theorem bitblastModule_tableImpl :
    TableImpl bitblastEnv bitblastModule.fns bitblastSpecTable := by
  dsimp only [bitblastModule, bitblastFns, Validate.fns, Aig.fns, Tseitin.fns, Driver.fns,
    Validate.validate_fns, Aig.aig_fns, Tseitin.tseitin_fns, Driver.driver_fns,
    List.cons_append, List.nil_append, bitblastSpecTable]
  refine ⟨SpecEntry.Impl.of (bv_read_u32_wp bitblastEnv),
    SpecEntry.Impl.of (bv_count_atoms_wp bitblastEnv (bitblastEnv_row_at 0 _)),
    SpecEntry.Impl.of (bv_validate_node_wp bitblastEnv (bitblastEnv_row_at 0 _)),
    SpecEntry.Impl.of (bv_validate_wp bitblastEnv (bitblastEnv_row_at 0 _)
      (bitblastEnv_row_at 1 _) (bitblastEnv_row_at 2 _)),
    SpecEntry.Impl.of (bv_hash_pair_wp bitblastEnv),
    SpecEntry.Impl.of (bv_aig_init_wp bitblastEnv),
    SpecEntry.Impl.of (bv_mk_and_wp bitblastEnv (bitblastEnv_row_at 4 _)),
    SpecEntry.Impl.of (bv_aig_not_wp bitblastEnv),
    SpecEntry.Impl.of (bv_aig_or_wp bitblastEnv (bitblastEnv_row_at 6 _)),
    SpecEntry.Impl.of (bv_aig_xor_wp bitblastEnv (bitblastEnv_row_at 6 _)),
    SpecEntry.Impl.of (bv_aig_beq_wp bitblastEnv (bitblastEnv_row_at 9 _)),
    SpecEntry.Impl.of (bv_aig_ite_wp bitblastEnv (bitblastEnv_row_at 6 _)),
    SpecEntry.Impl.of (bv_lits_mark_wp bitblastEnv),
    SpecEntry.Impl.of (bv_lits_release_wp bitblastEnv),
    SpecEntry.Impl.of (bv_lits_alloc_wp bitblastEnv),
    SpecEntry.Impl.of (bv_coi_mark_wp bitblastEnv),
    SpecEntry.Impl.of (bv_dec_len_wp bitblastEnv),
    SpecEntry.Impl.of (bv_lit_bytes_wp bitblastEnv (bitblastEnv_row_at 16 _)),
    SpecEntry.Impl.of (bv_write_dec_wp bitblastEnv (bitblastEnv_row_at 16 _)),
    SpecEntry.Impl.of (bv_write_lit_wp bitblastEnv (bitblastEnv_row_at 18 _)),
    SpecEntry.Impl.of (bv_write_dimacs_hdr_wp bitblastEnv (bitblastEnv_row_at 18 _)),
    SpecEntry.Impl.of (bv_write_clause_end_wp bitblastEnv),
    SpecEntry.Impl.of (bv_dimacs_write_wp bitblastEnv (bitblastEnv_row_at 16 _)
      (bitblastEnv_row_at 17 _) (bitblastEnv_row_at 19 _) (bitblastEnv_row_at 20 _)
      (bitblastEnv_row_at 21 _)),
    SpecEntry.Impl.of (bv_eval_ops_core_wp bitblastEnv (bitblastEnv_row_at 0 _)
      (bitblastEnv_row_at 6 _) (bitblastEnv_row_at 7 _) (bitblastEnv_row_at 10 _)
      (bitblastEnv_row_at 14 _)),
    SpecEntry.Impl.of (bv_eval_ops_shift_mul_wp bitblastEnv),
    SpecEntry.Impl.of (bv_eval_ops_div_cpop_wp bitblastEnv),
    SpecEntry.Impl.of (bv_eval_node_wp bitblastEnv (bitblastEnv_row_at 0 _)
      (bitblastEnv_row_at 6 _) (bitblastEnv_row_at 7 _) (bitblastEnv_row_at 8 _)
      (bitblastEnv_row_at 9 _) (bitblastEnv_row_at 10 _) (bitblastEnv_row_at 11 _)
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 24 _) (bitblastEnv_row_at 25 _)),
    SpecEntry.Impl.of (bv_eval_program_wp bitblastEnv (bitblastEnv_row_at 26 _)),
    SpecEntry.Impl.of (bv_init_workspace_wp bitblastEnv (bitblastEnv_row_at 0 _)
      (bitblastEnv_row_at 1 _) (bitblastEnv_row_at 5 _)),
    SpecEntry.Impl.of (bv_solve_bytes_wp bitblastEnv (bitblastEnv_row_at 3 _)
      (bitblastEnv_row_at 28 _) (bitblastEnv_row_at 27 _) (bitblastEnv_row_at 15 _)
      (bitblastEnv_row_at 22 _) (bitblastEnv_row_at 30 _)),
    trivial⟩

/-- Closed `ModuleOk` for `bitblastModule` against the canonical `31`-row `bitblastEnv`. -/
theorem bitblast_moduleOk : ModuleOk bitblastEnv bitblastModule :=
  Module.moduleOk_of_checkAcyclic bitblastModule_checkAcyclic bitblastModule_wf
    (Env.ofTable_sound bitblastModule_fns_nodup bitblastModule_tableImpl)

private theorem bitblastModule_fns_split :
    bitblastModule.fns = bitblastPre ++ [bvSolveBytesFn] := by
  rfl

/-- Top-level `bv_solve_bytes` UNSAT soundness (`XPost := False`) restricted to declared
internal callees and extern `kissat_solve_bytes` UNSAT contract. -/
theorem bv_solve_bytes_unsat_wp (progPtr progLen workPtr workCap fuel : BitVec 64)
    (m : Mem 64) (Q : Post [i64]) (progBytes : List UInt8) (R : Mem 64 → Prop)
    (hplen : progLen.toNat = progBytes.length)
    (hm : (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ R) m)
    (hQ : ∀ (r : BitVec 64) (m' : Mem 64),
      (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ R) m' →
      (r = 20#64 → ∀ prog : BVLogicalExpr, BVProg.parse progBytes = some prog → prog.Unsat) →
      (bvSolveTrivialUnsatCond progPtr progBytes workPtr workCap fuel → r = 20#64) →
      Q (r, ⟨⟩) m') :
    Func.wp bitblastSolvedEnv Driver.bv_solve_bytes_body
      (progPtr, progLen, workPtr, workCap, fuel, ⟨⟩) m Q (fun _ _ _ _ => False) :=
  bitblast_moduleOk.wp_restrict (fn := bvSolveBytesFn) bitblastModule_fns_split
    (bitblastEnv_row_at 29 ⟨"bv_solve_bytes", [i64, i64, i64, i64, i64], [i64],
        bvSolveBytesSpec, true⟩ (by rfl) (by intro _ _ _ _ h; exact h)
      (progPtr, progLen, workPtr, workCap, fuel, ⟨⟩) m Q (fun _ _ _ _ => False)
      ⟨progBytes, R, hplen, hm, fun r m' hm' hunsat htriv => hQ r m' hm' hunsat htriv⟩)

/-- `ValidBVP1` holds for concrete `nvProgBytes`. -/
theorem nvProgBytes_valid : ValidBVP1 nvProgBytes :=
  { len_ge := by decide
    len_mod4 := by decide
    magic_eq := by decide
    ver_eq := by decide
    nodes_pos := by decide
    root_lt := by decide
    total_len := by decide
    atoms_ok := by decide
    nodes_ok := by
      intro i hi
      have h3 : u32At nvProgBytes 3 = 1 := by decide
      have hi0 : i = 0 := by omega
      subst hi0
      decide
    root_bool := by decide }

/-- Workspace-fit and trivial-UNSAT preconditions hold concretely for `(nvProgPtr, nvWorkPtr)`. -/
theorem nvProgBytes_trivialUnsat :
    bvSolveTrivialUnsatCond nvProgPtr nvProgBytes nvWorkPtr nvWorkCap nvFuel := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    nvProgBytes_valid, ⟨by decide, by decide⟩, ?_, by decide⟩
  intro i hi
  have h3 : u32At nvProgBytes 3 = 1 := by decide
  have hi0 : i = 0 := by omega
  subst hi0
  decide

/-- Concrete `Mem 64` satisfies the separation-logic footprint of `bv_solve_bytes`. -/
theorem nvMem_ok :
    (bytes nvProgPtr nvProgBytes ⋆ region nvWorkPtr nvWorkCap.toNat ⋆
      (ExtHashMap.emp : Mem 64 → Prop)) nvMem := by
  have hl_p : nvProgBytes.length = 52 := rfl
  have hl_rep : (List.replicate 0x1000 (0 : UInt8)).length = 0x1000 := List.length_replicate
  have hlen : nvProgBytes.length + (List.replicate 0x1000 (0 : UInt8)).length ≤ 2 ^ 64 := by
    rw [hl_p, hl_rep]; decide
  have hsep := Mem.At_append_sep nvProgBytes (List.replicate 0x1000 (0 : UInt8)) nvProgPtr hlen
  have hself : Eq ((nvProgBytes ++ List.replicate 0x1000 (0 : UInt8)).At nvProgPtr) nvMem := rfl
  have hadr : nvProgPtr + BitVec.ofNat 64 nvProgBytes.length = nvWorkPtr := by
    rw [hl_p]; rfl
  rw [hsep, hadr] at hself
  have h1 : (bytes nvProgPtr nvProgBytes ⋆ region nvWorkPtr nvWorkCap.toNat) nvMem := by
    rw [sep_comm] at hself ⊢
    exact sep_mono (P := Eq ((List.replicate 0x1000 (0 : UInt8)).At nvWorkPtr))
      (fun _ h => ⟨List.replicate 0x1000 (0 : UInt8), hl_rep, h.symm⟩) hself
  simpa [Std.ExtHashMap.sep_emp] using h1

/-- Concrete `Mem 64` non-vacuity witness for `bv_solve_bytes_unsat_wp` returning `20#64` on a
1-node `BCONST false` `BVP1` program (`<= std3`). -/
theorem nv_bv_solve_bytes_unsat :
    Func.wp bitblastSolvedEnv Driver.bv_solve_bytes_body
      (nvProgPtr, nvProgLen, nvWorkPtr, nvWorkCap, nvFuel, ⟨⟩) nvMem
      (fun r m' =>
        r.1 = 20#64 ∧
        (bytes nvProgPtr nvProgBytes ⋆ region nvWorkPtr nvWorkCap.toNat ⋆
          (ExtHashMap.emp : Mem 64 → Prop)) m' ∧
        (∀ prog : BVLogicalExpr, BVProg.parse nvProgBytes = some prog → prog.Unsat))
      (fun _ _ _ _ => False) :=
  bv_solve_bytes_unsat_wp nvProgPtr nvProgLen nvWorkPtr nvWorkCap nvFuel nvMem _
    nvProgBytes ExtHashMap.emp (by decide) nvMem_ok
    (fun r m' hm' hunsat htriv =>
      have hr20 : r = 20#64 := htriv nvProgBytes_trivialUnsat
      ⟨hr20, hm', hunsat hr20⟩)

end

end LeanQbe.T.Examples.Bitblast.Proof
