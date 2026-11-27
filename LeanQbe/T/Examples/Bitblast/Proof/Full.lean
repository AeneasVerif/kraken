/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
public import LeanQbe.T.Examples.Bitblast.Proof.Specs
public import LeanQbe.T.Examples.Bitblast.Proof.OpsCoreHelpers
public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMulSpecs
public import LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpopHelpers
import LeanQbe.T.Examples.Bitblast.Proof.Arena
import LeanQbe.T.Examples.Bitblast.Proof.Bvp1
import LeanQbe.T.Examples.Bitblast.Proof.Validate0
import LeanQbe.T.Examples.Bitblast.Proof.ValidateNode
import LeanQbe.T.Examples.Bitblast.Proof.Validate
import LeanQbe.T.Examples.Bitblast.Proof.Aig
import LeanQbe.T.Examples.Bitblast.Proof.Tseitin0
import LeanQbe.T.Examples.Bitblast.Proof.Tseitin
import LeanQbe.T.Examples.Bitblast.Proof.OpsCore0
import LeanQbe.T.Examples.Bitblast.Proof.OpsCore1
import LeanQbe.T.Examples.Bitblast.Proof.OpsCore2
import LeanQbe.T.Examples.Bitblast.Proof.OpsCore
import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMul0
import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMul1
import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMul2
import LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop0
import LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop1
import LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop2
import LeanQbe.T.Examples.Bitblast.Proof.Driver0
import LeanQbe.T.Examples.Bitblast.Proof.DriverShiftMul
import LeanQbe.T.Examples.Bitblast.Proof.DriverDivCpop
import LeanQbe.T.Examples.Bitblast.Proof.Driver1
import LeanQbe.T.Examples.Bitblast.Proof.DriverInit
import LeanQbe.T.Examples.Bitblast.Proof.Driver
import LeanQbe.T.Logic.Bytes
import LeanQbe.T.Logic.MemLemmas

/-!
# End-to-End 32-Op Bitblast Module Soundness & UNSAT Proof (`Bitblast.Proof.Full`)

Assembles all `64` canonical `Func.wp` proofs (`Validate` + `Aig` + `Tseitin` + `OpsCore` +
`OpsShiftMul` + `OpsDivCpop` + `Driver`) into flat `bitblast_moduleOk : ModuleOk bitblastEnv
bitblastModule`, derives top-level `bv_solve_bytes_unsat_wp` with `XPost := False` covering all
`32` `BVP1` opcodes, and proves concrete `Mem 64` non-vacuity `nv_bv_solve_bytes_unsat` (`<= std3`).
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

/-- Closed `65`-row specification table for `bitblastModule` (`64` defined fns + `1` extern,
all `noExit = true`). -/
def bitblastSpecTable : List SpecEntry :=
  -- Validate (4): indices 0..3
  [ ⟨"bv_read_u32", [i64, i64], [i32], bvReadU32Spec, true⟩
  , ⟨"bv_count_atoms", [i64, i32], [i64], bvCountAtomsSpec, true⟩
  , ⟨"bv_validate_node", [i64, i64, i32, i32, i32], [.bool], bvValidateNodeSpec, true⟩
  , ⟨"bv_validate", [i64, i64], [.bool], bvValidateSpec, true⟩
  -- Aig (11): indices 4..14
  , ⟨"bv_hash_pair", [i32, i32], [i32], bvHashPairSpec, true⟩
  , ⟨"bv_aig_init", [i64, i64, i32, i64, i32, i32], [], bvAigInitSpec, true⟩
  , ⟨"bv_mk_and", [i64, i32, i32], [i32], bvMkAndSpec, true⟩
  , ⟨"bv_aig_not", [i32], [i32], bvAigNotSpec, true⟩
  , ⟨"bv_aig_or", [i64, i32, i32], [i32], bvAigOrSpec, true⟩
  , ⟨"bv_aig_xor", [i64, i32, i32], [i32], bvAigXorSpec, true⟩
  , ⟨"bv_aig_beq", [i64, i32, i32], [i32], bvAigBeqSpec, true⟩
  , ⟨"bv_aig_ite", [i64, i32, i32, i32], [i32], bvAigIteSpec, true⟩
  , ⟨"bv_lits_mark", [i64], [i32], bvLitsMarkSpec, true⟩
  , ⟨"bv_lits_release", [i64, i32], [], bvLitsReleaseSpec, true⟩
  , ⟨"bv_lits_alloc", [i64, i32], [i32], bvLitsAllocSpec, true⟩
  -- Tseitin (8): indices 15..22
  , ⟨"bv_coi_mark", [i64, i32], [], bvCoiMarkSpec, true⟩
  , ⟨"bv_dec_len", [i32], [i64], bvDecLenSpec, true⟩
  , ⟨"bv_lit_bytes", [i32], [i64], bvLitBytesSpec, true⟩
  , ⟨"bv_write_dec", [i64, i32], [i64], bvWriteDecSpec, true⟩
  , ⟨"bv_write_lit", [i64, i32], [i64], bvWriteLitSpec, true⟩
  , ⟨"bv_write_dimacs_hdr", [i64, i32, i32], [i64], bvWriteDimacsHdrSpec, true⟩
  , ⟨"bv_write_clause_end", [i64], [i64], bvWriteClauseEndSpec, true⟩
  , ⟨"bv_dimacs_write", [i64, i32], [.bool], bvDimacsWriteSpec, true⟩
  -- OpsCore (13): indices 23..35
  , ⟨"bv_slice_ok", [i64, i32, i32], [.bool], bvSliceOkSpec, true⟩
  , ⟨"bv_blast_extract", [i64, i32, i32, i32, i32], [i32], bvBlastExtractSpec, true⟩
  , ⟨"bv_blast_append", [i64, i32, i32, i32, i32], [i32], bvBlastAppendSpec, true⟩
  , ⟨"bv_blast_not", [i64, i32, i32], [i32], bvBlastNotSpec, true⟩
  , ⟨"bv_blast_bin_bitwise", [i64, i32, i32, i32, i32], [i32], bvBlastBinBitwiseSpec, true⟩
  , ⟨"bv_blast_and", [i64, i32, i32, i32], [i32], bvBlastAndSpec, true⟩
  , ⟨"bv_blast_or", [i64, i32, i32, i32], [i32], bvBlastOrSpec, true⟩
  , ⟨"bv_blast_xor", [i64, i32, i32, i32], [i32], bvBlastXorSpec, true⟩
  , ⟨"bv_full_adder_carry", [i64, i32, i32, i32], [i32], bvFullAdderCarrySpec, true⟩
  , ⟨"bv_blast_add", [i64, i32, i32, i32], [i32], bvBlastAddSpec, true⟩
  , ⟨"bv_blast_eq", [i64, i32, i32, i32], [i32], bvBlastEqSpec, true⟩
  , ⟨"bv_blast_ult", [i64, i32, i32, i32], [i32], bvBlastUltSpec, true⟩
  , ⟨"bv_blast_get_lsb_d", [i64, i32, i32, i32], [i32], bvBlastGetLsbDSpec, true⟩
  -- OpsShiftMul (12): indices 36..47
  , ⟨"bv_copy_lits", [i64, i32, i32, i32], [], bvCopyLitsSpec, true⟩
  , ⟨"bv_blast_replicate", [i64, i32, i32, i32], [i32], bvBlastReplicateSpec, true⟩
  , ⟨"bv_blast_rotl", [i64, i32, i32, i32], [i32], bvBlastRotlSpec, true⟩
  , ⟨"bv_blast_rotr", [i64, i32, i32, i32], [i32], bvBlastRotrSpec, true⟩
  , ⟨"bv_blast_ashrc", [i64, i32, i32, i32], [i32], bvBlastAshrcSpec, true⟩
  , ⟨"bv_blast_reverse", [i64, i32, i32], [i32], bvBlastReverseSpec, true⟩
  , ⟨"bv_blast_shift_var", [i64, i32, i32, i32, i32, i32], [i32], bvBlastShiftVarSpec, true⟩
  , ⟨"bv_blast_shl", [i64, i32, i32, i32, i32], [i32], bvBlastShlSpec, true⟩
  , ⟨"bv_blast_ushr", [i64, i32, i32, i32, i32], [i32], bvBlastUshrSpec, true⟩
  , ⟨"bv_blast_ashr", [i64, i32, i32, i32, i32], [i32], bvBlastAshrSpec, true⟩
  , ⟨"bv_blast_mul", [i64, i32, i32, i32], [i32], bvBlastMulSpec, true⟩
  , ⟨"bv_blast_clz", [i64, i32, i32], [i32], bvBlastClzSpec, true⟩
  -- OpsDivCpop (9): indices 48..56
  , ⟨"bv_blast_ite_into", [i64, i32, i32, i32, i32, i32], [.bool],
      OpsDivCpop.bvBlastIteIntoSpec, true⟩
  , ⟨"bv_blast_ite_slice", [i64, i32, i32, i32, i32], [i32],
      OpsDivCpop.bvBlastIteSliceSpec, true⟩
  , ⟨"bv_blast_sub_with_borrow", [i64, i32, i32, i32, i32], [i32],
      OpsDivCpop.bvBlastSubWithBorrowSpec, true⟩
  , ⟨"bv_blast_udiv_umod", [i64, i32, i32, i32, i32], [i32],
      OpsDivCpop.bvBlastUdivUmodSpec, true⟩
  , ⟨"bv_blast_udiv", [i64, i32, i32, i32], [i32], OpsDivCpop.bvBlastUdivSpec, true⟩
  , ⟨"bv_blast_umod", [i64, i32, i32, i32], [i32], OpsDivCpop.bvBlastUmodSpec, true⟩
  , ⟨"bv_blast_add_into", [i64, i32, i32, i32, i32], [.bool],
      OpsDivCpop.bvBlastAddIntoSpec, true⟩
  , ⟨"bv_blast_cpop_layer", [i64, i32, i32, i32, i32], [.bool],
      OpsDivCpop.bvBlastCpopLayerSpec, true⟩
  , ⟨"bv_blast_cpop", [i64, i32, i32], [i32], OpsDivCpop.bvBlastCpopSpec, true⟩
  -- Driver (7): indices 57..63
  , ⟨"bv_eval_ops_core", [i64, i32], [.bool], bvEvalSubSpec, true⟩
  , ⟨"bv_eval_ops_shift_mul", [i64, i32], [.bool], bvEvalSubSpec, true⟩
  , ⟨"bv_eval_ops_div_cpop", [i64, i32], [.bool], bvEvalSubSpec, true⟩
  , ⟨"bv_eval_node", [i64, i32], [.bool], bvEvalNodeSpec, true⟩
  , ⟨"bv_eval_program", [i64], [.bool], bvEvalProgramSpec, true⟩
  , ⟨"bv_init_workspace", [i64, i64, i64, i64], [.bool], bvInitWorkspaceSpec, true⟩
  , ⟨"bv_solve_bytes", [i64, i64, i64, i64, i64], [i64], bvSolveBytesSpec, true⟩
  -- Extern (1): index 64
  , ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], kissatSolveBytesUnsatSpec, true⟩ ]

/-- Closed canonical `Env` for `bitblastModule`. -/
def bitblastEnv : Env := Env.ofTable bitblastSpecTable

/-- Callee prefix before `bv_solve_bytes` inside `bitblastModule.fns` (`63` fns). -/
def bitblastPre : List Fn :=
  Validate.fns ++ Aig.fns ++ Tseitin.fns ++ OpsCore.fns ++
    OpsShiftMul.fns ++ OpsDivCpop.fns ++ Driver.fns.take 6

/-- Top-level `bv_solve_bytes` entry function matching the `64`th slot of `bitblastModule.fns`. -/
def bvSolveBytesFn : Fn :=
  ⟨"bv_solve_bytes", [i64, i64, i64, i64, i64], [i64], Driver.bv_solve_bytes_body⟩

/-- Restricted `Env` visible to `bv_solve_bytes` (`63` internal callees + `kissat_solve_bytes`). -/
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

theorem bitblastSpecTable_length : bitblastSpecTable.length = 65 := rfl

theorem bitblastSpecTable_nodup : (bitblastSpecTable.map SpecEntry.name).Nodup := by
  show ([ "bv_read_u32", "bv_count_atoms", "bv_validate_node", "bv_validate"
    , "bv_hash_pair", "bv_aig_init", "bv_mk_and", "bv_aig_not"
    , "bv_aig_or", "bv_aig_xor", "bv_aig_beq", "bv_aig_ite"
    , "bv_lits_mark", "bv_lits_release", "bv_lits_alloc"
    , "bv_coi_mark", "bv_dec_len", "bv_lit_bytes", "bv_write_dec"
    , "bv_write_lit", "bv_write_dimacs_hdr", "bv_write_clause_end", "bv_dimacs_write"
    , "bv_slice_ok", "bv_blast_extract", "bv_blast_append", "bv_blast_not"
    , "bv_blast_bin_bitwise", "bv_blast_and", "bv_blast_or", "bv_blast_xor"
    , "bv_full_adder_carry", "bv_blast_add", "bv_blast_eq", "bv_blast_ult"
    , "bv_blast_get_lsb_d"
    , "bv_copy_lits", "bv_blast_replicate", "bv_blast_rotl", "bv_blast_rotr"
    , "bv_blast_ashrc", "bv_blast_reverse", "bv_blast_shift_var", "bv_blast_shl"
    , "bv_blast_ushr", "bv_blast_ashr", "bv_blast_mul", "bv_blast_clz"
    , "bv_blast_ite_into", "bv_blast_ite_slice", "bv_blast_sub_with_borrow"
    , "bv_blast_udiv_umod", "bv_blast_udiv", "bv_blast_umod", "bv_blast_add_into"
    , "bv_blast_cpop_layer", "bv_blast_cpop"
    , "bv_eval_ops_core", "bv_eval_ops_shift_mul", "bv_eval_ops_div_cpop"
    , "bv_eval_node", "bv_eval_program", "bv_init_workspace", "bv_solve_bytes"
    , "kissat_solve_bytes" ] : List String).Nodup
  decide

theorem bitblastSpecTable_noExit : ∀ e ∈ bitblastSpecTable, e.noExit = true := by
  intro e he
  simp only [bitblastSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> rfl

theorem bitblastEnv_noExit :
    ∀ f as bs xs m Q X X',
      bitblastEnv f as bs xs m Q X → bitblastEnv f as bs xs m Q X' :=
  Env.ofTable_noExit bitblastSpecTable_noExit

theorem bitblastEnv_row_at (i : Nat) (e : SpecEntry)
    (hi : bitblastSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by
      intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → bitblastEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) bitblastSpecTable_nodup (hno xs m Q X h)

/-! ## Spec Refinement Bridges (`OpsShiftMul` & `OpsDivCpop` -> `OpsCore`) -/

private theorem smBvBlastAddSpec_refines_opsCore
    {xs : Tup Val [i64, i32, i32, i32]} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (h : smBvBlastAddSpec xs m Q X) : bvBlastAddSpec xs m Q X := by
  rcases xs with ⟨hPtr, aOff, bOff, w, ⟨⟩⟩
  rcases h with ⟨hdr, g, aw, ht, lp, R, haig, hlp_eq, hreq, hwf, hm, hQ⟩
  obtain ⟨hoom0, _, hsA, hsB⟩ := hreq rfl
  obtain ⟨hwfA, hwfB⟩ := hwf hoom0 rfl hsA hsB
  refine ⟨hdr, g, aw, ht, lp, R, haig, Nat.le_of_eq hlp_eq.symm, fun _ _ _ =>
    ⟨fun j hj => by rw [haig.aig_len_eq]; exact hwfA j hj,
     fun j hj => by rw [haig.aig_len_eq]; exact hwfB j hj⟩, hm, ?_⟩
  intro ret hdr' g' aw' ht' lp' m' hfr hext _ haig' hlp' hpres hlits_le _ hlcap' _ _ hok_r hoom_r
    hm'
  have hfr_sm : hdr.OpsFrame hdr' :=
    ⟨hfr.work_base, hfr.work_end, hfr.prog_ptr, hfr.aig_ptr, hfr.ht_ptr, hfr.atom_base_ptr,
     hfr.slice_off_ptr, hfr.lits_ptr, hfr.marks_ptr, hfr.dimacs_start, hfr.n_vars, hfr.n_nodes,
     hfr.n_cwords, hfr.root_node, hfr.num_atoms, hfr.aig_cap, hfr.ht_mask, hfr.lits_cap,
     hfr.dimacs_len⟩
  refine hQ ret hdr' g' aw' ht' lp' m' hfr_sm hext haig' hlp' hlits_le hlcap' hpres
    (fun hbad => by
      rcases hbad with h1 | h2 | h3 | h4
      · exact absurd hoom0 h1
      · cases h2
      · rw [hsA] at h3; cases h3
      · rw [hsB] at h4; cases h4)
    hoom_r
    (fun hz => by
      obtain ⟨h0, h1, h2, _, hret, hlen, hwf', hsd⟩ := hok_r hz
      exact ⟨h0, rfl, h1, h2, hret, hlen,
        fun j hj => by rw [← haig'.aig_len_eq]; exact hwf' j hj, hsd⟩)
    hm'

private theorem dcBvBlastEqSpec_refines_opsCore
    {xs : Tup Val [i64, i32, i32, i32]} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (h : OpsDivCpop.bvBlastEqSpec xs m Q X) : bvBlastEqSpec xs m Q X := by
  rcases xs with ⟨hPtr, aOff, bOff, w, ⟨⟩⟩
  rcases h with ⟨hdr, g, aw, ht, lp, R, haig, hcap_le, hlen_cap, hwf, hm, hQ⟩
  refine ⟨hdr, g, aw, ht, lp, R, haig, Nat.le_trans hlen_cap hcap_le,
    fun h0 hsA hsB => by
      obtain ⟨hlc, hptr, ha_s⟩ := sliceBoundsOk_sum hsA
      obtain ⟨_, _, hb_s⟩ := sliceBoundsOk_sum hsB
      obtain ⟨hwfA, hwfB⟩ := hwf h0 hlc hptr ha_s hb_s
      exact ⟨hwfA.2, hwfB.2⟩, hm, ?_⟩
  intro ret hdr' g' aw' ht' m' hfr hext hsz haig' hoom_pr hbound hok_r hoom_r hm'
  refine hQ ret hdr' g' aw' ht' m' hfr hext hsz haig' hoom_pr
    (fun h0 hlc hptr ha_s hb_s hc hg =>
      hbound h0 (sliceBoundsOk_of_parts hlc hptr ha_s) (sliceBoundsOk_of_parts hlc hptr hb_s) hc hg)
    hoom_r
    (fun hz => by
      obtain ⟨h0, hsA, hsB, hret_lt, hev⟩ := hok_r hz
      obtain ⟨hlc, hptr, ha_s⟩ := sliceBoundsOk_sum hsA
      obtain ⟨_, _, hb_s⟩ := sliceBoundsOk_sum hsB
      refine ⟨h0, hlc, hptr, ha_s, hb_s, hret_lt, fun ρ => ?_⟩
      rw [hev ρ]
      by_cases hall : ∀ j < w.toNat,
          g.evalLit ρ (UInt32.ofBitVec (lp.getD (aOff.toNat + j) 0#32)) =
            g.evalLit ρ (UInt32.ofBitVec (lp.getD (bOff.toNat + j) 0#32))
      · have hveq : OpsDivCpop.sliceVal g ρ lp aOff.toNat w.toNat =
            OpsDivCpop.sliceVal g ρ lp bOff.toNat w.toNat := by
          apply BitVec.eq_of_getLsbD_eq; intro j hj
          rw [OpsDivCpop.sliceVal_getLsbD hj, OpsDivCpop.sliceVal_getLsbD hj]; exact hall j hj
        rw [decide_eq_true hall, decide_eq_true hveq]
      · have hvne : OpsDivCpop.sliceVal g ρ lp aOff.toNat w.toNat ≠
            OpsDivCpop.sliceVal g ρ lp bOff.toNat w.toNat := fun heq => hall fun j hj => by
          have := congrArg (fun v => v.getLsbD j) heq
          rwa [OpsDivCpop.sliceVal_getLsbD hj, OpsDivCpop.sliceVal_getLsbD hj] at this
        rw [decide_eq_false hall, decide_eq_false hvne])
    hm'

private theorem bitblastModule_fns_nodup : (bitblastModule.fns.map Fn.name).Nodup := by
  have hchk := bitblastModule_checkAcyclic
  simp only [Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

private theorem bitblastModule_tableImpl :
    TableImpl bitblastEnv bitblastModule.fns bitblastSpecTable := by
  have hSmAdd : ∀ xs m Q X, smBvBlastAddSpec xs m Q X →
      bitblastEnv "bv_blast_add" [i64, i32, i32, i32] [i32] xs m Q X :=
    fun xs m Q X h => bitblastEnv_row_at 32 _ (hi := rfl) (hno := fun _ _ _ _ hs => hs)
      xs m Q X (smBvBlastAddSpec_refines_opsCore h)
  have hDcEq : ∀ xs m Q X, OpsDivCpop.bvBlastEqSpec xs m Q X →
      bitblastEnv "bv_blast_eq" [i64, i32, i32, i32] [i32] xs m Q X :=
    fun xs m Q X h => bitblastEnv_row_at 33 _ (hi := rfl) (hno := fun _ _ _ _ hs => hs)
      xs m Q X (dcBvBlastEqSpec_refines_opsCore h)
  dsimp only [bitblastModule, bitblastFns, Validate.fns, Aig.fns, Tseitin.fns, OpsCore.fns,
    OpsCore.opsCoreFns, OpsShiftMul.fns, OpsShiftMul.opsShiftMulFns, OpsDivCpop.fns,
    OpsDivCpop.opsDivCpopFns, Driver.fns, Validate.validate_fns, Aig.aig_fns, Tseitin.tseitin_fns,
    OpsCore.ops_core_fns, OpsShiftMul.ops_shift_mul_fns, OpsDivCpop.ops_div_cpop_fns,
    Driver.driver_fns, List.cons_append, List.nil_append, bitblastSpecTable]
  refine ⟨
    -- Validate (0..3)
    SpecEntry.Impl.of (bv_read_u32_wp bitblastEnv),
    SpecEntry.Impl.of (bv_count_atoms_wp bitblastEnv (bitblastEnv_row_at 0 _)),
    SpecEntry.Impl.of (bv_validate_node_wp bitblastEnv (bitblastEnv_row_at 0 _)),
    SpecEntry.Impl.of (bv_validate_wp bitblastEnv (bitblastEnv_row_at 0 _)
      (bitblastEnv_row_at 1 _) (bitblastEnv_row_at 2 _)),
    -- Aig (4..14)
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
    -- Tseitin (15..22)
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
    -- OpsCore (23..35)
    SpecEntry.Impl.of (bv_slice_ok_wp bitblastEnv),
    SpecEntry.Impl.of (bv_blast_extract_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 14 _)),
    SpecEntry.Impl.of (bv_blast_append_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 14 _)),
    SpecEntry.Impl.of (bv_blast_not_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 14 _) (bitblastEnv_row_at 7 _)),
    SpecEntry.Impl.of (bv_blast_bin_bitwise_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 14 _) (bitblastEnv_row_at 6 _)
      (bitblastEnv_row_at 8 _) (bitblastEnv_row_at 9 _)),
    SpecEntry.Impl.of (bv_blast_and_wp bitblastEnv (bitblastEnv_row_at 27 _)),
    SpecEntry.Impl.of (bv_blast_or_wp bitblastEnv (bitblastEnv_row_at 27 _)),
    SpecEntry.Impl.of (bv_blast_xor_wp bitblastEnv (bitblastEnv_row_at 27 _)),
    SpecEntry.Impl.of (bv_full_adder_carry_wp bitblastEnv
      (bitblastEnv_row_at 6 _) (bitblastEnv_row_at 8 _) (bitblastEnv_row_at 9 _)),
    SpecEntry.Impl.of (bv_blast_add_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 14 _) (bitblastEnv_row_at 9 _)
      (bitblastEnv_row_at 31 _)),
    SpecEntry.Impl.of (bv_blast_eq_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 6 _) (bitblastEnv_row_at 10 _)),
    SpecEntry.Impl.of (bv_blast_ult_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 7 _) (bitblastEnv_row_at 31 _)),
    SpecEntry.Impl.of (bv_blast_get_lsb_d_wp bitblastEnv (bitblastEnv_row_at 23 _)),
    -- OpsShiftMul (36..47)
    SpecEntry.Impl.of (bv_copy_lits_wp bitblastEnv),
    SpecEntry.Impl.of (bv_blast_replicate_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 14 _) (bitblastEnv_row_at 36 _)),
    SpecEntry.Impl.of (bv_blast_rotl_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 14 _)),
    SpecEntry.Impl.of (bv_blast_rotr_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 14 _)),
    SpecEntry.Impl.of (bv_blast_ashrc_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 14 _)),
    SpecEntry.Impl.of (bv_blast_reverse_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 14 _)),
    SpecEntry.Impl.of (bv_blast_shift_var_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 14 _) (bitblastEnv_row_at 12 _)
      (bitblastEnv_row_at 13 _) (bitblastEnv_row_at 36 _) (bitblastEnv_row_at 8 _)
      (bitblastEnv_row_at 11 _)),
    SpecEntry.Impl.of (bv_blast_shl_wp bitblastEnv (bitblastEnv_row_at 42 _)),
    SpecEntry.Impl.of (bv_blast_ushr_wp bitblastEnv (bitblastEnv_row_at 42 _)),
    SpecEntry.Impl.of (bv_blast_ashr_wp bitblastEnv (bitblastEnv_row_at 42 _)),
    SpecEntry.Impl.of (bv_blast_mul_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 14 _) (bitblastEnv_row_at 6 _)
      (bitblastEnv_row_at 12 _) (bitblastEnv_row_at 13 _) hSmAdd (bitblastEnv_row_at 11 _)),
    SpecEntry.Impl.of (bv_blast_clz_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 14 _) (bitblastEnv_row_at 11 _)),
    -- OpsDivCpop (48..56)
    SpecEntry.Impl.of (OpsDivCpop.bv_blast_ite_into_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 11 _)),
    SpecEntry.Impl.of (OpsDivCpop.bv_blast_ite_slice_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 12 _) (bitblastEnv_row_at 13 _)
      (bitblastEnv_row_at 14 _) (bitblastEnv_row_at 48 _)),
    SpecEntry.Impl.of (OpsDivCpop.bv_blast_sub_with_borrow_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 7 _) (bitblastEnv_row_at 6 _)
      (bitblastEnv_row_at 8 _) (bitblastEnv_row_at 9 _)),
    SpecEntry.Impl.of (OpsDivCpop.bv_blast_udiv_umod_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 12 _) (bitblastEnv_row_at 14 _)
      (bitblastEnv_row_at 13 _) hDcEq (bitblastEnv_row_at 7 _)
      (bitblastEnv_row_at 50 _) (bitblastEnv_row_at 48 _)),
    SpecEntry.Impl.of (OpsDivCpop.bv_blast_udiv_wp bitblastEnv (bitblastEnv_row_at 51 _)),
    SpecEntry.Impl.of (OpsDivCpop.bv_blast_umod_wp bitblastEnv (bitblastEnv_row_at 51 _)),
    SpecEntry.Impl.of (OpsDivCpop.bv_blast_add_into_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 9 _) (bitblastEnv_row_at 6 _)
      (bitblastEnv_row_at 8 _)),
    SpecEntry.Impl.of (OpsDivCpop.bv_blast_cpop_layer_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 54 _)),
    SpecEntry.Impl.of (OpsDivCpop.bv_blast_cpop_wp bitblastEnv
      (bitblastEnv_row_at 23 _) (bitblastEnv_row_at 12 _) (bitblastEnv_row_at 14 _)
      (bitblastEnv_row_at 13 _) (bitblastEnv_row_at 55 _)),
    -- Driver (57..63)
    SpecEntry.Impl.of (bv_eval_ops_core_wp bitblastEnv (bitblastEnv_row_at 0 _)
      (bitblastEnv_row_at 14 _) (bitblastEnv_row_at 24 _) (bitblastEnv_row_at 28 _)
      (bitblastEnv_row_at 29 _) (bitblastEnv_row_at 30 _) (bitblastEnv_row_at 32 _)
      (bitblastEnv_row_at 26 _) (bitblastEnv_row_at 25 _) (bitblastEnv_row_at 33 _)
      (bitblastEnv_row_at 34 _) (bitblastEnv_row_at 35 _)),
    SpecEntry.Impl.of (bv_eval_ops_shift_mul_wp bitblastEnv (bitblastEnv_row_at 0 _)
      (bitblastEnv_row_at 38 _) (bitblastEnv_row_at 39 _) (bitblastEnv_row_at 40 _)
      (bitblastEnv_row_at 41 _) (bitblastEnv_row_at 47 _) (bitblastEnv_row_at 37 _)
      (bitblastEnv_row_at 43 _) (bitblastEnv_row_at 44 _) (bitblastEnv_row_at 45 _)
      (bitblastEnv_row_at 46 _)),
    SpecEntry.Impl.of (bv_eval_ops_div_cpop_wp bitblastEnv (bitblastEnv_row_at 0 _)
      (bitblastEnv_row_at 52 _) (bitblastEnv_row_at 53 _) (bitblastEnv_row_at 56 _)),
    SpecEntry.Impl.of (bv_eval_node_wp bitblastEnv (bitblastEnv_row_at 0 _)
      (bitblastEnv_row_at 6 _) (bitblastEnv_row_at 7 _) (bitblastEnv_row_at 8 _)
      (bitblastEnv_row_at 9 _) (bitblastEnv_row_at 10 _) (bitblastEnv_row_at 11 _)
      (bitblastEnv_row_at 57 _) (bitblastEnv_row_at 58 _) (bitblastEnv_row_at 59 _)),
    SpecEntry.Impl.of (bv_eval_program_wp bitblastEnv (bitblastEnv_row_at 60 _)),
    SpecEntry.Impl.of (bv_init_workspace_wp bitblastEnv (bitblastEnv_row_at 0 _)
      (bitblastEnv_row_at 1 _) (bitblastEnv_row_at 5 _)),
    SpecEntry.Impl.of (bv_solve_bytes_wp bitblastEnv (bitblastEnv_row_at 3 _)
      (bitblastEnv_row_at 62 _) (bitblastEnv_row_at 61 _) (bitblastEnv_row_at 15 _)
      (bitblastEnv_row_at 22 _) (bitblastEnv_row_at 64 _)),
    trivial⟩

/-- Closed `ModuleOk` for `bitblastModule` against the canonical `65`-row `bitblastEnv`. -/
theorem bitblast_moduleOk : ModuleOk bitblastEnv bitblastModule :=
  Module.moduleOk_of_checkAcyclic bitblastModule_checkAcyclic bitblastModule_wf
    (Env.ofTable_sound bitblastModule_fns_nodup bitblastModule_tableImpl)

private theorem bitblastModule_fns_split :
    bitblastModule.fns = bitblastPre ++ [bvSolveBytesFn] := by
  rfl

/-- Top-level `bv_solve_bytes` UNSAT soundness (`XPost := False`) covering all `32` `BVP1`
opcodes, restricted to declared internal callees and extern `kissat_solve_bytes` UNSAT contract. -/
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
    (bitblastEnv_row_at 63 ⟨"bv_solve_bytes", [i64, i64, i64, i64, i64], [i64],
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
