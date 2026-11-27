/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
public import LeanQbe.T.Examples.Bitblast.Src.OpsShiftMul
public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMulSpecs
public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMul0
public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMul1
public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMul2
import LeanQbe.T.Logic.MemLemmas

/-!
# End-to-End `OpsShiftMul` Module Soundness & Non-Vacuity (`Bitblast.Proof.OpsShiftMul`)

Assembles all `12` canonical `Func.wp` proofs (`OpsShiftMul0`, `OpsShiftMul1`, `OpsShiftMul2`) into
flat `opsShiftMul_moduleOk : ModuleOk opsShiftMulEnv opsShiftMulModule`, provides closed
restricted-environment `Func.wp` corollaries (`XPost := False`) via `ModuleOk.wp_restrict`, and
establishes concrete `Mem 64` non-vacuity witnesses (`<= std3`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open Std.ExtHashMap
open Std.Tactic.BVDecide
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Src.OpsShiftMul

@[expose] public section

/-- Restricted `Env` visible to function `i` of `opsShiftMulFns` (`i` prior internal callees +
`8` declared externs). -/
def opsShiftMulRestrictedEnv (i : Nat) : Env :=
  Env.restrict opsShiftMulEnv
    ((opsShiftMulFns.take i).map Fn.sig ++ opsShiftMulExterns.map Extern.sig)

/-- Concrete `Mem 64` base address for `BVHdrState` witness (`0x100000`). -/
def nvSmH : BitVec 64 := 0x100000#64
def nvSmAigPtr : BitVec 64 := 0x100080#64
def nvSmHtPtr : BitVec 64 := 0x100088#64
def nvSmLitsPtr : BitVec 64 := 0x10008c#64
def nvSmAw : List (BitVec 64) := [0#64]
def nvSmHt : List (BitVec 32) := [0#32]
def nvSmLp : List (BitVec 32) := [1#32, 1#32, 1#32, 0#32] ++ List.replicate 12 0#32

/-- Concrete `BVHdrState` (`lits_len = 4`, `lits_cap = 16`, `a = 3#2`, `b = 1#2`, `oom = 0`). -/
def nvSmHdr : BVHdrState :=
  { work_base := nvSmH, work_end := 0x100200#64, prog_ptr := 0x200000#64,
    aig_ptr := nvSmAigPtr, ht_ptr := nvSmHtPtr, atom_base_ptr := nvSmH + 128,
    slice_off_ptr := nvSmH + 128, lits_ptr := nvSmLitsPtr, marks_ptr := nvSmLitsPtr,
    dimacs_start := nvSmLitsPtr, n_vars := 0#32, n_nodes := 0#32, n_cwords := 0#32,
    root_node := 0#32, num_atoms := 0#32, aig_len := 1#32, aig_cap := 1#32,
    ht_mask := 0#32, lits_len := 4#32, lits_cap := 16#32, oom := 0#32, dimacs_len := 0#32 }

/-- Empty well-formed concrete `Aig` (`0` atoms, `0` gates; constant literals `0#32`/`1#32`). -/
def nvSmAig : Aig := { A := 0, nodes := #[] }

def nvSmB0 : List UInt8 := bytes64 nvSmHdr.u64s
def nvSmB1 : List UInt8 := bytesOf (t := i32) nvSmHdr.u32s
def nvSmB2 : List UInt8 := bytes64 nvSmAw
def nvSmB3 : List UInt8 := bytesOf (t := i32) nvSmHt
def nvSmB4 : List UInt8 := bytesOf (t := i32) nvSmLp
def nvSmBytes : List UInt8 := nvSmB0 ++ (nvSmB1 ++ (nvSmB2 ++ (nvSmB3 ++ nvSmB4)))

/-- Concrete `Mem 64` slab holding `nvSmHdr`, `nvSmAw`, `nvSmHt`, and `nvSmLp` at `0x100000`. -/
def nvSmMem : Mem 64 := nvSmBytes.At nvSmH

end

public section

private theorem opsShiftMulFns_nodup : (opsShiftMulModule.fns.map Fn.name).Nodup := by
  have hchk := opsShiftMul_checkAcyclic
  simp only [Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

/-- Row-lookup helper into the closed `20`-row `opsShiftMulEnv`. -/
theorem opsShiftMulEnv_row_at (i : Nat) (e : SpecEntry)
    (hi : opsShiftMulSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by
      intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → opsShiftMulEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) opsShiftMulSpecTable_nodup (hno xs m Q X h)

/-- All `12` C0 functions of `opsShiftMulModule` implement `opsShiftMulSpecTable`. -/
theorem opsShiftMul_tableImpl :
    TableImpl opsShiftMulEnv opsShiftMulModule.fns opsShiftMulSpecTable := by
  dsimp only [opsShiftMulModule, opsShiftMulFns, ops_shift_mul_fns,
    List.cons_append, List.nil_append, opsShiftMulSpecTable, opsShiftMulFnSpecTable,
    opsShiftMulExternSpecTable]
  refine ⟨
    SpecEntry.Impl.of (bv_copy_lits_wp opsShiftMulEnv),
    SpecEntry.Impl.of (bv_blast_replicate_wp opsShiftMulEnv
      (opsShiftMulEnv_row_at 18 _) (opsShiftMulEnv_row_at 17 _) (opsShiftMulEnv_row_at 0 _)),
    SpecEntry.Impl.of (bv_blast_rotl_wp opsShiftMulEnv
      (opsShiftMulEnv_row_at 18 _) (opsShiftMulEnv_row_at 17 _)),
    SpecEntry.Impl.of (bv_blast_rotr_wp opsShiftMulEnv
      (opsShiftMulEnv_row_at 18 _) (opsShiftMulEnv_row_at 17 _)),
    SpecEntry.Impl.of (bv_blast_ashrc_wp opsShiftMulEnv
      (opsShiftMulEnv_row_at 18 _) (opsShiftMulEnv_row_at 17 _)),
    SpecEntry.Impl.of (bv_blast_reverse_wp opsShiftMulEnv
      (opsShiftMulEnv_row_at 18 _) (opsShiftMulEnv_row_at 17 _)),
    SpecEntry.Impl.of (bv_blast_shift_var_wp opsShiftMulEnv
      (opsShiftMulEnv_row_at 18 _) (opsShiftMulEnv_row_at 17 _) (opsShiftMulEnv_row_at 15 _)
      (opsShiftMulEnv_row_at 16 _) (opsShiftMulEnv_row_at 0 _) (opsShiftMulEnv_row_at 13 _)
      (opsShiftMulEnv_row_at 14 _)),
    SpecEntry.Impl.of (bv_blast_shl_wp opsShiftMulEnv (opsShiftMulEnv_row_at 6 _)),
    SpecEntry.Impl.of (bv_blast_ushr_wp opsShiftMulEnv (opsShiftMulEnv_row_at 6 _)),
    SpecEntry.Impl.of (bv_blast_ashr_wp opsShiftMulEnv (opsShiftMulEnv_row_at 6 _)),
    SpecEntry.Impl.of (bv_blast_mul_wp opsShiftMulEnv
      (opsShiftMulEnv_row_at 18 _) (opsShiftMulEnv_row_at 17 _) (opsShiftMulEnv_row_at 12 _)
      (opsShiftMulEnv_row_at 15 _) (opsShiftMulEnv_row_at 16 _) (opsShiftMulEnv_row_at 19 _)
      (opsShiftMulEnv_row_at 14 _)),
    SpecEntry.Impl.of (bv_blast_clz_wp opsShiftMulEnv
      (opsShiftMulEnv_row_at 18 _) (opsShiftMulEnv_row_at 17 _) (opsShiftMulEnv_row_at 14 _)),
    trivial⟩

/-- Closed `ModuleOk` for `opsShiftMulModule` against the canonical `20`-row `opsShiftMulEnv`. -/
theorem opsShiftMul_moduleOk : ModuleOk opsShiftMulEnv opsShiftMulModule :=
  Module.moduleOk_of_checkAcyclic opsShiftMul_checkAcyclic opsShiftMulFns_wf
    (Env.ofTable_sound opsShiftMulFns_nodup opsShiftMul_tableImpl)

/-- Generic closed restricted-environment `Func.wp` corollary (`XPost := False`) for slot `i`. -/
theorem opsShiftMul_restrict_wp (i : Nat) (name : String) (as rs : List Ty)
    (spec : Spec as rs) (body : Func as rs)
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs}
    (hpre : spec xs m Q (fun _ _ _ _ => False))
    (hsplit : opsShiftMulModule.fns = opsShiftMulFns.take i ++
      ⟨name, as, rs, body⟩ :: opsShiftMulFns.drop (i + 1) := by rfl)
    (hi : opsShiftMulSpecTable[i]? = some ⟨name, as, rs, spec, true⟩ := by rfl) :
    Func.wp (opsShiftMulRestrictedEnv i) body xs m Q (fun _ _ _ _ => False) :=
  opsShiftMul_moduleOk.wp_restrict (fn := ⟨name, as, rs, body⟩) hsplit
    (Env.ofTable_of_mem (List.mem_of_getElem? hi) opsShiftMulSpecTable_nodup hpre)

/-- Closed restricted-environment `bv_blast_mul` theorem (`XPost := False`). -/
theorem bv_blast_mul_closed_wp (h : BitVec 64) (aOff bOff w : BitVec 32)
    (m : Mem 64) (Q : Post [i32]) (hpre : bvBlastMulSpec (h, aOff, bOff, w, ()) m Q
      (fun _ _ _ _ => False)) :
    Func.wp (opsShiftMulRestrictedEnv 10) bv_blast_mul_body (h, aOff, bOff, w, ()) m Q
      (fun _ _ _ _ => False) :=
  opsShiftMul_restrict_wp 10 "bv_blast_mul" [i64, i32, i32, i32] [i32] bvBlastMulSpec
    bv_blast_mul_body hpre

/-- Closed restricted-environment `bv_blast_clz` theorem (`XPost := False`). -/
theorem bv_blast_clz_closed_wp (h : BitVec 64) (aOff w : BitVec 32)
    (m : Mem 64) (Q : Post [i32]) (hpre : bvBlastClzSpec (h, aOff, w, ()) m Q
      (fun _ _ _ _ => False)) :
    Func.wp (opsShiftMulRestrictedEnv 11) bv_blast_clz_body (h, aOff, w, ()) m Q
      (fun _ _ _ _ => False) :=
  opsShiftMul_restrict_wp 11 "bv_blast_clz" [i64, i32, i32] [i32] bvBlastClzSpec
    bv_blast_clz_body hpre

private theorem nvSmBytes_lens :
    nvSmB0.length = 80 ∧ nvSmB1.length = 48 ∧ nvSmB2.length = 8 ∧
    nvSmB3.length = 4 ∧ nvSmB4.length = 64 := by
  simp only [nvSmB0, nvSmB1, nvSmB2, nvSmB3, nvSmB4,
    bytes64_length, bytesOf_length, Ty.bytes, Ty.size]
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  have : nvSmLp.length = 16 := by simp [nvSmLp]
  omega

/-- Concrete `AigInv` holds on `(nvSmHdr, nvSmAig, nvSmAw, nvSmHt)`. -/
theorem nvSmAigInv_ok : AigInv nvSmHdr nvSmAig nvSmAw nvSmHt :=
  { wf := fun _ hi => by simp [nvSmAig] at hi
    num_atoms_eq := rfl
    aig_len_eq := rfl
    aig_len_le_cap := by decide
    aig_cap_eq := rfl
    aig_cap_lt := by decide
    gates_bound := by decide
    words_match := ⟨by decide, fun i hi => by simp [nvSmAig] at hi⟩
    ht_len := rfl
    ht_mask_lt := fun x => by
      rw [show nvSmHdr.ht_mask = 0#32 from rfl, BitVec.and_zero]; decide
    ht_pos := by decide
    ht_bound := by decide }

/-- Concrete `Mem 64` satisfies `(bvHdrMem ⋆ array64 ⋆ array ⋆ array ⋆ emp) nvSmMem`. -/
theorem nvSmMem_ok :
    (bvHdrMem nvSmH nvSmHdr ⋆ array64 nvSmHdr.aig_ptr nvSmAw ⋆
      array (t := i32) nvSmHdr.ht_ptr nvSmHt ⋆ array (t := i32) nvSmHdr.lits_ptr nvSmLp ⋆
      (emp : Mem 64 → Prop)) nvSmMem := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := nvSmBytes_lens
  have hs0 := Mem.At_append_sep nvSmB0 (nvSmB1 ++ (nvSmB2 ++ (nvSmB3 ++ nvSmB4))) nvSmH
    (by simp [List.length_append, h0, h1, h2, h3, h4])
  have hs1 := Mem.At_append_sep nvSmB1 (nvSmB2 ++ (nvSmB3 ++ nvSmB4)) (nvSmH + 80)
    (by simp [List.length_append, h1, h2, h3, h4])
  have hs2 := Mem.At_append_sep nvSmB2 (nvSmB3 ++ nvSmB4) nvSmAigPtr
    (by simp [List.length_append, h2, h3, h4])
  have hs3 := Mem.At_append_sep nvSmB3 nvSmB4 nvSmHtPtr (by rw [h3, h4]; decide)
  have ha0 : nvSmH + BitVec.ofNat 64 nvSmB0.length = nvSmH + 80 := by rw [h0]; rfl
  have ha1 : nvSmH + 80 + BitVec.ofNat 64 nvSmB1.length = nvSmAigPtr := by rw [h1]; rfl
  have ha2 : nvSmAigPtr + BitVec.ofNat 64 nvSmB2.length = nvSmHtPtr := by rw [h2]; rfl
  have ha3 : nvSmHtPtr + BitVec.ofNat 64 nvSmB3.length = nvSmLitsPtr := by rw [h3]; rfl
  rw [ha0] at hs0; rw [ha1] at hs1; rw [ha2] at hs2; rw [ha3] at hs3
  have hm : ((Eq (nvSmB0.At nvSmH) ⋆ Eq (nvSmB1.At (nvSmH + 80))) ⋆
      Eq (nvSmB2.At nvSmAigPtr) ⋆ Eq (nvSmB3.At nvSmHtPtr) ⋆
      Eq (nvSmB4.At nvSmLitsPtr)) nvSmMem := by
    have hself : Eq (nvSmBytes.At nvSmH) nvSmMem := rfl
    change Eq ((nvSmB0 ++ (nvSmB1 ++ (nvSmB2 ++ (nvSmB3 ++ nvSmB4)))).At nvSmH) nvSmMem
      at hself
    rw [hs0, hs1, hs2, hs3] at hself
    exact sep_ac hself
  have hhdr : ∀ m, (Eq (nvSmB0.At nvSmH) ⋆ Eq (nvSmB1.At (nvSmH + 80))) m →
      bvHdrMem nvSmH nvSmHdr m := fun m h =>
    sep_mono2 (fun _ e => e ▸ array64_bytes nvSmH nvSmHdr.u64s (by decide))
      (fun _ e => e ▸ array_bytes (t := i32) (nvSmH + 80) nvSmHdr.u32s (by decide)) m h
  have haig : ∀ m, Eq (nvSmB2.At nvSmAigPtr) m → array64 nvSmHdr.aig_ptr nvSmAw m := fun _ e =>
    show array64 nvSmAigPtr nvSmAw _ from e ▸ array64_bytes nvSmAigPtr nvSmAw (by decide)
  have hht : ∀ m, Eq (nvSmB3.At nvSmHtPtr) m → array (t := i32) nvSmHdr.ht_ptr nvSmHt m :=
    fun _ e =>
      show array (t := i32) nvSmHtPtr nvSmHt _ from e ▸ array_bytes (t := i32) nvSmHtPtr nvSmHt
        (by decide)
  have hlp : ∀ m, Eq (nvSmB4.At nvSmLitsPtr) m → array (t := i32) nvSmHdr.lits_ptr nvSmLp m :=
    fun _ e => show array (t := i32) nvSmLitsPtr nvSmLp _ from
      e ▸ array_bytes (t := i32) nvSmLitsPtr nvSmLp
        (by rw [show nvSmLp.length = 16 by simp [nvSmLp]]; decide)
  have hm' : (bvHdrMem nvSmH nvSmHdr ⋆ array64 nvSmHdr.aig_ptr nvSmAw ⋆
      array (t := i32) nvSmHdr.ht_ptr nvSmHt ⋆ array (t := i32) nvSmHdr.lits_ptr nvSmLp) nvSmMem :=
    sep_mono2 (sep_mono2 (sep_mono2 hhdr haig) hht) hlp nvSmMem hm
  exact sep_ac ((congrFun (Std.ExtHashMap.sep_emp _).symm nvSmMem).mp hm')

private theorem nvSm_pureOp_witness (i : Nat) (name : String) (as : List Ty) (spec : Spec as [i32])
    (body : Func as [i32])
    {ok : BVHdrState → Bool} {outW : BitVec 32} {idxFn : Nat → Nat}
    {xs : Tup Val as}
    (heq : spec xs nvSmMem = fun Q _ => bvLitsPureOpBody nvSmH ok outW idxFn nvSmMem Q)
    (hok : ok nvSmHdr = true)
    (hsplit : opsShiftMulModule.fns = opsShiftMulFns.take i ++
      ⟨name, as, [i32], body⟩ :: opsShiftMulFns.drop (i + 1) := by rfl)
    (hi : opsShiftMulSpecTable[i]? = some ⟨name, as, [i32], spec, true⟩ := by rfl) :
    Func.wp (opsShiftMulRestrictedEnv i) body xs nvSmMem
      (fun r m' =>
        r.1 = 4#32 ∧
        ∃ hdr' lp',
          nvSmHdr.OpsFrame hdr' ∧ hdr'.oom = 0#32 ∧ hdr'.lits_len = 4#32 + outW ∧
          lp'.length = 16 ∧
          (∀ j < outW.toNat, lp'.getD (4 + j) 0#32 = nvSmLp.getD (idxFn j) 0#32) ∧
          (bvHdrMem nvSmH hdr' ⋆ array (t := i32) hdr'.lits_ptr lp' ⋆
            (array64 nvSmHdr.aig_ptr nvSmAw ⋆ array (t := i32) nvSmHdr.ht_ptr nvSmHt ⋆
              (emp : Mem 64 → Prop))) m')
      (fun _ _ _ _ => False) := by
  refine opsShiftMul_restrict_wp i name as [i32] spec body ?_ hsplit hi
  rw [heq]
  refine ⟨nvSmHdr, nvSmLp, array64 nvSmHdr.aig_ptr nvSmAw ⋆
      array (t := i32) nvSmHdr.ht_ptr nvSmHt ⋆ (emp : Mem 64 → Prop),
    by simp [nvSmLp, nvSmHdr], sep_ac nvSmMem_ok,
    fun ret hdr' lp' m' hfr _ hlen _ hgood _ hm' => ?_⟩
  obtain ⟨hoom', hret, hlen', hbits⟩ := hgood hok
  have hl0 : nvSmLp.length = 16 := by simp [nvSmLp]
  have hret_n : ret.toNat = 4 := by rw [hret]; rfl
  rw [hret_n] at hbits
  exact ⟨hret, hdr', lp', hfr, hoom', hlen', hlen.trans hl0, hbits, hm'⟩

/-- Concrete `Mem 64` non-vacuity witness for `bv_copy_lits` (`[1#32, 0#32] -> slots [4, 5]`). -/
theorem nv_bv_copy_lits :
    Func.wp (opsShiftMulRestrictedEnv 0) bv_copy_lits_body (nvSmH, 4#32, 2#32, 2#32, ()) nvSmMem
      (fun _ m' =>
        ∃ lp', lp'.length = 16 ∧
          lp'.getD 4 0#32 = 1#32 ∧ lp'.getD 5 0#32 = 0#32 ∧
          (bvHdrMem nvSmH nvSmHdr ⋆ array (t := i32) nvSmHdr.lits_ptr lp' ⋆
            (array64 nvSmHdr.aig_ptr nvSmAw ⋆ array (t := i32) nvSmHdr.ht_ptr nvSmHt ⋆
              (emp : Mem 64 → Prop))) m')
      (fun _ _ _ _ => False) := by
  refine opsShiftMul_restrict_wp 0 "bv_copy_lits" [i64, i32, i32, i32] [] bvCopyLitsSpec
    bv_copy_lits_body ?_
  have hl0 : nvSmLp.length = 16 := by simp [nvSmLp]
  refine ⟨nvSmHdr, nvSmLp, array64 nvSmHdr.aig_ptr nvSmAw ⋆
      array (t := i32) nvSmHdr.ht_ptr nvSmHt ⋆ (emp : Mem 64 → Prop),
    by decide, by decide, by decide, Or.inr (by decide), sep_ac nvSmMem_ok,
    fun lp' m' hlen _ hcopy hm' => ?_⟩
  have h4 := hcopy 0 (by decide)
  have h5 := hcopy 1 (by decide)
  exact ⟨lp', hlen.trans hl0, h4, h5, hm'⟩

/-- Concrete `Mem 64` witness for `bv_blast_replicate` returning `4#32` (`4` replicated bits). -/
theorem nv_bv_blast_replicate :
    Func.wp (opsShiftMulRestrictedEnv 1) bv_blast_replicate_body
      (nvSmH, 2#32, 2#32, 2#32, ()) nvSmMem
      (fun r _ => r.1 = 4#32) (fun _ _ _ _ => False) := by
  have h := nvSm_pureOp_witness 1 "bv_blast_replicate" [i64, i32, i32, i32] bvBlastReplicateSpec
    bv_blast_replicate_body
    (ok := fun hdr => decide (hdr.oom = 0#32 ∧ sliceOkBool hdr 2#32 2#32 = true ∧
      (2#32 : BitVec 32).toNat * (2#32 : BitVec 32).toNat ≤
        hdr.lits_cap.toNat - hdr.lits_len.toNat))
    (outW := BitVec.ofNat 32 ((2#32 : BitVec 32).toNat * (2#32 : BitVec 32).toNat))
    (idxFn := fun j => (2#32 : BitVec 32).toNat + j % (2#32 : BitVec 32).toNat)
    (xs := (nvSmH, 2#32, 2#32, 2#32, ())) rfl (by decide)
  exact wp_mono (fun _ _ hr => hr.1) (fun _ _ _ _ hx => hx) _ _ h

/-- Concrete `Mem 64` witness for `bv_blast_rotl` returning `4#32` (`rotl([1, 0], 1) = [0, 1]`). -/
theorem nv_bv_blast_rotl :
    Func.wp (opsShiftMulRestrictedEnv 2) bv_blast_rotl_body (nvSmH, 2#32, 2#32, 1#32, ()) nvSmMem
      (fun r m' =>
        r.1 = 4#32 ∧ ∃ hdr' lp', nvSmHdr.OpsFrame hdr' ∧ hdr'.oom = 0#32 ∧
          lp'.getD 4 0#32 = 0#32 ∧ lp'.getD 5 0#32 = 1#32 ∧
          (bvHdrMem nvSmH hdr' ⋆ array (t := i32) hdr'.lits_ptr lp' ⋆
            (array64 nvSmHdr.aig_ptr nvSmAw ⋆ array (t := i32) nvSmHdr.ht_ptr nvSmHt ⋆
              (emp : Mem 64 → Prop))) m')
      (fun _ _ _ _ => False) := by
  have h := nvSm_pureOp_witness 2 "bv_blast_rotl" [i64, i32, i32, i32] bvBlastRotlSpec
    bv_blast_rotl_body
    (ok := fun hdr => decide (hdr.oom = 0#32 ∧ sliceOkBool hdr 2#32 2#32 = true ∧
      (2#32 : BitVec 32).toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat))
    (outW := 2#32)
    (idxFn := fun j =>
      let r := (1#32 : BitVec 32).toNat % (2#32 : BitVec 32).toNat
      (2#32 : BitVec 32).toNat +
        (if j < r then (2#32 : BitVec 32).toNat - r + j else j - r))
    (xs := (nvSmH, 2#32, 2#32, 1#32, ())) rfl (by decide)
  exact wp_mono (fun _ _ ⟨hret, hdr', lp', hfr, hoom', _, _, hbits, hm'⟩ =>
    ⟨hret, hdr', lp', hfr, hoom', hbits 0 (by decide), hbits 1 (by decide), hm'⟩)
    (fun _ _ _ _ hx => hx) _ _ h

/-- Concrete `Mem 64` witness for `bv_blast_rotr` returning `4#32` (`rotr([1, 0], 1) = [0, 1]`). -/
theorem nv_bv_blast_rotr :
    Func.wp (opsShiftMulRestrictedEnv 3) bv_blast_rotr_body (nvSmH, 2#32, 2#32, 1#32, ()) nvSmMem
      (fun r _ => r.1 = 4#32) (fun _ _ _ _ => False) := by
  have h := nvSm_pureOp_witness 3 "bv_blast_rotr" [i64, i32, i32, i32] bvBlastRotrSpec
    bv_blast_rotr_body
    (ok := fun hdr => decide (hdr.oom = 0#32 ∧ sliceOkBool hdr 2#32 2#32 = true ∧
      (2#32 : BitVec 32).toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat))
    (outW := 2#32)
    (idxFn := fun j =>
      let r := (1#32 : BitVec 32).toNat % (2#32 : BitVec 32).toNat
      let cut := (2#32 : BitVec 32).toNat - r
      (2#32 : BitVec 32).toNat + (if j < cut then r + j else j - cut))
    (xs := (nvSmH, 2#32, 2#32, 1#32, ())) rfl (by decide)
  exact wp_mono (fun _ _ hr => hr.1) (fun _ _ _ _ hx => hx) _ _ h

/-- Concrete `Mem 64` witness for `bv_blast_ashrc` returning `4#32`. -/
theorem nv_bv_blast_ashrc :
    Func.wp (opsShiftMulRestrictedEnv 4) bv_blast_ashrc_body (nvSmH, 2#32, 2#32, 1#32, ()) nvSmMem
      (fun r _ => r.1 = 4#32) (fun _ _ _ _ => False) := by
  have h := nvSm_pureOp_witness 4 "bv_blast_ashrc" [i64, i32, i32, i32] bvBlastAshrcSpec
    bv_blast_ashrc_body
    (ok := fun hdr => decide (hdr.oom = 0#32 ∧ sliceOkBool hdr 2#32 2#32 = true ∧
      (2#32 : BitVec 32).toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat))
    (outW := 2#32)
    (idxFn := fun j => (2#32 : BitVec 32).toNat +
      (if (1#32 : BitVec 32).toNat + j < (2#32 : BitVec 32).toNat then
        (1#32 : BitVec 32).toNat + j else (2#32 : BitVec 32).toNat - 1))
    (xs := (nvSmH, 2#32, 2#32, 1#32, ())) rfl (by decide)
  exact wp_mono (fun _ _ hr => hr.1) (fun _ _ _ _ hx => hx) _ _ h

/-- Concrete `Mem 64` witness for `bv_blast_reverse` returning `4#32` (`rev([1, 0]) = [0, 1]`). -/
theorem nv_bv_blast_reverse :
    Func.wp (opsShiftMulRestrictedEnv 5) bv_blast_reverse_body (nvSmH, 2#32, 2#32, ()) nvSmMem
      (fun r m' =>
        r.1 = 4#32 ∧ ∃ hdr' lp', nvSmHdr.OpsFrame hdr' ∧ hdr'.oom = 0#32 ∧
          lp'.getD 4 0#32 = 0#32 ∧ lp'.getD 5 0#32 = 1#32 ∧
          (bvHdrMem nvSmH hdr' ⋆ array (t := i32) hdr'.lits_ptr lp' ⋆
            (array64 nvSmHdr.aig_ptr nvSmAw ⋆ array (t := i32) nvSmHdr.ht_ptr nvSmHt ⋆
              (emp : Mem 64 → Prop))) m')
      (fun _ _ _ _ => False) := by
  have h := nvSm_pureOp_witness 5 "bv_blast_reverse" [i64, i32, i32] bvBlastReverseSpec
    bv_blast_reverse_body
    (ok := fun hdr => decide (hdr.oom = 0#32 ∧ sliceOkBool hdr 2#32 2#32 = true ∧
      (2#32 : BitVec 32).toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat))
    (outW := 2#32)
    (idxFn := fun j => (2#32 : BitVec 32).toNat + ((2#32 : BitVec 32).toNat - 1 - j))
    (xs := (nvSmH, 2#32, 2#32, ())) rfl (by decide)
  exact wp_mono (fun _ _ ⟨hret, hdr', lp', hfr, hoom', _, _, hbits, hm'⟩ =>
    ⟨hret, hdr', lp', hfr, hoom', hbits 0 (by decide), hbits 1 (by decide), hm'⟩)
    (fun _ _ _ _ hx => hx) _ _ h

private theorem nvSm_binOp_witness (i : Nat) (name : String) (as : List Ty) (spec : Spec as [i32])
    (body : Func as [i32])
    (sem : BitVec 2 → BitVec 2 → BitVec 2) {xs : Tup Val as}
    (heq : spec xs nvSmMem = fun Q _ =>
      bvBlastBinOpSpecBody nvSmH 0#32 2#32 2#32 2#32 true sem false nvSmMem Q)
    (hsplit : opsShiftMulModule.fns = opsShiftMulFns.take i ++
      ⟨name, as, [i32], body⟩ :: opsShiftMulFns.drop (i + 1) := by rfl)
    (hi : opsShiftMulSpecTable[i]? = some ⟨name, as, [i32], spec, true⟩ := by rfl) :
    Func.wp (opsShiftMulRestrictedEnv i) body xs nvSmMem
      (fun r _ => r.1 = 4#32 ∨ r.1 = 0xFFFFFFFF#32)
      (fun _ _ _ _ => False) := by
  refine opsShiftMul_restrict_wp i name as [i32] spec body ?_ hsplit hi
  rw [heq]
  have hw2 : (2#32 : BitVec 32).toNat = 2 := rfl
  refine ⟨nvSmHdr, nvSmAig, nvSmAw, nvSmHt, nvSmLp, (emp : Mem 64 → Prop),
    nvSmAigInv_ok, by simp [nvSmLp, nvSmHdr], fun hc => False.elim (Bool.false_ne_true hc),
    fun _ _ _ _ => ⟨fun j hj => by
      rw [hw2] at hj; rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> decide,
      fun j hj => by
        rw [hw2] at hj; rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> decide⟩,
    nvSmMem_ok, fun _ret hdr' _ _ _ _ _ _ _ _ _ _ _ _ _ hoom hok _ => ?_⟩
  by_cases hz : hdr'.oom = 0#32
  · exact Or.inl (hok hz).2.2.2.2.1
  · exact Or.inr (hoom hz)

/-- Concrete `Mem 64` non-vacuity witness for `bv_blast_shl` (`XPost := False`). -/
theorem nv_bv_blast_shl :
    Func.wp (opsShiftMulRestrictedEnv 7) bv_blast_shl_body
      (nvSmH, 0#32, 2#32, 2#32, 2#32, ()) nvSmMem
      (fun r _ => r.1 = 4#32 ∨ r.1 = 0xFFFFFFFF#32) (fun _ _ _ _ => False) :=
  nvSm_binOp_witness 7 "bv_blast_shl" [i64, i32, i32, i32, i32] bvBlastShlSpec
    bv_blast_shl_body (· <<< ·) rfl

/-- Concrete `Mem 64` non-vacuity witness for `bv_blast_mul` (`3#2 * 1#2 = 3#2` when `oom = 0`). -/
theorem nv_bv_blast_mul :
    Func.wp (opsShiftMulRestrictedEnv 10) bv_blast_mul_body (nvSmH, 0#32, 2#32, 2#32, ()) nvSmMem
      (fun r _ => r.1 = 4#32 ∨ r.1 = 0xFFFFFFFF#32) (fun _ _ _ _ => False) :=
  nvSm_binOp_witness 10 "bv_blast_mul" [i64, i32, i32, i32] bvBlastMulSpec
    bv_blast_mul_body (· * ·) rfl

/-- Concrete `Mem 64` non-vacuity witness for `bv_blast_mul` returning `-1` on out-of-range
slice. -/
theorem nv_bv_blast_mul_oom :
    Func.wp (opsShiftMulRestrictedEnv 10) bv_blast_mul_body
      (nvSmH, 10#32, 2#32, 2#32, ()) nvSmMem
      (fun r _ => r.1 = 0xFFFFFFFF#32) (fun _ _ _ _ => False) := by
  refine bv_blast_mul_closed_wp nvSmH 10#32 2#32 2#32 nvSmMem _ ?_
  refine ⟨nvSmHdr, nvSmAig, nvSmAw, nvSmHt, nvSmLp, (emp : Mem 64 → Prop),
    nvSmAigInv_ok, by simp [nvSmLp, nvSmHdr], fun hc => False.elim (Bool.false_ne_true hc),
    fun _ _ hbad _ => absurd hbad (by decide), nvSmMem_ok,
    fun _ret _hdr' _g' _aw' _ht' _lp' _m' _hfr _hext _haig' _hlen _hl1 _hl2 _hpre
      hfail hoom _hok _hm' => ?_⟩
  exact hoom (hfail (Or.inr (Or.inr (Or.inl (by decide)))))

/-- Concrete `Mem 64` non-vacuity witness for `bv_blast_clz` (`XPost := False`). -/
theorem nv_bv_blast_clz :
    Func.wp (opsShiftMulRestrictedEnv 11) bv_blast_clz_body (nvSmH, 2#32, 2#32, ()) nvSmMem
      (fun r _ => r.1 = 4#32 ∨ r.1 = 0xFFFFFFFF#32) (fun _ _ _ _ => False) := by
  have hw2 : (2#32 : BitVec 32).toNat = 2 := rfl
  refine bv_blast_clz_closed_wp nvSmH 2#32 2#32 nvSmMem _ ?_
  refine ⟨nvSmHdr, nvSmAig, nvSmAw, nvSmHt, nvSmLp, (emp : Mem 64 → Prop),
    nvSmAigInv_ok, by simp [nvSmLp, nvSmHdr],
    fun _ _ j hj => by
      rw [hw2] at hj; rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> decide,
    nvSmMem_ok, fun _ret hdr' _g' _aw' _ht' _lp' _m' _hfr _hext _haig' _hlen _hl1 _hl2 _hpre
      _hfail hoom hok _hm' => ?_⟩
  by_cases hz : hdr'.oom = 0#32
  · exact Or.inl (hok hz).2.2.1
  · exact Or.inr (hoom hz)

end

end LeanQbe.T.Examples.Bitblast.Proof
