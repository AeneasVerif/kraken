/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.OpsCoreHelpers
public import LeanQbe.T.Examples.Bitblast.Proof.OpsCore0
public import LeanQbe.T.Examples.Bitblast.Proof.OpsCore1
public import LeanQbe.T.Examples.Bitblast.Proof.OpsCore2
public import LeanQbe.T.Examples.Bitblast.Src.OpsCore
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Logic.ProofKit

/-!
# Canonical WP Certificate Assembly for `Bitblast.Src.OpsCore`

Exports canonical `SpecEntry` tables, `SegCert`, `ModuleOk`, `Env.Has`, `Spec.XFree`,
and `Func.wp` certificates for all 13 C0 functions in `Bitblast/Src/OpsCore.lean`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Src.OpsCore

/-! ## Canonical Spec Tables & Environment -/

@[expose] public section

/-- Canonical `SpecEntry` rows for the 6 AIG/literal externs imported by `OpsCore`. -/
def opsCoreAigExternSpecs : List SpecEntry :=
  [ { name := "bv_mk_and", as := [i64, i32, i32], rs := [i32],
      spec := bvMkAndSpec, noExit := true }
  , { name := "bv_aig_not", as := [i32], rs := [i32],
      spec := bvAigNotSpec, noExit := true }
  , { name := "bv_aig_or", as := [i64, i32, i32], rs := [i32],
      spec := bvAigOrSpec, noExit := true }
  , { name := "bv_aig_xor", as := [i64, i32, i32], rs := [i32],
      spec := bvAigXorSpec, noExit := true }
  , { name := "bv_aig_beq", as := [i64, i32, i32], rs := [i32],
      spec := bvAigBeqSpec, noExit := true }
  , { name := "bv_lits_alloc", as := [i64, i32], rs := [i32],
      spec := bvLitsAllocSpec, noExit := true } ]

/-- Canonical `SpecEntry` rows matching `OpsCore.opsCoreFns` order. -/
def opsCoreOwnSpecTable : List SpecEntry :=
  [ { name := "bv_slice_ok", as := [i64, i32, i32], rs := [.bool],
      spec := bvSliceOkSpec, noExit := true }
  , { name := "bv_blast_extract", as := [i64, i32, i32, i32, i32], rs := [i32],
      spec := bvBlastExtractSpec, noExit := true }
  , { name := "bv_blast_append", as := [i64, i32, i32, i32, i32], rs := [i32],
      spec := bvBlastAppendSpec, noExit := true }
  , { name := "bv_blast_not", as := [i64, i32, i32], rs := [i32],
      spec := bvBlastNotSpec, noExit := true }
  , { name := "bv_blast_bin_bitwise", as := [i64, i32, i32, i32, i32], rs := [i32],
      spec := bvBlastBinBitwiseSpec, noExit := true }
  , { name := "bv_blast_and", as := [i64, i32, i32, i32], rs := [i32],
      spec := bvBlastAndSpec, noExit := true }
  , { name := "bv_blast_or", as := [i64, i32, i32, i32], rs := [i32],
      spec := bvBlastOrSpec, noExit := true }
  , { name := "bv_blast_xor", as := [i64, i32, i32, i32], rs := [i32],
      spec := bvBlastXorSpec, noExit := true }
  , { name := "bv_full_adder_carry", as := [i64, i32, i32, i32], rs := [i32],
      spec := bvFullAdderCarrySpec, noExit := true }
  , { name := "bv_blast_add", as := [i64, i32, i32, i32], rs := [i32],
      spec := bvBlastAddSpec, noExit := true }
  , { name := "bv_blast_eq", as := [i64, i32, i32, i32], rs := [i32],
      spec := bvBlastEqSpec, noExit := true }
  , { name := "bv_blast_ult", as := [i64, i32, i32, i32], rs := [i32],
      spec := bvBlastUltSpec, noExit := true }
  , { name := "bv_blast_get_lsb_d", as := [i64, i32, i32, i32], rs := [i32],
      spec := bvBlastGetLsbDSpec, noExit := true } ]

/-- Combined canonical specification table for `OpsCore.opsCoreModule`. -/
def opsCoreSpecTable : List SpecEntry := opsCoreOwnSpecTable ++ opsCoreAigExternSpecs

/-- Canonical environment built from `opsCoreSpecTable`. -/
def opsCoreEnv : Env := Env.ofTable opsCoreSpecTable

end

/-! ## `XFree`, `Nodup`, `NoExit`, and Satisfaction Certificates -/

private theorem bvMkAndSpec_xfree : bvMkAndSpec.XFree := by xfree
private theorem bvAigNotSpec_xfree : bvAigNotSpec.XFree := by xfree
private theorem bvAigOrSpec_xfree : bvAigOrSpec.XFree := by xfree
private theorem bvAigXorSpec_xfree : bvAigXorSpec.XFree := by xfree
private theorem bvAigBeqSpec_xfree : bvAigBeqSpec.XFree := by xfree
private theorem bvLitsAllocSpec_xfree : bvLitsAllocSpec.XFree := by xfree

private theorem mem_own_has {Γ : Env} (hSat : Γ.Sat opsCoreOwnSpecTable)
    {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ opsCoreOwnSpecTable) (hx : sp.XFree) :
    Γ.Has nm sp :=
  Env.Sat.has hSat hmem hx

private theorem mem_ext_has {Γ : Env} (hSat : Γ.Sat opsCoreAigExternSpecs)
    {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ opsCoreAigExternSpecs) (hx : sp.XFree) :
    Γ.Has nm sp :=
  Env.Sat.has hSat hmem hx

public section

theorem opsCoreSpecTable_nodup : (opsCoreSpecTable.map SpecEntry.name).Nodup := by
  simp only [opsCoreSpecTable, opsCoreOwnSpecTable, opsCoreAigExternSpecs, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append]
  decide

theorem opsCoreSpecTable_noExit : ∀ e ∈ opsCoreSpecTable, e.noExit = true := by
  intro e he
  simp only [opsCoreSpecTable, opsCoreOwnSpecTable, opsCoreAigExternSpecs, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rfl
  · rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem opsCoreAigExternSpecs_xfree : ∀ e ∈ opsCoreAigExternSpecs, e.spec.XFree := by
  intro e he
  simp only [opsCoreAigExternSpecs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact bvMkAndSpec_xfree
  · exact bvAigNotSpec_xfree
  · exact bvAigOrSpec_xfree
  · exact bvAigXorSpec_xfree
  · exact bvAigBeqSpec_xfree
  · exact bvLitsAllocSpec_xfree

theorem opsCoreOwnSpecTable_xfree : ∀ e ∈ opsCoreOwnSpecTable, e.spec.XFree := by
  intro e he
  simp only [opsCoreOwnSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bvSliceOkSpec_xfree
  · exact bvBlastExtractSpec_xfree
  · exact bvBlastAppendSpec_xfree
  · exact bvBlastNotSpec_xfree
  · exact bvBlastBinBitwiseSpec_xfree
  · exact bvBlastAndSpec_xfree
  · exact bvBlastOrSpec_xfree
  · exact bvBlastXorSpec_xfree
  · exact bvFullAdderCarrySpec_xfree
  · exact bvBlastAddSpec_xfree
  · exact bvBlastEqSpec_xfree
  · exact bvBlastUltSpec_xfree
  · exact bvBlastGetLsbDSpec_xfree

theorem opsCoreSpecTable_xfree : ∀ e ∈ opsCoreSpecTable, e.spec.XFree := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact opsCoreOwnSpecTable_xfree e he
  · exact opsCoreAigExternSpecs_xfree e he

theorem opsCoreEnv_sat : opsCoreEnv.Sat opsCoreSpecTable :=
  Env.Sat.ofTable_self opsCoreSpecTable_nodup

theorem opsCoreEnv_sat_own : opsCoreEnv.Sat opsCoreOwnSpecTable :=
  Env.Sat.left opsCoreEnv_sat

theorem opsCoreEnv_sat_extern : opsCoreEnv.Sat opsCoreAigExternSpecs :=
  Env.Sat.right opsCoreEnv_sat

theorem opsCoreEnv_noExit :
    ∀ (f : Sym) (as bs : List Ty) (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X X' : XPost),
      opsCoreEnv f as bs xs m Q X → opsCoreEnv f as bs xs m Q X' :=
  Env.ofTable_noExit opsCoreSpecTable_noExit

/-! ## Canonical `Env.Has` Theorems -/

theorem opsCoreEnv_has_bv_slice_ok :
    opsCoreEnv.Has "bv_slice_ok" bvSliceOkSpec :=
  mem_own_has opsCoreEnv_sat_own (by simp [opsCoreOwnSpecTable]) bvSliceOkSpec_xfree

theorem opsCoreEnv_has_bv_blast_extract :
    opsCoreEnv.Has "bv_blast_extract" bvBlastExtractSpec :=
  mem_own_has opsCoreEnv_sat_own (by simp [opsCoreOwnSpecTable]) bvBlastExtractSpec_xfree

theorem opsCoreEnv_has_bv_blast_append :
    opsCoreEnv.Has "bv_blast_append" bvBlastAppendSpec :=
  mem_own_has opsCoreEnv_sat_own (by simp [opsCoreOwnSpecTable]) bvBlastAppendSpec_xfree

theorem opsCoreEnv_has_bv_blast_not :
    opsCoreEnv.Has "bv_blast_not" bvBlastNotSpec :=
  mem_own_has opsCoreEnv_sat_own (by simp [opsCoreOwnSpecTable]) bvBlastNotSpec_xfree

theorem opsCoreEnv_has_bv_blast_bin_bitwise :
    opsCoreEnv.Has "bv_blast_bin_bitwise" bvBlastBinBitwiseSpec :=
  mem_own_has opsCoreEnv_sat_own (by simp [opsCoreOwnSpecTable]) bvBlastBinBitwiseSpec_xfree

theorem opsCoreEnv_has_bv_blast_and :
    opsCoreEnv.Has "bv_blast_and" bvBlastAndSpec :=
  mem_own_has opsCoreEnv_sat_own (by simp [opsCoreOwnSpecTable]) bvBlastAndSpec_xfree

theorem opsCoreEnv_has_bv_blast_or :
    opsCoreEnv.Has "bv_blast_or" bvBlastOrSpec :=
  mem_own_has opsCoreEnv_sat_own (by simp [opsCoreOwnSpecTable]) bvBlastOrSpec_xfree

theorem opsCoreEnv_has_bv_blast_xor :
    opsCoreEnv.Has "bv_blast_xor" bvBlastXorSpec :=
  mem_own_has opsCoreEnv_sat_own (by simp [opsCoreOwnSpecTable]) bvBlastXorSpec_xfree

theorem opsCoreEnv_has_bv_full_adder_carry :
    opsCoreEnv.Has "bv_full_adder_carry" bvFullAdderCarrySpec :=
  mem_own_has opsCoreEnv_sat_own (by simp [opsCoreOwnSpecTable]) bvFullAdderCarrySpec_xfree

theorem opsCoreEnv_has_bv_blast_add :
    opsCoreEnv.Has "bv_blast_add" bvBlastAddSpec :=
  mem_own_has opsCoreEnv_sat_own (by simp [opsCoreOwnSpecTable]) bvBlastAddSpec_xfree

theorem opsCoreEnv_has_bv_blast_eq :
    opsCoreEnv.Has "bv_blast_eq" bvBlastEqSpec :=
  mem_own_has opsCoreEnv_sat_own (by simp [opsCoreOwnSpecTable]) bvBlastEqSpec_xfree

theorem opsCoreEnv_has_bv_blast_ult :
    opsCoreEnv.Has "bv_blast_ult" bvBlastUltSpec :=
  mem_own_has opsCoreEnv_sat_own (by simp [opsCoreOwnSpecTable]) bvBlastUltSpec_xfree

theorem opsCoreEnv_has_bv_blast_get_lsb_d :
    opsCoreEnv.Has "bv_blast_get_lsb_d" bvBlastGetLsbDSpec :=
  mem_own_has opsCoreEnv_sat_own (by simp [opsCoreOwnSpecTable]) bvBlastGetLsbDSpec_xfree

theorem opsCoreEnv_has_bv_mk_and :
    opsCoreEnv.Has "bv_mk_and" bvMkAndSpec :=
  mem_ext_has opsCoreEnv_sat_extern (by simp [opsCoreAigExternSpecs]) bvMkAndSpec_xfree

theorem opsCoreEnv_has_bv_aig_not :
    opsCoreEnv.Has "bv_aig_not" bvAigNotSpec :=
  mem_ext_has opsCoreEnv_sat_extern (by simp [opsCoreAigExternSpecs]) bvAigNotSpec_xfree

theorem opsCoreEnv_has_bv_aig_or :
    opsCoreEnv.Has "bv_aig_or" bvAigOrSpec :=
  mem_ext_has opsCoreEnv_sat_extern (by simp [opsCoreAigExternSpecs]) bvAigOrSpec_xfree

theorem opsCoreEnv_has_bv_aig_xor :
    opsCoreEnv.Has "bv_aig_xor" bvAigXorSpec :=
  mem_ext_has opsCoreEnv_sat_extern (by simp [opsCoreAigExternSpecs]) bvAigXorSpec_xfree

theorem opsCoreEnv_has_bv_aig_beq :
    opsCoreEnv.Has "bv_aig_beq" bvAigBeqSpec :=
  mem_ext_has opsCoreEnv_sat_extern (by simp [opsCoreAigExternSpecs]) bvAigBeqSpec_xfree

theorem opsCoreEnv_has_bv_lits_alloc :
    opsCoreEnv.Has "bv_lits_alloc" bvLitsAllocSpec :=
  mem_ext_has opsCoreEnv_sat_extern (by simp [opsCoreAigExternSpecs]) bvLitsAllocSpec_xfree

/-! ## `SegCert`, `TableImpl`, and `ModuleOk` Certificates -/

theorem opsCore_segCert :
    SegCert opsCoreAigExternSpecs opsCoreFns opsCoreOwnSpecTable := by
  intro Γ hExt hOwn
  have hMkAnd : Γ.Has "bv_mk_and" bvMkAndSpec :=
    mem_ext_has hExt (by simp [opsCoreAigExternSpecs]) bvMkAndSpec_xfree
  have hAigNot : Γ.Has "bv_aig_not" bvAigNotSpec :=
    mem_ext_has hExt (by simp [opsCoreAigExternSpecs]) bvAigNotSpec_xfree
  have hAigOr : Γ.Has "bv_aig_or" bvAigOrSpec :=
    mem_ext_has hExt (by simp [opsCoreAigExternSpecs]) bvAigOrSpec_xfree
  have hAigXor : Γ.Has "bv_aig_xor" bvAigXorSpec :=
    mem_ext_has hExt (by simp [opsCoreAigExternSpecs]) bvAigXorSpec_xfree
  have hAigBeq : Γ.Has "bv_aig_beq" bvAigBeqSpec :=
    mem_ext_has hExt (by simp [opsCoreAigExternSpecs]) bvAigBeqSpec_xfree
  have hLitsAlloc : Γ.Has "bv_lits_alloc" bvLitsAllocSpec :=
    mem_ext_has hExt (by simp [opsCoreAigExternSpecs]) bvLitsAllocSpec_xfree
  have hSliceOk : Γ.Has "bv_slice_ok" bvSliceOkSpec :=
    mem_own_has hOwn (by simp [opsCoreOwnSpecTable]) bvSliceOkSpec_xfree
  have hBinBitwise : Γ.Has "bv_blast_bin_bitwise" bvBlastBinBitwiseSpec :=
    mem_own_has hOwn (by simp [opsCoreOwnSpecTable]) bvBlastBinBitwiseSpec_xfree
  have hFac : Γ.Has "bv_full_adder_carry" bvFullAdderCarrySpec :=
    mem_own_has hOwn (by simp [opsCoreOwnSpecTable]) bvFullAdderCarrySpec_xfree
  simp only [TableImpl, opsCoreFns, ops_core_fns, opsCoreOwnSpecTable]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, bv_slice_ok_wp Γ⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, bv_blast_extract_wp Γ hSliceOk hLitsAlloc⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, bv_blast_append_wp Γ hSliceOk hLitsAlloc⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, bv_blast_not_wp Γ hSliceOk hLitsAlloc hAigNot⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, bv_blast_bin_bitwise_wp Γ hSliceOk hLitsAlloc hMkAnd hAigOr hAigXor⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, bv_blast_and_wp Γ hBinBitwise⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, bv_blast_or_wp Γ hBinBitwise⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, bv_blast_xor_wp Γ hBinBitwise⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, bv_full_adder_carry_wp Γ hMkAnd hAigOr hAigXor⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, bv_blast_add_wp Γ hSliceOk hLitsAlloc hAigXor hFac⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, bv_blast_eq_wp Γ hSliceOk hMkAnd hAigBeq⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, bv_blast_ult_wp Γ hSliceOk hAigNot hFac⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, bv_blast_get_lsb_d_wp Γ hSliceOk⟩

theorem opsCore_tableImpl :
    TableImpl opsCoreEnv opsCoreFns opsCoreSpecTable := by
  have hseg := opsCore_segCert opsCoreEnv opsCoreEnv_sat_extern opsCoreEnv_sat_own
  simpa [TableImpl, opsCoreFns, ops_core_fns, opsCoreSpecTable, opsCoreOwnSpecTable] using hseg

theorem opsCore_allFns_wf : AllFns Fn.Wf opsCoreModule.fns := by
  simp only [AllFns, opsCoreModule, opsCoreFns, ops_core_fns]
  exact ⟨bv_slice_ok_wf, bv_blast_extract_wf, bv_blast_append_wf, bv_blast_not_wf,
    bv_blast_bin_bitwise_wf, bv_blast_and_wf, bv_blast_or_wf, bv_blast_xor_wf,
    bv_full_adder_carry_wf, bv_blast_add_wf, bv_blast_eq_wf, bv_blast_ult_wf,
    bv_blast_get_lsb_d_wf, trivial⟩

theorem opsCore_moduleOk : ModuleOk opsCoreEnv opsCoreModule :=
  Env.ofTable_moduleOk opsCore_checkAcyclic opsCore_allFns_wf opsCore_tableImpl

theorem opsCore_modEnv_moduleOk :
    ModuleOk (Env.ofModule opsCoreModule opsCoreEnv) opsCoreModule :=
  ModuleOk.ofModule opsCore_moduleOk

end

end LeanQbe.T.Examples.Bitblast.Proof
