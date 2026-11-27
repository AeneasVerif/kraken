/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Main
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Module
public import LeanQbe.T.MainCertProof
public import LeanQbe.T.Examples.Kissat.Plain
public import LeanQbe.T.Examples.Kissat.PlainSpec
public import LeanQbe.T.Examples.Kissat.PlainLemmas
public import LeanQbe.T.Examples.Bitblast.Ref.BVProg
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
public import LeanQbe.T.Examples.Bitblast.Src.Full
public import LeanQbe.T.Examples.Bitblast.Proof.Specs
public import LeanQbe.T.Examples.Bitblast.Proof.Full
public import LeanQbe.T.Examples.Bitblast.Build.Flat
import LeanQbe.T.Examples.Bitblast.Proof.Driver
import LeanQbe.T.Examples.LratBytesDimacsLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Shared Arch-Free Linked Proof Bridge for `Bitblast` + `KissatPlain` (`BitblastCertCommon`)

Composes the `59`-function `Kissat.Plain.plainModule` (`plainEnv_moduleOk`) with the `64`-function
`Bitblast` core (`bitblast_moduleOk`) into the closed `123`-function `bitblastLinkedMod` (`0`
externs, `0` exits) and `bitblastLinkedEnv` (`<= std3` axioms, arch-free), plus concrete `0x1000#64`
`nvProgBytes` slab witnesses fitting `x64Init` / `armInit` (`4148 ≤ 8192` bytes).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.BitblastCertCommon

open Std Std.Sat Std.ExtHashMap Std.Tactic.BVDecide
open LeanQbe.T LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.Plain
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Ref.BVProg
open LeanQbe.T.Examples.Bitblast.Src.Full
open LeanQbe.T.Examples.Bitblast.Proof
open LeanQbe.T.Examples.Bitblast.Build
open Kraken.Bedrock2.Test

private def kissatExternEntry : SpecEntry :=
  ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], kissatSolveBytesUnsatSpec, true⟩

private theorem ofTable_mem_of_nodup {tbl : List SpecEntry} {e : SpecEntry}
    (he : e ∈ tbl) (hnd : (tbl.map SpecEntry.name).Nodup)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost}
    (h : Env.ofTable tbl e.name e.as e.rs xs m Q X) : e.eff xs m Q X := by
  induction tbl with
  | nil => nomatch he
  | cons e' es ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp he with rfl | hmem
    · exact (Env.ofTable_cons_self _ _ _ _ _ _).mp h
    · have hne : e'.name ≠ e.name := fun h' => hnd.1 (h' ▸ List.mem_map_of_mem hmem)
      exact ih hmem hnd.2 ((Env.ofTable_cons_ne hne _ _ _ _).mp h)

/-- Refinement from Bitblast's UNSAT-only `kissat_solve_bytes` extern contract to Kissat `Plain`'s
proved `plainSolveBytesSpec`. -/
theorem kissatSolveBytesUnsatSpec_refines_plain
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : kissatSolveBytesUnsatSpec xs m Q X) : plainSolveBytesSpec xs m Q X := by
  rcases xs with ⟨cnfPtr, cnfLen, workPtr, workCap, fuel, ⟨⟩⟩
  obtain ⟨cnfBytes, R, hcl, hcfit, hwfit, hm, hQ⟩ := h
  refine ⟨cnfBytes, workCap.toNat, R, ?_, ?_, hcfit, hwfit, hm,
    fun r m' _ hu _ hm' => hQ r m' hm' hu⟩
  · apply BitVec.eq_of_toNat_eq
    rw [hcl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · exact BitVec.eq_of_toNat_eq (by simp)

/-- Closed `123`-function linked `Module` (`plainModule.fns ++ bitblastModule.fns`, `0` externs, `0`
exits). -/
@[expose] def bitblastLinkedMod : Module :=
  { fns := plainModule.fns ++ bitblastModule.fns, externs := [], exits := [] }

theorem bitblastLinkedMod_fns_eq :
    bitblastLinkedMod.fns = plainModule.fns ++ bitblastModule.fns := rfl

theorem bitblastLinkedMod_fns_flat_eq :
    bitblastLinkedMod.fns = plainModule.fns ++ bitblastFlatMod.fns :=
  congrArg (plainModule.fns ++ ·) bitblastFlatMod_fns_eq.symm

theorem bitblastLinkedMod_checkAcyclic : bitblastLinkedMod.checkAcyclic = true := by
  t_kernel_rfl

theorem bitblastLinkedMod_wf : ∀ f ∈ bitblastLinkedMod.fns, f.Wf := fun f hf =>
  (List.mem_append.mp hf).elim (fun h => plainFns_wf f h) (fun h => bitblastModule_wf f h)

private theorem plain_bitblast_names_disj :
    ∀ s ∈ plainFns.map Fn.name, s ∉ bitblastFns.map Fn.name := by
  have hall :
      (plainFns.map Fn.name).all (fun s => !decide (s ∈ bitblastFns.map Fn.name)) = true := by
    decide
  intro s hs hmem
  have hm := List.all_eq_true.mp hall s hs
  simp [hmem] at hm

private theorem plain_bitblast_sig_disj {f : Sym} {as bs : List Ty}
    (hp : (f, as, bs) ∈ plainModule.sigs)
    (hb : (f, as, bs) ∈ bitblastModule.fns.map Fn.sig) : False := by
  have h1 : f ∈ plainFns.map Fn.name := by
    simp only [Module.sigs, plainModule, List.map_nil, List.append_nil, List.mem_map] at hp
    obtain ⟨fn, hfn, he⟩ := hp
    exact List.mem_map.mpr ⟨fn, hfn, congrArg Prod.fst he⟩
  have h2 : f ∈ bitblastFns.map Fn.name := by
    obtain ⟨fn, hfn, he⟩ := List.mem_map.mp hb
    exact List.mem_map.mpr ⟨fn, hfn, congrArg Prod.fst he⟩
  exact plain_bitblast_names_disj f h1 h2

/-- Disjoint union of `plainEnv` (`59` Kissat functions) and `bitblastEnv` (`64` Bitblast
functions). -/
@[expose] def bitblastLinkedEnv : Env :=
  fun f as bs xs m Q X =>
    ((f, as, bs) ∈ plainModule.sigs ∧ plainEnv f as bs xs m Q X) ∨
    ((f, as, bs) ∈ bitblastModule.fns.map Fn.sig ∧ bitblastEnv f as bs xs m Q X)

theorem bitblastLinkedEnv_noExit (f : Sym) (as bs : List Ty) (xs : Tup Val as)
    (m : Mem 64) (Q : Post bs) (X X' : XPost)
    (h : bitblastLinkedEnv f as bs xs m Q X) :
    bitblastLinkedEnv f as bs xs m Q X' :=
  h.elim (fun ⟨hm, hG⟩ => Or.inl ⟨hm, plainEnv_noExit f as bs xs m Q X X' hG⟩)
    (fun ⟨hm, hG⟩ => Or.inr ⟨hm, bitblastEnv_noExit f as bs xs m Q X X' hG⟩)

private theorem kissat_sig_mem_plain :
    ("kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64]) ∈ plainModule.sigs := by
  rw [Module.sigs]; decide

/-- All `123` functions in `bitblastLinkedMod` satisfy their `bitblastLinkedEnv` contracts under
`bitblastLinkedEnv` (`0` external calls unresolved). -/
theorem bitblastLinkedEnv_sound :
    ∀ fn ∈ bitblastLinkedMod.fns, ∀ xs m Q X,
      bitblastLinkedEnv fn.name fn.as fn.rs xs m Q X →
      Func.wp bitblastLinkedEnv fn.body xs m Q X := by
  intro fn hfn xs m Q X hs
  rcases List.mem_append.mp hfn with hplain | hbb
  · obtain ⟨p1, p2, hp⟩ := List.mem_iff_append.mp hplain
    have hsig : fn.sig ∈ plainModule.sigs := by
      rw [Module.sigs, hp, List.map_append]
      exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
    have hsp : plainEnv fn.name fn.as fn.rs xs m Q X :=
      hs.elim And.right (fun ⟨hb, _⟩ => absurd hb (fun hb' => plain_bitblast_sig_disj hsig hb'))
    have hwp := plainEnv_moduleOk.wp_restrict hp hsp
    have hwf := (plainEnv_moduleOk.fnsOk p1 fn p2 hp).1
    have hcalls := (plainEnv_moduleOk.fnsOk p1 fn p2 hp).2.1
    refine wp_env_agree_of_callsOk
      (hwf Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units fn.as))
      hcalls (fun g as bs hg ys m' P E hG => ?_) m hwp
    have hgsig : (g, as, bs) ∈ plainModule.sigs := by
      simp only [plainModule, List.map_nil, List.append_nil] at hg
      rw [Module.sigs, hp, List.map_append]
      exact List.mem_append_left _ (List.mem_append_left _ hg)
    exact Or.inl ⟨hgsig, hG.2⟩
  · obtain ⟨b1, b2, hb⟩ := List.mem_iff_append.mp hbb
    have hsig : fn.sig ∈ bitblastModule.fns.map Fn.sig := by
      rw [hb, List.map_append]
      exact List.mem_append_right _ List.mem_cons_self
    have hsb : bitblastEnv fn.name fn.as fn.rs xs m Q X :=
      hs.elim (fun ⟨hp, _⟩ => absurd hsig (fun hb' => plain_bitblast_sig_disj hp hb')) And.right
    have hwp := bitblast_moduleOk.wp_restrict hb hsb
    have hwf := (bitblast_moduleOk.fnsOk b1 fn b2 hb).1
    have hcalls := (bitblast_moduleOk.fnsOk b1 fn b2 hb).2.1
    refine wp_env_agree_of_callsOk
      (hwf Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units fn.as))
      hcalls (fun g as bs hg ys m' P E hG => ?_) m hwp
    rcases List.mem_append.mp hg with hg1 | hgext
    · have hgsig : (g, as, bs) ∈ bitblastModule.fns.map Fn.sig := by
        rw [hb, List.map_append]
        exact List.mem_append_left _ hg1
      exact Or.inr ⟨hgsig, hG.2⟩
    · simp only [bitblastModule, bitblastExterns, List.map_cons,
        List.map_nil, Extern.sig, List.mem_cons, List.not_mem_nil, or_false] at hgext
      rcases hgext with ⟨rfl, rfl, rfl⟩
      have hk : kissatExternEntry.eff ys m' P E :=
        ofTable_mem_of_nodup (tbl := bitblastSpecTable) (e := kissatExternEntry)
          (by simp [kissatExternEntry, bitblastSpecTable]) bitblastSpecTable_nodup hG.2
      have hplainSpec := kissatSolveBytesUnsatSpec_refines_plain (X := E) hk
      exact Or.inl ⟨kissat_sig_mem_plain,
        mkPlainEnv_solve_bytes plainSolveBytesSpec (fun _ _ _ _ h => h) ys m' P E hplainSpec⟩

/-- Complete closed `123`-function `ModuleOk` theorem composing `Kissat.Plain` (`59` fns) and
`Bitblast` (`64` fns). -/
theorem bitblastLinkedEnv_moduleOk : ModuleOk bitblastLinkedEnv bitblastLinkedMod :=
  Module.moduleOk_of_checkAcyclic bitblastLinkedMod_checkAcyclic
    bitblastLinkedMod_wf bitblastLinkedEnv_sound

/-- `bv_solve_bytes` satisfies `bvSolveBytesSpec` inside `bitblastLinkedEnv`. -/
theorem bitblastLinked_bvSolveBytesSpec
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : bvSolveBytesSpec xs m Q X) :
    bitblastLinkedEnv "bv_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X := by
  have hsig : ("bv_solve_bytes", [i64, i64, i64, i64, i64], [i64]) ∈
      bitblastModule.fns.map Fn.sig := by
    decide
  refine Or.inr ⟨hsig, ?_⟩
  exact bitblastEnv_row_at 63
    ⟨"bv_solve_bytes", [i64, i64, i64, i64, i64], [i64], bvSolveBytesSpec, true⟩
    (by rfl) (fun _ _ _ _ hs => hs) xs m Q X h

/-! ## Concrete `0x1000#64` Non-Vacuity Slab (`4148 ≤ 8192` bytes) -/

@[expose] def nvSlabPtr : BitVec 64 := 0x1000#64

@[expose] def nvSlabWorkPtr : BitVec 64 := 0x1034#64

@[expose] def nvSlabBytes : List UInt8 :=
  nvProgBytes ++ List.replicate 0x1000 (0 : UInt8)

theorem nvSlabBytes_length : nvSlabBytes.length = 4148 := by
  rw [nvSlabBytes, List.length_append, List.length_replicate]
  decide

theorem nvSlabBytes_le_8192 : nvSlabBytes.length ≤ 8192 := by
  rw [nvSlabBytes_length]; decide

theorem nvSlab_trivialUnsat :
    bvSolveTrivialUnsatCond nvSlabPtr nvProgBytes nvSlabWorkPtr nvWorkCap nvFuel := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    nvProgBytes_valid, ⟨by decide, by decide⟩, ?_, by decide⟩
  intro i hi
  have h3 : u32At nvProgBytes 3 = 1 := by decide
  have hi0 : i = 0 := by omega
  subst hi0
  decide

theorem nvSlab_sep :
    (bytes nvSlabPtr nvProgBytes ⋆ region nvSlabWorkPtr nvWorkCap.toNat ⋆
      (ExtHashMap.emp : Mem 64 → Prop)) (nvSlabBytes.At nvSlabPtr) := by
  have hl_p : nvProgBytes.length = 52 := rfl
  have hl_rep : (List.replicate 0x1000 (0 : UInt8)).length = 0x1000 := List.length_replicate
  have hlen : nvProgBytes.length + (List.replicate 0x1000 (0 : UInt8)).length ≤ 2 ^ 64 := by
    rw [hl_p, hl_rep]; decide
  have hsep := Mem.At_append_sep nvProgBytes (List.replicate 0x1000 (0 : UInt8)) nvSlabPtr hlen
  have hself : Eq (nvSlabBytes.At nvSlabPtr) (nvSlabBytes.At nvSlabPtr) := rfl
  have hadr : nvSlabPtr + BitVec.ofNat 64 nvProgBytes.length = nvSlabWorkPtr := by
    rw [hl_p]; rfl
  rw [show nvSlabBytes = nvProgBytes ++ List.replicate 0x1000 (0 : UInt8) from rfl,
    hsep, hadr] at hself
  have h1 : (bytes nvSlabPtr nvProgBytes ⋆ region nvSlabWorkPtr nvWorkCap.toNat)
      (nvSlabBytes.At nvSlabPtr) := by
    rw [sep_comm] at hself ⊢
    exact sep_mono (P := Eq ((List.replicate 0x1000 (0 : UInt8)).At nvSlabWorkPtr))
      (fun _ h => ⟨List.replicate 0x1000 (0 : UInt8), hl_rep, h.symm⟩) hself
  simpa [Std.ExtHashMap.sep_emp] using h1

/-- Concrete `bvSolveBytesSpec` instance for `nvProgBytes` (`BCONST false`) in `0x1000#64`
slab layout compatible with `x64Init` / `armInit`. -/
theorem nvSlab_bvSolveBytesSpec (Q : Post [i64]) (X : XPost)
    (hQ : ∀ m',
      (bytes nvSlabPtr nvProgBytes ⋆ region nvSlabWorkPtr nvWorkCap.toNat ⋆
        (ExtHashMap.emp : Mem 64 → Prop)) m' →
      (∀ prog : BVLogicalExpr, BVProg.parse nvProgBytes = some prog → prog.Unsat) →
      Q (20#64, ⟨⟩) m') :
    bvSolveBytesSpec (nvSlabPtr, nvProgLen, nvSlabWorkPtr, nvWorkCap, nvFuel, ⟨⟩)
      (nvSlabBytes.At nvSlabPtr) Q X :=
  ⟨nvProgBytes, ExtHashMap.emp, rfl, nvSlab_sep, fun r m' hm' hunsat htriv => by
    have hr : r = 20#64 := htriv nvSlab_trivialUnsat
    subst hr
    exact hQ m' hm' (hunsat rfl)⟩

end LeanQbeTest.T.BitblastCertCommon
