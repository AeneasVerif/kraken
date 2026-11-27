/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertInlineProof
public import LeanQbe.T.Examples.Kissat.KissatCertCommon
public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12Proof
public import LeanQbe.T.Examples.Bitblast.Ref.BVProg
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
public import LeanQbe.T.Examples.Bitblast.Src.Full
public import LeanQbe.T.Examples.Bitblast.Proof.Specs
public import LeanQbe.T.Examples.Bitblast.Proof.Full
import Kraken.Mem
import Kraken.Separation

/-!
# Parametric Arch-Free `Bitblast` + `KissatUnsatPkg` Linked Bridge (`FullFidelityBitblastLemmas`)

Composes ANY closed `P : KissatUnsatPkg` (e.g. `FullFidelityAssemblyStep12.fidStep12UnsatPkg`,
`517` fns, or future Step-13 `fidStep13UnsatPkg` in 1 line!) with the `64`-function `Bitblast`
module (`bitblast_moduleOk`) into:
1. `bitblastLinkedModOfPkg P` (`P.mod.fns ++ bitblastModule.fns`, `0` externs, `0` exits) and
   `bitblastInlLinkedModOfPkg P` (`(P.mod.optInlinePolicy P.inlPolicy).fns ++ bitblastModule.fns`,
   matching zero-recomp `fidCert.append bitblastTailCert` and `bv_decide_qbe` assembly emission!).
2. `bitblastLinkedEnvOfPkg P`, `bitblastLinkedEnv_moduleOk`, `bitblastInlLinkedEnv_moduleOk`, and
   `bitblastLinked_bvSolveBytesSpec` (`<= std3`, arch-free).
3. Concrete `FullFidelityAssemblyStep12.fidStep12UnsatPkg` instantiation (`517 + 64 = 581` fns,
   `0` name collisions, `checkAcyclic = true`, `<= std3`).
4. Arch-agnostic `ArchKissatAbi` machine-code soundness & non-vacuity combinators over raw
   `compileModuleOptInlinePolicy`, raw `compileModule` on `bitblastInlLinkedModOfPkg`, and
   `LinkedCert` (`<= std3`, zero `*Cert*`/`*Inl*` imports).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBitblastLemmas

open Std Std.Sat Std.ExtHashMap Std.Tactic.BVDecide
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.KissatCertCommon
open LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12
open LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Ref.BVProg
open LeanQbe.T.Examples.Bitblast.Src.Full
open LeanQbe.T.Examples.Bitblast.Proof
open Kraken Kraken.Bedrock2.Test

/-! ## 1. Parametric `Bitblast` + `KissatUnsatPkg` Linked Module & `ModuleOk` -/

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

/-- Refinement from Bitblast's UNSAT-only `kissat_solve_bytes` extern contract to ANY
`P : KissatUnsatPkg`'s `P.solve_intro`. -/
theorem kissatSolveBytesUnsatSpec_refines_pkg (P : KissatUnsatPkg)
    (hEntry : P.entryFn = "kissat_solve_bytes")
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : kissatSolveBytesUnsatSpec xs m Q X) :
    P.env "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X := by
  rcases xs with ⟨cnfPtr, cnfLen, workPtr, workCap, fuel, ⟨⟩⟩
  obtain ⟨cnfBytes, R, hcl, hcfit, hwfit, hm, hQ⟩ := h
  have hcl' : BitVec.ofNat 64 cnfBytes.length = cnfLen := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hcl]
  have hw' : BitVec.ofNat 64 workCap.toNat = workCap := BitVec.eq_of_toNat_eq (by simp)
  rw [← hEntry, ← hcl', ← hw']
  exact P.solve_intro hcfit hwfit hm (fun r m' _ hu _ hm' => hQ r m' hm' hu)

/-- Un-inlined closed linked `Module` composing `P.mod.fns` and `bitblastModule.fns`
(`0` externs, `0` exits). -/
@[expose] def bitblastLinkedModOfPkg (P : KissatUnsatPkg) : Module :=
  { fns := P.mod.fns ++ bitblastModule.fns, externs := [], exits := [] }

/-- PGO-inlined-Kissat + Bitblast closed linked `Module`
(`(P.mod.optInlinePolicy P.inlPolicy).fns ++ bitblastModule.fns`, `0` externs, `0` exits).
Matches both `bv_decide_qbe` assembly emission and zero-recomp `fidCert.append bitblastTailCert`. -/
@[expose] def bitblastInlLinkedModOfPkg (P : KissatUnsatPkg) : Module :=
  { fns := (P.mod.optInlinePolicy P.inlPolicy).fns ++ bitblastModule.fns,
    externs := [], exits := [] }

/-- Disjoint union of `P.env` and `bitblastEnv` keyed on function signatures. -/
@[expose] def bitblastLinkedEnvOfPkg (P : KissatUnsatPkg) : Env :=
  fun f as bs xs m Q X =>
    ((f, as, bs) ∈ P.mod.fns.map Fn.sig ∧ P.env f as bs xs m Q X) ∨
    ((f, as, bs) ∈ bitblastModule.fns.map Fn.sig ∧ bitblastEnv f as bs xs m Q X)

theorem bitblastLinkedEnv_noExit (P : KissatUnsatPkg)
    (f : Sym) (as bs : List Ty) (xs : Tup Val as)
    (m : Mem 64) (Q : Post bs) (X X' : XPost)
    (h : bitblastLinkedEnvOfPkg P f as bs xs m Q X) :
    bitblastLinkedEnvOfPkg P f as bs xs m Q X' := by
  rcases h with ⟨hsig, hG⟩ | ⟨hsig, hG⟩
  · obtain ⟨fn, hfn, hfnSig⟩ := List.mem_map.mp hsig
    simp only [Fn.sig, Prod.mk.injEq] at hfnSig
    rcases hfnSig with ⟨rfl, rfl, rfl⟩
    exact Or.inl ⟨hsig, P.noExit fn hfn xs m Q X X' hG⟩
  · exact Or.inr ⟨hsig, bitblastEnv_noExit f as bs xs m Q X X' hG⟩

private theorem sig_disj_of_name_disj {fs₁ fs₂ : List Fn}
    (hDisj : ∀ s ∈ fs₁.map Fn.name, s ∉ fs₂.map Fn.name)
    {f : Sym} {as bs : List Ty}
    (h1 : (f, as, bs) ∈ fs₁.map Fn.sig) (h2 : (f, as, bs) ∈ fs₂.map Fn.sig) : False := by
  obtain ⟨fn1, hfn1, he1⟩ := List.mem_map.mp h1
  obtain ⟨fn2, hfn2, he2⟩ := List.mem_map.mp h2
  exact hDisj f (List.mem_map.mpr ⟨fn1, hfn1, congrArg Prod.fst he1⟩)
    (List.mem_map.mpr ⟨fn2, hfn2, congrArg Prod.fst he2⟩)

private theorem split_append_elem {α : Type _} :
    ∀ {xs ys pre post : List α} {a : α},
      xs ++ ys = pre ++ a :: post →
      (∃ post₁, xs = pre ++ a :: post₁ ∧ post = post₁ ++ ys) ∨
      (∃ pre₂, ys = pre₂ ++ a :: post ∧ pre = xs ++ pre₂)
  | [], _, pre, post, a, h => Or.inr ⟨pre, h, rfl⟩
  | x :: xs, ys, [], post, a, h => by
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact Or.inl ⟨xs, by rw [h.1]; rfl, h.2.symm⟩
  | x :: xs, ys, p :: pre, post, a, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    rcases split_append_elem h.2 with ⟨post₁, hxs, hpost⟩ | ⟨pre₂, hys, hpre⟩
    · exact Or.inl ⟨post₁, by rw [h.1, hxs]; rfl, hpost⟩
    · exact Or.inr ⟨pre₂, hys, by rw [h.1, hpre]; rfl⟩

mutual
private theorem expr_callsOk_mono {s₁ s₂ : List SigEntry} {ex : List Sym}
    (hsub : ∀ x ∈ s₁, x ∈ s₂) {rs : List Ty} :
    (e : Expr (fun _ => Unit) (fun _ => Unit) rs) →
    Expr.callsOk s₁ ex e → Expr.callsOk s₂ ex e
  | .let_ _ k, hc => expr_callsOk_mono hsub (k (Tup.units _)) hc
  | .load _ _ k, hc => expr_callsOk_mono hsub (k ()) hc
  | .store _ _ k, hc => expr_callsOk_mono hsub k hc
  | .call _ _ k, hc => ⟨hsub _ hc.1, expr_callsOk_mono hsub (k (Tup.units _)) hc.2⟩
  | .jnz _ t e, hc => ⟨expr_callsOk_mono hsub t hc.1, expr_callsOk_mono hsub e hc.2⟩
  | .jump _ _, _ | .ret _, _ | .hlt, _ => trivial
  | .exit _ _, hc => hc
  | .group bodies k, hc =>
    ⟨blocks_callsOk_mono hsub (bodies (Tup.units _)) hc.1,
     expr_callsOk_mono hsub (k (Tup.units _)) hc.2⟩

private theorem blocks_callsOk_mono {s₁ s₂ : List SigEntry} {ex : List Sym}
    (hsub : ∀ x ∈ s₁, x ∈ s₂) {rs : List Ty} :
    {sig : List (List Ty)} → (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig) →
    Blocks.callsOk s₁ ex bs → Blocks.callsOk s₂ ex bs
  | _, .nil, _ => trivial
  | _, .cons b bs, hc =>
    ⟨expr_callsOk_mono hsub (b (Tup.units _)) hc.1, blocks_callsOk_mono hsub bs hc.2⟩
end

private theorem fn_callsOk_mono {f : Fn} {s₁ s₂ : List SigEntry} {ex : List Sym}
    (hsub : ∀ x ∈ s₁, x ∈ s₂) (hc : f.callsOk s₁ ex) : f.callsOk s₂ ex :=
  expr_callsOk_mono hsub _ hc

private theorem moduleOk_link_bitblast (P : KissatUnsatPkg) (M₁ : Module)
    (hEntry : P.entryFn = "kissat_solve_bytes")
    (hExt : M₁.externs = []) (hEx : M₁.exits = [])
    (hSigsEq : M₁.fns.map Fn.sig = P.mod.fns.map Fn.sig)
    (hOk₁ : ModuleOk P.env M₁)
    (hDisj : ∀ s ∈ P.mod.fns.map Fn.name, s ∉ bitblastModule.fns.map Fn.name) :
    ModuleOk (bitblastLinkedEnvOfPkg P)
      { fns := M₁.fns ++ bitblastModule.fns, externs := [], exits := [] } := by
  have hNamesEq : M₁.fns.map Fn.name = P.mod.fns.map Fn.name := by
    have := congrArg (List.map Prod.fst) hSigsEq
    simpa [List.map_map, Function.comp_def, Fn.sig] using this
  have hDisj₁ : ∀ s ∈ M₁.fns.map Fn.name, s ∉ bitblastModule.fns.map Fn.name := by
    rw [hNamesEq]; exact hDisj
  have hNodupM₁ : (M₁.fns.map Fn.name).Nodup := (List.nodup_append.mp hOk₁.nodup).1
  have hNodupBB : (bitblastModule.fns.map Fn.name).Nodup :=
    (List.nodup_append.mp bitblast_moduleOk.nodup).1
  have hKissatSig : ("kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64]) ∈
      P.mod.fns.map Fn.sig := by
    refine List.mem_map.mpr ⟨P.entryFn_fn, P.entry_mem, ?_⟩
    rcases P.entryFn_sig with ⟨h1, h2, h3⟩
    simp [Fn.sig, h1, h2, h3, hEntry]
  refine ⟨?_, fun pre fn post hsplit => ?_⟩
  · change ((M₁.fns ++ bitblastModule.fns).map Fn.name ++ []).Nodup
    rw [List.append_nil, List.map_append, List.nodup_append]
    exact ⟨hNodupM₁, hNodupBB, fun s hs₁ t hs₂ heq => hDisj₁ s hs₁ (heq ▸ hs₂)⟩
  · dsimp only at hsplit
    rcases split_append_elem hsplit with ⟨post₁, hM₁, _⟩ | ⟨pre₂, hBB, rfl⟩
    · have hfnOk := hOk₁.fnsOk pre fn post₁ hM₁
      have hcalls : fn.callsOk (pre.map Fn.sig ++ []) [] := by
        simpa [hExt, hEx] using hfnOk.2.1
      have hsig : fn.sig ∈ P.mod.fns.map Fn.sig := by
        rw [← hSigsEq, hM₁, List.map_append]
        exact List.mem_append_right _ List.mem_cons_self
      refine ⟨hfnOk.1, by simpa using hcalls, fun xs m Q X hs => ?_⟩
      have hsp : P.env fn.name fn.as fn.rs xs m Q X :=
        hs.elim And.right (fun ⟨hb, _⟩ => absurd hb (sig_disj_of_name_disj hDisj hsig))
      have hwp := hOk₁.wp_restrict hM₁ hsp
      refine wp_env_agree_of_callsOk
        (hfnOk.1 Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units fn.as))
        hfnOk.2.1 (fun g as bs hg ys m' P' E hG => ?_) m hwp
      simp only [hExt, List.map_nil, List.append_nil] at hg
      have hgsig : (g, as, bs) ∈ P.mod.fns.map Fn.sig := by
        rw [← hSigsEq, hM₁, List.map_append]
        exact List.mem_append_left _ hg
      exact Or.inl ⟨hgsig, hG.2⟩
    · have hfnOk := bitblast_moduleOk.fnsOk pre₂ fn post hBB
      have hsig : fn.sig ∈ bitblastModule.fns.map Fn.sig := by
        rw [hBB, List.map_append]
        exact List.mem_append_right _ List.mem_cons_self
      have hcalls : fn.callsOk ((M₁.fns ++ pre₂).map Fn.sig ++ [].map Extern.sig) [] := by
        simp only [List.map_nil, List.append_nil, List.map_append]
        refine fn_callsOk_mono (fun s hs => ?_) (by simpa [bitblastModule] using hfnOk.2.1)
        rcases List.mem_append.mp hs with hs₁ | hsext
        · exact List.mem_append_right _ hs₁
        · simp only [bitblastExterns, List.map_cons, List.map_nil, Extern.sig,
            List.mem_cons, List.not_mem_nil, or_false] at hsext
          subst hsext
          exact List.mem_append_left _ (hSigsEq.symm ▸ hKissatSig)
      refine ⟨hfnOk.1, hcalls, fun xs m Q X hs => ?_⟩
      have hsb : bitblastEnv fn.name fn.as fn.rs xs m Q X :=
        hs.elim (fun ⟨hp, _⟩ => absurd hsig (sig_disj_of_name_disj hDisj hp)) And.right
      have hwp := bitblast_moduleOk.wp_restrict hBB hsb
      refine wp_env_agree_of_callsOk
        (hfnOk.1 Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units fn.as))
        hfnOk.2.1 (fun g as bs hg ys m' P' E hG => ?_) m hwp
      rcases List.mem_append.mp hg with hg₁ | hgext
      · have hgsig : (g, as, bs) ∈ bitblastModule.fns.map Fn.sig := by
          rw [hBB, List.map_append]
          exact List.mem_append_left _ hg₁
        exact Or.inr ⟨hgsig, hG.2⟩
      · simp only [bitblastModule, bitblastExterns, List.map_cons,
          List.map_nil, Extern.sig, List.mem_cons, List.not_mem_nil, or_false] at hgext
        rcases hgext with ⟨rfl, rfl, rfl⟩
        have hk : kissatExternEntry.eff ys m' P' E :=
          ofTable_mem_of_nodup (tbl := bitblastSpecTable) (e := kissatExternEntry)
            (by simp [kissatExternEntry, bitblastSpecTable]) bitblastSpecTable_nodup hG.2
        exact Or.inl ⟨hKissatSig, kissatSolveBytesUnsatSpec_refines_pkg P hEntry hk⟩

/-- Parametric closed `ModuleOk` for `bitblastLinkedModOfPkg P` (`P.mod.fns ++ bitblastModule.fns`,
`0` externs, `0` exits) over ANY `P : KissatUnsatPkg`. -/
theorem bitblastLinkedEnv_moduleOk (P : KissatUnsatPkg)
    (hEntry : P.entryFn = "kissat_solve_bytes")
    (hExt : P.mod.externs = []) (hEx : P.mod.exits = [])
    (hDisj : ∀ s ∈ P.mod.fns.map Fn.name, s ∉ bitblastModule.fns.map Fn.name) :
    ModuleOk (bitblastLinkedEnvOfPkg P) (bitblastLinkedModOfPkg P) :=
  moduleOk_link_bitblast P P.mod hEntry hExt hEx rfl P.moduleOk hDisj

/-- Parametric closed `ModuleOk` for `bitblastInlLinkedModOfPkg P`
(`(P.mod.optInlinePolicy P.inlPolicy).fns ++ bitblastModule.fns`, `0` externs, `0` exits)
over ANY `P : KissatUnsatPkg`. -/
theorem bitblastInlLinkedEnv_moduleOk (P : KissatUnsatPkg)
    (hEntry : P.entryFn = "kissat_solve_bytes")
    (hExt : P.mod.externs = []) (hEx : P.mod.exits = [])
    (hDisj : ∀ s ∈ P.mod.fns.map Fn.name, s ∉ bitblastModule.fns.map Fn.name) :
    ModuleOk (bitblastLinkedEnvOfPkg P) (bitblastInlLinkedModOfPkg P) := by
  have hSigs : (P.mod.optInlinePolicy P.inlPolicy).fns.map Fn.sig = P.mod.fns.map Fn.sig := by
    have h := Module.optInlinePolicy_sigs P.mod P.inlPolicy
    simp only [Module.sigs, Module.optInlinePolicy_externs] at h
    exact List.append_cancel_right h
  exact moduleOk_link_bitblast P (P.mod.optInlinePolicy P.inlPolicy) hEntry
    hExt hEx hSigs (Module.optInlinePolicy_ok P.inlPolicy P.moduleOk) hDisj

/-- `bv_solve_bytes` satisfies `bvSolveBytesSpec` inside `bitblastLinkedEnvOfPkg P`. -/
theorem bitblastLinked_bvSolveBytesSpec (P : KissatUnsatPkg)
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : bvSolveBytesSpec xs m Q X) :
    bitblastLinkedEnvOfPkg P "bv_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X := by
  have hsig : ("bv_solve_bytes", [i64, i64, i64, i64, i64], [i64]) ∈
      bitblastModule.fns.map Fn.sig := by
    decide
  refine Or.inr ⟨hsig, ?_⟩
  exact bitblastEnv_row_at 63
    ⟨"bv_solve_bytes", [i64, i64, i64, i64, i64], [i64], bvSolveBytesSpec, true⟩
    (by rfl) (fun _ _ _ _ hs => hs) xs m Q X h

theorem bvSolveBytesFn_mem_linked (P : KissatUnsatPkg) :
    bvSolveBytesFn ∈ (bitblastLinkedModOfPkg P).fns :=
  List.mem_append_right _
    (List.mem_of_getElem? (rfl : bitblastModule.fns[63]? = some bvSolveBytesFn))

theorem bvSolveBytesFn_mem_inlLinked (P : KissatUnsatPkg) :
    bvSolveBytesFn ∈ (bitblastInlLinkedModOfPkg P).fns :=
  List.mem_append_right _
    (List.mem_of_getElem? (rfl : bitblastModule.fns[63]? = some bvSolveBytesFn))

/-! ## 2. Concrete `0x1000#64` Non-Vacuity Slab (`4148 ≤ 8192` bytes) -/

@[expose] def nvSlabPtr : BitVec 64 := 0x1000#64
@[expose] def nvSlabWorkPtr : BitVec 64 := 0x1034#64
@[expose] def nvSlabBytes : List UInt8 := nvProgBytes ++ List.replicate 0x1000 (0 : UInt8)

theorem nvSlabBytes_length : nvSlabBytes.length = 4148 := by
  rw [nvSlabBytes, List.length_append, List.length_replicate]; decide

theorem nvSlabBytes_le_8192 : nvSlabBytes.length ≤ 8192 := by
  rw [nvSlabBytes_length]; decide

theorem nvSlab_trivialUnsat :
    bvSolveTrivialUnsatCond nvSlabPtr nvProgBytes nvSlabWorkPtr nvWorkCap nvFuel := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    nvProgBytes_valid, ⟨by decide, by decide⟩, ?_, by decide⟩
  intro i hi
  have h3 : u32At nvProgBytes 3 = 1 := by decide
  have hi0 : i = 0 := by omega
  subst hi0; decide

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
    subst hr; exact hQ m' hm' (hunsat rfl)⟩

/-! ## 3. Arch-Agnostic Machine-Code Soundness & Non-Vacuity Combinators (`ArchKissatAbi`) -/

private theorem fn_mem_eq_of_nodup :
    ∀ {fs : List Fn} {f₁ f₂ : Fn},
      (fs.map Fn.name).Nodup → f₁ ∈ fs → f₂ ∈ fs → f₁.name = f₂.name → f₁ = f₂
  | [], _, _, _, h1, _, _ => nomatch h1
  | _ :: _, f₁, f₂, hnd, h1, h2, hnm => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h1 with rfl | h1' <;> rcases List.mem_cons.mp h2 with rfl | h2'
    · rfl
    · exact absurd (hnm ▸ List.mem_map_of_mem h2') hnd.1
    · exact absurd (hnm.symm ▸ List.mem_map_of_mem h1') hnd.1
    · exact fn_mem_eq_of_nodup hnd.2 h1' h2' hnm

/-- Lift `A.T.FnSpec` for `bv_solve_bytes` to end-to-end machine-code UNSAT soundness. -/
theorem bv_solve_bytes_unsat_of_fnspec (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (hh : A.T.mach.Host) {b : Nat}
    (hfn : A.T.FnSpec hh "bv_solve_bytes"
      (bitblastLinkedEnvOfPkg P "bv_solve_bytes" [i64, i64, i64, i64, i64] [i64]) b 0)
    (progPtr progLen workPtr workCap fuel : BitVec 64)
    (progBytes : List UInt8) (m : Mem 64) (Rm R : Mem 64 → Prop)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr)
    (hplen : progLen.toNat = progBytes.length)
    (hm : (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m)
    (hargs : A.args5Ok s progPtr progLen workPtr workCap fuel)
    (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆ Eq m ⋆ A.entryFrame s ra b ⋆ R)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        A.calleeSpOk s (A.T.mach.data st) ∧
        ∃ m',
          (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m' ∧
          (A.retGpr (A.T.mach.data st) = 20#64 →
            ∀ prog : BVLogicalExpr, BVProg.parse progBytes = some prog → prog.Unsat) ∧
          (bvSolveTrivialUnsatCond progPtr progBytes workPtr workCap fuel →
            A.retGpr (A.T.mach.data st) = 20#64) ∧
          (A.T.mach.mem (A.T.mach.data st) =⋆ Eq m' ⋆ A.exitFrame s b ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh "bv_solve_bytes")) := by
  let Q : Post [i64] := fun (r, ()) m' =>
    (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m' ∧
    (r = 20#64 → ∀ prog : BVLogicalExpr, BVProg.parse progBytes = some prog → prog.Unsat) ∧
    (bvSolveTrivialUnsatCond progPtr progBytes workPtr workCap fuel → r = 20#64)
  have hspec := bitblastLinked_bvSolveBytesSpec P
    (xs := (progPtr, progLen, workPtr, workCap, fuel, ())) (m := m) (Q := Q)
    (X := fun _ _ _ _ => False)
    ⟨progBytes, Rm, hplen, hm, fun r m' hm' hunsat htriv => ⟨hm', hunsat, htriv⟩⟩
  refine eventually_weaken _ _ _ _ ?_
    (solve_of_abi_fnspec A hh "bv_solve_bytes" hfn progPtr progLen workPtr workCap fuel
      hspec s ra R hargs hsp hmem)
  rintro st ⟨hpc, hcal, m', ⟨hm', hunsat, htriv⟩, hst⟩
  exact ⟨hpc, hcal, m', hm', hunsat, htriv, hst⟩

/-- Machine-code UNSAT soundness over raw `compileModuleOptInlinePolicy` on
`bitblastLinkedModOfPkg P` for ANY `policy : InlinePolicy`. -/
theorem bv_solve_bytes_unsat_of_compile_optInline (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (hEntry : P.entryFn = "kissat_solve_bytes")
    (hExt : P.mod.externs = []) (hEx : P.mod.exits = [])
    (hDisj : ∀ s ∈ P.mod.fns.map Fn.name, s ∉ bitblastModule.fns.map Fn.name)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (policy : InlinePolicy)
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModuleOptInlinePolicy A.T.toIsa A.lt A.T.frame.raBytes [] [] 0
      (bitblastLinkedModOfPkg P) hints policy = .ok (code, bounds))
    {b : Nat} (hb : ("bv_solve_bytes", b) ∈ bounds)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (progPtr progLen workPtr workCap fuel : BitVec 64)
    (progBytes : List UInt8) (m : Mem 64) (Rm R : Mem 64 → Prop)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr)
    (hplen : progLen.toNat = progBytes.length)
    (hm : (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m)
    (hargs : A.args5Ok s progPtr progLen workPtr workCap fuel)
    (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆ Eq m ⋆ A.entryFrame s ra b ⋆ R)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        A.calleeSpOk s (A.T.mach.data st) ∧
        ∃ m',
          (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m' ∧
          (A.retGpr (A.T.mach.data st) = 20#64 →
            ∀ prog : BVLogicalExpr, BVProg.parse progBytes = some prog → prog.Unsat) ∧
          (bvSolveTrivialUnsatCond progPtr progBytes workPtr workCap fuel →
            A.retGpr (A.T.mach.data st) = 20#64) ∧
          (A.T.mach.mem (A.T.mach.data st) =⋆ Eq m' ⋆ A.exitFrame s b ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh "bv_solve_bytes")) := by
  have hM := bitblastLinkedEnv_moduleOk P hEntry hExt hEx hDisj
  have ⟨hacyc, hwf, hwp⟩ := moduleOk_parts hM
  have hsupp := Compiled.compileModule_supportsSource hcm
  have hnd : ((bitblastLinkedModOfPkg P).fns.map Fn.name).Nodup :=
    (List.nodup_append.mp hM.nodup).1
  obtain ⟨f', hf', hnm, _, hspec⟩ :=
    compile_sound_optInlinePolicy A.T hh A.lt (bitblastLinkedModOfPkg P)
      (bitblastLinkedEnvOfPkg P) [] [] 0 policy hints code bounds k₀ hcm hc hu hacyc hwf hsupp hwp
      (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
      (fun _ h => nomatch h) ("bv_solve_bytes", b) hb
  have heqf : f' = bvSolveBytesFn :=
    fn_mem_eq_of_nodup hnd hf' (bvSolveBytesFn_mem_linked P) hnm.symm
  subst heqf
  have hfn := fnSpec_of_legalEnv_legalSig_eq_noExit has hrs
    (List.mem_append_left _ (List.mem_map_of_mem (bvSolveBytesFn_mem_linked P)))
    (fun args m Q X X' h => bitblastLinkedEnv_noExit P _ _ _ args m Q X X' h) hspec
  exact bv_solve_bytes_unsat_of_fnspec A P hh hfn progPtr progLen workPtr workCap fuel
    progBytes m Rm R s ra hplen hm hargs hsp hmem

/-- Machine-code UNSAT soundness over raw `compileModule` on `bitblastInlLinkedModOfPkg P`
(`(P.mod.optInlinePolicy P.inlPolicy).fns ++ bitblastModule.fns` — `bv_decide_qbe` assembly). -/
theorem bv_solve_bytes_unsat_of_compile_inl (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (hEntry : P.entryFn = "kissat_solve_bytes")
    (hExt : P.mod.externs = []) (hEx : P.mod.exits = [])
    (hDisj : ∀ s ∈ P.mod.fns.map Fn.name, s ∉ bitblastModule.fns.map Fn.name)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (hints : List A.T.toIsa.Hints) (code : List A.T.Directive) (bounds : List (Sym × Nat))
    (hcm : compileModule A.T.toIsa A.lt A.T.frame.raBytes [] [] 0
      (bitblastInlLinkedModOfPkg P).fns hints = .ok (code, bounds))
    {b : Nat} (hb : ("bv_solve_bytes", b) ∈ bounds)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (progPtr progLen workPtr workCap fuel : BitVec 64)
    (progBytes : List UInt8) (m : Mem 64) (Rm R : Mem 64 → Prop)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr)
    (hplen : progLen.toNat = progBytes.length)
    (hm : (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m)
    (hargs : A.args5Ok s progPtr progLen workPtr workCap fuel)
    (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆ Eq m ⋆ A.entryFrame s ra b ⋆ R)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        A.calleeSpOk s (A.T.mach.data st) ∧
        ∃ m',
          (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m' ∧
          (A.retGpr (A.T.mach.data st) = 20#64 →
            ∀ prog : BVLogicalExpr, BVProg.parse progBytes = some prog → prog.Unsat) ∧
          (bvSolveTrivialUnsatCond progPtr progBytes workPtr workCap fuel →
            A.retGpr (A.T.mach.data st) = 20#64) ∧
          (A.T.mach.mem (A.T.mach.data st) =⋆ Eq m' ⋆ A.exitFrame s b ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh "bv_solve_bytes")) := by
  have hM := bitblastInlLinkedEnv_moduleOk P hEntry hExt hEx hDisj
  have ⟨hacyc, hwf, hwp⟩ := moduleOk_parts hM
  have hsupp := Compiled.compileModule_supportsSource hcm
  have hnd : ((bitblastInlLinkedModOfPkg P).fns.map Fn.name).Nodup :=
    (List.nodup_append.mp hM.nodup).1
  obtain ⟨f', hf', hnm, _, hspec⟩ :=
    compile_sound A.T hh A.lt (bitblastInlLinkedModOfPkg P)
      (bitblastLinkedEnvOfPkg P) [] [] 0 hints code bounds k₀ hcm hc hu hacyc hwf hsupp hwp
      (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
      (fun _ h => nomatch h) ("bv_solve_bytes", b) hb
  have heqf : f' = bvSolveBytesFn :=
    fn_mem_eq_of_nodup hnd hf' (bvSolveBytesFn_mem_inlLinked P) hnm.symm
  subst heqf
  have hfn := fnSpec_of_legalEnv_legalSig_eq_noExit has hrs
    (List.mem_append_left _ (List.mem_map_of_mem (bvSolveBytesFn_mem_inlLinked P)))
    (fun args m Q X X' h => bitblastLinkedEnv_noExit P _ _ _ args m Q X X' h) hspec
  exact bv_solve_bytes_unsat_of_fnspec A P hh hfn progPtr progLen workPtr workCap fuel
    progBytes m Rm R s ra hplen hm hargs hsp hmem

/-- `LinkedCert`-parameterized `FnSpec` for `bv_solve_bytes` on `bitblastInlLinkedModOfPkg P`. -/
theorem bv_solve_bytes_fnSpec_of_cert (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (hEntry : P.entryFn = "kissat_solve_bytes")
    (hExt : P.mod.externs = []) (hEx : P.mod.exits = [])
    (hDisj : ∀ s ∈ P.mod.fns.map Fn.name, s ∉ bitblastModule.fns.map Fn.name)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (cert : LinkedCert A.T A.L A.lt A.hcl (bitblastInlLinkedModOfPkg P) [] [] 0 2048)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh) :
    A.T.Defined hh "bv_solve_bytes" ∧
      A.T.FnSpec hh "bv_solve_bytes"
        (bitblastLinkedEnvOfPkg P "bv_solve_bytes" [i64, i64, i64, i64, i64] [i64])
        (cert.bound "bv_solve_bytes") 0 := by
  have ⟨hacyc, hwf, hwp⟩ := moduleOk_parts (bitblastInlLinkedEnv_moduleOk P hEntry hExt hEx hDisj)
  exact cert.fnSpec_noExit_id hh (bitblastLinkedEnvOfPkg P) k₀ hc hu hacyc hwf hwp
    (bvSolveBytesFn_mem_inlLinked P) has hrs
    (fun args m Q X X' h => bitblastLinkedEnv_noExit P _ _ _ args m Q X X' h)

/-- `LinkedCert`-parameterized machine-code UNSAT soundness on `bitblastInlLinkedModOfPkg P`. -/
theorem bv_solve_bytes_unsat_of_cert (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (hEntry : P.entryFn = "kissat_solve_bytes")
    (hExt : P.mod.externs = []) (hEx : P.mod.exits = [])
    (hDisj : ∀ s ∈ P.mod.fns.map Fn.name, s ∉ bitblastModule.fns.map Fn.name)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (cert : LinkedCert A.T A.L A.lt A.hcl (bitblastInlLinkedModOfPkg P) [] [] 0 2048)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (progPtr progLen workPtr workCap fuel : BitVec 64)
    (progBytes : List UInt8) (m : Mem 64) (Rm R : Mem 64 → Prop)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr)
    (hplen : progLen.toNat = progBytes.length)
    (hm : (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m)
    (hargs : A.args5Ok s progPtr progLen workPtr workCap fuel)
    (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆ Eq m ⋆ A.entryFrame s ra (cert.bound "bv_solve_bytes") ⋆ R)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        A.calleeSpOk s (A.T.mach.data st) ∧
        ∃ m',
          (bytes progPtr progBytes ⋆ region workPtr workCap.toNat ⋆ Rm) m' ∧
          (A.retGpr (A.T.mach.data st) = 20#64 →
            ∀ prog : BVLogicalExpr, BVProg.parse progBytes = some prog → prog.Unsat) ∧
          (bvSolveTrivialUnsatCond progPtr progBytes workPtr workCap fuel →
            A.retGpr (A.T.mach.data st) = 20#64) ∧
          (A.T.mach.mem (A.T.mach.data st) =⋆ Eq m' ⋆
            A.exitFrame s (cert.bound "bv_solve_bytes") ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh "bv_solve_bytes")) :=
  bv_solve_bytes_unsat_of_fnspec A P hh
    (bv_solve_bytes_fnSpec_of_cert A P hEntry hExt hEx hDisj has hrs cert hh k₀ hc hu).2
    progPtr progLen workPtr workCap fuel progBytes m Rm R s ra hplen hm hargs hsp hmem

/-- `LinkedCert`-parameterized closed concrete-host non-vacuity run on `nvSlabBytes`
(`BCONST false` -> `ret0 = 20#64` and `prog.Unsat`). -/
theorem bv_solve_bytes_nv_run_of_cert (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (hEntry : P.entryFn = "kissat_solve_bytes")
    (hExt : P.mod.externs = []) (hEx : P.mod.exits = [])
    (hDisj : ∀ s ∈ P.mod.fns.map Fn.name, s ∉ bitblastModule.fns.map Fn.name)
    (has : A.lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64])
    (hrs : A.lt.legalSig [i64] = [i64])
    (cert : LinkedCert A.T A.L A.lt A.hcl (bitblastInlLinkedModOfPkg P) [] [] 0 2048) :
    let args : Tup Val [i64, i64, i64, i64, i64] :=
      (nvSlabPtr, nvProgLen, nvSlabWorkPtr, nvWorkCap, nvFuel, ())
    Eventually (A.T.mach.step cert.host)
      (fun st =>
        A.T.mach.pc st = A.init.ra0 ∧
        A.T.mach.getGpr (A.T.mach.data st) A.init.ret0 = 20#64 ∧
        ∀ prog : BVLogicalExpr, BVProg.parse nvProgBytes = some prog → prog.Unsat)
      (A.T.mach.mkState
        (A.init.initState (cert.bound "bv_solve_bytes") nvSlabBytes args)
        (A.T.mach.labelAddr cert.host "bv_solve_bytes")) := by
  intro args
  have ⟨locs, hlocs, _⟩ := A.argsIn_of_args5 (A.init_args5 0 [] 0#64 0#64 0#64 0#64 0#64)
  have hassign : (A.T.toIsa.assignArgs [i64, i64, i64, i64, i64]).isSome = true :=
    Option.isSome_iff_exists.mpr ⟨locs, hlocs⟩
  let Q : Post [i64] := fun (r, ()) _ =>
    r = 20#64 ∧ ∀ prog : BVLogicalExpr, BVProg.parse nvProgBytes = some prog → prog.Unsat
  have hspec := bitblastLinked_bvSolveBytesSpec P
    (nvSlab_bvSolveBytesSpec Q (fun _ _ _ _ => False) (fun _ _ hu => ⟨rfl, hu⟩))
  have hfn := (bv_solve_bytes_fnSpec_of_cert A P hEntry hExt hEx hDisj has hrs cert
    cert.host 0 cert.code_infix_host cert.labelsUnique).2
  refine cert.run_fnSpec A.init hfn nvSlabBytes args
    (Nat.le_trans nvSlabBytes_le_8192 A.maxMem_ge) hassign hspec (fun st h => ?_) A.maxStack_ge
  rcases h with ⟨hpc, ⟨⟨r, _⟩, m', ⟨hr20, hu⟩, hrets, _⟩⟩ | ⟨_, _, _, _, hf, _⟩
  · subst hr20
    exact ⟨hpc, A.init.retsIn_singleton 20#64 (A.T.mach.data st) hrets, hu⟩
  · exact False.elim hf

/-! ## 4. Concrete Gate-1 Step-12 Instantiation (`fidStep12Pkg`, `517 + 64 = 581` fns) -/

/-- Exposed Gate-1 Step-12 `KissatUnsatPkg` (same witness as `fidStep12UnsatPkg`, exposed so
`bitblastFidStep12LinkedMod` and `bitblastFidStep12InlLinkedMod` reduce definitionally). -/
@[expose] def fidStep12Pkg : KissatUnsatPkg where
  mod := fidStep12Module
  inlPolicy := fidInlPolicy
  entryFn := "kissat_solve_bytes"
  entryFn_fn := FullM6Orch.m6oSolveBytesFn
  entryFn_sig := ⟨rfl, rfl, rfl⟩
  entry_mem := fidStep12_solveBytes_mem
  env := fidStep12Env
  moduleOk := fidStep12_moduleOk
  noExit := fun f _ args m Q X X' h => fidStep12Env_noExit f.name f.as f.rs args m Q X X' h
  solve_intro := fun hcfit hwfit hm hreq =>
    fidStep12Env_solve_bytes_of (FullM7Fidelity.m7FidSolveBytesSpec_intro hcfit hwfit hm hreq)

private theorem fidStep12_bitblast_names_disj_bool :
    fidStep12FnNames.all
      (fun s => !(bitblastModule.fns.map Fn.name).contains s) = true := by
  t_kernel_rfl

/-- Zero name collisions between `fidStep12Module.fns` (`517` fns) and `bitblastModule.fns`
(`64` fns). -/
theorem fidStep12_bitblast_names_disj :
    ∀ s ∈ fidStep12Pkg.mod.fns.map Fn.name, s ∉ bitblastModule.fns.map Fn.name := by
  intro s hs hbb
  change s ∈ fidStep12Module.fns.map Fn.name at hs
  rw [fidStep12Module_map_name] at hs
  have h1 := List.all_eq_true.mp fidStep12_bitblast_names_disj_bool s hs
  rw [List.contains_iff_mem.mpr hbb] at h1
  cases h1

/-- Closed `581`-function un-inlined `Bitblast + KissatFidelity Step-12` module (`0` externs,
`0` exits). -/
@[expose] def bitblastFidStep12LinkedMod : Module :=
  bitblastLinkedModOfPkg fidStep12Pkg

/-- Closed `581`-function PGO-inlined `KissatFidelity Step-12 + Bitblast` module (`0` externs,
`0` exits) — exact module emitted by `bv_decide_qbe`. -/
@[expose] def bitblastFidStep12InlLinkedMod : Module :=
  bitblastInlLinkedModOfPkg fidStep12Pkg

/-- Closed `581`-function `Env` for `Bitblast + KissatFidelity Step-12`. -/
@[expose] def bitblastFidStep12LinkedEnv : Env :=
  bitblastLinkedEnvOfPkg fidStep12Pkg

theorem bitblastFidStep12_moduleOk :
    ModuleOk bitblastFidStep12LinkedEnv bitblastFidStep12LinkedMod :=
  bitblastLinkedEnv_moduleOk fidStep12Pkg rfl fidStep12_externs_empty fidStep12_noExit
    fidStep12_bitblast_names_disj

theorem bitblastFidStep12Inl_moduleOk :
    ModuleOk bitblastFidStep12LinkedEnv bitblastFidStep12InlLinkedMod :=
  bitblastInlLinkedEnv_moduleOk fidStep12Pkg rfl fidStep12_externs_empty fidStep12_noExit
    fidStep12_bitblast_names_disj

theorem bitblastFidStep12_checkAcyclic :
    bitblastFidStep12LinkedMod.checkAcyclic = true :=
  (moduleOk_parts bitblastFidStep12_moduleOk).1

theorem bitblastFidStep12Inl_checkAcyclic :
    bitblastFidStep12InlLinkedMod.checkAcyclic = true :=
  (moduleOk_parts bitblastFidStep12Inl_moduleOk).1

theorem bitblastFidStep12_bvSolveBytesSpec
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : bvSolveBytesSpec xs m Q X) :
    bitblastFidStep12LinkedEnv "bv_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X :=
  bitblastLinked_bvSolveBytesSpec fidStep12Pkg h

end LeanQbe.T.Examples.Kissat.FullFidelityBitblastLemmas

end
