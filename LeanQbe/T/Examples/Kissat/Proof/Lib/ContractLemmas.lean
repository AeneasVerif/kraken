/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Logic.CanonicalEnv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Core

/-!
# Shared Contract Proof Combinators & Subsystem Certificate Fold (`Proof.Lib.ContractLemmas`)

Lives outside `Spec/` so `Spec/Core.lean` remains theorem-free:
1. `*_toSpec_xfree`, `*_intro`, and `*_elim` for all six `Spec.Core` contract combinators.
2. `ScratchModifies` and `CorePres` framing helpers (`refl`, `trans`, `get_of_not_mem`, `mono`).
3. `SpecTable.has_at`: O(1)-style indexed capability projection from `Γ.Sat tbl`.
4. `SubsystemCert` and `SubsystemCert.fold`: replaces manual `sigs_append`/`t1..t41` chains.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Spec

open LeanQbe.T
open Kraken.Bedrock2.Test

/-! ## 1. `XFree`, `intro`, and `elim` for Canonical Contract Combinators -/

theorem PureContract.toSpec_xfree {as rs : List Ty} (K : PureContract as rs) :
    K.toSpec.XFree :=
  fun _ _ _ _ _ h => h

theorem PureContract.intro {as rs : List Ty} {K : PureContract as rs}
    {args : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (hpre : K.pre args) (hQ : ∀ res, K.post args res → Q res m) :
    K.toSpec args m Q X :=
  ⟨hpre, hQ⟩

theorem PureContract.elim {as rs : List Ty} {K : PureContract as rs}
    {args : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : K.toSpec args m Q X) :
    K.pre args ∧ ∀ res, K.post args res → Q res m :=
  h

theorem FnContract.toSpec_xfree {as rs : List Ty} {W W' : Type} (K : FnContract as rs W W') :
    K.toSpec.XFree :=
  fun _ _ _ _ _ h => h

theorem FnContract.intro {as rs : List Ty} {W W' : Type} {K : FnContract as rs W W'}
    {args : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (w : W) (R : Mem 64 → Prop) (hpre : K.pre args w) (hmem : (K.mem args w ⋆ R) m)
    (hQ : ∀ res w' m', K.post args w res w' → (K.postMem args w res w' ⋆ R) m' → Q res m') :
    K.toSpec args m Q X :=
  ⟨w, R, hpre, hmem, hQ⟩

theorem FnContract.elim {as rs : List Ty} {W W' : Type} {K : FnContract as rs W W'}
    {args : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : K.toSpec args m Q X) :
    ∃ (w : W) (R : Mem 64 → Prop),
      K.pre args w ∧ (K.mem args w ⋆ R) m ∧
      ∀ res w' m', K.post args w res w' → (K.postMem args w res w' ⋆ R) m' → Q res m' :=
  h

theorem FullContract.toSpec_xfree {extraArgs rs : List Ty} {W : Type}
    (K : FullContract extraArgs rs W) : K.toSpec.XFree :=
  fun _ _ _ _ _ h => h

theorem FullContract.intro {extraArgs rs : List Ty} {W : Type}
    {K : FullContract extraArgs rs W} {c : FullCfg} {s : FullState}
    {args : Tup Val extraArgs} {w : W} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post rs} {X : XPost}
    (hlen : s.LengthsOk c) (hpre : K.pre c s args w) (hmem : (FullMem c s ⋆ R) m)
    (hQ : ∀ res s' m', s'.LengthsOk c → K.post c s args w res s' →
      (FullMem c s' ⋆ R) m' → Q res m') :
    K.toSpec (c.hdr, args) m Q X :=
  ⟨c, s, w, R, rfl, hlen, hpre, hmem, hQ⟩

theorem FullContract.elim {extraArgs rs : List Ty} {W : Type}
    {K : FullContract extraArgs rs W} {h0 : BitVec 64}
    {args : Tup Val extraArgs} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : K.toSpec (h0, args) m Q X) :
    ∃ (c : FullCfg) (s : FullState) (w : W) (R : Mem 64 → Prop),
      h0 = c.hdr ∧ s.LengthsOk c ∧ K.pre c s args w ∧ (FullMem c s ⋆ R) m ∧
      ∀ res s' m', s'.LengthsOk c → K.post c s args w res s' →
        (FullMem c s' ⋆ R) m' → Q res m' :=
  h

theorem M6HdrContract.toSpec_xfree {extraArgs rs : List Ty} {W : Type}
    (K : M6HdrContract extraArgs rs W) : K.toSpec.XFree :=
  fun _ _ _ _ _ h => h

theorem M6HdrContract.intro {extraArgs rs : List Ty} {W : Type}
    {K : M6HdrContract extraArgs rs W} {c : FullCfg} {ext : List (BitVec 64)}
    {s : FullState} {args : Tup Val extraArgs} {w : W} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post rs} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hpre : K.pre c ext s args w) (hmem : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ res ext' s' m', M6HdrExtOk ext' → K.extFrame.rel ext ext' →
      s'.LengthsOk c → K.post c ext s args w res ext' s' →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q res m') :
    K.toSpec (c.hdr, args) m Q X :=
  ⟨c, ext, s, w, R, rfl, hcfg, hext, hlen, hpre, hmem, hQ⟩

theorem M6HdrContract.elim {extraArgs rs : List Ty} {W : Type}
    {K : M6HdrContract extraArgs rs W} {h0 : BitVec 64}
    {args : Tup Val extraArgs} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : K.toSpec (h0, args) m Q X) :
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (w : W)
      (R : Mem 64 → Prop),
      h0 = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      K.pre c ext s args w ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ res ext' s' m', M6HdrExtOk ext' → K.extFrame.rel ext ext' →
        s'.LengthsOk c → K.post c ext s args w res ext' s' →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q res m' :=
  h

theorem FullCfgContract.toSpec_xfree {extraArgs rs : List Ty} {W : Type}
    (K : FullCfgContract extraArgs rs W) : K.toSpec.XFree :=
  fun _ _ _ _ _ h => h

theorem FullCfgContract.intro {extraArgs rs : List Ty} {W : Type}
    {K : FullCfgContract extraArgs rs W} {c : FullCfg} {s : FullState}
    {args : Tup Val extraArgs} {w : W} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post rs} {X : XPost}
    (hlen : s.LengthsOk c) (hpre : K.pre c s args w) (hmem : (FullMem c s ⋆ R) m)
    (hQ : ∀ res c' s' m', FullCfgCompat c c' → s'.LengthsOk c' →
      K.post c s args w res c' s' → (FullMem c' s' ⋆ R) m' → Q res m') :
    K.toSpec (c.hdr, args) m Q X :=
  ⟨c, s, w, R, rfl, hlen, hpre, hmem, hQ⟩

theorem FullCfgContract.elim {extraArgs rs : List Ty} {W : Type}
    {K : FullCfgContract extraArgs rs W} {h0 : BitVec 64}
    {args : Tup Val extraArgs} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : K.toSpec (h0, args) m Q X) :
    ∃ (c : FullCfg) (s : FullState) (w : W) (R : Mem 64 → Prop),
      h0 = c.hdr ∧ s.LengthsOk c ∧ K.pre c s args w ∧ (FullMem c s ⋆ R) m ∧
      ∀ res c' s' m', FullCfgCompat c c' → s'.LengthsOk c' →
        K.post c s args w res c' s' → (FullMem c' s' ⋆ R) m' → Q res m' :=
  h

theorem M6HdrCfgContract.toSpec_xfree {extraArgs rs : List Ty} {W : Type}
    (K : M6HdrCfgContract extraArgs rs W) : K.toSpec.XFree :=
  fun _ _ _ _ _ h => h

theorem M6HdrCfgContract.intro {extraArgs rs : List Ty} {W : Type}
    {K : M6HdrCfgContract extraArgs rs W} {c : FullCfg} {ext : List (BitVec 64)}
    {s : FullState} {args : Tup Val extraArgs} {w : W} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post rs} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hpre : K.pre c ext s args w) (hmem : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ res c' ext' s' m', FullCfgCompat c c' → FullM6HdrCfgOk c' →
      M6HdrExtOk ext' → K.extFrame.rel ext ext' → s'.LengthsOk c' →
      K.post c ext s args w res c' ext' s' →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q res m') :
    K.toSpec (c.hdr, args) m Q X :=
  ⟨c, ext, s, w, R, rfl, hcfg, hext, hlen, hpre, hmem, hQ⟩

theorem M6HdrCfgContract.elim {extraArgs rs : List Ty} {W : Type}
    {K : M6HdrCfgContract extraArgs rs W} {h0 : BitVec 64}
    {args : Tup Val extraArgs} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : K.toSpec (h0, args) m Q X) :
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (w : W)
      (R : Mem 64 → Prop),
      h0 = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      K.pre c ext s args w ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ res c' ext' s' m', FullCfgCompat c c' → FullM6HdrCfgOk c' →
        M6HdrExtOk ext' → K.extFrame.rel ext ext' → s'.LengthsOk c' →
        K.post c ext s args w res c' ext' s' →
        (FullM6HdrMem c' ext' s' ⋆ R) m' → Q res m' :=
  h

/-! ## 2. `ScratchModifies` & `CorePres` Framing Lemmas -/

theorem CorePres.refl (s : FullState) : CorePres s s := rfl

theorem CorePres.trans {s₁ s₂ s₃ : FullState}
    (h₁₂ : CorePres s₁ s₂) (h₂₃ : CorePres s₂ s₃) : CorePres s₁ s₃ :=
  Eq.trans h₂₃ h₁₂

theorem ScratchModifies.refl (mod : List ScratchField) (s : FullState) :
    ScratchModifies mod s s :=
  fun _ _ => rfl

theorem ScratchModifies.trans {mod : List ScratchField} {s₁ s₂ s₃ : FullState}
    (h₁₂ : ScratchModifies mod s₁ s₂) (h₂₃ : ScratchModifies mod s₂ s₃) :
    ScratchModifies mod s₁ s₃ :=
  fun f hf => (h₂₃ f hf).trans (h₁₂ f hf)

theorem ScratchModifies.get_of_not_mem {mod : List ScratchField} {s s' : FullState}
    (h : ScratchModifies mod s s') {f : ScratchField} (hf : f ∉ mod) :
    s'.scratch.getField f = s.scratch.getField f :=
  h f hf

theorem ScratchModifies.mono {mod₁ mod₂ : List ScratchField} {s s' : FullState}
    (h : ScratchModifies mod₁ s s') (hsub : ∀ f ∈ mod₁, f ∈ mod₂) :
    ScratchModifies mod₂ s s' :=
  fun f hf => h f (fun hmem => hf (hsub f hmem))

end LeanQbe.T.Examples.Kissat.Proof.Spec

/-! ## 3. `SpecTable.has_at` & `SubsystemCert` Fold Combinator -/

namespace LeanQbe.T.Examples.Kissat.Proof.Lib

open LeanQbe.T

/-- Project an `XFree` capability from `Γ.Sat tbl` using an explicit table index `i`. -/
theorem SpecTable.has_at {Γ : Env} {tbl : List SpecEntry} (hSat : Γ.Sat tbl)
    (i : Nat) {e : SpecEntry} (hi : tbl[i]? = some e) (hX : e.spec.XFree) :
    Γ.Has e.name e.spec :=
  Env.Sat.has hSat (List.mem_of_getElem? hi) hX

/-- Self-contained certificate bundle for one subsystem (`Cert.lean`). -/
structure SubsystemCert where
  fns          : List Fn
  specs        : List SpecEntry
  deps         : List SpecEntry
  specs_sigs   : specs.map SpecEntry.sig = fns.map Fn.sig
  specs_noExit : specs.all SpecEntry.noExit = true
  cert         : SegCert deps fns specs

namespace SubsystemCert

/-- Concatenated `Fn` list across a list of subsystem certificates. -/
@[expose] def allFns (certs : List SubsystemCert) : List Fn :=
  certs.flatMap SubsystemCert.fns

/-- Concatenated `SpecEntry` table across a list of subsystem certificates. -/
@[expose] def allSpecs (certs : List SubsystemCert) : List SpecEntry :=
  certs.flatMap SubsystemCert.specs

theorem noExit_mem (c : SubsystemCert) : ∀ e ∈ c.specs, e.noExit = true :=
  fun e he => List.all_eq_true.mp c.specs_noExit e he

theorem names (c : SubsystemCert) : c.specs.map SpecEntry.name = c.fns.map Fn.name :=
  names_eq_of_sigs_eq c.specs_sigs

theorem allSpecs_sigs :
    ∀ certs : List SubsystemCert,
      (allSpecs certs).map SpecEntry.sig = (allFns certs).map Fn.sig
  | [] => rfl
  | c :: cs => by
    simp only [allSpecs, allFns, List.flatMap_cons, List.map_append, c.specs_sigs]
    exact congrArg (_ ++ ·) (allSpecs_sigs cs)

theorem allSpecs_noExit :
    ∀ certs : List SubsystemCert, (allSpecs certs).all SpecEntry.noExit = true
  | [] => rfl
  | c :: cs => by
    simp only [allSpecs, List.flatMap_cons, List.all_append, c.specs_noExit, Bool.true_and]
    exact allSpecs_noExit cs

theorem fold_tableImpl_aux {Γ : Env} {totalSpecs : List SpecEntry}
    (hTotal : Γ.Sat totalSpecs) :
    ∀ cs : List SubsystemCert,
      (∀ c ∈ cs, ∀ e ∈ c.deps, e ∈ totalSpecs) →
      Γ.Sat (allSpecs cs) →
      TableImpl Γ (allFns cs) (allSpecs cs)
  | [], _, _ => trivial
  | c :: cs, hdeps, hSat => by
    have hSat' : Γ.Sat (c.specs ++ allSpecs cs) := by
      simpa [allSpecs, List.flatMap_cons] using hSat
    have hdeps_c : Γ.Sat c.deps := fun e he => hTotal e (hdeps c List.mem_cons_self e he)
    have himpl_c := c.cert Γ hdeps_c hSat'.left
    have himpl_cs := fold_tableImpl_aux hTotal cs
      (fun c' hc' => hdeps c' (List.mem_cons_of_mem _ hc')) hSat'.right
    simpa [allFns, allSpecs, List.flatMap_cons] using
      TableImpl.append_sigs himpl_c c.specs_sigs himpl_cs

/-- Fold a list of subsystem certificates into a single closed `SubsystemCert` (`deps := []`),
replacing manual `sigs_append` / `noExit_append` / `t1..tN` chains. -/
@[expose] def fold (certs : List SubsystemCert)
    (hdeps : ∀ c ∈ certs, ∀ e ∈ c.deps, e ∈ allSpecs certs) : SubsystemCert where
  fns := allFns certs
  specs := allSpecs certs
  deps := []
  specs_sigs := allSpecs_sigs certs
  specs_noExit := allSpecs_noExit certs
  cert := fun _ _ hSat => fold_tableImpl_aux hSat certs hdeps hSat

end SubsystemCert

end LeanQbe.T.Examples.Kissat.Proof.Lib

end
