module

public import LeanQbe.T.LeanLCNF.Sem.Perceus
public import LeanQbe.T.LeanLCNF.Sem.LowerSound4
public import LeanQbe.T.LeanLCNF.LcnfC0LinkKit
public import LeanQbe.T.MainCertScc

/-!
# End-to-End Verified Lean-to-Machine Compilation (`E2E.lean`, `L5`)

Composes all `L1`–`L4b` layers (`lowerModule`, `LowerSound4`, `RcCheck`, `Perceus`,
`perceus_sound{,_idx}`, `LcnfC0LinkKit`, `LinkedCert`, `LinkedCertScc`) into pure
value-level `T.FnSpec` contracts with zero hand-written Tier-H or Tier-T weakest
preconditions:

* `PEnc` — canonical encoding of Lean types (`Nat`, `Bool`, `UIntN`, `USize`, `String`,
  `ByteArray`, `List`, `Array`, `Option`, `Prod`, `PVal`) into `PVal`.
* `encDeclSpec`, `encSpec1`, `encSpec2` — pure Tier-T `Spec` contracts parameterized by
  preconditions/postconditions over `PEnc`, `ResStateInv`, and `ValRep`.
* `hOfP_retTyped`, `hOfPIdx_retTyped` — automatic `HEnv.RetTyped` discharge.
* `rtC0CoreEnv_le_semChunks_acyc` — target-generic acyclic runtime lift through `LinkedCertScc`.
* `lowerModule_budgetSemScc` — `BudgetEnv.semScc` soundness via `BudgetEnv.lfp_wf_mkSccOp`.
* `lean_fn_compiled_acyclic`, `lean_fn_compiled_loop`, `lean_fn_compiled_scc` — target-parametric
  end-to-end theorems on any `T : Target` (`Amd64`, `Arm64`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

/-! ## 1. Lean Value Encoding `PEnc` and Pure Specifications -/

/-- Canonical embedding of Lean data types into Tier-P values paired with `LcTy`. -/
class PEnc (α : Type) where
  enc : α → PVal
  lcTy : LcTy

instance : PEnc PVal where
  enc := id
  lcTy := .tobject

instance : PEnc Nat where
  enc := .nat
  lcTy := .tobject

instance : PEnc Bool where
  enc := PVal.bool
  lcTy := .uint8

instance : PEnc UInt8 where
  enc x := .bits 8 x.toBitVec
  lcTy := .uint8

instance : PEnc UInt16 where
  enc x := .bits 16 x.toBitVec
  lcTy := .uint16

instance : PEnc UInt32 where
  enc x := .bits 32 x.toBitVec
  lcTy := .uint32

instance : PEnc UInt64 where
  enc x := .bits 64 x.toBitVec
  lcTy := .uint64

instance : PEnc USize where
  enc x := .bits 64 (BitVec.ofNat 64 x.toNat)
  lcTy := .usize

instance : PEnc String where
  enc := .str
  lcTy := .tobject

instance : PEnc ByteArray where
  enc bs := .barr bs.data.toList
  lcTy := .tobject

instance {α : Type} [PEnc α] : PEnc (List α) where
  enc xs := PVal.ofList (xs.map PEnc.enc)
  lcTy := .tobject

instance {α : Type} [PEnc α] : PEnc (Array α) where
  enc xs := .arr (xs.toList.map PEnc.enc)
  lcTy := .tobject

instance {α : Type} [PEnc α] : PEnc (Option α) where
  enc
    | none => .ctor 0 [] []
    | some a => .ctor 1 [PEnc.enc a] []
  lcTy := .tobject

instance {α β : Type} [PEnc α] [PEnc β] : PEnc (α × β) where
  enc p := .ctor 0 [PEnc.enc p.1, PEnc.enc p.2] []
  lcTy := .tobject

/-- Pure 1-argument Tier-P `PSpec` for `f : α → β` guarded by `Pre : α → Prop`. -/
@[expose] def pSpec1 {α β : Type} [PEnc α] [PEnc β]
    (Pre : α → Prop) (f : α → β) : PSpec :=
  fun pvs Q _ => ∃ a, Pre a ∧ pvs = [PEnc.enc a] ∧ Q (PEnc.enc (f a))

/-- Pure 2-argument Tier-P `PSpec` for `f : α₁ → α₂ → β` guarded by `Pre : α₁ → α₂ → Prop`. -/
@[expose] def pSpec2 {α₁ α₂ β : Type} [PEnc α₁] [PEnc α₂] [PEnc β]
    (Pre : α₁ → α₂ → Prop) (f : α₁ → α₂ → β) : PSpec :=
  fun pvs Q _ => ∃ a₁ a₂, Pre a₁ a₂ ∧ pvs = [PEnc.enc a₁, PEnc.enc a₂] ∧ Q (PEnc.enc (f a₁ a₂))

/-- Declaration-level pure Tier-T `Spec` over encoded values `pvs`, heap `σ`, and RC/resource
invariants (`HInv`, `RcInv`, `ResStateInv`, `ValRep`, `CallPreserve`), independent of `XPost`. -/
@[expose] def encDeclSpec (d : LcDecl)
    (Pre : List PVal → Nat → Nat → Nat → Prop)
    (Post : List PVal → PVal → Nat → Nat → Nat → Prop) :
    Spec (i64 :: (d.params.map (·.ty.toTTy)).take regArgs) [d.retTy.toTTy] :=
  fun (rt, xs) mem Q _X =>
    let spilled := (d.params.map (·.ty.toTTy)).drop regArgs
    ∃ (σ : HState) (R : Mem 64 → Prop) (pvs : List PVal)
      (extH ghostH : List (BitVec 64)) (rem₀ wr₀ rcr₀ : Nat),
      let as := wordsOfTup xs ++ spilledWords σ.st.extraArgs spilled
      spilled.length ≤ σ.st.extraArgs.length ∧
      HInv rt σ ∧ (σ.mem rt ⋆ R) mem ∧
      RcInv rt (entryRcFrame d pvs as extH ghostH) σ ∧
      HandlesInHeap (extH ++ ghostH) σ.objs ∧
      ResStateInv σ rem₀ wr₀ rcr₀ ∧
      pvs.length = d.params.length ∧
      Pre pvs rem₀ wr₀ rcr₀ ∧
      (∀ r rw σ' rem' wr' rcr' (h : rw.1 = d.retTy.toTTy),
        Post pvs r rem' wr' rcr' →
        HeapClean rt σ' →
        ResStateInv σ' rem' wr' rcr' →
        ValRep d.retTy r rw σ'.objs →
        HandlesRcSound (retHandles d.retTy rw ++ extH ++ ghostH) σ'.objs →
        CallPreserve (nonScalarWords d.params as) (extH ++ ghostH) σ σ' →
        ∀ m', HInv rt σ' → (σ'.mem rt ⋆ R) m' → Q (h ▸ rw.2, ()) m')

/-- Single-argument specialization of `encDeclSpec` for a Lean function `f : α → β`. -/
@[expose] def encSpec1 {α β : Type} [PEnc α] [PEnc β] (d : LcDecl)
    (Pre : α → Nat → Nat → Nat → Prop) (f : α → β)
    (PostR : α → Nat → Nat → Nat → Prop := fun _ _ _ _ => True) :
    Spec (i64 :: (d.params.map (·.ty.toTTy)).take regArgs) [d.retTy.toTTy] :=
  encDeclSpec d
    (fun pvs rem wr rcr => ∃ a, pvs = [PEnc.enc a] ∧ Pre a rem wr rcr)
    (fun pvs r rem' wr' rcr' =>
      ∀ a, pvs = [PEnc.enc a] → r = PEnc.enc (f a) ∧ PostR a rem' wr' rcr')

/-- Two-argument specialization of `encDeclSpec` for a Lean function `f : α₁ → α₂ → β`. -/
@[expose] def encSpec2 {α₁ α₂ β : Type} [PEnc α₁] [PEnc α₂] [PEnc β] (d : LcDecl)
    (Pre : α₁ → α₂ → Nat → Nat → Nat → Prop) (f : α₁ → α₂ → β)
    (PostR : α₁ → α₂ → Nat → Nat → Nat → Prop := fun _ _ _ _ _ => True) :
    Spec (i64 :: (d.params.map (·.ty.toTTy)).take regArgs) [d.retTy.toTTy] :=
  encDeclSpec d
    (fun pvs rem wr rcr => ∃ a₁ a₂, pvs = [PEnc.enc a₁, PEnc.enc a₂] ∧ Pre a₁ a₂ rem wr rcr)
    (fun pvs r rem' wr' rcr' =>
      ∀ a₁ a₂, pvs = [PEnc.enc a₁, PEnc.enc a₂] →
        r = PEnc.enc (f a₁ a₂) ∧ PostR a₁ a₂ rem' wr' rcr')

theorem encDeclSpec_noex {d : LcDecl}
    {PreP : List PVal → Nat → Nat → Nat → Prop}
    {PostP : List PVal → PVal → Nat → Nat → Nat → Prop}
    (args : Tup Val (i64 :: (d.params.map (·.ty.toTTy)).take regArgs))
    (m : Mem 64) (Q : Post [d.retTy.toTTy]) (X X' : XPost) :
    encDeclSpec d PreP PostP args m Q X → encDeclSpec d PreP PostP args m Q X' :=
  fun h => h

/-! ## 2. `ValRep` Word Typing, `hOfP` Return Typing, & `encDeclSpec` Lift -/

private theorem lcTy_width_of_not_scalar :
    ∀ {ty : LcTy}, ty.isScalar = false → ty.width = 64
  | .object, _ | .tobject, _ | .tagged, _ | .erased, _ | .void, _ => rfl

theorem ValRep_word_ty {ty : LcTy} {pv : PVal} {w : Word} {objs : List LcnfObj}
    (h : ValRep ty pv w objs) : w.1 = ty.toTTy := by
  unfold ValRep at h
  by_cases hs : ty.isScalar = true
  · simp only [hs, ↓reduceIte, ScalarRep] at h
    rcases h with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  · have hns : ty.isScalar = false := Bool.eq_false_iff.mpr hs
    simp only [hns, Bool.false_eq_true, ↓reduceIte] at h
    rcases h with ⟨_, rfl, _⟩
    simp [Word.i64, LcTy.toTTy, lcTy_width_of_not_scalar hns]

private theorem mod_nodup_of_inFirstOrder {m : LcModule}
    (hfrag : m.inFirstOrderFragment = true) :
    (m.decls.map (·.name)).Nodup := by
  simp only [LcModule.inFirstOrderFragment, Bool.and_eq_true] at hfrag
  exact nodup_of_symsNodup hfrag.1.1

theorem hOfP_retTyped {m : LcModule} (hfrag : m.inFirstOrderFragment = true) (Δp : PEnv) :
    HEnv.RetTyped m (hOfP m Δp) := by
  intro d hd as σ Q₁ Q₂ X₁ X₂ hQ hX
    ⟨rt, d', Δr, pvs, extH, ghostH, rem₀, wr₀, rcr₀, Qp, Xp, Pr, Er,
      hd', hnm, hresOk, hrc, hhih, hres, hlen, hdp, hdr, hq, hx⟩
  obtain rfl : d' = d := mod_decl_unique (mod_nodup_of_inFirstOrder hfrag) hd hd' hnm
  refine ⟨rt, d', Δr, pvs, extH, ghostH, rem₀, wr₀, rcr₀, Qp, Xp, Pr, Er,
    hd', rfl, hresOk, hrc, hhih, hres, hlen, hdp, hdr, ?_, ?_⟩
  · intro r rw σ' rem' wr' rcr' hqp hpr hc' hres' hvr hno hsnd hcpres
    exact hQ rw σ' (ValRep_word_ty hvr)
      (hq r rw σ' rem' wr' rcr' hqp hpr hc' hres' hvr hno hsnd hcpres)
  · intro c rem' wr' rcr' σ' hxp her
    exact hX _ σ' (hx c rem' wr' rcr' σ' hxp her)

theorem hOfPIdx_retTyped {m : LcModule} (hfrag : m.inFirstOrderFragment = true)
    (Δp : Nat → PEnv) (k : Nat) :
    HEnv.RetTyped m (hOfPIdx m Δp k) := by
  intro d hd as σ Q₁ Q₂ X₁ X₂ hQ hX
    ⟨rt, d', Δr, pvs, extH, ghostH, rem₀, wr₀, rcr₀, Qp, Xp, Pr, Er,
      hd', hnm, hresOk, hrc, hhih, hres, hlen, hdp, hdr, hq, hx⟩
  obtain rfl : d' = d := mod_decl_unique (mod_nodup_of_inFirstOrder hfrag) hd hd' hnm
  refine ⟨rt, d', Δr, pvs, extH, ghostH, rem₀, wr₀, rcr₀, Qp, Xp, Pr, Er,
    hd', rfl, hresOk, hrc, hhih, hres, hlen, hdp, hdr, ?_, ?_⟩
  · intro r rw σ' rem' wr' rcr' hqp hpr hc' hres' hvr hno hsnd hcpres
    exact hQ rw σ' (ValRep_word_ty hvr)
      (hq r rw σ' rem' wr' rcr' hqp hpr hc' hres' hvr hno hsnd hcpres)
  · intro c rem' wr' rcr' σ' hxp her
    exact hX _ σ' (hx c rem' wr' rcr' σ' hxp her)

theorem encDeclSpec_le_liftHOfP {m : LcModule} {d : LcDecl} (hd : d ∈ m.decls)
    {Δp : PEnv} {Δr : PResEnv} (hresOk : PResOk Δr m)
    {PreP : List PVal → Nat → Nat → Nat → Prop}
    {PostP : List PVal → PVal → Nat → Nat → Nat → Prop}
    (hpre : ∀ pvs rem₀ wr₀ rcr₀, PreP pvs rem₀ wr₀ rcr₀ →
      ∃ Qp Pr,
        Δp d.name pvs Qp (fun _ => False) ∧
        Δr d.name pvs rem₀ wr₀ rcr₀ Pr (fun _ _ _ _ => False) ∧
        (∀ r rem' wr' rcr', Qp r → Pr r rem' wr' rcr' → PostP pvs r rem' wr' rcr'))
    {xs : Tup Val (i64 :: (d.params.map (·.ty.toTTy)).take regArgs)}
    {mem : Mem 64} {Q : Post [d.retTy.toTTy]} {X : XPost}
    (hs : encDeclSpec d PreP PostP xs mem Q X) :
    liftDeclSpec (hOfP m Δp d.name) d.params d.retTy xs mem Q X := by
  rcases xs with ⟨rt, args⟩
  rcases hs with ⟨σ, R, pvs, extH, ghostH, rem₀, wr₀, rcr₀,
    hsp, hinv, hmem, hrc, hhih, hres, hlen, hpreP, hpost⟩
  obtain ⟨Qp, Pr, hdp, hdr, hPQ⟩ := hpre pvs rem₀ wr₀ rcr₀ hpreP
  refine ⟨σ, R, hsp, hinv, hmem, rt, d, Δr, pvs, extH, ghostH, rem₀, wr₀, rcr₀,
    Qp, fun _ => False, Pr, fun _ _ _ _ => False,
    hd, rfl, hresOk, hrc, hhih, hres, hlen, hdp, hdr, ?_, ?_⟩
  · intro r rw σ' rem' wr' rcr' hqp hpr hc' hres' hvr _ hsnd hcpres
    have hwty : rw.1 = d.retTy.toTTy := ValRep_word_ty hvr
    exact ⟨hwty, hpost r rw σ' rem' wr' rcr' hwty
      (hPQ r rem' wr' rcr' hqp hpr) hc' hres' hvr hsnd hcpres⟩
  · intro c _ _ _ _ hf; exact False.elim hf

theorem encDeclSpec_le_liftHOfPIdx {m : LcModule} {d : LcDecl} (hd : d ∈ m.decls)
    {Δp : Nat → PEnv} {Δr : Nat → PResEnv} (hresOk : PResOkIdx Δr m) (k : Nat)
    {PreP : List PVal → Nat → Nat → Nat → Prop}
    {PostP : List PVal → PVal → Nat → Nat → Nat → Prop}
    (hpre : ∀ pvs rem₀ wr₀ rcr₀, PreP pvs rem₀ wr₀ rcr₀ →
      ∃ Qp Pr,
        Δp k d.name pvs Qp (fun _ => False) ∧
        Δr k d.name pvs rem₀ wr₀ rcr₀ Pr (fun _ _ _ _ => False) ∧
        (∀ r rem' wr' rcr', Qp r → Pr r rem' wr' rcr' → PostP pvs r rem' wr' rcr'))
    {xs : Tup Val (i64 :: (d.params.map (·.ty.toTTy)).take regArgs)}
    {mem : Mem 64} {Q : Post [d.retTy.toTTy]} {X : XPost}
    (hs : encDeclSpec d PreP PostP xs mem Q X) :
    liftDeclSpec (hOfPIdx m Δp k d.name) d.params d.retTy xs mem Q X := by
  rcases xs with ⟨rt, args⟩
  rcases hs with ⟨σ, R, pvs, extH, ghostH, rem₀, wr₀, rcr₀,
    hsp, hinv, hmem, hrc, hhih, hres, hlen, hpreP, hpost⟩
  obtain ⟨Qp, Pr, hdp, hdr, hPQ⟩ := hpre pvs rem₀ wr₀ rcr₀ hpreP
  refine ⟨σ, R, hsp, hinv, hmem, rt, d, Δr, pvs, extH, ghostH, rem₀, wr₀, rcr₀,
    Qp, fun _ => False, Pr, fun _ _ _ _ => False,
    hd, rfl, hresOk, hrc, hhih, hres, hlen, hdp, hdr, ?_, ?_⟩
  · intro r rw σ' rem' wr' rcr' hqp hpr hc' hres' hvr _ hsnd hcpres
    have hwty : rw.1 = d.retTy.toTTy := ValRep_word_ty hvr
    exact ⟨hwty, hpost r rw σ' rem' wr' rcr' hwty
      (hPQ r rem' wr' rcr' hqp hpr) hc' hres' hvr hsnd hcpres⟩
  · intro c _ _ _ _ hf; exact False.elim hf

private theorem liftEnv_of_decl {m : LcModule} {Δ : HEnv} {d : LcDecl} (hd : d ∈ m.decls)
    {sym : Sym} {as rs : List Ty} (hsym : sym = mangleLc d.name)
    (ha : as = i64 :: (d.params.map (·.ty.toTTy)).take regArgs)
    (hr : rs = [d.retTy.toTTy]) {xs : Tup Val as} {mem : Mem 64} {Q : Post rs} {X : XPost}
    (hspec : liftDeclSpec (Δ d.name) d.params d.retTy (ha ▸ xs) mem (hr ▸ Q) X) :
    liftEnv m Δ sym as rs xs mem Q X := by
  subst hsym; subst ha; subst hr
  exact ⟨d, hd, rfl, rfl, rfl, hspec⟩

/-! ## 3. Acyclic Runtime `LinkedCert` Lift into `semChunks` -/

private theorem fn_eq_of_name_nodup' :
    ∀ {fs : List Fn}, (fs.map Fn.name).Nodup →
      ∀ {f g : Fn}, f ∈ fs → g ∈ fs → f.name = g.name → f = g
  | [], _, _, _, hf, _, _ => nomatch hf
  | _ :: _, hnd, f, g, hf, hg, hnm => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    rcases List.mem_cons.mp hf with rfl | hf' <;> rcases List.mem_cons.mp hg with rfl | hg'
    · rfl
    · exact absurd hnm.symm (hnd.1 g hg')
    · exact absurd hnm (hnd.1 f hf')
    · exact fn_eq_of_name_nodup' hnd.2 hf' hg' hnm

private theorem list_split_getElem {α : Type _} :
    ∀ (xs : List α) {i : Nat} (hi : i < xs.length),
      xs = xs.take i ++ xs[i] :: xs.drop (i + 1)
  | _ :: rest, 0, _ => rfl
  | x :: rest, i + 1, hi => by
    simp only [List.take_succ_cons, List.getElem_cons_succ, List.drop_succ_cons, List.cons_append]
    exact congrArg (x :: ·) (list_split_getElem rest (Nat.lt_of_succ_lt_succ hi))

private theorem acycChunk_rtC0CoreEnv_le_semScc {T : Target} {lt : LegalTarget}
    (c : CompiledChunk T lt rtExitSyms 64) (extSigs : List SigEntry) (Γprev : Env)
    (hc_acyc : (⟨c.fs, externsOfSigs extSigs, rtExitSyms⟩ : Module).checkAcyclic = true)
    (hc_nd : (c.fs.map Fn.name ++ extSigs.map Prod.fst).Nodup)
    (hc_sub : ∀ f ∈ c.fs, f ∈ rtC0CoreMod.fns)
    (hext_rt : ∀ f ∈ rtC0CoreMod.fns, f.sig ∈ extSigs →
      ∀ xs m Q X, rtC0CoreEnv f.name f.as f.rs xs m Q X → Γprev f.name f.as f.rs xs m Q X) :
    ∀ (i : Nat), (hi : i < c.fs.length) →
      let fn := c.fs[i]'hi
      ∀ xs m Q X, rtC0CoreEnv fn.name fn.as fn.rs xs m Q X →
        Env.semScc ⟨c.fs, externsOfSigs extSigs, rtExitSyms⟩
          Γprev fn.name fn.as fn.rs xs m Q X := by
  let M : Module := ⟨c.fs, externsOfSigs extSigs, rtExitSyms⟩
  have hnd_split := List.nodup_append.mp hc_nd
  have hnd_c : (c.fs.map Fn.name).Nodup := hnd_split.1
  have hnd_ext : (extSigs.map Prod.fst).Nodup := hnd_split.2.1
  have hdisj := hnd_split.2.2
  have hchk_parts := (Bool.and_eq_true _ _).mp hc_acyc
  have hcalls_all : Module.checkFnsCallsOk rtExitSyms extSigs [] c.fs = true := by
    simpa [M, externsOfSigs_map_sig] using hchk_parts.2
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi fn xs m Q X hrt
    have hmem_c : fn ∈ c.fs := List.getElem_mem hi
    have hmem_rt : fn ∈ rtC0CoreMod.fns := hc_sub fn hmem_c
    have hsplit_c : c.fs = c.fs.take i ++ fn :: c.fs.drop (i + 1) :=
      list_split_getElem c.fs hi
    have hcalls_M : fn.callsOk ((c.fs.take i).map Fn.sig ++ extSigs) rtExitSyms := by
      simpa using Module.checkFnsCallsOk_ok rtExitSyms extSigs [] c.fs (c.fs.take i) fn
        (c.fs.drop (i + 1)) hcalls_all hsplit_c
    obtain ⟨pre_rt, post_rt, hsplit_rt⟩ := List.mem_iff_append.mp hmem_rt
    have hfnOk_rt := rtC0CoreMod_moduleOk.fnsOk pre_rt fn post_rt hsplit_rt
    have hwp_rt := rtC0CoreMod_fn_sound hmem_rt hrt
    have hwp_res : Func.wp (Env.restrict rtC0CoreEnv (rtC0CoreMod.fns.map Fn.sig))
        fn.body xs m Q X := by
      refine wp_env_agree_of_callsOk
        (hfnOk_rt.1 Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units fn.as))
        hfnOk_rt.2.1 (fun g as bs hg xs' m' P E hcall => ⟨?_, hcall⟩) m hwp_rt
      simp only [rtC0CoreMod, List.map_nil, List.append_nil] at hg
      obtain ⟨gf, hgf, hsig⟩ := List.mem_map.mp hg
      have hgf' : gf ∈ rtC0CoreMod.fns := hsplit_rt ▸ List.mem_append_left _ hgf
      exact hsig ▸ List.mem_map_of_mem hgf'
    have hwp_M : Func.wp (Env.sccStep M (Env.semScc M Γprev) Γprev) fn.body xs m Q X := by
      refine wp_env_agree_of_callsOk
        (hfnOk_rt.1 Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units fn.as))
        hcalls_M (fun g as bs hg xs' m' P E hcall => ?_) m hwp_res
      rcases List.mem_append.mp hg with hpre | hext
      · obtain ⟨gf, hgf, hsig⟩ := List.mem_map.mp hpre
        rcases Prod.mk.inj hsig with ⟨rfl, hsig'⟩
        rcases Prod.mk.inj hsig' with ⟨rfl, rfl⟩
        obtain ⟨j, hj, hgj⟩ := List.mem_iff_getElem.mp hgf
        have hj_lt_i : j < i := Nat.lt_of_lt_of_le hj (List.length_take_le i c.fs)
        have hj_len : j < c.fs.length := Nat.lt_trans hj_lt_i hi
        have hgf_eq : c.fs[j]'hj_len = gf := by
          rw [List.getElem_take] at hgj
          exact hgj
        subst hgf_eq
        have hgf_mem : (c.fs[j]'hj_len) ∈ c.fs := List.getElem_mem hj_len
        have ih_g := ih j hj_lt_i hj_len xs' m' P E hcall.2
        exact Or.inl ⟨List.mem_map_of_mem hgf_mem, ih_g⟩
      · obtain ⟨grt, hgrt, hgrt_sig⟩ := List.mem_map.mp hcall.1
        rcases Prod.mk.inj hgrt_sig with ⟨hgn, hsig'⟩
        rcases Prod.mk.inj hsig' with ⟨hga, hgr⟩
        have hgrt_ext : grt.sig ∈ extSigs := by
          change (grt.name, grt.as, grt.rs) ∈ extSigs
          rw [hgn, hga, hgr]; exact hext
        subst hgn; subst hga; subst hgr
        refine Or.inr ⟨by rw [externsOfSigs_map_sig]; exact hext, ?_⟩
        exact hext_rt grt hgrt hgrt_ext xs' m' P E hcall.2
    refine Env.lfp_pre (sccOp_mono M Γprev) fn.name fn.as fn.rs xs m Q X ?_
    exact ⟨List.mem_map_of_mem hmem_c, fn, hmem_c, rfl, rfl, rfl, hwp_M⟩

private theorem acycChunk_rtC0CoreEnv_le_semChunks {T : Target} {lt : LegalTarget} :
    ∀ (chunks : List (CompiledChunk T lt rtExitSyms 64))
      (extSigs : List SigEntry) (Γprev : Env),
      checkChunksCalls rtExitSyms extSigs (chunks.map Chunk.acyc) = true →
      ((chunksFns chunks).map Fn.name ++ extSigs.map Prod.fst).Nodup →
      (∀ f ∈ chunksFns chunks, f ∈ rtC0CoreMod.fns) →
      (∀ f ∈ rtC0CoreMod.fns, f.sig ∈ extSigs →
        ∀ xs m Q X, rtC0CoreEnv f.name f.as f.rs xs m Q X → Γprev f.name f.as f.rs xs m Q X) →
      ∀ f ∈ rtC0CoreMod.fns, f.sig ∈ (chunksFns chunks).map Fn.sig ++ extSigs →
        ∀ xs m Q X, rtC0CoreEnv f.name f.as f.rs xs m Q X →
          semChunks extSigs Γprev (chunks.map Chunk.acyc) f.name f.as f.rs xs m Q X
  | [], extSigs, Γprev, _, _, _, hext_rt, f, hf_rt, hsig, xs, m, Q, X, hrt => by
    simp only [chunksFns, List.map_nil, List.nil_append, semChunks] at hsig ⊢
    exact hext_rt f hf_rt hsig xs m Q X hrt
  | c :: cs, extSigs, Γprev, hcalls, hnd, hsub, hext_rt, f, hf_rt, hsig, xs, m, Q, X, hrt => by
    simp only [List.map_cons, checkChunksCalls, Bool.and_eq_true] at hcalls
    have hc_acyc : (⟨c.fs, externsOfSigs extSigs, rtExitSyms⟩ : Module).checkAcyclic = true := by
      simpa [Chunk.callsOk] using hcalls.1
    dsimp only [chunksFns] at hnd hsub hsig
    simp only [List.map_append] at hnd hsig
    have hnd1 := List.nodup_append.mp hnd
    have hnd_fns := List.nodup_append.mp hnd1.1
    have hnd_c_ext : (c.fs.map Fn.name ++ extSigs.map Prod.fst).Nodup :=
      List.nodup_append.mpr ⟨hnd_fns.1, hnd1.2.1,
        fun a ha b hb he => hnd1.2.2 a (List.mem_append_left _ ha) b hb he⟩
    have hc_sub : ∀ g ∈ c.fs, g ∈ rtC0CoreMod.fns := fun g hg =>
      hsub g (List.mem_append_left _ hg)
    have hcs_sub : ∀ g ∈ chunksFns cs, g ∈ rtC0CoreMod.fns := fun g hg =>
      hsub g (List.mem_append_right _ hg)
    have hc_sem : ∀ g ∈ c.fs, ∀ xs' m' Q' X',
        rtC0CoreEnv g.name g.as g.rs xs' m' Q' X' →
        (Chunk.acyc c).sem extSigs Γprev g.name g.as g.rs xs' m' Q' X' := by
      intro g hg xs' m' Q' X' hg_rt
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
      exact Or.inl ⟨List.mem_map_of_mem (List.getElem_mem hi),
        acycChunk_rtC0CoreEnv_le_semScc c extSigs Γprev hc_acyc hnd_c_ext hc_sub hext_rt
          i hi xs' m' Q' X' hg_rt⟩
    have hnd_step :
        ((chunksFns cs).map Fn.name ++ (c.fs.map Fn.sig ++ extSigs).map Prod.fst).Nodup := by
      rw [List.map_append, show (c.fs.map Fn.sig).map Prod.fst = c.fs.map Fn.name by
        simp [List.map_map, Function.comp_def, Fn.sig]]
      refine List.nodup_append.mpr ⟨hnd_fns.2.1, hnd_c_ext, fun a ha b hb he => ?_⟩
      rcases List.mem_append.mp hb with hb_c | hb_e
      · exact hnd_fns.2.2 b hb_c a ha he.symm
      · exact hnd1.2.2 a (List.mem_append_right _ ha) b hb_e he
    have hext_step : ∀ g ∈ rtC0CoreMod.fns, g.sig ∈ c.fs.map Fn.sig ++ extSigs →
        ∀ xs' m' Q' X', rtC0CoreEnv g.name g.as g.rs xs' m' Q' X' →
          (Chunk.acyc c).sem extSigs Γprev g.name g.as g.rs xs' m' Q' X' := by
      intro g hg_rt hg_sig xs' m' Q' X' hg_core
      rcases List.mem_append.mp hg_sig with hc_sig | he_sig
      · obtain ⟨g', hg', hgeq⟩ := List.mem_map.mp hc_sig
        have hname : g'.name = g.name := congrArg Prod.fst hgeq
        have hgf : g' = g := fn_eq_of_name_nodup' rtC0CoreMod_fns_names_nodup
          (hc_sub g' hg') hg_rt hname
        subst hgf
        exact hc_sem g' hg' xs' m' Q' X' hg_core
      · exact (Chunk.acyc c).sem_intro_ext he_sig (hext_rt g hg_rt he_sig xs' m' Q' X' hg_core)
    have hsig_step : f.sig ∈ (chunksFns cs).map Fn.sig ++ (c.fs.map Fn.sig ++ extSigs) := by
      rcases List.mem_append.mp hsig with h_l | h_e
      · rcases List.mem_append.mp h_l with h_c | h_cs
        · exact List.mem_append_right _ (List.mem_append_left _ h_c)
        · exact List.mem_append_left _ h_cs
      · exact List.mem_append_right _ (List.mem_append_right _ h_e)
    rw [List.map_cons, semChunks]
    change semChunks (c.fs.map Fn.sig ++ extSigs) ((Chunk.acyc c).sem extSigs Γprev)
      (cs.map Chunk.acyc) f.name f.as f.rs xs m Q X
    exact acycChunk_rtC0CoreEnv_le_semChunks cs (c.fs.map Fn.sig ++ extSigs)
      ((Chunk.acyc c).sem extSigs Γprev) hcalls.2 hnd_step hcs_sub hext_step
      f hf_rt hsig_step xs m Q X hrt

theorem rtC0CoreEnv_le_semChunks_acyc {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa} {maxB : Nat}
    (rtCert : LinkedCert T L lt hcl rtC0CoreMod [] rtExitSyms 64 maxB)
    (hcalls : checkChunksCalls rtExitSyms [] (rtCert.chunks.map Chunk.acyc) = true)
    (Γ₀ : Env) {f : Fn} (hf : f ∈ rtC0CoreMod.fns)
    {xs : Tup Val f.as} {m : Mem 64} {Q : Post f.rs} {X : XPost}
    (hrt : rtC0CoreEnv f.name f.as f.rs xs m Q X) :
    semChunks [] Γ₀ (rtCert.chunks.map Chunk.acyc) f.name f.as f.rs xs m Q X := by
  have hhp := checkLinkList_parts rtCert.linkCheck
  have hnd_fns := (List.nodup_append.mp hhp.2.2.2.1).1
  rw [← rtCert.fns_eq] at hnd_fns
  have hnd :
      ((chunksFns rtCert.chunks).map Fn.name ++ ([] : List SigEntry).map Prod.fst).Nodup := by
    simpa [← rtCert.fns_eq] using hnd_fns
  have hsub : ∀ g ∈ chunksFns rtCert.chunks, g ∈ rtC0CoreMod.fns := by
    intro g hg; rw [rtCert.fns_eq]; exact hg
  have hsig : f.sig ∈ (chunksFns rtCert.chunks).map Fn.sig ++ [] := by
    rw [List.append_nil, ← rtCert.fns_eq]; exact List.mem_map_of_mem hf
  exact acycChunk_rtC0CoreEnv_le_semChunks rtCert.chunks [] Γ₀ hcalls hnd hsub
    (fun _ _ h => nomatch h) f hf hsig xs m Q X hrt

/-! ## 4. `BudgetEnv.semScc` Bridge (`lowerModule_budgetSemScc`) -/

private theorem lowerModule_budget_wp_mono :
    BudgetFn.EvalMono (fun Γcall _ bfn => Func.wp Γcall bfn.toFn.body) :=
  fun bfn _ _ _ _ hC _ xs m _ _ hwp => wp_env_mono hC (bfn.toFn.body Val Cont xs) m hwp

theorem mem_sccChunksSigAcc_of_mem_ext {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} :
    ∀ (cs : List (Chunk T lt exits nX)) (extSigs : List SigEntry) {s : SigEntry},
      s ∈ extSigs → s ∈ sccChunksSigAcc extSigs cs
  | [], _, _, hs => hs
  | c :: cs, extSigs, _, hs =>
    mem_sccChunksSigAcc_of_mem_ext cs (c.fns.map Fn.sig ++ extSigs) (List.mem_append_right _ hs)

theorem mem_sccChunksSigAcc_of_mem_fns {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} :
    ∀ (cs : List (Chunk T lt exits nX)) (extSigs : List SigEntry) {f : Fn},
      f ∈ sccChunksFns cs → f.sig ∈ sccChunksSigAcc extSigs cs
  | [], _, _, hf => nomatch hf
  | c :: cs, extSigs, f, hf => by
    dsimp only [sccChunksFns] at hf
    dsimp only [sccChunksSigAcc]
    rcases List.mem_append.mp hf with h_c | h_cs
    · exact mem_sccChunksSigAcc_of_mem_ext cs (c.fns.map Fn.sig ++ extSigs)
        (List.mem_append_left _ (List.mem_map_of_mem h_c))
    · exact mem_sccChunksSigAcc_of_mem_fns cs (c.fns.map Fn.sig ++ extSigs) h_cs

private theorem decl_eq_of_mangle_nodup {ds : List LcDecl}
    (hnd : (ds.map (fun d => mangleLc d.name)).Nodup)
    {d₁ d₂ : LcDecl} (h1 : d₁ ∈ ds) (h2 : d₂ ∈ ds)
    (hm : mangleLc d₁.name = mangleLc d₂.name) : d₁ = d₂ := by
  induction ds with
  | nil => cases h1
  | cons a rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp h1 with rfl | h1' <;> rcases List.mem_cons.mp h2 with rfl | h2'
    · rfl
    · exact absurd ⟨d₂, h2', hm.symm⟩ hnd.1
    · exact absurd ⟨d₁, h1', hm⟩ hnd.1
    · exact ih hnd.2 h1' h2'

private theorem rtCoreCallSigs_subset_rtMod :
    rtCoreCallSigs.all (fun s => decide (s ∈ rtC0CoreMod.fns.map Fn.sig)) = true := by
  decide

private theorem find_name_eq_some_of_nodup' :
    ∀ {xs : List LcDecl}, (xs.map (·.name)).Nodup → ∀ {d : LcDecl},
      d ∈ xs → xs.find? (·.name == d.name) = some d
  | [], _, _, hd => by cases hd
  | a :: rest, hn, d, hd => by
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp hd with rfl | hd'
    · simp [List.find?]
    · have hne : a.name ≠ d.name := fun heq => hn.1 (heq ▸ List.mem_map_of_mem hd')
      simp only [List.find?, beq_false_of_ne hne]
      exact find_name_eq_some_of_nodup' hn.2 hd'

private theorem func_wp_uncast {Γ : Env} {as₁ as₂ rs₁ rs₂ : List Ty} {body : Func as₁ rs₁}
    (ha : as₁ = as₂) (hr : rs₁ = rs₂)
    {xs : Tup Val as₁} {mem : Mem 64} {Q : Post rs₁} {X : XPost}
    (h : Func.wp Γ body (ha ▸ (ha ▸ xs)) mem (hr ▸ (hr ▸ Q)) X) :
    Func.wp Γ body xs mem Q X := by
  subst ha; subst hr; exact h

private theorem lowerDecl_budget_body {m : LcModule} {Δh : Nat → HEnv} {d : LcDecl}
    {tf : Frontend.C0.TFlatFn} {fnB : Fn} {Γcall : Env} {idx : Nat}
    (hfrag : m.inFirstOrderFragment = true) (hret : ∀ k, HEnv.RetTyped m (Δh k))
    (hmOk : HModuleOkIdx Δh m) (hndName : (m.decls.map (·.name)).Nodup)
    (hdMem : d ∈ m.decls) (hfragD : d.inFirstOrder m.decls = true)
    (hrtΓ : rtCoreCallEnv.le Γcall) (hΓlt : ∀ j, j < idx → HCallEnvOk m (Δh j) Γcall)
    (hlowD : lowerDecl (firstOrderLEnv m) d = .ok tf) (htfEq : tf.toFn = fnB)
    {ha : fnB.as = i64 :: (d.params.map (·.ty.toTTy)).take regArgs}
    {hr : fnB.rs = [d.retTy.toTTy]}
    {xs : Tup Val fnB.as} {mem : Mem 64} {Q : Post fnB.rs} {X : XPost}
    (hdl : liftDeclSpec (Δh idx d.name) d.params d.retTy (ha ▸ xs) mem (hr ▸ Q) X) :
    Func.wp Γcall fnB.body xs mem Q X := by
  subst htfEq
  refine func_wp_uncast ha hr ?_
  cases hself : hasSelfTail d.name d.params.length d.body with
  | false =>
    cases idx with
    | zero =>
      have hΓ0 : HCallEnvOk m HEnv.bot Γcall := HCallEnvOk_bot hrtΓ
      exact lowerDecl_sound_spec hfrag hΓ0 (HEnv.RetTyped_bot m) hfragD hself
        hlowD (fun rt as σ Q' X' hinv hpm hs => hmOk.2 0 d hdMem rt as σ Q' X' hinv hpm hs)
        hdl ha hr
    | succ k' =>
      exact lowerDecl_sound_spec hfrag (hΓlt k' (Nat.lt_succ_self k')) (hret k')
        hfragD hself hlowD
        (fun rt as σ Q' X' hinv hpm hs => hmOk.2 (k' + 1) d hdMem rt as σ Q' X' hinv hpm hs)
        hdl ha hr
  | true =>
    exact lowerDecl_sound_loop hfrag hrtΓ hΓlt (fun j _ => hret j) hfragD
      (find_name_eq_some_of_nodup' hndName hdMem) hself hlowD
      (fun j _ rt as σ Q' X' hinv hpm hs => hmOk.2 j d hdMem rt as σ Q' X' hinv hpm hs)
      hdl ha hr

private theorem lowerModule_budgetStep_helper {m : LcModule} {Δh : Nat → HEnv}
    (hfrag : m.inFirstOrderFragment = true) (hret : ∀ k, HEnv.RetTyped m (Δh k))
    (hmOk : HModuleOkIdx Δh m) (reqBudget : Nat → Nat)
    (BM : BudgetModule) (extSigs : List SigEntry) (Γext : Env)
    (hext_eq : BM.externs = externsOfSigs extSigs)
    (hrt_ext : ∀ f as bs, (f, as, bs) ∈ rtCoreCallSigs →
      (f, as, bs) ∈ extSigs ∧
      ∀ xs mem Q X, rtC0CoreEnv f as bs xs mem Q X → Γext f as bs xs mem Q X)
    (hmap : ∀ bfn ∈ BM.fns, ∃ d ∈ m.decls, ∃ tf,
      lowerDecl (firstOrderLEnv m) d = .ok tf ∧ tf.toFn = bfn.toFn)
    (hreq : ∀ bfn ∈ BM.fns, ∀ k sb, reqBudget k ≤ sb →
      bfn.maxFrame ≤ sb ∧ bfn.minEntry ≤ sb ∧
      ∀ j, j < k → reqBudget j ≤ sb - bfn.maxFrame)
    (hother : ∀ j, ∀ d ∈ m.decls,
      (mangleLc d.name, i64 :: (d.params.map (·.ty.toTTy)).take regArgs, [d.retTy.toTTy]) ∈
        BM.fnSigs ∨
      (∀ xs mem Q X, liftDeclSpec (Δh j d.name) d.params d.retTy xs mem Q X →
        (mangleLc d.name, i64 :: (d.params.map (·.ty.toTTy)).take regArgs, [d.retTy.toTTy]) ∈
          extSigs ∧
        Γext (mangleLc d.name) (i64 :: (d.params.map (·.ty.toTTy)).take regArgs) [d.retTy.toTTy]
          xs mem Q X)) :
    ∀ k sb, reqBudget k ≤ sb →
      ∀ bfn ∈ BM.fns,
        ∀ xs mem Q X,
          liftEnv m (Δh k) bfn.toFn.name bfn.toFn.as bfn.toFn.rs xs mem Q X →
          BudgetEnv.semScc BM Γext sb bfn.toFn.name bfn.toFn.as bfn.toFn.rs xs mem Q X := by
  let S : Nat → Env := fun k => liftEnv m (Δh k)
  have hndName : (m.decls.map (·.name)).Nodup := mod_nodup_of_inFirstOrder hfrag
  have hndMangle : (m.decls.map (fun d => mangleLc d.name)).Nodup := by
    have hf := hfrag
    simp only [LcModule.inFirstOrderFragment, Bool.and_eq_true] at hf
    exact nodup_of_symsNodup hf.1.2
  have hfragD : ∀ d ∈ m.decls, d.inFirstOrder m.decls = true := fun d hd => by
    have hf := hfrag
    simp only [LcModule.inFirstOrderFragment, Bool.and_eq_true, List.all_eq_true] at hf
    exact hf.2 d hd
  have hres := BudgetEnv.lfp_wf_mkSccOp (lt := Nat.lt) Nat.lt_wfRel.wf reqBudget BM
    (BudgetEnv.const Γext) lowerModule_budget_wp_mono S
    (fun idx sb hsb bfn hbfn Γcall _ hcall hcext _ _ xs mem Q X hS => by
      have ⟨hmax, hmin, hsub⟩ := hreq bfn hbfn idx sb hsb
      refine ⟨hmax, hmin, ?_⟩
      obtain ⟨d, hdMem, tf, hlowD, htfEq⟩ := hmap bfn hbfn
      have hsig : tf.toFn.name = mangleLc d.name ∧
          tf.toFn.as = i64 :: (d.params.map (·.ty.toTTy)).take regArgs ∧
          tf.toFn.rs = [d.retTy.toTTy] := lowerDecl_sig hlowD
      rcases hS with ⟨d', hd'Mem, hnm', ha, hr, hdl⟩
      have hnm_eq : mangleLc d'.name = mangleLc d.name :=
        hnm'.trans (by rw [← htfEq]; exact hsig.1)
      have hd_eq : d' = d := decl_eq_of_mangle_nodup hndMangle hd'Mem hdMem hnm_eq
      subst hd_eq
      have hrtΓ : rtCoreCallEnv.le Γcall := by
        intro f as bs xs' m' Q' X' ⟨hsig_rt, hcore⟩
        obtain ⟨hmem_ext, hΓext⟩ := hrt_ext f as bs hsig_rt
        exact hcext f as bs xs' m' Q' X'
          ⟨by rw [BudgetModule.extSigs, hext_eq, externsOfSigs_map_sig]; exact hmem_ext,
           hΓext xs' m' Q' X' hcore⟩
      have hΓlt : ∀ j, j < idx → HCallEnvOk m (Δh j) Γcall := by
        intro j hj
        refine ⟨?_, hrtΓ⟩
        intro sym as' bs' xs' m' Q' X' hlift
        rcases hlift with ⟨d₀, hd₀Mem, hsym₀, ha₀, hr₀, hdl₀⟩
        subst hsym₀; subst ha₀; subst hr₀
        rcases hother j d₀ hd₀Mem with hfnSig | hext_d
        · exact hcall j hj (hsub j hj) _ _ _ xs' m' Q' X'
            ⟨hfnSig, d₀, hd₀Mem, rfl, rfl, rfl, hdl₀⟩
        · obtain ⟨hmem_ext, hΓext⟩ := hext_d xs' m' Q' X' hdl₀
          exact hcext _ _ _ xs' m' Q' X'
            ⟨by rw [BudgetModule.extSigs, hext_eq, externsOfSigs_map_sig]; exact hmem_ext,
             hΓext⟩
      exact lowerDecl_budget_body hfrag hret hmOk hndName hdMem (hfragD d' hd'Mem)
        hrtΓ hΓlt hlowD htfEq hdl)
  intro k sb hsb bfn hbfn xs mem Q X hlift
  have hsig : bfn.toFn.sig ∈ BM.fnSigs := List.mem_map_of_mem hbfn
  exact hres k sb hsb bfn.toFn.name bfn.toFn.as bfn.toFn.rs xs mem Q X ⟨hsig, hlift⟩

/-! ## 5. Top-Level Target-Parametric `lean_fn_compiled_*` Theorems -/

/-- End-to-end verified compilation of a non-loop acyclic Lean function into machine code on any
target `T : Target` (`Amd64`, `Arm64`). Composes `perceus_sound`, `lowerModule_moduleOk`, and
`linkRtC0Cert_fnSpec_of_spec` with zero hand-written Tier-H or Tier-T WP. -/
theorem lean_fn_compiled_acyclic
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {m : LcModule} {progTfs : List Frontend.C0.TFlatFn} {maxB : Nat}
    (hfrag : m.inFirstOrderFragment = true)
    (hrc : RcCheck m = true) (hmwf : perceusModWf m = true)
    (hlow : lowerModule m = .ok progTfs)
    (hacyc : (linkLcnfWithRtC0 progTfs false).checkAcyclic = true)
    (hnoLoop : ∀ d ∈ m.decls, hasSelfTail d.name d.params.length d.body = false)
    {Δp : PEnv} (hp : PModuleOk Δp m)
    (cert : LinkedCert T L lt hcl (linkLcnfWithRtC0 progTfs false) [] rtExitSyms 64 maxB)
    (hleg : LegalSigAll lt (linkLcnfWithRtC0 progTfs false).fns)
    {d : LcDecl} (hd : d ∈ m.decls) {tf : Frontend.C0.TFlatFn} (htf : tf ∈ progTfs)
    (hlowD : lowerDecl (firstOrderLEnv m) d = .ok tf)
    {PreP : List PVal → Nat → Nat → Nat → Prop}
    {PostP : List PVal → PVal → Nat → Nat → Nat → Prop}
    {Δr : PResEnv} (hresOk : PResOk Δr m)
    (hpre : ∀ pvs rem₀ wr₀ rcr₀, PreP pvs rem₀ wr₀ rcr₀ →
      ∃ Qp Pr,
        Δp d.name pvs Qp (fun _ => False) ∧
        Δr d.name pvs rem₀ wr₀ rcr₀ Pr (fun _ _ _ _ => False) ∧
        (∀ r rem' wr' rcr', Qp r → Pr r rem' wr' rcr' → PostP pvs r rem' wr' rcr'))
    (ha : tf.toFn.as = i64 :: (d.params.map (·.ty.toTTy) |>.take regArgs) :=
      (lowerDecl_sig hlowD).2.1)
    (hr : tf.toFn.rs = [d.retTy.toTTy] := (lowerDecl_sig hlowD).2.2) :
    T.Defined cert.host tf.toFn.name ∧
      T.FnSpec cert.host tf.toFn.name
        (fun xs mem Q X => encDeclSpec d PreP PostP (ha ▸ xs) mem (hr ▸ Q) X)
        (cert.bound tf.toFn.name) 64 := by
  have hH : HModuleOk (hOfP m Δp) m := perceus_sound hrc hmwf hp
  have hmodOk := lowerModule_moduleOk hfrag hlow hacyc (hOfP_retTyped hfrag Δp) hH hnoLoop
  have hfProg : tf.toFn ∈ (lcnfProgMod progTfs).fns :=
    List.mem_map_of_mem htf
  have hsig := lowerDecl_sig hlowD
  have hwp : ∀ fn ∈ (lcnfProgMod progTfs).fns, ∀ xs mem Q X,
      liftEnv m (hOfP m Δp) fn.name fn.as fn.rs xs mem Q X →
      Func.wp (linkRtC0Env (liftEnv m (hOfP m Δp))) fn.body xs mem Q X := by
    intro fn hfn xs mem Q X hspec
    have hdisj : ¬fn.name ∈ rtCoreFnNames := by
      have hnd := linkLcnfWithRtC0_nodup_of_checkAcyclic hacyc
      exact lcnfProgMod_disjoint_rt_of_nodup hnd fn hfn
    have hfLink : fn ∈ (linkLcnfWithRtC0 progTfs false).fns := by
      rw [linkLcnfWithRtC0_fns_eq]; exact List.mem_append_right _ hfn
    obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp hfLink
    exact (hmodOk.fnsOk pre fn post hsplit).2.2 xs mem Q X
      ((linkRtC0Env_prog (liftEnv m (hOfP m Δp)) hdisj).mpr hspec)
  have hfLink : tf.toFn ∈ (linkLcnfWithRtC0 progTfs false).fns := by
    rw [linkLcnfWithRtC0_fns_eq]; exact List.mem_append_right _ hfProg
  have hdisj_tf : ¬tf.toFn.name ∈ rtCoreFnNames :=
    lcnfProgMod_disjoint_rt_of_nodup (linkLcnfWithRtC0_nodup_of_checkAcyclic hacyc) tf.toFn hfProg
  have ⟨hdef, hlegSpec⟩ := cert.fnSpec_host (linkRtC0Env (liftEnv m (hOfP m Δp))) hacyc
    (linkLcnfWithRtC0_fns_wf progTfs) (linkLcnfWithRtC0_wp_all _ hacyc hwp) hfLink
  have hsrc := fnSpec_of_legalEnv_legalSig_eq (hleg tf.toFn hfLink).1 (hleg tf.toFn hfLink).2
    (List.mem_append_left _ (List.mem_map_of_mem hfLink)) hlegSpec
  refine ⟨hdef, Target.FnSpec.of_spec T hsrc fun args mem Q X hspec => ?_⟩
  exact (linkRtC0Env_prog (liftEnv m (hOfP m Δp)) hdisj_tf).mpr
    (liftEnv_of_decl hd hsig.1 ha hr (encDeclSpec_le_liftHOfP hd hresOk hpre hspec))

/-- End-to-end verified compilation of a self-tail or acyclic Lean function into machine code
on any target `T : Target` (`Amd64`, `Arm64`), via `perceus_sound_idx` and
`lowerModule_moduleOk_idx`. -/
theorem lean_fn_compiled_loop
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {m : LcModule} {progTfs : List Frontend.C0.TFlatFn} {maxB : Nat}
    (hfrag : m.inFirstOrderFragment = true)
    (hrc : RcCheck m = true) (hmwf : perceusModWf m = true)
    (hlow : lowerModule m = .ok progTfs)
    (hacyc : (linkLcnfWithRtC0 progTfs false).checkAcyclic = true)
    {Δp : Nat → PEnv} (hp : PModuleOkIdx Δp m) (k : Nat)
    (cert : LinkedCert T L lt hcl (linkLcnfWithRtC0 progTfs false) [] rtExitSyms 64 maxB)
    (hleg : LegalSigAll lt (linkLcnfWithRtC0 progTfs false).fns)
    {d : LcDecl} (hd : d ∈ m.decls) {tf : Frontend.C0.TFlatFn} (htf : tf ∈ progTfs)
    (hlowD : lowerDecl (firstOrderLEnv m) d = .ok tf)
    {PreP : List PVal → Nat → Nat → Nat → Prop}
    {PostP : List PVal → PVal → Nat → Nat → Nat → Prop}
    {Δr : Nat → PResEnv} (hresOk : PResOkIdx Δr m)
    (hpre : ∀ pvs rem₀ wr₀ rcr₀, PreP pvs rem₀ wr₀ rcr₀ →
      ∃ Qp Pr,
        Δp k d.name pvs Qp (fun _ => False) ∧
        Δr k d.name pvs rem₀ wr₀ rcr₀ Pr (fun _ _ _ _ => False) ∧
        (∀ r rem' wr' rcr', Qp r → Pr r rem' wr' rcr' → PostP pvs r rem' wr' rcr'))
    (ha : tf.toFn.as = i64 :: (d.params.map (·.ty.toTTy) |>.take regArgs) :=
      (lowerDecl_sig hlowD).2.1)
    (hr : tf.toFn.rs = [d.retTy.toTTy] := (lowerDecl_sig hlowD).2.2) :
    T.Defined cert.host tf.toFn.name ∧
      T.FnSpec cert.host tf.toFn.name
        (fun xs mem Q X => encDeclSpec d PreP PostP (ha ▸ xs) mem (hr ▸ Q) X)
        (cert.bound tf.toFn.name) 64 := by
  have hH : HModuleOkIdx (hOfPIdx m Δp) m := perceus_sound_idx hrc hmwf hp
  have hmodOk := lowerModule_moduleOk_idx hfrag hlow hacyc
    (hOfPIdx_retTyped hfrag Δp) hH k
  have hfProg : tf.toFn ∈ (lcnfProgMod progTfs).fns := List.mem_map_of_mem htf
  have hsig := lowerDecl_sig hlowD
  have hwp : ∀ fn ∈ (lcnfProgMod progTfs).fns, ∀ xs mem Q X,
      liftEnv m (hOfPIdx m Δp k) fn.name fn.as fn.rs xs mem Q X →
      Func.wp (linkRtC0Env (liftEnv m (hOfPIdx m Δp k))) fn.body xs mem Q X := by
    intro fn hfn xs mem Q X hspec
    have hdisj : ¬fn.name ∈ rtCoreFnNames := by
      have hnd := linkLcnfWithRtC0_nodup_of_checkAcyclic hacyc
      exact lcnfProgMod_disjoint_rt_of_nodup hnd fn hfn
    have hfLink : fn ∈ (linkLcnfWithRtC0 progTfs false).fns := by
      rw [linkLcnfWithRtC0_fns_eq]; exact List.mem_append_right _ hfn
    obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp hfLink
    exact (hmodOk.fnsOk pre fn post hsplit).2.2 xs mem Q X
      ((linkRtC0Env_prog (liftEnv m (hOfPIdx m Δp k)) hdisj).mpr hspec)
  have hfLink : tf.toFn ∈ (linkLcnfWithRtC0 progTfs false).fns := by
    rw [linkLcnfWithRtC0_fns_eq]; exact List.mem_append_right _ hfProg
  have hdisj_tf : ¬tf.toFn.name ∈ rtCoreFnNames :=
    lcnfProgMod_disjoint_rt_of_nodup (linkLcnfWithRtC0_nodup_of_checkAcyclic hacyc) tf.toFn hfProg
  have ⟨hdef, hlegSpec⟩ := cert.fnSpec_host (linkRtC0Env (liftEnv m (hOfPIdx m Δp k))) hacyc
    (linkLcnfWithRtC0_fns_wf progTfs) (linkLcnfWithRtC0_wp_all _ hacyc hwp) hfLink
  have hsrc := fnSpec_of_legalEnv_legalSig_eq (hleg tf.toFn hfLink).1 (hleg tf.toFn hfLink).2
    (List.mem_append_left _ (List.mem_map_of_mem hfLink)) hlegSpec
  refine ⟨hdef, Target.FnSpec.of_spec T hsrc fun args mem Q X hspec => ?_⟩
  exact (linkRtC0Env_prog (liftEnv m (hOfPIdx m Δp k)) hdisj_tf).mpr
    (liftEnv_of_decl hd hsig.1 ha hr (encDeclSpec_le_liftHOfPIdx hd hresOk k hpre hspec))

private theorem semChunks_append' {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (cs₁ cs₂ : List (Chunk T lt exits nX)) (extSigs : List SigEntry) (Γ₀ : Env) :
    semChunks extSigs Γ₀ (cs₁ ++ cs₂) =
      semChunks (sccChunksSigAcc extSigs cs₁) (semChunks extSigs Γ₀ cs₁) cs₂ := by
  induction cs₁ generalizing extSigs Γ₀ with
  | nil => rfl
  | cons c rest ih =>
    simpa only [List.cons_append, semChunks, sccChunksSigAcc] using
      ih (c.fns.map Fn.sig ++ extSigs) (c.sem extSigs Γ₀)

private theorem sccChunksSigAcc_append {T : Target} {lt : LegalTarget} {exits : List Sym}
    {nX : Nat} (cs₁ cs₂ : List (Chunk T lt exits nX)) (extSigs : List SigEntry) :
    sccChunksSigAcc extSigs (cs₁ ++ cs₂) =
      sccChunksSigAcc (sccChunksSigAcc extSigs cs₁) cs₂ := by
  induction cs₁ generalizing extSigs with
  | nil => rfl
  | cons c rest ih => exact ih (c.fns.map Fn.sig ++ extSigs)

/-- End-to-end verified compilation of a recursive Lean function into native machine code on any
`T : Target` (`Amd64`, `Arm64`) backed by a closed `LinkedCertScc` whose runtime prefix is lifted
from a pre-verified `rtC0CoreMod` `LinkedCert` without recompiling the runtime. -/
theorem lean_fn_compiled_scc
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {linkedMod : Module} {maxBound maxBrt maxB : Nat}
    {ext : List (SigEntry × Nat)} {bfs : List BudgetFn}
    {hints : List T.toIsa.Hints} {exportBounds : List (Sym × Nat)}
    (cert : LinkedCertScc T L lt hcl linkedMod [] rtExitSyms 64 maxBound [])
    (rtCert : LinkedCert T L lt hcl rtC0CoreMod [] rtExitSyms 64 maxBrt)
    (hcalls_rt : checkChunksCalls rtExitSyms [] (rtCert.chunks.map Chunk.acyc) = true)
    (cbr : CompiledBudgetRec T lt ext rtExitSyms 64 bfs hints maxB exportBounds)
    (midChunks tailChunks : List (Chunk T lt rtExitSyms 64))
    (hchunks : cert.chunks =
      (rtCert.chunks.map Chunk.acyc ++ midChunks) ++
        Chunk.recBudgetSCC ext bfs hints maxB exportBounds cbr :: tailChunks)
    (hwf_linked : ∀ f ∈ linkedMod.fns, f.Wf)
    {m : LcModule} (hfrag : m.inFirstOrderFragment = true)
    (hrc : RcCheck m = true) (hmwf : perceusModWf m = true)
    {Δp : Nat → PEnv} (hp : PModuleOkIdx Δp m) (k : Nat)
    (reqBudget : Nat → Nat)
    (hmap : ∀ bfn ∈ bfs, ∃ d₀ ∈ m.decls, ∃ tf₀,
      lowerDecl (firstOrderLEnv m) d₀ = .ok tf₀ ∧ tf₀.toFn = bfn.toFn)
    (hreq : ∀ bfn ∈ bfs, ∀ idx sb, reqBudget idx ≤ sb →
      bfn.maxFrame ≤ sb ∧ bfn.minEntry ≤ sb ∧
      ∀ j, j < idx → reqBudget j ≤ sb - bfn.maxFrame)
    (hother : ∀ j, ∀ d₀ ∈ m.decls,
      (mangleLc d₀.name, i64 :: (d₀.params.map (·.ty.toTTy)).take regArgs, [d₀.retTy.toTTy]) ∈
        bfs.map (·.toFn.sig) ∨
      (∀ xs mem Q X, liftDeclSpec (hOfPIdx m Δp j d₀.name) d₀.params d₀.retTy xs mem Q X →
        (mangleLc d₀.name, i64 :: (d₀.params.map (·.ty.toTTy)).take regArgs, [d₀.retTy.toTTy]) ∈
          sccChunksSigAcc [] (rtCert.chunks.map Chunk.acyc ++ midChunks) ∧
        semChunks [] (fun _ _ _ _ _ _ _ => False) (rtCert.chunks.map Chunk.acyc ++ midChunks)
          (mangleLc d₀.name) (i64 :: (d₀.params.map (·.ty.toTTy)).take regArgs) [d₀.retTy.toTTy]
          xs mem Q X))
    {d : LcDecl} (hd : d ∈ m.decls) {tf : Frontend.C0.TFlatFn}
    (hlowD : lowerDecl (firstOrderLEnv m) d = .ok tf)
    {bfn : BudgetFn} (hbfn : bfn ∈ bfs) (htf : tf.toFn = bfn.toFn)
    (hf_linked : bfn.toFn ∈ linkedMod.fns)
    (hk_bound : reqBudget k ≤ cert.bound bfn.toFn.name)
    (hnot_after : bfn.toFn.name ∉ (sccChunksFns tailChunks).map Fn.name)
    (has : lt.legalSig bfn.toFn.as = bfn.toFn.as)
    (hrs : lt.legalSig bfn.toFn.rs = bfn.toFn.rs)
    {PreP : List PVal → Nat → Nat → Nat → Prop}
    {PostP : List PVal → PVal → Nat → Nat → Nat → Prop}
    {Δr : Nat → PResEnv} (hresOk : PResOkIdx Δr m)
    (hpre : ∀ pvs rem₀ wr₀ rcr₀, PreP pvs rem₀ wr₀ rcr₀ →
      ∃ Qp Pr,
        Δp k d.name pvs Qp (fun _ => False) ∧
        Δr k d.name pvs rem₀ wr₀ rcr₀ Pr (fun _ _ _ _ => False) ∧
        (∀ r rem' wr' rcr', Qp r → Pr r rem' wr' rcr' → PostP pvs r rem' wr' rcr'))
    (ha : bfn.toFn.as = i64 :: (d.params.map (·.ty.toTTy) |>.take regArgs) := by
      rw [← htf]; exact (lowerDecl_sig hlowD).2.1)
    (hr : bfn.toFn.rs = [d.retTy.toTTy] := by
      rw [← htf]; exact (lowerDecl_sig hlowD).2.2) :
    T.Defined cert.host bfn.toFn.name ∧
      T.FnSpec cert.host bfn.toFn.name
        (fun xs mem Q X => encDeclSpec d PreP PostP (ha ▸ xs) mem (hr ▸ Q) X)
        (cert.bound bfn.toFn.name) 64 := by
  let Δh := hOfPIdx m Δp
  have hH : HModuleOkIdx Δh m := perceus_sound_idx hrc hmwf hp
  let Γ₀ : Env := fun _ _ _ _ _ _ _ => False
  let pre := rtCert.chunks.map Chunk.acyc ++ midChunks
  let extSigs := sccChunksSigAcc [] pre
  let Γext := semChunks [] Γ₀ pre
  let chunk := Chunk.recBudgetSCC ext bfs hints maxB exportBounds cbr
  let BM : BudgetModule := ⟨bfs, externsOfSigs extSigs, rtExitSyms⟩
  have hnd_all := (List.nodup_append.mp (checkLinkSccList_parts cert.linkCheck).2.2.2.2.1).1
  have hnd_mid : ((sccChunksFns (rtCert.chunks.map Chunk.acyc)).map Fn.name ++
      (sccChunksFns midChunks).map Fn.name).Nodup := by
    rw [hchunks, sccChunksFns_append, sccChunksFns_append, List.map_append,
      List.map_append] at hnd_all
    exact (List.nodup_append.mp hnd_all).1
  have hdisj_rt_mid : ∀ f ∈ rtC0CoreMod.fns, f.name ∉ (sccChunksFns midChunks).map Fn.name := by
    intro f hf hm
    have hf_rt_scc : f ∈ sccChunksFns (rtCert.chunks.map Chunk.acyc) := by
      rw [show sccChunksFns (rtCert.chunks.map Chunk.acyc) = chunksFns rtCert.chunks from
        by induction rtCert.chunks with | nil => rfl | cons c cs ih =>
            simp [sccChunksFns, chunksFns, Chunk.fns, ih]]
      rw [← rtCert.fns_eq]; exact hf
    exact (List.nodup_append.mp hnd_mid).2.2 f.name (List.mem_map_of_mem hf_rt_scc) f.name hm rfl
  have hrt_ext : ∀ f as bs, (f, as, bs) ∈ rtCoreCallSigs →
      (f, as, bs) ∈ extSigs ∧
      ∀ xs mem Q X, rtC0CoreEnv f as bs xs mem Q X → Γext f as bs xs mem Q X := by
    intro f as bs hsig_rt
    have hmem_sig : (f, as, bs) ∈ rtC0CoreMod.fns.map Fn.sig :=
      decide_eq_true_iff.mp ((List.all_eq_true.mp rtCoreCallSigs_subset_rtMod) (f, as, bs) hsig_rt)
    obtain ⟨grt, hgrt, hgrt_sig⟩ := List.mem_map.mp hmem_sig
    have hgrt_scc : grt ∈ sccChunksFns (rtCert.chunks.map Chunk.acyc) := by
      rw [show sccChunksFns (rtCert.chunks.map Chunk.acyc) = chunksFns rtCert.chunks from
        by induction rtCert.chunks with | nil => rfl | cons c cs ih =>
            simp [sccChunksFns, chunksFns, Chunk.fns, ih]]
      rw [← rtCert.fns_eq]; exact hgrt
    have hsig_rtSigs : grt.sig ∈ sccChunksSigAcc [] (rtCert.chunks.map Chunk.acyc) :=
      mem_sccChunksSigAcc_of_mem_fns (rtCert.chunks.map Chunk.acyc) [] hgrt_scc
    have hsig_ext : grt.sig ∈ extSigs := by
      dsimp only [extSigs, pre]
      rw [sccChunksSigAcc_append]
      exact mem_sccChunksSigAcc_of_mem_ext midChunks _ hsig_rtSigs
    refine ⟨by change (f, as, bs) ∈ extSigs; rw [← hgrt_sig]; exact hsig_ext, ?_⟩
    intro xs mem Q X hrt
    have hsem_rt : semChunks [] Γ₀ (rtCert.chunks.map Chunk.acyc)
        grt.name grt.as grt.rs (by cases hgrt_sig; exact xs) mem
        (by cases hgrt_sig; exact Q) X :=
      rtC0CoreEnv_le_semChunks_acyc rtCert hcalls_rt Γ₀ hgrt
        (by cases hgrt_sig; exact hrt)
    dsimp only [Γext, pre]
    rw [semChunks_append']
    have hagree := semChunks_agree_earlier midChunks
      (sccChunksSigAcc [] (rtCert.chunks.map Chunk.acyc))
      (semChunks [] Γ₀ (rtCert.chunks.map Chunk.acyc)) (hdisj_rt_mid grt hgrt) hsig_rtSigs
    cases hgrt_sig
    exact (hagree xs mem Q X).mpr hsem_rt
  have hsem_budget := lowerModule_budgetStep_helper hfrag (hOfPIdx_retTyped hfrag Δp) hH
    reqBudget BM extSigs Γext rfl hrt_ext hmap hreq hother
  have hchunk_mem : chunk ∈ cert.chunks := by
    rw [hchunks]; exact List.mem_append_right _ List.mem_cons_self
  have hfn_mem_chunk : bfn.toFn ∈ chunk.fns := by
    dsimp only [chunk, Chunk.fns]; exact List.mem_map_of_mem hbfn
  have hbd_eq : cert.bound bfn.toFn.name = chunk.bound bfn.toFn.name :=
    cert.bound_eq_chunk hchunk_mem (List.mem_map_of_mem hfn_mem_chunk)
  have hbd_le : reqBudget k ≤ budgetBound exportBounds maxB bfn.toFn.name := by
    simpa [chunk, Chunk.bound, CompiledBudgetRec.bound, hbd_eq] using hk_bound
  refine cert.fnSpec_host_src_of_le hwf_linked hf_linked
    (fun xs mem Q X => encDeclSpec d PreP PostP (ha ▸ xs) mem (hr ▸ Q) X)
    has hrs (fun _ _ _ _ _ h => h) ?_
  intro xs mem Q X hspec
  have hsig := lowerDecl_sig hlowD
  have hdl : liftEnv m (Δh k) bfn.toFn.name bfn.toFn.as bfn.toFn.rs xs mem Q X :=
    liftEnv_of_decl hd (by rw [← htf]; exact hsig.1) ha hr
      (encDeclSpec_le_liftHOfPIdx hd hresOk k hpre hspec)
  dsimp only [LinkedCertScc.sem]
  rw [hchunks, semChunks_append']
  exact LinkedCertScc.semChunks_of_head hnot_after xs mem Q X
    (LinkedCertScc.recBudgetChunk_sem_of_budgetSemScc cbr hbfn hbd_le
      (hsem_budget k (reqBudget k) (Nat.le_refl _) bfn hbfn xs mem Q X hdl))

end LeanQbe.T.LeanLCNF.Sem
