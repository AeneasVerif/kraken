module

public import LeanQbe.T.MainCertCore

/-!
# Proof Helpers for `LinkedCert` (`MainCertProof`)

Pure, `Lean`-meta-free theorem helpers over `LeanQbe.T.MainCertCore`:
* `legalSigAll_nil`, `legalSigAll_append`;
* `LinkedCert` bound, host, label-uniqueness, exit, `FnSpec`, and `Eventually` lifts.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

theorem legalSigAll_nil {lt : LegalTarget} : LegalSigAll lt [] :=
  fun _ h => nomatch h

theorem legalSigAll_append {lt : LegalTarget} {fs₁ fs₂ : List Fn}
    (h₁ : checkLegalSigAll lt fs₁ = true) (h₂ : LegalSigAll lt fs₂) :
    LegalSigAll lt (fs₁ ++ fs₂) := by
  intro f hf
  rcases List.mem_append.mp hf with h1 | h2
  · exact legalSigAll_of_check h₁ f h1
  · exact h₂ f h2

namespace LinkedCert

variable {T : Target} {L : TargetLayout T} {lt : LegalTarget}
  {hcl : Rega.LabelClean T.toIsa} {mod : Module}
  {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}

theorem bound_le_max (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound) (nm : Sym) :
    cert.bound nm ≤ maxBound :=
  Nat.le_trans (cert.compiled.bound_le_max nm) cert.maxBound_le

theorem bound_eq_chunk (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound)
    {c : CompiledChunk T lt exits nX} (hc : c ∈ cert.chunks)
    {nm : Sym} (hnm : nm ∈ c.fs.map Fn.name) :
    cert.bound nm = c.compiled.bound nm :=
  linkCompiledList_bound cert.linkCheck hc hnm

theorem prog_host (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound) :
    T.mach.prog cert.host = cert.code ++ exits.map T.frame.label :=
  cert.compiled.prog_host

theorem code_infix_host (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound) :
    cert.code.IsInfixAt (T.mach.prog cert.host) 0 :=
  cert.compiled.code_infix_host

theorem labelsUnique (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound) :
    T.LabelsUnique cert.host :=
  cert.compiled.labelsUnique

theorem defined_exit_host (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound)
    {g : Sym} (hg : g ∈ exits) : T.Defined cert.host g :=
  cert.compiled.defined_exit_host hg

/-! ### Whole-module `FnSpec` lifts -/

/-- General module linking theorem over any host `h` containing `cert.code` at `k₀`. -/
theorem fnSpec (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    (hext : ∀ p ∈ ext₀,
      T.FnSpec h p.1.1 (legalEnv lt (Env.ofModule mod Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : (∀ p ∈ ext₀, ∀ q ∈ ext₀, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ ext₀, p.1.1 ∉ mod.fns.map Fn.name))
    (hexits : ∀ g ∈ exits, T.Defined h g) {f : Fn} (hf : f ∈ mod.fns) :
    T.Defined h f.name ∧ T.FnSpec h f.name
      (legalEnv lt (Env.ofModule mod Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
      (cert.bound f.name) nX :=
  cert.compiled.fnSpec mod cert.fns_eq h Γ k₀ hc hu hacyc hwf cert.supportsAll hwp
    hext hext_uniq hexits hf

/-- Whole-module `Defined` + `FnSpec` on `cert.host` via `linkCompiledList_fnSpec`. -/
theorem fnSpec_linked (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound)
    (Γ : Env) (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    (hext : ∀ p ∈ ext₀,
      T.FnSpec cert.host p.1.1 (legalEnv lt (Env.ofModule mod Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : (∀ p ∈ ext₀, ∀ q ∈ ext₀, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ ext₀, p.1.1 ∉ mod.fns.map Fn.name))
    {f : Fn} (hf : f ∈ mod.fns) :
    T.Defined cert.host f.name ∧ T.FnSpec cert.host f.name
      (legalEnv lt (Env.ofModule mod Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
      (cert.bound f.name) nX :=
  linkCompiledList_fnSpec hcl ext₀ cert.chunks cert.linkCheck mod cert.fns_eq Γ
    hacyc hwf cert.supportsAll hwp hext hext_uniq hf

/-- Self-contained `Defined` + `FnSpec` on `cert.host` when `ext₀ = []`. -/
theorem fnSpec_host (cert : LinkedCert T L lt hcl mod [] exits nX maxBound)
    (Γ : Env) (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {f : Fn} (hf : f ∈ mod.fns) :
    T.Defined cert.host f.name ∧ T.FnSpec cert.host f.name
      (legalEnv lt (Env.ofModule mod Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
      (cert.bound f.name) nX :=
  cert.fnSpec_linked Γ hacyc hwf hwp
    (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩ hf

/-- Source-level `Defined` + `FnSpec` on `cert.host` (`ext₀ = []`) when `lt.legalSig` fixes
`(f.as, f.rs)` and `Γ` ignores exit continuations. -/
theorem fnSpec_host_src (cert : LinkedCert T L lt hcl mod [] exits nX maxBound)
    (Γ : Env) (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {f : Fn} (hf : f ∈ mod.fns)
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X') :
    T.Defined cert.host f.name ∧
      T.FnSpec cert.host f.name (Γ f.name f.as f.rs) (cert.bound f.name) nX := by
  obtain ⟨hdef, hspec⟩ := cert.fnSpec_host Γ hacyc hwf hwp hf
  exact ⟨hdef, fnSpec_of_legalEnv_legalSig_eq_noExit has hrs
    (List.mem_append_left _ (List.mem_map_of_mem hf)) hnoex hspec⟩

/-- Source-level `Defined` + `FnSpec` on `cert.host` (`ext₀ = []`) given `LegalSigAll`. -/
theorem fnSpec_host_of_legalSigAll (cert : LinkedCert T L lt hcl mod [] exits nX maxBound)
    (Γ : Env) (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hleg : LegalSigAll lt mod.fns)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {f : Fn} (hf : f ∈ mod.fns)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X') :
    T.Defined cert.host f.name ∧
      T.FnSpec cert.host f.name (Γ f.name f.as f.rs) (cert.bound f.name) nX :=
  have ⟨has, hrs⟩ := hleg f hf
  cert.fnSpec_host_src Γ hacyc hwf hwp hf has hrs hnoex

/-- Drop-in replacement for `Compiled.fnSpec_noExit_id` over any host `h` containing `cert.code`
at `k₀` with unique labels (`ext₀ = []`, `exits = []`). -/
theorem fnSpec_noExit_id (cert : LinkedCert T L lt hcl mod [] [] nX maxBound)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {f : Fn} (hf : f ∈ mod.fns)
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X') :
    T.Defined h f.name ∧ T.FnSpec h f.name (Γ f.name f.as f.rs) (cert.bound f.name) nX :=
  cert.compiled.fnSpec_noExit_id mod cert.fns_eq h Γ k₀ hc hu hacyc hwf cert.supportsAll hwp
    hf has hrs hnoex

/-- Arbitrary-host `fnSpec_noExit_id` specialized with `LegalSigAll lt mod.fns`. -/
theorem fnSpec_noExit_of_legalSigAll (cert : LinkedCert T L lt hcl mod [] [] nX maxBound)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hleg : LegalSigAll lt mod.fns)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {f : Fn} (hf : f ∈ mod.fns)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X') :
    T.Defined h f.name ∧ T.FnSpec h f.name (Γ f.name f.as f.rs) (cert.bound f.name) nX :=
  have ⟨has, hrs⟩ := hleg f hf
  cert.fnSpec_noExit_id h Γ k₀ hc hu hacyc hwf hwp hf has hrs hnoex

/-- General module linking theorem accessed directly by index `i < mod.fns.length`. -/
theorem fnSpec_at_idx (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    (hext : ∀ p ∈ ext₀,
      T.FnSpec h p.1.1 (legalEnv lt (Env.ofModule mod Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : (∀ p ∈ ext₀, ∀ q ∈ ext₀, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ ext₀, p.1.1 ∉ mod.fns.map Fn.name))
    (hexits : ∀ g ∈ exits, T.Defined h g) {i : Nat} (hi : i < mod.fns.length) :
    T.Defined h (mod.fns[i]).name ∧ T.FnSpec h (mod.fns[i]).name
      (legalEnv lt (Env.ofModule mod Γ) (mod.fns[i]).name (lt.legalSig (mod.fns[i]).as)
        (lt.legalSig (mod.fns[i]).rs)) (cert.bound (mod.fns[i]).name) nX :=
  cert.fnSpec h Γ k₀ hc hu hacyc hwf hwp hext hext_uniq hexits (List.getElem_mem hi)

/-- Self-contained `Defined` + `FnSpec` on `cert.host` (`ext₀ = []`) accessed by index. -/
theorem fnSpec_host_at_idx (cert : LinkedCert T L lt hcl mod [] exits nX maxBound)
    (Γ : Env) (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {i : Nat} (hi : i < mod.fns.length) :
    T.Defined cert.host (mod.fns[i]).name ∧ T.FnSpec cert.host (mod.fns[i]).name
      (legalEnv lt (Env.ofModule mod Γ) (mod.fns[i]).name (lt.legalSig (mod.fns[i]).as)
        (lt.legalSig (mod.fns[i]).rs)) (cert.bound (mod.fns[i]).name) nX :=
  cert.fnSpec_host Γ hacyc hwf hwp (List.getElem_mem hi)

/-- Source-level `Defined` + `FnSpec` on `cert.host` (`ext₀ = []`) accessed by index. -/
theorem fnSpec_host_src_at_idx (cert : LinkedCert T L lt hcl mod [] exits nX maxBound)
    (Γ : Env) (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {i : Nat} (hi : i < mod.fns.length)
    (has : lt.legalSig (mod.fns[i]).as = (mod.fns[i]).as)
    (hrs : lt.legalSig (mod.fns[i]).rs = (mod.fns[i]).rs)
    (hnoex : ∀ (args : Tup Val _) (m : Mem 64) (Q : Post _) (X X' : XPost),
      Γ (mod.fns[i]).name (mod.fns[i]).as (mod.fns[i]).rs args m Q X →
      Γ (mod.fns[i]).name (mod.fns[i]).as (mod.fns[i]).rs args m Q X') :
    T.Defined cert.host (mod.fns[i]).name ∧
      T.FnSpec cert.host (mod.fns[i]).name (Γ (mod.fns[i]).name (mod.fns[i]).as (mod.fns[i]).rs)
        (cert.bound (mod.fns[i]).name) nX :=
  cert.fnSpec_host_src Γ hacyc hwf hwp (List.getElem_mem hi) has hrs hnoex

/-- Source-level `Defined` + `FnSpec` on `cert.host` (`ext₀ = []`) with `LegalSigAll` by index. -/
theorem fnSpec_host_sig_idx (cert : LinkedCert T L lt hcl mod [] exits nX maxBound)
    (Γ : Env) (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hleg : LegalSigAll lt mod.fns)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {i : Nat} (hi : i < mod.fns.length)
    (hnoex : ∀ (args : Tup Val _) (m : Mem 64) (Q : Post _) (X X' : XPost),
      Γ (mod.fns[i]).name (mod.fns[i]).as (mod.fns[i]).rs args m Q X →
      Γ (mod.fns[i]).name (mod.fns[i]).as (mod.fns[i]).rs args m Q X') :
    T.Defined cert.host (mod.fns[i]).name ∧
      T.FnSpec cert.host (mod.fns[i]).name (Γ (mod.fns[i]).name (mod.fns[i]).as (mod.fns[i]).rs)
        (cert.bound (mod.fns[i]).name) nX :=
  cert.fnSpec_host_of_legalSigAll Γ hacyc hwf hleg hwp (List.getElem_mem hi) hnoex

/-- Arbitrary-host `fnSpec_noExit_id` accessed by index (`ext₀ = []`, `exits = []`). -/
theorem fnSpec_noExit_id_at_idx (cert : LinkedCert T L lt hcl mod [] [] nX maxBound)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {i : Nat} (hi : i < mod.fns.length)
    (has : lt.legalSig (mod.fns[i]).as = (mod.fns[i]).as)
    (hrs : lt.legalSig (mod.fns[i]).rs = (mod.fns[i]).rs)
    (hnoex : ∀ (args : Tup Val _) (m : Mem 64) (Q : Post _) (X X' : XPost),
      Γ (mod.fns[i]).name (mod.fns[i]).as (mod.fns[i]).rs args m Q X →
      Γ (mod.fns[i]).name (mod.fns[i]).as (mod.fns[i]).rs args m Q X') :
    T.Defined h (mod.fns[i]).name ∧ T.FnSpec h (mod.fns[i]).name
      (Γ (mod.fns[i]).name (mod.fns[i]).as (mod.fns[i]).rs) (cert.bound (mod.fns[i]).name) nX :=
  cert.fnSpec_noExit_id h Γ k₀ hc hu hacyc hwf hwp (List.getElem_mem hi) has hrs hnoex

/-- Arbitrary-host `fnSpec_noExit_of_legalSigAll` accessed by index. -/
theorem fnSpec_noExit_sig_idx (cert : LinkedCert T L lt hcl mod [] [] nX maxBound)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hleg : LegalSigAll lt mod.fns)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {i : Nat} (hi : i < mod.fns.length)
    (hnoex : ∀ (args : Tup Val _) (m : Mem 64) (Q : Post _) (X X' : XPost),
      Γ (mod.fns[i]).name (mod.fns[i]).as (mod.fns[i]).rs args m Q X →
      Γ (mod.fns[i]).name (mod.fns[i]).as (mod.fns[i]).rs args m Q X') :
    T.Defined h (mod.fns[i]).name ∧ T.FnSpec h (mod.fns[i]).name
      (Γ (mod.fns[i]).name (mod.fns[i]).as (mod.fns[i]).rs) (cert.bound (mod.fns[i]).name) nX :=
  cert.fnSpec_noExit_of_legalSigAll h Γ k₀ hc hu hacyc hwf hleg hwp (List.getElem_mem hi) hnoex

/-! ### Concrete `TargetInit` `Eventually` lifts -/

section ConcreteInit

variable {maxStack maxMem : Nat}

/-- Run `nm` in `cert.host` from `I.initState (cert.bound nm) bsMem args` using `hf`. -/
theorem run_fnSpec (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound)
    (I : TargetInit T maxStack maxMem) {nm : Sym} {as bs : List Ty} {spec : Spec as bs}
    (hf : T.FnSpec cert.host nm spec (cert.bound nm) nX)
    (bsMem : List UInt8) (args : Tup Val as) (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs as).isSome = true) {Q : Post bs} {X : XPost}
    (hspec : spec args (bsMem.At 0x1000#64) Q X) {post : T.mach.State → Prop}
    (hpost : ∀ st,
      (T.mach.pc st = I.ra0 ∧ ∃ rets m', Q rets m' ∧ T.RetsIn rets (T.mach.data st) ∧
        (T.mach.mem (T.mach.data st) =⋆ Eq m' ⋆ T.Exit I.sp0 (cert.bound nm) ⋆
          Std.ExtHashMap.emp)) ∨
      (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64), X sym' cs xs m' ∧
        T.mach.pc st = T.mach.labelAddr cert.host sym' ∧ T.ArgsIn xs (T.mach.data st)) → post st)
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host) post
      (T.mach.mkState (I.initState (cert.bound nm) bsMem args) (T.mach.labelAddr cert.host nm)) :=
  I.run_fnSpec cert.compiled hf bsMem args hbs hargs hspec hpost
    (Nat.le_trans cert.maxBound_le hbound)

/-- Run a non-exiting function returning `(v, ()) : Tup Val [t]` in `cert.host`. -/
theorem run_ret1 (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound)
    (I : TargetInit T maxStack maxMem) {nm : Sym} {as : List Ty} {t : Ty} {spec : Spec as [t]}
    (hf : T.FnSpec cert.host nm spec (cert.bound nm) nX) (bsMem : List UInt8) (args : Tup Val as)
    (v : Val t) (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs as).isSome = true)
    {Q : Post [t]} (hspec : spec args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()))
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.RetsIn (bs := [t]) (v, ()) (T.mach.data st))
      (T.mach.mkState (I.initState (cert.bound nm) bsMem args) (T.mach.labelAddr cert.host nm)) :=
  I.run_ret1 cert.compiled hf bsMem args v hbs hargs hspec hQ
    (Nat.le_trans cert.maxBound_le hbound)

/-- `i64` specialization of `run_ret1` projecting directly to `I.ret0`. -/
theorem run_ret1_i64 (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound)
    (I : TargetInit T maxStack maxMem) {nm : Sym} {as : List Ty} {spec : Spec as [i64]}
    (hf : T.FnSpec cert.host nm spec (cert.bound nm) nX) (bsMem : List UInt8) (args : Tup Val as)
    (v : Val i64) (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs as).isSome = true)
    {Q : Post [i64]} (hspec : spec args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()))
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v)
      (T.mach.mkState (I.initState (cert.bound nm) bsMem args) (T.mach.labelAddr cert.host nm)) :=
  I.run_ret1_i64 cert.compiled hf bsMem args v hbs hargs hspec hQ
    (Nat.le_trans cert.maxBound_le hbound)

/-- Run a non-exiting function returning `(v, ()) : Tup Val [t]` and establishing heap `P`. -/
theorem run_ret1_sep (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound)
    (I : TargetInit T maxStack maxMem) {nm : Sym} {as : List Ty} {t : Ty} {spec : Spec as [t]}
    (hf : T.FnSpec cert.host nm spec (cert.bound nm) nX) (bsMem : List UInt8) (args : Tup Val as)
    (v : Val t) (P : Mem 64 → Prop) (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs as).isSome = true) {Q : Post [t]}
    (hspec : spec args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()) ∧ P m')
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.RetsIn (bs := [t]) (v, ()) (T.mach.data st) ∧
        (T.mach.mem (T.mach.data st) =⋆ P ⋆ T.Exit I.sp0 (cert.bound nm) ⋆ Std.ExtHashMap.emp))
      (T.mach.mkState (I.initState (cert.bound nm) bsMem args) (T.mach.labelAddr cert.host nm)) :=
  I.run_ret1_sep cert.compiled hf bsMem args v P hbs hargs hspec hQ
    (Nat.le_trans cert.maxBound_le hbound)

/-- `i64` specialization of `run_ret1_sep` projecting directly to `I.ret0`. -/
theorem run_ret1_sep_i64 (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound)
    (I : TargetInit T maxStack maxMem) {nm : Sym} {as : List Ty} {spec : Spec as [i64]}
    (hf : T.FnSpec cert.host nm spec (cert.bound nm) nX) (bsMem : List UInt8) (args : Tup Val as)
    (v : Val i64) (P : Mem 64 → Prop) (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs as).isSome = true) {Q : Post [i64]}
    (hspec : spec args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()) ∧ P m')
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v ∧
        (T.mach.mem (T.mach.data st) =⋆ P ⋆ T.Exit I.sp0 (cert.bound nm) ⋆ Std.ExtHashMap.emp))
      (T.mach.mkState (I.initState (cert.bound nm) bsMem args) (T.mach.labelAddr cert.host nm)) :=
  I.run_ret1_sep_i64 cert.compiled hf bsMem args v P hbs hargs hspec hQ
    (Nat.le_trans cert.maxBound_le hbound)

/-- One-shot end-to-end `Eventually` theorem from source module soundness to `cert.host`. -/
theorem eventually_fnSpec (cert : LinkedCert T L lt hcl mod [] exits nX maxBound)
    (I : TargetInit T maxStack maxMem) (Γ : Env)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {f : Fn} (hf : f ∈ mod.fns) (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X')
    (bsMem : List UInt8) (args : Tup Val f.as) (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs f.as).isSome = true) {Q : Post f.rs} {X : XPost}
    (hspec : Γ f.name f.as f.rs args (bsMem.At 0x1000#64) Q X) {post : T.mach.State → Prop}
    (hpost : ∀ st,
      (T.mach.pc st = I.ra0 ∧ ∃ rets m', Q rets m' ∧ T.RetsIn rets (T.mach.data st) ∧
        (T.mach.mem (T.mach.data st) =⋆ Eq m' ⋆ T.Exit I.sp0 (cert.bound f.name) ⋆
          Std.ExtHashMap.emp)) ∨
      (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64), X sym' cs xs m' ∧
        T.mach.pc st = T.mach.labelAddr cert.host sym' ∧ T.ArgsIn xs (T.mach.data st)) → post st)
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host) post
      (T.mach.mkState (I.initState (cert.bound f.name) bsMem args)
        (T.mach.labelAddr cert.host f.name)) :=
  cert.run_fnSpec I (cert.fnSpec_host_src Γ hacyc hwf hwp hf has hrs hnoex).2
    bsMem args hbs hargs hspec hpost hbound

/-- One-shot end-to-end `Eventually` for non-exiting `i64`-returning `f ∈ mod.fns` with `P`. -/
theorem eventually_ret1_sep_i64 (cert : LinkedCert T L lt hcl mod [] exits nX maxBound)
    (I : TargetInit T maxStack maxMem) (Γ : Env)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {f : Fn} (hf : f ∈ mod.fns) (hret : f.rs = [i64])
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X')
    (bsMem : List UInt8) (args : Tup Val f.as) (v : Val i64) (P : Mem 64 → Prop)
    (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs f.as).isSome = true)
    {Q : Post [i64]}
    (hspec : Γ f.name f.as [i64] args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()) ∧ P m')
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v ∧
        (T.mach.mem (T.mach.data st) =⋆ P ⋆ T.Exit I.sp0 (cert.bound f.name) ⋆ Std.ExtHashMap.emp))
      (T.mach.mkState (I.initState (cert.bound f.name) bsMem args)
        (T.mach.labelAddr cert.host f.name)) := by
  have hfn := (cert.fnSpec_host_src Γ hacyc hwf hwp hf has hrs hnoex).2
  rw [hret] at hfn
  exact cert.run_ret1_sep_i64 I hfn bsMem args v P hbs hargs hspec hQ hbound

/-- One-shot `eventually_ret1_sep_i64` specialized with `LegalSigAll lt mod.fns`. -/
theorem eventually_ret1_sep_i64_of_legalSigAll
    (cert : LinkedCert T L lt hcl mod [] exits nX maxBound)
    (I : TargetInit T maxStack maxMem) (Γ : Env)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hleg : LegalSigAll lt mod.fns)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {f : Fn} (hf : f ∈ mod.fns) (hret : f.rs = [i64])
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X')
    (bsMem : List UInt8) (args : Tup Val f.as) (v : Val i64) (P : Mem 64 → Prop)
    (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs f.as).isSome = true)
    {Q : Post [i64]}
    (hspec : Γ f.name f.as [i64] args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()) ∧ P m')
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v ∧
        (T.mach.mem (T.mach.data st) =⋆ P ⋆ T.Exit I.sp0 (cert.bound f.name) ⋆ Std.ExtHashMap.emp))
      (T.mach.mkState (I.initState (cert.bound f.name) bsMem args)
        (T.mach.labelAddr cert.host f.name)) :=
  have ⟨has, hrs⟩ := hleg f hf
  cert.eventually_ret1_sep_i64 I Γ hacyc hwf hwp hf hret has hrs hnoex
    bsMem args v P hbs hargs hspec hQ hbound

/-- One-shot end-to-end `Eventually` theorem for a non-exiting `i64`-returning `f ∈ mod.fns`. -/
theorem eventually_ret1_i64 (cert : LinkedCert T L lt hcl mod [] exits nX maxBound)
    (I : TargetInit T maxStack maxMem) (Γ : Env)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {f : Fn} (hf : f ∈ mod.fns) (hret : f.rs = [i64])
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X')
    (bsMem : List UInt8) (args : Tup Val f.as) (v : Val i64)
    (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs f.as).isSome = true)
    {Q : Post [i64]}
    (hspec : Γ f.name f.as [i64] args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()))
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v)
      (T.mach.mkState (I.initState (cert.bound f.name) bsMem args)
        (T.mach.labelAddr cert.host f.name)) :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1⟩)
    (cert.eventually_ret1_sep_i64 I Γ hacyc hwf hwp hf hret has hrs hnoex
      bsMem args v (fun _ => True) hbs hargs hspec
      (fun rets m' hm' => ⟨hQ rets m' hm', trivial⟩) hbound)

/-- One-shot `Eventually` theorem accessed by index `i < mod.fns.length`. -/
theorem eventually_fnSpec_at_idx (cert : LinkedCert T L lt hcl mod [] exits nX maxBound)
    (I : TargetInit T maxStack maxMem) (Γ : Env)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {i : Nat} (hi : i < mod.fns.length)
    (has : lt.legalSig (mod.fns[i]).as = (mod.fns[i]).as)
    (hrs : lt.legalSig (mod.fns[i]).rs = (mod.fns[i]).rs)
    (hnoex : ∀ (args : Tup Val _) (m : Mem 64) (Q : Post _) (X X' : XPost),
      Γ (mod.fns[i]).name (mod.fns[i]).as (mod.fns[i]).rs args m Q X →
      Γ (mod.fns[i]).name (mod.fns[i]).as (mod.fns[i]).rs args m Q X')
    (bsMem : List UInt8) (args : Tup Val (mod.fns[i]).as) (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs (mod.fns[i]).as).isSome = true)
    {Q : Post (mod.fns[i]).rs} {X : XPost}
    (hspec : Γ (mod.fns[i]).name (mod.fns[i]).as (mod.fns[i]).rs args (bsMem.At 0x1000#64) Q X)
    {post : T.mach.State → Prop}
    (hpost : ∀ st,
      (T.mach.pc st = I.ra0 ∧ ∃ rets m', Q rets m' ∧ T.RetsIn rets (T.mach.data st) ∧
        (T.mach.mem (T.mach.data st) =⋆ Eq m' ⋆ T.Exit I.sp0 (cert.bound (mod.fns[i]).name) ⋆
          Std.ExtHashMap.emp)) ∨
      (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64), X sym' cs xs m' ∧
        T.mach.pc st = T.mach.labelAddr cert.host sym' ∧ T.ArgsIn xs (T.mach.data st)) →
      post st)
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host) post
      (T.mach.mkState (I.initState (cert.bound (mod.fns[i]).name) bsMem args)
        (T.mach.labelAddr cert.host (mod.fns[i]).name)) :=
  cert.eventually_fnSpec I Γ hacyc hwf hwp (List.getElem_mem hi) has hrs hnoex
    bsMem args hbs hargs hspec hpost hbound

/-- One-shot `eventually_ret1_sep_i64` theorem accessed by index `i < mod.fns.length`. -/
theorem eventually_ret1_sep_idx (cert : LinkedCert T L lt hcl mod [] exits nX maxBound)
    (I : TargetInit T maxStack maxMem) (Γ : Env)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {i : Nat} (hi : i < mod.fns.length) (hret : (mod.fns[i]).rs = [i64])
    (has : lt.legalSig (mod.fns[i]).as = (mod.fns[i]).as)
    (hrs : lt.legalSig (mod.fns[i]).rs = (mod.fns[i]).rs)
    (hnoex : ∀ (args : Tup Val _) (m : Mem 64) (Q : Post _) (X X' : XPost),
      Γ (mod.fns[i]).name (mod.fns[i]).as (mod.fns[i]).rs args m Q X →
      Γ (mod.fns[i]).name (mod.fns[i]).as (mod.fns[i]).rs args m Q X')
    (bsMem : List UInt8) (args : Tup Val (mod.fns[i]).as) (v : Val i64) (P : Mem 64 → Prop)
    (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs (mod.fns[i]).as).isSome = true)
    {Q : Post [i64]}
    (hspec : Γ (mod.fns[i]).name (mod.fns[i]).as [i64] args (bsMem.At 0x1000#64) Q
      (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()) ∧ P m')
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v ∧
        (T.mach.mem (T.mach.data st) =⋆ P ⋆ T.Exit I.sp0 (cert.bound (mod.fns[i]).name) ⋆
          Std.ExtHashMap.emp))
      (T.mach.mkState (I.initState (cert.bound (mod.fns[i]).name) bsMem args)
        (T.mach.labelAddr cert.host (mod.fns[i]).name)) :=
  cert.eventually_ret1_sep_i64 I Γ hacyc hwf hwp (List.getElem_mem hi) hret has hrs hnoex
    bsMem args v P hbs hargs hspec hQ hbound

/-- One-shot `eventually_ret1_sep_i64_of_legalSigAll` accessed by index. -/
theorem eventually_ret1_sep_sig_idx (cert : LinkedCert T L lt hcl mod [] exits nX maxBound)
    (I : TargetInit T maxStack maxMem) (Γ : Env)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hleg : LegalSigAll lt mod.fns)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {i : Nat} (hi : i < mod.fns.length) (hret : (mod.fns[i]).rs = [i64])
    (hnoex : ∀ (args : Tup Val _) (m : Mem 64) (Q : Post _) (X X' : XPost),
      Γ (mod.fns[i]).name (mod.fns[i]).as (mod.fns[i]).rs args m Q X →
      Γ (mod.fns[i]).name (mod.fns[i]).as (mod.fns[i]).rs args m Q X')
    (bsMem : List UInt8) (args : Tup Val (mod.fns[i]).as) (v : Val i64) (P : Mem 64 → Prop)
    (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs (mod.fns[i]).as).isSome = true)
    {Q : Post [i64]}
    (hspec : Γ (mod.fns[i]).name (mod.fns[i]).as [i64] args (bsMem.At 0x1000#64) Q
      (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()) ∧ P m')
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v ∧
        (T.mach.mem (T.mach.data st) =⋆ P ⋆ T.Exit I.sp0 (cert.bound (mod.fns[i]).name) ⋆
          Std.ExtHashMap.emp))
      (T.mach.mkState (I.initState (cert.bound (mod.fns[i]).name) bsMem args)
        (T.mach.labelAddr cert.host (mod.fns[i]).name)) :=
  have ⟨has, hrs⟩ := hleg (mod.fns[i]) (List.getElem_mem hi)
  cert.eventually_ret1_sep_idx I Γ hacyc hwf hwp hi hret has hrs hnoex
    bsMem args v P hbs hargs hspec hQ hbound

/-- One-shot `eventually_ret1_i64` theorem accessed by index `i < mod.fns.length`. -/
theorem eventually_ret1_idx (cert : LinkedCert T L lt hcl mod [] exits nX maxBound)
    (I : TargetInit T maxStack maxMem) (Γ : Env)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {i : Nat} (hi : i < mod.fns.length) (hret : (mod.fns[i]).rs = [i64])
    (has : lt.legalSig (mod.fns[i]).as = (mod.fns[i]).as)
    (hrs : lt.legalSig (mod.fns[i]).rs = (mod.fns[i]).rs)
    (hnoex : ∀ (args : Tup Val _) (m : Mem 64) (Q : Post _) (X X' : XPost),
      Γ (mod.fns[i]).name (mod.fns[i]).as (mod.fns[i]).rs args m Q X →
      Γ (mod.fns[i]).name (mod.fns[i]).as (mod.fns[i]).rs args m Q X')
    (bsMem : List UInt8) (args : Tup Val (mod.fns[i]).as) (v : Val i64)
    (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs (mod.fns[i]).as).isSome = true)
    {Q : Post [i64]}
    (hspec : Γ (mod.fns[i]).name (mod.fns[i]).as [i64] args (bsMem.At 0x1000#64) Q
      (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()))
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v)
      (T.mach.mkState (I.initState (cert.bound (mod.fns[i]).name) bsMem args)
        (T.mach.labelAddr cert.host (mod.fns[i]).name)) :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1⟩)
    (cert.eventually_ret1_sep_idx I Γ hacyc hwf hwp hi hret has hrs hnoex
      bsMem args v (fun _ => True) hbs hargs hspec
      (fun rets m' hm' => ⟨hQ rets m' hm', trivial⟩) hbound)

end ConcreteInit

end LinkedCert

end LeanQbe.T
