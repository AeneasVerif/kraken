module

public import LeanQbe.T.MainLink
public import LeanQbe.T.MainLinkSplice
public import LeanQbe.T.MainSplice
public meta import Lean
public meta import LeanQbe.T.MainLink
public meta import LeanQbe.T.MainLinkSplice
public meta import LeanQbe.T.MainSplice

/-!
# Scalable Chunked Native Compilation Certificates (`MainCert`)

Target-parameterized (zero architecture imports) chunked compilation and linking certificate layer
built over `LeanQbe.T.MainLink` (`compileCheckedLit`, `linkCompiledList`, `linkCompiledList_fnSpec`)
and `LeanQbe.T.MainLinkSplice`:

* **Structural slice & chunk composition lemmas**: `drop_take_append_drop`, `slice_cons_eq`,
  `slice_last_eq`, `checkSupportsChunk`, `supportsAll_append`, `LegalSigAll`, `checkLegalSigAll`,
  `legalSigAll_of_check`, and `chunksMaxBound_cons` prove `mod.fns = chunksFns chunks`,
  `supportsSource`, `LegalSigAll`, and `chunksMaxBound ≤ maxBound` in `O(#chunks)` kernel steps
  without unfolding function bodies.
* **`LinkedCert`**: bundles the linked `CompiledChunk` list, O(N) metadata-only `checkLinkList`
  certificate, `mod.fns = chunksFns chunks`, chunk-composed `supportsSource`, and `maxBound` proof,
  exposing `compiled`, `host`, `code`, `bound`, whole-module `FnSpec` lifts (`fnSpec`,
  `fnSpec_linked`, `fnSpec_host`, `fnSpec_host_src`, `fnSpec_host_of_legalSigAll`,
  `fnSpec_noExit_id`, `fnSpec_noExit_of_legalSigAll`), and `TargetInit` `Eventually` lifts
  (`run_fnSpec`, `run_ret1`, `run_ret1_i64`, `run_ret1_sep`, `run_ret1_sep_i64`,
  `eventually_fnSpec`, `eventually_ret1`, `eventually_ret1_i64`, `eventually_ret1_sep`,
  `eventually_ret1_sep_i64`).
* **`compile_linked_chunks!`** (strictly `scoped` to `LeanQbe.T`): splits any acyclic `Module` into
  callee-first chunks of size `K`, evaluates hints and `compileModule` once in compiled meta code,
  splices literal `(ext, hints, code, bounds)` definitions, emits independent per-chunk kernel
  checks (`compileModule`, `checkCompileLit`, `checkSupportsChunk`) + O(N) `checkLinkList`, and
  binds the resulting `LinkedCert`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## 1. O(#chunks) list-slicing, `supportsSource`, `LegalSigAll`, & stack-bound helpers -/

/-- Adjacent slice identity used to reconstruct `mod.fns = chunksFns chunks` in O(#chunks) steps
without unfolding `mod.fns` or any `Fn.body`. -/
theorem drop_take_append_drop {α : Type _} (l : List α) (s k : Nat) :
    (l.drop s).take k ++ l.drop (s + k) = l.drop s := by
  have hdrop : l.drop (s + k) = (l.drop s).drop k := by
    rw [List.drop_drop, Nat.add_comm]
  rw [hdrop, List.take_append_drop]

/-- Inductive step for building `l.drop s = c_s ++ (c_{s+1} ++ ...)` along chunk boundaries. -/
theorem slice_cons_eq {α : Type _} {l rest : List α} {s k : Nat}
    (h : l.drop (s + k) = rest) :
    l.drop s = (l.drop s).take k ++ rest := by
  rw [← h, drop_take_append_drop]

/-- Terminal chunk identity closing the slice chain at `l.drop s`. -/
theorem slice_last_eq {α : Type _} (l : List α) (s : Nat) :
    l.drop s = l.drop s ++ [] :=
  (List.append_nil _).symm

/-- Kernel-reducible per-chunk `supportsSource` checker. -/
def checkSupportsChunk (lt : LegalTarget) (fs : List Fn) : Bool :=
  fs.all (fun f => (f.earlyOpt).body.supportsSource lt)

theorem supportsAll_nil {lt : LegalTarget} :
    ∀ f ∈ ([] : List Fn), (f.earlyOpt).body.supportsSource lt = true :=
  fun _ h => nomatch h

theorem supportsAll_append {lt : LegalTarget} {fs₁ fs₂ : List Fn}
    (h₁ : checkSupportsChunk lt fs₁ = true)
    (h₂ : ∀ f ∈ fs₂, (f.earlyOpt).body.supportsSource lt = true) :
    ∀ f ∈ fs₁ ++ fs₂, (f.earlyOpt).body.supportsSource lt = true := by
  intro f hf
  rcases List.mem_append.mp hf with h1 | h2
  · exact List.all_eq_true.mp h₁ f h1
  · exact h₂ f h2

theorem supportsAll_of_eq {lt : LegalTarget} {fs₁ fs₂ : List Fn} (heq : fs₁ = fs₂)
    (h : ∀ f ∈ fs₂, (f.earlyOpt).body.supportsSource lt = true) :
    ∀ f ∈ fs₁, (f.earlyOpt).body.supportsSource lt = true :=
  heq ▸ h

/-- Every function in `fs` has identity legalization (`lt.legalSig f.as = f.as` and
`lt.legalSig f.rs = f.rs`). -/
def LegalSigAll (lt : LegalTarget) (fs : List Fn) : Prop :=
  ∀ f ∈ fs, lt.legalSig f.as = f.as ∧ lt.legalSig f.rs = f.rs

/-- Kernel-reducible boolean checker for `LegalSigAll`. -/
def checkLegalSigAll (lt : LegalTarget) (fs : List Fn) : Bool :=
  fs.all (fun f => (lt.legalSig f.as == f.as) && (lt.legalSig f.rs == f.rs))

theorem legalSigAll_of_check {lt : LegalTarget} {fs : List Fn}
    (h : checkLegalSigAll lt fs = true) : LegalSigAll lt fs := by
  intro f hf
  have h' := List.all_eq_true.mp h f hf
  simp only [Bool.and_eq_true, beq_iff_eq] at h'
  exact h'

theorem legalSigAll_nil {lt : LegalTarget} : LegalSigAll lt [] :=
  fun _ h => nomatch h

theorem legalSigAll_append {lt : LegalTarget} {fs₁ fs₂ : List Fn}
    (h₁ : checkLegalSigAll lt fs₁ = true) (h₂ : LegalSigAll lt fs₂) :
    LegalSigAll lt (fs₁ ++ fs₂) := by
  intro f hf
  rcases List.mem_append.mp hf with h1 | h2
  · exact legalSigAll_of_check h₁ f h1
  · exact h₂ f h2

theorem chunksMaxBound_nil {T : Target} {lt : LegalTarget} {exits : List Sym} {nX B : Nat} :
    chunksMaxBound ([] : List (CompiledChunk T lt exits nX)) ≤ B :=
  Nat.zero_le B

theorem chunksMaxBound_cons {T : Target} {lt : LegalTarget} {exits : List Sym} {nX B : Nat}
    {c : CompiledChunk T lt exits nX} {cs : List (CompiledChunk T lt exits nX)}
    (hc : c.maxBound ≤ B) (hcs : chunksMaxBound cs ≤ B) :
    chunksMaxBound (c :: cs) ≤ B :=
  Nat.max_le.mpr ⟨hc, hcs⟩

theorem chunksFns_append {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (cs₁ cs₂ : List (CompiledChunk T lt exits nX)),
      chunksFns (cs₁ ++ cs₂) = chunksFns cs₁ ++ chunksFns cs₂
  | [], _ => rfl
  | c :: cs₁, cs₂ => by
    simp only [List.cons_append, chunksFns, chunksFns_append cs₁ cs₂, List.append_assoc]

theorem chunksMaxBound_append {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (cs₁ cs₂ : List (CompiledChunk T lt exits nX)),
      chunksMaxBound (cs₁ ++ cs₂) = Nat.max (chunksMaxBound cs₁) (chunksMaxBound cs₂)
  | [], cs₂ => by simp [chunksMaxBound]
  | c :: cs₁, cs₂ => by
    simp only [List.cons_append, chunksMaxBound, chunksMaxBound_append cs₁ cs₂, Nat.max_assoc]

/-! ## 2. `LinkedCert`: chunked literal-backed module compilation certificate -/

/-- Chunked, literal-backed native compilation and linking certificate for an acyclic `Module`
over any target `T`, layout `L`, legalization `lt`, and structural `LabelClean` proof `hcl`. -/
structure LinkedCert (T : Target) (L : TargetLayout T) (lt : LegalTarget)
    (hcl : Rega.LabelClean T.toIsa) (mod : Module)
    (ext₀ : List (SigEntry × Nat) := []) (exits : List Sym := []) (nX : Nat := 0)
    (maxBound : Nat := 2048) where
  chunks : List (CompiledChunk T lt exits nX)
  linkCheck : checkLinkList L ext₀ chunks = true
  fns_eq : mod.fns = chunksFns chunks
  supportsAll : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true
  maxBound_le : chunksMaxBound chunks ≤ maxBound

namespace LinkedCert

variable {T : Target} {L : TargetLayout T} {lt : LegalTarget}
  {hcl : Rega.LabelClean T.toIsa} {mod : Module}
  {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}

/-- Linked whole-module `Compiled` bundle built via `linkCompiledList` from `cert.chunks`. -/
def compiled (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound) :
    Compiled T lt ext₀ exits nX (chunksFns cert.chunks)
      (chunksHints cert.chunks) (chunksMaxBound cert.chunks) :=
  linkCompiledList L hcl ext₀ cert.chunks cert.linkCheck

/-- Linked machine-code host for the full module. -/
def host (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound) : T.mach.Host :=
  cert.compiled.host

/-- Concatenated literal directive stream of all linked chunks. -/
def code (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound) : List T.Directive :=
  cert.compiled.code

/-- Concatenated literal `(fnName, stackBound)` table of all linked chunks. -/
def bounds (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound) : List (Sym × Nat) :=
  cert.compiled.bounds

/-- Stack bound computed for function `nm` in `cert`. -/
def bound (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound) (nm : Sym) : Nat :=
  cert.compiled.bound nm

/-- Number of compiled chunks linked in `cert`. -/
def numChunks (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound) : Nat :=
  cert.chunks.length

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
      (T.mach.mkState (I.initState (cert.bound nm) bsMem args)
        (T.mach.labelAddr cert.host nm)) :=
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
      (T.mach.mkState (I.initState (cert.bound nm) bsMem args)
        (T.mach.labelAddr cert.host nm)) :=
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
      (T.mach.mkState (I.initState (cert.bound nm) bsMem args)
        (T.mach.labelAddr cert.host nm)) :=
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
      (T.mach.mkState (I.initState (cert.bound nm) bsMem args)
        (T.mach.labelAddr cert.host nm)) :=
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
      (T.mach.mkState (I.initState (cert.bound nm) bsMem args)
        (T.mach.labelAddr cert.host nm)) :=
  I.run_ret1_sep_i64 cert.compiled hf bsMem args v P hbs hargs hspec hQ
    (Nat.le_trans cert.maxBound_le hbound)

/-- One-shot end-to-end `Eventually` theorem from source module soundness to `cert.host` execution
for any function `f ∈ mod.fns` (`ext₀ = []`). -/
theorem eventually_fnSpec (cert : LinkedCert T L lt hcl mod [] exits nX maxBound)
    (I : TargetInit T maxStack maxMem) (Γ : Env)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {f : Fn} (hf : f ∈ mod.fns)
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
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

/-- One-shot end-to-end `Eventually` theorem for a non-exiting `i64`-returning `f ∈ mod.fns`
with final heap postcondition `P`. -/
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

end ConcreteInit

/-- Compositionally link two pre-verified `LinkedCert`s (for instance, compiled in parallel in
separate `.lean` modules) into a single whole-module `LinkedCert` using only O(N) metadata-only
`checkLinkList` validation. -/
def append {mod₁ mod₂ mod : Module} {ext₂ : List (SigEntry × Nat)} {maxB₁ maxB₂ : Nat}
    (c₁ : LinkedCert T L lt hcl mod₁ ext₀ exits nX maxB₁)
    (c₂ : LinkedCert T L lt hcl mod₂ ext₂ exits nX maxB₂)
    (hmod : mod.fns = mod₁.fns ++ mod₂.fns)
    (hchk : checkLinkList L ext₀ (c₁.chunks ++ c₂.chunks) = true) :
    LinkedCert T L lt hcl mod ext₀ exits nX (Nat.max maxB₁ maxB₂) where
  chunks := c₁.chunks ++ c₂.chunks
  linkCheck := hchk
  fns_eq := by
    rw [hmod, c₁.fns_eq, c₂.fns_eq, chunksFns_append]
  supportsAll := by
    intro f hf
    rw [hmod, List.mem_append] at hf
    rcases hf with h1 | h2
    · exact c₁.supportsAll f h1
    · exact c₂.supportsAll f h2
  maxBound_le := by
    rw [chunksMaxBound_append]
    exact Nat.max_le.mpr
      ⟨Nat.le_trans c₁.maxBound_le (Nat.le_max_left _ _),
       Nat.le_trans c₂.maxBound_le (Nat.le_max_right _ _)⟩

end LinkedCert

/-! ## 3. Meta chunk evaluator & `scoped` `compile_linked_chunks!` command elaborator -/

meta section

open Lean Elab Command Meta

/-- Meta-evaluated literal expressions for a single compiled chunk. -/
structure EvalChunkData where
  startIdx : Nat
  fnCount : Nat
  isLast : Bool
  extLit : Lean.Expr
  hintsLit : Lean.Expr
  codeLit : Lean.Expr
  boundsLit : Lean.Expr
  deriving Inhabited

/-- Output of `evalLinkedChunks`: per-chunk literal data plus the final accumulated `exportedExt`
literal (`sigBounds` of all chunks prepended onto `ext0`) for downstream `LinkedCert.append`. -/
structure EvalModuleData where
  chunks : List EvalChunkData
  finalExtLit : Lean.Expr
  deriving Inhabited

/-- Independent per-function meta prepass (`earlyOpt → supportsSource → legal → lateOpt →
`Spill.hints` → `mf.ext`), safe to evaluate across worker tasks before sequential bound linking. -/
def evalOneFnStage1 (I : Isa) (lt : LegalTarget) (f : Fn) :
    Except String (Sym × I.Hints × Fn × Rega.Ext) :=
  let ef := f.earlyOpt
  if !ef.body.supportsSource lt then
    .error s!"{f.name}: unsupported source op for target"
  else
    let mf := (ef.legal lt).lateOpt
    let h := Spill.hints I mf
    .ok (f.name, h, mf, mf.ext)

/-- Sequential callee stack-bound check over pre-evaluated `Spill.hints` and `Rega.Ext`. -/
def evalOneFnBoundCheck (I : Isa) (raBytes : Nat) (exits : List Sym) (nX maxBound : Nat)
    (acc : List (SigEntry × Nat)) (name : Sym) (h : I.Hints) (ext : Rega.Ext) :
    Except String Nat :=
  match checkAndBoundExt I raBytes exits nX acc h ext with
  | some b =>
    if !Nat.ble b maxBound then
      .error s!"{name}: stack bound {b} exceeds maxBound={maxBound}"
    else
      .ok b
  | none => .error s!"{name}: unknown callee, undeclared exit, or stack overflow"

/-- Bound-only `Type 0` stage-1 prepass (drops `Fn` body immediately so tasks retain no ASTs). -/
def evalOneFnBoundStage1 (I : Isa) (lt : LegalTarget) (f : Fn) :
    Except String (Sym × I.Hints × Rega.Ext × SigEntry) :=
  match evalOneFnStage1 I lt f with
  | .error e => .error e
  | .ok (nm, h, mf, ext) => .ok (nm, h, ext, mf.sig)

/-- Fast bound-only meta pass matching `evalOneFn`'s computed `(bound, sig)` without running
`Rega.lowerFn`. -/
def evalOneFnBound (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (exits : List Sym) (nX maxBound : Nat) (acc : List (SigEntry × Nat)) (f : Fn) :
    Except String (Nat × SigEntry) := do
  let (nm, h, ext, sig) ← evalOneFnBoundStage1 I lt f
  let b ← evalOneFnBoundCheck I raBytes exits nX maxBound acc nm h ext
  .ok (b, sig)

/-- Single-function fused meta pass: runs `earlyOpt`, checks `supportsSource`, runs
`legal → lateOpt` once, computes `Spill.hints`, lowers via `Rega.lowerFn`, and checks stack bounds
matching `compileModule` exactly without repeating `earlyOpt`/`mid`. -/
def evalOneFn (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (exits : List Sym) (nX maxBound : Nat) (acc : List (SigEntry × Nat)) (f : Fn) :
    Except String (I.Hints × List I.Directive × Nat × SigEntry) :=
  match evalOneFnStage1 I lt f with
  | .error e => .error e
  | .ok (nm, h, mf, ext) =>
    match Rega.lowerFn I h ext mf,
          evalOneFnBoundCheck I raBytes exits nX maxBound acc nm h ext with
    | .ok c, .ok b => .ok (h, c, b, mf.sig)
    | .error e, _ => .error s!"{nm}: {e}"
    | _, .error e => .error e

/-- Compiled meta evaluator splitting `fs` into callee-first chunks of at most `chunkSize`
functions (clamped to `≥ 1`) and, when `maxDirs > 0`, capping each multi-function chunk at
`maxDirs` emitted directives so heavy functions automatically receive dedicated single-function
chunks. Threads `sigBoundsOf` accumulators matching `checkChunksExt` and returns pure `Lean.Expr`
literals for every chunk. -/
def evalLinkedChunks (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (fs : List Fn) (chunkSize maxBound maxDirs : Nat)
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)] :
    Except String EvalModuleData := do
  let k := Nat.max chunkSize 1
  if fs.isEmpty then
    let (code, bounds) ← compileModule I lt raBytes ext0 exits nX [] []
    let extLit := Lean.toExpr ext0
    pure {
      chunks := [{
        startIdx := 0
        fnCount := 0
        isLast := true
        extLit := extLit
        hintsLit := Lean.toExpr ([] : List I.Hints)
        codeLit := Lean.toExpr code
        boundsLit := Lean.toExpr bounds
      }]
      finalExtLit := extLit
    }
  else
    -- First pass: compile every function once in parallel across worker threads, then resolve
    -- sequential callee bounds into `(name, hint, code, bound, sig)`.
    let tasks := fs.map fun f => Task.spawn fun () =>
      match evalOneFnStage1 I lt f with
      | .error e => .error e
      | .ok (nm, h, mf, ext) =>
        match Rega.lowerFn I h ext mf with
        | .ok c => .ok (nm, h, c, ext, mf.sig)
        | .error e => .error s!"{nm}: {e}"
    let rec compileAll (acc : List (SigEntry × Nat)) :
        List (Task (Except String (Sym × I.Hints × List I.Directive × Rega.Ext × SigEntry))) →
        Except String (List (Sym × I.Hints × List I.Directive × Nat × SigEntry))
      | [] => .ok []
      | t :: rest => do
        let (nm, h, c, ext, sig) ← t.get
        let b ← evalOneFnBoundCheck I raBytes exits nX maxBound acc nm h ext
        let tail ← compileAll ((sig, b) :: acc) rest
        pure ((nm, h, c, b, sig) :: tail)
    let compiled ← compileAll ext0 tasks
    -- Second pass: group into callee-first chunks honoring `chunkSize` and optional `maxDirs`.
    let rec takeChunk (cnt dirSum : Nat)
        (revChunk : List (Sym × I.Hints × List I.Directive × Nat × SigEntry)) :
        List (Sym × I.Hints × List I.Directive × Nat × SigEntry) →
        List (Sym × I.Hints × List I.Directive × Nat × SigEntry) ×
          List (Sym × I.Hints × List I.Directive × Nat × SigEntry)
      | [] => (revChunk.reverse, [])
      | x :: xs =>
        let nextDirs := dirSum + x.2.2.1.length
        if cnt < k && (maxDirs == 0 || nextDirs <= maxDirs) then
          takeChunk (cnt + 1) nextDirs (x :: revChunk) xs
        else
          (revChunk.reverse, x :: xs)
    let rec groupChunks : Nat → Nat → List (SigEntry × Nat) →
        List (Sym × I.Hints × List I.Directive × Nat × SigEntry) →
        List EvalChunkData → EvalModuleData
      | 0, _, acc, _, out => { chunks := out.reverse, finalExtLit := Lean.toExpr acc }
      | _, _, acc, [], out => { chunks := out.reverse, finalExtLit := Lean.toExpr acc }
      | fuel + 1, idx, acc, first :: rest, out =>
        let (grp, rest') := takeChunk 1 first.2.2.1.length [first] rest
        let isLast := rest'.isEmpty
        let hints := grp.map (fun x => x.2.1)
        let code := grp.foldr (fun x cs => x.2.2.1 ++ cs) []
        let bounds := grp.map (fun x => (x.1, x.2.2.2.1))
        let sigs := grp.map (fun x => (x.2.2.2.2, x.2.2.2.1))
        let entry : EvalChunkData := {
          startIdx := idx
          fnCount := grp.length
          isLast := isLast
          extLit := Lean.toExpr acc
          hintsLit := Lean.toExpr hints
          codeLit := Lean.toExpr code
          boundsLit := Lean.toExpr bounds
        }
        groupChunks fuel (idx + grp.length) (sigs ++ acc) rest' (entry :: out)
    pure (groupChunks (compiled.length + 1) 0 ext0 compiled [])

def addCertDef (declNm : Name) (ty val : Lean.Expr) : CoreM Unit :=
  withCurrHeartbeats do
    let decl := Declaration.defnDecl {
      name := declNm, levelParams := [], type := ty, value := val,
      hints := .abbrev, safety := .safe }
    addDecl decl (forceExpose := true)
    compileDecl decl

def addCertThm (declNm : Name) (ty val : Lean.Expr) : CoreM Unit :=
  withCurrHeartbeats do
    addDecl (Declaration.thmDecl {
      name := declNm, levelParams := [], type := ty, value := val })

def addKernelEqThm (declNm : Name) (eqTy lhs rhs : Lean.Expr) (u : Level) :
    CoreM Unit :=
  addCertThm declNm
    (mkApp3 (Lean.mkConst ``Eq [u.succ]) eqTy lhs rhs)
    (mkApp2 (Lean.mkConst ``Eq.refl [u.succ]) eqTy lhs)

structure CertInputs where
  targE : Lean.Expr
  layoutE : Lean.Expr
  ltE : Lean.Expr
  clE : Lean.Expr
  modE : Lean.Expr
  isaE : Lean.Expr
  raE : Lean.Expr
  labelE : Lean.Expr
  progSmallE : Lean.Expr
  dirTy : Lean.Expr
  listDirTy : Lean.Expr
  listHintsTy : Lean.Expr
  ext0E : Lean.Expr
  exitsE : Lean.Expr
  nXE : Lean.Expr
  maxBE : Lean.Expr
  chunks : List EvalChunkData
  finalExtLit : Lean.Expr

def parseCertOptions (optKeys : TSyntaxArray `ident) (optVals : TSyntaxArray `term) :
    CommandElabM (Option Term × Option Term × Option Term × Option Term × Option Term) := do
  let mut maxBT? : Option Term := none
  let mut extT? : Option Term := none
  let mut exitsT? : Option Term := none
  let mut nXT? : Option Term := none
  let mut maxDirsT? : Option Term := none
  for i in [:optKeys.size] do
    let k := optKeys[i]!.getId
    let v := optVals[i]!
    match k with
    | `maxBound => maxBT? := some v
    | `ext => extT? := some v
    | `exits => exitsT? := some v
    | `nX => nXT? := some v
    | `maxDirs => maxDirsT? := some v
    | _ =>
      throwErrorAt optKeys[i]!
        "compile_linked_chunks!: unknown option '{k}'; expected maxBound, ext, exits, nX, maxDirs"
  return (maxBT?, extT?, exitsT?, nXT?, maxDirsT?)

def elabAndEvalChunks (targT layoutT ltT clT modT : Term) (chunkSize : Nat)
    (maxBT? extT? exitsT? nXT? maxDirsT? : Option Term) : TermElabM CertInputs := do
  let targE ← Term.elabTerm targT (some (Lean.mkConst ``LeanQbe.T.Target))
  let layoutTy := mkApp (Lean.mkConst ``LeanQbe.T.TargetLayout) targE
  let layoutE ← Term.elabTerm layoutT (some layoutTy)
  let ltE ← Term.elabTerm ltT (some (Lean.mkConst ``LeanQbe.T.LegalTarget))
  let isaE := mkApp (Lean.mkConst ``LeanQbe.T.Target.toIsa) targE
  let clTy := mkApp (Lean.mkConst ``LeanQbe.T.Rega.LabelClean) isaE
  let clE ← Term.elabTerm clT (some clTy)
  let modE ← Term.elabTerm modT (some (Lean.mkConst ``LeanQbe.T.Module))
  let sigEntryNatTy :=
    mkApp2 (Lean.mkConst ``Prod [.zero, .zero])
      (Lean.mkConst ``LeanQbe.T.SigEntry) (Lean.mkConst ``Nat)
  let listExtTy := mkApp (Lean.mkConst ``List [.zero]) sigEntryNatTy
  let listSymTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.Sym)
  let ext0E ← match extT? with
    | some t => Term.elabTerm t (some listExtTy)
    | none => pure (mkApp (Lean.mkConst ``List.nil [.zero]) sigEntryNatTy)
  let exitsE ← match exitsT? with
    | some t => Term.elabTerm t (some listSymTy)
    | none => pure (mkApp (Lean.mkConst ``List.nil [.zero]) (Lean.mkConst ``LeanQbe.T.Sym))
  let nXE ← match nXT? with
    | some t => Term.elabTerm t (some (Lean.mkConst ``Nat))
    | none => pure (mkNatLit 0)
  let maxBE ← match maxBT? with
    | some t => Term.elabTerm t (some (Lean.mkConst ``Nat))
    | none => pure (mkNatLit 2048)
  let maxDirsE ← match maxDirsT? with
    | some t => Term.elabTerm t (some (Lean.mkConst ``Nat))
    | none => pure (mkNatLit 0)
  Term.synthesizeSyntheticMVarsNoPostponing
  let targE ← instantiateMVars targE
  let layoutE ← instantiateMVars layoutE
  let ltE ← instantiateMVars ltE
  let clE ← instantiateMVars clE
  let modE ← instantiateMVars modE
  let isaE ← instantiateMVars isaE
  let ext0E ← instantiateMVars ext0E
  let exitsE ← instantiateMVars exitsE
  let nXE ← instantiateMVars nXE
  let maxBE ← instantiateMVars maxBE
  let maxDirsE ← instantiateMVars maxDirsE
  let regTy ← whnf (mkApp (Lean.mkConst ``LeanQbe.T.Isa.Reg) isaE)
  let vregTy ← whnf (mkApp (Lean.mkConst ``LeanQbe.T.Isa.VReg) isaE)
  let condTy ← whnf (mkApp (Lean.mkConst ``LeanQbe.T.Isa.Cond) isaE)
  let hintTy := mkApp3 (Lean.mkConst ``LeanQbe.T.Hints) regTy vregTy condTy
  let listHintsConcreteTy := mkApp (Lean.mkConst ``List [.zero]) hintTy
  let dirConcreteTy ← whnf (mkApp (Lean.mkConst ``LeanQbe.T.Isa.Directive) isaE)
  let listDirConcreteTy := mkApp (Lean.mkConst ``List [.zero]) dirConcreteTy
  let toExprHintsInst ← synthInstance
    (mkApp (Lean.mkConst ``Lean.ToExpr [.zero]) listHintsConcreteTy)
  let toExprDirInst ← synthInstance
    (mkApp (Lean.mkConst ``Lean.ToExpr [.zero]) listDirConcreteTy)
  let frameE ← mkAppM ``LeanQbe.T.Isa.frame #[isaE]
  let raE ← mkAppM ``LeanQbe.T.FrameIsa.raBytes #[frameE]
  let labelE ← mkAppM ``LeanQbe.T.FrameIsa.label #[frameE]
  let progSmallE ← mkAppM ``LeanQbe.T.TargetLayout.progSmall #[layoutE]
  let fnsE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) modE
  let callE ← instantiateMVars (mkAppN (Lean.mkConst ``LeanQbe.T.evalLinkedChunks)
    #[isaE, ltE, raE, ext0E, exitsE, nXE, fnsE, mkNatLit chunkSize, maxBE, maxDirsE,
      toExprHintsInst, toExprDirInst])
  let outTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero]) (Lean.mkConst ``String)
    (Lean.mkConst ``LeanQbe.T.EvalModuleData)
  let evalRes ← unsafe evalExpr (Except String EvalModuleData) outTy callE
  let modData ← match evalRes with
    | .error e => throwError "compile_linked_chunks!: {e}"
    | .ok md => pure md
  let dirTy := mkApp (Lean.mkConst ``LeanQbe.T.Isa.Directive) isaE
  let listDirTy := mkApp (Lean.mkConst ``List [.zero]) dirTy
  let listHintsTy := mkApp (Lean.mkConst ``List [.zero])
    (mkApp (Lean.mkConst ``LeanQbe.T.Isa.Hints) isaE)
  return {
    targE, layoutE, ltE, clE, modE, isaE, raE, labelE, progSmallE,
    dirTy, listDirTy, listHintsTy, ext0E, exitsE, nXE, maxBE,
    chunks := modData.chunks, finalExtLit := modData.finalExtLit
  }

/-- `compile_linked_chunks! certName target layout legalTarget labelClean mod chunkSize
[(maxBound := ...)] [(ext := ...)] [(exits := ...)] [(nX := ...)] [(maxDirs := ...)]` splits
`mod.fns` into callee-first chunks of at most `chunkSize` functions (and optional `maxDirs`
directives), evaluates hints and `compileModule` in a single fused meta pass, splices literal
`(ext, hints, code, bounds)` per chunk, checks each chunk independently in the kernel
(`compileModule`, `checkCompileLit`, `checkSupportsChunk`), links all chunks via O(N)
metadata-only `checkLinkList`, and defines `certName : LinkedCert ...`. -/
scoped syntax "compile_linked_chunks! " ident
    term:arg term:arg term:arg term:arg term:arg num
    ("(" ident " := " term ")")* : command

scoped elab_rules : command
  | `(compile_linked_chunks! $certId $targT $layoutT $ltT $clT $modT $chunkSizeLit
      $[($optKeys := $optVals)]*) => do
    let ns ← getCurrNamespace
    let certNm := ns ++ certId.getId
    let auxNs := certNm ++ `aux
    let (maxBT?, extT?, exitsT?, nXT?, maxDirsT?) ← parseCertOptions optKeys optVals
    let inp ← liftTermElabM <|
      elabAndEvalChunks targT layoutT ltT clT modT chunkSizeLit.getNat
        maxBT? extT? exitsT? nXT? maxDirsT?
    let fnTy := Lean.mkConst ``LeanQbe.T.Fn
    let listFnTy := mkApp (Lean.mkConst ``List [1]) fnTy
    let symTy := Lean.mkConst ``LeanQbe.T.Sym
    let sigEntryNatTy :=
      mkApp2 (Lean.mkConst ``Prod [.zero, .zero])
        (Lean.mkConst ``LeanQbe.T.SigEntry) (Lean.mkConst ``Nat)
    let listExtTy := mkApp (Lean.mkConst ``List [.zero]) sigEntryNatTy
    let symNatTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) symTy (Lean.mkConst ``Nat)
    let listBoundsTy := mkApp (Lean.mkConst ``List [.zero]) symNatTy
    let okPairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) inp.listDirTy listBoundsTy
    let excTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero]) (Lean.mkConst ``String) okPairTy
    let fnsBaseE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) inp.modE
    -- Pass 1: emit all chunks' pure literal definitions (`fns`, `hints`, `ext`, `code`, `bounds`).
    let mut chunkNames : Array (Name × Name × Name × Name × Name × Name × Name × Name × Name ×
      EvalChunkData) := #[]
    let mut ci : Nat := 0
    for ch in inp.chunks do
      let pfx := s!"c{ci}"
      let fnsNm := auxNs ++ Name.mkSimple s!"{pfx}_fns"
      let hintsNm := auxNs ++ Name.mkSimple s!"{pfx}_hints"
      let extNm := auxNs ++ Name.mkSimple s!"{pfx}_ext"
      let codeNm := auxNs ++ Name.mkSimple s!"{pfx}_code"
      let boundsNm := auxNs ++ Name.mkSimple s!"{pfx}_bounds"
      let cmNm := auxNs ++ Name.mkSimple s!"{pfx}_cm"
      let metaNm := auxNs ++ Name.mkSimple s!"{pfx}_meta"
      let suppNm := auxNs ++ Name.mkSimple s!"{pfx}_supp"
      let compNm := auxNs ++ Name.mkSimple s!"{pfx}_compiled"
      let dropE := mkApp3 (Lean.mkConst ``List.drop [1]) fnTy (mkNatLit ch.startIdx) fnsBaseE
      let sliceE :=
        if ch.isLast then dropE
        else mkApp3 (Lean.mkConst ``List.take [1]) fnTy (mkNatLit ch.fnCount) dropE
      liftCoreM do
        addCertDef fnsNm listFnTy sliceE
        addCertDef hintsNm inp.listHintsTy ch.hintsLit
        addCertDef extNm listExtTy ch.extLit
        addCertDef codeNm inp.listDirTy ch.codeLit
        addCertDef boundsNm listBoundsTy ch.boundsLit
      chunkNames := chunkNames.push
        (fnsNm, hintsNm, extNm, codeNm, boundsNm, cmNm, metaNm, suppNm, compNm, ch)
      ci := ci + 1
    -- Pass 2: queue ALL per-chunk kernel theorems (`cm`, `meta`, `supp`) together so Lean's
    -- async kernel threadpool checks all chunks in parallel across CPU cores.
    for (fnsNm, hintsNm, extNm, codeNm, boundsNm, cmNm, metaNm, suppNm, _, _) in chunkNames do
      let cmLhs := mkAppN (Lean.mkConst ``LeanQbe.T.compileModule)
        #[inp.isaE, inp.ltE, inp.raE, Lean.mkConst extNm, inp.exitsE, inp.nXE,
          Lean.mkConst fnsNm, Lean.mkConst hintsNm]
      let cmRhs := mkApp3 (Lean.mkConst ``Except.ok [.zero, .zero])
        (Lean.mkConst ``String) okPairTy
        (mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) inp.listDirTy listBoundsTy
          (Lean.mkConst codeNm) (Lean.mkConst boundsNm))
      liftCoreM <| addKernelEqThm cmNm excTy cmLhs cmRhs .zero
      let fnNamesE := mkApp4 (Lean.mkConst ``List.map [1, .zero])
        fnTy symTy (Lean.mkConst ``LeanQbe.T.Fn.name) (Lean.mkConst fnsNm)
      let metaLhs := mkAppN (Lean.mkConst ``LeanQbe.T.checkCompileLit)
        #[inp.dirTy, inp.labelE, inp.progSmallE, Lean.mkConst codeNm, Lean.mkConst boundsNm,
          fnNamesE, inp.exitsE, inp.maxBE]
      liftCoreM <| addKernelEqThm metaNm (Lean.mkConst ``Bool)
        metaLhs (Lean.mkConst ``Bool.true) .zero
      let suppLhs := mkApp2 (Lean.mkConst ``LeanQbe.T.checkSupportsChunk)
        inp.ltE (Lean.mkConst fnsNm)
      liftCoreM <| addKernelEqThm suppNm (Lean.mkConst ``Bool)
        suppLhs (Lean.mkConst ``Bool.true) .zero
    -- Pass 3: assemble per-chunk `Compiled` bundles and `CompiledChunk` entries.
    let mut chunkEntries : List Lean.Expr := []
    for (fnsNm, hintsNm, extNm, codeNm, boundsNm, cmNm, metaNm, _, compNm, _) in chunkNames do
      let compTy := mkAppN (Lean.mkConst ``LeanQbe.T.Compiled)
        #[inp.targE, inp.ltE, Lean.mkConst extNm, inp.exitsE, inp.nXE,
          Lean.mkConst fnsNm, Lean.mkConst hintsNm, inp.maxBE]
      let compVal := mkAppN (Lean.mkConst ``LeanQbe.T.compileCheckedLit)
        #[inp.targE, inp.layoutE, inp.ltE, inp.clE, Lean.mkConst extNm, inp.exitsE, inp.nXE,
          Lean.mkConst fnsNm, Lean.mkConst hintsNm, inp.maxBE,
          Lean.mkConst codeNm, Lean.mkConst boundsNm, Lean.mkConst cmNm, Lean.mkConst metaNm]
      liftCoreM <| addCertDef compNm compTy compVal
      let chunkVal := mkAppN (Lean.mkConst ``LeanQbe.T.CompiledChunk.mk)
        #[inp.targE, inp.ltE, inp.exitsE, inp.nXE, Lean.mkConst extNm, Lean.mkConst fnsNm,
          Lean.mkConst hintsNm, inp.maxBE, Lean.mkConst compNm]
      chunkEntries := chunkEntries ++ [chunkVal]
    -- Emit linked chunk list and O(N) metadata-only link check
    let chunkTy := mkAppN (Lean.mkConst ``LeanQbe.T.CompiledChunk)
      #[inp.targE, inp.ltE, inp.exitsE, inp.nXE]
    let listChunkTy := mkApp (Lean.mkConst ``List [1]) chunkTy
    let chunksVal := chunkEntries.foldr
      (fun c acc => mkApp3 (Lean.mkConst ``List.cons [1]) chunkTy c acc)
      (mkApp (Lean.mkConst ``List.nil [1]) chunkTy)
    let chunksNm := auxNs ++ `chunks
    liftCoreM <| addCertDef chunksNm listChunkTy chunksVal
    let linkCheckNm := auxNs ++ `link_check
    let linkLhs := mkAppN (Lean.mkConst ``LeanQbe.T.checkLinkList)
      #[inp.targE, inp.layoutE, inp.ltE, inp.exitsE, inp.nXE, inp.ext0E, Lean.mkConst chunksNm]
    liftCoreM <| addKernelEqThm linkCheckNm (Lean.mkConst ``Bool)
      linkLhs (Lean.mkConst ``Bool.true) .zero
    -- Build O(#chunks) proofs of `mod.fns = chunksFns chunks`, `supportsAll`, and `maxBound_le`
    let fnsEqNm := auxNs ++ `fns_eq
    let suppAllNm := auxNs ++ `supportsAll
    let maxBLeNm := auxNs ++ `maxBound_le
    let chunksFnsE := mkAppN (Lean.mkConst ``LeanQbe.T.chunksFns)
      #[inp.targE, inp.ltE, inp.exitsE, inp.nXE, Lean.mkConst chunksNm]
    let fnsEqTy := mkApp3 (Lean.mkConst ``Eq [2]) listFnTy fnsBaseE chunksFnsE
    let mut fnsEqProof : Lean.Expr := default
    let mut restFnsE : Lean.Expr := mkApp (Lean.mkConst ``List.nil [1]) fnTy
    let mut suppProof : Lean.Expr := mkApp (Lean.mkConst ``LeanQbe.T.supportsAll_nil) inp.ltE
    let mut maxBProof : Lean.Expr := mkAppN (Lean.mkConst ``LeanQbe.T.chunksMaxBound_nil)
      #[inp.targE, inp.ltE, inp.exitsE, inp.nXE, inp.maxBE]
    let mut restChunksE : Lean.Expr := mkApp (Lean.mkConst ``List.nil [1]) chunkTy
    let nChunks := chunkNames.size
    for revIdx in [:nChunks] do
      let i := nChunks - 1 - revIdx
      let (fnsNm, _, _, _, _, _, _, suppNm, _, ch) := chunkNames[i]!
      let chunkVal := chunkEntries[i]!
      let curFnsE := Lean.mkConst fnsNm
      if revIdx == 0 then
        fnsEqProof := mkApp3 (Lean.mkConst ``LeanQbe.T.slice_last_eq [1])
          fnTy fnsBaseE (mkNatLit ch.startIdx)
      else
        fnsEqProof := mkApp6 (Lean.mkConst ``LeanQbe.T.slice_cons_eq [1])
          fnTy fnsBaseE restFnsE (mkNatLit ch.startIdx) (mkNatLit ch.fnCount) fnsEqProof
      suppProof := mkApp5 (Lean.mkConst ``LeanQbe.T.supportsAll_append)
        inp.ltE curFnsE restFnsE (Lean.mkConst suppNm) suppProof
      maxBProof := mkAppN (Lean.mkConst ``LeanQbe.T.chunksMaxBound_cons)
        #[inp.targE, inp.ltE, inp.exitsE, inp.nXE, inp.maxBE, chunkVal, restChunksE,
          mkApp (Lean.mkConst ``Nat.le_refl) inp.maxBE, maxBProof]
      restFnsE := mkApp3 (Lean.mkConst ``List.append [1]) fnTy curFnsE restFnsE
      restChunksE := mkApp3 (Lean.mkConst ``List.cons [1]) chunkTy chunkVal restChunksE
    -- Emit `fns_eq`, `supportsAll`, `maxBound_le`, and the final `LinkedCert`
    liftCoreM <| addCertThm fnsEqNm fnsEqTy fnsEqProof
    let (suppAllTy, suppAllVal, maxBLeProp) ← liftTermElabM do
      let sVal ← mkAppM ``LeanQbe.T.supportsAll_of_eq #[Lean.mkConst fnsEqNm, suppProof]
      let sTy ← inferType sVal
      let lhs := mkAppN (Lean.mkConst ``LeanQbe.T.chunksMaxBound)
        #[inp.targE, inp.ltE, inp.exitsE, inp.nXE, Lean.mkConst chunksNm]
      let mProp ← mkAppM ``LE.le #[lhs, inp.maxBE]
      return (← instantiateMVars sTy, ← instantiateMVars sVal, ← instantiateMVars mProp)
    liftCoreM do
      addCertThm suppAllNm suppAllTy suppAllVal
      addCertThm maxBLeNm maxBLeProp maxBProof
    let certTy := mkAppN (Lean.mkConst ``LeanQbe.T.LinkedCert)
      #[inp.targE, inp.layoutE, inp.ltE, inp.clE, inp.modE,
        inp.ext0E, inp.exitsE, inp.nXE, inp.maxBE]
    let certVal := mkAppN (Lean.mkConst ``LeanQbe.T.LinkedCert.mk)
      #[inp.targE, inp.layoutE, inp.ltE, inp.clE, inp.modE,
        inp.ext0E, inp.exitsE, inp.nXE, inp.maxBE,
        Lean.mkConst chunksNm, Lean.mkConst linkCheckNm, Lean.mkConst fnsEqNm,
        Lean.mkConst suppAllNm, Lean.mkConst maxBLeNm]
    liftCoreM do
      addCertDef certNm certTy certVal
      addCertDef (certNm ++ `exportedExt) listExtTy inp.finalExtLit

/-- Evaluates `evalOneFnBound` in order over `fs` starting from `ext0`, returning `(totalLen,
extLit)` where `extLit` is the literal `List (SigEntry × Nat)` expression `(sig, b) :: acc`
matching `compileModule`'s reverse accumulator order. -/
def evalPrefixExtWithLen (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX maxBound : Nat)
    (fs : List Fn) : Except String (Nat × Lean.Expr) := do
  let tasks := fs.map fun f => Task.spawn fun () => evalOneFnBoundStage1 I lt f
  let rec go (acc : List (SigEntry × Nat)) :
      List (Task (Except String (Sym × I.Hints × Rega.Ext × SigEntry))) →
      Except String (List (SigEntry × Nat))
    | [] => .ok acc
    | t :: rest => do
      let (nm, h, ext, sig) ← t.get
      let b ← evalOneFnBoundCheck I raBytes exits nX maxBound acc nm h ext
      go ((sig, b) :: acc) rest
  let out ← go ext0 tasks
  pure (out.length, Lean.toExpr out)

/-- Evaluates `evalOneFnBound` in order over `fs` starting from `ext0`, returning the literal
`List (SigEntry × Nat)` expression `(sig, b) :: acc` matching `compileModule`'s accumulator. -/
def evalPrefixExt (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX maxBound : Nat)
    (fs : List Fn) : Except String Lean.Expr :=
  Prod.snd <$> evalPrefixExtWithLen I lt raBytes ext0 exits nX maxBound fs

def parsePrefixExtOptions (optKeys : TSyntaxArray `ident) (optVals : TSyntaxArray `term) :
    CommandElabM (Option Term × Option Term × Option Term × Option Term × Option Ident) := do
  let mut maxBT? : Option Term := none
  let mut extT? : Option Term := none
  let mut exitsT? : Option Term := none
  let mut nXT? : Option Term := none
  let mut prefixId? : Option Ident := none
  for i in [:optKeys.size] do
    let k := optKeys[i]!.getId
    let v := optVals[i]!
    match k with
    | `maxBound => maxBT? := some v
    | `ext => extT? := some v
    | `exits => exitsT? := some v
    | `nX => nXT? := some v
    | `prefixDef =>
      if let `($id:ident) := v then
        prefixId? := some id
      else
        throwErrorAt v "eval_prefix_ext!: prefixDef must be an identifier"
    | _ =>
      throwErrorAt optKeys[i]!
        "eval_prefix_ext!: unknown option '{k}'; expected maxBound, ext, exits, nX, prefixDef"
  return (maxBT?, extT?, exitsT?, nXT?, prefixId?)

def elabAndEvalPrefixExt (targT ltT fnsT : Term)
    (maxBT? extT? exitsT? nXT? : Option Term) : TermElabM (Lean.Expr × Nat × Lean.Expr) := do
  let targE ← Term.elabTerm targT (some (Lean.mkConst ``LeanQbe.T.Target))
  let ltE ← Term.elabTerm ltT (some (Lean.mkConst ``LeanQbe.T.LegalTarget))
  let listFnTy := mkApp (Lean.mkConst ``List [1]) (Lean.mkConst ``LeanQbe.T.Fn)
  let fnsE ← Term.elabTerm fnsT (some listFnTy)
  let sigEntryNatTy :=
    mkApp2 (Lean.mkConst ``Prod [.zero, .zero])
      (Lean.mkConst ``LeanQbe.T.SigEntry) (Lean.mkConst ``Nat)
  let listExtTy := mkApp (Lean.mkConst ``List [.zero]) sigEntryNatTy
  let listSymTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.Sym)
  let ext0E ← match extT? with
    | some t => Term.elabTerm t (some listExtTy)
    | none => pure (mkApp (Lean.mkConst ``List.nil [.zero]) sigEntryNatTy)
  let exitsE ← match exitsT? with
    | some t => Term.elabTerm t (some listSymTy)
    | none => pure (mkApp (Lean.mkConst ``List.nil [.zero]) (Lean.mkConst ``LeanQbe.T.Sym))
  let nXE ← match nXT? with
    | some t => Term.elabTerm t (some (Lean.mkConst ``Nat))
    | none => pure (mkNatLit 0)
  let maxBE ← match maxBT? with
    | some t => Term.elabTerm t (some (Lean.mkConst ``Nat))
    | none => pure (mkNatLit 2048)
  Term.synthesizeSyntheticMVarsNoPostponing
  let targE ← instantiateMVars targE
  let ltE ← instantiateMVars ltE
  let fnsE ← instantiateMVars fnsE
  let ext0E ← instantiateMVars ext0E
  let exitsE ← instantiateMVars exitsE
  let nXE ← instantiateMVars nXE
  let maxBE ← instantiateMVars maxBE
  let isaE := mkApp (Lean.mkConst ``LeanQbe.T.Target.toIsa) targE
  let frameE ← mkAppM ``LeanQbe.T.Isa.frame #[isaE]
  let raE ← mkAppM ``LeanQbe.T.FrameIsa.raBytes #[frameE]
  let callE ← instantiateMVars (mkAppN (Lean.mkConst ``LeanQbe.T.evalPrefixExtWithLen)
    #[isaE, ltE, raE, ext0E, exitsE, nXE, maxBE, fnsE])
  let pairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero])
    (Lean.mkConst ``Nat) (Lean.mkConst ``Lean.Expr)
  let outTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero]) (Lean.mkConst ``String) pairTy
  let evalRes ← unsafe evalExpr (Except String (Nat × Lean.Expr)) outTy callE
  match evalRes with
  | .error e => throwError "eval_prefix_ext!: {e}"
  | .ok (total, extLit) => return (listExtTy, total, extLit)

/-- `eval_prefix_ext! extName target legalTarget fnsExpr [(ext := ...)] [(exits := ...)]
[(nX := ...)] [(maxBound := ...)] [(prefixDef := ...)]` runs `evalOneFnBound` in compiled meta
code over `fnsExpr` starting from `ext` (default `[]`) and emits `def extName : List (SigEntry ×
Nat) := <literal>` matching `compileModule`'s `(sig, bound) :: acc` reverse order. When
`(prefixDef := pfxName)` is supplied, also emits `def pfxName (k : Nat) : List (SigEntry × Nat) :=
extName.drop (total - k)` for `O(1)` prefix slicing across parallel certs. -/
scoped syntax "eval_prefix_ext! " ident
    term:arg term:arg term:arg
    ("(" ident " := " term ")")* : command

scoped elab_rules : command
  | `(eval_prefix_ext! $extId $targT $ltT $fnsT $[($optKeys := $optVals)]*) => do
    let ns ← getCurrNamespace
    let extNm := ns ++ extId.getId
    let (maxBT?, extT?, exitsT?, nXT?, prefixId?) ← parsePrefixExtOptions optKeys optVals
    let (listExtTy, total, extLit) ← liftTermElabM <|
      elabAndEvalPrefixExt targT ltT fnsT maxBT? extT? exitsT? nXT?
    liftCoreM do
      addCertDef extNm listExtTy extLit
      if let some pfxId := prefixId? then
        let pfxNm := ns ++ pfxId.getId
        let natTy := Lean.mkConst ``Nat
        let symEntryNatTy :=
          mkApp2 (Lean.mkConst ``Prod [.zero, .zero])
            (Lean.mkConst ``LeanQbe.T.SigEntry) natTy
        let dropIdx := mkApp2 (Lean.mkConst ``Nat.sub) (mkNatLit total) (mkBVar 0)
        let dropVal := mkApp3 (Lean.mkConst ``List.drop [.zero])
          symEntryNatTy dropIdx (Lean.mkConst extNm)
        let pfxTy := Lean.mkForall `k .default natTy listExtTy
        let pfxVal := Lean.mkLambda `k .default natTy dropVal
        addCertDef pfxNm pfxTy pfxVal

end

end LeanQbe.T
