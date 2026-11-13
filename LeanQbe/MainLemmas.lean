module

public import LeanQbe.Main
public import LeanQbe.RegaLemmas
public import LeanQbe.OptLemmas
public import LeanQbe.FlatLemmas

/-!
# Correctness of the pipeline

* `compileFn_correct`: if `compileFn T.toIsa f = .ok code` and the code sits in host `h`, the
  compiled function meets the *source* function's `wp` as a `FnSpec`. The mid-end refines contracts
  (`Func.opt_spec`), the lowering is `lowerFn_correct`, and `FnSpec` is antitone in the contract.
* `compileFn_leaf_correct`: specialization of `compileFn_correct` to leaf functions without exits.
* `compile_correct`: module-level linking for an acyclic list of functions `fs` (callees first).
* `compile_sound`: top-level module compilation and linking theorem for `compileModule`, which
  computes and checks all stack bounds inside the compiler.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

theorem compileFn_correct {T : Target} (h : T.Host) (f : Fn) (Γ : Env)
    (bound : String → Nat) (n nX : Nat) (code : List T.Directive) (k₀ : Nat)
    (hcomp : compileFn T.toIsa f = .ok code) (hcode : code.IsInfixAt (T.prog h) k₀)
    (hu : T.LabelsUnique h) (hwf : Func.Wf f.body)
    (hFn : T.frameSize (f.nslots T.toIsa) ≤ n) (hn : n + T.raBytes ≤ 2 ^ 64)
    (hcallees : ∀ g ∈ f.opt.ext.callees,
      T.FnSpec h g (Γ g) (bound g) nX ∧ T.frameSize (f.nslots T.toIsa) + T.raBytes + bound g ≤ n)
    (hexits : ∀ g ∈ f.opt.ext.exits, T.Defined h g ∧ nX ≤ n) :
    T.FnSpec h f.name (Func.spec Γ f.body) n nX :=
  Target.FnSpec.of_spec T (Rega.lowerFn_correct h (f.hints T.toIsa) f.opt.ext f.opt Γ bound n nX
    code k₀ hcomp hcode hu (Func.opt_wf hwf) hFn hn hcallees hexits)
    fun _ _ _ _ hs => Func.opt_spec hwf hs

theorem compileFn_leaf_correct {T : Target} (h : T.Host) (f : Fn) (Γ : Env) (n nX : Nat)
    (code : List T.Directive) (k₀ : Nat)
    (hcomp : compileFn T.toIsa f = .ok code) (hcode : code.IsInfixAt (T.prog h) k₀)
    (hu : T.LabelsUnique h) (hwf : Func.Wf f.body)
    (hcallees : f.opt.ext.callees = []) (hexits : f.opt.ext.exits = [])
    (hFn : T.frameSize (f.nslots T.toIsa) ≤ n) (hn : n + T.raBytes ≤ 2 ^ 64) :
    T.FnSpec h f.name (Func.spec Γ f.body) n nX :=
  compileFn_correct h f Γ (fun _ => 0) n nX code k₀ hcomp hcode hu hwf hFn hn
    (by rw [hcallees]; intro _ hg; nomatch hg)
    (by rw [hexits]; intro _ hg; nomatch hg)

/-- Compiling and linking a list of functions (callees first). -/
theorem compile_correct {T : Target} (h : T.Host) (Γ : Env) (bound : String → Nat) (nX : Nat) :
    ∀ (fs : List Fn) (code : List T.Directive) (k₀ : Nat),
    compile T.toIsa fs = .ok code → code.IsInfixAt (T.prog h) k₀ → T.LabelsUnique h →
    (∀ (pre : List Fn) (f : Fn) (post : List Fn), fs = pre ++ f :: post →
      Func.Wf f.body ∧
      (∀ args m Q X, Γ f.name args m Q X → Func.spec Γ f.body args m Q X) ∧
      T.frameSize (f.nslots T.toIsa) ≤ bound f.name ∧
      bound f.name + T.raBytes ≤ 2 ^ 64 ∧
      (∀ g ∈ f.opt.ext.callees,
        (g ∈ pre.map Fn.name ∨ T.FnSpec h g (Γ g) (bound g) nX) ∧
        T.frameSize (f.nslots T.toIsa) + T.raBytes + bound g ≤ bound f.name) ∧
      (∀ g ∈ f.opt.ext.exits, T.Defined h g ∧ nX ≤ bound f.name)) →
    ∀ f ∈ fs, T.FnSpec h f.name (Γ f.name) (bound f.name) nX
  | [], _, _, _, _, _, _, f, hf => nomatch hf
  | f₀ :: fs, code, k₀, hcomp, hcode, hu, hstep, f, hf => by
    simp only [compile] at hcomp
    split at hcomp
    · rename_i c₀ cs hc₀ hcs
      simp only [Except.ok.injEq] at hcomp
      subst hcomp
      obtain ⟨hwf₀, hspec₀, hFn₀, hn₀, hcallees₀, hexits₀⟩ := hstep [] f₀ fs rfl
      have hf₀ : T.FnSpec h f₀.name (Γ f₀.name) (bound f₀.name) nX :=
        Target.FnSpec.of_spec T
          (compileFn_correct h f₀ Γ bound (bound f₀.name) nX c₀ k₀ hc₀ hcode.append.1 hu hwf₀
            hFn₀ hn₀
            (fun g hg => by
              obtain ⟨h1 | h1, h2⟩ := hcallees₀ g hg
              · nomatch h1
              · exact ⟨h1, h2⟩)
            hexits₀)
          hspec₀
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hf₀
      · refine compile_correct h Γ bound nX fs cs (k₀ + c₀.length) hcs hcode.append.2 hu
          (fun pre f' post heq => ?_) f hf
        grind
    · simp at hcomp
    · simp at hcomp

theorem lookupBound_mem {bounds : List (String × Nat)} {g : String} {b : Nat}
    (h : lookupBound bounds g = some b) : (g, b) ∈ bounds := by
  unfold lookupBound at h
  cases hf : bounds.find? (fun p => p.1 == g) with
  | none => simp [hf] at h
  | some p => grind

theorem calleesBound_spec {F raBytes : Nat} {bounds : List (String × Nat)} :
    ∀ {gs : List String} {n : Nat},
    calleesBound F raBytes bounds gs = some n →
    F ≤ n ∧ ∀ g ∈ gs, ∃ bg, lookupBound bounds g = some bg ∧ F + raBytes + bg ≤ n
  | [], _, h => by
    simp only [calleesBound, Option.some.injEq] at h
    grind
  | g :: gs, n, h => by
    unfold calleesBound at h
    split at h
    · rename_i bg rest hbg hrest
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hF, ih⟩ := calleesBound_spec hrest
      grind
    · simp at h

theorem checkAndBound_spec {I : Isa} {raBytes : Nat} {exits : List String} {nX : Nat}
    {bounds : List (String × Nat)} {f : Fn} {b : Nat}
    (h : checkAndBound I raBytes exits nX bounds f = some b) :
    I.frameSize (f.nslots I) ≤ b ∧
    b + raBytes ≤ 2 ^ 64 ∧
    (∀ g ∈ f.opt.ext.callees,
      ∃ bg, lookupBound bounds g = some bg ∧ I.frameSize (f.nslots I) + raBytes + bg ≤ b) ∧
    (∀ g ∈ f.opt.ext.exits, g ∈ exits ∧ nX ≤ b) := by
  unfold checkAndBound at h
  cases hn₁ : calleesBound (I.frameSize (f.nslots I)) raBytes bounds f.opt.ext.callees with
  | none => simp [hn₁] at h
  | some n₁ =>
    rw [hn₁] at h
    dsimp only at h
    split at h
    · rename_i hall
      generalize hn_def : (if f.opt.ext.exits.isEmpty = true then n₁ else Nat.max n₁ nX) = n at h
      split at h
      · rename_i h264
        simp only [Option.some.injEq] at h
        subst h hn_def
        obtain ⟨hF, hcallees⟩ := calleesBound_spec hn₁
        grind
      · simp at h
    · simp at h

/-- Top-level compiler-correctness theorem: if `compileModule` succeeds on `fs` producing
`(code, bounds)`, and `code` is in host `h` with unique labels, then every `(name, b) ∈ bounds`
is defined in `h` and satisfies its source contract `Γ name` as a `Target.FnSpec` with stack bound `b`. -/
theorem compile_sound {T : Target} (h : T.Host) (Γ : Env)
    (extCallees : List (String × Nat)) (exits : List String) (nX : Nat) :
    ∀ (fs : List Fn) (code : List T.Directive) (bounds : List (String × Nat)) (k₀ : Nat),
    compileModule T.toIsa T.raBytes extCallees exits nX fs = .ok (code, bounds) →
    code.IsInfixAt (T.prog h) k₀ →
    T.LabelsUnique h →
    (∀ f ∈ fs, Func.Wf f.body) →
    (∀ f ∈ fs, ∀ args m Q X, Γ f.name args m Q X → Func.spec Γ f.body args m Q X) →
    (∀ p ∈ extCallees, T.FnSpec h p.1 (Γ p.1) p.2 nX) →
    (∀ g ∈ exits, T.Defined h g) →
    ∀ p ∈ bounds, T.Defined h p.1 ∧ T.FnSpec h p.1 (Γ p.1) p.2 nX
  | [], _, _, _, hcomp, _, _, _, _, _, _, p, hp => by
    simp only [compileModule, Except.ok.injEq, Prod.mk.injEq] at hcomp
    grind
  | f :: fs, code, bounds, k₀, hcomp, hcode, hu, hwf, hspec, hext, hexits, p, hp => by
    simp only [compileModule] at hcomp
    split at hcomp
    · rename_i c b hc hb
      split at hcomp
      · rename_i cs bs hrest
        simp only [Except.ok.injEq, Prod.mk.injEq] at hcomp
        rcases hcomp with ⟨rfl, rfl⟩
        obtain ⟨hF, hn, hcallees, hex⟩ := checkAndBound_spec hb
        let bound : String → Nat := fun g => (lookupBound extCallees g).getD 0
        have hf_def : T.Defined h f.name := by
          unfold compileFn Rega.lowerFn at hc
          split at hc
          · split at hc
            · simp only [Except.ok.injEq] at hc
              subst hc
              exact ⟨k₀, hcode.append.1.cons.1⟩
            · simp at hc
          · simp at hc
        have hf_spec : T.FnSpec h f.name (Γ f.name) b nX := by
          refine Target.FnSpec.of_spec T
            (compileFn_correct h f Γ bound b nX c k₀ hc hcode.append.1 hu
              (hwf f List.mem_cons_self) hF hn (fun g hg => ?_) (fun g hg => ?_))
            (hspec f List.mem_cons_self)
          · obtain ⟨bg, hlk, hbg⟩ := hcallees g hg
            have hgb : bound g = bg := by dsimp [bound]; rw [hlk]; rfl
            rw [hgb]
            exact ⟨hext (g, bg) (lookupBound_mem hlk), hbg⟩
          · grind
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨hf_def, hf_spec⟩
        · exact compile_sound h Γ ((f.name, b) :: extCallees) exits nX fs cs bs (k₀ + c.length)
            hrest hcode.append.2 hu
            (fun f' hf' => hwf f' (List.mem_cons_of_mem _ hf'))
            (fun f' hf' => hspec f' (List.mem_cons_of_mem _ hf'))
            (fun q hq => by
              rcases List.mem_cons.mp hq with rfl | hq
              · exact hf_spec
              · exact hext q hq)
            hexits p hp
      · simp at hcomp
    · simp at hcomp
    · simp at hcomp

theorem compile_of_compileModule {I : Isa} {raBytes : Nat} {exits : List String} {nX : Nat} :
    ∀ {fs : List Fn} {extCallees : List (String × Nat)} {code : List I.Directive}
      {bounds : List (String × Nat)},
    compileModule I raBytes extCallees exits nX fs = .ok (code, bounds) →
    compile I fs = .ok code
  | [], _, _, _, h => by
    simp only [compileModule, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩
    rfl
  | f :: fs, extCallees, code, bounds, h => by
    simp only [compileModule] at h
    split at h
    · rename_i c b hc hb
      split at h
      · rename_i cs bs hrest
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, _⟩
        have ih := compile_of_compileModule hrest
        simp [compile, hc, ih]
      · simp at h
    · simp at h
    · simp at h

/-- Extract the emitted directives from a `compileModule` result (made `@[irreducible]` below
so the kernel never re-evaluates `res`). -/
def extractCode {D : Type} (res : Except String (List D × List (String × Nat))) : List D :=
  match res with
  | .ok (c, _) => c
  | .error _ => []

/-- Extract the computed stack bounds from a `compileModule` result (made `@[irreducible]` below
so the kernel never re-evaluates `res`). -/
def extractBounds {D : Type} (res : Except String (List D × List (String × Nat))) :
    List (String × Nat) :=
  match res with
  | .ok (_, b) => b
  | .error _ => []

theorem extractResult_eq {D : Type} {label : String → D} {labelsNodup : List D → Bool}
    {res : Except String (List D × List (String × Nat))}
    {fnNames exits : List String} {maxBound : Nat}
    (h : checkCompileResult label labelsNodup res fnNames exits maxBound = true) :
    res = .ok (extractCode res, extractBounds res) := by
  cases res with
  | error _ => simp [checkCompileResult] at h
  | ok cb => rcases cb with ⟨c, b⟩; rfl

theorem extract_nodup {D : Type} {label : String → D} {labelsNodup : List D → Bool}
    {res : Except String (List D × List (String × Nat))}
    {fnNames exits : List String} {maxBound : Nat}
    (h : checkCompileResult label labelsNodup res fnNames exits maxBound = true) :
    labelsNodup (extractCode res ++ exits.map label) = true := by
  cases res with
  | error _ => simp [checkCompileResult] at h
  | ok cb =>
    rcases cb with ⟨c, b⟩
    simp only [checkCompileResult, Bool.and_eq_true] at h
    exact h.1.1.1

theorem extract_small {D : Type} {label : String → D} {labelsNodup : List D → Bool}
    {res : Except String (List D × List (String × Nat))}
    {fnNames exits : List String} {maxBound : Nat}
    (h : checkCompileResult label labelsNodup res fnNames exits maxBound = true) :
    4 * (extractCode res ++ exits.map label).length < 2 ^ 64 := by
  cases res with
  | error _ => simp [checkCompileResult] at h
  | ok cb =>
    rcases cb with ⟨c, b⟩
    simp only [checkCompileResult, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.2

theorem extract_bound_le {D : Type} {label : String → D} {labelsNodup : List D → Bool}
    {res : Except String (List D × List (String × Nat))}
    {fnNames exits : List String} {maxBound : Nat}
    (h : checkCompileResult label labelsNodup res fnNames exits maxBound = true)
    (nm : String) :
    (lookupBound (extractBounds res) nm).getD 0 ≤ maxBound := by
  cases res with
  | error _ => simp [checkCompileResult] at h
  | ok cb =>
    rcases cb with ⟨c, b⟩
    simp only [checkCompileResult, Bool.and_eq_true] at h
    have hall := h.1.2
    dsimp [extractBounds]
    cases hlk : lookupBound b nm with
    | none => simp
    | some v =>
      have hmem := lookupBound_mem hlk
      grind

theorem extract_bound_mem {D : Type} {label : String → D} {labelsNodup : List D → Bool}
    {res : Except String (List D × List (String × Nat))}
    {fnNames exits : List String} {maxBound : Nat}
    (h : checkCompileResult label labelsNodup res fnNames exits maxBound = true)
    {nm : String} (hnm : nm ∈ fnNames) :
    (nm, (lookupBound (extractBounds res) nm).getD 0) ∈ extractBounds res := by
  cases res with
  | error _ => simp [checkCompileResult] at h
  | ok cb =>
    rcases cb with ⟨c, b⟩
    simp only [checkCompileResult, Bool.and_eq_true] at h
    have hall := List.all_eq_true.mp h.2 nm hnm
    dsimp [extractBounds]
    cases hlk : lookupBound b nm with
    | none => simp [hlk] at hall
    | some v => exact lookupBound_mem hlk

attribute [irreducible] extractCode extractBounds

/-- Bundle of a compiled module on target `T`, constructed from a single kernel evaluation of
`checkCompile` so that downstream proofs never re-evaluate the compiler. -/
structure Compiled (T : Target) (extCallees : List (String × Nat)) (exits : List String)
    (nX : Nat) (fs : List Fn) (maxBound : Nat := 2048) where
  code : List T.Directive
  bounds : List (String × Nat)
  compileModule_eq : compileModule T.toIsa T.raBytes extCallees exits nX fs = .ok (code, bounds)
  compile_eq : compile T.toIsa fs = .ok code
  bound_mem : ∀ {nm : String}, nm ∈ fs.map Fn.name → (nm, (lookupBound bounds nm).getD 0) ∈ bounds
  bound_le : ∀ (nm : String), (lookupBound bounds nm).getD 0 ≤ maxBound
  host : T.Host
  prog_host : T.prog host = code ++ exits.map T.label
  labelsUnique : T.LabelsUnique host

namespace Compiled

variable {T : Target} {extCallees : List (String × Nat)} {exits : List String}
  {nX : Nat} {fs : List Fn} {maxBound : Nat}

/-- Symbolic stack bound computed for function `nm` in `M`. -/
def bound (M : Compiled T extCallees exits nX fs maxBound) (nm : String) : Nat :=
  (lookupBound M.bounds nm).getD 0

theorem bound_mem_of_mem (M : Compiled T extCallees exits nX fs maxBound)
    {nm : String} (hnm : nm ∈ fs.map Fn.name) :
    (nm, M.bound nm) ∈ M.bounds :=
  M.bound_mem hnm

theorem bound_le_max (M : Compiled T extCallees exits nX fs maxBound) (nm : String) :
    M.bound nm ≤ maxBound :=
  M.bound_le nm

theorem code_infix_host (M : Compiled T extCallees exits nX fs maxBound) :
    M.code.IsInfixAt (T.prog M.host) 0 := by
  rw [M.prog_host]
  exact ⟨exits.map T.label, rfl⟩

theorem defined_exit_host (M : Compiled T extCallees exits nX fs maxBound)
    {g : String} (hg : g ∈ exits) :
    T.Defined M.host g := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
  refine ⟨M.code.length + i, ?_⟩
  rw [M.prog_host, List.getElem?_append_right (by omega)]
  grind

/-- Module linking theorem over any host `h` containing `M.code` at `k₀` with unique labels. -/
theorem fnSpec (M : Compiled T extCallees exits nX fs maxBound)
    (h : T.Host) (Γ : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.prog h) k₀) (hu : T.LabelsUnique h)
    (hwf : ∀ f ∈ fs, Func.Wf f.body)
    (hsound : ∀ f ∈ fs, ∀ args m Q X, Γ f.name args m Q X → Func.spec Γ f.body args m Q X)
    (hext : ∀ p ∈ extCallees, T.FnSpec h p.1 (Γ p.1) p.2 nX)
    (hexits : ∀ g ∈ exits, T.Defined h g)
    {nm : String} (hnm : nm ∈ fs.map Fn.name) :
    T.Defined h nm ∧ T.FnSpec h nm (Γ nm) (M.bound nm) nX :=
  compile_sound h Γ extCallees exits nX fs M.code M.bounds k₀
    M.compileModule_eq hc hu hwf hsound hext hexits
    (nm, M.bound nm) (M.bound_mem hnm)

/-- Module linking theorem specialized to `M.host` (when `extCallees = []`). -/
theorem fnSpec_host (M : Compiled T [] exits nX fs maxBound)
    (Γ : Env)
    (hwf : ∀ f ∈ fs, Func.Wf f.body)
    (hsound : ∀ f ∈ fs, ∀ args m Q X, Γ f.name args m Q X → Func.spec Γ f.body args m Q X)
    {nm : String} (hnm : nm ∈ fs.map Fn.name) :
    T.Defined M.host nm ∧ T.FnSpec M.host nm (Γ nm) (M.bound nm) nX :=
  M.fnSpec M.host Γ 0 M.code_infix_host M.labelsUnique hwf hsound
    (fun _ hp => nomatch hp) (fun _ hg => M.defined_exit_host hg) hnm

end Compiled

/-- Single boolean predicate checked once by `kernel_rfl` per program and target. -/
def checkCompile (T : Target) (L : TargetLayout T)
    (extCallees : List (String × Nat)) (exits : List String) (nX : Nat)
    (fs : List Fn) (maxBound : Nat := 2048) : Bool :=
  checkCompileResult T.label L.labelsNodup
    (compileModule T.toIsa T.raBytes extCallees exits nX fs)
    (fs.map Fn.name) exits maxBound

/-- Construct `Compiled` from a single proof of `checkCompile = true`. -/
def compileChecked (T : Target) (L : TargetLayout T)
    (extCallees : List (String × Nat)) (exits : List String) (nX : Nat)
    (fs : List Fn) (maxBound : Nat := 2048)
    (h : checkCompile T L extCallees exits nX fs maxBound = true) :
    Compiled T extCallees exits nX fs maxBound where
  code := extractCode (compileModule T.toIsa T.raBytes extCallees exits nX fs)
  bounds := extractBounds (compileModule T.toIsa T.raBytes extCallees exits nX fs)
  compileModule_eq := extractResult_eq h
  compile_eq := compile_of_compileModule (extractResult_eq h)
  bound_mem := extract_bound_mem h
  bound_le := extract_bound_le h
  host := L.layoutOf
    (extractCode (compileModule T.toIsa T.raBytes extCallees exits nX fs) ++ exits.map T.label)
    (extract_small h)
  prog_host := L.prog_layoutOf _ _
  labelsUnique := L.labelsUnique_layoutOf (extract_small h) (extract_nodup h)

namespace TargetInit

variable {T : Target} (I : TargetInit T)

/-- Run a function `nm` in `M.host` from `I.initState (M.bound nm) bs args` using `hf`. -/
theorem run_fnSpec {exits : List String} {nX : Nat} {fs : List Fn}
    (M : Compiled T [] exits nX fs 2048) {nm : String} {spec : Spec}
    (hf : T.FnSpec M.host nm spec (M.bound nm) nX)
    (bs : List UInt8) (args : List Val)
    (hbs : bs.length ≤ 8192) (hargs : args.length ≤ 6)
    {Q : Post} {X : XPost}
    (hspec : spec args (bs.At 0x1000#64) Q X)
    {post : T.State → Prop}
    (hpost : ∀ st,
      (T.pc st = I.ra0 ∧ ∃ rets m', Q rets m' ∧ T.RetsIn rets (T.data st) ∧
        (T.mem (T.data st) =⋆ Eq m' ⋆ T.Exit I.sp0 (M.bound nm) ⋆ Std.ExtHashMap.emp)) ∨
      (∃ sym' as m', X sym' as m' ∧ T.pc st = T.labelAddr M.host sym' ∧
        T.ArgsIn as (T.data st)) →
      post st) :
    Eventually (T.step M.host) post
      (T.mkState (I.initState (M.bound nm) bs args) (T.labelAddr M.host nm)) := by
  have hmem := I.mem_entry (M.bound nm) bs args (M.bound_le_max nm) hbs
  rw [← I.get_sp (M.bound nm) bs args] at hmem
  refine eventually_weaken _ _ _ _ ?_
    (hf args (bs.At 0x1000#64) Q X hspec (I.initState (M.bound nm) bs args) I.ra0
      Std.ExtHashMap.emp (I.argsIn _ _ _ hargs) (I.raReg _ _ _)
      (by rw [I.get_sp]; exact I.spEntry) hmem)
  rintro st (⟨hpc, rets, m', hQ, hrets, _, hm'⟩ | ⟨sym', as, m', hX, _, hpc, has, _⟩)
  · rw [I.get_sp] at hm'
    exact hpost st (Or.inl ⟨hpc, rets, m', hQ, hrets, hm'⟩)
  · exact hpost st (Or.inr ⟨sym', as, m', hX, hpc, has⟩)

/-- Run a non-exiting function returning a single value `v` in `I.ret0`. -/
theorem run_ret1 {exits : List String} {nX : Nat} {fs : List Fn}
    (M : Compiled T [] exits nX fs 2048) {nm : String} {spec : Spec}
    (hf : T.FnSpec M.host nm spec (M.bound nm) nX)
    (bs : List UInt8) (args : List Val) (v : Val)
    (hbs : bs.length ≤ 8192) (hargs : args.length ≤ 6)
    {Q : Post}
    (hspec : spec args (bs.At 0x1000#64) Q (fun _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = [v]) :
    Eventually (T.step M.host)
      (fun st => T.pc st = I.ra0 ∧ T.get (T.data st) I.ret0 = v)
      (T.mkState (I.initState (M.bound nm) bs args) (T.labelAddr M.host nm)) := by
  refine I.run_fnSpec M hf bs args hbs hargs hspec ?_
  rintro st (⟨hpc, rets, m', hq, hrets, _⟩ | ⟨_, _, _, hx, _⟩)
  · have hr := hQ rets m' hq; subst hr
    exact ⟨hpc, I.retsIn_singleton v _ hrets⟩
  · exact hx.elim

/-- Run a non-exiting function returning `[v]` and establishing memory predicate `P`. -/
theorem run_ret1_sep {exits : List String} {nX : Nat} {fs : List Fn}
    (M : Compiled T [] exits nX fs 2048) {nm : String} {spec : Spec}
    (hf : T.FnSpec M.host nm spec (M.bound nm) nX)
    (bs : List UInt8) (args : List Val) (v : Val) (P : Mem 64 → Prop)
    (hbs : bs.length ≤ 8192) (hargs : args.length ≤ 6)
    {Q : Post}
    (hspec : spec args (bs.At 0x1000#64) Q (fun _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = [v] ∧ P m') :
    Eventually (T.step M.host)
      (fun st => T.pc st = I.ra0 ∧ T.get (T.data st) I.ret0 = v ∧
        (T.mem (T.data st) =⋆ P ⋆ T.Exit I.sp0 (M.bound nm) ⋆ Std.ExtHashMap.emp))
      (T.mkState (I.initState (M.bound nm) bs args) (T.labelAddr M.host nm)) := by
  refine I.run_fnSpec M hf bs args hbs hargs hspec ?_
  rintro st (⟨hpc, rets, m', hq, hrets, hm'⟩ | ⟨_, _, _, hx, _⟩)
  · obtain ⟨rfl, hP⟩ := hQ rets m' hq
    exact ⟨hpc, I.retsIn_singleton v _ hrets,
      sep_mono (fun _ => sep_mono (fun _ e => e ▸ hP)) hm'⟩
  · exact hx.elim

end TargetInit

end LeanQbe
