module

public import LeanQbe.T.MainLemmas
public import LeanQbe.T.OptPolicy
import LeanQbe.T.OptLemmas
import LeanQbe.T.InlineLemmas
import LeanQbe.T.MainInline
import LeanQbe.T.RegaLemmas

/-!
# Post-`mid` Late Inlining & Direct Compilation (`MainLateInline`)

Purely additive Class `L` module supporting **late inlining after `Fn.midPolicy`** so outer
functions receive full mid-end optimization (`earlyOpt → legal → lateOpt`) while `@predictable` /
lifted snippet callees are spliced via `Inline.spliceRet` (`Module.inlinePolicy`) **after** all
CFG/value passes — preserving `sDirect` AST structure verbatim inside `.group` for `SpillSnippet`
`zipTrees` matching.

Key definitions and theorems:
* `makeLateInlinePolicy`, `lateInlineSnippetsPolicy`: `InlinePolicy` constructors selecting
  whitelisted snippet symbols with explicit node budgets while keeping cold helpers out of line.
* `Module.midPolicy`, `Module.lateInline`, `Module.midThenLateInline`: staged per-function
  `midPolicy` followed by post-`mid` `Module.inlinePolicy`.
* `compileDirectModule`, `compileLateInlined`: verified backend lowering on already-mid-compiled
  modules (never re-running `Fn.mid` over the inlined result).
* `compileDirectModule_sound`, `compileLateInlined_sound`, `DirectCompiled`: end-to-end
  `T.Defined` + `T.FnSpec` + `DirectCompiled` / `TargetInit` execution theorems matching
  `MainLemmas`, using only standard axioms (`std3`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Late-inlining policy and module transforms -/

/-- Build an `InlinePolicy` that late-inlines ONLY callees in `snippetBudgets` (up to their listed
node size budget; `defaultMaxSize = 0` keeps unlisted cold helpers out of line). -/
def makeLateInlinePolicy (snippetBudgets : List (Sym × Nat))
    (defaultMaxSize : Nat := 0) : InlinePolicy :=
  { budget := fun sym =>
      match snippetBudgets.find? (fun p => p.1 == sym) with
      | some p => p.2
      | none => defaultMaxSize
    leafMax := 0
    singleSiteMax := 0
    maxCallerSize := 0
    maxCalleeCalls := 0
    maxCalleeLoops := none
    maxTotalDup := 0
    leafNoLoopMaxDup := 0
    requireLoopSite := false
    maxCallerCalls := 0
    exemptNoLoopMax := 0
    maxCallerLoopDup := 0
    coldLoopGuardMax := 0
    coldLoopGuardMin := 0
    keepOutOfLine := [] }

/-- Build an `InlinePolicy` granting `snippetBudget` (default `100000`) to every symbol in
`snippetSyms` and `0` to all other functions. -/
def lateInlineSnippetsPolicy (snippetSyms : List Sym)
    (snippetBudget : Nat := 100000) : InlinePolicy :=
  makeLateInlinePolicy (snippetSyms.map (·, snippetBudget)) 0

/-- Apply per-function `Fn.midPolicy lt` across every function in `M`. -/
def Module.midPolicy (M : Module) (lt : LegalTarget) (policyOf : Sym → SnippetOptPolicy) :
    Module :=
  { M with fns := M.fns.map (fun fn => fn.midPolicy lt (policyOf fn.name)) }

/-- Run post-`mid` `Module.inlinePolicy` WITHOUT re-running `Fn.renorm` or `lateOpt`, preserving
callee AST structure inside `.group` for structural `zipTrees` matching. -/
def Module.lateInline (M : Module) (inlPol : InlinePolicy) : Module :=
  M.inlinePolicy inlPol

/-- Stage 1 (`Module.midPolicy`) followed by Stage 2 (`Module.lateInline`). -/
def Module.midThenLateInline (M : Module) (lt : LegalTarget)
    (policyOf : Sym → SnippetOptPolicy) (inlPol : InlinePolicy) : Module :=
  (M.midPolicy lt policyOf).lateInline inlPol

theorem Module.lateInline_sigs (M : Module) (inlPol : InlinePolicy) :
    (M.lateInline inlPol).sigs = M.sigs :=
  Module.inlinePolicy_sigs M inlPol

theorem Module.lateInline_names (M : Module) (inlPol : InlinePolicy) :
    (M.lateInline inlPol).names = M.names :=
  Module.inlinePolicy_names M inlPol

theorem Module.lateInline_namesNodup (M : Module) (inlPol : InlinePolicy) :
    (M.lateInline inlPol).namesNodup ↔ M.namesNodup :=
  Iff.of_eq (Module.inlinePolicy_namesNodup M inlPol)

/-- `ModuleOk` preservation for post-`mid` `Module.lateInline`. -/
theorem Module.lateInline_ok {Γ : Env} {M : Module} (inlPol : InlinePolicy)
    (hM : ModuleOk Γ M) : ModuleOk Γ (M.lateInline inlPol) :=
  Module.inlinePolicy_ok inlPol hM

/-! ## Direct backend compilation (without re-running `Fn.mid`) -/

/-- Compile an acyclic callee-first list of already-mid-compiled functions with externally
supplied `hints`, checking callee bounds and 64-bit stack safety via `checkAndBoundExt`. -/
def compileDirectModule (I : Isa) (raBytes : Nat)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat) :
    List Fn → List I.Hints → Except String (List I.Directive × List (Sym × Nat))
  | [], [] => .ok ([], [])
  | mf :: fs, h :: hs =>
    let ext := mf.ext
    match Rega.lowerFn I h ext mf,
          checkAndBoundExt I raBytes exits nX extCallees h ext with
    | .ok c, some b =>
      match compileDirectModule I raBytes ((mf.sig, b) :: extCallees) exits nX fs hs with
      | .ok (cs, bs) => .ok (c ++ cs, (mf.name, b) :: bs)
      | .error e => .error e
    | .error e, _ => .error s!"{mf.name}: {e}"
    | _, none => .error s!"{mf.name}: unknown callee, undeclared exit, or stack overflow"
  | _, _ => .error "compileDirectModule: fn/hints length mismatch"

/-- Check source support under `earlyOptPolicy`, run `Module.midThenLateInline`, and compile
the resulting functions directly via `compileDirectModule`. -/
def compileLateInlined (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (M : Module) (policyOf : Sym → SnippetOptPolicy) (inlPol : InlinePolicy)
    (hints : List I.Hints) : Except String (List I.Directive × List (Sym × Nat)) :=
  if M.fns.all (fun f => (f.earlyOptPolicy (policyOf f.name)).body.supportsSource lt) then
    compileDirectModule I raBytes extCallees exits nX
      (M.midThenLateInline lt policyOf inlPol).fns hints
  else
    .error "compileLateInlined: unsupported source op for target"

/-! ## Label uniqueness and direct soundness proofs -/

private theorem compileDirectModule_code_labels {T : Target} (hcl : Rega.LabelClean T.toIsa)
    (raBytes : Nat) (exits : List Sym) (nX : Nat) :
    ∀ {extCallees : List (SigEntry × Nat)} {fs : List Fn} {hints : List T.toIsa.Hints}
      {code : List T.Directive} {bounds : List (Sym × Nat)},
      compileDirectModule T.toIsa raBytes extCallees exits nX fs hints = .ok (code, bounds) →
      (fs.map Fn.name).Nodup → fs.all (fun f => fnNameOk f.name) = true →
      (∀ (i : Nat) (l : Sym), code[i]? = some (T.frame.label l) →
        ∃ f ∈ fs, l = f.name ∨ ∃ a, l = Rega.lname f.name a) ∧
      (∀ (i j : Nat) (l : Sym),
        code[i]? = some (T.frame.label l) → code[j]? = some (T.frame.label l) → i = j)
  | _, [], [], _, _, hcm, _, _ => by
    dsimp only [compileDirectModule] at hcm
    cases hcm
    exact ⟨fun _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩
  | _, [], _ :: _, _, _, hcm, _, _ => by dsimp only [compileDirectModule] at hcm; cases hcm
  | _, _ :: _, [], _, _, hcm, _, _ => by dsimp only [compileDirectModule] at hcm; cases hcm
  | extCallees, f :: fs, h :: hs, code, bounds, hcm, hnd, hok => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    simp only [List.all_cons, Bool.and_eq_true] at hok
    dsimp only [compileDirectModule] at hcm
    split at hcm
    · rename_i c b hl _
      split at hcm
      · rename_i cs bs hrest
        simp only [Except.ok.injEq, Prod.mk.injEq] at hcm
        rcases hcm with ⟨rfl, rfl⟩
        obtain ⟨ih_mem, ih_uniq⟩ :=
          compileDirectModule_code_labels hcl raBytes exits nX hrest hnd.2 hok.2
        have hc_mem : ∀ (i : Nat) (l : Sym), c[i]? = some (T.frame.label l) →
            l = f.name ∨ ∃ a, l = Rega.lname f.name a := fun i l hi =>
          Rega.lowerFn_label_mem hcl hl hi
        have hc_uniq := Rega.lowerFn_labelsUnique hcl hl
        constructor
        · intro i l hi
          by_cases hlt : i < c.length
          · rw [List.getElem?_append_left hlt] at hi; exact ⟨f, List.mem_cons_self, hc_mem i l hi⟩
          · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hi
            obtain ⟨g, hg, hl'⟩ := ih_mem (i - c.length) l hi
            exact ⟨g, List.mem_cons_of_mem f hg, hl'⟩
        · intro i j l hi hj
          have disj : ∀ {i₁ j₁ : Nat}, c[i₁]? = some (T.frame.label l) →
              cs[j₁]? = some (T.frame.label l) → False := by
            intro i₁ j₁ hi₁ hj₁
            obtain ⟨g, hg, hlg⟩ := ih_mem j₁ l hj₁
            have hgok := List.all_eq_true.mp hok.2 g hg
            rcases hc_mem i₁ l hi₁ with rfl | ⟨a, rfl⟩ <;> rcases hlg with hgl | ⟨b, hgl⟩
            · exact hnd.1 g hg hgl.symm
            · exact lname_ne_cross hok.1 hgl.symm
            · exact lname_ne_cross hgok hgl
            · exact hnd.1 g hg (lname_inj_cross hok.1 hgok hgl).1.symm
          by_cases hic : i < c.length <;> by_cases hjc : j < c.length
          · rw [List.getElem?_append_left hic] at hi
            rw [List.getElem?_append_left hjc] at hj
            exact hc_uniq i j l hi hj
          · rw [List.getElem?_append_left hic] at hi
            rw [List.getElem?_append_right (Nat.le_of_not_lt hjc)] at hj
            exact absurd hi (fun h' => disj h' hj)
          · rw [List.getElem?_append_right (Nat.le_of_not_lt hic)] at hi
            rw [List.getElem?_append_left hjc] at hj
            exact absurd hj (fun h' => disj h' hi)
          · have hi' : c.length ≤ i := Nat.le_of_not_lt hic
            have hj' : c.length ≤ j := Nat.le_of_not_lt hjc
            rw [List.getElem?_append_right hi'] at hi
            rw [List.getElem?_append_right hj'] at hj
            have heq := ih_uniq (i - c.length) (j - c.length) l hi hj
            omega
      · cases hcm
    · cases hcm
    · cases hcm

private theorem nodup_getElem?_inj' {α : Type} :
    ∀ {xs : List α} {i j : Nat} {a : α}, xs.Nodup → xs[i]? = some a → xs[j]? = some a → i = j
  | [], _, _, _, _, hi, _ => by simp at hi
  | _ :: _, 0, 0, _, _, _, _ => rfl
  | x :: xs, 0, j + 1, a, hnd, hi, hj => by
    simp only [List.nodup_cons] at hnd
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    simp only [List.getElem?_cons_succ] at hj
    subst hi
    exact absurd (List.mem_of_getElem? hj) hnd.1
  | x :: xs, i + 1, 0, a, hnd, hi, hj => by
    simp only [List.nodup_cons] at hnd
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    simp only [List.getElem?_cons_succ] at hi
    subst hj
    exact absurd (List.mem_of_getElem? hi) hnd.1
  | _ :: _, i + 1, j + 1, _, hnd, hi, hj => by
    simp only [List.nodup_cons] at hnd
    exact congrArg Nat.succ (nodup_getElem?_inj' hnd.2 hi hj)

/-- Label uniqueness for `compileDirectModule` given `Rega.LabelClean`, `fnNameOk`, and disjoint
function/exit names. -/
theorem compileDirectModule_labelsUnique {T : Target} (hcl : Rega.LabelClean T.toIsa)
    (host : T.mach.Host) {raBytes : Nat} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} {fs : List Fn} {hints : List T.toIsa.Hints}
    {code : List T.Directive} {bounds : List (Sym × Nat)}
    (hprog : T.mach.prog host = code ++ exits.map T.frame.label)
    (hcm : compileDirectModule T.toIsa raBytes extCallees exits nX fs hints = .ok (code, bounds))
    (hnd : (fs.map Fn.name ++ exits).Nodup)
    (hok : (fs.map Fn.name ++ exits).all fnNameOk = true) :
    T.LabelsUnique host := by
  have hnd_split := List.nodup_append.mp hnd
  simp only [List.all_append, Bool.and_eq_true, List.all_map] at hok
  obtain ⟨hmem, huniq⟩ :=
    compileDirectModule_code_labels hcl raBytes exits nX hcm hnd_split.1 hok.1
  have hEx : ∀ (k : Nat) (l : Sym),
      (exits.map T.frame.label)[k]? = some (T.frame.label l) → exits[k]? = some l := by
    intro k l hk
    rw [List.getElem?_map] at hk
    cases hx : exits[k]? with
    | none => simp [hx] at hk
    | some e =>
      simp only [hx, Option.map_some, Option.some.injEq] at hk
      rw [hcl.label_inj e l hk]
  have hdisj : ∀ (i₁ k₂ : Nat) (l : Sym), code[i₁]? = some (T.frame.label l) →
      (exits.map T.frame.label)[k₂]? = some (T.frame.label l) → False := by
    intro i₁ k₂ l hi₁ hk₂
    have hmemE : l ∈ exits := List.mem_of_getElem? (hEx k₂ l hk₂)
    have hlok : fnNameOk l = true := List.all_eq_true.mp hok.2 l hmemE
    obtain ⟨f, hf, hlf⟩ := hmem i₁ l hi₁
    rcases hlf with hl_eq | ⟨a, hl_eq⟩
    · exact hnd_split.2.2 l (hl_eq ▸ List.mem_map_of_mem hf) l hmemE rfl
    · exact lname_ne_cross hlok hl_eq.symm
  intro i j l hi hj
  rw [hprog] at hi hj
  rcases Nat.lt_or_ge i code.length with hiL | hiR
  · rcases Nat.lt_or_ge j code.length with hjL | hjR
    · rw [List.getElem?_append_left hiL] at hi
      rw [List.getElem?_append_left hjL] at hj
      exact huniq i j l hi hj
    · rw [List.getElem?_append_left hiL] at hi
      rw [List.getElem?_append_right hjR] at hj
      exact absurd hi (fun h' => hdisj i (j - code.length) l h' hj)
  · rcases Nat.lt_or_ge j code.length with hjL | hjR
    · rw [List.getElem?_append_right hiR] at hi
      rw [List.getElem?_append_left hjL] at hj
      exact absurd hj (fun h' => hdisj j (i - code.length) l h' hi)
    · rw [List.getElem?_append_right hiR] at hi
      rw [List.getElem?_append_right hjR] at hj
      have heq := nodup_getElem?_inj' hnd_split.2.1 (hEx _ _ hi) (hEx _ _ hj)
      omega

private theorem find?_pred' {α : Type} {p : α → Bool} :
    ∀ {xs : List α} {x : α}, xs.find? p = some x → p x = true
  | [], _, h => by simp at h
  | y :: ys, x, h => by
    simp only [List.find?] at h
    cases hp : p y with
    | true => simp [hp] at h; subst h; exact hp
    | false => simp [hp] at h; exact find?_pred' h

private theorem defined_of_lowerFn' {T : Target} {host : T.mach.Host}
    {hints : T.toIsa.Hints} {E : Rega.Ext} {f : Fn} {code : List T.Directive} {k₀ : Nat}
    (hl : Rega.lowerFn T.toIsa hints E f = .ok code)
    (hc : code.IsInfixAt (T.mach.prog host) k₀) : T.Defined host f.name := by
  unfold Rega.lowerFn at hl
  split at hl
  · cases hl
  · cases hal : T.toIsa.assignArgs f.as with
    | none => simp [hal] at hl
    | some argLocs =>
      cases hrl : T.toIsa.assignRets f.rs with
      | none => simp [hal, hrl] at hl
      | some _ =>
        simp only [hal, hrl] at hl
        cases hb : Rega.bindAbiParams T.toIsa argLocs 0
            { regs := [], slots := .empty, defs := .empty, vecWidths := .empty } with
        | none => simp [hb] at hl
        | some st0 =>
          simp only [hb] at hl
          cases hle : Rega.lowerExpr T.toIsa hints E f.name
              (f.body Rega.VNat Rega.LNat (Tup.levels f.as 0)) f.as.length 0 0 st0 none with
          | error _ => simp [hle] at hl
          | ok _ =>
            simp only [hle, Except.ok.injEq] at hl
            subst hl
            exact ⟨k₀, (List.IsInfixAt.cons hc).1⟩

private theorem compileDirectModule_sound_aux (T : Target) (host : T.mach.Host)
    (exits : List Sym) (nX : Nat) (hexits : ∀ g ∈ exits, T.Defined host g) (Γ : Env) :
    ∀ {fs : List Fn} {hints : List T.toIsa.Hints} {extCallees : List (SigEntry × Nat)}
      {code : List T.Directive} {bounds : List (Sym × Nat)} {k₀ : Nat},
      compileDirectModule T.toIsa T.frame.raBytes extCallees exits nX fs hints =
        .ok (code, bounds) →
      code.IsInfixAt (T.mach.prog host) k₀ → T.LabelsUnique host → (fs.map Fn.name).Nodup →
      (∀ f ∈ fs, f.Wf ∧ ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X) →
      (∀ p ∈ extCallees, T.FnSpec host p.1.1 (Γ p.1.1 p.1.2.1 p.1.2.2) p.2 nX) →
      (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) →
      (∀ p ∈ extCallees, p.1.1 ∉ fs.map Fn.name) →
      ∀ p ∈ bounds, ∃ f ∈ fs, p.1 = f.name ∧ T.Defined host p.1 ∧
        T.FnSpec host p.1 (Γ p.1 f.as f.rs) p.2 nX
  | [], [], _, _, _, _, hcm, _, _, _, _, _, _, _, p, hp => by
    dsimp only [compileDirectModule] at hcm; cases hcm; cases hp
  | [], _ :: _, _, _, _, _, hcm, _, _, _, _, _, _, _, _, _ => by
    dsimp only [compileDirectModule] at hcm; cases hcm
  | _ :: _, [], _, _, _, _, hcm, _, _, _, _, _, _, _, _, _ => by
    dsimp only [compileDirectModule] at hcm; cases hcm
  | mf :: fs, hint :: hints, extCallees, code, bounds, k₀, hcm, hc, hu, hfsnd, hfns,
      hext, hext_eq, hext_disj, p, hp => by
    simp only [List.map_cons, List.nodup_cons] at hfsnd
    obtain ⟨hfwf, hfwp⟩ := hfns mf List.mem_cons_self
    dsimp only [compileDirectModule] at hcm
    cases hl : Rega.lowerFn T.toIsa hint mf.ext mf with
    | error _ => simp [hl] at hcm
    | ok c =>
      cases hchk : checkAndBoundExt T.toIsa T.frame.raBytes exits nX extCallees hint mf.ext with
      | none => simp [hl, hchk] at hcm
      | some b =>
        simp only [hl, hchk] at hcm
        cases hrest : compileDirectModule T.toIsa T.frame.raBytes ((mf.sig, b) :: extCallees)
            exits nX fs hints with
        | error _ => simp [hrest] at hcm
        | ok res =>
          rcases res with ⟨cs, bs⟩
          simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at hcm
          rcases hcm with ⟨rfl, rfl⟩
          obtain ⟨hc_inf, hcs_inf⟩ := List.IsInfixAt.append hc
          obtain ⟨hfr, hn, hcal_b, hex_b⟩ := checkAndBoundExt_spec hchk
          let bound : Sym → Nat := fun g =>
            match extCallees.find? (fun q => q.1.1 == g) with
            | some q => q.2
            | none => 0
          have hcal : ∀ g as bs', (g, as, bs') ∈ mf.ext.callees →
              T.FnSpec host g (Γ g as bs') (bound g) nX ∧
              Rega.effFrame T.toIsa hint mf.ext + T.frame.raBytes + bound g ≤ b := by
            intro g as bs' hg
            obtain ⟨bg, hlk, hle⟩ := hcal_b (g, as, bs') hg
            have hmem : ((g, as, bs'), bg) ∈ extCallees := lookupBound_mem hlk
            have hbd_eq : bound g = bg := by
              dsimp only [bound]
              cases hfnd : extCallees.find? (fun q => q.1.1 == g) with
              | none =>
                exfalso
                have hnot := List.find?_eq_none.mp hfnd ((g, as, bs'), bg) hmem
                simp at hnot
              | some q =>
                have hqmem : q ∈ extCallees := List.mem_of_find?_eq_some hfnd
                have hpred : q.1.1 = g :=
                  beq_iff_eq.mp (find?_pred' (p := fun q : SigEntry × Nat => q.1.1 == g) hfnd)
                exact hext_eq q hqmem ((g, as, bs'), bg) hmem hpred
            rw [hbd_eq]; exact ⟨hext ((g, as, bs'), bg) hmem, hle⟩
          have hex : ∀ g, g ∈ mf.ext.exits → T.Defined host g ∧ nX ≤ b := fun g hg =>
            ⟨hexits g (hex_b g hg).1, (hex_b g hg).2⟩
          have hfdef : T.Defined host mf.name := defined_of_lowerFn' hl hc_inf
          have hfspec : T.FnSpec host mf.name (Func.spec Γ mf.body) b nX :=
            Rega.lowerFn_correct T host hint mf.ext mf Γ b nX bound
              hfwf hl hc_inf hu hfr hn hcal hex
          have hfspec' : T.FnSpec host mf.name (Γ mf.name mf.as mf.rs) b nX := fun xs m Q X hq =>
            hfspec xs m Q X (hfwp xs m Q X hq)
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact ⟨mf, List.mem_cons_self, rfl, hfdef, hfspec'⟩
          · have hfns' : ∀ g ∈ fs, g.Wf ∧
                ∀ xs m Q X, Γ g.name g.as g.rs xs m Q X → Func.wp Γ g.body xs m Q X :=
              fun g hg => hfns g (List.mem_cons_of_mem mf hg)
            have hext' : ∀ q ∈ (mf.sig, b) :: extCallees,
                T.FnSpec host q.1.1 (Γ q.1.1 q.1.2.1 q.1.2.2) q.2 nX := by
              intro q hq
              rcases List.mem_cons.mp hq with rfl | hq'
              · exact hfspec'
              · exact hext q hq'
            have hext_disj' : ∀ q ∈ (mf.sig, b) :: extCallees, q.1.1 ∉ fs.map Fn.name := by
              intro q hq hmem
              rcases List.mem_cons.mp hq with rfl | hq'
              · exact hfsnd.1 hmem
              · exact hext_disj q hq' (List.mem_cons_of_mem mf.name hmem)
            have hext_eq' : ∀ q₁ ∈ (mf.sig, b) :: extCallees,
                ∀ q₂ ∈ (mf.sig, b) :: extCallees, q₁.1.1 = q₂.1.1 → q₁.2 = q₂.2 := by
              intro q₁ hq₁ q₂ hq₂ hsym
              rcases List.mem_cons.mp hq₁ with rfl | hq₁' <;>
                rcases List.mem_cons.mp hq₂ with rfl | hq₂'
              · rfl
              · exact absurd (hsym.symm ▸ List.mem_cons_self) (hext_disj q₂ hq₂')
              · exact absurd (hsym ▸ List.mem_cons_self) (hext_disj q₁ hq₁')
              · exact hext_eq q₁ hq₁' q₂ hq₂' hsym
            obtain ⟨g, hg, heqn, hgdef, hgspec⟩ :=
              compileDirectModule_sound_aux T host exits nX hexits Γ hrest hcs_inf hu hfsnd.2
                hfns' hext' hext_eq' hext_disj' p hp'
            exact ⟨g, List.mem_cons_of_mem mf hg, heqn, hgdef, hgspec⟩

/-- Top-level soundness for `compileDirectModule` over any already-mid-compiled function list
whose functions satisfy `Fn.Wf` and `Func.wp Γ`. -/
theorem compileDirectModule_sound (T : Target) (host : T.mach.Host)
    (Γ : Env) (fs : List Fn) (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (hints : List T.toIsa.Hints) (code : List T.Directive) (bounds : List (Sym × Nat)) (k₀ : Nat)
    (hcm : compileDirectModule T.toIsa T.frame.raBytes extCallees exits nX fs hints =
      .ok (code, bounds))
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hnd : (fs.map Fn.name).Nodup)
    (hwf : ∀ f ∈ fs, f.Wf)
    (hwp : ∀ f ∈ fs, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    (hext : ∀ p ∈ extCallees, T.FnSpec host p.1.1 (Γ p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ extCallees, p.1.1 ∉ fs.map Fn.name))
    (hexits : ∀ g ∈ exits, T.Defined host g) :
    ∀ p ∈ bounds, ∃ f ∈ fs, p.1 = f.name ∧ T.Defined host p.1 ∧
      T.FnSpec host p.1 (Γ p.1 f.as f.rs) p.2 nX :=
  compileDirectModule_sound_aux T host exits nX hexits Γ hcm hc hu hnd
    (fun f hf => ⟨hwf f hf, hwp f hf⟩) hext hext_uniq.1 hext_uniq.2

/-! ## `Module.midThenLateInline` invariant propagation (`Wf`, `Func.wp`, `names`, `sigs`) -/

private theorem inlineFnsPolicy_wf_wp (policy : InlinePolicy) (siteCounts loopCounts : List (Sym × Nat))
    (extSigs : List SigEntry) (exits : List Sym) (Γ : Env) :
    ∀ (seenSigs : List SigEntry) (cands rest : List Fn),
      CandsWpOk Γ cands →
      (∀ f ∈ rest, f.Wf ∧ ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X) →
      ∀ f ∈ inlineFnsPolicy policy siteCounts loopCounts extSigs exits seenSigs cands rest,
        f.Wf ∧ ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X
  | _, _, [], _, _, f, hf => nomatch hf
  | seenSigs, cands, fn :: rest, hcands, hrest, f, hf => by
    have ⟨hfn_wf, hfn_spec⟩ := hrest fn List.mem_cons_self
    let candsFn := selectCandsForCaller policy cands fn
    have hwpFn : CandsWpOk Γ candsFn := fun g hg => hcands g (selectCandsForCaller_mem policy cands fn g hg)
    let fn0 := fn.inline candsFn
    have hfn0_wf : fn0.Wf := Func.inline_wf hwpFn.wfOk hfn_wf
    have hfn0_spec : ∀ xs m Q X, Γ fn0.name fn0.as fn0.rs xs m Q X →
        Func.wp Γ fn0.body xs m Q X :=
      fun xs m Q X hg => Func.inline_spec hwpFn fn.body (hfn_spec xs m Q X hg)
    dsimp only [inlineFnsPolicy] at hf
    rcases List.mem_cons.mp hf with rfl | hf'
    · exact ⟨hfn0_wf, hfn0_spec⟩
    · have hcands' : CandsWpOk Γ (if inlineCandidateOkPolicy policy (lookupCallSite siteCounts fn0.name)
          (lookupCallSite loopCounts fn0.name) (seenSigs ++ extSigs) exits fn0
          then fn0 :: cands else cands) := by
        split
        · intro g hg
          rcases List.mem_cons.mp hg with rfl | hg'
          · exact ⟨hfn0_wf, hfn0_spec⟩
          · exact hcands g hg'
        · exact hcands
      exact inlineFnsPolicy_wf_wp policy siteCounts loopCounts extSigs exits Γ
        (seenSigs ++ [fn.sig]) _ rest hcands'
        (fun g hg => hrest g (List.mem_cons_of_mem fn hg)) f hf'

theorem Module.inlinePolicy_wf_wp {Γ : Env} {M : Module} (policy : InlinePolicy := {})
    (hwf : ∀ f ∈ M.fns, f.Wf)
    (hwp : ∀ f ∈ M.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X) :
    ∀ f ∈ (M.inlinePolicy policy).fns,
      f.Wf ∧ ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X := by
  dsimp only [Module.inlinePolicy]
  exact inlineFnsPolicy_wf_wp policy _ _ (M.externs.map Extern.sig) M.exits Γ [] [] M.fns
    (fun _ h => nomatch h) (fun f hf => ⟨hwf f hf, hwp f hf⟩)

private theorem inlineFnsPolicy_map_sig (policy : InlinePolicy) (siteCounts loopCounts : List (Sym × Nat))
    (extSigs : List SigEntry) (exits : List Sym) :
    ∀ (seenSigs : List SigEntry) (cands rest : List Fn),
      (inlineFnsPolicy policy siteCounts loopCounts extSigs exits seenSigs cands rest).map Fn.sig =
        rest.map Fn.sig
  | _, _, [] => rfl
  | seenSigs, cands, fn :: rest => by
    dsimp only [inlineFnsPolicy]
    rw [List.map_cons, inlineFnsPolicy_map_sig]
    rfl

theorem Module.inlinePolicy_fns_sigs (M : Module) (policy : InlinePolicy := {}) :
    (M.inlinePolicy policy).fns.map Fn.sig = M.fns.map Fn.sig := by
  dsimp only [Module.inlinePolicy]
  exact inlineFnsPolicy_map_sig policy _ _ (M.externs.map Extern.sig) M.exits [] [] M.fns

theorem Module.midThenLateInline_fns_sigs (M : Module) (lt : LegalTarget)
    (policyOf : Sym → SnippetOptPolicy) (inlPol : InlinePolicy) :
    (M.midThenLateInline lt policyOf inlPol).fns.map Fn.sig =
      M.fns.map (fun f => (f.name, lt.legalSig f.as, lt.legalSig f.rs)) := by
  dsimp only [Module.midThenLateInline, Module.lateInline]
  rw [Module.inlinePolicy_fns_sigs _ inlPol]
  simp only [Module.midPolicy, List.map_map, Function.comp_def, Fn.sig, Fn.midPolicy,
    Fn.midFromEarlyPolicy, Fn.earlyOptPolicy]

theorem Module.midThenLateInline_fns_names (M : Module) (lt : LegalTarget)
    (policyOf : Sym → SnippetOptPolicy) (inlPol : InlinePolicy) :
    (M.midThenLateInline lt policyOf inlPol).fns.map Fn.name = M.fns.map Fn.name := by
  have h := congrArg (List.map Prod.fst) (M.midThenLateInline_fns_sigs lt policyOf inlPol)
  simpa [List.map_map, Function.comp_def, Fn.sig] using h

private theorem sig_eq_of_mem_map_sig {lt : LegalTarget} {M : Module}
    {policyOf : Sym → SnippetOptPolicy} {inlPol : InlinePolicy}
    {g : Fn} (hg : g ∈ (M.midThenLateInline lt policyOf inlPol).fns) :
    ∃ f ∈ M.fns, g.name = f.name ∧ g.as = lt.legalSig f.as ∧ g.rs = lt.legalSig f.rs := by
  have hsig_in : g.sig ∈ (M.midThenLateInline lt policyOf inlPol).fns.map Fn.sig :=
    List.mem_map_of_mem hg
  rw [M.midThenLateInline_fns_sigs lt policyOf inlPol, List.mem_map] at hsig_in
  rcases hsig_in with ⟨f, hf, hfeq⟩
  simp only [Fn.sig, Prod.mk.injEq] at hfeq
  exact ⟨f, hf, hfeq.1.symm, hfeq.2.1.symm, hfeq.2.2.symm⟩

private theorem list_split_mem {α : Type _} : ∀ {xs : List α} {x : α},
    x ∈ xs → ∃ pre post, xs = pre ++ x :: post
  | [], _, h => nomatch h
  | y :: ys, x, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact ⟨[], ys, rfl⟩
    · obtain ⟨pre, post, rfl⟩ := list_split_mem h'
      exact ⟨y :: pre, post, rfl⟩

private theorem midPolicy_fn_spec {lt : LegalTarget} {M : Module} {Γ : Env}
    (hnd : M.namesNodup) {f : Fn} (hf : f ∈ M.fns) (pol : SnippetOptPolicy)
    (hwf : f.Wf) (hsupp : (f.earlyOptPolicy pol).body.supportsSource lt = true)
    (hwp : ∀ xs m P E, Env.ofModule M Γ f.name f.as f.rs xs m P E →
      Func.wp (Env.ofModule M Γ) f.body xs m P E) :
    ∀ xs' m Q' X',
      legalEnv lt (Env.ofModule M Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs) xs' m Q' X' →
      Func.spec (legalEnv lt (Env.ofModule M Γ)) (f.midPolicy lt pol).body xs' m Q' X' := by
  intro xs' m Q' X' h
  rcases h with ⟨as, bs, has, hbs, xs, P, E, hxs, hQ, hX, hΓ⟩
  have heq : as = f.as ∧ bs = f.rs := by
    by_cases hp : (as, bs) = (f.as, f.rs)
    · exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
    · exact absurd hΓ (Env.ofModule_empty_off_sig hnd Γ hf hp xs m P E)
  obtain ⟨rfl, rfl⟩ := heq
  refine Fn.midPolicy_spec hwf hsupp (Env.ofModule M Γ)
    (by simpa only [cast_eq] using hxs) (fun r m₁ hr => by have := hQ r m₁ hr; rwa [cast_eq] at this)
    hX (hwp xs m P E hΓ)

/-- End-to-end compilation soundness for `compileLateInlined` (`Module.midThenLateInline` +
`compileDirectModule`), proving `T.Defined` and `T.FnSpec` at `legalEnv lt (Env.ofModule M Γ)`
for any `ModuleOk Γ M`. -/
theorem compileLateInlined_sound (T : Target) (host : T.mach.Host) (lt : LegalTarget)
    (M : Module) (policyOf : Sym → SnippetOptPolicy) (inlPol : InlinePolicy) (Γ : Env)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (hints : List T.toIsa.Hints) (code : List T.Directive) (bounds : List (Sym × Nat)) (k₀ : Nat)
    (hcm : compileLateInlined T.toIsa lt T.frame.raBytes extCallees exits nX M policyOf inlPol
      hints = .ok (code, bounds))
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hM : ModuleOk Γ M)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec host p.1.1 (legalEnv lt (Env.ofModule M Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ extCallees, p.1.1 ∉ M.fns.map Fn.name))
    (hexits : ∀ g ∈ exits, T.Defined host g) :
    ∀ p ∈ bounds, ∃ f ∈ M.fns, p.1 = f.name ∧ T.Defined host p.1 ∧
      T.FnSpec host p.1
        (legalEnv lt (Env.ofModule M Γ) p.1 (lt.legalSig f.as) (lt.legalSig f.rs)) p.2 nX := by
  dsimp only [compileLateInlined] at hcm
  split at hcm
  · rename_i hsuppAll
    have hsupp : ∀ f ∈ M.fns, (f.earlyOptPolicy (policyOf f.name)).body.supportsSource lt = true :=
      fun f hf => List.all_eq_true.mp hsuppAll f hf
    let Γ_mid := legalEnv lt (Env.ofModule M Γ)
    let M_mid := M.midPolicy lt policyOf
    let M_late := M.midThenLateInline lt policyOf inlPol
    have hMod := ModuleOk.ofModule hM
    have hwp_mod : ∀ f ∈ M.fns, f.Wf ∧ ∀ xs m Q X,
        Env.ofModule M Γ f.name f.as f.rs xs m Q X →
        Func.wp (Env.ofModule M Γ) f.body xs m Q X := by
      intro f hf
      obtain ⟨pre, post, hsplit⟩ := list_split_mem hf
      have ⟨hfwf, _, hfwp⟩ := hMod.fnsOk pre f post hsplit
      exact ⟨hfwf, hfwp⟩
    have hmid_ok : ∀ g ∈ M_mid.fns,
        g.Wf ∧ ∀ xs m Q X, Γ_mid g.name g.as g.rs xs m Q X → Func.wp Γ_mid g.body xs m Q X := by
      intro g hg
      dsimp only [M_mid, Module.midPolicy] at hg
      rw [List.mem_map] at hg
      rcases hg with ⟨f, hf, rfl⟩
      have ⟨hfwf, hfwp⟩ := hwp_mod f hf
      refine ⟨Fn.midPolicy_wf lt (policyOf f.name) hfwf, ?_⟩
      exact midPolicy_fn_spec hM.nodup hf (policyOf f.name) hfwf (hsupp f hf) hfwp
    have hlate_ok := Module.inlinePolicy_wf_wp (M := M_mid) (Γ := Γ_mid) inlPol
      (fun g hg => (hmid_ok g hg).1) (fun g hg => (hmid_ok g hg).2)
    have hMnd : (M.fns.map Fn.name).Nodup := (List.nodup_append.mp hM.nodup).1
    have hLateNd : (M_late.fns.map Fn.name).Nodup := by
      simpa [M_late, M.midThenLateInline_fns_names lt policyOf inlPol] using hMnd
    have hExDisj : ∀ p ∈ extCallees, p.1.1 ∉ M_late.fns.map Fn.name := by
      intro p hp
      simpa [M_late, M.midThenLateInline_fns_names lt policyOf inlPol] using hext_uniq.2 p hp
    intro p hp
    obtain ⟨g, hg, hgnm, hgdef, hgspec⟩ :=
      compileDirectModule_sound T host Γ_mid M_late.fns extCallees exits nX hints code bounds k₀
        hcm hc hu hLateNd
        (fun x hx => (hlate_ok x hx).1) (fun x hx => (hlate_ok x hx).2)
        hext ⟨hext_uniq.1, hExDisj⟩ hexits p hp
    obtain ⟨f, hf, hfnm, hfas, hfrs⟩ := sig_eq_of_mem_map_sig hg
    refine ⟨f, hf, hgnm.trans hfnm, hgdef, ?_⟩
    rw [← hfas, ← hfrs]
    exact hgspec
  · cases hcm

end LeanQbe.T
