module

public import LeanQbe.T.MainLink
public import LeanQbe.T.LinkBudgetLfp
public import LeanQbe.T.LinkUtil
import LeanQbe.T.OptLemmas
import LeanQbe.T.LegalLemmas
import LeanQbe.T.RegaLemmas

/-!
# Target-Parameterized Budget-SCC Linking & `Chunk` Sub-Chunking (`MainLinkScc`)

Target-independent compositional compilation and linking over `MainLink` and `LinkBudgetLfp`
(`BudgetModule`, `CompiledBudgetRec`, `RecBudgetSubChunk`), factoring `linkChunks_aux` via
`chunk_step_wp` and `chunk_sig_decomp`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

open Std Std.ExtHashMap
open LeanQbe.T.LinkRec
open LeanQbe.T.LinkScc

/-! ## 1. `machEnv`, `pullEnv`, and Shared SCC Linking Helpers -/

@[expose] def machEnv (T : Target) (h : T.mach.Host) (n nX : Nat) : Env :=
  fun sym _as bs args m Q X =>
    ∀ (s : T.mach.MData) (ra : T.mach.Addr) (R : Mem 64 → Prop),
      T.ArgsIn args s → T.frameSpec.raReg s ra →
      T.frameSpec.spEntry (T.mach.getGpr s T.frame.sp) →
      (T.mach.mem s =⋆ Eq m ⋆ T.Entry (T.mach.getGpr s T.frame.sp) ra n ⋆ R) →
      Eventually (T.mach.step h)
        (fun st =>
          (T.mach.pc st = ra ∧ ∃ (rets : Tup Val bs) (m' : Mem 64),
            Q rets m' ∧ T.RetsIn rets (T.mach.data st) ∧ T.Restored s (T.mach.data st) ∧
            (T.mach.mem (T.mach.data st) =⋆
              Eq m' ⋆ T.Exit (T.mach.getGpr s T.frame.sp) n ⋆ R)) ∨
          (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64),
            X sym' cs xs m' ∧ T.Defined h sym' ∧ T.mach.pc st = T.mach.labelAddr h sym' ∧
            T.ArgsIn xs (T.mach.data st) ∧
            T.frameSpec.spEntry (T.mach.getGpr (T.mach.data st) T.frame.sp) ∧
            ∃ (ra' : T.mach.Addr) (n' : Nat) (F : Mem 64 → Prop),
              nX ≤ n' ∧ n' + T.frame.raBytes ≤ 2 ^ 64 ∧ T.frameSpec.raReg (T.mach.data st) ra' ∧
              (T.mach.mem (T.mach.data st) =⋆
                Eq m' ⋆ T.Entry (T.mach.getGpr (T.mach.data st) T.frame.sp) ra' n' ⋆ F ⋆ R)))
        (T.mach.mkState s (T.mach.labelAddr h sym))

@[expose] def pullEnv (lt : LegalTarget) (G : Env) : Env :=
  fun f as bs xs m P E =>
    G f (lt.legalSig as) (lt.legalSig bs) (encodeTup lt as xs) m (legalPost lt P) (legalXPost lt E)

theorem fnSpec_iff_machEnv {T : Target} {h : T.mach.Host} {sym : Sym} {as bs : List Ty}
    {spec : Spec as bs} {n nX : Nat} :
    T.FnSpec h sym spec n nX ↔
      ∀ args m Q X, spec args m Q X → machEnv T h n nX sym as bs args m Q X := Iff.rfl

theorem machEnv_conseq (T : Target) (h : T.mach.Host) (n nX : Nat) :
    ∀ f as bs xs m (Q Q' : Post bs) (X X' : XPost),
      (∀ r m', Q r m' → Q' r m') → (∀ g cs ys m', X g cs ys m' → X' g cs ys m') →
      machEnv T h n nX f as bs xs m Q X → machEnv T h n nX f as bs xs m Q' X' := by
  intro f as bs xs m Q Q' X X' hQ hX hm s ra R ha hra hsp hmem
  refine eventually_weaken _ _ _ _ ?_ (hm s ra R ha hra hsp hmem)
  rintro st (⟨hpc, rets, m', hq, hrets, hrest, hmem'⟩ |
    ⟨sym', cs, xs', m', hx, hd, hpc, has, hsp', ra', n', F, hn', hb', hra', hmem'⟩)
  · exact Or.inl ⟨hpc, rets, m', hQ rets m' hq, hrets, hrest, hmem'⟩
  · exact Or.inr ⟨sym', cs, xs', m', hX sym' cs xs' m' hx, hd, hpc, has, hsp',
      ra', n', F, hn', hb', hra', hmem'⟩

theorem legalEnv_pullEnv_le (lt : LegalTarget) {G : Env}
    (hconseq : ∀ f as bs xs m (Q Q' : Post bs) (X X' : XPost),
      (∀ r m', Q r m' → Q' r m') → (∀ g cs ys m', X g cs ys m' → X' g cs ys m') →
      G f as bs xs m Q X → G f as bs xs m Q' X') :
    Env.le (legalEnv lt (pullEnv lt G)) G := by
  rintro f as' bs' xs' m Q' X' ⟨as, bs, has, hbs, xs, P, E, hxs, hQ, hX, hpull⟩
  subst has; subst hbs
  have hxs' : encodeTup lt as xs = xs' := by simpa only [cast_eq] using hxs
  have hQ' : ∀ r m₁, legalPost lt P r m₁ → Q' r m₁ := fun r m₁ hp => by
    have := hQ r m₁ hp; rwa [cast_eq] at this
  subst hxs'
  exact hconseq f (lt.legalSig as) (lt.legalSig bs) (encodeTup lt as xs) m
    (legalPost lt P) Q' (legalXPost lt E) X' hQ' hX hpull

private theorem compileFn_body_correct (T : Target) (host : T.mach.Host) (lt : LegalTarget)
    (hints : T.toIsa.Hints) (E : Rega.Ext) (f : Fn) (Γcall : Env) (n nX : Nat) (bound : Sym → Nat)
    {code : List T.Directive} {k₀ : Nat} (hwf : f.Wf)
    (hsupp : (f.earlyOpt).body.supportsSource lt = true)
    (hl : Rega.lowerFn T.toIsa hints E (f.mid lt) = .ok code)
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hfr : Rega.effFrame T.toIsa hints E ≤ n) (hn : n + T.frame.raBytes ≤ 2 ^ 64)
    (hcal : ∀ g as bs, (g, as, bs) ∈ E.callees →
      T.FnSpec host g (legalEnv lt Γcall g as bs) (bound g) nX ∧
      Rega.effFrame T.toIsa hints E + T.frame.raBytes + bound g ≤ n)
    (hex : ∀ g, g ∈ E.exits → T.Defined host g ∧ nX ≤ n) :
    ∀ xs m P E', Func.wp Γcall f.body xs m P E' →
      machEnv T host n nX f.name (lt.legalSig f.as) (lt.legalSig f.rs)
        (encodeTup lt f.as xs) m (legalPost lt P) (legalXPost lt E') := by
  intro xs m P E' hwp
  have hspec : T.FnSpec host f.name (fun args' m' Q' X' =>
      args' = encodeTup lt f.as xs ∧ m' = m ∧
      Q' = legalPost lt P ∧ X' = legalXPost lt E') n nX := by
    refine Target.FnSpec.of_spec T (Rega.lowerFn_correct T host hints E (f.mid lt)
      (legalEnv lt Γcall) n nX bound (fn_mid_wf hwf) hl hc hu hfr hn hcal hex) ?_
    rintro args' m' Q' X' ⟨rfl, hm, rfl, rfl⟩; subst m'
    exact @fn_mid_spec lt f hwf hsupp Γcall xs (encodeTup lt f.as xs) rfl m P E'
      (legalPost lt P) (legalXPost lt E') (fun _ _ h => h) (fun _ _ _ _ h => h) hwp
  exact hspec (encodeTup lt f.as xs) m (legalPost lt P) (legalXPost lt E') ⟨rfl, rfl, rfl, rfl⟩

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
                | ok _ => simp only [hle, Except.ok.injEq] at hl; subst hl
                          exact ⟨k₀, (List.IsInfixAt.cons hc).1⟩

private theorem extCallee_fnSpec {T : Target} {h : T.mach.Host} {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {extSigs : List SigEntry} {fnNames : List Sym}
    {Γcall Γext : Env} {nX : Nat}
    (hext : ∀ p ∈ extCallees,
      T.FnSpec h p.1.1 (legalEnv lt (Env.restrict Γext extSigs) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : ∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2)
    (hdisj : ∀ p ∈ extCallees, p.1.1 ∉ fnNames)
    (hstep : ∀ g, g ∉ fnNames → ∀ as bs xs m Q X,
      legalEnv lt Γcall g as bs xs m Q X →
      legalEnv lt (Env.restrict Γext extSigs) g as bs xs m Q X)
    {g : Sym} {as' bs' : List Ty} {bg : Nat}
    (hlk : lookupBound extCallees (g, as', bs') = some bg) :
    fnNames.contains g = false ∧
      (match extCallees.find? (fun q => q.1.1 == g) with | some q => q.2 | none => 0) = bg ∧
      T.FnSpec h g (legalEnv lt Γcall g as' bs') bg nX := by
  have hmem := lookupBound_mem hlk; have hnot : g ∉ fnNames := hdisj ((g, as', bs'), bg) hmem
  refine ⟨by simpa [List.contains_eq_mem] using hnot, ?_,
    Target.FnSpec.of_spec T (hext ((g, as', bs'), bg) hmem) (hstep g hnot as' bs')⟩
  cases hfnd : extCallees.find? (fun q => q.1.1 == g) with
  | none => exfalso; have := List.find?_eq_none.mp hfnd ((g, as', bs'), bg) hmem; simp at this
  | some q =>
      exact hext_uniq q (List.mem_of_find?_eq_some hfnd) ((g, as', bs'), bg) hmem
        (beq_iff_eq.mp (list_find?_pred (p := fun q : SigEntry × Nat => q.1.1 == g) hfnd))

private theorem recCallee_sccStep_fnSpec {T : Target} {h : T.mach.Host} {lt : LegalTarget}
    {M : Module} (hnd : M.namesNodup) {Γrec Γext : Env} {b nX : Nat} {gfn : Fn}
    (hgfn : gfn ∈ M.fns) (hrec : Env.le Γrec (pullEnv lt (machEnv T h b nX))) :
    T.FnSpec h gfn.name
      (legalEnv lt (Env.sccStep M Γrec Γext) gfn.name (lt.legalSig gfn.as) (lt.legalSig gfn.rs))
      b nX := by
  intro args' m0 Q' X' ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hst⟩
  rcases hst with ⟨_, hG⟩ | ⟨hmemE, _⟩
  · exact legalEnv_pullEnv_le lt (machEnv_conseq T h b nX) gfn.name _ _ args' m0 Q' X'
      ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hrec gfn.name as₀ bs₀ xs₀ m0 P₀ E₀ hG⟩
  · exact absurd hmemE (fn_name_not_mem_externs_mod hnd hgfn)

private theorem link_scc_extract_fnSpec {T : Target} {h : T.mach.Host} {lt : LegalTarget}
    {b nX : Nat} {f : Fn} {S : Env}
    (hle : ∀ xs₀ m P₀ E₀, S f.name f.as f.rs xs₀ m P₀ E₀ →
      pullEnv lt (machEnv T h b nX) f.name f.as f.rs xs₀ m P₀ E₀) :
    T.FnSpec h f.name
      (legalEnv lt (Env.onlyFn f S) f.name (lt.legalSig f.as) (lt.legalSig f.rs)) b nX := by
  intro args m Q X ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, _, ha, hb, hsem⟩
  subst ha; subst hb
  exact legalEnv_pullEnv_le lt (machEnv_conseq T h b nX)
    f.name (lt.legalSig f.as) (lt.legalSig f.rs) args m Q X
    ⟨f.as, f.rs, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hle xs₀ m P₀ E₀ hsem⟩

private theorem link_scc_extCallee_step {T : Target} {h : T.mach.Host} {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {extSigs : List SigEntry} {fnNames : List Sym}
    {Γcall Γext : Env} {nX : Nat} {g : Sym} {as' bs' : List Ty} {bg F sb : Nat}
    (hext : ∀ p ∈ extCallees,
      T.FnSpec h p.1.1 (legalEnv lt (Env.restrict Γext extSigs) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : ∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2)
    (hdisj : ∀ p ∈ extCallees, p.1.1 ∉ fnNames)
    (hstep : ∀ g, g ∉ fnNames → ∀ as bs xs m Q X,
      legalEnv lt Γcall g as bs xs m Q X →
      legalEnv lt (Env.restrict Γext extSigs) g as bs xs m Q X)
    (hlk : lookupBound extCallees (g, as', bs') = some bg)
    (hle : F + T.frame.raBytes + bg ≤ sb) (brec : Nat) :
    T.FnSpec h g (legalEnv lt Γcall g as' bs')
      (if fnNames.contains g then brec
        else match extCallees.find? (fun q => q.1.1 == g) with | some q => q.2 | none => 0) nX ∧
      F + T.frame.raBytes + (if fnNames.contains g then brec
        else match extCallees.find? (fun q => q.1.1 == g) with
          | some q => q.2 | none => 0) ≤ sb := by
  obtain ⟨hcon, hbd, hfn⟩ := extCallee_fnSpec hext hext_uniq hdisj hstep hlk
  simp only [hcon, Bool.false_eq_true, ↓reduceIte, hbd]; exact ⟨hfn, hle⟩

/-! ## 2. Shared Sub-Chunk Helpers, `CompiledBudgetRec`, and `link_scc_budget_lfp` -/

private theorem ext_disj_of_forall {α : Type _} (getName : α → Sym)
    {ext : List (SigEntry × Nat)} {xs : List α} (hdisj : ∀ p ∈ ext, p.1.1 ∉ xs.map getName) :
    ext.any (fun p => xs.any (fun x => getName x == p.1.1)) = false := by
  cases hne : ext.any (fun p => xs.any (fun x => getName x == p.1.1)) with
  | false => rfl
  | true =>
      obtain ⟨p, hp, hf⟩ := List.any_eq_true.mp hne
      obtain ⟨x, hxm, hnm⟩ := List.any_eq_true.mp hf
      exact absurd ((beq_iff_eq.mp hnm) ▸ List.mem_map_of_mem hxm) (hdisj p hp)

private theorem ext_disj_names_to_items {α : Type _} (getName : α → Sym)
    {extCallees : List (SigEntry × Nat)} {xs : List α}
    (h : !(extCallees.any (fun p => (xs.map getName).any (fun nm => nm == p.1.1))) = true) :
    (extCallees.any (fun p => xs.any (fun x => getName x == p.1.1))) = false :=
  bool_not_eq_false (by simpa [List.any_map, Function.comp_def] using h)

@[expose] def sigListBeq : List SigEntry → List SigEntry → Bool
  | [], [] => true
  | a :: as, b :: bs => SigEntry.beq a b && sigListBeq as bs
  | _, _ => false
theorem sigListBeq_eq : ∀ {xs ys : List SigEntry}, sigListBeq xs ys = true → xs = ys
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
      dsimp only [sigListBeq] at h; simp only [Bool.and_eq_true, SigEntry.beq_iff_eq] at h
      rw [h.1, sigListBeq_eq h.2]

/-- Common subchunk & linked-host layout/name metadata checker shared across `RecBudgetSubChunk`
and `checkLinkSccList`. -/
@[expose] def checkHostNamesOk {T : Target} (L : TargetLayout T) (exits : List Sym)
    (fnNames : List Sym) (code : List T.Directive) : Bool :=
  fnNames.all fnNameOk && exits.all fnNameOk && stringsNodup (fnNames ++ exits) &&
  L.progSmall (code ++ exits.map T.frame.label)

@[expose] def checkBudgetCallees (F raBytes minEntry : Nat) (recSigs : List SigEntry)
    (extCallees : List (SigEntry × Nat)) (gs : List SigEntry) : Bool :=
  gs.all fun g =>
    if recSigs.any (SigEntry.beq g) then true
    else match lookupBound extCallees g with
      | some bg => Nat.ble (F + raBytes + bg) minEntry | none => false

@[expose] def checkAndBoundBudgetRecExt (I : Isa) (raBytes : Nat) (recSigs : List SigEntry)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (h : I.Hints) (ext : Rega.Ext) (bfn : BudgetFn) : Bool :=
  let F := Rega.effFrame I h ext
  Nat.ble (F + raBytes) bfn.maxFrame &&
  checkBudgetCallees F raBytes bfn.minEntry recSigs extCallees ext.callees &&
  ext.exits.all (fun g => exits.contains g) && (ext.exits.isEmpty || Nat.ble nX bfn.minEntry)

@[expose] def checkAndBoundBudgetRecMid (I : Isa) (raBytes : Nat) (recSigs : List SigEntry)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (h : I.Hints) (mf : Fn) (bfn : BudgetFn) : Bool :=
  checkAndBoundBudgetRecExt I raBytes recSigs extCallees exits nX h mf.ext bfn

@[expose] def checkAndBoundBudgetRec (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (recSigs : List SigEntry) (extCallees : List (SigEntry × Nat)) (exits : List Sym)
    (nX : Nat) (bfn : BudgetFn) (h : I.Hints) : Bool :=
  checkAndBoundBudgetRecMid I raBytes recSigs extCallees exits nX h (bfn.toFn.mid lt) bfn

@[expose] def compileModuleBudgetRecAux (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (recSigs : List SigEntry) (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat) :
    List BudgetFn → List I.Hints → Except String (List I.Directive)
  | [], [] => .ok []
  | bfn :: bfs, h :: hs =>
    let f := bfn.toFn; let mf := f.mid lt
    match Rega.lowerFn I h mf.ext mf,
          checkAndBoundBudgetRecExt I raBytes recSigs extCallees exits nX h mf.ext bfn with
    | .ok c, true =>
      match compileModuleBudgetRecAux I lt raBytes recSigs extCallees exits nX bfs hs with
      | .ok cs => .ok (c ++ cs) | .error e => .error e
    | .error e, _ => .error s!"{f.name}: {e}"
    | _, false => .error s!"{f.name}: frame/callee budget exceeded or unknown callee/exit"
  | _, _ => .error "compileModuleBudgetRec: fn/hints length mismatch"

@[expose] def compileModuleBudgetRec (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX maxBound : Nat)
    (bfs : List BudgetFn) (hints : List I.Hints) (exportBounds : List (Sym × Nat) := []) :
    Except String (List I.Directive) :=
  let recSigs := bfs.map fun b => (b.toFn.name, lt.legalSig b.toFn.as, lt.legalSig b.toFn.rs)
  if extCallees.any (fun p => bfs.any (fun b => b.toFn.name == p.1.1)) then
    .error "compileModuleBudgetRec: external callee collides with module function"
  else if !(Nat.ble maxBound (2 ^ 64) && Nat.ble (maxBound + raBytes) (2 ^ 64) &&
      exportBounds.all (fun p => Nat.ble p.2 maxBound)) then
    .error s!"compileModuleBudgetRec: stack bound overflow (maxBound={maxBound})"
  else compileModuleBudgetRecAux I lt raBytes recSigs extCallees exits nX bfs hints

@[expose] def budgetBound (exportBounds : List (Sym × Nat)) (maxBound : Nat) (nm : Sym) : Nat :=
  (lookupFnBound exportBounds nm).getD maxBound

@[expose] def budgetRecSigsOf (lt : LegalTarget) (bfs : List BudgetFn) : List SigEntry :=
  bfs.map fun b => (b.toFn.name, lt.legalSig b.toFn.as, lt.legalSig b.toFn.rs)

@[expose] def sigBoundsBudgetRecOf (lt : LegalTarget) (bfs : List BudgetFn)
    (exportBounds : List (Sym × Nat)) (maxBound : Nat) : List (SigEntry × Nat) :=
  bfs.map fun b =>
    ((b.toFn.name, lt.legalSig b.toFn.as, lt.legalSig b.toFn.rs),
      budgetBound exportBounds maxBound b.toFn.name)

@[expose] def checkCompileBudgetRecResult {D : Type} (label : Sym → D) (progSmall : List D → Bool)
    (res : Except String (List D)) (fnNames exits : List Sym) : Bool :=
  match res with
  | .error _ => false
  | .ok code => fnNames.all fnNameOk && exits.all fnNameOk &&
      stringsNodup (fnNames ++ exits) && progSmall (code ++ exits.map label)

@[expose] def extractBudgetRecCode {D : Type} : Except String (List D) → List D
  | .ok c => c | .error _ => []

attribute [irreducible] extractBudgetRecCode

private theorem checkBudgetCallees_spec {F raBytes minEntry : Nat} {recSigs : List SigEntry}
    {extCallees : List (SigEntry × Nat)} {gs : List SigEntry}
    (h : checkBudgetCallees F raBytes minEntry recSigs extCallees gs = true) :
    ∀ g ∈ gs, g ∈ recSigs ∨ (g ∉ recSigs ∧ ∃ bg, lookupBound extCallees g = some bg ∧
      F + raBytes + bg ≤ minEntry) := by
  intro g hg; have hall := List.all_eq_true.mp h g hg
  by_cases hrec : recSigs.any (SigEntry.beq g) = true
  · obtain ⟨s, hs, heq⟩ := List.any_eq_true.mp hrec
    exact Or.inl ((SigEntry.beq_iff_eq.mp heq) ▸ hs)
  · have hrec_f := Bool.eq_false_iff.mpr hrec
    rw [hrec_f] at hall; simp only [Bool.false_eq_true, ↓reduceIte] at hall
    have hnr : g ∉ recSigs := fun hm =>
      hrec (List.any_eq_true.mpr ⟨g, hm, SigEntry.beq_iff_eq.mpr rfl⟩)
    cases hlk : lookupBound extCallees g with
    | none => rw [hlk] at hall; simp at hall
    | some bg => rw [hlk] at hall; exact Or.inr ⟨hnr, bg, rfl, Nat.le_of_ble_eq_true hall⟩

private theorem checkAndBoundBudgetRecExt_spec {I : Isa} {raBytes : Nat}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {h : I.Hints} {ext : Rega.Ext} {bfn : BudgetFn}
    (hc : checkAndBoundBudgetRecExt I raBytes recSigs extCallees exits nX h ext bfn = true) :
    Rega.effFrame I h ext + raBytes ≤ bfn.maxFrame ∧
      (∀ g ∈ ext.callees, g ∈ recSigs ∨
        (g ∉ recSigs ∧ ∃ bg, lookupBound extCallees g = some bg ∧
          Rega.effFrame I h ext + raBytes + bg ≤ bfn.minEntry)) ∧
      (∀ g ∈ ext.exits, g ∈ exits ∧ nX ≤ bfn.minEntry) := by
  dsimp only [checkAndBoundBudgetRecExt] at hc; simp only [Bool.and_eq_true] at hc
  refine ⟨Nat.le_of_ble_eq_true hc.1.1.1, checkBudgetCallees_spec hc.1.1.2, fun g hg => ?_⟩
  have hne : ext.exits.isEmpty = false := by cases he : ext.exits <;> simp_all
  have hor := hc.2; rw [hne] at hor; simp only [Bool.false_or] at hor
  exact ⟨by simpa using List.all_eq_true.mp hc.1.2 g hg, Nat.le_of_ble_eq_true hor⟩

private theorem checkBudgetCallees_mono_lookupBound {F raBytes minEntry : Nat}
    {recSigs : List SigEntry} {ext₁ ext₂ : List (SigEntry × Nat)}
    (hmono : ∀ g bg, lookupBound ext₁ g = some bg → lookupBound ext₂ g = some bg)
    {gs : List SigEntry} (hc : checkBudgetCallees F raBytes minEntry recSigs ext₁ gs = true) :
    checkBudgetCallees F raBytes minEntry recSigs ext₂ gs = true := by
  dsimp only [checkBudgetCallees] at hc ⊢; rw [List.all_eq_true] at hc ⊢
  intro g hg; have h1 := hc g hg
  by_cases hrec : recSigs.any (SigEntry.beq g) = true
  · simp only [hrec, ↓reduceIte]
  · simp only [Bool.eq_false_iff.mpr hrec, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
    cases hlk : lookupBound ext₁ g with
    | none => rw [hlk] at h1; simp at h1
    | some bg => rw [hlk] at h1; rw [hmono g bg hlk]; exact h1

private theorem checkAndBoundBudgetRecExt_mono_lookupBound {I : Isa} {raBytes : Nat}
    {recSigs : List SigEntry} {extCallees₁ extCallees₂ : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} {h : I.Hints} {ext : Rega.Ext} {bfn : BudgetFn}
    (hmono : ∀ g bg, lookupBound extCallees₁ g = some bg → lookupBound extCallees₂ g = some bg)
    (hc : checkAndBoundBudgetRecExt I raBytes recSigs extCallees₁ exits nX h ext bfn = true) :
    checkAndBoundBudgetRecExt I raBytes recSigs extCallees₂ exits nX h ext bfn = true := by
  dsimp only [checkAndBoundBudgetRecExt] at hc ⊢; simp only [Bool.and_eq_true] at hc ⊢
  exact ⟨⟨⟨hc.1.1.1, checkBudgetCallees_mono_lookupBound hmono hc.1.1.2⟩, hc.1.2⟩, hc.2⟩

private def budgetLoopStep (I : Isa) (lt : LegalTarget) (raBytes : Nat) (recSigs : List SigEntry)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (bfn : BudgetFn) (h : I.Hints) : Except String (List I.Directive × Unit) :=
  let f := bfn.toFn; let mf := f.mid lt
  match Rega.lowerFn I h mf.ext mf,
        checkAndBoundBudgetRecExt I raBytes recSigs extCallees exits nX h mf.ext bfn with
  | .ok c, true => .ok (c, ())
  | .error e, _ => .error s!"{f.name}: {e}"
  | _, false => .error s!"{f.name}: frame/callee budget exceeded or unknown callee/exit"

private theorem compileModuleBudgetRecAux_eq_map (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (recSigs : List SigEntry) (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat) :
    ∀ (bfs : List BudgetFn) (hints : List I.Hints),
      compileModuleBudgetRecAux I lt raBytes recSigs extCallees exits nX bfs hints =
        (compileSeqLoop () (fun _ _ => ()) (budgetLoopStep I lt raBytes recSigs extCallees exits nX)
          "compileModuleBudgetRec: fn/hints length mismatch" bfs hints).map Prod.fst
  | [], [] => rfl
  | [], _ :: _ | _ :: _, [] => by simp [compileModuleBudgetRecAux, compileSeqLoop, Except.map]
  | bfn :: bfs, h :: hs => by
      dsimp only [compileModuleBudgetRecAux, compileSeqLoop, budgetLoopStep]
      cases Rega.lowerFn I h (bfn.toFn.mid lt).ext (bfn.toFn.mid lt) with
      | error _ => simp [Except.map]
      | ok _ =>
          cases checkAndBoundBudgetRecExt I raBytes recSigs extCallees exits nX h
              (bfn.toFn.mid lt).ext bfn with
          | false => simp [Except.map]
          | true =>
              dsimp only
              rw [compileModuleBudgetRecAux_eq_map I lt raBytes recSigs extCallees exits nX bfs hs]
              cases compileSeqLoop () (fun _ _ => ())
                  (budgetLoopStep I lt raBytes recSigs extCallees exits nX)
                  "compileModuleBudgetRec: fn/hints length mismatch" bfs hs <;> rfl

private theorem compileModuleBudgetRecAux_eq_loop (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (recSigs : List SigEntry) (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (bfs : List BudgetFn) (hints : List I.Hints) (code : List I.Directive) :
    compileModuleBudgetRecAux I lt raBytes recSigs extCallees exits nX bfs hints = .ok code ↔
      compileSeqLoop () (fun _ _ => ()) (budgetLoopStep I lt raBytes recSigs extCallees exits nX)
        "compileModuleBudgetRec: fn/hints length mismatch" bfs hints = .ok (code, ()) := by
  rw [compileModuleBudgetRecAux_eq_map]
  cases compileSeqLoop () (fun _ _ => ())
      (budgetLoopStep I lt raBytes recSigs extCallees exits nX)
      "compileModuleBudgetRec: fn/hints length mismatch" bfs hints with
  | error _ => simp [Except.map] | ok r => rcases r with ⟨c, ⟨⟩⟩; simp [Except.map]

theorem compileModuleBudgetRecAux_mono_lookupBound {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {recSigs : List SigEntry} {exits : List Sym} {nX : Nat} {ext₁ ext₂ : List (SigEntry × Nat)}
    {bfs : List BudgetFn} {hints : List I.Hints} {code : List I.Directive}
    (hmono : ∀ g bg, lookupBound ext₁ g = some bg → lookupBound ext₂ g = some bg)
    (h : compileModuleBudgetRecAux I lt raBytes recSigs ext₁ exits nX bfs hints = .ok code) :
    compileModuleBudgetRecAux I lt raBytes recSigs ext₂ exits nX bfs hints = .ok code := by
  rw [compileModuleBudgetRecAux_eq_loop] at h ⊢
  refine compileSeqLoop_mono (fun bfn hint _ _ hst => ?_) h
  dsimp only [budgetLoopStep] at hst ⊢
  cases hl : Rega.lowerFn I hint (bfn.toFn.mid lt).ext (bfn.toFn.mid lt) with
  | error _ => simp [hl] at hst
  | ok _ =>
      cases hc : checkAndBoundBudgetRecExt I raBytes recSigs ext₁ exits nX hint
          (bfn.toFn.mid lt).ext bfn with
      | false => simp [hl, hc] at hst
      | true =>
          simp only [hl, hc] at hst
          simpa [hl, checkAndBoundBudgetRecExt_mono_lookupBound hmono hc] using hst

theorem compileModuleBudgetRec_mono_lookupBound {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {ext₁ ext₂ : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}
    {bfs : List BudgetFn} {hints : List I.Hints} {exportBounds : List (Sym × Nat)}
    {code : List I.Directive}
    (hmono : ∀ g bg, lookupBound ext₁ g = some bg → lookupBound ext₂ g = some bg)
    (hdisj : ∀ p ∈ ext₂, p.1.1 ∉ bfs.map (fun b => b.toFn.name))
    (h : compileModuleBudgetRec I lt raBytes ext₁ exits nX maxBound
      bfs hints exportBounds = .ok code) :
    compileModuleBudgetRec I lt raBytes ext₂ exits nX maxBound
      bfs hints exportBounds = .ok code := by
  dsimp only [compileModuleBudgetRec] at h ⊢; split at h
  · simp at h
  · rw [ext_disj_of_forall (fun b : BudgetFn => b.toFn.name) hdisj]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hov : (!(Nat.ble maxBound (2 ^ 64) && Nat.ble (maxBound + raBytes) (2 ^ 64) &&
        exportBounds.all (fun p => Nat.ble p.2 maxBound))) = true
    · simp [hov] at h
    · simp only [hov] at h ⊢; exact compileModuleBudgetRecAux_mono_lookupBound hmono h

theorem compile_of_compileModuleBudgetRec {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}
    {bfs : List BudgetFn} {hints : List I.Hints} {exportBounds : List (Sym × Nat)}
    {code : List I.Directive}
    (h : compileModuleBudgetRec I lt raBytes extCallees exits nX maxBound bfs hints exportBounds =
      .ok code) : compile I lt (bfs.map BudgetFn.toFn) hints = .ok code := by
  dsimp only [compileModuleBudgetRec] at h
  split at h; · simp at h
  split at h; · simp at h
  rw [compileModuleBudgetRecAux_eq_loop] at h
  refine compileSeqLoop_compile BudgetFn.toFn (fun bfn hint _ _ hst => ?_) h
  dsimp only [budgetLoopStep] at hst
  cases hl : Rega.lowerFn I hint (bfn.toFn.mid lt).ext (bfn.toFn.mid lt) with
  | error _ => simp [hl] at hst
  | ok c' =>
      cases hc : checkAndBoundBudgetRecExt I raBytes
          (bfs.map fun b => (b.toFn.name, lt.legalSig b.toFn.as, lt.legalSig b.toFn.rs))
          extCallees exits nX hint (bfn.toFn.mid lt).ext bfn with
      | false => simp [hl, hc] at hst
      | true => simp only [hl, hc, Except.ok.injEq, Prod.mk.injEq] at hst; rw [← hst.1]; exact hl

theorem compileModuleBudgetRec_bounds_le {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}
    {bfs : List BudgetFn} {hints : List I.Hints} {exportBounds : List (Sym × Nat)}
    {code : List I.Directive}
    (h : compileModuleBudgetRec I lt raBytes extCallees exits nX maxBound bfs hints exportBounds =
      .ok code) :
    maxBound ≤ 2 ^ 64 ∧ maxBound + raBytes ≤ 2 ^ 64 ∧
      exportBounds.all (fun p => Nat.ble p.2 maxBound) = true := by
  dsimp only [compileModuleBudgetRec] at h
  split at h; · simp at h
  split at h; · simp at h
  · rename_i hok; simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true] at hok
    exact ⟨Nat.le_of_ble_eq_true hok.1.1, Nat.le_of_ble_eq_true hok.1.2, hok.2⟩

private theorem compileModuleBudgetRecAux_mem {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {bfs : List BudgetFn} {hints : List I.Hints} {code : List I.Directive}
    (h : compileModuleBudgetRecAux I lt raBytes recSigs extCallees exits nX bfs hints = .ok code) :
    ∀ bfn ∈ bfs, ∃ hint c k_f,
      Rega.lowerFn I hint (bfn.toFn.mid lt).ext (bfn.toFn.mid lt) = .ok c ∧
      c.IsInfixAt code k_f ∧ k_f ≤ code.length ∧
      checkAndBoundBudgetRecExt I raBytes recSigs extCallees exits nX hint
        (bfn.toFn.mid lt).ext bfn = true := by
  rw [compileModuleBudgetRecAux_eq_loop] at h; intro bfn hbfn
  obtain ⟨hint, c, k_f, _, hst, hinf, hklen⟩ := compileSeqLoop_mem h bfn hbfn
  dsimp only [budgetLoopStep] at hst
  cases hl : Rega.lowerFn I hint (bfn.toFn.mid lt).ext (bfn.toFn.mid lt) with
  | error _ => simp [hl] at hst
  | ok _ =>
      cases hc : checkAndBoundBudgetRecExt I raBytes recSigs extCallees exits nX hint
          (bfn.toFn.mid lt).ext bfn with
      | false => simp [hl, hc] at hst
      | true =>
          simp only [hl, hc, Except.ok.injEq, Prod.mk.injEq] at hst
          rcases hst with ⟨rfl, _⟩; exact ⟨hint, _, k_f, hl, hinf, hklen, hc⟩

theorem compileModuleBudgetRec_labelsUnique {T : Target} (hcl : Rega.LabelClean T.toIsa)
    {lt : LegalTarget} {raBytes : Nat} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX maxBound : Nat} {bfs : List BudgetFn} {hints : List T.toIsa.Hints}
    {exportBounds : List (Sym × Nat)} {code : List T.Directive}
    (hcm : compileModuleBudgetRec T.toIsa lt raBytes extCallees exits nX maxBound bfs hints
      exportBounds = .ok code)
    (hnd : (bfs.map (fun b => b.toFn.name) ++ exits).Nodup)
    (hok : (bfs.map (fun b => b.toFn.name) ++ exits).all fnNameOk = true) :
    ∀ (i j : Nat) (l : Sym),
      (code ++ exits.map T.frame.label)[i]? = some (T.frame.label l) →
      (code ++ exits.map T.frame.label)[j]? = some (T.frame.label l) → i = j :=
  compile_labelsUnique hcl (compile_of_compileModuleBudgetRec hcm)
    (by simpa [List.map_map, Function.comp_def] using hnd)
    (by simpa [List.map_map, Function.comp_def] using hok)

private theorem compileModuleBudgetRec_disjoint {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}
    {bfs : List BudgetFn} {hints : List I.Hints} {exportBounds : List (Sym × Nat)}
    {code : List I.Directive}
    (h : compileModuleBudgetRec I lt raBytes extCallees exits nX maxBound bfs hints exportBounds =
      .ok code) :
    (∀ p ∈ extCallees, p.1.1 ∉ bfs.map (fun b => b.toFn.name)) ∧
      compileModuleBudgetRecAux I lt raBytes
        (bfs.map fun b => (b.toFn.name, lt.legalSig b.toFn.as, lt.legalSig b.toFn.rs))
        extCallees exits nX bfs hints = .ok code := by
  dsimp only [compileModuleBudgetRec] at h; split at h; · simp at h
  · rename_i hno; split at h; · simp at h
    · refine ⟨fun p hp hm => ?_, h⟩
      obtain ⟨b, hb, hnm⟩ := List.mem_map.mp hm
      exact hno (List.any_eq_true.mpr ⟨p, hp, List.any_eq_true.mpr ⟨b, hb, beq_iff_eq.mpr hnm⟩⟩)

structure CompiledBudgetRec (T : Target) (lt : LegalTarget) (extCallees : List (SigEntry × Nat))
    (exits : List Sym) (nX : Nat) (bfs : List BudgetFn) (hints : List T.toIsa.Hints)
    (maxBound : Nat := 2048) (exportBounds : List (Sym × Nat) := []) where
  code : List T.Directive
  compileModuleBudgetRec_eq :
    compileModuleBudgetRec T.toIsa lt T.frame.raBytes extCallees exits nX maxBound
      bfs hints exportBounds = .ok code
  compile_eq : compile T.toIsa lt (bfs.map BudgetFn.toFn) hints = .ok code
  maxBound_le : maxBound ≤ 2 ^ 64
  total_ra_le : maxBound + T.frame.raBytes ≤ 2 ^ 64
  exportBounds_le : exportBounds.all (fun p => Nat.ble p.2 maxBound) = true
  host : T.mach.Host
  prog_host : T.mach.prog host = code ++ exits.map T.frame.label
  labelsUnique : T.LabelsUnique host

namespace CompiledBudgetRec
variable {T : Target} {lt : LegalTarget} {extCallees : List (SigEntry × Nat)}
  {exits : List Sym} {nX : Nat} {bfs : List BudgetFn} {hints : List T.toIsa.Hints}
  {maxBound : Nat} {exportBounds : List (Sym × Nat)}
@[expose] def bound
    (_M : CompiledBudgetRec T lt extCallees exits nX bfs hints maxBound exportBounds)
    (nm : Sym) : Nat := budgetBound exportBounds maxBound nm
@[expose] def sigBounds
    (_M : CompiledBudgetRec T lt extCallees exits nX bfs hints maxBound exportBounds) :
    List (SigEntry × Nat) := sigBoundsBudgetRecOf lt bfs exportBounds maxBound
theorem bound_le_max
    (M : CompiledBudgetRec T lt extCallees exits nX bfs hints maxBound exportBounds)
    (nm : Sym) : M.bound nm ≤ maxBound := by
  dsimp only [bound, budgetBound]
  cases hlk : lookupFnBound exportBounds nm with
  | none => exact Nat.le_refl _
  | some _ =>
      exact Nat.le_of_ble_eq_true (List.all_eq_true.mp M.exportBounds_le _ (lookupFnBound_mem hlk))
theorem bound_ra_le
    (M : CompiledBudgetRec T lt extCallees exits nX bfs hints maxBound exportBounds)
    (nm : Sym) : M.bound nm + T.frame.raBytes ≤ 2 ^ 64 :=
  Nat.le_trans (Nat.add_le_add_right (M.bound_le_max nm) _) M.total_ra_le
theorem code_infix_host
    (M : CompiledBudgetRec T lt extCallees exits nX bfs hints maxBound exportBounds) :
    M.code.IsInfixAt (T.mach.prog M.host) 0 := by
  rw [M.prog_host]; exact ⟨exits.map T.frame.label, rfl⟩
theorem defined_exit_host
    (M : CompiledBudgetRec T lt extCallees exits nX bfs hints maxBound exportBounds)
    {g : Sym} (hg : g ∈ exits) : T.Defined M.host g := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
  refine ⟨M.code.length + i, ?_⟩
  rw [M.prog_host, List.getElem?_append_right (by omega), List.getElem?_map]; simp [hi]
end CompiledBudgetRec

@[expose] def checkCompileBudgetRecLit {D : Type} (label : Sym → D) (progSmall : List D → Bool)
    (code : List D) (fnNames exits : List Sym) : Bool :=
  checkCompileBudgetRecResult label progSmall (.ok code) fnNames exits

theorem checkCompileBudgetRecLit_parts {D : Type} {label : Sym → D}
    {progSmall : List D → Bool} {code : List D} {fnNames exits : List Sym}
    (h : checkCompileBudgetRecLit label progSmall code fnNames exits = true) :
    fnNames.all fnNameOk = true ∧ exits.all fnNameOk = true ∧
      (fnNames ++ exits).Nodup ∧ progSmall (code ++ exits.map label) = true := by
  simp only [checkCompileBudgetRecLit, checkCompileBudgetRecResult, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, stringsNodup_nodup h.1.2, h.2⟩

@[expose] def compileCheckedBudgetRecLit (T : Target) (L : TargetLayout T) (lt : LegalTarget)
    (hcl : Rega.LabelClean T.toIsa) (extCallees : List (SigEntry × Nat)) (exits : List Sym)
    (nX : Nat) (bfs : List BudgetFn) (hints : List T.toIsa.Hints) (maxBound : Nat := 2048)
    (exportBounds : List (Sym × Nat) := []) (code : List T.Directive)
    (hcm : compileModuleBudgetRec T.toIsa lt T.frame.raBytes extCallees exits nX maxBound
      bfs hints exportBounds = .ok code)
    (hchk : checkCompileBudgetRecLit T.frame.label L.progSmall code
      (bfs.map (fun b => b.toFn.name)) exits = true) :
    CompiledBudgetRec T lt extCallees exits nX bfs hints maxBound exportBounds where
  code := code; compileModuleBudgetRec_eq := hcm
  compile_eq := compile_of_compileModuleBudgetRec hcm
  maxBound_le := (compileModuleBudgetRec_bounds_le hcm).1
  total_ra_le := (compileModuleBudgetRec_bounds_le hcm).2.1
  exportBounds_le := (compileModuleBudgetRec_bounds_le hcm).2.2
  host := L.layoutOf (code ++ exits.map T.frame.label) (checkCompileBudgetRecLit_parts hchk).2.2.2
  prog_host := L.prog_layoutOf _ _
  labelsUnique := by
    have hp := checkCompileBudgetRecLit_parts hchk; intro i j l hi hj
    rw [L.prog_layoutOf _ hp.2.2.2] at hi hj
    exact compileModuleBudgetRec_labelsUnique hcl hcm hp.2.2.1
      (by simp only [List.all_append, Bool.and_eq_true]; exact ⟨hp.1, hp.2.1⟩) i j l hi hj

structure RecBudgetSubChunk (T : Target) (lt : LegalTarget) (recSigs : List SigEntry)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat) : Type 1 where
  bfs : List BudgetFn
  hints : List T.toIsa.Hints
  code : List T.Directive
  compileAux_eq :
    compileModuleBudgetRecAux T.toIsa lt T.frame.raBytes
      recSigs extCallees exits nX bfs hints = .ok code

@[expose] def recBudgetSubchunksBfs {T : Target} {lt : LegalTarget} {recSigs : List SigEntry}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    (scs : List (RecBudgetSubChunk T lt recSigs extCallees exits nX)) : List BudgetFn :=
  scs.foldr (fun sc acc => sc.bfs ++ acc) []
@[expose] def recBudgetSubchunksHints {T : Target} {lt : LegalTarget} {recSigs : List SigEntry}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    (scs : List (RecBudgetSubChunk T lt recSigs extCallees exits nX)) : List T.toIsa.Hints :=
  scs.foldr (fun sc acc => sc.hints ++ acc) []
@[expose] def recBudgetSubchunksCode {T : Target} {lt : LegalTarget} {recSigs : List SigEntry}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    (scs : List (RecBudgetSubChunk T lt recSigs extCallees exits nX)) : List T.Directive :=
  scs.foldr (fun sc acc => sc.code ++ acc) []

theorem compileModuleBudgetRecAux_append {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {bfs₁ bfs₂ : List BudgetFn} {hints₁ hints₂ : List I.Hints} {c₁ c₂ : List I.Directive}
    (h₁ : compileModuleBudgetRecAux I lt raBytes recSigs extCallees exits nX bfs₁ hints₁ = .ok c₁)
    (h₂ : compileModuleBudgetRecAux I lt raBytes recSigs extCallees exits nX bfs₂ hints₂ = .ok c₂) :
    compileModuleBudgetRecAux I lt raBytes recSigs extCallees exits nX
      (bfs₁ ++ bfs₂) (hints₁ ++ hints₂) = .ok (c₁ ++ c₂) := by
  rw [compileModuleBudgetRecAux_eq_loop] at h₁ h₂ ⊢
  exact compileSeqLoop_append (fun _ => rfl) (fun _ _ _ => rfl) h₁ h₂

theorem compileModuleBudgetRecAux_subchunks_eq {T : Target} {lt : LegalTarget}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat} :
    ∀ scs : List (RecBudgetSubChunk T lt recSigs extCallees exits nX),
      compileModuleBudgetRecAux T.toIsa lt T.frame.raBytes recSigs extCallees exits nX
        (recBudgetSubchunksBfs scs) (recBudgetSubchunksHints scs) = .ok (recBudgetSubchunksCode scs)
  | [] => rfl
  | sc :: scs => by
      dsimp only [recBudgetSubchunksBfs, recBudgetSubchunksHints, recBudgetSubchunksCode,
        List.foldr_cons]
      exact compileModuleBudgetRecAux_append sc.compileAux_eq
        (compileModuleBudgetRecAux_subchunks_eq scs)

@[expose] def checkRecBudgetSubchunks {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    (maxBound : Nat) (exportBounds : List (Sym × Nat))
    (scs : List (RecBudgetSubChunk T lt recSigs extCallees exits nX)) : Bool :=
  let bfs := recBudgetSubchunksBfs scs; let fnNames := bfs.map (fun b => b.toFn.name)
  sigListBeq recSigs (budgetRecSigsOf lt bfs) &&
  !(extCallees.any (fun p => fnNames.any (fun nm => nm == p.1.1))) &&
  Nat.ble maxBound (2 ^ 64) && Nat.ble (maxBound + T.frame.raBytes) (2 ^ 64) &&
  exportBounds.all (fun p => Nat.ble p.2 maxBound) &&
  checkHostNamesOk L exits fnNames (recBudgetSubchunksCode scs)

theorem linkBudgetRecSubchunks_cm {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    (maxBound : Nat) (exportBounds : List (Sym × Nat))
    (scs : List (RecBudgetSubChunk T lt recSigs extCallees exits nX))
    (h : checkRecBudgetSubchunks L maxBound exportBounds scs = true) :
    compileModuleBudgetRec T.toIsa lt T.frame.raBytes extCallees exits nX maxBound
      (recBudgetSubchunksBfs scs) (recBudgetSubchunksHints scs) exportBounds =
      .ok (recBudgetSubchunksCode scs) := by
  dsimp only [checkRecBudgetSubchunks] at h; simp only [Bool.and_eq_true] at h
  have haux := (congrArg (fun r => compileModuleBudgetRecAux T.toIsa lt T.frame.raBytes r
    extCallees exits nX (recBudgetSubchunksBfs scs) (recBudgetSubchunksHints scs))
    (sigListBeq_eq h.1.1.1.1.1)).symm.trans (compileModuleBudgetRecAux_subchunks_eq scs)
  dsimp only [budgetRecSigsOf] at haux; dsimp only [compileModuleBudgetRec]
  simp only [ext_disj_names_to_items (fun b : BudgetFn => b.toFn.name) h.1.1.1.1.2,
    Bool.false_eq_true, ↓reduceIte, h.1.1.1.2, h.1.1.2, h.1.2, Bool.and_self, Bool.not_true]
  exact haux

theorem linkBudgetRecSubchunks_chk {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    (maxBound : Nat) (exportBounds : List (Sym × Nat))
    (scs : List (RecBudgetSubChunk T lt recSigs extCallees exits nX))
    (h : checkRecBudgetSubchunks L maxBound exportBounds scs = true) :
    checkCompileBudgetRecLit T.frame.label L.progSmall (recBudgetSubchunksCode scs)
      ((recBudgetSubchunksBfs scs).map (fun b => b.toFn.name)) exits = true := by
  dsimp only [checkRecBudgetSubchunks, checkHostNamesOk] at h; simp only [Bool.and_eq_true] at h
  simp only [checkCompileBudgetRecLit, checkCompileBudgetRecResult, Bool.and_eq_true]; exact h.2

@[expose] def linkBudgetRecSubchunks {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    (hcl : Rega.LabelClean T.toIsa) {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} (maxBound : Nat) (exportBounds : List (Sym × Nat))
    (scs : List (RecBudgetSubChunk T lt recSigs extCallees exits nX))
    (h : checkRecBudgetSubchunks L maxBound exportBounds scs = true) :
    CompiledBudgetRec T lt extCallees exits nX (recBudgetSubchunksBfs scs)
      (recBudgetSubchunksHints scs) maxBound exportBounds :=
  compileCheckedBudgetRecLit T L lt hcl extCallees exits nX (recBudgetSubchunksBfs scs)
    (recBudgetSubchunksHints scs) maxBound exportBounds (recBudgetSubchunksCode scs)
    (linkBudgetRecSubchunks_cm L maxBound exportBounds scs h)
    (linkBudgetRecSubchunks_chk L maxBound exportBounds scs h)

private theorem wp_evalMono :
    BudgetFn.EvalMono (fun Γcall _ bfn => Func.wp Γcall bfn.toFn.body) :=
  fun bfn _ _ _ _ hC _ xs m _ _ hwp => wp_env_mono hC (bfn.toFn.body Val Cont xs) m hwp

private theorem legalEnv_budgetCallSlot_ext {BM : BudgetModule} {lt : LegalTarget}
    {bfn : BudgetFn} {Γext : BudgetEnv} {G : BudgetEnv} {sb : Nat}
    {g : Sym} (hg : g ∉ BM.fns.map (fun b => b.toFn.name))
    {as bs : List Ty} {xs' : Tup Val as} {m0 : Mem 64} {Q' : Post bs} {X' : XPost}
    (h : legalEnv lt (BudgetEnv.callSlot BM bfn Γext G sb) g as bs xs' m0 Q' X') :
    legalEnv lt (Env.restrict (Γext (sb - bfn.maxFrame)) BM.extSigs) g as bs xs' m0 Q' X' := by
  rcases h with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hstep⟩
  rcases hstep with ⟨hsig, _⟩ | ⟨hsig, hΓ⟩
  · obtain ⟨b, hb, hbeq⟩ := List.mem_map.mp hsig
    have hnm : b.toFn.name = g := congrArg Prod.fst hbeq
    exact absurd (hnm ▸ List.mem_map_of_mem hb) hg
  · exact ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hsig, hΓ⟩

/-- **Single-shot `BudgetEnv.lfp` SCC linking theorem (`link_scc_budget_lfp`).** -/
theorem link_scc_budget_lfp {T : Target} {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {bfs : List BudgetFn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    {exportBounds : List (Sym × Nat)}
    (M : CompiledBudgetRec T lt extCallees exits nX bfs hints maxBound exportBounds)
    (BM : BudgetModule) (hbfs : BM.fns = bfs) (h : T.mach.Host) (Γext : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hcyc : checkCyclic BM.toModule = true) (hwf : ∀ bfn ∈ BM.fns, bfn.toFn.Wf)
    (hsupp : ∀ bfn ∈ BM.fns, (bfn.toFn.earlyOpt).body.supportsSource lt = true)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec h p.1.1 (legalEnv lt (Env.restrict Γext BM.extSigs) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : ∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2)
    (hexits : ∀ g ∈ exits, T.Defined h g) :
    ∀ sb, sb + T.frame.raBytes ≤ 2 ^ 64 → ∀ bfn ∈ BM.fns,
      T.Defined h bfn.toFn.name ∧ T.FnSpec h bfn.toFn.name
        (legalEnv lt (Env.onlyFn bfn.toFn (BudgetEnv.semScc BM Γext sb))
          bfn.toFn.name (lt.legalSig bfn.toFn.as) (lt.legalSig bfn.toFn.rs)) sb nX := by
  have hnd := Module.namesNodup_of_checkNamesNodup ((Bool.and_eq_true _ _).mp hcyc).1
  obtain ⟨hdisj, haux⟩ := compileModuleBudgetRec_disjoint
    (show compileModuleBudgetRec T.toIsa lt T.frame.raBytes extCallees exits nX maxBound
      BM.fns hints exportBounds = .ok M.code from hbfs ▸ M.compileModuleBudgetRec_eq)
  let cap := 2 ^ 64 - T.frame.raBytes
  let G : BudgetEnv := fun sb => pullEnv lt (machEnv T h sb nX)
  have hpre : ∀ sb, sb ≤ cap → Env.le (BudgetEnv.sccOp BM Γext G sb) (G sb) := by
    intro sb hsb_cap f as bs xs m P E hΦ
    rcases hΦ with ⟨bfn, hbfn, rfl, rfl, rfl, hmax, hmin, hwp⟩
    obtain ⟨hint, c, k_f, hl, hinf, hklen, hchk⟩ := compileModuleBudgetRecAux_mem haux bfn hbfn
    obtain ⟨hfr_max, hcal_b, hex_b⟩ := checkAndBoundBudgetRecExt_spec hchk
    let bound : Sym → Nat := fun g =>
      if (BM.fns.map (fun b => b.toFn.name)).contains g then sb - bfn.maxFrame
      else match extCallees.find? (fun q => q.1.1 == g) with | some q => q.2 | none => 0
    have hcal : ∀ g as' bs', (g, as', bs') ∈ (bfn.toFn.mid lt).ext.callees →
        T.FnSpec h g (legalEnv lt (BudgetEnv.callSlot BM bfn (BudgetEnv.const Γext) G sb) g as' bs')
          (bound g) nX ∧
        Rega.effFrame T.toIsa hint (bfn.toFn.mid lt).ext + T.frame.raBytes + bound g ≤ sb := by
      intro g as' bs' hg
      rcases hcal_b (g, as', bs') hg with hrec_sig | ⟨_, bg, hlk, _⟩
      · obtain ⟨gbfn, hgbfn, hgeq⟩ := List.mem_map.mp hrec_sig
        rcases Prod.mk.inj hgeq with ⟨rfl, hsig_ab⟩; rcases Prod.mk.inj hsig_ab with ⟨rfl, rfl⟩
        have hcon : (BM.fns.map (fun b => b.toFn.name)).contains gbfn.toFn.name = true := by
          simpa using List.mem_map_of_mem hgbfn
        dsimp only [bound]; simp only [hcon, ↓reduceIte]
        have hstep_eq : BudgetEnv.callSlot BM bfn (BudgetEnv.const Γext) G sb =
            Env.sccStep BM.toModule (G (sb - bfn.maxFrame)) Γext := by
          funext _ _ _ _ _ _ _
          simp [BudgetEnv.callSlot, BudgetEnv.sccStep, Env.sccStep, BudgetModule.fnSigs,
            BudgetModule.extSigs, BudgetModule.toModule, List.map_map, Function.comp_def,
            ParamEnv.const]
        exact ⟨hstep_eq ▸ recCallee_sccStep_fnSpec hnd (List.mem_map_of_mem hgbfn) (Env.le_refl _),
          by omega⟩
      · exact link_scc_extCallee_step hext hext_uniq hdisj
          (fun g hnot _ _ _ _ _ _ hleg => (legalEnv_budgetCallSlot_ext
            (Γext := BudgetEnv.const Γext) hnot hleg :
              legalEnv lt (Env.restrict Γext BM.extSigs) _ _ _ _ _ _ _))
          hlk (by omega) (sb - bfn.maxFrame)
    exact compileFn_body_correct T h lt hint (bfn.toFn.mid lt).ext bfn.toFn
      (BudgetEnv.callSlot BM bfn (BudgetEnv.const Γext) G sb) sb nX bound
      (hwf bfn hbfn) (hsupp bfn hbfn) hl (list_isInfixAt_trans hklen hinf hc) hu (by omega)
      (by dsimp only [cap] at hsb_cap; omega) hcal
      (fun g hg => ⟨hexits g (hex_b g hg).1, Nat.le_trans (hex_b g hg).2 hmin⟩) xs m P E hwp
  have hlfp := BudgetEnv.lfp_le_of_prefix_below
    (BudgetEnv.mkSccOp_budgetLocal BM (BudgetEnv.const Γext) wp_evalMono) cap G hpre
  intro sb hsb bfn hbfn
  have hsb_cap : sb ≤ cap := by dsimp only [cap]; omega
  obtain ⟨hint, c, k_f, hl, hinf, hklen, _⟩ := compileModuleBudgetRecAux_mem haux bfn hbfn
  exact ⟨defined_of_lowerFn' (f := bfn.toFn.mid lt) hl (list_isInfixAt_trans hklen hinf hc),
    link_scc_extract_fnSpec fun xs₀ m P₀ E₀ hsem =>
      hlfp sb hsb_cap bfn.toFn.name bfn.toFn.as bfn.toFn.rs xs₀ m P₀ E₀ hsem⟩

theorem link_scc_budget_lfp_host {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat}
    {bfs : List BudgetFn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    {exportBounds : List (Sym × Nat)}
    (M : CompiledBudgetRec T lt [] exits nX bfs hints maxBound exportBounds)
    (BM : BudgetModule) (hbfs : BM.fns = bfs) (Γext : Env)
    (hcyc : checkCyclic BM.toModule = true) (hwf : ∀ bfn ∈ BM.fns, bfn.toFn.Wf)
    (hsupp : ∀ bfn ∈ BM.fns, (bfn.toFn.earlyOpt).body.supportsSource lt = true) :
    ∀ sb, sb + T.frame.raBytes ≤ 2 ^ 64 → ∀ bfn ∈ BM.fns,
      T.Defined M.host bfn.toFn.name ∧ T.FnSpec M.host bfn.toFn.name
        (legalEnv lt (Env.onlyFn bfn.toFn (BudgetEnv.semScc BM Γext sb))
          bfn.toFn.name (lt.legalSig bfn.toFn.as) (lt.legalSig bfn.toFn.rs)) sb nX :=
  link_scc_budget_lfp M BM hbfs M.host Γext 0 M.code_infix_host M.labelsUnique hcyc hwf hsupp
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ hg => M.defined_exit_host hg)

/-! ## 3. Mixed Acyclic + Cyclic Budget-SCC `Chunk` Linking -/

inductive Chunk (T : Target) (lt : LegalTarget) (exits : List Sym) (nX : Nat) : Type 1 where
  | acyc (c : CompiledChunk T lt exits nX) : Chunk T lt exits nX
  | recBudgetSCC (extCallees : List (SigEntry × Nat)) (bfs : List BudgetFn)
      (hints : List T.toIsa.Hints) (maxBound : Nat) (exportBounds : List (Sym × Nat))
      (compiled : CompiledBudgetRec T lt extCallees exits nX bfs hints maxBound exportBounds) :
      Chunk T lt exits nX

namespace Chunk

variable {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}

@[expose] def ofBudgetRecSubchunks (L : TargetLayout T) (hcl : Rega.LabelClean T.toIsa)
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} (maxBound : Nat)
    (exportBounds : List (Sym × Nat))
    (scs : List (RecBudgetSubChunk T lt recSigs extCallees exits nX))
    (h : checkRecBudgetSubchunks L maxBound exportBounds scs = true) : Chunk T lt exits nX :=
  .recBudgetSCC extCallees (recBudgetSubchunksBfs scs) (recBudgetSubchunksHints scs)
    maxBound exportBounds (linkBudgetRecSubchunks L hcl maxBound exportBounds scs h)

@[expose] def fns (c : Chunk T lt exits nX) : List Fn :=
  Chunk.casesOn c (·.fs) (fun _ bfs _ _ _ _ => bfs.map BudgetFn.toFn)
@[expose] def hints (c : Chunk T lt exits nX) : List T.toIsa.Hints :=
  Chunk.casesOn c (·.hints) (fun _ _ h _ _ _ => h)
@[expose] def code (c : Chunk T lt exits nX) : List T.Directive :=
  Chunk.casesOn c (·.compiled.code) (fun _ _ _ _ _ m => m.code)
@[expose] def maxBound (c : Chunk T lt exits nX) : Nat :=
  Chunk.casesOn c (·.maxBound) (fun _ _ _ mb _ _ => mb)
@[expose] def extCallees (c : Chunk T lt exits nX) : List (SigEntry × Nat) :=
  Chunk.casesOn c (·.extCallees) (fun ext _ _ _ _ _ => ext)
@[expose] def sigBounds (c : Chunk T lt exits nX) : List (SigEntry × Nat) :=
  Chunk.casesOn c (·.compiled.sigBounds) (fun _ _ _ _ _ m => m.sigBounds)
@[expose] def bound (c : Chunk T lt exits nX) (nm : Sym) : Nat :=
  Chunk.casesOn c (fun m => m.compiled.bound nm) (fun _ _ _ _ _ m => m.bound nm)
theorem compile_eq (c : Chunk T lt exits nX) : compile T.toIsa lt c.fns c.hints = .ok c.code := by
  cases c with
  | acyc cc => exact cc.compiled.compile_eq
  | recBudgetSCC _ _ _ _ _ cbr => exact cbr.compile_eq

end Chunk

@[expose] def sccChunksFns {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    List (Chunk T lt exits nX) → List Fn
  | [] => [] | c :: cs => c.fns ++ sccChunksFns cs
@[expose] def sccChunksHints {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    List (Chunk T lt exits nX) → List T.toIsa.Hints
  | [] => [] | c :: cs => c.hints ++ sccChunksHints cs
@[expose] def sccChunksCode {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    List (Chunk T lt exits nX) → List T.Directive
  | [] => [] | c :: cs => c.code ++ sccChunksCode cs
@[expose] def sccChunksMaxBound {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    List (Chunk T lt exits nX) → Nat
  | [] => 0 | c :: cs => Nat.max c.maxBound (sccChunksMaxBound cs)

theorem sccChunksFns_append {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (cs₁ cs₂ : List (Chunk T lt exits nX)),
      sccChunksFns (cs₁ ++ cs₂) = sccChunksFns cs₁ ++ sccChunksFns cs₂
  | [], _ => rfl
  | _ :: cs₁, cs₂ => by
      simp only [List.cons_append, sccChunksFns, sccChunksFns_append cs₁ cs₂, List.append_assoc]

theorem sccChunksCode_append {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (cs₁ cs₂ : List (Chunk T lt exits nX)),
      sccChunksCode (cs₁ ++ cs₂) = sccChunksCode cs₁ ++ sccChunksCode cs₂
  | [], _ => rfl
  | _ :: cs₁, cs₂ => by
      simp only [List.cons_append, sccChunksCode, sccChunksCode_append cs₁ cs₂, List.append_assoc]

theorem sccChunksMaxBound_nil {T : Target} {lt : LegalTarget} {exits : List Sym} {nX B : Nat} :
    sccChunksMaxBound ([] : List (Chunk T lt exits nX)) ≤ B := Nat.zero_le B

theorem sccChunksMaxBound_cons {T : Target} {lt : LegalTarget} {exits : List Sym} {nX B : Nat}
    {c : Chunk T lt exits nX} {cs : List (Chunk T lt exits nX)}
    (hc : c.maxBound ≤ B) (hcs : sccChunksMaxBound cs ≤ B) :
    sccChunksMaxBound (c :: cs) ≤ B := Nat.max_le.mpr ⟨hc, hcs⟩

theorem sccChunksMaxBound_append {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (cs₁ cs₂ : List (Chunk T lt exits nX)),
      sccChunksMaxBound (cs₁ ++ cs₂) = Nat.max (sccChunksMaxBound cs₁) (sccChunksMaxBound cs₂)
  | [], cs₂ => by simp [sccChunksMaxBound]
  | _ :: cs₁, cs₂ => by
      simp only [List.cons_append, sccChunksMaxBound, sccChunksMaxBound_append cs₁ cs₂,
        Nat.max_assoc]

@[expose] def checkSccChunksExt {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (acc : List (SigEntry × Nat)) : List (Chunk T lt exits nX) → Bool
  | [] => true
  | c :: cs => checkExtCompat acc c.extCallees && checkSccChunksExt (c.sigBounds.reverse ++ acc) cs

@[expose] def checkLinkSccList {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} (ext₀ : List (SigEntry × Nat))
    (chunks : List (Chunk T lt exits nX)) : Bool :=
  let fnNames := (sccChunksFns chunks).map Fn.name
  checkSccChunksExt ext₀ chunks && !(ext₀.any (fun p => fnNames.any (fun nm => nm == p.1.1))) &&
  checkHostNamesOk L exits fnNames (sccChunksCode chunks)

@[expose] def externsOfSigs (sigs : List SigEntry) : List Extern :=
  sigs.map fun s => ⟨s.1, s.2.1, s.2.2⟩
theorem externsOfSigs_map_sig (sigs : List SigEntry) :
    (externsOfSigs sigs).map Extern.sig = sigs := by
  induction sigs with
  | nil => rfl
  | cons s _ ih => rcases s with ⟨nm, as, bs⟩; simpa [externsOfSigs, Extern.sig] using ih
@[expose] def Chunk.callsOk {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (extSigs : List SigEntry) (c : Chunk T lt exits nX) : Bool :=
  Chunk.casesOn c
    (fun m => Module.checkAcyclic ⟨m.fs, externsOfSigs extSigs, exits⟩)
    (fun _ bfs _ _ _ _ => LinkRec.checkCyclic ⟨bfs.map BudgetFn.toFn, externsOfSigs extSigs, exits⟩)
@[expose] def checkChunksCalls {T : Target} {lt : LegalTarget} {nX : Nat} (exits : List Sym) :
    List SigEntry → List (Chunk T lt exits nX) → Bool
  | _, [] => true
  | extSigs, c :: rest =>
      c.callsOk extSigs && checkChunksCalls exits (c.fns.map Fn.sig ++ extSigs) rest

theorem checkLinkSccList_parts {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} {ext₀ : List (SigEntry × Nat)}
    {chunks : List (Chunk T lt exits nX)}
    (h : checkLinkSccList L ext₀ chunks = true) :
    checkSccChunksExt ext₀ chunks = true ∧
      (∀ p ∈ ext₀, p.1.1 ∉ (sccChunksFns chunks).map Fn.name) ∧
      ((sccChunksFns chunks).map Fn.name).all fnNameOk = true ∧ exits.all fnNameOk = true ∧
      ((sccChunksFns chunks).map Fn.name ++ exits).Nodup ∧
      L.progSmall (sccChunksCode chunks ++ exits.map T.frame.label) = true := by
  dsimp only [checkLinkSccList, checkHostNamesOk] at h; simp only [Bool.and_eq_true] at h
  refine ⟨h.1.1, fun p hp hmem => ?_, h.2.1.1.1, h.2.1.1.2, stringsNodup_nodup h.2.1.2, h.2.2⟩
  have hfalse := bool_not_eq_false h.1.2
  have hany : ext₀.any (fun p => ((sccChunksFns chunks).map Fn.name).any
      (fun nm => nm == p.1.1)) = true :=
    List.any_eq_true.mpr ⟨p, hp, List.any_eq_true.mpr ⟨p.1.1, hmem, beq_iff_eq.mpr rfl⟩⟩
  rw [hany] at hfalse; cases hfalse

@[expose] def sccHost {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} (ext₀ : List (SigEntry × Nat))
    (chunks : List (Chunk T lt exits nX))
    (h : checkLinkSccList L ext₀ chunks = true) : T.mach.Host :=
  L.layoutOf (sccChunksCode chunks ++ exits.map T.frame.label) (checkLinkSccList_parts h).2.2.2.2.2
theorem sccProg_host {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} (ext₀ : List (SigEntry × Nat))
    (chunks : List (Chunk T lt exits nX)) (h : checkLinkSccList L ext₀ chunks = true) :
    T.mach.prog (sccHost L ext₀ chunks h) = sccChunksCode chunks ++ exits.map T.frame.label :=
  L.prog_layoutOf _ _
theorem sccCode_infix_host {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} (ext₀ : List (SigEntry × Nat))
    (chunks : List (Chunk T lt exits nX)) (h : checkLinkSccList L ext₀ chunks = true) :
    (sccChunksCode chunks).IsInfixAt (T.mach.prog (sccHost L ext₀ chunks h)) 0 := by
  rw [sccProg_host]; exact ⟨exits.map T.frame.label, rfl⟩
theorem sccDefined_exit_host {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} (ext₀ : List (SigEntry × Nat))
    (chunks : List (Chunk T lt exits nX)) (h : checkLinkSccList L ext₀ chunks = true)
    {g : Sym} (hg : g ∈ exits) : T.Defined (sccHost L ext₀ chunks h) g := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
  refine ⟨(sccChunksCode chunks).length + i, ?_⟩
  rw [sccProg_host, List.getElem?_append_right (by omega), List.getElem?_map]; simp [hi]

private theorem sccChunks_code_labels {T : Target} (hcl : Rega.LabelClean T.toIsa)
    {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (chunks : List (Chunk T lt exits nX)),
      ((sccChunksFns chunks).map Fn.name).Nodup →
      (sccChunksFns chunks).all (fun f => fnNameOk f.name) = true →
      (∀ (i : Nat) (l : Sym), (sccChunksCode chunks)[i]? = some (T.frame.label l) →
        ∃ f ∈ sccChunksFns chunks, l = f.name ∨ ∃ a, l = Rega.lname f.name a) ∧
      (∀ (i j : Nat) (l : Sym), (sccChunksCode chunks)[i]? = some (T.frame.label l) →
        (sccChunksCode chunks)[j]? = some (T.frame.label l) → i = j)
  | [], _, _ => ⟨fun _ _ hi => by simp [sccChunksCode] at hi,
      fun _ _ _ hi => by simp [sccChunksCode] at hi⟩
  | c :: cs, hnd, hok => by
      dsimp only [sccChunksFns] at hnd hok
      simp only [List.map_append, List.all_append, Bool.and_eq_true] at hnd hok
      have hnd_s := List.nodup_append.mp hnd
      obtain ⟨hc_mem, hc_uniq⟩ := compile_code_labels hcl lt c.compile_eq hnd_s.1 hok.1
      obtain ⟨ih_mem, ih_uniq⟩ := sccChunks_code_labels hcl cs hnd_s.2.1 hok.2
      have hdisj : ∀ {i₁ j₁ : Nat} {l : Sym}, c.code[i₁]? = some (T.frame.label l) →
          (sccChunksCode cs)[j₁]? = some (T.frame.label l) → False := by
        intro i₁ j₁ l hi₁ hj₁
        obtain ⟨f₁, hf₁, h₁⟩ := hc_mem i₁ l hi₁; obtain ⟨f₂, hf₂, h₂⟩ := ih_mem j₁ l hj₁
        have hok₁ := List.all_eq_true.mp hok.1 f₁ hf₁; have hok₂ := List.all_eq_true.mp hok.2 f₂ hf₂
        rcases h₁ with rfl | ⟨a, rfl⟩ <;> rcases h₂ with hnm | ⟨b, hnm⟩
        · exact hnd_s.2.2 f₁.name (List.mem_map_of_mem hf₁) f₂.name (List.mem_map_of_mem hf₂) hnm
        · exact lname_ne_cross hok₁ hnm.symm
        · exact lname_ne_cross hok₂ hnm
        · exact hnd_s.2.2 f₁.name (List.mem_map_of_mem hf₁) f₂.name
            (List.mem_map_of_mem hf₂) (lname_inj_cross hok₁ hok₂ hnm).1
      constructor
      · intro i l hi; dsimp only [sccChunksCode, sccChunksFns] at hi ⊢
        by_cases hlt : i < c.code.length
        · rw [List.getElem?_append_left hlt] at hi
          obtain ⟨f, hf, hl⟩ := hc_mem i l hi; exact ⟨f, List.mem_append_left _ hf, hl⟩
        · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hi
          obtain ⟨f, hf, hl⟩ := ih_mem (i - c.code.length) l hi
          exact ⟨f, List.mem_append_right _ hf, hl⟩
      · intro i j l hi hj; dsimp only [sccChunksCode] at hi hj
        by_cases hic : i < c.code.length <;> by_cases hjc : j < c.code.length
        · rw [List.getElem?_append_left hic] at hi; rw [List.getElem?_append_left hjc] at hj
          exact hc_uniq i j l hi hj
        · rw [List.getElem?_append_left hic] at hi
          rw [List.getElem?_append_right (Nat.le_of_not_lt hjc)] at hj
          exact absurd hi (fun h' => hdisj h' hj)
        · rw [List.getElem?_append_right (Nat.le_of_not_lt hic)] at hi
          rw [List.getElem?_append_left hjc] at hj; exact absurd hj (fun h' => hdisj h' hi)
        · rw [List.getElem?_append_right (Nat.le_of_not_lt hic)] at hi
          rw [List.getElem?_append_right (Nat.le_of_not_lt hjc)] at hj
          have heq := ih_uniq (i - c.code.length) (j - c.code.length) l hi hj; omega

theorem sccLabelsUnique {T : Target} (L : TargetLayout T) (hcl : Rega.LabelClean T.toIsa)
    {lt : LegalTarget} {exits : List Sym} {nX : Nat} (ext₀ : List (SigEntry × Nat))
    (chunks : List (Chunk T lt exits nX)) (h : checkLinkSccList L ext₀ chunks = true) :
    T.LabelsUnique (sccHost L ext₀ chunks h) := by
  have hp := checkLinkSccList_parts h
  have hnd_s := List.nodup_append.mp hp.2.2.2.2.1
  have hok_fns : (sccChunksFns chunks).all (fun f => fnNameOk f.name) = true := by
    simpa [List.all_map, Function.comp_def] using hp.2.2.1
  obtain ⟨hmem, huniq⟩ := sccChunks_code_labels hcl chunks hnd_s.1 hok_fns
  have hok_all : ((sccChunksFns chunks).map Fn.name ++ exits).all fnNameOk = true := by
    simp only [List.all_append, Bool.and_eq_true]; exact ⟨hp.2.2.1, hp.2.2.2.1⟩
  intro i j l hi hj; rw [sccProg_host] at hi hj
  exact append_exits_labelsUnique hcl hmem huniq hp.2.2.2.2.1 hok_all i j l hi hj

@[expose] def sccBound {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    List (Chunk T lt exits nX) → Sym → Nat
  | [], _ => 0
  | c :: cs, nm => if (c.fns.map Fn.name).contains nm then c.bound nm else sccBound cs nm

theorem sccBound_le_max {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (chunks : List (Chunk T lt exits nX)) (nm : Sym),
      sccBound chunks nm ≤ sccChunksMaxBound chunks
  | [], _ => Nat.le_refl 0
  | c :: cs, nm => by
      dsimp only [sccBound, sccChunksMaxBound]; split
      · refine Nat.le_trans ?_ (Nat.le_max_left _ _)
        cases c with
        | acyc m => exact m.compiled.bound_le_max nm
        | recBudgetSCC _ _ _ _ _ m => exact m.bound_le_max nm
      · exact Nat.le_trans (sccBound_le_max cs nm) (Nat.le_max_right _ _)

private theorem mem_sccChunksFns_of_mem_chunk {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} {c : Chunk T lt exits nX} :
    ∀ {cs : List (Chunk T lt exits nX)}, c ∈ cs → ∀ {g : Fn}, g ∈ c.fns → g ∈ sccChunksFns cs
  | [], hc, _, _ => nomatch hc
  | _ :: _, hc, _, hg => by
      rcases List.mem_cons.mp hc with rfl | hds
      · exact List.mem_append_left _ hg
      · exact List.mem_append_right _ (mem_sccChunksFns_of_mem_chunk hds hg)

theorem sccBound_eq_chunk {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (chunks : List (Chunk T lt exits nX)), ((sccChunksFns chunks).map Fn.name).Nodup →
      ∀ c ∈ chunks, ∀ {nm : Sym}, nm ∈ c.fns.map Fn.name → sccBound chunks nm = c.bound nm
  | [], _, _, hc, _, _ => nomatch hc
  | c₀ :: cs, hnd, c, hc, nm, hnm => by
      dsimp only [sccChunksFns] at hnd; simp only [List.map_append] at hnd
      have hnd_s := List.nodup_append.mp hnd
      rcases List.mem_cons.mp hc with rfl | hcs
      · have hcon : (c.fns.map Fn.name).contains nm = true := by
          simpa [List.contains_eq_mem] using hnm
        dsimp only [sccBound]; simp only [hcon, ↓reduceIte]
      · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hnm
        have hnot0 : f.name ∉ c₀.fns.map Fn.name := fun h0 => hnd_s.2.2 f.name h0 f.name
          (List.mem_map_of_mem (mem_sccChunksFns_of_mem_chunk hcs hf)) rfl
        have hcon : (c₀.fns.map Fn.name).contains f.name = false := by
          simpa [List.contains_eq_mem] using hnot0
        dsimp only [sccBound]; simp only [hcon, Bool.false_eq_true, ↓reduceIte]
        exact sccBound_eq_chunk cs hnd_s.2.1 c hcs (List.mem_map_of_mem hf)

/-! ## 4. Closed Canonical `semChunks` Environment and `linkChunks_fnSpec` -/

@[expose] def Chunk.sem {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (extSigs : List SigEntry) : Chunk T lt exits nX → Env → Env
  | .acyc c, Γprev =>
      let M : Module := ⟨c.fs, externsOfSigs extSigs, exits⟩
      Env.sccStep M (Env.semScc M Γprev) Γprev
  | .recBudgetSCC _ bfs _ maxB exportBounds _, Γprev =>
      let BM : BudgetModule := ⟨bfs, externsOfSigs extSigs, exits⟩
      BudgetEnv.sccStep BM (fun f as bs xs m Q X =>
        BudgetEnv.semScc BM Γprev (budgetBound exportBounds maxB f) f as bs xs m Q X) Γprev

@[expose] def semChunks {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (extSigs : List SigEntry) (Γ₀ : Env) : List (Chunk T lt exits nX) → Env
  | [] => Γ₀ | c :: cs => semChunks (c.fns.map Fn.sig ++ extSigs) (c.sem extSigs Γ₀) cs

theorem Chunk.sem_intro_ext {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (c : Chunk T lt exits nX) {extSigs : List SigEntry} {Γ₀ : Env}
    {f : Sym} {as bs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (hmem : (f, as, bs) ∈ extSigs) (hΓ : Γ₀ f as bs xs m Q X) :
    c.sem extSigs Γ₀ f as bs xs m Q X := by
  cases c <;>
    simp [Chunk.sem, Env.sccStep, BudgetEnv.sccStep, BudgetModule.extSigs, externsOfSigs_map_sig]
  all_goals exact Or.inr ⟨hmem, hΓ⟩

theorem Chunk.sem_elim {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (c : Chunk T lt exits nX) {extSigs : List SigEntry} {Γ₀ : Env}
    {f : Sym} {as bs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : c.sem extSigs Γ₀ f as bs xs m Q X) :
    (f, as, bs) ∈ c.fns.map Fn.sig ∨ ((f, as, bs) ∈ extSigs ∧ Γ₀ f as bs xs m Q X) := by
  cases c with
  | acyc _ =>
      dsimp only [Chunk.sem, Env.sccStep] at h; rw [externsOfSigs_map_sig] at h
      rcases h with ⟨h1, _⟩ | ⟨h2, hΓ⟩; exact Or.inl h1; exact Or.inr ⟨h2, hΓ⟩
  | recBudgetSCC _ _ _ _ _ _ =>
      dsimp only [Chunk.sem, BudgetEnv.sccStep, BudgetModule.fnSigs, BudgetModule.extSigs] at h
      rw [externsOfSigs_map_sig] at h
      rcases h with ⟨h1, _⟩ | ⟨h2, hΓ⟩
      · exact Or.inl (by dsimp only [Chunk.fns]; rw [List.map_map]; exact h1)
      · exact Or.inr ⟨h2, hΓ⟩

theorem Chunk.sem_iff_of_not_mem {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (c : Chunk T lt exits nX) {extSigs : List SigEntry} {Γ₀ : Env}
    {f : Sym} {as bs : List Ty} (hnot : f ∉ c.fns.map Fn.name) (hmem : (f, as, bs) ∈ extSigs)
    (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost) :
    c.sem extSigs Γ₀ f as bs xs m Q X ↔ Γ₀ f as bs xs m Q X :=
  ⟨fun h => (c.sem_elim h).elim
    (fun hs => by
      obtain ⟨g, hg, he⟩ := List.mem_map.mp hs
      have hnm : g.name = f := congrArg Prod.fst he
      exact absurd (hnm ▸ List.mem_map_of_mem hg) hnot) And.right, c.sem_intro_ext hmem⟩

theorem Chunk.mem_sigBounds {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (c : Chunk T lt exits nX) {p : SigEntry × Nat} (hp : p ∈ c.sigBounds) :
    ∃ g ∈ c.fns, p = ((g.name, lt.legalSig g.as, lt.legalSig g.rs), c.bound g.name) := by
  cases c <;> simp only [Chunk.sigBounds, Compiled.sigBounds,
    CompiledBudgetRec.sigBounds, sigBoundsBudgetRecOf, List.mem_map] at hp
  · obtain ⟨g, hg, rfl⟩ := hp; exact ⟨g, hg, rfl⟩
  · obtain ⟨b, hb, rfl⟩ := hp; exact ⟨b.toFn, List.mem_map_of_mem hb, rfl⟩

private theorem sccChunks_fn_not_mem_rest {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} {c : Chunk T lt exits nX} {cs : List (Chunk T lt exits nX)}
    {f : Fn} (hf : f ∈ c.fns) (hnd : ((c.fns ++ sccChunksFns cs).map Fn.name).Nodup) :
    f.name ∉ (sccChunksFns cs).map Fn.name := by
  simp only [List.map_append] at hnd
  exact fun hm => (List.nodup_append.mp hnd).2.2 f.name (List.mem_map_of_mem hf) f.name hm rfl

theorem semChunks_agree_earlier {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} :
    ∀ (cs : List (Chunk T lt exits nX)) (extSigs : List SigEntry) (Γ₀ : Env)
      {f : Fn}, f.name ∉ (sccChunksFns cs).map Fn.name → f.sig ∈ extSigs →
      ∀ xs m Q X, semChunks extSigs Γ₀ cs f.name f.as f.rs xs m Q X ↔ Γ₀ f.name f.as f.rs xs m Q X
  | [], _, _, _, _, _, _, _, _, _ => Iff.rfl
  | c :: cs, extSigs, Γ₀, f, hnot, hmem, xs, m, Q, X => by
      dsimp only [sccChunksFns] at hnot
      simp only [List.map_append, List.mem_append, not_or] at hnot
      dsimp only [semChunks]
      rw [semChunks_agree_earlier cs (c.fns.map Fn.sig ++ extSigs) (c.sem extSigs Γ₀)
        hnot.2 (List.mem_append_right _ hmem) xs m Q X]
      exact c.sem_iff_of_not_mem hnot.1 hmem xs m Q X

private theorem chunk_step_wp {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (h : T.mach.Host) (c : Chunk T lt exits nX) (k₀ : Nat) (acc : List (SigEntry × Nat))
    (extSigs : List SigEntry) (Γcur : Env) (hinf_c : c.code.IsInfixAt (T.mach.prog h) k₀)
    (hu : T.LabelsUnique h)
    (hcompat : ∀ g bg, lookupBound c.extCallees g = some bg → lookupBound acc g = some bg)
    (hcalls_c : c.callsOk extSigs = true) (hnd_fns : (c.fns.map Fn.name).Nodup)
    (hnd_ext : (extSigs.map Prod.fst).Nodup)
    (hdisj_fns_ext : ∀ a ∈ c.fns.map Fn.name, ∀ b ∈ extSigs.map Prod.fst, a ≠ b)
    (hwf : ∀ g ∈ c.fns, g.Wf) (hsupp : ∀ g ∈ c.fns, (g.earlyOpt).body.supportsSource lt = true)
    (hacc : ∀ p ∈ acc,
      T.FnSpec h p.1.1 (legalEnv lt (Env.restrict Γcur extSigs) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hacc_uniq : ∀ p ∈ acc, ∀ q ∈ acc, p.1.1 = q.1.1 → p.2 = q.2)
    (hdisj_c_ext : ∀ p ∈ acc, p.1.1 ∉ c.fns.map Fn.name)
    (hexits : ∀ g ∈ exits, T.Defined h g) :
    ∀ g ∈ c.fns, T.Defined h g.name ∧ T.FnSpec h g.name
      (legalEnv lt (Env.onlyFn g (c.sem extSigs Γcur)) g.name (lt.legalSig g.as) (lt.legalSig g.rs))
      (c.bound g.name) nX := by
  cases c with
  | acyc cc =>
      let M : Module := ⟨cc.fs, externsOfSigs extSigs, exits⟩
      let Γnext : Env := Env.sccStep M (Env.semScc M Γcur) Γcur
      have hMnd : M.namesNodup := by
        rw [Module.namesNodup, Module.names,
          show M.externs.map Extern.name = extSigs.map Prod.fst by
            simp [M, externsOfSigs, List.map_map, Function.comp_def]]
        exact List.nodup_append.mpr ⟨hnd_fns, hnd_ext, hdisj_fns_ext⟩
      have hcm_acc := compileModule_mono_lookupBound hcompat cc.compiled.compileModule_eq
      have hwp_step : ∀ g ∈ M.fns, ∀ xs m Q X,
          Γnext g.name g.as g.rs xs m Q X → Func.wp Γnext g.body xs m Q X := by
        intro g hg xs m Q X hΓ; rcases hΓ with ⟨_, hg_sem⟩ | ⟨hex_mem, _⟩
        · rcases Env.lfp_post (sccOp_mono M Γcur) g.name g.as g.rs xs m Q X hg_sem with
            ⟨_, fn, hfn, hnm, ha, hr, hwp⟩
          obtain rfl := fn_eq_of_mem_fns hnd_fns hfn hg hnm; exact hwp
        · exact absurd hex_mem (fn_name_not_mem_externs_mod hMnd hg)
      have hext_M : ∀ p ∈ acc,
          T.FnSpec h p.1.1 (legalEnv lt (Env.ofModule M Γnext) p.1.1 p.1.2.1 p.1.2.2) p.2 nX := by
        intro p hp; refine Target.FnSpec.of_spec T (hacc p hp) fun args m0 Q X hleg => ?_
        rcases hleg with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hsig, hΓ⟩
        have hnot_fnsig : (p.1.1, as₀, bs₀) ∉ M.fns.map Fn.sig := fun hm => by
          obtain ⟨fn, hfn, heq⟩ := List.mem_map.mp hm
          exact hdisj_c_ext p hp ((congrArg Prod.fst heq) ▸ List.mem_map_of_mem hfn)
        rcases List.mem_append.mp hsig with hm_fn | hm_ex
        · exact absurd hm_fn hnot_fnsig
        · rw [externsOfSigs_map_sig] at hm_ex
          rcases hΓ with ⟨_, _⟩ | ⟨_, hΓcur⟩
          · exact absurd (by assumption) hnot_fnsig
          · exact ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hm_ex, hΓcur⟩
      have hsound := compile_sound T h lt M Γnext acc exits nX cc.hints cc.compiled.code
        cc.compiled.bounds k₀ hcm_acc hinf_c hu hcalls_c hwf hsupp hwp_step hext_M
        ⟨hacc_uniq, hdisj_c_ext⟩ hexits
      intro g hg
      obtain ⟨g', hg', hnm, hdef, hspec⟩ :=
        hsound (g.name, cc.compiled.bound g.name) (cc.compiled.bound_mem (List.mem_map_of_mem hg))
      obtain rfl := fn_eq_of_mem_fns hnd_fns hg hg' hnm
      refine ⟨hdef, Target.FnSpec.of_spec T hspec fun _ _ _ _ ⟨_, _, has₀, hbs₀, _, _, _,
          hxs₀, hQ₀, hX₀, _, ha, hb, hΓn⟩ => ?_⟩
      subst ha; subst hb
      exact ⟨g.as, g.rs, has₀, hbs₀, _, _, _, hxs₀, hQ₀, hX₀,
        List.mem_append_left _ (List.mem_map_of_mem hg), hΓn⟩
  | recBudgetSCC ext bfs hints maxB expB cbr =>
      let BM : BudgetModule := ⟨bfs, externsOfSigs extSigs, exits⟩
      have hdisj_b : ∀ p ∈ acc, p.1.1 ∉ bfs.map (fun b => b.toFn.name) := fun p hp hm =>
        hdisj_c_ext p hp (by dsimp only [Chunk.fns]; rwa [List.map_map])
      let M_acc : CompiledBudgetRec T lt acc exits nX bfs hints maxB expB :=
        { cbr with compileModuleBudgetRec_eq :=
            compileModuleBudgetRec_mono_lookupBound hcompat hdisj_b cbr.compileModuleBudgetRec_eq }
      have hext_M : ∀ p ∈ acc, T.FnSpec h p.1.1
          (legalEnv lt (Env.restrict Γcur BM.extSigs) p.1.1 p.1.2.1 p.1.2.2) p.2 nX :=
        fun p hp => by
          dsimp only [BM, BudgetModule.extSigs]; rw [externsOfSigs_map_sig]; exact hacc p hp
      have hres := link_scc_budget_lfp M_acc BM rfl h Γcur k₀ hinf_c hu hcalls_c
        (fun b hb => hwf b.toFn (List.mem_map_of_mem hb))
        (fun b hb => hsupp b.toFn (List.mem_map_of_mem hb)) hext_M hacc_uniq hexits
      have hMnd := Module.namesNodup_of_checkNamesNodup ((Bool.and_eq_true _ _).mp hcalls_c).1
      intro g hg; obtain ⟨bg, hbg, rfl⟩ := List.mem_map.mp hg
      obtain ⟨hdef, hspec⟩ := hres (cbr.bound bg.toFn.name) (cbr.bound_ra_le bg.toFn.name) bg hbg
      refine ⟨hdef, Target.FnSpec.of_spec T hspec fun _ _ _ _ ⟨_, _, has₀, hbs₀, _, _, _,
          hxs₀, hQ₀, hX₀, _, ha, hb, hstep⟩ => ?_⟩
      subst ha; subst hb
      rcases hstep with ⟨_, hsem⟩ | ⟨hmemE, _⟩
      · exact ⟨bg.toFn.as, bg.toFn.rs, has₀, hbs₀, _, _, _, hxs₀, hQ₀, hX₀, rfl, rfl, rfl, hsem⟩
      · exact absurd hmemE (fn_name_not_mem_externs_mod hMnd (List.mem_map_of_mem hbg))

private theorem chunk_sig_decomp {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    {h : T.mach.Host} (c : Chunk T lt exits nX) (cs : List (Chunk T lt exits nX))
    (acc : List (SigEntry × Nat)) (extSigs : List SigEntry) (Γcur : Env)
    (hnd : ((c.fns.map Fn.name ++ (sccChunksFns cs).map Fn.name) ++ extSigs.map Prod.fst).Nodup)
    (hchunk_spec : ∀ g ∈ c.fns, T.Defined h g.name ∧ T.FnSpec h g.name
      (legalEnv lt (Env.onlyFn g (c.sem extSigs Γcur)) g.name (lt.legalSig g.as) (lt.legalSig g.rs))
      (c.bound g.name) nX)
    (hacc : ∀ p ∈ acc,
      T.FnSpec h p.1.1 (legalEnv lt (Env.restrict Γcur extSigs) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hacc_uniq : ∀ p ∈ acc, ∀ q ∈ acc, p.1.1 = q.1.1 → p.2 = q.2)
    (hdisj_c_ext : ∀ p ∈ acc, p.1.1 ∉ c.fns.map Fn.name)
    (hacc_disj : ∀ p ∈ acc, p.1.1 ∉ (c.fns ++ sccChunksFns cs).map Fn.name) :
    ((sccChunksFns cs).map Fn.name ++ (c.fns.map Fn.sig ++ extSigs).map Prod.fst).Nodup ∧
    (∀ p ∈ c.sigBounds.reverse ++ acc, T.FnSpec h p.1.1
      (legalEnv lt (Env.restrict (c.sem extSigs Γcur) (c.fns.map Fn.sig ++ extSigs))
        p.1.1 p.1.2.1 p.1.2.2) p.2 nX) ∧
    (∀ p ∈ c.sigBounds.reverse ++ acc, ∀ q ∈ c.sigBounds.reverse ++ acc,
      p.1.1 = q.1.1 → p.2 = q.2) ∧
    (∀ p ∈ c.sigBounds.reverse ++ acc, p.1.1 ∉ (sccChunksFns cs).map Fn.name) := by
  have hnd_1 := List.nodup_append.mp hnd; have hnd_fns := List.nodup_append.mp hnd_1.1
  have hmapFst : (c.fns.map Fn.sig ++ extSigs).map Prod.fst =
      c.fns.map Fn.name ++ extSigs.map Prod.fst := by simp [List.map_append, Fn.sig]
  have hndS : ((c.fns.map Fn.sig ++ extSigs).map Prod.fst).Nodup := by
    rw [hmapFst]; exact List.nodup_append.mpr ⟨hnd_fns.1, hnd_1.2.1,
      fun a ha b hb he => hnd_1.2.2 a (List.mem_append_left _ ha) b hb he⟩
  have hsigB : ∀ p ∈ c.sigBounds.reverse, ∃ g ∈ c.fns,
      p = ((g.name, lt.legalSig g.as, lt.legalSig g.rs), c.bound g.name) :=
    fun p hp => c.mem_sigBounds (List.mem_reverse.mp hp)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hmapFst]; refine List.nodup_append.mpr ⟨hnd_fns.2.1, by rw [← hmapFst]; exact hndS,
      fun a ha b hb he => (List.mem_append.mp hb).elim (fun h => hnd_fns.2.2 b h a ha he.symm)
        (fun h => hnd_1.2.2 a (List.mem_append_right _ ha) b h he)⟩
  · intro p hp; rcases List.mem_append.mp hp with hp_c | hp_acc
    · obtain ⟨g, hg, rfl⟩ := hsigB p hp_c
      refine Target.FnSpec.of_spec T (hchunk_spec g hg).2 fun _ _ _ _ ⟨_, _, has₀, hbs₀,
          _, _, _, hxs₀, hQ₀, hX₀, hmemS, hΓ⟩ => ?_
      obtain ⟨rfl, rfl⟩ := mem_unique_fst_sig hndS hmemS
        (List.mem_append_left _ (List.mem_map_of_mem hg))
      exact ⟨g.as, g.rs, has₀, hbs₀, _, _, _, hxs₀, hQ₀, hX₀, rfl, rfl, rfl, hΓ⟩
    · refine Target.FnSpec.of_spec T (hacc p hp_acc) fun _ _ _ _ ⟨_, _, has₀, hbs₀,
          xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hmemS, hΓ⟩ => ?_
      have hnot_fn := hdisj_c_ext p hp_acc
      rcases List.mem_append.mp hmemS with hm_c | hm_e
      · obtain ⟨fn, hfn, heq⟩ := List.mem_map.mp hm_c
        exact absurd ((congrArg Prod.fst heq) ▸ List.mem_map_of_mem hfn) hnot_fn
      · exact ⟨_, _, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hm_e,
          (c.sem_iff_of_not_mem hnot_fn hm_e _ _ _ _).mp hΓ⟩
  · intro p hp q hq hnm; rcases List.mem_append.mp hp with hp_c | hp_acc <;>
        rcases List.mem_append.mp hq with hq_c | hq_acc
    · obtain ⟨g₁, hg₁, rfl⟩ := hsigB p hp_c; obtain ⟨g₂, hg₂, rfl⟩ := hsigB q hq_c
      rw [fn_eq_of_mem_fns hnd_fns.1 hg₁ hg₂ hnm]
    · obtain ⟨g₁, hg₁, rfl⟩ := hsigB p hp_c
      exact absurd (hnm ▸ List.mem_map_of_mem hg₁) (hdisj_c_ext q hq_acc)
    · obtain ⟨g₂, hg₂, rfl⟩ := hsigB q hq_c
      exact absurd (hnm.symm ▸ List.mem_map_of_mem hg₂) (hdisj_c_ext p hp_acc)
    · exact hacc_uniq p hp_acc q hq_acc hnm
  · intro p hp hm; rcases List.mem_append.mp hp with hp_c | hp_acc
    · obtain ⟨g, hg, rfl⟩ := hsigB p hp_c
      exact hnd_fns.2.2 g.name (List.mem_map_of_mem hg) g.name hm rfl
    · exact hacc_disj p hp_acc (by rw [List.map_append]; exact List.mem_append_right _ hm)

theorem linkChunks_fnSpec {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (h : T.mach.Host) (ext₀ : List (SigEntry × Nat)) (extSigs : List SigEntry) (Γ₀ : Env)
    (chunks : List (Chunk T lt exits nX)) (k₀ : Nat)
    (hc : (sccChunksCode chunks).IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hchkExt : checkSccChunksExt ext₀ chunks = true)
    (hcalls : checkChunksCalls exits extSigs chunks = true)
    (hnd : ((sccChunksFns chunks).map Fn.name ++ extSigs.map Prod.fst).Nodup)
    (hwf : ∀ f ∈ sccChunksFns chunks, f.Wf)
    (hsupp : ∀ f ∈ sccChunksFns chunks, (f.earlyOpt).body.supportsSource lt = true)
    (hext : ∀ p ∈ ext₀,
      T.FnSpec h p.1.1 (legalEnv lt (Env.restrict Γ₀ extSigs) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : ∀ p ∈ ext₀, ∀ q ∈ ext₀, p.1.1 = q.1.1 → p.2 = q.2)
    (hext_disj : ∀ p ∈ ext₀, p.1.1 ∉ (sccChunksFns chunks).map Fn.name)
    (hexits : ∀ g ∈ exits, T.Defined h g) :
    ∀ c ∈ chunks, ∀ f ∈ c.fns, T.Defined h f.name ∧ T.FnSpec h f.name
      (legalEnv lt (Env.onlyFn f (semChunks extSigs Γ₀ chunks)) f.name
        (lt.legalSig f.as) (lt.legalSig f.rs)) (c.bound f.name) nX := by
  cases chunks with
  | nil => intro _ hc; nomatch hc
  | cons c cs =>
      intro c' hc' f hf
      dsimp only [checkSccChunksExt] at hchkExt; dsimp only [checkChunksCalls] at hcalls
      simp only [Bool.and_eq_true] at hchkExt hcalls
      obtain ⟨hinf_c, hinf_cs⟩ := List.IsInfixAt.append hc
      have hnd_top : ((c.fns.map Fn.name ++ (sccChunksFns cs).map Fn.name) ++
          extSigs.map Prod.fst).Nodup := by simpa [sccChunksFns, List.map_append] using hnd
      have hnd_1 := List.nodup_append.mp hnd_top; have hnd_fns := List.nodup_append.mp hnd_1.1
      have hdisj_c_ext : ∀ p ∈ ext₀, p.1.1 ∉ c.fns.map Fn.name := fun p hp hm =>
        hext_disj p hp (by
          dsimp only [sccChunksFns]; rw [List.map_append]; exact List.mem_append_left _ hm)
      have hchunk_spec := chunk_step_wp h c k₀ ext₀ extSigs Γ₀ hinf_c hu
        (checkExtCompat_lookupBound hchkExt.1) hcalls.1 hnd_fns.1 hnd_1.2.1
        (fun a ha b hb he => hnd_1.2.2 a (List.mem_append_left _ ha) b hb he)
        (fun g hg => hwf g (List.mem_append_left _ hg))
        (fun g hg => hsupp g (List.mem_append_left _ hg)) hext hext_uniq hdisj_c_ext hexits
      rcases List.mem_cons.mp hc' with rfl | hcs
      · refine ⟨(hchunk_spec f hf).1, Target.FnSpec.of_spec T (hchunk_spec f hf).2
          fun _ _ _ _ ⟨_, _, has₀, hbs₀, _, _, _, hxs₀, hQ₀, hX₀, _, ha, hb, hsem⟩ => ?_⟩
        subst ha; subst hb
        have hnot_rest := sccChunks_fn_not_mem_rest hf
          (by simpa only [List.map_append] using hnd_1.1)
        exact ⟨f.as, f.rs, has₀, hbs₀, _, _, _, hxs₀, hQ₀, hX₀, rfl, rfl, rfl,
          (semChunks_agree_earlier cs (c'.fns.map Fn.sig ++ extSigs) (c'.sem extSigs Γ₀)
            hnot_rest (List.mem_append_left _ (List.mem_map_of_mem hf)) _ _ _ _).mp hsem⟩
      · obtain ⟨hnd_cs, hacc', hacc_uniq', hacc_disj'⟩ := chunk_sig_decomp c cs ext₀ extSigs Γ₀
          hnd_top hchunk_spec hext hext_uniq hdisj_c_ext hext_disj
        exact linkChunks_fnSpec h (c.sigBounds.reverse ++ ext₀) (c.fns.map Fn.sig ++ extSigs)
          (c.sem extSigs Γ₀) cs (k₀ + c.code.length) hinf_cs hu hchkExt.2 hcalls.2
          hnd_cs (fun g hg => hwf g (List.mem_append_right _ hg))
          (fun g hg => hsupp g (List.mem_append_right _ hg))
          hacc' hacc_uniq' hacc_disj' hexits c' hcs f hf

theorem linkChunks_fnSpec_linked {T : Target} (L : TargetLayout T)
    (hcl : Rega.LabelClean T.toIsa) {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (ext₀ : List (SigEntry × Nat)) (extSigs : List SigEntry) (Γ₀ : Env)
    (chunks : List (Chunk T lt exits nX)) (hchk : checkLinkSccList L ext₀ chunks = true)
    (hcalls : checkChunksCalls exits extSigs chunks = true)
    (hnd_ext : (extSigs.map Prod.fst).Nodup)
    (hdisj_ext : ∀ nm ∈ (sccChunksFns chunks).map Fn.name, nm ∉ extSigs.map Prod.fst)
    (hwf : ∀ f ∈ sccChunksFns chunks, f.Wf)
    (hsupp : ∀ f ∈ sccChunksFns chunks, (f.earlyOpt).body.supportsSource lt = true)
    (hext : ∀ p ∈ ext₀, T.FnSpec (sccHost L ext₀ chunks hchk) p.1.1
      (legalEnv lt (Env.restrict Γ₀ extSigs) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : ∀ p ∈ ext₀, ∀ q ∈ ext₀, p.1.1 = q.1.1 → p.2 = q.2) :
    ∀ c ∈ chunks, ∀ f ∈ c.fns,
      T.Defined (sccHost L ext₀ chunks hchk) f.name ∧
      T.FnSpec (sccHost L ext₀ chunks hchk) f.name
        (legalEnv lt (Env.onlyFn f (semChunks extSigs Γ₀ chunks)) f.name
          (lt.legalSig f.as) (lt.legalSig f.rs)) (sccBound chunks f.name) nX := by
  have hp := checkLinkSccList_parts hchk
  have hnd_fns := (List.nodup_append.mp hp.2.2.2.2.1).1
  have hnd : ((sccChunksFns chunks).map Fn.name ++ extSigs.map Prod.fst).Nodup :=
    List.nodup_append.mpr ⟨hnd_fns, hnd_ext, fun a ha b hb he => hdisj_ext a ha (he ▸ hb)⟩
  intro c hc f hf
  have hres := linkChunks_fnSpec (sccHost L ext₀ chunks hchk) ext₀ extSigs Γ₀ chunks 0
    (sccCode_infix_host L ext₀ chunks hchk) (sccLabelsUnique L hcl ext₀ chunks hchk)
    hp.1 hcalls hnd hwf hsupp hext hext_uniq hp.2.1
    (fun _ hg => sccDefined_exit_host L ext₀ chunks hchk hg) c hc f hf
  rw [sccBound_eq_chunk chunks hnd_fns c hc (List.mem_map_of_mem hf)]; exact hres

theorem linkChunks_fnSpec_host {T : Target} (L : TargetLayout T)
    (hcl : Rega.LabelClean T.toIsa) {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (chunks : List (Chunk T lt exits nX)) (hchk : checkLinkSccList L [] chunks = true)
    (hcalls : checkChunksCalls exits [] chunks = true) (hwf : ∀ f ∈ sccChunksFns chunks, f.Wf)
    (hsupp : ∀ f ∈ sccChunksFns chunks, (f.earlyOpt).body.supportsSource lt = true) :
    ∀ c ∈ chunks, ∀ f ∈ c.fns,
      T.Defined (sccHost L [] chunks hchk) f.name ∧
      T.FnSpec (sccHost L [] chunks hchk) f.name
        (legalEnv lt (Env.onlyFn f (semChunks [] (fun _ _ _ _ _ _ _ => False) chunks))
          f.name (lt.legalSig f.as) (lt.legalSig f.rs)) (sccBound chunks f.name) nX :=
  linkChunks_fnSpec_linked L hcl [] [] (fun _ _ _ _ _ _ _ => False) chunks hchk hcalls
    List.nodup_nil (fun _ _ hm => nomatch hm) hwf hsupp
    (fun _ h => nomatch h) (fun _ h => nomatch h)

end LeanQbe.T
