module

public import Kraken.Layout
public import LeanQbe.T.Target
public meta import Lean.Elab.Tactic

/-!
# Arch-Free `CleanCode`, `TRel` Inversion, and `@[scoped isel_step]` Tactic Engine (`Stage 0`)

Target-neutral instruction-selection proof infrastructure shared by `Amd64` and `Arm64` without
co-importing `Kraken.X64` or `Kraken.AArch64`:

* `trel{1,2,3}_inv_generic`: arity-1/2/3 `TRel` inversions.
* `emitClean` / `emitClean_noLab` / `emitCleanOpt` / `emitCleanPair`: lift `List Instr` to
  `List (Kraken.Directive Instr Const)` with zero `.label` directives by construction.
* `@[scoped isel_step]` attribute and `isel_step` / `isel_steps` tactics matching unresolved
  `` `Program.wp `` via non-reducing `forallTelescope`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## 1. Target-Generic `TRel` Inversion Combinators -/

theorem trel1_inv_generic {R V C : Type} {P : ∀ t, PArg R V C t → Val t → Prop} {t : Ty}
    {pa : PArg R V C t} {v : Val t}
    (h : TRel P (as := [t]) (pa, ()) (v, ())) : P t pa v := by
  cases h with | cons hx _ => exact hx

theorem trel2_inv_generic {R V C : Type} {P : ∀ t, PArg R V C t → Val t → Prop} {t₁ t₂ : Ty}
    {pa : PArg R V C t₁} {pb : PArg R V C t₂} {va : Val t₁} {vb : Val t₂}
    (h : TRel P (as := [t₁, t₂]) (pa, pb, ()) (va, vb, ())) : P t₁ pa va ∧ P t₂ pb vb := by
  cases h with | cons hx h2 => cases h2 with | cons hy _ => exact ⟨hx, hy⟩

theorem trel3_inv_generic {R V C : Type} {P : ∀ t, PArg R V C t → Val t → Prop}
    {t₁ t₂ t₃ : Ty} {pa : PArg R V C t₁} {pb : PArg R V C t₂} {pc : PArg R V C t₃}
    {va : Val t₁} {vb : Val t₂} {vc : Val t₃}
    (h : TRel P (as := [t₁, t₂, t₃]) (pa, pb, pc, ()) (va, vb, vc, ())) :
    P t₁ pa va ∧ P t₂ pb vb ∧ P t₃ pc vc := by
  cases h with
  | cons hx h2 => cases h2 with | cons hy h3 => cases h3 with | cons hz _ => exact ⟨hx, hy, hz⟩

/-! ## 2. `CleanCode`: `NoLab`-by-Construction on `Kraken.Directive` -/

/-- Lift a straight-line instruction list to `List (Kraken.Directive I D)` with zero `.label`
directives by construction. -/
def emitClean {I D : Type} (ins : List I) : List (Kraken.Directive I D) :=
  ins.map Kraken.Directive.instr

theorem emitClean_nil {I D : Type} :
    emitClean (I := I) (D := D) [] = [] := rfl

theorem emitClean_cons {I D : Type} (i : I) (is : List I) :
    emitClean (D := D) (i :: is) = Kraken.Directive.instr i :: emitClean is := rfl

theorem emitClean_append {I D : Type} (a b : List I) :
    emitClean (D := D) (a ++ b) = emitClean a ++ emitClean b :=
  List.map_append

theorem emitClean_ite {I D : Type} (p : Prop) [Decidable p] (a b : List I) :
    emitClean (D := D) (if p then a else b) = if p then emitClean a else emitClean b := by
  split <;> rfl

theorem emitClean_noLab {I D : Type} (ins : List I) (l : String) :
    (Kraken.Directive.label l : Kraken.Directive I D) ∉ emitClean ins := by
  intro hm
  rcases List.mem_map.mp hm with ⟨_, _, heq⟩
  cases heq

/-- Lift an optional straight-line instruction list to `Option (List (Kraken.Directive I D))`. -/
def emitCleanOpt {I D : Type} (x : Option (List I)) : Option (List (Kraken.Directive I D)) :=
  x.map emitClean

/-- Lift an optional `(List I × α)` result to `Option (List (Kraken.Directive I D) × α)`. -/
def emitCleanPair {I D α : Type} (x : Option (List I × α)) :
    Option (List (Kraken.Directive I D) × α) :=
  x.map fun (is, a) => (emitClean is, a)

theorem emitCleanOpt_noLab {I D : Type} {x : Option (List I)}
    {c : List (Kraken.Directive I D)} (h : emitCleanOpt x = some c) (l : String) :
    (Kraken.Directive.label l : Kraken.Directive I D) ∉ c := by
  rcases Option.map_eq_some_iff.mp h with ⟨_, _, rfl⟩
  exact emitClean_noLab _ l

theorem emitCleanPair_noLab {I D α : Type} {x : Option (List I × α)}
    {c : List (Kraken.Directive I D)} {a : α}
    (h : emitCleanPair x = some (c, a)) (l : String) :
    (Kraken.Directive.label l : Kraken.Directive I D) ∉ c := by
  rcases Option.map_eq_some_iff.mp h with ⟨⟨_, _⟩, _, h1⟩
  obtain ⟨rfl, -⟩ := Prod.mk.inj h1
  exact emitClean_noLab _ l

theorem emitCleanOpt_eq_some {I D : Type} {x : Option (List I)}
    {c : List (Kraken.Directive I D)} :
    emitCleanOpt x = some c ↔ ∃ ci, x = some ci ∧ c = emitClean ci := by
  simp only [emitCleanOpt, Option.map_eq_some_iff]
  exact ⟨fun ⟨ci, h, hc⟩ => ⟨ci, h, hc.symm⟩, fun ⟨ci, h, hc⟩ => ⟨ci, h, hc.symm⟩⟩

theorem emitCleanPair_eq_some {I D α : Type} {x : Option (List I × α)}
    {c : List (Kraken.Directive I D)} {a : α} :
    emitCleanPair x = some (c, a) ↔ ∃ ci, x = some (ci, a) ∧ c = emitClean ci := by
  constructor
  · intro h
    rcases Option.map_eq_some_iff.mp h with ⟨⟨ci, ai⟩, hci, h1⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    exact ⟨ci, hci, rfl⟩
  · rintro ⟨ci, hci, rfl⟩
    simp [emitCleanPair, hci]

theorem emitCleanPair_isSome {I D α : Type} (x : Option (List I × α)) :
    (emitCleanPair (D := D) x).isSome = x.isSome := by
  cases x <;> rfl

namespace IselClean
attribute [scoped simp] emitClean_nil emitClean_cons emitClean_append emitClean_ite
  emitCleanPair_isSome
end IselClean

/-! ## 3. Head-Indexed `@[scoped isel_step]` Attribute & Tactic Engine -/

namespace IselStep

open Lean Meta Elab Tactic

/-- Metadata extracted from a `@[scoped isel_step]` rule. -/
meta structure IselStepEntry where
  ruleName : Name
  headKey  : Name
  isLast   : Bool
  nIntros  : Nat
  deriving BEq, Inhabited

/-- Scoped environment extension storing registered `@[isel_step]` rules. -/
meta initialize iselStepExt :
    SimpleScopedEnvExtension IselStepEntry (Array IselStepEntry) ←
  registerSimpleScopedEnvExtension {
    initial := #[]
    addEntry := fun arr e => arr.push e
  }

/-- Extract a canonical operation/helper head name by peeling `Kraken.Directive.instr` and
known single-instruction wrappers (using unresolved `Name` literals to remain arch-free). -/
private meta partial def extractInstrKey (e : Lean.Expr) : Name :=
  let e := e.consumeMData.headBeta
  let nm := e.getAppFn.consumeMData.constName?.getD Name.anonymous
  if nm == ``Kraken.Directive.instr && e.getAppNumArgs ≥ 1 then
    extractInstrKey e.appArg!
  else if (nm == `LeanQbe.T.Amd64.ins || nm == `LeanQbe.T.Amd64.ins32 ||
           nm == `LeanQbe.T.Amd64.ins16 || nm == `LeanQbe.T.Amd64.ins8 ||
           nm == `LeanQbe.T.Amd64.insI || nm == `LeanQbe.T.Amd64.ins32I ||
           nm == `LeanQbe.T.Amd64.ins16I || nm == `LeanQbe.T.Amd64.ins8I ||
           nm == `LeanQbe.T.Arm64.ins || nm == `LeanQbe.T.Arm64.insI ||
           nm == `Kraken.X64.Instr.regular || nm == `Kraken.X64.Instr.avx ||
           nm == `Kraken.AArch64.Instr.mk) && e.getAppNumArgs ≥ 1 then
    extractInstrKey e.appArg!
  else if (nm == `LeanQbe.T.Amd64.insW || nm == `LeanQbe.T.Amd64.insWI) &&
          e.getAppNumArgs ≥ 2 then
    extractInstrKey e.appArg!
  else
    nm

/-- Inspect `... → Program.wp (hd :: rest) ...` using non-reducing `forallTelescope` and the
unresolved `` `Program.wp `` name literal (matching both `Kraken.X64` and `Kraken.AArch64`). -/
private meta def analyzeIselRule (declName : Name) : MetaM IselStepEntry := do
  let info ← getConstInfo declName
  forallTelescope info.type fun xs body => do
    let body := body.consumeMData.headBeta
    let some wpFn := body.getAppFn.constName?
      | throwError "isel_step: conclusion must be Program.wp"
    unless wpFn == `Program.wp do
      throwError "isel_step: expected Program.wp, got {wpFn}"
    let args := body.getAppArgs
    unless args.size ≥ 2 do
      throwError "isel_step: expected Program.wp with ≥ 2 arguments, got {args.size}"
    let prog := args[1]!.consumeMData
    unless prog.isAppOfArity ``List.cons 3 do
      throwError "isel_step: program must start with List.cons, got {prog}"
    let hd := prog.getArg! 1 |>.consumeMData
    let tl := prog.getArg! 2 |>.consumeMData
    let isLast := tl.getAppFn.isConstOf ``List.nil
    let headKey := extractInstrKey hd
    if xs.isEmpty then
      throwError "isel_step: rule {declName} must take a continuation hypothesis"
    let lastHyp := xs.back!
    let lastTy ← inferType lastHyp
    let nIntros ← forallTelescope lastTy fun ys _ => pure ys.size
    return { ruleName := declName, headKey, isLast, nIntros }

meta initialize registerBuiltinAttribute {
  name := `isel_step
  descr := "Register a single-instruction Program.wp stepping rule for isel_step / isel_steps"
  add := fun decl stx kind => do
    let _ := stx
    let entry ← (analyzeIselRule decl).run' {} {}
    iselStepExt.add entry kind
}

private meta def tryEntries (g : MVarId) (cands : Array IselStepEntry) : TacticM Bool := do
  for e in cands do
    let s ← saveState
    try
      let [hk] ← g.apply (← mkConstWithFreshMVarLevels e.ruleName) | s.restore; continue
      let (_, hk') ← hk.introN e.nIntros
      setGoals [hk']
      return true
    catch _ => s.restore
  return false

/-- Perform one head-indexed `Program.wp` step using active `@[scoped isel_step]` rules. -/
meta def iselStepOnce (entries : Array IselStepEntry) : TacticM Bool := withMainContext do
  let g ← getMainGoal
  let ty := (← instantiateMVars (← g.getType)).consumeMData.headBeta
  unless ty.getAppFn.isConstOf `Program.wp && ty.getAppNumArgs ≥ 2 do return false
  let prog0 := ty.getAppArgs[1]!.consumeMData
  let prog ←
    if prog0.isAppOfArity ``List.cons 3 then pure prog0
    else if prog0.isAppOf ``emitClean || prog0.isAppOf ``List.map then whnf prog0
    else pure prog0
  unless prog.isAppOfArity ``List.cons 3 do return false
  let hd := prog.getArg! 1 |>.consumeMData
  let tl0 := prog.getArg! 2 |>.consumeMData
  let tl ←
    if tl0.isAppOf ``List.nil || tl0.isAppOfArity ``List.cons 3 then pure tl0
    else if tl0.isAppOf ``emitClean || tl0.isAppOf ``List.map then whnf tl0
    else pure tl0
  let isLast := tl.getAppFn.isConstOf ``List.nil
  let key := extractInstrKey hd
  let cands := entries.filter fun e =>
    e.isLast == isLast && (e.headKey == key || e.headKey == Name.anonymous)
  if ← tryEntries g cands then return true
  if let some hd' ← unfoldDefinition? hd then
    let key' := extractInstrKey hd'
    if key' != key then
      let cands' := entries.filter fun e =>
        e.isLast == isLast && (e.headKey == key' || e.headKey == Name.anonymous)
      if ← tryEntries g cands' then return true
  return false

/-- Execute a single `@[scoped isel_step]` step on a `Program.wp` goal. -/
elab "isel_step" : tactic => do
  let entries := iselStepExt.getState (← getEnv)
  unless ← iselStepOnce entries do
    throwError "isel_step: no matching @[isel_step] rule for goal"

/-- Repeat head-indexed `isel_step` across straight-line `Program.wp` instruction sequences. -/
elab "isel_steps" : tactic => do
  let entries := iselStepExt.getState (← getEnv)
  let mut fuel := 64
  while fuel > 0 do
    fuel := fuel - 1
    if !(← iselStepOnce entries) then break

end IselStep

end LeanQbe.T
