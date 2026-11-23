module

public import LeanQbe.T.Main

/-!
# Measure/Fuel-Indexed Cyclic & Mutual-Recursion Module Linking

Extends `LeanQbe.T.Module` and `LeanQbe.T.Main` with measure/fuel-indexed cyclic and mutually
recursive module linking without modifying `Module`, `Main`, `Rega`, or `Target`:

* **Source/IR linking**: `checkCyclic`, `CallsOkRec`, `Env.onlyFn`, `Env.stepRec`,
  `Env.ofModuleRec`, `Env.ofModuleRecAt`, `envOfMeasureSpec`, and `ModuleRecOk`.
* **Machine compilation & stack-bound validation**: `calleesBoundRec`, `checkAndBoundRecExt`,
  `checkAndBoundRecMid`, `checkAndBoundRec`, `compileModuleRecAux`, and `compileModuleRec`,
  tracking per-function base footprint + external acyclic callees (`baseBound`) and cyclic SCC
  per-call frame increment (`stepBound := max_f (F_f + raBytes)`), declared exits (`nX`), and
  `baseBound + fuel * stepBound ≤ maxBound ≤ 2^64` (plus `+ raBytes ≤ 2^64`).
* **Kernel result checkers & extractors**: `checkCompileRecResult`,
  `checkCompileRecResultWithLabels`, `extractRecCode`, `extractRecBase`, `extractRecStep`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LinkRec

open LeanQbe.T

/-! ## 1. Cyclic `Module` Checks and Measure-Indexed Environments -/

/-- Decidable-free boolean check that `M.namesNodup` holds and every function in `M.fns` only
calls signatures in `M.sigs` (including mutual/self calls) and exits in `M.exits`. -/
def checkCyclic (M : Module) : Bool :=
  M.checkNamesNodup && M.fns.all (fun fn => fn.checkCallsOk M.sigs M.exits)

/-- Well-formedness and cyclic call/exit closure for a module `M`. -/
def CallsOkRec (M : Module) : Prop :=
  M.namesNodup ∧ ∀ fn ∈ M.fns, fn.Wf ∧ fn.callsOk M.sigs M.exits

/-- Restrict `Γ` to the single function signature `(f.name, f.as, f.rs)`. -/
def Env.onlyFn (f : Fn) (Γ : Env) : Env :=
  fun g as bs xs m Q X =>
    g = f.name ∧ ∃ (ha : as = f.as) (hb : bs = f.rs),
      Γ f.name f.as f.rs (ha ▸ xs) m (hb ▸ Q) X

/-- Measure-stepped environment available to the body of a recursive function at fuel `k`:
cyclic callees in `recSigs` may only be invoked at strictly smaller `k' < k`, while external
acyclic callees in `extSigs` are invoked at fixed `Γext`. -/
def Env.stepRec (recSigs extSigs : List SigEntry) (Γrec : Nat → Env) (Γext : Env)
    (k : Nat) : Env :=
  fun f as bs xs m Q X =>
    ((f, as, bs) ∈ recSigs ∧ ∃ k', k' < k ∧ Γrec k' f as bs xs m Q X) ∨
    ((f, as, bs) ∈ extSigs ∧ Γext f as bs xs m Q X)

/-- Closed cyclic module environment pairing measure-indexed `Γrec` over `M.fns` with fixed
external contracts `Γext` over `M.externs`. -/
def Env.ofModuleRec (M : Module) (Γrec : Nat → Env) (Γext : Env) : Env :=
  fun f as bs xs m Q X =>
    ((f, as, bs) ∈ M.fns.map Fn.sig ∧ ∃ k, Γrec k f as bs xs m Q X) ∨
    ((f, as, bs) ∈ M.externs.map Extern.sig ∧ Γext f as bs xs m Q X)

/-- Measure-`k` slice of `Env.ofModuleRec` matching `CompiledRec` stack bound `base + k * step`. -/
def Env.ofModuleRecAt (M : Module) (Γrec : Nat → Env) (Γext : Env) (k : Nat) : Env :=
  fun f as bs xs m Q X =>
    ((f, as, bs) ∈ M.fns.map Fn.sig ∧ Γrec k f as bs xs m Q X) ∨
    ((f, as, bs) ∈ M.externs.map Extern.sig ∧ Γext f as bs xs m Q X)

/-- Lift a single-signature measure-indexed contract family `P : Sym → Nat → Spec as bs` into
`Nat → Env`. -/
def envOfMeasureSpec {as bs : List Ty} (P : Sym → Nat → Spec as bs) : Nat → Env :=
  fun k f as' bs' xs m Q X =>
    ∃ (ha : as' = as) (hb : bs' = bs), P f k (ha ▸ xs) m (hb ▸ Q) X

/-- Cyclic module correctness obligation: `M.namesNodup`, per-function `Wf` and `callsOk`, and
every `fn ∈ M.fns` at fuel `k` satisfies `Func.wp` under `Env.stepRec ... k`. -/
structure ModuleRecOk (Γrec : Nat → Env) (Γext : Env) (M : Module) : Prop where
  nodup : M.namesNodup
  fnsOk : ∀ fn ∈ M.fns,
    fn.Wf ∧ fn.callsOk M.sigs M.exits ∧
    ∀ k xs m Q X, Γrec k fn.name fn.as fn.rs xs m Q X →
      Func.wp (Env.stepRec (M.fns.map Fn.sig) (M.externs.map Extern.sig) Γrec Γext k)
        fn.body xs m Q X

/-! ## 2. Measure-Indexed Machine Compilation and Stack-Bound Checking -/

/-- Compute the base-case stack bound of a function with local frame `F` and return-address bytes
`raBytes` across `gs`: cyclic callees in `recSigs` require `F + raBytes` at `k = 0`, while
external acyclic callees in `extCallees` require `F + raBytes + bg`. -/
def calleesBoundRec (F raBytes : Nat) (recSigs : List SigEntry)
    (extCallees : List (SigEntry × Nat)) : List SigEntry → Option Nat
  | [] => some F
  | g :: gs =>
    if recSigs.any (SigEntry.beq g) then
      (calleesBoundRec F raBytes recSigs extCallees gs).map (Nat.max (F + raBytes))
    else
      match lookupBound extCallees g, calleesBoundRec F raBytes recSigs extCallees gs with
      | some bg, some rest => some (Nat.max (F + raBytes + bg) rest)
      | _, _ => none

/-- Compute `(baseBound_f, stepBound_f)` for pre-extracted `ext : Rega.Ext` and `h : I.Hints`,
verifying all callees (cyclic or external) and declared exits (`nX` headroom). -/
def checkAndBoundRecExt (I : Isa) (raBytes : Nat) (recSigs : List SigEntry)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (h : I.Hints) (ext : Rega.Ext) : Option (Nat × Nat) :=
  let F := I.frame.frameSize h.totalSlots
  match calleesBoundRec F raBytes recSigs extCallees ext.callees with
  | none => none
  | some n₁ =>
    if ext.exits.all (fun g => exits.contains g) then
      let b := if ext.exits.isEmpty then n₁ else Nat.max n₁ nX
      some (b, F + raBytes)
    else none

/-- Compute `(baseBound_f, stepBound_f)` for a pre-lowered mid-end function `mf = f.mid lt`. -/
def checkAndBoundRecMid (I : Isa) (raBytes : Nat) (recSigs : List SigEntry)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (h : I.Hints) (mf : Fn) : Option (Nat × Nat) :=
  checkAndBoundRecExt I raBytes recSigs extCallees exits nX h mf.ext

/-- Compute `(baseBound_f, stepBound_f)` for `f` under legalization target `lt` and hints `h`. -/
def checkAndBoundRec (I : Isa) (lt : LegalTarget) (raBytes : Nat) (recSigs : List SigEntry)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (f : Fn) (h : I.Hints) : Option (Nat × Nat) :=
  checkAndBoundRecMid I raBytes recSigs extCallees exits nX h (f.mid lt)

/-- Compile a potentially cyclic list of functions `fs` against `recSigs` and `extCallees`,
accumulating `(code, max_f base_f, max_f (F_f + raBytes))`. -/
def compileModuleRecAux (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (recSigs : List SigEntry) (extCallees : List (SigEntry × Nat))
    (exits : List Sym) (nX : Nat) :
    List Fn → List I.Hints → Except String (List I.Directive × Nat × Nat)
  | [], [] => .ok ([], 0, 0)
  | f :: fs, h :: hs =>
    let mf := f.mid lt
    let ext := mf.ext
    match Rega.lowerFn I h ext mf,
          checkAndBoundRecExt I raBytes recSigs extCallees exits nX h ext with
    | .ok c, some (bf, sf) =>
      match compileModuleRecAux I lt raBytes recSigs extCallees exits nX fs hs with
      | .ok (cs, brest, srest) =>
        .ok (c ++ cs, Nat.max bf brest, Nat.max sf srest)
      | .error e => .error e
    | .error e, _ => .error s!"{f.name}: {e}"
    | _, none => .error s!"{f.name}: unknown callee or undeclared exit"
  | _, _ => .error "compileModuleRec: fn/hints length mismatch"

/-- Compile and validate a cyclic/mutually-recursive module `fs` without requiring acyclicity,
checking disjointness of `extCallees` from `fs`, per-function `Rega.lowerFn`, cyclic/external
callee bounds (`baseBound`), SCC frame step (`stepBound`), declared exits (`nX`), and
`baseBound + fuel * stepBound ≤ maxBound ≤ 2^64` (plus `+ raBytes ≤ 2^64`). -/
def compileModuleRec (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX fuel maxBound : Nat)
    (fs : List Fn) (hints : List I.Hints) :
    Except String (List I.Directive × Nat × Nat) :=
  let recSigs := fs.map (fun f => (f.name, lt.legalSig f.as, lt.legalSig f.rs))
  if extCallees.any (fun p => fs.any (fun f => f.name == p.1.1)) then
    .error "compileModuleRec: external callee collides with module function"
  else
    match compileModuleRecAux I lt raBytes recSigs extCallees exits nX fs hints with
    | .error e => .error e
    | .ok (code, baseBound, stepBound) =>
      let totalBound := baseBound + fuel * stepBound
      if Nat.ble totalBound maxBound &&
         Nat.ble maxBound (2 ^ 64) &&
         Nat.ble (totalBound + raBytes) (2 ^ 64) then
        .ok (code, baseBound, stepBound)
      else
        .error s!"compileModuleRec: stack bound overflow ({totalBound} > {maxBound})"

/-! ## 3. Kernel-Reducible Checkers and Result Extractors -/

/-- Kernel-reducible check using structural `fnNameOk` + `stringsNodup (fnNames ++ exits)`. -/
def checkCompileRecResult {D : Type} (label : Sym → D) (progSmall : List D → Bool)
    (res : Except String (List D × Nat × Nat)) (fnNames exits : List Sym) : Bool :=
  match res with
  | .error _ => false
  | .ok (code, _, _) =>
    let prog := code ++ exits.map label
    fnNames.all fnNameOk &&
    exits.all fnNameOk &&
    stringsNodup (fnNames ++ exits) &&
    progSmall prog

/-- Variant of `checkCompileRecResult` using an explicit `labelsNodup` directive checker. -/
def checkCompileRecResultWithLabels {D : Type} (label : Sym → D)
    (labelsNodup progSmall : List D → Bool)
    (res : Except String (List D × Nat × Nat)) (exits : List Sym) : Bool :=
  match res with
  | .error _ => false
  | .ok (code, _, _) =>
    let prog := code ++ exits.map label
    labelsNodup prog && progSmall prog

/-- Extract the directive stream from a `compileModuleRec` result. -/
def extractRecCode {D : Type} : Except String (List D × Nat × Nat) → List D
  | .ok (c, _, _) => c
  | .error _ => []

/-- Extract `baseBound` from a `compileModuleRec` result. -/
def extractRecBase {D : Type} : Except String (List D × Nat × Nat) → Nat
  | .ok (_, b, _) => b
  | .error _ => 0

/-- Extract `stepBound` from a `compileModuleRec` result. -/
def extractRecStep {D : Type} : Except String (List D × Nat × Nat) → Nat
  | .ok (_, _, s) => s
  | .error _ => 0

attribute [irreducible] extractRecCode extractRecBase extractRecStep

end LeanQbe.T.LinkRec
