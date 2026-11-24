module

public import LeanQbe.T.Module
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Flat
public import LeanQbe.T.FlatLemmas
public import Std.Data.HashMap
public meta import Lean
public meta import LeanQbe.T.Module
public meta import LeanQbe.T.Flat

/-!
# PatchModule: Additive M8 Splicing, `PatchBundle`, `splice_module!`, and `derive_reuse_bridge!`

Strictly additive assembly combinator and proof-automation module for Kissat M8 and future
multi-module splices (zero edits to existing `FullM7*` modules):

1. **Transparent `@[expose]` splicing primitives:**
   `spliceFns`, `spliceRows`, `patchInsAt`, `patchRowInsAt`, `patchFns`, `patchRows`,
   `patchModule`, `spliceModule`, `checkSlotPlan`, `checkPatchCallsOk`, `checkNoCallBad`.
2. **`PatchBundle`, `patchEnv`, and `patchBundle_moduleOk`:**
   Packages `(baseMod, baseTable, baseOk, repls, replRows, befores, beforeRows, rewiredRows)`
   with head-first priority `patchEnv` (`rewiredRows ++ replRows ++ beforeRows ++ baseTable`)
   and lifts `ModuleOk` via `patchBundle_moduleOk`, `patchBundle_moduleOk_isolated`, and
   `patchBundle_moduleOk_sameSpecs` without re-evaluating untouched base function bodies.
3. **Command elaborators:**
   * `splice_module!`: auto-computes slot indices, emits one batched `<id>_slotSigs`
     kernel `Eq.refl` theorem replacing dozens of manual `idx_N` lemmas, derives
     `<id>_replSigs_ok`, `<id>_names_nodup`, `<id>_wf`, and `<id>_acyclic`.
   * `derive_reuse_bridge!`: computes maximal identical `Fn` runs between two `Module`s
     using `reifyFunc` + `tflatBeq` and emits one batched kernel `Eq.refl` slice bridge
     with `O(1)` per-slice and per-function projections (`reuseSlice_at`, `fn_eq_of_slice_eq`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.PatchModule

open LeanQbe.T

/-! ## 1. Transparent Splicing Definitions (`@[expose]`) -/

@[expose] public section

/-- Replace functions in `fs` whose `name` appears in `repls`, preserving order. -/
def spliceFns (repls : List Fn) (fs : List Fn) : List Fn :=
  fs.map fun f => (repls.find? (·.name == f.name)).getD f

/-- Replace `SpecEntry` rows in `tbl` whose `name` appears in `repls`. -/
def spliceRows (repls : List SpecEntry) (tbl : List SpecEntry) : List SpecEntry :=
  tbl.map fun e => (repls.find? (·.name == e.name)).getD e

/-- Functions queued in `befores` for insertion immediately before `f`. -/
def patchInsAt (befores : List (Sym × List Fn)) (f : Fn) : List Fn :=
  match befores.find? (·.1 == f.name) with
  | some (_, ins) => ins
  | none => []

/-- Spec rows queued in `befores` for insertion immediately before `e`. -/
def patchRowInsAt (befores : List (Sym × List SpecEntry)) (e : SpecEntry) : List SpecEntry :=
  match befores.find? (·.1 == e.name) with
  | some (_, ins) => ins
  | none => []

/-- Combined replacement + before-host helper insertion over `fs`. -/
def patchFns (repls : List Fn) (befores : List (Sym × List Fn)) (fs : List Fn) : List Fn :=
  fs.flatMap fun f => patchInsAt befores f ++ [(repls.find? (·.name == f.name)).getD f]

/-- Combined replacement + before-host insertion over `SpecEntry` rows. -/
def patchRows (repls : List SpecEntry) (befores : List (Sym × List SpecEntry))
    (tbl : List SpecEntry) : List SpecEntry :=
  tbl.flatMap fun e => patchRowInsAt befores e ++ [(repls.find? (·.name == e.name)).getD e]

/-- Patch a `Module` with `repls` and optional `befores` insertions. -/
def patchModule (M : LeanQbe.T.Module) (repls : List Fn)
    (befores : List (Sym × List Fn) := []) : LeanQbe.T.Module :=
  { M with fns := patchFns repls befores M.fns }

/-- Splice replacements into a `Module`. -/
def spliceModule (M : LeanQbe.T.Module) (repls : List Fn) : LeanQbe.T.Module :=
  { M with fns := spliceFns repls M.fns }

/-- Boolean slot-plan verifier: checks that `idxs` matches each `r ∈ repls` in `baseFns`
with equal name and signature. -/
def checkSlotPlan (baseFns repls : List Fn) (idxs : List Nat) : Bool :=
  (repls.length == idxs.length) &&
  (repls.zip idxs).all fun (p : Fn × Nat) =>
    match baseFns[p.2]? with
    | some g => p.1.name == g.name && p.1.sig == g.sig
    | none => false

mutual
/-- `Bool` check ensuring `e` never calls any symbol in `bad`. -/
def checkNoCallInExpr (bad : List Sym) {rs : List Ty} :
    Expr (fun _ => Unit) (fun _ => Unit) rs → Bool
  | .let_ _ k => checkNoCallInExpr bad (k (Tup.units _))
  | .load _ _ k => checkNoCallInExpr bad (k ())
  | .store _ _ k => checkNoCallInExpr bad k
  | .call f (bs := bs) _ k => !bad.contains f && checkNoCallInExpr bad (k (Tup.units bs))
  | .jnz _ t e => checkNoCallInExpr bad t && checkNoCallInExpr bad e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => true
  | .group (sig := sig) bodies k =>
      checkNoCallInBlocks bad (bodies (Tup.units sig)) &&
      checkNoCallInExpr bad (k (Tup.units sig))

def checkNoCallInBlocks (bad : List Sym) {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Unit) rs sig → Bool
  | _, .nil => true
  | _, .cons b bs => checkNoCallInExpr bad (b (Tup.units _)) && checkNoCallInBlocks bad bs
end

/-- `Bool` check ensuring `fn` makes no direct call to any symbol in `bad`. -/
def noCallInFn (bad : List Sym) (fn : Fn) : Bool :=
  checkNoCallInExpr bad (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as))

/-- Single-pass checker that all functions in `fs` outside `skipNames` avoid calling `bad`. -/
def checkNoCallBad (skipNames bad : List Sym) (fs : List Fn) : Bool :=
  fs.all fun f => skipNames.contains f.name || noCallInFn bad f

/-- Single-pass `O(|M|)` callsOk checker skipping untouched base bodies and validating ONLY
inserted helpers (`befores`) and replacements (`repls`). -/
def checkPatchCallsOkAux (exits : List Sym) (repls : List Fn)
    (befores : List (Sym × List Fn)) : List SigEntry → List Fn → Bool
  | _, [] => true
  | allowed, f :: fs =>
    let ins := patchInsAt befores f
    let (allowed1, okIns) := ins.foldl
      (fun (acc, ok) g => (g.sig :: acc, ok && g.checkCallsOk acc exits))
      (allowed, true)
    let r? := repls.find? (·.name == f.name)
    let okCur := match r? with
      | some r => r.sig == f.sig && r.checkCallsOk allowed1 exits
      | none => true
    let curSig := match r? with | some r => r.sig | none => f.sig
    okIns && okCur && checkPatchCallsOkAux exits repls befores (curSig :: allowed1) fs

def checkPatchCallsOk (M : LeanQbe.T.Module) (repls : List Fn)
    (befores : List (Sym × List Fn)) : Bool :=
  checkPatchCallsOkAux M.exits repls befores (M.externs.map Extern.sig) M.fns

/-- Decidable structural equality on `Tup (Arg K) ts`. -/
def tupArgBeq : {ts : List Ty} → Tup (Arg K) ts → Tup (Arg K) ts → Bool
  | [], (), () => true
  | _ :: _, (a, as), (b, bs) => decide (a = b) && tupArgBeq as bs

/-- Decidable structural equality on `Op K ts`. -/
def opKBeq {ts : List Ty} (o₁ o₂ : Op K ts) : Bool :=
  match o₁, o₂ with
  | @Op.mk _ _ s1 c1 a1, @Op.mk _ _ s2 c2 a2 =>
    if h : s1 = s2 then
      decide ((h ▸ c1) = c2) && tupArgBeq (h ▸ a1) a2
    else false

mutual
/-- Structural equality on reified `TFlat rs` trees (no PHOAS binder sensitivity). -/
def tflatBeq {rs : List Ty} : TFlat rs → TFlat rs → Bool
  | @TFlat.let_ _ ts1 op1 k1, @TFlat.let_ _ ts2 op2 k2 =>
    if h : ts1 = ts2 then opKBeq (h ▸ op1) op2 && tflatBeq k1 k2 else false
  | .load t1 a1 k1, .load t2 a2 k2 =>
    t1 == t2 && decide (a1 = a2) && tflatBeq k1 k2
  | @TFlat.store _ t1 v1 a1 k1, @TFlat.store _ t2 v2 a2 k2 =>
    if h : t1 = t2 then decide ((h ▸ v1) = v2) && decide (a1 = a2) && tflatBeq k1 k2 else false
  | @TFlat.call _ f1 as1 bs1 args1 k1, @TFlat.call _ f2 as2 bs2 args2 k2 =>
    if ha : as1 = as2 then
      f1 == f2 && bs1 == bs2 && tupArgBeq (ha ▸ args1) args2 && tflatBeq k1 k2
    else false
  | .jnz c1 t1 e1, .jnz c2 t2 e2 =>
    decide (c1 = c2) && tflatBeq t1 t2 && tflatBeq e1 e2
  | @TFlat.jump _ ts1 j1 a1, @TFlat.jump _ ts2 j2 a2 =>
    if h : ts1 = ts2 then j1 == j2 && tupArgBeq (h ▸ a1) a2 else false
  | .ret v1, .ret v2 => tupArgBeq v1 v2
  | @TFlat.exit _ f1 as1 a1, @TFlat.exit _ f2 as2 a2 =>
    if h : as1 = as2 then f1 == f2 && tupArgBeq (h ▸ a1) a2 else false
  | .hlt, .hlt => true
  | @TFlat.group _ s1 b1 k1, @TFlat.group _ s2 b2 k2 =>
    if h : s1 = s2 then tblocksBeq (h ▸ b1) b2 && tflatBeq k1 k2 else false
  | _, _ => false

def tblocksBeq {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → TBlocks rs sig → Bool
  | _, .nil, .nil => true
  | _, .cons b1 bs1, .cons b2 bs2 => tflatBeq b1 b2 && tblocksBeq bs1 bs2
end

/-- Structural comparison of two `Fn` values via `reifyFunc` + `tflatBeq`. -/
def fnStructBeq (f₁ f₂ : Fn) : Bool :=
  if hr : f₁.rs = f₂.rs then
    f₁.name == f₂.name && f₁.as == f₂.as &&
    tflatBeq (reifyFunc f₁.body) (hr ▸ reifyFunc f₂.body)
  else false

/-- `Type 0` summary computed by `computeSplicePlan` for `splice_module!`. -/
structure SplicePlanData where
  slotIdxs : List Nat
  replSigs : List (Option SigEntry)
  baseLen : Nat
  replsLen : Nat
  beforesLen : Nat
  err? : Option String := none
  deriving Inhabited

/-- Pure evaluator computing slot indices, signatures, nodup, and callsOk checks for
`splice_module!`, returning `Type 0` metadata for `Meta.evalExpr`. -/
def computeSplicePlan (baseMod : LeanQbe.T.Module) (repls : List Fn)
    (befores : List (Sym × List Fn)) : SplicePlanData :=
  Id.run do
    let mut nameToSlot : Std.HashMap Sym (Nat × SigEntry) := {}
    let mut idx := 0
    for f in baseMod.fns do
      if !nameToSlot.contains f.name then
        nameToSlot := nameToSlot.insert f.name (idx, f.sig)
      idx := idx + 1
    let mut slotIdxs : List Nat := []
    let mut replSigs : List (Option SigEntry) := []
    for r in repls do
      match nameToSlot.get? r.name with
      | none =>
        return {
          slotIdxs := [], replSigs := [], baseLen := baseMod.fns.length,
          replsLen := repls.length, beforesLen := (befores.flatMap Prod.snd).length,
          err? := some s!"replacement `{r.name}` not found in base module"
        }
      | some (i, gsig) =>
        if r.sig != gsig then
          return {
            slotIdxs := [], replSigs := [], baseLen := baseMod.fns.length,
            replsLen := repls.length, beforesLen := (befores.flatMap Prod.snd).length,
            err? := some s!"signature mismatch on `{r.name}`: repl {repr r.sig} ≠ base {repr gsig}"
          }
        slotIdxs := slotIdxs ++ [i]
        replSigs := replSigs ++ [some r.sig]
    let patchedFns := patchFns repls befores baseMod.fns
    let patchedMod : LeanQbe.T.Module := { baseMod with fns := patchedFns }
    if !patchedMod.checkNamesNodup then
      return {
        slotIdxs, replSigs, baseLen := baseMod.fns.length, replsLen := repls.length,
        beforesLen := (befores.flatMap Prod.snd).length,
        err? := some "patched module has duplicate function/extern names"
      }
    if !checkPatchCallsOk baseMod repls befores then
      return {
        slotIdxs, replSigs, baseLen := baseMod.fns.length, replsLen := repls.length,
        beforesLen := (befores.flatMap Prod.snd).length,
        err? := some "patched functions/insertions fail checkPatchCallsOk"
      }
    return {
      slotIdxs, replSigs, baseLen := baseMod.fns.length, replsLen := repls.length,
      beforesLen := (befores.flatMap Prod.snd).length, err? := none
    }

/-- Pure evaluator finding maximal contiguous runs `(offA, offB, len)` of structurally
identical `Fn`s between `modA` and `modB` for `derive_reuse_bridge!`. -/
def computeReuseRuns (modA modB : LeanQbe.T.Module) : List (Nat × Nat × Nat) :=
  Id.run do
    let arrA := modA.fns.toArray
    let arrB := modB.fns.toArray
    let mut bPos : Std.HashMap Sym (Array Nat) := {}
    for j in [:arrB.size] do
      if hjb : j < arrB.size then
        let nm := arrB[j].name
        let cur := bPos.getD nm #[]
        bPos := bPos.insert nm (cur.push j)
    let mut runs : List (Nat × Nat × Nat) := []
    let mut i : Nat := 0
    while hia : i < arrA.size do
      let fA := arrA[i]
      let candidates := bPos.getD fA.name #[]
      let mut bestOffB? : Option Nat := none
      let mut bestLen : Nat := 0
      for j0 in candidates do
        if hj0 : j0 < arrB.size then
          if fnStructBeq fA arrB[j0] then
            let mut k : Nat := 1
            while hkA : i + k < arrA.size do
              if hkB : j0 + k < arrB.size then
                if fnStructBeq arrA[i + k] arrB[j0 + k] then
                  k := k + 1
                else
                  break
              else
                break
            if k > bestLen then
              bestLen := k
              bestOffB? := some j0
      match bestOffB? with
      | some j0 =>
        runs := runs ++ [(i, j0, bestLen)]
        i := i + bestLen
      | none =>
        i := i + 1
    return runs

/-- Assembly descriptor bundling a base verified `Module`, delta replacements `repls` / `replRows`,
optional `befores` / `beforeRows` helper insertions, and optional `rewiredRows` overrides. -/
structure PatchBundle where
  baseMod : LeanQbe.T.Module
  baseTable : List SpecEntry
  baseOk : LeanQbe.T.ModuleOk (Env.ofTable baseTable) baseMod
  repls : List Fn
  replRows : List SpecEntry
  befores : List (Sym × List Fn) := []
  beforeRows : List SpecEntry := []
  rewiredRows : List SpecEntry := []

def PatchBundle.patchedFns (b : PatchBundle) : List Fn :=
  patchFns b.repls b.befores b.baseMod.fns

def PatchBundle.patchedMod (b : PatchBundle) : LeanQbe.T.Module :=
  { b.baseMod with fns := b.patchedFns }

def PatchBundle.frontTable (b : PatchBundle) : List SpecEntry :=
  b.rewiredRows ++ b.replRows ++ b.beforeRows

def PatchBundle.frontNames (b : PatchBundle) : List Sym :=
  b.frontTable.map SpecEntry.name

/-- Patched specification environment giving head-first priority to `rewiredRows`, then
`replRows`, then `beforeRows`, falling back to `baseTable` for untouched base functions. -/
def patchEnv (b : PatchBundle) : Env :=
  Env.ofTable (b.frontTable ++ b.baseTable)

end

/-! ## 2. Splice Algebra, Checkers, and `PatchBundle` Lifting Proofs -/

public section

theorem patchFns_nil (repls fs : List Fn) : patchFns repls [] fs = spliceFns repls fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp [patchFns, spliceFns, patchInsAt] at ih ⊢
    exact ih

theorem spliceFns_append (repls fs₁ fs₂ : List Fn) :
    spliceFns repls (fs₁ ++ fs₂) = spliceFns repls fs₁ ++ spliceFns repls fs₂ := by
  simp [spliceFns, List.map_append]

theorem patchFns_append (repls : List Fn) (befores : List (Sym × List Fn)) (fs₁ fs₂ : List Fn) :
    patchFns repls befores (fs₁ ++ fs₂) =
      patchFns repls befores fs₁ ++ patchFns repls befores fs₂ := by
  simp [patchFns, List.flatMap_append]

/-- Extract a single slot's signature from one batched `slotSigs` equality. -/
theorem slotSig_at {xs : List Fn} {idxs : List Nat} {sigs : List (Option SigEntry)}
    (h : idxs.map (fun i => xs[i]?.map Fn.sig) = sigs) (k : Nat) :
    match idxs[k]?, sigs[k]? with
    | some idx, some sg => xs[idx]?.map Fn.sig = sg
    | _, _ => True := by
  have hk := congrArg (·[k]?) h
  cases hi : idxs[k]? with
  | none => trivial
  | some idx =>
    cases hs : sigs[k]? with
    | none => trivial
    | some sg =>
      simp only [List.getElem?_map, hi, hs, Option.map_some, Option.some.injEq] at hk
      exact hk

/-- Extract a single `(drop, take)` slice equality from one batched `reuse_eq` theorem. -/
theorem reuseSlice_at {fnsA fnsB : List Fn} {runs : List (Nat × Nat × Nat)}
    (h : runs.map (fun r => (fnsA.drop r.1).take r.2.2) =
         runs.map (fun r => (fnsB.drop r.2.1).take r.2.2))
    (k a b len : Nat) (hk : runs[k]? = some (a, b, len)) :
    (fnsA.drop a).take len = (fnsB.drop b).take len := by
  have hget := congrArg (·[k]?) h
  simpa [List.getElem?_map, hk] using hget

/-- Extract a single `Fn` equality inside a matched reuse slice. -/
theorem fn_eq_of_slice_eq {fnsA fnsB : List Fn} {a b len j : Nat}
    (hsl : (fnsA.drop a).take len = (fnsB.drop b).take len) (hj : j < len) :
    fnsA[a + j]? = fnsB[b + j]? := by
  have hget := congrArg (·[j]?) hsl
  simpa [List.getElem?_take, List.getElem?_drop, hj] using hget

private theorem checkSlotPlan_aux {baseFns repls : List Fn} {idxs : List Nat}
    (hlen : repls.length = idxs.length)
    (hzip : (repls.zip idxs).all (fun (p : Fn × Nat) =>
      match baseFns[p.2]? with
      | some (g : Fn) => p.1.name == g.name && p.1.sig == g.sig
      | none => false) = true) :
    ∀ r ∈ repls, ∃ (i : Nat) (g : Fn), baseFns[i]? = some g ∧ r.name = g.name ∧ r.sig = g.sig := by
  induction repls generalizing idxs with
  | nil => intro r hr; nomatch hr
  | cons r rs ih =>
    cases idxs with
    | nil => simp at hlen
    | cons i is =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hzip
      intro r' hr'
      rcases List.mem_cons.mp hr' with rfl | hmem
      · cases hg : baseFns[i]? with
        | none => simp [hg] at hzip
        | some g =>
          have hpair := hzip.1
          simp only [hg, Bool.and_eq_true, beq_iff_eq] at hpair
          exact ⟨i, g, hg, hpair.1, hpair.2⟩
      · exact ih hlen hzip.2 r' hmem

private theorem nodup_getElem?_inj {α : Type _} {xs : List α} (hnd : xs.Nodup)
    {i j : Nat} {a : α} (hi : xs[i]? = some a) (hj : xs[j]? = some a) : i = j := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons x xs ih =>
    have ⟨hnmem, hnd'⟩ := List.nodup_cons.mp hnd
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp at hi hj
        subst hi
        exact False.elim (hnmem (List.mem_iff_getElem?.mpr ⟨j, hj⟩))
    | succ i =>
      cases j with
      | zero =>
        simp at hi hj
        subst hj
        exact False.elim (hnmem (List.mem_iff_getElem?.mpr ⟨i, hi⟩))
      | succ j =>
        simp at hi hj
        exact congrArg Nat.succ (ih hnd' hi hj)

theorem replSigs_of_checkSlotPlan {baseFns repls : List Fn} {idxs : List Nat}
    (hnd : (baseFns.map Fn.name).Nodup)
    (hplan : checkSlotPlan baseFns repls idxs = true) :
    ∀ r ∈ repls, ∀ g ∈ baseFns, r.name = g.name → r.sig = g.sig := by
  simp only [checkSlotPlan, Bool.and_eq_true, beq_iff_eq] at hplan
  have hcov := checkSlotPlan_aux hplan.1 hplan.2
  intro r hr g hg heq
  obtain ⟨i, g0, hget, hrn, hrs⟩ := hcov r hr
  have hsame : g = g0 := by
    obtain ⟨kg, hkg⟩ := List.mem_iff_getElem?.mp hg
    have hm1 : (baseFns.map Fn.name)[kg]? = some g.name := by simp [List.getElem?_map, hkg]
    have hm2 : (baseFns.map Fn.name)[i]? = some g.name := by
      simp [List.getElem?_map, hget, ← heq, hrn]
    have hk_eq_i := nodup_getElem?_inj hnd hm1 hm2
    subst hk_eq_i
    rw [hget] at hkg
    exact (Option.some.inj hkg).symm
  subst hsame
  exact hrs

private theorem forall_wf_cons {f : Fn} {fs : List Fn} (hf : f.Wf) (hfs : ∀ g ∈ fs, g.Wf) :
    ∀ g ∈ f :: fs, g.Wf := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hmem
  · exact hf
  · exact hfs g hmem

theorem forall_wf_of_len_zero {xs : List Fn} (h : xs.length = 0) : ∀ f ∈ xs, f.Wf := by
  cases xs with
  | nil => intro _ hm; nomatch hm
  | cons _ _ => simp at h

theorem list_ne_nil_of_len_succ {α : Type _} {xs : List α} {n : Nat}
    (h : xs.length = n + 1) : xs ≠ [] := by
  intro heq; subst heq; simp at h

theorem forall_wf_of_cons_step {xs : List Fn} {n : Nat}
    (hlen : xs.length = n + 1)
    (hhd : (xs.head (list_ne_nil_of_len_succ hlen)).Wf)
    (htl : ∀ f ∈ xs.tail, f.Wf) :
    ∀ f ∈ xs, f.Wf := by
  cases xs with
  | nil => simp at hlen
  | cons _ _ => exact forall_wf_cons hhd htl

theorem patchFns_wf {repls fs : List Fn} {befores : List (Sym × List Fn)}
    (hfs : ∀ f ∈ fs, f.Wf)
    (hrepls : ∀ r ∈ repls, r.Wf)
    (hbefores : ∀ ins ∈ befores.flatMap Prod.snd, ins.Wf) :
    ∀ g ∈ patchFns repls befores fs, g.Wf := by
  intro g hg
  simp only [patchFns, List.mem_flatMap, List.mem_append, List.mem_singleton] at hg
  rcases hg with ⟨f, hf, hins | rfl⟩
  · unfold patchInsAt at hins
    split at hins
    · rename_i tgt ins hfind
      have hmem : (tgt, ins) ∈ befores := List.mem_of_find?_eq_some hfind
      exact hbefores g (List.mem_flatMap.mpr ⟨(tgt, ins), hmem, hins⟩)
    · nomatch hins
  · cases hfind : repls.find? (·.name == f.name) with
    | none => simp; exact hfs f hf
    | some r => simp; exact hrepls r (List.mem_of_find?_eq_some hfind)

/-! ### `callsOk` monotonicity and `noCallIn` transport -/

mutual
theorem expr_callsOk_mono {a₁ a₂ : List SigEntry} {exits : List Sym} {rs : List Ty}
    (hsub : ∀ s ∈ a₁, s ∈ a₂) :
    ∀ (e : Expr (fun _ => Unit) (fun _ => Unit) rs),
      e.callsOk a₁ exits → e.callsOk a₂ exits
  | .let_ _ k, h => expr_callsOk_mono hsub (k (Tup.units _)) h
  | .load _ _ k, h => expr_callsOk_mono hsub (k ()) h
  | .store _ _ k, h => expr_callsOk_mono hsub k h
  | .call _ _ _, h => ⟨hsub _ h.1, expr_callsOk_mono hsub _ h.2⟩
  | .jnz _ t e, h => ⟨expr_callsOk_mono hsub t h.1, expr_callsOk_mono hsub e h.2⟩
  | .jump _ _, h | .ret _, h | .exit _ _, h | .hlt, h => h
  | .group (sig := sig) bodies k, h =>
      ⟨blocks_callsOk_mono hsub (bodies (Tup.units sig)) h.1,
       expr_callsOk_mono hsub (k (Tup.units sig)) h.2⟩

theorem blocks_callsOk_mono {a₁ a₂ : List SigEntry} {exits : List Sym} {rs : List Ty}
    (hsub : ∀ s ∈ a₁, s ∈ a₂) :
    ∀ {sig : List (List Ty)} (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig),
      bs.callsOk a₁ exits → bs.callsOk a₂ exits
  | _, .nil, h => h
  | _, .cons b bs, h => ⟨expr_callsOk_mono hsub (b (Tup.units _)) h.1, blocks_callsOk_mono hsub bs h.2⟩
end

theorem fn_callsOk_mono {a₁ a₂ : List SigEntry} {exits : List Sym} {fn : Fn}
    (hsub : ∀ s ∈ a₁, s ∈ a₂) (h : fn.callsOk a₁ exits) : fn.callsOk a₂ exits :=
  expr_callsOk_mono hsub _ h

mutual
theorem expr_checkCallsOk_mono {a₁ a₂ : List SigEntry} {exits : List Sym} {rs : List Ty}
    (hsub : ∀ s ∈ a₁, s ∈ a₂) :
    ∀ (e : Expr (fun _ => Unit) (fun _ => Unit) rs),
      e.checkCallsOk a₁ exits = true → e.checkCallsOk a₂ exits = true
  | .let_ _ k, h => expr_checkCallsOk_mono hsub (k (Tup.units _)) h
  | .load _ _ k, h => expr_checkCallsOk_mono hsub (k ()) h
  | .store _ _ k, h => expr_checkCallsOk_mono hsub k h
  | .call f (as := as) (bs := bs) _ k, h => by
      simp only [Expr.checkCallsOk, Bool.and_eq_true, List.any_eq_true, SigEntry.beq_iff_eq] at h ⊢
      obtain ⟨⟨s, hs, rfl⟩, hk⟩ := h
      exact ⟨⟨(f, as, bs), hsub _ hs, rfl⟩, expr_checkCallsOk_mono hsub (k (Tup.units bs)) hk⟩
  | .jnz _ t e, h => by
      simp only [Expr.checkCallsOk, Bool.and_eq_true] at h ⊢
      exact ⟨expr_checkCallsOk_mono hsub t h.1, expr_checkCallsOk_mono hsub e h.2⟩
  | .jump _ _, h | .ret _, h | .exit _ _, h | .hlt, h => h
  | .group (sig := sig) bodies k, h => by
      simp only [Expr.checkCallsOk, Bool.and_eq_true] at h ⊢
      exact ⟨blocks_checkCallsOk_mono hsub (bodies (Tup.units sig)) h.1,
        expr_checkCallsOk_mono hsub (k (Tup.units sig)) h.2⟩

theorem blocks_checkCallsOk_mono {a₁ a₂ : List SigEntry} {exits : List Sym} {rs : List Ty}
    (hsub : ∀ s ∈ a₁, s ∈ a₂) :
    ∀ {sig : List (List Ty)} (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig),
      bs.checkCallsOk a₁ exits = true → bs.checkCallsOk a₂ exits = true
  | _, .nil, h => h
  | _, .cons b bs, h => by
      simp only [Blocks.checkCallsOk, Bool.and_eq_true] at h ⊢
      exact ⟨expr_checkCallsOk_mono hsub (b (Tup.units _)) h.1, blocks_checkCallsOk_mono hsub bs h.2⟩
end

theorem fn_checkCallsOk_mono {a₁ a₂ : List SigEntry} {exits : List Sym} {fn : Fn}
    (hsub : ∀ s ∈ a₁, s ∈ a₂) (h : fn.checkCallsOk a₁ exits = true) :
    fn.checkCallsOk a₂ exits = true :=
  expr_checkCallsOk_mono hsub _ h

mutual
theorem expr_callsOk_filter_noCallIn {allowed : List SigEntry} {exits : List Sym}
    {bad : List Sym} {rs : List Ty} :
    ∀ (e : Expr (fun _ => Unit) (fun _ => Unit) rs),
      e.callsOk allowed exits → checkNoCallInExpr bad e = true →
      e.callsOk (allowed.filter fun s => !bad.contains s.1) exits
  | .let_ _ k, hc, hn => expr_callsOk_filter_noCallIn (k (Tup.units _)) hc hn
  | .load _ _ k, hc, hn => expr_callsOk_filter_noCallIn (k ()) hc hn
  | .store _ _ k, hc, hn => expr_callsOk_filter_noCallIn k hc hn
  | .call f (as := as) (bs := bs) _ k, hc, hn => by
      simp only [Expr.callsOk] at hc ⊢
      simp only [checkNoCallInExpr, Bool.and_eq_true] at hn
      have hn1 : (!bad.contains (f, as, bs).1) = true := hn.1
      exact ⟨List.mem_filter.mpr ⟨hc.1, hn1⟩, expr_callsOk_filter_noCallIn (k (Tup.units bs)) hc.2 hn.2⟩
  | .jnz _ t e, hc, hn => by
      simp only [checkNoCallInExpr, Bool.and_eq_true] at hn
      exact ⟨expr_callsOk_filter_noCallIn t hc.1 hn.1, expr_callsOk_filter_noCallIn e hc.2 hn.2⟩
  | .jump _ _, hc, _ | .ret _, hc, _ | .exit _ _, hc, _ | .hlt, hc, _ => hc
  | .group (sig := sig) bodies k, hc, hn => by
      simp only [checkNoCallInExpr, Bool.and_eq_true] at hn
      exact ⟨blocks_callsOk_filter_noCallIn (bodies (Tup.units sig)) hc.1 hn.1,
        expr_callsOk_filter_noCallIn (k (Tup.units sig)) hc.2 hn.2⟩

theorem blocks_callsOk_filter_noCallIn {allowed : List SigEntry} {exits : List Sym}
    {bad : List Sym} {rs : List Ty} :
    ∀ {sig : List (List Ty)} (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig),
      bs.callsOk allowed exits → checkNoCallInBlocks bad bs = true →
      bs.callsOk (allowed.filter fun s => !bad.contains s.1) exits
  | _, .nil, hc, _ => hc
  | _, .cons b bs, hc, hn => by
      simp only [checkNoCallInBlocks, Bool.and_eq_true] at hn
      exact ⟨expr_callsOk_filter_noCallIn (b (Tup.units _)) hc.1 hn.1,
        blocks_callsOk_filter_noCallIn bs hc.2 hn.2⟩
end

theorem fn_wp_env_agree_of_noCallIn {Γ Γ' : Env} {allowed : List SigEntry}
    {exits bad : List Sym} {fn : Fn}
    (hwf : fn.Wf)
    (hcalls : fn.callsOk allowed exits)
    (hno : noCallInFn bad fn = true)
    (hagree : ∀ f as bs, (f, as, bs) ∈ allowed → f ∉ bad →
      ∀ xs m P E, Γ f as bs xs m P E → Γ' f as bs xs m P E)
    {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost} :
    Func.wp Γ fn.body xs m Q X → Func.wp Γ' fn.body xs m Q X := by
  have hcalls' : fn.callsOk (allowed.filter fun s => !bad.contains s.1) exits :=
    expr_callsOk_filter_noCallIn _ hcalls hno
  refine wp_env_agree_of_callsOk (hwf _ _ _ _ _ _) hcalls' ?_ m
  intro f as bs hmem
  rw [List.mem_filter] at hmem
  refine hagree f as bs hmem.1 ?_
  intro hbad
  have hc : bad.contains f = true := List.contains_iff_mem.mpr hbad
  have hnb : (!bad.contains f) = true := hmem.2
  rw [hc] at hnb
  cases hnb

/-! ### `Env.ofTable` prefix and override lookup lemmas -/

theorem env_ofTable_append_not_mem {pfx tbl : List SpecEntry} {f : Sym}
    (hf : ∀ e ∈ pfx, e.name ≠ f) (as rs : List Ty) :
    Env.ofTable (pfx ++ tbl) f as rs = Env.ofTable tbl f as rs := by
  induction pfx with
  | nil => rfl
  | cons e es ih =>
    have hne : e.name ≠ f := hf e (by simp)
    funext xs m Q X
    rw [List.cons_append, Env.ofTable_cons_ne hne]
    exact congrFun (congrFun (congrFun (congrFun (ih fun e' he' => hf e' (by simp [he'])) xs) m) Q) X

theorem env_ofTable_find?_of_append {pfx tbl : List SpecEntry} {f : Sym} {e : SpecEntry}
    (hfind : pfx.find? (·.name == f) = some e)
    {as rs : List Ty} (has : e.as = as) (hrs : e.rs = rs)
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Env.ofTable (pfx ++ tbl) f as rs xs m Q X) :
    e.cast has hrs xs m Q X := by
  induction pfx with
  | nil => simp at hfind
  | cons hd tl ih =>
    simp only [List.find?] at hfind
    by_cases hnm : (hd.name == f) = true
    · simp only [hnm, Option.some.injEq] at hfind
      subst hfind
      have heq : hd.name = f := beq_iff_eq.mp hnm
      subst heq
      rw [List.cons_append] at h
      rcases h with ⟨_, hcast⟩ | ⟨hne, _⟩
      · exact hcast
      · exact (hne ⟨rfl, has, hrs⟩).elim
    · have hne : hd.name ≠ f := by simp [beq_iff_eq] at hnm; exact hnm
      simp only [hnm] at hfind
      rw [List.cons_append, Env.ofTable_cons_ne hne] at h
      exact ih hfind h

theorem patchEnv_base_eq (b : PatchBundle) {f : Sym}
    (hf : b.frontTable.find? (·.name == f) = none) (as rs : List Ty) :
    patchEnv b f as rs = Env.ofTable b.baseTable f as rs := by
  refine env_ofTable_append_not_mem (fun e he heq => ?_) as rs
  have hmem := List.find?_eq_none.mp hf e he
  simp [heq] at hmem

/-! ### `patchFns` / `checkPatchCallsOk` structural correspondence -/

private theorem foldl_ins_sigs_eq {exits : List Sym} {ins : List Fn} {acc : List SigEntry}
    {ok0 : Bool} :
    ∀ {allowed : List SigEntry},
    (∀ s, s ∈ acc ↔ s ∈ allowed) →
    (∀ s, s ∈ (ins.foldl (fun p g => (g.sig :: p.1, p.2 && g.checkCallsOk p.1 exits))
      (acc, ok0)).1 ↔ s ∈ (ins.map Fn.sig ++ allowed)) := by
  induction ins generalizing acc ok0 with
  | nil => intro allowed h s; simpa using h s
  | cons g gs ih =>
    intro allowed h s
    simp only [List.foldl_cons, List.map_cons, List.cons_append]
    have hstep := @ih (g.sig :: acc) (ok0 && g.checkCallsOk acc exits) (g.sig :: allowed)
      (fun x => by simp [h x]) s
    simpa [List.mem_append, or_comm, or_left_comm, or_assoc] using hstep

private theorem foldl_ins_mem_ok {exits : List Sym} {ins : List Fn} :
    ∀ {acc allowed : List SigEntry} {ok0 : Bool},
    (∀ s, s ∈ acc ↔ s ∈ allowed) →
    (ins.foldl (fun p g => (g.sig :: p.1, p.2 && g.checkCallsOk p.1 exits))
      (acc, ok0)).2 = true →
    ok0 = true ∧ ∀ pre g post, ins = pre ++ g :: post →
      g.callsOk (pre.map Fn.sig ++ allowed) exits := by
  induction ins with
  | nil =>
    intro acc allowed ok0 _ hok
    exact ⟨hok, fun pre g post h => by cases pre <;> simp at h⟩
  | cons g gs ih =>
    intro acc allowed ok0 hmem hok
    simp only [List.foldl_cons] at hok
    have hnext := ih (acc := g.sig :: acc) (allowed := g.sig :: allowed)
      (ok0 := ok0 && g.checkCallsOk acc exits)
      (fun x => by simp [hmem x]) hok
    have hok0 : ok0 = true := (Bool.and_eq_true _ _ |>.mp hnext.1).1
    have hg_acc : g.checkCallsOk acc exits = true := (Bool.and_eq_true _ _ |>.mp hnext.1).2
    refine ⟨hok0, fun pre g' post hsplit => ?_⟩
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hsplit
      rcases hsplit with ⟨rfl, _⟩
      exact Fn.callsOk_of_checkCallsOk
        (fn_checkCallsOk_mono (fun s hs => (hmem s).mp hs) hg_acc)
    | cons x pre' =>
      simp only [List.cons_append, List.cons.injEq] at hsplit
      rcases hsplit with ⟨rfl, hrest⟩
      have hcall := hnext.2 pre' g' post hrest
      refine fn_callsOk_mono (fun s hs => ?_) hcall
      simp only [List.map_cons, List.mem_append, List.mem_cons] at hs ⊢
      rcases hs with h1 | rfl | h2
      · exact Or.inl (Or.inr h1)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr h2

private theorem drop_eq_cons_of_getElem? {α : Type _} {xs : List α} {i : Nat} {x : α}
    (hx : xs[i]? = some x) : xs.drop i = x :: xs.drop (i + 1) := by
  induction xs generalizing i with
  | nil => simp at hx
  | cons y ys ih =>
    cases i with
    | zero => simp at hx; simp [hx]
    | succ i => simp at hx ⊢; exact ih hx

private theorem split_append_cons {α : Type _} {xs : List α} {x y : α} {zs pre post : List α}
    (h : xs ++ y :: zs = pre ++ x :: post) :
    (∃ iPre iPost, xs = iPre ++ x :: iPost ∧ pre = iPre) ∨
    (x = y ∧ pre = xs) ∨
    (∃ tPre, zs = tPre ++ x :: post ∧ pre = xs ++ y :: tPre) := by
  by_cases hlt : pre.length < xs.length
  · have hpre_eq : pre = xs.take pre.length := by
      have ht := congrArg (List.take pre.length) h
      simpa [List.take_left', List.take_append_of_le_length (Nat.le_of_lt hlt)] using ht.symm
    have hget : xs[pre.length]? = some x := by
      have hg := congrArg (·[pre.length]?) h
      simpa [List.getElem?_append_left hlt] using hg
    have hx_split : xs = xs.take pre.length ++ x :: xs.drop (pre.length + 1) := by
      have hd := List.take_append_drop pre.length xs
      have hdrop : xs.drop pre.length = x :: xs.drop (pre.length + 1) :=
        drop_eq_cons_of_getElem? hget
      simpa [hdrop] using hd.symm
    exact Or.inl ⟨xs.take pre.length, xs.drop (pre.length + 1), hx_split, hpre_eq⟩
  · have hge : xs.length ≤ pre.length := Nat.not_lt.mp hlt
    by_cases heq : pre.length = xs.length
    · have hpre_eq : pre = xs := by
        have ht := congrArg (List.take pre.length) h
        simpa [List.take_left', heq] using ht.symm
      have hget : x = y := by
        have hg := congrArg (·[xs.length]?) h
        simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero] at hg
        have hg2 : (pre ++ x :: post)[pre.length]? = some x := by simp
        rw [← heq, hg2] at hg
        exact (Option.some.inj hg).symm
      exact Or.inr (Or.inl ⟨hget, hpre_eq⟩)
    · have hgt : xs.length < pre.length := Nat.lt_of_le_of_ne hge (Ne.symm heq)
      have htake_pre : pre.take (xs.length + 1) = xs ++ [y] := by
        have ht := congrArg (List.take (xs.length + 1)) h
        have hL : (xs ++ y :: zs).take (xs.length + 1) = xs ++ [y] := by
          have : xs ++ y :: zs = (xs ++ [y]) ++ zs := by simp [List.append_assoc]
          rw [this, List.take_left' (by simp)]
        have hR : (pre ++ x :: post).take (xs.length + 1) = pre.take (xs.length + 1) := by
          rw [List.take_append_of_le_length hgt]
        exact hR.symm.trans (ht.symm.trans hL)
      have hpre_eq : pre = xs ++ y :: pre.drop (xs.length + 1) := by
        have hd := List.take_append_drop (xs.length + 1) pre
        rw [htake_pre, List.append_assoc, List.singleton_append] at hd
        exact hd.symm
      rw [hpre_eq, List.append_assoc, List.cons_append] at h
      have h1 := List.append_cancel_left h
      have h2 := (List.cons.inj h1).2
      exact Or.inr (Or.inr ⟨pre.drop (xs.length + 1), h2, hpre_eq⟩)

private theorem patchFns_cons (repls : List Fn) (befores : List (Sym × List Fn))
    (f : Fn) (fs : List Fn) :
    patchFns repls befores (f :: fs) =
      patchInsAt befores f ++ [(repls.find? (·.name == f.name)).getD f] ++
        patchFns repls befores fs := by
  simp [patchFns]

private theorem patchFns_split_mem {repls : List Fn} {befores : List (Sym × List Fn)}
    {fs pre post : List Fn} {fn : Fn}
    (hsplit : patchFns repls befores fs = pre ++ fn :: post) :
    ∃ bPre f0 bPost, fs = bPre ++ f0 :: bPost ∧
      (∀ s ∈ bPre.map Fn.sig,
        (∀ r ∈ repls, ∀ g ∈ fs, r.name = g.name → r.sig = g.sig) → s ∈ pre.map Fn.sig) ∧
      ((∃ iPre iPost, patchInsAt befores f0 = iPre ++ fn :: iPost ∧
          ∀ s, s ∈ (patchFns repls befores bPre ++ iPre).map Fn.sig → s ∈ pre.map Fn.sig) ∨
       (fn = (repls.find? (·.name == f0.name)).getD f0 ∧
          ∀ s, s ∈ (patchFns repls befores bPre ++ patchInsAt befores f0).map Fn.sig →
            s ∈ pre.map Fn.sig)) := by
  induction fs generalizing pre with
  | nil => simp [patchFns] at hsplit
  | cons f fs ih =>
    rw [patchFns_cons, List.append_assoc, List.singleton_append] at hsplit
    rcases split_append_cons hsplit with
      ⟨iPre, iPost, hi, hpreEq⟩ | ⟨hr, rfl⟩ | ⟨preRest, htail, rfl⟩
    · subst hpreEq
      refine ⟨[], f, fs, rfl, fun _ h => by simp at h, Or.inl ⟨pre, iPost, hi, fun s hs => ?_⟩⟩
      simpa [patchFns] using hs
    · refine ⟨[], f, fs, rfl, fun _ h => by simp at h, Or.inr ⟨hr, fun s hs => ?_⟩⟩
      simpa [patchFns] using hs
    · obtain ⟨bPre', f0, bPost, hfs_eq, hsigPre, hcase⟩ := ih htail
      refine ⟨f :: bPre', f0, bPost, by rw [hfs_eq, List.cons_append], fun s hs hrepl => ?_, ?_⟩
      · simp only [List.map_cons, List.mem_cons] at hs
        rw [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
        rcases hs with rfl | hs'
        · right; left
          cases hf : repls.find? (·.name == f.name) with
          | none => rfl
          | some rf =>
            have hnm : rf.name = f.name := by simpa [beq_iff_eq] using List.find?_some hf
            exact (hrepl rf (List.mem_of_find?_eq_some hf) f (by simp) hnm).symm
        · exact Or.inr (Or.inr (hsigPre s hs' fun rf hrf g0 hg0 =>
            hrepl rf hrf g0 (by simp [hg0])))
      · rcases hcase with ⟨iPre, iPost, hi, hpreM⟩ | ⟨hr', hpreM⟩
        · refine Or.inl ⟨iPre, iPost, hi, fun s hs => ?_⟩
          rw [List.map_append, List.mem_append, patchFns_cons] at hs
          rw [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
          rcases hs with hA | h3
          · simp only [List.map_append, List.map_singleton, List.mem_append,
              List.mem_singleton] at hA
            rcases hA with (h1 | hcur) | h2
            · exact Or.inl h1
            · exact Or.inr (Or.inl hcur)
            · exact Or.inr (Or.inr (hpreM s (by rw [List.map_append, List.mem_append]; exact Or.inl h2)))
          · exact Or.inr (Or.inr (hpreM s (by rw [List.map_append, List.mem_append]; exact Or.inr h3)))
        · refine Or.inr ⟨hr', fun s hs => ?_⟩
          rw [List.map_append, List.mem_append, patchFns_cons] at hs
          rw [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
          rcases hs with hA | h3
          · simp only [List.map_append, List.map_singleton, List.mem_append,
              List.mem_singleton] at hA
            rcases hA with (h1 | hcur) | h2
            · exact Or.inl h1
            · exact Or.inr (Or.inl hcur)
            · exact Or.inr (Or.inr (hpreM s (by rw [List.map_append, List.mem_append]; exact Or.inl h2)))
          · exact Or.inr (Or.inr (hpreM s (by rw [List.map_append, List.mem_append]; exact Or.inr h3)))

private theorem checkPatchCallsOk_sound {exits : List Sym} {extSigs : List SigEntry}
    {repls : List Fn} {befores : List (Sym × List Fn)}
    {fs : List Fn} {seen acc : List SigEntry}
    (hacc : ∀ s, s ∈ acc ↔ s ∈ seen ++ extSigs)
    (hchk : checkPatchCallsOkAux exits repls befores acc fs = true) :
    ∀ bPre f0 bPost, fs = bPre ++ f0 :: bPost →
      (∀ iPre g iPost, patchInsAt befores f0 = iPre ++ g :: iPost →
        g.callsOk ((patchFns repls befores bPre).map Fn.sig ++ iPre.map Fn.sig ++ seen ++ extSigs) exits) ∧
      (∀ r, repls.find? (·.name == f0.name) = some r →
        r.sig = f0.sig ∧
        r.callsOk ((patchFns repls befores bPre).map Fn.sig ++
          (patchInsAt befores f0).map Fn.sig ++ seen ++ extSigs) exits) := by
  induction fs generalizing seen acc with
  | nil => intro bPre f0 bPost h; cases bPre <;> simp at h
  | cons f fs ih =>
    simp only [checkPatchCallsOkAux, Bool.and_eq_true] at hchk
    obtain ⟨⟨hokIns, hokCur⟩, hrest⟩ := hchk
    let ins := patchInsAt befores f
    let flds := ins.foldl (fun (acc, ok) g => (g.sig :: acc, ok && g.checkCallsOk acc exits))
      (acc, true)
    have hmem1 : ∀ s, s ∈ flds.1 ↔ s ∈ ins.map Fn.sig ++ seen ++ extSigs := by
      intro s
      have h := @foldl_ins_sigs_eq exits ins acc true (seen ++ extSigs) hacc s
      simpa [flds, List.mem_append, or_comm, or_left_comm, or_assoc] using h
    have hinsCalls := foldl_ins_mem_ok hacc hokIns
    let curSig := match repls.find? (·.name == f.name) with | some r => r.sig | none => f.sig
    have hmem2 : ∀ s, s ∈ (curSig :: flds.1) ↔
        s ∈ (ins.map Fn.sig ++ [curSig] ++ seen) ++ extSigs := by
      intro s
      simp [List.mem_cons, hmem1, List.mem_append, or_comm, or_left_comm, or_assoc]
    have hih := ih (seen := ins.map Fn.sig ++ [curSig] ++ seen) (acc := curSig :: flds.1)
      hmem2 hrest
    intro bPre f0 bPost hsplit
    cases bPre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hsplit
      rcases hsplit with ⟨rfl, rfl⟩
      constructor
      · intro iPre g iPost hi
        have hc := hinsCalls.2 iPre g iPost hi
        refine fn_callsOk_mono (fun s hs => ?_) hc
        simp only [patchFns, List.flatMap_nil, List.map_nil, List.nil_append,
          List.mem_append, or_assoc] at hs ⊢
        simpa [hacc] using hs
      · intro r hr
        simp only [hr, Bool.and_eq_true, beq_iff_eq] at hokCur
        refine ⟨hokCur.1, fn_callsOk_mono (fun s hs => ?_) (Fn.callsOk_of_checkCallsOk hokCur.2)⟩
        have hs' := (hmem1 s).mp hs
        simpa [patchFns, List.mem_append, or_comm, or_left_comm, or_assoc] using hs'
    | cons x bPre' =>
      simp only [List.cons_append, List.cons.injEq] at hsplit
      rcases hsplit with ⟨rfl, hrest_eq⟩
      have hsub := hih bPre' f0 bPost hrest_eq
      have hcur : ((repls.find? (·.name == f.name)).getD f).sig =
          (match repls.find? (·.name == f.name) with | some r => r.sig | none => f.sig) := by
        cases repls.find? (·.name == f.name) <;> rfl
      constructor
      · intro iPre g iPost hi
        refine fn_callsOk_mono (fun s hs => ?_) (hsub.1 iPre g iPost hi)
        rw [patchFns_cons]
        simp only [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton,
          hcur, or_assoc] at hs ⊢
        rcases hs with h1 | h2 | h3 | h4 | h5 | h6
        · exact Or.inr (Or.inr (Or.inl h1))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h2)))
        · exact Or.inl h3
        · exact Or.inr (Or.inl h4)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6))))
      · intro r hr
        refine ⟨(hsub.2 r hr).1, fn_callsOk_mono (fun s hs => ?_) (hsub.2 r hr).2⟩
        rw [patchFns_cons]
        simp only [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton,
          hcur, or_assoc] at hs ⊢
        rcases hs with h1 | h2 | h3 | h4 | h5 | h6
        · exact Or.inr (Or.inr (Or.inl h1))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h2)))
        · exact Or.inl h3
        · exact Or.inr (Or.inl h4)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6))))

/-- `O(1)` lift of `Module.checkAcyclic` for patched modules given base `M.checkAcyclic = true`
and `checkPatchCallsOk M repls befores = true` (zero re-verification of untouched base bodies). -/
theorem patchModule_checkAcyclic_fast {M : LeanQbe.T.Module} {repls : List Fn}
    {befores : List (Sym × List Fn)}
    (hBase : M.checkAcyclic = true)
    (hNodup : (patchModule M repls befores).checkNamesNodup = true)
    (hPatch : checkPatchCallsOk M repls befores = true)
    (hReplSigs : ∀ r ∈ repls, ∀ g ∈ M.fns, r.name = g.name → r.sig = g.sig) :
    (patchModule M repls befores).namesNodup ∧
    (∀ pre fn post, (patchModule M repls befores).fns = pre ++ fn :: post →
      fn.callsOk (pre.map Fn.sig ++ M.externs.map Extern.sig) M.exits) := by
  refine ⟨Module.namesNodup_of_checkNamesNodup hNodup, fun pre fn post hsplit => ?_⟩
  simp only [Module.checkAcyclic, Bool.and_eq_true] at hBase
  obtain ⟨bPre, f0, bPost, hfs, hPreSigs, hcase⟩ := patchFns_split_mem hsplit
  have hcallsOk_base := Module.checkFnsCallsOk_ok M.exits (M.externs.map Extern.sig) [] M.fns
    bPre f0 bPost hBase.2 (by simpa using hfs)
  have hpatch := checkPatchCallsOk_sound (extSigs := M.externs.map Extern.sig)
    (seen := []) (acc := M.externs.map Extern.sig)
    (fun s => by simp) hPatch bPre f0 bPost hfs
  rcases hcase with ⟨iPre, iPost, hi, hpreMem⟩ | ⟨hfn, hpreMem⟩
  · refine fn_callsOk_mono (fun s hs => ?_) (hpatch.1 iPre fn iPost hi)
    simp only [List.append_nil, List.mem_append] at hs ⊢
    rcases hs with h1 | h2
    · exact Or.inl (hpreMem s (by simpa [List.mem_append] using h1))
    · exact Or.inr h2
  · cases hr : repls.find? (·.name == f0.name) with
    | none =>
      simp [hr] at hfn
      subst hfn
      refine fn_callsOk_mono (fun s hs => ?_) (by simpa using hcallsOk_base)
      simp only [List.mem_append] at hs ⊢
      rcases hs with h1 | h2
      · exact Or.inl (hPreSigs s h1 fun r' hr' g0 hg0 => hReplSigs r' hr' g0 hg0)
      · exact Or.inr h2
    | some r =>
      have hcalls_r := (hpatch.2 r hr).2
      simp [hr] at hfn
      subst hfn
      refine fn_callsOk_mono (fun s hs => ?_) hcalls_r
      simp only [List.append_nil, List.mem_append] at hs ⊢
      rcases hs with h1 | h2
      · exact Or.inl (hpreMem s (by simpa [List.mem_append] using h1))
      · exact Or.inr h2

/-- Prove `ModuleOk (patchEnv b) b.patchedMod` cleanly for a `PatchBundle`, reusing `b.baseOk`
for all untouched base functions via `checkNoCallBad`/`noCallInFn` transport. -/
theorem patchBundle_moduleOk (b : PatchBundle)
    (hnodup : b.patchedMod.namesNodup)
    (hreplSigs : ∀ r ∈ b.repls, ∀ g ∈ b.baseMod.fns, r.name = g.name → r.sig = g.sig)
    (hnewWf : ∀ fn, (fn ∈ b.repls ∨ fn ∈ b.befores.flatMap Prod.snd) → fn.Wf)
    (hcalls : checkPatchCallsOk b.baseMod b.repls b.befores = true)
    (hfrontCovered : ∀ fn, (fn ∈ b.repls ∨ fn ∈ b.befores.flatMap Prod.snd) →
      (b.frontTable.find? (·.name == fn.name)).isSome = true)
    (hfrontImpl : ∀ fn e, fn ∈ b.patchedMod.fns →
      b.frontTable.find? (·.name == fn.name) = some e → SpecEntry.Impl (patchEnv b) fn e)
    (bad : List Sym)
    (hnoCallBad : ∀ fn ∈ b.baseMod.fns,
      b.repls.find? (·.name == fn.name) = none →
      b.frontTable.find? (·.name == fn.name) = none →
      noCallInFn bad fn = true)
    (hagree : ∀ s ∈ b.baseMod.sigs, s.1 ∉ bad →
      ∀ xs m P E, Env.ofTable b.baseTable s.1 s.2.1 s.2.2 xs m P E →
        patchEnv b s.1 s.2.1 s.2.2 xs m P E) :
    LeanQbe.T.ModuleOk (patchEnv b) b.patchedMod := by
  refine ⟨hnodup, fun pre fn post hsplit => ?_⟩
  have hfn_mem : fn ∈ b.patchedMod.fns := hsplit ▸ by simp
  obtain ⟨bPre, f0, bPost, hfs, hPreSigs, hcase⟩ := patchFns_split_mem hsplit
  have hf0_ok := b.baseOk.fnsOk bPre f0 bPost hfs
  have hpatch := checkPatchCallsOk_sound (extSigs := b.baseMod.externs.map Extern.sig)
    (seen := []) (acc := b.baseMod.externs.map Extern.sig)
    (fun s => by simp) hcalls bPre f0 bPost hfs
  have hwp_front : ∀ e, b.frontTable.find? (·.name == fn.name) = some e →
      ∀ xs m Q X, patchEnv b fn.name fn.as fn.rs xs m Q X → Func.wp (patchEnv b) fn.body xs m Q X := by
    intro e he xs m Q X hlookup
    obtain ⟨_, has_eq, hrs_eq⟩ := (hfrontImpl fn e hfn_mem he).1
    have hwp_e := (hfrontImpl fn e hfn_mem he).2
    have he_cast := env_ofTable_find?_of_append he has_eq hrs_eq hlookup
    exact hwp_e xs m Q X he_cast
  rcases hcase with ⟨iPre, iPost, hi, hpreMem⟩ | ⟨hfn, hpreMem⟩
  · have hins_mem : fn ∈ b.befores.flatMap Prod.snd := by
      have hmemIns : fn ∈ patchInsAt b.befores f0 := hi ▸ by simp
      unfold patchInsAt at hmemIns
      split at hmemIns
      · rename_i tgt ins hfind
        exact List.mem_flatMap.mpr ⟨(tgt, ins), List.mem_of_find?_eq_some hfind, hmemIns⟩
      · nomatch hmemIns
    have hwf_fn : fn.Wf := hnewWf fn (Or.inr hins_mem)
    have hcalls_fn : fn.callsOk (pre.map Fn.sig ++ b.baseMod.externs.map Extern.sig) b.baseMod.exits := by
      refine fn_callsOk_mono (fun s hs => ?_) (hpatch.1 iPre fn iPost hi)
      simp only [List.append_nil, List.mem_append] at hs ⊢
      rcases hs with h1 | h2
      · exact Or.inl (hpreMem s (by simpa [List.mem_append] using h1))
      · exact Or.inr h2
    have hsome := hfrontCovered fn (Or.inr hins_mem)
    cases hfind : b.frontTable.find? (·.name == fn.name) with
    | none => simp [hfind] at hsome
    | some e => exact ⟨hwf_fn, hcalls_fn, hwp_front e hfind⟩
  · cases hr : b.repls.find? (·.name == f0.name) with
    | some r =>
      have hcalls_r := (hpatch.2 r hr).2
      simp [hr] at hfn
      subst hfn
      have hfn_repl : fn ∈ b.repls := List.mem_of_find?_eq_some hr
      have hwf_fn : fn.Wf := hnewWf fn (Or.inl hfn_repl)
      have hcalls_fn : fn.callsOk (pre.map Fn.sig ++ b.baseMod.externs.map Extern.sig) b.baseMod.exits := by
        refine fn_callsOk_mono (fun s hs => ?_) hcalls_r
        simp only [List.append_nil, List.mem_append] at hs ⊢
        rcases hs with h1 | h2
        · exact Or.inl (hpreMem s (by simpa [List.mem_append] using h1))
        · exact Or.inr h2
      have hsome := hfrontCovered fn (Or.inl hfn_repl)
      cases hfind : b.frontTable.find? (·.name == fn.name) with
      | none => simp [hfind] at hsome
      | some e => exact ⟨hwf_fn, hcalls_fn, hwp_front e hfind⟩
    | none =>
      simp [hr] at hfn
      subst hfn
      have hf0_mem : fn ∈ b.baseMod.fns := hfs ▸ by simp
      have hwf_fn : fn.Wf := hf0_ok.1
      have hcalls_fn : fn.callsOk (pre.map Fn.sig ++ b.baseMod.externs.map Extern.sig) b.baseMod.exits := by
        refine fn_callsOk_mono (fun s hs => ?_) hf0_ok.2.1
        simp only [List.mem_append] at hs ⊢
        rcases hs with h1 | h2
        · exact Or.inl (hPreSigs s h1 hreplSigs)
        · exact Or.inr h2
      cases hfind : b.frontTable.find? (·.name == fn.name) with
      | some e => exact ⟨hwf_fn, hcalls_fn, hwp_front e hfind⟩
      | none =>
        refine ⟨hwf_fn, hcalls_fn, fun xs m Q X hlookup => ?_⟩
        rw [patchEnv_base_eq b hfind] at hlookup
        have hwp_base := hf0_ok.2.2 xs m Q X hlookup
        have hno := hnoCallBad fn hf0_mem hr hfind
        refine fn_wp_env_agree_of_noCallIn hwf_fn hf0_ok.2.1 hno (fun f as bs hmem hnb => ?_) hwp_base
        refine hagree (f, as, bs) ?_ hnb
        simp only [Module.sigs, List.mem_append, List.mem_map] at hmem ⊢
        rcases hmem with ⟨g, hg, hgsig⟩ | ⟨ex, hex, hexsig⟩
        · left; exact ⟨g, hfs ▸ List.mem_append_left _ hg, hgsig⟩
        · right; exact ⟨ex, hex, hexsig⟩

/-- Specialization of `patchBundle_moduleOk` where `bad := b.frontNames`: any callee not in
`b.frontNames` automatically has `patchEnv b = Env.ofTable b.baseTable` (`hagree` free). -/
theorem patchBundle_moduleOk_isolated (b : PatchBundle)
    (hnodup : b.patchedMod.namesNodup)
    (hreplSigs : ∀ r ∈ b.repls, ∀ g ∈ b.baseMod.fns, r.name = g.name → r.sig = g.sig)
    (hnewWf : ∀ fn, (fn ∈ b.repls ∨ fn ∈ b.befores.flatMap Prod.snd) → fn.Wf)
    (hcalls : checkPatchCallsOk b.baseMod b.repls b.befores = true)
    (hfrontCovered : ∀ fn, (fn ∈ b.repls ∨ fn ∈ b.befores.flatMap Prod.snd) →
      (b.frontTable.find? (·.name == fn.name)).isSome = true)
    (hfrontImpl : ∀ fn e, fn ∈ b.patchedMod.fns →
      b.frontTable.find? (·.name == fn.name) = some e → SpecEntry.Impl (patchEnv b) fn e)
    (hnoCallBad : checkNoCallBad (b.repls.map Fn.name ++ b.frontNames) b.frontNames b.baseMod.fns = true) :
    LeanQbe.T.ModuleOk (patchEnv b) b.patchedMod := by
  refine patchBundle_moduleOk b hnodup hreplSigs hnewWf hcalls hfrontCovered hfrontImpl
    b.frontNames (fun fn hmem hr hfind => ?_) (fun s _ hs => ?_)
  · have hcell : ((b.repls.map Fn.name ++ b.frontNames).contains fn.name ||
        noCallInFn b.frontNames fn) = true := by
      simp only [checkNoCallBad, List.all_eq_true] at hnoCallBad
      exact hnoCallBad fn hmem
    rcases (Bool.or_eq_true _ _).mp hcell with hskip | hok
    · rw [List.contains_iff_mem, List.mem_append] at hskip
      rcases hskip with hreplMem | hfrontMem
      · obtain ⟨r, hr', hrname⟩ := List.mem_map.mp hreplMem
        have hsome : (b.repls.find? (·.name == fn.name)).isSome = true :=
          List.find?_isSome.mpr ⟨r, hr', beq_iff_eq.mpr hrname⟩
        simp [hr] at hsome
      · obtain ⟨e, he, hename⟩ := List.mem_map.mp hfrontMem
        have hsome : (b.frontTable.find? (·.name == fn.name)).isSome = true :=
          List.find?_isSome.mpr ⟨e, he, beq_iff_eq.mpr hename⟩
        simp [hfind] at hsome
    · exact hok
  · have hnone : b.frontTable.find? (·.name == s.1) = none := by
      rw [List.find?_eq_none]
      intro e he hbeq
      exact hs (beq_iff_eq.mp hbeq ▸ List.mem_map_of_mem he)
    rw [patchEnv_base_eq b hnone]
    intro _ _ _ _ h; exact h

theorem module_fns_namesNodup {M : LeanQbe.T.Module} (h : M.namesNodup) :
    (M.fns.map Fn.name).Nodup :=
  (List.nodup_append.mp h).1

mutual
private theorem noCallInExpr_nil {rs : List Ty} :
    ∀ (e : Expr (fun _ => Unit) (fun _ => Unit) rs), checkNoCallInExpr [] e = true
  | .let_ _ k => noCallInExpr_nil (k (Tup.units _))
  | .load _ _ k => noCallInExpr_nil (k ())
  | .store _ _ k => noCallInExpr_nil k
  | .call _ (bs := bs) _ k => by
    simpa [checkNoCallInExpr] using noCallInExpr_nil (k (Tup.units bs))
  | .jnz _ t e => by
    simp only [checkNoCallInExpr, Bool.and_eq_true]
    exact ⟨noCallInExpr_nil t, noCallInExpr_nil e⟩
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => rfl
  | .group (sig := sig) bodies k => by
    simp only [checkNoCallInExpr, Bool.and_eq_true]
    exact ⟨noCallInBlocks_nil (bodies (Tup.units sig)), noCallInExpr_nil (k (Tup.units sig))⟩

private theorem noCallInBlocks_nil {rs : List Ty} :
    ∀ {sig : List (List Ty)} (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig),
      checkNoCallInBlocks [] bs = true
  | _, .nil => rfl
  | _, .cons b bs => by
    simp only [checkNoCallInBlocks, Bool.and_eq_true]
    exact ⟨noCallInExpr_nil (b (Tup.units _)), noCallInBlocks_nil bs⟩
end

/-- Specialization of `patchBundle_moduleOk` when overrides preserve base caller specs (`bad := []`),
so NO `noCallBad` exclusion scan is required. -/
theorem patchBundle_moduleOk_sameSpecs (b : PatchBundle)
    (hnodup : b.patchedMod.namesNodup)
    (hreplSigs : ∀ r ∈ b.repls, ∀ g ∈ b.baseMod.fns, r.name = g.name → r.sig = g.sig)
    (hnewWf : ∀ fn, (fn ∈ b.repls ∨ fn ∈ b.befores.flatMap Prod.snd) → fn.Wf)
    (hcalls : checkPatchCallsOk b.baseMod b.repls b.befores = true)
    (hfrontCovered : ∀ fn, (fn ∈ b.repls ∨ fn ∈ b.befores.flatMap Prod.snd) →
      (b.frontTable.find? (·.name == fn.name)).isSome = true)
    (hfrontImpl : ∀ fn e, fn ∈ b.patchedMod.fns →
      b.frontTable.find? (·.name == fn.name) = some e → SpecEntry.Impl (patchEnv b) fn e)
    (hagree : ∀ s ∈ b.baseMod.sigs,
      ∀ xs m P E, Env.ofTable b.baseTable s.1 s.2.1 s.2.2 xs m P E →
        patchEnv b s.1 s.2.1 s.2.2 xs m P E) :
    LeanQbe.T.ModuleOk (patchEnv b) b.patchedMod :=
  patchBundle_moduleOk b hnodup hreplSigs hnewWf hcalls hfrontCovered hfrontImpl []
    (fun _fn _ _ _ => noCallInExpr_nil _) (fun s hs _ => hagree s hs)

end

/-! ## 3. Meta Elaborators: `splice_module!` and `derive_reuse_bridge!` -/

public section

open Lean Meta Elab Command Term

private meta def addExposedDef (declNm : Name) (ty val : Lean.Expr) : CoreM Unit := do
  let decl := Declaration.defnDecl {
    name := declNm, levelParams := [], type := ty, value := val,
    hints := .abbrev, safety := .safe
  }
  addDecl decl (forceExpose := true)
  compileDecl decl
  enableRealizationsForConst declNm

private meta def addKernelThm (declNm : Name) (ty val : Lean.Expr) : CoreM Unit :=
  addDecl (Declaration.thmDecl {
    name := declNm, levelParams := [], type := ty, value := val
  })

private meta def mkKernelEqPair (lhs rhs : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let eqTy ← mkEq lhs rhs
  let reflPrf ← mkEqRefl lhs
  return (eqTy, reflPrf)

private meta partial def tyToExpr : Ty → Lean.Expr
  | .bool => Lean.mkConst ``Ty.bool
  | .bits n => mkApp (Lean.mkConst ``Ty.bits) (mkNatLit n)
  | .float .h => mkApp (Lean.mkConst ``Ty.float) (Lean.mkConst ``Fmt.h)
  | .float .s => mkApp (Lean.mkConst ``Ty.float) (Lean.mkConst ``Fmt.s)
  | .float .d => mkApp (Lean.mkConst ``Ty.float) (Lean.mkConst ``Fmt.d)
  | .float .q => mkApp (Lean.mkConst ``Ty.float) (Lean.mkConst ``Fmt.q)
  | .pair a b => mkApp2 (Lean.mkConst ``Ty.pair) (tyToExpr a) (tyToExpr b)

private meta def tyListToExpr (ts : List Ty) : Lean.Expr :=
  let tyC := Lean.mkConst ``Ty
  let nilE := mkApp (Lean.mkConst ``List.nil [.zero]) tyC
  ts.foldr (fun t acc => mkApp3 (Lean.mkConst ``List.cons [.zero]) tyC (tyToExpr t) acc) nilE

private meta def sigEntryToExpr (s : SigEntry) : Lean.Expr :=
  let tyC := Lean.mkConst ``Ty
  let listTyC := mkApp (Lean.mkConst ``List [.zero]) tyC
  let symC := Lean.mkConst ``LeanQbe.T.Sym
  let pairR := mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero])
    listTyC listTyC (tyListToExpr s.2.1) (tyListToExpr s.2.2)
  let pairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) listTyC listTyC
  mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) symC pairTy (mkStrLit s.1) pairR

private meta def mkOptionSigListExpr (sigs : List (Option SigEntry)) : Lean.Expr :=
  let sigC := Lean.mkConst ``LeanQbe.T.SigEntry
  let optC := mkApp (Lean.mkConst ``Option [.zero]) sigC
  let nilE := mkApp (Lean.mkConst ``List.nil [.zero]) optC
  sigs.foldr (init := nilE) fun sOpt acc =>
    let elE := match sOpt with
      | none => mkApp (Lean.mkConst ``Option.none [.zero]) sigC
      | some s => mkApp2 (Lean.mkConst ``Option.some [.zero]) sigC (sigEntryToExpr s)
    mkApp3 (Lean.mkConst ``List.cons [.zero]) optC elE acc

private meta def mkNatListExpr (ns : List Nat) : Lean.Expr :=
  let natTy := Lean.mkConst ``Nat
  let nilE := mkApp (Lean.mkConst ``List.nil [.zero]) natTy
  ns.foldr (fun n acc => mkApp3 (Lean.mkConst ``List.cons [.zero]) natTy (mkNatLit n) acc) nilE

private meta def mkRunListExpr (runs : List (Nat × Nat × Nat)) : Lean.Expr :=
  let natTy := Lean.mkConst ``Nat
  let p2Ty := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) natTy natTy
  let p3Ty := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) natTy p2Ty
  let nilE := mkApp (Lean.mkConst ``List.nil [.zero]) p3Ty
  runs.foldr (init := nilE) fun (a, b, len) acc =>
    let inner := mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) natTy natTy (mkNatLit b) (mkNatLit len)
    let outer := mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) natTy p2Ty (mkNatLit a) inner
    mkApp3 (Lean.mkConst ``List.cons [.zero]) p3Ty outer acc

private meta def proveFnWfByReify (fnE : Lean.Expr) : MetaM Lean.Expr := do
  let bodyE ← mkAppM ``LeanQbe.T.Fn.body #[fnE]
  let asE ← mkAppM ``LeanQbe.T.Fn.as #[fnE]
  let kTy := Lean.mkConst ``LeanQbe.T.K
  let klTy := Lean.mkConst ``LeanQbe.T.KL
  let lvlsE ← mkAppM ``LeanQbe.T.Tup.levels #[asE, mkNatLit 0]
  let rawE := mkAppN bodyE #[kTy, klTy, lvlsE]
  let lenE ← mkAppM ``List.length #[asE]
  let tflatE ← mkAppM ``LeanQbe.T.toTFlat #[rawE, lenE, mkNatLit 0]
  let vArrTy ← mkArrow (Lean.mkConst ``Ty) (mkSort Level.one)
  let listTyC ← mkAppM ``List #[Lean.mkConst ``Ty]
  let lArrTy ← mkArrow listTyC (mkSort Level.one)
  let rhsE ← withLocalDeclD `V vArrTy fun vF =>
    withLocalDeclD `L lArrTy fun lF => do
      let xsTy ← mkAppM ``Tup #[vF, asE]
      withLocalDeclD `xs xsTy fun xsF => do
        let sigVTy ← mkAppOptM ``Sigma #[some (Lean.mkConst ``Ty), some vF]
        let sigLTy ← mkAppOptM ``Sigma #[some listTyC, some lF]
        let emptyV ← mkAppOptM ``List.nil #[some sigVTy]
        let emptyL ← mkAppOptM ``List.nil #[some sigLTy]
        let pushed ← mkAppM ``LeanQbe.T.pushTup #[xsF, emptyV]
        let denoted ← mkAppM ``LeanQbe.T.denote #[vF, lF, tflatE, pushed, emptyL]
        mkLambdaFVars #[vF, lF, xsF] denoted
  let reflPrf ← mkEqRefl bodyE
  let eqPrf ← mkExpectedTypeHint reflPrf (← mkEq bodyE rhsE)
  mkAppM ``LeanQbe.T.Func.wf_of_reify #[eqPrf]

private meta partial def autoProveListWf (xsE : Lean.Expr) : Nat → MetaM Lean.Expr
  | 0 => do
    let lenE ← mkAppM ``List.length #[xsE]
    let eq0 ← mkExpectedTypeHint (← mkEqRefl lenE) (← mkEq lenE (mkNatLit 0))
    mkAppM ``forall_wf_of_len_zero #[eq0]
  | m + 1 => do
    let lenE ← mkAppM ``List.length #[xsE]
    let succE ← mkAppM ``Nat.succ #[mkNatLit m]
    let lenEq ← mkExpectedTypeHint (← mkEqRefl lenE) (← mkEq lenE succE)
    let nePrf ← mkAppM ``list_ne_nil_of_len_succ #[lenEq]
    let headTerm ← mkAppM ``List.head #[xsE, nePrf]
    let hdWf ← proveFnWfByReify headTerm
    let tlE ← mkAppM ``List.tail #[xsE]
    let tlWf ← autoProveListWf tlE m
    mkAppM ``forall_wf_of_cons_step #[lenEq, hdWf, tlWf]

private meta def parseSpliceOptions (keys : Array (TSyntax `ident)) (vals : Array Term) :
    CommandElabM (Option Term × Option Term × Option Term × Option Term × Option Term) := do
  let mut beforesT? : Option Term := none
  let mut baseWfT? : Option Term := none
  let mut baseAcT? : Option Term := none
  let mut replsWfT? : Option Term := none
  let mut beforesWfT? : Option Term := none
  for i in [:keys.size] do
    let k := keys[i]!.getId
    let v := vals[i]!
    if k == `befores then beforesT? := some v
    else if k == `baseWf then baseWfT? := some v
    else if k == `baseAcyclic then baseAcT? := some v
    else if k == `replsWf then replsWfT? := some v
    else if k == `beforesWf then beforesWfT? := some v
    else throwError "splice_module!: unknown option `{k}`"
  return (beforesT?, baseWfT?, baseAcT?, replsWfT?, beforesWfT?)

/-- `splice_module! <name> <baseMod> <repls> [(befores := ...)] [(baseWf := ...)] [(baseAcyclic := ...)] [(replsWf := ...)] [(beforesWf := ...)]`

Auto-computes slot indices matching `<repls>` in `<baseMod>.fns`, defines exposed
`<name>_fns`, `<name>`, `<name>_slotIdxs`, `<name>_replSigs`, emits ONE batched
`<name>_slotSigs` kernel `Eq.refl` theorem + `<name>_slotPlan` + `<name>_replSigs_ok`,
plus `<name>_names_nodup`, `<name>_wf`, and `<name>_acyclic` (or `<name>_fast_ok`). -/
syntax "splice_module! " ident term:arg term:arg ("(" ident " := " term ")")* : command

elab_rules : command
  | `(splice_module! $nameId $baseModT $replsT $[($optKeys := $optVals)]*) => do
    let ns ← getCurrNamespace
    let stem := nameId.getId.toString
    let mkNm (s : String) : Name := ns ++ Name.mkSimple s
    let fnsNm := mkNm (stem ++ "_fns")
    let modNm := ns ++ nameId.getId
    let slotIdxsNm := mkNm (stem ++ "_slotIdxs")
    let replSigsNm := mkNm (stem ++ "_replSigs")
    let slotSigsNm := mkNm (stem ++ "_slotSigs")
    let slotPlanNm := mkNm (stem ++ "_slotPlan")
    let replSigsOkNm := mkNm (stem ++ "_replSigs_ok")
    let checkNodupNm := mkNm (stem ++ "_checkNamesNodup")
    let namesNodupNm := mkNm (stem ++ "_names_nodup")
    let patchCallsNm := mkNm (stem ++ "_patchCallsOk")
    let wfNm := mkNm (stem ++ "_wf")
    let acyclicNm := mkNm (stem ++ "_acyclic")

    let (beforesT?, baseWfT?, baseAcT?, replsWfT?, beforesWfT?) ←
      parseSpliceOptions optKeys optVals

    let (modE, replsE, beforesE, plan, baseWfE?, baseAcE?, replsWfE?, beforesWfE?) ←
      liftTermElabM do
        let modTy := Lean.mkConst ``LeanQbe.T.Module
        let fnTy := Lean.mkConst ``LeanQbe.T.Fn
        let listFnTy ← mkAppM ``List #[fnTy]
        let befElemTy ← mkAppM ``Prod #[Lean.mkConst ``LeanQbe.T.Sym, listFnTy]
        let befTy ← mkAppM ``List #[befElemTy]
        let modE ← Term.elabTerm baseModT (some modTy)
        let replsE ← Term.elabTerm replsT (some listFnTy)
        let beforesE ← match beforesT? with
          | some bt => Term.elabTerm bt (some befTy)
          | none => mkAppOptM ``List.nil #[some befElemTy]
        Term.synthesizeSyntheticMVarsNoPostponing
        let modE ← instantiateMVars modE
        let replsE ← instantiateMVars replsE
        let beforesE ← instantiateMVars beforesE
        let planCallE ← mkAppM ``computeSplicePlan #[modE, replsE, beforesE]
        let plan ← unsafe Meta.evalExpr SplicePlanData
          (Lean.mkConst ``SplicePlanData) planCallE

        let baseWfE? ← baseWfT?.mapM fun t => do
          let baseFns ← mkAppM ``LeanQbe.T.Module.fns #[modE]
          let ty ← withLocalDeclD `f fnTy fun fF => do
            let m ← mkAppM ``Membership.mem #[baseFns, fF]
            let w ← mkAppM ``LeanQbe.T.Fn.Wf #[fF]
            mkForallFVars #[fF] (← mkArrow m w)
          Term.elabTerm t (some ty)
        let baseAcE? ← baseAcT?.mapM fun t => do
          let lhs ← mkAppM ``LeanQbe.T.Module.checkAcyclic #[modE]
          let ty ← mkEq lhs (Lean.mkConst ``Bool.true)
          Term.elabTerm t (some ty)
        let replsWfE? ← replsWfT?.mapM fun t => do
          let ty ← withLocalDeclD `r fnTy fun rF => do
            let m ← mkAppM ``Membership.mem #[replsE, rF]
            let w ← mkAppM ``LeanQbe.T.Fn.Wf #[rF]
            mkForallFVars #[rF] (← mkArrow m w)
          Term.elabTerm t (some ty)
        let beforesWfE? ← beforesWfT?.mapM fun t => do
          let sndFn ← withLocalDeclD `p befElemTy fun pF => do
            mkLambdaFVars #[pF] (← mkAppM ``Prod.snd #[pF])
          let flatBef ← mkAppM ``List.flatMap #[sndFn, beforesE]
          let ty ← withLocalDeclD `ins fnTy fun insF => do
            let m ← mkAppM ``Membership.mem #[flatBef, insF]
            let w ← mkAppM ``LeanQbe.T.Fn.Wf #[insF]
            mkForallFVars #[insF] (← mkArrow m w)
          Term.elabTerm t (some ty)
        Term.synthesizeSyntheticMVarsNoPostponing
        return (modE, replsE, beforesE, plan, baseWfE?, baseAcE?, replsWfE?, beforesWfE?)

    if let some err := plan.err? then
      throwError "splice_module!: {err}"

    -- Phase 1: emit exposed data defs (`_fns`, `<name>`, `_slotIdxs`, `_replSigs`).
    let (fnsVal, fnsTy, modVal, modTy, slotIdxsVal, listNatTy, replSigsVal, listOptSigTy) ←
      liftTermElabM do
        let fnTy := Lean.mkConst ``LeanQbe.T.Fn
        let listFnTy ← mkAppM ``List #[fnTy]
        let baseFnsE ← mkAppM ``LeanQbe.T.Module.fns #[modE]
        let fnsVal ← mkAppM ``patchFns #[replsE, beforesE, baseFnsE]
        let extsE ← mkAppM ``LeanQbe.T.Module.externs #[modE]
        let exitsE ← mkAppM ``LeanQbe.T.Module.exits #[modE]
        let modVal := mkApp3 (Lean.mkConst ``LeanQbe.T.Module.mk)
          (Lean.mkConst fnsNm) extsE exitsE
        let listNatTy ← mkAppM ``List #[Lean.mkConst ``Nat]
        let slotIdxsVal := mkNatListExpr plan.slotIdxs
        let optSigTy ← mkAppM ``Option #[Lean.mkConst ``LeanQbe.T.SigEntry]
        let listOptSigTy ← mkAppM ``List #[optSigTy]
        let replSigsVal := mkOptionSigListExpr plan.replSigs
        return (fnsVal, listFnTy, modVal, Lean.mkConst ``LeanQbe.T.Module,
          slotIdxsVal, listNatTy, replSigsVal, listOptSigTy)

    liftCoreM do
      addExposedDef fnsNm fnsTy fnsVal
      addExposedDef modNm modTy modVal
      addExposedDef slotIdxsNm listNatTy slotIdxsVal
      addExposedDef replSigsNm listOptSigTy replSigsVal

    -- Phase 2: emit batched kernel checks and structural theorems.
    let declPairs ← liftTermElabM do
      let baseFnsE ← mkAppM ``LeanQbe.T.Module.fns #[modE]
      let slotMapFn ← withLocalDeclD `i (Lean.mkConst ``Nat) fun iF => do
        let getE ← mkAppM ``GetElem?.getElem? #[baseFnsE, iF]
        let body ← mkAppM ``Option.map #[Lean.mkConst ``LeanQbe.T.Fn.sig, getE]
        mkLambdaFVars #[iF] body
      let slotMapLhs ← mkAppM ``List.map #[slotMapFn, Lean.mkConst slotIdxsNm]
      let (slotSigsTy, slotSigsPrf) ← mkKernelEqPair slotMapLhs (Lean.mkConst replSigsNm)

      let planLhs ← mkAppM ``checkSlotPlan #[baseFnsE, replsE, Lean.mkConst slotIdxsNm]
      let (slotPlanTy, slotPlanPrf) ← mkKernelEqPair planLhs (Lean.mkConst ``Bool.true)

      let checkNodupLhs ← mkAppM ``LeanQbe.T.Module.checkNamesNodup #[Lean.mkConst modNm]
      let (checkNodupTy, checkNodupPrf) ← mkKernelEqPair checkNodupLhs (Lean.mkConst ``Bool.true)

      let patchCallsLhs ← mkAppM ``checkPatchCallsOk #[modE, replsE, beforesE]
      let (patchCallsTy, patchCallsPrf) ← mkKernelEqPair patchCallsLhs (Lean.mkConst ``Bool.true)

      return #[(slotSigsNm, slotSigsTy, slotSigsPrf),
        (slotPlanNm, slotPlanTy, slotPlanPrf),
        (checkNodupNm, checkNodupTy, checkNodupPrf),
        (patchCallsNm, patchCallsTy, patchCallsPrf)]

    liftCoreM do
      for (nm, ty, prf) in declPairs do
        addKernelThm nm ty prf

    -- Phase 3: derive `_names_nodup`, `_wf`, `_replSigs_ok`, `_acyclic` cleanly.
    let derivedThms ← liftTermElabM do
      let fnTy := Lean.mkConst ``LeanQbe.T.Fn
      let baseFnsE ← mkAppM ``LeanQbe.T.Module.fns #[modE]
      let nodupPrf ← mkAppM ``LeanQbe.T.Module.namesNodup_of_checkNamesNodup #[Lean.mkConst checkNodupNm]
      let nodupTy ← inferType nodupPrf

      let wfGoalTy (xsE : Lean.Expr) : MetaM Lean.Expr :=
        withLocalDeclD `f fnTy fun fF => do
          let m ← mkAppM ``Membership.mem #[xsE, fF]
          let w ← mkAppM ``LeanQbe.T.Fn.Wf #[fF]
          mkForallFVars #[fF] (← mkArrow m w)
      let baseWfE ← match baseWfE? with
        | some e => pure e
        | none => autoProveListWf baseFnsE plan.baseLen
      let replsWfE ← match replsWfE? with
        | some e => pure e
        | none => autoProveListWf replsE plan.replsLen
      let listFnTy ← mkAppM ``List #[fnTy]
      let befElemTy ← mkAppM ``Prod #[Lean.mkConst ``LeanQbe.T.Sym, listFnTy]
      let sndFn ← withLocalDeclD `p befElemTy fun pF => do
        mkLambdaFVars #[pF] (← mkAppM ``Prod.snd #[pF])
      let flatBefE ← mkAppM ``List.flatMap #[sndFn, beforesE]
      let beforesWfE ← match beforesWfE? with
        | some e => pure e
        | none => autoProveListWf flatBefE plan.beforesLen
      let patchWfPrf ← mkAppM ``patchFns_wf #[baseWfE, replsWfE, beforesWfE]
      let wfTy ← wfGoalTy (Lean.mkConst fnsNm)

      let baseChkLhs ← mkAppM ``LeanQbe.T.Module.checkNamesNodup #[modE]
      let baseChkTy ← mkEq baseChkLhs (Lean.mkConst ``Bool.true)
      let baseChkPrf ← mkExpectedTypeHint (← mkEqRefl baseChkLhs) baseChkTy
      let baseNodupPrf ← mkAppM ``LeanQbe.T.Module.namesNodup_of_checkNamesNodup #[baseChkPrf]
      let baseFnsNodup ← mkAppM ``module_fns_namesNodup #[baseNodupPrf]
      let replSigsOkPrf ← mkAppM ``replSigs_of_checkSlotPlan #[baseFnsNodup, Lean.mkConst slotPlanNm]
      let replSigsOkTy ← inferType replSigsOkPrf

      return #[
        (namesNodupNm, nodupTy, nodupPrf),
        (wfNm, wfTy, patchWfPrf),
        (replSigsOkNm, replSigsOkTy, replSigsOkPrf)
      ]

    liftCoreM do
      for (nm, ty, prf) in derivedThms do
        addKernelThm nm ty prf

    let acThms ← liftTermElabM do
      let mut thms : Array (Name × Lean.Expr × Lean.Expr) := #[]
      match baseAcE? with
      | some baseAcE =>
        let fastPrf ← mkAppM ``patchModule_checkAcyclic_fast
          #[baseAcE, Lean.mkConst checkNodupNm, Lean.mkConst patchCallsNm, Lean.mkConst replSigsOkNm]
        let fastNm := mkNm (stem ++ "_fast_ok")
        thms := thms.push (fastNm, ← inferType fastPrf, fastPrf)
        if plan.baseLen ≤ 64 then
          let acLhs ← mkAppM ``LeanQbe.T.Module.checkAcyclic #[Lean.mkConst modNm]
          let (acTy, acPrf) ← mkKernelEqPair acLhs (Lean.mkConst ``Bool.true)
          thms := thms.push (acyclicNm, acTy, acPrf)
        else
          thms := thms.push (acyclicNm, ← inferType fastPrf, fastPrf)
      | none =>
        let acLhs ← mkAppM ``LeanQbe.T.Module.checkAcyclic #[Lean.mkConst modNm]
        let (acTy, acPrf) ← mkKernelEqPair acLhs (Lean.mkConst ``Bool.true)
        thms := thms.push (acyclicNm, acTy, acPrf)
      return thms

    liftCoreM do
      for (nm, ty, prf) in acThms do
        addKernelThm nm ty prf

/-- `derive_reuse_bridge! <bridgeName> <modA> <modB>`

Evaluates `modA.fns` and `modB.fns`, identifies all maximal contiguous runs `(offA, offB, len)`
of structurally identical `Fn`s (via `reifyFunc` + `tflatBeq`), and emits:
* `<bridgeName>_runs : List (Nat × Nat × Nat)`
* `<bridgeName>_lhsSlices`, `<bridgeName>_rhsSlices`
* `<bridgeName>_eq : <bridgeName>_lhsSlices = <bridgeName>_rhsSlices` (single batched kernel `Eq.refl`)
* `<bridgeName>_slice_k` per-slice projection theorems. -/
syntax "derive_reuse_bridge! " ident term:arg term:arg : command

elab_rules : command
  | `(derive_reuse_bridge! $bridgeId $modAT $modBT) => do
    let ns ← getCurrNamespace
    let stem := bridgeId.getId.toString
    let mkNm (s : String) : Name := ns ++ Name.mkSimple s
    let runsNm := mkNm (stem ++ "_runs")
    let lhsNm := mkNm (stem ++ "_lhsSlices")
    let rhsNm := mkNm (stem ++ "_rhsSlices")
    let eqNm := mkNm (stem ++ "_eq")

    let (modAE, modBE, runs) ← liftTermElabM do
      let modTy := Lean.mkConst ``LeanQbe.T.Module
      let modAE ← Term.elabTerm modAT (some modTy)
      let modBE ← Term.elabTerm modBT (some modTy)
      Term.synthesizeSyntheticMVarsNoPostponing
      let modAE ← instantiateMVars modAE
      let modBE ← instantiateMVars modBE
      let runsCall ← mkAppM ``computeReuseRuns #[modAE, modBE]
      let natTy := Lean.mkConst ``Nat
      let p2Ty ← mkAppM ``Prod #[natTy, natTy]
      let runTy ← mkAppM ``Prod #[natTy, p2Ty]
      let listRunTy ← mkAppM ``List #[runTy]
      let runs ← unsafe Meta.evalExpr (List (Nat × Nat × Nat)) listRunTy runsCall
      return (modAE, modBE, runs)

    let (runsVal, listRunTy, modAE, modBE) ← liftTermElabM do
      let natTy := Lean.mkConst ``Nat
      let p2Ty ← mkAppM ``Prod #[natTy, natTy]
      let runTy ← mkAppM ``Prod #[natTy, p2Ty]
      let listRunTy ← mkAppM ``List #[runTy]
      let runsVal := mkRunListExpr runs
      return (runsVal, listRunTy, modAE, modBE)

    liftCoreM <| addExposedDef runsNm listRunTy runsVal

    let (lhsVal, rhsVal, listListFnTy) ← liftTermElabM do
      let fnTy := Lean.mkConst ``LeanQbe.T.Fn
      let listFnTy ← mkAppM ``List #[fnTy]
      let listListFnTy ← mkAppM ``List #[listFnTy]
      let natTy := Lean.mkConst ``Nat
      let p2Ty ← mkAppM ``Prod #[natTy, natTy]
      let runTy ← mkAppM ``Prod #[natTy, p2Ty]
      let fnsAE ← mkAppM ``LeanQbe.T.Module.fns #[modAE]
      let fnsBE ← mkAppM ``LeanQbe.T.Module.fns #[modBE]
      let mkSliceMapper (fnsExpr : Lean.Expr) (useSecond : Bool) : MetaM Lean.Expr :=
        withLocalDeclD `r runTy fun rF => do
          let offE ←
            if !useSecond then mkAppM ``Prod.fst #[rF]
            else mkAppM ``Prod.fst #[← mkAppM ``Prod.snd #[rF]]
          let lenE ← mkAppM ``Prod.snd #[← mkAppM ``Prod.snd #[rF]]
          let dropE ← mkAppM ``List.drop #[offE, fnsExpr]
          let takeE ← mkAppM ``List.take #[lenE, dropE]
          mkLambdaFVars #[rF] takeE
      let lhsMap ← mkSliceMapper fnsAE false
      let rhsMap ← mkSliceMapper fnsBE true
      let lhsVal ← mkAppM ``List.map #[lhsMap, Lean.mkConst runsNm]
      let rhsVal ← mkAppM ``List.map #[rhsMap, Lean.mkConst runsNm]
      return (lhsVal, rhsVal, listListFnTy)

    liftCoreM do
      addExposedDef lhsNm listListFnTy lhsVal
      addExposedDef rhsNm listListFnTy rhsVal

    let (eqTy, eqPrf) ← liftTermElabM <|
      mkKernelEqPair (Lean.mkConst lhsNm) (Lean.mkConst rhsNm)
    liftCoreM <| addKernelThm eqNm eqTy eqPrf

    let sliceThms ← liftTermElabM do
      let mut out : Array (Name × Lean.Expr × Lean.Expr) := #[]
      let mut k : Nat := 0
      for (a, b, len) in runs do
        if k < 128 then
          let pairE ← mkAppM ``Prod.mk #[mkNatLit b, mkNatLit len]
          let tripleE ← mkAppM ``Prod.mk #[mkNatLit a, pairE]
          let getE ← mkAppM ``GetElem?.getElem? #[Lean.mkConst runsNm, mkNatLit k]
          let hkPrf ← mkEqRefl getE
          let hkTy ← mkEq getE (← mkAppM ``Option.some #[tripleE])
          let hkTyped ← mkExpectedTypeHint hkPrf hkTy
          let slPrf ← mkAppM ``reuseSlice_at
            #[Lean.mkConst eqNm, mkNatLit k, mkNatLit a, mkNatLit b, mkNatLit len, hkTyped]
          let sliceNm := mkNm (s!"{stem}_slice_{k}")
          out := out.push (sliceNm, ← inferType slPrf, slPrf)
        k := k + 1
      return out

    liftCoreM do
      for (nm, ty, prf) in sliceThms do
        addKernelThm nm ty prf

end

end LeanQbe.T.Examples.Kissat.PatchModule
