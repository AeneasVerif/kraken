module

public import LeanQbe.T.Logic.CanonicalEnv
public import LeanQbe.T.FlatLemmas
meta import Lean.Elab.Command

/-!
# Unit Tests & 410-Function Kernel Timing Gate for `CanonicalEnv`

1. Unit tests covering:
   - `Env.Has` definitional compatibility with standard `∀ xs m Q X, S xs m Q X → Γ …` hypotheses
     and `Env.Has.of_le` (`Spec.Le.refl`, `Spec.Le.trans`).
   - `Spec.or` & `Spec.iUnion` multi-mode specs (`Spec.impl_or`, `Spec.impl_iUnion`,
     `Spec.le_or_left`, `Spec.le_or_right`, `Spec.le_iUnion`), `Spec.XFree` (`xfree`,
     `Spec.XFree.or`, `Spec.XFree.iUnion`), and `Env.ofTable_noExit` / `has_of_noExit_false`.
   - `Env.override` (`Env.Has.override_new`, `Env.Has.override_old`, `Env.Sat.override_new`,
     `Env.Sat.override_old`, `Env.override_pos`, `Env.override_neg`).
   - Multi-segment `SegCert` composition (`TableImpl.append`, `TableImpl.append_sigs`,
     `AllFns.of_forall`, `AllFns.append`) and assembly via `ModuleOk.ofCanonical`,
     `ModuleOk.ofCanonicalSigs`, and `ModuleOk.ofCanonicalTrie`.
2. Mandatory `CS0` kernel timing gate:
   - Synthetic `410`-function acyclic module (`40` segments: `30×10 + 10×11`) with ~`1,900`
     cross-segment call edges and `410`-row canonical spec table, measuring `trace.profiler`
     elaboration & kernel times for `ModuleOk.ofCanonical`, `ModuleOk.ofCanonicalTrie`, `Nodup`,
     and `Env.Sat.ofTable` lookup.
3. `#print axioms` audit (`<= std3`, single line `< 115c`).
-/

set_option autoImplicit false

namespace LeanQbeTest.T.CanonicalEnvTest

open LeanQbe.T

/-! ## 1. Toy Multi-Segment Module: `Env.Has`, `Spec.or`, `Spec.iUnion`, `SegCert` -/

public section

/-- Leaf function: returns `x + 1`. -/
@[expose] def incFn : Fn :=
  ⟨"inc", [i64], [i64], fun _ _ (x, ()) =>
    .let_ (op2 (.add i64) (.var x) (.imm 1#64)) fun (y, ()) => .ret (.var y, ())⟩

/-- Multi-mode function: if `mode = 0`, returns `x + 10`; otherwise returns `x + x`. -/
@[expose] def modeFn : Fn :=
  ⟨"mode", [i64, i64], [i64], fun _ _ (md, x, ()) =>
    .let_ (op2 (.eq i64) (.var md) (.imm 0#64)) fun (c, ()) =>
    .jnz (.var c)
      (.let_ (op2 (.add i64) (.var x) (.imm 10#64)) fun (y, ()) => .ret (.var y, ()))
      (.let_ (op2 (.add i64) (.var x) (.var x)) fun (y, ()) => .ret (.var y, ()))⟩

/-- Caller in Segment 1 using mode 0 of `modeFn` and `incFn`. -/
@[expose] def call0Fn : Fn :=
  ⟨"call0", [i64], [i64], fun _ _ (x, ()) =>
    .call "inc" (as := [i64]) (bs := [i64]) (.var x, ()) fun (y, ()) =>
    .call "mode" (as := [i64, i64]) (bs := [i64]) (.imm 0#64, .var y, ()) fun (z, ()) =>
    .ret (.var z, ())⟩

/-- Caller in Segment 1 using mode 1 of `modeFn`. -/
@[expose] def call1Fn : Fn :=
  ⟨"call1", [i64], [i64], fun _ _ (x, ()) =>
    .call "mode" (as := [i64, i64]) (bs := [i64]) (.imm 1#64, .var x, ()) fun (z, ()) =>
    .ret (.var z, ())⟩

@[expose] def incSpec : Spec [i64] [i64] :=
  fun (x, ()) m Q _ => Q (x + 1#64, ()) m

@[expose] def incWeakSpec : Spec [i64] [i64] :=
  fun (x, ()) m Q _ => ∃ y, y = x + 1#64 ∧ Q (y, ()) m

@[expose] def mode0Spec : Spec [i64, i64] [i64] :=
  fun (md, x, ()) m Q _ => md = 0#64 ∧ Q (x + 10#64, ()) m

@[expose] def mode1Spec : Spec [i64, i64] [i64] :=
  fun (md, x, ()) m Q _ => md ≠ 0#64 ∧ Q (x + x, ()) m

@[expose] def modeSpec : Spec [i64, i64] [i64] :=
  Spec.or mode0Spec mode1Spec

@[expose] def modeIdxSpec : Bool → Spec [i64, i64] [i64]
  | true => mode0Spec
  | false => mode1Spec

@[expose] def call0Spec : Spec [i64] [i64] :=
  fun (x, ()) m Q _ => Q (x + 1#64 + 10#64, ()) m

@[expose] def call1Spec : Spec [i64] [i64] :=
  fun (x, ()) m Q _ => Q (x + x, ()) m

@[expose] def incRow : SpecEntry := ⟨"inc", [i64], [i64], incSpec, true⟩
@[expose] def modeRow : SpecEntry := ⟨"mode", [i64, i64], [i64], modeSpec, true⟩
@[expose] def call0Row : SpecEntry := ⟨"call0", [i64], [i64], call0Spec, true⟩
@[expose] def call1Row : SpecEntry := ⟨"call1", [i64], [i64], call1Spec, true⟩

@[expose] def seg0Fns : List Fn := [incFn, modeFn]
@[expose] def seg0Specs : List SpecEntry := [incRow, modeRow]
@[expose] def seg1Fns : List Fn := [call0Fn, call1Fn]
@[expose] def seg1Specs : List SpecEntry := [call0Row, call1Row]

@[expose] def toyFns : List Fn := seg0Fns ++ seg1Fns
@[expose] def toyTbl : List SpecEntry := seg0Specs ++ seg1Specs
@[expose] def toyMod : LeanQbe.T.Module := ⟨toyFns, [], []⟩

theorem seg0_sigs : seg0Specs.map SpecEntry.sig = seg0Fns.map Fn.sig := rfl
theorem seg1_sigs : seg1Specs.map SpecEntry.sig = seg1Fns.map Fn.sig := rfl
theorem toy_sigs : toyTbl.map SpecEntry.sig = toyFns.map Fn.sig := rfl

theorem inc_mem : incRow ∈ seg0Specs := .head _
theorem mode_mem : modeRow ∈ seg0Specs := .tail _ (.head _)
theorem call0_mem : call0Row ∈ seg1Specs := .head _
theorem call1_mem : call1Row ∈ seg1Specs := .tail _ (.head _)

theorem inc_xfree : Spec.XFree incSpec := by xfree
theorem mode_xfree : Spec.XFree modeSpec :=
  Spec.XFree.or (by xfree) (by xfree)
theorem iunion_xfree : Spec.XFree (Spec.iUnion modeIdxSpec) :=
  Spec.XFree.iUnion fun b => by cases b <;> xfree

theorem seg0_has_inc {Γ : Env} (h : Γ.Sat seg0Specs) : Γ.Has "inc" incSpec :=
  h.has inc_mem inc_xfree

theorem seg0_has_mode {Γ : Env} (h : Γ.Sat seg0Specs) : Γ.Has "mode" modeSpec :=
  h.has mode_mem mode_xfree

theorem inc_weak_le : incWeakSpec.Le incSpec := by
  rintro ⟨x, ⟨⟩⟩ m Q X ⟨y, rfl, hQ⟩
  exact hQ

theorem inc_wf : Fn.Wf incFn := by t_wf_reify
theorem mode_wf : Fn.Wf modeFn := by t_wf_reify
theorem call0_wf : Fn.Wf call0Fn := by t_wf_reify
theorem call1_wf : Fn.Wf call1Fn := by t_wf_reify

theorem inc_wp (Γ : Env) :
    ∀ a m Q X, incSpec a m Q X → Func.wp Γ incFn.body a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  dsimp only [Func.wp, incFn]
  t_wp_unfold
  exact hQ

theorem mode0_wp (Γ : Env) :
    ∀ a m Q X, mode0Spec a m Q X → Func.wp Γ modeFn.body a m Q X := by
  rintro ⟨md, x, ⟨⟩⟩ m Q X ⟨rfl, hQ⟩
  dsimp only [Func.wp, modeFn]
  t_wp_unfold
  exact hQ

theorem mode1_wp (Γ : Env) :
    ∀ a m Q X, mode1Spec a m Q X → Func.wp Γ modeFn.body a m Q X := by
  rintro ⟨md, x, ⟨⟩⟩ m Q X ⟨hne, hQ⟩
  dsimp only [Func.wp, modeFn]
  t_wp_unfold
  exact ⟨fun h => absurd h hne, fun _ => hQ⟩

theorem mode_wp (Γ : Env) :
    ∀ a m Q X, modeSpec a m Q X → Func.wp Γ modeFn.body a m Q X :=
  Spec.impl_or (mode0_wp Γ) (mode1_wp Γ)

theorem mode_iunion_wp (Γ : Env) :
    ∀ a m Q X, Spec.iUnion modeIdxSpec a m Q X → Func.wp Γ modeFn.body a m Q X :=
  Spec.impl_iUnion fun b => match b with
    | true => mode0_wp Γ
    | false => mode1_wp Γ

/-- Definitional compatibility: `call0_wp` uses a raw `∀ xs m Q X, ...` callee hyp
for `"inc"` and `Γ.Has` for `"mode"`, yet both are interchangeable. -/
theorem call0_wp (Γ : Env)
    (hInc : ∀ xs m Q X, incWeakSpec xs m Q X → Γ "inc" [i64] [i64] xs m Q X)
    (hMode : Γ.Has "mode" mode0Spec) :
    ∀ a m Q X, call0Spec a m Q X → Func.wp Γ call0Fn.body a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  simp only [Func.wp, call0Fn, wp, vals, Arg.val]
  refine ⟨fun (y, ()) m' => y = x + 1#64 ∧ m' = m, fun _ _ _ _ => False,
    hInc _ _ _ _ ⟨x + 1#64, rfl, rfl, rfl⟩, ?_, fun _ _ _ _ h => h.elim⟩
  rintro ⟨y, ⟨⟩⟩ m1 ⟨rfl, hm1⟩
  subst hm1
  refine ⟨fun (z, ()) m2 => z = x + 1#64 + 10#64 ∧ m2 = m1, fun _ _ _ _ => False,
    hMode _ _ _ _ ⟨rfl, rfl, rfl⟩, ?_, fun _ _ _ _ h => h.elim⟩
  rintro ⟨z, ⟨⟩⟩ m2 ⟨rfl, hm2⟩
  subst hm2
  exact hQ

theorem call1_wp (Γ : Env) (hMode : Γ.Has "mode" mode1Spec) :
    ∀ a m Q X, call1Spec a m Q X → Func.wp Γ call1Fn.body a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  simp only [Func.wp, call1Fn, wp, vals, Arg.val]
  refine ⟨fun (z, ()) m' => z = x + x ∧ m' = m, fun _ _ _ _ => False,
    hMode _ _ _ _ ⟨by decide, rfl, rfl⟩, ?_, fun _ _ _ _ h => h.elim⟩
  rintro ⟨z, ⟨⟩⟩ m' ⟨rfl, rfl⟩
  exact hQ

theorem seg0_cert : SegCert [] seg0Fns seg0Specs := fun Γ _ _ =>
  ⟨.of (inc_wp Γ), .of (mode_wp Γ), trivial⟩

theorem seg1_cert : SegCert seg0Specs seg1Fns seg1Specs := fun Γ hd _ =>
  ⟨.of (call0_wp Γ ((seg0_has_inc hd).of_le inc_weak_le)
      ((seg0_has_mode hd).of_le Spec.le_or_left)),
   .of (call1_wp Γ ((seg0_has_mode hd).of_le Spec.le_or_right)),
   trivial⟩

theorem toy_wf : AllFns Fn.Wf toyMod.fns :=
  AllFns.append ⟨inc_wf, mode_wf, trivial⟩ ⟨call0_wf, call1_wf, trivial⟩

theorem toy_acyc : toyMod.checkAcyclic = true := by t_kernel_rfl
theorem toy_trie : toyMod.checkAcyclicTrie = true := by t_kernel_rfl

theorem toy_ok : ModuleOk (Env.ofTable toyTbl) toyMod :=
  ModuleOk.ofCanonical toy_acyc toy_wf rfl fun Γ h =>
    TableImpl.append (seg0_cert Γ (.nil Γ) h.left) rfl (seg1_cert Γ h.left h.right)

theorem toy_sigs_ok : ModuleOk (Env.ofTable toyTbl) toyMod :=
  ModuleOk.ofCanonicalSigs toy_acyc toy_wf toy_sigs fun Γ h =>
    TableImpl.append_sigs (seg0_cert Γ (.nil Γ) h.left) seg0_sigs (seg1_cert Γ h.left h.right)

theorem toy_trie_ok : ModuleOk (Env.ofTable toyTbl) toyMod :=
  ModuleOk.ofCanonicalTrie toy_trie toy_wf rfl fun Γ h =>
    TableImpl.append (seg0_cert Γ (.nil Γ) h.left) rfl (seg1_cert Γ h.left h.right)

theorem toy_noExit : ∀ f as bs xs m Q X X',
    Env.ofTable toyTbl f as bs xs m Q X → Env.ofTable toyTbl f as bs xs m Q X' :=
  Env.ofTable_noExit (by simp [toyTbl, seg0Specs, seg1Specs, incRow, modeRow, call0Row, call1Row])

theorem toy_has_mode0 : (Env.ofTable toyTbl).Has "mode" mode0Spec :=
  have hnd : (toyTbl.map SpecEntry.name).Nodup := nodup_of_checkAcyclic toy_acyc rfl
  (seg0_has_mode (Env.Sat.ofTable hnd fun _ h => h).left).of_le Spec.le_or_left

theorem toy_has_mode1 : (Env.ofTable toyTbl).Has "mode" mode1Spec :=
  have hnd : (toyTbl.map SpecEntry.name).Nodup := nodup_of_checkAcyclicTrie toy_trie rfl
  (seg0_has_mode (Env.Sat.ofTable hnd fun _ h => h).left).of_le Spec.le_or_right

/-! ## 2. `Env.override` & `noExit := false` Capability Tests -/

@[expose] def incPlus2Spec : Spec [i64] [i64] :=
  fun (x, ()) m Q _ => Q (x + 2#64, ()) m

@[expose] def incNewRow : SpecEntry := ⟨"inc", [i64], [i64], incPlus2Spec, false⟩

theorem override_sat_new :
    (Env.override ["inc"] (Env.ofTable [incNewRow]) (Env.ofTable toyTbl)).Sat [incNewRow] :=
  Env.Sat.override_new
    (Env.Sat.ofTable (by decide) fun _ h => h)
    (fun e he => by simp only [List.mem_singleton] at he; subst he; decide)

theorem override_sat_mode :
    (Env.override ["inc"] (Env.ofTable [incNewRow]) (Env.ofTable toyTbl)).Sat [modeRow] :=
  Env.Sat.override_old
    (Env.Sat.ofTable (nodup_of_checkAcyclic toy_acyc rfl) fun _ h =>
      List.mem_append_left _ (List.mem_cons_of_mem _ h))
    (fun e he => by simp only [List.mem_singleton] at he; subst he; decide)

theorem override_ok :
    (Env.override ["inc"] (Env.ofTable [incNewRow]) (Env.ofTable toyTbl)).Has "inc" incPlus2Spec ∧
    (Env.override ["inc"] (Env.ofTable [incNewRow]) (Env.ofTable toyTbl)).Has "mode" modeSpec :=
  ⟨override_sat_new.has_of_noExit_false (.head _) rfl,
   override_sat_mode.has (.head _) mode_xfree⟩

theorem iunion_ok :
    ∀ a m Q X, Spec.iUnion modeIdxSpec a m Q X →
      Func.wp (Env.ofTable toyTbl) modeFn.body a m Q X :=
  mode_iunion_wp _

/-! ## 3. Mandatory `CS0` Kernel Timing Gate (`410` Functions / `40` Segments) -/

open Lean Elab Command in
/-- Generate a `410`-function acyclic DAG (`40` segments: `30×10 + 10×11`) with up to `5`
cross-segment call edges per function (~`1,900` total edges), proving `Fn.Wf`, `f_wp`, `mem`,
`has`, `SegCert`, `checkAcyclicTrie`, `nodup_of_checkAcyclicTrie`, `ModuleOk.ofCanonical`,
`ModuleOk.ofCanonicalTrie`, and `Env.Sat.ofTable` lookups under `set_option trace.profiler true`. -/
elab "gen_410_gate " pfx:ident sizes:num* : command => do
  let ns := pfx.getId.toString
  let segSizes := sizes.toList.map (·.getNat)
  let total := segSizes.foldl (· + ·) 0
  let offsets := [1, 7, 19, 43, 97]
  let mut fnSeg : Array Nat := #[]
  for segIdx in [:segSizes.length] do
    for _ in [:segSizes[segIdx]!] do
      fnSeg := fnSeg.push segIdx

  let mut globalIdx := 0
  let mut segDeps : Array (Array Nat) := #[]
  for segIdx in [:segSizes.length] do
    let cnt := segSizes[segIdx]!
    let startIdx := globalIdx
    let mut depsSet : Array Nat := #[]
    for _ in [:cnt] do
      let i := globalIdx
      let fnNm := mkIdent (Name.mkSimple s!"{ns}_fn_{i}")
      let wfNm := mkIdent (Name.mkSimple s!"{ns}_wf_{i}")
      let specNm := mkIdent (Name.mkSimple s!"{ns}_spec_{i}")
      let rowNm := mkIdent (Name.mkSimple s!"{ns}_row_{i}")
      let wpNm := mkIdent (Name.mkSimple s!"{ns}_wp_{i}")
      let symLit := Syntax.mkStrLit s!"{ns}_f_{i}"
      let callees := offsets.filterMap fun d => if i >= d then some (i - d) else none
      for c in callees do
        let cs := fnSeg[c]!
        if cs < segIdx && !depsSet.contains cs then
          depsSet := depsSet.push cs

      let mut bodyStx ← `(term| .ret (.var x.1, ()))
      let mut wfBodyStx ← `(term| Wf.ret (TRel.cons' (ArgRel.var (.head _)) .nil'))
      for c in callees.reverse do
        let cSym := Syntax.mkStrLit s!"{ns}_f_{c}"
        bodyStx ← `(term| .call $cSym (as := [i64]) (bs := [i64]) (.var x.1, ()) fun x => $bodyStx)
        wfBodyStx ← `(term|
          Wf.call $cSym (TRel.cons' (ArgRel.var (.head _)) .nil') fun _ _ => $wfBodyStx)
      elabCommand (← `(command|
        @[expose] def $fnNm : Fn := ⟨$symLit, [i64], [i64], fun _ _ x => $bodyStx⟩))
      elabCommand (← `(command|
        theorem $wfNm : Fn.Wf $fnNm := fun _ _ _ _ _ _ => $wfBodyStx))
      elabCommand (← `(command|
        @[expose] def $specNm : Spec [i64] [i64] :=
          fun (_x, ()) _m Q _ => ∀ r m', Q (r, ()) m'))
      elabCommand (← `(command|
        @[expose] def $rowNm : SpecEntry := ⟨$symLit, [i64], [i64], $specNm, true⟩))

      let mut binders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) := #[]
      let mut termStx ← `(term| hQ _ _)
      for idx in [:callees.length] do
        let c := callees[idx]!
        let hId := mkIdent (Name.mkSimple s!"hc_{idx}")
        let cSym := Syntax.mkStrLit s!"{ns}_f_{c}"
        let cSpec := mkIdent (Name.mkSimple s!"{ns}_spec_{c}")
        binders := binders.push (← `(bracketedBinder| ($hId : Γ.Has $cSym $cSpec)))
      for idx in [:callees.length] do
        let revIdx := callees.length - 1 - idx
        let hId := mkIdent (Name.mkSimple s!"hc_{revIdx}")
        termStx ← `(term| ⟨_, fun _ _ _ _ => False, $hId _ _ _ _ (fun _ _ => $termStx),
          fun _ _ h => h, fun _ _ _ _ h => False.elim h⟩)
      elabCommand (← `(command|
        theorem $wpNm (Γ : Env) $binders:bracketedBinder* :
            ∀ a m Q X, $specNm a m Q X → Func.wp Γ ($fnNm).body a m Q X :=
          fun (_, ()) _ _ _ hQ => $termStx))
      globalIdx := globalIdx + 1

    segDeps := segDeps.push depsSet
    let segFnsNm := mkIdent (Name.mkSimple s!"{ns}_seg{segIdx}_fns")
    let segSpecsNm := mkIdent (Name.mkSimple s!"{ns}_seg{segIdx}_specs")
    let segCertNm := mkIdent (Name.mkSimple s!"{ns}_seg{segIdx}_cert")
    let fnElems : Array Term := (Array.range cnt).map fun k =>
      mkIdent (Name.mkSimple s!"{ns}_fn_{startIdx + k}")
    let rowElems : Array Term := (Array.range cnt).map fun k =>
      mkIdent (Name.mkSimple s!"{ns}_row_{startIdx + k}")
    elabCommand (← `(command| @[expose] def $segFnsNm : List Fn := [$fnElems,*]))
    elabCommand (← `(command| @[expose] def $segSpecsNm : List SpecEntry := [$rowElems,*]))

    for k in [:cnt] do
      let i := startIdx + k
      let memNm := mkIdent (Name.mkSimple s!"{ns}_mem_{i}")
      let hasNm := mkIdent (Name.mkSimple s!"{ns}_has_{i}")
      let rowNm := mkIdent (Name.mkSimple s!"{ns}_row_{i}")
      let specNm := mkIdent (Name.mkSimple s!"{ns}_spec_{i}")
      let symLit := Syntax.mkStrLit s!"{ns}_f_{i}"
      let mut memProof ← `(term| List.Mem.head _)
      for _ in [:k] do
        memProof ← `(term| List.Mem.tail _ $memProof)
      elabCommand (← `(command| theorem $memNm : $rowNm ∈ $segSpecsNm := $memProof))
      elabCommand (← `(command| theorem $hasNm {Γ : Env} (h : Γ.Sat $segSpecsNm) :
          Γ.Has $symLit $specNm := h.has $memNm (by xfree)))

    let depsList := depsSet.toList
    let mut depsTerm : Term ← `(term| ([] : List SpecEntry))
    if !depsList.isEmpty then
      let last := depsList.getLast!
      depsTerm := mkIdent (Name.mkSimple s!"{ns}_seg{last}_specs")
      for d in depsList.dropLast.reverse do
        let dSpecs := mkIdent (Name.mkSimple s!"{ns}_seg{d}_specs")
        depsTerm ← `(term| $dSpecs ++ $depsTerm)

    let mut implTerm ← `(term| True.intro)
    for kRev in [:cnt] do
      let k := cnt - 1 - kRev
      let i := startIdx + k
      let wpNm := mkIdent (Name.mkSimple s!"{ns}_wp_{i}")
      let callees := offsets.filterMap fun d => if i >= d then some (i - d) else none
      let mut callArgs : Array Term := #[]
      for c in callees do
        let hasNm := mkIdent (Name.mkSimple s!"{ns}_has_{c}")
        let cs := fnSeg[c]!
        if cs == segIdx then
          callArgs := callArgs.push (← `(term| $hasNm hs))
        else
          let pos := depsList.idxOf cs
          let mut proj ← `(term| hd)
          for _ in [:pos] do
            proj ← `(term| Env.Sat.right $proj)
          if pos + 1 < depsList.length then
            proj ← `(term| Env.Sat.left $proj)
          callArgs := callArgs.push (← `(term| $hasNm $proj))
      let item ← `(term| SpecEntry.Impl.of ($wpNm Γ $callArgs*))
      implTerm ← `(term| ⟨$item, $implTerm⟩)
    elabCommand (← `(command|
      theorem $segCertNm : SegCert $depsTerm $segFnsNm $segSpecsNm :=
        fun Γ hd hs => $implTerm))

  let numSegs := segSizes.length
  let mut allFnsTerm : Term := mkIdent (Name.mkSimple s!"{ns}_seg{numSegs - 1}_fns")
  let mut allSpecsTerm : Term := mkIdent (Name.mkSimple s!"{ns}_seg{numSegs - 1}_specs")
  for idx in [:numSegs - 1] do
    let s := numSegs - 2 - idx
    let sf := mkIdent (Name.mkSimple s!"{ns}_seg{s}_fns")
    let ss := mkIdent (Name.mkSimple s!"{ns}_seg{s}_specs")
    allFnsTerm ← `(term| $sf ++ $allFnsTerm)
    allSpecsTerm ← `(term| $ss ++ $allSpecsTerm)

  let fnsNm := mkIdent (Name.mkSimple s!"{ns}_fns")
  let tblNm := mkIdent (Name.mkSimple s!"{ns}_tbl")
  let modNm := mkIdent (Name.mkSimple s!"{ns}_mod")
  let wfAllNm := mkIdent (Name.mkSimple s!"{ns}_all_wf")
  let trieNm := mkIdent (Name.mkSimple s!"{ns}_trie")
  let namesNm := mkIdent (Name.mkSimple s!"{ns}_names")
  let nodupNm := mkIdent (Name.mkSimple s!"{ns}_nodup")
  let okNm := mkIdent (Name.mkSimple s!"{ns}_ok")
  let canonNm := mkIdent (Name.mkSimple s!"{ns}_canon")
  let sat0Nm := mkIdent (Name.mkSimple s!"{ns}_sat0")
  let satLastNm := mkIdent (Name.mkSimple s!"{ns}_sat{total - 1}")

  elabCommand (← `(command| @[expose] def $fnsNm : List Fn := $allFnsTerm))
  elabCommand (← `(command| @[expose] def $tblNm : List SpecEntry := $allSpecsTerm))
  elabCommand (← `(command| @[expose] def $modNm : LeanQbe.T.Module := ⟨$fnsNm, [], []⟩))

  for s in [:numSegs] do
    let segWfNm := mkIdent (Name.mkSimple s!"{ns}_seg{s}_wf")
    let segFnsNm := mkIdent (Name.mkSimple s!"{ns}_seg{s}_fns")
    let startS := (segSizes.take s).foldl (· + ·) 0
    let cnt := segSizes[s]!
    let mut t ← `(term| True.intro)
    for kRev in [:cnt] do
      let i := startS + (cnt - 1 - kRev)
      let wfi := mkIdent (Name.mkSimple s!"{ns}_wf_{i}")
      t ← `(term| ⟨$wfi, $t⟩)
    elabCommand (← `(command| theorem $segWfNm : AllFns Fn.Wf $segFnsNm := $t))

  let mut allWfTerm : Term := mkIdent (Name.mkSimple s!"{ns}_seg{numSegs - 1}_wf")
  for idx in [:numSegs - 1] do
    let s := numSegs - 2 - idx
    let sw := mkIdent (Name.mkSimple s!"{ns}_seg{s}_wf")
    allWfTerm ← `(term| AllFns.append $sw $allWfTerm)
  elabCommand (← `(command| theorem $wfAllNm : AllFns Fn.Wf ($modNm).fns := $allWfTerm))

  elabCommand (← `(command|
    set_option trace.profiler true in
    theorem $trieNm : ($modNm).checkAcyclicTrie = true := by t_kernel_rfl))
  elabCommand (← `(command|
    set_option trace.profiler true in
    theorem $namesNm : ($tblNm).map SpecEntry.name = ($modNm).fns.map Fn.name := by t_kernel_rfl))
  elabCommand (← `(command|
    set_option trace.profiler true in
    theorem $nodupNm : (($tblNm).map SpecEntry.name).Nodup :=
      nodup_of_checkAcyclicTrie $trieNm $namesNm))

  let mut tacs : Array (TSyntax `tactic) := #[]
  tacs := tacs.push (← `(tactic| intro Γ h))
  tacs := tacs.push (← `(tactic| have hrem := h))
  for s in [:numSegs] do
    let hId := mkIdent (Name.mkSimple s!"hs_{s}")
    if s + 1 < numSegs then
      tacs := tacs.push (← `(tactic| have $hId := hrem.left))
      tacs := tacs.push (← `(tactic| have hrem := hrem.right))
    else
      tacs := tacs.push (← `(tactic| have $hId := hrem))

  let mut appTerm : Term := ← do
    let s := numSegs - 1
    let certNm := mkIdent (Name.mkSimple s!"{ns}_seg{s}_cert")
    let hsId := mkIdent (Name.mkSimple s!"hs_{s}")
    let depsList := segDeps[s]!.toList
    let mut depsArg : Term ← `(term| Env.Sat.nil Γ)
    if !depsList.isEmpty then
      let last := depsList.getLast!
      depsArg := mkIdent (Name.mkSimple s!"hs_{last}")
      for d in depsList.dropLast.reverse do
        let dId := mkIdent (Name.mkSimple s!"hs_{d}")
        depsArg ← `(term| Env.Sat.append $dId $depsArg)
    `(term| $certNm Γ $depsArg $hsId)

  for idx in [:numSegs - 1] do
    let s := numSegs - 2 - idx
    let certNm := mkIdent (Name.mkSimple s!"{ns}_seg{s}_cert")
    let hsId := mkIdent (Name.mkSimple s!"hs_{s}")
    let depsList := segDeps[s]!.toList
    let mut depsArg : Term ← `(term| Env.Sat.nil Γ)
    if !depsList.isEmpty then
      let last := depsList.getLast!
      depsArg := mkIdent (Name.mkSimple s!"hs_{last}")
      for d in depsList.dropLast.reverse do
        let dId := mkIdent (Name.mkSimple s!"hs_{d}")
        depsArg ← `(term| Env.Sat.append $dId $depsArg)
    let segImpl ← `(term| $certNm Γ $depsArg $hsId)
    appTerm ← `(term| TableImpl.append $segImpl rfl $appTerm)

  tacs := tacs.push (← `(tactic| exact $appTerm))
  elabCommand (← `(command|
    set_option trace.profiler true in
    theorem $okNm : ModuleOk (Env.ofTable $tblNm) $modNm :=
      ModuleOk.ofCanonicalTrie $trieNm $wfAllNm $namesNm (by $tacs;*)))
  elabCommand (← `(command|
    set_option trace.profiler true in
    theorem $canonNm (hchk : ($modNm).checkAcyclic = true) :
        ModuleOk (Env.ofTable $tblNm) $modNm :=
      ModuleOk.ofCanonical hchk $wfAllNm $namesNm (by $tacs;*)))

  let firstHas := mkIdent (Name.mkSimple s!"{ns}_has_0")
  let firstSpec := mkIdent (Name.mkSimple s!"{ns}_spec_0")
  let firstSym := Syntax.mkStrLit s!"{ns}_f_0"
  elabCommand (← `(command|
    set_option trace.profiler true in
    theorem $sat0Nm : (Env.ofTable $tblNm).Has $firstSym $firstSpec :=
      $firstHas (Env.Sat.ofTable $nodupNm fun _ h => h).left))

  let lastIdx := total - 1
  let lastHas := mkIdent (Name.mkSimple s!"{ns}_has_{lastIdx}")
  let lastSpec := mkIdent (Name.mkSimple s!"{ns}_spec_{lastIdx}")
  let lastSym := Syntax.mkStrLit s!"{ns}_f_{lastIdx}"
  let mut satProj ← `(term| Env.Sat.ofTable $nodupNm fun _ h => h)
  for _ in [:numSegs - 1] do
    satProj ← `(term| Env.Sat.right $satProj)
  elabCommand (← `(command|
    set_option trace.profiler true in
    theorem $satLastNm : (Env.ofTable $tblNm).Has $lastSym $lastSpec :=
      $lastHas $satProj))

gen_410_gate g410
  10 10 10 10 10 10 10 10 10 10
  10 10 10 10 10 10 10 10 10 10
  10 10 10 10 10 10 10 10 10 10
  11 11 11 11 11 11 11 11 11 11

theorem g410_len : g410_fns.length = 410 ∧ g410_tbl.length = 410 :=
  ⟨by t_kernel_rfl, by t_kernel_rfl⟩

end

/-! ## 4. Axiom Audit (`<= std3`, single line `< 115c`) -/

#print axioms LeanQbe.T.Spec.Le.refl
#print axioms LeanQbe.T.Spec.impl_or
#print axioms LeanQbe.T.Env.Sat.ofTable
#print axioms LeanQbe.T.Env.Sat.has
#print axioms LeanQbe.T.ModuleOk.ofCanonical
#print axioms LeanQbe.T.ModuleOk.ofCanonicalTrie
#print axioms toy_ok
#print axioms toy_sigs_ok
#print axioms toy_trie_ok
#print axioms toy_noExit
#print axioms toy_has_mode0
#print axioms toy_has_mode1
#print axioms override_ok
#print axioms iunion_ok
#print axioms g410_trie
#print axioms g410_nodup
#print axioms g410_ok
#print axioms g410_canon
#print axioms g410_sat0
#print axioms g410_sat409

end LeanQbeTest.T.CanonicalEnvTest
