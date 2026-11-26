module

public import LeanQbe.T.Vll.FactorX647
public import LeanQbe.T.MainLemmas
public import LeanQbe.T.Unified.DriverLemmas
public import LeanQbe.T.Amd64.TargLemmas
import LeanQbe.T.TargetLemmas
import LeanQbe.T.RegaLemmas

/-!
# BedrockMach SysV x86-64 `FactorX64`: `Unified.Factoring` & Semantic Bridges

Connects `vllX64Target` (`BedrockMach` L1 on `x64Arch`) and `x64Target` (`Kraken.X64`) via:
* §3 (`Unified.Factoring`): `FlatFn`, `sanitizeHints`, `x64FactoringOn`, `x64Factoring`, and
  byte-identical `compileFn` / `compile` / `compileModule` / `Rega.lowerFn` transport theorems.
* §4 (`TargetLayout`, `Compiled`, & `FnSpec` Bridge): `vllX64Layout`, state/ABI simulation
  (`machToKraken`, `vllX64_{argsIn,retsIn,restored}_iff`), bidirectional `Compiled` bridges
  (`vllX64_compiled_to_x64`, `x64_compiled_to_vllX64`, `vllX64_compileChecked_pair`),
  simultaneous `FnSpec` bridges (`vllX64_compiled_fnSpec_pair`, `x64_compiled_fnSpec_to_vllX64`,
  `vllX64_compiled_fnSpec_src`), and concrete `vllStep` lifting (`vllX64_of_call`).

Zero `Arm64` / `Kraken.AArch64` imports, zero `@[expose]` on proof theorems/lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

open LeanQbe.T
open LeanQbe.T.Amd64
open Std Std.ExtHashMap

/-! ## 3. `Unified.Factoring` & Top-Level Compilation Parity -/

/-- Neutralize any `.rsp` block-entry hint so `Rega.lowerFn` respects `x64AddrValid` while keeping
all other register-allocation hints intact. -/
@[expose] def sanitizeHints (h : x64Isa.Hints) : x64Isa.Hints :=
  if hintsNoRsp h then h else { h with entry := .empty }

theorem sanitizeHints_noRsp (h : x64Isa.Hints) : hintsNoRsp (sanitizeHints h) = true := by
  unfold sanitizeHints
  split
  · assumption
  · rfl

theorem sanitizeHints_eq {h : x64Isa.Hints} (hh : hintsNoRsp h = true) :
    sanitizeHints h = h := by
  simp [sanitizeHints, hh]

theorem vllX64Target_toIsa : vllX64Target.toIsa = vllX64Isa := rfl

theorem vllX64Target_raBytes : vllX64Target.frame.raBytes = x64Target.frame.raBytes := rfl

/-- First-order `Type 0` function representation backed by `TFlat rs`, adapting `Fn : Type 1` to
`Unified.Factoring (Src : Type)`. -/
structure FlatFn : Type where
  name : Sym
  as : List Ty
  rs : List Ty
  body : TFlat rs

/-- Denote a first-order `FlatFn` back into a PHOAS `Fn`. -/
@[expose] def FlatFn.toFn (f : FlatFn) : Fn :=
  ⟨f.name, f.as, f.rs, denoteFunc f.body⟩

/-- Reify a PHOAS `Fn` into its `Type 0` `FlatFn` representative (`f.toFlatFn.toFn = Fn.renorm f`).
-/
@[expose] def Fn.toFlatFn (f : Fn) : FlatFn :=
  ⟨f.name, f.as, f.rs, reifyFunc f.body⟩

/-- `Unified.Factoring` firewall between direct `x64Target` lowering and `vllX64Target` + `asmX64`
over `FlatFn` for any hint oracle satisfying `hintsNoRsp`. -/
@[expose] def x64FactoringOn (lt : LegalTarget) (h : Fn → x64Isa.Hints)
    (hh : ∀ f, hintsNoRsp (h f) = true) :
    Unified.Factoring FlatFn _root_.Directive (Instr x64Arch) where
  direct f := compileFn x64Target.toIsa lt (h f.toFn) f.toFn
  vll f := compileFn vllX64Target.toIsa lt (h f.toFn) f.toFn
  asm := asmX64
  factor f := vllX64_compileFn_eq lt (h f.toFn) (hh f.toFn) f.toFn

/-- Default `Unified.Factoring` instance factoring `Fn.computeHints x64Isa lt` through
`sanitizeHints`. -/
@[expose] def x64Factoring (lt : LegalTarget := x64LegalTarget)
    (h : Fn → x64Isa.Hints := Fn.computeHints x64Isa lt) :
    Unified.Factoring FlatFn _root_.Directive (Instr x64Arch) :=
  x64FactoringOn lt (fun f => sanitizeHints (h f)) (fun f => sanitizeHints_noRsp (h f))

theorem x64Factoring_eq_direct (lt : LegalTarget) (h : Fn → x64Isa.Hints)
    (f : FlatFn) (hh : hintsNoRsp (h f.toFn) = true) :
    (x64Factoring lt h).direct f = compileFn x64Target.toIsa lt (h f.toFn) f.toFn := by
  dsimp only [x64Factoring, x64FactoringOn]
  rw [sanitizeHints_eq hh]

theorem x64Factoring_flat_same_bytes (lt : LegalTarget) (h : Fn → x64Isa.Hints)
    (hh : ∀ f, hintsNoRsp (h f) = true) (f : FlatFn) {is : List (Instr x64Arch)}
    (hv : compileFn vllX64Target.toIsa lt (h f.toFn) f.toFn = .ok is) :
    compileFn x64Target.toIsa lt (h f.toFn) f.toFn = .ok (asmX64List is) :=
  (x64FactoringOn lt h hh).same_bytes f is hv

theorem x64Factoring_flat_transport (lt : LegalTarget) (h : Fn → x64Isa.Hints)
    (hh : ∀ f, hintsNoRsp (h f) = true) (Cert : FlatFn → List _root_.Directive → Prop)
    (hc : ∀ f ds, compileFn x64Target.toIsa lt (h f.toFn) f.toFn = .ok ds → Cert f ds)
    (f : FlatFn) {is : List (Instr x64Arch)}
    (hv : compileFn vllX64Target.toIsa lt (h f.toFn) f.toFn = .ok is) :
    Cert f (asmX64List is) :=
  (x64FactoringOn lt h hh).transport Cert hc f is hv

theorem x64Factoring_lowerFn (h : x64Isa.Hints) (hh : hintsNoRsp h = true) (E : Rega.Ext) (f : Fn)
    (hf : ExprNoSameExt (f.body Rega.VNat Rega.LNat (Tup.levels f.as 0))) :
    (Rega.lowerFn vllX64Target.toIsa h E f).map asmX64List = Rega.lowerFn x64Target.toIsa h E f :=
  vllX64_lowerFn_eq h hh E f hf

theorem x64Factoring_same_bytes (lt : LegalTarget) (h : x64Isa.Hints) (hh : hintsNoRsp h = true)
    (f : Fn) {is : List (Instr x64Arch)}
    (hv : compileFn vllX64Target.toIsa lt h f = .ok is) :
    compileFn x64Target.toIsa lt h f = .ok (asmX64List is) := by
  change compileFn vllX64Isa lt h f = .ok is at hv
  change compileFn x64Isa lt h f = .ok (asmX64List is)
  rw [← vllX64_compileFn_eq lt h hh f, hv]; rfl

theorem x64Factoring_transport (lt : LegalTarget) (h : x64Isa.Hints) (hh : hintsNoRsp h = true)
    (Cert : Fn → List _root_.Directive → Prop) (f : Fn)
    (hc : ∀ ds, compileFn x64Target.toIsa lt h f = .ok ds → Cert f ds)
    {is : List (Instr x64Arch)} (hv : compileFn vllX64Target.toIsa lt h f = .ok is) :
    Cert f (asmX64List is) :=
  hc (asmX64List is) (x64Factoring_same_bytes lt h hh f hv)

theorem x64Factoring_compile_ok (lt : LegalTarget) (fs : List Fn) (hints : List x64Isa.Hints)
    (hall : hints.all hintsNoRsp = true) {is : List (Instr x64Arch)}
    (hv : compile vllX64Target.toIsa lt fs hints = .ok is) :
    compile x64Target.toIsa lt fs hints = .ok (asmX64List is) := by
  change compile vllX64Isa lt fs hints = .ok is at hv
  change compile x64Isa lt fs hints = .ok (asmX64List is)
  rw [← vllX64_compile_eq lt fs hints hall, hv]; rfl

theorem x64Factoring_compileModule_ok (lt : LegalTarget) (exits : List Sym) (nX : Nat)
    (extCallees : List (SigEntry × Nat)) (fs : List Fn) (hints : List x64Isa.Hints)
    (hall : hints.all hintsNoRsp = true) {is : List (Instr x64Arch)}
    {bounds : List (Sym × Nat)}
    (hv : compileModule vllX64Target.toIsa lt vllX64Target.frame.raBytes
      extCallees exits nX fs hints = .ok (is, bounds)) :
    compileModule x64Target.toIsa lt x64Target.frame.raBytes
      extCallees exits nX fs hints = .ok (asmX64List is, bounds) := by
  change compileModule vllX64Isa lt 8 extCallees exits nX fs hints = .ok (is, bounds) at hv
  change compileModule x64Isa lt 8 extCallees exits nX fs hints = .ok (asmX64List is, bounds)
  rw [← vllX64_compileModule_eq lt 8 exits nX extCallees fs hints hall, hv]; rfl

/-! ## 4. `vllX64Layout`, `Compiled` Bridges, & `FnSpec` Semantic Simulation -/

/-- Kernel-reducible bound check for laying out `List (Instr x64Arch)` under `mkVllHost`. -/
@[expose] def vllX64ProgSmall (p : List (Instr x64Arch)) : Bool :=
  decide (4 * p.length < 2 ^ 64)

/-- Concrete `VllHost x64Arch` target layout for `vllX64Target` (`TargetLayout.ofClean`). -/
@[expose] def vllX64Layout : TargetLayout vllX64Target :=
  TargetLayout.ofClean vllX64ProgSmall
    (fun prog h => mkVllHost x64Arch prog (of_decide_eq_true h))
    (fun _ _ => rfl)

private theorem asmX64List_map_label (exits : List Sym) :
    asmX64List (exits.map (Instr.label (A := x64Arch))) = exits.map x64Target.frame.label := by
  induction exits with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.map_cons, asmX64List, List.flatMap_cons]
    exact congrArg ((.label x : _root_.Directive) :: ·) ih

theorem checkCompileResult_x64_of_vll {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat} {fs : List Fn}
    {hints : List x64Isa.Hints} {maxBound : Nat}
    (hall : hints.all hintsNoRsp = true)
    (hv : checkCompile vllX64Target vllX64Layout lt extCallees exits nX fs hints maxBound = true)
    (hxs : x64ProgSmall
      (asmX64List (extractCode (compileModule vllX64Isa lt 8 extCallees exits nX fs hints)) ++
        exits.map x64Target.frame.label) = true) :
    checkCompile x64Target x64Layout lt extCallees exits nX fs hints maxBound = true := by
  dsimp only [checkCompile, checkCompileResult] at hv ⊢
  cases hcmV : compileModule vllX64Isa lt 8 extCallees exits nX fs hints with
  | error e =>
    have hcmV' : compileModule vllX64Target.toIsa lt vllX64Target.frame.raBytes
        extCallees exits nX fs hints = .error e := hcmV
    rw [hcmV'] at hv; cases hv
  | ok p =>
    rcases p with ⟨codeV, boundsV⟩
    let codeT : List vllX64Target.Directive := codeV
    have hcmV' : compileModule vllX64Target.toIsa lt vllX64Target.frame.raBytes
        extCallees exits nX fs hints = .ok (codeT, boundsV) := hcmV
    rw [hcmV'] at hv
    dsimp only at hv
    simp only [Bool.and_eq_true] at hv
    have hcmX : compileModule x64Target.toIsa lt x64Target.frame.raBytes
        extCallees exits nX fs hints = .ok (asmX64List codeV, boundsV) :=
      x64Factoring_compileModule_ok lt exits nX extCallees fs hints hall hcmV'
    have hxs' : x64Layout.progSmall (asmX64List codeV ++ exits.map x64Target.frame.label) =
        true := by
      change x64ProgSmall _ = true
      unfold extractCode at hxs
      rw [hcmV] at hxs
      exact hxs
    rw [hcmX]
    dsimp only
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨hv.1.1.1.1.1, hv.1.1.1.1.2⟩, hv.1.1.1.2⟩, hxs'⟩, hv.1.2⟩, hv.2⟩

private theorem asmX64List_cons (x : Instr x64Arch) (xs : List (Instr x64Arch)) :
    asmX64List (x :: xs) = asmX64 x ++ asmX64List xs :=
  List.flatMap_cons

private theorem mem_asmX64List_label (l : Sym) :
    ∀ {xs : List (Instr x64Arch)} {j : Nat},
      xs[j]? = some (.label l) →
      ∃ k : Nat, (asmX64List xs)[k]? = some (.label l : _root_.Directive)
  | [], _, hj => by simp at hj
  | x :: xs, 0, hj => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
    exact ⟨0, rfl⟩
  | x :: xs, j + 1, hj => by
    simp only [List.getElem?_cons_succ] at hj
    obtain ⟨k, hk⟩ := mem_asmX64List_label l hj
    refine ⟨(asmX64 x).length + k, ?_⟩
    rw [asmX64List_cons, List.getElem?_append_right (Nat.le_add_right _ _)]
    simpa [Nat.add_sub_cancel_left] using hk

private theorem asmX64List_label_dup_of_dup (l : Sym) :
    ∀ {xs : List (Instr x64Arch)} {i j : Nat},
      i < j → xs[i]? = some (.label l) → xs[j]? = some (.label l) →
      ∃ i' j' : Nat, i' < j' ∧ (asmX64List xs)[i']? = some (.label l : _root_.Directive) ∧
        (asmX64List xs)[j']? = some (.label l : _root_.Directive)
  | [], _, _, _, hi, _ => by simp at hi
  | x :: xs, 0, j + 1, _, hi, hj => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
    simp only [List.getElem?_cons_succ] at hj
    obtain ⟨k, hk⟩ := mem_asmX64List_label l hj
    refine ⟨0, k + 1, Nat.zero_lt_succ k, rfl, ?_⟩
    have h0 : asmX64 (.label l : Instr x64Arch) = [(.label l : _root_.Directive)] := rfl
    rw [asmX64List_cons, h0, List.singleton_append, List.getElem?_cons_succ]
    exact hk
  | x :: xs, i + 1, j + 1, hlt, hi, hj => by
    simp only [List.getElem?_cons_succ] at hi hj
    obtain ⟨i', j', hlt', hi', hj'⟩ :=
      asmX64List_label_dup_of_dup l (Nat.succ_lt_succ_iff.mp hlt) hi hj
    refine ⟨(asmX64 x).length + i', (asmX64 x).length + j', Nat.add_lt_add_left hlt' _, ?_, ?_⟩
    · rw [asmX64List_cons, List.getElem?_append_right (Nat.le_add_right _ _)]
      simpa [Nat.add_sub_cancel_left] using hi'
    · rw [asmX64List_cons, List.getElem?_append_right (Nat.le_add_right _ _)]
      simpa [Nat.add_sub_cancel_left] using hj'

theorem labelsUnique_vll_of_x64 {codeV : List (Instr x64Arch)} {exits : List Sym}
    {hv : VllHost x64Arch} {hx : Host}
    (hvp : hv.prog = codeV ++ exits.map (Instr.label (A := x64Arch)))
    (hxp : x64Mach.prog hx = asmX64List codeV ++ exits.map x64Target.frame.label)
    (hu : x64Target.LabelsUnique hx) :
    vllX64Target.LabelsUnique hv := by
  intro i j l hi hj
  change hv.prog[i]? = some (Instr.label l) at hi
  change hv.prog[j]? = some (Instr.label l) at hj
  have hdup : ∀ a b : Nat, a < b → hv.prog[a]? = some (Instr.label l) →
      hv.prog[b]? = some (Instr.label l) → False := by
    intro a b hlt ha hb
    have ha' : (codeV ++ exits.map (Instr.label (A := x64Arch)))[a]? = some (Instr.label l) :=
      hvp ▸ ha
    have hb' : (codeV ++ exits.map (Instr.label (A := x64Arch)))[b]? = some (Instr.label l) :=
      hvp ▸ hb
    obtain ⟨i', j', hlt', hi', hj'⟩ := asmX64List_label_dup_of_dup l hlt ha' hb'
    rw [asmX64List_append, asmX64List_map_label, ← hxp] at hi' hj'
    exact Nat.ne_of_lt hlt' (hu i' j' l hi' hj')
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · exact False.elim (hdup i j hlt hi hj)
  · exact heq
  · exact False.elim (hdup j i hgt hj hi)

/-- Upgrade a `Compiled vllX64Target` artifact into `Compiled x64Target` with identical bounds and
`code = asmX64List Mv.code`. -/
@[expose] def vllX64_compiled_to_x64 {lt : LegalTarget} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} {fs : List Fn} {hints : List x64Isa.Hints} {maxBound : Nat}
    (Mv : Compiled vllX64Target lt extCallees exits nX fs hints maxBound)
    (hh : hints.all hintsNoRsp = true)
    (hxnd : x64Layout.labelsNodup (asmX64List Mv.code ++ exits.map x64Target.frame.label) = true)
    (hxs : x64ProgSmall (asmX64List Mv.code ++ exits.map x64Target.frame.label) = true) :
    Compiled x64Target lt extCallees exits nX fs hints maxBound where
  code := asmX64List Mv.code
  bounds := Mv.bounds
  compileModule_eq := x64Factoring_compileModule_ok lt exits nX extCallees fs hints hh
    Mv.compileModule_eq
  compile_eq := x64Factoring_compile_ok lt fs hints hh Mv.compile_eq
  bound_mem := Mv.bound_mem
  bound_le := Mv.bound_le
  host := x64Layout.layoutOf (asmX64List Mv.code ++ exits.map x64Target.frame.label) hxs
  prog_host := x64Layout.prog_layoutOf _ hxs
  labelsUnique := x64Layout.labelsUnique_layoutOf hxs hxnd

/-- Replicate a `Compiled x64Target` artifact on `vllX64Target` with identical bounds and
`asmX64List Mv.code = Mx.code` (deriving `LabelsUnique` directly from `Mx.labelsUnique`). -/
@[expose] def x64_compiled_to_vllX64 {lt : LegalTarget} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} {fs : List Fn} {hints : List x64Isa.Hints} {maxBound : Nat}
    (Mx : Compiled x64Target lt extCallees exits nX fs hints maxBound)
    (hh : hints.all hintsNoRsp = true)
    (hvs : vllX64ProgSmall
      (extractCode (compileModule vllX64Isa lt 8 extCallees exits nX fs hints) ++
        exits.map vllX64Isa.frame.label) = true) :
    Σ' (Mv : Compiled vllX64Target lt extCallees exits nX fs hints maxBound),
      asmX64List Mv.code = Mx.code ∧ Mv.bounds = Mx.bounds := by
  have heq := vllX64_compileModule_eq lt 8 exits nX extCallees fs hints hh
  cases hcmV : compileModule vllX64Isa lt 8 extCallees exits nX fs hints with
  | error e =>
    have hbad : compileModule x64Isa lt 8 extCallees exits nX fs hints = .error e := by
      rw [← heq, hcmV]; rfl
    have hmx : compileModule x64Isa lt 8 extCallees exits nX fs hints =
        .ok (Mx.code, Mx.bounds) := Mx.compileModule_eq
    rw [hbad] at hmx; cases hmx
  | ok p =>
    rcases p with ⟨codeV, boundsV⟩
    have hxok : compileModule x64Isa lt 8 extCallees exits nX fs hints =
        .ok (asmX64List codeV, boundsV) := by rw [← heq, hcmV]; rfl
    have hmx : compileModule x64Isa lt 8 extCallees exits nX fs hints =
        .ok (Mx.code, Mx.bounds) := Mx.compileModule_eq
    have hpair : (asmX64List codeV, boundsV) = (Mx.code, Mx.bounds) :=
      Except.ok.inj (hxok.symm.trans hmx)
    obtain ⟨hcode, hbounds⟩ := Prod.mk.inj hpair
    have hex_eq :
        extractCode (compileModule vllX64Isa lt 8 extCallees exits nX fs hints) = codeV := by
      unfold extractCode; rw [hcmV]
    have hvs' : vllX64ProgSmall (codeV ++ exits.map vllX64Isa.frame.label) = true := by
      rw [hex_eq] at hvs
      exact hvs
    let codeI : List (Instr x64Arch) := codeV
    let hv := vllX64Layout.layoutOf (codeV ++ exits.map vllX64Isa.frame.label) hvs'
    have hvp : hv.prog = codeV ++ exits.map vllX64Isa.frame.label :=
      vllX64Layout.prog_layoutOf _ hvs'
    have hvp' : hv.prog = codeI ++ exits.map (Instr.label (A := x64Arch)) := hvp
    refine ⟨{
      code := codeV
      bounds := boundsV
      compileModule_eq := hcmV
      compile_eq := compile_of_compileModule hcmV
      bound_mem := fun hnm => hbounds ▸ Mx.bound_mem hnm
      bound_le := fun nm => hbounds ▸ Mx.bound_le nm
      host := hv
      prog_host := hvp'
      labelsUnique := labelsUnique_vll_of_x64 hvp' (hcode ▸ Mx.prog_host) Mx.labelsUnique
    }, hcode, hbounds⟩

/-- Single-check dual-target constructor from `checkCompile` (`O(1)` label uniqueness without
scanning emitted `.L` labels). -/
@[expose] def vllX64_compileChecked_pair {lt : LegalTarget} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} {fs : List Fn} {hints : List x64Isa.Hints} {maxBound : Nat}
    (hh : hints.all hintsNoRsp = true)
    (hv : checkCompile vllX64Target vllX64Layout lt extCallees exits nX fs hints maxBound = true)
    (hxs : x64ProgSmall
      (asmX64List (extractCode (compileModule vllX64Isa lt 8 extCallees exits nX fs hints)) ++
        exits.map x64Target.frame.label) = true) :
    Σ' (Mv : Compiled vllX64Target lt extCallees exits nX fs hints maxBound)
       (Mx : Compiled x64Target lt extCallees exits nX fs hints maxBound),
      Mx.code = asmX64List Mv.code ∧ Mx.bounds = Mv.bounds := by
  let Mv := compileChecked vllX64Target vllX64Layout lt vllX64LabelClean extCallees exits nX fs
    hints maxBound hv
  have hx := checkCompileResult_x64_of_vll hh hv hxs
  let Mx := compileChecked x64Target x64Layout lt x64LabelClean extCallees exits nX fs hints
    maxBound hx
  have hcmX := x64Factoring_compileModule_ok lt exits nX extCallees fs hints hh Mv.compileModule_eq
  have hcmX' : compileModule x64Isa lt 8 extCallees exits nX fs hints =
      .ok (asmX64List Mv.code, Mv.bounds) := hcmX
  have hmx' : compileModule x64Isa lt 8 extCallees exits nX fs hints =
      .ok (Mx.code, Mx.bounds) := Mx.compileModule_eq
  have hpair := Prod.mk.inj (Except.ok.inj (hmx'.symm.trans hcmX'))
  exact ⟨Mv, Mx, hpair.1, hpair.2⟩

/-! ### Machine-State Simulation & Simultaneous `FnSpec` Bridges -/

private theorem abiHolds_trel_iff (sv : MachSt x64Arch) :
    ∀ {ts : List Ty} (locs : Tup (AbiReg Reg64 RegMm) ts) (xs : Tup Val ts),
      TRel (vllX64Target.mach.AbiHolds sv) locs xs ↔
        TRel (x64Target.mach.AbiHolds (machToKraken sv)) locs xs
  | [], _, _ => ⟨fun _ => .nil, fun _ => .nil⟩
  | _ :: _, (loc, locs), (x, xs) => by
    have hhead : vllX64Target.mach.AbiHolds sv _ loc x ↔
        x64Target.mach.AbiHolds (machToKraken sv) _ loc x := by
      cases loc with
      | gpr r =>
        dsimp only [Machine.AbiHolds, vllX64Target, x64Target, vllTarget, vllMach, x64Mach,
          machToKraken]
        rw [regsOfFn_get64 sv.gpr r]
      | vec vr =>
        dsimp only [Machine.AbiHolds, vllX64Target, x64Target, vllTarget, vllMach, x64Mach,
          machToKraken]
        rw [zmmsOfFn_get512 sv.vreg vr]
    have htail := abiHolds_trel_iff sv locs xs
    constructor
    · intro h; cases h with | cons h1 h2 => exact .cons (hhead.mp h1) (htail.mp h2)
    · intro h; cases h with | cons h1 h2 => exact .cons (hhead.mpr h1) (htail.mpr h2)

theorem vllX64_argsIn_iff (sv : MachSt x64Arch) {as : List Ty} (args : Tup Val as) :
    vllX64Target.ArgsIn args sv ↔ x64Target.ArgsIn args (machToKraken sv) := by
  have hass : vllX64Target.toIsa.assignArgs as = x64Target.toIsa.assignArgs as :=
    vllX64_assignArgs_eq as
  constructor
  · rintro ⟨locs, hlocs, hr⟩
    exact ⟨locs, hass ▸ hlocs, (abiHolds_trel_iff sv locs args).mp hr⟩
  · rintro ⟨locs, hlocs, hr⟩
    exact ⟨locs, hass.symm ▸ hlocs, (abiHolds_trel_iff sv locs args).mpr hr⟩

theorem vllX64_retsIn_iff (sv : MachSt x64Arch) {bs : List Ty} (rets : Tup Val bs) :
    vllX64Target.RetsIn rets sv ↔ x64Target.RetsIn rets (machToKraken sv) := by
  have hass : vllX64Target.toIsa.assignRets bs = x64Target.toIsa.assignRets bs :=
    vllX64_assignRets_eq bs
  constructor
  · rintro ⟨locs, hlocs, hr⟩
    exact ⟨locs, hass ▸ hlocs, (abiHolds_trel_iff sv locs rets).mp hr⟩
  · rintro ⟨locs, hlocs, hr⟩
    exact ⟨locs, hass.symm ▸ hlocs, (abiHolds_trel_iff sv locs rets).mpr hr⟩

theorem vllX64_entry_eq (sp : BitVec 64) (ra : Int64) (n : Nat) :
    vllX64Target.Entry sp ra.toBitVec n = x64Target.Entry sp ra n := rfl

theorem vllX64_exit_eq (sp : BitVec 64) (n : Nat) :
    vllX64Target.Exit sp n = x64Target.Exit sp n := rfl

theorem vllX64_restored_iff (sv sv' : MachSt x64Arch) :
    vllX64Target.Restored sv sv' ↔ x64Target.Restored (machToKraken sv) (machToKraken sv') := by
  have hg1 : ∀ r, (machToKraken sv).regs.get64 r = sv.gpr r := regsOfFn_get64 sv.gpr
  have hg2 : ∀ r, (machToKraken sv').regs.get64 r = sv'.gpr r := regsOfFn_get64 sv'.gpr
  change ((∀ r ∈ x64Frame.calleeSaved, sv'.gpr r = sv.gpr r) ∧
      sv'.gpr .rsp = sv.gpr .rsp + BitVec.ofNat 64 8) ↔
    ((∀ r ∈ x64Frame.calleeSaved,
        (machToKraken sv').regs.get64 r = (machToKraken sv).regs.get64 r) ∧
      (machToKraken sv').regs.get64 .rsp =
        (machToKraken sv).regs.get64 .rsp + BitVec.ofNat 64 8)
  constructor
  · rintro ⟨hcs, hsp⟩
    exact ⟨fun r hr => by rw [hg1 r, hg2 r]; exact hcs r hr,
      by rw [hg1 .rsp, hg2 .rsp]; exact hsp⟩
  · rintro ⟨hcs, hsp⟩
    exact ⟨fun r hr => by have h := hcs r hr; rwa [hg1 r, hg2 r] at h,
      by have h := hsp; rwa [hg1 .rsp, hg2 .rsp] at h⟩

/-- Concrete `BedrockMach` `vllStep` call lifting theorem from `vllX64Target.FnSpec`. -/
theorem vllX64_of_call (hv : VllHost x64Arch) {sym : Sym} {b nX : Nat} {as bs : List Ty}
    {spec : Spec as bs} (hfn : vllX64Target.FnSpec hv sym spec b nX)
    {args : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost} (hspec : spec args m Q X)
    (s : MachSt x64Arch) (ra : BitVec 64) (R : Mem 64 → Prop)
    (hargs : vllX64Target.ArgsIn args s)
    (hsp : (s.gpr .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.mem =⋆ Eq m ⋆
      (region (s.gpr .rsp - BitVec.ofNat 64 b) b ⋆ cell64 (s.gpr .rsp) ra) ⋆ R) :
    Eventually (vllStep hv)
      (fun st =>
        (st.pc = ra ∧
          (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], st.data.gpr r = s.gpr r) ∧
          st.data.gpr .rsp = s.gpr .rsp + 8#64 ∧
          ∃ rets m', Q rets m' ∧ vllX64Target.RetsIn rets st.data ∧
            (st.data.mem =⋆ Eq m' ⋆ region (s.gpr .rsp - BitVec.ofNat 64 b) (b + 8) ⋆ R)) ∨
        (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64),
          X sym' cs xs m' ∧ vllX64Target.Defined hv sym' ∧ st.pc = hv.labelAddr sym' ∧
          vllX64Target.ArgsIn xs st.data ∧
          (st.data.gpr .rsp + 8#64).toNat % 16 = 0 ∧
          ∃ (ra' : BitVec 64) (n' : Nat) (F : Mem 64 → Prop), nX ≤ n' ∧
            (st.data.mem =⋆ Eq m' ⋆
              vllX64Target.Entry (st.data.gpr .rsp) ra' n' ⋆ F ⋆ R)))
      ⟨s, hv.labelAddr sym⟩ := by
  refine eventually_weaken _ _ _ _ ?_ (hfn args m Q X hspec s ra R hargs trivial hsp hmem)
  rintro st (⟨hpc, rets, m', hQ, hrets, ⟨hcs, hsp'⟩, hm'⟩ |
    ⟨sym', cs, xs, m', hX, hdef, hpc, has, hspE, ra', n', F, hnX, _, _, hm'⟩)
  · exact Or.inl ⟨hpc, fun r hr => hcs r hr, hsp', rets, m', hQ, hrets, hm'⟩
  · exact Or.inr ⟨sym', cs, xs, m', hX, hdef, hpc, has, hspE, ra', n', F, hnX, hm'⟩

/-- Simultaneous semantic bridge connecting `vllX64Target.FnSpec` (on `BedrockMach` `VllHost`) and
`x64Target.FnSpec` (on Kraken `Host`) for every function in `mod.fns`. -/
theorem vllX64_compiled_fnSpec_pair {lt : LegalTarget} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} {fs : List Fn} {hints : List x64Isa.Hints} {maxBound : Nat}
    (Mv : Compiled vllX64Target lt extCallees exits nX fs hints maxBound)
    (Mx : Compiled x64Target lt extCallees exits nX fs hints maxBound)
    (hbounds : Mx.bounds = Mv.bounds)
    (mod : Module) (hfs : mod.fns = fs) (Γ : Env)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    (hext_v : ∀ p ∈ extCallees,
      vllX64Target.FnSpec Mv.host p.1.1 (legalEnv lt (Env.ofModule mod Γ) p.1.1 p.1.2.1 p.1.2.2)
        p.2 nX)
    (hext_x : ∀ p ∈ extCallees,
      x64Target.FnSpec Mx.host p.1.1 (legalEnv lt (Env.ofModule mod Γ) p.1.1 p.1.2.1 p.1.2.2)
        p.2 nX)
    (hext_uniq : (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ extCallees, p.1.1 ∉ mod.fns.map Fn.name))
    {f : Fn} (hf : f ∈ mod.fns) :
    (vllX64Target.Defined Mv.host f.name ∧ vllX64Target.FnSpec Mv.host f.name
      (legalEnv lt (Env.ofModule mod Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
      (Mv.bound f.name) nX) ∧
    (x64Target.Defined Mx.host f.name ∧ x64Target.FnSpec Mx.host f.name
      (legalEnv lt (Env.ofModule mod Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
      (Mv.bound f.name) nX) := by
  have hv := Mv.fnSpec mod hfs Mv.host Γ 0 Mv.code_infix_host Mv.labelsUnique hacyc hwf hsupp hwp
    hext_v hext_uniq (fun _ hg => Mv.defined_exit_host hg) hf
  have hx := Mx.fnSpec mod hfs Mx.host Γ 0 Mx.code_infix_host Mx.labelsUnique hacyc hwf hsupp hwp
    hext_x hext_uniq (fun _ hg => Mx.defined_exit_host hg) hf
  have hb_eq : Mx.bound f.name = Mv.bound f.name := by
    simp only [Compiled.bound, hbounds]
  exact ⟨hv, hb_eq ▸ hx⟩

/-- Transport a `Compiled x64Target` module certificate to a paired `BedrockMach`
`vllX64Target.FnSpec` + `x64Target.FnSpec` theorem with `asmX64List Mv.code = Mx.code`. -/
theorem x64_compiled_fnSpec_to_vllX64 {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    {fs : List Fn} {hints : List x64Isa.Hints} {maxBound : Nat}
    (Mx : Compiled x64Target lt [] exits nX fs hints maxBound)
    (hh : hints.all hintsNoRsp = true)
    (hvs : vllX64ProgSmall
      (extractCode (compileModule vllX64Isa lt 8 [] exits nX fs hints) ++
        exits.map vllX64Isa.frame.label) = true)
    (mod : Module) (hfs : mod.fns = fs) (Γ : Env)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {f : Fn} (hf : f ∈ mod.fns)
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X') :
    let pair := x64_compiled_to_vllX64 Mx hh hvs
    let Mv := pair.1
    asmX64List Mv.code = Mx.code ∧
    (vllX64Target.Defined Mv.host f.name ∧
      vllX64Target.FnSpec Mv.host f.name (Γ f.name f.as f.rs) (Mv.bound f.name) nX) ∧
    (x64Target.Defined Mx.host f.name ∧
      x64Target.FnSpec Mx.host f.name (Γ f.name f.as f.rs) (Mv.bound f.name) nX) := by
  dsimp only
  let pair := x64_compiled_to_vllX64 Mx hh hvs
  have hvSpec := pair.1.fnSpec_host_src mod hfs Γ hacyc hwf hsupp hwp hf has hrs hnoex
  have hxSpec := Mx.fnSpec_host_src mod hfs Γ hacyc hwf hsupp hwp hf has hrs hnoex
  have hb_eq : Mx.bound f.name = pair.1.bound f.name := by
    simp only [Compiled.bound, pair.2.2]
  exact ⟨pair.2.1, hvSpec, hb_eq ▸ hxSpec⟩

/-- End-to-end closed-module dual-target `FnSpec` + concrete Kraken `step1 Host.exe` execution
bridge starting from a verified `vllX64Target` build certificate `checkCompile`. -/
theorem vllX64_compiled_fnSpec_src {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    {fs : List Fn} {hints : List x64Isa.Hints} {maxBound : Nat}
    (hh : hints.all hintsNoRsp = true)
    (hv : checkCompile vllX64Target vllX64Layout lt [] exits nX fs hints maxBound = true)
    (hxs : x64ProgSmall
      (asmX64List (extractCode (compileModule vllX64Isa lt 8 [] exits nX fs hints)) ++
        exits.map x64Target.frame.label) = true)
    (mod : Module) (hfs : mod.fns = fs) (Γ : Env)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {f : Fn} (hf : f ∈ mod.fns)
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X') :
    let pair := vllX64_compileChecked_pair hh hv hxs
    let Mv := pair.1
    let Mx := pair.2.1
    Mx.code = asmX64List Mv.code ∧
    (vllX64Target.Defined Mv.host f.name ∧
      vllX64Target.FnSpec Mv.host f.name (Γ f.name f.as f.rs) (Mv.bound f.name) nX) ∧
    (x64Target.Defined Mx.host f.name ∧
      x64Target.FnSpec Mx.host f.name (Γ f.name f.as f.rs) (Mv.bound f.name) nX) := by
  dsimp only
  let pair := vllX64_compileChecked_pair hh hv hxs
  have hcm := pair.2.2
  have hvSpec := pair.1.fnSpec_host_src mod hfs Γ hacyc hwf hsupp hwp hf has hrs hnoex
  have hxSpec := pair.2.1.fnSpec_host_src mod hfs Γ hacyc hwf hsupp hwp hf has hrs hnoex
  have hb_eq : pair.2.1.bound f.name = pair.1.bound f.name := by
    simp only [Compiled.bound, hcm.2]
  exact ⟨hcm.1, hvSpec, hb_eq ▸ hxSpec⟩

end LeanQbe.T.Vll