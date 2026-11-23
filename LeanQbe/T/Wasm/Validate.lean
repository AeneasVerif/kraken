module

public import LeanQbe.T.Wasm.Ast

/-!
# WebAssembly Core Validator (`LeanQbe.T.Wasm.Validate`)

Decidable type, arity, local/global/memory-bounds, and structured control-flow validator
`validateModule : WModule → Bool` for the AST in `LeanQbe.T.Wasm.Ast`, including standard
polymorphic stack tracking after `unreachable`/`br`/`br_table`/`return_`.

Also proves exact stack-shape inversion lemmas used by `LeanQbe.T.Wasm.Lower` and
`LeanQbe.T.Wasm.Safety` to relate reachable stacks to lowered IR arguments.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Wasm

/-- Maximum supported WebAssembly function parameter count (with 3 ABI args = 6 GPRs). -/
abbrev maxWasmParams : Nat := 3

/-- Maximum supported WebAssembly function result count (with status/fuel = 4 GPRs). -/
abbrev maxWasmResults : Nat := 2

/-- Validation context for a single WebAssembly function body. -/
structure WValCtx where
  types : List WFuncTy
  fnTypes : List WFuncTy
  hasMem : Bool
  globals : List WGlobalDecl
  locals : List WValTy
  results : List WValTy
  labels : List (List WValTy)
  deriving Repr, Inhabited

/-- Abstract operand stack used during validation (head of `vals` is top of stack). -/
structure VStack where
  vals : List WValTy
  unreach : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Pop any single value from `s` (synthesizes `.i32` if `vals = []` in unreachable code). -/
def popAny (s : VStack) : Option (WValTy × VStack) :=
  match s.vals with
  | t :: rest => some (t, { s with vals := rest })
  | [] => if s.unreach then some (.i32, s) else none

/-- Pop a value of expected type `e` from `s` (succeeds on empty unreachable stack). -/
def popExpect (e : WValTy) (s : VStack) : Option VStack :=
  match s.vals with
  | t :: rest => if t == e then some { s with vals := rest } else none
  | [] => if s.unreach then some s else none

/-- Pop a reversed signature list from the top of `s` (first element popped from head). -/
def popListRev : List WValTy → VStack → Option VStack
  | [], s => some s
  | t :: ts, s => do
    let s' ← popExpect t s
    popListRev ts s'

/-- Pop `ts` (Wasm bottom-to-top order, so `ts.getLast` is on top of `s`). -/
def popList (ts : List WValTy) (s : VStack) : Option VStack :=
  popListRev ts.reverse s

/-- Push `ts` onto `s` (Wasm bottom-to-top order, so `ts.getLast` ends up on top). -/
def pushList (ts : List WValTy) (s : VStack) : VStack :=
  { s with vals := ts.reverse ++ s.vals }

/-- Check that `s` ends a block expecting exactly `expected`. -/
def validateEnd (expected : List WValTy) (s : VStack) : Bool :=
  match popList expected s with
  | some rem => rem.vals.isEmpty
  | none => false

/-- Validate unary operator width against legal target widths (`extend32_s` only on `i64`). -/
def validateUnOp (w : WValTy) : WUnOp → Bool
  | .clz | .ctz | .popcnt | .extend8_s | .extend16_s => true
  | .extend32_s => w == .i64

/-- Validate WebAssembly linear memory load width/signedness combination. -/
def validateLoad (resTy : WValTy) (width : WMemWidth) (signed : Bool) : Bool :=
  (width.bits < resTy.bitWidth) || (width.bits == resTy.bitWidth && !signed)

/-- Validate WebAssembly linear memory store width against source type width. -/
def validateStore (srcTy : WValTy) (width : WMemWidth) : Bool :=
  width.bits ≤ srcTy.bitWidth

/-- Unreachable empty stack produced by `unreachable`/`br`/`br_table`/`return_`. -/
@[reducible] def unreachStack : VStack := { vals := [], unreach := true }

mutual
/-- Validate one `WInstr` against `ctx` and `s`, returning the post-instruction stack. -/
def validateInstr (ctx : WValCtx) (s : VStack) : WInstr → Option VStack
  | .unreachable => some unreachStack
  | .nop => some s
  | .block bt body => do
    let ft ← bt.resolve ctx.types
    let sAfter ← popList ft.params s
    let ctx' := { ctx with labels := ft.results :: ctx.labels }
    let sBody0 : VStack := { vals := ft.params.reverse, unreach := false }
    let sBodyEnd ← validateSeq ctx' sBody0 body
    if validateEnd ft.results sBodyEnd then some (pushList ft.results sAfter) else none
  | .loop bt body => do
    let ft ← bt.resolve ctx.types
    let sAfter ← popList ft.params s
    let ctx' := { ctx with labels := ft.params :: ctx.labels }
    let sBody0 : VStack := { vals := ft.params.reverse, unreach := false }
    let sBodyEnd ← validateSeq ctx' sBody0 body
    if validateEnd ft.results sBodyEnd then some (pushList ft.results sAfter) else none
  | .if_ bt thenBody elseBody => do
    let ft ← bt.resolve ctx.types
    let s1 ← popExpect .i32 s
    let sAfter ← popList ft.params s1
    let ctx' := { ctx with labels := ft.results :: ctx.labels }
    let sBody0 : VStack := { vals := ft.params.reverse, unreach := false }
    let sThenEnd ← validateSeq ctx' sBody0 thenBody
    let sElseEnd ← validateSeq ctx' sBody0 elseBody
    if validateEnd ft.results sThenEnd && validateEnd ft.results sElseEnd then
      some (pushList ft.results sAfter)
    else
      none
  | .br depth => do
    let lblTys ← ctx.labels[depth]?
    let _ ← popList lblTys s
    some unreachStack
  | .br_if depth => do
    let lblTys ← ctx.labels[depth]?
    let s1 ← popExpect .i32 s
    let s2 ← popList lblTys s1
    some (pushList lblTys s2)
  | .br_table targets defaultTarget => do
    let s1 ← popExpect .i32 s
    let defTys ← ctx.labels[defaultTarget]?
    if targets.all (fun t => ctx.labels[t]? == some defTys) then
      let _ ← popList defTys s1
      some unreachStack
    else
      none
  | .return_ => do
    let _ ← popList ctx.results s
    some unreachStack
  | .call fnIdx => do
    let ft ← ctx.fnTypes[fnIdx]?
    let s1 ← popList ft.params s
    some (pushList ft.results s1)
  | .drop => do
    let (_, s1) ← popAny s
    some s1
  | .select => do
    let s1 ← popExpect .i32 s
    let (t2, s2) ← popAny s1
    let s3 ← popExpect t2 s2
    some (pushList [t2] s3)
  | .local_get idx => do
    let t ← ctx.locals[idx]?
    some (pushList [t] s)
  | .local_set idx => do
    let t ← ctx.locals[idx]?
    popExpect t s
  | .local_tee idx => do
    let t ← ctx.locals[idx]?
    let s1 ← popExpect t s
    some (pushList [t] s1)
  | .global_get idx => do
    let g ← ctx.globals[idx]?
    some (pushList [g.ty] s)
  | .load resTy width signed _ => do
    if ctx.hasMem && validateLoad resTy width signed then
      let s1 ← popExpect .i32 s
      some (pushList [resTy] s1)
    else
      none
  | .store srcTy width _ => do
    if ctx.hasMem && validateStore srcTy width then
      let s1 ← popExpect srcTy s
      popExpect .i32 s1
    else
      none
  | .memory_size =>
    if ctx.hasMem then some (pushList [.i32] s) else none
  | .memory_grow => do
    if ctx.hasMem then
      let s1 ← popExpect .i32 s
      some (pushList [.i32] s1)
    else
      none
  | .memory_copy | .memory_fill => do
    if ctx.hasMem then
      let s1 ← popExpect .i32 s
      let s2 ← popExpect .i32 s1
      popExpect .i32 s2
    else
      none
  | .i32_const _ => some (pushList [.i32] s)
  | .i64_const _ => some (pushList [.i64] s)
  | .eqz w => do
    let s1 ← popExpect w s
    some (pushList [.i32] s1)
  | .unop w op => do
    if validateUnOp w op then
      let s1 ← popExpect w s
      some (pushList [w] s1)
    else
      none
  | .binop w _ => do
    let s1 ← popExpect w s
    let s2 ← popExpect w s1
    some (pushList [w] s2)
  | .relop w _ => do
    let s1 ← popExpect w s
    let s2 ← popExpect w s1
    some (pushList [.i32] s2)
  | .wrap_i64 => do
    let s1 ← popExpect .i64 s
    some (pushList [.i32] s1)
  | .extend_i32_s | .extend_i32_u => do
    let s1 ← popExpect .i32 s
    some (pushList [.i64] s1)

/-- Validate a sequence of instructions left-to-right. -/
def validateSeq (ctx : WValCtx) (s : VStack) : List WInstr → Option VStack
  | [] => some s
  | i :: rest => do
    let s' ← validateInstr ctx s i
    validateSeq ctx s' rest
end

/-- Check that all strings in a list are pairwise distinct. -/
def distinctNames : List Sym → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && distinctNames xs

/-- Check one function signature against module type section and ABI bounds. -/
def resolveOneFnType (types : List WFuncTy) (f : WFunc) : Option WFuncTy := do
  let ft ← types[f.typeIdx]?
  if ft.params.length ≤ maxWasmParams && ft.results.length ≤ maxWasmResults then
    some ft
  else
    none

/-- Auxiliary recursive resolver for function signatures across a function list. -/
def resolveFnTypesAux (types : List WFuncTy) : List WFunc → Option (List WFuncTy)
  | [] => some []
  | f :: fs => do
    let ft ← resolveOneFnType types f
    let rest ← resolveFnTypesAux types fs
    some (ft :: rest)

/-- Resolved function signature table for module `m`, returning `none` if any `typeIdx` is invalid
or exceeds the verified register ABI limits. -/
def resolveModuleFnTypes (m : WModule) : Option (List WFuncTy) :=
  resolveFnTypesAux m.types m.funcs

/-- Validate a single function `f` inside module `m` given resolved `fnTypes`. -/
def validateFunc (m : WModule) (fnTypes : List WFuncTy) (f : WFunc) : Bool :=
  match m.types[f.typeIdx]? with
  | none => false
  | some ft =>
    let okAbi :=
      !f.name.isEmpty && ft.params.length ≤ maxWasmParams && ft.results.length ≤ maxWasmResults
    if !okAbi then false else
      let ctx : WValCtx :=
        { types := m.types
          fnTypes := fnTypes
          hasMem := m.memory.isSome
          globals := m.globals
          locals := ft.params ++ f.locals
          results := ft.results
          labels := [ft.results] }
      let s0 : VStack := { vals := [], unreach := false }
      match validateSeq ctx s0 f.body with
      | some sEnd => validateEnd ft.results sEnd
      | none => false

/-- Validate optional linear memory section metadata. -/
def validateMemory : Option WMemSpec → Bool
  | none => true
  | some mem =>
    mem.initPages ≤ 65536 &&
    mem.maxPages.all (fun mx => mem.initPages ≤ mx && mx ≤ 65536)

/-- Decidable full validator for a `WModule`. -/
def validateModule (m : WModule) : Bool :=
  let okGlobals := m.globals.all (fun g => !g.mut_)
  let okMem := validateMemory m.memory
  let okNames := distinctNames (m.funcs.map (·.name))
  match resolveModuleFnTypes m with
  | none => false
  | some fnTypes =>
    okGlobals && okMem && okNames && m.funcs.all (validateFunc m fnTypes)

/-! ## Stack & Signature Inversion Lemmas -/

theorem popAny_unreach {s : VStack} {t : WValTy} {s' : VStack}
    (h : popAny s = some (t, s')) : s'.unreach = s.unreach := by
  cases hs : s.vals with
  | nil =>
    simp only [popAny, hs] at h
    cases hu : s.unreach <;> simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩
      exact hu
  | cons _ _ =>
    simp only [popAny, hs, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    rfl

theorem popAny_reach_spec {s : VStack} (hu : s.unreach = false) {t : WValTy} {s' : VStack}
    (h : popAny s = some (t, s')) : s.vals = t :: s'.vals ∧ s'.unreach = false := by
  cases hs : s.vals with
  | nil =>
    simp only [popAny, hs, hu, Bool.false_eq_true, ↓reduceIte] at h
    cases h
  | cons a rest =>
    simp only [popAny, hs, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, hu⟩

theorem popExpect_unreach {e : WValTy} {s s' : VStack}
    (h : popExpect e s = some s') : s'.unreach = s.unreach := by
  cases hs : s.vals with
  | nil =>
    simp only [popExpect, hs] at h
    cases hu : s.unreach <;> simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
    · cases h
    · simp only [Option.some.injEq] at h; subst h; exact hu
  | cons t _ =>
    simp only [popExpect, hs] at h
    split at h
    · cases h; rfl
    · cases h

theorem popExpect_reach_spec {e : WValTy} {s : VStack} (hu : s.unreach = false) {s' : VStack}
    (h : popExpect e s = some s') : s.vals = e :: s'.vals ∧ s'.unreach = false := by
  cases hs : s.vals with
  | nil =>
    simp only [popExpect, hs, hu, Bool.false_eq_true, ↓reduceIte] at h
    cases h
  | cons t rest =>
    simp only [popExpect, hs] at h
    cases hte : (t == e)
    · simp only [hte, Bool.false_eq_true, ↓reduceIte] at h; cases h
    · simp only [hte, ↓reduceIte, Option.some.injEq] at h
      have hteq : t = e := beq_iff_eq.mp hte
      subst hteq; subst h
      exact ⟨rfl, hu⟩

theorem popListRev_unreach : ∀ {ts : List WValTy} {s s' : VStack},
    popListRev ts s = some s' → s'.unreach = s.unreach
  | [], s, s', h => by simp only [popListRev, Option.some.injEq] at h; subst h; rfl
  | t :: ts, s, s', h => by
    simp only [popListRev, Option.bind_eq_bind] at h
    cases hp : popExpect t s with
    | none => rw [hp] at h; cases h
    | some s1 =>
      rw [hp] at h
      exact (popListRev_unreach h).trans (popExpect_unreach hp)

theorem popListRev_reach_spec : ∀ {ts : List WValTy} {s s' : VStack},
    s.unreach = false → popListRev ts s = some s' →
    s.vals = ts ++ s'.vals ∧ s'.unreach = false
  | [], s, s', hu, h => by
    simp only [popListRev, Option.some.injEq] at h; subst h; exact ⟨rfl, hu⟩
  | t :: ts, s, s', hu, h => by
    simp only [popListRev, Option.bind_eq_bind] at h
    cases hp : popExpect t s with
    | none => rw [hp] at h; cases h
    | some s1 =>
      rw [hp] at h
      obtain ⟨hs, hu1⟩ := popExpect_reach_spec hu hp
      obtain ⟨hs1, hu'⟩ := popListRev_reach_spec hu1 h
      refine ⟨?_, hu'⟩
      rw [hs, hs1]; rfl

theorem popList_reach_spec {ts : List WValTy} {s s' : VStack}
    (hu : s.unreach = false) (h : popList ts s = some s') :
    s.vals = ts.reverse ++ s'.vals ∧ s'.unreach = false :=
  popListRev_reach_spec hu h

theorem validateEnd_reach_eq {expected : List WValTy} {s : VStack}
    (hu : s.unreach = false) (h : validateEnd expected s = true) :
    s.vals = expected.reverse := by
  simp only [validateEnd] at h
  cases hp : popList expected s with
  | none => rw [hp] at h; simp at h
  | some rem =>
    rw [hp] at h
    have hempty : rem.vals = [] := List.isEmpty_iff.mp (by simpa using h)
    obtain ⟨hs, _⟩ := popList_reach_spec hu hp
    rw [hs, hempty, List.append_nil]

theorem distinctNames_nodup : ∀ {xs : List Sym}, distinctNames xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [distinctNames, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨fun hmem => ?_, distinctNames_nodup h.2⟩
    have hc : xs.contains x = true := List.elem_iff.mpr hmem
    rw [hc] at h
    cases h.1

theorem resolveModuleFnTypes_spec {m : WModule} {fts : List WFuncTy}
    (h : resolveModuleFnTypes m = some fts) :
    fts.length = m.funcs.length ∧
    (∀ (i : Nat) (f : WFunc), m.funcs[i]? = some f →
      ∃ ft, m.types[f.typeIdx]? = some ft ∧ fts[i]? = some ft ∧
        ft.params.length ≤ maxWasmParams ∧ ft.results.length ≤ maxWasmResults) := by
  have haux : ∀ (fs : List WFunc) (res : List WFuncTy),
      resolveFnTypesAux m.types fs = some res →
      res.length = fs.length ∧
      (∀ (i : Nat) (f : WFunc), fs[i]? = some f →
        ∃ ft, m.types[f.typeIdx]? = some ft ∧ res[i]? = some ft ∧
          ft.params.length ≤ maxWasmParams ∧ ft.results.length ≤ maxWasmResults) := by
    intro fs
    induction fs with
    | nil =>
      intro res hm
      simp only [resolveFnTypesAux, Option.some.injEq] at hm
      subst hm
      exact ⟨rfl, fun i f hf => by cases i <;> simp at hf⟩
    | cons fn rest ih =>
      intro res hm
      simp only [resolveFnTypesAux, Bind.bind, Option.bind] at hm
      cases h1 : resolveOneFnType m.types fn with
      | none => rw [h1] at hm; cases hm
      | some ft =>
        rw [h1] at hm
        cases h2 : resolveFnTypesAux m.types rest with
        | none => rw [h2] at hm; cases hm
        | some rrest =>
          rw [h2] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          simp only [resolveOneFnType, Bind.bind, Option.bind] at h1
          cases ht : m.types[fn.typeIdx]? with
          | none => rw [ht] at h1; cases h1
          | some ft' =>
            rw [ht] at h1
            by_cases hlim : (ft'.params.length ≤ maxWasmParams &&
                ft'.results.length ≤ maxWasmResults) = true
            · simp only [hlim, ↓reduceIte, Option.some.injEq] at h1
              subst h1
              obtain ⟨hlen, hfn⟩ := ih rrest h2
              refine ⟨by simp [hlen], fun i f hf => ?_⟩
              cases i with
              | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
                subst hf
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hlim
                exact ⟨ft', ht, rfl, hlim.1, hlim.2⟩
              | succ j =>
                simp only [List.getElem?_cons_succ] at hf ⊢
                exact hfn j f hf
            · simp only [hlim, Bool.false_eq_true, ↓reduceIte] at h1
              cases h1
  exact haux m.funcs fts h

theorem validateModule_elim {m : WModule} (h : validateModule m = true) :
    (m.funcs.map (·.name)).Nodup ∧
    (∀ g ∈ m.globals, g.mut_ = false) ∧
    validateMemory m.memory = true ∧
    ∃ fnTypes,
      resolveModuleFnTypes m = some fnTypes ∧
      ∀ f ∈ m.funcs, validateFunc m fnTypes f = true := by
  simp only [validateModule] at h
  cases hres : resolveModuleFnTypes m with
  | none => rw [hres] at h; simp at h
  | some fnTypes =>
    rw [hres] at h
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    rcases h with ⟨⟨⟨hg, hm⟩, hnd⟩, hfuncs⟩
    refine ⟨distinctNames_nodup hnd, fun g hmem => ?_, hm, fnTypes, rfl, hfuncs⟩
    have hg' := hg g hmem
    cases gm : g.mut_
    · rfl
    · simp [gm] at hg'

theorem validateFunc_elim {m : WModule} {fnTypes : List WFuncTy} {f : WFunc}
    (h : validateFunc m fnTypes f = true) :
    ∃ ft sEnd,
      m.types[f.typeIdx]? = some ft ∧
      !f.name.isEmpty = true ∧
      ft.params.length ≤ maxWasmParams ∧
      ft.results.length ≤ maxWasmResults ∧
      validateSeq
        { types := m.types, fnTypes := fnTypes, hasMem := m.memory.isSome,
          globals := m.globals, locals := ft.params ++ f.locals,
          results := ft.results, labels := [ft.results] }
        { vals := [], unreach := false } f.body = some sEnd ∧
      validateEnd ft.results sEnd = true := by
  simp only [validateFunc] at h
  cases ht : m.types[f.typeIdx]? with
  | none => rw [ht] at h; simp at h
  | some ft =>
    rw [ht] at h
    dsimp only at h
    split at h
    · simp at h
    · next hok =>
      simp only [Bool.not_eq_true'] at hok
      have hok' :
          (!f.name.isEmpty && ft.params.length ≤ maxWasmParams &&
            ft.results.length ≤ maxWasmResults) = true := by
        cases hcond : (!f.name.isEmpty && ft.params.length ≤ maxWasmParams &&
            ft.results.length ≤ maxWasmResults)
        · simp [hcond] at hok
        · rfl
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok'
      cases hs : validateSeq
          { types := m.types, fnTypes := fnTypes, hasMem := m.memory.isSome,
            globals := m.globals, locals := ft.params ++ f.locals,
            results := ft.results, labels := [ft.results] }
          { vals := [], unreach := false } f.body with
      | none => rw [hs] at h; simp at h
      | some sEnd =>
        rw [hs] at h
        exact ⟨ft, sEnd, rfl, hok'.1.1, hok'.1.2, hok'.2, hs, h⟩

end LeanQbe.T.Wasm
