module

public import LeanQbe.T.LeanLCNF.Basic
public import LeanQbe.T.LeanLCNF.Lower1
public import LeanQbe.T.LeanLCNF.LcnfC0Ffi
public import LeanQbe.T.Bootstrap0.Splice0
public meta import Lean
public meta import LeanQbe.T.LeanLCNF.Basic
public meta import LeanQbe.T.LeanLCNF.Lower1
public meta import LeanQbe.T.LeanLCNF.LcnfC0Ffi
public meta import LeanQbe.T.Bootstrap0.Splice0

/-!
# Zero-Axiom `C0Extern` FFI Specification, Lowering Bridge & Borrow Validation (`C0Extern`)

Strictly additive Shard `F1` bridge tying verified pure-C0 runtime/FFI modules (`LcnfC0Ffi.ffiMod`)
to `LeanLCNF` (`Basic`, total kernel-reducible `Lower1`) without axioms or `@[extern]`:

1. **`C0Extern` & static borrow/signature checking**: `C0Extern` (`leanName`, `c0Sym`, `params`,
   `borrows`, `retTy`, `passRt`), pure kernel validators `checkC0Externs` / `validateC0Externs` /
   `validateLcModuleExts`, and `ffiC0Externs` tying into `LcnfC0Ffi.ffiMod`.
2. **Total kernel-reducible lowering with extern dispatch (`lowerModuleWithExts`)**:
   dispatches `LcVal.fap` calls targeting registered `C0Extern`s directly to `c0Sym` (prepending
   `rt` when `passRt = true`, and using `call1`/`call0` without `rt` when `passRt = false`), while
   proving `lowerModuleWithExts m [] = lowerModule m` when no externs are active.
3. **Elaboration-time borrow-parity extraction & splicing**: `readLcModuleWithExts` verifies `@&`
   borrow parity against Lean's compiled LCNF signature (`getImpureSignature?`) before stopping BFS
   at extern stubs; `lcnf_of_lean_with_exts!` and `splice_lcnf_tflat_with_exts!` produce
   kernel-checked `TFlatFn` lists and `Fn.Wf` witnesses.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T
open LeanQbe.T.Frontend.C0

/-! ## 1. `C0Extern` Specification & Validation -/

/-- Verified mapping from a Lean declaration name to a pure-C0 symbol in `Module`. -/
structure C0Extern where
  /-- Raw Lean declaration name (e.g. `"Demo.ffiSolve"`) or mangled LCNF symbol. -/
  leanName : String
  /-- Target C0 function symbol in the linked runtime/FFI `Module`. -/
  c0Sym : String
  /-- Expected Lean LCNF parameter types in call order. -/
  params : List LcTy
  /-- Borrow flags (`true` iff `@&` borrowed in Lean's LCNF ABI). -/
  borrows : List Bool
  /-- Expected Lean LCNF return type (`.void` or boxed `Unit` when paired with `c0Void`). -/
  retTy : LcTy
  /-- Prepend the implicit `rt : i64` runtime state pointer as C0 argument `0`. -/
  passRt : Bool := true
  /-- Set `true` when the C0 target returns `void` (`rs = []`), e.g. `lcnf_ffi_restore_scratch`. -/
  c0Void : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Canonical mangled LCNF symbol corresponding to `e.leanName`. -/
@[expose] def C0Extern.lcnfSym (e : C0Extern) : String :=
  mangleLc e.leanName

/-- Return `true` iff symbol `sym` identifies extern descriptor `e` (raw or mangled). -/
@[expose] def C0Extern.matchesSym (e : C0Extern) (sym : String) : Bool :=
  sym == e.leanName || sym == e.lcnfSym

/-- Lowered `LeanQbe.T.Ty` signature of the target C0 function parameters. -/
@[expose] def C0Extern.c0ArgTys (e : C0Extern) : List Ty :=
  let args := e.params.map LcTy.toTTy
  if e.passRt then i64 :: args else args

/-- Lowered `LeanQbe.T.Ty` return signature of the target C0 function. -/
@[expose] def C0Extern.c0RetTys (e : C0Extern) : List Ty :=
  if e.c0Void || e.retTy == .void then [] else [e.retTy.toTTy]

/-- Expected `Extern` declaration for `lcnfTModuleWithExts`. -/
@[expose] def C0Extern.toExtern (e : C0Extern) : Extern :=
  { name := e.c0Sym, as := e.c0ArgTys, rs := e.c0RetTys }

/-- Check structural sanity and SysV/AAPCS64 argument-register budget (`≤ 6` C0 args). -/
@[expose] def C0Extern.wf (e : C0Extern) : Bool :=
  !e.leanName.isEmpty &&
  !e.c0Sym.isEmpty &&
  e.params.length == e.borrows.length &&
  e.c0ArgTys.length ≤ 6

/-- Verify that an `LcExtern` matches the LCNF parameter and return types of `e`. -/
@[expose] def C0Extern.matchesExtern (e : C0Extern) (ext : LcExtern) : Bool :=
  e.matchesSym ext.name && ext.params == e.params && ext.retTy == e.retTy

/-- Verify that an `LcDecl` has identical types AND `@&` borrow flags to `e`. -/
@[expose] def C0Extern.matchesDecl (e : C0Extern) (d : LcDecl) : Bool :=
  e.matchesSym d.name &&
  d.params.map (·.ty) == e.params &&
  d.params.map (·.borrow) == e.borrows &&
  d.retTy == e.retTy

/-- Lookup a `C0Extern` in `exts` by raw Lean name or mangled LCNF symbol. -/
@[expose] def lookupC0Extern (exts : List C0Extern) (sym : String) : Option C0Extern :=
  exts.find? (·.matchesSym sym)

/-- Check that `fn : Fn` in a C0 `Module` implements the exact ABI signature of `e`. -/
@[expose] def C0Extern.matchesC0Fn (e : C0Extern) (fn : Fn) : Bool :=
  fn.name == e.c0Sym && fn.as == e.c0ArgTys && fn.rs == e.c0RetTys

/-- Boolean check of well-formedness, uniqueness, and optional C0 signature compatibility. -/
@[expose] def checkC0Externs (exts : List C0Extern)
    (c0Mod? : Option LeanQbe.T.Module := none) : Bool :=
  exts.all (·.wf) &&
  symsNodup (exts.map (·.leanName)) &&
  symsNodup (exts.map (·.lcnfSym)) &&
  match c0Mod? with
  | none => true
  | some c0Mod => exts.all fun e => c0Mod.fns.any e.matchesC0Fn

/-- Validate well-formedness, uniqueness, and optional C0 `Module` signature compatibility for
every `C0Extern` in `exts`. -/
@[expose] def validateC0Externs (exts : List C0Extern)
    (c0Mod? : Option LeanQbe.T.Module := none) : Except String Unit := do
  for e in exts do
    if !e.wf then
      throw s!"C0Extern `{e.leanName}` -> `{e.c0Sym}` failed wf/arity check"
  if !symsNodup (exts.map (·.leanName)) then
    throw "validateC0Externs: duplicate leanName"
  if !symsNodup (exts.map (·.lcnfSym)) then
    throw "validateC0Externs: duplicate mangled lcnfSym"
  if let some c0Mod := c0Mod? then
    for e in exts do
      if !(c0Mod.fns.any e.matchesC0Fn) then
        throw s!"C0Extern `{e.leanName}` expects C0 sig `{e.c0Sym}` missing in C0 module"

/-- Validate `exts` against both an `LcModule` (matching any present decls/externs, including `@&`
borrow flags on `m.decls`) and an optional C0 `Module`. -/
@[expose] def validateLcModuleExts (m : LcModule) (exts : List C0Extern)
    (c0Mod? : Option LeanQbe.T.Module := none) : Except String Unit := do
  validateC0Externs exts c0Mod?
  for d in m.decls do
    if let some e := lookupC0Extern exts d.name then
      if !e.matchesDecl d then
        throw s!"LcDecl `{d.name}` borrow/type mismatch against C0Extern `{e.c0Sym}`"
  for ext in m.externs do
    if let some e := lookupC0Extern exts ext.name then
      if !e.matchesExtern ext then
        throw s!"LcExtern `{ext.name}` type mismatch against C0Extern `{e.c0Sym}`"

/-- Check borrow and type compatibility of `exts` against `m` as a kernel-reducible `Bool`. -/
@[expose] def checkLcModuleExts (m : LcModule) (exts : List C0Extern)
    (c0Mod? : Option LeanQbe.T.Module := none) : Bool :=
  checkC0Externs exts c0Mod? &&
  (m.decls.all fun d =>
    match lookupC0Extern exts d.name with
    | none => true
    | some e => e.matchesDecl d) &&
  (m.externs.all fun ext =>
    match lookupC0Extern exts ext.name with
    | none => true
    | some e => e.matchesExtern ext)

/-! ## 2. Canonical `LcnfC0Ffi.ffiMod` Extern Descriptors -/

/-- Pure C0 FFI primitives from `LcnfC0Ffi.ffiMod` exposed as `C0Extern` descriptors for Lean
programs (borrow accessors take `passRt := false`; allocating/boxing helpers take `passRt := true`).
-/
@[expose] def ffiC0Externs : List C0Extern :=
  [ { leanName := "LeanQbe.T.LeanLCNF.Ffi.getEnd"
      c0Sym := "lcnf_ffi_get_end"
      params := []
      borrows := []
      retTy := .usize
      passRt := true }
  , { leanName := "LeanQbe.T.LeanLCNF.Ffi.carveScratch"
      c0Sym := "lcnf_ffi_carve_scratch"
      params := [.usize]
      borrows := [false]
      retTy := .usize
      passRt := true }
  , { leanName := "LeanQbe.T.LeanLCNF.Ffi.restoreScratch"
      c0Sym := "lcnf_ffi_restore_scratch"
      params := [.usize]
      borrows := [false]
      retTy := .tagged
      passRt := true
      c0Void := true }
  , { leanName := "LeanQbe.T.LeanLCNF.Ffi.baPtr"
      c0Sym := "lcnf_ffi_ba_ptr"
      params := [.object]
      borrows := [true]
      retTy := .usize
      passRt := false }
  , { leanName := "LeanQbe.T.LeanLCNF.Ffi.baLen"
      c0Sym := "lcnf_ffi_ba_len"
      params := [.object]
      borrows := [true]
      retTy := .usize
      passRt := false }
  , { leanName := "LeanQbe.T.LeanLCNF.Ffi.mkOk"
      c0Sym := "lcnf_ffi_mk_ok"
      params := [.tobject]
      borrows := [false]
      retTy := .tobject
      passRt := true }
  , { leanName := "LeanQbe.T.LeanLCNF.Ffi.baOfBytes"
      c0Sym := "lcnf_ffi_ba_of_bytes"
      params := [.usize, .usize]
      borrows := [false, false]
      retTy := .object
      passRt := true }
  , { leanName := "LeanQbe.T.LeanLCNF.Ffi.baWrapOk"
      c0Sym := "lcnf_ffi_ba_wrap_ok"
      params := [.usize, .usize]
      borrows := [false, false]
      retTy := .tobject
      passRt := true }
  , { leanName := "LeanQbe.T.LeanLCNF.Ffi.sentinelByteIdx"
      c0Sym := "lcnf_ffi_sentinel_byte_idx"
      params := [.usize]
      borrows := [false]
      retTy := .usize
      passRt := false }
  , { leanName := "LeanQbe.T.LeanLCNF.Ffi.natBytesLen"
      c0Sym := "lcnf_ffi_nat_bytes_len"
      params := [.tobject]
      borrows := [true]
      retTy := .usize
      passRt := false }
  , { leanName := "LeanQbe.T.LeanLCNF.Ffi.natBytesPtr"
      c0Sym := "lcnf_ffi_nat_bytes_ptr"
      params := [.tobject]
      borrows := [true]
      retTy := .usize
      passRt := true }
  , { leanName := "LeanQbe.T.LeanLCNF.Ffi.natOfBytes"
      c0Sym := "lcnf_ffi_nat_of_bytes"
      params := [.usize, .usize]
      borrows := [false, false]
      retTy := .tobject
      passRt := true }
  , { leanName := "LeanQbe.T.LeanLCNF.Ffi.natWrapOk"
      c0Sym := "lcnf_ffi_nat_wrap_ok"
      params := [.usize, .usize]
      borrows := [false, false]
      retTy := .tobject
      passRt := true }
  , { leanName := "LeanQbe.T.LeanLCNF.Ffi.baToNatS"
      c0Sym := "lcnf_ffi_ba_to_nat_s"
      params := [.object]
      borrows := [true]
      retTy := .tobject
      passRt := true }
  , { leanName := "LeanQbe.T.LeanLCNF.Ffi.natSToBa"
      c0Sym := "lcnf_ffi_nat_s_to_ba"
      params := [.tobject]
      borrows := [true]
      retTy := .tobject
      passRt := true }
  ]

theorem ffiC0Externs_check : checkC0Externs ffiC0Externs (some ffiMod) = true := by
  decide

theorem ffiC0Externs_valid : validateC0Externs ffiC0Externs (some ffiMod) = .ok () :=
  rfl

/-! ## 3. Kernel-Reducible Lowering with `C0Extern` Dispatch -/

/-- Filter out Lean stub declarations replaced by `C0Extern` descriptors. -/
@[expose] def LcModule.stripExts (m : LcModule) (exts : List C0Extern) : LcModule :=
  { m with decls := m.decls.filter fun d => (lookupC0Extern exts d.name).isNone }

theorem LcModule.stripExts_nil (m : LcModule) : m.stripExts [] = m := by
  cases m
  simp [LcModule.stripExts, lookupC0Extern]

/-- Lower argument operands for a `C0Extern` call in `(Ty, LArg)` order. -/
@[expose] def lowerC0ExtArgs (c : LCtx) :
    List LcTy → List LcArg → LM (List (Ty × LArg))
  | [], [] => pure []
  | t :: ts, a :: as => do
    let v ← argAt c a t
    let rest ← lowerC0ExtArgs c ts as
    pure ((t.toTTy, v) :: rest)
  | _, _ => lfail "lowerC0ExtArgs: arity mismatch"

/-- Lower a direct `LcVal.fap` call targeting `ext : C0Extern` to `call1`/`call0`, passing `c.rt`
as argument `0` iff `ext.passRt = true`. -/
@[expose] def lowerC0ExternCall (c : LCtx) (ty : LcTy) (ext : C0Extern)
    (args : List LcArg) (k : LArg → LM LExpr) : LM LExpr := do
  if !ext.wf then
    lfail s!"LeanLCNF ({c.fn}): C0Extern `{ext.leanName}` -> `{ext.c0Sym}` is not wf"
  if args.length != ext.params.length then
    lfail s!"LeanLCNF ({c.fn}): C0Extern `{ext.c0Sym}` expected {ext.params.length} args"
  let lowered ← lowerC0ExtArgs c ext.params args
  let fullArgs := if ext.passRt then (i64, c.rt) :: lowered else lowered
  if ext.c0Void || ext.retTy == .void then
    call0 ext.c0Sym (fullArgs.map (·.1)) (fullArgs.map (·.2))
      (k (imm ty.width (if ty.isScalar then 0 else 1)))
  else
    call1 ext.c0Sym (fullArgs.map (·.1)) ext.retTy.toTTy (fullArgs.map (·.2)) fun r =>
      convW ext.retTy.width ty.width r k

/-- `fap f as` checking `exts : List C0Extern` before falling back to `Lower1.lowerFap`. -/
@[expose] def lowerFapWithExts (exts : List C0Extern) (env : LEnv) (c : LCtx)
    (f : String) (as : List LcArg) (ty : LcTy) (k : LArg → LM LExpr) : LM LExpr :=
  match lookupC0Extern exts f with
  | some ext => lowerC0ExternCall c ty ext as k
  | none => lowerFap env c f as ty k

/-- Lower a `LetValue` bound at type `ty`, dispatching `fap` through `lowerFapWithExts`. -/
@[expose] def lowerValWithExts (exts : List C0Extern) (env : LEnv) (c : LCtx)
    (ty : LcTy) (v : LcVal) (k : LArg → LM LExpr) : LM LExpr :=
  match v with
  | .fap f as => lowerFapWithExts exts env c f as ty k
  | _ => lowerVal env c ty v k

mutual
/-- Lower `LcCode` structurally with `C0Extern` call dispatch. -/
@[expose] def lowerCodeWithExts (exts : List C0Extern) (env : LEnv) (c : LCtx) :
    LcCode → LM LExpr
  | .let_ x ty v k =>
    match selfTailJump? c (.let_ x ty v k) with
    | some jump => jump
    | none => lowerValWithExts exts env c ty v fun r =>
        lowerCodeWithExts exts env (c.bind x r ty) k
  | .jp j ps body k => do
    let lbl ← fresh
    let pvs ← ps.mapM fun p => freshVar p.ty.toTTy
    let c' := { c with jps := (j, lbl, ps.map (·.ty)) :: c.jps }
    let b ← lowerCodeWithExts exts env (c'.bindAll ps (pvs.map vArg)) body
    let kk ← lowerCodeWithExts exts env c' k
    pure (.group [(lbl, pvs, b)] kk)
  | .jmp j as => do
    let some (lbl, ts) := c.jps.lookup j
      | lfail s!"LeanLCNF ({c.fn}): unbound join point {j}"
    if as.length != ts.length then lfail s!"LeanLCNF ({c.fn}): jmp arity"
    let args ← (as.zip ts).mapM fun (a, t) => argAt c a t
    pure (.jump lbl (ts.map LcTy.toTTy) args)
  | .cases x alts => lowerCases c x (lowerAltsWithExts exts env c alts)
  | .ret a => do pure (.ret [c.retTy.toTTy] [← argAt c a c.retTy])
  | .unreach => pure (.exit "lcnf_panic" [i64, i64] [c.rt, imm64 panicUnreachable])
  | .oset x i y k => do
    let (xa, _) ← c.var x
    storeAt i64 (← argAt c y .tobject) xa (8 + 8 * i) (lowerCodeWithExts exts env c k)
  | .uset x i y k => do
    storeAt i64 (← c.var y).1 (← c.var x).1 (8 + 8 * i) (lowerCodeWithExts exts env c k)
  | .sset x n off y ty k => do
    storeAt ty.toTTy (← argAt c (.var y) ty) (← c.var x).1 (8 + 8 * n + off)
      (lowerCodeWithExts exts env c k)
  | .setTag x cidx k => do
    storeAt i8 (imm 8 cidx) (← c.var x).1 7 (lowerCodeWithExts exts env c k)
  | .inc x n chk k => do
    let (xa, xt) ← c.var x
    emitInc xa xt n chk (lowerCodeWithExts exts env c k)
  | .dec x n chk k => do
    let (xa, xt) ← c.var x
    emitDec c.rt xa xt n chk (lowerCodeWithExts exts env c k)
  | .del x k => do
    call0 "lcnf_free_obj" [i64, i64] [c.rt, (← c.var x).1] (lowerCodeWithExts exts env c k)

/-- `lowerCodeWithExts` over `cases` alternatives. -/
@[expose] def lowerAltsWithExts (exts : List C0Extern) (env : LEnv) (c : LCtx) :
    List (LcPat × LcCode) → List (LcPat × LM LExpr)
  | [] => []
  | (p, b) :: rest => (p, lowerCodeWithExts exts env c b) :: lowerAltsWithExts exts env c rest
end

/-- Lower one declaration using `exts` for `C0Extern` call dispatch. -/
@[expose] def lowerDeclWithExts (exts : List C0Extern) (env : LEnv) (d : LcDecl) :
    Except String Frontend.C0.TFlatFn := do
  let tys := d.params.map (·.ty.toTTy)
  let act := withParams tys fun rt pargs => do
    let c0 : LCtx := { fn := d.name, rt, retTy := d.retTy, params := d.params.map (·.ty) }
    if hasSelfTail d.name d.params.length d.body then
      let lbl ← fresh
      let lvs ← tys.mapM freshVar
      let b ← lowerCodeWithExts exts env
        ({ c0 with loop? := some lbl }.bindAll d.params (lvs.map vArg)) d.body
      pure (.group [(lbl, lvs, b)] (.jump lbl tys pargs))
    else lowerCodeWithExts exts env (c0.bindAll d.params pargs) d.body
  let ((ps, body), _) ← act.run 1
  finishFn (mangleLc d.name) ps d.retTy.toTTy body

/-- Lower a whole impure LCNF module with `C0Extern` validation and call dispatch, matching
`Lower1.lowerModule` identically when `exts = []`. -/
@[expose] def lowerModuleWithExts (m : LcModule) (exts : List C0Extern) :
    Except String (List Frontend.C0.TFlatFn) := do
  if !checkLcModuleExts m exts none then
    throw "LeanLCNF: C0Extern validation failed (wf, uniqueness, or borrow/type mismatch)"
  let m' := m.stripExts exts
  let targets ← m'.cloTargets
  let consts := m'.decls.filter fun d => d.params.isEmpty && !d.retTy.isScalar
  let allLits := m'.decls.map (·.body.lits)
  let strs := dedupStr (allLits.flatMap (·.1))
  let bigNats := dedupNat (allLits.flatMap (·.2))
  let totalGlobals := consts.length + strs.length + bigNats.length
  if totalGlobals > rtGlobalSlots then throw "LeanLCNF: too many closed constants/literals"
  let strBase := consts.length
  let natBase := strBase + strs.length
  let env : LEnv :=
    { decls := m'.decls.foldl (fun s d => (d.name, d) :: s) []
      funIds := m'.papTargets.zip (List.range m'.papTargets.length) |>.foldl
        (fun s (f, i) => (f, i) :: s) []
      globals := consts.zip (List.range consts.length) |>.foldl
        (fun s (d, i) => (d.name, i) :: s) []
      strLits := strs.zip (List.range strs.length) |>.foldl
        (fun s (x, i) => (x, strBase + i) :: s) []
      bigNatLits := bigNats.zip (List.range bigNats.length) |>.foldl
        (fun s (x, i) => (x, natBase + i) :: s) [] }
  let fns ← m'.decls.mapM (lowerDeclWithExts exts env)
  let maxK := if targets.isEmpty then m'.maxAp else Nat.max 1 m'.maxAp
  let applies ← (List.range maxK).mapM fun i => genApply (i + 1) targets
  let all := fns ++ applies
  if !symsNodup (all.map (·.name)) then throw "LeanLCNF: mangled symbol collision"
  pure all

/-- Package `tfs` as a `LeanQbe.T.Module` whose `externs` declare both `rtExterns` and
`exts.map C0Extern.toExtern` (discharging cleanly via `ffiMod` / `rtC0CoreMod` linking). -/
@[expose] def lcnfTModuleWithExts (tfs : List Frontend.C0.TFlatFn) (exts : List C0Extern) :
    LeanQbe.T.Module :=
  { fns := tflatFnsToFns tfs
    externs := rtExterns ++ exts.map C0Extern.toExtern
    exits := rtExitSyms }

theorem lowerFapWithExts_nil (env : LEnv) (c : LCtx) (f : String) (as : List LcArg)
    (ty : LcTy) (k : LArg → LM LExpr) :
    lowerFapWithExts [] env c f as ty k = lowerFap env c f as ty k :=
  rfl

theorem lowerValWithExts_nil (env : LEnv) (c : LCtx) (ty : LcTy) (v : LcVal)
    (k : LArg → LM LExpr) :
    lowerValWithExts [] env c ty v k = lowerVal env c ty v k := by
  cases v <;> rfl

mutual
theorem lowerCodeWithExts_nil (env : LEnv) (c : LCtx) :
    ∀ code : LcCode, lowerCodeWithExts [] env c code = lowerCode env c code
  | .let_ x ty v k => by
    simp only [lowerCodeWithExts, lowerCode]
    cases selfTailJump? c (.let_ x ty v k) with
    | some _ => rfl
    | none =>
      simp only [lowerValWithExts_nil]
      congr 1
      funext r
      exact lowerCodeWithExts_nil env (c.bind x r ty) k
  | .jp j ps body k => by
    simp only [lowerCodeWithExts, lowerCode]
    congr 1; funext lbl; congr 1; funext pvs
    have hb := lowerCodeWithExts_nil env
      ({ c with jps := (j, lbl, ps.map fun (p : LcParam) => p.ty) :: c.jps }.bindAll
        ps (pvs.map vArg)) body
    have hk := lowerCodeWithExts_nil env
      { c with jps := (j, lbl, ps.map fun (p : LcParam) => p.ty) :: c.jps } k
    rw [hb, hk]
  | .jmp _ _ => rfl
  | .cases x alts => by
    simp only [lowerCodeWithExts, lowerCode, lowerAltsWithExts_nil]
  | .ret _ => rfl
  | .unreach => rfl
  | .oset x i y k => by
    simp only [lowerCodeWithExts, lowerCode, lowerCodeWithExts_nil]
  | .uset x i y k => by
    simp only [lowerCodeWithExts, lowerCode, lowerCodeWithExts_nil]
  | .sset x n off y ty k => by
    simp only [lowerCodeWithExts, lowerCode, lowerCodeWithExts_nil]
  | .setTag x cidx k => by
    simp only [lowerCodeWithExts, lowerCode, lowerCodeWithExts_nil]
  | .inc x n chk k => by
    simp only [lowerCodeWithExts, lowerCode, lowerCodeWithExts_nil]
  | .dec x n chk k => by
    simp only [lowerCodeWithExts, lowerCode, lowerCodeWithExts_nil]
  | .del x k => by
    simp only [lowerCodeWithExts, lowerCode, lowerCodeWithExts_nil]

theorem lowerAltsWithExts_nil (env : LEnv) (c : LCtx) :
    ∀ alts : List (LcPat × LcCode),
      lowerAltsWithExts [] env c alts = lowerAlts env c alts
  | [] => rfl
  | (p, b) :: rest => by
    simp only [lowerAltsWithExts, lowerAlts, lowerCodeWithExts_nil, lowerAltsWithExts_nil]
end

theorem lowerDeclWithExts_nil (env : LEnv) (d : LcDecl) :
    lowerDeclWithExts [] env d = lowerDecl env d := by
  simp [lowerDeclWithExts, lowerDecl, lowerCodeWithExts_nil]

theorem lowerModuleWithExts_nil (m : LcModule) :
    lowerModuleWithExts m [] = lowerModule m := by
  have hchk : checkLcModuleExts m [] none = true := by
    simp [checkLcModuleExts, checkC0Externs, symsNodup, lookupC0Extern]
  have hfun (env : LEnv) : lowerDeclWithExts [] env = lowerDecl env :=
    funext (lowerDeclWithExts_nil env)
  simp [lowerModuleWithExts, lowerModule, hchk, LcModule.stripExts_nil, hfun]

/-! ## 4. Elaboration-Time Borrow-Parity Check, Extraction & Splicing -/

meta section

open Lean Elab Command Meta Compiler LCNF
open LeanQbe.T.Frontend.C0 (addExposedDecl)

/-- Meta-local `C0Extern` helpers (module-mode meta code may call types from the same file's
public section, plus public imports like `Basic.mangleLc`? No — `Basic` is `public meta
import`, so `Basic`'s public defs ARE meta-usable, while `C0Extern`'s own public defs are not). -/
def mStringToName (s : String) : Name :=
  (s.splitOn ".").foldl (fun acc part => Name.str acc part) Name.anonymous

def mMatchesSym (e : C0Extern) (sym : String) : Bool :=
  sym == e.leanName || sym == mangleLc e.leanName

def mArgCapOk (e : C0Extern) : Bool :=
  let n := e.params.length + if e.passRt then 1 else 0
  !e.leanName.isEmpty && !e.c0Sym.isEmpty && e.params.length == e.borrows.length && n ≤ 6

def mLookupExt (exts : List C0Extern) (sym : String) : Option C0Extern :=
  exts.find? (mMatchesSym · sym)

def mMatchesDecl (e : C0Extern) (d : LcDecl) : Bool :=
  mMatchesSym e d.name &&
  d.params.map (·.ty) == e.params &&
  d.params.map (·.borrow) == e.borrows &&
  d.retTy == e.retTy

def mValidateExts (exts : List C0Extern) : Except String Unit := do
  for e in exts do
    if !mArgCapOk e then
      throw s!"C0Extern `{e.leanName}` -> `{e.c0Sym}` failed wf/arity check"
  if !symsNodup (exts.map (·.leanName)) then
    throw "validateC0Externs: duplicate leanName"
  if !symsNodup (exts.map (fun e => mangleLc e.leanName)) then
    throw "validateC0Externs: duplicate mangled lcnfSym"

/-- Check `@&` borrow parity and parameter/return `LcTy` parity for one `C0Extern` against Lean's
compiled LCNF signature (`getImpureSignature?`) or local impure LCNF decl (`getLocalImpureDecl?`).
-/
def verifyC0ExternBorrowMeta (ext : C0Extern) : CoreM Unit := do
  if !mArgCapOk ext then
    throwError "C0Extern `{ext.leanName}` -> `{ext.c0Sym}` failed wf/arity check"
  let nm := mStringToName ext.leanName
  if let some sig ← getImpureSignature? nm then
    let ps ← sig.params.toList.mapM fun p => ofExcept (xTy p.type)
    let bs := sig.params.toList.map (·.borrow)
    let rTy ← ofExcept (xTy sig.type)
    if ps != ext.params then
      throwError
        "C0Extern `{ext.leanName}` param mismatch: expected {repr ext.params}, got {repr ps}"
    if bs != ext.borrows then
      throwError
        "C0Extern `{ext.leanName}` @& borrow mismatch: expected {repr ext.borrows}, got {repr bs}"
    if rTy != ext.retTy then
      throwError
        "C0Extern `{ext.leanName}` ret mismatch: expected {repr ext.retTy}, got {repr rTy}"
  else if let some d ← getLocalImpureDecl? nm then
    let ld ← ofExcept (xDecl d)
    if !mMatchesDecl ext ld then
      throwError "C0Extern `{ext.leanName}` decl type/borrow mismatch against `{ld.name}`"
  else
    throwError "C0Extern `{ext.leanName}` not found in Lean LCNF signature environment"

/-- Verify `@&` borrow parity for all `C0Extern` entries (requiring every entry when
`verifyAll = true`, or every entry present in the Lean environment plus all BFS-reached externs
when `verifyAll = false`) and read a closed `LcModule` stopping BFS expansion at registered
`C0Extern` callees. -/
partial def readLcModuleWithExts (modName : String) (roots : List Name) (exts : List C0Extern)
    (verifyAll : Bool := false) : CoreM LcModule := do
  if let .error msg := mValidateExts exts then
    throwError msg
  let env ← getEnv
  for ext in exts do
    if verifyAll || env.contains (mStringToName ext.leanName) then
      verifyC0ExternBorrowMeta ext
  let mut queue := roots
  let mut seen : NameSet := {}
  let mut decls : Array LcDecl := #[]
  let mut lcExts : Array LcExtern := #[]
  let mut snaps : Array LcSnap := #[]
  while true do
    match queue with
    | [] => break
    | nm :: rest =>
      queue := rest
      if seen.contains nm then continue
      seen := seen.insert nm
      if let some ext := mLookupExt exts nm.toString then
        verifyC0ExternBorrowMeta ext
        lcExts := lcExts.push { name := nm.toString, params := ext.params, retTy := ext.retTy }
        continue
      let mut found : Option LcDecl := none
      if let some d ← getLocalImpureDecl? nm then
        match xDecl d with
        | .ok ld => found := some ld
        | .error e => throwError e
        let imp := toString (← ppDecl' d .impure)
        let mono ← match ← getMonoDecl? nm with
          | some m => pure (toString (← ppDecl' m .mono))
          | none => pure ""
        snaps := snaps.push { name := nm.toString, mono, impure := imp }
      else if let .str base "_boxed" := nm then
        if let some sig ← getImpureSignature? base then
          match synthBoxed sig with
          | .ok ld => found := some ld
          | .error e => throwError e
      match found with
      | some ld =>
        decls := decls.push ld
        for c in mRefs ld.body do
          let cn := c.toName
          if !seen.contains cn then queue := queue ++ [cn]
      | none =>
        match ← getImpureSignature? nm with
        | some sig =>
          let ps ← sig.params.toList.mapM fun p => ofExcept (xTy p.type)
          let rTy ← ofExcept (xTy sig.type)
          lcExts := lcExts.push { name := nm.toString, params := ps, retTy := rTy }
        | none => throwError m!"LeanLCNF: no impure LCNF decl or signature for '{nm}'"
  let m : LcModule :=
    { name := modName, roots := roots.map (·.toString), decls := decls.toList,
      externs := lcExts.toList, snaps := snaps.toList }
  for d in m.decls do
    if let some ext := mLookupExt exts d.name then
      if !mMatchesDecl ext d then
        throwError "LcDecl `{d.name}` borrow/type mismatch against `{ext.c0Sym}`"
  for ext in m.externs do
    if let some ce := mLookupExt exts ext.name then
      if !(ext.params == ce.params && ext.retTy == ce.retTy) then
        throwError "LcExtern `{ext.name}` type mismatch against `{ce.c0Sym}`"
  pure m

/-- `lcnf_of_lean_with_exts! m exts [f, g, ...]` extracts `m : LcModule` with `@&` borrow parity
checked on every `C0Extern` in `exts`, stopping BFS at those stubs. -/
elab "lcnf_of_lean_with_exts! " modId:ident extsT:term:arg "[" roots:ident,* "]" :
    command => do
  let ns ← getCurrNamespace
  let rs ← liftTermElabM <| roots.getElems.toList.mapM fun r =>
    Lean.resolveGlobalConstNoOverload r.raw
  let exts ← liftTermElabM do
    let listC0Ty := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``C0Extern)
    let e ← Term.elabTerm extsT (some listC0Ty)
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    unsafe Meta.evalExpr (List C0Extern) listC0Ty e
  let fullNm := ns ++ modId.getId
  let m ← liftCoreM <| readLcModuleWithExts modId.getId.toString rs exts
  liftCoreM do
    let mut dNames : Array Lean.Expr := #[]
    for (d, i) in m.decls.zip (List.range m.decls.length) do
      let nm := fullNm.str s!"d{i}"
      addLcConst nm (mkConst ``LcDecl) (eDecl d)
      dNames := dNames.push (mkConst nm)
    let mut sNames : Array Lean.Expr := #[]
    for (s, i) in m.snaps.zip (List.range m.snaps.length) do
      let nm := fullNm.str s!"s{i}"
      addLcConst nm (mkConst ``LcSnap) (eSnap s)
      sNames := sNames.push (mkConst nm)
    let strT := mkConst ``String
    let eList' := fun (tyE : Lean.Expr) (xs : List Lean.Expr) =>
      xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [.zero]) tyE x acc)
        (mkApp (mkConst ``List.nil [.zero]) tyE)
    let val := mkAppN (mkConst ``LcModule.mk) #[mkStrLit m.name,
      eList' strT (m.roots.map mkStrLit), eList' (mkConst ``LcDecl) dNames.toList,
      eList' (mkConst ``LcExtern) (m.externs.map eExtern),
      eList' (mkConst ``LcSnap) sNames.toList]
    addLcConst fullNm (mkConst ``LcModule) val
    enableRealizationsForConst fullNm

/-- Add `thmNm : lowerModuleWithExts lcE extsE = .ok rawE`, checked purely by kernel `Eq.refl`. -/
def addLowerWithExtsThm (thmNm : Name) (lcE extsE rawE : Lean.Expr) : CoreM Unit := do
  let exTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero])
    (Lean.mkConst ``String) Bootstrap0.tflatFnListTy
  let lhs := mkApp2 (Lean.mkConst ``LeanQbe.T.LeanLCNF.lowerModuleWithExts) lcE extsE
  let rhs := mkApp3 (Lean.mkConst ``Except.ok [.zero, .zero])
    (Lean.mkConst ``String) Bootstrap0.tflatFnListTy rawE
  addDecl <| .thmDecl {
    name := thmNm, levelParams := []
    type := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) exTy lhs rhs
    value := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) exTy rhs }

/-- Splices `lowerModuleWithExts lcMod exts` (callees-first topologically sorted) as kernel
`TFlatFn` defs, emitting kernel-checked `<tfs>_lower` and `<tfs>_perm`. -/
elab "splice_lcnf_tflat_with_exts! " modId:ident lcModT:term:arg extsT:term:arg :
    command => do
  let ns ← getCurrNamespace
  let outNm := ns ++ modId.getId
  let listC0Ty := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``C0Extern)
  let tflatListTy := Bootstrap0.tflatFnListTy
  let exTflatTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero])
    (Lean.mkConst ``String) tflatListTy
  let (lcE, extsE, tfsRes) ← liftTermElabM do
    let lcTerm ← Term.elabTerm lcModT (some (Lean.mkConst ``LeanQbe.T.LeanLCNF.LcModule))
    let exTerm ← Term.elabTerm extsT (some listC0Ty)
    Term.synthesizeSyntheticMVarsNoPostponing
    let lcE ← instantiateMVars lcTerm
    let extsE ← instantiateMVars exTerm
    let callE := mkApp2 (Lean.mkConst ``LeanQbe.T.LeanLCNF.lowerModuleWithExts) lcE extsE
    let res ← unsafe Meta.evalExpr (Except String (List Frontend.C0.TFlatFn)) exTflatTy callE
    pure (lcE, extsE, res)
  let tfsRaw ← match tfsRes with
    | .ok tfs => pure tfs
    | .error e => throwError "splice_lcnf_tflat_with_exts!: {e}"
  let tfs ← match Bootstrap0.topoSortTFlat tfsRaw with
    | .ok sorted => pure sorted
    | .error e => throwError "splice_lcnf_tflat_with_exts!: {e}"
  for tf in tfs do
    if !tf.flat.wfCheck (pushTypes tf.as []) [] then
      throwError "splice_lcnf_tflat_with_exts!: wfCheck failed for {tf.name}"
  let mut fnNames : List Name := []
  let c0TfConst := Lean.mkConst ``LeanQbe.T.Frontend.C0.TFlatFn
  for (tf, i) in tfs.zip (List.range tfs.length) do
    let e ← match Bootstrap0.spliceTFlatFn tf with
      | .ok e => pure e
      | .error err => throwError "splice_lcnf_tflat_with_exts!: {err}"
    let nm := outNm ++ Name.mkSimple s!"tf_{i}"
    liftCoreM <| addExposedDecl nm c0TfConst e (forceExpose := true)
    fnNames := fnNames ++ [nm]
  liftCoreM <| addExposedDecl outNm tflatListTy
    (Bootstrap0.tflatFnListLit fnNames) (forceExpose := true)
  let posIn (xs : List Frontend.C0.TFlatFn) (nm : String) : Nat :=
    (xs.findIdx? (·.name == nm)).getD 0
  let rawNames := tfsRaw.map fun tf => fnNames.getD (posIn tfs tf.name) outNm
  let rawNm := outNm.appendAfter "_raw"
  liftCoreM <| addExposedDecl rawNm tflatListTy
    (Bootstrap0.tflatFnListLit rawNames) (forceExpose := true)
  liftCoreM <| addLowerWithExtsThm (outNm.appendAfter "_lower") lcE extsE (Lean.mkConst rawNm)
  liftTermElabM <| Bootstrap0.addPermThm (outNm.appendAfter "_perm")
    (tfs.map fun tf => posIn tfsRaw tf.name) (Lean.mkConst outNm) (Lean.mkConst rawNm)

end

end LeanQbe.T.LeanLCNF
