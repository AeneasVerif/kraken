module

public import LeanQbe.T.LeanLCNF.Basic
public meta import Lean
public meta import LeanQbe.T.LeanLCNF.Basic

/-!
# Cross-Module `Lean.IR` → `LcModule` Extractor

Reconstructs a transitively closed `LcModule` across module boundaries by walking `Lean.IR.Decl`
entries from `Lean.IR.findEnvDecl`. Unlike `impureExt` (`Basic.lean`), which is a non-persistent
`EnvExtension` limited to declarations elaborated in the current module, `.ir` artifacts persisted
for `meta import` modules retain complete `Lean.IR.Decl.fdecl` bodies for imported definitions,
including `_boxed`, `_redArg`, and `_closed_*` specializations across `Init` and `LeanQbe`.

* `extractIRClosure`: total BFS closure walk over `Environment` starting from `roots : List Name`,
  partitioning reachable targets into `fdecls`, `externs`, `opaqueStubs` (stripped bodies from
  modules imported without `meta import`), and `missing` names.
* `irTy`, `irVal`, `irCode`, `irDeclToLcDecl`, `irDeclToLcExtern`: total 1:1 structural converters
  from `Lean.IR` to `LcTy` / `LcVal` / `LcCode` / `LcDecl` / `LcExtern` (`Except String` error
  reporting; persistent RC operations are dropped exactly as `EmitC` and `Basic.lean` drop them).
* `readLcModuleIR` / `readLcModuleIRCore`: end-to-end `Environment → Except String LcModule` (and
  `CoreM LcModule`) entry points failing loudly on missing decls, opaque stubs, or unsupported
  `IRType`s.
* `lcnf_ir_of_lean!`: command elaborator splicing a small cross-module `LcModule` into kernel defs.

All `Lean.IR` logic lives in `public meta section` so non-meta `LeanQbe` libraries importing
`LeanQbe.T.LeanLCNF.Hub` do not pull `Lean.Compiler.IR` into non-meta runtime artifacts.
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF

public meta section

open Lean

/-- Result of walking the reachable `Lean.IR` call graph from `roots`. -/
structure IRClosure where
  roots : List Name
  fdecls : Array IR.Decl
  externs : Array IR.Decl
  missing : Array Name
  opaqueStubs : Array Name
  deriving Inhabited

/-- Convert a `Lean.IR.IRType` to `LcTy`, rejecting stack-allocated `struct`/`union`/`float32`. -/
def irTy : IR.IRType → Except String LcTy
  | .float => .ok .float
  | .uint8 => .ok .uint8
  | .uint16 => .ok .uint16
  | .uint32 => .ok .uint32
  | .uint64 => .ok .uint64
  | .usize => .ok .usize
  | .erased => .ok .erased
  | .object => .ok .object
  | .tobject => .ok .tobject
  | .tagged => .ok .tagged
  | .void => .ok .void
  | .float32 => .error "LeanLCNF.FromIR: unsupported IRType.float32"
  | .struct n _ => .error s!"LeanLCNF.FromIR: unsupported IRType.struct {n}"
  | .union n _ => .error s!"LeanLCNF.FromIR: unsupported IRType.union {n}"

/-- Convert a `Lean.IR.Arg` to `LcArg`. -/
def irArg : IR.Arg → LcArg
  | .var x => .var x.idx
  | .erased => .erased

/-- Convert a `Lean.IR.CtorInfo` to `LcCtor`. -/
def irCtor (i : IR.CtorInfo) : LcCtor :=
  { name := i.name.toString, cidx := i.cidx, size := i.size, usize := i.usize, ssize := i.ssize }

/-- Convert a `Lean.IR.Param` to `LcParam`. -/
def irParam (p : IR.Param) : Except String LcParam := do
  pure { id := p.x.idx, ty := ← irTy p.ty, borrow := p.borrow }

/-- Convert a `Lean.IR.Expr` bound at type `ty` to `LcVal`. -/
def irVal (ty : IR.IRType) : IR.Expr → Except String LcVal
  | .ctor i ys => .ok (.ctor (irCtor i) (ys.toList.map irArg))
  | .reset n x => .ok (.reset n x.idx)
  | .reuse x i u ys => .ok (.reuse x.idx (irCtor i) u (ys.toList.map irArg))
  | .proj i x => .ok (.oproj i x.idx)
  | .uproj i x => .ok (.uproj i x.idx)
  | .sproj n o x => .ok (.sproj n o x.idx)
  | .fap c ys => .ok (.fap c.toString (ys.toList.map irArg))
  | .pap c ys => .ok (.pap c.toString (ys.toList.map irArg))
  | .ap x ys => .ok (.ap x.idx (ys.toList.map irArg))
  | .box t x => return .box (← irTy t) x.idx
  | .unbox x => .ok (.unbox x.idx)
  | .lit (.num n) => .ok (if ty.isScalar then .lit (.scalar n) else .lit (.nat n))
  | .lit (.str s) => .ok (.lit (.str s))
  | .isShared x => .ok (.isShared x.idx)

private theorem array_toList_sizeOf_lt {α : Type} [SizeOf α] (xs : Array α) :
    sizeOf xs.toList < sizeOf xs := by
  cases xs
  simp

mutual
/-- Convert `Lean.IR.FnBody` to `LcCode` (dropping persistent `inc`/`dec` as `EmitC` does). -/
def irCode : IR.FnBody → Except String LcCode
  | .vdecl x ty e b => do
    .ok (.let_ x.idx (← irTy ty) (← irVal ty e) (← irCode b))
  | .jdecl j xs v b => do
    let ps ← xs.toList.mapM irParam
    .ok (.jp j.idx ps (← irCode v) (← irCode b))
  | .set x i y b => do .ok (.oset x.idx i (irArg y) (← irCode b))
  | .setTag x c b => do .ok (.setTag x.idx c (← irCode b))
  | .uset x i y b => do .ok (.uset x.idx i y.idx (← irCode b))
  | .sset x i o y ty b => do .ok (.sset x.idx i o y.idx (← irTy ty) (← irCode b))
  | .inc x n c p b => if p then irCode b else do .ok (.inc x.idx n c (← irCode b))
  | .dec x n c p b => if p then irCode b else do .ok (.dec x.idx n c (← irCode b))
  | .del x b => do .ok (.del x.idx (← irCode b))
  | .case _ x _ cs => do .ok (.cases x.idx (← irAlts cs.toList))
  | .ret x => .ok (.ret (irArg x))
  | .jmp j ys => .ok (.jmp j.idx (ys.toList.map irArg))
  | .unreachable => .ok .unreach
termination_by b => sizeOf b
decreasing_by
  all_goals simp_wf
  all_goals
    try
      have h := array_toList_sizeOf_lt ‹Array IR.Alt›
      omega
  all_goals omega

/-- Convert a list of `Lean.IR.Alt` alternatives to `(LcPat × LcCode)` pairs. -/
def irAlts : List IR.Alt → Except String (List (LcPat × LcCode))
  | [] => .ok []
  | .ctor i b :: rest => do
    .ok ((.ctor i.cidx i.name.toString, ← irCode b) :: (← irAlts rest))
  | .default b :: rest => do
    .ok ((.dflt, ← irCode b) :: (← irAlts rest))
termination_by alts => sizeOf alts
end

mutual
/-- Collect all direct `fap`/`pap` target `Name`s referenced in `b`. -/
def irRefs (acc : Array Name) : IR.FnBody → Array Name
  | .vdecl _ _ e b =>
    let acc := match e with | .fap c _ | .pap c _ => acc.push c | _ => acc
    irRefs acc b
  | .jdecl _ _ v b => irRefs (irRefs acc v) b
  | .set _ _ _ b | .setTag _ _ b | .uset _ _ _ b | .sset _ _ _ _ _ b
  | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b => irRefs acc b
  | .case _ _ _ cs => irAltsRefs acc cs.toList
  | .ret _ | .jmp _ _ | .unreachable => acc
termination_by b => sizeOf b
decreasing_by
  all_goals simp_wf
  all_goals
    try
      have h := array_toList_sizeOf_lt ‹Array IR.Alt›
      omega
  all_goals omega

/-- Collect direct `fap`/`pap` targets over `case` alternatives. -/
def irAltsRefs (acc : Array Name) : List IR.Alt → Array Name
  | [] => acc
  | .ctor _ b :: rest | .default b :: rest => irAltsRefs (irRefs acc b) rest
termination_by alts => sizeOf alts
end

private def pushUnseen (seen : NameSet) (rear : List Name) (names : Array Name) :
    NameSet × List Name :=
  names.foldl (init := (seen, rear)) fun (s, q) n =>
    if s.contains n then (s, q) else (s.insert n, n :: q)

private def isOpaqueStub : IR.Decl → Bool
  | .extern _ _ _ extData =>
    match extData.entries with
    | [.opaque] => true
    | _ => false
  | _ => false

/-- Walk all `Lean.IR.Decl`s reachable from `roots` via `fap`/`pap` edges using
`Lean.IR.findEnvDecl`. Each symbol is queued at most once in deterministic BFS order. -/
def extractIRClosure (env : Environment) (roots : List Name) : Except String IRClosure :=
  let (seen0, revRoots) := roots.foldl (init := ({}, [])) fun (s, q) n =>
    if s.contains n then (s, q) else (s.insert n, n :: q)
  let rec go (fuel : Nat) (front rear : List Name) (seen : NameSet)
      (fdecls exts : Array IR.Decl) (missing opq : Array Name) : Except String IRClosure :=
    match fuel with
    | 0 => .error "LeanLCNF.FromIR: IR closure traversal exceeded step bound"
    | fuel + 1 =>
      match front, rear with
      | [], [] => .ok { roots, fdecls, externs := exts, missing, opaqueStubs := opq }
      | [], _ => go fuel rear.reverse [] seen fdecls exts missing opq
      | n :: rest, _ =>
        match IR.findEnvDecl env n with
        | some d@(.fdecl _ _ _ b _) =>
          let (seen', rear') := pushUnseen seen rear (irRefs #[] b)
          go fuel rest rear' seen' (fdecls.push d) exts missing opq
        | some d@(.extern ..) =>
          if isOpaqueStub d then
            go fuel rest rear seen fdecls exts missing (opq.push n)
          else
            go fuel rest rear seen fdecls (exts.push d) missing opq
        | none =>
          go fuel rest rear seen fdecls exts (missing.push n) opq
  let maxSteps := env.allImportedModuleNames.size * 4096 + 65536
  go maxSteps revRoots.reverse [] seen0 #[] #[] #[] #[]

/-- Convert a `Lean.IR.Decl.fdecl` to `LcDecl`, tagging errors with the declaration name. -/
def irDeclToLcDecl : IR.Decl → Except String LcDecl
  | .fdecl f xs ty b _ =>
    let res : Except String LcDecl := do
      let ps ← xs.toList.mapM irParam
      let retTy ← irTy ty
      let body ← irCode b
      .ok { name := f.toString, params := ps, retTy, body }
    res.mapError fun msg => s!"{f}: {msg}"
  | .extern f .. => .error s!"LeanLCNF.FromIR: expected fdecl, got extern '{f}'"

/-- Convert a `Lean.IR.Decl.extern` to `LcExtern`, tagging errors with the declaration name. -/
def irDeclToLcExtern : IR.Decl → Except String LcExtern
  | .extern f xs ty _ =>
    let res : Except String LcExtern := do
      let params ← xs.toList.mapM fun p => irTy p.ty
      let retTy ← irTy ty
      .ok { name := f.toString, params, retTy }
    res.mapError fun msg => s!"{f}: {msg}"
  | .fdecl f .. => .error s!"LeanLCNF.FromIR: expected extern, got fdecl '{f}'"

private def previewNames (names : Array Name) (limit : Nat := 8) : String :=
  let head := String.intercalate ", " (names.toList.take limit |>.map toString)
  if names.size > limit then s!"{head}, ... (+{names.size - limit} more)" else head

/-- Convert a closed `IRClosure` into an `LcModule`, failing loudly on missing decls, opaque
stubs (missing `meta import`), or unsupported `IRType`s. -/
def irClosureToLcModule (modName : String) (c : IRClosure) : Except String LcModule := do
  if !c.missing.isEmpty then
    .error s!"LeanLCNF.FromIR: {c.missing.size} missing IR decl(s): {previewNames c.missing}"
  if !c.opaqueStubs.isEmpty then
    let pv := previewNames c.opaqueStubs
    .error s!"LeanLCNF.FromIR: {c.opaqueStubs.size} opaque IR stub(s) (add `meta import`?): {pv}"
  let mut decls : Array LcDecl := Array.mkEmpty c.fdecls.size
  for d in c.fdecls do
    decls := decls.push (← irDeclToLcDecl d)
  let mut exts : Array LcExtern := Array.mkEmpty c.externs.size
  for d in c.externs do
    exts := exts.push (← irDeclToLcExtern d)
  .ok { name := modName
        roots := c.roots.map (·.toString)
        decls := decls.toList
        externs := exts.toList
        snaps := [] }

/-- Extract a transitively closed `LcModule` rooted at `roots` from `env` via `Lean.IR`. -/
def readLcModuleIR (env : Environment) (modName : String) (roots : List Name) :
    Except String LcModule :=
  extractIRClosure env roots >>= irClosureToLcModule modName

/-- Extract a transitively closed `LcModule` rooted at `roots` from the current `CoreM`
environment. -/
def readLcModuleIRCore (modName : String) (roots : List Name) : CoreM LcModule := do
  Lean.ofExcept (readLcModuleIR (← getEnv) modName roots)

open Elab Command in
/-- `lcnf_ir_of_lean! m [f, g, ...]` defines `m : LcModule` from cross-module `Lean.IR`
declarations reachable from `f, g, ...`, splicing each `LcDecl` as `m.d<i>` so no term is
deeply nested. -/
elab "lcnf_ir_of_lean! " modId:ident "[" roots:ident,* "]" : command => do
  let ns ← getCurrNamespace
  let rs ← liftTermElabM <| roots.getElems.toList.mapM fun r =>
    Lean.resolveGlobalConstNoOverload r.raw
  let fullNm := ns ++ modId.getId
  let m ← liftCoreM <| readLcModuleIRCore modId.getId.toString rs
  liftCoreM do
    let mut dNames : Array Lean.Expr := #[]
    for (d, i) in m.decls.zip (List.range m.decls.length) do
      let nm := fullNm.str s!"d{i}"
      addLcConst nm (mkConst ``LcDecl) (eDecl d)
      dNames := dNames.push (mkConst nm)
    let strT := mkConst ``String
    let val := mkAppN (mkConst ``LcModule.mk) #[mkStrLit m.name,
      eList strT (m.roots.map mkStrLit), eList (mkConst ``LcDecl) dNames.toList,
      eList (mkConst ``LcExtern) (m.externs.map eExtern),
      eList (mkConst ``LcSnap) []]
    addLcConst fullNm (mkConst ``LcModule) val
    enableRealizationsForConst fullNm

end

end LeanQbe.T.LeanLCNF
