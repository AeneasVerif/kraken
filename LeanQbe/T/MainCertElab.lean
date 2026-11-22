module

public import LeanQbe.T.MainCertCore
public meta import Lean
public meta import LeanQbe.T.MainLink
public meta import LeanQbe.T.MainCertCore
public meta import LeanQbe.T.MainLinkSplice
public meta import LeanQbe.T.MainSplice

/-!
# Meta Chunk & Prefix-Bound Certificate Elaborators (`MainCertElab`)

Meta evaluators and `scoped` command elaborators (`compile_linked_chunks!`, `eval_prefix_ext!`)
emitting kernel-checked `LinkedCert` certificates and auto-computed `(SigEntry × Nat)` prefix
bounds over `LeanQbe.T.MainCertCore` without re-running `compileFn` or `Rega.lowerFn` in the kernel.

Pure proof-only `compile_linked_chunks!` definitions default to `(compile := false)` and
`(compileExt := false)` (`Lean.addNoncomputable`) to eliminate `.c`/`.ir`/`.olean.private` bloat,
while `eval_prefix_ext!` and opted-in `(compileExt := true)` definitions remain computable for
downstream `evalExpr`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

meta section

open Lean Elab Command Meta

/-- Meta-evaluated literal expressions for a single compiled chunk. -/
structure EvalChunkData where
  startIdx : Nat
  fnCount : Nat
  isLast : Bool
  extLit : Lean.Expr
  hintsLit : Lean.Expr
  codeLit : Lean.Expr
  boundsLit : Lean.Expr
  deriving Inhabited

/-- Output of `evalLinkedChunks`: per-chunk literal data plus the final accumulated `exportedExt`
literal (`sigBounds` of all chunks prepended onto `ext0`) for downstream `LinkedCert.append`. -/
structure EvalModuleData where
  chunks : List EvalChunkData
  finalExtLit : Lean.Expr
  deriving Inhabited

/-- Independent per-function meta prepass (`earlyOpt → supportsSource → legal → lateOpt →
`Spill.hints` → `mf.ext`), safe to evaluate across worker tasks before sequential bound linking. -/
def evalOneFnStage1 (I : Isa) (lt : LegalTarget) (f : Fn) :
    Except String (Sym × I.Hints × Fn × Rega.Ext) :=
  let ef := f.earlyOpt
  if !ef.body.supportsSource lt then
    .error s!"{f.name}: unsupported source op for target"
  else
    let mf := (ef.legal lt).lateOpt
    let h := Spill.hints I mf
    .ok (f.name, h, mf, mf.ext)

/-- Sequential callee stack-bound check over pre-evaluated `Spill.hints` and `Rega.Ext`. -/
def evalOneFnBoundCheck (I : Isa) (raBytes : Nat) (exits : List Sym) (nX maxBound : Nat)
    (acc : List (SigEntry × Nat)) (name : Sym) (h : I.Hints) (ext : Rega.Ext) :
    Except String Nat :=
  match checkAndBoundExt I raBytes exits nX acc h ext with
  | some b =>
    if !Nat.ble b maxBound then
      .error s!"{name}: stack bound {b} exceeds maxBound={maxBound}"
    else
      .ok b
  | none => .error s!"{name}: unknown callee, undeclared exit, or stack overflow"

/-- Bound-only `Type 0` stage-1 prepass (drops `Fn` body immediately so tasks retain no ASTs). -/
def evalOneFnBoundStage1 (I : Isa) (lt : LegalTarget) (f : Fn) :
    Except String (Sym × I.Hints × Rega.Ext × SigEntry) :=
  match evalOneFnStage1 I lt f with
  | .error e => .error e
  | .ok (nm, h, mf, ext) => .ok (nm, h, ext, mf.sig)

/-- Fast bound-only meta pass matching `evalOneFn`'s computed `(bound, sig)` without running
`Rega.lowerFn`. -/
def evalOneFnBound (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (exits : List Sym) (nX maxBound : Nat) (acc : List (SigEntry × Nat)) (f : Fn) :
    Except String (Nat × SigEntry) := do
  let (nm, h, ext, sig) ← evalOneFnBoundStage1 I lt f
  let b ← evalOneFnBoundCheck I raBytes exits nX maxBound acc nm h ext
  .ok (b, sig)

/-- Single-function fused meta pass: runs `earlyOpt`, checks `supportsSource`, runs
`legal → lateOpt` once, computes `Spill.hints`, lowers via `Rega.lowerFn`, and checks stack bounds
matching `compileModule` exactly without repeating `earlyOpt`/`mid`. -/
def evalOneFn (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (exits : List Sym) (nX maxBound : Nat) (acc : List (SigEntry × Nat)) (f : Fn) :
    Except String (I.Hints × List I.Directive × Nat × SigEntry) :=
  match evalOneFnStage1 I lt f with
  | .error e => .error e
  | .ok (nm, h, mf, ext) =>
    match Rega.lowerFn I h ext mf,
          evalOneFnBoundCheck I raBytes exits nX maxBound acc nm h ext with
    | .ok c, .ok b => .ok (h, c, b, mf.sig)
    | .error e, _ => .error s!"{nm}: {e}"
    | _, .error e => .error e

/-- Compiled meta evaluator splitting `fs` into callee-first chunks of at most `chunkSize`
functions (clamped to `≥ 1`) and, when `maxDirs > 0`, capping each multi-function chunk at
`maxDirs` emitted directives so heavy functions automatically receive dedicated single-function
chunks. Threads `sigBoundsOf` accumulators matching `checkChunksExt` and returns pure `Lean.Expr`
literals for every chunk. -/
def evalLinkedChunks (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (fs : List Fn) (chunkSize maxBound maxDirs : Nat)
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)] :
    Except String EvalModuleData := do
  let k := Nat.max chunkSize 1
  if fs.isEmpty then
    let (code, bounds) ← compileModule I lt raBytes ext0 exits nX [] []
    let extLit := Lean.toExpr ext0
    pure {
      chunks := [{
        startIdx := 0
        fnCount := 0
        isLast := true
        extLit := extLit
        hintsLit := Lean.toExpr ([] : List I.Hints)
        codeLit := Lean.toExpr code
        boundsLit := Lean.toExpr bounds
      }]
      finalExtLit := extLit
    }
  else
    -- First pass: compile every function once in parallel across worker threads, then resolve
    -- sequential callee bounds into `(name, hint, code, bound, sig)`.
    let tasks := fs.map fun f => Task.spawn fun () =>
      match evalOneFnStage1 I lt f with
      | .error e => .error e
      | .ok (nm, h, mf, ext) =>
        match Rega.lowerFn I h ext mf with
        | .ok c => .ok (nm, h, c, ext, mf.sig)
        | .error e => .error s!"{nm}: {e}"
    let rec compileAll (acc : List (SigEntry × Nat)) :
        List (Task (Except String (Sym × I.Hints × List I.Directive × Rega.Ext × SigEntry))) →
        Except String (List (Sym × I.Hints × List I.Directive × Nat × SigEntry))
      | [] => .ok []
      | t :: rest => do
        let (nm, h, c, ext, sig) ← t.get
        let b ← evalOneFnBoundCheck I raBytes exits nX maxBound acc nm h ext
        let tail ← compileAll ((sig, b) :: acc) rest
        pure ((nm, h, c, b, sig) :: tail)
    let compiled ← compileAll ext0 tasks
    -- Second pass: group into callee-first chunks honoring `chunkSize` and optional `maxDirs`.
    let rec takeChunk (cnt dirSum : Nat)
        (revChunk : List (Sym × I.Hints × List I.Directive × Nat × SigEntry)) :
        List (Sym × I.Hints × List I.Directive × Nat × SigEntry) →
        List (Sym × I.Hints × List I.Directive × Nat × SigEntry) ×
          List (Sym × I.Hints × List I.Directive × Nat × SigEntry)
      | [] => (revChunk.reverse, [])
      | x :: xs =>
        let nextDirs := dirSum + x.2.2.1.length
        if cnt < k && (maxDirs == 0 || nextDirs <= maxDirs) then
          takeChunk (cnt + 1) nextDirs (x :: revChunk) xs
        else
          (revChunk.reverse, x :: xs)
    let rec groupChunks : Nat → Nat → List (SigEntry × Nat) →
        List (Sym × I.Hints × List I.Directive × Nat × SigEntry) →
        List EvalChunkData → EvalModuleData
      | 0, _, acc, _, out => { chunks := out.reverse, finalExtLit := Lean.toExpr acc }
      | _, _, acc, [], out => { chunks := out.reverse, finalExtLit := Lean.toExpr acc }
      | fuel + 1, idx, acc, first :: rest, out =>
        let (grp, rest') := takeChunk 1 first.2.2.1.length [first] rest
        let isLast := rest'.isEmpty
        let hints := grp.map (fun x => x.2.1)
        let code := grp.foldr (fun x cs => x.2.2.1 ++ cs) []
        let bounds := grp.map (fun x => (x.1, x.2.2.2.1))
        let sigs := grp.map (fun x => (x.2.2.2.2, x.2.2.2.1))
        let entry : EvalChunkData := {
          startIdx := idx
          fnCount := grp.length
          isLast := isLast
          extLit := Lean.toExpr acc
          hintsLit := Lean.toExpr hints
          codeLit := Lean.toExpr code
          boundsLit := Lean.toExpr bounds
        }
        groupChunks fuel (idx + grp.length) (sigs ++ acc) rest' (entry :: out)
    pure (groupChunks (compiled.length + 1) 0 ext0 compiled [])

def addCertDef (declNm : Name) (ty val : Lean.Expr) (compile : Bool := true) : CoreM Unit :=
  withCurrHeartbeats do
    let decl := Declaration.defnDecl {
      name := declNm, levelParams := [], type := ty, value := val,
      hints := .abbrev, safety := .safe }
    addDecl decl (forceExpose := true)
    if compile then
      compileDecl decl
    else
      modifyEnv (Lean.addNoncomputable · declNm)

def addCertThm (declNm : Name) (ty val : Lean.Expr) : CoreM Unit :=
  withCurrHeartbeats do
    addDecl (Declaration.thmDecl {
      name := declNm, levelParams := [], type := ty, value := val })

def addKernelEqThm (declNm : Name) (eqTy lhs rhs : Lean.Expr) (u : Level) :
    CoreM Unit :=
  addCertThm declNm
    (mkApp3 (Lean.mkConst ``Eq [u.succ]) eqTy lhs rhs)
    (mkApp2 (Lean.mkConst ``Eq.refl [u.succ]) eqTy lhs)

structure CertOptions where
  maxBT? : Option Term := none
  extT? : Option Term := none
  exitsT? : Option Term := none
  nXT? : Option Term := none
  maxDirsT? : Option Term := none
  compileT? : Option Term := none
  compileExtT? : Option Term := none
  deriving Inhabited

structure CertInputs where
  targE : Lean.Expr
  layoutE : Lean.Expr
  ltE : Lean.Expr
  clE : Lean.Expr
  modE : Lean.Expr
  isaE : Lean.Expr
  raE : Lean.Expr
  labelE : Lean.Expr
  progSmallE : Lean.Expr
  dirTy : Lean.Expr
  listDirTy : Lean.Expr
  listHintsTy : Lean.Expr
  ext0E : Lean.Expr
  exitsE : Lean.Expr
  nXE : Lean.Expr
  maxBE : Lean.Expr
  compileCert : Bool
  compileExt : Bool
  chunks : List EvalChunkData
  finalExtLit : Lean.Expr

def parseCertOptions (optKeys : TSyntaxArray `ident) (optVals : TSyntaxArray `term) :
    CommandElabM CertOptions := do
  let mut opts : CertOptions := {}
  for i in [:optKeys.size] do
    let k := optKeys[i]!.getId
    let v := optVals[i]!
    match k with
    | `maxBound => opts := { opts with maxBT? := some v }
    | `ext => opts := { opts with extT? := some v }
    | `exits => opts := { opts with exitsT? := some v }
    | `nX => opts := { opts with nXT? := some v }
    | `maxDirs => opts := { opts with maxDirsT? := some v }
    | `compile => opts := { opts with compileT? := some v }
    | `compileExt => opts := { opts with compileExtT? := some v }
    | _ =>
      throwErrorAt optKeys[i]!
        ("compile_linked_chunks!: unknown option '{k}'; expected " ++
          "maxBound, ext, exits, nX, maxDirs, compile, compileExt")
  return opts

def evalBoolOpt (opt? : Option Term) (defaultVal : Bool) : TermElabM Bool := do
  match opt? with
  | none => pure defaultVal
  | some t =>
    let e ← Term.elabTerm t (some (Lean.mkConst ``Bool))
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    unsafe evalExpr Bool (Lean.mkConst ``Bool) e

def elabAndEvalChunks (targT layoutT ltT clT modT : Term) (chunkSize : Nat)
    (opts : CertOptions) : TermElabM CertInputs := do
  let targE ← Term.elabTerm targT (some (Lean.mkConst ``LeanQbe.T.Target))
  let layoutTy := mkApp (Lean.mkConst ``LeanQbe.T.TargetLayout) targE
  let layoutE ← Term.elabTerm layoutT (some layoutTy)
  let ltE ← Term.elabTerm ltT (some (Lean.mkConst ``LeanQbe.T.LegalTarget))
  let isaE := mkApp (Lean.mkConst ``LeanQbe.T.Target.toIsa) targE
  let clTy := mkApp (Lean.mkConst ``LeanQbe.T.Rega.LabelClean) isaE
  let clE ← Term.elabTerm clT (some clTy)
  let modE ← Term.elabTerm modT (some (Lean.mkConst ``LeanQbe.T.Module))
  let sigEntryNatTy :=
    mkApp2 (Lean.mkConst ``Prod [.zero, .zero])
      (Lean.mkConst ``LeanQbe.T.SigEntry) (Lean.mkConst ``Nat)
  let listExtTy := mkApp (Lean.mkConst ``List [.zero]) sigEntryNatTy
  let listSymTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.Sym)
  let ext0E ← match opts.extT? with
    | some t => Term.elabTerm t (some listExtTy)
    | none => pure (mkApp (Lean.mkConst ``List.nil [.zero]) sigEntryNatTy)
  let exitsE ← match opts.exitsT? with
    | some t => Term.elabTerm t (some listSymTy)
    | none => pure (mkApp (Lean.mkConst ``List.nil [.zero]) (Lean.mkConst ``LeanQbe.T.Sym))
  let nXE ← match opts.nXT? with
    | some t => Term.elabTerm t (some (Lean.mkConst ``Nat))
    | none => pure (mkNatLit 0)
  let maxBE ← match opts.maxBT? with
    | some t => Term.elabTerm t (some (Lean.mkConst ``Nat))
    | none => pure (mkNatLit 2048)
  let maxDirsE ← match opts.maxDirsT? with
    | some t => Term.elabTerm t (some (Lean.mkConst ``Nat))
    | none => pure (mkNatLit 0)
  let compileCert ← evalBoolOpt opts.compileT? false
  let compileExt ← evalBoolOpt opts.compileExtT? false
  Term.synthesizeSyntheticMVarsNoPostponing
  let targE ← instantiateMVars targE
  let layoutE ← instantiateMVars layoutE
  let ltE ← instantiateMVars ltE
  let clE ← instantiateMVars clE
  let modE ← instantiateMVars modE
  let isaE ← instantiateMVars isaE
  let ext0E ← instantiateMVars ext0E
  let exitsE ← instantiateMVars exitsE
  let nXE ← instantiateMVars nXE
  let maxBE ← instantiateMVars maxBE
  let maxDirsE ← instantiateMVars maxDirsE
  let regTy ← whnf (mkApp (Lean.mkConst ``LeanQbe.T.Isa.Reg) isaE)
  let vregTy ← whnf (mkApp (Lean.mkConst ``LeanQbe.T.Isa.VReg) isaE)
  let condTy ← whnf (mkApp (Lean.mkConst ``LeanQbe.T.Isa.Cond) isaE)
  let hintTy := mkApp3 (Lean.mkConst ``LeanQbe.T.Hints) regTy vregTy condTy
  let listHintsConcreteTy := mkApp (Lean.mkConst ``List [.zero]) hintTy
  let dirConcreteTy ← whnf (mkApp (Lean.mkConst ``LeanQbe.T.Isa.Directive) isaE)
  let listDirConcreteTy := mkApp (Lean.mkConst ``List [.zero]) dirConcreteTy
  let toExprHintsInst ← synthInstance
    (mkApp (Lean.mkConst ``Lean.ToExpr [.zero]) listHintsConcreteTy)
  let toExprDirInst ← synthInstance
    (mkApp (Lean.mkConst ``Lean.ToExpr [.zero]) listDirConcreteTy)
  let frameE ← mkAppM ``LeanQbe.T.Isa.frame #[isaE]
  let raE ← mkAppM ``LeanQbe.T.FrameIsa.raBytes #[frameE]
  let labelE ← mkAppM ``LeanQbe.T.FrameIsa.label #[frameE]
  let progSmallE ← mkAppM ``LeanQbe.T.TargetLayout.progSmall #[layoutE]
  let fnsE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) modE
  let callE ← instantiateMVars (mkAppN (Lean.mkConst ``LeanQbe.T.evalLinkedChunks)
    #[isaE, ltE, raE, ext0E, exitsE, nXE, fnsE, mkNatLit chunkSize, maxBE, maxDirsE,
      toExprHintsInst, toExprDirInst])
  let outTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero]) (Lean.mkConst ``String)
    (Lean.mkConst ``LeanQbe.T.EvalModuleData)
  let evalRes ← unsafe evalExpr (Except String EvalModuleData) outTy callE
  let modData ← match evalRes with
    | .error e => throwError "compile_linked_chunks!: {e}"
    | .ok md => pure md
  let dirTy := mkApp (Lean.mkConst ``LeanQbe.T.Isa.Directive) isaE
  let listDirTy := mkApp (Lean.mkConst ``List [.zero]) dirTy
  let listHintsTy := mkApp (Lean.mkConst ``List [.zero])
    (mkApp (Lean.mkConst ``LeanQbe.T.Isa.Hints) isaE)
  return {
    targE, layoutE, ltE, clE, modE, isaE, raE, labelE, progSmallE,
    dirTy, listDirTy, listHintsTy, ext0E, exitsE, nXE, maxBE,
    compileCert, compileExt,
    chunks := modData.chunks, finalExtLit := modData.finalExtLit
  }

/-- `compile_linked_chunks! certName target layout legalTarget labelClean mod chunkSize
[(maxBound := ...)] [(ext := ...)] [(exits := ...)] [(nX := ...)] [(maxDirs := ...)]
[(compile := ...)] [(compileExt := ...)]` splits `mod.fns` into callee-first chunks of at most
`chunkSize` functions (and optional `maxDirs` directives), evaluates hints and `compileModule` in
a single fused meta pass, splices literal `(ext, hints, code, bounds)` per chunk, checks each
chunk independently in the kernel (`compileModule`, `checkCompileLit`, `checkSupportsChunk`), links
all chunks via O(N) metadata-only `checkLinkList`, and defines `certName : LinkedCert ...`. -/
scoped syntax "compile_linked_chunks! " ident
    term:arg term:arg term:arg term:arg term:arg num
    ("(" ident " := " term ")")* : command

scoped elab_rules : command
  | `(compile_linked_chunks! $certId $targT $layoutT $ltT $clT $modT $chunkSizeLit
      $[($optKeys := $optVals)]*) => do
    let ns ← getCurrNamespace
    let certNm := ns ++ certId.getId
    let auxNs := certNm ++ `aux
    let opts ← parseCertOptions optKeys optVals
    let inp ← liftTermElabM <|
      elabAndEvalChunks targT layoutT ltT clT modT chunkSizeLit.getNat opts
    let fnTy := Lean.mkConst ``LeanQbe.T.Fn
    let listFnTy := mkApp (Lean.mkConst ``List [1]) fnTy
    let symTy := Lean.mkConst ``LeanQbe.T.Sym
    let sigEntryNatTy :=
      mkApp2 (Lean.mkConst ``Prod [.zero, .zero])
        (Lean.mkConst ``LeanQbe.T.SigEntry) (Lean.mkConst ``Nat)
    let listExtTy := mkApp (Lean.mkConst ``List [.zero]) sigEntryNatTy
    let symNatTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) symTy (Lean.mkConst ``Nat)
    let listBoundsTy := mkApp (Lean.mkConst ``List [.zero]) symNatTy
    let okPairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) inp.listDirTy listBoundsTy
    let excTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero]) (Lean.mkConst ``String) okPairTy
    let fnsBaseE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) inp.modE
    -- Pass 1: emit all chunks' pure literal definitions (`fns`, `hints`, `ext`, `code`, `bounds`).
    let mut chunkNames : Array (Name × Name × Name × Name × Name × Name × Name × Name × Name ×
      EvalChunkData) := #[]
    let mut ci : Nat := 0
    for ch in inp.chunks do
      let pfx := s!"c{ci}"
      let fnsNm := auxNs ++ Name.mkSimple s!"{pfx}_fns"
      let hintsNm := auxNs ++ Name.mkSimple s!"{pfx}_hints"
      let extNm := auxNs ++ Name.mkSimple s!"{pfx}_ext"
      let codeNm := auxNs ++ Name.mkSimple s!"{pfx}_code"
      let boundsNm := auxNs ++ Name.mkSimple s!"{pfx}_bounds"
      let cmNm := auxNs ++ Name.mkSimple s!"{pfx}_cm"
      let metaNm := auxNs ++ Name.mkSimple s!"{pfx}_meta"
      let suppNm := auxNs ++ Name.mkSimple s!"{pfx}_supp"
      let compNm := auxNs ++ Name.mkSimple s!"{pfx}_compiled"
      let dropE := mkApp3 (Lean.mkConst ``List.drop [1]) fnTy (mkNatLit ch.startIdx) fnsBaseE
      let sliceE :=
        if ch.isLast then dropE
        else mkApp3 (Lean.mkConst ``List.take [1]) fnTy (mkNatLit ch.fnCount) dropE
      liftCoreM do
        addCertDef fnsNm listFnTy sliceE inp.compileCert
        addCertDef hintsNm inp.listHintsTy ch.hintsLit inp.compileCert
        addCertDef extNm listExtTy ch.extLit inp.compileCert
        addCertDef codeNm inp.listDirTy ch.codeLit inp.compileCert
        addCertDef boundsNm listBoundsTy ch.boundsLit inp.compileCert
      chunkNames := chunkNames.push
        (fnsNm, hintsNm, extNm, codeNm, boundsNm, cmNm, metaNm, suppNm, compNm, ch)
      ci := ci + 1
    -- Pass 2: queue ALL per-chunk kernel theorems (`cm`, `meta`, `supp`) together so Lean's
    -- async kernel threadpool checks all chunks in parallel across CPU cores.
    for (fnsNm, hintsNm, extNm, codeNm, boundsNm, cmNm, metaNm, suppNm, _, _) in chunkNames do
      let cmLhs := mkAppN (Lean.mkConst ``LeanQbe.T.compileModule)
        #[inp.isaE, inp.ltE, inp.raE, Lean.mkConst extNm, inp.exitsE, inp.nXE,
          Lean.mkConst fnsNm, Lean.mkConst hintsNm]
      let cmRhs := mkApp3 (Lean.mkConst ``Except.ok [.zero, .zero])
        (Lean.mkConst ``String) okPairTy
        (mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) inp.listDirTy listBoundsTy
          (Lean.mkConst codeNm) (Lean.mkConst boundsNm))
      liftCoreM <| addKernelEqThm cmNm excTy cmLhs cmRhs .zero
      let fnNamesE := mkApp4 (Lean.mkConst ``List.map [1, .zero])
        fnTy symTy (Lean.mkConst ``LeanQbe.T.Fn.name) (Lean.mkConst fnsNm)
      let metaLhs := mkAppN (Lean.mkConst ``LeanQbe.T.checkCompileLit)
        #[inp.dirTy, inp.labelE, inp.progSmallE, Lean.mkConst codeNm, Lean.mkConst boundsNm,
          fnNamesE, inp.exitsE, inp.maxBE]
      liftCoreM <| addKernelEqThm metaNm (Lean.mkConst ``Bool)
        metaLhs (Lean.mkConst ``Bool.true) .zero
      let suppLhs := mkApp2 (Lean.mkConst ``LeanQbe.T.checkSupportsChunk)
        inp.ltE (Lean.mkConst fnsNm)
      liftCoreM <| addKernelEqThm suppNm (Lean.mkConst ``Bool)
        suppLhs (Lean.mkConst ``Bool.true) .zero
    -- Pass 3: assemble per-chunk `Compiled` bundles and `CompiledChunk` entries.
    let mut chunkEntries : List Lean.Expr := []
    for (fnsNm, hintsNm, extNm, codeNm, boundsNm, cmNm, metaNm, _, compNm, _) in chunkNames do
      let compTy := mkAppN (Lean.mkConst ``LeanQbe.T.Compiled)
        #[inp.targE, inp.ltE, Lean.mkConst extNm, inp.exitsE, inp.nXE,
          Lean.mkConst fnsNm, Lean.mkConst hintsNm, inp.maxBE]
      let compVal := mkAppN (Lean.mkConst ``LeanQbe.T.compileCheckedLit)
        #[inp.targE, inp.layoutE, inp.ltE, inp.clE, Lean.mkConst extNm, inp.exitsE, inp.nXE,
          Lean.mkConst fnsNm, Lean.mkConst hintsNm, inp.maxBE,
          Lean.mkConst codeNm, Lean.mkConst boundsNm, Lean.mkConst cmNm, Lean.mkConst metaNm]
      liftCoreM <| addCertDef compNm compTy compVal inp.compileCert
      let chunkVal := mkAppN (Lean.mkConst ``LeanQbe.T.CompiledChunk.mk)
        #[inp.targE, inp.ltE, inp.exitsE, inp.nXE, Lean.mkConst extNm, Lean.mkConst fnsNm,
          Lean.mkConst hintsNm, inp.maxBE, Lean.mkConst compNm]
      chunkEntries := chunkEntries ++ [chunkVal]
    -- Emit linked chunk list and O(N) metadata-only link check
    let chunkTy := mkAppN (Lean.mkConst ``LeanQbe.T.CompiledChunk)
      #[inp.targE, inp.ltE, inp.exitsE, inp.nXE]
    let listChunkTy := mkApp (Lean.mkConst ``List [1]) chunkTy
    let chunksVal := chunkEntries.foldr
      (fun c acc => mkApp3 (Lean.mkConst ``List.cons [1]) chunkTy c acc)
      (mkApp (Lean.mkConst ``List.nil [1]) chunkTy)
    let chunksNm := auxNs ++ `chunks
    liftCoreM <| addCertDef chunksNm listChunkTy chunksVal inp.compileCert
    let linkCheckNm := auxNs ++ `link_check
    let linkLhs := mkAppN (Lean.mkConst ``LeanQbe.T.checkLinkList)
      #[inp.targE, inp.layoutE, inp.ltE, inp.exitsE, inp.nXE, inp.ext0E, Lean.mkConst chunksNm]
    liftCoreM <| addKernelEqThm linkCheckNm (Lean.mkConst ``Bool)
      linkLhs (Lean.mkConst ``Bool.true) .zero
    -- Build O(#chunks) proofs of `mod.fns = chunksFns chunks`, `supportsAll`, and `maxBound_le`
    let fnsEqNm := auxNs ++ `fns_eq
    let suppAllNm := auxNs ++ `supportsAll
    let maxBLeNm := auxNs ++ `maxBound_le
    let chunksFnsE := mkAppN (Lean.mkConst ``LeanQbe.T.chunksFns)
      #[inp.targE, inp.ltE, inp.exitsE, inp.nXE, Lean.mkConst chunksNm]
    let fnsEqTy := mkApp3 (Lean.mkConst ``Eq [2]) listFnTy fnsBaseE chunksFnsE
    let mut fnsEqProof : Lean.Expr := default
    let mut restFnsE : Lean.Expr := mkApp (Lean.mkConst ``List.nil [1]) fnTy
    let mut suppProof : Lean.Expr := mkApp (Lean.mkConst ``LeanQbe.T.supportsAll_nil) inp.ltE
    let mut maxBProof : Lean.Expr := mkAppN (Lean.mkConst ``LeanQbe.T.chunksMaxBound_nil)
      #[inp.targE, inp.ltE, inp.exitsE, inp.nXE, inp.maxBE]
    let mut restChunksE : Lean.Expr := mkApp (Lean.mkConst ``List.nil [1]) chunkTy
    let nChunks := chunkNames.size
    for revIdx in [:nChunks] do
      let i := nChunks - 1 - revIdx
      let (fnsNm, _, _, _, _, _, _, suppNm, _, ch) := chunkNames[i]!
      let chunkVal := chunkEntries[i]!
      let curFnsE := Lean.mkConst fnsNm
      if revIdx == 0 then
        fnsEqProof := mkApp3 (Lean.mkConst ``LeanQbe.T.slice_last_eq [1])
          fnTy fnsBaseE (mkNatLit ch.startIdx)
      else
        fnsEqProof := mkApp6 (Lean.mkConst ``LeanQbe.T.slice_cons_eq [1])
          fnTy fnsBaseE restFnsE (mkNatLit ch.startIdx) (mkNatLit ch.fnCount) fnsEqProof
      suppProof := mkApp5 (Lean.mkConst ``LeanQbe.T.supportsAll_append)
        inp.ltE curFnsE restFnsE (Lean.mkConst suppNm) suppProof
      maxBProof := mkAppN (Lean.mkConst ``LeanQbe.T.chunksMaxBound_cons)
        #[inp.targE, inp.ltE, inp.exitsE, inp.nXE, inp.maxBE, chunkVal, restChunksE,
          mkApp (Lean.mkConst ``Nat.le_refl) inp.maxBE, maxBProof]
      restFnsE := mkApp3 (Lean.mkConst ``List.append [1]) fnTy curFnsE restFnsE
      restChunksE := mkApp3 (Lean.mkConst ``List.cons [1]) chunkTy chunkVal restChunksE
    -- Emit `fns_eq`, `supportsAll`, `maxBound_le`, and the final `LinkedCert`
    liftCoreM <| addCertThm fnsEqNm fnsEqTy fnsEqProof
    let (suppAllTy, suppAllVal, maxBLeProp) ← liftTermElabM do
      let sVal ← mkAppM ``LeanQbe.T.supportsAll_of_eq #[Lean.mkConst fnsEqNm, suppProof]
      let sTy ← inferType sVal
      let lhs := mkAppN (Lean.mkConst ``LeanQbe.T.chunksMaxBound)
        #[inp.targE, inp.ltE, inp.exitsE, inp.nXE, Lean.mkConst chunksNm]
      let mProp ← mkAppM ``LE.le #[lhs, inp.maxBE]
      return (← instantiateMVars sTy, ← instantiateMVars sVal, ← instantiateMVars mProp)
    liftCoreM do
      addCertThm suppAllNm suppAllTy suppAllVal
      addCertThm maxBLeNm maxBLeProp maxBProof
    let certTy := mkAppN (Lean.mkConst ``LeanQbe.T.LinkedCert)
      #[inp.targE, inp.layoutE, inp.ltE, inp.clE, inp.modE,
        inp.ext0E, inp.exitsE, inp.nXE, inp.maxBE]
    let certVal := mkAppN (Lean.mkConst ``LeanQbe.T.LinkedCert.mk)
      #[inp.targE, inp.layoutE, inp.ltE, inp.clE, inp.modE,
        inp.ext0E, inp.exitsE, inp.nXE, inp.maxBE,
        Lean.mkConst chunksNm, Lean.mkConst linkCheckNm, Lean.mkConst fnsEqNm,
        Lean.mkConst suppAllNm, Lean.mkConst maxBLeNm]
    liftCoreM do
      addCertDef certNm certTy certVal inp.compileCert
      addCertDef (certNm ++ `exportedExt) listExtTy inp.finalExtLit inp.compileExt

/-- Evaluates `evalOneFnBound` in order over `fs` starting from `ext0`, returning `(totalLen,
extLit)` where `extLit` is the literal `List (SigEntry × Nat)` expression `(sig, b) :: acc`
matching `compileModule`'s reverse accumulator order. -/
def evalPrefixExtWithLen (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX maxBound : Nat)
    (fs : List Fn) : Except String (Nat × Lean.Expr) := do
  let tasks := fs.map fun f => Task.spawn fun () => evalOneFnBoundStage1 I lt f
  let rec go (acc : List (SigEntry × Nat)) :
      List (Task (Except String (Sym × I.Hints × Rega.Ext × SigEntry))) →
      Except String (List (SigEntry × Nat))
    | [] => .ok acc
    | t :: rest => do
      let (nm, h, ext, sig) ← t.get
      let b ← evalOneFnBoundCheck I raBytes exits nX maxBound acc nm h ext
      go ((sig, b) :: acc) rest
  let out ← go ext0 tasks
  pure (out.length, Lean.toExpr out)

/-- Evaluates `evalOneFnBound` in order over `fs` starting from `ext0`, returning the literal
`List (SigEntry × Nat)` expression `(sig, b) :: acc` matching `compileModule`'s accumulator. -/
def evalPrefixExt (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX maxBound : Nat)
    (fs : List Fn) : Except String Lean.Expr :=
  Prod.snd <$> evalPrefixExtWithLen I lt raBytes ext0 exits nX maxBound fs

def parsePrefixExtOptions (optKeys : TSyntaxArray `ident) (optVals : TSyntaxArray `term) :
    CommandElabM (Option Term × Option Term × Option Term × Option Term × Option Ident) := do
  let mut maxBT? : Option Term := none
  let mut extT? : Option Term := none
  let mut exitsT? : Option Term := none
  let mut nXT? : Option Term := none
  let mut prefixId? : Option Ident := none
  for i in [:optKeys.size] do
    let k := optKeys[i]!.getId
    let v := optVals[i]!
    match k with
    | `maxBound => maxBT? := some v
    | `ext => extT? := some v
    | `exits => exitsT? := some v
    | `nX => nXT? := some v
    | `prefixDef =>
      if let `($id:ident) := v then
        prefixId? := some id
      else
        throwErrorAt v "eval_prefix_ext!: prefixDef must be an identifier"
    | _ =>
      throwErrorAt optKeys[i]!
        "eval_prefix_ext!: unknown option '{k}'; expected maxBound, ext, exits, nX, prefixDef"
  return (maxBT?, extT?, exitsT?, nXT?, prefixId?)

def elabAndEvalPrefixExt (targT ltT fnsT : Term)
    (maxBT? extT? exitsT? nXT? : Option Term) : TermElabM (Lean.Expr × Nat × Lean.Expr) := do
  let targE ← Term.elabTerm targT (some (Lean.mkConst ``LeanQbe.T.Target))
  let ltE ← Term.elabTerm ltT (some (Lean.mkConst ``LeanQbe.T.LegalTarget))
  let listFnTy := mkApp (Lean.mkConst ``List [1]) (Lean.mkConst ``LeanQbe.T.Fn)
  let fnsE ← Term.elabTerm fnsT (some listFnTy)
  let sigEntryNatTy :=
    mkApp2 (Lean.mkConst ``Prod [.zero, .zero])
      (Lean.mkConst ``LeanQbe.T.SigEntry) (Lean.mkConst ``Nat)
  let listExtTy := mkApp (Lean.mkConst ``List [.zero]) sigEntryNatTy
  let listSymTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.Sym)
  let ext0E ← match extT? with
    | some t => Term.elabTerm t (some listExtTy)
    | none => pure (mkApp (Lean.mkConst ``List.nil [.zero]) sigEntryNatTy)
  let exitsE ← match exitsT? with
    | some t => Term.elabTerm t (some listSymTy)
    | none => pure (mkApp (Lean.mkConst ``List.nil [.zero]) (Lean.mkConst ``LeanQbe.T.Sym))
  let nXE ← match nXT? with
    | some t => Term.elabTerm t (some (Lean.mkConst ``Nat))
    | none => pure (mkNatLit 0)
  let maxBE ← match maxBT? with
    | some t => Term.elabTerm t (some (Lean.mkConst ``Nat))
    | none => pure (mkNatLit 2048)
  Term.synthesizeSyntheticMVarsNoPostponing
  let targE ← instantiateMVars targE
  let ltE ← instantiateMVars ltE
  let fnsE ← instantiateMVars fnsE
  let ext0E ← instantiateMVars ext0E
  let exitsE ← instantiateMVars exitsE
  let nXE ← instantiateMVars nXE
  let maxBE ← instantiateMVars maxBE
  let isaE := mkApp (Lean.mkConst ``LeanQbe.T.Target.toIsa) targE
  let frameE ← mkAppM ``LeanQbe.T.Isa.frame #[isaE]
  let raE ← mkAppM ``LeanQbe.T.FrameIsa.raBytes #[frameE]
  let callE ← instantiateMVars (mkAppN (Lean.mkConst ``LeanQbe.T.evalPrefixExtWithLen)
    #[isaE, ltE, raE, ext0E, exitsE, nXE, maxBE, fnsE])
  let pairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero])
    (Lean.mkConst ``Nat) (Lean.mkConst ``Lean.Expr)
  let outTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero]) (Lean.mkConst ``String) pairTy
  let evalRes ← unsafe evalExpr (Except String (Nat × Lean.Expr)) outTy callE
  match evalRes with
  | .error e => throwError "eval_prefix_ext!: {e}"
  | .ok (total, extLit) => return (listExtTy, total, extLit)

/-- `eval_prefix_ext! extName target legalTarget fnsExpr [(ext := ...)] [(exits := ...)]
[(nX := ...)] [(maxBound := ...)] [(prefixDef := ...)]` runs `evalOneFnBound` in compiled meta
code over `fnsExpr` starting from `ext` (default `[]`) and emits `def extName : List (SigEntry ×
Nat) := <literal>` matching `compileModule`'s `(sig, bound) :: acc` reverse order. When
`(prefixDef := pfxName)` is supplied, also emits `def pfxName (k : Nat) : List (SigEntry × Nat) :=
extName.drop (total - k)` for `O(1)` prefix slicing across parallel certs. -/
scoped syntax "eval_prefix_ext! " ident
    term:arg term:arg term:arg
    ("(" ident " := " term ")")* : command

scoped elab_rules : command
  | `(eval_prefix_ext! $extId $targT $ltT $fnsT $[($optKeys := $optVals)]*) => do
    let ns ← getCurrNamespace
    let extNm := ns ++ extId.getId
    let (maxBT?, extT?, exitsT?, nXT?, prefixId?) ← parsePrefixExtOptions optKeys optVals
    let (listExtTy, total, extLit) ← liftTermElabM <|
      elabAndEvalPrefixExt targT ltT fnsT maxBT? extT? exitsT? nXT?
    liftCoreM do
      addCertDef extNm listExtTy extLit
      if let some pfxId := prefixId? then
        let pfxNm := ns ++ pfxId.getId
        let natTy := Lean.mkConst ``Nat
        let symEntryNatTy :=
          mkApp2 (Lean.mkConst ``Prod [.zero, .zero])
            (Lean.mkConst ``LeanQbe.T.SigEntry) natTy
        let dropIdx := mkApp2 (Lean.mkConst ``Nat.sub) (mkNatLit total) (mkBVar 0)
        let dropVal := mkApp3 (Lean.mkConst ``List.drop [.zero])
          symEntryNatTy dropIdx (Lean.mkConst extNm)
        let pfxTy := Lean.mkForall `k .default natTy listExtTy
        let pfxVal := Lean.mkLambda `k .default natTy dropVal
        addCertDef pfxNm pfxTy pfxVal

end

end LeanQbe.T
