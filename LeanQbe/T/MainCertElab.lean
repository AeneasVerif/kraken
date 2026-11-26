module

public import LeanQbe.T.MainCertCore
public meta import Lean
public meta import LeanQbe.T.MainLink
public meta import LeanQbe.T.MainCertCore
public meta import LeanQbe.T.MainCertFlatDecode
public meta import LeanQbe.T.MainLinkSplice
public meta import LeanQbe.T.MainSplice

/-!
# Meta Chunk & Prefix-Bound Certificate Elaborators (`MainCertElab`)

Meta evaluators, shared elaborator primitives, and `scoped` command elaborators
(`compile_linked_chunks!`, `eval_prefix_ext!`) emitting kernel-checked `LinkedCert` certificates
and `(SigEntry × Nat)` prefix bounds over `LeanQbe.T.MainCertCore`.

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

private def matFn (fn : Fn) : Fn := ⟨fn.name, fn.as, fn.rs, denoteFunc (reifyFunc fn.body)⟩

/-- Independent per-function meta prepass (`earlyOpt → supportsSource → legal → lateOpt →
`Spill.hints` → `mf.ext`), safe to evaluate across worker tasks before sequential linking. -/
def evalOneFnStage1 (I : Isa) (lt : LegalTarget) (f : Fn) :
    Except String (Sym × I.Hints × Fn × Rega.Ext) :=
  let ef := matFn f.earlyOpt
  if !ef.body.supportsSource lt then .error s!"{f.name}: unsupported source op for target"
  else let mf := Fn.midFromEarly lt ef; .ok (f.name, Spill.hints I mf, mf, mf.ext)

/-- Sequential callee stack-bound check over pre-evaluated `Spill.hints` and `Rega.Ext`. -/
def evalOneFnBoundCheck (I : Isa) (raBytes : Nat) (exits : List Sym) (nX maxBound : Nat)
    (acc : List (SigEntry × Nat)) (name : Sym) (h : I.Hints) (ext : Rega.Ext) :
    Except String Nat :=
  match checkAndBoundExt I raBytes exits nX acc h ext with
  | some b =>
    if !Nat.ble b maxBound then .error s!"{name}: stack bound {b} exceeds maxBound={maxBound}"
    else .ok b
  | none => .error s!"{name}: unknown callee, undeclared exit, or stack overflow"

/-- Bound-only stage-1 prepass (drops `Fn` body immediately so tasks retain no ASTs). -/
def evalOneFnBoundStage1 (I : Isa) (lt : LegalTarget) (f : Fn) :
    Except String (Sym × I.Hints × Rega.Ext × SigEntry) :=
  match evalOneFnStage1 I lt f with
  | .error e => .error e | .ok (nm, h, mf, ext) => .ok (nm, h, ext, mf.sig)

/-- Fast bound-only meta pass matching `evalOneFn`'s computed `(bound, sig)`. -/
def evalOneFnBound (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (exits : List Sym) (nX maxBound : Nat) (acc : List (SigEntry × Nat)) (f : Fn) :
    Except String (Nat × SigEntry) := do
  let (nm, h, ext, sig) ← evalOneFnBoundStage1 I lt f
  .ok (← evalOneFnBoundCheck I raBytes exits nX maxBound acc nm h ext, sig)

/-- Single-function fused meta pass matching `compileModule` without repeating `earlyOpt`/`mid`. -/
def evalOneFn (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (exits : List Sym) (nX maxBound : Nat) (acc : List (SigEntry × Nat)) (f : Fn) :
    Except String (I.Hints × List I.Directive × Nat × SigEntry) :=
  match evalOneFnStage1 I lt f with
  | .error e => .error e
  | .ok (nm, h, mf, ext) =>
    match Rega.lowerFn I h ext mf, evalOneFnBoundCheck I raBytes exits nX maxBound acc nm h ext with
    | .ok c, .ok b => .ok (h, c, b, mf.sig)
    | .error e, _ => .error s!"{nm}: {e}"
    | _, .error e => .error e

/-- Deduplicate `callees` (by `SigEntry.beq`) and retain only their entries from `acc`,
yielding a minimal literal `extCallees` table for pruned-`ext` chunk compilation (`N4`). -/
def pruneExtCallees (callees : List SigEntry)
    (acc : List (SigEntry × Nat)) : List (SigEntry × Nat) :=
  let uniq := callees.foldl (fun seen g =>
    if seen.any (SigEntry.beq · g) then seen else seen ++ [g]) []
  uniq.filterMap fun g => (lookupBound acc g).map fun b => (g, b)

/-- Spawn stage-1 + `Rega.lowerFn` across worker threads and collect outputs in source order. -/
def spawnLowerItems {α β : Type _} (I : Isa) (lt : LegalTarget) (xs : List α)
    (getFn : α → Fn) (mkOut : Sym → I.Hints → List I.Directive → Fn → Rega.Ext → α → β) :
    Except String (List β) :=
  let tasks := xs.map fun x => Task.spawn fun () =>
    match evalOneFnStage1 I lt (getFn x) with
    | .error e => .error e
    | .ok (nm, h, mf, ext) =>
      match Rega.lowerFn I h ext mf with
      | .ok c => .ok (mkOut nm h c mf ext x) | .error e => .error s!"{nm}: {e}"
  let rec collect : List (Task (Except String β)) → Except String (List β)
    | [] => .ok [] | t :: ts => do let v ← t.get; .ok (v :: (← collect ts))
  collect tasks

/-- Greedily take a chunk prefix bounded by item count `k` and optional directive cap `maxDirs`. -/
def takeDirBounded {α : Type _} (k maxDirs : Nat) (getDirs : α → Nat) (first : α)
    (rest : List α) : List α × List α :=
  let rec go (cnt dirSum : Nat) (rev : List α) : List α → List α × List α
    | [] => (rev.reverse, [])
    | x :: xs =>
      let nextDirs := dirSum + getDirs x
      if cnt < k && (maxDirs == 0 || nextDirs <= maxDirs) then
        go (cnt + 1) nextDirs (x :: rev) xs
      else (rev.reverse, x :: xs)
  go 1 (getDirs first) [first] rest

/-- Shared chunk binder/grouper over pre-lowered `(name, hints, code, ext, sig)` records, reused
by both PHOAS (`evalLinkedChunks`) and flat (`MainCertFlatElab.evalLinkedChunksFlat`). -/
def evalLinkedChunksCore (I : Isa) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (chunkSize maxBound maxDirs : Nat) (pruneExt : Bool := false)
    (lowered : List (Sym × I.Hints × List I.Directive × Rega.Ext × SigEntry))
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)] :
    Except String EvalModuleData := do
  let k := Nat.max chunkSize 1
  if lowered.isEmpty then
    let extLit := Lean.toExpr (if pruneExt then ([] : List (SigEntry × Nat)) else ext0)
    pure {
      chunks := [{
        startIdx := 0, fnCount := 0, isLast := true, extLit := extLit
        hintsLit := Lean.toExpr ([] : List I.Hints)
        codeLit := Lean.toExpr ([] : List I.Directive)
        boundsLit := Lean.toExpr ([] : List (Sym × Nat))
      }]
      finalExtLit := Lean.toExpr ext0
    }
  else
    let rec bindAll (acc : List (SigEntry × Nat)) :
        List (Sym × I.Hints × List I.Directive × Rega.Ext × SigEntry) →
        Except String (List (Sym × I.Hints × List I.Directive × Nat × SigEntry × Rega.Ext))
      | [] => .ok []
      | (nm, h, c, ext, sig) :: rest => do
        let b ← evalOneFnBoundCheck I raBytes exits nX maxBound acc nm h ext
        .ok ((nm, h, c, b, sig, ext) :: (← bindAll ((sig, b) :: acc) rest))
    let compiled ← bindAll ext0 lowered
    let rec groupChunks : Nat → Nat → List (SigEntry × Nat) →
        List (Sym × I.Hints × List I.Directive × Nat × SigEntry × Rega.Ext) →
        List EvalChunkData → EvalModuleData
      | 0, _, acc, _, out | _, _, acc, [], out =>
        { chunks := out.reverse, finalExtLit := Lean.toExpr acc }
      | fuel + 1, idx, acc, first :: rest, out =>
        let (grp, rest') := takeDirBounded k maxDirs (·.2.2.1.length) first rest
        let chunkExt :=
          if pruneExt then
            pruneExtCallees (grp.foldr (fun x cs => x.2.2.2.2.2.callees ++ cs) []) acc
          else acc
        let entry : EvalChunkData := {
          startIdx := idx, fnCount := grp.length, isLast := rest'.isEmpty
          extLit := Lean.toExpr chunkExt, hintsLit := Lean.toExpr (grp.map (·.2.1))
          codeLit := Lean.toExpr (grp.foldr (fun x cs => x.2.2.1 ++ cs) [])
          boundsLit := Lean.toExpr (grp.map fun x => (x.1, x.2.2.2.1))
        }
        let sigs := grp.map fun x => (x.2.2.2.2.1, x.2.2.2.1)
        groupChunks fuel (idx + grp.length) (sigs.reverse ++ acc) rest' (entry :: out)
    pure (groupChunks (compiled.length + 1) 0 ext0 compiled [])

/-- Compiled meta evaluator splitting `fs` into callee-first chunks bounded by `chunkSize` and
optional `maxDirs`, returning literal `Lean.Expr` data for every chunk. When `pruneExt` is `true`,
each chunk's `extLit` contains only direct `ext.callees` bounds looked up in `acc`. -/
def evalLinkedChunks (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (fs : List Fn) (chunkSize maxBound maxDirs : Nat)
    (pruneExt : Bool := false)
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)] :
    Except String EvalModuleData := do
  let lowered ← spawnLowerItems I lt fs id fun nm h c mf ext _ => (nm, h, c, ext, mf.sig)
  evalLinkedChunksCore I raBytes ext0 exits nX chunkSize maxBound maxDirs pruneExt lowered

/-- Curried meta chunk evaluator over decoded `List TFlatFn` (converting via `TFlatFn.toFn`). -/
def makeChunkEvaluator (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym)
    (nX chunkSize maxBound maxDirs : Nat) (pruneExt : Bool := false)
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)] :
    List TFlatFn → Except String EvalModuleData :=
  fun fs =>
    evalLinkedChunks I lt raBytes ext0 exits nX (fs.map TFlatFn.toFn)
      chunkSize maxBound maxDirs pruneExt

def addCertDef (declNm : Name) (ty val : Lean.Expr) (compile : Bool := true) : CoreM Unit :=
  withCurrHeartbeats do
    let decl := Declaration.defnDecl {
      name := declNm, levelParams := [], type := ty, value := val,
      hints := .abbrev, safety := .safe }
    addDecl decl (forceExpose := true)
    if compile then compileDecl decl else modifyEnv (Lean.addNoncomputable · declNm)

def addCertThm (declNm : Name) (ty val : Lean.Expr) : CoreM Unit :=
  withCurrHeartbeats do
    addDecl (Declaration.thmDecl { name := declNm, levelParams := [], type := ty, value := val })

def addKernelEqThm (declNm : Name) (eqTy lhs rhs : Lean.Expr) (u : Level) : CoreM Unit :=
  addCertThm declNm (mkApp3 (Lean.mkConst ``Eq [u.succ]) eqTy lhs rhs)
    (mkApp2 (Lean.mkConst ``Eq.refl [u.succ]) eqTy lhs)

/-- Build a kernel `List` literal expression at universe `u`. -/
def mkExprList (u : Level) (elemTy : Lean.Expr) (elems : List Lean.Expr) : Lean.Expr :=
  elems.foldr (fun e acc => mkApp3 (Lean.mkConst ``List.cons [u]) elemTy e acc)
    (mkApp (Lean.mkConst ``List.nil [u]) elemTy)

/-- Build a `List.drop`/`List.take` slice expression over `baseListE` at universe `u`. -/
def mkSliceExpr (elemTy baseListE : Lean.Expr) (startIdx fnCount : Nat)
    (isLast : Bool) (u : Level := 1) : Lean.Expr :=
  let dropE := mkApp3 (Lean.mkConst ``List.drop [u]) elemTy (mkNatLit startIdx) baseListE
  if isLast then dropE else mkApp3 (Lean.mkConst ``List.take [u]) elemTy (mkNatLit fnCount) dropE

/-- Common type constants reused across certificate elaborators. -/
structure CertTypes where
  fnTy : Lean.Expr
  listFnTy : Lean.Expr
  symTy : Lean.Expr
  sigTy : Lean.Expr
  listSigTy : Lean.Expr
  natTy : Lean.Expr
  sigEntryNatTy : Lean.Expr
  listExtTy : Lean.Expr
  symNatTy : Lean.Expr
  listBoundsTy : Lean.Expr
  pairNatTy : Lean.Expr

def mkCertTypes : CertTypes :=
  let fnTy := Lean.mkConst ``LeanQbe.T.Fn
  let symTy := Lean.mkConst ``LeanQbe.T.Sym
  let sigTy := Lean.mkConst ``LeanQbe.T.SigEntry
  let natTy := Lean.mkConst ``Nat
  let sigEntryNatTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) sigTy natTy
  let symNatTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) symTy natTy
  { fnTy, listFnTy := mkApp (Lean.mkConst ``List [1]) fnTy, symTy, sigTy,
    listSigTy := mkApp (Lean.mkConst ``List [.zero]) sigTy, natTy, sigEntryNatTy,
    listExtTy := mkApp (Lean.mkConst ``List [.zero]) sigEntryNatTy, symNatTy,
    listBoundsTy := mkApp (Lean.mkConst ``List [.zero]) symNatTy,
    pairNatTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) natTy natTy }

def elabOptTerm (opt? : Option Term) (ty defaultE : Lean.Expr) : TermElabM Lean.Expr :=
  match opt? with | some t => Term.elabTerm t (some ty) | none => pure defaultE

/-- Elaborate `(ext0, exits, nX, maxBound)` terms shared by all cert commands. -/
def elabCommonBoundArgs (extT? exitsT? nXT? maxBT? : Option Term) :
    TermElabM (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := do
  let tys := mkCertTypes
  let ext0E ← elabOptTerm extT? tys.listExtTy
    (mkApp (Lean.mkConst ``List.nil [.zero]) tys.sigEntryNatTy)
  let exitsE ← elabOptTerm exitsT? (mkApp (Lean.mkConst ``List [.zero]) tys.symTy)
    (mkApp (Lean.mkConst ``List.nil [.zero]) tys.symTy)
  let nXE ← elabOptTerm nXT? tys.natTy (mkNatLit 0)
  let maxBE ← elabOptTerm maxBT? tys.natTy (mkNatLit 2048)
  return (ext0E, exitsE, nXE, maxBE)

structure CertOptions where
  maxBT? : Option Term := none
  extT? : Option Term := none
  exitsT? : Option Term := none
  nXT? : Option Term := none
  maxDirsT? : Option Term := none
  compileT? : Option Term := none
  compileExtT? : Option Term := none
  pruneExtT? : Option Term := none
  flatT? : Option Term := none
  deriving Inhabited

/-- Shared base target/layout/option fields elaborated for both acyclic and SCC certs. -/
structure CertBaseEnv where
  targE : Lean.Expr
  layoutE : Lean.Expr
  ltE : Lean.Expr
  clE : Lean.Expr
  isaE : Lean.Expr
  raE : Lean.Expr
  labelE : Lean.Expr
  progSmallE : Lean.Expr
  dirTy : Lean.Expr
  listDirTy : Lean.Expr
  listHintsTy : Lean.Expr
  toExprHintsInst : Lean.Expr
  toExprDirInst : Lean.Expr
  ext0E : Lean.Expr
  exitsE : Lean.Expr
  nXE : Lean.Expr
  maxBE : Lean.Expr
  maxDirsE : Lean.Expr
  compileCert : Bool
  compileExt : Bool

/-- Elaborated inputs for `compile_linked_chunks!`. -/
structure CertInputs where
  base : CertBaseEnv
  modE : Lean.Expr
  chunks : List EvalChunkData
  finalExtLit : Lean.Expr
  flat? : Option (Lean.Expr × Lean.Expr) := none

/-- Shared key-value option parser used across certificate commands. -/
def parseKvOptions {α : Type} (cmd expected : String) (init : α)
    (step : α → Name → Term → CommandElabM (Option α))
    (optKeys : TSyntaxArray `ident) (optVals : TSyntaxArray `term) : CommandElabM α := do
  let mut st := init
  for i in [:optKeys.size] do
    let k := optKeys[i]!.getId; let v := optVals[i]!
    match ← step st k v with
    | some st' => st := st'
    | none => throwErrorAt optKeys[i]! "{cmd}: unknown option '{k}'; expected {expected}"
  return st

def parseCertOptions (optKeys : TSyntaxArray `ident) (optVals : TSyntaxArray `term) :
    CommandElabM CertOptions :=
  parseKvOptions "compile_linked_chunks!"
    "maxBound, ext, exits, nX, maxDirs, compile, compileExt, pruneExt, flat" {}
    (fun opts k v => pure <| match k with
      | `maxBound => some { opts with maxBT? := some v }
      | `ext => some { opts with extT? := some v }
      | `exits => some { opts with exitsT? := some v }
      | `nX => some { opts with nXT? := some v }
      | `maxDirs => some { opts with maxDirsT? := some v }
      | `compile => some { opts with compileT? := some v }
      | `compileExt => some { opts with compileExtT? := some v }
      | `pruneExt => some { opts with pruneExtT? := some v }
      | `flat => some { opts with flatT? := some v }
      | _ => none) optKeys optVals

def evalBoolOpt (opt? : Option Term) (defaultVal : Bool) : TermElabM Bool := do
  match opt? with
  | none => pure defaultVal
  | some t =>
    let e ← Term.elabTerm t (some (Lean.mkConst ``Bool))
    Term.synthesizeSyntheticMVarsNoPostponing
    unsafe evalExpr Bool (Lean.mkConst ``Bool) (← instantiateMVars e)

/-- Synthesize `Lean.ToExpr` instances for `List I.Hints` and `List I.Directive`. -/
def synthIsaToExpr (isaE : Lean.Expr) : TermElabM (Lean.Expr × Lean.Expr) := do
  let regTy ← whnf (mkApp (Lean.mkConst ``LeanQbe.T.Isa.Reg) isaE)
  let vregTy ← whnf (mkApp (Lean.mkConst ``LeanQbe.T.Isa.VReg) isaE)
  let condTy ← whnf (mkApp (Lean.mkConst ``LeanQbe.T.Isa.Cond) isaE)
  let hintTy := mkApp3 (Lean.mkConst ``LeanQbe.T.Hints) regTy vregTy condTy
  let dirTy ← whnf (mkApp (Lean.mkConst ``LeanQbe.T.Isa.Directive) isaE)
  let hInst ← synthInstance
    (mkApp (Lean.mkConst ``Lean.ToExpr [.zero]) (mkApp (Lean.mkConst ``List [.zero]) hintTy))
  let dInst ← synthInstance
    (mkApp (Lean.mkConst ``Lean.ToExpr [.zero]) (mkApp (Lean.mkConst ``List [.zero]) dirTy))
  return (hInst, dInst)

/-- Elaborate common target, layout, labelClean, option terms, and ISA meta instances. -/
def elabCertBase (targT layoutT ltT clT : Term) (opts : CertOptions) : TermElabM CertBaseEnv := do
  let tys := mkCertTypes
  let targE ← Term.elabTerm targT (some (Lean.mkConst ``LeanQbe.T.Target))
  let layoutE ← Term.elabTerm layoutT (some (mkApp (Lean.mkConst ``LeanQbe.T.TargetLayout) targE))
  let ltE ← Term.elabTerm ltT (some (Lean.mkConst ``LeanQbe.T.LegalTarget))
  let isaE := mkApp (Lean.mkConst ``LeanQbe.T.Target.toIsa) targE
  let clE ← Term.elabTerm clT (some (mkApp (Lean.mkConst ``LeanQbe.T.Rega.LabelClean) isaE))
  let (ext0E, exitsE, nXE, maxBE) ←
    elabCommonBoundArgs opts.extT? opts.exitsT? opts.nXT? opts.maxBT?
  let maxDirsE ← elabOptTerm opts.maxDirsT? tys.natTy (mkNatLit 0)
  let compileCert ← evalBoolOpt opts.compileT? false
  let compileExt ← evalBoolOpt opts.compileExtT? false
  Term.synthesizeSyntheticMVarsNoPostponing
  let targE ← instantiateMVars targE; let layoutE ← instantiateMVars layoutE
  let ltE ← instantiateMVars ltE; let clE ← instantiateMVars clE
  let isaE ← instantiateMVars isaE; let ext0E ← instantiateMVars ext0E
  let exitsE ← instantiateMVars exitsE; let nXE ← instantiateMVars nXE
  let maxBE ← instantiateMVars maxBE; let maxDirsE ← instantiateMVars maxDirsE
  let (toExprHintsInst, toExprDirInst) ← synthIsaToExpr isaE
  let frameE ← mkAppM ``LeanQbe.T.Isa.frame #[isaE]
  let raE ← mkAppM ``LeanQbe.T.FrameIsa.raBytes #[frameE]
  let labelE ← mkAppM ``LeanQbe.T.FrameIsa.label #[frameE]
  let progSmallE ← mkAppM ``LeanQbe.T.TargetLayout.progSmall #[layoutE]
  let dirTy := mkApp (Lean.mkConst ``LeanQbe.T.Isa.Directive) isaE
  let listDirTy := mkApp (Lean.mkConst ``List [.zero]) dirTy
  let listHintsTy := mkApp (Lean.mkConst ``List [.zero])
    (mkApp (Lean.mkConst ``LeanQbe.T.Isa.Hints) isaE)
  return {
    targE, layoutE, ltE, clE, isaE, raE, labelE, progSmallE, dirTy, listDirTy, listHintsTy,
    toExprHintsInst, toExprDirInst, ext0E, exitsE, nXE, maxBE, maxDirsE, compileCert, compileExt
  }

/-- Emitted declaration names for one `.acyc` chunk (shared by `MainCertElab` & `MainCertScc`). -/
structure AcycChunkNames where
  startIdx : Nat
  fnCount : Nat
  isLast : Bool := false
  fnsNm : Name
  hintsNm : Name
  extNm : Name
  codeNm : Name
  boundsNm : Name
  cmNm : Name
  metaNm : Name
  compNm : Name
  flatNm? : Option Name := none
  cmFlatNm? : Option Name := none
  deriving Inhabited

/-- Pass-1 emission of literal definitions for one `.acyc` chunk. -/
def emitAcycChunkDefs (auxNs : Name) (pfx : String) (compileCert : Bool)
    (fnsBaseE listHintsTy listDirTy : Lean.Expr) (ch : EvalChunkData)
    (flatBaseE? : Option Lean.Expr := none) :
    CommandElabM AcycChunkNames := do
  let tys := mkCertTypes
  let nm := fun s => auxNs ++ Name.mkSimple s!"{pfx}_{s}"
  let fnsNm := nm "fns"; let hintsNm := nm "hints"; let extNm := nm "ext"
  let codeNm := nm "code"; let boundsNm := nm "bounds"
  let sliceE := mkSliceExpr tys.fnTy fnsBaseE ch.startIdx ch.fnCount ch.isLast
  let flatNm? := flatBaseE?.map fun _ => nm "flat"
  let cmFlatNm? := flatBaseE?.map fun _ => nm "cm_flat"
  liftCoreM do
    addCertDef fnsNm tys.listFnTy sliceE compileCert
    addCertDef hintsNm listHintsTy ch.hintsLit compileCert
    addCertDef extNm tys.listExtTy ch.extLit compileCert
    addCertDef codeNm listDirTy ch.codeLit compileCert
    addCertDef boundsNm tys.listBoundsTy ch.boundsLit compileCert
    if let (some flatBaseE, some flatNm) := (flatBaseE?, flatNm?) then
      let flatTy := Lean.mkConst ``LeanQbe.T.TFlatFn
      let listFlatTy := mkApp (Lean.mkConst ``List [.zero]) flatTy
      let flatSliceE := mkSliceExpr flatTy flatBaseE ch.startIdx ch.fnCount ch.isLast .zero
      addCertDef flatNm listFlatTy flatSliceE false
  return {
    startIdx := ch.startIdx, fnCount := ch.fnCount, isLast := ch.isLast,
    fnsNm, hintsNm, extNm, codeNm, boundsNm,
    cmNm := nm "cm", metaNm := nm "meta", compNm := nm "compiled",
    flatNm?, cmFlatNm?
  }

/-- Pass-2 kernel equality theorems (`compileModule` & `checkCompileLit`) for `.acyc`.
When `flatCtx?` and `ac.flatNm?`/`ac.cmFlatNm?` are present, reduces `compileModuleFlat` in the
kernel and derives `ac.cmNm` in O(1) via `compileModule_of_flat_eq`. -/
def emitAcycChunkThms (b : CertBaseEnv) (ac : AcycChunkNames)
    (flatCtx? : Option (Lean.Expr × Lean.Expr × Name) := none) : CoreM Unit := do
  let tys := mkCertTypes
  let okPairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) b.listDirTy tys.listBoundsTy
  let excTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero]) (Lean.mkConst ``String) okPairTy
  let cmLhs := mkAppN (Lean.mkConst ``LeanQbe.T.compileModule)
    #[b.isaE, b.ltE, b.raE, Lean.mkConst ac.extNm, b.exitsE, b.nXE,
      Lean.mkConst ac.fnsNm, Lean.mkConst ac.hintsNm]
  let cmRhs := mkApp3 (Lean.mkConst ``Except.ok [.zero, .zero]) (Lean.mkConst ``String) okPairTy
    (mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) b.listDirTy tys.listBoundsTy
      (Lean.mkConst ac.codeNm) (Lean.mkConst ac.boundsNm))
  match flatCtx?, ac.flatNm?, ac.cmFlatNm? with
  | some (fnsBaseE, flatFnsConstE, fnsFlatEqNm), some flatNm, some cmFlatNm =>
    let flatTy := Lean.mkConst ``LeanQbe.T.TFlatFn
    let cmFlatLhs := mkAppN (Lean.mkConst `LeanQbe.T.compileModuleFlat)
      #[b.isaE, b.ltE, b.raE, Lean.mkConst ac.extNm, b.exitsE, b.nXE,
        Lean.mkConst flatNm, Lean.mkConst ac.hintsNm]
    addKernelEqThm cmFlatNm excTy cmFlatLhs cmRhs .zero
    let sliceEqPf := if ac.isLast then
      mkAppN (Lean.mkConst `LeanQbe.T.map_drop_eq [.zero, .one])
        #[flatTy, tys.fnTy, Lean.mkConst ``LeanQbe.T.TFlatFn.toFn, fnsBaseE, flatFnsConstE,
          Lean.mkConst fnsFlatEqNm, mkNatLit ac.startIdx]
    else
      mkAppN (Lean.mkConst `LeanQbe.T.map_slice_eq [.zero, .one])
        #[flatTy, tys.fnTy, Lean.mkConst ``LeanQbe.T.TFlatFn.toFn, fnsBaseE, flatFnsConstE,
          Lean.mkConst fnsFlatEqNm, mkNatLit ac.startIdx, mkNatLit ac.fnCount]
    let cmTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) excTy cmLhs cmRhs
    let cmVal := mkAppN (Lean.mkConst `LeanQbe.T.compileModule_of_flat_eq)
      #[b.isaE, b.ltE, b.raE, Lean.mkConst ac.extNm, b.exitsE, b.nXE,
        Lean.mkConst ac.fnsNm, Lean.mkConst flatNm, Lean.mkConst ac.hintsNm,
        Lean.mkConst ac.codeNm, Lean.mkConst ac.boundsNm, sliceEqPf, Lean.mkConst cmFlatNm]
    addCertThm ac.cmNm cmTy cmVal
  | _, _, _ =>
    addKernelEqThm ac.cmNm excTy cmLhs cmRhs .zero
  let fnNamesE := mkApp4 (Lean.mkConst ``List.map [1, .zero])
    tys.fnTy tys.symTy (Lean.mkConst ``LeanQbe.T.Fn.name) (Lean.mkConst ac.fnsNm)
  let metaLhs := mkAppN (Lean.mkConst ``LeanQbe.T.checkCompileLit)
    #[b.dirTy, b.labelE, b.progSmallE, Lean.mkConst ac.codeNm, Lean.mkConst ac.boundsNm,
      fnNamesE, b.exitsE, b.maxBE]
  addKernelEqThm ac.metaNm (Lean.mkConst ``Bool) metaLhs (Lean.mkConst ``Bool.true) .zero

/-- Pass-3 assembly of `Compiled` and `CompiledChunk.mk` for one `.acyc` chunk. -/
def emitAcycCompiledChunk (b : CertBaseEnv) (ac : AcycChunkNames) : CoreM Lean.Expr := do
  let compTy := mkAppN (Lean.mkConst ``LeanQbe.T.Compiled)
    #[b.targE, b.ltE, Lean.mkConst ac.extNm, b.exitsE, b.nXE,
      Lean.mkConst ac.fnsNm, Lean.mkConst ac.hintsNm, b.maxBE]
  let compVal := mkAppN (Lean.mkConst ``LeanQbe.T.compileCheckedLit)
    #[b.targE, b.layoutE, b.ltE, b.clE, Lean.mkConst ac.extNm, b.exitsE, b.nXE,
      Lean.mkConst ac.fnsNm, Lean.mkConst ac.hintsNm, b.maxBE, Lean.mkConst ac.codeNm,
      Lean.mkConst ac.boundsNm, Lean.mkConst ac.cmNm, Lean.mkConst ac.metaNm]
  addCertDef ac.compNm compTy compVal b.compileCert
  return mkAppN (Lean.mkConst ``LeanQbe.T.CompiledChunk.mk)
    #[b.targE, b.ltE, b.exitsE, b.nXE, Lean.mkConst ac.extNm, Lean.mkConst ac.fnsNm,
      Lean.mkConst ac.hintsNm, b.maxBE, Lean.mkConst ac.compNm]

def elabAndEvalChunks (targT layoutT ltT clT modT : Term) (chunkSize : Nat)
    (opts : CertOptions) : TermElabM CertInputs := do
  let b ← elabCertBase targT layoutT ltT clT opts
  let pruneExt ← evalBoolOpt opts.pruneExtT? false
  let flat ← evalBoolOpt opts.flatT? false
  let modE ← instantiateMVars (← Term.elabTerm modT (some (Lean.mkConst ``LeanQbe.T.Module)))
  let fnsE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) modE
  let pruneExtE := Lean.mkConst (if pruneExt then ``Bool.true else ``Bool.false)
  let outTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero]) (Lean.mkConst ``String)
    (Lean.mkConst ``LeanQbe.T.EvalModuleData)
  let (evalRes, flat?) ← match (← decodeFlatSliceExpr fnsE) with
    | some (flatFns, flatListE, pf) =>
      let listFlatTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.TFlatFn)
      let runnerTy := Lean.mkForall `_ .default listFlatTy outTy
      if flat then
        let env ← getEnv
        for nm in [`LeanQbe.T.makeChunkEvaluatorFlat, `LeanQbe.T.compileModuleFlat,
            `LeanQbe.T.compileModule_of_flat_eq, `LeanQbe.T.map_slice_eq,
            `LeanQbe.T.map_drop_eq] do
          if !env.contains nm then
            throwError "compile_linked_chunks!: (flat := true) missing '{nm}' \
              (add `public import LeanQbe.T.MainCertFlat` and \
              `meta import LeanQbe.T.MainCertFlatElab`)"
        let callE ← instantiateMVars (mkAppN (Lean.mkConst `LeanQbe.T.makeChunkEvaluatorFlat)
          #[b.isaE, b.ltE, b.raE, b.ext0E, b.exitsE, b.nXE, mkNatLit chunkSize, b.maxBE,
            b.maxDirsE, pruneExtE, b.toExprHintsInst, b.toExprDirInst])
        let runner ← unsafe evalExpr (List TFlatFn → Except String EvalModuleData) runnerTy callE
        pure (runner flatFns, some (flatListE, pf))
      else
        let callE ← instantiateMVars (mkAppN (Lean.mkConst ``LeanQbe.T.makeChunkEvaluator)
          #[b.isaE, b.ltE, b.raE, b.ext0E, b.exitsE, b.nXE, mkNatLit chunkSize, b.maxBE,
            b.maxDirsE, pruneExtE, b.toExprHintsInst, b.toExprDirInst])
        let runner ← unsafe evalExpr (List TFlatFn → Except String EvalModuleData) runnerTy callE
        pure (runner flatFns, none)
    | none =>
      if flat then
        throwError "compile_linked_chunks!: (flat := true) requires a materialized \
          TFlatFn/denoteFunc slice (decodeFlatSliceExpr returned none)"
      let callE ← instantiateMVars (mkAppN (Lean.mkConst ``LeanQbe.T.evalLinkedChunks)
        #[b.isaE, b.ltE, b.raE, b.ext0E, b.exitsE, b.nXE, fnsE, mkNatLit chunkSize, b.maxBE,
          b.maxDirsE, pruneExtE, b.toExprHintsInst, b.toExprDirInst])
      pure (← unsafe evalExpr (Except String EvalModuleData) outTy callE, none)
  match evalRes with
  | .error e => throwError "compile_linked_chunks!: {e}"
  | .ok md => return {
      base := b, modE := modE, chunks := md.chunks, finalExtLit := md.finalExtLit, flat? := flat? }

/-- `compile_linked_chunks! certName target layout legalTarget labelClean mod chunkSize
[(maxBound := ...)] [(ext := ...)] [(exits := ...)] [(nX := ...)] [(maxDirs := ...)]
[(compile := ...)] [(compileExt := ...)] [(pruneExt := ...)] [(flat := ...)]` splits `mod.fns`
into callee-first chunks, checks each chunk independently in the kernel, links all chunks via
`checkLinkList`, and defines `certName : LinkedCert ...`. -/
scoped syntax "compile_linked_chunks! " ident
    term:arg term:arg term:arg term:arg term:arg num ("(" ident " := " term ")")* : command

scoped elab_rules : command
  | `(compile_linked_chunks! $certId $targT $layoutT $ltT $clT $modT $chunkSizeLit
      $[($optKeys := $optVals)]*) => do
    let ns ← getCurrNamespace; let certNm := ns ++ certId.getId; let auxNs := certNm ++ `aux
    let opts ← parseCertOptions optKeys optVals
    let inp ← liftTermElabM <| elabAndEvalChunks targT layoutT ltT clT modT chunkSizeLit.getNat opts
    let b := inp.base; let tys := mkCertTypes
    let fnsBaseE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) inp.modE
    let flatCtx? : Option (Lean.Expr × Lean.Expr × Name) ← match inp.flat? with
      | some (flatListE, pf) =>
        let flatTy := Lean.mkConst ``LeanQbe.T.TFlatFn
        let listFlatTy := mkApp (Lean.mkConst ``List [.zero]) flatTy
        let flatFnsNm := auxNs ++ `flatFns
        let fnsFlatEqNm := auxNs ++ `fns_flat_eq
        let flatFnsConstE := Lean.mkConst flatFnsNm
        let rhsE := mkApp4 (Lean.mkConst ``List.map [.zero, .one])
          flatTy tys.fnTy (Lean.mkConst ``LeanQbe.T.TFlatFn.toFn) flatFnsConstE
        let eqTy := mkApp3 (Lean.mkConst ``Eq [2]) tys.listFnTy fnsBaseE rhsE
        liftCoreM do
          addCertDef flatFnsNm listFlatTy flatListE false
          addCertThm fnsFlatEqNm eqTy pf
        pure (some (fnsBaseE, flatFnsConstE, fnsFlatEqNm))
      | none => pure none
    let flatBaseE? := flatCtx?.map (·.2.1)
    let mut chunkNames : Array AcycChunkNames := #[]
    let mut ci : Nat := 0
    for ch in inp.chunks do
      chunkNames := chunkNames.push
        (← emitAcycChunkDefs auxNs s!"c{ci}" b.compileCert fnsBaseE b.listHintsTy b.listDirTy ch
          flatBaseE?)
      ci := ci + 1
    for ac in chunkNames do liftCoreM <| emitAcycChunkThms b ac flatCtx?
    let mut chunkEntries : List Lean.Expr := []
    for ac in chunkNames do
      chunkEntries := chunkEntries ++ [← liftCoreM <| emitAcycCompiledChunk b ac]
    let chunkTy := mkAppN (Lean.mkConst ``LeanQbe.T.CompiledChunk)
      #[b.targE, b.ltE, b.exitsE, b.nXE]
    let chunksNm := auxNs ++ `chunks
    liftCoreM <| addCertDef chunksNm (mkApp (Lean.mkConst ``List [1]) chunkTy)
      (mkExprList 1 chunkTy chunkEntries) b.compileCert
    let linkCheckNm := auxNs ++ `link_check
    let linkLhs := mkAppN (Lean.mkConst ``LeanQbe.T.checkLinkList)
      #[b.targE, b.layoutE, b.ltE, b.exitsE, b.nXE, b.ext0E, Lean.mkConst chunksNm]
    liftCoreM <| addKernelEqThm linkCheckNm (Lean.mkConst ``Bool) linkLhs
      (Lean.mkConst ``Bool.true) .zero
    let fnsEqNm := auxNs ++ `fns_eq; let suppAllNm := auxNs ++ `supportsAll
    let maxBLeNm := auxNs ++ `maxBound_le
    let chunksFnsE := mkAppN (Lean.mkConst ``LeanQbe.T.chunksFns)
      #[b.targE, b.ltE, b.exitsE, b.nXE, Lean.mkConst chunksNm]
    let mut fnsEqProof : Lean.Expr := default
    let mut restFnsE := mkApp (Lean.mkConst ``List.nil [1]) tys.fnTy
    let mut maxBProof := mkAppN (Lean.mkConst ``LeanQbe.T.chunksMaxBound_nil)
      #[b.targE, b.ltE, b.exitsE, b.nXE, b.maxBE]
    let mut restChunksE := mkApp (Lean.mkConst ``List.nil [1]) chunkTy
    let nChunks := chunkNames.size
    for revIdx in [:nChunks] do
      let i := nChunks - 1 - revIdx
      let ac := chunkNames[i]!; let chunkVal := chunkEntries[i]!
      fnsEqProof := if revIdx == 0 then
        mkApp3 (Lean.mkConst ``LeanQbe.T.slice_last_eq [1]) tys.fnTy fnsBaseE (mkNatLit ac.startIdx)
      else mkApp6 (Lean.mkConst ``LeanQbe.T.slice_cons_eq [1])
        tys.fnTy fnsBaseE restFnsE (mkNatLit ac.startIdx) (mkNatLit ac.fnCount) fnsEqProof
      maxBProof := mkAppN (Lean.mkConst ``LeanQbe.T.chunksMaxBound_cons)
        #[b.targE, b.ltE, b.exitsE, b.nXE, b.maxBE, chunkVal, restChunksE,
          mkApp (Lean.mkConst ``Nat.le_refl) b.maxBE, maxBProof]
      restFnsE := mkApp3 (Lean.mkConst ``List.append [1]) tys.fnTy (Lean.mkConst ac.fnsNm) restFnsE
      restChunksE := mkApp3 (Lean.mkConst ``List.cons [1]) chunkTy chunkVal restChunksE
    liftCoreM <| addCertThm fnsEqNm
      (mkApp3 (Lean.mkConst ``Eq [2]) tys.listFnTy fnsBaseE chunksFnsE) fnsEqProof
    let (suppAllTy, suppAllVal, maxBLeProp) ← liftTermElabM do
      let sVal ← mkAppM ``LeanQbe.T.supportsAll_of_eq #[Lean.mkConst fnsEqNm,
        mkAppN (Lean.mkConst ``LeanQbe.T.supportsAll_of_chunks)
          #[b.targE, b.ltE, b.exitsE, b.nXE, Lean.mkConst chunksNm]]
      let lhs := mkAppN (Lean.mkConst ``LeanQbe.T.chunksMaxBound)
        #[b.targE, b.ltE, b.exitsE, b.nXE, Lean.mkConst chunksNm]
      return (← instantiateMVars (← inferType sVal), ← instantiateMVars sVal,
        ← instantiateMVars (← mkAppM ``LE.le #[lhs, b.maxBE]))
    liftCoreM do
      addCertThm suppAllNm suppAllTy suppAllVal
      addCertThm maxBLeNm maxBLeProp maxBProof
      addCertDef certNm
        (mkAppN (Lean.mkConst ``LeanQbe.T.LinkedCert)
          #[b.targE, b.layoutE, b.ltE, b.clE, inp.modE, b.ext0E, b.exitsE, b.nXE, b.maxBE])
        (mkAppN (Lean.mkConst ``LeanQbe.T.LinkedCert.mk)
          #[b.targE, b.layoutE, b.ltE, b.clE, inp.modE, b.ext0E, b.exitsE, b.nXE, b.maxBE,
            Lean.mkConst chunksNm, Lean.mkConst linkCheckNm, Lean.mkConst fnsEqNm,
            Lean.mkConst suppAllNm, Lean.mkConst maxBLeNm]) b.compileCert
      addCertDef (certNm ++ `exportedExt) tys.listExtTy inp.finalExtLit b.compileExt

/-- Shared prefix-bound accumulator over pre-spawned bound stage-1 worker tasks, reused by
both PHOAS (`evalPrefixExtWithLen`) and flat (`MainCertFlatElab.makePrefixExt*EvaluatorFlat`). -/
def evalPrefixExtFromTasks (I : Isa) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX maxBound : Nat)
    (tasks : List (Task (Except String (Sym × I.Hints × Rega.Ext × SigEntry))))
    (pruneTasks? :
      Option (List (Task (Except String (Sym × I.Hints × Rega.Ext × SigEntry)))) := none) :
    Except String (Nat × Lean.Expr) := do
  let rec go (acc : List (SigEntry × Nat)) :
      List (Task (Except String (Sym × I.Hints × Rega.Ext × SigEntry))) →
      Except String (List (SigEntry × Nat))
    | [] => .ok acc
    | t :: rest => do
      let (nm, h, ext, sig) ← t.get
      go ((sig, ← evalOneFnBoundCheck I raBytes exits nX maxBound acc nm h ext) :: acc) rest
  let out ← go ext0 tasks
  match pruneTasks? with
  | none => pure (out.length, Lean.toExpr out)
  | some tTasks =>
    let mut callees : List SigEntry := []
    for t in tTasks do
      let (_, _, ext, _) ← t.get
      callees := callees ++ ext.callees
    pure (out.length, Lean.toExpr (pruneExtCallees callees out))

/-- Evaluates `evalOneFnBound` in order over `fs` starting from `ext0`, returning `(totalLen,
extLit)` in `compileModule`'s reverse `(sig, bound) :: acc` order. When `pruneFor?` is
`some targetFns`, prunes the emitted literal down to direct callees of `targetFns`. -/
def evalPrefixExtWithLen (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX maxBound : Nat)
    (fs : List Fn) (pruneFor? : Option (List Fn) := none) :
    Except String (Nat × Lean.Expr) :=
  let tasks := fs.map fun f => Task.spawn fun () => evalOneFnBoundStage1 I lt f
  let pruneTasks? := pruneFor?.map fun targetFns =>
    targetFns.map fun f => Task.spawn fun () => evalOneFnBoundStage1 I lt f
  evalPrefixExtFromTasks I raBytes ext0 exits nX maxBound tasks pruneTasks?

/-- Evaluates `evalOneFnBound` in order over `fs` starting from `ext0`. -/
def evalPrefixExt (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX maxBound : Nat)
    (fs : List Fn) : Except String Lean.Expr :=
  Prod.snd <$> evalPrefixExtWithLen I lt raBytes ext0 exits nX maxBound fs

/-- Curried meta prefix-bound evaluator over decoded `List TFlatFn`. -/
def makePrefixExtEvaluator (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX maxBound : Nat)
    (pruneFor? : Option (List Fn) := none) :
    List TFlatFn → Except String (Nat × Lean.Expr) :=
  fun fs =>
    evalPrefixExtWithLen I lt raBytes ext0 exits nX maxBound (fs.map TFlatFn.toFn) pruneFor?

/-- Curried meta prefix-bound evaluator when both `fns` and `pruneFor` are `TFlatFn`-decoded. -/
def makePrefixExtPrunedEvaluator (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX maxBound : Nat) :
    List TFlatFn → List TFlatFn → Except String (Nat × Lean.Expr) :=
  fun fs pfs =>
    evalPrefixExtWithLen I lt raBytes ext0 exits nX maxBound
      (fs.map TFlatFn.toFn) (some (pfs.map TFlatFn.toFn))

structure PrefixExtOptions where
  maxBT? : Option Term := none
  extT? : Option Term := none
  exitsT? : Option Term := none
  nXT? : Option Term := none
  prefixId? : Option Ident := none
  pruneForT? : Option Term := none
  flatT? : Option Term := none
  deriving Inhabited

def parsePrefixExtOptions (optKeys : TSyntaxArray `ident) (optVals : TSyntaxArray `term) :
    CommandElabM PrefixExtOptions :=
  parseKvOptions "eval_prefix_ext!" "maxBound, ext, exits, nX, prefixDef, pruneFor, flat" {}
    (fun opts k v => match k with
      | `maxBound => pure (some { opts with maxBT? := some v })
      | `ext => pure (some { opts with extT? := some v })
      | `exits => pure (some { opts with exitsT? := some v })
      | `nX => pure (some { opts with nXT? := some v })
      | `prefixDef =>
        if let `($id:ident) := v then pure (some { opts with prefixId? := some id })
        else throwErrorAt v "eval_prefix_ext!: prefixDef must be an identifier"
      | `pruneFor => pure (some { opts with pruneForT? := some v })
      | `flat => pure (some { opts with flatT? := some v })
      | _ => pure none) optKeys optVals

def elabAndEvalPrefixExt (targT ltT fnsT : Term) (opts : PrefixExtOptions) :
    TermElabM (Lean.Expr × Nat × Lean.Expr) := do
  let tys := mkCertTypes
  let targE ← Term.elabTerm targT (some (Lean.mkConst ``LeanQbe.T.Target))
  let ltE ← Term.elabTerm ltT (some (Lean.mkConst ``LeanQbe.T.LegalTarget))
  let fnsE ← Term.elabTerm fnsT (some tys.listFnTy)
  let (ext0E, exitsE, nXE, maxBE) ←
    elabCommonBoundArgs opts.extT? opts.exitsT? opts.nXT? opts.maxBT?
  let pruneForRaw? ← match opts.pruneForT? with
    | some t => some <$> Term.elabTerm t (some tys.listFnTy)
    | none => pure none
  let flat ← evalBoolOpt opts.flatT? false
  Term.synthesizeSyntheticMVarsNoPostponing
  let targE ← instantiateMVars targE; let ltE ← instantiateMVars ltE
  let fnsE ← instantiateMVars fnsE; let ext0E ← instantiateMVars ext0E
  let exitsE ← instantiateMVars exitsE; let nXE ← instantiateMVars nXE
  let maxBE ← instantiateMVars maxBE
  let pruneForRaw? ← pruneForRaw?.mapM instantiateMVars
  let pruneForE := match pruneForRaw? with
    | some pfE => mkApp2 (Lean.mkConst ``Option.some [1]) tys.listFnTy pfE
    | none => mkApp (Lean.mkConst ``Option.none [1]) tys.listFnTy
  let isaE := mkApp (Lean.mkConst ``LeanQbe.T.Target.toIsa) targE
  let raE ← mkAppM ``LeanQbe.T.FrameIsa.raBytes #[← mkAppM ``LeanQbe.T.Isa.frame #[isaE]]
  let pairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) tys.natTy (Lean.mkConst ``Lean.Expr)
  let outTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero]) (Lean.mkConst ``String) pairTy
  let listFlatTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.TFlatFn)
  let evalRes ← match (← decodeFlatSliceExpr fnsE) with
    | some (flatFns, _, _) =>
      if flat then
        let env ← getEnv
        for nm in [`LeanQbe.T.makePrefixExtEvaluatorFlat,
            `LeanQbe.T.makePrefixExtPrunedEvaluatorFlat] do
          if !env.contains nm then
            throwError "eval_prefix_ext!: (flat := true) missing '{nm}' \
              (add `meta import LeanQbe.T.MainCertFlatElab`)"
      let decodedPrune? ← match pruneForRaw? with
        | some pfE => decodeFlatSliceExpr pfE
        | none => pure none
      match decodedPrune? with
      | some (pruneFlats, _, _) =>
        let runnerTy := Lean.mkForall `_ .default listFlatTy
          (Lean.mkForall `_ .default listFlatTy outTy)
        let fnNm := if flat then `LeanQbe.T.makePrefixExtPrunedEvaluatorFlat
          else ``LeanQbe.T.makePrefixExtPrunedEvaluator
        let callE ← instantiateMVars (mkAppN (Lean.mkConst fnNm)
          #[isaE, ltE, raE, ext0E, exitsE, nXE, maxBE])
        let runner ← unsafe evalExpr
          (List TFlatFn → List TFlatFn → Except String (Nat × Lean.Expr)) runnerTy callE
        pure (runner flatFns pruneFlats)
      | none =>
        let runnerTy := Lean.mkForall `_ .default listFlatTy outTy
        let fnNm := if flat then `LeanQbe.T.makePrefixExtEvaluatorFlat
          else ``LeanQbe.T.makePrefixExtEvaluator
        let callE ← instantiateMVars (mkAppN (Lean.mkConst fnNm)
          #[isaE, ltE, raE, ext0E, exitsE, nXE, maxBE, pruneForE])
        let runner ← unsafe evalExpr
          (List TFlatFn → Except String (Nat × Lean.Expr)) runnerTy callE
        pure (runner flatFns)
    | none =>
      if flat then
        throwError "eval_prefix_ext!: (flat := true) requires a materialized \
          TFlatFn/denoteFunc slice (decodeFlatSliceExpr returned none)"
      let callE ← instantiateMVars (mkAppN (Lean.mkConst ``LeanQbe.T.evalPrefixExtWithLen)
        #[isaE, ltE, raE, ext0E, exitsE, nXE, maxBE, fnsE, pruneForE])
      unsafe evalExpr (Except String (Nat × Lean.Expr)) outTy callE
  match evalRes with
  | .error e => throwError "eval_prefix_ext!: {e}"
  | .ok (total, extLit) => return (tys.listExtTy, total, extLit)

/-- `eval_prefix_ext! extName target legalTarget fnsExpr [(ext := ...)] [(exits := ...)]
[(nX := ...)] [(maxBound := ...)] [(prefixDef := ...)] [(pruneFor := ...)] [(flat := ...)]` runs
`evalOneFnBound` in compiled meta code and emits `def extName : List (SigEntry × Nat) :=
<literal>`. -/
scoped syntax "eval_prefix_ext! " ident
    term:arg term:arg term:arg ("(" ident " := " term ")")* : command

scoped elab_rules : command
  | `(eval_prefix_ext! $extId $targT $ltT $fnsT $[($optKeys := $optVals)]*) => do
    let ns ← getCurrNamespace; let extNm := ns ++ extId.getId
    let opts ← parsePrefixExtOptions optKeys optVals
    let (listExtTy, total, extLit) ← liftTermElabM <|
      elabAndEvalPrefixExt targT ltT fnsT opts
    liftCoreM do
      addCertDef extNm listExtTy extLit
      if let some pfxId := opts.prefixId? then
        let tys := mkCertTypes
        let dropVal := mkApp3 (Lean.mkConst ``List.drop [.zero]) tys.sigEntryNatTy
          (mkApp2 (Lean.mkConst ``Nat.sub) (mkNatLit total) (mkBVar 0)) (Lean.mkConst extNm)
        addCertDef (ns ++ pfxId.getId) (Lean.mkForall `k .default tys.natTy listExtTy)
          (Lean.mkLambda `k .default tys.natTy dropVal)

end

end LeanQbe.T
