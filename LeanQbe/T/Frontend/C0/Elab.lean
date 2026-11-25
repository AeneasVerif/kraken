module

public import LeanQbe.T.Frontend.C0.Syntax
public import LeanQbe.T.Frontend.C0.Parser
public import LeanQbe.T.Frontend.C0.Layout
public import LeanQbe.T.Frontend.C0.Lower
public import LeanQbe.T.Notation
public meta import LeanQbe.T.Frontend.C0.Syntax
public meta import LeanQbe.T.Frontend.C0.Parser
public meta import LeanQbe.T.Frontend.C0.Layout
public meta import LeanQbe.T.Frontend.C0.Lower
public meta import LeanQbe.T.Notation
public meta import Lean.Elab.Command

/-!
# C0 Direct PHOAS Elaborator, `c0_decl!`, `c0_file!`, and `#c0_shape`

Elaborates lowered C0 functions (`LFn`) directly into kernel `LeanQbe.T.Fn` definitions using
projection lambdas (`Prod.fst`/`Prod.snd`) and explicit `Op.mk` applications
(matching `Notation.lean`'s elaboration strategy),
checks acyclic `Module` ordering, and registers `#c0_shape` metadata for proof authors.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Frontend.C0

open Lean Elab Command Term Meta
open LeanQbe.T
open LeanQbe.T.Notation

/-! ## `#c0_shape`, `c0_header!`, and `#c0_audit` Environment Extensions -/

meta initialize c0ShapeExt :
    SimpleScopedEnvExtension (Name × FnShape) (NameMap FnShape × Std.HashMap String FnShape) ←
  registerSimpleScopedEnvExtension {
    name := `LeanQbe.T.Frontend.C0.c0ShapeExt
    initial := ({}, {})
    addEntry := fun (byLean, byC) (nm, sh) => (byLean.insert nm sh, byC.insert sh.name sh)
  }

meta initialize c0HeaderExt :
    SimpleScopedEnvExtension (String × String) (Std.HashMap String String) ←
  registerSimpleScopedEnvExtension {
    name := `LeanQbe.T.Frontend.C0.c0HeaderExt
    initial := {}
    addEntry := fun map (k, v) => map.insert k v
  }

/-- Retrieve all currently registered C0 headers from the environment. -/
meta def getC0Headers (env : Lean.Environment) : Std.HashMap String String :=
  c0HeaderExt.getState env

/-- Upstream provenance metadata captured from `#pragma c0_upstream`. -/
meta structure Provenance : Type where
  loc : String
  upstreamFn : String
  deriving Repr, BEq, Inhabited

/-- Function fidelity classification. -/
meta inductive FnTag : Type
  | fidelity
  | extension
  | unannotated
  deriving Repr, BEq, Inhabited

meta def FnTag.toString : FnTag → String
  | .fidelity => "@fidelity"
  | .extension => "@extension"
  | .unannotated => "@unannotated"

/-- Single loop audit verdict. -/
meta inductive LoopAuditVerdict : Type
  | okBoundedByPragma (reason : String)
  | okTickGuarded (detail : String)
  | okTickUpdated (detail : String)
  | okConstantBound (bound : Nat)
  | violationUnboundedLoop (detail : String)
  deriving Repr, BEq, Inhabited

meta def LoopAuditVerdict.isOk : LoopAuditVerdict → Bool
  | .violationUnboundedLoop _ => false
  | _ => true

/-- Audit record for a single loop. -/
meta structure LoopAudit : Type where
  loopIndex : Nat
  loopKind : String
  condStr : String
  verdict : LoopAuditVerdict
  deriving Repr, BEq, Inhabited

/-- Audit report for a single function. -/
meta structure FnAuditReport : Type where
  fnName : String
  provenance : Option Provenance := none
  tag : FnTag := .unannotated
  directCallees : List String := []
  reachableCallees : List String := []
  extensionCallsReachable : List String := []
  loops : List LoopAudit := []
  isFidelityClean : Bool := true
  hasLoopViolations : Bool := false
  deriving Repr, BEq, Inhabited

/-- Module audit report aggregating all functions. -/
meta structure ModuleAuditReport : Type where
  moduleName : String
  fnReports : List FnAuditReport := []
  totalFns : Nat := 0
  passedFns : Nat := 0
  hasViolations : Bool := false
  deriving Repr, BEq, Inhabited

/-- Formatted display for a function audit report. -/
meta def FnAuditReport.format (r : FnAuditReport) : String :=
  let provStr := match r.provenance with
    | some p => s!"{p.loc} ({p.upstreamFn})"
    | none => "(unannotated)"
  let tagStr := r.tag.toString
  let extStr :=
    if r.tag == .extension then
      "N/A (@extension function)"
    else if r.extensionCallsReachable.isEmpty then
      "PASS (0 @extension calls reachable)"
    else
      s!"FAIL (reaches @extension: {String.intercalate ", " r.extensionCallsReachable})"
  let loopLines :=
    if r.loops.isEmpty then
      ["  (no loops in function body)"]
    else
      r.loops.map fun l =>
        let vStr := match l.verdict with
          | .okBoundedByPragma reason => s!"[PASS: bounded] {reason}"
          | .okTickGuarded msg => s!"[PASS: tick-guarded] {msg}"
          | .okTickUpdated msg => s!"[PASS: tick-updated] {msg}"
          | .okConstantBound b => s!"[PASS: constant-bound <= {b}]"
          | .violationUnboundedLoop msg => s!"[FAIL: UNBOUNDED] {msg}"
        s!"  - Loop #{l.loopIndex} ({l.loopKind}): {vStr}\n    guard: {l.condStr}"
  let overallPass := r.isFidelityClean && !r.hasLoopViolations
  let statusStr :=
    if overallPass then
      "PASS (0 violations)"
    else
      let fidErr :=
        if !r.isFidelityClean then
          [s!"fidelity violation ({r.extensionCallsReachable.length} ext calls)"]
        else []
      let loopErr :=
        if r.hasLoopViolations then
          let violCount := (r.loops.filter (fun l => !l.verdict.isOk)).length
          [s!"{violCount} loop tick-accounting violation(s)"]
        else []
      s!"FAIL ({String.intercalate ", " (fidErr ++ loopErr)})"
  s!"============================================================\n" ++
  s!"C0 Audit Report: {r.fnName}\n" ++
  s!"============================================================\n" ++
  s!"* Provenance:  {provStr}\n" ++
  s!"* Tag:         {tagStr}\n" ++
  s!"* Extensions:  {extStr}\n" ++
  s!"* Loops ({r.loops.length}):\n" ++
  String.intercalate "\n" loopLines ++ "\n" ++
  s!"------------------------------------------------------------\n" ++
  s!"Result: {statusStr}\n" ++
  s!"============================================================"

/-- Formatted display for a module audit report. -/
meta def ModuleAuditReport.format (m : ModuleAuditReport) : String :=
  let fnSummaries := m.fnReports.map fun r =>
    let prov := match r.provenance with
      | some p => s!" -> {p.loc}"
      | none => ""
    let status := if r.isFidelityClean && !r.hasLoopViolations then "PASS" else "FAIL"
    s!"  - {r.fnName} [{r.tag.toString}]{prov} -> {status}"
  let statusStr := if !m.hasViolations then "PASS" else "FAIL (violations found)"
  let bodyStr :=
    if fnSummaries.isEmpty then "  (no functions)" else String.intercalate "\n" fnSummaries
  s!"============================================================\n" ++
  s!"C0 Module Audit: {m.moduleName} ({m.passedFns}/{m.totalFns} passed)\n" ++
  s!"============================================================\n" ++
  bodyStr ++ "\n" ++
  s!"------------------------------------------------------------\n" ++
  s!"Overall Module Status: {statusStr}\n" ++
  s!"============================================================"

meta inductive AuditEntry : Type
  | fn (rep : FnAuditReport)
  | mod (rep : ModuleAuditReport)
  deriving Repr, Inhabited

meta initialize c0AuditExt :
    SimpleScopedEnvExtension (Name × AuditEntry)
      (NameMap AuditEntry × Std.HashMap String AuditEntry) ←
  registerSimpleScopedEnvExtension {
    name := `LeanQbe.T.Frontend.C0.c0AuditExt
    initial := ({}, {})
    addEntry := fun (byLean, byC) (nm, ent) =>
      let cName := match ent with
        | .fn rep => rep.fnName
        | .mod rep => rep.moduleName
      (byLean.insert nm ent, byC.insert cName ent)
  }

private meta def toLowerChar (c : Char) : Char :=
  if 'A' <= c && c <= 'Z' then Char.ofNat (c.toNat + 32) else c

private meta def stringContainsCI (haystack needle : String) : Bool :=
  let hcs := haystack.toList.map toLowerChar
  let ncs := needle.toList.map toLowerChar
  if ncs.isEmpty then true
  else
    let rec go : List Char → Bool
      | [] => false
      | cs@(_ :: rest) =>
        if cs.take ncs.length == ncs then true
        else go rest
    go hcs

private meta partial def exprToString : Expr → String
  | .intLit v _ _ => s!"{v}"
  | .floatLit _ => "float"
  | .boolLit b => s!"{b}"
  | .null => "NULL"
  | .var s => s
  | .cast ty e => s!"({c0TypeToString ty}){exprToString e}"
  | .sizeofTy ty => s!"sizeof({c0TypeToString ty})"
  | .sizeofExpr e => s!"sizeof({exprToString e})"
  | .offsetof ty fld => s!"offsetof({c0TypeToString ty}, {fld})"
  | .unary op e => s!"{unaryOpToString op}{exprToString e}"
  | .binary op l r => s!"{exprToString l} {binOpToString op} {exprToString r}"
  | .ternary c t e => s!"{exprToString c} ? {exprToString t} : {exprToString e}"
  | .field e f => s!"{exprToString e}.{f}"
  | .arrow e f => s!"{exprToString e}->{f}"
  | .index a i => s!"{exprToString a}[{exprToString i}]"
  | .call fn args => s!"{fn}({String.intercalate ", " (args.map exprToString)})"
where
  c0TypeToString : C0Type → String
    | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
    | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
    | .bool => "bool" | .void => "void" | .f64 => "f64"
    | .ptr t => s!"{c0TypeToString t}*"
    | .structRef s => s!"struct {s}"
    | .unionRef s => s!"union {s}"
    | .typedefRef s => s
    | _ => "type"
  unaryOpToString : UnaryOp → String
    | .neg => "-" | .pos => "+" | .bitnot => "~" | .lognot => "!"
    | .deref => "*" | .addrOf => "&"
  binOpToString : BinOp → String
    | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
    | .bitand => "&" | .bitor => "|" | .bitxor => "^" | .shl => "<<" | .shr => ">>"
    | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
    | .logand => "&&" | .logor => "||"

private meta partial def exprVarNames : Expr → List String
  | .var nm => [nm]
  | .cast _ e | .sizeofExpr e | .unary _ e | .field e _ | .arrow e _ => exprVarNames e
  | .binary _ l r => exprVarNames l ++ exprVarNames r
  | .ternary c t e => exprVarNames c ++ exprVarNames t ++ exprVarNames e
  | .index a i => exprVarNames a ++ exprVarNames i
  | .call _ args => args.flatMap exprVarNames
  | _ => []

private meta def isTickName (s : String) : Bool :=
  stringContainsCI s "tick"

private meta def isLimitName (s : String) : Bool :=
  stringContainsCI s "lim" || stringContainsCI s "limit" ||
  stringContainsCI s "bound" || stringContainsCI s "budget" || stringContainsCI s "max"

private meta def checkCondTickGuarded (cond : Expr) : Option String :=
  let vars := exprVarNames cond
  let hasTick := vars.any isTickName
  let hasLim := vars.any isLimitName
  if hasTick && hasLim then
    some "guarded by ticks and limit/bound"
  else if hasLim then
    some "guarded by limit/bound variable"
  else if hasTick then
    some "guarded by tick condition"
  else
    none

private meta def checkSmallConstantBound (cond : Expr) : Option Nat :=
  match cond with
  | .binary op (.var _) (.intLit val _ _)
  | .binary op (.cast _ (.var _)) (.intLit val _ _) =>
    if (op == .lt || op == .le || op == .ne) && val > 0 && val ≤ 128 then
      some val.toNat
    else none
  | .binary op (.intLit val _ _) (.var _)
  | .binary op (.intLit val _ _) (.cast _ (.var _)) =>
    if (op == .gt || op == .ge || op == .ne) && val > 0 && val ≤ 128 then
      some val.toNat
    else none
  | _ => none

private meta partial def findSmallConstantBound : Expr → Option Nat
  | .binary .logand l r => findSmallConstantBound l <|> findSmallConstantBound r
  | e => checkSmallConstantBound e

private meta def lvalMentionsTick : LVal → Bool
  | .var nm => isTickName nm
  | .arrow _ fld => isTickName fld
  | .dot b fld => isTickName fld || lvalMentionsTick b
  | .index a i => (exprVarNames a ++ exprVarNames i).any isTickName
  | .deref p => (exprVarNames p).any isTickName

private meta partial def stmtUpdatesTicks : Stmt → Option String
  | .assign lv _ _ =>
    if lvalMentionsTick lv then some "ticks assigned via lvalue" else none
  | .incDec lv _ =>
    if lvalMentionsTick lv then some "ticks incremented/decremented" else none
  | .callStmt _ fn args =>
    if isTickName fn || (args.flatMap exprVarNames).any isTickName then
      some s!"call '{fn}' updating ticks"
    else none
  | .block stmts =>
    stmts.findSome? stmtUpdatesTicks
  | .ifStmt _ thn els? =>
    stmtUpdatesTicks thn <|> (els?.bind stmtUpdatesTicks)
  | .whileStmt _ b | .doWhileStmt b _ =>
    stmtUpdatesTicks b
  | .forStmt _ _ step? b =>
    (step?.bind stmtUpdatesTicks) <|> stmtUpdatesTicks b
  | .labelStmt _ s =>
    stmtUpdatesTicks s
  | .switchStmt _ arms =>
    arms.findSome? fun arm => arm.body.findSome? stmtUpdatesTicks
  | _ => none

private meta structure LoopRecord where
  index : Nat
  kind : String
  cond : Option Expr
  step : Option Stmt
  body : Stmt

private meta partial def collectLoopRecords (body : Stmt) : List LoopRecord :=
  let rec go (s : Stmt) (idx : Nat) : List LoopRecord × Nat :=
    match s with
    | .whileStmt cond b =>
      let rec0 : LoopRecord :=
        { index := idx, kind := "while", cond := some cond, step := none, body := b }
      let (inner, nextIdx) := go b (idx + 1)
      (rec0 :: inner, nextIdx)
    | .doWhileStmt b cond =>
      let rec0 : LoopRecord :=
        { index := idx, kind := "do-while", cond := some cond, step := none, body := b }
      let (inner, nextIdx) := go b (idx + 1)
      (rec0 :: inner, nextIdx)
    | .forStmt _ cond? step? b =>
      let rec0 : LoopRecord :=
        { index := idx, kind := "for", cond := cond?, step := step?, body := b }
      let (stepLoops, idx2) := match step? with | some st => go st (idx + 1) | none => ([], idx + 1)
      let (bodyLoops, idx3) := go b idx2
      (rec0 :: stepLoops ++ bodyLoops, idx3)
    | .block stmts =>
      stmts.foldl (fun (acc, curIdx) st =>
        let (sub, nextIdx) := go st curIdx
        (acc ++ sub, nextIdx)
      ) ([], idx)
    | .ifStmt _ thn els? =>
      let (thnLoops, idx2) := go thn idx
      let (elsLoops, idx3) := match els? with | some els => go els idx2 | none => ([], idx2)
      (thnLoops ++ elsLoops, idx3)
    | .labelStmt _ st => go st idx
    | .switchStmt _ arms =>
      arms.foldl (fun (acc, curIdx) arm =>
        let (sub, nextIdx) := arm.body.foldl (fun (aAcc, aIdx) st =>
          let (subSt, nextIdxSt) := go st aIdx
          (aAcc ++ subSt, nextIdxSt)
        ) ([], curIdx)
        (acc ++ sub, nextIdx)
      ) ([], idx)
    | _ => ([], idx)
  (go body 0).1

private meta def auditLoopRecord (lr : LoopRecord) (fd : FnDef) : LoopAudit :=
  let loopReason? := fd.boundedLoops.lookup lr.index
  let fnReason? := if !fd.boundedReasons.isEmpty then
    some (String.intercalate "; " fd.boundedReasons)
  else none
  let condStr := match lr.cond with
    | some c => exprToString c
    | none => "(none)"
  let stepTicks := match lr.step with
    | some st => stmtUpdatesTicks st
    | none => none
  let bodyTicks := stmtUpdatesTicks lr.body
  let condTickMsg? := match lr.cond with
    | some c => checkCondTickGuarded c
    | none => none
  let condBound? := match lr.cond with
    | some c => findSmallConstantBound c
    | none => none
  let tickUpdateMsg? := stepTicks <|> bodyTicks
  let verdict : LoopAuditVerdict :=
    if let some r := loopReason? then
      .okBoundedByPragma r
    else if let some r := fnReason? then
      .okBoundedByPragma r
    else if let some msg := condTickMsg? then
      .okTickGuarded msg
    else if let some tickMsg := tickUpdateMsg? then
      .okTickUpdated tickMsg
    else if let some bound := condBound? then
      .okConstantBound bound
    else
      .violationUnboundedLoop
        s!"non-trivial loop lacking tick update, limit guard, or #pragma c0_bounded: '{condStr}'"
  { loopIndex := lr.index, loopKind := lr.kind, condStr, verdict }

private meta partial def exprCallees : Expr → List String
  | .call fn args => fn :: args.flatMap exprCallees
  | .unary _ e | .cast _ e | .sizeofExpr e | .field e _ | .arrow e _ => exprCallees e
  | .binary _ l r => exprCallees l ++ exprCallees r
  | .ternary c t e => exprCallees c ++ exprCallees t ++ exprCallees e
  | .index a i => exprCallees a ++ exprCallees i
  | _ => []

private meta partial def stmtCallees : Stmt → List String
  | .callStmt _ fn args => fn :: args.flatMap exprCallees
  | .assign _ _ rhs => exprCallees rhs
  | .ifStmt c thn els? => exprCallees c ++ stmtCallees thn ++ (els?.map stmtCallees |>.getD [])
  | .whileStmt c b => exprCallees c ++ stmtCallees b
  | .doWhileStmt b c => stmtCallees b ++ exprCallees c
  | .forStmt init? cond? step? b =>
    (init?.map stmtCallees |>.getD []) ++
    (cond?.map exprCallees |>.getD []) ++
    (step?.map stmtCallees |>.getD []) ++
    stmtCallees b
  | .switchStmt c arms =>
    exprCallees c ++ arms.flatMap (fun a => a.body.flatMap stmtCallees)
  | .block stmts => stmts.flatMap stmtCallees
  | .labelStmt _ s => stmtCallees s
  | .retStmt es => es.flatMap exprCallees
  | .assumeStmt c | .checkStmt c _ | .assertStmt c _ => exprCallees c
  | _ => []

private meta def fnCallees (fd : FnDef) : List String := Id.run do
  let raw := fd.body.flatMap stmtCallees
  let mut seen : Std.HashSet String := {}
  let mut out : List String := []
  for c in raw do
    if !seen.contains c then
      seen := seen.insert c
      out := out ++ [c]
  return out

private meta partial def computeReachable (start : String)
    (callMap : Std.HashMap String (List String)) : List String :=
  let rec bfs (work : List String) (visited : Std.HashSet String) (acc : List String) :
      List String :=
    match work with
    | [] => acc
    | cur :: rest =>
      let callees := callMap.get? cur |>.getD []
      let (nextWork, newVisited, newAcc) :=
        callees.foldl (fun (w, v, a) callee =>
          if !v.contains callee then
            (w ++ [callee], v.insert callee, a ++ [callee])
          else (w, v, a)
        ) (rest, visited, acc)
      bfs nextWork newVisited newAcc
  bfs [start] (Std.HashSet.emptyWithCapacity.insert start) []

/-- Audit a single parsed C0 function definition against a whole-module context. -/
meta def auditFunction (fd : FnDef) (callMap : Std.HashMap String (List String))
    (tagMap : Std.HashMap String FnTag) (defaultTag : FnTag := .unannotated) : FnAuditReport :=
  let provenance : Option Provenance := fd.upstreamLoc.map fun loc =>
    { loc, upstreamFn := fd.upstreamFn.getD fd.name }
  let tag : FnTag :=
    if fd.isExtension then .extension
    else if fd.isFidelity then .fidelity
    else defaultTag
  let direct := fnCallees fd
  let reachable := computeReachable fd.name callMap
  let extReach := reachable.filter (fun c => (tagMap.get? c).getD .unannotated == .extension)
  let isFidelityClean := if tag == .fidelity then extReach.isEmpty else true
  let loops := (collectLoopRecords (.block fd.body)).map (fun lr => auditLoopRecord lr fd)
  let hasLoopViolations := loops.any (fun l => !l.verdict.isOk)
  {
    fnName := fd.name
    provenance
    tag
    directCallees := direct
    reachableCallees := reachable
    extensionCallsReachable := extReach
    loops
    isFidelityClean
    hasLoopViolations
  }

/-- Audit an entire parsed `TranslationUnit`. -/
meta def auditTranslationUnit (tu : TranslationUnit) (modName : String := "c0_module") :
    ModuleAuditReport := Id.run do
  let hasModFid := tu.decls.any fun | .pragma .fidelity => true | _ => false
  let hasModExt := tu.decls.any fun | .pragma .extension => true | _ => false
  let defaultTag : FnTag :=
    if hasModExt && !hasModFid then .extension
    else if hasModFid && !hasModExt then .fidelity
    else .unannotated
  let mut fnDefs : List FnDef := []
  let mut callMap : Std.HashMap String (List String) := {}
  let mut tagMap : Std.HashMap String FnTag := {}
  for d in tu.decls do
    if let .fnDef fd := d then
      fnDefs := fnDefs ++ [fd]
      callMap := callMap.insert fd.name (fnCallees fd)
      let tag := if fd.isExtension then .extension
        else if fd.isFidelity then .fidelity
        else defaultTag
      tagMap := tagMap.insert fd.name tag
  let fnReports := fnDefs.map (fun fd => auditFunction fd callMap tagMap defaultTag)
  let passedFns := (fnReports.filter (fun r => r.isFidelityClean && !r.hasLoopViolations)).length
  let hasViolations := passedFns < fnReports.length
  return {
    moduleName := modName
    fnReports
    totalFns := fnReports.length
    passedFns
    hasViolations
  }

/-- Audit a C0 source string directly (with optional header map). -/
meta def auditC0Source (src : String) (modName : String := "c0_module")
    (headers : Std.HashMap String String := {}) : Except String ModuleAuditReport := do
  let tu ← parseC0 src headers
  pure (auditTranslationUnit tu modName)

/-- Look up a single function's audit report from a C0 source string. -/
meta def auditC0Fn (src : String) (fnName : String)
    (headers : Std.HashMap String String := {}) : Except String FnAuditReport := do
  let rep ← auditC0Source src "c0_module" headers
  match rep.fnReports.find? (·.fnName == fnName) with
  | some r => pure r
  | none => throw s!"function '{fnName}' not found in audit"

/-! ## Direct PHOAS `Lean.Expr` Builder from `LExpr` -/

meta def tyToExpr : Ty → Lean.Expr
  | .bool => boolTyExpr
  | .bits 8 => i8TyExpr
  | .bits 16 => i16TyExpr
  | .bits 32 => i32TyExpr
  | .bits 64 => i64TyExpr
  | .bits n => mkApp (Lean.mkConst ``LeanQbe.T.Ty.bits) (mkNatLit n)
  | .float f => mkFloatTy f
  | .pair a b => mkPairTy (tyToExpr a) (tyToExpr b)

meta def valToExpr : (t : Ty) → Val t → Lean.Expr
  | .bool, true => Lean.mkConst ``Bool.true
  | .bool, false => Lean.mkConst ``Bool.false
  | .bits n, v => bvNatLit (mkNatLit n) v.toNat
  | .float f, v => bvNatLit (mkNatLit f.width) v.toNat
  | .pair a b, (va, vb) =>
    let ta := mkApp (Lean.mkConst ``LeanQbe.T.Val) (tyToExpr a)
    let tb := mkApp (Lean.mkConst ``LeanQbe.T.Val) (tyToExpr b)
    mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) ta tb (valToExpr a va) (valToExpr b vb)

meta def cmpOpToExpr (o : CmpOp) : Lean.Expr :=
  Lean.mkConst <| match o with
    | .eq => ``LeanQbe.T.CmpOp.eq | .ne => ``LeanQbe.T.CmpOp.ne
    | .ult => ``LeanQbe.T.CmpOp.ult | .ule => ``LeanQbe.T.CmpOp.ule
    | .ugt => ``LeanQbe.T.CmpOp.ugt | .uge => ``LeanQbe.T.CmpOp.uge
    | .slt => ``LeanQbe.T.CmpOp.slt | .sle => ``LeanQbe.T.CmpOp.sle
    | .sgt => ``LeanQbe.T.CmpOp.sgt | .sge => ``LeanQbe.T.CmpOp.sge

meta def fcmpOpToExpr (o : FCmpOp) : Lean.Expr :=
  Lean.mkConst <| match o with
    | .eq => ``LeanQbe.T.FCmpOp.eq | .ne => ``LeanQbe.T.FCmpOp.ne
    | .lt => ``LeanQbe.T.FCmpOp.lt | .le => ``LeanQbe.T.FCmpOp.le
    | .gt => ``LeanQbe.T.FCmpOp.gt | .ge => ``LeanQbe.T.FCmpOp.ge
    | .ord => ``LeanQbe.T.FCmpOp.ord | .uno => ``LeanQbe.T.FCmpOp.uno

private meta def mkTyOp (nm : Name) (t : Ty) : Except String Lean.Expr :=
  pure <| mkApp (Lean.mkConst nm) (tyToExpr t)

private meta def mkNatOp (nm : Name) (n : Nat) : Except String Lean.Expr :=
  pure <| mkApp (Lean.mkConst nm) (mkNatLit n)

private meta def mkNat2Op (nm : Name) (m n : Nat) : Except String Lean.Expr :=
  pure <| mkApp2 (Lean.mkConst nm) (mkNatLit m) (mkNatLit n)

meta def opCodeToExpr {sig rs : List Ty} : OpCode sig rs → Except String Lean.Expr
  | .copy t => mkTyOp ``LeanQbe.T.OpCode.copy t
  | .add t => mkTyOp ``LeanQbe.T.OpCode.add t
  | .sub t => mkTyOp ``LeanQbe.T.OpCode.sub t
  | .mul t => mkTyOp ``LeanQbe.T.OpCode.mul t
  | .neg t => mkTyOp ``LeanQbe.T.OpCode.neg t
  | .and t => mkTyOp ``LeanQbe.T.OpCode.and t
  | .or t => mkTyOp ``LeanQbe.T.OpCode.or t
  | .xor t => mkTyOp ``LeanQbe.T.OpCode.xor t
  | .not t => mkTyOp ``LeanQbe.T.OpCode.not t
  | .shl t => mkTyOp ``LeanQbe.T.OpCode.shl t
  | .lshr t => mkTyOp ``LeanQbe.T.OpCode.lshr t
  | .ashr t => mkTyOp ``LeanQbe.T.OpCode.ashr t
  | .rotl t => mkTyOp ``LeanQbe.T.OpCode.rotl t
  | .rotr t => mkTyOp ``LeanQbe.T.OpCode.rotr t
  | .fadd t => mkTyOp ``LeanQbe.T.OpCode.fadd t
  | .fsub t => mkTyOp ``LeanQbe.T.OpCode.fsub t
  | .fmul t => mkTyOp ``LeanQbe.T.OpCode.fmul t
  | .fdiv t => mkTyOp ``LeanQbe.T.OpCode.fdiv t
  | .fneg t => mkTyOp ``LeanQbe.T.OpCode.fneg t
  | .clz n => mkNatOp ``LeanQbe.T.OpCode.clz n
  | .ctz n => mkNatOp ``LeanQbe.T.OpCode.ctz n
  | .popcnt n => mkNatOp ``LeanQbe.T.OpCode.popcnt n
  | .ofBool n => mkNatOp ``LeanQbe.T.OpCode.ofBool n
  | .addc n => mkNatOp ``LeanQbe.T.OpCode.addc n
  | .subb n => mkNatOp ``LeanQbe.T.OpCode.subb n
  | .umulw n => mkNatOp ``LeanQbe.T.OpCode.umulw n
  | .udiv n => mkNatOp ``LeanQbe.T.OpCode.udiv n
  | .sdiv n => mkNatOp ``LeanQbe.T.OpCode.sdiv n
  | .urem n => mkNatOp ``LeanQbe.T.OpCode.urem n
  | .srem n => mkNatOp ``LeanQbe.T.OpCode.srem n
  | .zext m n => mkNat2Op ``LeanQbe.T.OpCode.zext m n
  | .sext m n => mkNat2Op ``LeanQbe.T.OpCode.sext m n
  | .trunc m n => mkNat2Op ``LeanQbe.T.OpCode.trunc m n
  | .cmp o t m _ =>
    let me := tyToExpr m
    pure <| mkApp4 (Lean.mkConst ``LeanQbe.T.OpCode.cmp)
      (cmpOpToExpr o) (tyToExpr t) me (mkMaskEqRefl me)
  | .fcmp o t m _ =>
    let me := tyToExpr m
    pure <| mkApp4 (Lean.mkConst ``LeanQbe.T.OpCode.fcmp)
      (fcmpOpToExpr o) (tyToExpr t) me (mkMaskEqRefl me)
  | .bitcast t u _ =>
    let eqPf := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero])
      (Lean.mkConst ``Nat) (mkNatLit t.size)
    pure <| mkApp3 (Lean.mkConst ``LeanQbe.T.OpCode.bitcast) (tyToExpr t) (tyToExpr u) eqPf
  | .fptoui f n => pure <| mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.fptoui) (fmtConst f) (mkNatLit n)
  | .fptosi f n => pure <| mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.fptosi) (fmtConst f) (mkNatLit n)
  | .uitofp n f => pure <| mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.uitofp) (mkNatLit n) (fmtConst f)
  | .sitofp n f => pure <| mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.sitofp) (mkNatLit n) (fmtConst f)
  | _ => throw "unsupported OpCode in C0 elaborator"

meta structure ElabCtx : Type where
  V : Lean.Expr
  L : Lean.Expr
  rsExpr : Lean.Expr
  depth : Nat := 0
  vars : Std.HashMap Nat
    (Nat × Option (Nat × Lean.Expr × Lean.Expr × List Lean.Expr) × Lean.Expr) := {}
  lbls : Std.HashMap Nat
    (Nat × Option (Nat × Lean.Expr × Lean.Expr × List Lean.Expr) × Lean.Expr) := {}

meta def ElabCtx.varRef (ctx : ElabCtx) (id : Nat) : Except String Lean.Expr :=
  match ctx.vars.get? id with
  | some (lvl, proj?, _) =>
    let base := Lean.Expr.bvar (ctx.depth - 1 - lvl)
    pure <| match proj? with
      | none => base
      | some (i, kind, f, tys) => mkTypedProj kind f tys base i
  | none => throw s!"C0 elab: unbound variable id {id}"

meta def ElabCtx.lblRef (ctx : ElabCtx) (lid : Nat) : Except String (Lean.Expr × Lean.Expr) :=
  match ctx.lbls.get? lid with
  | some (lvl, proj?, sigExpr) =>
    let base := Lean.Expr.bvar (ctx.depth - 1 - lvl)
    let r := match proj? with
      | none => base
      | some (i, kind, f, tys) => mkTypedProj kind f tys base i
    pure (r, sigExpr)
  | none => throw s!"C0 elab: unbound label id {lid}"

meta def argToExpr (ctx : ElabCtx) (a : LArg) : Except String Lean.Expr := do
  let tyE := tyToExpr a.ty
  match a with
  | .var id _ =>
    let vRef ← ctx.varRef id
    pure <| mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.var) ctx.V tyE vRef
  | .imm t v =>
    pure <| mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.imm) ctx.V tyE (valToExpr t v)

meta def argListToTupExpr (ctx : ElabCtx) (args : List LArg) : Except String Lean.Expr := do
  let argF := mkArgApp ctx.V
  let tys := args.map fun a => tyToExpr a.ty
  let vals ← args.mapM (argToExpr ctx)
  pure (mkTupElems tyConst argF tys vals)

meta def withLoadVar (ctx : ElabCtx) (lv : LVar) (k : ElabCtx → Except String Lean.Expr) :
    Except String Lean.Expr := do
  let lvl := ctx.depth
  let tyE := tyToExpr lv.ty
  let vTy := mkApp ctx.V tyE
  let ctx' := {
    ctx with
    depth := ctx.depth + 1
    vars := ctx.vars.insert lv.id (lvl, none, tyE)
  }
  let body ← k ctx'
  pure (.lam (Name.mkSimple lv.name) vTy body .default)

meta def withTupleLVars (ctx : ElabCtx) (lvs : List LVar) (k : ElabCtx → Except String Lean.Expr) :
    Except String Lean.Expr := do
  let lvl := ctx.depth
  let elemTys := lvs.map fun v => tyToExpr v.ty
  let tupTy := mkTupTy tyConst ctx.V elemTys
  let mut vars := ctx.vars
  let mut i := 0
  for lv in lvs do
    let proj := some (i, tyConst, ctx.V, elemTys)
    vars := vars.insert lv.id (lvl, proj, tyToExpr lv.ty)
    i := i + 1
  let ctx' := { ctx with depth := ctx.depth + 1, vars }
  let body ← k ctx'
  pure (.lam `p tupTy body .default)

meta def withGroupLabelsL (ctx : ElabCtx) (blocks : List (Nat × List LVar × LExpr))
    (k : ElabCtx → Except String Lean.Expr) : Except String Lean.Expr := do
  let lvl := ctx.depth
  let elemTys := blocks.map fun (_, ps, _) => listLit tyConst (ps.map fun v => tyToExpr v.ty)
  let tupTy := mkTupTy listTyConst ctx.L elemTys
  let mut lbls := ctx.lbls
  let mut j := 0
  for (lid, ps, _) in blocks do
    let sigE := listLit tyConst (ps.map fun v => tyToExpr v.ty)
    let proj := some (j, listTyConst, ctx.L, elemTys)
    lbls := lbls.insert lid (lvl, proj, sigE)
    j := j + 1
  let ctx' := { ctx with depth := ctx.depth + 1, lbls }
  let body ← k ctx'
  pure (.lam `Js tupTy body .default)

meta partial def lExprToLeanExpr (ctx : ElabCtx) : LExpr → Except String Lean.Expr
  | .let_ op binders k => do
    let rsE := listLit tyConst (op.rs.map tyToExpr)
    let sigE := listLit tyConst (op.sig.map tyToExpr)
    let codeE ← opCodeToExpr op.code
    let argsE ← argListToTupExpr ctx op.args
    let opE := mkAppN (Lean.mkConst ``LeanQbe.T.Op.mk) #[ctx.V, rsE, sigE, codeE, argsE]
    let lamE ← withTupleLVars ctx binders fun ctx' => lExprToLeanExpr ctx' k
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.let_) #[ctx.V, ctx.L, ctx.rsExpr, rsE, opE, lamE]
  | .load t addr binder k => do
    let tE := tyToExpr t
    let addrE ← argToExpr ctx addr
    let lamE ← withLoadVar ctx binder fun ctx' => lExprToLeanExpr ctx' k
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.load) #[ctx.V, ctx.L, ctx.rsExpr, tE, addrE, lamE]
  | .store t val addr k => do
    let tE := tyToExpr t
    let valE ← argToExpr ctx val
    let addrE ← argToExpr ctx addr
    let restE ← lExprToLeanExpr ctx k
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.store)
      #[ctx.V, ctx.L, ctx.rsExpr, tE, valE, addrE, restE]
  | .call f as bs args binders k => do
    let asE := listLit tyConst (as.map tyToExpr)
    let bsE := listLit tyConst (bs.map tyToExpr)
    let argsE ← argListToTupExpr ctx args
    let lamE ← withTupleLVars ctx binders fun ctx' => lExprToLeanExpr ctx' k
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.call)
      #[ctx.V, ctx.L, ctx.rsExpr, mkStrLit f, asE, bsE, argsE, lamE]
  | .jnz c t e => do
    let cE ← argToExpr ctx c
    let tE ← lExprToLeanExpr ctx t
    let eE ← lExprToLeanExpr ctx e
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.jnz) #[ctx.V, ctx.L, ctx.rsExpr, cE, tE, eE]
  | .jump lid _ args => do
    let (lRef, tsE) ← ctx.lblRef lid
    let argsE ← argListToTupExpr ctx args
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.jump)
      #[ctx.V, ctx.L, ctx.rsExpr, tsE, lRef, argsE]
  | .ret _ args => do
    let vsE ← argListToTupExpr ctx args
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.ret) #[ctx.V, ctx.L, ctx.rsExpr, vsE]
  | .exit f as args => do
    let asE := listLit tyConst (as.map tyToExpr)
    let argsE ← argListToTupExpr ctx args
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.exit)
      #[ctx.V, ctx.L, ctx.rsExpr, mkStrLit f, asE, argsE]
  | .hlt =>
    pure <| mkApp3 (Lean.mkConst ``LeanQbe.T.Expr.hlt) ctx.V ctx.L ctx.rsExpr
  | .group blocks k => do
    let sigList := blocks.map fun (_, ps, _) => listLit tyConst (ps.map fun v => tyToExpr v.ty)
    let sigE := listLit listTyConst sigList
    let bodiesLam ← withGroupLabelsL ctx blocks fun ctx' => mkBlocksExpr ctx' blocks
    let entryLam ← withGroupLabelsL ctx blocks fun ctx' => lExprToLeanExpr ctx' k
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.group)
      #[ctx.V, ctx.L, ctx.rsExpr, sigE, bodiesLam, entryLam]
where
  mkBlocksExpr (ctx : ElabCtx) : List (Nat × List LVar × LExpr) → Except String Lean.Expr
    | [] => pure <| mkApp3 (Lean.mkConst ``LeanQbe.T.Blocks.nil) ctx.V ctx.L ctx.rsExpr
    | (_, ps, body) :: rest => do
      let tsE := listLit tyConst (ps.map fun v => tyToExpr v.ty)
      let restSigE := listLit listTyConst
        (rest.map fun (_, rps, _) => listLit tyConst (rps.map fun v => tyToExpr v.ty))
      let bLam ← withTupleLVars ctx ps fun ctx' => lExprToLeanExpr ctx' body
      let bsE ← mkBlocksExpr ctx rest
      pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Blocks.cons)
        #[ctx.V, ctx.L, ctx.rsExpr, tsE, restSigE, bLam, bsE]

meta def lFnToLeanExprM (lfn : LFn) : MetaM (Lean.Expr × Lean.Expr × Lean.Expr) := do
  let asList := lfn.params.map fun v => tyToExpr v.ty
  let rsList := lfn.rs.map tyToExpr
  let asExpr := listLit tyConst asList
  let rsExpr := listLit tyConst rsList
  let vSort := Lean.Expr.forallE `t tyConst (.sort 1) .default
  let lSort := Lean.Expr.forallE `ts listTyConst (.sort 1) .default
  withLocalDeclD `V vSort fun V =>
  withLocalDeclD `L lSort fun L => do
    let initCtx : ElabCtx := { V, L, rsExpr }
    let bodyLam ← match withTupleLVars initCtx lfn.params
        fun ctx' => lExprToLeanExpr ctx' lfn.body with
      | .ok e => pure e
      | .error err => throwError err
    let funcExpr ← mkLambdaFVars #[V, L] bodyLam
    pure (funcExpr, asExpr, rsExpr)

/-! ## Acyclicity Check for Lowered Modules -/

meta partial def lExprCalls : LExpr → List Sym
  | .let_ _ _ k | .load _ _ _ k | .store _ _ _ k => lExprCalls k
  | .call f _ _ _ _ k => f :: lExprCalls k
  | .jnz _ t e => lExprCalls t ++ lExprCalls e
  | .jump _ _ _ | .ret _ _ | .exit _ _ _ | .hlt => []
  | .group blocks k =>
    (blocks.foldl (fun acc (_, _, b) => acc ++ lExprCalls b) []) ++ lExprCalls k

meta def checkLModuleAcyclic (m : LModule) : Except String Unit := do
  let mut definedSoFar : Std.HashSet String := {}
  let mut extSet : Std.HashSet String := {}
  for ex in m.externs do
    if extSet.contains ex.name then
      throw s!"duplicate extern declaration '{ex.name}'"
    extSet := extSet.insert ex.name
  let fnNames : Std.HashSet String := m.fns.foldl (fun s f => s.insert f.name) {}
  for fn in m.fns do
    if definedSoFar.contains fn.name then
      throw s!"duplicate function definition '{fn.name}'"
    if extSet.contains fn.name then
      throw s!"function '{fn.name}' collides with extern declaration"
    for callee in lExprCalls fn.body do
      if callee == fn.name then
        throw s!"recursive call to '{callee}' is not permitted in acyclic C0 module"
      if !definedSoFar.contains callee && !extSet.contains callee then
        if fnNames.contains callee then
          throw (s!"forward/cyclic call from '{fn.name}' to '{callee}' violates " ++
            "callees-first acyclic module ordering")
        else
          throw s!"call from '{fn.name}' to undeclared function '{callee}'"
    definedSoFar := definedSoFar.insert fn.name

/-! ## Commands: `c0_decl!`, `c0_file!`, and `#c0_shape` -/

/-- Add a non-polymorphic definition, compile it, and enable realizations. With
`forceExpose := true` the body is exported even outside an `@[expose]` section (so downstream
`module` proofs can unfold it); otherwise this is exactly `addAndCompile`. -/
meta def addExposedDecl (name : Name) (type value : Lean.Expr) (forceExpose : Bool := false) :
    CoreM Unit := do
  let decl := .defnDecl {
    name, levelParams := [], type, value, hints := .regular 0, safety := .safe
  }
  addDecl decl (forceExpose := forceExpose)
  compileDecl decl
  enableRealizationsForConst name

/-- Elaborate a C0 translation unit into kernel `<fn>_body : Func as rs` / `<fn> : Fn` defs in
the current namespace, plus `<pfx>_fns` (and, if `emitModule`, `<pfx>_module`) when a prefix
is given. `exits` lists runtime symbols whose calls are promoted into `.exit` terminators;
`forceExpose` exports all bodies; `registerShapes` records `#c0_shape` metadata. -/
meta def elabC0Module (modPrefix? : Option Name) (src : String) (exits : List Sym := [])
    (forceExpose : Bool := false) (registerShapes : Bool := true) (emitModule : Bool := true) :
    CommandElabM Unit := do
  let env ← getEnv
  let hdrMap := getC0Headers env
  let tu ← match parseC0 src hdrMap with
    | .ok tu => pure tu
    | .error err => throwError err
  let lmod ← match lowerTranslationUnit tu with
    | .ok m => pure m
    | .error err => throwError err
  let lmod : LModule := if exits.isEmpty then lmod else
    { lmod with fns := lmod.fns.map fun f => { f with body := promoteExitCalls exits f.body } }
  if let .error err := checkLModuleAcyclic lmod then
    throwError err
  let ns ← getCurrNamespace
  let modAudit := auditTranslationUnit tu (modPrefix?.map (·.toString) |>.getD "anon_module")
  let mut fnConstNames : List Name := []
  for lfn in lmod.fns do
    let leanName := ns ++ Name.mkSimple lfn.name
    let bodyName := ns ++ Name.mkSimple (lfn.name ++ "_body")
    let (funcExpr, asExpr, rsExpr) ← liftTermElabM (lFnToLeanExprM lfn)
    -- Define `<lfn.name>_body : Func as rs` first so `<lfn.name> : Fn` references it cleanly
    let funcTy := mkApp2 (Lean.mkConst ``LeanQbe.T.Func) asExpr rsExpr
    liftCoreM <| addExposedDecl bodyName funcTy funcExpr forceExpose
    let fnExpr := mkApp4 (Lean.mkConst ``LeanQbe.T.Fn.mk)
      (mkStrLit lfn.name) asExpr rsExpr (Lean.mkConst bodyName)
    liftCoreM <| addExposedDecl leanName (Lean.mkConst ``LeanQbe.T.Fn) fnExpr forceExpose
    if registerShapes then
      modifyEnv fun env =>
        let env := c0ShapeExt.addEntry env (leanName, lfn.shape)
        c0ShapeExt.addEntry env (bodyName, lfn.shape)
    if let some fnRep := modAudit.fnReports.find? (·.fnName == lfn.name) then
      modifyEnv fun env =>
        let env := c0AuditExt.addEntry env (leanName, .fn fnRep)
        c0AuditExt.addEntry env (bodyName, .fn fnRep)
    fnConstNames := fnConstNames ++ [leanName]
  if let some pfx := modPrefix? then
    let modLeanName := ns ++ pfx
    modifyEnv fun env => c0AuditExt.addEntry env (modLeanName, .mod modAudit)
    let fnType := Lean.mkConst ``LeanQbe.T.Fn
    let fnsName := ns ++ Name.mkSimple (pfx.toString ++ "_fns")
    let fnsTy := mkApp (Lean.mkConst ``List [.one]) fnType
    let fnsVal := listLit fnType (fnConstNames.map Lean.mkConst) .one
    liftCoreM <| addExposedDecl fnsName fnsTy fnsVal forceExpose
    if emitModule then
      let modName := ns ++ Name.mkSimple (pfx.toString ++ "_module")
      let extsExpr := listLit (Lean.mkConst ``LeanQbe.T.Extern) <| lmod.externs.map fun ex =>
        mkApp3 (Lean.mkConst ``LeanQbe.T.Extern.mk) (mkStrLit ex.name)
          (listLit tyConst (ex.as.map tyToExpr)) (listLit tyConst (ex.rs.map tyToExpr))
      let exitsExpr := listLit (Lean.mkConst ``LeanQbe.T.Sym) (lmod.exits.map mkStrLit)
      let modVal := mkApp3 (Lean.mkConst ``LeanQbe.T.Module.mk)
        (Lean.mkConst fnsName) extsExpr exitsExpr
      liftCoreM <| addExposedDecl modName (Lean.mkConst ``LeanQbe.T.Module) modVal forceExpose

syntax "c0_header! " ident str : command
syntax "c0_header! " str str : command
syntax "c0_decl! " (ident)? str : command
syntax "c0_file! " (ident)? str : command
syntax "#c0_shape " ident : command
syntax "#c0_shape " str : command
syntax "#c0_audit " ident : command
syntax "#c0_audit " str : command

elab_rules : command
  | `(c0_header! $id:ident $src:str) => do
    let name := id.getId.toString
    modifyEnv fun env => c0HeaderExt.addEntry env (name, src.getString)
  | `(c0_header! $id:str $src:str) => do
    let name := id.getString
    modifyEnv fun env => c0HeaderExt.addEntry env (name, src.getString)
  | `(c0_decl! $[$pfx:ident]? $src:str) =>
    elabC0Module (pfx.map (·.getId)) src.getString
  | `(c0_file! $[$pfx:ident]? $path:str) => do
    let content ← IO.FS.readFile path.getString
    elabC0Module (pfx.map (·.getId)) content
  | `(#c0_shape $id:ident) => do
    let (byLean, byC) := c0ShapeExt.getState (← getEnv)
    let ns ← getCurrNamespace
    let sh? := byLean.find? id.getId <|> byLean.find? (ns ++ id.getId) <|>
      byC.get? id.getId.toString
    match sh? with
    | some sh => logInfo sh.format
    | none => throwErrorAt id s!"no C0 shape metadata registered for '{id.getId}'"
  | `(#c0_shape $nm:str) => do
    let (_, byC) := c0ShapeExt.getState (← getEnv)
    match byC.get? nm.getString with
    | some sh => logInfo sh.format
    | none => throwErrorAt nm s!"no C0 shape metadata registered for \"{nm.getString}\""
  | `(#c0_audit $id:ident) => do
    let (byLean, byC) := c0AuditExt.getState (← getEnv)
    let ns ← getCurrNamespace
    let ent? := byLean.find? id.getId <|> byLean.find? (ns ++ id.getId) <|>
      byC.get? id.getId.toString
    match ent? with
    | some (.fn rep) => logInfo rep.format
    | some (.mod rep) => logInfo rep.format
    | none => throwErrorAt id s!"no C0 audit metadata registered for '{id.getId}'"
  | `(#c0_audit $nm:str) => do
    let (_, byC) := c0AuditExt.getState (← getEnv)
    match byC.get? nm.getString with
    | some (.fn rep) => logInfo rep.format
    | some (.mod rep) => logInfo rep.format
    | none => throwErrorAt nm s!"no C0 audit metadata registered for \"{nm.getString}\""

end LeanQbe.T.Frontend.C0
