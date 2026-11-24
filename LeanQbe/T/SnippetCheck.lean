module

public import LeanQbe.T.Target
public import LeanQbe.T.Flat
public import LeanQbe.T.Main
public import LeanQbe.T.SpillSnippet

/-!
# Target-Generic `@predictable` Static Budget & `AsmIso` Framework (`SnippetCheck`)

Provides fail-loud, IP-attributed static checking for `@predictable` and lifted snippets
without touching any existing compiler files or importing architecture crates:

* `SnippetBudget`, `SnippetDiag`, `BudgetReport`: configurable thresholds for interior spills
  (`maxInteriorSpills := 0`), edge moves (`maxEdgeMoves`), if-conversion (`forbidIfConv`),
  total instructions (`maxTotalInsns`), per-op expansion (`maxOpExpansion`), and call freedom
  (`requireZeroCalls := true`).
* `auditRegionHints`: checks `SpillSnippet.RegionFind` + `I.Hints` (`PreStep` moves at interior
  vs entry/exit edges, `OpCode.select` if-conversion presence, `.call` freedom), emitting exact
  per-IP diagnostics on violation.
* `extractSubHints`: projects `I.Hints` back onto `sDirect` via `TreeZip` so callers can lower
  and profile the exact in-place snippet register/flag/variant assignment standalone.
* `IsoVerdict` & generic CFG bijection helpers (`bindBijection`): shared across `Amd64/Snippet`
  and `Arm64/Snippet` for Tier 1 / Tier 2 `AsmIso` checking.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

namespace SnippetCheck

/-! ## `@predictable` Static Budget Specification & Diagnostics -/

/-- Configurable predictability contract for an embedded or standalone snippet. -/
structure SnippetBudget where
  name              : String := "snippet"
  maxInteriorSpills : Nat := 0
  maxEdgeMoves      : Option Nat := none
  forbidIfConv      : Bool := false
  maxTotalInsns     : Option Nat := none
  maxOpExpansion    : Option Nat := none
  requireZeroCalls  : Bool := true
  deriving DecidableEq, Repr, Inhabited

namespace SnippetBudget

/-- Strict `@predictable` budget enforcing `0` interior spills, `0` calls, and no if-conversion. -/
def predictable (name : String := "snippet") (maxInsns? : Option Nat := none) :
    SnippetBudget :=
  { name := name
    maxInteriorSpills := 0
    forbidIfConv := true
    maxTotalInsns := maxInsns?
    requireZeroCalls := true }

end SnippetBudget

/-- Single IP-attributed diagnostic emitted when a snippet violates its `@predictable` budget. -/
structure SnippetDiag where
  ip?     : Option Nat := none
  kind    : String
  message : String
  deriving DecidableEq, Repr, Inhabited

instance : ToString SnippetDiag where
  toString d :=
    match d.ip? with
    | some ip => s!"[{d.kind} @ ip {ip}] {d.message}"
    | none    => s!"[{d.kind}] {d.message}"

/-- Summary of checks passed for a `@predictable` region or standalone snippet. -/
structure BudgetReport where
  name           : String
  irOps          : Nat
  interiorSpills : Nat
  entryEdgeMoves : Nat
  exitEdgeMoves  : Nat
  totalInsns?    : Option Nat := none
  notes          : List String := []
  deriving DecidableEq, Repr, Inhabited

def isSpillMove {R V C : Type} : Move R V C → Bool
  | .st _ _ | .ld _ _ | .vst _ _ _ | .vld _ _ _ => true
  | _ => false

def isEdgeRegMove {R V C : Type} : Move R V C → Bool
  | .st _ _ | .ld _ _ | .vst _ _ _ | .vld _ _ _ | .mov _ _ | .vmov _ _ _ => true
  | _ => false

def isSelectOpCode : {as bs : List Ty} → OpCode as bs → Bool
  | _, _, .select _ => true
  | _, _, _ => false

mutual
/-- Collect `(ip)` sites of any `.let_` with `OpCode.select` in a `Live.Tree`. -/
def collectSelectIps : Live.Tree → List Nat
  | .let_ _ ip _ _ op k =>
    (if isSelectOpCode op.code then [ip] else []) ++ collectSelectIps k
  | .load _ _ _ _ _ k | .store _ _ _ _ _ k | .call _ _ _ _ _ _ _ k | .skip _ _ k =>
    collectSelectIps k
  | .jnz _ _ _ _ t e => collectSelectIps t ++ collectSelectIps e
  | .group _ bs k => collectSelectIpsBlocks bs ++ collectSelectIps k
  | _ => []

/-- Block-list companion of `collectSelectIps`. -/
def collectSelectIpsBlocks : Live.TreeBlocks → List Nat
  | .nil => []
  | .cons _ _ b bs => collectSelectIps b ++ collectSelectIpsBlocks bs
end

-- Count IR operation / terminator nodes in a `Live.Tree`.
mutual
def countTreeIrOps : Live.Tree → Nat
  | .let_ _ _ _ _ _ k | .load _ _ _ _ _ k | .store _ _ _ _ _ k
  | .call _ _ _ _ _ _ _ k | .skip _ _ k => 1 + countTreeIrOps k
  | .jnz _ _ _ _ t e => 1 + countTreeIrOps t + countTreeIrOps e
  | .jump .. | .ret .. | .exit .. => 1
  | .stop _ => 0
  | .group _ bs k => countBlocksIrOps bs + countTreeIrOps k

/-- Block-list companion of `countTreeIrOps`. -/
def countBlocksIrOps : Live.TreeBlocks → Nat
  | .nil => 0
  | .cons _ _ b bs => countTreeIrOps b + countBlocksIrOps bs
end

/-- Project `I.Hints` from an outer inlined function back onto `sDirect`'s `(nv, ip, lid)` index
space via `TreeZip` (preserving registers, flags, variants, elides, and `clearFlags`, with `nslots = 0`
for interior spill-free replay). -/
def extractSubHints (I : Isa) (hOuter : I.Hints) (z : SpillSnippet.TreeZip) : I.Hints :=
  let dest := z.nvMap.foldl (fun t (v1, v2) =>
    match hOuter.dest.find? v2 with
    | some loc => t.insert v1 loc
    | none => t) .empty
  let entry := z.lidMap.foldl (fun t (lid1, lid2) =>
    match hOuter.entry.find? lid2 with
    | some enO =>
      let live1 := enO.live.filterMap fun (sa, loc) =>
        match sa with
        | .var v2 =>
          match z.nvMap.find? (·.2 == v2) with
          | some (v1, _) => some (SymArg.var v1, loc)
          | none => none
        | _ => some (sa, loc)
      t.insert lid1 ⟨live1, enO.ploc⟩
    | none => t) .empty
  let variant := z.ipMap.foldl (fun t (ip1, ip2) =>
    match hOuter.variant.find? ip2 with
    | some vh => t.insert ip1 vh
    | none => t) .empty
  let elide := z.ipMap.foldl (fun t (ip1, ip2) =>
    match hOuter.elide.find? ip2 with
    | some e => t.insert ip1 e
    | none => t) .empty
  let invertJnz := z.ipMap.foldl (fun t (ip1, ip2) =>
    match hOuter.invertJnz.find? ip2 with
    | some iv => t.insert ip1 iv
    | none => t) .empty
  let pre := z.ipMap.foldl (fun t (ip1, ip2) =>
    match hOuter.pre.find? ip2 with
    | some ps => if ps.clearFlags then t.insert ip1 { clearFlags := true, moves := [] } else t
    | none => t) .empty
  let deferJnz := z.ipMap.foldl (fun t (ip1, ip2) =>
    match hOuter.deferJnz.find? ip2 with
    | some b => t.insert ip1 b
    | none => t) .empty
  let deferLea := z.ipMap.foldl (fun t (ip1, ip2) =>
    match hOuter.deferLea.find? ip2 with
    | some b => t.insert ip1 b
    | none => t) .empty
  let saved := hOuter.saved
  { dest := dest, entry := entry, pre := pre, variant := variant,
    elide := elide, invertJnz := invertJnz, deferJnz := deferJnz, deferLea := deferLea,
    nslots := 0, saved := saved }

/-- Audit an embedded snippet region `reg` under `hOuter` against `budget`, producing a
fail-loud list of IP-attributed `SnippetDiag`s or a passing `BudgetReport`. -/
def auditRegionHints (I : Isa) (hOuter : I.Hints) (reg : SpillSnippet.RegionFind)
    (budget : SnippetBudget := {}) (bodyInsns? : Option Nat := none) :
    Except (List SnippetDiag) BudgetReport :=
  let diags : List SnippetDiag := []
  let diags :=
    if budget.requireZeroCalls && SpillSnippet.treeHasCall reg.calleeTree then
      diags ++ [{ kind := "call_in_snippet",
                  message := s!"@{budget.name} contains a `.call` node (unpoisoning impossible)" }]
    else diags
  let selectIps := if budget.forbidIfConv then collectSelectIps reg.calleeTree else []
  let diags := selectIps.foldl (fun acc ip =>
    acc ++ [{ ip? := some ip, kind := "if_conv",
              message := s!"if-conversion (.select) in @{budget.name}; set `noIfOpt := true`" }])
    diags
  let interiorIps := reg.calleeIps.filter (· != reg.startIp)
  let (interiorSpills, spillDiags) := interiorIps.foldl (fun (cnt, ds) ip =>
    match hOuter.pre.find? ip with
    | some ps =>
      let spCnt := (ps.moves.filter isSpillMove).length
      if spCnt > 0 then
        let d : SnippetDiag :=
          { ip? := some ip, kind := "interior_spill",
            message := s!"PreStep ip {ip} inside @{budget.name} emitted {spCnt} spill move(s)" }
        (cnt + spCnt, ds ++ [d])
      else (cnt, ds)
    | none => (cnt, ds)) (0, [])
  let diags :=
    if interiorSpills > budget.maxInteriorSpills then diags ++ spillDiags else diags
  let entryEdgeMoves := match hOuter.pre.find? reg.startIp with
    | some ps => (ps.moves.filter isEdgeRegMove).length
    | none => 0
  let exitEdgeMoves := match hOuter.pre.find? reg.exitNextIp with
    | some ps => (ps.moves.filter isEdgeRegMove).length
    | none => 0
  let totalEdgeMoves := entryEdgeMoves + exitEdgeMoves
  let diags := match budget.maxEdgeMoves with
    | some maxE =>
      if totalEdgeMoves > maxE then
        diags ++ [{ ip? := some reg.startIp, kind := "edge_moves",
                    message := s!"@{budget.name} emitted {totalEdgeMoves} edge moves > budget {maxE}" }]
      else diags
    | none => diags
  let diags := match budget.maxTotalInsns, bodyInsns? with
    | some maxI, some n =>
      if n > maxI then
        diags ++ [{ kind := "insn_budget",
                    message := s!"@{budget.name} emitted {n} insns > budget {maxI}" }]
      else diags
    | _, _ => diags
  if !diags.isEmpty then .error diags
  else
    .ok {
      name := budget.name
      irOps := countTreeIrOps reg.calleeTree
      interiorSpills := interiorSpills
      entryEdgeMoves := entryEdgeMoves
      exitEdgeMoves := exitEdgeMoves
      totalInsns? := bodyInsns?
    }

/-- Audit an embedded snippet `sDirect` inside `outerLate` using hints `hOuter`, optionally
re-lowering `sDirect` standalone to count exact emitted directives (`totalInsns?`). -/
def auditSnippetInOuter (I : Isa) (sDirect outerLate : Fn) (hOuter : I.Hints)
    (budget : SnippetBudget := {})
    (countBodyInsns? : Option (List I.Directive → Nat) := none) :
    Except (List SnippetDiag) BudgetReport := do
  let (t0, _, _, _, _, _) := Live.Tree.ofFn outerLate
  let (tSnip, _, _, _, _, _) := Live.Tree.ofFn sDirect
  let (reg, z) ←
    match SpillSnippet.findMarkedRegion?
        SpillSnippet.defaultStartMagics SpillSnippet.defaultExitMagics t0 with
    | some r =>
      match SpillSnippet.zipTrees tSnip r.calleeTree with
      | some z => pure (r, z)
      | none => .error [{ kind := "region_mismatch",
                          message := s!"@{budget.name} marked region failed `zipTrees`" }]
    | none =>
      match SpillSnippet.findInlinedRegionByTree? tSnip t0 with
      | some rz => pure rz
      | none => .error [{ kind := "region_not_found",
                          message := s!"@{budget.name} region not found in `{outerLate.name}`" }]
  let bodyInsns? ← match countBodyInsns? with
    | none => pure none
    | some countFn =>
      let hSub := extractSubHints I hOuter z
      match Rega.lowerFn I hSub sDirect.ext sDirect with
      | .ok dirs => pure (some (countFn dirs))
      | .error _ =>
        match Rega.lowerFn I (Spill.hints I sDirect) sDirect.ext sDirect with
        | .ok dirs => pure (some (countFn dirs))
        | .error e =>
          .error [{ kind := "sub_lower_err",
                    message := s!"@{budget.name} extracted sub-hints failed lowering: {e}" }]
  auditRegionHints I hOuter reg budget bodyInsns?

/-- Lower `outerLate` with `hOuter` AND verify `budget` over `sDirect`'s region, returning both
the lowered assembly directives and the verified `BudgetReport`. -/
def lowerAndCheckBudget (I : Isa) (sDirect outerLate : Fn) (hOuter : I.Hints)
    (budget : SnippetBudget := {})
    (countBodyInsns? : Option (List I.Directive → Nat) := none) :
    Except (List SnippetDiag) (List I.Directive × BudgetReport) := do
  match Rega.lowerFn I hOuter outerLate.ext outerLate with
  | .error e =>
    .error [{ kind := "rega_error", message := s!"`{outerLate.name}` Rega failed: {e}" }]
  | .ok dirs =>
    let rep ← auditSnippetInOuter I sDirect outerLate hOuter budget countBodyInsns?
    pure (dirs, rep)

/-! ## Target-Generic `AsmIso` Verdict & CFG Bijection Helpers -/

/-- Outcome of structural AST/CFG assembly isomorphism checking (`AsmIso`). -/
inductive IsoVerdict where
  | tier1 (blocks ops : Nat)
  | tier2 (blocks ops diffs : Nat) (notes : List String)
  | fail  (reason detail : String)
  deriving Repr, BEq, Inhabited

/-- True iff `v` passed either Tier 1 (exact modulo alpha/block labels) or Tier 2 (modulo known
safe canonicalizations). -/
def IsoVerdict.passed : IsoVerdict → Bool
  | .tier1 .. | .tier2 .. => true
  | .fail .. => false

instance : ToString IsoVerdict where
  toString
    | .tier1 b o => s!"tier1(blocks={b}, ops={o})"
    | .tier2 b o d ns => s!"tier2(blocks={b}, ops={o}, diffs={d}, {ns})"
    | .fail r d => s!"fail({r}: {d})"

/-- Check and extend a 1-to-1 bijection `List (α × α)` (`false` on inconsistent mapping). -/
def bindBijection {α : Type} [BEq α] (a b : α) (m : List (α × α)) : Option (List (α × α)) :=
  match m.find? (·.1 == a) with
  | some (_, b') => if b' == b then some m else none
  | none =>
    if m.any (·.2 == b) then none else some ((a, b) :: m)

/-- True iff assembly label `l` names a compiler-local basic block (`.L...`). -/
def isLocalLabel (l : String) : Bool :=
  l.startsWith ".L" || (l.splitOn ".L").length > 1

/-- Normalized CFG block terminator parameterized by target branch condition type `BC`. -/
inductive CfgTerm (BC : Type) where
  | ret
  | exit (sym : String)
  | jmp (tgt : String)
  | jcc (cond : BC) (taken : String) (fall : String)
  | fall (tgt : String)
  | endMark
  deriving Repr, BEq

instance {BC : Type} : Inhabited (CfgTerm BC) := ⟨.endMark⟩

/-- Summary instruction/code-quality metrics extracted from directive lists. -/
structure BudgetMetrics where
  totalInsns : Nat := 0
  bodyInsns  : Nat := 0
  spills     : Nat := 0
  regMoves   : Nat := 0
  boolChains : Nat := 0
  selectOps  : Nat := 0
  cmpsTests  : Nat := 0
  branches   : Nat := 0
  jmps       : Nat := 0
  leas       : Nat := 0
  calls      : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-! ## Shared Untrusted Snippet AST Lifting (`NOp`, `NExpr`, `lowerNExprGen`) -/

/-- Named-variable operation representation emitted during untrusted assembly lifting before
PHOAS / de Bruijn `TFlat` resolution. -/
inductive NOp where
  | copy (w : Nat) (x : Nat)
  | movi (w : Nat) (c : BitVec 64)
  | bin (w : Nat) (op : String) (a : Nat) (b : Option Nat) (imm : Option (BitVec 64))
  | un (w : Nat) (op : String) (a : Nat)
  | zext (m n : Nat) (x : Nat)
  | sext (m n : Nat) (x : Nat)
  | trunc (m n : Nat) (x : Nat)
  | cmp (co : CmpOp) (w : Nat) (a : Nat) (b : Option Nat) (imm : Option (BitVec 64))
  | select (w : Nat) (cond : Nat) (a : Nat) (b : Nat)
  | ofBool (w : Nat) (cond : Nat)
  | load (w : Nat) (addr : Nat)
  | store (w : Nat) (v : Nat) (addr : Nat)
  | addc (w : Nat) (a : Nat) (b : Option Nat) (imm : Option (BitVec 64))
      (cin? : Option Nat) (cinImm : Bool)
  | umulw (w : Nat) (a b : Nat)
  deriving Repr

/-- Named-variable expression tree produced by assembly frontends prior to `lowerNExprGen`. -/
inductive NExpr where
  | let1 (id : Nat) (ty : Ty) (op : NOp) (k : NExpr)
  | let2 (id1 id2 : Nat) (t1 t2 : Ty) (op : NOp) (k : NExpr)
  | jnz (condId : Nat) (t e : NExpr)
  | jump (blkIdx : Nat) (args : List Nat)
  | ret (vs : List Nat)
  | group (blocks : List (Nat × List (Nat × Ty) × NExpr)) (entry : NExpr)
  deriving Repr

/-- Single lifted statement (`let1` or multi-result `let2`) prepended onto a continuation. -/
inductive LiftedStmt where
  | def1 (id : Nat) (ty : Ty) (op : NOp)
  | def2 (id1 id2 : Nat) (t1 t2 : Ty) (op : NOp)
  deriving Repr

/-- Wrap a list of `LiftedStmt`s around terminator `term`. -/
def wrapStmts (stmts : List LiftedStmt) (term : NExpr) : NExpr :=
  stmts.foldr (fun s acc =>
    match s with
    | .def1 id ty op => .let1 id ty op acc
    | .def2 id1 id2 t1 t2 op => .let2 id1 id2 t1 t2 op acc) term

/-- Output bundle of `lowerNExprGen` mapping lifted AST + IP-indexed hint metadata. -/
structure LowerNRes (rs : List Ty) where
  tflat  : TFlat rs
  nv     : Nat
  nl     : Nat
  ip     : Nat
  vhs    : List (Nat × VariantHint)
  elides : List (Nat × Bool)
  vmap   : List (Nat × Nat)

/-- Target-generic bundle returned by `liftSnippet` (`Amd64.Snippet` / `Arm64.Snippet`). -/
structure LiftedSnippet (Reg Cond : Type) (rs : List Ty) where
  name         : Sym
  as           : List Ty
  tflat        : TFlat rs
  relHints     : SpillSnippet.RelHints Reg Cond
  ipHintMap    : List (Nat × VariantHint) := []
  ipElideMap   : List (Nat × Bool) := []
  varToSoftReg : List (Nat × Reg) := []

/-- Convert a `LiftedSnippet` into a verified-pipeline-ready `Fn` (`denoteFunc lifted.tflat`). -/
def LiftedSnippet.toFn {Reg Cond : Type} {rs : List Ty}
    (l : LiftedSnippet Reg Cond rs) : Fn :=
  ⟨l.name, l.as, rs, denoteFunc l.tflat⟩

def mkArgTup (env : List (Nat × Ty)) :
    (ts : List Ty) → List Nat → Except String (Tup (Arg K) ts)
  | [], [] => pure ()
  | t :: ts, a :: args => do
    let idx ← match env.findIdx? (fun p => p.1 == a) with
      | some i =>
        if env[i]!.2 == t then pure i
        else throw s!"jump_arg_type_mismatch {a}: {repr env[i]!.2} != {repr t}"
      | none => throw s!"unbound_jump_arg {a}"
    let rest ← mkArgTup env ts args
    pure (.var idx, rest)
  | _, _ => throw "jump_arity_mismatch"

def shiftArg {t : Ty} (k : Nat) : Arg K t → Arg K t
  | .var i => .var (i + k)
  | .imm c => .imm c

def resolveBitsAt (rs : List Ty) (w x nv ip : Nat) (env : List (Nat × Ty)) :
    Except String (Arg K (.bits w) × (TFlat rs → TFlat rs) × List (Nat × Ty) × Nat × Nat) :=
  match env.findIdx? (fun p => p.1 == x) with
  | none => throw s!"unbound_var {x}"
  | some idx =>
    let tx := env[idx]!.2
    if tx == .bits w then
      pure (.var idx, _root_.id, env, nv, ip)
    else
      match tx with
      | .bits m =>
        if w < m then
          let wrap := fun (cont : TFlat rs) => TFlat.let_ ⟨.trunc m w, (.var idx, ())⟩ cont
          pure (.var 0, wrap, (x, .bits w) :: env, nv + 1, ip + 1)
        else
          let wrap := fun (cont : TFlat rs) => TFlat.let_ ⟨.zext m w, (.var idx, ())⟩ cont
          pure (.var 0, wrap, (x, .bits w) :: env, nv + 1, ip + 1)
      | _ => throw s!"type_mismatch {x}: {repr tx} vs .bits {w}"

def resolveBitsOptAt (rs : List Ty) (w nv ip : Nat) (env : List (Nat × Ty))
    (b? : Option Nat) (imm? : Option (BitVec 64)) :
    Except String (Arg K (.bits w) × (TFlat rs → TFlat rs) × List (Nat × Ty) × Nat × Nat) :=
  match b?, imm? with
  | some b, none => resolveBitsAt rs w b nv ip env
  | none, some c => pure (.imm (c.setWidth w), _root_.id, env, nv, ip)
  | _, _ => throw "bad_opt_rhs_args"

def coerceArgList (ts : List Ty) (idx : Nat) (args : List Nat) (env : List (Nat × Ty))
    (nv : Nat) : List LiftedStmt × List Nat :=
  match args with
  | [] => ([], [])
  | v :: rest =>
    let freshId := nv + 100000 + idx
    match ts[idx]?, env.find? (·.1 == v) with
    | some .bool, some (_, .bits w) =>
      let st := LiftedStmt.def1 freshId .bool (.cmp .ne w v none (some 0#64))
      let (stsR, vsR) := coerceArgList ts (idx + 1) rest ((freshId, .bool) :: env) nv
      (st :: stsR, freshId :: vsR)
    | some (.bits wt), some (_, .bool) =>
      let st := LiftedStmt.def1 freshId (.bits wt) (.ofBool wt v)
      let (stsR, vsR) := coerceArgList ts (idx + 1) rest ((freshId, .bits wt) :: env) nv
      (st :: stsR, freshId :: vsR)
    | some (.bits wt), some (_, .bits wa) =>
      if wt == wa then
        let (stsR, vsR) := coerceArgList ts (idx + 1) rest env nv
        (stsR, v :: vsR)
      else
        let st := if wt < wa then LiftedStmt.def1 freshId (.bits wt) (.trunc wa wt v)
                  else LiftedStmt.def1 freshId (.bits wt) (.zext wa wt v)
        let (stsR, vsR) := coerceArgList ts (idx + 1) rest ((freshId, .bits wt) :: env) nv
        (st :: stsR, freshId :: vsR)
    | _, _ =>
      let (stsR, vsR) := coerceArgList ts (idx + 1) rest env nv
      (stsR, v :: vsR)

/-- Lower a named-variable `NExpr` directly into `TFlat rs` (`Env.head`-first de Bruijn indices),
retaining variable-to-index `vmap` and IP-keyed `VariantHint` / `elide` tables. -/
partial def lowerNExprGen (rs : List Ty) (env : List (Nat × Ty)) (lenv : List (Nat × List Ty))
    (nv nl ip : Nat) (variants : List (Nat × VariantHint)) (elideVars : List Nat) :
    NExpr → Except String (LowerNRes rs)
  | .let1 id ty op k => do
    let resolveBits (w x : Nat) := resolveBitsAt rs w x nv ip env
    let vargExact (t : Ty) (x : Nat) : Except String (Arg K t) :=
      match env.findIdx? (fun p => p.1 == x) with
      | some idx =>
        if env[idx]!.2 == t then pure (.var idx)
        else throw s!"type_mismatch {x}: expected {repr t}, got {repr env[idx]!.2}"
      | none => throw s!"unbound_var {x}"
    let mk1 (outTy : Ty) {ts : List Ty} (wrap : TFlat rs → TFlat rs) (env' : List (Nat × Ty))
        (nv' ip' : Nat) (code : OpCode ts [outTy]) (args : Tup (Arg K) ts) := do
      let res ← lowerNExprGen rs ((id, outTy) :: env') lenv (nv' + 1) nl (ip' + 1)
        variants elideVars k
      let vhs' := match variants.find? (·.1 == id) with
        | some (_, vh) => (ip', vh) :: res.vhs
        | none => res.vhs
      let elides' := if elideVars.contains id then (ip', true) :: res.elides else res.elides
      pure { res with tflat := wrap (TFlat.let_ ⟨code, args⟩ res.tflat),
                      vhs := vhs', elides := elides', vmap := (id, nv') :: res.vmap }
    match ty, op with
    | .bits w, .copy _ x =>
      let (ax, wrap, env', nv', ip') ← resolveBits w x
      mk1 (.bits w) wrap env' nv' ip' (.copy (.bits w)) (ax, ())
    | .bits w, .movi _ c =>
      mk1 (.bits w) _root_.id env nv ip (.copy (.bits w)) (Arg.imm (c.setWidth w), ())
    | .bits w, .bin _ nm a b? imm? =>
      let (aa, wrapA, env1, nv1, ip1) ← resolveBits w a
      let (ab, wrapB, env2, nv2, ip2) ← resolveBitsOptAt rs w nv1 ip1 env1 b? imm?
      let aa' := shiftArg (nv2 - nv1) aa
      let wrap := fun x => wrapA (wrapB x)
      match nm with
      | "add" => mk1 (.bits w) wrap env2 nv2 ip2 (.add (.bits w)) (aa', ab, ())
      | "sub" => mk1 (.bits w) wrap env2 nv2 ip2 (.sub (.bits w)) (aa', ab, ())
      | "mul" => mk1 (.bits w) wrap env2 nv2 ip2 (.mul (.bits w)) (aa', ab, ())
      | "and" => mk1 (.bits w) wrap env2 nv2 ip2 (.and (.bits w)) (aa', ab, ())
      | "or"  => mk1 (.bits w) wrap env2 nv2 ip2 (.or (.bits w)) (aa', ab, ())
      | "xor" => mk1 (.bits w) wrap env2 nv2 ip2 (.xor (.bits w)) (aa', ab, ())
      | "shl" => mk1 (.bits w) wrap env2 nv2 ip2 (.shl (.bits w)) (aa', ab, ())
      | "lshr" => mk1 (.bits w) wrap env2 nv2 ip2 (.lshr (.bits w)) (aa', ab, ())
      | "ashr" => mk1 (.bits w) wrap env2 nv2 ip2 (.ashr (.bits w)) (aa', ab, ())
      | "udiv" => mk1 (.bits w) wrap env2 nv2 ip2 (.udiv w) (aa', ab, ())
      | "sdiv" => mk1 (.bits w) wrap env2 nv2 ip2 (.sdiv w) (aa', ab, ())
      | _ => throw s!"bad_bin_op {nm}"
    | .bits w, .un _ nm a =>
      let (aa, wrap, env', nv', ip') ← resolveBits w a
      match nm with
      | "neg" => mk1 (.bits w) wrap env' nv' ip' (.neg (.bits w)) (aa, ())
      | "not" => mk1 (.bits w) wrap env' nv' ip' (.not (.bits w)) (aa, ())
      | _ => throw s!"bad_un_op {nm}"
    | .bits n, .zext m _ x =>
      let (ax, wrap, env', nv', ip') ← resolveBits m x
      mk1 (.bits n) wrap env' nv' ip' (.zext m n) (ax, ())
    | .bits n, .sext m _ x =>
      let (ax, wrap, env', nv', ip') ← resolveBits m x
      mk1 (.bits n) wrap env' nv' ip' (.sext m n) (ax, ())
    | .bits n, .trunc m _ x =>
      let (ax, wrap, env', nv', ip') ← resolveBits m x
      mk1 (.bits n) wrap env' nv' ip' (.trunc m n) (ax, ())
    | .bool, .cmp co w a b? imm? =>
      let (aa, wrapA, env1, nv1, ip1) ← resolveBits w a
      let (ab, wrapB, env2, nv2, ip2) ← resolveBitsOptAt rs w nv1 ip1 env1 b? imm?
      let aa' := shiftArg (nv2 - nv1) aa
      mk1 .bool (fun x => wrapA (wrapB x)) env2 nv2 ip2 (.cmp co (.bits w)) (aa', ab, ())
    | .bits w, .select _ cond a b =>
      let ac ← vargExact .bool cond
      let (aa, wrapA, env1, nv1, ip1) ← resolveBits w a
      let (ab, wrapB, env2, nv2, ip2) ← resolveBitsAt rs w b nv1 ip1 env1
      let ac' := shiftArg (nv2 - nv) ac
      let aa' := shiftArg (nv2 - nv1) aa
      mk1 (.bits w) (fun x => wrapA (wrapB x)) env2 nv2 ip2 (.select (.bits w)) (ac', aa', ab, ())
    | .bits w, .ofBool _ cond =>
      let ac ← vargExact .bool cond
      mk1 (.bits w) _root_.id env nv ip (.ofBool w) (ac, ())
    | .bits w, .load _ addr =>
      let (aa, wrap, env', nv', ip') ← resolveBits 64 addr
      let res ← lowerNExprGen rs ((id, .bits w) :: env') lenv (nv' + 1) nl (ip' + 1)
        variants elideVars k
      pure { res with tflat := wrap (TFlat.load (.bits w) aa res.tflat),
                      vmap := (id, nv') :: res.vmap }
    | .bits w, .store _ v addr =>
      let (av, wrapA, env1, nv1, ip1) ← resolveBits w v
      let (aa, wrapB, env2, nv2, ip2) ← resolveBitsAt rs 64 addr nv1 ip1 env1
      let av' := shiftArg (nv2 - nv1) av
      let res ← lowerNExprGen rs env2 lenv nv2 nl (ip2 + 1) variants elideVars k
      pure { res with tflat := wrapA (wrapB (TFlat.store av' aa res.tflat)) }
    | _, _ => throw s!"unsupported_let1 {repr ty} {repr op}"
  | .let2 id1 id2 t1 t2 op k => do
    match t1, t2, op with
    | .bits w, .bool, .addc _ a b? imm? cin? cinImm =>
      let aa ← match env.findIdx? (·.1 == a) with
        | some i => pure (Arg.var i : Arg K (.bits w))
        | none => throw s!"unbound {a}"
      let ab : Arg K (.bits w) ← match b?, imm? with
        | some b, none => match env.findIdx? (·.1 == b) with
          | some i => pure (Arg.var i) | none => throw s!"unbound {b}"
        | none, some c => pure (Arg.imm (c.setWidth w))
        | _, _ => throw "bad addc"
      let ac : Arg K .bool ← match cin? with
        | some c => match env.findIdx? (·.1 == c) with
          | some i => pure (Arg.var i) | none => throw s!"unbound {c}"
        | none => pure (Arg.imm cinImm)
      let env' := (id2, .bool) :: (id1, .bits w) :: env
      let res ← lowerNExprGen rs env' lenv (nv + 2) nl (ip + 1) variants elideVars k
      let vhs' := match variants.find? (·.1 == id1) with
        | some (_, vh) => (ip, vh) :: res.vhs
        | none => res.vhs
      pure { res with tflat := TFlat.let_ ⟨.addc w, (aa, ab, ac, ())⟩ res.tflat,
                      vhs := vhs', vmap := (id1, nv) :: (id2, nv + 1) :: res.vmap }
    | .bits w, .bits _, .umulw _ a b =>
      let (aa, wrapA, env1, nv1, ip1) ← resolveBitsAt rs w a nv ip env
      let (ab, wrapB, env2, nv2, ip2) ← resolveBitsAt rs w b nv1 ip1 env1
      let aa' := shiftArg (nv2 - nv1) aa
      let env' := (id2, .bits w) :: (id1, .bits w) :: env2
      let res ← lowerNExprGen rs env' lenv (nv2 + 2) nl (ip2 + 1) variants elideVars k
      pure { res with tflat := wrapA (wrapB (TFlat.let_ ⟨.umulw w, (aa', ab, ())⟩ res.tflat)),
                      vmap := (id1, nv2) :: (id2, nv2 + 1) :: res.vmap }
    | _, _, _ => throw "unsupported_let2"
  | .jnz c t e => do
    let ac : Arg K .bool ← match env.findIdx? (·.1 == c) with
      | some i => pure (.var i) | none => throw s!"unbound {c}"
    let rE ← lowerNExprGen rs env lenv nv (nl + 1) (ip + 1) variants elideVars e
    let rT ← lowerNExprGen rs env lenv rE.nv rE.nl rE.ip variants elideVars t
    pure { tflat := .jnz ac rT.tflat rE.tflat, nv := rT.nv, nl := rT.nl, ip := rT.ip,
           vhs := rE.vhs ++ rT.vhs, elides := rE.elides ++ rT.elides, vmap := rE.vmap ++ rT.vmap }
  | .jump blkIdx args => do
    let lidx ← match lenv.findIdx? (·.1 == blkIdx) with
      | some i => pure i | none => throw s!"unbound_blk {blkIdx}"
    let ts := lenv[lidx]!.2
    let (cStmts, args') := coerceArgList ts 0 args env nv
    if cStmts.isEmpty then
      let tup ← mkArgTup env ts args
      pure { tflat := .jump (ts := ts) lidx tup, nv := nv, nl := nl, ip := ip + 1,
             vhs := [], elides := [], vmap := [] }
    else
      let kExpr := wrapStmts cStmts (NExpr.jump blkIdx args')
      lowerNExprGen rs env lenv nv nl ip variants elideVars kExpr
  | .ret vs => do
    let (cStmts, vs') := coerceArgList rs 0 vs env nv
    if cStmts.isEmpty then
      let tup ← mkArgTup env rs vs
      pure { tflat := .ret tup, nv := nv, nl := nl, ip := ip + 1,
             vhs := [], elides := [], vmap := [] }
    else
      let kExpr := wrapStmts cStmts (NExpr.ret vs')
      lowerNExprGen rs env lenv nv nl ip variants elideVars kExpr
  | .group blocks entry => do
    let lenv' := blocks.foldl (fun acc (bidx, ps, _) => (bidx, ps.map Prod.snd) :: acc) lenv
    let nl' := nl + blocks.length
    let rK ← lowerNExprGen rs env lenv' nv nl' ip variants elideVars entry
    let rec lowerBs (bs : List (Nat × List (Nat × Ty) × NExpr)) (nvAcc nlAcc ipAcc : Nat) :
        Except String ((sig : List (List Ty)) × TBlocks rs sig × Nat × Nat × Nat ×
                       List (Nat × VariantHint) × List (Nat × Bool) × List (Nat × Nat)) :=
      match bs with
      | [] => pure ⟨[], .nil, nvAcc, nlAcc, ipAcc, [], [], []⟩
      | (_, ps, body) :: rest => do
        let envB := ps.foldl (fun acc (pid, pt) => (pid, pt) :: acc) env
        let pmap := (List.range ps.length).map fun i => (ps[i]!.1, nvAcc + i)
        let rB ← lowerNExprGen rs envB lenv' (nvAcc + ps.length) nlAcc ipAcc
          variants elideVars body
        let ⟨sigR, tbs, nv'', nl'', ip'', vhR, elR, vmR⟩ ← lowerBs rest rB.nv rB.nl rB.ip
        pure ⟨(ps.map Prod.snd) :: sigR, .cons rB.tflat tbs, nv'', nl'', ip'',
              rB.vhs ++ vhR, rB.elides ++ elR, pmap ++ rB.vmap ++ vmR⟩
    let ⟨sig, tbs, nv2, nl2, ip2, vhBs, elBs, vmBs⟩ ← lowerBs blocks rK.nv rK.nl rK.ip
    pure { tflat := .group (sig := sig) tbs rK.tflat, nv := nv2, nl := nl2, ip := ip2,
           vhs := rK.vhs ++ vhBs, elides := rK.elides ++ elBs, vmap := rK.vmap ++ vmBs }

end SnippetCheck

end LeanQbe.T
