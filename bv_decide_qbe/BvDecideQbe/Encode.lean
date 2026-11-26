module

public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
public import Std.Data.HashMap

/-!
# Untrusted DAG-Sharing `BVP1` Encoder and Upfront Workspace Sizing (`S3a`)

Encodes `Std.Tactic.BVDecide.BVLogicalExpr` into:
- `words : List Nat` (matching `Bitblast.Ref.BVProg.parseWords` 1:1 on all 32 opcodes)
- `bytes : ByteArray` (canonical little-endian 32-bit word stream)
- `varTable : Array (Nat × Nat)` (`(bvIdx, width)` per variable slot)
- `atomBase : Array Nat` (`atomBase[0] = 1`, `atomBase[k+1] = atomBase[k] + varTable[k].2`)
- `stats : ProgStats` + deterministic `estimateWorkSize` clamped to `[256 KiB, 512 MiB]`.
-/

set_option autoImplicit false

public section

namespace BvDecideQbe

open Std.Tactic.BVDecide

/-- `BVP1` magic word (`"BVP1"` little-endian = `0x31505642`). -/
def bvpMagic : Nat := 0x31505642
/-- `BVP1` format version (`1`). -/
def bvpVersion : Nat := 1
/-- Exclusive upper bound on 32-bit unsigned words (`2^32`). -/
def u32Bound : Nat := 4294967296

/-- `BVP1` opcode tags matching `LeanQbe.T.Examples.Bitblast.Ref.BVProg`. -/
def opVar : Nat := 0
def opConst : Nat := 1
def opExtract : Nat := 2
def opAnd : Nat := 3
def opOr : Nat := 4
def opXor : Nat := 5
def opAdd : Nat := 6
def opMul : Nat := 7
def opUdiv : Nat := 8
def opUmod : Nat := 9
def opNot : Nat := 10
def opRotL : Nat := 11
def opRotR : Nat := 12
def opAshrC : Nat := 13
def opReverse : Nat := 14
def opClz : Nat := 15
def opCpop : Nat := 16
def opAppend : Nat := 17
def opReplicate : Nat := 18
def opShl : Nat := 19
def opUshr : Nat := 20
def opAshr : Nat := 21
def opEq : Nat := 22
def opUlt : Nat := 23
def opGetLsbD : Nat := 24
def opBConst : Nat := 25
def opBNot : Nat := 26
def opGateAnd : Nat := 27
def opGateXor : Nat := 28
def opGateBeq : Nat := 29
def opGateOr : Nat := 30
def opIte : Nat := 31

@[inline] private def isU32 (x : Nat) : Bool :=
  Nat.blt x u32Bound

private def binOpEq : BVBinOp → BVBinOp → Bool
  | .and, .and | .or, .or | .xor, .xor | .add, .add
  | .mul, .mul | .udiv, .udiv | .umod, .umod => true
  | _, _ => false

private def unOpEq : BVUnOp → BVUnOp → Bool
  | .not, .not | .reverse, .reverse | .clz, .clz | .cpop, .cpop => true
  | .rotateLeft a, .rotateLeft b => a == b
  | .rotateRight a, .rotateRight b => a == b
  | .arithShiftRightConst a, .arithShiftRightConst b => a == b
  | _, _ => false

private def bvExprHEq : {w1 w2 : Nat} → BVExpr w1 → BVExpr w2 → Bool
  | w1, w2, .var i1, .var i2 => w1 == w2 && i1 == i2
  | w1, w2, .const v1, .const v2 => w1 == w2 && v1.toNat == v2.toNat
  | w1, w2, .extract s1 _ e1, .extract s2 _ e2 => w1 == w2 && s1 == s2 && bvExprHEq e1 e2
  | w1, w2, .bin l1 op1 r1, .bin l2 op2 r2 =>
    w1 == w2 && binOpEq op1 op2 && bvExprHEq l1 l2 && bvExprHEq r1 r2
  | w1, w2, .un op1 e1, .un op2 e2 => w1 == w2 && unOpEq op1 op2 && bvExprHEq e1 e2
  | w1, w2, .append l1 r1 _, .append l2 r2 _ => w1 == w2 && bvExprHEq l1 l2 && bvExprHEq r1 r2
  | w1, w2, .replicate n1 e1 _, .replicate n2 e2 _ => w1 == w2 && n1 == n2 && bvExprHEq e1 e2
  | w1, w2, .shiftLeft l1 r1, .shiftLeft l2 r2 => w1 == w2 && bvExprHEq l1 l2 && bvExprHEq r1 r2
  | w1, w2, .shiftRight l1 r1, .shiftRight l2 r2 => w1 == w2 && bvExprHEq l1 l2 && bvExprHEq r1 r2
  | w1, w2, .arithShiftRight l1 r1, .arithShiftRight l2 r2 =>
    w1 == w2 && bvExprHEq l1 l2 && bvExprHEq r1 r2
  | _, _, _, _ => false

private def bvPredEq : BVPred → BVPred → Bool
  | .bin l1 .eq r1, .bin l2 .eq r2 => bvExprHEq l1 l2 && bvExprHEq r1 r2
  | .bin l1 .ult r1, .bin l2 .ult r2 => bvExprHEq l1 l2 && bvExprHEq r1 r2
  | .getLsbD e1 i1, .getLsbD e2 i2 => i1 == i2 && bvExprHEq e1 e2
  | _, _ => false

private def gateEq : Gate → Gate → Bool
  | .and, .and | .xor, .xor | .beq, .beq | .or, .or => true
  | _, _ => false

private def logicalExprEq : BVLogicalExpr → BVLogicalExpr → Bool
  | .literal p1, .literal p2 => bvPredEq p1 p2
  | .const b1, .const b2 => b1 == b2
  | .not x1, .not x2 => logicalExprEq x1 x2
  | .gate g1 l1 r1, .gate g2 l2 r2 => gateEq g1 g2 && logicalExprEq l1 l2 && logicalExprEq r1 r2
  | .ite d1 l1 r1, .ite d2 l2 r2 =>
    logicalExprEq d1 d2 && logicalExprEq l1 l2 && logicalExprEq r1 r2
  | _, _ => false

/-- Minimum upfront scratch workspace (`256 KiB`). -/
def minWorkBytes : Nat := 256 * 1024

/-- Maximum upfront scratch workspace (`512 MiB`). -/
def maxWorkBytes : Nat := 512 * 1024 * 1024

/-- Encoded `BVP1` statistics used for deterministic upfront workspace sizing. -/
structure ProgStats where
  nVars : Nat
  nNodes : Nat
  nCwords : Nat
  totalAtomBits : Nat
  estAigGates : Nat
  estClauses : Nat
  maxWidth : Nat
  deriving Repr, BEq, Inhabited

/-- Result of encoding a `BVLogicalExpr` into the `BVP1` wire format. -/
structure EncodedProg where
  words : List Nat
  bytes : ByteArray
  varTable : Array (Nat × Nat)
  atomBase : Array Nat
  stats : ProgStats
  deriving Inhabited

instance : BEq EncodedProg where
  beq a b :=
    a.words == b.words &&
    a.bytes.data == b.bytes.data &&
    a.varTable == b.varTable &&
    a.atomBase == b.atomBase &&
    a.stats == b.stats

/-- Append one 32-bit `Nat` word in little-endian byte order onto a `ByteArray`. -/
@[inline] def pushWordLE (ba : ByteArray) (w : Nat) : ByteArray :=
  let b0 := (w % 256).toUInt8
  let b1 := ((w / 256) % 256).toUInt8
  let b2 := ((w / 65536) % 256).toUInt8
  let b3 := ((w / 16777216) % 256).toUInt8
  (((ba.push b0).push b1).push b2).push b3

/-- Pack a list of 32-bit `Nat` words into a little-endian `ByteArray`. -/
def wordsToByteArrayLE (ws : List Nat) : ByteArray :=
  ws.foldl pushWordLE (ByteArray.emptyWithCapacity (ws.length * 4))

private def log2Ceil (w : Nat) : Nat :=
  if w <= 1 then 1 else Nat.log2 (w - 1) + 1

private def nextPow2 (n : Nat) : Nat :=
  if n <= 1 then 1 else 1 <<< (Nat.log2 (n - 1) + 1)

/-- Estimated AIG gate count for one unique `BVP1` node. -/
def opAigEstimate (op w argWidth : Nat) : Nat :=
  if op == opAdd || op == opEq || op == opUlt then
    6 * argWidth
  else if op == opShl || op == opUshr || op == opAshr then
    4 * w * log2Ceil w
  else if op == opMul || op == opUdiv || op == opUmod then
    4 * w * w
  else if op == opCpop then
    2 * w * w
  else if op == opXor || op == opGateXor || op == opGateBeq || op == opIte then
    3 * w
  else if op == opAnd || op == opOr || op == opGateAnd || op == opGateOr then
    w
  else if op == opClz then
    3 * w
  else
    0

/-- Deterministic upfront workspace-sizing formula (in `Nat` bytes, clamped to `[256 KiB, 512 MiB]`).
Combines estimated bitblaster AIG/HT/lit/DIMACS space, Kissat fixed per-variable state, and
clause arena headroom (`4 * est_clauses * 48`), rounded up to a power of two. -/
def estimateWorkBytesNat (stats : ProgStats) : Nat :=
  let estAig := stats.totalAtomBits + stats.estAigGates + 1
  let estClauses := stats.estClauses
  let htSlots := max 1024 (nextPow2 (2 * estAig))
  let bitblastBytes :=
    128 +
    8 * estAig +
    4 * htSlots +
    4 * stats.nNodes +
    4 * (stats.totalAtomBits + stats.estAigGates + 8 * stats.maxWidth) +
    32 * estClauses
  let maxVarsEst := estAig + min (estAig / 2 + 16) 4096
  let kissatFixed := 4096 + 160 * maxVarsEst
  let kissatClauseHeadroom := 4 * estClauses * 48
  let rawBytes := bitblastBytes + kissatFixed + kissatClauseHeadroom
  min maxWorkBytes (max minWorkBytes (nextPow2 rawBytes))

/-- Deterministic upfront workspace size in `UInt64` bytes, clamped to `[256 KiB, 512 MiB]`. -/
def estimateWorkSize (stats : ProgStats) : UInt64 :=
  (estimateWorkBytesNat stats).toUInt64

/-- Upfront workspace size estimate for an already-encoded `BVP1` program. -/
def EncodedProg.estimateWorkSize (p : EncodedProg) : UInt64 :=
  BvDecideQbe.estimateWorkSize p.stats

private structure BVKey where
  w : Nat
  expr : BVExpr w

private instance : BEq BVKey where
  beq a b := bvExprHEq a.expr b.expr

private instance : Hashable BVKey where
  hash a := a.expr.hashCode a.w

private structure LogicalKey where
  expr : BVLogicalExpr

private instance : BEq LogicalKey where
  beq a b := logicalExprEq a.expr b.expr

private instance : Hashable LogicalKey where
  hash a := a.expr.hashCode

private structure EncodeState where
  vars : Array (Nat × Nat) := #[]
  atomBase : Array Nat := #[]
  varMap : Std.HashMap (Nat × Nat) Nat := {}
  totalAtomBits : Nat := 0
  cwords : Array Nat := #[]
  nodes : Array (Nat × Nat × Nat × Nat × Nat) := #[]
  estAigGates : Nat := 0
  maxWidth : Nat := 0
  bvMap : Std.HashMap BVKey Nat := {}
  logMap : Std.HashMap LogicalKey Nat := {}

private def pushConstWords (cw : Array Nat) (val nw : Nat) : Array Nat :=
  Id.run do
    let mut out := cw
    let mut v := val
    for _ in [0:nw] do
      out := out.push (v % u32Bound)
      v := v / u32Bound
    return out

private def emitNode (st : EncodeState) (op w a b c : Nat) (argWidth : Nat := w) :
    Option (Nat × EncodeState) :=
  if isU32 op && isU32 w && isU32 a && isU32 b && isU32 c then
    let idx := st.nodes.size
    if isU32 idx then
      some (idx, { st with
        nodes := st.nodes.push (op, w, a, b, c)
        estAigGates := st.estAigGates + opAigEstimate op w argWidth
        maxWidth := max st.maxWidth argWidth })
    else none
  else none

private def getOrAddVar (st : EncodeState) (bvIdx w : Nat) : Option (Nat × EncodeState) :=
  if !(isU32 bvIdx && isU32 w) then none
  else
    match st.varMap.get? (bvIdx, w) with
    | some slot => some (slot, st)
    | none =>
      let slot := st.vars.size
      if isU32 slot then
        let base := 1 + st.totalAtomBits
        some (slot, { st with
          vars := st.vars.push (bvIdx, w)
          atomBase := st.atomBase.push base
          varMap := st.varMap.insert (bvIdx, w) slot
          totalAtomBits := st.totalAtomBits + w
          maxWidth := max st.maxWidth w })
      else none

private def binOpTag : BVBinOp → Nat
  | .and => opAnd | .or => opOr | .xor => opXor | .add => opAdd
  | .mul => opMul | .udiv => opUdiv | .umod => opUmod

private def unOpTagAndArg : BVUnOp → Nat × Nat
  | .not => (opNot, 0)
  | .rotateLeft n => (opRotL, n)
  | .rotateRight n => (opRotR, n)
  | .arithShiftRightConst n => (opAshrC, n)
  | .reverse => (opReverse, 0)
  | .clz => (opClz, 0)
  | .cpop => (opCpop, 0)

private def gateTag : Gate → Nat
  | .and => opGateAnd | .xor => opGateXor | .beq => opGateBeq | .or => opGateOr

private def encodeBVExprAux (st : EncodeState) : {w : Nat} → BVExpr w →
    Option (Nat × EncodeState)
  | w, .var idx => do
    let (slot, st1) ← getOrAddVar st idx w
    emitNode st1 opVar w slot 0 0
  | w, .const val =>
    let nw := (w + 31) / 32
    let off := st.cwords.size
    let cw' := pushConstWords st.cwords val.toNat nw
    if isU32 cw'.size then
      emitNode { st with cwords := cw' } opConst w off 0 0
    else none
  | _, .extract start len inner => do
    let (b, st1) ← encodeBVExpr st inner
    emitNode st1 opExtract len start b 0
  | w, .bin lhs bop rhs => do
    let (a, st1) ← encodeBVExpr st lhs
    let (b, st2) ← encodeBVExpr st1 rhs
    emitNode st2 (binOpTag bop) w a b 0
  | w, .un uop inner => do
    let (a, st1) ← encodeBVExpr st inner
    let (tag, arg) := unOpTagAndArg uop
    emitNode st1 tag w a arg 0
  | w, .append lhs rhs _ => do
    let (a, st1) ← encodeBVExpr st lhs
    let (b, st2) ← encodeBVExpr st1 rhs
    emitNode st2 opAppend w a b 0
  | w, .replicate n inner _ => do
    let (a, st1) ← encodeBVExpr st inner
    emitNode st1 opReplicate w a n 0
  | w, .shiftLeft lhs rhs => do
    let (a, st1) ← encodeBVExpr st lhs
    let (b, st2) ← encodeBVExpr st1 rhs
    emitNode st2 opShl w a b 0
  | w, .shiftRight lhs rhs => do
    let (a, st1) ← encodeBVExpr st lhs
    let (b, st2) ← encodeBVExpr st1 rhs
    emitNode st2 opUshr w a b 0
  | w, .arithShiftRight lhs rhs => do
    let (a, st1) ← encodeBVExpr st lhs
    let (b, st2) ← encodeBVExpr st1 rhs
    emitNode st2 opAshr w a b 0
where
  encodeBVExpr (st : EncodeState) {w : Nat} (e : BVExpr w) :
      Option (Nat × EncodeState) := do
    let key : BVKey := ⟨w, e⟩
    if let some idx := st.bvMap.get? key then
      return (idx, st)
    let (idx, st') ← encodeBVExprAux st e
    return (idx, { st' with bvMap := st'.bvMap.insert key idx })

private def encodeBVLogical (st : EncodeState) (e : BVLogicalExpr) :
    Option (Nat × EncodeState) := do
  let key : LogicalKey := ⟨e⟩
  if let some idx := st.logMap.get? key then
    return (idx, st)
  let (idx, st') ← match e with
    | .literal (.bin (w := argW) lhs pred rhs) =>
      let (a, st1) ← encodeBVExprAux.encodeBVExpr st lhs
      let (b, st2) ← encodeBVExprAux.encodeBVExpr st1 rhs
      let tag := match pred with | .eq => opEq | .ult => opUlt
      emitNode st2 tag 1 a b 0 argW
    | .literal (.getLsbD inner bit) =>
      let (a, st1) ← encodeBVExprAux.encodeBVExpr st inner
      emitNode st1 opGetLsbD 1 a bit 0
    | .const b =>
      emitNode st opBConst 1 (if b then 1 else 0) 0 0
    | .not x =>
      let (a, st1) ← encodeBVLogical st x
      emitNode st1 opBNot 1 a 0 0
    | .gate g x y =>
      let (a, st1) ← encodeBVLogical st x
      let (b, st2) ← encodeBVLogical st1 y
      emitNode st2 (gateTag g) 1 a b 0
    | .ite d l r =>
      let (a, st1) ← encodeBVLogical st d
      let (b, st2) ← encodeBVLogical st1 l
      let (c, st3) ← encodeBVLogical st2 r
      emitNode st3 opIte 1 a b c
  return (idx, { st' with logMap := st'.logMap.insert key idx })

/-- Untrusted DAG-sharing `BVLogicalExpr` encoder producing `BVP1` words, packed LE bytes,
variable table, `atomBase` offsets, and sizing stats. Returns `none` if any parameter or pool
count reaches `2^32`. -/
def encode (e : BVLogicalExpr) : Option EncodedProg := do
  let (root, st) ← encodeBVLogical {} e
  let nVars := st.vars.size
  let nNodes := st.nodes.size
  let nCwords := st.cwords.size
  if !(isU32 nVars && isU32 nNodes && isU32 nCwords && isU32 root && 0 < nNodes) then
    none
  let totalWords := 8 + 2 * nVars + nCwords + 5 * nNodes
  let mut ws : Array Nat := Array.emptyWithCapacity totalWords
  ws := ws.push bvpMagic
  ws := ws.push bvpVersion
  ws := ws.push nVars
  ws := ws.push nNodes
  ws := ws.push nCwords
  ws := ws.push root
  ws := ws.push 0
  ws := ws.push 0
  for (bvIdx, w) in st.vars do
    ws := ws.push bvIdx
    ws := ws.push w
  for cw in st.cwords do
    ws := ws.push cw
  for (op, w, a, b, c) in st.nodes do
    ws := ws.push op
    ws := ws.push w
    ws := ws.push a
    ws := ws.push b
    ws := ws.push c
  let bytes := ws.foldl pushWordLE (ByteArray.emptyWithCapacity (ws.size * 4))
  let stats : ProgStats := {
    nVars := nVars
    nNodes := nNodes
    nCwords := nCwords
    totalAtomBits := st.totalAtomBits
    estAigGates := st.estAigGates
    estClauses := 3 * st.estAigGates + 1
    maxWidth := st.maxWidth
  }
  return {
    words := ws.toList
    bytes := bytes
    varTable := st.vars
    atomBase := st.atomBase
    stats := stats
  }

/-- Encode a `BVLogicalExpr` into `BVP1` 32-bit `Nat` words (`none` if any limit reaches `2^32`). -/
def encodeWords (e : BVLogicalExpr) : Option (List Nat) :=
  (encode e).map (·.words)

/-- Convenience upfront workspace size estimate directly from a `BVLogicalExpr`. -/
def estimateWorkSizeOfExpr (e : BVLogicalExpr) : UInt64 :=
  match encode e with
  | some p => p.estimateWorkSize
  | none => minWorkBytes.toUInt64

end BvDecideQbe
