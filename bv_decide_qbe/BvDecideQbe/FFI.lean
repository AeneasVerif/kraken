module

public import Lean.Meta.Basic
public import Lean.Elab.DeclarationRange
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic

/-!
# Encapsulated Trusted FFI Boundary for `bv_solve_bytes` (`Step 2`)

Only module allowed to invoke `leanqbe_solve_bv_bytes` (`bv_solve_bytes`) or emit
`_leanqbe.bv_solve.ax` axioms:
- `RawSolveResult`, `allocWorkBuf`, and `solveBVBytesRaw` are strictly `private`.
- `UnsatWitness` has a `private mk ::` constructor so no outside module can forge a witness.
- `solveBVProg` / `solveBVProgWithStats` pack `words : List Nat` directly inside this trusted
  boundary, invoke `bv_solve_bytes` with `2x` workspace doubling on `.workTooSmall`, and on `.unsat`
  return a witness whose `addAxiom` continuation emits one per-invocation
  `Lean.addDecl (.axiomDecl ...)` matching `BVProg.unsat_of_bv_solve_words`.
- Probing (e.g. during `+uf` CEGAR) emits zero axioms until `witness.addAxiom` is called on commit.
-/

set_option autoImplicit false

public section

namespace BvDecideQbe

open Lean
open Lean.Meta
open Std.Tactic.BVDecide

private def bvProgWordsToBytesLEName : Name :=
  `LeanQbe.T.Examples.Bitblast.Ref.BVProg.wordsToBytesLE

private def bvProgParseName : Name :=
  `LeanQbe.T.Examples.Bitblast.Ref.BVProg.parse

@[expose] def bvProgU32Bound : Nat := 4294967296

/-- Private FFI result matching `leanqbe_solve_bv_bytes` C constructor layout. -/
private inductive RawSolveResult where
  | unsat
  | sat (model : ByteArray)
  | unknown
  | workTooSmall
  | timeout
  deriving BEq, Inhabited

@[extern "leanqbe_alloc_work_buf"]
private opaque allocWorkBuf (n : UInt64) : ByteArray

@[extern "leanqbe_solve_bv_bytes"]
private opaque solveBVBytesRaw (prog : @& ByteArray) (work : ByteArray) (fuel : UInt64) :
    RawSolveResult

/-- Default initial scratch workspace size (`256 KiB`; auto-doubles on `.workTooSmall`). -/
def defaultInitWorkBytes : UInt64 := 256 * 1024

/-- Default maximum scratch workspace size (`1 GiB`). -/
def defaultMaxWorkBytes : UInt64 := 1024 * 1024 * 1024

/-- Calibrated `KissatFidelity` propagation/search fuel units per second of wall-clock timeout. -/
def fuelPerSecond : UInt64 := 15000000

/-- Convert a wall-clock `timeout` in seconds into a deterministic `KissatFidelity` fuel budget
(`0` yields `0`, triggering an immediate `.timeout`). -/
def fuelOfTimeout (timeoutSec : Nat) : UInt64 :=
  if timeoutSec == 0 then
    0
  else
    let prod := timeoutSec * fuelPerSecond.toNat
    if prod >= UInt64.size then
      UInt64.ofNat (UInt64.size - 1)
    else
      prod.toUInt64

/-- Default Kissat fuel budget (`10` seconds). -/
def defaultFuel : UInt64 := fuelOfTimeout 10

/-- Unforgeable UNSAT witness produced only when in-process `bv_solve_bytes` returns `20`.
Constructor `UnsatWitness.mk` is `private` to `BvDecideQbe.FFI`. -/
structure UnsatWitness where
  private mk ::
  words : List Nat
  addAxiom : (axiomDeclRange? : Option Syntax := none) → MetaM Name
  addAxiomWithWsExpr : (axiomDeclRange? : Option Syntax := none) → MetaM (Name × Expr)

/-- Outcome of an in-process verified `bv_solve_bytes` invocation. -/
inductive VerifiedSolveResult where
  | unsat (witness : UnsatWitness)
  | sat (model : ByteArray)
  | unknown
  | workTooSmall
  | timeout

instance : Inhabited VerifiedSolveResult := ⟨.unknown⟩

/-- Full outcome + resource accounting returned by `solveBVProgWithStats`. -/
structure SolveOutcome where
  result : VerifiedSolveResult
  workBytesUsed : Nat
  attempts : Nat
  deriving Inhabited

private def smallNatLitExprs : Array Expr :=
  (Array.range 64).map mkRawNatLit

@[inline] private def mkCachedNatLit (w : Nat) : Expr :=
  if h : w < smallNatLitExprs.size then
    smallNatLitExprs[w]
  else
    mkRawNatLit w

/-- Build a closed `List Nat` expression directly from `Array Nat` without reversing a `List`. -/
def mkNatListExprArray (ws : Array Nat) : Expr := Id.run do
  let natTy := mkConst ``Nat
  let nil := mkApp (mkConst ``List.nil [0]) natTy
  let cons := mkApp (mkConst ``List.cons [0]) natTy
  let mut acc := nil
  let mut i := ws.size
  while i > 0 do
    i := i - 1
    acc := mkApp2 cons (mkCachedNatLit ws[i]!) acc
  return acc

/-- Build a closed `List Nat` expression using tail-recursive folding and raw `Nat` literals. -/
def mkNatListExpr (ws : List Nat) : Expr :=
  let natTy := mkConst ``Nat
  let nil := mkApp (mkConst ``List.nil [0]) natTy
  let cons := mkApp (mkConst ``List.cons [0]) natTy
  ws.reverse.foldl (fun acc w => mkApp2 cons (mkCachedNatLit w) acc) nil

/-- Build the `Prop` matching `LinkedCert` conclusion word-for-word:
`∃ e : BVLogicalExpr, BVProg.parse (BVProg.wordsToBytesLE ws) = some e ∧ e.Unsat`. -/
private def mkBvSolveAxiomType (wsExpr : Expr) : Expr :=
  let bvLogTy := mkConst ``BVLogicalExpr
  let optBvLogTy := mkApp (mkConst ``Option [0]) bvLogTy
  let bytesExpr := mkApp (mkConst bvProgWordsToBytesLEName) wsExpr
  let parsedExpr := mkApp (mkConst bvProgParseName) bytesExpr
  let eqExpr := mkApp3 (mkConst ``Eq [1]) optBvLogTy parsedExpr
    (mkApp2 (mkConst ``Option.some [0]) bvLogTy (mkBVar 0))
  let unsatExpr := mkApp (mkConst ``BVLogicalExpr.Unsat) (mkBVar 0)
  let pred := mkLambda `e .default bvLogTy (mkApp2 (mkConst ``And) eqExpr unsatExpr)
  mkApp2 (mkConst ``Exists [1]) bvLogTy pred

private def getClosedU32NatLit? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal w) => if w < bvProgU32Bound then some w else none
  | .app (.app (.app (.const ``OfNat.ofNat _) (.const ``Nat [])) (.lit (.natVal w))) _ =>
    if w < bvProgU32Bound then some w else none
  | _ => none

private partial def isClosedU32NatListExpr (e : Expr) : Bool :=
  match e with
  | .app (.const ``List.nil [0]) (.const ``Nat []) => true
  | .app (.app (.app (.const ``List.cons [0]) (.const ``Nat [])) hd) tl =>
    (getClosedU32NatLit? hd).isSome && isClosedU32NatListExpr tl
  | _ => false

/-- Structurally validate that `ty` has the exact trusted `bv_solve_bytes` axiom shape:
`∃ e : BVLogicalExpr, BVProg.parse (BVProg.wordsToBytesLE ws) = some e ∧ e.Unsat`
with a closed `List Nat` of `< 2^32` literals. Defends axiom audits against prefix spoofing. -/
def isValidBvSolveAxiomType (ty : Expr) : Bool :=
  match ty with
  | .app (.app (.const ``Exists [1]) (.const ``BVLogicalExpr []))
      (.lam _ (.const ``BVLogicalExpr []) body _) =>
    match body with
    | .app (.app (.const ``And []) eqExpr)
        (.app (.const ``BVLogicalExpr.Unsat []) (.bvar 0)) =>
      match eqExpr with
      | .app (.app (.app (.const ``Eq [1])
          (.app (.const ``Option [0]) (.const ``BVLogicalExpr [])))
          (.app (.const parseNm []) (.app (.const w2bNm []) wsExpr)))
          (.app (.app (.const ``Option.some [0]) (.const ``BVLogicalExpr [])) (.bvar 0)) =>
        parseNm == bvProgParseName && w2bNm == bvProgWordsToBytesLEName &&
          isClosedU32NatListExpr wsExpr
      | _ => false
    | _ => false
  | _ => false

/-- Append one 32-bit `Nat` word in canonical little-endian byte order onto `ba`. -/
@[expose, inline] def pushWordU32LE (ba : ByteArray) (w : Nat) : ByteArray :=
  let u := w.toUInt32
  (((ba.push u.toUInt8).push (u >>> 8).toUInt8).push (u >>> 16).toUInt8).push
    (u >>> 24).toUInt8

/-- Tail-recursive list loop backing `packWordsU32LE`. -/
@[expose] def packWordsU32LEGo : List Nat → ByteArray → Option ByteArray
  | [], ba => some ba
  | w :: ws, ba =>
    if w < bvProgU32Bound then
      packWordsU32LEGo ws (pushWordU32LE ba w)
    else
      none

/-- Pack `words : List Nat` into canonical little-endian 32-bit words inside the trusted boundary
so the solved bytes match `BVProg.wordsToBytesLE words` 1:1. Returns `none` if any word `≥ 2^32`. -/
@[expose] def packWordsU32LE (words : List Nat) : Option ByteArray :=
  packWordsU32LEGo words (ByteArray.emptyWithCapacity (words.length * 4))

/-- Indexed array loop backing `packWordsArrayU32LE`. -/
@[expose] def packWordsArrayU32LEGo (words : Array Nat) (i : Nat) (ba : ByteArray) :
    Option ByteArray :=
  if h : i < words.size then
    if words[i] < bvProgU32Bound then
      packWordsArrayU32LEGo words (i + 1) (pushWordU32LE ba words[i])
    else
      none
  else
    some ba
termination_by words.size - i

/-- Single-pass trusted packer from `Array Nat` into canonical little-endian 32-bit words.
Returns `none` if any word `≥ 2^32`. -/
@[expose] def packWordsArrayU32LE (words : Array Nat) : Option ByteArray :=
  packWordsArrayU32LEGo words 0 (ByteArray.emptyWithCapacity (words.size * 4))

private theorem byteArray_toList_loop_eq (bs : ByteArray) :
    ∀ (i : Nat) (r : List UInt8),
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  intro i r
  fun_induction ByteArray.toList.loop bs i r with
  | case1 i r hi ih =>
    rw [ih]
    have hltData : i < bs.data.size := by rw [ByteArray.size_data]; exact hi
    have hlt : i < bs.data.toList.length := by rw [Array.length_toList]; exact hltData
    have hget : bs.get! i = bs.data.toList[i]'hlt := by
      cases bs with
      | mk data =>
        simp only [ByteArray.get!, getElem!_pos data i hltData]
        rfl
    rw [List.reverse_cons, List.append_assoc, List.singleton_append, hget,
      List.getElem_cons_drop]
  | case2 i r hge =>
    have hle : bs.data.toList.length ≤ i := by
      rw [Array.length_toList, ByteArray.size_data]
      exact Nat.le_of_not_lt hge
    have hdrop : bs.data.toList.drop i = [] := List.drop_eq_nil_of_le hle
    simp [hdrop]

/-- `ByteArray.toList` coincides with `bs.data.toList`. -/
theorem byteArray_toList_eq_data_toList (bs : ByteArray) :
    bs.toList = bs.data.toList := by
  simpa [ByteArray.toList] using byteArray_toList_loop_eq bs 0 []

private theorem uint8_eq_of_toNat_eq {a b : UInt8} (h : a.toNat = b.toNat) : a = b :=
  UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

private theorem toUInt32_shr_toUInt8 {w k : Nat} (hw : w < bvProgU32Bound) (hk : k < 32) :
    ((w.toUInt32 >>> k.toUInt32).toUInt8) = ((w / 2 ^ k) % 256).toUInt8 := by
  apply uint8_eq_of_toNat_eq
  have hw32 : w < UInt32.size := hw
  have hk32 : k < UInt32.size := Nat.lt_trans hk (by decide)
  simp only [Nat.toUInt32, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight,
    UInt32.toNat_ofNat_of_lt' hw32, UInt32.toNat_ofNat_of_lt' hk32, Nat.mod_eq_of_lt hk,
    Nat.shiftRight_eq_div_pow, Nat.toUInt8, UInt8.toNat_ofNat',
    Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 256)]

/-- Pushing one `< 2^32` word onto `ba` appends its exact 4 little-endian bytes. -/
theorem pushWordU32LE_toList (ba : ByteArray) {w : Nat} (hw : w < bvProgU32Bound) :
    (pushWordU32LE ba w).toList =
      ba.toList ++ [(w % 256).toUInt8, ((w / 256) % 256).toUInt8,
        ((w / 65536) % 256).toUInt8, ((w / 16777216) % 256).toUInt8] := by
  have hb0 : w.toUInt32.toUInt8 = (w % 256).toUInt8 := by
    apply uint8_eq_of_toNat_eq
    have hw32 : w < UInt32.size := hw
    simp only [Nat.toUInt32, UInt32.toNat_toUInt8, UInt32.toNat_ofNat_of_lt' hw32,
      Nat.toUInt8, UInt8.toNat_ofNat', Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 256)]
  have hb1 : (w.toUInt32 >>> 8).toUInt8 = ((w / 256) % 256).toUInt8 :=
    toUInt32_shr_toUInt8 hw (by decide : 8 < 32)
  have hb2 : (w.toUInt32 >>> 16).toUInt8 = ((w / 65536) % 256).toUInt8 :=
    toUInt32_shr_toUInt8 hw (by decide : 16 < 32)
  have hb3 : (w.toUInt32 >>> 24).toUInt8 = ((w / 16777216) % 256).toUInt8 :=
    toUInt32_shr_toUInt8 hw (by decide : 24 < 32)
  simp only [byteArray_toList_eq_data_toList, pushWordU32LE, ByteArray.data_push,
    Array.toList_push, hb0, hb1, hb2, hb3, List.append_assoc, List.cons_append, List.nil_append]

private theorem packWordsArrayU32LEGo_eq (words : Array Nat) :
    ∀ (i : Nat) (ba : ByteArray),
      packWordsArrayU32LEGo words i ba = packWordsU32LEGo (words.toList.drop i) ba := by
  intro i ba
  fun_induction packWordsArrayU32LEGo words i ba with
  | case1 i ba hlt hw ih =>
    have hlt' : i < words.toList.length := by rw [Array.length_toList]; exact hlt
    have hdrop : words.toList.drop i = words[i] :: words.toList.drop (i + 1) := by
      simpa using (List.getElem_cons_drop hlt').symm
    rw [hdrop, packWordsU32LEGo, ih]
    simp [hw]
  | case2 i ba hlt hge =>
    have hlt' : i < words.toList.length := by rw [Array.length_toList]; exact hlt
    have hdrop : words.toList.drop i = words[i] :: words.toList.drop (i + 1) := by
      simpa using (List.getElem_cons_drop hlt').symm
    rw [hdrop, packWordsU32LEGo]
    simp [hge]
  | case3 i ba hge =>
    have hdrop : words.toList.drop i = [] :=
      List.drop_eq_nil_of_le (by rw [Array.length_toList]; exact Nat.le_of_not_lt hge)
    rw [hdrop, packWordsU32LEGo]

/-- `packWordsArrayU32LE` is extensionally identical to `packWordsU32LE words.toList`. -/
theorem packWordsArrayU32LE_eq_packWordsU32LE (words : Array Nat) :
    packWordsArrayU32LE words = packWordsU32LE words.toList := by
  unfold packWordsArrayU32LE packWordsU32LE
  have hcap : ByteArray.emptyWithCapacity (words.size * 4) =
      ByteArray.emptyWithCapacity (words.toList.length * 4) := by
    simp
  rw [hcap]
  simpa using packWordsArrayU32LEGo_eq words 0
    (ByteArray.emptyWithCapacity (words.toList.length * 4))

private def emitBvSolveAxiom (wsExpr : Expr) (axiomDeclRange? : Option Syntax) :
    MetaM (Name × Expr) := do
  let axType := mkBvSolveAxiomType wsExpr
  let auxAxiomName ← Lean.mkAuxDeclName `_leanqbe.bv_solve.ax
  Lean.addDecl <| .axiomDecl {
    name := auxAxiomName
    levelParams := []
    type := axType
    isUnsafe := false
  }
  if let some ref := axiomDeclRange? then
    Elab.addDeclarationRangesFromSyntax auxAxiomName ref
  return (auxAxiomName, wsExpr)

private def mkUnsatWitness (words : List Nat) : UnsatWitness :=
  let commit := fun axiomDeclRange? =>
    emitBvSolveAxiom (mkNatListExpr words) axiomDeclRange?
  {
    words := words
    addAxiom := fun axiomDeclRange? => return (← commit axiomDeclRange?).1
    addAxiomWithWsExpr := commit
  }

private def mkUnsatWitnessArray (words : Array Nat) : UnsatWitness :=
  let commit := fun axiomDeclRange? =>
    emitBvSolveAxiom (mkNatListExprArray words) axiomDeclRange?
  {
    words := words.toList
    addAxiom := fun axiomDeclRange? => return (← commit axiomDeclRange?).1
    addAxiomWithWsExpr := commit
  }

private def solvePackedBVProg (progBA : ByteArray) (mkWitness : Unit → UnsatWitness)
    (initWorkBytes maxWorkBytes fuel : UInt64) : IO SolveOutcome := do
  let clampedMax := min defaultMaxWorkBytes (max 1 maxWorkBytes)
  let clampedInit := min clampedMax (max 1 initWorkBytes)
  go clampedMax 32 clampedInit 1
where
  go (clampedMax : UInt64) : Nat → UInt64 → Nat → IO SolveOutcome
    | 0, curWork, attempts =>
      return { result := .workTooSmall, workBytesUsed := curWork.toNat, attempts := attempts }
    | steps + 1, curWork, attempts => do
      let work := allocWorkBuf curWork
      match solveBVBytesRaw progBA work fuel with
      | .unsat =>
        return {
          result := .unsat (mkWitness ())
          workBytesUsed := curWork.toNat
          attempts := attempts
        }
      | .sat model =>
        return {
          result := .sat model
          workBytesUsed := curWork.toNat
          attempts := attempts
        }
      | .unknown =>
        return {
          result := .unknown
          workBytesUsed := curWork.toNat
          attempts := attempts
        }
      | .timeout =>
        return {
          result := .timeout
          workBytesUsed := curWork.toNat
          attempts := attempts
        }
      | .workTooSmall =>
        if curWork < clampedMax then
          let nextWork :=
            if curWork > clampedMax / 2 then clampedMax else curWork * 2
          if nextWork <= curWork then
            return { result := .workTooSmall, workBytesUsed := curWork.toNat, attempts := attempts }
          else
            go clampedMax steps nextWork (attempts + 1)
        else
          return { result := .workTooSmall, workBytesUsed := curWork.toNat, attempts := attempts }

/-- Solve a `BVP1` 32-bit `Array Nat` word stream in-process via verified `bv_solve_bytes`,
with deterministic `2x` workspace retry on `.workTooSmall`. Zero axioms are emitted until
`witness.addAxiom` / `witness.addAxiomWithWsExpr` is explicitly invoked. -/
def solveBVProgArrayWithStats (words : Array Nat)
    (initWorkBytes : UInt64 := defaultInitWorkBytes)
    (maxWorkBytes : UInt64 := defaultMaxWorkBytes)
    (fuel : UInt64 := defaultFuel) : IO SolveOutcome := do
  let some progBA := packWordsArrayU32LE words
    | return { result := .unknown, workBytesUsed := 0, attempts := 0 }
  solvePackedBVProg progBA (fun () => mkUnsatWitnessArray words) initWorkBytes maxWorkBytes fuel

/-- Solve a `BVP1` 32-bit word stream in-process via verified `bv_solve_bytes`, with deterministic
`2x` workspace retry on `.workTooSmall` up to `min 1GiB maxWorkBytes`, returning `SolveOutcome`.
Zero axioms are emitted until `witness.addAxiom` is explicitly invoked. -/
def solveBVProgWithStats (words : List Nat)
    (initWorkBytes : UInt64 := defaultInitWorkBytes)
    (maxWorkBytes : UInt64 := defaultMaxWorkBytes)
    (fuel : UInt64 := defaultFuel) : IO SolveOutcome := do
  let some progBA := packWordsU32LE words
    | return { result := .unknown, workBytesUsed := 0, attempts := 0 }
  solvePackedBVProg progBA (fun () => mkUnsatWitness words) initWorkBytes maxWorkBytes fuel

/-- Solve a `BVP1` 32-bit word stream in-process via verified `bv_solve_bytes`. -/
def solveBVProg (words : List Nat)
    (initWorkBytes : UInt64 := defaultInitWorkBytes)
    (maxWorkBytes : UInt64 := defaultMaxWorkBytes)
    (fuel : UInt64 := defaultFuel) : IO VerifiedSolveResult := do
  return (← solveBVProgWithStats words initWorkBytes maxWorkBytes fuel).result

end BvDecideQbe
