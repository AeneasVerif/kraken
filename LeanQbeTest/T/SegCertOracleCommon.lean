/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.InlinePlan
public import LeanQbe.T.Main
public import LeanQbe.T.MainFlat

/-!
# Subsystem-Aligned Build Oracle Serializer (`SegCertOracleCommon`)

Pure compiled `IO` oracle library (zero `*Lemmas*`, zero `Lean` meta, zero arch crates) that:
1. Extracts exact per-subsystem `InlPlan`s from `policyToInlPlan` (`selectCandsForCaller` parity),
   determines minimal cross-subsystem `Exports` targets (`planExportsFor`), and computes DAG deps.
2. Serializes deterministic, `<= 100`-column Lean 4 data modules:
   - `Oracle/<S>.lean`: `def plan : InlPlan`
   - `Inl/<S>/Exports.lean`: pure `TFlatFn` leaf (zero import of `Src/<S>` or `Inl/<S>`)
   - `Oracle/{Amd64,Arm64}/<S>.lean`: `hints`, pruned `ext`, plus per-fn `hint_<fn>` / `ext_<fn>`
3. Emits subsystem manifest + per-fn size/bound JSON for `scripts/gen_build_segs.py`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertOracle

open LeanQbe.T

/-- Named source subsystem input for oracle generation. -/
structure SegInput where
  name : String
  srcMod : String
  srcFns : String := "fns"
  fns : List Fn

/-- Computed arch-neutral plan, dependency, and export metadata for one subsystem. -/
structure SegPlanInfo where
  seg : SegInput
  plan : InlPlan
  deps : List String
  exportNames : List Sym
  inlinedFlats : List TFlatFn

/-! ## 1. Deterministic `<= 96`-Column Lean Literal & Stream Printers -/

private def maxCol : Nat := 96

private def fmtStr (s : String) : String :=
  toString (repr s)

private def fmtTyStr : Ty → String
  | .bool => ".bool"
  | .bits 8 => "i8"
  | .bits 16 => "i16"
  | .bits 32 => "i32"
  | .bits 64 => "i64"
  | .bits n => s!"(Ty.bits {n})"
  | .float .h => "f16"
  | .float .s => "f32"
  | .float .d => "f64"
  | .float .q => "f128"
  | .pair a b => s!"(.pair {fmtTyStr a} {fmtTyStr b})"

private def packLines (pfx sfx contIndent : String) (elems : List String) : List String :=
  match elems with
  | [] => [pfx ++ sfx]
  | first :: rest =>
    Id.run do
      let mut out : Array String := #[]
      let mut cur := pfx ++ first
      let sfxPad := max 1 sfx.length
      for el in rest do
        let candidate := cur ++ ", " ++ el
        if candidate.length + sfxPad <= maxCol then
          cur := candidate
        else
          out := out.push (cur ++ ",")
          cur := contIndent ++ el
      out := out.push (cur ++ sfx)
      return out.toList

private def fmtListLines (pfx sfx indent : String) (elems : List String) : List String :=
  if elems.isEmpty then [pfx ++ "[]" ++ sfx]
  else
    let one := pfx ++ "[" ++ String.intercalate ", " elems ++ "]" ++ sfx
    if one.length <= maxCol then [one]
    else packLines (pfx ++ "[") ("]" ++ sfx) (indent ++ "  ") elems

private def fmtTyListStr (ts : List Ty) : String :=
  "[" ++ String.intercalate ", " (ts.map fmtTyStr) ++ "]"

private def fmtFmt : Fmt → String
  | .h => ".h" | .s => ".s" | .d => ".d" | .q => ".q"

private def fmtCmpOp : CmpOp → String
  | .eq => ".eq" | .ne => ".ne" | .ult => ".ult" | .ule => ".ule" | .ugt => ".ugt"
  | .uge => ".uge" | .slt => ".slt" | .sle => ".sle" | .sgt => ".sgt" | .sge => ".sge"

private def fmtFCmpOp : FCmpOp → String
  | .eq => ".eq" | .ne => ".ne" | .lt => ".lt" | .le => ".le"
  | .gt => ".gt" | .ge => ".ge" | .ord => ".ord" | .uno => ".uno"

private def fmtValStr : (t : Ty) → Val t → String
  | .bool, v => if v then "true" else "false"
  | .bits n, v => s!"BitVec.ofNat {n} {v.toNat}"
  | .float f, v => s!"BitVec.ofNat {f.width} {v.toNat}"
  | .pair a b, (x, y) => s!"({fmtValStr a x}, {fmtValStr b y})"

private def fmtValAtom : (t : Ty) → Val t → String
  | .bool, v => if v then "true" else "false"
  | .pair a b, (x, y) => fmtValStr (.pair a b) (x, y)
  | t, v => s!"({fmtValStr t v})"

private def fmtArgKAtom (t : Ty) : Arg K t → String
  | .var idx => s!"(.var {idx})"
  | .imm c => s!"(.imm {fmtValAtom t c})"

private def fmtArgKElem (t : Ty) : Arg K t → String
  | .var idx => s!".var {idx}"
  | .imm c => s!".imm {fmtValAtom t c}"

private def fmtTupArgKElems : (ts : List Ty) → Tup (Arg K) ts → List String
  | [], () => []
  | t :: ts, (a, rest) => fmtArgKElem t a :: fmtTupArgKElems ts rest

private def fmtTupArgKInline (ts : List Ty) (args : Tup (Arg K) ts) : String :=
  let elems := fmtTupArgKElems ts args
  if elems.isEmpty then "()"
  else "(" ++ String.intercalate ", " (elems ++ ["()"]) ++ ")"

private def fmtTupArgKLines (pfx sfx indent : String) (ts : List Ty)
    (args : Tup (Arg K) ts) : List String :=
  let elems := fmtTupArgKElems ts args
  if elems.isEmpty then [pfx ++ "()" ++ sfx]
  else
    let allElems := elems ++ ["()"]
    let one := pfx ++ "(" ++ String.intercalate ", " allElems ++ ")" ++ sfx
    if one.length <= maxCol then [one]
    else packLines (pfx ++ "(") (")" ++ sfx) indent allElems

private def fmtOpCodeStr {sig rs : List Ty} : OpCode sig rs → String
  | .copy t => ".copy " ++ fmtTyStr t
  | .add t => ".add " ++ fmtTyStr t
  | .sub t => ".sub " ++ fmtTyStr t
  | .mul t => ".mul " ++ fmtTyStr t
  | .neg t => ".neg " ++ fmtTyStr t
  | .and t => ".and " ++ fmtTyStr t
  | .or t => ".or " ++ fmtTyStr t
  | .xor t => ".xor " ++ fmtTyStr t
  | .not t => ".not " ++ fmtTyStr t
  | .ternlog t i => s!".ternlog {fmtTyStr t} (BitVec.ofNat 8 {i.toNat})"
  | .shl t => ".shl " ++ fmtTyStr t
  | .lshr t => ".lshr " ++ fmtTyStr t
  | .ashr t => ".ashr " ++ fmtTyStr t
  | .rotl t => ".rotl " ++ fmtTyStr t
  | .rotr t => ".rotr " ++ fmtTyStr t
  | .fshl n => s!".fshl {n}"
  | .fshr n => s!".fshr {n}"
  | .bswap t => ".bswap " ++ fmtTyStr t
  | .clz n => s!".clz {n}"
  | .cls n => s!".cls {n}"
  | .rbit n => s!".rbit {n}"
  | .ctz n => s!".ctz {n}"
  | .popcnt n => s!".popcnt {n}"
  | .cmp o t m _ => s!".cmp {fmtCmpOp o} {fmtTyStr t} {fmtTyStr m} rfl"
  | .select t => ".select " ++ fmtTyStr t
  | .blend t m _ => s!".blend {fmtTyStr t} {fmtTyStr m} rfl"
  | .zext m n => s!".zext {m} {n}"
  | .sext m n => s!".sext {m} {n}"
  | .trunc m n => s!".trunc {m} {n}"
  | .ofBool n => s!".ofBool {n}"
  | .addc n => s!".addc {n}"
  | .subb n => s!".subb {n}"
  | .umulw n => s!".umulw {n}"
  | .smulw n => s!".smulw {n}"
  | .udiv n => s!".udiv {n}"
  | .sdiv n => s!".sdiv {n}"
  | .urem n => s!".urem {n}"
  | .srem n => s!".srem {n}"
  | .udiv0 n => s!".udiv0 {n}"
  | .sdiv0 n => s!".sdiv0 {n}"
  | .mkpair a b => s!".mkpair {fmtTyStr a} {fmtTyStr b}"
  | .unpair a b => s!".unpair {fmtTyStr a} {fmtTyStr b}"
  | .bitcast t u _ => s!".bitcast {fmtTyStr t} {fmtTyStr u} rfl"
  | .shufd t i => s!".shufd {fmtTyStr t} (BitVec.ofNat 8 {i.toNat})"
  | .shufb t => ".shufb " ++ fmtTyStr t
  | .alignr t i => s!".alignr {fmtTyStr t} (BitVec.ofNat 8 {i.toNat})"
  | .blendw t i => s!".blendw {fmtTyStr t} (BitVec.ofNat 8 {i.toNat})"
  | .sha256rnds2 => ".sha256rnds2"
  | .sha256msg1 => ".sha256msg1"
  | .sha256msg2 => ".sha256msg2"
  | .fadd t => ".fadd " ++ fmtTyStr t
  | .fsub t => ".fsub " ++ fmtTyStr t
  | .fmul t => ".fmul " ++ fmtTyStr t
  | .fdiv t => ".fdiv " ++ fmtTyStr t
  | .ffma t => ".ffma " ++ fmtTyStr t
  | .fsqrt t => ".fsqrt " ++ fmtTyStr t
  | .fneg t => ".fneg " ++ fmtTyStr t
  | .fabs t => ".fabs " ++ fmtTyStr t
  | .fcmp o t m _ => s!".fcmp {fmtFCmpOp o} {fmtTyStr t} {fmtTyStr m} rfl"
  | .fptoui f n => s!".fptoui {fmtFmt f} {n}"
  | .fptosi f n => s!".fptosi {fmtFmt f} {n}"
  | .uitofp n f => s!".uitofp {n} {fmtFmt f}"
  | .sitofp n f => s!".sitofp {n} {fmtFmt f}"
  | .fcvt f g => s!".fcvt {fmtFmt f} {fmtFmt g}"

private def mkIndent (n : Nat) : String :=
  String.ofList (List.replicate (min n 12) ' ')

private def wrapSfx (lines : List String) (sfx : String) : List String :=
  match lines.reverse with
  | [] => [sfx]
  | last :: restRev => (last ++ sfx) :: restRev |>.reverse

private def stripLeadingSpaces (s : String) : String :=
  String.ofList (s.toList.dropWhile (· == ' '))

private def wrapParenLines (ind : String) (lines : List String) (sfx : String) : List String :=
  match lines with
  | [] => [ind ++ "()" ++ sfx]
  | [one] =>
    let trimmed := stripLeadingSpaces one
    let cand := ind ++ "(" ++ trimmed ++ ")" ++ sfx
    if cand.length <= maxCol then [cand]
    else [ind ++ "(" ++ trimmed, ind ++ ")" ++ sfx]
  | first :: rest =>
    let head := ind ++ "(" ++ stripLeadingSpaces first
    let tail := wrapSfx rest (")" ++ sfx)
    head :: tail

private def fmtOpKLines (pfx sfx indent : String) {rs : List Ty} (op : Op K rs) : List String :=
  let codeS := fmtOpCodeStr op.code
  let argS := fmtTupArgKInline op.sig op.args
  let one := pfx ++ "⟨" ++ codeS ++ ", " ++ argS ++ "⟩" ++ sfx
  if one.length <= maxCol then [one]
  else
    let l1 := pfx ++ "⟨" ++ codeS ++ ","
    if l1.length <= maxCol then
      l1 :: fmtTupArgKLines indent ("⟩" ++ sfx) (indent ++ "  ") op.sig op.args
    else
      [pfx ++ "⟨", indent ++ codeS ++ ","] ++
        fmtTupArgKLines indent ("⟩" ++ sfx) (indent ++ "  ") op.sig op.args

mutual
private def fmtTFlatLines (depth : Nat) (sfx : String) {rs : List Ty} :
    TFlat rs → List String
  | .let_ (ts := ts) op k =>
    let ind := mkIndent depth
    let subInd := mkIndent (depth + 2)
    let tsS := fmtTyListStr ts
    let head := s!"{ind}TFlat.let_ (ts := {tsS}) "
    let opLines :=
      if head.length + 20 <= maxCol then
        fmtOpKLines head " <|" subInd op
      else
        [s!"{ind}TFlat.let_ (ts := {tsS})"] ++ fmtOpKLines subInd " <|" subInd op
    opLines ++ fmtTFlatLines depth sfx k
  | .load t a k =>
    let ind := mkIndent depth
    let subInd := mkIndent (depth + 2)
    let line := s!"{ind}TFlat.load {fmtTyStr t} {fmtArgKAtom i64 a} <|"
    let hd :=
      if line.length <= maxCol then [line]
      else [s!"{ind}TFlat.load {fmtTyStr t}", s!"{subInd}{fmtArgKAtom i64 a} <|"]
    hd ++ fmtTFlatLines depth sfx k
  | .store (t := t) v a k =>
    let ind := mkIndent depth
    let subInd := mkIndent (depth + 2)
    let tS := fmtTyStr t
    let vS := fmtArgKAtom t v
    let aS := fmtArgKAtom i64 a
    let line := s!"{ind}TFlat.store (t := {tS}) {vS} {aS} <|"
    let hd :=
      if line.length <= maxCol then [line]
      else [s!"{ind}TFlat.store (t := {tS}) {vS}", s!"{subInd}{aS} <|"]
    hd ++ fmtTFlatLines depth sfx k
  | .call f (as := as) bs args k =>
    let ind := mkIndent depth
    let subInd := mkIndent (depth + 2)
    let asS := fmtTyListStr as
    let bsS := fmtTyListStr bs
    let argsS := fmtTupArgKInline as args
    let one := s!"{ind}TFlat.call {fmtStr f} (as := {asS}) {bsS} {argsS} <|"
    let hd :=
      if one.length <= maxCol then [one]
      else
        let l1 := s!"{ind}TFlat.call {fmtStr f} (as := {asS}) {bsS}"
        let l1Lines :=
          if l1.length <= maxCol then [l1]
          else
            [s!"{ind}TFlat.call {fmtStr f}"] ++
              fmtListLines (subInd ++ "(as := ") ")" (subInd ++ "  ") (as.map fmtTyStr) ++
              fmtListLines subInd "" (subInd ++ "  ") (bs.map fmtTyStr)
        l1Lines ++ fmtTupArgKLines subInd " <|" (subInd ++ "  ") as args
    hd ++ fmtTFlatLines depth sfx k
  | .jnz c t e =>
    let ind := mkIndent depth
    let subInd := mkIndent (depth + 2)
    let tLines := wrapParenLines subInd (fmtTFlatLines (depth + 2) "" t) " <|"
    let hd := s!"{ind}TFlat.jnz {fmtArgKAtom .bool c}"
    [hd] ++ tLines ++ fmtTFlatLines depth sfx e
  | .jump (ts := ts) j args =>
    let ind := mkIndent depth
    let subInd := mkIndent (depth + 2)
    let tsS := fmtTyListStr ts
    let argsS := fmtTupArgKInline ts args
    let one := s!"{ind}TFlat.jump (ts := {tsS}) {j} {argsS}{sfx}"
    if one.length <= maxCol then [one]
    else
      let l1 := s!"{ind}TFlat.jump (ts := {tsS}) {j}"
      let l1Lines :=
        if l1.length <= maxCol then [l1]
        else fmtListLines (s!"{ind}TFlat.jump (ts := ") s!") {j}" subInd (ts.map fmtTyStr)
      l1Lines ++ fmtTupArgKLines subInd sfx (subInd ++ "  ") ts args
  | .ret vs =>
    let ind := mkIndent depth
    fmtTupArgKLines (ind ++ "TFlat.ret ") sfx (ind ++ "  ") rs vs
  | .exit f (as := as) args =>
    let ind := mkIndent depth
    let subInd := mkIndent (depth + 2)
    let asS := fmtTyListStr as
    let argsS := fmtTupArgKInline as args
    let one := s!"{ind}TFlat.exit {fmtStr f} (as := {asS}) {argsS}{sfx}"
    if one.length <= maxCol then [one]
    else
      let l1 := s!"{ind}TFlat.exit {fmtStr f} (as := {asS})"
      let l1Lines :=
        if l1.length <= maxCol then [l1]
        else [s!"{ind}TFlat.exit {fmtStr f}"] ++
          fmtListLines (subInd ++ "(as := ") ")" (subInd ++ "  ") (as.map fmtTyStr)
      l1Lines ++ fmtTupArgKLines subInd sfx (subInd ++ "  ") as args
  | .hlt => [mkIndent depth ++ "TFlat.hlt" ++ sfx]
  | .group (sig := sig) bodies k =>
    let ind := mkIndent depth
    let subInd := mkIndent (depth + 2)
    let sigS := "[" ++ String.intercalate ", " (sig.map fmtTyListStr) ++ "]"
    let hd := s!"{ind}TFlat.group (sig := {sigS})"
    let hdLines :=
      if hd.length <= maxCol then [hd]
      else fmtListLines (s!"{ind}TFlat.group (sig := ") ")" subInd (sig.map fmtTyListStr)
    let bLines := wrapParenLines subInd (fmtTBlocksLines (depth + 2) "" bodies) " <|"
    hdLines ++ bLines ++ fmtTFlatLines depth sfx k

private def fmtTBlocksLines (depth : Nat) (sfx : String) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → List String
  | _, .nil => [mkIndent depth ++ "TBlocks.nil" ++ sfx]
  | _, .cons (ts := ts) b bs =>
    let ind := mkIndent depth
    let subInd := mkIndent (depth + 2)
    let tsS := fmtTyListStr ts
    let hd := s!"{ind}TBlocks.cons (ts := {tsS})"
    let hdLines :=
      if hd.length <= maxCol then [hd]
      else fmtListLines (s!"{ind}TBlocks.cons (ts := ") ")" subInd (ts.map fmtTyStr)
    let bLines := wrapParenLines subInd (fmtTFlatLines (depth + 2) "" b) " <|"
    hdLines ++ bLines ++ fmtTBlocksLines depth sfx bs
end

private def fmtTFlatFnDef (idx : Nat) (tf : TFlatFn) : List String :=
  [ s!"@[expose] def flat{idx} : TFlatFn := \{"
  , s!"  name := {fmtStr tf.name}," ] ++
  fmtListLines "  as := " "," "  " (tf.as.map fmtTyStr) ++
  fmtListLines "  rs := " "," "  " (tf.rs.map fmtTyStr) ++
  [ "  body :=" ] ++
  fmtTFlatLines 4 " }" tf.body

private def fmtSigBoundInline (entry : SigEntry × Nat) : String :=
  let ((nm, as, rs), b) := entry
  s!"(({fmtStr nm}, {fmtTyListStr as}, {fmtTyListStr rs}), {b})"

private def fmtSigBoundLines (pfx sfx indent : String) (entry : SigEntry × Nat) : List String :=
  let ((nm, as, rs), b) := entry
  let one := pfx ++ fmtSigBoundInline entry ++ sfx
  if one.length <= maxCol then [one]
  else
    let subInd := indent ++ "  "
    let head := s!"{pfx}(({fmtStr nm},"
    if head.length <= maxCol then
      [head] ++
        fmtListLines subInd "," subInd (as.map fmtTyStr) ++
        fmtListLines subInd s!"), {b}){sfx}" subInd (rs.map fmtTyStr)
    else
      [pfx ++ "((" ++ fmtStr nm ++ ","] ++
        fmtListLines subInd "," subInd (as.map fmtTyStr) ++
        fmtListLines subInd s!"), {b}){sfx}" subInd (rs.map fmtTyStr)

private def fmtExtListLines (pfx sfx indent : String) (xs : List (SigEntry × Nat)) : List String :=
  if xs.isEmpty then [pfx ++ " []" ++ sfx]
  else
    let allOne := pfx ++ " [" ++ String.intercalate ", " (xs.map fmtSigBoundInline) ++ "]" ++ sfx
    if allOne.length <= maxCol then [allOne]
    else
      let rec go : Bool → List (SigEntry × Nat) → List String
        | _, [] => []
        | isFirst, [x] =>
          let p := if isFirst then indent ++ "[" else indent ++ " "
          fmtSigBoundLines p ("]" ++ sfx) (indent ++ " ") x
        | isFirst, x :: rest =>
          let p := if isFirst then indent ++ "[" else indent ++ " "
          fmtSigBoundLines p "," (indent ++ " ") x ++ go false rest
      [pfx] ++ go true xs

/-! ## 2. Compact ASCII-64 Stream Codec for `Hints` -/

private def c64Char (v : Nat) : Char :=
  let d := v % 64
  if d < 10 then Char.ofNat (48 + d)
  else if d < 36 then Char.ofNat (55 + d)
  else if d < 62 then Char.ofNat (61 + d)
  else if d == 62 then '+'
  else '/'

private def encNatAux : Nat → List Char → List Char
  | n, acc =>
    let lo := n % 32
    let ch := c64Char (if acc.isEmpty then lo else lo + 32)
    if n < 32 then ch :: acc
    else encNatAux (n / 32) (ch :: acc)
termination_by n => n

private def encNat (n : Nat) (acc : Array Char) : Array Char :=
  (encNatAux n []).foldl Array.push acc

private def chunkString (chunkLen : Nat) (s : String) : List String :=
  let rec go (pos : Nat) (cs : List Char) (cur : List Char) (out : List String) : List String :=
    match cs with
    | [] =>
      let last := String.ofList cur.reverse
      (if last.isEmpty && !out.isEmpty then out else last :: out).reverse
    | c :: rest =>
      if pos + 1 >= chunkLen then
        go 0 rest [] (String.ofList (c :: cur).reverse :: out)
      else
        go (pos + 1) rest (c :: cur) out
  go 0 s.toList [] []

private def trieToSortedList {α : Type} (t : Trie α) : List (Nat × α) :=
  let rec go (base stride : Nat) : Trie α → Array (Nat × α) → Array (Nat × α)
    | .empty, acc => acc
    | .node v e o, acc =>
      let acc1 := match v with | some x => acc.push (base, x) | none => acc
      let acc2 := go (base + stride) (stride * 2) e acc1
      go (base + 2 * stride) (stride * 2) o acc2
  (go 0 1 t #[]).qsort (fun a b => a.1 < b.1) |>.toList

private def boolTrieMasks (t : Trie Bool) : Nat × Nat :=
  (trieToSortedList t).foldl (fun (tm, fm) (k, b) =>
    if b then (tm ||| (1 <<< k), fm) else (tm, fm ||| (1 <<< k))) (0, 0)

private def fmtSlotWidth : SlotWidth → String
  | .w64 => ".w64" | .w128 => ".w128" | .w256 => ".w256" | .w512 => ".w512"

private def slotWidthIdx : SlotWidth → Nat
  | .w64 => 0 | .w128 => 1 | .w256 => 2 | .w512 => 3

private def fmtAtom (s : String) : String :=
  if s.contains ' ' then s!"({s})" else s

private def fmtLocStr {R V C : Type} (fR : R → String) (fV : V → String) (fC : C → String) :
    Loc R V C → String
  | .gpr r => s!"(.gpr {fmtAtom (fR r)})"
  | .vec v => s!"(.vec {fmtAtom (fV v)})"
  | .flag c => s!"(.flag {fmtAtom (fC c)})"
  | .slot i w => s!"(.slot {i} {fmtSlotWidth w})"

private structure OracleSymTables where
  regs : Array String := #[]
  vregs : Array String := #[]
  conds : Array String := #[]
  locs : Array String := #[]

private def internStr (arr : Array String) (s : String) : Nat × Array String :=
  match arr.findIdx? (· == s) with
  | some i => (i, arr)
  | none => (arr.size, arr.push s)

private def internLoc {R V C : Type} (fR : R → String) (fV : V → String) (fC : C → String)
    (tbl : OracleSymTables) (l : Loc R V C) : Nat × OracleSymTables :=
  let (idx, locs') := internStr tbl.locs (fmtLocStr fR fV fC l)
  (idx, { tbl with locs := locs' })

private def internHintsSyms {R V C : Type} (fR : R → String) (fV : V → String) (fC : C → String)
    (tbl0 : OracleSymTables) (h : Hints R V C) : OracleSymTables := Id.run do
  let mut tbl := tbl0
  for (_, l) in trieToSortedList h.dest do
    let (_, tbl') := internLoc fR fV fC tbl l
    tbl := tbl'
  for (_, e) in trieToSortedList h.entry do
    for (_, l) in e.live do
      let (_, tbl') := internLoc fR fV fC tbl l
      tbl := tbl'
    for l in e.ploc do
      let (_, tbl') := internLoc fR fV fC tbl l
      tbl := tbl'
  for (_, p) in trieToSortedList h.pre do
    for mv in p.moves do
      match mv with
      | .mov d s =>
        let (_, r1) := internStr tbl.regs (fmtAtom (fR d))
        let (_, r2) := internStr r1 (fmtAtom (fR s))
        tbl := { tbl with regs := r2 }
      | .movi d _ | .ld d _ =>
        let (_, r1) := internStr tbl.regs (fmtAtom (fR d))
        tbl := { tbl with regs := r1 }
      | .st _ s =>
        let (_, r1) := internStr tbl.regs (fmtAtom (fR s))
        tbl := { tbl with regs := r1 }
      | .setcc d c =>
        let (_, r1) := internStr tbl.regs (fmtAtom (fR d))
        let (_, c1) := internStr tbl.conds (fmtAtom (fC c))
        tbl := { tbl with regs := r1, conds := c1 }
      | .vmov _ d s =>
        let (_, v1) := internStr tbl.vregs (fmtAtom (fV d))
        let (_, v2) := internStr v1 (fmtAtom (fV s))
        tbl := { tbl with vregs := v2 }
      | .vmovi _ d _ | .vld _ d _ =>
        let (_, v1) := internStr tbl.vregs (fmtAtom (fV d))
        tbl := { tbl with vregs := v1 }
      | .vst _ _ s =>
        let (_, v1) := internStr tbl.vregs (fmtAtom (fV s))
        tbl := { tbl with vregs := v1 }
  for r in h.saved do
    let (_, r1) := internStr tbl.regs (fmtAtom (fR r))
    tbl := { tbl with regs := r1 }
  return tbl

private def encBoolList (bs : List Bool) (acc : Array Char) : Array Char :=
  let mask := bs.zipIdx.foldl (fun m (b, i) => if b then m ||| (1 <<< i) else m) 0
  encNat mask (encNat bs.length acc)

private def encSymArg (a : SymArg) (acc : Array Char) : Array Char :=
  match a with
  | .immBool false => encNat 0 acc
  | .immBool true => encNat 1 acc
  | .immBits w c => encNat c.toNat (encNat w (encNat 2 acc))
  | .immVec sw c => encNat c.toNat (encNat (slotWidthIdx sw) (encNat 3 acc))
  | .var x => encNat (x + 4) acc

private def encDeltas {α : Type} (xs : List (Nat × α)) (f : α → Array Char → Array Char)
    (acc : Array Char) : Array Char := Id.run do
  let mut out := encNat xs.length acc
  let mut prev := 0
  let mut isFirst := true
  for (k, v) in xs do
    let d := if isFirst then k else k - prev - 1
    out := f v (encNat d out)
    prev := k
    isFirst := false
  return out

private def encHintsStream {R V C : Type} (fR : R → String) (fV : V → String) (fC : C → String)
    (tbl : OracleSymTables) (h : Hints R V C) : String := Id.run do
  let idxOf := fun (arr : Array String) (s : String) =>
    (arr.findIdx? (· == s)).getD 0
  let locIdx := fun (l : Loc R V C) => idxOf tbl.locs (fmtLocStr fR fV fC l)
  let regIdx := fun (r : R) => idxOf tbl.regs (fmtAtom (fR r))
  let vregIdx := fun (v : V) => idxOf tbl.vregs (fmtAtom (fV v))
  let condIdx := fun (c : C) => idxOf tbl.conds (fmtAtom (fC c))
  let mut out : Array Char := #[]
  out := encDeltas (trieToSortedList h.dest) (fun l a => encNat (locIdx l) a) out
  out := encDeltas (trieToSortedList h.entry) (fun e a =>
    let a1 := encNat e.live.length a
    let a2 := e.live.foldl (fun acc (sa, l) => encNat (locIdx l) (encSymArg sa acc)) a1
    let a3 := encNat e.ploc.length a2
    let a4 := e.ploc.foldl (fun acc l => encNat (locIdx l) acc) a3
    encBoolList e.plocZ (encBoolList e.liveZ a4)) out
  out := encDeltas (trieToSortedList h.pre) (fun p a =>
    let packed := p.moves.length * 2 + (if p.clearFlags then 1 else 0)
    p.moves.foldl (fun acc mv => match mv with
      | .mov d s => encNat (regIdx s) (encNat (regIdx d) (encNat 0 acc))
      | .movi d c => encNat c.toNat (encNat (regIdx d) (encNat 1 acc))
      | .ld d i => encNat i (encNat (regIdx d) (encNat 2 acc))
      | .st i s => encNat (regIdx s) (encNat i (encNat 3 acc))
      | .setcc d c => encNat (condIdx c) (encNat (regIdx d) (encNat 4 acc))
      | .vmov w d s =>
        encNat (vregIdx s) (encNat (vregIdx d) (encNat (slotWidthIdx w) (encNat 5 acc)))
      | .vmovi w d c =>
        encNat c.toNat (encNat (vregIdx d) (encNat (slotWidthIdx w) (encNat 6 acc)))
      | .vld w d i =>
        encNat i (encNat (vregIdx d) (encNat (slotWidthIdx w) (encNat 7 acc)))
      | .vst w i s =>
        encNat (vregIdx s) (encNat i (encNat (slotWidthIdx w) (encNat 8 acc))))
      (encNat packed a)) out
  out := encDeltas (trieToSortedList h.variant) (fun vh a => match vh with
    | .default => encNat 0 a
    | .adcx => encNat 1 a
    | .adox => encNat 2 a
    | .mulxFast => encNat 3 a
    | .decInc => encNat 4 a
    | .disp off => encNat off.toBitVec.toNat (encNat 5 a)) out
  for bt in [h.elide, h.invertJnz, h.deferJnz, h.deferLea, h.deadFlags, h.mulHiIps] do
    let (tm, fm) := boolTrieMasks bt
    out := encNat fm (encNat tm out)
  out := encNat h.nslots out
  out := encNat h.saved.length out
  for r in h.saved do
    out := encNat (regIdx r) out
  return String.ofList out.toList

private def decoderHelperLines (isaExpr : String) : List String :=
  [ s!"@[expose] def _d64 (c : Char) : Nat :="
  , "  let n := c.toNat"
  , "  if n >= 97 then n - 61"
  , "  else if n >= 65 then n - 55"
  , "  else if n >= 48 then n - 48"
  , "  else if n == 43 then 62 else 63"
  , ""
  , "@[expose] def _rNatAux (acc : Nat) : List Char → Nat × List Char"
  , "  | [] => (acc, [])"
  , "  | c :: cs =>"
  , "    let v := _d64 c; let acc' := acc * 32 + v % 32"
  , "    if v >= 32 then _rNatAux acc' cs else (acc', cs)"
  , ""
  , "@[expose] def _rNat (cs : List Char) : Nat × List Char := _rNatAux 0 cs"
  , ""
  , "@[expose] def _rList {α : Type} (f : List Char → α × List Char) :"
  , "    Nat → List Char → List α × List Char"
  , "  | 0, cs => ([], cs)"
  , "  | n + 1, cs =>"
  , "    let (x, cs1) := f cs; let (xs, cs2) := _rList f n cs1; (x :: xs, cs2)"
  , ""
  , "@[expose] def _rDeltas {α : Type} (f : List Char → α × List Char) :"
  , "    Nat → Bool → Nat → List Char → List (Nat × α) × List Char"
  , "  | 0, _, _, cs => ([], cs)"
  , "  | n + 1, isF, prev, cs =>"
  , "    let (d, cs1) := _rNat cs"
  , "    let k := if isF then d else prev + 1 + d"
  , "    let (v, cs2) := f cs1"
  , "    let (rest, cs3) := _rDeltas f n false k cs2"
  , "    ((k, v) :: rest, cs3)"
  , ""
  , "@[expose] def _rTrie {α : Type} (f : List Char → α × List Char)"
  , "    (cs : List Char) : Trie α × List Char :="
  , "  let (n, cs1) := _rNat cs"
  , "  let (ps, cs2) := _rDeltas f n true 0 cs1"
  , "  (ps.foldl (fun t (k, v) => t.insert k v) .empty, cs2)"
  , ""
  , "@[expose] def _rTrieOpt {α : Type} (f : List Char → Option α × List Char)"
  , "    (cs : List Char) : Trie α × List Char :="
  , "  let (n, cs1) := _rNat cs"
  , "  let (ps, cs2) := _rDeltas f n true 0 cs1"
  , "  (ps.foldl (fun t (k, vo) => match vo with | some v => t.insert k v | none => t) .empty,"
  , "    cs2)"
  , ""
  , "@[expose] def _mkBTGo (i t f : Nat) (acc : Trie Bool) : Trie Bool :="
  , "  if h : t = 0 ∧ f = 0 then acc"
  , "  else"
  , "    let acc' := if t % 2 == 1 then acc.insert i true"
  , "      else if f % 2 == 1 then acc.insert i false else acc"
  , "    _mkBTGo (i + 1) (t / 2) (f / 2) acc'"
  , "termination_by t + f"
  , ""
  , "@[expose] def _rBTrie (cs : List Char) : Trie Bool × List Char :="
  , "  let (tm, cs1) := _rNat cs; let (fm, cs2) := _rNat cs1"
  , "  (_mkBTGo 0 tm fm .empty, cs2)"
  , ""
  , "@[expose] def _rBoolsAux : Nat → Nat → List Bool"
  , "  | 0, _ => []"
  , "  | n + 1, m => (m % 2 == 1) :: _rBoolsAux n (m / 2)"
  , ""
  , "@[expose] def _rBools (cs : List Char) : List Bool × List Char :="
  , "  let (n, cs1) := _rNat cs; let (m, cs2) := _rNat cs1"
  , "  (_rBoolsAux n m, cs2)"
  , ""
  , "@[expose] def _sw : Nat → SlotWidth"
  , "  | 0 => .w64 | 1 => .w128 | 2 => .w256 | _ => .w512"
  , ""
  , "@[expose] def _rSymArg (cs : List Char) : SymArg × List Char :="
  , "  let (t, cs1) := _rNat cs"
  , "  match t with"
  , "  | 0 => (.immBool false, cs1)"
  , "  | 1 => (.immBool true, cs1)"
  , "  | 2 => let (w, c2) := _rNat cs1; let (c, c3) := _rNat c2"
  , "    (.immBits w (BitVec.ofNat 64 c), c3)"
  , "  | 3 => let (w, c2) := _rNat cs1; let (c, c3) := _rNat c2"
  , "    (.immVec (_sw w) (BitVec.ofNat 512 c), c3)"
  , "  | k + 4 => (.var k, cs1)"
  , ""
  , s!"@[expose] def _rLoc (cs : List Char) : Option (Loc {isaExpr}.Reg {isaExpr}.VReg"
  , s!"    {isaExpr}.Cond) × List Char :="
  , "  let (i, cs1) := _rNat cs; (_locs[i]?, cs1)"
  , ""
  , s!"@[expose] def _rMove (cs : List Char) : Option (Move {isaExpr}.Reg {isaExpr}.VReg"
  , s!"    {isaExpr}.Cond) × List Char :="
  , "  let (t, cs1) := _rNat cs"
  , "  match t with"
  , "  | 0 => let (d, c2) := _rNat cs1; let (s, c3) := _rNat c2"
  , "    ((_regs[d]?.bind fun dr => _regs[s]?.map (.mov dr ·)), c3)"
  , "  | 1 => let (d, c2) := _rNat cs1; let (c, c3) := _rNat c2"
  , "    (_regs[d]?.map (.movi · (BitVec.ofNat 64 c)), c3)"
  , "  | 2 => let (d, c2) := _rNat cs1; let (i, c3) := _rNat c2"
  , "    (_regs[d]?.map (.ld · i), c3)"
  , "  | 3 => let (i, c2) := _rNat cs1; let (s, c3) := _rNat c2"
  , "    (_regs[s]?.map (.st i ·), c3)"
  , "  | 4 => let (d, c2) := _rNat cs1; let (c, c3) := _rNat c2"
  , "    ((_regs[d]?.bind fun dr => _conds[c]?.map (.setcc dr ·)), c3)"
  , "  | 5 => let (w, c2) := _rNat cs1; let (d, c3) := _rNat c2; let (s, c4) := _rNat c3"
  , "    ((_vregs[d]?.bind fun dv => _vregs[s]?.map (.vmov (_sw w) dv ·)), c4)"
  , "  | 6 => let (w, c2) := _rNat cs1; let (d, c3) := _rNat c2; let (c, c4) := _rNat c3"
  , "    (_vregs[d]?.map (.vmovi (_sw w) · (BitVec.ofNat 512 c)), c4)"
  , "  | 7 => let (w, c2) := _rNat cs1; let (d, c3) := _rNat c2; let (i, c4) := _rNat c3"
  , "    (_vregs[d]?.map (.vld (_sw w) · i), c4)"
  , "  | _ => let (w, c2) := _rNat cs1; let (i, c3) := _rNat c2; let (s, c4) := _rNat c3"
  , "    (_vregs[s]?.map (.vst (_sw w) i ·), c4)"
  , ""
  , s!"@[expose] def _rEntry (cs : List Char) : Entry {isaExpr}.Reg {isaExpr}.VReg"
  , s!"    {isaExpr}.Cond × List Char :="
  , "  let (nl, c1) := _rNat cs"
  , "  let (lv, c2) := _rList (fun s => let (sa, s1) := _rSymArg s"
  , "    let (lo, s2) := _rLoc s1; (lo.map (sa, ·), s2)) nl c1"
  , "  let (np, c3) := _rNat c2"
  , "  let (pl, c4) := _rList _rLoc np c3"
  , "  let (lz, c5) := _rBools c4; let (pz, c6) := _rBools c5"
  , "  ({ live := lv.filterMap id, ploc := pl.filterMap id, liveZ := lz, plocZ := pz }, c6)"
  , ""
  , s!"@[expose] def _rPre (cs : List Char) : PreStep {isaExpr}.Reg {isaExpr}.VReg"
  , s!"    {isaExpr}.Cond × List Char :="
  , "  let (pk, c1) := _rNat cs"
  , "  let (ms, c2) := _rList _rMove (pk / 2) c1"
  , "  ({ clearFlags := pk % 2 == 1, moves := ms.filterMap id }, c2)"
  , ""
  , "@[expose] def _rVar (cs : List Char) : VariantHint × List Char :="
  , "  let (t, c1) := _rNat cs"
  , "  match t with"
  , "  | 0 => (.default, c1) | 1 => (.adcx, c1) | 2 => (.adox, c1)"
  , "  | 3 => (.mulxFast, c1) | 4 => (.decInc, c1)"
  , "  | _ => let (o, c2) := _rNat c1; (.disp (Int64.ofBitVec (BitVec.ofNat 64 o)), c2)"
  , ""
  , s!"@[expose] def _decH (chunks : Array String) : {isaExpr}.Hints :="
  , "  let cs := (chunks.foldl (· ++ ·) \"\").toList"
  , "  let (dt, c1) := _rTrieOpt _rLoc cs"
  , "  let (et, c2) := _rTrie _rEntry c1"
  , "  let (pt, c3) := _rTrie _rPre c2"
  , "  let (vt, c4) := _rTrie _rVar c3"
  , "  let (el, c5) := _rBTrie c4; let (ij, c6) := _rBTrie c5"
  , "  let (dj, c7) := _rBTrie c6; let (dl, c8) := _rBTrie c7"
  , "  let (df, c9) := _rBTrie c8; let (mh, c10) := _rBTrie c9"
  , "  let (ns, c11) := _rNat c10; let (sn, c12) := _rNat c11"
  , "  let (sv, _) := _rList (fun s => let (i, s1) := _rNat s; (_regs[i]?, s1)) sn c12"
  , "  { dest := dt, entry := et, pre := pt, variant := vt, elide := el, invertJnz := ij"
  , "    deferJnz := dj, deferLea := dl, deadFlags := df, mulHiIps := mh"
  , "    nslots := ns, saved := sv.filterMap id }" ]

private def pruneExt (callees : List SigEntry)
    (acc : List (SigEntry × Nat)) : List (SigEntry × Nat) :=
  let uniq := callees.foldl (fun seen g =>
    if seen.any (SigEntry.beq · g) then seen else g :: seen) [] |>.reverse
  uniq.filterMap fun g => (lookupBound acc g).map fun b => (g, b)

/-! ## 3. Per-Subsystem Plan, Exports, and Arch Oracle Generators -/

/-- Compute full `InlPlan` from `policy`, split by subsystem, and derive exact DAG deps and
minimal cross-subsystem `Exports`. -/
def computeSegPlans (policy : InlinePolicy) (segs : List SegInput)
    (externs : List Extern := []) (exits : List Sym := []) :
    InlPlan × List SegPlanInfo :=
  let fullMod : Module := { fns := segs.flatMap (·.fns), externs := externs, exits := exits }
  let fullPlan := policyToInlPlan policy fullMod
  let inlFull := inlineFnsPlan fullPlan [] fullMod.fns
  let flatFull := inlFull.map fun fn => ⟨fn.name, fn.as, fn.rs, reifyFunc fn.body⟩
  let rec split (ownerMap : List (Sym × String)) (remFlats : List TFlatFn) :
      List SegInput → List SegPlanInfo
    | [] => []
    | s :: rest =>
      let n := s.fns.length
      let sFlats := remFlats.take n
      let sNames := s.fns.map Fn.name
      let sPlan := fullPlan.filter fun (caller, _) => sNames.contains caller
      let sTargets := sPlan.flatMap Prod.snd
      let deps := sTargets.foldl (fun acc callee =>
        match ownerMap.find? (fun p => p.1 == callee) with
        | some (_, owner) =>
          if owner == s.name || acc.contains owner then acc else acc ++ [owner]
        | none => acc) []
      let expNames := planExportsFor fullPlan sNames
      let ownerMap' := ownerMap ++ sNames.map fun nm => (nm, s.name)
      { seg := s, plan := sPlan, deps := deps, exportNames := expNames,
        inlinedFlats := sFlats } :: split ownerMap' (remFlats.drop n) rest
  (fullPlan, split [] flatFull segs)

/-- Render `<Base>/Oracle/<S>.lean` carrying `def plan : InlPlan`. -/
def renderPlanOracleLean (modNs : String) (segPlan : InlPlan) : String :=
  let nPlan := segPlan.length
  let entries := segPlan.zipIdx.map fun ((caller, callees), i) =>
    let comma := if i + 1 < nPlan then "," else ""
    let cs := "[" ++ String.intercalate ", " (callees.map fmtStr) ++ "]"
    let one := "  (" ++ fmtStr caller ++ ", " ++ cs ++ ")" ++ comma
    if one.length <= maxCol then [one]
    else fmtListLines ("  (" ++ fmtStr caller ++ ", ") (")" ++ comma) "    " (callees.map fmtStr)
  let planLines :=
    if segPlan.isEmpty then ["@[expose] def plan : InlPlan := []"]
    else
      let singleElems := segPlan.map fun (caller, callees) =>
        "(" ++ fmtStr caller ++ ", [" ++ String.intercalate ", " (callees.map fmtStr) ++ "])"
      let one := "@[expose] def plan : InlPlan := [" ++ String.intercalate ", " singleElems ++ "]"
      if one.length <= maxCol then [one]
      else ["@[expose] def plan : InlPlan := ["] ++ entries.flatten ++ ["]"]
  String.intercalate "\n" <|
    [ "module"
    , ""
    , "public import LeanQbe.T.InlinePlan"
    , ""
    , "set_option autoImplicit false"
    , ""
    , "public section"
    , ""
    , s!"namespace {modNs}"
    , ""
    , "open LeanQbe.T"
    , "" ] ++
    planLines ++
    [ ""
    , s!"end {modNs}"
    , "" ]

/-- Render pure data leaf `<Base>/Inl/<S>/Exports.lean` (zero import of `Src` or `Inl`). -/
def renderExportsLean (modNs : String) (expFlats : List TFlatFn) : String :=
  let defs := expFlats.zipIdx.flatMap fun (tf, i) =>
    fmtTFlatFnDef i tf ++ [""]
  let fnElems := (List.range expFlats.length).map fun i => s!"flat{i}.toFn"
  let fnsLines := fmtListLines "@[expose] def fns : List Fn := " "" "  " fnElems
  String.intercalate "\n" <|
    [ "module"
    , ""
    , "public import LeanQbe.T.Flat"
    , "public import LeanQbe.T.Module"
    , ""
    , "set_option autoImplicit false"
    , ""
    , "public section"
    , ""
    , s!"namespace {modNs}"
    , ""
    , "open LeanQbe.T"
    , "" ] ++
    defs ++
    fnsLines ++
    [ ""
    , s!"end {modNs}"
    , "" ]

/-- Compute oracle hints + pruned `ext` for one subsystem on target `(I, lt)`, returning
`(leanSource, nextExtAcc, perFnNameBoundSize)`. -/
def renderArchOracleLean (I : Isa) (fR : I.Reg → String) (fV : I.VReg → String)
    (fC : I.Cond → String) (lt : LegalTarget) (isaMod archNs isaExpr modNs : String)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX maxBound : Nat)
    (segFlats : List TFlatFn) :
    IO (String × List (SigEntry × Nat) × List (Sym × Nat × Nat)) := do
  let mut acc := ext0
  let mut hintsRev : List (Sym × I.Hints × List (SigEntry × Nat)) := []
  let mut allCallees : List SigEntry := []
  let mut metricsRev : List (Sym × Nat × Nat) := []
  let mut tbl : OracleSymTables := {}
  for f in segFlats do
    if !f.wfCheck then
      throw <| IO.userError s!"[SegCertOracle] {f.name}: flat wfCheck failed"
    let ef := earlyOptFlat f
    if !ef.supportsSource lt then
      throw <| IO.userError s!"[SegCertOracle] {f.name}: unsupported source op"
    let mf := midStageFlat lt ef
    let ext := TFlat.ext mf.body
    let h := Spill.hints I mf.toFn
    match checkAndBoundExt I I.frame.raBytes exits nX acc h ext with
    | none => throw <| IO.userError s!"[SegCertOracle] {f.name}: checkAndBoundExt failed"
    | some b =>
      if b > maxBound then
        throw <| IO.userError s!"[SegCertOracle] {f.name}: bound {b} > maxBound {maxBound}"
      let fnExt := pruneExt ext.callees acc
      allCallees := allCallees ++ ext.callees
      tbl := internHintsSyms fR fV fC tbl h
      hintsRev := (f.name, h, fnExt) :: hintsRev
      metricsRev := (f.name, b, tflatSize mf.body) :: metricsRev
      acc := (mf.sig, b) :: acc
  let items := hintsRev.reverse
  let segExt := pruneExt allCallees ext0
  let arrLines (nm ty : String) (xs : Array String) : List String :=
    if xs.isEmpty then [s!"@[expose] def {nm} : Array {ty} := #[]"]
    else
      let one := s!"@[expose] def {nm} : Array {ty} := #[" ++
        String.intercalate ", " xs.toList ++ "]"
      if one.length <= maxCol then [one]
      else [s!"@[expose] def {nm} : Array {ty} := #["] ++
        packLines "  " "]" "  " xs.toList
  let tblLines :=
    arrLines "_regs" s!"{isaExpr}.Reg" tbl.regs ++
    arrLines "_vregs" s!"{isaExpr}.VReg" tbl.vregs ++
    arrLines "_conds" s!"{isaExpr}.Cond" tbl.conds ++
    arrLines "_locs" s!"(Loc {isaExpr}.Reg {isaExpr}.VReg {isaExpr}.Cond)" tbl.locs
  let perFnDefs := items.flatMap fun (nm, h, fnExt) =>
    let stream := encHintsStream fR fV fC tbl h
    let chunks := chunkString 86 stream
    let quoted := chunks.map fmtStr
    let hOne := s!"@[expose] def hint_{nm} : {isaExpr}.Hints := _decH #[" ++
      String.intercalate ", " quoted ++ "]"
    let hLines :=
      if quoted.length <= 1 && hOne.length <= maxCol then [hOne]
      else
        [s!"@[expose] def hint_{nm} : {isaExpr}.Hints := _decH #["] ++
          packLines "  " "]" "  " quoted
    let extPfx := s!"@[expose] def ext_{nm} : List (SigEntry × Nat) :="
    let eLines := fmtExtListLines extPfx "" "  " fnExt
    hLines ++ eLines ++ [""]
  let hintNames := items.map fun (nm, _, _) => s!"hint_{nm}"
  let hintsPfx := s!"@[expose] def hints : List {isaExpr}.Hints := "
  let hintsLines := fmtListLines hintsPfx "" "  " hintNames
  let segExtLines :=
    fmtExtListLines "@[expose] def ext : List (SigEntry × Nat) :=" "" "  " segExt
  let src := String.intercalate "\n" <|
    [ "module"
    , ""
    , "public import LeanQbe.T.Main"
    , s!"public import {isaMod}"
    , ""
    , "set_option autoImplicit false"
    , ""
    , "public section"
    , ""
    , s!"namespace {modNs}"
    , ""
    , s!"open LeanQbe.T {archNs}"
    , "" ] ++
    tblLines ++ [""] ++
    decoderHelperLines isaExpr ++ [""] ++
    perFnDefs ++
    hintsLines ++ [""] ++
    segExtLines ++
    [ ""
    , s!"end {modNs}"
    , "" ]
  pure (src, acc, metricsRev.reverse)

/-- Format per-function `{name, bound, flat_size}` JSON for `gen_build_segs.py --profile`. -/
def formatProfileJson (rows : List (Sym × Nat × Nat)) : String :=
  let objs := rows.map fun (nm, b, sz) =>
    s!"  \{\"name\": \"{nm}\", \"bound\": {b}, \"flat_size\": {sz}}"
  "[\n" ++ String.intercalate ",\n" objs ++ "\n]\n"

/-- Format a JSON manifest consumed directly by `scripts/gen_build_segs.py --manifest`. -/
def formatManifestJson (baseNs srcFullMod srcFullModSym : String)
    (infos : List SegPlanInfo) : String :=
  let q := fun (s : String) => "\"" ++ s ++ "\""
  let qList := fun (xs : List String) => "[" ++ String.intercalate ", " (xs.map q) ++ "]"
  let segObjs := infos.map fun info =>
    let fnNames := info.seg.fns.map Fn.name
    "    {" ++
    s!"\"name\": {q info.seg.name}, \"src_mod\": {q info.seg.srcMod}, " ++
    s!"\"src_fns\": {q info.seg.srcFns}, \"fns\": {qList fnNames}, " ++
    s!"\"deps\": {qList info.deps}, \"exports\": {qList info.exportNames}" ++
    "}"
  "{\n" ++
  s!"  \"base_ns\": {q baseNs},\n" ++
  s!"  \"src_full_mod\": {q srcFullMod},\n" ++
  s!"  \"src_full_mod_sym\": {q srcFullModSym},\n" ++
  "  \"segs\": [\n" ++
  String.intercalate ",\n" segObjs ++
  "\n  ]\n}\n"

end LeanQbeTest.T.SegCertOracle
