module

public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
public import Std.Data.HashMap

/-!
# `BVP1` Bytecode Specification and Kernel-Fast Word Parser (`Bitblast.Ref.BVProg`)

Defines the `BVP1` 32-bit-word bytecode format for unrestricted `Std.Tactic.BVDecide.BVLogicalExpr`:
- `BVProg.wordsToBytesLE` and `BVProg.bytesToWordsLE`
- `BVProg.BinTree`: structurally recursive `O(log N)` binary-digit map for fast kernel reduction
- `BVProg.parseWords` (`List Nat -> Option BVLogicalExpr`) and `BVProg.parse` (`List UInt8`)
- Zero-axiom bridge `BVProg.parse_wordsToBytesLE` and `BVProg.unsat_of_bv_solve_words`
- Untrusted DAG-sharing encoder `BVProg.encode : BVLogicalExpr -> Option (List Nat)`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Bitblast.Ref.BVProg

open Std.Tactic.BVDecide

/-! ## 1. `BVP1` Format Constants and Opcodes -/

/-- `BVP1` magic word (`"BVP1"` little-endian = `0x31505642`). -/
@[expose] def bvpMagic : Nat := 0x31505642

/-- `BVP1` format version (`1`). -/
@[expose] def bvpVersion : Nat := 1

/-- Exclusive upper bound on 32-bit unsigned words (`2^32`). -/
@[expose] def u32Bound : Nat := 4294967296

/-- `BVP1` opcode tags for `BVExpr`, `BVPred`, and `BVLogicalExpr`. -/
@[expose] def opVar : Nat := 0
@[expose] def opConst : Nat := 1
@[expose] def opExtract : Nat := 2
@[expose] def opAnd : Nat := 3
@[expose] def opOr : Nat := 4
@[expose] def opXor : Nat := 5
@[expose] def opAdd : Nat := 6
@[expose] def opMul : Nat := 7
@[expose] def opUdiv : Nat := 8
@[expose] def opUmod : Nat := 9
@[expose] def opNot : Nat := 10
@[expose] def opRotL : Nat := 11
@[expose] def opRotR : Nat := 12
@[expose] def opAshrC : Nat := 13
@[expose] def opReverse : Nat := 14
@[expose] def opClz : Nat := 15
@[expose] def opCpop : Nat := 16
@[expose] def opAppend : Nat := 17
@[expose] def opReplicate : Nat := 18
@[expose] def opShl : Nat := 19
@[expose] def opUshr : Nat := 20
@[expose] def opAshr : Nat := 21
@[expose] def opEq : Nat := 22
@[expose] def opUlt : Nat := 23
@[expose] def opGetLsbD : Nat := 24
@[expose] def opBConst : Nat := 25
@[expose] def opBNot : Nat := 26
@[expose] def opGateAnd : Nat := 27
@[expose] def opGateXor : Nat := 28
@[expose] def opGateBeq : Nat := 29
@[expose] def opGateOr : Nat := 30
@[expose] def opIte : Nat := 31

/-! ## 2. Little-Endian 32-Bit Word <-> Byte Encoding -/

/-- Canonical little-endian byte stream of a `BVP1` 32-bit word list (4 bytes per word). -/
@[expose] def wordsToBytesLE : List Nat → List UInt8
  | [] => []
  | w :: ws =>
    (w % 256).toUInt8 :: ((w / 256) % 256).toUInt8 ::
    ((w / 65536) % 256).toUInt8 :: ((w / 16777216) % 256).toUInt8 ::
    wordsToBytesLE ws

/-- Decode 4 little-endian bytes into a 32-bit `Nat`. -/
@[expose] def u32OfBytesLE (b0 b1 b2 b3 : UInt8) : Nat :=
  b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat))

/-- Decode a little-endian byte stream into 32-bit `Nat` words (requires length `≡ 0 (mod 4)`). -/
@[expose] def bytesToWordsLE : List UInt8 → Option (List Nat)
  | [] => some []
  | b0 :: b1 :: b2 :: b3 :: rest =>
    match bytesToWordsLE rest with
    | some ws => some (u32OfBytesLE b0 b1 b2 b3 :: ws)
    | none => none
  | _ => none

/-! ## 3. Structurally Recursive `O(log N)` 4-Way Radix Tree (`RadixTree` / `BinTree`) -/

/-- 4-way radix tree indexed by `idx : Nat` using base-4 digits (`idx % 4`, `idx / 4`).
Uses structural recursion on `fuel : Nat` (`fuel = 16` covers all `idx < 2^32`) and `Nat.beq`/
`Nat.blt`/`match` so kernel reduction avoids `WellFounded.fix` and `Decidable` proof wrappers. -/
inductive RadixTree (α : Type) where
  | empty
  | node (val : Option α) (c0 c1 c2 c3 : RadixTree α)

/-- Alias for compatibility with `bv_decide_v1_next_steps_plan.md` naming. -/
abbrev BinTree := RadixTree

/-- Structurally recursive 4-way lookup bounded by `fuel`. -/
@[expose] def RadixTree.getAux {α : Type} : Nat → RadixTree α → Nat → Option α
  | _, .empty, _ => none
  | 0, .node v _ _ _ _, _ => v
  | fuel + 1, .node v c0 c1 c2 c3, idx =>
    match Nat.beq idx 0 with
    | true => v
    | false =>
      let r := idx % 4
      let q := idx / 4
      match Nat.blt r 2 with
      | true =>
        match Nat.beq r 0 with
        | true => RadixTree.getAux fuel c0 q
        | false => RadixTree.getAux fuel c1 q
      | false =>
        match Nat.beq r 2 with
        | true => RadixTree.getAux fuel c2 q
        | false => RadixTree.getAux fuel c3 q

/-- Lookup `idx < 2^32` in `t`. -/
@[expose] def RadixTree.get? {α : Type} (t : RadixTree α) (idx : Nat) : Option α :=
  RadixTree.getAux 16 t idx

/-- Structurally recursive 4-way insertion bounded by `fuel`. -/
@[expose] def RadixTree.insertAux {α : Type} :
    Nat → RadixTree α → Nat → α → RadixTree α
  | 0, .empty, _, x => .node (some x) .empty .empty .empty .empty
  | 0, .node _ c0 c1 c2 c3, _, x => .node (some x) c0 c1 c2 c3
  | fuel + 1, .empty, idx, x =>
    match Nat.beq idx 0 with
    | true => .node (some x) .empty .empty .empty .empty
    | false =>
      let r := idx % 4
      let q := idx / 4
      let sub := RadixTree.insertAux fuel .empty q x
      match Nat.blt r 2 with
      | true =>
        match Nat.beq r 0 with
        | true => .node none sub .empty .empty .empty
        | false => .node none .empty sub .empty .empty
      | false =>
        match Nat.beq r 2 with
        | true => .node none .empty .empty sub .empty
        | false => .node none .empty .empty .empty sub
  | fuel + 1, .node v c0 c1 c2 c3, idx, x =>
    match Nat.beq idx 0 with
    | true => .node (some x) c0 c1 c2 c3
    | false =>
      let r := idx % 4
      let q := idx / 4
      match Nat.blt r 2 with
      | true =>
        match Nat.beq r 0 with
        | true => .node v (RadixTree.insertAux fuel c0 q x) c1 c2 c3
        | false => .node v c0 (RadixTree.insertAux fuel c1 q x) c2 c3
      | false =>
        match Nat.beq r 2 with
        | true => .node v c0 c1 (RadixTree.insertAux fuel c2 q x) c3
        | false => .node v c0 c1 c2 (RadixTree.insertAux fuel c3 q x)

/-- Insert `(idx, x)` into `t` for `idx < 2^32`. -/
@[expose] def RadixTree.insert {α : Type} (t : RadixTree α) (idx : Nat) (x : α) :
    RadixTree α :=
  RadixTree.insertAux 16 t idx x

/-! ## 4. Kernel-Fast `BVProg.parseWords` and `BVProg.parse` -/

/-- Variable table entry `{u32 bv_idx, u32 width}`. -/
structure VarEntry where
  bvIdx : Nat
  width : Nat

/-- Parsed DAG node in the unified `BVP1` node space. -/
inductive ProgNode where
  | bv (w : Nat) (expr : BVExpr w)
  | bool (expr : BVLogicalExpr)

/-- Check `x < 2^32`. -/
@[expose] def isU32 (x : Nat) : Bool :=
  Nat.blt x u32Bound

/-- Parse `n` `{bvIdx, width}` pairs into a `BinTree VarEntry`, validating `< 2^32`. -/
@[expose] def parseVars :
    Nat → Nat → BinTree VarEntry → List Nat → Option (BinTree VarEntry × List Nat)
  | 0, _, acc, ws => some (acc, ws)
  | n + 1, idx, acc, bvIdx :: width :: rest =>
    match isU32 bvIdx && isU32 width with
    | true => parseVars n (idx + 1) (acc.insert idx ⟨bvIdx, width⟩) rest
    | false => none
  | _ + 1, _, _, _ => none

/-- Parse `n` constant-pool words into a `BinTree Nat`, validating `< 2^32`. -/
@[expose] def parseCwords :
    Nat → Nat → BinTree Nat → List Nat → Option (BinTree Nat × List Nat)
  | 0, _, acc, ws => some (acc, ws)
  | n + 1, idx, acc, cw :: rest =>
    match isU32 cw with
    | true => parseCwords n (idx + 1) (acc.insert idx cw) rest
    | false => none
  | _ + 1, _, _, [] => none

/-- Fold `nw` LSB-first 32-bit words starting at `base` in `cwords` into a GMP `Nat`. -/
@[expose] def readConstNatAux (cwords : BinTree Nat) (base : Nat) : Nat → Nat → Option Nat
  | 0, acc => some acc
  | k + 1, acc =>
    match cwords.get? (base + k) with
    | some w => readConstNatAux cwords base k (acc * u32Bound + w)
    | none => none

/-- Parse a `BVExpr.bin` node whose operand widths must both equal `w`. -/
@[expose] def mkBvBin (nodes : BinTree ProgNode) (w a b : Nat) (bop : BVBinOp) :
    Option ProgNode :=
  match nodes.get? a, nodes.get? b with
  | some (.bv lw lhs), some (.bv rw rhs) =>
    if hl : lw = w then
      if hr : rw = w then
        some (.bv w (.bin (hl ▸ lhs) bop (hr ▸ rhs)))
      else none
    else none
  | _, _ => none

/-- Parse a `BVExpr.un` node whose operand width must equal `w`. -/
@[expose] def mkBvUn (nodes : BinTree ProgNode) (w a : Nat) (uop : BVUnOp) : Option ProgNode :=
  match nodes.get? a with
  | some (.bv ew e) =>
    if h : ew = w then some (.bv w (.un uop (h ▸ e))) else none
  | _ => none

/-- Parse a binary `BVPred` (`eq`/`ult`) node with `w = 1`. -/
@[expose] def mkPredBin (nodes : BinTree ProgNode) (w a b : Nat) (pred : BVBinPred) :
    Option ProgNode :=
  match Nat.beq w 1 with
  | true =>
    match nodes.get? a, nodes.get? b with
    | some (.bv lw lhs), some (.bv rw rhs) =>
      if h : rw = lw then some (.bool (.literal (.bin lhs pred (h ▸ rhs)))) else none
    | _, _ => none
  | false => none

/-- Parse a `BVLogicalExpr.gate` node with `w = 1`. -/
@[expose] def mkGateNode (nodes : BinTree ProgNode) (w a b : Nat) (g : Gate) : Option ProgNode :=
  match Nat.beq w 1 with
  | true =>
    match nodes.get? a, nodes.get? b with
    | some (.bool lhs), some (.bool rhs) => some (.bool (.gate g lhs rhs))
    | _, _ => none
  | false => none

/-- Decode a single `{op, w, a, b, c}` node entry via 5-level binary dispatch on `op`. -/
@[expose] def decodeNode (vars : BinTree VarEntry) (cwords : BinTree Nat)
    (nodes : BinTree ProgNode) (op w a b c : Nat) : Option ProgNode :=
  match Nat.blt op 16 with
  | true =>
    match Nat.blt op 8 with
    | true =>
      match Nat.blt op 4 with
      | true =>
        match Nat.blt op 2 with
        | true =>
          match Nat.beq op 0 with
          | true =>
            match vars.get? a with
            | some ve =>
              match Nat.beq ve.width w with
              | true => some (.bv w (.var ve.bvIdx))
              | false => none
            | none => none
          | false =>
            let nw := (w + 31) / 32
            match readConstNatAux cwords a nw 0 with
            | some val => some (.bv w (.const (BitVec.ofNat w val)))
            | none => none
        | false =>
          match Nat.beq op 2 with
          | true =>
            match nodes.get? b with
            | some (.bv _ e) => some (.bv w (.extract a w e))
            | _ => none
          | false => mkBvBin nodes w a b .and
      | false =>
        match Nat.blt op 6 with
        | true =>
          match Nat.beq op 4 with
          | true => mkBvBin nodes w a b .or
          | false => mkBvBin nodes w a b .xor
        | false =>
          match Nat.beq op 6 with
          | true => mkBvBin nodes w a b .add
          | false => mkBvBin nodes w a b .mul
    | false =>
      match Nat.blt op 12 with
      | true =>
        match Nat.blt op 10 with
        | true =>
          match Nat.beq op 8 with
          | true => mkBvBin nodes w a b .udiv
          | false => mkBvBin nodes w a b .umod
        | false =>
          match Nat.beq op 10 with
          | true => mkBvUn nodes w a .not
          | false => mkBvUn nodes w a (.rotateLeft b)
      | false =>
        match Nat.blt op 14 with
        | true =>
          match Nat.beq op 12 with
          | true => mkBvUn nodes w a (.rotateRight b)
          | false => mkBvUn nodes w a (.arithShiftRightConst b)
        | false =>
          match Nat.beq op 14 with
          | true => mkBvUn nodes w a .reverse
          | false => mkBvUn nodes w a .clz
  | false =>
    match Nat.blt op 24 with
    | true =>
      match Nat.blt op 20 with
      | true =>
        match Nat.blt op 18 with
        | true =>
          match Nat.beq op 16 with
          | true => mkBvUn nodes w a .cpop
          | false =>
            match nodes.get? a, nodes.get? b with
            | some (.bv _ lhs), some (.bv _ rhs) =>
              if h : w = _ + _ then some (.bv w (.append lhs rhs h)) else none
            | _, _ => none
        | false =>
          match Nat.beq op 18 with
          | true =>
            match nodes.get? a with
            | some (.bv ew e) =>
              if h : w = ew * b then some (.bv w (.replicate b e h)) else none
            | _ => none
          | false =>
            match nodes.get? a, nodes.get? b with
            | some (.bv lw lhs), some (.bv _ rhs) =>
              if h : lw = w then some (.bv w (.shiftLeft (h ▸ lhs) rhs)) else none
            | _, _ => none
      | false =>
        match Nat.blt op 22 with
        | true =>
          match Nat.beq op 20 with
          | true =>
            match nodes.get? a, nodes.get? b with
            | some (.bv lw lhs), some (.bv _ rhs) =>
              if h : lw = w then some (.bv w (.shiftRight (h ▸ lhs) rhs)) else none
            | _, _ => none
          | false =>
            match nodes.get? a, nodes.get? b with
            | some (.bv lw lhs), some (.bv _ rhs) =>
              if h : lw = w then some (.bv w (.arithShiftRight (h ▸ lhs) rhs)) else none
            | _, _ => none
        | false =>
          match Nat.beq op 22 with
          | true => mkPredBin nodes w a b .eq
          | false => mkPredBin nodes w a b .ult
    | false =>
      match Nat.blt op 28 with
      | true =>
        match Nat.blt op 26 with
        | true =>
          match Nat.beq op 24 with
          | true =>
            match Nat.beq w 1 with
            | true =>
              match nodes.get? a with
              | some (.bv _ e) => some (.bool (.literal (.getLsbD e b)))
              | _ => none
            | false => none
          | false =>
            match Nat.beq w 1 && Nat.blt a 2 with
            | true => some (.bool (.const (Nat.beq a 1)))
            | false => none
        | false =>
          match Nat.beq op 26 with
          | true =>
            match Nat.beq w 1 with
            | true =>
              match nodes.get? a with
              | some (.bool x) => some (.bool (.not x))
              | _ => none
            | false => none
          | false => mkGateNode nodes w a b .and
      | false =>
        match Nat.blt op 32 with
        | true =>
          match Nat.blt op 30 with
          | true =>
            match Nat.beq op 28 with
            | true => mkGateNode nodes w a b .xor
            | false => mkGateNode nodes w a b .beq
          | false =>
            match Nat.beq op 30 with
            | true => mkGateNode nodes w a b .or
            | false =>
              match Nat.beq w 1 with
              | true =>
                match nodes.get? a, nodes.get? b, nodes.get? c with
                | some (.bool d), some (.bool l), some (.bool r) => some (.bool (.ite d l r))
                | _, _, _ => none
              | false => none
        | false => none

/-- Parse `n` 5-word node entries sequentially into `nodes`, validating `< 2^32`. -/
@[expose] def parseNodes (vars : BinTree VarEntry) (cwords : BinTree Nat) :
    Nat → Nat → BinTree ProgNode → List Nat → Option (BinTree ProgNode × List Nat)
  | 0, _, nodes, ws => some (nodes, ws)
  | n + 1, idx, nodes, op :: w :: a :: b :: c :: rest =>
    match isU32 op && isU32 w && isU32 a && isU32 b && isU32 c with
    | true =>
      match decodeNode vars cwords nodes op w a b c with
      | some node => parseNodes vars cwords n (idx + 1) (nodes.insert idx node) rest
      | none => none
    | false => none
  | _ + 1, _, _, _ => none

/-- Kernel-fast word-level `BVP1` parser over `List Nat` GMP literals. -/
@[expose] def parseWords : List Nat → Option BVLogicalExpr
  | magic :: ver :: nVars :: nNodes :: nCwords :: root :: r0 :: r1 :: rest =>
    match isU32 magic && isU32 ver && isU32 nVars && isU32 nNodes &&
          isU32 nCwords && isU32 root && isU32 r0 && isU32 r1 &&
          Nat.beq magic bvpMagic && Nat.beq ver bvpVersion &&
          Nat.blt 0 nNodes && Nat.blt root nNodes with
    | true =>
      match parseVars nVars 0 .empty rest with
      | some (vars, rest1) =>
        match parseCwords nCwords 0 .empty rest1 with
        | some (cwords, rest2) =>
          match parseNodes vars cwords nNodes 0 .empty rest2 with
          | some (nodes, []) =>
            match nodes.get? root with
            | some (.bool e) => some e
            | _ => none
          | _ => none
        | none => none
      | none => none
    | false => none
  | _ => none

/-- Canonical byte-level `BVP1` parser over `List UInt8`. -/
@[expose] def parse (bs : List UInt8) : Option BVLogicalExpr :=
  match bytesToWordsLE bs with
  | some ws => parseWords ws
  | none => none

/-! ## 5. Zero-Axiom Bridge Theorems (`parse_wordsToBytesLE`, `unsat_of_bv_solve_words`) -/

private def AllU32 (ws : List Nat) : Prop :=
  ∀ w ∈ ws, w < u32Bound

private theorem allU32_of_isU32_and {w : Nat} {ws : List Nat}
    (hw : isU32 w = true) (hws : AllU32 ws) : AllU32 (w :: ws) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact Nat.blt_eq.mp hw
  · exact hws x hx

private theorem parseVars_allU32 {n idx : Nat} {vars vars' : BinTree VarEntry}
    {ws rest : List Nat}
    (h : parseVars n idx vars ws = some (vars', rest))
    (hrest : AllU32 rest) : AllU32 ws := by
  induction n generalizing idx vars ws with
  | zero =>
    simp only [parseVars, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    exact hrest
  | succ n ih =>
    rcases ws with _ | ⟨bvIdx, _ | ⟨width, rest0⟩⟩
    · simp [parseVars] at h
    · simp [parseVars] at h
    · unfold parseVars at h
      split at h
      · rename_i hok
        simp only [Bool.and_eq_true] at hok
        exact allU32_of_isU32_and hok.1 (allU32_of_isU32_and hok.2 (ih h))
      · simp at h

private theorem parseCwords_allU32 {n idx : Nat} {cw cw' : BinTree Nat}
    {ws rest : List Nat}
    (h : parseCwords n idx cw ws = some (cw', rest))
    (hrest : AllU32 rest) : AllU32 ws := by
  induction n generalizing idx cw ws with
  | zero =>
    simp only [parseCwords, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    exact hrest
  | succ n ih =>
    rcases ws with _ | ⟨w, rest0⟩
    · simp [parseCwords] at h
    · unfold parseCwords at h
      split at h
      · rename_i hok
        exact allU32_of_isU32_and hok (ih h)
      · simp at h

private theorem parseNodes_allU32 {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {n idx : Nat} {nodes nodes' : BinTree ProgNode} {ws : List Nat}
    (h : parseNodes vars cwords n idx nodes ws = some (nodes', [])) : AllU32 ws := by
  induction n generalizing idx nodes ws with
  | zero =>
    simp only [parseNodes, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    intro x hx; cases hx
  | succ n ih =>
    rcases ws with _ | ⟨op, _ | ⟨w, _ | ⟨a, _ | ⟨b, _ | ⟨c, rest0⟩⟩⟩⟩⟩
    · simp [parseNodes] at h
    · simp [parseNodes] at h
    · simp [parseNodes] at h
    · simp [parseNodes] at h
    · simp [parseNodes] at h
    · unfold parseNodes at h
      split at h
      · rename_i hok
        simp only [Bool.and_eq_true] at hok
        split at h
        · exact allU32_of_isU32_and hok.1.1.1.1 (allU32_of_isU32_and hok.1.1.1.2
            (allU32_of_isU32_and hok.1.1.2 (allU32_of_isU32_and hok.1.2
              (allU32_of_isU32_and hok.2 (ih h)))))
        · simp at h
      · simp at h

private theorem parseWords_allU32 {ws : List Nat} {e : BVLogicalExpr}
    (h : parseWords ws = some e) : AllU32 ws := by
  rcases ws with _ | ⟨magic, _ | ⟨ver, _ | ⟨nVars, _ | ⟨nNodes, _ | ⟨nCwords,
      _ | ⟨root, _ | ⟨r0, _ | ⟨r1, rest⟩⟩⟩⟩⟩⟩⟩⟩
  · simp [parseWords] at h
  · simp [parseWords] at h
  · simp [parseWords] at h
  · simp [parseWords] at h
  · simp [parseWords] at h
  · simp [parseWords] at h
  · simp [parseWords] at h
  · simp [parseWords] at h
  · rw [parseWords] at h
    split at h
    · rename_i hhdr
      simp only [Bool.and_eq_true] at hhdr
      rcases hvars : parseVars nVars 0 .empty rest with _ | ⟨vars, rest1⟩
      · rw [hvars] at h; simp at h
      · rw [hvars] at h; dsimp only at h
        rcases hcws : parseCwords nCwords 0 .empty rest1 with _ | ⟨cwords, rest2⟩
        · rw [hcws] at h; simp at h
        · rw [hcws] at h; dsimp only at h
          rcases hnds : parseNodes vars cwords nNodes 0 .empty rest2 with _ | ⟨nodes, rest3⟩
          · rw [hnds] at h; simp at h
          · rw [hnds] at h
            rcases rest3 with _ | ⟨_, _⟩
            · have hall2 := parseNodes_allU32 hnds
              have hall1 := parseCwords_allU32 hcws hall2
              have hall0 := parseVars_allU32 hvars hall1
              exact allU32_of_isU32_and hhdr.1.1.1.1.1.1.1.1.1.1.1
                (allU32_of_isU32_and hhdr.1.1.1.1.1.1.1.1.1.1.2
                (allU32_of_isU32_and hhdr.1.1.1.1.1.1.1.1.1.2
                (allU32_of_isU32_and hhdr.1.1.1.1.1.1.1.1.2
                (allU32_of_isU32_and hhdr.1.1.1.1.1.1.1.2
                (allU32_of_isU32_and hhdr.1.1.1.1.1.1.2
                (allU32_of_isU32_and hhdr.1.1.1.1.1.2
                (allU32_of_isU32_and hhdr.1.1.1.1.2 hall0)))))))
            · simp at h
    · simp at h

private theorem u32OfBytesLE_word {w : Nat} (hw : w < u32Bound) :
    u32OfBytesLE (w % 256).toUInt8 ((w / 256) % 256).toUInt8
      ((w / 65536) % 256).toUInt8 ((w / 16777216) % 256).toUInt8 = w := by
  unfold u32OfBytesLE u32Bound at *
  simp only [Nat.toUInt8, UInt8.toNat_ofNat', Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 256)]
  have hb0 : w % 256 < 256 := Nat.mod_lt _ (by decide)
  have hb1 : (w / 256) % 256 < 256 := Nat.mod_lt _ (by decide)
  have hb2 : (w / 65536) % 256 < 256 := Nat.mod_lt _ (by decide)
  have hb3 : (w / 16777216) % 256 < 256 := Nat.mod_lt _ (by decide)
  omega

private theorem bytesToWordsLE_wordsToBytesLE {ws : List Nat} (h : AllU32 ws) :
    bytesToWordsLE (wordsToBytesLE ws) = some ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hw : w < u32Bound := h w (by simp)
    have hws : AllU32 ws := fun x hx => h x (by simp [hx])
    simp only [wordsToBytesLE, bytesToWordsLE, ih hws, u32OfBytesLE_word hw]

/-- Zero-axiom bridge: word-level `parseWords` refines byte-level `parse (wordsToBytesLE ws)`. -/
theorem parse_wordsToBytesLE {ws : List Nat} {e : BVLogicalExpr}
    (h : parseWords ws = some e) :
    parse (wordsToBytesLE ws) = some e := by
  unfold parse
  rw [bytesToWordsLE_wordsToBytesLE (parseWords_allU32 h)]
  exact h

/-- Alias matching `bv_decide_v1_next_steps_plan.md` §2.1. -/
theorem parse_of_words {ws : List Nat} {e : BVLogicalExpr}
    (h : parseWords ws = some e) :
    parse (wordsToBytesLE ws) = some e :=
  parse_wordsToBytesLE h

/-- Top-level zero-axiom reflection theorem closing `e.Unsat` from `bv_solve_bytes` (`<= std3`). -/
theorem unsat_of_bv_solve_words (ws : List Nat) (e : BVLogicalExpr)
    (hsolve : ∃ e', parse (wordsToBytesLE ws) = some e' ∧ e'.Unsat)
    (hparse : parseWords ws = some e) :
    e.Unsat := by
  obtain ⟨e', hp', hu⟩ := hsolve
  rw [parse_wordsToBytesLE hparse] at hp'
  cases hp'
  exact hu

/-! ## 6. Structural Equality Helpers (Outside `@[no_expose]` `decEq`) and Untrusted Encoder -/

/-- Structural `BVBinOp` equality. -/
@[expose] def binOpEq : BVBinOp → BVBinOp → Bool
  | .and, .and | .or, .or | .xor, .xor | .add, .add
  | .mul, .mul | .udiv, .udiv | .umod, .umod => true
  | _, _ => false

/-- Structural `BVUnOp` equality. -/
@[expose] def unOpEq : BVUnOp → BVUnOp → Bool
  | .not, .not | .reverse, .reverse | .clz, .clz | .cpop, .cpop => true
  | .rotateLeft a, .rotateLeft b => a == b
  | .rotateRight a, .rotateRight b => a == b
  | .arithShiftRightConst a, .arithShiftRightConst b => a == b
  | _, _ => false

/-- Structural `BVExpr` equality across potentially distinct width parameters. -/
@[expose] def bvExprHEq : {w1 w2 : Nat} → BVExpr w1 → BVExpr w2 → Bool
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

/-- Structural `BVPred` equality. -/
@[expose] def bvPredEq : BVPred → BVPred → Bool
  | .bin l1 .eq r1, .bin l2 .eq r2 => bvExprHEq l1 l2 && bvExprHEq r1 r2
  | .bin l1 .ult r1, .bin l2 .ult r2 => bvExprHEq l1 l2 && bvExprHEq r1 r2
  | .getLsbD e1 i1, .getLsbD e2 i2 => i1 == i2 && bvExprHEq e1 e2
  | _, _ => false

/-- Structural `Gate` equality. -/
@[expose] def gateEq : Gate → Gate → Bool
  | .and, .and | .xor, .xor | .beq, .beq | .or, .or => true
  | _, _ => false

/-- Structural `BVLogicalExpr` equality (kernel-reducible, independent of `@[no_expose]`
`decEq`). -/
@[expose] def logicalExprEq : BVLogicalExpr → BVLogicalExpr → Bool
  | .literal p1, .literal p2 => bvPredEq p1 p2
  | .const b1, .const b2 => b1 == b2
  | .not x1, .not x2 => logicalExprEq x1 x2
  | .gate g1 l1 r1, .gate g2 l2 r2 => gateEq g1 g2 && logicalExprEq l1 l2 && logicalExprEq r1 r2
  | .ite d1 l1 r1, .ite d2 l2 r2 =>
    logicalExprEq d1 d2 && logicalExprEq l1 l2 && logicalExprEq r1 r2
  | _, _ => false

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
  varMap : Std.HashMap (Nat × Nat) Nat := {}
  cwords : Array Nat := #[]
  nodes : Array (Nat × Nat × Nat × Nat × Nat) := #[]
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

private def emitNode (st : EncodeState) (op w a b c : Nat) : Option (Nat × EncodeState) :=
  if isU32 op && isU32 w && isU32 a && isU32 b && isU32 c then
    let idx := st.nodes.size
    if isU32 idx then
      some (idx, { st with nodes := st.nodes.push (op, w, a, b, c) })
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
        some (slot, { st with
          vars := st.vars.push (bvIdx, w)
          varMap := st.varMap.insert (bvIdx, w) slot })
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
    | .literal (.bin lhs pred rhs) =>
      let (a, st1) ← encodeBVExprAux.encodeBVExpr st lhs
      let (b, st2) ← encodeBVExprAux.encodeBVExpr st1 rhs
      let tag := match pred with | .eq => opEq | .ult => opUlt
      emitNode st2 tag 1 a b 0
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

/-- Untrusted DAG-sharing encoder `BVLogicalExpr -> Option (List Nat)` into `BVP1` word stream.
Returns `none` if any parameter, width, or pool count reaches `2^32`. -/
def encode (e : BVLogicalExpr) : Option (List Nat) := do
  let (root, st) ← encodeBVLogical {} e
  let nVars := st.vars.size
  let nNodes := st.nodes.size
  let nCwords := st.cwords.size
  if !(isU32 nVars && isU32 nNodes && isU32 nCwords && isU32 root && 0 < nNodes) then
    none
  let mut ws : Array Nat := #[bvpMagic, bvpVersion, nVars, nNodes, nCwords, root, 0, 0]
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
  return ws.toList

end LeanQbe.T.Examples.Bitblast.Ref.BVProg
