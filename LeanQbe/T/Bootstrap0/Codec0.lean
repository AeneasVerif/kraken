module

public import LeanQbe.T.Bootstrap0.Types0
public import LeanQbe.T.LeanLCNF.Basic
meta import LeanQbe.T.LeanLCNF.Basic

/-!
# Stage B Binary `TFlatModule0` Codec (`Codec0`)

Pure, first-order, monomorphic, strictly closure-free, zero-global, acyclic binary encoder and
decoder for `LeanQbe.T.Bootstrap0.TFlatModule0`:

* Wire format (`LQB0`, version `1`, canonical little-endian):
  - Header: 4-byte magic `[0x4c, 0x51, 0x42, 0x30]` (`"LQB0"`) + 1-byte version `0x01`.
  - Functions (`List TFlatFn0`), extern signatures (`List ExtSig0`), exit symbols (`List Sym0`),
    each prefixed by a `UInt32` count.
  - `TFlat0` ASTs serialized in preorder (`tag | payload | children`), encoded and decoded
    iteratively via explicit first-order continuation worklists/stacks (`EncItem0` / `DecFrame0`).
  - Trailing bytes, truncated inputs, and out-of-range tags are rejected cleanly (`none`).
* LCNF hygiene: zero closures (`papTargets = []`, `maxAp = 0`), zero globals (`consts = 0`,
  `strs = 0`, `bigNats = 0`), acyclic lowered call graph (`checkAcyclic = true`), `≤ 5`
  parameters per function, and `≤ 250` x86-64 directives per lowered function.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

/-! ## 1. Low-level Scalar and Enum Codecs -/

namespace Codec0

/-- Emit 2 raw bytes into `ba`. -/
@[expose] def e2 (ba : ByteArray) (a b : UInt8) : ByteArray :=
  (ba.push a).push b

/-- Emit 4 raw bytes into `ba`. -/
@[expose] def e4 (ba : ByteArray) (a b c d : UInt8) : ByteArray :=
  (((ba.push a).push b).push c).push d

/-- Emit 5-byte `LQB0\x01` header into `ba`. -/
@[expose, noinline] def encodeHeader (ba : ByteArray) : ByteArray :=
  (e4 ba 0x4c 0x51 0x42 0x30).push 0x01

/-- Encode `UInt32` in little-endian order. -/
@[expose, noinline] def encodeU32 (ba : ByteArray) (v : UInt32) : ByteArray :=
  e4 ba v.toUInt8 (v >>> 8).toUInt8 (v >>> 16).toUInt8 (v >>> 24).toUInt8

/-- Encode `UInt64` in little-endian order. -/
@[expose, noinline] def encodeU64 (ba : ByteArray) (v : UInt64) : ByteArray :=
  encodeU32 (encodeU32 ba v.toUInt32) (v >>> 32).toUInt32

/-- Tag byte for `Ty0`. -/
@[expose] def ty0Tag : Ty0 → UInt8
  | .bool => 0 | .b8 => 1 | .b16 => 2 | .b32 => 3 | .b64 => 4

/-- Encode `Ty0` as 1 byte. -/
@[expose, noinline] def encodeTy0 (ba : ByteArray) (t : Ty0) : ByteArray :=
  ba.push (ty0Tag t)

/-- Tag byte for `Width`. -/
@[expose] def widthTag : Width → UInt8
  | .W8 => 0 | .W16 => 1 | .W32 => 2 | .W64 => 3

/-- Encode `Width` as 1 byte. -/
@[expose, noinline] def encodeWidth0 (ba : ByteArray) (w : Width) : ByteArray :=
  ba.push (widthTag w)

/-- Tag byte for `CmpOp`. -/
@[expose] def cmpOpTag : CmpOp → UInt8
  | .eq => 0 | .ne => 1 | .ult => 2 | .ule => 3 | .ugt => 4
  | .uge => 5 | .slt => 6 | .sle => 7 | .sgt => 8 | .sge => 9

/-- Tag byte for `UnOp0`. -/
@[expose] def unOp0Tag : UnOp0 → UInt8
  | .copy => 0 | .neg => 1 | .not => 2

/-- Tag byte for `BinOp0`. -/
@[expose] def binOp0Tag : BinOp0 → UInt8
  | .add => 0 | .sub => 1 | .mul => 2 | .and => 3 | .or => 4 | .xor => 5
  | .shl => 6 | .lshr => 7 | .ashr => 8 | .rotl => 9 | .rotr => 10

/-- Tag byte for `DivOp0`. -/
@[expose] def divOp0Tag : DivOp0 → UInt8
  | .udiv => 0 | .urem => 1 | .sdiv => 2 | .srem => 3

/-- Tag byte for `ConvOp0`. -/
@[expose] def convOp0Tag : ConvOp0 → UInt8
  | .ofBool => 0 | .zext => 1 | .sext => 2 | .trunc => 3

/-- Encode `Arg0`. -/
@[expose, noinline] def encodeArg0 (ba : ByteArray) : Arg0 → ByteArray
  | .var idx => encodeU32 (ba.push 0) idx
  | .immBool false => ba.push 1
  | .immBool true => ba.push 2
  | .immBits w val => encodeU64 (encodeWidth0 (ba.push 3) w) val

/-- Encode `OpCode0` (`.un`/`.bin`/`.cmp`). -/
@[expose, noinline] def encodeOpCodeLow0 (ba : ByteArray) : OpCode0 → ByteArray
  | .un op t => e2 (ba.push 0) (unOp0Tag op) (ty0Tag t)
  | .bin op t => e2 (ba.push 1) (binOp0Tag op) (ty0Tag t)
  | .cmp co t => e2 (ba.push 2) (cmpOpTag co) (ty0Tag t)
  | _ => ba

/-- Encode `OpCode0`. -/
@[expose, noinline] def encodeOpCode0 (ba : ByteArray) (op : OpCode0) : ByteArray :=
  match op with
  | .select t => e2 ba 3 (ty0Tag t)
  | .conv c wSrc wDst => e4 ba 4 (convOp0Tag c) (widthTag wSrc) (widthTag wDst)
  | .div d w => e2 (ba.push 5) (divOp0Tag d) (widthTag w)
  | .umulw64 => ba.push 6
  | _ => encodeOpCodeLow0 ba op

/-! ## 2. List Length Helpers and List Encoders -/

/-- Length of `List Ty0` as `UInt32`. -/
@[expose] def lenTysU32 (xs : @& List Ty0) (acc : UInt32) : UInt32 :=
  match xs with
  | [] => acc
  | _ :: rest => lenTysU32 rest (acc + 1)

/-- Length of `List Arg0` as `UInt32`. -/
@[expose] def lenArgsU32 (xs : @& List Arg0) (acc : UInt32) : UInt32 :=
  match xs with
  | [] => acc
  | _ :: rest => lenArgsU32 rest (acc + 1)

/-- Length of `List Sym0` as `UInt32`. -/
@[expose] def lenSymsU32 (xs : @& List Sym0) (acc : UInt32) : UInt32 :=
  match xs with
  | [] => acc
  | _ :: rest => lenSymsU32 rest (acc + 1)

/-- Length of `List (List Ty0 × TFlat0)` as `UInt32`. -/
@[expose] def lenBlocksU32 (xs : @& List (List Ty0 × TFlat0)) (acc : UInt32) : UInt32 :=
  match xs with
  | [] => acc
  | _ :: rest => lenBlocksU32 rest (acc + 1)

/-- Length of `List TFlatFn0` as `UInt32`. -/
@[expose] def lenFnsU32 (xs : @& List TFlatFn0) (acc : UInt32) : UInt32 :=
  match xs with
  | [] => acc
  | _ :: rest => lenFnsU32 rest (acc + 1)

/-- Length of `List ExtSig0` as `UInt32`. -/
@[expose] def lenExtsU32 (xs : @& List ExtSig0) (acc : UInt32) : UInt32 :=
  match xs with
  | [] => acc
  | _ :: rest => lenExtsU32 rest (acc + 1)

/-- Encode elements of `List Ty0`. -/
@[expose] def encodeTyListLoop0 (ba : ByteArray) : List Ty0 → ByteArray
  | [] => ba
  | t :: rest => encodeTyListLoop0 (encodeTy0 ba t) rest

/-- Encode length-prefixed `List Ty0`. -/
@[expose, noinline] def encodeTyList0 (ba : ByteArray) (xs : List Ty0) : ByteArray :=
  encodeTyListLoop0 (encodeU32 ba (lenTysU32 xs 0)) xs

/-- Encode elements of `List Arg0`. -/
@[expose] def encodeArgListLoop0 (ba : ByteArray) : List Arg0 → ByteArray
  | [] => ba
  | a :: rest => encodeArgListLoop0 (encodeArg0 ba a) rest

/-- Encode length-prefixed `List Arg0`. -/
@[expose, noinline] def encodeArgList0 (ba : ByteArray) (xs : List Arg0) : ByteArray :=
  encodeArgListLoop0 (encodeU32 ba (lenArgsU32 xs 0)) xs

/-- Encode elements of `List Sym0`. -/
@[expose] def encodeSymListLoop0 (ba : ByteArray) : List Sym0 → ByteArray
  | [] => ba
  | s :: rest => encodeSymListLoop0 (encodeU32 ba s) rest

/-- Encode length-prefixed `List Sym0`. -/
@[expose, noinline] def encodeSymList0 (ba : ByteArray) (xs : List Sym0) : ByteArray :=
  encodeSymListLoop0 (encodeU32 ba (lenSymsU32 xs 0)) xs

/-! ## 3. Iterative Preorder `TFlat0` Encoder -/

/-- Explicit continuation item for tail-recursive preorder `TFlat0` serialization. -/
inductive EncItem0 where
  | node (t : TFlat0)
  | blocks (bs : List (List Ty0 × TFlat0))

mutual
/-- Structural node count of `TFlat0` (used strictly for termination). -/
@[expose] def tflatWeight : TFlat0 → Nat
  | .let1 _ _ k => 1 + tflatWeight k
  | .let2Umulw64 _ _ k => 1 + tflatWeight k
  | .load _ _ k => 1 + tflatWeight k
  | .store _ _ _ k => 1 + tflatWeight k
  | .call _ _ _ _ k => 1 + tflatWeight k
  | .tailCall _ _ _ => 1
  | .jnz _ t e => 1 + tflatWeight t + tflatWeight e
  | .jump _ _ => 1
  | .ret _ => 1
  | .exit _ _ _ => 1
  | .hlt => 1
  | .group bodies k => 2 + blocksWeight bodies + tflatWeight k

/-- Weight of a `.group` block list. -/
@[expose] def blocksWeight : List (List Ty0 × TFlat0) → Nat
  | [] => 1
  | (_, b) :: rest => 1 + tflatWeight b + blocksWeight rest
end

/-- Total termination weight of an `EncItem0` worklist. -/
@[expose] def encWorkWeight : List EncItem0 → Nat
  | [] => 0
  | .node t :: rest => tflatWeight t + encWorkWeight rest
  | .blocks bs :: rest => blocksWeight bs + encWorkWeight rest

/-- Encode `.call` header (`fnSym`, `as`, `bs`, `args`) after tag byte. -/
@[expose, noinline] def encodeCallHdr0 (ba : ByteArray) (fnSym : Sym0) (as bs : List Ty0)
    (args : List Arg0) : ByteArray :=
  encodeArgList0 (encodeTyList0 (encodeTyList0 (encodeU32 ba fnSym) as) bs) args

/-- Encode `(fnSym, as, args)` header for `.tailCall`/`.exit` after tag byte. -/
@[expose, noinline] def encodeSigArgs0 (ba : ByteArray) (fnSym : Sym0) (as : List Ty0)
    (args : List Arg0) : ByteArray :=
  encodeArgList0 (encodeTyList0 (encodeU32 ba fnSym) as) args

/-- Encode `.let1` prefix (`tag 0 | op | args`). -/
@[expose, noinline] def encodeLet1Hdr0 (ba : ByteArray) (op : OpCode0)
    (args : List Arg0) : ByteArray :=
  encodeArgList0 (encodeOpCode0 (ba.push 0) op) args

/-- Encode `.store` prefix (`tag 3 | t | val | addr`). -/
@[expose, noinline] def encodeStoreHdr0 (ba : ByteArray) (t : Ty0)
    (val addr : Arg0) : ByteArray :=
  encodeArg0 (encodeArg0 (encodeTy0 (ba.push 3) t) val) addr

/-- Encode leaf `TFlat0` node (`.tailCall`/`.jump`/`.ret`/`.exit`/`.hlt`). -/
@[expose, noinline] def encodeLeafNode0 (ba : ByteArray) (node : TFlat0) : ByteArray :=
  match node with
  | .tailCall fnSym as args => encodeSigArgs0 (ba.push 5) fnSym as args
  | .jump j args => encodeArgList0 (encodeU32 (ba.push 7) j) args
  | .ret vs => encodeArgList0 (ba.push 8) vs
  | .exit fnSym as args => encodeSigArgs0 (ba.push 9) fnSym as args
  | _ => ba.push 10

/-- Step helper for linear/branching `TFlat0` headers. -/
@[expose, noinline] def encodeLinearHdr0 (ba : ByteArray) (node : TFlat0) : ByteArray :=
  match node with
  | .let1 op args _ => encodeLet1Hdr0 ba op args
  | .let2Umulw64 a b _ => encodeArg0 (encodeArg0 (ba.push 1) a) b
  | .load t addr _ => encodeArg0 (encodeTy0 (ba.push 2) t) addr
  | .store t val addr _ => encodeStoreHdr0 ba t val addr
  | .call fnSym as bs args _ => encodeCallHdr0 (ba.push 4) fnSym as bs args
  | .jnz c _ _ => encodeArg0 (ba.push 6) c
  | .group bodies _ => encodeU32 (ba.push 11) (lenBlocksU32 bodies 0)
  | _ => encodeLeafNode0 ba node

/-- Push child continuation items for linear `TFlat0` nodes (`.let1`..`.call`). -/
@[expose, noinline] def pushEncLinChildren0 (t : TFlat0) (rest : List EncItem0) :
    List EncItem0 :=
  match t with
  | .let1 _ _ k => .node k :: rest
  | .let2Umulw64 _ _ k => .node k :: rest
  | .load _ _ k => .node k :: rest
  | .store _ _ _ k => .node k :: rest
  | .call _ _ _ _ k => .node k :: rest
  | _ => rest

/-- Push child continuation items for `t` onto `rest`. -/
@[expose, noinline] def pushEncChildren0 (t : TFlat0) (rest : List EncItem0) :
    List EncItem0 :=
  match t with
  | .jnz _ t1 e1 => .node t1 :: .node e1 :: rest
  | .group bodies k => .blocks bodies :: .node k :: rest
  | _ => pushEncLinChildren0 t rest

private theorem pushEncChildren0_lt (t : TFlat0) (rest : List EncItem0) :
    encWorkWeight (pushEncChildren0 t rest) < tflatWeight t + encWorkWeight rest := by
  cases t <;> simp [pushEncChildren0, pushEncLinChildren0, encWorkWeight, tflatWeight] <;> omega

/-- Build `.blocks` continuation after encoding block signature `ts`. -/
@[expose, noinline] def mkBlockCont0 (ba : ByteArray) (b : TFlat0)
    (tl : List (List Ty0 × TFlat0)) (rest : List EncItem0) :
    ByteArray × List EncItem0 :=
  (ba, .node b :: .blocks tl :: rest)

/-- Execute one `.blocks` step of `encodeTFlatWork0` (`<= 160` directives). -/
@[expose, noinline] def encodeBlocksStep0 (ba : ByteArray)
    (bs : List (List Ty0 × TFlat0)) (rest : List EncItem0) :
    ByteArray × List EncItem0 :=
  match bs with
  | [] => (ba, rest)
  | (ts, b) :: tl => mkBlockCont0 (encodeTyList0 ba ts) b tl rest

/-- Execute one step of `encodeTFlatWork0` (`<= 180` directives). -/
@[expose, noinline] def encodeWorkStep0 (ba : ByteArray) (item : EncItem0)
    (rest : List EncItem0) : ByteArray × List EncItem0 :=
  match item with
  | .blocks bs => encodeBlocksStep0 ba bs rest
  | .node t => (encodeLinearHdr0 ba t, pushEncChildren0 t rest)

private theorem encodeWorkStep0_lt (ba : ByteArray) (item : EncItem0)
    (rest : List EncItem0) :
    encWorkWeight (encodeWorkStep0 ba item rest).2 < encWorkWeight (item :: rest) := by
  cases item with
  | blocks bs =>
    cases bs with
    | nil => simp [encodeWorkStep0, encodeBlocksStep0, encWorkWeight, blocksWeight]
    | cons hd tl =>
      simp [encodeWorkStep0, encodeBlocksStep0, mkBlockCont0, encWorkWeight, blocksWeight]
      omega
  | node t =>
    dsimp only [encodeWorkStep0, encWorkWeight]
    exact pushEncChildren0_lt t rest

/-- Tail-recursive worklist encoder for `TFlat0`. -/
@[expose] def encodeTFlatWork0 (ba : ByteArray) (work : List EncItem0) : ByteArray :=
  match work with
  | [] => ba
  | item :: rest =>
    let step := encodeWorkStep0 ba item rest
    encodeTFlatWork0 step.1 step.2
termination_by encWorkWeight work
decreasing_by exact encodeWorkStep0_lt ba item rest

/-- Encode a single `TFlat0` AST into `ba`. -/
@[expose, noinline] def encodeTFlat0 (ba : ByteArray) (t : TFlat0) : ByteArray :=
  encodeTFlatWork0 ba [.node t]

/-- Encode one `TFlatFn0`. -/
@[expose, noinline] def encodeFn0 (ba : ByteArray) (fn : TFlatFn0) : ByteArray :=
  let ba1 := encodeTyList0 (encodeTyList0 (encodeU32 ba fn.name) fn.as) fn.rs
  encodeTFlat0 ba1 fn.body

/-- Encode `List TFlatFn0` elements. -/
@[expose] def encodeFnListLoop0 (ba : ByteArray) : List TFlatFn0 → ByteArray
  | [] => ba
  | fn :: rest => encodeFnListLoop0 (encodeFn0 ba fn) rest

/-- Encode length-prefixed `List TFlatFn0`. -/
@[expose, noinline] def encodeFnList0 (ba : ByteArray) (fns : List TFlatFn0) : ByteArray :=
  encodeFnListLoop0 (encodeU32 ba (lenFnsU32 fns 0)) fns

/-- Encode one `ExtSig0`. -/
@[expose, noinline] def encodeExt0 (ba : ByteArray) (ex : ExtSig0) : ByteArray :=
  encodeTyList0 (encodeTyList0 (encodeU32 ba ex.name) ex.as) ex.rs

/-- Encode `List ExtSig0` elements. -/
@[expose] def encodeExtListLoop0 (ba : ByteArray) : List ExtSig0 → ByteArray
  | [] => ba
  | ex :: rest => encodeExtListLoop0 (encodeExt0 ba ex) rest

/-- Encode length-prefixed `List ExtSig0`. -/
@[expose, noinline] def encodeExtList0 (ba : ByteArray) (exts : List ExtSig0) : ByteArray :=
  encodeExtListLoop0 (encodeU32 ba (lenExtsU32 exts 0)) exts

end Codec0

/-- Encode a `TFlatModule0` into canonical `LQB0` binary bytes (`0` closures, `0` globals). -/
@[expose] def encodeMod0 (m : TFlatModule0) : ByteArray :=
  let cap : Nat := match m.fns, m.externs, m.exits with | [], [], [] => 17 | _, _, _ => 64
  let ba := Codec0.encodeHeader (ByteArray.emptyWithCapacity cap)
  let ba := Codec0.encodeFnList0 ba m.fns
  let ba := Codec0.encodeExtList0 ba m.externs
  Codec0.encodeSymList0 ba m.exits

/-! ## 4. Monomorphic Decoder Result Types and Primitives -/

namespace Codec0

/-- Monomorphic decode result for `UInt8`. -/
inductive DecU8Res where
  | none
  | ok (v : UInt8) (pos : Nat)

/-- Monomorphic decode result for `UInt16`. -/
inductive DecU16Res where
  | none
  | ok (v : UInt32) (pos : Nat)

/-- Monomorphic decode result for `UInt32`. -/
inductive DecU32Res where
  | none
  | ok (v : UInt32) (pos : Nat)

/-- Monomorphic decode result for `UInt64`. -/
inductive DecU64Res where
  | none
  | ok (v : UInt64) (pos : Nat)

/-- Monomorphic decode result for `Ty0`. -/
inductive DecTyRes where
  | none
  | ok (v : Ty0) (pos : Nat)

/-- Monomorphic decode result for `Width`. -/
inductive DecWidthRes where
  | none
  | ok (v : Width) (pos : Nat)

/-- Monomorphic decode result for `Arg0`. -/
inductive DecArgRes where
  | none
  | ok (v : Arg0) (pos : Nat)

/-- Monomorphic decode result for `OpCode0`. -/
inductive DecOpRes where
  | none
  | ok (v : OpCode0) (pos : Nat)

/-- Monomorphic decode result for `List Ty0`. -/
inductive DecTysRes where
  | none
  | ok (v : List Ty0) (pos : Nat)

/-- Monomorphic decode result for `List Arg0`. -/
inductive DecArgsRes where
  | none
  | ok (v : List Arg0) (pos : Nat)

/-- Monomorphic decode result for `List Sym0`. -/
inductive DecSymsRes where
  | none
  | ok (v : List Sym0) (pos : Nat)

/-- Monomorphic decode result for `TFlat0`. -/
inductive DecTFlatRes where
  | none
  | ok (v : TFlat0) (pos : Nat)

/-- Monomorphic decode result for `TFlatFn0`. -/
inductive DecFnRes where
  | none
  | ok (v : TFlatFn0) (pos : Nat)

/-- Monomorphic decode result for `ExtSig0`. -/
inductive DecExtRes where
  | none
  | ok (v : ExtSig0) (pos : Nat)

/-- Monomorphic decode result for `(Sym0 × List Ty0)` prefix. -/
inductive DecSymTysRes where
  | none
  | ok (sym : Sym0) (tys : List Ty0) (pos : Nat)

/-- Monomorphic decode result for `(Sym0 × List Ty0 × List Ty0)` prefix. -/
inductive DecCallSigRes where
  | none
  | ok (sym : Sym0) (as bs : List Ty0) (pos : Nat)

/-- Monomorphic decode result for `List TFlatFn0`. -/
inductive DecFnsRes where
  | none
  | ok (v : List TFlatFn0) (pos : Nat)

/-- Monomorphic decode result for `List ExtSig0`. -/
inductive DecExtsRes where
  | none
  | ok (v : List ExtSig0) (pos : Nat)

/-- Explicit continuation frame for iterative `TFlat0` decoding. -/
inductive DecFrame0 where
  | let1 (op : OpCode0) (args : List Arg0)
  | let2Umulw64 (a b : Arg0)
  | load (t : Ty0) (addr : Arg0)
  | store (t : Ty0) (val addr : Arg0)
  | call (fnSym : Sym0) (as bs : List Ty0) (args : List Arg0)
  | jnzL (c : Arg0)
  | jnzR (c : Arg0) (t : TFlat0)
  | groupBody (remAfterCur : UInt32) (curTs : List Ty0)
      (doneRev : List (List Ty0 × TFlat0))
  | groupKEmpty
  | groupK (bodies : List (List Ty0 × TFlat0))

/-- Outcome of popping completed `DecFrame0` frames. -/
inductive DecFrameStep0 where
  | none
  | done (v : TFlat0) (pos : Nat)
  | cont (pos : Nat) (frames : List DecFrame0)

/-- Outcome of decoding one `TFlat0` node header. -/
inductive DecStep0 where
  | none
  | push (pos : Nat) (f : DecFrame0)
  | leaf (pos : Nat) (v : TFlat0)

/-- Proof helper allowing `UInt32` decrement without `Nat` overhead in LCNF. -/
theorem u32Sub1Lt (n : UInt32) (h : n ≠ 0) : (n - 1).toNat < n.toNat := by
  have hn : n.toNat ≠ 0 := by
    intro hz
    apply h
    calc n = UInt32.ofNat n.toNat := UInt32.ofNat_toNat.symm
      _ = UInt32.ofNat 0 := by rw [hz]
      _ = 0 := rfl
  have h1 : (1 : UInt32) ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
  rw [UInt32.toNat_sub_of_le n 1 h1]
  exact Nat.sub_lt (Nat.pos_of_ne_zero hn) Nat.zero_lt_one

/-- Decode a single byte at `pos`. -/
@[expose, noinline] def decodeU8 (ba : @& ByteArray) (pos : Nat) : DecU8Res :=
  if h : pos < ba.size then .ok (ba[pos]'h) (pos + 1) else .none

/-- Decode 2 little-endian bytes into `UInt32` at `pos`. -/
@[expose, noinline] def decodeU16 (ba : @& ByteArray) (pos : Nat) : DecU16Res :=
  match decodeU8 ba pos with
  | .none => .none
  | .ok b0 pos1 =>
    match decodeU8 ba pos1 with
    | .none => .none
    | .ok b1 pos2 => .ok (b0.toUInt32 ||| (b1.toUInt32 <<< 8)) pos2

/-- Decode a little-endian `UInt32` at `pos`. -/
@[expose, noinline] def decodeU32 (ba : @& ByteArray) (pos : Nat) : DecU32Res :=
  match decodeU16 ba pos with
  | .none => .none
  | .ok lo pos1 =>
    match decodeU16 ba pos1 with
    | .none => .none
    | .ok hi pos2 => .ok (lo ||| (hi <<< 16)) pos2

/-- Decode a little-endian `UInt64` at `pos`. -/
@[expose, noinline] def decodeU64 (ba : @& ByteArray) (pos : Nat) : DecU64Res :=
  match decodeU32 ba pos with
  | .none => .none
  | .ok lo pos1 =>
    match decodeU32 ba pos1 with
    | .none => .none
    | .ok hi pos2 => .ok (lo.toUInt64 ||| (hi.toUInt64 <<< 32)) pos2

/-- Verify the 5-byte `LQB0\x01` header starting at `pos = 0`. -/
@[expose, noinline] def checkHeader (ba : @& ByteArray) : Bool :=
  match decodeU32 ba 0 with
  | .none => false
  | .ok magic _ =>
    if magic == 0x3042514c then
      match decodeU8 ba 4 with
      | .ok 1 _ => true
      | _ => false
    else false

/-- Decode `Ty0` at `pos` (`0` closed globals). -/
@[expose, noinline] def decodeTy0 (ba : @& ByteArray) (pos : Nat) : DecTyRes :=
  match decodeU8 ba pos with
  | .none => .none
  | .ok b pos1 =>
    if b == 0 then .ok .bool pos1
    else if b == 1 then .ok .b8 pos1
    else if b == 2 then .ok .b16 pos1
    else if b == 3 then .ok .b32 pos1
    else if b == 4 then .ok .b64 pos1
    else .none

/-- Decode `Width` at `pos` (`0` closed globals). -/
@[expose, noinline] def decodeWidth0 (ba : @& ByteArray) (pos : Nat) : DecWidthRes :=
  match decodeU8 ba pos with
  | .none => .none
  | .ok b pos1 =>
    if b == 0 then .ok .W8 pos1
    else if b == 1 then .ok .W16 pos1
    else if b == 2 then .ok .W32 pos1
    else if b == 3 then .ok .W64 pos1
    else .none

/-- Decode `.immBits` payload of `Arg0`. -/
@[expose, noinline] def decodeArgBits0 (ba : @& ByteArray) (pos : Nat) : DecArgRes :=
  match decodeWidth0 ba pos with
  | .none => .none
  | .ok w pos1 =>
    match decodeU64 ba pos1 with
    | .none => .none
    | .ok val pos2 => .ok (.immBits w val) pos2

/-- Decode `.var` payload of `Arg0`. -/
@[expose, noinline] def decodeArgVar0 (ba : @& ByteArray) (pos : Nat) : DecArgRes :=
  match decodeU32 ba pos with
  | .none => .none
  | .ok idx pos1 => .ok (.var idx) pos1

/-- Decode `Arg0` at `pos`. -/
@[expose, noinline] def decodeArg0 (ba : @& ByteArray) (pos : Nat) : DecArgRes :=
  match decodeU8 ba pos with
  | .none => .none
  | .ok tag pos1 =>
    if tag == 0 then decodeArgVar0 ba pos1
    else if tag == 1 then .ok (.immBool false) pos1
    else if tag == 2 then .ok (.immBool true) pos1
    else if tag == 3 then decodeArgBits0 ba pos1
    else .none

/-- Decode `UnOp0` + `Ty0` into `OpCode0.un` (`0` closed globals). -/
@[expose, noinline] def decodeOpUn0 (ba : @& ByteArray) (pos : Nat) : DecOpRes :=
  match decodeU8 ba pos with
  | .none => .none
  | .ok b pos1 =>
    if 2 < b then .none
    else
      match decodeTy0 ba pos1 with
      | .none => .none
      | .ok t pos2 =>
        if b == 0 then .ok (.un .copy t) pos2
        else if b == 1 then .ok (.un .neg t) pos2
        else .ok (.un .not t) pos2

/-- Decode `BinOp0` (low 0..5) + `Ty0` into `OpCode0.bin` (`0` closed globals). -/
@[expose, noinline] def decodeOpBinLow0 (b : UInt8) (t : Ty0) (pos : Nat) : DecOpRes :=
  if b == 0 then .ok (.bin .add t) pos
  else if b == 1 then .ok (.bin .sub t) pos
  else if b == 2 then .ok (.bin .mul t) pos
  else if b == 3 then .ok (.bin .and t) pos
  else if b == 4 then .ok (.bin .or t) pos
  else .ok (.bin .xor t) pos

/-- Decode `BinOp0` (high 6..10) + `Ty0` into `OpCode0.bin` (`0` closed globals). -/
@[expose, noinline] def decodeOpBinHi0 (b : UInt8) (t : Ty0) (pos : Nat) : DecOpRes :=
  if b == 6 then .ok (.bin .shl t) pos
  else if b == 7 then .ok (.bin .lshr t) pos
  else if b == 8 then .ok (.bin .ashr t) pos
  else if b == 9 then .ok (.bin .rotl t) pos
  else .ok (.bin .rotr t) pos

/-- Decode `BinOp0` + `Ty0` into `OpCode0.bin` (`0` closed globals). -/
@[expose, noinline] def decodeOpBin0 (ba : @& ByteArray) (pos : Nat) : DecOpRes :=
  match decodeU8 ba pos with
  | .none => .none
  | .ok b pos1 =>
    if 10 < b then .none
    else
      match decodeTy0 ba pos1 with
      | .none => .none
      | .ok t pos2 =>
        if b <= 5 then decodeOpBinLow0 b t pos2
        else decodeOpBinHi0 b t pos2

/-- Decode `CmpOp` (low 0..4) + `Ty0` into `OpCode0.cmp` (`0` closed globals). -/
@[expose, noinline] def decodeOpCmpLow0 (b : UInt8) (t : Ty0) (pos : Nat) : DecOpRes :=
  if b == 0 then .ok (.cmp .eq t) pos
  else if b == 1 then .ok (.cmp .ne t) pos
  else if b == 2 then .ok (.cmp .ult t) pos
  else if b == 3 then .ok (.cmp .ule t) pos
  else .ok (.cmp .ugt t) pos

/-- Decode `CmpOp` (high 5..9) + `Ty0` into `OpCode0.cmp` (`0` closed globals). -/
@[expose, noinline] def decodeOpCmpHi0 (b : UInt8) (t : Ty0) (pos : Nat) : DecOpRes :=
  if b == 5 then .ok (.cmp .uge t) pos
  else if b == 6 then .ok (.cmp .slt t) pos
  else if b == 7 then .ok (.cmp .sle t) pos
  else if b == 8 then .ok (.cmp .sgt t) pos
  else .ok (.cmp .sge t) pos

/-- Decode `CmpOp` + `Ty0` into `OpCode0.cmp` (`0` closed globals). -/
@[expose, noinline] def decodeOpCmp0 (ba : @& ByteArray) (pos : Nat) : DecOpRes :=
  match decodeU8 ba pos with
  | .none => .none
  | .ok b pos1 =>
    if 9 < b then .none
    else
      match decodeTy0 ba pos1 with
      | .none => .none
      | .ok t pos2 =>
        if b <= 4 then decodeOpCmpLow0 b t pos2
        else decodeOpCmpHi0 b t pos2

/-- Decode `.un`/`.bin`/`.cmp` part of `OpCode0`. -/
@[expose, noinline] def decodeOpCodeLow0 (ba : @& ByteArray) (pos : Nat) (tag : UInt8) :
    DecOpRes :=
  if tag == 0 then decodeOpUn0 ba pos
  else if tag == 1 then decodeOpBin0 ba pos
  else decodeOpCmp0 ba pos

/-- Construct `.conv` `OpCode0` from validated tag (`0..3`). -/
@[expose, noinline] def mkConvOp0 (cByte : UInt8) (wSrc wDst : Width) (pos : Nat) :
    DecOpRes :=
  if cByte == 0 then .ok (.conv .ofBool wSrc wDst) pos
  else if cByte == 1 then .ok (.conv .zext wSrc wDst) pos
  else if cByte == 2 then .ok (.conv .sext wSrc wDst) pos
  else .ok (.conv .trunc wSrc wDst) pos

/-- Decode `.conv` `OpCode0` (`0` closed globals). -/
@[expose, noinline] def decodeOpConv0 (ba : @& ByteArray) (pos : Nat) : DecOpRes :=
  match decodeU8 ba pos with
  | .none => .none
  | .ok cByte pos1 =>
    if 3 < cByte then .none
    else
      match decodeWidth0 ba pos1 with
      | .none => .none
      | .ok wSrc pos2 =>
        match decodeWidth0 ba pos2 with
        | .none => .none
        | .ok wDst pos3 => mkConvOp0 cByte wSrc wDst pos3

/-- Construct `.div` `OpCode0` from validated tag (`0..3`). -/
@[expose, noinline] def mkDivOp0 (dByte : UInt8) (w : Width) (pos : Nat) : DecOpRes :=
  if dByte == 0 then .ok (.div .udiv w) pos
  else if dByte == 1 then .ok (.div .urem w) pos
  else if dByte == 2 then .ok (.div .sdiv w) pos
  else .ok (.div .srem w) pos

/-- Decode `.div` `OpCode0` (`0` closed globals). -/
@[expose, noinline] def decodeOpDiv0 (ba : @& ByteArray) (pos : Nat) : DecOpRes :=
  match decodeU8 ba pos with
  | .none => .none
  | .ok dByte pos1 =>
    if 3 < dByte then .none
    else
      match decodeWidth0 ba pos1 with
      | .none => .none
      | .ok w pos2 => mkDivOp0 dByte w pos2

/-- Decode `.conv` / `.div` / `.select` / `.umulw64` part of `OpCode0`. -/
@[expose, noinline] def decodeOpCodeHi0 (ba : @& ByteArray) (pos : Nat) (tag : UInt8) :
    DecOpRes :=
  if tag == 3 then
    match decodeTy0 ba pos with
    | .none => .none
    | .ok t pos1 => .ok (.select t) pos1
  else if tag == 4 then decodeOpConv0 ba pos
  else if tag == 5 then decodeOpDiv0 ba pos
  else if tag == 6 then .ok .umulw64 pos
  else .none

/-- Decode `OpCode0` at `pos`. -/
@[expose, noinline] def decodeOpCode0 (ba : @& ByteArray) (pos : Nat) : DecOpRes :=
  match decodeU8 ba pos with
  | .none => .none
  | .ok tag pos1 =>
    if tag <= 2 then decodeOpCodeLow0 ba pos1 tag
    else decodeOpCodeHi0 ba pos1 tag

/-! ## 5. Tail-Recursive List Reversers and List Decoders -/

/-- Tail-recursive list reverse for `List Ty0`. -/
@[expose] def revTys0 (xs acc : List Ty0) : List Ty0 :=
  match xs with
  | [] => acc
  | x :: rest => revTys0 rest (x :: acc)

/-- Tail-recursive list reverse for `List Arg0`. -/
@[expose] def revArgs0 (xs acc : List Arg0) : List Arg0 :=
  match xs with
  | [] => acc
  | x :: rest => revArgs0 rest (x :: acc)

/-- Tail-recursive list reverse for `List Sym0`. -/
@[expose] def revSyms0 (xs acc : List Sym0) : List Sym0 :=
  match xs with
  | [] => acc
  | x :: rest => revSyms0 rest (x :: acc)

/-- Tail-recursive list reverse for `List (List Ty0 × TFlat0)`. -/
@[expose] def revBlocks0 (xs acc : List (List Ty0 × TFlat0)) :
    List (List Ty0 × TFlat0) :=
  match xs with
  | [] => acc
  | x :: rest => revBlocks0 rest (x :: acc)

/-- Tail-recursive list reverse for `List TFlatFn0`. -/
@[expose] def revFns0 (xs acc : List TFlatFn0) : List TFlatFn0 :=
  match xs with
  | [] => acc
  | x :: rest => revFns0 rest (x :: acc)

/-- Tail-recursive list reverse for `List ExtSig0`. -/
@[expose] def revExts0 (xs acc : List ExtSig0) : List ExtSig0 :=
  match xs with
  | [] => acc
  | x :: rest => revExts0 rest (x :: acc)

/-- Decode `rem` elements of `List Ty0` into `acc` (reversed). -/
@[expose] def decodeTyListLoop0 (ba : @& ByteArray) (pos : Nat) (rem : UInt32)
    (acc : List Ty0) : DecTysRes :=
  if h : rem = 0 then .ok (revTys0 acc []) pos
  else
    have _ := u32Sub1Lt rem h
    match decodeTy0 ba pos with
    | .none => .none
    | .ok t pos1 => decodeTyListLoop0 ba pos1 (rem - 1) (t :: acc)
termination_by rem.toNat

/-- Decode length-prefixed `List Ty0`. -/
@[expose, noinline] def decodeTyList0 (ba : @& ByteArray) (pos : Nat) : DecTysRes :=
  match decodeU32 ba pos with
  | .none => .none
  | .ok cnt pos1 => decodeTyListLoop0 ba pos1 cnt []

/-- Decode `rem` elements of `List Arg0` into `acc` (reversed). -/
@[expose] def decodeArgListLoop0 (ba : @& ByteArray) (pos : Nat) (rem : UInt32)
    (acc : List Arg0) : DecArgsRes :=
  if h : rem = 0 then .ok (revArgs0 acc []) pos
  else
    have _ := u32Sub1Lt rem h
    match decodeArg0 ba pos with
    | .none => .none
    | .ok a pos1 => decodeArgListLoop0 ba pos1 (rem - 1) (a :: acc)
termination_by rem.toNat

/-- Decode length-prefixed `List Arg0`. -/
@[expose, noinline] def decodeArgList0 (ba : @& ByteArray) (pos : Nat) : DecArgsRes :=
  match decodeU32 ba pos with
  | .none => .none
  | .ok cnt pos1 => decodeArgListLoop0 ba pos1 cnt []

/-- Decode `rem` elements of `List Sym0` into `acc` (reversed). -/
@[expose] def decodeSymListLoop0 (ba : @& ByteArray) (pos : Nat) (rem : UInt32)
    (acc : List Sym0) : DecSymsRes :=
  if h : rem = 0 then .ok (revSyms0 acc []) pos
  else
    have _ := u32Sub1Lt rem h
    match decodeU32 ba pos with
    | .none => .none
    | .ok s pos1 => decodeSymListLoop0 ba pos1 (rem - 1) (s :: acc)
termination_by rem.toNat

/-- Decode length-prefixed `List Sym0`. -/
@[expose, noinline] def decodeSymList0 (ba : @& ByteArray) (pos : Nat) : DecSymsRes :=
  match decodeU32 ba pos with
  | .none => .none
  | .ok cnt pos1 => decodeSymListLoop0 ba pos1 cnt []

/-! ## 6. Iterative Stack-Based `TFlat0` and Module Decoders -/

/-- Decode `(sym, tys)` prefix helper. -/
@[expose, noinline] def decodeSymTys0 (ba : @& ByteArray) (pos : Nat) : DecSymTysRes :=
  match decodeU32 ba pos with
  | .none => .none
  | .ok sym pos1 =>
    match decodeTyList0 ba pos1 with
    | .none => .none
    | .ok tys pos2 => .ok sym tys pos2

/-- Decode `(sym, as, bs)` prefix helper. -/
@[expose, noinline] def decodeCallSig0 (ba : @& ByteArray) (pos : Nat) : DecCallSigRes :=
  match decodeSymTys0 ba pos with
  | .none => .none
  | .ok sym as pos1 =>
    match decodeTyList0 ba pos1 with
    | .none => .none
    | .ok bs pos2 => .ok sym as bs pos2

/-- Build `.call` step from decoded signature and arguments. -/
@[expose, noinline] def mkCallStep0 (fnSym : Sym0) (as bs : List Ty0)
    (argsRes : DecArgsRes) : DecStep0 :=
  match argsRes with
  | .none => .none
  | .ok args pos2 => .push pos2 (.call fnSym as bs args)

/-- Decode `.call` node header after signature prefix. -/
@[expose, noinline] def finishCallStep0 (ba : @& ByteArray)
    (sig : DecCallSigRes) : DecStep0 :=
  match sig with
  | .none => .none
  | .ok fnSym as bs pos1 => mkCallStep0 fnSym as bs (decodeArgList0 ba pos1)

/-- Decode `.call` node header (`fnSym`, `as`, `bs`, `args`). -/
@[expose, noinline] def decodeCallStep0 (ba : @& ByteArray) (pos : Nat) : DecStep0 :=
  finishCallStep0 ba (decodeCallSig0 ba pos)

/-- Build `.let1` step from decoded opcode and arguments. -/
@[expose, noinline] def mkLet1Step0 (op : OpCode0) (argsRes : DecArgsRes) : DecStep0 :=
  match argsRes with
  | .none => .none
  | .ok args pos2 => .push pos2 (.let1 op args)

/-- Finish `.let1` node header after opcode decode. -/
@[expose, noinline] def finishLet1Step0 (ba : @& ByteArray) (opRes : DecOpRes) : DecStep0 :=
  match opRes with
  | .none => .none
  | .ok op pos1 => mkLet1Step0 op (decodeArgList0 ba pos1)

/-- Decode `.let1` node header (`tag 0`). -/
@[expose, noinline] def decodeLet1Step0 (ba : @& ByteArray) (pos : Nat) : DecStep0 :=
  finishLet1Step0 ba (decodeOpCode0 ba pos)

/-- Decode `.let2Umulw64` node header (`tag 1`). -/
@[expose, noinline] def decodeLet2Step0 (ba : @& ByteArray) (pos : Nat) : DecStep0 :=
  match decodeArg0 ba pos with
  | .none => .none
  | .ok a pos1 =>
    match decodeArg0 ba pos1 with
    | .none => .none
    | .ok b pos2 => .push pos2 (.let2Umulw64 a b)

/-- Decode `.load` node header (`tag 2`). -/
@[expose, noinline] def decodeLoadStep0 (ba : @& ByteArray) (pos : Nat) : DecStep0 :=
  match decodeTy0 ba pos with
  | .none => .none
  | .ok t pos1 =>
    match decodeArg0 ba pos1 with
    | .none => .none
    | .ok addr pos2 => .push pos2 (.load t addr)

/-- Finish `.store` node header after `(t, val)` decode. -/
@[expose, noinline] def finishStoreStep0 (ba : @& ByteArray) (t : Ty0)
    (valRes : DecArgRes) : DecStep0 :=
  match valRes with
  | .none => .none
  | .ok val pos1 =>
    match decodeArg0 ba pos1 with
    | .none => .none
    | .ok addr pos2 => .push pos2 (.store t val addr)

/-- Decode `.store` node header (`tag 3`). -/
@[expose, noinline] def decodeStoreStep0 (ba : @& ByteArray) (pos : Nat) : DecStep0 :=
  match decodeTy0 ba pos with
  | .none => .none
  | .ok t pos1 => finishStoreStep0 ba t (decodeArg0 ba pos1)

/-- Decode `.let1`/`.let2Umulw64`/`.load`/`.store` node headers (`tag` 0..3). -/
@[expose, noinline] def decodeLinLowStep0 (ba : @& ByteArray) (pos : Nat) (tag : UInt8) :
    DecStep0 :=
  if tag == 0 then decodeLet1Step0 ba pos
  else if tag == 1 then decodeLet2Step0 ba pos
  else if tag == 2 then decodeLoadStep0 ba pos
  else decodeStoreStep0 ba pos

/-- Build `.tailCall` / `.exit` leaf step from decoded signature and arguments. -/
@[expose, noinline] def mkTailOrExit0 (isExit : Bool) (fnSym : Sym0) (as : List Ty0)
    (argsRes : DecArgsRes) : DecStep0 :=
  match argsRes with
  | .none => .none
  | .ok args pos2 =>
    if isExit then .leaf pos2 (.exit fnSym as args)
    else .leaf pos2 (.tailCall fnSym as args)

/-- Finish `.tailCall` / `.exit` leaf node after `(fnSym, as)` decode. -/
@[expose, noinline] def finishTailOrExit0 (ba : @& ByteArray) (isExit : Bool)
    (sig : DecSymTysRes) : DecStep0 :=
  match sig with
  | .none => .none
  | .ok fnSym as pos1 => mkTailOrExit0 isExit fnSym as (decodeArgList0 ba pos1)

/-- Decode `.tailCall` (`isExit = false`) or `.exit` (`isExit = true`). -/
@[expose, noinline] def decodeTailOrExitStep0 (ba : @& ByteArray) (pos : Nat)
    (isExit : Bool) : DecStep0 :=
  finishTailOrExit0 ba isExit (decodeSymTys0 ba pos)

/-- Decode `.jump` leaf node (`tag 7`). -/
@[expose, noinline] def decodeJumpStep0 (ba : @& ByteArray) (pos : Nat) : DecStep0 :=
  match decodeU32 ba pos with
  | .none => .none
  | .ok j pos1 =>
    match decodeArgList0 ba pos1 with
    | .none => .none
    | .ok args pos2 => .leaf pos2 (.jump j args)

/-- Decode `.ret`/`.exit`/`.hlt` leaf nodes (`tag` 8,9,10). -/
@[expose, noinline] def decodeLeafHiStep0 (ba : @& ByteArray) (pos : Nat) (tag : UInt8) :
    DecStep0 :=
  if tag == 8 then
    match decodeArgList0 ba pos with
    | .none => .none
    | .ok vs pos1 => .leaf pos1 (.ret vs)
  else if tag == 9 then decodeTailOrExitStep0 ba pos true
  else if tag == 10 then .leaf pos .hlt
  else .none

/-- Decode `.tailCall`/`.jump`/`.ret`/`.exit`/`.hlt` leaf nodes (`tag` 5,7,8,9,10). -/
@[expose, noinline] def decodeLeafStep0 (ba : @& ByteArray) (pos : Nat) (tag : UInt8) :
    DecStep0 :=
  if tag == 5 then decodeTailOrExitStep0 ba pos false
  else if tag == 7 then decodeJumpStep0 ba pos
  else decodeLeafHiStep0 ba pos tag

/-- Decode `.group` node header (`tag == 11`). -/
@[expose, noinline] def decodeGroupStep0 (ba : @& ByteArray) (pos : Nat) : DecStep0 :=
  match decodeU32 ba pos with
  | .none => .none
  | .ok cnt pos1 =>
    if cnt == 0 then .push pos1 .groupKEmpty
    else
      match decodeTyList0 ba pos1 with
      | .none => .none
      | .ok ts0 pos2 => .push pos2 (.groupBody (cnt - 1) ts0 [])

/-- Decode `.jnz` (`tag == 6`) and `.group` (`tag == 11`) node headers. -/
@[expose, noinline] def decodeBranchStep0 (ba : @& ByteArray) (pos : Nat) (tag : UInt8) :
    DecStep0 :=
  if tag == 6 then
    match decodeArg0 ba pos with
    | .none => .none
    | .ok c pos1 => .push pos1 (.jnzL c)
  else if tag == 11 then decodeGroupStep0 ba pos
  else decodeLeafStep0 ba pos tag

/-- Decode one `TFlat0` node header at `pos`. -/
@[expose, noinline] def decodeNodeStep0 (ba : @& ByteArray) (pos : Nat) : DecStep0 :=
  match decodeU8 ba pos with
  | .none => .none
  | .ok tag pos1 =>
    if tag <= 3 then decodeLinLowStep0 ba pos1 tag
    else if tag == 4 then decodeCallStep0 ba pos1
    else decodeBranchStep0 ba pos1 tag

/-- Wrap `v` in a `.let1`/`.let2Umulw64`/`.load`/`.store` `DecFrame0`. -/
@[expose, noinline] def applyLinLowFrame0 (f : DecFrame0) (v : TFlat0) : TFlat0 :=
  match f with
  | .let1 op args => .let1 op args v
  | .let2Umulw64 a b => .let2Umulw64 a b v
  | .load t addr => .load t addr v
  | .store t val addr => .store t val addr v
  | _ => v

/-- Wrap `v` in a `.call`/`.jnzR`/`.groupK*` `DecFrame0`. -/
@[expose, noinline] def applyLinFrame0 (f : DecFrame0) (v : TFlat0) : TFlat0 :=
  match f with
  | .call fnSym as bs args => .call fnSym as bs args v
  | .jnzR c t => .jnz c t v
  | .groupKEmpty => .group [] v
  | .groupK bodies => .group bodies v
  | _ => applyLinLowFrame0 f v

/-- Read next `.groupBody` type list and push next frame. -/
@[expose, noinline] def nextGroupBodyCont0 (ba : @& ByteArray) (pos : Nat)
    (remAfterCur : UInt32) (doneRev : List (List Ty0 × TFlat0))
    (rest : List DecFrame0) : DecFrameStep0 :=
  match decodeTyList0 ba pos with
  | .none => .none
  | .ok tsNext pos' => .cont pos' (.groupBody (remAfterCur - 1) tsNext doneRev :: rest)

/-- Build next `DecFrame0` after completing a `.groupBody` block. -/
@[expose, noinline] def nextGroupFrame0 (ba : @& ByteArray) (pos : Nat) (remAfterCur : UInt32)
    (doneRev : List (List Ty0 × TFlat0)) (rest : List DecFrame0) : DecFrameStep0 :=
  if remAfterCur == 0 then .cont pos (.groupK (revBlocks0 doneRev []) :: rest)
  else nextGroupBodyCont0 ba pos remAfterCur doneRev rest

/-- Advance a `.groupBody` continuation frame after finishing one block body `v`. -/
@[expose, noinline] def applyGroupBody0 (ba : @& ByteArray) (pos : Nat) (v : TFlat0)
    (f : DecFrame0) (rest : List DecFrame0) : DecFrameStep0 :=
  match f with
  | .groupBody remAfterCur curTs doneRev =>
    nextGroupFrame0 ba pos remAfterCur ((curTs, v) :: doneRev) rest
  | _ => .none

/-- Dispatch one top frame `f` (`jnzL`, `groupBody`, or linear wrapper). -/
@[expose, noinline] def stepNonLinFrame0 (ba : @& ByteArray) (pos : Nat) (v : TFlat0)
    (f : DecFrame0) (rest : List DecFrame0) : DecFrameStep0 :=
  match f with
  | .jnzL c => .cont pos (.jnzR c v :: rest)
  | .groupBody _ _ _ => applyGroupBody0 ba pos v f rest
  | _ => .none

/-- Pop completed continuation frames until empty (`done`) or next child needed (`cont`). -/
@[expose] def decodeApplyFrames0 (ba : @& ByteArray) (pos : Nat) (v : TFlat0)
    (frames : List DecFrame0) : DecFrameStep0 :=
  match frames with
  | [] => .done v pos
  | f :: rest =>
    match f with
    | .jnzL _ | .groupBody _ _ _ => stepNonLinFrame0 ba pos v f rest
    | _ => decodeApplyFrames0 ba pos (applyLinFrame0 f v) rest

/-- Advance one `DecNodeStep0` against continuation `frames`. -/
@[expose, noinline] def stepLoopFrame0 (ba : @& ByteArray) (step : DecStep0)
    (frames : List DecFrame0) : DecFrameStep0 :=
  match step with
  | .none => .none
  | .push pos1 f => .cont pos1 (f :: frames)
  | .leaf pos1 v => decodeApplyFrames0 ba pos1 v frames

/-- Fuel-bounded iterative `TFlat0` decoder loop. -/
@[expose] def decodeTFlatLoop0 (fuel : UInt32) (ba : @& ByteArray) (pos : Nat)
    (frames : List DecFrame0) : DecTFlatRes :=
  if h : fuel = 0 then .none
  else
    have _ := u32Sub1Lt fuel h
    match stepLoopFrame0 ba (decodeNodeStep0 ba pos) frames with
    | .none => .none
    | .done res pos2 => .ok res pos2
    | .cont pos2 frames' => decodeTFlatLoop0 (fuel - 1) ba pos2 frames'
termination_by fuel.toNat

/-- Decode a single `TFlat0` AST starting at `pos`. -/
@[expose, noinline] def decodeTFlat0 (ba : @& ByteArray) (pos : Nat) : DecTFlatRes :=
  let rem := ba.size - pos
  let fuel : UInt32 := if rem < 0xffffffff then UInt32.ofNat rem else 0xffffffff
  decodeTFlatLoop0 fuel ba pos []

/-- Decode `(name, as, rs)` signature prefix of `TFlatFn0` or `ExtSig0`. -/
@[expose, noinline] def decodeExt0 (ba : @& ByteArray) (pos : Nat) : DecExtRes :=
  match decodeCallSig0 ba pos with
  | .none => .none
  | .ok name as rs pos1 => .ok { name, as, rs } pos1

/-- Decode one `TFlatFn0`. -/
@[expose, noinline] def decodeFn0 (ba : @& ByteArray) (pos : Nat) : DecFnRes :=
  match decodeExt0 ba pos with
  | .none => .none
  | .ok hdr pos1 =>
    match decodeTFlat0 ba pos1 with
    | .none => .none
    | .ok body pos2 => .ok { name := hdr.name, as := hdr.as, rs := hdr.rs, body } pos2

/-- Decode `rem` elements of `List TFlatFn0` into `acc` (reversed). -/
@[expose] def decodeFnListLoop0 (ba : @& ByteArray) (pos : Nat) (rem : UInt32)
    (acc : List TFlatFn0) : DecFnsRes :=
  if h : rem = 0 then .ok (revFns0 acc []) pos
  else
    have _ := u32Sub1Lt rem h
    match decodeFn0 ba pos with
    | .none => .none
    | .ok fn pos1 => decodeFnListLoop0 ba pos1 (rem - 1) (fn :: acc)
termination_by rem.toNat

/-- Decode length-prefixed `List TFlatFn0`. -/
@[expose, noinline] def decodeFnList0 (ba : @& ByteArray) (pos : Nat) : DecFnsRes :=
  match decodeU32 ba pos with
  | .none => .none
  | .ok cnt pos1 => decodeFnListLoop0 ba pos1 cnt []

/-- Decode `rem` elements of `List ExtSig0` into `acc` (reversed). -/
@[expose] def decodeExtListLoop0 (ba : @& ByteArray) (pos : Nat) (rem : UInt32)
    (acc : List ExtSig0) : DecExtsRes :=
  if h : rem = 0 then .ok (revExts0 acc []) pos
  else
    have _ := u32Sub1Lt rem h
    match decodeExt0 ba pos with
    | .none => .none
    | .ok ex pos1 => decodeExtListLoop0 ba pos1 (rem - 1) (ex :: acc)
termination_by rem.toNat

/-- Decode length-prefixed `List ExtSig0`. -/
@[expose, noinline] def decodeExtList0 (ba : @& ByteArray) (pos : Nat) : DecExtsRes :=
  match decodeU32 ba pos with
  | .none => .none
  | .ok cnt pos1 => decodeExtListLoop0 ba pos1 cnt []

/-- Finalize `TFlatModule0` when `exits` reaches exact end of buffer. -/
@[expose, noinline] def mkModIfEof0 (ba : @& ByteArray) (fns : List TFlatFn0)
    (exts : List ExtSig0) (exitsRes : DecSymsRes) : Option TFlatModule0 :=
  match exitsRes with
  | .none => none
  | .ok exits pos2 =>
    if pos2 == ba.size then some { fns, externs := exts, exits } else none

/-- Decode `exits` tail of `TFlatModule0` after `fns` and `externs`. -/
@[expose, noinline] def decodeModExits0 (ba : @& ByteArray) (pos : Nat)
    (fns : List TFlatFn0) (exts : List ExtSig0) : Option TFlatModule0 :=
  mkModIfEof0 ba fns exts (decodeSymList0 ba pos)

/-- Decode `(exts, exits)` tail of `TFlatModule0` after `fns`. -/
@[expose, noinline] def decodeModTail0 (ba : @& ByteArray) (pos : Nat)
    (fns : List TFlatFn0) : Option TFlatModule0 :=
  match decodeExtList0 ba pos with
  | .none => none
  | .ok exts pos1 => decodeModExits0 ba pos1 fns exts

/-- Decode `(fns, externs, exits)` payload after verified header. -/
@[expose, noinline] def decodeModBody0 (ba : @& ByteArray) : Option TFlatModule0 :=
  match decodeFnList0 ba 5 with
  | .none => none
  | .ok fns pos1 => decodeModTail0 ba pos1 fns

end Codec0

/-- Decode canonical `LQB0` binary bytes into a `TFlatModule0`, rejecting malformed or trailing
bytes (`0` closures, `0` globals). -/
@[expose] def decodeMod0 (ba : @& ByteArray) : Option TFlatModule0 :=
  if Codec0.checkHeader ba then Codec0.decodeModBody0 ba else none

/-! ## 7. Extracted Impure LCNF Modules for Stage B Verification Gates -/

lcnf_of_lean! codec0DecodeLcMod [decodeMod0]
lcnf_of_lean! codec0LcMod [encodeMod0, decodeMod0]

end LeanQbe.T.Bootstrap0
