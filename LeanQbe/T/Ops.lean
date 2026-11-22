module

public import LeanQbe.T.Ty
public import Kraken.Mem

/-!
# Target-neutral typed operations and partial memory

* Operands `Arg V t` (`var` or `imm`), operation structures `Op V rs` pairing a signature-indexed
  `OpCode as rs` with an operand tuple `Tup (Arg V) as`.
* Multi-result target-neutral `OpCode` covering §0 scalar/vector/shuffle/SHA/float opcodes plus
  semantics-only opcodes (full integer/FP/conversion suite). `cmp`, `fcmp`, and `blend` carry
  `(m : Ty := t.mask) (h : m = t.mask := by rfl)` (variant C) so `deriving DecidableEq` succeeds.
* **Relational** `OpCode.wp` (`UB = False`, `unspecified = ∀`), using Lean's `Float.Model` for
  IEEE floating-point operations (leaving NaN results nondeterministic).
* Partial memory `loadVal`, `storeOk`, `storeMem` over `Kraken.Mem 64`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Operands -/

/-- An operand: a variable or a typed immediate. -/
inductive Arg (V : Ty → Type) (t : Ty) : Type
  | var (v : V t)
  | imm (c : Val t)

/-- Value of a concrete operand. -/
def Arg.val {t : Ty} : Arg Val t → Val t
  | .var v => v
  | .imm c => c

/-- Rename variables inside an operand. -/
def Arg.mapV {V W : Ty → Type} (f : ∀ t, V t → W t) {t : Ty} : Arg V t → Arg W t
  | .var v => .var (f t v)
  | .imm c => .imm c

/-- Variables mentioned by an operand. -/
def Arg.vars {V : Ty → Type} {t : Ty} : Arg V t → List ((u : Ty) × V u)
  | .var v => [⟨t, v⟩]
  | .imm _ => []

@[inline] instance {V : Ty → Type} {t : Ty} [DecidableEq (V t)] : DecidableEq (Arg V t)
  | .var x, .var y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .imm x, .imm y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .var _, .imm _ => isFalse (fun e => by cases e)
  | .imm _, .var _ => isFalse (fun e => by cases e)

instance {V : Ty → Type} {t : Ty} : Inhabited (Arg V t) := ⟨.imm default⟩

instance {V : Ty → Type} {t : Ty} [Repr (V t)] : Repr (Arg V t) where
  reprPrec
    | .var v, p => Repr.addAppParen ("Arg.var " ++ reprArg v) p
    | .imm c, p => Repr.addAppParen ("Arg.imm " ++ reprArg c) p

/-! ## Comparison predicates and `OpCode` -/

/-- Integer comparison predicates. -/
inductive CmpOp
  | eq | ne | ult | ule | ugt | uge | slt | sle | sgt | sge
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Flip an integer comparison predicate so `b (o.swap) a = a o b`. -/
def CmpOp.swap : CmpOp → CmpOp
  | .eq => .eq | .ne => .ne
  | .ult => .ugt | .ule => .uge | .ugt => .ult | .uge => .ule
  | .slt => .sgt | .sle => .sge | .sgt => .slt | .sge => .sle

/-- Negate an integer comparison predicate so `a (o.neg) b = !(a o b)`. -/
def CmpOp.neg : CmpOp → CmpOp
  | .eq => .ne | .ne => .eq
  | .ult => .uge | .ule => .ugt | .ugt => .ule | .uge => .ult
  | .slt => .sge | .sle => .sgt | .sgt => .sle | .sge => .slt

/-- IEEE floating-point comparison predicates.
`eq`, `lt`, `le`, `gt`, `ge` are ordered (returning `false` if either operand is NaN);
`ne` is unordered-or-not-equal (`true` on `lt`, `gt`, or when either operand is NaN, matching
IEEE/C `!=`); `ord` is true iff neither operand is NaN; `uno` is true iff either is NaN. -/
inductive FCmpOp
  | eq | ne | lt | le | gt | ge | ord | uno
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Target-neutral opcodes indexed by operand and result type lists. -/
inductive OpCode : List Ty → List Ty → Type
  /-- Pure copy / identity. -/
  | copy (t : Ty) : OpCode [t] [t]
  /-- Integer arithmetic (leaf-wise on pairs/vectors; UB on floats). -/
  | add (t : Ty) : OpCode [t, t] [t]
  | sub (t : Ty) : OpCode [t, t] [t]
  | mul (t : Ty) : OpCode [t, t] [t]
  | neg (t : Ty) : OpCode [t] [t]
  /-- Bitwise logic (leaf-wise on any type, including floats). -/
  | and (t : Ty) : OpCode [t, t] [t]
  | or (t : Ty) : OpCode [t, t] [t]
  | xor (t : Ty) : OpCode [t, t] [t]
  | not (t : Ty) : OpCode [t] [t]
  /-- 3-input bitwise function with truth table `imm` (`vpternlogd`). -/
  | ternlog (t : Ty) (imm : BitVec 8) : OpCode [t, t, t] [t]
  /-- Shifts and rotates (count masked to leaf bit width; UB on floats). -/
  | shl (t : Ty) : OpCode [t, t] [t]
  | lshr (t : Ty) : OpCode [t, t] [t]
  | ashr (t : Ty) : OpCode [t, t] [t]
  | rotl (t : Ty) : OpCode [t, t] [t]
  | rotr (t : Ty) : OpCode [t, t] [t]
  /-- Funnel shifts: `fshl hi lo c` / `fshr hi lo c` (`shld`/`shrd`/`EXTR`). -/
  | fshl (n : Nat) : OpCode [.bits n, .bits n, .bits n] [.bits n]
  | fshr (n : Nat) : OpCode [.bits n, .bits n, .bits n] [.bits n]
  /-- Bit and byte permutations. -/
  | bswap (t : Ty) : OpCode [t] [t]
  | clz (n : Nat) : OpCode [.bits n] [.bits n]
  | cls (n : Nat) : OpCode [.bits n] [.bits n]
  | rbit (n : Nat) : OpCode [.bits n] [.bits n]
  | ctz (n : Nat) : OpCode [.bits n] [.bits n]
  | popcnt (n : Nat) : OpCode [.bits n] [.bits n]
  /-- Leaf-wise integer comparisons, returning a mask of `bool`s. -/
  | cmp (o : CmpOp) (t : Ty) (m : Ty := t.mask) (h : m = t.mask := by rfl) : OpCode [t, t] [m]
  /-- Scalar conditional select (`cmovcc`/`CSEL`). -/
  | select (t : Ty) : OpCode [.bool, t, t] [t]
  /-- Lane-wise select on a mask tree (variant C for `DecidableEq`). -/
  | blend (t : Ty) (m : Ty := t.mask) (h : m = t.mask := by rfl) : OpCode [m, t, t] [t]
  /-- Integer width extensions, truncations, and boolean materialisation.
  `zext`/`sext` require `m ≤ n` and `trunc` requires `n ≤ m`; wrong directions are UB (`False`). -/
  | zext (m n : Nat) : OpCode [.bits m] [.bits n]
  | sext (m n : Nat) : OpCode [.bits m] [.bits n]
  | trunc (m n : Nat) : OpCode [.bits m] [.bits n]
  | ofBool (n : Nat) : OpCode [.bool] [.bits n]
  /-- Multi-result carry arithmetic (`adc`/`sbb`/`adcx`/`adox`/`ADCS`/`SBCS`). -/
  | addc (n : Nat) : OpCode [.bits n, .bits n, .bool] [.bits n, .bool]
  | subb (n : Nat) : OpCode [.bits n, .bits n, .bool] [.bits n, .bool]
  /-- Full double-width multiplication (`mul`/`mulx`/`MUL`+`UMULH`/`SMULH`). -/
  | umulw (n : Nat) : OpCode [.bits n, .bits n] [.bits n, .bits n]
  | smulw (n : Nat) : OpCode [.bits n, .bits n] [.bits n, .bits n]
  /-- UB division/remainder (`False` on zero divisor or signed `intMin / -1`). -/
  | udiv (n : Nat) : OpCode [.bits n, .bits n] [.bits n]
  | sdiv (n : Nat) : OpCode [.bits n, .bits n] [.bits n]
  | urem (n : Nat) : OpCode [.bits n, .bits n] [.bits n]
  | srem (n : Nat) : OpCode [.bits n, .bits n] [.bits n]
  /-- Hardware-total division matching AArch64 `UDIV`/`SDIV` (`x / 0 = 0`). -/
  | udiv0 (n : Nat) : OpCode [.bits n, .bits n] [.bits n]
  | sdiv0 (n : Nat) : OpCode [.bits n, .bits n] [.bits n]
  /-- Pair construction, projection, and bitcast. -/
  | mkpair (a b : Ty) : OpCode [a, b] [.pair a b]
  | unpair (a b : Ty) : OpCode [.pair a b] [a, b]
  | bitcast (t u : Ty) (h : t.size = u.size) : OpCode [t] [u]
  /-- x64 128-bit-lane shuffles and blends (`pshufd`/`pshufb`/`palignr`/`pblendw`). -/
  | shufd (t : Ty) (imm : BitVec 8) : OpCode [t] [t]
  | shufb (t : Ty) : OpCode [t, t] [t]
  | alignr (t : Ty) (imm : BitVec 8) : OpCode [t, t] [t]
  | blendw (t : Ty) (imm : BitVec 8) : OpCode [t, t] [t]
  /-- SHA-256 round / message-schedule opcodes (`sha256rnds2`/`sha256msg1`/`sha256msg2`). -/
  | sha256rnds2 : OpCode [v4i32, v4i32, v4i32] [v4i32]
  | sha256msg1 : OpCode [v4i32, v4i32] [v4i32]
  | sha256msg2 : OpCode [v4i32, v4i32] [v4i32]
  /-- IEEE floating-point operations (leaf-wise on float trees; NaN payloads unspecified). -/
  | fadd (t : Ty) : OpCode [t, t] [t]
  | fsub (t : Ty) : OpCode [t, t] [t]
  | fmul (t : Ty) : OpCode [t, t] [t]
  | fdiv (t : Ty) : OpCode [t, t] [t]
  | ffma (t : Ty) : OpCode [t, t, t] [t]
  | fsqrt (t : Ty) : OpCode [t] [t]
  | fneg (t : Ty) : OpCode [t] [t]
  | fabs (t : Ty) : OpCode [t] [t]
  | fcmp (o : FCmpOp) (t : Ty) (m : Ty := t.mask) (h : m = t.mask := by rfl) : OpCode [t, t] [m]
  /-- Float-to-unsigned-int truncation toward zero. UB (`False`) on NaN, `±∞`, or truncated
  integer outside `[0, 2^n)` (note values in `(-1, 0)` truncate to `0` and are defined). -/
  | fptoui (f : Fmt) (n : Nat) : OpCode [.float f] [.bits n]
  /-- Float-to-signed-int truncation toward zero. UB (`False`) when `n = 0`, on NaN/`±∞`, or on
  truncated integer outside `[-(2^(n-1)), 2^(n-1))`. -/
  | fptosi (f : Fmt) (n : Nat) : OpCode [.float f] [.bits n]
  | uitofp (n : Nat) (f : Fmt) : OpCode [.bits n] [.float f]
  | sitofp (n : Nat) (f : Fmt) : OpCode [.bits n] [.float f]
  | fcvt (f g : Fmt) : OpCode [.float f] [.float g]
  deriving DecidableEq

/-- Convenience wrappers for integer comparison opcodes. -/
@[reducible] def OpCode.eq (t : Ty) : OpCode [t, t] [t.mask] := .cmp .eq t
@[reducible] def OpCode.ne (t : Ty) : OpCode [t, t] [t.mask] := .cmp .ne t
@[reducible] def OpCode.ult (t : Ty) : OpCode [t, t] [t.mask] := .cmp .ult t
@[reducible] def OpCode.ule (t : Ty) : OpCode [t, t] [t.mask] := .cmp .ule t
@[reducible] def OpCode.ugt (t : Ty) : OpCode [t, t] [t.mask] := .cmp .ugt t
@[reducible] def OpCode.uge (t : Ty) : OpCode [t, t] [t.mask] := .cmp .uge t
@[reducible] def OpCode.slt (t : Ty) : OpCode [t, t] [t.mask] := .cmp .slt t
@[reducible] def OpCode.sle (t : Ty) : OpCode [t, t] [t.mask] := .cmp .sle t
@[reducible] def OpCode.sgt (t : Ty) : OpCode [t, t] [t.mask] := .cmp .sgt t
@[reducible] def OpCode.sge (t : Ty) : OpCode [t, t] [t.mask] := .cmp .sge t

/-! ## Operation wrapper and builders -/

/-- An operation with its operand tuple; `rs` are its result types. -/
structure Op (V : Ty → Type) (rs : List Ty) : Type where
  {sig : List Ty}
  code : OpCode sig rs
  args : Tup (Arg V) sig

def op1 {V : Ty → Type} {t : Ty} {rs : List Ty} (c : OpCode [t] rs) (a : Arg V t) : Op V rs :=
  ⟨c, (a, ())⟩

def op2 {V : Ty → Type} {t u : Ty} {rs : List Ty} (c : OpCode [t, u] rs) (a : Arg V t)
    (b : Arg V u) : Op V rs :=
  ⟨c, (a, b, ())⟩

def op3 {V : Ty → Type} {t u w : Ty} {rs : List Ty} (c : OpCode [t, u, w] rs) (a : Arg V t)
    (b : Arg V u) (d : Arg V w) : Op V rs :=
  ⟨c, (a, b, d, ())⟩

/-- Evaluate a tuple of concrete operands. -/
def vals : {ts : List Ty} → Tup (Arg Val) ts → Tup Val ts
  | [], () => ()
  | _ :: _, (a, as) => (a.val, vals as)

/-- Map a variable renaming across all operands of `op`. -/
def Op.mapV {V W : Ty → Type} (f : ∀ t, V t → W t) {rs : List Ty} (op : Op V rs) : Op W rs :=
  ⟨op.code, op.args.map (fun _ a => a.mapV f)⟩

def tupVars {V : Ty → Type} : {ts : List Ty} → Tup (Arg V) ts → List ((t : Ty) × V t)
  | [], () => []
  | _ :: _, (a, as) => a.vars ++ tupVars as

/-- All variables referenced by `op`. -/
def Op.vars {V : Ty → Type} {rs : List Ty} (op : Op V rs) : List ((t : Ty) × V t) :=
  tupVars op.args

/-! ## Semantic helpers -/

/-- Lift a binary operation leaf-wise over `Val t`. -/
def lift2 (f : ∀ {n}, BitVec n → BitVec n → BitVec n) (g : Bool → Bool → Bool) :
    (t : Ty) → Val t → Val t → Val t
  | .bool, a, b => g a b
  | .bits _, a, b => f a b
  | .float _, a, b => f a b
  | .pair s u, a, b => (lift2 f g s a.1 b.1, lift2 f g u a.2 b.2)

/-- Lift a unary operation leaf-wise over `Val t`. -/
def lift1 (f : ∀ {n}, BitVec n → BitVec n) (g : Bool → Bool) : (t : Ty) → Val t → Val t
  | .bool, a => g a
  | .bits _, a => f a
  | .float _, a => f a
  | .pair s u, a => (lift1 f g s a.1, lift1 f g u a.2)

/-- Lift a 3-argument bitwise operation leaf-wise over `Val t`. -/
def lift3 (f : ∀ {n}, BitVec n → BitVec n → BitVec n → BitVec n)
    (g : Bool → Bool → Bool → Bool) : (t : Ty) → Val t → Val t → Val t → Val t
  | .bool, a, b, c => g a b c
  | .bits _, a, b, c => f a b c
  | .float _, a, b, c => f a b c
  | .pair s u, a, b, c => (lift3 f g s a.1 b.1 c.1, lift3 f g u a.2 b.2 c.2)

/-- Lift a comparison leaf-wise over `Val t`, returning `Val t.mask`. -/
def liftCmp (f : ∀ {n}, BitVec n → BitVec n → Bool) (g : Bool → Bool → Bool) :
    (t : Ty) → Val t → Val t → Val t.mask
  | .bool, a, b => g a b
  | .bits _, a, b => f a b
  | .float _, a, b => f a b
  | .pair s u, a, b => (liftCmp f g s a.1 b.1, liftCmp f g u a.2 b.2)

/-- Lane-wise select on a mask tree. -/
def blendV : (t : Ty) → Val t.mask → Val t → Val t → Val t
  | .bool, c, a, b => if c then a else b
  | .bits _, c, a, b => if c then a else b
  | .float _, c, a, b => if c then a else b
  | .pair s u, c, a, b => (blendV s c.1 a.1 b.1, blendV u c.2 a.2 b.2)

def CmpOp.evalBits {n : Nat} : CmpOp → BitVec n → BitVec n → Bool
  | .eq, a, b => decide (a = b)
  | .ne, a, b => decide (a ≠ b)
  | .ult, a, b => a.ult b
  | .ule, a, b => a.ule b
  | .ugt, a, b => b.ult a
  | .uge, a, b => b.ule a
  | .slt, a, b => a.slt b
  | .sle, a, b => a.sle b
  | .sgt, a, b => b.slt a
  | .sge, a, b => b.sle a

def CmpOp.evalBool : CmpOp → Bool → Bool → Bool
  | .eq, a, b => decide (a = b)
  | .ne, a, b => decide (a ≠ b)
  | .ult, a, b => !a && b
  | .ule, a, b => !a || b
  | .ugt, a, b => a && !b
  | .uge, a, b => a || !b
  | .slt, a, b => a && !b
  | .sle, a, b => a || !b
  | .sgt, a, b => !a && b
  | .sge, a, b => !a || b

/-- Reverse the `w / 8` bytes of `x`. -/
def bswapBits {w : Nat} (x : BitVec w) : BitVec w :=
  let n := w / 8
  (go n).setWidth w
where go : (n : Nat) → BitVec (8 * n)
  | 0 => 0#0
  | n + 1 => (go n ++ x.extractLsb' (8 * n) 8).cast (by omega)

/-- Bitwise ternary logic (`vpternlogd` truth table). -/
def ternaryLogic {w : Nat} (a b c : BitVec w) (imm : BitVec 8) : BitVec w :=
  let pick (bit : Bool) (v : BitVec w) := if bit then v else ~~~v
  (List.range 8).foldl (fun acc k =>
    if imm.getLsbD k then
      acc ||| (pick (k / 4 % 2 == 1) a &&& pick (k / 2 % 2 == 1) b &&& pick (k % 2 == 1) c)
    else acc) 0#w

def ternaryLogicBool (a b c : Bool) (imm : BitVec 8) : Bool :=
  imm.getLsbD (4 * a.toNat + 2 * b.toNat + c.toNat)

/-- `sdivDefined a b` holds iff `b ≠ 0` and `(a, b) ≠ (intMin, -1)`. -/
def sdivDefined {n : Nat} (a b : BitVec n) : Bool :=
  b != 0 && !(a == BitVec.intMin n && b == BitVec.allOnes n)

/-- Lane `i` of `v`, cut into `c`-bit lanes from the least significant end. -/
def bvLane {w : Nat} (c i : Nat) (v : BitVec w) : BitVec c :=
  v.extractLsb' (c * i) c

/-- Assemble a `w`-bit vector from `c`-bit lane function `f`. -/
def bvOfLanes (w c : Nat) (f : Nat → BitVec c) : BitVec w :=
  (List.range (w / c)).foldl (fun acc i => acc ||| ((f i).setWidth w <<< (c * i))) 0#w

/-- Per 16-byte block dword shuffle (`pshufd`). -/
def shuffleDwords {w : Nat} (a : BitVec w) (imm : BitVec 8) : BitVec w :=
  bvOfLanes w 32 fun i => bvLane 32 (4 * (i / 4) + (imm.toNat >>> (2 * (i % 4))) % 4) a

/-- Per 16-byte block byte shuffle (`pshufb`). -/
def shuffleBytes {w : Nat} (a m : BitVec w) : BitVec w :=
  bvOfLanes w 8 fun i =>
    let index := bvLane 8 i m
    if index.msb then 0#8 else bvLane 8 (16 * (i / 16) + index.toNat % 16) a

/-- Per 16-byte block byte shift-right over `(hi, lo)` (`palignr`). -/
def alignBytes {w : Nat} (hi lo : BitVec w) (imm : BitVec 8) : BitVec w :=
  bvOfLanes w 8 fun i =>
    let j := i % 16 + imm.toNat
    if j < 16 then bvLane 8 (16 * (i / 16) + j) lo
    else if j < 32 then bvLane 8 (16 * (i / 16) + j - 16) hi
    else 0#8

/-- Per 16-bit word select controlled by `imm` bits mod 8 (`pblendw`). -/
def blendWords {w : Nat} (a b : BitVec w) (imm : BitVec 8) : BitVec w :=
  bvOfLanes w 16 fun i => if imm.getLsbD (i % 8) then bvLane 16 i b else bvLane 16 i a

namespace Sha256

def «Σ₀» (x : BitVec 32) : BitVec 32 := x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22
def «Σ₁» (x : BitVec 32) : BitVec 32 := x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25
def σ₀ (x : BitVec 32) : BitVec 32 := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> 3
def σ₁ (x : BitVec 32) : BitVec 32 := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ x >>> 10
def ch (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (~~~x &&& z)
def maj (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

structure State where
  (a b c d e f g h : BitVec 32)

def State.round (s : State) (wk : BitVec 32) : State :=
  let t := ch s.e s.f s.g + «Σ₁» s.e + wk + s.h
  ⟨t + maj s.a s.b s.c + «Σ₀» s.a, s.a, s.b, s.c, t + s.d, s.e, s.f, s.g⟩

def rounds2 (cdgh abef wk : BitVec 128) : BitVec 128 :=
  let s : State := ⟨bvLane 32 3 abef, bvLane 32 2 abef, bvLane 32 3 cdgh, bvLane 32 2 cdgh,
    bvLane 32 1 abef, bvLane 32 0 abef, bvLane 32 1 cdgh, bvLane 32 0 cdgh⟩
  let s1 := s.round (bvLane 32 0 wk)
  let s2 := s1.round (bvLane 32 1 wk)
  bvOfLanes 128 32 fun | 0 => s1.e | 1 => s2.e | 2 => s1.a | _ => s2.a

def msg1 (w0123 w4 : BitVec 128) : BitVec 128 :=
  bvOfLanes 128 32 fun i =>
    bvLane 32 i w0123 + σ₀ (if i < 3 then bvLane 32 (i + 1) w0123 else bvLane 32 0 w4)

def msg2 (sums w : BitVec 128) : BitVec 128 :=
  let w16 := bvLane 32 0 sums + σ₁ (bvLane 32 2 w)
  let w17 := bvLane 32 1 sums + σ₁ (bvLane 32 3 w)
  let w18 := bvLane 32 2 sums + σ₁ w16
  let w19 := bvLane 32 3 sums + σ₁ w17
  bvOfLanes 128 32 fun | 0 => w16 | 1 => w17 | 2 => w18 | _ => w19

end Sha256

/-! ## IEEE floating-point helpers via `Float.Model` -/

/-- `Float.Model.Format` corresponding to `Fmt`. -/
@[reducible] def Fmt.format : Fmt → Float.Model.Format
  | .h => ⟨10, by decide, 5, by decide⟩
  | .s => Float.Model.Format.binary32
  | .d => Float.Model.Format.binary64
  | .q => ⟨112, by decide, 15, by decide⟩

theorem Fmt.format_numBits (f : Fmt) : f.format.numBits = f.width := by
  cases f <;> rfl

def unpackFloat (f : Fmt) (x : BitVec f.width) : Float.Model.UnpackedFloat :=
  Float.Model.UnpackedFloat.unpack f.format (x.cast (Fmt.format_numBits f).symm)

def packFloat (f : Fmt) (u : Float.Model.UnpackedFloat) : BitVec f.width :=
  (Float.Model.UnpackedFloat.pack f.format u).cast (Fmt.format_numBits f)

/-- True iff the bit representation encodes a NaN in format `f`. -/
def isFloatNaN (f : Fmt) (r : BitVec f.width) : Bool :=
  (unpackFloat f r).isNaN

/-- Relational continuation for a float leaf: NaNs are universally quantified (any NaN encoding),
while non-NaN results are deterministic. -/
def floatResultWp (f : Fmt) (res : Float.Model.UnpackedFloat) (k : BitVec f.width → Prop) : Prop :=
  if res.isNaN then ∀ r : BitVec f.width, isFloatNaN f r = true → k r
  else k (packFloat f res)

def liftFloatRel1 (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    (t : Ty) → Val t → (Val t → Prop) → Prop
  | .float f, a, k => floatResultWp f (op f.format (unpackFloat f a)) k
  | .pair s u, a, k =>
    liftFloatRel1 op s a.1 fun r1 => liftFloatRel1 op u a.2 fun r2 => k (r1, r2)
  | _, _, _ => False

def liftFloatRel2 (op : Float.Model.Format → Float.Model.UnpackedFloat →
    Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    (t : Ty) → Val t → Val t → (Val t → Prop) → Prop
  | .float f, a, b, k =>
    floatResultWp f (op f.format (unpackFloat f a) (unpackFloat f b)) k
  | .pair s u, a, b, k =>
    liftFloatRel2 op s a.1 b.1 fun r1 => liftFloatRel2 op u a.2 b.2 fun r2 => k (r1, r2)
  | _, _, _, _ => False

def liftFloatRel3 (op : Float.Model.Format → Float.Model.UnpackedFloat →
    Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    (t : Ty) → Val t → Val t → Val t → (Val t → Prop) → Prop
  | .float f, a, b, c, k =>
    floatResultWp f (op f.format (unpackFloat f a) (unpackFloat f b) (unpackFloat f c)) k
  | .pair s u, a, b, c, k =>
    liftFloatRel3 op s a.1 b.1 c.1 fun r1 =>
      liftFloatRel3 op u a.2 b.2 c.2 fun r2 => k (r1, r2)
  | _, _, _, _, _ => False

/-- Leaf IEEE comparison: `eq`/`lt`/`le`/`gt`/`ge` are ordered (`false` on NaN); `ne` is
unordered-or-not-equal (`true` on `lt`, `gt`, or NaN). -/
def fcmpLeaf (o : FCmpOp) (f : Fmt) (a b : BitVec f.width) : Bool :=
  let c := Float.Model.UnpackedFloat.compare (unpackFloat f a) (unpackFloat f b)
  match o, c with
  | .eq, some .eq => true
  | .ne, some .lt | .ne, some .gt | .ne, none => true
  | .lt, some .lt => true
  | .le, some .lt | .le, some .eq => true
  | .gt, some .gt => true
  | .ge, some .gt | .ge, some .eq => true
  | .ord, some _ => true
  | .uno, none => true
  | _, _ => false

def liftFCmp (o : FCmpOp) : (t : Ty) → Val t → Val t → Val t.mask
  | .bool, _, _ => false
  | .bits _, _, _ => false
  | .float f, a, b => fcmpLeaf o f a b
  | .pair s u, a, b => (liftFCmp o s a.1 b.1, liftFCmp o u a.2 b.2)

/-- Truncate a finite/zero unpacked float toward zero; `none` for NaN/Inf. -/
def truncToInt : Float.Model.UnpackedFloat → Option Int
  | .zero _ => some 0
  | .finite s m e _ =>
    let absVal : Nat := if 0 ≤ e then m * 2 ^ e.toNat else m / 2 ^ (-e).toNat
    some (s.apply absVal)
  | _ => none

/-- Cast a non-NaN unpacked float to format `dst`. -/
def convertFloat (src dst : Fmt) (b : BitVec src.width) (k : BitVec dst.width → Prop) : Prop :=
  match unpackFloat src b with
  | .notANumber => ∀ r : BitVec dst.width, isFloatNaN dst r = true → k r
  | .finite s m e _ =>
    k (packFloat dst (Float.Model.UnpackedFloat.round dst.format s m e))
  | u => k (packFloat dst u)

/-! ## Relational `OpCode.wp` and `Op.wp` -/

/-- Relational weakest-precondition semantics of `OpCode`.
Undefined behaviour is `False`; unspecified results (such as NaN payloads) quantify `∀`. -/
def OpCode.wp : {as rs : List Ty} → OpCode as rs → Tup Val as → (Tup Val rs → Prop) → Prop
  | _, _, .copy _, (a, ()), post => post (a, ())
  | _, _, .add t, (a, b, ()), post =>
      if t.hasFloat then False else post (lift2 (· + ·) (· ^^ ·) t a b, ())
  | _, _, .sub t, (a, b, ()), post =>
      if t.hasFloat then False else post (lift2 (· - ·) (· ^^ ·) t a b, ())
  | _, _, .mul t, (a, b, ()), post =>
      if t.hasFloat then False else post (lift2 (· * ·) (· && ·) t a b, ())
  | _, _, .neg t, (a, ()), post =>
      if t.hasFloat then False else post (lift1 (- ·) id t a, ())
  | _, _, .and t, (a, b, ()), post => post (lift2 (· &&& ·) (· && ·) t a b, ())
  | _, _, .or t, (a, b, ()), post => post (lift2 (· ||| ·) (· || ·) t a b, ())
  | _, _, .xor t, (a, b, ()), post => post (lift2 (· ^^^ ·) (· ^^ ·) t a b, ())
  | _, _, .not t, (a, ()), post => post (lift1 (~~~ ·) (! ·) t a, ())
  | _, _, .ternlog t imm, (a, b, c, ()), post =>
      post (lift3 (fun x y z => ternaryLogic x y z imm)
        (fun x y z => ternaryLogicBool x y z imm) t a b c, ())
  | _, _, .shl t, (a, b, ()), post =>
      if t.hasFloat then False
      else post (lift2 (fun {n} x y => x <<< (y.toNat % n)) (fun x _ => x) t a b, ())
  | _, _, .lshr t, (a, b, ()), post =>
      if t.hasFloat then False
      else post (lift2 (fun {n} x y => x >>> (y.toNat % n)) (fun x _ => x) t a b, ())
  | _, _, .ashr t, (a, b, ()), post =>
      if t.hasFloat then False
      else post (lift2 (fun {n} x y => x.sshiftRight (y.toNat % n)) (fun x _ => x) t a b, ())
  | _, _, .rotl t, (a, b, ()), post =>
      if t.hasFloat then False
      else post (lift2 (fun {n} x y => x.rotateLeft (y.toNat % n)) (fun x _ => x) t a b, ())
  | _, _, .rotr t, (a, b, ()), post =>
      if t.hasFloat then False
      else post (lift2 (fun {n} x y => x.rotateRight (y.toNat % n)) (fun x _ => x) t a b, ())
  | _, _, .fshl n, (a, b, c, ()), post =>
      post ((((a ++ b) <<< (c.toNat % n)).extractLsb' n n), ())
  | _, _, .fshr n, (a, b, c, ()), post =>
      post ((((a ++ b) >>> (c.toNat % n)).extractLsb' 0 n), ())
  | _, _, .bswap t, (a, ()), post =>
      if !t.bswapOk then False else post (lift1 bswapBits id t a, ())
  | _, _, .clz _, (a, ()), post => post (a.clz, ())
  | _, _, .cls n, (a, ()), post => post ((if a.msb then (~~~a).clz else a.clz) - 1#n, ())
  | _, _, .rbit _, (a, ()), post => post (a.reverse, ())
  | _, _, .ctz _, (a, ()), post => post (a.reverse.clz, ())
  | _, _, .popcnt _, (a, ()), post => post (a.cpop, ())
  | _, _, .cmp o t _ rfl, (a, b, ()), post =>
      if t.hasFloat then False else post (liftCmp o.evalBits o.evalBool t a b, ())
  | _, _, .select _, (c, a, b, ()), post => post (if c then a else b, ())
  | _, _, .blend t _ rfl, (c, a, b, ()), post => post (blendV t c a b, ())
  | _, _, .zext m n, (a, ()), post => m ≤ n ∧ post (a.setWidth n, ())
  | _, _, .sext m n, (a, ()), post => m ≤ n ∧ post (a.signExtend n, ())
  | _, _, .trunc m n, (a, ()), post => n ≤ m ∧ post (a.setWidth n, ())
  | _, _, .ofBool n, (c, ()), post => post (BitVec.ofNat n c.toNat, ())
  | _, _, .addc n, (a, b, c, ()), post =>
      post (a + b + BitVec.ofNat n c.toNat, decide (2 ^ n ≤ a.toNat + b.toNat + c.toNat), ())
  | _, _, .subb n, (a, b, c, ()), post =>
      post (a - b - BitVec.ofNat n c.toNat, decide (a.toNat < b.toNat + c.toNat), ())
  | _, _, .umulw n, (a, b, ()), post =>
      post (a * b, BitVec.ofNat n (a.toNat * b.toNat / 2 ^ n), ())
  | _, _, .smulw n, (a, b, ()), post =>
      post (a * b, (BitVec.ofInt (n + n) (a.toInt * b.toInt)).extractLsb' n n, ())
  | _, _, .udiv _, (a, b, ()), post => b ≠ 0 ∧ post (a / b, ())
  | _, _, .sdiv _, (a, b, ()), post => sdivDefined a b = true ∧ post (a.sdiv b, ())
  | _, _, .urem _, (a, b, ()), post => b ≠ 0 ∧ post (a % b, ())
  | _, _, .srem _, (a, b, ()), post => sdivDefined a b = true ∧ post (a.srem b, ())
  | _, _, .udiv0 _, (a, b, ()), post => post (if b = 0 then 0 else a / b, ())
  | _, _, .sdiv0 _, (a, b, ()), post => post (if b = 0 then 0 else a.sdiv b, ())
  | _, _, .mkpair _ _, (a, b, ()), post => post ((a, b), ())
  | _, _, .unpair _ _, (p, ()), post => post (p.1, p.2, ())
  | _, _, .bitcast t u h, (a, ()), post => post (ofBits u ((toBits t a).cast h), ())
  | _, _, .shufd t imm, (a, ()), post =>
      t.size ≠ 0 ∧ t.size % 128 = 0 ∧ post (ofBits t (shuffleDwords (toBits t a) imm), ())
  | _, _, .shufb t, (a, m, ()), post =>
      t.size ≠ 0 ∧ t.size % 128 = 0 ∧
        post (ofBits t (shuffleBytes (toBits t a) (toBits t m)), ())
  | _, _, .alignr t imm, (hi, lo, ()), post =>
      t.size ≠ 0 ∧ t.size % 128 = 0 ∧
        post (ofBits t (alignBytes (toBits t hi) (toBits t lo) imm), ())
  | _, _, .blendw t imm, (a, b, ()), post =>
      t.size ≠ 0 ∧ t.size % 128 = 0 ∧
        post (ofBits t (blendWords (toBits t a) (toBits t b) imm), ())
  | _, _, .sha256rnds2, (cdgh, abef, wk, ()), post =>
      post (ofBits v4i32
        (Sha256.rounds2 (toBits v4i32 cdgh) (toBits v4i32 abef) (toBits v4i32 wk)), ())
  | _, _, .sha256msg1, (w0123, w4, ()), post =>
      post (ofBits v4i32 (Sha256.msg1 (toBits v4i32 w0123) (toBits v4i32 w4)), ())
  | _, _, .sha256msg2, (sums, w, ()), post =>
      post (ofBits v4i32 (Sha256.msg2 (toBits v4i32 sums) (toBits v4i32 w)), ())
  | _, _, .fadd t, (a, b, ()), post =>
      if !t.isFloatTree then False
      else liftFloatRel2 Float.Model.UnpackedFloat.add t a b fun r => post (r, ())
  | _, _, .fsub t, (a, b, ()), post =>
      if !t.isFloatTree then False
      else liftFloatRel2 Float.Model.UnpackedFloat.sub t a b fun r => post (r, ())
  | _, _, .fmul t, (a, b, ()), post =>
      if !t.isFloatTree then False
      else liftFloatRel2 Float.Model.UnpackedFloat.mul t a b fun r => post (r, ())
  | _, _, .fdiv t, (a, b, ()), post =>
      if !t.isFloatTree then False
      else liftFloatRel2 Float.Model.UnpackedFloat.div t a b fun r => post (r, ())
  | _, _, .ffma t, (a, b, c, ()), post =>
      if !t.isFloatTree then False
      else liftFloatRel3 Float.Model.UnpackedFloat.fma t a b c fun r => post (r, ())
  | _, _, .fsqrt t, (a, ()), post =>
      if !t.isFloatTree then False
      else liftFloatRel1 Float.Model.UnpackedFloat.sqrt t a fun r => post (r, ())
  | _, _, .fneg t, (a, ()), post =>
      if !t.isFloatTree then False
      else post (lift1 (fun {n} x => x ^^^ (1#n <<< (n - 1))) id t a, ())
  | _, _, .fabs t, (a, ()), post =>
      if !t.isFloatTree then False
      else post (lift1 (fun {n} x => x &&& ~~~(1#n <<< (n - 1))) id t a, ())
  | _, _, .fcmp o t _ rfl, (a, b, ()), post =>
      if !t.isFloatTree then False else post (liftFCmp o t a b, ())
  | _, _, .fptoui f n, (a, ()), post =>
      match truncToInt (unpackFloat f a) with
      | some z => 0 ≤ z ∧ z < 2 ^ n ∧ post (BitVec.ofInt n z, ())
      | none => False
  | _, _, .fptosi f n, (a, ()), post =>
      n ≠ 0 ∧ match truncToInt (unpackFloat f a) with
      | some z => -(2 ^ (n - 1) : Int) ≤ z ∧ z < 2 ^ (n - 1) ∧ post (BitVec.ofInt n z, ())
      | none => False
  | _, _, .uitofp _ f, (a, ()), post =>
      post (packFloat f (Float.Model.UnpackedFloat.ofInt f.format a.toNat), ())
  | _, _, .sitofp _ f, (a, ()), post =>
      post (packFloat f (Float.Model.UnpackedFloat.ofInt f.format a.toInt), ())
  | _, _, .fcvt f g, (a, ()), post => convertFloat f g a fun r => post (r, ())

/-- Weakest precondition of an operation applied to concrete/variable operands. -/
def Op.wp {rs : List Ty} (op : Op Val rs) (post : Tup Val rs → Prop) : Prop :=
  op.code.wp (vals op.args) post

/-! ## Partial memory over `Kraken.Mem 64` -/

/-- Load a value of type `t` from address `a` in partial memory `m`.
Returns `none` (UB) if any byte in `[a, a + t.bytes)` is unmapped, or if `t = .bool` and the
loaded byte is not in `{0, 1}` (i.e., `byte > 1`). -/
def loadVal (m : Mem 64) (t : Ty) (a : BitVec 64) : Option (Val t) :=
  (m.loadInt a t.bytes).bind fun i =>
    match t with
    | .bool => if i == 0 || i == 1 then some (i == 1) else none
    | .bits n => some (ofBits (.bits n) (BitVec.ofInt n i))
    | .float f => some (ofBits (.float f) (BitVec.ofInt f.width i))
    | .pair x y => some (ofBits (.pair x y) (BitVec.ofInt (x.size + y.size) i))

/-- Store `v : Val t` at address `a` in little-endian byte order. -/
def storeMem (m : Mem 64) (t : Ty) (a : BitVec 64) (v : Val t) : Mem 64 :=
  m.storeInt a t.bytes ((toBits t v).setWidth (8 * t.bytes)).toInt

/-- A store of `t` at `a` is defined iff all `t.bytes` bytes at `a` are mapped in `m`. -/
def storeOk (m : Mem 64) (t : Ty) (a : BitVec 64) : Prop :=
  ∃ i, m.loadInt a t.bytes = some i

end LeanQbe.T
