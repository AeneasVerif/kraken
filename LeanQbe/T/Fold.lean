module

public import LeanQbe.T.OptUtil

/-!
# Constant folding, trivial-op simplification, algebraic rules, and strength reduction (`T6`)

PHOAS-to-PHOAS optimisation pass `fold : Nat → Expr (FVal V) L rs → Expr V L rs` where
`FVal V t = Arg V t × FKey t` (`FKey t = Arg K t`, `K _ = Nat`): every bound variable carries its
replacement operand `Arg V t` in the output expression and a `V`-independent symbolic key `FKey t`
so equal variables (`a.fkey == b.fkey`) can be detected without `DecidableEq V`.

1. **Constant folding (`OpCode.eval?`)**: evaluates all 64 `OpCode` constructors when all operands
   are immediate and preconditions hold (preserving UB `False` by keeping undefined constant ops).
   For IEEE float operations returning NaN, folds deterministically to the canonical quiet NaN
   `canonNaN f` (`UnpackedFloat.packedNaN`), which refines the universal NaN quantification in `wp`.
2. **Instruction elimination (`Op.simpAct`)**:
   - constant folding (including multi-result ops `addc`, `subb`, `umulw`, `smulw`, `unpair`);
   - `copy t a → a`, `bitcast t t h a → a`, `zext/sext/trunc n n a → a`, `neg .bool a → a`;
   - leaf-wise annihilators, identities, and self-rules across `.bool`, `.bits n`, and non-float
     `pair`/vector trees (`add`, `sub`, `mul`, `and`, `or`, `xor`, `shl`, `lshr`, `ashr`, `rotl`,
     `rotr`, `cmp`, `select`, `blend`, `ternlog`, `addc`, `subb`, `umulw`, `smulw`, `udiv`/`sdiv`,
     `urem`/`srem`, `udiv0`/`sdiv0`).
3. **Strength reduction (`Op.rewrite`)**:
   - leaf-wise power-of-two `mul t a (2^m) → shl t a m` (both operand orders, scalar & vector);
   - power-of-two `udiv n a (2^m) → lshr n a m` and `urem n a (2^m) → and n a (2^m - 1)`.
4. **Static branches**: `jnz (.imm b) t e` keeps only the taken branch.

Correctness (`LeanQbe/T/FoldLemmas.lean`): `fold_wp`, `fold_wf`, `Func.fold_spec`, `Func.fold_wf`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-- Symbolic variable key for detecting equal variables independently of `V`. -/
abbrev FKey (t : Ty) := Arg K t

/-- Input representation of a value in `fold`: replacement operand paired with symbolic key. -/
abbrev FVal (V : Ty → Type) (t : Ty) := Arg V t × FKey t

/-- Output operand of an input operand. -/
def Arg.fout {V : Ty → Type} {t : Ty} : Arg (FVal V) t → Arg V t
  | .var p => p.1
  | .imm c => .imm c

/-- Symbolic key of an input operand. -/
def Arg.fkey {V : Ty → Type} {t : Ty} : Arg (FVal V) t → FKey t
  | .var p => p.2
  | .imm c => .imm c

/-- Pair `(fout, fkey)` of an input operand. -/
def Arg.fpair {V : Ty → Type} {t : Ty} (a : Arg (FVal V) t) : FVal V t := (a.fout, a.fkey)

/-- Constant `FVal` carrying immediate `c`. -/
def fimm {V : Ty → Type} {t : Ty} (c : Val t) : FVal V t := (.imm c, .imm c)

/-- Wrap bound output variables `xs : Tup V ts` into fresh `FVal V`s starting at `next`. -/
abbrev freshFVals {V : Ty → Type} : (ts : List Ty) → Tup V ts → Nat → Tup (FVal V) ts :=
  tupFreshWith fun x next => (.var x, .var next)

/-! ## Canonical quiet NaN and total computable `OpCode` constant evaluator -/

/-- Canonical quiet NaN bit representation in IEEE format `f`. -/
def canonNaN (f : Fmt) : BitVec f.width :=
  (Float.Model.UnpackedFloat.packedNaN f.format).cast (Fmt.format_numBits f)

def evalFloatLeaf1 (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (f : Fmt) (a : BitVec f.width) : BitVec f.width :=
  let res := op f.format (unpackFloat f a)
  if res.isNaN then canonNaN f else packFloat f res

def evalFloatLeaf2 (op : Float.Model.Format → Float.Model.UnpackedFloat →
    Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (f : Fmt) (a b : BitVec f.width) : BitVec f.width :=
  let res := op f.format (unpackFloat f a) (unpackFloat f b)
  if res.isNaN then canonNaN f else packFloat f res

def evalFloatLeaf3 (op : Float.Model.Format → Float.Model.UnpackedFloat →
    Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (f : Fmt) (a b c : BitVec f.width) : BitVec f.width :=
  let res := op f.format (unpackFloat f a) (unpackFloat f b) (unpackFloat f c)
  if res.isNaN then canonNaN f else packFloat f res

def evalFloat1 (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    (t : Ty) → Val t → Option (Val t)
  | .float f, a => some (evalFloatLeaf1 op f a)
  | .pair s u, a => do
    let r1 ← evalFloat1 op s a.1
    let r2 ← evalFloat1 op u a.2
    pure (r1, r2)
  | _, _ => none

def evalFloat2 (op : Float.Model.Format → Float.Model.UnpackedFloat →
    Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    (t : Ty) → Val t → Val t → Option (Val t)
  | .float f, a, b => some (evalFloatLeaf2 op f a b)
  | .pair s u, a, b => do
    let r1 ← evalFloat2 op s a.1 b.1
    let r2 ← evalFloat2 op u a.2 b.2
    pure (r1, r2)
  | _, _, _ => none

def evalFloat3 (op : Float.Model.Format → Float.Model.UnpackedFloat →
    Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    (t : Ty) → Val t → Val t → Val t → Option (Val t)
  | .float f, a, b, c => some (evalFloatLeaf3 op f a b c)
  | .pair s u, a, b, c => do
    let r1 ← evalFloat3 op s a.1 b.1 c.1
    let r2 ← evalFloat3 op u a.2 b.2 c.2
    pure (r1, r2)
  | _, _, _, _ => none

def evalConvertFloat (src dst : Fmt) (b : BitVec src.width) : BitVec dst.width :=
  match unpackFloat src b with
  | .notANumber => canonNaN dst
  | .finite s m e _ => packFloat dst (Float.Model.UnpackedFloat.round dst.format s m e)
  | u => packFloat dst u

/-- Evaluate an `OpCode` on concrete operand values when defined.
Returns `none` on UB so undefined constant operations are kept in the IR.
For float NaN results, returns `canonNaN` as a valid refinement of `OpCode.wp`. -/
def OpCode.eval? : {sig rs : List Ty} → OpCode sig rs → Tup Val sig → Option (Tup Val rs)
  | _, _, .copy _, (a, ()) => some (a, ())
  | _, _, .add t, (a, b, ()) =>
    if t.hasFloat then none else some (lift2 (· + ·) (· ^^ ·) t a b, ())
  | _, _, .sub t, (a, b, ()) =>
    if t.hasFloat then none else some (lift2 (· - ·) (· ^^ ·) t a b, ())
  | _, _, .mul t, (a, b, ()) =>
    if t.hasFloat then none else some (lift2 (· * ·) (· && ·) t a b, ())
  | _, _, .neg t, (a, ()) =>
    if t.hasFloat then none else some (lift1 (- ·) id t a, ())
  | _, _, .and t, (a, b, ()) => some (lift2 (· &&& ·) (· && ·) t a b, ())
  | _, _, .or t, (a, b, ()) => some (lift2 (· ||| ·) (· || ·) t a b, ())
  | _, _, .xor t, (a, b, ()) => some (lift2 (· ^^^ ·) (· ^^ ·) t a b, ())
  | _, _, .not t, (a, ()) => some (lift1 (~~~ ·) (! ·) t a, ())
  | _, _, .ternlog t imm, (a, b, c, ()) =>
    some (lift3 (fun x y z => ternaryLogic x y z imm)
      (fun x y z => ternaryLogicBool x y z imm) t a b c, ())
  | _, _, .shl t, (a, b, ()) =>
    if t.hasFloat then none
    else some (lift2 (fun {n} x y => x <<< (y.toNat % n)) (fun x _ => x) t a b, ())
  | _, _, .lshr t, (a, b, ()) =>
    if t.hasFloat then none
    else some (lift2 (fun {n} x y => x >>> (y.toNat % n)) (fun x _ => x) t a b, ())
  | _, _, .ashr t, (a, b, ()) =>
    if t.hasFloat then none
    else some (lift2 (fun {n} x y => x.sshiftRight (y.toNat % n)) (fun x _ => x) t a b, ())
  | _, _, .rotl t, (a, b, ()) =>
    if t.hasFloat then none
    else some (lift2 (fun {n} x y => x.rotateLeft (y.toNat % n)) (fun x _ => x) t a b, ())
  | _, _, .rotr t, (a, b, ()) =>
    if t.hasFloat then none
    else some (lift2 (fun {n} x y => x.rotateRight (y.toNat % n)) (fun x _ => x) t a b, ())
  | _, _, .fshl n, (a, b, c, ()) =>
    some ((((a ++ b) <<< (c.toNat % n)).extractLsb' n n), ())
  | _, _, .fshr n, (a, b, c, ()) =>
    some ((((a ++ b) >>> (c.toNat % n)).extractLsb' 0 n), ())
  | _, _, .bswap t, (a, ()) =>
    if t.bswapOk then some (lift1 bswapBits id t a, ()) else none
  | _, _, .clz _, (a, ()) => some (a.clz, ())
  | _, _, .cls n, (a, ()) => some ((if a.msb then (~~~a).clz else a.clz) - 1#n, ())
  | _, _, .rbit _, (a, ()) => some (a.reverse, ())
  | _, _, .ctz _, (a, ()) => some (a.reverse.clz, ())
  | _, _, .popcnt _, (a, ()) => some (a.cpop, ())
  | _, _, .cmp o t _ h, (a, b, ()) =>
    if t.hasFloat then none
    else some (cast (congrArg (fun u => Tup Val [u]) h.symm)
      (liftCmp o.evalBits o.evalBool t a b, ()))
  | _, _, .select _, (c, a, b, ()) => some (if c then a else b, ())
  | _, _, .blend t _ h, (c, a, b, ()) =>
    some (blendV t (cast (congrArg Val h) c) a b, ())
  | _, _, .zext m n, (a, ()) => if m ≤ n then some (a.setWidth n, ()) else none
  | _, _, .sext m n, (a, ()) => if m ≤ n then some (a.signExtend n, ()) else none
  | _, _, .trunc m n, (a, ()) => if n ≤ m then some (a.setWidth n, ()) else none
  | _, _, .ofBool n, (c, ()) => some (BitVec.ofNat n c.toNat, ())
  | _, _, .addc n, (a, b, c, ()) =>
    some (a + b + BitVec.ofNat n c.toNat,
      decide (2 ^ n ≤ a.toNat + b.toNat + c.toNat), ())
  | _, _, .subb n, (a, b, c, ()) =>
    some (a - b - BitVec.ofNat n c.toNat,
      decide (a.toNat < b.toNat + c.toNat), ())
  | _, _, .umulw n, (a, b, ()) =>
    some (a * b, BitVec.ofNat n (a.toNat * b.toNat / 2 ^ n), ())
  | _, _, .smulw n, (a, b, ()) =>
    some (a * b, (BitVec.ofInt (n + n) (a.toInt * b.toInt)).extractLsb' n n, ())
  | _, _, .udiv _, (a, b, ()) => if b ≠ 0 then some (a / b, ()) else none
  | _, _, .sdiv _, (a, b, ()) => if sdivDefined a b then some (a.sdiv b, ()) else none
  | _, _, .urem _, (a, b, ()) => if b ≠ 0 then some (a % b, ()) else none
  | _, _, .srem _, (a, b, ()) => if sdivDefined a b then some (a.srem b, ()) else none
  | _, _, .udiv0 _, (a, b, ()) => some (if b = 0 then 0 else a / b, ())
  | _, _, .sdiv0 _, (a, b, ()) => some (if b = 0 then 0 else a.sdiv b, ())
  | _, _, .mkpair _ _, (a, b, ()) => some ((a, b), ())
  | _, _, .unpair _ _, (p, ()) => some (p.1, p.2, ())
  | _, _, .bitcast t u h, (a, ()) => some (ofBits u ((toBits t a).cast h), ())
  | _, _, .shufd t imm, (a, ()) =>
    if t.size ≠ 0 && t.size % 128 == 0 then
      some (ofBits t (shuffleDwords (toBits t a) imm), ())
    else none
  | _, _, .shufb t, (a, m, ()) =>
    if t.size ≠ 0 && t.size % 128 == 0 then
      some (ofBits t (shuffleBytes (toBits t a) (toBits t m)), ())
    else none
  | _, _, .alignr t imm, (hi, lo, ()) =>
    if t.size ≠ 0 && t.size % 128 == 0 then
      some (ofBits t (alignBytes (toBits t hi) (toBits t lo) imm), ())
    else none
  | _, _, .blendw t imm, (a, b, ()) =>
    if t.size ≠ 0 && t.size % 128 == 0 then
      some (ofBits t (blendWords (toBits t a) (toBits t b) imm), ())
    else none
  | _, _, .sha256rnds2, (cdgh, abef, wk, ()) =>
    some (ofBits v4i32
      (Sha256.rounds2 (toBits v4i32 cdgh) (toBits v4i32 abef) (toBits v4i32 wk)), ())
  | _, _, .sha256msg1, (w0123, w4, ()) =>
    some (ofBits v4i32 (Sha256.msg1 (toBits v4i32 w0123) (toBits v4i32 w4)), ())
  | _, _, .sha256msg2, (sums, w, ()) =>
    some (ofBits v4i32 (Sha256.msg2 (toBits v4i32 sums) (toBits v4i32 w)), ())
  | _, _, .fadd t, (a, b, ()) =>
    (evalFloat2 Float.Model.UnpackedFloat.add t a b).map (·, ())
  | _, _, .fsub t, (a, b, ()) =>
    (evalFloat2 Float.Model.UnpackedFloat.sub t a b).map (·, ())
  | _, _, .fmul t, (a, b, ()) =>
    (evalFloat2 Float.Model.UnpackedFloat.mul t a b).map (·, ())
  | _, _, .fdiv t, (a, b, ()) =>
    (evalFloat2 Float.Model.UnpackedFloat.div t a b).map (·, ())
  | _, _, .ffma t, (a, b, c, ()) =>
    (evalFloat3 Float.Model.UnpackedFloat.fma t a b c).map (·, ())
  | _, _, .fsqrt t, (a, ()) =>
    (evalFloat1 Float.Model.UnpackedFloat.sqrt t a).map (·, ())
  | _, _, .fneg t, (a, ()) =>
    if t.isFloatTree then
      some (lift1 (fun {n} x => x ^^^ (1#n <<< (n - 1))) id t a, ())
    else none
  | _, _, .fabs t, (a, ()) =>
    if t.isFloatTree then
      some (lift1 (fun {n} x => x &&& ~~~(1#n <<< (n - 1))) id t a, ())
    else none
  | _, _, .fcmp o t _ h, (a, b, ()) =>
    if t.isFloatTree then
      some (cast (congrArg (fun u => Tup Val [u]) h.symm) (liftFCmp o t a b, ()))
    else none
  | _, _, .fptoui f n, (a, ()) =>
    (truncToInt (unpackFloat f a)).bind fun z =>
      if 0 ≤ z ∧ z < 2 ^ n then some (BitVec.ofInt n z, ()) else none
  | _, _, .fptosi f n, (a, ()) =>
    if n ≠ 0 then
      (truncToInt (unpackFloat f a)).bind fun z =>
        if -(2 ^ (n - 1) : Int) ≤ z ∧ z < (2 ^ (n - 1) : Int) then
          some (BitVec.ofInt n z, ())
        else none
    else none
  | _, _, .uitofp _ f, (a, ()) =>
    some (packFloat f (Float.Model.UnpackedFloat.ofInt f.format a.toNat), ())
  | _, _, .sitofp _ f, (a, ()) =>
    some (packFloat f (Float.Model.UnpackedFloat.ofInt f.format a.toInt), ())
  | _, _, .fcvt f g, (a, ()) =>
    some (evalConvertFloat f g a, ())

/-! ## Leaf-wise constants for algebraic identities and annihilators -/

/-- Leaf-wise additive/bitwise zero (`false` for `bool`, `0#n` for `bits n`). -/
def zeroVal : (t : Ty) → Val t
  | .bool => false
  | .bits n => 0#n
  | .float f => 0#f.width
  | .pair a b => (zeroVal a, zeroVal b)

/-- Leaf-wise all-ones (`true` for `bool`, `allOnes n` for `bits n`). -/
def onesVal : (t : Ty) → Val t
  | .bool => true
  | .bits n => BitVec.allOnes n
  | .float f => BitVec.allOnes f.width
  | .pair a b => (onesVal a, onesVal b)

/-- Leaf-wise multiplicative identity (`true` for `bool`, `1#n` for `bits n`). -/
def oneVal : (t : Ty) → Val t
  | .bool => true
  | .bits n => 1#n
  | .float f => 0#f.width
  | .pair a b => (oneVal a, oneVal b)

/-- Broadcast a `Bool` across a comparison mask tree `Val t.mask`. -/
def splatMaskVal : (t : Ty) → Bool → Val t.mask
  | .bool, b => b
  | .bits _, b => b
  | .float _, b => b
  | .pair s u, b => (splatMaskVal s b, splatMaskVal u b)

def isZeroVal : (t : Ty) → Val t → Bool
  | .bool, v => !v
  | .bits _, v => v == 0
  | .float _, v => v == 0
  | .pair a b, v => isZeroVal a v.1 && isZeroVal b v.2

def isOnesVal : (t : Ty) → Val t → Bool
  | .bool, v => v
  | .bits n, v => v == BitVec.allOnes n
  | .float f, v => v == BitVec.allOnes f.width
  | .pair a b, v => isOnesVal a v.1 && isOnesVal b v.2

def isOneVal : (t : Ty) → Val t → Bool
  | .bool, v => v
  | .bits n, v => v == 1#n
  | .float _, _ => false
  | .pair a b, v => isOneVal a v.1 && isOneVal b v.2

def isZeroArg? {V : Ty → Type} {t : Ty} (a : Arg V t) : Bool :=
  match a.imm? with
  | some v => isZeroVal t v
  | none => false

def isOnesArg? {V : Ty → Type} {t : Ty} (a : Arg V t) : Bool :=
  match a.imm? with
  | some v => isOnesVal t v
  | none => false

def isOneArg? {V : Ty → Type} {t : Ty} (a : Arg V t) : Bool :=
  match a.imm? with
  | some v => isOneVal t v
  | none => false

def CmpOp.isRefl : CmpOp → Bool
  | .eq | .sle | .sge | .ule | .uge => true
  | .ne | .slt | .sgt | .ult | .ugt => false

/-! ## Instruction elimination (`SimpAct`) -/

/-- Replacement for one result of a `let_` instruction: either a constant or an operand of `op`.
Completely independent of `V`, so `Wf` preservation sees identical actions on both sides. -/
inductive SimpElem (u : Ty) (sig : List Ty) : Type
  | imm (c : Val u) : SimpElem u sig
  | arg (i : Member u sig) : SimpElem u sig
  deriving DecidableEq

/-- Replacement tuple for every result of an eliminated `OpCode sig rs`. -/
abbrev SimpAct (sig rs : List Ty) := Tup (fun u => SimpElem u sig) rs

/-- Convert a concrete result tuple into a constant `SimpAct`. -/
def simpImms {sig : List Ty} : {rs : List Ty} → Tup Val rs → SimpAct sig rs
  | [], () => ()
  | _ :: _, (c, cs) => (.imm c, simpImms cs)

/-- Apply a `SimpAct` to the input operands of `op` to obtain replacement `FVal V`s. -/
def SimpAct.apply {V : Ty → Type} {sig : List Ty} (args : Tup (Arg (FVal V)) sig) :
    {rs : List Ty} → SimpAct sig rs → Tup (FVal V) rs
  | [], () => ()
  | _ :: _, (.imm c, act) => (fimm c, SimpAct.apply args act)
  | _ :: _, (.arg i, act) => ((args.get i).fpair, SimpAct.apply args act)

/-- Decide whether `op` simplifies away completely into a `SimpAct`. -/
def Op.simpAct {V : Ty → Type} {rs : List Ty} (op : Op (FVal V) rs) : Option (SimpAct op.sig rs) :=
  let outArgs := tupMapArg (fun _ => Arg.fout) op.args
  match (tupImms? outArgs).bind op.code.eval? with
  | some res => some (simpImms res)
  | none =>
    let ⟨code, args⟩ := op
    match code, args with
    | .copy _, _ => some (.arg .here, ())
    | .add t, (a, b, ()) =>
      if t.hasFloat then none
      else if isZeroArg? b.fout then some (.arg .here, ())
      else if isZeroArg? a.fout then some (.arg (.there .here), ())
      else none
    | .sub t, (a, b, ()) =>
      if t.hasFloat then none
      else if a.fkey == b.fkey then some (.imm (zeroVal t), ())
      else if isZeroArg? b.fout then some (.arg .here, ())
      else none
    | .mul t, (a, b, ()) =>
      if t.hasFloat then none
      else if isZeroArg? a.fout || isZeroArg? b.fout then some (.imm (zeroVal t), ())
      else if isOneArg? b.fout then some (.arg .here, ())
      else if isOneArg? a.fout then some (.arg (.there .here), ())
      else none
    | .neg .bool, _ => some (.arg .here, ())
    | .and t, (a, b, ()) =>
      if isZeroArg? a.fout || isZeroArg? b.fout then some (.imm (zeroVal t), ())
      else if isOnesArg? b.fout then some (.arg .here, ())
      else if isOnesArg? a.fout then some (.arg (.there .here), ())
      else if a.fkey == b.fkey then some (.arg .here, ())
      else none
    | .or t, (a, b, ()) =>
      if isOnesArg? a.fout || isOnesArg? b.fout then some (.imm (onesVal t), ())
      else if isZeroArg? b.fout then some (.arg .here, ())
      else if isZeroArg? a.fout then some (.arg (.there .here), ())
      else if a.fkey == b.fkey then some (.arg .here, ())
      else none
    | .xor t, (a, b, ()) =>
      if a.fkey == b.fkey then some (.imm (zeroVal t), ())
      else if isZeroArg? b.fout then some (.arg .here, ())
      else if isZeroArg? a.fout then some (.arg (.there .here), ())
      else none
    | .ternlog t imm, _ =>
      if imm == 0#8 then some (.imm (zeroVal t), ())
      else if imm == 0xff#8 then some (.imm (onesVal t), ())
      else if imm == 0xf0#8 then some (.arg .here, ())
      else if imm == 0xcc#8 then some (.arg (.there .here), ())
      else if imm == 0xaa#8 then some (.arg (.there (.there .here)), ())
      else none
    | .shl t, (_, b, ()) | .lshr t, (_, b, ()) | .ashr t, (_, b, ())
    | .rotl t, (_, b, ()) | .rotr t, (_, b, ()) =>
      if !t.hasFloat && isZeroArg? b.fout then some (.arg .here, ()) else none
    | .cmp o t _ h, (a, b, ()) =>
      if !t.hasFloat && a.fkey == b.fkey then
        some (.imm (cast (congrArg Val h.symm) (splatMaskVal t o.isRefl)), ())
      else none
    | .select _, (c, a, b, ()) =>
      match c.fout.imm? with
      | some true => some (.arg (.there .here), ())
      | some false => some (.arg (.there (.there .here)), ())
      | none => if a.fkey == b.fkey then some (.arg (.there .here), ()) else none
    | .blend t _ h, (c, a, b, ()) =>
      match c.fout.imm? with
      | some mc =>
        let mc' : Val t.mask := cast (congrArg Val h) mc
        if mc' == splatMaskVal t true then some (.arg (.there .here), ())
        else if mc' == splatMaskVal t false then some (.arg (.there (.there .here)), ())
        else if a.fkey == b.fkey then some (.arg (.there .here), ()) else none
      | none => if a.fkey == b.fkey then some (.arg (.there .here), ()) else none
    | .zext m n, _ | .sext m n, _ | .trunc m n, _ =>
      if h : m = n then
        some (cast (congrArg (fun k => SimpAct [.bits m] [.bits k]) h) (.arg .here, ()))
      else none
    | .addc _, (a, b, c, ()) =>
      if c.fout.imm? == some false then
        if isZeroArg? b.fout then some (.arg .here, .imm false, ())
        else if isZeroArg? a.fout then some (.arg (.there .here), .imm false, ())
        else none
      else none
    | .subb n, (a, b, c, ()) =>
      if c.fout.imm? == some false then
        if isZeroArg? b.fout then some (.arg .here, .imm false, ())
        else if a.fkey == b.fkey then some (.imm 0#n, .imm false, ())
        else none
      else none
    | .umulw n, (a, b, ()) | .smulw n, (a, b, ()) =>
      if isZeroArg? a.fout || isZeroArg? b.fout then some (.imm 0#n, .imm 0#n, ()) else none
    | .udiv n, (_, b, ()) =>
      if 0 < n && b.fout.imm? == some 1#n then some (.arg .here, ()) else none
    | .sdiv n, (_, b, ()) =>
      if 1 < n && b.fout.imm? == some 1#n then some (.arg .here, ()) else none
    | .urem n, (_, b, ()) =>
      if 0 < n && b.fout.imm? == some 1#n then some (.imm 0#n, ()) else none
    | .srem n, (_, b, ()) =>
      if 1 < n && b.fout.imm? == some 1#n then some (.imm 0#n, ()) else none
    | .udiv0 n, (_, b, ()) =>
      if b.fout.imm? == some 0#n then some (.imm 0#n, ())
      else if 0 < n && b.fout.imm? == some 1#n then some (.arg .here, ())
      else none
    | .sdiv0 n, (_, b, ()) =>
      if b.fout.imm? == some 0#n then some (.imm 0#n, ())
      else if 1 < n && b.fout.imm? == some 1#n then some (.arg .here, ())
      else none
    | .bitcast t u _, _ =>
      match tyDecEq t u with
      | isTrue htu => some (cast (congrArg (fun k => SimpAct [t] [k]) htu) (.arg .here, ()))
      | isFalse _ => none
    | _, _ => none

/-! ## Strength reduction (`Op.rewrite`) -/

/-- Find `m < limit` such that `x = BitVec.twoPow w m`. -/
def findPow2 (w : Nat) (x : BitVec w) : Nat → Option Nat
  | 0 => none
  | m + 1 => if x = BitVec.twoPow w m then some m else findPow2 w x m

/-- If every leaf of `t` in `v` is a power of two `2^m` (for `.bits n` with `m < n`), return the
leaf-wise shift amount `m`. -/
def leafPow2Shift? : (t : Ty) → Val t → Option (Val t)
  | .bits n, c => (findPow2 n c n).map (BitVec.ofNat n)
  | .pair a b, v => do
    let s1 ← leafPow2Shift? a v.1
    let s2 ← leafPow2Shift? b v.2
    pure (s1, s2)
  | _, _ => none

/-- Rewrite kept operations to cheaper ones with identical `Op.wp`:
power-of-two `mul → shl` (scalar & non-float vector), power-of-two `udiv → lshr`, `urem → and`. -/
def Op.rewrite {V : Ty → Type} {rs : List Ty} (op : Op V rs) : Op V rs :=
  let ⟨code, args⟩ := op
  match code, args with
  | .mul t, (a, b, ()) =>
    if t.hasFloat then ⟨.mul t, (a, b, ())⟩
    else match b.imm?.bind (leafPow2Shift? t) with
    | some s => op2 (.shl t) a (.imm s)
    | none =>
      match a.imm?.bind (leafPow2Shift? t) with
      | some s => op2 (.shl t) b (.imm s)
      | none => ⟨.mul t, (a, b, ())⟩
  | .udiv n, (a, b, ()) =>
    match b.imm?.bind (fun c => findPow2 n c n) with
    | some m => op2 (.lshr (.bits n)) a (.imm (BitVec.ofNat n m))
    | none => ⟨.udiv n, (a, b, ())⟩
  | .urem n, (a, b, ()) =>
    match b.imm?.bind (fun c => findPow2 n c n) with
    | some m => op2 (.and (.bits n)) a (.imm (BitVec.twoPow n m - 1#n))
    | none => ⟨.urem n, (a, b, ())⟩
  | code, args => ⟨code, args⟩

/-! ## PHOAS `fold` pass -/

mutual
def fold {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (next : Nat) :
    Expr (FVal V) L rs → Expr V L rs
  | .let_ (ts := ts) op k =>
    match op.simpAct with
    | some act => fold next (k (act.apply op.args))
    | none =>
      let op' : Op V ts := (⟨op.code, tupMapArg (fun _ => Arg.fout) op.args⟩ : Op V ts).rewrite
      .let_ op' fun xs => fold (next + ts.length) (k (freshFVals ts xs next))
  | .load t a k =>
    .load t a.fout fun v => fold (next + 1) (k (.var v, .var next))
  | .store v a k =>
    .store v.fout a.fout (fold next k)
  | .call f (bs := bs) args k =>
    .call f (tupMapArg (fun _ => Arg.fout) args) fun xs =>
      fold (next + bs.length) (k (freshFVals bs xs next))
  | .jnz c t e =>
    match c.fout with
    | .imm true => fold next t
    | .imm false => fold next e
    | .var v => .jnz (.var v) (fold next t) (fold next e)
  | .jump j args => .jump j (tupMapArg (fun _ => Arg.fout) args)
  | .ret vs => .ret (tupMapArg (fun _ => Arg.fout) vs)
  | .exit f args => .exit f (tupMapArg (fun _ => Arg.fout) args)
  | .hlt => .hlt
  | .group bodies k =>
    .group (fun Js => foldB next (bodies Js)) (fun Js => fold next (k Js))

def foldB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (next : Nat) :
    {sig : List (List Ty)} → Blocks (FVal V) L rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons (ts := ts) b bs =>
    .cons (fun xs => fold (next + ts.length) (b (freshFVals ts xs next))) (foldB next bs)
end

/-- Fold constants, trivial ops, algebraic rules, strength reductions, and static branches. -/
def Func.fold {as rs : List Ty} (f : Func as rs) : Func as rs :=
  fun V L xs => LeanQbe.T.fold as.length (f (FVal V) L (freshFVals as xs 0))

end LeanQbe.T
