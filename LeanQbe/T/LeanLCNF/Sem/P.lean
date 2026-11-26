module

public import LeanQbe.T.LeanLCNF.Basic
public import LeanQbe.T.LeanLCNF.Lower
public import LeanQbe.T.LeanLCNF.Lower1

/-!
# Tier-P (Pure, RC-Erased) Semantics and Fuel-Indexed Oracle for Impure `LeanLCNF`

Canonical total Tier-P definitions matching `lcnf_semantics_design_plan.md` (§2.4–§2.6, §3):
1. `PVal`: algebraic value tree (`erased`, `bits`, `nat`, `int`, `ctor`, `str`, `arr`, `barr`,
   `clo`), structural equality, and functional constructor/scalar/box helpers.
2. `PPost`, `PXPost`, `PSpec`, `PEnv`, `PJEnv`, `PValEnv`, `PArity`, and refinement orders.
3. `primP`: pure primitive evaluator mirroring `Lower.externPrim`.
4. `PApply`, `PVal.wp`, `PWp`: env-parametric, total weakest-precondition semantics with lfp
   join points (`.jp`), demonic `isShared`, functional `oset`/`uset`/`sset`/`setTag`, erased
   `inc`/`dec`/`del`, and `unreach` / `outOfBounds` / bad-closure routing to `X`.
5. `PModuleOk`, `PModuleOkIdx`: acyclic and measure-indexed module correctness predicates.
6. `PEval`: total executable fuel-indexed big-step oracle returning `Option POutcome`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

/-! ## 1. Panic Codes & Pure Values (`PVal`) -/

/-- Panic code for container capacity overflow (`panicCapCode` in `LcnfC0ContainersSpec`). -/
@[expose] def panicCap : Nat := 2

/-- Panic code for `outOfBounds._redArg` (`panicOobCode` in `LcnfC0ContainersSpec`). -/
@[expose] def panicOob : Nat := 7

/-- Pure algebraic value tree for Tier-P semantics (no heap addresses, no RC metadata). -/
inductive PVal where
  | erased
  | bits (w : Nat) (v : BitVec w)
  | nat (n : Nat)
  | int (z : Int)
  | ctor (cidx : Nat) (objs : List PVal) (scal : List UInt8)
  | str (s : String)
  | arr (xs : List PVal)
  | barr (bs : List UInt8)
  | clo (f : String) (arity : Nat) (fixed : List PVal)
  deriving Repr, Inhabited

mutual
/-- Structural boolean equality on `PVal`. -/
@[expose] def PVal.beq : PVal → PVal → Bool
  | .erased, .erased => true
  | .bits w1 v1, .bits w2 v2 => w1 == w2 && v1.toNat == v2.toNat
  | .nat n1, .nat n2 => n1 == n2
  | .int z1, .int z2 => z1 == z2
  | .ctor c1 os1 s1, .ctor c2 os2 s2 => c1 == c2 && PVal.beqList os1 os2 && s1 == s2
  | .str s1, .str s2 => s1 == s2
  | .arr xs1, .arr xs2 => PVal.beqList xs1 xs2
  | .barr bs1, .barr bs2 => bs1 == bs2
  | .clo f1 a1 fx1, .clo f2 a2 fx2 => f1 == f2 && a1 == a2 && PVal.beqList fx1 fx2
  | _, _ => false

/-- Structural boolean equality on `List PVal`. -/
@[expose] def PVal.beqList : List PVal → List PVal → Bool
  | [], [] => true
  | x :: xs, y :: ys => PVal.beq x y && PVal.beqList xs ys
  | _, _ => false
end

instance : BEq PVal := ⟨PVal.beq⟩

/-- Normal or abnormal outcome of pure evaluation. -/
inductive POutcome where
  | ret (v : PVal)
  | panic (code : Nat)
  deriving Repr, Inhabited

@[expose] def POutcome.beq : POutcome → POutcome → Bool
  | .ret v1, .ret v2 => PVal.beq v1 v2
  | .panic c1, .panic c2 => c1 == c2
  | _, _ => false

instance : BEq POutcome := ⟨POutcome.beq⟩

/-! ## 2. Pure Byte, Constructor, List, and Box Helpers -/

/-- Encode a `Bool` as impure LCNF `uint8` (`0#8` / `1#8`). -/
@[expose] def PVal.bool (b : Bool) : PVal :=
  .bits 8 (if b then 1#8 else 0#8)

/-- Read `k` little-endian bytes from `bs` starting at `off` into a `Nat`. -/
@[expose] def PVal.readNatLE (bs : List UInt8) (off : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (bs.getD off 0).toNat + 256 * PVal.readNatLE bs (off + 1) k

/-- Read a `w`-bit little-endian bitvector from `bs` starting at byte offset `off`. -/
@[expose] def PVal.readBitsLE (w : Nat) (bs : List UInt8) (off : Nat) : BitVec w :=
  BitVec.ofNat w (PVal.readNatLE bs off ((w + 7) / 8))

/-- Encode `n : Nat` into `k` little-endian bytes. -/
@[expose] def PVal.writeNatLE (n : Nat) : Nat → List UInt8
  | 0 => []
  | k + 1 => UInt8.ofNat (n % 256) :: PVal.writeNatLE (n / 256) k

/-- Overwrite `patch.length` bytes in `bs` starting at `off`. -/
@[expose] def PVal.writeBytesAt (bs : List UInt8) (off : Nat) (patch : List UInt8) : List UInt8 :=
  bs.take off ++ patch ++ bs.drop (off + patch.length)

/-- Extract the dispatch tag of a `PVal` for `LcCode.cases` and `getObjTagNat`. -/
@[expose] def PVal.tag? : PVal → Option Nat
  | .ctor cidx _ _ => some cidx
  | .bits _ v => some v.toNat
  | .nat n => some n
  | .erased => some 0
  | _ => none

/-- Extract the underlying `Nat` of a bitvector or `Nat` `PVal`. -/
@[expose] def PVal.toNat? : PVal → Option Nat
  | .bits _ v => some v.toNat
  | .nat n => some n
  | .ctor cidx [] [] => some cidx
  | .erased => some 0
  | _ => none

/-- Extract a `BitVec w` from a `.bits` `PVal` (with exact width match). -/
@[expose] def PVal.toBits? (w : Nat) : PVal → Option (BitVec w)
  | .bits m v => if h : m = w then some (h ▸ v) else none
  | _ => none

/-- Encode a `List PVal` as a Lean `List` constructor chain (`nil = 0`, `cons = 1`). -/
@[expose] def PVal.ofList : List PVal → PVal
  | [] => .ctor 0 [] []
  | x :: xs => .ctor 1 [x, PVal.ofList xs] []

/-- Decode a Lean `List` constructor chain into `List PVal`. -/
@[expose] def PVal.toList? : PVal → Option (List PVal)
  | .ctor 0 [] _ => some []
  | .ctor 1 [x, xs] _ => (PVal.toList? xs).map (x :: ·)
  | _ => none

/-- Project object field `i` (`oproj i x`). -/
@[expose] def PVal.getObj? (v : PVal) (i : Nat) : Option PVal :=
  match v with
  | .ctor _ objs _ => objs[i]?
  | _ => none

/-- Project `usize` scalar field `i` (`uproj i x`). -/
@[expose] def PVal.getUsize? (v : PVal) (i : Nat) : Option PVal :=
  match v with
  | .ctor _ objs scal =>
    if objs.length ≤ i then
      let bOff := 8 * (i - objs.length)
      if bOff + 8 ≤ scal.length then some (.bits 64 (PVal.readBitsLE 64 scal bOff))
      else none
    else none
  | _ => none

/-- Project scalar field at `(n, off)` of type `ty` (`sproj n off x`). -/
@[expose] def PVal.getScalar? (v : PVal) (n off : Nat) (ty : LcTy) : Option PVal :=
  match v with
  | .ctor _ objs scal =>
    if objs.length ≤ n then
      let bOff := 8 * (n - objs.length) + off
      if bOff + ty.toTTy.bytes ≤ scal.length then
        some (.bits ty.width (PVal.readBitsLE ty.width scal bOff))
      else none
    else none
  | _ => none

/-- Functional update of object field `i` (`oset x i y`). -/
@[expose] def PVal.setObj (v : PVal) (i : Nat) (y : PVal) : Option PVal :=
  match v with
  | .ctor cidx objs scal =>
    if i < objs.length then some (.ctor cidx (objs.set i y) scal) else none
  | _ => none

/-- Functional update of `usize` field `i` (`uset x i y`). -/
@[expose] def PVal.setUsize (v : PVal) (i : Nat) (y : PVal) : Option PVal :=
  match v, y.toBits? 64 with
  | .ctor cidx objs scal, some yv =>
    if objs.length ≤ i then
      let bOff := 8 * (i - objs.length)
      if bOff + 8 ≤ scal.length then
        some (.ctor cidx objs (PVal.writeBytesAt scal bOff (PVal.writeNatLE yv.toNat 8)))
      else none
    else none
  | _, _ => none

/-- Functional update of scalar field `(n, off)` of type `ty` (`sset x n off y ty`). -/
@[expose] def PVal.setScalar (v : PVal) (n off : Nat) (ty : LcTy) (y : PVal) : Option PVal :=
  match v, y.toNat? with
  | .ctor cidx objs scal, some yNat =>
    if objs.length ≤ n then
      let bOff := 8 * (n - objs.length) + off
      let nb := ty.toTTy.bytes
      if bOff + nb ≤ scal.length then
        some (.ctor cidx objs (PVal.writeBytesAt scal bOff (PVal.writeNatLE yNat nb)))
      else none
    else none
  | _, _ => none

/-- Functional update of constructor tag (`setTag x cidx`). -/
@[expose] def PVal.setTag (v : PVal) (cidx : Nat) : Option PVal :=
  match v with
  | .ctor _ objs scal => some (.ctor cidx objs scal)
  | _ => none

/-- Pure `box ty x`: normalizes scalar width; preserves already-boxed values. -/
@[expose] def PVal.box (t : LcTy) (v : PVal) : Option PVal :=
  match t with
  | .uint8 | .uint16 | .uint32 | .uint64 | .usize | .float =>
    match v with
    | .bits _ bv => some (.bits t.width (bv.setWidth t.width))
    | .ctor cidx [] [] => some (.bits t.width (BitVec.ofNat t.width cidx))
    | .nat n => some (.bits t.width (BitVec.ofNat t.width n))
    | .erased => some (.bits t.width (BitVec.ofNat t.width 0))
    | _ => none
  | _ => some v

/-- Pure `unbox x` at binder type `ty`. -/
@[expose] def PVal.unbox (ty : LcTy) (v : PVal) : Option PVal :=
  match v with
  | .bits _ bv => some (.bits ty.width (bv.setWidth ty.width))
  | .nat n => some (.bits ty.width (BitVec.ofNat ty.width n))
  | .ctor cidx [] [] => some (.bits ty.width (BitVec.ofNat ty.width cidx))
  | .erased => some (.bits ty.width (BitVec.ofNat ty.width 0))
  | _ => none

/-- Kernel-reducible, total arbitrary-precision decimal formatter for `Nat`. -/
@[expose] def PVal.natToDecStr (n : Nat) : String :=
  let rec go (k : Nat) (acc : List Char) : List Char :=
    let acc' := digitChar (k % 10) :: acc
    if h : k < 10 then acc'
    else go (k / 10) acc'
  termination_by k
  decreasing_by
    have hpos : 0 < k := by omega
    exact Nat.div_lt_self hpos (by decide)
  String.ofList (go n [])

/-! ## 3. Tier-P Contracts, Environments, and Primitive Table (`primP`) -/

/-- Return postcondition at Tier P. -/
abbrev PPost : Type := PVal → Prop

/-- Abnormal-exit postcondition at Tier P (panic code). -/
abbrev PXPost : Type := Nat → Prop

/-- Tier-P function contract: args → normal post → panic post → Prop. -/
abbrev PSpec : Type := List PVal → PPost → PXPost → Prop

/-- Tier-P call environment for module declarations. -/
abbrev PEnv : Type := String → PSpec

/-- Tier-P join-point continuation environment. -/
abbrev PJEnv : Type := Nat → List PVal → Prop

/-- Map from module declaration names to parameter arities (for `pap`). -/
abbrev PArity : Type := String → Option Nat

/-- Named Tier-P local variable environment. -/
abbrev PValEnv : Type := Nat → Option PVal

@[expose] def PEnv.bot : PEnv := fun _ _ _ _ => False

@[expose] def PJEnv.empty : PJEnv := fun _ _ => False

@[expose] def PJEnv.set (J : PJEnv) (j : Nat) (Jj : List PVal → Prop) : PJEnv :=
  fun i => if i = j then Jj else J i

@[expose] def PValEnv.empty : PValEnv := fun _ => none

@[expose] def PValEnv.set (ρ : PValEnv) (x : Nat) (v : PVal) : PValEnv :=
  fun i => if i = x then some v else ρ i

/-- Bind parameters left-to-right (matching `LCtx.bindAll` and `HValEnv.bindAll`). -/
@[expose] def PValEnv.bindAll (ρ : PValEnv) : List LcParam → List PVal → PValEnv
  | p :: ps, v :: vs => (ρ.set p.id v).bindAll ps vs
  | _, _ => ρ

/-- Evaluate an `LcArg` in a Tier-P environment. -/
@[expose] def PValEnv.evalArg (ρ : PValEnv) : LcArg → Option PVal
  | .erased => some .erased
  | .var x => ρ x

/-- Evaluate a list of `LcArg`s in a Tier-P environment. -/
@[expose] def PValEnv.evalArgs (ρ : PValEnv) : List LcArg → Option (List PVal)
  | [] => some []
  | a :: as =>
    match ρ.evalArg a, ρ.evalArgs as with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- Pointwise refinement order on Tier-P specs, call environments, and join environments. -/
@[expose] def PSpec.le (S₁ S₂ : PSpec) : Prop :=
  ∀ as Q X, S₁ as Q X → S₂ as Q X

@[expose] def PEnv.le (Δ₁ Δ₂ : PEnv) : Prop :=
  ∀ f, PSpec.le (Δ₁ f) (Δ₂ f)

@[expose] def PJEnv.le (J₁ J₂ : PJEnv) : Prop :=
  ∀ j as, J₁ j as → J₂ j as

@[expose] def PSpec.Mono (S : PSpec) : Prop :=
  ∀ as (Q₁ Q₂ : PPost) (X₁ X₂ : PXPost),
    (∀ r, Q₁ r → Q₂ r) → (∀ c, X₁ c → X₂ c) → S as Q₁ X₁ → S as Q₂ X₂

/-- Arity map derived from an `LcModule`. -/
@[expose] def modArityOf (m : LcModule) (f : String) : Option Nat :=
  (m.decls.find? (·.name == f)).map (·.params.length)

/-- Decidable classifier for built-in extern primitives lowered by `Lower.externPrim`. -/
@[expose] def pIsPrimName (name : String) : Bool :=
  match splitDot name with
  | ["Nat", _] | ["Array", _] | ["ByteArray", _] | ["Float", _]
  | ["Char", _] | ["Int", _] | ["Int64", _] | ["getObjTagNat"]
  | ["System", "Platform", "getNumBits"] | ["outOfBounds", "_redArg"] => true
  | "String" :: _ => true
  | [ty, _] => (uintWidth? ty).isSome
  | _ => false

/-- Lexicographical comparison of byte lists (`0 = lt`, `1 = eq`, `2 = gt`). -/
@[expose] def cmpByteList : List UInt8 → List UInt8 → Nat
  | [], [] => 1
  | [], _ :: _ => 0
  | _ :: _, [] => 2
  | a :: as, b :: bs =>
    if a < b then 0 else if a > b then 2 else cmpByteList as bs

/-- Pure `Nat.*` primitives. -/
@[expose] def primNatP (op : String) (as : List PVal) : Option PVal :=
  match op, as with
  | "add", [.nat a, .nat b] => some (.nat (a + b))
  | "sub", [.nat a, .nat b] => some (.nat (a - b))
  | "mul", [.nat a, .nat b] => some (.nat (a * b))
  | "div", [.nat a, .nat b] => some (.nat (a / b))
  | "mod", [.nat a, .nat b] => some (.nat (a % b))
  | "decEq", [.nat a, .nat b] | "beq", [.nat a, .nat b] => some (PVal.bool (a == b))
  | "decLt", [.nat a, .nat b] | "blt", [.nat a, .nat b] => some (PVal.bool (decide (a < b)))
  | "decLe", [.nat a, .nat b] | "ble", [.nat a, .nat b] => some (PVal.bool (decide (a ≤ b)))
  | "shiftRight", [.nat a, .nat b] => some (.nat (a >>> b))
  | "shiftLeft", [.nat a, .nat b] => some (.nat (a <<< b))
  | "land", [.nat a, .nat b] => some (.nat (a &&& b))
  | "lor", [.nat a, .nat b] => some (.nat (a ||| b))
  | "xor", [.nat a, .nat b] => some (.nat (a ^^^ b))
  | "pow", [.nat a, .nat b] => some (.nat (a ^ b))
  | "gcd", [.nat a, .nat b] => some (.nat (Nat.gcd a b))
  | "pred", [.nat a] => some (.nat (a - 1))
  | "log2", [.nat a] => some (.nat a.log2)
  | "reprFast", [.nat a] => some (.str (PVal.natToDecStr a))
  | _, _ => none

/-- Pure `UIntN.*` / `USize.*` primitives at bit width `w`. -/
@[expose] def primUintP (w : Nat) (op : String) (as : List PVal) : Option PVal :=
  let bin (f : BitVec w → BitVec w → BitVec w) : Option PVal :=
    match as with
    | [a, b] => match a.toBits? w, b.toBits? w with
      | some av, some bv => some (.bits w (f av bv))
      | _, _ => none
    | _ => none
  let cmp (p : BitVec w → BitVec w → Bool) : Option PVal :=
    match as with
    | [a, b] => match a.toBits? w, b.toBits? w with
      | some av, some bv => some (PVal.bool (p av bv))
      | _, _ => none
    | _ => none
  let un (f : BitVec w → PVal) : Option PVal :=
    match as with | [a] => (a.toBits? w).map f | _ => none
  match op with
  | "add" => bin (· + ·) | "sub" => bin (· - ·) | "mul" => bin (· * ·)
  | "land" => bin (· &&& ·) | "lor" => bin (· ||| ·) | "xor" => bin (· ^^^ ·)
  | "shiftLeft" => bin fun a b => a <<< (b &&& BitVec.ofNat w (w - 1))
  | "shiftRight" => bin fun a b => a >>> (b &&& BitVec.ofNat w (w - 1))
  | "div" => bin fun a b => if b = 0 then 0 else a / b
  | "mod" => bin fun a b => if b = 0 then a else a % b
  | "complement" => un fun a => .bits w (~~~a)
  | "neg" => un fun a => .bits w (-a)
  | "decEq" | "beq" => cmp (· == ·)
  | "decLt" | "blt" => cmp fun a b => decide (a < b)
  | "decLe" | "ble" => cmp fun a b => decide (a ≤ b)
  | "ofNat" | "ofBitVec" =>
    match as with | [.nat n] => some (.bits w (BitVec.ofNat w n)) | _ => none
  | "ofNatLT" =>
    match as with
    | [.nat n] | [.nat n, _] => some (.bits w (BitVec.ofNat w n))
    | _ => none
  | "toNat" | "toBitVec" => un fun a => .nat a.toNat
  | "repr" => un fun a => .str (PVal.natToDecStr a.toNat)
  | "toUInt8" => un fun a => .bits 8 (a.setWidth 8)
  | "toUInt16" => un fun a => .bits 16 (a.setWidth 16)
  | "toUInt32" => un fun a => .bits 32 (a.setWidth 32)
  | "toUInt64" | "toUSize" => un fun a => .bits 64 (a.setWidth 64)
  | "toFloat" => un fun a => .bits 64 (UInt64.ofNat a.toNat).toFloat.toBits.toBitVec
  | _ => none

/-- Pure `Int.*` primitives. -/
@[expose] def primIntP (op : String) (as : List PVal) : Option PVal :=
  match op, as with
  | "ofNat", [.nat n] => some (.int (Int.ofNat n))
  | "negSucc", [.nat n] => some (.int (Int.negSucc n))
  | "neg", [.int a] => some (.int (-a))
  | "add", [.int a, .int b] => some (.int (a + b))
  | "sub", [.int a, .int b] => some (.int (a - b))
  | "mul", [.int a, .int b] => some (.int (a * b))
  | "ediv", [.int a, .int b] => some (.int (Int.ediv a b))
  | "emod", [.int a, .int b] => some (.int (Int.emod a b))
  | "tdiv", [.int a, .int b] | "divExact", [.int a, .int b, _] => some (.int (Int.tdiv a b))
  | "tmod", [.int a, .int b] => some (.int (Int.tmod a b))
  | "natAbs", [.int a] => some (.nat a.natAbs)
  | "decEq", [.int a, .int b] => some (PVal.bool (a == b))
  | "decLt", [.int a, .int b] => some (PVal.bool (decide (a < b)))
  | "decLe", [.int a, .int b] => some (PVal.bool (decide (a ≤ b)))
  | "decNonneg", [.int a] => some (PVal.bool (decide (0 ≤ a)))
  | _, _ => none

/-- Pure `Int64.*` primitives (`bits 64`, two's complement). -/
@[expose] def primInt64P (op : String) (as : List PVal) : Option PVal :=
  match op, as with
  | "ofNat", [.nat n] => some (.bits 64 (BitVec.ofNat 64 n))
  | "decEq", [.bits 64 a, .bits 64 b] => some (PVal.bool (a == b))
  | "decLt", [.bits 64 a, .bits 64 b] => some (PVal.bool (a.slt b))
  | "decLe", [.bits 64 a, .bits 64 b] => some (PVal.bool (a.sle b))
  | "toInt", [.bits 64 a] => some (.int a.toInt)
  | "add", _ | "sub", _ | "mul", _ | "land", _ | "lor", _ | "xor", _
  | "neg", _ | "complement", _ => primUintP 64 op as
  | _, _ => none

/-- Pure `Char.*` primitives. -/
@[expose] def primCharP (op : String) (as : List PVal) : Option PVal :=
  match op, as with
  | "ofNat", [.nat n] => some (.bits 32 (BitVec.ofNat 32 (Char.ofNat n).toNat))
  | "ofNatAux", [.nat n, _] => some (.bits 32 (BitVec.ofNat 32 n))
  | "utf8Size", [.bits 32 c] => some (.nat (Char.ofNat c.toNat).utf8Size)
  | _, _ => none

/-- Pure `String.*` primitives. -/
@[expose] def primStringP (parts : List String) (as : List PVal) : Option PVal :=
  match parts, as with
  | ["length"], [.str s] | ["Internal", "length"], [.str s] => some (.nat s.length)
  | ["utf8ByteSize"], [.str s] => some (.nat s.utf8ByteSize)
  | ["toListImpl"], [.str s] | ["data"], [.str s] =>
    some (PVal.ofList (s.toList.map fun c => .bits 32 (BitVec.ofNat 32 c.toNat)))
  | ["ofList"], [cs] | ["mk"], [cs] =>
    (PVal.toList? cs).bind fun xs =>
      (xs.mapM fun (v : PVal) => v.toNat?.map Char.ofNat).map fun chs => .str (String.ofList chs)
  | ["push"], [.str s, .bits 32 c] => some (.str (s.push (Char.ofNat c.toNat)))
  | ["propagateMark"], [_, x] => some x
  | ["append"], [.str s1, .str s2] | ["Internal", "append"], [.str s1, .str s2] =>
    some (.str (s1 ++ s2))
  | ["decEq"], [.str s1, .str s2] => some (PVal.bool (s1 == s2))
  | ["decidableLT"], [.str s1, .str s2] => some (PVal.bool (decide (s1 < s2)))
  | ["compare"], [.str s1, .str s2] =>
    let r : BitVec 8 := match compare s1 s2 with | .lt => 0#8 | .eq => 1#8 | .gt => 2#8
    some (.bits 8 r)
  | ["Pos", "Raw", "get"], [.str s, .nat i]
  | ["Pos", "Raw", "get!"], [.str s, .nat i]
  | ["get"], [.str s, .nat i] | ["get!"], [.str s, .nat i]
  | ["Internal", "get"], [.str s, .nat i]
  | ["Pos", "Raw", "get'"], [.str s, .nat i, _]
  | ["get'"], [.str s, .nat i, _] | ["decodeChar"], [.str s, .nat i, _] =>
    some (.bits 32 (BitVec.ofNat 32 (String.Pos.Raw.get s ⟨i⟩).toNat))
  | ["Pos", "Raw", "next"], [.str s, .nat i]
  | ["next"], [.str s, .nat i] | ["Internal", "next"], [.str s, .nat i]
  | ["Pos", "Raw", "next'"], [.str s, .nat i, _]
  | ["Pos", "next"], [.str s, .nat i, _] =>
    some (.nat (String.Pos.Raw.next s ⟨i⟩).byteIdx)
  | ["Pos", "Raw", "atEnd"], [.str s, .nat i]
  | ["atEnd"], [.str s, .nat i] | ["Internal", "atEnd"], [.str s, .nat i] =>
    some (PVal.bool (String.Pos.Raw.atEnd s ⟨i⟩))
  | ["Pos", "Raw", "isValid"], [.str s, .nat i] =>
    some (PVal.bool (String.Pos.Raw.isValid s ⟨i⟩))
  | ["Pos", "Raw", "extract"], [.str s, .nat b, .nat e]
  | ["extract"], [.str s, .nat b, .nat e]
  | ["Internal", "extract"], [.str s, .nat b, .nat e] =>
    some (.str (String.Pos.Raw.extract s ⟨b⟩ ⟨e⟩))
  | ["getUTF8Byte"], [.str s, .nat i, _]
  | ["getUtf8Byte"], [.str s, .nat i, _]
  | ["Internal", "getUTF8Byte"], [.str s, .nat i, _] =>
    some (.bits 8 (BitVec.ofNat 8 (s.toUTF8.toList.getD i 0).toNat))
  | _, _ => none

/-- Pure `Array.*` primitives (functional updates). -/
@[expose] def primArrayP (op : String) (as : List PVal) : Option PVal :=
  let swapList (xs : List PVal) (i j : Nat) : List PVal :=
    match xs[i]?, xs[j]? with
    | some vi, some vj => (xs.set i vj).set j vi
    | _, _ => xs
  match op, as with
  | "empty", [_] => some (.arr [])
  | "mkEmpty", [_, .nat _] | "emptyWithCapacity", [_, .nat _] => some (.arr [])
  | "mk", [_, xs] => (PVal.toList? xs).map .arr
  | "toList", [_, .arr xs] => some (PVal.ofList xs)
  | "push", [_, .arr xs, v] => some (.arr (xs ++ [v]))
  | "replicate", [_, .nat n, v] => some (.arr (List.replicate n v))
  | "size", [_, .arr xs] => some (.nat xs.length)
  | "usize", [_, .arr xs] => some (.bits 64 (BitVec.ofNat 64 xs.length))
  | "get!Internal", [_, dv, .arr xs, .nat i]
  | "get!InternalBorrowed", [_, dv, .arr xs, .nat i] => some (xs.getD i dv)
  | "getInternal", [_, .arr xs, .nat i, _]
  | "getInternalBorrowed", [_, .arr xs, .nat i, _] => some (xs.getD i .erased)
  | "uget", [_, .arr xs, .bits 64 i, _]
  | "ugetBorrowed", [_, .arr xs, .bits 64 i, _] => some (xs.getD i.toNat .erased)
  | "set!", [_, .arr xs, .nat i, v]
  | "set", [_, .arr xs, .nat i, v, _] => some (.arr (xs.set i v))
  | "uset", [_, .arr xs, .bits 64 i, v, _] => some (.arr (xs.set i.toNat v))
  | "pop", [_, .arr xs] => some (.arr xs.dropLast)
  | "swap", [_, .arr xs, .nat i, .nat j, _, _]
  | "swapIfInBounds", [_, .arr xs, .nat i, .nat j] => some (.arr (swapList xs i j))
  | "propagateMark", [_, _, _, ys] => some ys
  | _, _ => none

/-- Pure `ByteArray.*` primitives (functional updates). -/
@[expose] def primByteArrayP (op : String) (as : List PVal) : Option PVal :=
  match op, as with
  | "empty", [] => some (.barr [])
  | "emptyWithCapacity", [.nat _] => some (.barr [])
  | "mk", [.arr xs] =>
    (xs.mapM fun (v : PVal) => v.toNat?.map UInt8.ofNat).map .barr
  | "data", [.barr bs] =>
    some (.arr (bs.map fun b => .bits 8 (BitVec.ofNat 8 b.toNat)))
  | "push", [.barr bs, .bits 8 b] => some (.barr (bs ++ [UInt8.ofNat b.toNat]))
  | "size", [.barr bs] => some (.nat bs.length)
  | "usize", [.barr bs] => some (.bits 64 (BitVec.ofNat 64 bs.length))
  | "get!", [.barr bs, .nat i] | "get", [.barr bs, .nat i, _] =>
    some (.bits 8 (BitVec.ofNat 8 (bs.getD i 0).toNat))
  | "uget", [.barr bs, .bits 64 i, _] =>
    some (.bits 8 (BitVec.ofNat 8 (bs.getD i.toNat 0).toNat))
  | "set!", [.barr bs, .nat i, .bits 8 b] | "set", [.barr bs, .nat i, .bits 8 b, _] =>
    some (.barr (bs.set i (UInt8.ofNat b.toNat)))
  | "uset", [.barr bs, .bits 64 i, .bits 8 b, _] =>
    some (.barr (bs.set i.toNat (UInt8.ofNat b.toNat)))
  | "beq", [.barr a, .barr b] | "decEq", [.barr a, .barr b] =>
    some (PVal.bool (a == b))
  | "decidableLT", [.barr a, .barr b] =>
    some (PVal.bool (cmpByteList a b == 0))
  | "compare", [.barr a, .barr b] =>
    some (.bits 8 (BitVec.ofNat 8 (cmpByteList a b)))
  | "propagateMark", [_, b] => some b
  | _, _ => none

/-- Pure `Float.*` primitives (`Float` represented as IEEE-754 `bits 64`). -/
@[expose] def primFloatP (op : String) (as : List PVal) : Option PVal :=
  let ofBV (a : BitVec 64) : Float := Float.ofBits (UInt64.ofBitVec a)
  let toBV (f : Float) : PVal := .bits 64 f.toBits.toBitVec
  match op, as with
  | "toBits", [a] | "ofBits", [a] | "toModel", [a] | "ofModel", [a] => some a
  | "ofScientific", [.nat m, .bits 8 neg, .nat e] =>
    some (toBV (Float.ofScientific m (neg != 0#8) e))
  | "add", [.bits 64 a, .bits 64 b] => some (toBV (ofBV a + ofBV b))
  | "sub", [.bits 64 a, .bits 64 b] => some (toBV (ofBV a - ofBV b))
  | "mul", [.bits 64 a, .bits 64 b] => some (toBV (ofBV a * ofBV b))
  | "div", [.bits 64 a, .bits 64 b] => some (toBV (ofBV a / ofBV b))
  | "beq", [.bits 64 a, .bits 64 b] => some (PVal.bool (ofBV a == ofBV b))
  | "decLt", [.bits 64 a, .bits 64 b] | "lt", [.bits 64 a, .bits 64 b] =>
    some (PVal.bool (decide (ofBV a < ofBV b)))
  | "decLe", [.bits 64 a, .bits 64 b] | "le", [.bits 64 a, .bits 64 b] =>
    some (PVal.bool (decide (ofBV a ≤ ofBV b)))
  | "pow", [.bits 64 a, .bits 64 b] => some (toBV (Float.pow (ofBV a) (ofBV b)))
  | "atan2", [.bits 64 a, .bits 64 b] => some (toBV (Float.atan2 (ofBV a) (ofBV b)))
  | "neg", [.bits 64 a] => some (toBV (-(ofBV a)))
  | "abs", [.bits 64 a] => some (toBV (Float.abs (ofBV a)))
  | "sqrt", [.bits 64 a] => some (toBV (Float.sqrt (ofBV a)))
  | "sin", [.bits 64 a] => some (toBV (Float.sin (ofBV a)))
  | "cos", [.bits 64 a] => some (toBV (Float.cos (ofBV a)))
  | "tan", [.bits 64 a] => some (toBV (Float.tan (ofBV a)))
  | "exp", [.bits 64 a] => some (toBV (Float.exp (ofBV a)))
  | "log", [.bits 64 a] => some (toBV (Float.log (ofBV a)))
  | "floor", [.bits 64 a] => some (toBV (Float.floor (ofBV a)))
  | "ceil", [.bits 64 a] => some (toBV (Float.ceil (ofBV a)))
  | "round", [.bits 64 a] => some (toBV (Float.round (ofBV a)))
  | "isNaN", [.bits 64 a] => some (PVal.bool (ofBV a).isNaN)
  | "isInf", [.bits 64 a] => some (PVal.bool (ofBV a).isInf)
  | "isFinite", [.bits 64 a] => some (PVal.bool (ofBV a).isFinite)
  | "toUInt64", [.bits 64 a] => some (.bits 64 (ofBV a).toUInt64.toBitVec)
  | "toUInt32", [.bits 64 a] => some (.bits 32 (ofBV a).toUInt32.toBitVec)
  | "toUInt16", [.bits 64 a] => some (.bits 16 (ofBV a).toUInt16.toBitVec)
  | "toUInt8", [.bits 64 a] => some (.bits 8 (ofBV a).toUInt8.toBitVec)
  | "toInt64", [.bits 64 a] => some (.bits 64 (ofBV a).toInt64.toBitVec)
  | "toString", [.bits 64 a] => some (.str (ofBV a).toString)
  | _, _ => none

/-- Top-level pure primitive evaluator mirroring `Lower.externPrim`.
(`outOfBounds._redArg` panics with `panicOob` and is routed to `X` in `PVal.wp`/`PEval`.) -/
@[expose] def primP (name : String) (as : List PVal) : Option PVal :=
  match splitDot name with
  | ["Nat", op] => primNatP op as
  | ["Array", op] => primArrayP op as
  | "String" :: rest => primStringP rest as
  | ["ByteArray", op] => primByteArrayP op as
  | ["Float", op] => primFloatP op as
  | ["Char", op] => primCharP op as
  | ["Int", op] => primIntP op as
  | ["Int64", op] => primInt64P op as
  | ["getObjTagNat"] =>
    match as with
    | [_, x] | [x] => x.tag?.map .nat
    | _ => none
  | ["System", "Platform", "getNumBits"] => some (.nat 64)
  | [ty, op] =>
    match uintWidth? ty with
    | some w => primUintP w op as
    | none => none
  | _ => none

/-! ## 4. Tier-P Weakest Precondition (`PApply`, `PVal.wp`, `PWp`) -/

/-- Exact, under-, and over-application of a Tier-P closure value `fn` to `args`. -/
@[expose] def PApply (Δ : PEnv) (fn : PVal) (args : List PVal) (K : PPost) (X : PXPost) : Prop :=
  match fn with
  | .clo f arity fixed =>
    let rem := arity - fixed.length
    if args.isEmpty then K (.clo f arity fixed)
    else if _hrem : rem = 0 then X panicBadClosure
    else if _hlt : args.length < rem then K (.clo f arity (fixed ++ args))
    else if _heq : args.length = rem then
      ∃ (P : PPost) (E : PXPost),
        Δ f (fixed ++ args) P E ∧ (∀ r, P r → K r) ∧ (∀ c, E c → X c)
    else
      ∃ (P : PPost) (E : PXPost),
        Δ f (fixed ++ args.take rem) P E ∧
        (∀ r, P r → PApply Δ r (args.drop rem) K X) ∧ (∀ c, E c → X c)
  | _ => X panicBadClosure
termination_by args.length
decreasing_by
  simp only [List.length_drop]
  omega

/-- Construct a `PVal` for `.ctor ci as` or `.reuse _ ci _ as` at binder type `ty`. -/
@[expose] def PVal.mkCtor (ty : LcTy) (ci : LcCtor) (vs : List PVal) : Option PVal :=
  if ci.isScalar then
    some (if ty.isScalar then .bits ty.width (BitVec.ofNat ty.width ci.cidx)
          else .ctor ci.cidx [] [])
  else if vs.length == ci.size then
    some (.ctor ci.cidx vs (List.replicate (8 * ci.usize + ci.ssize) 0))
  else none

/-- Weakest precondition of `LcVal` bound at type `ty` at Tier P. -/
@[expose] def PVal.wp (ar : PArity) (Δ : PEnv) (ρ : PValEnv) (ty : LcTy)
    (v : LcVal) (K : PPost) (X : PXPost) : Prop :=
  match v with
  | .lit (.nat n) => K (.nat n)
  | .lit (.str s) => K (.str s)
  | .lit (.scalar n) => K (.bits ty.width (BitVec.ofNat ty.width n))
  | .erased => K .erased
  | .ap f as =>
    match ρ f, ρ.evalArgs as with
    | some fn, some vs => PApply Δ fn vs K X
    | _, _ => False
  | .ctor ci as =>
    match ρ.evalArgs as with
    | some vs =>
      match PVal.mkCtor ty ci vs with
      | some r => K r
      | none => False
    | none => False
  | .oproj i x =>
    match (ρ x).bind (·.getObj? i) with
    | some r => K r
    | none => False
  | .uproj i x =>
    match (ρ x).bind (·.getUsize? i) with
    | some r => K r
    | none => False
  | .sproj n off x =>
    match (ρ x).bind (·.getScalar? n off ty) with
    | some r => K r
    | none => False
  | .fap f as =>
    match ρ.evalArgs as with
    | none => False
    | some vs =>
      if f == "outOfBounds._redArg" then
        if vs.length == 1 then X panicOob else False
      else if pIsPrimName f then
        match primP f vs with
        | some r => K r
        | none => False
      else
        ∃ (P : PPost) (E : PXPost),
          Δ f vs P E ∧ (∀ r, P r → K r) ∧ (∀ c, E c → X c)
  | .pap f as =>
    match ar f, ρ.evalArgs as with
    | some a, some vs =>
      if vs.length < a then K (.clo f a vs) else False
    | _, _ => False
  | .reset _ x =>
    match ρ x with
    | some _ => K .erased
    | none => False
  | .reuse x ci _ as =>
    match ρ x, ρ.evalArgs as with
    | some _, some vs =>
      match PVal.mkCtor ty ci vs with
      | some r => K r
      | none => False
    | _, _ => False
  | .box t x =>
    match (ρ x).bind (PVal.box t) with
    | some r => K r
    | none => False
  | .unbox x =>
    match (ρ x).bind (PVal.unbox ty) with
    | some r => K r
    | none => False
  | .isShared x =>
    (ρ x).isSome ∧ ∀ b : Bool, K (PVal.bool b)

mutual
/-- Total-correctness Tier-P weakest precondition of impure `LcCode`.
Join points (`.jp`) use least fixed points (matching `HWp` and `T.wp`'s `.group`), `isShared` is
demonic, `oset`/`uset`/`sset`/`setTag` perform functional updates, `inc`/`dec`/`del` are erased,
and `unreach` routes to `X panicUnreachable`. -/
@[expose] def PWp (ar : PArity) (Δ : PEnv) (J : PJEnv) (ρ : PValEnv)
    (Q : PPost) (X : PXPost) : LcCode → Prop
  | .let_ x ty v k =>
    PVal.wp ar Δ ρ ty v (fun r => PWp ar Δ J (ρ.set x r) Q X k) X
  | .jp j ps body k =>
    ∀ (Jj : List PVal → Prop),
      (∀ as, as.length = ps.length →
        PWp ar Δ (J.set j Jj) (ρ.bindAll ps as) Q X body → Jj as) →
      PWp ar Δ (J.set j Jj) ρ Q X k
  | .jmp j as =>
    match ρ.evalArgs as with
    | some vs => J j vs
    | none => False
  | .cases x alts =>
    match (ρ x).bind PVal.tag? with
    | some tag => PWpCtorAlts ar Δ J ρ Q X tag alts (PWpDfltAlts ar Δ J ρ Q X alts)
    | none => False
  | .ret a =>
    match ρ.evalArg a with
    | some v => Q v
    | none => False
  | .unreach => X panicUnreachable
  | .oset x i y k =>
    match ρ x, ρ.evalArg y with
    | some xv, some yv =>
      match xv.setObj i yv with
      | some xv' => PWp ar Δ J (ρ.set x xv') Q X k
      | none => False
    | _, _ => False
  | .uset x i y k =>
    match ρ x, ρ y with
    | some xv, some yv =>
      match xv.setUsize i yv with
      | some xv' => PWp ar Δ J (ρ.set x xv') Q X k
      | none => False
    | _, _ => False
  | .sset x n off y ty k =>
    match ρ x, ρ y with
    | some xv, some yv =>
      match xv.setScalar n off ty yv with
      | some xv' => PWp ar Δ J (ρ.set x xv') Q X k
      | none => False
    | _, _ => False
  | .setTag x cidx k =>
    match (ρ x).bind (·.setTag cidx) with
    | some xv' => PWp ar Δ J (ρ.set x xv') Q X k
    | none => False
  | .inc _ _ _ k | .dec _ _ _ k | .del _ k => PWp ar Δ J ρ Q X k

/-- Pass 1 of `cases` dispatch: match the first `.ctor tag _` alternative, else `kDflt`. -/
@[expose] def PWpCtorAlts (ar : PArity) (Δ : PEnv) (J : PJEnv) (ρ : PValEnv)
    (Q : PPost) (X : PXPost) (tag : Nat) : List (LcPat × LcCode) → Prop → Prop
  | [], kDflt => kDflt
  | (.ctor ci _, b) :: rest, kDflt =>
    if ci = tag then PWp ar Δ J ρ Q X b
    else PWpCtorAlts ar Δ J ρ Q X tag rest kDflt
  | (.dflt, _) :: rest, kDflt => PWpCtorAlts ar Δ J ρ Q X tag rest kDflt

/-- Pass 2 of `cases` dispatch: enter the first `.dflt` alternative, or `False`. -/
@[expose] def PWpDfltAlts (ar : PArity) (Δ : PEnv) (J : PJEnv) (ρ : PValEnv)
    (Q : PPost) (X : PXPost) : List (LcPat × LcCode) → Prop
  | [] => False
  | (.dflt, b) :: _ => PWp ar Δ J ρ Q X b
  | (.ctor _ _, _) :: rest => PWpDfltAlts ar Δ J ρ Q X rest
end

/-! ## 5. Module Correctness (`PModuleOk`, `PModuleOkIdx`) -/

/-- Closed / acyclic Tier-P module correctness: every declaration satisfies its contract in `Δ`. -/
@[expose] def PModuleOk (Δ : PEnv) (m : LcModule) : Prop :=
  ∀ d ∈ m.decls, ∀ as Q X,
    as.length = d.params.length → Δ d.name as Q X →
    PWp (modArityOf m) Δ PJEnv.empty (PValEnv.empty.bindAll d.params as) Q X d.body

/-- Measure-indexed Tier-P module correctness for recursive / self-tail modules. -/
@[expose] def PModuleOkIdx (Δ : Nat → PEnv) (m : LcModule) : Prop :=
  (∀ k, PEnv.le (Δ k) (Δ (k + 1))) ∧
  ∀ k, ∀ d ∈ m.decls, ∀ as Q X,
    as.length = d.params.length → Δ k d.name as Q X →
    PWp (modArityOf m) (match k with | 0 => PEnv.bot | k' + 1 => Δ k')
      PJEnv.empty (PValEnv.empty.bindAll d.params as) Q X d.body

/-! ## 6. Executable Fuel-Indexed Oracle (`PEval`) -/

/-- Select the matching `cases` alternative for `tag` (first `.ctor tag _`, else first `.dflt`). -/
@[expose] def selectAlt (tag : Nat) (alts : List (LcPat × LcCode)) : Option LcCode :=
  match alts.find? (fun p => match p.1 with | .ctor ci _ => ci == tag | .dflt => false) with
  | some (_, b) => some b
  | none => (alts.find? (fun p => match p.1 with | .dflt => true | _ => false)).map Prod.snd

/-- Lexical join-point binding entry for `PEval`. -/
abbrev PJEntry : Type := Nat × List LcParam × LcCode × PValEnv

/-- Apply a closure value `fn` to `args` in `PEval`, invoking `callFn` for saturated calls. -/
@[expose] def PEvalApply (callFn : String → List PVal → Option POutcome)
    (fn : PVal) (args : List PVal) : Option POutcome :=
  match fn with
  | .clo f arity fixed =>
    let rem := arity - fixed.length
    if args.isEmpty then some (.ret (.clo f arity fixed))
    else if _hrem : rem = 0 then some (.panic panicBadClosure)
    else if _hlt : args.length < rem then some (.ret (.clo f arity (fixed ++ args)))
    else if _heq : args.length = rem then callFn f (fixed ++ args)
    else
      match callFn f (fixed ++ args.take rem) with
      | some (.ret r) => PEvalApply callFn r (args.drop rem)
      | other => other
  | _ => some (.panic panicBadClosure)
termination_by args.length
decreasing_by
  simp only [List.length_drop]
  omega

/-- Evaluate one `LcVal` in `PEval`, delegating calls to `callFn`. -/
@[expose] def PEvalVal (m : LcModule) (shared : Bool)
    (callFn : String → List PVal → Option POutcome) (ρ : PValEnv) (ty : LcTy) :
    LcVal → Option POutcome
  | .lit (.nat n) => some (.ret (.nat n))
  | .lit (.str s) => some (.ret (.str s))
  | .lit (.scalar n) => some (.ret (.bits ty.width (BitVec.ofNat ty.width n)))
  | .erased => some (.ret .erased)
  | .ap f as =>
    match ρ f, ρ.evalArgs as with
    | some fn, some vs => PEvalApply callFn fn vs
    | _, _ => none
  | .ctor ci as => (ρ.evalArgs as).bind fun vs => (PVal.mkCtor ty ci vs).map .ret
  | .oproj i x => ((ρ x).bind (·.getObj? i)).map .ret
  | .uproj i x => ((ρ x).bind (·.getUsize? i)).map .ret
  | .sproj n off x => ((ρ x).bind (·.getScalar? n off ty)).map .ret
  | .fap f as =>
    (ρ.evalArgs as).bind fun vs =>
      if f == "outOfBounds._redArg" then
        if vs.length == 1 then some (.panic panicOob) else none
      else if pIsPrimName f then (primP f vs).map .ret
      else callFn f vs
  | .pap f as =>
    match modArityOf m f, ρ.evalArgs as with
    | some a, some vs => if vs.length < a then some (.ret (.clo f a vs)) else none
    | _, _ => none
  | .reset _ x => (ρ x).map fun _ => .ret .erased
  | .reuse x ci _ as =>
    match ρ x, ρ.evalArgs as with
    | some _, some vs => (PVal.mkCtor ty ci vs).map .ret
    | _, _ => none
  | .box t x => ((ρ x).bind (PVal.box t)).map .ret
  | .unbox x => ((ρ x).bind (PVal.unbox ty)).map .ret
  | .isShared x => (ρ x).map fun _ => .ret (PVal.bool shared)

mutual
/-- Structurally recursive single-frame evaluator for `LcCode`, delegating function calls and
join-point jumps to `callFn` and `jmpFn` (which consume one unit of fuel). -/
@[expose] def PEvalStep (m : LcModule) (shared : Bool)
    (callFn : String → List PVal → Option POutcome)
    (jmpFn : List PJEntry → PValEnv → LcCode → Option POutcome)
    (jps : List PJEntry) (ρ : PValEnv) : LcCode → Option POutcome
  | .let_ x ty v k =>
    match PEvalVal m shared callFn ρ ty v with
    | some (.ret r) => PEvalStep m shared callFn jmpFn jps (ρ.set x r) k
    | other => other
  | .jp j ps body k => PEvalStep m shared callFn jmpFn ((j, ps, body, ρ) :: jps) ρ k
  | .jmp j as =>
    match jps.dropWhile (fun e => e.1 != j), ρ.evalArgs as with
    | (_, ps, body, ρ0) :: outer, some vs =>
      if vs.length == ps.length then
        jmpFn ((j, ps, body, ρ0) :: outer) (ρ0.bindAll ps vs) body
      else none
    | _, _ => none
  | .cases x alts =>
    match (ρ x).bind PVal.tag? with
    | some tag =>
      PEvalCtorAlts m shared callFn jmpFn jps ρ tag alts
        (PEvalDfltAlts m shared callFn jmpFn jps ρ alts)
    | none => none
  | .ret a => (ρ.evalArg a).map .ret
  | .unreach => some (.panic panicUnreachable)
  | .oset x i y k =>
    match ρ x, ρ.evalArg y with
    | some xv, some yv =>
      match xv.setObj i yv with
      | some xv' => PEvalStep m shared callFn jmpFn jps (ρ.set x xv') k
      | none => none
    | _, _ => none
  | .uset x i y k =>
    match ρ x, ρ y with
    | some xv, some yv =>
      match xv.setUsize i yv with
      | some xv' => PEvalStep m shared callFn jmpFn jps (ρ.set x xv') k
      | none => none
    | _, _ => none
  | .sset x n off y ty k =>
    match ρ x, ρ y with
    | some xv, some yv =>
      match xv.setScalar n off ty yv with
      | some xv' => PEvalStep m shared callFn jmpFn jps (ρ.set x xv') k
      | none => none
    | _, _ => none
  | .setTag x cidx k =>
    match (ρ x).bind (·.setTag cidx) with
    | some xv' => PEvalStep m shared callFn jmpFn jps (ρ.set x xv') k
    | none => none
  | .inc _ _ _ k | .dec _ _ _ k | .del _ k => PEvalStep m shared callFn jmpFn jps ρ k

/-- Pass 1 of `PEvalStep` `cases` dispatch: first `.ctor tag _` alternative, else `dflt`. -/
@[expose] def PEvalCtorAlts (m : LcModule) (shared : Bool)
    (callFn : String → List PVal → Option POutcome)
    (jmpFn : List PJEntry → PValEnv → LcCode → Option POutcome)
    (jps : List PJEntry) (ρ : PValEnv) (tag : Nat) :
    List (LcPat × LcCode) → Option POutcome → Option POutcome
  | [], dflt => dflt
  | (.ctor ci _, b) :: rest, dflt =>
    if ci == tag then PEvalStep m shared callFn jmpFn jps ρ b
    else PEvalCtorAlts m shared callFn jmpFn jps ρ tag rest dflt
  | (.dflt, _) :: rest, dflt => PEvalCtorAlts m shared callFn jmpFn jps ρ tag rest dflt

/-- Pass 2 of `PEvalStep` `cases` dispatch: first `.dflt` alternative, else `none`. -/
@[expose] def PEvalDfltAlts (m : LcModule) (shared : Bool)
    (callFn : String → List PVal → Option POutcome)
    (jmpFn : List PJEntry → PValEnv → LcCode → Option POutcome)
    (jps : List PJEntry) (ρ : PValEnv) : List (LcPat × LcCode) → Option POutcome
  | [] => none
  | (.dflt, b) :: _ => PEvalStep m shared callFn jmpFn jps ρ b
  | (.ctor _ _, _) :: rest => PEvalDfltAlts m shared callFn jmpFn jps ρ rest
end

/-- Fuel-indexed big-step evaluator for `LcCode` (fuel decrements on calls and `jmp`). -/
@[expose] def PEvalCode (fuel : Nat) (m : LcModule) (shared : Bool)
    (jps : List PJEntry) (ρ : PValEnv) (code : LcCode) : Option POutcome :=
  match fuel with
  | 0 => none
  | f + 1 =>
    let callFn (fn : String) (args : List PVal) : Option POutcome :=
      match m.decls.find? (·.name == fn) with
      | some d =>
        if args.length == d.params.length then
          PEvalCode f m shared [] (PValEnv.empty.bindAll d.params args) d.body
        else none
      | none => none
    PEvalStep m shared callFn (PEvalCode f m shared) jps ρ code

/-- Top-level executable fuel-indexed Tier-P oracle for module declaration `fn`. -/
@[expose] def PEval (fuel : Nat) (m : LcModule) (fn : String) (args : List PVal)
    (shared : Bool := false) : Option POutcome :=
  match m.decls.find? (·.name == fn) with
  | some d =>
    if args.length == d.params.length then
      PEvalCode fuel m shared [] (PValEnv.empty.bindAll d.params args) d.body
    else none
  | none => none

end LeanQbe.T.LeanLCNF.Sem
