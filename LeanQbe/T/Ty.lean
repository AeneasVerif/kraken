module

/-!
# Types, values, bit views, and tuple infrastructure

The typed IR uses four value type constructors (`Ty`):
* `bool` (`Bool`)
* `bits n` (`BitVec n`)
* `float f` (`BitVec f.width` for IEEE interchange formats `h/s/d/q`: NaN payloads are preserved
  by moves, loads, stores, and bitcasts; floating-point operations interpret the bits)
* `pair a b` (`Val a × Val b`)

Vectors of `2^k` lanes are the balanced binary tree `Ty.vec k t`. Multi-result operations,
call signatures, and head-bound block parameters use `Tup`, a nested product type ending in `Unit`
so that pattern-matching binders `fun (x, y, ()) => …` are definitionally projections.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## IEEE floating-point formats and type codes -/

/-- IEEE-754 binary interchange formats (16/32/64/128 bits). -/
inductive Fmt
  | h
  | s
  | d
  | q
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Bit width of an IEEE interchange format. -/
@[reducible] def Fmt.width : Fmt → Nat
  | .h => 16
  | .s => 32
  | .d => 64
  | .q => 128

/-- Value types of the typed IR. -/
inductive Ty
  | bool
  | bits (n : Nat)
  | float (f : Fmt)
  | pair (a b : Ty)
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Semantic domain of a type code. -/
@[reducible] def Val : Ty → Type
  | .bool => Bool
  | .bits n => BitVec n
  | .float f => BitVec f.width
  | .pair a b => Val a × Val b

@[instance_reducible] def Val.decEq : (t : Ty) → DecidableEq (Val t)
  | .bool => inferInstanceAs (DecidableEq Bool)
  | .bits n => inferInstanceAs (DecidableEq (BitVec n))
  | .float f => inferInstanceAs (DecidableEq (BitVec f.width))
  | .pair a b => @instDecidableEqProd _ _ (Val.decEq a) (Val.decEq b)

@[instance_reducible] def Val.inhabited : (t : Ty) → Inhabited (Val t)
  | .bool => inferInstanceAs (Inhabited Bool)
  | .bits n => inferInstanceAs (Inhabited (BitVec n))
  | .float f => inferInstanceAs (Inhabited (BitVec f.width))
  | .pair a b => @instInhabitedProd _ _ (Val.inhabited a) (Val.inhabited b)

@[instance_reducible] def Val.repr : (t : Ty) → Repr (Val t)
  | .bool => inferInstanceAs (Repr Bool)
  | .bits n => inferInstanceAs (Repr (BitVec n))
  | .float f => inferInstanceAs (Repr (BitVec f.width))
  | .pair a b => let _ := Val.repr a; let _ := Val.repr b; inferInstanceAs (Repr (Val a × Val b))

attribute [local instance] Val.decEq Val.inhabited Val.repr

@[instance_reducible] instance (priority := low) instDecidableEqVal (t : Ty) : DecidableEq (Val t) :=
  Val.decEq t
@[instance_reducible] instance (priority := low) instInhabitedVal (t : Ty) : Inhabited (Val t) :=
  Val.inhabited t
@[instance_reducible] instance (priority := low) instReprVal (t : Ty) : Repr (Val t) :=
  Val.repr t

abbrev i8 : Ty := .bits 8
abbrev i16 : Ty := .bits 16
abbrev i32 : Ty := .bits 32
abbrev i64 : Ty := .bits 64
abbrev f16 : Ty := .float .h
abbrev f32 : Ty := .float .s
abbrev f64 : Ty := .float .d
abbrev f128 : Ty := .float .q

/-- `2^k` lanes of `t`, as a balanced tree. -/
@[reducible] def Ty.vec : Nat → Ty → Ty
  | 0, t => t
  | k + 1, t => .pair (Ty.vec k t) (Ty.vec k t)

abbrev v4i32 : Ty := Ty.vec 2 i32
abbrev v8i32 : Ty := Ty.vec 3 i32
abbrev v2i64 : Ty := Ty.vec 1 i64
abbrev v4f32 : Ty := Ty.vec 2 f32

/-- Type of a comparison mask: one `bool` per leaf. -/
@[reducible] def Ty.mask : Ty → Ty
  | .pair a b => .pair a.mask b.mask
  | _ => .bool

/-- Size in bits (used for memory accesses and bitcasts).
Fields of a `pair a b` are tightly bit-packed with no inter-field padding (`a.size + b.size`);
for example, `.pair .bool i8` has size `9` bits (`bytes = 2`), so the `i8` straddles bits `1..8`
across the byte `0` / byte `1` boundary. -/
@[reducible] def Ty.size : Ty → Nat
  | .bool => 1
  | .bits n => n
  | .float f => f.width
  | .pair a b => a.size + b.size

/-- Number of bytes needed to store `t` in memory (ceiling `⌈t.size / 8⌉` of the bit-packed
size; e.g. `.pair .bool i8` takes `2` bytes with the `i8` straddling byte `0` and byte `1`). -/
@[reducible] def Ty.bytes (t : Ty) : Nat := (t.size + 7) / 8

/-- True iff `t` contains any floating-point leaf. -/
@[reducible] def Ty.hasFloat : Ty → Bool
  | .float _ => true
  | .pair a b => a.hasFloat || b.hasFloat
  | _ => false

/-- True iff every leaf of `t` is a floating-point type. -/
@[reducible] def Ty.isFloatTree : Ty → Bool
  | .float _ => true
  | .pair a b => a.isFloatTree && b.isFloatTree
  | _ => false

/-- True iff every leaf of `t` is a byte-multiple bitvector (`bits n` with `8 ∣ n`). -/
@[reducible] def Ty.bswapOk : Ty → Bool
  | .bits n => n % 8 == 0
  | .pair a b => a.bswapOk && b.bswapOk
  | _ => false

/-! ## Bit views and lane indexing -/

/-- Pack a value into `t.size` bits, placing the first pair component in the low bits with no
inter-field padding (so e.g. `.pair .bool i8` places `bool` in bit `0` and `i8` in bits `1..8`,
straddling the byte boundary when stored in little-endian byte order). -/
def toBits : (t : Ty) → Val t → BitVec t.size
  | .bool, b => BitVec.ofBool b
  | .bits _, x => x
  | .float _, x => x
  | .pair a b, x => (toBits b x.2 ++ toBits a x.1).cast (Nat.add_comm _ _)

/-- Unpack `t.size` bits into `Val t`, reading the first pair component from the low bits
(matching the bit-packed layout of `toBits`, with no inter-field padding). -/
def ofBits : (t : Ty) → BitVec t.size → Val t
  | .bool, x => x.getLsbD 0
  | .bits _, x => x
  | .float _, x => x
  | .pair a b, x => (ofBits a (x.extractLsb' 0 a.size), ofBits b (x.extractLsb' a.size b.size))

/-- Reinterpret the bits of a value of type `t` as a value of type `u` of equal bit size. -/
def bitcastVal (t u : Ty) (h : t.size = u.size) (x : Val t) : Val u :=
  ofBits u ((toBits t x).cast h)

/-- Lane `i` (0-indexed from the left/low end) of a balanced `2^k`-lane vector. -/
def lane : (k : Nat) → {t : Ty} → Val (Ty.vec k t) → Nat → Val t
  | 0, _, x, _ => x
  | k + 1, _, x, i => if i < 2 ^ k then lane k x.1 i else lane k x.2 (i - 2 ^ k)

/-! ## Tuples and typed membership -/

/-- A right-nested tuple indexed by a list of type codes. -/
@[reducible] def Tup {α : Type} (f : α → Type) : List α → Type
  | [] => Unit
  | a :: as => f a × Tup f as

/-- Evidence that `a` appears in `as`. -/
inductive Member {α : Type} : α → List α → Type
  | here {a : α} {as : List α} : Member a (a :: as)
  | there {a b : α} {as : List α} : Member a as → Member a (b :: as)
  deriving DecidableEq

/-- Project element `i` from a tuple. -/
def Tup.get {α : Type} {f : α → Type} : {as : List α} → {a : α} → Tup f as → Member a as → f a
  | _ :: _, _, xs, .here => xs.1
  | _ :: _, _, xs, .there i => xs.2.get i

/-- Map a natural transformation over a tuple. -/
def Tup.map {α : Type} {f g : α → Type} (h : ∀ a, f a → g a) : {as : List α} → Tup f as → Tup g as
  | [], () => ()
  | _ :: _, xs => (h _ xs.1, xs.2.map h)

/-- Pointwise relation over two tuples of the same signature. -/
inductive TRel {α : Type} {f g : α → Type} (R : ∀ a, f a → g a → Prop) :
    {as : List α} → Tup f as → Tup g as → Prop
  | nil : TRel R (as := []) () ()
  | cons {a : α} {as : List α} {x : f a} {y : g a} {xs : Tup f as} {ys : Tup g as} :
      R a x y → TRel R xs ys → TRel R (as := a :: as) (x, xs) (y, ys)

/-- Typed relational context pairing names from two instantiations. -/
abbrev Ctx {α : Type} (f g : α → Type) : Type := List ((a : α) × f a × g a)

/-- Pair two tuples element-wise into a context. -/
def Tup.zip {α : Type} {f g : α → Type} : {as : List α} → Tup f as → Tup g as → Ctx f g
  | [], _, _ => []
  | a :: _, xs, ys => ⟨a, xs.1, ys.1⟩ :: zip xs.2 ys.2

/-- Consecutive de Bruijn levels `n, n + 1, …` for a signature. -/
def Tup.levels {α : Type} : (as : List α) → Nat → Tup (fun _ : α => Nat) as
  | [], _ => ()
  | _ :: as, n => (n, levels as (n + 1))

/-- Every positional entry of two tuples is paired in `G`. -/
def EnvRel {α : Type} {f g : α → Type} (G : Ctx f g) {as : List α}
    (xs : Tup f as) (ys : Tup g as) : Prop :=
  ∀ a (i : Member a as), ⟨a, xs.get i, ys.get i⟩ ∈ G

end LeanQbe.T
