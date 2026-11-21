module

public import LeanQbe.T.Flat

/-!
# Target-parameterized IR legalisation (`T5`, `G13`)

Implements the `G13` packing oracle and target capability specification (`PackOracle`,
`LegalTarget`), the PHOAS-to-PHOAS legalisation pass (`legalExpr`, `Func.legal`), and the
decidable/computable `TFlat.isLegal` / `Func.isLegal` predicate:

* **`G13` packing oracle (`PackOracle`, `LegalTarget`)**: target-neutral capability record
  (importing neither `Kraken.X64` nor `Kraken.AArch64`), reusable directly by `T7` (`Rega`).
  `PackOracle.g13` keeps balanced `Ty.vec k leaf` of target vector register width packed and splits
  all other `pair a b` values into their scalar/packed leaves.
* **(a) Pair & wide-vector splitting**: splits non-packed `pair`s and over-wide vectors across
  function signatures, `let_` results, `group` block parameters, `jump`, `ret`, `call`, and
  `exit`. Eliminates `mkpair`/`unpair` on split pairs into zero-instruction tuple wiring; splits
  byte-aligned `load`/`store` directly and non-byte-aligned `load`/`store` via legal byte chunks.
* **(b) `bits n` widening**: widens `bits n` (`n ∉ target.bitWidths`, `n ≤ 64`) to the next
  supported width with zero-extension invariant (`x' = x.setWidth w`), masking arithmetic/bitwise/
  shift/multiply/conversion results and sign-extending operands (`shl` + `ashr`) for signed
  comparisons, `ashr`, `sdiv`/`srem`/`sdiv0`, `smulw`, `cls`, `sext`, and `sitofp`.
* **(c) Vector halving & scalarization**: recursively halves `vec (k + 1) t = .pair (vec k t) (vec k
  t)`
  (§0f) down to target vector register widths (`512 → 256 → 128`) or down to scalar leaves.
* **(d) Derived opcode expansion**: expands `blend` on `bool` leaves into scalar `select`s,
  expands vector `shl` by uniform immediate into `rotr` + `and` (and `rotl` by uniform immediate
  into `rotr`), scalarizes unsupported vector ops, expands scalar `ternlog` into `and`/`or`/`not`,
  expands `bool` `cmp`/`select`/`add`/`sub`/`mul`/`neg`, and converts general `bitcast`s via
  64-bit word streams.
* **`Legal` predicate (`TFlat.isLegal`, `Func.isLegal`)**: computable `Bool` checker over reified
  `TFlat` verifying legal types, supported bit widths, no unsplit non-packed pairs (except strict
  pack/unpack bridges at packed vector boundaries when packed vectors are enabled), and no
  derived-only opcodes.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## `G13` packing oracle and target capabilities -/

/-- `G13` packing oracle: decides which `.pair` types stay packed as a single register/value unit
(vs splitting along `.pair a b`). Reused directly by `T7` (`Rega`). -/
structure PackOracle where
  /-- True iff `t` (when a `.pair`) is kept packed as a single unit. -/
  keepPacked : Ty → Bool

/-- True iff `t` is a `.pair` that the oracle keeps packed. -/
@[reducible] def PackOracle.isPackedPair (o : PackOracle) : Ty → Bool
  | .pair a b => o.keepPacked (.pair a b)
  | _ => false

/-- Oracle that splits every `.pair` down to scalar leaves (e.g. AArch64 per §0). -/
def PackOracle.none : PackOracle := ⟨fun _ => false⟩

/-- If `t` is a balanced tree `Ty.vec k leaf` with `leaf ∈ vecLeaves`, return `some (k, leaf)`. -/
def matchVecOf (vecLeaves : List Ty) (t : Ty) : Option (Nat × Ty) :=
  if t ∈ vecLeaves then some (0, t)
  else match t with
    | .pair a b =>
      if a == b then (matchVecOf vecLeaves a).map fun (k, leaf) => (k + 1, leaf)
      else none
    | _ => none

/-- Baseline `G13` type-directed packing oracle: keeps balanced `Ty.vec k leaf` trees packed
when `leaf ∈ vecLeaves`, `t` is a `.pair`, and `t.size ∈ vecWidths`; splits all other pairs. -/
def PackOracle.g13 (vecWidths : List Nat) (vecLeaves : List Ty) : PackOracle where
  keepPacked t :=
    match t with
    | .pair _ _ =>
      match matchVecOf vecLeaves t with
      | some _ => t.size ∈ vecWidths
      | Option.none => false
    | _ => false

/-- Target capability specification for `T5` legalisation and `T7` register allocation. -/
structure LegalTarget where
  /-- Packing oracle (`G13`) deciding which `.pair` types stay packed in vector registers. -/
  oracle : PackOracle
  /-- Whether packed vector boundary `mkpair`/`unpair` bridges are permitted (false on scalar-only
  targets like AArch64; true on vector targets like x64). -/
  allowPackBridge : Bool := true
  /-- Supported scalar bit widths (default `[8, 16, 32, 64]`). -/
  bitWidths : List Nat := [8, 16, 32, 64]
  /-- Supported scalar floating-point formats. -/
  floatFmts : List Fmt := [.s, .d]
  /-- Whether `ternlog` is legal on scalar `.bits w` (false: expand to `and`/`or`/`not`). -/
  scalarTernlog : Bool := false
  /-- Whether `cmp` on `.bool` is legal (false: expand to `and`/`or`/`xor`/`not`). -/
  boolCmp : Bool := false
  /-- Whether `select` on `.bool` is legal (false: expand to `and`/`or`/`not`). -/
  boolSelect : Bool := false
  /-- Whether bitwise logic (`and`/`or`/`xor`/`not`/`ternlog`) is legal directly on scalar floats
  (false: `bitcast` to integer `bits`, run bitwise op, `bitcast` back). -/
  scalarFloatBitwise : Bool := false
  /-- Packed vector integer/shuffle/SHA opcodes supported natively at packed vector type `t`,
  given whether the right-hand operand (if any) is a uniform immediate shift/rotate count. -/
  vecIntOpSupported : {as rs : List Ty} → OpCode as rs → Ty → (uniformImmRhs : Bool) → Bool
  /-- Packed vector floating-point opcodes supported natively at packed vector type `t`. -/
  vecFloatOpSupported : {as rs : List Ty} → OpCode as rs → Ty → Bool

/-- True iff `t` is a balanced `Ty.vec k (.bits 32)` (`i32` lanes). -/
def isI32Vec : Ty → Bool
  | .bits 32 => true
  | .pair a b => a == b && isI32Vec a
  | _ => false

/-- True iff `t` is a balanced `Ty.vec k (.float .s)` (`f32` lanes). -/
def isF32Vec : Ty → Bool
  | .float .s => true
  | .pair a b => a == b && isF32Vec a
  | _ => false

/-- AArch64 scalar target (no vector or FP registers in upstream Kraken per §0). -/
def LegalTarget.aarch64 : LegalTarget where
  oracle := .none
  allowPackBridge := false
  bitWidths := [8, 16, 32, 64]
  floatFmts := []
  vecIntOpSupported _ _ _ := false
  vecFloatOpSupported _ _ := false

/-- Scalar target with IEEE scalar floats (`h`/`s`/`d`) and no packed vectors. -/
def LegalTarget.scalar64 : LegalTarget where
  oracle := .none
  allowPackBridge := false
  bitWidths := [8, 16, 32, 64]
  floatFmts := [.h, .s, .d]
  vecIntOpSupported _ _ _ := false
  vecFloatOpSupported _ _ := false

/-- x64 target parameterized by supported vector register bit widths (`[128]`, `[128, 256]`, or
`[128, 256, 512]`), supporting the §0 `i32`/`f32` vector subset. -/
def LegalTarget.x64 (vecWidths : List Nat := [128, 256, 512]) : LegalTarget where
  oracle := PackOracle.g13 vecWidths [i32, f32]
  allowPackBridge := !vecWidths.isEmpty
  bitWidths := [8, 16, 32, 64]
  floatFmts := [.s, .d]
  vecIntOpSupported {as rs} code t uniformImm :=
    match code with
    | .copy _ => true
    | .add _ => isI32Vec t
    | .and _ | .or _ | .xor _ | .not _ | .ternlog _ _ => true
    | .rotr _ | .lshr _ => isI32Vec t && uniformImm
    | .shufd _ _ | .shufb _ | .alignr _ _ | .blendw _ _ => t.size != 0 && t.size % 128 == 0
    | .sha256rnds2 | .sha256msg1 | .sha256msg2 => t == v4i32
    | _ => false
  vecFloatOpSupported {_as _rs} code t :=
    match code with
    | .fadd _ | .fsub _ => isF32Vec t
    | _ => false

abbrev LegalTarget.x64SSE : LegalTarget := LegalTarget.x64 [128]
abbrev LegalTarget.x64AVX2 : LegalTarget := LegalTarget.x64 [128, 256]
abbrev LegalTarget.x64AVX512 : LegalTarget := LegalTarget.x64 [128, 256, 512]

/-! ## Bit-width widening and type/signature splitting -/

/-- Smallest element of `ws` that is `≥ n`, if any. -/
def minGe (n : Nat) : List Nat → Option Nat
  | [] => none
  | w :: ws =>
    match minGe n ws with
    | none => if n ≤ w then some w else none
    | some best => if n ≤ w && w < best then some w else some best

/-- Widen `n` to the smallest supported bit width `w ∈ target.bitWidths` with `n ≤ w`, or `n` if
none exists. -/
def LegalTarget.widenWidth (target : LegalTarget) (n : Nat) : Nat :=
  (minGe n target.bitWidths).getD n

/-- True iff every atomic leaf of `t` is legal under `target`. -/
def LegalTarget.hasLegalLeaves (target : LegalTarget) : Ty → Bool
  | .bool => true
  | .bits n => n ∈ target.bitWidths
  | .float f => f ∈ target.floatFmts
  | .pair a b => target.hasLegalLeaves a && target.hasLegalLeaves b

/-- True iff `t` is kept packed as a single vector/aggregate unit by `target`.
Only packs `.pair`s when `allowPackBridge = true` and every leaf of `t` is already legal. -/
@[reducible] def LegalTarget.keepsPacked (target : LegalTarget) (t : Ty) : Bool :=
  target.allowPackBridge && target.oracle.isPackedPair t && target.hasLegalLeaves t

/-- Single legal leaf check (`bool`, `bits w` with `w ∈ bitWidths`, `float f` with `f ∈ floatFmts`,
or packed pair). -/
def LegalTarget.isLegalTy (target : LegalTarget) : Ty → Bool
  | .bool => true
  | .bits n => n ∈ target.bitWidths
  | .float f => f ∈ target.floatFmts
  | .pair a b => target.keepsPacked (.pair a b)

/-- Signature check: every type in `ts` is a single legal type. -/
def LegalTarget.isLegalSig (target : LegalTarget) (ts : List Ty) : Bool :=
  ts.all target.isLegalTy

/-- Legalized type list for a source type `t`: scalar leaves are widened if needed, packed pairs
stay as `[t]`, and non-packed pairs flatten recursively to their leaves. -/
def LegalTarget.legalTys (target : LegalTarget) : Ty → List Ty
  | .bool => [.bool]
  | .bits n => [.bits (target.widenWidth n)]
  | .float f => [.float f]
  | .pair a b =>
    if target.keepsPacked (.pair a b) then [.pair a b]
    else target.legalTys a ++ target.legalTys b

/-- Legalized signature for a list of source types. -/
def LegalTarget.legalSig (target : LegalTarget) : List Ty → List Ty
  | [] => []
  | t :: ts => target.legalTys t ++ target.legalSig ts

/-- Scalar-only leaf types of `t` (ignoring packing, widening `bits n`). -/
def LegalTarget.leafTys (target : LegalTarget) : Ty → List Ty
  | .bool => [.bool]
  | .bits n => [.bits (target.widenWidth n)]
  | .float f => [.float f]
  | .pair a b => target.leafTys a ++ target.leafTys b

/-- True iff `t` is a recursively byte-aligned non-`.bool` structure (`load`/`store` can split
along `.pair a b` directly at byte offsets without bit-straddling). -/
def Ty.isByteAlignedStruct : Ty → Bool
  | .bool => false
  | .bits n => n > 0 && n % 8 == 0
  | .float _ => true
  | .pair a b => a.isByteAlignedStruct && b.isByteAlignedStruct

/-! ## Tuple append/split and parameter/label plumbing -/

/-- Concatenate two tuples of types `as` and `bs`. -/
def tupAppend {α : Type} {f : α → Type} :
    {as bs : List α} → Tup f as → Tup f bs → Tup f (as ++ bs)
  | [], _, (), ys => ys
  | _ :: _, _, (x, xs), ys => (x, tupAppend xs ys)

/-- Split a tuple over `as ++ bs` into its `as` prefix and `bs` suffix. -/
def tupSplit {α : Type} {f : α → Type} :
    {as bs : List α} → Tup f (as ++ bs) → Tup f as × Tup f bs
  | [], _, ys => ((), ys)
  | _ :: _, _, (x, rest) =>
    let (xs, ys) := tupSplit rest
    ((x, xs), ys)

/-- Convert a tuple of variables into a tuple of `.var` operands. -/
def varsTup {V : Ty → Type} : {ts : List Ty} → Tup V ts → Tup (Arg V) ts
  | [], () => ()
  | _ :: _, (v, vs) => (.var v, varsTup vs)

/-- Map `Member a as` through `g` to `Member (g a) (as.map g)`. -/
def Member.map {α β : Type} (g : α → β) : {a : α} → {as : List α} → Member a as →
    Member (g a) (as.map g)
  | _, _ :: _, .here => .here
  | _, _ :: _, .there i => .there (Member.map g i)

/-- Reinterpret `Tup f (as.map g)` as `Tup (fun a => f (g a)) as`. -/
def tupLiftMap {α β : Type} (g : α → β) (f : β → Type) :
    {as : List α} → Tup f (as.map g) → Tup (fun a => f (g a)) as
  | [], () => ()
  | _ :: _, (x, xs) => (x, tupLiftMap g f xs)

/-- Variable representation in input expressions during legalisation: each source variable of type
`t` maps to a tuple of target operands of types `target.legalTys t`. -/
abbrev LVar (target : LegalTarget) (V : Ty → Type) (t : Ty) : Type :=
  Tup (Arg V) (target.legalTys t)

/-- Label representation in input expressions during legalisation: each source label of signature
`ts` maps to a target label of signature `target.legalSig ts`. -/
abbrev LLab (target : LegalTarget) (L : List Ty → Type) (ts : List Ty) : Type :=
  L (target.legalSig ts)

/-- Cast a bitvector operand across equal widths (without rewriting inside surrounding types). -/
def castArgBits {V : Ty → Type} {m n : Nat} (h : m = n) (x : Arg V (.bits m)) :
    Arg V (.bits n) :=
  h ▸ x

/-- Encode a concrete source value directly into `.imm` leaf operands (`leafTys t`). -/
def leafImm {V : Ty → Type} (target : LegalTarget) : (t : Ty) → Val t →
  Tup (Arg V) (target.leafTys t)
  | .bool, b => (.imm b, ())
  | .bits n, x => (.imm (x.setWidth (target.widenWidth n)), ())
  | .float _, x => (.imm x, ())
  | .pair a b, p => tupAppend (leafImm target a p.1) (leafImm target b p.2)

/-- Reinterpret `Tup (Arg V) (target.legalTys (.pair a b))` as `[.pair a b]` when packed. -/
def packedToTup {target : LegalTarget} {V : Ty → Type} {a b : Ty}
    (h : target.keepsPacked (.pair a b) = true) :
    Tup (Arg V) (target.legalTys (.pair a b)) → Tup (Arg V) [.pair a b] :=
  fun xs => cast (by simp [LegalTarget.legalTys, h]) xs

/-- Reinterpret `Tup (Arg V) [.pair a b]` as `target.legalTys (.pair a b)` when packed. -/
def tupToPacked {target : LegalTarget} {V : Ty → Type} {a b : Ty}
    (h : target.keepsPacked (.pair a b) = true) :
    Tup (Arg V) [.pair a b] → Tup (Arg V) (target.legalTys (.pair a b)) :=
  fun xs => cast (by simp [LegalTarget.legalTys, h]) xs

/-- Reinterpret `Tup (Arg V) (target.legalTys (.pair a b))` as split leaves when unpacked. -/
def splitToTup {target : LegalTarget} {V : Ty → Type} {a b : Ty}
    (h : target.keepsPacked (.pair a b) = false) :
    Tup (Arg V) (target.legalTys (.pair a b)) →
      Tup (Arg V) (target.legalTys a ++ target.legalTys b) :=
  fun xs => cast (by simp [LegalTarget.legalTys, h]) xs

/-- Reinterpret split leaves as `Tup (Arg V) (target.legalTys (.pair a b))` when unpacked. -/
def tupToSplit {target : LegalTarget} {V : Ty → Type} {a b : Ty}
    (h : target.keepsPacked (.pair a b) = false) :
    Tup (Arg V) (target.legalTys a ++ target.legalTys b) →
      Tup (Arg V) (target.legalTys (.pair a b)) :=
  fun xs => cast (by simp [LegalTarget.legalTys, h]) xs

/-- Encode a concrete source value `Val t` into its legalized target tuple (zero-extending widened
`bits n` and flattening split pairs). -/
def encodeVal (target : LegalTarget) : (t : Ty) → Val t → Tup Val (target.legalTys t)
  | .bool, b => (b, ())
  | .bits n, x => (x.setWidth (target.widenWidth n), ())
  | .float _, x => (x, ())
  | .pair a b, p =>
    if h : target.keepsPacked (.pair a b) then
      cast (by simp [LegalTarget.legalTys, h]) (show Tup Val [.pair a b] from (p, ()))
    else
      let hf := Bool.eq_false_iff.mpr h
      cast (by simp [LegalTarget.legalTys, hf])
        (tupAppend (encodeVal target a p.1) (encodeVal target b p.2))

/-- Encode a concrete source tuple `Tup Val ts` into `Tup Val (target.legalSig ts)`. -/
def encodeTup (target : LegalTarget) : (ts : List Ty) → Tup Val ts → Tup Val (target.legalSig ts)
  | [], () => ()
  | t :: ts, (x, xs) => tupAppend (encodeVal target t x) (encodeTup target ts xs)

/-- Encode a concrete source value into a tuple of `.imm` operands. -/
def encodeImm {V : Ty → Type} (target : LegalTarget) :
    (t : Ty) → Val t → Tup (Arg V) (target.legalTys t)
  | .bool, b => (.imm b, ())
  | .bits n, x => (.imm (x.setWidth (target.widenWidth n)), ())
  | .float _, x => (.imm x, ())
  | .pair a b, p =>
    if h : target.keepsPacked (.pair a b) then
      tupToPacked h (.imm p, ())
    else
      let hf := Bool.eq_false_iff.mpr h
      tupToSplit hf (tupAppend (encodeImm target a p.1) (encodeImm target b p.2))

/-- Lower an operand `Arg (LVar target V) t` into a tuple of target operands. -/
def legalArg (target : LegalTarget) {V : Ty → Type} {t : Ty} :
    Arg (LVar target V) t → Tup (Arg V) (target.legalTys t)
  | .var xs => xs
  | .imm c => encodeImm target t c

/-- Split a flat tuple of target variables `Tup V (target.legalSig ts)` into `Tup (LVar target V)
  ts`. -/
def splitParams (target : LegalTarget) {V : Ty → Type} :
    (ts : List Ty) → Tup V (target.legalSig ts) → Tup (LVar target V) ts
  | [], () => ()
  | _ :: ts, xs =>
    let (xt, xts) := tupSplit xs
    (varsTup xt, splitParams target ts xts)

/-- Flatten a tuple of source arguments `Tup (Arg (LVar target V)) ts` into target arguments. -/
def joinArgs (target : LegalTarget) {V : Ty → Type} :
    {ts : List Ty} → Tup (Arg (LVar target V)) ts → Tup (Arg V) (target.legalSig ts)
  | [], () => ()
  | _ :: _, (a, as) => tupAppend (legalArg target a) (joinArgs target as)

/-! ## Low-level bitvector and packed-pair CPS emitters -/

section Emitters

/-- Low `n` bits set to `1` inside `BitVec w` (for `n ≤ w`). -/
def lowMask (n w : Nat) : BitVec w :=
  (BitVec.allOnes w) >>> (w - n)

/-- Sign-extend a zero-extended `n`-bit value stored in `BitVec w` (`0 < n < w`) to full width `w`
via `shl` + `ashr` by `w - n`. -/
def emitSextToW {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (n w : Nat)
    (x : Arg V (.bits w)) (k : Arg V (.bits w) → Expr V L rs) : Expr V L rs :=
  if n == 0 || w ≤ n then k x
  else
    let sh := BitVec.ofNat w (w - n)
    .let_ (op2 (.shl (.bits w)) x (.imm sh)) fun (s, ()) =>
    .let_ (op2 (.ashr (.bits w)) (.var s) (.imm sh)) fun (r, ()) =>
    k (.var r)

/-- Mask a `BitVec w` down to its low `n` bits when `n < w`. -/
def emitMaskToN {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (n w : Nat)
    (x : Arg V (.bits w)) (k : Arg V (.bits w) → Expr V L rs) : Expr V L rs :=
  if n == 0 then k (.imm 0#w)
  else if w ≤ n then k x
  else .let_ (op2 (.and (.bits w)) x (.imm (lowMask n w))) fun (r, ()) => k (.var r)

/-- Compute `c.toNat % n` in `BitVec w` when `0 < n < w`. -/
def emitCountMod {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (n w : Nat)
    (c : Arg V (.bits w)) (k : Arg V (.bits w) → Expr V L rs) : Expr V L rs :=
  match c with
  | .imm cb => k (.imm (BitVec.ofNat w (cb.toNat % n)))
  | .var _ =>
    .let_ (op2 (.urem w) c (.imm (BitVec.ofNat w n))) fun (r, ()) => k (.var r)

/-- Unpack an `Arg V t` into scalar leaves `target.leafTys t` via `.unpair` and `.zext`. -/
def unpackToLeaves (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (t : Ty) → Arg V t → (Tup (Arg V) (target.leafTys t) → Expr V L rs) → Expr V L rs
  | .bool, x, k => k (x, ())
  | .bits n, x, k =>
    let w := target.widenWidth n
    if h : n = w then k (castArgBits h x, ())
    else if n ≤ w then .let_ (op1 (.zext n w) x) fun (r, ()) => k (.var r, ())
    else k (.imm 0#w, ())
  | .float _, x, k => k (x, ())
  | .pair a b, p, k =>
    match p with
    | .imm c => k (leafImm target (.pair a b) c)
    | .var v =>
      .let_ (op1 (.unpair a b) (.var v)) fun (va, vb, ()) =>
        unpackToLeaves target a (.var va) fun la =>
          unpackToLeaves target b (.var vb) fun lb =>
            k (tupAppend la lb)

/-- Unpack an `Arg V t` into `target.legalTys t` (stopping at packed nodes). -/
def unpackToLegal (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (t : Ty) → Arg V t → (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | .bool, x, k => k (x, ())
  | .bits n, x, k =>
    let w := target.widenWidth n
    if h : n = w then k (castArgBits h x, ())
    else if n ≤ w then .let_ (op1 (.zext n w) x) fun (r, ()) => k (.var r, ())
    else k (.imm 0#w, ())
  | .float _, x, k => k (x, ())
  | .pair a b, p, k =>
    if h : target.keepsPacked (.pair a b) then
      k (tupToPacked h (p, ()))
    else
      let hf := Bool.eq_false_iff.mpr h
      match p with
      | .imm c => k (encodeImm target (.pair a b) c)
      | .var v =>
        .let_ (op1 (.unpair a b) (.var v)) fun (va, vb, ()) =>
          unpackToLegal target a (.var va) fun la =>
            unpackToLegal target b (.var vb) fun lb =>
              k (tupToSplit hf (tupAppend la lb))

/-- Pack `Tup (Arg V) (target.legalTys t)` back into `Arg V t`. -/
def packFromLegal (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (t : Ty) → Tup (Arg V) (target.legalTys t) → (Arg V t → Expr V L rs) → Expr V L rs
  | .bool, (x, ()), k => k x
  | .bits n, (x, ()), k =>
    let w := target.widenWidth n
    if h : n = w then k (castArgBits h.symm x)
    else if n ≤ w then .let_ (op1 (.trunc w n) x) fun (r, ()) => k (.var r)
    else k (.imm default)
  | .float _, (x, ()), k => k x
  | .pair a b, xs, k =>
    if h : target.keepsPacked (.pair a b) then
      k (packedToTup h xs).1
    else
      let hf := Bool.eq_false_iff.mpr h
      let (la, lb) := tupSplit (splitToTup hf xs)
      packFromLegal target a la fun va =>
        packFromLegal target b lb fun vb =>
          .let_ (op2 (.mkpair a b) va vb) fun (p, ()) => k (.var p)

/-- Convert `Tup (Arg V) (target.legalTys t)` into `Tup (Arg V) (target.leafTys t)`. -/
def splitLegalToLeaves (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (t : Ty) → Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.leafTys t) → Expr V L rs) → Expr V L rs
  | .bool, xs, k => k xs
  | .bits _, xs, k => k xs
  | .float _, xs, k => k xs
  | .pair a b, xs, k =>
    if h : target.keepsPacked (.pair a b) then
      unpackToLeaves target (.pair a b) (packedToTup h xs).1 k
    else
      let hf := Bool.eq_false_iff.mpr h
      let (la, lb) := tupSplit (splitToTup hf xs)
      splitLegalToLeaves target a la fun fa =>
        splitLegalToLeaves target b lb fun fb =>
          k (tupAppend fa fb)

/-- Convert `Tup (Arg V) (target.leafTys t)` back into `Tup (Arg V) (target.legalTys t)`. -/
def packLeavesToLegal (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (t : Ty) → Tup (Arg V) (target.leafTys t) →
    (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | .bool, xs, k => k xs
  | .bits _, xs, k => k xs
  | .float _, xs, k => k xs
  | .pair a b, xs, k =>
    if h : target.keepsPacked (.pair a b) then
      let (fa, fb) := tupSplit xs
      packLeavesToLegal target a fa fun la =>
        packLeavesToLegal target b fb fun lb =>
          packFromLegal target a la fun va =>
            packFromLegal target b lb fun vb =>
              .let_ (op2 (.mkpair a b) va vb) fun (p, ()) =>
                k (tupToPacked h (.var p, ()))
    else
      let hf := Bool.eq_false_iff.mpr h
      let (fa, fb) := tupSplit xs
      packLeavesToLegal target a fa fun la =>
        packLeavesToLegal target b fb fun lb =>
          k (tupToSplit hf (tupAppend la lb))

/-! ## Ternary logic and boolean expansion helpers -/

/-- Expand `ternlog t imm` into `not`/`and`/`or` on scalar `t` (`.bool` or `.bits w`). -/
def emitTernlog {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (t : Ty) (zeroVal onesVal : Val t)
    (a b c : Arg V t) (imm : BitVec 8)
    (k : Arg V t → Expr V L rs) : Expr V L rs :=
  if imm == 0#8 then k (.imm zeroVal)
  else if imm == 0xff#8 then k (.imm onesVal)
  else
    .let_ (op1 (.not t) a) fun (na, ()) =>
    .let_ (op1 (.not t) b) fun (nb, ()) =>
    .let_ (op1 (.not t) c) fun (nc, ()) =>
    go 0 none a b c (.var na) (.var nb) (.var nc)
where
  go (idx : Nat) (acc : Option (Arg V t))
      (a b c na nb nc : Arg V t) : Expr V L rs :=
    if idx ≥ 8 then
      match acc with
      | some res => k res
      | none => k (.imm zeroVal)
    else if imm.getLsbD idx then
      let pa := if idx / 4 % 2 == 1 then a else na
      let pb := if idx / 2 % 2 == 1 then b else nb
      let pc := if idx % 2 == 1 then c else nc
      .let_ (op2 (.and t) pa pb) fun (t1, ()) =>
      .let_ (op2 (.and t) (.var t1) pc) fun (term, ()) =>
      match acc with
      | none => go (idx + 1) (some (.var term)) a b c na nb nc
      | some prev =>
        .let_ (op2 (.or t) prev (.var term)) fun (acc', ()) =>
        go (idx + 1) (some (.var acc')) a b c na nb nc
    else go (idx + 1) acc a b c na nb nc
  termination_by 8 - idx

/-- Expand `ternlog (.bits w) imm` into `not`/`and`/`or` on `.bits w`. -/
def emitTernlogBits {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (w : Nat)
    (a b c : Arg V (.bits w)) (imm : BitVec 8)
    (k : Arg V (.bits w) → Expr V L rs) : Expr V L rs :=
  emitTernlog (.bits w) 0#w (BitVec.allOnes w) a b c imm k

/-- Expand `ternlog .bool imm` into `not`/`and`/`or` on `.bool`. -/
def emitTernlogBool {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (a b c : Arg V .bool) (imm : BitVec 8)
    (k : Arg V .bool → Expr V L rs) : Expr V L rs :=
  emitTernlog .bool false true a b c imm k

/-- Expand `cmp o .bool a b` into pure `.bool` logic (`not`/`and`/`or`/`xor`). -/
def emitBoolCmp {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (o : CmpOp) (a b : Arg V .bool) (k : Arg V .bool → Expr V L rs) : Expr V L rs :=
  match o with
  | .eq =>
    .let_ (op2 (.xor .bool) a b) fun (x, ()) =>
    .let_ (op1 (.not .bool) (.var x)) fun (r, ()) => k (.var r)
  | .ne => .let_ (op2 (.xor .bool) a b) fun (r, ()) => k (.var r)
  | .ult | .sgt =>
    .let_ (op1 (.not .bool) a) fun (na, ()) =>
    .let_ (op2 (.and .bool) (.var na) b) fun (r, ()) => k (.var r)
  | .ule | .sge =>
    .let_ (op1 (.not .bool) a) fun (na, ()) =>
    .let_ (op2 (.or .bool) (.var na) b) fun (r, ()) => k (.var r)
  | .ugt | .slt =>
    .let_ (op1 (.not .bool) b) fun (nb, ()) =>
    .let_ (op2 (.and .bool) a (.var nb)) fun (r, ()) => k (.var r)
  | .uge | .sle =>
    .let_ (op1 (.not .bool) b) fun (nb, ()) =>
    .let_ (op2 (.or .bool) a (.var nb)) fun (r, ()) => k (.var r)

/-- Expand `select .bool c a b` into `(c && a) || (!c && b)`. -/
def emitBoolSelect {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (c a b : Arg V .bool) (k : Arg V .bool → Expr V L rs) : Expr V L rs :=
  .let_ (op2 (.and .bool) c a) fun (t1, ()) =>
  .let_ (op1 (.not .bool) c) fun (nc, ()) =>
  .let_ (op2 (.and .bool) (.var nc) b) fun (t2, ()) =>
  .let_ (op2 (.or .bool) (.var t1) (.var t2)) fun (r, ()) => k (.var r)

/-! ## Packed vector uniform shift/rotate helpers -/

/-- If `t` is non-empty, has only `.bits w` leaves of a single positive width `w`, and `c` has
the same `val.toNat % w` at every leaf, return `some (w, count)`. -/
def uniformShiftLeaf? : (t : Ty) → Val t → Option (Nat × Nat)
  | .bits w, x => if w == 0 then none else some (w, x.toNat % w)
  | .pair a b, (x, y) => do
    let (wa, ca) ← uniformShiftLeaf? a x
    let (wb, cb) ← uniformShiftLeaf? b y
    if wa == wb && ca == cb then some (wa, ca) else none
  | _, _ => none

/-- Construct a `Val t` filling every `.bits w` leaf with `v`. -/
def splatBits (w : Nat) (v : BitVec w) : (t : Ty) → Val t
  | .bool => false
  | .bits n => if h : n = w then h ▸ v else 0#n
  | .float f => 0#f.width
  | .pair a b => (splatBits w v a, splatBits w v b)

/-! ## General 64-bit word stream packing/unpacking (`bitcast`, unaligned `load`/`store`, scalar
  128-bit ops) -/

/-- Append one `w`-bit leaf (passed as zero-extended `Arg V i64`, `0 ≤ w ≤ 64`) onto the
64-bit word stream accumulator `(ws, acc, accBits)`. -/
def pushLeafWord64 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (w : Nat) (leaf : Arg V i64)
    (ws : List (Arg V i64)) (acc : Arg V i64) (accBits : Nat)
    (cont : List (Arg V i64) → Arg V i64 → Nat → Expr V L rs) : Expr V L rs :=
  if w == 0 then cont ws acc accBits
  else if accBits == 0 then
    if w ≥ 64 then cont (ws ++ [leaf]) (.imm 0#64) 0
    else cont ws leaf w
  else
    .let_ (op2 (.shl i64) leaf (.imm (BitVec.ofNat 64 accBits))) fun (sh, ()) =>
    .let_ (op2 (.or i64) acc (.var sh)) fun (loWord, ()) =>
    if accBits + w < 64 then
      cont ws (.var loWord) (accBits + w)
    else if accBits + w == 64 then
      cont (ws ++ [.var loWord]) (.imm 0#64) 0
    else
      .let_ (op2 (.lshr i64) leaf (.imm (BitVec.ofNat 64 (64 - accBits)))) fun (hiPart, ()) =>
      cont (ws ++ [.var loWord]) (.var hiPart) (accBits + w - 64)

/-- Pack scalar leaves of `t` into a list of `i64` words (LSB first, 64 bits per word, top word
zero-padded in unused upper bits). -/
def packLeavesToWords64 (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (t : Ty) (leaves : Tup (Arg V) (target.leafTys t))
    (k : List (Arg V i64) → Expr V L rs) : Expr V L rs :=
  go t leaves [] (.imm 0#64) 0 fun ws acc accBits =>
    if accBits == 0 then k ws else k (ws ++ [acc])
where
  go (u : Ty) (xs : Tup (Arg V) (target.leafTys u))
      (ws : List (Arg V i64)) (acc : Arg V i64) (accBits : Nat)
      (cont : List (Arg V i64) → Arg V i64 → Nat → Expr V L rs) : Expr V L rs :=
    match u, xs with
    | .bool, (b, ()) =>
      .let_ (op1 (.ofBool 64) b) fun (w64, ()) => pushLeafWord64 1 (.var w64) ws acc accBits cont
    | .bits n, (x, ()) =>
      let wn := target.widenWidth n
      if n == 0 then cont ws acc accBits
      else if h : wn = 64 then
        pushLeafWord64 (min n 64) (castArgBits h x) ws acc accBits cont
      else if wn < 64 then
        .let_ (op1 (.zext wn 64) x) fun (w64, ()) => pushLeafWord64 n (.var w64) ws acc accBits cont
      else
        .let_ (op1 (.trunc wn 64) x) fun (w64, ()) =>
          pushLeafWord64 (min n 64) (.var w64) ws acc accBits cont
    | .float f, (x, ()) =>
      let fw := f.width
      .let_ (op1 (.bitcast (.float f) (.bits fw) rfl) x) fun (bi, ()) =>
        if h : fw = 64 then
          pushLeafWord64 64 (castArgBits h (.var bi)) ws acc accBits cont
        else if fw < 64 then
          .let_ (op1 (.zext fw 64) (.var bi)) fun (w64, ()) =>
            pushLeafWord64 fw (.var w64) ws acc accBits cont
        else
          .let_ (op1 (.trunc fw 64) (.var bi)) fun (w64, ()) =>
            pushLeafWord64 64 (.var w64) ws acc accBits cont
    | .pair a b, xs =>
      let (fa, fb) := tupSplit xs
      go a fa ws acc accBits fun ws1 acc1 bits1 =>
        go b fb ws1 acc1 bits1 cont

/-- Extract `w ≤ 64` bits at bit offset `off` from `words : List (Arg V i64)` as an `Arg V i64`
(with upper `64 - w` bits zero). -/
def extractBitsFromWords64 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (words : List (Arg V i64)) (off w : Nat)
    (k : Arg V i64 → Expr V L rs) : Expr V L rs :=
  if w == 0 then k (.imm 0#64)
  else
    let idx := off / 64
    let bitOff := off % 64
    let w0 := words.getD idx (.imm 0#64)
    let getShifted (val : Arg V i64) (sh : Nat) (cont : Arg V i64 → Expr V L rs) : Expr V L rs :=
      if sh == 0 then cont val
      else .let_ (op2 (.lshr i64) val (.imm (BitVec.ofNat 64 sh))) fun (r, ()) => cont (.var r)
    getShifted w0 bitOff fun lo =>
      if bitOff + w ≤ 64 then
        emitMaskToN w 64 lo k
      else
        let w1 := words.getD (idx + 1) (.imm 0#64)
        .let_ (op2 (.shl i64) w1 (.imm (BitVec.ofNat 64 (64 - bitOff)))) fun (hi, ()) =>
        .let_ (op2 (.or i64) lo (.var hi)) fun (comb, ()) =>
        emitMaskToN w 64 (.var comb) k

/-- Unpack `Tup (Arg V) (target.leafTys u)` from `words : List (Arg V i64)` starting at bit offset
  `off`. -/
def unpackWords64ToLeaves (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (words : List (Arg V i64)) (off : Nat) :
    (u : Ty) → (Tup (Arg V) (target.leafTys u) → Expr V L rs) → Expr V L rs
  | .bool, k =>
    extractBitsFromWords64 words off 1 fun raw =>
      .let_ (op2 (.ne i64) raw (.imm 0#64)) fun (b, ()) => k (.var b, ())
  | .bits n, k =>
    let wn := target.widenWidth n
    if n == 0 then k (.imm 0#wn, ())
    else
      extractBitsFromWords64 words off (min n 64) fun raw =>
        if h : wn = 64 then k (castArgBits h.symm raw, ())
        else if wn < 64 then .let_ (op1 (.trunc 64 wn) raw) fun (r, ()) => k (.var r, ())
        else .let_ (op1 (.zext 64 wn) raw) fun (r, ()) => k (.var r, ())
  | .float f, k =>
    let fw := f.width
    extractBitsFromWords64 words off (min fw 64) fun raw =>
      if h : fw = 64 then
        have hsz : (Ty.bits 64).size = (Ty.float f).size := by simpa [Ty.size, fw] using h.symm
        .let_ (op1 (.bitcast (.bits 64) (.float f) hsz) raw) fun (r, ()) => k (.var r, ())
      else if fw < 64 then
        .let_ (op1 (.trunc 64 fw) raw) fun (bi, ()) =>
        .let_ (op1 (.bitcast (.bits fw) (.float f) rfl) (.var bi)) fun (r, ()) => k (.var r, ())
      else
        .let_ (op1 (.zext 64 fw) raw) fun (bi, ()) =>
        .let_ (op1 (.bitcast (.bits fw) (.float f) rfl) (.var bi)) fun (r, ()) => k (.var r, ())
  | .pair a b, k =>
    unpackWords64ToLeaves target words off a fun fa =>
      unpackWords64ToLeaves target words (off + a.size) b fun fb =>
        k (tupAppend fa fb)

/-! ## Byte-chunked memory helpers for widened `bits n` and unaligned pairs -/

/-- Largest byte count `c` such that `c ≤ b`, `8 * c ∈ bitWidths`, and `0 < c`. -/
def maxByteChunk (b : Nat) : List Nat → Nat
  | [] => 0
  | w :: ws =>
    let best := maxByteChunk b ws
    if w % 8 == 0 && 0 < w && w / 8 ≤ b && best < w / 8 then w / 8 else best

/-- Decompose `b` bytes into a list of byte-chunk sizes `c` with `8 * c ∈ bitWidths`. -/
def chunkBytes (bitWidths : List Nat) (b : Nat) : List Nat :=
  match b with
  | 0 => []
  | b' + 1 =>
    let c := maxByteChunk (b' + 1) bitWidths
    if _h : 0 < c ∧ c ≤ b' + 1 then
      c :: chunkBytes bitWidths (b' + 1 - c)
    else []
termination_by b

/-- Load `cs` byte chunks starting at `ptr + byteOff`, packing them into `i64` words. -/
def loadByteChunksToWords64 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (ptr : Arg V i64) (byteOff : Nat) :
    List Nat → List (Arg V i64) → Arg V i64 → Nat →
    (List (Arg V i64) → Expr V L rs) → Expr V L rs
  | [], ws, acc, accBits, k =>
    if accBits == 0 then k ws else k (ws ++ [acc])
  | c :: cs, ws, acc, accBits, k =>
    let w := 8 * c
    let emitAddr (cont : Arg V i64 → Expr V L rs) : Expr V L rs :=
      if byteOff == 0 then cont ptr
      else .let_ (op2 (.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, ()) =>
        cont (.var ap)
    emitAddr fun ap =>
      .load (.bits w) ap fun raw =>
        let asWord (cont : Arg V i64 → Expr V L rs) : Expr V L rs :=
          if h : w = 64 then cont (castArgBits h (.var raw))
          else if w < 64 then .let_ (op1 (.zext w 64) (.var raw)) fun (z, ()) => cont (.var z)
          else .let_ (op1 (.trunc w 64) (.var raw)) fun (z, ()) => cont (.var z)
        asWord fun wd =>
          pushLeafWord64 (min w 64) wd ws acc accBits fun ws' acc' bits' =>
            loadByteChunksToWords64 ptr (byteOff + c) cs ws' acc' bits' k

/-- Store `cs` byte chunks from `words : List (Arg V i64)` starting at `ptr + byteOff`. -/
def storeByteChunksFromWords64 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (words : List (Arg V i64)) (ptr : Arg V i64) (byteOff : Nat) :
    List Nat → Expr V L rs → Expr V L rs
  | [], k => k
  | c :: cs, k =>
    let w := 8 * c
    extractBitsFromWords64 words (8 * byteOff) (min w 64) fun raw =>
      let toChunk (cont : Arg V (.bits w) → Expr V L rs) : Expr V L rs :=
        if h : w = 64 then cont (castArgBits h.symm raw)
        else if w < 64 then .let_ (op1 (.trunc 64 w) raw) fun (tr, ()) => cont (.var tr)
        else .let_ (op1 (.zext 64 w) raw) fun (tr, ()) => cont (.var tr)
      let emitAddr (cont : Arg V i64 → Expr V L rs) : Expr V L rs :=
        if byteOff == 0 then cont ptr
        else .let_ (op2 (.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, ()) =>
          cont (.var ap)
      toChunk fun val =>
        emitAddr fun ap =>
          .store (t := .bits w) val ap (storeByteChunksFromWords64 words ptr (byteOff + c) cs k)

/-- Load `n`-bit widened integer as `w := target.widenWidth n` from `ptr` using legal byte chunks.
  -/
def emitLoadBits {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (bitWidths : List Nat) (n w : Nat) (ptr : Arg V i64)
    (k : Arg V (.bits w) → Expr V L rs) : Expr V L rs :=
  let b := (n + 7) / 8
  if b == 0 then k (.imm 0#w)
  else
    go 0 (chunkBytes bitWidths b) none
where
  go (byteOff : Nat) (cs : List Nat) (acc : Option (Arg V (.bits w))) : Expr V L rs :=
    match cs with
    | [] =>
      match acc with
      | none => k (.imm 0#w)
      | some v => emitMaskToN n w v k
    | c :: rest =>
      let cw := 8 * c
      let emitAddr (cont : Arg V i64 → Expr V L rs) : Expr V L rs :=
        if byteOff == 0 then cont ptr
        else .let_ (op2 (.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, ()) =>
          cont (.var ap)
      emitAddr fun ap =>
        .load (.bits cw) ap fun raw =>
          let toW (cont : Arg V (.bits w) → Expr V L rs) : Expr V L rs :=
            if h : cw = w then cont (castArgBits h (.var raw))
            else if cw < w then .let_ (op1 (.zext cw w) (.var raw)) fun (z, ()) => cont (.var z)
            else .let_ (op1 (.trunc cw w) (.var raw)) fun (z, ()) => cont (.var z)
          toW fun vw =>
            let shifted (cont : Arg V (.bits w) → Expr V L rs) : Expr V L rs :=
              if byteOff == 0 then cont vw
              else .let_ (op2 (.shl (.bits w)) vw (.imm (BitVec.ofNat w (8 * byteOff))))
                fun (s, ()) =>
                cont (.var s)
            shifted fun sv =>
              match acc with
              | none => go (byteOff + c) rest (some sv)
              | some prev =>
                .let_ (op2 (.or (.bits w)) prev sv) fun (u, ()) =>
                go (byteOff + c) rest (some (.var u))

/-- Store `n`-bit widened integer (held zero-extended in `v : Arg V (.bits w)`) to `ptr` using
legal byte chunks. -/
def emitStoreBits {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (bitWidths : List Nat) (n w : Nat) (v : Arg V (.bits w)) (ptr : Arg V i64)
    (k : Expr V L rs) : Expr V L rs :=
  let b := (n + 7) / 8
  if b == 0 then k
  else go 0 (chunkBytes bitWidths b)
where
  go (byteOff : Nat) : List Nat → Expr V L rs
    | [] => k
    | c :: rest =>
      let cw := 8 * c
      let shifted (cont : Arg V (.bits w) → Expr V L rs) : Expr V L rs :=
        if byteOff == 0 then cont v
        else .let_ (op2 (.lshr (.bits w)) v (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, ()) =>
          cont (.var s)
      let emitAddr (cont : Arg V i64 → Expr V L rs) : Expr V L rs :=
        if byteOff == 0 then cont ptr
        else .let_ (op2 (.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, ()) =>
          cont (.var ap)
      shifted fun sv =>
        let toCw (cont : Arg V (.bits cw) → Expr V L rs) : Expr V L rs :=
          if h : cw = w then cont (castArgBits h.symm sv)
          else if cw < w then .let_ (op1 (.trunc w cw) sv) fun (tr, ()) => cont (.var tr)
          else .let_ (op1 (.zext w cw) sv) fun (tr, ()) => cont (.var tr)
        toCw fun val =>
          emitAddr fun ap =>
            .store (t := .bits cw) val ap (go (byteOff + c) rest)

/-! ## Scalarization of 128-bit shuffles (`shufd`, `shufb`, `alignr`, `blendw`) and SHA-256 -/

section Simd128Scalar

/-- Split `w0, w1 : Arg V i64` into 4 `i32` lanes `(d0, d1, d2, d3)`. -/
def words2ToDwords4 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (w0 w1 : Arg V i64)
    (k : Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 → Expr V L rs) : Expr V L rs :=
  .let_ (op1 (.trunc 64 32) w0) fun (d0, ()) =>
  .let_ (op2 (.lshr i64) w0 (.imm 32#64)) fun (hi0, ()) =>
  .let_ (op1 (.trunc 64 32) (.var hi0)) fun (d1, ()) =>
  .let_ (op1 (.trunc 64 32) w1) fun (d2, ()) =>
  .let_ (op2 (.lshr i64) w1 (.imm 32#64)) fun (hi1, ()) =>
  .let_ (op1 (.trunc 64 32) (.var hi1)) fun (d3, ()) =>
  k (.var d0) (.var d1) (.var d2) (.var d3)

/-- Pack 4 `i32` lanes into 2 `i64` words. -/
def dwords4ToWords2 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (d0 d1 d2 d3 : Arg V i32)
    (k : Arg V i64 → Arg V i64 → Expr V L rs) : Expr V L rs :=
  .let_ (op1 (.zext 32 64) d0) fun (z0, ()) =>
  .let_ (op1 (.zext 32 64) d1) fun (z1, ()) =>
  .let_ (op2 (.shl i64) (.var z1) (.imm 32#64)) fun (s1, ()) =>
  .let_ (op2 (.or i64) (.var z0) (.var s1)) fun (w0, ()) =>
  .let_ (op1 (.zext 32 64) d2) fun (z2, ()) =>
  .let_ (op1 (.zext 32 64) d3) fun (z3, ()) =>
  .let_ (op2 (.shl i64) (.var z3) (.imm 32#64)) fun (s3, ()) =>
  .let_ (op2 (.or i64) (.var z2) (.var s3)) fun (w1, ()) =>
  k (.var w0) (.var w1)

/-- Extract the 4 bytes of an `i32` lane. -/
def dwordToBytes4 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (d : Arg V i32)
    (k : Arg V i8 → Arg V i8 → Arg V i8 → Arg V i8 → Expr V L rs) : Expr V L rs :=
  .let_ (op1 (.trunc 32 8) d) fun (b0, ()) =>
  .let_ (op2 (.lshr i32) d (.imm 8#32)) fun (s1, ()) =>
  .let_ (op1 (.trunc 32 8) (.var s1)) fun (b1, ()) =>
  .let_ (op2 (.lshr i32) d (.imm 16#32)) fun (s2, ()) =>
  .let_ (op1 (.trunc 32 8) (.var s2)) fun (b2, ()) =>
  .let_ (op2 (.lshr i32) d (.imm 24#32)) fun (s3, ()) =>
  .let_ (op1 (.trunc 32 8) (.var s3)) fun (b3, ()) =>
  k (.var b0) (.var b1) (.var b2) (.var b3)

/-- Pack 4 `i8` bytes into an `i32` lane. -/
def bytes4ToDword {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (b0 b1 b2 b3 : Arg V i8) (k : Arg V i32 → Expr V L rs) : Expr V L rs :=
  .let_ (op1 (.zext 8 32) b0) fun (z0, ()) =>
  .let_ (op1 (.zext 8 32) b1) fun (z1, ()) =>
  .let_ (op2 (.shl i32) (.var z1) (.imm 8#32)) fun (s1, ()) =>
  .let_ (op2 (.or i32) (.var z0) (.var s1)) fun (o1, ()) =>
  .let_ (op1 (.zext 8 32) b2) fun (z2, ()) =>
  .let_ (op2 (.shl i32) (.var z2) (.imm 16#32)) fun (s2, ()) =>
  .let_ (op2 (.or i32) (.var o1) (.var s2)) fun (o2, ()) =>
  .let_ (op1 (.zext 8 32) b3) fun (z3, ()) =>
  .let_ (op2 (.shl i32) (.var z3) (.imm 24#32)) fun (s3, ()) =>
  .let_ (op2 (.or i32) (.var o2) (.var s3)) fun (r, ()) =>
  k (.var r)

/-- Unpack 4 `i32`s into 16 `i8`s. -/
def dwords4ToBytes16 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (d0 d1 d2 d3 : Arg V i32) (k : List (Arg V i8) → Expr V L rs) : Expr V L rs :=
  dwordToBytes4 d0 fun b0 b1 b2 b3 =>
  dwordToBytes4 d1 fun b4 b5 b6 b7 =>
  dwordToBytes4 d2 fun b8 b9 b10 b11 =>
  dwordToBytes4 d3 fun b12 b13 b14 b15 =>
  k [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]

/-- Pack a list of 16 `i8`s (defaulting missing to `0#8`) into 4 `i32`s. -/
def bytes16ToDwords4 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (bs : List (Arg V i8))
    (k : Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 → Expr V L rs) : Expr V L rs :=
  let getB (i : Nat) := bs.getD i (.imm 0#8)
  bytes4ToDword (getB 0) (getB 1) (getB 2) (getB 3) fun d0 =>
  bytes4ToDword (getB 4) (getB 5) (getB 6) (getB 7) fun d1 =>
  bytes4ToDword (getB 8) (getB 9) (getB 10) (getB 11) fun d2 =>
  bytes4ToDword (getB 12) (getB 13) (getB 14) (getB 15) fun d3 =>
  k d0 d1 d2 d3

/-- Scalarized 128-bit `shufd` over 4 `i32`s: zero runtime instructions (pure permutation). -/
def scalarShufd128 {V : Ty → Type} (imm : BitVec 8) (d0 d1 d2 d3 : Arg V i32) :
    Arg V i32 × Arg V i32 × Arg V i32 × Arg V i32 :=
  let pick (i : Nat) : Arg V i32 :=
    match (imm.toNat >>> (2 * i)) % 4 with
    | 0 => d0 | 1 => d1 | 2 => d2 | _ => d3
  (pick 0, pick 1, pick 2, pick 3)

/-- One 32-bit lane step of scalarized 128-bit `blendw` over two `i32`s using static 16-bit masks.
  -/
def scalarBlendwLane {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (imm : BitVec 8) (idx : Nat) (ai bi : Arg V i32)
    (cont : Arg V i32 → Expr V L rs) : Expr V L rs :=
  let loSel := imm.getLsbD (2 * idx)
  let hiSel := imm.getLsbD (2 * idx + 1)
  match loSel, hiSel with
  | false, false => cont ai
  | true, true => cont bi
  | true, false =>
    .let_ (op2 (.and i32) ai (.imm 0xffff0000#32)) fun (am, ()) =>
    .let_ (op2 (.and i32) bi (.imm 0x0000ffff#32)) fun (bm, ()) =>
    .let_ (op2 (.or i32) (.var am) (.var bm)) fun (r, ()) => cont (.var r)
  | false, true =>
    .let_ (op2 (.and i32) ai (.imm 0x0000ffff#32)) fun (am, ()) =>
    .let_ (op2 (.and i32) bi (.imm 0xffff0000#32)) fun (bm, ()) =>
    .let_ (op2 (.or i32) (.var am) (.var bm)) fun (r, ()) => cont (.var r)

/-- Scalarized 128-bit `blendw` over 4 `i32`s using static 16-bit masks. -/
def scalarBlendw128 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (imm : BitVec 8) (a0 a1 a2 a3 b0 b1 b2 b3 : Arg V i32)
    (k : Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 → Expr V L rs) : Expr V L rs :=
  scalarBlendwLane imm 0 a0 b0 fun r0 =>
  scalarBlendwLane imm 1 a1 b1 fun r1 =>
  scalarBlendwLane imm 2 a2 b2 fun r2 =>
  scalarBlendwLane imm 3 a3 b3 fun r3 =>
  k r0 r1 r2 r3

/-- Scalarized 128-bit `alignr` over 4 `i32`s (byte-level select by static `imm`). -/
def scalarAlignr128 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (imm : BitVec 8) (h0 h1 h2 h3 l0 l1 l2 l3 : Arg V i32)
    (k : Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 → Expr V L rs) : Expr V L rs :=
  dwords4ToBytes16 l0 l1 l2 l3 fun lbs =>
  dwords4ToBytes16 h0 h1 h2 h3 fun hbs =>
  let outBs := (List.range 16).map fun i =>
    let j := i + imm.toNat
    if j < 16 then lbs.getD j (.imm 0#8)
    else if j < 32 then hbs.getD (j - 16) (.imm 0#8)
    else .imm 0#8
  bytes16ToDwords4 outBs k

/-- Scalarized 128-bit `shufb` over 4 `i32`s via 16-byte mux. -/
def scalarShufb128 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (a0 a1 a2 a3 m0 m1 m2 m3 : Arg V i32)
    (k : Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 → Expr V L rs) : Expr V L rs :=
  dwords4ToBytes16 a0 a1 a2 a3 fun abs =>
  dwords4ToBytes16 m0 m1 m2 m3 fun mbs =>
  doBytes abs mbs 0 []
where
  muxBytes (idx : Arg V i8) : List (Arg V i8) → Nat → (Arg V i8 → Expr V L rs) → Expr V L rs
    | [], _, cont => cont (.imm 0#8)
    | [b], _, cont => cont b
    | b :: bs, j, cont =>
      muxBytes idx bs (j + 1) fun rest =>
      .let_ (op2 (.eq i8) idx (.imm (BitVec.ofNat 8 j))) fun (eqj, ()) =>
      .let_ (op3 (.select i8) (.var eqj) b rest) fun (r, ()) => cont (.var r)
  doBytes (abs mbs : List (Arg V i8)) (i : Nat) (acc : List (Arg V i8)) : Expr V L rs :=
    if i ≥ 16 then bytes16ToDwords4 acc k
    else
      let mb := mbs.getD i (.imm 0#8)
      .let_ (op2 (.slt i8) mb (.imm 0#8)) fun (neg, ()) =>
      .let_ (op2 (.and i8) mb (.imm 15#8)) fun (idx, ()) =>
      muxBytes (.var idx) abs 0 fun sel =>
      .let_ (op3 (.select i8) (.var neg) (.imm 0#8) sel) fun (res, ()) =>
      doBytes abs mbs (i + 1) (acc ++ [.var res])
  termination_by 16 - i

section Sha256Scalar

def emitRotr32 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (x : Arg V i32) (n : Nat) (k : Arg V i32 → Expr V L rs) : Expr V L rs :=
  .let_ (op2 (.rotr i32) x (.imm (BitVec.ofNat 32 n))) fun (r, ()) => k (.var r)

def emitLshr32 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (x : Arg V i32) (n : Nat) (k : Arg V i32 → Expr V L rs) : Expr V L rs :=
  .let_ (op2 (.lshr i32) x (.imm (BitVec.ofNat 32 n))) fun (r, ()) => k (.var r)

def emitXor32 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (a b : Arg V i32) (k : Arg V i32 → Expr V L rs) : Expr V L rs :=
  .let_ (op2 (.xor i32) a b) fun (r, ()) => k (.var r)

def emitAdd32 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (a b : Arg V i32) (k : Arg V i32 → Expr V L rs) : Expr V L rs :=
  .let_ (op2 (.add i32) a b) fun (r, ()) => k (.var r)

def emitAnd32 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (a b : Arg V i32) (k : Arg V i32 → Expr V L rs) : Expr V L rs :=
  .let_ (op2 (.and i32) a b) fun (r, ()) => k (.var r)

def emitNot32 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (a : Arg V i32) (k : Arg V i32 → Expr V L rs) : Expr V L rs :=
  .let_ (op1 (.not i32) a) fun (r, ()) => k (.var r)

def emitShaMix3 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (thirdLshr : Bool) (n1 n2 n3 : Nat) (x : Arg V i32)
    (k : Arg V i32 → Expr V L rs) : Expr V L rs :=
  emitRotr32 x n1 fun r1 => emitRotr32 x n2 fun r2 =>
  (if thirdLshr then emitLshr32 x n3 else emitRotr32 x n3) fun r3 =>
  emitXor32 r1 r2 fun t => emitXor32 t r3 k

def emitShaSigma0 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (x : Arg V i32) (k : Arg V i32 → Expr V L rs) : Expr V L rs :=
  emitShaMix3 false 2 13 22 x k

def emitShaSigma1 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (x : Arg V i32) (k : Arg V i32 → Expr V L rs) : Expr V L rs :=
  emitShaMix3 false 6 11 25 x k

def emitShaSig0 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (x : Arg V i32) (k : Arg V i32 → Expr V L rs) : Expr V L rs :=
  emitShaMix3 true 7 18 3 x k

def emitShaSig1 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (x : Arg V i32) (k : Arg V i32 → Expr V L rs) : Expr V L rs :=
  emitShaMix3 true 17 19 10 x k

def emitShaCh {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (x y z : Arg V i32) (k : Arg V i32 → Expr V L rs) : Expr V L rs :=
  emitAnd32 x y fun xy => emitNot32 x fun nx => emitAnd32 nx z fun nxz => emitXor32 xy nxz k

def emitShaMaj {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (x y z : Arg V i32) (k : Arg V i32 → Expr V L rs) : Expr V L rs :=
  emitAnd32 x y fun xy => emitAnd32 x z fun xz => emitAnd32 y z fun yz =>
  emitXor32 xy xz fun t => emitXor32 t yz k

def emitShaRound {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (a b c d e f g h wk : Arg V i32)
    (k : Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 →
      Arg V i32 → Expr V L rs) :
    Expr V L rs :=
  emitShaCh e f g fun chv =>
  emitShaSigma1 e fun s1 =>
  emitAdd32 chv s1 fun t1 =>
  emitAdd32 t1 wk fun t2 =>
  emitAdd32 t2 h fun t =>
  emitShaMaj a b c fun majv =>
  emitShaSigma0 a fun s0 =>
  emitAdd32 t majv fun m1 =>
  emitAdd32 m1 s0 fun a' =>
  emitAdd32 t d fun e' =>
  k a' a b c e' e f g

/-- Scalarized `sha256rnds2` over 4-lane `i32` triples. -/
def scalarSha256rnds2 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (cd0 cd1 cd2 cd3 ab0 ab1 ab2 ab3 wk0 wk1 _wk2 _wk3 : Arg V i32)
    (k : Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 → Expr V L rs) : Expr V L rs :=
  emitShaRound ab3 ab2 cd3 cd2 ab1 ab0 cd1 cd0 wk0 fun a1 b1 c1 d1 e1 f1 g1 h1 =>
  emitShaRound a1 b1 c1 d1 e1 f1 g1 h1 wk1 fun a2 _ _ _ e2 _ _ _ =>
  k e1 e2 a1 a2

/-- Scalarized `sha256msg1` over 4-lane `i32` pairs. -/
def scalarSha256msg1 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (a0 a1 a2 a3 b0 _b1 _b2 _b3 : Arg V i32)
    (k : Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 → Expr V L rs) : Expr V L rs :=
  emitShaSig0 a1 fun s0 => emitAdd32 a0 s0 fun r0 =>
  emitShaSig0 a2 fun s1 => emitAdd32 a1 s1 fun r1 =>
  emitShaSig0 a3 fun s2 => emitAdd32 a2 s2 fun r2 =>
  emitShaSig0 b0 fun s3 => emitAdd32 a3 s3 fun r3 =>
  k r0 r1 r2 r3

/-- Scalarized `sha256msg2` over 4-lane `i32` pairs. -/
def scalarSha256msg2 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (s0 s1 s2 s3 _w0 _w1 w2 w3 : Arg V i32)
    (k : Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 → Expr V L rs) : Expr V L rs :=
  emitShaSig1 w2 fun sig2 => emitAdd32 s0 sig2 fun w16 =>
  emitShaSig1 w3 fun sig3 => emitAdd32 s1 sig3 fun w17 =>
  emitShaSig1 w16 fun sig16 => emitAdd32 s2 sig16 fun w18 =>
  emitShaSig1 w17 fun sig17 => emitAdd32 s3 sig17 fun w19 =>
  k w16 w17 w18 w19

end Sha256Scalar

end Simd128Scalar

end Emitters


end LeanQbe.T
