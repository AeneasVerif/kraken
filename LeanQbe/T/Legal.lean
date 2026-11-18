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
* **(c) Vector halving & scalarization**: recursively halves `vec (k + 1) t = .pair (vec k t) (vec k t)`
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
def leafImm {V : Ty → Type} (target : LegalTarget) : (t : Ty) → Val t → Tup (Arg V) (target.leafTys t)
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
    Tup (Arg V) (target.legalTys (.pair a b)) → Tup (Arg V) (target.legalTys a ++ target.legalTys b) :=
  fun xs => cast (by simp [LegalTarget.legalTys, h]) xs

/-- Reinterpret split leaves as `Tup (Arg V) (target.legalTys (.pair a b))` when unpacked. -/
def tupToSplit {target : LegalTarget} {V : Ty → Type} {a b : Ty}
    (h : target.keepsPacked (.pair a b) = false) :
    Tup (Arg V) (target.legalTys a ++ target.legalTys b) → Tup (Arg V) (target.legalTys (.pair a b)) :=
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

/-- Split a flat tuple of target variables `Tup V (target.legalSig ts)` into `Tup (LVar target V) ts`. -/
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

/-- Expand `ternlog (.bits w) imm` into `not`/`and`/`or` on `.bits w`. -/
def emitTernlogBits {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (w : Nat)
    (a b c : Arg V (.bits w)) (imm : BitVec 8)
    (k : Arg V (.bits w) → Expr V L rs) : Expr V L rs :=
  if imm == 0#8 then k (.imm 0#w)
  else if imm == 0xff#8 then k (.imm (BitVec.allOnes w))
  else
    .let_ (op1 (.not (.bits w)) a) fun (na, ()) =>
    .let_ (op1 (.not (.bits w)) b) fun (nb, ()) =>
    .let_ (op1 (.not (.bits w)) c) fun (nc, ()) =>
    go 0 none a b c (.var na) (.var nb) (.var nc)
where
  go (idx : Nat) (acc : Option (Arg V (.bits w)))
      (a b c na nb nc : Arg V (.bits w)) : Expr V L rs :=
    if idx ≥ 8 then
      match acc with
      | some res => k res
      | none => k (.imm 0#w)
    else if imm.getLsbD idx then
      let pa := if idx / 4 % 2 == 1 then a else na
      let pb := if idx / 2 % 2 == 1 then b else nb
      let pc := if idx % 2 == 1 then c else nc
      .let_ (op2 (.and (.bits w)) pa pb) fun (t1, ()) =>
      .let_ (op2 (.and (.bits w)) (.var t1) pc) fun (term, ()) =>
      match acc with
      | none => go (idx + 1) (some (.var term)) a b c na nb nc
      | some prev =>
        .let_ (op2 (.or (.bits w)) prev (.var term)) fun (acc', ()) =>
        go (idx + 1) (some (.var acc')) a b c na nb nc
    else go (idx + 1) acc a b c na nb nc
  termination_by 8 - idx

/-- Expand `ternlog .bool imm` into `not`/`and`/`or` on `.bool`. -/
def emitTernlogBool {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (a b c : Arg V .bool) (imm : BitVec 8)
    (k : Arg V .bool → Expr V L rs) : Expr V L rs :=
  if imm == 0#8 then k (.imm false)
  else if imm == 0xff#8 then k (.imm true)
  else
    .let_ (op1 (.not .bool) a) fun (na, ()) =>
    .let_ (op1 (.not .bool) b) fun (nb, ()) =>
    .let_ (op1 (.not .bool) c) fun (nc, ()) =>
    go 0 none a b c (.var na) (.var nb) (.var nc)
where
  go (idx : Nat) (acc : Option (Arg V .bool))
      (a b c na nb nc : Arg V .bool) : Expr V L rs :=
    if idx ≥ 8 then
      match acc with
      | some res => k res
      | none => k (.imm false)
    else if imm.getLsbD idx then
      let pa := if idx / 4 % 2 == 1 then a else na
      let pb := if idx / 2 % 2 == 1 then b else nb
      let pc := if idx % 2 == 1 then c else nc
      .let_ (op2 (.and .bool) pa pb) fun (t1, ()) =>
      .let_ (op2 (.and .bool) (.var t1) pc) fun (term, ()) =>
      match acc with
      | none => go (idx + 1) (some (.var term)) a b c na nb nc
      | some prev =>
        .let_ (op2 (.or .bool) prev (.var term)) fun (acc', ()) =>
        go (idx + 1) (some (.var acc')) a b c na nb nc
    else go (idx + 1) acc a b c na nb nc
  termination_by 8 - idx

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

/-! ## General 64-bit word stream packing/unpacking (`bitcast`, unaligned `load`/`store`, scalar 128-bit ops) -/

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

/-- Unpack `Tup (Arg V) (target.leafTys u)` from `words : List (Arg V i64)` starting at bit offset `off`. -/
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
      else .let_ (op2 (.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, ()) => cont (.var ap)
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
        else .let_ (op2 (.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, ()) => cont (.var ap)
      toChunk fun val =>
        emitAddr fun ap =>
          .store (t := .bits w) val ap (storeByteChunksFromWords64 words ptr (byteOff + c) cs k)

/-- Load `n`-bit widened integer as `w := target.widenWidth n` from `ptr` using legal byte chunks. -/
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
        else .let_ (op2 (.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, ()) => cont (.var ap)
      emitAddr fun ap =>
        .load (.bits cw) ap fun raw =>
          let toW (cont : Arg V (.bits w) → Expr V L rs) : Expr V L rs :=
            if h : cw = w then cont (castArgBits h (.var raw))
            else if cw < w then .let_ (op1 (.zext cw w) (.var raw)) fun (z, ()) => cont (.var z)
            else .let_ (op1 (.trunc cw w) (.var raw)) fun (z, ()) => cont (.var z)
          toW fun vw =>
            let shifted (cont : Arg V (.bits w) → Expr V L rs) : Expr V L rs :=
              if byteOff == 0 then cont vw
              else .let_ (op2 (.shl (.bits w)) vw (.imm (BitVec.ofNat w (8 * byteOff)))) fun (s, ()) =>
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
        else .let_ (op2 (.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, ()) => cont (.var ap)
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

/-- One 32-bit lane step of scalarized 128-bit `blendw` over two `i32`s using static 16-bit masks. -/
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

def emitShaSigma0 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (x : Arg V i32) (k : Arg V i32 → Expr V L rs) : Expr V L rs :=
  emitRotr32 x 2 fun r2 => emitRotr32 x 13 fun r13 => emitRotr32 x 22 fun r22 =>
  emitXor32 r2 r13 fun t => emitXor32 t r22 k

def emitShaSigma1 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (x : Arg V i32) (k : Arg V i32 → Expr V L rs) : Expr V L rs :=
  emitRotr32 x 6 fun r6 => emitRotr32 x 11 fun r11 => emitRotr32 x 25 fun r25 =>
  emitXor32 r6 r11 fun t => emitXor32 t r25 k

def emitShaSig0 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (x : Arg V i32) (k : Arg V i32 → Expr V L rs) : Expr V L rs :=
  emitRotr32 x 7 fun r7 => emitRotr32 x 18 fun r18 => emitLshr32 x 3 fun s3 =>
  emitXor32 r7 r18 fun t => emitXor32 t s3 k

def emitShaSig1 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (x : Arg V i32) (k : Arg V i32 → Expr V L rs) : Expr V L rs :=
  emitRotr32 x 17 fun r17 => emitRotr32 x 19 fun r19 => emitLshr32 x 10 fun s10 =>
  emitXor32 r17 r19 fun t => emitXor32 t s10 k

def emitShaCh {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (x y z : Arg V i32) (k : Arg V i32 → Expr V L rs) : Expr V L rs :=
  emitAnd32 x y fun xy => emitNot32 x fun nx => emitAnd32 nx z fun nxz => emitXor32 xy nxz k

def emitShaMaj {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (x y z : Arg V i32) (k : Arg V i32 → Expr V L rs) : Expr V L rs :=
  emitAnd32 x y fun xy => emitAnd32 x z fun xz => emitAnd32 y z fun yz =>
  emitXor32 xy xz fun t => emitXor32 t yz k

def emitShaRound {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (a b c d e f g h wk : Arg V i32)
    (k : Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 → Expr V L rs) :
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

/-! ## Generic tree lifters for unary, binary, ternary, comparison, select, and blend ops -/

/-- Legalize any leaf-wise unary op over `t`. -/
def legalUnaryTree (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (mkCode : (u : Ty) → OpCode [u] [u])
    (vecSupported : (u : Ty) → Bool)
    (onBool : Arg V .bool → (Arg V .bool → Expr V L rs) → Expr V L rs)
    (onBits : (n : Nat) → Arg V (.bits (target.widenWidth n)) →
      (Arg V (.bits (target.widenWidth n)) → Expr V L rs) → Expr V L rs)
    (onFloat : (f : Fmt) → Arg V (.float f) →
      (Arg V (.float f) → Expr V L rs) → Expr V L rs) :
    (t : Ty) → Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | .bool, (x, ()), k => onBool x fun r => k (r, ())
  | .bits n, (x, ()), k => onBits n x fun r => k (r, ())
  | .float f, (x, ()), k => onFloat f x fun r => k (r, ())
  | .pair t1 t2, xs, k =>
    if h : target.keepsPacked (.pair t1 t2) then
      let xs' := packedToTup h xs
      if vecSupported (.pair t1 t2) then
        .let_ (op1 (mkCode (.pair t1 t2)) xs'.1) fun (r, ()) =>
          k (tupToPacked h (.var r, ()))
      else
        splitLegalToLeaves target (.pair t1 t2) xs fun fx =>
        let rec goS : (u : Ty) → Tup (Arg V) (target.leafTys u) →
            (Tup (Arg V) (target.leafTys u) → Expr V L rs) → Expr V L rs
          | .bool, (x, ()), cont => onBool x fun r => cont (r, ())
          | .bits n, (x, ()), cont => onBits n x fun r => cont (r, ())
          | .float f, (x, ()), cont => onFloat f x fun r => cont (r, ())
          | .pair u1 u2, fxu, cont =>
            let (fx1, fx2) := tupSplit fxu
            goS u1 fx1 fun r1 => goS u2 fx2 fun r2 => cont (tupAppend r1 r2)
        goS (.pair t1 t2) fx fun fres => packLeavesToLegal target (.pair t1 t2) fres k
    else
      let hf := Bool.eq_false_iff.mpr h
      let (x1, x2) := tupSplit (splitToTup hf xs)
      legalUnaryTree target mkCode vecSupported onBool onBits onFloat t1 x1 fun r1 =>
      legalUnaryTree target mkCode vecSupported onBool onBits onFloat t2 x2 fun r2 =>
      k (tupToSplit hf (tupAppend r1 r2))

/-- Legalize `bswap t` across scalar/pair types (splitting packed vectors since `bswap` is
scalar-only on target). -/
def legalBswapTree (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (t : Ty) → Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | t, xs, k =>
    if !t.bswapOk then .hlt
    else
      legalUnaryTree target .bswap (fun _ => false)
        (fun _ _ => .hlt)
        (fun n x cont =>
          let w := target.widenWidth n
          if n == 0 then cont (.imm 0#w)
          else if n == 8 then cont x
          else if n == w then
            .let_ (op1 (.bswap (.bits w)) x) fun (r, ()) => cont (.var r)
          else if w % 8 == 0 then
            .let_ (op1 (.bswap (.bits w)) x) fun (bw, ()) =>
            .let_ (op2 (.lshr (.bits w)) (.var bw) (.imm (BitVec.ofNat w (w - n)))) fun (r, ()) =>
            cont (.var r)
          else .hlt)
        (fun _ _ _ => .hlt)
        t xs k

/-- Legalize any leaf-wise ternary op (`ternlog`, `ffma`) over `t`. -/
def legalTernaryTree (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (mkCode : (u : Ty) → OpCode [u, u, u] [u])
    (vecSupported : (u : Ty) → Bool)
    (onBool : Arg V .bool → Arg V .bool → Arg V .bool →
      (Arg V .bool → Expr V L rs) → Expr V L rs)
    (onBits : (n : Nat) → Arg V (.bits (target.widenWidth n)) → Arg V (.bits (target.widenWidth n)) →
      Arg V (.bits (target.widenWidth n)) →
      (Arg V (.bits (target.widenWidth n)) → Expr V L rs) → Expr V L rs)
    (onFloat : (f : Fmt) → Arg V (.float f) → Arg V (.float f) → Arg V (.float f) →
      (Arg V (.float f) → Expr V L rs) → Expr V L rs) :
    (t : Ty) → Tup (Arg V) (target.legalTys t) → Tup (Arg V) (target.legalTys t) →
    Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | .bool, (a, ()), (b, ()), (c, ()), k => onBool a b c fun r => k (r, ())
  | .bits n, (a, ()), (b, ()), (c, ()), k => onBits n a b c fun r => k (r, ())
  | .float f, (a, ()), (b, ()), (c, ()), k => onFloat f a b c fun r => k (r, ())
  | .pair t1 t2, xs, ys, zs, k =>
    if h : target.keepsPacked (.pair t1 t2) then
      let xs' := packedToTup h xs
      let ys' := packedToTup h ys
      let zs' := packedToTup h zs
      if vecSupported (.pair t1 t2) then
        .let_ (op3 (mkCode (.pair t1 t2)) xs'.1 ys'.1 zs'.1) fun (r, ()) =>
          k (tupToPacked h (.var r, ()))
      else
        splitLegalToLeaves target (.pair t1 t2) xs fun fx =>
        splitLegalToLeaves target (.pair t1 t2) ys fun fy =>
        splitLegalToLeaves target (.pair t1 t2) zs fun fz =>
        let rec goS : (u : Ty) → Tup (Arg V) (target.leafTys u) →
            Tup (Arg V) (target.leafTys u) → Tup (Arg V) (target.leafTys u) →
            (Tup (Arg V) (target.leafTys u) → Expr V L rs) → Expr V L rs
          | .bool, (a, ()), (b, ()), (c, ()), cont => onBool a b c fun r => cont (r, ())
          | .bits n, (a, ()), (b, ()), (c, ()), cont => onBits n a b c fun r => cont (r, ())
          | .float f, (a, ()), (b, ()), (c, ()), cont => onFloat f a b c fun r => cont (r, ())
          | .pair u1 u2, fxu, fyu, fzu, cont =>
            let (fx1, fx2) := tupSplit fxu
            let (fy1, fy2) := tupSplit fyu
            let (fz1, fz2) := tupSplit fzu
            goS u1 fx1 fy1 fz1 fun r1 => goS u2 fx2 fy2 fz2 fun r2 => cont (tupAppend r1 r2)
        goS (.pair t1 t2) fx fy fz fun fres => packLeavesToLegal target (.pair t1 t2) fres k
    else
      let hf := Bool.eq_false_iff.mpr h
      let (x1, x2) := tupSplit (splitToTup hf xs)
      let (y1, y2) := tupSplit (splitToTup hf ys)
      let (z1, z2) := tupSplit (splitToTup hf zs)
      legalTernaryTree target mkCode vecSupported onBool onBits onFloat t1 x1 y1 z1 fun r1 =>
      legalTernaryTree target mkCode vecSupported onBool onBits onFloat t2 x2 y2 z2 fun r2 =>
      k (tupToSplit hf (tupAppend r1 r2))

/-- Non-dependent tag distinguishing `rotl` (`some true`) and `shl` (`some false`) from all other
opcodes without dependent GADT pattern matching on fixed index lists. -/
@[reducible] def opShiftKind : {as bs : List Ty} → OpCode as bs → Option Bool
  | _, _, .rotl _ => some true
  | _, _, .shl _ => some false
  | _, _, _ => none

/-- Non-dependent tag identifying shift/rotate opcodes (`shl`/`lshr`/`ashr`/`rotl`/`rotr`). -/
@[reducible] def opIsShift : {as bs : List Ty} → OpCode as bs → Bool
  | _, _, .shl _
  | _, _, .lshr _
  | _, _, .ashr _
  | _, _, .rotl _
  | _, _, .rotr _ => true
  | _, _, _ => false

/-- Check whether `rhs` at type `u` is a uniform `.imm` when `code` is a shift/rotate opcode. -/
@[reducible] def checkUniformImmShift {V : Ty → Type} {as bs : List Ty} (u : Ty)
    (code : OpCode as bs) (rhs : Arg V u) : Bool :=
  if opIsShift code then
    match rhs with
    | .imm c => (uniformShiftLeaf? u c).isSome
    | _ => false
  else false

/-- Legalize a leaf-wise binary operation over `t`. -/
def legalBinTree (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (mkCode : (u : Ty) → OpCode [u, u] [u])
    (vecSupported : (u : Ty) → Bool → Bool)
    (onBool : Arg V .bool → Arg V .bool → (Arg V .bool → Expr V L rs) → Expr V L rs)
    (onBits : (n : Nat) → Arg V (.bits (target.widenWidth n)) → Arg V (.bits (target.widenWidth n)) →
      (Arg V (.bits (target.widenWidth n)) → Expr V L rs) → Expr V L rs)
    (onFloat : (f : Fmt) → Arg V (.float f) → Arg V (.float f) →
      (Arg V (.float f) → Expr V L rs) → Expr V L rs)
    (uniformImmRhs : (u : Ty) → Arg (LVar target V) u → Bool) :
    (t : Ty) → Tup (Arg V) (target.legalTys t) → Tup (Arg V) (target.legalTys t) →
    Option (Arg (LVar target V) t) →
    (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | .bool, (a, ()), (b, ()), _, k => onBool a b fun r => k (r, ())
  | .bits n, (a, ()), (b, ()), _, k => onBits n a b fun r => k (r, ())
  | .float f, (a, ()), (b, ()), _, k => onFloat f a b fun r => k (r, ())
  | .pair t1 t2, xs, ys, rawRhs, k =>
    if h : target.keepsPacked (.pair t1 t2) then
      let xs' := packedToTup h xs
      let ys' := packedToTup h ys
      let unif := checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) ys'.1
      if vecSupported (.pair t1 t2) unif then
        .let_ (op2 (mkCode (.pair t1 t2)) xs'.1 ys'.1) fun (r, ()) =>
          k (tupToPacked h (.var r, ()))
      else
        let handledDerived : Option (Expr V L rs) :=
          match opShiftKind (mkCode (.pair t1 t2)), rawRhs with
          | some true, some (.imm c) =>
            match uniformShiftLeaf? (.pair t1 t2) c with
            | some (w, s) =>
              if s == 0 then
                some (k (tupToPacked h xs'))
              else if target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true then
                let rc := splatBits w (BitVec.ofNat w (w - s)) (.pair t1 t2)
                some (.let_ (op2 (.rotr (.pair t1 t2)) xs'.1 (.imm rc)) fun (r, ()) =>
                  k (tupToPacked h (.var r, ())))
              else none
            | none => none
          | some false, some (.imm c) =>
            match uniformShiftLeaf? (.pair t1 t2) c with
            | some (w, s) =>
              if s == 0 then
                some (k (tupToPacked h xs'))
              else if target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true &&
                      target.vecIntOpSupported (.and (.pair t1 t2)) (.pair t1 t2) false then
                let rc := splatBits w (BitVec.ofNat w (w - s)) (.pair t1 t2)
                let mc := splatBits w (BitVec.allOnes w <<< s) (.pair t1 t2)
                some (.let_ (op2 (.rotr (.pair t1 t2)) xs'.1 (.imm rc)) fun (rt, ()) =>
                  .let_ (op2 (.and (.pair t1 t2)) (.var rt) (.imm mc)) fun (r, ()) =>
                    k (tupToPacked h (.var r, ())))
              else none
            | none => none
          | _, _ => none
        match handledDerived with
        | some e => e
        | none =>
          splitLegalToLeaves target (.pair t1 t2) xs fun fx =>
          splitLegalToLeaves target (.pair t1 t2) ys fun fy =>
          let rec goS : (u : Ty) → Tup (Arg V) (target.leafTys u) →
              Tup (Arg V) (target.leafTys u) →
              (Tup (Arg V) (target.leafTys u) → Expr V L rs) → Expr V L rs
            | .bool, (a, ()), (b, ()), cont => onBool a b fun r => cont (r, ())
            | .bits n, (a, ()), (b, ()), cont => onBits n a b fun r => cont (r, ())
            | .float f, (a, ()), (b, ()), cont => onFloat f a b fun r => cont (r, ())
            | .pair u1 u2, fxu, fyu, cont =>
              let (fx1, fx2) := tupSplit fxu
              let (fy1, fy2) := tupSplit fyu
              goS u1 fx1 fy1 fun r1 => goS u2 fx2 fy2 fun r2 => cont (tupAppend r1 r2)
          goS (.pair t1 t2) fx fy fun fres => packLeavesToLegal target (.pair t1 t2) fres k
    else
      let hf := Bool.eq_false_iff.mpr h
      let (x1, x2) := tupSplit (splitToTup hf xs)
      let (y1, y2) := tupSplit (splitToTup hf ys)
      legalBinTree target mkCode vecSupported onBool onBits onFloat uniformImmRhs t1 x1 y1 none fun r1 =>
      legalBinTree target mkCode vecSupported onBool onBits onFloat uniformImmRhs t2 x2 y2 none fun r2 =>
      k (tupToSplit hf (tupAppend r1 r2))

/-- Legalize arithmetic/bitwise/shift at a scalar `.bits n` leaf. -/
def legalBitsArith (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (n : Nat) : OpCode [.bits n, .bits n] [.bits n] →
    Arg V (.bits (target.widenWidth n)) → Arg V (.bits (target.widenWidth n)) →
    (Arg V (.bits (target.widenWidth n)) → Expr V L rs) → Expr V L rs
  | code, a, b, k =>
    let w := target.widenWidth n
    if n == 0 then k (.imm 0#w)
    else
      match code with
      | .add _ => .let_ (op2 (.add (.bits w)) a b) fun (r, ()) => emitMaskToN n w (.var r) k
      | .sub _ => .let_ (op2 (.sub (.bits w)) a b) fun (r, ()) => emitMaskToN n w (.var r) k
      | .mul _ => .let_ (op2 (.mul (.bits w)) a b) fun (r, ()) => emitMaskToN n w (.var r) k
      | .and _ => .let_ (op2 (.and (.bits w)) a b) fun (r, ()) => k (.var r)
      | .or _ => .let_ (op2 (.or (.bits w)) a b) fun (r, ()) => k (.var r)
      | .xor _ => .let_ (op2 (.xor (.bits w)) a b) fun (r, ()) => k (.var r)
      | .shl _ =>
        if n == w then .let_ (op2 (.shl (.bits w)) a b) fun (r, ()) => k (.var r)
        else emitCountMod n w b fun c =>
          .let_ (op2 (.shl (.bits w)) a c) fun (r, ()) => emitMaskToN n w (.var r) k
      | .lshr _ =>
        if n == w then .let_ (op2 (.lshr (.bits w)) a b) fun (r, ()) => k (.var r)
        else emitCountMod n w b fun c =>
          .let_ (op2 (.lshr (.bits w)) a c) fun (r, ()) => k (.var r)
      | .ashr _ =>
        if n == w then .let_ (op2 (.ashr (.bits w)) a b) fun (r, ()) => k (.var r)
        else emitCountMod n w b fun c => emitSextToW n w a fun sa =>
          .let_ (op2 (.ashr (.bits w)) sa c) fun (r, ()) => emitMaskToN n w (.var r) k
      | .rotl _ =>
        if n == w then .let_ (op2 (.rotl (.bits w)) a b) fun (r, ()) => k (.var r)
        else
          emitCountMod n w b fun c =>
          .let_ (op2 (.sub (.bits w)) (.imm (BitVec.ofNat w n)) c) fun (nc, ()) =>
          .let_ (op2 (.shl (.bits w)) a c) fun (lo, ()) =>
          .let_ (op2 (.lshr (.bits w)) a (.var nc)) fun (hi, ()) =>
          .let_ (op2 (.or (.bits w)) (.var lo) (.var hi)) fun (comb, ()) =>
          emitMaskToN n w (.var comb) k
      | .rotr _ =>
        if n == w then .let_ (op2 (.rotr (.bits w)) a b) fun (r, ()) => k (.var r)
        else
          emitCountMod n w b fun c =>
          .let_ (op2 (.sub (.bits w)) (.imm (BitVec.ofNat w n)) c) fun (nc, ()) =>
          .let_ (op2 (.lshr (.bits w)) a c) fun (lo, ()) =>
          .let_ (op2 (.shl (.bits w)) a (.var nc)) fun (hi, ()) =>
          .let_ (op2 (.or (.bits w)) (.var lo) (.var hi)) fun (comb, ()) =>
          emitMaskToN n w (.var comb) k
      | _ => .hlt

/-- Legalize `cmp o t` into scalar comparisons / boolean logic. -/
def legalCmpTree (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (o : CmpOp) : (t : Ty) → Tup (Arg V) (target.legalTys t) → Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t.mask) → Expr V L rs) → Expr V L rs
  | .bool, (a, ()), (b, ()), k =>
    if target.boolCmp then .let_ (op2 (.cmp o .bool) a b) fun (r, ()) => k (.var r, ())
    else emitBoolCmp o a b fun r => k (r, ())
  | .bits n, (a, ()), (b, ()), k =>
    let w := target.widenWidth n
    if n == 0 then k (.imm (o.evalBits 0#0 0#0), ())
    else if n == w then .let_ (op2 (.cmp o (.bits w)) a b) fun (r, ()) => k (.var r, ())
    else
      let isSigned := match o with | .slt | .sle | .sgt | .sge => true | _ => false
      if isSigned then
        emitSextToW n w a fun sa => emitSextToW n w b fun sb =>
          .let_ (op2 (.cmp o (.bits w)) sa sb) fun (r, ()) => k (.var r, ())
      else .let_ (op2 (.cmp o (.bits w)) a b) fun (r, ()) => k (.var r, ())
  | .float _, _, _, _ => .hlt
  | .pair t1 t2, xs, ys, k =>
    splitLegalToLeaves target (.pair t1 t2) xs fun fx =>
    splitLegalToLeaves target (.pair t1 t2) ys fun fy =>
    let rec goMask : (u : Ty) → Tup (Arg V) (target.leafTys u) →
        Tup (Arg V) (target.leafTys u) →
        (Tup (Arg V) (target.leafTys u.mask) → Expr V L rs) → Expr V L rs
      | .bool, (a, ()), (b, ()), cont =>
        if target.boolCmp then .let_ (op2 (.cmp o .bool) a b) fun (r, ()) => cont (.var r, ())
        else emitBoolCmp o a b fun r => cont (r, ())
      | .bits n, (a, ()), (b, ()), cont =>
        let w := target.widenWidth n
        if n == 0 then cont (.imm (o.evalBits 0#0 0#0), ())
        else if n == w then .let_ (op2 (.cmp o (.bits w)) a b) fun (r, ()) => cont (.var r, ())
        else
          let isSigned := match o with | .slt | .sle | .sgt | .sge => true | _ => false
          if isSigned then
            emitSextToW n w a fun sa => emitSextToW n w b fun sb =>
              .let_ (op2 (.cmp o (.bits w)) sa sb) fun (r, ()) => cont (.var r, ())
          else .let_ (op2 (.cmp o (.bits w)) a b) fun (r, ()) => cont (.var r, ())
      | .float _, _, _, _ => .hlt
      | .pair u1 u2, fxu, fyu, cont =>
        let (fx1, fx2) := tupSplit fxu
        let (fy1, fy2) := tupSplit fyu
        goMask u1 fx1 fy1 fun m1 => goMask u2 fx2 fy2 fun m2 => cont (tupAppend m1 m2)
    goMask (.pair t1 t2) fx fy fun mres => packLeavesToLegal target (Ty.mask (.pair t1 t2)) mres k

/-- Legalize `select` over `t`. -/
def legalSelectTree (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (c : Arg V .bool) : (t : Ty) →
    Tup (Arg V) (target.legalTys t) → Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | .bool, (a, ()), (b, ()), k =>
    if target.boolSelect then .let_ (op3 (.select .bool) c a b) fun (r, ()) => k (.var r, ())
    else emitBoolSelect c a b fun r => k (r, ())
  | .bits n, (a, ()), (b, ()), k =>
    .let_ (op3 (.select (.bits (target.widenWidth n))) c a b) fun (r, ()) => k (.var r, ())
  | .float f, (a, ()), (b, ()), k =>
    .let_ (op3 (.select (.float f)) c a b) fun (r, ()) => k (.var r, ())
  | .pair t1 t2, xs, ys, k =>
    splitLegalToLeaves target (.pair t1 t2) xs fun fx =>
    splitLegalToLeaves target (.pair t1 t2) ys fun fy =>
    let rec goSel : (u : Ty) → Tup (Arg V) (target.leafTys u) →
        Tup (Arg V) (target.leafTys u) →
        (Tup (Arg V) (target.leafTys u) → Expr V L rs) → Expr V L rs
      | .bool, (a, ()), (b, ()), cont =>
        if target.boolSelect then .let_ (op3 (.select .bool) c a b) fun (r, ()) => cont (.var r, ())
        else emitBoolSelect c a b fun r => cont (r, ())
      | .bits n, (a, ()), (b, ()), cont =>
        .let_ (op3 (.select (.bits (target.widenWidth n))) c a b) fun (r, ()) => cont (.var r, ())
      | .float f, (a, ()), (b, ()), cont =>
        .let_ (op3 (.select (.float f)) c a b) fun (r, ()) => cont (.var r, ())
      | .pair u1 u2, fxu, fyu, cont =>
        let (fx1, fx2) := tupSplit fxu
        let (fy1, fy2) := tupSplit fyu
        goSel u1 fx1 fy1 fun r1 => goSel u2 fx2 fy2 fun r2 => cont (tupAppend r1 r2)
    goSel (.pair t1 t2) fx fy fun fres => packLeavesToLegal target (.pair t1 t2) fres k

/-- Legalize `blend t` into scalar `select`s on `bool` leaves. -/
def legalBlendTree (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (t : Ty) → Tup (Arg V) (target.legalTys t.mask) →
    Tup (Arg V) (target.legalTys t) → Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | .bool, (c, ()), (a, ()), (b, ()), k =>
    if target.boolSelect then .let_ (op3 (.select .bool) c a b) fun (r, ()) => k (.var r, ())
    else emitBoolSelect c a b fun r => k (r, ())
  | .bits n, (c, ()), (a, ()), (b, ()), k =>
    .let_ (op3 (.select (.bits (target.widenWidth n))) c a b) fun (r, ()) => k (.var r, ())
  | .float f, (c, ()), (a, ()), (b, ()), k =>
    .let_ (op3 (.select (.float f)) c a b) fun (r, ()) => k (.var r, ())
  | .pair t1 t2, ms, xs, ys, k =>
    splitLegalToLeaves target (Ty.mask (.pair t1 t2)) ms fun fm =>
    splitLegalToLeaves target (.pair t1 t2) xs fun fx =>
    splitLegalToLeaves target (.pair t1 t2) ys fun fy =>
    let rec goBlend : (u : Ty) → Tup (Arg V) (target.leafTys u.mask) →
        Tup (Arg V) (target.leafTys u) → Tup (Arg V) (target.leafTys u) →
        (Tup (Arg V) (target.leafTys u) → Expr V L rs) → Expr V L rs
      | .bool, (c, ()), (a, ()), (b, ()), cont =>
        if target.boolSelect then .let_ (op3 (.select .bool) c a b) fun (r, ()) => cont (.var r, ())
        else emitBoolSelect c a b fun r => cont (r, ())
      | .bits n, (c, ()), (a, ()), (b, ()), cont =>
        .let_ (op3 (.select (.bits (target.widenWidth n))) c a b) fun (r, ()) => cont (.var r, ())
      | .float f, (c, ()), (a, ()), (b, ()), cont =>
        .let_ (op3 (.select (.float f)) c a b) fun (r, ()) => cont (.var r, ())
      | .pair u1 u2, fmu, fxu, fyu, cont =>
        let (fm1, fm2) := tupSplit fmu
        let (fx1, fx2) := tupSplit fxu
        let (fy1, fy2) := tupSplit fyu
        goBlend u1 fm1 fx1 fy1 fun r1 => goBlend u2 fm2 fx2 fy2 fun r2 => cont (tupAppend r1 r2)
    goBlend (.pair t1 t2) fm fx fy fun fres => packLeavesToLegal target (.pair t1 t2) fres k

/-- Legalize `fcmp o t`. -/
def legalFCmpTree (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (o : FCmpOp) : (t : Ty) → Tup (Arg V) (target.legalTys t) → Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t.mask) → Expr V L rs) → Expr V L rs
  | .bool, _, _, _ => .hlt
  | .bits _, _, _, _ => .hlt
  | .float f, (a, ()), (b, ()), k => .let_ (op2 (.fcmp o (.float f)) a b) fun (r, ()) => k (.var r, ())
  | .pair t1 t2, xs, ys, k =>
    splitLegalToLeaves target (.pair t1 t2) xs fun fx =>
    splitLegalToLeaves target (.pair t1 t2) ys fun fy =>
    let rec goFCmp : (u : Ty) → Tup (Arg V) (target.leafTys u) →
        Tup (Arg V) (target.leafTys u) →
        (Tup (Arg V) (target.leafTys u.mask) → Expr V L rs) → Expr V L rs
      | .float f, (a, ()), (b, ()), cont =>
        .let_ (op2 (.fcmp o (.float f)) a b) fun (r, ()) => cont (.var r, ())
      | .pair u1 u2, fxu, fyu, cont =>
        let (fx1, fx2) := tupSplit fxu
        let (fy1, fy2) := tupSplit fyu
        goFCmp u1 fx1 fy1 fun m1 => goFCmp u2 fx2 fy2 fun m2 => cont (tupAppend m1 m2)
      | _, _, _, _ => .hlt
    goFCmp (.pair t1 t2) fx fy fun mres => packLeavesToLegal target (Ty.mask (.pair t1 t2)) mres k

/-- Scalarized 128-bit-lane fallback over word streams for shuffles across arbitrary `t`
with `t.size ≠ 0 ∧ t.size % 128 = 0`. -/
def legalSimdScalar128 (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (on128 : Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 →
             Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 →
      (Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 → Expr V L rs) → Expr V L rs)
    (t : Ty) (xs ys : Tup (Arg V) (target.legalTys t))
    (k : Tup (Arg V) (target.legalTys t) → Expr V L rs) : Expr V L rs :=
  splitLegalToLeaves target t xs fun fx =>
  splitLegalToLeaves target t ys fun fy =>
  packLeavesToWords64 target t fx fun wx =>
  packLeavesToWords64 target t fy fun wy =>
  let rec goWords : List (Arg V i64) → List (Arg V i64) → List (Arg V i64) → Expr V L rs
    | x0 :: x1 :: rxs, y0 :: y1 :: rys, acc =>
      words2ToDwords4 x0 x1 fun a0 a1 a2 a3 =>
      words2ToDwords4 y0 y1 fun b0 b1 b2 b3 =>
      on128 a0 a1 a2 a3 b0 b1 b2 b3 fun r0 r1 r2 r3 =>
      dwords4ToWords2 r0 r1 r2 r3 fun w0 w1 =>
      goWords rxs rys (acc ++ [w0, w1])
    | _, _, acc =>
      unpackWords64ToLeaves target acc 0 t fun fres =>
        packLeavesToLegal target t fres k
  goWords wx wy []

/-- Legalize `shufd t imm`. -/
def legalShufd (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (imm : BitVec 8) : (t : Ty) → Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | t, xs, k =>
    if t.size == 0 || t.size % 128 != 0 then .hlt
    else
      let on128 := fun a0 a1 a2 a3 _ _ _ _ cont =>
        let (r0, r1, r2, r3) := scalarShufd128 imm a0 a1 a2 a3
        cont r0 r1 r2 r3
      match t with
      | .pair a b =>
        if h : target.keepsPacked (.pair a b) then
          let xs' := packedToTup h xs
          if target.vecIntOpSupported (.shufd (.pair a b) imm) (.pair a b) false then
            .let_ (op1 (.shufd (.pair a b) imm) xs'.1) fun (r, ()) => k (tupToPacked h (.var r, ()))
          else legalSimdScalar128 target on128 (.pair a b) xs xs k
        else if a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0 then
          let hf := Bool.eq_false_iff.mpr h
          let (xa, xb) := tupSplit (splitToTup hf xs)
          legalShufd target imm a xa fun ra =>
          legalShufd target imm b xb fun rb =>
          k (tupToSplit hf (tupAppend ra rb))
        else legalSimdScalar128 target on128 (.pair a b) xs xs k
      | t' => legalSimdScalar128 target on128 t' xs xs k

/-- Legalize `blendw t imm`. -/
def legalBlendw (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (imm : BitVec 8) : (t : Ty) → Tup (Arg V) (target.legalTys t) → Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | t, xs, ys, k =>
    if t.size == 0 || t.size % 128 != 0 then .hlt
    else
      match t with
      | .pair a b =>
        if h : target.keepsPacked (.pair a b) then
          let xs' := packedToTup h xs
          let ys' := packedToTup h ys
          if target.vecIntOpSupported (.blendw (.pair a b) imm) (.pair a b) false then
            .let_ (op2 (.blendw (.pair a b) imm) xs'.1 ys'.1) fun (r, ()) =>
              k (tupToPacked h (.var r, ()))
          else legalSimdScalar128 target (scalarBlendw128 imm) (.pair a b) xs ys k
        else if a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0 then
          let hf := Bool.eq_false_iff.mpr h
          let (xa, xb) := tupSplit (splitToTup hf xs)
          let (ya, yb) := tupSplit (splitToTup hf ys)
          legalBlendw target imm a xa ya fun ra =>
          legalBlendw target imm b xb yb fun rb =>
          k (tupToSplit hf (tupAppend ra rb))
        else legalSimdScalar128 target (scalarBlendw128 imm) (.pair a b) xs ys k
      | t' => legalSimdScalar128 target (scalarBlendw128 imm) t' xs ys k

/-- Legalize `alignr t imm`. -/
def legalAlignr (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (imm : BitVec 8) : (t : Ty) → Tup (Arg V) (target.legalTys t) → Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | t, xs, ys, k =>
    if t.size == 0 || t.size % 128 != 0 then .hlt
    else
      match t with
      | .pair a b =>
        if h : target.keepsPacked (.pair a b) then
          let xs' := packedToTup h xs
          let ys' := packedToTup h ys
          if target.vecIntOpSupported (.alignr (.pair a b) imm) (.pair a b) false then
            .let_ (op2 (.alignr (.pair a b) imm) xs'.1 ys'.1) fun (r, ()) =>
              k (tupToPacked h (.var r, ()))
          else legalSimdScalar128 target (scalarAlignr128 imm) (.pair a b) xs ys k
        else if a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0 then
          let hf := Bool.eq_false_iff.mpr h
          let (xa, xb) := tupSplit (splitToTup hf xs)
          let (ya, yb) := tupSplit (splitToTup hf ys)
          legalAlignr target imm a xa ya fun ra =>
          legalAlignr target imm b xb yb fun rb =>
          k (tupToSplit hf (tupAppend ra rb))
        else legalSimdScalar128 target (scalarAlignr128 imm) (.pair a b) xs ys k
      | t' => legalSimdScalar128 target (scalarAlignr128 imm) t' xs ys k

/-- Legalize `shufb t`. -/
def legalShufb (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (t : Ty) → Tup (Arg V) (target.legalTys t) → Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | t, xs, ys, k =>
    if t.size == 0 || t.size % 128 != 0 then .hlt
    else
      match t with
      | .pair a b =>
        if h : target.keepsPacked (.pair a b) then
          let xs' := packedToTup h xs
          let ys' := packedToTup h ys
          if target.vecIntOpSupported (.shufb (.pair a b)) (.pair a b) false then
            .let_ (op2 (.shufb (.pair a b)) xs'.1 ys'.1) fun (r, ()) =>
              k (tupToPacked h (.var r, ()))
          else legalSimdScalar128 target scalarShufb128 (.pair a b) xs ys k
        else if a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0 then
          let hf := Bool.eq_false_iff.mpr h
          let (xa, xb) := tupSplit (splitToTup hf xs)
          let (ya, yb) := tupSplit (splitToTup hf ys)
          legalShufb target a xa ya fun ra =>
          legalShufb target b xb yb fun rb =>
          k (tupToSplit hf (tupAppend ra rb))
        else legalSimdScalar128 target scalarShufb128 (.pair a b) xs ys k
      | t' => legalSimdScalar128 target scalarShufb128 t' xs ys k

/-- Helper: legalize scalar float bitwise op (`and`/`or`/`xor`/`not`/`ternlog`). -/
def legalFloatBit2 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (target : LegalTarget) (mkOp : (w : Nat) → OpCode [.bits w, .bits w] [.bits w])
    (mkFOp : (f : Fmt) → OpCode [.float f, .float f] [.float f])
    (f : Fmt) (x y : Arg V (.float f)) (cont : Arg V (.float f) → Expr V L rs) : Expr V L rs :=
  if target.scalarFloatBitwise then
    .let_ (op2 (mkFOp f) x y) fun (r, ()) => cont (.var r)
  else
    let fw := f.width
    .let_ (op1 (.bitcast (.float f) (.bits fw) rfl) x) fun (bx, ()) =>
    .let_ (op1 (.bitcast (.float f) (.bits fw) rfl) y) fun (by_, ()) =>
    .let_ (op2 (mkOp fw) (.var bx) (.var by_)) fun (br, ()) =>
    .let_ (op1 (.bitcast (.bits fw) (.float f) rfl) (.var br)) fun (r, ()) => cont (.var r)

/-- Legalize a single `Op (LVar target V) rs'` into a continuation receiving `Tup (LVar target V) rs'`. -/
def legalOp (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {outRs : List Ty}
    {rs' : List Ty} (op : Op (LVar target V) rs')
    (k : Tup (LVar target V) rs' → Expr V L outRs) : Expr V L outRs :=
  let ⟨code, args⟩ := op
  match code with
  | .copy _ =>
    let (a, ()) := args
    k (legalArg target a, ())
  | .add t =>
    let (a, b, ()) := args
    if t.hasFloat then .hlt
    else
      legalBinTree target .add (fun u unif => target.vecIntOpSupported (.add u) u unif)
        (fun x y cont => .let_ (op2 (.xor .bool) x y) fun (r, ()) => cont (.var r))
        (fun n x y cont => legalBitsArith target n (.add (.bits n)) x y cont)
        (fun _ _ _ _ => .hlt) (fun _ _ => false)
        t (legalArg target a) (legalArg target b) none fun r => k (r, ())
  | .sub t =>
    let (a, b, ()) := args
    if t.hasFloat then .hlt
    else
      legalBinTree target .sub (fun u unif => target.vecIntOpSupported (.sub u) u unif)
        (fun x y cont => .let_ (op2 (.xor .bool) x y) fun (r, ()) => cont (.var r))
        (fun n x y cont => legalBitsArith target n (.sub (.bits n)) x y cont)
        (fun _ _ _ _ => .hlt) (fun _ _ => false)
        t (legalArg target a) (legalArg target b) none fun r => k (r, ())
  | .mul t =>
    let (a, b, ()) := args
    if t.hasFloat then .hlt
    else
      legalBinTree target .mul (fun u unif => target.vecIntOpSupported (.mul u) u unif)
        (fun x y cont => .let_ (op2 (.and .bool) x y) fun (r, ()) => cont (.var r))
        (fun n x y cont => legalBitsArith target n (.mul (.bits n)) x y cont)
        (fun _ _ _ _ => .hlt) (fun _ _ => false)
        t (legalArg target a) (legalArg target b) none fun r => k (r, ())
  | .neg t =>
    let (a, ()) := args
    if t.hasFloat then .hlt
    else
      legalUnaryTree target .neg (fun u => target.vecIntOpSupported (.neg u) u false)
        (fun x cont => cont x)
        (fun n x cont =>
          let w := target.widenWidth n
          if n == 0 then cont (.imm 0#w)
          else .let_ (op1 (.neg (.bits w)) x) fun (r, ()) => emitMaskToN n w (.var r) cont)
        (fun _ _ _ => .hlt)
        t (legalArg target a) fun r => k (r, ())
  | .and t =>
    let (a, b, ()) := args
    legalBinTree target .and (fun u unif => target.vecIntOpSupported (.and u) u unif)
      (fun x y cont => .let_ (op2 (.and .bool) x y) fun (r, ()) => cont (.var r))
      (fun n x y cont => legalBitsArith target n (.and (.bits n)) x y cont)
      (legalFloatBit2 target (fun w => .and (.bits w)) (fun f => .and (.float f)))
      (fun _ _ => false)
      t (legalArg target a) (legalArg target b) none fun r => k (r, ())
  | .or t =>
    let (a, b, ()) := args
    legalBinTree target .or (fun u unif => target.vecIntOpSupported (.or u) u unif)
      (fun x y cont => .let_ (op2 (.or .bool) x y) fun (r, ()) => cont (.var r))
      (fun n x y cont => legalBitsArith target n (.or (.bits n)) x y cont)
      (legalFloatBit2 target (fun w => .or (.bits w)) (fun f => .or (.float f)))
      (fun _ _ => false)
      t (legalArg target a) (legalArg target b) none fun r => k (r, ())
  | .xor t =>
    let (a, b, ()) := args
    legalBinTree target .xor (fun u unif => target.vecIntOpSupported (.xor u) u unif)
      (fun x y cont => .let_ (op2 (.xor .bool) x y) fun (r, ()) => cont (.var r))
      (fun n x y cont => legalBitsArith target n (.xor (.bits n)) x y cont)
      (legalFloatBit2 target (fun w => .xor (.bits w)) (fun f => .xor (.float f)))
      (fun _ _ => false)
      t (legalArg target a) (legalArg target b) none fun r => k (r, ())
  | .not t =>
    let (a, ()) := args
    legalUnaryTree target .not (fun u => target.vecIntOpSupported (.not u) u false)
      (fun x cont => .let_ (op1 (.not .bool) x) fun (r, ()) => cont (.var r))
      (fun n x cont =>
        let w := target.widenWidth n
        if n == 0 then cont (.imm 0#w)
        else if n == w then .let_ (op1 (.not (.bits w)) x) fun (r, ()) => cont (.var r)
        else .let_ (op1 (.not (.bits w)) x) fun (r, ()) => emitMaskToN n w (.var r) cont)
      (fun f x cont =>
        if target.scalarFloatBitwise then .let_ (op1 (.not (.float f)) x) fun (r, ()) => cont (.var r)
        else
          let fw := f.width
          .let_ (op1 (.bitcast (.float f) (.bits fw) rfl) x) fun (bx, ()) =>
          .let_ (op1 (.not (.bits fw)) (.var bx)) fun (br, ()) =>
          .let_ (op1 (.bitcast (.bits fw) (.float f) rfl) (.var br)) fun (r, ()) => cont (.var r))
      t (legalArg target a) fun r => k (r, ())
  | .ternlog t imm =>
    let (a, b, c, ()) := args
    legalTernaryTree target (fun u => .ternlog u imm)
      (fun u => target.vecIntOpSupported (.ternlog u imm) u false)
      (fun x y z cont => emitTernlogBool x y z imm cont)
      (fun n x y z cont =>
        let w := target.widenWidth n
        if n == 0 then cont (.imm 0#w)
        else if target.scalarTernlog then
          .let_ (op3 (.ternlog (.bits w) imm) x y z) fun (r, ()) => emitMaskToN n w (.var r) cont
        else emitTernlogBits w x y z imm fun r => emitMaskToN n w r cont)
      (fun f x y z cont =>
        if target.scalarFloatBitwise && target.scalarTernlog then
          .let_ (op3 (.ternlog (.float f) imm) x y z) fun (r, ()) => cont (.var r)
        else
          let fw := f.width
          .let_ (op1 (.bitcast (.float f) (.bits fw) rfl) x) fun (bx, ()) =>
          .let_ (op1 (.bitcast (.float f) (.bits fw) rfl) y) fun (by_, ()) =>
          .let_ (op1 (.bitcast (.float f) (.bits fw) rfl) z) fun (bz, ()) =>
          (if target.scalarTernlog then
             fun cc => .let_ (op3 (.ternlog (.bits fw) imm) (.var bx) (.var by_) (.var bz)) fun (br, ()) => cc (.var br)
           else emitTernlogBits fw (.var bx) (.var by_) (.var bz) imm) fun br =>
          .let_ (op1 (.bitcast (.bits fw) (.float f) rfl) br) fun (r, ()) => cont (.var r))
      t (legalArg target a) (legalArg target b) (legalArg target c) fun r => k (r, ())
  | .shl t =>
    let (a, b, ()) := args
    if t.hasFloat then .hlt
    else
      legalBinTree target .shl (fun u unif => target.vecIntOpSupported (.shl u) u unif)
        (fun x _ cont => cont x)
        (fun n x y cont => legalBitsArith target n (.shl (.bits n)) x y cont)
        (fun _ _ _ _ => .hlt)
        (fun u rhs => match rhs with | .imm c => (uniformShiftLeaf? u c).isSome | _ => false)
        t (legalArg target a) (legalArg target b) (some b) fun r => k (r, ())
  | .lshr t =>
    let (a, b, ()) := args
    if t.hasFloat then .hlt
    else
      legalBinTree target .lshr (fun u unif => target.vecIntOpSupported (.lshr u) u unif)
        (fun x _ cont => cont x)
        (fun n x y cont => legalBitsArith target n (.lshr (.bits n)) x y cont)
        (fun _ _ _ _ => .hlt)
        (fun u rhs => match rhs with | .imm c => (uniformShiftLeaf? u c).isSome | _ => false)
        t (legalArg target a) (legalArg target b) (some b) fun r => k (r, ())
  | .ashr t =>
    let (a, b, ()) := args
    if t.hasFloat then .hlt
    else
      legalBinTree target .ashr (fun u unif => target.vecIntOpSupported (.ashr u) u unif)
        (fun x _ cont => cont x)
        (fun n x y cont => legalBitsArith target n (.ashr (.bits n)) x y cont)
        (fun _ _ _ _ => .hlt)
        (fun u rhs => match rhs with | .imm c => (uniformShiftLeaf? u c).isSome | _ => false)
        t (legalArg target a) (legalArg target b) (some b) fun r => k (r, ())
  | .rotl t =>
    let (a, b, ()) := args
    if t.hasFloat then .hlt
    else
      legalBinTree target .rotl (fun u unif => target.vecIntOpSupported (.rotl u) u unif)
        (fun x _ cont => cont x)
        (fun n x y cont => legalBitsArith target n (.rotl (.bits n)) x y cont)
        (fun _ _ _ _ => .hlt)
        (fun u rhs => match rhs with | .imm c => (uniformShiftLeaf? u c).isSome | _ => false)
        t (legalArg target a) (legalArg target b) (some b) fun r => k (r, ())
  | .rotr t =>
    let (a, b, ()) := args
    if t.hasFloat then .hlt
    else
      legalBinTree target .rotr (fun u unif => target.vecIntOpSupported (.rotr u) u unif)
        (fun x _ cont => cont x)
        (fun n x y cont => legalBitsArith target n (.rotr (.bits n)) x y cont)
        (fun _ _ _ _ => .hlt)
        (fun u rhs => match rhs with | .imm c => (uniformShiftLeaf? u c).isSome | _ => false)
        t (legalArg target a) (legalArg target b) (some b) fun r => k (r, ())
  | .fshl n =>
    let (a, b, c, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let (c', ()) := legalArg target c
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), ())
    else if n == w then
      .let_ (op3 (.fshl w) a' b' c') fun (r, ()) => k ((.var r, ()), ())
    else
      emitCountMod n w c' fun cm =>
      .let_ (op2 (.sub (.bits w)) (.imm (BitVec.ofNat w n)) cm) fun (nc, ()) =>
      .let_ (op2 (.shl (.bits w)) a' cm) fun (lo, ()) =>
      .let_ (op2 (.lshr (.bits w)) b' (.var nc)) fun (hi, ()) =>
      .let_ (op2 (.or (.bits w)) (.var lo) (.var hi)) fun (comb, ()) =>
      emitMaskToN n w (.var comb) fun r => k ((r, ()), ())
  | .fshr n =>
    let (a, b, c, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let (c', ()) := legalArg target c
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), ())
    else if n == w then
      .let_ (op3 (.fshr w) a' b' c') fun (r, ()) => k ((.var r, ()), ())
    else
      emitCountMod n w c' fun cm =>
      .let_ (op2 (.sub (.bits w)) (.imm (BitVec.ofNat w n)) cm) fun (nc, ()) =>
      .let_ (op2 (.lshr (.bits w)) b' cm) fun (lo, ()) =>
      .let_ (op2 (.shl (.bits w)) a' (.var nc)) fun (hi, ()) =>
      .let_ (op2 (.or (.bits w)) (.var lo) (.var hi)) fun (comb, ()) =>
      emitMaskToN n w (.var comb) fun r => k ((r, ()), ())
  | .bswap t =>
    let (a, ()) := args
    legalBswapTree target t (legalArg target a) fun r => k (r, ())
  | .clz n =>
    let (a, ()) := args
    let (a', ()) := legalArg target a
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), ())
    else if n == w then
      .let_ (op1 (.clz w) a') fun (r, ()) => k ((.var r, ()), ())
    else
      .let_ (op1 (.clz w) a') fun (cw, ()) =>
      .let_ (op2 (.sub (.bits w)) (.var cw) (.imm (BitVec.ofNat w (w - n)))) fun (r, ()) =>
      k ((.var r, ()), ())
  | .cls n =>
    let (a, ()) := args
    let (a', ()) := legalArg target a
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), ())
    else if n == w then
      .let_ (op1 (.cls w) a') fun (r, ()) => k ((.var r, ()), ())
    else
      emitSextToW n w a' fun sa =>
      .let_ (op1 (.cls w) sa) fun (cw, ()) =>
      .let_ (op2 (.sub (.bits w)) (.var cw) (.imm (BitVec.ofNat w (w - n)))) fun (r, ()) =>
      k ((.var r, ()), ())
  | .rbit n =>
    let (a, ()) := args
    let (a', ()) := legalArg target a
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), ())
    else if n == w then
      .let_ (op1 (.rbit w) a') fun (r, ()) => k ((.var r, ()), ())
    else
      .let_ (op1 (.rbit w) a') fun (rw, ()) =>
      .let_ (op2 (.lshr (.bits w)) (.var rw) (.imm (BitVec.ofNat w (w - n)))) fun (r, ()) =>
      k ((.var r, ()), ())
  | .ctz n =>
    let (a, ()) := args
    let (a', ()) := legalArg target a
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), ())
    else if n == w then
      .let_ (op1 (.ctz w) a') fun (r, ()) => k ((.var r, ()), ())
    else
      .let_ (op2 (.or (.bits w)) a' (.imm (BitVec.ofNat w (2 ^ n)))) fun (ao, ()) =>
      .let_ (op1 (.ctz w) (.var ao)) fun (r, ()) =>
      k ((.var r, ()), ())
  | .popcnt n =>
    let (a, ()) := args
    let (a', ()) := legalArg target a
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), ())
    else .let_ (op1 (.popcnt w) a') fun (r, ()) => k ((.var r, ()), ())
  | .cmp o t m h =>
    let (a, b, ()) := args
    if t.hasFloat then .hlt
    else
      legalCmpTree target o t (legalArg target a) (legalArg target b) fun r =>
        k (by subst h; exact (r, ()))
  | .select t =>
    let (c, a, b, ()) := args
    let (c', ()) := legalArg target c
    legalSelectTree target c' t (legalArg target a) (legalArg target b) fun r => k (r, ())
  | .blend t m h =>
    let (c, a, b, ()) := args
    let c' : Tup (Arg V) (target.legalTys t.mask) := by subst h; exact legalArg target c
    legalBlendTree target t c' (legalArg target a) (legalArg target b) fun r => k (r, ())
  | .zext m n =>
    let (a, ()) := args
    if m > n then .hlt
    else
      let (a', ()) := legalArg target a
      let wm := target.widenWidth m
      let wn := target.widenWidth n
      if m == 0 then k ((.imm 0#wn, ()), ())
      else if h : wm = wn then k ((castArgBits h a', ()), ())
      else if wm < wn then .let_ (op1 (.zext wm wn) a') fun (r, ()) => k ((.var r, ()), ())
      else .hlt
  | .sext m n =>
    let (a, ()) := args
    if m > n then .hlt
    else
      let (a', ()) := legalArg target a
      let wm := target.widenWidth m
      let wn := target.widenWidth n
      if m == 0 then k ((.imm 0#wn, ()), ())
      else
        emitSextToW m wm a' fun sx =>
        let step2 (cont : Arg V (.bits wn) → Expr V L outRs) : Expr V L outRs :=
          if h : wm = wn then cont (castArgBits h sx)
          else if wm < wn then .let_ (op1 (.sext wm wn) sx) fun (r, ()) => cont (.var r)
          else .hlt
        step2 fun r => emitMaskToN n wn r fun rm => k ((rm, ()), ())
  | .trunc m n =>
    let (a, ()) := args
    if n > m then .hlt
    else
      let (a', ()) := legalArg target a
      let wm := target.widenWidth m
      let wn := target.widenWidth n
      if n == 0 then k ((.imm 0#wn, ()), ())
      else
        let step1 (cont : Arg V (.bits wn) → Expr V L outRs) : Expr V L outRs :=
          if h : wn = wm then cont (castArgBits h.symm a')
          else if wn < wm then .let_ (op1 (.trunc wm wn) a') fun (r, ()) => cont (.var r)
          else .hlt
        step1 fun r => emitMaskToN n wn r fun rm => k ((rm, ()), ())
  | .ofBool n =>
    let (c, ()) := args
    let (c', ()) := legalArg target c
    let wn := target.widenWidth n
    if n == 0 then k ((.imm 0#wn, ()), ())
    else .let_ (op1 (.ofBool wn) c') fun (r, ()) => k ((.var r, ()), ())
  | .addc n =>
    let (a, b, c, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let (c', ()) := legalArg target c
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), (c', ()), ())
    else if n == w then
      .let_ (op3 (.addc w) a' b' c') fun (s, co, ()) => k ((.var s, ()), (.var co, ()), ())
    else
      .let_ (op1 (.ofBool w) c') fun (cw, ()) =>
      .let_ (op2 (.add (.bits w)) a' b') fun (ab, ()) =>
      .let_ (op2 (.add (.bits w)) (.var ab) (.var cw)) fun (sw, ()) =>
      emitMaskToN n w (.var sw) fun s =>
      .let_ (op2 (.ule (.bits w)) (.imm ((1#w) <<< n)) (.var sw)) fun (co, ()) =>
      k ((s, ()), (.var co, ()), ())
  | .subb n =>
    let (a, b, c, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let (c', ()) := legalArg target c
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), (c', ()), ())
    else if n == w then
      .let_ (op3 (.subb w) a' b' c') fun (d, bo, ()) => k ((.var d, ()), (.var bo, ()), ())
    else
      .let_ (op3 (.subb w) a' b' c') fun (dw, bo, ()) =>
      emitMaskToN n w (.var dw) fun d =>
      k ((d, ()), (.var bo, ()), ())
  | .umulw n =>
    let (a, b, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), (.imm 0#w, ()), ())
    else if n == w then
      .let_ (op2 (.umulw w) a' b') fun (lo, hi, ()) => k ((.var lo, ()), (.var hi, ()), ())
    else
      .let_ (op2 (.umulw w) a' b') fun (loW, hiW, ()) =>
      emitMaskToN n w (.var loW) fun lo =>
      .let_ (op2 (.lshr (.bits w)) (.var loW) (.imm (BitVec.ofNat w n))) fun (p1, ()) =>
      .let_ (op2 (.shl (.bits w)) (.var hiW) (.imm (BitVec.ofNat w (w - n)))) fun (p2, ()) =>
      .let_ (op2 (.or (.bits w)) (.var p1) (.var p2)) fun (hiComb, ()) =>
      emitMaskToN n w (.var hiComb) fun hi =>
      k ((lo, ()), (hi, ()), ())
  | .smulw n =>
    let (a, b, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), (.imm 0#w, ()), ())
    else if n == w then
      .let_ (op2 (.smulw w) a' b') fun (lo, hi, ()) => k ((.var lo, ()), (.var hi, ()), ())
    else
      emitSextToW n w a' fun sa =>
      emitSextToW n w b' fun sb =>
      .let_ (op2 (.smulw w) sa sb) fun (loW, hiW, ()) =>
      emitMaskToN n w (.var loW) fun lo =>
      .let_ (op2 (.lshr (.bits w)) (.var loW) (.imm (BitVec.ofNat w n))) fun (p1, ()) =>
      .let_ (op2 (.shl (.bits w)) (.var hiW) (.imm (BitVec.ofNat w (w - n)))) fun (p2, ()) =>
      .let_ (op2 (.or (.bits w)) (.var p1) (.var p2)) fun (hiComb, ()) =>
      emitMaskToN n w (.var hiComb) fun hi =>
      k ((lo, ()), (hi, ()), ())
  | .udiv n =>
    let (a, b, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let w := target.widenWidth n
    if n == 0 then .hlt
    else .let_ (op2 (.udiv w) a' b') fun (r, ()) => k ((.var r, ()), ())
  | .sdiv n =>
    let (a, b, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let w := target.widenWidth n
    if n == 0 then .hlt
    else if n == w then .let_ (op2 (.sdiv w) a' b') fun (r, ()) => k ((.var r, ()), ())
    else
      emitSextToW n w a' fun sa =>
      emitSextToW n w b' fun sb =>
      .let_ (op2 (.sdiv w) sa sb) fun (r, ()) =>
      emitMaskToN n w (.var r) fun rm => k ((rm, ()), ())
  | .urem n =>
    let (a, b, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let w := target.widenWidth n
    if n == 0 then .hlt
    else .let_ (op2 (.urem w) a' b') fun (r, ()) => k ((.var r, ()), ())
  | .srem n =>
    let (a, b, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let w := target.widenWidth n
    if n == 0 then .hlt
    else if n == w then .let_ (op2 (.srem w) a' b') fun (r, ()) => k ((.var r, ()), ())
    else
      emitSextToW n w a' fun sa =>
      emitSextToW n w b' fun sb =>
      .let_ (op2 (.srem w) sa sb) fun (r, ()) =>
      emitMaskToN n w (.var r) fun rm => k ((rm, ()), ())
  | .udiv0 n =>
    let (a, b, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), ())
    else .let_ (op2 (.udiv0 w) a' b') fun (r, ()) => k ((.var r, ()), ())
  | .sdiv0 n =>
    let (a, b, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), ())
    else if n == w then .let_ (op2 (.sdiv0 w) a' b') fun (r, ()) => k ((.var r, ()), ())
    else
      emitSextToW n w a' fun sa =>
      emitSextToW n w b' fun sb =>
      .let_ (op2 (.sdiv0 w) sa sb) fun (r, ()) =>
      emitMaskToN n w (.var r) fun rm => k ((rm, ()), ())
  | .mkpair a b =>
    let (va, vb, ()) := args
    let la := legalArg target va
    let lb := legalArg target vb
    if h : target.keepsPacked (.pair a b) then
      packFromLegal target a la fun pa =>
      packFromLegal target b lb fun pb =>
      .let_ (op2 (.mkpair a b) pa pb) fun (p, ()) =>
        k (tupToPacked h (.var p, ()), ())
    else
      let hf := Bool.eq_false_iff.mpr h
      k (tupToSplit hf (tupAppend la lb), ())
  | .unpair a b =>
    let (vp, ()) := args
    let lp := legalArg target vp
    if h : target.keepsPacked (.pair a b) then
      match (packedToTup h lp).1 with
      | .imm c => k (encodeImm target a c.1, encodeImm target b c.2, ())
      | .var v =>
        .let_ (op1 (.unpair a b) (.var v)) fun (va, vb, ()) =>
        unpackToLegal target a (.var va) fun la =>
        unpackToLegal target b (.var vb) fun lb =>
          k (la, lb, ())
    else
      let hf := Bool.eq_false_iff.mpr h
      let (la, lb) := tupSplit (splitToTup hf lp)
      k (la, lb, ())
  | .bitcast t u h =>
    let (a, ()) := args
    let la := legalArg target a
    if heq : t = u then
      k (heq ▸ la, ())
    else
      let isNativeTy (x : Ty) : Bool :=
        target.isLegalTy x && match x with | .bits n => target.widenWidth n == n | _ => true
      if ht : isNativeTy t then
        if hu : isNativeTy u then
          have hlt : target.legalTys t = [t] := by
            cases t with
            | bool => rfl
            | bits n =>
              have hw : target.widenWidth n = n := by
                simpa [isNativeTy] using ((Bool.and_eq_true _ _).mp ht).2
              simp [LegalTarget.legalTys, hw]
            | float _ => rfl
            | pair _ _ => simp [isNativeTy, LegalTarget.isLegalTy] at ht; simp [LegalTarget.legalTys, ht]
          have hlu : target.legalTys u = [u] := by
            cases u with
            | bool => rfl
            | bits n =>
              have hw : target.widenWidth n = n := by
                simpa [isNativeTy] using ((Bool.and_eq_true _ _).mp hu).2
              simp [LegalTarget.legalTys, hw]
            | float _ => rfl
            | pair _ _ => simp [isNativeTy, LegalTarget.isLegalTy] at hu; simp [LegalTarget.legalTys, hu]
          let x' : Arg V t := (cast (by rw [hlt]) la : Tup (Arg V) [t]).1
          .let_ (op1 (.bitcast t u h) x') fun (r, ()) =>
            k (cast (by simp [LVar, hlu]) (show Tup (Arg V) [u] from (.var r, ())), ())
        else
          splitLegalToLeaves target t la fun fx =>
          packLeavesToWords64 target t fx fun words =>
          unpackWords64ToLeaves target words 0 u fun fu =>
          packLeavesToLegal target u fu fun res => k (res, ())
      else
        splitLegalToLeaves target t la fun fx =>
        packLeavesToWords64 target t fx fun words =>
        unpackWords64ToLeaves target words 0 u fun fu =>
        packLeavesToLegal target u fu fun res => k (res, ())
  | .shufd t imm =>
    let (a, ()) := args
    legalShufd target imm t (legalArg target a) fun r => k (r, ())
  | .shufb t =>
    let (a, m, ()) := args
    legalShufb target t (legalArg target a) (legalArg target m) fun r => k (r, ())
  | .alignr t imm =>
    let (hi, lo, ()) := args
    legalAlignr target imm t (legalArg target hi) (legalArg target lo) fun r => k (r, ())
  | .blendw t imm =>
    let (a, b, ()) := args
    legalBlendw target imm t (legalArg target a) (legalArg target b) fun r => k (r, ())
  | .sha256rnds2 =>
    let (cdgh, abef, wk, ()) := args
    if hk : target.keepsPacked v4i32 then
      if target.vecIntOpSupported .sha256rnds2 v4i32 false then
        have hl : target.legalTys v4i32 = [v4i32] := by simp [LegalTarget.legalTys, hk]
        let c' : Arg V v4i32 := (cast (by rw [hl]) (legalArg target cdgh) : Tup (Arg V) [v4i32]).1
        let a' : Arg V v4i32 := (cast (by rw [hl]) (legalArg target abef) : Tup (Arg V) [v4i32]).1
        let w' : Arg V v4i32 := (cast (by rw [hl]) (legalArg target wk) : Tup (Arg V) [v4i32]).1
        .let_ (op3 .sha256rnds2 c' a' w') fun (r, ()) =>
          k (cast (by simp [LVar, hl]) (show Tup (Arg V) [v4i32] from (.var r, ())), ())
      else
        splitLegalToLeaves target v4i32 (legalArg target cdgh) fun fc =>
        splitLegalToLeaves target v4i32 (legalArg target abef) fun fa =>
        splitLegalToLeaves target v4i32 (legalArg target wk) fun fw =>
        packLeavesToWords64 target v4i32 fc fun wc =>
        packLeavesToWords64 target v4i32 fa fun wa =>
        packLeavesToWords64 target v4i32 fw fun ww =>
        words2ToDwords4 (wc.getD 0 (.imm 0#64)) (wc.getD 1 (.imm 0#64)) fun cd0 cd1 cd2 cd3 =>
        words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun ab0 ab1 ab2 ab3 =>
        words2ToDwords4 (ww.getD 0 (.imm 0#64)) (ww.getD 1 (.imm 0#64)) fun wk0 wk1 wk2 wk3 =>
        scalarSha256rnds2 cd0 cd1 cd2 cd3 ab0 ab1 ab2 ab3 wk0 wk1 wk2 wk3 fun r0 r1 r2 r3 =>
        dwords4ToWords2 r0 r1 r2 r3 fun w0 w1 =>
        unpackWords64ToLeaves target [w0, w1] 0 v4i32 fun fres =>
        packLeavesToLegal target v4i32 fres fun res => k (res, ())
    else
      splitLegalToLeaves target v4i32 (legalArg target cdgh) fun fc =>
      splitLegalToLeaves target v4i32 (legalArg target abef) fun fa =>
      splitLegalToLeaves target v4i32 (legalArg target wk) fun fw =>
      packLeavesToWords64 target v4i32 fc fun wc =>
      packLeavesToWords64 target v4i32 fa fun wa =>
      packLeavesToWords64 target v4i32 fw fun ww =>
      words2ToDwords4 (wc.getD 0 (.imm 0#64)) (wc.getD 1 (.imm 0#64)) fun cd0 cd1 cd2 cd3 =>
      words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun ab0 ab1 ab2 ab3 =>
      words2ToDwords4 (ww.getD 0 (.imm 0#64)) (ww.getD 1 (.imm 0#64)) fun wk0 wk1 wk2 wk3 =>
      scalarSha256rnds2 cd0 cd1 cd2 cd3 ab0 ab1 ab2 ab3 wk0 wk1 wk2 wk3 fun r0 r1 r2 r3 =>
      dwords4ToWords2 r0 r1 r2 r3 fun w0 w1 =>
      unpackWords64ToLeaves target [w0, w1] 0 v4i32 fun fres =>
      packLeavesToLegal target v4i32 fres fun res => k (res, ())
  | .sha256msg1 =>
    let (w0123, w4, ()) := args
    if hk : target.keepsPacked v4i32 && target.vecIntOpSupported .sha256msg1 v4i32 false then
      have hkp : target.keepsPacked v4i32 = true := (Bool.and_eq_true _ _).mp hk |>.1
      have hl : target.legalTys v4i32 = [v4i32] := by simp [LegalTarget.legalTys, hkp]
      let a' : Arg V v4i32 := (cast (by rw [hl]) (legalArg target w0123) : Tup (Arg V) [v4i32]).1
      let b' : Arg V v4i32 := (cast (by rw [hl]) (legalArg target w4) : Tup (Arg V) [v4i32]).1
      .let_ (op2 .sha256msg1 a' b') fun (r, ()) =>
        k (cast (by simp [LVar, hl]) (show Tup (Arg V) [v4i32] from (.var r, ())), ())
    else
      splitLegalToLeaves target v4i32 (legalArg target w0123) fun fa =>
      splitLegalToLeaves target v4i32 (legalArg target w4) fun fb =>
      packLeavesToWords64 target v4i32 fa fun wa =>
      packLeavesToWords64 target v4i32 fb fun wb =>
      words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun a0 a1 a2 a3 =>
      words2ToDwords4 (wb.getD 0 (.imm 0#64)) (wb.getD 1 (.imm 0#64)) fun b0 b1 b2 b3 =>
      scalarSha256msg1 a0 a1 a2 a3 b0 b1 b2 b3 fun r0 r1 r2 r3 =>
      dwords4ToWords2 r0 r1 r2 r3 fun w0 w1 =>
      unpackWords64ToLeaves target [w0, w1] 0 v4i32 fun fres =>
      packLeavesToLegal target v4i32 fres fun res => k (res, ())
  | .sha256msg2 =>
    let (sums, w, ()) := args
    if hk : target.keepsPacked v4i32 then
      if target.vecIntOpSupported .sha256msg2 v4i32 false then
        have hl : target.legalTys v4i32 = [v4i32] := by simp [LegalTarget.legalTys, hk]
        let a' : Arg V v4i32 := (cast (by rw [hl]) (legalArg target sums) : Tup (Arg V) [v4i32]).1
        let b' : Arg V v4i32 := (cast (by rw [hl]) (legalArg target w) : Tup (Arg V) [v4i32]).1
        .let_ (op2 .sha256msg2 a' b') fun (r, ()) =>
          k (cast (by simp [LVar, hl]) (show Tup (Arg V) [v4i32] from (.var r, ())), ())
      else
        splitLegalToLeaves target v4i32 (legalArg target sums) fun fa =>
        splitLegalToLeaves target v4i32 (legalArg target w) fun fb =>
        packLeavesToWords64 target v4i32 fa fun wa =>
        packLeavesToWords64 target v4i32 fb fun wb =>
        words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun s0 s1 s2 s3 =>
        words2ToDwords4 (wb.getD 0 (.imm 0#64)) (wb.getD 1 (.imm 0#64)) fun w0 w1 w2 w3 =>
        scalarSha256msg2 s0 s1 s2 s3 w0 w1 w2 w3 fun r0 r1 r2 r3 =>
        dwords4ToWords2 r0 r1 r2 r3 fun wr0 wr1 =>
        unpackWords64ToLeaves target [wr0, wr1] 0 v4i32 fun fres =>
        packLeavesToLegal target v4i32 fres fun res => k (res, ())
    else
      splitLegalToLeaves target v4i32 (legalArg target sums) fun fa =>
      splitLegalToLeaves target v4i32 (legalArg target w) fun fb =>
      packLeavesToWords64 target v4i32 fa fun wa =>
      packLeavesToWords64 target v4i32 fb fun wb =>
      words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun s0 s1 s2 s3 =>
      words2ToDwords4 (wb.getD 0 (.imm 0#64)) (wb.getD 1 (.imm 0#64)) fun w0 w1 w2 w3 =>
      scalarSha256msg2 s0 s1 s2 s3 w0 w1 w2 w3 fun r0 r1 r2 r3 =>
      dwords4ToWords2 r0 r1 r2 r3 fun wr0 wr1 =>
      unpackWords64ToLeaves target [wr0, wr1] 0 v4i32 fun fres =>
      packLeavesToLegal target v4i32 fres fun res => k (res, ())
  | .fadd t =>
    let (a, b, ()) := args
    if !t.isFloatTree then .hlt
    else
      legalBinTree target .fadd (fun u _ => target.vecFloatOpSupported (.fadd u) u)
        (fun _ _ _ => .hlt) (fun _ _ _ _ => .hlt)
        (fun f x y cont => .let_ (op2 (.fadd (.float f)) x y) fun (r, ()) => cont (.var r))
        (fun _ _ => false)
        t (legalArg target a) (legalArg target b) none fun r => k (r, ())
  | .fsub t =>
    let (a, b, ()) := args
    if !t.isFloatTree then .hlt
    else
      legalBinTree target .fsub (fun u _ => target.vecFloatOpSupported (.fsub u) u)
        (fun _ _ _ => .hlt) (fun _ _ _ _ => .hlt)
        (fun f x y cont => .let_ (op2 (.fsub (.float f)) x y) fun (r, ()) => cont (.var r))
        (fun _ _ => false)
        t (legalArg target a) (legalArg target b) none fun r => k (r, ())
  | .fmul t =>
    let (a, b, ()) := args
    if !t.isFloatTree then .hlt
    else
      legalBinTree target .fmul (fun u _ => target.vecFloatOpSupported (.fmul u) u)
        (fun _ _ _ => .hlt) (fun _ _ _ _ => .hlt)
        (fun f x y cont => .let_ (op2 (.fmul (.float f)) x y) fun (r, ()) => cont (.var r))
        (fun _ _ => false)
        t (legalArg target a) (legalArg target b) none fun r => k (r, ())
  | .fdiv t =>
    let (a, b, ()) := args
    if !t.isFloatTree then .hlt
    else
      legalBinTree target .fdiv (fun u _ => target.vecFloatOpSupported (.fdiv u) u)
        (fun _ _ _ => .hlt) (fun _ _ _ _ => .hlt)
        (fun f x y cont => .let_ (op2 (.fdiv (.float f)) x y) fun (r, ()) => cont (.var r))
        (fun _ _ => false)
        t (legalArg target a) (legalArg target b) none fun r => k (r, ())
  | .ffma t =>
    let (a, b, c, ()) := args
    if !t.isFloatTree then .hlt
    else
      legalTernaryTree target .ffma (fun u => target.vecFloatOpSupported (.ffma u) u)
        (fun _ _ _ _ => .hlt) (fun _ _ _ _ _ => .hlt)
        (fun f x y z cont => .let_ (op3 (.ffma (.float f)) x y z) fun (r, ()) => cont (.var r))
        t (legalArg target a) (legalArg target b) (legalArg target c) fun r => k (r, ())
  | .fsqrt t =>
    let (a, ()) := args
    if !t.isFloatTree then .hlt
    else
      legalUnaryTree target .fsqrt (fun u => target.vecFloatOpSupported (.fsqrt u) u)
        (fun _ _ => .hlt) (fun _ _ _ => .hlt)
        (fun f x cont => .let_ (op1 (.fsqrt (.float f)) x) fun (r, ()) => cont (.var r))
        t (legalArg target a) fun r => k (r, ())
  | .fneg t =>
    let (a, ()) := args
    if !t.isFloatTree then .hlt
    else
      legalUnaryTree target .fneg (fun u => target.vecFloatOpSupported (.fneg u) u)
        (fun _ _ => .hlt) (fun _ _ _ => .hlt)
        (fun f x cont => .let_ (op1 (.fneg (.float f)) x) fun (r, ()) => cont (.var r))
        t (legalArg target a) fun r => k (r, ())
  | .fabs t =>
    let (a, ()) := args
    if !t.isFloatTree then .hlt
    else
      legalUnaryTree target .fabs (fun u => target.vecFloatOpSupported (.fabs u) u)
        (fun _ _ => .hlt) (fun _ _ _ => .hlt)
        (fun f x cont => .let_ (op1 (.fabs (.float f)) x) fun (r, ()) => cont (.var r))
        t (legalArg target a) fun r => k (r, ())
  | .fcmp o t m h =>
    let (a, b, ()) := args
    if !t.isFloatTree then .hlt
    else
      legalFCmpTree target o t (legalArg target a) (legalArg target b) fun r =>
        k (by subst h; exact (r, ()))
  | .fptoui f n =>
    let (a, ()) := args
    let (a', ()) := legalArg target a
    let w := target.widenWidth n
    if n == 0 then
      .let_ (op1 (.fptoui f w) a') fun (_, ()) => k ((.imm 0#w, ()), ())
    else
      .let_ (op1 (.fptoui f w) a') fun (r, ()) => k ((.var r, ()), ())
  | .fptosi f n =>
    let (a, ()) := args
    let (a', ()) := legalArg target a
    let w := target.widenWidth n
    if n == 0 then .hlt
    else if n == w then
      .let_ (op1 (.fptosi f w) a') fun (r, ()) => k ((.var r, ()), ())
    else
      .let_ (op1 (.fptosi f w) a') fun (r, ()) =>
      emitMaskToN n w (.var r) fun rm => k ((rm, ()), ())
  | .uitofp n f =>
    let (a, ()) := args
    let (a', ()) := legalArg target a
    let w := target.widenWidth n
    if n == 0 then
      .let_ (op1 (.uitofp w f) (.imm 0#w)) fun (r, ()) => k ((.var r, ()), ())
    else
      .let_ (op1 (.uitofp w f) a') fun (r, ()) => k ((.var r, ()), ())
  | .sitofp n f =>
    let (a, ()) := args
    let (a', ()) := legalArg target a
    let w := target.widenWidth n
    if n == 0 then
      .let_ (op1 (.sitofp w f) (.imm 0#w)) fun (r, ()) => k ((.var r, ()), ())
    else
      emitSextToW n w a' fun sa =>
      .let_ (op1 (.sitofp w f) sa) fun (r, ()) => k ((.var r, ()), ())
  | .fcvt f g =>
    let (a, ()) := args
    let (a', ()) := legalArg target a
    .let_ (op1 (.fcvt f g) a') fun (r, ()) => k ((.var r, ()), ())

/-- Legalize `load t ptr k`. -/
def legalLoad (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (t : Ty) (ptr : Arg V i64) (k : LVar target V t → Expr V L rs) : Expr V L rs :=
  match t with
  | .bool => .load .bool ptr fun v => k (.var v, ())
  | .bits n =>
    let w := target.widenWidth n
    if n == w then .load (.bits w) ptr fun v => k (.var v, ())
    else emitLoadBits target.bitWidths n w ptr fun r => k (r, ())
  | .float f => .load (.float f) ptr fun v => k (.var v, ())
  | .pair a b =>
    if h : target.keepsPacked (.pair a b) then
      .load (.pair a b) ptr fun v =>
        k (tupToPacked h (.var v, ()))
    else if (Ty.pair a b).isByteAlignedStruct then
      let hf := Bool.eq_false_iff.mpr h
      legalLoad target a ptr fun la =>
      (if a.bytes == 0 then fun cont => cont ptr
       else fun cont => .let_ (op2 (.add i64) ptr (.imm (BitVec.ofNat 64 a.bytes))) fun (p2, ()) =>
         cont (.var p2)) fun ptr2 =>
        legalLoad target b ptr2 fun lb =>
          k (tupToSplit hf (tupAppend la lb))
    else
      let bCount := (Ty.pair a b).bytes
      if bCount == 0 then
        unpackWords64ToLeaves target [] 0 (.pair a b) fun fres =>
          packLeavesToLegal target (.pair a b) fres k
      else
        loadByteChunksToWords64 ptr 0 (chunkBytes target.bitWidths bCount) [] (.imm 0#64) 0 fun words =>
          unpackWords64ToLeaves target words 0 (.pair a b) fun fres =>
            packLeavesToLegal target (.pair a b) fres k

/-- Legalize `store t v ptr k`. -/
def legalStore (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (t : Ty) → LVar target V t → Arg V i64 → Expr V L rs → Expr V L rs
  | .bool, (v, ()), ptr, k => .store (t := .bool) v ptr k
  | .bits n, (v, ()), ptr, k =>
    let w := target.widenWidth n
    if n == w then .store (t := .bits w) v ptr k
    else emitStoreBits target.bitWidths n w v ptr k
  | .float f, (v, ()), ptr, k => .store (t := .float f) v ptr k
  | .pair a b, xs, ptr, k =>
    if h : target.keepsPacked (.pair a b) then
      let xs' := packedToTup h xs
      .store (t := .pair a b) xs'.1 ptr k
    else if (Ty.pair a b).isByteAlignedStruct then
      let hf := Bool.eq_false_iff.mpr h
      let (la, lb) := tupSplit (splitToTup hf xs)
      legalStore target a la ptr <|
        if a.bytes == 0 then legalStore target b lb ptr k
        else .let_ (op2 (.add i64) ptr (.imm (BitVec.ofNat 64 a.bytes))) fun (p2, ()) =>
          legalStore target b lb (.var p2) k
    else
      let bCount := (Ty.pair a b).bytes
      if bCount == 0 then k
      else
        splitLegalToLeaves target (.pair a b) xs fun fx =>
        packLeavesToWords64 target (.pair a b) fx fun words =>
          storeByteChunksFromWords64 words ptr 0 (chunkBytes target.bitWidths bCount) k

mutual
/-- Legalize an expression `Expr (LVar target V) (LLab target L) rs` into `Expr V L (target.legalSig rs)`. -/
def legalExpr (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Expr (LVar target V) (LLab target L) rs → Expr V L (target.legalSig rs)
  | .let_ op k => legalOp target op fun res => legalExpr target (k res)
  | .load t a k =>
    if h64 : target.widenWidth 64 = 64 then
      legalLoad target t (castArgBits h64 (legalArg target a).1) fun res => legalExpr target (k res)
    else .hlt
  | .store (t := t) v a k =>
    if h64 : target.widenWidth 64 = 64 then
      legalStore target t (legalArg target v) (castArgBits h64 (legalArg target a).1) (legalExpr target k)
    else .hlt
  | .call f (as := as) (bs := bs) args k =>
    .call f (as := target.legalSig as) (bs := target.legalSig bs) (joinArgs target args) fun res =>
      legalExpr target (k (splitParams target bs res))
  | .jnz c t e => .jnz (legalArg target c).1 (legalExpr target t) (legalExpr target e)
  | .jump j args => .jump j (joinArgs target args)
  | .ret vs => .ret (joinArgs target vs)
  | .exit f (as := as) args => .exit f (as := target.legalSig as) (joinArgs target args)
  | .hlt => .hlt
  | .group (sig := sig) bodies k =>
    .group (sig := sig.map target.legalSig)
      (fun Js => legalBlocks target (bodies (tupLiftMap target.legalSig L Js)))
      (fun Js => legalExpr target (k (tupLiftMap target.legalSig L Js)))

/-- Legalize a block list `Blocks`. -/
def legalBlocks (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (LVar target V) (LLab target L) rs sig →
    Blocks V L (target.legalSig rs) (sig.map target.legalSig)
  | _, .nil => .nil
  | _, .cons (ts := ts) b bs =>
    .cons (fun xs => legalExpr target (b (splitParams target ts xs))) (legalBlocks target bs)
end

/-- Legalize a closed typed function `Func as rs` for `target`. -/
def Func.legal (target : LegalTarget) {as rs : List Ty} (f : Func as rs) :
    Func (target.legalSig as) (target.legalSig rs) :=
  fun V L xs => legalExpr target (f (LVar target V) (LLab target L) (splitParams target as xs))

/-- Legalize a named typed function `Fn`. -/
def Fn.legal (target : LegalTarget) (fn : Fn) : Fn :=
  ⟨fn.name, target.legalSig fn.as, target.legalSig fn.rs, Func.legal target fn.body⟩

/-! ## Decidable `Legal` predicate and `supportsSource` check -/

/-- Variable kind tracked during `TFlat.isLegal`: normal legal values vs transient pack/unpack
bridges immediately around packed vector boundaries. -/
inductive VarKind
  | normal
  | unpackedBridge
  | packedBridge
  deriving DecidableEq, Repr

/-- Check variable index `idx` in `Γ` at expected type `t` and allowed kind predicate. -/
def checkVarKind (Γ : List (Ty × VarKind)) (t : Ty) (allowed : VarKind → Bool) (idx : Nat) : Bool :=
  match listGet? Γ idx with
  | some (t', k) =>
    (match tyDecEq t' t with | isTrue _ => true | isFalse _ => false) && allowed k
  | none => false

/-- Check a normal operand in `TFlat.isLegal`. -/
def checkLegalArg (Γ : List (Ty × VarKind)) (t : Ty) : Arg K t → Bool
  | .var idx => checkVarKind Γ t (· == .normal) idx
  | .imm _ => true

/-- Check a tuple of normal operands in `TFlat.isLegal`. -/
def checkLegalArgs (Γ : List (Ty × VarKind)) : {ts : List Ty} → Tup (Arg K) ts → Bool
  | [], () => true
  | t :: _, (a, as) => checkLegalArg Γ t a && checkLegalArgs Γ as

/-- Push a signature of normal legal variables onto `Γ`. -/
def pushNormal (ts : List Ty) (Γ : List (Ty × VarKind)) : List (Ty × VarKind) :=
  pushTypes (ts.map (·, VarKind.normal)) Γ

/-- Check whether `OpCode` (other than `mkpair`/`unpair`, handled by `VarKind` rules) is legal
under `target`, given whether the right-hand operand of a shift/rotate is a uniform immediate. -/
def LegalTarget.isLegalOp (target : LegalTarget) :
    {as rs : List Ty} → OpCode as rs → (uniformImmRhs : Bool) → Bool
  | _, _, .copy t, _ => target.isLegalTy t
  | _, _, .add t, unif =>
    match t with
    | .bits n => n ∈ target.bitWidths
    | .pair a b => target.keepsPacked (.pair a b) && target.vecIntOpSupported (.add t) (.pair a b) unif
    | _ => false
  | _, _, .sub t, unif =>
    match t with
    | .bits n => n ∈ target.bitWidths
    | .pair a b => target.keepsPacked (.pair a b) && target.vecIntOpSupported (.sub t) (.pair a b) unif
    | _ => false
  | _, _, .mul t, unif =>
    match t with
    | .bits n => n ∈ target.bitWidths
    | .pair a b => target.keepsPacked (.pair a b) && target.vecIntOpSupported (.mul t) (.pair a b) unif
    | _ => false
  | _, _, .neg t, unif =>
    match t with
    | .bits n => n ∈ target.bitWidths
    | .pair a b => target.keepsPacked (.pair a b) && target.vecIntOpSupported (.neg t) (.pair a b) unif
    | _ => false
  | _, _, .and t, unif =>
    match t with
    | .bool => true
    | .bits n => n ∈ target.bitWidths
    | .float f => target.scalarFloatBitwise && f ∈ target.floatFmts
    | .pair a b => target.keepsPacked (.pair a b) && target.vecIntOpSupported (.and t) (.pair a b) unif
  | _, _, .or t, unif =>
    match t with
    | .bool => true
    | .bits n => n ∈ target.bitWidths
    | .float f => target.scalarFloatBitwise && f ∈ target.floatFmts
    | .pair a b => target.keepsPacked (.pair a b) && target.vecIntOpSupported (.or t) (.pair a b) unif
  | _, _, .xor t, unif =>
    match t with
    | .bool => true
    | .bits n => n ∈ target.bitWidths
    | .float f => target.scalarFloatBitwise && f ∈ target.floatFmts
    | .pair a b => target.keepsPacked (.pair a b) && target.vecIntOpSupported (.xor t) (.pair a b) unif
  | _, _, .not t, unif =>
    match t with
    | .bool => true
    | .bits n => n ∈ target.bitWidths
    | .float f => target.scalarFloatBitwise && f ∈ target.floatFmts
    | .pair a b => target.keepsPacked (.pair a b) && target.vecIntOpSupported (.not t) (.pair a b) unif
  | _, _, .ternlog t imm, unif =>
    match t with
    | .bits n => target.scalarTernlog && n ∈ target.bitWidths
    | .float f => target.scalarTernlog && target.scalarFloatBitwise && f ∈ target.floatFmts
    | .pair a b =>
      target.keepsPacked (.pair a b) && target.vecIntOpSupported (.ternlog t imm) (.pair a b) unif
    | .bool => false
  | _, _, .shl t, unif =>
    match t with
    | .bits n => n ∈ target.bitWidths
    | .pair a b => target.keepsPacked (.pair a b) && target.vecIntOpSupported (.shl t) (.pair a b) unif
    | _ => false
  | _, _, .lshr t, unif =>
    match t with
    | .bits n => n ∈ target.bitWidths
    | .pair a b => target.keepsPacked (.pair a b) && target.vecIntOpSupported (.lshr t) (.pair a b) unif
    | _ => false
  | _, _, .ashr t, unif =>
    match t with
    | .bits n => n ∈ target.bitWidths
    | .pair a b => target.keepsPacked (.pair a b) && target.vecIntOpSupported (.ashr t) (.pair a b) unif
    | _ => false
  | _, _, .rotl t, unif =>
    match t with
    | .bits n => n ∈ target.bitWidths
    | .pair a b => target.keepsPacked (.pair a b) && target.vecIntOpSupported (.rotl t) (.pair a b) unif
    | _ => false
  | _, _, .rotr t, unif =>
    match t with
    | .bits n => n ∈ target.bitWidths
    | .pair a b => target.keepsPacked (.pair a b) && target.vecIntOpSupported (.rotr t) (.pair a b) unif
    | _ => false
  | _, _, .fshl n, _ | _, _, .fshr n, _
  | _, _, .clz n, _ | _, _, .cls n, _ | _, _, .rbit n, _ | _, _, .ctz n, _ | _, _, .popcnt n, _
  | _, _, .addc n, _ | _, _, .subb n, _ | _, _, .umulw n, _ | _, _, .smulw n, _
  | _, _, .udiv n, _ | _, _, .sdiv n, _ | _, _, .urem n, _ | _, _, .srem n, _
  | _, _, .udiv0 n, _ | _, _, .sdiv0 n, _
  | _, _, .ofBool n, _ => n ∈ target.bitWidths && 0 < n
  | _, _, .bswap t, _ =>
    match t with
    | .bits n => n ∈ target.bitWidths && n % 8 == 0 && n > 8
    | _ => false
  | _, _, .cmp _ t _ _, _ =>
    match t with
    | .bits n => n ∈ target.bitWidths && 0 < n
    | .bool => target.boolCmp
    | _ => false
  | _, _, .select t, _ =>
    match t with
    | .bits n => n ∈ target.bitWidths
    | .float f => f ∈ target.floatFmts
    | .bool => target.boolSelect
    | .pair _ _ => false
  | _, _, .blend _ _ _, _ => false
  | _, _, .zext m n, _ | _, _, .sext m n, _ =>
    m ∈ target.bitWidths && n ∈ target.bitWidths && m < n
  | _, _, .trunc m n, _ =>
    m ∈ target.bitWidths && n ∈ target.bitWidths && n < m
  | _, _, .mkpair _ _, _ | _, _, .unpair _ _, _ => false
  | _, _, .bitcast t u _, _ => target.isLegalTy t && target.isLegalTy u && t != u
  | _, _, .shufd t imm, _ =>
    target.keepsPacked t && t.size != 0 && t.size % 128 == 0 &&
      target.vecIntOpSupported (.shufd t imm) t false
  | _, _, .shufb t, _ =>
    target.keepsPacked t && t.size != 0 && t.size % 128 == 0 &&
      target.vecIntOpSupported (.shufb t) t false
  | _, _, .alignr t imm, _ =>
    target.keepsPacked t && t.size != 0 && t.size % 128 == 0 &&
      target.vecIntOpSupported (.alignr t imm) t false
  | _, _, .blendw t imm, _ =>
    target.keepsPacked t && t.size != 0 && t.size % 128 == 0 &&
      target.vecIntOpSupported (.blendw t imm) t false
  | _, _, .sha256rnds2, _ =>
    target.keepsPacked v4i32 && target.vecIntOpSupported .sha256rnds2 v4i32 false
  | _, _, .sha256msg1, _ =>
    target.keepsPacked v4i32 && target.vecIntOpSupported .sha256msg1 v4i32 false
  | _, _, .sha256msg2, _ =>
    target.keepsPacked v4i32 && target.vecIntOpSupported .sha256msg2 v4i32 false
  | _, _, .fadd t, _ =>
    match t with
    | .float f => f ∈ target.floatFmts
    | .pair a b => target.keepsPacked (.pair a b) && target.vecFloatOpSupported (.fadd t) (.pair a b)
    | _ => false
  | _, _, .fsub t, _ =>
    match t with
    | .float f => f ∈ target.floatFmts
    | .pair a b => target.keepsPacked (.pair a b) && target.vecFloatOpSupported (.fsub t) (.pair a b)
    | _ => false
  | _, _, .fmul t, _ =>
    match t with
    | .float f => f ∈ target.floatFmts
    | .pair a b => target.keepsPacked (.pair a b) && target.vecFloatOpSupported (.fmul t) (.pair a b)
    | _ => false
  | _, _, .fdiv t, _ =>
    match t with
    | .float f => f ∈ target.floatFmts
    | .pair a b => target.keepsPacked (.pair a b) && target.vecFloatOpSupported (.fdiv t) (.pair a b)
    | _ => false
  | _, _, .ffma t, _ =>
    match t with
    | .float f => f ∈ target.floatFmts
    | .pair a b => target.keepsPacked (.pair a b) && target.vecFloatOpSupported (.ffma t) (.pair a b)
    | _ => false
  | _, _, .fsqrt t, _ =>
    match t with
    | .float f => f ∈ target.floatFmts
    | .pair a b => target.keepsPacked (.pair a b) && target.vecFloatOpSupported (.fsqrt t) (.pair a b)
    | _ => false
  | _, _, .fneg t, _ =>
    match t with
    | .float f => f ∈ target.floatFmts
    | .pair a b => target.keepsPacked (.pair a b) && target.vecFloatOpSupported (.fneg t) (.pair a b)
    | _ => false
  | _, _, .fabs t, _ =>
    match t with
    | .float f => f ∈ target.floatFmts
    | .pair a b => target.keepsPacked (.pair a b) && target.vecFloatOpSupported (.fabs t) (.pair a b)
    | _ => false
  | _, _, .fcmp _ t _ _, _ =>
    match t with
    | .float f => f ∈ target.floatFmts
    | _ => false
  | _, _, .fptoui f n, _ | _, _, .fptosi f n, _ | _, _, .uitofp n f, _ | _, _, .sitofp n f, _ =>
    f ∈ target.floatFmts && n ∈ target.bitWidths
  | _, _, .fcvt f g, _ => f ∈ target.floatFmts && g ∈ target.floatFmts

/-- True iff `code` is a shift/rotate whose right-hand operand in `args` is a uniform `.imm`. -/
def isUniformImmShift : {as rs : List Ty} → OpCode as rs → Tup (Arg K) as → Bool
  | _, _, .shl t, (_, .imm c, ())
  | _, _, .lshr t, (_, .imm c, ())
  | _, _, .ashr t, (_, .imm c, ())
  | _, _, .rotl t, (_, .imm c, ())
  | _, _, .rotr t, (_, .imm c, ()) => (uniformShiftLeaf? t c).isSome
  | _, _, _, _ => false

mutual
/-- Total computable legality checker for `TFlat rs` under value context `Γ` and label context `Δ`. -/
def TFlat.isLegal (target : LegalTarget) {rs : List Ty}
    (Γ : List (Ty × VarKind)) (Δ : List (List Ty)) : TFlat rs → Bool
  | .let_ (ts := ts) op k =>
    let ⟨code, args⟩ := op
    match code with
    | .unpair a b =>
      let (p, ()) := args
      target.allowPackBridge && target.hasLegalLeaves (.pair a b) &&
      (match p with
       | .var idx =>
         checkVarKind Γ (.pair a b)
           (fun vk => (vk == .normal && target.isLegalTy (.pair a b)) || vk == .unpackedBridge) idx
       | .imm _ => false) &&
      let ka := if target.isLegalTy a then VarKind.normal else .unpackedBridge
      let kb := if target.isLegalTy b then VarKind.normal else .unpackedBridge
      k.isLegal target (pushTypes [(a, ka), (b, kb)] Γ) Δ
    | .mkpair a b =>
      let (va, vb, ()) := args
      let chkIn (u : Ty) : Arg K u → Bool
        | .var idx =>
          checkVarKind Γ u
            (fun vk => (vk == .normal && target.isLegalTy u) || vk == .packedBridge) idx
        | .imm _ => target.isLegalTy u
      target.allowPackBridge && target.hasLegalLeaves (.pair a b) &&
      chkIn a va && chkIn b vb &&
      let kres := if target.isLegalTy (.pair a b) then VarKind.normal else .packedBridge
      k.isLegal target ((.pair a b, kres) :: Γ) Δ
    | _ =>
      target.isLegalOp code (isUniformImmShift op.code op.args) && target.isLegalSig ts &&
        checkLegalArgs Γ args && k.isLegal target (pushNormal ts Γ) Δ
  | .load t a k =>
    target.isLegalTy t && checkLegalArg Γ i64 a && k.isLegal target ((t, .normal) :: Γ) Δ
  | .store (t := t) v a k =>
    target.isLegalTy t && checkLegalArg Γ t v && checkLegalArg Γ i64 a && k.isLegal target Γ Δ
  | .call _ (as := as) bs args k =>
    target.isLegalSig as && target.isLegalSig bs && checkLegalArgs Γ args &&
      k.isLegal target (pushNormal bs Γ) Δ
  | .jnz c t e =>
    checkLegalArg Γ .bool c && t.isLegal target Γ Δ && e.isLegal target Γ Δ
  | .jump (ts := ts) j args =>
    target.isLegalSig ts &&
      (match listGet? Δ j with
       | some ts' => match listTyDecEq ts' ts with | isTrue _ => true | isFalse _ => false
       | none => false) &&
      checkLegalArgs Γ args
  | .ret vs => target.isLegalSig rs && checkLegalArgs Γ vs
  | .exit _ (as := as) args => target.isLegalSig as && checkLegalArgs Γ args
  | .hlt => true
  | .group (sig := sig) bodies k =>
    sig.all target.isLegalSig &&
      bodies.isLegal target Γ (pushTypes sig Δ) && k.isLegal target Γ (pushTypes sig Δ)

/-- Total computable legality checker for `TBlocks rs sig`. -/
def TBlocks.isLegal (target : LegalTarget) {rs : List Ty}
    (Γ : List (Ty × VarKind)) (Δ : List (List Ty)) : {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, .nil => true
  | _, .cons (ts := ts) b bs =>
    target.isLegalSig ts && b.isLegal target (pushNormal ts Γ) Δ && bs.isLegal target Γ Δ
end

/-- Computable `Legal` predicate on a closed `Func as rs` via `toTFlat`. -/
def Func.isLegal (target : LegalTarget) {as rs : List Ty} (f : Func as rs) : Bool :=
  target.isLegalSig as && target.isLegalSig rs &&
    (toTFlat (f K KL (Tup.levels as 0)) as.length 0).isLegal target (pushNormal as []) []

/-! ## Source-program supportability check for `legal_isLegal` -/

/-- True iff `target` supports every scalar leaf width (`∃ w ∈ bitWidths, n ≤ w`) and float
format (`f ∈ floatFmts`, `f.width ≤ 64`) occurring in `t`. -/
def LegalTarget.supportsTy (target : LegalTarget) : Ty → Bool
  | .bool => true
  | .bits n => target.bitWidths.any (n ≤ ·) && n ≤ 64
  | .float f => f ∈ target.floatFmts && f.width ≤ 64
  | .pair a b => target.supportsTy a && target.supportsTy b

/-- Target configuration sanity check (true by `decide` on `aarch64`, `scalar64`, `x64`, etc.). -/
def LegalTarget.valid (target : LegalTarget) : Bool :=
  (8 ∈ target.bitWidths) && (64 ∈ target.bitWidths) &&
    target.bitWidths.all (fun w => 0 < w && w % 8 == 0 && w ≤ 64) &&
    target.floatFmts.all fun f => f.width ∈ target.bitWidths && f.width ≤ 64

/-- Check that every type in `op.code` is supported by `target`. -/
def LegalTarget.supportsOpCode (target : LegalTarget) : {as rs : List Ty} → OpCode as rs → Bool
  | _, _, .copy t | _, _, .add t | _, _, .sub t | _, _, .mul t | _, _, .neg t
  | _, _, .and t | _, _, .or t | _, _, .xor t | _, _, .not t | _, _, .ternlog t _
  | _, _, .shl t | _, _, .lshr t | _, _, .ashr t | _, _, .rotl t | _, _, .rotr t
  | _, _, .bswap t | _, _, .cmp _ t _ _ | _, _, .select t | _, _, .blend t _ _
  | _, _, .fadd t | _, _, .fsub t | _, _, .fmul t | _, _, .fdiv t | _, _, .ffma t
  | _, _, .fsqrt t | _, _, .fneg t | _, _, .fabs t | _, _, .fcmp _ t _ _ => target.supportsTy t
  | _, _, .shufd t _ | _, _, .shufb t | _, _, .alignr t _ | _, _, .blendw t _ =>
    target.supportsTy t && (32 ∈ target.bitWidths)
  | _, _, .fshl n | _, _, .fshr n | _, _, .clz n | _, _, .cls n | _, _, .rbit n
  | _, _, .ctz n | _, _, .popcnt n | _, _, .ofBool n
  | _, _, .addc n | _, _, .subb n | _, _, .umulw n | _, _, .smulw n
  | _, _, .udiv n | _, _, .sdiv n | _, _, .urem n | _, _, .srem n
  | _, _, .udiv0 n | _, _, .sdiv0 n => target.supportsTy (.bits n)
  | _, _, .zext m n | _, _, .sext m n | _, _, .trunc m n =>
    target.supportsTy (.bits m) && target.supportsTy (.bits n)
  | _, _, .mkpair a b | _, _, .unpair a b => target.supportsTy a && target.supportsTy b
  | _, _, .bitcast t u _ => target.supportsTy t && target.supportsTy u
  | _, _, .sha256rnds2 | _, _, .sha256msg1 | _, _, .sha256msg2 =>
    target.supportsTy v4i32 && (32 ∈ target.bitWidths)
  | _, _, .fptoui f n | _, _, .fptosi f n | _, _, .uitofp n f | _, _, .sitofp n f =>
    target.supportsTy (.float f) && target.supportsTy (.bits n)
  | _, _, .fcvt f g => target.supportsTy (.float f) && target.supportsTy (.float g)

mutual
/-- Check that every type/operation in a `TFlat` is within `target`'s legalizable domain. -/
def TFlat.supportsSource (target : LegalTarget) {rs : List Ty} : TFlat rs → Bool
  | .let_ op k => target.supportsOpCode op.code && k.supportsSource target
  | .load t _ k => target.supportsTy t && t.bytes ≤ 2 ^ 64 && k.supportsSource target
  | .store (t := t) _ _ k => target.supportsTy t && t.bytes ≤ 2 ^ 64 && k.supportsSource target
  | .call _ (as := as) bs _ k =>
    as.all target.supportsTy && bs.all target.supportsTy && k.supportsSource target
  | .jnz _ t e => t.supportsSource target && e.supportsSource target
  | .jump (ts := ts) _ _ => ts.all target.supportsTy
  | .ret _ => rs.all target.supportsTy
  | .exit _ (as := as) _ => as.all target.supportsTy
  | .hlt => true
  | .group (sig := sig) bodies k =>
    sig.all (·.all target.supportsTy) && bodies.supportsSource target && k.supportsSource target

def TBlocks.supportsSource (target : LegalTarget) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, .nil => true
  | _, .cons (ts := ts) b bs =>
    ts.all target.supportsTy && b.supportsSource target && bs.supportsSource target
end

/-- Computable check that `f : Func as rs` uses only bit widths/float formats legalizable by `target`. -/
def Func.supportsSource (target : LegalTarget) {as rs : List Ty} (f : Func as rs) : Bool :=
  target.valid && as.all target.supportsTy && rs.all target.supportsTy &&
    (toTFlat (f K KL (Tup.levels as 0)) as.length 0).supportsSource target

end LeanQbe.T
