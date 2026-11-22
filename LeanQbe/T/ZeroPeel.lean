module

public import LeanQbe.T.OptUtil

/-!
# Mid-End Constant-Fill Widening & Bounded 1st-Iter Loop Peeling (`O-M3`)

Standalone typed-IR (`TFlat`) mid-end optimization pass `Func.zeroPeel` (and configurable
`Func.zeroPeelWith`, `Fn.zeroPeel`, `TFlat.zeroPeelWith`) combining two high-ROI transforms:

1. **Contiguous Constant-Fill Loop Widening (`widenFillSingle`):**
   Detects single-block counted loops (`.group (sig := [[i64]]) (.cons body .nil) (.jump 0 init)`)
   that store a constant `i8`/`i16`/`i32`/`i64` splatted value to `base + ((off + i) <<< s)`
   (`s ∈ {0, 1, 2, 3}`, commuted forms supported) while incrementing `i` by `1` toward `bound`
   (`.ult`/`.ule`/`.ugt`/`.uge`). Prepends a pre-loop executing unrolled `i64` stores
   (`unrollN := 8`, i.e., `64` bytes/iter) while `(bound - i) ≥u stepK`, then branches to the
   original scalar loop (at label `1`) to handle `0..stepK-1` tail iterations and normal exit.

2. **Bounded 1st-Iteration Loop Peeling (`peelSingle`):**
   For single-block loops with `zpLoops body == 0`, `zpSize body ≤ peelBudget` (default `36`),
   `countJump0 k == 1`, `!hasGroup k`, and (by default, `peelImmOnly := true`) an immediate
   argument at the loop entry `.jump 0`, unrolls the first iteration directly into the entry arm
   (`inlineJump0`) without modifying outer `.group` back-edges (exposing constant/0-iter fast paths
   such as single-byte `readLeb128`).

Correctness (`LeanQbe/T/ZeroPeelLemmas.lean`): `Func.zeroPeel_wf`, `Func.zeroPeel_spec`,
`Func.zeroPeel_callsOk`, `Fn.zeroPeel_wf`, `Fn.zeroPeel_spec`, `Fn.zeroPeel_callsOk`, and
`Module.zeroPeel_ok`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-- Configuration parameters for `Func.zeroPeelWith`. -/
structure ZeroPeelConfig where
  /-- Number of unrolled `i64` stores per wide-loop iteration (`0 < unrollN ≤ 64` enables
  constant-fill widening; default `8` = `64` bytes per iteration). -/
  unrollN : Nat := 8
  /-- Maximum `TFlat` node count of a single-block loop body eligible for 1st-iter peeling
  (`0` disables loop peeling; default `36`). -/
  peelBudget : Nat := 36
  /-- Restrict 1st-iter peeling to entry jumps passing at least one immediate operand
  (default `true`). -/
  peelImmOnly : Bool := true
  /-- Skip rewriting functions with `zpSize tf ≥ maxFnSize` to bound compile time and code
  size (default `4000`). -/
  maxFnSize : Nat := 4000
  deriving Repr, DecidableEq, Inhabited

namespace ZeroPeel

/-! ## De Bruijn variable shifting and 1st-iteration inlining -/

/-- Shift de Bruijn variable indices `≥ d` by `+n` inside an operand. -/
def shiftArgAbove (d n : Nat) : {t : Ty} → Arg K t → Arg K t
  | _, .var i => if i >= d then .var (i + n) else .var i
  | _, .imm v => .imm v

/-- Shift all variable indices in an operand by `+n`. -/
abbrev tArgShift (n : Nat) {t : Ty} (a : Arg K t) : Arg K t :=
  shiftArgAbove 0 n a

/-- Shift de Bruijn variable indices `≥ d` by `+n` across an operand tuple. -/
def shiftTupAbove (d n : Nat) : {ts : List Ty} → Tup (Arg K) ts → Tup (Arg K) ts
  | [], () => ()
  | _ :: _, (a, as) => (shiftArgAbove d n a, shiftTupAbove d n as)

mutual
/-- Shift free de Bruijn variable indices `≥ d` by `+n` inside a `TFlat` term. -/
def shiftTFlat (d n : Nat) : {rs : List Ty} → TFlat rs → TFlat rs
  | _, .let_ (ts := ts) op k =>
    let ⟨code, args⟩ := op
    .let_ ⟨code, shiftTupAbove d n args⟩ (shiftTFlat (d + ts.length) n k)
  | _, .load t a k => .load t (shiftArgAbove d n a) (shiftTFlat (d + 1) n k)
  | _, .store v a k => .store (shiftArgAbove d n v) (shiftArgAbove d n a) (shiftTFlat d n k)
  | _, .call f bs args k => .call f bs (shiftTupAbove d n args) (shiftTFlat (d + bs.length) n k)
  | _, .jnz c t e => .jnz (shiftArgAbove d n c) (shiftTFlat d n t) (shiftTFlat d n e)
  | _, .jump j args => .jump j (shiftTupAbove d n args)
  | _, .ret vs => .ret (shiftTupAbove d n vs)
  | _, .exit f args => .exit f (shiftTupAbove d n args)
  | _, .hlt => .hlt
  | _, .group bs k => .group (shiftTBlocks d n bs) (shiftTFlat d n k)

/-- Block-list companion of `shiftTFlat`. -/
def shiftTBlocks (d n : Nat) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → TBlocks rs sig
  | _, .nil => .nil
  | _, .cons (ts := ts) b bs => .cons (shiftTFlat (d + ts.length) n b) (shiftTBlocks d n bs)
end

/-- Bind an operand tuple evaluated at depth `d` via `.copy` instructions before `body`. -/
def letBindTup {rs : List Ty} :
    {ts : List Ty} → Tup (Arg K) ts → Nat → TFlat rs → TFlat rs
  | [], (), _, body => body
  | t :: _, (a, as), d, body =>
    .let_ (op1 (.copy t) (shiftArgAbove 0 d a)) (letBindTup as (d + 1) body)

/-- Replace label-`0` tail jumps in `k` (assuming `!hasGroup k`) with a 1-step inlined copy of
`body` parameterized by `ts0`. -/
def inlineJump0 {rs : List Ty} (body : TFlat rs) (ts0 : List Ty) : Nat → TFlat rs → TFlat rs
  | d, .let_ (ts := ts) op k => .let_ op (inlineJump0 body ts0 (d + ts.length) k)
  | d, .load t a k => .load t a (inlineJump0 body ts0 (d + 1) k)
  | d, .store v a k => .store v a (inlineJump0 body ts0 d k)
  | d, .call f bs args k => .call f bs args (inlineJump0 body ts0 (d + bs.length) k)
  | d, .jnz c t e => .jnz c (inlineJump0 body ts0 d t) (inlineJump0 body ts0 d e)
  | d, .jump (ts := ts) j args =>
    if j == 0 then
      if h : ts = ts0 then
        letBindTup (h ▸ args) 0 (shiftTFlat ts0.length d body)
      else .jump j args
    else .jump j args
  | _, .ret vs => .ret vs
  | _, .exit f args => .exit f args
  | _, .hlt => .hlt
  | _, .group bs k => .group bs k

/-! ## Structural predicates & size/loop metrics -/

/-- True iff an operand tuple contains at least one `.imm` operand. -/
def tupHasImm : {ts : List Ty} → Tup (Arg K) ts → Bool
  | [], () => false
  | _ :: _, (.imm _, _) => true
  | _ :: _, (.var _, rest) => tupHasImm rest

/-- True iff some label-`0` jump in `tf` passes at least one `.imm` operand. -/
def kJump0HasImm {rs : List Ty} : TFlat rs → Bool
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => kJump0HasImm k
  | .jnz _ t e => kJump0HasImm t || kJump0HasImm e
  | .jump j args => j == 0 && tupHasImm args
  | _ => false

/-- True iff `tf` contains any nested `.group` node outside nested block bodies. -/
def hasGroup {rs : List Ty} : TFlat rs → Bool
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => hasGroup k
  | .jnz _ t e => hasGroup t || hasGroup e
  | .group _ _ => true
  | _ => false

/-- Count occurrences of `.jump 0` in `tf` (without entering nested `.group`s). -/
def countJump0 {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => countJump0 k
  | .jnz _ t e => countJump0 t + countJump0 e
  | .jump 0 _ => 1
  | _ => 0

mutual
/-- Node count of a `TFlat` term. -/
def zpSize {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => 1 + zpSize k
  | .jnz _ t e => 1 + zpSize t + zpSize e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => 1
  | .group bodies k => 1 + zpSizeB bodies + zpSize k

/-- Block-list companion of `zpSize`. -/
def zpSizeB {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Nat
  | _, .nil => 0
  | _, .cons b bs => zpSize b + zpSizeB bs
end

mutual
/-- Count explicit jumps to de Bruijn label `l` in a `TFlat` term. -/
def zpJumps (l : Nat) {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => zpJumps l k
  | .jnz _ t e => zpJumps l t + zpJumps l e
  | .jump j _ => if j == l then 1 else 0
  | .ret _ | .exit _ _ | .hlt => 0
  | .group (sig := sig) bodies k => zpJumpsB (l + sig.length) bodies + zpJumps (l + sig.length) k

/-- Block-list companion of `zpJumps`. -/
def zpJumpsB (l : Nat) {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Nat
  | _, .nil => 0
  | _, .cons b bs => zpJumps l b + zpJumpsB l bs
end

mutual
/-- Count single-block self-jumping loops inside a `TFlat` term. -/
def zpLoops {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => zpLoops k
  | .jnz _ t e => zpLoops t + zpLoops e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => 0
  | .group (sig := [_]) (.cons b .nil) k =>
    (if zpJumps 0 b > 0 then 1 else 0) + zpLoops b + zpLoops k
  | .group bodies k => zpLoopsB bodies + zpLoops k

/-- Block-list companion of `zpLoops`. -/
def zpLoopsB {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Nat
  | _, .nil => 0
  | _, .cons b bs => zpLoops b + zpLoopsB bs
end

/-! ## Constant-fill pattern matcher & wide-store builder -/

/-- True iff `c` is a deterministic, total (UB-free) bitvector/pair/bool opcode whose
weakest precondition unconditionally supplies its computed output tuple. -/
def isTotalPureOp : {as rs : List Ty} → OpCode as rs → Bool
  | _, _, .copy _ => true
  | _, _, .add t | _, _, .sub t | _, _, .mul t | _, _, .neg t
  | _, _, .shl t | _, _, .lshr t | _, _, .ashr t | _, _, .rotl t | _, _, .rotr t => !t.hasFloat
  | _, _, .and _ | _, _, .or _ | _, _, .xor _ | _, _, .not _
  | _, _, .ternlog _ _ | _, _, .fshl _ | _, _, .fshr _
  | _, _, .clz _ | _, _, .cls _ | _, _, .rbit _ | _, _, .ctz _ | _, _, .popcnt _ => true
  | _, _, .cmp _ t _ _ => !t.hasFloat
  | _, _, .select _ | _, _, .blend _ _ _ | _, _, .ofBool _ => true
  | _, _, .zext m n | _, _, .sext m n => decide (m ≤ n)
  | _, _, .trunc m n => decide (n ≤ m)
  | _, _, .addc _ | _, _, .subb _ | _, _, .umulw _ | _, _, .smulw _
  | _, _, .udiv0 _ | _, _, .sdiv0 _ | _, _, .mkpair _ _ | _, _, .unpair _ _ => true
  | _, _, _ => false

/-- Symbolic 64-bit value expression relative to a single-argument (`i : i64`) loop body. -/
inductive Sym64
  | loopI
  | outer (idx0 : Nat)
  | const (v : BitVec 64)
  | add (a b : Sym64)
  | shlConst (a : Sym64) (s : Nat)
  | cmpU (lt : Bool) (bound : Arg K i64)
  | other
  deriving Inhabited

/-- Resolve an operand against symbolic loop-local stack `env` (`loopI` at `env.size`).
Only `i64` variables become `.loopI` or `.outer`, ensuring outer operands preserve `i64` type. -/
def argToSym64 (env : Array Sym64) : {t : Ty} → Arg K t → Sym64
  | .bits 64, .imm v => .const v
  | t, .var idx =>
    let d := env.size
    if idx < d then env[d - 1 - idx]!
    else if t == i64 then
      if idx == d then .loopI
      else .outer (idx - (d + 1))
    else .other
  | _, .imm _ => .other

/-- Convert a loop-invariant symbolic value back to an `Arg K i64` in the `.group`-enclosing
variable scope (index `0` at `.group` entry). -/
def symToOuterArg64 : Sym64 → Option (Arg K i64)
  | .outer idx0 => some (.var idx0)
  | .const v => some (.imm v)
  | _ => none

/-- Match `loopI` or `off + loopI` / `loopI + off` with loop-invariant `off`. -/
def matchOffLoop : Sym64 → Option (Option (Arg K i64))
  | .loopI => some none
  | .add a b =>
    match a, b with
    | .loopI, x => (symToOuterArg64 x).map some
    | x, .loopI => (symToOuterArg64 x).map some
    | _, _ => none
  | _ => none

/-- Match `base + (idx <<< sExpected)` (or `base + idx` when `sExpected = 0`, in either order). -/
def matchAddr (sExpected : Nat) : Sym64 → Option (Arg K i64 × Option (Arg K i64))
  | .add x y =>
    let check (p idx : Sym64) : Option (Arg K i64 × Option (Arg K i64)) :=
      match symToOuterArg64 p with
      | some base =>
        if sExpected == 0 then (matchOffLoop idx).map (base, ·)
        else match idx with
          | .shlConst inner s =>
            if s == sExpected then (matchOffLoop inner).map (base, ·) else none
          | _ => none
      | none => none
    match check x y with
    | some r => some r
    | none => check y x
  | _ => none

/-- Match `loopI + 1` or `1 + loopI`. -/
def matchInc1 : Sym64 → Bool
  | .add .loopI (.const 1#64) => true
  | .add (.const 1#64) .loopI => true
  | _ => false

/-- Core symbolic evaluator for single-result 64-bit integer/compare operations. -/
def evalSymOp1 (env : Array Sym64) {ts : List Ty} (op : Op K ts) : Option Sym64 :=
  let ⟨code, args⟩ := op
  match code with
  | .copy t =>
    if h : t = i64 then some (argToSym64 env (h ▸ args).1) else none
  | .add t =>
    if h : t = i64 then
      let (a, b, ()) := h ▸ args
      some (.add (argToSym64 env a) (argToSym64 env b))
    else none
  | .shl t =>
    if h : t = i64 then
      let (a, b, ()) := h ▸ args
      some (match argToSym64 env b with
        | .const v => .shlConst (argToSym64 env a) (v.toNat % 64)
        | _ => .other)
    else none
  | .cmp o t _ _ =>
    if h : t = i64 then
      let (a, b, ()) := h ▸ args
      let sa := argToSym64 env a
      let sb := argToSym64 env b
      some <| (match o, sa, sb with
        | .ult, .loopI, _ => (symToOuterArg64 sb).map (Sym64.cmpU true)
        | .ule, .loopI, _ => (symToOuterArg64 sb).map (Sym64.cmpU false)
        | .ugt, _, .loopI => (symToOuterArg64 sa).map (Sym64.cmpU true)
        | .uge, _, .loopI => (symToOuterArg64 sa).map (Sym64.cmpU false)
        | _, _, _ => none).getD .other
    else none
  | _ => none

/-- Abstractly evaluate `op` to a list of `Sym64` values matching `ts.length`. -/
def evalSymOp (env : Array Sym64) {ts : List Ty} (op : Op K ts) : List Sym64 :=
  match ts, evalSymOp1 env op with
  | [_], some s => [s]
  | _, _ => ts.map fun _ => .other

/-- Recognized constant-fill scalar loop specification. -/
structure FillSpec where
  isLt : Bool
  bound : Arg K i64
  base : Arg K i64
  off? : Option (Arg K i64)
  shift : Nat
  fill64 : BitVec 64

/-- Replicate a constant `i8`/`i16`/`i32`/`i64` fill scalar to a 64-bit word and return its
element log2 byte size `shift ∈ {0, 1, 2, 3}`. -/
def splatVal64 : {t : Ty} → Val t → Option (Nat × BitVec 64)
  | .bits 8, v =>
    let x : BitVec 64 := v.setWidth 64
    let x2 := x ||| (x <<< 8)
    let x4 := x2 ||| (x2 <<< 16)
    some (0, x4 ||| (x4 <<< 32))
  | .bits 16, v =>
    let x : BitVec 64 := v.setWidth 64
    let x2 := x ||| (x <<< 16)
    some (1, x2 ||| (x2 <<< 32))
  | .bits 32, v =>
    let x : BitVec 64 := v.setWidth 64
    some (2, x ||| (x <<< 32))
  | .bits 64, v => some (3, v)
  | _, _ => none

/-- Verify that `k` executes only total pure `.let_` bindings and tail-jumps to label `0`
with `loopI + 1`. -/
def checkJump0Inc1 {rs : List Ty} (env : Array Sym64) : TFlat rs → Bool
  | .let_ op k =>
    isTotalPureOp op.code && checkJump0Inc1 (env ++ (evalSymOp env op).toArray) k
  | .jump (ts := [.bits 64]) 0 (nextArg, ()) => matchInc1 (argToSym64 env nextArg)
  | _ => false

/-- Recognize a total-pure `.let_` prefix ending in a constant fill `.store` followed by
`checkJump0Inc1`. -/
def matchBodyTail {rs : List Ty} (env : Array Sym64) (isLt : Bool) (bound : Arg K i64) :
    TFlat rs → Option FillSpec
  | .let_ op k =>
    if isTotalPureOp op.code then
      matchBodyTail (env ++ (evalSymOp env op).toArray) isLt bound k
    else none
  | .store valArg addrArg cont =>
    match valArg with
    | .imm v =>
      match splatVal64 v with
      | some (shift, fill64) =>
        match matchAddr shift (argToSym64 env addrArg) with
        | some (base, off?) =>
          if checkJump0Inc1 env cont then some { isLt, bound, base, off?, shift, fill64 }
          else none
        | none => none
      | none => none
    | _ => none
  | _ => none

/-- Recognize a counted fill loop body: pure `.let_` header, `.jnz` on `i <u bound` or `i ≤u bound`,
and a `matchBodyTail` true arm. -/
def matchFillBody {rs : List Ty} (env : Array Sym64) : TFlat rs → Option FillSpec
  | .let_ op k =>
    if isTotalPureOp op.code then
      matchFillBody (env ++ (evalSymOp env op).toArray) k
    else none
  | .jnz c t _ =>
    match argToSym64 env c with
    | .cmpU isLt bnd => matchBodyTail env isLt bnd t
    | _ => none
  | _ => none

/-- Helper emitting the remaining sequential 64-bit stores after the first store. -/
def mkStoreChainGoRest {rs : List Ty} (fill64 : BitVec 64) (stepK : Nat) :
    Nat → Nat → Nat → TFlat rs
  | _, 0, curIDepth =>
    .let_ (op2 (.add i64) (.var curIDepth) (.imm (BitVec.ofNat 64 stepK)))
      (.jump (ts := [i64]) 0 (.var 0, ()))
  | m, r + 1, curIDepth =>
    .let_ (op2 (.add i64) (.var (m - 1)) (.imm (BitVec.ofNat 64 (8 * m))))
      (.store (t := i64) (.imm fill64) (.var 0)
        (mkStoreChainGoRest fill64 stepK (m + 1) r (curIDepth + 1)))

/-- Emit `n` sequential 64-bit stores from `basePtr` at `0, 8, ..., 8*(n-1)` given `basePtr` at var
index `0` and `i` at `iDepth`, then jump back to label `0` with `i + stepK`. -/
def mkStoreChain {rs : List Ty} (fill64 : BitVec 64) (stepK : Nat) : Nat → Nat → TFlat rs
  | 0, _ => .hlt
  | 1, iDepth =>
    .store (t := i64) (.imm fill64) (.var 0)
      (.let_ (op2 (.add i64) (.var iDepth) (.imm (BitVec.ofNat 64 stepK)))
        (.jump (ts := [i64]) 0 (.var 0, ())))
  | r + 2, iDepth =>
    .store (t := i64) (.imm fill64) (.var 0) (mkStoreChainGoRest fill64 stepK 1 (r + 1) iDepth)

/-- Build the wide-loop body (`label 0` of inner `.group`, while `label 1` is the enclosing scalar
tail loop). -/
def mkWideBody {rs : List Ty} (spec : FillSpec) (unrollN : Nat) : TFlat rs :=
  let k64 := 8 >>> spec.shift
  let stepK := unrollN * k64
  let bnd1 := tArgShift 1 spec.bound
  let withBase (d : Nat) (idxVar : Arg K i64) : TFlat rs :=
    .let_ (op2 (.add i64) (tArgShift d spec.base) idxVar)
      (mkStoreChain spec.fill64 stepK unrollN d)
  let withShift (d : Nat) (idxVar : Arg K i64) : TFlat rs :=
    if spec.shift == 0 then withBase d idxVar
    else
      .let_ (op2 (.shl i64) idxVar (.imm (BitVec.ofNat 64 spec.shift)))
        (withBase (d + 1) (.var 0))
  let bodyTrue : TFlat rs :=
    match spec.off? with
    | none => withShift 3 (.var 2)
    | some off =>
      .let_ (op2 (.add i64) (.var 2) (tArgShift 3 off))
        (withShift 4 (.var 0))
  .let_ (op2 (.sub i64) bnd1 (.var 0))
    (.let_ (op2 (.uge i64) (.var 0) (.imm (BitVec.ofNat 64 stepK)))
      (.jnz (.var 0) bodyTrue (.jump (ts := [i64]) 1 (.var 2, ()))))

/-- Build the wide-loop wrapper group (`label 0` = wide loop, `label 1` = outer scalar tail)
with an entry bounds guard. -/
def mkWideWrapper {rs : List Ty} (spec : FillSpec) (unrollN : Nat)
    (initArg : Arg K i64) : TFlat rs :=
  let cmpOp : CmpOp := if spec.isLt then .ult else .ule
  let h : (Ty.bits 64).mask = Ty.bool := rfl
  let wb := mkWideBody spec unrollN
  let kCheck : TFlat rs :=
    .let_ (op2 (.cmp cmpOp (.bits 64) .bool h) initArg spec.bound)
      (.jnz (.var 0)
        (.jump (ts := [i64]) 0 (tArgShift 1 initArg, ()))
        (.jump (ts := [i64]) 1 (tArgShift 1 initArg, ())))
  .group (sig := [[i64]]) (.cons wb .nil) kCheck

/-! ## Single-node rules and bottom-up `TFlat` pass -/

/-- Attempt constant-fill loop widening on a single-block group `(body, k)`. -/
def widenFillSingle (unrollN : Nat) {rs : List Ty} (ts0 : List Ty) (body k : TFlat rs) :
    Option (TFlat rs) :=
  if unrollN == 0 || unrollN > 64 then none
  else
    match ts0, k with
    | [.bits 64], .jump (ts := [.bits 64]) 0 (initArg, ()) =>
      match matchFillBody #[] body with
      | some spec =>
        some (.group (sig := [[.bits 64]]) (.cons body .nil)
          (mkWideWrapper spec unrollN initArg))
      | none => none
    | _, _ => none

/-- Attempt bounded 1st-iteration loop peeling on a single-block group `(body, k)`. -/
def peelSingle (cfg : ZeroPeelConfig) {rs : List Ty} (ts0 : List Ty) (body k : TFlat rs) :
    Option (TFlat rs) :=
  if cfg.peelBudget > 0 && zpLoops body == 0 && zpSize body ≤ cfg.peelBudget &&
      countJump0 k == 1 && !hasGroup k && (!cfg.peelImmOnly || kJump0HasImm k) then
    some (.group (sig := [ts0]) (.cons body .nil) (inlineJump0 body ts0 0 k))
  else
    none

mutual
/-- Bottom-up wide-fill + 1st-iter loop-peeling rewrite on `TFlat rs`. -/
def zpeelTF (cfg : ZeroPeelConfig) {rs : List Ty} : TFlat rs → TFlat rs
  | .let_ op k => .let_ op (zpeelTF cfg k)
  | .load t a k => .load t a (zpeelTF cfg k)
  | .store v a k => .store v a (zpeelTF cfg k)
  | .call f bs args k => .call f bs args (zpeelTF cfg k)
  | .jnz c t e => .jnz c (zpeelTF cfg t) (zpeelTF cfg e)
  | .jump j args => .jump j args
  | .ret vs => .ret vs
  | .exit f args => .exit f args
  | .hlt => .hlt
  | .group (sig := sig) bs k =>
    let bs' := zpeelBs cfg bs
    let k' := zpeelTF cfg k
    match sig, bs' with
    | [ts0], .cons body .nil =>
      match widenFillSingle cfg.unrollN ts0 body k' with
      | some g => g
      | none =>
        match peelSingle cfg ts0 body k' with
        | some g => g
        | none => .group (sig := [ts0]) (.cons body .nil) k'
    | _, _ => .group bs' k'

/-- Block-list companion of `zpeelTF`. -/
def zpeelBs (cfg : ZeroPeelConfig) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → TBlocks rs sig
  | _, .nil => .nil
  | _, .cons b bs => .cons (zpeelTF cfg b) (zpeelBs cfg bs)
end

end ZeroPeel

/-- Apply wide constant-fill vectorization/unrolling and bounded 1st-iteration loop peeling
directly on a `TFlat` term. -/
def TFlat.zeroPeelWith (cfg : ZeroPeelConfig := {}) {rs : List Ty} (tf : TFlat rs) :
    TFlat rs :=
  if ZeroPeel.zpSize tf < cfg.maxFnSize then ZeroPeel.zpeelTF cfg tf else tf

/-- Apply `ZeroPeel` to a closed `Func` with explicit configuration `cfg`. Reifies once; falls back
unchanged if `wfCheck` fails or `zpSize tf ≥ cfg.maxFnSize`. -/
def Func.zeroPeelWith (cfg : ZeroPeelConfig := {}) {as rs : List Ty} (f : Func as rs) :
    Func as rs :=
  let tf := reifyFunc f
  if tf.wfCheck (pushTypes as []) [] && ZeroPeel.zpSize tf < cfg.maxFnSize then
    denoteFunc (ZeroPeel.zpeelTF cfg tf)
  else
    f

/-- Apply default `ZeroPeel` (`unrollN := 8`, `peelBudget := 36`, `peelImmOnly := true`,
`maxFnSize := 4000`) to a closed `Func`. -/
def Func.zeroPeel {as rs : List Ty} (f : Func as rs) (cfg : ZeroPeelConfig := {}) :
    Func as rs :=
  Func.zeroPeelWith cfg f

/-- Apply `ZeroPeel` to a named function `Fn`, preserving `name`, `as`, and `rs`. -/
def Fn.zeroPeel (fn : Fn) (cfg : ZeroPeelConfig := {}) : Fn :=
  ⟨fn.name, fn.as, fn.rs, Func.zeroPeel fn.body cfg⟩

end LeanQbe.T
