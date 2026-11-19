module

public import LeanQbe.T.IL
public import LeanQbe.T.Module

/-!
# Untrusted Stock-QBE `.ssa` Printer for `LeanQbe.T`

Prints single-return scalar integer `LeanQbe.T.Fn` and `LeanQbe.T.Module` programs to stock QBE
IL text (`.ssa`), mirroring `LeanQbe/Print.lean`'s QBE representation and `LeanQbe/T/PrintCpp.lean`'s
PHOAS traversal.

* Scalar representation: every `.bool` (`0`/`1`) and `.bits n` (`n ≤ 64`) value lives zero-extended
  in a 64-bit QBE temporary of class `l` (`%v{k}`). Parameters and calls use ABI type `l` (matching
  `LeanQbe/Print.lean` and the C harnesses in `test/*_main.c`), normalizing narrower widths cleanly.
* Join points: group labels allocate `@L{id}` and block-parameter temporaries `%L{id}_p{i}`. Jump
  sites assign `%L{id}_p{i} =l copy ...` first; block entries copy `%L{id}_p{i}` into fresh `%v{k}`
  temporaries so parallel swaps never clobber arguments.
* Control & exits: `jnz c` emits `%c{k} =w cnew {c}, 0` and fresh `@j{jt}`/`@j{je}` branch labels;
  `exit $f(args)` emits `call $f(args)` followed by `hlt`.
* Unsupported constructs (floating-point, pair/vector/SIMD, width `> 64`, `load`/`store` outside
  `.bool`/`i8`/`i16`/`i32`/`i64`, multi-result calls/returns, duplicate module symbols) return a
  descriptive `Except.error`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.PrintQbe

open LeanQbe.T

/-- PHOAS variable representation: QBE temporary name (always `%v{n}` or `%p{n}`). -/
abbrev SV : Ty → Type := fun _ => String

/-- PHOAS label representation: monotonic block ID and parameter-temporary names `%L{id}_p{i}`. -/
abbrev SL : List Ty → Type := fun ts => Nat × Tup SV ts

/-- A rendered basic block to be emitted after `@start`. -/
structure Block where
  id : Nat
  lines : Array String
  outJumps : Array Nat

/-- Mutable emitter state for a single function. -/
structure St where
  nv : Nat := 0
  nl : Nat := 0
  nj : Nat := 0
  blocks : Array Block := #[]
  curLines : Array String := #[]
  curJumps : Array Nat := #[]

/-- Printer monad threading `St` over `Except String`. -/
abbrev M := StateT St (Except String)

def liftE {α : Type} (e : Except String α) : M α :=
  StateT.lift e

def emit (s : String) : M Unit :=
  modify fun st => { st with curLines := st.curLines.push s }

def ins (s : String) : M Unit :=
  emit ("\t" ++ s)

def freshVar : M String :=
  modifyGet fun st => (s!"%v{st.nv}", { st with nv := st.nv + 1 })

def freshTmp (pfx : String) : M String :=
  modifyGet fun st => (s!"%{pfx}{st.nv}", { st with nv := st.nv + 1 })

def freshJ : M Nat :=
  modifyGet fun st => (st.nj, { st with nj := st.nj + 1 })

def lblName (id : Nat) : String := s!"@L{id}"

def blockParamName (lid idx : Nat) : String := s!"%L{lid}_p{idx}"

def recordJump (lid : Nat) : M Unit :=
  modify fun st =>
    if st.curJumps.contains lid then st else { st with curJumps := st.curJumps.push lid }

def checkSym (role : String) (s : Sym) : M Unit := do
  if s.isEmpty then
    throw s!"PrintQbe: empty {role} symbol name"
  if s.any (fun c => c.isWhitespace || c == ',' || c == '(' || c == ')') then
    throw s!"PrintQbe: invalid character in {role} symbol '{s}'"

/-- Validate a supported scalar type (`none` for `.bool`, `some n` for `.bits n` with `n ≤ 64`). -/
def scalarKind : Ty → Except String (Option Nat)
  | .bool => pure none
  | .bits n =>
    if n ≤ 64 then pure (some n)
    else throw s!"PrintQbe: bitwidth {n} > 64 is not supported by stock QBE"
  | .float _ => throw "PrintQbe: floating-point types are not supported"
  | .pair _ _ => throw "PrintQbe: pair/vector types are not supported"

def checkScalarTy (t : Ty) : Except String Unit := do
  let _ ← scalarKind t
  pure ()

def checkBits (n : Nat) : M Unit :=
  liftE (checkScalarTy (.bits n))

def tyWidth : Ty → Nat
  | .bool => 1
  | .bits n => n
  | _ => 0

def maskForWidth (n : Nat) : Nat :=
  if n == 0 then 0
  else if n ≥ 64 then 0xFFFFFFFFFFFFFFFF
  else (1 <<< n) - 1

def argStr : {t : Ty} → Arg SV t → String
  | _, .var v => v
  | .bool, .imm b => if b then "1" else "0"
  | .bits _, .imm v => toString v.toNat
  | .float _, .imm v => toString v.toNat
  | .pair _ _, .imm _ => "0"

def cmpOpName : CmpOp → String
  | .eq  => "eq"
  | .ne  => "ne"
  | .ult => "ult"
  | .ule => "ule"
  | .ugt => "ugt"
  | .uge => "uge"
  | .slt => "slt"
  | .sle => "sle"
  | .sgt => "sgt"
  | .sge => "sge"

/-- Signed comparisons on 1-bit `.bool` (`true = -1, false = 0`) inverted relative to `0`/`1`. -/
def boolCmpOpName : CmpOp → String
  | .slt => "ugt"
  | .sle => "uge"
  | .sgt => "ult"
  | .sge => "ule"
  | o    => cmpOpName o

/-- Emit `{dst} =l ...` containing `src` zero-extended from `n` bits (`0 ≤ n ≤ 64`). -/
def emitMask (dst src : String) (n : Nat) : M Unit := do
  match n with
  | 0  => ins s!"{dst} =l copy 0"
  | 8  => ins s!"{dst} =l extub {src}"
  | 16 => ins s!"{dst} =l extuh {src}"
  | 32 => ins s!"{dst} =l extuw {src}"
  | 64 => if dst != src then ins s!"{dst} =l copy {src}" else pure ()
  | _  => ins s!"{dst} =l and {src}, {maskForWidth n}"

/-- Emit `{dst} =l ...` containing `src` sign-extended from `m` bits (`0 ≤ m ≤ 64`) to 64 bits. -/
def emitSext64 (dst src : String) (m : Nat) : M Unit := do
  match m with
  | 0  => ins s!"{dst} =l copy 0"
  | 8  => ins s!"{dst} =l extsb {src}"
  | 16 => ins s!"{dst} =l extsh {src}"
  | 32 => ins s!"{dst} =l extsw {src}"
  | 64 => if dst != src then ins s!"{dst} =l copy {src}" else pure ()
  | _  =>
    let sh := 64 - m
    let t ← freshTmp "sx"
    ins s!"{t} =l shl {src}, {sh}"
    ins s!"{dst} =l sar {t}, {sh}"

/-- Emit a binary instruction on `bits n`, maintaining the zero-extended `l` invariant. -/
def emitBitsBin (op : String) (n : Nat) (dst a b : String) : M Unit := do
  if n == 0 then
    ins s!"{dst} =l copy 0"
  else if n == 64 then
    ins s!"{dst} =l {op} {a}, {b}"
  else if n == 32 then
    ins s!"{dst}_w =w {op} {a}, {b}"
    ins s!"{dst} =l extuw {dst}_w"
  else
    let t ← freshTmp "bw"
    ins s!"{t} =l {op} {a}, {b}"
    emitMask dst t n

/-- Emit bitwise 3-input ternary logic on `n` bits (`0 ≤ n ≤ 64`). -/
def emitTernlog (n : Nat) (imm : BitVec 8) (dst a b c : String) : M Unit := do
  if n == 0 then
    ins s!"{dst} =l copy 0"
    return
  let ones := maskForWidth n
  let na ← freshTmp "tlna"
  let nb ← freshTmp "tlnb"
  let nc ← freshTmp "tlnc"
  ins s!"{na} =l xor {a}, {ones}"
  ins s!"{nb} =l xor {b}, {ones}"
  ins s!"{nc} =l xor {c}, {ones}"
  let mut terms : Array String := #[]
  for k in List.range 8 do
    if imm.getLsbD k then
      let va := if k / 4 % 2 == 1 then a else na
      let vb := if k / 2 % 2 == 1 then b else nb
      let vc := if k % 2 == 1 then c else nc
      let t1 ← freshTmp "tl1"
      let t2 ← freshTmp "tl2"
      ins s!"{t1} =l and {va}, {vb}"
      ins s!"{t2} =l and {t1}, {vc}"
      terms := terms.push t2
  if terms.isEmpty then
    ins s!"{dst} =l copy 0"
  else
    let mut acc := terms[0]!
    for i in [1 : terms.size] do
      let next ← freshTmp "tla"
      ins s!"{next} =l or {acc}, {terms[i]!}"
      acc := next
    if dst != acc then
      ins s!"{dst} =l copy {acc}"

/-- Compute 64-bit unsigned double-width product `(lo, hi)` into pre-allocated temporaries. -/
def emitUmul64 (lo hi a b : String) : M Unit := do
  let a0 ← freshTmp "a0"
  let a1 ← freshTmp "a1"
  let b0 ← freshTmp "b0"
  let b1 ← freshTmp "b1"
  let p00 ← freshTmp "p00"
  let p01 ← freshTmp "p01"
  let p10 ← freshTmp "p10"
  let p11 ← freshTmp "p11"
  let p00h ← freshTmp "p00h"
  let p01l ← freshTmp "p01l"
  let p01h ← freshTmp "p01h"
  let p10l ← freshTmp "p10l"
  let p10h ← freshTmp "p10h"
  let t1 ← freshTmp "mt1"
  let t2 ← freshTmp "mt2"
  let t2h ← freshTmp "mt2h"
  let h1 ← freshTmp "mh1"
  let h2 ← freshTmp "mh2"
  ins s!"{lo} =l mul {a}, {b}"
  ins s!"{a0} =l extuw {a}"
  ins s!"{a1} =l shr {a}, 32"
  ins s!"{b0} =l extuw {b}"
  ins s!"{b1} =l shr {b}, 32"
  ins s!"{p00} =l mul {a0}, {b0}"
  ins s!"{p01} =l mul {a0}, {b1}"
  ins s!"{p10} =l mul {a1}, {b0}"
  ins s!"{p11} =l mul {a1}, {b1}"
  ins s!"{p00h} =l shr {p00}, 32"
  ins s!"{p01l} =l extuw {p01}"
  ins s!"{p01h} =l shr {p01}, 32"
  ins s!"{p10l} =l extuw {p10}"
  ins s!"{p10h} =l shr {p10}, 32"
  ins s!"{t1} =l add {p00h}, {p01l}"
  ins s!"{t2} =l add {t1}, {p10l}"
  ins s!"{t2h} =l shr {t2}, 32"
  ins s!"{h1} =l add {p11}, {p01h}"
  ins s!"{h2} =l add {h1}, {p10h}"
  ins s!"{hi} =l add {h2}, {t2h}"

/-- Compute `dst = if c != 0 then tval else fval`. -/
def emitSelect (dst c tval fval : String) : M Unit := do
  let jt ← freshJ
  let je ← freshJ
  let jk ← freshJ
  let cw ← freshTmp "sc"
  ins s!"{cw} =w cnew {c}, 0"
  ins s!"jnz {cw}, @j{jt}, @j{je}"
  emit s!"@j{jt}"
  ins s!"{dst} =l copy {tval}"
  ins s!"jmp @j{jk}"
  emit s!"@j{je}"
  ins s!"{dst} =l copy {fval}"
  ins s!"jmp @j{jk}"
  emit s!"@j{jk}"

/-- Normalize shift or rotate count `s` modulo `n` (`n ≥ 2`) in an `l` temporary (`0 ≤ sm < n`). -/
def emitShiftCount (n : Nat) (s : String) : M String := do
  let sm ← freshTmp "sm"
  if n == 2 || n == 4 || n == 8 || n == 16 || n == 32 || n == 64 then
    ins s!"{sm} =l and {s}, {n - 1}"
  else
    ins s!"{sm} =l urem {s}, {n}"
  pure sm

/-- Emit a logical shift (`shl` or `shr`) over scalar `.bool` / `.bits n`. -/
def emitShift (op : String) (k : Option Nat) (dst a s : String) : M Unit := do
  match k with
  | none | some 0 | some 1 => ins s!"{dst} =l copy {a}"
  | some n =>
    let sm ← emitShiftCount n s
    emitBitsBin op n dst a sm

/-- Emit a left (`isLeft = true`) or right (`isLeft = false`) rotate over scalar `.bool` / `.bits n`. -/
def emitRotate (isLeft : Bool) (k : Option Nat) (dst a s : String) : M Unit := do
  let fwdOp := if isLeft then "shl" else "shr"
  let revOp := if isLeft then "shr" else "shl"
  match k with
  | none | some 0 | some 1 => ins s!"{dst} =l copy {a}"
  | some n =>
    let sm ← emitShiftCount n s
    let ns0 ← freshTmp "rns0"
    ins s!"{ns0} =l sub {n}, {sm}"
    let ns ← if n == 32 || n == 64 then do
        let r ← freshTmp "rns"
        ins s!"{r} =l and {ns0}, {n - 1}"
        pure r
      else pure ns0
    let lo ← freshTmp "rlo"
    let hi ← freshTmp "rhi"
    if n == 64 then
      ins s!"{lo} =l {fwdOp} {a}, {sm}"
      ins s!"{hi} =l {revOp} {a}, {ns}"
      ins s!"{dst} =l or {lo}, {hi}"
    else if n == 32 then
      let r0 ← freshTmp "r0"
      ins s!"{lo} =w {fwdOp} {a}, {sm}"
      ins s!"{hi} =w {revOp} {a}, {ns}"
      ins s!"{r0} =w or {lo}, {hi}"
      ins s!"{dst} =l extuw {r0}"
    else
      let r0 ← freshTmp "r0"
      ins s!"{lo} =l {fwdOp} {a}, {sm}"
      ins s!"{hi} =l {revOp} {a}, {ns}"
      ins s!"{r0} =l or {lo}, {hi}"
      emitMask dst r0 n

/-- Emit a signed division or remainder (`div` or `rem`) at width `n` (`n ≤ 64`). -/
def emitSDivCore (op : String) (n : Nat) (dst a b : String) : M Unit := do
  if n == 0 then ins s!"{dst} =l copy 0"
  else if n == 64 then ins s!"{dst} =l {op} {a}, {b}"
  else if n == 32 then
    ins s!"{dst}_w =w {op} {a}, {b}"
    ins s!"{dst} =l extuw {dst}_w"
  else
    let ax ← freshTmp "ax"
    let bx ← freshTmp "bx"
    let t ← freshTmp "sd"
    emitSext64 ax a n
    emitSext64 bx b n
    ins s!"{t} =l {op} {ax}, {bx}"
    emitMask dst t n

/-- Emit a scalar operation into fresh `%v*` result temporaries. -/
def emitOp : {sig rs : List Ty} → OpCode sig rs → Tup (Arg SV) sig → M (Tup SV rs)
  | _, _, .copy t, (a, ()) => do
    liftE (checkScalarTy t)
    let v ← freshVar
    ins s!"{v} =l copy {argStr a}"
    pure (v, ())
  | _, _, .add t, (a, b, ()) => do
    let k ← liftE (scalarKind t)
    let v ← freshVar
    match k with
    | none => ins s!"{v} =l xor {argStr a}, {argStr b}"
    | some n => emitBitsBin "add" n v (argStr a) (argStr b)
    pure (v, ())
  | _, _, .sub t, (a, b, ()) => do
    let k ← liftE (scalarKind t)
    let v ← freshVar
    match k with
    | none => ins s!"{v} =l xor {argStr a}, {argStr b}"
    | some n => emitBitsBin "sub" n v (argStr a) (argStr b)
    pure (v, ())
  | _, _, .mul t, (a, b, ()) => do
    let k ← liftE (scalarKind t)
    let v ← freshVar
    match k with
    | none => ins s!"{v} =l and {argStr a}, {argStr b}"
    | some n => emitBitsBin "mul" n v (argStr a) (argStr b)
    pure (v, ())
  | _, _, .neg t, (a, ()) => do
    let k ← liftE (scalarKind t)
    let v ← freshVar
    match k with
    | none => ins s!"{v} =l copy {argStr a}"
    | some n => emitBitsBin "sub" n v "0" (argStr a)
    pure (v, ())
  | _, _, .and t, (a, b, ()) => do
    liftE (checkScalarTy t)
    let v ← freshVar
    ins s!"{v} =l and {argStr a}, {argStr b}"
    pure (v, ())
  | _, _, .or t, (a, b, ()) => do
    liftE (checkScalarTy t)
    let v ← freshVar
    ins s!"{v} =l or {argStr a}, {argStr b}"
    pure (v, ())
  | _, _, .xor t, (a, b, ()) => do
    liftE (checkScalarTy t)
    let v ← freshVar
    ins s!"{v} =l xor {argStr a}, {argStr b}"
    pure (v, ())
  | _, _, .not t, (a, ()) => do
    let k ← liftE (scalarKind t)
    let v ← freshVar
    match k with
    | none => ins s!"{v} =l xor {argStr a}, 1"
    | some n => emitBitsBin "xor" n v (argStr a) "-1"
    pure (v, ())
  | _, _, .ternlog t imm, (a, b, c, ()) => do
    liftE (checkScalarTy t)
    let v ← freshVar
    emitTernlog (tyWidth t) imm v (argStr a) (argStr b) (argStr c)
    pure (v, ())
  | _, _, .shl t, (a, s, ()) => do
    let k ← liftE (scalarKind t)
    let v ← freshVar
    emitShift "shl" k v (argStr a) (argStr s)
    pure (v, ())
  | _, _, .lshr t, (a, s, ()) => do
    let k ← liftE (scalarKind t)
    let v ← freshVar
    emitShift "shr" k v (argStr a) (argStr s)
    pure (v, ())
  | _, _, .ashr t, (a, s, ()) => do
    let k ← liftE (scalarKind t)
    let v ← freshVar
    match k with
    | none | some 0 | some 1 => ins s!"{v} =l copy {argStr a}"
    | some n =>
      let sm ← emitShiftCount n (argStr s)
      if n == 64 then
        ins s!"{v} =l sar {argStr a}, {sm}"
      else if n == 32 then
        ins s!"{v}_w =w sar {argStr a}, {sm}"
        ins s!"{v} =l extuw {v}_w"
      else
        let ax ← freshTmp "ax"
        let t0 ← freshTmp "sr"
        emitSext64 ax (argStr a) n
        ins s!"{t0} =l sar {ax}, {sm}"
        emitMask v t0 n
    pure (v, ())
  | _, _, .rotl t, (a, s, ()) => do
    let k ← liftE (scalarKind t)
    let v ← freshVar
    emitRotate true k v (argStr a) (argStr s)
    pure (v, ())
  | _, _, .rotr t, (a, s, ()) => do
    let k ← liftE (scalarKind t)
    let v ← freshVar
    emitRotate false k v (argStr a) (argStr s)
    pure (v, ())
  | _, _, .cmp o t _ _, (a, b, ()) => do
    let k ← liftE (scalarKind t)
    let v ← freshVar
    match k with
    | none =>
      ins s!"{v} =l c{boolCmpOpName o}l {argStr a}, {argStr b}"
    | some 0 =>
      let r := match o with
        | .eq | .ule | .uge | .sle | .sge => "1"
        | _ => "0"
      ins s!"{v} =l copy {r}"
    | some 64 =>
      ins s!"{v} =l c{cmpOpName o}l {argStr a}, {argStr b}"
    | some 32 =>
      ins s!"{v} =l c{cmpOpName o}w {argStr a}, {argStr b}"
    | some n =>
      match o with
      | .slt | .sle | .sgt | .sge =>
        let ax ← freshTmp "cx"
        let bx ← freshTmp "cy"
        emitSext64 ax (argStr a) n
        emitSext64 bx (argStr b) n
        ins s!"{v} =l c{cmpOpName o}l {ax}, {bx}"
      | _ =>
        ins s!"{v} =l c{cmpOpName o}l {argStr a}, {argStr b}"
    pure (v, ())
  | _, _, .select t, (c, a, b, ()) => do
    liftE (checkScalarTy t)
    let v ← freshVar
    emitSelect v (argStr c) (argStr a) (argStr b)
    pure (v, ())
  | _, _, .zext m n, (a, ()) => do
    checkBits m
    checkBits n
    if m > n then throw s!"PrintQbe: invalid zext width {m} > {n}"
    let v ← freshVar
    emitMask v (argStr a) m
    pure (v, ())
  | _, _, .sext m n, (a, ()) => do
    checkBits m
    checkBits n
    if m > n then throw s!"PrintQbe: invalid sext width {m} > {n}"
    let v ← freshVar
    let sx ← freshTmp "sx"
    emitSext64 sx (argStr a) m
    emitMask v sx n
    pure (v, ())
  | _, _, .trunc m n, (a, ()) => do
    checkBits m
    checkBits n
    if n > m then throw s!"PrintQbe: invalid trunc width {n} > {m}"
    let v ← freshVar
    emitMask v (argStr a) n
    pure (v, ())
  | _, _, .ofBool n, (c, ()) => do
    checkBits n
    let v ← freshVar
    if n == 0 then
      ins s!"{v} =l copy 0"
    else
      ins s!"{v} =l copy {argStr c}"
    pure (v, ())
  | _, _, .addc n, (a, b, cin, ()) => do
    checkBits n
    let s ← freshVar
    let c ← freshVar
    if n == 0 then
      ins s!"{s} =l copy 0"
      ins s!"{c} =l copy {argStr cin}"
    else if n < 64 then
      let t1 ← freshTmp "ac1"
      let t2 ← freshTmp "ac2"
      ins s!"{t1} =l add {argStr a}, {argStr b}"
      ins s!"{t2} =l add {t1}, {argStr cin}"
      emitMask s t2 n
      ins s!"{c} =l shr {t2}, {n}"
    else
      let ab ← freshTmp "acab"
      let c1 ← freshTmp "acc1"
      let c2 ← freshTmp "acc2"
      ins s!"{ab} =l add {argStr a}, {argStr b}"
      ins s!"{c1} =l cultl {ab}, {argStr a}"
      ins s!"{s} =l add {ab}, {argStr cin}"
      ins s!"{c2} =l cultl {s}, {ab}"
      ins s!"{c} =l or {c1}, {c2}"
    pure (s, c, ())
  | _, _, .subb n, (a, b, cin, ()) => do
    checkBits n
    let d ← freshVar
    let bout ← freshVar
    if n == 0 then
      ins s!"{d} =l copy 0"
      ins s!"{bout} =l copy {argStr cin}"
    else
      let b1 ← freshTmp "sbb1"
      let ab ← freshTmp "sbab"
      let abm ← freshTmp "sbam"
      let b2 ← freshTmp "sbb2"
      let dr ← freshTmp "sbdr"
      ins s!"{b1} =l cultl {argStr a}, {argStr b}"
      ins s!"{ab} =l sub {argStr a}, {argStr b}"
      emitMask abm ab n
      ins s!"{b2} =l cultl {abm}, {argStr cin}"
      ins s!"{dr} =l sub {abm}, {argStr cin}"
      emitMask d dr n
      ins s!"{bout} =l or {b1}, {b2}"
    pure (d, bout, ())
  | _, _, .umulw n, (a, b, ()) => do
    checkBits n
    let lo ← freshVar
    let hi ← freshVar
    if n == 0 then
      ins s!"{lo} =l copy 0"
      ins s!"{hi} =l copy 0"
    else if n ≤ 32 then
      let p ← freshTmp "um"
      let hr ← freshTmp "umh"
      ins s!"{p} =l mul {argStr a}, {argStr b}"
      emitMask lo p n
      ins s!"{hr} =l shr {p}, {n}"
      emitMask hi hr n
    else if n == 64 then
      emitUmul64 lo hi (argStr a) (argStr b)
    else
      let lo128 ← freshTmp "mlo"
      let hi128 ← freshTmp "mhi"
      let sh1 ← freshTmp "msh1"
      let sh2 ← freshTmp "msh2"
      let hr ← freshTmp "mhr"
      emitUmul64 lo128 hi128 (argStr a) (argStr b)
      emitMask lo lo128 n
      ins s!"{sh1} =l shr {lo128}, {n}"
      ins s!"{sh2} =l shl {hi128}, {64 - n}"
      ins s!"{hr} =l or {sh1}, {sh2}"
      emitMask hi hr n
    pure (lo, hi, ())
  | _, _, .smulw n, (a, b, ()) => do
    checkBits n
    let lo ← freshVar
    let hi ← freshVar
    if n == 0 then
      ins s!"{lo} =l copy 0"
      ins s!"{hi} =l copy 0"
    else if n ≤ 32 then
      let ax ← freshTmp "sa"
      let bx ← freshTmp "sb"
      let p ← freshTmp "sp"
      let hr ← freshTmp "shr"
      emitSext64 ax (argStr a) n
      emitSext64 bx (argStr b) n
      ins s!"{p} =l mul {ax}, {bx}"
      emitMask lo p n
      ins s!"{hr} =l sar {p}, {n}"
      emitMask hi hr n
    else
      let ax ← freshTmp "sa"
      let bx ← freshTmp "sb"
      let lo128 ← freshTmp "mlo"
      let uhi ← freshTmp "muh"
      let sa ← freshTmp "msa"
      let sb ← freshTmp "msb"
      let subA ← freshTmp "msuba"
      let subB ← freshTmp "msubb"
      let hi1 ← freshTmp "mh1"
      let hi64 ← freshTmp "mh64"
      emitSext64 ax (argStr a) n
      emitSext64 bx (argStr b) n
      emitUmul64 lo128 uhi ax bx
      ins s!"{sa} =l csltl {ax}, 0"
      ins s!"{sb} =l csltl {bx}, 0"
      emitSelect subA sa bx "0"
      emitSelect subB sb ax "0"
      ins s!"{hi1} =l sub {uhi}, {subA}"
      ins s!"{hi64} =l sub {hi1}, {subB}"
      if n == 64 then
        ins s!"{lo} =l copy {lo128}"
        ins s!"{hi} =l copy {hi64}"
      else
        let sh1 ← freshTmp "msh1"
        let sh2 ← freshTmp "msh2"
        let hr ← freshTmp "mhr"
        emitMask lo lo128 n
        ins s!"{sh1} =l shr {lo128}, {n}"
        ins s!"{sh2} =l shl {hi64}, {64 - n}"
        ins s!"{hr} =l or {sh1}, {sh2}"
        emitMask hi hr n
    pure (lo, hi, ())
  | _, _, .udiv n, (a, b, ()) => do
    checkBits n
    let v ← freshVar
    emitBitsBin "udiv" n v (argStr a) (argStr b)
    pure (v, ())
  | _, _, .urem n, (a, b, ()) => do
    checkBits n
    let v ← freshVar
    emitBitsBin "urem" n v (argStr a) (argStr b)
    pure (v, ())
  | _, _, .sdiv n, (a, b, ()) => do
    checkBits n
    let v ← freshVar
    emitSDivCore "div" n v (argStr a) (argStr b)
    pure (v, ())
  | _, _, .srem n, (a, b, ()) => do
    checkBits n
    let v ← freshVar
    emitSDivCore "rem" n v (argStr a) (argStr b)
    pure (v, ())
  | _, _, .udiv0 n, (a, b, ()) => do
    checkBits n
    let v ← freshVar
    if n == 0 then
      ins s!"{v} =l copy 0"
    else
      let jt ← freshJ
      let je ← freshJ
      let jk ← freshJ
      let nz ← freshTmp "dnz"
      ins s!"{nz} =l cnel {argStr b}, 0"
      ins s!"jnz {nz}, @j{jt}, @j{je}"
      emit s!"@j{jt}"
      emitBitsBin "udiv" n v (argStr a) (argStr b)
      ins s!"jmp @j{jk}"
      emit s!"@j{je}"
      ins s!"{v} =l copy 0"
      ins s!"jmp @j{jk}"
      emit s!"@j{jk}"
    pure (v, ())
  | _, _, .sdiv0 n, (a, b, ()) => do
    checkBits n
    let v ← freshVar
    if n == 0 then
      ins s!"{v} =l copy 0"
    else
      let intMin : Nat := 1 <<< (n - 1)
      let allOnes : Nat := maskForWidth n
      let jt ← freshJ
      let jz ← freshJ
      let jov ← freshJ
      let jdo ← freshJ
      let jk ← freshJ
      let nz ← freshTmp "snz"
      let isMin ← freshTmp "smin"
      let isM1 ← freshTmp "sm1"
      let isOv ← freshTmp "sov"
      ins s!"{nz} =l cnel {argStr b}, 0"
      ins s!"jnz {nz}, @j{jt}, @j{jz}"
      emit s!"@j{jz}"
      ins s!"{v} =l copy 0"
      ins s!"jmp @j{jk}"
      emit s!"@j{jt}"
      ins s!"{isMin} =l ceql {argStr a}, {intMin}"
      ins s!"{isM1} =l ceql {argStr b}, {allOnes}"
      ins s!"{isOv} =l and {isMin}, {isM1}"
      ins s!"jnz {isOv}, @j{jov}, @j{jdo}"
      emit s!"@j{jov}"
      ins s!"{v} =l copy {intMin}"
      ins s!"jmp @j{jk}"
      emit s!"@j{jdo}"
      emitSDivCore "div" n v (argStr a) (argStr b)
      ins s!"jmp @j{jk}"
      emit s!"@j{jk}"
    pure (v, ())
  | _, _, .bitcast t u _, (a, ()) => do
    liftE (checkScalarTy t)
    liftE (checkScalarTy u)
    let v ← freshVar
    ins s!"{v} =l copy {argStr a}"
    pure (v, ())
  | _, _, .fshl _, _ => throw "PrintQbe: opcode fshl is not supported"
  | _, _, .fshr _, _ => throw "PrintQbe: opcode fshr is not supported"
  | _, _, .bswap _, _ => throw "PrintQbe: opcode bswap is not supported"
  | _, _, .clz _, _ => throw "PrintQbe: opcode clz is not supported"
  | _, _, .cls _, _ => throw "PrintQbe: opcode cls is not supported"
  | _, _, .rbit _, _ => throw "PrintQbe: opcode rbit is not supported"
  | _, _, .ctz _, _ => throw "PrintQbe: opcode ctz is not supported"
  | _, _, .popcnt _, _ => throw "PrintQbe: opcode popcnt is not supported"
  | _, _, .blend _ _ _, _ => throw "PrintQbe: vector opcode blend is not supported"
  | _, _, .mkpair _ _, _ => throw "PrintQbe: pair/vector opcode mkpair is not supported"
  | _, _, .unpair _ _, _ => throw "PrintQbe: pair/vector opcode unpair is not supported"
  | _, _, .shufd _ _, _ => throw "PrintQbe: vector opcode shufd is not supported"
  | _, _, .shufb _, _ => throw "PrintQbe: vector opcode shufb is not supported"
  | _, _, .alignr _ _, _ => throw "PrintQbe: vector opcode alignr is not supported"
  | _, _, .blendw _ _, _ => throw "PrintQbe: vector opcode blendw is not supported"
  | _, _, .sha256rnds2, _ => throw "PrintQbe: vector opcode sha256rnds2 is not supported"
  | _, _, .sha256msg1, _ => throw "PrintQbe: vector opcode sha256msg1 is not supported"
  | _, _, .sha256msg2, _ => throw "PrintQbe: vector opcode sha256msg2 is not supported"
  | _, _, .fadd _, _ => throw "PrintQbe: float opcode fadd is not supported"
  | _, _, .fsub _, _ => throw "PrintQbe: float opcode fsub is not supported"
  | _, _, .fmul _, _ => throw "PrintQbe: float opcode fmul is not supported"
  | _, _, .fdiv _, _ => throw "PrintQbe: float opcode fdiv is not supported"
  | _, _, .ffma _, _ => throw "PrintQbe: float opcode ffma is not supported"
  | _, _, .fsqrt _, _ => throw "PrintQbe: float opcode fsqrt is not supported"
  | _, _, .fneg _, _ => throw "PrintQbe: float opcode fneg is not supported"
  | _, _, .fabs _, _ => throw "PrintQbe: float opcode fabs is not supported"
  | _, _, .fcmp _ _ _ _, _ => throw "PrintQbe: float opcode fcmp is not supported"
  | _, _, .fptoui _ _, _ => throw "PrintQbe: float opcode fptoui is not supported"
  | _, _, .fptosi _ _, _ => throw "PrintQbe: float opcode fptosi is not supported"
  | _, _, .uitofp _ _, _ => throw "PrintQbe: float opcode uitofp is not supported"
  | _, _, .sitofp _ _, _ => throw "PrintQbe: float opcode sitofp is not supported"
  | _, _, .fcvt _ _, _ => throw "PrintQbe: float opcode fcvt is not supported"

def loadInstr : Ty → Except String String
  | .bool => pure "loadub"
  | .bits 8 => pure "loadub"
  | .bits 16 => pure "loaduh"
  | .bits 32 => pure "loaduw"
  | .bits 64 => pure "loadl"
  | t => throw s!"PrintQbe: unsupported load type (expected bool/i8/i16/i32/i64), got {repr t}"

def storeInstr : Ty → Except String String
  | .bool => pure "storeb"
  | .bits 8 => pure "storeb"
  | .bits 16 => pure "storeh"
  | .bits 32 => pure "storew"
  | .bits 64 => pure "storel"
  | t => throw s!"PrintQbe: unsupported store type (expected bool/i8/i16/i32/i64), got {repr t}"

def formatCallArgs : {as : List Ty} → Tup (Arg SV) as → M (List String)
  | [], _ => pure []
  | t :: _, (a, as) => do
    liftE (checkScalarTy t)
    let rest ← formatCallArgs as
    pure (s!"l {argStr a}" :: rest)

def emitCall (f : Sym) {as : List Ty} : (bs : List Ty) → Tup (Arg SV) as → M (Tup SV bs)
  | [], args => do
    checkSym "call" f
    let argList ← formatCallArgs args
    ins s!"call ${f}({", ".intercalate argList})"
    pure ()
  | [bt], args => do
    checkSym "call" f
    liftE (checkScalarTy bt)
    let argList ← formatCallArgs args
    let argStrList := ", ".intercalate argList
    let v ← freshVar
    if bt == .bits 64 then
      ins s!"{v} =l call ${f}({argStrList})"
    else
      ins s!"{v}_raw =l call ${f}({argStrList})"
      emitMask v s!"{v}_raw" (tyWidth bt)
    pure (v, ())
  | bs@(_ :: _ :: _), _ =>
    throw s!"PrintQbe: call ${f} returns {bs.length} values; stock QBE supports at most 1"

def emitJumpArgs : {ts : List Ty} → Tup SV ts → Tup (Arg SV) ts → M Unit
  | [], _, _ => pure ()
  | t :: _, (p, ps), (a, as) => do
    liftE (checkScalarTy t)
    ins s!"{p} =l copy {argStr a}"
    emitJumpArgs ps as

def allocBlockParams (lid : Nat) : (idx : Nat) → (ts : List Ty) → M (Tup SV ts)
  | _, [] => pure ()
  | idx, t :: ts => do
    liftE (checkScalarTy t)
    let rest ← allocBlockParams lid (idx + 1) ts
    pure (blockParamName lid idx, rest)

def freshLabel (ts : List Ty) : M (SL ts) := do
  let lid ← modifyGet fun st => (st.nl, { st with nl := st.nl + 1 })
  let ps ← allocBlockParams lid 0 ts
  pure (lid, ps)

def allocLabels : (sig : List (List Ty)) → M (Tup SL sig)
  | [] => pure ()
  | ts :: sig => do
    let l ← freshLabel ts
    let ls ← allocLabels sig
    pure (l, ls)

def bindBlockParams : {ts : List Ty} → Tup SV ts → M (Tup SV ts)
  | [], () => pure ()
  | _ :: _, (p, ps) => do
    let v ← freshVar
    ins s!"{v} =l copy {p}"
    let vs ← bindBlockParams ps
    pure (v, vs)

def formatRet : {rs : List Ty} → Tup (Arg SV) rs → M String
  | [], _ => pure "ret"
  | [t], (a, _) => do
    liftE (checkScalarTy t)
    pure s!"ret {argStr a}"
  | _ :: _ :: _, _ => throw "PrintQbe: ret with >1 value is not supported by stock QBE"

mutual
  def goExpr {rs : List Ty} : Expr SV SL rs → M Unit
    | .let_ op k => do
      let outs ← emitOp op.code op.args
      goExpr (k outs)
    | .load t a k => do
      let op ← liftE (loadInstr t)
      let v ← freshVar
      ins s!"{v} =l {op} {argStr a}"
      goExpr (k v)
    | .store (t := t) v a k => do
      let op ← liftE (storeInstr t)
      ins s!"{op} {argStr v}, {argStr a}"
      goExpr k
    | .call f (bs := bs) args k => do
      let outs ← emitCall f bs args
      goExpr (k outs)
    | .jnz c t e => do
      let jt ← freshJ
      let je ← freshJ
      ins s!"%c{jt} =w cnew {argStr c}, 0"
      ins s!"jnz %c{jt}, @j{jt}, @j{je}"
      emit s!"@j{jt}"
      goExpr t
      emit s!"@j{je}"
      goExpr e
    | .jump j args => do
      recordJump j.1
      emitJumpArgs j.2 args
      ins s!"jmp {lblName j.1}"
    | .ret vs => do
      let s ← formatRet vs
      ins s
    | .exit f args => do
      checkSym "exit" f
      let argList ← formatCallArgs args
      ins s!"call ${f}({", ".intercalate argList})"
      ins "hlt"
    | .hlt => ins "hlt"
    | .group bodies k => do
      let ls ← allocLabels _
      goExpr (k ls)
      goBlocks ls (bodies ls)

  def goBlocks {rs : List Ty} : {sig : List (List Ty)} → Tup SL sig →
      Blocks SV SL rs sig → M Unit
    | [], _, .nil => pure ()
    | _ :: _, (l, ls), .cons b bs => do
      let st ← get
      let savedLines := st.curLines
      let savedJumps := st.curJumps
      set { st with curLines := #[lblName l.1], curJumps := #[] }
      let xs ← bindBlockParams l.2
      goExpr (b xs)
      let st' ← get
      let blk : Block := { id := l.1, lines := st'.curLines, outJumps := st'.curJumps }
      set { st' with
        curLines := savedLines
        curJumps := savedJumps
        blocks := st'.blocks.push blk }
      goBlocks ls bs
end

def buildEntryParams : (idx : Nat) → (ts : List Ty) → M (Tup SV ts × List String)
  | _, [] => pure ((), [])
  | idx, t :: ts => do
    liftE (checkScalarTy t)
    let pname := s!"%p{idx}"
    let rawName := if t == .bits 64 then pname else s!"%p{idx}_raw"
    if t != .bits 64 then
      emitMask pname rawName (tyWidth t)
    let (restVars, restDecls) ← buildEntryParams (idx + 1) ts
    pure ((pname, restVars), s!"l {rawName}" :: restDecls)

def reachableBlockIds (blocks : Array Block) (seeds : Array Nat) : Array Nat := Id.run do
  let mut visited : Array Nat := #[]
  let mut queue : List Nat := seeds.toList
  while !queue.isEmpty do
    match queue with
    | [] => pure ()
    | id :: rest =>
      queue := rest
      if !visited.contains id then
        visited := visited.push id
        if let some blk := blocks.find? (fun b => b.id == id) then
          for dst in blk.outJumps do
            if !visited.contains dst then
              queue := dst :: queue
  pure visited

/-- Print one `LeanQbe.T.Fn` to exported stock QBE IL text (`.ssa`). -/
def fn (f : Fn) : Except String String := do
  if f.rs.length > 1 then
    throw s!"PrintQbe: function ${f.name} returns {f.rs.length} values; stock QBE supports at most 1"
  match f.rs with
  | [rt] => checkScalarTy rt
  | _ => pure ()
  let action : M (List String) := do
    checkSym "function" f.name
    let (entryVars, paramDecls) ← buildEntryParams 0 f.as
    goExpr (f.body SV SL entryVars)
    pure paramDecls
  let (paramDecls, st) ← action.run { curLines := #["@start"] }
  let liveIds := reachableBlockIds st.blocks st.curJumps
  let liveBlocks := (st.blocks.toList.filter fun b => liveIds.contains b.id).mergeSort
    (fun a b => a.id ≤ b.id)
  let allLines := st.curLines.toList ++ (liveBlocks.flatMap fun b => b.lines.toList)
  let retStr := if f.rs.isEmpty then "" else "l "
  let paramStr := ", ".intercalate paramDecls
  pure (s!"export function {retStr}${f.name}({paramStr}) \{\n" ++ "\n".intercalate allLines ++ "\n}\n")

/-- Print a list of functions to stock QBE IL text (`.ssa`), rejecting duplicate function names. -/
def fns (fs : List Fn) : Except String String := do
  let mut seen : List Sym := []
  for f in fs do
    if seen.contains f.name then
      throw s!"PrintQbe: duplicate function symbol '{f.name}'"
    seen := f.name :: seen
  let parts ← fs.mapM fn
  pure ("\n".intercalate parts)

/-- Print a `LeanQbe.T.Module` to stock QBE IL text (`.ssa`), checking symbol uniqueness across
functions and externs. -/
def module (m : Module) : Except String String := do
  let mut seen : List Sym := []
  for name in m.names do
    if seen.contains name then
      throw s!"PrintQbe: duplicate symbol '{name}' in module"
    seen := name :: seen
  let parts ← m.fns.mapM fn
  pure ("\n".intercalate parts)

end LeanQbe.T.PrintQbe

end
