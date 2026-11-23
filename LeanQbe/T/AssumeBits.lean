module

public import LeanQbe.T.OptUtil

/-!
# Known-bits and branch-implied `AssumeBits` pass

PHOAS-to-PHOAS optimisation pass `assumeBits : Nat → List BitFact → Expr (ABVal V) L rs →
Expr V L rs` where every variable carries its replacement operand `out : Arg V t` and
`V`-independent known-bits metadata `info : ABInfo`:
* `id`: a fresh lexical identity (so `.jnz` arms can attach facts to already-bound variables);
* `kz`: a known-zero mask (every bit set in `kz` is `0` in the value), seeded by immediates,
  `zext`, `and` with an immediate, `lshr`/`shl` by an immediate, `trunc`, `ofBool`, and propagated
  through `and`/`or`/`xor`/`select`;
* `zf` / `nf`: bit facts `(id, mask)` implied when the value is zero / nonzero (`false` / `true`
  for `.bool`), seeded by `x &&& c` (`x &&& c = 0` clears the bits `c` of `x`) and lifted through
  `x == 0`, `x != 0`, `x <s 0`, `x >=s 0`, `x <u c`, `x >=u c`, and `!c`.

At `.jnz c t e`, the facts `c.nf` hold in `t` and `c.zf` hold in `e`; facts are scoped lexically
(`List BitFact`), so they flow into every dominated `let_`, nested `.jnz`, and `group` body.

Rewrites (`abElim?`):
* `and x c → x` when every bit cleared by `c` is known zero in `x` (e.g. `x &&& 0x7fffffff` on the
  arm where `(x &&& 0x80000000) == 0`);
* `and x c → 0` when every bit kept by `c` is known zero in `x`;
* `copy x → x`.

Correctness (`LeanQbe/T/AssumeBitsLemmas.lean`): `assumeBits_wp`, `assumeBits_wf`,
`assumeBits_callsOk`, `Func.assumeBits_spec`, `Func.assumeBits_wf`, `Func.assumeBits_callsOk`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-- Bit fact `(id, mask)`: every bit set in `mask` is `0` in the `.bits` value bound with lexical
identity `id`. -/
abbrev BitFact : Type := Nat × Nat

/-- `V`-independent known-bits metadata of a value. -/
structure ABInfo : Type where
  /-- Fresh lexical identity of the bound variable (`none` for immediates). -/
  id : Option Nat := none
  /-- Known-zero mask: every bit set in `kz` is `0` in the value. -/
  kz : Nat := 0
  /-- Facts implied when the value is zero (`false` for `.bool`, `0#n` for `.bits n`). -/
  zf : List BitFact := []
  /-- Facts implied when the value is nonzero (`true` for `.bool`, `≠ 0#n` for `.bits n`). -/
  nf : List BitFact := []

/-- Input value representation of `assumeBits`: replacement operand and known-bits metadata. -/
structure ABVal (V : Ty → Type) (t : Ty) : Type where
  out : Arg V t
  info : ABInfo

/-- Known-zero mask of an immediate (the complement of a `.bits n` constant). -/
def immKz : (t : Ty) → Val t → Nat
  | .bits n, c => (2 ^ n - 1) ^^^ BitVec.toNat c
  | _, _ => 0

/-- Metadata of an immediate operand. -/
def ABInfo.ofImm (t : Ty) (c : Val t) : ABInfo := { kz := immKz t c }

/-- Fresh variable `ABVal` with lexical identity `next` and no known bits. -/
def ABVal.fresh {V : Ty → Type} {t : Ty} (v : V t) (next : Nat) : ABVal V t :=
  ⟨.var v, { id := some next }⟩

/-- Wrap bound output variables `xs : Tup V ts` into fresh `ABVal V`s starting at `next`. -/
abbrev freshABVals {V : Ty → Type} : (ts : List Ty) → Tup V ts → Nat → Tup (ABVal V) ts :=
  tupFreshWith fun x next => ABVal.fresh x next

/-- Metadata of an input operand. -/
def Arg.abInfo {V : Ty → Type} {t : Ty} : Arg (ABVal V) t → ABInfo
  | .var a => a.info
  | .imm c => ABInfo.ofImm t c

/-- Output operand of an input operand. -/
def Arg.abOut {V : Ty → Type} {t : Ty} : Arg (ABVal V) t → Arg V t
  | .var a => a.out
  | .imm c => .imm c

/-- Promote an input operand to an `ABVal`. -/
def Arg.toAB {V : Ty → Type} {t : Ty} : Arg (ABVal V) t → ABVal V t
  | .var a => a
  | .imm c => ⟨.imm c, ABInfo.ofImm t c⟩

/-- Map `Arg.abOut` across a tuple of operands. -/
abbrev tupAOut {V : Ty → Type} : {ts : List Ty} → Tup (Arg (ABVal V)) ts → Tup (Arg V) ts :=
  tupMapArg fun _ => Arg.abOut

/-! ## Facts, masks, and `V`-independent operand shapes -/

/-- Union of the masks of every fact on identity `i`. -/
def factMask (i : Nat) : List BitFact → Nat
  | [] => 0
  | f :: F => if f.1 == i then f.2 ||| factMask i F else factMask i F

/-- Known-zero mask of `a` strengthened by the in-scope facts `F` on its identity. -/
def ABInfo.kzIn (F : List BitFact) (a : ABInfo) : Nat :=
  match a.id with
  | some i => a.kz ||| factMask i F
  | none => a.kz

/-- `V`-independent shape of an operand: metadata and immediate value (if any). -/
abbrev ABShape (t : Ty) : Type := ABInfo × Option (Val t)

/-- Shape of an input operand. -/
def Arg.abShape {V : Ty → Type} {t : Ty} (a : Arg (ABVal V) t) : ABShape t :=
  (a.abInfo, a.abOut.imm?)

/-- Shapes of a tuple of input operands. -/
abbrev tupABShape {V : Ty → Type} {ts : List Ty} (args : Tup (Arg (ABVal V)) ts) :
    Tup ABShape ts :=
  args.map fun _ a => a.abShape

/-- Single fact `(id, m)` on the identity of shape `s` (none for immediates). -/
def ABShape.fact {t : Ty} (s : ABShape t) (m : Nat) : List BitFact :=
  match s.1.id with
  | some i => [(i, m)]
  | none => []

/-- Mask with bits `[k, n)` set. -/
def highFrom (n k : Nat) : Nat := (2 ^ (n - k) - 1) <<< k

/-- Sign bit of an `n`-bit value. -/
def signBit (n : Nat) : Nat := 2 ^ (n - 1)

/-- Number of low bits needed by every value strictly below `c`. -/
def ltBits (c : Nat) : Nat := (c - 1).log2 + 1

/-- `x &&& c = x` whenever every bit cleared by `c` is known zero (`kz`). -/
def andKeeps (n kz : Nat) (c : BitVec n) : Bool :=
  ((2 ^ n - 1) ^^^ c.toNat) &&& kz == (2 ^ n - 1) ^^^ c.toNat

/-- `x &&& c = 0` whenever every bit kept by `c` is known zero (`kz`). -/
def andKills (kz : Nat) {n : Nat} (c : BitVec n) : Bool :=
  c.toNat &&& kz == c.toNat

/-! ## Elimination and result metadata (both `V`-independent) -/

/-- Replacement of an eliminated result: an operand of the operation or a constant. -/
inductive ABElim (sig : List Ty) (t : Ty) : Type
  | arg (i : Member t sig)
  | imm (c : Val t)

/-- Elimination of `x &&& c` / `c &&& x` against the known-zero mask `kz` of `x`. -/
def andElim? (n kz : Nat) (c : BitVec n) (i : Member (Ty.bits n) [Ty.bits n, Ty.bits n]) :
    Option (Tup (fun u => ABElim [Ty.bits n, Ty.bits n] u) [Ty.bits n]) :=
  if andKeeps n kz c then some (.arg i, ())
  else if andKills kz c then some (.imm 0#n, ())
  else none

/-- Decide whether an operation is eliminated (`copy x → x`, redundant or annihilated `and`). -/
def abElim? : {sig ts : List Ty} → OpCode sig ts → Tup ABShape sig → List BitFact →
    Option (Tup (fun u => ABElim sig u) ts)
  | _, _, .copy _, _, _ => some (.arg .here, ())
  | _, _, .and (.bits n), (sa, sb, ()), F =>
    match sb.2, sa.2 with
    | some c, _ => andElim? n (sa.1.kzIn F) c .here
    | none, some c => andElim? n (sb.1.kzIn F) c (.there .here)
    | none, none => none
  | _, _, _, _, _ => none

/-- Metadata (except identity) of the first result of an emitted operation. -/
structure ABRes : Type where
  kz : Nat := 0
  zf : List BitFact := []
  nf : List BitFact := []

/-- Result metadata of a scalar `.bits n` comparison `a o b`. -/
def cmpRes (o : CmpOp) (n : Nat) (sa sb : ABShape (.bits n)) : ABRes :=
  match o, sb.2 with
  | .ne, some c => if c == 0#n then { zf := sa.1.zf, nf := sa.1.nf } else {}
  | .eq, some c => if c == 0#n then { zf := sa.1.nf, nf := sa.1.zf } else {}
  | .slt, some c => if c == 0#n then { zf := sa.fact (signBit n) } else {}
  | .sge, some c => if c == 0#n then { nf := sa.fact (signBit n) } else {}
  | .ult, some c => { nf := sa.fact (highFrom n (ltBits c.toNat)) }
  | .uge, some c => { zf := sa.fact (highFrom n (ltBits c.toNat)) }
  | _, _ => {}

/-- Result metadata of `and t a b`. -/
def andRes : (t : Ty) → ABShape t → ABShape t → List BitFact → ABRes
  | .bits _, sa, sb, F =>
    { kz := sa.1.kzIn F ||| sb.1.kzIn F
      zf := match sb.2, sa.2 with
        | some c, _ => sa.fact c.toNat
        | none, some c => sb.fact c.toNat
        | none, none => [] }
  | _, _, _, _ => {}

/-- Result metadata of `or t a b` / `xor t a b` / `select t c a b` (bits known zero in both). -/
def orRes : (t : Ty) → ABShape t → ABShape t → List BitFact → ABRes
  | .bits _, sa, sb, F => { kz := sa.1.kzIn F &&& sb.1.kzIn F }
  | _, _, _, _ => {}

/-- Result metadata of `lshr t a b`. -/
def lshrRes : (t : Ty) → ABShape t → ABShape t → List BitFact → ABRes
  | .bits n, sa, sb, F =>
    match sb.2 with
    | some c =>
      let s := c.toNat % n
      { kz := (sa.1.kzIn F >>> s) ||| highFrom n (n - s) }
    | none => {}
  | _, _, _, _ => {}

/-- Result metadata of `shl t a b`. -/
def shlRes : (t : Ty) → ABShape t → ABShape t → List BitFact → ABRes
  | .bits n, sa, sb, F =>
    match sb.2 with
    | some c =>
      let s := c.toNat % n
      { kz := (sa.1.kzIn F <<< s) ||| (2 ^ s - 1) }
    | none => {}
  | _, _, _, _ => {}

/-- Result metadata of `not t a` (negation swaps the zero / nonzero facts of a `.bool`). -/
def notRes : (t : Ty) → ABShape t → ABRes
  | .bool, sa => { zf := sa.1.nf, nf := sa.1.zf }
  | _, _ => {}

/-- Result metadata of an emitted (non-eliminated) operation. -/
def abRes : {sig ts : List Ty} → OpCode sig ts → Tup ABShape sig → List BitFact → ABRes
  | _, _, .and t, (sa, sb, ()), F => andRes t sa sb F
  | _, _, .or t, (sa, sb, ()), F => orRes t sa sb F
  | _, _, .xor t, (sa, sb, ()), F => orRes t sa sb F
  | _, _, .not t, (sa, ()), _ => notRes t sa
  | _, _, .lshr t, (sa, sb, ()), F => lshrRes t sa sb F
  | _, _, .shl t, (sa, sb, ()), F => shlRes t sa sb F
  | _, _, .select t, (_, sa, sb, ()), F => orRes t sa sb F
  | _, _, .zext m n, (sa, ()), F => { kz := sa.1.kzIn F ||| highFrom n m }
  | _, _, .trunc _ _, (sa, ()), F => { kz := sa.1.kzIn F }
  | _, _, .ofBool n, _, _ => { kz := highFrom n 1 }
  | _, _, .cmp o (.bits n) _ _, (sa, sb, ()), _ => cmpRes o n sa sb
  | _, _, _, _, _ => {}

/-! ## The `assumeBits` pass -/

/-- Apply an elimination tuple to the input operands. -/
def ABElim.apply {V : Ty → Type} {sig : List Ty} (args : Tup (Arg (ABVal V)) sig) :
    {ts : List Ty} → Tup (fun u => ABElim sig u) ts → Tup (ABVal V) ts
  | [], () => ()
  | _ :: _, (.arg i, act) => ((args.get i).toAB, ABElim.apply args act)
  | u :: _, (.imm c, act) => (⟨.imm c, ABInfo.ofImm u c⟩, ABElim.apply args act)

/-- Wrap the results of an emitted operation: the first result carries `r`, and every result
gets a fresh identity starting at `next`. -/
def abWrap {V : Ty → Type} (r : ABRes) : (ts : List Ty) → Tup V ts → Nat → Tup (ABVal V) ts
  | [], (), _ => ()
  | _ :: ts, (x, xs), next =>
    (⟨.var x, ⟨some next, r.kz, r.zf, r.nf⟩⟩, freshABVals ts xs (next + 1))

/-- Outcome of lowering a `let_` binding in `assumeBits`. -/
inductive ABLetStep (V : Ty → Type) (ts : List Ty) : Type
  | elim (res : Tup (ABVal V) ts)
  | emit (op : Op V ts) (wrap : Tup V ts → Tup (ABVal V) ts)

/-- Lower one `let_` operation under in-scope facts `F` with fresh identities from `next`. -/
def Op.abLet {V : Ty → Type} {ts : List Ty} (op : Op (ABVal V) ts) (F : List BitFact)
    (next : Nat) : ABLetStep V ts :=
  let sh := tupABShape op.args
  match abElim? op.code sh F with
  | some act => .elim (ABElim.apply op.args act)
  | none => .emit ⟨op.code, tupAOut op.args⟩ fun xs => abWrap (abRes op.code sh F) ts xs next

mutual
/-- Known-bits / branch-implied simplification of an expression under in-scope facts `F`. -/
def assumeBits {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (next : Nat)
    (F : List BitFact) : Expr (ABVal V) L rs → Expr V L rs
  | .let_ (ts := ts) op k =>
    match op.abLet F next with
    | .elim res => assumeBits next F (k res)
    | .emit op' wrap => .let_ op' fun xs => assumeBits (next + ts.length) F (k (wrap xs))
  | .load t a k =>
    .load t a.abOut fun v => assumeBits (next + 1) F (k (ABVal.fresh v next))
  | .store v a k =>
    .store v.abOut a.abOut (assumeBits next F k)
  | .call f (bs := bs) args k =>
    .call f (tupAOut args) fun xs =>
      assumeBits (next + bs.length) F (k (freshABVals bs xs next))
  | .jnz c t e =>
    .jnz c.abOut (assumeBits next (c.abInfo.nf ++ F) t) (assumeBits next (c.abInfo.zf ++ F) e)
  | .jump j args => .jump j (tupAOut args)
  | .ret vs => .ret (tupAOut vs)
  | .exit f args => .exit f (tupAOut args)
  | .hlt => .hlt
  | .group bodies k =>
    .group (fun Js => assumeBitsB next F (bodies Js)) (fun Js => assumeBits next F (k Js))

/-- Block-list companion of `assumeBits`. -/
def assumeBitsB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (next : Nat)
    (F : List BitFact) : {sig : List (List Ty)} → Blocks (ABVal V) L rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons (ts := ts) b bs =>
    .cons (fun xs => assumeBits (next + ts.length) F (b (freshABVals ts xs next)))
      (assumeBitsB next F bs)
end

/-- Known-bits and branch-implied simplification of a closed function. -/
def Func.assumeBits {as rs : List Ty} (f : Func as rs) : Func as rs :=
  fun V L xs => LeanQbe.T.assumeBits as.length [] (f (ABVal V) L (freshABVals as xs 0))

end LeanQbe.T
