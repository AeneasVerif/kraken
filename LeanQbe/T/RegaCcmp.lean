module

public import LeanQbe.T.RegaDefs
public import LeanQbe.T.RegaW62
public import LeanQbe.T.RegaZext
public import LeanQbe.T.RegaCmpReuse

/-!
# Wave 6.2-B Helpers: `CSNEG` Dynamic Negation & `CCMP`/`CCMN` Step Selection (`RegaCcmp`)

Pure symbolic-allocator helpers for Wave 6.2-B (`OPT-8`):
* `asNegOf?` / `trySelectNeg`: matches `select (.bits w) c x (-x)` or `select (.bits w) c (-x) x`
  via `DefFact.negVar w x` and emits `I.gpr.selectNeg?` (`CSNEG`).
* `ccmpTargetNoFlag` / `ccmpPickStep`: validates `targetJ` entry locations are flag-free and lowers
  one conditional-compare (`CCMP`/`CCMN`) chain step at widths `32`/`64` (direct) or `< 32`
  unsigned/eq (widened via `widenZextArg32`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Rega

/-! ## 1. Dynamic Conditional Negation (`CSNEG`) -/

/-- Check if `a` equals `x` (`.var x`, `false`) or `-x` (via `.negVar w x` in `defs`, `true`). -/
def asNegOf? (defs : Trie DefFact) (w : Nat) : Arg VNat (.bits w) → Option (Nat × Bool)
  | .var v =>
    match defs.find? v with
    | some (.negVar w' x) => if Nat.beq w' w then some (x, true) else some (v, false)
    | _ => some (v, false)
  | .imm _ => none

/-- Lower `select (.bits w) c x (-x)` or `select (.bits w) c (-x) x` via `I.gpr.selectNeg?`. -/
def trySelectNeg (I : Isa) (st : SymState I) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg VNat) sig)
    (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) :
    Option (List I.Directive × FlagMask × Bool) :=
  match I.gpr.selectNeg?, sig, ts, code, args, dsts with
  | some selNegFn, _, _, .select (.bits w), (c, a, b, ()), (.gpr rd, ()) =>
    if ![8, 16, 32, 64].contains w then none
    else
      let pair? := match asNegOf? st.defs w a, asNegOf? st.defs w b with
        | some (xa, false), some (xb, true) =>
          if Nat.beq xa xb then some (xa, false) else none
        | some (xa, true), some (xb, false) =>
          if Nat.beq xa xb then some (xa, true) else none
        | _, _ => none
      pair?.bind fun (x, negFirst) =>
        (findGprFor I true st.regs (.var x)).bind fun rx =>
          tryArg I st [] .bool c fun pc =>
            (selNegFn w pc rx negFirst rd).map fun (code, cl) =>
              (code, cl, Nat.beq w 32 && I.gpr.zeroUpper32SelectNeg)
  | _, _, _, _, _, _ => none

/-! ## 2. Conditional Compare (`CCMP`/`CCMN`) Chain Helpers -/

/-- `true` when `a` is immediate `0#w`. -/
def ccmpIsZeroArg {w : Nat} : Arg VNat (.bits w) → Bool
  | .imm c => c == 0#w
  | _ => false

/-- `true` when `co` against `0#w` would lower as a single-instruction `cbz`/`cbnz`/`tbz`/`tbnz`. -/
def ccmpIsZeroCmp {w : Nat} (co : CmpOp) (a b : Arg VNat (.bits w)) : Bool :=
  [CmpOp.eq, .ne, .slt, .sge].contains co && (ccmpIsZeroArg a || ccmpIsZeroArg b)

/-- `true` iff `targetJ`'s entry entry-live and parameter locations contain no `.flag _` entries,
guaranteeing later `ccmp` steps (which only clobber flags + scratch) preserve `zeroMoveJump?`. -/
def ccmpTargetNoFlag (I : Isa) (h : I.Hints) (targetJ : Nat) : Bool :=
  match h.entry.find? targetJ with
  | some en =>
    en.live.all (fun (_, loc) => match loc with | .flag _ => false | _ => true) &&
    en.ploc.all fun loc => match loc with | .flag _ => false | _ => true
  | none => false

/-- Emit one `CCMP`/`CCMN` (`isOr := true`) instruction updating `prevCond` with `co a b`, returning
`(dstCond, code, clob, isNonCb)`. Supports widths `32`/`64` directly and `< 32` unsigned/eq via
`widenZextArg32`. -/
def ccmpPickStep (I : Isa) (st : SymState I) (prevCond : I.Cond) (co : CmpOp) {w : Nat}
    (a b : Arg VNat (.bits w)) : Option (I.Cond × List I.Directive × FlagMask × Bool) :=
  I.gpr.ccmp?.bind fun ccmpFn =>
    if Nat.beq w 32 || Nat.beq w 64 then
      tryArg I st [] (.bits w) a fun pa =>
        tryArg I st [] (.bits w) b fun pb =>
          (ccmpFn prevCond true co w pa pb).map fun (dst, code, cl) =>
            (dst, code, cl, !ccmpIsZeroCmp co a b)
    else if Nat.blt w 32 && cmpIsUnsignedOrEq co then
      (widenZextArg32 I st.regs a).bind fun pa =>
        (widenZextArg32 I st.regs b).bind fun pb =>
          (ccmpFn prevCond true co 32 pa pb).map fun (dst, code, cl) =>
            (dst, code, cl, !ccmpIsZeroCmp co a b)
    else none

/-! ## 3. Shared Structural `Expr` Counters & Variable-Freedom Predicates -/

/-- `true` when argument `a` is `.var x`. -/
def argHasVar {t : Ty} (a : Arg VNat t) (x : Nat) : Bool :=
  match a with | .var y => Nat.beq y x | .imm _ => false

/-- `true` when variable `x` occurs among the arguments `args`. -/
def argsHaveVar : {ts : List Ty} → Tup (Arg VNat) ts → Nat → Bool
  | [], (), _ => false
  | _ :: _, (a, as), x => argHasVar a x || argsHaveVar as x

/-- `true` when `e` is a jump whose target entry and arguments never mention variable `x`. -/
def jumpAvoids {rs : List Ty} {I : Isa} (h : I.Hints) (x : Nat) : Expr VNat LNat rs → Bool
  | .jump j args => !argsHaveVar args x &&
    match h.entry.find? j with
    | some en => en.live.all fun (sa, _) => !symArgEq sa (.var x)
    | none => false
  | _ => false

mutual
/-- Instruction-pointer count consumed by `lowerExpr` on `e` starting at `(nv, nl)`. -/
def exprIpCount {rs : List Ty} : Expr VNat LNat rs → Nat → Nat → Nat × Nat × Nat
  | .let_ (ts := ts) _ k, nv, nl =>
    let (nv1, nl1, d) := exprIpCount (k (Tup.levels ts nv)) (nv + ts.length) nl
    (nv1, nl1, d + 1)
  | .load _ _ k, nv, nl =>
    let (nv1, nl1, d) := exprIpCount (k nv) (nv + 1) nl
    (nv1, nl1, d + 1)
  | .store _ _ k, nv, nl =>
    let (nv1, nl1, d) := exprIpCount k nv nl
    (nv1, nl1, d + 1)
  | .call (bs := bs) _ _ k, nv, nl =>
    let (nv1, nl1, d) := exprIpCount (k (Tup.levels bs nv)) (nv + bs.length) nl
    (nv1, nl1, d + 1)
  | .jnz (.imm b) t e, nv, nl =>
    let (nv1, nl1, d) := if b then exprIpCount t nv nl else exprIpCount e nv nl
    (nv1, nl1, d + 1)
  | .jnz (.var _) t e, nv, nl =>
    let (nv1, nl1, de) := exprIpCount e nv (nl + 1)
    let (nv2, nl2, dt) := exprIpCount t nv1 nl1
    (nv2, nl2, de + dt + 1)
  | .jump _ _, nv, nl | .ret _, nv, nl | .exit _ _, nv, nl | .hlt, nv, nl => (nv, nl, 1)
  | .group (sig := sig) bodies k, nv, nl =>
    let ls := Tup.levels sig nl
    let (nv1, nl1, dk) := exprIpCount (k ls) nv (nl + sig.length)
    let (nv2, nl2, db) := blocksIpCount (bodies ls) nv1 nl1
    (nv2, nl2, dk + db)

def blocksIpCount {rs : List Ty} :
    {sig : List (List Ty)} → Blocks VNat LNat rs sig → Nat → Nat → Nat × Nat × Nat
  | _, .nil, nv, nl => (nv, nl, 0)
  | _, .cons (ts := ts) b bs, nv, nl =>
    let (nv1, nl1, db) := exprIpCount (b (Tup.levels ts nv)) (nv + ts.length) nl
    let (nv2, nl2, dbs) := blocksIpCount bs nv1 nl1
    (nv2, nl2, db + dbs)
end

/-- Instruction-pointer at which `lowerExpr` starts lowering the `then`-arm `t` of `jnz`. -/
def jnzIpT {rs : List Ty} (nv nl ip : Nat) (t e : Expr VNat LNat rs) : Nat :=
  match t with
  | .jump _ _ => ip + 1 + (exprIpCount e nv (nl + 1)).2.2
  | _ => ip + 1

mutual
def exprFreeOfVar {I : Isa} (h : I.Hints) (x : Nat) {rs : List Ty} :
    Expr VNat LNat rs → Nat → Bool
  | .let_ (ts := ts) op k, nv =>
    !argsHaveVar op.args x && exprFreeOfVar h x (k (Tup.levels ts nv)) (nv + ts.length)
  | .load _ a k, nv =>
    !argHasVar a x && exprFreeOfVar h x (k nv) (nv + 1)
  | .store v a k, nv =>
    !argHasVar v x && !argHasVar a x && exprFreeOfVar h x k nv
  | .call (bs := bs) _ args k, nv =>
    !argsHaveVar args x && exprFreeOfVar h x (k (Tup.levels bs nv)) (nv + bs.length)
  | .jnz c t e, nv =>
    !argHasVar c x && exprFreeOfVar h x t nv && exprFreeOfVar h x e nv
  | .jump j args, _ =>
    !argsHaveVar args x &&
      match h.entry.find? j with
      | some en => en.live.all fun (sa, _) => !symArgEq sa (.var x)
      | none => true
  | .ret vs, _ => !argsHaveVar vs x
  | .exit _ args, _ => !argsHaveVar args x
  | .hlt, _ => true
  | .group (sig := sig) bodies k, nv =>
    let ls := Tup.levels sig 0
    exprFreeOfVar h x (k ls) nv && blocksFreeOfVar h x (bodies ls) nv

def blocksFreeOfVar {I : Isa} (h : I.Hints) (x : Nat) {rs : List Ty} :
    {sig : List (List Ty)} → Blocks VNat LNat rs sig → Nat → Bool
  | _, .nil, _ => true
  | _, .cons (ts := ts) b bs, nv =>
    exprFreeOfVar h x (b (Tup.levels ts nv)) (nv + ts.length) && blocksFreeOfVar h x bs nv
end

/-- Unpack `.cmp co (.bits w) .bool` without generating a dependent multi-arg matcher. -/
def ccmpAsCmp? {sig ts : List Ty} (code : OpCode sig ts) : Tup (Arg VNat) sig →
    Option (Sigma fun w => CmpOp × Arg VNat (.bits w) × Arg VNat (.bits w)) :=
  match code with
  | .cmp co (.bits w) .bool _ => fun (a, b, _) => some ⟨w, co, a, b⟩
  | _ => fun _ => none

end Rega
end LeanQbe.T
