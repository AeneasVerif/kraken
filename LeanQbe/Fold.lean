module

public import LeanQbe.WP

/-!
# Constant folding, copy propagation, algebraic simplification and strength reduction
(QBE `fold.c`, `copy.c`, `simpl.c`), PHOAS to PHOAS

`fold n next : Expr (FVal V) L → Expr V L` reads its input at `FVal V = Arg V × FKey` (`FKey = Arg Nat`):
every input variable carries the operand `Arg V` that replaces it in the output and a symbolic key
`FKey` (assigned from `next`, so that `a.fkey == b.fkey` detects equal variables without `DecidableEq V`).

At `.let_ op k` (when no labels are pending, `n = 0`):

1. **Instruction elimination (`Op.simpAct`)** replaces the bound variable directly in `k` (0 instructions):
   * constant folding when all operands are immediate and `Op.eval` is defined;
   * `copy .l a → a` and redundant 64-bit extension `ext .l .l sg a → a`;
   * annihilators at `.w` and `.l`: `mul a 0 → 0`, `mul 0 b → 0`, `and a 0 → 0`, `and 0 b → 0`;
   * self-annihilators at `.w` and `.l`: `sub x x → 0`, `xor x x → 0`;
   * self-identities at `.l`: `and .l x x → x`, `or .l x x → x`;
   * identities at `.l`: `add x 0`, `add 0 x`, `sub x 0`, `mul x 1`, `mul 1 x`, `or x 0`, `or 0 x`,
     `xor x 0`, `xor 0 x`, `and x (-1)`, `and (-1) x`, `shl/shr/sar x 0 → x`;
   * self-comparisons at `.w` and `.l`: `eq/sle/sge/ule/uge x x → 1`, `ne/slt/sgt/ult/ugt x x → 0`.
2. **Operation rewriting (`Op.rewrite`)** simplifies kept instructions:
   * power-of-two multiply strength reduction: `mul x (2^m) → shl x m` and `mul (2^m) x → shl x m`
     (at `.l` for `m < 64`, at `.w` for `m < 32`);
   * class-`w` identity rules (`add.w x 0`, `sub.w x 0`, `mul.w x 1`, `or.w x 0`, `xor.w x 0`,
     `and.w x (-1)`, `shl/shr/sar.w x 0`) → `copy .w x`;
   * redundant 32-bit extensions (`ext .w .w sg a`, `ext .w .l sg a`, `ext .l .w false a`) → `copy .w a`.
3. **Static branches**: `jnz (.imm c) t e` keeps only the taken branch.

An undefined constant operation (division by zero) is kept, so that the output is undefined there too.
Correctness (`FoldLemmas`): the source `wp` implies the `wp` of the output, and `Wf` is preserved.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

abbrev FKey := Arg Nat
abbrev FVal (V : Type) := Arg V × FKey

def Arg.fout {V : Type} : Arg (FVal V) → Arg V
  | .var p => p.1
  | .imm c => .imm c

def Arg.fkey {V : Type} : Arg (FVal V) → FKey
  | .var p => p.2
  | .imm c => .imm c

def Arg.fpair {V : Type} (a : Arg (FVal V)) : FVal V := (a.fout, a.fkey)

def fimm {V : Type} (c : Val) : FVal V := (.imm c, .imm c)

def Arg.join {V : Type} : Arg (Arg V) → Arg V
  | .var a => a
  | .imm c => .imm c

def Arg.imm? {V : Type} : Arg V → Option Val
  | .var _ => none
  | .imm c => some c

def Op.mapArgs {V W : Type} (f : Arg V → Arg W) : Op V → Op W
  | .bin k o a b => .bin k o (f a) (f b)
  | .cmp k o a b => .cmp k o (f a) (f b)
  | .ext k s sg a => .ext k s sg (f a)
  | .copy k a => .copy k (f a)

def Op.join {V : Type} : Op (Arg V) → Op V := Op.mapArgs Arg.join

/-- The operation with all operands immediate, if they are. -/
def Op.toImm? {V : Type} : Op V → Option (Op Val)
  | .bin k o a b => do let a ← a.imm?; let b ← b.imm?; pure (.bin k o (.imm a) (.imm b))
  | .cmp k o a b => do let a ← a.imm?; let b ← b.imm?; pure (.cmp k o (.imm a) (.imm b))
  | .ext k s sg a => do let a ← a.imm?; pure (.ext k s sg (.imm a))
  | .copy k a => do let a ← a.imm?; pure (.copy k (.imm a))

/-- The value of an operation whose operands are all immediate and which is defined. -/
def Op.constVal? {V : Type} (op : Op V) : Option Val := op.toImm?.bind Op.eval

/-- `copy` at class `l` is the identity. -/
def Op.copyL? {V : Type} : Op V → Option (Arg V)
  | .copy .l a => some a
  | _ => none

/-- What operand or constant an operation simplifies to (eliminating the instruction).
Independent of `V`, so two `Wf`-related instantiations always choose the same action. -/
inductive SimpAct
  | imm (c : Val)
  | fst
  | snd
  deriving DecidableEq, Repr

def CmpOp.isRefl : CmpOp → Bool
  | .eq | .sle | .sge | .ule | .uge => true
  | .ne | .slt | .sgt | .ult | .ugt => false

def cmpAct (_k : Cls) (o : CmpOp) (eqKey : Bool) : Option SimpAct :=
  if eqKey then some (.imm (boolVal o.isRefl)) else none

def copyAct : Cls → Option SimpAct
  | .l => some .fst
  | .w => none

def extAct : Cls → Sz → Bool → Option SimpAct
  | .l, .l, _ => some .fst
  | _, _, _ => none

def binAct (k : Cls) (o : BinOp) (ai bi : Option Val) (eqKey : Bool) : Option SimpAct :=
  match o with
  | .mul =>
    if ai == some 0 then some (.imm 0)
    else if bi == some 0 then some (.imm 0)
    else if k == .l && bi == some 1 then some .fst
    else if k == .l && ai == some 1 then some .snd
    else none
  | .and =>
    if ai == some 0 then some (.imm 0)
    else if bi == some 0 then some (.imm 0)
    else if k == .l && bi == some (BitVec.allOnes 64) then some .fst
    else if k == .l && eqKey then some .fst
    else if k == .l && ai == some (BitVec.allOnes 64) then some .snd
    else none
  | .add =>
    if k == .l && bi == some 0 then some .fst
    else if k == .l && ai == some 0 then some .snd
    else none
  | .sub =>
    if eqKey then some (.imm 0)
    else if k == .l && bi == some 0 then some .fst
    else none
  | .or =>
    if k == .l && bi == some 0 then some .fst
    else if k == .l && eqKey then some .fst
    else if k == .l && ai == some 0 then some .snd
    else none
  | .xor =>
    if eqKey then some (.imm 0)
    else if k == .l && bi == some 0 then some .fst
    else if k == .l && ai == some 0 then some .snd
    else none
  | .shl | .shr | .sar =>
    if k == .l && bi == some 0 then some .fst else none
  | .div | .udiv | .rem | .urem => none

def Op.simpAct {V : Type} (op : Op (FVal V)) : Option SimpAct :=
  match (op.mapArgs Arg.fout).constVal? with
  | some c => some (.imm c)
  | none =>
    match op with
    | .bin k o a b => binAct k o a.fout.imm? b.fout.imm? (a.fkey == b.fkey)
    | .cmp k o a b => cmpAct k o (a.fkey == b.fkey)
    | .ext k s sg _ => extAct k s sg
    | .copy k _ => copyAct k

def Op.firstArg {V : Type} : Op (FVal V) → Arg (FVal V)
  | .bin _ _ a _ => a
  | .cmp _ _ a _ => a
  | .ext _ _ _ a => a
  | .copy _ a => a

def Op.secondArg {V : Type} : Op (FVal V) → Arg (FVal V)
  | .bin _ _ _ b => b
  | .cmp _ _ _ b => b
  | .ext _ _ _ a => a
  | .copy _ a => a

def SimpAct.apply {V : Type} (op : Op (FVal V)) : SimpAct → FVal V
  | .imm c => fimm c
  | .fst => op.firstArg.fpair
  | .snd => op.secondArg.fpair

/-- Find `m < limit` such that `x = 2^m`. -/
def findPow2 (w : Nat) (x : BitVec w) : Nat → Option Nat
  | 0 => none
  | m + 1 => if x = BitVec.twoPow w m then some m else findPow2 w x m

def pow2Shift? : Cls → Val → Option Val
  | .l, c => (findPow2 64 c 64).map (BitVec.ofNat 64)
  | .w, c => (findPow2 32 (lo32 c) 32).map (BitVec.ofNat 64)

/-- Power-of-two multiply strength reduction (`mul x (2^m) → shl x m`, both operand orders). -/
def rewriteMul {V : Type} (k : Cls) (a b : Arg V) : Op V :=
  match b.imm?.bind (pow2Shift? k) with
  | some m => .bin k .shl a (.imm m)
  | none =>
    match a.imm?.bind (pow2Shift? k) with
    | some m => .bin k .shl b (.imm m)
    | none => .bin k .mul a b

/-- Rewrite an operation to a cheaper operation with the same `Op.eval` (power-of-two multiply
strength reduction, class-`w` identity rules, redundant extensions). -/
def rewriteBin {V : Type} (k : Cls) (o : BinOp) (a b : Arg V) : Op V :=
  match k, o with
  | .w, .add =>
    if b.imm? == some 0 then .copy .w a
    else if a.imm? == some 0 then .copy .w b
    else .bin .w .add a b
  | .w, .sub =>
    if b.imm? == some 0 then .copy .w a else .bin .w .sub a b
  | .w, .or =>
    if b.imm? == some 0 then .copy .w a
    else if a.imm? == some 0 then .copy .w b
    else .bin .w .or a b
  | .w, .xor =>
    if b.imm? == some 0 then .copy .w a
    else if a.imm? == some 0 then .copy .w b
    else .bin .w .xor a b
  | .w, .and =>
    if b.imm? == some (BitVec.allOnes 64) then .copy .w a
    else if a.imm? == some (BitVec.allOnes 64) then .copy .w b
    else .bin .w .and a b
  | .w, .shl | .w, .shr | .w, .sar =>
    if b.imm? == some 0 then .copy .w a else .bin .w o a b
  | .w, .mul =>
    if b.imm? == some 1 then .copy .w a
    else if a.imm? == some 1 then .copy .w b
    else rewriteMul .w a b
  | .l, .mul => rewriteMul .l a b
  | k, o => .bin k o a b

def Op.rewrite {V : Type} : Op V → Op V
  | .bin k o a b => rewriteBin k o a b
  | .cmp k o a b => .cmp k o a b
  | .ext .w .w _ a => .copy .w a
  | .ext .w .l _ a => .copy .w a
  | .ext .l .w false a => .copy .w a
  | .ext k s sg a => .ext k s sg a
  | .copy k a => .copy k a

/-- `fold n next e`: `n` is the number of labels declared and not yet defined at `e` (statically known;
it is the length of `wp`'s `acc`), and `next` is the next fresh key. Instructions are only removed where
`n = 0`: removing one elsewhere would let pending labels reach the code after it, which `wp` keeps from
them (junk shapes). -/
def fold {V L : Type} (n next : Nat) : Expr (FVal V) L → Expr V L
  | .let_ op k =>
    if n = 0 then
      match op.simpAct with
      | some act => fold 0 next (k (act.apply op))
      | none =>
        .let_ (op.mapArgs Arg.fout).rewrite fun v => fold 0 (next + 1) (k (.var v, .var next))
    else .let_ (op.mapArgs Arg.fout).rewrite fun v => fold 0 (next + 1) (k (.var v, .var next))
  | .load c s sg a k => .load c s sg a.fout fun v => fold 0 (next + 1) (k (.var v, .var next))
  | .store s v a k => .store s v.fout a.fout (fold 0 next k)
  | .call f as k => .call f (as.map Arg.fout) (fold 0 next k)
  | .jnz c t e =>
    if n = 0 then
      match c.fout with
      | .imm c => if Truthy c then fold 0 next t else fold 0 next e
      | .var v => .jnz (.var v) (fold 0 next t) (fold 0 next e)
    else .jnz c.fout (fold 0 next t) (fold 0 next e)
  | .jump j as => .jump j (as.map Arg.fout)
  | .ret vs => .ret (vs.map Arg.fout)
  | .exit f as => .exit f (as.map Arg.fout)
  | .hlt => .hlt
  | .param f => .param fun v => fold 0 (next + 1) (f (.var v, .var next))
  | .label f => .label fun j => fold (n + 1) next (f j)
  | .block b r => .block (fold 0 next b) (fold (n - 1) next r)

def Func.fold (f : Func) : Func := fun V L => LeanQbe.fold 0 0 (f (FVal V) L)

end LeanQbe
