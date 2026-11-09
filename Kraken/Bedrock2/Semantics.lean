module

-- Ported from bedrock2/src/bedrock2/Semantics.v at mit-plv/bedrock2@757f17c6083bf8d43b5293a0db545c8d0aa32a13
--GEN: Deliberate differences from Rocq: access sizes are one/two/four/eight (no word-sized access;
--GEN: `eight` truncates on load and zero-extends on store when w < 64), `stackalloc` has no
--GEN: divisibility side condition, and `Env` is an association list.

public import Kraken.Bedrock2.Memory

@[expose] public section

open Std

namespace Kraken.Bedrock2

variable {w : Nat}

abbrev Locals (w : Nat) := ExtHashMap String (BitVec w)

abbrev Env := List (String × Func)

abbrev LogItem (w : Nat) :=
  (Mem w × String × List (BitVec w)) × (Mem w × List (BitVec w))

abbrev Trace (w : Nat) := List (LogItem w)

abbrev ExtSpec (w : Nat) :=
  Trace w → (mGive : Mem w) → (action : String) → (args : List (BitVec w)) →
  (post : Mem w → List (BitVec w) → Prop) → Prop

structure ExtSpec.Ok (ext : ExtSpec w) : Prop where
  mGive_unique : ∀ t m mGive1 mKeep1 mGive2 mKeep2 a args post1 post2,
    split m mKeep1 mGive1 → split m mKeep2 mGive2 →
    ext t mGive1 a args post1 → ext t mGive2 a args post2 →
    mGive1 = mGive2
  weaken : ∀ t mGive a args (post1 post2 : Mem w → List (BitVec w) → Prop),
    (∀ mReceive rets, post1 mReceive rets → post2 mReceive rets) →
    ext t mGive a args post1 → ext t mGive a args post2
  intersect : ∀ t mGive a args (post1 post2 : Mem w → List (BitVec w) → Prop),
    ext t mGive a args post1 → ext t mGive a args post2 →
    ext t mGive a args (fun mReceive rets => post1 mReceive rets ∧ post2 mReceive rets)

def shamt (b : BitVec w) : Nat := b.toNat % 2 ^ Nat.log2 w

def interpOp1 : Op1 → BitVec w → BitVec w
  | .not, a => ~~~a
  | .opp, a => -a

def interpBinop : BinOp → BitVec w → BitVec w → BitVec w
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .mulhuu, a, b => .ofNat w (a.toNat * b.toNat / 2 ^ w)
  | .divu, a, b => if b = 0 then .allOnes w else a / b
  | .remu, a, b => a % b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .sru, a, b => a >>> shamt b
  | .slu, a, b => a <<< shamt b
  | .srs, a, b => a.sshiftRight (shamt b)
  | .lts, a, b => if a.slt b then 1 else 0
  | .ltu, a, b => if a.ult b then 1 else 0
  | .eq, a, b => if a = b then 1 else 0

def Expr.eval (m : Mem w) (l : Locals w) : Expr → Option (BitVec w)
  | .literal v => some (.ofInt w v)
  | .var x => l.get? x
  | .inlinetable sz t index => do load? sz (t.At 0) (← eval m l index)
  | .load sz a => do load? sz m (← eval m l a)
  | .op1 o e => do return interpOp1 o (← eval m l e)
  | .op o e1 e2 => do return interpBinop o (← eval m l e1) (← eval m l e2)
  | .ite c e1 e2 => do if (← eval m l c) = 0 then eval m l e2 else eval m l e1

def evalArgs (m : Mem w) (l : Locals w) (args : List Expr) : Option (List (BitVec w)) :=
  args.mapM (Expr.eval m l)

def putManyZip (ks : List String) (vs : List (BitVec w)) (l : Locals w) : Option (Locals w) :=
  if ks.length = vs.length then some (l.insertMany (ks.zip vs)) else none

def getMany (l : Locals w) (ks : List String) : Option (List (BitVec w)) :=
  ks.mapM l.get?

inductive Exec (ext : ExtSpec w) (e : Env) :
    Nat → Cmd → Trace w → Mem w → Locals w → (Trace w → Mem w → Locals w → Prop) → Prop
  | skip B t m l post :
      post t m l →
      Exec ext e B .skip t m l post
  | set x ex B t m l post v :
      ex.eval m l = some v →
      post t m (l.insert x v) →
      Exec ext e B (.set x ex) t m l post
  | unset x B t m l post :
      post t m (l.erase x) →
      Exec ext e B (.unset x) t m l post
  | store sz ea ev B t m l post a v m' :
      ea.eval m l = some a →
      ev.eval m l = some v →
      store? sz m a v = some m' →
      post t m' l →
      Exec ext e B (.store sz ea ev) t m l post
  | stackalloc x n body B t mSmall l post :
      n ≤ B →
      (∀ a mStack mCombined, anybytes a n mStack → split mCombined mSmall mStack →
        Exec ext e (B - n) body t mCombined (l.insert x a) fun t' mCombined' l' =>
          ∃ mSmall' mStack', anybytes a n mStack' ∧ split mCombined' mSmall' mStack' ∧
            post t' mSmall' l') →
      Exec ext e B (.stackalloc x n body) t mSmall l post
  | if_true B t m l ec c1 c2 post v :
      ec.eval m l = some v →
      v ≠ 0 →
      Exec ext e B c1 t m l post →
      Exec ext e B (.cond ec c1 c2) t m l post
  | if_false B t m l ec c1 c2 post v :
      ec.eval m l = some v →
      v = 0 →
      Exec ext e B c2 t m l post →
      Exec ext e B (.cond ec c1 c2) t m l post
  | seq c1 c2 B t m l post mid :
      Exec ext e B c1 t m l mid →
      (∀ t' m' l', mid t' m' l' → Exec ext e B c2 t' m' l' post) →
      Exec ext e B (.seq c1 c2) t m l post
  | while_false ec c B t m l post v :
      ec.eval m l = some v →
      v = 0 →
      post t m l →
      Exec ext e B (.while ec c) t m l post
  | while_true ec c B t m l post v mid :
      ec.eval m l = some v →
      v ≠ 0 →
      Exec ext e B c t m l mid →
      (∀ t' m' l', mid t' m' l' → Exec ext e B (.while ec c) t' m' l' post) →
      Exec ext e B (.while ec c) t m l post
  | call binds fname arges B t m l post f args lf mid :
      e.lookup fname = some f →
      evalArgs m l arges = some args →
      putManyZip f.params args ∅ = some lf →
      Exec ext e B f.body t m lf mid →
      (∀ t' m' st1, mid t' m' st1 →
        ∃ retvs, getMany st1 f.rets = some retvs ∧
        ∃ l', putManyZip binds retvs l = some l' ∧
        post t' m' l') →
      Exec ext e B (.call binds fname arges) t m l post
  | interact binds action arges args B t m l post mKeep mGive mid :
      split m mKeep mGive →
      evalArgs m l arges = some args →
      ext t mGive action args mid →
      (∀ mReceive resvals, mid mReceive resvals →
        ∃ l', putManyZip binds resvals l = some l' ∧
        ∀ m', split m' mKeep mReceive →
        post (((mGive, action, args), (mReceive, resvals)) :: t) m' l') →
      Exec ext e B (.interact binds action arges) t m l post

end Kraken.Bedrock2
