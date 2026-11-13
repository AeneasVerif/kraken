module

-- Ported from bedrock2/src/bedrock2/Syntax.v at mit-plv/bedrock2@757f17c6083bf8d43b5293a0db545c8d0aa32a13

@[expose] public section

namespace Kraken.Bedrock2

inductive Op1
  | not | opp
  deriving Repr, DecidableEq, Inhabited

inductive BinOp
  | add | sub | mul | mulhuu | divu | remu | and | or | xor | sru | slu | srs | lts | ltu | eq
  deriving Repr, DecidableEq, Inhabited

inductive AccessSize
  | one | two | four | eight
  deriving Repr, DecidableEq, Inhabited

def AccessSize.bytes : AccessSize → Nat
  | .one => 1 | .two => 2 | .four => 4 | .eight => 8

def AccessSize.ofWidth (w : Nat) : AccessSize :=
  if w = 32 then .four else .eight

inductive Expr
  | literal (v : Int)
  | var (x : String)
  | load (sz : AccessSize) (addr : Expr)
  | inlinetable (sz : AccessSize) (table : List UInt8) (index : Expr)
  | op1 (op : Op1) (e : Expr)
  | op (op : BinOp) (e1 e2 : Expr)
  | ite (c e1 e2 : Expr)
  deriving Repr, DecidableEq, Inhabited

inductive Cmd
  | skip
  | set (lhs : String) (rhs : Expr)
  | unset (lhs : String)
  | store (sz : AccessSize) (addr : Expr) (value : Expr)
  | stackalloc (lhs : String) (nbytes : Nat) (body : Cmd)
  | cond (condition : Expr) (nonzeroBranch zeroBranch : Cmd)
  | seq (s1 s2 : Cmd)
  | while (test : Expr) (body : Cmd)
  | call (binds : List String) (function : String) (args : List Expr)
  | interact (binds : List String) (action : String) (args : List Expr)
  deriving Repr, DecidableEq, Inhabited

structure Func where
  params : List String
  rets : List String
  body : Cmd
  deriving Repr, DecidableEq, Inhabited

end Kraken.Bedrock2
