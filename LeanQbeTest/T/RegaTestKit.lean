module

public import LeanQbe.T.Main
public import LeanQbe.T.MainLemmas
public import LeanQbe.T.Spill
public import LeanQbeTest.T.Common.CertHarness
import LeanQbe.T.FlatLemmas

/-!
# Shared Rega & Isel Test Kit (`RegaTestKit`)

Architecture-neutral helpers, test programs, and analysis utilities shared across
`FlagRaOpt{,Arm64}Test`, `InvertJnz{,Arm64}Test`, and related register allocation /
instruction selection tests without importing either `Kraken.X64` or `Kraken.AArch64`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.RegaTestKit

open LeanQbe.T
open LeanQbeTest.T.Common.CertHarness

/-- Hints from default heuristics for a target `T` and legal rules `lt`. -/
@[reducible] def hintsOf (T : Target) (lt : LegalTarget) (fs : List Fn) : List T.toIsa.Hints :=
  fs.map (Fn.computeHints T.toIsa lt)

/-- End-to-end verified compilation check (lowering, labels, stack bounds). -/
@[reducible] def chk (T : Target) (L : TargetLayout T) (lt : LegalTarget) (fs : List Fn)
    (exs : List (SigEntry × Nat) := []) (maxBound : Nat := 2048) : Bool :=
  checkCompile T L lt exs [] 0 fs (hintsOf T lt fs) maxBound

/-- Emitted code of a module (empty on a compile error). -/
@[reducible] def codeOf (T : Target) (lt : LegalTarget) (fs : List Fn)
    (exs : List (SigEntry × Nat) := []) : List T.toIsa.Directive :=
  extractCode (compileModule T.toIsa lt T.frame.raBytes exs [] 0 fs (hintsOf T lt fs))

/-- Count directives matching predicate `p`. -/
def countDirs {α : Type} (p : α → Bool) (ds : List α) : Nat :=
  (ds.filter p).length

/-! ## 1. Flag fusion test programs (`cmpCases`, `cmpOps`, `cmpFn`) -/

def cmpOps : List CmpOp := [.eq, .ne, .ult, .ule, .ugt, .uge, .slt, .sle, .sgt, .sge]

/-- `cmp co` at width `w`, operand form `form` (`0` reg-reg, `1` reg-imm, `2` imm-reg), feeding
a `jnz` (`jnz? = true`) or a `select`. -/
def cmpFn (co : CmpOp) (w form : Nat) (jnz? : Bool) : Fn :=
  ⟨"cmpCase", [.bits w, .bits w, i64, i64], [i64], fun V _ (x, y, a, b, ()) =>
    let l : Arg V (.bits w) := if form == 2 then .imm 5 else .var x
    let r : Arg V (.bits w) := if form == 1 then .imm 5 else .var y
    .let_ (op2 (.cmp co (.bits w)) l r) fun (c, ()) =>
    if jnz? then .jnz (.var c) (.ret (.var a, ())) (.ret (.var b, ()))
    else .let_ (op3 (.select i64) (.var c) (.var a) (.var b)) fun (s, ()) => .ret (.var s, ())⟩

def cmpCases : List Fn :=
  cmpOps.flatMap fun co => [8, 16, 32, 64].flatMap fun w =>
    [0, 1, 2].flatMap fun form => [false, true].map (cmpFn co w form)

/-! ## 2. Carry-chain and `SpillFlags` test programs -/

/-- `c = cmp co x y` stays live across an `addc` with a dead carry-out, then feeds a `select`. -/
def addcAfter (nm : Sym) (co : CmpOp) : Fn :=
  ⟨nm, [i64, i64, i64, i64], [i64, i64], fun _ _ (x, y, a, b, ()) =>
    .let_ (op2 (.cmp co i64) (.var x) (.var y)) fun (c, ()) =>
    .let_ (op3 (.addc 64) (.var a) (.var b) (.imm false)) fun (s0, _c0, ()) =>
    .let_ (op3 (.select i64) (.var c) (.var s0) (.imm 0)) fun (r, ()) =>
    .ret (.var r, .var s0, ())⟩

/-! ## 3. Per-call splitting test programs & call tree analysis -/

def slowFn : Fn :=
  ⟨"slow", [i64], [i64], fun _ _ (x, ()) =>
    .let_ (op2 (.mul i64) (.var x) (.var x)) fun (r, ()) => .ret (.var r, ())⟩

/-- `sel x y`: the fast path returns `x + y`; the cold path calls `slow x` with `y` live across. -/
def selFn : Fn :=
  ⟨"sel", [i64, i64], [i64], fun _ _ (x, y, ()) =>
    .let_ (op2 (.and i64) (.var x) (.imm 1)) fun (t, ()) =>
    .let_ (op2 (.cmp .eq i64) (.var t) (.imm 0)) fun (c, ()) =>
    .jnz (.var c)
      (.let_ (op2 (.add i64) (.var x) (.var y)) fun (r, ()) => .ret (.var r, ()))
      (.call "slow" (as := [i64]) (bs := [i64]) (.var x, ()) fun (s, ()) =>
        .let_ (op2 (.add i64) (.var s) (.var y)) fun (r, ()) => .ret (.var r, ()))⟩

mutual
def callIps : Live.Tree → List Nat
  | .call _ ip _ _ _ _ _ k => ip :: callIps k
  | .let_ _ _ _ _ _ k | .load _ _ _ _ _ k | .store _ _ _ _ _ k | .skip _ _ k => callIps k
  | .jnz _ _ _ _ t e => callIps t ++ callIps e
  | .group _ bs k => callIpsB bs ++ callIps k
  | _ => []

def callIpsB : Live.TreeBlocks → List Nat
  | .nil => []
  | .cons _ _ b bs => callIps b ++ callIpsB bs
end

def isSlotMove {R V C : Type} : Move R V C → Bool
  | .st .. | .ld .. | .vst .. | .vld .. => true
  | _ => false

/-- `PreStep` ips (below `nip`) that move a value between a register and a stack slot. -/
def slotMoveIps {R V C : Type} (h : Hints R V C) (nip : Nat) : List Nat :=
  (List.range nip).filter fun ip => match h.pre.find? ip with
    | some ps => ps.moves.any isSlotMove
    | none => false

/-! ## 4. InvertJnz loop test programs -/

/-- Loop where then-arm continues the loop and else-arm exits.
`mT > mE` causes `Spill.hints` to record `invertJnz = true`. -/
def hotLoopFn (name : Sym := "hotLoop") : Fn :=
  ⟨name, [i64, i64], [i64], fun _ _ (n, a, ()) =>
    .group (sig := [[i64, i64]])
      (fun (loopLbl, ()) => .cons (ts := [i64, i64]) (fun (i, acc, ()) =>
        .let_ (op2 (.cmp .eq i64) (.var i) (.imm 0)) fun (c, ()) =>
        .jnz (.var c)
          (.let_ (op2 (.add i64) (.var acc) (.var i)) fun (acc', ()) =>
           .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
           .jump loopLbl (.var i', .var acc', ()))
          (.ret (.var acc, ()))) .nil)
      (fun (loopLbl, ()) => .jump loopLbl (.var n, .var a, ()))⟩

/-- Loop where then-arm exits and else-arm continues the loop.
`mE > mT` causes `Spill.hints` to keep `invertJnz = false`. -/
def coldThenFn (name : Sym := "coldThen") : Fn :=
  ⟨name, [i64, i64], [i64], fun _ _ (n, a, ()) =>
    .group (sig := [[i64, i64]])
      (fun (loopLbl, ()) => .cons (ts := [i64, i64]) (fun (i, acc, ()) =>
        .let_ (op2 (.cmp .eq i64) (.var i) (.imm 0)) fun (c, ()) =>
        .jnz (.var c)
          (.ret (.var acc, ()))
          (.let_ (op2 (.add i64) (.var acc) (.var i)) fun (acc', ()) =>
           .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
           .jump loopLbl (.var i', .var acc', ()))) .nil)
      (fun (loopLbl, ()) => .jump loopLbl (.var n, .var a, ()))⟩

end LeanQbeTest.T.RegaTestKit
