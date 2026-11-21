module

public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Bignum
public import LeanQbe.T.Spill
meta import LeanQbe.T.Arm64.TargLemmas
meta import LeanQbe.T.Examples.Bignum
meta import LeanQbe.T.Spill
public meta import Kraken.AArch64.Print

/-!
# Flag Fusion, Flag-Coloring Fixpoint & Per-Call Live-Range Splitting on AArch64

AArch64 twin of `LeanQbeTest.T.FlagRaOptTest` (x64), kept in its own module so the two targets'
Kraken ISAs are never co-imported. Every check compiles through the verified `Rega.lowerFn` via
`checkCompile` on `armTarget`:

1. Flag fusion over `GprIsa.cmpFlags`: all `240` `cmp` cases (`10` `CmpOp`s, `4` widths, `3`
   operand forms, `select`/`jnz` consumers) compile with zero `cset` (`CSINC`).
2. `Bignum` keeps compiling with no more `cset`s than before (`mul4x4`: `21`).
3. The `SpillFlags` fixpoint keeps `addcAfterUlt`/`addcAfterCmp`/`addcAfterSlt` compiling.
4. Per-call splitting: the `sel`-style cold-branch call leaves the fast path spill-free.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.FlagRaOptArm64Test

open LeanQbe.T LeanQbe.T.Arm64

/-! ## Helpers -/

/-- Hints from the production heuristics (`Fn.computeHints` = `Spill.hints ∘ Fn.mid`). -/
meta def hintsOf (fs : List Fn) : List armTarget.toIsa.Hints :=
  fs.map (Fn.computeHints armTarget.toIsa armLegalTarget)

/-- End-to-end verified compilation check (lowering, labels, stack bounds). -/
meta def chk (fs : List Fn) : Bool :=
  checkCompile armTarget armLayout armLegalTarget [] [] 0 fs (hintsOf fs) 2048

/-- Emitted code of a module (empty on a compile error). -/
meta def codeOf (fs : List Fn) : List armTarget.toIsa.Directive :=
  extractCode (compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes [] [] 0 fs
    (hintsOf fs))

/-- `cset` is `CSINC xd, xzr, xzr, ¬c`. -/
meta def isCsetDir (d : armTarget.toIsa.Directive) : Bool :=
  (Kraken.AArch64.Print.directive d).startsWith "csinc"

meta def countDirs (p : armTarget.toIsa.Directive → Bool) (ds : List armTarget.toIsa.Directive) :
    Nat :=
  (ds.filter p).length

/-! ## 1. Flag fusion: `240` `cmp` cases, zero `cset` -/

meta def cmpOps : List CmpOp := [.eq, .ne, .ult, .ule, .ugt, .uge, .slt, .sle, .sgt, .sge]

/-- `cmp co` at width `w`, operand form `form` (`0` reg-reg, `1` reg-imm, `2` imm-reg), feeding
a `jnz` (`jnz? = true`) or a `select`. -/
meta def cmpFn (co : CmpOp) (w form : Nat) (jnz? : Bool) : Fn :=
  ⟨"cmpCase", [.bits w, .bits w, i64, i64], [i64], fun V _ (x, y, a, b, ()) =>
    let l : Arg V (.bits w) := if form == 2 then .imm 5 else .var x
    let r : Arg V (.bits w) := if form == 1 then .imm 5 else .var y
    .let_ (op2 (.cmp co (.bits w)) l r) fun (c, ()) =>
    if jnz? then .jnz (.var c) (.ret (.var a, ())) (.ret (.var b, ()))
    else .let_ (op3 (.select i64) (.var c) (.var a) (.var b)) fun (s, ()) => .ret (.var s, ())⟩

meta def cmpCases : List Fn :=
  cmpOps.flatMap fun co => [8, 16, 32, 64].flatMap fun w =>
    [0, 1, 2].flatMap fun form => [false, true].map (cmpFn co w form)

#guard cmpCases.length == 240
#guard cmpCases.all fun f => chk [f]
#guard (cmpCases.map fun f => countDirs isCsetDir (codeOf [f])).sum == 0

/-! ## 2. `Bignum` keeps compiling without extra `cset`s -/

#guard chk Examples.Bignum.mul4x4Module.fns
#guard countDirs isCsetDir (codeOf Examples.Bignum.mul4x4Module.fns) ≤ 21
#guard chk Examples.Bignum.addMod25519Module.fns && chk Examples.Bignum.subMod25519Module.fns

/-! ## 3. `SpillFlags` fixpoint: no failed `adcx`/`adox` speculation -/

/-- `c = cmp co x y` stays live across an `addc` with a dead carry-out, then feeds a `select`. -/
meta def addcAfter (nm : Sym) (co : CmpOp) : Fn :=
  ⟨nm, [i64, i64, i64, i64], [i64, i64], fun _ _ (x, y, a, b, ()) =>
    .let_ (op2 (.cmp co i64) (.var x) (.var y)) fun (c, ()) =>
    .let_ (op3 (.addc 64) (.var a) (.var b) (.imm false)) fun (s0, _c0, ()) =>
    .let_ (op3 (.select i64) (.var c) (.var s0) (.imm 0)) fun (r, ()) =>
    .ret (.var r, .var s0, ())⟩

#guard chk [addcAfter "addcAfterUlt" .ult]
#guard chk [addcAfter "addcAfterCmp" .eq]
#guard chk [addcAfter "addcAfterSlt" .slt]

/-! ## 4. Per-call splitting: cold-branch call, spill-free fast path -/

meta def slowFn : Fn :=
  ⟨"slow", [i64], [i64], fun _ _ (x, ()) =>
    .let_ (op2 (.mul i64) (.var x) (.var x)) fun (r, ()) => .ret (.var r, ())⟩

/-- `sel x y`: the fast path returns `x + y`; the cold path calls `slow x` with `y` live across. -/
meta def selFn : Fn :=
  ⟨"sel", [i64, i64], [i64], fun _ _ (x, y, ()) =>
    .let_ (op2 (.and i64) (.var x) (.imm 1)) fun (t, ()) =>
    .let_ (op2 (.cmp .eq i64) (.var t) (.imm 0)) fun (c, ()) =>
    .jnz (.var c)
      (.let_ (op2 (.add i64) (.var x) (.var y)) fun (r, ()) => .ret (.var r, ()))
      (.call "slow" (as := [i64]) (bs := [i64]) (.var x, ()) fun (s, ()) =>
        .let_ (op2 (.add i64) (.var s) (.var y)) fun (r, ()) => .ret (.var r, ()))⟩

mutual
meta def callIps : Live.Tree → List Nat
  | .call _ ip _ _ _ _ _ k => ip :: callIps k
  | .let_ _ _ _ _ _ k | .load _ _ _ _ _ k | .store _ _ _ _ _ k | .skip _ _ k => callIps k
  | .jnz _ _ _ _ t e => callIps t ++ callIps e
  | .group _ bs k => callIpsB bs ++ callIps k
  | _ => []

meta def callIpsB : Live.TreeBlocks → List Nat
  | .nil => []
  | .cons _ _ b bs => callIps b ++ callIpsB bs
end

meta def isSlotMove : armTarget.toIsa.Move → Bool
  | .st .. | .ld .. | .vst .. | .vld .. => true
  | _ => false

/-- `PreStep` ips (below `nip`) that move a value between a register and a stack slot. -/
meta def slotMoveIps (h : armTarget.toIsa.Hints) (nip : Nat) : List Nat :=
  (List.range nip).filter fun ip => match h.pre.find? ip with
    | some ps => ps.moves.any isSlotMove
    | none => false

meta def selMid : Fn := selFn.mid armLegalTarget
meta def selHints : armTarget.toIsa.Hints := Spill.hints armTarget.toIsa selMid
meta def selTree : Live.Tree × List (Nat × Ty) × Nat × Nat × Nat × Trie Ty := Live.Tree.ofFn selMid

#guard chk [slowFn, selFn]
#guard selHints.saved.isEmpty
#guard
  let cs := callIps selTree.1
  let ips := slotMoveIps selHints selTree.2.2.2.2.1
  cs.length == 1 && ips.length == 2 && ips.all fun ip => cs.any fun c => ip == c || ip == c + 1

end LeanQbeTest.T.FlagRaOptArm64Test
