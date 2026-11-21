module

public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Bignum
public import LeanQbe.T.Spill
meta import LeanQbe.T.Amd64.TargLemmas
meta import LeanQbe.T.Examples.Bignum
meta import LeanQbe.T.Spill

/-!
# Flag Fusion, Flag-Coloring Fixpoint & Per-Call Live-Range Splitting on x64

Regression tests for the untrusted `Spill` / `SpillFlags` hint heuristics on `x64Target` (every
check compiles through the verified `Rega.lowerFn` via `checkCompile`); the AArch64 twin is
`LeanQbeTest.T.FlagRaOptArm64Test` (the two targets' Kraken ISAs are never co-imported):

1. Flag fusion over `GprIsa.cmpFlags`: all `240` combinations of `10` `CmpOp`s, `4` widths, `3`
   operand forms (reg-reg, reg-imm, imm-reg) and `2` consumers (`select`, `jnz`) compile with
   zero `setcc`.
2. Carry-first condition priority: `Bignum.mul4x4` keeps `11 mulx`, `12 adcx`, `12 adox`, and
   `0 setcc`.
3. The `SpillFlags` fixpoint: a `cmp` web live across an `.addc` whose carry-out cannot stay in
   flags no longer relies on a speculated `adcx`/`adox` variant (`addcAfterUlt` and
   `addcAfterCmp` used to fail `Rega` with `let: op`).
4. Per-call splitting: in a `sel`-style function whose cold branch calls `slow`, the call-crossing
   argument lives in a caller-saved register, no callee-saved register is saved, and every stack
   access sits at the call (backup store) or right after it (reload): the fast path has no
   spills.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.FlagRaOptTest

open LeanQbe.T LeanQbe.T.Amd64

/-! ## Helpers -/

/-- Hints from the production heuristics (`Fn.computeHints` = `Spill.hints ∘ Fn.mid`). -/
meta def hintsOf (fs : List Fn) : List x64Target.toIsa.Hints :=
  fs.map (Fn.computeHints x64Target.toIsa x64LegalTarget)

/-- End-to-end verified compilation check (lowering, labels, stack bounds). -/
meta def chk (fs : List Fn) : Bool :=
  checkCompile x64Target x64Layout x64LegalTarget [] [] 0 fs (hintsOf fs) 2048

/-- Emitted code of a module (empty on a compile error). -/
meta def codeOf (fs : List Fn) : List x64Target.toIsa.Directive :=
  extractCode (compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes [] [] 0 fs
    (hintsOf fs))

meta def isSetccDir : Directive → Bool
  | .instr (.regular _ _ (.setcc _ _)) => true
  | _ => false

meta def isMulxDir : Directive → Bool
  | .instr (.regular _ _ (.mulx _ _ _)) => true
  | _ => false

meta def isAdcxDir : Directive → Bool
  | .instr (.regular _ _ (.adcx _ _)) => true
  | _ => false

meta def isAdoxDir : Directive → Bool
  | .instr (.regular _ _ (.adox _ _)) => true
  | _ => false

meta def countDirs (p : Directive → Bool) (ds : List Directive) : Nat := (ds.filter p).length

/-! ## 1. Flag fusion: `240` `cmp` cases, zero `setcc` -/

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
#guard (cmpCases.map fun f => countDirs isSetccDir (codeOf [f])).sum == 0

/-! ## 2. Carry-first priority keeps `mul4x4`'s dual carry chains -/

meta def mul4x4Code : List Directive := codeOf Examples.Bignum.mul4x4Module.fns

#guard chk Examples.Bignum.mul4x4Module.fns
#guard countDirs isMulxDir mul4x4Code == 11
#guard countDirs isAdcxDir mul4x4Code == 12
#guard countDirs isAdoxDir mul4x4Code == 12
#guard countDirs isSetccDir mul4x4Code == 0
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

meta def isSlotMove : x64Target.toIsa.Move → Bool
  | .st .. | .ld .. | .vst .. | .vld .. => true
  | _ => false

/-- `PreStep` ips (below `nip`) that move a value between a register and a stack slot. -/
meta def slotMoveIps (h : x64Target.toIsa.Hints) (nip : Nat) : List Nat :=
  (List.range nip).filter fun ip => match h.pre.find? ip with
    | some ps => ps.moves.any isSlotMove
    | none => false

meta def selMid : Fn := selFn.mid x64LegalTarget
meta def selHints : x64Target.toIsa.Hints := Spill.hints x64Target.toIsa selMid
meta def selTree : Live.Tree × List (Nat × Ty) × Nat × Nat × Nat × Trie Ty := Live.Tree.ofFn selMid

#guard chk [slowFn, selFn]
#guard selHints.saved.isEmpty
#guard
  let cs := callIps selTree.1
  let ips := slotMoveIps selHints selTree.2.2.2.2.1
  cs.length == 1 && ips.length == 2 && ips.all fun ip => cs.any fun c => ip == c || ip == c + 1

/-! ## 5. Stage 1a `[base + disp]` addressing via `Hints.elide` + `DefFact.addImm64` -/

meta def isAddSubLeaDir : Directive → Bool
  | .instr (.regular _ .W64 (.add (.reg (.low .rsp .W64)) _))
  | .instr (.regular _ .W64 (.sub (.reg (.low .rsp .W64)) _)) => false
  | .instr (.regular _ _ (.add _ _))
  | .instr (.regular _ _ (.sub _ _))
  | .instr (.regular _ _ (.lea _ _)) => true
  | _ => false

/-- Elides both `add64 +16` and `sub64 8` (`[-8]`) into memory displacements; preserves `cmp`
flags live across the elided `add64` (`0 setcc`). -/
meta def addrDispFn : Fn :=
  ⟨"addrDispX64", [i64, i64], [i64], fun _ _ (p, y, ()) =>
    .let_ (op2 (.cmp .ult i64) (.var p) (.var y)) fun (c, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 16)) fun (p1, ()) =>
    .let_ (op2 (.sub i64) (.var p) (.imm 8)) fun (p2, ()) =>
    .load i32 (.var p1) fun a =>
    .let_ (op1 (.zext 32 64) (.var a)) fun (az, ()) =>
    .store (t := i64) (.var az) (.var p2) (
    .let_ (op3 (.select i64) (.var c) (.var p) (.var y)) fun (r, ()) =>
    .ret (.var r, ()))⟩

/-- Elided address def whose base `p` crosses `call slow`, reloading `p` at the load site. -/
meta def addrCallFn : Fn :=
  ⟨"addrCallX64", [i64, i64], [i64], fun _ _ (p, k, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 24)) fun (p1, ()) =>
    .call "slow" (as := [i64]) (bs := [i64]) (.var k, ()) fun (_r, ()) =>
    .load i64 (.var p1) fun x =>
    .ret (.var x, ())⟩

/-- Vector `[base + disp]` (`v4i32` unaligned load at `base + 32`) elides `add64`. -/
meta def addrVecFn : Fn :=
  ⟨"addrVecX64", [i64], [v4i32], fun _ _ (p, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 32)) fun (p1, ()) =>
    .load v4i32 (.var p1) fun v =>
    .ret (.var v, ())⟩

/-- Non-address use (value of `store`) prevents elision, and out-of-int32 disp (`2^33`) prevents
elision so no fallback `movabs+add` inside `addrToExpr` is triggered. -/
meta def addrNoElideFn : Fn :=
  ⟨"addrNoElideX64", [i64, i64], [i64], fun _ _ (p, q, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 8)) fun (v1, ()) =>
    .store (t := i64) (.var v1) (.var q) (
    .let_ (op2 (.add i64) (.var p) (.imm (BitVec.ofNat 64 (2 ^ 33)))) fun (pBig, ()) =>
    .load i64 (.var pBig) fun r =>
    .ret (.var r, ()))⟩

#guard chk [addrDispFn]
#guard countDirs isAddSubLeaDir (codeOf [addrDispFn]) == 0
#guard countDirs isSetccDir (codeOf [addrDispFn]) == 0
#guard chk [slowFn, addrCallFn]
#guard (Fn.computeHints x64Target.toIsa x64LegalTarget addrCallFn).elide.getD 0 false == true
#guard chk [addrVecFn]
#guard countDirs isAddSubLeaDir (codeOf [addrVecFn]) == 0
#guard chk [addrNoElideFn]
#guard (Fn.computeHints x64Target.toIsa x64LegalTarget addrNoElideFn).elide.getD 0 false == false
#guard (Fn.computeHints x64Target.toIsa x64LegalTarget addrNoElideFn).elide.getD 2 false == false

/-! ## 6. Stage 1b `[base + idx * scale + disp]` SIB addressing (`Hints.elide` + `DefFact`) -/

meta def isSibMemDir : Directive → Bool
  | .instr (.regular _ _ (.mov dst src)) =>
    (match dst with | .mem e => e.idx.isSome | _ => false) ||
    (match src with | .regOrMem (.mem e) => e.idx.isSome | _ => false)
  | .instr (.regular _ _ (.movzx dst src)) =>
    (match dst with | .mem e => e.idx.isSome | _ => false) ||
    (match src with | .mem e => e.idx.isSome | _ => false)
  | _ => false

meta def isShlDir : Directive → Bool
  | .instr (.regular _ _ (.shl _ _)) => true
  | _ => false

/-- Covers Kissat SIB patterns: `vals[lit]` (`scale=1`, `zext`), `ar[(idx+2)<<2]` &
`ar[(idx+3)<<2]` (`scale=4, disp=8,12` across `cmp`/`select`), and `wvec[(lit<<1)+1]`
(`scale=8, disp=4` store). Emits 4 SIB memory ops, 0 `shl`, 0 `add`/`sub`/`lea`, 0 `setcc`. -/
meta def addrSibChainFn : Fn :=
  ⟨"addrSibChainX64", [i64, i64, i64, i32, i64], [i32],
    fun _ _ (vals, ar, wvec, lit, idx, ()) =>
      .let_ (op1 (.zext 32 64) (.var lit)) fun (lit64, ()) =>
      .let_ (op2 (.add i64) (.var vals) (.var lit64)) fun (pv, ()) =>
      .load i8 (.var pv) fun vb =>
      .let_ (op1 (.zext 8 32) (.var vb)) fun (vb32, ()) =>
      .let_ (op2 (.cmp .ult i64) (.var idx) (.var vals)) fun (c, ()) =>
      .let_ (op2 (.add i64) (.var idx) (.imm 2)) fun (c2, ()) =>
      .let_ (op2 (.shl i64) (.var c2) (.imm 2)) fun (o2, ()) =>
      .let_ (op2 (.add i64) (.var ar) (.var o2)) fun (pa2, ()) =>
      .let_ (op2 (.add i64) (.var idx) (.imm 3)) fun (c3, ()) =>
      .let_ (op2 (.shl i64) (.var c3) (.imm 2)) fun (o3, ()) =>
      .let_ (op2 (.add i64) (.var ar) (.var o3)) fun (pa3, ()) =>
      .load i32 (.var pa2) fun a2 =>
      .load i32 (.var pa3) fun a3 =>
      .let_ (op2 (.shl i64) (.var lit64) (.imm 3)) fun (wl, ()) =>
      .let_ (op2 (.add i64) (.var wvec) (.var wl)) fun (pw0, ()) =>
      .let_ (op2 (.add i64) (.var pw0) (.imm 4)) fun (pw1, ()) =>
      .store (t := i32) (.var vb32) (.var pw1) (
      .let_ (op3 (.select i32) (.var c) (.var a2) (.var a3)) fun (res, ()) =>
      .ret (.var res, ()))⟩

/-- Elides `(idx + 1) << 2` + `base` across `call slow`, preserving `p` and `idx` live. -/
meta def addrSibCallFn : Fn :=
  ⟨"addrSibCallX64", [i64, i64, i64], [i64], fun _ _ (p, idx, k, ()) =>
    .let_ (op2 (.add i64) (.var idx) (.imm 1)) fun (i1, ()) =>
    .let_ (op2 (.shl i64) (.var i1) (.imm 2)) fun (off, ()) =>
    .let_ (op2 (.add i64) (.var p) (.var off)) fun (pa, ()) =>
    .call "slow" (as := [i64]) (bs := [i64]) (.var k, ()) fun (_r, ()) =>
    .load i64 (.var pa) fun x =>
    .ret (.var x, ())⟩

/-- Vector `vload` with `[base + idx * 8 + 16]` SIB elides `add`/`shl`. -/
meta def addrSibVecFn : Fn :=
  ⟨"addrSibVecX64", [i64, i64], [v4i32], fun _ _ (p, idx, ()) =>
    .let_ (op2 (.add i64) (.var idx) (.imm 2)) fun (i2, ()) =>
    .let_ (op2 (.shl i64) (.var i2) (.imm 3)) fun (off, ()) =>
    .let_ (op2 (.add i64) (.var p) (.var off)) fun (pa, ()) =>
    .load v4i32 (.var pa) fun v =>
    .ret (.var v, ())⟩

/-- Scale-shift overflow (`<< 4`), non-address value use, and int32 disp overflow prevent SIB
elision cleanly. -/
meta def addrSibNoElideFn : Fn :=
  ⟨"addrSibNoElideX64", [i64, i64, i64], [i64], fun _ _ (p, idx, q, ()) =>
    .let_ (op2 (.shl i64) (.var idx) (.imm 4)) fun (s16, ()) =>
    .let_ (op2 (.add i64) (.var p) (.var s16)) fun (p16, ()) =>
    .load i64 (.var p16) fun v0 =>
    .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun (s4, ()) =>
    .let_ (op2 (.add i64) (.var p) (.var s4)) fun (pEsc, ()) =>
    .store (t := i64) (.var pEsc) (.var q) (
    .let_ (op2 (.add i64) (.var idx) (.imm (BitVec.ofNat 64 (2 ^ 30)))) fun (ib, ()) =>
    .let_ (op2 (.shl i64) (.var ib) (.imm 3)) fun (ob, ()) =>
    .let_ (op2 (.add i64) (.var p) (.var ob)) fun (pBig, ()) =>
    .load i64 (.var pBig) fun v1 =>
    .let_ (op2 (.add i64) (.var v0) (.var v1)) fun (r, ()) =>
    .ret (.var r, ()))⟩

#guard chk [addrSibChainFn]
#guard countDirs isSibMemDir (codeOf [addrSibChainFn]) == 4
#guard countDirs isShlDir (codeOf [addrSibChainFn]) == 0
#guard countDirs isAddSubLeaDir (codeOf [addrSibChainFn]) == 0
#guard countDirs isSetccDir (codeOf [addrSibChainFn]) == 0
#guard chk [slowFn, addrSibCallFn]
#guard countDirs isSibMemDir (codeOf [slowFn, addrSibCallFn]) == 1
#guard countDirs isShlDir (codeOf [slowFn, addrSibCallFn]) == 0
#guard countDirs isAddSubLeaDir (codeOf [slowFn, addrSibCallFn]) == 0
#guard (Fn.computeHints x64Target.toIsa x64LegalTarget addrSibCallFn).elide.getD 0 false == true
#guard (Fn.computeHints x64Target.toIsa x64LegalTarget addrSibCallFn).elide.getD 1 false == true
#guard (Fn.computeHints x64Target.toIsa x64LegalTarget addrSibCallFn).elide.getD 2 false == true
#guard chk [addrSibVecFn]
#guard countDirs isShlDir (codeOf [addrSibVecFn]) == 0
#guard countDirs isAddSubLeaDir (codeOf [addrSibVecFn]) == 0
#guard chk [addrSibNoElideFn]
#guard (Fn.computeHints x64Target.toIsa x64LegalTarget addrSibNoElideFn).elide.getD 0 false == false
#guard (Fn.computeHints x64Target.toIsa x64LegalTarget addrSibNoElideFn).elide.getD 3 false == false
#guard (Fn.computeHints x64Target.toIsa x64LegalTarget addrSibNoElideFn).elide.getD 6 false == false

/-- Non-destructive 3-address `lea` (`C1b`) for live inputs (`x + y`, `x + 3`, `y - 2`) with both
`x` and `y` live to the return tuple, emitting `lea` instead of `mov + add/sub`, plus `cmp`/`select`
with `0 setcc` across `x + 3`/`y - 2`. -/
meta def leaNonDestructFn : Fn :=
  ⟨"leaNonDestructX64", [i64, i64], [i64, i64], fun _ _ (x, y, ()) =>
    .let_ (op2 (.add i64) (.var x) (.var y)) fun (s1, ()) =>
    .let_ (op2 (.cmp .ult i64) (.var x) (.var y)) fun (c, ()) =>
    .let_ (op2 (.add i64) (.var x) (.imm 3)) fun (s2, ()) =>
    .let_ (op2 (.sub i64) (.var y) (.imm 2)) fun (s3, ()) =>
    .let_ (op3 (.select i64) (.var c) (.var s2) (.var s3)) fun (r0, ()) =>
    .let_ (op2 (.xor i64) (.var x) (.var y)) fun (k0, ()) =>
    .let_ (op2 (.xor i64) (.var r0) (.var k0)) fun (r1, ()) =>
    .ret (.var s1, .var r1, ())⟩

meta def isAddOrSubDir : Directive → Bool
  | .instr (.regular _ .W64 (.add (.reg (.low .rsp .W64)) _))
  | .instr (.regular _ .W64 (.sub (.reg (.low .rsp .W64)) _)) => false
  | .instr (.regular _ _ (.add _ _))
  | .instr (.regular _ _ (.sub _ _)) => true
  | _ => false

meta def isLeaDir : Directive → Bool
  | .instr (.regular _ _ (.lea _ _)) => true
  | _ => false

#guard chk [leaNonDestructFn]
#guard countDirs isAddOrSubDir (codeOf [leaNonDestructFn]) == 0
#guard countDirs isLeaDir (codeOf [leaNonDestructFn]) == 3
#guard countDirs isSetccDir (codeOf [leaNonDestructFn]) == 0

/-! ## 7. Upper-32 zero tracking: `zext 32 64` elision (`C1c`) -/

meta def isMovlRegDir : Directive → Bool
  | .instr (.regular _ .W32 (.mov (.reg (.low _ .W32)) (.regOrMem (.reg (.low _ .W32))))) => true
  | _ => false

meta def isSelfMovlDir : Directive → Bool
  | .instr (.regular _ .W32 (.mov (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))) =>
    rd == rs
  | _ => false

/-- `load i32` directly followed by `zext 32 64` emits zero reg-to-reg `movl`. -/
meta def zext32LoadRetFn : Fn :=
  ⟨"zext32LoadRetX64", [i64], [i64], fun _ _ (p, ()) =>
    .load i32 (.var p) fun a =>
    .let_ (op1 (.zext 32 64) (.var a)) fun (z, ()) =>
    .ret (.var z, ())⟩

/-- `load i32`, `and i32`, and `lshr i32` preserve zero upper 32 bits even across `call slow`,
eliminating any self-`movl` at `zext 32 64`. -/
meta def zext32UpperZeroFn : Fn :=
  ⟨"zext32UpperZeroX64", [i64, i64], [i64], fun _ _ (p, k, ()) =>
    .load i32 (.var p) fun a =>
    .let_ (op2 (.and i32) (.var a) (.imm 0xfff)) fun (b, ()) =>
    .let_ (op2 (.lshr i32) (.var b) (.imm 1)) fun (c, ()) =>
    .call "slow" (as := [i64]) (bs := [i64]) (.var k, ()) fun (r0, ()) =>
    .let_ (op1 (.zext 32 64) (.var c)) fun (z, ()) =>
    .let_ (op2 (.add i64) (.var z) (.var r0)) fun (ans, ()) =>
    .ret (.var ans, ())⟩

/-- `trunc 64 32` can leave non-zero upper bits; `zext 32 64` MUST retain a `movl`. -/
meta def zext32AfterTruncFn : Fn :=
  ⟨"zext32AfterTruncX64", [i64], [i64], fun _ _ (x, ()) =>
    .let_ (op1 (.trunc 64 32) (.var x)) fun (y, ()) =>
    .let_ (op1 (.zext 32 64) (.var y)) fun (z, ()) =>
    .ret (.var z, ())⟩

#guard chk [zext32LoadRetFn]
#guard countDirs isMovlRegDir (codeOf [zext32LoadRetFn]) == 0
#guard chk [slowFn, zext32UpperZeroFn]
#guard countDirs isSelfMovlDir (codeOf [slowFn, zext32UpperZeroFn]) == 0
#guard chk [zext32AfterTruncFn]
#guard countDirs isMovlRegDir (codeOf [zext32AfterTruncFn]) >= 1

end LeanQbeTest.T.FlagRaOptTest
