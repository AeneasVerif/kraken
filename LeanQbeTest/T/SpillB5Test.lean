module

import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Examples.Kissat.Plain
import LeanQbe.T.Examples.LratBytes
import LeanQbe.T.Main
import LeanQbe.T.Spill
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.Plain
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.Main
meta import LeanQbe.T.Spill

/-!
# Spill-Placement Heuristics on x64 (`Spill.Cfg`)

Regression tests for the untrusted spill-placement heuristics switched by `Spill.Cfg`, on the
x64 target (`Kraken.X64` through `LeanQbe.T.Amd64.Targ`; an AArch64 module could not share this
file). Every hint set below is re-checked by the verified `Rega.lowerFn`, and each section
compares the default configuration with `Spill.Cfg.legacy` or with a single switch turned off:

1. `sink`: a slot-homed value that is read on the early-return arm is no longer stored before
   the branch (the store moves into the arm that keeps the value).
2. `joinGuard`: a slot-homed join parameter that is read first thing in its block keeps a
   register `Entry.ploc` (no store on every edge followed by an immediate reload).
3. `regEntry`: the fast arm of a watch-scan shaped loop carries no stack traffic, because the
   loop header takes its spilled live-in in the register the back edges hold it in.
4. High-pressure GPR budget guards: `joinGuard` caps promotion within the block GPR budget, and
   `regEntry` reserves GPRs for non-slot-direct parameters (`immJoverB5`, `regStealB5`).
5. `Kissat.Plain` / `LratBytes` hot functions lower under every configuration, and the default hints
   need no more spill moves than the legacy ones (strictly fewer on `plain_prop_lit`,
   `plain_sweep`, `plain_zero_tables`). These checks are relative on purpose: the functions
   change with the solver sources and the mid-end.
6. `armEvict`: a loop invariant read on the fast arm keeps its register there while a heavy slow
   arm that does not read it evicts it (`armEvFn`).

The synthetic functions are lowered as written (no mid-end), so their shape is fixed.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.SpillB5Test

open LeanQbe.T LeanQbe.T.Amd64

/-! ## Helpers -/

/-- `Spill.hints` of `f` as written (no mid-end) under `cfg`. -/
meta def hintsOf (cfg : Spill.Cfg) (f : Fn) : x64Target.toIsa.Hints :=
  Spill.hints x64Target.toIsa f (cfg := cfg)

/-- Directives of `f` lowered with its `cfg` hints (`none` if `Rega.lowerFn` rejects them). -/
meta def lower? (cfg : Spill.Cfg) (f : Fn) : Option (List x64Target.toIsa.Directive) :=
  match Rega.lowerFn x64Target.toIsa (hintsOf cfg f) f.ext f with
  | .ok c => some c
  | .error _ => none

meta def lowers (cfg : Spill.Cfg) (f : Fn) : Bool := (lower? cfg f).isSome

/-- Directive count of `f` under `cfg` (`0` if lowering fails). -/
meta def dirs (cfg : Spill.Cfg) (f : Fn) : Nat := ((lower? cfg f).map List.length).getD 0

meta def isSt : x64Target.toIsa.Move → Bool
  | .st .. => true
  | _ => false

meta def isSlotMove : x64Target.toIsa.Move → Bool
  | .st .. | .ld .. => true
  | _ => false

/-- Number of `PreStep` moves satisfying `p` at the instruction pointers `ips`. -/
meta def movesAt (h : x64Target.toIsa.Hints) (p : x64Target.toIsa.Move → Bool)
    (ips : List Nat) : Nat :=
  ips.foldl (fun n ip => match h.pre.find? ip with
    | some ps => n + (ps.moves.filter p).length
    | none => n) 0

/-- Spill moves (slot stores and reloads) of all `PreStep`s of `f` under `cfg`. -/
meta def spillMoves (cfg : Spill.Cfg) (f : Fn) : Nat :=
  movesAt (hintsOf cfg f) isSlotMove (List.range (Live.Tree.ofFn f).2.2.2.2.1)

/-- Instruction pointers along the path that takes arm `bs[i]` (`true` = then) at its `i`-th
`jnz` and stops at the first terminator. -/
meta def pathIps : List Bool → Live.Tree → List Nat
  | bs, .let_ _ ip _ _ _ k | bs, .load _ ip _ _ _ k | bs, .store _ ip _ _ _ k
  | bs, .call _ ip _ _ _ _ _ k | bs, .skip _ ip k => ip :: pathIps bs k
  | true :: bs, .jnz _ ip _ _ t _ => ip :: pathIps bs t
  | false :: bs, .jnz _ ip _ _ _ e => ip :: pathIps bs e
  | [], .jnz _ ip _ _ _ _ => [ip]
  | _, .jump _ ip _ _ _ | _, .ret _ ip _ _ | _, .exit _ ip _ _ _ | _, .stop ip => [ip]
  | bs, .group _ _ k => pathIps bs k

/-- Number of slot-direct (`.slot`) block parameter locations in the entries of `h`. -/
meta def slotPlocs (h : x64Target.toIsa.Hints) (nl : Nat) : Nat :=
  (List.range nl).foldl (fun n l => match h.entry.find? l with
    | some en => n + (en.ploc.filter fun | .slot .. => true | _ => false).length
    | none => n) 0

/-- `a + 1, …, a + n` (innermost first), handed to `body`. -/
meta def adds {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (a : V i64) :
    Nat → (List (V i64) → Expr V L rs) → Expr V L rs
  | 0, body => body []
  | n + 1, body =>
    .let_ (op2 (.add i64) (.var a) (.imm (BitVec.ofNat 64 (n + 1)))) fun (x, ()) =>
      adds a n fun xs => body (x :: xs)

/-- Fold every `x ∈ xs` into `acc` (three reads of `x` each), then continue with `k`. -/
meta def mix {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    List (V i64) → V i64 → (V i64 → Expr V L rs) → Expr V L rs
  | [], acc, k => k acc
  | x :: xs, acc, k =>
    .let_ (op2 (.xor i64) (.var acc) (.var x)) fun (y, ()) =>
    .let_ (op2 (.add i64) (.var y) (.var x)) fun (z, ()) =>
    .let_ (op2 (.xor i64) (.var z) (.var x)) fun (w, ()) => mix xs w k

meta def noSink : Spill.Cfg := { sink := false }
meta def noJoinGuard : Spill.Cfg := { joinGuard := false }
meta def noCacheHint : Spill.Cfg := { cacheHint := false }
meta def noRegEntry : Spill.Cfg := { regEntry := false }
meta def noArmEvict : Spill.Cfg := { armEvict := false }
meta def noArmX : Spill.Cfg := { armX := false }
meta def allCfgs : List Spill.Cfg :=
  [{}, .legacy, noSink, noJoinGuard, noCacheHint, noRegEntry, noArmEvict, noArmX]

/-! ## 1. `sink`: no spill store before an early return -/

/-- `x` is returned at once on the `then` arm; the `else` arm keeps it live across fourteen
heavier values, so `x` is slot-homed. -/
meta def sinkFn : Fn :=
  ⟨"sinkB5", [i64, i64], [i64], fun _ _ (a, b, ()) =>
    .let_ (op2 (.add i64) (.var a) (.imm 99)) fun (x, ()) =>
    .let_ (op2 (.cmp .eq i64) (.var b) (.imm 0)) fun (c, ()) =>
    .jnz (.var c) (.ret (.var x, ()))
      (adds b 14 fun hs => mix hs b fun z =>
        .let_ (op2 (.xor i64) (.var z) (.var x)) fun (r, ()) => .ret (.var r, ()))⟩

/-- Instruction pointers of the early-return path of `sinkFn`. -/
meta def sinkFast : List Nat := pathIps [true] (Live.Tree.ofFn sinkFn).1

#guard allCfgs.all (lowers · sinkFn)
#guard (hintsOf {} sinkFn).nslots != 0
#guard movesAt (hintsOf .legacy sinkFn) isSt sinkFast == 1
#guard movesAt (hintsOf noSink sinkFn) isSt sinkFast == 1
#guard movesAt (hintsOf {} sinkFn) isSlotMove sinkFast == 0
#guard movesAt (hintsOf { Spill.Cfg.legacy with sink := true } sinkFn) isSlotMove sinkFast == 0

/-! ## 2. `joinGuard`: a join parameter read at once arrives in a register -/

/-- Both arms define the join argument in a register; the join block reads the parameter first
thing and then keeps it live across fourteen heavier values, so it is slot-homed. -/
meta def joinFn : Fn :=
  ⟨"joinB5", [i64, i64, i64], [i64], fun _ _ (a, b, q, ()) =>
    .let_ (op2 (.cmp .eq i64) (.var b) (.imm 0)) fun (c, ()) =>
    .group (sig := [[i64]])
      (fun (_, ()) => .cons (fun (p, ()) =>
        .let_ (op2 (.add i64) (.var p) (.imm 1)) fun (u, ()) =>
        adds u 14 fun hs => mix hs u fun z =>
        .let_ (op2 (.xor i64) (.var z) (.var p)) fun (r, ()) => .ret (.var r, ())) .nil)
      (fun (j, ()) => .jnz (.var c)
        (.let_ (op2 (.add i64) (.var a) (.imm 3)) fun (v, ()) => .jump j (.var v, ()))
        (.store (t := i64) (.var a) (.var q)
          (.let_ (op2 (.mul i64) (.var a) (.var b)) fun (v, ()) => .jump j (.var v, ()))))⟩

meta def joinLabels : Nat := (Live.Tree.ofFn joinFn).2.2.2.1

#guard allCfgs.all (lowers · joinFn)
#guard slotPlocs (hintsOf .legacy joinFn) joinLabels == 1
#guard slotPlocs (hintsOf noJoinGuard joinFn) joinLabels == 1
#guard slotPlocs (hintsOf {} joinFn) joinLabels == 0

/-! ## 3. `regEntry`: a watch-scan shaped loop with a stack-free fast arm -/

/-- Watch-scan shaped loop: the fast arm continues at once, while the slow arm computes ten
heavier values, which spills loop-carried state. -/
meta def scanFn : Fn :=
  ⟨"scanB5", [i64, i64, i64], [i64], fun _ _ (p, m, q, ()) =>
    loop1 (ts := [i64, i64])
      (fun L (i, acc, ()) =>
        .let_ (op2 (.cmp .ult i64) (.var i) (.var m)) fun (c0, ()) =>
        .jnz (.var c0)
          (.let_ (op2 (.add i64) (.var p) (.var i)) fun (a, ()) =>
           .load i64 (.var a) fun v =>
           .let_ (op2 (.add i64) (.var i) (.imm 16)) fun (i2, ()) =>
           .let_ (op2 (.cmp .ult i64) (.var v) (.var m)) fun (c1, ()) =>
           .jnz (.var c1)
             (.let_ (op2 (.add i64) (.var acc) (.var v)) fun (acc', ()) =>
              .jump L (.var i2, .var acc', ()))
             (adds q 10 fun hs => mix hs acc fun z =>
              .let_ (op2 (.xor i64) (.var z) (.var v)) fun (acc', ()) =>
              .jump L (.var i2, .var acc', ())))
          (.ret (.var acc, ())))
      (fun L => .jump L (.imm 0, .imm 0, ()))⟩

/-- Instruction pointers of the fast arm of the loop body of `scanFn` (block `0`). -/
meta def scanFast : List Nat :=
  let t := (Live.Tree.ofFn scanFn).1
  pathIps [true, true] (((t.blocks.find? fun b => b.1 == 0).map (·.2.2)).getD t)

#guard allCfgs.all (lowers · scanFn)
#guard (hintsOf {} scanFn).nslots != 0
#guard scanFast.length == 9
#guard movesAt (hintsOf .legacy scanFn) isSlotMove scanFast == 1
#guard movesAt (hintsOf noRegEntry scanFn) isSlotMove scanFast == 1
#guard movesAt (hintsOf {} scanFn) isSlotMove scanFast == 0
#guard dirs {} scanFn ≤ dirs .legacy scanFn

/-! ## 4. High-pressure GPR budget guards (`joinGuard` & `regEntry`) -/

/-- Apply `mix xs` sequentially `n` times so `xs` hold high coloring weight. -/
meta def heavyMix {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (xs : List (V i64)) (acc : V i64) : Nat → (V i64 → Expr V L rs) → Expr V L rs
  | 0, k => k acc
  | n + 1, k => mix xs acc fun acc' => heavyMix xs acc' n k

/-- Join block with `11` GPR-homed live-ins (`ls`) and `5` early-read slot-homed parameters
passed immediates on both arms: `joinGuard` must promote only within the block GPR budget. -/
meta def immJoverFn : Fn :=
  ⟨"immJoverB5", [i64, i64], [i64], fun _ _ (a, b, ()) =>
    adds a 11 fun ls =>
    .let_ (op2 (.cmp .eq i64) (.var b) (.imm 0)) fun (c, ()) =>
    .group (sig := [[i64, i64, i64, i64, i64]])
      (fun (_, ()) => .cons (fun (p0, p1, p2, p3, p4, ()) =>
        .let_ (op2 (.add i64) (.var p0) (.var p1)) fun (u0, ()) =>
        .let_ (op2 (.add i64) (.var p2) (.var p3)) fun (u1, ()) =>
        .let_ (op2 (.xor i64) (.var u0) (.var p4)) fun (u2, ()) =>
        .let_ (op2 (.add i64) (.var u1) (.var u2)) fun (u3, ()) =>
        adds b 8 fun hs =>
        heavyMix hs u3 2 fun zh =>
        heavyMix ls zh 4 fun zl =>
        .let_ (op2 (.xor i64) (.var zl) (.var p0)) fun (r0, ()) =>
        .let_ (op2 (.xor i64) (.var r0) (.var p1)) fun (r1, ()) =>
        .let_ (op2 (.xor i64) (.var r1) (.var p2)) fun (r2, ()) =>
        .let_ (op2 (.xor i64) (.var r2) (.var p3)) fun (r3, ()) =>
        .let_ (op2 (.xor i64) (.var r3) (.var p4)) fun (r4, ()) =>
        .ret (.var r4, ())) .nil)
      (fun (j, ()) => .jnz (.var c)
        (.jump j (.imm 1, .imm 2, .imm 3, .imm 4, .imm 5, ()))
        (.jump j (.imm 6, .imm 7, .imm 8, .imm 9, .imm 10, ())))⟩

/-- Loop header with `2` early-read slot-homed params, heavy GPR live-ins (`ls` + `m`/`q`), and
`1` spilled live-in (`x`): `pickRegIn` must reserve GPR budget for `pickPlocs`. -/
meta def regStealFn : Fn :=
  ⟨"regStealB5", [i64, i64, i64], [i64], fun _ _ (p, m, q, ()) =>
    adds p 10 fun ls =>
    .let_ (op2 (.add i64) (.var q) (.imm 77)) fun (x, ()) =>
    loop1 (ts := [i64, i64])
      (fun L (p0, p1, ()) =>
        .let_ (op2 (.add i64) (.var p0) (.var p1)) fun (s0, ()) =>
        .let_ (op2 (.cmp .ult i64) (.var s0) (.var m)) fun (c0, ()) =>
        .jnz (.var c0)
          (.let_ (op2 (.cmp .ult i64) (.var s0) (.var q)) fun (c1, ()) =>
           .jnz (.var c1)
             (.let_ (op2 (.xor i64) (.var x) (.var s0)) fun (y, ()) =>
              .let_ (op2 (.add i64) (.var p0) (.imm 1)) fun (p0', ()) =>
              .let_ (op2 (.add i64) (.var p1) (.imm 2)) fun (p1', ()) =>
              heavyMix ls y 4 fun z =>
              .let_ (op2 (.xor i64) (.var z) (.var p0)) fun (z1, ()) =>
              .let_ (op2 (.xor i64) (.var z1) (.var p1)) fun (z2, ()) =>
              .jump L (.var z2, .var p1', ()))
             (adds q 14 fun hs =>
              heavyMix hs x 3 fun zh =>
              .jump L (.var zh, .var s0, ())))
          (.ret (.var s0, ())))
      (fun L => .jump L (.imm 1, .imm 2, ()))⟩

meta def onlyJoinGuard : Spill.Cfg :=
  { sink := false, joinGuard := true, cacheHint := false, regEntry := false }

#guard (onlyJoinGuard :: allCfgs).all (lowers · immJoverFn)
#guard slotPlocs (hintsOf {} immJoverFn) (Live.Tree.ofFn immJoverFn).2.2.2.1 ≥ 3
#guard (onlyJoinGuard :: allCfgs).all (lowers · regStealFn)

/-! ## 5. `Kissat.Plain` and `LratBytes` hot functions -/

/-- Mid-end output (`Fn.mid`) of the named `Kissat.Plain` / `LratBytes` function. -/
meta def midOf (name : Sym) : Fn :=
  match (Examples.Kissat.Plain.plainFns ++ Examples.LratBytes.lratBytesFns).find?
      fun f => f.name == name with
  | some f => f.mid x64LegalTarget
  | none => ⟨name, [], [], fun _ _ _ => .hlt⟩

/-- `f` lowers under every configuration, and the default hints need no more spill moves than
the legacy ones. -/
meta def noWorse (f : Fn) : Bool :=
  allCfgs.all (lowers · f) && spillMoves {} f ≤ spillMoves .legacy f

mutual
meta def callIpsTree : Live.Tree → List Nat
  | .let_ _ _ _ _ _ k | .load _ _ _ _ _ k | .store _ _ _ _ _ k | .skip _ _ k =>
    callIpsTree k
  | .call _ ip _ _ _ _ _ k => ip :: callIpsTree k
  | .jnz _ _ _ _ t e => callIpsTree t ++ callIpsTree e
  | .group _ bs k => callIpsTree k ++ callIpsBlocks bs
  | _ => []

meta def callIpsBlocks : Live.TreeBlocks → List Nat
  | .nil => []
  | .cons _ _ b bs => callIpsTree b ++ callIpsBlocks bs
end

meta def isCsSt (m : x64Target.toIsa.Move) : Bool :=
  match m with
  | .st _ r => x64Frame.calleeSaved.contains r
  | _ => false

meta def callCsSts (f : Fn) : Nat :=
  movesAt (hintsOf {} f) isCsSt (callIpsTree (Live.Tree.ofFn f).1)

meta structure SpillCmp where
  allOk : Bool
  defMoves : Nat
  noArmXMoves : Nat
  legMoves : Nat
  defDirs : Nat
  legDirs : Nat
  csCallStIps : List Nat
  noArmXCsCallSts : Nat

meta def cmpFn (f : Fn) : SpillCmp :=
  let (tr, _, _, _, nip, _) := Live.Tree.ofFn f
  let ips := List.range nip
  let callIps := callIpsTree tr
  let hDef := hintsOf {} f
  let hLeg := hintsOf .legacy f
  let hNoArmX := hintsOf noArmX f
  let defLow := Rega.lowerFn x64Target.toIsa hDef f.ext f
  let legLow := Rega.lowerFn x64Target.toIsa hLeg f.ext f
  let noArmXLow := Rega.lowerFn x64Target.toIsa hNoArmX f.ext f
  let restOk := [noSink, noJoinGuard, noCacheHint, noRegEntry, noArmEvict].all (lowers · f)
  let ok? {α β} : Except α β → Bool | .ok _ => true | .error _ => false
  { allOk := ok? defLow && ok? legLow && ok? noArmXLow && restOk
    defMoves := movesAt hDef isSlotMove ips
    noArmXMoves := movesAt hNoArmX isSlotMove ips
    legMoves := movesAt hLeg isSlotMove ips
    defDirs := match defLow with | .ok c => c.length | .error _ => 0
    legDirs := match legLow with | .ok c => c.length | .error _ => 0
    csCallStIps := callIps.filter fun ip =>
      match hDef.pre.find? ip with
      | some ps => (ps.moves.filter isCsSt).length != 0
      | none => false
    noArmXCsCallSts := movesAt hNoArmX isCsSt callIps }

meta def propLitCmp : SpillCmp := cmpFn (midOf "plain_prop_lit")

#guard propLitCmp.allOk && propLitCmp.defMoves < propLitCmp.legMoves

meta def watchPushCmp : SpillCmp := cmpFn (midOf "plain_watch_push")
meta def backtrackCmp : SpillCmp := cmpFn (midOf "plain_backtrack")
meta def heapDownCmp : SpillCmp := cmpFn (midOf "plain_heap_down")
meta def addClauseCmp : SpillCmp := cmpFn (midOf "plain_add_clause")
meta def analyzeLitCmp : SpillCmp := cmpFn (midOf "plain_analyze_lit")
meta def sec5Cmps : List SpillCmp :=
  [watchPushCmp, backtrackCmp, heapDownCmp, addClauseCmp, analyzeLitCmp]

-- Hot `Kissat.Plain` and `LratBytes` loops pass `noWorse` (`defMoves <= legMoves`) across all
-- `Spill.Cfg` variants.
#guard sec5Cmps.all fun c => c.allOk && c.defMoves ≤ c.legMoves
#guard (sec5Cmps.foldl (fun a c => a + c.defMoves) 0) ≤
  (sec5Cmps.foldl (fun a c => a + c.legMoves) 0)
#guard Examples.LratBytes.lratBytesFns.all fun f => noWorse (f.mid x64LegalTarget)

/-! ## 6. Leaf & low-call caller-saved register preference -/

/-- Leaf function with 3 returns avoids saving callee-saved registers. -/
meta def leafFn : Fn :=
  ⟨"leafB5", [i64, i64], [i64], fun _ _ (a, b, ()) =>
    .let_ (op2 (.cmp .eq i64) (.var a) (.imm 0)) fun (c1, ()) =>
    .jnz (.var c1) (.ret (.imm 1, ()))
      (.let_ (op2 (.cmp .eq i64) (.var b) (.imm 0)) fun (c2, ()) =>
       .jnz (.var c2) (.ret (.imm 2, ()))
         (.let_ (op2 (.add i64) (.var a) (.var b)) fun (s, ()) =>
          .ret (.var s, ())))⟩

#guard allCfgs.all (lowers · leafFn)
#guard (hintsOf {} leafFn).saved.isEmpty
#guard (hintsOf {} (midOf "plain_assign")).saved.isEmpty
#guard let h := hintsOf {} (midOf "plain_add_clause"); h.nslots == 0 || h.saved.length ≤ 2

/-! ## 7. Cold-arm live-range splitting, `evIn`, and CS cache survival -/

/-- A split variable arriving evicted at `.jump` is not reloaded when dead at target `j`. -/
meta def deadJumpEvFn : Fn :=
  ⟨"deadJumpEvB5", [i64, i64], [i64], fun _ _ (a, b, ()) =>
    .let_ (op2 (.cmp .eq i64) (.var a) (.imm 0)) fun (c0, ()) =>
    .jnz (.var c0) (.ret (.imm 0, ()))
      (.let_ (op2 (.add i64) (.var a) (.imm 7)) fun (x, ()) =>
       .group (sig := [[i64]])
         (fun (_, ()) => .cons (fun (p, ()) => .ret (.var p, ())) .nil)
         (fun (j, ()) =>
           .let_ (op2 (.cmp .eq i64) (.var b) (.imm 0)) fun (c1, ()) =>
           .jnz (.var c1)
             (.call (as := [i64]) (bs := [i64]) "extFn" (.var a, ()) fun (_, ()) =>
               .jnz (.var c1)
                 (.jump j (.imm 1, ()))
                 (.let_ (op2 (.add i64) (.var x) (.imm 3)) fun (w, ()) => .ret (.var w, ())))
             (.let_ (op2 (.add i64) (.var x) (.var b)) fun (y, ()) =>
              .let_ (op2 (.xor i64) (.var y) (.var x)) fun (z, ()) =>
              .let_ (op2 (.add i64) (.var z) (.var x)) fun (z2, ()) =>
              .jump j (.var z2, ()))))⟩

/-- Last IP on the dead `.jump` arm after the call in `deadJumpEvFn`. -/
meta def deadJumpArmIp : List Nat :=
  let all := pathIps [false, true, true] (Live.Tree.ofFn deadJumpEvFn).1
  match all.reverse with | ip :: _ => [ip] | [] => []

#guard allCfgs.all (lowers · deadJumpEvFn)
#guard movesAt (hintsOf {} deadJumpEvFn) isSlotMove deadJumpArmIp == 0

/-- Outer loop with high-use `x` (`uOut ≥ 8`) wrapping a high-pressure inner loop where `x` is
unused: `tryEvictSplit` keeps `x` in a GPR outside the inner loop and evicts inside it. -/
meta def coldEvFn : Fn :=
  ⟨"coldEvB5", [i64, i64, i64], [i64], fun _ _ (a, m, q, ()) =>
    .let_ (op2 (.add i64) (.var a) (.imm 11)) fun (x, ()) =>
    loop1 (ts := [i64, i64])
      (fun L0 (i, acc, ()) =>
        .let_ (op2 (.cmp .ult i64) (.var i) (.var m)) fun (c0, ()) =>
        .jnz (.var c0)
          (.let_ (op2 (.xor i64) (.var acc) (.var x)) fun (u0, ()) =>
           .let_ (op2 (.add i64) (.var u0) (.var x)) fun (u1, ()) =>
           .let_ (op2 (.xor i64) (.var u1) (.var x)) fun (u2, ()) =>
           .let_ (op2 (.add i64) (.var u2) (.var x)) fun (u3, ()) =>
           .let_ (op2 (.xor i64) (.var u3) (.var x)) fun (u4, ()) =>
           .let_ (op2 (.add i64) (.var u4) (.var x)) fun (u5, ()) =>
           .let_ (op2 (.xor i64) (.var u5) (.var x)) fun (u6, ()) =>
           .let_ (op2 (.add i64) (.var u6) (.var x)) fun (u7, ()) =>
           loop1 (ts := [i64, i64])
             (fun L1 (k, s, ()) =>
               .let_ (op2 (.cmp .ult i64) (.var k) (.var q)) fun (c1, ()) =>
               .jnz (.var c1)
                 (adds q 13 fun hs => heavyMix hs s 2 fun s' =>
                  .let_ (op2 (.add i64) (.var k) (.imm 1)) fun (k', ()) =>
                  .jump L1 (.var k', .var s', ()))
                 (.let_ (op2 (.xor i64) (.var s) (.var x)) fun (acc', ()) =>
                  .let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
                  .jump L0 (.var i', .var acc', ())))
             (fun L1 => .jump L1 (.imm 0, .var u7, ())))
          (.ret (.var acc, ())))
      (fun L0 => .jump L0 (.imm 0, .imm 0, ()))⟩

#guard allCfgs.all (lowers · coldEvFn)
-- The outer-loop ALU reads of a spilled `x` now fold into slot operands (jump live-ins no longer
-- count as region reuse), so `regEntry` saves no moves here; keep the guard against legacy.
#guard spillMoves {} coldEvFn ≤ spillMoves noRegEntry coldEvFn
#guard spillMoves {} coldEvFn < spillMoves .legacy coldEvFn

meta def zeroTablesCmp : SpillCmp := cmpFn (midOf "plain_zero_tables")
meta def sortTmpCmp : SpillCmp := cmpFn (midOf "plain_sort_tmp")
meta def shrinkBlkCmp : SpillCmp := cmpFn (midOf "plain_shrink_blk")
meta def analyzeCmp : SpillCmp := cmpFn (midOf "plain_analyze")
meta def minShrinkCmp : SpillCmp := cmpFn (midOf "plain_min_shrink")
meta def sweepCmp : SpillCmp := cmpFn (midOf "plain_sweep")
meta def sec8Cmps : List SpillCmp :=
  [zeroTablesCmp, sortTmpCmp, shrinkBlkCmp, analyzeCmp, minShrinkCmp, sweepCmp]

-- Heavy live `Kissat.Plain` loops keep lowering cleanly across every config:
-- * `plain_sweep` (`83 < 111`, eliminating `noArmX`'s callee-saved `.call` save),
--   `plain_zero_tables` (`37 < 46`), `plain_sort_tmp` (`9 < 11`), `plain_analyze` (`11 < 13`),
--   and `plain_min_shrink` (`2 < 3`) satisfy `noWorse`.
-- * `plain_shrink_blk` (`39` vs `legacy=37`, `defDirs=447 <= legDirs=451`) lowers cleanly.
#guard sec8Cmps.all (·.allOk)
#guard [zeroTablesCmp, sortTmpCmp, analyzeCmp, minShrinkCmp, sweepCmp].all fun c =>
  c.noArmXMoves ≤ c.legMoves && c.defMoves ≤ c.legMoves
#guard shrinkBlkCmp.defMoves ≤ 39
#guard shrinkBlkCmp.defDirs ≤ shrinkBlkCmp.legDirs + 2
#guard (sec8Cmps.foldl (fun a c => a + c.defMoves) 0) ≤
  (sec8Cmps.foldl (fun a c => a + c.legMoves) 0)

/-! ## 8. Flag-to-slot jump argument lowering (`jumpSlotMoves` `.flag cc` -> `.slot s`) -/

/-- A flag-homed boolean condition (`.flag cc`) passed as a `.jump` argument to a block whose
parameter `ploc` is `.slot s .w64`. -/
meta def flagJumpSlotFn : Fn :=
  ⟨"flagJumpSlotB5", [i64, i64, i64], [i64], fun _ _ (a, b, q, ()) =>
    .group (sig := [[.bool]])
      (fun (_, ()) => .cons (fun (p, ()) =>
        adds b 14 fun hs => heavyMix hs b 2 fun z =>
        .call (as := [i64]) (bs := [i64]) "extFn" (.var z, ()) fun (u, ()) =>
        .jnz (.var p) (.ret (.var u, ())) (.ret (.imm 0, ()))) .nil)
      (fun (j, ()) =>
        .let_ (op2 (.cmp .eq i64) (.var a) (.imm 0)) fun (c0, ()) =>
        .jnz (.var c0)
          (.let_ (op2 (.cmp .ult i64) (.var b) (.var q)) fun (c, ()) =>
           .jump j (.var c, ()))
          (.store (t := i64) (.var a) (.var q)
            (.jump j (.imm false, ()))))⟩

#guard allCfgs.all (lowers · flagJumpSlotFn)
#guard (compile x64Target.toIsa x64LegalTarget [flagJumpSlotFn]
  [Fn.computeHints x64Target.toIsa x64LegalTarget flagJumpSlotFn]).isOk = true

/-! ## 9. Two-hop affinity & loop block-parameter weighting (`S11`/`S15`) -/

/-- Single-use `.load` feeding `.add` feeding `.call` arg 0 coalesces cleanly to `%rdi`. -/
meta def twoHopLoadCallFn : Fn :=
  ⟨"twoHopLoadCallB5", [i64, i64], [i64], fun _ _ (p, off, ()) =>
    .load i64 (.var p) fun v =>
    .let_ (op2 (.add i64) (.var v) (.var off)) fun (arg0, ()) =>
    .call (as := [i64]) (bs := [i64]) "extFn" (.var arg0, ()) fun (r, ()) =>
    .ret (.var r, ())⟩

/-- Loop-carried counter `i` stays in a GPR (`0` slot-direct `ploc`s) when competing with
temporary loop computations. -/
meta def loopBpGprFn : Fn :=
  ⟨"loopBpGprB5", [i64, i64], [i64], fun _ _ (n, q, ()) =>
    loop1 (ts := [i64, i64])
      (fun L (i, acc, ()) =>
        .let_ (op2 (.cmp .ult i64) (.var i) (.var n)) fun (c, ()) =>
        .jnz (.var c)
          (.load i64 (.var q) fun x =>
           .let_ (op2 (.add i64) (.var acc) (.var x)) fun (acc', ()) =>
           .let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
           .jump L (.var i', .var acc', ()))
          (.ret (.var acc, ())))
      (fun L => .jump L (.imm 0, .imm 0, ()))⟩

#guard lowers {} twoHopLoadCallFn
#guard (hintsOf {} twoHopLoadCallFn).dest.find? 2 == some (.gpr .rdi)
#guard lowers {} loopBpGprFn
#guard slotPlocs (hintsOf {} loopBpGprFn) (Live.Tree.ofFn loopBpGprFn).2.2.2.1 == 0

/-! ## 10. Arm-scoped eviction (`armEvict`) -/

/-- Loop whose fast arm loads through the invariant `x` three times, while the slow arm computes
fourteen heavier values without reading `x`: `x` is spilled unless it is evicted only inside the
slow arm (and reloaded at its exit). -/
meta def armEvFn : Fn :=
  ⟨"armEvB5", [i64, i64, i64], [i64], fun _ _ (a, m, q, ()) =>
    .let_ (op2 (.add i64) (.var a) (.imm 11)) fun (x, ()) =>
    loop1 (ts := [i64, i64])
      (fun L (i, acc, ()) =>
        .let_ (op2 (.cmp .ult i64) (.var i) (.var m)) fun (c0, ()) =>
        .jnz (.var c0)
          (.let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
           .let_ (op2 (.cmp .eq i64) (.var acc) (.var q)) fun (c1, ()) =>
           .jnz (.var c1)
             (adds q 14 fun hs => heavyMix hs acc 2 fun s => .jump L (.var i', .var s, ()))
             (.load i64 (.var x) fun v0 =>
              .let_ (op2 (.add i64) (.var x) (.imm 8)) fun (x8, ()) =>
              .load i64 (.var x8) fun v1 =>
              .let_ (op2 (.add i64) (.var x) (.imm 16)) fun (x16, ()) =>
              .load i64 (.var x16) fun v2 =>
              .let_ (op2 (.add i64) (.var acc) (.var v0)) fun (a1, ()) =>
              .let_ (op2 (.add i64) (.var a1) (.var v1)) fun (a2, ()) =>
              .let_ (op2 (.add i64) (.var a2) (.var v2)) fun (a3, ()) =>
              .jump L (.var i', .var a3, ())))
          (.ret (.var acc, ())))
      (fun L => .jump L (.imm 0, .imm 0, ()))⟩

/-- Instruction pointers of the fast arm of the loop body of `armEvFn` (block `0`). -/
meta def armEvFast : List Nat :=
  let t := (Live.Tree.ofFn armEvFn).1
  pathIps [true, false] (((t.blocks.find? fun b => b.1 == 0).map (·.2.2)).getD t)

#guard allCfgs.all (lowers · armEvFn)
#guard armEvFast.length == 14
#guard movesAt (hintsOf {} armEvFn) isSlotMove armEvFast == 0
#guard movesAt (hintsOf noArmEvict armEvFn) isSlotMove armEvFast ≥ 1
#guard movesAt (hintsOf .legacy armEvFn) isSlotMove armEvFast ≥ 1

/-! ## 11. Wave P1 Oracle Upgrades (`csCost`, `cheapSplit`, `fitBlockGprs`) -/

/-- Multi-return function (`8` `.ret` sites, like `CondThreadOpt` output) with a call-crossing
incoming arg `y` kept in a callee-saved register instead of spilling in the prologue. -/
meta def multiRetCsFn : Fn :=
  ⟨"multiRetCsB5", [i64, i64], [i64], fun V L (a, y, ()) =>
    let rec br : Nat → V i64 → Expr V L [i64]
      | 0, acc => .ret (.var acc, ())
      | n + 1, acc =>
        .let_ (op2 (.cmp .eq i64) (.var acc) (.imm (BitVec.ofNat 64 n))) fun (c, ()) =>
        .jnz (.var c)
          (.let_ (op2 (.add i64) (.var acc) (.var y)) fun (r, ()) => .ret (.var r, ()))
          (br n acc)
    .call (as := [i64]) (bs := [i64]) "extFn" (.var a, ()) fun (r0, ()) =>
    .call (as := [i64]) (bs := [i64]) "extFn" (.var r0, ()) fun (r1, ()) =>
    .let_ (op2 (.add i64) (.var r1) (.var y)) fun (s0, ()) =>
    .let_ (op2 (.xor i64) (.var s0) (.var y)) fun (s1, ()) =>
    br 7 s1⟩

#guard allCfgs.all (lowers · multiRetCsFn)
#guard !(hintsOf {} multiRetCsFn).saved.isEmpty
#guard (hintsOf {} multiRetCsFn).nslots == 0

/-- Loop-crossing variable with cheap def/call splitting around a cold loop call lowers cleanly
even when callee-saved registers are saturated by heavier loop-carried variables. -/
meta def loopCallSplitFn : Fn :=
  ⟨"loopCallSplitB5", [i64, i64, i64], [i64], fun _ _ (a, m, q, ()) =>
    .let_ (op2 (.add i64) (.var a) (.imm 5)) fun (inv, ()) =>
    adds m 6 fun cs =>
    loop1 (ts := [i64, i64])
      (fun L (i, acc, ()) =>
        .let_ (op2 (.cmp .ult i64) (.var i) (.var m)) fun (c0, ()) =>
        .jnz (.var c0)
          (.let_ (op2 (.cmp .eq i64) (.var i) (.var q)) fun (c1, ()) =>
           .jnz (.var c1)
             (.call (as := [i64]) (bs := [i64]) "extFn" (.var q, ()) fun (r, ()) =>
              .let_ (op2 (.add i64) (.var r) (.var inv)) fun (acc', ()) =>
              .let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
              .jump L (.var i', .var acc', ()))
             (heavyMix cs acc 4 fun z =>
              .let_ (op2 (.add i64) (.var z) (.var inv)) fun (z', ()) =>
              .let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
              .jump L (.var i', .var z', ())))
          (.ret (.var acc, ())))
      (fun L => .jump L (.imm 0, .imm 0, ()))⟩

#guard allCfgs.all (lowers · loopCallSplitFn)
#guard (compile x64Target.toIsa x64LegalTarget [loopCallSplitFn]
  [Fn.computeHints x64Target.toIsa x64LegalTarget loopCallSplitFn]).isOk = true

/-- Block with `9` parameters (`3` spilled with swapped slots) plus heavy live-across pressure:
`fitBlockGprs` caps active entry GPRs so `pickPlocs` never runs out of GPRs. -/
meta def highPressureBlockFn : Fn :=
  ⟨"highPressureBlockB5", [i64, i64], [i64], fun _ _ (a, b, ()) =>
    adds a 5 fun ls =>
    .group (sig := [[i64, i64, i64, i64, i64, i64, i64, i64, i64]])
      (fun (_, ()) => .cons (fun (p0, p1, p2, p3, p4, p5, p6, p7, p8, ()) =>
        adds b 8 fun hs =>
        heavyMix hs p0 2 fun z0 =>
        .let_ (op2 (.add i64) (.var z0) (.var p1)) fun (s1, ()) =>
        .let_ (op2 (.add i64) (.var s1) (.var p2)) fun (s2, ()) =>
        .let_ (op2 (.add i64) (.var s2) (.var p3)) fun (s3, ()) =>
        .let_ (op2 (.add i64) (.var s3) (.var p4)) fun (s4, ()) =>
        .let_ (op2 (.add i64) (.var s4) (.var p5)) fun (s5, ()) =>
        .let_ (op2 (.add i64) (.var s5) (.var p6)) fun (s6, ()) =>
        .let_ (op2 (.add i64) (.var s6) (.var p7)) fun (s7, ()) =>
        .let_ (op2 (.add i64) (.var s7) (.var p8)) fun (s8, ()) =>
        heavyMix ls s8 3 fun z1 =>
        .ret (.var z1, ())) .nil)
      (fun (j, ()) =>
        .let_ (op2 (.cmp .eq i64) (.var a) (.imm 0)) fun (c, ()) =>
        .jnz (.var c)
          (adds a 9 fun xs => match xs with
            | [x0, x1, x2, x3, x4, x5, x6, x7, x8] =>
              .jump j (.var x0, .var x1, .var x2, .var x3, .var x4,
                .var x5, .var x6, .var x7, .var x8, ())
            | _ => .ret (.var b, ()))
          (adds b 9 fun ys => match ys with
            | [y0, y1, y2, y3, y4, y5, y6, y7, y8] =>
              .jump j (.var y8, .var y7, .var y6, .var y5, .var y4,
                .var y3, .var y2, .var y1, .var y0, ())
            | _ => .ret (.var a, ())))⟩

#guard allCfgs.all (lowers · highPressureBlockFn)
#guard (compile x64Target.toIsa x64LegalTarget [highPressureBlockFn]
  [Fn.computeHints x64Target.toIsa x64LegalTarget highPressureBlockFn]).isOk = true

/-! ## 12. Callee-saved `.call` eviction & `tryLoopBoundarySplit` profitability guards -/

-- `plain_sweep` and `plain_zero_tables` emit `0` callee-saved `.call`-site `.st` moves across
-- all calls (`armX` eliminates the extra `noArmX` `.call` save in `plain_sweep`).
#guard sweepCmp.csCallStIps.isEmpty
#guard sweepCmp.noArmXCsCallSts == 1
#guard zeroTablesCmp.csCallStIps.isEmpty
#guard sweepCmp.defMoves ≤ 83
#guard zeroTablesCmp.defMoves ≤ 37
#guard sortTmpCmp.defMoves ≤ 9
#guard analyzeCmp.defMoves ≤ 11

/-- Call-crossing invariant `x` with a cold high-pressure arm (`bk != none`) stays in a
callee-saved GPR and emits `0` `.st` evictions across subsequent `.call` sites. -/
meta def csCallArmEvFn : Fn :=
  ⟨"csCallArmEvB5", [i64, i64, i64], [i64], fun _ _ (a, m, q, ()) =>
    .let_ (op2 (.add i64) (.var a) (.imm 13)) fun (x, ()) =>
    .let_ (op2 (.cmp .eq i64) (.var m) (.imm 0)) fun (c, ()) =>
    .jnz (.var c)
      (.call (as := [i64]) (bs := [i64]) "extFn" (.var q, ()) fun (r0, ()) =>
       .call (as := [i64]) (bs := [i64]) "extFn" (.var r0, ()) fun (r1, ()) =>
       .let_ (op2 (.add i64) (.var r1) (.var x)) fun (s0, ()) =>
       .call (as := [i64]) (bs := [i64]) "extFn" (.var s0, ()) fun (r2, ()) =>
       .let_ (op2 (.xor i64) (.var r2) (.var x)) fun (s1, ()) =>
       .ret (.var s1, ()))
      (adds q 14 fun hs => heavyMix hs q 3 fun zh =>
       .let_ (op2 (.xor i64) (.var zh) (.var x)) fun (s2, ()) => .ret (.var s2, ()))⟩

#guard allCfgs.all (lowers · csCallArmEvFn)
#guard !(hintsOf {} csCallArmEvFn).saved.isEmpty
#guard callCsSts csCallArmEvFn == 0

/-- Single-use post-loop variable `x` live across a high-pressure loop with two exit paths does
not trigger an unprofitable `tryLoopBoundarySplit`. -/
meta def noBadLoopSplitFn : Fn :=
  ⟨"noBadLoopSplitB5", [i64, i64, i64], [i64], fun _ _ (a, m, q, ()) =>
    .let_ (op2 (.add i64) (.var a) (.imm 19)) fun (x, ()) =>
    .group (sig := [[i64], [i64, i64]])
      (fun (doneL, loopL, ()) =>
        .cons (fun (acc, ()) =>
          .let_ (op2 (.add i64) (.var acc) (.var x)) fun (res, ()) =>
          .ret (.var res, ()))
        (.cons (fun (i, acc, ()) =>
          .let_ (op2 (.cmp .ult i64) (.var i) (.var m)) fun (c0, ()) =>
          .jnz (.var c0)
            (adds q 14 fun hs => heavyMix hs acc 2 fun s =>
             .let_ (op2 (.cmp .eq i64) (.var s) (.var q)) fun (c1, ()) =>
             .jnz (.var c1)
               (.jump doneL (.var s, ()))
               (.let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
                .jump loopL (.var i', .var s, ())))
            (.jump doneL (.var acc, ()))) .nil))
      (fun (_, loopL, ()) => .jump loopL (.imm 0, .imm 0, ()))⟩

#guard allCfgs.all (lowers · noBadLoopSplitFn)
#guard spillMoves {} noBadLoopSplitFn ≤ spillMoves .legacy noBadLoopSplitFn

end LeanQbeTest.T.SpillB5Test
