module

public import LeanQbe.T.Amd64.Targ
public import LeanQbe.T.Examples.Kissat.FullM4
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Main
public import LeanQbe.T.Spill
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM4
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.Main
meta import LeanQbe.T.Spill

/-!
# Train B5-1 Spill-Placement Heuristics on x64 (`Spill.Cfg`)

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
5. `FullM4` / `LratBytes` hot functions lower under every configuration, and the default hints
   need no more spill moves than the legacy ones (strictly fewer on `full_prop_lit_raw`). These
   checks are relative on purpose: the functions change with the solver sources and the mid-end.

The synthetic functions are lowered as written (no mid-end), so their shape is fixed.
-/

set_option autoImplicit false

@[expose] public section

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
meta def allCfgs : List Spill.Cfg := [{}, .legacy, noSink, noJoinGuard, noCacheHint, noRegEntry]

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

/-! ## 5. `FullM4` and `LratBytes` hot functions -/

/-- Mid-end output (`Fn.mid`) of the named `FullM4` / `LratBytes` function. -/
meta def midOf (name : Sym) : Fn :=
  match (Examples.Kissat.FullM4.m4Fns ++ Examples.LratBytes.lratBytesFns).find?
      fun f => f.name == name with
  | some f => f.mid x64LegalTarget
  | none => ⟨name, [], [], fun _ _ _ => .hlt⟩

/-- `f` lowers under every configuration, and the default hints need no more spill moves than
the legacy ones. -/
meta def noWorse (f : Fn) : Bool :=
  allCfgs.all (lowers · f) && spillMoves {} f ≤ spillMoves .legacy f

meta def propLitRaw : Fn := midOf "full_prop_lit_raw"

#guard noWorse propLitRaw
#guard spillMoves {} propLitRaw < spillMoves .legacy propLitRaw
#guard ["full_watch_push", "full_shrink_blk", "full_bva_hop1", "full_queue_mtf",
  "full_analyze_lit"].all fun n => noWorse (midOf n)
#guard Examples.LratBytes.lratBytesFns.all fun f => noWorse (f.mid x64LegalTarget)

end LeanQbeTest.T.SpillB5Test
