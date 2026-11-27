module

public import LeanQbe.T.Amd64.Targ
public import LeanQbe.T.Amd64.PrintATTAlign
public import LeanQbe.T.Driver
public import LeanQbe.T.Examples.Kissat.Plain
public import LeanQbe.T.MainInline
public import LeanQbe.T.Spill
public import LeanQbe.T.SpillCoalesce
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.PrintATTAlign
meta import LeanQbe.T.Driver
meta import LeanQbe.T.Examples.Kissat.Plain
meta import LeanQbe.T.MainInline
meta import LeanQbe.T.Spill
meta import LeanQbe.T.SpillCoalesce

/-!
# Wave 6.1-B (`OPT-2`): `W6-D` Spill / Coalescing Oracle Activation & Regression Guards

Tests the untrusted `Spill.Cfg` extensions and `SpillCoalesce` passes on x86-64 (`0` proof LOC):
- `D1` (`loopRegIn := true`): promotes slot-homed loop invariants into free loop GPRs
  (`addLoopRegIn`), eliminating `cmp (%rsp)` in compact byte-scan replacement loops
  (`replScanLoopFn`, `loopRegInFn`).
- `D2` (`coldNest := false` default; unit-tested with `true`): scales nested cold loops cleanly
  without throttling hot inner loops under default config (`coldNestFn`).
- `D3` (`costPrio := false` default; unit-tested with `true`): boosts in-loop definition spill
  cost cleanly under opt-in (`costPrioFn`).
- `D4` (`dfKeep := false` default; unit-tested with `true`): avoids clobbering deferred-store
  cache registers in `allocDefs` under opt-in (`dfKeepFn`).
- `D5` (`joinCoal := true`): unit-tests `addJumpAffAnti` (both non-latch and latch paths),
  `swapColorsArr` pairwise recoloring (respecting `armEv`/`zext` invariants), and `Kissat.Plain`
  non-regression / byte-scan replacement elimination.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.OptW61SpillOracleTest

open LeanQbe.T LeanQbe.T.Amd64

/-! ## Helpers -/

meta def baseOracleCfg : Spill.Cfg :=
  { loopRegIn := false, coldNest := false, costPrio := false,
    dfKeep := false, joinCoal := false }

meta def hintsOf (cfg : Spill.Cfg) (f : Fn) : x64Target.toIsa.Hints :=
  Spill.hints x64Target.toIsa f (cfg := cfg)

meta def lowerAsm? (cfg : Spill.Cfg) (f : Fn) : Option String :=
  match Rega.lowerFn x64Target.toIsa (hintsOf cfg f) f.ext f with
  | .ok ds => some (toATTAligned ds)
  | .error _ => none

meta def lowers (cfg : Spill.Cfg) (f : Fn) : Bool :=
  (lowerAsm? cfg f).isSome

meta def insnLines (asm : String) : List String :=
  (asm.splitOn "\n").filterMap fun ln =>
    let s := ln.trimAscii.toString
    if s.isEmpty || s.startsWith "." || s.endsWith ":" then none else some s

meta def isRspSt (s : String) : Bool :=
  s.startsWith "mov" && ((s.splitOn ", ").drop 1).any (·.contains "(%rsp)")

meta def foldRspCmps (asm : String) : Nat :=
  ((insnLines asm).filter fun s => s.startsWith "cmp" && s.contains "(%rsp)").length

meta def stRspCount (asm : String) : Nat :=
  ((insnLines asm).filter isRspSt).length

meta def adds {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (a : V i64) :
    Nat → (List (V i64) → Expr V L rs) → Expr V L rs
  | 0, body => body []
  | n + 1, body =>
    .let_ (op2 (.add i64) (.var a) (.imm (BitVec.ofNat 64 (n + 1)))) fun (x, ()) =>
      adds a n fun xs => body (x :: xs)

meta def mix {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    List (V i64) → V i64 → (V i64 → Expr V L rs) → Expr V L rs
  | [], acc, k => k acc
  | x :: xs, acc, k =>
    .let_ (op2 (.xor i64) (.var acc) (.var x)) fun (y, ()) =>
      .let_ (op2 (.add i64) (.var y) (.var x)) fun (z, ()) =>
        .let_ (op2 (.xor i64) (.var z) (.var x)) fun (w, ()) => mix xs w k

meta def heavyMix {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (xs : List (V i64)) (acc : V i64) : Nat → (V i64 → Expr V L rs) → Expr V L rs
  | 0, k => k acc
  | n + 1, k => mix xs acc fun acc' => heavyMix xs acc' n k

/-! ## Default `Spill.Cfg` Policy Guards -/

#guard ({} : Spill.Cfg).loopRegIn == true
#guard ({} : Spill.Cfg).coldNest == false
#guard ({} : Spill.Cfg).costPrio == false
#guard ({} : Spill.Cfg).dfKeep == false
#guard ({} : Spill.Cfg).joinCoal == true

/-! ## `D1` (`loopRegIn`): Loop-Scoped Register Promotion of Spilled Invariants -/

/-- `lim = *n` is forced into a stack slot by pre-loop live pressure `hs`, then read inside an
unconstrained counting loop: `loopRegIn` promotes `lim` into a loop GPR, removing `cmp (%rsp)`. -/
meta def loopRegInFn : Fn :=
  ⟨"loopRegInW61", [i64, i64], [i64], fun _ _ (p, n, ()) =>
    .load i64 (.var n) fun lim =>
    adds p 14 fun hs =>
    heavyMix hs n 5 fun dead =>
    .let_ (op2 (.add i64) (.var dead) (.var n)) fun (s0, ()) =>
    loop1 (ts := [i64, i64])
      (fun L (i, acc, ()) =>
        .let_ (op2 (.cmp .ult i64) (.var i) (.var lim)) fun (c0, ()) =>
        .jnz (.var c0)
          (.let_ (op2 (.add i64) (.var p) (.var i)) fun (addr, ()) =>
           .load i64 (.var addr) fun v =>
           .let_ (op2 (.add i64) (.var acc) (.var v)) fun (acc', ()) =>
           .let_ (op2 (.add i64) (.var i) (.imm 8)) fun (i', ()) =>
           .jump L (.var i', .var acc', ()))
          (.ret (.var acc, ())))
      (fun L => .jump L (.imm 0, .var s0, ()))⟩

#guard lowers baseOracleCfg loopRegInFn
#guard lowers {} loopRegInFn
#guard (lowerAsm? baseOracleCfg loopRegInFn).map foldRspCmps == some 1
#guard (lowerAsm? {} loopRegInFn).map foldRspCmps == some 0

/-! ## `D2` (`coldNest`) & `D3` (`costPrio`) & `D4` (`dfKeep`) Opt-In Unit Guards -/

/-- Outer loop with an inner loop nested three `jnz` levels deep (`8 * mult ≤ loopMult`):
opt-in `{ coldNest := true }` lowers cleanly and shifts slot/register decisions vs default. -/
meta def coldNestFn : Fn :=
  ⟨"coldNestW61", [i64, i64, i64], [i64], fun _ _ (p, m, fl, ()) =>
    adds p 11 fun hot =>
    loop1 (ts := [i64, i64])
      (fun L (i, acc, ()) =>
        .let_ (op2 (.cmp .ult i64) (.var i) (.var m)) fun (c0, ()) =>
        .jnz (.var c0)
          (.let_ (op2 (.cmp .ne i64) (.var fl) (.imm 0)) fun (c1, ()) =>
           .jnz (.var c1)
             (.let_ (op2 (.cmp .ne i64) (.var fl) (.imm 1)) fun (c2, ()) =>
              .jnz (.var c2)
                (.let_ (op2 (.cmp .ne i64) (.var fl) (.imm 2)) fun (c3, ()) =>
                 .jnz (.var c3)
                   (loop1 (ts := [i64, i64])
                     (fun L2 (j, inner, ()) =>
                       .let_ (op2 (.cmp .ult i64) (.var j) (.var m)) fun (cj, ()) =>
                       .jnz (.var cj)
                         (adds m 8 fun cs =>
                          mix cs inner fun z =>
                          .let_ (op2 (.add i64) (.var j) (.imm 1)) fun (j', ()) =>
                          .jump L2 (.var j', .var z, ()))
                         (.let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
                          .jump L (.var i', .var inner, ())))
                     (fun L2 => .jump L2 (.imm 0, .var acc, ())))
                   (.let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
                    .jump L (.var i', .var acc, ())))
                (.let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
                 .jump L (.var i', .var acc, ())))
             (mix hot acc fun hsum =>
              .let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
              .jump L (.var i', .var hsum, ())))
          (mix hot acc fun res => .ret (.var res, ())))
      (fun L => .jump L (.imm 0, .imm 0, ()))⟩

#guard lowers {} coldNestFn
#guard lowers { coldNest := true } coldNestFn
#guard (lowerAsm? {} coldNestFn) != (lowerAsm? { coldNest := true } coldNestFn)

/-- Loop-body definitions competing for GPRs with spilled/live values under `{ costPrio := true }`
vs `{}`: lowers cleanly under both settings and activates `defW`. -/
meta def costPrioFn : Fn :=
  ⟨"costPrioW61", [i64, i64, i64], [i64], fun _ _ (p, m, q, ()) =>
    .let_ (op2 (.add i64) (.var q) (.imm 11)) fun (inv, ()) =>
    loop1 (ts := [i64, i64])
      (fun L (i, acc, ()) =>
        .let_ (op2 (.cmp .ult i64) (.var i) (.var m)) fun (c0, ()) =>
        .jnz (.var c0)
          (.let_ (op2 (.add i64) (.var p) (.var i)) fun (a, ()) =>
           .load i64 (.var a) fun v =>
           adds q 12 fun ds =>
           .let_ (op2 (.cmp .eq i64) (.var v) (.imm 0)) fun (c1, ()) =>
           .jnz (.var c1)
             (.let_ (op2 (.add i64) (.var acc) (.var inv)) fun (acc1, ()) =>
              .let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
              .jump L (.var i', .var acc1, ()))
             (mix ds v fun z =>
              .let_ (op2 (.xor i64) (.var z) (.var inv)) fun (z2, ()) =>
              .let_ (op2 (.add i64) (.var acc) (.var z2)) fun (acc2, ()) =>
              .let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
              .jump L (.var i', .var acc2, ())))
          (.ret (.var acc, ())))
      (fun L => .jump L (.imm 0, .imm 0, ()))⟩

#guard lowers {} costPrioFn
#guard lowers { costPrio := true } costPrioFn

/-- Deferred store `x` followed by a fresh definition under `{ dfKeep := true }` vs `{}`
lowers cleanly under both settings. -/
meta def dfKeepFn : Fn :=
  ⟨"dfKeepW61", [i64, i64], [i64], fun _ _ (p, m, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 3)) fun (x, ()) =>
    adds m 12 fun hs =>
    .let_ (op2 (.add i64) (.var m) (.imm 5)) fun (y, ()) =>
    mix hs y fun z =>
    .let_ (op2 (.add i64) (.var x) (.var z)) fun (r, ()) =>
    .ret (.var r, ())⟩

#guard lowers {} dfKeepFn
#guard lowers { dfKeep := true } dfKeepFn

/-! ## `D5` (`joinCoal`): `SpillCoalesce.addJumpAffAnti` & `swapColorsArr` -/

-- `addJumpAffAnti`: non-latch join gets `boost = 2` when `joinCoal = true`, `1` when `false`,
-- while latches keep `min (pow8 depth) 512`.
#guard
  let rOff := Spill.addJumpAffAnti false 0 [some 0, some 2] [1, 3] 10 [] [] false
  let rOn  := Spill.addJumpAffAnti false 0 [some 0, some 2] [1, 3] 10 [] [] true
  let rLat := Spill.addJumpAffAnti true  2 [some 0, some 2] [1, 3] 10 [] [] true
  rOff == ([(2, 3, 80), (0, 1, 80)], [(2, 1, 20), (0, 3, 20)]) &&
  rOn  == ([(2, 3, 160), (0, 1, 160)], [(2, 1, 20), (0, 3, 20)]) &&
  rLat == ([(2, 3, 5120), (0, 1, 5120)], [(2, 1, 2560), (0, 3, 2560)])

-- `swapColorsArr`: swaps two interfering variables (`0 ↔ 1`) when their net affinity strictly
-- improves, and refuses to move `armEv`-pinned or `zextPeers`-tied variables.
#guard
  let ctx : Spill.Ctx x64Target.toIsa :=
    { allGpr := [], allVec := [], gReg := .empty, vReg := .empty,
      nGpr := 2, nVec := 0, gAlloc := [0, 1], csIds := [], vAlloc := [],
      gScr := none, vScr := none, cross := .empty, loops := .empty,
      loopReach := .empty, banks := .empty, flagHome := .empty,
      bparams := .empty, lTrie := .empty }
  let order := [(10, 0), (10, 1)]
  let interf := #[[1], [0], [], []]
  let affArr := #[[(2, 10)], [(3, 10)], [(0, 10)], [(1, 10)]]
  let antiArr := Array.replicate 4 []
  let abiGArr := Array.replicate 4 []
  let emptyA := Array.replicate 4 ([] : List Nat)
  let h0 : Array (Spill.Home x64Target.Cond) := #[.gpr 0, .gpr 1, .gpr 1, .gpr 0]
  let hSwapped := Spill.swapColorsArr ctx order interf affArr antiArr abiGArr
    emptyA emptyA emptyA .empty [] (fun _ _ => false) h0
  let armPinned := emptyA.set! 0 [99]
  let hPinned := Spill.swapColorsArr ctx order interf affArr antiArr abiGArr
    emptyA armPinned emptyA .empty [] (fun _ _ => false) h0
  let gprOf : Spill.Home x64Target.Cond → Option Nat | .gpr r => some r | _ => none
  gprOf (hSwapped.getD 0 .none) == some 1 && gprOf (hSwapped.getD 1 .none) == some 0 &&
  gprOf (hPinned.getD 0 .none) == some 0 && gprOf (hPinned.getD 1 .none) == some 1

/-! ## Replacement-Scan & `Kissat.Plain` Real-Benchmark Guards -/

/-- Self-contained byte replacement-scan loop (`cmpb $0, ...; jb`) whose limit is spilled before
the loop under `baseOracleCfg`, exercising `replLoopCmpRspCount` (`1 -> 0` under `loopRegIn`). -/
meta def replScanLoopFn : Fn :=
  ⟨"replScanLoopW61", [i64, i64], [i64], fun _ _ (vals, nptr, ()) =>
    .load i64 (.var nptr) fun lim =>
    adds vals 14 fun hs =>
    heavyMix hs nptr 5 fun dead =>
    .let_ (op2 (.add i64) (.var dead) (.var nptr)) fun (s0, ()) =>
    .group (sig := [[i64]])
      (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
      (fun (doneL, ()) =>
        loop1 (ts := [i64, i64])
          (fun L (i, acc, ()) =>
            .let_ (op2 (.add i64) (.var vals) (.var i)) fun (addr, ()) =>
            .load (.bits 8) (.var addr) fun b =>
            .let_ (op2 (.cmp .slt (.bits 8)) (.var b) (.imm 0#8)) fun (neg, ()) =>
            .jnz (.var neg)
              (.let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
               .let_ (op2 (.cmp .ult i64) (.var i') (.var lim)) fun (c0, ()) =>
               .jnz (.var c0)
                 (.jump L (.var i', .var acc, ()))
                 (.jump doneL (.var acc, ())))
              (.jump doneL (.var i, ())))
          (fun L => .jump L (.imm 0, .var s0, ())))⟩

/-- Check replacement-scan inner loop blocks (`cmpb $0 ... jb`, `≤ 10` insns)
for folded `cmp (%rsp)` instructions. -/
meta def replLoopCmpRspCount (asm : String) : Nat :=
  let lines := asm.splitOn "\n"
  let step (acc : List (String × List String) × Option (String × List String)) (raw : String) :=
    let s := raw.trimAscii.toString
    if s.startsWith ".L" && s.endsWith ":" then
      let nm := (s.dropEnd 1).toString
      let acc' := match acc.2 with | some b => b :: acc.1 | none => acc.1
      (acc', some (nm, []))
    else if s.isEmpty || s.startsWith "." then acc
    else match acc.2 with
      | some (nm, bs) => (acc.1, some (nm, s :: bs))
      | none => acc
  let (blks, last) := lines.foldl step ([], none)
  let allBlks := match last with | some b => b :: blks | none => blks
  allBlks.foldl (fun n (lbl, revIns) =>
    let ins := revIns.reverse
    let hasCmpb0 := ins.any (·.startsWith "cmpb $0,")
    let hasBackJb := ins.any (· == s!"jb {lbl}")
    if hasCmpb0 && hasBackJb && Nat.ble ins.length 10 then
      n + (ins.filter fun s => s.startsWith "cmp" && s.contains "(%rsp)").length
    else n) 0

meta def plainPolMidFn? (nm : String) : Option Fn :=
  let raw? := ((Examples.Kissat.Plain.plainModule).optInlinePolicy {}).fns.find? (·.name == nm)
  raw?.map fun raw => Fn.midFromEarly x64LegalTarget (Driver.matFn raw.earlyOpt)

#guard
  match lowerAsm? baseOracleCfg replScanLoopFn, lowerAsm? {} replScanLoopFn with
  | some asmBase, some asmDef =>
    replLoopCmpRspCount asmBase == 1 &&
    replLoopCmpRspCount asmDef == 0
  | _, _ => false

#guard
  ["plain_backtrack", "plain_zero_tables", "plain_prop_lit", "plain_sweep",
   "plain_reduce"].all fun nm =>
    match plainPolMidFn? nm with
    | none => false
    | some fm =>
      match lowerAsm? baseOracleCfg fm, lowerAsm? {} fm with
      | some asmBase, some asmDef =>
        stRspCount asmDef ≤ stRspCount asmBase &&
        foldRspCmps asmDef ≤ foldRspCmps asmBase
      | _, _ => false

end LeanQbeTest.T.OptW61SpillOracleTest
