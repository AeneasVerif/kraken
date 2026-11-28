module

import LeanQbe.T.LeanLCNF.Lower1
import LeanQbe.T.LeanLCNF.Demo
import LeanQbe.T.FlatLemmas
import LeanQbe.T.PrintCpp
import LeanQbe.T.PrintQbe
meta import LeanQbe.T.LeanLCNF.Lower1
meta import LeanQbe.T.LeanLCNF.Demo
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe

/-!
# Tests for the impure `LCNF` → `LeanQbe.T` pipeline (`LeanQbe.T.LeanLCNF`)

* Structural `#guard`s on the spliced real impure LCNF (`Demo.demoMod`): FBIP `isShared`/`oset`
  reuse in `RBNode.ins`/`mapValues`, unboxed `sset`/`sproj` fields, 6-parameter `run`, closures.
* Lowering of every declaration plus `lcnf_apply_1..3`; `Func.checkTFlat` on every reified
  function, `loop1` self-tail loops, and the `Func.Wf` theorem `lcnf_demo_wf`.
* `main <dir>`: writes the PrintCpp translation unit `lcnf_gen.hpp`, the stage-by-stage traces
  (`<f>.mono`, `<f>.impure`, `<f>.T.ssa`) and `metrics.txt` for `test/lcnf/run.sh`.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.LeanLCNFTest

open LeanQbe.T hiding TFlatFn
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Frontend.C0 (TFlatFn)

/-! ## 1. The spliced impure LCNF -/

/-- Declaration of the demo module by (short) name. -/
def demoDecl? (short : String) : Option LcDecl :=
  Demo.demoMod.decls.find? (·.name == "LeanQbe.T.LeanLCNF.Demo." ++ short)

mutual
/-- Does `p` hold for some `let` value in `c`? -/
def anyVal (p : LcVal → Bool) : LcCode → Bool
  | .let_ _ _ v k => p v || anyVal p k
  | .jp _ _ b k => anyVal p b || anyVal p k
  | .cases _ alts => anyValAlts p alts
  | .oset _ _ _ k | .uset _ _ _ k | .sset _ _ _ _ _ k | .setTag _ _ k
  | .inc _ _ _ k | .dec _ _ _ k | .del _ k => anyVal p k
  | .jmp _ _ | .ret _ | .unreach => false

/-- `anyVal` over alternatives. -/
def anyValAlts (p : LcVal → Bool) : List (LcPat × LcCode) → Bool
  | [] => false
  | (_, b) :: rest => anyVal p b || anyValAlts p rest
end

mutual
/-- Does `c` contain a statement satisfying `p`? -/
def anyStmt (p : LcCode → Bool) : LcCode → Bool
  | c@(.let_ _ _ _ k) | c@(.oset _ _ _ k) | c@(.uset _ _ _ k) | c@(.sset _ _ _ _ _ k)
  | c@(.setTag _ _ k) | c@(.inc _ _ _ k) | c@(.dec _ _ _ k) | c@(.del _ k) => p c || anyStmt p k
  | c@(.jp _ _ b k) => p c || anyStmt p b || anyStmt p k
  | c@(.cases _ alts) => p c || anyStmtAlts p alts
  | c => p c

/-- `anyStmt` over alternatives. -/
def anyStmtAlts (p : LcCode → Bool) : List (LcPat × LcCode) → Bool
  | [] => false
  | (_, b) :: rest => anyStmt p b || anyStmtAlts p rest
end

def declHas (short : String) (p : LcCode → Bool) : Bool :=
  (demoDecl? short).any fun d => anyStmt p d.body

#guard Demo.demoMod.decls.length ≥ 80
#guard Demo.demoMod.externs.map (·.name) |>.all fun n =>
  n.startsWith "Nat." || n.startsWith "UInt64." || n.startsWith "USize."
-- `USize.add._boxed` is synthesized from the persisted signature and `dec`s its boxed arguments.
#guard (demoDecl? "usizeSum").isSome &&
  (Demo.demoMod.decls.find? (·.name == "USize.add._boxed")).any fun d =>
    anyStmt (fun | .dec .. => true | _ => false) d.body
-- FBIP: `ExpandResetReuse`'s `isShared` diamond with in-place `oset` in `ins` / `mapValues`.
#guard (demoDecl? "RBNode.ins").any fun d => anyVal (fun | .isShared _ => true | _ => false) d.body
#guard declHas "RBNode.mapValues" fun | .oset .. => true | _ => false
#guard declHas "RBNode.ins" fun | .sset .. => true | _ => false
-- Unboxed `UInt64` constructor fields and the 6-parameter tail-recursive VM loop.
#guard (demoDecl? "run").any fun d =>
  d.params.length == 6 && anyVal (fun | .sproj .. => true | _ => false) d.body
#guard declHas "run" fun | .sset _ _ _ _ .uint64 _ => true | _ => false
-- Join points and closures.
#guard declHas "RBNode.balance" fun | .jp .. => true | _ => false
#guard Demo.demoMod.papTargets.length ≥ 10
#guard Demo.demoMod.maxAp == 3
#guard Demo.demoMod.snaps.any fun s => s.name.endsWith "RBNode.ins" && !s.mono.isEmpty

/-! ## 2. Lowering, reification, `Func.Wf` -/

/-- The lowered demo program (empty on a lowering error, which the `#guard`s below reject). -/
def demoTfs : List TFlatFn := (lowerModule Demo.lcnfProgram).toOption.getD []

/-- The reified demo program. -/
def demoFns : List Fn := Frontend.C0.tflatFnsToFns demoTfs

/-- Every function of the lowered demo program is `Func.Wf`. -/
theorem lcnf_demo_wf : ∀ f ∈ demoFns, f.Wf := Frontend.C0.tflatFnsToFns_wf demoTfs

#guard (lowerModule Demo.lcnfProgram).isOk
#guard demoTfs.length == Demo.lcnfProgram.decls.length + 3
#guard demoFns.all fun f => Func.checkTFlat f.body
#guard (demoFns.map (·.name)).contains "lcnf_apply_3"

mutual
/-- `(ops, loads, stores, calls, jnz, groups)` of a `TFlat`. -/
def counts {rs : List Ty} : TFlat rs → Nat × Nat × Nat × Nat × Nat × Nat
  | .let_ _ k => let (a, b, c, d, e, f) := counts k; (a + 1, b, c, d, e, f)
  | .load _ _ k => let (a, b, c, d, e, f) := counts k; (a, b + 1, c, d, e, f)
  | .store _ _ k => let (a, b, c, d, e, f) := counts k; (a, b, c + 1, d, e, f)
  | .call _ _ _ k => let (a, b, c, d, e, f) := counts k; (a, b, c, d + 1, e, f)
  | .jnz _ t e =>
    let (a, b, c, d, x, f) := counts t
    let (a', b', c', d', x', f') := counts e
    (a + a', b + b', c + c', d + d', x + x' + 1, f + f')
  | .group bs k =>
    let (a, b, c, d, x, f) := countsB bs
    let (a', b', c', d', x', f') := counts k
    (a + a', b + b', c + c', d + d', x + x', f + f' + 1)
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => (0, 0, 0, 0, 0, 0)

/-- `counts` over blocks. -/
def countsB {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig →
    Nat × Nat × Nat × Nat × Nat × Nat
  | _, .nil => (0, 0, 0, 0, 0, 0)
  | _, .cons b bs =>
    let (a, b1, c, d, e, f) := counts b
    let (a', b', c', d', e', f') := countsB bs
    (a + a', b1 + b', c + c', d + d', e + e', f + f')
end

/-- One metrics line per lowered function. -/
def metricsLine (tf : TFlatFn) : String :=
  let (o, l, s, c, j, g) := counts tf.flat
  s!"{tf.name} params={tf.as.length} ops={o} loads={l} stores={s} calls={c} jnz={j} groups={g}"

/-! ## 3. Axioms -/

#print axioms lcnf_demo_wf

/-! ## 4. Artifact generator -/

/-- Representative declarations traced stage by stage. -/
def traced : List String :=
  ["RBNode.ins", "RBNode.mapValues", "mmerge", "dpll", "run", "sortBench._lam_5._boxed"]

/-- Write `lcnf_gen.hpp`, traces and metrics into `outDir`. -/
def generateArtifacts (outDir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll outDir
  let tfs ← IO.ofExcept (lowerModule Demo.lcnfProgram)
  let m := lcnfTModule tfs
  IO.FS.writeFile (outDir / "lcnf_gen.hpp") (← IO.ofExcept (PrintCpp.ppTModule m))
  IO.FS.writeFile (outDir / "metrics.txt") (String.intercalate "\n" (tfs.map metricsLine) ++ "\n")
  let tr := outDir / "trace"
  IO.FS.createDirAll tr
  for short in traced do
    let full := "LeanQbe.T.LeanLCNF.Demo." ++ short
    let file := short.replace "." "_"
    match Demo.demoMod.snaps.find? (·.name == full) with
    | some s =>
      IO.FS.writeFile (tr / s!"{file}.mono") (s.mono ++ "\n")
      IO.FS.writeFile (tr / s!"{file}.impure") (s.impure ++ "\n")
    | none => throw (IO.userError s!"no snapshot for {full}")
    match (Frontend.C0.tflatFnsToFns tfs).find? (·.name == mangleLc full) with
    | some f => IO.FS.writeFile (tr / s!"{file}.T.ssa") ((← IO.ofExcept (PrintQbe.fn f)) ++ "\n")
    | none => throw (IO.userError s!"no lowered function for {full}")

end LeanQbeTest.T.LeanLCNFTest

public def main (args : List String) : IO Unit :=
  LeanQbeTest.T.LeanLCNFTest.generateArtifacts (args.headD "lcnf-out")
