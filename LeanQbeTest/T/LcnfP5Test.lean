module

import LeanQbe.T.LeanLCNF.Lower1
import LeanQbe.T.LeanLCNF.Coverage
import LeanQbe.T.FlatLemmas
import LeanQbe.T.PrintCpp
import LeanQbe.T.PrintQbe
meta import LeanQbe.T.LeanLCNF.Lower1
meta import LeanQbe.T.LeanLCNF.Coverage
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe

/-!
# Extended Coverage Tests (`LeanQbe.T.LeanLCNF.Coverage`)

* Structural `#guard`s verifying extracted string literals, big `Nat` literals (`≥ 2^63`),
  `Array`/`String`/`ByteArray` externs, `Float` (`bits 64`), `lowerModule` success,
  `Func.checkTFlat`, `PrintCpp`, and `PrintQbe`.
* Kernel-checked `Func.Wf` theorem `lcnf_cov_wf`.
* `main <dir>`: writes `lcnf_p5_gen.hpp` for the `PrintCpp` differential runner.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.LcnfP5Test

open LeanQbe.T hiding TFlatFn
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Frontend.C0 (TFlatFn)

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

def covTfs : List TFlatFn := (lowerModule Coverage.covProgram).toOption.getD []
def covFns : List Fn := Frontend.C0.tflatFnsToFns covTfs

theorem lcnf_cov_wf : ∀ f ∈ covFns, f.Wf := Frontend.C0.tflatFnsToFns_wf covTfs

#guard Coverage.covMod.decls.any fun d =>
  anyVal (fun | .lit (.str _) => true | _ => false) d.body
#guard Coverage.covMod.decls.any fun d =>
  anyVal (fun | .lit (.nat n) => n ≥ 2 ^ 63 | _ => false) d.body
#guard Coverage.covMod.decls.any fun d =>
  d.params.any (fun p => p.ty == .float) || d.retTy == .float ||
    anyVal (fun | .fap "Float.sqrt" _ => true | _ => false) d.body
#guard (lowerModule Coverage.covProgram).isOk
#guard !covFns.isEmpty
#guard covFns.all fun f => Func.checkTFlat f.body
#guard (PrintCpp.ppTModule (lcnfTModule covTfs)).isOk
#guard (PrintQbe.module (lcnfTModule covTfs)).isOk

/-! Bootstrap prims: all 23 externs the full `leanqbe` closure needs (+ `Int.tdiv`/`tmod`) are
reached from `covMod` and lowered; non-ASCII names mangle injectively. -/
def bootExterns : List String :=
  [ "getObjTagNat", "UInt64.ofBitVec", "UInt32.ofBitVec", "UInt64.toBitVec", "USize.ofNatLT"
  , "USize.repr", "Int64.ofNat", "Int64.decEq", "Int64.toInt", "System.Platform.getNumBits"
  , "Int.ofNat", "Int.negSucc", "Int.neg", "Int.add", "Int.sub", "Int.mul", "Int.ediv"
  , "Int.emod", "Int.natAbs", "Int.decEq", "Int.decLt", "Int.decLe", "Int.tdiv", "Int.tmod" ]
#guard bootExterns.all fun n => Coverage.covMod.externs.any (·.name == n)
#guard mangleLc "Sha256.σ₀" == "l_Sha256_u3c3_u2080_"
#guard [mangleLc "Sha256.σ₀", mangleLc "Sha256.σ₁", mangleLc "Sha256.«Σ₀»",
  mangleLc "Sha256.«Σ₁»"].eraseDups.length == 4
#guard covTfs.any (·.name == mangleLc "LeanQbe.T.LeanLCNF.Coverage.Sha.«Σ₁»")
#guard rtGlobalSlots == 4096

#print axioms lcnf_cov_wf

def generateArtifacts (outDir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll outDir
  let tfs ← IO.ofExcept (lowerModule Coverage.covProgram)
  let m := lcnfTModule tfs
  IO.FS.writeFile (outDir / "lcnf_p5_gen.hpp") (← IO.ofExcept (PrintCpp.ppTModule m))

end LeanQbeTest.T.LcnfP5Test

public def main (args : List String) : IO Unit :=
  LeanQbeTest.T.LcnfP5Test.generateArtifacts (args.headD "lcnf-out")
