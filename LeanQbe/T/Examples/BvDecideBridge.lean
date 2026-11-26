module

public import Std.Tactic.BVDecide.Reflect
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Examples.LratBytesDimacsLemmas
public import LeanQbe.T.InterpKissat
public import LeanQbe.T.Examples.Kissat.PlainLemmas
import LeanQbe.T.Logic.MemLemmas
import Kraken.SeparationMem
import Kraken.Separation

/-!
# Zero-Axiom `Std.Tactic.BVDecide` <-> Verified Kissat Reflection Bridge (`M1a`)

Purely additive leaf bridge connecting `Std.Tactic.BVDecide` bitblasting (`BVLogicalExpr.bitblast`,
`AIG.toCNF`, `Entrypoint.relabelNat`) to verified DIMACS byte-level SAT solving
(`LeanQbe.T.Examples.LratBytes.parseDimacs` / `encodeDimacs` / `parseDimacs_encodeDimacs`) and the
verified Kissat `D-Plain` interpreter (`interpModule plainModule`).

All definitions and proofs use `0` custom axioms (`<= std3`), `0` `@[extern]`, `0`
`@[implemented_by]`, `0` `native_decide`, `0` `bv_decide`, and `0` `import all`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.BvDecideBridge

open Std Std.Sat Std.ExtHashMap
open Std.Tactic.BVDecide
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.Plain

/-! ## 1. Decidable `ValidDimacsCnf` and fast `ByteArray` DIMACS encoder -/

/-- Decidable Boolean checker for `ValidDimacsCnf`:
`cnfMaxVar cnf < dimacsBound`, `cnf.clauses.size < dimacsBound`, and every variable is `≥ 1`. -/
@[expose] def validDimacsB (cnf : CNF Nat) : Bool :=
  decide (cnfMaxVar cnf < dimacsBound) &&
  decide (cnf.clauses.size < dimacsBound) &&
  cnf.clauses.toList.all (fun cl => cl.literals.all (fun l => decide (1 ≤ l.1)))

theorem validDimacsB_iff (cnf : CNF Nat) :
    validDimacsB cnf = true ↔ ValidDimacsCnf cnf := by
  unfold validDimacsB ValidDimacsCnf
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc]

/-- Append a `List UInt8` onto a `ByteArray` via in-place `ByteArray.push`. -/
@[expose] def pushBytes (ba : ByteArray) (bs : List UInt8) : ByteArray :=
  bs.foldl ByteArray.push ba

/-- Append a single DIMACS literal (`"<v> "` or `"-<v> "`) onto a `ByteArray`. -/
@[expose] def pushDimacsLit (ba : ByteArray) (l : Literal Nat) : ByteArray :=
  let ba := if l.2 then ba else ba.push asciiMinus
  (pushBytes ba (natToBytes l.1)).push asciiSpace

/-- Append a `0\n`-terminated DIMACS clause onto a `ByteArray`. -/
@[expose] def pushDimacsClause (ba : ByteArray) (cl : CNF.Clause Nat) : ByteArray :=
  let ba := cl.literals.foldl pushDimacsLit ba
  (ba.push asciiZero).push asciiNewline

/-- Linear `ByteArray` ASCII DIMACS encoder matching `LratBytes.encodeDimacs` byte-for-byte. -/
@[expose] def encodeDimacsBA (cnf : CNF Nat) : ByteArray :=
  let ba := pushBytes ByteArray.empty dimacsHeaderPrefix
  let ba := pushBytes ba (natToBytes (cnfMaxVar cnf))
  let ba := ba.push asciiSpace
  let ba := pushBytes ba (natToBytes cnf.clauses.size)
  let ba := ba.push asciiNewline
  cnf.clauses.foldl pushDimacsClause ba

private theorem push_data_toList (ba : ByteArray) (b : UInt8) :
    (ba.push b).data.toList = ba.data.toList ++ [b] := by
  cases ba; exact Array.toList_push

private theorem pushBytes_data_toList (bs : List UInt8) (ba : ByteArray) :
    (pushBytes ba bs).data.toList = ba.data.toList ++ bs := by
  unfold pushBytes
  induction bs generalizing ba with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, ih, push_data_toList, List.append_assoc, List.singleton_append]

private theorem pushDimacsLit_data_toList (l : Literal Nat) (ba : ByteArray) :
    (pushDimacsLit ba l).data.toList = ba.data.toList ++ encodeDimacsLit l := by
  unfold pushDimacsLit encodeDimacsLit
  cases l.2 <;> simp [pushBytes_data_toList, List.append_assoc]

private theorem foldl_pushDimacsLit_data_toList (ls : List (Literal Nat)) (ba : ByteArray) :
    (ls.foldl pushDimacsLit ba).data.toList =
      ba.data.toList ++ ls.flatMap encodeDimacsLit := by
  induction ls generalizing ba with
  | nil => simp
  | cons l ls ih =>
    rw [List.foldl_cons, ih, pushDimacsLit_data_toList, List.flatMap_cons, List.append_assoc]

private theorem pushDimacsClause_data_toList (cl : CNF.Clause Nat) (ba : ByteArray) :
    (pushDimacsClause ba cl).data.toList = ba.data.toList ++ encodeDimacsClause cl := by
  unfold pushDimacsClause encodeDimacsClause
  rw [push_data_toList, push_data_toList, foldl_pushDimacsLit_data_toList]
  simp [List.append_assoc]

private theorem foldl_pushDimacsClause_data_toList
    (cls : List (CNF.Clause Nat)) (ba : ByteArray) :
    (cls.foldl pushDimacsClause ba).data.toList =
      ba.data.toList ++ cls.flatMap encodeDimacsClause := by
  induction cls generalizing ba with
  | nil => simp
  | cons cl cls ih =>
    rw [List.foldl_cons, ih, pushDimacsClause_data_toList, List.flatMap_cons, List.append_assoc]

theorem encodeDimacsBA_toList (cnf : CNF Nat) :
    (encodeDimacsBA cnf).data.toList = encodeDimacs cnf := by
  unfold encodeDimacsBA encodeDimacs
  rw [← Array.foldl_toList, foldl_pushDimacsClause_data_toList]
  rw [push_data_toList, pushBytes_data_toList, push_data_toList,
      pushBytes_data_toList, pushBytes_data_toList]
  have hempty : ByteArray.empty.data.toList = [] := rfl
  rw [hempty, List.nil_append]

/-! ## 2. Solver-parametric `BVLogicalExpr` reflection pipeline -/

/-- Bitblast `bv`, shift CNF variables to `1`-based DIMACS indices, validate bounds, and invoke
`solve` on the encoded DIMACS `ByteArray`, accepting only UNSAT status `20`. -/
@[expose] def verifyBVExprWith (solve : ByteArray → UInt64 → UInt64)
    (bv : BVLogicalExpr) (fuel : UInt64) : Bool :=
  let cnf := (AIG.toCNF bv.bitblast.relabelNat).relabel (· + 1)
  validDimacsB cnf && solve (encodeDimacsBA cnf) fuel == 20

/-- End-to-end soundness of `verifyBVExprWith` for any byte-level DIMACS UNSAT solver `solve`. -/
theorem unsat_of_verifyBVExprWith (solve : ByteArray → UInt64 → UInt64)
    (hsound : ∀ (ba : ByteArray) (fuel : UInt64),
      solve ba fuel = 20 → ∃ cnf, parseDimacs ba.data.toList = some cnf ∧ cnf.Unsat)
    (bv : BVLogicalExpr) (fuel : UInt64)
    (h : verifyBVExprWith solve bv fuel = true) :
    bv.Unsat := by
  unfold verifyBVExprWith at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hvalid, hsolve⟩ := h
  have hv : ValidDimacsCnf ((AIG.toCNF bv.bitblast.relabelNat).relabel (· + 1)) :=
    (validDimacsB_iff _).mp hvalid
  obtain ⟨cnf', hparse, hunsat⟩ := hsound _ fuel hsolve
  rw [encodeDimacsBA_toList, parseDimacs_encodeDimacs hv] at hparse
  cases hparse
  have hunsat0 : (AIG.toCNF bv.bitblast.relabelNat).Unsat :=
    (CNF.unsat_relabel_iff (fun _ _ heq => Nat.succ.inj heq)).mp hunsat
  apply BVLogicalExpr.unsat_of_bitblast
  rw [← AIG.Entrypoint.relabelNat_unsat_iff]
  rw [← AIG.toCNF_equisat]
  exact hunsat0

/-! ## 3. Zero-axiom `M1a` instantiation via `interpModule` on `plainModule` -/

/-- Scratch buffer length allocated for `kissat_solve_bytes` on a `cnfSize`-byte DIMACS input. -/
@[expose] def plainBridgeWorkLen (cnfSize : Nat) : Nat :=
  max 8192 (cnfSize * 20 + 4096)

/-- Run the verified 59-function Kissat `D-Plain` module (`plainModule`) inside the verified
first-order interpreter (`interpModule`), returning `20` on UNSAT, `10` on SAT, or `0` on
unknown / out-of-fuel / malformed input. -/
@[expose] def solvePlainInterp (cnf : ByteArray) (fuel : UInt64) : UInt64 :=
  let cnfBytes := cnf.data.toList
  let wlen := plainBridgeWorkLen cnfBytes.length
  let cnfPtr : BitVec 64 := 0x1000#64
  let workPtr : BitVec 64 := cnfPtr + BitVec.ofNat 64 cnfBytes.length
  if cnfPtr.toNat + cnfBytes.length + wlen < 2 ^ 64 then
    let m0 : Mem 64 := (cnfBytes ++ List.replicate wlen 0).At cnfPtr
    let args : Tup Val [i64, i64, i64, i64, i64] :=
      (cnfPtr, BitVec.ofNat 64 cnfBytes.length, workPtr, BitVec.ofNat 64 wlen, fuel, ())
    match interpModule plainModule fuel.toNat "kissat_solve_bytes"
        [i64, i64, i64, i64, i64] [i64] args m0 with
    | .ok (r, ()) _ => UInt64.ofBitVec r
    | _ => 0
  else
    0

private theorem plainBridge_mem_sep (cnfPtr : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hfit : cnfPtr.toNat + cnfBytes.length + wlen < 2 ^ 64) :
    (bytes cnfPtr cnfBytes ⋆ region (cnfPtr + BitVec.ofNat 64 cnfBytes.length) wlen ⋆ emp)
      ((cnfBytes ++ List.replicate wlen 0).At cnfPtr) := by
  have hwlen : (List.replicate wlen (0 : UInt8)).length = wlen := List.length_replicate
  have hle : cnfBytes.length + (List.replicate wlen (0 : UInt8)).length ≤ 2 ^ 64 := by
    rw [hwlen]; omega
  have h0 : Eq ((cnfBytes ++ List.replicate wlen 0).At cnfPtr)
      ((cnfBytes ++ List.replicate wlen 0).At cnfPtr) := rfl
  rw [Mem.At_append_sep cnfBytes (List.replicate wlen 0) cnfPtr hle] at h0
  have h1 : (bytes cnfPtr cnfBytes ⋆
      region (cnfPtr + BitVec.ofNat 64 cnfBytes.length) wlen)
      ((cnfBytes ++ List.replicate wlen 0).At cnfPtr) :=
    sep_mono_r (fun _ hf => ⟨List.replicate wlen 0, hwlen, hf.symm⟩) h0
  rwa [sep_emp]

/-- Zero-axiom soundness of `solvePlainInterp`: combines `plainEnv_moduleOk`,
`ModuleOk.env_sound`, and `interpModule_ok_witness` (`<= std3`). -/
theorem solvePlainInterp_sound (ba : ByteArray) (fuel : UInt64)
    (h : solvePlainInterp ba fuel = 20) :
    ∃ cnf, parseDimacs ba.data.toList = some cnf ∧ cnf.Unsat := by
  unfold solvePlainInterp at h
  dsimp only at h
  split at h
  · rename_i hfit
    let cnfBytes := ba.data.toList
    let wlen := plainBridgeWorkLen cnfBytes.length
    let cnfPtr : BitVec 64 := 0x1000#64
    let workPtr : BitVec 64 := cnfPtr + BitVec.ofNat 64 cnfBytes.length
    let m0 : Mem 64 := (cnfBytes ++ List.replicate wlen 0).At cnfPtr
    let args : Tup Val [i64, i64, i64, i64, i64] :=
      (cnfPtr, BitVec.ofNat 64 cnfBytes.length, workPtr, BitVec.ofNat 64 wlen, fuel, ())
    cases hrun : interpModule plainModule fuel.toNat "kissat_solve_bytes"
        [i64, i64, i64, i64, i64] [i64] args m0 with
    | outOfFuel => rw [hrun] at h; simp at h
    | ub => rw [hrun] at h; simp at h
    | exit _ _ _ => rw [hrun] at h; simp at h
    | ok res m' =>
      rcases res with ⟨r, ⟨⟩⟩
      rw [hrun] at h
      dsimp only at h
      have hr20 : r = 20#64 := by
        have hbv := congrArg UInt64.toBitVec h
        simpa using hbv
      have h4096 : (0x1000#64 : BitVec 64).toNat = 4096 := rfl
      have hcfit : cnfPtr.toNat + cnfBytes.length < 2 ^ 64 := by
        dsimp only [cnfPtr, cnfBytes, wlen] at hfit ⊢; rw [h4096] at hfit ⊢; omega
      have hwp_work : workPtr.toNat = cnfPtr.toNat + cnfBytes.length := by
        dsimp only [workPtr, cnfPtr, cnfBytes] at hcfit ⊢
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)]
      have hwfit : workPtr.toNat + wlen < 2 ^ 64 := by
        dsimp only [cnfPtr, cnfBytes, wlen] at hfit hwp_work ⊢; rw [h4096] at hfit; omega
      have hm0 : (bytes cnfPtr cnfBytes ⋆ region workPtr wlen ⋆ emp) m0 :=
        plainBridge_mem_sep cnfPtr cnfBytes wlen hfit
      let Q : Post [i64] := fun (r', ()) m'' =>
        (r' = 0#64 ∨ r' = 10#64 ∨ r' = 20#64) ∧
        (r' = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (r' = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (bytes cnfPtr cnfBytes ⋆ region workPtr wlen ⋆ emp) m''
      let X : XPost := fun _ _ _ _ => False
      have hEnv : ModuleEnvSound (Env.ofModule plainModule plainEnv) plainModule :=
        ModuleOk.env_sound plainEnv_moduleOk rfl
      have hmem : kissat_solve_bytes ∈ plainModule.fns := by
        simp [plainModule, plainFns, plain2_fns]
      have hlook : lookupFn plainModule "kissat_solve_bytes"
          [i64, i64, i64, i64, i64] [i64] = some kissat_solve_bytes_body :=
        lookupFn_of_mem plainEnv_moduleOk.nodup hmem
      have hplain : plainEnv "kissat_solve_bytes"
          [i64, i64, i64, i64, i64] [i64] args m0 Q X :=
        mkPlainEnv_solve_bytes plainSolveBytesSpec (fun _ _ _ _ hs => hs) args m0 Q X
          ⟨cnfBytes, wlen, emp, rfl, rfl, hcfit, hwfit, hm0,
            fun r' m'' hdom hu hs hm'' => ⟨hdom, hu, hs, hm''⟩⟩
      have hsig : ("kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64]) ∈
          plainModule.sigs :=
        List.mem_append_left _ (List.mem_map.mpr ⟨kissat_solve_bytes, hmem, rfl⟩)
      have hrestr : (Env.ofModule plainModule plainEnv) "kissat_solve_bytes"
          [i64, i64, i64, i64, i64] [i64] args m0 Q X :=
        ⟨hsig, hplain⟩
      rcases List.mem_iff_append.mp hmem with ⟨pre, post, hsplit⟩
      have ⟨_, _, hwp_fn⟩ := plainEnv_moduleOk.ofModule.fnsOk pre kissat_solve_bytes post hsplit
      have hwp := hwp_fn args m0 Q X hrestr
      have hpost := interpModule_ok_witness plainModule (Env.ofModule plainModule plainEnv)
        hEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] args m0 Q X
        kissat_solve_bytes_body hlook kissat_solve_bytes_wf hwp fuel.toNat (r, ()) m' hrun
      exact hpost.2.1 hr20
  · simp at h

/-- End-to-end zero-axiom `BVLogicalExpr` reflection theorem backed by `interpModule` running
the verified 59-function `Kissat.Plain` C0 SAT solver (`<= std3`). -/
theorem unsat_of_verifyBVExprPlainInterp (bv : BVLogicalExpr) (fuel : UInt64)
    (h : verifyBVExprWith solvePlainInterp bv fuel = true) :
    bv.Unsat :=
  unsat_of_verifyBVExprWith solvePlainInterp solvePlainInterp_sound bv fuel h

end LeanQbe.T.Examples.BvDecideBridge
