module

public import Std.Tactic.BVDecide.Reflect
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Examples.LratBytesDimacsLemmas
public import LeanQbe.T.InterpKissat
public import LeanQbe.T.Examples.Kissat.Proof.Full
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Solver
import LeanQbe.T.Logic.MemLemmas
import Kraken.SeparationMem
import Kraken.Separation

/-!
# Zero-Axiom `Std.Tactic.BVDecide` <-> Verified Kissat Reflection Bridge (`M1a`)

Purely additive leaf bridge connecting `Std.Tactic.BVDecide` bitblasting (`BVLogicalExpr.bitblast`,
`AIG.toCNF`, `Entrypoint.relabelNat`) to verified DIMACS byte-level SAT solving
(`LeanQbe.T.Examples.LratBytes.parseDimacs` / `encodeDimacs` / `parseDimacs_encodeDimacs`) and the
verified full Kissat interpreter (`interpModule Src.Full.kissatModule`).

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
open LeanQbe.T.Examples.Kissat.Src.Full
open LeanQbe.T.Examples.Kissat.Proof
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Full

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

/-! ## 3. `Kissat.Ref.parseDimacs` vs `LratBytes.parseDimacs` Equivalence -/

private theorem ref_skipWsCommentsAux_eq (inComment : Bool) (bs : List UInt8) :
    Kissat.Ref.skipWsCommentsAux inComment bs =
      LratBytes.skipWsCommentsAux inComment bs := by
  induction bs generalizing inComment with
  | nil => cases inComment <;> rfl
  | cons b bs ih =>
    cases inComment with
    | true =>
      by_cases hb : b = 10
      · subst hb; exact ih false
      · simp [Kissat.Ref.skipWsCommentsAux, LratBytes.skipWsCommentsAux, ih true]
    | false =>
      simp only [Kissat.Ref.skipWsCommentsAux, LratBytes.skipWsCommentsAux]
      have hws : Kissat.Ref.isDimacsWs b = LratBytes.isDimacsWs b := rfl
      rw [hws]
      cases LratBytes.isDimacsWs b
      · cases b == 99 <;> simp [ih]
      · simp [ih]

private theorem ref_skipWsComments_eq (bs : List UInt8) :
    Kissat.Ref.skipWsComments bs = LratBytes.skipWsComments bs :=
  ref_skipWsCommentsAux_eq false bs

private theorem ref_skipWs_eq (bs : List UInt8) :
    Kissat.Ref.skipWs bs = LratBytes.skipWs bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [Kissat.Ref.skipWs, LratBytes.skipWs]
    have hws : Kissat.Ref.isDimacsWs b = LratBytes.isDimacsWs b := rfl
    rw [hws]
    cases LratBytes.isDimacsWs b <;> simp [ih]

private theorem ref_skipWs1_eq (bs : List UInt8) :
    Kissat.Ref.skipWs1 bs = LratBytes.skipWs1 bs := by
  cases bs with
  | nil => rfl
  | cons b bs =>
    simp only [Kissat.Ref.skipWs1, LratBytes.skipWs1, ref_skipWs_eq]
    rfl

private theorem ref_parseDigitsAux_eq (acc : Nat) (bs : List UInt8) :
    Kissat.Ref.parseDigitsAux acc bs = LratBytes.parseDigitsAux acc bs := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    simp only [Kissat.Ref.parseDigitsAux, LratBytes.parseDigitsAux]
    have hd : Kissat.Ref.isDimacsDigit b = LratBytes.isDimacsDigit b := rfl
    have hws : Kissat.Ref.isDimacsWs b = LratBytes.isDimacsWs b := rfl
    have hbd : Kissat.Ref.dimacsBound = LratBytes.dimacsBound := rfl
    rw [hd, hws, hbd]
    cases LratBytes.isDimacsDigit b
    · rfl
    · simp only [↓reduceIte]
      split <;> simp [ih]

private theorem ref_parseNat_eq (bs : List UInt8) :
    Kissat.Ref.parseNat bs = LratBytes.parseNat bs := by
  cases bs with
  | nil => rfl
  | cons b bs =>
    simp only [Kissat.Ref.parseNat, LratBytes.parseNat, ref_parseDigitsAux_eq]
    rfl

private theorem ref_parseHeader_eq (bs : List UInt8) :
    Kissat.Ref.parseHeader bs = LratBytes.parseHeader bs := by
  simp only [Kissat.Ref.parseHeader, LratBytes.parseHeader, ref_skipWsComments_eq,
    ref_skipWs1_eq, ref_parseNat_eq]
  split
  · rename_i bs1 heq
    split
    · rename_i bs1' heq'
      rw [heq] at heq'
      injection heq' with _ htl
      subst htl
      cases LratBytes.skipWs1 bs1 with
      | none => rfl
      | some bs2 =>
        dsimp only [bind, Option.bind]
        split <;> split <;> simp_all
    · rename_i hnot
      exact absurd heq (hnot _)
  · split <;> simp_all

private theorem ref_parseClauseAux_eq (fuel mv : Nat) (acc : List (Literal Nat))
    (bs : List UInt8) :
    Kissat.Ref.parseClauseAux fuel mv acc bs = LratBytes.parseClauseAux fuel mv acc bs := by
  induction fuel generalizing acc bs with
  | zero => rfl
  | succ fuel ih =>
    simp only [Kissat.Ref.parseClauseAux, LratBytes.parseClauseAux, ref_skipWsComments_eq]
    cases LratBytes.skipWsComments bs with
    | nil => rfl
    | cons b rest =>
      by_cases hb : b = 45
      · subst hb
        simp only [ref_parseNat_eq]
        cases LratBytes.parseNat rest with
        | none => rfl
        | some vr => dsimp only; split <;> simp [ih]
      · simp only [ref_parseNat_eq]
        cases hpn : LratBytes.parseNat (b :: rest) with
        | none => split <;> simp_all
        | some vr =>
          rcases vr with ⟨v, r'⟩
          cases v with
          | zero => split <;> simp_all
          | succ v => split <;> simp_all

private theorem ref_parseClause_eq (mv : Nat) (bs : List UInt8) :
    Kissat.Ref.parseClause mv bs = LratBytes.parseClause mv bs :=
  ref_parseClauseAux_eq (bs.length + 1) mv [] bs

private theorem ref_parseClauses_eq (mv k : Nat) (cnf : CNF Nat) (bs : List UInt8) :
    Kissat.Ref.parseClauses mv k cnf bs = LratBytes.parseClauses mv k cnf bs := by
  induction k generalizing cnf bs with
  | zero =>
    simp only [Kissat.Ref.parseClauses, LratBytes.parseClauses, ref_skipWsComments_eq]
  | succ k ih =>
    simp only [Kissat.Ref.parseClauses, LratBytes.parseClauses, ref_parseClause_eq]
    cases LratBytes.parseClause mv bs with
    | none => rfl
    | some cr => simp [ih]

private theorem ref_parseDimacs_eq_lratBytes (bs : List UInt8) :
    Kissat.Ref.parseDimacs bs = LratBytes.parseDimacs bs := by
  simp only [Kissat.Ref.parseDimacs, LratBytes.parseDimacs, ref_parseHeader_eq]
  cases LratBytes.parseHeader bs with
  | none => rfl
  | some hdr => exact ref_parseClauses_eq hdr.1 hdr.2.1 CNF.empty hdr.2.2

/-! ## 4. Zero-axiom `M1a` instantiation via `interpModule` on `Src.Full.kissatModule` -/

/-- Scratch buffer length allocated for full `kissat_solve_bytes` (`M6Hdr` + variable arrays)
on a `cnfSize`-byte DIMACS input. -/
@[expose] def fullBridgeWorkLen (cnfSize : Nat) : Nat :=
  max 16384 (cnfSize * 24 + 8192)

/-- Run the verified `418`-function full Kissat module (`Src.Full.kissatModule`) inside the
verified first-order interpreter (`interpModule`), returning `20` on UNSAT, `10` on SAT, or `0`
on unknown / out-of-fuel / malformed input. -/
@[expose] def solveFullInterp (cnf : ByteArray) (fuel : UInt64) : UInt64 :=
  let cnfBytes := cnf.data.toList
  let wlen := fullBridgeWorkLen cnfBytes.length
  let cnfPtr : BitVec 64 := 0x1000#64
  let workPtr : BitVec 64 := cnfPtr + BitVec.ofNat 64 cnfBytes.length
  if cnfPtr.toNat + cnfBytes.length + wlen < 2 ^ 64 then
    let m0 : Mem 64 := (cnfBytes ++ List.replicate wlen 0).At cnfPtr
    let args : Tup Val [i64, i64, i64, i64, i64] :=
      (cnfPtr, BitVec.ofNat 64 cnfBytes.length, workPtr, BitVec.ofNat 64 wlen, fuel, ())
    match interpModule kissatModule fuel.toNat "kissat_solve_bytes"
        [i64, i64, i64, i64, i64] [i64] args m0 with
    | .ok (r, ()) _ => UInt64.ofBitVec r
    | _ => 0
  else
    0

private theorem fullBridge_mem_sep (cnfPtr : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
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

/-- Zero-axiom UNSAT soundness of `solveFullInterp`: combines `Proof.Full.full_moduleOk`,
`Proof.Spec.Solver.solveBytesSpec`, `ModuleOk.env_sound`, and `interpModule_ok_witness`
(`<= std3`). -/
theorem solveFullInterp_sound (ba : ByteArray) (fuel : UInt64)
    (h : solveFullInterp ba fuel = 20) :
    ∃ cnf, parseDimacs ba.data.toList = some cnf ∧ cnf.Unsat := by
  unfold solveFullInterp at h
  dsimp only at h
  split at h
  · rename_i hfit
    let cnfBytes := ba.data.toList
    let wlen := fullBridgeWorkLen cnfBytes.length
    let cnfPtr : BitVec 64 := 0x1000#64
    let workPtr : BitVec 64 := cnfPtr + BitVec.ofNat 64 cnfBytes.length
    let m0 : Mem 64 := (cnfBytes ++ List.replicate wlen 0).At cnfPtr
    let args : Tup Val [i64, i64, i64, i64, i64] :=
      (cnfPtr, BitVec.ofNat 64 cnfBytes.length, workPtr, BitVec.ofNat 64 wlen, fuel, ())
    cases hrun : interpModule kissatModule fuel.toNat "kissat_solve_bytes"
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
        fullBridge_mem_sep cnfPtr cnfBytes wlen hfit
      let Q : Post [i64] := fun (r', ()) m'' =>
        (r' = 0#64 ∨ r' = 10#64 ∨ r' = 20#64) ∧
        (r' = 20#64 → ∃ cnf, Kissat.Ref.parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnfPtr cnfBytes ⋆ region workPtr wlen ⋆ emp) m''
      let X : XPost := fun _ _ _ _ => False
      have hEnv : ModuleEnvSound (Env.ofModule kissatModule fullEnv) kissatModule :=
        ModuleOk.env_sound full_moduleOk rfl
      have hmem : fullSolveBytesFn ∈ kissatModule.fns := fullSolveBytesFn_mem
      have hlook : lookupFn kissatModule "kissat_solve_bytes"
          [i64, i64, i64, i64, i64] [i64] = some Kissat.Src.Search.kissat_solve_bytes_body :=
        lookupFn_of_mem full_moduleOk.nodup hmem
      have hfull : fullEnv "kissat_solve_bytes"
          [i64, i64, i64, i64, i64] [i64] args m0 Q X := by
        refine fullEnv_solve_bytes_of ?_
        unfold Solver.solveBytesSpec
        refine FnContract.intro (cnfBytes, wlen) emp ⟨rfl, rfl, hcfit, hwfit⟩ hm0 ?_
        rintro ⟨r', ⟨⟩⟩ ⟨⟩ m'' ⟨hdom, h20, _⟩ hm''
        exact ⟨hdom, h20, hm''⟩
      have hsig : ("kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64]) ∈
          kissatModule.sigs :=
        List.mem_append_left _ (List.mem_map.mpr ⟨fullSolveBytesFn, hmem, rfl⟩)
      have hrestr : (Env.ofModule kissatModule fullEnv) "kissat_solve_bytes"
          [i64, i64, i64, i64, i64] [i64] args m0 Q X :=
        ⟨hsig, hfull⟩
      rcases List.mem_iff_append.mp hmem with ⟨pre, post, hsplit⟩
      have ⟨hwf, _, hwp_fn⟩ := full_moduleOk.ofModule.fnsOk pre fullSolveBytesFn post hsplit
      have hwp := hwp_fn args m0 Q X hrestr
      have hpost := interpModule_ok_witness kissatModule (Env.ofModule kissatModule fullEnv)
        hEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] args m0 Q X
        Kissat.Src.Search.kissat_solve_bytes_body hlook hwf hwp fuel.toNat (r, ()) m' hrun
      obtain ⟨cnf, hparse, hunsat⟩ := hpost.2.1 hr20
      exact ⟨cnf, by rwa [← ref_parseDimacs_eq_lratBytes], hunsat⟩
  · simp at h

/-- End-to-end zero-axiom `BVLogicalExpr` reflection theorem backed by `interpModule` running
the verified `418`-function `Kissat.Src.Full` C0 SAT solver (`<= std3`). -/
theorem unsat_of_verifyBVExprFullInterp (bv : BVLogicalExpr) (fuel : UInt64)
    (h : verifyBVExprWith solveFullInterp bv fuel = true) :
    bv.Unsat :=
  unsat_of_verifyBVExprWith solveFullInterp solveFullInterp_sound bv fuel h

/-- Compatibility alias forwarding `plainBridgeWorkLen` to `fullBridgeWorkLen`. -/
abbrev plainBridgeWorkLen : Nat → Nat := fullBridgeWorkLen

/-- Compatibility alias forwarding `solvePlainInterp` to `solveFullInterp` (`Proof.Full`). -/
abbrev solvePlainInterp : ByteArray → UInt64 → UInt64 := solveFullInterp

/-- Compatibility alias forwarding `solvePlainInterp_sound` to `solveFullInterp_sound`. -/
theorem solvePlainInterp_sound (ba : ByteArray) (fuel : UInt64)
    (h : solvePlainInterp ba fuel = 20) :
    ∃ cnf, parseDimacs ba.data.toList = some cnf ∧ cnf.Unsat :=
  solveFullInterp_sound ba fuel h

/-- Compatibility alias forwarding `unsat_of_verifyBVExprPlainInterp` to
`unsat_of_verifyBVExprFullInterp`. -/
theorem unsat_of_verifyBVExprPlainInterp (bv : BVLogicalExpr) (fuel : UInt64)
    (h : verifyBVExprWith solvePlainInterp bv fuel = true) :
    bv.Unsat :=
  unsat_of_verifyBVExprFullInterp bv fuel h

end LeanQbe.T.Examples.BvDecideBridge
