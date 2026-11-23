module

public import LeanQbe.T.Examples.Kissat.PlainLemmas
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullBridgeLemmas1
public import LeanQbe.T.Examples.Kissat.FullBridgeLemmas2
public import LeanQbe.T.Examples.Kissat.FullBridgeLemmas3
public import LeanQbe.T.Examples.Kissat.FullBridgeLemmas4
public import LeanQbe.T.Examples.Kissat.FullBridgeLemmas5
public import LeanQbe.T.Examples.Kissat.FullBridgeLemmas6
public import LeanQbe.T.Examples.Kissat.FullBridgeLemmas7
public import LeanQbe.T.Examples.Kissat.FullBridgeLemmas8a
public import LeanQbe.T.Examples.Kissat.FullBridgeLemmas8b
public import LeanQbe.T.Examples.Kissat.FullBridgeLemmas9
public import LeanQbe.T.Examples.Kissat.FullProof1
public import LeanQbe.T.Examples.Kissat.FullProof
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
public import LeanQbe.T.Examples.Kissat.FullDeduce1UipLemmas
public import LeanQbe.T.Examples.Kissat.FullDeduce1UipNv
public import LeanQbe.T.Examples.Kissat.FullVivifyLemmas
public import LeanQbe.T.Examples.Kissat.FullTransLemmas
public import LeanQbe.T.Examples.Kissat.FullProbeTransLemmas
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas
public import LeanQbe.T.Examples.Kissat.FullFastCoreLemmas
public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas
public import LeanQbe.T.Examples.Kissat.FullKittenLemmas
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas
public import LeanQbe.T.Examples.Kissat.FullFastProof
public import LeanQbe.T.Examples.Kissat.FullM3Proof
public import LeanQbe.T.Examples.Kissat.FullM4Proof
meta import LeanQbe.T.Examples.Kissat.PlainLemmas
meta import LeanQbe.T.Examples.Kissat.FullSpec
meta import LeanQbe.T.Examples.Kissat.FullBridgeLemmas7
meta import LeanQbe.T.Examples.Kissat.FullBridgeLemmas8a
meta import LeanQbe.T.Examples.Kissat.FullBridgeLemmas8b
meta import LeanQbe.T.Examples.Kissat.FullBridgeLemmas9
meta import LeanQbe.T.Examples.Kissat.FullDeduce1UipLemmas
meta import LeanQbe.T.Examples.Kissat.FullProof
meta import LeanQbe.T.Examples.Kissat.FullFast
meta import LeanQbe.T.Examples.Kissat.FullM3
meta import LeanQbe.T.Examples.Kissat.FullM4
import all Std.Sat.CNF.Basic
import all Std.Sat.CNF.Sat

/-!
# Kissat audit, part 1: the trusted specification boundary (architecture-independent)

This file is meant to be read by a human auditor. It restates, with every type written out in
full (no wrapper `abbrev`s introduced here), the shared trusted specification (`parseDimacs`,
`CNF.Unsat`, `CNF.Sat`) and source-level contracts for earlier Kissat builds:
* Retired solvers whose native machine-code audits live under `LeanQbeLegacyTest/`: `D-Plain`
  (`plainModule`, `59` functions, SAT+UNSAT), `D-Full` (`fullModule`, `166` functions,
  UNSAT-only), `D-Full M2 Fast` (`fastModule`, `196` functions, UNSAT-only), `D-Full M3`
  (`m3Module`, `204` functions, UNSAT-only), `D-Full M4` (`m4Module`, `231` functions, UNSAT-only
  here; SAT+UNSAT in `KissatSatSoundTest.lean` and `KissatM4LegacyAudit*.lean`), and the
  superseded partial `FullFastSched` (`schedModule`, `173` functions, `16/173` rows proved).
* The active native-certified solver `D-Full M5` (`270` functions, SAT+UNSAT) is audited in
  `KissatAuditX64.lean`, `KissatAuditArm64.lean`, `KissatM5Audit*.lean`,
  `KissatM5SoundAudit*.lean`, and `KissatSatSoundTest.lean`.

It imports neither `Kraken.X64` nor `Kraken.AArch64`.

## What must be trusted

1. `Std.Sat.CNF.Unsat` and `Std.Sat.CNF.Sat` from the Lean standard library: a CNF is
   unsatisfiable iff every assignment `a : Nat → Bool` evaluates it to `false`, and satisfied by
   `a` iff `a` evaluates it to `true` (Section 1 below restates both definitions by `Iff.rfl`).
2. `LeanQbe.T.Examples.LratBytes.parseDimacs : List UInt8 → Option (CNF Nat)`, the total, pure
   specification of ASCII DIMACS (header `p cnf <vars> <clauses>`, `0`-terminated clauses,
   `c` comments, whitespace, and nothing but whitespace/comments after the last clause). A
   solver answer is only ever about `cnf` with `parseDimacs cnfBytes = some cnf`; malformed
   input can only produce the answer `0` (unknown). Section 2 checks the parser on concrete
   inputs.
3. The Lean kernel and the standard axioms `propext`, `Classical.choice`, `Quot.sound`
   (Section 14).
4. For the machine-code theorems only: the Kraken x86-64 / AArch64 instruction semantics and the
   assembler/linker that turn the emitted directives into an executable.

Everything else (the C0 solver sources, the `LeanQbe.T` compiler, and all `Func.wp` proofs) is
checked by the kernel and need not be trusted.
-/

set_option autoImplicit false

public section

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat

/-! ## 1. The meaning of `Unsat` and `Sat` (definitional restatements) -/

/-- A CNF is unsatisfiable iff *every* Boolean assignment of its variables falsifies it. -/
theorem audit_unsat_def (cnf : CNF Nat) : cnf.Unsat ↔ ∀ a : Nat → Bool, cnf.eval a = false :=
  Iff.rfl

/-- `cnf.Sat a` iff the assignment `a` satisfies every clause of `cnf`. -/
theorem audit_sat_def (cnf : CNF Nat) (a : Nat → Bool) : cnf.Sat a ↔ cnf.eval a = true :=
  Iff.rfl

/-- `Unsat` and `Sat` are mutually exclusive, so the answers `10` and `20` can never both be
justified for the same input. -/
theorem audit_unsat_not_sat (cnf : CNF Nat) (a : Nat → Bool) (h : cnf.Unsat) : ¬ cnf.Sat a := by
  intro hs
  have h1 : cnf.eval a = false := h a
  have h2 : cnf.eval a = true := hs
  rw [h1] at h2
  exact Bool.false_ne_true h2

/-! ## 2. Executable checks of the DIMACS specification `parseDimacs` -/

/-- Clause lists as plain `(variable, polarity)` literal lists, for readable `#guard`s. -/
def auditLits (bs : List UInt8) : Option (List (List (Nat × Bool))) :=
  (parseDimacs bs).map fun cnf => cnf.clauses.toList.map (·.literals)

-- UNSAT example: `x1 ∧ ¬x1`.
#guard auditLits "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList == some [[(1, true)], [(1, false)]]
-- SAT example: `x1`.
#guard auditLits "p cnf 1 1\n1 0\n".toUTF8.toList == some [[(1, true)]]
-- Comments and extra whitespace are accepted.
#guard auditLits "c hi\np cnf 2 1\n 1  -2 0\n".toUTF8.toList == some [[(1, true), (2, false)]]
-- Malformed inputs are rejected (the solvers then may only answer `0`).
#guard (parseDimacs "".toUTF8.toList).isNone
#guard (parseDimacs "hello\n".toUTF8.toList).isNone
#guard (parseDimacs "p cnf 1 2\n1 0\n".toUTF8.toList).isNone
#guard (parseDimacs "p cnf 1 1\n2 0\n".toUTF8.toList).isNone
#guard (parseDimacs "p cnf 1 1\n1 0\n1 0\n".toUTF8.toList).isNone

-- The concrete byte vectors used by the non-vacuity theorems are exactly these two inputs.
#guard Plain.plainNvUnsatBytes == "p cnf 1 2\n1 0\n-1 0\n".toUTF8.toList
#guard Plain.plainNvSatBytes == "p cnf 1 1\n1 0\n".toUTF8.toList

/-- The UNSAT example parses to `x1 ∧ ¬x1`, which is unsatisfiable. -/
theorem audit_unsat_example :
    ∃ cnf, parseDimacs Plain.plainNvUnsatBytes = some cnf ∧ cnf.Unsat := by
  refine ⟨_, Plain.parseDimacs_plainUnsat, fun a => ?_⟩
  cases h : a 1 <;>
    simp [Plain.plainNvUnsatCnf, CNF.eval_add, CNF.Clause.eval, CNF.Clause.literals_ofLiterals, h]

/-- The SAT example parses to `x1`, which is satisfied by the all-`true` assignment. -/
theorem audit_sat_example :
    ∃ cnf, parseDimacs Plain.plainNvSatBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α := by
  have hs : Plain.plainNvSatCnf.Sat (fun _ => true) := by
    simp [Plain.plainNvSatCnf, CNF.Sat, CNF.eval_add, CNF.Clause.eval,
      CNF.Clause.literals_ofLiterals]
  exact ⟨_, Plain.parseDimacs_plainSat, fun hu => audit_unsat_not_sat _ _ hu hs, _, hs⟩

/-! ## 3. Module shapes -/

#guard Plain.plainFns.length == 59
#guard Plain.plainModule.checkAcyclic == true
#guard Full.fullFns.length == 166
#guard Full.fullModule.checkAcyclic == true

/-! ## 4. Source-level contracts of `kissat_solve_bytes`

The C0 entry point is `uint64_t kissat_solve_bytes(const uint8_t *cnf_ptr, uint64_t cnf_len,
uint8_t *work_ptr, uint64_t work_len, uint64_t fuel)`. Memory is described in separation logic:
`bytes p bs` owns the bytes `bs` at `[p, p + bs.length)`, `region p n` owns `n` bytes of arbitrary
content at `[p, p + n)`, `⋆` is separating conjunction, and `R` is an arbitrary frame (memory the
caller owns and the solver must not touch). `Func.wp Γ body args m Q X` says: started in memory
`m`, the body terminates normally with results satisfying `Q` (and never takes an `exit`
satisfying `X` unless allowed). -/

/-- **`D-Plain` source correctness** (restates `Plain.plain_solve_bytes_correct`). For any DIMACS
bytes, workspace size, fuel and frame: the result is `0`, `10` or `20`; `20` means the input
parses to an unsatisfiable CNF; `10` means it parses to a satisfiable CNF (with a witness); the
input bytes are unchanged, the workspace is returned as a `region`, and the frame `R` is kept. -/
theorem audit_plain_solve_bytes_correct
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp Plain.plainEnv Plain.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  Plain.plain_solve_bytes_correct hcfit hwfit hm

/-- **`D-Plain` UNSAT non-vacuity** (restates `Plain.plain_unsat_nonvacuous`): on the bytes of
`p cnf 1 2 / 1 0 / -1 0` (placed at `0x1000`, followed by a 2048-byte workspace, fuel 16), the
solver really answers `20`, so the UNSAT branch of the contract is reachable. -/
theorem audit_plain_unsat_nonvacuous :
    Func.wp Plain.plainUnsatEnv Plain.kissat_solve_bytes_body
      (0x1000#64, BitVec.ofNat 64 Plain.plainNvUnsatBytes.length,
        0x1000#64 + BitVec.ofNat 64 Plain.plainNvUnsatBytes.length, 2048#64, 16#64, ())
      ((Plain.plainNvUnsatBytes ++ List.replicate 2048 0).At 0x1000#64)
      (fun rs _ => rs = (20#64, ()) ∧ Plain.plainNvUnsatCnf.Unsat) (fun _ _ _ _ => False) :=
  Plain.plain_unsat_nonvacuous

/-- **`D-Plain` SAT non-vacuity** (restates `Plain.plain_sat_nonvacuous`): on the bytes of
`p cnf 1 1 / 1 0` the solver really answers `10`. -/
theorem audit_plain_sat_nonvacuous :
    Func.wp Plain.plainSatEnv Plain.kissat_solve_bytes_body
      (0x1000#64, BitVec.ofNat 64 Plain.plainNvSatBytes.length,
        0x1000#64 + BitVec.ofNat 64 Plain.plainNvSatBytes.length, 2048#64, 16#64, ())
      ((Plain.plainNvSatBytes ++ List.replicate 2048 0).At 0x1000#64)
      (fun rs _ => rs = (10#64, ()) ∧ ¬ Plain.plainNvSatCnf.Unsat ∧ ∃ α, Plain.plainNvSatCnf.Sat α)
      (fun _ _ _ _ => False) :=
  Plain.plain_sat_nonvacuous

/-- **`D-Full` contract** (unfolds `Full.fullSolveBytesSpec`, the entry of `fullEnv` for
`kissat_solve_bytes`). It is UNSAT-only: the caller provides DIMACS bytes, a workspace and a frame
`R`; on return the result is `0`, `10` or `20`, `20` certifies that the input parses to an
unsatisfiable CNF, and the memory is restored. No claim is made about the answer `10` (model
reconstruction after inprocessing is intentionally not verified). -/
theorem audit_full_spec_contract
    (cnf_ptr cnf_len work_ptr work_len fuel : BitVec 64) (m : Mem 64) (Q : Post [i64])
    (X : XPost) :
    Full.fullSolveBytesSpec (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q X ↔
      ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
        cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
        cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
        ∀ r m',
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
          Q (r, ()) m' :=
  Iff.rfl

/-- `fullEnv` assigns exactly `fullSolveBytesSpec` to `kissat_solve_bytes` (the last of the 166
rows of `fullSpecTable`), so `ModuleOk fullEnv fullModule` is a statement about this contract. -/
theorem audit_fullEnv_eq :
    Full.fullEnv = Env.ofTable (Full.fullSpecTable Full.fullSolveBytesSpec) :=
  rfl

/-! ## 5. Verified Canonical `D-Full` Bridge Coverage (`166/166` + `FullProof` Assembly)

Canonical `Full.fullSpecTable Full.fullSolveBytesSpec` lists 166 functions (`FullSpec.lean`).
Across `FullBridgeLemmas1`–`7` (`145`), `FullBridgeLemmas8a` (`6`: `[106..111]`),
`FullBridgeLemmas8b` (`7`: `[62,63,64,66,67,68,77]`), `FullOneLitConflLemmas` (`1`: `[78]`),
`FullDeduce1UipLemmas` (`1`: `[79]`), and `FullBridgeLemmas9` (`6`: `[160..165]`), all `166`
of `166` entries now have machine-checked `SpecEntry.Impl Full.fullEnv` bridges (`FullProof`
proves top-level UNSAT and unconditional `166/166` `ModuleOk` assembly, with UNSAT non-vacuity in
`FullOneLitConflLemmas` and `FullDeduce1UipNv`), alongside `D-Full` component contracts
(`FullVivifyLemmas`, `FullTransLemmas`, `FullProbeTransLemmas`), all verified with zero
target-architecture imports. -/

#guard Full.fullBridge7Indices.length == 22
#guard Full.fullBridge8aIndices.length == 6
#guard Full.fullBridge8bIndices.length == 7
#guard Full.fullBridge9Indices.length == 6
#guard Full.fullBridge8aIndices == Full.fullRemaining8aIndices
#guard (Full.fullBridge8bIndices ++ [78, 79]) == Full.fullRemaining8bIndices
#guard Full.fullRemaining8bIndices.length == 9

theorem audit_full_table_sigs :
    (Full.fullSpecTable Full.fullSolveBytesSpec).map (fun e => (e.name, e.as, e.rs)) =
      Full.fullModule.fns.map (fun f => (f.name, f.as, f.rs)) :=
  Full.fullSpecTable_sigs Full.fullSolveBytesSpec

theorem audit_full_table_noExit :
    ∀ e ∈ Full.fullSpecTable Full.fullSolveBytesSpec, e.noExit = true :=
  Full.fullSpecTable_noExit Full.fullSolveBytesSpec

theorem audit_full_bridge7_ok (n : Nat) (hn : n ∈ Full.fullBridge7Indices) :
    ∃ fn row,
      Full.fullFns[n]? = some fn ∧
        (Full.fullSpecTable Full.fullSolveBytesSpec)[n]? = some row ∧
          SpecEntry.Impl Full.fullEnv fn row :=
  Full.full_bridge_7_ok n hn

theorem audit_full_qrenum_br (Γ : Env) :
    ∀ a m Q X, Full.fullQueueRenumberSpec a m Q X →
      Func.wp Γ Full.full_queue_renumber_body a m Q X :=
  Full.full_queue_renumber_bridge_wp Γ

theorem audit_full_isqrt_br (Γ : Env) :
    ∀ a m Q X, Full.fullIsqrtSpec a m Q X →
      Func.wp Γ Full.full_isqrt_body a m Q X :=
  Full.full_isqrt_bridge_wp Γ

theorem audit_full_walk_br (Γ : Env)
    (hCol : ∀ (a : Tup Val [i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      Full.fullWalkCollectSpec a m Q X → Γ "full_walk_collect" [i64] [i64] a m Q X)
    (hSat : ∀ (a : Tup Val [i64, i64, i64]) (m : Mem 64) (Q : Post [.bool]) (X : XPost),
      Full.fullWalkClSatSpec a m Q X → Γ "full_walk_cl_sat" [i64, i64, i64] [.bool] a m Q X)
    (hRng : ∀ (a : Tup Val [i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      Full.fullRngNextSpec a m Q X → Γ "full_rng_next" [i64] [i64] a m Q X)
    (hPick : ∀ (a : Tup Val [i64, i64, i64]) (m : Mem 64) (Q : Post [i32]) (X : XPost),
      Full.fullWalkPickLitSpec a m Q X →
        Γ "full_walk_pick_lit" [i64, i64, i64] [i32] a m Q X) :
    ∀ a m Q X, Full.fullWalkSpec a m Q X →
      Func.wp Γ Full.full_walk_body a m Q X :=
  Full.full_walk_bridge_wp Γ hCol hSat hRng hPick

theorem audit_full_lucky_br (Γ : Env)
    (hPol : ∀ (a : Tup Val [i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      Full.fullLuckyPolarSpec a m Q X → Γ "full_lucky_polar" [i64] [i64] a m Q X)
    (hScan : ∀ (a : Tup Val [i64, .bool, .bool]) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      Full.fullLuckyScanSpec a m Q X →
        Γ "full_lucky_scan" [i64, .bool, .bool] [i64] a m Q X)
    (hAsn : ∀ (a : Tup Val [i64, i32, i32]) (m : Mem 64) (Q : Post []) (X : XPost),
      Full.fullAssignSpec a m Q X → Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hBt : ∀ (a : Tup Val [i64, i64]) (m : Mem 64) (Q : Post []) (X : XPost),
      Full.fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ (a : Tup Val [i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      Full.fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullLuckySpec a m Q X →
      Func.wp Γ Full.full_lucky_body a m Q X :=
  Full.full_lucky_bridge_wp Γ hPol hScan hAsn hBt hProp

theorem audit_full_reduce_br (Γ : Env)
    (hSqrt : ∀ (a : Tup Val [i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      Full.fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hLog : ∀ (a : Tup Val [i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      Full.fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hNext : ∀ (a : Tup Val [i64, i32]) (m : Mem 64) (Q : Post [i32]) (X : XPost),
      Full.fullArenaNextSpec a m Q X → Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hTiers : ∀ (a : Tup Val [i64]) (m : Mem 64) (Q : Post []) (X : XPost),
      Full.fullRecomputeTiersSpec a m Q X → Γ "full_recompute_tiers" [i64] [] a m Q X)
    (hMarks : ∀ (a : Tup Val [i64, .bool]) (m : Mem 64) (Q : Post []) (X : XPost),
      Full.fullMarkReasonsSpec a m Q X → Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hSort : ∀ (a : Tup Val [i64, i64]) (m : Mem 64) (Q : Post []) (X : XPost),
      Full.fullSortRedsSpec a m Q X → Γ "full_sort_reds" [i64, i64] [] a m Q X)
    (hBt : ∀ (a : Tup Val [i64, i64]) (m : Mem 64) (Q : Post []) (X : XPost),
      Full.fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ (a : Tup Val [i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      Full.fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ (a : Tup Val [i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      Full.fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullReduceSpec a m Q X →
      Func.wp Γ Full.full_reduce_body a m Q X :=
  Full.full_reduce_bridge_wp Γ hSqrt hLog hNext hTiers hMarks hSort hBt hProp hSweep

theorem audit_full_viv_deduce_wp (Γ : Env) :
    ∀ a m Q X, Full.FullVivifySpecs.fullVivDeduceSpec a m Q X →
      Func.wp Γ Full.full_viv_deduce_body a m Q X :=
  Full.full_viv_deduce_wp Γ

theorem audit_full_trans_wp (Γ : Env)
    (hBt : ∀ (args : Tup Val [i64, i64]) (m : Mem 64) (Q : Post []) (X : XPost),
      Full.fullBacktrackSpec args m Q X → Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hLit : ∀ (args : Tup Val [i64, i32]) (m : Mem 64) (Q : Post [.bool]) (X : XPost),
      Full.fullTransLitSpec args m Q X → Γ "full_trans_lit" [i64, i32] [.bool] args m Q X)
    (hProp : ∀ (args : Tup Val [i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      Full.fullPropagateSpec args m Q X → Γ "full_propagate" [i64] [i64] args m Q X)
    (hDefrag : ∀ (args : Tup Val [i64]) (m : Mem 64) (Q : Post []) (X : XPost),
      Full.fullWstackDefragSpec args m Q X → Γ "full_wstack_defrag" [i64] [] args m Q X) :
    ∀ a m Q X, Full.fullTransitiveSpec a m Q X →
      Func.wp Γ Full.full_transitive_body a m Q X :=
  Full.full_transitive_wp Γ hBt hLit hProp hDefrag

theorem audit_full_probe_run_wp (Γ : Env)
    (hBt : ∀ (args : Tup Val [i64, i64]) (m : Mem 64) (Q : Post []) (X : XPost),
      Full.FullProbeTransSpecs.fullBacktrackSpec args m Q X →
        Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hAssume : ∀ (args : Tup Val [i64, i32]) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      Full.FullProbeTransSpecs.fullProbeAssumePairSpec args m Q X →
        Γ "full_probe_assume_pair" [i64, i32] [i64] args m Q X) :
    ∀ a m Q X, Full.FullProbeTransSpecs.fullProbeRunSpec a m Q X →
      Func.wp Γ Full.full_probe_run_body a m Q X :=
  Full.full_probe_run_wp Γ hBt hAssume

/-- **`D-Full` Bridge 8a** (`FullBridgeLemmas8a.full_bridge_8a_ok`): all 6 `ProbeTrans` indices
`[106..111]` satisfy `SpecEntry.Impl Full.fullEnv`. -/
theorem audit_full_bridge_8a_ok :
    ∀ n ∈ Full.fullBridge8aIndices,
      ∃ fn row, Full.fullFns[n]? = some fn ∧
        (Full.fullSpecTable Full.fullSolveBytesSpec)[n]? = some row ∧
        SpecEntry.Impl Full.fullEnv fn row :=
  Full.full_bridge_8a_ok

/-- **`D-Full` `full_probe_run` bridge** (`FullBridgeLemmas8a.full_probe_run_bridge_wp`): links
the `D-Full` probe-run contract to `Full.fullProbeRunSpec` under `Γ`. -/
theorem audit_full_probe_run_bridge_wp (Γ : Env)
    (hBt : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAssumePair : ∀ a m Q X, Full.fullProbeAssumePairSpec a m Q X →
      Γ "full_probe_assume_pair" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, Full.fullProbeRunSpec a m Q X →
      Func.wp Γ Full.full_probe_run_body a m Q X :=
  Full.full_probe_run_bridge_wp Γ hBt hAssumePair

/-- **`D-Full` Bridge 8b** (`FullBridgeLemmas8b.full_bridge_8b_ok`): all 7 Analyze/OTFS indices
`[62, 63, 64, 66, 67, 68, 77]` satisfy `SpecEntry.Impl Full.fullEnv`. -/
theorem audit_full_bridge_8b_ok :
    ∀ n ∈ Full.fullBridge8bIndices,
      ∃ fn row, Full.fullFns[n]? = some fn ∧
        (Full.fullSpecTable Full.fullSolveBytesSpec)[n]? = some row ∧
        SpecEntry.Impl Full.fullEnv fn row :=
  Full.full_bridge_8b_ok

/-- **`D-Full` `full_analyze_rsn` bridge** (`FullBridgeLemmas8b.full_analyze_rsn_bridge_wp`). -/
theorem audit_full_analyze_rsn_bridge_wp (Γ : Env)
    (hLit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullAnalyzeRsnSpec a m Q X →
      Func.wp Γ Full.full_analyze_rsn_body a m Q X :=
  Full.full_analyze_rsn_bridge_wp Γ hLit

/-- **`D-Full` `full_otfs_large` bridge** (`FullBridgeLemmas8b.full_otfs_large_bridge_wp`). -/
theorem audit_full_otfs_large_bridge_wp (Γ : Env)
    (hUnw : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullOtfsLargeSpec a m Q X →
      Func.wp Γ Full.full_otfs_large_body a m Q X :=
  Full.full_otfs_large_bridge_wp Γ hUnw hPush

/-- **`D-Full` `full_otfs_bin` bridge** (`FullBridgeLemmas8b.full_otfs_bin_bridge_wp`). -/
theorem audit_full_otfs_bin_bridge_wp (Γ : Env)
    (hUnw : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullOtfsBinSpec a m Q X →
      Func.wp Γ Full.full_otfs_bin_body a m Q X :=
  Full.full_otfs_bin_bridge_wp Γ hUnw hPush

/-- **`D-Full` Bridge 9** (`FullBridgeLemmas9.full_bridge_9_ok`): all 6 top-level orchestrator
indices `[160..165]` satisfy `SpecEntry.Impl Full.fullEnv`. -/
theorem audit_full_bridge_9_ok :
    ∀ n ∈ Full.fullBridge9Indices,
      ∃ fn row, Full.fullFns[n]? = some fn ∧
        (Full.fullSpecTable Full.fullSolveBytesSpec)[n]? = some row ∧
        SpecEntry.Impl Full.fullEnv fn row :=
  Full.full_bridge_9_ok

/-- **`D-Full` top-level `kissat_solve_bytes` WP** (`FullProof1.kissat_solve_bytes_wp`). -/
theorem audit_kissat_solve_bytes_wp (Γ : Env)
    (hInit : ∀ a m Q X, Full.fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hParse : ∀ a m Q X, Full.fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hPre : ∀ a m Q X, Full.fullPreprocessSpec a m Q X →
      Γ "full_preprocess" [i64] [i64] a m Q X)
    (hSearch : ∀ a m Q X, Full.fullSearchSpec a m Q X →
      Γ "full_search" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, Full.fullExtendSpec a m Q X →
      Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ args m Q X, Full.fullSolveBytesSpec args m Q X →
      Func.wp Γ Full.kissat_solve_bytes_body args m Q X :=
  Full.kissat_solve_bytes_wp Γ hInit hParse hPre hSearch hExt hCheck

/-- **`D-Full` `kissat_solve_bytes` bridge** (`FullBridgeLemmas9.kissat_solve_bytes_bridge_wp`).
-/
theorem audit_kissat_solve_bytes_bridge_wp (Γ : Env)
    (hInit : ∀ a m Q X, Full.fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hParse : ∀ a m Q X, Full.fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hPre : ∀ a m Q X, Full.fullPreprocessSpec a m Q X →
      Γ "full_preprocess" [i64] [i64] a m Q X)
    (hSearch : ∀ a m Q X, Full.fullSearchSpec a m Q X →
      Γ "full_search" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, Full.fullExtendSpec a m Q X →
      Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullSolveBytesSpec a m Q X →
      Func.wp Γ Full.kissat_solve_bytes_body a m Q X :=
  Full.kissat_solve_bytes_bridge_wp Γ hInit hParse hPre hSearch hExt hCheck

/-- **`D-Full` source-level UNSAT soundness** (`FullProof.full_solve_bytes_correct`): under
`Full.fullEnv`, `kissat_solve_bytes` returns `{0, 10, 20}`, `20` certifies `cnf.Unsat`, and the
input bytes, workspace, and frame `R` are preserved. -/
theorem audit_full_solve_bytes_correct {cnf_ptr work_ptr fuel : BitVec 64}
    {cnfBytes : List UInt8} {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp Full.fullEnv Full.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' => (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  Full.full_solve_bytes_correct hcfit hwfit hm

/-- **`D-Full` source-level UNSAT non-vacuity** (`FullProof.full_unsat_nonvacuous`): concrete
`Mem 64` witness showing `kissat_solve_bytes` reaches `20` with `fullNvUnsatCnf.Unsat` under
`XPost := False`. -/
theorem audit_full_unsat_nonvacuous :
    let m0 : Mem 64 := (Full.fullPayload Full.fullNvUnsatBytes).At Full.fullNvCnfPtr
    Func.wp Full.fullUnsatEnv Full.kissat_solve_bytes_body
      (Full.fullNvCnfPtr, BitVec.ofNat 64 Full.fullNvUnsatBytes.length,
        Full.fullNvWorkPtr Full.fullNvUnsatBytes, 4096#64, 16#64, ())
      m0 (fun rs _ => rs = (20#64, ()) ∧ Full.fullNvUnsatCnf.Unsat)
      (fun _ _ _ _ => False) :=
  Full.full_unsat_nonvacuous

/-- **`D-Full` `ModuleOk` missing-slice lemma** (`FullProof.fullEnv_moduleOk_of_missing`): reduces
`ModuleOk Full.fullEnv Full.fullModule` to `fullRemaining8aIndices` (`6`) and
`fullRemaining8bIndices` (`9`). -/
theorem audit_fullEnv_moduleOk_of_missing
    (h8a : ∀ n ∈ Full.fullRemaining8aIndices, ∃ fn row, Full.fullFns[n]? = some fn ∧
      (Full.fullSpecTable Full.fullSolveBytesSpec)[n]? = some row ∧
      SpecEntry.Impl Full.fullEnv fn row)
    (h8b : ∀ n ∈ Full.fullRemaining8bIndices, ∃ fn row, Full.fullFns[n]? = some fn ∧
      (Full.fullSpecTable Full.fullSolveBytesSpec)[n]? = some row ∧
      SpecEntry.Impl Full.fullEnv fn row) :
    ModuleOk Full.fullEnv Full.fullModule :=
  Full.fullEnv_moduleOk_of_missing h8a h8b

/-- **`D-Full` `full_one_lit_confl` bridge** (`FullOneLitConflLemmas.full_one_lit_confl_bridge_wp`,
row `[78]`). -/
theorem audit_full_one_lit_confl_bridge_wp :
    ∃ fn' row', Full.fullFns[78]? = some fn' ∧
      (Full.fullSpecTable Full.fullSolveBytesSpec)[78]? = some row' ∧
      SpecEntry.Impl Full.fullEnv fn' row' :=
  Full.full_one_lit_confl_bridge_wp

/-- **`D-Full` `full_one_lit_confl` concrete UNSAT non-vacuity**
(`FullOneLitConflLemmas.nv_full_one_lit_confl`). -/
theorem audit_nv_full_one_lit_confl :
    Func.wp Full.fullEnv Full.full_one_lit_confl_body (Full.nvOneLitCfg.hdr, ()) Full.nvOneLitMem
      (fun (r, ()) m' => r = 20#64 ∧ Full.nvOneLitF0.Unsat ∧
        Full.FullMem Full.nvOneLitCfg Full.nvOneLitState m')
      (fun _ _ _ _ => False) :=
  Full.nv_full_one_lit_confl

/-- **`D-Full` `full_deduce_1uip` bridge** (`FullDeduce1UipLemmas.full_deduce_1uip_bridge_wp`,
row `[79]`). -/
theorem audit_full_deduce_1uip_bridge_wp :
    ∃ fn' row', Full.fullFns[79]? = some fn' ∧
      (Full.fullSpecTable Full.fullSolveBytesSpec)[79]? = some row' ∧
      SpecEntry.Impl Full.fullEnv fn' row' :=
  Full.full_deduce_1uip_bridge_wp

/-- **`D-Full` `full_deduce_1uip` parametric non-vacuity**
(`FullDeduce1UipNv.nv_full_deduce_1uip_of_wp`): given the WP for row `[79]`, concrete `Mem 64`
execution reaches a sound outcome under `XPost := False`. -/
theorem audit_nv_full_deduce_1uip_of_wp
    (hwp : ∀ args m Q X, Full.fullDeduce1uipSpec args m Q X →
      Func.wp Full.fullEnv Full.full_deduce_1uip.body args m Q X) :
    Func.wp Full.fullEnv Full.full_deduce_1uip.body (Full.nvOneLitCfg.hdr, ()) Full.nvDeduceMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧
          Full.nvDeduceF0.Unsat ∧
            ∃ s', Full.FullState.LengthsOk Full.nvOneLitCfg s' ∧
              Full.FullMem Full.nvOneLitCfg s' m' ∧
              Full.FullOtfsInvW Full.nvOneLitCfg Full.nvDeduceF0 [[0], [1]] s' ∧
              (r = 1#64 → s'.core.cur_level = 1 ∧ 1 ≤ s'.core.tmp_len ∧
                (cnfOfClauses [[0], [1]]).EntailsClause
                  (cnfClause (List.map BitVec.toNat (List.take s'.core.tmp_len s'.core.tmp)))) ∧
              (r = 2#64 → ∃ cut', cut' ≤ s'.core.trail_end ∧
                Full.FullCutInvW Full.nvOneLitCfg Full.nvDeduceF0 [[0], [1]] cut' s' ∧
                Full.FullConflictOkCut [[0], [1]] cut' s'))
      (fun _ _ _ _ => False) :=
  Full.nv_full_deduce_1uip_of_wp hwp

/-- **`D-Full` `full_deduce_1uip` unconditional UNSAT non-vacuity**
(`FullDeduce1UipNv.nv_full_deduce_1uip`). -/
theorem audit_nv_full_deduce_1uip :
    Func.wp Full.fullEnv Full.full_deduce_1uip.body (Full.nvOneLitCfg.hdr, ()) Full.nvDeduceMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧
          Full.nvDeduceF0.Unsat ∧
            ∃ s', Full.FullState.LengthsOk Full.nvOneLitCfg s' ∧
              Full.FullMem Full.nvOneLitCfg s' m' ∧
              Full.FullOtfsInvW Full.nvOneLitCfg Full.nvDeduceF0 [[0], [1]] s' ∧
              (r = 1#64 → s'.core.cur_level = 1 ∧ 1 ≤ s'.core.tmp_len ∧
                (cnfOfClauses [[0], [1]]).EntailsClause
                  (cnfClause (List.map BitVec.toNat (List.take s'.core.tmp_len s'.core.tmp)))) ∧
              (r = 2#64 → ∃ cut', cut' ≤ s'.core.trail_end ∧
                Full.FullCutInvW Full.nvOneLitCfg Full.nvDeduceF0 [[0], [1]] cut' s' ∧
                Full.FullConflictOkCut [[0], [1]] cut' s'))
      (fun _ _ _ _ => False) :=
  Full.nv_full_deduce_1uip

/-- **`D-Full` unconditional `166/166` `ModuleOk fullEnv fullModule`**
(`FullProof.fullEnv_moduleOk`). -/
theorem audit_fullEnv_moduleOk : ModuleOk Full.fullEnv Full.fullModule :=
  Full.fullEnv_moduleOk

/-- **`D-Full` unconditional `166/166` `ModuleOk fullUnsatEnv fullModule`**
(`FullProof.fullUnsatEnv_moduleOk`). -/
theorem audit_fullUnsatEnv_moduleOk : ModuleOk Full.fullUnsatEnv Full.fullModule :=
  Full.fullUnsatEnv_moduleOk

/-! ## 6. M2 Fast Scheduler (`FullFastSched`: `173` fns) & `FullFastBveBudgets` -/

-- Source-level only (`FullFastSched` + `FullFastBveBudgets`); no `*Cert*` or arch imports.
-- Partially proved: `schedEnv_moduleOk` does not exist (`sched_proved_rows_ok` covers `16/173`
-- rows plus top-level `Func.wp`); legacy machine-code theorems take an undischarged
-- `(hmok : ModuleOk schedEnv schedModule)` hypothesis (superseded by `FullFast` and `FullM3`).
-- `FullFastBveBudgets` has unconditional `ModuleOk` (`7/7` fns).

section M2aFastSchedAudit

open Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat.Full
open Std.ExtHashMap (emp)
open LeanQbe.T.Examples.Kissat.FullFastSched
  (schedSplicedFns schedSplicedFns_wf schedModule sched_acyclic schedSpecTable mkSchedEnv
    schedEnv schedProvedIndices sched_proved_rows_ok sched_solve_bytes_correct
    sched_unsat_nonvacuous schedUnsatEnv schedNvUnsatBytes schedNvUnsatCnf schedNvCnfPtr
    schedNvWorkPtr schedPayload)

theorem audit_sched_wf : ∀ f ∈ schedSplicedFns, f.Wf :=
  schedSplicedFns_wf

theorem audit_sched_acyc : schedModule.checkAcyclic = true :=
  sched_acyclic

theorem audit_sched_rows (ms : Spec [i64, i64, i64, i64, i64] [i64])
    (hw : ∀ a m Q X, ms a m Q X → fullSolveBytesCoreSpec a m Q X) :
    ∀ n ∈ schedProvedIndices,
      ∃ fn row, schedSplicedFns[n]? = some fn ∧ (schedSpecTable ms)[n]? = some row ∧
        SpecEntry.Impl (mkSchedEnv ms) fn row :=
  sched_proved_rows_ok ms hw

theorem audit_sched_ok {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp schedEnv Full.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  sched_solve_bytes_correct hcfit hwfit hm

theorem audit_sched_nv :
    let m0 : Mem 64 := (schedPayload schedNvUnsatBytes).At schedNvCnfPtr
    Func.wp schedUnsatEnv Full.kissat_solve_bytes_body
      (schedNvCnfPtr, BitVec.ofNat 64 schedNvUnsatBytes.length,
        schedNvWorkPtr schedNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 20#64 ∧ schedNvUnsatCnf.Unsat ∧
        (bytes schedNvCnfPtr schedNvUnsatBytes ⋆
          region (schedNvWorkPtr schedNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  sched_unsat_nonvacuous

end M2aFastSchedAudit

section M2aBveBudgetsAudit

open Std.Sat LeanQbe.T LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
  (TmkZero fastBveBudgetsModule fastBveBudgets_allFns_wf fastBveBudgets_acyclic
    fastBveBudgetsSpecTable fastBveBudgets_tableImpl fastBveBudgetsEnv fastBveBudgets_moduleOk
    full_bve_var_body bve_gate_pg_ng_extUnsatSound nvDenseUnsatState nvDenseUnsatMem
    nv_fast_bve_var nv_fast_bve_var_def fullBveGatesDefFastSpec fullBveWeakenTmkSpec
    fullBveCommitResTmkSpec fullExtendPush2TmkSpec fullExtendPushClTmkSpec)

theorem audit_bve_wf : AllFns Fn.Wf fastBveBudgetsModule.fns :=
  fastBveBudgets_allFns_wf

theorem audit_bve_acyc : fastBveBudgetsModule.checkAcyclic = true :=
  fastBveBudgets_acyclic

theorem audit_bve_impl :
    TableImpl fastBveBudgetsEnv fastBveBudgetsModule.fns fastBveBudgetsSpecTable :=
  fastBveBudgets_tableImpl

theorem audit_bve_modok : ModuleOk fastBveBudgetsEnv fastBveBudgetsModule :=
  fastBveBudgets_moduleOk

theorem audit_bve_ext {F0 : CNF Nat} {cur_vars v : Nat}
    {Rest P N : List (List Nat)} {pg ng : Nat → Bool}
    (hExt : ExtUnsatSound F0 cur_vars (Rest ++ P.map (fun C => (2 * v) :: C) ++
      N.map (fun D => (2 * v + 1) :: D))) :
    let Res := ((List.range P.length).flatMap fun i =>
      (List.range N.length).filterMap fun j =>
        if pg i || ng j then some (P[i]?.getD [] ++ N[j]?.getD []) else none)
    ExtUnsatSound F0 cur_vars (Rest ++ Res) :=
  bve_gate_pg_ng_extUnsatSound hExt

theorem audit_bve_nv :
    Func.wp fastBveBudgetsEnv FullFastBveBudgets.full_bve_var_body
      (nvOneLitCfg.hdr, 0#32, ()) nvDenseUnsatMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧ (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fast_bve_var

theorem audit_bve_nv_def :
    let Γdef : Env := fun f as bs xs m Q X =>
      if f = "full_bve_gates" then
        ∃ (h1 : as = [i64, i32, i32, i32]) (h2 : bs = []),
          fullBveGatesDefFastSpec (h1 ▸ xs) m (h2 ▸ Q) X
      else if f = "full_bve_weaken" then
        ∃ (h1 : as = [i64, i32, i32, i32]) (h2 : bs = [.bool]),
          fullBveWeakenTmkSpec (h1 ▸ xs) m (h2 ▸ Q) X
      else if f = "full_bve_commit_res" then
        ∃ (h1 : as = [i64, i64, i64]) (h2 : bs = [i64]),
          fullBveCommitResTmkSpec (h1 ▸ xs) m (h2 ▸ Q) X
      else if f = "full_extend_push2" then
        ∃ (h1 : as = [i64, i32, i32]) (h2 : bs = [.bool]),
          fullExtendPush2TmkSpec (h1 ▸ xs) m (h2 ▸ Q) X
      else if f = "full_extend_push_cl" then
        ∃ (h1 : as = [i64, i32, i32]) (h2 : bs = [.bool]),
          fullExtendPushClTmkSpec (h1 ▸ xs) m (h2 ▸ Q) X
      else fastBveBudgetsEnv f as bs xs m Q X
    Func.wp Γdef FullFastBveBudgets.full_bve_var_body
      (nvOneLitCfg.hdr, 0#32, ()) nvDenseUnsatMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧ TmkZero s' ∧
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fast_bve_var_def

end M2aBveBudgetsAudit

/-! ## 7. M2 Fast-Core BCP (`FullFastCore`: `[47..49]` splice & UNSAT soundness) -/

section M2bFastCoreAudit

open LeanQbe.T LeanQbe.T.Examples.Kissat
open Std.ExtHashMap (emp)
open LeanQbe.T.Examples.Kissat.FastCore
  (fastCoreEnv fastCoreFullModule fastCore_fullEnv_moduleOk_of_missing
    full_propagate_body nvFastPropCfg nvFastPropMem nv_fast_propagate_sound)

/-- **`FullFastCore` spliced `ModuleOk` missing-slice lemma**
(`FullFastCoreLemmas.fastCore_fullEnv_moduleOk_of_missing`): replaces `[47..49]` in
`Full.fullModule` while preserving `151/166` closed proofs. -/
theorem audit_fcore_modok
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → Full.fullSolveBytesCoreSpec a m Q X)
    (h8a : ∀ n ∈ Full.fullRemaining8aIndices,
      ∃ fn row, Full.fullFns[n]? = some fn ∧ (Full.fullSpecTable mainSpec)[n]? = some row ∧
        SpecEntry.Impl (Full.mkFullEnv mainSpec) fn row)
    (h8b : ∀ n ∈ Full.fullRemaining8bIndices,
      ∃ fn row, Full.fullFns[n]? = some fn ∧ (Full.fullSpecTable mainSpec)[n]? = some row ∧
        SpecEntry.Impl (Full.mkFullEnv mainSpec) fn row) :
    ModuleOk (Full.mkFullEnv mainSpec) fastCoreFullModule :=
  fastCore_fullEnv_moduleOk_of_missing mainSpec hweaken h8a h8b

/-- **`FullFastCore` `full_propagate` concrete `Mem 64` UNSAT soundness**
(`FullFastCoreLemmas.nv_fast_propagate_sound`): under `fastCoreEnv` and `XPost := False`,
conflict return (`r = 1#64`) certifies `Full.nvOneLitF0.Unsat`. -/
theorem audit_fcore_nv :
    Func.wp fastCoreEnv full_propagate_body (nvFastPropCfg.hdr, ()) nvFastPropMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) ∧
        (r = 1#64 → Full.nvOneLitF0.Unsat) ∧
        ∃ s', (Full.FullMem nvFastPropCfg s' ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  nv_fast_propagate_sound

end M2bFastCoreAudit

/-! ## 8. M2 3-Hop BVA & Max-Degree Binary Heap (`FullBvaHeap`: `13` fns) -/

section M2bBvaHeapAudit

open Std.Sat LeanQbe.T LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
  (bvaHeapEnv bvaHeapModule bvaHeap_moduleOk nvBvaDenseMem nv_bva_factor)

/-- **`FullBvaHeap` closed `19`-row `ModuleOk` (`13` fns + `6` canonical `Full` externs)**
(`FullBvaHeapLemmas.bvaHeap_moduleOk`). -/
theorem audit_bva_modok : ModuleOk bvaHeapEnv bvaHeapModule :=
  bvaHeap_moduleOk

/-- **`FullBvaHeap` `full_factor` concrete `Mem 64` UNSAT non-vacuity (`XPost := False`)**
(`FullBvaHeapLemmas.nv_bva_factor`). -/
theorem audit_bva_nv_factor :
    Func.wp bvaHeapEnv FullBvaHeap.full_factor_body (nvOneLitCfg.hdr, 10#64, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧ r = 1#64 ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_bva_factor

end M2bBvaHeapAudit

/-! ## 9. M2 Embedded `kitten` (`FullKitten`: `15` fns) -/

section M2bFullKittenAudit

open LeanQbe.T LeanQbe.T.Examples.Kissat.Full

/-- **`FullKitten` closed `ModuleOk` (`15/15` fns + `full_kitten_solve` dispatch)**
(`FullKittenLemmas.fullKittenEnv_moduleOk`). -/
theorem audit_fk_modok : ModuleOk fullKittenEnv fullKittenModule :=
  fullKittenEnv_moduleOk

/-- **`FullKitten` `full_kitten_solve` concrete `Mem 64` `r = 20#64` UNSAT non-vacuity
(`XPost := False`)** (`FullKittenLemmas.nv_full_kitten_solve_unsat20`). -/
theorem audit_fk_nv20 :
    Func.wp fullKittenEnv full_kitten_solve_body
      (nvKittenCfg.hdr, 8192#64, ()) nvKittenMem
      (fun (r, ()) m' => ∃ scr',
        r = 20#64 ∧
        (kittenStateOfScratch scr').incons ≠ 0xFFFFFFFF#32 ∧
        (cnfOfClauses (kittenOrigClausesS scr') ++ unitsCnf (kittenAssumpLitsS scr')).Unsat ∧
        FullMem nvKittenCfg
          { nvKittenState with
            scratch := { nvKittenState.scratch with scratch_buf := scr' } } m')
      (fun _ _ _ _ => False) :=
  nv_full_kitten_solve_unsat20

end M2bFullKittenAudit

/-! ## 10. M2 `FullDefSweep` (`9/9` fns, `defSweepEnv_moduleOk`, NV) -/

section M2bFullDefSweepAudit

open LeanQbe.T.Examples.Kissat.FullDefSweep

theorem _root_.audit_fds_modok :
    ModuleOk defSweepEnv fullDefSweepModule :=
  defSweepEnv_moduleOk

theorem _root_.audit_fds_nv :
    Func.wp defSweepEnv
      LeanQbe.T.Examples.Kissat.FullDefSweep.full_sweep_dense_body
      (nvDefSweepCfg.hdr, 10#64, 8192#64, ()) nvDefSweepMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvDefSweepCfg Full.nvOneLitF0 s' ∧
        (r = 1#64 ∨ r = 20#64) ∧
        Full.nvOneLitF0.Unsat ∧ Full.FullMem nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_full_def_sweep

end M2bFullDefSweepAudit

/-! ## 11. `D-Full M2 Fast` (`FullFastProof`, `196/196` unconditional, UNSAT-only) -/

section M2FullFastAudit

open Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFast

#guard fastFns.length == 196
#guard fastModule.checkAcyclic == true

theorem _root_.audit_fast_wf : ∀ f ∈ fastFns, f.Wf := fastFns_wf

theorem _root_.audit_fast_acyc : fastModule.checkAcyclic = true := fast_acyclic

theorem _root_.audit_fast_modok : ModuleOk fastEnv fastModule := fastEnv_moduleOk

theorem _root_.audit_fast_umodok : ModuleOk fastUnsatEnv fastModule := fastUnsatEnv_moduleOk

theorem _root_.audit_fast_ok
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fastEnv Full.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  fast_solve_bytes_correct hcfit hwfit hm

theorem _root_.audit_fast_nv :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp fastUnsatEnv Full.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 20#64 ∧ fullNvUnsatCnf.Unsat ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  fast_unsat_nonvacuous

end M2FullFastAudit

/-! ## 12. `D-Full M3` (`FullM3Proof`, `204/204` unconditional, UNSAT-only) -/

section M3FullM3Audit

open Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM3

#guard m3Fns.length == 204
#guard m3Module.checkAcyclic == true

theorem _root_.audit_m3_wf : ∀ f ∈ m3Fns, f.Wf := m3Fns_wf

theorem _root_.audit_m3_acyc : m3Module.checkAcyclic = true := m3_acyclic

theorem _root_.audit_m3_modok : ModuleOk m3Env m3Module := m3Env_moduleOk

theorem _root_.audit_m3_umodok : ModuleOk m3UnsatEnv m3Module := m3UnsatEnv_moduleOk

theorem _root_.audit_m3_ok
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m3Env Full.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  m3_solve_bytes_correct hcfit hwfit hm

theorem _root_.audit_m3_nv :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp m3UnsatEnv Full.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 20#64 ∧ fullNvUnsatCnf.Unsat ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  m3_unsat_nonvacuous

end M3FullM3Audit

/-! ## 13. `D-Full M4` (`FullM4Proof`, `231/231` unconditional, UNSAT-only) -/

section M4FullM4Audit

open Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4

#guard m4Fns.length == 231
#guard m4Module.checkAcyclic == true

theorem _root_.audit_m4_wf : ∀ f ∈ m4Fns, f.Wf := m4Fns_wf

theorem _root_.audit_m4_acyc : m4Module.checkAcyclic = true := m4_acyclic

theorem _root_.audit_m4_modok : ModuleOk m4Env m4Module := m4Env_moduleOk

theorem _root_.audit_m4_umodok : ModuleOk m4UnsatEnv m4Module := m4UnsatEnv_moduleOk

theorem _root_.audit_m4_ok
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m4Env FullM4.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  m4_solve_bytes_correct hcfit hwfit hm

theorem _root_.audit_m4_nv :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp m4UnsatEnv FullM4.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 20#64 ∧ fullNvUnsatCnf.Unsat ∧
        (bytes fullNvCnfPtr fullNvUnsatBytes ⋆
          region (fullNvWorkPtr fullNvUnsatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  m4_unsat_nonvacuous

end M4FullM4Audit

/-! ## 14. `#print axioms` (one line each, `⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms audit_unsat_def
#print axioms audit_sat_def
#print axioms audit_unsat_not_sat
#print axioms audit_unsat_example
#print axioms audit_sat_example
#print axioms audit_plain_solve_bytes_correct
#print axioms audit_plain_unsat_nonvacuous
#print axioms audit_plain_sat_nonvacuous
#print axioms audit_full_spec_contract
#print axioms audit_fullEnv_eq
#print axioms audit_full_table_sigs
#print axioms audit_full_table_noExit
#print axioms audit_full_bridge7_ok
#print axioms audit_full_qrenum_br
#print axioms audit_full_isqrt_br
#print axioms audit_full_walk_br
#print axioms audit_full_lucky_br
#print axioms audit_full_reduce_br
#print axioms audit_full_viv_deduce_wp
#print axioms audit_full_trans_wp
#print axioms audit_full_probe_run_wp
#print axioms audit_full_bridge_8a_ok
#print axioms audit_full_probe_run_bridge_wp
#print axioms audit_full_bridge_8b_ok
#print axioms audit_full_analyze_rsn_bridge_wp
#print axioms audit_full_otfs_large_bridge_wp
#print axioms audit_full_otfs_bin_bridge_wp
#print axioms audit_full_bridge_9_ok
#print axioms audit_kissat_solve_bytes_wp
#print axioms audit_kissat_solve_bytes_bridge_wp
#print axioms audit_full_solve_bytes_correct
#print axioms audit_full_unsat_nonvacuous
#print axioms audit_fullEnv_moduleOk_of_missing
#print axioms audit_full_one_lit_confl_bridge_wp
#print axioms audit_nv_full_one_lit_confl
#print axioms audit_full_deduce_1uip_bridge_wp
#print axioms audit_nv_full_deduce_1uip_of_wp
#print axioms audit_nv_full_deduce_1uip
#print axioms audit_fullEnv_moduleOk
#print axioms audit_fullUnsatEnv_moduleOk
#print axioms audit_sched_wf
#print axioms audit_sched_acyc
#print axioms audit_sched_rows
#print axioms audit_sched_ok
#print axioms audit_sched_nv
#print axioms audit_bve_wf
#print axioms audit_bve_acyc
#print axioms audit_bve_impl
#print axioms audit_bve_modok
#print axioms audit_bve_ext
#print axioms audit_bve_nv
#print axioms audit_bve_nv_def
#print axioms audit_fcore_modok
#print axioms audit_fcore_nv
#print axioms audit_bva_modok
#print axioms audit_bva_nv_factor
#print axioms audit_fk_modok
#print axioms audit_fk_nv20
#print axioms audit_fds_modok
#print axioms audit_fds_nv
#print axioms audit_fast_wf
#print axioms audit_fast_acyc
#print axioms audit_fast_modok
#print axioms audit_fast_umodok
#print axioms audit_fast_ok
#print axioms audit_fast_nv
#print axioms audit_m3_wf
#print axioms audit_m3_acyc
#print axioms audit_m3_modok
#print axioms audit_m3_umodok
#print axioms audit_m3_ok
#print axioms audit_m3_nv
#print axioms audit_m4_wf
#print axioms audit_m4_acyc
#print axioms audit_m4_modok
#print axioms audit_m4_umodok
#print axioms audit_m4_ok
#print axioms audit_m4_nv
