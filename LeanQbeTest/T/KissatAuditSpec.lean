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
public import LeanQbe.T.Examples.Kissat.FullVivifyLemmas
public import LeanQbe.T.Examples.Kissat.FullTransLemmas
public import LeanQbe.T.Examples.Kissat.FullProbeTransLemmas
meta import LeanQbe.T.Examples.Kissat.PlainLemmas
meta import LeanQbe.T.Examples.Kissat.FullSpec
meta import LeanQbe.T.Examples.Kissat.FullBridgeLemmas7
import all Std.Sat.CNF.Basic
import all Std.Sat.CNF.Sat

/-!
# Kissat audit, part 1: the trusted specification boundary (architecture-independent)

This file is meant to be read by a human auditor. It restates, with every type written out in
full (no wrapper `abbrev`s introduced here), the statements on which the verified Kissat solvers
`D-Plain` (`plainModule`, 59 functions) and `D-Full` (`fullModule`, 166 functions) rest. It
imports neither `Kraken.X64` nor `Kraken.AArch64`; the machine-code theorems are audited in
`KissatAuditX64.lean` and `KissatAuditArm64.lean`.

## What must be trusted

1. `Std.Sat.CNF.Unsat` and `Std.Sat.CNF.Sat` from the Lean standard library: a CNF is
   unsatisfiable iff every assignment `a : Nat → Bool` evaluates it to `false`, and satisfied by
   `a` iff `a` evaluates it to `true` (§1 below restates both definitions by `Iff.rfl`).
2. `LeanQbe.T.Examples.LratBytes.parseDimacs : List UInt8 → Option (CNF Nat)`, the total, pure
   specification of ASCII DIMACS (header `p cnf <vars> <clauses>`, `0`-terminated clauses,
   `c` comments, whitespace, and nothing but whitespace/comments after the last clause). A
   solver answer is only ever about `cnf` with `parseDimacs cnfBytes = some cnf`; malformed
   input can only produce the answer `0` (unknown). §2 checks the parser on concrete inputs.
3. The Lean kernel and the standard axioms `propext`, `Classical.choice`, `Quot.sound` (§5).
4. For the machine-code theorems only: the Kraken x86-64 / AArch64 instruction semantics and the
   assembler/linker that turn the emitted directives into an executable.

Everything else (the C0 source of both solvers, the `LeanQbe.T` compiler, and all `Func.wp`
proofs) is checked by the kernel and need not be trusted.
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

/-! ## 5. Verified Canonical `D-Full` Bridge Coverage (`FullBridgeLemmas` + Stage-4 Components)

Canonical `Full.fullSpecTable Full.fullSolveBytesSpec` lists 166 functions (`FullSpec.lean`).
Across `FullBridgeLemmas1`–`7`, 145 of those 166 entries (`26 + 32 + 11 + 26 + 18 + 10 + 22`)
now have machine-checked `SpecEntry.Impl Full.fullEnv` / `_bridge_wp` proofs targeting the
canonical `fullEnv`, alongside landed Stage-4 solver component contracts (`FullVivifyLemmas`,
`FullTransLemmas`, `FullProbeTransLemmas`), all verified with zero target-architecture imports. -/

#guard Full.fullBridge7Indices.length == 22

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

/-! ## 6. `#print axioms` (one line each, `⊆ [propext, Classical.choice, Quot.sound]`) -/

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
