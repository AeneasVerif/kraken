module

public import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
public import LeanQbe.T.Examples.Kissat.FullM6SatSound
public import LeanQbe.T.Examples.Kissat.FullM6Orch
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof
public import LeanQbe.T.Examples.Kissat.FullM5SchedLemmas
public import LeanQbe.T.Examples.Kissat.FullSatSound
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullArena1
public import LeanQbe.T.Examples.Kissat.FullM4Proof1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `M6.0` Search, End-to-End `kissat_solve_bytes_m6`, & Tail Table (`FullM6OrchProof2`)

Proves the top-level M6 orchestrator functions from `FullM6Orch.lean` on
`FullM6HdrMem` / `FullM6HdrInv` with ZERO compile-time dependency on
`FullM6OrchProof0/1.lean` or `FullM6OrchAdaptersProof*.lean`:
25: 1. `full_search_m6_wp` (`fullM6SearchSpec`, core `FullM6HdrInv` UNSAT soundness +
26:    `extend_len ≤ extend_cap`) + `full_search_wp` forwarding wrapper.
27: 2. `kissat_solve_bytes_m6_core_wp` (`fullM6SolveBytesCoreModelSpec`, BOTH UNSAT +
28:    constructive `readModelFromWorkM6` SAT model soundness + `UnitUnsatTrace`) +
29:    `kissat_solve_bytes_m6_wp` (`fullM6SolveBytesSpec`) + `kissat_solve_bytes` wrappers.
30: 3. `full_m6_mem_init_exact_wp` (`fullM6MemInitExactSpec` supplying `probing = 0`,
31:    `vals = replicate`, `wvec = replicate` required by `Full.fullParseBodySpec`).
32: 4. Parametric `m6Orch_tail_tableImpl` and `mkM6OrchEnv_moduleOk`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Orch

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullM4
open LeanQbe.T.Examples.Kissat.FullM4Compact
open LeanQbe.T.Examples.Kissat.FullM5Sched
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics
open Kraken.Bedrock2.Test

/-! ## 1. Local Callee & Init Specs (`FullM6SatSound` provides `fullM6*` top-level specs) -/

/-- `full_reduce_m6(h, force)` contract matching `FullM6OrchProof0.m6ReduceSpec`. -/
def m6ReduceSpec : Spec [i64, .bool] [i64] := fun (h, _force, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
    (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInvW c F0 F_cur ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      FullM6HdrInvW c F0 F_cur ext' s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_level ≤ s.core.cur_level → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.cur_vars = s.core.cur_vars → s'.core.tmp = s.core.tmp →
      s'.core.tmp_len = s.core.tmp_len → s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64) →
      (r = 1#64 → 0 < s'.core.cur_level →
        s'.core.cur_level = s.core.cur_level ∧ s'.core.vals = s.core.vals ∧
        s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
        s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem m6ReduceSpec_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {force : Bool} {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r ext' s' m',
      FullM6HdrInvW c F0 F_cur ext' s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_level ≤ s.core.cur_level → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.cur_vars = s.core.cur_vars → s'.core.tmp = s.core.tmp →
      s'.core.tmp_len = s.core.tmp_len → s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64) →
      (r = 1#64 → 0 < s'.core.cur_level →
        s'.core.cur_level = s.core.cur_level ∧ s'.core.vals = s.core.vals ∧
        s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
        s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    m6ReduceSpec (c.hdr, force, ()) m Q X :=
  ⟨c, F0, F_cur, ext, s, R, rfl, hinv, hm, hQ⟩

theorem m6ReduceSpec_elim {h : BitVec 64} {force : Bool} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (hs : m6ReduceSpec (h, force, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
      (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrInvW c F0 F_cur ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        FullM6HdrInvW c F0 F_cur ext' s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
        s'.core.cur_level ≤ s.core.cur_level → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        s'.core.cur_vars = s.core.cur_vars → s'.core.tmp = s.core.tmp →
        s'.core.tmp_len = s.core.tmp_len → s'.scratch.work_stk2 = s.scratch.work_stk2 →
        (r = 20#64 → F0.Unsat) →
        (r = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64) →
        (r = 1#64 → 0 < s'.core.cur_level →
          s'.core.cur_level = s.core.cur_level ∧ s'.core.vals = s.core.vals ∧
          s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
          s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' := hs

theorem m6ReduceSpec_monoX {xs : Tup Val [i64, .bool]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : m6ReduceSpec xs m Q X) : m6ReduceSpec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

/-- `full_switch_mode_m6(h)` specification matching `FullM6OrchProof0.m6SwitchModeSpec`. -/
def m6SwitchModeSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ ext' s' m',
      s'.core = s.core → s'.LengthsOk c → FullProbeScratchPres s s' → M6HdrExtOk ext' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

theorem m6SwitchModeSpec_of {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ ext' s' m',
      s'.core = s.core → s'.LengthsOk c → FullProbeScratchPres s s' → M6HdrExtOk ext' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    m6SwitchModeSpec (c.hdr, ()) m Q X :=
  ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩

theorem m6SwitchModeSpec_elim {h : BitVec 64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hs : m6SwitchModeSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ ext' s' m',
        s'.core = s.core → s'.LengthsOk c → FullProbeScratchPres s s' → M6HdrExtOk ext' →
        (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m' := hs

theorem m6SwitchModeSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : m6SwitchModeSpec xs m Q X) : m6SwitchModeSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

/-- `full_rephase_m6_hdr(h)` specification matching `FullM6OrchAdaptersProof0.m6aRephaseSpec`
verbatim. -/
def m6aRephaseSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullCoreInv c F0 s ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ vals' lvl' rsns' trl' tp' te' prop' cl' unass' fuel' sc' ext' m',
      let s' : FullState :=
        { core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                                trail_pos := tp', trail_end := te', propagated := prop',
                                cur_level := cl', unassigned := unass', fuel := fuel' }
          scratch := sc' }
      M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      FullCoreInv c F0 s' → (s.scratch.stable ≠ 0#64 → cl' = 0) →
      cl' ≤ s.core.cur_level → fuel'.toNat ≤ s.core.fuel.toNat →
      FullExtScratchPres s s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

theorem m6aRephaseSpec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hinv : FullCoreInv c F0 s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ vals' lvl' rsns' trl' tp' te' prop' cl' unass' fuel' sc' ext' m',
      let s' : FullState :=
        { core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                                trail_pos := tp', trail_end := te', propagated := prop',
                                cur_level := cl', unassigned := unass', fuel := fuel' }
          scratch := sc' }
      M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      FullCoreInv c F0 s' → (s.scratch.stable ≠ 0#64 → cl' = 0) →
      cl' ≤ s.core.cur_level → fuel'.toNat ≤ s.core.fuel.toNat →
      FullExtScratchPres s s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    m6aRephaseSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hcfg, hext, hinv, hm, hQ⟩

theorem m6aRephaseSpec_elim {h : BitVec 64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hs : m6aRephaseSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullCoreInv c F0 s ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ vals' lvl' rsns' trl' tp' te' prop' cl' unass' fuel' sc' ext' m',
        let s' : FullState :=
          { core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                                  trail_pos := tp', trail_end := te', propagated := prop',
                                  cur_level := cl', unassigned := unass', fuel := fuel' }
            scratch := sc' }
        M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        FullCoreInv c F0 s' → (s.scratch.stable ≠ 0#64 → cl' = 0) →
        cl' ≤ s.core.cur_level → fuel'.toNat ≤ s.core.fuel.toNat →
        FullExtScratchPres s s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m' := hs

theorem m6aRephaseSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : m6aRephaseSpec xs m Q X) : m6aRephaseSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

/-- `full_simplify_m6(h, do_probe, do_elim)` specification matching `FullM6OrchProof1`. -/
def fullM6SimplifySpec : Spec [i64, .bool, .bool] [i64] := fun (h, _dp, _de, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r c' ext' s' m',
      FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m'

theorem fullM6SimplifySpec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {dp de : Bool} {Q : Post [i64]}
    {X : XPost} (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r c' ext' s' m',
      FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m') :
    fullM6SimplifySpec (c.hdr, dp, de, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩

theorem fullM6SimplifySpec_elim {h : BitVec 64} {dp de : Bool} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hs : fullM6SimplifySpec (h, dp, de, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r c' ext' s' m',
        FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
        (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 20#64 → F0.Unsat) →
        (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
        (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m' := hs

theorem fullM6SimplifySpec_monoX {xs : Tup Val [i64, .bool, .bool]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : fullM6SimplifySpec xs m Q X) :
    fullM6SimplifySpec xs m Q X' := by
  rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

/-- Strengthened `full_m6_mem_init` specification carrying `probing = 0`,
`vals = replicate`, and `wvec = replicate` needed by `Full.fullParseBodySpec`. -/
def fullM6MemInitExactSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cend, work_base, avail, fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (R : Mem 64 → Prop),
      cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_base.toNat + avail.toNat < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_base avail.toNat ⋆ R) m ∧
      (∀ m', (bytes cnf_ptr cnfBytes ⋆ region work_base avail.toNat ⋆ R) m' →
        (avail.toNat < fullM6HdrTotalBytes ∨
          ∀ mv nc rest, parseHeader cnfBytes = some (mv, nc, rest) →
            avail.toNat - fullM6ExtBytes < fullFixedBytes mv + nc * 40 + 136) →
        Q (0#64, ()) m') ∧
      ∀ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (j : Nat)
        (rest : List UInt8) (m' : Mem 64),
        c.hdr = work_base + BitVec.ofNat 64 fullM6ExtBytes →
        c.avail = avail.toNat - fullM6ExtBytes →
        FullM6HdrCfgOk c → M6HdrExtInitOk ext →
        parseHeader cnfBytes = some (c.mv, c.nc, rest) →
        j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        FullM6HdrInv c (shiftDownCnf CNF.empty) ext s →
        s.core.cur_vars = c.mv → s.core.d_cur = cnf_ptr + BitVec.ofNat 64 j →
        s.core.arena_len = 0 → s.core.wlen = 1 → s.core.trail_end = 0 →
        s.core.propagated = 0 → s.core.cur_level = 0 → s.core.fuel = fuel →
        s.core.oom = 0#64 → s.core.inconsistent = 0#64 → s.core.probing = 0#64 →
        s.core.vals = List.replicate (2 * c.max_vars) 0#8 →
        s.core.wvec = List.replicate (4 * c.max_vars) 0#32 →
        (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s ⋆ R) m' → Q (c.hdr, ()) m'

theorem fullM6MemInitExactSpec_of {cnf_ptr cend work_base avail fuel : BitVec 64}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hcend : cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_base.toNat + avail.toNat < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_base avail.toNat ⋆ R) m)
    (hfail : ∀ m', (bytes cnf_ptr cnfBytes ⋆ region work_base avail.toNat ⋆ R) m' →
      (avail.toNat < fullM6HdrTotalBytes ∨
        ∀ mv nc rest, parseHeader cnfBytes = some (mv, nc, rest) →
          avail.toNat - fullM6ExtBytes < fullFixedBytes mv + nc * 40 + 136) →
      Q (0#64, ()) m')
    (hok : ∀ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (j : Nat)
      (rest : List UInt8) (m' : Mem 64),
      c.hdr = work_base + BitVec.ofNat 64 fullM6ExtBytes →
      c.avail = avail.toNat - fullM6ExtBytes →
      FullM6HdrCfgOk c → M6HdrExtInitOk ext →
      parseHeader cnfBytes = some (c.mv, c.nc, rest) →
      j ≤ cnfBytes.length → cnfBytes.drop j = rest →
      FullM6HdrInv c (shiftDownCnf CNF.empty) ext s →
      s.core.cur_vars = c.mv → s.core.d_cur = cnf_ptr + BitVec.ofNat 64 j →
      s.core.arena_len = 0 → s.core.wlen = 1 → s.core.trail_end = 0 →
      s.core.propagated = 0 → s.core.cur_level = 0 → s.core.fuel = fuel →
      s.core.oom = 0#64 → s.core.inconsistent = 0#64 → s.core.probing = 0#64 →
      s.core.vals = List.replicate (2 * c.max_vars) 0#8 →
      s.core.wvec = List.replicate (4 * c.max_vars) 0#32 →
      (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s ⋆ R) m' → Q (c.hdr, ()) m') :
    fullM6MemInitExactSpec (cnf_ptr, cend, work_base, avail, fuel, ()) m Q X :=
  ⟨cnfBytes, R, hcend, hcfit, hwfit, hm, hfail, hok⟩

theorem fullM6MemInitExactSpec_monoX
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : fullM6MemInitExactSpec xs m Q X) : fullM6MemInitExactSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, _, ⟨⟩⟩; exact h

private theorem m6_bv64_ugt_max_sub_false {p : BitVec 64} {n : Nat}
    (hfit : p.toNat + n < 2 ^ 64) :
    ((0xFFFFFFFFFFFFFFFF#64 - p).ult (BitVec.ofNat 64 n)) = false := by
  have hp := p.isLt
  have hmax : (0xFFFFFFFFFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 64 - 1 := rfl
  have hsub : 0xFFFFFFFFFFFFFFFF#64 - p = BitVec.ofNat 64 (2 ^ 64 - 1 - p.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, hmax, bv64_ofNat_toNat (by omega)]; omega
  rw [hsub, bv_ult_eq (by omega) (by omega)]
  simp only [decide_eq_false_iff_not]; omega

private theorem m6_max_sub_nat_lt_false {a b : Nat} (hfit : a + b < 2 ^ 64) :
    ¬ ((2 ^ 64 - a + (2 ^ 64 - 1)) % 2 ^ 64 < b) := by
  by_cases ha : a = 0
  · subst ha
    have heq : 2 ^ 64 - 0 + (2 ^ 64 - 1) = (2 ^ 64 - 1) + 1 * 2 ^ 64 := by omega
    rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · have heq : 2 ^ 64 - a + (2 ^ 64 - 1) = (2 ^ 64 - 1 - a) + 1 * 2 ^ 64 := by omega
    rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- Proves `Func.wp Γ full_m6_mem_init_body` against `fullM6MemInitExactSpec` from
`Full.fullInitStateSpec` and `FullM6Hdr.m6HdrInitSpec`. -/
theorem full_m6_mem_init_exact_wp (Γ : Env)
    (hInit : ∀ a m Q X, Full.fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hHdrInit : ∀ a m Q X, FullM6Hdr.m6HdrInitSpec a m Q X →
      Γ "m6_hdr_init" [i64] [] a m Q X) :
    ∀ a m Q X, fullM6MemInitExactSpec a m Q X →
      Func.wp Γ full_m6_mem_init_body a m Q X := by
  rintro ⟨cnf_ptr, cend, work_base, avail, fuel, ⟨⟩⟩ m Q X
    ⟨cnfBytes, R, rfl, hcfit, hwfit, hm, hfail, hok⟩
  unfold Func.wp full_m6_mem_init_body
  c0_hsplit
  · c0_hfast; exact hfail m hm (Or.inl (by unfold fullM6HdrTotalBytes; exact hc))
  · have hav_ge : 3456 ≤ avail.toNat := Nat.le_of_not_lt hc
    have hbw : BitVec.ofNat 64 work_base.toNat = work_base := by simp [BitVec.ofNat_toNat]
    have hbad : (0xFFFFFFFFFFFFFFFF#64 - avail).ult work_base = false := by
      rw [← hbw]; exact m6_bv64_ugt_max_sub_false (by omega)
    wp_unfold
    rw [show (18446744073709551615 : BitVec 64) = 0xFFFFFFFFFFFFFFFF#64 from rfl, hbad]
    refine ⟨(fun h => by cases h), fun _ => ?_⟩
    have hext_eq : BitVec.ofNat 64 fullM6ExtBytes = (2304 : BitVec 64) := rfl
    have hrem_ge : 1152 ≤ avail.toNat - fullM6ExtBytes := by unfold fullM6ExtBytes at *; omega
    have hsum_avail : fullM6ExtBytes + (avail.toNat - fullM6ExtBytes) = avail.toNat := by
      unfold fullM6ExtBytes; omega
    have havail_lt : avail.toNat < 2 ^ 64 := avail.isLt
    have hsplit : (bytes cnf_ptr cnfBytes ⋆
        (region work_base fullM6ExtBytes ⋆
          region (work_base + 2304) (avail.toNat - fullM6ExtBytes)) ⋆ R) m := by
      have hreg := region_split (a := work_base) (n1 := fullM6ExtBytes)
        (n2 := avail.toNat - fullM6ExtBytes) (by omega)
      rw [hsum_avail] at hreg
      rw [← hext_eq]
      simpa [hreg] using hm
    have hhdr_fit : (work_base + (2304 : BitVec 64)).toNat +
        (avail.toNat - fullM6ExtBytes) < 2 ^ 64 := by
      have : (work_base + (2304 : BitVec 64)).toNat = work_base.toNat + 2304 := by
        rw [BitVec.toNat_add, show ((2304 : BitVec 64)).toNat = 2304 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      unfold fullM6ExtBytes at *; omega
    have hav_sub : (avail - (2304 : BitVec 64)).toNat = avail.toNat - fullM6ExtBytes := by
      rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; unfold fullM6ExtBytes at *; omega)]
      rfl
    have hsplit' : (bytes cnf_ptr cnfBytes ⋆
        region (work_base + 2304) (avail - 2304).toNat ⋆
          (region work_base fullM6ExtBytes ⋆ R)) m := by
      rw [hav_sub]; rw [sep_assoc] at hsplit ⊢; exact sep_ac hsplit
    c0_hfast
    c0_call hInit
    refine ⟨cnfBytes, region work_base fullM6ExtBytes ⋆ R, rfl, hcfit,
      by rw [hav_sub]; exact hhdr_fit, by rw [hav_sub]; exact hrem_ge, hsplit', ?_, ?_⟩
    · intro m' hm' hbad
      c0_hfast
      have hm'_orig : (bytes cnf_ptr cnfBytes ⋆ region work_base avail.toNat ⋆ R) m' := by
        have hreg := region_split (a := work_base) (n1 := fullM6ExtBytes)
          (n2 := avail.toNat - fullM6ExtBytes) (by omega)
        rw [hsum_avail, hext_eq] at hreg
        have h1' : (bytes cnf_ptr cnfBytes ⋆
            (region work_base fullM6ExtBytes ⋆
              region (work_base + 2304) (avail.toNat - fullM6ExtBytes)) ⋆ R) m' := by
          rw [hav_sub] at hm'
          exact sep_ac hm'
        rw [← hreg] at h1'; exact h1'
      refine hfail m' hm'_orig (Or.inr fun mv nc rest hp => ?_)
      have hbad' := hbad mv nc rest hp; rwa [hav_sub] at hbad'
    · intro c s j rest m' hch hca hph hj hdrop hsp hcv hdcur hal hwlen hte hprop hcl
        hfu _hun hprb _hmc _hmf hoom hinc hvals hwvec _hlm _hmrk _hextl hm'
      c0_hfast
      · have hcfg : FullM6HdrCfgOk c := by
          refine M6HdrCfgOk_of_le ?_
          rw [hch, BitVec.toNat_add, show ((2304 : BitVec 64)).toNat = 2304 from rfl,
            Nat.mod_eq_of_lt (by unfold fullM6ExtBytes at *; omega)]
          omega
        have hm'_sep : (region work_base (8 * fullM6ExtWords) ⋆
            (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R)) m' := by
          simpa only [show fullM6ExtBytes = 8 * fullM6ExtWords from rfl] using sep_ac hm'
        have hm'_arr0 := sep_mono (fun _ (hr : region work_base (8 * fullM6ExtWords) _) =>
          region_to_array64 fullM6ExtWords (by decide) hr) hm'_sep
        obtain ⟨ext0, hm'_ex⟩ := sep_ex_l.mp hm'_arr0
        obtain ⟨hext0_len, hm'_pure⟩ := sep_pure_l.mp hm'_ex
        have hwb_sub : work_base = c.hdr - (2304 : BitVec 64) := by
          rw [hch]; bv_omega
        have hm'_arr : (FullM6HdrMem c ext0 s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m' := by
          rw [hwb_sub] at hm'_pure
          exact fullM6HdrMem_ext_unfocus (sep_mono_r (fun _ f => sep_ac f) hm'_pure)
        rw [← hch]
        c0_call hHdrInit
        refine m6HdrInitSpec_of (c := c) (ext := ext0) (s := s)
          hcfg (M6HdrExtOk.of_len hext0_len) hsp.lengths hm'_arr
          fun ext' m2 hinit hm2 => ?_
        c0_hfast
        exact hok c ext' s j rest m2 hch (hav_sub ▸ hca) hcfg hinit hph hj
          hdrop (FullM6HdrInv.mk_inv hcfg hinit.toOk hsp) hcv hdcur hal hwlen hte hprop hcl hfu
          hoom hinc hprb hvals hwvec (sep_ac hm2)
      · cases hc

/-! ## 2. `FullM6HdrMem` Call Bridges, Invariant Lifts, & Region Collapse -/

private theorem fullM6HdrInvW_to_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState} (h : FullM6HdrInvW c F0 F_cur ext s) :
    FullM6HdrInv c F0 ext s :=
  h.toInv

private theorem m6Hdr_call_fullBcpS15_invW {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', FullM6BcpS15.fullBcpS15Spec (c.hdr, ()) m Q' X' →
      Γ "full_propagate" [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext s' → FullTrailExt s.core s'.core →
      FullArenaPermEq s.core s'.core → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → s'.core.propagated = s'.core.trail_end ∧
        (s.core.oom = 0#64 → s'.core.oom = 0#64) ∧
        (s.core.propagated < s.core.trail_end → s'.core.fuel.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → s'.core.fuel.toNat < s.core.fuel.toNat ∧ s'.core.oom = 0#64 ∧
        FullConflictOkW F_cur s') →
      (r = 2#64 → s'.core.oom ≠ 0#64 ∨ s'.core.fuel = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_propagate" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hinv.sparseW
  refine hΓ _ X ⟨c, F0, F_cur, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp.1, hsp.2.1,
    hsp.2.2.2.2.2, (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' s'
    hlen' hw' htr' hperm' _ hfu' hdom hr0 hr1 hr2 hno hm'
  have hnd' : FullArenaVarsNodup s' := by
    intro r' hr' hgb'
    have hr0' : r' ∈ fullArenaClauseRefs s := by
      change r' ∈ fullArenaClauseRefsCore s'.core at hr'
      change r' ∈ fullArenaClauseRefsCore s.core
      rwa [← hperm'.2.1]
    have hp := hperm'.2.2 r' hr0'
    have hgb0 : fullArenaClauseGarb s r' = false := by
      change fullArenaClauseGarbCore s.core r' = false
      change fullArenaClauseGarbCore s'.core r' = false at hgb'
      rwa [← hp.2.1]
    exact (hp.2.2.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 r' hr0' hgb0)
  have hll' : FullLastLearnedWf s' :=
    hsp.2.2.2.2.1.1.of_refs_subset rfl fun r' hr' => by
      change r' ∈ fullArenaClauseRefsCore s.core at hr'
      change r' ∈ fullArenaClauseRefsCore s'.core
      rwa [hperm'.2.1]
  have hinv' : FullM6HdrInvW c F0 F_cur ext s' :=
    FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
      ⟨hlen', hw', hsp.2.2.1, hnd', ⟨hll', hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩
  exact hk r s' m' hinv' htr' hperm' hfu' hdom hr0 hr1 hr2 hno
    ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem m6Hdr_call_m6Analyze_invW {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', FullM6Hdr.m6HdrAnalyzeSpec (c.hdr, ()) m Q' X' →
      Γ "full_analyze_m6_hdr" [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hcok : FullConflictOkW F_cur s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInvW c F0 F_cur ext' s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_analyze_m6_hdr" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  exact hΓ _ X (m6HdrAnalyzeSpec_of hinv hcok hm
    fun r ext' s' m' hext' hlen' hr _ hfu _ hu _ h1 hm' =>
      hk r ext' s' m' hext' hlen' hr hfu hu h1 hm')

private theorem m6Hdr_call_m6Reduce_invW {Γ : Env} {force : Bool} {ret : List Ty}
    {args : Tup (Arg Val) [i64, .bool]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, force, ()))
    (hΓ : ∀ Q' X', m6ReduceSpec (c.hdr, force, ()) m Q' X' →
      Γ "full_reduce_m6" [i64, .bool] [i64] (c.hdr, force, ()) m Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext' s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_reduce_m6" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  exact hΓ _ X (m6ReduceSpec_of hinv hm fun r ext' s' m' hinv' hr _ hfu _ _ _ _ hu _ _ hm' =>
    hk r ext' s' m' hinv' hr hfu hu hm')

private theorem m6Hdr_call_m6SwitchMode_inv {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', m6SwitchModeSpec (c.hdr, ()) m Q' X' →
      Γ "full_switch_mode_m6" [i64] [] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext' s' → s'.core = s.core → FullProbeScratchPres s s' →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_switch_mode_m6" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hΓ _ X (m6SwitchModeSpec_of hinv.cfgOk hinv.extOk hinv.sparse.lengths hm
    fun ext' s' m' hcore hlen hpr hext _ hm' => ?_)
  have hinv' : FullM6HdrInv c F0 ext' s' :=
    fullM6HdrInv_of_core_eq (fullM6HdrInv_with_ext hinv hext) hlen hcore hpr.1
  exact hk ext' s' m' hinv' hcore hpr hm'

private theorem m6Hdr_call_fullRestartDue_inv_exact {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', Full.fullRestartDueSpec (c.hdr, ()) m Q' X' →
      Γ "full_restart_due" [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core = s.core →
      (r = 0#64 ∨ r = 1#64) → (FullM6HdrMem c ext s' ⋆ R) m' →
      wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_restart_due" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hΓ _ X ⟨c, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hinv.sparse.lengths,
    (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  rintro ⟨r, ⟨⟩⟩ s' m' hcore hlen ⟨hdom, hpres⟩ hm'
  have hceq : s'.core = s.core := @Full.fullCoreState_agrees_with_scratch c s s' hcore
  have hinv' : FullM6HdrInv c F0 ext s' :=
    fullM6HdrInv_of_core_eq hinv hlen hceq hpres
  exact hk r s' m' hinv' hceq hdom ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem m6Hdr_call_fullRestart_inv {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', Full.fullRestartSpec (c.hdr, ()) m Q' X' →
      Γ "full_restart" [i64] [] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core.cur_level ≤ s.core.cur_level →
      s'.core.fuel = s.core.fuel → FullExtScratchPres s s' →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_restart" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hinv.sparse
  have hcore := fullM6HdrInv_to_coreInv hinv
  refine hΓ _ X ⟨c, F0, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hcore.coreInv,
    (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' s' hc' hcl' hpres' hm'
  have hlm' : FullLitMarksClear c s' := ⟨hsp.2.1.1, hsp.2.1.2⟩
  have hvn' : FullArenaVarsNodup s' := hsp.2.2.1
  have hwf' : FullLastLearnedWf s' :=
    hsp.2.2.2.1.1.of_refs_subset hpres'.1 fun _ hr => hr
  have hext_sc' : FullExtScratchOk c s' :=
    ⟨hwf', by change sc'.extend_len ≤ c.extend_cap; rw [hpres'.2]; exact hsp.2.2.2.1.2⟩
  have hinv' : FullM6HdrInv c F0 ext s' :=
    FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk ⟨hc', hlm', hvn', hext_sc', hsp.2.2.2.2⟩
  exact hk s' m' hinv' hcl' rfl hpres' ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem m6Hdr_call_m4Reorder_inv {Γ : Env} {budget : BitVec 64} {ret : List Ty}
    {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, budget, ()))
    (hΓ : ∀ Q' X', FullM4.m4ReorderSpec (c.hdr, budget, ()) m Q' X' →
      Γ "full_reorder_m6" [i64, i64] [i64] (c.hdr, budget, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core.fuel = s.core.fuel →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_reorder_m6" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hΓ _ X ⟨c, F0, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hinv.sparse,
    (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro r s' m' hsp' _ _ hfu' hm'
  exact hk r s' m' (FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk hsp') hfu'
    ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem m6Hdr_call_m6Rephase_inv {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', m6aRephaseSpec (c.hdr, ()) m Q' X' →
      Γ "full_rephase_m6_hdr" [i64] [] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext' s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_rephase_m6_hdr" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hinv.sparse
  have hcore := fullM6HdrInv_to_coreInv hinv
  refine hΓ _ X (m6aRephaseSpec_of hinv.cfgOk hinv.extOk hcore.coreInv hm ?_)
  intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' fuel' sc' ext' m' s'
    ⟨hext', _⟩ hc' _ _ hfu' hpres' hm'
  have hlm' : FullLitMarksClear c s' := ⟨hsp.2.1.1, hsp.2.1.2⟩
  have hvn' : FullArenaVarsNodup s' := hsp.2.2.1
  have hwf' : FullLastLearnedWf s' :=
    hsp.2.2.2.1.1.of_refs_subset hpres'.1 fun _ hr => hr
  have hext_sc' : FullExtScratchOk c s' :=
    ⟨hwf', by change sc'.extend_len ≤ c.extend_cap; rw [hpres'.2]; exact hsp.2.2.2.1.2⟩
  have hinv' : FullM6HdrInv c F0 ext' s' :=
    FullM6HdrInv.mk_inv hinv.cfgOk hext' ⟨hc', hlm', hvn', hext_sc', hsp.2.2.2.2⟩
  exact hk ext' s' m' hinv' hfu' hm'

private theorem m6Hdr_call_m6Simplify_inv {Γ : Env} {dp de : Bool} {ret : List Ty}
    {args : Tup (Arg Val) [i64, .bool, .bool]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, dp, de, ()))
    (hΓ : ∀ Q' X', fullM6SimplifySpec (c.hdr, dp, de, ()) m Q' X' →
      Γ "full_simplify_m6" [i64, .bool, .bool] [i64] (c.hdr, dp, de, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (c' : FullCfg) (ext' : List (BitVec 64)) (s' : FullState)
      (m' : Mem 64),
      FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_simplify_m6" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  exact hΓ _ X (fullM6SimplifySpec_of hinv hm hk)

private theorem m6Hdr_call_m6Decide_inv {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', FullM6Hdr.m6HdrDecideSpec (c.hdr, ()) m Q' X' →
      Γ "m6_hdr_decide" [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext' s' → (r = 0#64 ∨ r = 1#64) →
      s'.core.fuel = s.core.fuel →
      (r = 0#64 → s'.core.cur_level = s.core.cur_level ∧ s'.core.trail_end = s.core.trail_end) →
      (r = 1#64 → s'.core.cur_level = s.core.cur_level + 1 ∧
        s'.core.trail_end = s.core.trail_end + 1) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "m6_hdr_decide" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hinv.sparse
  have hcore := fullM6HdrInv_to_coreInv hinv
  refine hΓ _ X (FullM6Hdr.m6HdrDecideSpec_of hcore hm ?_)
  intro r vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' ext' m' s'
    hcore' hpres' hdom h0 h1 hm'
  have hlm' : FullLitMarksClear c s' := ⟨hsp.2.1.1, hsp.2.1.2⟩
  have hvn' : FullArenaVarsNodup s' := hsp.2.2.1
  have hwf' : FullLastLearnedWf s' :=
    hsp.2.2.2.1.1.of_refs_subset hpres'.1 fun _ hr => hr
  have hext_sc' : FullExtScratchOk c s' :=
    ⟨hwf', by change sc'.extend_len ≤ c.extend_cap; rw [hpres'.2]; exact hsp.2.2.2.1.2⟩
  have hinv' : FullM6HdrInv c F0 ext' s' :=
    FullM6HdrInv.mk_inv hcore'.cfgOk hcore'.extOk
      ⟨hcore'.coreInv, hlm', hvn', hext_sc', hsp.2.2.2.2⟩
  exact hk r ext' s' m' hinv' hdom rfl h0 (fun hr1 => ⟨(h1 hr1).1, (h1 hr1).2.1⟩) hm'

/-- Collapses `SatCheckRest` (with `bva_cap` updated at index 94) + `array64 (c.hdr - 2304) ext`
+ leading alignment padding back into `region work_ptr wlen`. -/
private theorem m6_satCheckModel_post_to_m6_region {work_ptr : BitVec 64} {wlen : Nat}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {bva_bv mv' nc' cur' val' cnf_ptr : BitVec 64} {cnfBytes : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hw_ge : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hch : c.hdr = fullM6WorkHdr work_ptr)
    (hca : c.avail = wlen - fullAlignPad work_ptr - fullM6ExtBytes)
    (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (bytes cnf_ptr cnfBytes ⋆ dimacsState c.hdr mv' nc' cur' val' ⋆
      bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
      (array64 (c.hdr + 32) ((Full.hdrTailWords c s).set 94 bva_bv) ⋆
        array (t := i8) c.pLitMark s.core.lit_mark ⋆
        array (t := i8) c.pMark s.core.mrk ⋆
        FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
        FullScratchArrays c s.scratch ⋆ c.pad ⋆ array64 (c.hdr - 2304) ext ⋆
        region work_ptr (fullAlignPad work_ptr) ⋆ R)) m) :
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m := by
  have hmx := c.hmaxv; have ha := c.harena; have hw := c.hwcap
  have hd := c.hdel; have hred := c.hred; have he := c.hext; have hscr := c.hscr
  have hmd := fullMinDepthOf_le c.max_vars
  unfold dimacsBound FullScratchArrays FullScrByteArrs FullScrU32A FullScrWksArrs
    FullScrMetaArrs FullScrDynArrs FullCoreU32A FullCoreU32B FullCoreDynArrs at *
  have hc := hlen.core_ok; have hs := hlen.scratch_ok
  have f8 : ∀ {a : BitVec 64} {xs : List (Val i8)} {n : Nat}, xs.length = n → n ≤ 2 ^ 64 →
      ∀ f, array (t := i8) a xs f → region a n f := fun {a xs n} hn hbd f hf => by
    simpa [Ty.bytes, Ty.size, i8, hn] using
      array_to_region (t := i8) (by simp [Ty.bytes, Ty.size, i8, hn, hbd]) hf
  have f32 : ∀ {a : BitVec 64} {xs : List (Val i32)} {n m0 : Nat}, xs.length = n → 4 * n = m0 →
      m0 ≤ 2 ^ 64 → ∀ f, array (t := i32) a xs f → region a m0 f :=
    fun {a xs n m0} hn hm0 hbd f hf => by
      simpa [Ty.bytes, Ty.size, i32, hn, hm0] using
        array_to_region (t := i32) (by simp [Ty.bytes, Ty.size, i32, hn]; omega) hf
  have f64 : ∀ {a : BitVec 64} {xs : List (BitVec 64)} {n m0 : Nat}, xs.length = n →
      8 * n = m0 → m0 ≤ 2 ^ 64 → ∀ f, array64 a xs f → region a m0 f :=
    fun {a xs n m0} hn hm0 hbd f hf => by
      simpa [Ty.bytes, Ty.size, i64, hn, hm0] using
        array_to_region (t := i64) (a := a) (xs := xs) (by simp [Ty.bytes, Ty.size, i64]; omega)
          ((array64_eq_array a xs) ▸ hf)
  have hm_ac : (((bytes cnf_ptr cnfBytes ⋆ R) ⋆
      (array64 (c.hdr - 2304) ext ⋆ region work_ptr (fullAlignPad work_ptr))) ⋆
      ((dimacsState c.hdr mv' nc' cur' val' ⋆
        array64 (c.hdr + 32) ((Full.hdrTailWords c s).set 94 bva_bv)) ⋆
      ((bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
        (array (t := i8) c.pWalkVals s.scratch.walk_vals ⋆
          (array (t := i8) c.pLitMark s.core.lit_mark ⋆
          (array (t := i8) c.pMark s.core.mrk ⋆
            (array (t := i8) c.pPhases s.scratch.phases ⋆
              (array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
                (array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
                  array (t := i8) c.pWalkBest s.scratch.walk_best))))))) ⋆
      ((array (t := i32) c.pFlags s.core.flags ⋆
        (array (t := i32) c.pLevel s.core.lvl ⋆
          (array (t := i32) c.pReason s.core.rsns ⋆
            (array (t := i32) c.pTrail s.core.trl ⋆
              array (t := i32) c.pTrailPos s.core.trail_pos)))) ⋆
      ((array (t := i32) c.pTmp s.core.tmp ⋆
        (array (t := i32) c.pHeap s.scratch.heap ⋆
          (array (t := i32) c.pPos s.scratch.pos ⋆
            (array (t := i32) c.pMinClr s.core.min_clr ⋆
              array (t := i32) c.pShrinkStk s.scratch.shrink_stk)))) ⋆
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        (array (t := i32) c.pQNext s.scratch.q_next ⋆
          (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
            (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
              array (t := i32) c.pFrameDec s.core.frame_dec)))) ⋆
      ((array (t := i32) c.pWvec s.core.wvec ⋆
        (array (t := i32) c.pRepr s.core.repr ⋆
          (array (t := i32) c.pWsort s.scratch.wsort ⋆
            (array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
              (array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
                (array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
                  (array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
                    (array64 c.pScore s.scratch.score ⋆
                      array64 c.pSimSig s.scratch.sim_sig)))))))) ⋆
      ((array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
          (array (t := i32) c.pLastLearned s.scratch.last_learned ⋆
            (array (t := i32) c.pArena s.core.arena ⋆
              (array (t := i32) c.pWstk s.core.wstk ⋆
                (array (t := i32) c.pDelayed s.scratch.delayed ⋆
                  (array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
                    (array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
                      array (t := i32) c.pScratchBuf s.scratch.scratch_buf)))))))) ⋆
      c.pad)))))))) m := sep_ac hm
  have h1 : (((bytes cnf_ptr cnfBytes ⋆ R) ⋆
      (array64 (c.hdr - 2304) ext ⋆ region work_ptr (fullAlignPad work_ptr))) ⋆
      ((region c.hdr 32 ⋆ region (c.hdr + 32#64) 1120) ⋆
      ((region c.pVals (2 * c.max_vars) ⋆
        (region c.pWalkVals (2 * c.max_vars) ⋆
          (region c.pLitMark (2 * c.max_vars) ⋆
          (region c.pMark c.max_vars ⋆
            (region c.pPhases c.max_vars ⋆
              (region c.pPhasesTarget c.max_vars ⋆
                (region c.pPhasesBest c.max_vars ⋆
                  region c.pWalkBest c.max_vars))))))) ⋆
      ((region c.pFlags (4 * c.max_vars) ⋆
        (region c.pLevel (4 * c.max_vars) ⋆
          (region c.pReason (4 * c.max_vars) ⋆
            (region c.pTrail (4 * c.max_vars) ⋆
              region c.pTrailPos (4 * c.max_vars))))) ⋆
      ((region c.pTmp (4 * c.max_vars) ⋆
        (region c.pHeap (4 * c.max_vars) ⋆
          (region c.pPos (4 * c.max_vars) ⋆
            (region c.pMinClr (4 * c.max_vars) ⋆
              region c.pShrinkStk (4 * c.max_vars))))) ⋆
      ((region c.pQPrev (4 * c.max_vars) ⋆
        (region c.pQNext (4 * c.max_vars) ⋆
          (region c.pQStamp (4 * c.max_vars) ⋆
            (region c.pFrameTrail (4 * (c.max_vars + 1)) ⋆
              region c.pFrameDec (4 * (c.max_vars + 1)))))) ⋆
      ((region c.pWvec (16 * c.max_vars) ⋆
        (region c.pRepr (8 * c.max_vars) ⋆
          (region c.pWsort (8 * c.max_vars) ⋆
            (region c.pWorkStk1 (8 * c.max_vars) ⋆
              (region c.pWorkStk2 (8 * c.max_vars) ⋆
                (region c.pTarjanMark (8 * c.max_vars) ⋆
                  (region c.pTarjanReach (8 * c.max_vars) ⋆
                    (region c.pScore (8 * c.max_vars) ⋆
                      region c.pSimSig (8 * c.max_vars))))))))) ⋆
      ((region c.pMinStk (8 * c.minDepth) ⋆
        (region c.pGlueUsed 256 ⋆
          (region c.pLastLearned 64 ⋆
            (region c.pArena (4 * c.arena_cap) ⋆
              (region c.pWstk (4 * c.wcap) ⋆
                (region c.pDelayed (12 * c.delayed_cap) ⋆
                  (region c.pRedRefs (4 * c.red_cap) ⋆
                    (region c.pExtendStk (4 * c.extend_cap) ⋆
                      region c.pScratchBuf (4 * c.scratch_cap))))))))) ⋆
      c.pad)))))))) m := by
    refine sep_mono_r (sep_mono2 ?_ ?_) hm_ac
    · exact sep_mono2 (fun _ h => dimacsState_to_region h)
        (f64 (by rw [List.length_set, Full.hdrTailWords_length]) rfl (by decide))
    · refine sep_mono2 ?_ (sep_mono2 ?_ (sep_mono2 ?_ (sep_mono2 ?_ (sep_mono2 ?_ (sep_mono2 ?_
        (fun _ hb => hb))))))
      · exact sep_mono2 (fun _ hb => by
            have hb' := bytes_to_region hb; simpa [hc.vals_len] using hb')
          (sep_mono2 (f8 hs.walk_vals_len (by omega))
            (sep_mono2 (f8 hc.lit_mark_len (by omega))
              (sep_mono2 (f8 hc.mrk_len (by omega))
                (sep_mono2 (f8 hs.phases_len (by omega))
                  (sep_mono2 (f8 hs.phases_target_len (by omega))
                    (sep_mono2 (f8 hs.phases_best_len (by omega))
                      (f8 hs.walk_best_len (by omega))))))))
      · exact sep_mono2 (f32 hc.flags_len rfl (by omega))
          (sep_mono2 (f32 hc.lvl_len rfl (by omega))
            (sep_mono2 (f32 hc.rsns_len rfl (by omega))
              (sep_mono2 (f32 hc.trl_len rfl (by omega))
                (f32 hc.trail_pos_len rfl (by omega)))))
      · exact sep_mono2 (f32 hc.tmp_len_arr rfl (by omega))
          (sep_mono2 (f32 hs.heap_len_arr rfl (by omega))
            (sep_mono2 (f32 hs.pos_len rfl (by omega))
              (sep_mono2 (f32 hc.min_clr_len_arr rfl (by omega))
                (f32 hs.shrink_stk_len rfl (by omega)))))
      · exact sep_mono2 (f32 hs.q_prev_len rfl (by omega))
          (sep_mono2 (f32 hs.q_next_len rfl (by omega))
            (sep_mono2 (f32 hs.q_stamp_len rfl (by omega))
              (sep_mono2 (f32 hc.frame_trail_len rfl (by omega))
                (f32 hc.frame_dec_len rfl (by omega)))))
      · exact sep_mono2 (f32 hc.wvec_len (by omega) (by omega))
          (sep_mono2 (f32 hc.repr_len (by omega) (by omega))
            (sep_mono2 (f32 hs.wsort_len (by omega) (by omega))
              (sep_mono2 (f32 hs.work_stk1_len (by omega) (by omega))
                (sep_mono2 (f32 hs.work_stk2_len (by omega) (by omega))
                  (sep_mono2 (f32 hs.tarjan_mark_len (by omega) (by omega))
                    (sep_mono2 (f32 hs.tarjan_reach_len (by omega) (by omega))
                      (sep_mono2 (f64 hs.score_len rfl (by omega))
                        (f64 hs.sim_sig_len rfl (by omega)))))))))
      · exact sep_mono2 (f32 hc.min_stk_len (by unfold FullCfg.minDepth; omega)
          (by unfold FullCfg.minDepth; omega))
          (sep_mono2 (f32 hs.glue_used_len (by decide) (by decide))
            (sep_mono2 (f32 hs.last_learned_len (by decide) (by decide))
              (sep_mono2 (f32 hc.arena_len_arr rfl (by omega))
                (sep_mono2 (f32 hc.wstk_len_arr rfl (by omega))
                  (sep_mono2 (f32 hs.delayed_len_arr (by omega) (by omega))
                    (sep_mono2 (f32 hs.red_refs_len rfl (by omega))
                      (sep_mono2 (f32 hs.extend_stk_len rfl (by omega))
                        (f32 hs.scratch_buf_len rfl (by omega)))))))))
  have h2 : (((bytes cnf_ptr cnfBytes ⋆ R) ⋆
      (array64 (c.hdr - 2304) ext ⋆ region work_ptr (fullAlignPad work_ptr))) ⋆
      region c.hdr c.avail) m :=
    sep_mono_r (fun _ h => c.regions_to_avail (sep_ac h)) h1
  have hext_reg : ∀ f, array64 (c.hdr - 2304) ext f →
      region (fullM6WorkBase work_ptr) fullM6ExtBytes f := by
    intro f hf
    have hwb_eq : c.hdr - 2304 = fullM6WorkBase work_ptr := by
      rw [hch]; unfold fullM6WorkHdr fullM6WorkBase fullM6ExtBytes; bv_omega
    rw [hwb_eq] at hf
    exact f64 hext.len rfl (by decide) f hf
  have hm_wb : ((bytes cnf_ptr cnfBytes ⋆ R) ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆
        (region (fullM6WorkBase work_ptr) fullM6ExtBytes ⋆ region c.hdr c.avail))) m := by
    have hm_a : ((bytes cnf_ptr cnfBytes ⋆ R) ⋆
        (region work_ptr (fullAlignPad work_ptr) ⋆
          (array64 (c.hdr - 2304) ext ⋆ region c.hdr c.avail))) m := sep_ac h2
    exact sep_mono_r (fun _ h => sep_mono_r (fun _ h' => sep_mono hext_reg h') h) hm_a
  have h_wb_avail : region (fullM6WorkBase work_ptr) fullM6ExtBytes ⋆ region c.hdr c.avail =
      region (fullM6WorkBase work_ptr) (wlen - fullAlignPad work_ptr) := by
    have hhdr_eq : fullM6WorkBase work_ptr + BitVec.ofNat 64 fullM6ExtBytes = c.hdr := by
      rw [hch]; unfold fullM6WorkHdr fullM6WorkBase fullM6ExtBytes; bv_omega
    have heq_sz : fullM6ExtBytes + c.avail = wlen - fullAlignPad work_ptr := by
      rw [hca]; unfold fullM6HdrTotalBytes at hw_ge; unfold fullM6ExtBytes at ⊢; omega
    have hfit_sub : wlen - fullAlignPad work_ptr ≤ 2 ^ 64 := by omega
    rw [← hhdr_eq]
    exact region_merge_eq heq_sz hfit_sub
  have hm_wb2 : ((bytes cnf_ptr cnfBytes ⋆ R) ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆
        region (fullM6WorkBase work_ptr) (wlen - fullAlignPad work_ptr))) m := by
    rw [← h_wb_avail]; exact hm_wb
  have h_all : region work_ptr (fullAlignPad work_ptr) ⋆
      region (fullM6WorkBase work_ptr) (wlen - fullAlignPad work_ptr) = region work_ptr wlen := by
    have hpad_eq : work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) = fullM6WorkBase work_ptr :=
      rfl
    have heq_sz : fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr) = wlen := by
      unfold fullM6HdrTotalBytes at hw_ge; omega
    rw [← hpad_eq]
    exact region_merge_eq heq_sz (by omega)
  rw [h_all] at hm_wb2
  exact sep_ac hm_wb2

private theorem m6_cnf_sat_congr {a b : Nat → Bool} {cnf : CNF Nat}
    (hs : cnf.Sat a) (h : ∀ cl ∈ cnf, ∀ l ∈ cl.literals, a l.1 = b l.1) : cnf.Sat b := by
  rw [CNF.sat_iff_all_mem_sat] at hs ⊢
  intro cl hcl
  have hc := hs cl hcl
  rw [CNF.Clause.sat_iff_exists_mem_eq] at hc ⊢
  rcases hc with ⟨l, hl, heq⟩
  have hlit : l ∈ cl.literals := CNF.Clause.mem_literals_iff.mpr hl
  exact ⟨l, hl, by rw [← h cl hcl l hlit]; exact heq⟩

/-- Certifies `cnf.Sat (readModelFromWorkM6 M work_ptr)` after `kissat_check_model` returns `1#64`
under post-compaction `h->d.mv = c0.mv` and updated `h->bva_cap` (word `94 ≠ 4 = pVals`). -/
private theorem sat_of_checkModel_post_m6_bva
    {work_ptr : BitVec 64} {c0 c2 : FullCfg} {s : FullState}
    {bva_bv : BitVec 64} {cnfBytes : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hch : c2.hdr = fullM6WorkHdr work_ptr)
    (hcomp : FullCfgCompat c0 c2)
    (hlen : s.LengthsOk c2)
    (hm : (array64 (c2.hdr + 32) ((Full.hdrTailWords c2 s).set 94 bva_bv) ⋆
      bytes c2.pVals (s.core.vals.map UInt8.ofBitVec) ⋆ R) m)
    (hrun : runKissatCheckModel cnfBytes (s.core.vals.map UInt8.ofBitVec) c0.mv = true) :
    ∃ cnf, parseDimacs cnfBytes = some cnf ∧
      ∀ (F : Mem 64 → Prop) (M : Mem 64),
        (Eq m ⋆ F) M → cnf.Sat (readModelFromWorkM6 M work_ptr) := by
  have hmv_le : c0.mv ≤ c2.max_vars := by
    have h0 := c0.hbva; have heq := hcomp.max_vars; omega
  have hmx := c2.hmaxv; unfold dimacsBound at hmx
  have hvals_len : 2 * c0.mv ≤ (s.core.vals.map UInt8.ofBitVec).length := by
    rw [List.length_map, hlen.core_ok.vals_len]; omega
  obtain ⟨cnf, mv, hp, hmv_le_mv, hvars, hsat0⟩ := runKissatCheckModel_sat_exact hrun
  refine ⟨cnf, hp, fun F M hM => ?_⟩
  have hget4 : ((Full.hdrTailWords c2 s).set 94 bva_bv)[4]? = some c2.pVals := rfl
  have h4lt : 4 < ((Full.hdrTailWords c2 s).set 94 bva_bv).length := by
    rw [List.length_set, Full.hdrTailWords_length]; decide
  have hm1 : (array64 (c2.hdr + 32) ((Full.hdrTailWords c2 s).set 94 bva_bv) ⋆
      (bytes c2.pVals (s.core.vals.map UInt8.ofBitVec) ⋆ R)) m := sep_ac hm
  have hvptr_hdr : loadVal m i64 (c2.hdr + 32 + BitVec.ofNat 64 (8 * 4)) =
      some (((Full.hdrTailWords c2 s).set 94 bva_bv)[4]) :=
    loadVal_array64 h4lt hm1
  have h4val : ((Full.hdrTailWords c2 s).set 94 bva_bv)[4] = c2.pVals := by
    have := List.getElem?_eq_getElem h4lt
    rw [hget4] at this; exact (Option.some.inj this).symm
  have hvptr_addr : work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) + 2368#64 =
      c2.hdr + 32 + BitVec.ofNat 64 (8 * 4) := by
    rw [hch]; unfold fullM6WorkHdr fullM6WorkBase fullM6ExtBytes; bv_omega
  have hvptr : loadVal m i64 (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) + 2368#64) =
      some c2.pVals := by
    rw [hvptr_addr, ← h4val]; exact hvptr_hdr
  refine m6_cnf_sat_congr hsat0 fun cl hcl lit hlit => ?_
  have ⟨hv1, hv2⟩ := hvars cl hcl lit hlit
  have hvne : (lit.1 == 0) = false := by
    cases h : (lit.1 == 0)
    · rfl
    · simp at h; omega
  have hidx : 2 * (lit.1 - 1) < (s.core.vals.map UInt8.ofBitVec).length := by
    rw [List.length_map, hlen.core_ok.vals_len]
    have := Nat.le_trans hv2 hmv_le_mv
    omega
  have hbd : (s.core.vals.map UInt8.ofBitVec).length ≤ 2 ^ 64 := by
    rw [List.length_map, hlen.core_ok.vals_len]; omega
  have hm2 : (bytes c2.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
      (array64 (c2.hdr + 32) ((Full.hdrTailWords c2 s).set 94 bva_bv) ⋆ R)) m := sep_ac hm
  have hbm : loadVal m i8 (c2.pVals + BitVec.ofNat 64 (2 * (lit.1 - 1))) =
      some (BitVec.ofNat 8 (s.core.vals.map UInt8.ofBitVec)[2 * (lit.1 - 1)].toNat) :=
    load_bytes_at hidx hbd hm2
  have hrm := readModelFromWorkM6_frame hM hvptr hbm
  rw [hrm, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
  simp only [hvne, Bool.false_eq_true, ↓reduceIte, Option.getD_some]
  congr 2
  apply UInt8.eq_of_toBitVec_eq
  simp

private theorem m6_parseClauses_vars_pos {mv : Nat} :
    ∀ {n : Nat} {acc : CNF Nat} {bs : List UInt8} {cnf : CNF Nat},
      CnfVarsPos acc → parseClauses mv n acc bs = some cnf → CnfVarsPos cnf
  | 0, acc, bs, cnf, hacc, h => by
    unfold parseClauses at h
    cases hsw : skipWsComments bs with
    | nil => rw [hsw] at h; cases Option.some.inj h; exact hacc
    | cons _ _ => rw [hsw] at h; cases h
  | n + 1, acc, bs, cnf, hacc, h => by
    unfold parseClauses at h
    cases hpc : parseClause mv bs with
    | none => rw [hpc] at h; cases h
    | some p =>
      rcases p with ⟨cl, rest⟩
      rw [hpc] at h
      exact m6_parseClauses_vars_pos
        (cnfVarsPos_add hacc (parseClauseAux_vars_pos (by simp) hpc)) h

private theorem m6_parseDimacs_vars_pos {bs : List UInt8} {cnf : CNF Nat}
    (h : parseDimacs bs = some cnf) : CnfVarsPos cnf := by
  unfold parseDimacs at h
  cases hh : parseHeader bs with
  | none => rw [hh] at h; cases h
  | some p =>
    rcases p with ⟨mv, nc, rest⟩
    rw [hh] at h
    exact m6_parseClauses_vars_pos (by intro _ hc; simp at hc) h

private theorem m6_alignPad_bv_eq (p : BitVec 64) :
    (8#64 - (p &&& 7#64)) &&& 7#64 = BitVec.ofNat 64 (fullAlignPad p) := by
  apply BitVec.eq_of_toNat_eq
  rw [fullAlignPad_eq, bv64_ofNat_toNat (by have := fullAlignPad_lt8 p; omega)]

private theorem m6_alignPad_bv_ofNat_eq (p : BitVec 64) :
    ((8 : BitVec 64) - (p &&& 7)) &&& 7 = BitVec.ofNat 64 (fullAlignPad p) :=
  m6_alignPad_bv_eq p

private theorem m6_alignPad_bv_comm_eq (p : BitVec 64) :
    (7 : BitVec 64) &&& (8 - (p &&& 7)) = BitVec.ofNat 64 (fullAlignPad p) := by
  rw [BitVec.and_comm]; exact m6_alignPad_bv_eq p

private theorem m6_bytes_hdrMem_to_region {cnf_ptr work_ptr : BitVec 64}
    {cnfBytes : List UInt8} {wlen : Nat} {c : FullCfg} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hle : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen) (hfit : wlen ≤ 2 ^ 64)
    (hhdr : c.hdr = fullM6WorkHdr work_ptr)
    (hav : c.avail = wlen - fullAlignPad work_ptr - fullM6ExtBytes)
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s ⋆
      region work_ptr (fullAlignPad work_ptr) ⋆ R) m) :
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m := by
  have h1 : ((region work_ptr (fullAlignPad work_ptr) ⋆ FullM6HdrMem c ext s) ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m :=
    sep_ac hm
  have h2 : (region work_ptr wlen ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m :=
    sep_mono (fun _ g =>
      region_work_from_m6_hdrMem hle hfit hhdr hav hcfg hext hlen g) h1
  exact sep_ac h2

/-! ## 3. `full_search_m6_wp` (`fullM6SearchSpec`) & `full_search_wp` -/

/-- Well-founded termination measure for `full_search_m6`: lexicographic on
`(fuel, c.max_vars - trail_end)`. Note `c.max_vars` is invariant under `FullCfgCompat`. -/
def m6SearchVariant (c : FullCfg) (s : FullState) : Nat :=
  (c.max_vars + 1) * s.core.fuel.toNat + (c.max_vars - s.core.trail_end)

/-- Parametric `Func.wp` proof for `full_search_m6` against `fullM6SearchSpec` (`0` model proofs,
using `FullM6BcpS15.fullBcpS15Spec`, `FullM6Hdr.m6HdrAnalyzeSpec`, `FullM6Hdr.m6HdrDecideSpec`,
`m6ReduceSpec`, `m6SwitchModeSpec`, `FullM4.m4ReorderSpec`, `m6aRephaseSpec`,
`fullM6SimplifySpec`, `Full.fullRestartDueSpec`, `Full.fullRestartSpec`). -/
theorem full_search_m6_wp (Γ : Env)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hAnalyze : ∀ a m Q X, FullM6Hdr.m6HdrAnalyzeSpec a m Q X →
      Γ "full_analyze_m6_hdr" [i64] [i64] a m Q X)
    (hReduce : ∀ a m Q X, m6ReduceSpec a m Q X →
      Γ "full_reduce_m6" [i64, .bool] [i64] a m Q X)
    (hSwitch : ∀ a m Q X, m6SwitchModeSpec a m Q X →
      Γ "full_switch_mode_m6" [i64] [] a m Q X)
    (hRstDue : ∀ a m Q X, Full.fullRestartDueSpec a m Q X →
      Γ "full_restart_due" [i64] [i64] a m Q X)
    (hRst : ∀ a m Q X, Full.fullRestartSpec a m Q X →
      Γ "full_restart" [i64] [] a m Q X)
    (hReorder : ∀ a m Q X, FullM4.m4ReorderSpec a m Q X →
      Γ "full_reorder_m6" [i64, i64] [i64] a m Q X)
    (hRephase : ∀ a m Q X, m6aRephaseSpec a m Q X →
      Γ "full_rephase_m6_hdr" [i64] [] a m Q X)
    (hSimplify : ∀ a m Q X, fullM6SimplifySpec a m Q X →
      Γ "full_simplify_m6" [i64, .bool, .bool] [i64] a m Q X)
    (hDecide : ∀ a m Q X, FullM6Hdr.m6HdrDecideSpec a m Q X →
      Γ "m6_hdr_decide" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullM6SearchSpec a m Q X → Func.wp Γ full_search_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases fullM6SearchSpec_elim hs with ⟨c0, F0, ext0, s0, R, rfl, hinv0, _, hm0, hQ⟩
  unfold Func.wp full_search_m6_body
  c0_hsteps_nogrp
  refine wp_while_state1 (α := BitVec 64 × FullCfg × List (BitVec 64) × FullState) Prod.fst
    (fun ⟨_, c, _, s⟩ => m6SearchVariant c s)
    (fun ⟨_, c, ext, s⟩ ml =>
      FullCfgCompat c0 c ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) ml)
    (fun J hJ => by
      c0_hsteps
      exact hJ (10000#64, c0, ext0, s0) m ⟨FullCfgCompat.refl c0, hinv0, hm0⟩)
    ?_
  rintro J ⟨rlim, c, ext, s⟩ ml ⟨hcompat, hinv, hml⟩ ih
  rw [← hcompat.hdr]
  have hsp := hinv.sparse
  have hlen := hsp.lengths
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hml_f := fullM6HdrMem_focus hml
  c0_hsplit
  rotate_left; · cases hc
  c0_hsteps
  · -- `h->oom != 0ULL`
    exact hQ 0#64 c ext s ml hcompat hlen hinv.cfgOk hinv.extOk (Or.inl rfl)
      (fun hc => absurd hc (by decide)) (fun hc => absurd hc (by decide)) hml
  · -- `h->fuel == 0ULL`
    exact hQ 0#64 c ext s ml hcompat hlen hinv.cfgOk hinv.extOk (Or.inl rfl)
      (fun hc => absurd hc (by decide)) (fun hc => absurd hc (by decide)) hml
  · -- `oom == 0` and `fuel != 0`: propagate
    have hfu_pos : 0 < s.core.fuel.toNat := by
      have hpos : s.core.fuel.toNat ≠ 0 :=
        fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
      omega
    obtain ⟨F_cur, hinvW⟩ := fullM6HdrInv_exists_witness hinv
    refine m6Hdr_call_fullBcpS15_invW rfl (hProp _ _) hinvW hml ?_
    intro pr s1 m1 hinvW1 htr1 _ hfu1 hdom1 _ hr1 _ _ hm1
    have hinv1 := hinvW1.toInv
    have hlen1 := hinv1.sparse.lengths
    have hm1_f := fullM6HdrMem_focus hm1
    c0_hsteps
    · -- `pr == 2#64`: return `0#64`
      exact hQ 0#64 c ext s1 m1 hcompat hlen1 hinv1.cfgOk hinv1.extOk (Or.inl rfl)
        (fun hc => by cases hc) (fun hc => by cases hc) hm1
    · -- `pr == 1#64`: conflict
      have hpr1 : pr = 1#64 := hc
      obtain ⟨hfu_lt, _, hcok1⟩ := hr1 hpr1
      have hmu_conf : ∀ {c' : FullCfg} {ext' : List (BitVec 64)} {s' : FullState},
          c'.max_vars = c.max_vars → s'.core.fuel.toNat ≤ s1.core.fuel.toNat →
          FullM6HdrInv c' F0 ext' s' → m6SearchVariant c' s' < m6SearchVariant c s := by
        intro c' ext' s' hmveq hfule hinv'
        unfold m6SearchVariant
        rw [hmveq]
        have h1 : s'.core.fuel.toNat ≤ s.core.fuel.toNat - 1 := by omega
        have hmul : (c.max_vars + 1) * s'.core.fuel.toNat ≤
            (c.max_vars + 1) * (s.core.fuel.toNat - 1) :=
          Nat.mul_le_mul_left (c.max_vars + 1) h1
        have hte' : s'.core.trail_end ≤ c'.max_vars :=
          Nat.le_trans hinv'.sparse.lengths.core_ok.trail_end_le
            hinv'.sparse.lengths.core_ok.cur_vars_le
        have h2 : c.max_vars - s'.core.trail_end ≤ c.max_vars := Nat.sub_le _ _
        have hs_mul : (c.max_vars + 1) * s.core.fuel.toNat =
            (c.max_vars + 1) * (s.core.fuel.toNat - 1) + (c.max_vars + 1) := by
          have hsub : s.core.fuel.toNat - 1 + 1 = s.core.fuel.toNat := by omega
          calc (c.max_vars + 1) * s.core.fuel.toNat
              = (c.max_vars + 1) * (s.core.fuel.toNat - 1 + 1) := by rw [hsub]
            _ = (c.max_vars + 1) * (s.core.fuel.toNat - 1) + (c.max_vars + 1) := Nat.mul_succ _ _
        omega
      refine m6Hdr_call_m6Analyze_invW rfl (hAnalyze _ _) hinvW1 hcok1 hm1 ?_
      intro ast ext2 s2 m2 hext2 hlen2 hast hfu2 hu2 ha1 hm2
      have hm2_f := fullM6HdrMem_focus hm2
      c0_hsteps_nogrp
      · -- `ast == 20#64`
        exact hQ 20#64 c ext2 s2 m2 hcompat hlen2 hinv1.cfgOk hext2 (Or.inr (Or.inr rfl))
          (fun _ => hu2 hc) (fun hc => by cases hc) hm2
      · -- `ast != 1#64`
        exact hQ 0#64 c ext2 s2 m2 hcompat hlen2 hinv1.cfgOk hext2 (Or.inl rfl)
          (fun hc => by cases hc) (fun hc => by cases hc) hm2
      · -- `ast == 1#64`
        have hast1 : ast = 1#64 := hc
        obtain ⟨hinvW2, _⟩ := ha1 hast1
        have hinv2 := hinvW2.toInv
        let ContInv : BitVec 64 × FullCfg × List (BitVec 64) × FullState → Mem 64 → Prop :=
          fun ⟨_, c8, ext8, s8⟩ m8 =>
            FullCfgCompat c0 c8 ∧ FullM6HdrInv c8 F0 ext8 s8 ∧
            s8.core.fuel.toNat ≤ s2.core.fuel.toNat ∧ (FullM6HdrMem c8 ext8 s8 ⋆ R) m8
        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
          (fun v => (v, ())) (fun _ => True) ?_
          (fun _ hJmd => by c0_hsteps <;> exact hJmd _ trivial)
        intro _ mode_due _
        c0_hsteps_nogrp
        refine wp_join_state1 (α := BitVec 64 × FullCfg × List (BitVec 64) × FullState)
          Prod.fst ContInv ?_ ?_
        · intro _ ⟨r8, c8, ext8, s8⟩ m8 ⟨hc8, hinv8, hfu8, hm8⟩
          c0_hsteps
          exact ih (r8, c8, ext8, s8) m8
            (hmu_conf (hc8.max_vars.trans hcompat.max_vars.symm)
              (Nat.le_trans hfu8 hfu2) hinv8)
            ⟨hc8, hinv8, hm8⟩
        · intro Jr1 hJr1
          have hm2_f1 := fullM6HdrMem_focus hm2
          c0_hsplit
          · c0_hsteps
            refine m6Hdr_call_m6Reduce_invW rfl (hReduce _ _) hinvW2 hm2 ?_
            intro rr ext3 s3 m3 hinvW3 _ hfu3 hu3 hm3
            have hinv3 := hinvW3.toInv
            have hlen3 := hinv3.sparse.lengths
            c0_hsteps
            · exact hQ 20#64 c ext3 s3 m3 hcompat hlen3 hinv3.cfgOk hinv3.extOk
                (Or.inr (Or.inr rfl)) (fun _ => hu3 hc) (fun hc => by cases hc) hm3
            · exact hQ 0#64 c ext3 s3 m3 hcompat hlen3 hinv3.cfgOk hinv3.extOk
                (Or.inl rfl) (fun hc => by cases hc) (fun hc => by cases hc) hm3
            · exact hJr1 (rlim, c, ext3, s3) m3 ⟨hcompat, hinv3, hfu3, hm3⟩
          · refine wp_join_state1 (α := BitVec 64 × FullCfg × List (BitVec 64) × FullState)
              Prod.fst ContInv ?_ ?_
            · intro _ p mp hp; c0_hsteps; exact hJr1 p mp hp
            · intro Jr2 hJr2
              c0_hsplit
              · c0_hsteps
                refine m6Hdr_call_m6SwitchMode_inv rfl (hSwitch _ _) hinv2 hm2 ?_
                intro ext3 s3 m3 hinv3 hcore3 _ hm3
                c0_hsteps
                exact hJr2 (rlim, c, ext3, s3) m3
                  ⟨hcompat, hinv3, by rw [hcore3]; exact Nat.le_refl _, hm3⟩
              · refine wp_join_state1 (α := BitVec 64 × FullCfg × List (BitVec 64) × FullState)
                  Prod.fst ContInv ?_ ?_
                · intro _ p mp hp; c0_hsteps; exact hJr2 p mp hp
                · intro Jr3 hJr3
                  c0_hsteps
                  refine m6Hdr_call_fullRestartDue_inv_exact rfl (hRstDue _ _) hinv2 hm2 ?_
                  intro rdu s3 m3 hinv3 hcore3 _ hm3
                  have hm3_f := fullM6HdrMem_focus hm3
                  c0_hsplit
                  · c0_hsteps
                    refine m6Hdr_call_fullRestart_inv rfl (hRst _ _) hinv3 hm3 ?_
                    intro s4 m4 hinv4 _ hfu4 _ hm4
                    c0_hsteps
                    exact hJr3 (rlim, c, ext2, s4) m4
                      ⟨hcompat, hinv4, by rw [hfu4, hcore3]; exact Nat.le_refl _, hm4⟩
                  · refine wp_join_state1 (α := BitVec 64 × FullCfg × List (BitVec 64) × FullState)
                      Prod.fst ContInv ?_ ?_
                    · intro _ p mp hp; c0_hsteps; exact hJr3 p mp hp
                    · intro Jr4 hJr4
                      c0_hsteps
                      · -- `stable == 0 && conflicts >= reorder_limit`
                        refine m6Hdr_call_m4Reorder_inv rfl (hReorder _ _) hinv3 hm3 ?_
                        intro _r s4 m4 hinv4 hfu4 hm4
                        c0_hsteps
                        exact hJr4 (s3.scratch.conflicts + 10000#64, c, ext2, s4) m4
                          ⟨hcompat, hinv4, by rw [hfu4, hcore3]; exact Nat.le_refl _, hm4⟩
                      all_goals
                        have hm3_f' := fullM6HdrMem_focus hm3
                        first
                        | exact hJr4 (rlim, c, ext2, s3) m3
                            ⟨hcompat, hinv3, by rw [hcore3]; exact Nat.le_refl _, hm3⟩
                        | (refine m6Hdr_call_m6Rephase_inv rfl (hRephase _ _) hinv3 hm3 ?_
                           intro ext4 s4 m4 hinv4 hfu4 hm4
                           c0_hsteps
                           exact hJr4 (rlim, c, ext4, s4) m4
                             ⟨hcompat, hinv4, by rw [← hcore3]; exact hfu4, hm4⟩)
                        | (refine m6Hdr_call_m6Simplify_inv (dp := true) (de := false)
                             rfl (hSimplify _ _) hinv3 hm3 ?_
                           intro sr c4 ext4 s4 m4 hcomp4 hlen4 hcfg4 hext4 _hsr hfu4 hu4 hs1 hm4
                           have hcompat4 := hcompat.trans hcomp4
                           c0_hsteps
                           · exact hQ 20#64 c4 ext4 s4 m4 hcompat4 hlen4 hcfg4 hext4
                               (Or.inr (Or.inr rfl)) (fun _ => hu4 hc) (fun hc => by cases hc) hm4
                           · exact hQ 0#64 c4 ext4 s4 m4 hcompat4 hlen4 hcfg4 hext4
                               (Or.inl rfl) (fun hc => by cases hc) (fun hc => by cases hc) hm4
                           · obtain ⟨hinv4, _⟩ := hs1 hc
                             exact hJr4 (rlim, c4, ext4, s4) m4
                               ⟨hcompat4, hinv4, by rw [← hcore3]; exact hfu4, hm4⟩)
                        | (refine m6Hdr_call_m6Simplify_inv (dp := false) (de := true)
                             rfl (hSimplify _ _) hinv3 hm3 ?_
                           intro sr c4 ext4 s4 m4 hcomp4 hlen4 hcfg4 hext4 _hsr hfu4 hu4 hs1 hm4
                           have hcompat4 := hcompat.trans hcomp4
                           c0_hsteps
                           · exact hQ 20#64 c4 ext4 s4 m4 hcompat4 hlen4 hcfg4 hext4
                               (Or.inr (Or.inr rfl)) (fun _ => hu4 hc) (fun hc => by cases hc) hm4
                           · exact hQ 0#64 c4 ext4 s4 m4 hcompat4 hlen4 hcfg4 hext4
                               (Or.inl rfl) (fun hc => by cases hc) (fun hc => by cases hc) hm4
                           · obtain ⟨hinv4, _⟩ := hs1 hc
                             exact hJr4 (rlim, c4, ext4, s4) m4
                               ⟨hcompat4, hinv4, by rw [← hcore3]; exact hfu4, hm4⟩)
    · -- `pr == 0#64`: unassigned == 0
      exact hQ 10#64 c ext s1 m1 hcompat hlen1 hinv1.cfgOk hinv1.extOk (Or.inr (Or.inl rfl))
        (fun hc => by cases hc) (fun _ => hinv1.sparse.2.2.2.1.2) hm1
    · -- `pr == 0#64`: `m6_hdr_decide(h)`
      refine m6Hdr_call_m6Decide_inv rfl (hDecide _ _) hinv1 hm1 ?_
      intro dr ext2 s2 m2 hinv2 hdomd hfu2 h0d h1d hm2
      have hlen2 := hinv2.sparse.lengths
      have hm2_f := fullM6HdrMem_focus hm2
      c0_hsteps
      · exact hQ 10#64 c ext2 s2 m2 hcompat hlen2 hinv2.cfgOk hinv2.extOk
          (Or.inr (Or.inl rfl)) (fun hc => by cases hc)
          (fun _ => hinv2.sparse.2.2.2.1.2) hm2
      · exact hQ 0#64 c ext2 s2 m2 hcompat hlen2 hinv2.cfgOk hinv2.extOk
          (Or.inl rfl) (fun hc => by cases hc) (fun hc => by cases hc) hm2
      · -- `dr == 1#64`: continue loop
        have hdr1 : dr = 1#64 := hdomd.resolve_left hc
        obtain ⟨_, hte2⟩ := h1d hdr1
        have hte_lt : s.core.trail_end < s2.core.trail_end := by
          have := htr1.1; omega
        have hte2_le : s2.core.trail_end ≤ c.max_vars :=
          Nat.le_trans hlen2.core_ok.trail_end_le hlen2.core_ok.cur_vars_le
        have hmu_dec : m6SearchVariant c s2 < m6SearchVariant c s := by
          unfold m6SearchVariant
          rw [hfu2]
          have hmul : (c.max_vars + 1) * s1.core.fuel.toNat ≤
              (c.max_vars + 1) * s.core.fuel.toNat :=
            Nat.mul_le_mul_left (c.max_vars + 1) hfu1
          have hte0_le : s.core.trail_end ≤ c.max_vars :=
            Nat.le_trans hlen.core_ok.trail_end_le hlen.core_ok.cur_vars_le
          omega
        exact ih (rlim, c, ext2, s2) m2 hmu_dec ⟨hcompat, hinv2, hm2⟩

/-- Forwarding WP wrapper for `full_search` (`full_search_body`). -/
theorem full_search_wp (Γ : Env)
    (hSearchM6 : ∀ a m Q X, fullM6SearchSpec a m Q X →
      Γ "full_search_m6" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullM6SearchSpec a m Q X → Func.wp Γ full_search_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  unfold Func.wp full_search_body
  c0_call hSearchM6
  exact hs

/-! ## 4. `kissat_solve_bytes_m6` & `kissat_solve_bytes` End-to-End Proofs -/

/-- End-to-end WP proof of `kissat_solve_bytes_m6` against `fullM6SolveBytesCoreModelSpec`
(certifying BOTH UNSAT, constructive `readModelFromWorkM6` SAT with post-compaction `orig_mv`
& `bva_cap` restoration, and `UnitUnsatTrace`). -/
theorem kissat_solve_bytes_m6_core_wp (Γ : Env)
    (hMemInit : ∀ a m Q X, fullM6MemInitExactSpec a m Q X →
      Γ "full_m6_mem_init" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hParse : ∀ a m Q X, Full.fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hPre : ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Γ "full_preprocess_m6" [i64] [i64] a m Q X)
    (hSearch : ∀ a m Q X, fullM6SearchSpec a m Q X →
      Γ "full_search_m6" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, Full.fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullM6SolveBytesCoreModelSpec a m Q X →
      Func.wp Γ kissat_solve_bytes_m6_body a m Q X := by
  rintro ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, ⟨⟩⟩ m Q X hs
  obtain ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, hQ⟩ :=
    fullM6SolveBytesCoreModelSpec_elim hs
  unfold Func.wp kissat_solve_bytes_m6_body
  have ret0 : ∀ m' (hno : fuel = 0#64 ∨ cnf_ptr = 0#64 ∨ work_ptr = 0#64 ∨
      wlen < fullAlignPad work_ptr + fullM6HdrTotalBytes),
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' → Q (0#64, ()) m' := by
    intro m' hno hm'
    refine hQ 0#64 m' (Or.inl rfl) (fun hc => by cases hc) (fun hc => by cases hc)
      (fun mv nc _ hcn hwk hfu hsz _ _ _ => ?_) hm'
    rcases hno with rfl | rfl | rfl | hlt
    · simp at hfu
    · exact absurd rfl hcn
    · exact absurd rfl hwk
    · have hpad := fullAlignPad_lt8 work_ptr
      unfold fullM6HdrTotalBytes at hlt
      have : fullM6ExtBytes = 2304 := rfl
      have : 1152 ≤ fullFixedBytes mv + nc * 40 + 136 := by
        unfold fullFixedBytes; omega
      omega
  wp_unfold
  refine ⟨fun hf0 => ?_, fun _ => ?_⟩
  · exact ret0 m (Or.inl hf0) hm
  refine ⟨fun hcp0 => ?_, fun _ => ?_⟩
  · exact ret0 m (Or.inr (Or.inl hcp0)) hm
  refine ⟨fun hwp0 => ?_, fun _ => ?_⟩
  · exact ret0 m (Or.inr (Or.inr (Or.inl hwp0))) hm
  have hnot0 : ~~~(0 : BitVec 64) = 0xFFFFFFFFFFFFFFFF#64 := rfl
  rw [hnot0, m6_bv64_ugt_max_sub_false hcfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  rw [m6_bv64_ugt_max_sub_false hwfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  have hpad_eq := m6_alignPad_bv_eq work_ptr
  have hpad_ofNat := m6_alignPad_bv_ofNat_eq work_ptr
  have hpad_comm := m6_alignPad_bv_comm_eq work_ptr
  have hw_nat : (BitVec.ofNat 64 wlen).toNat = wlen := bv64_ofNat_toNat (by omega)
  have hp_nat : (BitVec.ofNat 64 (fullAlignPad work_ptr)).toNat = fullAlignPad work_ptr :=
    bv64_ofNat_toNat (by have := fullAlignPad_lt8 work_ptr; omega)
  have hfit_p : fullAlignPad work_ptr + fullM6HdrTotalBytes < 2 ^ 64 := by
    have := fullAlignPad_lt8 work_ptr; unfold fullM6HdrTotalBytes; omega
  have hpad_ult : (BitVec.ofNat 64 wlen).ult (((8 - (work_ptr &&& 7)) &&& 7) + 3456) =
      decide (wlen < fullAlignPad work_ptr + fullM6HdrTotalBytes) := by
    rw [hpad_ofNat, show (3456 : BitVec 64) = BitVec.ofNat 64 fullM6HdrTotalBytes from rfl,
      bv_add_ofNat, bv_ult_eq (by omega) (by omega)]
  rw [hpad_ult]; simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun hlt => ?_, fun hw_ge_not => ?_⟩
  · exact ret0 m (Or.inr (Or.inr (Or.inr hlt))) hm
  have hw_ge : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen := Nat.le_of_not_lt hw_ge_not
  have hwfit_lt : wlen ≤ 2 ^ 64 := Nat.le_of_lt (by omega)
  have hm_wb : (bytes cnf_ptr cnfBytes ⋆
      region (fullM6WorkBase work_ptr) (wlen - fullAlignPad work_ptr) ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m := by
    have heq : fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr) = wlen := by
      unfold fullM6HdrTotalBytes at hw_ge; omega
    have hmg : region work_ptr (fullAlignPad work_ptr) ⋆
        region (fullM6WorkBase work_ptr) (wlen - fullAlignPad work_ptr) =
        region work_ptr wlen :=
      region_merge_eq heq hwfit_lt
    rw [← hmg] at hm
    exact sep_ac hm
  have hwb_fit : (fullM6WorkBase work_ptr).toNat + (wlen - fullAlignPad work_ptr) <
      2 ^ 64 := by
    have := fullM6WorkBase_toNat_lt (work_ptr := work_ptr) (wlen := wlen) hw_ge hwfit
    omega
  have hwb_bv : work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) =
      fullM6WorkBase work_ptr := rfl
  have hav_bv : BitVec.ofNat 64 wlen - BitVec.ofNat 64 (fullAlignPad work_ptr) =
      BitVec.ofNat 64 (wlen - fullAlignPad work_ptr) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by
        simp only [BitVec.le_def, hw_nat, hp_nat]
        unfold fullM6HdrTotalBytes at hw_ge; omega),
      hw_nat, hp_nat, bv64_ofNat_toNat (by omega)]
  c0_hsteps
  c0_call hMemInit
  simp only [hpad_ofNat]
  refine fullM6MemInitExactSpec_of
    (R := region work_ptr (fullAlignPad work_ptr) ⋆ R) rfl hcfit
    (by rw [hwb_bv, hav_bv, bv64_ofNat_toNat (by omega)]; exact hwb_fit)
    (by rw [hwb_bv, hav_bv, bv64_ofNat_toNat (by omega)]; exact sep_ac hm_wb) ?_ ?_
  · intro m' hm' hbad
    c0_hfast
    · have hm'_orig : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' := by
        have h1 : (region work_ptr (fullAlignPad work_ptr) ⋆
            region (fullM6WorkBase work_ptr) (wlen - fullAlignPad work_ptr) ⋆
            (bytes cnf_ptr cnfBytes ⋆ R)) m' := by
          rw [hwb_bv, hav_bv, bv64_ofNat_toNat (by omega)] at hm'
          exact sep_ac hm'
        have hpad_eq' : work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) =
            fullM6WorkBase work_ptr := rfl
        have hmg := region_merge_eq (a := work_ptr)
          (show fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr) = wlen by
            unfold fullM6HdrTotalBytes at hw_ge; omega) (by omega)
        rw [hpad_eq'] at hmg
        rw [hmg] at h1; exact sep_ac h1
      refine hQ 0#64 m' (Or.inl rfl) (fun hc => by cases hc) (fun hc => by cases hc)
        (fun mv nc i0 _ _ _ hsz hi0 hp hu => ?_) hm'_orig
      rcases hbad with hlt | hcap
      · rw [hav_bv, bv64_ofNat_toNat (by omega)] at hlt
        unfold fullM6HdrTotalBytes at hlt hw_ge
        have := fullAlignPad_lt8 work_ptr; omega
      · have hcap' := hcap mv nc (cnfBytes.drop i0) hp
        rw [hav_bv, bv64_ofNat_toNat (by omega)] at hcap'
        have : fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen := hsz
        have := fullAlignPad_lt8 work_ptr
        unfold fullFixedBytes at *; omega
    · exact absurd rfl hc
  · intro c0 ext0 s0 j0 rest0 m1 hch0 hca0 hcfg0 hinit0 hp0 hj0 hdrop0 hinv0 hcv0
      hdcur0 hal0 hwlen0 hte0 hprop0 hcl0 hfu0 hoom0 hinc0 hprb0 hvals0 hwvec0 hm1
    have hch0_work : c0.hdr = fullM6WorkHdr work_ptr := by
      rw [hch0, hwb_bv]; rfl
    have hca0_work : c0.avail = wlen - fullAlignPad work_ptr - fullM6ExtBytes := by
      rw [hca0, hav_bv, bv64_ofNat_toNat (by omega)]
    c0_hfast
    · exfalso
      have hnz := M6HdrCfgOk_le hcfg0
      rw [hc] at hnz
      simp at hnz
    · have htake0 : List.take (2 * c0.mv) s0.core.vals =
          List.replicate (2 * c0.mv) 0#8 := by
        have hle : 2 * c0.mv ≤ 2 * c0.max_vars := by
          have := c0.hbva; omega
        rw [hvals0, List.take_replicate, Nat.min_eq_left hle]
      have hm1_parse : (bytes cnf_ptr cnfBytes ⋆ FullMem c0 s0 ⋆
          (array64 (c0.hdr - 2304) ext0 ⋆
            region work_ptr (fullAlignPad work_ptr) ⋆ R)) m1 :=
        sep_ac (fullM6HdrMem_ext_focus
          (R := bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)
          (sep_ac hm1))
      c0_call hParse
      refine ⟨c0, s0, cnf_ptr, cnfBytes, j0,
        array64 (c0.hdr - 2304) ext0 ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R,
        rfl, rfl, hcfit, hj0, hdrop0 ▸ hp0, hcv0, hdcur0, hcl0, hte0, hprop0, hal0,
        hoom0, hprb0, hinc0, hvals0, hwvec0, hinv0.sparse, hm1_parse, ?_⟩
      intro pr s1 m2 hlen1 hdomp _ _ _ hp20 hp1 hunitp hm2
      have hm2_hdr : (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c0 ext0 s1 ⋆
          region work_ptr (fullAlignPad work_ptr) ⋆ R) m2 :=
        sep_ac (fullM6HdrMem_ext_unfocus (c := c0) (ext := ext0) (s := s1)
          (R := bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)
          (sep_ac hm2))
      c0_hfast
      · -- `pr != 1#64`: `pr = 20#64` or `pr = 0#64`
        have hm2_reg : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m2 :=
          m6_bytes_hdrMem_to_region hw_ge hwfit_lt hch0_work hca0_work hcfg0 hinit0.toOk
            hlen1 hm2_hdr
        rcases hdomp with rfl | rfl | rfl
        · exact hQ 0#64 m2 (Or.inl rfl) (fun h => by cases h) (fun h => by cases h)
            (fun mv nc i1 _ _ _ _ _ hp1' hu1' => by
              have heq : some (mv, nc, cnfBytes.drop i1) =
                  some (c0.mv, c0.nc, cnfBytes.drop j0) := by
                rw [← hp1', hp0, hdrop0]
              have hinj := Option.some.inj heq
              have hmv_eq : mv = c0.mv := congrArg (·.1) hinj
              have hnc_eq : nc = c0.nc := congrArg (·.2.1) hinj
              have hdrop_eq : cnfBytes.drop i1 = cnfBytes.drop j0 :=
                congrArg (·.2.2) hinj
              rw [hmv_eq, hnc_eq, hdrop_eq] at hu1'
              have hu0 : UnitUnsatTrace c0.mv (List.take (2 * c0.mv) s0.core.vals)
                  (cnfBytes.drop j0) c0.nc := by
                simpa [htake0] using hu1'
              have h20 := hunitp hu0
              cases h20)
            hm2_reg
        · exact absurd rfl hc
        · exact hQ 20#64 m2 (Or.inr (Or.inr rfl)) (fun _ => hp20 rfl)
            (fun h => by cases h) (fun _ _ _ _ _ _ _ _ _ _ => rfl) hm2_reg
      · -- `pr == 1#64`: `parseDimacs cnfBytes = some cnf`
        have hpr1 : pr = 1#64 := hc
        obtain ⟨cnf, hparse_cnf, hsp1, hcl1⟩ := hp1 hpr1
        have hcnf_pos : CnfVarsPos cnf := m6_parseDimacs_vars_pos hparse_cnf
        have hno_utrace : ¬ ∃ mv nc i1,
            parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i1) ∧
            UnitUnsatTrace mv (List.replicate (2 * mv) 0#8)
              (cnfBytes.drop i1) nc := by
          rintro ⟨mv, nc, i1, hp1', hu1'⟩
          have heq : some (mv, nc, cnfBytes.drop i1) =
              some (c0.mv, c0.nc, cnfBytes.drop j0) := by
            rw [← hp1', hp0, hdrop0]
          have hinj := Option.some.inj heq
          have hmv_eq : mv = c0.mv := congrArg (·.1) hinj
          have hnc_eq : nc = c0.nc := congrArg (·.2.1) hinj
          have hdrop_eq : cnfBytes.drop i1 = cnfBytes.drop j0 :=
            congrArg (·.2.2) hinj
          rw [hmv_eq, hnc_eq, hdrop_eq] at hu1'
          have hu0 : UnitUnsatTrace c0.mv (List.take (2 * c0.mv) s0.core.vals)
              (cnfBytes.drop j0) c0.nc := by
            simpa [htake0] using hu1'
          have h20 := hunitp hu0
          rw [hpr1] at h20; cases h20
        have hm2_f := fullM6HdrMem_focus
          (R := bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)
          (sep_ac hm2_hdr)
        have hinv1 : FullM6HdrInv c0 (shiftDownCnf cnf) ext0 s1 :=
          FullM6HdrInv.mk_inv hcfg0 hinit0.toOk hsp1
        have hm2_call : (FullM6HdrMem c0 ext0 s1 ⋆
            (bytes cnf_ptr cnfBytes ⋆
              region work_ptr (fullAlignPad work_ptr) ⋆ R)) m2 :=
          sep_ac hm2_hdr
        c0_call hPre
        refine fullM6PreprocessSpec_of hinv1 hcl1 hm2_call (by
                    intro ppr c2 ext2 s2 m3 hcomp2 hlen2 hcfg2 hext2 hdom2 _ hpp20 hpp1 hpp10 hm3
                    have hm3' : (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c2 ext2 s2 ⋆
                        region work_ptr (fullAlignPad work_ptr) ⋆ R) m3 := sep_ac hm3
                    have hch2_w : c2.hdr = fullM6WorkHdr work_ptr := hcomp2.hdr.trans hch0_work
                    have hca2_w : c2.avail = wlen - fullAlignPad work_ptr - fullM6ExtBytes :=
                      hcomp2.avail.trans hca0_work
                    c0_hsteps_nogrp
                    · -- `ppr == 20#64`
                      have hm3_reg : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m3 :=
                        m6_bytes_hdrMem_to_region hw_ge hwfit_lt hch2_w hca2_w
                          hcfg2 hext2 hlen2 hm3'
                      exact hQ 20#64 m3 (Or.inr (Or.inr rfl))
                        (fun _ => ⟨cnf, hparse_cnf, shiftDownCnf_unsat hcnf_pos (hpp20 hc)⟩)
                        (fun h => by cases h)
                        (fun _ _ _ _ _ _ _ _ hp hu => absurd ⟨_, _, _, hp, hu⟩ hno_utrace)
                        hm3_reg
                    · -- Join outer `J_fin` handling `(sr, c_end, ext_end, s_end)`
                      have hpp_ne20 : ppr ≠ 20#64 := hc
                      let PreFin : BitVec 64 → FullCfg → List (BitVec 64) → FullState →
                          Mem 64 → Prop := fun sr cE extE sE mE =>
                        FullCfgCompat c0 cE ∧ FullM6HdrCfgOk cE ∧ M6HdrExtOk extE ∧
                        sE.LengthsOk cE ∧
                        (sr = 0#64 ∨ sr = 10#64 ∨ sr = 20#64) ∧
                        (sr = 20#64 → cnf.Unsat) ∧
                        (sr = 10#64 → sE.scratch.extend_len ≤ cE.extend_cap) ∧
                        (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem cE extE sE ⋆
                          region work_ptr (fullAlignPad work_ptr) ⋆ R) mE
                      c0_to_group
                      refine wp_join_group (ts := [i64])
                        (fun (sr, _) mE => ∃ cE extE sE, PreFin sr cE extE sE mE) ?_ ?_
                      · rintro _ ⟨sr, ⟨⟩⟩ mE ⟨cE, extE, sE, hcompatE, hcfgE, hextE, hlenE,
                          hdomE, huE, hext_leE, hmE⟩
                        have hchE_w : cE.hdr = fullM6WorkHdr work_ptr :=
                          hcompatE.hdr.trans hch0_work
                        have hcaE_w : cE.avail = wlen - fullAlignPad work_ptr - fullM6ExtBytes :=
                          hcompatE.avail.trans hca0_work
                        c0_hfast
                        · -- `sr == 10#64`: `full_extend` + `orig_mv` + `bva_cap`
                          have hext_le : sE.scratch.extend_len ≤ cE.extend_cap := hext_leE hc
                          rw [← hcompatE.hdr]
                          c0_call hExt
                          refine ⟨cE, sE, array64 (cE.hdr - 2304) extE ⋆
                              (bytes cnf_ptr cnfBytes ⋆
                                region work_ptr (fullAlignPad work_ptr) ⋆ R),
                              ⟨rfl, hext_le⟩, hlenE, ?_, ?_⟩
                          · simp only [fullExtendSlice_mem]
                            exact sep_ac (fullM6HdrMem_ext_focus (R := bytes cnf_ptr cnfBytes ⋆
                              region work_ptr (fullAlignPad work_ptr) ⋆ R) (sep_ac hmE))
                          · intro ⟨⟩ s4 m4 _ hlen4 _ hm4
                            simp only [fullExtendSlice_mem] at hm4
                            have hm4_f : (FullMem cE s4 ⋆
                                (array64 (cE.hdr - 2304) extE ⋆ bytes cnf_ptr cnfBytes ⋆
                                  region work_ptr (fullAlignPad work_ptr) ⋆ R)) m4 := sep_ac hm4
                            refine wp_store_sep
                              (FullM4Compact.full_store_mv_mid (BitVec.ofNat 64 c0.mv) hm4_f) ?_
                            intro m4_1 hm4_1
                            c0_step
                            refine wp_load_of (FullM4Compact.full_load_max_vars_mid hm4_1) ?_
                            c0_step
                            let bva_bv : BitVec 64 :=
                              BitVec.ofNat 64 cE.max_vars - BitVec.ofNat 64 c0.mv
                            have hmid_arr : (array64 (cE.hdr + 32) (Full.hdrTailWords cE s4) ⋆
                                (dimacsState cE.hdr (BitVec.ofNat 64 c0.mv)
                                    (BitVec.ofNat 64 cE.nc) s4.core.d_cur s4.core.d_val ⋆
                                  FullCoreArrays cE s4.core ⋆ FullScratchArrays cE s4.scratch ⋆
                                  cE.pad ⋆ array64 (cE.hdr - 2304) extE ⋆ bytes cnf_ptr cnfBytes ⋆
                                  region work_ptr (fullAlignPad work_ptr) ⋆ R)) m4_1 := by
                              unfold FullM4Compact.FullMemShrinkMid at hm4_1; exact sep_ac hm4_1
                            obtain ⟨hst_bva_ok, hm4_bva⟩ := store_array64 (i := 94) bva_bv
                              (by rw [Full.hdrTailWords_length]; decide) hmid_arr
                            have hptr784 : cE.hdr + 32 + BitVec.ofNat 64 (8 * 94) =
                                cE.hdr + 784 := by
                              rw [BitVec.add_assoc, show (32 : BitVec 64) +
                                BitVec.ofNat 64 (8 * 94) = 784 by decide]
                            rw [hptr784] at hst_bva_ok hm4_bva
                            refine wp_store_sep ⟨hst_bva_ok, hm4_bva⟩ ?_
                            intro m4_2 hm4_2
                            have hld_pvals : loadVal m4_2 i64 (cE.hdr + (64 : BitVec 64)) =
                                some cE.pVals := by
                              have haddr64 : cE.hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * 4) =
                                  cE.hdr + (64 : BitVec 64) := by bv_omega
                              have h4lt : 4 < ((Full.hdrTailWords cE s4).set 94 bva_bv).length := by
                                rw [List.length_set, Full.hdrTailWords_length]; decide
                              have hget4 : ((Full.hdrTailWords cE s4).set 94 bva_bv)[4]? =
                                  some cE.pVals := rfl
                              have hv := loadVal_array64 h4lt hm4_2
                              rw [haddr64] at hv
                              have h4val : ((Full.hdrTailWords cE s4).set 94 bva_bv)[4] =
                                  cE.pVals := by
                                have := List.getElem?_eq_getElem h4lt
                                rw [hget4] at this; exact (Option.some.inj this).symm
                              rwa [h4val] at hv
                            c0_hsteps
                            refine wp_load_of hld_pvals ?_
                            have hm4_2' : (bytes cnf_ptr cnfBytes ⋆
                                dimacsState cE.hdr (BitVec.ofNat 64 c0.mv)
                                  (BitVec.ofNat 64 cE.nc) s4.core.d_cur s4.core.d_val ⋆
                                bytes cE.pVals (s4.core.vals.map UInt8.ofBitVec) ⋆
                                (array64 (cE.hdr + 32) ((Full.hdrTailWords cE s4).set 94 bva_bv) ⋆
                                  array (t := i8) cE.pLitMark s4.core.lit_mark ⋆
                                  array (t := i8) cE.pMark s4.core.mrk ⋆
                                  FullCoreU32A cE s4.core ⋆ FullCoreU32B cE s4.core ⋆
                                  FullCoreDynArrs cE s4.core ⋆
                                  FullScratchArrays cE s4.scratch ⋆ cE.pad ⋆
                                  array64 (cE.hdr - 2304) extE ⋆
                                  region work_ptr (fullAlignPad work_ptr) ⋆ R)) m4_2 := by
                              have hb_vals : ∀ f, array (t := i8) cE.pVals s4.core.vals f →
                                  bytes cE.pVals (s4.core.vals.map UInt8.ofBitVec) f :=
                                fun f hf => by
                                have hb := array_eq_bytesOf (t := i8) cE.pVals s4.core.vals
                                  (by have hmx := cE.hmaxv; unfold dimacsBound at hmx
                                      simp only [Ty.bytes, Ty.size, i8, hlen4.core_ok.vals_len]
                                      omega) hf
                                rw [bytesOf_i8_eq_map] at hb; exact hb.symm
                              have hm4_2_exp : (array (t := i8) cE.pVals s4.core.vals ⋆
                                  (bytes cnf_ptr cnfBytes ⋆
                                    dimacsState cE.hdr (BitVec.ofNat 64 c0.mv)
                                      (BitVec.ofNat 64 cE.nc) s4.core.d_cur s4.core.d_val ⋆
                                    array64 (cE.hdr + 32)
                                      ((Full.hdrTailWords cE s4).set 94 bva_bv) ⋆
                                    array (t := i8) cE.pLitMark s4.core.lit_mark ⋆
                                    array (t := i8) cE.pMark s4.core.mrk ⋆
                                    FullCoreU32A cE s4.core ⋆ FullCoreU32B cE s4.core ⋆
                                    FullCoreDynArrs cE s4.core ⋆
                                    FullScratchArrays cE s4.scratch ⋆ cE.pad ⋆
                                    array64 (cE.hdr - 2304) extE ⋆
                                    region work_ptr (fullAlignPad work_ptr) ⋆ R)) m4_2 := by
                                unfold FullCoreArrays FullCoreByteArrs at hm4_2
                                exact sep_ac hm4_2
                              exact sep_ac (sep_mono hb_vals hm4_2_exp)
                            have hmxE := cE.hmaxv; unfold dimacsBound at hmxE
                            have hmv0_le : c0.mv ≤ cE.max_vars := by
                              have := c0.hbva; have := hcompatE.max_vars; omega
                            c0_call hCheck
                            refine ⟨BitVec.ofNat 64 c0.mv, BitVec.ofNat 64 cE.nc, s4.core.d_cur,
                              s4.core.d_val, cnfBytes, s4.core.vals.map UInt8.ofBitVec, c0.mv, _,
                              rfl, rfl, hcfit,
                              (by have := c0.hbva; have := c0.hmaxv
                                  unfold dimacsBound at *; omega),
                              by rw [List.length_map, hlen4.core_ok.vals_len]; omega,
                              by rw [List.length_map, hlen4.core_ok.vals_len]; omega,
                              hm4_2', ?_⟩
                            intro ok mv' nc' cur' val' m5 hok_eq hm5
                            have hm5_reg : (bytes cnf_ptr cnfBytes ⋆
                                region work_ptr wlen ⋆ R) m5 :=
                              m6_satCheckModel_post_to_m6_region hw_ge hwfit hchE_w hcaE_w
                                hextE hlen4 hm5
                            c0_hsteps_nogrp
                            refine wp_join_state_pure (α := BitVec 64) (fun r => (r, ()))
                              (fun ret => ret = 0#64 ∨
                                (ret = 10#64 ∧
                                  runKissatCheckModel cnfBytes
                                    (s4.core.vals.map UInt8.ofBitVec) c0.mv = true)) ?_ ?_
                            · intro _ ret hret
                              c0_hsteps
                              rcases hret with rfl | ⟨rfl, hrun⟩
                              · exact hQ 0#64 m5 (Or.inl rfl) (fun h => by cases h)
                                  (fun h => by cases h)
                                  (fun _ _ _ _ _ _ _ _ hp hu => absurd ⟨_, _, _, hp, hu⟩ hno_utrace)
                                  hm5_reg
                              · refine hQ 10#64 m5 (Or.inr (Or.inl rfl)) (fun h => by cases h)
                                  (fun _ => ?_)
                                  (fun _ _ _ _ _ _ _ _ hp hu => absurd ⟨_, _, _, hp, hu⟩ hno_utrace)
                                  hm5_reg
                                refine sat_of_checkModel_post_m6_bva (bva_bv := bva_bv)
                                  (R := bytes cnf_ptr cnfBytes ⋆
                                    dimacsState cE.hdr mv' nc' cur' val' ⋆
                                    array (t := i8) cE.pLitMark s4.core.lit_mark ⋆
                                    array (t := i8) cE.pMark s4.core.mrk ⋆
                                    FullCoreU32A cE s4.core ⋆ FullCoreU32B cE s4.core ⋆
                                    FullCoreDynArrs cE s4.core ⋆
                                    FullScratchArrays cE s4.scratch ⋆ cE.pad ⋆
                                    array64 (cE.hdr - 2304) extE ⋆
                                    region work_ptr (fullAlignPad work_ptr) ⋆ R)
                                  hchE_w hcompatE hlen4 (sep_ac hm5) hrun
                            · intro Jr hJr
                              c0_hsteps
                              · by_cases hrun : runKissatCheckModel cnfBytes
                                    (s4.core.vals.map UInt8.ofBitVec) c0.mv = true
                                · exact hJr 10#64 (Or.inr ⟨rfl, hrun⟩)
                                · exfalso; rw [hc] at hok_eq; simp [hrun] at hok_eq
                              · exact hJr 0#64 (Or.inl rfl)
                        · -- `sr != 10#64` (`sr = 0#64` or `sr = 20#64`)
                          have hmE_reg : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) mE :=
                            m6_bytes_hdrMem_to_region hw_ge hwfit_lt hchE_w hcaE_w
                              hcfgE hextE hlenE hmE
                          c0_hfast
                          rcases hdomE with rfl | rfl | rfl
                          · exact hQ 0#64 mE (Or.inl rfl) (fun h => by cases h)
                              (fun h => by cases h)
                              (fun _ _ _ _ _ _ _ _ hp hu => absurd ⟨_, _, _, hp, hu⟩ hno_utrace)
                              hmE_reg
                          · exact absurd rfl hc
                          · exact hQ 20#64 mE (Or.inr (Or.inr rfl))
                              (fun _ => ⟨cnf, hparse_cnf, huE rfl⟩)
                              (fun h => by cases h) (fun _ _ _ _ _ _ _ _ _ _ => rfl) hmE_reg
                      · intro J_fin hJ_fin
                        c0_hsteps_nogrp
                        · -- `ppr == 10#64`
                          exact hJ_fin (10#64, ()) m3 ⟨c2, ext2, s2, hcomp2, hcfg2, hext2, hlen2,
                            Or.inr (Or.inl rfl), fun h => absurd h (by decide),
                            fun _ => hpp10 hc, hm3'⟩
                        · have hpp_ne10 : ppr ≠ 10#64 := hc
                          c0_to_group
                          refine wp_join_group (ts := [i64])
                            (fun (sr, _) mE => ∃ cE extE sE, PreFin sr cE extE sE mE)
                            (fun _ ⟨sr, ⟨⟩⟩ mE hpre => hJ_fin (sr, ()) mE hpre) ?_
                          intro J_mid hJ_mid
                          c0_hsteps_nogrp
                          · -- `ppr == 0#64`
                            exact hJ_mid (0#64, ()) m3 ⟨c2, ext2, s2, hcomp2, hcfg2, hext2,
                              hlen2, Or.inl rfl, fun h => absurd h (by decide),
                              fun h => absurd h (by decide), hm3'⟩
                          · -- `ppr == 1#64`: `full_search_m6`
                            have hpp_ne0 : ppr ≠ 0#64 := hc
                            have hppr1 : ppr = 1#64 := by
                              rcases hdom2 with rfl | rfl | rfl | rfl
                              · exact absurd rfl hpp_ne0
                              · rfl
                              · exact absurd rfl hpp_ne10
                              · exact absurd rfl hpp_ne20
                            obtain ⟨hinv2, hcl2⟩ := hpp1 hppr1
                            have hm3_call : (FullM6HdrMem c2 ext2 s2 ⋆
                                (bytes cnf_ptr cnfBytes ⋆
                                  region work_ptr (fullAlignPad work_ptr) ⋆ R)) m3 :=
                              sep_ac hm3'
                            rw [← hcomp2.hdr]
                            c0_call hSearch
                            refine fullM6SearchSpec_of hinv2 hcl2 hm3_call ?_
                            intro sr c3 ext3 s3 m4 hcomp3 hlen3 hcfg3 hext3 hdom3 hs20 hs10 hm4
                            exact hJ_mid (sr, ()) m4 ⟨c3, ext3, s3, hcomp2.trans hcomp3, hcfg3,
                              hext3, hlen3, hdom3,
                              fun h20 => shiftDownCnf_unsat hcnf_pos (hs20 h20),
                              hs10, sep_ac hm4⟩)

/-- Forwarding `kissat_solve_bytes_m6` WP against `fullM6SolveBytesSpec`. -/
theorem kissat_solve_bytes_m6_wp (Γ : Env)
    (hMemInit : ∀ a m Q X, fullM6MemInitExactSpec a m Q X →
      Γ "full_m6_mem_init" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hParse : ∀ a m Q X, Full.fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hPre : ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Γ "full_preprocess_m6" [i64] [i64] a m Q X)
    (hSearch : ∀ a m Q X, fullM6SearchSpec a m Q X →
      Γ "full_search_m6" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, Full.fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullM6SolveBytesSpec a m Q X →
      Func.wp Γ kissat_solve_bytes_m6_body a m Q X :=
  fun a m Q X hs =>
    kissat_solve_bytes_m6_core_wp Γ hMemInit hParse hPre hSearch hExt hCheck a m Q X
      (fullM6SolveBytesCoreModelSpec_of_spec hs)

/-- Forwarding WP wrapper for `kissat_solve_bytes` (`kissat_solve_bytes_body`). -/
theorem kissat_solve_bytes_core_wp (Γ : Env)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hSolveM6 : ∀ a m Q X, solveSpec a m Q X →
      Γ "kissat_solve_bytes_m6" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, solveSpec a m Q X → Func.wp Γ kissat_solve_bytes_body a m Q X := by
  rintro ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, ⟨⟩⟩ m Q X hs
  unfold Func.wp kissat_solve_bytes_body
  c0_call hSolveM6
  exact hs

/-! ## 5. Tail Spec Table & Parametric `mkM6OrchEnv_moduleOk` -/

/-- Forwarding WP wrapper for `full_preprocess` (`full_preprocess_body`). -/
theorem full_preprocess_wp (Γ : Env)
    (hPreM6 : ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Γ "full_preprocess_m6" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullM6PreprocessSpec a m Q X → Func.wp Γ full_preprocess_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  unfold Func.wp full_preprocess_body
  c0_call hPreM6
  exact hs

/-- Tail `5` functions of `FullM6Orch.m6OrchModule`:
`[full_search_m6, kissat_solve_bytes_m6, full_preprocess, full_search, kissat_solve_bytes]`. -/
def m6OrchTailFns : List Fn := m6Orch_fns.drop 24

/-- Specification table rows matching `m6OrchTailFns` (`5` entries, `0` exits). -/
def m6OrchTailSpecTable
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64] := fullM6SolveBytesCoreModelSpec) :
    List SpecEntry :=
  [ ⟨"full_search_m6", [i64], [i64], fullM6SearchSpec, true⟩,
    ⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64], solveSpec, true⟩,
    ⟨"full_preprocess", [i64], [i64], fullM6PreprocessSpec, true⟩,
    ⟨"full_search", [i64], [i64], fullM6SearchSpec, true⟩,
    ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], solveSpec, true⟩ ]

theorem m6OrchTailSpecTable_len (s : Spec [i64, i64, i64, i64, i64] [i64]) :
    m6OrchTailFns.length = (m6OrchTailSpecTable s).length := by rfl

theorem m6OrchTailSpecTable_sigs (s : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m6OrchTailSpecTable s).map (fun e => (e.name, e.as, e.rs)) =
      m6OrchTailFns.map (fun f => (f.name, f.as, f.rs)) := by rfl

theorem m6OrchTailSpecTable_noExit (s : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m6OrchTailSpecTable s).all SpecEntry.noExit = true := by rfl

theorem m6OrchTailFns_wf : AllFns Fn.Wf m6OrchTailFns :=
  allFns_drop (allFns_of_mem m6Orch_fns_wf) 24

/-- Parametric `TableImpl` for `m6OrchTailFns` (`full_search_m6`, `kissat_solve_bytes_m6`,
`full_preprocess`, `full_search`, `kissat_solve_bytes`) with ZERO dependency on
`FullM6OrchProof0/1.lean`. -/
theorem m6Orch_tail_tableImpl (Γ : Env)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hWeaken : ∀ a m Q X, solveSpec a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hMemInit : ∀ a m Q X, fullM6MemInitExactSpec a m Q X →
      Γ "full_m6_mem_init" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hParse : ∀ a m Q X, Full.fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hAnalyze : ∀ a m Q X, FullM6Hdr.m6HdrAnalyzeSpec a m Q X →
      Γ "full_analyze_m6_hdr" [i64] [i64] a m Q X)
    (hReduce : ∀ a m Q X, m6ReduceSpec a m Q X →
      Γ "full_reduce_m6" [i64, .bool] [i64] a m Q X)
    (hSwitch : ∀ a m Q X, m6SwitchModeSpec a m Q X →
      Γ "full_switch_mode_m6" [i64] [] a m Q X)
    (hRstDue : ∀ a m Q X, Full.fullRestartDueSpec a m Q X →
      Γ "full_restart_due" [i64] [i64] a m Q X)
    (hRst : ∀ a m Q X, Full.fullRestartSpec a m Q X →
      Γ "full_restart" [i64] [] a m Q X)
    (hReorder : ∀ a m Q X, FullM4.m4ReorderSpec a m Q X →
      Γ "full_reorder_m6" [i64, i64] [i64] a m Q X)
    (hRephase : ∀ a m Q X, m6aRephaseSpec a m Q X →
      Γ "full_rephase_m6_hdr" [i64] [] a m Q X)
    (hPre : ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Γ "full_preprocess_m6" [i64] [i64] a m Q X)
    (hSimplify : ∀ a m Q X, fullM6SimplifySpec a m Q X →
      Γ "full_simplify_m6" [i64, .bool, .bool] [i64] a m Q X)
    (hDecide : ∀ a m Q X, FullM6Hdr.m6HdrDecideSpec a m Q X →
      Γ "m6_hdr_decide" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, Full.fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hSearchM6 : ∀ a m Q X, fullM6SearchSpec a m Q X →
      Γ "full_search_m6" [i64] [i64] a m Q X)
    (hSolveM6 : ∀ a m Q X, solveSpec a m Q X →
      Γ "kissat_solve_bytes_m6" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    TableImpl Γ m6OrchTailFns (m6OrchTailSpecTable solveSpec) := by
  refine tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs =>
      wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m ?_⟩
    (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs =>
        wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m ?_⟩
      (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs =>
          wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m ?_⟩
        (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs =>
            wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m ?_⟩
          (tableImpl_cons ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _ hs =>
              wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m ?_⟩
            (tableImpl_nil Γ [])))))
  · exact full_search_m6_wp Γ hProp hAnalyze hReduce hSwitch hRstDue hRst hReorder hRephase
      hSimplify hDecide xs m Q (fun _ _ _ _ => False) hs
  · exact kissat_solve_bytes_m6_core_wp Γ hMemInit hParse hPre hSearchM6 hExt hCheck xs m Q
      (fun _ _ _ _ => False) (hWeaken xs m Q (fun _ _ _ _ => False) hs)
  · exact full_preprocess_wp Γ hPre xs m Q (fun _ _ _ _ => False) hs
  · exact full_search_wp Γ hSearchM6 xs m Q (fun _ _ _ _ => False) hs
  · exact kissat_solve_bytes_core_wp Γ solveSpec hSolveM6 xs m Q (fun _ _ _ _ => False) hs

/-- Assembles `ModuleOk` for `m6OrchModule` from any prefix `TableImpl` for `m6Orch_fns.take 24`
and callee lookups on `Env.ofTable (tPfx ++ m6OrchTailSpecTable solveSpec)`. -/
theorem mkM6OrchEnv_moduleOk
    (tPfx : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hWeaken : ∀ a m Q X, solveSpec a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hSolveMonoX : ∀ a m Q X X', solveSpec a m Q X → solveSpec a m Q X')
    (hPfxLen : (m6Orch_fns.take 24).length = tPfx.length)
    (hPfxNoTail : ∀ e ∈ tPfx, e.name ∉
      ["full_search_m6", "kissat_solve_bytes_m6", "full_preprocess",
       "full_search", "kissat_solve_bytes"])
    (hPfxNd : (tPfx.map SpecEntry.name).Nodup)
    (hPfxNoExit : tPfx.all SpecEntry.noExit = true)
    (hPfxOk : TableImpl (Env.ofTable (tPfx ++ m6OrchTailSpecTable solveSpec))
      (m6Orch_fns.take 24) tPfx)
    (hMemInit : ∀ a m Q X, fullM6MemInitExactSpec a m Q X →
      Env.ofTable (tPfx ++ m6OrchTailSpecTable solveSpec)
        "full_m6_mem_init" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hParse : ∀ a m Q X, Full.fullParseBodySpec a m Q X →
      Env.ofTable (tPfx ++ m6OrchTailSpecTable solveSpec)
        "full_parse_body" [i64, i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Env.ofTable (tPfx ++ m6OrchTailSpecTable solveSpec)
        "full_propagate" [i64] [i64] a m Q X)
    (hAnalyze : ∀ a m Q X, FullM6Hdr.m6HdrAnalyzeSpec a m Q X →
      Env.ofTable (tPfx ++ m6OrchTailSpecTable solveSpec)
        "full_analyze_m6_hdr" [i64] [i64] a m Q X)
    (hReduce : ∀ a m Q X, m6ReduceSpec a m Q X →
      Env.ofTable (tPfx ++ m6OrchTailSpecTable solveSpec)
        "full_reduce_m6" [i64, .bool] [i64] a m Q X)
    (hSwitch : ∀ a m Q X, m6SwitchModeSpec a m Q X →
      Env.ofTable (tPfx ++ m6OrchTailSpecTable solveSpec)
        "full_switch_mode_m6" [i64] [] a m Q X)
    (hRstDue : ∀ a m Q X, Full.fullRestartDueSpec a m Q X →
      Env.ofTable (tPfx ++ m6OrchTailSpecTable solveSpec)
        "full_restart_due" [i64] [i64] a m Q X)
    (hRst : ∀ a m Q X, Full.fullRestartSpec a m Q X →
      Env.ofTable (tPfx ++ m6OrchTailSpecTable solveSpec)
        "full_restart" [i64] [] a m Q X)
    (hReorder : ∀ a m Q X, FullM4.m4ReorderSpec a m Q X →
      Env.ofTable (tPfx ++ m6OrchTailSpecTable solveSpec)
        "full_reorder_m6" [i64, i64] [i64] a m Q X)
    (hRephase : ∀ a m Q X, m6aRephaseSpec a m Q X →
      Env.ofTable (tPfx ++ m6OrchTailSpecTable solveSpec)
        "full_rephase_m6_hdr" [i64] [] a m Q X)
    (hPre : ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Env.ofTable (tPfx ++ m6OrchTailSpecTable solveSpec)
        "full_preprocess_m6" [i64] [i64] a m Q X)
    (hSimplify : ∀ a m Q X, fullM6SimplifySpec a m Q X →
      Env.ofTable (tPfx ++ m6OrchTailSpecTable solveSpec)
        "full_simplify_m6" [i64, .bool, .bool] [i64] a m Q X)
    (hDecide : ∀ a m Q X, FullM6Hdr.m6HdrDecideSpec a m Q X →
      Env.ofTable (tPfx ++ m6OrchTailSpecTable solveSpec)
        "m6_hdr_decide" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, Full.fullExtendSpec a m Q X →
      Env.ofTable (tPfx ++ m6OrchTailSpecTable solveSpec)
        "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Env.ofTable (tPfx ++ m6OrchTailSpecTable solveSpec)
        "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ModuleOk (Env.ofTable (tPfx ++ m6OrchTailSpecTable solveSpec)) m6OrchModule := by
  let tbl := tPfx ++ m6OrchTailSpecTable solveSpec
  have htail_nd : (List.map SpecEntry.name (m6OrchTailSpecTable solveSpec)).Nodup := by
    simp only [m6OrchTailSpecTable, List.map_cons, List.map_nil]
    decide
  have hnd : (tbl.map SpecEntry.name).Nodup := by
    rw [show tbl = tPfx ++ m6OrchTailSpecTable solveSpec from rfl, List.map_append]
    refine List.nodup_append.mpr ⟨hPfxNd, htail_nd, fun x hx y hy heq => ?_⟩
    rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
    rcases List.mem_map.mp hy with ⟨e', he', rfl⟩
    apply hPfxNoTail e he
    rw [heq]
    simp only [m6OrchTailSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he'
    rcases he' with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  have hnoExit : tbl.all SpecEntry.noExit = true :=
    tbl_all_noExit_append hPfxNoExit (m6OrchTailSpecTable_noExit solveSpec)
  have hSearchM6 : ∀ a m Q X, fullM6SearchSpec a m Q X →
      Env.ofTable tbl "full_search_m6" [i64] [i64] a m Q X := fun a m Q X hs =>
    env_ofTable_noExit_all hnoExit _ _ _ _ _ _ (fun _ _ _ _ => False) X
      (env_ofTable_row_at (idx := tPfx.length)
        (e := ⟨"full_search_m6", [i64], [i64], fullM6SearchSpec, true⟩)
        (by simp [tbl, m6OrchTailSpecTable]) hnd
        (fullM6SearchSpec_monoX (X' := fun _ _ _ _ => False) hs))
  have hSolveM6 : ∀ a m Q X, solveSpec a m Q X →
      Env.ofTable tbl "kissat_solve_bytes_m6" [i64, i64, i64, i64, i64] [i64] a m Q X :=
    fun a m Q X hs =>
      env_ofTable_noExit_all hnoExit _ _ _ _ _ _ (fun _ _ _ _ => False) X
        (env_ofTable_row_at (idx := tPfx.length + 1)
          (e := ⟨"kissat_solve_bytes_m6", [i64, i64, i64, i64, i64], [i64], solveSpec, true⟩)
          (by simp [tbl, m6OrchTailSpecTable]) hnd
          (hSolveMonoX a m Q X (fun _ _ _ _ => False) hs))
  refine moduleOk_of_two_segments m6Orch_acyclic
    (show m6OrchModule.fns = m6Orch_fns.take 24 ++ m6OrchTailFns from
      (List.take_append_drop 24 m6Orch_fns).symm)
    hPfxLen
    (allFns_take (allFns_of_mem m6Orch_fns_wf) 24)
    m6OrchTailFns_wf
    hPfxOk
    (m6Orch_tail_tableImpl (Env.ofTable tbl) solveSpec hWeaken hMemInit hParse hProp hAnalyze
      hReduce hSwitch hRstDue hRst hReorder hRephase hPre hSimplify hDecide hExt hCheck
      hSearchM6 hSolveM6)

end LeanQbe.T.Examples.Kissat.FullM6Orch
