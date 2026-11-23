module

public import LeanQbe.T.Examples.Kissat.DimacsLemmas
public import LeanQbe.T.Examples.Kissat.CorePlusHeurLemmas
public import LeanQbe.T.Examples.Kissat.CorePlusIngestLemmas1
public import LeanQbe.T.Examples.Kissat.CorePlusIngestLemmas
public import LeanQbe.T.Examples.Kissat.CorePlusPropLemmas
public import LeanQbe.T.Examples.Kissat.CorePlusMinimizeLemmas1
public import LeanQbe.T.Examples.Kissat.CorePlusMinimizeLemmas
public import LeanQbe.T.Examples.Kissat.CorePlusAnalyzeLemmas1
public import LeanQbe.T.Examples.Kissat.CorePlusAnalyzeLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# End-to-End Kissat `D-Core+` `kissat_solve_bytes` Verification & Non-Vacuity

Proves:
1. `kissat_solve_bytes_core_wp` / `kissat_solve_bytes_wp`: full termination (`h->fuel.toNat`
   variant), read-only `[cnf_ptr, cnf_ptr + cnf_len)`, restored `region work_ptr work_len`,
   return code `r ∈ {0, 10, 20}`, restart `kissat_backtrack(0)`, `kissat_decide`, mandatory
   `kissat_check_model` SAT gate, UNSAT soundness (`r = 20 → ∃ cnf, parseDimacs = some cnf ∧
   cnf.Unsat`), SAT soundness (`r = 10 → ∃ cnf, parseDimacs = some cnf ∧ ¬ cnf.Unsat ∧
   ∃ α, cnf.Sat α`), and deterministic unit-clause witness traces.
2. Concrete UNSAT (`20#64`) and SAT (`10#64`) non-vacuity contracts and `1024`-byte workspace
   payload helpers (`corePlusPayload`, `corePlusPayload_sep`).
3. Closed 36-function `Env.ofTable` assembly (`mkCorePlusEnv_tableImpl`, `corePlusEnv_sound`,
   `corePlusEnv_noExit`, `corePlusEnv_moduleOk`, `solve_bytes_correct`) and source-level concrete
   non-vacuity theorems (`unsat_nonvacuous`, `sat_nonvacuous`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.CorePlus

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Pure DIMACS, bit-vector, and invariant-framing helpers -/

private theorem parseClauseAux_vars_pos {fuel mv : Nat} {acc : List (Literal Nat)}
    {bs rest : List UInt8} {cl : CNF.Clause Nat}
    (hacc : ∀ lit ∈ acc, 1 ≤ lit.1)
    (h : parseClauseAux fuel mv acc bs = some (cl, rest)) :
    ∀ lit ∈ cl.literals, 1 ≤ lit.1 := by
  induction fuel generalizing acc bs with
  | zero => simp [parseClauseAux] at h
  | succ fuel ih =>
    rw [parseClauseAux_eq_nextLitPure] at h
    cases hn : nextLitPure mv bs with
    | err => rw [hn] at h; cases h
    | endClause rest' =>
      rw [hn] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      intro lit hlit
      simp only [CNF.Clause.literals_ofLiterals, List.mem_reverse] at hlit
      exact hacc lit hlit
    | lit l rest' =>
      rw [hn] at h
      refine ih (fun lit hlit => ?_) h
      rcases List.mem_cons.mp hlit with rfl | hm
      · simp [kissatLitToDimacsLiteral]
      · exact hacc lit hm

private theorem parseClauses_vars_pos {mv : Nat} :
    ∀ {n : Nat} {acc : CNF Nat} {bs : List UInt8} {cnf : CNF Nat},
      CnfVarsPos acc → parseClauses mv n acc bs = some cnf → CnfVarsPos cnf
  | 0, acc, bs, cnf, hacc, h => by
    unfold parseClauses at h
    cases hsw : skipWsComments bs with
    | nil =>
      rw [hsw] at h; cases Option.some.inj h; exact hacc
    | cons _ _ => rw [hsw] at h; cases h
  | n + 1, acc, bs, cnf, hacc, h => by
    unfold parseClauses at h
    cases hpc : parseClause mv bs with
    | none => rw [hpc] at h; cases h
    | some p =>
      rcases p with ⟨cl, rest⟩
      rw [hpc] at h
      exact parseClauses_vars_pos (cnfVarsPos_add hacc (parseClauseAux_vars_pos (by simp) hpc)) h

private theorem parseDimacs_vars_pos {bs : List UInt8} {cnf : CNF Nat}
    (h : parseDimacs bs = some cnf) : CnfVarsPos cnf := by
  unfold parseDimacs at h
  cases hh : parseHeader bs with
  | none => rw [hh] at h; cases h
  | some p =>
    rcases p with ⟨mv, nc, rest⟩
    rw [hh] at h
    exact parseClauses_vars_pos (by intro _ hc; simp at hc) h

private theorem bv64_and7_eq_ofNat (p : BitVec 64) :
    p &&& 7 = BitVec.ofNat 64 (p.toNat % 8) := by
  apply BitVec.eq_of_toNat_eq
  have h := BitVec.toNat_and p 7
  have h7 : (7 : BitVec 64).toNat = 7 := rfl
  rw [h7, Nat.and_two_pow_sub_one_eq_mod p.toNat 3] at h
  rw [h, bv64_ofNat_toNat (by omega)]

private theorem corePlusInv_with_fuel {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    (hinv : CorePlusInv c F0 s) (f : BitVec 64) :
    CorePlusInv c F0 { s with fuel := f } :=
  ⟨{ hinv.core with
      lengths := { hinv.core.lengths with vals_len := hinv.core.lengths.vals_len }
      clauses := { hinv.core.clauses with bounds := hinv.core.clauses.bounds } },
    hinv.marks⟩

private theorem corePlusInv_with_rel_trigger {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    (hinv : CorePlusInv c F0 s) (v : BitVec 64) :
    CorePlusInv c F0 { s with heur := { s.heur with rel_trigger := v } } :=
  hinv.with_heur { hinv.core.lengths.heur_ok with }

/-! ## 2. Modular helpers for `kissat_solve_bytes` CDCL loop -/

local macro "cp_step" : tactic => `(tactic| (try (change wp _ _ _ _ _); c0_step))
local macro "cp_steps" : tactic => `(tactic| (try (change wp _ _ _ _ _); c0_steps))

/-- Alignment split & merge helpers for `work_ptr`, `pad = alignPad work_ptr`, `wlen`. -/
private theorem solve_bytes_merge_reg {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hw_ge : alignPad work_ptr ≤ wlen) {m' : Mem 64}
    (hm' : (bytes cnf_ptr cnfBytes ⋆
      region (work_ptr + BitVec.ofNat 64 (alignPad work_ptr)) (wlen - alignPad work_ptr) ⋆
      (region work_ptr (alignPad work_ptr) ⋆ R)) m') :
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' := by
  have h1 : ((region work_ptr (alignPad work_ptr) ⋆
      region (work_ptr + BitVec.ofNat 64 (alignPad work_ptr)) (wlen - alignPad work_ptr)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m' := sep_ac hm'
  have h2 : (region work_ptr (alignPad work_ptr + (wlen - alignPad work_ptr)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m' :=
    sep_mono (fun _ f => pad_region_merge (by omega) f) h1
  rw [show alignPad work_ptr + (wlen - alignPad work_ptr) = wlen by omega] at h2
  exact sep_ac h2

private theorem solve_bytes_merge_arena {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {c : CorePlusCfg} {st : CorePlusState}
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64) (hw_ge : alignPad work_ptr ≤ wlen)
    (hch : c.hdr = work_ptr + BitVec.ofNat 64 (alignPad work_ptr))
    (hca : c.avail = wlen - alignPad work_ptr) (hlen : st.LengthsOk c) {m' : Mem 64}
    (hm' : (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c st ⋆
      (region work_ptr (alignPad work_ptr) ⋆ R)) m') :
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' := by
  apply solve_bytes_merge_reg hwfit hw_ge
  have h1 : (CorePlusMem c st ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (alignPad work_ptr) ⋆ R)) m' := sep_ac hm'
  have h2 : (region (work_ptr + BitVec.ofNat 64 (alignPad work_ptr)) (wlen - alignPad work_ptr) ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (alignPad work_ptr) ⋆ R)) m' :=
    sep_mono (fun _ f => by rw [← hch, ← hca]; exact CorePlusArenaInv.to_region ⟨hlen, f⟩) h1
  exact sep_ac h2

/-- SAT fast-path predicate tracked across the main CDCL loop for deterministic unit SAT traces. -/
private def SatFastState (c : CorePlusCfg) (cnfBytes : List UInt8) (j0 : Nat)
    (fuel : BitVec 64) (st : CorePlusState) : Prop :=
  ∀ vals' te',
    te' < fuel.toNat →
    UnitSatTrace c.mv (List.replicate (2 * c.mv) 0#8) 0 (cnfBytes.drop j0) c.nc vals' te' →
    (∀ v < c.mv, vals'[2 * v]?.getD 0#8 ≠ 0#8) →
    runKissatCheckModel cnfBytes (vals'.map UInt8.ofBitVec) c.mv = true →
    st.vals = vals' ∧ st.trail_end = te' ∧ st.propagated = 0 ∧ st.cur_level = 0 ∧
    st.wh = List.replicate (2 * c.mv) 0xFFFFFFFF#32 ∧ st.fuel = fuel

/-- Postcondition at loop break (`B (res_v, ()) mb`) for `kissat_solve_bytes`. -/
private def SolveExitPost (c : CorePlusCfg) (cnf : CNF Nat) (cnf_ptr work_ptr fuel : BitVec 64)
    (cnfBytes : List UInt8) (j0 wlen : Nat) (R : Mem 64 → Prop)
    (res_v : BitVec 64) (mb : Mem 64) : Prop :=
  (res_v = 0#64 ∨ res_v = 10#64 ∨ res_v = 20#64) ∧
  (res_v = 20#64 → cnf.Unsat) ∧
  (res_v = 10#64 → ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
  (∀ vals' te', te' < fuel.toNat →
    UnitSatTrace c.mv (List.replicate (2 * c.mv) 0#8) 0 (cnfBytes.drop j0) c.nc vals' te' →
    (∀ v < c.mv, vals'[2 * v]?.getD 0#8 ≠ 0#8) →
    runKissatCheckModel cnfBytes (vals'.map UInt8.ofBitVec) c.mv = true →
    res_v = 10#64) ∧
  (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) mb

/-- Invariant on every back-edge to the CDCL loop head (`rem = st.fuel.toNat`). -/
private def SolveLoopInv (c : CorePlusCfg) (cnf : CNF Nat) (cnf_ptr work_ptr fuel : BitVec 64)
    (cnfBytes : List UInt8) (j0 : Nat) (R : Mem 64 → Prop)
    (rem : Nat) (ml : Mem 64) : Prop :=
  ∃ st : CorePlusState,
    rem = st.fuel.toNat ∧ CorePlusInv c (shiftDownCnf cnf) st ∧
    SatFastState c cnfBytes j0 fuel st ∧
    (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c st ⋆
      (region work_ptr (alignPad work_ptr) ⋆ R)) ml

/-- Post-`kissat_decide` check-model gate (`dst == 0`) for `kissat_solve_bytes`. -/
private theorem solve_bytes_check_model_step {Γ : Env} {Q : Post [i64]} {X : XPost}
    {B : Cont [i64]} {c : CorePlusCfg} {cnf : CNF Nat} {cnf_ptr work_ptr fuel : BitVec 64}
    {cnfBytes : List UInt8} {j0 wlen : Nat} {R : Mem 64 → Prop} {s3 : CorePlusState} {m3 : Mem 64}
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64) (hw_ge : alignPad work_ptr ≤ wlen)
    (hch : c.hdr = work_ptr + BitVec.ofNat 64 (alignPad work_ptr))
    (hca : c.avail = wlen - alignPad work_ptr)
    (hparse : parseDimacs cnfBytes = some cnf)
    (hlen3 : s3.LengthsOk c)
    (hsat3 : ∀ vals' te',
      te' < fuel.toNat →
      UnitSatTrace c.mv (List.replicate (2 * c.mv) 0#8) 0 (cnfBytes.drop j0) c.nc vals' te' →
      (∀ v < c.mv, vals'[2 * v]?.getD 0#8 ≠ 0#8) →
      runKissatCheckModel cnfBytes (vals'.map UInt8.ofBitVec) c.mv = true →
      s3.vals = vals')
    (hm3_b : (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s3 ⋆
      (region work_ptr (alignPad work_ptr) ⋆ R)) m3)
    (hB : ∀ res_v mb,
      SolveExitPost c cnf cnf_ptr work_ptr fuel cnfBytes j0 wlen R res_v mb →
      B (res_v, ()) mb) :
    wp Γ Q X (Expr.call (as := [i64, i64, i64, i64, i64]) (bs := [i64]) "kissat_check_model"
      (Arg.var cnf_ptr, Arg.var (cnf_ptr + BitVec.ofNat 64 cnfBytes.length),
        Arg.var c.hdr, Arg.var c.pVals, Arg.var (BitVec.ofNat 64 c.mv), ())
      fun p => Expr.group (sig := [[i64]])
        (fun _ => Blocks.cons (fun p1 => Expr.jump B (Arg.var p1.fst, ())) Blocks.nil)
        fun Js => Expr.let_
          { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
            args := (Arg.var p.fst, Arg.imm 1, ()) }
          fun p1 => Expr.jnz (Arg.var p1.fst)
            (Expr.jump Js.fst (Arg.imm 10, ())) (Expr.jump Js.fst (Arg.imm 0, ()))) m3 := by
  have hmv_bd := c.hmv; unfold dimacsBound at hmv_bd
  have hcm_mem := corePlusMem_to_checkModel hlen3 hm3_b
  c0_call hCheck
  refine ⟨BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc, s3.d_cur, s3.d_val,
    cnfBytes, s3.vals.map UInt8.ofBitVec, c.mv,
    CorePlusCheckRest c s3 ⋆ (region work_ptr (alignPad work_ptr) ⋆ R),
    rfl, rfl, hcfit, by omega,
    by simp [hlen3.vals_len], by simp [hlen3.vals_len]; omega,
    by simpa [sep_assoc] using hcm_mem, ?_⟩
  intro ok mv' nc' cur' val' m4 hok hm4
  have hm4_reg : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m4 :=
    solve_bytes_merge_reg hwfit hw_ge (by
      rw [← hch, ← hca]
      exact checkModel_post_to_region hlen3 (by simpa [sep_assoc] using hm4))
  refine wp_join_group
    (fun (res_v, ()) m5 => res_v = (if ok = 1#64 then 10#64 else 0#64) ∧ m5 = m4)
    (fun _ ⟨res_v, ⟨⟩⟩ m5 ⟨hres_v, hm5⟩ => by
      subst hres_v m5; c0_steps
      cases hrun : runKissatCheckModel cnfBytes (s3.vals.map UInt8.ofBitVec) c.mv with
      | false =>
        rw [hrun] at hok; simp only [Bool.false_eq_true, ↓reduceIte] at hok; subst hok
        refine hB 0#64 m4 ⟨Or.inl rfl, (fun h => by cases h), (fun h => by cases h), ?_, hm4_reg⟩
        intro vals' te' hte hst hnz hcm
        have hvs3 := hsat3 vals' te' hte hst hnz hcm
        rw [hvs3, hcm] at hrun; cases hrun
      | true =>
        rw [hrun] at hok; simp only [↓reduceIte] at hok; subst hok
        obtain ⟨cnf', _, hparse', _, hnu, hsat⟩ := runKissatCheckModel_sound hrun
        rw [hparse] at hparse'; have hce : cnf = cnf' := Option.some.inj hparse'; subst hce
        exact hB 10#64 m4 ⟨Or.inr (Or.inl rfl), (fun h => by cases h), fun _ => ⟨hnu, hsat⟩,
          fun _ _ _ _ _ _ => rfl, hm4_reg⟩)
    (fun Jr hJr => by
      c0_steps
      · exact hJr (10#64, ()) m4 ⟨by simp [hc], rfl⟩
      · exact hJr (0#64, ()) m4 ⟨by have hne : ok ≠ 1#64 := hc; simp [hne], rfl⟩)

/-- Main CDCL `while (true)` loop of `kissat_solve_bytes` after `kissat_parse_body` returns `1`. -/
private theorem solve_bytes_main_loop {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : CorePlusCfg} {cnf : CNF Nat} {cnf_ptr work_ptr fuel : BitVec 64}
    {cnfBytes : List UInt8} {j0 : Nat} {R : Mem 64 → Prop} {s1 : CorePlusState} {m1 : Mem 64}
    (hinv1 : CorePlusInv c (shiftDownCnf cnf) s1)
    (hsf1 : SatFastState c cnfBytes j0 fuel s1)
    (hm1 : (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s1 ⋆
      (region work_ptr (alignPad work_ptr) ⋆ R)) m1)
    {body : Tup Cont [[]] → Expr Val Cont [i64]}
    (hbody : ∀ (L : Cont []) (rem : Nat) (ml : Mem 64)
      (_ih : ∀ n' m', n' < rem →
        SolveLoopInv c cnf cnf_ptr work_ptr fuel cnfBytes j0 R n' m' → L () m')
      (st : CorePlusState),
      rem = st.fuel.toNat → CorePlusInv c (shiftDownCnf cnf) st →
      SatFastState c cnfBytes j0 fuel st →
      (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c st ⋆
        (region work_ptr (alignPad work_ptr) ⋆ R)) ml →
      wp Γ Q X (body (L, ())) ml) :
    wp Γ Q X (Expr.group (sig := [[]])
      (fun Ls => Blocks.cons (fun _ => body Ls) Blocks.nil)
      fun Ls => Expr.jump Ls.fst ()) m1 := by
  refine wp_loop_group
    (fun rem () ml => SolveLoopInv c cnf cnf_ptr work_ptr fuel cnfBytes j0 R rem ml) ?_ ?_
  · rintro L rem ⟨⟩ ml ih ⟨st, hrem, hst_inv, hsf, hml⟩
    exact hbody L rem ml (fun n' m' hlt h => ih n' () m' hlt h) st hrem hst_inv hsf hml
  · intro L hL; cp_steps
    exact hL s1.fuel.toNat () m1 ⟨s1, rfl, hinv1, hsf1, hm1⟩

/-- Conflict branch (`pr == 1`) of one CDCL loop iteration (`level 0 → 20`, else `analyze`). -/
private theorem solve_bytes_pr1_step {Γ : Env} {Q : Post [i64]} {X : XPost}
    {B J2 : Cont [i64]} {c : CorePlusCfg} {cnf : CNF Nat} {cnf_ptr work_ptr fuel : BitVec 64}
    {cnfBytes : List UInt8} {j0 wlen : Nat} {R : Mem 64 → Prop} {st s2 : CorePlusState}
    {m2 : Mem 64}
    (hAnalyze : ∀ a m Q X, corePlusAnalyzeSpec a m Q X →
      Γ "kissat_analyze" [i64, i64] [i64] a m Q X)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64) (hw_ge : alignPad work_ptr ≤ wlen)
    (hch : c.hdr = work_ptr + BitVec.ofNat 64 (alignPad work_ptr))
    (hca : c.avail = wlen - alignPad work_ptr)
    (hcnf_pos : CnfVarsPos cnf) (hs2_inv : CorePlusInv c (shiftDownCnf cnf) s2)
    (hfuel_lt : s2.fuel.toNat < st.fuel.toNat) (hcid_lt : s2.confl_cid.toNat < s2.num_clauses)
    (hfals : ∀ l ∈ clauseLits s2 s2.confl_cid.toNat, s2.vals[l]?.getD 0#8 = 0xFF#8)
    (hsf_false : ∀ vals0 te0, te0 < fuel.toNat →
      UnitSatTrace c.mv (List.replicate (2 * c.mv) 0#8) 0 (cnfBytes.drop j0) c.nc vals0 te0 →
      (∀ v < c.mv, vals0[2 * v]?.getD 0#8 ≠ 0#8) →
      runKissatCheckModel cnfBytes (vals0.map UInt8.ofBitVec) c.mv = true → False)
    (hm2 : (CorePlusMem c s2 ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (alignPad work_ptr) ⋆ R)) m2)
    (hB : ∀ res_v mb,
      SolveExitPost c cnf cnf_ptr work_ptr fuel cnfBytes j0 wlen R res_v mb →
      B (res_v, ()) mb)
    (hJ2 : ∀ rv m_next, (∃ s_next : CorePlusState,
      s_next.fuel.toNat < st.fuel.toNat ∧ CorePlusInv c (shiftDownCnf cnf) s_next ∧
      SatFastState c cnfBytes j0 fuel s_next ∧
      (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s_next ⋆
        (region work_ptr (alignPad work_ptr) ⋆ R)) m_next) → J2 (rv, ()) m_next) :
    wp Γ Q X (Expr.let_
      { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var c.hdr, Arg.imm 160, ()) }
      fun p3 => Expr.load i64 (Arg.var p3.fst) fun ld =>
      Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                  args := (Arg.var ld, Arg.imm 0, ()) }
      fun p4 => Expr.jnz (Arg.var p4.fst) (Expr.jump B (Arg.imm 20, ()))
        (Expr.let_
          { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var c.hdr, Arg.imm 176, ()) }
          fun p5 => Expr.load i64 (Arg.var p5.fst) fun ld1 =>
          Expr.call (as := [i64, i64]) (bs := [i64]) "kissat_analyze"
            (Arg.var c.hdr, Arg.var ld1, ())
          fun p6 => Expr.let_
            { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
              args := (Arg.var p6.fst, Arg.imm 20, ()) }
            fun p7 => Expr.jnz (Arg.var p7.fst) (Expr.jump B (Arg.imm 20, ()))
              (Expr.let_
                { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool rfl,
                  args := (Arg.var p6.fst, Arg.imm 1, ()) }
                fun p8 => Expr.jnz (Arg.var p8.fst) (Expr.jump B (Arg.imm 0, ()))
                  (Expr.jump J2 (Arg.imm 0, ()))))) m2 := by
  have hm2_b : (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s2 ⋆
      (region work_ptr (alignPad work_ptr) ⋆ R)) m2 := sep_ac hm2
  have hcl_lt := hs2_inv.core.lengths.cur_level_lt
  cp_steps
  · have hcl0 : s2.cur_level = 0 := by c0_bound
    have huns := shiftDownCnf_unsat hcnf_pos
      (hs2_inv.core.level0_unsat_of_conflict hcl0 hcid_lt hfals)
    exact hB 20#64 m2 ⟨Or.inr (Or.inr rfl), fun _ => huns, (fun h => by cases h),
      fun v0 t0 h1 h2 h3 h4 => (hsf_false v0 t0 h1 h2 h3 h4).elim,
      solve_bytes_merge_arena hwfit hw_ge hch hca hs2_inv.core.lengths hm2_b⟩
  · c0_call hAnalyze
    refine ⟨c, shiftDownCnf cnf, s2,
      bytes cnf_ptr cnfBytes ⋆ region work_ptr (alignPad work_ptr) ⋆ R,
      rfl, hs2_inv, hcid_lt, hfals, hm2, ?_⟩
    intro ast vals3 lvl3 rsns3 trl3 te3 prop3 cl3 tc3 tl3 mrk3 tmp3 wh3 cls3 wn3 lpool3
      ll3 nc3 mstk3 mclr3 mcl3 mcf3 heur3 m3 s3 hlen3 _ hast20 hast1 hm3
    have hm3_b : (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s3 ⋆
        (region work_ptr (alignPad work_ptr) ⋆ R)) m3 := sep_ac hm3
    cp_steps
    · exact hB 20#64 m3 ⟨Or.inr (Or.inr rfl),
        fun _ => shiftDownCnf_unsat hcnf_pos (hast20 hc), (fun h => by cases h),
        fun v0 t0 h1 h2 h3 h4 => (hsf_false v0 t0 h1 h2 h3 h4).elim,
        solve_bytes_merge_arena hwfit hw_ge hch hca hlen3 hm3_b⟩
    · exact hB 0#64 m3 ⟨Or.inl rfl, (fun h => by cases h), (fun h => by cases h),
        fun v0 t0 h1 h2 h3 h4 => (hsf_false v0 t0 h1 h2 h3 h4).elim,
        solve_bytes_merge_arena hwfit hw_ge hch hca hlen3 hm3_b⟩
    · exact hJ2 0#64 m3 ⟨s3, hfuel_lt, hast1 hc,
        fun v0 t0 h1 h2 h3 h4 => (hsf_false v0 t0 h1 h2 h3 h4).elim, hm3_b⟩

/-- `kissat_decide` + SAT check-model gate inside the `pr == 0` branch of `kissat_solve_bytes`. -/
private theorem solve_bytes_decide_step {Γ : Env} {Q : Post [i64]} {X : XPost}
    {B J3 : Cont [i64]} {c : CorePlusCfg} {cnf : CNF Nat} {cnf_ptr work_ptr fuel : BitVec 64}
    {cnfBytes : List UInt8} {j0 wlen : Nat} {R : Mem 64 → Prop} {st s2' : CorePlusState}
    {m2 : Mem 64}
    (hDecide : ∀ a m Q X, corePlusDecideSpec a m Q X →
      Γ "kissat_decide" [i64] [i64] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64) (hw_ge : alignPad work_ptr ≤ wlen)
    (hch : c.hdr = work_ptr + BitVec.ofNat 64 (alignPad work_ptr))
    (hca : c.avail = wlen - alignPad work_ptr) (hparse : parseDimacs cnfBytes = some cnf)
    (hs2'_inv : CorePlusInv c (shiftDownCnf cnf) s2') (hfu_lt : s2'.fuel.toNat < st.fuel.toNat)
    (hsf_s2' : ∀ vals0 te0, te0 < fuel.toNat →
      UnitSatTrace c.mv (List.replicate (2 * c.mv) 0#8) 0 (cnfBytes.drop j0) c.nc vals0 te0 →
      (∀ v < c.mv, vals0[2 * v]?.getD 0#8 ≠ 0#8) →
      runKissatCheckModel cnfBytes (vals0.map UInt8.ofBitVec) c.mv = true →
      s2'.vals = vals0)
    (hm2 : (CorePlusMem c s2' ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (alignPad work_ptr) ⋆ R)) m2)
    (hB : ∀ res_v mb,
      SolveExitPost c cnf cnf_ptr work_ptr fuel cnfBytes j0 wlen R res_v mb →
      B (res_v, ()) mb)
    (hJ3 : ∀ rv m_next, (∃ s_next : CorePlusState,
      s_next.fuel.toNat < st.fuel.toNat ∧ CorePlusInv c (shiftDownCnf cnf) s_next ∧
      SatFastState c cnfBytes j0 fuel s_next ∧
      (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s_next ⋆
        (region work_ptr (alignPad work_ptr) ⋆ R)) m_next) → J3 (rv, ()) m_next) :
    let cnf_end := cnf_ptr + BitVec.ofNat 64 cnfBytes.length
    wp Γ Q X (Expr.call (as := [i64]) (bs := [i64]) "kissat_decide" (Arg.var c.hdr, ())
      fun p8 => Expr.let_
        { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
          args := (Arg.var p8.fst, Arg.imm 0, ()) }
        fun p9 => Expr.jnz (Arg.var p9.fst)
          (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                       args := (Arg.var c.hdr, Arg.imm 64, ()) }
            fun p10 => Expr.load i64 (Arg.var p10.fst) fun ld2 =>
            Expr.load i64 (Arg.var c.hdr) fun ld3 =>
            Expr.call (as := [i64, i64, i64, i64, i64]) (bs := [i64])
              "kissat_check_model"
              (Arg.var cnf_ptr, Arg.var cnf_end, Arg.var c.hdr,
                Arg.var ld2, Arg.var ld3, ())
            fun p11 => Expr.group (sig := [[i64]])
              (fun _ => Blocks.cons (fun p12 =>
                Expr.jump B (Arg.var p12.fst, ())) Blocks.nil)
              fun Js => Expr.let_
                { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                  args := (Arg.var p11.fst, Arg.imm 1, ()) }
                fun p12 => Expr.jnz (Arg.var p12.fst)
                  (Expr.jump Js.fst (Arg.imm 10, ()))
                  (Expr.jump Js.fst (Arg.imm 0, ())))
          (Expr.jump J3 (Arg.imm 0, ()))) m2 := by
  dsimp only
  c0_call hDecide
  refine ⟨c, shiftDownCnf cnf, s2',
    bytes cnf_ptr cnfBytes ⋆ region work_ptr (alignPad work_ptr) ⋆ R,
    rfl, hs2'_inv, hm2, ?_⟩
  intro dst vals3 lvl3 rsns3 trl3 te3 cl3 heur3 m3 s3 hs3_inv _ _ hdst0 hdst_all hm3
  have hm3_b : (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s3 ⋆
      (region work_ptr (alignPad work_ptr) ⋆ R)) m3 := sep_ac hm3
  cp_steps
  · exact solve_bytes_check_model_step hCheck hcfit hwfit hw_ge hch hca hparse
      hs3_inv.core.lengths
      (fun vals0 te0 hte hst hnz hcm => by
        have hvs2 := hsf_s2' vals0 te0 hte hst hnz hcm
        have hs3_eq := (hdst0 hc).1
        change vals3 = vals0; rw [hs3_eq]; exact hvs2)
      hm3_b hB
  · exact hJ3 0#64 m3 ⟨s3, hfu_lt, hs3_inv,
      fun vals0 te0 hte hst hnz hcm => by
        have hvs2 := hsf_s2' vals0 te0 hte hst hnz hcm
        have h0 := (hdst_all (by rw [hvs2]; exact hnz)).1
        exact absurd h0 hc,
      hm3_b⟩

/-- Non-conflict branch (`pr == 0`): fuel check/decrement, optional restart, or `decide` + check. -/
private theorem solve_bytes_pr0_step {Γ : Env} {Q : Post [i64]} {X : XPost}
    {B J2 : Cont [i64]} {c : CorePlusCfg} {cnf : CNF Nat} {cnf_ptr work_ptr fuel : BitVec 64}
    {cnfBytes : List UInt8} {j0 wlen : Nat} {R : Mem 64 → Prop} {st s2 : CorePlusState}
    {m2 : Mem 64}
    (hBacktrack : ∀ a m Q X, corePlusBacktrackSpec a m Q X →
      Γ "kissat_backtrack" [i64, i64] [] a m Q X)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64) (hw_ge : alignPad work_ptr ≤ wlen)
    (hch : c.hdr = work_ptr + BitVec.ofNat 64 (alignPad work_ptr))
    (hca : c.avail = wlen - alignPad work_ptr)
    (hs2_inv : CorePlusInv c (shiftDownCnf cnf) s2) (hfuel_le : s2.fuel.toNat ≤ st.fuel.toNat)
    (hsf_s2 : ∀ vals0 te0, te0 < fuel.toNat →
      UnitSatTrace c.mv (List.replicate (2 * c.mv) 0#8) 0 (cnfBytes.drop j0) c.nc vals0 te0 →
      (∀ v < c.mv, vals0[2 * v]?.getD 0#8 ≠ 0#8) →
      runKissatCheckModel cnfBytes (vals0.map UInt8.ofBitVec) c.mv = true →
      s2.vals = vals0 ∧ s2.cur_level = 0 ∧ s2.fuel.toNat = fuel.toNat - te0)
    (hm2 : (CorePlusMem c s2 ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (alignPad work_ptr) ⋆ R)) m2)
    (hB : ∀ res_v mb,
      SolveExitPost c cnf cnf_ptr work_ptr fuel cnfBytes j0 wlen R res_v mb →
      B (res_v, ()) mb)
    (hJ2 : ∀ rv m_next, (∃ s_next : CorePlusState,
      s_next.fuel.toNat < st.fuel.toNat ∧ CorePlusInv c (shiftDownCnf cnf) s_next ∧
      SatFastState c cnfBytes j0 fuel s_next ∧
      (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s_next ⋆
        (region work_ptr (alignPad work_ptr) ⋆ R)) m_next) → J2 (rv, ()) m_next)
    {decide_e : Tup Cont [[i64]] → Expr Val Cont [i64]}
    (hDec_wp : ∀ (J3 : Cont [i64]) (m_d : Mem 64),
      let s2' : CorePlusState := { s2 with fuel := s2.fuel - 1 }
      s2'.fuel.toNat < st.fuel.toNat → CorePlusInv c (shiftDownCnf cnf) s2' →
      (CorePlusMem c s2' ⋆
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr (alignPad work_ptr) ⋆ R)) m_d →
      (∀ rv m_next, (∃ s_next : CorePlusState,
        s_next.fuel.toNat < st.fuel.toNat ∧ CorePlusInv c (shiftDownCnf cnf) s_next ∧
        SatFastState c cnfBytes j0 fuel s_next ∧
        (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s_next ⋆
          (region work_ptr (alignPad work_ptr) ⋆ R)) m_next) → J3 (rv, ()) m_next) →
      wp Γ Q X (decide_e (J3, ())) m_d) :
    wp Γ Q X (Expr.let_
      { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var c.hdr, Arg.imm 168, ()) }
      fun p3 => Expr.load i64 (Arg.var p3.fst) fun ld =>
      Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                  args := (Arg.var ld, Arg.imm 0, ()) }
      fun p4 => Expr.jnz (Arg.var p4.fst) (Expr.jump B (Arg.imm 0, ()))
        (Expr.let_
          { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var c.hdr, Arg.imm 168, ()) }
          fun p5 => Expr.load i64 (Arg.var p5.fst) fun ld1 =>
          Expr.let_ { sig := [i64, i64], code := OpCode.sub i64,
                      args := (Arg.var ld1, Arg.imm 1, ()) }
          fun p6 => Expr.let_
            { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var c.hdr, Arg.imm 168, ()) }
            fun p7 => Expr.store (Arg.var p6.fst) (Arg.var p7.fst)
              (Expr.group (sig := [[i64]])
                (fun _ => Blocks.cons (fun p => Expr.jump J2 (Arg.var p.fst, ())) Blocks.nil)
                fun J3 => Expr.group (sig := [[]])
                  (fun _ => Blocks.cons (fun _ => decide_e J3) Blocks.nil)
                  fun Jd => Expr.let_
                    { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var c.hdr, Arg.imm 144, ()) }
                    fun p8 => Expr.load i64 (Arg.var p8.fst) fun ld2 =>
                    Expr.load i64 (Arg.var c.hdr) fun ld3 =>
                    Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
                                args := (Arg.var ld2, Arg.var ld3, ()) }
                    fun p9 => Expr.jnz (Arg.var p9.fst)
                      (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                   args := (Arg.var c.hdr, Arg.imm 160, ()) }
                        fun p10 => Expr.load i64 (Arg.var p10.fst) fun ld4 =>
                        Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
                                    args := (Arg.var ld4, Arg.imm 0, ()) }
                        fun p11 => Expr.jnz (Arg.var p11.fst)
                          (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                       args := (Arg.var c.hdr, Arg.imm 328, ()) }
                            fun p12 => Expr.load i64 (Arg.var p12.fst) fun ld5 =>
                            Expr.let_
                              { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool rfl,
                                args := (Arg.var ld5, Arg.imm 0, ()) }
                              fun p13 => Expr.jnz (Arg.var p13.fst)
                                (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                             args := (Arg.var c.hdr, Arg.imm 328, ()) }
                                  fun p14 => Expr.store (Arg.imm (t := i64) 0) (Arg.var p14.fst)
                                    (Expr.call (as := [i64, i64]) (bs := []) "kissat_backtrack"
                                      (Arg.var c.hdr, Arg.imm 0, ())
                                      fun _ => Expr.jump J3.fst (Arg.imm 0, ())))
                                (Expr.jump Jd.fst ()))
                          (Expr.jump Jd.fst ()))
                      (Expr.jump Jd.fst ())))) m2 := by
  have hm2_b : (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s2 ⋆
      (region work_ptr (alignPad work_ptr) ⋆ R)) m2 := sep_ac hm2
  cp_step; cp_step; cp_step
  · exact hB 0#64 m2 ⟨Or.inl rfl, (fun h => by cases h), (fun h => by cases h),
      (fun vals0 te0 hte hst hnz hcm => by
        have hrem := (hsf_s2 vals0 te0 hte hst hnz hcm).2.2
        have hfz2 : s2.fuel.toNat = 0 := by rw [hc]; rfl
        omega),
      solve_bytes_merge_arena hwfit hw_ge hch hca hs2_inv.core.lengths hm2_b⟩
  have hf2_pos : 0 < s2.fuel.toNat :=
    Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
  have hf2_sub : (s2.fuel - 1).toNat = s2.fuel.toNat - 1 := bv64_sub1_toNat hc
  cp_step; cp_step
  let s2' : CorePlusState := { s2 with fuel := s2.fuel - 1 }
  have hs2'_inv : CorePlusInv c (shiftDownCnf cnf) s2' := corePlusInv_with_fuel hs2_inv _
  have hfu_lt : s2'.fuel.toNat < st.fuel.toNat := by
    change (s2.fuel - 1).toNat < st.fuel.toNat; rw [hf2_sub]; omega
  refine wp_join_group
    (fun (rv, ()) m_next => ∃ s_next : CorePlusState,
      s_next.fuel.toNat < st.fuel.toNat ∧ CorePlusInv c (shiftDownCnf cnf) s_next ∧
      SatFastState c cnfBytes j0 fuel s_next ∧
      (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s_next ⋆
        (region work_ptr (alignPad work_ptr) ⋆ R)) m_next)
    (fun _ ⟨rv, ⟨⟩⟩ m_next h => by cp_steps; exact hJ2 rv m_next h)
    (fun J3 hJ3 => ?_)
  refine wp_join_group (fun () m_d => m_d = m)
    (fun _ ⟨⟩ m_d hmd => by
      subst hmd
      exact hDec_wp J3 m_d hfu_lt hs2'_inv (sep_ac hm) (fun rv mn h => hJ3 (rv, ()) mn h))
    (fun Jd hJd => by
      cp_steps
      · have hcl_pos : 0 < s2.cur_level := by
          have := hs2_inv.core.lengths.cur_level_lt; c0_bound
        c0_call hBacktrack
        refine ⟨c, shiftDownCnf cnf, { s2' with heur := { s2'.heur with rel_trigger := 0#64 } },
          bytes cnf_ptr cnfBytes ⋆ region work_ptr (alignPad work_ptr) ⋆ R,
          rfl, corePlusInv_with_rel_trigger hs2'_inv 0#64, Nat.zero_le _, sep_ac hm, ?_⟩
        intro vals3 lvl3 rsns3 te3 prop3 heur3 m3 s3 hs3_inv _ _ hm3
        cp_steps
        exact hJ3 (0#64, ()) m3 ⟨s3, hfu_lt, hs3_inv,
          fun vals0 te0 hte hst hnz hcm => by
            have hcl0 := (hsf_s2 vals0 te0 hte hst hnz hcm).2.1; omega,
          sep_ac hm3⟩
      · exact hJd () m rfl
      · exact hJd () m rfl
      · exact hJd () m rfl)

/-- One iteration of the CDCL `while (true)` loop body in `kissat_solve_bytes`. -/
private theorem solve_bytes_iter_body {Γ : Env} {Q : Post [i64]} {X : XPost}
    {B : Cont [i64]} {L : Cont []}
    {c : CorePlusCfg} {cnf : CNF Nat} {cnf_ptr work_ptr fuel : BitVec 64}
    {cnfBytes : List UInt8} {j0 wlen : Nat} {R : Mem 64 → Prop} {st : CorePlusState} {ml : Mem 64}
    (hProp : ∀ a m Q X, corePlusPropagateSpec a m Q X →
      Γ "kissat_propagate" [i64] [i64] a m Q X)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64) (hw_ge : alignPad work_ptr ≤ wlen)
    (hch : c.hdr = work_ptr + BitVec.ofNat 64 (alignPad work_ptr))
    (hca : c.avail = wlen - alignPad work_ptr)
    (hst_inv : CorePlusInv c (shiftDownCnf cnf) st)
    (hsf : SatFastState c cnfBytes j0 fuel st)
    (hml : (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c st ⋆
      (region work_ptr (alignPad work_ptr) ⋆ R)) ml)
    (hB : ∀ res_v mb,
      SolveExitPost c cnf cnf_ptr work_ptr fuel cnfBytes j0 wlen R res_v mb →
      B (res_v, ()) mb)
    (ih : ∀ n' m', n' < st.fuel.toNat →
      SolveLoopInv c cnf cnf_ptr work_ptr fuel cnfBytes j0 R n' m' → L () m')
    {pr1_e pr0_e : Tup Cont [[i64]] → Expr Val Cont [i64]}
    (hpr1_wp : ∀ (J2 : Cont [i64]) (s2 : CorePlusState) (m2 : Mem 64),
      CorePlusInv c (shiftDownCnf cnf) s2 → s2.fuel.toNat < st.fuel.toNat →
      s2.confl_cid.toNat < s2.num_clauses →
      (∀ l ∈ clauseLits s2 s2.confl_cid.toNat, s2.vals[l]?.getD 0#8 = 0xFF#8) →
      (∀ vals0 te0, te0 < fuel.toNat →
        UnitSatTrace c.mv (List.replicate (2 * c.mv) 0#8) 0 (cnfBytes.drop j0) c.nc vals0 te0 →
        (∀ v < c.mv, vals0[2 * v]?.getD 0#8 ≠ 0#8) →
        runKissatCheckModel cnfBytes (vals0.map UInt8.ofBitVec) c.mv = true → False) →
      (CorePlusMem c s2 ⋆ (bytes cnf_ptr cnfBytes ⋆ region work_ptr (alignPad work_ptr) ⋆ R)) m2 →
      (∀ rv m_next, (∃ s_next : CorePlusState,
        s_next.fuel.toNat < st.fuel.toNat ∧ CorePlusInv c (shiftDownCnf cnf) s_next ∧
        SatFastState c cnfBytes j0 fuel s_next ∧
        (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s_next ⋆
          (region work_ptr (alignPad work_ptr) ⋆ R)) m_next) → J2 (rv, ()) m_next) →
      wp Γ Q X (pr1_e (J2, ())) m2)
    (hpr0_wp : ∀ (J2 : Cont [i64]) (s2 : CorePlusState) (m2 : Mem 64),
      CorePlusInv c (shiftDownCnf cnf) s2 → s2.fuel.toNat ≤ st.fuel.toNat →
      (∀ vals0 te0, te0 < fuel.toNat →
        UnitSatTrace c.mv (List.replicate (2 * c.mv) 0#8) 0 (cnfBytes.drop j0) c.nc vals0 te0 →
        (∀ v < c.mv, vals0[2 * v]?.getD 0#8 ≠ 0#8) →
        runKissatCheckModel cnfBytes (vals0.map UInt8.ofBitVec) c.mv = true →
        s2.vals = vals0 ∧ s2.cur_level = 0 ∧ s2.fuel.toNat = fuel.toNat - te0) →
      (CorePlusMem c s2 ⋆ (bytes cnf_ptr cnfBytes ⋆ region work_ptr (alignPad work_ptr) ⋆ R)) m2 →
      (∀ rv m_next, (∃ s_next : CorePlusState,
        s_next.fuel.toNat < st.fuel.toNat ∧ CorePlusInv c (shiftDownCnf cnf) s_next ∧
        SatFastState c cnfBytes j0 fuel s_next ∧
        (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s_next ⋆
          (region work_ptr (alignPad work_ptr) ⋆ R)) m_next) → J2 (rv, ()) m_next) →
      wp Γ Q X (pr0_e (J2, ())) m2) :
    wp Γ Q X (Expr.jnz (Arg.imm true)
      (Expr.call (as := [i64]) (bs := [i64]) "kissat_propagate" (Arg.var c.hdr, ())
        fun p => Expr.let_
          { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
            args := (Arg.var p.fst, Arg.imm 2, ()) }
          fun p1 => Expr.jnz (Arg.var p1.fst) (Expr.jump B (Arg.imm 0, ()))
            (Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun _ => Expr.jump L ()) Blocks.nil)
              fun J2 => Expr.let_
                { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                  args := (Arg.var p.fst, Arg.imm 1, ()) }
                fun p2 => Expr.jnz (Arg.var p2.fst) (pr1_e J2) (pr0_e J2)))
      (Expr.jump B (Arg.imm 0, ()))) ml := by
  refine wp_jnz_of (fun _ => ?_) (fun h => by cases h)
  have hml_a : (CorePlusMem c st ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (alignPad work_ptr) ⋆ R)) ml := sep_ac hml
  c0_call hProp
  refine ⟨c, shiftDownCnf cnf, st,
    bytes cnf_ptr cnfBytes ⋆ region work_ptr (alignPad work_ptr) ⋆ R, rfl, hst_inv, hml_a, ?_⟩
  intro pr vals' lvl' rsns' trl' te' prop' wh' wn' cls' lpool' fuel' confl' heur' m2
    s2 hs2_inv hfuel_le _ _ _ hpr1 hpr_empty hm2
  have hm2_b : (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s2 ⋆
      (region work_ptr (alignPad work_ptr) ⋆ R)) m2 := sep_ac hm2
  have hsf_prop : ∀ vals0 te0, te0 < fuel.toNat →
      UnitSatTrace c.mv (List.replicate (2 * c.mv) 0#8) 0 (cnfBytes.drop j0) c.nc vals0 te0 →
      (∀ v < c.mv, vals0[2 * v]?.getD 0#8 ≠ 0#8) →
      runKissatCheckModel cnfBytes (vals0.map UInt8.ofBitVec) c.mv = true →
      pr = 0#64 ∧ s2.vals = vals0 ∧ s2.cur_level = 0 ∧ s2.fuel.toNat = fuel.toNat - te0 := by
    intro vals0 te0 hte hst hnz hcm
    obtain ⟨hvs, htes, hprs, hcls, hwhs, hfus⟩ := hsf vals0 te0 hte hst hnz hcm
    have hempty : ∀ l < 2 * c.mv, st.wh[l]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
      intro l hl; rw [hwhs, List.getElem?_replicate]; simp [hl]
    have hres := hpr_empty hempty (by rw [htes, hprs, hfus]; omega)
    exact ⟨hres.1, by change vals' = vals0; rw [hres.2.1, hvs], hcls,
      by change fuel'.toNat = _; rw [hres.2.2.2, htes, hprs, hfus]; omega⟩
  cp_step; cp_step
  · exact hB 0#64 m2 ⟨Or.inl rfl, (fun h => by cases h), (fun h => by cases h),
      (fun vals0 te0 hte hst hnz hcm => by
        have h0 := (hsf_prop vals0 te0 hte hst hnz hcm).1; rw [hc] at h0; cases h0),
      solve_bytes_merge_arena hwfit hw_ge hch hca hs2_inv.core.lengths hm2_b⟩
  refine wp_join_group
    (fun (_, ()) m_next => ∃ s_next : CorePlusState,
      s_next.fuel.toNat < st.fuel.toNat ∧ CorePlusInv c (shiftDownCnf cnf) s_next ∧
      SatFastState c cnfBytes j0 fuel s_next ∧
      (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s_next ⋆
        (region work_ptr (alignPad work_ptr) ⋆ R)) m_next)
    (fun _ ⟨_, ⟨⟩⟩ m_next ⟨s_next, hlt_next, hinv_next, hsf_next, hm_next⟩ => by
      cp_steps
      exact ih s_next.fuel.toNat m_next hlt_next ⟨s_next, rfl, hinv_next, hsf_next, hm_next⟩)
    (fun J2 hJ2 => ?_)
  cp_step; cp_step
  · obtain ⟨hfuel_lt, hcid_lt, hfals⟩ := hpr1 hc
    exact hpr1_wp J2 s2 m2 hs2_inv hfuel_lt hcid_lt hfals
      (fun vals0 te0 hte hst hnz hcm => by
        have h0 := (hsf_prop vals0 te0 hte hst hnz hcm).1; rw [hc] at h0; cases h0)
      hm2 (fun rv m_next h => hJ2 (rv, ()) m_next h)
  · exact hpr0_wp J2 s2 m2 hs2_inv hfuel_le
      (fun vals0 te0 hte hst hnz hcm => (hsf_prop vals0 te0 hte hst hnz hcm).2)
      hm2 (fun rv m_next h => hJ2 (rv, ()) m_next h)

/-! ## 3. Top-level `kissat_solve_bytes_core_wp` and `kissat_solve_bytes_wp` -/

private theorem solve_bytes_align_pad {work_ptr : BitVec 64} {m : Mem 64} {Jp : Cont [i64]}
    (hJp : ∀ xs m2, (match xs with | (pad_v, ()) => pad_v = BitVec.ofNat 64 (alignPad work_ptr) ∧
      m2 = m) → Jp xs m2) :
    ((work_ptr &&& 7) = 0 → Jp (0#64, ()) m) ∧
    (¬ (work_ptr &&& 7) = 0 → Jp (8 - (work_ptr &&& 7), ()) m) := by
  rw [bv64_and7_eq_ofNat work_ptr]
  have hmod0 :
      BitVec.ofNat 64 (work_ptr.toNat % 8) = (0 : BitVec 64) ↔ work_ptr.toNat % 8 = 0 := by
    constructor
    · intro h; have ht := congrArg BitVec.toNat h; rwa [bv64_ofNat_toNat (by omega)] at ht
    · intro h; rw [h]; rfl
  rw [hmod0]
  refine ⟨fun hm0 => hJp (0#64, ()) m ⟨by simp [alignPad, hm0], rfl⟩, fun hmne => ?_⟩
  have hsub : (8 : BitVec 64) - BitVec.ofNat 64 (work_ptr.toNat % 8) =
      BitVec.ofNat 64 (8 - work_ptr.toNat % 8) :=
    bv_sub_ofNat (a := 8) (b := work_ptr.toNat % 8) (by omega) (by decide)
  exact hJp _ m ⟨by rw [hsub]; simp [alignPad, hmne], rfl⟩

theorem kissat_solve_bytes_core_wp (Γ : Env)
    (hInit : ∀ a m Q X, corePlusInitStateSpec a m Q X →
      Γ "kissat_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hParse : ∀ a m Q X, corePlusParseBodySpec a m Q X →
      Γ "kissat_parse_body" [i64, i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, corePlusPropagateSpec a m Q X →
      Γ "kissat_propagate" [i64] [i64] a m Q X)
    (hAnalyze : ∀ a m Q X, corePlusAnalyzeSpec a m Q X →
      Γ "kissat_analyze" [i64, i64] [i64] a m Q X)
    (hBacktrack : ∀ a m Q X, corePlusBacktrackSpec a m Q X →
      Γ "kissat_backtrack" [i64, i64] [] a m Q X)
    (hDecide : ∀ a m Q X, corePlusDecideSpec a m Q X →
      Γ "kissat_decide" [i64] [i64] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ args m Q X, corePlusSolveBytesCoreSpec args m Q X →
      Func.wp Γ kissat_solve_bytes_body args m Q X := by
  rintro ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, ⟨⟩⟩ m Q X
    ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, hQ⟩
  unfold Func.wp kissat_solve_bytes_body; wp_unfold
  refine ⟨fun hf0 => ?_, fun hfne => ?_⟩
  · have hfz : fuel.toNat = 0 := by rw [hf0]; rfl
    exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h) (fun h => by cases h)
      (fun _ _ _ hpos => by omega) (fun _ _ _ _ _ hlt => by omega) hm
  have hfpos : 0 < fuel.toNat :=
    Nat.pos_of_ne_zero fun h0 => hfne (BitVec.eq_of_toNat_eq (by simpa using h0))
  have hnot0 : ~~~(0 : BitVec 64) = 0xFFFFFFFFFFFFFFFF#64 := rfl
  rw [hnot0, bv64_ugt_max_sub_false hcfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  rw [bv64_ugt_max_sub_false hwfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  let pNat : Nat := alignPad work_ptr
  have hp_lt8 : pNat < 8 := alignPad_lt8 work_ptr
  refine wp_join_group (fun (pad_v, ()) m2 => pad_v = BitVec.ofNat 64 pNat ∧ m2 = m) ?_ ?_
  · rintro _ ⟨pad_v, ⟨⟩⟩ m2 ⟨hpad_v, hm2⟩
    subst hpad_v m2; wp_unfold
    rw [show (360 : BitVec 64) = BitVec.ofNat 64 360 from rfl, bv_add_ofNat,
      bv_ult_eq (by omega) (by omega)]
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun hw_small => ?_, fun hw_ok => ?_⟩
    · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h) (fun h => by cases h)
        (fun mv nc _ _ hsz _ _ _ => by unfold cpFixedBytes at hsz; omega)
        (fun mv nc _ _ _ _ hsz _ _ _ _ => by unfold cpFixedBytes at hsz; omega) hm
    · let hdr_addr : BitVec 64 := work_ptr + BitVec.ofNat 64 pNat
      let availNat : Nat := wlen - pNat
      have hav_eq : BitVec.ofNat 64 wlen - BitVec.ofNat 64 pNat = BitVec.ofNat 64 availNat :=
        bv64_sub_pad (by omega) (by omega)
      rw [hav_eq]
      have hhdr_fit : hdr_addr.toNat + availNat < 2 ^ 64 := by
        rw [bv_add_ofNat_toNat (by omega)]; omega
      have hsplit : (bytes cnf_ptr cnfBytes ⋆
          region hdr_addr availNat ⋆ (region work_ptr pNat ⋆ R)) m := by
        have h1 : (region work_ptr wlen ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
        rw [← region_merge_eq (a := work_ptr) (n1 := pNat) (n2 := availNat) (n := wlen)
          (by omega) (by omega)] at h1
        exact sep_ac h1
      c0_call hInit
      refine ⟨cnfBytes, region work_ptr pNat ⋆ R, rfl, hcfit,
        by simpa [hdr_addr, bv64_ofNat_toNat (by omega : availNat < 2 ^ 64)] using hhdr_fit,
        by rw [bv64_ofNat_toNat (by omega)]; omega,
        by simpa [bv64_ofNat_toNat (by omega : availNat < 2 ^ 64)] using hsplit, ?_, ?_⟩
      · intro m' hm' hfail
        wp_unfold
        have hm'_r : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' :=
          solve_bytes_merge_reg hwfit (by omega)
            (by simpa [bv64_ofNat_toNat (by omega : availNat < 2 ^ 64)] using hm')
        refine hQ 0#64 m' (Or.inl rfl) (fun h => by cases h) (fun h => by cases h)
          (fun mv nc i0 _ hsz _ hhdr _ => by
            have hlt := hfail mv nc (cnfBytes.drop i0) hhdr
            rw [bv64_ofNat_toNat (by omega)] at hlt; omega)
          (fun mv nc i0 _ _ _ hsz _ hhdr _ _ _ => by
            have hlt := hfail mv nc (cnfBytes.drop i0) hhdr
            rw [bv64_ofNat_toNat (by omega)] at hlt; omega) hm'_r
      · intro c s0 j0 rest0 m0 hch hca0 hhdr0 hj0 hdrop0 hinv0 hdcur0
          _ hnc0 hte0 hpr0 hcl0 hfu0 _ _ hvals0 hwh0 _ hm0
        have hca : c.avail = availNat := by rw [hca0, bv64_ofNat_toNat (by omega)]
        wp_unfold; rw [← hch]
        c0_call hParse
        refine ⟨c, s0, cnf_ptr, cnfBytes, j0, region work_ptr pNat ⋆ R,
          rfl, rfl, hcfit, hj0, by rwa [hdrop0], hdcur0, hcl0, hte0, hpr0, hnc0, hinv0, hm0, ?_⟩
        intro pst s1 m1 hlen1 hpst_dom hfu1 _ hpst20 hpst1 hsat_tr huns_tr hm1
        c0_steps
        · refine hQ 0#64 m1 (Or.inl rfl) (fun h => by cases h) (fun h => by cases h)
            (fun mv nc i0 _ _ _ hhdr hut => by
              rw [hhdr0, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hhdr
              rcases hhdr with ⟨rfl, rfl, hre⟩
              have h20 := huns_tr (by rw [hvals0, hdrop0, hre]; exact hut)
              rw [hc] at h20; cases h20)
            (fun mv nc i0 vals' te' _ _ _ hhdr hst _ _ => by
              rw [hhdr0, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hhdr
              rcases hhdr with ⟨rfl, rfl, hre⟩
              have h1 := (hsat_tr vals' te' (by rw [hvals0, hdrop0, hre]; exact hst)).1
              rw [hc] at h1; cases h1)
            (solve_bytes_merge_arena hwfit (by omega) hch hca hlen1 hm1)
        · refine hQ 20#64 m1 (Or.inr (Or.inr rfl)) (fun _ => hpst20 hc)
            (fun h => by cases h) (fun _ _ _ _ _ _ _ _ => rfl)
            (fun mv nc i0 vals' te' _ _ _ hhdr hst _ _ => by
              rw [hhdr0, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hhdr
              rcases hhdr with ⟨rfl, rfl, hre⟩
              have h1 := (hsat_tr vals' te' (by rw [hvals0, hdrop0, hre]; exact hst)).1
              rw [hc] at h1; cases h1)
            (solve_bytes_merge_arena hwfit (by omega) hch hca hlen1 hm1)
        · have hpst_eq1 : pst = 1#64 := by
            rcases hpst_dom with h | h | h
            · exact absurd h (by assumption)
            · exact h
            · exact absurd h hc
          obtain ⟨cnf, hparse, hinv1, hcl1⟩ := hpst1 hpst_eq1
          have hcnf_pos : CnfVarsPos cnf := parseDimacs_vars_pos hparse
          have hnot_unsat_trace :
              ¬ UnitUnsatTrace c.mv (List.replicate (2 * c.mv) 0#8) (cnfBytes.drop j0) c.nc :=
            fun hut => by have h20 := huns_tr (by rwa [hvals0]); rw [hpst_eq1] at h20; cases h20
          have hsf1 : SatFastState c cnfBytes j0 fuel s1 := fun vals' te' _ hst _ _ => by
            obtain ⟨_, hvs, htes, hprs, _, hwhs⟩ := hsat_tr vals' te' (by rwa [hvals0])
            exact ⟨hvs, htes, hprs, hcl1, by rw [hwhs, hwh0], by rw [hfu1, hfu0]⟩
          have hB_exit : ∀ res_v mb,
              SolveExitPost c cnf cnf_ptr work_ptr fuel cnfBytes j0 wlen R res_v mb →
              J (res_v, ()) mb :=
            fun res_v mb ⟨hdom, hu, hs, hsf, hmb⟩ =>
              hJ (res_v, ()) mb (hQ res_v mb hdom (fun h20 => ⟨cnf, hparse, hu h20⟩)
                (fun h10 => ⟨cnf, hparse, hs h10⟩)
                (fun mv nc i0 _ _ _ hhdr hut => by
                  rw [hhdr0, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hhdr
                  rcases hhdr with ⟨rfl, rfl, hre⟩
                  exact absurd (by rwa [hdrop0, hre]) hnot_unsat_trace)
                (fun mv nc i0 vals' te' hte _ _ hhdr hst hnz hcm => by
                  rw [hhdr0, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hhdr
                  rcases hhdr with ⟨rfl, rfl, hre⟩
                  exact hsf vals' te' hte (by rwa [hdrop0, hre]) hnz hcm) hmb)
          refine solve_bytes_main_loop hinv1 hsf1 hm1 ?_
          intro L rem ml ih st hrem hst_inv hsf hml
          subst hrem
          refine solve_bytes_iter_body hProp hwfit (by omega) hch hca hst_inv hsf hml hB_exit ih
            ?_ ?_
          · intro J2 s2 m2 hs2 hflt hcid hfals hsfF hm2 hJ2
            exact solve_bytes_pr1_step hAnalyze hwfit (by omega) hch hca hcnf_pos hs2 hflt
              hcid hfals hsfF hm2 hB_exit hJ2
          · intro J2 s2 m2 hs2 hfle hsfs2 hm2 hJ2
            refine solve_bytes_pr0_step hBacktrack hwfit (by omega) hch hca hs2 hfle hsfs2 hm2
              hB_exit hJ2 ?_
            intro J3 m_d s2' hfu_lt hs2'_inv hm_d hJ3
            exact solve_bytes_decide_step hDecide hCheck hcfit hwfit (by omega) hch hca hparse
              hs2'_inv hfu_lt (fun v0 t0 h1 h2 h3 h4 => (hsfs2 v0 t0 h1 h2 h3 h4).1) hm_d hB_exit
              hJ3
  · intro Jp hJp; wp_unfold; exact solve_bytes_align_pad hJp

theorem kissat_solve_bytes_wp (Γ : Env)
    (hInit : ∀ a m Q X, corePlusInitStateSpec a m Q X →
      Γ "kissat_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hParse : ∀ a m Q X, corePlusParseBodySpec a m Q X →
      Γ "kissat_parse_body" [i64, i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, corePlusPropagateSpec a m Q X →
      Γ "kissat_propagate" [i64] [i64] a m Q X)
    (hAnalyze : ∀ a m Q X, corePlusAnalyzeSpec a m Q X →
      Γ "kissat_analyze" [i64, i64] [i64] a m Q X)
    (hBacktrack : ∀ a m Q X, corePlusBacktrackSpec a m Q X →
      Γ "kissat_backtrack" [i64, i64] [] a m Q X)
    (hDecide : ∀ a m Q X, corePlusDecideSpec a m Q X →
      Γ "kissat_decide" [i64] [i64] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ args m Q X, corePlusSolveBytesSpec args m Q X →
      Func.wp Γ kissat_solve_bytes_body args m Q X :=
  fun args m Q X h =>
    kissat_solve_bytes_core_wp Γ hInit hParse hProp hAnalyze hBacktrack hDecide hCheck
      args m Q X (corePlusSolveBytesCoreSpec_of_spec h)

/-! ## 4. Concrete UNSAT (`20#64`) and SAT (`10#64`) non-vacuity contracts (`1024`-byte work) -/

/-- Concrete UNSAT DIMACS input (`p cnf 1 2\n1 0\n-1 0\n`, 19 bytes). -/
def cpNvUnsatBytes : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 49, 32, 50, 10, 49, 32, 48, 10, 45, 49, 32, 48, 10]

/-- Parsed `Std.Sat.CNF Nat` for `cpNvUnsatBytes`. -/
def cpNvUnsatCnf : CNF Nat :=
  (CNF.empty.add (CNF.Clause.ofLiterals [(1, true)])).add (CNF.Clause.ofLiterals [(1, false)])

theorem parseDimacs_cpNvUnsatBytes : parseDimacs cpNvUnsatBytes = some cpNvUnsatCnf := rfl

/-- Concrete SAT DIMACS input (`p cnf 1 1\n1 0\n`, 14 bytes). -/
def cpNvSatBytes : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 49, 32, 49, 10, 49, 32, 48, 10]

/-- Parsed `Std.Sat.CNF Nat` for `cpNvSatBytes`. -/
def cpNvSatCnf : CNF Nat :=
  CNF.empty.add (CNF.Clause.ofLiterals [(1, true)])

theorem parseDimacs_cpNvSatBytes : parseDimacs cpNvSatBytes = some cpNvSatCnf := rfl

private theorem cpNvUnsat_header :
    parseHeader cpNvUnsatBytes = some (1, 2, cpNvUnsatBytes.drop 9) := by decide

private theorem cpNvUnsat_trace :
    UnitUnsatTrace 1 (List.replicate 2 0#8) (cpNvUnsatBytes.drop 9) 2 := by
  have hcl1 : parseClause 1 (cpNvUnsatBytes.drop 9) =
      some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral 0], cpNvUnsatBytes.drop 13) := rfl
  have hcl2 : parseClause 1 (cpNvUnsatBytes.drop 13) =
      some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral 1], [10]) := rfl
  exact UnitUnsatTrace.step (l := 0) (by decide) hcl1 (by decide)
    (UnitUnsatTrace.conflict (l := 1) (by decide) hcl2 (by decide) ⟨CNF.empty, rfl⟩)

private theorem cpNvSat_header :
    parseHeader cpNvSatBytes = some (1, 1, cpNvSatBytes.drop 9) := by decide

private theorem cpNvSat_trace :
    UnitSatTrace 1 (List.replicate 2 0#8) 0 (cpNvSatBytes.drop 9) 1 [1#8, 0xFF#8] 1 := by
  have hcl1 : parseClause 1 (cpNvSatBytes.drop 9) =
      some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral 0], [10]) := rfl
  have hdone : UnitSatTrace 1 [1#8, 0xFF#8] 1 [10] 0 [1#8, 0xFF#8] 1 :=
    UnitSatTrace.done (by decide)
  exact UnitSatTrace.step (l := 0) (by decide) hcl1 (by decide) (by simpa using hdone)

private theorem cpNvSat_checkModel :
    runKissatCheckModel cpNvSatBytes ([1#8, 0xFF#8].map UInt8.ofBitVec) 1 = true := by decide

/-- Concrete UNSAT witness contract (`cpNvUnsatBytes`, `work_len = 1024`, `fuel = 16`). -/
def corePlusUnsatWitnessSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q _ =>
    ∃ R : Mem 64 → Prop,
      cnf_len = BitVec.ofNat 64 cpNvUnsatBytes.length ∧ work_len = 1024#64 ∧ fuel = 16#64 ∧
      cnf_ptr.toNat + cpNvUnsatBytes.length < 2 ^ 64 ∧ work_ptr.toNat + 1024 < 2 ^ 64 ∧
      (bytes cnf_ptr cpNvUnsatBytes ⋆ region work_ptr 1024 ⋆ R) m ∧
      ∀ m', cpNvUnsatCnf.Unsat →
        (bytes cnf_ptr cpNvUnsatBytes ⋆ region work_ptr 1024 ⋆ R) m' → Q (20#64, ()) m'

theorem corePlusSolveBytesCoreSpec_of_unsatWitness
    {args : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : corePlusUnsatWitnessSpec args m Q X) : corePlusSolveBytesCoreSpec args m Q X := by
  obtain ⟨R, hcl, hwl, hfu, hcfit, hwfit, hm, hQ⟩ := h
  refine ⟨cpNvUnsatBytes, 1024, R, hcl, hwl, hcfit, hwfit, hm, fun r m' _ hu _ huns_w _ hm' => ?_⟩
  have hr20 : r = 20#64 :=
    huns_w 1 2 9 (by rw [hfu]; decide)
      (by unfold cpFixedBytes valsBytes markBytes u32VarBytes whBytes minDepthOf; decide)
      (by decide) cpNvUnsat_header cpNvUnsat_trace
  subst hr20
  obtain ⟨cnf, hparse, huns⟩ := hu rfl
  rw [parseDimacs_cpNvUnsatBytes] at hparse; cases Option.some.inj hparse
  exact hQ m' huns hm'

/-- Concrete SAT witness contract (`cpNvSatBytes`, `work_len = 1024`, `fuel = 16`). -/
def corePlusSatWitnessSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q _ =>
    ∃ R : Mem 64 → Prop,
      cnf_len = BitVec.ofNat 64 cpNvSatBytes.length ∧ work_len = 1024#64 ∧ fuel = 16#64 ∧
      cnf_ptr.toNat + cpNvSatBytes.length < 2 ^ 64 ∧ work_ptr.toNat + 1024 < 2 ^ 64 ∧
      (bytes cnf_ptr cpNvSatBytes ⋆ region work_ptr 1024 ⋆ R) m ∧
      ∀ m', ¬ cpNvSatCnf.Unsat → (∃ α, cpNvSatCnf.Sat α) →
        (bytes cnf_ptr cpNvSatBytes ⋆ region work_ptr 1024 ⋆ R) m' → Q (10#64, ()) m'

theorem corePlusSolveBytesCoreSpec_of_satWitness
    {args : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : corePlusSatWitnessSpec args m Q X) : corePlusSolveBytesCoreSpec args m Q X := by
  obtain ⟨R, hcl, hwl, hfu, hcfit, hwfit, hm, hQ⟩ := h
  refine ⟨cpNvSatBytes, 1024, R, hcl, hwl, hcfit, hwfit, hm, fun r m' _ _ hs _ hsat_w hm' => ?_⟩
  have hr10 : r = 10#64 :=
    hsat_w 1 1 9 [1#8, 0xFF#8] 1 (by rw [hfu]; decide)
      (by unfold cpFixedBytes valsBytes markBytes u32VarBytes whBytes minDepthOf; decide)
      (by decide) cpNvSat_header cpNvSat_trace
      (fun v hv => by rw [show v = 0 by omega]; decide) cpNvSat_checkModel
  subst hr10
  obtain ⟨cnf, hparse, hnu, hsat⟩ := hs rfl
  rw [parseDimacs_cpNvSatBytes] at hparse; cases Option.some.inj hparse
  exact hQ m' hnu hsat hm'

abbrev corePlusNvCnfPtr : BitVec 64 := 0x1000#64
abbrev corePlusNvWorkPtr (cnfBytes : List UInt8) : BitVec 64 :=
  corePlusNvCnfPtr + BitVec.ofNat 64 cnfBytes.length

def corePlusPayload (cnfBytes : List UInt8) : List UInt8 :=
  cnfBytes ++ List.replicate 1024 0

theorem corePlusPayload_length (cnfBytes : List UInt8) :
    (corePlusPayload cnfBytes).length = cnfBytes.length + 1024 := by
  simp only [corePlusPayload, List.length_append, List.length_replicate]

theorem corePlusPayload_sep (cnfBytes : List UInt8) (hcb : cnfBytes.length ≤ 4096) :
    (bytes corePlusNvCnfPtr cnfBytes ⋆ region (corePlusNvWorkPtr cnfBytes) 1024)
      ((corePlusPayload cnfBytes).At corePlusNvCnfPtr) := by
  have h1024 : (List.replicate 1024 (0 : UInt8)).length = 1024 := List.length_replicate
  have h1 := Mem.At_append_sep cnfBytes (List.replicate 1024 0) corePlusNvCnfPtr
    (by simp only [h1024]; omega)
  have h0 : (Eq ((cnfBytes ++ List.replicate 1024 0).At corePlusNvCnfPtr))
      ((corePlusPayload cnfBytes).At corePlusNvCnfPtr) := rfl
  rw [h1] at h0
  exact sep_mono_r (fun _ hfW => ⟨List.replicate 1024 0, h1024, hfW.symm⟩) h0

/-! ## 5. Closed 36-function `Env.ofTable` assembly, `ModuleOk`, and non-vacuity -/

private theorem coreplusFns_nodup : (coreplusFns.map Fn.name).Nodup := by
  have hchk := coreplus_acyclic
  simp only [coreplusModule, Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

private theorem corePlusSpecTable_nodup
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((corePlusSpecTable mainSpec).map SpecEntry.name).Nodup := by
  have h : (corePlusSpecTable mainSpec).map SpecEntry.name = coreplusFns.map Fn.name := rfl
  rw [h]
  exact coreplusFns_nodup

private theorem mkCorePlusEnv_row {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (e : SpecEntry)
    (he : e ∈ corePlusSpecTable mainSpec := by
      simp only [corePlusSpecTable, List.mem_cons, true_or, or_true])
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkCorePlusEnv mainSpec e.name e.as e.rs xs m Q X :=
  fun xs m Q X h => Env.ofTable_of_mem he (corePlusSpecTable_nodup mainSpec) (hno xs m Q X h)

private theorem allFns_of_forall {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | _ :: _, h =>
      ⟨h _ List.mem_cons_self, allFns_of_forall fun f hf => h f (List.mem_cons_of_mem _ hf)⟩

/-- Row-by-row `TableImpl` for all 36 functions in `coreplusFns` (`dimacs_fns ++ coreplus_fns`)
against `corePlusSpecTable mainSpec` (zero N-way `rcases`). -/
theorem mkCorePlusEnv_tableImpl
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ args m Q X, mainSpec args m Q X → corePlusSolveBytesCoreSpec args m Q X) :
    TableImpl (mkCorePlusEnv mainSpec) coreplusFns (corePlusSpecTable mainSpec) := by
  let Γ := mkCorePlusEnv mainSpec
  let hWs := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_is_ws", [i64], [.bool], kissatIsWsSpec, true⟩
  let hDig := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_is_digit", [i64], [.bool], kissatIsDigitSpec, true⟩
  let hSwc := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, true⟩
  let hWs1 := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_skip_ws1", [i64, i64], [.bool], kissatSkipWs1Spec, true⟩
  let hNat := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_read_nat", [i64, i64], [.bool], kissatReadNatSpec, true⟩
  let hHdr := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩
  let hLit := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_next_lit", [i64, i64], [i64], kissatNextLitSpec, true⟩
  let hCheck := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩
  let hSiftUp := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_heap_sift_up", [i64, i32], [], corePlusHeapSiftUpSpec, true⟩
  let hSiftDown := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_heap_sift_down", [i64, i32], [], corePlusHeapSiftDownSpec, true⟩
  let hHeapPush := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_heap_push", [i64, i32], [], corePlusHeapPushSpec, true⟩
  let hPopMax := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_heap_pop_max", [i64], [i64], corePlusHeapPopMaxSpec, true⟩
  let hRescale := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_rescale_scores", [i64], [], corePlusRescaleScoresSpec, true⟩
  let hBump := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_bump_var", [i64, i32], [], corePlusBumpVarSpec, true⟩
  let hDecay := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_bump_decay", [i64], [], corePlusBumpDecaySpec, true⟩
  let hRel := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_tick_reluctant", [i64], [], corePlusTickReluctantSpec, true⟩
  let hAssign := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_assign", [i64, i32, i32], [], corePlusAssignSpec, true⟩
  let hAddWatch := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_add_watch", [i64, i32, i32], [], corePlusAddWatchSpec, true⟩
  let hAddCl := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_add_clause", [i64, i32], [i64], corePlusAddClauseSpec, true⟩
  let hBt := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_backtrack", [i64, i64], [], corePlusBacktrackSpec, true⟩
  let hZero := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_zero_tables", [i64], [], corePlusZeroTablesSpec, true⟩
  let hInit := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_init_state", [i64, i64, i64, i64, i64], [.bool], corePlusInitStateSpec, true⟩
  let hSkip := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_skip_clause_syntax", [i64, i64], [.bool], corePlusSkipClauseSyntaxSpec, true⟩
  let hIngest := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_ingest_clause", [i64, i64], [i64], corePlusIngestClauseSpec, true⟩
  let hParse := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_parse_body", [i64, i64], [i64], corePlusParseBodySpec, true⟩
  let hFind := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_find_repl", [i64, i64, i32, i32, i64], [i32], corePlusFindReplSpec, true⟩
  let hPropLit := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_propagate_lit", [i64, i32], [i64], corePlusPropagateLitSpec, true⟩
  let hProp := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_propagate", [i64], [i64], corePlusPropagateSpec, true⟩
  let hAc := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_analyze_clause", [i64, i32, i32], [.bool], corePlusAnalyzeClauseSpec, true⟩
  let hCm := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_clear_marks", [i64, i64], [], corePlusClearMarksSpec, true⟩
  let hMm := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_min_mark", [i64, i32, i8], [], corePlusMinMarkSpec, true⟩
  let hMl := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_minimize_lit", [i64, i32], [.bool], corePlusMinimizeLitSpec, true⟩
  let hMin := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_minimize_clause", [i64], [], corePlusMinimizeClauseSpec, true⟩
  let hAnalyze := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_analyze", [i64, i64], [i64], corePlusAnalyzeSpec, true⟩
  let hDecide := mkCorePlusEnv_row (mainSpec := mainSpec)
    ⟨"kissat_decide", [i64], [i64], corePlusDecideSpec, true⟩
  exact
    ⟨ .of (kissat_is_ws_wp Γ), .of (kissat_is_digit_wp Γ)
    , .of (kissat_skip_ws_comments_wp Γ hWs), .of (kissat_skip_ws1_wp Γ hWs)
    , .of (kissat_read_nat_wp Γ hDig hWs), .of (kissat_parse_header_wp Γ hSwc hWs1 hNat)
    , .of (kissat_next_lit_wp Γ hSwc hNat), .of (kissat_check_model_exact_wp Γ hHdr hLit hSwc)
    , .of (kissat_heap_sift_up_wp Γ), .of (kissat_heap_sift_down_wp Γ)
    , .of (kissat_heap_push_wp Γ hSiftUp), .of (kissat_heap_pop_max_wp Γ hSiftDown)
    , .of (kissat_rescale_scores_wp Γ), .of (kissat_bump_var_wp Γ hSiftUp hRescale)
    , .of (kissat_bump_decay_wp Γ hRescale), .of (kissat_tick_reluctant_wp Γ)
    , .of (kissat_assign_wp Γ), .of (kissat_add_watch_wp Γ)
    , .of (kissat_add_clause_wp Γ hAddWatch), .of (kissat_backtrack_wp Γ hHeapPush)
    , .of (kissat_zero_tables_wp Γ), .of (kissat_init_state_wp Γ hHdr hZero)
    , .of (kissat_skip_clause_syntax_wp Γ hLit)
    , .of (kissat_ingest_clause_wp Γ hLit hAssign hAddCl)
    , .of (kissat_parse_body_wp Γ hSkip hIngest hSwc)
    , .of (kissat_find_repl_wp Γ), .of (kissat_propagate_lit_wp Γ hFind hAssign)
    , .of (kissat_propagate_wp Γ hPropLit), .of (kissat_analyze_clause_wp Γ)
    , .of (kissat_clear_marks_wp Γ), .of (kissat_min_mark_wp Γ)
    , .of (kissat_minimize_lit_wp Γ hMm), .of (kissat_min_clause_wp Γ hMm hMl)
    , .of (kissat_analyze_wp Γ hAc hCm hBump hDecay hMin hRel hBt hAddCl hAssign)
    , .of (kissat_decide_wp Γ hPopMax hAssign)
    , .of (fun args m Q X h =>
        kissat_solve_bytes_core_wp Γ hInit hParse hProp hAnalyze hBt hDecide hCheck
          args m Q X (hweaken args m Q X h))
    , trivial ⟩

theorem mkCorePlusEnv_sound
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ args m Q X, mainSpec args m Q X → corePlusSolveBytesCoreSpec args m Q X) :
    ∀ f ∈ coreplusFns, ∀ args m Q X,
      mkCorePlusEnv mainSpec f.name f.as f.rs args m Q X →
      Func.wp (mkCorePlusEnv mainSpec) f.body args m Q X :=
  Env.ofTable_sound coreplusFns_nodup (mkCorePlusEnv_tableImpl mainSpec hweaken)

theorem mkCorePlusEnv_noExit (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ f as bs xs m Q X X',
      mkCorePlusEnv mainSpec f as bs xs m Q X →
      mkCorePlusEnv mainSpec f as bs xs m Q X' :=
  Env.ofTable_noExit (corePlusSpecTable_noExit mainSpec)

theorem mkCorePlusEnv_moduleOk
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ args m Q X, mainSpec args m Q X → corePlusSolveBytesCoreSpec args m Q X) :
    ModuleOk (mkCorePlusEnv mainSpec) coreplusModule :=
  Env.ofTable_moduleOk coreplus_acyclic (allFns_of_forall coreplusFns_wf)
    (mkCorePlusEnv_tableImpl mainSpec hweaken)

theorem mkCorePlusEnv_solve_bytes (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hno : ∀ xs m Q X, mainSpec xs m Q X → mainSpec xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, mainSpec xs m Q X →
      mkCorePlusEnv mainSpec "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem
      (e := ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], mainSpec, true⟩)
      (by simp [corePlusSpecTable]) (corePlusSpecTable_nodup mainSpec) (hno xs m Q X h)

/-- Headline: every function in `coreplusFns` satisfies its contract in `corePlusEnv`. -/
theorem corePlusEnv_sound :
    ∀ f ∈ coreplusFns, ∀ args m Q X,
      corePlusEnv f.name f.as f.rs args m Q X →
      Func.wp corePlusEnv f.body args m Q X :=
  mkCorePlusEnv_sound corePlusSolveBytesSpec (fun _ _ _ _ => corePlusSolveBytesCoreSpec_of_spec)

/-- Every row in `corePlusEnv` ignores exit continuations (`Compiled.fnSpec_noExit_id`). -/
theorem corePlusEnv_noExit :
    ∀ f as bs xs m Q X X',
      corePlusEnv f as bs xs m Q X → corePlusEnv f as bs xs m Q X' :=
  mkCorePlusEnv_noExit corePlusSolveBytesSpec

/-- Headline: full 36-function `ModuleOk` for `coreplusModule` under `corePlusEnv`. -/
theorem corePlusEnv_moduleOk : ModuleOk corePlusEnv coreplusModule :=
  mkCorePlusEnv_moduleOk corePlusSolveBytesSpec (fun _ _ _ _ => corePlusSolveBytesCoreSpec_of_spec)

/-- Headline source-level correctness of `kissat_solve_bytes` under `corePlusEnv`:
returns `r ∈ {0, 10, 20}`, keeps `[cnf_ptr, cnf_ptr + cnf_len)` read-only, restores
`region work_ptr work_len`, and certifies UNSAT (`20`) and SAT (`10`). -/
theorem solve_bytes_correct
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp corePlusEnv kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  corePlusEnv_sound kissat_solve_bytes (by simp [coreplusFns, coreplus_fns]) _ m _ X
    (mkCorePlusEnv_solve_bytes corePlusSolveBytesSpec (fun _ _ _ _ h => h) _ m _ X
      ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm,
        fun _ _ hdom hu hs hm' => ⟨hdom, hu, hs, hm'⟩⟩)

/-- Closed 36-function environment for concrete UNSAT non-vacuity (`20#64`). -/
def cpUnsatEnv : Env := mkCorePlusEnv corePlusUnsatWitnessSpec

theorem cpUnsatEnv_sound :
    ∀ f ∈ coreplusFns, ∀ args m Q X,
      cpUnsatEnv f.name f.as f.rs args m Q X → Func.wp cpUnsatEnv f.body args m Q X :=
  mkCorePlusEnv_sound corePlusUnsatWitnessSpec
    (fun _ _ _ _ => corePlusSolveBytesCoreSpec_of_unsatWitness)

theorem cpUnsatEnv_noExit :
    ∀ f as bs xs m Q X X',
      cpUnsatEnv f as bs xs m Q X → cpUnsatEnv f as bs xs m Q X' :=
  mkCorePlusEnv_noExit corePlusUnsatWitnessSpec

theorem cpUnsatEnv_moduleOk : ModuleOk cpUnsatEnv coreplusModule :=
  mkCorePlusEnv_moduleOk corePlusUnsatWitnessSpec
    (fun _ _ _ _ => corePlusSolveBytesCoreSpec_of_unsatWitness)

/-- Headline source-level UNSAT non-vacuity: `kissat_solve_bytes` returns `20#64` and proves
`cpNvUnsatCnf.Unsat` on `cpNvUnsatBytes` with `work_len = 1024` and `fuel = 16`. -/
theorem unsat_nonvacuous :
    let m0 : Mem 64 := (corePlusPayload cpNvUnsatBytes).At corePlusNvCnfPtr
    Func.wp cpUnsatEnv kissat_solve_bytes_body
      (corePlusNvCnfPtr, BitVec.ofNat 64 cpNvUnsatBytes.length,
        corePlusNvWorkPtr cpNvUnsatBytes, 1024#64, 16#64, ()) m0
      (fun rs _ => rs = (20#64, ()) ∧ cpNvUnsatCnf.Unsat) (fun _ _ _ _ => False) := by
  apply cpUnsatEnv_sound kissat_solve_bytes (by simp [coreplusFns, coreplus_fns])
  exact mkCorePlusEnv_solve_bytes corePlusUnsatWitnessSpec (fun _ _ _ _ h => h) _ _ _ _
    ⟨emp, rfl, rfl, rfl, by decide, by decide,
      by rw [sep_emp]; exact corePlusPayload_sep cpNvUnsatBytes (by decide),
      fun _ hu _ => ⟨rfl, hu⟩⟩

/-- Closed 36-function environment for concrete SAT non-vacuity (`10#64`). -/
def cpSatEnv : Env := mkCorePlusEnv corePlusSatWitnessSpec

theorem cpSatEnv_sound :
    ∀ f ∈ coreplusFns, ∀ args m Q X,
      cpSatEnv f.name f.as f.rs args m Q X → Func.wp cpSatEnv f.body args m Q X :=
  mkCorePlusEnv_sound corePlusSatWitnessSpec
    (fun _ _ _ _ => corePlusSolveBytesCoreSpec_of_satWitness)

theorem cpSatEnv_noExit :
    ∀ f as bs xs m Q X X',
      cpSatEnv f as bs xs m Q X → cpSatEnv f as bs xs m Q X' :=
  mkCorePlusEnv_noExit corePlusSatWitnessSpec

theorem cpSatEnv_moduleOk : ModuleOk cpSatEnv coreplusModule :=
  mkCorePlusEnv_moduleOk corePlusSatWitnessSpec
    (fun _ _ _ _ => corePlusSolveBytesCoreSpec_of_satWitness)

/-- Headline source-level SAT non-vacuity: `kissat_solve_bytes` returns `10#64` and proves
`¬ cpNvSatCnf.Unsat ∧ ∃ α, cpNvSatCnf.Sat α` on `cpNvSatBytes` (`work_len = 1024`, `fuel = 16`). -/
theorem sat_nonvacuous :
    let m0 : Mem 64 := (corePlusPayload cpNvSatBytes).At corePlusNvCnfPtr
    Func.wp cpSatEnv kissat_solve_bytes_body
      (corePlusNvCnfPtr, BitVec.ofNat 64 cpNvSatBytes.length,
        corePlusNvWorkPtr cpNvSatBytes, 1024#64, 16#64, ()) m0
      (fun rs _ => rs = (10#64, ()) ∧ ¬ cpNvSatCnf.Unsat ∧ ∃ α, cpNvSatCnf.Sat α)
      (fun _ _ _ _ => False) := by
  apply cpSatEnv_sound kissat_solve_bytes (by simp [coreplusFns, coreplus_fns])
  exact mkCorePlusEnv_solve_bytes corePlusSatWitnessSpec (fun _ _ _ _ h => h) _ _ _ _
    ⟨emp, rfl, rfl, rfl, by decide, by decide,
      by rw [sep_emp]; exact corePlusPayload_sep cpNvSatBytes (by decide),
      fun _ hnu hsat _ => ⟨rfl, hnu, hsat⟩⟩

end LeanQbe.T.Examples.Kissat.CorePlus
