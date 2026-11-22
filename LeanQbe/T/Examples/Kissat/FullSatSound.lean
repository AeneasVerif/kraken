/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM5Proof
import LeanQbe.T.Examples.Kissat.DimacsLemmas
import LeanQbe.T.Examples.Kissat.FullParseInitLemmas3
import Kraken.Mem
import Kraken.Separation

/-!
# End-to-End UNSAT + SAT Soundness & Constructive Model Extraction (`FullSatSound`)

Zero-drag, purely additive post-hoc byte-level SAT + UNSAT soundness over the existing verified
`kissat_check_model` call at `FullM5Orch.lean:646` and `FullM4.lean:393`:

1. Generic acyclic `LeanQbe.T.ModuleOk.respec_tail` transporting any existing `ModuleOk Γ₀ M`
   to `ModuleOk Γ₁ M` when only the final top entrypoint specs change.
2. Constructive `readModelFromWork (m' : Mem 64) (work_ptr : BitVec 64) (v : Nat) : Bool`
   (indirecting through `h->values` at `work_ptr + fullAlignPad work_ptr + 64`, surviving
   `FullHdr` tail extensions) + framing lemma `readModelFromWork_frame` + exact pure bridge
   `runKissatCheckModel_sat_exact`.
3. Top-level specifications `fullSolveBytesSoundSpec` (existential UNSAT + SAT) and
   `fullSolveBytesModelSpec` (constructive framed `readModelFromWork` + UNSAT).
4. Parametric `(Γ : Env)` `Func.wp` proofs `kissat_solve_bytes_m5_model_wp` and
   `m4_kissat_solve_bytes_model_wp`, plus closed `m4SoundEnv_moduleOk`,
   `m4_solve_bytes_model_correct`, `m4_solve_bytes_sound_correct`, `m5SoundEnv_moduleOk`,
   `m5_solve_bytes_model_correct`, and `m5_solve_bytes_sound_correct`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-- Generic acyclic tail-respec transport: if `ModuleOk Γ₀ M` holds and `M.fns = pfx ++ tail`,
then any `Γ₁` that agrees with `Γ₀` on `pfx` and `M.externs` and certifies each `fn ∈ tail`
yields `ModuleOk Γ₁ M` without re-proving any function in `pfx`. -/
theorem ModuleOk.respec_tail {Γ₀ Γ₁ : Env} {M : Module} {pfx tail : List Fn}
    (hM₀ : ModuleOk Γ₀ M) (hsplit : M.fns = pfx ++ tail)
    (hAgree : ∀ f as bs, (f, as, bs) ∈ pfx.map Fn.sig ++ M.externs.map Extern.sig →
      ∀ xs m Q X, Γ₀ f as bs xs m Q X ↔ Γ₁ f as bs xs m Q X)
    (hTail : ∀ fn ∈ tail, ∀ xs m Q X,
      Γ₁ fn.name fn.as fn.rs xs m Q X → Func.wp Γ₁ fn.body xs m Q X) :
    ModuleOk Γ₁ M := by
  refine ⟨hM₀.nodup, fun pre fn post hfn => ?_⟩
  have ⟨hwf, hcalls, hwp₀⟩ := hM₀.fnsOk pre fn post hfn
  refine ⟨hwf, hcalls, ?_⟩
  have heq : pre ++ fn :: post = pfx ++ tail := hfn.symm.trans hsplit
  by_cases hlt : pre.length < pfx.length
  · have hfn_get : pfx[pre.length]? = some fn := by
      have h1 := congrArg (fun l => l[pre.length]?) heq
      simpa [List.getElem?_append_left hlt] using h1.symm
    have hfn_pfx : fn ∈ pfx := List.mem_of_getElem? hfn_get
    have hpre_sub : ∀ x ∈ pre, x ∈ pfx := fun x hx => by
      have htk := congrArg (List.take pre.length) heq
      rw [List.take_left, List.take_append_of_le_length (Nat.le_of_lt hlt)] at htk
      rw [htk] at hx; exact List.mem_of_mem_take hx
    intro xs m Q X hs₁
    have hs₀ : Γ₀ fn.name fn.as fn.rs xs m Q X :=
      (hAgree fn.name fn.as fn.rs
        (List.mem_append_left _ (List.mem_map_of_mem hfn_pfx)) xs m Q X).mpr hs₁
    refine wp_env_agree_of_callsOk
      (hwf Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units fn.as)) hcalls
      (fun g as bs hg ys m' P E hG => (hAgree g as bs ?_ ys m' P E).mp hG) m (hwp₀ xs m Q X hs₀)
    rcases List.mem_append.mp hg with hp | he
    · obtain ⟨f', hf', hsig⟩ := List.mem_map.mp hp
      exact List.mem_append_left _ (hsig ▸ List.mem_map_of_mem (hpre_sub f' hf'))
    · exact List.mem_append_right _ he
  · have hge : pfx.length ≤ pre.length := Nat.le_of_not_lt hlt
    have hfn_tail : fn ∈ tail := by
      have h1 := congrArg (fun l => l[pre.length]?) heq
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, List.getElem?_append_right hge] at h1
      exact List.mem_of_getElem? h1.symm
    exact hTail fn hfn_tail

end LeanQbe.T

namespace LeanQbe.T.Examples.Kissat

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.Full hiding
  full_init_state_body full_init_state_wf
  full_reduce_body full_reduce_wf
  full_preprocess_body full_preprocess_wf
  full_search_body full_search_wf
  kissat_solve_bytes_body kissat_solve_bytes_full_wf
  full_add_bin_body full_add_bin_wf
open Kraken.Bedrock2.Test

/-! ## 1. Constructive `readModelFromWork` & Pure `runKissatCheckModel` Exactness Bridge -/

/-- Read the 1-based DIMACS variable `v`'s Boolean assignment from workspace memory `m'` at
`work_ptr`, indirecting through `h->values` at `work_ptr + fullAlignPad work_ptr + 64`.
Survives future `FullHdr` tail extensions because `h->values` sits at fixed offset `64`. -/
def readModelFromWork (m' : Mem 64) (work_ptr : BitVec 64) (v : Nat) : Bool :=
  if v == 0 then false
  else
    match loadVal m' i64 (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) + 64#64) with
    | none => false
    | some vals_ptr =>
      match loadVal m' i8 (vals_ptr + BitVec.ofNat 64 (2 * (v - 1))) with
      | none => false
      | some b => i8BytePos (UInt8.ofBitVec b)

/-- Definitional unfolding of `readModelFromWork` (exported without `@[expose]`). -/
theorem readModelFromWork_eq (m' : Mem 64) (work_ptr : BitVec 64) (v : Nat) :
    readModelFromWork m' work_ptr v =
      if v == 0 then false
      else
        match loadVal m' i64 (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) + 64#64) with
        | none => false
        | some vals_ptr =>
          match loadVal m' i8 (vals_ptr + BitVec.ofNat 64 (2 * (v - 1))) with
          | none => false
          | some b => i8BytePos (UInt8.ofBitVec b) := by rfl

private theorem u8_ofBitVec_ofNat_toNat (b : UInt8) :
    UInt8.ofBitVec (BitVec.ofNat 8 b.toNat) = b := by
  have h : BitVec.ofNat 8 b.toNat = b.toBitVec := by
    apply BitVec.eq_of_toNat_eq
    simp
  rw [h]

/-- Framing lemma for `readModelFromWork`: whenever `h->values` points to `vals_ptr` and byte
`2 * (v - 1)` is mapped in `m'`, every framed superset memory `M` (`(Eq m' ⋆ F) M`) reads the
same Boolean assignment at variable `v`. -/
theorem readModelFromWork_frame {m' M : Mem 64} {F : Mem 64 → Prop} {work_ptr vals_ptr : BitVec 64}
    {v : Nat} {b : BitVec 8} (hM : (Eq m' ⋆ F) M)
    (hptr : loadVal m' i64 (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) + 64#64) =
      some vals_ptr)
    (hb : loadVal m' i8 (vals_ptr + BitVec.ofNat 64 (2 * (v - 1))) = some b) :
    readModelFromWork M work_ptr v = if v == 0 then false else i8BytePos (UInt8.ofBitVec b) := by
  unfold readModelFromWork
  split
  · rfl
  · rw [loadVal_frame hM hptr]; dsimp only; rw [loadVal_frame hM hb]

private theorem evalLitVals_implies_fn {l : Nat} {valsBytes : List UInt8}
    (h : evalLitVals valsBytes l = true) :
    (fun v => if v == 0 then false else i8BytePos (valsBytes.getD (2 * (v - 1)) 0))
      (kissatLitToDimacsLiteral l).1 = (kissatLitToDimacsLiteral l).2 := by
  unfold evalLitVals at h
  simp only [kissatLitToDimacsLiteral, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    beq_iff_eq, ↓reduceIte, Nat.add_sub_cancel]
  cases hs : litSign l
  · rw [hs] at h; simpa using h
  · rw [hs] at h; dsimp only at h
    unfold i8ByteNeg at h; unfold i8BytePos
    grind

private theorem checkClauseValsAux_sat_exact {fuel mv : Nat} {valsBytes : List UInt8}
    {sat sat' : Bool} {acc : List (Literal Nat)} {bs rest : List UInt8}
    (hacc_bd : ∀ lit ∈ acc, 1 ≤ lit.1 ∧ lit.1 ≤ mv)
    (hsat : sat = true → ∃ lit ∈ acc,
      (fun v => if v == 0 then false else i8BytePos (valsBytes.getD (2 * (v - 1)) 0)) lit.1 =
        lit.2)
    (h : checkClauseValsAux fuel mv valsBytes sat bs = some (sat', rest)) :
    ∃ cl, parseClauseAux fuel mv acc bs = some (cl, rest) ∧
      (∀ lit ∈ cl.literals, 1 ≤ lit.1 ∧ lit.1 ≤ mv) ∧
      (sat' = true →
        cl.Sat (fun v =>
          if v == 0 then false else i8BytePos (valsBytes.getD (2 * (v - 1)) 0))) := by
  induction fuel generalizing sat acc bs with
  | zero => simp [checkClauseValsAux] at h
  | succ fuel ih =>
    rw [checkClauseValsAux] at h
    rw [parseClauseAux_eq_nextLitPure]
    cases hn : nextLitPure mv bs with
    | err => rw [hn] at h; cases h
    | endClause rest' =>
      rw [hn] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine ⟨CNF.Clause.ofLiterals acc.reverse, rfl, ?_, fun ht => ?_⟩
      · intro lit hlit
        simp only [CNF.Clause.literals_ofLiterals, List.mem_reverse] at hlit
        exact hacc_bd lit hlit
      · obtain ⟨lit, hmem, heq⟩ := hsat ht
        rw [CNF.Clause.sat_iff_exists_mem_eq]
        exact ⟨lit, by rw [← CNF.Clause.mem_literals_iff]; simp [hmem], heq⟩
    | lit l rest' =>
      rw [hn] at h
      have ⟨hlt, _, _⟩ := nextLitPure_lit_bounds hn
      have hl_bd : 1 ≤ (kissatLitToDimacsLiteral l).1 ∧ (kissatLitToDimacsLiteral l).1 ≤ mv := by
        simp only [kissatLitToDimacsLiteral, litVar]; omega
      refine ih (fun lit hlit => ?_) (fun ht => ?_) h
      · rcases List.mem_cons.mp hlit with rfl | hmem
        · exact hl_bd
        · exact hacc_bd lit hmem
      · simp only [Bool.or_eq_true] at ht
        rcases ht with h1 | h2
        · obtain ⟨lit, hmem, heq⟩ := hsat h1
          exact ⟨lit, List.mem_cons_of_mem _ hmem, heq⟩
        · exact ⟨kissatLitToDimacsLiteral l, List.mem_cons_self, evalLitVals_implies_fn h2⟩

private theorem checkClausesVals_sat_exact {mv k : Nat} {valsBytes bs : List UInt8}
    {accCnf : CNF Nat}
    (hacc_bd : ∀ cl ∈ accCnf, ∀ lit ∈ cl.literals, 1 ≤ lit.1 ∧ lit.1 ≤ mv)
    (hacc_sat : accCnf.Sat
      (fun v => if v == 0 then false else i8BytePos (valsBytes.getD (2 * (v - 1)) 0)))
    (h : checkClausesVals mv valsBytes k bs = true) :
    ∃ cnf, parseClauses mv k accCnf bs = some cnf ∧
      (∀ cl ∈ cnf, ∀ lit ∈ cl.literals, 1 ≤ lit.1 ∧ lit.1 ≤ mv) ∧
      cnf.Sat (fun v => if v == 0 then false else i8BytePos (valsBytes.getD (2 * (v - 1)) 0)) := by
  induction k generalizing accCnf bs with
  | zero =>
    simp only [checkClausesVals] at h
    exact ⟨accCnf, by simp [parseClauses, h], hacc_bd, hacc_sat⟩
  | succ k ih =>
    simp only [checkClausesVals] at h
    cases hc : checkClauseValsAux (bs.length + 1) mv valsBytes false bs with
    | none => rw [hc] at h; cases h
    | some p =>
      rcases p with ⟨sat, rest⟩
      rw [hc] at h
      cases sat with
      | false => cases h
      | true =>
        obtain ⟨cl, hcl, hcl_bd, hcl_sat⟩ :=
          checkClauseValsAux_sat_exact (acc := []) (by simp) (by simp) hc
        have hpc : parseClause mv bs = some (cl, rest) := hcl
        have hadd_bd : ∀ c ∈ accCnf.add cl, ∀ lit ∈ c.literals, 1 ≤ lit.1 ∧ lit.1 ≤ mv := by
          intro c hc_mem lit hlit
          rcases CNF.mem_add.mp hc_mem with rfl | hmem
          · exact hcl_bd lit hlit
          · exact hacc_bd c hmem lit hlit
        have hadd_sat : (accCnf.add cl).Sat
            (fun v => if v == 0 then false else i8BytePos (valsBytes.getD (2 * (v - 1)) 0)) :=
          CNF.sat_add.mpr ⟨hcl_sat rfl, hacc_sat⟩
        obtain ⟨cnf, hpc', hbd', hsat'⟩ := ih hadd_bd hadd_sat h
        exact ⟨cnf, by simp [parseClauses, hpc, hpc'], hbd', hsat'⟩

/-- Exact constructive soundness of `runKissatCheckModel`: returns `cnf` with variable bounds
`1 ≤ lit.1 ≤ mv ≤ mv_max` and certifies satisfaction directly on the 1-based byte predicate. -/
theorem runKissatCheckModel_sat_exact {cnfBytes valsBytes : List UInt8} {mv_max : Nat}
    (h : runKissatCheckModel cnfBytes valsBytes mv_max = true) :
    ∃ cnf mv, parseDimacs cnfBytes = some cnf ∧ mv ≤ mv_max ∧
      (∀ cl ∈ cnf, ∀ lit ∈ cl.literals, 1 ≤ lit.1 ∧ lit.1 ≤ mv) ∧
      cnf.Sat (fun v => if v == 0 then false else i8BytePos (valsBytes.getD (2 * (v - 1)) 0)) := by
  unfold runKissatCheckModel at h
  cases hh : parseHeader cnfBytes with
  | none => rw [hh] at h; cases h
  | some p =>
    rcases p with ⟨mv, nc, rest⟩
    rw [hh] at h; dsimp only at h
    split at h
    · cases h
    · next hle =>
      obtain ⟨cnf, hcls, hbd, hsat⟩ :=
        checkClausesVals_sat_exact (accCnf := CNF.empty) (by simp) (by simp) h
      exact ⟨cnf, mv, by simp [parseDimacs, hh, hcls], by omega, hbd, hsat⟩

private theorem cnf_sat_congr {cnf : CNF Nat} {α β : Nat → Bool}
    (hEq : ∀ cl ∈ cnf, ∀ lit ∈ cl.literals, α lit.1 = β lit.1)
    (h : cnf.Sat α) : cnf.Sat β := by
  rw [CNF.sat_iff_all_mem_sat] at h ⊢
  intro cl hcl
  have hc := h cl hcl
  rw [CNF.Clause.sat_iff_exists_mem_eq] at hc ⊢
  obtain ⟨lit, hmem, hval⟩ := hc
  have hlit : lit ∈ cl.literals := CNF.Clause.mem_literals_iff.mpr hmem
  exact ⟨lit, hmem, (hEq cl hcl lit hlit).symm.trans hval⟩

/-- Direct witness from `cnf.Sat α` to `¬ cnf.Unsat ∧ ∃ α, cnf.Sat α`. -/
theorem cnf_not_unsat_of_sat {cnf : CNF Nat} {α : Nat → Bool} (h : cnf.Sat α) :
    ¬ cnf.Unsat ∧ ∃ β, cnf.Sat β :=
  ⟨fun hu => CNF.unsat_iff_not_sat.mp hu α h, α, h⟩

/-! ## 2. Top-Level UNSAT + SAT Specs (`fullSolveBytesSoundSpec`, `fullSolveBytesModelSpec`) -/

/-- Existential end-to-end UNSAT + SAT soundness specification for `kissat_solve_bytes`:
returns `0`, `10`, or `20`; `20` certifies `cnf.Unsat`; `10` certifies `¬ cnf.Unsat ∧ ∃ α,
cnf.Sat α`; preserves exact input/workspace framing. -/
def fullSolveBytesSoundSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, _fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
        Q (r, ()) m'

/-- Constructive end-to-end UNSAT + SAT model specification for `kissat_solve_bytes`:
returns `0`, `10`, or `20`; `20` certifies `cnf.Unsat`; `10` certifies that `readModelFromWork M
work_ptr` satisfies `cnf` in every framed superset memory `M` of `m'` (hence both in source
memory `m'` and in full machine memory `st.data.dmem`). -/
def fullSolveBytesModelSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, _fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
          ∀ (F : Mem 64 → Prop) (M : Mem 64), (Eq m' ⋆ F) M →
            cnf.Sat (readModelFromWork M work_ptr)) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
        Q (r, ()) m'

/-- Public introduction rule for `fullSolveBytesModelSpec` (avoids needing `@[expose]`). -/
theorem fullSolveBytesModelSpec_intro
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m)
    (hQ : ∀ r m',
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
      (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        ∀ (F : Mem 64 → Prop) (M : Mem 64), (Eq m' ⋆ F) M →
          cnf.Sat (readModelFromWork M work_ptr)) →
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
      Q (r, ()) m') :
    fullSolveBytesModelSpec
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ())
      m Q X :=
  ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, hQ⟩

/-- `fullSolveBytesModelSpec` refines `fullSolveBytesSoundSpec` (contravariantly on `Q`). -/
theorem fullSolveBytesModelSpec_of_soundSpec
    {a : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : fullSolveBytesSoundSpec a m Q X) : fullSolveBytesModelSpec a m Q X := by
  obtain ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm, hQ⟩ := h
  refine ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm, fun r m' hdom hu hsat hm' => ?_⟩
  refine hQ r m' hdom hu (fun h10 => ?_) hm'
  obtain ⟨cnf, hp, hmod⟩ := hsat h10
  have hsat_m' : cnf.Sat (readModelFromWork m' a.2.2.1) :=
    hmod emp m' (by rw [sep_emp])
  exact ⟨cnf, hp, cnf_not_unsat_of_sat hsat_m'⟩

/-! ## 3. Shared Extend + Verified Model-Check Postcondition Proof (`m5` & `m4`) -/

section SolveModelProofs

open scoped Full.FullArenaTactics

private theorem sat_parseClauses_vars_pos {mv : Nat} :
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
      exact sat_parseClauses_vars_pos
        (cnfVarsPos_add hacc (parseClauseAux_vars_pos (by simp) hpc)) h

private theorem sat_parseDimacs_vars_pos {bs : List UInt8} {cnf : CNF Nat}
    (h : parseDimacs bs = some cnf) : CnfVarsPos cnf := by
  unfold parseDimacs at h
  cases hh : parseHeader bs with
  | none => rw [hh] at h; cases h
  | some p =>
    rcases p with ⟨mv, nc, rest⟩
    rw [hh] at h
    exact sat_parseClauses_vars_pos (by intro _ hc; simp at hc) h

private theorem sat_bv64_ugt_max_sub_false {p : BitVec 64} {n : Nat}
    (hfit : p.toNat + n < 2 ^ 64) :
    ((0xFFFFFFFFFFFFFFFF#64 - p).ult (BitVec.ofNat 64 n)) = false := by
  have hp := p.isLt
  have hmax : (0xFFFFFFFFFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 64 - 1 := rfl
  have hsub : 0xFFFFFFFFFFFFFFFF#64 - p = BitVec.ofNat 64 (2 ^ 64 - 1 - p.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, hmax, bv64_ofNat_toNat (by omega)]; omega
  rw [hsub, bv_ult_eq (by omega) (by omega)]
  simp only [decide_eq_false_iff_not]; omega

private theorem sat_alignPad_bv_eq (p : BitVec 64) :
    (8 - (p &&& 7)) &&& 7 = BitVec.ofNat 64 (fullAlignPad p) := by
  apply BitVec.eq_of_toNat_eq
  rw [show ((8 : BitVec 64) - (p &&& 7)) &&& 7 = (8#64 - (p &&& 7#64)) &&& 7#64 from rfl,
    fullAlignPad_eq, bv64_ofNat_toNat (by have := fullAlignPad_lt8 p; omega)]

private theorem sat_merge_reg {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hw_ge : fullAlignPad work_ptr ≤ wlen) {m' : Mem 64}
    (hm' : (bytes cnf_ptr cnfBytes ⋆
      region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
        (wlen - fullAlignPad work_ptr) ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m') :
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' := by
  have h1 : ((region work_ptr (fullAlignPad work_ptr) ⋆
      region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
        (wlen - fullAlignPad work_ptr)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m' := sep_ac hm'
  have h2 : (region work_ptr (fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m' :=
    sep_mono (fun _ f => pad_region_merge (by omega) f) h1
  rw [show fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr) = wlen by omega] at h2
  exact sep_ac h2

private theorem sat_merge_arena {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {c : FullCfg} {st : FullState}
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64) (hw_ge : fullAlignPad work_ptr ≤ wlen)
    (hch : c.hdr = work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
    (hca : c.avail = wlen - fullAlignPad work_ptr) (hlen : st.LengthsOk c) {m' : Mem 64}
    (hm' : (bytes cnf_ptr cnfBytes ⋆ FullMem c st ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m') :
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' := by
  apply sat_merge_reg hwfit hw_ge
  have h1 : (FullMem c st ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m' := sep_ac hm'
  have h2 : (region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
      (wlen - fullAlignPad work_ptr) ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m' :=
    sep_mono (fun _ f => by rw [← hch, ← hca]; exact FullArenaInv.to_region ⟨hlen, f⟩) h1
  exact sep_ac h2

private def SatCheckRest (c : FullCfg) (s : FullState) (bva_bv : BitVec 64) : Mem 64 → Prop :=
  array64 (c.hdr + 32) ((Full.hdrTailWords c s).set 94 bva_bv) ⋆
  array (t := i8) c.pLitMark s.core.lit_mark ⋆ array (t := i8) c.pMark s.core.mrk ⋆
  FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
  FullScratchArrays c s.scratch ⋆ c.pad

private theorem sat_arr8 {a : BitVec 64} {xs : List (BitVec 8)} {n : Nat}
    (hn : xs.length = n) (hbd : n ≤ 2 ^ 64) (f : Mem 64) (hf : array (t := i8) a xs f) :
    region a n f := by
  simpa [Ty.bytes, Ty.size, i8, hn] using
    array_to_region (t := i8) (by simp [Ty.bytes, Ty.size, i8, hn, hbd]) hf

private theorem sat_arr32 (m : Nat) {a : BitVec 64} {xs : List (BitVec 32)} {n : Nat}
    (hn : xs.length = n) (hm : 4 * n = m) (hbd : m ≤ 2 ^ 64) (f : Mem 64)
    (hf : array (t := i32) a xs f) : region a m f := by
  simpa [Ty.bytes, Ty.size, i32, hn, hm] using
    array_to_region (t := i32) (by simp [Ty.bytes, Ty.size, i32, hn]; omega) hf

private theorem sat_arr64 (m : Nat) {a : BitVec 64} {xs : List (BitVec 64)} {n : Nat}
    (hn : xs.length = n) (hm : 8 * n = m) (hbd : m ≤ 2 ^ 64) (f : Mem 64)
    (hf : array64 a xs f) : region a m f := by
  simpa [Ty.bytes, Ty.size, i64, hn, hm] using
    array_to_region (t := i64) (xs := xs) (by simp [Ty.bytes, Ty.size, i64, hn]; omega)
      ((array64_eq_array a xs) ▸ hf)

private theorem sat_checkModel_post_to_region {c : FullCfg} {s : FullState}
    {bva_bv mv' nc' cur' val' : BitVec 64} {cnf_ptr : BitVec 64} {cnfBytes : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (hlen : s.LengthsOk c)
    (hm : (bytes cnf_ptr cnfBytes ⋆ dimacsState c.hdr mv' nc' cur' val' ⋆
      bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆ (SatCheckRest c s bva_bv ⋆ R)) m) :
    (bytes cnf_ptr cnfBytes ⋆ region c.hdr c.avail ⋆ R) m := by
  have hmx := c.hmaxv; have ha := c.harena; have hw := c.hwcap
  have hd := c.hdel; have hred := c.hred; have hext := c.hext; have hscr := c.hscr
  have hmd := fullMinDepthOf_le c.max_vars
  unfold dimacsBound at *
  have hc := hlen.core_ok; have hs := hlen.scratch_ok
  have h1 : ((bytes cnf_ptr cnfBytes ⋆ R) ⋆
      ((dimacsState c.hdr mv' nc' cur' val' ⋆
          array64 (c.hdr + 32) ((Full.hdrTailWords c s).set 94 bva_bv)) ⋆
        ((bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
            array (t := i8) c.pWalkVals s.scratch.walk_vals ⋆
            array (t := i8) c.pLitMark s.core.lit_mark) ⋆
          (array (t := i8) c.pMark s.core.mrk ⋆ array (t := i8) c.pPhases s.scratch.phases ⋆
            array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
            array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
            array (t := i8) c.pWalkBest s.scratch.walk_best)) ⋆
        (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
          array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
          array (t := i32) c.pTrailPos s.core.trail_pos) ⋆
        (array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pHeap s.scratch.heap ⋆
          array (t := i32) c.pPos s.scratch.pos ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
          array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆
        (array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
          array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
          array (t := i32) c.pFrameDec s.core.frame_dec) ⋆
        (array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr ⋆
          array (t := i32) c.pWsort s.scratch.wsort ⋆
          array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
          array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
          array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
          array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
          array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig) ⋆
        (array (t := i32) c.pMinStk s.core.min_stk ⋆
          array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
          array (t := i32) c.pLastLearned s.scratch.last_learned ⋆
          array (t := i32) c.pArena s.core.arena ⋆ array (t := i32) c.pWstk s.core.wstk ⋆
          array (t := i32) c.pDelayed s.scratch.delayed ⋆
          array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
          array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
          array (t := i32) c.pScratchBuf s.scratch.scratch_buf) ⋆
        c.pad)) m := by
    unfold SatCheckRest FullCoreU32A FullCoreU32B FullCoreDynArrs FullScratchArrays
      FullScrByteArrs FullScrU32A FullScrWksArrs FullScrMetaArrs FullScrDynArrs at hm
    exact sep_ac hm
  have hHead : ∀ k,
      (dimacsState c.hdr mv' nc' cur' val' ⋆
        array64 (c.hdr + 32) ((Full.hdrTailWords c s).set 94 bva_bv)) k →
      (region c.hdr 32 ⋆ region (c.hdr + BitVec.ofNat 64 32) 1120) k :=
    sep_mono2 (fun _ hb => dimacsState_to_region hb)
      (sat_arr64 1120 (by rw [List.length_set, Full.hdrTailWords_length])
        (by decide) (by decide))
  have hB : ∀ k,
      ((bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
          array (t := i8) c.pWalkVals s.scratch.walk_vals ⋆
          array (t := i8) c.pLitMark s.core.lit_mark) ⋆
        (array (t := i8) c.pMark s.core.mrk ⋆ array (t := i8) c.pPhases s.scratch.phases ⋆
          array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
          array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
          array (t := i8) c.pWalkBest s.scratch.walk_best)) k →
      ((region c.pVals (2 * c.max_vars) ⋆ region c.pWalkVals (2 * c.max_vars) ⋆
          region c.pLitMark (2 * c.max_vars)) ⋆
        (region c.pMark c.max_vars ⋆ region c.pPhases c.max_vars ⋆
          region c.pPhasesTarget c.max_vars ⋆ region c.pPhasesBest c.max_vars ⋆
          region c.pWalkBest c.max_vars)) k :=
    sep_mono2
      (sep_mono2
        (sep_mono2
          (fun x (hb : bytes c.pVals (s.core.vals.map UInt8.ofBitVec) x) => by
            have hb' := bytes_to_region hb; simpa [hc.vals_len] using hb')
          (sat_arr8 hs.walk_vals_len (by omega)))
        (sat_arr8 hc.lit_mark_len (by omega)))
      (sep_mono2
        (sep_mono2
          (sep_mono2 (sep_mono2 (sat_arr8 hc.mrk_len (by omega))
              (sat_arr8 hs.phases_len (by omega)))
            (sat_arr8 hs.phases_target_len (by omega)))
          (sat_arr8 hs.phases_best_len (by omega)))
        (sat_arr8 hs.walk_best_len (by omega)))
  have hU1 : ∀ k,
      (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) k →
      (region c.pFlags (4 * c.max_vars) ⋆ region c.pLevel (4 * c.max_vars) ⋆
        region c.pReason (4 * c.max_vars) ⋆ region c.pTrail (4 * c.max_vars) ⋆
        region c.pTrailPos (4 * c.max_vars)) k :=
    sep_mono2
      (sep_mono2
        (sep_mono2
          (sep_mono2 (sat_arr32 (4 * c.max_vars) hc.flags_len rfl (by omega))
            (sat_arr32 (4 * c.max_vars) hc.lvl_len rfl (by omega)))
          (sat_arr32 (4 * c.max_vars) hc.rsns_len rfl (by omega)))
        (sat_arr32 (4 * c.max_vars) hc.trl_len rfl (by omega)))
      (sat_arr32 (4 * c.max_vars) hc.trail_pos_len rfl (by omega))
  have hU2 : ∀ k,
      (array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pHeap s.scratch.heap ⋆
        array (t := i32) c.pPos s.scratch.pos ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
        array (t := i32) c.pShrinkStk s.scratch.shrink_stk) k →
      (region c.pTmp (4 * c.max_vars) ⋆ region c.pHeap (4 * c.max_vars) ⋆
        region c.pPos (4 * c.max_vars) ⋆ region c.pMinClr (4 * c.max_vars) ⋆
        region c.pShrinkStk (4 * c.max_vars)) k :=
    sep_mono2
      (sep_mono2
        (sep_mono2
          (sep_mono2 (sat_arr32 (4 * c.max_vars) hc.tmp_len_arr rfl (by omega))
            (sat_arr32 (4 * c.max_vars) hs.heap_len_arr rfl (by omega)))
          (sat_arr32 (4 * c.max_vars) hs.pos_len rfl (by omega)))
        (sat_arr32 (4 * c.max_vars) hc.min_clr_len_arr rfl (by omega)))
      (sat_arr32 (4 * c.max_vars) hs.shrink_stk_len rfl (by omega))
  have hU3 : ∀ k,
      (array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
        array (t := i32) c.pFrameDec s.core.frame_dec) k →
      (region c.pQPrev (4 * c.max_vars) ⋆ region c.pQNext (4 * c.max_vars) ⋆
        region c.pQStamp (4 * c.max_vars) ⋆ region c.pFrameTrail (4 * (c.max_vars + 1)) ⋆
        region c.pFrameDec (4 * (c.max_vars + 1))) k :=
    sep_mono2
      (sep_mono2
        (sep_mono2
          (sep_mono2 (sat_arr32 (4 * c.max_vars) hs.q_prev_len rfl (by omega))
            (sat_arr32 (4 * c.max_vars) hs.q_next_len rfl (by omega)))
          (sat_arr32 (4 * c.max_vars) hs.q_stamp_len rfl (by omega)))
        (sat_arr32 (4 * (c.max_vars + 1)) hc.frame_trail_len rfl (by omega)))
      (sat_arr32 (4 * (c.max_vars + 1)) hc.frame_dec_len rfl (by omega))
  have hT1 : ∀ k,
      (array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr ⋆
        array (t := i32) c.pWsort s.scratch.wsort ⋆
        array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
        array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
        array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
        array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
        array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig) k →
      (region c.pWvec (16 * c.max_vars) ⋆ region c.pRepr (8 * c.max_vars) ⋆
        region c.pWsort (8 * c.max_vars) ⋆ region c.pWorkStk1 (8 * c.max_vars) ⋆
        region c.pWorkStk2 (8 * c.max_vars) ⋆ region c.pTarjanMark (8 * c.max_vars) ⋆
        region c.pTarjanReach (8 * c.max_vars) ⋆ region c.pScore (8 * c.max_vars) ⋆
        region c.pSimSig (8 * c.max_vars)) k :=
    sep_mono2
      (sep_mono2
        (sep_mono2
          (sep_mono2
            (sep_mono2
              (sep_mono2
                (sep_mono2
                  (sep_mono2 (sat_arr32 (16 * c.max_vars) hc.wvec_len (by omega) (by omega))
                    (sat_arr32 (8 * c.max_vars) hc.repr_len (by omega) (by omega)))
                  (sat_arr32 (8 * c.max_vars) hs.wsort_len (by omega) (by omega)))
                (sat_arr32 (8 * c.max_vars) hs.work_stk1_len (by omega) (by omega)))
              (sat_arr32 (8 * c.max_vars) hs.work_stk2_len (by omega) (by omega)))
            (sat_arr32 (8 * c.max_vars) hs.tarjan_mark_len (by omega) (by omega)))
          (sat_arr32 (8 * c.max_vars) hs.tarjan_reach_len (by omega) (by omega)))
        (sat_arr64 (8 * c.max_vars) hs.score_len rfl (by omega)))
      (sat_arr64 (8 * c.max_vars) hs.sim_sig_len rfl (by omega))
  have hT2 : ∀ k,
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
        array (t := i32) c.pLastLearned s.scratch.last_learned ⋆
        array (t := i32) c.pArena s.core.arena ⋆ array (t := i32) c.pWstk s.core.wstk ⋆
        array (t := i32) c.pDelayed s.scratch.delayed ⋆
        array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
        array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
        array (t := i32) c.pScratchBuf s.scratch.scratch_buf) k →
      (region c.pMinStk (8 * c.minDepth) ⋆ region c.pGlueUsed 256 ⋆
        region c.pLastLearned 64 ⋆ region c.pArena (4 * c.arena_cap) ⋆
        region c.pWstk (4 * c.wcap) ⋆ region c.pDelayed (12 * c.delayed_cap) ⋆
        region c.pRedRefs (4 * c.red_cap) ⋆ region c.pExtendStk (4 * c.extend_cap) ⋆
        region c.pScratchBuf (4 * c.scratch_cap)) k :=
    sep_mono2
      (sep_mono2
        (sep_mono2
          (sep_mono2
            (sep_mono2
              (sep_mono2
                (sep_mono2
                  (sep_mono2
                    (sat_arr32 (8 * c.minDepth) hc.min_stk_len
                      (by unfold FullCfg.minDepth; omega) (by unfold FullCfg.minDepth; omega))
                    (sat_arr32 256 hs.glue_used_len (by decide) (by decide)))
                  (sat_arr32 64 hs.last_learned_len (by decide) (by decide)))
                (sat_arr32 (4 * c.arena_cap) hc.arena_len_arr rfl (by omega)))
              (sat_arr32 (4 * c.wcap) hc.wstk_len_arr rfl (by omega)))
            (sat_arr32 (12 * c.delayed_cap) hs.delayed_len_arr (by omega) (by omega)))
          (sat_arr32 (4 * c.red_cap) hs.red_refs_len rfl (by omega)))
        (sat_arr32 (4 * c.extend_cap) hs.extend_stk_len rfl (by omega)))
      (sat_arr32 (4 * c.scratch_cap) hs.scratch_buf_len rfl (by omega))
  have h2 : ((bytes cnf_ptr cnfBytes ⋆ R) ⋆ region c.hdr c.avail) m :=
    sep_mono_r (fun _ h => c.regions_to_avail h)
      (sep_mono_r
        (sep_mono2
          (sep_mono2
            (sep_mono2
              (sep_mono2
                (sep_mono2 (sep_mono2 (sep_mono2 hHead hB) hU1) hU2)
                hU3)
              hT1)
            hT2)
          (fun _ hb => hb))
        h1)
  exact sep_ac h2

/-- Shared extend + verified `kissat_check_model` tail proof for both M4 and M5: keeps `hok`
and constructs framed `readModelFromWork M work_ptr` satisfaction whenever `ok = 1#64`. -/
private theorem sat_solve_bytes_extend_check {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c0 c2 : FullCfg} {s3 : FullState} {cnf_ptr work_ptr hdr_ptr : BitVec 64}
    {cnfBytes : List UInt8} {wlen : Nat} {R : Mem 64 → Prop} {m3 : Mem 64}
    (hExt : ∀ a m Q X, Full.fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64) (hw_ge : fullAlignPad work_ptr ≤ wlen)
    (hcompat : FullM4Compact.FullCfgCompat c0 c2)
    (hch_ptr : c0.hdr = hdr_ptr)
    (hch : c0.hdr = work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
    (hca : c0.avail = wlen - fullAlignPad work_ptr)
    (hlen3 : s3.LengthsOk c2) (hext3 : s3.scratch.extend_len ≤ c2.extend_cap)
    (hm3 : (bytes cnf_ptr cnfBytes ⋆ FullMem c2 s3 ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m3)
    (hRet : ∀ r m', (r = 0#64 ∨ r = 10#64) →
      (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        ∀ (F : Mem 64 → Prop) (M : Mem 64), (Eq m' ⋆ F) M →
          cnf.Sat (readModelFromWork M work_ptr)) →
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' → Q (r, ()) m') :
    let cnf_end := cnf_ptr + BitVec.ofNat 64 cnfBytes.length
    wp Γ Q X (Expr.call (as := [i64]) (bs := []) "full_extend" (Arg.var hdr_ptr, ()) fun _ =>
      Expr.store (t := i64) (Arg.var (BitVec.ofNat 64 c0.mv)) (Arg.var hdr_ptr)
      (Expr.let_ ⟨OpCode.add i64, (Arg.var hdr_ptr, Arg.imm 768, ())⟩
        fun p_mx => Expr.load i64 (Arg.var p_mx.fst) fun ld_mx =>
        Expr.let_ ⟨OpCode.sub i64, (Arg.var ld_mx, Arg.var (BitVec.ofNat 64 c0.mv), ())⟩
          fun p_bva => Expr.let_ ⟨OpCode.add i64, (Arg.var hdr_ptr, Arg.imm 784, ())⟩
            fun p_bva_addr => Expr.store (t := i64) (Arg.var p_bva.fst) (Arg.var p_bva_addr.fst)
              (Expr.let_ ⟨OpCode.add i64, (Arg.var hdr_ptr, Arg.imm 64, ())⟩
                fun p1 => Expr.load i64 (Arg.var p1.fst) fun ld_v =>
                Expr.call (as := [i64, i64, i64, i64, i64]) (bs := [i64]) "kissat_check_model"
                  (Arg.var cnf_ptr, Arg.var cnf_end, Arg.var hdr_ptr, Arg.var ld_v,
                   Arg.var (BitVec.ofNat 64 c0.mv), ())
                fun p2 => Expr.group (sig := [[i64]])
                  (fun _ => Blocks.cons (fun p3 => Expr.ret (Arg.var p3.fst, ())) Blocks.nil)
                  fun Jr => Expr.let_
                    ⟨OpCode.cmp CmpOp.eq i64 Ty.bool rfl, (Arg.var p2.fst, Arg.imm 1, ())⟩
                    fun p3 => Expr.jnz (Arg.var p3.fst)
                      (Expr.jump Jr.fst (Arg.imm 10, ()))
                      (Expr.jump Jr.fst (Arg.imm 0, ()))))) m3 := by
  dsimp only
  have hch2 : c2.hdr = hdr_ptr := hcompat.hdr.trans hch_ptr
  have hch2_w : c2.hdr = work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) :=
    hcompat.hdr.trans hch
  rw [← hch2]
  c0_call hExt
  refine ⟨c2, s3, bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R,
    ⟨rfl, hext3⟩, hlen3,
    by dsimp only [Full.fullExtendSlice, SafetySlice.ofMask]; exact sep_ac hm3, ?_⟩
  intro ⟨⟩ s4 m4 _ hlen4 _ hm4
  dsimp only [Full.fullExtendSlice, SafetySlice.ofMask] at hm4
  have hm4_f : (FullMem c2 s4 ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m4 := sep_ac hm4
  refine wp_store_sep (FullM4Compact.full_store_mv_mid (BitVec.ofNat 64 c0.mv) hm4_f) ?_
  intro m4_1 hm4_1
  c0_step
  refine wp_load_of (FullM4Compact.full_load_max_vars_mid hm4_1) ?_
  c0_step
  let bva_bv : BitVec 64 := BitVec.ofNat 64 c2.max_vars - BitVec.ofNat 64 c0.mv
  have hmid_arr : (array64 (c2.hdr + 32) (Full.hdrTailWords c2 s4) ⋆
      (dimacsState c2.hdr (BitVec.ofNat 64 c0.mv) (BitVec.ofNat 64 c2.nc)
          s4.core.d_cur s4.core.d_val ⋆
        FullCoreArrays c2 s4.core ⋆ FullScratchArrays c2 s4.scratch ⋆ c2.pad ⋆
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R))) m4_1 := by
    unfold FullM4Compact.FullMemShrinkMid at hm4_1; exact sep_ac hm4_1
  obtain ⟨hst_bva_ok, hm4_bva⟩ := store_array64 (i := 94) bva_bv
    (by rw [Full.hdrTailWords_length]; decide) hmid_arr
  have hptr784 : c2.hdr + 32 + BitVec.ofNat 64 (8 * 94) = c2.hdr + 784 := by
    rw [BitVec.add_assoc, show (32 : BitVec 64) + BitVec.ofNat 64 (8 * 94) = 784 by decide]
  rw [hptr784] at hst_bva_ok hm4_bva
  refine wp_store_sep ⟨hst_bva_ok, hm4_bva⟩ ?_
  intro m4_2 hm4_2
  c0_step
  have hget4 := loadVal_array64 (i := 4)
    (by rw [List.length_set, Full.hdrTailWords_length]; decide) hm4_2
  rw [BitVec.add_assoc, show (32 : BitVec 64) + BitVec.ofNat 64 (8 * 4) = 64 by decide,
    List.getElem_set_ne (by decide)] at hget4
  have hpv4 : (Full.hdrTailWords c2 s4)[4]'(by rw [Full.hdrTailWords_length]; decide) =
      c2.pVals := rfl
  rw [hpv4] at hget4
  refine wp_load_of hget4 ?_
  have hmv0_bd := c0.hmv; have hmx0_bd := c0.hmaxv; have hbva0 := c0.hbva
  unfold dimacsBound at hmv0_bd hmx0_bd
  let valsBytes : List UInt8 := s4.core.vals.map UInt8.ofBitVec
  have hm4_2_b : (bytes cnf_ptr cnfBytes ⋆
      dimacsState c2.hdr (BitVec.ofNat 64 c0.mv) (BitVec.ofNat 64 c2.nc)
        s4.core.d_cur s4.core.d_val ⋆
      bytes c2.pVals valsBytes ⋆
      (SatCheckRest c2 s4 bva_bv ⋆ (region work_ptr (fullAlignPad work_ptr) ⋆ R))) m4_2 := by
    have ha1 : (array (t := i8) c2.pVals s4.core.vals ⋆
        (bytes cnf_ptr cnfBytes ⋆
          dimacsState c2.hdr (BitVec.ofNat 64 c0.mv) (BitVec.ofNat 64 c2.nc)
            s4.core.d_cur s4.core.d_val ⋆
          (SatCheckRest c2 s4 bva_bv ⋆
            (region work_ptr (fullAlignPad work_ptr) ⋆ R)))) m4_2 := by
      unfold SatCheckRest FullCoreArrays FullCoreByteArrs at *; exact sep_ac hm4_2
    have hm2x : c2.max_vars < 2 * dimacsBound := c2.hmaxv
    unfold dimacsBound at hm2x
    have ha2 : (bytes c2.pVals valsBytes ⋆
        (bytes cnf_ptr cnfBytes ⋆
          dimacsState c2.hdr (BitVec.ofNat 64 c0.mv) (BitVec.ofNat 64 c2.nc)
            s4.core.d_cur s4.core.d_val ⋆
          (SatCheckRest c2 s4 bva_bv ⋆
            (region work_ptr (fullAlignPad work_ptr) ⋆ R)))) m4_2 := by
      refine sep_mono (fun _ hf => ?_) ha1
      have hbytes := array_eq_bytesOf (t := i8) c2.pVals s4.core.vals
        (by simp [Ty.bytes, Ty.size, i8, hlen4.core_ok.vals_len]; omega) hf
      rw [bytesOf_i8_eq_map] at hbytes; exact hbytes.symm
    exact sep_ac ha2
  have hvals_ge : 2 * c0.mv ≤ valsBytes.length := by
    have := hcompat.max_vars; simp [valsBytes, hlen4.core_ok.vals_len]; omega
  have hvals_lt : valsBytes.length ≤ 2 ^ 64 := by
    have := c2.hmaxv; unfold dimacsBound at this
    simp [valsBytes, hlen4.core_ok.vals_len]; omega
  c0_call hCheck
  refine ⟨BitVec.ofNat 64 c0.mv, BitVec.ofNat 64 c2.nc, s4.core.d_cur, s4.core.d_val,
    cnfBytes, valsBytes, c0.mv,
    SatCheckRest c2 s4 bva_bv ⋆ (region work_ptr (fullAlignPad work_ptr) ⋆ R),
    rfl, rfl, hcfit, by omega, hvals_ge, hvals_lt,
    by simpa [sep_assoc] using hm4_2_b, ?_⟩
  intro ok mv' nc' cur' val' m5 hok hm5
  have hm5_reg : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m5 :=
    sat_merge_reg hwfit hw_ge (by
      rw [← hch, ← hca, ← hcompat.hdr, ← hcompat.avail]
      exact sat_checkModel_post_to_region hlen4 (by simpa [sep_assoc] using hm5))
  have hm5_ptr : loadVal m5 i64
      (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) + 64#64) = some c2.pVals := by
    have h_arr : (array64 (c2.hdr + 32) ((Full.hdrTailWords c2 s4).set 94 bva_bv) ⋆
        (bytes cnf_ptr cnfBytes ⋆ dimacsState c2.hdr mv' nc' cur' val' ⋆
          bytes c2.pVals valsBytes ⋆ array (t := i8) c2.pLitMark s4.core.lit_mark ⋆
          array (t := i8) c2.pMark s4.core.mrk ⋆ FullCoreU32A c2 s4.core ⋆
          FullCoreU32B c2 s4.core ⋆ FullCoreDynArrs c2 s4.core ⋆
          FullScratchArrays c2 s4.scratch ⋆ c2.pad ⋆
          (region work_ptr (fullAlignPad work_ptr) ⋆ R))) m5 := by
      unfold SatCheckRest at hm5; exact sep_ac hm5
    have hld := loadVal_array64 (i := 4)
      (by rw [List.length_set, Full.hdrTailWords_length]; decide) h_arr
    rw [BitVec.add_assoc, show (32 : BitVec 64) + BitVec.ofNat 64 (8 * 4) = 64#64 by decide,
      List.getElem_set_ne (by decide), hpv4, hch2_w] at hld
    exact hld
  have hm5_vals : (bytes c2.pVals valsBytes ⋆
      (bytes cnf_ptr cnfBytes ⋆ dimacsState c2.hdr mv' nc' cur' val' ⋆
        SatCheckRest c2 s4 bva_bv ⋆ (region work_ptr (fullAlignPad work_ptr) ⋆ R))) m5 :=
    sep_ac hm5
  have h10_model : ok = 1#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
      ∀ (F : Mem 64 → Prop) (M : Mem 64), (Eq m5 ⋆ F) M →
        cnf.Sat (readModelFromWork M work_ptr) := by
    intro hok1
    have hrun : runKissatCheckModel cnfBytes valsBytes c0.mv = true := by
      cases hrc : runKissatCheckModel cnfBytes valsBytes c0.mv
      · rw [hrc] at hok; simp only [Bool.false_eq_true, ↓reduceIte] at hok
        rw [hok1] at hok; cases hok
      · rfl
    obtain ⟨cnf, mv, hparse, hmv_le, hbd, hsat⟩ := runKissatCheckModel_sat_exact hrun
    refine ⟨cnf, hparse, fun F M hM => cnf_sat_congr (fun cl hcl lit hlit => ?_) hsat⟩
    obtain ⟨hv_lo, hv_hi⟩ := hbd cl hcl lit hlit
    have hidx : 2 * (lit.1 - 1) < valsBytes.length := by omega
    have hbyte := load_bytes_at hidx hvals_lt hm5_vals
    rw [readModelFromWork_frame hM hm5_ptr hbyte, u8_ofBitVec_ofNat_toNat]
    have hv_ne : (lit.1 == 0) = false := beq_false_of_ne (by omega)
    simp [hv_ne, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
  refine wp_join_group (ts := [i64])
    (fun (res_v, ()) m6 =>
      (res_v = 0#64 ∨ res_v = 10#64) ∧
      (res_v = 10#64 → ok = 1#64) ∧ m6 = m5)
    (fun _ ⟨res_v, ⟨⟩⟩ m6 ⟨hres_v, hres10, hm6⟩ => by
      rw [hm6]; c0_hsteps
      exact hRet res_v m5 hres_v (fun h10 => h10_model (hres10 h10)) hm5_reg)
    (fun Jr hJr => by
      c0_hsteps
      · exact hJr (10#64, ()) m5 ⟨Or.inr rfl, (fun _ => hc), rfl⟩
      · exact hJr (0#64, ()) m5 ⟨Or.inl rfl, (fun h => by cases h), rfl⟩)

/-- Parametric `Func.wp` theorem for M5 `kissat_solve_bytes_m5` against `fullSolveBytesModelSpec`
(UNSAT + constructive framed `readModelFromWork` SAT soundness). -/
theorem kissat_solve_bytes_m5_model_wp (Γ : Env)
    (hInit : ∀ a m Q X, Full.fullInitStateSpec a m Q X →
      Γ "full_init_state_m5" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hParse : ∀ a m Q X, Full.fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hPre : ∀ a m Q X, FullM4.m4PreprocessSpec a m Q X →
      Γ "full_preprocess_m5" [i64] [i64] a m Q X)
    (hSearch : ∀ a m Q X, FullM4.m4SearchSpec a m Q X →
      Γ "full_search_m5" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, Full.fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullSolveBytesModelSpec a m Q X →
      Func.wp Γ FullM5Orch.kissat_solve_bytes_m5_body a m Q X := by
  rintro ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, ⟨⟩⟩ m Q X
    ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, hQ⟩
  unfold Func.wp FullM5Orch.kissat_solve_bytes_m5_body; wp_unfold
  refine ⟨fun _ => hQ 0#64 m (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm,
    fun _ => ?_⟩
  refine ⟨fun _ => hQ 0#64 m (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm,
    fun _ => ?_⟩
  refine ⟨fun _ => hQ 0#64 m (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm,
    fun _ => ?_⟩
  have hnot0 : ~~~(0 : BitVec 64) = 0xFFFFFFFFFFFFFFFF#64 := rfl
  rw [hnot0, sat_bv64_ugt_max_sub_false hcfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  rw [sat_bv64_ugt_max_sub_false hwfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  let pNat : Nat := fullAlignPad work_ptr
  have hp_lt8 : pNat < 8 := fullAlignPad_lt8 work_ptr
  have hpad_ult : (BitVec.ofNat 64 wlen).ult (((8 - (work_ptr &&& 7)) &&& 7) + 1152) =
      decide (wlen < pNat + 1152) := by
    rw [sat_alignPad_bv_eq work_ptr, show (1152 : BitVec 64) = BitVec.ofNat 64 1152 from rfl,
      bv_add_ofNat, bv_ult_eq (by omega) (by omega)]
  rw [hpad_ult]; simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun _ => hQ 0#64 m (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm,
    fun hw_ge_not => ?_⟩
  have hw_ok : pNat + 1152 ≤ wlen := by omega
  let hdr_addr : BitVec 64 := work_ptr + BitVec.ofNat 64 pNat
  let availNat : Nat := wlen - pNat
  have hpad_bv : (8 - (work_ptr &&& 7)) &&& 7 = BitVec.ofNat 64 pNat := sat_alignPad_bv_eq work_ptr
  have hhdr_bv : work_ptr + ((8 - (work_ptr &&& 7)) &&& 7) = hdr_addr := by rw [hpad_bv]
  have hav_bv :
      BitVec.ofNat 64 wlen - ((8 - (work_ptr &&& 7)) &&& 7) = BitVec.ofNat 64 availNat := by
    rw [hpad_bv]; exact bv_sub_ofNat (by omega) (by omega)
  have hav_toNat : (BitVec.ofNat 64 wlen - ((8 - (work_ptr &&& 7)) &&& 7)).toNat = availNat := by
    rw [hav_bv, bv64_ofNat_toNat (by omega)]
  have hhdr_fit : hdr_addr.toNat + availNat < 2 ^ 64 := by
    rw [bv_add_ofNat_toNat (by omega)]; omega
  have hsplit : (bytes cnf_ptr cnfBytes ⋆
      region hdr_addr availNat ⋆ (region work_ptr pNat ⋆ R)) m := by
    have h1 : (region work_ptr wlen ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
    have h2 : ((region work_ptr pNat ⋆ region hdr_addr availNat) ⋆
        (bytes cnf_ptr cnfBytes ⋆ R)) m :=
      sep_mono (fun _ f => region_work_to_hdr (by omega) (by omega) f) h1
    exact sep_ac h2
  c0_call hInit
  refine ⟨cnfBytes, region work_ptr pNat ⋆ R, rfl, hcfit,
    by rw [hhdr_bv, hav_toNat]; exact hhdr_fit,
    by rw [hav_toNat]; omega,
    by rw [hhdr_bv, hav_toNat]; exact hsplit, ?_, ?_⟩
  · intro m' hm' _; wp_unfold
    have hm'_r : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' :=
      sat_merge_reg hwfit (by omega) (by rw [hhdr_bv, hav_toNat] at hm'; exact hm')
    exact hQ 0#64 m' (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm'_r
  · intro c s0 j0 rest0 m0 hch_ptr hca0 hhdr0 hj0 hdrop0 hinv0 hcv0 hdcur0
      hal0 _ hte0 hpr0 hcl0 _ _ hprob0 _ _ hoom0 hinc0 hvals0 hwvec0 _ _ _ hm0
    have hch : c.hdr = hdr_addr := hch_ptr.trans hhdr_bv
    have hca : c.avail = availNat := hca0.trans hav_toNat
    c0_hsplit
    rotate_left; · cases hc
    c0_hsteps
    c0_call hParse
    refine ⟨c, s0, cnf_ptr, cnfBytes, j0, region work_ptr pNat ⋆ R,
      hch_ptr.symm, rfl, hcfit, hj0, by rwa [hdrop0], hcv0, hdcur0, hcl0, hte0, hpr0, hal0,
      hoom0, hprob0, hinc0, hvals0, hwvec0, hinv0, hm0, ?_⟩
    intro pb s1 m1 hlen1 hpb_dom _ _ _ hpb20 hpb1 _ hm1; c0_hsteps
    · rcases hpb_dom with rfl | h1 | rfl
      · exact hQ 0#64 m1 (Or.inl rfl) (fun h => by cases h) (fun h => by cases h)
          (sat_merge_arena hwfit (by omega) hch hca hlen1 hm1)
      · exact absurd h1 hc
      · exact hQ 20#64 m1 (Or.inr (Or.inr rfl)) (fun _ => hpb20 rfl) (fun h => by cases h)
          (sat_merge_arena hwfit (by omega) hch hca hlen1 hm1)
    · obtain ⟨cnf, hparse, hinv1, hcl1⟩ := hpb1 hc
      have hcnf_pos : CnfVarsPos cnf := sat_parseDimacs_vars_pos hparse
      have hm1_load :
          (FullMem c s1 ⋆ (bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R)) m1 := sep_ac hm1
      have hload_mv : loadVal m1 i64 (work_ptr + ((8 - (work_ptr &&& 7)) &&& 7)) =
          some (BitVec.ofNat 64 c.mv) := by
        rw [hhdr_bv, ← hch]
        exact FullArenaTactics.load_full_mv hm1_load
      refine wp_load_of hload_mv ?_
      c0_call hPre; refine ⟨c, shiftDownCnf cnf, s1,
        bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
        hch_ptr.symm, hinv1, hcl1, sep_ac hm1, ?_⟩
      intro pp c2 s2 m2 hcomp2 hlen2 hpp_dom _ hpp20 hpp1 hpp10 hm2
      have hch2 : c2.hdr = hdr_addr := hcomp2.hdr.trans hch
      have hca2 : c2.avail = availNat := hcomp2.avail.trans hca
      c0_hsplit
      · c0_hsteps
        exact hQ 20#64 m2 (Or.inr (Or.inr rfl))
          (fun _ => ⟨cnf, hparse, shiftDownCnf_unsat hcnf_pos (hpp20 hc)⟩)
          (fun h => by cases h)
          (sat_merge_arena hwfit (by omega) hch2 hca2 hlen2 (sep_ac hm2))
      c0_hsteps_nogrp
      refine wp_join_state1 (α := BitVec 64 × FullCfg × FullState) Prod.fst
        (fun p mr => FullM4Compact.FullCfgCompat c p.2.1 ∧
          p.2.2.LengthsOk p.2.1 ∧ (p.1 = 0#64 ∨ p.1 = 10#64 ∨ p.1 = 20#64) ∧
          (p.1 = 20#64 → cnf.Unsat) ∧ (p.1 = 10#64 → p.2.2.scratch.extend_len ≤ p.2.1.extend_cap) ∧
          (bytes cnf_ptr cnfBytes ⋆ FullMem p.2.1 p.2.2 ⋆ (region work_ptr pNat ⋆ R)) mr)
        (fun _ ⟨rv, cr, sr⟩ mr ⟨hcompr, hlen_r, hrv_dom, hrv_u, hrv_ext, hmr⟩ => by
          have hchr : cr.hdr = hdr_addr := hcompr.hdr.trans hch
          have hcar : cr.avail = availNat := hcompr.avail.trans hca
          c0_hsteps
          · exact sat_solve_bytes_extend_check hExt hCheck hcfit hwfit (by omega) hcompr
              hch_ptr (by rw [← hpad_bv]; exact hch_ptr) hca hlen_r (hrv_ext hc) hmr
              fun res m_end hres hmod hm_end =>
                hQ res m_end (hres.elim Or.inl fun h => Or.inr (Or.inl h))
                  (fun h20 => by rcases hres with rfl | rfl <;> cases h20)
                  hmod hm_end
          · exact hQ rv mr hrv_dom (fun h20 => ⟨cnf, hparse, hrv_u h20⟩)
              (fun h10 => absurd h10 ‹rv ≠ 10#64›)
              (sat_merge_arena hwfit (by omega) hchr hcar hlen_r hmr))
        (fun Jr hJr => by
          c0_hsplit
          · c0_hsteps
            exact hJr (10#64, c2, s2) m2 ⟨hcomp2, hlen2, Or.inr (Or.inl rfl), (fun h => by cases h),
              (fun _ => hpp10 hc), sep_ac hm2⟩
          · c0_hsteps_nogrp
            refine wp_join_state1 (α := BitVec 64 × FullCfg × FullState) Prod.fst
              (fun p mr => FullM4Compact.FullCfgCompat c p.2.1 ∧
                p.2.2.LengthsOk p.2.1 ∧ (p.1 = 0#64 ∨ p.1 = 10#64 ∨ p.1 = 20#64) ∧
                (p.1 = 20#64 → cnf.Unsat) ∧
                (p.1 = 10#64 → p.2.2.scratch.extend_len ≤ p.2.1.extend_cap) ∧
                (bytes cnf_ptr cnfBytes ⋆ FullMem p.2.1 p.2.2 ⋆ (region work_ptr pNat ⋆ R)) mr)
              (fun _ p mr hp => by c0_hsteps; exact hJr p mr hp)
              (fun Jr2 hJr2 => by
                c0_hsplit
                · c0_hsteps
                  exact hJr2 (0#64, c2, s2) m2 ⟨hcomp2, hlen2, Or.inl rfl,
                    (fun h => by cases h), (fun h => by cases h), sep_ac hm2⟩
                · have hpp_eq1 : pp = 1#64 := by
                    rcases hpp_dom with h0 | h1 | h10 | h20
                    · exact absurd h0 hc
                    · exact h1
                    · exact absurd h10 (by assumption)
                    · exact absurd h20 (by assumption)
                  obtain ⟨hinv2, hcl2⟩ := hpp1 hpp_eq1
                  c0_hsteps; rw [hhdr_bv, ← hch2]; c0_call hSearch
                  refine ⟨c2, shiftDownCnf cnf, s2,
                    bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
                    rfl, hinv2, hcl2, hm2, ?_⟩
                  intro r3 c3 s3 m3 hcomp3 hlen3 hr3_dom hur3 hext3 hm3; c0_hsteps
                  exact hJr2 (r3, c3, s3) m3 ⟨hcomp2.trans hcomp3, hlen3, hr3_dom,
                    fun h20 => shiftDownCnf_unsat hcnf_pos (hur3 h20), hext3, sep_ac hm3⟩))

/-- Parametric `Func.wp` theorem for M4 `kissat_solve_bytes` against `fullSolveBytesModelSpec`
(UNSAT + constructive framed `readModelFromWork` SAT soundness). -/
theorem m4_kissat_solve_bytes_model_wp (Γ : Env)
    (hInit : ∀ a m Q X, Full.fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hParse : ∀ a m Q X, Full.fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hPre : ∀ a m Q X, FullM4.m4PreprocessSpec a m Q X →
      Γ "full_preprocess" [i64] [i64] a m Q X)
    (hSearch : ∀ a m Q X, FullM4.m4SearchSpec a m Q X →
      Γ "full_search" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, Full.fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullSolveBytesModelSpec a m Q X →
      Func.wp Γ FullM4.kissat_solve_bytes_body a m Q X := by
  rintro ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, ⟨⟩⟩ m Q X
    ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, hQ⟩
  unfold Func.wp FullM4.kissat_solve_bytes_body; wp_unfold
  refine ⟨fun _ => hQ 0#64 m (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm,
    fun _ => ?_⟩
  refine ⟨fun _ => hQ 0#64 m (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm,
    fun _ => ?_⟩
  refine ⟨fun _ => hQ 0#64 m (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm,
    fun _ => ?_⟩
  have hnot0 : ~~~(0 : BitVec 64) = 0xFFFFFFFFFFFFFFFF#64 := rfl
  rw [hnot0, sat_bv64_ugt_max_sub_false hcfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  rw [sat_bv64_ugt_max_sub_false hwfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  let pNat : Nat := fullAlignPad work_ptr
  have hp_lt8 : pNat < 8 := fullAlignPad_lt8 work_ptr
  have hpad_ult : (BitVec.ofNat 64 wlen).ult (((8 - (work_ptr &&& 7)) &&& 7) + 1152) =
      decide (wlen < pNat + 1152) := by
    rw [sat_alignPad_bv_eq work_ptr, show (1152 : BitVec 64) = BitVec.ofNat 64 1152 from rfl,
      bv_add_ofNat, bv_ult_eq (by omega) (by omega)]
  rw [hpad_ult]; simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun _ => hQ 0#64 m (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm,
    fun hw_ge_not => ?_⟩
  have hw_ok : pNat + 1152 ≤ wlen := by omega
  let hdr_addr : BitVec 64 := work_ptr + BitVec.ofNat 64 pNat
  let availNat : Nat := wlen - pNat
  have hpad_bv : (8 - (work_ptr &&& 7)) &&& 7 = BitVec.ofNat 64 pNat := sat_alignPad_bv_eq work_ptr
  have hhdr_bv : work_ptr + ((8 - (work_ptr &&& 7)) &&& 7) = hdr_addr := by rw [hpad_bv]
  have hav_bv :
      BitVec.ofNat 64 wlen - ((8 - (work_ptr &&& 7)) &&& 7) = BitVec.ofNat 64 availNat := by
    rw [hpad_bv]; exact bv_sub_ofNat (by omega) (by omega)
  have hav_toNat : (BitVec.ofNat 64 wlen - ((8 - (work_ptr &&& 7)) &&& 7)).toNat = availNat := by
    rw [hav_bv, bv64_ofNat_toNat (by omega)]
  have hhdr_fit : hdr_addr.toNat + availNat < 2 ^ 64 := by
    rw [bv_add_ofNat_toNat (by omega)]; omega
  have hsplit : (bytes cnf_ptr cnfBytes ⋆
      region hdr_addr availNat ⋆ (region work_ptr pNat ⋆ R)) m := by
    have h1 : (region work_ptr wlen ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
    have h2 : ((region work_ptr pNat ⋆ region hdr_addr availNat) ⋆
        (bytes cnf_ptr cnfBytes ⋆ R)) m :=
      sep_mono (fun _ f => region_work_to_hdr (by omega) (by omega) f) h1
    exact sep_ac h2
  c0_call hInit
  refine ⟨cnfBytes, region work_ptr pNat ⋆ R, rfl, hcfit,
    by rw [hhdr_bv, hav_toNat]; exact hhdr_fit,
    by rw [hav_toNat]; omega,
    by rw [hhdr_bv, hav_toNat]; exact hsplit, ?_, ?_⟩
  · intro m' hm' _; wp_unfold
    have hm'_r : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' :=
      sat_merge_reg hwfit (by omega) (by rw [hhdr_bv, hav_toNat] at hm'; exact hm')
    exact hQ 0#64 m' (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm'_r
  · intro c s0 j0 rest0 m0 hch_ptr hca0 hhdr0 hj0 hdrop0 hinv0 hcv0 hdcur0
      hal0 _ hte0 hpr0 hcl0 _ _ hprob0 _ _ hoom0 hinc0 hvals0 hwvec0 _ _ _ hm0
    have hch : c.hdr = hdr_addr := hch_ptr.trans hhdr_bv
    have hca : c.avail = availNat := hca0.trans hav_toNat
    c0_hsplit
    rotate_left; · cases hc
    c0_hsteps
    c0_call hParse
    refine ⟨c, s0, cnf_ptr, cnfBytes, j0, region work_ptr pNat ⋆ R,
      hch_ptr.symm, rfl, hcfit, hj0, by rwa [hdrop0], hcv0, hdcur0, hcl0, hte0, hpr0, hal0,
      hoom0, hprob0, hinc0, hvals0, hwvec0, hinv0, hm0, ?_⟩
    intro pb s1 m1 hlen1 hpb_dom _ _ _ hpb20 hpb1 _ hm1; c0_hsteps
    · rcases hpb_dom with rfl | h1 | rfl
      · exact hQ 0#64 m1 (Or.inl rfl) (fun h => by cases h) (fun h => by cases h)
          (sat_merge_arena hwfit (by omega) hch hca hlen1 hm1)
      · exact absurd h1 hc
      · exact hQ 20#64 m1 (Or.inr (Or.inr rfl)) (fun _ => hpb20 rfl) (fun h => by cases h)
          (sat_merge_arena hwfit (by omega) hch hca hlen1 hm1)
    · obtain ⟨cnf, hparse, hinv1, hcl1⟩ := hpb1 hc
      have hcnf_pos : CnfVarsPos cnf := sat_parseDimacs_vars_pos hparse
      have hm1_load :
          (FullMem c s1 ⋆ (bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R)) m1 := sep_ac hm1
      have hload_mv : loadVal m1 i64 (work_ptr + ((8 - (work_ptr &&& 7)) &&& 7)) =
          some (BitVec.ofNat 64 c.mv) := by
        rw [hhdr_bv, ← hch]
        exact FullArenaTactics.load_full_mv hm1_load
      refine wp_load_of hload_mv ?_
      c0_call hPre; refine ⟨c, shiftDownCnf cnf, s1,
        bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
        hch_ptr.symm, hinv1, hcl1, sep_ac hm1, ?_⟩
      intro pp c2 s2 m2 hcomp2 hlen2 hpp_dom _ hpp20 hpp1 hpp10 hm2
      have hch2 : c2.hdr = hdr_addr := hcomp2.hdr.trans hch
      have hca2 : c2.avail = availNat := hcomp2.avail.trans hca
      c0_hsplit
      · c0_hsteps
        exact hQ 20#64 m2 (Or.inr (Or.inr rfl))
          (fun _ => ⟨cnf, hparse, shiftDownCnf_unsat hcnf_pos (hpp20 hc)⟩)
          (fun h => by cases h)
          (sat_merge_arena hwfit (by omega) hch2 hca2 hlen2 (sep_ac hm2))
      c0_hsteps_nogrp
      refine wp_join_state1 (α := BitVec 64 × FullCfg × FullState) Prod.fst
        (fun p mr => FullM4Compact.FullCfgCompat c p.2.1 ∧
          p.2.2.LengthsOk p.2.1 ∧ (p.1 = 0#64 ∨ p.1 = 10#64 ∨ p.1 = 20#64) ∧
          (p.1 = 20#64 → cnf.Unsat) ∧ (p.1 = 10#64 → p.2.2.scratch.extend_len ≤ p.2.1.extend_cap) ∧
          (bytes cnf_ptr cnfBytes ⋆ FullMem p.2.1 p.2.2 ⋆ (region work_ptr pNat ⋆ R)) mr)
        (fun _ ⟨rv, cr, sr⟩ mr ⟨hcompr, hlen_r, hrv_dom, hrv_u, hrv_ext, hmr⟩ => by
          have hchr : cr.hdr = hdr_addr := hcompr.hdr.trans hch
          have hcar : cr.avail = availNat := hcompr.avail.trans hca
          c0_hsteps
          · exact sat_solve_bytes_extend_check hExt hCheck hcfit hwfit (by omega) hcompr
              hch_ptr (by rw [← hpad_bv]; exact hch_ptr) hca hlen_r (hrv_ext hc) hmr
              fun res m_end hres hmod hm_end =>
                hQ res m_end (hres.elim Or.inl fun h => Or.inr (Or.inl h))
                  (fun h20 => by rcases hres with rfl | rfl <;> cases h20)
                  hmod hm_end
          · exact hQ rv mr hrv_dom (fun h20 => ⟨cnf, hparse, hrv_u h20⟩)
              (fun h10 => absurd h10 ‹rv ≠ 10#64›)
              (sat_merge_arena hwfit (by omega) hchr hcar hlen_r hmr))
        (fun Jr hJr => by
          c0_hsplit
          · c0_hsteps
            exact hJr (10#64, c2, s2) m2 ⟨hcomp2, hlen2, Or.inr (Or.inl rfl), (fun h => by cases h),
              (fun _ => hpp10 hc), sep_ac hm2⟩
          · c0_hsteps_nogrp
            refine wp_join_state1 (α := BitVec 64 × FullCfg × FullState) Prod.fst
              (fun p mr => FullM4Compact.FullCfgCompat c p.2.1 ∧
                p.2.2.LengthsOk p.2.1 ∧ (p.1 = 0#64 ∨ p.1 = 10#64 ∨ p.1 = 20#64) ∧
                (p.1 = 20#64 → cnf.Unsat) ∧
                (p.1 = 10#64 → p.2.2.scratch.extend_len ≤ p.2.1.extend_cap) ∧
                (bytes cnf_ptr cnfBytes ⋆ FullMem p.2.1 p.2.2 ⋆ (region work_ptr pNat ⋆ R)) mr)
              (fun _ p mr hp => by c0_hsteps; exact hJr p mr hp)
              (fun Jr2 hJr2 => by
                c0_hsplit
                · c0_hsteps
                  exact hJr2 (0#64, c2, s2) m2 ⟨hcomp2, hlen2, Or.inl rfl,
                    (fun h => by cases h), (fun h => by cases h), sep_ac hm2⟩
                · have hpp_eq1 : pp = 1#64 := by
                    rcases hpp_dom with h0 | h1 | h10 | h20
                    · exact absurd h0 hc
                    · exact h1
                    · exact absurd h10 (by assumption)
                    · exact absurd h20 (by assumption)
                  obtain ⟨hinv2, hcl2⟩ := hpp1 hpp_eq1
                  c0_hsteps; rw [hhdr_bv, ← hch2]; c0_call hSearch
                  refine ⟨c2, shiftDownCnf cnf, s2,
                    bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
                    rfl, hinv2, hcl2, hm2, ?_⟩
                  intro r3 c3 s3 m3 hcomp3 hlen3 hr3_dom hur3 hext3 hm3; c0_hsteps
                  exact hJr2 (r3, c3, s3) m3 ⟨hcomp2.trans hcomp3, hlen3, hr3_dom,
                    fun h20 => shiftDownCnf_unsat hcnf_pos (hur3 h20), hext3, sep_ac hm3⟩))

end SolveModelProofs

/-! ## 4. Closed `m4SoundEnv` (`231` fns) via `ModuleOk.respec_tail` -/

private theorem ofTable_iff_of_mem {tbl : List SpecEntry} {e : SpecEntry} (he : e ∈ tbl)
    (hnd : (tbl.map SpecEntry.name).Nodup) {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs}
    {X : XPost} :
    Env.ofTable tbl e.name e.as e.rs xs m Q X ↔ e.eff xs m Q X := by
  induction tbl with
  | nil => nomatch he
  | cons e' es ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp he with rfl | hmem
    · exact Env.ofTable_cons_self _ _ _ _ _ _
    · have hne : e'.name ≠ e.name := fun h' => hnd.1 (h' ▸ List.mem_map_of_mem hmem)
      exact (Env.ofTable_cons_ne hne _ _ _ _).trans (ih hmem hnd.2)

private theorem ofTable_agree_prefix {tbl₀ tbl₁ : List SpecEntry} {pfx : List Fn} {k : Nat}
    (htk : tbl₀.take k = tbl₁.take k)
    (hnd₀ : (tbl₀.map SpecEntry.name).Nodup) (hnd₁ : (tbl₁.map SpecEntry.name).Nodup)
    (hsigs : (tbl₀.take k).map (fun e => (e.name, e.as, e.rs)) = pfx.map Fn.sig) :
    ∀ f as bs, (f, as, bs) ∈ pfx.map Fn.sig →
      ∀ xs m Q X, Env.ofTable tbl₀ f as bs xs m Q X ↔ Env.ofTable tbl₁ f as bs xs m Q X := by
  intro f as bs hmem xs m Q X
  rw [← hsigs, List.mem_map] at hmem
  obtain ⟨e, he_tk, hsig⟩ := hmem
  rcases hsig with ⟨rfl, rfl, rfl⟩
  have he₀ : e ∈ tbl₀ := List.mem_of_mem_take he_tk
  have he₁ : e ∈ tbl₁ := List.mem_of_mem_take (htk ▸ he_tk)
  exact (ofTable_iff_of_mem he₀ hnd₀).trans (ofTable_iff_of_mem he₁ hnd₁).symm

private theorem wp_noExit_lift {Γ : Env} {rs : List Ty} {e : Expr Val Cont rs} {m : Mem 64}
    {Q : Post rs} {X : XPost} (h : wp Γ Q (fun _ _ _ _ => False) e m) :
    wp Γ Q X e m :=
  wp_mono (fun _ _ hq => hq) (fun _ _ _ _ hf => hf.elim) e m h

/-- Closed `231`-function UNSAT + constructive SAT model environment for `FullM4.m4Module`. -/
def m4SoundEnv : Env := FullM4.mkM4Env fullSolveBytesModelSpec

theorem m4SoundEnv_noExit :
    ∀ f as bs xs m Q X X', m4SoundEnv f as bs xs m Q X → m4SoundEnv f as bs xs m Q X' :=
  FullM4.mkM4Env_noExit fullSolveBytesModelSpec

/-- Entry-point elimination helper for `m4SoundEnv` (avoids needing `@[expose]`). -/
theorem m4SoundEnv_solve_bytes_model {a : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : fullSolveBytesModelSpec a m Q X) :
    m4SoundEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X := by
  let h230 := FullM4.mkM4Env_row_at (mainSpec := fullSolveBytesModelSpec) 230
    ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], fullSolveBytesModelSpec, true⟩
  exact h230 a m Q X h

/-- Unconditional closed `ModuleOk` for `m4SoundEnv` on all `231` functions of `FullM4.m4Module`,
transporting the `230`-function prefix verbatim from `FullM4.m4Env_moduleOk` via
`ModuleOk.respec_tail`. -/
theorem m4SoundEnv_moduleOk : ModuleOk m4SoundEnv FullM4.m4Module := by
  have hsplit : FullM4.m4Module.fns = FullM4.m4Fns.take 230 ++ [FullM4.m4SolveBytesFn] := by
    change FullM4.m4Fns = FullM4.m4Fns.take 230 ++ [FullM4.m4SolveBytesFn]
    have hdrop : FullM4.m4Fns.drop 230 = [FullM4.m4SolveBytesFn] := by t_kernel_rfl
    rw [← hdrop, List.take_append_drop]
  have hsigs : ((FullM4.m4SpecTable fullSolveBytesSpec).take 230).map
      (fun e => (e.name, e.as, e.rs)) = (FullM4.m4Fns.take 230).map Fn.sig := by
    rw [List.map_take, List.map_take]
    exact congrArg (List.take 230) (FullM4.m4SpecTable_sigs fullSolveBytesSpec)
  have hagree : ∀ f as bs, (f, as, bs) ∈
      (FullM4.m4Fns.take 230).map Fn.sig ++ FullM4.m4Module.externs.map Extern.sig →
      ∀ xs m Q X, FullM4.m4Env f as bs xs m Q X ↔ m4SoundEnv f as bs xs m Q X := by
    intro f as bs hmem xs m Q X
    simp only [FullM4.m4Module, List.map_nil, List.append_nil] at hmem
    exact ofTable_agree_prefix (k := 230) (by t_kernel_rfl)
      (FullM4.m4SpecTable_nodup fullSolveBytesSpec)
      (FullM4.m4SpecTable_nodup fullSolveBytesModelSpec) hsigs f as bs hmem xs m Q X
  refine FullM4.m4Env_moduleOk.respec_tail hsplit hagree fun fn hfn xs m Q X hs => ?_
  rcases List.mem_singleton.mp hfn with rfl
  let h7 := FullM4.mkM4Env_row_at (mainSpec := fullSolveBytesModelSpec) 7
    ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩
  let h41 := FullM4.mkM4Env_row_at (mainSpec := fullSolveBytesModelSpec) 41
    ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩
  let h44 := FullM4.mkM4Env_row_at (mainSpec := fullSolveBytesModelSpec) 44
    ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩
  let h100 := FullM4.mkM4Env_row_at (mainSpec := fullSolveBytesModelSpec) 100
    ⟨"full_extend", [i64], [], fullExtendSpec, true⟩
  let h227 := FullM4.mkM4Env_row_at (mainSpec := fullSolveBytesModelSpec) 227
    ⟨"full_preprocess", [i64], [i64], FullM4.m4PreprocessSpec, true⟩
  let h229 := FullM4.mkM4Env_row_at (mainSpec := fullSolveBytesModelSpec) 229
    ⟨"full_search", [i64], [i64], FullM4.m4SearchSpec, true⟩
  exact wp_noExit_lift (m4_kissat_solve_bytes_model_wp m4SoundEnv h41 h44 h227 h229 h100 h7
    xs m Q _ (FullM4.mkM4Env_row_elim 230
      ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], fullSolveBytesModelSpec, true⟩
      rfl rfl hs))

/-- Source-level UNSAT + constructive SAT model soundness of Unified M4 `kissat_solve_bytes`
under `m4SoundEnv` (`231` functions): `r = 20` certifies `cnf.Unsat` and `r = 10` certifies
`cnf.Sat (readModelFromWork m' work_ptr)`. -/
theorem m4_solve_bytes_model_correct
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m4SoundEnv FullM4.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
          cnf.Sat (readModelFromWork m' work_ptr)) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X := by
  have hsplit : FullM4.m4Module.fns = FullM4.m4Fns.take 230 ++ FullM4.m4SolveBytesFn :: [] := by
    change FullM4.m4Fns = FullM4.m4Fns.take 230 ++ [FullM4.m4SolveBytesFn]
    have hdrop : FullM4.m4Fns.drop 230 = [FullM4.m4SolveBytesFn] := by t_kernel_rfl
    rw [← hdrop, List.take_append_drop]
  exact (m4SoundEnv_moduleOk.fnsOk _ _ _ hsplit).2.2 _ m _ X
    (m4SoundEnv_solve_bytes_model
      ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, fun _ m' hdom hu hmod hm' =>
        ⟨hdom, hu, fun h10 =>
          let ⟨cnf, hp, hf⟩ := hmod h10
          ⟨cnf, hp, hf emp m' (by rw [sep_emp])⟩, hm'⟩⟩)

/-- Source-level UNSAT + existential SAT soundness of Unified M4 `kissat_solve_bytes` under
`m4SoundEnv` (`231` functions). -/
theorem m4_solve_bytes_sound_correct
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m4SoundEnv FullM4.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  wp_mono
    (fun (_, ()) _ ⟨hdom, hu, hmod, hm'⟩ =>
      ⟨hdom, hu, fun h10 =>
        let ⟨cnf, hp, hsat⟩ := hmod h10
        ⟨cnf, hp, cnf_not_unsat_of_sat hsat⟩, hm'⟩)
    (fun _ _ _ _ h => h) _ m
    (m4_solve_bytes_model_correct hcfit hwfit hm)

/-! ## 5. Closed `m5SoundEnv` (`270` fns) via `ModuleOk.respec_tail` -/

/-- Closed `270`-function UNSAT + constructive SAT model environment for `FullM5.m5Module`. -/
def m5SoundEnv : Env := FullM5.mkM5Env fullSolveBytesModelSpec

theorem m5SoundEnv_noExit :
    ∀ f as bs xs m Q X X', m5SoundEnv f as bs xs m Q X → m5SoundEnv f as bs xs m Q X' :=
  FullM5.mkM5Env_noExit fullSolveBytesModelSpec

/-- Entry-point introduction helper for `m5SoundEnv` (`kissat_solve_bytes`). -/
theorem m5SoundEnv_solve_bytes_model {a : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : fullSolveBytesModelSpec a m Q X) :
    m5SoundEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] a m Q X :=
  (FullM5.mkM5Env_solve_bytes_iff fullSolveBytesModelSpec).mpr h

/-- Unconditional closed `ModuleOk` for `m5SoundEnv` on all `270` functions of `FullM5.m5Module`,
transporting all `268` prefix functions verbatim from `FullM5.m5Env_moduleOk` via
`ModuleOk.respec_tail`. -/
theorem m5SoundEnv_moduleOk : ModuleOk m5SoundEnv FullM5.m5Module := by
  let fnM5 : Fn :=
    ⟨"kissat_solve_bytes_m5", [i64, i64, i64, i64, i64], [i64],
      FullM5Orch.kissat_solve_bytes_m5_body⟩
  have hsplit : FullM5.m5Module.fns =
      FullM5.m5Fns.take 268 ++ [fnM5, FullM5.m5SolveBytesFwdFn] := by
    change FullM5.m5Fns = FullM5.m5Fns.take 268 ++ [fnM5, FullM5.m5SolveBytesFwdFn]
    have hdrop : FullM5.m5Fns.drop 268 = [fnM5, FullM5.m5SolveBytesFwdFn] := by t_kernel_rfl
    rw [← hdrop, List.take_append_drop]
  have hagree : ∀ f as bs, (f, as, bs) ∈
      (FullM5.m5Fns.take 268).map Fn.sig ++ FullM5.m5Module.externs.map Extern.sig →
      ∀ xs m Q X, FullM5.m5Env f as bs xs m Q X ↔ m5SoundEnv f as bs xs m Q X := by
    intro f as bs hmem xs m Q X
    simp only [FullM5.m5Module, List.map_nil, List.append_nil] at hmem
    rw [FullM5.m5Env_eq_mkM5Env]
    exact FullM5.mkM5Env_agree_prefix fullSolveBytesSpec fullSolveBytesModelSpec
      f as bs hmem xs m Q X
  refine FullM5.m5Env_moduleOk.respec_tail hsplit hagree fun fn hfn xs m Q X hs => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl
  · exact wp_noExit_lift (kissat_solve_bytes_m5_model_wp m5SoundEnv
      (FullM5.mkM5Env_init_state_m5 fullSolveBytesModelSpec)
      (FullM5.mkM5Env_parse_body fullSolveBytesModelSpec)
      (FullM5.mkM5Env_preprocess_m5 fullSolveBytesModelSpec)
      (FullM5.mkM5Env_search_m5 fullSolveBytesModelSpec)
      (FullM5.mkM5Env_extend fullSolveBytesModelSpec)
      (FullM5.mkM5Env_check_model fullSolveBytesModelSpec)
      xs m Q _ ((FullM5.mkM5Env_solve_bytes_m5_iff fullSolveBytesModelSpec).mp hs))
  · exact wp_noExit_lift (FullM5.m5_solve_bytes_fwd_wp m5SoundEnv
      (S := fullSolveBytesModelSpec)
      (fun a m' Q' X' h' =>
        (FullM5.mkM5Env_solve_bytes_m5_iff fullSolveBytesModelSpec).mpr h')
      xs m Q _ ((FullM5.mkM5Env_solve_bytes_iff fullSolveBytesModelSpec).mp hs))

/-- Source-level UNSAT + constructive SAT model soundness of Unified M5 `kissat_solve_bytes`
under `m5SoundEnv` (`270` functions): `r = 20` certifies `cnf.Unsat` and `r = 10` certifies
`cnf.Sat (readModelFromWork m' work_ptr)`. -/
theorem m5_solve_bytes_model_correct
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m5SoundEnv FullM5.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
          cnf.Sat (readModelFromWork m' work_ptr)) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X := by
  have hsplit : FullM5.m5Module.fns =
      FullM5.m5Fns.take 269 ++ FullM5.m5SolveBytesFwdFn :: [] := by
    change FullM5.m5Fns = FullM5.m5Fns.take 269 ++ [FullM5.m5SolveBytesFwdFn]
    have hdrop : FullM5.m5Fns.drop 269 = [FullM5.m5SolveBytesFwdFn] := by t_kernel_rfl
    rw [← hdrop, List.take_append_drop]
  exact (m5SoundEnv_moduleOk.fnsOk _ _ _ hsplit).2.2 _ m _ X
    (m5SoundEnv_solve_bytes_model
      ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, fun _ m' hdom hu hmod hm' =>
        ⟨hdom, hu, fun h10 =>
          let ⟨cnf, hp, hf⟩ := hmod h10
          ⟨cnf, hp, hf emp m' (by rw [sep_emp])⟩, hm'⟩⟩)

/-- Source-level UNSAT + existential SAT soundness of Unified M5 `kissat_solve_bytes` under
`m5SoundEnv` (`270` functions). -/
theorem m5_solve_bytes_sound_correct
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m5SoundEnv FullM5.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  wp_mono
    (fun (_, ()) _ ⟨hdom, hu, hmod, hm'⟩ =>
      ⟨hdom, hu, fun h10 =>
        let ⟨cnf, hp, hsat⟩ := hmod h10
        ⟨cnf, hp, cnf_not_unsat_of_sat hsat⟩, hm'⟩)
    (fun _ _ _ _ h => h) _ m
    (m5_solve_bytes_model_correct hcfit hwfit hm)

end LeanQbe.T.Examples.Kissat
