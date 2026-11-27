/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Logic.Bytes
public import LeanQbe.T.Logic.MemLemmas
public import Kraken.Mem
public import Kraken.Separation

/-!
# Kissat End-to-End UNSAT + SAT Soundness Bridge (`Proof.Spec.SatNv`)

1. Generic `LeanQbe.T.ModuleOk.respec_tail` transport.
2. Constructive workspace model readers (`readModelFromWork`, `readModelFromWorkM6`), host framing
   lemmas, and `runKissatCheckModel_sat_exact`.
3. `M6Hdr` region alignment & `kissat_check_model` bridges (`m6HdrMem_to_checkModel`,
   `checkModel_post_to_m6_region`, `sat_of_runKissatCheckModel_m6`).
4. Top-level `FullM6` phase/solver contracts (`fullM6PreprocessSpec`, `fullM6SearchSpec`,
   `fullM6SolveBytesSpec`, `fullM6SolvePreCheckSpec`), `fullM6_extend_check_cont`, and
   host-memory combinators (`fullM6_solve_bytes_sound_combinator`, `fullM6_host_sound_lift`).
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

namespace LeanQbe.T.Examples.Kissat.Proof.Spec

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src
open Kraken.Bedrock2.Test

/-- Exact decision specification of `kissat_check_model(cnf_ptr, cnf_end, d, vals, mv_max)`. -/
@[expose] def kissatCheckModelExactSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cend, d, vals_ptr, mv_max_v, ()) m Q _ =>
    ∃ (mv0 nc0 cur0 val0 : BitVec 64) (cnfBytes valsBytes : List UInt8) (mv_max : Nat)
      (R : Mem 64 → Prop),
      cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
      mv_max_v = BitVec.ofNat 64 mv_max ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      mv_max < 2 ^ 64 ∧
      2 * mv_max ≤ valsBytes.length ∧
      valsBytes.length ≤ 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv0 nc0 cur0 val0 ⋆
        bytes vals_ptr valsBytes ⋆ R) m ∧
      ∀ (r mv' nc' cur' val' : BitVec 64) (m' : Mem 64),
        r = (if runKissatCheckModel cnfBytes valsBytes mv_max then 1#64 else 0#64) →
        (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv' nc' cur' val' ⋆
          bytes vals_ptr valsBytes ⋆ R) m' →
        Q (r, ()) m'


/-! ## 1. Constructive `readModelFromWork` & Pure `runKissatCheckModel` Exactness Bridge -/

/-- Read the 1-based DIMACS variable `v`'s Boolean assignment from workspace memory `m'` at
`work_ptr`, indirecting through `h->values` at `work_ptr + fullAlignPad work_ptr + 64`.
Survives future `FullHdr` tail extensions because `h->values` sits at fixed offset `64`. -/
@[expose] def readModelFromWork (m' : Mem 64) (work_ptr : BitVec 64) (v : Nat) : Bool :=
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
    rw [checkClauseValsAux] at h; rw [parseClauseAux_eq_nextLitPure]
    cases hn : nextLitPure mv bs with
    | err => rw [hn] at h; cases h
    | endClause rest' =>
      rw [hn] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine ⟨CNF.Clause.ofLiterals acc.reverse, rfl, ?_, fun ht => ?_⟩
      · intro lit hlit
        simp only [CNF.Clause.literals_ofLiterals, List.mem_reverse] at hlit
        exact hacc_bd lit hlit
      · obtain ⟨lit, hmem, heq⟩ := hsat ht; rw [CNF.Clause.sat_iff_exists_mem_eq]
        exact ⟨lit, by rw [← CNF.Clause.mem_literals_iff]; simp [hmem], heq⟩
    | lit l rest' =>
      rw [hn] at h
      have ⟨hlt, _, _⟩ := nextLitPure_lit_bounds hn
      have hl_bd : 1 ≤ (kissatLitToDimacsLiteral l).1 ∧
          (kissatLitToDimacsLiteral l).1 ≤ mv := by
        simp only [kissatLitToDimacsLiteral, litVar]; omega
      refine ih (fun lit hlit => ?_) (fun ht => ?_) h
      · rcases List.mem_cons.mp hlit with rfl | hmem; exact hl_bd; exact hacc_bd lit hmem
      · rcases Bool.or_eq_true _ _ |>.mp ht with h1 | h2
        · obtain ⟨lit, hmem, heq⟩ := hsat h1; exact ⟨lit, List.mem_cons_of_mem _ hmem, heq⟩
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
      rcases p with ⟨sat, rest⟩; rw [hc] at h
      cases sat with
      | false => cases h
      | true =>
        obtain ⟨cl, hcl, hcl_bd, hcl_sat⟩ :=
          checkClauseValsAux_sat_exact (acc := []) (by simp) (by simp) hc
        obtain ⟨cnf, hpc', hbd', hsat'⟩ := ih (fun c hc_mem lit hlit => by
          rcases CNF.mem_add.mp hc_mem with rfl | hmem
          · exact hcl_bd lit hlit
          · exact hacc_bd c hmem lit hlit)
          (CNF.sat_add.mpr ⟨hcl_sat rfl, hacc_sat⟩) h
        exact ⟨cnf, by simp [parseClauses, show parseClause mv bs = some (cl, rest) from hcl, hpc'],
          hbd', hsat'⟩

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


/-! ## 1. `M6Hdr` Alignment, Prefix Layout (`3,456 B`), and `readModelFromWorkM6` -/

/-- Aligned base address of the `M6Hdr` workspace (`work_ptr + fullAlignPad work_ptr`). -/
@[expose] def fullM6WorkBase (work_ptr : BitVec 64) : BitVec 64 :=
  work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr)

/-- Aligned `FullHdr *h` pointer placed `fullM6ExtBytes = 2304` bytes past `fullM6WorkBase`. -/
@[expose] def fullM6WorkHdr (work_ptr : BitVec 64) : BitVec 64 :=
  fullM6WorkBase work_ptr + BitVec.ofNat 64 fullM6ExtBytes

/-- Byte address of the `h->values` field (`fullM6WorkBase + 2368#64`, i.e., `2304 + 64`). -/
@[expose] def fullM6ValuesFieldPtr (work_ptr : BitVec 64) : BitVec 64 :=
  fullM6WorkBase work_ptr + BitVec.ofNat 64 (fullM6ExtBytes + 64)

theorem fullM6WorkHdr_add_64 (work_ptr : BitVec 64) :
    fullM6WorkHdr work_ptr + 64#64 = fullM6ValuesFieldPtr work_ptr := by
  unfold fullM6WorkHdr fullM6ValuesFieldPtr fullM6WorkBase fullM6ExtBytes
  rw [BitVec.add_assoc]
  rfl

theorem m6ExtAddr_fullM6WorkHdr (work_ptr : BitVec 64) :
    m6ExtAddr (fullM6WorkHdr work_ptr) = fullM6WorkBase work_ptr := by
  rw [m6ExtAddr_eq]
  unfold fullM6WorkHdr fullM6ExtBytes
  exact BitVec.add_sub_cancel (fullM6WorkBase work_ptr) (BitVec.ofNat 64 2304)

theorem fullM6WorkBase_toNat_lt {work_ptr : BitVec 64} {wlen : Nat}
    (hle : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen)
    (hfit : work_ptr.toNat + wlen < 2 ^ 64) :
    (fullM6WorkBase work_ptr).toNat = work_ptr.toNat + fullAlignPad work_ptr := by
  unfold fullM6WorkBase
  exact bv_add_ofNat_toNat (by omega)

theorem fullAlignPad_fullM6WorkBase {work_ptr : BitVec 64} {wlen : Nat}
    (hle : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen)
    (hfit : work_ptr.toNat + wlen < 2 ^ 64) :
    fullAlignPad (fullM6WorkBase work_ptr) = 0 := by
  have hbt := fullM6WorkBase_toNat_lt hle hfit
  have hmod : (fullM6WorkBase work_ptr).toNat % 8 = 0 := by
    rw [hbt]
    unfold fullAlignPad
    split <;> omega
  unfold fullAlignPad
  simp [hmod]

theorem fullAlignPad_fullM6WorkHdr {work_ptr : BitVec 64} {wlen : Nat}
    (hle : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen)
    (hfit : work_ptr.toNat + wlen < 2 ^ 64) :
    fullAlignPad (fullM6WorkHdr work_ptr) = 0 := by
  have hbt := fullM6WorkBase_toNat_lt hle hfit
  have hhdr : (fullM6WorkHdr work_ptr).toNat =
      (fullM6WorkBase work_ptr).toNat + fullM6ExtBytes := by
    unfold fullM6WorkHdr fullM6ExtBytes fullM6HdrTotalBytes at *
    exact bv_add_ofNat_toNat (by omega)
  have hmod : (fullM6WorkHdr work_ptr).toNat % 8 = 0 := by
    rw [hhdr, hbt]
    unfold fullM6ExtBytes fullAlignPad
    split <;> omega
  unfold fullAlignPad
  simp [hmod]

/-- Constructive host model reader for `M6Hdr` (`3,456 B` prefix: `2,304 B` extension +
`1,152 B` `FullHdr`). Reads `vals_ptr = h->values` at `work_ptr + fullAlignPad work_ptr + 2368#64`
and tests signed positive `i8` polarity (`1..127`) at `vals_ptr + 2 * (v - 1)`. -/
@[expose] def readModelFromWorkM6 (m' : Mem 64) (work_ptr : BitVec 64) (v : Nat) : Bool :=
  if v == 0 then false
  else
    match loadVal m' i64
        (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) + 2368#64) with
    | none => false
    | some vals_ptr =>
      match loadVal m' i8 (vals_ptr + BitVec.ofNat 64 (2 * (v - 1))) with
      | none => false
      | some b => i8BytePos { toBitVec := b }

theorem readModelFromWorkM6_eq (m' : Mem 64) (work_ptr : BitVec 64) (v : Nat) :
    readModelFromWorkM6 m' work_ptr v =
      if v == 0 then false
      else
        match loadVal m' i64
            (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) + 2368#64) with
        | none => false
        | some vals_ptr =>
          match loadVal m' i8 (vals_ptr + BitVec.ofNat 64 (2 * (v - 1))) with
          | none => false
          | some b => i8BytePos { toBitVec := b } := rfl

theorem readModelFromWorkM6_zero (m' : Mem 64) (work_ptr : BitVec 64) :
    readModelFromWorkM6 m' work_ptr 0 = false := by
  rw [readModelFromWorkM6_eq]; simp

theorem readModelFromWorkM6_frame {m' M : Mem 64} {F : Mem 64 → Prop}
    {work_ptr vals_ptr : BitVec 64} {v : Nat} {b : BitVec 8}
    (hM : (Eq m' ⋆ F) M)
    (hvptr : loadVal m' i64
      (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) + 2368#64) = some vals_ptr)
    (hb : loadVal m' i8 (vals_ptr + BitVec.ofNat 64 (2 * (v - 1))) = some b) :
    readModelFromWorkM6 M work_ptr v =
      if v == 0 then false else i8BytePos (UInt8.ofBitVec b) := by
  rw [readModelFromWorkM6_eq]
  have hvptr' : loadVal M i64
      (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) + 2368#64) = some vals_ptr :=
    loadVal_frame hM hvptr
  have hb' : loadVal M i8 (vals_ptr + BitVec.ofNat 64 (2 * (v - 1))) = some b :=
    loadVal_frame hM hb
  rw [hvptr']
  dsimp only
  rw [hb']

theorem readModelFromWorkM6_eq_readModelFromWork (m' : Mem 64) (work_ptr : BitVec 64)
    (halign : fullAlignPad (fullM6WorkHdr work_ptr) = 0) (v : Nat) :
    readModelFromWorkM6 m' work_ptr v = readModelFromWork m' (fullM6WorkHdr work_ptr) v := by
  rw [readModelFromWorkM6_eq, readModelFromWork_eq, halign]
  have haddr : fullM6WorkHdr work_ptr + BitVec.ofNat 64 0 + 64#64 =
      work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) + 2368#64 := by
    unfold fullM6WorkHdr fullM6WorkBase fullM6ExtBytes
    simp only [BitVec.add_zero, BitVec.add_assoc]
    rfl
  rw [haddr]

theorem readModelFromWorkM6_eq_readModelFromWork_of_lt (m' : Mem 64) {work_ptr : BitVec 64}
    {wlen : Nat} (hle : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen)
    (hfit : work_ptr.toNat + wlen < 2 ^ 64) (v : Nat) :
    readModelFromWorkM6 m' work_ptr v = readModelFromWork m' (fullM6WorkHdr work_ptr) v :=
  readModelFromWorkM6_eq_readModelFromWork m' work_ptr
    (fullAlignPad_fullM6WorkHdr hle hfit) v

/-! ## 2. `M6Hdr` Region Alignment, Separation Framing, and Check-Model Bridges -/

/-- Split `region work_ptr wlen` into leading alignment padding `[work_ptr .. +pad)` and the
8-byte-aligned `M6Hdr` workspace `[fullM6WorkBase work_ptr .. +(wlen - pad))`. -/
theorem region_work_to_m6_workBase {work_ptr : BitVec 64} {wlen : Nat} {m : Mem 64}
    (hle : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen) (hfit : wlen ≤ 2 ^ 64)
    (hm : region work_ptr wlen m) :
    (region work_ptr (fullAlignPad work_ptr) ⋆
      region (fullM6WorkBase work_ptr) (wlen - fullAlignPad work_ptr)) m := by
  have heq : fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr) = wlen := by omega
  exact (congrFun (region_merge_eq heq hfit) m).mpr hm

/-- Collapse leading alignment padding + `FullM6HdrMem c ext s` (`3,456 B` header + arrays) back
to `region work_ptr wlen`. -/
theorem region_work_from_m6_hdrMem {work_ptr : BitVec 64} {wlen : Nat} {c : FullCfg}
    {ext : List (BitVec 64)} {s : FullState} {m : Mem 64}
    (hle : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen) (hfit : wlen ≤ 2 ^ 64)
    (hhdr : c.hdr = fullM6WorkHdr work_ptr)
    (hav : c.avail = wlen - fullAlignPad work_ptr - fullM6ExtBytes)
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (region work_ptr (fullAlignPad work_ptr) ⋆ FullM6HdrMem c ext s) m) :
    region work_ptr wlen m := by
  have hreg : (region work_ptr (fullAlignPad work_ptr) ⋆
      region (fullM6WorkBase work_ptr) (wlen - fullAlignPad work_ptr)) m := by
    refine sep_mono_r (fun _ h => ?_) hm
    have hr := fullM6HdrMem_to_region hcfg hext hlen h
    rw [hhdr, m6ExtAddr_fullM6WorkHdr, hav] at hr
    have hsz : fullM6ExtBytes + (wlen - fullAlignPad work_ptr - fullM6ExtBytes) =
        wlen - fullAlignPad work_ptr := by
      unfold fullM6HdrTotalBytes fullM6ExtBytes at *; omega
    rwa [hsz] at hr
  have heq : fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr) = wlen := by omega
  exact (congrFun (region_merge_eq heq hfit) m).mp hreg

theorem m6HdrMem_to_checkModel {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c)
    (hm : (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s ⋆ R) m) :
    (bytes cnf_ptr cnfBytes ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆
      bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
      (FullCheckRest c s ⋆ array64 (c.hdr - 2304) ext ⋆ R)) m := by
  have hm0 : (FullM6HdrMem c ext s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
  rw [fullM6HdrMem_iff] at hm0
  have hm1 : (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆
      (array64 (c.hdr - 2304) ext ⋆ R)) m := sep_ac hm0
  exact sep_ac (fullMem_to_checkModel hlen hm1)

theorem checkModel_post_to_m6_region {work_ptr : BitVec 64} {wlen : Nat}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {mv' nc' cur' val' cnf_ptr : BitVec 64} {cnfBytes : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hle : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen) (hfit : wlen ≤ 2 ^ 64)
    (hhdr : c.hdr = fullM6WorkHdr work_ptr)
    (hav : c.avail = wlen - fullAlignPad work_ptr - fullM6ExtBytes)
    (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (bytes cnf_ptr cnfBytes ⋆ dimacsState c.hdr mv' nc' cur' val' ⋆
      bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
      (FullCheckRest c s ⋆ array64 (c.hdr - 2304) ext ⋆
        region work_ptr (fullAlignPad work_ptr) ⋆ R)) m) :
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m := by
  have hm0 : (bytes cnf_ptr cnfBytes ⋆ dimacsState c.hdr mv' nc' cur' val' ⋆
      bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
      (FullCheckRest c s ⋆ (array64 (c.hdr - 2304) ext ⋆
        region work_ptr (fullAlignPad work_ptr) ⋆ R))) m := sep_ac hm
  have hm1 := checkModel_post_to_region hlen hm0
  have hsub : c.hdr - 2304 = fullM6WorkBase work_ptr := by
    rw [← m6ExtAddr_eq, hhdr, m6ExtAddr_fullM6WorkHdr]
  have hreg_ext : ∀ f, array64 (c.hdr - 2304) ext f →
      region (fullM6WorkBase work_ptr) fullM6ExtBytes f := fun f hf => by
    have hext_len := hext.len
    have hr := array_to_region (t := i64) (a := c.hdr - 2304) (xs := ext)
      (by simp only [Ty.bytes, Ty.size]; omega) ((array64_eq_array _ ext) ▸ hf)
    rw [hsub] at hr
    simpa [Ty.bytes, Ty.size, hext_len, fullM6ExtBytes] using hr
  have hm1a : ((bytes cnf_ptr cnfBytes ⋆ R) ⋆ (region work_ptr (fullAlignPad work_ptr) ⋆
      (array64 (c.hdr - 2304) ext ⋆ region c.hdr c.avail))) m := sep_ac hm1
  have hm2 : ((bytes cnf_ptr cnfBytes ⋆ R) ⋆ (region work_ptr (fullAlignPad work_ptr) ⋆
      (region (fullM6WorkBase work_ptr) fullM6ExtBytes ⋆
        region (fullM6WorkHdr work_ptr) c.avail))) m :=
    sep_mono_r (fun _ => sep_mono_r (sep_mono2 hreg_ext (fun _ h => by rwa [← hhdr]))) hm1a
  have hsum : fullM6ExtBytes + c.avail = wlen - fullAlignPad work_ptr := by
    rw [hav]; unfold fullM6HdrTotalBytes fullM6ExtBytes at *; omega
  rw [show (region (fullM6WorkBase work_ptr) fullM6ExtBytes ⋆
      region (fullM6WorkHdr work_ptr) c.avail) =
      region (fullM6WorkBase work_ptr) (wlen - fullAlignPad work_ptr) from
    region_merge_eq (a := fullM6WorkBase work_ptr) hsum (by omega)] at hm2
  have heq : fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr) = wlen := by omega
  exact sep_ac (sep_mono_r (fun _ hr => (congrFun (region_merge_eq heq hfit) _).mp hr) hm2)

private theorem readModelFromWorkM6_of_loads {c : FullCfg} {s : FullState}
    {m' M : Mem 64} {F : Mem 64 → Prop} {work_ptr : BitVec 64}
    (hhdr : c.hdr = fullM6WorkHdr work_ptr) (hlen : s.LengthsOk c)
    (hvptr_hdr : loadVal m' i64 (c.hdr + 64#64) = some c.pVals)
    (hm_arr : ∀ {i} (hi : i < s.core.vals.length),
      loadVal m' i8 (c.pVals + BitVec.ofNat 64 i) = some s.core.vals[i])
    (hM : (Eq m' ⋆ F) M) {v : Nat} (hv1 : 1 ≤ v) (hv2 : v ≤ c.mv) :
    readModelFromWorkM6 M work_ptr v =
      i8BytePos ((s.core.vals.map UInt8.ofBitVec).getD (2 * (v - 1)) 0) := by
  have hvptr : loadVal m' i64
      (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) + 2368#64) = some c.pVals := by
    have ha : work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) + 2368#64 = c.hdr + 64#64 := by
      rw [hhdr, fullM6WorkHdr_add_64]; rfl
    rwa [ha]
  have hidx_lt : 2 * (v - 1) < s.core.vals.length := by
    have := hlen.core_ok.vals_len; have := hlen.core_ok.cur_vars_ge
    have := hlen.core_ok.cur_vars_le; omega
  rw [readModelFromWorkM6_frame hM hvptr (hm_arr hidx_lt), beq_false_of_ne (by omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx_lt]

/-- From `FullM6HdrMem c ext s` framed in `m'` and any extended host memory `M` satisfying
`(Eq m' ⋆ F) M`, `readModelFromWorkM6 M work_ptr v` equals the signed polarity of
`s.core.vals[2 * (v - 1)]` for every `1 ≤ v ≤ c.mv`. -/
theorem readModelFromWorkM6_of_vals {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {m' M : Mem 64} {R F : Mem 64 → Prop} {work_ptr : BitVec 64}
    (hhdr : c.hdr = fullM6WorkHdr work_ptr) (hlen : s.LengthsOk c)
    (hm' : (FullM6HdrMem c ext s ⋆ R) m') (hM : (Eq m' ⋆ F) M)
    {v : Nat} (hv1 : 1 ≤ v) (hv2 : v ≤ c.mv) :
    readModelFromWorkM6 M work_ptr v =
      i8BytePos ((s.core.vals.map UInt8.ofBitVec).getD (2 * (v - 1)) 0) := by
  rw [fullM6HdrMem_iff] at hm'
  have hvptr_hdr : loadVal m' i64 (c.hdr + 64#64) = some c.pVals := by
    have hl := fullHdrTailGet (c := c) (s := s) 4 (by decide) hm'
    simpa [BitVec.add_assoc, show (hdrTailWords c s)[4]'(by simp) = c.pVals from rfl]
      using hl
  have hmem_vals : (array (t := i8) c.pVals s.core.vals ⋆
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆
      array (t := i8) c.pLitMark s.core.lit_mark ⋆ array (t := i8) c.pMark s.core.mrk ⋆
      FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
      FullScratchArrays c s.scratch ⋆ c.pad ⋆ array64 (c.hdr - 2304) ext ⋆ R)) m' := by
    unfold FullMem FullCoreArrays FullCoreByteArrs at hm'; exact sep_ac hm'
  exact readModelFromWorkM6_of_loads hhdr hlen hvptr_hdr
    (fun {i} hi => by
      simpa [Ty.bytes, Ty.size] using loadVal_array (t := i8) (a := c.pVals) (xs := s.core.vals)
        (i := i) (by decide) hi hmem_vals) hM hv1 hv2

/-- Extract `readModelFromWorkM6 M work_ptr v` directly from the un-collapsed
`kissat_check_model` postcondition heap (`FullCheckRest c s` + `bytes c.pVals ...`). -/
theorem readModelFromWorkM6_of_checkModel_post {c : FullCfg} {s : FullState}
    {mv' nc' cur' val' : BitVec 64} {m' M : Mem 64} {R F : Mem 64 → Prop}
    {work_ptr : BitVec 64} (hhdr : c.hdr = fullM6WorkHdr work_ptr) (hlen : s.LengthsOk c)
    (hm' : (dimacsState c.hdr mv' nc' cur' val' ⋆
      bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆ FullCheckRest c s ⋆ R) m')
    (hM : (Eq m' ⋆ F) M) {v : Nat} (hv1 : 1 ≤ v) (hv2 : v ≤ c.mv) :
    readModelFromWorkM6 M work_ptr v =
      i8BytePos ((s.core.vals.map UInt8.ofBitVec).getD (2 * (v - 1)) 0) := by
  have hm_unfold : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      (dimacsState c.hdr mv' nc' cur' val' ⋆ bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
        array (t := i8) c.pLitMark s.core.lit_mark ⋆ array (t := i8) c.pMark s.core.mrk ⋆
        FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
        FullScratchArrays c s.scratch ⋆ c.pad ⋆ R)) m' := by
    unfold FullCheckRest at hm'; exact sep_ac hm'
  have hvptr_hdr : loadVal m' i64 (c.hdr + 64#64) = some c.pVals := by
    have hl := loadVal_array64 (a := c.hdr + 32) (xs := hdrTailWords c s) (i := 4)
      (by simp) hm_unfold
    have ha : c.hdr + 32 + BitVec.ofNat 64 (8 * 4) = c.hdr + 64#64 := by rw [BitVec.add_assoc]; rfl
    rwa [show (hdrTailWords c s)[4]'(by simp) = c.pVals from rfl, ha] at hl
  have hfit_vals : (i8).bytes * s.core.vals.length ≤ 2 ^ 64 := by
    have hmx := c.hmaxv; have := hlen.core_ok.vals_len; unfold dimacsBound at hmx
    simp only [Ty.bytes, Ty.size]; omega
  have hm_bytes : (bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
        dimacsState c.hdr mv' nc' cur' val' ⋆
        array (t := i8) c.pLitMark s.core.lit_mark ⋆ array (t := i8) c.pMark s.core.mrk ⋆
        FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
        FullScratchArrays c s.scratch ⋆ c.pad ⋆ R)) m' := sep_ac hm_unfold
  have hm_arr : (array (t := i8) c.pVals s.core.vals ⋆
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
        dimacsState c.hdr mv' nc' cur' val' ⋆
        array (t := i8) c.pLitMark s.core.lit_mark ⋆ array (t := i8) c.pMark s.core.mrk ⋆
        FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
        FullScratchArrays c s.scratch ⋆ c.pad ⋆ R)) m' :=
    sep_mono (fun _ hb => by
      unfold bytes at hb; subst hb; rw [← bytesOf_i8_eq_map]
      exact array_bytes (t := i8) c.pVals s.core.vals hfit_vals) hm_bytes
  exact readModelFromWorkM6_of_loads hhdr hlen hvptr_hdr
    (fun {i} hi => by
      simpa [Ty.bytes, Ty.size] using loadVal_array (t := i8) (a := c.pVals) (xs := s.core.vals)
        (i := i) (by decide) hi hm_arr) hM hv1 hv2

private theorem sat_of_vals_m6 {c : FullCfg} {s : FullState}
    {m' : Mem 64} {work_ptr : BitVec 64} {cnfBytes : List UInt8}
    (hchk : runKissatCheckModel cnfBytes (s.core.vals.map UInt8.ofBitVec) c.mv = true)
    (hrm : ∀ F M, (Eq m' ⋆ F) M → ∀ {v}, 1 ≤ v → v ≤ c.mv →
      readModelFromWorkM6 M work_ptr v =
        i8BytePos ((s.core.vals.map UInt8.ofBitVec).getD (2 * (v - 1)) 0)) :
    ∃ cnf, parseDimacs cnfBytes = some cnf ∧
      ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
      ∀ (F : Mem 64 → Prop) (M : Mem 64),
        (Eq m' ⋆ F) M → cnf.Sat (readModelFromWorkM6 M work_ptr) := by
  obtain ⟨cnf, mv, hp, _, hvars, hsat⟩ := runKissatCheckModel_sat_exact hchk
  have hnot := cnf_not_unsat_of_sat hsat
  refine ⟨cnf, hp, hnot.1, hnot.2, fun F M hM => ?_⟩
  rw [CNF.sat_iff_all_mem_sat] at hsat ⊢
  intro cl hcl
  obtain ⟨lit, hmem, heq⟩ := (CNF.Clause.sat_iff_exists_mem_eq).mp (hsat cl hcl)
  have hb := hvars cl hcl lit hmem
  refine (CNF.Clause.sat_iff_exists_mem_eq).mpr ⟨lit, hmem, ?_⟩
  rw [hrm F M hM hb.1 (by omega)]
  simpa [beq_false_of_ne (by omega : lit.1 ≠ 0)] using heq

/-- Zero-drag SAT soundness from concrete `runKissatCheckModel = true` over `FullM6HdrMem`:
produces parsed `cnf`, constructive host-framed `cnf.Sat (readModelFromWorkM6 M work_ptr)`,
and `¬ cnf.Unsat`. -/
theorem sat_of_runKissatCheckModel_m6 {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {m' : Mem 64} {R : Mem 64 → Prop} {work_ptr : BitVec 64} {cnfBytes : List UInt8}
    (hhdr : c.hdr = fullM6WorkHdr work_ptr) (hlen : s.LengthsOk c)
    (hm' : (FullM6HdrMem c ext s ⋆ R) m')
    (hchk : runKissatCheckModel cnfBytes (s.core.vals.map UInt8.ofBitVec) c.mv = true) :
    ∃ cnf, parseDimacs cnfBytes = some cnf ∧
      ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
      ∀ (F : Mem 64 → Prop) (M : Mem 64),
        (Eq m' ⋆ F) M → cnf.Sat (readModelFromWorkM6 M work_ptr) :=
  sat_of_vals_m6 hchk fun _ _ hM _ hv1 hv2 => readModelFromWorkM6_of_vals hhdr hlen hm' hM hv1 hv2

/-- Zero-drag SAT soundness directly from the post-`kissat_check_model` heap. -/
theorem sat_of_checkModel_post_m6 {c : FullCfg} {s : FullState}
    {mv' nc' cur' val' : BitVec 64} {m' : Mem 64} {R : Mem 64 → Prop}
    {work_ptr : BitVec 64} {cnfBytes : List UInt8}
    (hhdr : c.hdr = fullM6WorkHdr work_ptr) (hlen : s.LengthsOk c)
    (hm' : (dimacsState c.hdr mv' nc' cur' val' ⋆
      bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆ FullCheckRest c s ⋆ R) m')
    (hchk : runKissatCheckModel cnfBytes (s.core.vals.map UInt8.ofBitVec) c.mv = true) :
    ∃ cnf, parseDimacs cnfBytes = some cnf ∧
      ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
      ∀ (F : Mem 64 → Prop) (M : Mem 64),
        (Eq m' ⋆ F) M → cnf.Sat (readModelFromWorkM6 M work_ptr) :=
  sat_of_vals_m6 hchk fun _ _ hM _ hv1 hv2 =>
    readModelFromWorkM6_of_checkModel_post hhdr hlen hm' hM hv1 hv2

/-! ## 3. `FullM6` Phase & Top-Level Specifications -/

/-- Generic `M6Hdr`-aware preprocessing contract (operating over `FullM6HdrInv` and
`FullM6HdrMem` while permitting M4 compaction via `FullCfgCompat`). -/
@[expose] def fullM6PreprocessSpec : Spec [i64] [i64] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0 ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r c' ext' s' m',
        FullCfgCompat c c' → s'.LengthsOk c' →
        FullM6HdrCfgOk c' → M6HdrExtOk ext' →
        (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 20#64 → F0.Unsat) →
        (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
        (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
        (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Generic `M6Hdr`-aware CDCL search contract (operating over `FullM6HdrInv` and
`FullM6HdrMem` while permitting M4 compaction via `FullCfgCompat`). -/
@[expose] def fullM6SearchSpec : Spec [i64] [i64] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0 ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r c' ext' s' m',
        FullCfgCompat c c' → s'.LengthsOk c' →
        FullM6HdrCfgOk c' → M6HdrExtOk ext' →
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → F0.Unsat) →
        (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
        (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m'

theorem fullM6PreprocessSpec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hcl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r c' ext' s' m',
      FullCfgCompat c c' → s'.LengthsOk c' →
      FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m') :
    fullM6PreprocessSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩

theorem fullM6PreprocessSpec_elim {h : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : fullM6PreprocessSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0 ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r c' ext' s' m',
        FullCfgCompat c c' → s'.LengthsOk c' →
        FullM6HdrCfgOk c' → M6HdrExtOk ext' →
        (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 20#64 → F0.Unsat) →
        (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
        (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
        (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m' :=
  hs

theorem fullM6PreprocessSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : fullM6PreprocessSpec xs m Q X) :
    fullM6PreprocessSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem fullM6SearchSpec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hcl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r c' ext' s' m',
      FullCfgCompat c c' → s'.LengthsOk c' →
      FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) →
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m') :
    fullM6SearchSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩

theorem fullM6SearchSpec_elim {h : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : fullM6SearchSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0 ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r c' ext' s' m',
        FullCfgCompat c c' → s'.LengthsOk c' →
        FullM6HdrCfgOk c' → M6HdrExtOk ext' →
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → F0.Unsat) →
        (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
        (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m' :=
  hs

theorem fullM6SearchSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : fullM6SearchSpec xs m Q X) : fullM6SearchSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h


/-- Lift `fullPreprocessSpec` precondition to `fullM6PreprocessSpec`. -/
theorem fullM6PreprocessSpec_of_full {a : Tup Val [i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : fullM6PreprocessSpec a m Q X) :
    fullPreprocessSpec a m Q X := by
  rcases a with ⟨hptr, ⟨⟩⟩
  obtain ⟨c, F0, ext, s, R, rfl, hinv, hlvl, hm, hQ⟩ := h
  rw [fullM6HdrMem_iff] at hm
  refine ⟨c, F0, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hinv.sparse, hlvl, hm,
    fun r s' m' hlen hdom hfuel h20 h1 h10 hm' => ?_⟩
  have hcmp : FullCfgCompat c c :=
    ⟨rfl, rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hm_m6 : (FullM6HdrMem c ext s' ⋆ R) m' := (fullM6HdrMem_iff c ext s' R m').mpr hm'
  exact hQ r c ext s' m' hcmp hlen hinv.cfgOk hinv.extOk hdom hfuel h20
    (fun h1' => let x := h1 h1'; ⟨FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk x.1, x.2⟩)
    h10 hm_m6

/-- Lift `fullSearchSpec` precondition to `fullM6SearchSpec`. -/
theorem fullM6SearchSpec_of_full {a : Tup Val [i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : fullM6SearchSpec a m Q X) :
    fullSearchSpec a m Q X := by
  rcases a with ⟨hptr, ⟨⟩⟩
  obtain ⟨c, F0, ext, s, R, rfl, hinv, hlvl, hm, hQ⟩ := h
  rw [fullM6HdrMem_iff] at hm
  refine ⟨c, F0, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hinv.sparse, hlvl, hm,
    fun r s' m' hlen hdom h20 h10 hm' => ?_⟩
  have hcmp : FullCfgCompat c c :=
    ⟨rfl, rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hm_m6 : (FullM6HdrMem c ext s' ⋆ R) m' := (fullM6HdrMem_iff c ext s' R m').mpr hm'
  exact hQ r c ext s' m' hcmp hlen hinv.cfgOk hinv.extOk hdom h20 h10 hm_m6

/-- Core `M6Hdr` UNSAT-only `kissat_solve_bytes` contract (`3,456 B` workspace threshold
`fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen`) with deterministic level-0
unit-contradiction non-vacuity (`UnitUnsatTrace → r = 20#64`). -/
@[expose] def fullM6SolveBytesCoreSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (∀ mv nc i0,
          cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
          fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen →
          i0 ≤ cnfBytes.length →
          parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
          r = 20#64) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
        Q (r, ()) m'

/-- UNSAT-only top-level contract for `M6Hdr` `kissat_solve_bytes` (`0 | 10 | 20`, frame `R`). -/
@[expose] def fullM6SolveBytesUnsatSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, _fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
        Q (r, ()) m'

/-- Non-framed UNSAT + SAT `M6Hdr` soundness specification using `readModelFromWorkM6`. -/
@[expose] def fullM6SolveBytesSoundSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, _fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
          cnf.Sat (readModelFromWorkM6 m' work_ptr)) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
        Q (r, ()) m'

/-- Host-framed UNSAT + SAT `M6Hdr` soundness specification quantifying over arbitrary host
extensions `(Eq m' ⋆ F) M`. -/
@[expose] def fullM6SolveBytesModelSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, _fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
          ∀ (F : Mem 64 → Prop) (M : Mem 64),
            (Eq m' ⋆ F) M → cnf.Sat (readModelFromWorkM6 M work_ptr)) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
        Q (r, ()) m'

/-- Combined host-framed UNSAT+SAT + deterministic level-0 `UnitUnsatTrace` specification for
`M6Hdr` solvers. -/
@[expose] def fullM6SolveBytesCoreModelSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
          ∀ (F : Mem 64 → Prop) (M : Mem 64),
            (Eq m' ⋆ F) M → cnf.Sat (readModelFromWorkM6 M work_ptr)) →
        (∀ mv nc i0,
          cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
          fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen →
          i0 ≤ cnfBytes.length →
          parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
          r = 20#64) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
        Q (r, ()) m'

/-- Canonical top-level `FullM6` specification (`fullM6SolveBytesModelSpec`). -/
abbrev fullM6SolveBytesSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fullM6SolveBytesModelSpec

theorem fullM6SolveBytesSpec_intro {cnf_ptr work_ptr fuel : BitVec 64}
    {cnfBytes : List UInt8} {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m)
    (hQ : ∀ r m',
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
      (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        ∀ (F : Mem 64 → Prop) (M : Mem 64),
          (Eq m' ⋆ F) M → cnf.Sat (readModelFromWorkM6 M work_ptr)) →
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' → Q (r, ()) m') :
    fullM6SolveBytesSpec
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ())
      m Q X :=
  ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, hQ⟩

theorem fullM6SolveBytesCoreModelSpec_intro {cnf_ptr work_ptr fuel : BitVec 64}
    {cnfBytes : List UInt8} {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m)
    (hQ : ∀ r m',
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
      (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        ∀ (F : Mem 64 → Prop) (M : Mem 64),
          (Eq m' ⋆ F) M → cnf.Sat (readModelFromWorkM6 M work_ptr)) →
      (∀ mv nc i0,
        cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
        fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen →
        i0 ≤ cnfBytes.length →
        parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
        UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
        r = 20#64) →
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' → Q (r, ()) m') :
    fullM6SolveBytesCoreModelSpec
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ())
      m Q X :=
  ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, hQ⟩

theorem fullM6SolveBytesCoreModelSpec_elim {cnf_ptr cnf_len work_ptr work_len fuel : BitVec 64}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : fullM6SolveBytesCoreModelSpec (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q X) :
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
          ∀ (F : Mem 64 → Prop) (M : Mem 64),
            (Eq m' ⋆ F) M → cnf.Sat (readModelFromWorkM6 M work_ptr)) →
        (∀ mv nc i0, cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
          fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen →
          i0 ≤ cnfBytes.length → parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
          r = 20#64) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' → Q (r, ()) m' :=
  hs

theorem fullM6SolveBytesCoreModelSpec_monoX
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : fullM6SolveBytesCoreModelSpec xs m Q X) :
    fullM6SolveBytesCoreModelSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, _, ⟨⟩⟩; exact h

theorem fullM6SolveBytesSpec_elim {cnf_ptr cnf_len work_ptr work_len fuel : BitVec 64}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : fullM6SolveBytesSpec (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q X) :
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m',
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
          ∀ (F : Mem 64 → Prop) (M : Mem 64),
            (Eq m' ⋆ F) M → cnf.Sat (readModelFromWorkM6 M work_ptr)) →
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' → Q (r, ()) m' :=
  hs

theorem fullM6SolveBytesSpec_monoX
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : fullM6SolveBytesSpec xs m Q X) : fullM6SolveBytesSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, _, ⟨⟩⟩; exact h

theorem fullM6SolveBytesSpec_of_soundSpec
    {a : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : fullM6SolveBytesSoundSpec a m Q X) :
    fullM6SolveBytesSpec a m Q X := by
  rcases a with ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, ⟨⟩⟩
  obtain ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm, hQ⟩ := h
  refine ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm, fun r m' hdom h20 h10 hm' => ?_⟩
  refine hQ r m' hdom h20 (fun hr => ?_) hm'
  obtain ⟨cnf, hp, hsat⟩ := h10 hr
  exact ⟨cnf, hp, hsat emp m' (by rw [Std.ExtHashMap.sep_emp])⟩

theorem fullM6SolveBytesSpec_of_unsatSpec
    {a : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : fullM6SolveBytesUnsatSpec a m Q X) :
    fullM6SolveBytesSpec a m Q X := by
  rcases a with ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, ⟨⟩⟩
  obtain ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm, hQ⟩ := h
  exact ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm, fun r m' hdom h20 _ hm' =>
    hQ r m' hdom h20 hm'⟩

theorem fullM6SolveBytesCoreSpec_of_unsatSpec
    {a : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : fullM6SolveBytesUnsatSpec a m Q X) :
    fullM6SolveBytesCoreSpec a m Q X := by
  rcases a with ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, ⟨⟩⟩
  obtain ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm, hQ⟩ := h
  exact ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm, fun r m' hdom h20 _ hm' =>
    hQ r m' hdom h20 hm'⟩

theorem fullM6SolveBytesCoreModelSpec_of_spec
    {a : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : fullM6SolveBytesSpec a m Q X) :
    fullM6SolveBytesCoreModelSpec a m Q X := by
  rcases a with ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, ⟨⟩⟩
  obtain ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm, hQ⟩ := h
  exact ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm, fun r m' hdom h20 h10 _ hm' =>
    hQ r m' hdom h20 h10 hm'⟩

theorem fullM6SolveBytesCoreModelSpec_of_coreSpec
    {a : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : fullM6SolveBytesCoreSpec a m Q X) :
    fullM6SolveBytesCoreModelSpec a m Q X := by
  rcases a with ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, ⟨⟩⟩
  obtain ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm, hQ⟩ := h
  exact ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm, fun r m' hdom h20 _ htr hm' =>
    hQ r m' hdom h20 htr hm'⟩

theorem fullM6_unsatSpec_of_solveBytesSpec_wp (Γ : Env)
    (solveBody : Func [i64, i64, i64, i64, i64] [i64])
    (hwp : ∀ (a : Tup Val [i64, i64, i64, i64, i64]) (m : Mem 64)
      (Q : Post [i64]) (X : XPost),
      fullM6SolveBytesSpec a m Q X → Func.wp Γ solveBody a m Q X) :
    ∀ a m Q X, fullM6SolveBytesUnsatSpec a m Q X → Func.wp Γ solveBody a m Q X :=
  fun a m Q X h => hwp a m Q X (fullM6SolveBytesSpec_of_unsatSpec h)

/-- Intermediate `FullM6` post-search / pre-extend invariant capturing the exact state handed
to `full_extend` and `kissat_check_model` at `r = 10#64`. -/
@[expose]
def FullM6PreCheckPost (cnf_ptr : BitVec 64) (cnfBytes : List UInt8) (work_ptr : BitVec 64)
    (wlen : Nat) (R : Mem 64 → Prop) (m' : Mem 64) (r : BitVec 64) : Prop :=
  (r = 0#64 ∧ (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') ∨
  (r = 20#64 ∧ (∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') ∨
  (r = 10#64 ∧ ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState),
    fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen ∧
    c.hdr = fullM6WorkHdr work_ptr ∧
    c.avail = wlen - fullAlignPad work_ptr - fullM6ExtBytes ∧
    FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    s.scratch.extend_len ≤ c.extend_cap ∧
    (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s ⋆
      region work_ptr (fullAlignPad work_ptr) ⋆ R) m')

/-- Pre-extend `M6Hdr` solver core contract feeding `fullM6_extend_check_cont` without
requiring SAT model-finding proofs inside preprocessing or CDCL search. -/
@[expose] def fullM6SolvePreCheckSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, _fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m', FullM6PreCheckPost cnf_ptr cnfBytes work_ptr wlen R m' r → Q (r, ()) m'

theorem FullM6PreCheckPost_of {cnf_ptr : BitVec 64} {cnfBytes : List UInt8}
    {work_ptr : BitVec 64} {wlen : Nat} {R : Mem 64 → Prop} {m' : Mem 64} {r : BitVec 64}
    (h : (r = 0#64 ∧ (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') ∨
      (r = 20#64 ∧ (∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') ∨
      (r = 10#64 ∧ ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState),
        fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen ∧
        c.hdr = fullM6WorkHdr work_ptr ∧
        c.avail = wlen - fullAlignPad work_ptr - fullM6ExtBytes ∧
        FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
        s.scratch.extend_len ≤ c.extend_cap ∧
        (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s ⋆
          region work_ptr (fullAlignPad work_ptr) ⋆ R) m')) :
    FullM6PreCheckPost cnf_ptr cnfBytes work_ptr wlen R m' r :=
  h

theorem FullM6PreCheckPost_elim {cnf_ptr : BitVec 64} {cnfBytes : List UInt8}
    {work_ptr : BitVec 64} {wlen : Nat} {R : Mem 64 → Prop} {m' : Mem 64} {r : BitVec 64}
    (h : FullM6PreCheckPost cnf_ptr cnfBytes work_ptr wlen R m' r) :
    (r = 0#64 ∧ (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') ∨
    (r = 20#64 ∧ (∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') ∨
    (r = 10#64 ∧ ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState),
      fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen ∧
      c.hdr = fullM6WorkHdr work_ptr ∧
      c.avail = wlen - fullAlignPad work_ptr - fullM6ExtBytes ∧
      FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      s.scratch.extend_len ≤ c.extend_cap ∧
      (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s ⋆
        region work_ptr (fullAlignPad work_ptr) ⋆ R) m') :=
  h

theorem FullM6PreCheckPost_of_zero {cnf_ptr : BitVec 64} {cnfBytes : List UInt8}
    {work_ptr : BitVec 64} {wlen : Nat} {R : Mem 64 → Prop} {m' : Mem 64}
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') :
    FullM6PreCheckPost cnf_ptr cnfBytes work_ptr wlen R m' 0#64 :=
  Or.inl ⟨rfl, hm⟩

theorem FullM6PreCheckPost_of_unsat {cnf_ptr : BitVec 64} {cnfBytes : List UInt8}
    {work_ptr : BitVec 64} {wlen : Nat} {R : Mem 64 → Prop} {m' : Mem 64}
    (hu : ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') :
    FullM6PreCheckPost cnf_ptr cnfBytes work_ptr wlen R m' 20#64 :=
  Or.inr (Or.inl ⟨rfl, hu, hm⟩)

theorem FullM6PreCheckPost_of_sat {cnf_ptr : BitVec 64} {cnfBytes : List UInt8}
    {work_ptr : BitVec 64} {wlen : Nat} {R : Mem 64 → Prop} {m' : Mem 64}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    (hle : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen)
    (hhdr : c.hdr = fullM6WorkHdr work_ptr)
    (hav : c.avail = wlen - fullAlignPad work_ptr - fullM6ExtBytes)
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hext_le : s.scratch.extend_len ≤ c.extend_cap)
    (hm : (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s ⋆
      region work_ptr (fullAlignPad work_ptr) ⋆ R) m') :
    FullM6PreCheckPost cnf_ptr cnfBytes work_ptr wlen R m' 10#64 :=
  Or.inr (Or.inr ⟨rfl, c, ext, s, hle, hhdr, hav, hcfg, hext, hlen, hext_le, hm⟩)

theorem fullM6SolvePreCheckSpec_of {cnf_ptr cnf_len work_ptr work_len fuel : BitVec 64}
    {cnfBytes : List UInt8} {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcl : cnf_len = BitVec.ofNat 64 cnfBytes.length) (hwl : work_len = BitVec.ofNat 64 wlen)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m)
    (hQ : ∀ r m', FullM6PreCheckPost cnf_ptr cnfBytes work_ptr wlen R m' r → Q (r, ()) m') :
    fullM6SolvePreCheckSpec (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q X :=
  ⟨cnfBytes, wlen, R, hcl, hwl, hcfit, hwfit, hm, hQ⟩

theorem fullM6SolvePreCheckSpec_elim {cnf_ptr cnf_len work_ptr work_len fuel : BitVec 64}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : fullM6SolvePreCheckSpec (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q X) :
    ∃ (cnfBytes : List UInt8) (wlen : Nat) (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧ work_len = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ work_ptr.toNat + wlen < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m ∧
      ∀ r m', FullM6PreCheckPost cnf_ptr cnfBytes work_ptr wlen R m' r → Q (r, ()) m' :=
  hs

theorem fullM6SolvePreCheckSpec_monoX
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : fullM6SolvePreCheckSpec xs m Q X) : fullM6SolvePreCheckSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, _, ⟨⟩⟩; exact h

/-! ## 4. Zero-Drag Post-Hoc `full_extend` + `kissat_check_model` & Generic Combinators -/

/-- Zero-drag post-hoc `full_extend` + `kissat_check_model` step discharge over
`FullM6HdrMem`: builds `fullExtendSpec` and `kissatCheckModelExactSpec` obligations whose
final branch proves all postconditions of `fullM6SolveBytesSpec`. -/
theorem fullM6_extend_check_cont {cnf_ptr cnf_end work_ptr : BitVec 64}
    {cnfBytes : List UInt8} {wlen : Nat} {c : FullCfg} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    {K : BitVec 64 → Mem 64 → Prop}
    (hcend : cnf_end = cnf_ptr + BitVec.ofNat 64 cnfBytes.length)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hle : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen)
    (hhdr : c.hdr = fullM6WorkHdr work_ptr)
    (hav : c.avail = wlen - fullAlignPad work_ptr - fullM6ExtBytes)
    (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hext_le : s.scratch.extend_len ≤ c.extend_cap)
    (hm : (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s ⋆
      region work_ptr (fullAlignPad work_ptr) ⋆ R) m)
    (hk : ∀ r m',
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
      (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        ∀ (F : Mem 64 → Prop) (M : Mem 64),
          (Eq m' ⋆ F) M → cnf.Sat (readModelFromWorkM6 M work_ptr)) →
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' → K r m') :
    fullExtendSpec (c.hdr, ()) m (fun () m1 =>
      ∃ s1, s1.LengthsOk c ∧
        (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s1 ⋆
          region work_ptr (fullAlignPad work_ptr) ⋆ R) m1 ∧
        kissatCheckModelExactSpec
          (cnf_ptr, cnf_end, c.hdr, c.pVals, BitVec.ofNat 64 c.mv, ()) m1
          (fun (ok, ()) m2 => K (if ok == 1#64 then 10#64 else 0#64) m2) X) X := by
  have hm0 : (FullM6HdrMem c ext s ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m := sep_ac hm
  rw [fullM6HdrMem_iff] at hm0
  have hm_full : (FullMem c s ⋆ (bytes cnf_ptr cnfBytes ⋆
      array64 (c.hdr - 2304) ext ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m := sep_ac hm0
  refine ⟨c, s, bytes cnf_ptr cnfBytes ⋆ array64 (c.hdr - 2304) ext ⋆
      region work_ptr (fullAlignPad work_ptr) ⋆ R,
    ⟨rfl, hext_le⟩, hlen, hm_full, fun ⟨⟩ s1 m1 _ hlen1 _ hm1 => ?_⟩
  unfold fullExtendSlice SafetySlice.ofMask at hlen1 hm1; dsimp only at hlen1 hm1
  have hm1_sep : (FullMem c s1 ⋆ (array64 (c.hdr - 2304) ext ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R))) m1 := sep_ac hm1
  rw [← fullM6HdrMem_iff] at hm1_sep
  have hm1_m6 : (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s1 ⋆
      region work_ptr (fullAlignPad work_ptr) ⋆ R) m1 := sep_ac hm1_sep
  refine ⟨s1, hlen1, hm1_m6, BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc,
    s1.core.d_cur, s1.core.d_val, cnfBytes, s1.core.vals.map UInt8.ofBitVec, c.mv,
    FullCheckRest c s1 ⋆ array64 (c.hdr - 2304) ext ⋆
      region work_ptr (fullAlignPad work_ptr) ⋆ R,
    hcend, rfl, hcfit, ?_, ?_, ?_,
    sep_ac (m6HdrMem_to_checkModel (ext := ext) (cnf_ptr := cnf_ptr) (cnfBytes := cnfBytes)
      (R := region work_ptr (fullAlignPad work_ptr) ⋆ R) hlen1 (sep_ac hm1_m6)),
    fun ok mv' nc' cur' val' m2 hok hm2 => ?_⟩
  · have hmv := c.hmv; unfold dimacsBound at hmv; omega
  · have := hlen1.core_ok.cur_vars_ge; have := hlen1.core_ok.cur_vars_le
    simp only [List.length_map, hlen1.core_ok.vals_len]; omega
  · have hmx := c.hmaxv; unfold dimacsBound at hmx
    simp only [List.length_map, hlen1.core_ok.vals_len]; omega
  · have hm2_reg := checkModel_post_to_m6_region hle (by omega) hhdr hav hext hlen1 hm2
    cases hrun : runKissatCheckModel cnfBytes (s1.core.vals.map UInt8.ofBitVec) c.mv
    · simp only [show (if ok == 1#64 then (10#64 : BitVec 64) else 0#64) = 0#64 from by
        rw [hok, hrun]; decide]
      exact hk 0#64 m2 (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm2_reg
    · simp only [show (if ok == 1#64 then (10#64 : BitVec 64) else 0#64) = 10#64 from by
        rw [hok, hrun]; decide]
      have hm2_chk : (dimacsState c.hdr mv' nc' cur' val' ⋆
          bytes c.pVals (s1.core.vals.map UInt8.ofBitVec) ⋆ FullCheckRest c s1 ⋆
          (bytes cnf_ptr cnfBytes ⋆ array64 (c.hdr - 2304) ext ⋆
            region work_ptr (fullAlignPad work_ptr) ⋆ R)) m2 := sep_ac hm2
      obtain ⟨cnf, hp, _, _, hsat⟩ := sat_of_checkModel_post_m6 hhdr hlen1 hm2_chk hrun
      exact hk 10#64 m2 (Or.inr (Or.inl rfl)) (fun h => by cases h) (fun _ => ⟨cnf, hp, hsat⟩)
        hm2_reg

/-- Specification-level post-hoc combinator upgrading any `fullM6SolvePreCheckSpec` outcome
into `fullM6SolveBytesSpec` via `fullM6_extend_check_cont`. -/
theorem fullM6_preCheck_to_solveBytesSpec {cnf_ptr cnf_end work_ptr : BitVec 64}
    {cnfBytes : List UInt8} {wlen : Nat} {R : Mem 64 → Prop} {X : XPost}
    {K : BitVec 64 → Mem 64 → Prop}
    (hcend : cnf_end = cnf_ptr + BitVec.ofNat 64 cnfBytes.length)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hk : ∀ r m',
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
      (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        ∀ (F : Mem 64 → Prop) (M : Mem 64),
          (Eq m' ⋆ F) M → cnf.Sat (readModelFromWorkM6 M work_ptr)) →
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' → K r m') :
    ∀ r m', FullM6PreCheckPost cnf_ptr cnfBytes work_ptr wlen R m' r →
      (r = 0#64 ∧ K 0#64 m') ∨
      (r = 20#64 ∧ K 20#64 m') ∨
      (r = 10#64 ∧ ∃ (c : FullCfg) (ext : List (BitVec 64)) (_s : FullState),
        fullExtendSpec (c.hdr, ()) m' (fun () m1 =>
          ∃ s1, s1.LengthsOk c ∧
            (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s1 ⋆
              region work_ptr (fullAlignPad work_ptr) ⋆ R) m1 ∧
            kissatCheckModelExactSpec
              (cnf_ptr, cnf_end, c.hdr, c.pVals, BitVec.ofNat 64 c.mv, ()) m1
              (fun (ok, ()) m2 => K (if ok == 1#64 then 10#64 else 0#64) m2) X) X) := by
  intro r m' hpre
  rcases hpre with ⟨rfl, hm0⟩ | ⟨rfl, hu, hm20⟩ |
      ⟨rfl, c, ext, s, hle, hhdr, hav, _hcfg, hext, hlen, hext_le, hm10⟩
  · exact Or.inl ⟨rfl, hk 0#64 m' (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm0⟩
  · exact Or.inr (Or.inl ⟨rfl,
      hk 20#64 m' (Or.inr (Or.inr rfl)) (fun _ => hu) (fun h => by cases h) hm20⟩)
  · exact Or.inr (Or.inr ⟨rfl, c, ext, s,
      fullM6_extend_check_cont hcend hcfit hwfit hle hhdr hav hext hlen hext_le hm10 hk⟩)

/-! ## 5. Generic `FullM6` Top-Level Soundness Combinators -/

/-- Generic `FullM6` top-level soundness combinator parameterized over ANY solver body
`solveBody : Func [i64, i64, i64, i64, i64] [i64]` satisfying `fullM6SolveBytesSpec`:
guarantees `r ∈ {0#64, 10#64, 20#64}`, `r = 20#64 → cnf.Unsat`,
`r = 10#64 → ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧ ∀ F M, (Eq m' ⋆ F) M →
cnf.Sat (readModelFromWorkM6 M work_ptr)`, and preserves arbitrary host frame `R`. -/
theorem fullM6_solve_bytes_sound_combinator (Γ : Env)
    (solveBody : Func [i64, i64, i64, i64, i64] [i64])
    (hwp : ∀ (a : Tup Val [i64, i64, i64, i64, i64]) (m : Mem 64)
      (Q : Post [i64]) (X : XPost),
      fullM6SolveBytesSpec a m Q X → Func.wp Γ solveBody a m Q X)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp Γ solveBody
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
            ∀ (F : Mem 64 → Prop) (M : Mem 64),
              (Eq m' ⋆ F) M → cnf.Sat (readModelFromWorkM6 M work_ptr)) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) := by
  refine hwp _ _ _ _ (fullM6SolveBytesSpec_intro hcfit hwfit hm ?_)
  intro r m' hdom h20 h10 hm'
  refine ⟨hdom, h20, fun hr10 => ?_, hm'⟩
  obtain ⟨cnf, hp, hsat⟩ := h10 hr10
  have hnot := cnf_not_unsat_of_sat (hsat emp m' (by rw [Std.ExtHashMap.sep_emp]))
  exact ⟨cnf, hp, hnot.1, hnot.2, hsat⟩

/-- Generic `ModuleOk` wrapper of `fullM6_solve_bytes_sound_combinator`: works for any
top-level `Fn` registered in `M : Module` whenever `Γ fnName [i64, i64, i64, i64, i64] [i64]`
strengthens `fullM6SolveBytesSpec`. -/
theorem fullM6_solve_bytes_moduleOk_combinator (Γ : Env) (M : Module) (fnName : Sym)
    (fnBody : Func [i64, i64, i64, i64, i64] [i64])
    (hMod : ModuleOk Γ M)
    (hMem : (⟨fnName, [i64, i64, i64, i64, i64], [i64], fnBody⟩ : Fn) ∈ M.fns)
    (hSpec : ∀ (a : Tup Val [i64, i64, i64, i64, i64]) (m : Mem 64)
      (Q : Post [i64]) (X : XPost),
      fullM6SolveBytesSpec a m Q X →
      Γ fnName [i64, i64, i64, i64, i64] [i64] a m Q X)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp Γ fnBody
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
            ∀ (F : Mem 64 → Prop) (M' : Mem 64),
              (Eq m' ⋆ F) M' → cnf.Sat (readModelFromWorkM6 M' work_ptr)) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hMem
  have hfn := (hMod.fnsOk pre ⟨fnName, [i64, i64, i64, i64, i64], [i64], fnBody⟩ post hsplit).2.2
  exact fullM6_solve_bytes_sound_combinator Γ fnBody
    (fun a m0 Q X hsp => hfn a m0 Q X (hSpec a m0 Q X hsp)) hcfit hwfit hm

/-- Tail-respec helper: upgrades a verified UNSAT-only `Module`
whose suffix `tail` implements `fullM6SolveBytesSpec` into `ModuleOk Γ₁ M`. -/
theorem fullM6_respec_tail_moduleOk {Γ₀ Γ₁ : Env} {M : Module} {pfx tail : List Fn}
    (hMod : ModuleOk Γ₀ M) (hsplit : M.fns = pfx ++ tail)
    (hpfx : ∀ f as bs, (f, as, bs) ∈ pfx.map Fn.sig ++ M.externs.map Extern.sig →
      ∀ xs m Q X, Γ₀ f as bs xs m Q X ↔ Γ₁ f as bs xs m Q X)
    (htail : ∀ fn ∈ tail, ∀ xs m Q X,
      Γ₁ fn.name fn.as fn.rs xs m Q X → Func.wp Γ₁ fn.body xs m Q X) :
    ModuleOk Γ₁ M :=
  ModuleOk.respec_tail hMod hsplit hpfx htail

/-- Architecture-agnostic machine-memory soundness lift (`KissatM6Sound` on x64 and
Arm64): extracts UNSAT soundness, host-framed `readModelFromWorkM6 st_dmem work_ptr` SAT
soundness, `r ∈ {0, 10, 20}`, and host memory preservation directly from a `fullM6SolveBytesSpec`
postcondition `Q (r, ()) m'` plus machine heap split `(Eq m' ⋆ F_host) st_dmem`. -/
theorem fullM6_host_sound_lift {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hq :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        ∀ (F : Mem 64 → Prop) (M : Mem 64),
          (Eq m' ⋆ F) M → cnf.Sat (readModelFromWorkM6 M work_ptr)) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hdmem : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
      ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
      cnf.Sat (readModelFromWorkM6 st_dmem work_ptr)) ∧
    ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) ⋆ F_host) st_dmem := by
  refine ⟨hq.1, hq.2.1, fun hr10 => ?_, ?_⟩
  · obtain ⟨cnf, hp, hsat⟩ := hq.2.2.1 hr10
    have hst := hsat F_host st_dmem hdmem
    have hnot := cnf_not_unsat_of_sat hst
    exact ⟨cnf, hp, hnot.1, hnot.2, hst⟩
  · exact sep_mono (fun m0 hm0 => by subst hm0; exact hq.2.2.2) hdmem


end LeanQbe.T.Examples.Kissat.Proof.Spec
