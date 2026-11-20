module

public import LeanQbe.T.Examples.Kissat.FullProof1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Top-Level `full_search`, `kissat_solve_bytes` & UNSAT Non-Vacuity (`Stage 4`)

Proves:
1. `full_search_wp`: `Func.wp` for `full_search` (`Full.lean:1108-1137`) with lexicographic
   termination measure `2 * fuel + (if propagated = trail_end then 1 else 0)`.
2. `kissat_solve_bytes_core_wp` & `kissat_solve_bytes_wp`: UNSAT-only soundness (`r ∈ {0, 10, 20}`,
   `r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`, read-only `cnfBytes`, restored
   `region work_ptr wlen`, `fullExtendSlice` framing of `full_extend`, `fullMem_to_checkModel` /
   `checkModel_post_to_region` framing of `kissat_check_model`, and `UnitUnsatTrace → r = 20#64`).
3. Concrete UNSAT non-vacuity (`fullNvUnsatBytes` → `20#64` and `fullNvUnsatCnf.Unsat` under
   `work_len = 4096`, `fuel = 16`, ZERO `UnitSatTrace` / SAT proofs).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full.FullTopSpecs
open Kraken.Bedrock2.Test

/-! ## 1. Pure bit-vector and alignment-framing helpers -/

private theorem bv64_ugt_max_sub_false {p : BitVec 64} {n : Nat}
    (hfit : p.toNat + n < 2 ^ 64) :
    ((0xFFFFFFFFFFFFFFFF#64 - p).ult (BitVec.ofNat 64 n)) = false := by
  have hp := p.isLt
  have hmax : (0xFFFFFFFFFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 64 - 1 := rfl
  have hsub : 0xFFFFFFFFFFFFFFFF#64 - p = BitVec.ofNat 64 (2 ^ 64 - 1 - p.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, hmax, bv64_ofNat_toNat (by omega)]; omega
  rw [hsub, bv_ult_eq (by omega) (by omega)]
  simp only [decide_eq_false_iff_not]; omega

private theorem fullAlignPad_bv_eq (p : BitVec 64) :
    (8 - (p &&& 7)) &&& 7 = BitVec.ofNat 64 (fullAlignPad p) := by
  apply BitVec.eq_of_toNat_eq
  rw [show ((8 : BitVec 64) - (p &&& 7)) &&& 7 = (8#64 - (p &&& 7#64)) &&& 7#64 from rfl,
    fullAlignPad_eq, bv64_ofNat_toNat (by have := fullAlignPad_lt8 p; omega)]

private theorem full_merge_reg {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
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

private theorem full_merge_arena {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {c : FullCfg} {st : FullState}
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64) (hw_ge : fullAlignPad work_ptr ≤ wlen)
    (hch : c.hdr = work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
    (hca : c.avail = wlen - fullAlignPad work_ptr) (hlen : st.LengthsOk c) {m' : Mem 64}
    (hm' : (bytes cnf_ptr cnfBytes ⋆ FullMem c st ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m') :
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' := by
  apply full_merge_reg hwfit hw_ge
  have h1 : (FullMem c st ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m' := sep_ac hm'
  have h2 : (region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
      (wlen - fullAlignPad work_ptr) ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m' :=
    sep_mono (fun _ f => by rw [← hch, ← hca]; exact FullArenaInv.to_region ⟨hlen, f⟩) h1
  exact sep_ac h2

/-- Lexicographic termination measure for `full_search`: either `fuel` strictly decreases (on any
propagation step) or `propagated = trail_end` flips to `propagated < trail_end` (on `decide`). -/
def searchVariant (st : FullState) : Nat :=
  2 * st.core.fuel.toNat + if st.core.propagated = st.core.trail_end then 1 else 0

/-! ## 2. `full_search_wp` (`Full.lean:1108-1137`) -/

section TopOrchestrators2

open scoped FullArenaTactics

local macro "fp_step" : tactic => `(tactic| (try (change wp _ _ _ _ _); c0_step))
local macro "fp_steps" : tactic => `(tactic| (try (change wp _ _ _ _ _); c0_steps))

/-- `Func.wp` proof for `full_search` (`Full.lean:1108-1137`). -/
theorem full_search_wp (Γ : Env)
    (hLucky : ∀ a m Q X, fullLuckySpec a m Q X → Γ "full_lucky" [i64] [i64] a m Q X)
    (hWarm : ∀ a m Q X, fullWarmupSpec a m Q X → Γ "full_warmup" [i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hAna : ∀ a m Q X, fullAnalyzeSpec a m Q X → Γ "full_analyze" [i64] [i64] a m Q X)
    (hSw : ∀ a m Q X, fullSwitchModeSpec a m Q X → Γ "full_switch_mode" [i64] [] a m Q X)
    (hReph : ∀ a m Q X, fullRephaseSpec a m Q X → Γ "full_rephase" [i64] [] a m Q X)
    (hRed : ∀ a m Q X, fullReduceSpec a m Q X → Γ "full_reduce" [i64, .bool] [i64] a m Q X)
    (hSimp : ∀ a m Q X, fullSimplifySpec a m Q X → Γ "full_simplify" [i64] [i64] a m Q X)
    (hRdue : ∀ a m Q X, fullRestartDueSpec a m Q X → Γ "full_restart_due" [i64] [i64] a m Q X)
    (hRst : ∀ a m Q X, fullRestartSpec a m Q X → Γ "full_restart" [i64] [] a m Q X)
    (hDec : ∀ a m Q X, fullDecideSpec a m Q X → Γ "full_decide" [i64] [i64] a m Q X) :
    ∀ args m Q X, fullSearchSpec args m Q X → Func.wp Γ full_search_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_search_body; fp_steps
  c0_call hLucky; refine ⟨c, F0, s, R, rfl, hinv, hcl0, hm, ?_⟩
  intro lk s1 m1 hlen1 hlk_dom _ hulk hsp1 hext1 hm1; fp_steps
  · rw [hc]; exact hQ 20#64 s1 m1 hlen1 (Or.inr (Or.inr rfl)) (fun _ => hulk hc)
      (fun h => by cases h) hm1
  · rw [hc]; exact hQ 10#64 s1 m1 hlen1 (Or.inr (Or.inl rfl)) (fun h => by cases h)
      (fun _ => hext1 hc) hm1
  have hlk02 : lk = 0#64 ∨ lk = 2#64 := by
    rcases hlk_dom with h0 | h2 | h10 | h20
    · exact Or.inl h0
    · exact Or.inr h2
    · exact absurd h10 hc
    · exact absurd h20 (by assumption)
  have hinv1 : FullSparseInv c F0 s1 := hsp1 hlk02
  c0_call hWarm; refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
  intro s2 m2 hinv2 _ hm2; fp_steps
  -- Main CDCL `while (true)` loop with variant `searchVariant st`
  refine wp_loop_group (ts := [])
    (fun rem () ml => ∃ st : FullState,
      rem = searchVariant st ∧ FullSparseInv c F0 st ∧ (FullMem c st ⋆ R) ml) ?_ ?_
  · rintro L rem ⟨⟩ ml ih ⟨st, rfl, hst, hml⟩
    fp_steps
    · exact hQ 0#64 st ml hst.lengths (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hml
    · exact hQ 0#64 st ml hst.lengths (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hml
    rotate_left 1
    · cases hc
    c0_call hProp; refine ⟨c, F0, st, R, rfl, hst, hml, ?_⟩
    intro pr s3 m3 hlen3 hpr_dom _ hfu3 hpr0 hpr1 _ hm3; fp_steps
    · exact hQ 0#64 s3 m3 hlen3 (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm3
    · -- Conflict branch (`pr == 1ULL`)
      obtain ⟨hsp3, hfu3_lt, hconf3⟩ := hpr1 hc
      c0_call hAna; refine ⟨c, F0, s3, R, rfl, hsp3, hconf3, hm3, ?_⟩
      intro ast s4 m4 hlen4 hast_dom hfu4 hua4 hsp4 hm4; fp_steps
      · exact hQ 20#64 s4 m4 hlen4 (Or.inr (Or.inr rfl)) (fun _ => hua4 hc)
          (fun h => by cases h) hm4
      · exact hQ 0#64 s4 m4 hlen4 (Or.inl rfl) (fun h => by cases h)
          (fun h => by cases h) hm4
      have hinv4 : FullSparseInv c F0 s4 := hsp4 hc
      c0_call hSw; refine ⟨c, s4, R, rfl, hinv4.lengths, hm4, ?_⟩
      intro ⟨⟩ s5 m5 hcore5 hlen5 ⟨hll5, hext5⟩ hm5
      dsimp only [fullSafetySlice, SafetySlice.ofMask] at hm5
      have hinv5 : FullSparseInv c F0 s5 := hinv4.of_safety_slice hcore5 hlen5 hll5 hext5
      have hfu5 : s5.core.fuel.toNat < st.core.fuel.toNat := by
        have heq : s5.core = s4.core := fullCoreState_agrees_with_scratch hcore5
        rw [heq]; omega
      -- Optional `full_rephase`
      refine wp_join_group (ts := [])
        (fun () m6 => ∃ s6 : FullState,
          FullSparseInv c F0 s6 ∧ s6.core.fuel.toNat < st.core.fuel.toNat ∧
          (FullMem c s6 ⋆ R) m6)
        (fun _ ⟨⟩ m6 ⟨s6, hinv6, hfu6, hm6⟩ => by
          c0_let_simp
          -- Optional `full_reduce(h, false)`
          refine wp_join_group (ts := [])
            (fun () m7 => ∃ s7 : FullState,
              FullSparseInv c F0 s7 ∧ s7.core.fuel.toNat < st.core.fuel.toNat ∧
              (FullMem c s7 ⋆ R) m7)
            (fun _ ⟨⟩ m7 ⟨s7, hinv7, hfu7, hm7⟩ => by
              c0_let_simp
              -- Optional `full_simplify` else optional `full_restart`
              refine wp_join_group (ts := [])
                (fun () m8 => ∃ s8 : FullState,
                  FullSparseInv c F0 s8 ∧ s8.core.fuel.toNat < st.core.fuel.toNat ∧
                  (FullMem c s8 ⋆ R) m8)
                (fun _ ⟨⟩ m8 ⟨s8, hinv8, hfu8, hm8⟩ => by
                  fp_steps
                  have hv_lt : searchVariant s8 < searchVariant st := by
                    unfold searchVariant; split <;> split <;> omega
                  exact ih (searchVariant s8) () m8 hv_lt ⟨s8, rfl, hinv8, hm8⟩)
                (fun J_sr hJ_sr => by
                  c0_let_simp
                  -- `if (conflicts >= probe_limit || conflicts >= elim_limit)`
                  refine wp_join_group (ts := [])
                    (fun () ms => ms = m7)
                    (fun _ ⟨⟩ ms hms => by
                      subst hms; fp_steps
                      c0_call hSimp; refine ⟨c, F0, s7, R, rfl, hinv7, hm7, ?_⟩
                      intro sr s8 m8 hlen8 _ hfu8 hus8 hsp8 hm8; fp_steps
                      · exact hQ 20#64 s8 m8 hlen8 (Or.inr (Or.inr rfl)) (fun _ => hus8 hc)
                          (fun h => by cases h) hm8
                      · exact hQ 0#64 s8 m8 hlen8 (Or.inl rfl) (fun h => by cases h)
                          (fun h => by cases h) hm8
                      exact hJ_sr () m8 ⟨s8, hsp8 hc, by omega, hm8⟩)
                    (fun J_simp hJ_simp => by
                      fp_steps
                      · exact hJ_simp () m7 rfl
                      · exact hJ_simp () m7 rfl
                      · c0_call hRdue; refine ⟨c, s7, R, rfl, hinv7.lengths, hm7, ?_⟩
                        intro ⟨rd, ⟨⟩⟩ s7' m7' hcore7' hlen7' ⟨hll7', hext7'⟩ hm7'
                        dsimp only [fullSafetySlice, SafetySlice.ofMask] at hm7'
                        have hinv7' : FullSparseInv c F0 s7' :=
                          hinv7.of_safety_slice hcore7' hlen7' hll7' hext7'
                        have hfu7' : s7'.core.fuel.toNat < st.core.fuel.toNat := by
                          have heq : s7'.core = s7.core :=
                            fullCoreState_agrees_with_scratch hcore7'
                          rw [heq]; exact hfu7
                        fp_steps
                        · c0_call hRst; refine ⟨c, F0, s7', R, rfl, hinv7', hm7', ?_⟩
                          intro s8 m8 hinv8 hfu8 hm8; fp_steps
                          exact hJ () m8 (by fp_steps; exact hJ_sr () m8 ⟨s8, hinv8, by omega, hm8⟩)
                        · exact hJ_sr () m7' ⟨s7', hinv7', hfu7', hm7'⟩)))
            (fun J_rd hJ_rd => by
              fp_steps
              · c0_call hRed; refine ⟨c, F0, s6, R, rfl, hinv6, hm6, ?_⟩
                intro rr s7 m7 hlen7 _ hfu7 hur7 hsp7 _ hm7; fp_steps
                · exact hQ 20#64 s7 m7 hlen7 (Or.inr (Or.inr rfl)) (fun _ => hur7 hc)
                    (fun h => by cases h) hm7
                · exact hQ 0#64 s7 m7 hlen7 (Or.inl rfl) (fun h => by cases h)
                    (fun h => by cases h) hm7
                exact hJ_rd () m7 ⟨s7, hsp7 hc, by omega, hm7⟩
              · exact hJ_rd () m6 ⟨s6, hinv6, hfu6, hm6⟩))
        (fun J_rp hJ_rp => by
          fp_steps
          · c0_call hReph; refine ⟨c, F0, s5, R, rfl, hinv5, hm5, ?_⟩
            intro s6 m6 hinv6 hfu6 hm6; fp_steps
            exact hJ_rp () m6 ⟨s6, hinv6, by omega, hm6⟩
          · exact hJ_rp () m5 ⟨s5, hinv5, hfu5, hm5⟩)
    · -- Non-conflict branch (`pr == 0ULL`), `unassigned == 0ULL`
      have hpr_eq0 : pr = 0#64 := by
        rcases hpr_dom with h0 | h1 | h2
        · exact h0
        · exact absurd h1 (by assumption)
        · exact absurd h2 (by assumption)
      obtain ⟨hsp3, _, _⟩ := hpr0 hpr_eq0
      exact hQ 10#64 s3 m3 hlen3 (Or.inr (Or.inl rfl)) (fun h => by cases h)
        (fun _ => hsp3.extend_len_le) hm3
    · -- Non-conflict branch (`pr == 0ULL`), `unassigned ≠ 0ULL`
      have hpr_eq0 : pr = 0#64 := by
        rcases hpr_dom with h0 | h1 | h2
        · exact h0
        · exact absurd h1 (by assumption)
        · exact absurd h2 (by assumption)
      obtain ⟨hsp3, hprop3, hfu3_lt_if⟩ := hpr0 hpr_eq0
      c0_call hDec; refine ⟨c, F0, s3, R, rfl, hsp3, hm3, ?_⟩
      intro dr s4 m4 hlen4 hdr_dom hfu4 hpr4 hd1 hd0 hm4; fp_steps
      · exact hQ 10#64 s4 m4 hlen4 (Or.inr (Or.inl rfl)) (fun h => by cases h)
          (fun _ => hd0 (by assumption)) hm4
      · exact hQ 0#64 s4 m4 hlen4 (Or.inl rfl) (fun h => by cases h)
          (fun h => by cases h) hm4
      · have hdr1 : dr = 1#64 := hdr_dom.resolve_left hc
        obtain ⟨hsp4, hte4⟩ := hd1 hdr1
        have hv_lt : searchVariant s4 < searchVariant st := by
          have hne4 : s4.core.propagated ≠ s4.core.trail_end := by omega
          have hle_st := hst.lengths.core_ok.propagated_le
          unfold searchVariant
          simp only [hne4, ↓reduceIte, Nat.add_zero, hfu4]
          by_cases heq_st : st.core.propagated = st.core.trail_end
          · simp only [heq_st, ↓reduceIte]; omega
          · simp only [heq_st, ↓reduceIte, Nat.add_zero]
            have hlt_f := hfu3_lt_if (by omega)
            omega
        exact ih (searchVariant s4) () m4 hv_lt ⟨s4, rfl, hsp4, hm4⟩
  · intro _ hL; fp_steps
    exact hL (searchVariant s2) () m2 ⟨s2, rfl, hinv2, hm2⟩

/-! ## 3. `kissat_solve_bytes_core_wp` and `kissat_solve_bytes_wp` (`Full.lean:1139-1160`) -/

/-- Post-search `r == 10ULL` gate: `full_extend` (via `fullExtendSlice`) + `kissat_check_model`
(via `fullMem_to_checkModel` / `checkModel_post_to_region`), restoring `(bytes ⋆ region ⋆ R) m'`. -/
private theorem solve_bytes_extend_check {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {s3 : FullState} {cnf_ptr work_ptr hdr_ptr : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m3 : Mem 64}
    (hExt : ∀ a m Q X, fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64) (hw_ge : fullAlignPad work_ptr ≤ wlen)
    (hch_ptr : c.hdr = hdr_ptr)
    (hch : c.hdr = work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
    (hca : c.avail = wlen - fullAlignPad work_ptr)
    (hlen3 : s3.LengthsOk c) (hext3 : s3.scratch.extend_len ≤ c.extend_cap)
    (hm3 : (bytes cnf_ptr cnfBytes ⋆ FullMem c s3 ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m3)
    (hRet : ∀ r m', (r = 0#64 ∨ r = 10#64) →
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' → Q (r, ()) m') :
    let cnf_end := cnf_ptr + BitVec.ofNat 64 cnfBytes.length
    wp Γ Q X (Expr.call (as := [i64]) (bs := []) "full_extend" (Arg.var hdr_ptr, ()) fun _ =>
      Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var hdr_ptr, Arg.imm 64, ()) }
      fun p1 => Expr.load i64 (Arg.var p1.fst) fun ld_v =>
      Expr.load i64 (Arg.var hdr_ptr) fun ld_mv =>
      Expr.call (as := [i64, i64, i64, i64, i64]) (bs := [i64]) "kissat_check_model"
        (Arg.var cnf_ptr, Arg.var cnf_end, Arg.var hdr_ptr, Arg.var ld_v, Arg.var ld_mv, ())
      fun p2 => Expr.group (sig := [[i64]])
        (fun _ => Blocks.cons (fun p3 => Expr.ret (Arg.var p3.fst, ())) Blocks.nil)
        fun Jr => Expr.let_
          { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
            args := (Arg.var p2.fst, Arg.imm 1, ()) }
          fun p3 => Expr.jnz (Arg.var p3.fst)
            (Expr.jump Jr.fst (Arg.imm 10, ())) (Expr.jump Jr.fst (Arg.imm 0, ()))) m3 := by
  dsimp only
  rw [← hch_ptr]
  c0_call hExt
  refine ⟨c, s3, bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R,
    ⟨rfl, hext3⟩, hlen3,
    by dsimp only [fullExtendSlice, SafetySlice.ofMask]; exact sep_ac hm3, ?_⟩
  intro ⟨⟩ s4 m4 _ hlen4 _ hm4
  dsimp only [fullExtendSlice, SafetySlice.ofMask] at hm4
  fp_steps
  have hm4_b : (bytes cnf_ptr cnfBytes ⋆ FullMem c s4 ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m4 := sep_ac hm4
  have hmv_bd := c.hmv; have hmx_bd := c.hmaxv; have hbva := c.hbva
  unfold dimacsBound at hmv_bd hmx_bd
  have hcm_mem := fullMem_to_checkModel hlen4 hm4_b
  c0_call hCheck
  refine ⟨BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc, s4.core.d_cur, s4.core.d_val,
    cnfBytes, s4.core.vals.map UInt8.ofBitVec, c.mv,
    FullCheckRest c s4 ⋆ (region work_ptr (fullAlignPad work_ptr) ⋆ R),
    rfl, rfl, hcfit, by omega,
    by simp [hlen4.core_ok.vals_len]; omega,
    by simp [hlen4.core_ok.vals_len]; omega,
    by simpa [sep_assoc] using hcm_mem, ?_⟩
  intro ok mv' nc' cur' val' m5 _ hm5
  have hm5_reg : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m5 :=
    full_merge_reg hwfit hw_ge (by
      rw [← hch, ← hca]
      exact checkModel_post_to_region hlen4 (by simpa [sep_assoc] using hm5))
  refine wp_join_group (ts := [i64])
    (fun (res_v, ()) m6 => (res_v = 0#64 ∨ res_v = 10#64) ∧ m6 = m5)
    (fun _ ⟨res_v, ⟨⟩⟩ m6 ⟨hres_v, hm6⟩ => by
      rw [hm6]; fp_steps; exact hRet res_v m5 hres_v hm5_reg)
    (fun Jr hJr => by
      fp_steps
      · exact hJr (10#64, ()) m5 ⟨Or.inr rfl, rfl⟩
      · exact hJr (0#64, ()) m5 ⟨Or.inl rfl, rfl⟩)

/-- `Func.wp` proof for `D-Full` `kissat_solve_bytes` (`Full.lean:1139-1160`) under
`fullSolveBytesCoreSpec` (UNSAT-only soundness + `UnitUnsatTrace` non-vacuity). -/
theorem kissat_solve_bytes_core_wp (Γ : Env)
    (hInit : ∀ a m Q X, fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hParse : ∀ a m Q X, fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hPre : ∀ a m Q X, fullPreprocessSpec a m Q X → Γ "full_preprocess" [i64] [i64] a m Q X)
    (hSearch : ∀ a m Q X, fullSearchSpec a m Q X → Γ "full_search" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ args m Q X, fullSolveBytesCoreSpec args m Q X →
      Func.wp Γ kissat_solve_bytes_body args m Q X := by
  rintro ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, ⟨⟩⟩ m Q X
    ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, hQ⟩
  unfold Func.wp kissat_solve_bytes_body; wp_unfold
  refine ⟨fun hf0 => ?_, fun _ => ?_⟩
  · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h)
      (fun _ _ _ _ _ hf => by rw [hf0] at hf; simp at hf) hm
  refine ⟨fun hcp0 => ?_, fun _ => ?_⟩
  · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h)
      (fun _ _ _ hcp => absurd hcp0 hcp) hm
  refine ⟨fun hwp0 => ?_, fun _ => ?_⟩
  · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h)
      (fun _ _ _ _ hwp => absurd hwp0 hwp) hm
  have hnot0 : ~~~(0 : BitVec 64) = 0xFFFFFFFFFFFFFFFF#64 := rfl
  rw [hnot0, bv64_ugt_max_sub_false hcfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  rw [bv64_ugt_max_sub_false hwfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  let pNat : Nat := fullAlignPad work_ptr
  have hp_lt8 : pNat < 8 := fullAlignPad_lt8 work_ptr
  have hpad_ult : (BitVec.ofNat 64 wlen).ult (((8 - (work_ptr &&& 7)) &&& 7) + 1152) =
      decide (wlen < pNat + 1152) := by
    rw [fullAlignPad_bv_eq work_ptr, show (1152 : BitVec 64) = BitVec.ofNat 64 1152 from rfl,
      bv_add_ofNat, bv_ult_eq (by omega) (by omega)]
  rw [hpad_ult]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun hw_small => ?_, fun hw_ge_not => ?_⟩
  · exact hQ 0#64 m (Or.inl rfl) (fun h => by cases h)
      (fun mv nc _ _ _ _ hsz _ _ _ => by unfold fullFixedBytes at hsz; omega) hm
  have hw_ok : pNat + 1152 ≤ wlen := by omega
  let hdr_addr : BitVec 64 := work_ptr + BitVec.ofNat 64 pNat
  let availNat : Nat := wlen - pNat
  have hpad_bv : (8 - (work_ptr &&& 7)) &&& 7 = BitVec.ofNat 64 pNat := fullAlignPad_bv_eq work_ptr
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
  · intro m' hm' hfail; wp_unfold
    have hm'_r : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' :=
      full_merge_reg hwfit (by omega) (by rw [hhdr_bv, hav_toNat] at hm'; exact hm')
    exact hQ 0#64 m' (Or.inl rfl) (fun h => by cases h)
      (fun mv nc i0 _ _ _ hsz _ hhdr _ => by
        have hlt := hfail mv nc (cnfBytes.drop i0) hhdr
        rw [hav_toNat] at hlt; omega) hm'_r
  · intro c s0 j0 rest0 m0 hch_ptr hca0 hhdr0 hj0 hdrop0 hinv0 hdcur0
      hcv0 hal0 _ hte0 hpr0 hcl0 _ hoom0 hinc0 hvals0 hm0
    have hch : c.hdr = hdr_addr := hch_ptr.trans hhdr_bv
    have hca : c.avail = availNat := hca0.trans hav_toNat
    have hvals_take : s0.core.vals.take (2 * c.mv) = List.replicate (2 * c.mv) 0#8 := by
      have hbva := c.hbva
      rw [hvals0, List.take_replicate, Nat.min_eq_left (by omega)]
    fp_step
    rotate_left 1
    · cases hc
    c0_call hParse
    refine ⟨c, s0, cnf_ptr, cnfBytes, j0, region work_ptr pNat ⋆ R,
      hch_ptr.symm, rfl, hcfit, hj0, by rwa [hdrop0], hdcur0, hcv0, hcl0, hte0, hpr0, hal0,
      hoom0, hinc0, hinv0, hm0, ?_⟩
    intro pb s1 m1 hlen1 hpb_dom hpb20 hpb1 huns_tr hm1; fp_steps
    · -- `pb ≠ 1#64`: `pb = 0#64` or `pb = 20#64`
      rcases hpb_dom with rfl | h1 | rfl
      · refine hQ 0#64 m1 (Or.inl rfl) (fun h => by cases h) ?_
          (full_merge_arena hwfit (by omega) hch hca hlen1 hm1)
        intro mv nc i0 _ _ _ _ _ hhdr hut
        rw [hhdr0, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hhdr
        rcases hhdr with ⟨rfl, rfl, hre⟩
        have h20 := huns_tr (by rw [hvals_take, hdrop0, hre]; exact hut)
        cases h20
      · exact absurd h1 hc
      · exact hQ 20#64 m1 (Or.inr (Or.inr rfl)) (fun _ => hpb20 rfl)
          (fun _ _ _ _ _ _ _ _ _ _ => rfl)
          (full_merge_arena hwfit (by omega) hch hca hlen1 hm1)
    · -- `pb == 1#64`: `cnf` parsed, `UnitUnsatTrace` ruled out
      obtain ⟨cnf, hparse, hinv1, hcl1⟩ := hpb1 hc
      have hnot_ut : ∀ mv nc i0, cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
          fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen → i0 ≤ cnfBytes.length →
          parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc → False := by
        intro mv nc i0 _ _ _ _ _ hhdr hut
        rw [hhdr0, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hhdr
        rcases hhdr with ⟨rfl, rfl, hre⟩
        have h20 := huns_tr (by rw [hvals_take, hdrop0, hre]; exact hut)
        rw [hc] at h20; cases h20
      c0_call hPre; refine ⟨c, cnf, s1, bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
        hch_ptr.symm, hinv1, hcl1, sep_ac hm1, ?_⟩
      intro pp s2 m2 hlen2 hpp_dom _ hpp20 hpp1 hpp10 hm2
      fp_step
      · fp_steps; exact hQ 20#64 m2 (Or.inr (Or.inr rfl)) (fun _ => ⟨cnf, hparse, hpp20 hc⟩)
          (fun _ _ _ _ _ _ _ _ _ _ => rfl)
          (full_merge_arena hwfit (by omega) hch hca hlen2 (sep_ac hm2))
      -- `r = (pp == 10) ? 10 : ((pp == 0) ? 0 : full_search(h))`
      refine wp_join_group (ts := [i64])
        (fun (rv, ()) mr => ∃ sr : FullState,
          sr.LengthsOk c ∧ (rv = 0#64 ∨ rv = 10#64 ∨ rv = 20#64) ∧
          (rv = 20#64 → cnf.Unsat) ∧
          (rv = 10#64 → sr.scratch.extend_len ≤ c.extend_cap) ∧
          (bytes cnf_ptr cnfBytes ⋆ FullMem c sr ⋆ (region work_ptr pNat ⋆ R)) mr)
        (fun _ ⟨rv, ⟨⟩⟩ mr ⟨sr, hlen_r, hrv_dom, hrv_u, hrv_ext, hmr⟩ => by
          fp_steps
          · exact solve_bytes_extend_check hExt hCheck hcfit hwfit (by omega) hch_ptr hch hca
              hlen_r (hrv_ext hc) hmr fun res m_end hres hm_end =>
                hQ res m_end (hres.elim Or.inl fun h => Or.inr (Or.inl h))
                  (fun h20 => by rcases hres with rfl | rfl <;> cases h20)
                  (fun mv nc i0 h1 h2 h3 h4 h5 h6 h7 =>
                    (hnot_ut mv nc i0 h1 h2 h3 h4 h5 h6 h7).elim)
                  hm_end
          · exact hQ rv mr hrv_dom (fun h20 => ⟨cnf, hparse, hrv_u h20⟩)
              (fun mv nc i0 h1 h2 h3 h4 h5 h6 h7 => (hnot_ut mv nc i0 h1 h2 h3 h4 h5 h6 h7).elim)
              (full_merge_arena hwfit (by omega) hch hca hlen_r hmr))
        (fun J_r hJ_r => by
          fp_step; fp_step
          · fp_steps; exact hJ_r (10#64, ()) m2 ⟨s2, hlen2, Or.inr (Or.inl rfl),
              (fun h => by cases h), (fun _ => hpp10 hc), sep_ac hm2⟩
          · refine wp_join_group (ts := [i64])
              (fun (rv, ()) mr => ∃ sr : FullState,
                sr.LengthsOk c ∧ (rv = 0#64 ∨ rv = 10#64 ∨ rv = 20#64) ∧
                (rv = 20#64 → cnf.Unsat) ∧
                (rv = 10#64 → sr.scratch.extend_len ≤ c.extend_cap) ∧
                (bytes cnf_ptr cnfBytes ⋆ FullMem c sr ⋆ (region work_ptr pNat ⋆ R)) mr)
              (fun _ ⟨rv, ⟨⟩⟩ mr hmr => by fp_steps; exact hJ_r (rv, ()) mr hmr)
              (fun J_r2 hJ_r2 => by
                fp_steps
                · exact hJ_r2 (0#64, ()) m2 ⟨s2, hlen2, Or.inl rfl, (fun h => by cases h),
                    (fun h => by cases h), sep_ac hm2⟩
                · have hpp_eq1 : pp = 1#64 := by
                    rcases hpp_dom with h0 | h1 | h10 | h20
                    · exact absurd h0 hc
                    · exact h1
                    · exact absurd h10 (by assumption)
                    · exact absurd h20 (by assumption)
                  obtain ⟨hinv2, hcl2⟩ := hpp1 hpp_eq1
                  c0_call hSearch
                  refine ⟨c, cnf, s2, bytes cnf_ptr cnfBytes ⋆ region work_ptr pNat ⋆ R,
                    hch_ptr.symm, hinv2, hcl2, hm2, ?_⟩
                  intro r3 s3 m3 hlen3 hr3_dom hu3 hext3 hm3; fp_steps
                  exact hJ_r2 (r3, ()) m3 ⟨s3, hlen3, hr3_dom, hu3, hext3, sep_ac hm3⟩))

theorem kissat_solve_bytes_wp (Γ : Env)
    (hInit : ∀ a m Q X, fullInitStateSpec a m Q X →
      Γ "full_init_state" [i64, i64, i64, i64, i64] [.bool] a m Q X)
    (hParse : ∀ a m Q X, fullParseBodySpec a m Q X →
      Γ "full_parse_body" [i64, i64] [i64] a m Q X)
    (hPre : ∀ a m Q X, fullPreprocessSpec a m Q X → Γ "full_preprocess" [i64] [i64] a m Q X)
    (hSearch : ∀ a m Q X, fullSearchSpec a m Q X → Γ "full_search" [i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, fullExtendSpec a m Q X → Γ "full_extend" [i64] [] a m Q X)
    (hCheck : ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Γ "kissat_check_model" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ args m Q X, fullSolveBytesSpec args m Q X →
      Func.wp Γ kissat_solve_bytes_body args m Q X :=
  fun args m Q X h =>
    kissat_solve_bytes_core_wp Γ hInit hParse hPre hSearch hExt hCheck args m Q X
      (fullSolveBytesCoreSpec_of_spec h)

end TopOrchestrators2

/-! ## 4. Concrete UNSAT (`20#64`) non-vacuity witness & Phase-1 closed driver (`4096`-byte work) -/

/-- Concrete UNSAT DIMACS input (`p cnf 1 2\n1 0\n-1 0\n`, 19 bytes). -/
def fullNvUnsatBytes : List UInt8 :=
  [112, 32, 99, 110, 102, 32, 49, 32, 50, 10, 49, 32, 48, 10, 45, 49, 32, 48, 10]

/-- Parsed `Std.Sat.CNF Nat` for `fullNvUnsatBytes`. -/
def fullNvUnsatCnf : CNF Nat :=
  (CNF.empty.add (CNF.Clause.ofLiterals [(1, true)])).add (CNF.Clause.ofLiterals [(1, false)])

theorem parseDimacs_fullNvUnsatBytes : parseDimacs fullNvUnsatBytes = some fullNvUnsatCnf := rfl

private theorem fullNvUnsat_header :
    parseHeader fullNvUnsatBytes = some (1, 2, fullNvUnsatBytes.drop 9) := by decide

private theorem fullNvUnsat_trace :
    UnitUnsatTrace 1 (List.replicate 2 0#8) (fullNvUnsatBytes.drop 9) 2 := by
  have hcl1 : parseClause 1 (fullNvUnsatBytes.drop 9) =
      some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral 0], fullNvUnsatBytes.drop 13) := rfl
  have hcl2 : parseClause 1 (fullNvUnsatBytes.drop 13) =
      some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral 1], [10]) := rfl
  exact UnitUnsatTrace.step (l := 0) (by decide) hcl1 (by decide)
    (UnitUnsatTrace.conflict (l := 1) (by decide) hcl2 (by decide) ⟨CNF.empty, rfl⟩)

/-- Concrete UNSAT witness contract (`fullNvUnsatBytes`, `work_len = 4096`, `fuel = 16`). -/
def fullUnsatWitnessSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q _ =>
    ∃ R : Mem 64 → Prop,
      cnf_ptr ≠ 0#64 ∧ work_ptr ≠ 0#64 ∧
      cnf_len = BitVec.ofNat 64 fullNvUnsatBytes.length ∧ work_len = 4096#64 ∧ fuel = 16#64 ∧
      cnf_ptr.toNat + fullNvUnsatBytes.length < 2 ^ 64 ∧ work_ptr.toNat + 4096 < 2 ^ 64 ∧
      (bytes cnf_ptr fullNvUnsatBytes ⋆ region work_ptr 4096 ⋆ R) m ∧
      ∀ m', fullNvUnsatCnf.Unsat →
        (bytes cnf_ptr fullNvUnsatBytes ⋆ region work_ptr 4096 ⋆ R) m' → Q (20#64, ()) m'

theorem fullSolveBytesCoreSpec_of_unsatWitness
    {args : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : fullUnsatWitnessSpec args m Q X) : fullSolveBytesCoreSpec args m Q X := by
  obtain ⟨R, hcp, hwp, hcl, hwl, hfu, hcfit, hwfit, hm, hQ⟩ := h
  refine ⟨fullNvUnsatBytes, 4096, R, hcl, hwl, hcfit, hwfit, hm, fun r m' _ hu huns_w hm' => ?_⟩
  have hr20 : r = 20#64 :=
    huns_w 1 2 9 hcp hwp (by rw [hfu]; decide)
      (by unfold fullFixedBytes valsBytes markBytes u32FullBytes fullMinDepthOf; decide)
      (by decide) fullNvUnsat_header fullNvUnsat_trace
  subst hr20
  obtain ⟨cnf, hparse, huns⟩ := hu rfl
  rw [parseDimacs_fullNvUnsatBytes] at hparse; cases Option.some.inj hparse
  exact hQ m' huns hm'

abbrev fullNvCnfPtr : BitVec 64 := 0x1000#64
abbrev fullNvWorkPtr (cnfBytes : List UInt8) : BitVec 64 :=
  fullNvCnfPtr + BitVec.ofNat 64 cnfBytes.length

def fullPayload (cnfBytes : List UInt8) : List UInt8 :=
  cnfBytes ++ List.replicate 4096 0

theorem fullPayload_length (cnfBytes : List UInt8) :
    (fullPayload cnfBytes).length = cnfBytes.length + 4096 := by
  simp only [fullPayload, List.length_append, List.length_replicate]

theorem fullPayload_sep (cnfBytes : List UInt8) (hcb : cnfBytes.length ≤ 4096) :
    (bytes fullNvCnfPtr cnfBytes ⋆ region (fullNvWorkPtr cnfBytes) 4096)
      ((fullPayload cnfBytes).At fullNvCnfPtr) := by
  have h4096 : (List.replicate 4096 (0 : UInt8)).length = 4096 := List.length_replicate
  have h1 := Mem.At_append_sep cnfBytes (List.replicate 4096 0) fullNvCnfPtr
    (by simp only [h4096]; omega)
  have h0 : (Eq ((cnfBytes ++ List.replicate 4096 0).At fullNvCnfPtr))
      ((fullPayload cnfBytes).At fullNvCnfPtr) := rfl
  rw [h1] at h0
  exact sep_mono_r (fun _ hfW => ⟨List.replicate 4096 0, h4096, hfW.symm⟩) h0

/-- Phase-1 environment exposing the `kissat_solve_bytes` callees (`full_init_state`,
`full_parse_body`, `full_preprocess`, `full_search`, `full_extend`, `kissat_check_model`).
Phase 2 replaces this with the full 166-function `mkFullEnv` + `fullEnv_moduleOk`. -/
def fullTopEnv : Env :=
  Env.ofTable
    [ ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩
    , ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩
    , ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩
    , ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩
    , ⟨"full_extend", [i64], [], fullExtendSpec, true⟩
    , ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩
    ]

private theorem fullTopEnv_nodup :
    (["full_init_state", "full_parse_body", "full_preprocess", "full_search",
      "full_extend", "kissat_check_model"] : List Sym).Nodup := by decide

private theorem fullTopEnv_row (e : SpecEntry)
    (he : e ∈
      [ ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩
      , ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩
      , ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩
      , ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩
      , ⟨"full_extend", [i64], [], fullExtendSpec, true⟩
      , ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩
      ] := by simp only [List.mem_cons, true_or, or_true])
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → fullTopEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h => Env.ofTable_of_mem he fullTopEnv_nodup (hno xs m Q X h)

/-- Phase-1 source-level UNSAT-only correctness of `D-Full` `kissat_solve_bytes`. -/
theorem full_solve_bytes_correct
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp fullTopEnv kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  kissat_solve_bytes_wp fullTopEnv
    (fullTopEnv_row ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool],
      fullInitStateSpec, true⟩)
    (fullTopEnv_row ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩)
    (fullTopEnv_row ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩)
    (fullTopEnv_row ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩)
    (fullTopEnv_row ⟨"full_extend", [i64], [], fullExtendSpec, true⟩)
    (fullTopEnv_row ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64],
      kissatCheckModelExactSpec, true⟩)
    _ m _ X
    ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, fun _ _ hdom hu hm' => ⟨hdom, hu, hm'⟩⟩

/-- Closed concrete UNSAT non-vacuity: `kissat_solve_bytes` returns `20#64` and proves
`fullNvUnsatCnf.Unsat` on `fullNvUnsatBytes` with `work_len = 4096` and `fuel = 16`. -/
theorem full_unsat_nonvacuous :
    let m0 : Mem 64 := (fullPayload fullNvUnsatBytes).At fullNvCnfPtr
    Func.wp fullTopEnv kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvUnsatBytes.length,
        fullNvWorkPtr fullNvUnsatBytes, 4096#64, 16#64, ()) m0
      (fun rs _ => rs = (20#64, ()) ∧ fullNvUnsatCnf.Unsat) (fun _ _ _ _ => False) :=
  kissat_solve_bytes_core_wp fullTopEnv
    (fullTopEnv_row ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool],
      fullInitStateSpec, true⟩)
    (fullTopEnv_row ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩)
    (fullTopEnv_row ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩)
    (fullTopEnv_row ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩)
    (fullTopEnv_row ⟨"full_extend", [i64], [], fullExtendSpec, true⟩)
    (fullTopEnv_row ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64],
      kissatCheckModelExactSpec, true⟩)
    _ _ _ _
    (fullSolveBytesCoreSpec_of_unsatWitness
      ⟨emp, by decide, by decide, rfl, rfl, rfl, by decide, by decide,
        by rw [sep_emp]; exact fullPayload_sep fullNvUnsatBytes (by decide),
        fun _ hu _ => ⟨rfl, hu⟩⟩)

end LeanQbe.T.Examples.Kissat.Full
