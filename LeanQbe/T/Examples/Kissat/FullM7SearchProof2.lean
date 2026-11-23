module

public import LeanQbe.T.Examples.Kissat.FullM7SearchProof1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Stage-3 M7 Search Parity `Func.wp` Proofs — Part 2

Plain `public section` (`0` `@[expose]`) parametric `(Γ : Env)` `Func.wp` proofs for the remaining
`5` `FullM7Search` functions (`ema_swap`, `switch_mode`, `randec_var`, `decide`, `lucky_late`)
plus their `4` canonical `FullSpec` drop-in bridges.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7Search

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open scoped FullArenaTactics

/-! ## 1. Local Stepper Tactics & BitVec/Invariant Helpers -/

private theorem p2_strip_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
private theorem p2_strip_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
private theorem p2_strip_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

local macro "p2_strip" : tactic =>
  `(tactic| first | apply p2_strip_32_64 | apply p2_strip_8_32 | apply p2_strip_8_64)
local macro "p2_unmdata" : tactic =>
  `(tactic| first | change LeanQbe.T.Func.wp _ _ _ _ _ _ | change LeanQbe.T.wp _ _ _ _ _)
local elab "p2_hsteps_ns" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 10000
local macro "p2_steps_raw" : tactic =>
  `(tactic| (
    (try p2_unmdata)
    (repeat p2_strip)
    p2_hsteps_ns
    repeat (any_goals (p2_strip; repeat p2_strip); p2_hsteps_ns)))
local macro "p2_steps" : tactic =>
  `(tactic| (
      (try p2_unmdata)
      (repeat p2_strip)
      c0_steps
      repeat (any_goals (p2_strip; repeat p2_strip); c0_steps)))

open Lean Elab Tactic in
/-- Step straight-line `C0Step` ops, stopping at `Expr.group` instead of inlining join points. -/
local elab "p2_to_group_step" : tactic => do
  for _ in [:500] do
    let mut progressed := false
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let rawTy ← Lean.instantiateMVars (← g.getType)
      let ty := rawTy.consumeMData
      if rawTy.isMData then
        let g'' ← g.change ty (checkDefEq := false)
        replaceMainGoal [g'']
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta.consumeMData).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push (← getMainGoal)
      else if ← LeanQbe.T.C0Step.stepOnce then
        progressed := true
        evalTactic (← `(tactic| all_goals (try (repeat p2_strip))))
        out := out ++ (← getUnsolvedGoals)
      else
        out := out.push (← getMainGoal)
    setGoals out.toList
    if !progressed then break

local macro "p2_to_group" : tactic =>
  `(tactic| ((try p2_unmdata); (repeat p2_strip); p2_to_group_step))

open Lean Elab Tactic in
/-- Step straight-line `C0Step` ops until `Expr.jnz`, then split it once. -/
local elab "p2_split" : tactic => do
  for _ in [:120] do
    let g ← getMainGoal
    let rawTy ← Lean.instantiateMVars (← g.getType)
    let ty := rawTy.consumeMData
    if rawTy.isMData then
      let g' ← g.change ty (checkDefEq := false)
      replaceMainGoal [g']
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta.consumeMData).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| c0_step))
      break
    evalTactic (← `(tactic| all_goals (repeat p2_strip)))
    if ← Lean.Elab.Tactic.tryTactic (evalTactic (← `(tactic| c0_step))) then
      evalTactic (← `(tactic| all_goals (repeat p2_strip)))
    else
      break

local macro "p2_call" hSpec:term : tactic =>
  `(tactic| (p2_unmdata; c0_call $hSpec))

private theorem p2_bv64_add1_toNat {k : BitVec 64} (hk : k.toNat + 1 < 2 ^ 64) :
    (k + 1#64).toNat = k.toNat + 1 := by
  bv_omega

private theorem p2_bv64_sub1_toNat {k : BitVec 64} (hk : k ≠ 0#64) :
    (k - 1#64).toNat = k.toNat - 1 := by
  bv_omega

private theorem p2_bv64_ofNat_toNat {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem p2_probePres_refl (s : FullState) : FullProbeScratchPres s s :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem p2_probePres_trans {s₁ s₂ s₃ : FullState}
    (h12 : FullProbeScratchPres s₁ s₂) (h23 : FullProbeScratchPres s₂ s₃) :
    FullProbeScratchPres s₁ s₃ :=
  ⟨⟨h23.1.1.trans h12.1.1, h23.1.2.trans h12.1.2⟩, h23.2.1.trans h12.2.1,
   h23.2.2.1.trans h12.2.2.1, h23.2.2.2.1.trans h12.2.2.2.1,
   h23.2.2.2.2.1.trans h12.2.2.2.2.1, h23.2.2.2.2.2.1.trans h12.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.trans h12.2.2.2.2.2.2.2⟩

private theorem p2_fullMem_eq {c : FullCfg} {s₁ s₂ : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (h : s₁ = s₂) (hm : (FullMem c s₁ ⋆ R) m) : (FullMem c s₂ ⋆ R) m :=
  h ▸ hm

private theorem p2_fullCoreInv_with_scratch {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullCoreInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c) :
    FullCoreInv c F0 { s with scratch := sc' } :=
  hinv.with_fuel_scratch_spec ⟨hinv.lengths.core_ok, hok⟩ rfl

private theorem p2_m7Set64_step {c : FullCfg} {sc : FullScratch} {s0 : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {k n : Nat} {val : BitVec 64}
    (hk : k = n) (hn : n < 63)
    (hlen : ({ core := s0.core, scratch := { sc with glue_used :=
      (if k < 63 then m7Set64List sc.glue_used k val else sc.glue_used) } } : FullState).LengthsOk
      c)
    (hm : (FullMem c { core := s0.core, scratch := { sc with glue_used :=
      (if k < 63 then m7Set64List sc.glue_used k val else sc.glue_used) } } ⋆ R) m) :
    ({ core := s0.core, scratch := { sc with glue_used :=
      (m7Set64List sc.glue_used n val) } } : FullState).LengthsOk c ∧
      (FullMem c { core := s0.core, scratch := { sc with glue_used :=
        (m7Set64List sc.glue_used n val) } } ⋆ R) m := by
  subst hk; have h : k < 63 := hn; simp only [h, ↓reduceIte] at hlen hm; exact ⟨hlen, hm⟩

private theorem p2_ite_eq_left {α : Type} {c : Prop} [Decidable c] (hc : c) (a b : α) :
    (if c then a else b) = a := ite_eq_left hc

private theorem p2_ite_eq_right {α : Type} {c : Prop} [Decidable c] (hc : ¬c) (a b : α) :
    (if c then a else b) = b := ite_eq_right hc

/-! ## 2. `full_ema_swap_m7` `Func.wp` Proof -/

theorem full_ema_swap_m7_wp (Γ : Env)
    (hInit : EnvSpec Γ "full_m7_state_init" m7StateInitSpec)
    (hGet : EnvSpec Γ "full_m7_get64" m7Get64Spec)
    (hSet : EnvSpec Γ "full_m7_set64" m7Set64Spec) :
    ∀ a m Q X, m7EmaSwapSpec a m Q X →
      Func.wp Γ full_ema_swap_m7_body a m Q X := by
  rintro ⟨h, old_m, new_m, ⟨⟩⟩ m Q X hspec
  obtain ⟨c, s, R, rfl, hlen, hm, hQ⟩ := m7EmaSwapSpec_elim hspec
  unfold Func.wp full_ema_swap_m7_body
  let omNat : Nat := if old_m ≠ 0#64 then 1 else 0
  let nmNat : Nat := if new_m ≠ 0#64 then 1 else 0
  let omBv : BitVec 64 := BitVec.ofNat 64 omNat
  let nmBv : BitVec 64 := BitVec.ofNat 64 nmNat
  p2_to_group
  apply wp_join_group (ts := [i64]) (fun xs m0 => xs = (omBv, ()) ∧ m0 = m)
  · rintro _J10 ⟨om, ⟨⟩⟩ m0 ⟨hom, hm0⟩
    injection hom with hom; subst om; subst m0; rw [Blocks.get_here]; p2_to_group
    apply wp_join_group (ts := [i64]) (fun xs m0 => xs = (nmBv, ()) ∧ m0 = m)
    · rintro _J20 ⟨nm, ⟨⟩⟩ m0 ⟨hnm, hm0⟩
      injection hnm with hnm; subst nm; subst m0; rw [Blocks.get_here]; p2_steps
      let s0 : FullState := { s with scratch := { s.scratch with stable := omBv } }
      have hlen0 : s0.LengthsOk c := ⟨hlen.core_ok, { hlen.scratch_ok with
        walk_vals_len := hlen.scratch_ok.walk_vals_len }⟩
      p2_call hInit
      refine m7StateInitSpec_of hlen0 (by assumption) fun hlen1 hi1 hp1 m1 hm1 => ?_
      p2_to_group
      let gu0 := m7StateInitGu s0.scratch
      have hgu0_len : gu0.length = 64 := hi1.len
      let s1 : FullState :=
        { s with scratch := { s.scratch with stable := nmBv, glue_used := gu0 } }
      have hlen1' : s1.LengthsOk c := ⟨hlen1.core_ok,
        { hlen1.scratch_ok with walk_vals_len := hlen1.scratch_ok.walk_vals_len }⟩
      apply wp_join_group (ts := [i64])
        (fun xs m1' => xs = (BitVec.ofNat 64 (if omNat = 0 then 40 else 48), ()) ∧
          (FullMem c s1 ⋆ R) m1')
      · rintro _J30 ⟨old_base, ⟨⟩⟩ m1' ⟨hob, hm1'⟩
        injection hob with hob; subst old_base; rw [Blocks.get_here]
        let obNat : Nat := if omNat = 0 then 40 else 48
        have hob_eq : (BitVec.ofNat 64 obNat).toNat = obNat :=
          p2_bv64_ofNat_toNat (by dsimp [obNat]; split <;> decide)
        have hob_add2 : (BitVec.ofNat 64 obNat + 2#64).toNat = obNat + 2 := by
          dsimp [obNat]; split <;> decide
        have hob_add4 : (BitVec.ofNat 64 obNat + 4#64).toNat = obNat + 4 := by
          dsimp [obNat]; split <;> decide
        have hob_add6 : (BitVec.ofNat 64 obNat + 6#64).toNat = obNat + 6 := by
          dsimp [obNat]; split <;> decide
        p2_steps
        p2_call hSet
        refine m7Set64Spec_of hlen1' hm1' fun hlen_a m2 hm2 => ?_
        p2_steps
        obtain ⟨hlen1a, hm2'⟩ := p2_m7Set64_step (n := obNat)
          (by dsimp [obNat]; by_cases h : omNat = 0 <;> (simp [h]; try decide))
          (by dsimp [obNat]; split <;> decide) hlen_a hm2
        p2_call hSet
        refine m7Set64Spec_of hlen1a hm2' fun hlen_b m3 hm3 => ?_
        p2_steps
        obtain ⟨hlen1b, hm3'⟩ := p2_m7Set64_step (n := obNat + 2)
          (by dsimp [obNat]; by_cases h : omNat = 0 <;> (simp [h]; try decide))
          (by dsimp [obNat]; split <;> decide) hlen_b hm3
        p2_call hSet
        refine m7Set64Spec_of hlen1b hm3' fun hlen_c m4 hm4 => ?_
        p2_steps
        obtain ⟨hlen1c, hm4'⟩ := p2_m7Set64_step (n := obNat + 4)
          (by dsimp [obNat]; by_cases h : omNat = 0 <;> (simp [h]; try decide))
          (by dsimp [obNat]; split <;> decide) hlen_c hm4
        p2_call hSet
        refine m7Set64Spec_of hlen1c hm4' fun hlen_d m5 hm5 => ?_
        p2_steps
        obtain ⟨hlen1d, hm5d⟩ := p2_m7Set64_step (n := obNat + 6)
          (by dsimp [obNat]; by_cases h : omNat = 0 <;> (simp [h]; try decide))
          (by dsimp [obNat]; split <;> decide) hlen_d hm5
        let curV := (s.scratch.ema_fast_biased, s.scratch.ema_fast_exp,
          s.scratch.ema_slow_biased, s.scratch.ema_slow_exp)
        let gu1 := m7ModeEmaSet gu0 omNat curV
        have hgu1_len : gu1.length = 64 := by rw [m7ModeEmaSet_length]; exact hgu0_len
        have hgu1_eq : m7Set64List (m7Set64List (m7Set64List (m7Set64List gu0 obNat
            s.scratch.ema_fast_biased) (obNat + 2) s.scratch.ema_fast_exp)
            (obNat + 4) s.scratch.ema_slow_biased) (obNat + 6) s.scratch.ema_slow_exp = gu1 := by
          dsimp [gu1, curV]; rw [m7ModeEmaSet_eq]
          dsimp [obNat, m7GuEma0FbIdx, m7GuEma1FbIdx]
          try (by_cases h_om : omNat = 0 <;> simp [h_om])
        let s2 : FullState := { s1 with scratch := { s1.scratch with glue_used := gu1 } }
        have hlen2 : s2.LengthsOk c := ⟨hlen1'.core_ok,
          { hlen1'.scratch_ok with glue_used_len := hgu1_len }⟩
        have hm5' : (FullMem c s2 ⋆ R) m5 := p2_fullMem_eq (by
          dsimp [s2, s1]; rw [hgu1_eq]) hm5d
        p2_call hGet
        refine m7Get64Spec_of hlen2 hm5' ?_
        p2_to_group
        let maskPrev := m7Get64Val gu1 38
        let mask : BitVec 64 := maskPrev ||| (1#64 <<< omBv)
        have h_om_mod : omBv.toNat % 64 = omBv.toNat := by
          by_cases h : old_m = 0#64 <;> simp [omBv, omNat, h]
        have h_nm_mod : nmBv.toNat % 64 = nmBv.toNat := by
          by_cases h : new_m = 0#64 <;> simp [nmBv, nmNat, h]
        have hsh_om : 1#64 <<< omBv = 1#64 <<< omNat := by
          dsimp [omBv, omNat]; split <;> decide
        have hsh_nm : 1#64 <<< nmBv = 1#64 <<< nmNat := by
          dsimp [nmBv, nmNat]; split <;> decide
        apply wp_join_group (ts := [i64])
          (fun xs m6 => xs = (BitVec.ofNat 64 (if nmNat = 0 then 40 else 48), ()) ∧
            (FullMem c s2 ⋆ R) m6)
        · rintro _J40 ⟨new_base, ⟨⟩⟩ m6 ⟨hnb, hm6⟩
          injection hnb with hnb; subst new_base; rw [Blocks.get_here]
          let nbNat : Nat := if nmNat = 0 then 40 else 48
          have hnb_eq : (BitVec.ofNat 64 nbNat).toNat = nbNat :=
            p2_bv64_ofNat_toNat (by dsimp [nbNat]; split <;> decide)
          have hnb_add2 : (BitVec.ofNat 64 nbNat + 2#64).toNat = nbNat + 2 := by
            dsimp [nbNat]; split <;> decide
          have hnb_add4 : (BitVec.ofNat 64 nbNat + 4#64).toNat = nbNat + 4 := by
            dsimp [nbNat]; split <;> decide
          have hnb_add6 : (BitVec.ofNat 64 nbNat + 6#64).toNat = nbNat + 6 := by
            dsimp [nbNat]; split <;> decide
          let bit : BitVec 64 := 1#64 <<< nmBv
          apply wp_join_group (ts := [i64]) (fun (fmask, ()) mf =>
            ∃ scFinal : FullScratch,
              scFinal = m7EmaSwapSc s.scratch old_m new_m ∧
              ∃ guPre : List (BitVec 32),
                guPre.length = 64 ∧
                m7Set64List guPre 38 fmask = scFinal.glue_used ∧
                (FullMem c { core := s.core, scratch := { scFinal with glue_used := guPre } } ⋆
                  R) mf)
          · rintro _J50 ⟨fmask, ⟨⟩⟩ mf
              ⟨scFinal, hscF, guPre, hguP_len, hguP_eq, hmf⟩
            rw [hscF] at hmf hguP_eq
            rw [Blocks.get_here]; p2_steps
            let sPre : FullState :=
              { core := s.core, scratch := { m7EmaSwapSc s.scratch old_m new_m with
                glue_used := guPre } }
            have hlenPre : sPre.LengthsOk c := ⟨hlen.core_ok, by
              have hl := m7EmaSwapSc_lengths hlen.scratch_ok old_m new_m
              exact { hl with glue_used_len := hguP_len }⟩
            p2_call hSet
            refine m7Set64Spec_of hlenPre hmf fun hlenFinal mFinal hmFinal => ?_
            p2_steps
            have hmFinal' :
                (FullMem c { core := s.core, scratch := m7EmaSwapSc s.scratch old_m new_m } ⋆ R)
                  mFinal :=
              p2_fullMem_eq (by dsimp [sPre]; rw [hguP_eq]) hmFinal
            exact hQ (by
              have hl := m7EmaSwapSc_lengths hlen.scratch_ok old_m new_m
              exact ⟨hlen.core_ok, hl⟩)
              (M7GuPrefixPres.of_forall fun _ hk => m7EmaSwapSc_prefix s.scratch old_m new_m hk)
              (m7EmaSwapSc_initOk hlen.scratch_ok.glue_used_len old_m new_m)
              mFinal hmFinal'
          · intro J50 hJ50
            have h38 : (38#64 : BitVec 64).toNat = 38 := by decide
            simp only [h38] at *
            have hnb_lt63 : (BitVec.ofNat 64 nbNat).toNat < 63 := by
              rw [hnb_eq]; dsimp [nbNat]; split <;> decide
            have hnb2_lt63 : (BitVec.ofNat 64 nbNat + 2#64).toNat < 63 := by
              rw [hnb_add2]; dsimp [nbNat]; split <;> decide
            have hnb4_lt63 : (BitVec.ofNat 64 nbNat + 4#64).toNat < 63 := by
              rw [hnb_add4]; dsimp [nbNat]; split <;> decide
            have hnb6_lt63 : (BitVec.ofNat 64 nbNat + 6#64).toNat < 63 := by
              rw [hnb_add6]; dsimp [nbNat]; split <;> decide
            clear hlen_a hlen_b hlen_c hlen_d hm2 hm3 hm4 hm5 hlen1a hlen1b hlen1c hlen1d
            clear hm2' hm3' hm4' hm5d hm5' hlen1' hm1' hlen1 hlen0 hm
            p2_to_group; p2_split
            · have hcond : mask &&& bit ≠ 0#64 := by
                simpa [mask, maskPrev, bit, s2, s1, h_om_mod, h_nm_mod] using hc
              p2_call hGet; refine m7Get64Spec_of hlen2 hm6 ?_; p2_steps
              let s3 : FullState := { core := s.core, scratch := { s2.scratch with
                ema_fast_biased := m7Get64Val gu1 nbNat } }
              have hlen3 : s3.LengthsOk c := ⟨hlen2.core_ok,
                { hlen2.scratch_ok with walk_vals_len := hlen2.scratch_ok.walk_vals_len }⟩
              have hm3a : (FullMem c s3 ⋆ R) m := p2_fullMem_eq (by
                dsimp [s3, s2, s1]
                try simp only [hnb_lt63, hnb_eq, ↓reduceIte]
                dsimp [nbNat]; try by_cases h_nm' : nmNat = 0 <;> simp [h_nm']) hm
              p2_call hGet; refine m7Get64Spec_of hlen3 hm3a ?_; p2_steps
              let s4 : FullState := { core := s.core, scratch := { s3.scratch with
                ema_fast_exp := m7Get64Val gu1 (nbNat + 2) } }
              have hlen4 : s4.LengthsOk c := ⟨hlen3.core_ok,
                { hlen3.scratch_ok with walk_vals_len := hlen3.scratch_ok.walk_vals_len }⟩
              have hm4a : (FullMem c s4 ⋆ R) m := p2_fullMem_eq (by
                dsimp [s4, s3, s2, s1]
                try simp only [hnb2_lt63, hnb_add2, ↓reduceIte]
                dsimp [nbNat]; try by_cases h_nm' : nmNat = 0 <;> simp [h_nm']) hm
              p2_call hGet; refine m7Get64Spec_of hlen4 hm4a ?_; p2_steps
              let s5 : FullState := { core := s.core, scratch := { s4.scratch with
                ema_slow_biased := m7Get64Val gu1 (nbNat + 4) } }
              have hlen5 : s5.LengthsOk c := ⟨hlen4.core_ok,
                { hlen4.scratch_ok with walk_vals_len := hlen4.scratch_ok.walk_vals_len }⟩
              have hm5a : (FullMem c s5 ⋆ R) m := p2_fullMem_eq (by
                dsimp [s5, s4, s3, s2, s1]
                try simp only [hnb4_lt63, hnb_add4, ↓reduceIte]
                dsimp [nbNat]; try by_cases h_nm' : nmNat = 0 <;> simp [h_nm']) hm
              p2_call hGet; refine m7Get64Spec_of hlen5 hm5a ?_; p2_steps
              let s6 : FullState := { core := s.core, scratch := { s5.scratch with
                ema_slow_exp := m7Get64Val gu1 (nbNat + 6) } }
              have hm6a : (FullMem c s6 ⋆ R) m := p2_fullMem_eq (by
                dsimp [s6, s5, s4, s3, s2, s1]
                try simp only [hnb6_lt63, hnb_add6, ↓reduceIte]
                dsimp [nbNat]; try by_cases h_nm' : nmNat = 0 <;> simp [h_nm']) hm
              have hcond' :
                  (m7Get64Val gu1 38 ||| 1#64 <<< omNat) &&& 1#64 <<< nmNat ≠ 0#64 := by
                have h0 := hcond
                dsimp only [mask, maskPrev, bit] at h0
                rwa [hsh_om, hsh_nm] at h0
              have hema :
                  (m7Get64Val gu1 nbNat, m7Get64Val gu1 (nbNat + 2),
                   m7Get64Val gu1 (nbNat + 4), m7Get64Val gu1 (nbNat + 6)) =
                    m7ModeEmaGet gu1 nmNat := by
                rw [m7ModeEmaGet_eq]
                dsimp [nbNat, m7GuEma0FbIdx, m7GuEma1FbIdx]
                try (by_cases h_nm : nmNat = 0 <;> simp [h_nm])
              have hsw : m7EmaSwapSc s.scratch old_m new_m =
                  { s6.scratch with glue_used := m7Set64List gu1 38 mask } := by
                rw [m7EmaSwapSc_eq]
                refine Eq.trans (p2_ite_eq_left hcond' _ _) ?_
                dsimp [s6, s5, s4, s3, s2, s1]
                have h4 := hema; dsimp only [nmNat] at h4
                have hmEq : m7GuEmaMaskIdx = 38 := rfl
                dsimp only [omNat, nmNat, mask, maskPrev, gu1, curV, gu0, s0, omBv] at h4 ⊢
                rw [hsh_om, hmEq]; simp only [← h4]; rfl
              have hscEq :
                  s6.scratch = { m7EmaSwapSc s.scratch old_m new_m with glue_used := gu1 } := by
                rw [hsw]
              simp only [show 38 < 63 by decide, ↓reduceIte, h_om_mod]
              refine hJ50 (mask, ()) _ ⟨m7EmaSwapSc s.scratch old_m new_m, rfl, gu1, hgu1_len, ?_,
                p2_fullMem_eq (by dsimp [s6] at hscEq ⊢; rw [← hscEq]) hm6a⟩
              rw [hsw]
            · have hcond : ¬(mask &&& bit ≠ 0#64) := by
                have hc' : (mask &&& bit) = 0#64 := by
                  simpa [mask, maskPrev, bit, s2, s1, h_om_mod, h_nm_mod] using hc
                simp [hc']
              have hcond' :
                  ¬((m7Get64Val gu1 38 ||| 1#64 <<< omNat) &&& 1#64 <<< nmNat ≠ 0#64) := by
                have h0 := hcond
                dsimp only [mask, maskPrev, bit] at h0
                rwa [hsh_om, hsh_nm] at h0
              p2_steps
              let initExp : BitVec 64 := 1#64 <<< 32
              have hiE : initExp = m7EmaInitExp := by decide
              let s3 : FullState := { s2 with scratch := { s2.scratch with
                ema_fast_biased := 0#64, ema_fast_exp := initExp,
                ema_slow_biased := 0#64, ema_slow_exp := initExp } }
              have hlen3 : s3.LengthsOk c := ⟨hlen2.core_ok,
                { hlen2.scratch_ok with walk_vals_len := hlen2.scratch_ok.walk_vals_len }⟩
              p2_call hSet; refine m7Set64Spec_of hlen3 hm fun hlen_e m6' hm6' => ?_
              p2_steps
              obtain ⟨hlen3a, hm6''⟩ := p2_m7Set64_step (n := nbNat)
                (by dsimp [nbNat]; by_cases h : nmNat = 0 <;> (simp [h]; try decide))
                (by dsimp [nbNat]; split <;> decide) hlen_e hm6'
              p2_call hSet; refine m7Set64Spec_of hlen3a hm6'' fun hlen_f m7 hm7 => ?_
              p2_steps
              obtain ⟨hlen3b, hm7'⟩ := p2_m7Set64_step (n := nbNat + 2)
                (by dsimp [nbNat]; by_cases h : nmNat = 0 <;> (simp [h]; try decide))
                (by dsimp [nbNat]; split <;> decide) hlen_f hm7
              p2_call hSet; refine m7Set64Spec_of hlen3b hm7' fun hlen_g m8 hm8 => ?_
              p2_steps
              obtain ⟨hlen3c, hm8'⟩ := p2_m7Set64_step (n := nbNat + 4)
                (by dsimp [nbNat]; by_cases h : nmNat = 0 <;> (simp [h]; try decide))
                (by dsimp [nbNat]; split <;> decide) hlen_g hm8
              p2_call hSet; refine m7Set64Spec_of hlen3c hm8' fun hlen_h m9 hm9 => ?_
              p2_steps
              obtain ⟨hlen3d, hm9'⟩ := p2_m7Set64_step (n := nbNat + 6)
                (by dsimp [nbNat]; by_cases h : nmNat = 0 <;> (simp [h]; try decide))
                (by dsimp [nbNat]; split <;> decide) hlen_h hm9
              let initV := (0#64, m7EmaInitExp, 0#64, m7EmaInitExp)
              let gu3 := m7ModeEmaSet gu1 nmNat initV
              have hgu3_len : gu3.length = 64 := by rw [m7ModeEmaSet_length]; exact hgu1_len
              have hgu3_eq : m7Set64List (m7Set64List (m7Set64List (m7Set64List gu1 nbNat 0#64)
                  (nbNat + 2) initExp) (nbNat + 4) 0#64) (nbNat + 6) initExp = gu3 := by
                dsimp [gu3, initV]; rw [m7ModeEmaSet_eq]
                dsimp [nbNat, m7GuEma0FbIdx, m7GuEma1FbIdx]
                rw [hiE]; try (by_cases h_nm : nmNat = 0 <;> simp [h_nm])
              have hsw : m7EmaSwapSc s.scratch old_m new_m =
                  { s3.scratch with glue_used := m7Set64List gu3 38 (mask ||| bit) } := by
                rw [m7EmaSwapSc_eq]
                refine Eq.trans (p2_ite_eq_right hcond' _ _) ?_
                dsimp only [s3, s2, s1, gu3, initV, gu1, curV, gu0, s0, mask, maskPrev, bit, nbNat]
                rw [hiE, hsh_om, hsh_nm]
                dsimp only [omBv, omNat, nmNat]; rfl
              have hscEq :
                  { s3.scratch with glue_used := gu3 } =
                    { m7EmaSwapSc s.scratch old_m new_m with glue_used := gu3 } := by
                rw [hsw]
              simp only [show 38 < 63 by decide, ↓reduceIte, h_om_mod, h_nm_mod]
              refine hJ50 (mask ||| bit, ()) m9
                ⟨m7EmaSwapSc s.scratch old_m new_m, rfl, gu3, hgu3_len, ?_,
                  p2_fullMem_eq (by
                    have hgu3' := hgu3_eq
                    dsimp [initExp] at hgu3'
                    dsimp [s3, s2, s1, initExp] at hscEq ⊢
                    rw [hgu3']
                    exact congrArg (fun sc : FullScratch =>
                      ({ core := s.core, scratch := sc } : FullState)) hscEq) hm9'⟩
              rw [hsw]
        · intro J40 hJ40; p2_to_group; p2_split
          · have h0 : nmNat = 0 := by by_cases h : new_m = 0#64 <;> simp_all [nmBv, nmNat]
            exact hJ40 (40#64, ()) m5 ⟨by simp [h0], hm5'⟩
          · have h0 : nmNat ≠ 0 := by by_cases h : new_m = 0#64 <;> simp_all [nmBv, nmNat]
            exact hJ40 (48#64, ()) m5 ⟨by simp [h0], hm5'⟩
      · intro J30 hJ30; p2_to_group; p2_split
        · have h0 : omNat = 0 := by by_cases h : old_m = 0#64 <;> simp_all [omBv, omNat]
          exact hJ30 (40#64, ()) _ ⟨by simp [h0], by assumption⟩
        · have h0 : omNat ≠ 0 := by by_cases h : old_m = 0#64 <;> simp_all [omBv, omNat]
          exact hJ30 (48#64, ()) _ ⟨by simp [h0], by assumption⟩
    · intro J20 hJ20; p2_to_group; p2_split
      · refine hJ20 (1#64, ()) m ⟨?_, rfl⟩
        by_cases h : new_m = 0#64 <;> simp_all [nmBv, nmNat]
      · refine hJ20 (0#64, ()) m ⟨?_, rfl⟩
        by_cases h : new_m = 0#64 <;> simp_all [nmBv, nmNat]
  · intro J10 hJ10; p2_to_group; p2_split
    · refine hJ10 (1#64, ()) m ⟨?_, rfl⟩
      by_cases h : old_m = 0#64 <;> simp_all [omBv, omNat]
    · refine hJ10 (0#64, ()) m ⟨?_, rfl⟩
      by_cases h : old_m = 0#64 <;> simp_all [omBv, omNat]

private theorem p2_m7ModeEmaGet_set_mask (gu : List (BitVec 32)) (mode : Nat) (val : BitVec 64) :
    m7ModeEmaGet (m7Set64List gu m7GuEmaMaskIdx val) mode = m7ModeEmaGet gu mode := by
  have hge : ∀ j, 40 ≤ j → m7Get64Val (m7Set64List gu m7GuEmaMaskIdx val) j = m7Get64Val gu j :=
    fun j hj => m7Get64Val_set64_ne val (Or.inr (by rw [m7GuEmaMaskIdx_eq]; omega))
  rw [m7ModeEmaGet_eq, m7ModeEmaGet_eq, m7GuEma0FbIdx_eq, m7GuEma1FbIdx_eq]
  dsimp only
  by_cases hm : mode = 0 <;> simp only [hm, ↓reduceIte]
  · rw [hge 40 (by omega), hge 42 (by omega), hge 44 (by omega), hge 46 (by omega)]
  · rw [hge 48 (by omega), hge 50 (by omega), hge 52 (by omega), hge 54 (by omega)]

private theorem p2_m7Get64Val_emaSet_mask (gu : List (BitVec 32)) (mode : Nat)
    (v : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) :
    m7Get64Val (m7ModeEmaSet gu mode v) m7GuEmaMaskIdx = m7Get64Val gu m7GuEmaMaskIdx := by
  have hltG : ∀ (g : List (BitVec 32)) idx val, 40 ≤ idx →
      m7Get64Val (m7Set64List g idx val) m7GuEmaMaskIdx = m7Get64Val g m7GuEmaMaskIdx :=
    fun g idx val hidx => m7Get64Val_set64_ne val (Or.inl (by rw [m7GuEmaMaskIdx_eq]; omega))
  rw [m7ModeEmaSet_eq, m7GuEma0FbIdx_eq, m7GuEma1FbIdx_eq]
  dsimp only
  by_cases hm : mode = 0 <;> simp only [hm, ↓reduceIte]
  · rw [hltG _ 46 _ (by omega), hltG _ 44 _ (by omega),
      hltG _ 42 _ (by omega), hltG _ 40 _ (by omega)]
  · rw [hltG _ 54 _ (by omega), hltG _ 52 _ (by omega),
      hltG _ 50 _ (by omega), hltG _ 48 _ (by omega)]

private theorem p2_bit0_or_left {a b : BitVec 64} (h : a &&& 1#64 ≠ 0#64) :
    (a ||| b) &&& 1#64 ≠ 0#64 := by
  intro hc
  have h1 := congrArg (fun x : BitVec 64 => x[0]) hc
  simp only [BitVec.getElem_and, BitVec.getElem_or,
    show (1#64 : BitVec 64)[0] = true by decide, Bool.and_true,
    show (0#64 : BitVec 64)[0] = false by decide, Bool.or_eq_false_iff] at h1
  apply h
  apply BitVec.eq_of_getElem_eq
  intro k hk
  rcases k with rfl | k
  · simp [h1.1]
  · have hb : (1#64 : BitVec 64)[k + 1] = false := by
      rw [BitVec.getElem_eq_testBit_toNat, show (1#64 : BitVec 64).toNat = 1 by decide,
        Nat.testBit_succ]
      simp
    simp only [BitVec.getElem_and, BitVec.getElem_zero, hb, Bool.and_false]

private theorem p2_apply_ite {α β : Type} (f : α → β) (P : Prop) [Decidable P] (a b : α) :
    f (if P then a else b) = if P then f a else f b := by
  by_cases h : P <;> simp [h]

private theorem p2_ite_eq {α : Type} (P : Prop) [Decidable P] {a b c : α}
    (ha : a = c) (hb : b = c) : (if P then a else b) = c := by
  by_cases h : P <;> simp [h, ha, hb]

private theorem p2_emaSwapSc_proj {α : Type} (f : FullScratch → α)
    (hf : ∀ (sc : FullScratch) st fb fe sb se gu,
      f { sc with
        stable := st, ema_fast_biased := fb, ema_fast_exp := fe,
        ema_slow_biased := sb, ema_slow_exp := se, glue_used := gu } = f sc)
    (sc : FullScratch) (om nm : BitVec 64) :
    f (m7EmaSwapSc sc om nm) = f sc := by
  rw [m7EmaSwapSc_eq]; dsimp only
  rw [p2_apply_ite f]
  exact p2_ite_eq _ (hf _ _ _ _ _ _ _) (hf _ _ _ _ _ _ _)

private theorem p2_ema_swap_f2s_stable (sc : FullScratch) :
    (m7EmaSwapSc sc 0#64 1#64).stable = 1#64 := by
  rw [m7EmaSwapSc_eq]; dsimp only
  rw [p2_apply_ite FullScratch.stable]
  exact p2_ite_eq _ rfl rfl

private theorem p2_ema_swap_s2f_facts (sc : FullScratch) (hgu : sc.glue_used.length = 64) :
    let sc' := m7EmaSwapSc sc 1#64 0#64
    sc'.stable = 0#64 ∧
      m7ModeEmaGet sc'.glue_used 1 =
        (sc.ema_fast_biased, sc.ema_fast_exp, sc.ema_slow_biased, sc.ema_slow_exp) ∧
      ((m7Get64Val sc.glue_used m7GuMagicIdx = m7SearchMagic ∧
        (m7Get64Val sc.glue_used m7GuEmaMaskIdx &&& 1#64) ≠ 0#64) →
       let saved := m7ModeEmaGet sc.glue_used 0
       sc'.ema_fast_biased = saved.1 ∧ sc'.ema_fast_exp = saved.2.1 ∧
       sc'.ema_slow_biased = saved.2.2.1 ∧ sc'.ema_slow_exp = saved.2.2.2) := by
  rw [m7EmaSwapSc_eq]
  dsimp only
  simp only [show ((1#64 : BitVec 64) ≠ 0#64) = True by decide,
    show ((0#64 : BitVec 64) ≠ 0#64) = False by decide, ↓reduceIte]
  let gu0 := m7StateInitGu { sc with stable := BitVec.ofNat 64 1 }
  have hgu0 : gu0.length = 64 := (m7StateInitGu_length _).trans hgu
  let curV := (sc.ema_fast_biased, sc.ema_fast_exp, sc.ema_slow_biased, sc.ema_slow_exp)
  let gu1 := m7ModeEmaSet gu0 1 curV
  let mask := m7Get64Val gu1 m7GuEmaMaskIdx ||| 1#64 <<< 1
  refine ⟨?_, ?_, ?_⟩
  · rw [p2_apply_ite FullScratch.stable]
    exact p2_ite_eq _ rfl rfl
  · by_cases hcond : mask &&& 1#64 <<< 0 ≠ 0#64
    · have hc' := hcond; dsimp only [mask, gu1, curV, gu0] at hc'
      simp only [eq_true hc', ↓reduceIte, p2_m7ModeEmaGet_set_mask]
      exact m7ModeEmaGet_set_self curV hgu0
    · have hc' := hcond; dsimp only [mask, gu1, curV, gu0] at hc'
      simp only [eq_false hc', ↓reduceIte, p2_m7ModeEmaGet_set_mask]
      rw [m7ModeEmaGet_set_other _ (by decide : (0 = 0) ≠ (1 = 0))]
      exact m7ModeEmaGet_set_self curV hgu0
  · rintro ⟨hmag, hmask⟩
    have hgu0_eq : gu0 = sc.glue_used := m7StateInitGu_of_magic hmag
    have hmask1 : m7Get64Val gu1 m7GuEmaMaskIdx = m7Get64Val sc.glue_used m7GuEmaMaskIdx := by
      dsimp only [gu1]; rw [p2_m7Get64Val_emaSet_mask, hgu0_eq]
    have hcond : mask &&& 1#64 <<< 0 ≠ 0#64 := by
      rw [show (1#64 <<< 0 : BitVec 64) = 1#64 by decide]
      dsimp only [mask]; rw [hmask1]
      exact p2_bit0_or_left hmask
    have hc' := hcond; dsimp only [mask, gu1, curV, gu0] at hc'
    simp only [eq_true hc', ↓reduceIte]
    have hnw : m7ModeEmaGet gu1 0 = m7ModeEmaGet sc.glue_used 0 := by
      dsimp only [gu1]; rw [m7ModeEmaGet_set_other _ (by decide : (1 = 0) ≠ (0 = 0)), hgu0_eq]
    rw [hnw]
    exact ⟨rfl, rfl, rfl, rfl⟩

private theorem p2_probePres_emaSwap (sc : FullScratch) (om nm : BitVec 64)
    {s0 s1 : FullState} (hp : FullProbeScratchPres s0 s1)
    (hsc : s1.scratch = sc) :
    FullProbeScratchPres s0 { s1 with scratch := m7EmaSwapSc sc om nm } := by
  subst hsc
  have h : ∀ {α} (f : FullScratch → α)
      (hf : ∀ (sc : FullScratch) st fb fe sb se gu,
        f { sc with
          stable := st, ema_fast_biased := fb, ema_fast_exp := fe,
          ema_slow_biased := sb, ema_slow_exp := se, glue_used := gu } = f sc),
      f (m7EmaSwapSc s1.scratch om nm) = f s1.scratch :=
    fun f hf => p2_emaSwapSc_proj f hf s1.scratch om nm
  exact ⟨⟨(h _ fun _ _ _ _ _ _ _ => rfl).trans hp.1.1,
      (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.1.2⟩,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.2.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.2.2.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.2.2.2.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.2.2.2.2.2⟩

private theorem p2_shl1_toNat_lt {i : BitVec 64} {n : Nat}
    (hi : i.toNat < n) (hn : n < 2 ^ 60) : (i <<< (1 : Nat)).toNat = 2 * i.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem p2_lshr1_toNat_le (x : BitVec 64) : (x >>> (1 : Nat)).toNat ≤ x.toNat := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  omega

local macro "p2_jnz_split" h:ident : tactic =>
  `(tactic| (rw [wp_jnz]; dsimp only [Arg.val]; refine ⟨fun $h => ?_, fun $h => ?_⟩))

private theorem p2_lengthsOk_of {c : FullCfg} {s s' : FullState}
    (h : s.LengthsOk c) (hc : s'.core = s.core)
    (h1 : s'.scratch.walk_vals = s.scratch.walk_vals)
    (h2 : s'.scratch.phases = s.scratch.phases)
    (h3 : s'.scratch.phases_target = s.scratch.phases_target)
    (h4 : s'.scratch.phases_best = s.scratch.phases_best)
    (h5 : s'.scratch.walk_best = s.scratch.walk_best)
    (h6 : s'.scratch.heap = s.scratch.heap) (h7 : s'.scratch.pos = s.scratch.pos)
    (h8 : s'.scratch.shrink_stk = s.scratch.shrink_stk)
    (h9 : s'.scratch.q_prev = s.scratch.q_prev) (h10 : s'.scratch.q_next = s.scratch.q_next)
    (h11 : s'.scratch.q_stamp = s.scratch.q_stamp) (h12 : s'.scratch.wsort = s.scratch.wsort)
    (h13 : s'.scratch.work_stk1 = s.scratch.work_stk1)
    (h14 : s'.scratch.work_stk2 = s.scratch.work_stk2)
    (h15 : s'.scratch.tarjan_mark = s.scratch.tarjan_mark)
    (h16 : s'.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (h17 : s'.scratch.score = s.scratch.score) (h18 : s'.scratch.sim_sig = s.scratch.sim_sig)
    (h19 : s'.scratch.glue_used = s.scratch.glue_used)
    (h20 : s'.scratch.last_learned = s.scratch.last_learned)
    (h21 : s'.scratch.delayed = s.scratch.delayed)
    (h22 : s'.scratch.red_refs = s.scratch.red_refs)
    (h23 : s'.scratch.extend_stk = s.scratch.extend_stk)
    (h24 : s'.scratch.scratch_buf = s.scratch.scratch_buf) :
    s'.LengthsOk c :=
  ⟨hc ▸ h.core_ok,
    { walk_vals_len := h1 ▸ h.scratch_ok.walk_vals_len
      phases_len := h2 ▸ h.scratch_ok.phases_len
      phases_target_len := h3 ▸ h.scratch_ok.phases_target_len
      phases_best_len := h4 ▸ h.scratch_ok.phases_best_len
      walk_best_len := h5 ▸ h.scratch_ok.walk_best_len
      heap_len_arr := h6 ▸ h.scratch_ok.heap_len_arr
      pos_len := h7 ▸ h.scratch_ok.pos_len
      shrink_stk_len := h8 ▸ h.scratch_ok.shrink_stk_len
      q_prev_len := h9 ▸ h.scratch_ok.q_prev_len
      q_next_len := h10 ▸ h.scratch_ok.q_next_len
      q_stamp_len := h11 ▸ h.scratch_ok.q_stamp_len
      wsort_len := h12 ▸ h.scratch_ok.wsort_len
      work_stk1_len := h13 ▸ h.scratch_ok.work_stk1_len
      work_stk2_len := h14 ▸ h.scratch_ok.work_stk2_len
      tarjan_mark_len := h15 ▸ h.scratch_ok.tarjan_mark_len
      tarjan_reach_len := h16 ▸ h.scratch_ok.tarjan_reach_len
      score_len := h17 ▸ h.scratch_ok.score_len
      sim_sig_len := h18 ▸ h.scratch_ok.sim_sig_len
      glue_used_len := h19 ▸ h.scratch_ok.glue_used_len
      last_learned_len := h20 ▸ h.scratch_ok.last_learned_len
      delayed_len_arr := h21 ▸ h.scratch_ok.delayed_len_arr
      red_refs_len := h22 ▸ h.scratch_ok.red_refs_len
      extend_stk_len := h23 ▸ h.scratch_ok.extend_stk_len
      scratch_buf_len := h24 ▸ h.scratch_ok.scratch_buf_len }⟩

/-- Parametric WP proof for `full_switch_mode_m7` against `m7SwitchModeSpec`. -/
theorem full_switch_mode_m7_wp (Γ : Env)
    (hIlog : EnvSpec Γ "full_ilog10" fullIlog10Spec)
    (hHeapDown : EnvSpec Γ "full_heap_down" fullHeapDownSpec)
    (hEmaSwap : EnvSpec Γ "full_ema_swap_m7" m7EmaSwapSpec)
    (hLog10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec) :
    ∀ a m Q X, m7SwitchModeSpec a m Q X → Func.wp Γ full_switch_mode_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hspec
  obtain ⟨c, s, R, hc_eq, hlen, hm, hQ⟩ := m7SwitchModeSpec_elim hspec
  dsimp only at hc_eq; subst hc_eq
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  have hok := hlen.core_ok
  have hsok := hlen.scratch_ok
  have hcv_le := hok.cur_vars_le
  let P : Tup Val [i64, i64] → Mem 64 → Prop := fun (om, nm, _) mJ =>
    ∃ sJ : FullState,
      sJ.core = s.core ∧ sJ.LengthsOk c ∧ FullProbeScratchPres s sJ ∧
      om = (if s.scratch.stable = 0#64 then 0#64 else 1#64) ∧
      nm = (if s.scratch.stable = 0#64 then 1#64 else 0#64) ∧
      (s.scratch.stable = 0#64 → s.scratch.mode_confl_lim ≤ s.scratch.conflicts) ∧
      (s.scratch.stable ≠ 0#64 →
        s.scratch.mode_tick_lim ≤ s.scratch.search_ticks ∧ M7GuPrefixPres s sJ ∧
        sJ.scratch.glue_used = s.scratch.glue_used ∧
        sJ.scratch.ema_fast_biased = s.scratch.ema_fast_biased ∧
        sJ.scratch.ema_fast_exp = s.scratch.ema_fast_exp ∧
        sJ.scratch.ema_slow_biased = s.scratch.ema_slow_biased ∧
        sJ.scratch.ema_slow_exp = s.scratch.ema_slow_exp) ∧
      (FullMem c sJ ⋆ R) mJ
  refine wp_join_group P ?_ ?_
  · rintro Js ⟨om, nm, ⟨⟩⟩ mJ ⟨sJ, hcJ, hlenJ, hpsJ, hom, hnm, hf2s, hs2f, hmJ⟩
    rw [Blocks.get_here]
    p2_steps_raw
    let sJ1 : FullState := { sJ with scratch := { sJ.scratch with
      switched := sJ.scratch.switched + 1#64
      mode_count := sJ.scratch.mode_count + 1#64 } }
    have hlenJ1 : sJ1.LengthsOk c :=
      p2_lengthsOk_of hlenJ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    p2_call hEmaSwap
    refine m7EmaSwapSpec_of hlenJ1 (by assumption) fun hlenSw hpreSw hinitSw mSw hmSw => ?_
    let sSw : FullState := { sJ1 with scratch := m7EmaSwapSc sJ1.scratch om nm }
    let Pret : Tup Val [] → Mem 64 → Prop := fun _ mRet =>
      ∃ sRet : FullState,
        sRet.core = s.core ∧ sRet.LengthsOk c ∧ FullProbeScratchPres s sRet ∧
        (s.scratch.stable = 0#64 →
          M7StateInitOk sRet.scratch.glue_used ∧ sRet.scratch.stable = 1#64) ∧
        (s.scratch.stable ≠ 0#64 →
          M7GuPrefixPres s sRet ∧ M7StateInitOk sRet.scratch.glue_used ∧
          m7ModeEmaGet sRet.scratch.glue_used 1 =
            (s.scratch.ema_fast_biased, s.scratch.ema_fast_exp,
             s.scratch.ema_slow_biased, s.scratch.ema_slow_exp) ∧
          sRet.scratch.stable = 0#64 ∧
          ((m7Get64Val s.scratch.glue_used m7GuMagicIdx = m7SearchMagic ∧
            (m7Get64Val s.scratch.glue_used m7GuEmaMaskIdx &&& 1#64) ≠ 0#64) →
           let saved := m7ModeEmaGet s.scratch.glue_used 0
           sRet.scratch.ema_fast_biased = saved.1 ∧ sRet.scratch.ema_fast_exp = saved.2.1 ∧
           sRet.scratch.ema_slow_biased = saved.2.2.1 ∧
           sRet.scratch.ema_slow_exp = saved.2.2.2)) ∧
        (FullMem c sRet ⋆ R) mRet
    refine wp_join_group Pret ?_ ?_
    · rintro Js_r ⟨⟩ mRet ⟨sRet, hcRet, hlenRet, hpsRet, hrf2s, hrs2f, hmRet⟩
      rw [Blocks.get_here]
      p2_steps_raw
      refine hQ sRet mRet hcRet hlenRet hpsRet ?_ ?_ ?_ hmRet
      · intro hEarly
        exfalso
        rcases hEarly with ⟨hst0, hlt⟩ | ⟨hstne, hlt⟩
        · have hle := hf2s hst0
          exact Nat.not_lt_of_ge (BitVec.le_def.mp hle) (BitVec.lt_def.mp hlt)
        · have hle := (hs2f hstne).1
          exact Nat.not_lt_of_ge (BitVec.le_def.mp hle) (BitVec.lt_def.mp hlt)
      · rintro ⟨hst0, _⟩; exact hrf2s hst0
      · rintro ⟨hstne, _⟩; exact hrs2f hstne
    · intro Js_r hJs_r
      have hpsSw : FullProbeScratchPres s sSw :=
        p2_probePres_emaSwap sJ1.scratch om nm hpsJ rfl
      p2_steps_raw
      p2_jnz_split hstab0
      · simp only [beq_iff_eq] at hstab0
        have hstne : s.scratch.stable ≠ 0#64 := by
          intro hst0
          have hom0 : om = 0#64 := by simp [hom, hst0]
          have hnm1 : nm = 1#64 := by simp [hnm, hst0]
          have h1 : sSw.scratch.stable = 1#64 := by
            dsimp only [sSw]; rw [hom0, hnm1]; exact p2_ema_swap_f2s_stable _
          rw [h1] at hstab0
          exact absurd hstab0 (by decide)
        obtain ⟨_, hpreJ, hguJ, hfbJ, hfeJ, hsbJ, hseJ⟩ := hs2f hstne
        have hom1 : om = 1#64 := by simp [hom, hstne]
        have hnm0 : nm = 0#64 := by simp [hnm, hstne]
        have hguSw : sJ1.scratch.glue_used.length = 64 := hlenJ1.scratch_ok.glue_used_len
        have hfacts := p2_ema_swap_s2f_facts sJ1.scratch hguSw
        have heq_f : sSw.scratch = m7EmaSwapSc sJ1.scratch 1#64 0#64 := by
          dsimp only [sSw]; rw [hom1, hnm0]
        p2_steps_raw
        refine wp_join_group (ts := [i64]) (fun _ mRl => mRl = mSw) ?_ ?_
        · rintro J_rl ⟨rs, ⟨⟩⟩ mRl rfl
          rw [Blocks.get_here]
          p2_steps_raw
          let sRet : FullState := { sSw with scratch := { sSw.scratch with
            restart_limit := sSw.scratch.conflicts + rs } }
          have hlenRet : sRet.LengthsOk c :=
            p2_lengthsOk_of hlenSw rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          refine hJs_r () _ ⟨sRet, hcJ, hlenRet,
            hpsSw, fun h0 => absurd h0 hstne, fun _ => ?_, by assumption⟩
          have hpre_full : M7GuPrefixPres s sRet :=
            M7GuPrefixPres.trans hpreJ (@M7GuPrefixPres.congr_glue sJ1 sSw sJ sRet rfl rfl hpreSw)
          have hema1 : m7ModeEmaGet sRet.scratch.glue_used 1 =
              (s.scratch.ema_fast_biased, s.scratch.ema_fast_exp,
               s.scratch.ema_slow_biased, s.scratch.ema_slow_exp) := by
            change m7ModeEmaGet sSw.scratch.glue_used 1 = _
            rw [heq_f, hfacts.2.1]
            change (sJ.scratch.ema_fast_biased, sJ.scratch.ema_fast_exp,
              sJ.scratch.ema_slow_biased, sJ.scratch.ema_slow_exp) = _
            rw [hfbJ, hfeJ, hsbJ, hseJ]
          have hmag_eq : m7Get64Val sJ1.scratch.glue_used m7GuMagicIdx =
              m7Get64Val s.scratch.glue_used m7GuMagicIdx := by
            change m7Get64Val sJ.scratch.glue_used _ = _; rw [hguJ]
          have hmsk_eq : m7Get64Val sJ1.scratch.glue_used m7GuEmaMaskIdx =
              m7Get64Val s.scratch.glue_used m7GuEmaMaskIdx := by
            change m7Get64Val sJ.scratch.glue_used _ = _; rw [hguJ]
          have hget0_eq : m7ModeEmaGet sJ1.scratch.glue_used 0 =
              m7ModeEmaGet s.scratch.glue_used 0 := by
            change m7ModeEmaGet sJ.scratch.glue_used 0 = _; rw [hguJ]
          refine ⟨hpre_full, hinitSw, hema1,
            (by change sSw.scratch.stable = 0#64; rw [heq_f]; exact hfacts.1),
            fun ⟨hm1, hm2⟩ => ?_⟩
          have hsaved := hfacts.2.2 ⟨by rw [hmag_eq]; exact hm1, by rw [hmsk_eq]; exact hm2⟩
          rw [← hget0_eq]
          change sSw.scratch.ema_fast_biased = _ ∧ sSw.scratch.ema_fast_exp = _ ∧
            sSw.scratch.ema_slow_biased = _ ∧ sSw.scratch.ema_slow_exp = _
          rw [heq_f]
          exact hsaved
        · intro J_rl hJ_rl
          p2_steps_raw
          p2_jnz_split hrg0
          · p2_steps_raw
            refine wp_join_group (ts := [i64]) (fun _ m2 => m2 = mSw) ?_ ?_
            · rintro J_r2 ⟨rc, ⟨⟩⟩ m2 hm2
              subst m2
              rw [Blocks.get_here]
              p2_steps_raw
              p2_call hIlog
              intro r _ _
              refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = mSw) ?_ ?_
              · rintro J_r3 ⟨d, ⟨⟩⟩ m3 hm3
                subst m3
                rw [Blocks.get_here]
                p2_steps_raw
                exact hJ_rl (d, ()) mSw rfl
              · intro J_r3 hJ_r3
                p2_steps_raw
                p2_jnz_split hdg1 <;> p2_steps_raw <;> exact hJ_r3 _ mSw rfl
            · intro J_r2 hJ_r2
              p2_steps_raw
              p2_jnz_split hrlim <;> p2_steps_raw <;> exact hJ_r2 _ mSw rfl
          · p2_steps_raw; exact hJ_rl (1#64, ()) mSw rfl
      · simp only [beq_eq_false_iff_ne] at hstab0
        have hst0 : s.scratch.stable = 0#64 := by
          by_cases hst : s.scratch.stable = 0#64
          · exact hst
          · exfalso
            have hom1 : om = 1#64 := by simp [hom, hst]
            have hnm0 : nm = 0#64 := by simp [hnm, hst]
            have h0 : sSw.scratch.stable = 0#64 := by
              dsimp only [sSw]; rw [hom1, hnm0]
              exact (p2_ema_swap_s2f_facts sJ1.scratch hlenJ1.scratch_ok.glue_used_len).1
            exact hstab0 h0
        have hom0 : om = 0#64 := by simp [hom, hst0]
        have hnm1 : nm = 1#64 := by simp [hnm, hst0]
        have h1 : sSw.scratch.stable = 1#64 := by
          dsimp only [sSw]; rw [hom0, hnm1]; exact p2_ema_swap_f2s_stable _
        p2_steps_raw
        exact hJs_r () mSw ⟨sSw, hcJ, hlenSw, hpsSw,
          fun _ => ⟨hinitSw, h1⟩, fun hne => absurd hst0 hne, hmSw⟩
  · intro Js hJs
    p2_steps_raw
    p2_jnz_split hst0
    · simp only [beq_iff_eq] at hst0
      p2_steps_raw
      p2_jnz_split hconfl
      · simp only [BitVec.ult, decide_eq_true_eq] at hconfl
        p2_steps_raw
        exact hQ s m rfl hlen (p2_probePres_refl s) (fun _ => rfl)
          (fun ⟨_, hle⟩ => absurd (BitVec.le_def.mp hle) (Nat.not_le_of_gt hconfl))
          (fun ⟨hne, _⟩ => absurd hst0 hne) hm
      · simp only [BitVec.ult, decide_eq_false_iff_not] at hconfl
        have hle_confl : s.scratch.mode_confl_lim ≤ s.scratch.conflicts :=
          BitVec.le_def.mpr (Nat.le_of_not_lt hconfl)
        p2_steps_raw
        let s1 : FullState := { s with scratch := { s.scratch with stable := 1#64 } }
        refine wp_join_group (ts := [i64])
          (fun _ m1 => (FullMem c s1 ⋆ R) m1) ?_ ?_
        · rintro J_d ⟨delta, ⟨⟩⟩ m1 hm1
          rw [Blocks.get_here]
          p2_steps_raw
          let s2 : FullState := { s1 with scratch := { s1.scratch with
            mode_tick_lim := s1.scratch.search_ticks + delta
            mode_saved_ticks := s1.scratch.search_ticks } }
          refine wp_join_group (ts := [i64])
            (fun _ m2 => (FullMem c s2 ⋆ R) m2) ?_ ?_
          · rintro J_l ⟨lim, ⟨⟩⟩ m2 hm2
            rw [Blocks.get_here]
            p2_steps_raw
            let s3 : FullState := { s2 with scratch := { s2.scratch with
              rel_wait := lim, rel_u := 1#64, rel_v := 1#64, rel_trigger := 0#64 } }
            have hlen3 : s3.LengthsOk c :=
              p2_lengthsOk_of hlen rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            have hps3 : FullProbeScratchPres s s3 := p2_probePres_refl s
            refine wp_loop_inv (ts := [i64, i64])
              (fun (hl, i, ()) mL => ∃ hp ps : List (BitVec 32),
                hp.length = c.max_vars ∧ ps.length = c.max_vars ∧
                hl.toNat ≤ i.toNat ∧ i.toNat ≤ s.core.cur_vars ∧
                (FullMem c { s3 with scratch :=
                  { s3.scratch with heap := hp, pos := ps } } ⋆ R) mL)
              (fun (_, i, ()) _ => s.core.cur_vars - i.toNat) ?_ ?_
            · intro J3 hJ3
              p2_steps_raw
              exact hJ3 (0#64, 0#64, ()) _ ⟨s3.scratch.heap, s3.scratch.pos,
                hsok.heap_len_arr, hsok.pos_len, by simp, Nat.zero_le _, by assumption⟩
            · rintro J3 ⟨hl, i, ⟨⟩⟩ mL ⟨hp, ps, hhp, hps_len, hle_hi, hi_le, hmL⟩ hJ3
              rw [Blocks.get_here]
              p2_steps_raw
              p2_jnz_split hilt
              · simp only [BitVec.ult, decide_eq_true_eq] at hilt
                have hi_lt : i.toNat < s.core.cur_vars := by
                  change _ < s.core.cur_vars % 2 ^ 64 at hilt
                  rw [Nat.mod_eq_of_lt (by omega)] at hilt
                  exact hilt
                have hi_mx : i.toNat < c.max_vars := by omega
                have h2i_len : (i <<< (1 : Nat)).toNat < s3.core.vals.length := by
                  rw [hok.vals_len, p2_shl1_toNat_lt hi_mx (by omega)]; omega
                refine wp_join_group (ts := [i64])
                  (fun (hl', ()) mN => ∃ hp' ps' : List (BitVec 32),
                    hp'.length = c.max_vars ∧ ps'.length = c.max_vars ∧
                    hl'.toNat ≤ i.toNat + 1 ∧
                    (FullMem c { s3 with scratch :=
                      { s3.scratch with heap := hp', pos := ps' } } ⋆ R) mN)
                  ?_ ?_
                · rintro J_nx ⟨hl', ⟨⟩⟩ mN ⟨hp', ps', hhp', hps', hle', hmN⟩
                  rw [Blocks.get_here]
                  p2_steps_raw
                  have hi1 : (i + 1#64).toNat = i.toNat + 1 := p2_bv64_add1_toNat (by omega)
                  exact hJ3 (hl', i + 1#64, ()) mN (by dsimp only; rw [hi1]; omega)
                    ⟨hp', ps', hhp', hps', by rw [hi1]; exact hle', by omega, hmN⟩
                · intro J_nx hJ_nx
                  refine wp_join_group (ts := [])
                    (fun _ mA => (FullMem c { s3 with scratch :=
                      { s3.scratch with heap := hp, pos := ps } } ⋆ R) mA)
                    ?_ ?_
                  · rintro J_else ⟨⟩ mA hmA
                    rw [Blocks.get_here]
                    have hps_lt : i.toNat < ps.length := by omega
                    p2_steps_raw
                    exact hJ_nx (hl, ()) _ ⟨hp, ps.set i.toNat 0xFFFFFFFF#32, hhp,
                      by simpa using hps_len, by omega, by assumption⟩
                  · intro J_else hJ_else
                    have hfl_lt : i.toNat < s3.core.flags.length := by
                      rw [hok.flags_len]; omega
                    p2_steps_raw
                    p2_jnz_split hact
                    · p2_steps_raw
                      p2_jnz_split hun
                      · have hhp_lt : hl.toNat < hp.length := by omega
                        have hps_lt : i.toNat < ps.length := by omega
                        rw [wp_let_mul_eq]
                        simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val]
                        rw [wp_let_add_eq]
                        simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val]
                        p2_steps_raw
                        have hhl1 : (hl + 1#64).toNat = hl.toNat + 1 :=
                          p2_bv64_add1_toNat (by omega)
                        exact hJ_nx (hl + 1#64, ()) _ ⟨hp.set hl.toNat (i.setWidth 32),
                          ps.set i.toNat (hl.setWidth 32), by simpa using hhp,
                          by simpa using hps_len, by omega, by assumption⟩
                      · p2_steps_raw; exact hJ_else () _ (by assumption)
                    · p2_steps_raw; exact hJ_else () _ (by assumption)
              · p2_steps_raw
                have hhl_le : hl.toNat ≤ c.max_vars := by omega
                let s4 : FullState := { s3 with scratch :=
                  { s3.scratch with heap := hp, pos := ps, heap_len := hl.toNat } }
                have hlen4 : s4.LengthsOk c :=
                  ⟨hlen3.core_ok,
                    { hlen3.scratch_ok with heap_len_arr := hhp, pos_len := hps_len }⟩
                refine wp_loop_inv (ts := [i64])
                  (fun (k, ()) mD => ∃ sD : FullState,
                    sD.core = s.core ∧ sD.LengthsOk c ∧ FullProbeScratchPres s sD ∧
                    k.toNat ≤ c.max_vars ∧ (FullMem c sD ⋆ R) mD)
                  (fun (k, ()) _ => k.toNat) ?_ ?_
                · intro J4 hJ4
                  p2_steps_raw
                  exact hJ4 (hl >>> 1#64, ()) _ ⟨s4, rfl, hlen4, hps3,
                    le_trans (p2_lshr1_toNat_le hl) hhl_le, by assumption⟩
                · rintro J4 ⟨k, ⟨⟩⟩ mD ⟨sD, hcD, hlenD, hpsD, hk_le, hmD⟩ hJ4
                  rw [Blocks.get_here]
                  p2_steps_raw
                  p2_jnz_split hkpos
                  · simp only [BitVec.ult, decide_eq_true_eq] at hkpos
                    have hk_gt : 0 < k.toNat := by
                      simpa using hkpos
                    have hk1 : (k - 1#64).toNat = k.toNat - 1 :=
                      p2_bv64_sub1_toNat (fun h => by simp [h] at hk_gt)
                    have hk1_hp : (k - 1#64).toNat < sD.scratch.heap.length := by
                      rw [hlenD.scratch_ok.heap_len_arr]; omega
                    p2_steps_raw
                    p2_call hHeapDown
                    refine ⟨c, sD, R, rfl, hlenD, hmD, fun () sD' mD' hcD' hlenD' hpost hmD' => ?_⟩
                    rcases hpost with ⟨_, hpsD'⟩
                    have hcD'_eq : sD'.core = sD.core := hcD'
                    exact hJ4 (k - 1#64, ()) mD' (by dsimp only; rw [hk1]; omega)
                      ⟨sD', hcD'_eq.trans hcD, hlenD', p2_probePres_trans hpsD hpsD',
                        by rw [hk1]; omega, hmD'⟩
                  · p2_steps_raw
                    exact hJs (0#64, 1#64, ()) mD ⟨sD, hcD, hlenD, hpsD,
                      by simp [hst0], by simp [hst0], fun _ => hle_confl,
                      fun hne => absurd hst0 hne, hmD⟩
          · intro J_l hJ_l
            p2_steps_raw
            p2_jnz_split hlim1
            · p2_steps_raw
              p2_jnz_split hlim2 <;> p2_steps_raw <;> exact hJ_l _ _ (by assumption)
            · p2_steps_raw; exact hJ_l _ _ (by assumption)
        · intro J_d hJ_d
          p2_steps_raw
          p2_jnz_split hdiff <;> p2_steps_raw <;> exact hJ_d _ _ (by assumption)
    · simp only [beq_eq_false_iff_ne] at hst0
      p2_steps_raw
      p2_jnz_split hticks
      · simp only [BitVec.ult, decide_eq_true_eq] at hticks
        p2_steps_raw
        exact hQ s m rfl hlen (p2_probePres_refl s) (fun _ => rfl)
          (fun ⟨h0, _⟩ => absurd h0 hst0)
          (fun ⟨_, hle⟩ => absurd (BitVec.le_def.mp hle) (Nat.not_le_of_gt hticks)) hm
      · simp only [BitVec.ult, decide_eq_false_iff_not] at hticks
        have hle_ticks : s.scratch.mode_tick_lim ≤ s.scratch.search_ticks :=
          BitVec.le_def.mpr (Nat.le_of_not_lt hticks)
        p2_steps_raw
        let s1 : FullState := { s with scratch := { s.scratch with stable := 0#64 } }
        refine wp_join_group (ts := [i64]) (fun _ m1 => (FullMem c s1 ⋆ R) m1) ?_ ?_
        · rintro J_c ⟨cc, ⟨⟩⟩ m1 hm1
          rw [Blocks.get_here]
          p2_steps_raw
          p2_call hLog10
          refine m7Log10Q16Spec_of fun r _ _ => ?_
          p2_steps_raw
          refine wp_join_group (ts := [i64]) (fun _ m2 => (FullMem c s1 ⋆ R) m2) ?_ ?_
          · rintro J_d ⟨delta, ⟨⟩⟩ m2 hm2
            rw [Blocks.get_here]
            p2_steps_raw
            let s4 : FullState := { s1 with scratch := { s1.scratch with
              mode_confl_lim := s1.scratch.conflicts + delta
              mode_saved_ticks := s1.scratch.search_ticks
              q_search_idx := s1.scratch.q_last } }
            refine wp_join_group (ts := [])
              (fun _ m5 => ∃ qss : BitVec 64,
                (FullMem c { s4 with scratch :=
                  { s4.scratch with q_search_stamp := qss } } ⋆ R) m5) ?_ ?_
            · rintro J_q ⟨⟩ m5 ⟨qss, hm5⟩
              rw [Blocks.get_here]
              p2_steps_raw
              let sJ : FullState := { s4 with scratch :=
                { s4.scratch with q_search_stamp := qss } }
              have hlenJ : sJ.LengthsOk c :=
                p2_lengthsOk_of hlen rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                  rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
              exact hJs (1#64, 0#64, ()) m5 ⟨sJ, rfl, hlenJ, p2_probePres_refl s,
                by rw [ite_eq_right_iff.mpr fun h => absurd h (by simpa using hst0)],
                by rw [ite_eq_right_iff.mpr fun h => absurd h (by simpa using hst0)],
                fun h0 => absurd h0 hst0,
                fun _ => ⟨hle_ticks, @M7GuPrefixPres.congr_glue s s s sJ rfl rfl
                  (M7GuPrefixPres.refl s), rfl, rfl, rfl, rfl, rfl⟩, hm5⟩
            · intro J_q hJ_q
              p2_steps_raw
              p2_jnz_split hqlt
              · simp only [BitVec.ult, decide_eq_true_eq] at hqlt
                have hq_nat : s.scratch.q_last.toNat < s.core.cur_vars := by
                  change _ < s.core.cur_vars % 2 ^ 64 at hqlt
                  rw [Nat.mod_eq_of_lt (by omega)] at hqlt
                  exact hqlt
                have hq_len : s.scratch.q_last.toNat < s.scratch.q_stamp.length := by
                  rw [hsok.q_stamp_len]; omega
                p2_steps_raw
                exact hJ_q () _ ⟨_, by assumption⟩
              · p2_steps_raw
                exact hJ_q () _ ⟨s4.scratch.q_search_stamp, by assumption⟩
          · intro J_d hJ_d
            p2_steps_raw
            p2_jnz_split hcle
            · p2_steps_raw; exact hJ_d _ _ (by assumption)
            · p2_steps_raw
              refine wp_join_group (ts := [i64]) (fun _ mx => (FullMem c s1 ⋆ R) mx) ?_ ?_
              · rintro J_x ⟨cv, ⟨⟩⟩ mx hmx2
                rw [Blocks.get_here]
                p2_steps_raw; exact hJ_d _ _ hmx2
              · intro J_x hJ_x
                p2_steps_raw
                p2_jnz_split hcgt <;> p2_steps_raw <;> exact hJ_x _ _ (by assumption)
        · intro J_c hJ_c
          p2_steps_raw
          p2_jnz_split hcc <;> p2_steps_raw <;> exact hJ_c _ _ (by assumption)

/-- Canonical `Full.fullSwitchModeSpec` drop-in WP proof for `full_switch_mode_m7`. -/
theorem full_switch_mode_m7_dropin_wp (Γ : Env)
    (hIlog : EnvSpec Γ "full_ilog10" fullIlog10Spec)
    (hHeapDown : EnvSpec Γ "full_heap_down" fullHeapDownSpec)
    (hEmaSwap : EnvSpec Γ "full_ema_swap_m7" m7EmaSwapSpec)
    (hLog10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec) :
    ∀ a m Q X, Full.fullSwitchModeSpec a m Q X →
      Func.wp Γ full_switch_mode_m7_body a m Q X :=
  fun _ _ _ _ hs =>
    full_switch_mode_m7_wp Γ hIlog hHeapDown hEmaSwap hLog10 _ _ _ _
      (m7SwitchModeSpec_to_canon hs)

/-! ## 4. `full_randec_var_m7` `Func.wp` Proof -/

private theorem p2_sext32_eq0 (x : BitVec 8) (h : BitVec.signExtend 32 x = 0#32) :
    x = 0#8 := by
  revert x h; decide

/-- Parametric WP proof for `full_randec_var_m7` against `m7RandecVarSpec`. -/
theorem full_randec_var_m7_wp (Γ : Env)
    (hLcg : EnvSpec Γ "full_lcg_next_m7" m7LcgNextSpec)
    (hInit : EnvSpec Γ "full_m7_state_init" m7StateInitSpec)
    (hGet : EnvSpec Γ "full_m7_get64" m7Get64Spec)
    (hSet : EnvSpec Γ "full_m7_set64" m7Set64Spec)
    (hLog10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec) :
    ∀ a m Q X, m7RandecVarSpec a m Q X → Func.wp Γ full_randec_var_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hspec
  obtain ⟨c, s, R, rfl, hlen, hm, hQ⟩ := m7RandecVarSpec_elim hspec
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  have hok := hlen.core_ok
  have hsok := hlen.scratch_ok
  have hcv_le := hok.cur_vars_le
  let mkS : List (BitVec 32) → BitVec 64 → FullState := fun gu rng =>
    { s with scratch := { s.scratch with glue_used := gu, rng_state := rng } }
  have mkS_len : ∀ gu rng, gu.length = 64 → (mkS gu rng).LengthsOk c := fun gu rng hgu =>
    ⟨hlen.core_ok, { hsok with glue_used_len := hgu }⟩
  let ret_neg1 := fun {gu : List (BitVec 32)} {rng : BitVec 64} {ml : Mem 64}
      (hln : (mkS gu rng).LengthsOk c) (hp : M7GuPrefixPres s (mkS gu rng))
      (hml : (FullMem c (mkS gu rng) ⋆ R) ml) =>
    hQ 0xFFFFFFFFFFFFFFFF#64 (mkS gu rng) ml rfl hln
      ⟨p2_probePres_refl s, hp, Or.inl rfl⟩ hml
  unfold Func.wp full_randec_var_m7_body
  p2_steps
  · exact hQ 0xFFFFFFFFFFFFFFFF#64 s m rfl hlen
      ⟨p2_probePres_refl s, M7GuPrefixPres.refl s, Or.inl rfl⟩ hm
  · exact hQ 0xFFFFFFFFFFFFFFFF#64 s m rfl hlen
      ⟨p2_probePres_refl s, M7GuPrefixPres.refl s, Or.inl rfl⟩ hm
  · exact hQ 0xFFFFFFFFFFFFFFFF#64 s m rfl hlen
      ⟨p2_probePres_refl s, M7GuPrefixPres.refl s, Or.inl rfl⟩ hm
  · have hcv_pos : 0 < s.core.cur_vars := Nat.pos_of_ne_zero fun h0 => by
      simp_all
    p2_call hInit
    refine m7StateInitSpec_of hlen hm fun hlen0 hi0 hp0 m0 hm0 => ?_
    let gu0 := m7StateInitGu s.scratch
    have hgu0 : gu0.length = 64 := hi0.len
    have hm0' : (FullMem c (mkS gu0 s.scratch.rng_state) ⋆ R) m0 := hm0
    have hlen0' : (mkS gu0 s.scratch.rng_state).LengthsOk c := mkS_len gu0 _ hgu0
    have hp0' : M7GuPrefixPres s (mkS gu0 s.scratch.rng_state) := hp0
    p2_steps_raw
    p2_call hGet
    refine m7Get64Spec_of hlen0' hm0' ?_
    p2_steps_raw
    p2_call hGet
    refine m7Get64Spec_of hlen0' hm0' ?_
    p2_steps_raw
    refine wp_join_group (ts := [i64])
      (fun _ m1 => ∃ gu1 : List (BitVec 32), gu1.length = 64 ∧
        M7GuPrefixPres s (mkS gu1 s.scratch.rng_state) ∧
        (FullMem c (mkS gu1 s.scratch.rng_state) ⋆ R) m1) ?_ ?_
    · rintro J1 ⟨rem1, ⟨⟩⟩ m1 ⟨gu1, hgu1, hp1, hm1⟩
      rw [Blocks.get_here]
      have hlen1 := mkS_len gu1 s.scratch.rng_state hgu1
      p2_steps_raw
      refine wp_join_group (ts := [i64])
        (fun _ m2 => ∃ gu2 : List (BitVec 32), gu2.length = 64 ∧
          M7GuPrefixPres s (mkS gu2 s.scratch.rng_state) ∧
          (FullMem c (mkS gu2 s.scratch.rng_state) ⋆ R) m2) ?_ ?_
      · rintro J2 ⟨rem2, ⟨⟩⟩ m2 ⟨gu2, hgu2, hp2, hm2⟩
        rw [Blocks.get_here]
        have hlen2 := mkS_len gu2 s.scratch.rng_state hgu2
        p2_steps_raw
        let max_tries : BitVec 64 :=
          if (BitVec.ofNat 64 s.core.cur_vars) < 4096#64 then
            BitVec.ofNat 64 s.core.cur_vars * 4#64 + 16#64
          else 16384#64
        refine wp_join_group (ts := [i64])
          (fun (mt, ()) m3 => mt.toNat ≤ 16400 ∧
            (FullMem c (mkS gu2 s.scratch.rng_state) ⋆ R) m3) ?_ ?_
        · rintro J3 ⟨mt, ⟨⟩⟩ m3 ⟨hmt, hm3⟩
          rw [Blocks.get_here]
          p2_steps_raw
          refine wp_loop_inv (ts := [i64])
            (fun (tries, ()) mL => ∃ (guL : List (BitVec 32)) (rngL : BitVec 64),
              guL.length = 64 ∧ M7GuPrefixPres s (mkS guL rngL) ∧
              tries.toNat ≤ mt.toNat ∧ (FullMem c (mkS guL rngL) ⋆ R) mL)
            (fun (tries, ()) _ => mt.toNat - tries.toNat) ?_ ?_
          · intro JL hJL
            p2_steps_raw
            exact hJL (0#64, ()) m3 ⟨gu2, s.scratch.rng_state, hgu2, hp2, Nat.zero_le _, hm3⟩
          · rintro JL ⟨tries, ⟨⟩⟩ mL ⟨guL, rngL, hguL, hpL, htr_le, hmL⟩ hJL
            rw [Blocks.get_here]
            have hlenL := mkS_len guL rngL hguL
            p2_steps_raw
            p2_jnz_split hlt
            · simp only [BitVec.ult, decide_eq_true_eq] at hlt
              p2_steps_raw
              p2_call hLcg
              refine m7LcgNextSpec_of hlenL hmL fun lcg_r s' m' hc' hlen' ⟨hr_eq, hsc'⟩ hm' => ?_
              have hs'_eq : s' = mkS guL (m7LcgNextVal rngL).1 := by
                cases s'; simp only [mkS] at *; exact congr (congrArg FullState.mk hc') hsc'
              rw [hs'_eq] at hlen' hm'
              have hp' : M7GuPrefixPres s (mkS guL (m7LcgNextVal rngL).1) :=
                @M7GuPrefixPres.congr_glue s (mkS guL rngL) s (mkS guL (m7LcgNextVal rngL).1)
                  rfl rfl hpL
              have hcv_nat : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
                p2_bv64_ofNat_toNat (by omega)
              let idx := lcg_r % BitVec.ofNat 64 s.core.cur_vars
              have hidx_lt : idx.toNat < s.core.cur_vars := by
                dsimp only [idx]; rw [BitVec.toNat_umod, hcv_nat]; exact Nat.mod_lt _ hcv_pos
              have hidx_fl : idx.toNat < s.core.flags.length := by rw [hok.flags_len]; omega
              have hidx_v : (idx <<< 1#64).toNat = 2 * idx.toNat :=
                M7SearchTactics.bv64_shl1_toNat (by omega)
              have hidx_v2 : (idx <<< 1#64).toNat < s.core.vals.length := by
                rw [hidx_v, hok.vals_len]; omega
              p2_steps_raw
              refine wp_join_group (ts := []) (fun _ mN => mN = m') ?_ ?_
              · rintro Jnext ⟨⟩ mN hmN
                subst hmN
                rw [Blocks.get_here]
                p2_steps_raw
                have htr1 : (tries + 1#64).toNat = tries.toNat + 1 :=
                  p2_bv64_add1_toNat (by omega)
                exact hJL (tries + 1#64, ()) mN (by dsimp only; rw [htr1]; omega)
                  ⟨guL, (m7LcgNextVal rngL).1, hguL, hp', by rw [htr1]; exact hlt, hm'⟩
              · intro Jnext hJnext
                p2_steps_raw
                p2_jnz_split hact
                · p2_steps_raw
                  p2_jnz_split hval0
                  · p2_steps_raw
                    have hfl0 : (mkS guL (m7LcgNextVal rngL).1).core.flags[idx.toNat]?.getD 0#32 &&&
                        1#32 ≠ 0#32 := by
                      rw [List.getElem?_eq_getElem hidx_fl, Option.getD_some]
                      simpa [mkS, idx] using hact
                    have hv0 : (mkS guL (m7LcgNextVal rngL).1).core.vals[2 * idx.toNat]?.getD
                        0#8 = 0#8 := by
                      rw [← hidx_v, List.getElem?_eq_getElem hidx_v2, Option.getD_some]
                      exact p2_sext32_eq0 _ (by simpa [mkS, idx] using hval0)
                    exact hQ idx (mkS guL (m7LcgNextVal rngL).1) m' rfl hlen'
                      ⟨p2_probePres_refl s, hp', Or.inr ⟨hidx_lt, hfl0, hv0⟩⟩ hm'
                  · p2_steps_raw; exact hJnext () m' rfl
                · p2_steps_raw; exact hJnext () m' rfl
            · p2_steps_raw
              exact ret_neg1 hlenL hpL hmL
        · intro J3 hJ3
          p2_steps_raw
          p2_jnz_split hcv_lt
          · have hcv_nat : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
              p2_bv64_ofNat_toNat (by omega)
            have hcv_lt_nat : s.core.cur_vars < 4096 := by
              have h := hcv_lt
              simp only [BitVec.ult, hcv_nat] at h
              exact of_decide_eq_true (by simpa using h)
            p2_steps_raw
            have hmt_le : (BitVec.ofNat 64 s.core.cur_vars * 4#64 + 16#64).toNat ≤ 16400 := by
              bv_omega
            exact hJ3 (_, ()) m2 ⟨hmt_le, hm2⟩
          · p2_steps_raw
            exact hJ3 (16384#64, ()) m2 ⟨by decide, hm2⟩
      · intro J2 hJ2
        p2_steps_raw
        p2_jnz_split hrem0
        · p2_steps_raw
          p2_jnz_split hcl0
          · p2_steps_raw; exact ret_neg1 hlen1 hp1 hm1
          · p2_steps_raw
            p2_call hGet
            refine m7Get64Spec_of hlen1 hm1 ?_
            p2_steps_raw
            p2_jnz_split hclim
            · p2_steps_raw; exact ret_neg1 hlen1 hp1 hm1
            · p2_steps_raw
              p2_call hGet
              refine m7Get64Spec_of hlen1 hm1 ?_
              p2_steps_raw
              p2_call hSet
              refine m7Set64Spec_of hlen1 hm1 fun hlen2 m2 hm2 => ?_
              obtain ⟨hlen2', hm2'⟩ :=
                p2_m7Set64_step (n := 60) (by decide) (by decide) hlen2 hm2
              let gu2 := m7Set64List gu1 60 (m7Get64Val gu1 60 + 1#64)
              have hgu2 : gu2.length = 64 := by rw [m7Set64List_length]; exact hgu1
              have hp2 : M7GuPrefixPres s (mkS gu2 s.scratch.rng_state) :=
                M7GuPrefixPres.trans hp1 (M7GuPrefixPres.of_set64 _ (by decide))
              p2_steps_raw
              refine wp_join_group (ts := [i64])
                (fun _ mq => (FullMem c (mkS gu2 s.scratch.rng_state) ⋆ R) mq) ?_ ?_
              · rintro Jq ⟨qarg, ⟨⟩⟩ mq hmq
                rw [Blocks.get_here]
                p2_steps_raw
                p2_call hLog10
                refine m7Log10Q16Spec_of fun lg _ _ => ?_
                p2_steps_raw
                refine wp_join_group (ts := [i64])
                  (fun _ ml => (FullMem c (mkS gu2 s.scratch.rng_state) ⋆ R) ml) ?_ ?_
                · rintro Jl ⟨len, ⟨⟩⟩ ml hml
                  rw [Blocks.get_here]
                  p2_steps_raw
                  p2_call hSet
                  refine m7Set64Spec_of hlen2' hml fun hlen3 m3 hm3 => ?_
                  obtain ⟨hlen3', hm3'⟩ :=
                    p2_m7Set64_step (n := 56) (by decide) (by decide) hlen3 hm3
                  let gu3 := m7Set64List gu2 56 len
                  have hgu3 : gu3.length = 64 := by rw [m7Set64List_length]; exact hgu2
                  have hp3 : M7GuPrefixPres s (mkS gu3 s.scratch.rng_state) :=
                    M7GuPrefixPres.trans hp2 (M7GuPrefixPres.of_set64 _ (by decide))
                  p2_steps_raw
                  p2_call hSet
                  refine m7Set64Spec_of hlen3' hm3' fun hlen4 m4 hm4 => ?_
                  obtain ⟨hlen4', hm4'⟩ :=
                    p2_m7Set64_step (n := 58) (by decide) (by decide) hlen4 hm4
                  let gu4 :=
                    m7Set64List gu3 58 (s.scratch.conflicts + ((500#64 * lg) >>> 16#64))
                  have hgu4 : gu4.length = 64 := by rw [m7Set64List_length]; exact hgu3
                  have hp4 : M7GuPrefixPres s (mkS gu4 s.scratch.rng_state) :=
                    M7GuPrefixPres.trans hp3 (M7GuPrefixPres.of_set64 _ (by decide))
                  p2_steps_raw
                  exact hJ2 (len, ()) m4 ⟨gu4, hgu4, hp4, hm4'⟩
                · intro Jl hJl
                  p2_steps_raw
                  p2_jnz_split hlen10 <;> p2_steps_raw <;> exact hJl _ mq (by assumption)
              · intro Jq hJq
                p2_steps_raw
                p2_jnz_split hqarg <;> p2_steps_raw <;> exact hJq _ m2 hm2'
        · p2_steps_raw
          exact hJ2 (rem1, ()) m1 ⟨gu1, hgu1, hp1, hm1⟩
    · intro J1 hJ1
      p2_steps_raw
      p2_jnz_split hcfl
      · p2_steps_raw
        refine wp_join_group (ts := [i64])
          (fun _ mr => (FullMem c (mkS gu0 s.scratch.rng_state) ⋆ R) mr) ?_ ?_
        · rintro Jr ⟨rem', ⟨⟩⟩ mr hmr
          rw [Blocks.get_here]
          p2_steps_raw
          p2_call hSet
          refine m7Set64Spec_of hlen0' hmr fun hlen1a m1a hm1a => ?_
          obtain ⟨hlen1a', hm1a'⟩ :=
            p2_m7Set64_step (n := 56) (by decide) (by decide) hlen1a hm1a
          let gu1a := m7Set64List gu0 56 rem'
          have hgu1a : gu1a.length = 64 := by rw [m7Set64List_length]; exact hgu0
          have hp1a : M7GuPrefixPres s (mkS gu1a s.scratch.rng_state) :=
            M7GuPrefixPres.trans hp0' (M7GuPrefixPres.of_set64 _ (by decide))
          p2_steps_raw
          p2_call hSet
          refine m7Set64Spec_of hlen1a' hm1a' fun hlen1b m1b hm1b => ?_
          obtain ⟨hlen1b', hm1b'⟩ :=
            p2_m7Set64_step (n := 62) (by decide) (by decide) hlen1b hm1b
          let gu1b := m7Set64List gu1a 62 s.scratch.conflicts
          have hgu1b : gu1b.length = 64 := by rw [m7Set64List_length]; exact hgu1a
          have hp1b : M7GuPrefixPres s (mkS gu1b s.scratch.rng_state) :=
            M7GuPrefixPres.trans hp1a (M7GuPrefixPres.of_set64 _ (by decide))
          p2_steps_raw
          exact hJ1 (rem', ()) m1b ⟨gu1b, hgu1b, hp1b, hm1b'⟩
        · intro Jr hJr
          p2_steps_raw
          p2_jnz_split hremdc <;> p2_steps_raw <;> exact hJr _ m0 hm0'
      · p2_steps_raw
        exact hJ1 (m7Get64Val gu0 56, ()) m0 ⟨gu0, hgu0, hp0', hm0'⟩

/-- Canonical `Full.fullNextDecVarSpec` drop-in WP proof for `full_randec_var_m7`. -/
theorem full_randec_var_m7_dropin_wp (Γ : Env)
    (hLcg : EnvSpec Γ "full_lcg_next_m7" m7LcgNextSpec)
    (hInit : EnvSpec Γ "full_m7_state_init" m7StateInitSpec)
    (hGet : EnvSpec Γ "full_m7_get64" m7Get64Spec)
    (hSet : EnvSpec Γ "full_m7_set64" m7Set64Spec)
    (hLog10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec) :
    ∀ a m Q X, Full.fullNextDecVarSpec a m Q X →
      Func.wp Γ full_randec_var_m7_body a m Q X :=
  fun _ _ _ _ hs =>
    full_randec_var_m7_wp Γ hLcg hInit hGet hSet hLog10 _ _ _ _ (m7RandecVarSpec_to_canon hs)

/-! ## 5. `full_decide_m7` `Func.wp` Proof -/

/-- Parametric WP proof for `full_decide_m7` against `m7DecideSpec`. -/
theorem full_decide_m7_wp (Γ : Env)
    (hRandec : EnvSpec Γ "full_randec_var_m7" m7RandecVarSpec)
    (hNextDec : EnvSpec Γ "full_next_dec_var" fullNextDecVarSpec)
    (hAssign : EnvSpec Γ "full_assign" fullAssignSpec) :
    ∀ a m Q X, m7DecideSpec a m Q X → Func.wp Γ full_decide_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hspec
  obtain ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩ := m7DecideSpec_elim hspec
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  unfold Func.wp full_decide_m7_body
  p2_steps_raw
  p2_call hRandec
  refine m7RandecVarSpec_of hinv.lengths hm
    fun chosen s1 m1 hc1 hlen1 hp1 _ hch1 hm1 => ?_
  have hinv1 : FullCoreInv c F0 s1 := hinv.with_fuel_scratch_spec hlen1 hc1
  p2_steps_raw
  refine wp_join_group (ts := [i64])
    (fun (ch, ()) m2 => ∃ s2 : FullState,
      s2.core = s.core ∧ s2.LengthsOk c ∧ FullExtScratchPres s s2 ∧
      (ch = 0xFFFFFFFFFFFFFFFF#64 ∨
        ch.toNat < s.core.cur_vars ∧ s.core.vals[2 * ch.toNat]?.getD 0#8 = 0#8) ∧
      (FullMem c s2 ⋆ R) m2) ?_ ?_
  · rintro Jc ⟨ch, ⟨⟩⟩ m2 ⟨s2, hc2, hlen2, hext2, hch2, hm2⟩
    rw [Blocks.get_here]
    have hinv2 : FullCoreInv c F0 s2 := hinv.with_fuel_scratch_spec hlen2 hc2
    have hcl2 := hinv2.lengths.core_ok
    have hsok2 := hinv2.lengths.scratch_ok
    p2_steps_raw
    p2_jnz_split h_neg1
    · p2_steps_raw
      cases s2; dsimp only at hc2; subst hc2
      exact hQ 0#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
        s.core.frame_trail s.core.frame_dec s.core.trail_end s.core.cur_level s.core.unassigned
        s.core.unflushed _ m2 hinv2 hext2 (Or.inl rfl) (fun _ => ⟨rfl, rfl⟩)
        (fun h01 => by cases h01) hm2
    · obtain ⟨hv_lt, hval0⟩ := hch2.resolve_left (by simpa using h_neg1)
      have hcv2 : s.core.cur_vars ≤ c.max_vars := hc2 ▸ hcl2.cur_vars_le
      have hch_lt_max : ch.toNat < c.max_vars := by omega
      have hch_lt30 : ch.toNat < 2 ^ 30 := by omega
      have hv_tgt : ch.toNat < s2.scratch.phases_target.length := by
        rw [hsok2.phases_target_len]; omega
      have hv_ph : ch.toNat < s2.scratch.phases.length := by
        rw [hsok2.phases_len]; omega
      p2_steps_raw
      refine wp_join_group (fun _ md1 => m2 = md1) ?_ ?_
      · rintro Jd1 ⟨dph1, ⟨⟩⟩ _ rfl
        rw [Blocks.get_here]
        p2_steps_raw
        refine wp_join_group (fun _ md2 => m2 = md2) ?_ ?_
        · rintro Jd2 ⟨dph2, ⟨⟩⟩ _ rfl
          rw [Blocks.get_here]
          p2_steps_raw
          refine wp_join_group (fun _ md3 => m2 = md3) ?_ ?_
          · rintro Jd3 ⟨dph3, ⟨⟩⟩ _ rfl
            rw [Blocks.get_here]
            p2_steps_raw
            refine wp_join_group (ts := [i32])
              (fun (lit, ()) ml => m2 = ml ∧
                (lit.toNat = 2 * ch.toNat ∨ lit.toNat = 2 * ch.toNat + 1)) ?_ ?_
            · rintro Jl ⟨lit, ⟨⟩⟩ _ ⟨rfl, hlit_eq⟩
              rw [Blocks.get_here]
              cases s2 with | mk sc_c sc_sc =>
              dsimp only at hc2; subst hc2
              have hinv2' : FullCoreInv c F0 { core := s.core, scratch := sc_sc } := hinv2
              have hcl2' := hinv2'.lengths.core_ok
              have hsok2' := hinv2'.lengths.scratch_ok
              have hte2 : s.core.trail_end ≤ s.core.cur_vars := hcl2'.trail_end_le
              have hcv2' : s.core.cur_vars ≤ c.max_vars := hcl2'.cur_vars_le
              obtain ⟨_, hw2⟩ := hinv2'.witness
              have hcl2_le : s.core.cur_level ≤ s.core.trail_end := hw2.cur_level_le
              have hnlvl_bv : (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat =
                  s.core.cur_level + 1 := by
                have := p2_bv64_ofNat_toNat (n := s.core.cur_level) (by omega)
                bv_omega
              have hnlvl_nat := hnlvl_bv
              have hftrl1 : s.core.frame_trail.length = c.max_vars + 1 := hcl2'.frame_trail_len
              have hfdec1 : s.core.frame_dec.length = c.max_vars + 1 := hcl2'.frame_dec_len
              p2_steps_raw
              p2_jnz_split hnlvl_gt
              · p2_steps_raw
                exact hQ 0#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl
                  s.core.trail_pos s.core.frame_trail s.core.frame_dec s.core.trail_end
                  s.core.cur_level s.core.unassigned s.core.unflushed _ m2 hinv2' hext2
                  (Or.inl rfl) (fun _ => ⟨rfl, rfl⟩) (fun h01 => by cases h01) hm2
              · have hnlvl_le : s.core.cur_level + 1 ≤ c.max_vars := by
                  have h := hnlvl_gt
                  have h1 : (1 : BitVec 64) = 1#64 := rfl
                  have hm1 : (BitVec.ofNat 64 c.max_vars).toNat = c.max_vars :=
                    p2_bv64_ofNat_toNat (by omega)
                  simp only [BitVec.ult, h1, hnlvl_bv, hm1] at h
                  exact Nat.le_of_not_lt (of_decide_eq_false h)
                have hft_lt : (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat <
                    s.core.frame_trail.length := by
                  rw [hnlvl_bv, hftrl1]; omega
                have hfd_lt : (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat <
                    s.core.frame_dec.length := by
                  rw [hnlvl_bv, hfdec1]; omega
                have ⟨_, hun, hte_lt, _⟩ := m7_decide_preserves_fullCore hinv2' hsok2'
                  hcl2'.flags_len hv_lt hval0 hlit_eq (flags' := s.core.flags)
                  (unas' := s.core.unassigned) (unfl' := s.core.unflushed)
                let nlvl := s.core.cur_level + 1
                let ftrl' := s.core.frame_trail.set nlvl (BitVec.ofNat 32 s.core.trail_end)
                let fdec' := s.core.frame_dec.set nlvl lit
                let s_pre : FullState :=
                  { core := { s.core with frame_trail := ftrl', frame_dec := fdec',
                                          cur_level := nlvl }
                    scratch := sc_sc }
                have hlen_pre : s_pre.LengthsOk c :=
                  ⟨{ hcl2' with
                      frame_trail_len := by
                        dsimp only [s_pre, ftrl']; rw [List.length_set]; exact hftrl1
                      frame_dec_len := by
                        dsimp only [s_pre, fdec']; rw [List.length_set]; exact hfdec1 },
                    hsok2'⟩
                have hte_bv : (BitVec.ofNat 64 s.core.trail_end).setWidth 32 =
                    BitVec.ofNat 32 s.core.trail_end := by
                  apply BitVec.eq_of_toNat_eq
                  rw [BitVec.toNat_setWidth, p2_bv64_ofNat_toNat (by omega),
                    M7SearchTactics.bv32_ofNat_toNat (by omega), Nat.mod_eq_of_lt (by omega)]
                p2_steps_raw
                have hte_lt' : s.core.trail_end < s.core.cur_vars := hte_lt
                have hte_max : s.core.trail_end < c.max_vars := Nat.lt_of_lt_of_le hte_lt' hcv2'
                have hlit_v : lit.toNat / 2 = ch.toNat := by omega
                have hng : ¬ (s_pre.core.cur_vars ≤ lit.toNat / 2 ∨
                    c.max_vars ≤ s_pre.core.trail_end ∨
                    s_pre.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
                  change ¬ (s.core.cur_vars ≤ lit.toNat / 2 ∨
                    c.max_vars ≤ s.core.trail_end ∨
                    s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8)
                  simp only [hun, ne_eq, not_true_eq_false, or_false]; rw [hlit_v]; omega
                p2_call hAssign
                refine ⟨c, s_pre, R, rfl, hlen_pre, by dsimp [s_pre, nlvl]; omega, ?_, ?_⟩
                · dsimp only [s_pre, ftrl', fdec', nlvl]
                  have h1 : (BitVec.ofNat 64 s.core.cur_level + (1 : BitVec 64)).toNat =
                      s.core.cur_level + 1 := hnlvl_bv
                  rw [← h1, ← hte_bv]
                  assumption
                · simp only [hng, ↓reduceIte]
                  intro flags' unas' phases' m3 hfl_l hph_l hm3
                  have hsok3 : ({ sc_sc with phases := phases' } : FullScratch).LengthsOk c :=
                    { hsok2' with phases_len := hph_l }
                  have ⟨hinv3, _, _, _⟩ := m7_decide_preserves_fullCore hinv2' hsok3 hfl_l
                    hv_lt hval0 hlit_eq (flags' := flags')
                    (unas' := unas') (unfl' := s.core.unflushed)
                  have hnl_ne0 : nlvl ≠ 0 := by dsimp [nlvl]; omega
                  have hff : (4294967295 : BitVec 32) = 0xFFFFFFFF#32 := rfl
                  have htrl_lt : s.core.trail_end <
                      (s.core.trl.set s.core.trail_end lit).length := by
                    rw [List.length_set, hcl2'.trl_len]; omega
                  have htrl_val : s.core.vals[((s.core.trl.set s.core.trail_end
                      lit)[s.core.trail_end]?.getD 0#32).toNat]?.getD 0#8 = 0#8 := by
                    rw [List.getElem?_set_self (by rw [hcl2'.trl_len]; omega), Option.getD_some]
                    exact hun
                  have hm3' : (FullMem c
                      { core := { s.core with
                          vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                          flags := flags'
                          lvl := s.core.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 nlvl)
                          rsns := s.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32
                          trl := s.core.trl.set s.core.trail_end lit
                          trail_pos := s.core.trail_pos.set (lit.toNat / 2)
                            (BitVec.ofNat 32 s.core.trail_end)
                          frame_trail := ftrl', frame_dec := fdec'
                          trail_end := s.core.trail_end + 1, cur_level := nlvl
                          unassigned := unas', unflushed := s.core.unflushed }
                        scratch := { sc_sc with phases := phases' } } ⋆ R) m3 := by
                    simpa only [s_pre, hnl_ne0, ↓reduceIte, hff] using hm3
                  p2_steps_raw
                  exact hQ 1#64 _ flags' _ _ _ _ ftrl' fdec' (s.core.trail_end + 1) nlvl unas'
                    s.core.unflushed { sc_sc with phases := phases' } m3 hinv3 hext2 (Or.inr rfl)
                    (fun h10 => by cases h10)
                    (fun _ => ⟨rfl, rfl, htrl_lt, htrl_val⟩) hm3'
            · intro Jl hJl
              p2_steps
              · exact hJl _ m2 ⟨rfl, Or.inr (M7SearchTactics.bv32_lit_odd hch_lt30)⟩
              · exact hJl _ m2 ⟨rfl, Or.inl (M7SearchTactics.bv32_lit_even hch_lt30)⟩
          · intro Jd3 hJd3
            p2_steps <;> exact hJd3 _ m2 rfl
        · intro Jd2 hJd2
          p2_steps <;> exact hJd2 _ m2 rfl
      · intro Jd1 hJd1
        p2_steps <;> exact hJd1 _ m2 rfl
  · intro Jc hJc
    p2_steps_raw
    p2_jnz_split hc_neg1
    · p2_steps_raw
      p2_call hNextDec
      refine show Full.fullNextDecVarSpec _ _ _ _ from ⟨c, s1, R, rfl, hlen1, hm1,
        fun ⟨chosen', ⟨⟩⟩ s2 m2 hc2 hlen2 ⟨hext2, hch2⟩ hm2 => ?_⟩
      have hc2' : s2.core = s.core := Eq.trans hc2 hc1
      have hext2' : FullExtScratchPres s s2 :=
        ⟨hext2.1.trans hp1.1.1, hext2.2.trans hp1.1.2⟩
      have hch2' : chosen' = 0xFFFFFFFFFFFFFFFF#64 ∨
          chosen'.toNat < s.core.cur_vars ∧ s.core.vals[2 * chosen'.toNat]?.getD 0#8 = 0#8 := by
        simpa [hc1] using hch2
      p2_steps_raw
      exact hJc (chosen', ()) m2 ⟨s2, hc2', hlen2, hext2', hch2', hm2⟩
    · p2_steps_raw
      obtain ⟨hv_lt, _, hv0⟩ := hch1.resolve_left (by simpa using hc_neg1)
      exact hJc (chosen, ()) m1 ⟨s1, hc1, hlen1, hp1.1, Or.inr ⟨hv_lt, hv0⟩, hm1⟩

/-- Canonical `Full.fullDecideSpec` drop-in WP proof for `full_decide_m7`. -/
theorem full_decide_m7_dropin_wp (Γ : Env)
    (hRandec : EnvSpec Γ "full_randec_var_m7" m7RandecVarSpec)
    (hNextDec : EnvSpec Γ "full_next_dec_var" fullNextDecVarSpec)
    (hAssign : EnvSpec Γ "full_assign" fullAssignSpec) :
    ∀ a m Q X, Full.fullDecideSpec a m Q X → Func.wp Γ full_decide_m7_body a m Q X :=
  fun _ _ _ _ hs =>
    full_decide_m7_wp Γ hRandec hNextDec hAssign _ _ _ _ (m7DecideSpec_to_canon hs)

/-! ## 6. `full_lucky_late_m7` `Func.wp` Proof -/

private theorem p2_fullSparseInv_of_m7Decide {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s) {v : Nat} {lit : BitVec 32}
    {flags' : List (BitVec 32)} {unas' unfl' : BitVec 64} {phases' : List (BitVec 8)}
    (hfl_len : flags'.length = c.max_vars) (hph_len : phases'.length = c.max_vars)
    (hv_lt : v < s.core.cur_vars) (hval0 : s.core.vals[2 * v]?.getD 0#8 = 0#8)
    (hlit_eq : lit.toNat = 2 * v ∨ lit.toNat = 2 * v + 1) :
    let nlvl := s.core.cur_level + 1
    let ftrl' := s.core.frame_trail.set nlvl (BitVec.ofNat 32 s.core.trail_end)
    let fdec' := s.core.frame_dec.set nlvl lit
    let s' : FullState :=
      { core :=
          { s.core with
            vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := s.core.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 nlvl)
            rsns := s.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32
            trl := s.core.trl.set s.core.trail_end lit
            trail_pos := s.core.trail_pos.set (lit.toNat / 2) (BitVec.ofNat 32 s.core.trail_end)
            frame_trail := ftrl', frame_dec := fdec'
            trail_end := s.core.trail_end + 1, cur_level := nlvl
            unassigned := unas', unflushed := unfl' }
        scratch := { s.scratch with phases := phases' } }
    FullSparseInv c F0 s' ∧ s.core.vals[lit.toNat]?.getD 0#8 = 0#8 ∧
    s.core.trail_end < s.core.cur_vars ∧ nlvl ≤ c.max_vars := by
  intro nlvl ftrl' fdec' s'
  have hsok' : ({ s.scratch with phases := phases' } : FullScratch).LengthsOk c :=
    { hsp.1.lengths.scratch_ok with phases_len := hph_len }
  obtain ⟨hc', hv, hte, hnl⟩ := m7_decide_preserves_fullCore hsp.1 hsok' hfl_len hv_lt hval0
    hlit_eq (flags' := flags') (unas' := unas') (unfl' := unfl')
  refine ⟨⟨hc', hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2⟩, hv, hte, hnl⟩

private theorem p2_lucky_bt0_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {rs : List Ty} {Q : Post rs} {X : XPost}
    {k_bt : Tup Val [] → Expr Val Cont rs}
    (hBt : EnvSpec Γ "full_backtrack" fullBacktrackSpec)
    (hsp : FullSparseInv c F0 s) (hm : (FullMem c s ⋆ R) m)
    (hK : ∀ s' m', s'.LengthsOk c → s'.core.fuel = s.core.fuel →
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k_bt ()) m') :
    wp Γ Q X (@Expr.call Val Cont rs "full_backtrack" [i64, i64] []
      (Arg.var c.hdr, Arg.imm (0 : BitVec 64), PUnit.unit) k_bt) m := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hsp.1.lengths.core_ok.cur_vars_le
  have hte_le := hsp.1.lengths.core_ok.trail_end_le
  obtain ⟨F_cur, hw⟩ := hsp.1.witness
  have hcl_lt : s.core.cur_level < 2 ^ 64 := by have := hw.cur_level_le; omega
  p2_call hBt
  refine ⟨c, s, R, rfl, hsp.1.lengths, hcl_lt,
    fun _ => by
      have h0 : (0 : BitVec 64).toNat = 0 := rfl
      rw [h0]; have := hw.cur_level_le; omega,
    hw.trail_lits_lt, hm, ?_⟩
  dsimp only
  intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
    hlen' _ _ hcl' hps _ _ _ hwt _ hm'
  let s_bt : FullState :=
    { core := { s.core with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', cur_level := cl', unassigned := unass' }
      scratch := sc' }
  have hsp_bt : FullSparseInv c F0 s_bt :=
    fullSparseInv_of_fullBacktrack hsp hlen'
      (hwt F0 F_cur hw (Nat.zero_le _)) rfl rfl rfl rfl rfl hps.1.1 hps.1.2
  have hcl0_bt : s_bt.core.cur_level = 0 := by change cl' = 0; rw [hcl']; simp
  exact hK s_bt m' hlen' rfl hsp_bt hcl0_bt hm'

/-- Parametric WP proof for `full_lucky_late_m7` against `m7LuckyLateSpec`. -/
theorem full_lucky_late_m7_wp (Γ : Env)
    (hPolar : EnvSpec Γ "full_lucky_polar_m7" fullLuckyPolarSpec)
    (hScan : EnvSpec Γ "full_lucky_scan" fullLuckyScanSpec)
    (hAssign : EnvSpec Γ "full_assign" fullAssignSpec)
    (hBt : EnvSpec Γ "full_backtrack" fullBacktrackSpec)
    (hProp : EnvSpec Γ "full_propagate" fullPropagateSpec) :
    ∀ a m Q X, m7LuckyLateSpec a m Q X → Func.wp Γ full_lucky_late_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hspec
  obtain ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩ := m7LuckyLateSpec_elim hspec
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  unfold Func.wp full_lucky_late_m7_body
  p2_steps_raw
  p2_jnz_split hinc
  · have hinc_ne : s.core.inconsistent ≠ 0#64 := by simpa using hinc
    have hunsat : F0.Unsat := hsp.inconsistent_unsat hinc_ne
    p2_steps_raw
    let s' : FullState := { s with core := { s.core with probing := 0#64 } }
    have hsp' : FullSparseInv c F0 s' := fullSparseInv_with_probing hsp 0#64
    exact hQ 20#64 s' m hsp'.1.lengths (Or.inr (Or.inr (Or.inr rfl))) (Nat.le_refl _) rfl
      (fun _ => hunsat) (fun h => by rcases h with h | h <;> cases h)
      (fun h => by cases h) (by assumption)
  · p2_steps_raw
    refine wp_join_group (ts := [])
      (fun _ m1 => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
        s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
    · rintro J1 ⟨⟩ m1 ⟨s1, hsp1, hcl1_0, hfl1, hm1⟩
      rw [Blocks.get_here]
      p2_steps_raw
      refine wp_join_group (ts := [])
        (fun _ m2 => ∃ s2 : FullState, FullSparseInv c F0 s2 ∧ s2.core.cur_level = 0 ∧
          s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s2 ⋆ R) m2) ?_ ?_
      · rintro J2 ⟨⟩ m2 ⟨s2, hsp2, hcl2_0, hfl2, hm2⟩
        rw [Blocks.get_here]
        p2_steps_raw
        let s3 : FullState := { s2 with core := { s2.core with probing := 1#64 } }
        have hsp3 : FullSparseInv c F0 s3 := fullSparseInv_with_probing hsp2 1#64
        have hcl3_0 : s3.core.cur_level = 0 := hcl2_0
        p2_call hPolar
        refine ⟨c, F0, s3, R, rfl, hsp3.1, by assumption, ?_⟩
        intro pol hpol
        p2_steps_raw
        p2_jnz_split hpol0
        · p2_steps_raw
          refine wp_loop_inv (ts := [i64])
            (fun (idx, ()) ml => ∃ st : FullState,
              idx.toNat ≤ s3.core.cur_vars ∧ st.core.cur_vars = s3.core.cur_vars ∧
              FullSparseInv c F0 st ∧ st.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullMem c st ⋆ R) ml)
            (fun (idx, ()) _ => s3.core.cur_vars - idx.toNat) ?_ ?_
          · intro Jloop hJloop
            p2_steps_raw
            exact hJloop (0#64, ()) _ ⟨s3, Nat.zero_le _, rfl, hsp3, hfl2, by assumption⟩
          · rintro Jloop ⟨idx, ⟨⟩⟩ ml ⟨st, hidx_le, hcv_eq, hst, hfl, hml⟩ hJloop
            rw [Blocks.get_here]
            have hcv_le := hst.1.lengths.core_ok.cur_vars_le
            have hcl_ok := hst.1.lengths.core_ok
            p2_steps_raw
            p2_jnz_split hidx_lt_cv
            · have hidx_lt : idx.toNat < st.core.cur_vars := by
                have hlt : idx.toNat < st.core.cur_vars % 2 ^ 64 := by
                  simpa [BitVec.ult] using hidx_lt_cv
                rw [Nat.mod_eq_of_lt (by omega)] at hlt; exact hlt
              have hidx1_nat : (idx + 1#64).toNat = idx.toNat + 1 :=
                p2_bv64_add1_toNat (by omega)
              have hidx_fl : idx.toNat < st.core.flags.length := by rw [hcl_ok.flags_len]; omega
              have h2v : (idx <<< 1#64).toNat = 2 * idx.toNat :=
                M7SearchTactics.bv64_shl1_toNat (by omega)
              have hidx2_vl : (idx <<< 1#64).toNat < st.core.vals.length := by
                rw [h2v, hcl_ok.vals_len]; omega
              p2_steps_raw
              refine wp_join_group (ts := []) (fun _ mn =>
                ∃ st' : FullState, st'.core.cur_vars = s3.core.cur_vars ∧
                  FullSparseInv c F0 st' ∧ st'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  (FullMem c st' ⋆ R) mn) ?_ ?_
              · rintro Jnext ⟨⟩ mn ⟨st', hcv', hst', hfl', hmn⟩
                rw [Blocks.get_here]
                p2_steps_raw
                exact hJloop (idx + 1#64, ()) mn (by dsimp only; rw [hidx1_nat]; omega)
                  ⟨st', by rw [hidx1_nat]; omega, hcv', hst', hfl', hmn⟩
              · intro Jnext hJnext
                p2_steps_raw
                p2_jnz_split hact
                · p2_steps_raw
                  p2_jnz_split hval0_b
                  · have hval0 : st.core.vals[2 * idx.toNat]?.getD 0#8 = 0#8 := by
                      rw [← h2v, List.getElem?_eq_getElem hidx2_vl, Option.getD_some]
                      exact p2_sext32_eq0 _ (by simpa using hval0_b)
                    p2_steps_raw
                    p2_jnz_split hfuel0
                    · p2_steps_raw
                      refine p2_lucky_bt0_wp hBt hst hml
                        fun s_bt mb _ hfl_b hsp_b hcl0_b hmb => ?_
                      p2_steps_raw
                      let s' : FullState := { s_bt with core := { s_bt.core with probing := 0#64 } }
                      have hsp' : FullSparseInv c F0 s' := fullSparseInv_with_probing hsp_b 0#64
                      have hfl' : s'.core.fuel.toNat ≤ s.core.fuel.toNat := by
                        change s_bt.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hfl_b]; exact hfl
                      exact hQ 2#64 s' _ hsp'.1.lengths (Or.inr (Or.inl rfl)) hfl' rfl
                        (fun h => by cases h) (fun _ => ⟨hsp', hcl0_b⟩)
                        (fun h => by cases h) (by assumption)
                    · have hfl_ne : st.core.fuel ≠ 0#64 := by simpa using hfuel0
                      have hfl_sub : (st.core.fuel - 1#64).toNat = st.core.fuel.toNat - 1 :=
                        p2_bv64_sub1_toNat hfl_ne
                      let st1 : FullState :=
                        { st with core := { st.core with fuel := st.core.fuel - 1#64 } }
                      have hst1 : FullSparseInv c F0 st1 :=
                        fullSparseInv_with_fuel hst (st.core.fuel - 1#64)
                      have hfl1 : st1.core.fuel.toNat ≤ s.core.fuel.toNat := by
                        change (st.core.fuel - 1#64).toNat ≤ s.core.fuel.toNat
                        rw [hfl_sub]; omega
                      p2_steps_raw
                      refine wp_join_group (ts := [i32]) (fun (lit, _) mlit =>
                        (FullMem c st1 ⋆ R) mlit ∧
                          (lit.toNat = 2 * idx.toNat ∨ lit.toNat = 2 * idx.toNat + 1)) ?_ ?_
                      · rintro Jlit ⟨lit, ⟨⟩⟩ mlit ⟨hmlit, hlit_eq⟩
                        rw [Blocks.get_here]
                        obtain ⟨_, hw_1⟩ := hst1.1.witness
                        have hcv1_le := hst1.1.lengths.core_ok.cur_vars_le
                        have hcl1_le : st1.core.cur_level ≤ st1.core.trail_end := hw_1.cur_level_le
                        have hte1_le : st1.core.trail_end ≤ st1.core.cur_vars :=
                          hst1.1.lengths.core_ok.trail_end_le
                        have hnlvl_bv : (BitVec.ofNat 64 st1.core.cur_level + 1#64).toNat =
                            st1.core.cur_level + 1 := by
                          have := p2_bv64_ofNat_toNat (n := st1.core.cur_level) (by omega)
                          bv_omega
                        p2_steps_raw
                        p2_jnz_split hnlvl_gt
                        · p2_steps_raw
                          refine p2_lucky_bt0_wp hBt hst1 hmlit
                            fun s_bt mb _ hfl_b hsp_b hcl0_b hmb => ?_
                          p2_steps_raw
                          let s' : FullState :=
                            { s_bt with core := { s_bt.core with probing := 0#64 } }
                          have hsp' : FullSparseInv c F0 s' :=
                            fullSparseInv_with_probing hsp_b 0#64
                          have hfl' : s'.core.fuel.toNat ≤ s.core.fuel.toNat := by
                            change s_bt.core.fuel.toNat ≤ s.core.fuel.toNat
                            rw [hfl_b]; exact hfl1
                          exact hQ 0#64 s' _ hsp'.1.lengths (Or.inl rfl) hfl' rfl
                            (fun h => by cases h) (fun _ => ⟨hsp', hcl0_b⟩)
                            (fun h => by cases h) (by assumption)
                        · have hdec1 := p2_fullSparseInv_of_m7Decide hst1
                            hst1.1.lengths.core_ok.flags_len
                            hst1.1.lengths.scratch_ok.phases_len hidx_lt hval0 hlit_eq
                            (flags' := st1.core.flags) (unas' := st1.core.unassigned)
                            (unfl' := st1.core.unflushed) (phases' := st1.scratch.phases)
                          have hun := hdec1.2.1
                          have hte_lt := hdec1.2.2.1
                          have hnlvl_le := hdec1.2.2.2
                          let nlvl := st1.core.cur_level + 1
                          let ftrl' := st1.core.frame_trail.set nlvl
                            (BitVec.ofNat 32 st1.core.trail_end)
                          let fdec' := st1.core.frame_dec.set nlvl lit
                          let s_dec : FullState :=
                            { st1 with core := { st1.core with
                                cur_level := nlvl, frame_trail := ftrl', frame_dec := fdec' } }
                          have hftrl1 := hst1.1.lengths.core_ok.frame_trail_len
                          have hfdec1 := hst1.1.lengths.core_ok.frame_dec_len
                          have hdec_len : s_dec.LengthsOk c :=
                            ⟨{ hst1.1.lengths.core_ok with
                                frame_trail_len := by
                                  dsimp only [s_dec, ftrl']; rw [List.length_set]; exact hftrl1
                                frame_dec_len := by
                                  dsimp only [s_dec, fdec']; rw [List.length_set]; exact hfdec1 },
                              hst1.1.lengths.scratch_ok⟩
                          have hte_bv : (BitVec.ofNat 64 st1.core.trail_end).setWidth 32 =
                              BitVec.ofNat 32 st1.core.trail_end := by
                            apply BitVec.eq_of_toNat_eq
                            rw [BitVec.toNat_setWidth, p2_bv64_ofNat_toNat (by omega),
                              M7SearchTactics.bv32_ofNat_toNat (by omega),
                              Nat.mod_eq_of_lt (by omega)]
                          have hnlvl_lt_len :
                              (BitVec.ofNat 64 st1.core.cur_level + 1#64).toNat <
                                st1.core.frame_trail.length := by
                            rw [hnlvl_bv, hftrl1]; omega
                          have hnlvl_lt_dlen :
                              (BitVec.ofNat 64 st1.core.cur_level + 1#64).toNat <
                                st1.core.frame_dec.length := by
                            rw [hnlvl_bv, hfdec1]; omega
                          p2_steps_raw
                          have hidx_lt1 : idx.toNat < st1.core.cur_vars := hidx_lt
                          have hte_lt' : st1.core.trail_end < st1.core.cur_vars := hte_lt
                          have hte_max : st1.core.trail_end < c.max_vars :=
                            Nat.lt_of_lt_of_le hte_lt' hcv1_le
                          have hlit_v : lit.toNat / 2 = idx.toNat := by omega
                          have hng : ¬ (s_dec.core.cur_vars ≤ lit.toNat / 2 ∨
                              c.max_vars ≤ s_dec.core.trail_end ∨
                              s_dec.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
                            change ¬ (st1.core.cur_vars ≤ lit.toNat / 2 ∨
                              c.max_vars ≤ st1.core.trail_end ∨
                              st1.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8)
                            simp only [hun, ne_eq, not_true_eq_false, or_false]
                            rw [hlit_v]; omega
                          p2_call hAssign
                          refine ⟨c, s_dec, R, rfl, hdec_len, by dsimp [s_dec, nlvl]; omega,
                            ?_, ?_⟩
                          · dsimp only [s_dec, ftrl', fdec', nlvl]
                            have h1 :
                                (BitVec.ofNat 64 st1.core.cur_level + (1 : BitVec 64)).toNat =
                                  st1.core.cur_level + 1 := hnlvl_bv
                            rw [← h1, ← hte_bv]
                            assumption
                          · simp only [hng, ↓reduceIte]
                            intro flags' unas' phases' ma hfl_len hph_len hma
                            have hsp_asn0 := (p2_fullSparseInv_of_m7Decide hst1 hfl_len hph_len
                              hidx_lt hval0 hlit_eq (flags' := flags') (unas' := unas')
                              (unfl' := st1.core.unflushed) (phases' := phases')).1
                            let s_asn : FullState :=
                              { core := { s_dec.core with
                                  vals := (st1.core.vals.set lit.toNat 1#8).set
                                    (lit.toNat ^^^ 1) 0xFF#8
                                  flags := flags'
                                  lvl := st1.core.lvl.set (lit.toNat / 2)
                                    (BitVec.ofNat 32 nlvl)
                                  rsns := st1.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32
                                  trl := st1.core.trl.set st1.core.trail_end lit
                                  trail_pos := st1.core.trail_pos.set (lit.toNat / 2)
                                    (BitVec.ofNat 32 st1.core.trail_end)
                                  trail_end := st1.core.trail_end + 1
                                  unassigned := unas', unflushed := st1.core.unflushed }
                                scratch := { st1.scratch with phases := phases' } }
                            have hsp_asn : FullSparseInv c F0 s_asn := by
                              have hnl_ne0 : nlvl ≠ 0 := by dsimp [nlvl]; omega
                              simpa only [s_asn, s_dec, ftrl', fdec'] using hsp_asn0
                            have hma' : (FullMem c s_asn ⋆ R) ma := by
                              have hnl_ne0 : nlvl ≠ 0 := by dsimp [nlvl]; omega
                              have hff : (4294967295 : BitVec 32) = 0xFFFFFFFF#32 := rfl
                              simpa only [s_asn, s_dec, hnl_ne0, ↓reduceIte, hff] using hma
                            obtain ⟨F_cur_a, hw_a⟩ := hsp_asn.1.witness
                            p2_steps_raw
                            p2_call hProp
                            refine ⟨c, F0, F_cur_a, s_asn, R, rfl, hsp_asn.1.lengths, hw_a,
                              hsp_asn.2.2.2.2, hma', ?_⟩
                            dsimp only
                            intro pr vals'' flags'' lvl'' rsns'' trl'' tp'' te'' prop''
                              unass'' unfl'' wvec'' arena'' wstk'' wlen'' wu'' fuel'' ctype''
                              cref'' c0'' c1'' oom'' ticks'' wsort'' phases'' mp
                              hlen_p hw_p htr_p hperm_p hfl_p hr_or _ _ _ _ hmp
                            let s_p : FullState :=
                              { core := { s_asn.core with
                                  vals := vals'', flags := flags'', lvl := lvl'', rsns := rsns'',
                                  trl := trl'', trail_pos := tp'', trail_end := te'',
                                  propagated := prop'', unassigned := unass'', unflushed := unfl'',
                                  wvec := wvec'', arena := arena'', wstk := wstk'', wlen := wlen'',
                                  wusable := wu'', fuel := fuel'', confl_type := ctype'',
                                  confl_ref := cref'', confl_lit0 := c0'', confl_lit1 := c1'',
                                  oom := oom'' }
                                scratch := { s_asn.scratch with
                                  search_ticks := ticks'', wsort := wsort'', phases := phases'' } }
                            have hsp_p : FullSparseInv c F0 s_p :=
                              fullSparseInv_of_fullPropagate hsp_asn hlen_p hw_p hperm_p
                                rfl rfl rfl rfl rfl
                            have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat :=
                              Nat.le_trans hfl_p hfl1
                            have hcv_p : s_p.core.cur_vars = s3.core.cur_vars := by
                              change st.core.cur_vars = s3.core.cur_vars; exact hcv_eq
                            p2_steps_raw
                            p2_jnz_split hpr2
                            · p2_steps_raw
                              refine p2_lucky_bt0_wp hBt hsp_p hmp
                                fun s_bt mb _ hfl_b hsp_b hcl0_b hmb => ?_
                              p2_steps_raw
                              let s' : FullState :=
                                { s_bt with core := { s_bt.core with probing := 0#64 } }
                              have hsp' : FullSparseInv c F0 s' :=
                                fullSparseInv_with_probing hsp_b 0#64
                              have hfl' : s'.core.fuel.toNat ≤ s.core.fuel.toNat := by
                                change s_bt.core.fuel.toNat ≤ s.core.fuel.toNat
                                rw [hfl_b]; exact hfl_p'
                              exact hQ 2#64 s' _ hsp'.1.lengths (Or.inr (Or.inl rfl)) hfl' rfl
                                (fun h => by cases h) (fun _ => ⟨hsp', hcl0_b⟩)
                                (fun h => by cases h) (by assumption)
                            · p2_steps_raw
                              p2_jnz_split hpr1
                              · p2_steps_raw
                                refine p2_lucky_bt0_wp hBt hsp_p hmp
                                  fun s_bt mb _ hfl_b hsp_b hcl0_b hmb => ?_
                                p2_steps_raw
                                let s' : FullState :=
                                  { s_bt with core := { s_bt.core with probing := 0#64 } }
                                have hsp' : FullSparseInv c F0 s' :=
                                  fullSparseInv_with_probing hsp_b 0#64
                                have hfl' : s'.core.fuel.toNat ≤ s.core.fuel.toNat := by
                                  change s_bt.core.fuel.toNat ≤ s.core.fuel.toNat
                                  rw [hfl_b]; exact hfl_p'
                                exact hQ 0#64 s' _ hsp'.1.lengths (Or.inl rfl) hfl' rfl
                                  (fun h => by cases h) (fun _ => ⟨hsp', hcl0_b⟩)
                                  (fun h => by cases h) (by assumption)
                              · p2_steps_raw
                                exact hJnext () mp ⟨s_p, hcv_p, hsp_p, hfl_p', hmp⟩
                      · intro Jlit hJlit
                        p2_steps_raw
                        p2_jnz_split hsp_cond
                        · p2_steps_raw
                          have hlt30 : idx.toNat < 2 ^ 30 := by omega
                          exact hJlit (_, ()) _
                            ⟨by assumption, Or.inl (M7SearchTactics.bv32_lit_even hlt30)⟩
                        · p2_steps_raw
                          have hlt30 : idx.toNat < 2 ^ 30 := by omega
                          exact hJlit (_, ()) _
                            ⟨by assumption, Or.inr (M7SearchTactics.bv32_lit_odd hlt30)⟩
                  · p2_steps_raw; exact hJnext () ml ⟨st, hcv_eq, hst, hfl, hml⟩
                · p2_steps_raw; exact hJnext () ml ⟨st, hcv_eq, hst, hfl, hml⟩
            · p2_steps_raw
              let st' : FullState := { st with core := { st.core with probing := 0#64 } }
              have hst' : FullSparseInv c F0 st' := fullSparseInv_with_probing hst 0#64
              exact hQ 10#64 st' _ hst'.1.lengths (Or.inr (Or.inr (Or.inl rfl))) hfl rfl
                (fun h => absurd h (by decide)) (fun h => by rcases h with h | h <;> cases h)
                (fun _ => hst'.2.2.2.1.2) (by assumption)
        · let LuckyRet : Tup Val [i64] → Mem 64 → Prop := fun (r, _) mr =>
            ∃ sr : FullState, sr.LengthsOk c ∧ (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) ∧
              sr.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (r = 20#64 → F0.Unsat) ∧
              (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 sr ∧ sr.core.cur_level = 0) ∧
              (r = 10#64 → sr.scratch.extend_len ≤ c.extend_cap) ∧ (FullMem c sr ⋆ R) mr
          p2_steps_raw
          p2_call hScan
          refine ⟨c, F0, s3, R, rfl, hsp3, hcl3_0, by assumption, ?_⟩
          intro r1 s1_ m1_ hlen1_ hr1_ hfl1_ huns1_ h02_1_ h10_1_ hm1_
          p2_steps_raw
          refine wp_join_group (ts := [i64]) LuckyRet ?_ ?_
          · rintro JsA ⟨rA, ⟨⟩⟩ mA ⟨srA, hlenA, hrA, hflA, hunsA, h02A, h10A, hmA⟩
            rw [Blocks.get_here]
            p2_steps_raw
            refine wp_join_group (ts := [i64]) LuckyRet ?_ ?_
            · rintro JsB ⟨rB, ⟨⟩⟩ mB ⟨srB, hlenB, hrB, hflB, hunsB, h02B, h10B, hmB⟩
              rw [Blocks.get_here]
              p2_steps_raw
              refine wp_join_group (ts := [i64]) LuckyRet ?_ ?_
              · rintro JsC ⟨rC, ⟨⟩⟩ mC ⟨srC, hlenC, hrC, hflC, hunsC, h02C, h10C, hmC⟩
                rw [Blocks.get_here]
                p2_steps_raw
                let sr' : FullState := { srC with core := { srC.core with probing := 0#64 } }
                have hlenC' : sr'.LengthsOk c :=
                  ⟨{ hlenC.core_ok with vals_len := hlenC.core_ok.vals_len }, hlenC.scratch_ok⟩
                exact hQ rC sr' _ hlenC' hrC hflC rfl hunsC
                  (fun h02 => let ⟨hspC, hclC⟩ := h02C h02
                    ⟨fullSparseInv_with_probing hspC 0#64, hclC⟩)
                  h10C (by assumption)
              · intro JsC hJsC
                p2_steps_raw
                p2_jnz_split hrB0
                · obtain ⟨hspB, hclB⟩ := h02B (Or.inl (by simpa using hrB0))
                  p2_steps_raw
                  p2_call hScan
                  refine ⟨c, F0, srB, R, rfl, hspB, hclB, hmB, ?_⟩
                  intro r4 s4 m4 hlen4 hr4 hfl4 huns4 h02_4 h10_4 hm4
                  exact hJsC (r4, ()) m4 ⟨s4, hlen4, hr4, Nat.le_trans hfl4 hflB, huns4, h02_4,
                    h10_4, hm4⟩
                · p2_steps_raw
                  exact hJsC (rB, ()) mB ⟨srB, hlenB, hrB, hflB, hunsB, h02B, h10B, hmB⟩
            · intro JsB hJsB
              p2_steps_raw
              p2_jnz_split hrA0
              · obtain ⟨hspA, hclA⟩ := h02A (Or.inl (by simpa using hrA0))
                p2_steps_raw
                p2_call hScan
                refine ⟨c, F0, srA, R, rfl, hspA, hclA, hmA, ?_⟩
                intro r3 s3_ m3 hlen3 hr3 hfl3 huns3 h02_3 h10_3 hm3
                exact hJsB (r3, ()) m3 ⟨s3_, hlen3, hr3, Nat.le_trans hfl3 hflA, huns3, h02_3,
                  h10_3, hm3⟩
              · p2_steps_raw
                exact hJsB (rA, ()) mA ⟨srA, hlenA, hrA, hflA, hunsA, h02A, h10A, hmA⟩
          · intro JsA hJsA
            p2_steps_raw
            p2_jnz_split hr10
            · obtain ⟨hsp1_, hcl1_⟩ := h02_1_ (Or.inl (by simpa using hr10))
              p2_steps_raw
              p2_call hScan
              refine ⟨c, F0, s1_, R, rfl, hsp1_, hcl1_, hm1_, ?_⟩
              intro r2 s2_ m2 hlen2 hr2 hfl2_ huns2 h02_2 h10_2 hm2
              exact hJsA (r2, ()) m2 ⟨s2_, hlen2, hr2, Nat.le_trans hfl2_ (Nat.le_trans hfl1_ hfl2),
                huns2, h02_2, h10_2, hm2⟩
            · p2_steps_raw
              exact hJsA (r1, ()) m1_ ⟨s1_, hlen1_, hr1_, Nat.le_trans hfl1_ hfl2, huns1_,
                h02_1_, h10_1_, hm1_⟩
      · intro J2 hJ2
        p2_steps_raw
        p2_jnz_split hprop_lt
        · obtain ⟨F_cur1, hw1⟩ := hsp1.1.witness
          p2_steps_raw
          p2_call hProp
          refine ⟨c, F0, F_cur1, s1, R, rfl, hsp1.1.lengths, hw1, hsp1.2.2.2.2, hm1, ?_⟩
          dsimp only
          intro pr0 vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena'
            wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m_p
            hlen_p hw_p htr_p hperm_p hfl_p hr_or _ h1_p _ _ hm_p
          let s_p : FullState :=
            { core := { s1.core with
                vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
                unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
                wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
                confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
              scratch := { s1.scratch with
                search_ticks := ticks', wsort := wsort', phases := phases' } }
          have hsp_p : FullSparseInv c F0 s_p :=
            fullSparseInv_of_fullPropagate hsp1 hlen_p hw_p hperm_p rfl rfl rfl rfl rfl
          have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_p hfl1
          have hcl_p0 : s_p.core.cur_level = 0 := hcl1_0
          p2_steps_raw
          p2_jnz_split hpr0_1
          · obtain ⟨_, _, hconf⟩ := h1_p (by simpa using hpr0_1)
            have hunsat : F0.Unsat := level0_unsat_of_conflict_okW hw_p hcl_p0 hconf
            p2_steps_raw
            let s_inc : FullState :=
              { s_p with core := { s_p.core with inconsistent := 1#64, probing := 0#64 } }
            have hlen_inc : s_inc.LengthsOk c :=
              ⟨{ hlen_p.core_ok with vals_len := hlen_p.core_ok.vals_len }, hlen_p.scratch_ok⟩
            exact hQ 20#64 s_inc _ hlen_inc (Or.inr (Or.inr (Or.inr rfl))) hfl_p'
              rfl (fun _ => hunsat) (fun h => by rcases h with h | h <;> cases h)
              (fun h => by cases h) (by assumption)
          · p2_steps_raw
            p2_jnz_split hpr0_2
            · p2_steps_raw
              let s_pr : FullState := { s_p with core := { s_p.core with probing := 0#64 } }
              have hsp_pr : FullSparseInv c F0 s_pr := fullSparseInv_with_probing hsp_p 0#64
              exact hQ 2#64 s_pr _ hsp_pr.1.lengths (Or.inr (Or.inl rfl)) hfl_p' rfl
                (fun h => by cases h) (fun _ => ⟨hsp_pr, hcl_p0⟩) (fun h => by cases h)
                (by assumption)
            · p2_steps_raw
              exact hJ2 () m_p ⟨s_p, hsp_p, hcl_p0, hfl_p', hm_p⟩
        · p2_steps_raw
          exact hJ2 () m1 ⟨s1, hsp1, hcl1_0, hfl1, hm1⟩
    · intro J1 hJ1
      p2_steps_raw
      p2_jnz_split hcl0
      · p2_steps_raw
        refine p2_lucky_bt0_wp hBt hsp hm fun s1 m1 _ hfl_eq hsp1 hcl1_0 hm1 => ?_
        p2_steps_raw
        exact hJ1 () m1 ⟨s1, hsp1, hcl1_0, by rw [hfl_eq]; exact Nat.le_refl _, hm1⟩
      · have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
          have := hsp.1.lengths.core_ok.trail_end_le
          have := hsp.1.lengths.core_ok.cur_vars_le
          obtain ⟨_, hw0⟩ := hsp.1.witness
          have := hw0.cur_level_le; omega
        have hcl_eq0 : s.core.cur_level = 0 := by
          have h := hcl0
          simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_lt64] at h
          exact Nat.eq_zero_of_not_pos (of_decide_eq_false h)
        p2_steps_raw
        exact hJ1 () m ⟨s, hsp, hcl_eq0, Nat.le_refl _, hm⟩

/-- Canonical `Full.fullLuckySpec` drop-in WP proof for `full_lucky_late_m7`. -/
theorem full_lucky_late_m7_dropin_wp (Γ : Env)
    (hPolar : EnvSpec Γ "full_lucky_polar_m7" fullLuckyPolarSpec)
    (hScan : EnvSpec Γ "full_lucky_scan" fullLuckyScanSpec)
    (hAssign : EnvSpec Γ "full_assign" fullAssignSpec)
    (hBt : EnvSpec Γ "full_backtrack" fullBacktrackSpec)
    (hProp : EnvSpec Γ "full_propagate" fullPropagateSpec) :
    ∀ a m Q X, Full.fullLuckySpec a m Q X → Func.wp Γ full_lucky_late_m7_body a m Q X :=
  fun _ _ _ _ hs =>
    full_lucky_late_m7_wp Γ hPolar hScan hAssign hBt hProp _ _ _ _ (m7LuckyLateSpec_to_canon hs)

end LeanQbe.T.Examples.Kissat.FullM7Search
