module

public import LeanQbe.T.Examples.Kissat.FullM7SearchProof1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
import all Kraken.Mem
import all Kraken.Separation

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
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
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
        evalTactic (← `(tactic| all_goals (try (repeat p2_strip))))
        go (fuel - 1)
        out := out ++ (← getUnsolvedGoals)
      else
        out := out.push (← getMainGoal)
    setGoals out.toList
  go 500

local macro "p2_to_group" : tactic =>
  `(tactic| ((try p2_unmdata); (repeat p2_strip); p2_to_group_step))

open Lean Elab Tactic in
/-- Step straight-line `C0Step` ops until `Expr.jnz`, then split it once. -/
local elab "p2_split" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let g ← getMainGoal
    let rawTy ← Lean.instantiateMVars (← g.getType)
    let ty := rawTy.consumeMData
    if rawTy.isMData then
      let g' ← g.change ty (checkDefEq := false)
      replaceMainGoal [g']
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta.consumeMData).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← Lean.Elab.Tactic.evalTactic (← `(tactic| c0_step))
      return
    evalTactic (← `(tactic| all_goals (repeat p2_strip)))
    if ← Lean.Elab.Tactic.tryTactic (evalTactic (← `(tactic| c0_step))) then
      evalTactic (← `(tactic| all_goals (repeat p2_strip)))
      go (fuel - 1)
  go 120

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
    injection hom with hom; subst om; subst m0; simp only [Blocks.get]; p2_to_group
    apply wp_join_group (ts := [i64]) (fun xs m0 => xs = (nmBv, ()) ∧ m0 = m)
    · rintro _J20 ⟨nm, ⟨⟩⟩ m0 ⟨hnm, hm0⟩
      injection hnm with hnm; subst nm; subst m0; simp only [Blocks.get]; p2_steps
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
        injection hob with hob; subst old_base; simp only [Blocks.get]
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
          injection hnb with hnb; subst new_base; simp only [Blocks.get]
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
            simp only [Blocks.get]; p2_steps
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

end LeanQbe.T.Examples.Kissat.FullM7Search
