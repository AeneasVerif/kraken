/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1SweepDenseProof2c
import LeanQbe.T.Examples.Kissat.FullM6SweepProofEls
import LeanQbe.T.Examples.Kissat.FullM6SweepProofVar1b
import LeanQbe.T.Examples.Kissat.FullFidelitySweepProofVar
import LeanQbe.T.Examples.Kissat.FullCongLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullReduceLemmas1
import LeanQbe.T.Examples.Kissat.FullSpec1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S1-A Proofs — Part 2d (`full_m6_dense_els`)

Parametric `(Γ : Env)` proof (`public section`, `0` `@[expose]`, `0` `import all`,
`<= 100` cols, `< 1,400` LOC, every theorem `<= 420` lines):
1. `full_m6_dense_els_s13_wp` (`step13DenseElsSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongSpecs
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open FullM6Sweep.M6ElsBv
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FullM6Sweep.M6SweepTactics

local elab "c0_hsteps_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false, pruneJnz := false }
    10000

/-! ## 1. State Preservation & Union-Find Helpers -/

private theorem s13_denseInvW_set_incons {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    (huns : (cnfOfClauses F_cur).Unsat) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with inconsistent := 1#64 } } :=
  ⟨⟨{ hinv.1.core_ok with vals_len := hinv.1.core_ok.vals_len }, hinv.1.scratch_ok⟩,
   { hinv.2.1 with
     arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
     watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r)
     inconsistent_sound := fun _ => huns },
   hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem s13_denseInvW_set_repr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {rp' : List (BitVec 32)} (hrp : rp'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with repr := rp' } } :=
  ⟨⟨{ hinv.1.core_ok with repr_len := hrp }, hinv.1.scratch_ok⟩,
   { hinv.2.1 with
     arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
     watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem s13_denseInvW_inc_sweep {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    (sw' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with sweep_cnt := sw' } } :=
  ⟨⟨hinv.1.core_ok, { hinv.1.scratch_ok with glue_used_len := hinv.1.scratch_ok.glue_used_len }⟩,
   hinv.2.1, hinv.2.2.1, hinv.2.2.2.1,
   FullExtScratchOk.of_pres hinv.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => hr),
   hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem s13_denseInvW_after_addUnit {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc' phases' ta' ba' pt' pb'
      hp' ps' hl' qsi' qss'}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            cur_level := cl', unassigned := unass', unflushed := unfl',
                            inconsistent := inc' }
      scratch := { s.scratch with phases := phases', target_assigned := ta', best_assigned := ba',
                                  phases_target := pt', phases_best := pb', heap := hp', pos := ps',
                                  heap_len := hl', q_search_idx := qsi',
                                  q_search_stamp := qss' } } : FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                    trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                    cur_level := cl', unassigned := unass', unflushed := unfl',
                    inconsistent := inc' })
    (hcl' : cl' = 0) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                              cur_level := cl', unassigned := unass', unflushed := unfl',
                              inconsistent := inc' }
        scratch := { s.scratch with phases := phases', target_assigned := ta', best_assigned := ba',
                                    phases_target := pt', phases_best := pb', heap := hp',
                                    pos := ps', heap_len := hl', q_search_idx := qsi',
                                    q_search_stamp := qss' } } :=
  ⟨hlen', hw', hinv.2.2.1, (fun r hr hng => hinv.2.2.2.1 r hr hng),
   ⟨fun i hi => hinv.2.2.2.2.1.1 i hi, hinv.2.2.2.2.1.2⟩, hcl', hinv.2.2.2.2.2.2⟩

private theorem s13_bv8_sext32_eq0_iff (v : BitVec 8) : v.signExtend 32 = 0#32 ↔ v = 0#8 := by
  have h := m6_els_bv8_eq0 v
  constructor <;> intro hv
  · have hb : (v.signExtend 32 == 0#32) = true := beq_iff_eq.mpr hv
    rw [h] at hb; exact beq_iff_eq.mp hb
  · have hb : (v == 0#8) = true := beq_iff_eq.mpr hv
    rw [← h] at hb; exact beq_iff_eq.mp hb

private theorem s13_bv8_sext32_slt (v : BitVec 8) :
    (BitVec.signExtend 32 (BitVec.truncate 8 0#32)).slt (v.signExtend 32) =
      (0#8 : BitVec 8).slt v := by
  have ht : BitVec.truncate 8 0#32 = 0#8 := rfl
  have hm : min 32 8 = 8 := rfl
  rw [ht]; simp only [BitVec.slt, BitVec.toInt_signExtend, hm]
  have h1 := BitVec.le_toInt v
  have h2 := BitVec.toInt_lt (x := v)
  have h3 := BitVec.le_toInt (0#8 : BitVec 8)
  have h4 := BitVec.toInt_lt (x := (0#8 : BitVec 8))
  simp only [Nat.reduceSub] at h1 h2 h3 h4
  have hb : ∀ k : Int, -128 ≤ k → k < 128 → k.bmod 256 = k := by
    intro k hk1 hk2; unfold Int.bmod; dsimp only; split <;> omega
  rw [hb _ h3 h4, hb _ h1 h2]

private theorem s13_bv8_sgt0_of_sext32 {v : BitVec 8}
    (h : (BitVec.signExtend 32 (BitVec.truncate 8 0#32)).slt (v.signExtend 32) = true) :
    (0#8 : BitVec 8).slt v = true := by
  simpa only [s13_bv8_sext32_slt] using h

private theorem s13_bv8_nsgt0_of_sext32 {v : BitVec 8}
    (h : ¬ (BitVec.signExtend 32 (BitVec.truncate 8 0#32)).slt (v.signExtend 32) = true) :
    ¬ (0#8 : BitVec 8).slt v = true := by
  simpa only [s13_bv8_sext32_slt] using h

private theorem s13_nat_xor1_cases (x : Nat) :
    x ^^^ 1 = if x % 2 = 0 then x + 1 else x - 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor]
  rcases i with _ | i
  · simp only [Nat.testBit_zero, show (1 : Nat) % 2 = 1 from rfl, decide_true, Bool.xor_true]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h] <;> omega
  · simp only [Nat.testBit_succ, show (1 : Nat) / 2 = 0 from rfl, Nat.zero_testBit,
      Bool.xor_false]
    split <;> rename_i h
    · rw [show (x + 1) / 2 = x / 2 by omega]
    · rw [show (x - 1) / 2 = x / 2 by omega]

private theorem s13_nat_xor1_lt {x N : Nat} (hx : x < 2 * N) : x ^^^ 1 < 2 * N := by
  rw [s13_nat_xor1_cases]; split <;> omega

private theorem s13_entails_unit_of_pos_val {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (hcl0 : k.cur_level = 0) {l : Nat} (hlt : l < 2 * k.cur_vars)
    (hlv : l < k.vals.length) (hpos : (0#8 : BitVec 8).slt (k.vals[l]'hlv) = true) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l]) := by
  have hd := hw.vals_domain l hlt
  rw [List.getElem?_eq_getElem hlv, Option.getD_some] at hd
  rcases hd with h0 | h1 | h2
  · rw [h0] at hpos; exact absurd hpos (by decide)
  · exact m6_lvl0_true_entails hw hcl0 hlt
      (by rw [List.getElem?_eq_getElem hlv, Option.getD_some]; exact h1)
  · rw [h2] at hpos; exact absurd hpos (by decide)

private theorem s13_entails_unit_of_neg_val {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (hcl0 : k.cur_level = 0) {l : Nat} (hlt : l < 2 * k.cur_vars)
    (hlv : l < k.vals.length) (hnz : k.vals[l]'hlv ≠ 0#8)
    (hneg : ¬ (0#8 : BitVec 8).slt (k.vals[l]'hlv) = true) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1]) := by
  have hd := hw.vals_domain l hlt
  rw [List.getElem?_eq_getElem hlv, Option.getD_some] at hd
  rcases hd with h0 | h1 | h2
  · exact absurd h0 hnz
  · exact absurd (by rw [h1]; decide) hneg
  · exact m6_lvl0_false_entails hw hcl0 hlt
      (by rw [List.getElem?_eq_getElem hlv, Option.getD_some]; exact h2)

private theorem s13_litEquiv_neg_taut {f : CNF Nat} {a b : Nat} (h : LitEquiv f a b) :
    f.EntailsClause (cnfClause [a, b ^^^ 1]) ∧ f.EntailsClause (cnfClause [a ^^^ 1, b]) := by
  constructor <;> rw [CNF.entails_clause_def] <;> intro α hα <;> rw [← clauseEvalVal_iff] <;>
    simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
      show a ^^^ 1 = litNeg a from rfl, show b ^^^ 1 = litNeg b from rfl, evalLitVal_litNeg,
      litEquiv_eval hα h] <;> cases evalLitVal α b <;> rfl

private theorem s13_fullCongReprInv_union {F_cur : List (List Nat)} {nlits : Nat}
    {repr : List (BitVec 32)} (hinv : FullCongReprInv F_cur nlits repr)
    {ra rb : BitVec 32} (_hra : ra.toNat < nlits) (hrb : rb.toNat < nlits)
    (hrb1 : (rb ^^^ 1#32).toNat < nlits)
    (hlt : ra.toNat < rb.toNat) (hne : ra ≠ rb ^^^ 1#32)
    (heqv : LitEquiv (cnfOfClauses F_cur) ra.toNat rb.toNat) :
    let repr' := (repr.set rb.toNat ra).set (rb ^^^ 1#32).toNat (ra ^^^ 1#32)
    FullCongReprInv F_cur nlits repr' := by
  intro repr'
  have hrb_xor : (rb ^^^ 1#32).toNat = rb.toNat ^^^ 1 := m6_els_bv32_xor1_toNat rb
  have hra_xor : (ra ^^^ 1#32).toNat = ra.toNat ^^^ 1 := m6_els_bv32_xor1_toNat ra
  have hne_to : ra.toNat ≠ rb.toNat ^^^ 1 := fun h =>
    hne (BitVec.eq_of_toNat_eq (by rw [hrb_xor]; exact h))
  have hrb_ne : rb ^^^ 1#32 ≠ rb := fun h => by
    have h0 := congrArg (rb ^^^ ·) h
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] at h0
    exact absurd h0 (by decide)
  have hrb_ne_to : rb.toNat ^^^ 1 ≠ rb.toNat := fun h =>
    hrb_ne (BitVec.eq_of_toNat_eq (by rw [hrb_xor]; exact h))
  have h1 : (ra.toNat ^^^ 1) / 2 = ra.toNat / 2 := litVar_litNeg ra.toNat
  have h2 : (rb.toNat ^^^ 1) / 2 = rb.toNat / 2 := litVar_litNeg rb.toNat
  have hdiv : ra.toNat / 2 < rb.toNat / 2 := by
    by_cases heq : ra.toNat / 2 = rb.toNat / 2
    · exfalso
      have hdv_ra : ra.toNat = 2 * (ra.toNat / 2) + ra.toNat % 2 :=
        (Nat.div_add_mod ra.toNat 2).symm
      have hdv_rb : rb.toNat = 2 * (rb.toNat / 2) + rb.toNat % 2 :=
        (Nat.div_add_mod rb.toNat 2).symm
      have hdv_rb1 : rb.toNat ^^^ 1 = 2 * (rb.toNat / 2) + (rb.toNat ^^^ 1) % 2 := by
        rw [← h2]; exact (Nat.div_add_mod (rb.toNat ^^^ 1) 2).symm
      have hmod_ra : ra.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
      have hmod_rb : rb.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
      have hmod_rb1 : (rb.toNat ^^^ 1) % 2 < 2 := Nat.mod_lt _ (by decide)
      apply hne_to; omega
    · omega
  have hle_div : ra.toNat / 2 + 1 ≤ rb.toNat / 2 := hdiv
  have hx_lt : ra.toNat ^^^ 1 ≤ rb.toNat ^^^ 1 := by
    have hdv_ra1 : ra.toNat ^^^ 1 = 2 * (ra.toNat / 2) + (ra.toNat ^^^ 1) % 2 := by
      rw [← h1]; exact (Nat.div_add_mod (ra.toNat ^^^ 1) 2).symm
    have hdv_rb1 : rb.toNat ^^^ 1 = 2 * (rb.toNat / 2) + (rb.toNat ^^^ 1) % 2 := by
      rw [← h2]; exact (Nat.div_add_mod (rb.toNat ^^^ 1) 2).symm
    have hm1 : (ra.toNat ^^^ 1) % 2 < 2 := Nat.mod_lt _ (by decide)
    have hm2 : (rb.toNat ^^^ 1) % 2 < 2 := Nat.mod_lt _ (by decide)
    omega
  have hlen : nlits ≤ repr'.length := by simp [repr', List.length_set, hinv.1.1]
  have hrb_bd : rb.toNat < repr.length := by have := hinv.1.1; omega
  have hrb1_bd : (rb ^^^ 1#32).toNat < repr.length := by have := hinv.1.1; omega
  have hget : ∀ x < nlits,
      repr'[x]?.getD 0#32 =
        if x = (rb ^^^ 1#32).toNat then ra ^^^ 1#32
        else if x = rb.toNat then ra else repr[x]?.getD 0#32 := by
    intro x _
    by_cases h1 : x = (rb ^^^ 1#32).toNat
    · subst h1; dsimp only [repr']
      rw [ite_eq_left rfl, List.getElem?_set_self (by simp [List.length_set]; exact hrb1_bd),
        Option.getD_some]
    · rw [ite_eq_right h1]; dsimp only [repr']
      rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : x = rb.toNat
      · subst h2; rw [ite_eq_left rfl, List.getElem?_set_self hrb_bd, Option.getD_some]
      · rw [ite_eq_right h2, List.getElem?_set_ne (Ne.symm h2)]
  refine ⟨⟨hlen, fun x hx => ?_⟩, fun x hx => ?_⟩
  · rw [hget x hx]
    by_cases h1 : x = (rb ^^^ 1#32).toNat
    · rw [ite_eq_left h1, hra_xor, h1, hrb_xor]; exact hx_lt
    · rw [ite_eq_right h1]
      by_cases h2 : x = rb.toNat
      · rw [ite_eq_left h2, h2]; exact Nat.le_of_lt hlt
      · rw [ite_eq_right h2]; exact hinv.1.2 x hx
  · rw [hget x hx]
    by_cases h1 : x = (rb ^^^ 1#32).toNat
    · rw [ite_eq_left h1, h1, hrb_xor, hra_xor]
      simpa only [m6_els_bv32_xor1_toNat] using m6_litEquiv_neg heqv.symm
    · rw [ite_eq_right h1]
      by_cases h2 : x = rb.toNat
      · rw [ite_eq_left h2, h2]; exact heqv.symm
      · rw [ite_eq_right h2]; exact hinv.2 x hx

private theorem s13_dense_els_exit_ret {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} {R : Mem 64 → Prop} {mL : Mem 64} {Q : Post [.bool]}
    (hinvL : FullDenseInvW c F0 F_cur sL) (hcvL : sL.core.cur_vars = s.core.cur_vars)
    (hflL : sL.core.fuel = s.core.fuel)
    (hrepL : FullCongReprInv F_cur (2 * sL.core.cur_vars) sL.core.repr)
    (htmkL : sL.scratch.tarjan_mark = s.scratch.tarjan_mark)
    (htrhL : sL.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hscrL : sL.scratch.scratch_buf = s.scratch.scratch_buf)
    (hws2L : sL.scratch.work_stk2 = s.scratch.work_stk2)
    (hguL : sL.scratch.glue_used = s.scratch.glue_used)
    (hmL : (FullMem c sL ⋆ R) mL)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel →
      FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Q (sL.core.inconsistent == 0#64, ()) mL := by
  by_cases hinc : sL.core.inconsistent = 0#64
  · rw [show (sL.core.inconsistent == 0#64) = true from beq_iff_eq.mpr hinc]
    exact hQ true sL mL hinvL hcvL hflL hrepL htmkL htrhL hscrL hws2L hguL
      (fun hn => Bool.noConfusion hn) hmL
  · rw [show (sL.core.inconsistent == 0#64) = false from
      Bool.eq_false_iff.mpr (fun heq => hinc (beq_iff_eq.mp heq))]
    exact hQ false sL mL hinvL hcvL hflL hrepL htmkL htrhL hscrL hws2L hguL
      (fun _ => ⟨hinvL.2.1.ext_sound.2 (hinvL.2.1.inconsistent_sound hinc), hinc⟩) hmL

/-! ## 2. Inner Loop Step Proof -/

private def s13DenseElsStepExpr (c : FullCfg) (eiL nlits : Val i64) (a b : Val i32)
    (J : Cont [i64]) : Expr Val Cont [.bool] :=
  let pRepr := c.pRepr; let pVals := c.pVals; let pFl := c.pFlags
  let eiN := eiL + 1#64
  Expr.jnz (Arg.var (nlits.ule (a.setWidth 64))) (Expr.jump J (Arg.var eiN, ()))
    (Expr.let_ (Op.mk (.zext 32 64) (Arg.var b, ())) (fun (b64, ()) =>
    Expr.let_ (Op.mk (.cmp .uge i64 .bool rfl) (Arg.var b64, Arg.var nlits, ())) (fun (bb, ()) =>
    Expr.jnz (Arg.var bb) (Expr.jump J (Arg.var eiN, ()))
      (Expr.call (as := [i64, i32]) (bs := [i32]) "full_cong_find"
        (Arg.var pRepr, Arg.var a, ()) (fun (ra0, ()) =>
      Expr.call (as := [i64, i32]) (bs := [i32]) "full_cong_find"
        (Arg.var pRepr, Arg.var b, ()) (fun (rb0, ()) =>
      Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl) (Arg.var ra0, Arg.var rb0, ())) (fun (beq, ()) =>
      Expr.jnz (Arg.var beq) (Expr.jump J (Arg.var eiN, ()))
        (Expr.let_ (Op.mk (.xor i32) (Arg.var rb0, Arg.imm 1, ())) (fun (rb1, ()) =>
        Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl) (Arg.var ra0, Arg.var rb1, ()))
          (fun (bneg, ()) =>
        Expr.jnz (Arg.var bneg)
          (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1024, ())) (fun (pin, ()) =>
            Expr.store (t := i64) (Arg.imm 1) (Arg.var pin) (Expr.ret (Arg.imm false, ()))))
          (Expr.group (sig := [[i32, i32]]) (fun _Js2 => Blocks.cons
            (fun (p : Tup Val [i32, i32]) =>
            let ra := p.1; let rb := p.2.1
            Expr.let_ (Op.mk (.zext 32 64) (Arg.var ra, ())) (fun (ra64, ()) =>
            Expr.let_ (Op.mk (.add i64) (Arg.var pVals, Arg.var ra64, ())) (fun (ava, ()) =>
            Expr.load i8 (Arg.var ava) (fun va =>
            Expr.let_ (Op.mk (.zext 32 64) (Arg.var rb, ())) (fun (rb64, ()) =>
            Expr.let_ (Op.mk (.add i64) (Arg.var pVals, Arg.var rb64, ())) (fun (avb, ()) =>
            Expr.load i8 (Arg.var avb) (fun vb =>
            Expr.group (sig := [[]]) (fun _Js3 => Blocks.cons (fun _ =>
              Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) (fun (z8a, ()) =>
              Expr.let_ (Op.mk (.sext 8 32) (Arg.var va, ())) (fun (va32, ()) =>
              Expr.let_ (Op.mk (.sext 8 32) (Arg.var z8a, ())) (fun (z32a, ()) =>
              Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var va32, Arg.var z32a, ()))
                (fun (bva, ()) =>
              Expr.jnz (Arg.var bva)
                (Expr.group (sig := [[i32]]) (fun _Ju => Blocks.cons (fun (u, ()) =>
                  Expr.call (as := [i64, i32]) (bs := [.bool]) "full_add_unit"
                    (Arg.var c.hdr, Arg.var u, ()) (fun (okU, ()) =>
                  Expr.jnz (Arg.var okU) (Expr.jump J (Arg.var eiN, ()))
                    (Expr.ret (Arg.imm false, ())))) Blocks.nil)
                (fun Ju =>
                  Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) (fun (z8, ()) =>
                  Expr.let_ (Op.mk (.sext 8 32) (Arg.var va, ())) (fun (va32', ()) =>
                  Expr.let_ (Op.mk (.sext 8 32) (Arg.var z8, ())) (fun (z32, ()) =>
                  Expr.let_ (Op.mk (.cmp .sgt i32 .bool rfl) (Arg.var va32', Arg.var z32, ()))
                    (fun (bpos, ()) =>
                  Expr.jnz (Arg.var bpos) (Expr.jump Ju.fst (Arg.var rb, ()))
                    (Expr.let_ (Op.mk (.xor i32) (Arg.var rb, Arg.imm 1, ()))
                        (fun (rbn, ()) =>
                      Expr.jump Ju.fst (Arg.var rbn, ())))))))))
                (Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) (fun (z8b, ()) =>
                Expr.let_ (Op.mk (.sext 8 32) (Arg.var vb, ())) (fun (vb32, ()) =>
                Expr.let_ (Op.mk (.sext 8 32) (Arg.var z8b, ())) (fun (z32b, ()) =>
                Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var vb32, Arg.var z32b, ()))
                  (fun (bvb, ()) =>
                Expr.jnz (Arg.var bvb)
                  (Expr.group (sig := [[i32]]) (fun _Ju => Blocks.cons (fun (u, ()) =>
                    Expr.call (as := [i64, i32]) (bs := [.bool]) "full_add_unit"
                      (Arg.var c.hdr, Arg.var u, ()) (fun (okU, ()) =>
                    Expr.jnz (Arg.var okU) (Expr.jump J (Arg.var eiN, ()))
                      (Expr.ret (Arg.imm false, ())))) Blocks.nil)
                  (fun Ju =>
                    Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) (fun (z8, ()) =>
                    Expr.let_ (Op.mk (.sext 8 32) (Arg.var vb, ())) (fun (vb32', ()) =>
                    Expr.let_ (Op.mk (.sext 8 32) (Arg.var z8, ())) (fun (z32, ()) =>
                    Expr.let_ (Op.mk (.cmp .sgt i32 .bool rfl) (Arg.var vb32', Arg.var z32, ()))
                      (fun (bpos, ()) =>
                    Expr.jnz (Arg.var bpos) (Expr.jump Ju.fst (Arg.var ra, ()))
                      (Expr.let_ (Op.mk (.xor i32) (Arg.var ra, Arg.imm 1, ()))
                          (fun (ran, ()) =>
                        Expr.jump Ju.fst (Arg.var ran, ())))))))))
                  (Expr.let_ (Op.mk (.lshr i32) (Arg.var ra, Arg.imm 1, ())) (fun (va_idx, ()) =>
                  Expr.let_ (Op.mk (.zext 32 64) (Arg.var va_idx, ())) (fun (va64, ()) =>
                  Expr.let_ (Op.mk (.mul i64) (Arg.var va64, Arg.imm 4, ())) (fun (ova, ()) =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var pFl, Arg.var ova, ())) (fun (afva, ()) =>
                  Expr.load i32 (Arg.var afva) (fun fl_a =>
                  Expr.let_ (Op.mk (.and i32) (Arg.var fl_a, Arg.imm 1, ())) (fun (fa1, ()) =>
                  Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl) (Arg.var fa1, Arg.imm 0, ()))
                    (fun (bfa0, ()) =>
                  Expr.jnz (Arg.var bfa0) (Expr.jump J (Arg.var eiN, ()))
                    (Expr.let_ (Op.mk (.lshr i32) (Arg.var rb, Arg.imm 1, ()))
                        (fun (vb_idx, ()) =>
                    Expr.let_ (Op.mk (.zext 32 64) (Arg.var vb_idx, ())) (fun (vb64, ()) =>
                    Expr.let_ (Op.mk (.mul i64) (Arg.var vb64, Arg.imm 4, ())) (fun (ovb, ()) =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var pFl, Arg.var ovb, ())) (fun (afvb, ()) =>
                    Expr.load i32 (Arg.var afvb) (fun fl_b =>
                    Expr.let_ (Op.mk (.and i32) (Arg.var fl_b, Arg.imm 1, ())) (fun (fb1, ()) =>
                    Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl) (Arg.var fb1, Arg.imm 0, ()))
                      (fun (bfb0, ()) =>
                    Expr.jnz (Arg.var bfb0) (Expr.jump J (Arg.var eiN, ()))
                      (Expr.let_ (Op.mk (.zext 32 64) (Arg.var rb, ())) (fun (rb64b, ()) =>
                      Expr.let_ (Op.mk (.mul i64) (Arg.var rb64b, Arg.imm 4, ())) (fun (orb0, ()) =>
                      Expr.let_ (Op.mk (.add i64) (Arg.var pRepr, Arg.var orb0, ()))
                          (fun (arp0, ()) =>
                      Expr.store (Arg.var ra) (Arg.var arp0)
                        (Expr.let_ (Op.mk (.xor i32) (Arg.var rb, Arg.imm 1, ()))
                            (fun (rb1b, ()) =>
                        Expr.let_ (Op.mk (.zext 32 64) (Arg.var rb1b, ())) (fun (rb1_64, ()) =>
                        Expr.let_ (Op.mk (.mul i64) (Arg.var rb1_64, Arg.imm 4, ()))
                            (fun (orb1, ()) =>
                        Expr.let_ (Op.mk (.add i64) (Arg.var pRepr, Arg.var orb1, ()))
                            (fun (arp1, ()) =>
                        Expr.let_ (Op.mk (.xor i32) (Arg.var ra, Arg.imm 1, ())) (fun (ra1b, ()) =>
                        Expr.store (Arg.var ra1b) (Arg.var arp1)
                          (Expr.let_ (Op.mk (.lshr i32) (Arg.var rb, Arg.imm 1, ()))
                              (fun (vb_d, ()) =>
                          Expr.let_ (Op.mk (.zext 32 64) (Arg.var vb_d, ())) (fun (vb_d64, ()) =>
                          Expr.let_ (Op.mk (.mul i64) (Arg.var vb_d64, Arg.imm 4, ()))
                              (fun (ovb_d, ()) =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var pFl, Arg.var ovb_d, ()))
                              (fun (afvb_d, ()) =>
                          Expr.let_ (Op.mk (.lshr i32) (Arg.var rb, Arg.imm 1, ()))
                              (fun (vb_l, ()) =>
                          Expr.let_ (Op.mk (.zext 32 64) (Arg.var vb_l, ())) (fun (vb_l64, ()) =>
                          Expr.let_ (Op.mk (.mul i64) (Arg.var vb_l64, Arg.imm 4, ()))
                              (fun (ovb_l, ()) =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var pFl, Arg.var ovb_l, ()))
                              (fun (afvb_l, ()) =>
                          Expr.load i32 (Arg.var afvb_l) (fun fl_b2 =>
                          Expr.let_ (Op.mk (.or i32) (Arg.imm 1024, Arg.imm 1073741824, ()))
                              (fun (mk1, ()) =>
                          Expr.let_ (Op.mk (.or i32) (Arg.var mk1, Arg.imm 536870912, ()))
                              (fun (mk2, ()) =>
                          Expr.let_ (Op.mk (.not i32) (Arg.var mk2, ())) (fun (mk3, ()) =>
                          Expr.let_ (Op.mk (.and i32) (Arg.var fl_b2, Arg.var mk3, ()))
                              (fun (fl_b', ()) =>
                          Expr.store (Arg.var fl_b') (Arg.var afvb_d)
                            (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1080, ()))
                                (fun (pswc1, ()) =>
                            Expr.load i64 (Arg.var pswc1) (fun swc =>
                            Expr.let_ (Op.mk (.add i64) (Arg.var swc, Arg.imm 1, ()))
                                (fun (swcn, ()) =>
                            Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1080, ()))
                                (fun (pswc2, ()) =>
                            Expr.store (Arg.var swcn) (Arg.var pswc2)
                              (Expr.call (as := [i64, i32, i32]) (bs := [.bool])
                                "full_m6_els_lit" (Arg.var c.hdr, Arg.var rb, Arg.var ra, ())
                                (fun (okE1, ()) =>
                              Expr.jnz (Arg.var okE1)
                                (Expr.let_ (Op.mk (.xor i32) (Arg.var rb, Arg.imm 1, ()))
                                    (fun (rb1c, ()) =>
                                Expr.let_ (Op.mk (.xor i32) (Arg.var ra, Arg.imm 1, ()))
                                    (fun (ra1c, ()) =>
                                Expr.call (as := [i64, i32, i32]) (bs := [.bool])
                                  "full_m6_els_lit"
                                  (Arg.var c.hdr, Arg.var rb1c, Arg.var ra1c, ())
                                  (fun (okE2, ()) =>
                                Expr.jnz (Arg.var okE2)
                                  (Expr.let_ (Op.mk (.or i32) (Arg.var rb, Arg.imm 0, ()))
                                      (fun (rb0', ()) =>
                                  Expr.let_ (Op.mk (.xor i32) (Arg.var ra, Arg.imm 1, ()))
                                      (fun (ra1d, ()) =>
                                  Expr.call (as := [i64, i32, i32]) (bs := [i64]) "full_add_bin"
                                    (Arg.var c.hdr, Arg.var rb0', Arg.var ra1d, ())
                                    (fun (ab1, ()) =>
                                  Expr.let_ (Op.mk (.cmp .eq i64 .bool rfl)
                                      (Arg.var ab1, Arg.imm 20, ())) (fun (b1_20, ()) =>
                                  Expr.jnz (Arg.var b1_20) (Expr.ret (Arg.imm false, ()))
                                    (Expr.let_ (Op.mk (.cmp .eq i64 .bool rfl)
                                        (Arg.var ab1, Arg.imm 2, ())) (fun (b1_2, ()) =>
                                    Expr.jnz (Arg.var b1_2)
                                      (Expr.let_ (Op.mk (.add i64)
                                          (Arg.var c.hdr, Arg.imm 760, ())) (fun (po, ()) =>
                                        Expr.store (t := i64) (Arg.imm 1) (Arg.var po)
                                          (Expr.ret (Arg.imm true, ()))))
                                      (Expr.let_ (Op.mk (.xor i32) (Arg.var rb, Arg.imm 1, ()))
                                          (fun (rb1d, ()) =>
                                      Expr.call (as := [i64, i32, i32]) (bs := [i64])
                                        "full_add_bin"
                                        (Arg.var c.hdr, Arg.var rb1d, Arg.var ra, ())
                                        (fun (ab2, ()) =>
                                      Expr.let_ (Op.mk (.cmp .eq i64 .bool rfl)
                                          (Arg.var ab2, Arg.imm 20, ())) (fun (b2_20, ()) =>
                                      Expr.jnz (Arg.var b2_20) (Expr.ret (Arg.imm false, ()))
                                        (Expr.let_ (Op.mk (.cmp .eq i64 .bool rfl)
                                            (Arg.var ab2, Arg.imm 2, ())) (fun (b2_2, ()) =>
                                        Expr.jnz (Arg.var b2_2)
                                          (Expr.let_ (Op.mk (.add i64)
                                              (Arg.var c.hdr, Arg.imm 760, ())) (fun (po, ()) =>
                                            Expr.store (t := i64) (Arg.imm 1) (Arg.var po)
                                              (Expr.ret (Arg.imm true, ()))))
                                          (Expr.jump J (Arg.var eiN, ())))))))))))))))
                                  (Expr.ret (Arg.imm false, ()))))))
                                  (Expr.ret (Arg.imm false, ())))
                                    ))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            Blocks.nil)
            (fun Js3 =>
              Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) (fun (z8a, ()) =>
              Expr.let_ (Op.mk (.sext 8 32) (Arg.var va, ())) (fun (va32, ()) =>
              Expr.let_ (Op.mk (.sext 8 32) (Arg.var z8a, ())) (fun (z32a, ()) =>
              Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var va32, Arg.var z32a, ()))
                (fun (bva, ()) =>
              Expr.jnz (Arg.var bva)
                (Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) (fun (z8b, ()) =>
                Expr.let_ (Op.mk (.sext 8 32) (Arg.var vb, ())) (fun (vb32, ()) =>
                Expr.let_ (Op.mk (.sext 8 32) (Arg.var z8b, ())) (fun (z32b, ()) =>
                Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var vb32, Arg.var z32b, ()))
                  (fun (bvb, ()) =>
                Expr.jnz (Arg.var bvb)
                  (Expr.let_ (Op.mk (.sext 8 32) (Arg.var va, ())) (fun (va32', ()) =>
                  Expr.let_ (Op.mk (.sext 8 32) (Arg.var vb, ())) (fun (vb32', ()) =>
                  Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var va32', Arg.var vb32', ()))
                    (fun (bvne, ()) =>
                  Expr.jnz (Arg.var bvne)
                    (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1024, ()))
                        (fun (pin, ()) =>
                      Expr.store (t := i64) (Arg.imm 1) (Arg.var pin)
                        (Expr.ret (Arg.imm false, ()))))
                    (Expr.jump J (Arg.var eiN, ()))))))
                  (Expr.jump Js3.fst ()))))))
                (Expr.jump Js3.fst ())))))))))))))
            Blocks.nil)
          (fun Js2 =>
            Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var rb0, Arg.var ra0, ()))
              (fun (bsw, ()) =>
            Expr.jnz (Arg.var bsw) (Expr.jump Js2.fst (Arg.var rb0, Arg.var ra0, ()))
              (Expr.jump Js2.fst (Arg.var ra0, Arg.var rb0, ()))
                )))))))))))))

private theorem s13_dense_els_step_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hFind : ∀ a m Q X, Full.fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hAddUnit : M6EnvSpec Γ "full_add_unit" Full.fullAddUnitSpec)
    (hElsLit : ∀ a m Q X, step13ElsLitSpec a m Q X →
      Γ "full_m6_els_lit" [i64, i32, i32] [.bool] a m Q X)
    (hAddBin : M6EnvSpec Γ "full_add_bin" Full.fullAddBinSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sL : FullState}
    {neq : BitVec 32} {eiL : BitVec 64} {R : Mem 64 → Prop} {mL : Mem 64}
    {J : Cont [i64]}
    (hinvL : FullDenseInvW c F0 F_cur sL) (hcvL : sL.core.cur_vars = s.core.cur_vars)
    (hflL : sL.core.fuel = s.core.fuel)
    (hrepL : FullCongReprInv F_cur (2 * sL.core.cur_vars) sL.core.repr)
    (htmkL : sL.scratch.tarjan_mark = s.scratch.tarjan_mark)
    (htrhL : sL.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hscrL : sL.scratch.scratch_buf = s.scratch.scratch_buf)
    (hws2L : sL.scratch.work_stk2 = s.scratch.work_stk2)
    (hguL : sL.scratch.glue_used = s.scratch.glue_used)
    (heqb : M6EqBufOk F_cur s neq.toNat) (hneq_bd : neq.toNat < 2 ^ 32)
    (hei_lt : eiL.toNat < neq.toNat)
    (hei_next : (eiL + 1#64).toNat = eiL.toNat + 1)
    (_hinc0 : sL.core.inconsistent = 0#64) (hmL : (FullMem c sL ⋆ R) mL)
    (hJ : ∀ (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel →
      FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (FullMem c s' ⋆ R) m' → J (eiL + 1#64, ()) m')
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel →
      FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    let nlits := BitVec.ofNat 64 sL.core.cur_vars <<< 1#64
    let a := sL.scratch.work_stk2[(eiL <<< 1#64).toNat]?.getD 0#32
    let b := sL.scratch.work_stk2[((eiL <<< 1#64) + 1#64).toNat]?.getD 0#32
    wp Γ Q X (s13DenseElsStepExpr c eiL nlits a b J) mL := by
  let pRepr := c.pRepr; let pVals := c.pVals; let pFl := c.pFlags
  let nlits := BitVec.ofNat 64 sL.core.cur_vars <<< 1#64
  let a := sL.scratch.work_stk2[(eiL <<< 1#64).toNat]?.getD 0#32
  let b := sL.scratch.work_stk2[((eiL <<< 1#64) + 1#64).toNat]?.getD 0#32
  dsimp only [s13DenseElsStepExpr]
  have hcl := hinvL.1.core_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl.cur_vars_le; have hrp_len := hcl.repr_len
  have hvl_len := hcl.vals_len; have hfl_len := hcl.flags_len
  have ha_lt_cv : a.toNat < 2 * sL.core.cur_vars ∧ b.toNat < 2 * sL.core.cur_vars ∧
      LitEquiv (cnfOfClauses F_cur) a.toNat b.toNat := by
    have h1 := heqb.2 eiL.toNat hei_lt
    have hws := hws2L
    have he0 : (eiL <<< 1#64).toNat = 2 * eiL.toNat := by
      have : eiL.toNat < 2 ^ 32 := Nat.lt_trans hei_lt hneq_bd
      rw [show eiL <<< 1#64 = eiL <<< (1 : Nat) from rfl]; bv_omega
    have he1 : ((eiL <<< 1#64) + 1#64).toNat = 2 * eiL.toNat + 1 := by
      have : eiL.toNat < 2 ^ 32 := Nat.lt_trans hei_lt hneq_bd
      rw [show eiL <<< 1#64 = eiL <<< (1 : Nat) from rfl]; bv_omega
    dsimp only [a, b]; rw [hws, he0, he1, hcvL]
    exact h1
  have hnl_eq : nlits.toNat = 2 * sL.core.cur_vars := by
    dsimp only [nlits]; rw [show BitVec.ofNat 64 sL.core.cur_vars <<< 1#64 =
      BitVec.ofNat 64 sL.core.cur_vars <<< (1 : Nat) from rfl, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sL.core.cur_vars < 2 ^ 64),
      Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]; omega
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps!; exact hJ sL mL hinvL hcvL hflL hrepL htmkL htrhL hscrL hws2L hguL hmL
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps!; exact hJ sL mL hinvL hcvL hflL hrepL htmkL htrhL hscrL hws2L hguL hmL
  c0_hsteps_nogrp
  c0_call hFind
  refine ⟨F_cur, 2 * sL.core.cur_vars, sL.core.repr, FullReprRest c sL ⋆ R, hrepL,
    ha_lt_cv.1, focus_full_repr hmL, fun ra0 rp1 m1 hrl1 hrep1 _ hra0_lt ha_ra hm1 => ?_⟩
  let s1 : FullState := { sL with core := { sL.core with repr := rp1 } }
  have hinv1 := s13_denseInvW_set_repr hinvL (rp' := rp1) (by rw [hrl1, hrp_len])
  have hm1' : (FullMem c s1 ⋆ R) m1 := unfocus_full_repr hm1
  c0_hsteps_nogrp; c0_call hFind
  refine ⟨F_cur, 2 * s1.core.cur_vars, s1.core.repr, FullReprRest c s1 ⋆ R, hrep1,
    ha_lt_cv.2.1, focus_full_repr hm1', fun rb0 rp2 m2 hrl2 hrep2 _ hrb0_lt hb_rb hm2 => ?_⟩
  let s2 : FullState := { s1 with core := { s1.core with repr := rp2 } }
  have hinv2 := s13_denseInvW_set_repr hinv1 (rp' := rp2) (by rw [hrl2, hrl1, hrp_len])
  have hm2' : (FullMem c s2 ⋆ R) m2 := unfocus_full_repr hm2
  have hrab_eqv : LitEquiv (cnfOfClauses F_cur) ra0.toNat rb0.toNat :=
    ha_ra.symm.trans (ha_lt_cv.2.2.trans hb_rb)
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps!
    exact hJ s2 m2 hinv2 hcvL hflL hrep2 htmkL htrhL hscrL hws2L hguL hm2'
  c0_hsteps_nogrp
  c0_hsplit
  · have heq_neg : ra0 = rb0 ^^^ 1#32 := by assumption
    have huns : (cnfOfClauses F_cur).Unsat := by
      have hneg : LitEquiv (cnfOfClauses F_cur) rb0.toNat (litNeg rb0.toNat) := by
        unfold litNeg
        rw [← m6_els_bv32_xor1_toNat rb0]; exact (heq_neg ▸ hrab_eqv).symm
      exact unsat_of_litEquiv_neg hneg
    let s3 := { s2 with core := { s2.core with inconsistent := 1#64 } }
    c0_hsteps!
    exact hQ false s3 _ (s13_denseInvW_set_incons hinv2 huns) hcvL hflL hrep2 htmkL htrhL
      hscrL hws2L hguL (fun _ => ⟨hinv2.2.1.ext_sound.2 huns, by simp [s3]⟩)
      (by assumption)
  have hne_eq : ra0 ≠ rb0 := fun h => ‹ra0 ≠ rb0› h
  have hne_neg : ra0 ≠ rb0 ^^^ 1#32 := ‹_›
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i32, i32])
    (fun (ra, rb, ()) mj => mj = m2 ∧ ra.toNat < rb.toNat ∧ rb.toNat < 2 * s2.core.cur_vars ∧
      ra ≠ rb ^^^ 1#32 ∧ LitEquiv (cnfOfClauses F_cur) ra.toNat rb.toNat) ?_ ?_
  · rintro _ ⟨ra, rb, ⟨⟩⟩ mj ⟨hmj_eq, hlt_ab, hrb_lt, hne_n, heqv_ab⟩
    subst mj
    have hra_lt : ra.toNat < 2 * s2.core.cur_vars := by omega
    have hvl2 : s2.core.vals.length = 2 * c.max_vars := hvl_len
    have hcv2 : s2.core.cur_vars = sL.core.cur_vars := rfl
    have hra_vl : (ra.setWidth 64).toNat < s2.core.vals.length := by
      rw [bv_c0_zext32_64, hvl2]; omega
    have hrb_vl : (rb.setWidth 64).toNat < s2.core.vals.length := by
      rw [bv_c0_zext32_64, hvl2]; omega
    c0_hsteps_nogrp
    refine wp_join_group (ts := []) (fun () mK => mK = m2) ?_ ?_
    · rintro _ ⟨⟩ mK hmK; subst mK
      c0_hsteps_nogrp; c0_hsplit
      · c0_hsteps_nogrp
        refine wp_join_group (ts := [i32]) (fun (u, ()) mu => mu = m2 ∧
            u.toNat < 2 * s2.core.cur_vars ∧
            (cnfOfClauses F_cur).EntailsClause (cnfClause [u.toNat])) ?_ ?_
        · rintro _ ⟨u, ⟨⟩⟩ mu ⟨hmu, hu_lt, hu_ent⟩; subst mu
          c0_hsteps_nogrp; c0_call hAddUnit
          refine ⟨c, F0, F_cur, s2, R, rfl, hinv2.1, hinv2.2.1, fun _ => hu_ent, hm2', ?_⟩
          intro okU vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl'
            inc' phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' mU sU hlenU hwU
            hclU hfailU _ hmU
          have hinvU := s13_denseInvW_after_addUnit hinv2 hlenU hwU hclU
          c0_hsplit
          · c0_hsteps!
            exact hJ sU mU hinvU hcvL hflL hrep2 htmkL htrhL hscrL hws2L hguL hmU
          · have hokf : okU = false := by
              cases okU <;> first | rfl | contradiction | exact absurd rfl ‹_›
            c0_hsteps!
            exact hQ false sU mU hinvU hcvL hflL hrep2 htmkL htrhL hscrL hws2L hguL
              (fun _ => hfailU hu_lt hokf) hmU
        · intro Ju hJu
          c0_hsteps_nogrp; c0_hsplit
          · have hpos : (0#8 : BitVec 8).slt (s2.core.vals[ra.toNat]'(by rw [hvl2]; omega)) =
                true := ‹_›
            have hent_ra : (cnfOfClauses F_cur).EntailsClause (cnfClause [ra.toNat]) :=
              s13_entails_unit_of_pos_val hinv2.2.1 hinv2.2.2.2.2.2.1 hra_lt _ hpos
            c0_hsteps!
            exact hJu (rb, ()) m2 ⟨rfl, hrb_lt, s13_entails_clause_subst (cs := [ra.toNat])
              (fun _ hl => by simp at hl; subst hl; exact ⟨rb.toNat, by simp, heqv_ab⟩)
              hent_ra⟩
          · have hva_nz : s2.core.vals[ra.toNat]'(by rw [hvl2]; omega) ≠ 0#8 :=
              fun h => ‹¬ (s2.core.vals[ra.toNat]'(by rw [hvl2]; omega)).signExtend 32 = 0#32›
                (by simp [h])
            have hfa : (0#8 : BitVec 8).slt (s2.core.vals[ra.toNat]'(by rw [hvl2]; omega)) =
                false := ‹_›
            have hneg_va : ¬ (0#8 : BitVec 8).slt
                (s2.core.vals[ra.toNat]'(by rw [hvl2]; omega)) = true := by simp [hfa]
            have hent_nra : (cnfOfClauses F_cur).EntailsClause (cnfClause [ra.toNat ^^^ 1]) :=
              s13_entails_unit_of_neg_val hinv2.2.1 hinv2.2.2.2.2.2.1 hra_lt _ hva_nz hneg_va
            c0_hsteps!
            exact hJu (rb ^^^ 1#32, ()) m2 ⟨rfl,
              (by rw [m6_els_bv32_xor1_toNat]; exact s13_nat_xor1_lt hrb_lt),
              s13_entails_clause_subst (cs := [ra.toNat ^^^ 1])
                (fun _ hl => by
                  simp only [List.mem_singleton] at hl; subst hl
                  exact ⟨(rb ^^^ 1#32).toNat, by simp, by
                    rw [m6_els_bv32_xor1_toNat]; exact m6_litEquiv_neg heqv_ab⟩)
                hent_nra⟩
      · c0_hsteps_nogrp; c0_hsplit
        · c0_hsteps_nogrp
          refine wp_join_group (ts := [i32]) (fun (u, ()) mu => mu = m2 ∧
              u.toNat < 2 * s2.core.cur_vars ∧
              (cnfOfClauses F_cur).EntailsClause (cnfClause [u.toNat])) ?_ ?_
          · rintro _ ⟨u, ⟨⟩⟩ mu ⟨hmu, hu_lt, hu_ent⟩; subst mu
            c0_hsteps_nogrp; c0_call hAddUnit
            refine ⟨c, F0, F_cur, s2, R, rfl, hinv2.1, hinv2.2.1, fun _ => hu_ent, hm2', ?_⟩
            intro okU vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl'
              inc' phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' mU sU hlenU hwU
              hclU hfailU _ hmU
            have hinvU := s13_denseInvW_after_addUnit hinv2 hlenU hwU hclU
            c0_hsplit
            · c0_hsteps!
              exact hJ sU mU hinvU hcvL hflL hrep2 htmkL htrhL hscrL hws2L hguL hmU
            · have hokf : okU = false := by
                cases okU <;> first | rfl | contradiction | exact absurd rfl ‹_›
              c0_hsteps!
              exact hQ false sU mU hinvU hcvL hflL hrep2 htmkL htrhL hscrL hws2L hguL
                (fun _ => hfailU hu_lt hokf) hmU
          · intro Ju hJu
            c0_hsteps_nogrp; c0_hsplit
            · have hpos : (0#8 : BitVec 8).slt (s2.core.vals[rb.toNat]'(by rw [hvl2]; omega)) =
                  true := ‹_›
              have hent_rb : (cnfOfClauses F_cur).EntailsClause (cnfClause [rb.toNat]) :=
                s13_entails_unit_of_pos_val hinv2.2.1 hinv2.2.2.2.2.2.1 hrb_lt _ hpos
              c0_hsteps!
              exact hJu (ra, ()) m2 ⟨rfl, hra_lt, s13_entails_clause_subst (cs := [rb.toNat])
                (fun _ hl => by simp at hl; subst hl; exact ⟨ra.toNat, by simp, heqv_ab.symm⟩)
                hent_rb⟩
            · have hvb_nz : s2.core.vals[rb.toNat]'(by rw [hvl2]; omega) ≠ 0#8 :=
                fun h => ‹¬ (s2.core.vals[rb.toNat]'(by rw [hvl2]; omega)).signExtend 32 = 0#32›
                  (by simp [h])
              have hfb : (0#8 : BitVec 8).slt (s2.core.vals[rb.toNat]'(by rw [hvl2]; omega)) =
                  false := ‹_›
              have hneg_vb : ¬ (0#8 : BitVec 8).slt
                  (s2.core.vals[rb.toNat]'(by rw [hvl2]; omega)) = true := by simp [hfb]
              have hent_nrb : (cnfOfClauses F_cur).EntailsClause (cnfClause [rb.toNat ^^^ 1]) :=
                s13_entails_unit_of_neg_val hinv2.2.1 hinv2.2.2.2.2.2.1 hrb_lt _ hvb_nz hneg_vb
              c0_hsteps!
              exact hJu (ra ^^^ 1#32, ()) m2 ⟨rfl,
                (by rw [m6_els_bv32_xor1_toNat]; exact s13_nat_xor1_lt hra_lt),
                s13_entails_clause_subst (cs := [rb.toNat ^^^ 1])
                  (fun _ hl => by
                    simp only [List.mem_singleton] at hl; subst hl
                    exact ⟨(ra ^^^ 1#32).toNat, by simp, by
                      rw [m6_els_bv32_xor1_toNat]; exact m6_litEquiv_neg heqv_ab.symm⟩)
                  hent_nrb⟩
        · have hra_fl : (ra >>> 1#32).toNat < s2.core.flags.length := by
            rw [hfl_len, show ra >>> 1#32 = ra >>> (1 : Nat) from rfl,
              BitVec.toNat_ushiftRight]; omega
          c0_hsteps_nogrp; c0_hsplit
          · c0_hsteps!
            exact hJ s2 m2 hinv2 hcvL hflL hrep2 htmkL htrhL hscrL hws2L hguL hm2'
          have hrb_fl : (rb >>> 1#32).toNat < s2.core.flags.length := by
            rw [hfl_len, show rb >>> 1#32 = rb >>> (1 : Nat) from rfl,
              BitVec.toNat_ushiftRight]; omega
          c0_hsteps_nogrp; c0_hsplit
          · c0_hsteps!
            exact hJ s2 m2 hinv2 hcvL hflL hrep2 htmkL htrhL hscrL hws2L hguL hm2'
          have hrb_rp : rb.toNat < s2.core.repr.length := by
            show rb.toNat < rp2.length; rw [hrl2, hrl1, hrp_len]; omega
          have hrb1_rp : (rb ^^^ 1#32).toNat < s2.core.repr.length := by
            show (rb ^^^ 1#32).toNat < rp2.length
            rw [hrl2, hrl1, hrp_len, m6_els_bv32_xor1_toNat]
            have := s13_nat_xor1_lt hrb_lt; omega
          let rp3 := (rp2.set rb.toNat ra).set (rb ^^^ 1#32).toNat (ra ^^^ 1#32)
          let fl3 := s2.core.flags.set (rb >>> 1#32).toNat
            (s2.core.flags[(rb >>> 1#32).toNat]'hrb_fl &&&
              ~~~((1024#32 ||| 1073741824#32) ||| 536870912#32))
          let s3 : FullState :=
            { core := { s2.core with repr := rp3, flags := fl3 }
              scratch := { s2.scratch with sweep_cnt := s2.scratch.sweep_cnt + 1#64 } }
          have hrep3 : FullCongReprInv F_cur (2 * s3.core.cur_vars) s3.core.repr :=
            s13_fullCongReprInv_union hrep2 hra_lt hrb_lt
              (by rw [m6_els_bv32_xor1_toNat]; exact s13_nat_xor1_lt hrb_lt)
              hlt_ab hne_n heqv_ab
          have hinv3 : FullDenseInvW c F0 F_cur s3 :=
            s13_denseInvW_inc_sweep (FullFidelitySweep.fid_denseInvW_set_flags
              (s13_denseInvW_set_repr (rp' := rp3) hinv2
                (by simp only [rp3, List.length_set, hrl2]; exact hrl1.trans hrp_len))
              (flags' := fl3) (by simp only [fl3, List.length_set]; exact hfl_len)) _
          c0_hsteps_nogrp
          c0_call hElsLit
          refine ⟨c, F0, F_cur, s3, R, rfl, hinv3, hrb_lt, hra_lt, heqv_ab.symm, hrep3,
            (by assumption), ?_⟩
          intro okE1 s4 m4 hinv4 hcv4 hfl4 hrep4 htmk4 htrh4 hscr4 _ hws2_4 hgu4 hfail4 hm4
          c0_hsplit
          · have hrb1_lt : (rb ^^^ 1#32).toNat < 2 * s4.core.cur_vars := by
              rw [hcv4, m6_els_bv32_xor1_toNat]; exact s13_nat_xor1_lt hrb_lt
            have hra1_lt : (ra ^^^ 1#32).toNat < 2 * s4.core.cur_vars := by
              rw [hcv4, m6_els_bv32_xor1_toNat]; exact s13_nat_xor1_lt hra_lt
            have heqv1 : LitEquiv (cnfOfClauses F_cur) (rb ^^^ 1#32).toNat (ra ^^^ 1#32).toNat := by
              rw [m6_els_bv32_xor1_toNat, m6_els_bv32_xor1_toNat]
              exact m6_litEquiv_neg heqv_ab.symm
            c0_hsteps_nogrp; c0_call hElsLit
            refine ⟨c, F0, F_cur, s4, R, rfl, hinv4, hrb1_lt, hra1_lt, heqv1,
              (by simpa [hcv4] using hrep4), hm4, ?_⟩
            intro okE2 s5 m5 hinv5 hcv5 hfl5 hrep5 htmk5 htrh5 hscr5 _ hws2_5 hgu5 hfail5 hm5
            c0_hsplit
            · have hrp5_c : FullCongReprInv F_cur (2 * s5.core.cur_vars) s5.core.repr := by
                simpa [hcv5] using hrep5
              have hrb0_lt5 : (rb ||| 0#32).toNat < 2 * s5.core.cur_vars := by
                simpa [hcv5, hcv4] using hrb_lt
              have hra1_lt5 : (ra ^^^ 1#32).toNat < 2 * s5.core.cur_vars := by
                simpa [hcv5] using hra1_lt
              have hent_b1 : (cnfOfClauses F_cur).EntailsClause
                  (cnfClause [(rb ||| 0#32).toNat, (ra ^^^ 1#32).toNat]) := by
                have he0 : LitEquiv (cnfOfClauses F_cur) (rb ||| 0#32).toNat ra.toNat := by
                  simpa using heqv_ab.symm
                rw [m6_els_bv32_xor1_toNat]
                exact (s13_litEquiv_neg_taut he0).1
              c0_hsteps_nogrp; c0_call hAddBin
              refine ⟨c, F0, F_cur, s5, R, rfl, hinv5.1, hinv5.2.1, hinv5.2.2.2.2.2.1,
                fun _ _ => hent_b1, hm5, ?_⟩
              intro ab1 vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen'
                wu' nb' oom' inc' phases' wsort' m6 s6 hlen6 hw6 _ hab1_20 _ hm6
              have hinv6 := s13_denseInvW_after_addBin hinv5 hlen6 hw6
              c0_hsplit
              · have hab : ab1 = 20#64 := by bv_omega
                c0_hsteps!
                exact hQ false s6 m6 hinv6 (hcv5.trans (hcv4.trans hcvL))
                  (hfl5.trans (hfl4.trans hflL))
                  (by simpa [s6] using hrp5_c) (htmk5.trans (htmk4.trans htmkL))
                  (htrh5.trans (htrh4.trans htrhL))
                  (hscr5.trans (hscr4.trans hscrL)) (hws2_5.trans (hws2_4.trans hws2L))
                  (hgu5.trans (hgu4.trans hguL)) (fun _ => hab1_20 hab) hm6
              c0_hsplit
              · let s6o : FullState := { s6 with core := { s6.core with oom := 1#64 } }
                c0_hsteps!
                exact hQ true s6o _ (s13_denseInvW_set_oom hinv6)
                  (hcv5.trans (hcv4.trans hcvL)) (hfl5.trans (hfl4.trans hflL))
                  (by simpa [s6o, s6] using hrp5_c) (htmk5.trans (htmk4.trans htmkL))
                  (htrh5.trans (htrh4.trans htrhL))
                  (hscr5.trans (hscr4.trans hscrL)) (hws2_5.trans (hws2_4.trans hws2L))
                  (hgu5.trans (hgu4.trans hguL)) (fun h => Bool.noConfusion h)
                  (by assumption)
              · have hent_b2 : (cnfOfClauses F_cur).EntailsClause
                    (cnfClause [(rb ^^^ 1#32).toNat, ra.toNat]) := by
                  rw [m6_els_bv32_xor1_toNat]; exact (s13_litEquiv_neg_taut heqv_ab.symm).2
                c0_hsteps_nogrp; c0_call hAddBin
                refine ⟨c, F0, F_cur, s6, R, rfl, hinv6.1, hinv6.2.1, hinv6.2.2.2.2.2.1,
                  fun _ _ => hent_b2, hm6, ?_⟩
                intro ab2 vals2 flags2 lvl2 rsns2 trl2 tp2 te2 unass2 unfl2 wvec2 wstk2
                  wlen2 wu2 nb2 oom2 inc2 phases2 wsort2 m7 s7 hlen7 hw7 _ hab2_20 _ hm7
                have hinv7 := s13_denseInvW_after_addBin hinv6 hlen7 hw7
                c0_hsplit
                · have hab : ab2 = 20#64 := by bv_omega
                  c0_hsteps!
                  exact hQ false s7 m7 hinv7 (hcv5.trans (hcv4.trans hcvL))
                    (hfl5.trans (hfl4.trans hflL))
                    (by simpa [s7, s6] using hrp5_c) (htmk5.trans (htmk4.trans htmkL))
                    (htrh5.trans (htrh4.trans htrhL))
                    (hscr5.trans (hscr4.trans hscrL)) (hws2_5.trans (hws2_4.trans hws2L))
                    (hgu5.trans (hgu4.trans hguL)) (fun _ => hab2_20 hab) hm7
                c0_hsplit
                · let s7o : FullState := { s7 with core := { s7.core with oom := 1#64 } }
                  c0_hsteps!
                  exact hQ true s7o _ (s13_denseInvW_set_oom hinv7)
                    (hcv5.trans (hcv4.trans hcvL))
                    (hfl5.trans (hfl4.trans hflL))
                    (by simpa [s7o, s7, s6] using hrp5_c) (htmk5.trans (htmk4.trans htmkL))
                    (htrh5.trans (htrh4.trans htrhL))
                    (hscr5.trans (hscr4.trans hscrL)) (hws2_5.trans (hws2_4.trans hws2L))
                    (hgu5.trans (hgu4.trans hguL)) (fun h => Bool.noConfusion h)
                    (by assumption)
                · c0_hsteps!
                  exact hJ s7 m7 hinv7 (hcv5.trans (hcv4.trans hcvL))
                    (hfl5.trans (hfl4.trans hflL))
                    (by simpa [s7, s6] using hrp5_c) (htmk5.trans (htmk4.trans htmkL))
                    (htrh5.trans (htrh4.trans htrhL))
                    (hscr5.trans (hscr4.trans hscrL)) (hws2_5.trans (hws2_4.trans hws2L))
                    (hgu5.trans (hgu4.trans hguL)) hm7
            · have hokf : okE2 = false := by
                cases okE2 <;> first | rfl | contradiction | exact absurd rfl ‹_›
              c0_hsteps!
              exact hQ false s5 m5 hinv5 (hcv5.trans (hcv4.trans hcvL))
                (hfl5.trans (hfl4.trans hflL)) (by simpa only [hcv5] using hrep5)
                (htmk5.trans (htmk4.trans htmkL)) (htrh5.trans (htrh4.trans htrhL))
                (hscr5.trans (hscr4.trans hscrL)) (hws2_5.trans (hws2_4.trans hws2L))
                (hgu5.trans (hgu4.trans hguL)) (fun _ => hfail5 hokf) hm5
          · have hokf : okE1 = false := by
              cases okE1 <;> first | rfl | contradiction | exact absurd rfl ‹_›
            c0_hsteps!
            exact hQ false s4 m4 hinv4 (hcv4.trans hcvL) (hfl4.trans hflL)
              (by simpa only [hcv4] using hrep4) (htmk4.trans htmkL) (htrh4.trans htrhL)
              (hscr4.trans hscrL) (hws2_4.trans hws2L) (hgu4.trans hguL)
              (fun _ => hfail4 hokf) hm4
    · intro Js3 hJs3
      c0_hsteps_nogrp; c0_hsplit
      · c0_hsteps_nogrp; c0_hsplit
        · c0_hsteps_nogrp; c0_hsplit
          · have hva_nz : s2.core.vals[ra.toNat]'(by rw [hvl2]; omega) ≠ 0#8 := by
              have hca : (s2.core.vals[(ra.setWidth 64).toNat]'(by
                  rw [bv_c0_zext32_64, hvl2]; omega)).signExtend 32 ≠ 0#32 := by assumption
              simp only [bv_c0_zext32_64] at hca
              exact fun h => hca ((s13_bv8_sext32_eq0_iff _).mpr h)
            have hvb_nz : s2.core.vals[rb.toNat]'(by rw [hvl2]; omega) ≠ 0#8 := by
              have hcb : (s2.core.vals[(rb.setWidth 64).toNat]'(by
                  rw [bv_c0_zext32_64, hvl2]; omega)).signExtend 32 ≠ 0#32 := by assumption
              simp only [bv_c0_zext32_64] at hcb
              exact fun h => hcb ((s13_bv8_sext32_eq0_iff _).mpr h)
            have hcn : (s2.core.vals[(ra.setWidth 64).toNat]'(by
                  rw [bv_c0_zext32_64, hvl2]; omega)).signExtend 32 ≠
                (s2.core.vals[(rb.setWidth 64).toNat]'(by
                  rw [bv_c0_zext32_64, hvl2]; omega)).signExtend 32 := by assumption
            simp only [bv_c0_zext32_64] at hcn
            have hval_ne : s2.core.vals[ra.toNat]'(by rw [hvl2]; omega) ≠
                s2.core.vals[rb.toNat]'(by rw [hvl2]; omega) := fun heq =>
              hcn (congrArg (BitVec.signExtend 32) heq)
            have hdom_a : s2.core.vals[ra.toNat]'(by rw [hvl2]; omega) = 1#8 ∨
                s2.core.vals[ra.toNat]'(by rw [hvl2]; omega) = 0xFF#8 := by
              rcases hinv2.2.1.vals_domain ra.toNat hra_lt with h0 | h1 | h2
              · rw [List.getElem?_eq_getElem (by rw [hvl2]; omega), Option.getD_some] at h0
                exact absurd h0 hva_nz
              · rw [List.getElem?_eq_getElem (by rw [hvl2]; omega), Option.getD_some] at h1
                exact Or.inl h1
              · rw [List.getElem?_eq_getElem (by rw [hvl2]; omega), Option.getD_some] at h2
                exact Or.inr h2
            have hdom_b : s2.core.vals[rb.toNat]'(by rw [hvl2]; omega) = 1#8 ∨
                s2.core.vals[rb.toNat]'(by rw [hvl2]; omega) = 0xFF#8 := by
              rcases hinv2.2.1.vals_domain rb.toNat hrb_lt with h0 | h1 | h2
              · rw [List.getElem?_eq_getElem (by rw [hvl2]; omega), Option.getD_some] at h0
                exact absurd h0 hvb_nz
              · rw [List.getElem?_eq_getElem (by rw [hvl2]; omega), Option.getD_some] at h1
                exact Or.inl h1
              · rw [List.getElem?_eq_getElem (by rw [hvl2]; omega), Option.getD_some] at h2
                exact Or.inr h2
            have hcl0_2 : s2.core.cur_level = 0 := hinv2.2.2.2.2.2.1
            have huns : (cnfOfClauses F_cur).Unsat := by
              rcases hdom_a with ha1 | haf <;> rcases hdom_b with hb1 | hbf
              · exact absurd (ha1.trans hb1.symm) hval_ne
              · exact m6_litEquiv_unsat_contra heqv_ab
                  (m6_lvl0_true_entails hinv2.2.1 hcl0_2 hra_lt (by
                    rw [List.getElem?_eq_getElem (by rw [hvl2]; omega), Option.getD_some]
                    exact ha1))
                  (m6_lvl0_false_entails hinv2.2.1 hcl0_2 hrb_lt (by
                    rw [List.getElem?_eq_getElem (by rw [hvl2]; omega), Option.getD_some]
                    exact hbf))
              · exact m6_litEquiv_unsat_contra heqv_ab.symm
                  (m6_lvl0_true_entails hinv2.2.1 hcl0_2 hrb_lt (by
                    rw [List.getElem?_eq_getElem (by rw [hvl2]; omega), Option.getD_some]
                    exact hb1))
                  (m6_lvl0_false_entails hinv2.2.1 hcl0_2 hra_lt (by
                    rw [List.getElem?_eq_getElem (by rw [hvl2]; omega), Option.getD_some]
                    exact haf))
              · exact absurd (haf.trans hbf.symm) hval_ne
            let s3 := { s2 with core := { s2.core with inconsistent := 1#64 } }
            c0_hsteps!
            exact hQ false s3 _ (s13_denseInvW_set_incons hinv2 huns) hcvL hflL hrep2 htmkL htrhL
              hscrL hws2L hguL (fun _ => ⟨hinv2.2.1.ext_sound.2 huns, by simp [s3]⟩)
              (by assumption)
          · c0_hsteps!
            exact hJ s2 m2 hinv2 hcvL hflL hrep2 htmkL htrhL hscrL hws2L hguL hm2'
        · c0_hsteps!; exact hJs3 () m2 rfl
      · c0_hsteps!; exact hJs3 () m2 rfl
  · intro Js hJs
    c0_hsteps_nogrp; c0_hsplit
    · have hne_n : rb0 ≠ ra0 ^^^ 1#32 := fun h => hne_neg (by
        rw [h, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero])
      c0_hsteps!
      exact hJs (rb0, ra0, ()) m2 ⟨rfl, ‹_›, hra0_lt, hne_n, hrab_eqv.symm⟩
    · have hne_ab : ra0.toNat ≠ rb0.toNat := fun h => hne_eq (BitVec.eq_of_toNat_eq h)
      have hlt_ba : ra0.toNat < rb0.toNat := by
        have hnl : ¬ rb0.toNat < ra0.toNat := ‹_›; omega
      c0_hsteps!
      exact hJs (ra0, rb0, ()) m2 ⟨rfl, hlt_ba, hrb0_lt, hne_neg, hrab_eqv⟩

/-! ## 3. Main Theorem (`full_m6_dense_els_s13_wp`) -/

/-- Step-13 `full_m6_dense_els` (`FullCongReprInv` + incremental eager ELS). -/
theorem full_m6_dense_els_s13_wp (Γ : Env)
    (hFind : ∀ a m Q X, Full.fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hAddUnit : M6EnvSpec Γ "full_add_unit" Full.fullAddUnitSpec)
    (hElsLit : ∀ a m Q X, step13ElsLitSpec a m Q X →
      Γ "full_m6_els_lit" [i64, i32, i32] [.bool] a m Q X)
    (hAddBin : M6EnvSpec Γ "full_add_bin" Full.fullAddBinSpec)
    (hProp : ∀ a m Q X, step13DensePropSpec a m Q X →
      Γ "full_m6_dense_prop" [i64] [.bool] a m Q X) :
    ∀ args m Q X, step13DenseElsSpec args m Q X →
      Func.wp Γ full_m6_dense_els_body args m Q X := by
  rintro ⟨h, neq, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinv, heqb, hrep, hm, hQ⟩
  unfold Func.wp full_m6_dense_els_body
  c0_hsteps_nogrp
  refine wp_join_group (ts := []) (fun () m_e =>
      (neq = 0#32 ∨ s.core.inconsistent ≠ 0#64) ∧ (FullMem c s ⋆ R) m_e) ?_ ?_
  · rintro _ ⟨⟩ m_e ⟨_, hm_e⟩
    c0_hsteps!; exact s13_dense_els_exit_ret hinv rfl rfl hrep rfl rfl rfl rfl rfl hm_e hQ
  · intro J_e hJ_e
    c0_hsplit
    · c0_hsteps!; exact hJ_e () m ⟨Or.inl ‹_›, hm⟩
    c0_hsplit
    · c0_hsteps!; exact hJ_e () m ⟨Or.inr ‹_›, hm⟩
    have hneq_nz : neq ≠ 0#32 := ‹_›
    have hinc_z : s.core.inconsistent = 0#64 := ‹_›
    c0_hsteps_nogrp
    refine wp_while_state (ts := [i64]) (proj := fun ei : BitVec 64 => (ei, ()))
      (μ := fun ei => neq.toNat - ei.toNat)
      (Inv := fun ei ml => ei.toNat ≤ neq.toNat ∧ ∃ sL : FullState,
        FullDenseInvW c F0 F_cur sL ∧ sL.core.cur_vars = s.core.cur_vars ∧
        sL.core.fuel = s.core.fuel ∧ FullCongReprInv F_cur (2 * sL.core.cur_vars) sL.core.repr ∧
        sL.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
        sL.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
        sL.scratch.scratch_buf = s.scratch.scratch_buf ∧
        sL.scratch.work_stk2 = s.scratch.work_stk2 ∧
        sL.scratch.glue_used = s.scratch.glue_used ∧ (FullMem c sL ⋆ R) ml) ?_ ?_
    · intro J hJ; c0_hsteps!; exact hJ 0#64 m ⟨Nat.zero_le _, s, hinv, rfl, rfl, hrep, rfl, rfl,
        rfl, rfl, rfl, hm⟩
    · rintro J eiL ml ⟨hei_le, sL, hinvL, hcvL, hflL, hrepL, htmkL, htrhL, hscrL, hws2L, hguL,
        hmL⟩ ih
      c0_hsteps_nogrp
      refine wp_join_group (ts := []) (fun () mE => ∃ sE : FullState,
          FullDenseInvW c F0 F_cur sE ∧ sE.core.cur_vars = s.core.cur_vars ∧
          sE.core.fuel = s.core.fuel ∧ FullCongReprInv F_cur (2 * sE.core.cur_vars) sE.core.repr ∧
          sE.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
          sE.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
          sE.scratch.scratch_buf = s.scratch.scratch_buf ∧
          sE.scratch.work_stk2 = s.scratch.work_stk2 ∧
          sE.scratch.glue_used = s.scratch.glue_used ∧ (FullMem c sE ⋆ R) mE) ?_ ?_
      · rintro _ ⟨⟩ mE ⟨sE, hinvE, hcvE, hflE, hrepE, htmkE, htrhE, hscrE, hws2E, hguE, hmE⟩
        c0_hsteps_nogrp
        c0_hsplit
        · have hinc_nz : sE.core.inconsistent ≠ 0#64 := ‹_›
          have huns : F0.Unsat := hinvE.2.1.ext_sound.2 (hinvE.2.1.inconsistent_sound hinc_nz)
          c0_hsteps!
          exact hQ false sE mE hinvE hcvE hflE hrepE htmkE htrhE hscrE hws2E hguE
            (fun _ => ⟨huns, hinc_nz⟩) hmE
        · c0_hsteps_nogrp; c0_call hProp
          refine ⟨c, F0, F_cur, sE, R, rfl, hinvE, hmE, ?_⟩
          intro okP sP mP hinvP hcvP hflP hrpP _ _ htmkP htrhP hscrP _ hws2_P hguP _hinc_iff
            hfailP hmP
          have hrpP_c : FullCongReprInv F_cur (2 * sP.core.cur_vars) sP.core.repr := by
            rw [hrpP, hcvP]; exact hrepE
          c0_hsteps!
          exact hQ okP sP mP hinvP (hcvP.trans hcvE) (hflP.trans hflE) hrpP_c
            (htmkP.trans htmkE) (htrhP.trans htrhE) (hscrP.trans hscrE)
            (hws2_P.trans hws2E) (hguP.trans hguE) hfailP hmP
      · intro Jex hJex
        c0_hsplit
        · have hei_lt : eiL.toNat < neq.toNat := by
            have := ‹eiL.toNat < (BitVec.setWidth 64 neq).toNat›
            rwa [bv_c0_zext32_64] at this
          have hcvL_64 : sL.core.cur_vars < 2 ^ 64 := by
            have := hinvL.1.core_ok.cur_vars_le; have hmx := c.hmaxv; unfold dimacsBound at hmx
            omega
          have hneq_bd : neq.toNat < 2 ^ 32 := neq.isLt
          have hws2_len : sL.scratch.work_stk2.length = 2 * c.max_vars :=
            hinvL.1.scratch_ok.work_stk2_len
          have hcur_le : sL.core.cur_vars ≤ c.max_vars := hinvL.1.core_ok.cur_vars_le
          have heq_le : neq.toNat ≤ s.core.cur_vars := heqb.1
          have he0_bd : (eiL <<< 1#64).toNat < sL.scratch.work_stk2.length := by
            have hmx := c.hmaxv; unfold dimacsBound at hmx
            rw [hws2_len, show eiL <<< 1#64 = eiL <<< (1 : Nat) from rfl]; bv_omega
          have he1_bd : ((eiL <<< 1#64) + 1#64).toNat < sL.scratch.work_stk2.length := by
            have hmx := c.hmaxv; unfold dimacsBound at hmx
            rw [hws2_len, show eiL <<< 1#64 = eiL <<< (1 : Nat) from rfl]; bv_omega
          c0_hsteps_nogrp; c0_hsplit
          · c0_hsteps_nogrp; c0_hsplit
            · have hei1 : (eiL + 1#64).toNat = eiL.toNat + 1 := by
                have := heqb.1; have hmx := c.hmaxv; unfold dimacsBound at hmx
                have := hinvL.1.core_ok.cur_vars_le; bv_omega
              have hinc0 : sL.core.inconsistent = 0#64 := ‹_›
              c0_hsteps_nogrp
              have hstep := s13_dense_els_step_wp (X := X) hFind hAddUnit hElsLit hAddBin hinvL
                hcvL hflL hrepL htmkL htrhL hscrL hws2L hguL heqb neq.isLt hei_lt hei1 hinc0 hmL
                (fun s' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 hm' =>
                  ih (eiL + 1#64) m' (by rw [hei1]; omega) ⟨by rw [hei1]; omega, s', h1, h2, h3,
                    h4, h5, h6, h7, h8, h9, hm'⟩) hQ
              dsimp only [s13DenseElsStepExpr] at hstep
              have hcv_nl : BitVec.ofNat 64 sL.core.cur_vars <<< 1#64 =
                  BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat) := by rw [hcvL]; rfl
              have hei_shl : eiL <<< 1#64 = eiL <<< (1 : Nat) := rfl
              rw [List.getElem?_eq_getElem he0_bd, Option.getD_some,
                List.getElem?_eq_getElem he1_bd, Option.getD_some, hcv_nl] at hstep
              simp only [hei_shl] at hstep
              exact hstep
            · c0_hsteps!; exact hJex () ml ⟨sL, hinvL, hcvL, hflL, hrepL, htmkL, htrhL, hscrL,
                hws2L, hguL, hmL⟩
          · c0_hsteps!; exact hJex () ml ⟨sL, hinvL, hcvL, hflL, hrepL, htmkL, htrhL, hscrL,
              hws2L, hguL, hmL⟩
        · c0_hsteps!; exact hJex () ml ⟨sL, hinvL, hcvL, hflL, hrepL, htmkL, htrhL, hscrL,
            hws2L, hguL, hmL⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1
