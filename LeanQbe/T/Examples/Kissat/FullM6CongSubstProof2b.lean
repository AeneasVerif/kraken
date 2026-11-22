module

public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof2a
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Kissat M6 Congruence Closure & 2-Round Substitute Proofs — Part 2b

Builds on `FullM6CongSubstProof2a` (`M6EvalGateOk`, `M6HashGateOk`, `ev_*` helpers, `and_match`,
`xor_match`, `enq_var`) to provide `M6bHeadTactics` (`m3HeadLoop`-based fast tactics that never
skip explicit `J*` join continuations), pure gate-evaluation branch helpers, and fold/enqueue
macros for `FullM6CongSubstProof2b2` (`full_cong_eval_gate_wp`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6CongSubst

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open Kraken.Bedrock2.Test

/-! ## 1. `m3HeadLoop`-Based Head Tactics & Eval-Gate Macros (`M6bHeadTactics`) -/

namespace M6bHeadTactics
open Lean Meta Elab Tactic

/-- `O(1)` head-step loop stopping cleanly on `J*` join hypotheses and unrolling inline groups. -/
scoped elab "m6b_steps" : tactic =>
  FullM3CongBva.M3HeadTactics.m3HeadLoop
    { unrollGroup := true, splitJnz := false, strictMem := true } 10000

/-- Non-unrolling `O(1)` head-step loop stopping before `Expr.group`, `Expr.jnz`, and `J*`. -/
scoped elab "m6b_to_group" : tactic =>
  FullM3CongBva.M3HeadTactics.m3HeadLoop
    { unrollGroup := false, splitJnz := false, strictMem := false } 10000

/-- Step only `let_`/`jump`/`ret`/`exit` and `Func.wp`/variant goals without touching `J*`. -/
scoped elab "m6b_let" : tactic => do
  focus do
    FullM3CongBva.M3HeadTactics.m3LetLoop 200
    FullM3CongBva.M3HeadTactics.m3NormWpHead

/-- Fast non-unrolling `jnz` splitter (`unrollGroup := false`, no `c0_bound` on live arms). -/
scoped elab "m6b_split" : tactic => do
  focus do
    FullM3CongBva.M3HeadTactics.m3HeadLoop
      { unrollGroup := false, splitJnz := false, strictMem := false } 2000
    let g ← getMainGoal
    let ty ← instantiateMVars (← g.getType)
    if ty.isAppOfArity ``LeanQbe.T.wp 6 then
      let e := (ty.getArg! 4).consumeMData
      if e.isAppOfArity ``LeanQbe.T.Expr.jnz 6 then
        let c0 := (e.getArg! 3).consumeMData
        if c0.isAppOf ``LeanQbe.T.Arg.var && c0.getAppNumArgs ≥ 2 then
          let inner0 := c0.appArg!
          let inner := FullM3CongBva.M3HeadTactics.m3PeelBlocks inner0
          if inner != inner0 then
            let cArg := Lean.mkAppN c0.getAppFn
              (c0.getAppArgs.set! (c0.getAppNumArgs - 1) inner)
            let e' := Lean.mkAppN e.getAppFn (e.getAppArgs.set! 3 cArg)
            let g' ← g.change (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e'))
              (checkDefEq := false)
            setGoals [g']
        else
          let cArg ← whnf c0
          let e' := Lean.mkAppN e.getAppFn (e.getAppArgs.set! 3 cArg)
          let g' ← g.change (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e'))
            (checkDefEq := false)
          setGoals [g']
    let hcId := Lean.mkIdent `hc
    let tac1 ← `(tactic| refine Full.FullCongTactics.wp_jnz_var (fun $hcId => ?_)
      (fun $hcId => ?_))
    let tac2 ← `(tactic| refine C0HeadStep.head_wp_jnz rfl (fun $hcId => ?_)
      (fun $hcId => ?_))
    evalTactic tac1 <|> evalTactic tac2

/-- Fast call discharge reducing only `vals`/`Arg.val` arguments. -/
scoped macro "m6b_call " h:ident : tactic =>
  `(tactic| (
    refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_)
    try simp only [LeanQbe.T.vals_nil, LeanQbe.T.vals_cons,
      LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]))

end M6bHeadTactics

open scoped M6bHeadTactics

/-! ## 2. Pure Gate-Evaluation, BitVec, List, Folding & Enqueue Helpers -/

section EvalGateHelpers

theorem bv32_add1_lt_of {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

theorem bv32_add2_lt_of {x : BitVec 32} (h : x.toNat + 2 < 2 ^ 32) :
    (x + 2#32).toNat = x.toNat + 2 := by
  rw [BitVec.toNat_add, show (2#32 : BitVec 32).toNat = 2 from rfl, Nat.mod_eq_of_lt h]

theorem bv32_ule_not_le {a b : BitVec 32} (h : a.ule b = false) :
    b.toNat < a.toNat := by
  simp only [BitVec.ule, decide_eq_false_iff_not] at h; omega

theorem list_drop_take_succ {α : Type _} (l : List α) {i k : Nat} (hi : i < l.length) :
    (l.drop i).take (k + 1) = l[i]'hi :: (l.drop (i + 1)).take k := by
  induction l generalizing i k with
  | nil => simp at hi
  | cons a t ih =>
    cases i with
    | zero => simp
    | succ i' =>
      simp only [List.drop_succ_cons, List.getElem_cons_succ]
      exact ih (by simp at hi; omega)

theorem xor1_bit01_eval {α : Nat → Bool} {l b : BitVec 32}
    (hb : b = 0#32 ∨ b = 1#32) :
    evalLitVal α (l ^^^ b).toNat = ((b == 1#32) != evalLitVal α l.toNat) := by
  rcases hb with rfl | rfl
  · simp
  · rw [bv32_xor1_eq_litNeg, evalLitVal_litNeg]; cases evalLitVal α l.toNat <;> rfl

theorem xor1_bit01_lt {l b : BitVec 32} {n : Nat} (hl : l.toNat < 2 * n)
    (hb : b = 0#32 ∨ b = 1#32) : (l ^^^ b).toNat < 2 * n := by
  rcases hb with rfl | rfl
  · simpa using hl
  · rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hl

theorem ev_tag0_clash_lhs_entails {F_cur : List (List Nat)} {lhs0 lhs : BitVec 32}
    {rhs : List Nat} {tmps raw : List (BitVec 32)} {na_n ar_n : Nat}
    (hand0 : AndGateDef (cnfOfClauses F_cur) lhs0.toNat rhs)
    (hlhs_eqv : LitEquiv (cnfOfClauses F_cur) lhs0.toNat lhs.toNat)
    (hsub_s : ∀ j < na_n, ∃ k < ar_n, tmps[j]? = raw[k]?)
    (hrhs_of_raw : ∀ k < ar_n, ∃ x ∈ rhs,
      LitEquiv (cnfOfClauses F_cur) x (raw[k]?.getD 0#32).toNat)
    (hraw_len : raw.length = ar_n) (_hna_s : na_n ≤ tmps.length)
    (hmem : litNeg lhs.toNat ∈ (tmps.take na_n).map BitVec.toNat) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg lhs.toNat]) := by
  rw [List.mem_map] at hmem; obtain ⟨b, hb, hbn⟩ := hmem
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hb
  rw [List.length_take] at hj; rw [List.getElem_take] at hget
  obtain ⟨k, hk, hraw_j⟩ := hsub_s j (by omega)
  obtain ⟨x, hx, heqv⟩ := hrhs_of_raw k hk
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hraw_j
  have hraw_j' := Option.some.inj hraw_j
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hraw_j', hget] at heqv
  refine entails_of_eval_mem fun α hα => ⟨litNeg lhs.toNat, List.mem_cons_self .., ?_⟩
  by_cases hneg : evalLitVal α (litNeg lhs.toNat) = true
  · exact hneg
  · have hnl : evalLitVal α (litNeg lhs.toNat) = false := Bool.eq_false_iff.mpr hneg
    have hlt : evalLitVal α lhs.toNat = true := by
      rw [evalLitVal_litNeg] at hnl; simpa using hnl
    have hx_f : evalLitVal α x = false := by
      rw [litEquiv_eval hα heqv, hbn]; exact hnl
    have hand := andGateDef_eval hα hand0
    rw [litEquiv_eval hα hlhs_eqv, hlt] at hand
    have hall := List.all_eq_true.mp hand.symm x hx
    rw [hx_f] at hall; cases hall

theorem m6ScrFrame_refl {c : FullCfg} {g_len ctrl_off ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} (hlen : scr0.length = c.scratch_cap) :
    M6ScrFrame c g_len ctrl_off ht_off ht_sz scr0 scr0 :=
  ⟨hlen, fun _ _ _ => ⟨fun _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩⟩

theorem m6ScrFrame_pref {c : FullCfg} {g_len ctrl_off ht_off ht_sz : Nat}
    {scr0 scr scr_init : List (BitVec 32)} (hle : g_len ≤ ht_off)
    (hht : ht_off + ht_sz ≤ c.scratch_cap)
    (hpref0 : ∀ idx < g_len, scr0[idx]? = scr_init[idx]?)
    (hq0 : M6QueueCtx c scr0 g_len ctrl_off ht_off ht_sz)
    (hfr : M6ScrFrame c g_len ctrl_off ht_off ht_sz scr0 scr) :
    ∀ idx < g_len, scr[idx]? = scr_init[idx]? := by
  intro idx hidx
  have hlt_cap : idx < c.scratch_cap := by omega
  have hlt_ht : idx < ht_off := by omega
  rcases hq0 with rfl | ⟨occ_bkt, bkt_off, inq_off, q_off, hlay⟩
  · rw [(hfr.2 idx hlt_cap hlt_ht).1 rfl, hpref0 idx hidx]
  · have hlay_dup := hlay
    rcases hlay with ⟨_, _, hg_co, _, _, _, _, _, _, _, _, _, _, _, hcq, hqi, hib, hbh, _⟩
    rw [(hfr.2 idx hlt_cap hlt_ht).2 occ_bkt bkt_off inq_off q_off hlay_dup (by omega)
        (by omega) (by omega),
      hpref0 idx hidx]

theorem ev_trail_end_le_cur_vars {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) :
    k.trail_end ≤ k.cur_vars := by
  let vs := (List.range k.trail_end).map fun i => (k.trl[i]?.getD 0#32).toNat / 2
  have hnd : vs.Nodup := by
    rw [List.Nodup, List.pairwise_iff_getElem]
    intro i j hi hj hlt hget
    simp only [vs, List.length_map, List.length_range] at hi hj
    simp only [vs, List.getElem_map, List.getElem_range] at hget
    have heq := hw.trail_vars_nodup i j hi hj hget
    omega
  have hlt : ∀ v ∈ vs, v < k.cur_vars := by
    intro v hv; rw [List.mem_map] at hv; obtain ⟨i, hi, rfl⟩ := hv
    have hl := hw.trail_lits_lt i (List.mem_range.mp hi)
    omega
  simpa [vs] using nodup_lt_length_le hnd hlt

theorem ev_gate_tag0_and {F_cur : List (List Nat)} {lhs0 mword : BitVec 32}
    {g : Nat} {scr0 : List (BitVec 32)} (htag : mword >>> 28 = 0#32)
    (hsem :
      ((mword >>> 28).toNat = 0 ∧ 2 ≤ (mword &&& 0xFF#32).toNat ∧
        AndGateDef (cnfOfClauses F_cur) lhs0.toNat
          (((scr0.drop (g + 2)).take (mword &&& 0xFF#32).toNat).map BitVec.toNat)) ∨
      ((mword >>> 28).toNat = 1 ∧ 2 ≤ (mword &&& 0xFF#32).toNat ∧
        (mword &&& 0xFF#32).toNat ≤ 4 ∧
        XorListGateDef (cnfOfClauses F_cur) lhs0.toNat
          (((scr0.drop (g + 2)).take (mword &&& 0xFF#32).toNat).map BitVec.toNat)) ∨
      ((mword >>> 28).toNat = 2 ∧ (mword &&& 0xFF#32).toNat = 3 ∧
        IteGateDef (cnfOfClauses F_cur) lhs0.toNat (scr0[g + 2]?.getD 0#32).toNat
          (scr0[g + 3]?.getD 0#32).toNat (scr0[g + 4]?.getD 0#32).toNat)) :
    2 ≤ (mword &&& 0xFF#32).toNat ∧
      AndGateDef (cnfOfClauses F_cur) lhs0.toNat
        (((scr0.drop (g + 2)).take (mword &&& 0xFF#32).toNat).map BitVec.toNat) := by
  have h0 : (mword >>> 28).toNat = 0 := by rw [htag]; decide
  rcases hsem with ⟨_, ha, h⟩ | ⟨ht, _⟩ | ⟨ht, _⟩
  · exact ⟨ha, h⟩
  · omega
  · omega

theorem ev_gate_tag1_xor {F_cur : List (List Nat)} {lhs0 mword : BitVec 32}
    {g : Nat} {scr0 : List (BitVec 32)} (htag : mword >>> 28 = 1#32)
    (hsem :
      ((mword >>> 28).toNat = 0 ∧ 2 ≤ (mword &&& 0xFF#32).toNat ∧
        AndGateDef (cnfOfClauses F_cur) lhs0.toNat
          (((scr0.drop (g + 2)).take (mword &&& 0xFF#32).toNat).map BitVec.toNat)) ∨
      ((mword >>> 28).toNat = 1 ∧ 2 ≤ (mword &&& 0xFF#32).toNat ∧
        (mword &&& 0xFF#32).toNat ≤ 4 ∧
        XorListGateDef (cnfOfClauses F_cur) lhs0.toNat
          (((scr0.drop (g + 2)).take (mword &&& 0xFF#32).toNat).map BitVec.toNat)) ∨
      ((mword >>> 28).toNat = 2 ∧ (mword &&& 0xFF#32).toNat = 3 ∧
        IteGateDef (cnfOfClauses F_cur) lhs0.toNat (scr0[g + 2]?.getD 0#32).toNat
          (scr0[g + 3]?.getD 0#32).toNat (scr0[g + 4]?.getD 0#32).toNat)) :
    2 ≤ (mword &&& 0xFF#32).toNat ∧ (mword &&& 0xFF#32).toNat ≤ 4 ∧
      XorListGateDef (cnfOfClauses F_cur) lhs0.toNat
        (((scr0.drop (g + 2)).take (mword &&& 0xFF#32).toNat).map BitVec.toNat) := by
  have h1 : (mword >>> 28).toNat = 1 := by rw [htag]; decide
  rcases hsem with ⟨ht, _⟩ | ⟨_, ha2, ha4, h⟩ | ⟨ht, _⟩
  · omega
  · exact ⟨ha2, ha4, h⟩
  · omega

theorem ev_gate_tag2_ite {F_cur : List (List Nat)} {lhs0 mword : BitVec 32}
    {g : Nat} {scr0 : List (BitVec 32)} (htag : mword >>> 28 = 2#32)
    (hsem :
      ((mword >>> 28).toNat = 0 ∧ 2 ≤ (mword &&& 0xFF#32).toNat ∧
        AndGateDef (cnfOfClauses F_cur) lhs0.toNat
          (((scr0.drop (g + 2)).take (mword &&& 0xFF#32).toNat).map BitVec.toNat)) ∨
      ((mword >>> 28).toNat = 1 ∧ 2 ≤ (mword &&& 0xFF#32).toNat ∧
        (mword &&& 0xFF#32).toNat ≤ 4 ∧
        XorListGateDef (cnfOfClauses F_cur) lhs0.toNat
          (((scr0.drop (g + 2)).take (mword &&& 0xFF#32).toNat).map BitVec.toNat)) ∨
      ((mword >>> 28).toNat = 2 ∧ (mword &&& 0xFF#32).toNat = 3 ∧
        IteGateDef (cnfOfClauses F_cur) lhs0.toNat (scr0[g + 2]?.getD 0#32).toNat
          (scr0[g + 3]?.getD 0#32).toNat (scr0[g + 4]?.getD 0#32).toNat)) :
    (mword &&& 0xFF#32).toNat = 3 ∧
      IteGateDef (cnfOfClauses F_cur) lhs0.toNat (scr0[g + 2]?.getD 0#32).toNat
        (scr0[g + 3]?.getD 0#32).toNat (scr0[g + 4]?.getD 0#32).toNat := by
  have h2 : (mword >>> 28).toNat = 2 := by rw [htag]; decide
  rcases hsem with ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨_, ha3, h⟩
  · omega
  · omega
  · exact ⟨ha3, h⟩

theorem ev_tag1_rx_congr {F_cur : List (List Nat)} {scr0 tmpi : List (BitVec 32)}
    {lhs0 lhs : BitVec 32} {g ar : Nat} (hscr_ge : g + 2 + ar ≤ scr0.length)
    (har_le : ar ≤ tmpi.length)
    (hlhs : LitEquiv (cnfOfClauses F_cur) lhs0.toNat lhs.toNat)
    (heqv : ∀ k < ar, LitEquiv (cnfOfClauses F_cur)
      (scr0[g + 2 + k]?.getD 0#32).toNat (tmpi[k]?.getD 0#32).toNat)
    (hxor0 : XorListGateDef (cnfOfClauses F_cur) lhs0.toNat
      (((scr0.drop (g + 2)).take ar).map BitVec.toNat)) :
    XorListGateDef (cnfOfClauses F_cur) lhs.toNat ((tmpi.take ar).map BitVec.toNat) := by
  intro α hα
  have hlen : (((scr0.drop (g + 2)).take ar).map BitVec.toNat).length =
      ((tmpi.take ar).map BitVec.toNat).length := by
    simp only [List.length_map, List.length_take, List.length_drop]
    rw [Nat.min_eq_left (by omega), Nat.min_eq_left har_le]
  have heqv_i : ∀ i < (((scr0.drop (g + 2)).take ar).map BitVec.toNat).length,
      LitEquiv (cnfOfClauses F_cur)
        ((((scr0.drop (g + 2)).take ar).map BitVec.toNat)[i]?.getD 0)
        (((tmpi.take ar).map BitVec.toNat)[i]?.getD 0) := by
    intro i hi
    simp only [List.length_map, List.length_take, List.length_drop] at hi
    have hi_ar : i < ar := by omega
    rw [List.getElem?_eq_getElem (by simp [List.length_take, List.length_drop]; omega),
      List.getElem?_eq_getElem (by simp [List.length_take]; omega)]
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, Option.getD_some]
    have h1 := heqv i hi_ar
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
      Option.getD_some, Option.getD_some] at h1
    exact h1
  rw [← litEquiv_eval hα hlhs, hxor0 α hα]
  exact xorEvalList_of_litEquiv hα hlen heqv_i

theorem ev_tag1_ua0_entails {F_cur : List (List Nat)} {lhs : BitVec 32}
    (hxor : XorListGateDef (cnfOfClauses F_cur) lhs.toNat []) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg lhs.toNat]) := by
  refine entails_of_eval_mem fun α hα => ⟨litNeg lhs.toNat, List.mem_cons_self .., ?_⟩
  have h := hxor α hα
  rw [xorEvalList_nil] at h
  rw [evalLitVal_litNeg, h]; rfl

theorem ev_tag1_ua1_equiv {F_cur : List (List Nat)} {lhs r0 : BitVec 32}
    (hxor : XorListGateDef (cnfOfClauses F_cur) lhs.toNat [r0.toNat]) :
    LitEquiv (cnfOfClauses F_cur) lhs.toNat r0.toNat := by
  refine litEquiv_of_eval_eq fun α hα => ?_
  have h := hxor α hα
  rwa [xorEvalList_cons, xorEvalList_nil, Bool.bne_false] at h

theorem ev_tag1_ua2_equiv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs t0 t1 : BitVec 32} (hlhs : lhs.toNat < 2 * k.cur_vars)
    (hxor : XorListGateDef (cnfOfClauses F_cur) lhs.toNat [t0.toNat, t1.toNat])
    (hdom : k.vals[lhs.toNat]?.getD 0#8 = 1#8 ∨ k.vals[lhs.toNat]?.getD 0#8 = 0xFF#8) :
    LitEquiv (cnfOfClauses F_cur)
      (if k.vals[lhs.toNat]?.getD 0#8 = 1#8 then t0 ^^^ 1#32 else t0).toNat t1.toNat := by
  refine litEquiv_of_eval_eq fun α hα => ?_
  have hx := hxor α hα
  rw [xorEvalList_pair] at hx
  rcases hdom with h1 | hff
  · rw [h1, ite_eq_left rfl, bv32_xor1_eq_litNeg, evalLitVal_litNeg]
    have htr := entails_eval_true (vals1_entails hw hcl0 hlhs h1) hα
    rw [htr] at hx
    cases h0 : evalLitVal α t0.toNat <;> cases h1' : evalLitVal α t1.toNat <;>
      simp [h0, h1'] at hx ⊢
  · have hne : (0xFF#8 : BitVec 8) ≠ 1#8 := by decide
    rw [hff, ite_eq_right hne]
    have hfl := entails_neg_eval_false (valsff_entails_neg hw hcl0 hlhs hff) hα
    rw [hfl] at hx
    cases h0 : evalLitVal α t0.toNat <;> cases h1' : evalLitVal α t1.toNat <;>
      simp [h0, h1'] at hx ⊢

theorem ev_tag1_match_equiv {F_cur : List (List Nat)} {cv0 : Nat}
    {lhs ml : BitVec 32} {tmps : List (BitVec 32)} {harity : BitVec 32}
    (hgate : M6HashGateOk F_cur cv0 lhs tmps 1#32 harity)
    (hm : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α ml.toNat =
        xorEvalList α ((tmps.take harity.toNat).map BitVec.toNat)) :
    LitEquiv (cnfOfClauses F_cur) lhs.toNat ml.toNat := by
  refine litEquiv_of_eval_eq fun α hα => ?_
  obtain ⟨_, _, h1, _⟩ := hgate
  have hxor := (h1 rfl).2.2.2 α hα
  rw [hxor, hm α hα]

theorem ev_xor_list_step_eval_ne0 {α : Nat → Bool} {eflip eflip' : BitVec 32}
    {rx : List Nat} {tmps : List (BitVec 32)} {i na : Nat} {r : BitVec 32}
    (hfl : eflip = 0#32 ∨ eflip = 1#32)
    (h_prev : xorEvalList α (rx.take i) =
      ((eflip == 1#32) != xorEvalList α ((tmps.take na).map BitVec.toNat)))
    (hi_rx : i < rx.length) (hrx_i : rx[i]'hi_rx = r.toNat)
    (heval : evalLitVal α r.toNat = true ∨ evalLitVal α r.toNat = false)
    (hfl' : eflip' = if evalLitVal α r.toNat then eflip ^^^ 1#32 else eflip) :
    xorEvalList α (rx.take (i + 1)) =
      ((eflip' == 1#32) != xorEvalList α ((tmps.take na).map BitVec.toNat)) := by
  rw [List.take_succ_eq_append_getElem hi_rx, xorEvalList_append, hrx_i, h_prev]
  change (((eflip == 1#32) != _) != (evalLitVal α r.toNat != false)) = _
  rw [hfl']
  rcases hfl with rfl | rfl <;> rcases heval with h | h <;> rw [h] <;>
    cases xorEvalList α ((tmps.take na).map BitVec.toNat) <;> rfl

theorem ev_xor_list_step_push {α : Nat → Bool} {eflip : BitVec 32}
    {rx : List Nat} {tmps : List (BitVec 32)} {i na : Nat} {r : BitVec 32}
    (hfl : eflip = 0#32 ∨ eflip = 1#32)
    (h_prev : xorEvalList α (rx.take i) =
      ((eflip == 1#32) != xorEvalList α ((tmps.take na).map BitVec.toNat)))
    (hi_rx : i < rx.length) (hrx_i : rx[i]'hi_rx = r.toNat)
    (hna : na < tmps.length) :
    let e0 := r &&& ~~~1#32
    let tmps' := tmps.set na e0
    let eflip' := eflip ^^^ (r &&& 1#32)
    xorEvalList α (rx.take (i + 1)) =
      ((eflip' == 1#32) != xorEvalList α ((tmps'.take (na + 1)).map BitVec.toNat)) := by
  intro e0 tmps' eflip'
  rw [List.take_succ_eq_append_getElem hi_rx, xorEvalList_append, hrx_i, h_prev]
  have htk : (tmps'.take (na + 1)).map BitVec.toNat =
      (tmps.take na).map BitVec.toNat ++ [e0.toNat] := by
    dsimp only [tmps']
    rw [List.take_succ_eq_append_getElem (by rw [List.length_set]; omega),
      List.getElem_set_self (by rw [List.length_set]; omega),
      List.take_set_of_le (Nat.le_refl _), List.map_append]; rfl
  rw [htk, xorEvalList_append]
  change (((eflip == 1#32) != _) != (evalLitVal α r.toNat != false)) =
    ((eflip ^^^ (r &&& 1#32) == 1#32) != (_ != (evalLitVal α e0.toNat != false)))
  have hbit : (r &&& 1#32) = 0#32 ∨ (r &&& 1#32) = 1#32 := by
    have h0n : (0#32 : BitVec 32).toNat = 0 := rfl
    have h1n : (1#32 : BitVec 32).toNat = 1 := rfl
    have h1 : (r &&& 1#32).toNat < 2 := by
      rw [BitVec.toNat_and, h1n, Nat.and_one_is_mod]; exact Nat.mod_lt _ (by decide)
    rcases Nat.mod_two_eq_zero_or_one (r &&& 1#32).toNat with hm | hm
    · left; exact BitVec.eq_of_toNat_eq (by rw [h0n]; omega)
    · right; exact BitVec.eq_of_toNat_eq (by rw [h1n]; omega)
  have hev_0 : evalLitVal α e0.toNat = α (r.toNat / 2) := by
    dsimp only [e0]; rw [evalLitVal, litVar, litSign, m6_bv32_and_not1_toNat]
    simp [Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  have hand1 : (r &&& 1#32).toNat = r.toNat % 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
  have hev_r : evalLitVal α r.toNat =
      (evalLitVal α e0.toNat != ((r &&& 1#32) == 1#32)) := by
    rw [hev_0]
    rcases hbit with hb | hb <;> rw [hb] <;>
      have hmod := congrArg BitVec.toNat hb <;> rw [hand1] at hmod
    · change r.toNat % 2 = 0 at hmod
      simp [evalLitVal, litVar, litSign, hmod]
    · change r.toNat % 2 = 1 at hmod
      simp [evalLitVal, litVar, litSign, hmod]
  rw [hev_r]
  rcases hfl with rfl | rfl <;> rcases hbit with hb | hb <;> simp only [hb] <;>
    cases xorEvalList α ((tmps.take na).map BitVec.toNat) <;>
    cases evalLitVal α e0.toNat <;> rfl

theorem ev_bit_and1_xor_bit {eflip r : BitVec 32}
    (hfl : eflip = 0#32 ∨ eflip = 1#32) :
    (eflip ^^^ (r &&& 1#32)) = 0#32 ∨ (eflip ^^^ (r &&& 1#32)) = 1#32 := by
  have h0n : (0#32 : BitVec 32).toNat = 0 := rfl
  have h1n : (1#32 : BitVec 32).toNat = 1 := rfl
  have hbit : (r &&& 1#32) = 0#32 ∨ (r &&& 1#32) = 1#32 := by
    have h1 : (r &&& 1#32).toNat < 2 := by
      rw [BitVec.toNat_and, h1n, Nat.and_one_is_mod]; exact Nat.mod_lt _ (by decide)
    rcases Nat.mod_two_eq_zero_or_one (r &&& 1#32).toNat with hm | hm
    · left; exact BitVec.eq_of_toNat_eq (by rw [h0n]; omega)
    · right; exact BitVec.eq_of_toNat_eq (by rw [h1n]; omega)
  rcases hfl with rfl | rfl <;> rcases hbit with hb | hb <;>
    first | (rw [hb]; decide) | (rw [hb]; decide)

theorem ev_tag1_push_inv {F_cur : List (List Nat)} {cv0 maxv ar_n i1 na1 : Nat}
    {rl flip1 : BitVec 32} {tmpl tmpi : List (BitVec 32)} {rx0 : List Nat}
    (htl_l : tmpl.length = maxv) (hna_le : na1 ≤ i1) (hi1_lt : i1 < ar_n)
    (har_len : ar_n ≤ maxv) (hfl1 : flip1 = 0#32 ∨ flip1 = 1#32)
    (htail_l : ∀ q, i1 ≤ q → q < ar_n → tmpl[q]? = tmpi[q]?)
    (hlt_l : ∀ q < na1, (tmpl[q]?.getD 0#32).toNat < 2 * cv0 ∧
      (tmpl[q]?.getD 0#32).toNat % 2 = 0)
    (hrl_lt : rl.toNat < 2 * cv0) (hi1_rx : i1 < rx0.length)
    (hrx_i : rx0[i1]'hi1_rx = rl.toNat)
    (hxor_l : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      xorEvalList α (rx0.take i1) =
        ((flip1 == 1#32) != xorEvalList α ((tmpl.take na1).map BitVec.toNat))) :
    let e0 := rl &&& ~~~1#32
    let tmpl' := tmpl.set na1 e0
    tmpl'.length = maxv ∧ na1 + 1 ≤ i1 + 1 ∧ i1 + 1 ≤ ar_n ∧
    ((flip1 ^^^ (rl &&& 1#32)) = 0#32 ∨ (flip1 ^^^ (rl &&& 1#32)) = 1#32) ∧
    (∀ q, i1 + 1 ≤ q → q < ar_n → tmpl'[q]? = tmpi[q]?) ∧
    (∀ q < na1 + 1, (tmpl'[q]?.getD 0#32).toNat < 2 * cv0 ∧
      (tmpl'[q]?.getD 0#32).toNat % 2 = 0) ∧
    (∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      xorEvalList α (rx0.take (i1 + 1)) =
        (((flip1 ^^^ (rl &&& 1#32)) == 1#32) !=
          xorEvalList α ((tmpl'.take (na1 + 1)).map BitVec.toNat))) := by
  intro e0 tmpl'
  refine ⟨by rw [List.length_set]; exact htl_l, by omega, by omega,
    ev_bit_and1_xor_bit hfl1, ?_, ?_, ?_⟩
  · intro q hq1 hq2; dsimp only [tmpl']; rw [List.getElem?_set_ne (by omega)]
    exact htail_l q (by omega) hq2
  · intro q hq; dsimp only [tmpl']
    by_cases hqe : q = na1
    · subst hqe; rw [List.getElem?_set_self (by omega), Option.getD_some]
      dsimp only [e0]; rw [m6_bv32_and_not1_toNat]; omega
    · rw [List.getElem?_set_ne (Ne.symm hqe)]; exact hlt_l q (by omega)
  · intro α hα; exact ev_xor_list_step_push hfl1 (hxor_l α hα) hi1_rx hrx_i (by omega)

theorem ev_tag1_dedup_push_eq {α : Nat → Bool} {lhs' vjd : BitVec 32}
    {tmps tmpd : List (BitVec 32)} {ua_n jd_n na1_n : Nat}
    (hua_d : ua_n < tmpd.length) (hjd_s : jd_n < tmps.length)
    (hj_na : jd_n < na1_n) (_hna_s : na1_n ≤ tmps.length)
    (hvjd : vjd = tmps[jd_n]?.getD 0#32)
    (hxord : evalLitVal α lhs'.toNat =
      (xorEvalList α ((tmpd.take ua_n).map BitVec.toNat) !=
        xorEvalList α (((tmps.drop jd_n).take (na1_n - jd_n)).map BitVec.toNat))) :
    let tmpd' := tmpd.set ua_n vjd
    evalLitVal α lhs'.toNat =
      (xorEvalList α ((tmpd'.take (ua_n + 1)).map BitVec.toNat) !=
        xorEvalList α (((tmps.drop (jd_n + 1)).take (na1_n - (jd_n + 1))).map BitVec.toNat)) := by
  intro tmpd'
  have htk : (tmpd'.take (ua_n + 1)).map BitVec.toNat =
      (tmpd.take ua_n).map BitVec.toNat ++ [vjd.toNat] := by
    dsimp only [tmpd']
    rw [List.take_succ_eq_append_getElem (by rw [List.length_set]; exact hua_d),
      List.getElem_set_self (by rw [List.length_set]; exact hua_d),
      List.take_set_of_le (Nat.le_refl _), List.map_append]; rfl
  have hdp : ((tmps.drop jd_n).take (na1_n - jd_n)).map BitVec.toNat =
      vjd.toNat :: (((tmps.drop (jd_n + 1)).take (na1_n - (jd_n + 1))).map BitVec.toNat) := by
    have h0 : vjd = tmps[jd_n]'hjd_s := by
      rw [hvjd, List.getElem?_eq_getElem hjd_s, Option.getD_some]
    rw [h0, ← List.map_cons]; congr 1
    have hsub1 : na1_n - jd_n = (na1_n - (jd_n + 1)) + 1 := by omega
    rw [hsub1, list_drop_take_succ tmps hjd_s]
  rw [hxord, htk, hdp, xorEvalList_append, xorEvalList_cons, xorEvalList_cons, xorEvalList_nil]
  cases xorEvalList α ((tmpd.take ua_n).map BitVec.toNat) <;>
    cases evalLitVal α vjd.toNat <;>
    cases xorEvalList α (((tmps.drop (jd_n + 1)).take (na1_n - (jd_n + 1))).map BitVec.toNat) <;>
    rfl

theorem ev_tag1_dedup_skip_eq {α : Nat → Bool} {lhs' : BitVec 32}
    {tmps tmpd : List (BitVec 32)} {ua_n jd_n na1_n : Nat}
    (hjd1_s : jd_n + 1 < tmps.length) (hj2_na : jd_n + 1 < na1_n)
    (hsame : tmps[jd_n]?.getD 0#32 = tmps[jd_n + 1]?.getD 0#32)
    (hxord : evalLitVal α lhs'.toNat =
      (xorEvalList α ((tmpd.take ua_n).map BitVec.toNat) !=
        xorEvalList α (((tmps.drop jd_n).take (na1_n - jd_n)).map BitVec.toNat))) :
    evalLitVal α lhs'.toNat =
      (xorEvalList α ((tmpd.take ua_n).map BitVec.toNat) !=
        xorEvalList α (((tmps.drop (jd_n + 2)).take (na1_n - (jd_n + 2))).map BitVec.toNat)) := by
  have hjd_s : jd_n < tmps.length := by omega
  have h0 : tmps[jd_n]?.getD 0#32 = tmps[jd_n]'hjd_s := by
    rw [List.getElem?_eq_getElem hjd_s, Option.getD_some]
  have h1 : tmps[jd_n + 1]?.getD 0#32 = tmps[jd_n + 1]'hjd1_s := by
    rw [List.getElem?_eq_getElem hjd1_s, Option.getD_some]
  have hsub1 : na1_n - jd_n = (na1_n - (jd_n + 1)) + 1 := by omega
  have hsub2 : na1_n - (jd_n + 1) = (na1_n - (jd_n + 2)) + 1 := by omega
  have hslice : ((tmps.drop jd_n).take (na1_n - jd_n)).map BitVec.toNat =
      (tmps[jd_n]?.getD 0#32).toNat :: (tmps[jd_n + 1]?.getD 0#32).toNat ::
        (((tmps.drop (jd_n + 2)).take (na1_n - (jd_n + 2))).map BitVec.toNat) := by
    rw [h0, h1, ← List.map_cons, ← List.map_cons]; congr 1
    rw [hsub1, list_drop_take_succ tmps hjd_s, hsub2, list_drop_take_succ tmps hjd1_s]
  rw [hxord, hslice, hsame, xorEvalList_dedup_adj]

theorem ev_tag1_post_sort {F_cur : List (List Nat)} {cv0 na1_n : Nat} {lhs' : BitVec 32}
    {tmpl tmps : List (BitVec 32)} (htl : na1_n ≤ tmpl.length) (hts : tmps.length = tmpl.length)
    (hperm : List.Perm (tmps.take na1_n) (tmpl.take na1_n))
    (hlt_l : ∀ q < na1_n, (tmpl[q]?.getD 0#32).toNat < 2 * cv0 ∧
      (tmpl[q]?.getD 0#32).toNat % 2 = 0)
    (hxor_l' : XorListGateDef (cnfOfClauses F_cur) lhs'.toNat
      ((tmpl.take na1_n).map BitVec.toNat)) :
    (∀ q < na1_n, (tmps[q]?.getD 0#32).toNat < 2 * cv0 ∧
      (tmps[q]?.getD 0#32).toNat % 2 = 0) ∧
    XorListGateDef (cnfOfClauses F_cur) lhs'.toNat ((tmps.take na1_n).map BitVec.toNat) := by
  refine ⟨fun q hq => ?_, fun α hα => ?_⟩
  · have hmem : tmps[q]'(by omega) ∈ tmpl.take na1_n :=
      hperm.mem_iff.mp (mem_take_of_lt hq (by omega))
    obtain ⟨q0, hq0, hget0⟩ := lt_take_of_mem hmem
    simp only [Nat.lt_min] at hq0
    have h := hlt_l q0 hq0.1
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h hget0
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hget0]
    exact h
  · rw [hxor_l' α hα, xorEvalList_perm α (List.Perm.map _ hperm)]

theorem ev_tag2_tmp_ite {F_cur : List (List Nat)} {lhs_t c1 t2 e2 : BitVec 32}
    {tmpi : List (BitVec 32)} (ht_ge3 : 3 ≤ tmpi.length)
    (hite : IteGateDef (cnfOfClauses F_cur) lhs_t.toNat c1.toNat t2.toNat e2.toNat) :
    let tmps := ((tmpi.set 0 c1).set 1 t2).set 2 e2
    IteGateDef (cnfOfClauses F_cur) lhs_t.toNat
      (tmps[0]?.getD 0#32).toNat (tmps[1]?.getD 0#32).toNat (tmps[2]?.getD 0#32).toNat := by
  intro tmps
  have h0_c : tmps[0]?.getD 0#32 = c1 := by
    dsimp only [tmps]
    rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
      List.getElem?_set_self (by omega), Option.getD_some]
  have h1_c : tmps[1]?.getD 0#32 = t2 := by
    dsimp only [tmps]
    rw [List.getElem?_set_ne (by decide),
      List.getElem?_set_self (by simp; omega), Option.getD_some]
  have h2_c : tmps[2]?.getD 0#32 = e2 := by
    dsimp only [tmps]
    rw [List.getElem?_set_self (by simp; omega), Option.getD_some]
  rw [h0_c, h1_c, h2_c]; exact hite

theorem ev_enq_call_bv_core {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)}
    {alen0 cv0 g_len ht_off ht_sz : Nat} {ctrl_off : BitVec 64}
    {scr0 scr_init : List (BitVec 32)} {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost} {v : BitVec 32}
    (hok : M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off.toNat
      scr0 scr_init st)
    (hq_init : M6QueueCtx c scr_init g_len ctrl_off.toNat ht_off ht_sz)
    (hm : (FullMem c st ⋆ R) m)
    (k : ∀ s' m',
      M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off.toNat
        scr0 scr_init s' →
      s'.core = st.core → (FullMem c s' ⋆ R) m' → Q () m') :
    m6CongEnqVarSpec (c.hdr, ctrl_off, v, ()) m Q X := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  refine ⟨c, st, g_len, ht_off, ht_sz, R, rfl, hok.1.1, hok.2.2.2.2.2.2.2.1, hm,
    fun scr' m' hscrl' hq' hcap_eq hlay' hm' => ?_⟩
  exact k { st with scratch := { st.scratch with scratch_buf := scr' } } m'
    (m6EvalGateOk_enq hok hq_init hscrl' hq' hcap_eq hlay') rfl hm'

theorem ev_enq_call_bv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)}
    {alen0 cv0 g_len ht_off ht_sz : Nat} {ctrl_off : BitVec 64}
    {scr0 scr_init : List (BitVec 32)} {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost} {v : BitVec 32}
    (hok : M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off.toNat
      scr0 scr_init st)
    (hq_init : M6QueueCtx c scr_init g_len ctrl_off.toNat ht_off ht_sz)
    (hm : (FullMem c st ⋆ R) m)
    (k : ∀ s' m',
      M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off.toNat
        scr0 scr_init s' →
      s'.core.tmp = st.core.tmp → (FullMem c s' ⋆ R) m' → Q () m') :
    m6CongEnqVarSpec (c.hdr, ctrl_off, v, ()) m Q X :=
  ev_enq_call_bv_core hok hq_init hm fun s' m' hok' hc hm' =>
    k s' m' hok' (congrArg FullCoreState.tmp hc) hm'

theorem wsState_tmp (s : FullState) (r t : List (BitVec 32)) :
    (wsState s r t).core.tmp = t := rfl

theorem wsState_vals (s : FullState) (r t : List (BitVec 32)) :
    (wsState s r t).core.vals = s.core.vals := rfl

theorem wsState_scr (s : FullState) (r t : List (BitVec 32)) :
    (wsState s r t).scratch.scratch_buf = s.scratch.scratch_buf := rfl

theorem focus_ws_tmp {c : FullCfg} {s : FullState} {r t : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMem c (wsState s r t) ⋆ R) m) :
    (array (t := i32) c.pTmp t ⋆ (FullTmpRest c (wsState s r t) ⋆ R)) m :=
  focus_full_tmp hm

theorem unfocus_ws_tmp {c : FullCfg} {s : FullState} {r t t' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pTmp t' ⋆ (FullTmpRest c (wsState s r t) ⋆ R)) m) :
    (FullMem c (wsState s r t') ⋆ R) m :=
  ws_unfocus_tmp hm

structure M6EvCtx where
  cfg : FullCfg
  F0 : CNF Nat
  F_cur : List (List Nat)
  fuel0 : BitVec 64
  ar0 : List (BitVec 32)
  alen0 : Nat
  cv0 : Nat
  g_len : Nat
  ht_off : Nat
  ht_sz : Nat
  ctrl_off : Nat
  scr0 : List (BitVec 32)
  scr_init : List (BitVec 32)
  R : Mem 64 → Prop

@[expose] def M6EvStOk (ctx : M6EvCtx) (st : FullState) : Prop :=
  M6EvalGateOk ctx.cfg ctx.F0 ctx.F_cur ctx.fuel0 ctx.ar0 ctx.alen0 ctx.cv0
    ctx.g_len ctx.ht_off ctx.ht_sz ctx.ctrl_off ctx.scr0 ctx.scr_init st

structure M6EvOutCtx (ctx : M6EvCtx) (s0 : FullState) (Q : Post [i64]) : Prop where
  hcv0 : ctx.cv0 = s0.core.cur_vars
  hf0 : ctx.fuel0 = s0.core.fuel
  ha0 : ctx.ar0 = s0.core.arena
  hal0 : ctx.alen0 = s0.core.arena_len
  hs0 : ctx.scr_init = s0.scratch.scratch_buf
  hle : ctx.g_len ≤ ctx.ht_off
  hht : ctx.ht_off + ctx.ht_sz ≤ ctx.cfg.scratch_cap
  hpref0 : ∀ idx < ctx.g_len, ctx.scr_init[idx]? = ctx.scr0[idx]?
  hq0 : M6QueueCtx ctx.cfg ctx.scr_init ctx.g_len ctx.ctrl_off ctx.ht_off ctx.ht_sz
  hQ : ∀ (r : BitVec 64) s' m',
    FullDenseInvW ctx.cfg ctx.F0 ctx.F_cur s' →
    s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
    s'.core.arena = s0.core.arena → s'.core.arena_len = s0.core.arena_len →
    FullCongReprInv ctx.F_cur (2 * s'.core.cur_vars) s'.core.repr →
    (∀ idx < ctx.g_len, s'.scratch.scratch_buf[idx]? = ctx.scr0[idx]?) →
    M6CongHtInv ctx.F_cur s'.core.cur_vars ctx.scr0 s'.scratch.scratch_buf
      ctx.g_len ctx.ht_off ctx.ht_sz →
    M6QueueCtx ctx.cfg s'.scratch.scratch_buf ctx.g_len ctx.ctrl_off ctx.ht_off ctx.ht_sz →
    ((r &&& 2#64) = 0#64 →
      (∀ idx < ctx.cfg.scratch_cap, idx < ctx.ht_off →
        (ctx.ctrl_off = ctx.cfg.scratch_cap →
          s'.scratch.scratch_buf[idx]? = s0.scratch.scratch_buf[idx]?) ∧
        (∀ occ_bkt bkt_off inq_off q_off,
          M6CtrlLayout ctx.cfg s0.scratch.scratch_buf ctx.g_len ctx.ctrl_off
            occ_bkt bkt_off inq_off q_off ctx.ht_off ctx.ht_sz →
          idx ≠ ctx.ctrl_off + 5 →
          ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
          ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) →
          s'.scratch.scratch_buf[idx]? = s0.scratch.scratch_buf[idx]?))) →
    ((r &&& 2#64) ≠ 0#64 → ctx.F0.Unsat) →
    (FullMem ctx.cfg s' ⋆ ctx.R) m' → Q (r, ()) m'

theorem m6EvStOk_dw {ctx : M6EvCtx} {st : FullState} (h : M6EvStOk ctx st) :
    FullDenseInvW ctx.cfg ctx.F0 ctx.F_cur st := h.1

theorem m6EvStOk_wit {ctx : M6EvCtx} {st : FullState} (h : M6EvStOk ctx st) :
    FullWitnessInv ctx.cfg ctx.F0 ctx.F_cur st.core := h.1.2.1

theorem m6EvStOk_cl {ctx : M6EvCtx} {st : FullState} (h : M6EvStOk ctx st) :
    st.core.cur_level = 0 := h.1.2.2.2.2.2.1

theorem m6EvStOk_cv {ctx : M6EvCtx} {st : FullState} (h : M6EvStOk ctx st) :
    st.core.cur_vars = ctx.cv0 := h.2.1

theorem m6EvStOk_repr {ctx : M6EvCtx} {st : FullState} (h : M6EvStOk ctx st) :
    FullCongReprInv ctx.F_cur (2 * ctx.cv0) st.core.repr := h.2.2.2.2.2.1

theorem m6EvStOk_ht {ctx : M6EvCtx} {st : FullState} (h : M6EvStOk ctx st) :
    M6CongHtInv ctx.F_cur ctx.cv0 ctx.scr0 st.scratch.scratch_buf
      ctx.g_len ctx.ht_off ctx.ht_sz :=
  h.2.2.2.2.2.2.1

theorem m6EvStOk_q {ctx : M6EvCtx} {st : FullState} (h : M6EvStOk ctx st) :
    M6QueueCtx ctx.cfg st.scratch.scratch_buf ctx.g_len ctx.ctrl_off ctx.ht_off ctx.ht_sz :=
  h.2.2.2.2.2.2.2.1

theorem m6EvStOk_fr {ctx : M6EvCtx} {st : FullState} (h : M6EvStOk ctx st) :
    M6ScrFrame ctx.cfg ctx.g_len ctx.ctrl_off ctx.ht_off ctx.ht_sz
      ctx.scr_init st.scratch.scratch_buf :=
  h.2.2.2.2.2.2.2.2

theorem m6EvStOk_wsState {ctx : M6EvCtx} {s0 : FullState} (h : M6EvStOk ctx s0)
    {r t : List (BitVec 32)} (hr : r.length = 2 * ctx.cfg.max_vars)
    (ht : t.length = ctx.cfg.max_vars)
    (hrepr : FullCongReprInv ctx.F_cur (2 * ctx.cv0) r) :
    M6EvStOk ctx (wsState s0 r t) :=
  m6EvalGateOk_wsState h hr ht hrepr

theorem m6EvStOk_with_repr {ctx : M6EvCtx} {st : FullState} (h : M6EvStOk ctx st)
    {r : List (BitVec 32)} (hr : r.length = 2 * ctx.cfg.max_vars)
    (hrepr : FullCongReprInv ctx.F_cur (2 * ctx.cv0) r) :
    M6EvStOk ctx { st with core := { st.core with repr := r } } :=
  m6EvalGateOk_with_repr h hr hrepr

theorem m6EvStOk_with_repr_mclr {ctx : M6EvCtx} {st : FullState} (h : M6EvStOk ctx st)
    {r mc : List (BitVec 32)} (hr : r.length = 2 * ctx.cfg.max_vars)
    (hmc : mc.length = ctx.cfg.max_vars)
    (hrepr : FullCongReprInv ctx.F_cur (2 * ctx.cv0) r) :
    M6EvStOk ctx { st with core := { st.core with repr := r, min_clr := mc } } :=
  m6EvalGateOk_with_repr_mclr h hr hmc hrepr

theorem m6EvStOk_ht_insert {ctx : M6EvCtx} {stp : FullState}
    {g_len : Nat} {ht_off ht_sz ctrl_off g slot : BitVec 64}
    (hok : M6EvStOk ctx stp) (hgn : ctx.g_len = g_len)
    (hho : ctx.ht_off = ht_off.toNat) (hhs : ctx.ht_sz = ht_sz.toNat)
    (hco : ctx.ctrl_off = ctrl_off.toNat)
    (hg_lt : g.toNat < g_len) (hg_le_ht : g_len ≤ ht_off.toNat)
    (hht_le : ht_off.toNat + ht_sz.toNat ≤ ctx.cfg.scratch_cap)
    (hslot_lt : slot.toNat < ht_sz.toNat)
    (hgat : M6GateAt ctx.F_cur ctx.cv0 ctx.scr0 g_len g.toNat) :
    let scr_ins := stp.scratch.scratch_buf.set (ht_off.toNat + slot.toNat) (g.setWidth 32)
    M6EvStOk ctx { stp with scratch := { stp.scratch with
      scratch_buf := scr_ins, res_sz := stp.scratch.res_sz + 1#64 } } := by
  intro scr_ins
  have hgn64 : (BitVec.ofNat 64 g_len).toNat = g_len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hok1 : M6EvalGateOk ctx.cfg ctx.F0 ctx.F_cur ctx.fuel0 ctx.ar0 ctx.alen0 ctx.cv0
      (BitVec.ofNat 64 g_len).toNat ht_off.toNat ht_sz.toNat ctrl_off.toNat
      ctx.scr0 ctx.scr_init stp := by
    unfold M6EvStOk at hok
    rw [hgn64, ← hgn, ← hho, ← hhs, ← hco]; exact hok
  have hok2 := ev_ht_insert_ok hok1 (g_len := BitVec.ofNat 64 g_len)
    (hgn64.symm ▸ hg_lt) (hgn64.symm ▸ hg_le_ht) hht_le hslot_lt (hgn64.symm ▸ hgat)
  unfold M6EvStOk; rw [hgn, hho, hhs, hco, ← hgn64]; exact hok2

@[expose] def M6EvFindInv (ctx : M6EvCtx) (s0 : FullState) (g_n ar_n : Nat) :
    Tup Val [i32] → Mem 64 → Prop :=
  fun (i, ()) mi => ∃ (repri tmpi : List (BitVec 32)),
    repri.length = 2 * ctx.cfg.max_vars ∧ tmpi.length = ctx.cfg.max_vars ∧
    i.toNat ≤ ar_n ∧ FullCongReprInv ctx.F_cur (2 * ctx.cv0) repri ∧
    (∀ k' < i.toNat,
      (tmpi[k']?.getD 0#32).toNat < 2 * ctx.cv0 ∧
      LitEquiv (cnfOfClauses ctx.F_cur) (ctx.scr0[g_n + 2 + k']?.getD 0#32).toNat
        (tmpi[k']?.getD 0#32).toNat) ∧
    (FullMem ctx.cfg (wsState s0 repri tmpi) ⋆ ctx.R) mi

@[expose] def M6EvProbeInv (ctx : M6EvCtx) (stj : FullState) (ht_sz : Nat)
    (remp : Nat) : Tup Val [i64, i64, .bool] → Mem 64 → Prop :=
  fun (slot, probes, _, ()) mp => ∃ stp : FullState,
    slot.toNat < ht_sz ∧ probes.toNat ≤ 64 ∧ remp = 64 - probes.toNat ∧
    stp.core.tmp = stj.core.tmp ∧ M6EvStOk ctx stp ∧ (FullMem ctx.cfg stp ⋆ ctx.R) mp

@[expose] def M6EvMatchInv (ctx : M6EvCtx) (stp : FullState) (lhs' : BitVec 32) :
    Tup Val [.bool, i32] → Mem 64 → Prop :=
  fun (matched, mlhs, ()) mmatch =>
    ∃ repr_m mclr_m : List (BitVec 32),
      repr_m.length = 2 * ctx.cfg.max_vars ∧
      mclr_m.length = ctx.cfg.max_vars ∧
      FullCongReprInv ctx.F_cur (2 * ctx.cv0) repr_m ∧
      (matched = true → mlhs.toNat < 2 * ctx.cv0 ∧
        LitEquiv (cnfOfClauses ctx.F_cur) lhs'.toNat mlhs.toNat) ∧
      (FullMem ctx.cfg { stp with core :=
        { stp.core with repr := repr_m, min_clr := mclr_m } } ⋆ ctx.R) mmatch

theorem m6Ev_ret2 {ctx : M6EvCtx} {s0 su : FullState} {Q : Post [i64]} {mu : Mem 64}
    (hex : M6EvOutCtx ctx s0 Q) (hoku : M6EvStOk ctx su)
    (huns : ctx.F0.Unsat) (hmu : (FullMem ctx.cfg su ⋆ ctx.R) mu) :
    Q (2#64, ()) mu :=
  ev_ret2_q hex.hQ hex.hcv0 hex.hf0 hex.ha0 hex.hal0 hex.hs0 hex.hle hex.hht
    hex.hpref0 hex.hq0 hoku huns hmu

theorem m6Ev_exit {ctx : M6EvCtx} {s0 su : FullState} {Q : Post [i64]} {mu : Mem 64}
    (hex : M6EvOutCtx ctx s0 Q) (hoku : M6EvStOk ctx su)
    (hmu : (FullMem ctx.cfg su ⋆ ctx.R) mu) (ch keep : Bool) :
    let rv : BitVec 64 := (if ch then 1#64 else 0#64) ||| (if keep then 4#64 else 0#64)
    Q (rv, ()) mu :=
  ev_exit_q hex.hQ hex.hcv0 hex.hf0 hex.ha0 hex.hal0 hex.hs0 hex.hle hex.hht
    hex.hpref0 hex.hq0 hoku hmu ch keep

theorem m6Ev_unit {ctx : M6EvCtx} {st : FullState} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {lit next_ep : BitVec 32}
    (hok : M6EvStOk ctx st) (hl : lit.toNat < 2 * ctx.cv0)
    (hent : (cnfOfClauses ctx.F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hm : (FullMem ctx.cfg st ⋆ ctx.R) m)
    (k : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      M6EvStOk ctx s' → s'.core.tmp = st.core.tmp → (r = 2#64 → ctx.F0.Unsat) →
      (FullMem ctx.cfg s' ⋆ ctx.R) m' → Q (r, ()) m') :
    m3CongUnitFoldSpec (ctx.cfg.hdr, lit, next_ep, ()) m Q X :=
  ev_unit_call hok hl hent hm k

theorem m6Ev_unit_xor1 {ctx : M6EvCtx} {st : FullState} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {lit next_ep : BitVec 32}
    (hok : M6EvStOk ctx st) (hl : lit.toNat < 2 * ctx.cv0)
    (hent : (cnfOfClauses ctx.F_cur).EntailsClause (cnfClause [litNeg lit.toNat]))
    (hm : (FullMem ctx.cfg st ⋆ ctx.R) m)
    (k : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      M6EvStOk ctx s' → s'.core.tmp = st.core.tmp → (r = 2#64 → ctx.F0.Unsat) →
      (FullMem ctx.cfg s' ⋆ ctx.R) m' → Q (r, ()) m') :
    m3CongUnitFoldSpec (ctx.cfg.hdr, lit ^^^ 1#32, next_ep, ()) m Q X :=
  ev_unit_xor1 hok hl hent hm k

theorem m6Ev_equiv {ctx : M6EvCtx} {st : FullState} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {a b next_ep : BitVec 32}
    (hok : M6EvStOk ctx st) (ha : a.toNat < 2 * ctx.cv0) (hb : b.toNat < 2 * ctx.cv0)
    (heqv : LitEquiv (cnfOfClauses ctx.F_cur) a.toNat b.toNat)
    (hm : (FullMem ctx.cfg st ⋆ ctx.R) m)
    (k : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      M6EvStOk ctx s' → s'.core.tmp = st.core.tmp → (r = 2#64 → ctx.F0.Unsat) →
      (FullMem ctx.cfg s' ⋆ ctx.R) m' → Q (r, ()) m') :
    m3CongEquivFoldSpec (ctx.cfg.hdr, a, b, next_ep, ()) m Q X :=
  ev_equiv_call hok ha hb heqv hm k

theorem m6Ev_enq_core {ctx : M6EvCtx} {s0 st : FullState} {Qo : Post [i64]}
    {m : Mem 64} {Q : Post []} {X : XPost} {ctrl_off : BitVec 64} {v : BitVec 32}
    (hex : M6EvOutCtx ctx s0 Qo) (hok : M6EvStOk ctx st)
    (hco : ctrl_off.toNat = ctx.ctrl_off)
    (hm : (FullMem ctx.cfg st ⋆ ctx.R) m)
    (k : ∀ s' m', M6EvStOk ctx s' → s'.core = st.core → (FullMem ctx.cfg s' ⋆ ctx.R) m' → Q () m') :
    m6CongEnqVarSpec (ctx.cfg.hdr, ctrl_off, v, ()) m Q X := by
  have hq0' : M6QueueCtx ctx.cfg ctx.scr_init ctx.g_len ctrl_off.toNat ctx.ht_off ctx.ht_sz :=
    hco ▸ hex.hq0
  have hok' : M6EvalGateOk ctx.cfg ctx.F0 ctx.F_cur ctx.fuel0 ctx.ar0 ctx.alen0 ctx.cv0
      ctx.g_len ctx.ht_off ctx.ht_sz ctrl_off.toNat ctx.scr0 ctx.scr_init st := by
    unfold M6EvStOk at hok; rwa [hco]
  exact ev_enq_call_bv_core hok' hq0' hm fun s' m' h1 hc hm' =>
    k s' m' (by unfold M6EvStOk; rwa [← hco]) hc hm'

theorem m6Ev_enq {ctx : M6EvCtx} {s0 st : FullState} {Qo : Post [i64]}
    {m : Mem 64} {Q : Post []} {X : XPost} {ctrl_off : BitVec 64} {v : BitVec 32}
    (hex : M6EvOutCtx ctx s0 Qo) (hok : M6EvStOk ctx st)
    (hco : ctrl_off.toNat = ctx.ctrl_off)
    (hm : (FullMem ctx.cfg st ⋆ ctx.R) m)
    (k : ∀ s' m',
      M6EvStOk ctx s' → s'.core.tmp = st.core.tmp → (FullMem ctx.cfg s' ⋆ ctx.R) m' → Q () m') :
    m6CongEnqVarSpec (ctx.cfg.hdr, ctrl_off, v, ()) m Q X :=
  m6Ev_enq_core hex hok hco hm fun s' m' h1 hc hm' => k s' m' h1 (congrArg FullCoreState.tmp hc) hm'

@[expose] def M6EvOut (ctx : M6EvCtx) (lhs' tag harity : BitVec 32) (nh' : Bool)
    (mj : Mem 64) : Prop :=
  ∃ stj : FullState,
    M6EvStOk ctx stj ∧
    (nh' = true → M6HashGateOk ctx.F_cur ctx.cv0 lhs' stj.core.tmp tag harity) ∧
    (nh' = true → lhs'.toNat < 2 * ctx.cv0) ∧
    (FullMem ctx.cfg stj ⋆ ctx.R) mj

theorem m6EvOut {ctx : M6EvCtx} {lhs' tag harity : BitVec 32} {nh' : Bool} {mj : Mem 64}
    (stj : FullState) (hokj : M6EvStOk ctx stj)
    (hg : nh' = true → M6HashGateOk ctx.F_cur ctx.cv0 lhs' stj.core.tmp tag harity)
    (hl : nh' = true → lhs'.toNat < 2 * ctx.cv0)
    (hm : (FullMem ctx.cfg stj ⋆ ctx.R) mj) :
    M6EvOut ctx lhs' tag harity nh' mj :=
  ⟨stj, hokj, hg, hl, hm⟩

@[expose] def M6EvTag0P1Inv (ctx : M6EvCtx) (s0 : FullState)
    (repri : List (BitVec 32)) (raw : List (BitVec 32)) (ar_n : Nat)
    (il na : BitVec 32) (ml : Mem 64) : Prop :=
  ∃ tmpl : List (BitVec 32),
    tmpl.length = ctx.cfg.max_vars ∧ na.toNat ≤ il.toNat ∧ il.toNat ≤ ar_n ∧
    (∀ j, il.toNat ≤ j → j < ar_n → tmpl[j]? = raw[j]?) ∧
    (∀ j < na.toNat, ∃ k < ar_n, tmpl[j]? = raw[k]?) ∧
    (∀ k < il.toNat,
      s0.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
      ∃ j < na.toNat, tmpl[j]? = raw[k]?) ∧
    (FullMem ctx.cfg (wsState s0 repri tmpl) ⋆ ctx.R) ml

@[expose] def M6EvTag0P1Brk (ctx : M6EvCtx) (s0 : FullState)
    (repri : List (BitVec 32)) (raw : List (BitVec 32)) (ar_n : Nat)
    (il : BitVec 32) (has_false : Bool) (na : BitVec 32) (ml : Mem 64) : Prop :=
  ∃ tmpl : List (BitVec 32),
    tmpl.length = ctx.cfg.max_vars ∧ na.toNat ≤ ar_n ∧
    (has_false = true → ∃ k < ar_n,
      s0.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
    (has_false = false → il.toNat = ar_n ∧
      (∀ j < na.toNat, ∃ k < ar_n, tmpl[j]? = raw[k]?) ∧
      (∀ k < ar_n,
        s0.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
        ∃ j < na.toNat, tmpl[j]? = raw[k]?)) ∧
    (FullMem ctx.cfg (wsState s0 repri tmpl) ⋆ ctx.R) ml

@[expose] def M6EvTag0DedupInv (ctx : M6EvCtx) (s0 : FullState)
    (repri tmps : List (BitVec 32)) (na_n : Nat) (ua si : BitVec 32) (md : Mem 64) : Prop :=
  ∃ tmpd : List (BitVec 32),
    tmpd.length = ctx.cfg.max_vars ∧ ua.toNat ≤ si.toNat ∧ si.toNat ≤ na_n ∧
    (0 < si.toNat → 0 < ua.toNat) ∧
    (∀ j, si.toNat ≤ j → j < na_n → tmpd[j]? = tmps[j]?) ∧
    (∀ j < ua.toNat, ∃ k < na_n, tmpd[j]? = tmps[k]?) ∧
    (∀ j < si.toNat, ∃ q < ua.toNat, tmpd[q]?.getD 0#32 = tmps[j]?.getD 0#32) ∧
    (FullMem ctx.cfg (wsState s0 repri tmpd) ⋆ ctx.R) md

@[expose] def M6EvTag0DedupBrk (ctx : M6EvCtx) (s0 : FullState)
    (repri tmps : List (BitVec 32)) (lhs : BitVec 32) (na_n : Nat)
    (clash : Bool) (ua : BitVec 32) (md : Mem 64) : Prop :=
  ∃ tmpd : List (BitVec 32),
    tmpd.length = ctx.cfg.max_vars ∧ ua.toNat ≤ na_n ∧
    (∀ j < ua.toNat, ∃ k < na_n, tmpd[j]? = tmps[k]?) ∧
    (clash = true →
      litNeg lhs.toNat ∈ (tmps.take na_n).map BitVec.toNat ∨
      ∃ z ∈ (tmps.take na_n).map BitVec.toNat, litNeg z ∈ (tmps.take na_n).map BitVec.toNat) ∧
    (clash = false → 0 < ua.toNat ∧
      ∀ j < na_n, ∃ q < ua.toNat, tmpd[q]?.getD 0#32 = tmps[j]?.getD 0#32) ∧
    (FullMem ctx.cfg (wsState s0 repri tmpd) ⋆ ctx.R) md

@[expose] def M6EvTag1P1Inv (ctx : M6EvCtx) (s0 : FullState)
    (repri tmpi : List (BitVec 32)) (rx0 : List Nat) (ar_n : Nat)
    (i1 flip1 na1 : BitVec 32) (ml : Mem 64) : Prop :=
  ∃ tmpl : List (BitVec 32),
    tmpl.length = ctx.cfg.max_vars ∧ na1.toNat ≤ i1.toNat ∧ i1.toNat ≤ ar_n ∧
    (flip1 = 0#32 ∨ flip1 = 1#32) ∧
    (∀ q, i1.toNat ≤ q → q < ar_n → tmpl[q]? = tmpi[q]?) ∧
    (∀ q < na1.toNat, (tmpl[q]?.getD 0#32).toNat < 2 * ctx.cv0 ∧
      (tmpl[q]?.getD 0#32).toNat % 2 = 0) ∧
    (∀ α : Nat → Bool, (cnfOfClauses ctx.F_cur).Sat α →
      xorEvalList α (rx0.take i1.toNat) =
        ((flip1 == 1#32) != xorEvalList α ((tmpl.take na1.toNat).map BitVec.toNat))) ∧
    (FullMem ctx.cfg (wsState s0 repri tmpl) ⋆ ctx.R) ml

@[expose] def M6EvTag1DedupInv (ctx : M6EvCtx) (s0 : FullState)
    (repri tmps : List (BitVec 32)) (lhs' : BitVec 32) (na1_n : Nat) :
    Tup Val [i32, i32] → Mem 64 → Prop :=
  fun (jd, ua, ()) md => ∃ tmpd : List (BitVec 32),
    tmpd.length = ctx.cfg.max_vars ∧ ua.toNat ≤ jd.toNat ∧ jd.toNat ≤ na1_n ∧
    (∀ q, jd.toNat ≤ q → q < na1_n → tmpd[q]? = tmps[q]?) ∧
    (∀ q < ua.toNat, (tmpd[q]?.getD 0#32).toNat < 2 * ctx.cv0 ∧
      (tmpd[q]?.getD 0#32).toNat % 2 = 0) ∧
    (∀ α : Nat → Bool, (cnfOfClauses ctx.F_cur).Sat α →
      evalLitVal α lhs'.toNat =
        (xorEvalList α ((tmpd.take ua.toNat).map BitVec.toNat) !=
         xorEvalList α (((tmps.drop jd.toNat).take (na1_n - jd.toNat)).map BitVec.toNat))) ∧
    (FullMem ctx.cfg (wsState s0 repri tmpd) ⋆ ctx.R) md

end EvalGateHelpers

namespace M6bHeadTactics

/-- Uniform continuation handler after `full_cong_unit_fold` / `full_cong_equiv_fold` inside
`full_cong_eval_gate`: early-returns `2#64` if `r == 2#64`, else joins `(changed', ())`. -/
scoped elab "ev_after_fold " hex:ident hres:ident ch0:ident hc_ok:ident
    mm:ident hmem:ident chVar:ident " => " k:tacticSeq : tactic => do
  let hcId := Lean.mkIdent `hc
  Lean.Elab.Tactic.evalTactic <| ← `(tactic| (
    m6b_split
    · m6b_let
      exact m6Ev_ret2 $hex $hc_ok ($hres (beq_iff_eq.mp $hcId)) $hmem
    · m6b_to_group; refine wp_join_group (ts := [.bool]) (fun _ m_af => m_af = $mm)
        (fun _ ⟨$chVar, ⟨⟩⟩ m_af hm_af => by rw [hm_af]; m6b_let; ($k:tacticSeq)) ?_
      intro Jef hJef; m6b_split
      · m6b_let; exact hJef (true, ()) $mm rfl
      · m6b_let; exact hJef ($ch0, ()) $mm rfl))

/-- Uniform continuation handler after `full_cong_equiv_fold` with 2 `full_cong_enq_var` calls
inside `if (ef == 1ULL)`. -/
scoped elab "ev_after_equiv_enq2 " hex:ident henq:ident st0:ident hres:ident ch0:ident
    hc_ok:ident mm:ident hmem:ident stVar:ident hokVar:ident "_" mVar:ident hmVar:ident
    chVar:ident " => " k:tacticSeq : tactic => do
  let hcId := Lean.mkIdent `hc
  let ctxId := Lean.mkIdent `ctx
  Lean.Elab.Tactic.evalTactic <| ← `(tactic| (
    m6b_split
    · m6b_let
      exact m6Ev_ret2 $hex $hc_ok ($hres (beq_iff_eq.mp $hcId)) $hmem
    · m6b_to_group; refine wp_join_group (ts := [.bool])
        (fun (_, ()) m_af => ∃ s_af : FullState,
          M6EvStOk $ctxId s_af ∧
          s_af.core.tmp = ($st0).core.tmp ∧ (FullMem ($ctxId).cfg s_af ⋆ ($ctxId).R) m_af)
        (fun _ ⟨$chVar, ⟨⟩⟩ $mVar ⟨$stVar, $hokVar, _, $hmVar⟩ => by
          m6b_let; ($k:tacticSeq))
        ?_
      intro Jef hJef; m6b_split
      · m6b_steps; m6b_call $henq
        refine m6Ev_enq $hex $hc_ok rfl $hmem fun st_e1 m_e1 hok_e1 ht_e1 hm_e1 => ?_
        m6b_steps; m6b_call $henq
        refine m6Ev_enq $hex hok_e1 rfl hm_e1 fun st_e2 m_e2 hok_e2 ht_e2 hm_e2 => ?_
        m6b_let; exact hJef (true, ()) m_e2 ⟨st_e2, hok_e2, ht_e2.trans ht_e1, hm_e2⟩
      · m6b_let; exact hJef ($ch0, ()) $mm ⟨$st0, $hc_ok, rfl, $hmem⟩))

end M6bHeadTactics

end LeanQbe.T.Examples.Kissat.FullM6CongSubst
