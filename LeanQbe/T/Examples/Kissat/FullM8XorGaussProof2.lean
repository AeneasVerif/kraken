/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8XorGaussProof0
public import LeanQbe.T.Examples.Kissat.FullM8XorGaussProof1a
public import LeanQbe.T.Examples.Kissat.FullM8XorGaussProof2a
import LeanQbe.T.Examples.Kissat.FullAssignAddLemmas1
import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
public meta import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat M8 XOR / $\mathbb{F}_2$ Gauss-Jordan — Matrix Emission (`FullM8XorGaussProof2`)

`Func.wp` proof for `full_xor_emit_mat`, re-exporting `FullM8XorGaussProof2a` (`XorPoolCompClosed`,
`full_xor_build_mat_wp`, `full_xor_rref_wp`, `full_xor_emit_pool_small_wp`).
-/

set_option autoImplicit false

local elab "c0_hstraight" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 2000

local elab "c0_hstraight!" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false, strictMem := true } 2000

public section

namespace LeanQbe.T.Examples.Kissat.FullM8XorGauss

open Std Std.Sat Std.ExtHashMap LeanQbe.T.C0Step
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FullAssignAddTactics
open FullAssignAddTactics LeanQbe.T.Examples.Kissat.FullM6ProofUtil

/-! ## 1. Pure Helpers & Factored Sub-Block Proofs (`private`) -/

private def EmitStateOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 s : FullState) : Prop :=
  FullSparseInvW c F0 F_cur s ∧ s.core.cur_vars = s0.core.cur_vars ∧
  s.core.cur_level = 0 ∧ s.core.fuel = s0.core.fuel ∧
  s.scratch.scratch_buf = s0.scratch.scratch_buf ∧
  s.scratch.work_stk1 = s0.scratch.work_stk1 ∧
  s.scratch.work_stk2 = s0.scratch.work_stk2 ∧
  s.scratch.tarjan_reach = s0.scratch.tarjan_reach

private theorem emitStateOk_upd_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} (h : EmitStateOk c F0 F_cur s0 s)
    {tmp' : List (BitVec 32)} (ht : tmp'.length = s.core.tmp.length) :
    EmitStateOk c F0 F_cur s0 { s with core := { s.core with tmp := tmp' } } :=
  ⟨fullSparseInvW_upd_tmp h.1 ht, h.2.1, h.2.2.1, h.2.2.2.1,
   h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

private theorem emitStateOk_upd_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} (h : EmitStateOk c F0 F_cur s0 s) (oom' : BitVec 64) :
    EmitStateOk c F0 F_cur s0 { s with core := { s.core with oom := oom' } } :=
  ⟨fullSparseInvW_upd_oom h.1 oom', h.2.1, h.2.2.1, h.2.2.2.1,
   h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

private theorem emitStateOk_upd_inc {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} (h : EmitStateOk c F0 F_cur s0 s) (inc' : BitVec 64)
    (hu : inc' ≠ 0#64 → (cnfOfClauses F_cur).Unsat) :
    EmitStateOk c F0 F_cur s0 { s with core := { s.core with inconsistent := inc' } } :=
  ⟨fullSparseInvW_upd_inc h.1 inc' hu, h.2.1, h.2.2.1, h.2.2.2.1,
   h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

private theorem emitStateOk_of_addUnit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} (h : EmitStateOk c F0 F_cur s0 s)
    {vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
      phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss'}
    (let_s' : FullState)
    (hs'_eq : let_s' = { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te',
                            propagated := prop', cur_level := cl', unassigned := unass',
                            unflushed := unfl', inconsistent := inc' }
      scratch := { s.scratch with phases := phases', target_assigned := ta',
                                  best_assigned := ba', phases_target := pt',
                                  phases_best := pb', heap := hp', pos := ps',
                                  heap_len := hl', q_search_idx := qsi',
                                  q_search_stamp := qss' } })
    (hlen' : let_s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur let_s'.core)
    (hcl' : cl' = 0) : EmitStateOk c F0 F_cur s0 let_s' := by
  subst hs'_eq
  exact ⟨fullSparseInvW_of_addUnit h.1 _ rfl hlen' hw', h.2.1, hcl', h.2.2.2.1,
    h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

private theorem emitStateOk_of_addBin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} (h : EmitStateOk c F0 F_cur s0 s)
    {vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb' oom' inc'
      phases' wsort'}
    (let_s' : FullState)
    (hs'_eq : let_s' = { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                            oom := oom', inconsistent := inc' }
      scratch := { s.scratch with phases := phases', wsort := wsort' } })
    (hlen' : let_s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur let_s'.core) :
    EmitStateOk c F0 F_cur s0 let_s' := by
  subst hs'_eq
  exact ⟨fullSparseInvW_of_addBin h.1 _ rfl hlen' hw', h.2.1, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

private theorem emitStateOk_of_addClause3 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} (h : EmitStateOk c F0 F_cur s0 s)
    {arena' alen' wvec' wstk' wlen' wusable' fred' ni' nr' wsort'}
    (let_s' : FullState)
    (hs'_eq : let_s' = { s with
      core := { s.core with arena := arena', arena_len := alen', wvec := wvec',
                            wstk := wstk', wlen := wlen', wusable := wusable',
                            first_reducible := fred', num_irred := ni',
                            num_redundant := nr' }
      scratch := { s.scratch with wsort := wsort' } })
    (hlen' : let_s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur let_s'.core)
    (hrefs : ∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs let_s')
    (hnd : FullArenaVarsNodup s → FullArenaVarsNodup let_s') :
    EmitStateOk c F0 F_cur s0 let_s' := by
  subst hs'_eq
  exact ⟨fullSparseInvW_of_addClause3 h.1 _ rfl hlen' hw' hrefs hnd, h.2.1, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

private theorem nat_testBit_pow2_sub_one (n b : Nat) :
    (2 ^ n - 1).testBit b = decide (b < n) := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    cases b with
    | zero =>
      have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have hodd : (2 ^ (n + 1) - 1) % 2 = 1 := by rw [Nat.pow_succ]; omega
      simp [Nat.testBit_zero, hodd]
    | succ b =>
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.pow_succ',
        ← Nat.div_div_eq_div_mul, Nat.succ_lt_succ_iff]
      have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have hdiv : (2 * 2 ^ n - 1) / 2 = 2 ^ n - 1 := by omega
      rw [hdiv]
      simpa [Nat.testBit, Nat.shiftRight_eq_div_pow] using ih b

private theorem bv64_low_mask_getLsbD {k : BitVec 64} (hk : k.toNat < 64) {b : Nat}
    (hb : b < 64) :
    ((1#64 <<< k) - 1#64).getLsbD b = decide (b < k.toNat) := by
  have hsh : (1#64 <<< k).toNat = 2 ^ k.toNat := by
    change (1#64 <<< k.toNat).toNat = 2 ^ k.toNat
    rw [BitVec.toNat_shiftLeft, show (1#64).toNat = 1 from rfl, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk)
  have hpos : 1 ≤ 2 ^ k.toNat := Nat.one_le_two_pow
  have hsub : ((1#64 <<< k) - 1#64).toNat = 2 ^ k.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hsh]; exact hpos)), hsh]; rfl
  rw [BitVec.getLsbD_eq_getElem hb, BitVec.getElem_eq_testBit_toNat, hsub]
  exact nat_testBit_pow2_sub_one k.toNat b

private theorem bv64_shr_and1 {x : BitVec 64} {k : Nat} :
    (((x >>> k) &&& 1#64) = 0#64 ∨ ((x >>> k) &&& 1#64) = 1#64) ∧
    ((((x >>> k) &&& 1#64) != 0#64) = x.getLsbD k) := by
  have hbit : ∀ i < 64, ((x >>> k) &&& 1#64).getLsbD i =
      if i = 0 then x.getLsbD k else false := by
    intro i hi
    rw [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_one]
    cases i with
    | zero => simp
    | succ i => simp
  cases hx : x.getLsbD k
  · have h0 : ((x >>> k) &&& 1#64) = 0#64 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rw [hbit i hi, hx]; split <;> simp
    rw [h0]; decide
  · have h1 : ((x >>> k) &&& 1#64) = 1#64 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rw [hbit i hi, hx]; cases i <;> simp
    rw [h1]; decide

private def maskedRowWord (scr : List (BitVec 32)) (rbase ncols w : Nat) : BitVec 64 :=
  if w = ncols / 64 then rowU64 scr rbase w &&& ((1#64 <<< (ncols % 64)) - 1#64)
  else rowU64 scr rbase w

private theorem maskedRowWord_getLsbD {scr : List (BitVec 32)} {rbase ncols w b : Nat}
    (hw : w < (ncols + 64) / 64) (hb : b < 64) :
    (maskedRowWord scr rbase ncols w).getLsbD b =
      (decide (64 * w + b < ncols) && rowBit scr rbase (64 * w + b)) := by
  have hdiv : (64 * w + b) / 64 = w := by omega
  have hmod : (64 * w + b) % 64 = b := by omega
  unfold maskedRowWord rowBit
  rw [hdiv, hmod]
  by_cases hlast : w = ncols / 64
  · rw [ite_eq_left hlast, BitVec.getLsbD_and]
    have hmask : ((1#64 <<< (ncols % 64)) - 1#64).getLsbD b = decide (b < ncols % 64) := by
      have hk : (BitVec.ofNat 64 (ncols % 64)).toNat = ncols % 64 := Nat.mod_eq_of_lt (by omega)
      have h1 := bv64_low_mask_getLsbD (k := BitVec.ofNat 64 (ncols % 64)) (by omega) hb
      simpa [hk] using h1
    rw [hmask, Bool.and_comm]
    congr 1; apply decide_eq_decide.mpr; omega
  · rw [ite_eq_right hlast]
    have hlt : 64 * w + b < ncols := by omega
    simp [hlt]

private theorem rowBit_false_of_masked_zero {scr : List (BitVec 32)} {rbase ncols : Nat}
    (h0 : ∀ w < (ncols + 64) / 64, maskedRowWord scr rbase ncols w = 0#64) :
    ∀ c < ncols, rowBit scr rbase c = false := by
  intro c hc
  have h := maskedRowWord_getLsbD (scr := scr) (rbase := rbase) (ncols := ncols)
    (w := c / 64) (b := c % 64) (by omega) (by omega)
  rw [h0 (c / 64) (by omega), show 64 * (c / 64) + c % 64 = c by omega] at h
  simpa [hc] using h.symm

private def colsOf (nbits c0 c1 c2 c3 : BitVec 64) : List Nat :=
  if nbits = 0#64 then []
  else if nbits = 1#64 then [c0.toNat]
  else if nbits = 2#64 then [c0.toNat, c1.toNat]
  else if nbits = 3#64 then [c0.toNat, c1.toNat, c2.toNat]
  else [c0.toNat, c1.toNat, c2.toNat, c3.toNat]

private theorem pairwise_lt_append_singleton {xs : List Nat} {y : Nat}
    (hp : xs.Pairwise (· < ·)) (hgt : ∀ x ∈ xs, x < y) :
    (xs ++ [y]).Pairwise (· < ·) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.cons_append, List.pairwise_cons]
    have hpx := List.pairwise_cons.mp hp
    refine ⟨fun z hz => ?_, ih hpx.2 (fun a ha => hgt a (List.mem_cons_of_mem x ha))⟩
    rcases List.mem_append.mp hz with h1 | h2
    · exact hpx.1 z h1
    · rcases List.mem_singleton.mp h2 with rfl
      exact hgt x (List.mem_cons_self ..)

private theorem kernighan_step_inv {scr : List (BitVec 32)} {rbase ncols w : Nat}
    {cols : List Nat} {wv : BitVec 64} (hne : wv ≠ 0#64)
    (hcol_lt : ∀ c ∈ cols, c < 64 * (w + 1) ∧ c < ncols)
    (hpw : cols.Pairwise (· < ·))
    (hprev : ∀ c < ncols, c < 64 * w → (rowBit scr rbase c = true ↔ c ∈ cols))
    (hwv_hi : ∀ b < 64, wv.getLsbD b = true → 64 * w + b < ncols ∧ ∀ c ∈ cols, c < 64 * w + b)
    (hwv_cur : ∀ b < 64, 64 * w + b < ncols →
      (rowBit scr rbase (64 * w + b) = true ↔ wv.getLsbD b = true ∨ 64 * w + b ∈ cols)) :
    let b := wv.reverse.clz.toNat
    let col := 64 * w + b
    let cols' := cols ++ [col]
    let wv' := wv &&& (wv - 1#64)
    (∀ c ∈ cols', c < 64 * (w + 1) ∧ c < ncols) ∧ cols'.Pairwise (· < ·) ∧
    (∀ c < ncols, c < 64 * w → (rowBit scr rbase c = true ↔ c ∈ cols')) ∧
    (∀ j < 64, wv'.getLsbD j = true → 64 * w + j < ncols ∧ ∀ c ∈ cols', c < 64 * w + j) ∧
    (∀ j < 64, 64 * w + j < ncols →
      (rowBit scr rbase (64 * w + j) = true ↔ wv'.getLsbD j = true ∨ 64 * w + j ∈ cols')) := by
  dsimp only
  let b := wv.reverse.clz.toNat
  have hb_lt : b < 64 := ctz64_lt wv hne
  have hb_t : wv.getLsbD b = true := ctz64_getLsbD_true wv hne
  have ⟨hcol_nc, hcol_gt⟩ := hwv_hi b hb_lt hb_t
  have hclr : (wv &&& (wv - 1#64)) = wv ^^^ (1#64 <<< b) := kernighan_clear_lsb wv hne
  have hclr_bit : ∀ j < 64, (wv &&& (wv - 1#64)).getLsbD j =
      if j = b then false else wv.getLsbD j := by
    intro j hj
    rw [hclr, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one]
    by_cases hjb : j = b
    · subst hjb; simp [hb_t, hj]
    · by_cases hle : b ≤ j
      · have hne0 : ¬ (j - b = 0) := by omega
        simp [hne0, hjb]
      · have hjlt : j < b := by omega
        simp [hjlt, hjb]
  refine ⟨fun c hc => ?_, pairwise_lt_append_singleton hpw hcol_gt, fun c hc1 hc2 => ?_,
    fun j hj hjt => ?_, fun j hj hjnc => ?_⟩
  · rcases List.mem_append.mp hc with h1 | h2
    · exact hcol_lt c h1
    · rcases List.mem_singleton.mp h2 with rfl; exact ⟨by omega, hcol_nc⟩
  · rw [hprev c hc1 hc2]
    simp only [List.mem_append, List.mem_singleton]
    exact ⟨Or.inl, fun h => h.elim id (fun heq => by omega)⟩
  · rw [hclr_bit j hj] at hjt
    by_cases hjb : j = b
    · rw [ite_eq_left hjb] at hjt; cases hjt
    · rw [ite_eq_right hjb] at hjt
      have hbg : b < j := Classical.byContradiction fun hle => by
        have hlt : j < b := by omega
        have hf := ctz64_getLsbD_false_lt wv hlt
        rw [hf] at hjt; cases hjt
      have ⟨hjnc, hjgt⟩ := hwv_hi j hj hjt
      refine ⟨hjnc, fun c hc => ?_⟩
      rcases List.mem_append.mp hc with h1 | h2
      · exact hjgt c h1
      · rcases List.mem_singleton.mp h2 with rfl; omega
  · rw [hwv_cur j hj hjnc, hclr_bit j hj]
    by_cases hjb : j = b
    · subst hjb; simp [hb_t]; exact Or.inr rfl
    · rw [ite_eq_right hjb]
      simp only [List.mem_append, List.mem_singleton]
      exact ⟨fun h => h.elim Or.inl (fun h2 => Or.inr (Or.inl h2)),
        fun h => h.elim Or.inl (fun h2 => h2.elim Or.inr (fun heq => by omega))⟩

private theorem kernighan_toNat_lt {wv : BitVec 64} (hne : wv ≠ 0#64) :
    (wv &&& (wv - 1#64)).toNat < wv.toNat := by
  have hle := bv64_land_le_right wv (wv - 1#64)
  have hpos : 1 ≤ wv.toNat := Classical.byContradiction fun h0 =>
    hne (BitVec.eq_of_toNat_eq (by rw [show (0#64).toNat = 0 from rfl]; omega))
  have hsub : (wv - 1#64).toNat = wv.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ wv.toNat; exact hpos))]
    rfl
  omega

private theorem list_take3_eq {α : Type} {xs : List α} {a b c : α}
    (hlen : 3 ≤ xs.length) (h0 : xs[0]'(by omega) = a)
    (h1 : xs[1]'(by omega) = b) (h2 : xs[2]'(by omega) = c) :
    xs.take 3 = [a, b, c] := by
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, rest⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · simp_all

private theorem list_take4_eq {α : Type} {xs : List α} {a b c d : α}
    (hlen : 4 ≤ xs.length) (h0 : xs[0]'(by omega) = a)
    (h1 : xs[1]'(by omega) = b) (h2 : xs[2]'(by omega) = c) (h3 : xs[3]'(by omega) = d) :
    xs.take 4 = [a, b, c, d] := by
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, rest⟩⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · simp_all

private theorem bv32_mask_lit_toNat {v : BitVec 32} {m : BitVec 64} {i : Nat}
    (hv : v.toNat < 2 ^ 30) :
    ((v <<< (1 : Nat)) ||| ((m >>> i) &&& 1#64).setWidth 32).toNat =
      mkLit v.toNat (!((m.toNat >>> i) % 2 == 1)) := by
  have hand : ((m >>> i) &&& 1#64).toNat = (m.toNat >>> i) % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, show (1#64).toNat = 2 ^ 1 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have hsw : (((m >>> i) &&& 1#64).setWidth 32).toNat = (m.toNat >>> i) % 2 := by
    rw [BitVec.toNat_setWidth, hand, Nat.mod_eq_of_lt (by omega)]
  have hl := bv32_lit_from_var_rhs hv (by rw [hsw]; omega)
  rw [hl, hsw]
  have hrem : (m.toNat >>> i) % 2 = 0 ∨ (m.toNat >>> i) % 2 = 1 := by omega
  rcases hrem with h0 | h1
  · simp [mkLit, h0]
  · simp [mkLit, h1]

/-- Low-nibble parity `(m ^ m>>1 ^ m>>2 ^ m>>3) & 1` used by `full_xor_emit_mat`. -/
private abbrev nibPar (m : BitVec 64) : BitVec 64 :=
  (m ^^^ (m >>> (1 : Nat)) ^^^ (m >>> (2 : Nat)) ^^^ (m >>> (3 : Nat))) &&& 1#64

private theorem maskParity3_eq_nibPar {m : Nat} (hm : m < 8) :
    maskParity 3 m = (nibPar (BitVec.ofNat 64 m) != 0#64) := by
  have hc : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem maskParity4_eq_nibPar {m : Nat} (hm : m < 16) :
    maskParity 4 m = (nibPar (BitVec.ofNat 64 m) != 0#64) := by
  have hc : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨
      m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11 ∨ m = 12 ∨ m = 13 ∨ m = 14 ∨ m = 15 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem maskParity_of_nibPar_ne {k : Nat} {m rhs_bit : BitVec 64}
    (hk : k = 3 ∨ k = 4) (hm : m.toNat < 2 ^ k)
    (hrb : rhs_bit = 0#64 ∨ rhs_bit = 1#64) (hne : nibPar m ≠ rhs_bit) :
    maskParity k m.toNat = !(rhs_bit != 0#64) := by
  have hof : BitVec.ofNat 64 m.toNat = m := BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt m.isLt)
  have hmp : maskParity k m.toNat = (nibPar m != 0#64) := by
    rcases hk with rfl | rfl
    · simpa [hof] using maskParity3_eq_nibPar hm
    · simpa [hof] using maskParity4_eq_nibPar hm
  have hcp : nibPar m = 0#64 ∨ nibPar m = 1#64 := by
    have := (bv64_shr_and1 (x := m ^^^ (m >>> (1 : Nat)) ^^^ (m >>> (2 : Nat)) ^^^
      (m >>> (3 : Nat))) (k := 0)).1
    simpa [nibPar] using this
  rw [hmp]
  rcases hcp with h0 | h1 <;> rcases hrb with r0 | r1 <;> simp_all

private theorem emit_unit_lit_ok {F : CNF Nat} {c2v scr : List (BitVec 32)}
    {rbase ncols cv : Nat} {c0 c1 c2 c3 rhs_bit : BitVec 64} {v0 : BitVec 32}
    (hcv_lt : cv < 2 ^ 30) (hv0_cv : v0.toNat < cv) (hv0_eq : c2v[c0.toNat]?.getD 0#32 = v0)
    (hrb01 : rhs_bit = 0#64 ∨ rhs_bit = 1#64)
    (hrb_val : (rhs_bit != 0#64) = rowBit scr rbase ncols)
    (hcol_lt : ∀ col ∈ colsOf 1#64 c0 c1 c2 c3, col < ncols)
    (hcol_pw : (colsOf 1#64 c0 c1 c2 c3).Pairwise (· < ·))
    (hcol_bits : ∀ col < ncols, rowBit scr rbase col = true ↔ col ∈ colsOf 1#64 c0 c1 c2 c3)
    (hsound : XorPackedRowSound F c2v scr rbase ncols) :
    ((v0 <<< (1 : Nat)) ||| (rhs_bit ^^^ 1#64).setWidth 32).toNat < 2 * cv ∧
    F.EntailsClause (cnfClause
      [((v0 <<< (1 : Nat)) ||| (rhs_bit ^^^ 1#64).setWidth 32).toNat]) := by
  have hsnd1 := xorVarsSound_of_packedRow hcol_lt (hcol_pw.imp fun h => Nat.ne_of_lt h)
    hcol_bits hsound
  have hvs1 : ((colsOf 1#64 c0 c1 c2 c3).map fun col => (c2v[col]?.getD 0#32).toNat) =
      [v0.toNat] := by simp [colsOf, hv0_eq]
  rw [hvs1, ← hrb_val] at hsnd1
  have hrb32_le : (rhs_bit.setWidth 32).toNat ≤ 1 := by rcases hrb01 with rfl | rfl <;> decide
  have hrb32_ne : ((rhs_bit.setWidth 32) != 0#32) = (rhs_bit != 0#64) := by
    rcases hrb01 with rfl | rfl <;> decide
  have hrb32_xor : (rhs_bit ^^^ 1#64).setWidth 32 = rhs_bit.setWidth 32 ^^^ 1#32 := by
    rcases hrb01 with rfl | rfl <;> decide
  have hlit_eq : ((v0 <<< (1 : Nat)) ||| (rhs_bit ^^^ 1#64).setWidth 32).toNat =
      mkLit v0.toNat (rhs_bit != 0#64) := by
    rw [hrb32_xor, ← hrb32_ne]
    exact (bv32_lit_from_var_rhs_mkLit (by omega) hrb32_le).1
  refine ⟨?_, ?_⟩
  · rw [hlit_eq]; unfold mkLit; cases (rhs_bit != 0#64) <;> simp <;> omega
  · rw [hlit_eq]; exact entails_unit_of_xorVarsSound hsnd1

private theorem emit_bin_lits_ok {F : CNF Nat} {c2v scr : List (BitVec 32)}
    {rbase ncols cv : Nat} {c0 c1 c2 c3 rhs_bit : BitVec 64} {v0 v1 : BitVec 32}
    (hcv_lt : cv < 2 ^ 30) (hv0_cv : v0.toNat < cv) (hv1_cv : v1.toNat < cv)
    (hv0_eq : c2v[c0.toNat]?.getD 0#32 = v0) (hv1_eq : c2v[c1.toNat]?.getD 0#32 = v1)
    (hrb01 : rhs_bit = 0#64 ∨ rhs_bit = 1#64)
    (hrb_val : (rhs_bit != 0#64) = rowBit scr rbase ncols)
    (hcol_lt : ∀ col ∈ colsOf 2#64 c0 c1 c2 c3, col < ncols)
    (hcol_pw : (colsOf 2#64 c0 c1 c2 c3).Pairwise (· < ·))
    (hcol_bits : ∀ col < ncols, rowBit scr rbase col = true ↔ col ∈ colsOf 2#64 c0 c1 c2 c3)
    (hsound : XorPackedRowSound F c2v scr rbase ncols) :
    F.EntailsClause (cnfClause
      [((v0 <<< (1 : Nat)) ||| rhs_bit.setWidth 32).toNat,
       ((v1 <<< (1 : Nat)) ||| 1#32).toNat]) ∧
    F.EntailsClause (cnfClause
      [((v0 <<< (1 : Nat)) ||| (rhs_bit ^^^ 1#64).setWidth 32).toNat,
       (v1 <<< (1 : Nat)).toNat]) := by
  have hsnd2 := xorVarsSound_of_packedRow hcol_lt (hcol_pw.imp fun h => Nat.ne_of_lt h)
    hcol_bits hsound
  have hvs2 : ((colsOf 2#64 c0 c1 c2 c3).map fun col => (c2v[col]?.getD 0#32).toNat) =
      [v0.toNat, v1.toNat] := by simp [colsOf, hv0_eq, hv1_eq]
  rw [hvs2, ← hrb_val] at hsnd2
  have hbins := entails_bins_of_xorVarsSound hsnd2
  have hrb32_le : (rhs_bit.setWidth 32).toNat ≤ 1 := by rcases hrb01 with rfl | rfl <;> decide
  have hrb32_ne : ((rhs_bit.setWidth 32) != 0#32) = (rhs_bit != 0#64) := by
    rcases hrb01 with rfl | rfl <;> decide
  have hrb32_xor : (rhs_bit ^^^ 1#64).setWidth 32 = rhs_bit.setWidth 32 ^^^ 1#32 := by
    rcases hrb01 with rfl | rfl <;> decide
  have ha1 : ((v0 <<< (1 : Nat)) ||| rhs_bit.setWidth 32).toNat =
      mkLit v0.toNat (!(rhs_bit != 0#64)) := by
    rw [← hrb32_ne]; exact (bv32_lit_from_var_rhs_mkLit (by omega) hrb32_le).2
  have hb1 : ((v1 <<< (1 : Nat)) ||| 1#32).toNat = mkLit v1.toNat false := by
    simpa [mkLit] using bv32_lit_from_var_rhs (v := v1) (rb := 1#32) (by omega) (by decide)
  have ha2 : ((v0 <<< (1 : Nat)) ||| (rhs_bit ^^^ 1#64).setWidth 32).toNat =
      mkLit v0.toNat (rhs_bit != 0#64) := by
    rw [hrb32_xor, ← hrb32_ne]; exact (bv32_lit_from_var_rhs_mkLit (by omega) hrb32_le).1
  have hb2 : (v1 <<< (1 : Nat)).toNat = mkLit v1.toNat true := by
    simpa [mkLit] using bv32_lit_from_var_rhs (v := v1) (rb := 0#32) (by omega) (by decide)
  rw [ha1, hb1, ha2, hb2]
  exact hbins

private theorem emit_tmp_clause_ok {F : CNF Nat} {c2v : List (BitVec 32)} {cv : Nat}
    {c0 c1 c2 c3 nbits m_bv rhs_bit : BitVec 64} {v0 v1 v2 v3 : BitVec 32}
    {tmp_c : List (BitVec 32)} {rhs : Bool}
    (hcv_lt : cv < 2 ^ 30) (h34 : nbits = 3#64 ∨ nbits = 4#64)
    (hm_lt : m_bv.toNat < 2 ^ nbits.toNat)
    (hrb01 : rhs_bit = 0#64 ∨ rhs_bit = 1#64) (hrb_val : (rhs_bit != 0#64) = rhs)
    (hpar_ne : nibPar m_bv ≠ rhs_bit)
    (hv0_cv : v0.toNat < cv) (hv1_cv : v1.toNat < cv) (hv2_cv : v2.toNat < cv)
    (hv01 : v0 ≠ v1) (hv02 : v0 ≠ v2) (hv12 : v1 ≠ v2)
    (hv3_ok : nbits = 4#64 → v3.toNat < cv ∧ v3 ≠ v0 ∧ v3 ≠ v1 ∧ v3 ≠ v2)
    (hv0_eq : c2v[c0.toNat]?.getD 0#32 = v0) (hv1_eq : c2v[c1.toNat]?.getD 0#32 = v1)
    (hv2_eq : c2v[c2.toNat]?.getD 0#32 = v2)
    (hv3_eq : nbits = 4#64 → c2v[c3.toNat]?.getD 0#32 = v3)
    (hsnd : XorVarsSound F ((colsOf nbits c0 c1 c2 c3).map
      fun col => (c2v[col]?.getD 0#32).toNat) rhs)
    (hlen3 : 3 ≤ tmp_c.length) (hlen4 : nbits = 4#64 → 4 ≤ tmp_c.length)
    (ht0 : tmp_c[0]'(by omega) = (v0 <<< (1 : Nat)) ||| (m_bv &&& 1#64).setWidth 32)
    (ht1 : tmp_c[1]'(by omega) = (v1 <<< (1 : Nat)) ||| ((m_bv >>> (1 : Nat)) &&& 1#64).setWidth 32)
    (ht2 : tmp_c[2]'(by omega) = (v2 <<< (1 : Nat)) ||| ((m_bv >>> (2 : Nat)) &&& 1#64).setWidth 32)
    (ht3 : ∀ h4 : nbits = 4#64, tmp_c[3]'(by have := hlen4 h4; omega) =
      (v3 <<< (1 : Nat)) ||| ((m_bv >>> (3 : Nat)) &&& 1#64).setWidth 32) :
    (∀ l ∈ (tmp_c.take nbits.toNat).map BitVec.toNat, l < 2 * cv) ∧
    ((tmp_c.take nbits.toNat).map fun x => x.toNat / 2).Nodup ∧
    F.EntailsClause (cnfClause ((tmp_c.take nbits.toNat).map BitVec.toNat)) := by
  let l0 : BitVec 32 := (v0 <<< (1 : Nat)) ||| (m_bv &&& 1#64).setWidth 32
  let l1 : BitVec 32 := (v1 <<< (1 : Nat)) ||| ((m_bv >>> (1 : Nat)) &&& 1#64).setWidth 32
  let l2 : BitVec 32 := (v2 <<< (1 : Nat)) ||| ((m_bv >>> (2 : Nat)) &&& 1#64).setWidth 32
  let l3 : BitVec 32 := (v3 <<< (1 : Nat)) ||| ((m_bv >>> (3 : Nat)) &&& 1#64).setWidth 32
  have hl0 : l0.toNat = mkLit v0.toNat (!((m_bv.toNat >>> 0) % 2 == 1)) := by
    simpa [l0] using bv32_mask_lit_toNat (v := v0) (m := m_bv) (i := 0) (by omega)
  have hl1 : l1.toNat = mkLit v1.toNat (!((m_bv.toNat >>> 1) % 2 == 1)) :=
    bv32_mask_lit_toNat (by omega)
  have hl2 : l2.toNat = mkLit v2.toNat (!((m_bv.toNat >>> 2) % 2 == 1)) :=
    bv32_mask_lit_toNat (by omega)
  have hd0 : l0.toNat / 2 = v0.toNat := by rw [hl0]; exact litVar_mkLit _ _
  have hd1 : l1.toNat / 2 = v1.toNat := by rw [hl1]; exact litVar_mkLit _ _
  have hd2 : l2.toNat / 2 = v2.toNat := by rw [hl2]; exact litVar_mkLit _ _
  have hmp := maskParity_of_nibPar_ne (k := nbits.toNat)
    (by rcases h34 with rfl | rfl <;> simp) hm_lt hrb01 hpar_ne
  rw [hrb_val] at hmp
  rcases h34 with rfl | rfl
  · have htake : tmp_c.take 3 = [l0, l1, l2] := list_take3_eq hlen3 ht0 ht1 ht2
    have hvs : ((colsOf 3#64 c0 c1 c2 c3).map fun col => (c2v[col]?.getD 0#32).toNat) =
        [v0.toNat, v1.toNat, v2.toNat] := by simp [colsOf, hv0_eq, hv1_eq, hv2_eq]
    rw [hvs] at hsnd
    have hent := entails_xorMaskClause_of_xorVarsSound hsnd (mask := m_bv.toNat) hmp
    have hxm : xorMaskClause [v0.toNat, v1.toNat, v2.toNat] m_bv.toNat =
        [l0.toNat, l1.toNat, l2.toNat] := by
      simp [xorMaskClause, List.range_succ, hl0, hl1, hl2]
    rw [hxm] at hent
    rw [show (3#64).toNat = 3 from rfl, htake]
    refine ⟨?_, ?_, hent⟩
    · intro l hl
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl
      · rw [hl0]; unfold mkLit; split <;> omega
      · rw [hl1]; unfold mkLit; split <;> omega
      · rw [hl2]; unfold mkLit; split <;> omega
    · simp only [List.map_cons, List.map_nil, hd0, hd1, hd2, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, not_or, List.nodup_nil, not_false_eq_true, and_true]
      exact ⟨⟨fun h => hv01 (BitVec.eq_of_toNat_eq h),
        fun h => hv02 (BitVec.eq_of_toNat_eq h)⟩,
        fun h => hv12 (BitVec.eq_of_toNat_eq h)⟩
  · have ⟨hv3_cv, hv30, hv31, hv32⟩ := hv3_ok rfl
    have hl3 : l3.toNat = mkLit v3.toNat (!((m_bv.toNat >>> 3) % 2 == 1)) :=
      bv32_mask_lit_toNat (by omega)
    have hd3 : l3.toNat / 2 = v3.toNat := by rw [hl3]; exact litVar_mkLit _ _
    have htake : tmp_c.take 4 = [l0, l1, l2, l3] :=
      list_take4_eq (hlen4 rfl) ht0 ht1 ht2 (ht3 rfl)
    have hvs : ((colsOf 4#64 c0 c1 c2 c3).map fun col => (c2v[col]?.getD 0#32).toNat) =
        [v0.toNat, v1.toNat, v2.toNat, v3.toNat] := by
      simp [colsOf, hv0_eq, hv1_eq, hv2_eq, hv3_eq rfl]
    rw [hvs] at hsnd
    have hent := entails_xorMaskClause_of_xorVarsSound hsnd (mask := m_bv.toNat) hmp
    have hxm : xorMaskClause [v0.toNat, v1.toNat, v2.toNat, v3.toNat] m_bv.toNat =
        [l0.toNat, l1.toNat, l2.toNat, l3.toNat] := by
      simp [xorMaskClause, List.range_succ, hl0, hl1, hl2, hl3]
    rw [hxm] at hent
    rw [show (4#64).toNat = 4 from rfl, htake]
    refine ⟨?_, ?_, hent⟩
    · intro l hl
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl
      · rw [hl0]; unfold mkLit; split <;> omega
      · rw [hl1]; unfold mkLit; split <;> omega
      · rw [hl2]; unfold mkLit; split <;> omega
      · rw [hl3]; unfold mkLit; split <;> omega
    · simp only [List.map_cons, List.map_nil, hd0, hd1, hd2, hd3, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, not_or, List.nodup_nil, not_false_eq_true, and_true]
      exact ⟨⟨fun h => hv01 (BitVec.eq_of_toNat_eq h),
        fun h => hv02 (BitVec.eq_of_toNat_eq h),
        fun h => hv30 (BitVec.eq_of_toNat_eq h).symm⟩,
        ⟨fun h => hv12 (BitVec.eq_of_toNat_eq h),
        fun h => hv31 (BitVec.eq_of_toNat_eq h).symm⟩,
        fun h => hv32 (BitVec.eq_of_toNat_eq h).symm⟩

private def emitMatBinBranchExpr (hdr : Val i64) (a b : Val i32)
    (Jskip : Cont []) : Expr Val Cont [i64] :=
  .call (as := [i64, i32, i32]) (bs := [.bool]) "full_has_bin"
      (.var hdr, .var a, .var b, ()) fun p_7 =>
    .jnz (.var p_7.fst) (.jump Jskip ())
      (.let_ (Op.mk (.add i64) (.var hdr, .imm 56, ())) fun p_8 =>
        .load i64 (.var p_8.fst) fun ld =>
          .let_ (Op.mk (.add i64) (.var ld, .imm 8, ())) fun p_9 =>
            .let_ (Op.mk (.add i64) (.var hdr, .imm 40, ())) fun p_10 =>
              .load i64 (.var p_10.fst) fun ld =>
                .let_ (Op.mk (.cmp .uge i64 .bool rfl) (.var p_9.fst, .var ld, ())) fun p_11 =>
                  .jnz (.var p_11.fst) (.ret (.imm 1, ()))
                    (.call (as := [i64, i32, i32]) (bs := [i64]) "full_add_bin"
                        (.var hdr, .var a, .var b, ()) fun p =>
                      .let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var p.fst, .imm 20, ())) fun p_12 =>
                        .jnz (.var p_12.fst) (.ret (.imm 20, ()))
                          (.let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var p.fst, .imm 2, ())) fun p =>
                            .jnz (.var p.fst)
                              (.let_ (Op.mk (.add i64) (.var hdr, .imm 760, ())) fun p =>
                                .store (t := i64) (.imm 0) (.var p.fst) (.ret (.imm 1, ())))
                              (.jump Jskip ()))))

private theorem emit_mat_bin_branch_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s0 s : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {a b : BitVec 32} {Jskip : Cont []} {m : Mem 64}
    (hHasBin : ∀ a m Q X, fullHasBinSpec a m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hok : EmitStateOk c F0 F_cur s0 s)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat]))
    (hm : (FullMem c s ⋆ R) m)
    (hQ_ok : ∀ r s' m', EmitStateOk c F0 F_cur s0 s' → (r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hJskip : ∀ m', (∃ s', EmitStateOk c F0 F_cur s0 s' ∧ (FullMem c s' ⋆ R) m') →
      Jskip () m') :
    wp Γ Q X (emitMatBinBranchExpr c.hdr a b Jskip) m := by
  dsimp only [emitMatBinBranchExpr]
  c0_call hHasBin
  refine ⟨c, F0, F_cur, s, R, rfl, hok.1.1, hok.1.2.1, hm, fun _ _ => ?_⟩
  c0_hsplit
  · c0_hstraight; exact hJskip m ⟨s, hok, hm⟩
  · c0_hstraight
    c0_hsplit
    · c0_hstraight; exact hQ_ok 1#64 s m hok (Or.inl rfl) (fun h => by cases h) hm
    · c0_call hAddBin
      refine ⟨c, F0, F_cur, s, R, rfl, hok.1.1, hok.1.2.1, hok.2.2.1, fun _ _ => hent, hm,
        fun br vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb' oom'
          inc' phases' wsort' m1 hlen1 hw1 _ h20 _ hm1 => ?_⟩
      let s1 : FullState := { s with
        core := { s.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns',
          trl := trl', trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
          wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
          oom := oom', inconsistent := inc' }
        scratch := { s.scratch with phases := phases', wsort := wsort' } }
      have hok1 : EmitStateOk c F0 F_cur s0 s1 := emitStateOk_of_addBin hok s1 rfl hlen1 hw1
      c0_hsplit
      · c0_hstraight
        exact hQ_ok 20#64 s1 m1 hok1 (Or.inr rfl) (fun _ => (h20 (by assumption)).1) hm1
      · c0_hsplit
        · c0_hstraight
          exact hQ_ok 1#64 { s1 with core := { s1.core with oom := 0#64 } } _
            (emitStateOk_upd_oom hok1 0#64) (Or.inl rfl) (fun h => by cases h) hm
        · c0_hstraight; exact hJskip m1 ⟨s1, hok1, hm1⟩

private def emitMatWtLoopExpr (pScr rbase w64 wlast wmask : Val i64)
    (Jwt : Cont [i64, i64]) : Expr Val Cont [i64] :=
  .group (sig := [[i64, i64]])
    (fun Js_1 => .cons (fun p =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p.snd.fst, .var w64, ())) fun p_1 =>
        .jnz (.var p_1.fst)
          (.let_ (Op.mk (.shl i64) (.var p.snd.fst, .imm 1, ())) fun p_2 =>
            .let_ (Op.mk (.add i64) (.var rbase, .var p_2.fst, ())) fun p_3 =>
              .call (as := [i64, i64]) (bs := [i64]) "full_xor_read_u64"
                  (.var pScr, .var p_3.fst, ()) fun p_4 =>
                .group (sig := [[i64]])
                  (fun _ => .cons (fun p_5 =>
                    .group (sig := [[i64, i64]])
                      (fun Js_3 => .cons (fun p_6 =>
                        .group (sig := [[]])
                          (fun _ => .cons (fun _ =>
                            .let_ (Op.mk (.cmp .ugt i64 .bool rfl)
                                (.var p_6.fst, .imm 4, ())) fun p_8 =>
                              .jnz (.var p_8.fst)
                                (.jump Jwt (.var p_6.fst, .var p.snd.fst, ()))
                                (.let_ (Op.mk (.add i64) (.var p.snd.fst, .imm 1, ())) fun p =>
                                  .jump Js_1.fst (.var p_6.fst, .var p.fst, ()))) .nil)
                          (fun Js =>
                            .let_ (Op.mk (.cmp .ne i64 .bool rfl)
                                (.var p_6.snd.fst, .imm 0, ())) fun p =>
                              .jnz (.var p.fst)
                                (.let_ (Op.mk (.cmp .ule i64 .bool rfl)
                                    (.var p_6.fst, .imm 4, ())) fun p =>
                                  .jnz (.var p.fst)
                                    (.let_ (Op.mk (.add i64) (.var p_6.fst, .imm 1, ())) fun p =>
                                      .let_ (Op.mk (.sub i64)
                                          (.var p_6.snd.fst, .imm 1, ())) fun p_9 =>
                                        .let_ (Op.mk (.and i64)
                                            (.var p_6.snd.fst, .var p_9.fst, ())) fun p_10 =>
                                          .jump Js_3.fst (.var p.fst, .var p_10.fst, ()))
                                    (.jump Js.fst ()))
                                (.jump Js.fst ()))) .nil)
                      (fun Js => .jump Js.fst (.var p.fst, .var p_5.fst, ()))) .nil)
                  (fun Js =>
                    .let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var p.snd.fst, .var wlast, ())) fun p =>
                      .jnz (.var p.fst)
                        (.let_ (Op.mk (.and i64) (.var p_4.fst, .var wmask, ())) fun p =>
                          .jump Js.fst (.var p.fst, ()))
                        (.jump Js.fst (.var p_4.fst, ()))))
          (.jump Jwt (.var p.fst, .var p.snd.fst, ()))) .nil)
    (fun Js => .jump Js.fst (.imm 0, .imm 0, ()))

private theorem emit_mat_wt_loop_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {pScr rbase w64 wlast wmask : Val i64} {scr0 : List (BitVec 32)} {Rscr : Mem 64 → Prop}
    {rbase_nat ncols_nat : Nat} {Jwt : Cont [i64, i64]} {mr : Mem 64}
    (hRead : ∀ a m Q X, fullXorReadU64Spec a m Q X →
      Γ "full_xor_read_u64" [i64, i64] [i64] a m Q X)
    (hscr_lt : scr0.length < 2 ^ 32) (hnc_lt : ncols_nat < 2 ^ 30)
    (hrbase_nat : rbase.toNat = rbase_nat)
    (hrbase_end : rbase_nat + 2 * ((ncols_nat + 64) / 64) ≤ scr0.length)
    (hw64_nat : w64.toNat = (ncols_nat + 64) / 64)
    (hwlast_nat : wlast.toNat = ncols_nat / 64)
    (hwmask_eq : wmask = (1#64 <<< (ncols_nat % 64)) - 1#64)
    (hm_scr : (array (t := i32) pScr scr0 ⋆ Rscr) mr)
    (hJwt : ∀ st mwt,
      (match st with
      | (wt, _, ()) =>
        mwt = mr ∧ (wt = 0#64 → ∀ c < ncols_nat, rowBit scr0 rbase_nat c = false)) →
      Jwt st mwt) :
    wp Γ Q X (emitMatWtLoopExpr pScr rbase w64 wlast wmask Jwt) mr := by
  dsimp only [emitMatWtLoopExpr]
  let words64_nat := (ncols_nat + 64) / 64
  refine wp_loop_inv
    (fun (wt, w, ()) mw =>
      mw = mr ∧ w.toNat ≤ words64_nat ∧ wt.toNat ≤ 4 ∧
      (wt = 0#64 → ∀ w' < w.toNat, maskedRowWord scr0 rbase_nat ncols_nat w' = 0#64))
    (fun (_, w, ()) _ => words64_nat - w.toNat)
    (fun Jw hJw => by
      c0_hstraight
      exact hJw (0#64, 0#64, ()) mr
        ⟨rfl, Nat.zero_le _, Nat.zero_le _, fun _ _ hw => by simp at hw⟩)
    (fun Jw (wt, w, ()) mw ⟨hmw, hw_le, hwt_le, hwt0⟩ ihw => ?_)
  cases hmw
  c0_hsplit
  · have hw_lt : w.toNat < words64_nat := by dsimp only [words64_nat]; rw [← hw64_nat]; bv_omega
    have hw_succ : (w + 1#64).toNat = w.toNat + 1 := by dsimp [words64_nat] at hw_lt; bv_omega
    have hw2 : (w <<< (1 : Nat)).toNat = 2 * w.toNat :=
      bv64_shl1_toNat (by dsimp [words64_nat] at hw_lt; omega)
    have hidx_w : (rbase + (w <<< (1 : Nat))).toNat = rbase_nat + 2 * w.toNat := by
      rw [BitVec.toNat_add, hrbase_nat, hw2, Nat.mod_eq_of_lt (by omega)]
    have hidx_bd : (rbase + (w <<< (1 : Nat))).toNat + 1 < scr0.length := by
      rw [hidx_w]; dsimp [words64_nat] at hw_lt; omega
    c0_call hRead
    refine ⟨scr0, Rscr, hidx_bd, hscr_lt, hm_scr, ?_⟩
    dsimp only
    have hread_w : rowU64 scr0 (rbase + w <<< OfNat.ofNat 1).toNat 0 =
        rowU64 scr0 rbase_nat w.toNat := by unfold rowU64; simp [hidx_w]
    refine wp_join_state1 (fun x : Val i64 => x)
      (fun wv0 mw0 => mw0 = mr ∧ wv0 = maskedRowWord scr0 rbase_nat ncols_nat w.toNat) ?_ ?_
    · intro Jm0 wv0 mw0 ⟨hmw0, hwv0_eq⟩
      cases hmw0
      refine wp_loop_inv
        (fun (wt', wv_t, ()) mk =>
          mk = mr ∧ wt.toNat ≤ wt'.toNat ∧ (wt' = wt → wv_t = wv0))
        (fun (wt', _, ()) _ => 5 - wt'.toNat)
        (fun Jk hJk => by
          c0_hstraight
          exact hJk (wt, wv0, ()) mr ⟨rfl, Nat.le_refl _, fun _ => rfl⟩)
        (fun Jk (wt', wv_t, ()) mk ⟨hmk, hwt_le', hwv_t⟩ ihk => ?_)
      cases hmk
      refine wp_join0 (fun mx => mx = mr ∧ (wv_t = 0#64 ∨ 4 < wt'.toNat)) ?_ ?_
      · intro Jx mx ⟨hmx, hex⟩
        cases hmx
        c0_hsplit
        · c0_hstraight
          exact hJwt (wt', w, ()) mr ⟨rfl, fun h0 => by bv_omega⟩
        · have hle4 : wt'.toNat ≤ 4 := by bv_omega
          c0_hstraight
          refine ihw (wt', w + 1#64, ()) mr (by dsimp only; rw [hw_succ]; omega)
            ⟨rfl, by rw [hw_succ]; omega, hle4, fun h0 w' hw' => ?_⟩
          have hwt'0 : wt'.toNat = 0 := by rw [h0]; rfl
          have hwt_eq0 : wt = 0#64 :=
            BitVec.eq_of_toNat_eq (by rw [show (0#64).toNat = 0 from rfl]; omega)
          have hwv_eq0 : wv0 = 0#64 := by
            rw [← hwv_t (by rw [h0, hwt_eq0])]
            rcases hex with h | h
            · exact h
            · omega
          rw [hw_succ] at hw'
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hw') with hlt | rfl
          · exact hwt0 hwt_eq0 w' hlt
          · rw [← hwv0_eq, hwv_eq0]
      · intro Jx hJx
        c0_hsplit
        · c0_hsplit
          · have hle4 : wt'.toNat ≤ 4 := by bv_omega
            have hsucc : (wt' + 1#64).toNat = wt'.toNat + 1 := by bv_omega
            c0_hstraight
            exact ihk (wt' + 1#64, wv_t &&& (wv_t - 1#64), ()) mr (by dsimp only; omega)
              ⟨rfl, by omega, fun h => by have := congrArg BitVec.toNat h; omega⟩
          · c0_hstraight; exact hJx mr ⟨rfl, Or.inr (by bv_omega)⟩
        · c0_hstraight; exact hJx mr ⟨rfl, Or.inl (by bv_omega)⟩
    · intro Jm0 hJm0
      c0_hsplit
      · have hlast : w.toNat = ncols_nat / 64 := by rw [← hwlast_nat]; bv_omega
        c0_hstraight
        refine hJm0 _ mr ⟨rfl, ?_⟩
        unfold maskedRowWord; rw [ite_eq_left hlast, hread_w, hwmask_eq]
      · have hnlast : w.toNat ≠ ncols_nat / 64 := by
          rw [← hwlast_nat]; intro heq; exact (by assumption : w ≠ wlast)
            (BitVec.eq_of_toNat_eq heq)
        c0_hstraight
        refine hJm0 _ mr ⟨rfl, ?_⟩
        unfold maskedRowWord; rw [ite_eq_right hnlast, hread_w]
  · have hw_eq : w.toNat = words64_nat := by dsimp only [words64_nat]; rw [← hw64_nat]; bv_omega
    c0_hstraight
    exact hJwt (wt, w, ()) mr ⟨rfl, fun h0 =>
      rowBit_false_of_masked_zero (fun w' hw' => hwt0 h0 w' (by rw [hw_eq]; exact hw'))⟩

private def emitMatExtractExpr (pScr rbase w64 wlast wmask : Val i64)
    (Jex : Cont [i64, i64, i64, i64, i64, i64]) : Expr Val Cont [i64] :=
  .group (sig := [[i64, i64, i64, i64, i64, i64]])
    (fun Js26 => .cons (fun p26 =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p26.fst, .var w64, ())) fun v25 =>
        .jnz (.var v25.fst)
          (.let_ (Op.mk (.shl i64) (.var p26.fst, .imm 1, ())) fun v26 =>
            .let_ (Op.mk (.add i64) (.var rbase, .var v26.fst, ())) fun v27 =>
              .call (as := [i64, i64]) (bs := [i64]) "full_xor_read_u64"
                  (.var pScr, .var v27.fst, ()) fun r28 =>
                .group (sig := [[i64]])
                  (fun _ => .cons (fun p34 =>
                    .group (sig := [[i64, i64, i64, i64, i64, i64]])
                      (fun _ => .cons (fun p38 =>
                        .let_ (Op.mk (.cmp .ugt i64 .bool rfl)
                            (.var p38.snd.snd.snd.snd.fst, .imm 4, ())) fun v29 =>
                          .jnz (.var v29.fst)
                            (.jump Jex (.var p26.fst, .var p38.fst, .var p38.snd.fst,
                              .var p38.snd.snd.fst, .var p38.snd.snd.snd.fst,
                              .var p38.snd.snd.snd.snd.fst, ()))
                            (.let_ (Op.mk (.add i64) (.var p26.fst, .imm 1, ())) fun v30 =>
                              .jump Js26.fst (.var v30.fst, .var p38.fst, .var p38.snd.fst,
                                .var p38.snd.snd.fst, .var p38.snd.snd.snd.fst,
                                .var p38.snd.snd.snd.snd.fst, ()))) .nil)
                      (fun Js38 =>
                        .group (sig := [[i64, i64, i64, i64, i64, i64]])
                          (fun Js40 => .cons (fun p40 =>
                            .let_ (Op.mk (.cmp .ne i64 .bool rfl)
                                (.var p40.snd.snd.snd.snd.snd.fst, .imm 0, ())) fun v29 =>
                              .jnz (.var v29.fst)
                                (.let_ (Op.mk (.cmp .uge i64 .bool rfl)
                                    (.var p40.snd.snd.snd.snd.fst, .imm 4, ())) fun v30 =>
                                  .jnz (.var v30.fst)
                                    (.jump Js38.fst (.var p40.fst, .var p40.snd.fst,
                                      .var p40.snd.snd.fst, .var p40.snd.snd.snd.fst,
                                      .imm 5, .var p40.snd.snd.snd.snd.snd.fst, ()))
                                    (.let_ (Op.mk (.ctz 64)
                                        (.var p40.snd.snd.snd.snd.snd.fst, ())) fun v31 =>
                                      .let_ (Op.mk (.shl i64) (.var p26.fst, .imm 6, ())) fun v32 =>
                                        .let_ (Op.mk (.add i64)
                                            (.var v32.fst, .var v31.fst, ())) fun v33 =>
                                          .group (sig := [[i64, i64, i64, i64]])
                                            (fun _ => .cons (fun p52 =>
                                              .let_ (Op.mk (.add i64)
                                                  (.var p40.snd.snd.snd.snd.fst, .imm 1, ()))
                                                fun v34 =>
                                              .let_ (Op.mk (.sub i64)
                                                  (.var p40.snd.snd.snd.snd.snd.fst, .imm 1, ()))
                                                fun v35 =>
                                              .let_ (Op.mk (.and i64)
                                                  (.var p40.snd.snd.snd.snd.snd.fst,
                                                   .var v35.fst, ())) fun v36 =>
                                              .jump Js40.fst (.var p52.fst, .var p52.snd.fst,
                                                .var p52.snd.snd.fst, .var p52.snd.snd.snd.fst,
                                                .var v34.fst, .var v36.fst, ())) .nil)
                                            (fun Js52 =>
                                              .let_ (Op.mk (.cmp .eq i64 .bool rfl)
                                                  (.var p40.snd.snd.snd.snd.fst, .imm 0, ()))
                                                fun v34 =>
                                              .jnz (.var v34.fst)
                                                (.jump Js52.fst (.var v33.fst, .var p40.snd.fst,
                                                  .var p40.snd.snd.fst, .var p40.snd.snd.snd.fst,
                                                  ()))
                                                (.group (sig := [[i64, i64, i64]])
                                                  (fun _ => .cons (fun p58 =>
                                                    .jump Js52.fst (.var p40.fst, .var p58.fst,
                                                      .var p58.snd.fst, .var p58.snd.snd.fst, ()))
                                                    .nil)
                                                  (fun Js58 =>
                                                    .let_ (Op.mk (.cmp .eq i64 .bool rfl)
                                                        (.var p40.snd.snd.snd.snd.fst, .imm 1, ()))
                                                      fun v35 =>
                                                    .jnz (.var v35.fst)
                                                      (.jump Js58.fst (.var v33.fst,
                                                        .var p40.snd.snd.fst,
                                                        .var p40.snd.snd.snd.fst, ()))
                                                      (.group (sig := [[i64, i64]])
                                                        (fun _ => .cons (fun p64 =>
                                                          .jump Js58.fst (.var p40.snd.fst,
                                                            .var p64.fst, .var p64.snd.fst, ()))
                                                          .nil)
                                                        (fun Js64 =>
                                                          .let_ (Op.mk (.cmp .eq i64 .bool rfl)
                                                              (.var p40.snd.snd.snd.snd.fst,
                                                               .imm 2, ())) fun v36 =>
                                                          .jnz (.var v36.fst)
                                                            (.jump Js64.fst (.var v33.fst,
                                                              .var p40.snd.snd.snd.fst, ()))
                                                            (.jump Js64.fst (.var p40.snd.snd.fst,
                                                              .var v33.fst, ())))))))))
                                (.jump Js38.fst (.var p40.fst, .var p40.snd.fst,
                                  .var p40.snd.snd.fst, .var p40.snd.snd.snd.fst,
                                  .var p40.snd.snd.snd.snd.fst,
                                  .var p40.snd.snd.snd.snd.snd.fst, ()))) .nil)
                          (fun Js40 =>
                            .jump Js40.fst (.var p26.snd.fst, .var p26.snd.snd.fst,
                              .var p26.snd.snd.snd.fst, .var p26.snd.snd.snd.snd.fst,
                              .var p26.snd.snd.snd.snd.snd.fst, .var p34.fst, ())))) .nil)
                  (fun Js34 =>
                    .let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var p26.fst, .var wlast, ())) fun v29 =>
                      .jnz (.var v29.fst)
                        (.let_ (Op.mk (.and i64) (.var r28.fst, .var wmask, ())) fun v30 =>
                          .jump Js34.fst (.var v30.fst, ()))
                        (.jump Js34.fst (.var r28.fst, ()))))
          (.jump Jex (.var p26.fst, .var p26.snd.fst, .var p26.snd.snd.fst,
            .var p26.snd.snd.snd.fst, .var p26.snd.snd.snd.snd.fst,
            .var p26.snd.snd.snd.snd.snd.fst, ()))) .nil)
    (fun Js26 => .jump Js26.fst (.imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, ()))

private theorem emit_mat_extract_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {pScr rbase w64 wlast wmask : Val i64} {scr0 : List (BitVec 32)} {Rscr : Mem 64 → Prop}
    {rbase_nat ncols_nat : Nat} {Jex : Cont [i64, i64, i64, i64, i64, i64]} {mr : Mem 64}
    (hRead : ∀ a m Q X, fullXorReadU64Spec a m Q X →
      Γ "full_xor_read_u64" [i64, i64] [i64] a m Q X)
    (hscr_lt : scr0.length < 2 ^ 32) (hnc_lt : ncols_nat < 2 ^ 30)
    (hrbase_nat : rbase.toNat = rbase_nat)
    (hrbase_end : rbase_nat + 2 * ((ncols_nat + 64) / 64) ≤ scr0.length)
    (hw64_nat : w64.toNat = (ncols_nat + 64) / 64)
    (hwlast_nat : wlast.toNat = ncols_nat / 64)
    (hwmask_eq : wmask = (1#64 <<< (ncols_nat % 64)) - 1#64)
    (hm_scr : (array (t := i32) pScr scr0 ⋆ Rscr) mr)
    (hJex : ∀ st mx,
      (match st with
      | (_, c0, c1, c2, c3, nbits, ()) =>
        mx = mr ∧ (nbits.toNat ≤ 4 →
          (∀ col ∈ colsOf nbits c0 c1 c2 c3, col < ncols_nat) ∧
          (colsOf nbits c0 c1 c2 c3).Pairwise (· < ·) ∧
          (∀ col < ncols_nat, rowBit scr0 rbase_nat col = true ↔
            col ∈ colsOf nbits c0 c1 c2 c3))) →
      Jex st mx) :
    wp Γ Q X (emitMatExtractExpr pScr rbase w64 wlast wmask Jex) mr := by
  dsimp only [emitMatExtractExpr]
  let words64_nat := (ncols_nat + 64) / 64
  refine wp_loop_inv
    (fun (w, c0, c1, c2, c3, nbits, ()) mw =>
      mw = mr ∧ w.toNat ≤ words64_nat ∧ nbits.toNat ≤ 4 ∧
      (∀ col ∈ colsOf nbits c0 c1 c2 c3, col < 64 * w.toNat ∧ col < ncols_nat) ∧
      (colsOf nbits c0 c1 c2 c3).Pairwise (· < ·) ∧
      (∀ col < ncols_nat, col < 64 * w.toNat →
        (rowBit scr0 rbase_nat col = true ↔ col ∈ colsOf nbits c0 c1 c2 c3)))
    (fun (w, _, _, _, _, _, ()) _ => words64_nat - w.toNat)
    (fun Jw hJw => by
      c0_hstraight
      exact hJw (0#64, 0#64, 0#64, 0#64, 0#64, 0#64, ()) mr
        ⟨rfl, Nat.zero_le _, Nat.zero_le _, by simp [colsOf], by simp [colsOf],
         fun _ _ h => by simp at h⟩)
    (fun Jw (w, c0, c1, c2, c3, nbits, ()) mw
        ⟨hmw, hw_le, hnb_le, hcol_lt, hcol_pw, hcol_bits⟩ ihw => ?_)
  cases hmw
  c0_hsplit
  · have hw_lt : w.toNat < words64_nat := by dsimp only [words64_nat]; rw [← hw64_nat]; bv_omega
    have hw_succ : (w + 1#64).toNat = w.toNat + 1 := by dsimp [words64_nat] at hw_lt; bv_omega
    have hw2 : (w <<< (1 : Nat)).toNat = 2 * w.toNat :=
      bv64_shl1_toNat (by dsimp [words64_nat] at hw_lt; omega)
    have hidx_w : (rbase + (w <<< (1 : Nat))).toNat = rbase_nat + 2 * w.toNat := by
      rw [BitVec.toNat_add, hrbase_nat, hw2, Nat.mod_eq_of_lt (by omega)]
    have hidx_bd : (rbase + (w <<< (1 : Nat))).toNat + 1 < scr0.length := by
      rw [hidx_w]; dsimp [words64_nat] at hw_lt; omega
    c0_call hRead
    refine ⟨scr0, Rscr, hidx_bd, hscr_lt, hm_scr, ?_⟩
    dsimp only
    have hread_w : rowU64 scr0 (rbase + w <<< OfNat.ofNat 1).toNat 0 =
        rowU64 scr0 rbase_nat w.toNat := by unfold rowU64; simp [hidx_w]
    refine wp_join_state1 (fun x : Val i64 => x)
      (fun wv0 mw0 => mw0 = mr ∧ wv0 = maskedRowWord scr0 rbase_nat ncols_nat w.toNat) ?_ ?_
    · intro Jm0 wv0 mw0 ⟨hmw0, hwv0_eq⟩
      cases hmw0
      refine wp_join_state (fun x : Tup Val [i64, i64, i64, i64, i64, i64] => x)
        (fun (c0i, c1i, c2i, c3i, ni, _wvi, ()) mi =>
          mi = mr ∧
          (ni.toNat ≤ 4 →
            (∀ col ∈ colsOf ni c0i c1i c2i c3i, col < 64 * (w.toNat + 1) ∧ col < ncols_nat) ∧
            (colsOf ni c0i c1i c2i c3i).Pairwise (· < ·) ∧
            (∀ col < ncols_nat, col < 64 * (w.toNat + 1) →
              (rowBit scr0 rbase_nat col = true ↔ col ∈ colsOf ni c0i c1i c2i c3i)))) ?_ ?_
      · intro Jwv (c0i, c1i, c2i, c3i, ni, _wvi, ()) mi ⟨hmi, hni_ok⟩
        cases hmi
        c0_hsplit
        · c0_hstraight
          exact hJex (w, c0i, c1i, c2i, c3i, ni, ()) mr ⟨rfl, fun hle => by bv_omega⟩
        · have hni_le4 : ni.toNat ≤ 4 := by bv_omega
          have ⟨h1, h2, h3⟩ := hni_ok hni_le4
          c0_hstraight
          exact ihw (w + 1#64, c0i, c1i, c2i, c3i, ni, ()) mr
            (by dsimp only; rw [hw_succ]; omega)
            ⟨rfl, by rw [hw_succ]; omega, hni_le4,
             fun col hc => by rw [hw_succ]; exact h1 col hc, h2,
             fun col h1c h2c => by rw [hw_succ] at h2c; exact h3 col h1c h2c⟩
      · intro Jwv hJwv
        refine wp_loop_inv
          (fun (c0i, c1i, c2i, c3i, ni, wv, ()) mi =>
            mi = mr ∧ ni.toNat ≤ 4 ∧
            (∀ col ∈ colsOf ni c0i c1i c2i c3i, col < 64 * (w.toNat + 1) ∧ col < ncols_nat) ∧
            (colsOf ni c0i c1i c2i c3i).Pairwise (· < ·) ∧
            (∀ col < ncols_nat, col < 64 * w.toNat →
              (rowBit scr0 rbase_nat col = true ↔ col ∈ colsOf ni c0i c1i c2i c3i)) ∧
            (∀ b < 64, wv.getLsbD b = true →
              64 * w.toNat + b < ncols_nat ∧
              ∀ col ∈ colsOf ni c0i c1i c2i c3i, col < 64 * w.toNat + b) ∧
            (∀ b < 64, 64 * w.toNat + b < ncols_nat →
              (rowBit scr0 rbase_nat (64 * w.toNat + b) = true ↔
                wv.getLsbD b = true ∨ 64 * w.toNat + b ∈ colsOf ni c0i c1i c2i c3i)))
          (fun (_, _, _, _, _, wv, ()) _ => wv.toNat)
          (fun Jk hJk => by
            c0_hstraight
            refine hJk (c0, c1, c2, c3, nbits, wv0, ()) mr
              ⟨rfl, hnb_le,
               fun col hc => ⟨by have := (hcol_lt col hc).1; omega, (hcol_lt col hc).2⟩,
               hcol_pw, hcol_bits, fun b hb hbt => ?_, fun b hb hbnc => ?_⟩
            · rw [hwv0_eq, maskedRowWord_getLsbD hw_lt hb, Bool.and_eq_true,
                decide_eq_true_iff] at hbt
              exact ⟨hbt.1, fun col hc => by have := (hcol_lt col hc).1; omega⟩
            · rw [hwv0_eq, maskedRowWord_getLsbD hw_lt hb]
              simp only [hbnc, decide_true, Bool.true_and]
              exact ⟨Or.inl, fun h => h.elim id (fun hm => by have := (hcol_lt _ hm).1; omega)⟩)
          (fun Jk (c0i, c1i, c2i, c3i, ni, wv, ()) mi
              ⟨hmi, hni_le, hclt, hcpw, hcprev, hwv_hi, hwv_cur⟩ ihk => ?_)
        cases hmi
        c0_hsplit
        · have hwv_ne : wv ≠ 0#64 := by assumption
          c0_hsplit
          · c0_hstraight
            exact hJwv (c0i, c1i, c2i, c3i, 5#64, wv, ()) mr ⟨rfl, fun h => by bv_omega⟩
          · have hni_lt4 : ni.toNat < 4 := by bv_omega
            have hb_lt : wv.reverse.clz.toNat < 64 := ctz64_lt wv hwv_ne
            have hcol_bv : ((w <<< (6 : Nat)) + wv.reverse.clz).toNat =
                64 * w.toNat + wv.reverse.clz.toNat := by
              have hw6 : (w <<< (6 : Nat)).toNat = 64 * w.toNat :=
                bv64_shl6_toNat (by dsimp [words64_nat] at hw_lt; omega)
              rw [BitVec.toNat_add, hw6,
                Nat.mod_eq_of_lt (by dsimp [words64_nat] at hw_lt; omega)]
            c0_hstraight
            generalize hcol_eq : ((w <<< OfNat.ofNat 6) + wv.reverse.clz : BitVec 64) = col_bv
            have hcol_nat : col_bv.toNat = 64 * w.toNat + wv.reverse.clz.toNat := by
              rw [← hcol_eq]; exact hcol_bv
            refine wp_join_state (fun x : Tup Val [i64, i64, i64, i64] => x)
              (fun (c0', c1', c2', c3', ()) mu =>
                mu = mr ∧
                colsOf (ni + 1#64) c0' c1' c2' c3' = colsOf ni c0i c1i c2i c3i ++ [col_bv.toNat])
              ?_ ?_
            · intro Ju (c0', c1', c2', c3', ()) mu ⟨hmu, hpush⟩
              cases hmu
              have hstep := kernighan_step_inv hwv_ne hclt hcpw hcprev hwv_hi hwv_cur
              c0_hstraight
              refine ihk (c0', c1', c2', c3', ni + 1#64, wv &&& (wv - 1#64), ()) mr
                (kernighan_toNat_lt hwv_ne) ⟨rfl, by bv_omega, ?_, ?_, ?_, ?_, ?_⟩
              · rw [hpush, hcol_nat]; exact hstep.1
              · rw [hpush, hcol_nat]; exact hstep.2.1
              · intro c hc1 hc2; rw [hpush, hcol_nat]; exact hstep.2.2.1 c hc1 hc2
              · intro j hj hjt; rw [hpush, hcol_nat]; exact hstep.2.2.2.1 j hj hjt
              · intro j hj hjnc; rw [hpush, hcol_nat]; exact hstep.2.2.2.2 j hj hjnc
            · intro Ju hJu
              c0_hsplit
              · have h0 : ni = 0#64 := by assumption
                c0_hstraight
                exact hJu (col_bv, c1i, c2i, c3i, ()) mr ⟨rfl, by rw [h0]; simp [colsOf]⟩
              · refine wp_join_state (fun x : Tup Val [i64, i64, i64] => x)
                  (fun (c1', c2', c3', ()) mu =>
                    mu = mr ∧
                    colsOf (ni + 1#64) c0i c1' c2' c3' =
                      colsOf ni c0i c1i c2i c3i ++ [col_bv.toNat])
                  (fun _ (c1', c2', c3', ()) mu h => by
                    c0_hstraight; exact hJu (c0i, c1', c2', c3', ()) mu h)
                  (fun Ju1 hJu1 => ?_)
                c0_hsplit
                · have h1 : ni = 1#64 := by assumption
                  c0_hstraight
                  exact hJu1 (col_bv, c2i, c3i, ()) mr ⟨rfl, by rw [h1]; simp [colsOf]⟩
                · refine wp_join_state (fun x : Tup Val [i64, i64] => x)
                    (fun (c2', c3', ()) mu =>
                      mu = mr ∧
                      colsOf (ni + 1#64) c0i c1i c2' c3' =
                        colsOf ni c0i c1i c2i c3i ++ [col_bv.toNat])
                    (fun _ (c2', c3', ()) mu h => by
                      c0_hstraight; exact hJu1 (c1i, c2', c3', ()) mu h)
                    (fun Ju2 hJu2 => ?_)
                  c0_hsplit
                  · have h2 : ni = 2#64 := by assumption
                    c0_hstraight
                    exact hJu2 (col_bv, c3i, ()) mr ⟨rfl, by rw [h2]; simp [colsOf]⟩
                  · have h3 : ni = 3#64 := by
                      have : ni ≠ 0#64 := by assumption
                      have : ni ≠ 1#64 := by assumption
                      have : ni ≠ 2#64 := by assumption
                      bv_omega
                    c0_hstraight
                    exact hJu2 (c2i, col_bv, ()) mr ⟨rfl, by rw [h3]; simp [colsOf]⟩
        · have hwv0 : wv = 0#64 := by bv_omega
          c0_hstraight
          refine hJwv (c0i, c1i, c2i, c3i, ni, wv, ()) mr
            ⟨rfl, fun _ => ⟨hclt, hcpw, fun col h1c h2c => ?_⟩⟩
          by_cases hltw : col < 64 * w.toNat
          · exact hcprev col h1c hltw
          · have hb_eq : 64 * w.toNat + (col - 64 * w.toNat) = col := by omega
            have hc := hwv_cur (col - 64 * w.toNat) (by omega) (by rw [hb_eq]; exact h1c)
            rw [hb_eq, hwv0] at hc; simpa using hc
    · intro Jm0 hJm0
      c0_hsplit
      · have hlast : w.toNat = ncols_nat / 64 := by rw [← hwlast_nat]; bv_omega
        c0_hstraight
        refine hJm0 _ mr ⟨rfl, ?_⟩
        unfold maskedRowWord; rw [ite_eq_left hlast, hread_w, hwmask_eq]
      · have hnlast : w.toNat ≠ ncols_nat / 64 := by
          rw [← hwlast_nat]; intro heq; exact (by assumption : w ≠ wlast)
            (BitVec.eq_of_toNat_eq heq)
        c0_hstraight
        refine hJm0 _ mr ⟨rfl, ?_⟩
        unfold maskedRowWord; rw [ite_eq_right hnlast, hread_w]
  · have hw_eq : w.toNat = words64_nat := by dsimp only [words64_nat]; rw [← hw64_nat]; bv_omega
    c0_hstraight
    refine hJex (w, c0, c1, c2, c3, nbits, ()) mr
      ⟨rfl, fun _ => ⟨fun col hc => (hcol_lt col hc).2, hcol_pw, fun col hc =>
        hcol_bits col hc (by rw [hw_eq]; dsimp [words64_nat]; omega)⟩⟩

private def emitMatMLoopExpr (hdr pTmp emitted_cl wlim nbits rhs_bit : Val i64)
    (v0 v1 v2 v3 : Val i32) (Jvok : Cont [i64]) : Expr Val Cont [i64] :=
  .group (sig := [[i64, i64]])
    (fun Js96 => .cons (fun p96 =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p96.snd.fst, .var wlim, ())) fun v58 =>
        .jnz (.var v58.fst)
          (.group (sig := [[i64]])
            (fun _ => .cons (fun p104 =>
              .let_ (Op.mk (.add i64) (.var p96.snd.fst, .imm 1, ())) fun v59 =>
                .jump Js96.fst (.var p104.fst, .var v59.fst, ())) .nil)
            (fun Js104 =>
              .let_ (Op.mk (.lshr i64) (.var p96.snd.fst, .imm 1, ())) fun q1 =>
              .let_ (Op.mk (.xor i64) (.var p96.snd.fst, .var q1.fst, ())) fun q2 =>
              .let_ (Op.mk (.lshr i64) (.var p96.snd.fst, .imm 2, ())) fun q3 =>
              .let_ (Op.mk (.xor i64) (.var q2.fst, .var q3.fst, ())) fun q4 =>
              .let_ (Op.mk (.lshr i64) (.var p96.snd.fst, .imm 3, ())) fun q5 =>
              .let_ (Op.mk (.xor i64) (.var q4.fst, .var q5.fst, ())) fun q6 =>
              .let_ (Op.mk (.and i64) (.var q6.fst, .imm 1, ())) fun v60 =>
              .let_ (Op.mk (.cmp .ne i64 .bool rfl) (.var v60.fst, .var rhs_bit, ())) fun v61 =>
              .jnz (.var v61.fst)
                (.let_ (Op.mk (.sext 32 64) (.imm 0#32, ())) fun v62 =>
                 .let_ (Op.mk (.mul i64) (.var v62.fst, .imm 4, ())) fun v63 =>
                 .let_ (Op.mk (.add i64) (.var pTmp, .var v63.fst, ())) fun v64 =>
                 .let_ (Op.mk (.shl i32) (.var v0, .imm 1, ())) fun v65 =>
                 .let_ (Op.mk (.and i64) (.var p96.snd.fst, .imm 1, ())) fun v66 =>
                 .let_ (Op.mk (.trunc 64 32) (.var v66.fst, ())) fun v67 =>
                 .let_ (Op.mk (.or i32) (.var v65.fst, .var v67.fst, ())) fun v68 =>
                 .store (.var v68.fst) (.var v64.fst)
                 (.let_ (Op.mk (.sext 32 64) (.imm 1#32, ())) fun v69 =>
                  .let_ (Op.mk (.mul i64) (.var v69.fst, .imm 4, ())) fun v70 =>
                  .let_ (Op.mk (.add i64) (.var pTmp, .var v70.fst, ())) fun v71 =>
                  .let_ (Op.mk (.shl i32) (.var v1, .imm 1, ())) fun v72 =>
                  .let_ (Op.mk (.lshr i64) (.var p96.snd.fst, .imm 1, ())) fun v73 =>
                  .let_ (Op.mk (.and i64) (.var v73.fst, .imm 1, ())) fun v74 =>
                  .let_ (Op.mk (.trunc 64 32) (.var v74.fst, ())) fun v75 =>
                  .let_ (Op.mk (.or i32) (.var v72.fst, .var v75.fst, ())) fun v76 =>
                  .store (.var v76.fst) (.var v71.fst)
                  (.let_ (Op.mk (.sext 32 64) (.imm 2#32, ())) fun v77 =>
                   .let_ (Op.mk (.mul i64) (.var v77.fst, .imm 4, ())) fun v78 =>
                   .let_ (Op.mk (.add i64) (.var pTmp, .var v78.fst, ())) fun v79 =>
                   .let_ (Op.mk (.shl i32) (.var v2, .imm 1, ())) fun v80 =>
                   .let_ (Op.mk (.lshr i64) (.var p96.snd.fst, .imm 2, ())) fun v81 =>
                   .let_ (Op.mk (.and i64) (.var v81.fst, .imm 1, ())) fun v82 =>
                   .let_ (Op.mk (.trunc 64 32) (.var v82.fst, ())) fun v83 =>
                   .let_ (Op.mk (.or i32) (.var v80.fst, .var v83.fst, ())) fun v84 =>
                   .store (.var v84.fst) (.var v79.fst)
                   (.group (sig := [[]])
                     (fun _ => .cons (fun _ =>
                       .group (sig := [[.bool]])
                         (fun _ => .cons (fun p114 =>
                           .group (sig := [[i64]])
                             (fun _ => .cons (fun p118 =>
                               .jump Js104.fst (.var p118.fst, ())) .nil)
                             (fun Js118 =>
                               .jnz (.var p114.fst)
                                 (.jump Js118.fst (.var p96.fst, ()))
                                 (.let_ (Op.mk (.trunc 64 32) (.var nbits, ())) fun v85 =>
                                  .call (as := [i64, i32, i32, .bool]) (bs := [i64])
                                      "full_add_clause"
                                      (.var hdr, .var v85.fst, .imm 0#32, .imm false, ()) fun r86 =>
                                  .let_ (Op.mk (.cmp .eq i64 .bool rfl)
                                      (.var r86.fst, .imm 0xFFFFFFFF#64, ())) fun v87 =>
                                  .jnz (.var v87.fst) (.ret (.imm 1, ()))
                                    (.let_ (Op.mk (.add i64) (.var p96.fst, .imm 1, ())) fun v88 =>
                                      .jump Js118.fst (.var v88.fst, ()))))) .nil)
                         (fun Js114 =>
                           .let_ (Op.mk (.cmp .eq i64 .bool rfl)
                               (.var nbits, .imm 3, ())) fun v85 =>
                           .jnz (.var v85.fst)
                             (.group (sig := [[.bool]])
                               (fun _ => .cons (fun p120 =>
                                 .jump Js114.fst (.var p120.fst, ())) .nil)
                               (fun Js120 =>
                                 .let_ (Op.mk (.sext 32 64) (.imm 0#32, ())) fun v86 =>
                                 .let_ (Op.mk (.mul i64) (.var v86.fst, .imm 4, ())) fun v87 =>
                                 .let_ (Op.mk (.add i64) (.var pTmp, .var v87.fst, ())) fun v88 =>
                                 .load i32 (.var v88.fst) fun ld89 =>
                                 .let_ (Op.mk (.sext 32 64) (.imm 1#32, ())) fun v90 =>
                                 .let_ (Op.mk (.mul i64) (.var v90.fst, .imm 4, ())) fun v91 =>
                                 .let_ (Op.mk (.add i64) (.var pTmp, .var v91.fst, ())) fun v92 =>
                                 .load i32 (.var v92.fst) fun ld93 =>
                                 .let_ (Op.mk (.sext 32 64) (.imm 2#32, ())) fun v94 =>
                                 .let_ (Op.mk (.mul i64) (.var v94.fst, .imm 4, ())) fun v95 =>
                                 .let_ (Op.mk (.add i64) (.var pTmp, .var v95.fst, ())) fun v96 =>
                                 .load i32 (.var v96.fst) fun ld97 =>
                                 .call (as := [i64, i32, i32, i32]) (bs := [.bool])
                                     "full_has_ternary"
                                     (.var hdr, .var ld89, .var ld93, .var ld97, ()) fun r98 =>
                                 .jnz (.var r98.fst)
                                   (.jump Js120.fst (.imm true, ()))
                                   (.jump Js120.fst (.imm false, ()))))
                             (.jump Js114.fst (.imm false, ())))) .nil)
                     (fun Js110 =>
                       .let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var nbits, .imm 4, ())) fun v85 =>
                       .jnz (.var v85.fst)
                         (.let_ (Op.mk (.sext 32 64) (.imm 3#32, ())) fun v86 =>
                          .let_ (Op.mk (.mul i64) (.var v86.fst, .imm 4, ())) fun v87 =>
                          .let_ (Op.mk (.add i64) (.var pTmp, .var v87.fst, ())) fun v88 =>
                          .let_ (Op.mk (.shl i32) (.var v3, .imm 1, ())) fun v89 =>
                          .let_ (Op.mk (.lshr i64) (.var p96.snd.fst, .imm 3, ())) fun v90 =>
                          .let_ (Op.mk (.and i64) (.var v90.fst, .imm 1, ())) fun v91 =>
                          .let_ (Op.mk (.trunc 64 32) (.var v91.fst, ())) fun v92 =>
                          .let_ (Op.mk (.or i32) (.var v89.fst, .var v92.fst, ())) fun v93 =>
                          .store (.var v93.fst) (.var v88.fst) (.jump Js110.fst ()))
                         (.jump Js110.fst ()))))))
                (.jump Js104.fst (.var p96.fst, ()))))
          (.jump Jvok (.var p96.fst, ()))) .nil)
    (fun Js96 => .jump Js96.fst (.var emitted_cl, .imm 0, ()))

private theorem emit_mat_m_loop_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s0 sr : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {c0 c1 c2 c3 emitted_cl wlim nbits rhs_bit : Val i64} {v0 v1 v2 v3 : Val i32}
    {rhs : Bool} {Jvok : Cont [i64]} {mr : Mem 64}
    (hHasTern : ∀ a m Q X, fullHasTernarySpec a m Q X →
      Γ "full_has_ternary" [i64, i32, i32, i32] [.bool] a m Q X)
    (hAddClause : ∀ a m Q X, fullAddClauseSpec a m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X)
    (hcv_le : s0.core.cur_vars ≤ c.max_vars) (hcv_lt : s0.core.cur_vars < 536870912)
    (h34 : nbits = 3#64 ∨ nbits = 4#64) (hnb_cv : nbits.toNat ≤ s0.core.cur_vars)
    (hwlim_nat : wlim.toNat = 2 ^ nbits.toNat)
    (hrb01 : rhs_bit = 0#64 ∨ rhs_bit = 1#64) (hrb_val : (rhs_bit != 0#64) = rhs)
    (hv0_cv : v0.toNat < s0.core.cur_vars) (hv1_cv : v1.toNat < s0.core.cur_vars)
    (hv2_cv : v2.toNat < s0.core.cur_vars) (hv01 : v0 ≠ v1) (hv02 : v0 ≠ v2) (hv12 : v1 ≠ v2)
    (hv3_ok : nbits = 4#64 → v3.toNat < s0.core.cur_vars ∧ v3 ≠ v0 ∧ v3 ≠ v1 ∧ v3 ≠ v2)
    (hv0_eq : s0.scratch.work_stk2[c0.toNat]?.getD 0#32 = v0)
    (hv1_eq : s0.scratch.work_stk2[c1.toNat]?.getD 0#32 = v1)
    (hv2_eq : s0.scratch.work_stk2[c2.toNat]?.getD 0#32 = v2)
    (hv3_eq : nbits = 4#64 → s0.scratch.work_stk2[c3.toNat]?.getD 0#32 = v3)
    (hsnd : XorVarsSound (cnfOfClauses F_cur)
      ((colsOf nbits c0 c1 c2 c3).map fun col => (s0.scratch.work_stk2[col]?.getD 0#32).toNat) rhs)
    (hok_r : EmitStateOk c F0 F_cur s0 sr) (hm_r : (FullMem c sr ⋆ R) mr)
    (hQ_ok : ∀ r s' m', EmitStateOk c F0 F_cur s0 s' → (r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hJvok : ∀ em' m', (∃ s', EmitStateOk c F0 F_cur s0 s' ∧ (FullMem c s' ⋆ R) m') →
      Jvok (em', ()) m') :
    wp Γ Q X (emitMatMLoopExpr c.hdr c.pTmp emitted_cl wlim nbits rhs_bit v0 v1 v2 v3 Jvok) mr := by
  dsimp only [emitMatMLoopExpr]
  let lim_nat := 2 ^ nbits.toNat
  have hnb3 : 3 ≤ nbits.toNat := by rcases h34 with rfl | rfl <;> decide
  have hnb_le4 : nbits.toNat ≤ 4 := by rcases h34 with rfl | rfl <;> decide
  have hlim_le : lim_nat ≤ 16 := by dsimp [lim_nat]; rcases h34 with rfl | rfl <;> decide
  refine wp_loop_inv
    (fun (_em_m, m_bv, ()) mm => ∃ sm,
      m_bv.toNat ≤ lim_nat ∧ EmitStateOk c F0 F_cur s0 sm ∧ (FullMem c sm ⋆ R) mm)
    (fun (_, m_bv, ()) _ => lim_nat - m_bv.toNat)
    (fun Jm hJm => by
      c0_hstraight
      exact hJm (emitted_cl, 0#64, ()) mr ⟨sr, Nat.zero_le _, hok_r, hm_r⟩)
    (fun Jm (em_m, m_bv, ()) mm ⟨sm, hm_le, hok_m, hm_m⟩ ihm => ?_)
  c0_hsplit
  · have hm_lt : m_bv.toNat < lim_nat := by dsimp only [lim_nat]; rw [← hwlim_nat]; bv_omega
    have hm_succ : (m_bv + 1#64).toNat = m_bv.toNat + 1 := by bv_omega
    refine wp_join_state1 (fun x : Val i64 => x)
      (fun em' m' => ∃ sm', EmitStateOk c F0 F_cur s0 sm' ∧ (FullMem c sm' ⋆ R) m')
      (fun _ em' m' ⟨sm', hok', hm'⟩ => by
        c0_hstraight
        exact ihm (em', m_bv + 1#64, ()) m' (by dsimp only; rw [hm_succ]; omega)
          ⟨sm', by rw [hm_succ]; omega, hok', hm'⟩)
      (fun Jmstep hJmstep => ?_)
    c0_hsplit
    · have hpar_ne : nibPar m_bv ≠ rhs_bit := by assumption
      have htmp_len : sm.core.tmp.length = c.max_vars := hok_m.1.1.1.tmp_len_arr
      let l0 : BitVec 32 := (v0 <<< (1 : Nat)) ||| (m_bv &&& 1#64).setWidth 32
      let l1 : BitVec 32 := (v1 <<< (1 : Nat)) ||| ((m_bv >>> (1 : Nat)) &&& 1#64).setWidth 32
      let l2 : BitVec 32 := (v2 <<< (1 : Nat)) ||| ((m_bv >>> (2 : Nat)) &&& 1#64).setWidth 32
      let l3 : BitVec 32 := (v3 <<< (1 : Nat)) ||| ((m_bv >>> (3 : Nat)) &&& 1#64).setWidth 32
      have ht0 : (0 : Nat) < sm.core.tmp.length := by omega
      have ht1 : (1 : Nat) < (sm.core.tmp.set 0 l0).length := by simp; omega
      have ht2 : (2 : Nat) < ((sm.core.tmp.set 0 l0).set 1 l1).length := by simp; omega
      c0_hstraight
      let tmp3 := ((sm.core.tmp.set 0 l0).set 1 l1).set 2 l2
      have htmp3_len : tmp3.length = c.max_vars := by simp [tmp3, htmp_len]
      refine wp_join0
        (fun mt => ∃ (tmp_c : List (BitVec 32)) (htl : tmp_c.length = c.max_vars),
          tmp_c[0]'(by omega) = l0 ∧ tmp_c[1]'(by omega) = l1 ∧ tmp_c[2]'(by omega) = l2 ∧
          (∀ h4 : nbits = 4#64, tmp_c[3]'(by
            rw [htl]; rw [h4] at hnb_cv; simp only [BitVec.toNat_ofNat] at hnb_cv; omega) = l3) ∧
          (FullMem c { sm with core := { sm.core with tmp := tmp_c } } ⋆ R) mt) ?_ ?_
      · rintro Jtmp mt ⟨tmp_c, htc_len, htc0, htc1, htc2, htc3, hmt⟩
        let st_c : FullState := { sm with core := { sm.core with tmp := tmp_c } }
        have hok_c : EmitStateOk c F0 F_cur s0 st_c :=
          emitStateOk_upd_tmp hok_m (htc_len.trans htmp_len.symm)
        have hl0_lt : l0.toNat < 2 * st_c.core.cur_vars := by
          have hl0 := bv32_mask_lit_toNat (v := v0) (m := m_bv) (i := 0) (by omega)
          have hl0' : l0.toNat = mkLit v0.toNat (!((m_bv.toNat >>> 0) % 2 == 1)) := by
            simpa [l0] using hl0
          rw [hl0', hok_c.2.1]; unfold mkLit; split <;> omega
        refine wp_join_state1 (fun x : Val .bool => x) (fun _skip msk => msk = mt) ?_ ?_
        · intro Jsk skip msk hmsk
          cases hmsk
          refine wp_join_state1 (fun x : Val i64 => x)
            (fun em' m' => ∃ sm', EmitStateOk c F0 F_cur s0 sm' ∧ (FullMem c sm' ⋆ R) m')
            (fun _ em' m' h => by c0_hstraight; exact hJmstep em' m' h)
            (fun Jadd hJadd => ?_)
          c0_hsplit
          · c0_hstraight; exact hJadd em_m mt ⟨st_c, hok_c, hmt⟩
          · have hnb32 : (nbits.setWidth 32).toNat = nbits.toNat :=
              bv64_toNat_setWidth32_lt (by omega)
            have hcl_ok := emit_tmp_clause_ok (cv := s0.core.cur_vars) (by omega) h34 hm_lt
              hrb01 hrb_val hpar_ne hv0_cv hv1_cv hv2_cv hv01 hv02 hv12 hv3_ok hv0_eq hv1_eq
              hv2_eq hv3_eq hsnd (by omega) (fun h4 => by
                rw [htc_len]; rw [h4] at hnb_cv; simp only [BitVec.toNat_ofNat] at hnb_cv; omega)
              htc0 htc1 htc2 htc3
            c0_hstraight
            c0_call hAddClause
            refine ⟨c, F0, F_cur, st_c, R, rfl, hok_c.1.1, hok_c.1.2.1, hok_c.1.2.2.2.2.2,
              by rw [hnb32]; omega, fun _ => by rw [hnb32, hok_c.2.1]; exact hcl_ok, hmt, ?_⟩
            have hge3 : ¬ (nbits.setWidth 32).toNat < 2 := by omega
            have hne2 : ¬ (nbits.setWidth 32).toNat = 2 := by omega
            rw [ite_eq_right hge3, ite_eq_right hne2]
            intro cr arena' alen' wvec' wstk' wlen' wusable' fred' ni' nr' wsort' ma sa _ hlen_a
              hw_a hrefs_a hnd_a _ hma
            have hok_a : EmitStateOk c F0 F_cur s0 sa :=
              emitStateOk_of_addClause3 hok_c sa rfl hlen_a hw_a hrefs_a hnd_a
            c0_hsplit
            · c0_hstraight; exact hQ_ok 1#64 sa ma hok_a (Or.inl rfl) (fun h => by cases h) hma
            · c0_hstraight; exact hJadd (em_m + 1#64) ma ⟨sa, hok_a, hma⟩
        · intro Jsk hJsk
          c0_hsplit
          · refine wp_join_state1 (fun x : Val .bool => x) (fun _sk msk => msk = mt)
              (fun _ sk msk h => by c0_hstraight; exact hJsk sk msk h)
              (fun Jht hJht => ?_)
            have ht0_c : (0 : Nat) < tmp_c.length := by omega
            have ht1_c : (1 : Nat) < tmp_c.length := by omega
            have ht2_c : (2 : Nat) < tmp_c.length := by omega
            c0_hstraight
            c0_call hHasTern
            refine ⟨c, F0, F_cur, st_c, R, rfl, hok_c.1.1, hok_c.1.2.1, hok_c.1.2.2.2.1,
              hok_c.2.2.1, by change tmp_c[0].toNat < _; rw [htc0]; exact hl0_lt, hmt,
              fun _ _ => ?_⟩
            c0_hsplit
            · c0_hstraight; exact hJht true mt rfl
            · c0_hstraight; exact hJht false mt rfl
          · c0_hstraight; exact hJsk false mt rfl
      · intro Jtmp hJtmp
        c0_hsplit
        · have hnb4 : nbits = 4#64 := by assumption
          have ht3 : (3 : Nat) < tmp3.length := by
            rw [htmp3_len]; rw [hnb4] at hnb_cv; simp only [BitVec.toNat_ofNat] at hnb_cv; omega
          c0_hstraight
          refine hJtmp _ ⟨tmp3.set 3 l3, by simp [htmp3_len],
            by simp [tmp3, List.getElem_set_ne], by simp [tmp3, List.getElem_set_ne],
            by simp [tmp3, List.getElem_set_ne], fun _ => by simp [List.getElem_set_self], hm⟩
        · have hnb_ne4 : nbits ≠ 4#64 := by assumption
          c0_hstraight
          exact hJtmp _ ⟨tmp3, htmp3_len,
            by simp [tmp3, List.getElem_set_ne], by simp [tmp3, List.getElem_set_ne],
            by simp [tmp3, List.getElem_set_self], fun h => absurd h hnb_ne4, hm⟩
    · c0_hstraight; exact hJmstep em_m mm ⟨sm, hok_m, hm_m⟩
  · c0_hstraight; exact hJvok em_m mm ⟨sm, hok_m, hm_m⟩

private def emitMatN1Expr (hdr pWorkStk2 cur_vars_bv ncols emitted_cl rhs_bit c0 nbits : Val i64)
    (Jem1 : Cont [i64]) (Jelse1 : Cont []) : Expr Val Cont [i64] :=
  .let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var nbits, .imm 1, ())) fun v25 =>
  .jnz (.var v25.fst)
    (.let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var c0, .var ncols, ())) fun v26 =>
     .jnz (.var v26.fst)
       (.let_ (Op.mk (.mul i64) (.var c0, .imm 4, ())) fun v27 =>
        .let_ (Op.mk (.add i64) (.var pWorkStk2, .var v27.fst, ())) fun v28 =>
        .load i32 (.var v28.fst) fun ld29 =>
        .group (sig := [[]])
          (fun _ => .cons (fun _ => .jump Jem1 (.var emitted_cl, ())) .nil)
          (fun Js40 =>
            .let_ (Op.mk (.zext 32 64) (.var ld29, ())) fun v30 =>
            .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var v30.fst, .var cur_vars_bv, ())) fun v31 =>
            .jnz (.var v31.fst)
              (.let_ (Op.mk (.shl i32) (.var ld29, .imm 1, ())) fun v32 =>
               .let_ (Op.mk (.xor i64) (.var rhs_bit, .imm 1, ())) fun v33 =>
               .let_ (Op.mk (.trunc 64 32) (.var v33.fst, ())) fun v34 =>
               .let_ (Op.mk (.or i32) (.var v32.fst, .var v34.fst, ())) fun v35 =>
               .call (as := [i64, i32]) (bs := [.bool]) "full_add_unit"
                   (.var hdr, .var v35.fst, ()) fun r36 =>
               .jnz (.var r36.fst) (.jump Js40.fst ()) (.ret (.imm 20, ())))
              (.jump Js40.fst ())))
       (.jump Jelse1 ()))
    (.jump Jelse1 ())

private theorem emit_mat_n1_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sr : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {rbase_nat : Nat}
    {ncols emitted_cl rhs_bit c0 c1 c2 c3 nbits : Val i64} {Jem1 : Cont [i64]}
    {Jelse1 : Cont []} {mr : Mem 64}
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hcv_le : s0.core.cur_vars ≤ c.max_vars) (hcv_lt : s0.core.cur_vars < 536870912)
    (hnc_cv : ncols.toNat ≤ s0.core.cur_vars)
    (hc2v_lt : ∀ col < ncols.toNat, (s0.scratch.work_stk2[col]?.getD 0#32).toNat < s0.core.cur_vars)
    (hsound_r : XorPackedRowSound (cnfOfClauses F_cur) s0.scratch.work_stk2
      s0.scratch.scratch_buf rbase_nat ncols.toNat)
    (hrhs_bit_01 : rhs_bit = 0#64 ∨ rhs_bit = 1#64)
    (hrhs_bit_val : (rhs_bit != 0#64) = rowBit s0.scratch.scratch_buf rbase_nat ncols.toNat)
    (hcols_ok : nbits.toNat ≤ 4 →
      (∀ col ∈ colsOf nbits c0 c1 c2 c3, col < ncols.toNat) ∧
      (colsOf nbits c0 c1 c2 c3).Pairwise (· < ·) ∧
      (∀ col < ncols.toNat,
        rowBit s0.scratch.scratch_buf rbase_nat col = true ↔ col ∈ colsOf nbits c0 c1 c2 c3))
    (hok_r : EmitStateOk c F0 F_cur s0 sr) (hm_r : (FullMem c sr ⋆ R) mr)
    (hQ_ok : ∀ r s' m', EmitStateOk c F0 F_cur s0 s' → (r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hJem1 : ∀ em' m', (∃ s', EmitStateOk c F0 F_cur s0 s' ∧ (FullMem c s' ⋆ R) m') →
      Jem1 (em', ()) m')
    (hJelse1 : ∀ m', m' = mr → Jelse1 () m') :
    wp Γ Q X (emitMatN1Expr c.hdr c.pWorkStk2 (BitVec.ofNat 64 s0.core.cur_vars)
      ncols emitted_cl rhs_bit c0 nbits Jem1 Jelse1) mr := by
  dsimp only [emitMatN1Expr]
  let c2v0 := s0.scratch.work_stk2
  c0_hsplit
  · have hnb1 : nbits = 1#64 := by assumption
    c0_hsplit
    · have hc0_lt : c0.toNat < ncols.toNat := by bv_omega
      have hc2v_len : sr.scratch.work_stk2.length = 2 * c.max_vars := hok_r.1.1.2.work_stk2_len
      have hc0_l : c0.toNat < sr.scratch.work_stk2.length := by omega
      c0_hstraight
      generalize hv0 : (sr.scratch.work_stk2[c0.toNat]'hc0_l : BitVec 32) = v0
      have hv0_eq : c2v0[c0.toNat]?.getD 0#32 = v0 := by
        dsimp only [c2v0]; rw [← hok_r.2.2.2.2.2.2.1, List.getElem?_eq_getElem hc0_l, hv0]; rfl
      refine wp_join0
        (fun m' => ∃ s', EmitStateOk c F0 F_cur s0 s' ∧ (FullMem c s' ⋆ R) m')
        (fun _ m' h => by c0_hstraight; exact hJem1 emitted_cl m' h)
        (fun Ju hJu => ?_)
      c0_hsplit
      · have hv0_cv : v0.toNat < s0.core.cur_vars := by rw [← hv0_eq]; exact hc2v_lt c0.toNat hc0_lt
        have ⟨hcol_lt, hcol_pw, hcol_bits⟩ := hcols_ok (by rw [hnb1]; decide)
        rw [hnb1] at hcol_lt hcol_pw hcol_bits
        have ⟨hlit_lt, hent_u⟩ := emit_unit_lit_ok (by omega) hv0_cv hv0_eq
          hrhs_bit_01 hrhs_bit_val hcol_lt hcol_pw hcol_bits hsound_r
        c0_hstraight
        c0_call hAddUnit
        refine ⟨c, F0, F_cur, sr, R, rfl, hok_r.1.1, hok_r.1.2.1,
          fun _ => hent_u, hm_r, fun ok vals' flags' lvl' rsns' trl' tp' te' prop'
            cl' unass' unfl' inc' phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m'
            hlen' hw' hcl' hfail1 _ hm' => ?_⟩
        let s' : FullState := { sr with
          core := { sr.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns',
            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
            cur_level := cl', unassigned := unass', unflushed := unfl', inconsistent := inc' }
          scratch := { sr.scratch with
            phases := phases', target_assigned := ta', best_assigned := ba',
            phases_target := pt', phases_best := pb', heap := hp', pos := ps',
            heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' } }
        have hok' : EmitStateOk c F0 F_cur s0 s' :=
          emitStateOk_of_addUnit hok_r s' rfl hlen' hw' hcl'
        c0_hsplit
        · c0_hstraight; exact hJu m' ⟨s', hok', hm'⟩
        · have hok_f : ok = false := by cases ok <;> simp_all
          c0_hstraight
          exact hQ_ok 20#64 s' m' hok' (Or.inr rfl)
            (fun _ => (hfail1 (by rw [hok_r.2.1]; exact hlit_lt) hok_f).1) hm'
      · c0_hstraight; exact hJu mr ⟨sr, hok_r, hm_r⟩
    · c0_hstraight; exact hJelse1 mr rfl
  · c0_hstraight; exact hJelse1 mr rfl

private def emitMatN2Expr
    (hdr pWorkStk2 cur_vars_bv ncols emitted_cl rhs_bit c0 c1 nbits : Val i64)
    (Jem2 : Cont [i64]) (Jelse2 : Cont []) : Expr Val Cont [i64] :=
  .let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var nbits, .imm 2, ())) fun v25 =>
  .jnz (.var v25.fst)
    (.let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var c0, .var ncols, ())) fun v26 =>
     .jnz (.var v26.fst)
       (.let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var c1, .var ncols, ())) fun v27 =>
        .jnz (.var v27.fst)
          (.let_ (Op.mk (.mul i64) (.var c0, .imm 4, ())) fun v28 =>
           .let_ (Op.mk (.add i64) (.var pWorkStk2, .var v28.fst, ())) fun v29 =>
           .load i32 (.var v29.fst) fun ld30 =>
           .let_ (Op.mk (.mul i64) (.var c1, .imm 4, ())) fun v31 =>
           .let_ (Op.mk (.add i64) (.var pWorkStk2, .var v31.fst, ())) fun v32 =>
           .load i32 (.var v32.fst) fun ld33 =>
           .group (sig := [[]])
             (fun _ => .cons (fun _ => .jump Jem2 (.var emitted_cl, ())) .nil)
             (fun Js50 =>
               .let_ (Op.mk (.zext 32 64) (.var ld30, ())) fun v34 =>
               .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var v34.fst, .var cur_vars_bv, ()))
                 fun v35 =>
               .jnz (.var v35.fst)
                 (.let_ (Op.mk (.zext 32 64) (.var ld33, ())) fun v36 =>
                  .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var v36.fst, .var cur_vars_bv, ()))
                    fun v37 =>
                  .jnz (.var v37.fst)
                    (.let_ (Op.mk (.shl i32) (.var ld30, .imm 1, ())) fun v38 =>
                     .let_ (Op.mk (.trunc 64 32) (.var rhs_bit, ())) fun v39 =>
                     .let_ (Op.mk (.or i32) (.var v38.fst, .var v39.fst, ())) fun v40 =>
                     .let_ (Op.mk (.shl i32) (.var ld33, .imm 1, ())) fun v41 =>
                     .let_ (Op.mk (.or i32) (.var v41.fst, .imm 1, ())) fun v42 =>
                     .group (sig := [[]])
                       (fun _ => .cons (fun _ =>
                         .let_ (Op.mk (.shl i32) (.var ld30, .imm 1, ())) fun v43 =>
                         .let_ (Op.mk (.xor i64) (.var rhs_bit, .imm 1, ())) fun v44 =>
                         .let_ (Op.mk (.trunc 64 32) (.var v44.fst, ())) fun v45 =>
                         .let_ (Op.mk (.or i32) (.var v43.fst, .var v45.fst, ())) fun v46 =>
                         .let_ (Op.mk (.shl i32) (.var ld33, .imm 1, ())) fun v47 =>
                         .group (sig := [[]])
                           (fun _ => .cons (fun _ => .jump Js50.fst ()) .nil)
                           (fun Js64 => emitMatBinBranchExpr hdr v46.fst v47.fst Js64.fst)) .nil)
                       (fun Js60 => emitMatBinBranchExpr hdr v40.fst v42.fst Js60.fst))
                    (.jump Js50.fst ()))
                 (.jump Js50.fst ())))
          (.jump Jelse2 ()))
       (.jump Jelse2 ()))
    (.jump Jelse2 ())

private theorem emit_mat_n2_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sr : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {rbase_nat : Nat}
    {ncols emitted_cl rhs_bit c0 c1 c2 c3 nbits : Val i64} {Jem2 : Cont [i64]}
    {Jelse2 : Cont []} {mr : Mem 64}
    (hHasBin : ∀ a m Q X, fullHasBinSpec a m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hcv_le : s0.core.cur_vars ≤ c.max_vars) (hcv_lt : s0.core.cur_vars < 536870912)
    (hnc_cv : ncols.toNat ≤ s0.core.cur_vars)
    (hc2v_lt : ∀ col < ncols.toNat, (s0.scratch.work_stk2[col]?.getD 0#32).toNat < s0.core.cur_vars)
    (hsound_r : XorPackedRowSound (cnfOfClauses F_cur) s0.scratch.work_stk2
      s0.scratch.scratch_buf rbase_nat ncols.toNat)
    (hrhs_bit_01 : rhs_bit = 0#64 ∨ rhs_bit = 1#64)
    (hrhs_bit_val : (rhs_bit != 0#64) = rowBit s0.scratch.scratch_buf rbase_nat ncols.toNat)
    (hcols_ok : nbits.toNat ≤ 4 →
      (∀ col ∈ colsOf nbits c0 c1 c2 c3, col < ncols.toNat) ∧
      (colsOf nbits c0 c1 c2 c3).Pairwise (· < ·) ∧
      (∀ col < ncols.toNat,
        rowBit s0.scratch.scratch_buf rbase_nat col = true ↔ col ∈ colsOf nbits c0 c1 c2 c3))
    (hok_r : EmitStateOk c F0 F_cur s0 sr) (hm_r : (FullMem c sr ⋆ R) mr)
    (hQ_ok : ∀ r s' m', EmitStateOk c F0 F_cur s0 s' → (r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hJem2 : ∀ em' m', (∃ s', EmitStateOk c F0 F_cur s0 s' ∧ (FullMem c s' ⋆ R) m') →
      Jem2 (em', ()) m')
    (hJelse2 : ∀ m', m' = mr → Jelse2 () m') :
    wp Γ Q X (emitMatN2Expr c.hdr c.pWorkStk2 (BitVec.ofNat 64 s0.core.cur_vars)
      ncols emitted_cl rhs_bit c0 c1 nbits Jem2 Jelse2) mr := by
  dsimp only [emitMatN2Expr]
  let c2v0 := s0.scratch.work_stk2
  c0_hsplit
  · have hnb2 : nbits = 2#64 := by assumption
    c0_hsplit
    · have hc0_lt : c0.toNat < ncols.toNat := by bv_omega
      c0_hsplit
      · have hc1_lt : c1.toNat < ncols.toNat := by bv_omega
        have hc2v_len : sr.scratch.work_stk2.length = 2 * c.max_vars := hok_r.1.1.2.work_stk2_len
        have hc0_l : c0.toNat < sr.scratch.work_stk2.length := by omega
        have hc1_l : c1.toNat < sr.scratch.work_stk2.length := by omega
        c0_hstraight
        generalize hv0 : (sr.scratch.work_stk2[c0.toNat]'hc0_l : BitVec 32) = v0
        generalize hv1 : (sr.scratch.work_stk2[c1.toNat]'hc1_l : BitVec 32) = v1
        have hv0_eq : c2v0[c0.toNat]?.getD 0#32 = v0 := by
          dsimp only [c2v0]; rw [← hok_r.2.2.2.2.2.2.1, List.getElem?_eq_getElem hc0_l, hv0]; rfl
        have hv1_eq : c2v0[c1.toNat]?.getD 0#32 = v1 := by
          dsimp only [c2v0]; rw [← hok_r.2.2.2.2.2.2.1, List.getElem?_eq_getElem hc1_l, hv1]; rfl
        refine wp_join0
          (fun m' => ∃ s', EmitStateOk c F0 F_cur s0 s' ∧ (FullMem c s' ⋆ R) m')
          (fun _ m' h => by c0_hstraight; exact hJem2 emitted_cl m' h)
          (fun Jb2 hJb2 => ?_)
        c0_hsplit
        · c0_hsplit
          · have hv0_cv : v0.toNat < s0.core.cur_vars := by
              rw [← hv0_eq]; exact hc2v_lt c0.toNat hc0_lt
            have hv1_cv : v1.toNat < s0.core.cur_vars := by
              rw [← hv1_eq]; exact hc2v_lt c1.toNat hc1_lt
            have ⟨hcol_lt, hcol_pw, hcol_bits⟩ := hcols_ok (by rw [hnb2]; decide)
            rw [hnb2] at hcol_lt hcol_pw hcol_bits
            have ⟨hent1, hent2⟩ := emit_bin_lits_ok (by omega) hv0_cv hv1_cv
              hv0_eq hv1_eq hrhs_bit_01 hrhs_bit_val hcol_lt hcol_pw hcol_bits hsound_r
            c0_hstraight
            refine wp_join0
              (fun m1 => ∃ s1, EmitStateOk c F0 F_cur s0 s1 ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
            · rintro Jb1 m1 ⟨s1, hok1, hm1⟩
              c0_hstraight
              refine wp_join0
                (fun m2 => ∃ s2, EmitStateOk c F0 F_cur s0 s2 ∧ (FullMem c s2 ⋆ R) m2)
                (fun _ m2 h => by c0_hstraight; exact hJb2 m2 h)
                (fun Jb2i hJb2i => ?_)
              exact emit_mat_bin_branch_wp hHasBin hAddBin hok1 hent2 hm1 hQ_ok
                (fun m2 h => hJb2i m2 h)
            · intro Jb1 hJb1
              exact emit_mat_bin_branch_wp hHasBin hAddBin hok_r hent1 hm_r hQ_ok
                (fun m1 h => hJb1 m1 h)
          · c0_hstraight; exact hJb2 mr ⟨sr, hok_r, hm_r⟩
        · c0_hstraight; exact hJb2 mr ⟨sr, hok_r, hm_r⟩
      · c0_hstraight; exact hJelse2 mr rfl
    · c0_hstraight; exact hJelse2 mr rfl
  · c0_hstraight; exact hJelse2 mr rfl

private def emitMatN34Expr
    (hdr pWorkStk2 pTmp cur_vars_bv emitted_cl rhs_bit c0 c1 c2 c3 nbits : Val i64)
    (Jem34 : Cont [i64]) : Expr Val Cont [i64] :=
  .group (sig := [[]])
    (fun _ => .cons (fun _ =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var emitted_cl, .imm 64, ())) fun v25 =>
      .jnz (.var v25.fst)
        (.let_ (Op.mk (.cmp .ule i64 .bool rfl) (.var nbits, .var cur_vars_bv, ())) fun v26 =>
         .jnz (.var v26.fst)
           (.let_ (Op.mk (.add i64) (.var hdr, .imm 48, ())) fun v27 =>
            .load i64 (.var v27.fst) fun ld28 =>
            .let_ (Op.mk (.add i64) (.var ld28, .imm 64, ())) fun v29 =>
            .let_ (Op.mk (.add i64) (.var hdr, .imm 32, ())) fun v30 =>
            .load i64 (.var v30.fst) fun ld31 =>
            .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var v29.fst, .var ld31, ())) fun v32 =>
            .jnz (.var v32.fst)
              (.let_ (Op.mk (.add i64) (.var hdr, .imm 56, ())) fun v33 =>
               .load i64 (.var v33.fst) fun ld34 =>
               .let_ (Op.mk (.add i64) (.var ld34, .imm 64, ())) fun v35 =>
               .let_ (Op.mk (.add i64) (.var hdr, .imm 40, ())) fun v36 =>
               .load i64 (.var v36.fst) fun ld37 =>
               .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var v35.fst, .var ld37, ())) fun v38 =>
               .jnz (.var v38.fst)
                 (.let_ (Op.mk (.mul i64) (.var c0, .imm 4, ())) fun v39 =>
                  .let_ (Op.mk (.add i64) (.var pWorkStk2, .var v39.fst, ())) fun v40 =>
                  .load i32 (.var v40.fst) fun ld41 =>
                  .let_ (Op.mk (.mul i64) (.var c1, .imm 4, ())) fun v42 =>
                  .let_ (Op.mk (.add i64) (.var pWorkStk2, .var v42.fst, ())) fun v43 =>
                  .load i32 (.var v43.fst) fun ld44 =>
                  .let_ (Op.mk (.mul i64) (.var c2, .imm 4, ())) fun v45 =>
                  .let_ (Op.mk (.add i64) (.var pWorkStk2, .var v45.fst, ())) fun v46 =>
                  .load i32 (.var v46.fst) fun ld47 =>
                  .group (sig := [[i32]])
                    (fun _ => .cons (fun p62 =>
                      .group (sig := [[i64]])
                        (fun _ => .cons (fun p66 => .jump Jem34 (.var p66.fst, ())) .nil)
                        (fun Js66 =>
                          .let_ (Op.mk (.zext 32 64) (.var ld41, ())) fun v48 =>
                          .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                              (.var v48.fst, .var cur_vars_bv, ())) fun v49 =>
                          .jnz (.var v49.fst)
                            (.let_ (Op.mk (.zext 32 64) (.var ld44, ())) fun v50 =>
                             .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                 (.var v50.fst, .var cur_vars_bv, ())) fun v51 =>
                             .jnz (.var v51.fst)
                               (.let_ (Op.mk (.zext 32 64) (.var ld47, ())) fun v52 =>
                                .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                    (.var v52.fst, .var cur_vars_bv, ())) fun v53 =>
                                .jnz (.var v53.fst)
                                  (.let_ (Op.mk (.cmp .ne i32 .bool rfl)
                                      (.var ld41, .var ld44, ())) fun v54 =>
                                   .jnz (.var v54.fst)
                                     (.let_ (Op.mk (.cmp .ne i32 .bool rfl)
                                         (.var ld41, .var ld47, ())) fun v55 =>
                                      .jnz (.var v55.fst)
                                        (.let_ (Op.mk (.cmp .ne i32 .bool rfl)
                                            (.var ld44, .var ld47, ())) fun v56 =>
                                         .jnz (.var v56.fst)
                                           (.group (sig := [[]])
                                             (fun _ => .cons (fun _ =>
                                               .let_ (Op.mk (.shl i64) (.imm 1, .var nbits, ()))
                                                 fun v57 =>
                                               emitMatMLoopExpr hdr pTmp emitted_cl v57.fst nbits
                                                 rhs_bit ld41 ld44 ld47 p62.fst Js66.fst) .nil)
                                             (fun Js92 =>
                                               .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                                   (.var nbits, .imm 4, ())) fun v57 =>
                                               .jnz (.var v57.fst) (.jump Js92.fst ())
                                                 (.let_ (Op.mk (.zext 32 64) (.var p62.fst, ()))
                                                    fun v58 =>
                                                  .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                                      (.var v58.fst, .var cur_vars_bv, ()))
                                                    fun v59 =>
                                                  .jnz (.var v59.fst)
                                                    (.let_ (Op.mk (.cmp .ne i32 .bool rfl)
                                                        (.var p62.fst, .var ld41, ())) fun v60 =>
                                                     .jnz (.var v60.fst)
                                                       (.let_ (Op.mk (.cmp .ne i32 .bool rfl)
                                                           (.var p62.fst, .var ld44, ())) fun v61 =>
                                                        .jnz (.var v61.fst)
                                                          (.let_ (Op.mk (.cmp .ne i32 .bool rfl)
                                                              (.var p62.fst, .var ld47, ()))
                                                            fun v62 =>
                                                           .jnz (.var v62.fst)
                                                             (.jump Js92.fst ())
                                                             (.jump Js66.fst (.var emitted_cl, ())))
                                                          (.jump Js66.fst (.var emitted_cl, ())))
                                                       (.jump Js66.fst (.var emitted_cl, ())))
                                                    (.jump Js66.fst (.var emitted_cl, ())))))
                                           (.jump Js66.fst (.var emitted_cl, ())))
                                        (.jump Js66.fst (.var emitted_cl, ())))
                                     (.jump Js66.fst (.var emitted_cl, ())))
                                  (.jump Js66.fst (.var emitted_cl, ())))
                               (.jump Js66.fst (.var emitted_cl, ())))
                            (.jump Js66.fst (.var emitted_cl, ())))) .nil)
                    (fun Js62 =>
                      .let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var nbits, .imm 4, ())) fun v48 =>
                      .jnz (.var v48.fst)
                        (.let_ (Op.mk (.mul i64) (.var c3, .imm 4, ())) fun v49 =>
                         .let_ (Op.mk (.add i64) (.var pWorkStk2, .var v49.fst, ())) fun v50 =>
                         .load i32 (.var v50.fst) fun ld51 =>
                         .jump Js62.fst (.var ld51, ()))
                        (.jump Js62.fst (.imm 0#32, ()))))
                 (.jump Jem34 (.var emitted_cl, ())))
              (.jump Jem34 (.var emitted_cl, ())))
           (.jump Jem34 (.var emitted_cl, ())))
        (.jump Jem34 (.var emitted_cl, ()))) .nil)
    (fun Js42 =>
      .let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var nbits, .imm 3, ())) fun v25 =>
      .jnz (.var v25.fst) (.jump Js42.fst ())
        (.let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var nbits, .imm 4, ())) fun v26 =>
         .jnz (.var v26.fst) (.jump Js42.fst ()) (.jump Jem34 (.var emitted_cl, ()))))

private theorem emit_mat_n34_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sr : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {rbase_nat : Nat}
    {ncols emitted_cl rhs_bit c0 c1 c2 c3 nbits : Val i64} {Jem34 : Cont [i64]} {mr : Mem 64}
    (hHasTern : ∀ a m Q X, fullHasTernarySpec a m Q X →
      Γ "full_has_ternary" [i64, i32, i32, i32] [.bool] a m Q X)
    (hAddClause : ∀ a m Q X, fullAddClauseSpec a m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X)
    (hcv_le : s0.core.cur_vars ≤ c.max_vars) (hcv_lt : s0.core.cur_vars < 536870912)
    (hnc_cv : ncols.toNat ≤ s0.core.cur_vars)
    (hc2v_lt : ∀ col < ncols.toNat, (s0.scratch.work_stk2[col]?.getD 0#32).toNat < s0.core.cur_vars)
    (hsound_r : XorPackedRowSound (cnfOfClauses F_cur) s0.scratch.work_stk2
      s0.scratch.scratch_buf rbase_nat ncols.toNat)
    (hrhs_bit_01 : rhs_bit = 0#64 ∨ rhs_bit = 1#64)
    (hrhs_bit_val : (rhs_bit != 0#64) = rowBit s0.scratch.scratch_buf rbase_nat ncols.toNat)
    (hcols_ok : nbits.toNat ≤ 4 →
      (∀ col ∈ colsOf nbits c0 c1 c2 c3, col < ncols.toNat) ∧
      (colsOf nbits c0 c1 c2 c3).Pairwise (· < ·) ∧
      (∀ col < ncols.toNat,
        rowBit s0.scratch.scratch_buf rbase_nat col = true ↔ col ∈ colsOf nbits c0 c1 c2 c3))
    (hok_r : EmitStateOk c F0 F_cur s0 sr) (hm_r : (FullMem c sr ⋆ R) mr)
    (hQ_ok : ∀ r s' m', EmitStateOk c F0 F_cur s0 s' → (r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hJem34 : ∀ em' m', (∃ s', EmitStateOk c F0 F_cur s0 s' ∧ (FullMem c s' ⋆ R) m') →
      Jem34 (em', ()) m') :
    wp Γ Q X (emitMatN34Expr c.hdr c.pWorkStk2 c.pTmp (BitVec.ofNat 64 s0.core.cur_vars)
      emitted_cl rhs_bit c0 c1 c2 c3 nbits Jem34) mr := by
  dsimp only [emitMatN34Expr]
  let c2v0 := s0.scratch.work_stk2
  refine wp_join0 (fun m' => m' = mr ∧ (nbits = 3#64 ∨ nbits = 4#64)) ?_ ?_
  · rintro J34 m' ⟨hm', h34⟩; cases hm'
    have hnb_le4 : nbits.toNat ≤ 4 := by rcases h34 with rfl | rfl <;> decide
    have ⟨hcol_lt, hcol_pw, hcol_bits⟩ := hcols_ok hnb_le4
    have hsnd_cols := xorVarsSound_of_packedRow hcol_lt
      (hcol_pw.imp fun h => Nat.ne_of_lt h) hcol_bits hsound_r
    c0_hsplit
    · c0_hsplit
      · have hnb_cv : nbits.toNat ≤ s0.core.cur_vars := by
          have hcv_bv : (BitVec.ofNat 64 s0.core.cur_vars).toNat = s0.core.cur_vars :=
            bv64_ofNat_toNat (by omega)
          bv_omega
        c0_hstraight
        c0_hsplit
        · c0_hstraight
          c0_hsplit
          · have hc0_lt : c0.toNat < ncols.toNat := hcol_lt c0.toNat (by
              rcases h34 with rfl | rfl <;> simp [colsOf])
            have hc1_lt : c1.toNat < ncols.toNat := hcol_lt c1.toNat (by
              rcases h34 with rfl | rfl <;> simp [colsOf])
            have hc2_lt : c2.toNat < ncols.toNat := hcol_lt c2.toNat (by
              rcases h34 with rfl | rfl <;> simp [colsOf])
            have hc2v_len : sr.scratch.work_stk2.length = 2 * c.max_vars :=
              hok_r.1.1.2.work_stk2_len
            have hc0_l : c0.toNat < sr.scratch.work_stk2.length := by omega
            have hc1_l : c1.toNat < sr.scratch.work_stk2.length := by omega
            have hc2_l : c2.toNat < sr.scratch.work_stk2.length := by omega
            c0_hstraight
            generalize hv0 : (sr.scratch.work_stk2[c0.toNat]'hc0_l : BitVec 32) = v0
            generalize hv1 : (sr.scratch.work_stk2[c1.toNat]'hc1_l : BitVec 32) = v1
            generalize hv2 : (sr.scratch.work_stk2[c2.toNat]'hc2_l : BitVec 32) = v2
            have hv0_eq : c2v0[c0.toNat]?.getD 0#32 = v0 := by
              dsimp only [c2v0]; rw [← hok_r.2.2.2.2.2.2.1, List.getElem?_eq_getElem hc0_l, hv0]
              rfl
            have hv1_eq : c2v0[c1.toNat]?.getD 0#32 = v1 := by
              dsimp only [c2v0]; rw [← hok_r.2.2.2.2.2.2.1, List.getElem?_eq_getElem hc1_l, hv1]
              rfl
            have hv2_eq : c2v0[c2.toNat]?.getD 0#32 = v2 := by
              dsimp only [c2v0]; rw [← hok_r.2.2.2.2.2.2.1, List.getElem?_eq_getElem hc2_l, hv2]
              rfl
            refine wp_join_state1 (fun x : Val i32 => x)
              (fun v3 mv => mv = mr ∧ (nbits = 4#64 → c2v0[c3.toNat]?.getD 0#32 = v3)) ?_ ?_
            · intro Jv3 v3 mv ⟨hmv, hv3_eq⟩; cases hmv
              refine wp_join_state1 (fun x : Val i64 => x)
                (fun em' m' => ∃ s', EmitStateOk c F0 F_cur s0 s' ∧ (FullMem c s' ⋆ R) m')
                (fun _ em' m' h => by c0_hstraight; exact hJem34 em' m' h)
                (fun Jvok hJvok => ?_)
              have hv0_cv : v0.toNat < s0.core.cur_vars := by
                rw [← hv0_eq]; exact hc2v_lt c0.toNat hc0_lt
              have hv1_cv : v1.toNat < s0.core.cur_vars := by
                rw [← hv1_eq]; exact hc2v_lt c1.toNat hc1_lt
              have hv2_cv : v2.toNat < s0.core.cur_vars := by
                rw [← hv2_eq]; exact hc2v_lt c2.toNat hc2_lt
              c0_hsplit
              · c0_hsplit
                · c0_hsplit
                  · c0_hsplit
                    · have hv01 : v0 ≠ v1 := by assumption
                      c0_hsplit
                      · have hv02 : v0 ≠ v2 := by assumption
                        c0_hsplit
                        · have hv12 : v1 ≠ v2 := by assumption
                          refine wp_join0
                            (fun m' => m' = mr ∧ (nbits = 4#64 →
                              v3.toNat < s0.core.cur_vars ∧ v3 ≠ v0 ∧ v3 ≠ v1 ∧ v3 ≠ v2)) ?_ ?_
                          · rintro Jall m' ⟨hm', hv3_ok⟩; cases hm'
                            have hlim_nat : (1#64 <<< (nbits.toNat % 64)).toNat = 2 ^ nbits.toNat :=
                              by rcases h34 with rfl | rfl <;> decide
                            c0_hstraight
                            generalize hwlim :
                              ((1 : BitVec 64) <<< (nbits.toNat % 64) : BitVec 64) = wlim
                            have hwlim_nat : wlim.toNat = 2 ^ nbits.toNat := by
                              rw [← hwlim]; exact hlim_nat
                            exact emit_mat_m_loop_wp hHasTern hAddClause hcv_le hcv_lt h34 hnb_cv
                              hwlim_nat hrhs_bit_01 hrhs_bit_val hv0_cv hv1_cv hv2_cv hv01 hv02
                              hv12 hv3_ok hv0_eq hv1_eq hv2_eq hv3_eq hsnd_cols hok_r hm_r hQ_ok
                              hJvok
                          · intro Jall hJall
                            c0_hsplit
                            · have hnb_ne4 : nbits ≠ 4#64 := by bv_omega
                              c0_hstraight
                              exact hJall mr ⟨rfl, fun h => absurd h hnb_ne4⟩
                            · have hnb4 : nbits = 4#64 := by
                                rcases h34 with rfl | rfl
                                · exfalso; bv_omega
                                · rfl
                              have hv3_cv : v3.toNat < s0.core.cur_vars := by
                                rw [← hv3_eq hnb4]
                                exact hc2v_lt c3.toNat
                                  (hcol_lt c3.toNat (by rw [hnb4]; simp [colsOf]))
                              c0_hsplit
                              · c0_hsplit
                                · c0_hsplit
                                  · c0_hsplit
                                    · c0_hstraight
                                      exact hJall mr ⟨rfl, fun _ =>
                                        ⟨hv3_cv, by assumption, by assumption, by assumption⟩⟩
                                    · c0_hstraight; exact hJvok emitted_cl mr ⟨sr, hok_r, hm_r⟩
                                  · c0_hstraight; exact hJvok emitted_cl mr ⟨sr, hok_r, hm_r⟩
                                · c0_hstraight; exact hJvok emitted_cl mr ⟨sr, hok_r, hm_r⟩
                              · c0_hstraight; exact hJvok emitted_cl mr ⟨sr, hok_r, hm_r⟩
                        · c0_hstraight; exact hJvok emitted_cl mr ⟨sr, hok_r, hm_r⟩
                      · c0_hstraight; exact hJvok emitted_cl mr ⟨sr, hok_r, hm_r⟩
                    · c0_hstraight; exact hJvok emitted_cl mr ⟨sr, hok_r, hm_r⟩
                  · c0_hstraight; exact hJvok emitted_cl mr ⟨sr, hok_r, hm_r⟩
                · c0_hstraight; exact hJvok emitted_cl mr ⟨sr, hok_r, hm_r⟩
              · c0_hstraight; exact hJvok emitted_cl mr ⟨sr, hok_r, hm_r⟩
            · intro Jv3 hJv3
              c0_hsplit
              · have hnb4 : nbits = 4#64 := by assumption
                have hc3_lt : c3.toNat < ncols.toNat :=
                  hcol_lt c3.toNat (by rw [hnb4]; simp [colsOf])
                have hc3_l : c3.toNat < sr.scratch.work_stk2.length := by omega
                c0_hstraight
                exact hJv3 (sr.scratch.work_stk2[c3.toNat]'hc3_l) mr
                  ⟨rfl, fun _ => by
                    dsimp only [c2v0]
                    rw [← hok_r.2.2.2.2.2.2.1, List.getElem?_eq_getElem hc3_l]; rfl⟩
              · have hnb_ne4 : nbits ≠ 4#64 := by assumption
                c0_hstraight; exact hJv3 0#32 mr ⟨rfl, fun h => absurd h hnb_ne4⟩
          · c0_hstraight; exact hJem34 emitted_cl mr ⟨sr, hok_r, hm_r⟩
        · c0_hstraight; exact hJem34 emitted_cl mr ⟨sr, hok_r, hm_r⟩
      · c0_hstraight; exact hJem34 emitted_cl mr ⟨sr, hok_r, hm_r⟩
    · c0_hstraight; exact hJem34 emitted_cl mr ⟨sr, hok_r, hm_r⟩
  · intro J34 hJ34
    c0_hsplit
    · c0_hstraight; exact hJ34 mr ⟨rfl, Or.inl (by assumption)⟩
    · c0_hsplit
      · c0_hstraight; exact hJ34 mr ⟨rfl, Or.inr (by assumption)⟩
      · c0_hstraight; exact hJem34 emitted_cl mr ⟨sr, hok_r, hm_r⟩

/-! ## 2. Matrix Emission Specification & `Func.wp` (`full_xor_emit_mat`) -/

@[expose] def fullXorEmitMatSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (h, mat, nrows, ncols, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧
      mat.toNat + nrows.toNat * (2 * ((ncols.toNat + 64) / 64)) ≤ c.scratch_cap ∧
      ncols.toNat ≤ s.core.cur_vars ∧ nrows.toNat < 2 ^ 32 ∧
      (∀ col < ncols.toNat, (s.scratch.work_stk2[col]?.getD 0#32).toNat < s.core.cur_vars) ∧
      XorMatOk (cnfOfClauses F_cur) s.scratch.work_stk2 s.scratch.scratch_buf mat.toNat
        nrows.toNat ncols.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
        FullSparseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.cur_level = 0 → s'.core.fuel = s.core.fuel →
        s'.scratch.scratch_buf = s.scratch.scratch_buf →
        s'.scratch.work_stk1 = s.scratch.work_stk1 →
        s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem full_xor_emit_mat_wp (Γ : Env)
    (hRead : ∀ a m Q X, fullXorReadU64Spec a m Q X →
      Γ "full_xor_read_u64" [i64, i64] [i64] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hHasBin : ∀ a m Q X, fullHasBinSpec a m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hHasTern : ∀ a m Q X, fullHasTernarySpec a m Q X →
      Γ "full_has_ternary" [i64, i32, i32, i32] [.bool] a m Q X)
    (hAddClause : ∀ a m Q X, fullAddClauseSpec a m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullXorEmitMatSpec a m Q X → Func.wp Γ full_xor_emit_mat_body a m Q X := by
  rintro ⟨h, mat, nrows, ncols, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, R, rfl, hsp0, hlvl0, hbd, hnc_cv, hnr32, hc2v_lt, hmat0, hm0, hQ⟩
  let scr0 := s0.scratch.scratch_buf
  let c2v0 := s0.scratch.work_stk2
  have hscr0_len : scr0.length = c.scratch_cap := hsp0.1.2.scratch_buf_len
  have hcap_lt : c.scratch_cap < 268435456 := by
    have := c.hscr; rw [dimacsBound_val] at this; exact this
  have hmaxv_lt : c.max_vars < 536870912 := by
    have := c.hmaxv; rw [dimacsBound_val] at this; exact this
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hsp0.1.1.cur_vars_le
  have hcv_lt : s0.core.cur_vars < 536870912 := by omega
  let words64_nat := (ncols.toNat + 64) / 64
  let row_u32s_nat := 2 * words64_nat
  have hbd' : mat.toNat + nrows.toNat * row_u32s_nat ≤ c.scratch_cap := hbd
  have hw64_bv : ((ncols + 64#64) >>> (6 : Nat)).toNat = words64_nat := by
    dsimp [words64_nat]; rw [bv64_shr6_toNat, BitVec.toNat_add,
      show (64#64).toNat = 64 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hru_bv : (((ncols + 64#64) >>> (6 : Nat)) <<< (1 : Nat)).toNat = row_u32s_nat := by
    dsimp [row_u32s_nat]; rw [bv64_shl1_toNat (by rw [hw64_bv]; dsimp [words64_nat]; omega),
      hw64_bv]
  have hlw_bv : (ncols >>> (6 : Nat)).toNat = ncols.toNat / 64 := bv64_shr6_toNat ncols
  have hrsh_bv : (ncols &&& 63#64).toNat = ncols.toNat % 64 := bv64_and63_toNat ncols
  have hQ_ok : ∀ r s' m', EmitStateOk c F0 F_cur s0 s' → (r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m' :=
    fun r s' m' hok hr hu hm' =>
      hQ r s' m' hok.1 hok.2.1 hok.2.2.1 hok.2.2.2.1 hok.2.2.2.2.1
        hok.2.2.2.2.2.1 hok.2.2.2.2.2.2.2 hr hu hm'
  c0_hstraight
  generalize hw64 : ((ncols + 64) >>> OfNat.ofNat 6 : BitVec 64) = w64
  generalize hwru : (w64 <<< OfNat.ofNat 1 : BitVec 64) = wru
  generalize hwlast : (ncols >>> OfNat.ofNat 6 : BitVec 64) = wlast
  generalize hwrsh : (ncols &&& OfNat.ofNat 63 : BitVec 64) = wrsh
  generalize hwmask : (((1 : BitVec 64) <<< (wrsh.toNat % 64)) - 1 : BitVec 64) = wmask
  have hw64_nat : w64.toNat = words64_nat := by rw [← hw64]; exact hw64_bv
  have hwru_nat : wru.toNat = row_u32s_nat := by rw [← hwru, ← hw64]; exact hru_bv
  have hwlast_nat : wlast.toNat = ncols.toNat / 64 := by rw [← hwlast]; exact hlw_bv
  have hwrsh_nat : wrsh.toNat = ncols.toNat % 64 := by rw [← hwrsh]; exact hrsh_bv
  have hwmask_eq : wmask = (1#64 <<< (ncols.toNat % 64)) - 1#64 := by
    rw [← hwmask, hwrsh_nat, Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))]; rfl
  refine wp_loop_inv
    (fun (_em, r, ()) mr => ∃ sr,
      r.toNat ≤ nrows.toNat ∧ EmitStateOk c F0 F_cur s0 sr ∧ (FullMem c sr ⋆ R) mr)
    (fun (_, r, ()) _ => nrows.toNat - r.toNat)
    (fun J hJ => by
      c0_hstraight
      exact hJ (0#64, 0#64, ()) m0 ⟨s0, Nat.zero_le _,
        ⟨hsp0, rfl, hlvl0, rfl, rfl, rfl, rfl, rfl⟩, hm0⟩)
    (fun J (emitted_cl, r, ()) mr ⟨sr, hr_le, hok_r, hm_r⟩ ih => ?_)
  c0_hsplit
  · have hr_lt : r.toNat < nrows.toNat := by bv_omega
    have hr_succ : (r + 1#64).toNat = r.toNat + 1 := by bv_omega
    have hrow_r : (r.toNat + 1) * row_u32s_nat ≤ nrows.toNat * row_u32s_nat :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hr_lt)
    simp only [Nat.succ_mul] at hrow_r
    let rbase_nat := mat.toNat + r.toNat * row_u32s_nat
    have hrbase_end : rbase_nat + row_u32s_nat ≤ c.scratch_cap := by dsimp [rbase_nat]; omega
    have hrbase_bv : (mat + r * wru).toNat = rbase_nat := by
      have hm1 : (r * wru).toNat = r.toNat * row_u32s_nat := by
        rw [BitVec.toNat_mul, hwru_nat, Nat.mod_eq_of_lt (by omega)]
      rw [BitVec.toNat_add, hm1]; exact Nat.mod_eq_of_lt (by omega)
    have hsound_r : XorPackedRowSound (cnfOfClauses F_cur) c2v0 scr0 rbase_nat ncols.toNat :=
      hmat0 r.toNat hr_lt
    have hlw2 : (wlast <<< (1 : Nat)).toNat = 2 * (ncols.toNat / 64) := by
      rw [bv64_shl1_toNat (by omega), hwlast_nat]
    have hrhs_idx : (mat + r * wru + (wlast <<< (1 : Nat))).toNat =
        rbase_nat + 2 * (ncols.toNat / 64) := by
      rw [BitVec.toNat_add, hrbase_bv, hlw2, Nat.mod_eq_of_lt (by omega)]
    have hrhs_bd : (mat + r * wru + (wlast <<< (1 : Nat))).toNat + 1 < scr0.length := by
      rw [hrhs_idx, hscr0_len]; dsimp [row_u32s_nat, words64_nat] at hrbase_end; omega
    c0_hstraight
    generalize hrbase_eq : (mat + r * wru : BitVec 64) = rbase
    have hrbase_nat_eq : rbase.toNat = rbase_nat := by rw [← hrbase_eq]; exact hrbase_bv
    have hm_scr_r : (array (t := i32) c.pScratchBuf scr0 ⋆ (FullScrBufRest c sr ⋆ R)) mr := by
      dsimp only [scr0]; rw [← hok_r.2.2.2.2.1]; exact focus_full_scr_buf hm_r
    refine LeanQbe.T.wp_call_of_spec _ _ (hRead _ _ _ _ ?_)
    refine ⟨scr0, FullScrBufRest c sr ⋆ R, by rw [← hrbase_eq]; exact hrhs_bd,
      by rw [hscr0_len]; omega, hm_scr_r, ?_⟩
    c0_hstraight
    dsimp only
    have hread_rhs : rowU64 scr0 (Arg.var (rbase + wlast <<< OfNat.ofNat 1)).val.toNat 0 =
        rowU64 scr0 rbase_nat (ncols.toNat / 64) := by
      have hidx : (rbase + (wlast <<< OfNat.ofNat 1)).toNat =
          rbase_nat + 2 * (ncols.toNat / 64) := by rw [← hrbase_eq]; exact hrhs_idx
      unfold rowU64; simp [hidx]
    generalize hrhs_bit_eq :
      ((rowU64 scr0 (Arg.var (rbase + wlast <<< OfNat.ofNat 1)).val.toNat 0 >>>
        (wrsh.toNat % 64)) &&& 1 : BitVec 64) = rhs_bit
    have hrhs_bit_01 : rhs_bit = 0#64 ∨ rhs_bit = 1#64 := by
      rw [← hrhs_bit_eq]; exact bv64_shr_and1.1
    have hrhs_bit_val : (rhs_bit != 0#64) = rowBit scr0 rbase_nat ncols.toNat := by
      rw [← hrhs_bit_eq, hread_rhs]
      exact bv64_shr_and1.2.trans (by
        unfold rowBit; rw [hwrsh_nat, Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))])
    -- Weight-count loop (`while (w < words64)`) with `break`
    refine wp_join_state (fun x : Tup Val [i64, i64] => x)
      (fun (wt, _w, ()) mwt =>
        mwt = mr ∧ (wt = 0#64 → ∀ c < ncols.toNat, rowBit scr0 rbase_nat c = false)) ?_ ?_
    · intro Jwt (wt, _w, ()) mwt ⟨hmwt, hwt_zero⟩
      cases hmwt
      refine wp_join_state (fun x : Tup Val [i64, i64] => x)
        (fun (em', _w', ()) m' => ∃ s', EmitStateOk c F0 F_cur s0 s' ∧ (FullMem c s' ⋆ R) m') ?_ ?_
      · intro Jrow (em', _w', ()) m' ⟨s', hok', hm'⟩
        c0_hstraight
        exact ih (em', r + 1#64, ()) m' (by dsimp only; rw [hr_succ]; omega)
          ⟨s', by rw [hr_succ]; omega, hok', hm'⟩
      · intro Jrow hJrow
        c0_hsplit
        · have hwt0 : wt = 0#64 := by assumption
          c0_hsplit
          · have hrhs_t : rowBit scr0 rbase_nat ncols.toNat = true := by
              rw [← hrhs_bit_val]; simp [show rhs_bit ≠ 0#64 by assumption]
            have hunsat_cur : (cnfOfClauses F_cur).Unsat :=
              unsat_of_zero_packed_row (hwt_zero hwt0) hrhs_t hsound_r
            c0_hstraight
            exact hQ_ok 20#64 { sr with core := { sr.core with inconsistent := 1#64 } } _
              (emitStateOk_upd_inc hok_r 1#64 fun _ => hunsat_cur) (Or.inr rfl)
              (fun _ => unsat_of_sparseW_inconsistent hok_r.1 hunsat_cur) hm
          · c0_hstraight; exact hJrow (emitted_cl, _w, ()) mr ⟨sr, hok_r, hm_r⟩
        · refine wp_join_state (fun x : Tup Val [i64, i64] => x)
            (fun (em', _w', ()) m' => ∃ s', EmitStateOk c F0 F_cur s0 s' ∧ (FullMem c s' ⋆ R) m')
            (fun _ st m' h => by c0_hstraight; exact hJrow st m' h)
            (fun Jle4 hJle4 => ?_)
          c0_hsplit
          · refine wp_join_state (fun x : Tup Val [i64, i64, i64, i64, i64, i64] => x)
              (fun (_w', c0, c1, c2, c3, nbits, ()) mx =>
                mx = mr ∧ (nbits.toNat ≤ 4 →
                  (∀ col ∈ colsOf nbits c0 c1 c2 c3, col < ncols.toNat) ∧
                  (colsOf nbits c0 c1 c2 c3).Pairwise (· < ·) ∧
                  (∀ col < ncols.toNat,
                    rowBit scr0 rbase_nat col = true ↔ col ∈ colsOf nbits c0 c1 c2 c3))) ?_ ?_
            · intro Jex (_w', c0, c1, c2, c3, nbits, ()) mx ⟨hmx, hcols_ok⟩
              cases hmx
              refine wp_join_state1 (fun x : Val i64 => x)
                (fun em' m' => ∃ s', EmitStateOk c F0 F_cur s0 s' ∧ (FullMem c s' ⋆ R) m')
                (fun _ em' m' h => by c0_hstraight; exact hJle4 (em', _w', ()) m' h)
                (fun Jem1 hJem1 => ?_)
              refine wp_join0 (fun m' => m' = mr) ?_ ?_
              · intro Jelse1 m' hm'; cases hm'
                refine wp_join_state1 (fun x : Val i64 => x)
                  (fun em' m' => ∃ s', EmitStateOk c F0 F_cur s0 s' ∧ (FullMem c s' ⋆ R) m')
                  (fun _ em' m' h => by c0_hstraight; exact hJem1 em' m' h)
                  (fun Jem2 hJem2 => ?_)
                refine wp_join0 (fun m' => m' = mr) ?_ ?_
                · intro Jelse2 m' hm'; cases hm'
                  refine wp_join_state1 (fun x : Val i64 => x)
                    (fun em' m' => ∃ s', EmitStateOk c F0 F_cur s0 s' ∧ (FullMem c s' ⋆ R) m')
                    (fun _ em' m' h => by c0_hstraight; exact hJem2 em' m' h)
                    (fun Jem34 hJem34 => ?_)
                  exact emit_mat_n34_wp hHasTern hAddClause hcv_le hcv_lt hnc_cv hc2v_lt hsound_r
                    hrhs_bit_01 hrhs_bit_val hcols_ok hok_r hm_r hQ_ok hJem34
                · intro Jelse2 hJelse2
                  exact emit_mat_n2_wp hHasBin hAddBin hcv_le hcv_lt hnc_cv hc2v_lt hsound_r
                    hrhs_bit_01 hrhs_bit_val hcols_ok hok_r hm_r hQ_ok hJem2 hJelse2
              · intro Jelse1 hJelse1
                exact emit_mat_n1_wp hAddUnit hcv_le hcv_lt hnc_cv hc2v_lt hsound_r
                  hrhs_bit_01 hrhs_bit_val hcols_ok hok_r hm_r hQ_ok hJem1 hJelse1
            · intro Jex hJex
              exact emit_mat_extract_wp hRead (by rw [hscr0_len]; omega) (by omega) hrbase_nat_eq
                (by rw [hscr0_len]; exact hrbase_end) hw64_nat hwlast_nat hwmask_eq hm_scr_r hJex
          · c0_hstraight; exact hJle4 (emitted_cl, _w, ()) mr ⟨sr, hok_r, hm_r⟩
    · intro Jwt hJwt
      exact emit_mat_wt_loop_wp hRead (by rw [hscr0_len]; omega) (by omega) hrbase_nat_eq
        (by rw [hscr0_len]; exact hrbase_end) hw64_nat hwlast_nat hwmask_eq hm_scr_r hJwt
  · c0_hstraight
    exact hQ_ok 1#64 sr mr hok_r (Or.inl rfl) (fun h => by cases h) hm_r

end LeanQbe.T.Examples.Kissat.FullM8XorGauss
