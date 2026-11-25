/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8XorGaussProof0
public import LeanQbe.T.Examples.Kissat.FullM8XorGaussProof1a
import LeanQbe.T.Examples.Kissat.FullAssignAddLemmas1
import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
public meta import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat M8 XOR / $\mathbb{F}_2$ Gauss-Jordan — Build, RREF & Pool Emit (`FullM8XorGaussProof2a`)

`Func.wp` proofs for `full_xor_build_mat`, `full_xor_rref`, and `full_xor_emit_pool_small`.
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

/-! ## 1. Pure Helpers & State-Transition Wrappers (`private`) -/

theorem bv64_shl1_toNat {x : BitVec 64} (hx : x.toNat < 2 ^ 63) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega : x.toNat * 2 < 2 ^ 64)]
  exact Nat.mul_comm _ _

theorem bv64_shr6_toNat (x : BitVec 64) : (x >>> (6 : Nat)).toNat = x.toNat / 64 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv64_shl6_toNat {x : BitVec 64} (hx : x.toNat < 2 ^ 58) :
    (x <<< (6 : Nat)).toNat = 64 * x.toNat := by
  rw [BitVec.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq, show (2 : Nat) ^ 6 = 64 from rfl,
    Nat.mod_eq_of_lt (by omega : x.toNat * 64 < 2 ^ 64)]
  exact Nat.mul_comm _ _

theorem bv64_and63_toNat (x : BitVec 64) : (x &&& 63#64).toNat = x.toNat % 64 := by
  rw [BitVec.toNat_and, show (63#64).toNat = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

private theorem nat_two_mul_or_one (n : Nat) : (2 * n) ||| 1 = 2 * n + 1 := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or]
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.pow_succ', ← Nat.div_div_eq_div_mul]
    have h1 : (2 * n) / 2 = n := by omega
    have h2 : (2 * n + 1) / 2 = n := by omega
    have h3 : 1 / 2 = 0 := rfl
    rw [h1, h2, h3, Nat.zero_div]; simp

theorem bv32_lit_from_var_rhs {v : BitVec 32} {rb : BitVec 32}
    (hv : v.toNat < 2 ^ 30) (hrb : rb.toNat ≤ 1) :
    ((v <<< (1 : Nat)) ||| rb).toNat = 2 * v.toNat + rb.toNat := by
  have hsh : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
    rw [BitVec.toNat_shiftLeft]
    simp only [Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega : v.toNat * 2 < 2 ^ 32)]
    exact Nat.mul_comm _ _
  rcases (by omega : rb.toNat = 0 ∨ rb.toNat = 1) with h0 | h1
  · have : rb = 0#32 := BitVec.eq_of_toNat_eq h0
    subst this; simp [hsh]
  · have : rb = 1#32 := BitVec.eq_of_toNat_eq h1
    subst this
    rw [BitVec.toNat_or, hsh, show (1#32).toNat = 1 from rfl, nat_two_mul_or_one]

theorem bv32_lit_from_var_rhs_mkLit {v : BitVec 32} {rb : BitVec 32}
    (hv : v.toNat < 2 ^ 30) (hrb : rb.toNat ≤ 1) :
    ((v <<< (1 : Nat)) ||| (rb ^^^ 1#32)).toNat = mkLit v.toNat (rb != 0#32) ∧
    ((v <<< (1 : Nat)) ||| rb).toNat = mkLit v.toNat (!(rb != 0#32)) := by
  rcases (by omega : rb.toNat = 0 ∨ rb.toNat = 1) with h0 | h1
  · have hrb0 : rb = 0#32 := BitVec.eq_of_toNat_eq h0
    subst hrb0
    have h1 : ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1 :=
      bv32_lit_from_var_rhs hv (by decide)
    have h2 : ((v <<< (1 : Nat)) ||| 0#32).toNat = 2 * v.toNat :=
      bv32_lit_from_var_rhs hv (by decide)
    refine ⟨?_, ?_⟩
    · change ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1; exact h1
    · change ((v <<< (1 : Nat)) ||| 0#32).toNat = 2 * v.toNat; exact h2
  · have hrb1 : rb = 1#32 := BitVec.eq_of_toNat_eq h1
    subst hrb1
    have h1 : ((v <<< (1 : Nat)) ||| 0#32).toNat = 2 * v.toNat :=
      bv32_lit_from_var_rhs hv (by decide)
    have h2 : ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1 :=
      bv32_lit_from_var_rhs hv (by decide)
    refine ⟨?_, ?_⟩
    · change ((v <<< (1 : Nat)) ||| 0#32).toNat = 2 * v.toNat; exact h1
    · change ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1; exact h2

private theorem xorPackedRowSound_congr {F : CNF Nat} {c2v scr1 scr2 : List (BitVec 32)}
    {b1 b2 ncols : Nat}
    (heq : ∀ i < 2 * ((ncols + 64) / 64), scr2[b2 + i]? = scr1[b1 + i]?)
    (h : XorPackedRowSound F c2v scr1 b1 ncols) :
    XorPackedRowSound F c2v scr2 b2 ncols := by
  have hbit : ∀ c ≤ ncols, rowBit scr2 b2 c = rowBit scr1 b1 c := by
    intro c hc
    have hw : c / 64 < (ncols + 64) / 64 := by omega
    unfold rowBit rowU64
    rw [heq (2 * (c / 64)) (by omega),
      show b2 + 2 * (c / 64) + 1 = b2 + (2 * (c / 64) + 1) by omega,
      show b1 + 2 * (c / 64) + 1 = b1 + (2 * (c / 64) + 1) by omega,
      heq (2 * (c / 64) + 1) (by omega)]
  intro α hα
  have h0 := h α hα
  unfold xorEvalPacked at h0 ⊢
  rw [hbit ncols (Nat.le_refl _)]
  have hfold : ∀ k ≤ ncols,
      (List.range k).foldl
        (fun acc c => if rowBit scr2 b2 c then acc != α (c2v[c]?.getD 0#32).toNat else acc)
        false =
      (List.range k).foldl
        (fun acc c => if rowBit scr1 b1 c then acc != α (c2v[c]?.getD 0#32).toNat else acc)
        false := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih (Nat.le_of_lt hk), hbit k (Nat.le_of_lt hk)]
  rw [hfold ncols (Nat.le_refl _)]
  exact h0

private theorem filter_lt_succ_perm_mem' {cols : List Nat} {k : Nat}
    (hn : cols.Nodup) (hk : k ∈ cols) :
    (cols.filter (· < k + 1)).Perm (k :: cols.filter (· < k)) := by
  induction cols with
  | nil => simp at hk
  | cons x xs ih =>
    have hnx := List.nodup_cons.mp hn
    simp only [List.filter_cons, List.mem_cons] at hk ⊢
    rcases hk with rfl | hmem
    · have hk_not : ¬k ∈ xs := hnx.1
      have hfilt_eq :
          xs.filter (fun y => decide (y < k + 1)) = xs.filter (fun y => decide (y < k)) := by
        refine List.filter_congr fun y hy => ?_
        have hyk : y ≠ k := fun h => hk_not (h ▸ hy)
        by_cases hy1 : y < k + 1 <;> by_cases hy2 : y < k <;> simp_all <;> omega
      simp [hfilt_eq]
    · have hxk : x ≠ k := fun h => hnx.1 (h ▸ hmem)
      have ih' := ih hnx.2 hmem
      by_cases hlt : x < k
      · have hlt1 : x < k + 1 := Nat.lt_succ_of_lt hlt
        simp only [hlt1, hlt, decide_true, ↓reduceIte]
        exact (ih'.cons x).trans (List.Perm.swap k x _)
      · have hn1 : ¬ (x < k + 1) := by omega
        simp only [hn1, hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact ih'

private theorem filter_lt_succ_eq_of_nmem' {cols : List Nat} {k : Nat} (hk : k ∉ cols) :
    cols.filter (· < k + 1) = cols.filter (· < k) := by
  refine List.filter_congr fun x hx => ?_
  have hxk : x ≠ k := fun h => hk (h ▸ hx)
  by_cases h1 : x < k + 1 <;> by_cases h2 : x < k <;> simp_all <;> omega

private theorem xorPackedRowSound_of_xorVarsSound {F : CNF Nat} {c2v scr : List (BitVec 32)}
    {rbase ncols : Nat} {cols : List Nat}
    (hcol_lt : ∀ c ∈ cols, c < ncols) (hnodup : cols.Nodup)
    (hbits : ∀ c < ncols, rowBit scr rbase c = true ↔ c ∈ cols)
    (hsound : XorVarsSound F (cols.map fun c => (c2v[c]?.getD 0#32).toNat)
      (rowBit scr rbase ncols)) :
    XorPackedRowSound F c2v scr rbase ncols := by
  intro α hα
  suffices hstep : ∀ (k : Nat) (hk : k ≤ ncols),
      (List.range k).foldl
        (fun acc c => if rowBit scr rbase c then acc != α (c2v[c]?.getD 0#32).toNat else acc)
        false =
      xorEvalVars α ((cols.filter (· < k)).map fun c => (c2v[c]?.getD 0#32).toNat) by
    unfold xorEvalPacked
    have hfilt : cols.filter (· < ncols) = cols := List.filter_eq_self.mpr fun c hc => by
      simpa using hcol_lt c hc
    rw [hstep ncols (Nat.le_refl _), hfilt, hsound α hα]
    cases rowBit scr rbase ncols <;> rfl
  intro k hk
  induction k with
  | zero =>
    simp only [List.range_zero, List.foldl_nil]
    have hnil : cols.filter (fun x => decide (x < 0)) = [] :=
      List.filter_eq_nil_iff.mpr (by simp)
    rw [hnil]; rfl
  | succ k ih =>
    have hk_lt : k < ncols := hk
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ih (Nat.le_of_lt hk_lt)]
    by_cases hrb : rowBit scr rbase k = true
    · have hk_mem : k ∈ cols := (hbits k hk_lt).mp hrb
      have hperm := filter_lt_succ_perm_mem' hnodup hk_mem
      have hxperm := xorEvalVars_perm (α := α)
        (hperm.map fun c => (c2v[c]?.getD 0#32).toNat)
      rw [hrb, ite_eq_left rfl, hxperm, List.map_cons, xorEvalVars_cons]
      cases α (c2v[k]?.getD 0#32).toNat <;>
        cases xorEvalVars α ((cols.filter (· < k)).map fun c => (c2v[c]?.getD 0#32).toNat) <;>
        rfl
    · have hk_nmem : k ∉ cols := fun h => hrb ((hbits k hk_lt).mpr h)
      have hfilt_eq := filter_lt_succ_eq_of_nmem' hk_nmem
      have hrb_f : rowBit scr rbase k = false := by cases h : rowBit scr rbase k <;> simp_all
      rw [hrb_f, ite_eq_right Bool.false_ne_true, hfilt_eq]

private theorem poolStarts_step_mem {scr : List (BitVec 32)} {eq_end : Nat} :
    ∀ {fuel q p : Nat}, eq_end - q ≤ fuel → p ∈ poolStarts scr eq_end q fuel →
      let st := (((scr[p]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32).toNat
      p + 1 + st < eq_end → p + 1 + st ∈ poolStarts scr eq_end q fuel
  | 0, q, p, _, hp, _ => nomatch hp
  | fuel + 1, q, p, hfl, hp, hlt => by
    have hq_lt : q < eq_end := by
      unfold poolStarts at hp
      split at hp
      · assumption
      · exact nomatch hp
    rw [poolStarts_step_iff hq_lt] at hp ⊢
    rcases hp with rfl | ⟨hle, hrest⟩
    · right
      refine ⟨Nat.le_refl _, ?_⟩
      cases fuel with
      | zero => omega
      | succ f' =>
        rw [poolStarts_step_iff hlt]
        exact Or.inl rfl
    · right
      have hq_ge : q + 1 ≤ q + 1 + (((scr[q]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32).toNat := by
        omega
      refine ⟨by omega, poolStarts_step_mem (by omega) hrest hlt⟩

private theorem nodup_of_map' {α β : Type} (f : α → β) :
    ∀ {xs : List α}, (xs.map f).Nodup → xs.Nodup
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.nodup_cons]
    exact ⟨fun hx => h.1 (List.mem_map_of_mem hx), nodup_of_map' f h.2⟩

private theorem focus_full_scr_buf_upd {c : FullCfg} {s : FullState} {scr : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c { s with scratch := { s.scratch with scratch_buf := scr } } ⋆ R) m) :
    (array (t := i32) c.pScratchBuf scr ⋆ (FullScrBufRest c s ⋆ R)) m := by
  exact focus_full_scr_buf hm

theorem fullSparseInvW_of_addUnit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s)
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
    (hlen' : let_s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur let_s'.core) :
    FullSparseInvW c F0 F_cur let_s' := by
  subst hs'_eq
  refine ⟨hlen', hw', fullLitMarksClear_of_eq h.2.2.1 rfl rfl,
    fullArenaVarsNodup_of_eq h.2.2.2.1 rfl rfl, ?_, h.2.2.2.2.2⟩
  exact h.2.2.2.2.1.of_pres ⟨rfl, rfl⟩ fun _ hr => hr

theorem fullSparseInvW_of_addBin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s)
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
    FullSparseInvW c F0 F_cur let_s' := by
  subst hs'_eq
  refine ⟨hlen', hw', fullLitMarksClear_of_eq h.2.2.1 rfl rfl,
    fullArenaVarsNodup_of_eq h.2.2.2.1 rfl rfl, ?_, h.2.2.2.2.2⟩
  exact h.2.2.2.2.1.of_pres ⟨rfl, rfl⟩ fun _ hr => hr

theorem fullSparseInvW_of_addClause3 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s)
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
    FullSparseInvW c F0 F_cur let_s' := by
  subst hs'_eq
  refine ⟨hlen', hw', fullLitMarksClear_of_eq h.2.2.1 rfl rfl,
    hnd h.2.2.2.1, h.2.2.2.2.1.of_pres ⟨rfl, rfl⟩ hrefs, h.2.2.2.2.2⟩

/-! ## 2. Component Closure & Matrix Build (`full_xor_build_mat`) -/

@[expose] def XorPoolCompClosed (par scr : List (BitVec 32)) (eq_end : Nat) : Prop :=
  ∀ p ∈ poolStarts scr eq_end 0 eq_end,
    let hdr := scr[p]?.getD 0#32
    let clen := (hdr &&& 0xFFFF#32).toNat
    0 < clen → ∀ k < clen,
      par[(scr[p + 1 + k]?.getD 0#32).toNat]?.getD 0#32 =
      par[(scr[p + 1]?.getD 0#32).toNat]?.getD 0#32

@[expose] def fullXorBuildMatSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (h, root, eq_end, ncols, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ eq_end.toNat ≤ c.scratch_cap ∧
      0 < ncols.toNat ∧ ncols.toNat ≤ s.core.cur_vars ∧
      XorEqPoolOk (cnfOfClauses F_cur) s.core.cur_vars s.scratch.scratch_buf eq_end.toNat 0 ∧
      XorPoolCompClosed s.scratch.work_stk1 s.scratch.scratch_buf eq_end.toNat ∧
      (∀ v < s.core.cur_vars,
        (s.scratch.work_stk1[v]?.getD 0#32).toNat = root.toNat →
        (s.scratch.tarjan_reach[v]?.getD 0#32).toNat < ncols.toNat ∧
        (s.scratch.work_stk2[(s.scratch.tarjan_reach[v]?.getD 0#32).toNat]?.getD 0#32).toNat = v) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (nrows : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
        scr'.length = c.scratch_cap →
        (∀ i < eq_end.toNat, scr'[i]? = s.scratch.scratch_buf[i]?) →
        eq_end.toNat + nrows.toNat * (2 * ((ncols.toNat + 64) / 64)) ≤ c.scratch_cap →
        XorMatOk (cnfOfClauses F_cur) s.scratch.work_stk2 scr' eq_end.toNat
          nrows.toNat ncols.toNat →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q (nrows, ()) m'

theorem full_xor_build_mat_wp (Γ : Env)
    (hSetBit : ∀ a m Q X, fullXorSetBitSpec a m Q X →
      Γ "full_xor_set_bit" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullXorBuildMatSpec a m Q X → Func.wp Γ full_xor_build_mat_body a m Q X := by
  rintro ⟨h, root, eq_end, ncols, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hsp, heq_cap, hnc_pos, hnc_cv, hpool0, hclosed, hmap, hm0, hQ⟩
  let scr0 := s.scratch.scratch_buf
  have hscr0_len : scr0.length = c.scratch_cap := hsp.1.2.scratch_buf_len
  have hcap_lt : c.scratch_cap < 268435456 := by
    have := c.hscr; rw [dimacsBound_val] at this; exact this
  have hmaxv_lt : c.max_vars < 536870912 := by
    have := c.hmaxv; rw [dimacsBound_val] at this; exact this
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hsp.1.1.cur_vars_le
  have hcv_lt : s.core.cur_vars < 536870912 := by omega
  have hws1_len : s.scratch.work_stk1.length = 2 * c.max_vars := hsp.1.2.work_stk1_len
  have htr_len : s.scratch.tarjan_reach.length = 2 * c.max_vars := hsp.1.2.tarjan_reach_len
  have hw64_toNat : ((ncols + 64#64) >>> (6 : Nat)).toNat = (ncols.toNat + 64) / 64 := by
    rw [bv64_shr6_toNat, BitVec.toNat_add, show (64#64).toNat = 64 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hru_toNat : (((ncols + 64#64) >>> (6 : Nat)) <<< (1 : Nat)).toNat =
      2 * ((ncols.toNat + 64) / 64) := by
    rw [bv64_shl1_toNat (by rw [hw64_toNat]; omega), hw64_toNat]
  let row_u32s_nat := 2 * ((ncols.toNat + 64) / 64)
  have hru_pos : 0 < row_u32s_nat := by dsimp [row_u32s_nat]; omega
  c0_hstraight
  obtain ⟨w_ru, hw_ru⟩ : ∃ x : BitVec 64,
      (ncols + 64) >>> OfNat.ofNat 6 <<< OfNat.ofNat 1 = x := ⟨_, rfl⟩
  have hw_ru_nat : w_ru.toNat = row_u32s_nat := by rw [← hw_ru]; exact hru_toNat
  rw [hw_ru]
  c0_hsplit
  · c0_hstraight
    exact hQ 0#64 scr0 m0 hscr0_len (fun _ _ => rfl) (by simpa using heq_cap)
      (fun _ hr => absurd hr (Nat.not_lt_zero _)) hm0
  · c0_hsplit
    · exfalso; rw [← hw_ru_nat] at hru_pos; bv_omega
    · have heq_lt_cap : eq_end.toNat < c.scratch_cap := by bv_omega
      have hcap_bv : (BitVec.ofNat 64 c.scratch_cap).toNat = c.scratch_cap :=
        bv64_ofNat_toNat (by omega)
      have hsub_bv : (BitVec.ofNat 64 c.scratch_cap - eq_end).toNat =
          c.scratch_cap - eq_end.toNat := by
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hcap_bv]; omega)), hcap_bv]
      have hmr_toNat : ((BitVec.ofNat 64 c.scratch_cap - eq_end) / w_ru).toNat =
          (c.scratch_cap - eq_end.toNat) / row_u32s_nat := by
        rw [BitVec.toNat_udiv, hsub_bv, hw_ru_nat]
      obtain ⟨max_rows, hmr_eq⟩ : ∃ x : BitVec 64,
          (BitVec.ofNat 64 c.scratch_cap - eq_end) / w_ru = x := ⟨_, rfl⟩
      have hmr_nat : max_rows.toNat = (c.scratch_cap - eq_end.toNat) / row_u32s_nat := by
        rw [← hmr_eq]; exact hmr_toNat
      have hmr_fit : eq_end.toNat + max_rows.toNat * row_u32s_nat ≤ c.scratch_cap := by
        rw [hmr_nat]
        have := Nat.div_mul_le_self (c.scratch_cap - eq_end.toNat) row_u32s_nat
        omega
      c0_hstraight
      rw [hmr_eq]
      c0_hsplit
      · c0_hstraight
        exact hQ 0#64 scr0 m0 hscr0_len (fun _ _ => rfl) (by simpa using heq_cap)
          (fun _ hr => absurd hr (Nat.not_lt_zero _)) hm0
      · c0_hstraight
        refine wp_join_state (fun x : Tup Val [i64, i64] => x)
          (fun (nrows, _p, ()) mj => ∃ scr_cur,
            scr_cur.length = c.scratch_cap ∧
            (∀ i < eq_end.toNat, scr_cur[i]? = scr0[i]?) ∧
            eq_end.toNat + nrows.toNat * row_u32s_nat ≤ c.scratch_cap ∧
            XorMatOk (cnfOfClauses F_cur) s.scratch.work_stk2 scr_cur eq_end.toNat
              nrows.toNat ncols.toNat ∧
            (FullMem c { s with scratch := { s.scratch with scratch_buf := scr_cur } } ⋆ R) mj)
          ?_ ?_
        · intro J0 (nrows, _p, ()) mj ⟨scr_cur, hlen, hpre, hfit, hmat, hmj⟩
          c0_hstraight
          exact hQ nrows scr_cur mj hlen hpre hfit hmat hmj
        · intro J0 hJ0
          refine wp_loop_inv
            (fun (nrows, p, ()) m => ∃ scr_cur,
              p.toNat ≤ eq_end.toNat ∧ nrows.toNat ≤ max_rows.toNat ∧
              scr_cur.length = c.scratch_cap ∧
              (∀ i < eq_end.toNat, scr_cur[i]? = scr0[i]?) ∧
              (p.toNat < eq_end.toNat → p.toNat ∈ poolStarts scr0 eq_end.toNat 0 eq_end.toNat) ∧
              XorEqPoolOk (cnfOfClauses F_cur) s.core.cur_vars scr0 eq_end.toNat p.toNat ∧
              XorMatOk (cnfOfClauses F_cur) s.scratch.work_stk2 scr_cur eq_end.toNat
                nrows.toNat ncols.toNat ∧
              (FullMem c { s with scratch := { s.scratch with scratch_buf := scr_cur } } ⋆ R) m)
            (fun (_, p, ()) _ => eq_end.toNat - p.toNat)
            (fun J hJ => by
              c0_hstraight
              refine hJ (0#64, 0#64, ()) m0 ⟨scr0, Nat.zero_le _, Nat.zero_le _, hscr0_len,
                fun _ _ => rfl, ?_, hpool0, fun _ hr => absurd hr (Nat.not_lt_zero _), hm0⟩
              intro h0
              cases he : eq_end.toNat with
              | zero => omega
              | succ e' =>
                rw [poolStarts_step_iff (by omega)]
                exact Or.inl rfl)
            (fun J (nrows, p, ()) m ⟨scr_cur, hp_le, hnr_le, hlen_cur, hpre_cur, hp_mem, hpool_p,
                hmat_cur, hm_cur⟩ ih => ?_)
          c0_hsplit
          · have hp_lt : p.toNat < eq_end.toNat := by bv_omega
            c0_hsplit
            · have hnr_lt : nrows.toNat < max_rows.toNat := by bv_omega
              have hp_in : p.toNat ∈ poolStarts scr0 eq_end.toNat 0 eq_end.toNat := hp_mem hp_lt
              generalize hp_nat : p.toNat = p_nat at hpool_p
              cases hpool_p with
              | done => rw [hp_nat] at hp_lt; exact absurd hp_lt (Nat.lt_irrefl _)
              | @step _ hdr stride clen _ hhdr hst hcl hbd hbody hrest =>
                rw [← hp_nat] at hhdr hbd hbody hrest
                have hp_len : p.toNat < scr_cur.length := by omega
                have hg_p : scr_cur[p.toNat]'hp_len = hdr := by
                  have h1 := hpre_cur p.toNat hp_lt
                  rw [List.getElem?_eq_getElem hp_len, hhdr] at h1
                  exact Option.some.inj h1
                have hst_lt : stride < 2 ^ 15 := by
                  rw [hst, BitVec.toNat_and]
                  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                c0_hstraight
                rw [hg_p]
                obtain ⟨wst, hwst⟩ : ∃ w : BitVec 64,
                    ((hdr >>> 16 &&& 32767).setWidth 64) = w := ⟨_, rfl⟩
                have hst_w : wst.toNat = stride := by
                  rw [← hwst, bv_zext32_toNat,
                    show (hdr >>> 16 &&& (32767 : BitVec 32)) =
                      hdr >>> 16#32 &&& 0x7FFF#32 from rfl, ← hst]
                obtain ⟨wcl, hwcl⟩ : ∃ w : BitVec 64, (hdr &&& 65535).setWidth 64 = w := ⟨_, rfl⟩
                have hcl_w : wcl.toNat = clen := by
                  rw [← hwcl, bv_zext32_toNat,
                    show (hdr &&& (65535 : BitVec 32)) = hdr &&& 0xFFFF#32 from rfl, ← hcl]
                rw [hwst, hwcl]
                c0_hsplit
                · exfalso
                  have : p.toNat + 1 + stride ≤ eq_end.toNat := hbd
                  rw [← hst_w] at this; bv_omega
                · have hp_next : (p + 1#64 + wst).toNat = p.toNat + 1 + stride := by
                    rw [← hst_w]; bv_omega
                  have hp_next_mem : (p + 1#64 + wst).toNat < eq_end.toNat →
                      (p + 1#64 + wst).toNat ∈ poolStarts scr0 eq_end.toNat 0 eq_end.toNat := by
                    rw [hp_next]; intro hlt
                    have hstep := poolStarts_step_mem (scr := scr0) (eq_end := eq_end.toNat)
                      (fuel := eq_end.toNat) (q := 0) (p := p.toNat) (by omega) hp_in
                    have hst_eq : (((scr0[p.toNat]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32).toNat =
                        stride := by rw [hhdr, Option.getD_some, hst]
                    dsimp only at hstep; rw [hst_eq] at hstep
                    exact hstep hlt
                  refine wp_join_state1 (fun st : Val i64 => st)
                    (fun nrows' m' => ∃ scr',
                      nrows'.toNat ≤ max_rows.toNat ∧ scr'.length = c.scratch_cap ∧
                      (∀ i < eq_end.toNat, scr'[i]? = scr0[i]?) ∧
                      XorMatOk (cnfOfClauses F_cur) s.scratch.work_stk2 scr' eq_end.toNat
                        nrows'.toNat ncols.toNat ∧
                      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R)
                        m')
                    ?_ ?_
                  · intro J1 nrows' m' ⟨scr', hnr', hlen', hpre', hmat', hm'⟩
                    c0_hstraight
                    exact ih (nrows', p + 1#64 + wst, ()) m' (by dsimp only; omega)
                      ⟨scr', by rw [hp_next]; exact hbd, hnr', hlen', hpre', hp_next_mem,
                       by rw [hp_next]; exact hrest, hmat', hm'⟩
                  · intro J1 hJ1
                    c0_hsplit
                    · c0_hsplit
                      · rcases hbody with h0 | ⟨hpos, hcl_le, hss, hcv_vs, hsnd⟩
                        · exfalso; rw [← hcl_w] at h0; bv_omega
                        · have hp1_bv : (p + 1).toNat = p.toNat + 1 := by bv_omega
                          have hp1_lt : p.toNat + 1 < eq_end.toNat := by omega
                          have hp1_len : (p + 1).toNat < scr_cur.length := by omega
                          c0_hstraight
                          dsimp only
                          obtain ⟨v0, hv0⟩ : ∃ x : BitVec 32,
                              scr_cur[(p + 1).toNat]'hp1_len = x := ⟨_, rfl⟩
                          rw [hv0]
                          have hv0_eq : scr0[p.toNat + 1]? = some v0 := by
                            rw [← hpre_cur (p.toNat + 1) hp1_lt,
                              show scr_cur[p.toNat + 1]? = scr_cur[(p + 1).toNat]? from
                                congrArg (scr_cur[·]?) hp1_bv.symm,
                              List.getElem?_eq_getElem hp1_len, hv0]
                          refine wp_join_state1 (fun st : Val i64 => st)
                            (fun nrows' m' => ∃ scr',
                              nrows'.toNat ≤ max_rows.toNat ∧ scr'.length = c.scratch_cap ∧
                              (∀ i < eq_end.toNat, scr'[i]? = scr0[i]?) ∧
                              XorMatOk (cnfOfClauses F_cur) s.scratch.work_stk2 scr' eq_end.toNat
                                nrows'.toNat ncols.toNat ∧
                              (FullMem c { s with scratch :=
                                { s.scratch with scratch_buf := scr' } } ⋆ R) m')
                            (fun _ nr' m' h => by c0_hstraight; exact hJ1 nr' m' h)
                            (fun J2 hJ2 => ?_)
                          c0_hsplit
                          · have hv0_cv : v0.toNat < s.core.cur_vars := by
                              have hcv_bv : (BitVec.ofNat 64 s.core.cur_vars).toNat =
                                  s.core.cur_vars := bv64_ofNat_toNat (by omega)
                              have hz := bv_zext32_toNat v0
                              bv_omega
                            have hv0_ws1 : (v0.setWidth 64).toNat < s.scratch.work_stk1.length := by
                              rw [bv_zext32_toNat, hws1_len]; omega
                            c0_hsplit
                            · have hpar_v0 : (s.scratch.work_stk1[v0.toNat]?.getD 0#32).toNat =
                                  root.toNat := by
                                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                                have hz2 := bv_zext32_toNat
                                  (s.scratch.work_stk1[v0.toNat]'(by omega))
                                rw [← hz2]; exact congrArg BitVec.toNat hc
                              have hclosed_p := hclosed p.toNat hp_in
                              have hcl_hdr : ((scr0[p.toNat]?.getD 0#32) &&& 0xFFFF#32).toNat =
                                  clen := by rw [hhdr, Option.getD_some, hcl]
                              dsimp only at hclosed_p; rw [hcl_hdr] at hclosed_p
                              have hpar_all : ∀ k < clen,
                                  (s.scratch.work_stk1[(scr0[p.toNat + 1 + k]?.getD 0#32).toNat]?
                                    |>.getD 0#32).toNat = root.toNat := by
                                intro k hk
                                have hck := hclosed_p hpos k hk
                                rw [hck, hv0_eq, Option.getD_some]
                                exact hpar_v0
                              let rbase_nat := eq_end.toNat + nrows.toNat * row_u32s_nat
                              have hnr_row : (nrows.toNat + 1) * row_u32s_nat ≤
                                  max_rows.toNat * row_u32s_nat :=
                                Nat.mul_le_mul_right row_u32s_nat (Nat.succ_le_of_lt hnr_lt)
                              have hrbase_end : rbase_nat + row_u32s_nat ≤ c.scratch_cap := by
                                dsimp [rbase_nat]
                                simp only [Nat.succ_mul] at hnr_row
                                omega
                              have hrbase_bv : (eq_end + nrows * w_ru).toNat = rbase_nat := by
                                have hmul : (nrows * w_ru).toNat = nrows.toNat * row_u32s_nat := by
                                  rw [BitVec.toNat_mul, hw_ru_nat, Nat.mod_eq_of_lt (by omega)]
                                rw [BitVec.toNat_add, hmul]
                                exact Nat.mod_eq_of_lt (by omega)
                              obtain ⟨rbase, hrbase_eq⟩ : ∃ x : BitVec 64,
                                  eq_end + nrows * w_ru = x := ⟨_, rfl⟩
                              have hrbase_toNat : rbase.toNat = rbase_nat := by
                                rw [← hrbase_eq]; exact hrbase_bv
                              c0_hstraight
                              rw [hrbase_eq]
                              -- Zero-fill loop: `scr[rbase + zi] = 0` for `zi < row_u32s`
                              refine wp_loop_inv
                                (fun (zi, ()) mz => ∃ scr_z,
                                  zi.toNat ≤ row_u32s_nat ∧ scr_z.length = c.scratch_cap ∧
                                  (∀ i, i < rbase_nat ∨ rbase_nat + row_u32s_nat ≤ i →
                                    scr_z[i]? = scr_cur[i]?) ∧
                                  (∀ i < zi.toNat, scr_z[rbase_nat + i]? = some 0#32) ∧
                                  (FullMem c { s with scratch :=
                                    { s.scratch with scratch_buf := scr_z } } ⋆ R) mz)
                                (fun (zi, ()) _ => row_u32s_nat - zi.toNat)
                                (fun Jz hJz => by
                                  c0_hstraight
                                  exact hJz (0#64, ()) m ⟨scr_cur, Nat.zero_le _, hlen_cur,
                                    fun _ _ => rfl, fun _ hi => absurd hi (Nat.not_lt_zero _),
                                    hm_cur⟩)
                                (fun Jz (zi, ()) mz ⟨scr_z, hzi_le, hlen_z, hfr_z, hzero_z,
                                    hm_z⟩ ihz => ?_)
                              c0_hsplit
                              · have hzi_lt : zi.toNat < row_u32s_nat := by
                                  rw [← hw_ru_nat]; bv_omega
                                have hidx_z : (rbase + zi).toNat = rbase_nat + zi.toNat := by
                                  rw [← hrbase_toNat]; bv_omega
                                have hidx_len : (rbase + zi).toNat < scr_z.length := by omega
                                have hzi_succ : (zi + 1#64).toNat = zi.toNat + 1 := by bv_omega
                                c0_hstraight
                                refine ihz (zi + 1#64, ()) _ (by dsimp only; rw [hzi_succ]; omega)
                                  ⟨scr_z.set (rbase + zi).toNat 0#32, by rw [hzi_succ]; omega,
                                   by simp [hlen_z],
                                   fun i hi => by
                                     rw [List.getElem?_set_ne (by omega)]
                                     exact hfr_z i hi,
                                   fun i hi => by
                                     rw [hzi_succ] at hi
                                     rcases Nat.lt_or_eq_of_le
                                       (Nat.lt_succ_iff.mp hi) with hlt | rfl
                                     · rw [List.getElem?_set_ne (by omega)]
                                       exact hzero_z i hlt
                                     · rw [hidx_z, List.getElem?_set_self (by omega)],
                                   hm⟩
                              · have hzi_eq : zi.toNat = row_u32s_nat := by
                                  rw [← hw_ru_nat]; bv_omega
                                have hbits_zero : ∀ col ≤ ncols.toNat,
                                    rowBit scr_z rbase_nat col = false := by
                                  intro col hcol
                                  have hw_lt : col / 64 < (ncols.toNat + 64) / 64 := by omega
                                  unfold rowBit rowU64
                                  rw [hzero_z (2 * (col / 64)) (by omega),
                                    show rbase_nat + 2 * (col / 64) + 1 =
                                      rbase_nat + (2 * (col / 64) + 1) by omega,
                                    hzero_z (2 * (col / 64) + 1) (by omega)]
                                  simp
                                -- `k` loop: set bits for `scr[p + 1 + k]`
                                c0_hstraight
                                refine wp_loop_inv
                                  (fun (k, ()) mk => ∃ scr_k,
                                    k.toNat ≤ clen ∧ scr_k.length = c.scratch_cap ∧
                                    (∀ i, i < rbase_nat ∨ rbase_nat + row_u32s_nat ≤ i →
                                      scr_k[i]? = scr_cur[i]?) ∧
                                    (∀ col < ncols.toNat, rowBit scr_k rbase_nat col = true ↔
                                      col ∈ (List.range k.toNat).map fun j =>
                                        (s.scratch.tarjan_reach[
                                          (scr0[p.toNat + 1 + j]?.getD 0#32).toNat]?.getD
                                            0#32).toNat) ∧
                                    rowBit scr_k rbase_nat ncols.toNat = false ∧
                                    (FullMem c { s with scratch :=
                                      { s.scratch with scratch_buf := scr_k } } ⋆ R) mk)
                                  (fun (k, ()) _ => clen - k.toNat)
                                  (fun Jk hJk => by
                                    c0_hstraight
                                    exact hJk (0#64, ()) mz ⟨scr_z, Nat.zero_le _, hlen_z, hfr_z,
                                      fun col hcol => by simp [hbits_zero col (Nat.le_of_lt hcol)],
                                      hbits_zero ncols.toNat (Nat.le_refl _), hm_z⟩)
                                  (fun Jk (k, ()) mk ⟨scr_k, hk_le, hlen_k, hfr_k, hbits_k, hrhs_k,
                                      hm_k⟩ ihk => ?_)
                                c0_hsplit
                                · have hk_lt : k.toNat < clen := by rw [← hcl_w]; bv_omega
                                  have hpk_bv : (p + 1 + k).toNat = p.toNat + 1 + k.toNat := by
                                    bv_omega
                                  have hpk_lt : p.toNat + 1 + k.toNat < eq_end.toNat := by omega
                                  have hpk_len : (p + 1 + k).toNat < scr_k.length := by omega
                                  c0_hstraight
                                  dsimp only
                                  obtain ⟨vx, hvx⟩ : ∃ x : BitVec 32,
                                      scr_k[(p + 1 + k).toNat]'hpk_len = x := ⟨_, rfl⟩
                                  rw [hvx]
                                  have hvx_eq : scr0[p.toNat + 1 + k.toNat]? = some vx := by
                                    have h1 := hfr_k (p.toNat + 1 + k.toNat) (Or.inl (by omega))
                                    have h2 := hpre_cur (p.toNat + 1 + k.toNat) hpk_lt
                                    rw [← h2, ← h1,
                                      show scr_k[p.toNat + 1 + k.toNat]? =
                                        scr_k[(p + 1 + k).toNat]? from
                                        congrArg (scr_k[·]?) hpk_bv.symm,
                                      List.getElem?_eq_getElem hpk_len, hvx]
                                  have hvx_cv : vx.toNat < s.core.cur_vars := by
                                    have hmem : vx.toNat ∈ (List.range clen).map
                                        (fun j => (scr0[p.toNat + 1 + j]?.getD 0#32).toNat) := by
                                      refine List.mem_map.mpr
                                        ⟨k.toNat, List.mem_range.mpr hk_lt, ?_⟩
                                      rw [hvx_eq, Option.getD_some]
                                    exact hcv_vs vx.toNat hmem
                                  have hpar_vx :
                                      (s.scratch.work_stk1[vx.toNat]?.getD 0#32).toNat =
                                        root.toNat := by
                                    have h := hpar_all k.toNat hk_lt
                                    rwa [hvx_eq, Option.getD_some] at h
                                  have hmap_vx := hmap vx.toNat hvx_cv hpar_vx
                                  have hvxz : (vx.setWidth 64).toNat = vx.toNat :=
                                    bv_zext32_toNat vx
                                  have hvx_tr : (vx.setWidth 64).toNat <
                                      s.scratch.tarjan_reach.length := by
                                    rw [hvxz, htr_len]; omega
                                  have hk_succ : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
                                  refine wp_join0
                                    (fun mk' => ∃ scr_k',
                                      scr_k'.length = c.scratch_cap ∧
                                      (∀ i, i < rbase_nat ∨ rbase_nat + row_u32s_nat ≤ i →
                                        scr_k'[i]? = scr_cur[i]?) ∧
                                      (∀ col < ncols.toNat, rowBit scr_k' rbase_nat col = true ↔
                                        col ∈ (List.range (k.toNat + 1)).map fun j =>
                                          (s.scratch.tarjan_reach[
                                            (scr0[p.toNat + 1 + j]?.getD 0#32).toNat]?.getD
                                              0#32).toNat) ∧
                                      rowBit scr_k' rbase_nat ncols.toNat = false ∧
                                      (FullMem c { s with scratch :=
                                        { s.scratch with scratch_buf := scr_k' } } ⋆ R) mk')
                                    ?_ ?_
                                  · rintro Jks mk' ⟨scr_k', hlen_k', hfr_k', hbits_k', hrhs_k',
                                        hmk'⟩
                                    c0_hstraight
                                    exact ihk (k + 1#64, ()) mk'
                                      (by dsimp only; rw [hk_succ]; omega)
                                      ⟨scr_k', by rw [hk_succ]; omega, hlen_k', hfr_k',
                                       by simpa [hk_succ] using hbits_k', hrhs_k', hmk'⟩
                                  · intro Jks hJks
                                    c0_hsplit
                                    · c0_hstraight
                                      obtain ⟨vcol, hvcol⟩ : ∃ x : BitVec 32,
                                          s.scratch.tarjan_reach[(vx.setWidth 64).toNat]'hvx_tr =
                                            x := ⟨_, rfl⟩
                                      rw [hvcol]
                                      have hvcol_eq : s.scratch.tarjan_reach[vx.toNat]?.getD 0#32 =
                                          vcol := by
                                        rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
                                          ← hvcol]
                                        exact list_getElem_congr hvxz.symm (by omega) hvx_tr
                                      have hvcol_lt : vcol.toNat < ncols.toNat := by
                                        rw [← hvcol_eq]; exact hmap_vx.1
                                      refine wp_join0
                                        (fun mk' => ∃ scr_k',
                                          scr_k'.length = c.scratch_cap ∧
                                          (∀ i, i < rbase_nat ∨ rbase_nat + row_u32s_nat ≤ i →
                                            scr_k'[i]? = scr_cur[i]?) ∧
                                          (∀ col < ncols.toNat,
                                            rowBit scr_k' rbase_nat col = true ↔
                                            col ∈ (List.range (k.toNat + 1)).map fun j =>
                                              (s.scratch.tarjan_reach[
                                                (scr0[p.toNat + 1 + j]?.getD 0#32).toNat]?.getD
                                                  0#32).toNat) ∧
                                          rowBit scr_k' rbase_nat ncols.toNat = false ∧
                                          (FullMem c { s with scratch :=
                                            { s.scratch with scratch_buf := scr_k' } } ⋆ R) mk')
                                        (fun _ mk' h => by c0_hstraight; exact hJks mk' h)
                                        (fun Jki hJki => ?_)
                                      c0_hsplit
                                      · c0_call hSetBit
                                        refine ⟨scr_k, ncols.toNat, FullScrBufRest c s ⋆ R,
                                          by rw [bv_zext32_toNat]; exact Nat.le_of_lt hvcol_lt,
                                          by rw [hrbase_toNat, hlen_k]; exact hrbase_end,
                                          by omega, focus_full_scr_buf_upd hm_k,
                                          fun scr_k' mk' hlen_k' hfr_k' hrb_k' hmk' => ?_⟩
                                        have hmk'' : (FullMem c { s with scratch :=
                                            { s.scratch with scratch_buf := scr_k' } } ⋆ R) mk' :=
                                          unfocus_full_scr_buf hmk'
                                        c0_hstraight
                                        refine hJki mk'
                                          ⟨scr_k', hlen_k'.trans hlen_k,
                                           fun i hi => by
                                             rw [hfr_k' i (by rw [hrbase_toNat]; exact hi)]
                                             exact hfr_k i hi,
                                           ?_, ?_, hmk''⟩
                                        · intro col hcol
                                          rw [list_range_map_succ, List.mem_append,
                                            List.mem_singleton, hvx_eq, Option.getD_some, hvcol_eq]
                                          have hrb := hrb_k' col (Nat.le_of_lt hcol)
                                          rw [hrbase_toNat, bv_zext32_toNat] at hrb
                                          rw [hrb]
                                          by_cases hceq : col = vcol.toNat
                                          · simp [hceq]
                                          · simp [hceq, hbits_k col hcol]
                                        · have hrb := hrb_k' ncols.toNat (Nat.le_refl _)
                                          rw [hrbase_toNat, bv_zext32_toNat] at hrb
                                          rw [hrb, ite_eq_right (by omega), hrhs_k]
                                      · exfalso; rw [bv_zext32_toNat] at *; bv_omega
                                    · exfalso
                                      have hcv_bv : (BitVec.ofNat 64 s.core.cur_vars).toNat =
                                          s.core.cur_vars := bv64_ofNat_toNat (by omega)
                                      bv_omega
                                · have hk_eq : k.toNat = clen := by rw [← hcl_w]; bv_omega
                                  let cols := (List.range clen).map fun j =>
                                    (s.scratch.tarjan_reach[
                                      (scr0[p.toNat + 1 + j]?.getD 0#32).toNat]?.getD 0#32).toNat
                                  have hbits_all : ∀ col < ncols.toNat,
                                      rowBit scr_k rbase_nat col = true ↔ col ∈ cols := by
                                    intro col hcol; simpa [cols, hk_eq] using hbits_k col hcol
                                  have hcols_lt : ∀ col ∈ cols, col < ncols.toNat := by
                                    intro col hcol
                                    rcases List.mem_map.mp hcol with ⟨j, hj, rfl⟩
                                    have hj_lt : j < clen := List.mem_range.mp hj
                                    have hv_cv : (scr0[p.toNat + 1 + j]?.getD 0#32).toNat <
                                        s.core.cur_vars :=
                                      hcv_vs _ (List.mem_map.mpr ⟨j, hj, rfl⟩)
                                    exact (hmap _ hv_cv (hpar_all j hj_lt)).1
                                  have hcols_map : (cols.map fun col =>
                                      (s.scratch.work_stk2[col]?.getD 0#32).toNat) =
                                      (List.range clen).map
                                        (fun j => (scr0[p.toNat + 1 + j]?.getD 0#32).toNat) := by
                                    dsimp only [cols]; rw [List.map_map]
                                    refine List.map_congr_left fun j hj => ?_
                                    have hj_lt : j < clen := List.mem_range.mp hj
                                    have hv_cv : (scr0[p.toNat + 1 + j]?.getD 0#32).toNat <
                                        s.core.cur_vars :=
                                      hcv_vs _ (List.mem_map.mpr ⟨j, hj, rfl⟩)
                                    exact (hmap _ hv_cv (hpar_all j hj_lt)).2
                                  have hcols_nd : cols.Nodup := by
                                    have hvs_nd : ((List.range clen).map (fun j =>
                                        (scr0[p.toNat + 1 + j]?.getD 0#32).toNat)).Nodup :=
                                      hss.imp fun h => Nat.ne_of_lt h
                                    rw [← hcols_map] at hvs_nd
                                    exact nodup_of_map' _ hvs_nd
                                  refine wp_join0
                                    (fun mr => ∃ scr_r,
                                      scr_r.length = c.scratch_cap ∧
                                      (∀ i, i < rbase_nat ∨ rbase_nat + row_u32s_nat ≤ i →
                                        scr_r[i]? = scr_cur[i]?) ∧
                                      XorPackedRowSound (cnfOfClauses F_cur) s.scratch.work_stk2
                                        scr_r rbase_nat ncols.toNat ∧
                                      (FullMem c { s with scratch :=
                                        { s.scratch with scratch_buf := scr_r } } ⋆ R) mr)
                                    ?_ ?_
                                  · rintro Jr mr ⟨scr_r, hlen_r, hfr_r, hrow_r, hm_r⟩
                                    have hnr_succ : (nrows + 1#64).toNat = nrows.toNat + 1 := by
                                      bv_omega
                                    c0_hstraight
                                    refine hJ2 (nrows + 1#64) mr
                                      ⟨scr_r, by rw [hnr_succ]; omega, hlen_r,
                                       fun i hi => by
                                         rw [hfr_r i (Or.inl (by dsimp [rbase_nat]; omega))]
                                         exact hpre_cur i hi,
                                       ?_, hm_r⟩
                                    intro r hr
                                    rw [hnr_succ] at hr
                                    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hr) with hlt | rfl
                                    · have hdisj : eq_end.toNat + r * row_u32s_nat + row_u32s_nat ≤
                                          rbase_nat := by
                                        have := Nat.mul_le_mul_right row_u32s_nat
                                          (Nat.succ_le_of_lt hlt)
                                        simp only [Nat.succ_mul] at this
                                        dsimp [rbase_nat]; omega
                                      exact xorPackedRowSound_congr
                                        (fun i hi => hfr_r _ (Or.inl
                                          (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi _) hdisj)))
                                        (hmat_cur r hlt)
                                    · exact hrow_r
                                  · intro Jr hJr
                                    c0_hsplit
                                    · have hrhs_t : ((hdr >>> 31#32) != 0#32) = true := by
                                        simp only [bne_iff_ne, ne_eq]
                                        change hdr >>> (31 : Nat) ≠ 0#32; assumption
                                      c0_call hSetBit
                                      refine ⟨scr_k, ncols.toNat, FullScrBufRest c s ⋆ R,
                                        Nat.le_refl _,
                                        by rw [hrbase_toNat, hlen_k]; exact hrbase_end,
                                        by omega, focus_full_scr_buf_upd hm_k,
                                        fun scr_r mr hlen_r hfr_r hrb_r hmr => ?_⟩
                                      have hmr' : (FullMem c { s with scratch :=
                                          { s.scratch with scratch_buf := scr_r } } ⋆ R) mr :=
                                        unfocus_full_scr_buf hmr
                                      c0_hstraight
                                      refine hJr mr ⟨scr_r, hlen_r.trans hlen_k,
                                        fun i hi => by
                                          rw [hfr_r i (by rw [hrbase_toNat]; exact hi)]
                                          exact hfr_k i hi,
                                        ?_, hmr'⟩
                                      have hbits_r : ∀ col < ncols.toNat,
                                          rowBit scr_r rbase_nat col = true ↔ col ∈ cols := by
                                        intro col hcol
                                        have hb := hrb_r col (Nat.le_of_lt hcol)
                                        rw [hrbase_toNat, ite_eq_right (by omega)] at hb
                                        rw [hb]; exact hbits_all col hcol
                                      have hrhs_r : rowBit scr_r rbase_nat ncols.toNat = true := by
                                        have hb := hrb_r ncols.toNat (Nat.le_refl _)
                                        rw [hrbase_toNat, ite_eq_left rfl] at hb; exact hb
                                      refine xorPackedRowSound_of_xorVarsSound hcols_lt hcols_nd
                                        hbits_r ?_
                                      rw [hrhs_r, hcols_map, ← hrhs_t]; exact hsnd
                                    · have hrhs_f : ((hdr >>> 31#32) != 0#32) = false := by
                                        simp only [bne_eq_false_iff_eq]
                                        change hdr >>> (31 : Nat) = 0#32; bv_omega
                                      c0_hstraight
                                      refine hJr mk ⟨scr_k, hlen_k, hfr_k, ?_, hm_k⟩
                                      refine xorPackedRowSound_of_xorVarsSound hcols_lt hcols_nd
                                        hbits_all ?_
                                      rw [hrhs_k, hcols_map, ← hrhs_f]; exact hsnd
                            · c0_hstraight
                              exact hJ2 nrows m ⟨scr_cur, hnr_le, hlen_cur, hpre_cur, hmat_cur,
                                hm_cur⟩
                          · c0_hstraight
                            exact hJ2 nrows m ⟨scr_cur, hnr_le, hlen_cur, hpre_cur, hmat_cur,
                              hm_cur⟩
                      · c0_hstraight
                        exact hJ1 nrows m ⟨scr_cur, hnr_le, hlen_cur, hpre_cur, hmat_cur, hm_cur⟩
                    · c0_hstraight
                      exact hJ1 nrows m ⟨scr_cur, hnr_le, hlen_cur, hpre_cur, hmat_cur, hm_cur⟩
            · c0_hstraight
              have hnr_fit : eq_end.toNat + nrows.toNat * row_u32s_nat ≤ c.scratch_cap :=
                Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hnr_le) _) hmr_fit
              exact hJ0 (nrows, p, ()) m ⟨scr_cur, hlen_cur, hpre_cur, hnr_fit, hmat_cur, hm_cur⟩
          · c0_hstraight
            have hnr_fit : eq_end.toNat + nrows.toNat * row_u32s_nat ≤ c.scratch_cap :=
              Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hnr_le) _) hmr_fit
            exact hJ0 (nrows, p, ()) m ⟨scr_cur, hlen_cur, hpre_cur, hnr_fit, hmat_cur, hm_cur⟩

/-! ## 3. Packed $\mathbb{F}_2$ Gauss-Jordan RREF (`full_xor_rref`) -/

@[expose] def fullXorRrefSpec : Spec [i64, i64, i64, i64] [] :=
  fun (scr_ptr, mat, nrows, ncols, ()) m Q _ =>
    ∃ (F : CNF Nat) (c2v scr : List (BitVec 32)) (R : Mem 64 → Prop),
      mat.toNat + nrows.toNat * (2 * ((ncols.toNat + 64) / 64)) ≤ scr.length ∧
      scr.length < 2 ^ 32 ∧ ncols.toNat < 2 ^ 31 ∧ nrows.toNat < 2 ^ 32 ∧
      XorMatOk F c2v scr mat.toNat nrows.toNat ncols.toNat ∧
      (array (t := i32) scr_ptr scr ⋆ R) m ∧
      ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
        scr'.length = scr.length →
        (∀ i, i < mat.toNat ∨ mat.toNat + nrows.toNat * (2 * ((ncols.toNat + 64) / 64)) ≤ i →
          scr'[i]? = scr[i]?) →
        XorMatOk F c2v scr' mat.toNat nrows.toNat ncols.toNat →
        (array (t := i32) scr_ptr scr' ⋆ R) m' → Q () m'

theorem full_xor_rref_wp (Γ : Env)
    (hRead : ∀ a m Q X, fullXorReadU64Spec a m Q X →
      Γ "full_xor_read_u64" [i64, i64] [i64] a m Q X)
    (hSwap : ∀ a m Q X, fullXorSwapRowsSpec a m Q X →
      Γ "full_xor_swap_rows" [i64, i64, i64, i64, i64] [] a m Q X)
    (hXor : ∀ a m Q X, fullXorXorRowsSpec a m Q X →
      Γ "full_xor_xor_rows" [i64, i64, i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullXorRrefSpec a m Q X → Func.wp Γ full_xor_rref_body a m Q X := by
  rintro ⟨scr_ptr, mat, nrows, ncols, ⟨⟩⟩ m0 Q X
    ⟨F, c2v, scr0, R, hbd, hscr32, hnc31, hnr32, hmat0, hm0, hQ⟩
  let words64_nat := (ncols.toNat + 64) / 64
  let row_u32s_nat := 2 * words64_nat
  have hbd' : mat.toNat + nrows.toNat * row_u32s_nat ≤ scr0.length := hbd
  have hw64_bv : ((ncols + 64#64) >>> (6 : Nat)).toNat = words64_nat := by
    dsimp [words64_nat]; rw [bv64_shr6_toNat, BitVec.toNat_add, show (64#64).toNat = 64 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hru_bv : (((ncols + 64#64) >>> (6 : Nat)) <<< (1 : Nat)).toNat = row_u32s_nat := by
    dsimp [row_u32s_nat]; rw [bv64_shl1_toNat (by rw [hw64_bv]; dsimp [words64_nat]; omega),
      hw64_bv]
  c0_hstraight
  obtain ⟨w64, hw64⟩ : ∃ x : BitVec 64, (ncols + 64) >>> OfNat.ofNat 6 = x := ⟨_, rfl⟩
  obtain ⟨wru, hwru⟩ : ∃ x : BitVec 64, w64 <<< OfNat.ofNat 1 = x := ⟨_, rfl⟩
  have hw64_nat : w64.toNat = words64_nat := by rw [← hw64]; exact hw64_bv
  have hwru_nat : wru.toNat = row_u32s_nat := by rw [← hwru, ← hw64]; exact hru_bv
  rw [hw64, hwru]
  refine wp_loop_inv
    (fun (rank, col, ()) m => ∃ scr_cur,
      rank.toNat ≤ nrows.toNat ∧ col.toNat ≤ ncols.toNat ∧
      scr_cur.length = scr0.length ∧
      (∀ i, i < mat.toNat ∨ mat.toNat + nrows.toNat * row_u32s_nat ≤ i →
        scr_cur[i]? = scr0[i]?) ∧
      XorMatOk F c2v scr_cur mat.toNat nrows.toNat ncols.toNat ∧
      (array (t := i32) scr_ptr scr_cur ⋆ R) m)
    (fun (_, col, ()) _ => ncols.toNat - col.toNat)
    (fun J hJ => by
      c0_hstraight
      exact hJ (0#64, 0#64, ()) m0 ⟨scr0, Nat.zero_le _, Nat.zero_le _, rfl,
        fun _ _ => rfl, hmat0, hm0⟩)
    (fun J (rank, col, ()) m ⟨scr_cur, hrk_le, hcol_le, hlen_cur, hfr_cur, hmat_cur,
        hm_cur⟩ ih => ?_)
  c0_hsplit
  · have hcol_lt : col.toNat < ncols.toNat := by bv_omega
    c0_hsplit
    · have hrk_lt : rank.toNat < nrows.toNat := by bv_omega
      have hwoff_toNat : ((col >>> (6 : Nat)) <<< (1 : Nat)).toNat = 2 * (col.toNat / 64) := by
        rw [bv64_shl1_toNat (by rw [bv64_shr6_toNat]; omega), bv64_shr6_toNat]
      have hwoff_lt : 2 * (col.toNat / 64) + 1 < row_u32s_nat := by
        dsimp [row_u32s_nat, words64_nat]; omega
      c0_hstraight
      obtain ⟨woff, hwoff⟩ : ∃ x : BitVec 64,
          col >>> OfNat.ofNat 6 <<< OfNat.ofNat 1 = x := ⟨_, rfl⟩
      have hwoff_nat : woff.toNat = 2 * (col.toNat / 64) := by rw [← hwoff]; exact hwoff_toNat
      rw [hwoff]
      -- Pivot search loop (`while (r < nrows)`) with `break`
      refine wp_join_state (fun x : Tup Val [i64, i64] => x)
        (fun (piv, _r, ()) mp => piv.toNat ≤ nrows.toNat ∧ mp = m)
        ?_ ?_
      · intro Jp (piv, _r, ()) mp ⟨hpiv_le, hmp⟩
        subst mp
        c0_hstraight
        have hcol_succ : (col + 1#64).toNat = col.toNat + 1 := by bv_omega
        refine wp_join_state (fun x : Tup Val [i64, i64] => x)
          (fun (rank', _r', ()) m' => ∃ scr',
            rank'.toNat ≤ nrows.toNat ∧ scr'.length = scr0.length ∧
            (∀ i, i < mat.toNat ∨ mat.toNat + nrows.toNat * row_u32s_nat ≤ i →
              scr'[i]? = scr0[i]?) ∧
            XorMatOk F c2v scr' mat.toNat nrows.toNat ncols.toNat ∧
            (array (t := i32) scr_ptr scr' ⋆ R) m')
          ?_ ?_
        · intro Jc (rank', _r', ()) m' ⟨scr', hrk', hlen', hfr', hmat', hm'⟩
          c0_hstraight
          exact ih (rank', col + 1#64, ()) m' (by dsimp only; rw [hcol_succ]; omega)
            ⟨scr', hrk', by rw [hcol_succ]; omega, hlen', hfr', hmat', hm'⟩
        · intro Jc hJc
          c0_hsplit
          · have hpiv_lt : piv.toNat < nrows.toNat := by bv_omega
            refine wp_join0
              (fun ms => ∃ scr_s,
                scr_s.length = scr0.length ∧
                (∀ i, i < mat.toNat ∨ mat.toNat + nrows.toNat * row_u32s_nat ≤ i →
                  scr_s[i]? = scr0[i]?) ∧
                XorMatOk F c2v scr_s mat.toNat nrows.toNat ncols.toNat ∧
                (array (t := i32) scr_ptr scr_s ⋆ R) ms)
              ?_ ?_
            · rintro Js ms ⟨scr_s, hlen_s, hfr_s, hmat_s, hm_s⟩
              -- Elimination loop (`r = 0 .. nrows`)
              c0_hstraight
              refine wp_loop_inv
                (fun (r, ()) mr => ∃ scr_r,
                  r.toNat ≤ nrows.toNat ∧ scr_r.length = scr0.length ∧
                  (∀ i, i < mat.toNat ∨ mat.toNat + nrows.toNat * row_u32s_nat ≤ i →
                    scr_r[i]? = scr0[i]?) ∧
                  XorMatOk F c2v scr_r mat.toNat nrows.toNat ncols.toNat ∧
                  (array (t := i32) scr_ptr scr_r ⋆ R) mr)
                (fun (r, ()) _ => nrows.toNat - r.toNat)
                (fun Je hJe => by
                  c0_hstraight
                  exact hJe (0#64, ()) ms ⟨scr_s, Nat.zero_le _, hlen_s, hfr_s, hmat_s, hm_s⟩)
                (fun Je (r, ()) mr ⟨scr_r, hr_le, hlen_r, hfr_r, hmat_r, hm_r⟩ ihe => ?_)
              c0_hsplit
              · have hr_lt : r.toNat < nrows.toNat := by bv_omega
                have hr_succ : (r + 1#64).toNat = r.toNat + 1 := by bv_omega
                refine wp_join0
                  (fun mr' => ∃ scr_r',
                    scr_r'.length = scr0.length ∧
                    (∀ i, i < mat.toNat ∨ mat.toNat + nrows.toNat * row_u32s_nat ≤ i →
                      scr_r'[i]? = scr0[i]?) ∧
                    XorMatOk F c2v scr_r' mat.toNat nrows.toNat ncols.toNat ∧
                    (array (t := i32) scr_ptr scr_r' ⋆ R) mr')
                  ?_ ?_
                · rintro Jstep mr' ⟨scr_r', hlen_r', hfr_r', hmat_r', hm_r'⟩
                  c0_hstraight
                  exact ihe (r + 1#64, ()) mr' (by dsimp only; rw [hr_succ]; omega)
                    ⟨scr_r', by rw [hr_succ]; omega, hlen_r', hfr_r', hmat_r', hm_r'⟩
                · intro Jstep hJstep
                  c0_hsplit
                  · have hr_ne : r ≠ rank := by assumption
                    have hidx_r : (mat + r * wru + woff).toNat =
                        mat.toNat + r.toNat * row_u32s_nat + 2 * (col.toNat / 64) := by
                      have hrow_r : (r.toNat + 1) * row_u32s_nat ≤ nrows.toNat * row_u32s_nat :=
                        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hr_lt)
                      simp only [Nat.succ_mul] at hrow_r
                      have hm1 : (r * wru).toNat = r.toNat * row_u32s_nat := by
                        rw [BitVec.toNat_mul, hwru_nat, Nat.mod_eq_of_lt (by omega)]
                      have hm2 : (mat + r * wru).toNat = mat.toNat + r.toNat * row_u32s_nat := by
                        rw [BitVec.toNat_add, hm1, Nat.mod_eq_of_lt (by omega)]
                      rw [BitVec.toNat_add, hm2, hwoff_nat, Nat.mod_eq_of_lt (by omega)]
                    have hidx_bd : (mat + r * wru + woff).toNat + 1 < scr_r.length := by
                      have hrow_r : (r.toNat + 1) * row_u32s_nat ≤ nrows.toNat * row_u32s_nat :=
                        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hr_lt)
                      simp only [Nat.succ_mul] at hrow_r
                      rw [hidx_r, hlen_r]; omega
                    c0_call hRead
                    refine ⟨scr_r, R, hidx_bd, by omega, hm_r, ?_⟩
                    refine wp_join0
                      (fun mr' => ∃ scr_r',
                        scr_r'.length = scr0.length ∧
                        (∀ i, i < mat.toNat ∨ mat.toNat + nrows.toNat * row_u32s_nat ≤ i →
                          scr_r'[i]? = scr0[i]?) ∧
                        XorMatOk F c2v scr_r' mat.toNat nrows.toNat ncols.toNat ∧
                        (array (t := i32) scr_ptr scr_r' ⋆ R) mr')
                      (fun _ mr' h => by c0_hstraight; exact hJstep mr' h)
                      (fun Jxi hJxi => ?_)
                    c0_hsplit
                    · c0_call hXor
                      refine ⟨scr_r, nrows.toNat, R,
                        by rw [hw64_nat, hlen_r]; exact hbd, by omega, hr_lt, hrk_lt, hr_ne,
                        hm_r, fun scr_x mx hlen_x hfr_x hoth_x hxor_x hmx => ?_⟩
                      c0_hstraight
                      refine hJxi mx ⟨scr_x, hlen_x.trans hlen_r,
                        fun i hi => by
                          rw [hfr_x i (by rw [hw64_nat]; exact hi)]
                          exact hfr_r i hi,
                        ?_, hmx⟩
                      intro r' hr'
                      by_cases hrr : r' = r.toNat
                      · subst hrr
                        exact xorPackedRowSound_xor (words64 := words64_nat) rfl
                          (hmat_r r.toNat hr_lt) (hmat_r rank.toNat hrk_lt)
                          (fun w hw => by
                            have hx := hxor_x w (by rw [hw64_nat]; exact hw)
                            simpa [hw64_nat, row_u32s_nat, words64_nat] using hx)
                      · exact xorPackedRowSound_congr
                          (fun i hi => by
                            have ho := hoth_x r' hr' hrr i (by rw [hw64_nat]; exact hi)
                            simpa [hw64_nat, row_u32s_nat, words64_nat] using ho)
                          (hmat_r r' hr')
                    · c0_hstraight
                      exact hJxi mr ⟨scr_r, hlen_r, hfr_r, hmat_r, hm_r⟩
                  · c0_hstraight
                    exact hJstep mr ⟨scr_r, hlen_r, hfr_r, hmat_r, hm_r⟩
              · c0_hstraight
                have hrk_succ : (rank + 1#64).toNat = rank.toNat + 1 := by bv_omega
                exact hJc (rank + 1#64, r, ()) mr
                  ⟨scr_r, by rw [hrk_succ]; omega, hlen_r, hfr_r, hmat_r, hm_r⟩
            · intro Js hJs
              c0_hsplit
              · c0_call hSwap
                refine ⟨scr_cur, nrows.toNat, R,
                  by rw [hwru_nat, hlen_cur]; exact hbd, by omega, hrk_lt, hpiv_lt, hm_cur,
                  fun scr_s ms hlen_s hfr_s hsw_s hms => ?_⟩
                c0_hstraight
                refine hJs ms ⟨scr_s, hlen_s.trans hlen_cur,
                  fun i hi => by
                    rw [hfr_s i (by rw [hwru_nat]; exact hi)]
                    exact hfr_cur i hi,
                  ?_, hms⟩
                intro r' hr'
                have hsrc_lt : (if r' = rank.toNat then piv.toNat
                    else if r' = piv.toNat then rank.toNat else r') < nrows.toNat := by
                  split
                  · exact hpiv_lt
                  · split
                    · exact hrk_lt
                    · exact hr'
                exact xorPackedRowSound_congr
                  (fun i hi => by
                    have hs := hsw_s r' hr' i (by rw [hwru_nat]; exact hi)
                    simpa [hwru_nat, row_u32s_nat, words64_nat] using hs)
                  (hmat_cur _ hsrc_lt)
              · c0_hstraight
                exact hJs m ⟨scr_cur, hlen_cur, hfr_cur, hmat_cur, hm_cur⟩
          · c0_hstraight
            exact hJc (rank, _r, ()) m ⟨scr_cur, hrk_le, hlen_cur, hfr_cur, hmat_cur, hm_cur⟩
      · intro Jp hJp
        refine wp_loop_inv
          (fun (r, ()) mr => r.toNat ≤ nrows.toNat ∧ mr = m)
          (fun (r, ()) _ => nrows.toNat - r.toNat)
          (fun Jf hJf => by
            c0_hstraight
            exact hJf (rank, ()) m ⟨hrk_le, rfl⟩)
          (fun Jf (r, ()) mr ⟨hr_le, hmr⟩ ihf => ?_)
        subst mr
        c0_hsplit
        · have hr_lt : r.toNat < nrows.toNat := by bv_omega
          have hidx_r : (mat + r * wru + woff).toNat =
              mat.toNat + r.toNat * row_u32s_nat + 2 * (col.toNat / 64) := by
            have hrow_r : (r.toNat + 1) * row_u32s_nat ≤ nrows.toNat * row_u32s_nat :=
              Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hr_lt)
            simp only [Nat.succ_mul] at hrow_r
            have hm1 : (r * wru).toNat = r.toNat * row_u32s_nat := by
              rw [BitVec.toNat_mul, hwru_nat, Nat.mod_eq_of_lt (by omega)]
            have hm2 : (mat + r * wru).toNat = mat.toNat + r.toNat * row_u32s_nat := by
              rw [BitVec.toNat_add, hm1, Nat.mod_eq_of_lt (by omega)]
            rw [BitVec.toNat_add, hm2, hwoff_nat, Nat.mod_eq_of_lt (by omega)]
          have hidx_bd : (mat + r * wru + woff).toNat + 1 < scr_cur.length := by
            have hrow_r : (r.toNat + 1) * row_u32s_nat ≤ nrows.toNat * row_u32s_nat :=
              Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hr_lt)
            simp only [Nat.succ_mul] at hrow_r
            rw [hidx_r, hlen_cur]; omega
          c0_call hRead
          refine ⟨scr_cur, R, hidx_bd, by omega, hm_cur, ?_⟩
          c0_hsplit
          · c0_hstraight
            exact hJp (r, r, ()) m ⟨Nat.le_of_lt hr_lt, rfl⟩
          · have hr_succ : (r + 1#64).toNat = r.toNat + 1 := by bv_omega
            c0_hstraight
            exact ihf (r + 1#64, ()) m (by dsimp only; rw [hr_succ]; omega)
              ⟨by rw [hr_succ]; omega, rfl⟩
        · c0_hstraight
          exact hJp (nrows, r, ()) m ⟨Nat.le_refl _, rfl⟩
    · c0_hstraight
      exact hQ scr_cur m hlen_cur hfr_cur hmat_cur hm_cur
  · c0_hstraight
    exact hQ scr_cur m hlen_cur hfr_cur hmat_cur hm_cur

/-! ## 4. Small-Equation Pool Emission (`full_xor_emit_pool_small`) -/

@[expose] def fullXorEmitPoolSmallSpec : Spec [i64, i64] [i64] :=
  fun (h, eq_end, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧
      eq_end.toNat ≤ c.scratch_cap ∧
      XorEqPoolOk (cnfOfClauses F_cur) s.core.cur_vars s.scratch.scratch_buf eq_end.toNat 0 ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
        FullSparseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.cur_level = 0 → s'.core.fuel = s.core.fuel →
        s'.scratch.scratch_buf = s.scratch.scratch_buf →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem full_xor_emit_pool_small_wp (Γ : Env)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hHasBin : ∀ a m Q X, fullHasBinSpec a m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, fullXorEmitPoolSmallSpec a m Q X →
      Func.wp Γ full_xor_emit_pool_small_body a m Q X := by
  rintro ⟨h, eq_end, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s0, R, rfl, hsp0, hlvl0, heq_cap, hpool0, hm0, hQ⟩
  let scr0 := s0.scratch.scratch_buf
  have hscr0_len : scr0.length = c.scratch_cap := hsp0.1.2.scratch_buf_len
  have hcap_lt : c.scratch_cap < 268435456 := by
    have := c.hscr; rw [dimacsBound_val] at this; exact this
  have hmaxv_lt : c.max_vars < 536870912 := by
    have := c.hmaxv; rw [dimacsBound_val] at this; exact this
  have hcv_lt : s0.core.cur_vars < 536870912 := by
    have := hsp0.1.1.cur_vars_le; omega
  c0_hstraight
  refine wp_join_state1 (fun st : Val i64 => st)
    (fun _p mj => ∃ sj,
      FullSparseInvW c F0 F_cur sj ∧ sj.core.cur_vars = s0.core.cur_vars ∧
      sj.core.cur_level = 0 ∧ sj.core.fuel = s0.core.fuel ∧
      sj.scratch.scratch_buf = scr0 ∧ (FullMem c sj ⋆ R) mj)
    ?_ ?_
  · intro J0 _p mj ⟨sj, hsp_j, hcv_j, hlvl_j, hfl_j, hscr_j, hmj⟩
    c0_hstraight
    exact hQ 1#64 sj mj hsp_j hcv_j hlvl_j hfl_j hscr_j (Or.inl rfl)
      (fun h => by cases h) hmj
  · intro J0 hJ0
    refine wp_loop_inv
      (fun (p, ()) m => ∃ sp,
        p.toNat ≤ eq_end.toNat ∧
        FullSparseInvW c F0 F_cur sp ∧ sp.core.cur_vars = s0.core.cur_vars ∧
        sp.core.cur_level = 0 ∧ sp.core.fuel = s0.core.fuel ∧
        sp.scratch.scratch_buf = scr0 ∧
        XorEqPoolOk (cnfOfClauses F_cur) s0.core.cur_vars scr0 eq_end.toNat p.toNat ∧
        (FullMem c sp ⋆ R) m)
      (fun (p, ()) _ => eq_end.toNat - p.toNat)
      (fun J hJ => by
        c0_hstraight
        exact hJ (0#64, ()) m0 ⟨s0, Nat.zero_le _, hsp0, rfl, hlvl0, rfl, rfl, hpool0, hm0⟩)
      (fun J (p, ()) m ⟨sp, hp_le, hsp, hcv_p, hlvl_p, hfl_p, hscr_p, hpool_p, hm_p⟩ ih => ?_)
    c0_hsplit
    · have hp_lt : p.toNat < eq_end.toNat := by bv_omega
      generalize hp_nat : p.toNat = p_nat at hpool_p
      cases hpool_p with
      | done => rw [hp_nat] at hp_lt; exact absurd hp_lt (Nat.lt_irrefl _)
      | @step _ hdr stride clen _ hhdr hst hcl hbd hbody hrest =>
        rw [← hp_nat] at hhdr hbd hbody hrest
        have hp_len : p.toNat < sp.scratch.scratch_buf.length := by
          rw [hscr_p, hscr0_len]; omega
        have hg_p : sp.scratch.scratch_buf[p.toNat]'hp_len = hdr := by
          have h1 : sp.scratch.scratch_buf[p.toNat]? = some hdr := by rw [hscr_p]; exact hhdr
          rw [List.getElem?_eq_getElem hp_len] at h1
          exact Option.some.inj h1
        c0_hstraight
        rw [hg_p]
        obtain ⟨wst, hwst⟩ : ∃ w : BitVec 64,
            ((hdr >>> 16 &&& 32767).setWidth 64) = w := ⟨_, rfl⟩
        have hst_w : wst.toNat = stride := by
          rw [← hwst, bv_zext32_toNat,
            show (hdr >>> 16 &&& (32767 : BitVec 32)) = hdr >>> 16#32 &&& 0x7FFF#32 from rfl,
            ← hst]
        obtain ⟨wcl, hwcl⟩ : ∃ w : BitVec 64, (hdr &&& 65535).setWidth 64 = w := ⟨_, rfl⟩
        have hcl_w : wcl.toNat = clen := by
          rw [← hwcl, bv_zext32_toNat,
            show (hdr &&& (65535 : BitVec 32)) = hdr &&& 0xFFFF#32 from rfl, ← hcl]
        rw [hwst, hwcl]
        c0_hsplit
        · exfalso
          have : p.toNat + 1 + stride ≤ eq_end.toNat := hbd
          rw [← hst_w] at this; bv_omega
        · have hst_bd : p.toNat + 1 + wst.toNat ≤ eq_end.toNat := by rw [hst_w]; exact hbd
          have hp_next : (p + 1#64 + wst).toNat = p.toNat + 1 + stride := by
            rw [← hst_w]; bv_omega
          refine wp_join0
            (fun m' => ∃ sp',
              FullSparseInvW c F0 F_cur sp' ∧ sp'.core.cur_vars = s0.core.cur_vars ∧
              sp'.core.cur_level = 0 ∧ sp'.core.fuel = s0.core.fuel ∧
              sp'.scratch.scratch_buf = scr0 ∧ (FullMem c sp' ⋆ R) m')
            ?_ ?_
          · rintro Jstep m' ⟨sp', hsp', hcv', hlvl', hfl', hscr', hm'⟩
            c0_hstraight
            exact ih (p + 1#64 + wst, ()) m' (by dsimp only; omega)
              ⟨sp', by rw [hp_next]; exact hbd, hsp', hcv', hlvl', hfl', hscr',
               by rw [hp_next]; exact hrest, hm'⟩
          · intro Jstep hJstep
            refine wp_join0 (fun m_e => m_e = m) ?_ ?_
            · rintro Jelse m_e hm_e
              subst m_e
              refine wp_join0
                (fun m' => ∃ sp',
                  FullSparseInvW c F0 F_cur sp' ∧ sp'.core.cur_vars = s0.core.cur_vars ∧
                  sp'.core.cur_level = 0 ∧ sp'.core.fuel = s0.core.fuel ∧
                  sp'.scratch.scratch_buf = scr0 ∧ (FullMem c sp' ⋆ R) m')
                (fun _ m' hm' => by c0_hstraight; exact hJstep m' hm')
                (fun Je2 hJe2 => ?_)
              c0_hsplit
              · c0_hsplit
                · have hcl2 : clen = 2 := by rw [← hcl_w]; bv_omega
                  rcases hbody with h0 | ⟨_, _, _, hcv_vs, hsnd⟩
                  · omega
                  · have hp1_bv : (p + 1).toNat = p.toNat + 1 := by bv_omega
                    have hp2_bv : (p + 2).toNat = p.toNat + 2 := by bv_omega
                    have hp1_len : (p + 1).toNat < sp.scratch.scratch_buf.length := by
                      rw [hscr_p, hscr0_len]; omega
                    have hp2_len : (p + 2).toNat < sp.scratch.scratch_buf.length := by
                      rw [hscr_p, hscr0_len]; omega
                    c0_hstraight
                    obtain ⟨v0, hv0⟩ : ∃ x : BitVec 32,
                        sp.scratch.scratch_buf[(p + 1).toNat]'hp1_len = x := ⟨_, rfl⟩
                    obtain ⟨v1, hv1⟩ : ∃ x : BitVec 32,
                        sp.scratch.scratch_buf[(p + 2).toNat]'hp2_len = x := ⟨_, rfl⟩
                    rw [hv0, hv1]
                    have hv0_eq : scr0[p.toNat + 1]? = some v0 := by
                      rw [← hscr_p,
                        show sp.scratch.scratch_buf[p.toNat + 1]? =
                          sp.scratch.scratch_buf[(p + 1).toNat]? from
                          congrArg (sp.scratch.scratch_buf[·]?) hp1_bv.symm,
                        List.getElem?_eq_getElem hp1_len, hv0]
                    have hv1_eq : scr0[p.toNat + 2]? = some v1 := by
                      rw [← hscr_p,
                        show sp.scratch.scratch_buf[p.toNat + 2]? =
                          sp.scratch.scratch_buf[(p + 2).toNat]? from
                          congrArg (sp.scratch.scratch_buf[·]?) hp2_bv.symm,
                        List.getElem?_eq_getElem hp2_len, hv1]
                    refine wp_join0
                      (fun m' => ∃ sp',
                        FullSparseInvW c F0 F_cur sp' ∧ sp'.core.cur_vars = s0.core.cur_vars ∧
                        sp'.core.cur_level = 0 ∧ sp'.core.fuel = s0.core.fuel ∧
                        sp'.scratch.scratch_buf = scr0 ∧ (FullMem c sp' ⋆ R) m')
                      (fun _ m' hm' => by c0_hstraight; exact hJe2 m' hm')
                      (fun Jb2 hJb2 => ?_)
                    c0_hsplit
                    · c0_hsplit
                      · c0_hsplit
                        · have hcv_bv : (BitVec.ofNat 64 s0.core.cur_vars).toNat =
                              s0.core.cur_vars := bv64_ofNat_toNat (by omega)
                          have hv0_cv : v0.toNat < s0.core.cur_vars := by
                            have hz := bv_zext32_toNat v0; bv_omega
                          have hv1_cv : v1.toNat < s0.core.cur_vars := by
                            have hz := bv_zext32_toNat v1; bv_omega
                          have hvs2 : ((List.range clen).map
                              fun i => (scr0[p.toNat + 1 + i]?.getD 0#32).toNat) =
                              [v0.toNat, v1.toNat] := by
                            rw [hcl2]; simp [List.range_succ, hv0_eq, hv1_eq]
                          rw [hvs2] at hsnd
                          have hbins := entails_bins_of_xorVarsSound hsnd
                          have hrb_le : (hdr >>> 31#32).toNat ≤ 1 := bv32_shr31_le_one hdr
                          have ha1_eq : ((v0 <<< (1 : Nat)) ||| (hdr >>> 31#32)).toNat =
                              mkLit v0.toNat (!((hdr >>> 31#32) != 0#32)) :=
                            (bv32_lit_from_var_rhs_mkLit (by omega) hrb_le).2
                          have hb1_eq : ((v1 <<< (1 : Nat)) ||| 1#32).toNat =
                              mkLit v1.toNat false := by
                            have := bv32_lit_from_var_rhs (v := v1) (rb := 1#32)
                              (by omega) (by decide)
                            simpa [mkLit] using this
                          have ha2_eq : ((v0 <<< (1 : Nat)) ||| ((hdr >>> 31#32) ^^^ 1#32)).toNat =
                              mkLit v0.toNat ((hdr >>> 31#32) != 0#32) :=
                            (bv32_lit_from_var_rhs_mkLit (by omega) hrb_le).1
                          have hb2_eq : (v1 <<< (1 : Nat)).toNat = mkLit v1.toNat true := by
                            have := bv32_lit_from_var_rhs (v := v1) (rb := 0#32)
                              (by omega) (by decide)
                            simpa [mkLit] using this
                          refine wp_join0
                            (fun m1 => ∃ s1,
                              FullSparseInvW c F0 F_cur s1 ∧ s1.core.cur_vars = s0.core.cur_vars ∧
                              s1.core.cur_level = 0 ∧ s1.core.fuel = s0.core.fuel ∧
                              s1.scratch.scratch_buf = scr0 ∧ (FullMem c s1 ⋆ R) m1)
                            ?_ ?_
                          · rintro Jb1 m1 ⟨s1, hsp1, hcv1, hlvl1, hfl1, hscr1, hm1⟩
                            c0_hstraight
                            refine wp_join0
                              (fun m2 => ∃ s2,
                                FullSparseInvW c F0 F_cur s2 ∧ s2.core.cur_vars = s0.core.cur_vars ∧
                                s2.core.cur_level = 0 ∧ s2.core.fuel = s0.core.fuel ∧
                                s2.scratch.scratch_buf = scr0 ∧ (FullMem c s2 ⋆ R) m2)
                              (fun _ m2 h => by c0_hstraight; exact hJb2 m2 h)
                              (fun Js hJs => ?_)
                            c0_call hHasBin
                            refine ⟨c, F0, F_cur, s1, R, rfl, hsp1.1, hsp1.2.1, hm1,
                              fun ok2 _ => ?_⟩
                            c0_hsplit
                            · c0_hstraight
                              exact hJs m1 ⟨s1, hsp1, hcv1, hlvl1, hfl1, hscr1, hm1⟩
                            · c0_hstraight
                              c0_hsplit
                              · c0_call hAddBin
                                refine ⟨c, F0, F_cur, s1, R, rfl, hsp1.1, hsp1.2.1, hlvl1,
                                  fun _ _ => by
                                    change (cnfOfClauses F_cur).EntailsClause (cnfClause
                                      [((v0 <<< (1 : Nat)) ||| ((hdr >>> 31#32) ^^^ 1#32)).toNat,
                                       (v1 <<< (1 : Nat)).toNat])
                                    rw [ha2_eq, hb2_eq]; exact hbins.2,
                                  hm1, fun br2 vals' flags' lvl' rsns' trl' tp' te' unass' unfl'
                                    wvec' wstk' wlen' wu' nb' oom' inc' phases' wsort' m2 hlen2
                                    hw2 hbr2 h20 _ hm2 => ?_⟩
                                let s2 : FullState := { s1 with
                                  core := { s1.core with
                                    vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                    trl := trl', trail_pos := tp', trail_end := te',
                                    unassigned := unass', unflushed := unfl', wvec := wvec',
                                    wstk := wstk', wlen := wlen', wusable := wu',
                                    num_binary := nb', oom := oom', inconsistent := inc' }
                                  scratch := { s1.scratch with
                                    phases := phases', wsort := wsort' } }
                                have hsp2 : FullSparseInvW c F0 F_cur s2 :=
                                  fullSparseInvW_of_addBin hsp1 s2 rfl hlen2 hw2
                                c0_hsplit
                                · c0_hstraight
                                  exact hQ 20#64 s2 m2 hsp2 hcv1 hlvl1 hfl1 hscr1 (Or.inr rfl)
                                    (fun _ => (h20 (by assumption)).1) hm2
                                · c0_hsplit
                                  · c0_hstraight
                                    exact hQ 1#64 { s2 with core := { s2.core with oom := 0#64 } }
                                      _ (fullSparseInvW_upd_oom hsp2 0#64) hcv1 hlvl1 hfl1 hscr1
                                      (Or.inl rfl) (fun h => by cases h) hm
                                  · c0_hstraight
                                    exact hJs m2 ⟨s2, hsp2, hcv1, hlvl1, hfl1, hscr1, hm2⟩
                              · c0_hstraight
                                exact hJs m1 ⟨s1, hsp1, hcv1, hlvl1, hfl1, hscr1, hm1⟩
                          · intro Jb1 hJb1
                            c0_call hHasBin
                            refine ⟨c, F0, F_cur, sp, R, rfl, hsp.1, hsp.2.1, hm_p,
                              fun ok1 _ => ?_⟩
                            c0_hsplit
                            · c0_hstraight
                              exact hJb1 m ⟨sp, hsp, hcv_p, hlvl_p, hfl_p, hscr_p, hm_p⟩
                            · c0_hstraight
                              c0_hsplit
                              · c0_call hAddBin
                                refine ⟨c, F0, F_cur, sp, R, rfl, hsp.1, hsp.2.1, hlvl_p,
                                  fun _ _ => by
                                    change (cnfOfClauses F_cur).EntailsClause (cnfClause
                                      [((v0 <<< (1 : Nat)) ||| (hdr >>> 31#32)).toNat,
                                       ((v1 <<< (1 : Nat)) ||| 1#32).toNat])
                                    rw [ha1_eq, hb1_eq]; exact hbins.1,
                                  hm_p, fun br1 vals' flags' lvl' rsns' trl' tp' te' unass' unfl'
                                    wvec' wstk' wlen' wu' nb' oom' inc' phases' wsort' m1 hlen1
                                    hw1 hbr1 h20 _ hm1 => ?_⟩
                                let s1 : FullState := { sp with
                                  core := { sp.core with
                                    vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                    trl := trl', trail_pos := tp', trail_end := te',
                                    unassigned := unass', unflushed := unfl', wvec := wvec',
                                    wstk := wstk', wlen := wlen', wusable := wu',
                                    num_binary := nb', oom := oom', inconsistent := inc' }
                                  scratch := { sp.scratch with
                                    phases := phases', wsort := wsort' } }
                                have hsp1 : FullSparseInvW c F0 F_cur s1 :=
                                  fullSparseInvW_of_addBin hsp s1 rfl hlen1 hw1
                                c0_hsplit
                                · c0_hstraight
                                  exact hQ 20#64 s1 m1 hsp1 hcv_p hlvl_p hfl_p hscr_p (Or.inr rfl)
                                    (fun _ => (h20 (by assumption)).1) hm1
                                · c0_hsplit
                                  · c0_hstraight
                                    exact hQ 1#64 { s1 with core := { s1.core with oom := 0#64 } }
                                      _ (fullSparseInvW_upd_oom hsp1 0#64) hcv_p hlvl_p hfl_p hscr_p
                                      (Or.inl rfl) (fun h => by cases h) hm
                                  · c0_hstraight
                                    exact hJb1 m1 ⟨s1, hsp1, hcv_p, hlvl_p, hfl_p, hscr_p, hm1⟩
                              · c0_hstraight
                                exact hJb1 m ⟨sp, hsp, hcv_p, hlvl_p, hfl_p, hscr_p, hm_p⟩
                        · c0_hstraight
                          exact hJb2 m ⟨sp, hsp, hcv_p, hlvl_p, hfl_p, hscr_p, hm_p⟩
                      · c0_hstraight
                        exact hJb2 m ⟨sp, hsp, hcv_p, hlvl_p, hfl_p, hscr_p, hm_p⟩
                    · c0_hstraight
                      exact hJb2 m ⟨sp, hsp, hcv_p, hlvl_p, hfl_p, hscr_p, hm_p⟩
                · c0_hstraight
                  exact hJe2 m ⟨sp, hsp, hcv_p, hlvl_p, hfl_p, hscr_p, hm_p⟩
              · c0_hstraight
                exact hJe2 m ⟨sp, hsp, hcv_p, hlvl_p, hfl_p, hscr_p, hm_p⟩
            · intro Jelse hJelse
              c0_hsplit
              · c0_hsplit
                · have hcl1 : clen = 1 := by rw [← hcl_w]; bv_omega
                  rcases hbody with h0 | ⟨_, _, _, hcv_vs, hsnd⟩
                  · omega
                  · have hp1_bv : (p + 1).toNat = p.toNat + 1 := by bv_omega
                    have hp1_len : (p + 1).toNat < sp.scratch.scratch_buf.length := by
                      rw [hscr_p, hscr0_len]; omega
                    c0_hstraight
                    obtain ⟨v0, hv0⟩ : ∃ x : BitVec 32,
                        sp.scratch.scratch_buf[(p + 1).toNat]'hp1_len = x := ⟨_, rfl⟩
                    rw [hv0]
                    have hv0_eq : scr0[p.toNat + 1]? = some v0 := by
                      rw [← hscr_p,
                        show sp.scratch.scratch_buf[p.toNat + 1]? =
                          sp.scratch.scratch_buf[(p + 1).toNat]? from
                          congrArg (sp.scratch.scratch_buf[·]?) hp1_bv.symm,
                        List.getElem?_eq_getElem hp1_len, hv0]
                    refine wp_join0
                      (fun m' => ∃ sp',
                        FullSparseInvW c F0 F_cur sp' ∧ sp'.core.cur_vars = s0.core.cur_vars ∧
                        sp'.core.cur_level = 0 ∧ sp'.core.fuel = s0.core.fuel ∧
                        sp'.scratch.scratch_buf = scr0 ∧ (FullMem c sp' ⋆ R) m')
                      (fun _ m' hm' => by c0_hstraight; exact hJstep m' hm')
                      (fun Ju hJu => ?_)
                    c0_hsplit
                    · have hv0_cv : v0.toNat < s0.core.cur_vars := by
                        have hcv_bv : (BitVec.ofNat 64 s0.core.cur_vars).toNat =
                            s0.core.cur_vars := bv64_ofNat_toNat (by omega)
                        have hz := bv_zext32_toNat v0; bv_omega
                      have hvs1 : ((List.range clen).map
                          fun i => (scr0[p.toNat + 1 + i]?.getD 0#32).toNat) = [v0.toNat] := by
                        rw [hcl1]; simp [hv0_eq]
                      rw [hvs1] at hsnd
                      have hrb_le : (hdr >>> 31#32).toNat ≤ 1 := bv32_shr31_le_one hdr
                      have hlit_eq : ((v0 <<< (1 : Nat)) ||| ((hdr >>> 31#32) ^^^ 1#32)).toNat =
                          mkLit v0.toNat ((hdr >>> 31#32) != 0#32) :=
                        (bv32_lit_from_var_rhs_mkLit (by omega) hrb_le).1
                      have hlit_lt : ((v0 <<< (1 : Nat)) ||| ((hdr >>> 31#32) ^^^ 1#32)).toNat <
                          2 * sp.core.cur_vars := by
                        rw [hlit_eq, hcv_p]
                        unfold mkLit; cases ((hdr >>> 31#32) != 0#32) <;> simp <;> omega
                      c0_call hAddUnit
                      refine ⟨c, F0, F_cur, sp, R, rfl, hsp.1, hsp.2.1,
                        fun _ => by
                          change (cnfOfClauses F_cur).EntailsClause
                            (cnfClause [((v0 <<< (1 : Nat)) ||| ((hdr >>> 31#32) ^^^ 1#32)).toNat])
                          rw [hlit_eq]; exact entails_unit_of_xorVarsSound hsnd,
                        hm_p, fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl'
                          inc' phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m' hlen' hw' hcl'
                          hfail1 _ hm' => ?_⟩
                      let sp' : FullState := { sp with
                        core := { sp.core with
                          vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                          trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                          cur_level := cl', unassigned := unass', unflushed := unfl',
                          inconsistent := inc' }
                        scratch := { sp.scratch with
                          phases := phases', target_assigned := ta', best_assigned := ba',
                          phases_target := pt', phases_best := pb', heap := hp', pos := ps',
                          heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' } }
                      have hsp' : FullSparseInvW c F0 F_cur sp' :=
                        fullSparseInvW_of_addUnit hsp sp' rfl hlen' hw'
                      c0_hsplit
                      · c0_hstraight
                        exact hJu m' ⟨sp', hsp', hcv_p, hcl', hfl_p, hscr_p, hm'⟩
                      · have hok_f : ok = false := by cases ok <;> simp_all
                        c0_hstraight
                        exact hQ 20#64 sp' m' hsp' hcv_p hcl' hfl_p hscr_p (Or.inr rfl)
                          (fun _ => (hfail1 hlit_lt hok_f).1) hm'
                    · c0_hstraight
                      exact hJu m ⟨sp, hsp, hcv_p, hlvl_p, hfl_p, hscr_p, hm_p⟩
                · c0_hstraight; exact hJelse m rfl
              · c0_hstraight; exact hJelse m rfl
    · c0_hstraight
      exact hJ0 p m ⟨sp, hsp, hcv_p, hlvl_p, hfl_p, hscr_p, hm_p⟩

end LeanQbe.T.Examples.Kissat.FullM8XorGauss
