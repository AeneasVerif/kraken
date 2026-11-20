module

public import LeanQbe.T.Examples.Kissat.CorePlusSpec
public import LeanQbe.T.Logic.C0Step
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step
import all Kraken.Mem
import all Kraken.Separation

/-!
# Soundness Proofs for Kissat `CorePlus` Arena Primitives and Initialization (`Stage 2`)
Proves `Func.wp` specs for `kissat_{assign,add_watch,add_clause,backtrack,zero_tables,init_state}`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.CorePlus

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil LeanQbe.T.Examples.LratBytes
open Kraken.Bedrock2.Test

/-! ## 1. `bv_c0`, `cp_steps`, and `@[c0_load]` / `@[c0_store]` arena bridge -/

namespace IngestTactics

section BvC0Extras
@[scoped bv_c0] theorem bv32_toNat_0 : (0 : BitVec 32).toNat = 0 := rfl
@[scoped bv_c0] theorem bv32_toNat_1 : (1 : BitVec 32).toNat = 1 := rfl
@[scoped bv_c0] theorem bv64_toNat_0 : (0 : BitVec 64).toNat = 0 := rfl
@[scoped bv_c0] theorem bv64_toNat_1 : (1 : BitVec 64).toNat = 1 := rfl
@[scoped bv_c0] theorem bv_c0_xor1 (n : Nat) : n ^^^ 1 = n + 1 - 2 * (n % 2) := by
  have h := Kissat.litNeg_eq n; unfold Kissat.litNeg at h; rw [h]; split <;> omega
@[scoped bv_c0] theorem cfg_mv_mod (c : CorePlusCfg) : c.mv % 2 ^ 64 = c.mv := by
  have := c.hmv; unfold dimacsBound at this; exact Nat.mod_eq_of_lt (by omega)
@[scoped bv_c0] theorem cfg_nc_mod (c : CorePlusCfg) : c.nc % 2 ^ 64 = c.nc := by
  have := c.hnc; unfold dimacsBound at this; exact Nat.mod_eq_of_lt (by omega)
@[scoped bv_c0] theorem cfg_max_c_mod (c : CorePlusCfg) : c.max_c % 2 ^ 64 = c.max_c := by
  have := c.hmax_c; unfold dimacsBound at this; exact Nat.mod_eq_of_lt (by omega)
@[scoped bv_c0] theorem cfg_lcap_mod (c : CorePlusCfg) : c.lcap % 2 ^ 64 = c.lcap := by
  have := c.hlcap; unfold dimacsBound at this; exact Nat.mod_eq_of_lt (by omega)
@[scoped bv_c0] theorem bv32_toNat_mod64 (x : BitVec 32) : x.toNat % 2 ^ 64 = x.toNat :=
  Nat.mod_eq_of_lt (by have := x.isLt; omega)
@[scoped bv_c0] theorem bv32_div2_mod64 (x : BitVec 32) : (x.toNat / 2) % 2 ^ 64 = x.toNat / 2 :=
  Nat.mod_eq_of_lt (by have := x.isLt; omega)
@[scoped bv_c0] theorem bv64_toNat_mod64 (x : BitVec 64) : x.toNat % 2 ^ 64 = x.toNat :=
  Nat.mod_eq_of_lt x.isLt
theorem bv64_setWidth32_ofNat (x : Nat) :
    BitVec.setWidth 32 (BitVec.ofNat 64 x) = BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd _ (by decide)
attribute [scoped bv_c0] BitVec.toNat_ushiftRight BitVec.toNat_shiftLeft BitVec.toNat_xor
  BitVec.toNat_and Nat.shiftLeft_eq Nat.shiftRight_eq_div_pow List.length_set List.length_replicate
attribute [scoped bv_c0 high] LeanQbe.T.bv_c0_zext32_64 LeanQbe.T.bv_c0_zext8_64
  LeanQbe.T.bv_c0_zext8_32
end BvC0Extras

/-- Strip `Expr.mdata` wrappers on the goal target before running `c0_steps`. -/
scoped elab "cp_unmdata" : tactic => Lean.Elab.Tactic.liftMetaTactic1 fun g => do
  let ty ← Lean.instantiateMVars (← g.getType)
  if ty.isMData then return some (← g.replaceTargetDefEq ty.consumeMData) else return some g

scoped macro "cp_clean" : tactic =>
  `(tactic| simp only [Nat.reduceLeDiff, Nat.le_refl, true_and, and_true, Bool.false_or,
    Bool.or_false, Bool.true_and, Bool.and_true, Bool.not_true, Bool.not_false,
    decide_eq_true_eq, decide_eq_false_iff_not])

/-- Run `c0_steps`, discharging width side-conditions left by `zext`/`sext`/`trunc`. -/
scoped macro "cp_steps" : tactic =>
  `(tactic| (all_goals try cp_unmdata; c0_steps; repeat (
    any_goals cp_clean
    all_goals try cp_unmdata; c0_steps)))

section C0ArenaMem
variable {c : CorePlusCfg} {s : CorePlusState} {R : Mem 64 → Prop} {m : Mem 64}

private theorem cp_ptr_add_ofNat (p : BitVec 64) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

private theorem c0_store_cls_at (cid : BitVec 64) (k offb : Nat) (v : BitVec 32)
    (hk : 16 * cid.toNat + offb = 4 * (4 * cid.toNat + k)) (hm : (CorePlusMem c s ⋆ R) m)
    (hi : 4 * cid.toNat + k < s.cls.length) :
    storeOk m i32 (c.pClauses + cid * 16 + BitVec.ofNat 64 offb) ∧
      (CorePlusMem c { s with cls := s.cls.set (4 * cid.toNat + k) v } ⋆ R)
        (storeMem m i32 (c.pClauses + cid * 16 + BitVec.ofNat 64 offb) v) := by
  rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, c0_mul_ofNat, cp_ptr_add_ofNat, hk]
  exact store_arena_cls v hi hm

@[scoped c0_store] theorem c0_store_lpool_off (off idx : BitVec 64) (v : BitVec 32)
    (hm : (CorePlusMem c s ⋆ R) m) (hi : off.toNat + idx.toNat < s.lpool.length) :
    storeOk m i32 (c.pLpool + off * 4 + idx * 4) ∧
      (CorePlusMem c { s with lpool := s.lpool.set (off.toNat + idx.toNat) v } ⋆ R)
        (storeMem m i32 (c.pLpool + off * 4 + idx * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat, c0_mul_ofNat,
    cp_ptr_add_ofNat, ← Nat.mul_add]; exact store_arena_lpool v hi hm

@[scoped c0_store] theorem c0_store_cls_off (cid : BitVec 64) (v : BitVec 32)
    (hm : (CorePlusMem c s ⋆ R) m) (hi : 4 * cid.toNat < s.cls.length) :
    storeOk m i32 (c.pClauses + cid * 16) ∧
      (CorePlusMem c { s with cls := s.cls.set (4 * cid.toNat) v } ⋆ R)
        (storeMem m i32 (c.pClauses + cid * 16) v) := by
  rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, c0_mul_ofNat,
    show 16 * cid.toNat = 4 * (4 * cid.toNat) by omega]; exact store_arena_cls v hi hm

@[scoped c0_store] theorem c0_store_cls_size (cid : BitVec 64) (v : BitVec 32)
    (hm : (CorePlusMem c s ⋆ R) m) (hi : 4 * cid.toNat + 1 < s.cls.length) :
    storeOk m i32 (c.pClauses + cid * 16 + 4) ∧ (CorePlusMem c
      { s with cls := s.cls.set (4 * cid.toNat + 1) v } ⋆ R)
      (storeMem m i32 (c.pClauses + cid * 16 + 4) v) := c0_store_cls_at cid 1 4 v (by omega) hm hi
@[scoped c0_store] theorem c0_store_cls_searched (cid : BitVec 64) (v : BitVec 32)
    (hm : (CorePlusMem c s ⋆ R) m) (hi : 4 * cid.toNat + 2 < s.cls.length) :
    storeOk m i32 (c.pClauses + cid * 16 + 8) ∧ (CorePlusMem c
      { s with cls := s.cls.set (4 * cid.toNat + 2) v } ⋆ R)
      (storeMem m i32 (c.pClauses + cid * 16 + 8) v) := c0_store_cls_at cid 2 8 v (by omega) hm hi
@[scoped c0_store] theorem c0_store_cls_pad (cid : BitVec 64) (v : BitVec 32)
    (hm : (CorePlusMem c s ⋆ R) m) (hi : 4 * cid.toNat + 3 < s.cls.length) :
    storeOk m i32 (c.pClauses + cid * 16 + 12) ∧ (CorePlusMem c
      { s with cls := s.cls.set (4 * cid.toNat + 3) v } ⋆ R)
      (storeMem m i32 (c.pClauses + cid * 16 + 12) v) := c0_store_cls_at cid 3 12 v (by omega) hm hi
@[scoped c0_load] theorem c0_load_tmp0 (hm : (CorePlusMem c s ⋆ R) m) (hi : 0 < s.tmp.length) :
    loadVal m i32 (c.pTmp + 0#64) = some (s.tmp[0]'hi) := by
  rw [BitVec.add_zero, show c.pTmp = c.pTmp + BitVec.ofNat 64 (4 * 0) from (BitVec.add_zero _).symm]
  exact load_arena_tmp hi hm
@[scoped c0_load] theorem c0_load_tmp4 (hm : (CorePlusMem c s ⋆ R) m) (hi : 1 < s.tmp.length) :
    loadVal m i32 (c.pTmp + 4#64) = some (s.tmp[1]'hi) := by
  rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 (4 * 1) from rfl]; exact load_arena_tmp hi hm
end C0ArenaMem

end IngestTactics
open scoped IngestTactics
export IngestTactics (cp_ptr_add_ofNat bv64_setWidth32_ofNat)

/-! ## 2. `kissat_assign` and `kissat_add_watch` -/

private theorem bv64_add1_toNat {n : Nat} (h : n + 1 < 2 ^ 64) :
    (BitVec.ofNat 64 n + 1).toNat = n + 1 := by
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add,
    Kissat.bv64_ofNat_toNat h]

private abbrev cpAssignSt (s : CorePlusState) (lit rsn : BitVec 32) (ph : List (BitVec 8)) :
    CorePlusState :=
  { s with
    vals := (s.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
    lvl := s.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 s.cur_level)
    rsns := s.rsns.set (lit.toNat / 2) rsn, trl := s.trl.set s.trail_end lit
    trail_end := s.trail_end + 1, heur := { s.heur with phases := ph } }

private theorem assign_wp_ok {c : CorePlusCfg} {s : CorePlusState} {lit rsn : BitVec 32}
    (ph_b : BitVec 8) {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []}
    (hlen : s.LengthsOk c) (htelt : s.trail_end < c.mv)
    (hm : (CorePlusMem c (cpAssignSt s lit rsn (s.heur.phases.set (lit.toNat / 2) ph_b)) ⋆ R) m)
    (hQ : ∀ ph' m', ph'.length = c.mv → (cpAssignSt s lit rsn ph').LengthsOk c →
      (CorePlusMem c (cpAssignSt s lit rsn ph') ⋆ R) m' → Q () m') : Q () m := by
  have hh := hlen.heur_ok
  exact hQ (s.heur.phases.set (lit.toNat / 2) ph_b) m (by simp [hh.phases_len])
    { hlen with
      vals_len := by simp [hlen.vals_len], lvl_len := by simp [hlen.lvl_len],
      rsns_len := by simp [hlen.rsns_len], trl_len := by simp [hlen.trl_len],
      trail_end_le := by dsimp; omega,
      propagated_le := by dsimp; have := hlen.propagated_le; omega,
      heur_ok := { hh with phases_len := by simp [hh.phases_len] } } hm

theorem kissat_assign_wp (Γ : Env) :
    ∀ a m Q X, corePlusAssignSpec a m Q X → Func.wp Γ kissat_assign_body a m Q X := by
  rintro ⟨h, lit, rsn, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hmv := c.hmv; unfold dimacsBound at hmv; have hphl := hlen.heur_ok.phases_len
  have ⟨hvl, _, hll, hrsl, htrl, _, _, _, _, _, _, _, _, _, htel, _, hcll, _, _, _, _⟩ := hlen
  have h1 : (BitVec.setWidth 64 lit).toNat = lit.toNat := bv_c0_zext32_64 lit
  have h2 : (BitVec.setWidth 64 (lit ^^^ 1)).toNat = lit.toNat ^^^ 1 := by
    rw [bv_c0_zext32_64, BitVec.toNat_xor]; rfl
  have h3 : (BitVec.setWidth 64 (lit >>> 1)).toNat = lit.toNat / 2 := by
    rw [bv_c0_zext32_64, Kissat.bv32_lshr_1]
  have h4 : (BitVec.ofNat 64 s.trail_end).toNat = s.trail_end := Kissat.bv64_ofNat_toNat (by omega)
  have h5 : (BitVec.ofNat 64 s.trail_end + 1).toNat = s.trail_end + 1 := bv64_add1_toNat (by omega)
  have h6 : BitVec.setWidth 32 (BitVec.ofNat 64 s.cur_level) = BitVec.ofNat 32 s.cur_level :=
    bv64_setWidth32_ofNat s.cur_level
  cp_steps
  · simp only [show c.mv ≤ lit.toNat / 2 ∨ c.mv ≤ s.trail_end from
      Or.inl ‹c.mv ≤ lit.toNat / 2 ^ 1›, ite_true] at hQ; exact hQ
  · simp only [show c.mv ≤ lit.toNat / 2 ∨ c.mv ≤ s.trail_end from
      Or.inr (Nat.le_trans ‹c.mv ≤ s.trail_end % 2 ^ 64› (Nat.mod_le _ _)), ite_true] at hQ
    exact hQ
  all_goals
    have hnot : ¬ (c.mv ≤ lit.toNat / 2 ∨ c.mv ≤ s.trail_end) := by
      clear hm hQ; simp only [Nat.reducePow] at *; omega
    simp only [hnot, ite_false] at hQ; rw [h1, h2, h3, h4, h5, h6] at hm
    exact assign_wp_ok _ hlen (by omega) hm hQ

theorem kissat_add_watch_wp (Γ : Env) :
    ∀ a m Q X, corePlusAddWatchSpec a m Q X → Func.wp Γ kissat_add_watch_body a m Q X := by
  rintro ⟨h, w, lit, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hwhl := hlen.wh_len; have hwnl := hlen.wn_len
  cp_steps <;> first
    | exact hQ s.wh s.wn m hwhl hwnl hm | exact hQ _ _ _ (by simp [hwhl]) (by simp [hwnl]) hm

/-! ## 3. `kissat_add_clause` -/

private theorem addClause_exit {c : CorePlusCfg} {s : CorePlusState} (hlen : s.LengthsOk c)
    {len : BitVec 32} (hlen_mv : len.toNat ≤ c.mv) (hnc_lt : s.num_clauses < c.max_c)
    (hlen_rem : len.toNat ≤ c.lcap - s.lit_len) {lpool' wh' wn' : List (BitVec 32)}
    (hlpl' : lpool'.length = c.lcap) (hwl' : wh'.length = 2 * c.mv)
    (hwnl' : wn'.length = 2 * c.max_c) (hlp_old : ∀ k < s.lit_len, lpool'[k]? = s.lpool[k]?)
    (hlp_new : ∀ k < len.toNat, lpool'[s.lit_len + k]? = s.tmp[k]?) {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i64]}
    (hm : (CorePlusMem c (addClauseState s len.toNat lpool'
      ((((s.cls.set (4 * s.num_clauses) (BitVec.ofNat 32 s.lit_len)).set
        (4 * s.num_clauses + 1) len).set (4 * s.num_clauses + 2) 2#32).set
        (4 * s.num_clauses + 3) 0#32) wh' wn') ⋆ R) m)
    (hQ : ∀ lpool' cls' wh' wn' m',
      let s' := addClauseState s len.toNat lpool' cls' wh' wn'
      s'.LengthsOk c → (∀ id < s.num_clauses, clauseOff s' id = clauseOff s id ∧
        clauseSize s' id = clauseSize s id) →
      (∀ k < s.lit_len, lpool'[k]? = s.lpool[k]?) → clauseOff s' s.num_clauses = s.lit_len →
      clauseSize s' s.num_clauses = len.toNat →
      clauseLits s' s.num_clauses = (s.tmp.take len.toNat).map BitVec.toNat →
      (CorePlusMem c s' ⋆ R) m' → Q (BitVec.ofNat 64 s.num_clauses, ()) m') :
    Q (BitVec.ofNat 64 s.num_clauses, ()) m := by
  let cid := s.num_clauses
  let cls' := (((s.cls.set (4 * cid) (BitVec.ofNat 32 s.lit_len)).set (4 * cid + 1) len).set
    (4 * cid + 2) 2#32).set (4 * cid + 3) 0#32
  let s' := addClauseState s len.toNat lpool' cls' wh' wn'
  have hmc := c.hmax_c; have hlc := c.hlcap; unfold dimacsBound at hmc hlc
  have hll_le := hlen.lit_len_le
  have hoff32 : (BitVec.ofNat 32 s.lit_len).toNat = s.lit_len := Kissat.bv32_ofNat_toNat (by omega)
  have hcls'_len : cls'.length = 4 * c.max_c := by simp [cls', hlen.cls_len]
  have hoff_new : clauseOff s' cid = s.lit_len := by
    unfold clauseOff s' addClauseState; dsimp only
    rw [show cls' = _ from rfl, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_self (by rw [hlen.cls_len]; omega)]
    exact hoff32
  have hsz_new : clauseSize s' cid = len.toNat := by
    unfold clauseSize s' addClauseState; dsimp only
    rw [show cls' = _ from rfl, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by simp [hlen.cls_len]; omega)]; rfl
  refine hQ lpool' cls' wh' wn' m { hlen with
      wh_len := hwl', cls_len := hcls'_len, wn_len := hwnl', lpool_len := hlpl',
      lit_len_le := by dsimp [s', addClauseState]; omega,
      num_clauses_le := by dsimp [s', addClauseState]; omega }
    (fun id hid => by
      unfold clauseOff clauseSize addClauseState; dsimp only [s']
      exact ⟨by show _ = (s.cls[4 * id]?.getD 0#32).toNat; rw [show cls' = _ from rfl]
                repeat rw [List.getElem?_set_ne (by omega)],
        by show _ = (s.cls[4 * id + 1]?.getD 0#32).toNat; rw [show cls' = _ from rfl]
           repeat rw [List.getElem?_set_ne (by omega)]⟩)
    hlp_old hoff_new hsz_new (by
      unfold clauseLits; rw [hoff_new, hsz_new]
      apply List.ext_getElem (by dsimp [s', addClauseState]; simp [hlpl', hlen.tmp_len_arr]; omega)
      intro k hk1 _
      have hklt : k < len.toNat := by dsimp [s', addClauseState] at hk1; simp [hlpl'] at hk1; omega
      have heq := hlp_new k hklt
      rw [List.getElem?_eq_getElem (by rw [hlpl']; omega),
        List.getElem?_eq_getElem (by rw [hlen.tmp_len_arr]; omega)] at heq
      dsimp [s', addClauseState]; simp [Option.some.inj heq]) hm

theorem kissat_add_clause_wp (Γ : Env)
    (hWatch : ∀ a m Q X, corePlusAddWatchSpec a m Q X →
      Γ "kissat_add_watch" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, corePlusAddClauseSpec a m Q X → Func.wp Γ kissat_add_clause_body a m Q X := by
  rintro ⟨h, len, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlen_mv, hm, hQ⟩
  have hmv : c.mv < 2 ^ 28 := c.hmv; have hmc : c.max_c < 2 ^ 28 := c.hmax_c
  have hlc : c.lcap < 2 ^ 28 := c.hlcap
  have htmpl := hlen.tmp_len_arr; have hwhl := hlen.wh_len; have hclsl := hlen.cls_len
  have hwnl := hlen.wn_len; have hlpl := hlen.lpool_len; have hlll := hlen.lit_len_le
  have hncl := hlen.num_clauses_le
  cp_steps
  · simp only [show c.max_c ≤ s.num_clauses ∨ c.lcap - s.lit_len < len.toNat from
      Or.inl (by clear hm hQ; c0_bound), ite_true] at hQ; exact hQ
  · simp only [show c.max_c ≤ s.num_clauses ∨ c.lcap - s.lit_len < len.toNat from
      Or.inr (by clear hm hQ; c0_bound), ite_true] at hQ; exact hQ
  · have hok : ¬ (c.max_c ≤ s.num_clauses ∨ c.lcap - s.lit_len < len.toNat) := by
      clear hm hQ; c0_bound
    simp only [hok, ite_false] at hQ
    have hnc_lt : s.num_clauses < c.max_c := by omega
    have hrem : len.toNat ≤ c.lcap - s.lit_len := by omega
    have hcls_norm : (BitVec.setWidth 64 (BitVec.ofNat 32 s.num_clauses)).toNat =
        s.num_clauses := by rw [bv_c0_zext32_64, Kissat.bv32_ofNat_toNat (by omega)]
    have hret_bv : BitVec.setWidth 64 (BitVec.ofNat 32 s.num_clauses) =
        BitVec.ofNat 64 s.num_clauses :=
      BitVec.eq_of_toNat_eq (by rw [hcls_norm, Kissat.bv64_ofNat_toNat (by omega)])
    refine wp_loop_inv
      (fun (v : Tup Val [i32]) m_l => ∃ lpool_l : List (BitVec 32),
        v.1.toNat ≤ len.toNat ∧ lpool_l.length = c.lcap ∧
        (∀ k < s.lit_len, lpool_l[k]? = s.lpool[k]?) ∧
        (∀ k < v.1.toNat, lpool_l[s.lit_len + k]? = s.tmp[k]?) ∧
        (CorePlusMem c { s with
          lit_len := s.lit_len + len.toNat, num_clauses := s.num_clauses + 1
          lpool := lpool_l } ⋆ R) m_l)
      (fun v _ => len.toNat - v.1.toNat) ?_ ?_
    · intro J hJ; cp_steps
      have hll_add : (BitVec.ofNat 64 s.lit_len + BitVec.setWidth 64 len).toNat =
          s.lit_len + len.toNat := by clear hm hQ; simp only [bv_c0, Nat.reducePow]; omega
      have hnc_add : (BitVec.ofNat 64 s.num_clauses + 1).toNat = s.num_clauses + 1 := by
        clear hm hQ; simp only [bv_c0, Nat.reducePow]; omega
      rw [hll_add, hnc_add] at hm
      exact hJ (0#32, ()) m ⟨s.lpool, Nat.zero_le _, hlpl, fun _ _ => rfl,
        fun _ hk => by simp at hk, hm⟩
    · intro J ⟨iv, ⟨⟩⟩ m_l ⟨lpool_l, hile, hlpl_l, hlp_old, hlp_new, hm_l⟩ hJ
      dsimp only at hile hlp_new
      have hoff_eq : (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 s.lit_len)) +
          BitVec.setWidth 64 iv).toNat = s.lit_len + iv.toNat := by
        clear hm_l hQ; simp only [bv_c0, Nat.reducePow]; omega
      cp_steps
      · refine hJ (iv + 1#32, ()) _ (by clear hQ; c0_bound)
          ⟨lpool_l.set (s.lit_len + iv.toNat) (s.tmp[iv.toNat]'(by omega)),
            by clear hQ; c0_bound, by simp [hlpl_l],
            (fun k hk => by rw [List.getElem?_set_ne (by omega)]; exact hlp_old k hk), ?_, ?_⟩
        · intro k hk; have hiv1 : (iv + 1#32).toNat = iv.toNat + 1 := by clear hQ; c0_bound
          rw [hiv1] at hk; by_cases hki : k = iv.toNat
          · subst hki; rw [List.getElem?_set_self (by rw [hlpl_l]; omega),
              List.getElem?_eq_getElem (by rw [htmpl]; omega)]
          · rw [List.getElem?_set_ne (by omega)]; exact hlp_new k (by omega)
        · rw [hoff_eq] at hm; exact hm
      · have hiv : iv.toNat = len.toNat := by clear hQ; c0_bound
        have ht0 : 0 < s.tmp.length := by rw [htmpl]; clear hm hQ; c0_bound
        have ht1 : 1 < s.tmp.length := by rw [htmpl]; clear hm hQ; c0_bound
        cp_steps; rw [hiv] at hlp_new; simp only [bv64_setWidth32_ofNat, hcls_norm] at hm
        let cls1 := (((s.cls.set (4 * s.num_clauses) (BitVec.ofNat 32 s.lit_len)).set
          (4 * s.num_clauses + 1) len).set (4 * s.num_clauses + 2) 2#32).set
          (4 * s.num_clauses + 3) 0#32
        let s1 : CorePlusState := { s with
          lit_len := s.lit_len + len.toNat, num_clauses := s.num_clauses + 1,
          lpool := lpool_l, cls := cls1 }
        have hlen_l : s1.LengthsOk c := { hlen with
          cls_len := by simp [s1, cls1, hclsl], lpool_len := hlpl_l,
          lit_len_le := by dsimp [s1]; omega, num_clauses_le := by dsimp [s1]; omega }
        c0_call hWatch; refine ⟨c, s1, R, rfl, hlen_l, hm, fun wh1 wn1 m1 hwl1 hwnl1 hm1 => ?_⟩
        dsimp only [s1] at hm1; let s2 : CorePlusState := { s1 with wh := wh1, wn := wn1 }
        have ht1_1 : 1 < s2.tmp.length := ht1; cp_steps; c0_call hWatch
        refine ⟨c, s2, R, rfl, { hlen_l with wh_len := hwl1, wn_len := hwnl1 }, hm1,
          fun wh2 wn2 m2 hwl2 hwnl2 hm2 => by
            cp_steps; rw [bv64_setWidth32_ofNat, hret_bv]
            exact addClause_exit hlen hlen_mv hnc_lt hrem hlpl_l hwl2 hwnl2 hlp_old hlp_new hm2 hQ⟩
      · have hiv : iv.toNat = len.toNat := by clear hQ; c0_bound
        rw [hiv] at hlp_new; simp only [bv64_setWidth32_ofNat, hcls_norm] at hm
        rw [bv64_setWidth32_ofNat, hret_bv]
        exact addClause_exit hlen hlen_mv hnc_lt hrem hlpl_l hwhl hwnl hlp_old hlp_new hm hQ

/-! ## 4. `kissat_backtrack` -/

private structure BtPrefixInv (c : CorePlusCfg) (F0 : CNF Nat) (s : CorePlusState)
    (target_lvl te : Nat) (st : CorePlusState) : Prop where
  te_le : te ≤ s.trail_end
  agree : st = { s with vals := st.vals, lvl := st.lvl, rsns := st.rsns, heur := st.heur }
  len_ok : st.LengthsOk c
  vals_dom : ∀ l < 2 * c.mv, st.vals[l]?.getD 0#8 = 0#8 ∨
    st.vals[l]?.getD 0#8 = 1#8 ∨ st.vals[l]?.getD 0#8 = 0xFF#8
  vals_true : ∀ l < 2 * c.mv,
    st.vals[l]?.getD 0#8 = 1#8 ↔ ∃ i < te, (s.trl[i]?.getD 0#32).toNat = l
  vals_false : ∀ l < 2 * c.mv,
    st.vals[l]?.getD 0#8 = 0xFF#8 ↔ ∃ i < te, (s.trl[i]?.getD 0#32).toNat = l ^^^ 1
  lvl_eq : ∀ i < te,
    st.lvl[(s.trl[i]?.getD 0#32).toNat / 2]? = s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?
  rsns_eq : ∀ i < te,
    st.rsns[(s.trl[i]?.getD 0#32).toNat / 2]? = s.rsns[(s.trl[i]?.getD 0#32).toNat / 2]?
  popped_gt : ∀ i, te ≤ i → i < s.trail_end →
    target_lvl < (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat

private theorem btPrefixInv_step {c : CorePlusCfg} {F0 : CNF Nat} {s st : CorePlusState}
    {target_lvl te : Nat} (hcore : CorePlusCoreInv c F0 s)
    (hbt : BtPrefixInv c F0 s target_lvl te st) (hte : 0 < te)
    (hlvl_gt : target_lvl < (st.lvl[(s.trl[te - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    {heur' : HeurState} (hhok : heur'.LengthsOk c) :
    let lit := s.trl[te - 1]?.getD 0#32
    BtPrefixInv c F0 s target_lvl (te - 1)
      { st with
        vals := (st.vals.set lit.toNat 0#8).set (lit.toNat ^^^ 1) 0#8,
        lvl := st.lvl.set (lit.toNat / 2) 0#32,
        rsns := st.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32, heur := heur' } := by
  intro lit; have hte_le := hbt.te_le; have hlen := hbt.len_ok
  have hlt1 : lit.toNat < 2 * c.mv := hcore.trail_lits_lt (te - 1) (by omega)
  have hlt2 : lit.toNat ^^^ 1 < 2 * c.mv := Kissat.litNeg_lt_two_mul hlt1
  have hnovar : ∀ i < te - 1, (s.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := fun i hi hv =>
    by have := hcore.trail_vars_nodup i (te - 1) (by omega) (by omega) hv; omega
  have hvals_ne : ∀ i < te - 1, (s.trl[i]?.getD 0#32).toNat ≠ lit.toNat ∧
      (s.trl[i]?.getD 0#32).toNat ≠ lit.toNat ^^^ 1 ∧
      ((s.trl[i]?.getD 0#32).toNat ^^^ 1) ≠ lit.toNat ∧
      ((s.trl[i]?.getD 0#32).toNat ^^^ 1) ≠ lit.toNat ^^^ 1 := fun i hi => by
    have hnv := hnovar i hi; have hx := Kissat.litVar_litNeg (s.trl[i]?.getD 0#32).toNat
    have hy := Kissat.litVar_litNeg lit.toNat; unfold Kissat.litVar Kissat.litNeg at hx hy; omega
  let st' : CorePlusState := { st with
    vals := (st.vals.set lit.toNat 0#8).set (lit.toNat ^^^ 1) 0#8,
    lvl := st.lvl.set (lit.toNat / 2) 0#32, rsns := st.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32,
    heur := heur' }
  have hget_vals : ∀ l < 2 * c.mv, st'.vals[l]?.getD 0#8 =
      if l = lit.toNat ∨ l = lit.toNat ^^^ 1 then 0#8 else st.vals[l]?.getD 0#8 := fun l _ => by
    by_cases h2 : l = lit.toNat ^^^ 1
    · subst h2; dsimp [st']
      rw [List.getElem?_set_self (by rw [List.length_set, hlen.vals_len]; exact hlt2)]; simp
    · by_cases h1 : l = lit.toNat
      · subst h1; simp [st', h2, List.getElem?_set_ne (Ne.symm h2),
          List.getElem?_set_self (by rw [hlen.vals_len]; exact hlt1)]
      · simp [st', h1, h2, List.getElem?_set_ne (Ne.symm h2), List.getElem?_set_ne (Ne.symm h1)]
  refine ⟨by omega, congrArg (fun x : CorePlusState =>
      { x with vals := st'.vals, lvl := st'.lvl, rsns := st'.rsns, heur := heur' }) hbt.agree,
    { hlen with
      vals_len := by simp [hlen.vals_len], lvl_len := by simp [hlen.lvl_len],
      rsns_len := by simp [hlen.rsns_len], heur_ok := hhok }, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl; rw [hget_vals l hl]; split
    · exact Or.inl rfl
    · exact hbt.vals_dom l hl
  · intro l hl; rw [hget_vals l hl]; split
    · next heq => refine ⟨fun h => by simp at h, fun ⟨i, hi, hie⟩ => False.elim <| by
        rcases heq with rfl | rfl <;> first | exact (hvals_ne i hi).1 hie |
          exact (hvals_ne i hi).2.1 hie⟩
    · next hne =>
      rw [hbt.vals_true l hl]; refine ⟨fun ⟨i, hi, hie⟩ =>
        ⟨i, Nat.lt_of_not_ge fun h => hne (Or.inl ?_), hie⟩, fun ⟨i, hi, hie⟩ => ⟨i, by omega, hie⟩⟩
      rw [show i = te - 1 from by omega] at hie; exact hie.symm
  · intro l hl; rw [hget_vals l hl]; split
    · next heq => refine ⟨fun h => by simp at h, fun ⟨i, hi, hie⟩ => False.elim <| by
        have hx : ((s.trl[i]?.getD 0#32).toNat ^^^ 1) = l := by
          rw [hie]; exact Kissat.litNeg_litNeg l
        rcases heq with rfl | rfl <;>
          first | exact (hvals_ne i hi).2.2.1 hx | exact (hvals_ne i hi).2.2.2 hx⟩
    · next hne =>
      rw [hbt.vals_false l hl]; refine ⟨fun ⟨i, hi, hie⟩ =>
        ⟨i, Nat.lt_of_not_ge fun h => hne (Or.inr ?_), hie⟩, fun ⟨i, hi, hie⟩ => ⟨i, by omega, hie⟩⟩
      rw [show i = te - 1 from by omega] at hie
      exact (Kissat.litNeg_litNeg l).symm.trans (congrArg (· ^^^ 1) hie.symm)
  · intro i hi; dsimp [st']
    rw [List.getElem?_set_ne (hnovar i hi).symm]; exact hbt.lvl_eq i (by omega)
  · intro i hi; dsimp [st']; rw [List.getElem?_set_ne (hnovar i hi).symm]
    exact hbt.rsns_eq i (by omega)
  · intro i hi1 hi2; by_cases hie : i = te - 1
    · subst hie; have heq := hbt.lvl_eq (te - 1) (by omega); rwa [← congrArg (·.getD 0#32) heq]
    · exact hbt.popped_gt i (by omega) hi2

private theorem backtrack_exit {c : CorePlusCfg} {F0 : CNF Nat} {s st : CorePlusState}
    {target_lvl : BitVec 64} {te prop' : Nat} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []}
    (hinv : CorePlusInv c F0 s) (hbt : BtPrefixInv c F0 s target_lvl.toNat te st)
    (htl_cur : target_lvl.toNat ≤ s.cur_level)
    (hexit : te = 0 ∨
      (st.lvl[(s.trl[te - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat)
    (hprop : prop' = min s.propagated te)
    (hm : (CorePlusMem c
      { st with trail_end := te, propagated := prop', cur_level := target_lvl.toNat } ⋆ R) m)
    (hQ : ∀ vals' lvl' rsns' te' prop' heur' m',
      let s' : CorePlusState := { s with
        vals := vals', lvl := lvl', rsns := rsns', trail_end := te'
        propagated := prop', cur_level := target_lvl.toNat, heur := heur' }
      CorePlusInv c F0 s' → te' ≤ s.trail_end → (∀ i < s.trail_end,
        (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat → i < te') →
      (CorePlusMem c s' ⋆ R) m' → Q () m') : Q () m := by
  subst hprop; have hcore := hinv.core; have hlen := hbt.len_ok; have hte_le := hbt.te_le
  let s' : CorePlusState := { s with
    vals := st.vals, lvl := st.lvl, rsns := st.rsns, trail_end := te
    propagated := min s.propagated te, cur_level := target_lvl.toNat, heur := st.heur }
  have hkeep : ∀ i < s.trail_end,
      (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat → i < te :=
    fun i hi _ => Nat.lt_of_not_ge fun hge => by have := hbt.popped_gt i hge hi; omega
  have hlvl_s' : ∀ i < te, s'.lvl[(s'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 =
      s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 :=
    fun i hi => congrArg (·.getD 0#32) (hbt.lvl_eq i hi)
  have hrsns_s' : ∀ i < te, s'.rsns[(s'.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
      s.rsns[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 :=
    fun i hi => congrArg (·.getD 0xFFFFFFFF#32) (hbt.rsns_eq i hi)
  have hinhab : ∀ L, 1 ≤ L → L ≤ target_lvl.toNat →
      ∃ i < te, (s'.lvl[(s'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L := fun L h1 h2 =>
    let ⟨i, hi, hie⟩ := hcore.levels_inhabited L h1 (Nat.le_trans h2 htl_cur)
    have hi' := hkeep i hi (by omega); ⟨i, hi', by rw [hlvl_s' i hi']; exact hie⟩
  have hinv' : CorePlusInv c F0 s' := ⟨⟨{ hcore.lengths with
      vals_len := hlen.vals_len, lvl_len := hlen.lvl_len, rsns_len := hlen.rsns_len,
      trail_end_le := Nat.le_trans hte_le hcore.lengths.trail_end_le,
      propagated_le := Nat.min_le_right _ _, heur_ok := hlen.heur_ok,
      cur_level_lt := Nat.lt_of_le_of_lt htl_cur hcore.lengths.cur_level_lt },
    ⟨hcore.clauses.bounds, hcore.clauses.disjoint, hcore.clauses.lits_lt, hcore.clauses.entails⟩,
    Kissat.le_of_surj_range1
      (fun i => (s'.lvl[(s'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) hinhab,
    (fun i hi => hcore.trail_lits_lt i (Nat.lt_of_lt_of_le hi hte_le)),
    (fun i j hi hj => hcore.trail_vars_nodup i j
      (Nat.lt_of_lt_of_le hi hte_le) (Nat.lt_of_lt_of_le hj hte_le)),
    hbt.vals_dom, hbt.vals_true, hbt.vals_false,
    (fun i hi => by
      dsimp only [s'] at hi ⊢; rw [hlvl_s' i hi]; rcases hexit with rfl | _
      · cases hi
      · have h0 := Nat.sub_lt (Nat.zero_lt_of_lt hi) Nat.zero_lt_one
        have hm := hcore.trail_mono i (te - 1) (Nat.le_sub_one_of_lt hi)
          (Nat.lt_of_lt_of_le h0 hte_le)
        rw [← congrArg (·.getD 0#32) (hbt.lvl_eq (te - 1) h0)] at hm; exact by omega),
    (fun i j hij hj => by dsimp only [s'] at hj ⊢
                          rw [hlvl_s' i (Nat.lt_of_le_of_lt hij hj), hlvl_s' j hj]
                          exact hcore.trail_mono i j hij (Nat.lt_of_lt_of_le hj hte_le)),
    hinhab, (fun i hi hl0 => by dsimp only [s'] at hi hl0; rw [hlvl_s' i hi] at hl0
                                exact hcore.level0_sound i (Nat.lt_of_lt_of_le hi hte_le) hl0),
    (fun idx hidx hne => by dsimp only [s'] at hidx; rw [hrsns_s' idx hidx] at hne ⊢
                            exact hcore.reason_inv idx (Nat.lt_of_lt_of_le hidx hte_le) hne)⟩,
    hinv.marks⟩
  rw [show { st with
      trail_end := te, propagated := min s.propagated te,
      cur_level := target_lvl.toNat } = s' from by rw [hbt.agree]] at hm
  exact hQ st.vals st.lvl st.rsns te (min s.propagated te) st.heur m hinv' hbt.te_le hkeep hm

private theorem bt_exit_le {c : CorePlusCfg} {F0 : CNF Nat} {s st : CorePlusState}
    {target_lvl : BitVec 64} {te : Nat} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []}
    (hinv : CorePlusInv c F0 s) (hbt : BtPrefixInv c F0 s target_lvl.toNat te st)
    (htl_cur : target_lvl.toNat ≤ s.cur_level)
    (hexit : te = 0 ∨
      (st.lvl[(s.trl[te - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat)
    (hle : st.propagated ≤ te)
    (hm : (CorePlusMem c { st with trail_end := te, cur_level := target_lvl.toNat } ⋆ R) m)
    (hQ : ∀ vals' lvl' rsns' te' prop' heur' m',
      let s' : CorePlusState := { s with
        vals := vals', lvl := lvl', rsns := rsns', trail_end := te'
        propagated := prop', cur_level := target_lvl.toNat, heur := heur' }
      CorePlusInv c F0 s' → te' ≤ s.trail_end → (∀ i < s.trail_end,
        (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat → i < te') →
      (CorePlusMem c s' ⋆ R) m' → Q () m') : Q () m := by
  have hp : st.propagated = s.propagated := by rw [hbt.agree]
  rw [hp] at hm hle; exact backtrack_exit hinv hbt htl_cur hexit (Nat.min_eq_left hle).symm hm hQ

private theorem bt_lvl_at {c : CorePlusCfg} {F0 : CNF Nat} {s st : CorePlusState}
    (hcore : CorePlusCoreInv c F0 s) (hlvl_len : st.lvl.length = c.mv)
    (htrl_s : st.trl = s.trl) {i : Nat} (hi : i < s.trail_end) (hlt_s : i < st.trl.length) :
    ∃ hlt_v : (st.trl[i]'hlt_s).toNat / 2 < st.lvl.length,
      (st.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
        (st.lvl[(st.trl[i]'hlt_s).toNat / 2]'hlt_v).toNat := by
  have _ := hcore.trail_lits_lt i hi
  have hg : s.trl[i]?.getD 0#32 = st.trl[i]'hlt_s := by
    rw [List.getElem?_eq_getElem (by rwa [← htrl_s]), Option.getD_some]; simp only [htrl_s]
  have hv : (st.trl[i]'hlt_s).toNat / 2 < st.lvl.length := by rw [hlvl_len, ← hg]; omega
  exact ⟨hv, by rw [hg, List.getElem?_eq_getElem hv, Option.getD_some]⟩

theorem kissat_backtrack_wp (Γ : Env)
    (hHeapPush : ∀ a m Q X, corePlusHeapPushSpec a m Q X →
      Γ "kissat_heap_push" [i64, i32] [] a m Q X) :
    ∀ a m Q X, corePlusBacktrackSpec a m Q X → Func.wp Γ kissat_backtrack_body a m Q X := by
  rintro ⟨h, target_lvl, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, htl_cur, hm, hQ⟩
  have hcore := hinv.core; have hlen := hcore.lengths; have hmv : c.mv < 2 ^ 28 := c.hmv
  cp_steps
  refine wp_loop_inv
    (fun (te_v : Tup Val [i64]) ml => ∃ st,
      BtPrefixInv c F0 s target_lvl.toNat te_v.1.toNat st ∧ (CorePlusMem c st ⋆ R) ml)
    (fun te_v _ => te_v.1.toNat) ?_ ?_
  · intro L hL; cp_steps; refine hL (BitVec.ofNat 64 s.trail_end, ()) m ⟨s, ?_, hm⟩
    rw [Kissat.bv64_ofNat_toNat (by have := hlen.trail_end_le; omega)]
    exact ⟨Nat.le_refl _, rfl, hlen, hcore.vals_domain, hcore.vals_true_iff, hcore.vals_false_iff,
      fun _ _ => rfl, fun _ _ => rfl, fun _ h1 h2 => by omega⟩
  · intro L ⟨te_v, ⟨⟩⟩ ml ⟨st, hbt, hml⟩ hL
    have hte_le : te_v.toNat ≤ s.trail_end := hbt.te_le
    have hst_len := hbt.len_ok
    have hte_mv : te_v.toNat ≤ c.mv := Nat.le_trans hte_le hlen.trail_end_le
    have htrl_s : st.trl = s.trl := by rw [hbt.agree]
    have hs_pr : st.propagated = s.propagated := by rw [hbt.agree]
    have hte64 : te_v.toNat < 2 ^ 64 := by omega
    have hpr64 : st.propagated < 2 ^ 64 := by
      have := hst_len.propagated_le; have := hst_len.trail_end_le; omega
    cp_steps
    · have hp : 0 < te_v.toNat := hc
      have hsub : (te_v - 1#64).toNat = te_v.toNat - 1 :=
        bv64_sub1_toNat fun h0 => by have := congrArg BitVec.toNat h0; simp at this; omega
      have ht_lt : (te_v - 1#64).toNat < st.trl.length := by
        rw [htrl_s, hlen.trl_len, hsub]; omega
      have hlit_get : st.trl[(te_v - 1#64).toNat]'ht_lt = s.trl[te_v.toNat - 1]?.getD 0#32 := by
        rw [List.getElem?_eq_getElem (by rw [hlen.trl_len]; omega), Option.getD_some]
        simp only [htrl_s, hsub]
      have hlit_lt_nat : (st.trl[(te_v - 1#64).toNat]'ht_lt).toNat < 2 * c.mv := by
        rw [hlit_get]; exact hcore.trail_lits_lt (te_v.toNat - 1) (by omega)
      have ⟨hv_lt, hlvl_eq⟩ := bt_lvl_at hcore hst_len.lvl_len htrl_s (by omega) ht_lt
      have h1 : (BitVec.setWidth 64 (st.trl[(te_v - 1#64).toNat]'ht_lt)).toNat <
          st.vals.length := by rw [hst_len.vals_len, bv_c0_zext32_64]; exact hlit_lt_nat
      have h2 : (BitVec.setWidth 64 (st.trl[(te_v - 1#64).toNat]'ht_lt ^^^ 1#32)).toNat <
          st.vals.length := by
        rw [hst_len.vals_len, bv_c0_zext32_64, BitVec.toNat_xor,
          show (1#32 : BitVec 32).toNat = 1 from rfl]; exact Kissat.litNeg_lt_two_mul hlit_lt_nat
      have h3 : (BitVec.setWidth 64 (st.trl[(te_v - 1#64).toNat]'ht_lt >>> 1)).toNat <
          st.lvl.length := by rw [hst_len.lvl_len, bv_c0_zext32_64, Kissat.bv32_lshr_1]; omega
      have h4 : (BitVec.setWidth 64 (st.trl[(te_v - 1#64).toNat]'ht_lt >>> 1)).toNat <
          st.rsns.length := by rw [hst_len.rsns_len, ← hst_len.lvl_len]; exact h3
      cp_steps
      · have hle : (st.lvl[(s.trl[te_v.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
            target_lvl.toNat := by
          rw [← hsub, hlvl_eq]; clear hm hQ; simp only [bv_c0, Nat.reducePow] at *; omega
        exact backtrack_exit hinv hbt htl_cur (Or.inr hle)
          (Nat.min_eq_right (by dsimp only; rw [← hs_pr]; clear hm hQ; c0_bound)).symm hm hQ
      · have hle : (st.lvl[(s.trl[te_v.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
            target_lvl.toNat := by
          rw [← hsub, hlvl_eq]; clear hm hQ; simp only [bv_c0, Nat.reducePow] at *; omega
        exact bt_exit_le hinv hbt htl_cur (Or.inr hle) (by dsimp only; clear hm hQ; c0_bound) hm hQ
      · have hgt : target_lvl.toNat <
            (st.lvl[(s.trl[te_v.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
          rw [← hsub, hlvl_eq]; clear hm hQ; c0_bound
        let lit := s.trl[te_v.toNat - 1]?.getD 0#32
        let st1 : CorePlusState := { st with
          vals := (st.vals.set lit.toNat 0#8).set (lit.toNat ^^^ 1) 0#8,
          lvl := st.lvl.set (lit.toNat / 2) 0#32,
          rsns := st.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32 }
        have hbt1 := btPrefixInv_step hcore hbt hp hgt hst_len.heur_ok
        have hlit_get' : ∀ h : (te_v - 1).toNat < st.trl.length,
            st.trl[(te_v - 1).toNat]'h = lit := fun _ => hlit_get
        simp only [hlit_get'] at hm; c0_call hHeapPush
        refine ⟨c, st1, R, rfl, hbt1.len_ok, hm, fun heur' m' hhok' hm' => ?_⟩
        cp_steps; exact hL (te_v - 1#64, ()) m' (by dsimp only; rw [hsub]; omega)
          ⟨{ st1 with heur := heur' },
            by dsimp only; rw [hsub]; exact btPrefixInv_step hcore hbt hp hgt hhok', hm'⟩
    · exact backtrack_exit hinv hbt htl_cur (Or.inl (by clear hQ hm; dsimp only; omega))
        (Nat.min_eq_right (by dsimp only; rw [← hs_pr]; clear hm hQ; c0_bound)).symm hm hQ
    · exact bt_exit_le hinv hbt htl_cur (Or.inl (by clear hQ hm; dsimp only; omega))
        (by dsimp only; clear hm hQ; c0_bound) hm hQ

/-! ## 5. `kissat_zero_tables` -/

private theorem list_eq_replicate_of_forall {α : Type} {xs : List α} {n : Nat} {x : α}
    (hlen : xs.length = n) (hall : ∀ i < n, xs[i]? = some x) : xs = List.replicate n x := by
  apply List.ext_getElem (by simp [hlen]); intro i hi _
  have h1 := hall i (by omega); rw [List.getElem?_eq_getElem (by omega)] at h1; simpa using h1

private theorem zero_tables_loop2_step {c : CorePlusCfg} {s1 st : CorePlusState} {v : Nat}
    (v32 : BitVec 32) (hv : v < c.mv) (hlok : st.LengthsOk c)
    (hag : st = { s1 with
      mrk := st.mrk, lvl := st.lvl, rsns := st.rsns, tmp := st.tmp
      min_clr := st.min_clr, heur := st.heur })
    (hall : ∀ j < v, st.mrk[j]? = some 0#8 ∧ st.lvl[j]? = some 0#32 ∧
      st.rsns[j]? = some 0xFFFFFFFF#32 ∧ st.tmp[j]? = some 0#32 ∧ st.min_clr[j]? = some 0#32) :
    let heur' : HeurState := { st.heur with
      phases := st.heur.phases.set v 1#8, heap := st.heur.heap.set v v32
      pos := st.heur.pos.set v v32, score := st.heur.score.set v 0#64 }
    let st' : CorePlusState := { st with
      mrk := st.mrk.set v 0#8, lvl := st.lvl.set v 0#32
      rsns := st.rsns.set v 0xFFFFFFFF#32, tmp := st.tmp.set v 0#32
      min_clr := st.min_clr.set v 0#32, heur := heur' }
    v + 1 ≤ c.mv ∧ st' = { s1 with
      mrk := st'.mrk, lvl := st'.lvl, rsns := st'.rsns
      tmp := st'.tmp, min_clr := st'.min_clr, heur := heur' } ∧
    st'.LengthsOk c ∧ heur'.rel_trigger = st.heur.rel_trigger ∧
    ∀ j < v + 1, st'.mrk[j]? = some 0#8 ∧ st'.lvl[j]? = some 0#32 ∧
      st'.rsns[j]? = some 0xFFFFFFFF#32 ∧ st'.tmp[j]? = some 0#32 ∧
      st'.min_clr[j]? = some 0#32 := by
  intro heur' st'; have hhok := hlok.heur_ok
  have hhok' : heur'.LengthsOk c := ⟨by simpa [heur'] using hhok.heap_len_arr,
    by simpa [heur'] using hhok.pos_len, by simpa [heur'] using hhok.score_len,
    by simpa [heur'] using hhok.phases_len, hhok.heap_len_le⟩
  refine ⟨by omega, congrArg (fun x => { x with
      mrk := st'.mrk, lvl := st'.lvl, rsns := st'.rsns
      tmp := st'.tmp, min_clr := st'.min_clr, heur := heur' }) hag,
    { hlok with
      mrk_len := by simpa [st'] using hlok.mrk_len, lvl_len := by simpa [st'] using hlok.lvl_len,
      rsns_len := by simpa [st'] using hlok.rsns_len,
      tmp_len_arr := by simpa [st'] using hlok.tmp_len_arr,
      min_clr_len_arr := by simpa [st'] using hlok.min_clr_len_arr, heur_ok := hhok' },
    rfl, fun j hj => ?_⟩
  by_cases hje : j = v
  · subst hje; exact ⟨List.getElem?_set_self (by rw [hlok.mrk_len]; exact hv),
      List.getElem?_set_self (by rw [hlok.lvl_len]; exact hv),
      List.getElem?_set_self (by rw [hlok.rsns_len]; exact hv),
      List.getElem?_set_self (by rw [hlok.tmp_len_arr]; exact hv),
      List.getElem?_set_self (by rw [hlok.min_clr_len_arr]; exact hv)⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hall j (by omega)
    simp only [st', List.getElem?_set_ne (Ne.symm hje)]; exact ⟨h1, h2, h3, h4, h5⟩

theorem kissat_zero_tables_wp (Γ : Env) :
    ∀ a m Q X, corePlusZeroTablesSpec a m Q X → Func.wp Γ kissat_zero_tables_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hmv : c.mv < 2 ^ 28 := c.hmv; have hmd : c.minDepth ≤ 1000 := minDepthOf_le c.mv
  cp_steps
  refine wp_loop_inv
    (fun (i_v : Tup Val [i64]) ml => ∃ st, i_v.1.toNat ≤ 2 * c.mv ∧
      st = { s with vals := st.vals, wh := st.wh } ∧ st.vals.length = 2 * c.mv ∧
      st.wh.length = 2 * c.mv ∧
      (∀ k < i_v.1.toNat, st.vals[k]? = some 0#8 ∧ st.wh[k]? = some 0xFFFFFFFF#32) ∧
      (CorePlusMem c st ⋆ R) ml) (fun i_v _ => 2 * c.mv - i_v.1.toNat) ?_ ?_
  · intro L1 hL1; cp_steps; exact hL1 (0#64, ()) m
      ⟨s, Nat.zero_le _, rfl, hlen.vals_len, hlen.wh_len, (fun _ h => by cases h), hm⟩
  · intro L1 ⟨i_v, ⟨⟩⟩ ml ⟨st1, hi_le, hag1, hvl1, hwl1, hall1, hml1⟩ hL1
    dsimp only at hi_le hall1
    have hmvl1 : (BitVec.ofNat 64 c.mv <<< 1).toNat = 2 * c.mv := by
      simp only [bv_c0, Nat.reducePow]; omega
    cp_steps
    · have hilt : i_v.toNat < 2 * c.mv := by clear hm hQ; c0_bound
      have hi1 : (i_v + 1#64).toNat = i_v.toNat + 1 := by clear hm hQ; simp only [bv_c0]; omega
      refine hL1 (i_v + 1#64, ()) _ (by dsimp only; rw [hi1]; omega)
        ⟨_, by dsimp only; rw [hi1]; omega, congrArg (fun x =>
          { x with vals := st1.vals.set i_v.toNat 0#8, wh := st1.wh.set i_v.toNat 0xFFFFFFFF#32 })
          hag1, by simp [hvl1], by simp [hwl1], fun k hk => ?_, hm⟩
      dsimp only at hk; by_cases hke : k = i_v.toNat
      · subst hke; exact ⟨List.getElem?_set_self (by rw [hvl1]; exact hilt),
          List.getElem?_set_self (by rw [hwl1]; exact hilt)⟩
      · rw [hi1] at hk; have := hall1 k (by clear hm hQ; omega)
        simp only [List.getElem?_set_ne (Ne.symm hke)]; exact this
    · have hieq : i_v.toNat = 2 * c.mv := by clear hml1 hQ; c0_bound
      rw [hieq] at hall1
      let s1 : CorePlusState := { s with
        vals := List.replicate (2 * c.mv) 0#8, wh := List.replicate (2 * c.mv) 0xFFFFFFFF#32 }
      have hs1_eq : st1 = s1 := by rw [hag1, list_eq_replicate_of_forall hvl1
        (fun k hk => (hall1 k hk).1), list_eq_replicate_of_forall hwl1 (fun k hk => (hall1 k hk).2)]
      have hlen1 : s1.LengthsOk c := { hlen with vals_len := by simp [s1], wh_len := by simp [s1] }
      rw [hs1_eq] at hml1
      refine wp_loop_inv (fun (v_v : Tup Val [i64]) ml2 => ∃ st2, v_v.1.toNat ≤ c.mv ∧
          st2 = { s1 with
            mrk := st2.mrk, lvl := st2.lvl, rsns := st2.rsns, tmp := st2.tmp,
            min_clr := st2.min_clr, heur := st2.heur } ∧
          st2.LengthsOk c ∧ st2.heur.rel_trigger = s.heur.rel_trigger ∧
          (∀ j < v_v.1.toNat, st2.mrk[j]? = some 0#8 ∧ st2.lvl[j]? = some 0#32 ∧
            st2.rsns[j]? = some 0xFFFFFFFF#32 ∧ st2.tmp[j]? = some 0#32 ∧
            st2.min_clr[j]? = some 0#32) ∧ (CorePlusMem c st2 ⋆ R) ml2)
        (fun v_v _ => c.mv - v_v.1.toNat) ?_ ?_
      · intro L2 hL2; cp_steps
        exact hL2 (0#64, ()) _ ⟨s1, Nat.zero_le _, rfl, hlen1, rfl, (fun _ h => by cases h), hml1⟩
      · intro L2 ⟨v_v, ⟨⟩⟩ ml2 ⟨st2, hv_le, hag2, hlen2, hrt2, hall2, hml2⟩ hL2
        dsimp only at hv_le hall2
        have ⟨_, h1, h2, h3, _, h4, _, _, _, _, _, h5, _, _, _, _, _, _, _, _, h6, h7, h8, h9, _⟩ :=
          hlen2
        cp_steps
        · have hvlt : v_v.toNat < c.mv := by clear hm hQ; c0_bound
          have hv1 : (v_v + 1#64).toNat = v_v.toNat + 1 := by clear hm hQ; simp only [bv_c0]; omega
          obtain ⟨hv1_le, hag2', hlen2', hrt2', hall2'⟩ :=
            zero_tables_loop2_step (BitVec.setWidth 32 v_v) hvlt hlen2 hag2 hall2
          exact hL2 (v_v + 1#64, ()) _ (by dsimp only; rw [hv1]; omega)
            ⟨_, by dsimp only; rw [hv1]; exact hv1_le, hag2', hlen2', hrt2'.trans hrt2,
              fun j hj => hall2' j (by dsimp only at hj; rw [hv1] at hj; exact hj), hm⟩
        · have hveq : v_v.toNat = c.mv := by clear hml2 hQ; c0_bound
          rw [hveq] at hall2
          let s2 : CorePlusState := { s1 with
            mrk := List.replicate c.mv 0#8, lvl := List.replicate c.mv 0#32,
            rsns := List.replicate c.mv 0xFFFFFFFF#32, tmp := List.replicate c.mv 0#32,
            min_clr := List.replicate c.mv 0#32, heur := st2.heur }
          have hs2_eq : st2 = s2 := by rw [hag2, list_eq_replicate_of_forall h1
            (fun j hj => (hall2 j hj).1), list_eq_replicate_of_forall h2
            (fun j hj => (hall2 j hj).2.1), list_eq_replicate_of_forall h3
            (fun j hj => (hall2 j hj).2.2.1), list_eq_replicate_of_forall h4
            (fun j hj => (hall2 j hj).2.2.2.1), list_eq_replicate_of_forall h5
            (fun j hj => (hall2 j hj).2.2.2.2)]
          rw [hs2_eq] at hml2
          refine wp_loop_inv (fun (k_v : Tup Val [i64]) ml3 => ∃ st3, k_v.1.toNat ≤ 2 * c.minDepth ∧
            st3 = { s2 with min_stk := st3.min_stk } ∧ st3.min_stk.length = 2 * c.minDepth ∧
            (CorePlusMem c st3 ⋆ R) ml3) (fun k_v _ => 2 * c.minDepth - k_v.1.toNat) ?_ ?_
          · intro L3 hL3; cp_steps
            exact hL3 (0#64, ()) _
              ⟨s2, Nat.zero_le _, rfl, by rw [← hs2_eq]; exact hlen2.min_stk_len, hml2⟩
          · intro L3 ⟨k_v, ⟨⟩⟩ ml3 ⟨st3, hk_le, hag3, hmsl3, hml3⟩ hL3
            dsimp only at hk_le
            have hmdl : (BitVec.ofNat 64 c.minDepth <<< 1).toNat = 2 * c.minDepth := by
              simp only [bv_c0, Nat.reducePow]; omega
            cp_steps
            · have hk1 : (k_v + 1#64).toNat = k_v.toNat + 1 := by
                clear hm hQ; simp only [bv_c0]; omega
              exact hL3 (k_v + 1#64, ()) _ (by dsimp only; rw [hk1]; omega)
                ⟨_, by dsimp only; rw [hk1]; omega, congrArg (fun x =>
                  { x with min_stk := st3.min_stk.set k_v.toNat 0#32 }) hag3, by simp [hmsl3], hm⟩
            · rw [hag3] at hml3; exact hQ st3.min_stk st2.heur ml3 hmsl3 hlen2.heur_ok hrt2 hml3

/-! ## 6. `kissat_init_state` -/

private theorem cp_align8 {n : Nat} (hn : n + 7 < 2 ^ 64) :
    (BitVec.ofNat 64 n + (7 : BitVec 64)) &&& (~~~(7 : BitVec 64)) =
      BitVec.ofNat 64 (((n + 7) / 8) * 8) := by
  apply BitVec.eq_of_toNat_eq; rw [show (7 : BitVec 64) = BitVec.ofNat 64 7 from rfl, bv_add_ofNat]
  simp only [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show ((n + 7) / 8) * 8 < 2 ^ 64 by omega),
    show (2 ^ 64 - 1 - 7 % 2 ^ 64) = 2 ^ 64 - 8 from by decide]
  have hd := Nat.and_div_two_pow (a := n + 7) (b := 2 ^ 64 - 8) (n := 3)
  have hr := Nat.and_mod_two_pow (a := n + 7) (b := 2 ^ 64 - 8) (n := 3)
  rw [show (2 ^ 64 - 8) / 2 ^ 3 = 2 ^ 61 - 1 from by decide] at hd
  rw [show (2 ^ 64 - 8) % 2 ^ 3 = 0 from by decide, Nat.and_zero] at hr
  have hq := Nat.and_two_pow_sub_one_eq_mod ((n + 7) / 8) 61; rw [Nat.mod_eq_of_lt (by omega)] at hq
  rw [show (2 ^ 3 : Nat) = 8 from by decide] at hd hr; rw [hq] at hd; omega

private theorem cp_mul24 (n : Nat) :
    BitVec.ofNat 64 n * (24 : BitVec 64) = BitVec.ofNat 64 (n * 24) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_mod]

private def cpInitMaxC (nc rem : Nat) : Nat := min (nc + (rem - nc * 24) / 64) (dimacsBound - 1)
private def cpInitLcap (nc rem : Nat) : Nat :=
  min ((rem - cpInitMaxC nc rem * 24) / 4) (dimacsBound - 1)
private theorem cpInitMaxC_lt {nc rem : Nat} : cpInitMaxC nc rem < dimacsBound := by
  unfold cpInitMaxC dimacsBound; omega
private theorem cpInitLcap_lt {nc rem : Nat} : cpInitLcap nc rem < dimacsBound := by
  unfold cpInitLcap dimacsBound; omega
private theorem cp_init_arena_fits {mv nc avail : Nat} (h : cpFixedBytes mv + nc * 24 ≤ avail) :
    let rem := avail - cpFixedBytes mv
    cpFixedBytes mv + 24 * cpInitMaxC nc rem + 4 * cpInitLcap nc rem ≤ avail := by
  intro rem; have h1 : cpInitMaxC nc rem * 24 ≤ rem := by unfold cpInitMaxC; omega
  have h2 : 4 * cpInitLcap nc rem ≤ rem - cpInitMaxC nc rem * 24 := by unfold cpInitLcap; omega
  omega
private theorem reg_peel {a b : BitVec 64} {n1 n2 n : Nat} {m : Mem 64} (hm : region a n m)
    (hb : a + BitVec.ofNat 64 n1 = b := by rfl) (hn : n = n1 + n2 := by omega)
    (hle : n1 + n2 ≤ 2 ^ 64 := by omega) : (region a n1 ⋆ region b n2) m := by
  subst hb hn; rwa [← region_merge_eq (a := a) (n1 := n1) (n2 := n2) (n := n1 + n2) rfl hle] at hm
private theorem reg_pad_i8 {a : BitVec 64} (k : Nat) {n : Nat} {m : Mem 64} (hm : region a n m)
    (hk : k ≤ n := by omega) (hle : n ≤ 2 ^ 64 := by omega) : ∃ xs : List (BitVec 8),
      xs.length = k ∧ (array (t := i8) a xs ⋆ region (a + BitVec.ofNat 64 k) (n - k)) m := by
  obtain ⟨m1, m2, hu, hd, h1, h2⟩ := reg_peel (n1 := k) (n2 := n - k) hm
  obtain ⟨xs, h, ha⟩ := region_to_array_i8 k (by omega) h1; exact ⟨xs, h, m1, m2, hu, hd, ha, h2⟩
private theorem reg_pad_i32 {a : BitVec 64} (k : Nat) {n : Nat} {m : Mem 64} (hm : region a n m)
    (hk : 4 * k ≤ n := by omega) (hle : n ≤ 2 ^ 64 := by omega) :
    ∃ xs : List (BitVec 32), xs.length = k ∧
      (array (t := i32) a xs ⋆ region (a + BitVec.ofNat 64 (4 * k)) (n - 4 * k)) m := by
  obtain ⟨m1, m2, hu, hd, h1, h2⟩ := reg_peel (n1 := 4 * k) (n2 := n - 4 * k) hm
  obtain ⟨xs, h, ha⟩ := region_to_array_i32 k (by omega) h1; exact ⟨xs, h, m1, m2, hu, hd, ha, h2⟩

private theorem sep_push {P Q : Mem 64 → Prop} {m1 m2 m : Mem 64} (hu : m1.union m2 = m)
    (hd : m1.inter m2 = ∅) (hp : P m1) (hq : Q m2) : (P ⋆ Q) m := ⟨m1, m2, hu, hd, hp, hq⟩
private theorem sep_seed3 {A1 P1 A2 P2 A3 P3 R : Mem 64 → Prop} {m : Mem 64}
    (h : ((A1 ⋆ P1) ⋆ ((A2 ⋆ P2) ⋆ ((A3 ⋆ P3) ⋆ R))) m) :
    ((((A1 ⋆ A2) ⋆ A3) ⋆ ((P1 ⋆ P2) ⋆ P3)) ⋆ R) m := sep_ac h
private theorem sep_add_c_pad {C H Q arr pad R : Mem 64 → Prop} {m : Mem 64}
    (h : (((C ⋆ H) ⋆ Q) ⋆ ((arr ⋆ pad) ⋆ R)) m) : ((((C ⋆ arr) ⋆ H) ⋆ (Q ⋆ pad)) ⋆ R) m := sep_ac h
private theorem sep_add_h_pad {C H Q arr pad R : Mem 64 → Prop} {m : Mem 64}
    (h : (((C ⋆ H) ⋆ Q) ⋆ ((arr ⋆ pad) ⋆ R)) m) : (((C ⋆ (H ⋆ arr)) ⋆ (Q ⋆ pad)) ⋆ R) m := sep_ac h
private theorem sep_finish_arrs {C H Q SC WH WPad MS CL WN LP SL : Mem 64 → Prop} {m : Mem 64}
    (h : ((((C ⋆ H) ⋆ Q) ⋆ (SC ⋆ (WH ⋆ WPad) ⋆ MS)) ⋆ ((CL ⋆ WN) ⋆ (LP ⋆ SL))) m) :
    (((C ⋆ WH ⋆ MS ⋆ CL ⋆ WN ⋆ LP) ⋆ (H ⋆ SC)) ⋆ ((Q ⋆ WPad) ⋆ SL)) m := sep_ac h
private theorem sep_peel2 {CHQ SC WH WP MS R : Mem 64 → Prop} {m : Mem 64}
    (h : (CHQ ⋆ (SC ⋆ ((WH ⋆ WP) ⋆ (MS ⋆ R)))) m) : ((CHQ ⋆ ((SC ⋆ (WH ⋆ WP)) ⋆ MS)) ⋆ R) m :=
  sep_ac h
private theorem reorder_c12 {v mk lv rs tr tp mc w ms cl wn lp : Mem 64 → Prop} {m : Mem 64}
    (h : (((((((((((v ⋆ mk) ⋆ lv) ⋆ rs) ⋆ tr) ⋆ tp) ⋆ mc) ⋆ w) ⋆ ms) ⋆ cl) ⋆ wn) ⋆ lp) m) :
    (v ⋆ mk ⋆ lv ⋆ rs ⋆ tr ⋆ tp ⋆ w ⋆ cl ⋆ wn ⋆ lp ⋆ ms ⋆ mc) m := sep_ac h
private theorem reorder_h4 {ph hp pos sc : Mem 64 → Prop} {m : Mem 64}
    (h : (((ph ⋆ hp) ⋆ pos) ⋆ sc) m) : (hp ⋆ pos ⋆ sc ⋆ ph) m := sep_ac h

private abbrev cpPadRegs (c : CorePlusCfg) : Mem 64 → Prop :=
  region (c.pVals + BitVec.ofNat 64 (2 * c.mv)) (valsBytes c.mv - 2 * c.mv) ⋆
  region (c.pMark + BitVec.ofNat 64 c.mv) (markBytes c.mv - c.mv) ⋆
  region (c.pPhases + BitVec.ofNat 64 c.mv) (markBytes c.mv - c.mv) ⋆
  region (c.pLevel + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pReason + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pTrail + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pTmp + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pHeap + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pPos + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pMinClr + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv)

private theorem peel_c_i32 {C H Q : Mem 64 → Prop} {a : BitVec 64} (b : BitVec 64) (k n1 n2 : Nat)
    {n : Nat} {m : Mem 64} (hm : (((C ⋆ H) ⋆ Q) ⋆ region a n) m)
    (hb : a + BitVec.ofNat 64 n1 = b := by rfl) (hn : n = n1 + n2 := by omega)
    (hk : 4 * k ≤ n1 := by omega) (hle : n1 + n2 ≤ 2 ^ 64 := by omega) :
    ∃ xs : List (BitVec 32), xs.length = k ∧ ((((C ⋆ array (t := i32) a xs) ⋆ H) ⋆
      (Q ⋆ region (a + BitVec.ofNat 64 (4 * k)) (n1 - 4 * k))) ⋆ region b n2) m := by
  obtain ⟨m0, mr, hu0, hd0, hp, hreg⟩ := hm
  obtain ⟨m1, m2, hu1, hd1, r1, r2⟩ := reg_peel (b := b) (n1 := n1) (n2 := n2) hreg hb hn hle
  obtain ⟨xs, hxl, ax⟩ := reg_pad_i32 k r1
  exact ⟨xs, hxl, sep_add_c_pad ⟨m0, mr, hu0, hd0, hp, ⟨m1, m2, hu1, hd1, ax, r2⟩⟩⟩

private theorem peel_h_i32 {C H Q : Mem 64 → Prop} {a : BitVec 64} (b : BitVec 64) (k n1 n2 : Nat)
    {n : Nat} {m : Mem 64} (hm : (((C ⋆ H) ⋆ Q) ⋆ region a n) m)
    (hb : a + BitVec.ofNat 64 n1 = b := by rfl) (hn : n = n1 + n2 := by omega)
    (hk : 4 * k ≤ n1 := by omega) (hle : n1 + n2 ≤ 2 ^ 64 := by omega) :
    ∃ xs : List (BitVec 32), xs.length = k ∧ (((C ⋆ (H ⋆ array (t := i32) a xs)) ⋆
      (Q ⋆ region (a + BitVec.ofNat 64 (4 * k)) (n1 - 4 * k))) ⋆ region b n2) m := by
  obtain ⟨m0, mr, hu0, hd0, hp, hreg⟩ := hm
  obtain ⟨m1, m2, hu1, hd1, r1, r2⟩ := reg_peel (b := b) (n1 := n1) (n2 := n2) hreg hb hn hle
  obtain ⟨xs, hxl, ax⟩ := reg_pad_i32 k r1
  exact ⟨xs, hxl, sep_add_h_pad ⟨m0, mr, hu0, hd0, hp, ⟨m1, m2, hu1, hd1, ax, r2⟩⟩⟩

private structure InitArrs (c : CorePlusCfg) where
  (vals mrk ph : List (BitVec 8))
  (lvl rsns trl tmp hp pos mclr : List (BitVec 32)) (sc : List (BitVec 64))
  (wh mstk cls wn lp : List (BitVec 32))
  ok : vals.length = 2 * c.mv ∧ mrk.length = c.mv ∧ ph.length = c.mv ∧ lvl.length = c.mv ∧
    rsns.length = c.mv ∧ trl.length = c.mv ∧ tmp.length = c.mv ∧ hp.length = c.mv ∧
    pos.length = c.mv ∧ mclr.length = c.mv ∧ sc.length = c.mv ∧ wh.length = 2 * c.mv ∧
    mstk.length = 2 * c.minDepth ∧ cls.length = 4 * c.max_c ∧ wn.length = 2 * c.max_c ∧
    lp.length = c.lcap

private def initPreState (c : CorePlusCfg) (d_cur d_val fuel : BitVec 64) (a : InitArrs c) :
    CorePlusState :=
  { d_cur := d_cur, d_val := d_val, lit_len := 0, num_clauses := 0, trail_end := 0,
    propagated := 0, cur_level := 0, fuel := fuel, confl_cid := 0xFFFFFFFF#64, tmp_cnt := 0,
    tmp_len := 0, min_clr_len := 0, min_clr_full := 0#64, vals := a.vals, mrk := a.mrk,
    lvl := a.lvl, rsns := a.rsns, trl := a.trl, tmp := a.tmp, wh := a.wh, cls := a.cls, wn := a.wn,
    lpool := a.lp, min_stk := a.mstk, min_clr := a.mclr,
    heur := {
      heap_len := c.mv, scinc := BitVec.ofNat 64 268435456, rel_period := 1024#64
      rel_limit := 1048576#64, rel_wait := 1024#64, rel_u := 1#64, rel_v := 1#64
      rel_trigger := 0#64, conflicts := 0#64, learned_lits := 0#64, min_removed := 0#64
      heap := a.hp, pos := a.pos, score := a.sc, phases := a.ph } }

local macro "cp_om" : tactic => `(tactic| (unfold CorePlusCfg.slack cpFixedBytes; omega))

private theorem cp_avail_peel1 (c : CorePlusCfg) {m : Mem 64}
    (hm : region (c.hdr + BitVec.ofNat 64 360) (c.avail - 360) m) :
    ∃ (vals mrk ph : List (BitVec 8)) (lvl rsns trl tmp hp pos mclr : List (BitVec 32)),
      (vals.length = 2 * c.mv ∧ mrk.length = c.mv ∧ ph.length = c.mv ∧ lvl.length = c.mv ∧
        rsns.length = c.mv ∧ trl.length = c.mv ∧ tmp.length = c.mv ∧ hp.length = c.mv ∧
        pos.length = c.mv ∧ mclr.length = c.mv) ∧
      ((((array (t := i8) c.pVals vals ⋆ array (t := i8) c.pMark mrk ⋆
          array (t := i32) c.pLevel lvl ⋆ array (t := i32) c.pReason rsns ⋆
          array (t := i32) c.pTrail trl ⋆ array (t := i32) c.pTmp tmp ⋆
          array (t := i32) c.pMinClr mclr) ⋆
          (array (t := i8) c.pPhases ph ⋆ array (t := i32) c.pHeap hp ⋆
          array (t := i32) c.pPos pos)) ⋆ cpPadRegs c) ⋆
        region c.pScore (c.avail - (360 + valsBytes c.mv + 2 * markBytes c.mv +
          7 * u32VarBytes c.mv))) m := by
  have hmv := c.hmv; have hmc := c.hmax_c; have hlc := c.hlcap; unfold dimacsBound at hmv hmc hlc
  have hfit := c.havail_fit; have hsz := c.hsize; have hmd := minDepthOf_le c.mv
  have hv := valsBytes_ge c.mv; have hmk := markBytes_ge c.mv; have hu := u32VarBytes_ge c.mv
  have hfx := cpFixedBytes_lt c.hmv; unfold CorePlusCfg.minDepth at *
  unfold cpFixedBytes at hsz hfx
  let r0 := c.avail - 360 - valsBytes c.mv - 2 * markBytes c.mv; let uv := u32VarBytes c.mv
  obtain ⟨_, hr, u1, d1, r1, hr⟩ :=
    reg_peel (b := c.pMark) (n1 := valsBytes c.mv) (n2 := c.avail - 360 - valsBytes c.mv) hm
  obtain ⟨vals, h1, a1⟩ := reg_pad_i8 (2 * c.mv) r1
  obtain ⟨_, hr, u2, d2, r2, hr⟩ := reg_peel (b := c.pPhases) (n1 := markBytes c.mv)
    (n2 := c.avail - 360 - valsBytes c.mv - markBytes c.mv) hr
  obtain ⟨mrk, h2, a2⟩ := reg_pad_i8 c.mv r2
  obtain ⟨_, hr, u3, d3, r3, hr⟩ := reg_peel (b := c.pLevel) (n1 := markBytes c.mv) (n2 := r0) hr
  obtain ⟨ph, h3, a3⟩ := reg_pad_i8 c.mv r3
  have h0 := sep_seed3 (sep_push u1 d1 a1 (sep_push u2 d2 a2 (sep_push u3 d3 a3 hr)))
  obtain ⟨lvl, h4, h0⟩ := peel_c_i32 c.pReason c.mv uv (r0 - uv) h0
  obtain ⟨rsns, h5, h0⟩ := peel_c_i32 c.pTrail c.mv uv (r0 - 2 * uv) h0
  obtain ⟨trl, h6, h0⟩ := peel_c_i32 c.pTmp c.mv uv (r0 - 3 * uv) h0
  obtain ⟨tmp, h7, h0⟩ := peel_c_i32 c.pHeap c.mv uv (r0 - 4 * uv) h0
  obtain ⟨hp, h8, h0⟩ := peel_h_i32 c.pPos c.mv uv (r0 - 5 * uv) h0
  obtain ⟨pos, h9, h0⟩ := peel_h_i32 c.pMinClr c.mv uv (r0 - 6 * uv) h0
  obtain ⟨mclr, h10, h0⟩ := peel_c_i32 c.pScore c.mv uv
    (c.avail - (360 + valsBytes c.mv + 2 * markBytes c.mv + 7 * uv)) h0
  exact ⟨vals, mrk, ph, lvl, rsns, trl, tmp, hp, pos, mclr,
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, h0⟩

private theorem cp_avail_peel2 (c : CorePlusCfg) {m : Mem 64}
    (hm : region (c.hdr + BitVec.ofNat 64 360) (c.avail - 360) m) :
    ∃ (vals mrk ph : List (BitVec 8)) (lvl rsns trl tmp hp pos mclr wh mstk : List (BitVec 32))
      (sc : List (BitVec 64)),
      (vals.length = 2 * c.mv ∧ mrk.length = c.mv ∧ ph.length = c.mv ∧ lvl.length = c.mv ∧
        rsns.length = c.mv ∧ trl.length = c.mv ∧ tmp.length = c.mv ∧ hp.length = c.mv ∧
        pos.length = c.mv ∧ mclr.length = c.mv ∧ sc.length = c.mv ∧ wh.length = 2 * c.mv ∧
        mstk.length = 2 * c.minDepth) ∧
      (((((array (t := i8) c.pVals vals ⋆ array (t := i8) c.pMark mrk ⋆
          array (t := i32) c.pLevel lvl ⋆ array (t := i32) c.pReason rsns ⋆
          array (t := i32) c.pTrail trl ⋆ array (t := i32) c.pTmp tmp ⋆
          array (t := i32) c.pMinClr mclr) ⋆
          (array (t := i8) c.pPhases ph ⋆ array (t := i32) c.pHeap hp ⋆
          array (t := i32) c.pPos pos)) ⋆ cpPadRegs c) ⋆
        (array64 c.pScore sc ⋆ (array (t := i32) c.pWh wh ⋆
          region (c.pWh + BitVec.ofNat 64 (8 * c.mv)) (whBytes c.mv - 8 * c.mv)) ⋆
          array (t := i32) c.pMinStk mstk)) ⋆
        region c.pClauses (c.avail - (360 + valsBytes c.mv + 2 * markBytes c.mv +
          7 * u32VarBytes c.mv + 8 * c.mv + whBytes c.mv + 8 * minDepthOf c.mv))) m := by
  have hmv := c.hmv; unfold dimacsBound at hmv; have hfit := c.havail_fit; have hsz := c.hsize
  have hmd := minDepthOf_le c.mv; have hw := whBytes_ge c.mv; have hfx := cpFixedBytes_lt c.hmv
  unfold cpFixedBytes at hsz hfx
  let pre := 360 + valsBytes c.mv + 2 * markBytes c.mv + 7 * u32VarBytes c.mv
  let rtail := c.avail - (pre + 8 * c.mv + whBytes c.mv + 8 * minDepthOf c.mv)
  obtain ⟨vals, mrk, ph, lvl, rsns, trl, tmp, hp, pos, mclr,
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, mp, mr, hu0, hd0, hp0, hr0⟩ := cp_avail_peel1 c hm
  obtain ⟨_, _, u11, d11, r11, hr⟩ :=
    reg_peel (b := c.pWh) (n1 := 8 * c.mv) (n2 := whBytes c.mv + 8 * minDepthOf c.mv + rtail) hr0
  obtain ⟨sc, h11, a11⟩ := region_to_array64 c.mv (by omega) r11
  obtain ⟨_, _, u12, d12, r12, hr⟩ :=
    reg_peel (b := c.pMinStk) (n1 := whBytes c.mv) (n2 := 8 * minDepthOf c.mv + rtail) hr
  obtain ⟨wh, h12, a12⟩ := reg_pad_i32 (2 * c.mv) r12
  rw [show 4 * (2 * c.mv) = 8 * c.mv by omega] at a12
  obtain ⟨_, _, u13, d13, r13, r_cl⟩ :=
    reg_peel (b := c.pClauses) (n1 := 8 * minDepthOf c.mv) (n2 := rtail) hr
  obtain ⟨mstk, h13, a13⟩ := region_to_array_i32 (2 * minDepthOf c.mv) (by omega)
    (by simpa [show 4 * (2 * minDepthOf c.mv) = 8 * minDepthOf c.mv by omega] using r13)
  exact ⟨vals, mrk, ph, lvl, rsns, trl, tmp, hp, pos, mclr, wh, mstk, sc,
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩, sep_peel2 (sep_push hu0 hd0 hp0
      (sep_push u11 d11 a11 (sep_push u12 d12 a12 (sep_push u13 d13 a13 r_cl))))⟩

private theorem cp_avail_to_arrays (c : CorePlusCfg) {m : Mem 64}
    (hm : region (c.hdr + BitVec.ofNat 64 360) (c.avail - 360) m) :
    ∃ a : InitArrs c, (CoreArrays c (initPreState c 0#64 0#64 0#64 a) ⋆
      HeurArrays c (initPreState c 0#64 0#64 0#64 a).heur ⋆ c.pad) m := by
  have hmc := c.hmax_c; have hlc := c.hlcap; unfold dimacsBound at hmc hlc
  have hfit := c.havail_fit; have hsz := c.hsize; have hfx := cpFixedBytes_lt c.hmv
  unfold cpFixedBytes at hsz hfx
  obtain ⟨vals, mrk, ph, lvl, rsns, trl, tmp, hp, pos, mclr, wh, mstk, sc,
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩,
    m_pre, m_cl, hu_pc, hd_pc, h_pre, hr_cl⟩ := cp_avail_peel2 c hm
  obtain ⟨_, _, u14_5, d14_5, r14_5, hr⟩ := reg_peel (b := c.pLpool) (n1 := 24 * c.max_c)
    (n2 := 4 * c.lcap + c.slack) hr_cl (hn := by cp_om) (hle := by cp_om)
  obtain ⟨_, _, u14, d14, r14, r15⟩ :=
    reg_peel (b := c.pWn) (n1 := 16 * c.max_c) (n2 := 8 * c.max_c) r14_5
  obtain ⟨cls, h14, a14⟩ := region_to_array_i32 (4 * c.max_c) (by omega)
    (by simpa [show 4 * (4 * c.max_c) = 16 * c.max_c by omega] using r14)
  obtain ⟨wn, h15, a15⟩ := region_to_array_i32 (2 * c.max_c) (by omega)
    (by simpa [show 4 * (2 * c.max_c) = 8 * c.max_c by omega] using r15)
  obtain ⟨_, _, u16, d16, r16, r17⟩ := reg_peel (b := c.pSlack) (n1 := 4 * c.lcap)
    (n2 := c.slack) hr (hn := by cp_om) (hle := by cp_om)
  obtain ⟨lp, h16, a16⟩ := region_to_array_i32 c.lcap (by omega) r16
  have hm_out := sep_finish_arrs (sep_push hu_pc hd_pc h_pre
    (sep_push u14_5 d14_5 (sep_push u14 d14 a14 a15) (sep_push u16 d16 a16 r17)))
  refine ⟨⟨vals, mrk, ph, lvl, rsns, trl, tmp, hp, pos, mclr, sc, wh, mstk, cls, wn, lp,
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩⟩, ?_⟩
  unfold CoreArrays HeurArrays CorePlusCfg.pad initPreState
  exact sep_mono2 (sep_mono2 (fun _ h => reorder_c12 h) (fun _ h => reorder_h4 h)) (fun _ h => h)
    m hm_out
def hdrTail41 (hdr : BitVec 64) (ws : List (BitVec 64)) : Mem 64 → Prop :=
  fun m => ws.length = 41 ∧ array64 (hdr + 32) ws m
namespace IngestTactics
@[scoped c0_store] theorem c0_store_hdr64 (off v hdr : BitVec 64) (ws : List (BitVec 64))
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (hdrTail41 hdr ws ⋆ F) m)
    (h123 : 32 ≤ off.toNat ∧ (off.toNat - 32) % 8 = 0 ∧ (off.toNat - 32) / 8 < 41) :
    storeOk m i64 (hdr + off) ∧
      (hdrTail41 hdr (ws.set ((off.toNat - 32) / 8) v) ⋆ F) (storeMem m i64 (hdr + off) v) := by
  obtain ⟨m1, m2, hu, hd, ⟨hwl, ha⟩, hf⟩ := hm
  have h : hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * ((off.toNat - 32) / 8)) = hdr + off := by
    rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, cp_ptr_add_ofNat,
      show 32 + 8 * ((off.toNat - 32) / 8) = off.toNat by omega, bv_ofNat_toNat_eq]
  obtain ⟨hok, n1, n2, nhu, nhd, nha, nhf⟩ :=
    store_array64 (i := (off.toNat - 32) / 8) v (by rw [hwl]; exact h123.2.2)
      (⟨m1, m2, hu, hd, ha, hf⟩ : (array64 (hdr + 32) ws ⋆ F) m)
  rw [h] at hok nhu; exact ⟨hok, n1, n2, nhu, nhd, ⟨by simp [hwl], nha⟩, nhf⟩
@[scoped c0_load] theorem c0_load_dimacs_mv {d mv nc cur val : BitVec 64}
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (dimacsState d mv nc cur val ⋆ F) m) :
    loadVal m i64 d = some mv := Kissat.load_dimacs_mv hm
@[scoped c0_load] theorem c0_load_dimacs_nc {d mv nc cur val : BitVec 64}
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (dimacsState d mv nc cur val ⋆ F) m) :
    loadVal m i64 (d + 8) = some nc := Kissat.load_dimacs_nc hm
end IngestTactics
open scoped IngestTactics
private theorem len_cons10 {α} (xs : List α) (n : Nat) (h : xs.length = n + 10) :
    ∃ a b c d e f g h1 i j ys, ys.length = n ∧
      xs = a :: b :: c :: d :: e :: f :: g :: h1 :: i :: j :: ys := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h1, _ | ⟨i, _ |
    ⟨j, ys⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨a, b, c, d, e, f, g, h1, i, j, ys, h, rfl⟩

private theorem hdrTail_set_eq (c : CorePlusCfg) (fuel : BitVec 64) (a : InitArrs c)
    (ws : List (BitVec 64)) (hwl : ws.length = 41) :
    ((((((((((((((((((((((((((((((((((((((((ws.set 4 c.pVals).set 5 c.pMark).set 24 c.pPhases).set
      6 c.pLevel).set 7 c.pReason).set 8 c.pTrail).set 13 c.pTmp).set 21 c.pHeap).set
      22 c.pPos).set 26 c.pMinClr).set 23 c.pScore).set 9 c.pWh).set 25 c.pMinStk).set
      10 c.pClauses).set 11 c.pWn).set 12 c.pLpool).set 0 (BitVec.ofNat 64 c.max_c)).set
      1 (BitVec.ofNat 64 c.lcap)).set 2 0#64).set 3 0#64).set 14 0#64).set 15 0#64).set
      16 0#64).set 17 fuel).set 18 0xFFFFFFFF#64).set 19 0#64).set 20 0#64).set
      27 (BitVec.ofNat 64 c.mv)).set 28 (BitVec.ofNat 64 268435456)).set
      29 (BitVec.ofNat 64 c.minDepth)).set 30 0#64).set 31 0#64).set 32 1024#64).set
      33 1048576#64).set 34 1024#64).set 35 1#64).set 36 1#64).set 37 0#64).set 38 0#64).set
      39 0#64).set 40 0#64 = hdrTailWords c (initPreState c 0#64 0#64 fuel a) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ws1, h1, rfl⟩ := len_cons10 ws 31 hwl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ws2, h2, rfl⟩ := len_cons10 ws1 21 h1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ws3, h3, rfl⟩ := len_cons10 ws2 11 h2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ws4, h4, rfl⟩ := len_cons10 ws3 1 h3
  rcases ws4 with _ | ⟨_, _ | _⟩ <;> simp at h4
  simp only [List.set_cons_zero, List.set_cons_succ, hdrTailWords, initPreState]

namespace IngestTactics
scoped elab "cp_beta" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let ty ← Lean.instantiateMVars (← g.getType)
  if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
    let e := ty.getArg! 4; let e' := e.headBeta
    if e' != e then
      let g' ← Lean.Meta.withTransparency .reducible
        (g.replaceTargetDefEq (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e')))
      Lean.Elab.Tactic.setGoals [g']

private meta def clearStaleMem (m0 : Lean.Expr) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let .fvar mId := m0 | return
    for d in (← Lean.getLCtx).decls.toArray.reverse do
      let some d := d | continue
      let t ← Lean.instantiateMVars d.type
      if t.isAppOf ``Std.ExtHashMap.sep && t.appArg! == m0 then
        try Lean.Elab.Tactic.liftMetaTactic1 fun g => some <$> g.clear d.fvarId catch _ => pure ()
    try Lean.Elab.Tactic.liftMetaTactic1 fun g => some <$> g.clear mId catch _ => pure ()

private theorem cp_fst {α β : Type} (a : α) (b : β) : (a, b).1 = a := rfl
private theorem cp_snd {α β : Type} (a : α) (b : β) : (a, b).2 = b := rfl

section CpLetSteps
variable {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64} {n : Nat}
private theorem cp_let_copy {t : Ty} (a : Arg Val t) (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.copy t) (a, ())) k) m = wp Γ Q X (k (a.val, ())) m := by
  simp [wp_let_copy_eq]
private theorem cp_let_add (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.add (.bits n)) (a, b, ())) k) m =
      wp Γ Q X (k (a.val + b.val, ())) m := by simp [wp_let_add_eq, lift2, Ty.hasFloat]
private theorem cp_let_sub (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.sub (.bits n)) (a, b, ())) k) m =
      wp Γ Q X (k (a.val - b.val, ())) m := by simp [wp_let_sub_eq, lift2, Ty.hasFloat]
private theorem cp_let_mul (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.mul (.bits n)) (a, b, ())) k) m =
      wp Γ Q X (k (a.val * b.val, ())) m := by simp [wp_let_mul_eq, lift2, Ty.hasFloat]
private theorem cp_let_and (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.and (.bits n)) (a, b, ())) k) m =
      wp Γ Q X (k (a.val &&& b.val, ())) m := by simp [wp_let_and_eq, lift2]
private theorem cp_let_not (a : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.not (.bits n)) (a, ())) k) m =
      wp Γ Q X (k (~~~a.val, ())) m := by simp [wp_let_not_eq, lift1]
private theorem cp_let_shl (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.shl (.bits n)) (a, b, ())) k) m =
      wp Γ Q X (k (a.val <<< (b.val.toNat % n), ())) m := by
  simp [wp_let_shl_eq, lift2, Ty.hasFloat]
private theorem cp_let_lshr (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.lshr (.bits n)) (a, b, ())) k) m =
      wp Γ Q X (k (a.val >>> (b.val.toNat % n), ())) m := by
  simp [wp_let_lshr_eq, lift2, Ty.hasFloat]
private theorem cp_let_sext {mW nW : Nat} (a : Arg Val (.bits mW))
    (k : Tup Val [.bits nW] → Expr Val Cont rs) (h : mW ≤ nW) :
    wp Γ Q X (.let_ (Op.mk (.sext mW nW) (a, ())) k) m =
      wp Γ Q X (k (a.val.signExtend nW, ())) m := by simp [wp_let_sext_eq, h]
private theorem cp_let_ult {hm : Ty.bool = (Ty.bits n).mask} (a b : Arg Val (.bits n))
    (k : Tup Val [.bool] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult (.bits n) .bool hm) (a, b, ())) k) m =
      wp Γ Q X (k (a.val.ult b.val, ())) m := by
  simp [wp_let_cmp_eq, liftCmp, Ty.hasFloat, CmpOp.evalBits]
private theorem cp_let_ugt {hm : Ty.bool = (Ty.bits n).mask} (a b : Arg Val (.bits n))
    (k : Tup Val [.bool] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ugt (.bits n) .bool hm) (a, b, ())) k) m =
      wp Γ Q X (k (b.val.ult a.val, ())) m := by
  simp [wp_let_cmp_eq, liftCmp, Ty.hasFloat, CmpOp.evalBits]
end CpLetSteps

scoped macro "cp_val_simp" : conv =>
  `(conv| simp only [cp_fst, cp_snd, LeanQbe.T.op1_eq_mk, LeanQbe.T.op2_eq_mk, LeanQbe.T.vals_nil,
    LeanQbe.T.vals_cons, LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm, LeanQbe.T.Ty.hasFloat,
    LeanQbe.T.OpCode.ult, LeanQbe.T.OpCode.ugt, LeanQbe.T.evalBits_ult_eq,
    LeanQbe.T.evalBits_ugt_eq, LeanQbe.T.liftCmp, cast_eq, ite_self, ite_true, ite_false])

private meta def findSepMem (m0 : Lean.Expr) : Lean.Elab.Tactic.TacticM (Option Lean.Expr) :=
  Lean.Elab.Tactic.withMainContext do
    for d in (← Lean.getLCtx).decls.toArray.reverse do
      let some d := d | continue
      if d.isImplementationDetail then continue
      let t ← Lean.instantiateMVars d.type
      if t.isAppOf ``Std.ExtHashMap.sep && t.appArg! == m0 then return some d.toExpr
    return none

private meta def cpLetStep (e : Lean.Expr) : Lean.Elab.Tactic.TacticM Unit := do
  let op := e.getAppArgs[e.getAppNumArgs - 2]!
  let code := op.getAppArgs[op.getAppNumArgs - 2]!
  let tac ← match code.getAppFn.constName? with
    | some ``LeanQbe.T.OpCode.copy => `(tactic| refine (cp_let_copy _ _).mpr ?_)
    | some ``LeanQbe.T.OpCode.add => `(tactic| refine (cp_let_add _ _ _).mpr ?_)
    | some ``LeanQbe.T.OpCode.sub => `(tactic| refine (cp_let_sub _ _ _).mpr ?_)
    | some ``LeanQbe.T.OpCode.mul => `(tactic| refine (cp_let_mul _ _ _).mpr ?_)
    | some ``LeanQbe.T.OpCode.and => `(tactic| refine (cp_let_and _ _ _).mpr ?_)
    | some ``LeanQbe.T.OpCode.not => `(tactic| refine (cp_let_not _ _).mpr ?_)
    | some ``LeanQbe.T.OpCode.shl => `(tactic| refine (cp_let_shl _ _ _).mpr ?_)
    | some ``LeanQbe.T.OpCode.lshr => `(tactic| refine (cp_let_lshr _ _ _).mpr ?_)
    | some ``LeanQbe.T.OpCode.sext => `(tactic| refine (cp_let_sext _ _ (by decide)).mpr ?_)
    | some ``LeanQbe.T.OpCode.cmp =>
      match (code.getArg! 0).getAppFn.constName? with
      | some ``LeanQbe.T.CmpOp.ult => `(tactic| refine (cp_let_ult _ _ _).mpr ?_)
      | some ``LeanQbe.T.CmpOp.ugt => `(tactic| refine (cp_let_ugt _ _ _).mpr ?_)
      | _ => `(tactic| (
          refine (LeanQbe.T.wp_let_cmp_eq _ _ _ _ _).mpr ?_
          rw [ite_eq_right (fun hc => by revert hc; decide)]))
    | _ => `(tactic| first
        | refine (LeanQbe.T.wp_let_or_eq _ _ _).mpr ?_
        | refine (LeanQbe.T.wp_let_xor_eq _ _ _).mpr ?_
        | refine (LeanQbe.T.wp_let_select_eq _ _ _).mpr ?_
        | refine (LeanQbe.T.wp_let_zext_eq _ _ _ _).mpr ⟨by decide, ?_⟩
        | refine (LeanQbe.T.wp_let_trunc_eq _ _ _ _).mpr ⟨by decide, ?_⟩)
  Lean.Elab.Tactic.evalTactic tac

private meta def cpHeadStepOnce : Lean.Elab.Tactic.TacticM Bool :=
  Lean.Elab.Tactic.withMainContext do
    let g ← Lean.Elab.Tactic.getMainGoal
    let ty0 ← Lean.instantiateMVars (← g.getType)
    if ty0.isMData then Lean.Elab.Tactic.setGoals [← g.replaceTargetDefEq ty0.consumeMData]
    let g ← Lean.Elab.Tactic.getMainGoal
    let ty := (← Lean.instantiateMVars (← g.getType)).headBeta
    if !(ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6) then return false
    let e0 := ty.getArg! 4
    if e0.isMData then Lean.Elab.Tactic.setGoals [← g.replaceTargetDefEq
      (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e0.consumeMData))]
    let g ← Lean.Elab.Tactic.getMainGoal
    let e := ((← Lean.instantiateMVars (← g.getType)).headBeta.getArg! 4).headBeta
    match e.getAppFn.constName? with
    | some ``LeanQbe.T.Expr.let_ =>
      Lean.Elab.Tactic.evalTactic (← `(tactic| conv => arg 4; arg 1; cp_val_simp))
      let g ← Lean.Elab.Tactic.getMainGoal
      cpLetStep ((← Lean.instantiateMVars (← g.getType)).headBeta.getArg! 4).headBeta
      Lean.Elab.Tactic.evalTactic (← `(tactic| cp_beta)); return true
    | some ``LeanQbe.T.Expr.load =>
      Lean.Elab.Tactic.evalTactic (← `(tactic| conv => arg 4; arg 2; cp_val_simp))
      let g ← Lean.Elab.Tactic.getMainGoal
      let [hl, hk] := (← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels
        ``LeanQbe.T.wp_load_of)).take 2 | return false
      LeanQbe.T.C0Step.memSolve true hl; Lean.Elab.Tactic.setGoals [hk]
      Lean.Elab.Tactic.evalTactic (← `(tactic| cp_beta)); return true
    | some ``LeanQbe.T.Expr.store =>
      Lean.Elab.Tactic.evalTactic (← `(tactic| conv => arg 4; arg 1; cp_val_simp))
      Lean.Elab.Tactic.evalTactic (← `(tactic| conv => arg 4; arg 2; cp_val_simp))
      let g ← Lean.Elab.Tactic.getMainGoal
      let m0 := (← Lean.instantiateMVars (← g.getType)).getArg! 5
      let [hs, hk] := (← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels
        ``LeanQbe.T.wp_store_sep)).take 2 | return false
      Lean.Elab.Tactic.setGoals [hs]
      let okFast ← try
        let some hmE ← findSepMem m0 | throwError "no sep"
        let hmS ← Lean.Elab.Term.exprToSyntax hmE
        Lean.Elab.Tactic.evalTactic (← `(tactic| refine c0_store_hdr64 _ _ _ _ $hmS (by decide)))
        pure (← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty
      catch _ => pure false
      if !okFast then LeanQbe.T.C0Step.memSolve false hs
      Lean.Elab.Tactic.setGoals [hk]
      let mId := Lean.mkIdent `m; let hmId := Lean.mkIdent `hm
      Lean.Elab.Tactic.evalTactic (← `(tactic| intro $mId:ident $hmId:ident))
      if !okFast then Lean.Elab.Tactic.evalTactic (← `(tactic| try simp only
        [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm, Std.ExtHashMap.sep_emp] at $hmId:ident))
      clearStaleMem m0; return true
    | some ``LeanQbe.T.Expr.ret =>
      Lean.Elab.Tactic.evalTactic (← `(tactic| (rw [LeanQbe.T.wp_ret]; try simp only
        [LeanQbe.T.vals_cons, LeanQbe.T.vals_nil, LeanQbe.T.Arg.val_var,
          LeanQbe.T.Arg.val_imm, cp_fst, cp_snd]))); return true
    | some ``LeanQbe.T.Expr.jump =>
      Lean.Elab.Tactic.evalTactic (← `(tactic| (rw [LeanQbe.T.wp_jump]; try simp only
        [LeanQbe.T.vals_cons, LeanQbe.T.vals_nil, LeanQbe.T.Arg.val_var,
          LeanQbe.T.Arg.val_imm, cp_fst, cp_snd]))); return true
    | some ``LeanQbe.T.Expr.jnz =>
      Lean.Elab.Tactic.evalTactic (← `(tactic| conv => arg 4; arg 1; cp_val_simp)); return false
    | _ => return false

scoped elab "cp_head_steps" : tactic => do
  for _ in [:300] do
    let gs ← Lean.Elab.Tactic.getUnsolvedGoals
    if gs.isEmpty then break
    let g := gs.head!; Lean.Elab.Tactic.setGoals [g]
    let s ← Lean.Elab.Tactic.saveState
    let ok ← try cpHeadStepOnce catch _ => s.restore; pure false
    Lean.Elab.Tactic.setGoals ((← Lean.Elab.Tactic.getUnsolvedGoals) ++ gs.tail!)
    if !ok then break
end IngestTactics
open scoped IngestTactics

private theorem cp_shl_sext3 {n : Nat} (hn : n < 2 ^ 61) :
    BitVec.ofNat 64 n <<< (((3 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (8 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, show ((3 : BitVec 32).signExtend 64).toNat % 64 = 3 from rfl,
    Kissat.bv64_ofNat_toNat (by omega), Nat.shiftLeft_eq, Kissat.bv64_ofNat_toNat (by omega)]; omega
private theorem cp_vb_eq {mv : Nat} (hmv : mv < dimacsBound) :
    (BitVec.ofNat 64 mv <<< (((1 : BitVec 32).signExtend 64).toNat % 64) + 7) &&& ~~~7 =
      BitVec.ofNat 64 (valsBytes mv) := by
  unfold dimacsBound at hmv; rw [Kissat.bv_shl_sext1, cp_align8 (n := 2 * mv) (by omega)]; rfl
private theorem cp_mb_eq {mv : Nat} (hmv : mv < dimacsBound) :
    (BitVec.ofNat 64 mv + (7 : BitVec 64)) &&& ~~~(7 : BitVec 64) =
      BitVec.ofNat 64 (markBytes mv) := by
  unfold dimacsBound at hmv; rw [cp_align8 (n := mv) (by omega)]; rfl
private theorem cp_ub_eq {mv : Nat} (hmv : mv < dimacsBound) :
    (BitVec.ofNat 64 mv <<< (((2 : BitVec 32).signExtend 64).toNat % 64) + 7) &&& ~~~7 =
      BitVec.ofNat 64 (u32VarBytes mv) := by
  unfold dimacsBound at hmv; rw [Kissat.bv_shl_sext2, cp_align8 (n := 4 * mv) (by omega)]; rfl
private theorem cp_wb_eq {mv : Nat} (hmv : mv < dimacsBound) :
    ((BitVec.ofNat 64 mv <<< (((1 : BitVec 32).signExtend 64).toNat % 64)) <<<
      (((2 : BitVec 32).signExtend 64).toNat % 64) + 7) &&& ~~~7 =
      BitVec.ofNat 64 (whBytes mv) := by
  unfold dimacsBound at hmv; rw [Kissat.bv_shl_sext1, Kissat.bv_shl_sext2,
    show 4 * (2 * mv) = 8 * mv by omega, cp_align8 (n := 8 * mv) (by omega)]; rfl

private theorem cp_fixed_bv_eq {mv : Nat} (hmv : mv < dimacsBound) :
    (360 : BitVec 64) +
      ((BitVec.ofNat 64 mv <<< (((1 : BitVec 32).signExtend 64).toNat % 64) + 7) &&& ~~~7) +
      (((BitVec.ofNat 64 mv + 7) &&& ~~~7) <<< (((1 : BitVec 32).signExtend 64).toNat % 64)) +
      (((BitVec.ofNat 64 mv <<< (((2 : BitVec 32).signExtend 64).toNat % 64) + 7) &&& ~~~7) *
        (7 : BitVec 64)) + (BitVec.ofNat 64 mv <<< (((3 : BitVec 32).signExtend 64).toNat % 64)) +
      ((((BitVec.ofNat 64 mv <<< (((1 : BitVec 32).signExtend 64).toNat % 64)) <<<
        (((2 : BitVec 32).signExtend 64).toNat % 64)) + 7) &&& ~~~7) +
      (BitVec.ofNat 64 (minDepthOf mv) <<< (((3 : BitVec 32).signExtend 64).toNat % 64)) =
      BitVec.ofNat 64 (cpFixedBytes mv) := by
  have hmv' := hmv; unfold dimacsBound at hmv'; have hmd := minDepthOf_le mv
  rw [cp_vb_eq hmv, cp_mb_eq hmv, cp_ub_eq hmv, cp_wb_eq hmv, cp_shl_sext3 (by omega),
    cp_shl_sext3 (by omega), Kissat.bv_shl_sext1,
    show BitVec.ofNat 64 (u32VarBytes mv) * (7 : BitVec 64) = BitVec.ofNat 64 (u32VarBytes mv * 7)
      by apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_mod],
    show (360 : BitVec 64) = BitVec.ofNat 64 360 from rfl]; repeat rw [bv_add_ofNat]
  unfold cpFixedBytes markBytes; congr 1; omega

private theorem cp_ult_maxc_eq {x : Nat} (hx : x < 2 ^ 64) :
    (268435455 : BitVec 64).ult (BitVec.ofNat 64 x) = decide (dimacsBound - 1 < x) := by
  simpa [show (268435455 : BitVec 64) = BitVec.ofNat 64 (dimacsBound - 1) from rfl] using
    bv_ult_eq (a := dimacsBound - 1) (b := x) (by decide) hx

private theorem init_state_split_arena (c : CorePlusCfg) (fuel : BitVec 64) {cnf_ptr : BitVec 64}
    {cnfBytes : List UInt8} {j : Nat} {R : Mem 64 → Prop} {m0 : Mem 64} (hav360 : 360 ≤ c.avail)
    (hm0 : (bytes cnf_ptr cnfBytes ⋆ dimacsState c.hdr (BitVec.ofNat 64 c.mv)
        (BitVec.ofNat 64 c.nc) (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) ⋆
        (region (c.hdr + 32#64) (c.avail - 32) ⋆ R)) m0) :
    ∃ (ws : List (BitVec 64)) (a : InitArrs c), ws.length = 41 ∧ (hdrTail41 c.hdr ws ⋆
        (CoreArrays c (initPreState c (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) fuel a) ⋆
          HeurArrays c (initPreState c (cnf_ptr + BitVec.ofNat 64 j)
            (BitVec.ofNat 64 c.nc) fuel a).heur ⋆ c.pad ⋆ bytes cnf_ptr cnfBytes ⋆
          dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
            (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) ⋆ R)) m0 := by
  have hav_le := c.havail_fit
  obtain ⟨m_reg, m_cdr, hu_r, hd_r, h_reg, h_cdr⟩ := (show (region (c.hdr + 32#64) (c.avail - 32) ⋆
    (bytes cnf_ptr cnfBytes ⋆ dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
      (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) ⋆ R)) m0 from sep_ac hm0)
  obtain ⟨m_h, m_a, hu_ha, hd_ha, h_h, h_a⟩ := reg_peel (b := c.hdr + 360#64) (n1 := 328)
    (n2 := c.avail - 360) h_reg (hb := by rw [show (360#64 : BitVec 64) =
      BitVec.ofNat 64 (32 + 328) from rfl, ← cp_ptr_add_ofNat])
  obtain ⟨ws, hwl, h_ws⟩ := region_to_array64 41 (by decide) h_h
  obtain ⟨a, h_arrs⟩ := cp_avail_to_arrays c h_a
  have hca : CoreArrays c (initPreState c 0#64 0#64 0#64 a) = CoreArrays c
      (initPreState c (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) fuel a) := rfl
  have hha : HeurArrays c (initPreState c 0#64 0#64 0#64 a).heur = HeurArrays c
      (initPreState c (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) fuel a).heur := rfl
  rw [hca, hha] at h_arrs
  have h_ht : hdrTail41 c.hdr ws m_h := ⟨hwl, h_ws⟩
  refine ⟨ws, a, hwl, sep_ac (sep_push hu_r hd_r (sep_push hu_ha hd_ha h_ht h_arrs) h_cdr)⟩

private theorem init_hdrtail_norm (c : CorePlusCfg) (d_cur d_val fuel : BitVec 64)
    (a : InitArrs c) (ws : List (BitVec 64)) (hwl : ws.length = 41) :
    let vb := (BitVec.ofNat 64 c.mv <<< (((1 : BitVec 32).signExtend 64).toNat % 64) + 7) &&& ~~~7
    let mb := (BitVec.ofNat 64 c.mv + 7) &&& ~~~7
    let ub := (BitVec.ofNat 64 c.mv <<< (((2 : BitVec 32).signExtend 64).toNat % 64) + 7) &&& ~~~7
    let sb := BitVec.ofNat 64 c.mv <<< (((3 : BitVec 32).signExtend 64).toNat % 64)
    let wb := ((BitVec.ofNat 64 c.mv <<< (((1 : BitVec 32).signExtend 64).toNat % 64)) <<<
      (((2 : BitVec 32).signExtend 64).toNat % 64) + 7) &&& ~~~7
    let db := BitVec.ofNat 64 (minDepthOf c.mv) <<< (((3 : BitVec 32).signExtend 64).toNat % 64)
    let sc1 := (1 : BitVec 64) <<< (((28 : BitVec 32).signExtend 64).toNat % 64)
    let p0 := c.hdr + 360; let p1 := p0 + vb; let p2 := p1 + mb; let p3 := p2 + mb
    let p4 := p3 + ub; let p5 := p4 + ub; let p6 := p5 + ub; let p7 := p6 + ub
    let p8 := p7 + ub; let p9 := p8 + ub; let p10 := p9 + ub; let p11 := p10 + sb
    let p12 := p11 + wb; let p13 := p12 + db; let p15 := p13 + BitVec.ofNat 64 c.max_c * 24
    let p14 := p13 + (BitVec.ofNat 64 c.max_c <<< (((4 : BitVec 32).signExtend 64).toNat % 64))
    ((((((((((((((((((((((((((((((((((((((((ws.set 4 p0).set 5 p1).set 24 p2).set 6 p3).set
      7 p4).set 8 p5).set 13 p6).set 21 p7).set 22 p8).set 26 p9).set 23 p10).set 9 p11).set
      25 p12).set 10 p13).set 11 p14).set 12 p15).set 0 (BitVec.ofNat 64 c.max_c)).set
      1 (BitVec.ofNat 64 c.lcap)).set 2 0).set 3 0).set 14 0).set 15 0).set 16 0).set
      17 fuel).set 18 4294967295).set 19 0).set 20 0).set 27 (BitVec.ofNat 64 c.mv)).set
      28 sc1).set 29 (BitVec.ofNat 64 (minDepthOf c.mv))).set 30 0).set 31 0).set 32 1024).set
      33 1048576).set 34 1024).set 35 1).set 36 1).set 37 0).set 38 0).set 39 0).set 40 0 =
    hdrTailWords c (initPreState c d_cur d_val fuel a) := by
  have hmv := c.hmv; have hmc := c.hmax_c; unfold dimacsBound at hmv hmc
  have hmd := minDepthOf_le c.mv; dsimp only
  rw [show c.hdr + (360 : BitVec 64) = c.pVals from rfl, cp_vb_eq c.hmv, cp_mb_eq c.hmv,
    cp_ub_eq c.hmv, cp_wb_eq c.hmv, cp_shl_sext3 (by omega), cp_shl_sext3 (by omega),
    Kissat.bv_shl_sext4, show BitVec.ofNat 64 c.max_c * (24 : BitVec 64) =
      BitVec.ofNat 64 (24 * c.max_c) by rw [cp_mul24, show c.max_c * 24 = 24 * c.max_c by omega],
    show (1 : BitVec 64) <<< (((28 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 268435456 from by decide]
  exact hdrTail_set_eq c fuel a ws hwl

private theorem init_state_finish_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hZero : ∀ a m Q X, corePlusZeroTablesSpec a m Q X → Γ "kissat_zero_tables" [i64] [] a m Q X)
    {c : CorePlusCfg} {ws : List (BitVec 64)} {cnf_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {j : Nat} {rest : List UInt8} (a : InitArrs c) {R : Mem 64 → Prop} {m : Mem 64}
    (hhdr : parseHeader cnfBytes = some (c.mv, c.nc, rest)) (hj : j ≤ cnfBytes.length)
    (hdrop : cnfBytes.drop j = rest) (hws : ws = hdrTailWords c
      (initPreState c (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) fuel a))
    (hm : (hdrTail41 c.hdr ws ⋆ (CoreArrays c
      (initPreState c (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) fuel a) ⋆
      HeurArrays c (initPreState c (cnf_ptr + BitVec.ofNat 64 j)
        (BitVec.ofNat 64 c.nc) fuel a).heur ⋆ c.pad ⋆ bytes cnf_ptr cnfBytes ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) ⋆ R)) m)
    (hQtrue : ∀ (c' : CorePlusCfg) (s : CorePlusState) (j' : Nat) (rest' : List UInt8)
      (m' : Mem 64), c'.hdr = c.hdr → c'.avail = c.avail →
      parseHeader cnfBytes = some (c'.mv, c'.nc, rest') → j' ≤ cnfBytes.length →
      cnfBytes.drop j' = rest' → CorePlusInv c' (shiftDownCnf CNF.empty) s →
      s.d_cur = cnf_ptr + BitVec.ofNat 64 j' → s.lit_len = 0 → s.num_clauses = 0 →
      s.trail_end = 0 → s.propagated = 0 → s.cur_level = 0 → s.fuel = fuel → s.min_clr_len = 0 →
      s.min_clr_full = 0#64 → s.vals = List.replicate (2 * c'.mv) 0#8 →
      s.wh = List.replicate (2 * c'.mv) 0xFFFFFFFF#32 → s.heur.rel_trigger = 0#64 →
      (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c' s ⋆ R) m' → Q (true, ()) m') :
    wp Γ Q X (.call "kissat_zero_tables" (as := [i64]) (bs := [])
        (Arg.var (t := i64) c.hdr, ()) fun _ => .ret (Arg.imm (t := .bool) true, ())) m := by
  let s1 := initPreState c (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) fuel a
  have ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := a.ok
  have hlt32 : (0 : Nat) < 2 ^ 32 := by decide
  have hlt64 : (0 : Nat) < 2 ^ 64 := by decide
  have hmem1 : (CorePlusMem c s1 ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := by
    obtain ⟨m1, m2, hu, hd, ⟨_, ha1⟩, hr⟩ := hm
    have hm' := sep_push hu hd ha1 hr; rw [hws] at hm'; unfold CorePlusMem; exact sep_ac hm'
  have hlen1 : s1.LengthsOk c := ⟨h1, h2, h4, h5, h6, h7, h12, h14, h15, h16, h13, h10,
    Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.le_refl _, hlt32, hlt64, hlt64,
    Nat.zero_le _, ⟨h8, h9, h11, h3, Nat.le_refl _⟩⟩
  apply wp_call_of_spec; apply hZero
  refine ⟨c, s1, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen1, hmem1, ?_⟩
  intro mstk' heur' m' hmstk' hhok' hrt' s0 hm'; cp_head_steps
  have hlen0 : s0.LengthsOk c := { hlen1 with
    vals_len := by simp [s0], mrk_len := by simp [s0], lvl_len := by simp [s0],
    rsns_len := by simp [s0], tmp_len_arr := by simp [s0], wh_len := by simp [s0],
    min_stk_len := hmstk', min_clr_len_arr := by simp [s0], heur_ok := hhok' }
  rw [sep_comm_l, ← sep_assoc] at hm'
  exact hQtrue c s0 j rest m' rfl rfl hhdr hj hdrop (corePlusInv_init hlen0 rfl rfl rfl rfl rfl)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hrt' hm'

private theorem init_hdr_remerge {cnf_ptr hdr_addr : BitVec 64} {avail : Nat}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} (h32 : 32 ≤ avail) (hle : avail ≤ 2 ^ 64)
    {mv' nc' cur' val' : BitVec 64} {m' : Mem 64}
    (hm' : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr mv' nc' cur' val' ⋆
      region (hdr_addr + BitVec.ofNat 64 32) (avail - 32) ⋆ R) m') :
    (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail ⋆ R) m' := by
  have h2 := sep_mono2 (sep_mono2 (fun _ => Kissat.dimacsState_to_region) (fun _ h => h))
    (fun _ h => h) m' (show ((dimacsState hdr_addr mv' nc' cur' val' ⋆
      region (hdr_addr + BitVec.ofNat 64 32) (avail - 32)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m' from sep_ac hm')
  rw [region_merge_eq (a := hdr_addr) (n1 := 32) (n2 := avail - 32) (n := avail)
    (by omega) hle] at h2
  exact sep_ac h2

private theorem init_hdr_fail {cnf_ptr hdr_addr : BitVec 64} {avail : Nat}
    {cnfBytes rest : List UInt8} {mv nc : Nat} {cur' val' : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [.bool]} {m' : Mem 64} (h32 : 32 ≤ avail) (hle : avail ≤ 2 ^ 64)
    (hhdr : parseHeader cnfBytes = some (mv, nc, rest)) (hfail : avail < cpFixedBytes mv + nc * 24)
    (hm' : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr (BitVec.ofNat 64 mv)
      (BitVec.ofNat 64 nc) cur' val' ⋆ region (hdr_addr + 32#64) (avail - 32) ⋆ R) m')
    (hQfalse : ∀ m'', (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail ⋆ R) m'' →
      (∀ mv' nc' rest', parseHeader cnfBytes = some (mv', nc', rest') →
        avail < cpFixedBytes mv' + nc' * 24) → Q (false, ()) m'') : Q (false, ()) m' :=
  hQfalse m' (init_hdr_remerge h32 hle hm') fun _ _ _ h => by
    rw [hhdr] at h; rcases Option.some.inj h with ⟨rfl, rfl, rfl⟩; exact hfail

local macro "cp_jnz_t" h:ident : tactic => `(tactic|
  (dsimp only [Arg.val_var] at $h:ident; rw [decide_eq_true_eq] at $h:ident; cp_head_steps))
local macro "cp_jnz_f" h:ident : tactic => `(tactic|
  (dsimp only [Arg.val_var] at $h:ident; rw [decide_eq_false_iff_not] at $h:ident; cp_head_steps))

theorem kissat_init_state_wp (Γ : Env)
    (hHdr : ∀ a m Q X, kissatParseHeaderSpec a m Q X →
      Γ "kissat_parse_header" [i64, i64, i64] [.bool] a m Q X)
    (hZero : ∀ a m Q X, corePlusZeroTablesSpec a m Q X → Γ "kissat_zero_tables" [i64] [] a m Q X) :
    ∀ a m Q X, corePlusInitStateSpec a m Q X → Func.wp Γ kissat_init_state_body a m Q X := by
  rintro ⟨cnf_ptr, cend, hdr_addr, avail, fuel, ⟨⟩⟩ m Q X
    ⟨cnfBytes, R, rfl, hfit, havel_fit, hav360, hm_in, hQfalse, hQtrue⟩
  have hav_le : avail.toNat ≤ 2 ^ 64 := by omega
  have hm0 : (bytes cnf_ptr cnfBytes ⋆ (region hdr_addr 32 ⋆
      region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32)) ⋆ R) m := by
    rw [region_merge_eq (a := hdr_addr) (n1 := 32) (n2 := avail.toNat - 32) (n := avail.toNat)
      (by omega) hav_le]; exact hm_in
  obtain ⟨m_d, m_o, hu, hd, h_d32, h_o⟩ := (show (region hdr_addr 32 ⋆ (bytes cnf_ptr cnfBytes ⋆
    region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32) ⋆ R)) m from sep_ac hm0)
  obtain ⟨mv0, nc0, cur0, val0, h_dstate⟩ := Kissat.region32_to_dimacsState h_d32
  have hm_pre : (dimacsState hdr_addr mv0 nc0 cur0 val0 ⋆ (bytes cnf_ptr cnfBytes ⋆
      region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32) ⋆ R)) m :=
    ⟨m_d, m_o, hu, hd, h_dstate, h_o⟩
  unfold Func.wp kissat_init_state_body; apply wp_call_of_spec; apply hHdr
  change kissatParseHeaderSpec (cnf_ptr, cnf_ptr + BitVec.ofNat 64 cnfBytes.length, hdr_addr, ())
    m _ _
  refine ⟨mv0, nc0, cur0, val0, cnfBytes,
    region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32) ⋆ R, rfl, hfit, sep_ac hm_pre, ?_⟩
  cases hhdr : parseHeader cnfBytes with
  | none =>
    intro _ _ _ _ m' hm'; refine wp_jnz_of (fun hc => by cases hc) (fun _ => ?_)
    rw [wp_ret]; exact hQfalse m' (init_hdr_remerge (by omega) hav_le (sep_ac hm'))
      (fun _ _ _ h => by rw [hhdr] at h; cases h)
  | some p =>
    rcases p with ⟨mv, nc, rest⟩; intro j m0 hmv_bd hnc_bd hj hdrop hm0
    have hmv := hmv_bd; have hnc := hnc_bd; unfold dimacsBound at hmv hnc
    refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
    cp_head_steps
    refine wp_join_group
      (fun (md_v, ()) m_md => md_v = BitVec.ofNat 64 (minDepthOf mv) ∧ m_md = m0) ?_ ?_
    · rintro _ ⟨md_v, ⟨⟩⟩ m_md ⟨rfl, hm_md⟩; subst m_md; simp only [Blocks.get_here]; cp_head_steps
      have hfx_eq := cp_fixed_bv_eq hmv_bd; have hfx_lt := cpFixedBytes_lt hmv_bd
      have hult_fx : avail.ult (BitVec.ofNat 64 (cpFixedBytes mv)) =
          decide (avail.toNat < cpFixedBytes mv) := by
        simpa [bv_ofNat_toNat_eq avail] using bv_ult_eq avail.isLt (by omega)
      refine wp_jnz_of (fun hlt => ?_) (fun hge => ?_)
      · rw [hfx_eq, hult_fx] at hlt; cp_jnz_t hlt
        exact init_hdr_fail (by omega) hav_le hhdr (by omega) (sep_ac hm0) hQfalse
      · rw [hfx_eq, hult_fx] at hge; cp_jnz_f hge
        have hrem_eq : avail - BitVec.ofNat 64 (cpFixedBytes mv) =
            BitVec.ofNat 64 (avail.toNat - cpFixedBytes mv) := by
          simpa [bv_ofNat_toNat_eq avail] using bv_sub_ofNat (by omega) avail.isLt
        let rem := avail.toNat - cpFixedBytes mv; have hrem64 : rem < 2 ^ 64 := by omega
        rw [hfx_eq, hrem_eq, cp_mul24, bv_ult_eq hrem64 (by omega)]
        refine wp_jnz_of (fun hlt2 => ?_) (fun hge2 => ?_)
        · cp_jnz_t hlt2; exact init_hdr_fail (by omega) hav_le hhdr (by omega) (sep_ac hm0) hQfalse
        · cp_jnz_f hge2
          refine wp_join_group
            (fun (mc_v, ()) m1 => mc_v = BitVec.ofNat 64 (cpInitMaxC nc rem) ∧ m1 = m0) ?_ ?_
          · rintro _ ⟨mc_v, ⟨⟩⟩ m1 ⟨rfl, hm1⟩; subst m1; simp only [Blocks.get_here]; cp_head_steps
            have hmc_le : cpInitMaxC nc rem * 24 ≤ rem := by unfold cpInitMaxC; omega
            refine wp_join_group
              (fun (lc_v, ()) m2 => lc_v = BitVec.ofNat 64 (cpInitLcap nc rem) ∧ m2 = m0) ?_ ?_
            · rintro _ ⟨lc_v, ⟨⟩⟩ m2 ⟨rfl, hm2⟩; subst m2; simp only [Blocks.get_here]
              let c : CorePlusCfg := ⟨hdr_addr, avail.toNat, mv, nc, cpInitMaxC nc rem,
                cpInitLcap nc rem, hmv_bd, hnc_bd, cpInitMaxC_lt, cpInitLcap_lt, havel_fit,
                cp_init_arena_fits (by omega)⟩
              obtain ⟨ws, arrs, hwl, hm_st⟩ := init_state_split_arena c fuel hav360 hm0
              clear hm_in hm_pre hm0; cp_head_steps
              exact init_state_finish_wp hZero arrs hhdr hj hdrop (init_hdrtail_norm c
                (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) fuel arrs ws hwl) hm hQtrue
            · intro J2 hJ2; cp_head_steps; rw [hrem_eq, cp_mul24, bv_sub_ofNat hmc_le hrem64,
                Kissat.bv_shr_sext2 (by omega), cp_ult_maxc_eq (by omega)]
              refine wp_jnz_of (fun hgt => ?_) (fun hle => ?_)
              · cp_jnz_t hgt; refine hJ2 ((268435455 : BitVec 64), ()) m0 ⟨?_, rfl⟩
                unfold cpInitLcap dimacsBound at *; rw [Nat.min_eq_right (by omega)]; rfl
              · cp_jnz_f hle; refine hJ2 (_, ()) m0 ⟨?_, rfl⟩
                rw [Kissat.bv_shr_sext2 (by omega)]; unfold cpInitLcap dimacsBound at *
                rw [Nat.min_eq_left (by omega)]
          · intro J1 hJ1; cp_head_steps; rw [hrem_eq, cp_mul24,
              bv_sub_ofNat (a := rem) (b := nc * 24) (by omega) hrem64,
              Kissat.bv_shr_sext6 (by omega), bv_add_ofNat, cp_ult_maxc_eq (by omega)]
            refine wp_jnz_of (fun hgt => ?_) (fun hle => ?_)
            · cp_jnz_t hgt; refine hJ1 ((268435455 : BitVec 64), ()) m0 ⟨?_, rfl⟩
              unfold cpInitMaxC dimacsBound at *; rw [Nat.min_eq_right (by omega)]; rfl
            · cp_jnz_f hle; refine hJ1 (_, ()) m0 ⟨?_, rfl⟩
              rw [bv_add_ofNat]; unfold cpInitMaxC dimacsBound at *; rw [Nat.min_eq_left (by omega)]
    · intro J hJ; cp_head_steps
      have hadd1 : BitVec.ofNat 64 mv + (1 : BitVec 64) = BitVec.ofNat 64 (mv + 1) := by
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
      rw [hadd1, show (1000 : BitVec 64) = BitVec.ofNat 64 1000 from rfl,
        bv_ult_eq (by omega) (by decide)]
      refine wp_jnz_of (fun hlt => ?_) (fun hge => ?_)
      · cp_jnz_t hlt; exact hJ (_, ()) m0 ⟨by rw [hadd1]; simp [minDepthOf, hlt], rfl⟩
      · cp_jnz_f hge; exact hJ (_, ()) m0 ⟨by simp [minDepthOf, hge], rfl⟩

end LeanQbe.T.Examples.Kissat.CorePlus
