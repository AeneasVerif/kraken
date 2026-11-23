module

public import LeanQbe.T.Examples.Kissat.SolverSpec
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Min` C0 Propagation `Func.wp` Proofs

Builds on `SolverSpec` to specify and verify:
1. `kissat_find_repl` (`kissatFindReplSpec`, `kissat_find_repl_wp`)
2. `kissat_propagate_lit` (`kissatPropagateLitSpec`, `kissat_propagate_lit_wp`)
3. `kissat_propagate` (`kissatPropagateSpec`, `kissat_propagate_wp`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open Kraken.Bedrock2.Test

/-! ## 1. Private arithmetic, memory-focusing, and invariant helpers -/

private theorem bv32_add1_ofNat (n : Nat) :
    BitVec.ofNat 32 n + 1 = BitVec.ofNat 32 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

private theorem bv64_toNat_pos_of_ne_zero {f : BitVec 64} (hf : f ≠ 0) : 0 < f.toNat :=
  Nat.pos_of_ne_zero fun h0 => hf (BitVec.eq_of_toNat_eq (by simpa using h0))

theorem bv64_sub1_toNat {f : BitVec 64} (hf : f ≠ 0) :
    (f - 1).toNat = f.toNat - 1 := by
  have hpos : 0 < f.toNat := bv64_toNat_pos_of_ne_zero hf
  have hlt := f.isLt
  have hsub := bv_sub_ofNat (a := f.toNat) (b := 1) (by omega) hlt
  rw [bv_ofNat_toNat_eq f] at hsub
  change (f - 1#64).toNat = f.toNat - 1
  rw [hsub, bv64_ofNat_toNat (by omega)]

private theorem bv32_zext64_ult_eq (x : BitVec 32) (n : BitVec 64) :
    (x.setWidth 64).ult n = decide (x.toNat < n.toNat) := by
  have hx : x.toNat < 2 ^ 64 := by have := x.isLt; omega
  have h := bv_ult_eq hx n.isLt
  rwa [← bv32_zext64_eq, bv_ofNat_toNat_eq] at h

private theorem bv32_zext64_ule_eq (n : BitVec 64) (x : BitVec 32) :
    n.ule (x.setWidth 64) = decide (n.toNat ≤ x.toNat) := by
  have hx : x.toNat < 2 ^ 64 := by have := x.isLt; omega
  have h := bv_ule_eq n.isLt hx
  rwa [bv_ofNat_toNat_eq, ← bv32_zext64_eq] at h

private theorem bv32_sle0_eq_not_slt0 (x : BitVec 32) :
    (0#32).sle x = !(x.slt 0#32) := by
  simp only [BitVec.sle, BitVec.slt]
  have h0 : (0#32).toInt = 0 := rfl
  rw [h0]
  by_cases h : x.toInt < 0
  · simp [h, show ¬ (0 ≤ x.toInt) by omega]
  · simp [h, show 0 ≤ x.toInt by omega]

private theorem bv32_slot_props (w : BitVec 32) :
    let slot := w &&& 1#32
    (slot.toNat = 0 ∨ slot.toNat = 1) ∧
    (slot ^^^ 1#32).toNat = 1 - slot.toNat ∧
    slot.toNat ≠ (slot ^^^ 1#32).toNat := by
  have h1 : (w &&& 1#32).toNat = w.toNat % 2 := bv32_and_1 w
  have h2 : ((w &&& 1#32) ^^^ 1#32).toNat = (w &&& 1#32).toNat ^^^ 1 := bv32_xor_1 (w &&& 1#32)
  have hcases : (w &&& 1#32).toNat = 0 ∨ (w &&& 1#32).toNat = 1 := by omega
  rcases hcases with h0 | h1'
  · refine ⟨Or.inl h0, ?_, ?_⟩ <;> rw [h2, h0] <;> decide
  · refine ⟨Or.inr h1', ?_, ?_⟩ <;> rw [h2, h1'] <;> decide

private theorem bv32_ult_toNat (a b : BitVec 32) :
    a.ult b = decide (a.toNat < b.toNat) := by
  simp [BitVec.ult]

private theorem ptr_add_mul4 (base : BitVec 64) (off k : Nat) :
    base + BitVec.ofNat 64 (4 * off) + BitVec.ofNat 64 (4 * k) =
      base + BitVec.ofNat 64 (4 * (off + k)) := by
  rw [ptr_add_ofNat, ← Nat.mul_add]

private theorem ptr_cls_add4 (base : BitVec 64) (cid : Nat) :
    base + BitVec.ofNat 64 (4 * (4 * cid)) + 4 =
      base + BitVec.ofNat 64 (4 * (4 * cid + 1)) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 (4 * 1) from rfl, ptr_add_mul4]

private theorem ptr_cls_add8 (base : BitVec 64) (cid : Nat) :
    base + BitVec.ofNat 64 (4 * (4 * cid)) + 8 =
      base + BitVec.ofNat 64 (4 * (4 * cid + 2)) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 (4 * 2) from rfl, ptr_add_mul4]

private theorem arenaMem_focus_vals_lpool_slice {c : ArenaCfg} {s : ArenaState}
    {R : Mem 64 → Prop} {m : Mem 64} {off sz : Nat}
    (h : off + sz ≤ s.lpool.length) (hm : (ArenaMem c s ⋆ R) m) :
    ∃ F : Mem 64 → Prop,
      (array (t := i8) c.pVals s.vals ⋆
        array (t := i32) (c.pLpool + BitVec.ofNat 64 (4 * off))
          ((s.lpool.drop off).take sz) ⋆ F) m := by
  unfold ArenaMem at hm
  rw [array_slice_focus (t := i32) c.pLpool s.lpool h] at hm
  change (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
    array64 (c.hdr + 32) (hdrTailWords c s) ⋆
    array (t := i8) c.pVals s.vals ⋆
    array (t := i8) c.pMark s.mrk ⋆
    array (t := i32) c.pLevel s.lvl ⋆
    array (t := i32) c.pReason s.rsns ⋆
    array (t := i32) c.pTrail s.trl ⋆
    array (t := i32) c.pTmp s.tmp ⋆
    array (t := i32) c.pWh s.wh ⋆
    array (t := i32) c.pClauses s.cls ⋆
    array (t := i32) c.pWn s.wn ⋆
    (array (t := i32) (c.pLpool + BitVec.ofNat 64 (4 * off)) ((s.lpool.drop off).take sz) ⋆
      (array (t := i32) c.pLpool (s.lpool.take off) ⋆
        array (t := i32) (c.pLpool + BitVec.ofNat 64 (4 * (off + sz)))
          (s.lpool.drop (off + sz)))) ⋆
    c.pad ⋆ R) m at hm
  refine ⟨dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
    array64 (c.hdr + 32) (hdrTailWords c s) ⋆
    array (t := i8) c.pMark s.mrk ⋆
    array (t := i32) c.pLevel s.lvl ⋆
    array (t := i32) c.pReason s.rsns ⋆
    array (t := i32) c.pTrail s.trl ⋆
    array (t := i32) c.pTmp s.tmp ⋆
    array (t := i32) c.pWh s.wh ⋆
    array (t := i32) c.pClauses s.cls ⋆
    array (t := i32) c.pWn s.wn ⋆
    array (t := i32) c.pLpool (s.lpool.take off) ⋆
    array (t := i32) (c.pLpool + BitVec.ofNat 64 (4 * (off + sz))) (s.lpool.drop (off + sz)) ⋆
    c.pad ⋆ R, sep_ac hm⟩

private theorem SolverInv.with_watches {c : ArenaCfg} {F0 : CNF Nat} {s : ArenaState}
    {wh' wn' : List (BitVec 32)} (hinv : SolverInv c F0 s)
    (hw : wh'.length = 2 * c.mv) (hwn : wn'.length = 2 * c.max_c) :
    SolverInv c F0 { s with wh := wh', wn := wn' } := by
  have hc := hinv.core
  have hl := hc.lengths
  refine ⟨⟨⟨hl.vals_len, hl.mrk_len, hl.lvl_len, hl.rsns_len, hl.trl_len, hl.tmp_len_arr,
      hw, hl.cls_len, hwn, hl.lpool_len, hl.lit_len_le, hl.num_clauses_le, hl.trail_end_le,
      hl.propagated_le, hl.cur_level_lt, hl.tmp_cnt_lt, hl.tmp_len_lt⟩,
    ⟨hc.clauses.bounds, hc.clauses.disjoint, hc.clauses.lits_lt, hc.clauses.entails⟩,
    hc.cur_level_le, hc.trail_lits_lt, hc.trail_vars_nodup, hc.vals_domain,
    hc.vals_true_iff, hc.vals_false_iff, hc.lvl_le, hc.trail_mono,
    hc.levels_inhabited, hc.level0_sound, hc.reason_inv⟩, hinv.marks⟩

private theorem SolverInv.with_fuel_prop {c : ArenaCfg} {F0 : CNF Nat} {s : ArenaState}
    {fuel' : BitVec 64} {prop' : Nat} (hinv : SolverInv c F0 s)
    (hp : prop' ≤ s.trail_end) :
    SolverInv c F0 { s with fuel := fuel', propagated := prop' } := by
  have hc := hinv.core
  have hl := hc.lengths
  refine ⟨⟨⟨hl.vals_len, hl.mrk_len, hl.lvl_len, hl.rsns_len, hl.trl_len, hl.tmp_len_arr,
      hl.wh_len, hl.cls_len, hl.wn_len, hl.lpool_len, hl.lit_len_le, hl.num_clauses_le,
      hl.trail_end_le, hp, hl.cur_level_lt, hl.tmp_cnt_lt, hl.tmp_len_lt⟩,
    ⟨hc.clauses.bounds, hc.clauses.disjoint, hc.clauses.lits_lt, hc.clauses.entails⟩,
    hc.cur_level_le, hc.trail_lits_lt, hc.trail_vars_nodup, hc.vals_domain,
    hc.vals_true_iff, hc.vals_false_iff, hc.lvl_le, hc.trail_mono,
    hc.levels_inhabited, hc.level0_sound, hc.reason_inv⟩, hinv.marks⟩

private theorem SolverInv.with_confl {c : ArenaCfg} {F0 : CNF Nat} {s : ArenaState}
    {cid' : BitVec 64} (hinv : SolverInv c F0 s) :
    SolverInv c F0 { s with confl_cid := cid' } := by
  have hc := hinv.core
  have hl := hc.lengths
  refine ⟨⟨⟨hl.vals_len, hl.mrk_len, hl.lvl_len, hl.rsns_len, hl.trl_len, hl.tmp_len_arr,
      hl.wh_len, hl.cls_len, hl.wn_len, hl.lpool_len, hl.lit_len_le, hl.num_clauses_le,
      hl.trail_end_le, hl.propagated_le, hl.cur_level_lt, hl.tmp_cnt_lt, hl.tmp_len_lt⟩,
    ⟨hc.clauses.bounds, hc.clauses.disjoint, hc.clauses.lits_lt, hc.clauses.entails⟩,
    hc.cur_level_le, hc.trail_lits_lt, hc.trail_vars_nodup, hc.vals_domain,
    hc.vals_true_iff, hc.vals_false_iff, hc.lvl_le, hc.trail_mono,
    hc.levels_inhabited, hc.level0_sound, hc.reason_inv⟩, hinv.marks⟩

private structure PropLoopInv (c : ArenaCfg) (F0 : CNF Nat) (s st : ArenaState)
    (not_lit : BitVec 32) : Prop where
  inv : SolverInv c F0 st
  d_cur : st.d_cur = s.d_cur
  d_val : st.d_val = s.d_val
  num_clauses : st.num_clauses = s.num_clauses
  lit_len : st.lit_len = s.lit_len
  cur_level : st.cur_level = s.cur_level
  fuel : st.fuel = s.fuel
  propagated : st.propagated = s.propagated
  trail_end_ge : s.trail_end ≤ st.trail_end
  not_false : st.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8

private theorem clause_falsified_of_find_repl_none {c : ArenaCfg} {F0 : CNF Nat} {st : ArenaState}
    {cid slot not_lit other : Nat} (hinv : SolverInv c F0 st) (hcid : cid < st.num_clauses)
    (hslot : slot = 0 ∨ slot = 1)
    (hbd : clauseOff st cid + clauseSize st cid ≤ st.lpool.length)
    (hsz2 : 2 ≤ clauseSize st cid)
    (hnot_at : (st.lpool[clauseOff st cid + slot]'(by omega)).toNat = not_lit)
    (hnot_false : st.vals[not_lit]?.getD 0#8 = 0xFF#8)
    (hother_at : (st.lpool[clauseOff st cid + (1 - slot)]'(by omega)).toNat = other)
    (hfind : ∀ k, 2 ≤ k → k < clauseSize st cid →
      let cand := (((st.lpool.drop (clauseOff st cid)).take (clauseSize st cid))[k]?.getD
        0#32).toNat
      2 * c.mv ≤ cand ∨ ((st.vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = true) :
    ∀ l ∈ clauseLits st cid, l = other ∨ st.vals[l]?.getD 0#8 = 0xFF#8 := by
  intro l hl
  obtain ⟨k, hk, hget⟩ := (mem_clauseLits_iff hbd).mp hl
  by_cases hko : k = 1 - slot
  · subst hko; exact Or.inl (hget.symm.trans hother_at)
  · by_cases hks : k = slot
    · subst hks; exact Or.inr (by rw [← hget, hnot_at]; exact hnot_false)
    · have hk2 : 2 ≤ k := by omega
      have hslice_lt :
          k < ((st.lpool.drop (clauseOff st cid)).take (clauseSize st cid)).length := by
        rw [List.length_take, List.length_drop]; omega
      have hcand_eq :
          (((st.lpool.drop (clauseOff st cid)).take (clauseSize st cid))[k]?.getD 0#32).toNat =
            l := by
        rw [List.getElem?_eq_getElem hslice_lt, Option.getD_some,
          List.getElem_take, List.getElem_drop]
        exact hget
      have hl_lt : l < 2 * c.mv := hinv.core.clauses.lits_lt cid hcid l hl
      have hf := hfind k hk2 hk
      dsimp only at hf
      rw [hcand_eq] at hf
      have hslt : ((st.vals[l]?.getD 0#8).signExtend 32).slt 0#32 = true :=
        hf.resolve_left (by omega)
      exact Or.inr ((i8_vals_slt0 (hinv.core.vals_domain l hl_lt)).mp hslt)

private theorem unit_assign_preserves_inv {c : ArenaCfg} {F0 : CNF Nat} {st : ArenaState}
    {cid other : BitVec 32} {not_lit : Nat}
    (hinv : SolverInv c F0 st) (hcid : cid.toNat < st.num_clauses)
    (hother_lt : other.toNat < 2 * c.mv) (hun : st.vals[other.toNat]?.getD 0#8 = 0#8)
    (hunit : ∀ l ∈ clauseLits st cid.toNat, l = other.toNat ∨ st.vals[l]?.getD 0#8 = 0xFF#8)
    (hnot_lt : not_lit < 2 * c.mv) (hnot_false : st.vals[not_lit]?.getD 0#8 = 0xFF#8) :
    let v := other.toNat / 2
    let st' : ArenaState :=
      { st with
        vals := (st.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
        lvl := st.lvl.set v (BitVec.ofNat 32 st.cur_level)
        rsns := st.rsns.set v cid
        trl := st.trl.set st.trail_end other
        trail_end := st.trail_end + 1 }
    SolverInv c F0 st' ∧ st'.vals[not_lit]?.getD 0#8 = 0xFF#8 := by
  intro v st'
  have hcore' : SolverCoreInv c F0 st' := by
    refine assign_preserves_core hinv.core hother_lt hun (by have := hinv.core.cur_level_le; omega)
      (fun L hL1 hLle => Or.inr (hinv.core.levels_inhabited L hL1 hLle)) ?_ ?_
    · intro hl0
      refine entails_of_mem_or_false (hinv.core.clauses.entails cid.toNat hcid) fun l hl => ?_
      rcases hunit l hl with rfl | hfl
      · exact Or.inl (by simp)
      · refine Or.inr ?_
        have hlt := hinv.core.clauses.lits_lt cid.toNat hcid l hl
        obtain ⟨i, hi, heq⟩ := (hinv.core.vals_false_iff l hlt).mp hfl
        have hli : (st.lvl[(st.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
          have := hinv.core.lvl_le i hi; omega
        have hs := hinv.core.level0_sound i hi hli
        rwa [heq] at hs
    · intro _
      refine ⟨hcid, fun q hq => ?_⟩
      rcases hunit q hq with rfl | hfq
      · exact Or.inl rfl
      · exact Or.inr ((hinv.core.vals_false_iff q
          (hinv.core.clauses.lits_lt cid.toNat hcid q hq)).mp hfq)
  refine ⟨⟨hcore', hinv.marks⟩, ?_⟩
  obtain ⟨i, hi, heq⟩ := (hinv.core.vals_false_iff not_lit hnot_lt).mp hnot_false
  refine (hcore'.vals_false_iff not_lit hnot_lt).mpr ⟨i, by dsimp [st']; omega, ?_⟩
  dsimp only [st']
  rw [List.getElem?_set_ne (by omega : st.trail_end ≠ i)]
  exact heq

private theorem swap_watch_preserves_inv {c : ArenaCfg} {F0 : CNF Nat} {st : ArenaState}
    {cid k1 k2 : Nat} {srch l1 l2 : BitVec 32} {wh' wn' : List (BitVec 32)}
    (hinv : SolverInv c F0 st) (hcid : cid < st.num_clauses)
    (hk1 : k1 < clauseSize st cid) (hk2 : k2 < clauseSize st cid)
    (hbd : clauseOff st cid + clauseSize st cid ≤ st.lpool.length)
    (hl1 : st.lpool[clauseOff st cid + k1]'(by omega) = l1)
    (hl2 : st.lpool[clauseOff st cid + k2]'(by omega) = l2)
    (hwl : wh'.length = 2 * c.mv) (hwnl : wn'.length = 2 * c.max_c) :
    SolverInv c F0
      { st with
        cls := st.cls.set (4 * cid + 2) srch
        lpool := (st.lpool.set (clauseOff st cid + k1) l2).set (clauseOff st cid + k2) l1
        wh := wh', wn := wn' } := by
  subst hl1; subst hl2
  exact ⟨swapClause_preserves_core hinv.core hcid hk1 hk2 hwl hwnl, hinv.marks⟩

/-! ## 2. `kissat_find_repl` specification and `Func.wp` proof -/

/-- Specification of `kissat_find_repl(vals, lits, sz, srch, n_lits)`. -/
def kissatFindReplSpec : Spec [i64, i64, i32, i32, i64] [i32] :=
  fun (vals_ptr, lits_ptr, sz, srch, n_lits, ()) m Q _ =>
    ∃ (vals : List (BitVec 8)) (lits : List (BitVec 32)) (R : Mem 64 → Prop),
      vals.length = n_lits.toNat ∧
      lits.length = sz.toNat ∧
      2 ≤ srch.toNat ∧ srch.toNat ≤ sz.toNat ∧
      (array (t := i8) vals_ptr vals ⋆ array (t := i32) lits_ptr lits ⋆ R) m ∧
      ∀ r : BitVec 32,
        ((r = 0xFFFFFFFF#32 ∧
          ∀ k, 2 ≤ k → k < sz.toNat →
            let cand := (lits[k]?.getD 0#32).toNat
            n_lits.toNat ≤ cand ∨
              ((vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = true) ∨
         (2 ≤ r.toNat ∧ r.toNat < sz.toNat ∧
          let cand := (lits[r.toNat]?.getD 0#32).toNat
          cand < n_lits.toNat ∧
            ((vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = false)) →
        Q (r, ()) m

theorem kissat_find_repl_wp (Γ : Env) :
    ∀ args m Q X, kissatFindReplSpec args m Q X →
      Func.wp Γ kissat_find_repl_body args m Q X := by
  rintro ⟨vals_ptr, lits_ptr, sz, srch, n_lits, ⟨⟩⟩ m Q X
    ⟨vals, lits, R, hvl, hll, hsrch2, hsrch_le, hm, hQ⟩
  unfold Func.wp kissat_find_repl_body; wp_unfold
  have hsz_lt : sz.toNat < 2 ^ 32 := sz.isLt
  have hsrch_lt : srch.toNat < 2 ^ 32 := srch.isLt
  have hload_lits : ∀ k (hk : k < sz.toNat),
      loadVal m i32 (lits_ptr + BitVec.ofNat 64 (4 * k)) =
        some (lits[k]'(by rw [hll]; exact hk)) := fun k hk =>
    loadVal_array (t := i32) (by decide) (by rw [hll]; exact hk)
      (sep_ac hm : (array (t := i32) lits_ptr lits ⋆ (array (t := i8) vals_ptr vals ⋆ R)) m)
  have hload_vals : ∀ k (hk : k < n_lits.toNat),
      loadVal m i8 (vals_ptr + BitVec.ofNat 64 k) =
        some (vals[k]'(by rw [hvl]; exact hk)) := fun k hk => by
    simpa [Ty.bytes, Ty.size, i8] using
      loadVal_array (t := i8) (by decide) (by rw [hvl]; exact hk)
        (sep_ac hm : (array (t := i8) vals_ptr vals ⋆ (array (t := i32) lits_ptr lits ⋆ R)) m)
  refine wp_loop_group
    (fun rem (rv, ()) ml => ∃ r : Nat,
      srch.toNat ≤ r ∧ r ≤ sz.toNat ∧ rem = sz.toNat - r ∧
      rv = BitVec.ofNat 32 r ∧ ml = m ∧
      ∀ k, srch.toNat ≤ k → k < r →
        let cand := (lits[k]?.getD 0#32).toNat
        n_lits.toNat ≤ cand ∨
          ((vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = true) ?_ ?_
  · rintro L rem ⟨rv, ⟨⟩⟩ ml ih ⟨r, hr_ge, hr_le, rfl, rfl, rfl, hseen1⟩
    wp_unfold
    rw [show sz = BitVec.ofNat 32 sz.toNat from (bv_ofNat_toNat_eq sz).symm,
      bv32_ult_eq (by omega) hsz_lt]
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun hr_lt => ?_, fun hr_ge_sz => ?_⟩
    · rw [bv32_mul4_eq, bv32_ofNat_toNat (by omega)]
      refine ⟨_, hload_lits r hr_lt, ?_⟩
      have hcand_get : (lits[r]?.getD 0#32).toNat = (lits[r]'(by rw [hll]; exact hr_lt)).toNat := by
        simp [List.getElem?_eq_getElem (by rw [hll]; exact hr_lt)]
      refine wp_join_group
        (fun () m' => m' = ml ∧
          (n_lits.toNat ≤ (lits[r]'(by rw [hll]; exact hr_lt)).toNat ∨
            ((vals[(lits[r]'(by rw [hll]; exact hr_lt)).toNat]?.getD 0#8).signExtend 32).slt
              0#32 = true)) ?_ ?_
      · rintro _ ⟨⟩ m' ⟨rfl, hfail⟩
        wp_unfold
        rw [bv32_add1_ofNat]
        refine ih (sz.toNat - (r + 1)) _ m' (by omega)
          ⟨r + 1, by omega, by omega, rfl, rfl, rfl, fun k hk1 hk2 => ?_⟩
        by_cases hkr : k = r
        · subst k; simpa [hcand_get] using hfail
        · exact hseen1 k hk1 (by omega)
      · intro J hJ; wp_unfold
        rw [bv32_zext64_ult_eq]
        simp only [decide_eq_true_eq, decide_eq_false_iff_not]
        refine ⟨fun hlt_n => ?_, fun hge_n => hJ () ml ⟨rfl, Or.inl (by omega)⟩⟩
        rw [bv32_zext64_eq]
        refine ⟨_, hload_vals _ hlt_n, ?_⟩
        have hval_get : vals[(lits[r]'(by rw [hll]; exact hr_lt)).toNat]?.getD 0#8 =
            vals[(lits[r]'(by rw [hll]; exact hr_lt)).toNat]'(by rw [hvl]; exact hlt_n) := by
          simp [List.getElem?_eq_getElem (by rw [hvl]; exact hlt_n)]
        rw [trunc32_8_zero, i8_sext32_zero, bv32_sle0_eq_not_slt0]
        cases hslt : ((vals[(lits[r]'(by rw [hll]; exact hr_lt)).toNat]'(by
            rw [hvl]; exact hlt_n)).signExtend 32).slt 0#32
        · simp only [Bool.not_false, true_implies, Bool.true_eq_false, false_implies, and_true]
          refine hQ (BitVec.ofNat 32 r) (Or.inr ?_)
          dsimp only
          rw [bv32_ofNat_toNat (by omega), hcand_get, hval_get]
          exact ⟨by omega, hr_lt, hlt_n, hslt⟩
        · simp only [Bool.not_true, Bool.false_eq_true, false_implies, true_implies, true_and]
          exact hJ () ml ⟨rfl, Or.inr (by rw [hval_get]; exact hslt)⟩
    · have hreq : r = sz.toNat := by omega
      subst hreq
      refine wp_loop_group
        (fun rem2 (rv2, ()) ml2 => ∃ r2 : Nat,
          2 ≤ r2 ∧ r2 ≤ srch.toNat ∧ rem2 = srch.toNat - r2 ∧
          rv2 = BitVec.ofNat 32 r2 ∧ ml2 = ml ∧
          ∀ k, 2 ≤ k → k < r2 →
            let cand := (lits[k]?.getD 0#32).toNat
            n_lits.toNat ≤ cand ∨
              ((vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = true) ?_ ?_
      · rintro L2 rem2 ⟨rv2, ⟨⟩⟩ ml2 ih2 ⟨r2, hr2_ge, hr2_le, rfl, rfl, rfl, hseen2⟩
        wp_unfold
        rw [show srch = BitVec.ofNat 32 srch.toNat from (bv_ofNat_toNat_eq srch).symm,
          bv32_ult_eq (by omega) hsrch_lt]
        simp only [decide_eq_true_eq, decide_eq_false_iff_not]
        refine ⟨fun hr2_lt => ?_, fun hr2_ge_srch => ?_⟩
        · have hr2_sz : r2 < sz.toNat := by omega
          rw [bv32_mul4_eq, bv32_ofNat_toNat (by omega)]
          refine ⟨_, hload_lits r2 hr2_sz, ?_⟩
          have hcand_get : (lits[r2]?.getD 0#32).toNat =
              (lits[r2]'(by rw [hll]; exact hr2_sz)).toNat := by
            simp [List.getElem?_eq_getElem (by rw [hll]; exact hr2_sz)]
          refine wp_join_group
            (fun () m' => m' = ml2 ∧
              (n_lits.toNat ≤ (lits[r2]'(by rw [hll]; exact hr2_sz)).toNat ∨
                ((vals[(lits[r2]'(by rw [hll]; exact hr2_sz)).toNat]?.getD 0#8).signExtend 32).slt
                  0#32 = true)) ?_ ?_
          · rintro _ ⟨⟩ m' ⟨rfl, hfail⟩
            wp_unfold
            rw [bv32_add1_ofNat]
            refine ih2 (srch.toNat - (r2 + 1)) _ m' (by omega)
              ⟨r2 + 1, by omega, by omega, rfl, rfl, rfl, fun k hk1 hk2 => ?_⟩
            by_cases hkr : k = r2
            · subst k; simpa [hcand_get] using hfail
            · exact hseen2 k hk1 (by omega)
          · intro J hJ; wp_unfold
            rw [bv32_zext64_ult_eq]
            simp only [decide_eq_true_eq, decide_eq_false_iff_not]
            refine ⟨fun hlt_n => ?_, fun hge_n => hJ () ml2 ⟨rfl, Or.inl (by omega)⟩⟩
            rw [bv32_zext64_eq]
            refine ⟨_, hload_vals _ hlt_n, ?_⟩
            have hval_get : vals[(lits[r2]'(by rw [hll]; exact hr2_sz)).toNat]?.getD 0#8 =
                vals[(lits[r2]'(by rw [hll]; exact hr2_sz)).toNat]'(by rw [hvl]; exact hlt_n) := by
              simp [List.getElem?_eq_getElem (by rw [hvl]; exact hlt_n)]
            rw [trunc32_8_zero, i8_sext32_zero, bv32_sle0_eq_not_slt0]
            cases hslt : ((vals[(lits[r2]'(by rw [hll]; exact hr2_sz)).toNat]'(by
                rw [hvl]; exact hlt_n)).signExtend 32).slt 0#32
            · simp only [Bool.not_false, true_implies, Bool.true_eq_false, false_implies, and_true]
              refine hQ (BitVec.ofNat 32 r2) (Or.inr ?_)
              dsimp only
              rw [bv32_ofNat_toNat (by omega), hcand_get, hval_get]
              exact ⟨hr2_ge, hr2_sz, hlt_n, hslt⟩
            · simp only [Bool.not_true, Bool.false_eq_true, false_implies, true_implies, true_and]
              exact hJ () ml2 ⟨rfl, Or.inr (by rw [hval_get]; exact hslt)⟩
        · have hr2eq : r2 = srch.toNat := by omega
          subst hr2eq
          refine hQ 0xFFFFFFFF#32 (Or.inl ⟨rfl, fun k hk2 hksz => ?_⟩)
          by_cases hks : k < srch.toNat
          · exact hseen2 k hk2 hks
          · exact hseen1 k (by omega) hksz
      · intro L2 hL2; wp_unfold
        exact hL2 (srch.toNat - 2) _ ml
          ⟨2, Nat.le_refl _, hsrch2, rfl, rfl, rfl, fun _ h1 h2 => by omega⟩
  · intro L hL; wp_unfold
    exact hL (sz.toNat - srch.toNat) _ m
      ⟨srch.toNat, Nat.le_refl _, hsrch_le, rfl, (bv_ofNat_toNat_eq srch).symm, rfl,
        fun _ h1 h2 => by omega⟩

/-! ## 3. `kissat_propagate_lit` specification and `Func.wp` proof -/

/-- Specification of `kissat_propagate_lit(h, lit)`. -/
def kissatPropagateLitSpec : Spec [i64, i32] [i64] :=
  fun (h, lit, ()) m Q _ =>
    ∃ (c : ArenaCfg) (F0 : CNF Nat) (s : ArenaState) (R : Mem 64 → Prop),
      h = c.hdr ∧ SolverInv c F0 s ∧ (ArenaMem c s ⋆ R) m ∧
      ∀ r s' m',
        SolverInv c F0 s' →
        s'.d_cur = s.d_cur →
        s'.d_val = s.d_val →
        s'.num_clauses = s.num_clauses →
        s'.lit_len = s.lit_len →
        s'.cur_level = s.cur_level →
        s'.fuel = s.fuel →
        s'.propagated = s.propagated →
        s.trail_end ≤ s'.trail_end →
        (r = 0xFFFFFFFF#64 ∨
          (r.toNat < s'.num_clauses ∧
            ∀ l ∈ clauseLits s' r.toNat, s'.vals[l]?.getD 0#8 = 0xFF#8)) →
        (s.wh[(lit ^^^ 1#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 →
          r = 0xFFFFFFFF#64 ∧ s' = s) →
        (ArenaMem c s' ⋆ R) m' →
        Q (r, ()) m'

theorem kissat_propagate_lit_wp (Γ : Env)
    (hFind : ∀ args m Q X, kissatFindReplSpec args m Q X →
      Γ "kissat_find_repl" [i64, i64, i32, i32, i64] [i32] args m Q X)
    (hAssign : ∀ args m Q X, kissatAssignSpec args m Q X →
      Γ "kissat_assign" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, kissatPropagateLitSpec args m Q X →
      Func.wp Γ kissat_propagate_lit_body args m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  unfold Func.wp kissat_propagate_lit_body; wp_unfold
  have hmv := c.hmv; have hmc := c.hmax_c; have hlc := c.hlcap
  unfold dimacsBound at hmv hmc hlc
  have hlen0 := hinv.core.lengths
  let not_lit : BitVec 32 := lit ^^^ 1#32
  have hnot_eq : lit ^^^ 1 = not_lit := rfl
  rw [hnot_eq]
  refine ⟨_, load_arena_mv hm, ?_⟩
  rw [bv_shl_sext1, bv32_zext64_ule_eq, bv64_ofNat_toNat (by omega)]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun hge => hQ 0xFFFFFFFF#64 s m hinv rfl rfl rfl rfl rfl rfl rfl (Nat.le_refl _)
      (Or.inl rfl) (fun _ => ⟨rfl, rfl⟩) hm, fun hnot_lt_n => ?_⟩
  have hnot_lt : not_lit.toNat < 2 * c.mv := by omega
  refine ⟨_, load_arena_watch_head hm, _, load_arena_watch_next hm,
    _, load_arena_clauses hm, _, load_arena_lit_pool hm, _, load_arena_values hm, ?_⟩
  rw [bv32_zext64_eq]
  refine ⟨_, load_arena_vals (by rw [hlen0.vals_len]; exact hnot_lt) hm, ?_⟩
  rw [trunc32_8_zero, i8_sext32_zero, bv32_sle0_eq_not_slt0]
  have hval_get0 : s.vals[not_lit.toNat]?.getD 0#8 =
      s.vals[not_lit.toNat]'(by rw [hlen0.vals_len]; exact hnot_lt) := by
    simp [List.getElem?_eq_getElem (by rw [hlen0.vals_len]; exact hnot_lt)]
  cases hslt0 : ((s.vals[not_lit.toNat]'(by rw [hlen0.vals_len]; exact hnot_lt)).signExtend 32).slt
      0#32
  · simp only [Bool.not_false, true_implies, Bool.true_eq_false, false_implies, and_true]
    exact hQ 0xFFFFFFFF#64 s m hinv rfl rfl rfl rfl rfl rfl rfl (Nat.le_refl _)
      (Or.inl rfl) (fun _ => ⟨rfl, rfl⟩) hm
  · simp only [Bool.not_true, Bool.false_eq_true, false_implies, true_implies, true_and]
    have hnot_false0 : s.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 := by
      have := (i8_vals_slt0 (hinv.core.vals_domain not_lit.toNat hnot_lt)).mp
        (by rw [hval_get0]; exact hslt0)
      exact this
    rw [bv64_mul4_nat]
    refine ⟨_, load_arena_wh (by rw [hlen0.wh_len]; exact hnot_lt) hm,
      _, load_arena_num_clauses hm, ?_⟩
    rw [bv_shl_sext1, ofNat_add_one]
    have hmax_steps64 : 2 * s.num_clauses + 1 < 2 ^ 64 := by
      have := hlen0.num_clauses_le; omega
    refine wp_loop_break_group
      (fun (_pv, _wv, _sv, ()) mb => ∃ st : ArenaState,
        PropLoopInv c F0 s st not_lit ∧
        (s.wh[not_lit.toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 → st = s) ∧
        (ArenaMem c st ⋆ R) mb)
      (fun rem (prev_v, w_v, steps_v, ()) ml => ∃ (steps : Nat) (st : ArenaState),
        steps ≤ 2 * s.num_clauses + 1 ∧
        rem = (2 * s.num_clauses + 1) - steps ∧
        steps_v = BitVec.ofNat 64 steps ∧
        (prev_v = 0xFFFFFFFF#32 ∨ prev_v.toNat < 2 * c.max_c) ∧
        PropLoopInv c F0 s st not_lit ∧
        (s.wh[not_lit.toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 →
          w_v = 0xFFFFFFFF#32 ∧ st = s) ∧
        (ArenaMem c st ⋆ R) ml) ?_ ?_ ?_
    · rintro _ ⟨_pv, _wv, _sv, ⟨⟩⟩ mb ⟨st, hpi, hwh_s, hmb⟩
      wp_unfold
      exact hQ 0xFFFFFFFF#64 st mb hpi.inv hpi.d_cur hpi.d_val hpi.num_clauses hpi.lit_len
        hpi.cur_level hpi.fuel hpi.propagated hpi.trail_end_ge (Or.inl rfl)
        (fun hE => ⟨rfl, hwh_s hE⟩) hmb
    · rintro B L rem ⟨prev_v, w_v, steps_v, ⟨⟩⟩ ml hB ih
        ⟨steps, st, hsteps_le, rfl, rfl, hprev_ok, hpi, hwh_s, hml⟩
      wp_unfold
      have hlen := hpi.inv.core.lengths
      refine ⟨fun hw_ne => ?_, fun hw_eq =>
        hB (prev_v, w_v, BitVec.ofNat 64 steps, ()) ml
          ⟨st, hpi, fun hE => (hwh_s hE).2, hml⟩⟩
      have hwh_ne : s.wh[not_lit.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 :=
        fun hE => hw_ne (hwh_s hE).1
      rw [bv_ult_eq (by omega) hmax_steps64]
      simp only [decide_eq_true_eq, decide_eq_false_iff_not]
      refine ⟨fun hsteps_lt => ?_, fun _ =>
        hB (prev_v, w_v, BitVec.ofNat 64 steps, ()) ml
          ⟨st, hpi, fun hE => absurd hE hwh_ne, hml⟩⟩
      rw [ofNat_add_one]
      let cid : BitVec 32 := w_v >>> 1
      let slot : BitVec 32 := w_v &&& 1#32
      have hcid_eq : w_v >>> 1 = cid := rfl
      have hslot_eq : w_v &&& 1 = slot := rfl
      have hcid_nat : cid.toNat = w_v.toNat / 2 := bv32_lshr_1 w_v
      have hslot_props := bv32_slot_props w_v
      have hslot_cases : slot.toNat = 0 ∨ slot.toNat = 1 := hslot_props.1
      have hslot_xor : (slot ^^^ 1#32).toNat = 1 - slot.toNat := hslot_props.2.1
      have hslot_ne : slot.toNat ≠ (slot ^^^ 1#32).toNat := hslot_props.2.2
      rw [hcid_eq, hslot_eq]
      refine ⟨_, load_arena_num_clauses hml, ?_⟩
      have hnc64 : st.num_clauses < 2 ^ 64 := by have := hlen.num_clauses_le; omega
      rw [bv32_zext64_ule_eq, bv64_ofNat_toNat hnc64]
      simp only [decide_eq_true_eq, decide_eq_false_iff_not]
      refine ⟨fun _ => hB (prev_v, w_v, BitVec.ofNat 64 (steps + 1), ()) ml
          ⟨st, hpi, fun hE => absurd hE hwh_ne, hml⟩, fun hcid_not_ge => ?_⟩
      have hcid_lt : cid.toNat < st.num_clauses := by omega
      have hcid_mc : cid.toNat < c.max_c := by have := hlen.num_clauses_le; omega
      have hw_lt : w_v.toNat < 2 * c.max_c := by omega
      rw [bv32_mul4_eq]
      refine ⟨_, load_arena_wn (by rw [hlen.wn_len]; exact hw_lt) hml, ?_⟩
      let next_w := st.wn[w_v.toNat]'(by rw [hlen.wn_len]; exact hw_lt)
      rw [bv32_mul16_eq, ptr_cls_add4]
      have hcls1_lt : 4 * cid.toNat + 1 < st.cls.length := by rw [hlen.cls_len]; omega
      have hcls0_lt : 4 * cid.toNat < st.cls.length := by rw [hlen.cls_len]; omega
      refine ⟨_, load_arena_cls hcls1_lt hml, _, load_arena_cls hcls0_lt hml, ?_⟩
      let sz := st.cls[4 * cid.toNat + 1]'hcls1_lt
      let off := st.cls[4 * cid.toNat]'hcls0_lt
      have hsz_eq : sz.toNat = clauseSize st cid.toNat := by
        unfold clauseSize
        rw [List.getElem?_eq_getElem hcls1_lt, Option.getD_some]
      have hoff_eq : off.toNat = clauseOff st cid.toNat := by
        unfold clauseOff
        rw [List.getElem?_eq_getElem hcls0_lt, Option.getD_some]
      have hcl_bd := hpi.inv.core.clauses.bounds cid.toNat hcid_lt
      have hsz_ge2 : 2 ≤ sz.toNat := by omega
      have hoff_sz_ll : off.toNat + sz.toNat ≤ st.lit_len := by omega
      have hll_lcap : st.lit_len ≤ c.lcap := hlen.lit_len_le
      have hbd_lpool : off.toNat + sz.toNat ≤ st.lpool.length := by rw [hlen.lpool_len]; omega
      have hll64 : st.lit_len < 2 ^ 64 := by omega
      -- Group 1: `bad_cl` evaluates to `false`
      refine wp_join_group (fun (b, ()) m1 => b = false ∧ ml = m1) ?_ ?_
      · rintro _ ⟨b, ⟨⟩⟩ m1 ⟨rfl, rfl⟩
        wp_unfold
        rw [bv32_mul4_eq]
        -- Group 2: stale-watch drop handler `Js_3`
        refine wp_join_group (fun () m2 => ml = m2) ?_ ?_
        · rintro _ ⟨⟩ m2 rfl
          wp_unfold
          -- Group 3: unlink `prev` (`wh[not_lit] = next_w` or `wn[prev] = next_w`)
          refine wp_join_group (fun () m3 => ∃ wh' wn',
              wh'.length = 2 * c.mv ∧ wn'.length = 2 * c.max_c ∧
              (ArenaMem c { st with wh := wh', wn := wn' } ⋆ R) m3) ?_ ?_
          · rintro _ ⟨⟩ m3 ⟨wh', wn', hwl', hwnl', hm3⟩
            wp_unfold
            rw [bv32_mul4_eq]
            obtain ⟨ok_wn, hm4⟩ := store_arena_wn (s := { st with wh := wh', wn := wn' })
              (i := w_v.toNat) 0xFFFFFFFF#32 (by simpa [hwnl'] using hw_lt) hm3
            refine ⟨ok_wn, ?_⟩
            let st' : ArenaState := { st with wh := wh', wn := wn'.set w_v.toNat 0xFFFFFFFF#32 }
            have hst'_inv : SolverInv c F0 st' :=
              hpi.inv.with_watches hwl' (by simp [hwnl'])
            refine ih ((2 * s.num_clauses + 1) - (steps + 1)) _ _ (by omega)
              ⟨steps + 1, st', by omega, rfl, rfl, hprev_ok,
                ⟨hst'_inv, hpi.d_cur, hpi.d_val, hpi.num_clauses, hpi.lit_len, hpi.cur_level,
                  hpi.fuel, hpi.propagated, hpi.trail_end_ge, hpi.not_false⟩,
                fun hE => absurd hE hwh_ne, hm4⟩
          · intro J3 hJ3; wp_unfold
            refine ⟨fun hprev_eq => ?_, fun hprev_ne => ?_⟩
            · rw [bv32_mul4_eq]
              obtain ⟨ok_wh, hm3⟩ := store_arena_wh (i := not_lit.toNat) next_w
                (by rw [hlen.wh_len]; exact hnot_lt) hml
              exact ⟨ok_wh, hJ3 () _ ⟨st.wh.set not_lit.toNat next_w, st.wn,
                by simp [hlen.wh_len], hlen.wn_len, hm3⟩⟩
            · have hprev_lt : prev_v.toNat < 2 * c.max_c := hprev_ok.resolve_left hprev_ne
              rw [bv32_mul4_eq]
              obtain ⟨ok_wn, hm3⟩ := store_arena_wn (i := prev_v.toNat) next_w
                (by rw [hlen.wn_len]; exact hprev_lt) hml
              exact ⟨ok_wn, hJ3 () _ ⟨st.wh, st.wn.set prev_v.toNat next_w,
                hlen.wh_len, by simp [hlen.wn_len], hm3⟩⟩
        · intro Jdrop hJdrop; wp_unfold
          -- Group 4: check `(lits[0] != not_lit && lits[1] != not_lit)` then `lits[slot]`
          refine wp_join_group (fun () m2 => ml = m2) ?_ ?_
          · rintro _ ⟨⟩ m2 rfl
            wp_unfold
            rw [bv32_mul4_eq, ptr_add_mul4]
            have hslot_lpool : off.toNat + slot.toNat < st.lpool.length := by omega
            refine ⟨_, load_arena_lpool hslot_lpool hml, ?_⟩
            refine ⟨fun _ => hJdrop () ml rfl, fun hslot_is_not => ?_⟩
            have hnot_at : st.lpool[off.toNat + slot.toNat]'hslot_lpool = not_lit := hslot_is_not
            rw [bv32_mul4_eq, ptr_add_mul4]
            have hother_idx : off.toNat + (slot ^^^ 1#32).toNat < st.lpool.length := by omega
            refine ⟨_, load_arena_lpool hother_idx hml, ?_⟩
            let other := st.lpool[off.toNat + (slot ^^^ 1#32).toNat]'hother_idx
            have hother_mem : other.toNat ∈ clauseLits st cid.toNat := by
              refine (mem_clauseLits_iff (by rw [← hoff_eq, ← hsz_eq]; exact hbd_lpool)).mpr ?_
              refine ⟨(slot ^^^ 1#32).toNat, by omega, ?_⟩
              simp only [other, ← hoff_eq]
            have hother_lt : other.toNat < 2 * c.mv :=
              hpi.inv.core.clauses.lits_lt cid.toNat hcid_lt other.toNat hother_mem
            rw [bv32_zext64_ule_eq, bv64_ofNat_toNat (by omega)]
            simp only [decide_eq_true_eq, decide_eq_false_iff_not]
            refine ⟨fun hge => by dsimp only [other] at hother_lt; omega, fun _ => ?_⟩
            rw [bv32_zext64_eq]
            have hoval_idx : other.toNat < st.vals.length := by rw [hlen.vals_len]; exact hother_lt
            refine ⟨_, load_arena_vals hoval_idx hml, ?_⟩
            let oval := st.vals[other.toNat]'hoval_idx
            have hoval_get : st.vals[other.toNat]?.getD 0#8 = oval := by
              simp [oval, List.getElem?_eq_getElem hoval_idx]
            have hoval_dom : oval = 0#8 ∨ oval = 1#8 ∨ oval = 0xFF#8 := by
              rw [← hoval_get]; exact hpi.inv.core.vals_domain other.toNat hother_lt
            rw [trunc32_8_zero, i8_sext32_zero]
            refine ⟨fun hgt0 => ?_, fun hnot_gt0 => ?_⟩
            · refine ih ((2 * s.num_clauses + 1) - (steps + 1)) _ ml (by omega)
                ⟨steps + 1, st, by omega, rfl, rfl, Or.inr hw_lt, hpi,
                  fun hE => absurd hE hwh_ne, hml⟩
            · have hoval_ne1 : oval ≠ 1#8 := fun h1 => by
                rw [(i8_vals_sgt0 hoval_dom).mpr h1] at hnot_gt0; cases hnot_gt0
              have hoval_0_or_ff : oval = 0#8 ∨ oval = 0xFF#8 := by
                rcases hoval_dom with h0 | h1 | hff
                · exact Or.inl h0
                · exact absurd h1 hoval_ne1
                · exact Or.inr hff
              rw [ptr_cls_add8]
              have hcls2_lt : 4 * cid.toNat + 2 < st.cls.length := by rw [hlen.cls_len]; omega
              refine ⟨_, load_arena_cls hcls2_lt hml, ?_⟩
              -- Group 5: clamp `srch` to `[2, sz]`
              refine wp_join_group
                (fun (srch', ()) m3 => ml = m3 ∧ 2 ≤ srch'.toNat ∧ srch'.toNat ≤ sz.toNat) ?_ ?_
              · rintro _ ⟨srch', ⟨⟩⟩ m3 ⟨rfl, hsrch2, hsrch_le⟩
                wp_unfold
                obtain ⟨F, hfocus⟩ := arenaMem_focus_vals_lpool_slice hbd_lpool hml
                apply wp_call_of_spec; apply hFind
                simp only [vals_cons, vals_nil, Arg.val_var]
                refine ⟨st.vals, (st.lpool.drop off.toNat).take sz.toNat, F,
                  by rw [hlen.vals_len, bv64_ofNat_toNat (by omega)],
                  by rw [List.length_take, List.length_drop]; dsimp only [sz] at *; omega,
                  hsrch2, hsrch_le, hfocus, fun r hr_post => ?_⟩
                wp_unfold
                refine ⟨fun hr_ne => ?_, fun hr_eq => ?_⟩
                · have hr_found : 2 ≤ r.toNat ∧ r.toNat < sz.toNat ∧
                      let cand := (((st.lpool.drop off.toNat).take sz.toNat)[r.toNat]?.getD
                        0#32).toNat
                      cand < (BitVec.ofNat 64 (2 * c.mv)).toNat ∧
                        ((st.vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = false := by
                    rcases hr_post with ⟨heq, _⟩ | hok
                    · exact absurd heq hr_ne
                    · exact hok
                  obtain ⟨hr2, hr_lt, hcand_lt, _⟩ := hr_found
                  have hr_lpool : off.toNat + r.toNat < st.lpool.length := by omega
                  have hrepl_lt : (st.lpool[off.toNat + r.toNat]'hr_lpool).toNat < 2 * c.mv := by
                    have hslice_lt :
                        r.toNat < ((st.lpool.drop off.toNat).take sz.toNat).length := by
                      rw [List.length_take, List.length_drop]; omega
                    rw [List.getElem?_eq_getElem hslice_lt, Option.getD_some,
                      List.getElem_take, List.getElem_drop,
                      bv64_ofNat_toNat (by omega)] at hcand_lt
                    exact hcand_lt
                  rw [bv32_mul4_eq, ptr_add_mul4]
                  refine ⟨_, load_arena_lpool hr_lpool hml, ?_⟩
                  let repl := st.lpool[off.toNat + r.toNat]'hr_lpool
                  rw [ptr_cls_add8]
                  obtain ⟨ok_s, hm_s⟩ := store_arena_cls (i := 4 * cid.toNat + 2) r hcls2_lt hml
                  refine ⟨ok_s, ?_⟩
                  rw [bv32_mul4_eq, ptr_add_mul4]
                  let st_s1 : ArenaState := { st with cls := st.cls.set (4 * cid.toNat + 2) r }
                  obtain ⟨ok_l1, hm_l1⟩ := store_arena_lpool (s := st_s1)
                    (i := off.toNat + slot.toNat) repl (by simpa [st_s1] using hslot_lpool) hm_s
                  refine ⟨ok_l1, ?_⟩
                  let st_s2 : ArenaState :=
                    { st_s1 with lpool := st.lpool.set (off.toNat + slot.toNat) repl }
                  obtain ⟨ok_l2, hm_l2⟩ := store_arena_lpool (s := st_s2)
                    (i := off.toNat + r.toNat) not_lit (by simp [st_s2]; exact hr_lpool) hm_l1
                  refine ⟨ok_l2, ?_⟩
                  let st_sw : ArenaState :=
                    { st_s2 with
                      lpool := (st.lpool.set (off.toNat + slot.toNat) repl).set
                        (off.toNat + r.toNat) not_lit }
                  -- Group 6: unlink `prev` before prepending to `wh[repl]`
                  refine wp_join_group (fun () m4 => ∃ wh' wn',
                      wh'.length = 2 * c.mv ∧ wn'.length = 2 * c.max_c ∧
                      (ArenaMem c { st_sw with wh := wh', wn := wn' } ⋆ R) m4) ?_ ?_
                  · rintro _ ⟨⟩ m4 ⟨wh', wn', hwl', hwnl', hm4⟩
                    wp_unfold
                    rw [bv32_mul4_eq, bv32_mul4_eq]
                    let st_u : ArenaState := { st_sw with wh := wh', wn := wn' }
                    refine ⟨_, load_arena_wh (s := st_u) (by simpa [st_u, hwl'] using hrepl_lt) hm4,
                      ?_⟩
                    obtain ⟨ok_wn2, hm5⟩ := store_arena_wn (s := st_u) (i := w_v.toNat)
                      (wh'[repl.toNat]'(by rw [hwl']; exact hrepl_lt))
                      (by simpa [st_u, hwnl'] using hw_lt) hm4
                    refine ⟨ok_wn2, ?_⟩
                    let st_u2 : ArenaState :=
                      { st_u with
                        wn := wn'.set w_v.toNat (wh'[repl.toNat]'(by rw [hwl']; exact hrepl_lt)) }
                    obtain ⟨ok_wh2, hm6⟩ := store_arena_wh (s := st_u2) (i := repl.toNat) w_v
                      (by simpa [st_u2, st_u, hwl'] using hrepl_lt) hm5
                    refine ⟨ok_wh2, ?_⟩
                    let wh_f := wh'.set repl.toNat w_v
                    let wn_f := wn'.set w_v.toNat (wh'[repl.toNat]'(by rw [hwl']; exact hrepl_lt))
                    have hsw_inv : SolverInv c F0 { st_u2 with wh := wh_f } := by
                      simpa only [← hoff_eq] using
                        swap_watch_preserves_inv (k1 := slot.toNat) (k2 := r.toNat)
                          (srch := r) (l1 := not_lit) (l2 := repl) (wh' := wh_f) (wn' := wn_f)
                          hpi.inv hcid_lt (by omega) (by omega)
                          (by rw [← hoff_eq, ← hsz_eq]; exact hbd_lpool)
                          (by simpa only [← hoff_eq] using hnot_at)
                          (by simp [repl, ← hoff_eq])
                          (by simp [wh_f, hwl']) (by simp [wn_f, hwnl'])
                    refine ih ((2 * s.num_clauses + 1) - (steps + 1)) _ _ (by omega)
                      ⟨steps + 1, { st_u2 with wh := wh_f }, by omega, rfl, rfl, hprev_ok,
                        ⟨hsw_inv, hpi.d_cur, hpi.d_val, hpi.num_clauses, hpi.lit_len,
                          hpi.cur_level, hpi.fuel, hpi.propagated, hpi.trail_end_ge,
                          hpi.not_false⟩,
                        fun hE => absurd hE hwh_ne, hm6⟩
                  · intro J6 hJ6; wp_unfold
                    refine ⟨fun hprev_eq => ?_, fun hprev_ne => ?_⟩
                    · rw [bv32_mul4_eq]
                      obtain ⟨ok_wh, hm4⟩ := store_arena_wh (s := st_sw) (i := not_lit.toNat)
                        next_w (by simpa [st_sw, st_s2, st_s1, hlen.wh_len] using hnot_lt) hm_l2
                      exact ⟨ok_wh, hJ6 () _ ⟨st.wh.set not_lit.toNat next_w, st.wn,
                        by simp [hlen.wh_len], hlen.wn_len, hm4⟩⟩
                    · have hprev_lt : prev_v.toNat < 2 * c.max_c := hprev_ok.resolve_left hprev_ne
                      rw [bv32_mul4_eq]
                      obtain ⟨ok_wn, hm4⟩ := store_arena_wn (s := st_sw) (i := prev_v.toNat)
                        next_w (by simpa [st_sw, st_s2, st_s1, hlen.wn_len] using hprev_lt) hm_l2
                      exact ⟨ok_wn, hJ6 () _ ⟨st.wh, st.wn.set prev_v.toNat next_w,
                        hlen.wh_len, by simp [hlen.wn_len], hm4⟩⟩
                · have hfind_none : ∀ k, 2 ≤ k → k < sz.toNat →
                      let cand := (((st.lpool.drop off.toNat).take sz.toNat)[k]?.getD 0#32).toNat
                      2 * c.mv ≤ cand ∨
                        ((st.vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = true := by
                    rcases hr_post with ⟨_, hall⟩ | ⟨_, hlt, _⟩
                    · intro k hk2 hksz
                      have h := hall k hk2 hksz
                      rwa [bv64_ofNat_toNat (by omega)] at h
                    · rw [hr_eq] at hlt
                      have hff : (4294967295 : BitVec 32).toNat = 4294967295 := rfl
                      have hsz_lt := (st.cls[4 * cid.toNat + 1]'hcls1_lt).isLt
                      omega
                  have hunit : ∀ l ∈ clauseLits st cid.toNat,
                      l = other.toNat ∨ st.vals[l]?.getD 0#8 = 0xFF#8 :=
                    clause_falsified_of_find_repl_none (slot := slot.toNat)
                      (not_lit := not_lit.toNat) (other := other.toNat)
                      hpi.inv hcid_lt hslot_cases
                      (by rw [← hoff_eq, ← hsz_eq]; exact hbd_lpool)
                      (by rw [← hsz_eq]; exact hsz_ge2)
                      (by simpa only [← hoff_eq] using congrArg BitVec.toNat hnot_at)
                      hpi.not_false
                      (by simp only [other, ← hoff_eq, ← hslot_xor])
                      (by simpa only [← hoff_eq, ← hsz_eq] using hfind_none)
                  rw [trunc32_8_zero, i8_sext32_zero]
                  refine ⟨fun hlt0 => ?_, fun hnot_lt0 => ?_⟩
                  · have hother_ff : st.vals[other.toNat]?.getD 0#8 = 0xFF#8 := by
                      rw [hoval_get]
                      exact (i8_vals_slt0 hoval_dom).mp hlt0
                    have hcid64_nat : (cid.setWidth 64).toNat = cid.toNat := by
                      rw [bv32_zext64_eq, bv64_ofNat_toNat (by have := cid.isLt; omega)]
                    refine hQ (cid.setWidth 64) st ml hpi.inv hpi.d_cur hpi.d_val hpi.num_clauses
                      hpi.lit_len hpi.cur_level hpi.fuel hpi.propagated hpi.trail_end_ge
                      (Or.inr ⟨by rw [hcid64_nat]; exact hcid_lt, fun l hl => ?_⟩)
                      (fun hE => absurd hE hwh_ne) hml
                    rw [hcid64_nat] at hl
                    rcases hunit l hl with rfl | hff
                    · exact hother_ff
                    · exact hff
                  · have hoval_eq0 : oval = 0#8 := by
                      rcases hoval_0_or_ff with h0 | hff
                      · exact h0
                      · rw [(i8_vals_slt0 hoval_dom).mpr hff] at hnot_lt0; cases hnot_lt0
                    have hother_un : st.vals[other.toNat]?.getD 0#8 = 0#8 := by
                      rw [hoval_get]; exact hoval_eq0
                    have hte_lt : st.trail_end < c.mv :=
                      hpi.inv.core.trail_end_lt_of_unassigned hother_lt hother_un
                    have hnot_guard : ¬ (c.mv ≤ other.toNat / 2 ∨ c.mv ≤ st.trail_end) := by omega
                    apply wp_call_of_spec; apply hAssign
                    simp only [vals_cons, vals_nil, Arg.val_var]
                    refine ⟨c, st, R, rfl, hlen, hml, ?_⟩
                    dsimp only [other] at hnot_guard
                    simp only [hnot_guard, ↓reduceIte]
                    intro m_as _ hm_as
                    wp_unfold
                    obtain ⟨hinv_as, hnot_as⟩ := unit_assign_preserves_inv hpi.inv hcid_lt hother_lt
                      hother_un hunit hnot_lt hpi.not_false
                    refine ih ((2 * s.num_clauses + 1) - (steps + 1)) _ m_as (by omega)
                      ⟨steps + 1, _, by omega, rfl, rfl, Or.inr hw_lt,
                        ⟨hinv_as, hpi.d_cur, hpi.d_val, hpi.num_clauses, hpi.lit_len,
                          hpi.cur_level, hpi.fuel, hpi.propagated,
                          by dsimp; have := hpi.trail_end_ge; omega, hnot_as⟩,
                        fun hE => absurd hE hwh_ne, hm_as⟩
              · intro J5 hJ5; wp_unfold
                rw [bv32_ult_toNat]
                simp only [decide_eq_true_eq, decide_eq_false_iff_not]
                have h2nat : (2 : BitVec 32).toNat = 2 := rfl
                refine ⟨fun _ => hJ5 (2#32, ()) ml ⟨rfl, by decide, hsz_ge2⟩, fun hge2 => ?_⟩
                rw [bv32_ult_toNat]
                simp only [decide_eq_true_eq, decide_eq_false_iff_not]
                exact ⟨fun _ => hJ5 (2#32, ()) ml ⟨rfl, by decide, hsz_ge2⟩,
                  fun hle => hJ5 (_, ()) ml ⟨rfl, by omega, by dsimp [sz] at *; omega⟩⟩
          · intro J4 hJ4; wp_unfold
            rw [show ((0 : BitVec 32).signExtend 64) * 4 = BitVec.ofNat 64 (4 * 0) from rfl,
              ptr_add_mul4, Nat.add_zero]
            refine ⟨_, load_arena_lpool (by omega : off.toNat < st.lpool.length) hml, ?_⟩
            refine ⟨fun _ => ?_, fun _ => hJ4 () ml rfl⟩
            rw [show ((1 : BitVec 32).signExtend 64) * 4 = BitVec.ofNat 64 (4 * 1) from rfl,
              ptr_add_mul4]
            refine ⟨_, load_arena_lpool (by omega : off.toNat + 1 < st.lpool.length) hml, ?_⟩
            exact ⟨fun _ => hJdrop () ml rfl, fun _ => hJ4 () ml rfl⟩
      · intro J1 hJ1; wp_unfold
        rw [bv32_ult_toNat]
        simp only [decide_eq_true_eq, decide_eq_false_iff_not]
        have h2nat : (2 : BitVec 32).toNat = 2 := rfl
        refine ⟨fun hlt2 => by dsimp only [sz] at hsz_ge2; omega, fun _ => ?_⟩
        refine ⟨_, load_arena_lit_len hml, ?_⟩
        rw [bv32_zext64_eq, bv_ult_eq hll64 (by have := off.isLt; omega)]
        simp only [decide_eq_true_eq, decide_eq_false_iff_not]
        refine ⟨fun hgt => by dsimp only [off] at hoff_sz_ll; omega, fun _ => ?_⟩
        refine ⟨_, load_arena_lit_len hml, ?_⟩
        rw [bv32_zext64_eq, bv_sub_ofNat (by dsimp only [off] at hoff_sz_ll; omega) hll64,
          bv_ult_eq (by omega) (by have := sz.isLt; omega)]
        simp only [decide_eq_true_eq, decide_eq_false_iff_not]
        exact ⟨fun hgt => by dsimp only [off, sz] at hoff_sz_ll; omega,
          fun _ => hJ1 (false, ()) ml ⟨rfl, rfl⟩⟩
    · intro B L _ hL; wp_unfold
      have hwh0_get : s.wh[not_lit.toNat]?.getD 0xFFFFFFFF#32 =
          s.wh[not_lit.toNat]'(by rw [hlen0.wh_len]; exact hnot_lt) := by
        simp [List.getElem?_eq_getElem (by rw [hlen0.wh_len]; exact hnot_lt)]
      exact hL (2 * s.num_clauses + 1) _ m
        ⟨0, s, by omega, by omega, rfl, Or.inl rfl,
          ⟨hinv, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, hnot_false0⟩,
          fun hE => ⟨by rw [← hwh0_get]; exact hE, rfl⟩, hm⟩

/-! ## 4. `kissat_propagate` specification and `Func.wp` proof -/

/-- Specification of `kissat_propagate(h)`. -/
def kissatPropagateSpec : Spec [i64] [i64] :=
  fun (h, ()) m Q _ =>
    ∃ (c : ArenaCfg) (F0 : CNF Nat) (s : ArenaState) (R : Mem 64 → Prop),
      h = c.hdr ∧ SolverInv c F0 s ∧ (ArenaMem c s ⋆ R) m ∧
      ∀ r s' m',
        SolverInv c F0 s' →
        s'.d_cur = s.d_cur →
        s'.d_val = s.d_val →
        s'.cur_level = s.cur_level →
        s'.fuel.toNat ≤ s.fuel.toNat →
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
        (r = 0#64 → s'.propagated = s'.trail_end) →
        (r = 1#64 →
          s'.fuel.toNat < s.fuel.toNat ∧
          s'.confl_cid.toNat < s'.num_clauses ∧
          ∀ l ∈ clauseLits s' s'.confl_cid.toNat, s'.vals[l]?.getD 0#8 = 0xFF#8) →
        ((∀ l < 2 * c.mv, s.wh[l]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) →
          s.trail_end - s.propagated ≤ s.fuel.toNat →
          r = 0#64 ∧ s'.vals = s.vals ∧ s'.trail_end = s.trail_end ∧
          s'.fuel.toNat = s.fuel.toNat - (s.trail_end - s.propagated)) →
        (ArenaMem c s' ⋆ R) m' →
        Q (r, ()) m'

theorem kissat_propagate_wp (Γ : Env)
    (hPropLit : ∀ args m Q X, kissatPropagateLitSpec args m Q X →
      Γ "kissat_propagate_lit" [i64, i32] [i64] args m Q X) :
    ∀ args m Q X, kissatPropagateSpec args m Q X →
      Func.wp Γ kissat_propagate_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  unfold Func.wp kissat_propagate_body; wp_unfold
  have hmv := c.hmv; unfold dimacsBound at hmv
  refine ⟨_, load_arena_trail hm, ?_⟩
  let EmptyWh := ∀ l < 2 * c.mv, s.wh[l]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
  refine wp_loop_group
    (fun rem () ml => ∃ st : ArenaState,
      rem = st.fuel.toNat ∧
      SolverInv c F0 st ∧
      st.d_cur = s.d_cur ∧ st.d_val = s.d_val ∧ st.cur_level = s.cur_level ∧
      st.fuel.toNat ≤ s.fuel.toNat ∧
      (EmptyWh →
        st.wh = s.wh ∧ st.vals = s.vals ∧ st.trail_end = s.trail_end ∧
        s.propagated ≤ st.propagated ∧
        st.fuel.toNat + (st.propagated - s.propagated) = s.fuel.toNat) ∧
      (ArenaMem c st ⋆ R) ml) ?_ ?_
  · rintro L rem ⟨⟩ ml ih ⟨st, rfl, hst_inv, hd1, hd2, hcl, hfuel_le, hempty, hml⟩
    wp_unfold
    have hlen := hst_inv.core.lengths
    have hpr64 : st.propagated < 2 ^ 64 := by
      have := hlen.propagated_le; have := hlen.trail_end_le; omega
    have hte64 : st.trail_end < 2 ^ 64 := by have := hlen.trail_end_le; omega
    refine ⟨_, load_arena_propagated hml, _, load_arena_trail_end hml, ?_⟩
    rw [bv_ult_eq hpr64 hte64]
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun hpr_lt => ?_, fun hpr_ge => ?_⟩
    · refine ⟨_, load_arena_fuel hml, ?_⟩
      refine ⟨fun hfuel0 => ?_, fun hfuel_ne => ?_⟩
      · refine hQ 2#64 st ml hst_inv hd1 hd2 hcl hfuel_le (Or.inr (Or.inr rfl))
          (fun h => by cases h) (fun h => by cases h) ?_ hml
        intro hE hle
        obtain ⟨_, _, hte_eq, hpr_ge_s, hsum⟩ := hempty hE
        have hfz : st.fuel.toNat = 0 := by rw [hfuel0]; rfl
        omega
      · have hfuel_sub : (st.fuel - 1).toNat = st.fuel.toNat - 1 := bv64_sub1_toNat hfuel_ne
        have hfuel_pos : 0 < st.fuel.toNat := bv64_toNat_pos_of_ne_zero hfuel_ne
        refine ⟨_, load_arena_fuel hml, ?_⟩
        obtain ⟨ok1, hm1⟩ := store_arena_fuel (st.fuel - 1) hml
        refine ⟨ok1, _, load_arena_propagated hm1, ?_⟩
        rw [bv64_mul4_nat]
        have htrl_lt : st.propagated < st.trl.length := by
          rw [hlen.trl_len]; have := hlen.trail_end_le; omega
        refine ⟨_, load_arena_trl (s := { st with fuel := st.fuel - 1 }) htrl_lt hm1,
          _, load_arena_propagated hm1, ?_⟩
        rw [ofNat_add_one]
        obtain ⟨ok2, hm2⟩ := store_arena_propagated (st.propagated + 1) hm1
        refine ⟨ok2, ?_⟩
        let lit := st.trl[st.propagated]'htrl_lt
        let st1 : ArenaState := { st with fuel := st.fuel - 1, propagated := st.propagated + 1 }
        have hst1_inv : SolverInv c F0 st1 := hst_inv.with_fuel_prop (by omega)
        have hlit_lt : lit.toNat < 2 * c.mv := by
          have := hst_inv.core.trail_lits_lt st.propagated hpr_lt
          rwa [List.getElem?_eq_getElem htrl_lt, Option.getD_some] at this
        have hnlit_lt : (lit ^^^ 1#32).toNat < 2 * c.mv := by
          simpa [BitVec.toNat_xor] using litNeg_lt_two_mul hlit_lt
        apply wp_call_of_spec; apply hPropLit
        refine ⟨c, F0, st1, R, rfl, hst1_inv, hm2,
          fun confl st2 m2 hst2_inv hd1' hd2' _ _ hcl' hfuel' hpr' _ hconfl hwh_none hm2' => ?_⟩
        wp_unfold
        refine ⟨fun hne_c => ?_, fun heq_c => ?_⟩
        · obtain ⟨ok3, hm3⟩ := store_arena_confl_cid confl hm2'
          refine ⟨ok3, ?_⟩
          let st3 : ArenaState := { st2 with confl_cid := confl }
          have hconfl_ok : confl.toNat < st2.num_clauses ∧
              ∀ l ∈ clauseLits st2 confl.toNat, st2.vals[l]?.getD 0#8 = 0xFF#8 :=
            hconfl.resolve_left hne_c
          refine hQ 1#64 st3 _ hst2_inv.with_confl (hd1'.trans hd1) (hd2'.trans hd2)
            (hcl'.trans hcl) (by dsimp [st3]; rw [hfuel']; dsimp [st1]; omega)
            (Or.inr (Or.inl rfl)) (fun h => by cases h)
            (fun _ => ⟨by dsimp [st3]; rw [hfuel']; dsimp [st1]; omega,
              hconfl_ok.1, hconfl_ok.2⟩) ?_ hm3
          intro hE _
          obtain ⟨hwh_eq, _, _, _, _⟩ := hempty hE
          have hwh_st1 : st1.wh[(lit ^^^ 1#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
            dsimp [st1]; rw [hwh_eq]; exact hE _ hnlit_lt
          exact absurd (hwh_none hwh_st1).1 hne_c
        · refine ih st2.fuel.toNat () m2 (by rw [hfuel']; dsimp [st1]; omega)
            ⟨st2, rfl, hst2_inv, hd1'.trans hd1, hd2'.trans hd2, hcl'.trans hcl,
              by rw [hfuel']; dsimp [st1]; omega, ?_, hm2'⟩
          intro hE
          obtain ⟨hwh_eq, hvals_eq, hte_eq, hpr_ge_s, hsum⟩ := hempty hE
          have hwh_st1 : st1.wh[(lit ^^^ 1#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
            dsimp [st1]; rw [hwh_eq]; exact hE _ hnlit_lt
          have hst2_eq : st2 = st1 := (hwh_none hwh_st1).2
          rw [hst2_eq]
          dsimp [st1]
          exact ⟨hwh_eq, hvals_eq, hte_eq, by omega, by omega⟩
    · have hpr_eq : st.propagated = st.trail_end := by have := hlen.propagated_le; omega
      refine hQ 0#64 st ml hst_inv hd1 hd2 hcl hfuel_le (Or.inl rfl)
        (fun _ => hpr_eq) (fun h => by cases h) ?_ hml
      intro hE hle
      obtain ⟨_, hvals_eq, hte_eq, hpr_ge_s, hsum⟩ := hempty hE
      exact ⟨rfl, hvals_eq, hte_eq, by omega⟩
  · intro L hL; wp_unfold
    exact hL s.fuel.toNat () m
      ⟨s, rfl, hinv, rfl, rfl, rfl, Nat.le_refl _,
        fun _ => ⟨rfl, rfl, rfl, Nat.le_refl _, by omega⟩, hm⟩

end LeanQbe.T.Examples.Kissat
