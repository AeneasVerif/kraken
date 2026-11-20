module

public import LeanQbe.T.Examples.Kissat.CorePlusSpec
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Core+` BCP `Func.wp` Proofs (`Stage 2`, Wave 1b)

Builds directly on `CorePlusSpec` (using `C0Step` tactics and `@[c0_load]`/`@[c0_store]` helpers
from `CorePlusArena`) to verify:
1. `kissat_find_repl` (`kissat_find_repl_wp` → `corePlusFindReplSpec`)
2. `kissat_propagate_lit` (`kissat_propagate_lit_wp` → `corePlusPropagateLitSpec`)
3. `kissat_propagate` (`kissat_propagate_wp` → `corePlusPropagateSpec`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.CorePlus

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
  LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test

/-! ## 1. Arithmetic, memory-access, framing, and invariant helpers -/

private theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
private theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
private theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

local macro "cp_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)
local macro "cp_unmdata" : tactic =>
  `(tactic| first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)
local macro "cp_step" : tactic => `(tactic| ((try cp_unmdata); (repeat cp_strip); c0_step))
local macro "cp_steps" : tactic =>
  `(tactic| (
      (try cp_unmdata)
      (repeat cp_strip)
      c0_steps
      repeat (any_goals (cp_strip; repeat cp_strip); c0_steps)))

attribute [local bv_c0 high] bv_c0_zext32_64
attribute [local bv_c0] bv32_lshr_1 bv32_and_1 List.length_set Bool.false_eq_true

@[local bv_c0] private theorem bv64_shl1_nat (x : BitVec 64) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
@[local bv_c0] private theorem bv32_and1_xor1 (x : BitVec 32) :
    ((x &&& (1 : BitVec 32)) ^^^ (1 : BitVec 32)).toNat = 1 - x.toNat % 2 := by
  have h1 : (x &&& (1 : BitVec 32)).toNat = x.toNat % 2 := bv32_and_1 x
  have h2 : ((x &&& (1 : BitVec 32)) ^^^ (1 : BitVec 32)).toNat =
      (x &&& (1 : BitVec 32)).toNat ^^^ 1 := bv32_xor_1 (x &&& (1 : BitVec 32))
  rcases (by omega : x.toNat % 2 = 0 ∨ x.toNat % 2 = 1) with he | he <;> rw [h2, h1, he] <;> decide

private theorem bv32_sle0_eq_not_slt0 (x : BitVec 32) : (0#32).sle x = !(x.slt 0#32) := by
  simp only [BitVec.sle, BitVec.slt]; change decide (0 ≤ x.toInt) = !decide (x.toInt < 0)
  by_cases h : x.toInt < 0 <;> simp [h, show (0 ≤ x.toInt) ↔ ¬(x.toInt < 0) by omega]

private theorem ptr_cls_idx (a cid : BitVec 64) (d : Nat) :
    a + cid * 16 + BitVec.ofNat 64 (4 * d) = a + BitVec.ofNat 64 (4 * (4 * cid.toNat + d)) := by
  rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, c0_mul_ofNat, ptr_add_ofNat]
  congr 1; exact congrArg (BitVec.ofNat 64) (by omega)

section LocalMem
variable {c : CorePlusCfg} {s : CorePlusState} {R : Mem 64 → Prop} {m : Mem 64}

private theorem c0_load_cls_off {cid : BitVec 64} (hi : 4 * cid.toNat < s.cls.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pClauses + cid * 16) = some s.cls[4 * cid.toNat] := by
  rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, c0_mul_ofNat,
    show 16 * cid.toNat = 4 * (4 * cid.toNat) by omega]; exact load_arena_cls hi hm

private theorem c0_load_cls_size {cid : BitVec 64} (hi : 4 * cid.toNat + 1 < s.cls.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pClauses + cid * 16 + 4) = some s.cls[4 * cid.toNat + 1] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 (4 * 1) from rfl, ptr_cls_idx]
  exact load_arena_cls hi hm

private theorem c0_load_cls_srch {cid : BitVec 64} (hi : 4 * cid.toNat + 2 < s.cls.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pClauses + cid * 16 + 8) = some s.cls[4 * cid.toNat + 2] := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 (4 * 2) from rfl, ptr_cls_idx]
  exact load_arena_cls hi hm

private theorem c0_store_cls_srch {cid : BitVec 64} (v : BitVec 32)
    (hi : 4 * cid.toNat + 2 < s.cls.length) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i32 (c.pClauses + cid * 16 + 8) ∧
      (CorePlusMem c { s with cls := s.cls.set (4 * cid.toNat + 2) v } ⋆ R)
        (storeMem m i32 (c.pClauses + cid * 16 + 8) v) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 (4 * 2) from rfl, ptr_cls_idx]
  exact store_arena_cls v hi hm

private theorem c0_load_lpool_off {off k : BitVec 64} (hi : off.toNat + k.toNat < s.lpool.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pLpool + off * 4 + k * 4) = some s.lpool[off.toNat + k.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_ptr_off_mul]
  exact load_arena_lpool hi hm

private theorem c0_load_lpool_off0 {off : BitVec 64} (hi : off.toNat < s.lpool.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pLpool + off * 4 + 0#64) = some s.lpool[off.toNat] := by
  simpa using c0_load_lpool_off (off := off) (k := 0) (by simpa using hi) hm

private theorem c0_load_lpool_off1 {off : BitVec 64} (hi : off.toNat + 1 < s.lpool.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pLpool + off * 4 + 4#64) = some s.lpool[off.toNat + 1] := by
  simpa using c0_load_lpool_off (off := off) (k := 1) (by simpa using hi) hm

private theorem c0_store_lpool_off {off k : BitVec 64} (v : BitVec 32)
    (hi : off.toNat + k.toNat < s.lpool.length) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i32 (c.pLpool + off * 4 + k * 4) ∧
      (CorePlusMem c { s with lpool := s.lpool.set (off.toNat + k.toNat) v } ⋆ R)
        (storeMem m i32 (c.pLpool + off * 4 + k * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_ptr_off_mul]
  exact store_arena_lpool v hi hm

end LocalMem

attribute [local c0_load] c0_load_cls_off c0_load_cls_size c0_load_cls_srch
  c0_load_lpool_off c0_load_lpool_off0 c0_load_lpool_off1
attribute [local c0_store] c0_store_cls_srch c0_store_lpool_off

private theorem corePlusMem_focus_vals_lpool {c : CorePlusCfg} {s : CorePlusState}
    {R : Mem 64 → Prop} {m : Mem 64} {off sz : Nat} (h : off + sz ≤ s.lpool.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    ∃ F, (array (t := i8) c.pVals s.vals ⋆ array (t := i32) (c.pLpool + BitVec.ofNat 64 (4 * off))
      ((s.lpool.drop off).take sz) ⋆ F) m := by
  unfold CorePlusMem CoreArrays at hm
  rw [array_slice_focus (t := i32) c.pLpool s.lpool h, show i32.bytes = 4 from rfl] at hm
  exact ⟨_, by ecancel⟩

private abbrev propLitMask (t : CorePlusState) : CorePlusState :=
  { t with vals := [], lvl := [], rsns := [], trl := [], trail_end := 0, wh := [], wn := [],
           cls := [], lpool := [], heur := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, [], [], [], []⟩ }

private theorem propLit_eq_upd {s st : CorePlusState} (h : AgreesExcept propLitMask s st) :
    st = { s with
      vals := st.vals, lvl := st.lvl, rsns := st.rsns, trl := st.trl, trail_end := st.trail_end,
      wh := st.wh, wn := st.wn, cls := st.cls, lpool := st.lpool, heur := st.heur } := by
  cases s; cases st; cases h; rfl

private abbrev propMask (t : CorePlusState) : CorePlusState :=
  { propLitMask t with propagated := 0, fuel := 0, confl_cid := 0 }

private theorem prop_eq_upd {s st : CorePlusState} (h : AgreesExcept propMask s st) :
    st = { s with
      vals := st.vals, lvl := st.lvl, rsns := st.rsns, trl := st.trl, trail_end := st.trail_end,
      propagated := st.propagated, wh := st.wh, wn := st.wn, cls := st.cls, lpool := st.lpool,
      fuel := st.fuel, confl_cid := st.confl_cid, heur := st.heur } := by
  cases s; cases st; cases h; rfl

private theorem CorePlusInv.with_watches {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {wh' wn' : List (BitVec 32)} (h : CorePlusInv c F0 s)
    (hw : wh'.length = 2 * c.mv) (hwn : wn'.length = 2 * c.max_c) :
    CorePlusInv c F0 { s with wh := wh', wn := wn' } :=
  ⟨{ h.core with lengths := { h.core.lengths with wh_len := hw, wn_len := hwn },
                 clauses := { h.core.clauses with bounds := h.core.clauses.bounds } }, h.marks⟩

private theorem CorePlusInv.with_fuel_prop {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {fuel' : BitVec 64} {prop' : Nat} (h : CorePlusInv c F0 s) (hp : prop' ≤ s.trail_end) :
    CorePlusInv c F0 { s with fuel := fuel', propagated := prop' } :=
  ⟨{ h.core with lengths := { h.core.lengths with propagated_le := hp },
                 clauses := { h.core.clauses with bounds := h.core.clauses.bounds } }, h.marks⟩

private theorem CorePlusInv.with_confl {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {cid' : BitVec 64} (h : CorePlusInv c F0 s) : CorePlusInv c F0 { s with confl_cid := cid' } :=
  ⟨{ h.core with lengths := { h.core.lengths with vals_len := h.core.lengths.vals_len },
                 clauses := { h.core.clauses with bounds := h.core.clauses.bounds } }, h.marks⟩

private theorem clause_falsified_of_find_repl_none {c : CorePlusCfg} {F0 : CNF Nat}
    {st : CorePlusState} {cid slot not_lit other : Nat}
    (hinv : CorePlusInv c F0 st) (hcid : cid < st.num_clauses) (hslot : slot = 0 ∨ slot = 1)
    (hbd : clauseOff st cid + clauseSize st cid ≤ st.lpool.length) (hsz2 : 2 ≤ clauseSize st cid)
    (hnot_at : (st.lpool[clauseOff st cid + slot]'(by omega)).toNat = not_lit)
    (hnot_false : st.vals[not_lit]?.getD 0#8 = 0xFF#8)
    (hother_at : (st.lpool[clauseOff st cid + (1 - slot)]'(by omega)).toNat = other)
    (hfind : ∀ k, 2 ≤ k → k < clauseSize st cid →
      let cand := (((st.lpool.drop (clauseOff st cid)).take (clauseSize st cid))[k]?.getD
        0#32).toNat
      2 * c.mv ≤ cand ∨ ((st.vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = true) :
    ∀ l ∈ clauseLits st cid, l = other ∨ st.vals[l]?.getD 0#8 = 0xFF#8 := by
  intro l hl; obtain ⟨k, hk, hget⟩ := (mem_clauseLits_iff hbd).mp hl
  by_cases hko : k = 1 - slot
  · subst hko; exact Or.inl (hget.symm.trans hother_at)
  · by_cases hks : k = slot
    · subst hks; exact Or.inr (by rw [← hget, hnot_at]; exact hnot_false)
    · have hsl : k < ((st.lpool.drop (clauseOff st cid)).take (clauseSize st cid)).length := by
        rw [List.length_take, List.length_drop]; omega
      have hcand : (((st.lpool.drop (clauseOff st cid)).take (clauseSize st cid))[k]?.getD
          0#32).toNat = l := by
        rw [List.getElem?_eq_getElem hsl, Option.getD_some, List.getElem_take, List.getElem_drop]
        exact hget
      have hl_lt := hinv.core.clauses.lits_lt cid hcid l hl
      have hf := hfind k (by omega) hk; dsimp only at hf; rw [hcand] at hf
      exact Or.inr ((i8_vals_slt0 (hinv.core.vals_domain l hl_lt)).mp (hf.resolve_left (by omega)))

private theorem unit_assign_preserves_inv {c : CorePlusCfg} {F0 : CNF Nat} {st : CorePlusState}
    {cid other : BitVec 32} {phases' : List (BitVec 8)} {not_lit : Nat}
    (hinv : CorePlusInv c F0 st) (hcid : cid.toNat < st.num_clauses)
    (hother_lt : other.toNat < 2 * c.mv) (hph : phases'.length = c.mv)
    (hun : st.vals[other.toNat]?.getD 0#8 = 0#8)
    (hunit : ∀ l ∈ clauseLits st cid.toNat, l = other.toNat ∨ st.vals[l]?.getD 0#8 = 0xFF#8)
    (hnot_lt : not_lit < 2 * c.mv) (hnot_false : st.vals[not_lit]?.getD 0#8 = 0xFF#8) :
    let v := other.toNat / 2
    let st' : CorePlusState :=
      { st with vals := (st.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8,
                lvl := st.lvl.set v (BitVec.ofNat 32 st.cur_level), rsns := st.rsns.set v cid,
                trl := st.trl.set st.trail_end other, trail_end := st.trail_end + 1,
                heur := { st.heur with phases := phases' } }
    CorePlusInv c F0 st' ∧ st'.vals[not_lit]?.getD 0#8 = 0xFF#8 := by
  intro v st'
  have hcore' : CorePlusCoreInv c F0 st' := by
    refine assign_preserves_core hinv.core hother_lt hph hun
      (by have := hinv.core.cur_level_le; omega)
      (fun L hL1 hLle => Or.inr (hinv.core.levels_inhabited L hL1 hLle)) ?_ ?_
    · intro hl0
      refine entails_of_mem_or_false (hinv.core.clauses.entails cid.toNat hcid) fun l hl => ?_
      rcases hunit l hl with rfl | hfl
      · exact Or.inl (by simp)
      · obtain ⟨i, hi, heq⟩ :=
          (hinv.core.vals_false_iff l (hinv.core.clauses.lits_lt cid.toNat hcid l hl)).mp hfl
        have hli : (st.lvl[(st.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
          have := hinv.core.lvl_le i hi; omega
        have hs := hinv.core.level0_sound i hi hli; refine Or.inr ?_; rwa [heq] at hs
    · exact fun _ => ⟨hcid, fun q hq => (hunit q hq).elim Or.inl fun hfq => Or.inr
        ((hinv.core.vals_false_iff q (hinv.core.clauses.lits_lt cid.toNat hcid q hq)).mp hfq)⟩
  refine ⟨⟨hcore', hinv.marks⟩, ?_⟩
  obtain ⟨i, hi, heq⟩ := (hinv.core.vals_false_iff not_lit hnot_lt).mp hnot_false
  refine (hcore'.vals_false_iff not_lit hnot_lt).mpr ⟨i, by dsimp [st']; omega, ?_⟩
  dsimp only [st']; rw [List.getElem?_set_ne (by omega : st.trail_end ≠ i)]; exact heq

private theorem swap_watch_preserves_inv {c : CorePlusCfg} {F0 : CNF Nat} {st : CorePlusState}
    {cid k1 k2 : Nat} {srch l1 l2 : BitVec 32} {wh' wn' : List (BitVec 32)}
    (hinv : CorePlusInv c F0 st) (hcid : cid < st.num_clauses)
    (hk1 : k1 < clauseSize st cid) (hk2 : k2 < clauseSize st cid)
    (hbd : clauseOff st cid + clauseSize st cid ≤ st.lpool.length)
    (hl1 : st.lpool[clauseOff st cid + k1]'(by omega) = l1)
    (hl2 : st.lpool[clauseOff st cid + k2]'(by omega) = l2)
    (hwl : wh'.length = 2 * c.mv) (hwnl : wn'.length = 2 * c.max_c) :
    CorePlusInv c F0 { st with
      cls := st.cls.set (4 * cid + 2) srch,
      lpool := (st.lpool.set (clauseOff st cid + k1) l2).set (clauseOff st cid + k2) l1,
      wh := wh', wn := wn' } := by
  subst hl1; subst hl2
  exact ⟨swapClause_preserves_core hinv.core hcid hk1 hk2 hwl hwnl, hinv.marks⟩

/-! ## 2. `kissat_find_repl` `Func.wp` proof -/

private def findReplBad (vals : List (BitVec 8)) (lits : List (BitVec 32))
    (n_lits : BitVec 64) (k : Nat) : Prop :=
  let cand := (lits[k]?.getD 0#32).toNat
  n_lits.toNat ≤ cand ∨ ((vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = true

private theorem find_repl_ok {vals : List (BitVec 8)} {lits : List (BitVec 32)}
    {sz : BitVec 32} {n_lits : BitVec 64} {r : BitVec 32}
    (hvl : vals.length = n_lits.toNat) (hr2 : 2 ≤ r.toNat) (hr_sz : r.toNat < sz.toNat)
    {hi_lt : r.toNat < lits.length} {hj_lt : (lits[r.toNat]'hi_lt).toNat < vals.length}
    (hsle : (0#32).sle ((vals[(lits[r.toNat]'hi_lt).toNat]'hj_lt).signExtend 32) = true) :
    2 ≤ r.toNat ∧ r.toNat < sz.toNat ∧ let cand := (lits[r.toNat]?.getD 0#32).toNat
      cand < n_lits.toNat ∧ ((vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = false := by
  refine ⟨hr2, hr_sz, ?_⟩
  simp only [List.getElem?_eq_getElem hi_lt, Option.getD_some, List.getElem?_eq_getElem hj_lt]
  exact ⟨by omega, by rw [bv32_sle0_eq_not_slt0, Bool.not_eq_true'] at hsle; exact hsle⟩

private theorem find_repl_bad_slt {vals : List (BitVec 8)} {lits : List (BitVec 32)}
    {n_lits : BitVec 64} {r : BitVec 32} {hi_lt : r.toNat < lits.length}
    {hj_lt : (lits[r.toNat]'hi_lt).toNat < vals.length}
    (h : (0#32).sle ((vals[(lits[r.toNat]'hi_lt).toNat]'hj_lt).signExtend 32) = false) :
    findReplBad vals lits n_lits r.toNat := by
  refine Or.inr ?_
  simp only [List.getElem?_eq_getElem hi_lt, Option.getD_some, List.getElem?_eq_getElem hj_lt]
  rw [bv32_sle0_eq_not_slt0, Bool.not_eq_false'] at h; exact h

private theorem find_repl_bad_oob {vals : List (BitVec 8)} {lits : List (BitVec 32)}
    {n_lits : BitVec 64} {r : BitVec 32} {hi_lt : r.toNat < lits.length}
    (h : ¬ (lits[r.toNat]'hi_lt).toNat < n_lits.toNat) :
    findReplBad vals lits n_lits r.toNat := by
  refine Or.inl ?_; simp only [List.getElem?_eq_getElem hi_lt, Option.getD_some]; omega

theorem kissat_find_repl_wp (Γ : Env) :
    ∀ args m Q X, corePlusFindReplSpec args m Q X →
      Func.wp Γ CorePlus.kissat_find_repl_body args m Q X := by
  rintro ⟨vals_ptr, lits_ptr, sz, srch, n_lits, ⟨⟩⟩ m Q X
    ⟨vals, lits, R, hvl, hll, hsrch2, hsrch_le, hm, hQ⟩
  cp_steps
  refine wp_loop_inv
    (fun (r, ()) ml => srch.toNat ≤ r.toNat ∧ r.toNat ≤ sz.toNat ∧ ml = m ∧
      ∀ k, srch.toNat ≤ k → k < r.toNat → findReplBad vals lits n_lits k)
    (fun (r, ()) _ => sz.toNat - r.toNat)
    (fun J hJ => by cp_steps; exact hJ _ _ ⟨Nat.le_refl _, hsrch_le, rfl, fun _ _ _ => by omega⟩)
    (fun J (r, ()) ml ⟨hr_ge, hr_le, rfl, hseen1⟩ ih => ?_)
  cp_steps
  · exact hQ r (Or.inr (find_repl_ok hvl (by omega) (by omega) hc))
  · refine ih _ _ (by c0_bound) ⟨by c0_bound, by c0_bound, rfl, fun k hk1 hk2 =>
      if hkr : k = r.toNat then hkr ▸ find_repl_bad_slt hc else hseen1 k hk1 (by c0_bound)⟩
  · refine ih _ _ (by c0_bound) ⟨by c0_bound, by c0_bound, rfl, fun k hk1 hk2 =>
      if hkr : k = r.toNat then hkr ▸ find_repl_bad_oob hc else hseen1 k hk1 (by c0_bound)⟩
  · refine wp_loop_inv
      (fun (r2, ()) ml2 => 2 ≤ r2.toNat ∧ r2.toNat ≤ srch.toNat ∧ ml2 = ml ∧
        ∀ k, 2 ≤ k → k < r2.toNat → findReplBad vals lits n_lits k)
      (fun (r2, ()) _ => srch.toNat - r2.toNat)
      (fun J2 hJ2 => by
        cp_steps; exact hJ2 _ _ ⟨by decide, by c0_bound, rfl, fun _ _ _ => by c0_bound⟩)
      (fun J2 (r2, ()) ml2 ⟨hr2_ge, hr2_le, rfl, hseen2⟩ ih2 => ?_)
    cp_steps
    · exact hQ r2 (Or.inr (find_repl_ok hvl hr2_ge (by omega) hc))
    · refine ih2 _ _ (by c0_bound) ⟨by c0_bound, by c0_bound, rfl, fun k hk1 hk2 =>
        if hkr : k = r2.toNat then hkr ▸ find_repl_bad_slt hc else hseen2 k hk1 (by c0_bound)⟩
    · refine ih2 _ _ (by c0_bound) ⟨by c0_bound, by c0_bound, rfl, fun k hk1 hk2 =>
        if hkr : k = r2.toNat then hkr ▸ find_repl_bad_oob hc else hseen2 k hk1 (by c0_bound)⟩
    · exact hQ 0xFFFFFFFF#32 (Or.inl ⟨rfl, fun k hk2 hksz =>
        if hks : k < srch.toNat then hseen2 k hk2 (by omega) else hseen1 k (by omega) (by omega)⟩)

/-! ## 3. `kissat_propagate_lit` `Func.wp` proof -/

private structure PropLitInv (c : CorePlusCfg) (F0 : CNF Nat) (s st : CorePlusState)
    (not_lit : BitVec 32) : Prop where
  inv : CorePlusInv c F0 st
  agrees : AgreesExcept propLitMask s st
  trail_end_ge : s.trail_end ≤ st.trail_end
  rel_eq : st.heur.rel_trigger = s.heur.rel_trigger
  not_false : st.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8

theorem kissat_propagate_lit_wp (Γ : Env)
    (hFind : ∀ args m Q X, corePlusFindReplSpec args m Q X →
      Γ "kissat_find_repl" [i64, i64, i32, i32, i64] [i32] args m Q X)
    (hAssign : ∀ args m Q X, corePlusAssignSpec args m Q X →
      Γ "kissat_assign" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, corePlusPropagateLitSpec args m Q X →
      Func.wp Γ CorePlus.kissat_propagate_lit_body args m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmv := c.hmv; have hmc := c.hmax_c; have hlc := c.hlcap
  unfold dimacsBound at hmv hmc hlc
  have hlen0 := hinv.core.lengths
  have hvl0 := hlen0.vals_len; have hwl0 := hlen0.wh_len; have hnc0 := hlen0.num_clauses_le
  have hret_s : Q (0xFFFFFFFF#64, ()) m :=
    hQ 0xFFFFFFFF#64 s.vals s.lvl s.rsns s.trl s.trail_end s.wh s.wn s.cls s.lpool s.heur m
      hinv (Nat.le_refl _) rfl (Or.inl rfl) (fun _ => ⟨rfl, rfl⟩) hm
  unfold Func.wp CorePlus.kissat_propagate_lit_body; t_wp_unfold
  simp only [BitVec.reduceSignExtend, BitVec.reduceSetWidth, BitVec.reduceToNat, Nat.reduceMod]
  refine ⟨_, load_arena_mv hm, fun _ => hret_s, fun hlt_n => ?_⟩
  have hnot_lt : (lit ^^^ 1#32).toNat < 2 * c.mv := by
    have h1 : (lit ^^^ 1 : BitVec 32).toNat = (lit ^^^ 1#32).toNat := rfl
    rw [← h1]; c0_bound
  refine ⟨_, load_arena_watch_head hm, _, load_arena_watch_next hm,
    _, load_arena_clauses hm, _, load_arena_lit_pool hm, _, load_arena_values hm,
    _, c0_load_arena_vals (by c0_bound) hm, fun _ => hret_s, fun hge0 => ?_⟩
  have hnot_false0 : s.vals[(lit ^^^ 1#32).toNat]?.getD 0#8 = 0xFF#8 := by
    have hslt : ((s.vals[(lit ^^^ 1#32).toNat]'(by omega)).signExtend 32).slt 0#32 = true := by
      have h' := hge0
      simp only [bv_c0, bv32_sle0_eq_not_slt0, Bool.not_eq_false'] at h'; exact h'
    have hget : s.vals[(lit ^^^ 1#32).toNat]?.getD 0#8 =
        s.vals[(lit ^^^ 1#32).toNat]'(by omega) := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [hget]
    exact (i8_vals_slt0 (hget ▸ hinv.core.vals_domain _ hnot_lt)).mp hslt
  refine ⟨_, c0_load_arena_wh (by c0_bound) hm, _, load_arena_num_clauses hm, ?_⟩
  · have hret_st : ∀ {st : CorePlusState} {mb : Mem 64},
        PropLitInv c F0 s st (lit ^^^ 1#32) →
        (s.wh[(lit ^^^ 1#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 → st = s) →
        (CorePlusMem c st ⋆ R) mb → Q (0xFFFFFFFF#64, ()) mb := by
      intro st mb hpi hwh_s hmb
      have hst_eq := propLit_eq_upd hpi.agrees
      have hinv' := hpi.inv; rw [hst_eq] at hinv' hmb
      exact hQ 0xFFFFFFFF#64 st.vals st.lvl st.rsns st.trl st.trail_end st.wh st.wn st.cls
        st.lpool st.heur mb hinv' hpi.trail_end_ge hpi.rel_eq (Or.inl rfl)
        (fun hE => ⟨rfl, by rw [← hst_eq]; exact hwh_s hE⟩) hmb
    refine wp_unroll_group fun J hJ => ?_
    refine wp_loop_group
      (fun rem (prev_v, w_v, steps_v, ()) ml => ∃ st : CorePlusState,
        steps_v.toNat ≤ 2 * s.num_clauses + 1 ∧
        rem = (2 * s.num_clauses + 1) - steps_v.toNat ∧
        (prev_v = 0xFFFFFFFF#32 ∨ prev_v.toNat < 2 * c.max_c) ∧
        PropLitInv c F0 s st (lit ^^^ 1#32) ∧
        (s.wh[(lit ^^^ 1#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 →
          w_v = 0xFFFFFFFF#32 ∧ st = s) ∧
        (CorePlusMem c st ⋆ R) ml) ?_ ?_
    · rintro L rem ⟨prev_v, w_v, steps_v, ⟨⟩⟩ ml ih
        ⟨st, hsteps_le, rfl, hprev_ok, hpi, hwh_s, hml⟩
      have hlen := hpi.inv.core.lengths
      have hvl := hlen.vals_len; have hwl := hlen.wh_len; have hwnl := hlen.wn_len
      have hclsl := hlen.cls_len; have hlpl := hlen.lpool_len
      have hnc_le := hlen.num_clauses_le; have hll_le := hlen.lit_len_le
      have hnc_eq : st.num_clauses = s.num_clauses := hpi.agrees.get CorePlusState.num_clauses
      t_wp_unfold
      refine ⟨fun hw_ne => ?_, fun _ =>
        hJ _ ml (by cp_steps; exact hret_st hpi (fun hE => (hwh_s hE).2) hml)⟩
      have hwh_ne : s.wh[(lit ^^^ 1#32).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 :=
        fun hE => hw_ne (hwh_s hE).1
      refine ⟨fun hsteps_lt0 => ?_, fun _ =>
        hJ _ ml (by cp_steps; exact hret_st hpi (fun hE => absurd hE hwh_ne) hml)⟩
      have hsteps_lt : steps_v.toNat < 2 * s.num_clauses + 1 := by c0_bound
      have hsteps1 : (steps_v + (1 : BitVec 64)).toNat = steps_v.toNat + 1 := by c0_bound
      refine ⟨_, load_arena_num_clauses hml,
        fun _ => hJ _ ml (by cp_steps; exact hret_st hpi (fun hE => absurd hE hwh_ne) hml),
        fun hcid_lt0 => ?_⟩
      have hcid_lt : (w_v >>> (1 : Nat)).toNat < st.num_clauses := by c0_bound
      have hw_lt : w_v.toNat < 2 * c.max_c := by c0_bound
      have hslot_cases : (w_v &&& 1).toNat = 0 ∨ (w_v &&& 1).toNat = 1 := by c0_bound
      have hslot_xor : ((w_v &&& 1) ^^^ 1).toNat = 1 - (w_v &&& 1).toNat := by c0_bound
      refine ⟨_, c0_load_arena_wn (by c0_bound) hml,
        _, c0_load_cls_size (by c0_bound) hml, _, c0_load_cls_off (by c0_bound) hml, ?_⟩
      · generalize hoff_def :
          st.cls[4 * ((w_v >>> (1 : Nat)).setWidth 64).toNat]'(by c0_bound) = off_v
        generalize hsz_def :
          st.cls[4 * ((w_v >>> (1 : Nat)).setWidth 64).toNat + 1]'(by c0_bound) = sz_v
        have hcl_bd := hpi.inv.core.clauses.bounds (w_v >>> (1 : Nat)).toNat hcid_lt
        have hoff_eq : off_v.toNat = clauseOff st (w_v >>> (1 : Nat)).toNat := by
          rw [← hoff_def]; unfold clauseOff
          simp only [show 4 * ((w_v >>> (1 : Nat)).setWidth 64).toNat =
            4 * (w_v >>> (1 : Nat)).toNat by c0_bound,
            List.getElem?_eq_getElem (show 4 * (w_v >>> (1 : Nat)).toNat < st.cls.length by omega),
            Option.getD_some]
        have hsz_eq : sz_v.toNat = clauseSize st (w_v >>> (1 : Nat)).toNat := by
          rw [← hsz_def]; unfold clauseSize
          simp only [show 4 * ((w_v >>> (1 : Nat)).setWidth 64).toNat + 1 =
            4 * (w_v >>> (1 : Nat)).toNat + 1 by c0_bound,
            List.getElem?_eq_getElem (show 4 * (w_v >>> (1 : Nat)).toNat + 1 < st.cls.length by
              omega), Option.getD_some]
        have hsz_ge2 : 2 ≤ sz_v.toNat := hsz_eq ▸ hcl_bd.1
        have hoff_sz_ll : off_v.toNat + sz_v.toNat ≤ st.lit_len := by
          rw [hoff_eq, hsz_eq]; exact hcl_bd.2
        -- Group 1: `bad_cl` evaluates to `false`
        refine wp_join_group (fun (v : Tup Val [.bool]) m1 => v.1 = false ∧ ml = m1) ?_ ?_
        · rintro _ ⟨b, ⟨⟩⟩ m1 ⟨rfl, rfl⟩
          cp_step
          -- Group 2: stale-watch drop handler
          refine wp_join_group (fun (_ : Tup Val []) m2 => ml = m2) ?_ ?_
          · rintro _ ⟨⟩ m2 rfl
            cp_steps
            all_goals
              refine ih ((2 * s.num_clauses + 1) - (steps_v + 1).toNat) _ m (by omega)
                ⟨_, by omega, rfl, hprev_ok, ?_, fun hE => absurd hE hwh_ne, hm⟩
              exact ⟨hpi.inv.with_watches (by simp [hwl]) (by simp [hwnl]),
                (hpi.agrees.update _).update _, hpi.trail_end_ge, hpi.rel_eq, hpi.not_false⟩
          · intro Jdrop hJdrop
            cp_step
            -- Group 4: check `(lits[0] != not_lit && lits[1] != not_lit)`
            refine wp_join_group (fun (_ : Tup Val []) m2 => ml = m2) ?_ ?_
            · rintro _ ⟨⟩ m2 rfl
              t_wp_unfold
              simp only [BitVec.reduceSignExtend, BitVec.reduceSetWidth]
              refine ⟨_, c0_load_lpool_off (by c0_bound) hml,
                fun _ => hJdrop () ml rfl, fun hnot_at0 => ?_⟩
              have hnot_at : st.lpool[off_v.toNat + (w_v &&& 1).toNat]'(by omega) =
                  lit ^^^ 1#32 := by
                have hi : (off_v.setWidth 64).toNat +
                    ((w_v &&& 1).setWidth 64).toNat =
                    off_v.toNat + (w_v &&& 1).toNat := by c0_bound
                have h' : st.lpool[(off_v.setWidth 64).toNat +
                    ((w_v &&& 1).setWidth 64).toNat]'(by c0_bound) =
                    lit ^^^ 1#32 := hnot_at0
                simpa only [hi] using h'
              refine ⟨_, c0_load_lpool_off (by c0_bound) hml, ?_⟩
              generalize hother_def :
                st.lpool[(off_v.setWidth 64).toNat +
                  (((w_v &&& 1) ^^^ 1).setWidth 64).toNat]'(
                    by c0_bound) = other
              have hother_idx : off_v.toNat + ((w_v &&& 1) ^^^ 1).toNat <
                  st.lpool.length := by omega
              have hother_eq : other =
                  st.lpool[off_v.toNat + ((w_v &&& 1) ^^^ 1).toNat]'hother_idx := by
                rw [← hother_def]; congr 1
              have hother_mem : other.toNat ∈ clauseLits st (w_v >>> (1 : Nat)).toNat := by
                refine (mem_clauseLits_iff (by rw [← hoff_eq, ← hsz_eq]; omega)).mpr ?_
                refine ⟨((w_v &&& 1) ^^^ 1).toNat, by rw [← hsz_eq]; omega, ?_⟩
                rw [hother_eq]; simp only [← hoff_eq]
              have hother_lt : other.toNat < 2 * c.mv :=
                hpi.inv.core.clauses.lits_lt _ hcid_lt _ hother_mem
              refine ⟨fun hge => by exfalso; c0_bound, fun _ =>
                ⟨_, c0_load_arena_vals (by c0_bound) hml,
                  fun _ => ih ((2 * s.num_clauses + 1) - (steps_v + 1).toNat) _ ml (by omega)
                    ⟨st, by omega, rfl, Or.inr hw_lt, hpi,
                      fun hE => absurd hE hwh_ne, hml⟩,
                  fun hnot_gt0 => ⟨_, c0_load_cls_srch (by c0_bound) hml, ?_⟩⟩⟩
              · have hnot_gt0 : (0#32).slt ((st.vals[other.toNat]'(by omega)).signExtend 32) =
                    false := by
                  have h' := hnot_gt0; simp only [bv_c0] at h'; exact h'
                refine wp_join_group
                  (fun (v : Tup Val [i32]) m3 =>
                    ml = m3 ∧ 2 ≤ v.1.toNat ∧ v.1.toNat ≤ sz_v.toNat) ?_ ?_
                · rintro _ ⟨srch', ⟨⟩⟩ m3 ⟨rfl, hsrch2, hsrch_le⟩
                  cp_steps
                  obtain ⟨F, hfocus⟩ := corePlusMem_focus_vals_lpool
                    (off := off_v.toNat) (sz := sz_v.toNat) (by omega) hml
                  c0_call hFind
                  have hlits_ptr_eq : c.pLpool + off_v.setWidth 64 * 4 =
                      c.pLpool + BitVec.ofNat 64 (4 * off_v.toNat) := by
                    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
                    congr 1
                  refine ⟨st.vals, (st.lpool.drop off_v.toNat).take sz_v.toNat, F,
                    by c0_bound,
                    by rw [List.length_take, List.length_drop]; omega,
                    hsrch2, hsrch_le, by rwa [hlits_ptr_eq], fun r hr_post => ?_⟩
                  cp_step
                  · obtain ⟨hr2, hr_lt, hcand_lt, _⟩ := hr_post.resolve_left fun h => hc h.1
                    have hr_lpool : off_v.toNat + r.toNat < st.lpool.length := by omega
                    have hrepl_lt0 : (st.lpool[off_v.toNat + r.toNat]'hr_lpool).toNat <
                        2 * c.mv := by
                      have hsl : r.toNat <
                          ((st.lpool.drop off_v.toNat).take sz_v.toNat).length := by
                        rw [List.length_take, List.length_drop]; omega
                      rw [List.getElem?_eq_getElem hsl, Option.getD_some,
                        List.getElem_take, List.getElem_drop] at hcand_lt
                      c0_bound
                    t_wp_unfold
                    refine ⟨_, c0_load_lpool_off (by c0_bound) hml, ?_⟩
                    generalize hrepl_def :
                      st.lpool[(off_v.setWidth 64).toNat + (r.setWidth 64).toNat]'(
                        by c0_bound) = repl
                    have hrepl_eq : repl = st.lpool[off_v.toNat + r.toNat]'hr_lpool := by
                      rw [← hrepl_def]; congr 1
                    have hrepl_lt : repl.toNat < 2 * c.mv := hrepl_eq ▸ hrepl_lt0
                    obtain ⟨hok1, hm1⟩ := c0_store_cls_srch r
                      (cid := (w_v >>> (1 : Nat)).setWidth 64) (by c0_bound) hml
                    obtain ⟨hok2, hm2⟩ := c0_store_lpool_off repl (off := off_v.setWidth 64)
                      (k := (w_v &&& 1).setWidth 64) (by simp [hlpl]; c0_bound) hm1
                    obtain ⟨hok3, hm3⟩ := c0_store_lpool_off (lit ^^^ 1#32)
                      (off := off_v.setWidth 64) (k := r.setWidth 64) (by simp [hlpl]; c0_bound) hm2
                    refine ⟨hok1, hok2, hok3, ?_⟩
                    let st_sw : CorePlusState :=
                      { st with
                        cls := st.cls.set (4 * ((w_v >>> (1 : Nat)).setWidth 64).toNat + 2) r,
                        lpool := (st.lpool.set ((off_v.setWidth 64).toNat +
                          ((w_v &&& 1).setWidth 64).toNat) repl).set
                          ((off_v.setWidth 64).toNat + (r.setWidth 64).toNat) (lit ^^^ 1#32) }
                    refine wp_join_group (fun (_ : Tup Val []) m4 => ∃ wh' wn',
                        wh'.length = 2 * c.mv ∧ wn'.length = 2 * c.max_c ∧
                        (CorePlusMem c { st_sw with wh := wh', wn := wn' } ⋆ R) m4) ?_ ?_
                    · rintro _ ⟨⟩ m4 ⟨wh', wn', hwl', hwnl', hm4⟩
                      cp_steps
                      refine ih ((2 * s.num_clauses + 1) - (steps_v + 1).toNat) _ m (by omega)
                        ⟨_, by omega, rfl, hprev_ok, ?_, fun hE => absurd hE hwh_ne, hm⟩
                      refine ⟨?_, ((((hpi.agrees.update _).update _).update _).update _).update _,
                        hpi.trail_end_ge, hpi.rel_eq, hpi.not_false⟩
                      have h := swap_watch_preserves_inv (cid := (w_v >>> (1 : Nat)).toNat)
                        (k1 := (w_v &&& 1).toNat) (k2 := r.toNat) (srch := r)
                        (l1 := lit ^^^ 1#32) (l2 := repl)
                        (wh' := wh'.set (repl.setWidth 64).toNat w_v)
                        (wn' := wn'.set (w_v.setWidth 64).toNat
                          (wh'[(repl.setWidth 64).toNat]'(by rw [hwl']; c0_bound)))
                        hpi.inv hcid_lt (by rw [← hsz_eq]; omega) (by rw [← hsz_eq]; omega)
                        (by rw [← hoff_eq, ← hsz_eq]; omega)
                        (by simpa only [← hoff_eq] using hnot_at)
                        (by simpa only [← hoff_eq] using hrepl_eq.symm)
                        (by simp [hwl']) (by simp [hwnl'])
                      have hi_c : 4 * ((w_v >>> (1 : Nat)).setWidth 64).toNat + 2 =
                          4 * (w_v >>> (1 : Nat)).toNat + 2 := by c0_bound
                      have hi_s : (off_v.setWidth 64).toNat +
                          ((w_v &&& 1).setWidth 64).toNat =
                          clauseOff st (w_v >>> (1 : Nat)).toNat + (w_v &&& 1).toNat := by
                        rw [← hoff_eq]; c0_bound
                      have hi_r : (off_v.setWidth 64).toNat + (r.setWidth 64).toNat =
                          clauseOff st (w_v >>> (1 : Nat)).toNat + r.toNat := by
                        rw [← hoff_eq]; c0_bound
                      simpa only [st_sw, hi_c, hi_s, hi_r] using h
                    · intro J6 hJ6; t_wp_unfold
                      refine ⟨fun _ => ?_, fun hprev_ne => ?_⟩
                      · obtain ⟨hok, hm'⟩ := c0_store_arena_wh
                          (i := (lit ^^^ (1 : BitVec 32)).setWidth 64)
                          (st.wn[(w_v.setWidth 64).toNat]'(by c0_bound))
                          (by dsimp only; rw [hwl, bv_c0_zext32_64]; exact hnot_lt) hm3
                        exact ⟨hok, hJ6 () _ ⟨_, _, by simp [hwl], hwnl, hm'⟩⟩
                      · have hprev_lt : prev_v.toNat < 2 * c.max_c := hprev_ok.resolve_left hprev_ne
                        obtain ⟨hok, hm'⟩ := c0_store_arena_wn (i := prev_v.setWidth 64)
                          (st.wn[(w_v.setWidth 64).toNat]'(by c0_bound))
                          (by dsimp only; rw [hwnl, bv_c0_zext32_64]; exact hprev_lt) hm3
                        exact ⟨hok, hJ6 () _ ⟨_, _, hwl, by simp [hwnl], hm'⟩⟩
                  · have hfind_none : ∀ k, 2 ≤ k → k < sz_v.toNat →
                        let cand := (((st.lpool.drop off_v.toNat).take sz_v.toNat)[k]?.getD
                          0#32).toNat
                        2 * c.mv ≤ cand ∨
                          ((st.vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = true := by
                      rcases hr_post with ⟨_, hall⟩ | ⟨_, hlt, _⟩
                      · intro k hk2 hksz; have h := hall k hk2 hksz
                        rwa [show (BitVec.ofNat 64 c.mv <<< (1 : Nat)).toNat = 2 * c.mv by
                          c0_bound] at h
                      · rw [hc] at hlt; have := sz_v.isLt; c0_bound
                    have hunit := clause_falsified_of_find_repl_none (slot := (w_v &&& 1).toNat)
                      (not_lit := (lit ^^^ 1#32).toNat) (other := other.toNat)
                      hpi.inv hcid_lt hslot_cases (by rw [← hoff_eq, ← hsz_eq]; omega)
                      (by rw [← hsz_eq]; exact hsz_ge2)
                      (by simpa only [← hoff_eq] using congrArg BitVec.toNat hnot_at) hpi.not_false
                      (by rw [hother_eq]; simp only [← hoff_eq, ← hslot_xor])
                      (by simpa only [← hoff_eq, ← hsz_eq] using hfind_none)
                    have hoval_idx : other.toNat < st.vals.length := by omega
                    have hoval_get : st.vals[other.toNat]?.getD 0#8 =
                        st.vals[other.toNat]'hoval_idx := by
                      simp [List.getElem?_eq_getElem hoval_idx]
                    have hoval_dom := hoval_get ▸ hpi.inv.core.vals_domain other.toNat hother_lt
                    cp_steps
                    · have hother_ff : st.vals[other.toNat]?.getD 0#8 = 0xFF#8 :=
                        hoval_get.trans ((i8_vals_slt0 hoval_dom).mp hc)
                      have hst_eq := propLit_eq_upd hpi.agrees
                      have hinv' := hpi.inv; rw [hst_eq] at hinv' hml
                      refine hQ ((w_v >>> (1 : Nat)).setWidth 64) st.vals st.lvl st.rsns
                        st.trl st.trail_end st.wh st.wn st.cls st.lpool st.heur ml hinv'
                        hpi.trail_end_ge hpi.rel_eq
                        (Or.inr ⟨by rw [← hst_eq]; c0_bound, fun l hl => ?_⟩)
                        (fun hE => absurd hE hwh_ne) hml
                      rw [← hst_eq, show ((w_v >>> (1 : Nat)).setWidth 64).toNat =
                        (w_v >>> (1 : Nat)).toNat by c0_bound] at hl
                      exact (hunit l hl).elim (fun h => by dsimp only; exact h ▸ hother_ff) id
                    · have hother_un : st.vals[other.toNat]?.getD 0#8 = 0#8 := by
                        rw [hoval_get]; have hdom := hoval_dom
                        rcases hdom with h0 | h1 | hff
                        · exact h0
                        · exact absurd ((i8_vals_sgt0 hoval_dom).mpr h1) (by rw [hnot_gt0]; decide)
                        · exact absurd ((i8_vals_slt0 hoval_dom).mpr hff) (by rw [hc]; decide)
                      have hte_lt := hpi.inv.core.trail_end_lt_of_unassigned hother_lt hother_un
                      have hnot_guard : ¬ (c.mv ≤ other.toNat / 2 ∨ c.mv ≤ st.trail_end) := by omega
                      c0_call hAssign
                      refine ⟨c, st, R, rfl, hlen, hml, ?_⟩
                      simp only [hnot_guard, ↓reduceIte]
                      intro phases' m_as hph _ hm_as; cp_steps
                      obtain ⟨hinv_as, hnot_as⟩ := unit_assign_preserves_inv hpi.inv hcid_lt
                        hother_lt hph hother_un hunit hnot_lt hpi.not_false
                      exact ih ((2 * s.num_clauses + 1) - (steps_v + 1).toNat) _ m_as (by omega)
                        ⟨_, by omega, rfl, Or.inr hw_lt, ⟨hinv_as, hpi.agrees.update _,
                          by dsimp; have := hpi.trail_end_ge; omega, hpi.rel_eq, hnot_as⟩,
                          fun hE => absurd hE hwh_ne, hm_as⟩
                · intro J5 hJ5; t_wp_unfold
                  exact ⟨fun _ => hJ5 (2#32, ()) ml ⟨rfl, by decide, hsz_ge2⟩,
                    fun hge2 => ⟨fun _ => hJ5 (2#32, ()) ml ⟨rfl, by decide, hsz_ge2⟩,
                      fun hle => hJ5 (_, ()) ml ⟨rfl, by c0_bound, by c0_bound⟩⟩⟩
            · intro J4 hJ4; t_wp_unfold
              simp only [BitVec.reduceSignExtend, BitVec.reduceMul]
              exact ⟨_, c0_load_lpool_off0 (by c0_bound) hml,
                fun _ => ⟨_, c0_load_lpool_off1 (by c0_bound) hml,
                  fun _ => hJdrop () ml rfl, fun _ => hJ4 () ml rfl⟩,
                fun _ => hJ4 () ml rfl⟩
        · intro J1 hJ1; t_wp_unfold
          refine ⟨fun h => by exfalso; c0_bound, fun _ =>
            ⟨_, load_arena_lit_len hml, fun h => by exfalso; c0_bound,
              fun _ => ⟨_, load_arena_lit_len hml, fun h => by exfalso; c0_bound,
                fun _ => hJ1 (false, ()) ml ⟨rfl, rfl⟩⟩⟩⟩
    · intro L hL; cp_steps
      have hwh0_get : s.wh[(lit ^^^ 1#32).toNat]?.getD 0xFFFFFFFF#32 =
          s.wh[(lit ^^^ 1#32).toNat]'(by omega) := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hidx : (BitVec.setWidth 64 (lit ^^^ 1 : BitVec 32)).toNat = (lit ^^^ 1#32).toNat := by
        change ((lit ^^^ 1#32).setWidth 64).toNat = (lit ^^^ 1#32).toNat; c0_bound
      exact hL (2 * s.num_clauses + 1) _ m
        ⟨s, by c0_bound, by c0_bound, Or.inl rfl,
          ⟨hinv, .refl _ _, Nat.le_refl _, rfl, hnot_false0⟩,
          fun hE => ⟨by simp only [hidx]; rw [← hwh0_get]; exact hE, rfl⟩, hm⟩

/-! ## 4. `kissat_propagate` `Func.wp` proof -/

theorem kissat_propagate_wp (Γ : Env)
    (hPropLit : ∀ args m Q X, corePlusPropagateLitSpec args m Q X →
      Γ "kissat_propagate_lit" [i64, i32] [i64] args m Q X) :
    ∀ args m Q X, corePlusPropagateSpec args m Q X →
      Func.wp Γ CorePlus.kissat_propagate_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmv := c.hmv; unfold dimacsBound at hmv
  let EmptyWh := ∀ l < 2 * c.mv, s.wh[l]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
  cp_steps
  refine wp_loop_group
    (fun rem (_ : Tup Val []) ml => ∃ st : CorePlusState,
      rem = st.fuel.toNat ∧ CorePlusInv c F0 st ∧ AgreesExcept propMask s st ∧
      st.fuel.toNat ≤ s.fuel.toNat ∧ st.heur.rel_trigger = s.heur.rel_trigger ∧
      (EmptyWh → st.wh = s.wh ∧ st.vals = s.vals ∧ st.trail_end = s.trail_end ∧
        s.propagated ≤ st.propagated ∧
        st.fuel.toNat + (st.propagated - s.propagated) = s.fuel.toNat) ∧
      (CorePlusMem c st ⋆ R) ml) ?_ ?_
  · rintro L rem ⟨⟩ ml ih ⟨st, rfl, hst_inv, hag, hfuel_le, hrel, hempty, hml⟩
    have hlen := hst_inv.core.lengths
    have htl := hlen.trl_len; have hte_le := hlen.trail_end_le; have hpr_le := hlen.propagated_le
    cp_steps
    · have hst_eq := prop_eq_upd hag; rw [hst_eq] at hst_inv hml
      refine hQ 2#64 st.vals st.lvl st.rsns st.trl st.trail_end st.propagated st.wh st.wn st.cls
        st.lpool st.fuel st.confl_cid st.heur ml hst_inv hfuel_le hrel (Or.inr (Or.inr rfl))
        (by simp) (by simp) (fun hE _ => ?_) hml
      obtain ⟨_, _, _, _, _⟩ := hempty hE
      have hfz : st.fuel.toNat = 0 := by rw [hc]; rfl
      have : st.propagated < st.trail_end := by c0_bound
      omega
    · have hpr_lt : st.propagated < st.trail_end := by c0_bound
      have hfuel_sub : (st.fuel - 1).toNat = st.fuel.toNat - 1 := bv64_sub1_toNat hc
      have hfuel_pos : 0 < st.fuel.toNat :=
        Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
      have hpr1 : (BitVec.ofNat 64 st.propagated + 1#64).toNat = st.propagated + 1 := by c0_bound
      let st1 : CorePlusState :=
        { st with fuel := st.fuel - 1, propagated := (BitVec.ofNat 64 st.propagated + 1#64).toNat }
      have hlit_lt : (st.trl[(BitVec.ofNat 64 st.propagated).toNat]'(by c0_bound)).toNat <
          2 * c.mv := by
        have hidx : (BitVec.ofNat 64 st.propagated).toNat = st.propagated := by c0_bound
        simpa [hidx, List.getElem?_eq_getElem (show st.propagated < st.trl.length by omega)]
          using hst_inv.core.trail_lits_lt st.propagated hpr_lt
      have hnlit_lt : (st.trl[(BitVec.ofNat 64 st.propagated).toNat]'(by c0_bound) ^^^ 1#32).toNat <
          2 * c.mv := by simpa [BitVec.toNat_xor] using litNeg_lt_two_mul hlit_lt
      c0_call hPropLit
      refine ⟨c, F0, st1, R, rfl, hst_inv.with_fuel_prop (by omega), hm,
        fun confl vals' lvl' rsns' trl' te' wh' wn' cls' lpool' heur' m2
          hst2_inv _ hrel' hconfl hwh_none hm2 => ?_⟩
      let st2 : CorePlusState :=
        { st1 with vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_end := te',
                   wh := wh', wn := wn', cls := cls', lpool := lpool', heur := heur' }
      have hag2 : AgreesExcept propMask s st2 := (hag.update _).update _
      have hwh_e : EmptyWh → st1.wh[((st.trl[(BitVec.ofNat 64 st.propagated).toNat]'(
          by c0_bound)) ^^^ 1#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := fun hE => by
        dsimp [st1]; rw [(hempty hE).1]; exact hE _ hnlit_lt
      cp_steps
      · let st3 : CorePlusState := { st2 with confl_cid := confl }
        have hst3_inv : CorePlusInv c F0 st3 := hst2_inv.with_confl
        have hag3 : AgreesExcept propMask s st3 := hag2.update _
        have hst3_eq := prop_eq_upd hag3
        have hconfl_ok := hconfl.resolve_left hc
        change (CorePlusMem c st3 ⋆ R) m at hm; rw [hst3_eq] at hst3_inv hm
        have hnc_eq : s.num_clauses = st1.num_clauses := (hag.get CorePlusState.num_clauses).symm
        exact hQ 1#64 st3.vals st3.lvl st3.rsns st3.trl st3.trail_end st3.propagated st3.wh st3.wn
          st3.cls st3.lpool st3.fuel st3.confl_cid st3.heur m hst3_inv
          (by dsimp [st3, st2, st1]; omega) (hrel'.trans hrel) (Or.inr (Or.inl rfl)) (by simp)
          (fun _ => ⟨by dsimp [st3, st2, st1]; omega,
            by dsimp [st3]; rw [hnc_eq]; exact hconfl_ok.1, by dsimp [st3]; exact hconfl_ok.2⟩)
          (fun hE _ => absurd (hwh_none (hwh_e hE)).1 hc) hm
      · refine ih st2.fuel.toNat () m2 (by dsimp [st2, st1]; omega)
          ⟨st2, rfl, hst2_inv, hag2, by dsimp [st2, st1]; omega,
            hrel'.trans hrel, fun hE => ?_, hm2⟩
        obtain ⟨hwh_eq, hvals_eq, hte_eq, _, _⟩ := hempty hE
        have hst2_eq : st2 = st1 := (hwh_none (hwh_e hE)).2
        rw [hst2_eq]; dsimp only [st1]; rw [hpr1, hfuel_sub]
        exact ⟨hwh_eq, hvals_eq, hte_eq, by omega, by omega⟩
    · have hpr_eq : st.propagated = st.trail_end := by c0_bound
      have hst_eq := prop_eq_upd hag; rw [hst_eq] at hst_inv hml
      refine hQ 0#64 st.vals st.lvl st.rsns st.trl st.trail_end st.propagated st.wh st.wn st.cls
        st.lpool st.fuel st.confl_cid st.heur ml hst_inv hfuel_le hrel (Or.inl rfl)
        (fun _ => hpr_eq) (by simp) (fun hE _ => ?_) hml
      obtain ⟨_, hvals_eq, hte_eq, _, _⟩ := hempty hE
      exact ⟨rfl, hvals_eq, hte_eq, by omega⟩
  · intro L hL; cp_steps
    exact hL s.fuel.toNat () m ⟨s, rfl, hinv, .refl _ _, Nat.le_refl _, rfl,
      fun _ => ⟨rfl, rfl, rfl, Nat.le_refl _, by omega⟩, hm⟩

end LeanQbe.T.Examples.Kissat.CorePlus
