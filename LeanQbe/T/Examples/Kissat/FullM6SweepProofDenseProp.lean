module

public import LeanQbe.T.Examples.Kissat.FullM6SweepProofKitten2c

/-!
# Kissat `D-Full` M6 — Level-0 Dense Unit Propagation Proofs (`15..16/39`)

Parametric `(Γ : Env)` `Func.wp` proofs for `2/39` owned functions (`16/39` cumulative):
- `15/39`: `full_m6_dense_prop_lit_wp` (`m6DensePropLitSpec`)
- `16/39`: `full_m6_dense_prop_wp` (`m6DensePropSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

/-! ## 1. BitVector, `DenseWatchSliceOk`, and Level-0 Transition Helpers -/

section BvDenseProp

@[scoped bv_c0] theorem m6_bv32_xor1_toNat (l : BitVec 32) :
    (l ^^^ 1#32).toNat = l.toNat ^^^ 1 := by simp

@[scoped bv_c0] theorem m6_bv32_xor1_ofnat (l : BitVec 32) :
    (l ^^^ (1 : BitVec 32)).toNat = l.toNat ^^^ 1 := by simp

@[scoped bv_c0] theorem m6_bv64_shl1_bv (x : BitVec 64) :
    (x <<< 1#64).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem m6_bv64_shl1_ofnat (x : BitVec 64) :
    (x <<< (1 : BitVec 64)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem m6_bv64_shl1_nat (x : BitVec 64) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

private theorem m6_bv8_toInt_bounds (v : BitVec 8) : -128 ≤ v.toInt ∧ v.toInt < 128 := by
  unfold BitVec.toInt; have := v.isLt; split <;> omega

private theorem m6_toInt_sext32 (v : BitVec 8) : (v.signExtend 32).toInt = v.toInt := by
  rw [BitVec.toInt_signExtend, show min 32 8 = 8 from rfl]
  have ⟨h1, h2⟩ := m6_bv8_toInt_bounds v
  unfold Int.bmod; dsimp only; split <;> omega

@[scoped bv_c0] theorem m6_bv8_sgt0_eq (v : BitVec 8) :
    (0#32).slt (v.signExtend 32) = (0#8).slt v := by
  simp only [BitVec.slt, m6_toInt_sext32]; rfl

@[scoped bv_c0] theorem m6_bv8_slt0_eq (v : BitVec 8) :
    (v.signExtend 32).slt 0#32 = v.slt 0#8 := by
  simp only [BitVec.slt, m6_toInt_sext32]; rfl

@[scoped bv_c0] theorem m6_bv8_sge0_eq (v : BitVec 8) :
    (0#32).sle (v.signExtend 32) = (0#8).sle v := by
  simp only [BitVec.sle, m6_toInt_sext32]; rfl

@[scoped bv_c0] theorem m6_bv8_eq0_sext (v : BitVec 8) :
    (v.signExtend 32 == 0#32) = (v == 0#8) := by
  by_cases h : v = 0#8
  · subst h; decide
  · simp only [beq_false_of_ne h]
    apply beq_false_of_ne; intro heq
    have h1 : v.toInt = 0 := by rw [← m6_toInt_sext32, heq]; rfl
    apply h; unfold BitVec.toInt at h1
    apply BitVec.eq_of_toNat_eq
    change v.toNat = 0; split at h1 <;> omega

end BvDenseProp

private theorem m6_vals_lt0_iff {v : BitVec 8} (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) :
    v.slt 0#8 = true ↔ v = 0xFF#8 := by
  rcases hdom with rfl | rfl | rfl <;> decide

private theorem m6_vals_gt0_iff {v : BitVec 8} (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) :
    (0#8).slt v = true ↔ v = 1#8 := by
  rcases hdom with rfl | rfl | rfl <;> decide

private theorem m6_vals_ge0_false {v : BitVec 8} (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (h : (0#8).sle v = false) : v = 0xFF#8 := by
  rcases hdom with rfl | rfl | rfl <;> simp_all

private theorem m6_vals_eq0_of_np_nn {v : BitVec 8} (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (hnp : (0#8).slt v = false) (hnn : v.slt 0#8 = false) : v = 0#8 := by
  rcases hdom with rfl | rfl | rfl <;> simp_all

private theorem m6_denseSlice_step_bin {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} {w0 : BitVec 32} (hs : DenseWatchSliceOk F_cur k lit p rem)
    (hpos : 0 < rem) (hp : k.wstk[p]? = some w0)
    (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) :
    w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
    DenseWatchSliceOk F_cur k lit (p + 1) (rem - 1) := by
  cases hs with
  | empty => omega
  | bin hp' _ hne hlt hent hrest =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact ⟨hne, hlt, hent, hrest⟩
  | occ hp' _ hflag _ _ _ _ =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact absurd hflag hbin

private theorem m6_denseSlice_step_occ {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} {w0 : BitVec 32} (hs : DenseWatchSliceOk F_cur k lit p rem)
    (hpos : 0 < rem) (hp : k.wstk[p]? = some w0)
    (hocc : (w0 &&& 0x80000000#32) = 0#32) :
    2 ≤ rem ∧ 3 ≤ w0.toNat ∧
    ∃ cr, k.wstk[p + 1]? = some cr ∧ cr.toNat < 0x80000000 ∧
      cr.toNat ∈ fullArenaClauseRefsCore k ∧
      DenseWatchSliceOk F_cur k lit (p + 2) (rem - 2) := by
  cases hs with
  | empty => omega
  | bin hp' hflag _ _ _ _ =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact absurd hocc hflag
  | occ hp' hp1 _ h3 hlt href hrest =>
    rw [hp] at hp'; cases Option.some.inj hp'
    exact ⟨by omega, h3, _, hp1, hlt, href, hrest⟩

private theorem m6_denseSlice_congr {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p rem : Nat} (hcv : k'.cur_vars = k.cur_vars) (hw : k'.wstk = k.wstk)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hs : DenseWatchSliceOk F_cur k lit p rem) :
    DenseWatchSliceOk F_cur k' lit p rem := by
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  exact hs.relocate hrefl (le_of_eq hcv.symm) hsub fun _ _ => by rw [hw]

private theorem m6_lvl0_false_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {l : Nat} (hlt : l < 2 * k.cur_vars) (hf : k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1]) := by
  obtain ⟨i, hi, htrl⟩ := (hw.vals_false_iff l hlt).mp hf
  have hl0 : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le i hi; omega
  have hent := hw.level0_sound i hi hl0
  rwa [htrl] at hent

private theorem m6_entails_resolve_unit {F : CNF Nat} {p q : Nat}
    (hp : F.EntailsClause (cnfClause [p ^^^ 1])) (hpq : F.EntailsClause (cnfClause [p, q])) :
    F.EntailsClause (cnfClause [q]) := by
  rw [CNF.entails_clause_def] at hp hpq ⊢
  intro β hβ
  have h1 := hp β hβ
  have h2 := hpq β hβ
  rw [show p ^^^ 1 = litNeg p from rfl, sat_cnfClause_litNeg_iff] at h1
  obtain ⟨x, hx, hxs⟩ := (clause_sat_cnfClause_iff β [p, q]).mp h2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hxp | hxq
  · exact absurd ((sat_cnfClause_singleton β p).mpr (hxp ▸ hxs)) h1
  · exact (sat_cnfClause_singleton β q).mpr (hxq ▸ hxs)

private theorem m6_lvl0_clause_unit_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hcl0 : s.core.cur_level = 0)
    {cr unit : Nat} (hcr : cr ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cr = false)
    (hall : ∀ l ∈ fullArenaClauseLits s cr, l = unit ∨ s.core.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [unit]) := by
  rw [CNF.entails_clause_def]; intro β hβ
  have hent_cr := CNF.entails_clause_def.mp (hw.arena.entails cr hcr hng) β hβ
  obtain ⟨l, hl, hs⟩ := (clause_sat_cnfClause_iff β _).mp hent_cr
  rcases hall l hl with rfl | hf
  · exact (sat_cnfClause_singleton β l).mpr hs
  · exfalso
    have hlt := hw.arena.lits_lt cr hcr hng l hl
    have hent_l := CNF.entails_clause_def.mp (m6_lvl0_false_entails hw hcl0 hlt hf) β hβ
    have hneg := (sat_cnfClause_litNeg_iff β l).mp hent_l
    exact absurd ((sat_cnfClause_singleton β l).mpr hs) hneg

private theorem m6_lvl0_unit_contra_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {l : Nat} (hlt : l < 2 * k.cur_vars) (hf : k.vals[l]?.getD 0#8 = 0xFF#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [l])) :
    (cnfOfClauses F_cur).Unsat := by
  refine unsat_of_entails_nil (entails_of_mem_or_false hent fun x hx => ?_)
  simp only [List.mem_singleton] at hx; rw [hx]; right
  obtain ⟨i, hi, htrl⟩ := (hw.vals_false_iff l hlt).mp hf
  have hl0 : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le i hi; omega
  have hs := hw.level0_sound i hi hl0; rwa [htrl] at hs

/-- Fixed-`F_cur` level-0 `full_assign_lvl` transition preserving `FullDenseInvW`. -/
theorem assignLvl0_preserves_denseInvW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s) {lit : BitVec 32}
    {flags' : List (BitVec 32)} {unassigned' unflushed' : BitVec 64} {phases' : List (BitVec 8)}
    (hfll : flags'.length = c.max_vars) (hphl : phases'.length = c.max_vars)
    (hlit : lit.toNat < 2 * s.core.cur_vars)
    (hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat])) :
    let v := lit.toNat / 2
    let s' : FullState :=
      { s with
        core :=
          { s.core with
            vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := s.core.lvl.set v 0#32
            rsns := s.core.rsns.set v 0xFFFFFFFF#32
            trl := s.core.trl.set s.core.trail_end lit
            trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
            trail_end := s.core.trail_end + 1
            unassigned := unassigned', unflushed := unflushed' }
        scratch := { s.scratch with phases := phases' } }
    FullDenseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro v s'
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok; have hw := hinv.2.1
  have hcl0 := hinv.2.2.2.2.2.1
  have hte_lt : s.core.trail_end < s.core.cur_vars := hw.trail_end_lt_of_unassigned hlit hun
  have hnot_var : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hw.vals_zero_iff hlit).mp hun
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hv_lt : v < c.max_vars := by have := hcl.cur_vars_le; omega
  have hte_max : s.core.trail_end < c.max_vars := by have := hcl.cur_vars_le; omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by have := fullInv_max_vars_lt32 c; omega
  have htrl_get : ∀ i < s.core.trail_end + 1,
      (s'.core.trl[i]?.getD 0#32).toNat =
        if i = s.core.trail_end then lit.toNat else (s.core.trl[i]?.getD 0#32).toNat :=
    fun i _ => by
      by_cases he : i = s.core.trail_end
      · subst he; simp [s', List.getElem?_set_self (by rw [hcl.trl_len]; exact hte_max)]
      · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_get : ∀ w < s.core.cur_vars,
      (s'.core.lvl[w]?.getD 0#32).toNat =
        if w = v then 0 else (s.core.lvl[w]?.getD 0#32).toNat := fun w _ => by
    by_cases he : w = v
    · subst he; simp [s', List.getElem?_set_self (by rw [hcl.lvl_len]; exact hv_lt)]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * s.core.cur_vars,
      s'.core.vals[l]?.getD 0#8 =
        if l = lit.toNat ^^^ 1 then 0xFF#8 else if l = lit.toNat then 1#8
        else s.core.vals[l]?.getD 0#8 := fun l hl => by
    have hcm := hcl.cur_vars_le
    by_cases h1 : l = lit.toNat ^^^ 1
    · subst h1; dsimp only [s']; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by simp [hcl.vals_len]; omega)]; rfl
    · dsimp only [s']; simp only [h1, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = lit.toNat
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hcl.vals_len]; omega)]; rfl
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  have hrsn_get : ∀ w < s.core.cur_vars,
      s'.core.rsns[w]?.getD 0xFFFFFFFF#32 =
        if w = v then 0xFFFFFFFF#32 else s.core.rsns[w]?.getD 0xFFFFFFFF#32 := fun w _ => by
    by_cases he : w = v
    · subst he; simp [s', List.getElem?_set_self (by rw [hcl.rsns_len]; exact hv_lt)]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with
       vals_len := by simp [s', hcl.vals_len], flags_len := hfll,
       lvl_len := by simp [s', hcl.lvl_len], rsns_len := by simp [s', hcl.rsns_len],
       trl_len := by simp [s', hcl.trl_len], trail_pos_len := by simp [s', hcl.trail_pos_len],
       trail_end_le := by dsimp [s']; omega,
       propagated_le := by have := hcl.propagated_le; dsimp [s']; omega },
     { hsc with phases_len := hphl }⟩
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r)
      cur_level_le := by change s.core.cur_level ≤ s.core.trail_end + 1; omega
      trail_lits_lt := fun i hi => by
        change i < s.core.trail_end + 1 at hi
        change (s'.core.trl[i]?.getD 0#32).toNat < 2 * s.core.cur_vars
        rw [htrl_get i hi]; split
        · exact hlit
        · exact hw.trail_lits_lt i (by omega)
      trail_vars_nodup := fun i j hi hj hveq => by
        change i < s.core.trail_end + 1 at hi; change j < s.core.trail_end + 1 at hj
        change (s'.core.trl[i]?.getD 0#32).toNat / 2 =
          (s'.core.trl[j]?.getD 0#32).toNat / 2 at hveq
        rw [htrl_get i hi, htrl_get j hj] at hveq
        split at hveq <;> split at hveq
        · omega
        · exact absurd hveq.symm (hnot_var j (by omega))
        · exact absurd hveq (hnot_var i (by omega))
        · exact hw.trail_vars_nodup i j (by omega) (by omega) hveq
      vals_domain := fun l hl => by
        change l < 2 * s.core.cur_vars at hl; rw [hvals_get l hl]
        split; · exact Or.inr (Or.inr rfl)
        split; · exact Or.inr (Or.inl rfl)
        exact hw.vals_domain l hl
      vals_true_iff := fun l hl => by
        change l < 2 * s.core.cur_vars at hl
        change s'.core.vals[l]?.getD 0#8 = 1#8 ↔
          ∃ i < s.core.trail_end + 1, (s'.core.trl[i]?.getD 0#32).toNat = l
        rw [hvals_get l hl]; constructor
        · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
          · simp [hneg] at h1
          · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
            · exact ⟨s.core.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hpos]⟩
            · simp only [hpos, ↓reduceIte] at h1
              obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
              exact ⟨i, by omega,
                by rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
          by_cases hie : i = s.core.trail_end
          · simp only [hie, ↓reduceIte] at heq; subst heq; simp [Ne.symm hne_lit]
          · simp only [hie, ↓reduceIte] at heq
            have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
            have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
            have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
            simp only [h1, h2, ↓reduceIte]; exact (hw.vals_true_iff l hl).mpr ⟨i, by omega, heq⟩
      vals_false_iff := fun l hl => by
        change l < 2 * s.core.cur_vars at hl
        change s'.core.vals[l]?.getD 0#8 = 0xFF#8 ↔
          ∃ i < s.core.trail_end + 1, (s'.core.trl[i]?.getD 0#32).toNat = l ^^^ 1
        rw [hvals_get l hl]; constructor
        · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
          · exact ⟨s.core.trail_end, by omega, by
              rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hneg]
              exact (litNeg_litNeg _).symm⟩
          · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
            · simp [hpos] at h1
            · simp only [hpos, ↓reduceIte] at h1
              obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h1
              exact ⟨i, by omega,
                by rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
          by_cases hie : i = s.core.trail_end
          · simp only [hie, ↓reduceIte] at heq
            have hl_eq : l = lit.toNat ^^^ 1 := by
              have h := congrArg litNeg heq; have h1 : litNeg (l ^^^ 1) = l := litNeg_litNeg l
              rw [h1] at h; exact h.symm
            simp [hl_eq]
          · simp only [hie, ↓reduceIte] at heq
            have hlv : l / 2 ≠ v := by
              have h := hnot_var i (by omega); rw [heq] at h; rwa [fullInv_var_xor1] at h
            have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
            have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
            simp only [h1, h2, ↓reduceIte]; exact (hw.vals_false_iff l hl).mpr ⟨i, by omega, heq⟩
      lvl_le := fun i hi => by
        change i < s.core.trail_end + 1 at hi
        change (s'.core.lvl[(s'.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          s.core.cur_level
        rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp
        · have hilt : i < s.core.trail_end := by omega
          simp only [hie, ↓reduceIte]; rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)]
          simp only [hnot_var i hilt, ↓reduceIte]; exact hw.lvl_le i hilt
      dec_earliest := fun i j hi hj hleq hdec => by
        change i < s.core.trail_end + 1 at hi; change j < s.core.trail_end + 1 at hj
        change _ = _ at hleq; change 0 < _ ∧ _ at hdec
        rw [htrl_get i hi] at hleq; rw [htrl_get j hj] at hleq hdec
        by_cases hje : j = s.core.trail_end
        · subst hje; simp only [↓reduceIte] at hdec
          rw [hlvl_get v (by omega)] at hdec; simp at hdec
        · by_cases hie : i = s.core.trail_end
          · subst hie; simp only [↓reduceIte] at hleq
            have hjlt : j < s.core.trail_end := by omega
            simp only [hje, ↓reduceIte] at hleq hdec
            rw [hlvl_get v (by omega),
              hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega)] at hleq
            rw [hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega)] at hdec
            simp only [↓reduceIte, hnot_var j hjlt] at hleq hdec; omega
          · have hilt : i < s.core.trail_end := by omega
            have hjlt : j < s.core.trail_end := by omega
            simp only [hie, hje, ↓reduceIte] at hleq hdec
            rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega),
              hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega)] at hleq
            rw [hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega),
              hrsn_get _ (by have := hw.trail_lits_lt j hjlt; omega)] at hdec
            simp only [hnot_var i hilt, hnot_var j hjlt, ↓reduceIte] at hleq hdec
            exact hw.dec_earliest i j hilt hjlt hleq hdec
      levels_inhabited := fun L hL1 hLle => by change L ≤ s.core.cur_level at hLle; omega
      level0_sound := fun i hi hli => by
        change i < s.core.trail_end + 1 at hi
        change (s'.core.lvl[(s'.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 at hli
        change (cnfOfClauses F_cur).EntailsClause (cnfClause [(s'.core.trl[i]?.getD 0#32).toNat])
        rw [htrl_get i hi] at hli ⊢
        by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte] at hli ⊢; exact hent
        · have hilt : i < s.core.trail_end := by omega
          simp only [hie, ↓reduceIte] at hli ⊢
          rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)] at hli
          simp only [hnot_var i hilt, ↓reduceIte] at hli; exact hw.level0_sound i hilt hli
      trail_pos_inv := fun i hi => by
        change i < s.core.trail_end + 1 at hi
        change (s'.core.trail_pos[(s'.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = i
        rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
        · subst hie; simp only [↓reduceIte]; dsimp only [s']
          rw [List.getElem?_set_self (by rw [hcl.trail_pos_len]; exact hv_lt),
            Option.getD_some, bv32_ofNat_toNat hte_lt32]
        · have hilt : i < s.core.trail_end := by omega
          simp only [hie, ↓reduceIte]; dsimp only [s']
          rw [List.getElem?_set_ne (Ne.symm (hnot_var i hilt))]; exact hw.trail_pos_inv i hilt
      level0_rsn_none := fun idx hidx hli => by
        change idx < s.core.trail_end + 1 at hidx
        change (s'.core.lvl[(s'.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 at hli
        change s'.core.rsns[(s'.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
          0xFFFFFFFF#32
        rw [htrl_get idx hidx] at hli ⊢
        by_cases hie : idx = s.core.trail_end
        · simp only [hie, ↓reduceIte]; rw [hrsn_get v (by omega)]; simp
        · have hilt : idx < s.core.trail_end := by omega
          simp only [hie, ↓reduceIte] at hli ⊢
          rw [hlvl_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hli
          rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)]
          simp only [hnot_var idx hilt, ↓reduceIte] at hli ⊢
          exact hw.level0_rsn_none idx hilt hli
      frame_trail_lt := fun L hL => by
        change L ≤ s.core.cur_level at hL
        exact Nat.le_trans (hw.frame_trail_lt L hL) (Nat.le_succ _)
      frame_trail_mono := hw.frame_trail_mono
      frame_trail_before_lt := fun L hL1 hLle => by change L ≤ s.core.cur_level at hLle; omega
      frame_dec_lt := fun L hL1 hLle => by change L ≤ s.core.cur_level at hLle; omega
      reason_inv := fun idx hidx hne => by
        change idx < s.core.trail_end + 1 at hidx
        change s'.core.rsns[(s'.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
          0xFFFFFFFF#32 at hne
        rw [htrl_get idx hidx] at hne
        have hilt : idx < s.core.trail_end := by
          by_cases hie : idx = s.core.trail_end
          · simp only [hie, ↓reduceIte] at hne; rw [hrsn_get v (by omega)] at hne; simp at hne
          · omega
        have hl0 : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
          have := hw.lvl_le idx hilt; omega
        simp only [show idx ≠ s.core.trail_end by omega, ↓reduceIte] at hne
        rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hne
        simp only [hnot_var idx hilt, ↓reduceIte] at hne
        exact absurd (hw.level0_rsn_none idx hilt hl0) hne
      reason_lit_mem := fun idx hidx hne _ => by
        change idx < s.core.trail_end + 1 at hidx
        change s'.core.rsns[(s'.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
          0xFFFFFFFF#32 at hne
        rw [htrl_get idx hidx] at hne
        have hilt : idx < s.core.trail_end := by
          by_cases hie : idx = s.core.trail_end
          · simp only [hie, ↓reduceIte] at hne; rw [hrsn_get v (by omega)] at hne; simp at hne
          · omega
        have hl0 : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
          have := hw.lvl_le idx hilt; omega
        simp only [show idx ≠ s.core.trail_end by omega, ↓reduceIte] at hne
        rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hne
        simp only [hnot_var idx hilt, ↓reduceIte] at hne
        exact absurd (hw.level0_rsn_none idx hilt hl0) hne }
  exact ⟨⟨hlen', hw', hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hcl0, hinv.2.2.2.2.2.2⟩, rfl⟩

private theorem m6_markGarb_preserves_denseInvW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (ag' : BitVec 64) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullDenseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have hcl := hinv.1.core_ok; have hw := hinv.2.1; have hcl0 := hinv.2.2.2.2.2.1
  have hmg := hw.arena.markGarb hcl href ag'
  have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := hmg.1
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with arena_len_arr := by simp [s', hcl.arena_len_arr] }, hinv.1.scratch_ok⟩
  have hnd' : FullArenaVarsNodup s' :=
    FullArenaVarsNodup.of_markGarb ⟨hinv.1, F_cur, hw⟩ hinv.2.2.2.1 href ag'
  have hno_rsn : ∀ idx < s.core.trail_end,
      s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun idx hidx => hw.level0_rsn_none idx hidx (by have := hw.lvl_le idx hidx; omega)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := hmg.2
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl
        fun r hr => by change r ∈ fullArenaClauseRefs s'; rw [hrefs]; exact hr
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne }
  exact ⟨⟨hlen', hw', hinv.2.2.1, hnd',
    FullExtScratchOk.of_pres hinv.2.2.2.2.1 ⟨rfl, rfl⟩ (fun r hr => hrefs ▸ hr),
    hcl0, hinv.2.2.2.2.2.2⟩, hrefs⟩

private theorem m6_denseInvW_set_inconsistent {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    (ct c0 c1 cr : BitVec 64) (huns : (cnfOfClauses F_cur).Unsat) :
    FullDenseInvW c F0 F_cur
      { s with core :=
        { s.core with inconsistent := 1#64, confl_type := ct,
                      confl_lit0 := c0, confl_lit1 := c1, confl_ref := cr } } := by
  have hcl := hinv.1.core_ok; have hw := hinv.2.1
  let s' : FullState :=
    { s with core :=
      { s.core with inconsistent := 1#64, confl_type := ct,
                    confl_lit0 := c0, confl_lit1 := c1, confl_ref := cr } }
  have hlen' : s'.LengthsOk c := ⟨{ hcl with vals_len := hcl.vals_len }, hinv.1.scratch_ok⟩
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      inconsistent_sound := fun _ => huns
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  exact ⟨hlen', hw', hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1,
    hinv.2.2.2.2.2.2⟩

private theorem m6_denseInvW_set_propagated {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {prop' : Nat} (hle : prop' ≤ s.core.trail_end) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with propagated := prop' } } :=
  ⟨⟨{ hinv.1.core_ok with propagated_le := hle }, hinv.1.scratch_ok⟩,
   { hinv.2.1 with
     arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
     watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem m6_or_garb_mask (hdr : BitVec 32) :
    (hdr &&& 0x00080000#32) = 0#32 → (hdr &&& 0x00080000#32) = 0#32 := id

private theorem m6_getElem_congr {α : Type} {xs : List α} {i j : Nat}
    (hij : i = j) (hi : i < xs.length) (hj : j < xs.length) :
    xs[i]'hi = xs[j]'hj := by subst hij; rfl

/-! ## 2. `full_m6_dense_prop_lit_wp` (`15/39`) -/

private structure M6PropLitLoop (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sL : FullState) (not_lit p endW : BitVec 64) : Prop where
  dinv : FullDenseInvW c F0 F_cur sL
  cv : sL.core.cur_vars = s.core.cur_vars
  fuel : sL.core.fuel = s.core.fuel
  prop : sL.core.propagated = s.core.propagated
  te : s.core.trail_end ≤ sL.core.trail_end
  repr : sL.core.repr = s.core.repr
  alen : sL.core.arena_len = s.core.arena_len
  refs : fullArenaClauseRefs sL = fullArenaClauseRefs s
  tmk : sL.scratch.tarjan_mark = s.scratch.tarjan_mark
  trh : sL.scratch.tarjan_reach = s.scratch.tarjan_reach
  scr : sL.scratch.scratch_buf = s.scratch.scratch_buf
  ws1 : sL.scratch.work_stk1 = s.scratch.work_stk1
  ws2 : sL.scratch.work_stk2 = s.scratch.work_stk2
  inc : sL.core.inconsistent = s.core.inconsistent
  ple : p.toNat ≤ endW.toNat
  endle : endW.toNat ≤ sL.core.wlen
  slice : DenseWatchSliceOk F_cur sL.core not_lit.toNat p.toNat (endW.toNat - p.toNat)

private theorem m6_propLitLoop_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} {not_lit p endW : BitVec 64}
    (hlp : M6PropLitLoop c F0 F_cur s sL not_lit p endW) {p' : BitVec 64}
    (hp' : p'.toNat ≤ endW.toNat)
    (hsl : DenseWatchSliceOk F_cur sL.core not_lit.toNat p'.toNat (endW.toNat - p'.toNat)) :
    M6PropLitLoop c F0 F_cur s sL not_lit p' endW :=
  ⟨hlp.dinv, hlp.cv, hlp.fuel, hlp.prop, hlp.te, hlp.repr, hlp.alen, hlp.refs,
   hlp.tmk, hlp.trh, hlp.scr, hlp.ws1, hlp.ws2, hlp.inc, hp', hlp.endle, hsl⟩

private theorem m6_propLitLoop_markGarb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} {not_lit p endW : BitVec 64}
    (hlp : M6PropLitLoop c F0 F_cur s sL not_lit p endW)
    {cr p2 : BitVec 64} (hcr_ref : cr.toNat ∈ fullArenaClauseRefs sL)
    (hcr_lt : cr.toNat < sL.core.arena.length) (ag' : BitVec 64)
    (hp2 : p2.toNat ≤ endW.toNat)
    (hsl : DenseWatchSliceOk F_cur sL.core not_lit.toNat p2.toNat (endW.toNat - p2.toNat)) :
    let hdr := sL.core.arena[cr.toNat]'hcr_lt
    let s' : FullState :=
      { sL with core :=
        { sL.core with
          arena := sL.core.arena.set cr.toNat (hdr ||| 0x00080000#32)
          arena_garbage := ag' } }
    M6PropLitLoop c F0 F_cur s s' not_lit p2 endW := by
  intro hdr s'
  have hhdr : fullArenaHdr sL cr.toNat = hdr := by
    unfold fullArenaHdr fullArenaHdrCore
    rw [List.getElem?_eq_getElem hcr_lt, Option.getD_some]
  obtain ⟨hd, hrefs⟩ := m6_markGarb_preserves_denseInvW hlp.dinv hcr_ref ag'
  rw [hhdr] at hd hrefs
  have hsub : ∀ r ∈ fullArenaClauseRefsCore sL.core, r ∈ fullArenaClauseRefsCore s'.core :=
    fun r hr => by change r ∈ fullArenaClauseRefs s'; rw [hrefs]; exact hr
  exact ⟨hd, hlp.cv, hlp.fuel, hlp.prop, hlp.te, hlp.repr, hlp.alen, hrefs.trans hlp.refs,
    hlp.tmk, hlp.trh, hlp.scr, hlp.ws1, hlp.ws2, hlp.inc, hp2, hlp.endle,
    m6_denseSlice_congr (k := sL.core) (k' := s'.core) rfl rfl hsub hsl⟩

private theorem m6_propLitLoop_assignLvl0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} {not_lit p endW : BitVec 64}
    (hlp : M6PropLitLoop c F0 F_cur s sL not_lit p endW)
    {lit : BitVec 32} {flags' : List (BitVec 32)} {unass' : BitVec 64}
    {phases' : List (BitVec 8)} {p_nxt : BitVec 64}
    (hfll : flags'.length = c.max_vars) (hphl : phases'.length = c.max_vars)
    (hlit : lit.toNat < 2 * sL.core.cur_vars)
    (hun : sL.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hp_le : p_nxt.toNat ≤ endW.toNat)
    (hsl : DenseWatchSliceOk F_cur sL.core not_lit.toNat p_nxt.toNat (endW.toNat - p_nxt.toNat)) :
    let v := lit.toNat / 2
    let s' : FullState :=
      { sL with
        core :=
          { sL.core with
            vals := (sL.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := sL.core.lvl.set v 0#32
            rsns := sL.core.rsns.set v 0xFFFFFFFF#32
            trl := sL.core.trl.set sL.core.trail_end lit
            trail_pos := sL.core.trail_pos.set v (BitVec.ofNat 32 sL.core.trail_end)
            trail_end := sL.core.trail_end + 1
            unassigned := unass', unflushed := sL.core.unflushed + 1#64 }
        scratch := { sL.scratch with phases := phases' } }
    M6PropLitLoop c F0 F_cur s s' not_lit p_nxt endW := by
  intro v s'
  obtain ⟨hd, hrefs⟩ := assignLvl0_preserves_denseInvW hlp.dinv hfll hphl hlit hun hent
  exact ⟨hd, hlp.cv, hlp.fuel, hlp.prop, Nat.le_trans hlp.te (Nat.le_succ _), hlp.repr, hlp.alen,
    hrefs.trans hlp.refs, hlp.tmk, hlp.trh, hlp.scr, hlp.ws1, hlp.ws2, hlp.inc, hp_le, hlp.endle,
    m6_denseSlice_congr (k := sL.core) (k' := s'.core) rfl rfl (fun _ h => h) hsl⟩

private theorem m6_propLitLoop_exit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} {not_lit p endW : BitVec 64} {m' : Mem 64} {R : Mem 64 → Prop}
    {Q : Post [.bool]} (hlp : M6PropLitLoop c F0 F_cur s sL not_lit p endW)
    (hm' : (FullMem c sL ⋆ R) m')
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.propagated = s.core.propagated →
      s.core.trail_end ≤ s'.core.trail_end → s'.core.repr = s.core.repr →
      s'.core.arena_len = s.core.arena_len →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (ok = true → s'.core.inconsistent = s.core.inconsistent) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Q (true, ()) m' :=
  hQ true sL m' hlp.dinv hlp.cv hlp.fuel hlp.prop hlp.te hlp.repr hlp.alen hlp.refs
    hlp.tmk hlp.trh hlp.scr hlp.ws1 hlp.ws2 (fun h => Bool.noConfusion h)
    (fun _ => hlp.inc) hm'

private theorem m6_propLitLoop_conflict {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} {not_lit p endW : BitVec 64} {ct c0 c1 cr : BitVec 64}
    {m' : Mem 64} {R : Mem 64 → Prop} {Q : Post [.bool]}
    (hlp : M6PropLitLoop c F0 F_cur s sL not_lit p endW) (huns : (cnfOfClauses F_cur).Unsat)
    (hm' : (FullMem c { sL with core :=
        { sL.core with
          inconsistent := 1#64, confl_type := ct, confl_lit0 := c0,
          confl_lit1 := c1, confl_ref := cr } } ⋆ R) m')
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.propagated = s.core.propagated →
      s.core.trail_end ≤ s'.core.trail_end → s'.core.repr = s.core.repr →
      s'.core.arena_len = s.core.arena_len →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (ok = true → s'.core.inconsistent = s.core.inconsistent) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Q (false, ()) m' :=
  hQ false _ m' (m6_denseInvW_set_inconsistent hlp.dinv ct c0 c1 cr huns)
    hlp.cv hlp.fuel hlp.prop hlp.te hlp.repr hlp.alen hlp.refs hlp.tmk hlp.trh
    hlp.scr hlp.ws1 hlp.ws2 (fun _ => ⟨hlp.dinv.2.1.ext_sound.2 huns, by dsimp only; decide⟩)
    (fun h => Bool.noConfusion h) hm'

/-- `15/39`: Parametric `Func.wp` proof for `full_m6_dense_prop_lit`. -/
theorem full_m6_dense_prop_lit_wp (Γ : Env)
    (hAsg : M6EnvSpec Γ "full_assign_lvl" Full.fullAssignLvlSpec) :
    ∀ args m Q X, m6DensePropLitSpec args m Q X →
      Func.wp Γ full_m6_dense_prop_lit_body args m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinv, hm, hQ⟩
  have hcl := hinv.1.core_ok; have hw := hinv.2.1; have hcl0 := hinv.2.2.2.2.2.1
  have hmx := c.hmaxv; have har := c.harena; have hwc := c.hwcap
  unfold dimacsBound at hmx har hwc
  have hret_noop : ∀ (m' : Mem 64), (FullMem c s ⋆ R) m' → Q (true, ()) m' := fun m' hm' =>
    hQ true s m' hinv rfl rfl rfl (Nat.le_refl _) rfl rfl rfl rfl rfl rfl rfl rfl
      (fun h => Bool.noConfusion h) (fun _ => rfl) hm'
  c0_hsplit
  · -- `nlits ≤ not_lit`: immediate return `true`
    c0_hsteps!; exact hret_noop m hm
  · have hcv_le := hcl.cur_vars_le
    have hnot_lt_xor : lit.toNat ^^^ 1 < 2 * s.core.cur_vars := by bv_omega
    have hnot_lt : (lit ^^^ 1#32).toNat < 2 * s.core.cur_vars := by
      simpa [m6_bv32_xor1_toNat] using hnot_lt_xor
    have hnot_vl : (lit ^^^ 1#32).toNat < s.core.vals.length := by
      rw [hcl.vals_len]; omega
    c0_hsplit
    · -- `0 ≤ vals[not_lit]`: immediate return `true`
      c0_hsteps!; exact hret_noop m hm
    · have hnot_ge0_f : (0#8).sle (s.core.vals[(lit ^^^ 1#32).toNat]?.getD 0#8) = false := by
        rw [List.getElem?_eq_getElem hnot_vl, Option.getD_some]
        simpa only [m6_bv32_xor1_toNat] using ‹(0#8).sle _ = false›
      have hnot_fals : s.core.vals[(lit ^^^ 1#32).toNat]?.getD 0#8 = 0xFF#8 :=
        m6_vals_ge0_false (hw.vals_domain _ hnot_lt) hnot_ge0_f
      have hnot_ent : (cnfOfClauses F_cur).EntailsClause
          (cnfClause [(lit ^^^ 1#32).toNat ^^^ 1]) :=
        m6_lvl0_false_entails hw hcl0 hnot_lt hnot_fals
      have h2not0 : 2 * (lit.toNat ^^^ 1) < s.core.wvec.length := by
        rw [hcl.wvec_len]; omega
      have h2not1 : 2 * (lit.toNat ^^^ 1) + 1 < s.core.wvec.length := by
        rw [hcl.wvec_len]; omega
      have hdw0 : DenseWatchesInv F_cur s.core := by
        have hwm := hw.watches; unfold ModeWatchesInv at hwm
        rw [ite_eq_right (fun h0 => hinv.2.2.2.2.2.2 h0)] at hwm; exact hwm
      have hbd0 := hdw0.layout.bounds _ hnot_lt
      have hslice0 : DenseWatchSliceOk F_cur s.core (lit ^^^ 1#32).toNat
          (fullWatchOffCore s.core (lit ^^^ 1#32).toNat)
          (fullWatchSizeCore s.core (lit ^^^ 1#32).toNat) :=
        hdw0.slices _ hnot_lt
      let off0 := s.core.wvec[2 * (lit ^^^ 1#32).toNat]?.getD 0#32
      let sz0 := s.core.wvec[2 * (lit ^^^ 1#32).toNat + 1]?.getD 0#32
      have hoff0_def : off0.toNat = fullWatchOffCore s.core (lit ^^^ 1#32).toNat := rfl
      have hsz0_def : sz0.toNat = fullWatchSizeCore s.core (lit ^^^ 1#32).toNat := rfl
      have hoff0_eq : s.core.wvec[2 * (lit.toNat ^^^ 1) % 2 ^ 64]'(by
          rw [Nat.mod_eq_of_lt (by omega)]; exact h2not0) = off0 := by
        dsimp only [off0]
        have hlt64 : 2 * (lit ^^^ 1#32).toNat < 2 ^ 64 := by omega
        have h2' : 2 * (lit ^^^ 1#32).toNat < s.core.wvec.length := by
          simpa only [← m6_bv32_xor1_toNat] using h2not0
        rw [List.getElem?_eq_getElem h2', Option.getD_some]
        congr 1
        rw [← m6_bv32_xor1_toNat, Nat.mod_eq_of_lt (by omega)]
      have hsz0_eq : s.core.wvec[(2 * (lit.toNat ^^^ 1) + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
          change (2 * (lit.toNat ^^^ 1) + 1) % 2 ^ 64 < s.core.wvec.length
          rw [Nat.mod_eq_of_lt (by omega)]; exact h2not1) = sz0 := by
        dsimp only [sz0]
        have hlt64 : 2 * (lit ^^^ 1#32).toNat + 1 < 2 ^ 64 := by omega
        have h2' : 2 * (lit ^^^ 1#32).toNat + 1 < s.core.wvec.length := by
          simpa only [← m6_bv32_xor1_toNat] using h2not1
        rw [List.getElem?_eq_getElem h2', Option.getD_some]
        congr 1
        have h1 : (1 : BitVec 64).toNat = 1 := rfl
        rw [h1, ← m6_bv32_xor1_toNat, Nat.mod_eq_of_lt (by omega)]
      have hend64 : (off0.setWidth 64 + sz0.setWidth 64).toNat =
          off0.toNat + sz0.toNat := by bv_omega
      have hoff0_shl_idx :
          ((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)).toNat =
            2 * (lit.toNat ^^^ 1) % 2 ^ 64 := by
        rw [m6_bv64_shl1_nat, bv_c0_zext32_64, m6_bv32_xor1_ofnat]
      have hoff0_shl :
          s.core.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)).toNat]'(by
            rw [hoff0_shl_idx, Nat.mod_eq_of_lt (by omega)]; exact h2not0) = off0 := by
        simp only [hoff0_shl_idx]; exact hoff0_eq
      c0_hsteps_nogrp
      refine wp_while_break_state
        (brkTs := [i64]) (lpTs := [i64]) (β := BitVec 64 × FullState)
        (fun b => (b.1, ()))
        (fun b mb => M6PropLitLoop c F0 F_cur s b.2 ((lit ^^^ 1#32).setWidth 64) b.1
          (off0.setWidth 64 + sz0.setWidth 64) ∧ (FullMem c b.2 ⋆ R) mb)
        (α := BitVec 64 × FullState) (fun st => (st.1, ()))
        (fun st => (off0.setWidth 64 + sz0.setWidth 64).toNat - st.1.toNat)
        (fun st ml => M6PropLitLoop c F0 F_cur s st.2 ((lit ^^^ 1#32).setWidth 64) st.1
          (off0.setWidth 64 + sz0.setWidth 64) ∧ (FullMem c st.2 ⋆ R) ml)
        ?_ ?_ ?_
      · rintro B ⟨_, sB⟩ mB ⟨hlpB, hmB⟩
        c0_hsteps!; exact m6_propLitLoop_exit hlpB hmB hQ
      · rintro B L ⟨pL, sL⟩ mL hB hL ⟨hlpL, hmL⟩
        dsimp only at hlpL hmL
        c0_hsplit
        · -- `pL < endW`
          have hp_lt : pL.toNat < (off0.setWidth 64 + sz0.setWidth 64).toNat := by
            have hc1 : pL.toNat <
                ((s.core.wvec[2 * (lit.toNat ^^^ 1) % 2 ^ 64]'(by
                    rw [Nat.mod_eq_of_lt (by omega)]; exact h2not0)).toNat +
                  (s.core.wvec[(2 * (lit.toNat ^^^ 1) + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
                    change (2 * (lit.toNat ^^^ 1) + 1) % 2 ^ 64 < s.core.wvec.length
                    rw [Nat.mod_eq_of_lt (by omega)]; exact h2not1)).toNat) % 2 ^ 64 := ‹_›
            rw [hoff0_eq, hsz0_eq] at hc1
            rw [hend64]; bv_omega
          have hrem_pos : 0 < (off0.setWidth 64 + sz0.setWidth 64).toNat - pL.toNat := by omega
          have hclL := hlpL.dinv.1.core_ok
          have hwL := hlpL.dinv.2.1
          have hp_wlen : pL.toNat < sL.core.wstk.length := by
            rw [hclL.wstk_len_arr]; have := hclL.wlen_le; have := hlpL.endle; omega
          have hp1_nat : (pL + 1#64).toNat = pL.toNat + 1 := by bv_omega
          let w0 := sL.core.wstk[pL.toNat]'hp_wlen
          have hw0_get : sL.core.wstk[pL.toNat]? = some w0 := List.getElem?_eq_getElem hp_wlen
          c0_hsplit
          · -- Binary watch `(w0 &&& 0x80000000#32) ≠ 0#32`
            have hbin : (w0 &&& 0x80000000#32) ≠ 0#32 := ‹_›
            have hslL : DenseWatchSliceOk F_cur sL.core ((lit ^^^ 1#32).setWidth 64).toNat
                pL.toNat ((off0.setWidth 64 + sz0.setWidth 64).toNat - pL.toNat) := hlpL.slice
            rw [bv_c0_zext32_64] at hslL
            obtain ⟨_, hot_lt, hent_bin, hsl_nxt⟩ :=
              m6_denseSlice_step_bin hslL hrem_pos hw0_get hbin
            have hot_lt_L : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * sL.core.cur_vars := hot_lt
            have hot_ent : (cnfOfClauses F_cur).EntailsClause
                (cnfClause [(w0 &&& 0x7FFFFFFF#32).toNat]) :=
              m6_entails_resolve_unit hnot_ent hent_bin
            have hsl_nxt' : DenseWatchSliceOk F_cur sL.core
                ((lit ^^^ 1#32).setWidth 64).toNat (pL + 1#64).toNat
                ((off0.setWidth 64 + sz0.setWidth 64).toNat - (pL + 1#64).toNat) := by
              rw [bv_c0_zext32_64, hp1_nat, ← Nat.sub_sub]; exact hsl_nxt
            c0_hsplit
            · exfalso
              have hcvL_eq := hlpL.cv
              have hge : 2 * sL.core.cur_vars ≤ (w0 &&& 0x7FFFFFFF#32).toNat := by
                dsimp only [w0]; bv_omega
              omega
            · have hot_vl : ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat < sL.core.vals.length := by
                rw [hclL.vals_len, bv_c0_zext32_64]; have := hclL.cur_vars_le; omega
              c0_hsplit
              · -- `0 < vals[ot]`: already true, continue
                c0_hsteps!
                exact hL (pL + 1#64, sL) mL (by dsimp only; rw [hp1_nat]; omega)
                  ⟨m6_propLitLoop_step hlpL (by rw [hp1_nat]; omega) hsl_nxt', hmL⟩
              · c0_hsplit
                · -- `vals[ot] < 0`: binary conflict, return `false`
                  have hlt0 : (sL.core.vals[(w0 &&& 0x7FFFFFFF#32).toNat]?.getD 0#8).slt 0#8 =
                      true := by
                    rw [List.getElem?_eq_getElem (by rw [bv_c0_zext32_64] at hot_vl; exact hot_vl),
                      Option.getD_some]
                    exact ‹_›
                  have hfals_ot : sL.core.vals[(w0 &&& 0x7FFFFFFF#32).toNat]?.getD 0#8 =
                      0xFF#8 :=
                    (m6_vals_lt0_iff (hwL.vals_domain _ hot_lt_L)).mp hlt0
                  have huns := m6_lvl0_unit_contra_unsat hwL hlpL.dinv.2.2.2.2.2.1
                    hot_lt_L hfals_ot hot_ent
                  c0_hsteps!
                  exact m6_propLitLoop_conflict hlpL huns hm hQ
                · -- `vals[ot] == 0`: `full_assign_lvl(h, ot, 0xFFFFFFFF, 0)`, continue
                  have hw0_def : w0 = sL.core.wstk[pL.toNat]'hp_wlen := rfl
                  have hnp : (0#8).slt
                      (sL.core.vals[(w0 &&& 0x7FFFFFFF#32).toNat]?.getD 0#8) = false := by
                    rw [List.getElem?_eq_getElem (by rw [bv_c0_zext32_64] at hot_vl; exact hot_vl),
                      Option.getD_some]
                    exact ‹(0#8).slt _ = false›
                  have hnn : (sL.core.vals[(w0 &&& 0x7FFFFFFF#32).toNat]?.getD 0#8).slt 0#8 =
                      false := by
                    rw [List.getElem?_eq_getElem (by rw [bv_c0_zext32_64] at hot_vl; exact hot_vl),
                      Option.getD_some]
                    exact ‹BitVec.slt _ 0#8 = false›
                  have hun_ot : sL.core.vals[(w0 &&& 0x7FFFFFFF#32).toNat]?.getD 0#8 = 0#8 :=
                    m6_vals_eq0_of_np_nn (hwL.vals_domain _ hot_lt_L) hnp hnn
                  c0_call hAsg
                  refine ⟨c, sL, R, rfl, hlpL.dinv.1, hmL, ?_⟩
                  have hpre_f : ¬ (sL.core.cur_vars ≤ (w0 &&& 0x7FFFFFFF#32).toNat / 2 ∨
                      c.max_vars ≤ sL.core.trail_end ∨
                      sL.core.vals[(w0 &&& 0x7FFFFFFF#32).toNat]?.getD 0#8 ≠ 0#8) := by
                    have hte := hwL.trail_end_lt_of_unassigned hot_lt_L hun_ot
                    have := hclL.cur_vars_le
                    simp only [hun_ot, ne_eq, not_true_eq_false, or_false]; omega
                  have hmask : (2147483647 : BitVec 32) = 0x7FFFFFFF#32 := rfl
                  split
                  · next hcnd => exact absurd (by simpa only [← hw0_def, hmask] using hcnd) hpre_f
                  · dsimp only
                    intro flags' unass' phases' m' hfll hphl hm'
                    simp only [show ((0 : BitVec 32) = 0#32) = True from eq_true rfl, ↓reduceIte,
                      ← hw0_def] at hm'
                    let sA := { sL with
                      core := { sL.core with
                        vals := (sL.core.vals.set (w0 &&& 0x7FFFFFFF#32).toNat 1#8).set
                          ((w0 &&& 0x7FFFFFFF#32).toNat ^^^ 1) 0xFF#8
                        flags := flags'
                        lvl := sL.core.lvl.set ((w0 &&& 0x7FFFFFFF#32).toNat / 2) 0#32
                        rsns := sL.core.rsns.set ((w0 &&& 0x7FFFFFFF#32).toNat / 2) 0xFFFFFFFF#32
                        trl := sL.core.trl.set sL.core.trail_end (w0 &&& 0x7FFFFFFF#32)
                        trail_pos := sL.core.trail_pos.set
                          ((w0 &&& 0x7FFFFFFF#32).toNat / 2) (BitVec.ofNat 32 sL.core.trail_end)
                        trail_end := sL.core.trail_end + 1
                        unassigned := unass', unflushed := sL.core.unflushed + 1#64 }
                      scratch := { sL.scratch with phases := phases' } }
                    have hlpA := m6_propLitLoop_assignLvl0 hlpL (unass' := unass') hfll hphl
                      hot_lt_L hun_ot hot_ent (by rw [hp1_nat]; omega) hsl_nxt'
                    c0_hsteps!
                    exact hL (pL + 1#64, sA) m' (by dsimp only; rw [hp1_nat]; omega) ⟨hlpA, hm'⟩
          · -- Large occurrence branch `(w0 &&& 0x80000000#32) = 0#32`
            have hocc : (w0 &&& 0x80000000#32) = 0#32 := by
              first | exact ‹_› | exact Classical.not_not.mp ‹_›
            have hslL : DenseWatchSliceOk F_cur sL.core ((lit ^^^ 1#32).setWidth 64).toNat
                pL.toNat ((off0.setWidth 64 + sz0.setWidth 64).toNat - pL.toNat) := hlpL.slice
            rw [bv_c0_zext32_64] at hslL
            obtain ⟨hrem2, _, cr, hp1_get, hcr_lo31, hcr_ref, hsl_nxt⟩ :=
              m6_denseSlice_step_occ hslL hrem_pos hw0_get hocc
            have hp2_le : (pL + 1#64 + 1#64).toNat ≤
                (off0.setWidth 64 + sz0.setWidth 64).toNat := by bv_omega
            have hp2_nat : (pL + 1#64 + 1#64).toNat = pL.toNat + 2 := by bv_omega
            have hsl_nxt' : DenseWatchSliceOk F_cur sL.core
                ((lit ^^^ 1#32).setWidth 64).toNat (pL + 1#64 + 1#64).toNat
                ((off0.setWidth 64 + sz0.setWidth 64).toNat - (pL + 1#64 + 1#64).toNat) := by
              rw [bv_c0_zext32_64, hp2_nat, ← Nat.sub_sub]; exact hsl_nxt
            c0_hsplit
            · exfalso; have : (off0.setWidth 64 + sz0.setWidth 64).toNat ≤ (pL + 1#64).toNat := by
                bv_omega
              omega
            · have hp1_wlen : (pL + 1#64).toNat < sL.core.wstk.length := by
                rw [hclL.wstk_len_arr]; have := hclL.wlen_le; have := hlpL.endle; omega
              have hp1_ofnat : (pL + (1 : BitVec 64)).toNat = pL.toNat + 1 := hp1_nat
              have hp1_mod : (pL.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = pL.toNat + 1 := by
                have h1 : (1 : BitVec 64).toNat = 1 := rfl; rw [h1]; omega
              have hcr_eq_p1 : sL.core.wstk[pL.toNat + 1]'(by omega) = cr := by
                have hget : sL.core.wstk[pL.toNat + 1]? = some cr := hp1_get
                exact Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hget)
              have hwf_cr := hwL.arena.refs_wf cr.toNat hcr_ref
              have hcr_arlen : cr.toNat + 3 ≤ sL.core.arena_len := hwf_cr.1
              have hcr_fit : cr.toNat + 3 + fullArenaClauseSize sL cr.toNat ≤ sL.core.arena_len :=
                Nat.le_trans hwf_cr.2.2.1 hwf_cr.2.2.2.1
              have hcr_lt0 : cr.toNat < sL.core.arena.length := by
                have := hclL.arena_len_le; have := hclL.arena_len_arr; omega
              have hcr2_lt : (cr.setWidth 64 + 2#64).toNat < sL.core.arena.length := by
                have := hclL.arena_len_le; have := hclL.arena_len_arr
                have := c.harena; unfold dimacsBound at this; bv_omega
              have hcr2_nat : (cr.setWidth 64 + 2#64).toNat = cr.toNat + 2 := by bv_omega
              c0_hsplit
              · exfalso
                simp only [hp1_mod, hcr_eq_p1] at *
                have := hclL.arena_len_le; have := c.harena; unfold dimacsBound at this
                have hgt : sL.core.arena_len < (cr.setWidth 64 + 3#64).toNat := by bv_omega
                bv_omega
              · simp only [hp1_ofnat, hcr_eq_p1]
                let hdr := sL.core.arena[cr.toNat]'hcr_lt0
                let csz := sL.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_lt
                have hcsz_def : csz.toNat = fullArenaClauseSize sL cr.toNat := by
                  unfold fullArenaClauseSize fullArenaClauseSizeCore
                  rw [List.getElem?_eq_getElem (by rw [← hcr2_nat]; exact hcr2_lt),
                    Option.getD_some]
                  dsimp only [csz]
                  exact congrArg BitVec.toNat
                    (m6_getElem_congr hcr2_nat hcr2_lt
                      (by rw [← hcr2_nat]; exact hcr2_lt))
                have hcsz_idx : (cr.toNat + (2 : BitVec 64).toNat) % 2 ^ 64 =
                    (cr.setWidth 64 + 2#64).toNat := by bv_omega
                have hcsz_mod : sL.core.arena[(cr.toNat + (2 : BitVec 64).toNat) % 2 ^ 64]'(by
                    rw [hcsz_idx]; exact hcr2_lt) = csz := by
                  dsimp only [csz]; congr 1
                c0_hsplit
                · c0_hsteps!
                  exact hL (pL + 1#64 + 1#64, sL) mL
                    (by dsimp only; have := hp2_le; rw [hp2_nat] at this ⊢; omega)
                    ⟨m6_propLitLoop_step hlpL hp2_le hsl_nxt', hmL⟩
                · c0_hsplit
                  · c0_hsteps!
                    exact hL (pL + 1#64 + 1#64, sL) mL
                      (by dsimp only; have := hp2_le; rw [hp2_nat] at this ⊢; omega)
                      ⟨m6_propLitLoop_step hlpL hp2_le hsl_nxt', hmL⟩
                  · c0_hsplit
                    · exfalso
                      have := hclL.arena_len_le
                      have := c.harena; unfold dimacsBound at this
                      rw [← hcsz_def] at hcr_fit
                      bv_omega
                    · -- Valid non-garbage large clause scan!
                      have hgarb_zero : (hdr &&& 0x00080000#32) = 0#32 := by
                        have hm5 : (524288 : BitVec 32) = 0x00080000#32 := rfl
                        have h0v : (0 : BitVec 32) = 0#32 := rfl
                        change (sL.core.arena[cr.toNat]'hcr_lt0 &&& 0x00080000#32) = 0#32
                        rw [← hm5, ← h0v]; assumption
                      have hng : fullArenaClauseGarb sL cr.toNat = false := by
                        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                        rw [List.getElem?_eq_getElem hcr_lt0, Option.getD_some]
                        change ((hdr &&& 0x00080000#32) != 0#32) = false
                        rw [hgarb_zero]; rfl
                      have hbd_cr : cr.toNat + 3 + fullArenaClauseSize sL cr.toNat ≤
                          sL.core.arena.length := by
                        have := hclL.arena_len_le; have := hclL.arena_len_arr; omega
                      have hcl_lt_k : ∀ k (hk : k < csz.toNat),
                          (sL.core.arena[cr.toNat + 3 + k]'(by omega)).toNat <
                            2 * sL.core.cur_vars := fun k hk =>
                        hwL.arena.lits_lt cr.toNat hcr_ref hng _
                          ((mem_fullArenaClauseLitsCore_iff hbd_cr).mpr
                            ⟨k, by change k < fullArenaClauseSize sL cr.toNat
                                   rw [← hcsz_def]; exact hk, rfl⟩)
                      let ClScanInv (st : BitVec 32 × BitVec 32 × BitVec 32) : Prop :=
                        (st.1 = 0#32 ∨ st.1 = 1#32) ∧
                        st.2.2.toNat ≤ csz.toNat ∧
                        (st.1 = 0#32 → ∀ k < st.2.2.toNat,
                          let l := (sL.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat
                          sL.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
                        (st.1 = 1#32 →
                          st.2.1.toNat < 2 * sL.core.cur_vars ∧
                          sL.core.vals[st.2.1.toNat]?.getD 0#8 = 0#8 ∧
                          ∀ k < st.2.2.toNat,
                            let l := (sL.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat
                            l ≠ st.2.1.toNat → sL.core.vals[l]?.getD 0#8 = 0xFF#8)
                      let ClScanBrk (b : Bool × BitVec 32 × BitVec 32 × BitVec 32) : Prop :=
                        b.1 = false →
                          (b.2.1 = 0#32 → ∀ k < csz.toNat,
                            let l := (sL.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat
                            sL.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
                          (b.2.1 = 1#32 →
                            b.2.2.1.toNat < 2 * sL.core.cur_vars ∧
                            sL.core.vals[b.2.2.1.toNat]?.getD 0#8 = 0#8 ∧
                            ∀ k < csz.toNat,
                              let l := (sL.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat
                              l ≠ b.2.2.1.toNat → sL.core.vals[l]?.getD 0#8 = 0xFF#8)
                      refine wp_join_state (ts := [.bool, i32, i32, i32])
                        (proj := fun p : Bool × BitVec 32 × BitVec 32 × BitVec 32 =>
                          (p.1, p.2.1, p.2.2.1, p.2.2.2, ()))
                        (fun p m_sc => ClScanBrk p ∧ m_sc = mL) ?_ ?_
                      · rintro Jsc ⟨sat_v, nf_v, u_v, i_v⟩ m_sc ⟨hbrk, hm_sc⟩
                        subst m_sc; dsimp only at hbrk ⊢
                        c0_hsplit
                        · -- `sat_v = true`: mark clause garbage, update `arena_garbage`
                          c0_hsteps_nogrp
                          have hgarb_upd : sL.core.arena.set cr.toNat (hdr ||| 0x00080000#32) =
                              sL.core.arena.set (cr.setWidth 64).toNat (hdr ||| 0x00080000#32) := by
                            rw [bv_c0_zext32_64]
                          c0_hsteps!
                          have hlpG := m6_propLitLoop_markGarb hlpL
                            (cr := cr.setWidth 64)
                            (by rw [bv_c0_zext32_64]; exact hcr_ref)
                            (by rw [bv_c0_zext32_64]; exact hcr_lt0)
                            (sL.core.arena_garbage + 3#64 + csz.setWidth 64) hp2_le hsl_nxt'
                          exact hL (pL + 1#64 + 1#64, _) m
                            (by dsimp only; have := hp2_le; rw [hp2_nat] at this ⊢; omega)
                            ⟨hlpG, by dsimp only [csz]; exact hm⟩
                        · -- `sat_v = false`: check `non_false`
                          have hsat_f : sat_v = false := by cases sat_v <;> simp_all
                          obtain ⟨hnf0, hnf1⟩ := hbrk hsat_f
                          c0_hsplit
                          · -- `nf_v == 0`: clause conflict -> `false`
                            have hcr_fal : ∀ l ∈ fullArenaClauseLits sL cr.toNat,
                                sL.core.vals[l]?.getD 0#8 = 0xFF#8 := by
                              intro l hl
                              obtain ⟨k, hk, hget⟩ := (mem_fullArenaClauseLitsCore_iff hbd_cr).mp hl
                              have hk' : k < csz.toNat := by rw [hcsz_def]; exact hk
                              have hf := hnf0 ‹_› k hk'
                              rwa [List.getElem?_eq_getElem (by omega : cr.toNat + 3 + k <
                                sL.core.arena.length), Option.getD_some, hget] at hf
                            have huns : (cnfOfClauses F_cur).Unsat := by
                              rw [CNF.unsat_def]; intro β
                              rcases Bool.eq_false_or_eq_true (CNF.eval β (cnfOfClauses F_cur)) with
                                hβ | hfalse
                              · exfalso
                                have hent_cr := CNF.entails_clause_def.mp
                                  (hwL.arena.entails cr.toNat hcr_ref hng) β hβ
                                obtain ⟨l, hl, hs⟩ := (clause_sat_cnfClause_iff β _).mp hent_cr
                                have hlt := hwL.arena.lits_lt cr.toNat hcr_ref hng l hl
                                have hent_l := CNF.entails_clause_def.mp
                                  (m6_lvl0_false_entails hwL hlpL.dinv.2.2.2.2.2.1 hlt
                                    (hcr_fal l hl)) β hβ
                                have hneg := (sat_cnfClause_litNeg_iff β l).mp hent_l
                                exact absurd ((sat_cnfClause_singleton β l).mpr hs) hneg
                              · exact hfalse
                            c0_hsteps!
                            exact m6_propLitLoop_conflict hlpL huns hm hQ
                          · -- `nf_v != 0`
                            refine wp_join0 (fun m_fin => ∃ sF : FullState,
                                M6PropLitLoop c F0 F_cur s sF ((lit ^^^ 1#32).setWidth 64)
                                  (pL + 1#64 + 1#64) (off0.setWidth 64 + sz0.setWidth 64) ∧
                                (FullMem c sF ⋆ R) m_fin) ?_ ?_
                            · rintro _ m_fin ⟨sF, hlpF, hmF⟩
                              c0_hsteps!
                              exact hL (pL + 1#64 + 1#64, sF) m_fin
                                (by dsimp only; have := hp2_le; rw [hp2_nat] at this ⊢; omega)
                                ⟨hlpF, hmF⟩
                            · intro Jfin hJfin
                              c0_hsplit
                              · have hnf_eq1 : nf_v = 1#32 := ‹_›
                                obtain ⟨hu_lt, hu_eq0, hu_rest⟩ := hnf1 hnf_eq1
                                dsimp only at hu_lt hu_eq0 hu_rest
                                have hu_vl : (u_v.setWidth 64).toNat < sL.core.vals.length := by
                                  rw [hclL.vals_len, bv_c0_zext32_64]; have := hclL.cur_vars_le
                                  omega
                                c0_hsplit
                                · have hent_u : (cnfOfClauses F_cur).EntailsClause
                                      (cnfClause [u_v.toNat]) := by
                                    refine m6_lvl0_clause_unit_entails hwL
                                      hlpL.dinv.2.2.2.2.2.1 hcr_ref hng fun l hl => ?_
                                    obtain ⟨k, hk, hget⟩ :=
                                      (mem_fullArenaClauseLitsCore_iff hbd_cr).mp hl
                                    by_cases hlu : l = u_v.toNat
                                    · exact Or.inl hlu
                                    · right
                                      have hk' : k < csz.toNat := by rw [hcsz_def]; exact hk
                                      have hf := hu_rest k hk'
                                      rw [List.getElem?_eq_getElem (by omega : cr.toNat + 3 + k <
                                        sL.core.arena.length), Option.getD_some, hget] at hf
                                      exact hf hlu
                                  c0_call hAsg
                                  refine ⟨c, sL, R, rfl, hlpL.dinv.1, hmL, ?_⟩
                                  have hpre_f : ¬ (sL.core.cur_vars ≤ u_v.toNat / 2 ∨
                                      c.max_vars ≤ sL.core.trail_end ∨
                                      sL.core.vals[u_v.toNat]?.getD 0#8 ≠ 0#8) := by
                                    have hte := hwL.trail_end_lt_of_unassigned hu_lt hu_eq0
                                    have := hclL.cur_vars_le
                                    simp only [hu_eq0, ne_eq, not_true_eq_false, or_false]; omega
                                  split
                                  · next hcnd => exact absurd hcnd hpre_f
                                  · dsimp only
                                    intro flags' unass' phases' m' hfll hphl hm'
                                    have h0eq : ((0 : BitVec 32) = 0#32) = True := eq_true rfl
                                    simp only [h0eq, ↓reduceIte] at hm'
                                    have hlpA := m6_propLitLoop_assignLvl0 hlpL (unass' := unass')
                                      hfll hphl hu_lt hu_eq0 hent_u hp2_le hsl_nxt'
                                    c0_hsteps!
                                    exact hJfin m' ⟨_, hlpA, hm'⟩
                                · c0_hsteps!
                                  exact hJfin mL ⟨sL, m6_propLitLoop_step hlpL hp2_le hsl_nxt',
                                    hmL⟩
                              · c0_hsteps!
                                exact hJfin mL ⟨sL, m6_propLitLoop_step hlpL hp2_le hsl_nxt',
                                  hmL⟩
                      · -- Inner `while (i < csz)` loop
                        intro Jsc hJsc
                        refine wp_while_state (ts := [i32, i32, i32])
                          (proj := fun p : BitVec 32 × BitVec 32 × BitVec 32 =>
                            (p.1, p.2.1, p.2.2, ()))
                          (μ := fun p => csz.toNat - p.2.2.toNat)
                          (Inv := fun p ml => ClScanInv p ∧ ml = mL) ?_ ?_
                        · intro Jlp hJlp; c0_hsteps!
                          exact hJlp (0#32, 0xFFFFFFFF#32, 0#32) mL
                            ⟨⟨Or.inl rfl, by dsimp only; bv_omega, fun _ _ hk => by
                                dsimp only at hk; bv_omega,
                              fun h => by cases h⟩, rfl⟩
                        · rintro Jlp ⟨nf_i, u_i, i_i⟩ ml ⟨⟨hnf_d, hi_le, hi0, hi1⟩, hml⟩ ih_i
                          subst ml; dsimp only at hnf_d hi_le hi0 hi1 ⊢
                          c0_hsplit
                          · have hi_lt : i_i.toNat < csz.toNat := ‹_›
                            have hi1_nat : (i_i + 1#32).toNat = i_i.toNat + 1 := by bv_omega
                            have hidx_nat : (cr.setWidth 64 + 3#64 + i_i.setWidth 64).toNat =
                                cr.toNat + 3 + i_i.toNat := by bv_omega
                            have hidx_lt : cr.toNat + 3 + i_i.toNat < sL.core.arena.length := by
                              omega
                            have hidx_bd : (cr.setWidth 64 + (3 : BitVec 64) +
                                i_i.setWidth 64).toNat < sL.core.arena.length := by
                              change (cr.setWidth 64 + 3#64 + i_i.setWidth 64).toNat <
                                sL.core.arena.length
                              rw [hidx_nat]; exact hidx_lt
                            have hcl_ar : sL.core.arena[(cr.setWidth 64 + (3 : BitVec 64) +
                                i_i.setWidth 64).toNat]'hidx_bd =
                                sL.core.arena[cr.toNat + 3 + i_i.toNat]'hidx_lt :=
                              m6_getElem_congr hidx_nat hidx_bd hidx_lt
                            c0_hsteps_nogrp
                            simp only [hcl_ar]
                            let cl := sL.core.arena[cr.toNat + 3 + i_i.toNat]'hidx_lt
                            have hcl_eq : cl =
                                sL.core.arena[cr.toNat + 3 + i_i.toNat]'hidx_lt := rfl
                            have hcl_lt_k : cl.toNat < 2 * sL.core.cur_vars :=
                              hcl_lt_k i_i.toNat hi_lt
                            have hcl_lt_raw :
                                (sL.core.arena[cr.toNat + 3 + i_i.toNat]'hidx_lt).toNat <
                                  2 * sL.core.cur_vars := hcl_lt_k
                            have hcl_vl : (cl.setWidth 64).toNat < sL.core.vals.length := by
                              rw [hclL.vals_len, bv_c0_zext32_64]; have := hclL.cur_vars_le
                              omega
                            have hcl_vl' : cl.toNat < sL.core.vals.length := by
                              rw [← bv_c0_zext32_64 cl]; exact hcl_vl
                            have hcl_vl_raw :
                                (BitVec.setWidth 64 (sL.core.arena[cr.toNat + 3 +
                                  i_i.toNat]'hidx_lt)).toNat < sL.core.vals.length := hcl_vl
                            refine wp_join_state (ts := [.bool, i32, i32])
                              (proj := fun p : Bool × BitVec 32 × BitVec 32 =>
                                (p.1, p.2.1, p.2.2, ()))
                              (fun p m_st => ClScanInv (p.2.1, p.2.2, i_i + 1#32) ∧ m_st = mL)
                              ?_ ?_
                            · rintro Jst ⟨_b, nf_n, u_n⟩ m_st ⟨hinv_n, hm_st⟩
                              subst m_st
                              c0_hsteps!
                              exact ih_i (nf_n, u_n, i_i + 1#32) mL
                                (by dsimp only; rw [hi1_nat]; omega) ⟨hinv_n, rfl⟩
                            · intro Jst hJst
                              c0_hsplit
                              · -- `(u64)cl < nlits`
                                c0_hsplit
                                · -- `vals[cl] > 0`: `sat = true; break`
                                  c0_hsteps!
                                  exact hJsc (true, nf_i, u_i, i_i) mL
                                    ⟨fun h => Bool.noConfusion h, rfl⟩
                                · -- `!(vals[cl] > 0)`
                                  have hnp : (0#8).slt (sL.core.vals[cl.toNat]'hcl_vl') =
                                      false := by assumption
                                  refine wp_join_state (ts := [i32, i32])
                                    (proj := fun p : BitVec 32 × BitVec 32 => (p.1, p.2, ()))
                                    (fun p m_j => ClScanInv (p.1, p.2, i_i + 1#32) ∧ m_j = mL)
                                    ?_ ?_
                                  · rintro Jjn ⟨nf_j, u_j⟩ m_j ⟨hinv_j, hm_j⟩
                                    subst m_j
                                    c0_hsteps!
                                    exact hJst (false, nf_j, u_j) mL ⟨hinv_j, rfl⟩
                                  · intro Jjn hJjn
                                    c0_hsplit
                                    · -- `vals[cl] == 0`
                                      have heq0 : sL.core.vals[cl.toNat]'hcl_vl' = 0#8 := by
                                        dsimp only [cl]; assumption
                                      c0_hsteps!
                                      c0_hsplit
                                      · -- `1 < nf_i + 1`: `nf_i = 1#32`, `nf_i + 1 = 2#32`, `break`
                                        have hnf_eq2 : nf_i + 1#32 = 2#32 := by
                                          rcases hnf_d with rfl | rfl
                                          · exfalso; bv_omega
                                          · rfl
                                        c0_hsteps!
                                        have hbrk2 : ClScanBrk (false, nf_i + 1#32, cl, i_i) :=
                                          fun _ =>
                                          ⟨fun h => (by rw [hnf_eq2] at h; cases h),
                                           fun h => (by rw [hnf_eq2] at h; cases h)⟩
                                        exact hJsc (false, nf_i + 1#32, cl, i_i) mL ⟨hbrk2, rfl⟩
                                      · have hnf_eq0 : nf_i = 0#32 := by
                                          rcases hnf_d with rfl | rfl
                                          · rfl
                                          · exfalso; bv_omega
                                        subst hnf_eq0
                                        c0_hsteps!
                                        have hinv1 : ClScanInv (1#32, cl, i_i + 1#32) := by
                                          refine ⟨Or.inr rfl, by dsimp only; rw [hi1_nat]; omega,
                                            fun h => (by dsimp only at h; cases h),
                                            fun _ => ⟨hcl_lt_k, ?_, fun k hk hne => ?_⟩⟩
                                          · dsimp only
                                            rw [List.getElem?_eq_getElem hcl_vl',
                                              Option.getD_some]
                                            exact heq0
                                          · rw [hi1_nat] at hk
                                            by_cases hki : k = i_i.toNat
                                            · subst hki; exfalso; apply hne
                                              rw [List.getElem?_eq_getElem hidx_lt,
                                                Option.getD_some, ← hcl_eq]
                                            · exact hi0 rfl k (by omega)
                                        exact hJjn (1#32, cl) mL ⟨hinv1, rfl⟩
                                    · -- `vals[cl] != 0`: false (`0xFF#8`)
                                      have hne0 : sL.core.vals[cl.toNat]'hcl_vl' ≠ 0#8 := by
                                        dsimp only [cl]; assumption
                                      have hfals_cl : sL.core.vals[cl.toNat]'hcl_vl' = 0xFF#8 :=
                                        by
                                        rcases hwL.vals_domain _ hcl_lt_k with h0 | h1 | h2
                                        · rw [List.getElem?_eq_getElem hcl_vl', Option.getD_some]
                                            at h0
                                          exact absurd h0 hne0
                                        · rw [List.getElem?_eq_getElem hcl_vl', Option.getD_some]
                                            at h1
                                          rw [h1] at hnp; cases hnp
                                        · rw [List.getElem?_eq_getElem hcl_vl', Option.getD_some]
                                            at h2
                                          exact h2
                                      c0_hsteps!
                                      refine hJjn (nf_i, u_i) mL ⟨⟨hnf_d, by rw [hi1_nat]; omega,
                                        fun h0 k hk => ?_, fun h1 => ?_⟩, rfl⟩
                                      · rw [hi1_nat] at hk
                                        by_cases hki : k = i_i.toNat
                                        · subst hki
                                          rw [List.getElem?_eq_getElem hidx_lt, Option.getD_some,
                                            ← hcl_eq]
                                          try dsimp only
                                          rw [List.getElem?_eq_getElem hcl_vl', Option.getD_some]
                                          exact hfals_cl
                                        · exact hi0 h0 k (by omega)
                                      · obtain ⟨hu_lt, hu_0, hu_k⟩ := hi1 h1
                                        refine ⟨hu_lt, hu_0, fun k hk hne => ?_⟩
                                        rw [hi1_nat] at hk
                                        by_cases hki : k = i_i.toNat
                                        · subst hki
                                          rw [List.getElem?_eq_getElem hidx_lt, Option.getD_some,
                                            ← hcl_eq]
                                          try dsimp only
                                          rw [List.getElem?_eq_getElem hcl_vl', Option.getD_some]
                                          exact hfals_cl
                                        · exact hu_k k (by omega) hne
                              · exfalso; have hcvL := hlpL.cv; bv_omega
                          · -- `!(i_i < csz)`: natural exit
                            have hieq : i_i.toNat = csz.toNat := by
                              have hnot : ¬ i_i.toNat < sL.core.arena[(cr.toNat +
                                  (2 : BitVec 64).toNat) % 2 ^ 64].toNat := ‹_›
                              rw [hcsz_mod] at hnot; omega
                            c0_hsteps!
                            exact hJsc (false, nf_i, u_i, i_i) mL ⟨fun _ =>
                              ⟨fun h0 k hk => hi0 h0 k (hieq ▸ hk),
                               fun h1 => let h := hi1 h1; ⟨h.1, h.2.1, fun k hk hne =>
                                 h.2.2 k (hieq ▸ hk) hne⟩⟩, rfl⟩
        · -- `!(pL < endW)`: break out of outer `while`
          c0_hsteps!; exact hB (pL, sL) mL ⟨hlpL, hmL⟩
      · intro B L hB hL
        c0_hsteps!
        have hL0 := hL (off0.setWidth 64, s) m
          ⟨⟨hinv, rfl, rfl, rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
            by rw [bv_c0_zext32_64, hend64]; omega,
            by rw [hend64, hoff0_def, hsz0_def]; exact hbd0,
            by rw [bv_c0_zext32_64, bv_c0_zext32_64, hend64, hoff0_def, hsz0_def]
               simpa only [Nat.add_sub_cancel_left] using hslice0⟩, hm⟩
        simpa only [hoff0_shl] using hL0

/-! ## 3. `full_m6_dense_prop_wp` (`16/39`) -/

/-- `16/39`: Parametric `Func.wp` proof for `full_m6_dense_prop`. -/
theorem full_m6_dense_prop_wp (Γ : Env)
    (hLit : M6EnvSpec Γ "full_m6_dense_prop_lit" m6DensePropLitSpec) :
    ∀ args m Q X, m6DensePropSpec args m Q X →
      Func.wp Γ full_m6_dense_prop_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinv, hm, hQ⟩
  c0_hsteps_nogrp
  refine wp_while_state0 (μ := fun sL : FullState => c.max_vars - sL.core.propagated)
    (Inv := fun sL ml =>
      FullDenseInvW c F0 F_cur sL ∧ sL.core.cur_vars = s.core.cur_vars ∧
      sL.core.fuel = s.core.fuel ∧ sL.core.repr = s.core.repr ∧
      sL.core.arena_len = s.core.arena_len ∧ fullArenaClauseRefs sL = fullArenaClauseRefs s ∧
      sL.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
      sL.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
      sL.scratch.scratch_buf = s.scratch.scratch_buf ∧
      sL.scratch.work_stk1 = s.scratch.work_stk1 ∧
      sL.scratch.work_stk2 = s.scratch.work_stk2 ∧
      (sL.core.inconsistent ≠ 0#64 → F0.Unsat) ∧ (FullMem c sL ⋆ R) ml) ?_ ?_
  · intro J hJ
    exact hJ s m ⟨hinv, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun hinc => hinv.2.1.ext_sound.2 (hinv.2.1.inconsistent_sound hinc), hm⟩
  · rintro J sL ml ⟨hinvL, hcvL, hfuelL, hreprL, halenL, hrefsL, htmkL, htrhL, hscrL,
      hws1L, hws2L, hincL, hmL⟩ ihL
    refine wp_join0 (fun m_ex =>
        (¬ (sL.core.propagated < sL.core.trail_end ∧ sL.core.inconsistent = 0#64)) ∧
        (FullMem c sL ⋆ R) m_ex) ?_ ?_
    · intro _ m_ex ⟨hdn, hm_ex⟩
      c0_hsteps!
      rw [show (0 : BitVec 64) = 0#64 from rfl]
      by_cases hinc0 : sL.core.inconsistent = 0#64
      · have htrue : (sL.core.inconsistent == 0#64) = true := beq_iff_eq.mpr hinc0
        rw [htrue]
        exact hQ true sL m_ex hinvL hcvL hfuelL hreprL halenL hrefsL htmkL htrhL hscrL
          hws1L hws2L ⟨fun _ => hinc0, fun _ => rfl⟩ (fun h => Bool.noConfusion h) hm_ex
      · have hfalse : (sL.core.inconsistent == 0#64) = false :=
          beq_false_of_ne hinc0
        rw [hfalse]
        exact hQ false sL m_ex hinvL hcvL hfuelL hreprL halenL hrefsL htmkL htrhL hscrL
          hws1L hws2L ⟨fun h => Bool.noConfusion h, fun h => absurd h hinc0⟩
          (fun _ => ⟨hincL hinc0, hinc0⟩) hm_ex
    · intro Jex hJex
      have hmx := c.hmaxv; unfold dimacsBound at hmx
      have hclL := hinvL.1.core_ok
      have hcvL_le := hclL.cur_vars_le
      have hte_le := hclL.trail_end_le
      have hpr_le := hclL.propagated_le
      have hte_max : sL.core.trail_end ≤ c.max_vars := by omega
      c0_hsplit
      · c0_hsplit
        · have hpr_lt : sL.core.propagated < sL.core.trail_end := by bv_omega
          have hinc_0 : sL.core.inconsistent = 0#64 := ‹_›
          have hpr_trl : sL.core.propagated < sL.core.trl.length := by
            rw [hclL.trl_len]; omega
          have hpr_max : sL.core.propagated < c.max_vars := by omega
          have hpr1_nat : (BitVec.ofNat 64 sL.core.propagated + (1 : BitVec 64)).toNat =
              sL.core.propagated + 1 := by bv_omega
          c0_hsteps!
          let s1 := { sL with core := { sL.core with propagated := sL.core.propagated + 1 } }
          have hinv1 := m6_denseInvW_set_propagated hinvL (by omega : sL.core.propagated + 1 ≤
            sL.core.trail_end)
          c0_call hLit
          refine ⟨c, F0, F_cur, s1, R, rfl, hinv1, by simpa only [s1, hpr1_nat] using hm,
            fun ok s2 m2 hinv2 hcv2 hfuel2 hprop2 _ hrepr2 halen2 hrefs2 htmk2 htrh2 hscr2
              hws1_2 hws2_2 hok_f hok_t hm2 => ?_⟩
          c0_hsplit
          · have hokt : ok = true := ‹_›
            have hprop2' : s2.core.propagated = sL.core.propagated + 1 := hprop2
            exact ihL s2 m2 (by omega)
              ⟨hinv2, hcv2.trans hcvL, hfuel2.trans hfuelL, hrepr2.trans hreprL,
               halen2.trans halenL, hrefs2.trans hrefsL, htmk2.trans htmkL,
               htrh2.trans htrhL, hscr2.trans hscrL, hws1_2.trans hws1L, hws2_2.trans hws2L,
               fun h => absurd ((hok_t hokt).trans hinc_0) h, hm2⟩
          · have hokf : ok = false := by cases ok <;> simp_all
            obtain ⟨huns2, hinc2⟩ := hok_f hokf
            c0_hsteps!
            exact hQ false s2 m2 hinv2 (hcv2.trans hcvL) (hfuel2.trans hfuelL)
              (hrepr2.trans hreprL) (halen2.trans halenL) (hrefs2.trans hrefsL)
              (htmk2.trans htmkL) (htrh2.trans htrhL) (hscr2.trans hscrL)
              (hws1_2.trans hws1L) (hws2_2.trans hws2L)
              ⟨fun h => Bool.noConfusion h, fun h => absurd h hinc2⟩
              (fun _ => ⟨huns2, hinc2⟩) hm2
        · c0_hsteps!; exact hJex ml ⟨fun h => absurd h.2 ‹_›, hmL⟩
      · c0_hsteps!; exact hJex ml ⟨fun h => absurd h.1 (by bv_omega), hmL⟩

end LeanQbe.T.Examples.Kissat.FullM6Sweep
