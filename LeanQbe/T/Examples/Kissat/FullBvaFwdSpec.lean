module

public import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Shared BVA & Shrink-at-Root Invariant Helpers (`Stage 4`)

Extracted from `FullBvaFwdLemmas2` so `FullBvaFwdLemmas{2,3,4}` and `FullBvaHeapSpec`
compile as parallel siblings without depending on `_wp` proofs in `FullBvaFwdLemmas2`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open FullBvaFwdHelpers
open scoped FullArenaTactics FullBvaFwdTactics

/-! ## 4. Shared BVA & Shrink-at-Root Invariant Helpers -/

namespace FullBvaFwdHelpers

/-- Introducing fresh variable `fv = s.core.cur_vars` (`< c.max_vars`) via `cur_vars += 1` +
`full_init_fresh_var` transitions `FullWitnessInv c F0 F_cur` to
`FullWitnessInv c F0 (bvaExtendFormula fv L Q F_cur)` and preserves `FullDenseInv`. -/
theorem fullDenseInv_add_fresh_var {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} {L Q : List Nat}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hmrk : FullLitMarksClear c s) (hnodup : FullArenaVarsNodup s)
    (hext : FullExtScratchOk c s) (hl0 : s.core.cur_level = 0) (hdm : s.core.dense_mode ≠ 0#64)
    (hcv_lt : s.core.cur_vars < c.max_vars)
    (hL : ∀ f ∈ L, f < 2 * s.core.cur_vars) (hQ : ∀ q ∈ Q, q < 2 * s.core.cur_vars)
    (hprod : ∀ f ∈ L, ∀ q ∈ Q, (cnfOfClauses F_cur).EntailsClause (cnfClause [f, q]))
    (hlen' : s'.LengthsOk c)
    {vals' mrk' flags' lvl' rsns' wvec' : _} {unass' : BitVec 64}
    (hcore' : s'.core =
      { s.core with
        cur_vars := s.core.cur_vars + 1, vals := vals', mrk := mrk', flags := flags',
        lvl := lvl', rsns := rsns', wvec := wvec', unassigned := unass' })
    (hv0 : vals'[2 * s.core.cur_vars]?.getD 1#8 = 0#8)
    (hv1 : vals'[2 * s.core.cur_vars + 1]?.getD 1#8 = 0#8)
    (hv_oth : ∀ l < 2 * c.max_vars, l / 2 ≠ s.core.cur_vars → vals'[l]? = s.core.vals[l]?)
    (hmrk_fv : mrk'[s.core.cur_vars]?.getD 1#8 = 0#8)
    (hmrk_oth : ∀ v < c.max_vars, v ≠ s.core.cur_vars → mrk'[v]? = s.core.mrk[v]?)
    (hlvl_oth : ∀ v < c.max_vars, v ≠ s.core.cur_vars → lvl'[v]? = s.core.lvl[v]?)
    (hrsns_oth : ∀ v < c.max_vars, v ≠ s.core.cur_vars → rsns'[v]? = s.core.rsns[v]?)
    (hwvec_0 : ∀ k < 4, wvec'[4 * s.core.cur_vars + k]?.getD 1#32 = 0#32)
    (hwvec_oth : ∀ i < 4 * c.max_vars, i / 4 ≠ s.core.cur_vars → wvec'[i]? = s.core.wvec[i]?)
    (hll' : s'.scratch.last_learned = s.scratch.last_learned)
    (hext' : s'.scratch.extend_len = s.scratch.extend_len) :
    let F_next := bvaExtendFormula s.core.cur_vars L Q F_cur
    FullWitnessInv c F0 F_next s'.core ∧ FullDenseInv c F0 s' := by
  intro F_next
  let fv := s.core.cur_vars
  have hcl := hlen.core_ok; have hcl' := hlen'.core_ok
  have hent_orig : (cnfOfClauses F_next).Entails (cnfOfClauses F_cur) :=
    bvaExtendFormula_entails_orig fv L Q F_cur
  have hext_next : ExtUnsatSound F0 (fv + 1) F_next :=
    extUnsatSound_bvaExtendFormula hw.ext_sound hL hQ hprod
  have hdw : DenseWatchesInv F_cur s.core := by
    have h := hw.watches; unfold ModeWatchesInv at h; rwa [ite_eq_right hdm] at h
  have hwvec'_len : wvec'.length = 4 * c.max_vars := by simpa only [hcore'] using hcl'.wvec_len
  have hvals'_len : vals'.length = 2 * c.max_vars := by simpa only [hcore'] using hcl'.vals_len
  have hmrk'_len : mrk'.length = c.max_vars := by simpa only [hcore'] using hcl'.mrk_len
  have hwvec_get : ∀ idx < 4 * c.max_vars,
      s'.core.wvec[idx]?.getD 0#32 =
        if 4 * fv ≤ idx ∧ idx < 4 * fv + 4 then 0#32 else s.core.wvec[idx]?.getD 0#32 :=
    fun idx hidx => by
      rw [hcore']; dsimp only
      by_cases hin : 4 * fv ≤ idx ∧ idx < 4 * fv + 4
      · simp only [hin]
        have hltw : idx < wvec'.length := by rw [hwvec'_len]; exact hidx
        have hz := hwvec_0 (idx - 4 * fv) (by omega)
        rw [show 4 * fv + (idx - 4 * fv) = idx by omega, List.getElem?_eq_getElem hltw,
          Option.getD_some] at hz
        rw [List.getElem?_eq_getElem hltw, Option.getD_some, hz]; rfl
      · simp only [hin, ↓reduceIte]; rw [hwvec_oth idx hidx (by omega)]
  have hoff_eq : ∀ l < 2 * (fv + 1),
      fullWatchOffCore s'.core l = if l < 2 * fv then fullWatchOffCore s.core l else 0 :=
    fun l hl => by
      unfold fullWatchOffCore; rw [hwvec_get (2 * l) (by omega)]
      by_cases hlt : l < 2 * fv
      · have hnot : ¬ (4 * fv ≤ 2 * l ∧ 2 * l < 4 * fv + 4) := by omega
        rw [ite_eq_right hnot, ite_eq_left hlt]
      · have hin : 4 * fv ≤ 2 * l ∧ 2 * l < 4 * fv + 4 := by omega
        rw [ite_eq_left hin, ite_eq_right hlt]; rfl
  have hsz_eq : ∀ l < 2 * (fv + 1),
      fullWatchSizeCore s'.core l = if l < 2 * fv then fullWatchSizeCore s.core l else 0 :=
    fun l hl => by
      unfold fullWatchSizeCore; rw [hwvec_get (2 * l + 1) (by omega)]
      by_cases hlt : l < 2 * fv
      · have hnot : ¬ (4 * fv ≤ 2 * l + 1 ∧ 2 * l + 1 < 4 * fv + 4) := by omega
        rw [ite_eq_right hnot, ite_eq_left hlt]
      · have hin : 4 * fv ≤ 2 * l + 1 ∧ 2 * l + 1 < 4 * fv + 4 := by omega
        rw [ite_eq_left hin, ite_eq_right hlt]; rfl
  have hvals_get : ∀ l < 2 * (fv + 1),
      s'.core.vals[l]?.getD 0#8 = if l < 2 * fv then s.core.vals[l]?.getD 0#8 else 0#8 :=
    fun l hl => by
      rw [hcore']; dsimp only
      have hltv : l < vals'.length := by rw [hvals'_len]; omega
      by_cases hlt : l < 2 * fv
      · simp only [hlt, ↓reduceIte]; rw [hv_oth l (by omega) (by omega)]
      · simp only [hlt, ↓reduceIte]
        by_cases h0 : l = 2 * fv
        · subst h0; rw [List.getElem?_eq_getElem hltv, Option.getD_some] at hv0 ⊢; exact hv0
        · have h1 : l = 2 * fv + 1 := by omega
          subst h1; rw [List.getElem?_eq_getElem hltv, Option.getD_some] at hv1 ⊢; exact hv1
  have hcv' : s'.core.cur_vars = fv + 1 := by rw [hcore']
  have hte' : s'.core.trail_end = s.core.trail_end := by rw [hcore']
  have htrl' : s'.core.trl = s.core.trl := by rw [hcore']
  have har' : s'.core.arena = s.core.arena := by rw [hcore']
  have hal' : s'.core.arena_len = s.core.arena_len := by rw [hcore']
  have hdm' : s'.core.dense_mode = s.core.dense_mode := by rw [hcore']
  have hcl_0 : s'.core.cur_level = 0 := by rw [hcore']; exact hl0
  have hrefs' : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core := by
    unfold fullArenaClauseRefsCore; rw [har', hal']
  have hlvl_old : ∀ i < s.core.trail_end,
      (s'.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := fun i hi => by
    have hlt := hw.trail_lits_lt i hi
    rw [hcore']; dsimp only; rw [hlvl_oth _ (by omega) (by omega)]
    have := hw.lvl_le i hi; omega
  have hrsn_old : ∀ i < s.core.trail_end,
      s'.core.rsns[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun i hi => by
      have hlt := hw.trail_lits_lt i hi
      rw [hcore']; dsimp only; rw [hrsns_oth _ (by omega) (by omega)]
      exact hw.level0_rsn_none i hi (by have := hw.lvl_le i hi; omega)
  have hdw' : DenseWatchesInv F_next s'.core := by
    refine DenseWatchesInv.of_slices ?_ ?_ ?_ ?_
    · intro l hl; rw [hcv'] at hl; rw [hoff_eq l hl, hsz_eq l hl]
      split
      · rename_i hlt; rw [hcore']; exact hdw.layout.bounds l hlt
      · omega
    · intro l hl hpos; rw [hcv'] at hl; rw [hoff_eq l hl]; rw [hsz_eq l hl] at hpos
      split at hpos
      · rename_i hlt; simp only [hlt, ↓reduceIte]; exact hdw.layout.pos_off l hlt hpos
      · omega
    · intro l1 l2 h1 h2 hne hp1 hp2
      rw [hcv'] at h1 h2; rw [hoff_eq l1 h1, hoff_eq l2 h2, hsz_eq l1 h1, hsz_eq l2 h2]
      rw [hsz_eq l1 h1] at hp1; rw [hsz_eq l2 h2] at hp2
      split at hp1
      · rename_i h1lt
        split at hp2
        · rename_i h2lt
          simp only [h1lt, h2lt, ↓reduceIte]
          exact hdw.layout.disjoint l1 l2 h1lt h2lt hne hp1 hp2
        · omega
      · omega
    · intro l hl; rw [hcv'] at hl; rw [hoff_eq l hl, hsz_eq l hl]
      by_cases hlt : l < 2 * fv
      · simp only [hlt, ↓reduceIte]
        exact (hdw.slices l hlt).mono hent_orig (by rw [hcv']; omega) (fun _ hr => hrefs' ▸ hr)
          (fun _ _ _ => by rw [hcore'])
      · simp only [hlt, ↓reduceIte]; exact .empty
  have harena' : FullArenaClausesInv c F_next s'.core := by
    refine ⟨by rw [hal']; exact hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs'] at hr
      simpa only [har', hal', fullArenaClauseSizeCore] using hw.arena.refs_wf r hr
    · intro r hr hsh; rw [hrefs'] at hr
      simpa only [har', hal', fullArenaHdrCore, fullArenaClauseSizeCore] using
        hw.arena.shrk_term r hr (by simpa only [har', fullArenaHdrCore] using hsh)
    · intro r hr hng l hl; rw [hrefs'] at hr
      have hng0 : fullArenaClauseGarbCore s.core r = false := by
        simpa only [har', fullArenaClauseGarbCore, fullArenaHdrCore] using hng
      have hl0' : l ∈ fullArenaClauseLitsCore s.core r := by
        simpa only [har', fullArenaClauseLitsCore, fullArenaClauseSizeCore] using hl
      have := hw.arena.lits_lt r hr hng0 l hl0'
      rw [hcv']; omega
    · intro r hr hng; rw [hrefs'] at hr
      have hng0 : fullArenaClauseGarbCore s.core r = false := by
        simpa only [har', fullArenaClauseGarbCore, fullArenaHdrCore] using hng
      have heq : fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := by
        unfold fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har']
      rw [heq]
      exact CNF.entails_clause_trans hent_orig (hw.arena.entails r hr hng0)
  have hw' : FullWitnessInv c F0 F_next s'.core :=
    { ext_sound := hcv'.symm ▸ hext_next
      inconsistent_sound := fun hinc => by
        have hinc0 : s.core.inconsistent ≠ 0#64 := by rwa [hcore'] at hinc
        have hu := hw.inconsistent_sound hinc0
        rw [CNF.unsat_iff_not_sat] at hu ⊢; rw [CNF.entails_def] at hent_orig
        intro α hα; exact hu α (hent_orig α hα)
      arena := harena'
      watches := by unfold ModeWatchesInv; rw [hdm', ite_eq_right hdm]; exact hdw'
      cur_level_le := by rw [hcl_0]; exact Nat.zero_le _
      trail_lits_lt := fun i hi => by
        rw [hte'] at hi; rw [htrl', hcv']; have := hw.trail_lits_lt i hi; omega
      trail_vars_nodup := fun i j hi hj => by
        rw [hte'] at hi hj; rw [htrl']; exact hw.trail_vars_nodup i j hi hj
      vals_domain := fun l hl => by
        rw [hcv'] at hl; rw [hvals_get l hl]
        split; exact hw.vals_domain l ‹_›; exact Or.inl rfl
      vals_true_iff := fun l hl => by
        rw [hcv'] at hl; rw [hvals_get l hl, hte', htrl']
        by_cases hlt : l < 2 * fv
        · simp only [hlt, ↓reduceIte]; exact hw.vals_true_iff l hlt
        · simp only [hlt, ↓reduceIte]; constructor
          · intro h; cases h
          · rintro ⟨i, hi, heq⟩; have := hw.trail_lits_lt i hi; omega
      vals_false_iff := fun l hl => by
        rw [hcv'] at hl; rw [hvals_get l hl, hte', htrl']
        by_cases hlt : l < 2 * fv
        · simp only [hlt, ↓reduceIte]; exact hw.vals_false_iff l hlt
        · simp only [hlt, ↓reduceIte]; constructor
          · intro h; cases h
          · rintro ⟨i, hi, heq⟩
            have := hw.trail_lits_lt i hi; rw [heq] at this
            have hlt2 := litNeg_lt_two_mul this
            rw [show (l ^^^ 1) ^^^ 1 = l from litNeg_litNeg l] at hlt2; omega
      lvl_le := fun i hi => by rw [hte'] at hi; rw [htrl', hlvl_old i hi]; exact Nat.zero_le _
      dec_earliest := fun i j hi hj _ hdec => by
        rw [hte'] at hj; rw [htrl', hlvl_old j hj] at hdec; omega
      levels_inhabited := fun L h1 hle => by rw [hcl_0] at hle; omega
      level0_sound := fun i hi _ => by
        rw [hte'] at hi; rw [htrl']
        exact CNF.entails_clause_trans hent_orig
          (hw.level0_sound i hi (by have := hw.lvl_le i hi; omega))
      trail_pos_inv := fun i hi => by
        rw [hte'] at hi; rw [htrl', show s'.core.trail_pos = s.core.trail_pos by rw [hcore']]
        exact hw.trail_pos_inv i hi
      level0_rsn_none := fun idx hidx _ => by
        rw [hte'] at hidx; rw [htrl']; exact hrsn_old idx hidx
      frame_trail_lt := fun L hL => by
        rw [hcl_0] at hL; rw [hte', show s'.core.frame_trail = s.core.frame_trail by rw [hcore']]
        exact hw.frame_trail_lt L (by omega)
      frame_trail_mono := fun L1 L2 h1 h2 => by
        rw [hcl_0] at h2; rw [show s'.core.frame_trail = s.core.frame_trail by rw [hcore']]
        exact hw.frame_trail_mono L1 L2 h1 (by omega)
      frame_trail_before_lt := fun L h1 h2 => by rw [hcl_0] at h2; omega
      frame_dec_lt := fun L h1 h2 => by rw [hcl_0] at h2; omega
      reason_inv := fun idx hidx hne => by
        rw [hte'] at hidx; rw [htrl'] at hne; exact absurd (hrsn_old idx hidx) hne
      reason_lit_mem := fun idx hidx hne _ => by
        rw [hte'] at hidx; rw [htrl'] at hne; exact absurd (hrsn_old idx hidx) hne }
  have hmrk' : FullLitMarksClear c s' := by
    refine ⟨fun v hv => ?_, fun l hl => ?_⟩
    · rw [hcore']; dsimp only
      by_cases hve : v = fv
      · subst hve; have hltm : fv < mrk'.length := by rw [hmrk'_len]; exact hv
        rw [List.getElem?_eq_getElem hltm, Option.getD_some] at hmrk_fv ⊢; exact hmrk_fv
      · rw [hmrk_oth v hv hve]; exact hmrk.1 v hv
    · rw [show s'.core.lit_mark = s.core.lit_mark by rw [hcore']]; exact hmrk.2 l hl
  have hnodup' : FullArenaVarsNodup s' := by
    intro r hr hng; change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs'] at hr
    have hng0 : fullArenaClauseGarb s r = false := by
      simpa only [fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore, har'] using hng
    have hlits_eq : fullArenaClauseLits s' r = fullArenaClauseLits s r := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har']
    rw [hlits_eq]; exact hnodup r hr hng0
  have hext_ok' : FullExtScratchOk c s' :=
    ⟨fun i hi => by
      dsimp only; unfold fullArenaClauseRefs; rw [hll', hrefs']; exact hext.1 i hi,
     by rw [hext']; exact hext.2⟩
  exact ⟨hw', ⟨⟨hlen', F_next, hw'⟩, hmrk', hnodup', hext_ok', hcl_0, hdm' ▸ hdm⟩⟩

private theorem fwd_bit23_shrk : (0x00800000#32 : BitVec 32)[23] = true := by decide

/-- Skipping a prefix of non-sentinel words in `fullArenaSkipShrk`. -/
theorem fullArenaSkipShrk_skip_prefix {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {d fuel p : Nat}, p + d ≤ alen → d ≤ fuel →
      (∀ i, p ≤ i → i < p + d → ar[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) →
      fullArenaSkipShrk ar alen p fuel = fullArenaSkipShrk ar alen (p + d) (fuel - d)
  | 0, fuel, p, _, _, _ => by rw [Nat.add_zero, Nat.sub_zero]
  | d + 1, 0, _, _, hf, _ => by omega
  | d + 1, fuel + 1, p, hle, hf, hne => by
    have hp : p < alen := by omega
    have h0 : ar[p]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := hne p (Nat.le_refl _) (by omega)
    have hstep :
        fullArenaSkipShrk ar alen p (fuel + 1) = fullArenaSkipShrk ar alen (p + 1) fuel := by
      rw [fullArenaSkipShrk]; simp only [hp, ↓reduceIte, h0, ne_eq, not_false_eq_true]
    rw [hstep, show p + (d + 1) = p + 1 + d by omega, show fuel + 1 - (d + 1) = fuel - d by omega]
    exact fullArenaSkipShrk_skip_prefix (ar := ar) (alen := alen) (d := d) (fuel := fuel)
      (p := p + 1) (by omega) (by omega) fun i hi1 hi2 => hne i (by omega) (by omega)

/-- Shrinking live clause `cref` in place (`3 ≤ nsz < sz`) at `cur_level = 0` preserves
`fullArenaClauseRefsCore` and `FullWitnessInv c F0 F_cur`. -/
theorem fullWitnessInv_shrink_at_root {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c) (hw : FullWitnessInv c F0 F_cur k)
    (hl0 : k.cur_level = 0) {cref nsz : Nat} (href : cref ∈ fullArenaClauseRefsCore k)
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < fullArenaClauseSizeCore k cref)
    {arena' : List (BitVec 32)}
    (hal : arena'.length = c.arena_cap)
    (hhdr' : arena'[cref]? = some (if (fullArenaHdrCore k cref &&& 0x00800000#32) = 0#32
      then fullArenaHdrCore k cref ||| 0x00800000#32 else fullArenaHdrCore k cref))
    (hsz' : arena'[cref + 2]? = some (BitVec.ofNat 32 nsz))
    (hpad_new : (fullArenaHdrCore k cref &&& 0x00800000#32) = 0#32 →
      arena'[cref + 3 + fullArenaClauseSizeCore k cref - 1]? = some 0xFFFFFFFF#32 ∧
      ∀ i, cref + 3 + nsz ≤ i → i < cref + 3 + fullArenaClauseSizeCore k cref - 1 →
        arena'[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hpad_old : (fullArenaHdrCore k cref &&& 0x00800000#32) ≠ 0#32 →
      ∀ i, cref + 3 + nsz ≤ i → i < cref + 3 + fullArenaClauseSizeCore k cref →
        arena'[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hout : ∀ i, i < cref ∨ cref + 3 + fullArenaClauseSizeCore k cref ≤ i →
      arena'[i]? = k.arena[i]?)
    (hnew_lits_lt : ∀ l ∈ fullArenaClauseLitsCore { k with arena := arena' } cref,
      l < 2 * k.cur_vars)
    (hnew_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { k with arena := arena' } cref))) :
    let k' : FullCoreState := { k with arena := arena' }
    k'.LengthsOk c ∧
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    FullWitnessInv c F0 F_cur k' ∧
    (∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) := by
  intro k'
  have hcref_wf := hw.arena.refs_wf cref href
  have hsz_lt32 : nsz < 2 ^ 32 := by
    have := hlen.arena_len_le; have := c.harena; unfold dimacsBound at *; omega
  have har_len : cref < k.arena.length := by
    have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
  have hget_cref : k.arena[cref]? = some (fullArenaHdrCore k cref) := by
    unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem har_len, Option.getD_some]
  have hbit23_or : ∀ x : BitVec 32, ((x ||| 0x00800000#32) &&& 0x00800000#32) ≠ 0#32 :=
    fun x h => by have h23 := congrArg (·[23]) h; revert h23; simp [fwd_bit23_shrk]
  have hne_outside : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore k r ≤ cref ∧ fullArenaNextOff k.arena k.arena_len r ≤ cref) ∨
      (cref + 3 + fullArenaClauseSizeCore k cref ≤ r ∧
        fullArenaNextOff k.arena k.arena_len cref ≤ r) := by
    intro r hr hne; rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have := fullArenaScanRefs_disjoint hr href hlt
      have := (hw.arena.refs_wf r hr).2.2.1; exact Or.inl ⟨by omega, by omega⟩
    · have := fullArenaScanRefs_disjoint href hr hgt; exact Or.inr ⟨by omega, by omega⟩
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff arena' k.arena_len r = fullArenaNextOff k.arena k.arena_len r := by
    intro r hr
    by_cases hrc : r = cref
    · subst r
      have h1 : ¬ (cref + 3 > k.arena_len) := by omega
      have h2_old : ¬ (cref + 3 + (k.arena[cref + 2]?.getD 0#32).toNat > k.arena_len) := by
        unfold fullArenaClauseSizeCore at hcref_wf; omega
      have h2_new : ¬ (cref + 3 + nsz > k.arena_len) := by omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2_old, hhdr', hsz', Option.getD_some,
        bv32_ofNat_toNat hsz_lt32, h2_new]
      by_cases hsh : (fullArenaHdrCore k cref &&& 0x00800000#32) = 0#32
      · have hsh_ar : (k.arena[cref]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
          rw [hget_cref, Option.getD_some]; exact hsh
        simp only [hsh, ↓reduceIte, hbit23_or, ne_eq, not_false_eq_true, hsh_ar]
        obtain ⟨hsent, hskip⟩ := hpad_new hsh
        rw [show (k.arena[cref + 2]?.getD 0#32).toNat = fullArenaClauseSizeCore k cref from rfl,
          fullArenaSkipShrk_skip_prefix (ar := arena') (alen := k.arena_len)
            (d := fullArenaClauseSizeCore k cref - 1 - nsz)
            (fuel := k.arena_len - (cref + 3 + nsz)) (p := cref + 3 + nsz)
            (by omega) (by omega) fun i hi1 hi2 => hskip i hi1 (by omega),
          show cref + 3 + nsz + (fullArenaClauseSizeCore k cref - 1 - nsz) =
            cref + 3 + fullArenaClauseSizeCore k cref - 1 by omega,
          show k.arena_len - (cref + 3 + nsz) - (fullArenaClauseSizeCore k cref - 1 - nsz) =
            (k.arena_len - (cref + 3 + fullArenaClauseSizeCore k cref)) + 1 by omega]
        unfold fullArenaSkipShrk
        have hlt_a : cref + 3 + fullArenaClauseSizeCore k cref - 1 < k.arena_len := by omega
        simp only [hlt_a, ↓reduceIte, hsent, Option.getD_some, ne_eq, not_true_eq_false]; omega
      · have hsh_ar : (k.arena[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
          rw [hget_cref, Option.getD_some]; exact hsh
        simp only [hsh, ↓reduceIte, ne_eq, not_false_eq_true, hsh_ar]
        have hskip := hpad_old hsh
        rw [show (k.arena[cref + 2]?.getD 0#32).toNat = fullArenaClauseSizeCore k cref from rfl,
          fullArenaSkipShrk_skip_prefix (ar := arena') (alen := k.arena_len)
            (d := fullArenaClauseSizeCore k cref - nsz)
            (fuel := k.arena_len - (cref + 3 + nsz)) (p := cref + 3 + nsz)
            (by omega) (by omega) fun i hi1 hi2 => hskip i hi1 (by omega),
          show cref + 3 + nsz + (fullArenaClauseSizeCore k cref - nsz) =
            cref + 3 + fullArenaClauseSizeCore k cref by omega,
          show k.arena_len - (cref + 3 + nsz) - (fullArenaClauseSizeCore k cref - nsz) =
            k.arena_len - (cref + 3 + fullArenaClauseSizeCore k cref) by omega]
        exact fullArenaSkipShrk_congr fun i hi _ => hout i (Or.inr hi)
    · have hne := hne_outside r hr hrc; have := (hw.arena.refs_wf r hr).2.1
      refine fullArenaNextOff_congr_block
        (hout r (hne.imp (fun _ => by omega) (fun _ => by omega)))
        (hout (r + 2) (hne.imp (fun _ => by omega) (fun _ => by omega)))
        fun i hi1 hi2 => hout i (hne.imp (fun _ => by omega) (fun _ => by omega))
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hsz_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = if r = cref then nsz else fullArenaClauseSizeCore k r :=
    fun r hr => by
      unfold fullArenaClauseSizeCore; dsimp only [k']
      by_cases hrc : r = cref
      · subst r; simp [hsz', bv32_ofNat_toNat hsz_lt32]
      · simp only [hrc, ↓reduceIte]; have := (hw.arena.refs_wf r hr).2.1
        rw [hout (r + 2) ((hne_outside r hr hrc).imp (fun _ => by omega) (fun _ => by omega))]
  have hgarb_eq : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := fun r hr hne => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [k']
    rw [hout r ((hne_outside r hr hne).imp (fun _ => by omega) (fun _ => by omega))]
  have hlits_eq : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := fun r hr hne => by
    have hwf := hw.arena.refs_wf r hr; have := hlen.arena_len_le; have := hlen.arena_len_arr
    refine fullArenaClauseLitsCore_eq_of_hold (by omega) (by dsimp only [k']; omega)
      (by simpa [hne] using hsz_eq r hr) fun j hj => by
        dsimp only [k']
        exact hout (r + 3 + j) ((hne_outside r hr hne).imp (fun _ => by omega) (fun _ => by omega))
  have harena' : FullArenaClausesInv c F_cur k' := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := hw.arena.refs_wf r hr
      dsimp only [k'] at hnxt ⊢; rw [hnxt r hr, hsz_eq r hr]
      split
      · subst r; exact ⟨hwf.1, hnsz3, by omega, hwf.2.2.2.1, hwf.2.2.2.2⟩
      · exact hwf
    · intro r hr hsh; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r
        by_cases hsh0 : (fullArenaHdrCore k cref &&& 0x00800000#32) = 0#32
        · obtain ⟨hsent, _⟩ := hpad_new hsh0
          refine ⟨cref + 3 + fullArenaClauseSizeCore k cref - 1,
            by rw [hsz_eq cref hr]; simp only [↓reduceIte]; omega, by dsimp only [k']; omega, hsent⟩
        · obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term cref hr hsh0
          refine ⟨t, by rw [hsz_eq cref hr]; simp only [↓reduceIte]; omega,
            by dsimp only [k']; omega, by dsimp only [k']; rw [hout t (Or.inr ht1)]; exact hsent⟩
      · have hsh0 : (fullArenaHdrCore k r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢; dsimp only [k'] at hsh
          rwa [hout r ((hne_outside r hr hrc).imp (fun _ => by omega) (fun _ => by omega))] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
        have hsh_ar : (k.arena[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := hsh0
        obtain ⟨t0, ht0_lo, _, _, ht0_sent⟩ :=
          fullArenaNextOff_hits_sentinel (hw.arena.refs_wf r hr).1 hsh_ar ht1 ht2 hsent
        refine ⟨t0, by rw [hsz_eq r hr, ite_eq_right hrc]; exact ht0_lo,
          by dsimp only [k']; omega, ?_⟩
        dsimp only [k']
        rw [hout t0 ((hne_outside r hr hrc).imp (fun _ => by omega) (fun _ => by omega))]
        exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; exact hnew_lits_lt l hl
      · rw [hgarb_eq r hr hrc] at hng; rw [hlits_eq r hr hrc] at hl
        exact hw.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; exact hnew_ent
      · rw [hgarb_eq r hr hrc] at hng; rw [hlits_eq r hr hrc]
        exact hw.arena.entails r hr hng
  have hno_rsn : ∀ idx < k.trail_end,
      k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun idx hidx => hw.level0_rsn_none idx hidx (by have := hw.lvl_le idx hidx; omega)
  refine ⟨{ hlen with arena_len_arr := hal }, hrefs,
    { hw with
      arena := harena'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hrefs ▸ hr)
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne },
    fun r hr hne => ⟨hgarb_eq r hr hne, hlits_eq r hr hne⟩⟩

/-- Setting `inconsistent := 1#64` when `(cnfOfClauses F_cur).Unsat` preserves `FullWitnessInv`. -/
theorem fullWitnessInv_set_inconsistent {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hu : (cnfOfClauses F_cur).Unsat) :
    FullWitnessInv c F0 F_cur { k with inconsistent := 1#64 } :=
  { hw with
    inconsistent_sound := fun _ => hu, arena := { hw.arena with len_ok := hw.arena.len_ok },
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

/-- `(setWidth 32 (ofNat 64 v) <<< 1) ^^^ 1#32` equals `2 * v + 1` when in 32-bit range. -/
theorem bva_bv32_shl1_xor1 {v : Nat} (hv : 2 * v + 1 < 2 ^ 32) :
    ((BitVec.setWidth 32 (BitVec.ofNat 64 v) <<< (1 : Nat)) ^^^ 1#32).toNat = 2 * v + 1 := by
  have hshl : (BitVec.setWidth 32 (BitVec.ofNat 64 v) <<< (1 : Nat)).toNat = 2 * v := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt
      (by omega), Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
    omega
  have heq : (BitVec.setWidth 32 (BitVec.ofNat 64 v) <<< (1 : Nat)) ^^^ 1#32 =
      (BitVec.setWidth 32 (BitVec.ofNat 64 v) <<< (1 : Nat)) ||| 1#32 := by
    ext i hi; simp only [BitVec.getElem_xor, BitVec.getElem_or]
    cases i with
    | zero => simp [BitVec.getElem_shiftLeft]
    | succ n => simp [BitVec.getElem_eq_testBit_toNat, Nat.testBit_succ]
  rw [heq, FullBvaFwdTactics.bv32_or1_of_even (by rw [hshl]; omega), hshl]

end FullBvaFwdHelpers

end LeanQbe.T.Examples.Kissat.Full
