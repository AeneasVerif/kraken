module

public import LeanQbe.T.Examples.Kissat.FullBvaFwdSpec
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` BVA Variable Addition `Func.wp` Proofs — Part 3 (`Stage 4`)

Proves parametric `(Γ : Env)` `Func.wp` contracts for BVA (`Full.lean`):
1. `full_factor` (`full_factor_wp` → `fullFactorSpec`)
2. `full_bva_try_lit` (`full_bva_try_lit_wp` → `fullBvaTryLitSpec`)
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

/-! ## 1. Helper lemmas for BVA -/

private def bvaScrMask (t : FullState) : FullState :=
  { t with scratch := { t.scratch with scratch_buf := [] } }

private theorem bva_scr_reconstruct {s st : FullState}
    (h : AgreesExcept bvaScrMask s st) :
    st = { s with scratch := { s.scratch with scratch_buf := st.scratch.scratch_buf } } := by
  have hc : st.core = s.core := h.get FullState.core
  have hsc : st.scratch = { s.scratch with scratch_buf := st.scratch.scratch_buf } := by
    have h1 := congrArg FullState.scratch h
    cases st; cases s; rename_i _ sc1 _ sc2; cases sc1; cases sc2
    simp only [bvaScrMask] at h1; cases h1; rfl
  cases st; cases s; simp only at hc hsc; rw [hc]; exact congrArg (FullState.mk _) hsc

private theorem bva_scr_lengths {c : FullCfg} {s st : FullState}
    (h : AgreesExcept bvaScrMask s st) (hlen : s.LengthsOk c)
    (hsb : st.scratch.scratch_buf.length = c.scratch_cap) : st.LengthsOk c := by
  rw [bva_scr_reconstruct h]
  exact { hlen with scratch_ok := { hlen.scratch_ok with scratch_buf_len := hsb } }

private theorem bva_scr_dense {c : FullCfg} {F0 : CNF Nat} {s st : FullState}
    (h : AgreesExcept bvaScrMask s st) (hinv : FullDenseInv c F0 s)
    (hsb : st.scratch.scratch_buf.length = c.scratch_cap) : FullDenseInv c F0 st := by
  have heq := bva_scr_reconstruct h; have hlen' := bva_scr_lengths h hinv.1.lengths hsb
  rw [heq] at hlen' ⊢; obtain ⟨⟨_, F_cur, hw⟩, hmrk, hnodup, hext, hl0, hdm⟩ := hinv
  exact ⟨⟨hlen', F_cur, hw⟩, hmrk, hnodup, hext, hl0, hdm⟩

private theorem fullDenseInv_set_flags {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullDenseInv c F0 s) (fl' : List (BitVec 32)) (hfl : fl'.length = c.max_vars) :
    FullDenseInv c F0 { s with core := { s.core with flags := fl' } } := by
  obtain ⟨⟨hlen, F_cur, hw⟩, hmrk, hnodup, hext, hl0, hdm⟩ := hinv
  have hdw : DenseWatchesInv F_cur s.core := by
    have h := hw.watches; unfold ModeWatchesInv at h; rwa [ite_eq_right hdm] at h
  have hdw' : DenseWatchesInv F_cur { s.core with flags := fl' } :=
    DenseWatchesInv.of_slices hdw.layout.bounds hdw.layout.pos_off hdw.layout.disjoint
      (fun l hl => DenseWatchSliceOk.mono (k := s.core) (k' := { s.core with flags := fl' })
        (by rw [CNF.entails_def]; exact fun _ h => h)
        (Nat.le_refl _) (fun _ r => r) (fun _ _ _ => rfl) (hdw.slices l hl))
  refine ⟨⟨{ hlen with core_ok := { hlen.core_ok with flags_len := hfl } }, F_cur,
    { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
              watches := by unfold ModeWatchesInv; rw [ite_eq_right hdm]; exact hdw' }⟩,
    hmrk, hnodup, hext, hl0, hdm⟩

private theorem fullDenseInv_set_bva_cnt {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullDenseInv c F0 s) (cnt' : BitVec 64) :
    FullDenseInv c F0 { s with scratch := { s.scratch with bva_cnt := cnt' } } :=
  let ⟨⟨hlen, F_cur, hw⟩, hmrk, hnodup, hext, hl0, hdm⟩ := hinv
  ⟨⟨{ hlen with
      scratch_ok := { hlen.scratch_ok with scratch_buf_len := hlen.scratch_ok.scratch_buf_len } },
    F_cur, hw⟩, hmrk, hnodup, hext, hl0, hdm⟩

private theorem fullDenseInv_of_addBin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hinv : FullDenseInv c F0 s) (hlen' : s'.LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur s'.core) (hl0' : s'.core.cur_level = 0)
    (har' : s'.core.arena = s.core.arena) (hal' : s'.core.arena_len = s.core.arena_len)
    (hmrk' : s'.core.mrk = s.core.mrk) (hlm' : s'.core.lit_mark = s.core.lit_mark)
    (hdm' : s'.core.dense_mode = s.core.dense_mode)
    (hll' : s'.scratch.last_learned = s.scratch.last_learned)
    (hext' : s'.scratch.extend_len = s.scratch.extend_len) : FullDenseInv c F0 s' :=
  (fullDenseInv_of_fwd_call hinv hlen' hw' hl0' har' hal' hmrk' hlm' hdm' hll' hext').1

private theorem fullDenseInv_of_delBin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInv c F0 s) {wvec' wstk' : List (BitVec 32)}
    {wusable' nb' : BitVec 64}
    (hlen' : (FullState.mk
      { s.core with wvec := wvec', wstk := wstk', wusable := wusable', num_binary := nb' }
      s.scratch).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with wvec := wvec', wstk := wstk', wusable := wusable', num_binary := nb' }) :
    FullDenseInv c F0 (FullState.mk
      { s.core with wvec := wvec', wstk := wstk', wusable := wusable', num_binary := nb' }
      s.scratch) :=
  let ⟨_, hmrk, hnodup, hext, hl0, hdm⟩ := hinv; ⟨⟨hlen', F_cur, hw'⟩, hmrk, hnodup, hext, hl0, hdm⟩

/-! ## 2. `full_factor_wp` -/

theorem full_factor_wp (Γ : Env)
    (hBvaTryLit : ∀ args m Q X, fullBvaTryLitSpec args m Q X →
      Γ "full_bva_try_lit" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullFactorSpec args m Q X →
      Func.wp Γ full_factor_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hinv.1.lengths.core_ok.cur_vars_le
  bf_steps
  · exact hQ 1#64 s m hinv (Nat.le_refl _) rfl rfl hm
  · refine wp_loop_inv
      (fun (budget, v, ()) ml => ∃ st : FullState,
        FullDenseInv c F0 st ∧ s.core.cur_vars ≤ st.core.cur_vars ∧
        st.core.fuel = s.core.fuel ∧ v.toNat ≤ s.core.cur_vars ∧
        (FullMem c st ⋆ R) ml)
      (fun (_, v, _) _ => s.core.cur_vars - v.toNat)
      (fun Jloop hJloop => by
        bf_steps; exact hJloop (64#64, 0#64, ()) m ⟨s, hinv, Nat.le_refl _, rfl, Nat.zero_le _, hm⟩)
      (fun Jloop (budget, v, ()) ml ⟨st, hst, hcv_st, hfuel_st, hv_le, hml⟩ ih => ?_)
    have hfl_len := hst.1.lengths.core_ok.flags_len
    have hst_cv_le := hst.1.lengths.core_ok.cur_vars_le
    bf_steps
    · rename_i Jnext hJnext _
      have hv_lt : v.toNat < s.core.cur_vars := by c0_bound
      have hv_lt_mx : v.toNat < c.max_vars := by omega
      have hv1_toNat : (v + 1#64).toNat = v.toNat + 1 := by c0_bound
      have h2v : (v <<< (1 : Nat)).toNat = 2 * v.toNat :=
        bv64_shl1_toNat (by show 2 * v.toNat < 2 ^ 64; omega)
      have hv2_toNat : ((v <<< (1 : Nat)).truncate 32).toNat = 2 * v.toNat := by
        rw [BitVec.toNat_setWidth, h2v]; exact Nat.mod_eq_of_lt (by omega)
      have hv2p1_toNat : (((v <<< (1 : Nat)) ||| 1#64).truncate 32).toNat = 2 * v.toNat + 1 := by
        rw [BitVec.toNat_setWidth, FullBvaFwdTactics.bv64_or1_of_even (by rw [h2v]; omega), h2v]
        exact Nat.mod_eq_of_lt (by omega)
      have hst_p := fullDenseInv_set_flags hst
        (st.core.flags.set v.toNat (st.core.flags[v.toNat]'(by omega) &&& ~~~32#32))
        (by simp [hfl_len])
      c0_call hBvaTryLit
      refine ⟨c, F0, _, R, rfl, hst_p, by rw [hv2_toNat]; dsimp only; omega, by assumption,
        fun _ st1 m1 hst1 hcv1 hfuel1 hm1 => ?_⟩
      have hfl1 := hst1.1.lengths.core_ok.flags_len
      have hcv1_st : s.core.cur_vars ≤ st1.core.cur_vars := Nat.le_trans hcv_st hcv1
      apply hJ _ _; bf_steps
      · have hst_n := fullDenseInv_set_flags hst1
          (st1.core.flags.set v.toNat (st1.core.flags[v.toNat]'(by omega) &&& ~~~64#32))
          (by simp [hfl1])
        c0_call hBvaTryLit
        refine ⟨c, F0, _, R, rfl, hst_n, by rw [hv2p1_toNat]; dsimp only; omega, by assumption,
          fun _ st2 m2 hst2 hcv2 hfuel2 hm2 => ?_⟩
        apply hJ _ _; bf_steps
        exact ih (_, v + 1#64, ()) m2 (by dsimp only; rw [hv1_toNat]; omega)
          ⟨st2, hst2, Nat.le_trans hcv1_st hcv2, hfuel2.trans (hfuel1.trans hfuel_st),
           by rw [hv1_toNat]; omega, hm2⟩
      all_goals exact (ih (_, v + 1#64, ()) m1 (by dsimp only; rw [hv1_toNat]; omega)
        ⟨st1, hst1, hcv1_st, hfuel1.trans hfuel_st, by rw [hv1_toNat]; omega, hm1⟩)
    · have hv_lt : v.toNat < s.core.cur_vars := by c0_bound
      have hv1_toNat : (v + 1#64).toNat = v.toNat + 1 := by c0_bound
      have h2v : (v <<< (1 : Nat)).toNat = 2 * v.toNat :=
        bv64_shl1_toNat (by show 2 * v.toNat < 2 ^ 64; omega)
      have hv2p1_toNat : (((v <<< (1 : Nat)) ||| 1#64).truncate 32).toNat = 2 * v.toNat + 1 := by
        rw [BitVec.toNat_setWidth, FullBvaFwdTactics.bv64_or1_of_even (by rw [h2v]; omega), h2v]
        exact Nat.mod_eq_of_lt (by omega)
      have hst_n := fullDenseInv_set_flags hst
        (st.core.flags.set v.toNat (st.core.flags[v.toNat]'(by omega) &&& ~~~64#32))
        (by simp [hfl_len])
      c0_call hBvaTryLit
      refine ⟨c, F0, _, R, rfl, hst_n, by rw [hv2p1_toNat]; dsimp only; omega, by assumption,
        fun _ st2 m2 hst2 hcv2 hfuel2 hm2 => ?_⟩
      bf_steps; exact ih (budget - 1#64, v + 1#64, ()) m2 (by dsimp only; rw [hv1_toNat]; omega)
        ⟨st2, hst2, Nat.le_trans hcv_st hcv2, hfuel2.trans hfuel_st, by rw [hv1_toNat]; omega, hm2⟩
    all_goals try exact hQ 1#64 st ml hst hcv_st hfuel_st rfl hml
    all_goals exact (have hv_lt : v.toNat < s.core.cur_vars := by c0_bound
      have hv1_toNat : (v + 1#64).toNat = v.toNat + 1 := by c0_bound
      ih (budget, v + 1#64, ()) ml (by dsimp only; rw [hv1_toNat]; omega)
        ⟨st, hst, hcv_st, hfuel_st, by rw [hv1_toNat]; omega, hml⟩)

/-! ## 3. Factored pure lemmas & `full_bva_try_lit_wp` -/

private def BvaLoop1Inv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (f0 off sz p qn : Nat) (st1 : FullState) : Prop :=
  AgreesExcept bvaScrMask s st1 ∧
  st1.scratch.scratch_buf.length = c.scratch_cap ∧
  off ≤ p ∧ p ≤ off + sz ∧ qn ≤ 32 ∧
  DenseWatchSliceOk F_cur s.core f0 p (off + sz - p) ∧
  (∀ i < qn,
    let qi := (st1.scratch.scratch_buf[i]?.getD 0#32).toNat
    qi < 2 * s.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [f0, qi]))

private def BvaLoop2Inv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (q0 qoff qsz qn : Nat) (scr1 : List (BitVec 32)) (p dn : Nat) (st2 : FullState) : Prop :=
  AgreesExcept bvaScrMask s st2 ∧
  st2.scratch.scratch_buf.length = c.scratch_cap ∧
  qoff ≤ p ∧ p ≤ qoff + qsz ∧ 1 ≤ dn ∧ dn ≤ 16 ∧
  DenseWatchSliceOk F_cur s.core q0 p (qoff + qsz - p) ∧
  (∀ i < qn, st2.scratch.scratch_buf[i]? = scr1[i]?) ∧
  (∀ j < dn, (st2.scratch.scratch_buf[64 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)

private def BvaLoop3aInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (f0 f1 qn dn : Nat) (scr1 scr2 : List (BitVec 32)) (qi mn : Nat) (st3 : FullState) : Prop :=
  AgreesExcept bvaScrMask s st3 ∧
  st3.scratch.scratch_buf.length = c.scratch_cap ∧
  mn ≤ qi ∧ qi ≤ qn ∧
  (∀ i < qn, st3.scratch.scratch_buf[i]? = scr1[i]?) ∧
  (∀ j < dn, st3.scratch.scratch_buf[64 + j]? = scr2[64 + j]?) ∧
  (∀ k < mn,
    let qk := (st3.scratch.scratch_buf[128 + k]?.getD 0#32).toNat
    qk < 2 * s.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [f0, qk]) ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [f1, qk]))

private def BvaLoop3bInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (qn dn mn : Nat) (scr1 scr2 scr3 : List (BitVec 32)) (dj dm : Nat) (st4 : FullState) : Prop :=
  AgreesExcept bvaScrMask s st4 ∧
  st4.scratch.scratch_buf.length = c.scratch_cap ∧
  2 ≤ dm ∧ dm ≤ 8 ∧ dj ≤ dn ∧
  (∀ i < qn, st4.scratch.scratch_buf[i]? = scr1[i]?) ∧
  (∀ j < dn, st4.scratch.scratch_buf[64 + j]? = scr2[64 + j]?) ∧
  (∀ k < mn, st4.scratch.scratch_buf[128 + k]? = scr3[128 + k]?) ∧
  (∀ j < dm,
    let lj := (st4.scratch.scratch_buf[192 + j]?.getD 0#32).toNat
    lj < 2 * s.core.cur_vars ∧
    ∀ k < mn, (cnfOfClauses F_cur).EntailsClause
      (cnfClause [lj, (scr3[128 + k]?.getD 0#32).toNat]))

private theorem bva_loop1_push {c : FullCfg} {F_cur : List (List Nat)} {s st1 : FullState}
    {f0 off sz p qn : Nat} {ot : BitVec 32} (h : BvaLoop1Inv c F_cur s f0 off sz p qn st1)
    (hscr_ge : 512 ≤ c.scratch_cap) (hp_lt : p < off + sz) (hqn_lt : qn < 32)
    (hot_lt : ot.toNat < 2 * s.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [f0, ot.toNat]))
    (hrem_next : DenseWatchSliceOk F_cur s.core f0 (p + 1) (off + sz - p - 1)) :
    BvaLoop1Inv c F_cur s f0 off sz (p + 1) (qn + 1)
      { st1 with scratch :=
        { st1.scratch with scratch_buf := st1.scratch.scratch_buf.set qn ot } } :=
  let ⟨hag, hsb, hp_ge, hp_le, hqn_le, _, hok⟩ := h
  ⟨hag.trans rfl, by simp [hsb], by omega, by omega, by omega,
    by rw [show off + sz - (p + 1) = off + sz - p - 1 by omega]; exact hrem_next, fun i hi => by
      dsimp only; by_cases hie : i = qn
      · subst hie; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact ⟨hot_lt, hent⟩
      · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hok i (by omega)⟩

private theorem bva_loop2_push {c : FullCfg} {F_cur : List (List Nat)} {s st2 : FullState}
    {q0 qoff qsz qn p dn : Nat} {scr1 : List (BitVec 32)} {cand : BitVec 32}
    (h : BvaLoop2Inv c F_cur s q0 qoff qsz qn scr1 p dn st2)
    (hscr_ge : 512 ≤ c.scratch_cap) (hqn_le : qn ≤ 32) (hp_lt : p < qoff + qsz) (hdn_lt : dn < 16)
    (hcand_lt : cand.toNat < 2 * s.core.cur_vars)
    (hrem_next : DenseWatchSliceOk F_cur s.core q0 (p + 1) (qoff + qsz - p - 1)) :
    BvaLoop2Inv c F_cur s q0 qoff qsz qn scr1 (p + 1) (dn + 1)
      { st2 with scratch :=
          { st2.scratch with scratch_buf := st2.scratch.scratch_buf.set (64 + dn) cand } } :=
  let ⟨hag, hsb, hp_ge, hp_le, hdn_ge, hdn_le, _, hk1, hok⟩ := h
  ⟨hag.trans rfl, by simp [hsb], by omega, by omega, by omega, by omega,
    by rw [show qoff + qsz - (p + 1) = qoff + qsz - p - 1 by omega]; exact hrem_next,
    fun i hi => by dsimp only; rw [List.getElem?_set_ne (by omega)]; exact hk1 i hi,
    fun j hj => by
      dsimp only; by_cases hje : j = dn
      · subst hje; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hcand_lt
      · rw [List.getElem?_set_ne (by omega)]; exact hok j (by omega)⟩

private theorem bva_loop3a_push {c : FullCfg} {F_cur : List (List Nat)} {s st3a : FullState}
    {f0 f1 qn dn qi mn : Nat} {scr1 scr2 : List (BitVec 32)} {q : BitVec 32}
    (h : BvaLoop3aInv c F_cur s f0 f1 qn dn scr1 scr2 qi mn st3a)
    (hscr_ge : 512 ≤ c.scratch_cap) (hqn_le : qn ≤ 32) (hdn_le : dn ≤ 16)
    (hqi_lt : qi < qn) (hq_lt : q.toNat < 2 * s.core.cur_vars)
    (hf0_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [f0, q.toNat]))
    (hf1_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [f1, q.toNat])) :
    BvaLoop3aInv c F_cur s f0 f1 qn dn scr1 scr2 (qi + 1) (mn + 1)
      { st3a with scratch :=
          { st3a.scratch with scratch_buf := st3a.scratch.scratch_buf.set (128 + mn) q } } :=
  let ⟨hag, hsb, hmn_le, hqi_le, hk1, hk2, hok⟩ := h
  ⟨hag.trans rfl, by simp [hsb], by omega, by omega,
    fun i hi => by dsimp only; rw [List.getElem?_set_ne (by omega)]; exact hk1 i hi,
    fun j hj => by dsimp only; rw [List.getElem?_set_ne (by omega)]; exact hk2 j hj,
    fun k hk => by
      dsimp only; by_cases hke : k = mn
      · subst hke; rw [List.getElem?_set_self (by omega), Option.getD_some]
        exact ⟨hq_lt, hf0_ent, hf1_ent⟩
      · rw [List.getElem?_set_ne (by omega)]; exact hok k (by omega)⟩

private theorem bva_loop3b_init {c : FullCfg} {F_cur : List (List Nat)} {s st3a : FullState}
    {f0 f1 : BitVec 32} {qn dn qi mn bi : Nat} {scr1 scr2 : List (BitVec 32)}
    (h : BvaLoop3aInv c F_cur s f0.toNat f1.toNat qn dn scr1 scr2 qi mn st3a)
    (hscr_ge : 512 ≤ c.scratch_cap) (hqn_le : qn ≤ 32) (hdn_le : dn ≤ 16)
    (hbi_lt : bi < dn) (hf0_lt : f0.toNat < 2 * s.core.cur_vars)
    (hf1_lt : f1.toNat < 2 * s.core.cur_vars) :
    BvaLoop3bInv c F_cur s qn dn mn scr1 scr2 st3a.scratch.scratch_buf (bi + 1) 2
      { st3a with scratch :=
          { st3a.scratch with scratch_buf := (st3a.scratch.scratch_buf.set 192 f0).set 193 f1 } } :=
  let ⟨hag, hsb, hmn_le, hqi_le, hk1, hk2, hok⟩ := h
  ⟨hag.trans rfl, by simp [hsb], by omega, by omega, by omega,
    fun i hi => by
      dsimp only; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hk1 i hi,
    fun j hj => by
      dsimp only; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hk2 j hj,
    fun k hk => by
      dsimp only; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)],
    fun j hj => by
      dsimp only; by_cases hj1 : j = 1
      · subst hj1; rw [show 192 + 1 = 193 from rfl, List.getElem?_set_self (by simp [hsb]; omega),
          Option.getD_some]; exact ⟨hf1_lt, fun k hk => (hok k hk).2.2⟩
      · have hj0 : j = 0 := by omega
        subst hj0; rw [Nat.add_zero, List.getElem?_set_ne (by omega),
          List.getElem?_set_self (by omega), Option.getD_some]
        exact ⟨hf0_lt, fun k hk => (hok k hk).2.1⟩⟩

private theorem bva_loop3b_push {c : FullCfg} {F_cur : List (List Nat)} {s st4 : FullState}
    {qn dn mn dj dm : Nat} {scr1 scr2 scr3 : List (BitVec 32)} {fj : BitVec 32}
    (h : BvaLoop3bInv c F_cur s qn dn mn scr1 scr2 scr3 dj dm st4)
    (hscr_ge : 512 ≤ c.scratch_cap) (hqn_le : qn ≤ 32) (hdn_le : dn ≤ 16) (hmn_le : mn ≤ 32)
    (hdj_lt : dj < dn) (hdm_lt : dm < 8) (hfj_lt : fj.toNat < 2 * s.core.cur_vars)
    (hfj_ent : ∀ k < mn, (cnfOfClauses F_cur).EntailsClause
      (cnfClause [fj.toNat, (scr3[128 + k]?.getD 0#32).toNat])) :
    BvaLoop3bInv c F_cur s qn dn mn scr1 scr2 scr3 (dj + 1) (dm + 1)
      { st4 with scratch :=
          { st4.scratch with scratch_buf := st4.scratch.scratch_buf.set (192 + dm) fj } } :=
  let ⟨hag, hsb, hdm_ge, hdm_le, hdj_le, hk1, hk2, hk3, hok⟩ := h
  ⟨hag.trans rfl, by simp [hsb], by omega, by omega, by omega,
    fun i hi => by dsimp only; rw [List.getElem?_set_ne (by omega)]; exact hk1 i hi,
    fun j hj => by dsimp only; rw [List.getElem?_set_ne (by omega)]; exact hk2 j hj,
    fun t ht => by dsimp only; rw [List.getElem?_set_ne (by omega)]; exact hk3 t ht,
    fun j hj => by
      dsimp only; by_cases hje : j = dm
      · subst hje; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact ⟨hfj_lt, hfj_ent⟩
      · rw [List.getElem?_set_ne (by omega)]; exact hok j (by omega)⟩

private theorem bva_lengths_inc_cur_vars {c : FullCfg} {s st4 : FullState}
    (hag : AgreesExcept bvaScrMask s st4) (hlen : s.LengthsOk c)
    (hsb : st4.scratch.scratch_buf.length = c.scratch_cap) (hcv_lt : s.core.cur_vars < c.max_vars)
    (hcv1 : (BitVec.ofNat 64 s.core.cur_vars + 1#64).toNat = s.core.cur_vars + 1) :
    ({ st4 with core := { st4.core with
        cur_vars := (BitVec.ofNat 64 st4.core.cur_vars + 1#64).toNat } } :
      FullState).LengthsOk c := by
  have h1 := bva_scr_lengths hag hlen hsb
  have hcv_eq : st4.core.cur_vars = s.core.cur_vars := by rw [bva_scr_reconstruct hag]
  have hge := h1.core_ok.cur_vars_ge; have hte := h1.core_ok.trail_end_le
  exact { h1 with core_ok := { h1.core_ok with
    cur_vars_ge := by dsimp only; rw [hcv_eq, hcv1]; omega
    cur_vars_le := by dsimp only; rw [hcv_eq, hcv1]; omega
    trail_end_le := by dsimp only; rw [hcv_eq, hcv1]; omega } }

private theorem bva_loop1_skip {c : FullCfg} {F_cur : List (List Nat)} {s st1 : FullState}
    {f0 off sz p qn : Nat} (h : BvaLoop1Inv c F_cur s f0 off sz p qn st1) (hp_lt : p < off + sz)
    (hrem_next : DenseWatchSliceOk F_cur s.core f0 (p + 1) (off + sz - p - 1)) :
    BvaLoop1Inv c F_cur s f0 off sz (p + 1) qn st1 :=
  ⟨h.1, h.2.1, by have := h.2.2.1; omega, by have := h.2.2.2.1; omega, h.2.2.2.2.1,
    by rw [show off + sz - (p + 1) = off + sz - p - 1 by omega]; exact hrem_next, h.2.2.2.2.2.2⟩

private theorem bva_loop1_occ {c : FullCfg} {F_cur : List (List Nat)} {s st1 : FullState}
    {f0 off sz p qn : Nat} (h : BvaLoop1Inv c F_cur s f0 off sz p qn st1) (hp_lt : p < off + sz)
    (h2le : 2 ≤ off + sz - p)
    (hrem_next : DenseWatchSliceOk F_cur s.core f0 (p + 2) (off + sz - p - 2)) :
    BvaLoop1Inv c F_cur s f0 off sz (p + 2) qn st1 :=
  ⟨h.1, h.2.1, by have := h.2.2.1; omega, by have := h.2.2.2.1; omega, h.2.2.2.2.1,
    by rw [show off + sz - (p + 2) = off + sz - p - 2 by omega]; exact hrem_next, h.2.2.2.2.2.2⟩

private theorem bva_loop2_skip {c : FullCfg} {F_cur : List (List Nat)} {s st2 : FullState}
    {q0 qoff qsz qn p dn : Nat} {scr1 : List (BitVec 32)}
    (h : BvaLoop2Inv c F_cur s q0 qoff qsz qn scr1 p dn st2) (hp_lt : p < qoff + qsz)
    (hrem_next : DenseWatchSliceOk F_cur s.core q0 (p + 1) (qoff + qsz - p - 1)) :
    BvaLoop2Inv c F_cur s q0 qoff qsz qn scr1 (p + 1) dn st2 :=
  ⟨h.1, h.2.1, by have := h.2.2.1; omega, by have := h.2.2.2.1; omega,
    h.2.2.2.2.1, h.2.2.2.2.2.1,
    by rw [show qoff + qsz - (p + 1) = qoff + qsz - p - 1 by omega]; exact hrem_next,
    h.2.2.2.2.2.2.2⟩

private theorem bva_loop2_occ {c : FullCfg} {F_cur : List (List Nat)} {s st2 : FullState}
    {q0 qoff qsz qn p dn : Nat} {scr1 : List (BitVec 32)}
    (h : BvaLoop2Inv c F_cur s q0 qoff qsz qn scr1 p dn st2) (hp_lt : p < qoff + qsz)
    (h2le : 2 ≤ qoff + qsz - p)
    (hrem_next : DenseWatchSliceOk F_cur s.core q0 (p + 2) (qoff + qsz - p - 2)) :
    BvaLoop2Inv c F_cur s q0 qoff qsz qn scr1 (p + 2) dn st2 :=
  ⟨h.1, h.2.1, by have := h.2.2.1; omega, by have := h.2.2.2.1; omega,
    h.2.2.2.2.1, h.2.2.2.2.2.1,
    by rw [show qoff + qsz - (p + 2) = qoff + qsz - p - 2 by omega]; exact hrem_next,
    h.2.2.2.2.2.2.2⟩

private theorem bva_commit_dense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st4 st_init : FullState} {qn dn mn dj dm : Nat} {scr1 scr2 scr3 : List (BitVec 32)}
    (hinv : FullDenseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core)
    (hcv_lt : s.core.cur_vars < c.max_vars)
    (h3b : BvaLoop3bInv c F_cur s qn dn mn scr1 scr2 scr3 dj dm st4)
    (hscr3_lt : ∀ k < mn, (scr3[128 + k]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hlen_init : st_init.LengthsOk c)
    {vals' mrk' flags' lvl' rsns' wvec' : _} {unass' : BitVec 64}
    (hcore_init : st_init.core =
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
    (hll_init : st_init.scratch.last_learned = st4.scratch.last_learned)
    (hext_init : st_init.scratch.extend_len = st4.scratch.extend_len)
    (hsb_init : st_init.scratch.scratch_buf = st4.scratch.scratch_buf) :
    ∃ F_next : List (List Nat),
      FullWitnessInv c F0 F_next st_init.core ∧ FullDenseInv c F0 st_init ∧
      (∀ j < dm, (cnfOfClauses F_next).EntailsClause
        (cnfClause [2 * s.core.cur_vars,
          (st_init.scratch.scratch_buf[192 + j]?.getD 0#32).toNat])) ∧
      (∀ k < mn, (cnfOfClauses F_next).EntailsClause
        (cnfClause [2 * s.core.cur_vars + 1,
          (st_init.scratch.scratch_buf[128 + k]?.getD 0#32).toNat])) := by
  let L := (List.range dm).map fun j => (st4.scratch.scratch_buf[192 + j]?.getD 0#32).toNat
  let Q := (List.range mn).map fun k => (st4.scratch.scratch_buf[128 + k]?.getD 0#32).toNat
  have hst4_eq := bva_scr_reconstruct h3b.1
  have hll_s : st_init.scratch.last_learned = s.scratch.last_learned := by rw [hll_init, hst4_eq]
  have hext_s : st_init.scratch.extend_len = s.scratch.extend_len := by rw [hext_init, hst4_eq]
  have hL : ∀ l ∈ L, l < 2 * s.core.cur_vars := by
    intro l hl; simp only [L, List.mem_map, List.mem_range] at hl
    obtain ⟨j, hj, rfl⟩ := hl; exact (h3b.2.2.2.2.2.2.2.2 j hj).1
  have hQ_lt : ∀ q ∈ Q, q < 2 * s.core.cur_vars := by
    intro q hq; simp only [Q, List.mem_map, List.mem_range] at hq
    obtain ⟨k, hk, rfl⟩ := hq
    rw [h3b.2.2.2.2.2.2.2.1 k hk]; exact hscr3_lt k hk
  have hprod : ∀ l ∈ L, ∀ q ∈ Q, (cnfOfClauses F_cur).EntailsClause (cnfClause [l, q]) := by
    intro l hl q hq; simp only [L, Q, List.mem_map, List.mem_range] at hl hq
    obtain ⟨j, hj, rfl⟩ := hl; obtain ⟨k, hk, rfl⟩ := hq
    rw [h3b.2.2.2.2.2.2.2.1 k hk]; exact (h3b.2.2.2.2.2.2.2.2 j hj).2 k hk
  have ⟨hw', hd'⟩ := fullDenseInv_add_fresh_var hinv.1.lengths hw hinv.2.1 hinv.2.2.1
    hinv.2.2.2.1 hinv.2.2.2.2.1 hinv.2.2.2.2.2 hcv_lt hL hQ_lt hprod
    hlen_init hcore_init hv0 hv1 hv_oth hmrk_fv hmrk_oth hlvl_oth hrsns_oth hwvec_0 hwvec_oth
    hll_s hext_s
  have hpos_ent : ∀ j < dm,
      (cnfOfClauses (bvaExtendFormula s.core.cur_vars L Q F_cur)).EntailsClause
        (cnfClause [2 * s.core.cur_vars,
          (st_init.scratch.scratch_buf[192 + j]?.getD 0#32).toNat]) :=
    fun j hj => by
      rw [hsb_init]; exact bvaExtendFormula_entails_pos
        (by simp only [L, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
  have hneg_ent : ∀ k < mn,
      (cnfOfClauses (bvaExtendFormula s.core.cur_vars L Q F_cur)).EntailsClause
        (cnfClause [2 * s.core.cur_vars + 1,
          (st_init.scratch.scratch_buf[128 + k]?.getD 0#32).toNat]) :=
    fun k hk => by
      rw [hsb_init]; exact bvaExtendFormula_entails_neg
        (by simp only [Q, List.mem_map, List.mem_range]; exact ⟨k, hk, rfl⟩)
  exact ⟨bvaExtendFormula s.core.cur_vars L Q F_cur, hw', hd', hpos_ent, hneg_ent⟩

private def bvaCommitTailExpr (h scr_ptr : Val i64) (fv2 dm mn : Val i32) :
    Expr Val Cont [.bool] :=
  let op32 (c : OpCode [i32, i32] [i32]) (a b : Arg Val i32)
      (k : Val i32 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
    Expr.let_ { sig := [i32, i32], code := c, args := (a, b, ()) } fun p => k p.fst
  let cmp32 (op : CmpOp) (a b : Arg Val i32) (k : Val .bool → Expr Val Cont [.bool]) :=
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp op i32, args := (a, b, ()) } fun p =>
      k p.fst
  let ldSb (pidx : Arg Val i32) (k : Val i32 → Expr Val Cont [.bool]) :=
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (pidx, ()) } fun p1 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                args := (Arg.var p1.fst, Arg.imm 4, ()) } fun p2 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var scr_ptr, Arg.var p2.fst, ()) } fun p3 =>
    Expr.load i32 (Arg.var p3.fst) k
  Expr.group (fun Js => Blocks.cons (fun (p_96 : Tup Val [i32]) =>
    cmp32 .ult (Arg.var p_96.fst) (Arg.var dm) fun b => Expr.jnz (Arg.var b)
      (op32 (OpCode.add i32) (Arg.imm 192) (Arg.var p_96.fst) fun p_98 =>
       ldSb (Arg.var p_98) fun ld =>
       Expr.call "full_add_bin" (as := [i64, i32, i32]) (bs := [i64])
         (Arg.var h, Arg.var fv2, Arg.var ld, ()) fun _ =>
       op32 (OpCode.add i32) (Arg.var p_96.fst) (Arg.imm 1) fun p =>
       Expr.jump Js.fst (Arg.var p, ()))
      (Expr.group (fun Js => Blocks.cons (fun (p_98 : Tup Val [i32, i32]) =>
        cmp32 .ult (Arg.var p_98.snd.fst) (Arg.var mn) fun b => Expr.jnz (Arg.var b)
          (op32 (OpCode.add i32) (Arg.imm 128) (Arg.var p_98.snd.fst) fun p_100 =>
           ldSb (Arg.var p_100) fun ld =>
           Expr.group (fun Js_4 => Blocks.cons (fun (p_104 : Tup Val [i32]) =>
             cmp32 .ult (Arg.var p_104.fst) (Arg.var dm) fun b2 => Expr.jnz (Arg.var b2)
               (op32 (OpCode.add i32) (Arg.imm 192) (Arg.var p_104.fst) fun p_106 =>
                ldSb (Arg.var p_106) fun ld_11 =>
                Expr.call "full_delete_binary" (as := [i64, i32, i32]) (bs := [])
                  (Arg.var h, Arg.var ld_11, Arg.var ld, ()) fun _ =>
                op32 (OpCode.add i32) (Arg.var p_104.fst) (Arg.imm 1) fun p =>
                Expr.jump Js_4.fst (Arg.var p, ()))
               (op32 (OpCode.xor i32) (Arg.var fv2) (Arg.imm 1) fun p_106 =>
                Expr.call "full_add_bin" (as := [i64, i32, i32]) (bs := [i64])
                  (Arg.var h, Arg.var p_106, Arg.var ld, ()) fun _ =>
                op32 (OpCode.add i32) (Arg.var p_98.snd.fst) (Arg.imm 1) fun p =>
                Expr.jump Js.fst (Arg.var p_104.fst, Arg.var p, ()))) Blocks.nil)
             fun Js => Expr.jump Js.fst (Arg.imm 0, ()))
          (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                       args := (Arg.var h, Arg.imm 1104, ()) } fun p_100 =>
           Expr.load i64 (Arg.var p_100.fst) fun ld =>
           Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                       args := (Arg.var ld, Arg.imm 1, ()) } fun p_101 =>
           Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                       args := (Arg.var h, Arg.imm 1104, ()) } fun p =>
           Expr.store (Arg.var p_101.fst) (Arg.var p.fst) (Expr.ret (Arg.imm true, ()))))
        Blocks.nil) fun Js => Expr.jump Js.fst (Arg.var p_96.fst, Arg.imm 0, ()))) Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 0, ())

private theorem bva_commit_tail_wp (Γ : Env)
    (hAddBin : ∀ args m Q X, fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X)
    (hDelBin : ∀ args m Q X, fullDeleteBinarySpec args m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] args m Q X)
    (c : FullCfg) {F0 : CNF Nat} {F_next : List (List Nat)}
    {s st_init : FullState} {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost}
    {m_init : Mem 64} {dm mn : Val i32} {old_cv : Nat}
    (hdm_le : dm.toNat ≤ 8) (hmn_le : mn.toNat ≤ 32)
    (hcv_lt : old_cv < c.max_vars) (hmx : c.max_vars < 2 * 2 ^ 28)
    (hd_init : FullDenseInv c F0 st_init) (hw_init : FullWitnessInv c F0 F_next st_init.core)
    (hcv_init : st_init.core.cur_vars = old_cv + 1) (hfuel_init : st_init.core.fuel = s.core.fuel)
    (hscr_ge : 512 ≤ c.scratch_cap)
    (hpos_ent : ∀ j < dm.toNat, (cnfOfClauses F_next).EntailsClause
      (cnfClause [2 * old_cv, (st_init.scratch.scratch_buf[192 + j]?.getD 0#32).toNat]))
    (hneg_ent : ∀ k < mn.toNat, (cnfOfClauses F_next).EntailsClause
      (cnfClause [2 * old_cv + 1, (st_init.scratch.scratch_buf[128 + k]?.getD 0#32).toNat]))
    (hm_init : (FullMem c st_init ⋆ R) m_init)
    (hQ : ∀ (r : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInv c F0 s' → old_cv ≤ s'.core.cur_vars → s'.core.fuel = s.core.fuel →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (bvaCommitTailExpr c.hdr c.pScratchBuf
      (BitVec.setWidth 32 (BitVec.ofNat 64 old_cv) <<< (1 : Nat)) dm mn) m_init := by
  have hfv_n : (BitVec.setWidth 32 (BitVec.ofNat 64 old_cv)).toNat = old_cv := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hfresh_n :
      (BitVec.setWidth 32 (BitVec.ofNat 64 old_cv) <<< (1 : Nat)).toNat = 2 * old_cv := by
    rw [BitVec.toNat_shiftLeft, hfv_n, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  have hfresh1_n : ((BitVec.setWidth 32 (BitVec.ofNat 64 old_cv) <<< (1 : Nat)) ^^^ 1#32).toNat =
      2 * old_cv + 1 := bva_bv32_shl1_xor1 (by omega)
  unfold bvaCommitTailExpr; dsimp only
  refine wp_loop_inv
    (fun (j, ()) mlc => ∃ stc : FullState, FullDenseInv c F0 stc ∧
      FullWitnessInv c F0 F_next stc.core ∧ stc.core.cur_vars = old_cv + 1 ∧
      stc.core.fuel = s.core.fuel ∧ stc.scratch.scratch_buf = st_init.scratch.scratch_buf ∧
      j.toNat ≤ dm.toNat ∧ (FullMem c stc ⋆ R) mlc)
    (fun (j, ()) _ => dm.toNat - j.toNat)
    (fun Jc hJc => by
      bf_steps; exact hJc (0#32, ()) m_init ⟨st_init, hd_init, hw_init, hcv_init, hfuel_init, rfl,
        by rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega, hm_init⟩)
    (fun Jc (j, ()) mlc ⟨stc, hdc, hwc, hcvc, hfuelc, hsbc, hj_le, hmlc⟩ ihc => ?_)
  have hsbc_len : stc.scratch.scratch_buf.length = c.scratch_cap :=
    hdc.1.lengths.scratch_ok.scratch_buf_len
  bf_steps
  · have hj_lt : j.toNat < dm.toNat := hc
    have h192j_n : ((192 : BitVec 32) + j).toNat = 192 + j.toNat :=
      bv32_add_toNat (show 192 + j.toNat < 2 ^ 32 by omega)
    have hidx192 : (BitVec.setWidth 64 ((192 : BitVec 32) + j)).toNat = 192 + j.toNat := by
      rw [bv64_zext32_toNat, h192j_n]
    have h192j_sb : (BitVec.setWidth 64 ((192 : BitVec 32) + j)).toNat <
        stc.scratch.scratch_buf.length := by rw [hidx192, hsbc_len]; omega
    have hj1_n : (j + 1#32).toNat = j.toNat + 1 :=
      bv32_add_toNat (show j.toNat + 1 < 2 ^ 32 by omega)
    bf_steps; c0_call hAddBin
    refine ⟨c, F0, F_next, stc, R, rfl, hdc.1.lengths, hwc, hdc.2.2.2.2.1, fun _ _ => by
      have hpos := hpos_ent j.toNat hj_lt
      rw [← hfresh_n, ← hsbc, ← hidx192, List.getElem?_eq_getElem h192j_sb, Option.getD_some]
        at hpos
      exact hpos, hmlc,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc' hlenc' hwc' _ _ _ hmc' => ?_⟩
    bf_steps; exact ihc (j + 1#32, ()) mc' (by dsimp only; rw [hj1_n]; omega)
      ⟨_, fullDenseInv_of_addBin hdc hlenc' hwc' hdc.2.2.2.2.1 rfl rfl rfl rfl rfl rfl rfl,
        hwc', hcvc, hfuelc, hsbc, by rw [hj1_n]; omega, hmc'⟩
  · refine wp_loop_inv (fun (_, k, ()) mld => ∃ std : FullState, FullDenseInv c F0 std ∧
        FullWitnessInv c F0 F_next std.core ∧ std.core.cur_vars = old_cv + 1 ∧
        std.core.fuel = s.core.fuel ∧ std.scratch.scratch_buf = st_init.scratch.scratch_buf ∧
        k.toNat ≤ mn.toNat ∧ (FullMem c std ⋆ R) mld)
      (fun (_, k, _) _ => mn.toNat - k.toNat)
      (fun Jd hJd => by bf_steps; exact hJd (j, 0#32, ()) mlc ⟨stc, hdc, hwc, hcvc, hfuelc, hsbc,
        by rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega, hmlc⟩)
      (fun Jd (_, k, ()) mld ⟨std, hdd, hwd, hcvd, hfueld, hsbd, hk_le, hmld⟩ ihd => ?_)
    have hsbd_len := hdd.1.lengths.scratch_ok.scratch_buf_len
    bf_steps
    · have hk_lt : k.toNat < mn.toNat := hc
      have h128k_n : ((128 : BitVec 32) + k).toNat = 128 + k.toNat :=
        bv32_add_toNat (show 128 + k.toNat < 2 ^ 32 by omega)
      have hidx128 : (BitVec.setWidth 64 ((128 : BitVec 32) + k)).toNat = 128 + k.toNat := by
        rw [bv64_zext32_toNat, h128k_n]
      have h128k_sb : (BitVec.setWidth 64 ((128 : BitVec 32) + k)).toNat <
          std.scratch.scratch_buf.length := by rw [hidx128, hsbd_len]; omega
      have hk1_n : (k + 1#32).toNat = k.toNat + 1 :=
        bv32_add_toNat (show k.toNat + 1 < 2 ^ 32 by omega)
      bf_steps; generalize hqv : std.scratch.scratch_buf[(BitVec.setWidth 64
          ((128 : BitVec 32) + k)).toNat]'h128k_sb = q at *
      refine wp_loop_inv (fun (j, ()) mldi => ∃ stdi : FullState, FullDenseInv c F0 stdi ∧
          FullWitnessInv c F0 F_next stdi.core ∧ stdi.core.cur_vars = old_cv + 1 ∧
          stdi.core.fuel = s.core.fuel ∧ stdi.scratch.scratch_buf = st_init.scratch.scratch_buf ∧
          j.toNat ≤ dm.toNat ∧ (FullMem c stdi ⋆ R) mldi)
        (fun (j, ()) _ => dm.toNat - j.toNat)
        (fun Jdi hJdi => by bf_steps; exact hJdi (0#32, ()) mld ⟨std, hdd, hwd, hcvd, hfueld, hsbd,
          by rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega, hmld⟩)
        (fun Jdi (j, ()) mldi ⟨stdi, hddi, hwdi, hcvdi, hfueldi, hsbdi, hji_le, hmldi⟩
          ihdi => ?_)
      have hsbdi_len := hddi.1.lengths.scratch_ok.scratch_buf_len
      bf_steps
      · have hji_lt : j.toNat < dm.toNat := hc
        have h192j_n : ((192 : BitVec 32) + j).toNat = 192 + j.toNat :=
          bv32_add_toNat (show 192 + j.toNat < 2 ^ 32 by omega)
        have h192j_sb : (BitVec.setWidth 64 ((192 : BitVec 32) + j)).toNat <
            stdi.scratch.scratch_buf.length := by rw [bv64_zext32_toNat, h192j_n, hsbdi_len]; omega
        have hj1_n : (j + 1#32).toNat = j.toNat + 1 :=
          bv32_add_toNat (show j.toNat + 1 < 2 ^ 32 by omega)
        bf_steps; c0_call hDelBin
        have hdwi : DenseWatchesInv F_next stdi.core := by
          have h := hwdi.watches; unfold ModeWatchesInv at h
          rwa [ite_eq_right hddi.2.2.2.2.2] at h
        refine ⟨c, stdi, R, rfl, hddi.1.lengths, hdwi.layout, hmldi,
          fun wv' ws' wu' nb' mdi' hlendi' _ hmode' hmdi' => ?_⟩
        have hwdi' : FullWitnessInv c F0 F_next
            { stdi.core with wvec := wv', wstk := ws', wusable := wu', num_binary := nb' } :=
          { hwdi with
            arena := { hwdi.arena with len_ok := hwdi.arena.len_ok }
            watches := hmode' F_next hwdi.watches }
        bf_steps; exact ihdi (j + 1#32, ()) mdi' (by dsimp only; rw [hj1_n]; omega)
          ⟨_, fullDenseInv_of_delBin hddi hlendi' hwdi', hwdi', hcvdi, hfueldi, hsbdi,
           by rw [hj1_n]; omega, hmdi'⟩
      · c0_call hAddBin
        refine ⟨c, F0, F_next, stdi, R, rfl, hddi.1.lengths, hwdi, hddi.2.2.2.2.1, fun _ _ => by
          have hneg := hneg_ent k.toNat hk_lt
          rw [← hfresh1_n, ← hsbd, ← hidx128, List.getElem?_eq_getElem h128k_sb, Option.getD_some,
            hqv] at hneg
          simpa only [show (1 : BitVec 32) = 1#32 from rfl] using hneg, hmldi,
          fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ md' hlend' hwd' _ _ _ hmd' => ?_⟩
        bf_steps; exact ihd (j, k + 1#32, ()) md' (by dsimp only; rw [hk1_n]; omega)
          ⟨_, fullDenseInv_of_addBin hddi hlend' hwd' hddi.2.2.2.2.1 rfl rfl rfl rfl rfl rfl rfl,
            hwd', hcvdi, hfueldi, hsbdi, by rw [hk1_n]; omega, hmd'⟩
    · exact hQ true _ _ (fullDenseInv_set_bva_cnt hdd (std.scratch.bva_cnt + 1#64))
        (by dsimp only; rw [hcvd]; omega) hfueld hm

private theorem bva_commit_after_init (Γ : Env)
    (hAddBin : ∀ args m Q X, fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X)
    (hDelBin : ∀ args m Q X, fullDeleteBinarySpec args m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] args m Q X)
    (c : FullCfg) {F0 : CNF Nat} {F_cur : List (List Nat)} {s st4 st_init : FullState}
    {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost} {m_init : Mem 64} {dm mn : Val i32}
    {qn dn dj : Nat} {scr1 scr2 scr3 : List (BitVec 32)}
    (hdm_le : dm.toNat ≤ 8) (hmn_le : mn.toNat ≤ 32) (hcv_lt : s.core.cur_vars < c.max_vars)
    (hmx : c.max_vars < 2 * 2 ^ 28) (hscr_ge : 512 ≤ c.scratch_cap)
    (hinv : FullDenseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core)
    (h3b : BvaLoop3bInv c F_cur s qn dn mn.toNat scr1 scr2 scr3 dj dm.toNat st4)
    (hscr3_lt : ∀ k < mn.toNat, (scr3[128 + k]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hlen_init : st_init.LengthsOk c)
    {vals' mrk' flags' lvl' rsns' wvec' : _} {unass' : BitVec 64}
    (hcore_init : st_init.core =
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
    (hll_init : st_init.scratch.last_learned = st4.scratch.last_learned)
    (hext_init : st_init.scratch.extend_len = st4.scratch.extend_len)
    (hsb_init : st_init.scratch.scratch_buf = st4.scratch.scratch_buf)
    (hm_init : (FullMem c st_init ⋆ R) m_init)
    (hQ : ∀ (r : Bool) (s' : FullState) (m' : Mem 64), FullDenseInv c F0 s' →
      s.core.cur_vars ≤ s'.core.cur_vars → s'.core.fuel = s.core.fuel →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (bvaCommitTailExpr c.hdr c.pScratchBuf
      (BitVec.setWidth 32 (BitVec.ofNat 64 st4.core.cur_vars) <<< (1 : Nat)) dm mn) m_init := by
  have ⟨F_next, hw_init, hd_init, hpos_ent, hneg_ent⟩ :=
    bva_commit_dense hinv hw hcv_lt h3b hscr3_lt hlen_init hcore_init hv0 hv1 hv_oth hmrk_fv
      hmrk_oth hlvl_oth hrsns_oth hwvec_0 hwvec_oth hll_init hext_init hsb_init
  rw [bva_scr_reconstruct h3b.1]
  exact bva_commit_tail_wp Γ hAddBin hDelBin c hdm_le hmn_le hcv_lt hmx hd_init hw_init
    (by rw [hcore_init]) (by rw [hcore_init]) hscr_ge hpos_ent hneg_ent hm_init hQ

private def bvaLoop3bInnerExpr (h scr_ptr : Val i64) (mn fj : Val i32)
    (Js : Cont [.bool, i32]) : Expr Val Cont [.bool] :=
  Expr.group (fun Js_1 => Blocks.cons (fun (p : Tup Val [i32]) =>
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32,
                args := (Arg.var p.fst, Arg.var mn, ()) } fun p_1 =>
    Expr.jnz (Arg.var p_1.fst)
      (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                   args := (Arg.imm 128, Arg.var p.fst, ()) } fun p_2 =>
       Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                   args := (Arg.var p_2.fst, ()) } fun p_3 =>
       Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                   args := (Arg.var p_3.fst, Arg.imm 4, ()) } fun p_4 =>
       Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                   args := (Arg.var scr_ptr, Arg.var p_4.fst, ()) } fun p_5 =>
       Expr.load i32 (Arg.var p_5.fst) fun ld_1 =>
       Expr.call "full_has_bin" (as := [i64, i32, i32]) (bs := [.bool])
         (Arg.var h, Arg.var fj, Arg.var ld_1, ()) fun p_6 =>
       Expr.jnz (Arg.var p_6.fst)
         (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                      args := (Arg.var p.fst, Arg.imm 1, ()) } fun p =>
          Expr.jump Js_1.fst (Arg.var p.fst, ()))
         (Expr.jump Js (Arg.imm false, Arg.var p.fst, ())))
      (Expr.jump Js (Arg.imm true, Arg.var p.fst, ()))) Blocks.nil)
  fun Js_1 => Expr.jump Js_1.fst (Arg.imm 0, ())

private theorem bva_loop3b_inner_wp (Γ : Env)
    (hHasBin : ∀ args m Q X, fullHasBinSpec args m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] args m Q X)
    (c : FullCfg) {F0 : CNF Nat} {F_cur : List (List Nat)} {s st4 : FullState}
    {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost} {ml4 : Mem 64}
    {mn fj : Val i32} {scr3 : List (BitVec 32)} {Js : Cont [.bool, i32]}
    (hscr_ge : 512 ≤ c.scratch_cap) (hmn_le : mn.toNat ≤ 32)
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hag : AgreesExcept bvaScrMask s st4) (hsb4 : st4.scratch.scratch_buf.length = c.scratch_cap)
    (hk3 : ∀ k < mn.toNat, st4.scratch.scratch_buf[128 + k]? = scr3[128 + k]?)
    (hml4 : (FullMem c st4 ⋆ R) ml4)
    (hbreak : ∀ (k : Val i32) (ml4i : Mem 64), (FullMem c st4 ⋆ R) ml4i → Js (false, k, ()) ml4i)
    (hdone : ∀ (k : Val i32) (ml4i : Mem 64), k.toNat = mn.toNat →
      (∀ t < mn.toNat, (cnfOfClauses F_cur).EntailsClause
        (cnfClause [fj.toNat, (scr3[128 + t]?.getD 0#32).toNat])) →
      (FullMem c st4 ⋆ R) ml4i → Js (true, k, ()) ml4i) :
    wp Γ Q X (bvaLoop3bInnerExpr c.hdr c.pScratchBuf mn fj Js) ml4 := by
  have hst4_eq := bva_scr_reconstruct hag
  unfold bvaLoop3bInnerExpr
  refine wp_loop_inv
    (fun (k, ()) ml4i => k.toNat ≤ mn.toNat ∧ (∀ t < k.toNat,
      (cnfOfClauses F_cur).EntailsClause (cnfClause [fj.toNat, (scr3[128 + t]?.getD 0#32).toNat]))
      ∧ (FullMem c st4 ⋆ R) ml4i)
    (fun (k, ()) _ => mn.toNat - k.toNat)
    (fun J4i hJ4i => by
      bf_steps; exact hJ4i (0#32, ()) ml4
        ⟨by rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega, fun _ h => by simp at h, hml4⟩)
    (fun J4i (k, ()) ml4i ⟨hk_le, ham_ok, hml4i⟩ ih4i => ?_)
  bf_steps
  · have hk_lt : k.toNat < mn.toNat := hc
    have h128k_n : ((128 : BitVec 32) + k).toNat = 128 + k.toNat :=
      bv32_add_toNat (show 128 + k.toNat < 2 ^ 32 by omega)
    have hidx128 : (BitVec.setWidth 64 ((128 : BitVec 32) + k)).toNat = 128 + k.toNat := by
      rw [bv64_zext32_toNat, h128k_n]
    have h128k_sb : (BitVec.setWidth 64 ((128 : BitVec 32) + k)).toNat <
        st4.scratch.scratch_buf.length := by rw [hidx128, hsb4]; omega
    have hk1_n : (k + 1#32).toNat = k.toNat + 1 :=
      bv32_add_toNat (show k.toNat + 1 < 2 ^ 32 by omega)
    bf_steps; c0_call hHasBin
    refine ⟨c, F0, F_cur, st4, R, rfl, bva_scr_lengths hag hlen hsb4,
      by rw [hst4_eq]; exact hw, hml4i, fun rb hrb => ?_⟩
    bf_steps
    · have hrb_t := hrb hc
      refine ih4i _ _ (by
          dsimp only; rw [show (k + 1 : BitVec 32) = k + 1#32 from rfl, hk1_n]; omega)
        ⟨by rw [show (k + 1 : BitVec 32) = k + 1#32 from rfl, hk1_n]; omega,
         fun t ht => ?_, hml4i⟩
      rw [show (k + 1 : BitVec 32) = k + 1#32 from rfl, hk1_n] at ht
      by_cases htk : t = k.toNat
      · subst htk; have h2 := hrb_t.2.2.2.2
        rw [← hk3 k.toNat hk_lt, ← hidx128, List.getElem?_eq_getElem h128k_sb, Option.getD_some]
        exact h2
      · exact ham_ok t (by omega)
    · exact hbreak k ml4i hml4i
  · have hk_eq : k.toNat = mn.toNat := by have : ¬ k.toNat < mn.toNat := hc; omega
    exact hdone k ml4i hk_eq (fun t ht => ham_ok t (by omega)) hml4i

private def bvaLoop3bExpr (h scr_ptr : Val i64) (dn mn bi1 : Val i32) (Js_bi : Cont []) :
    Expr Val Cont [.bool] :=
  let zext64 (v : Val i32) (k : Val i64 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var v, ()) } fun p => k p.fst
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64)
      (k : Val i64 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
    Expr.let_ { sig := [i64, i64], code := c, args := (a, b, ()) } fun p => k p.fst
  let ld64 (off : Val i64) (k : Val i64 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
    op64 (OpCode.add i64) (Arg.var h) (Arg.imm off) fun p => Expr.load i64 (Arg.var p) k
  let ldSb (pidx : Arg Val i32) (k : Val i32 → Expr Val Cont [.bool]) :
      Expr Val Cont [.bool] :=
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (pidx, ()) } fun p1 =>
    op64 (OpCode.mul i64) (Arg.var p1.fst) (Arg.imm 4) fun p2 =>
    op64 (OpCode.add i64) (Arg.var scr_ptr) (Arg.var p2) fun p3 => Expr.load i32 (Arg.var p3) k
  Expr.group (fun Js_2 => Blocks.cons (fun (p_71 : Tup Val [i32, i32]) =>
    Expr.group (fun Js_3 => Blocks.cons (fun (_ : Tup Val []) =>
      zext64 p_71.fst fun d64 => zext64 mn fun m64 =>
      op64 (OpCode.mul i64) (Arg.var d64) (Arg.var m64) fun p_75 =>
      zext64 p_71.fst fun d64b => zext64 mn fun m64b =>
      op64 (OpCode.add i64) (Arg.var d64b) (Arg.var m64b) fun p_78 =>
      Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64,
                  args := (Arg.var p_75, Arg.var p_78, ()) } fun p_79 =>
      Expr.jnz (Arg.var p_79.fst)
        (ld64 40 fun ld => ld64 56 fun ld_10 =>
         op64 (OpCode.sub i64) (Arg.var ld) (Arg.var ld_10) fun p_82 =>
         zext64 p_71.fst fun d64c => zext64 mn fun m64c =>
         op64 (OpCode.add i64) (Arg.var d64c) (Arg.var m64c) fun p_85 =>
         op64 (OpCode.add i64) (Arg.var p_85) (Arg.imm 4) fun p_86 =>
         op64 (OpCode.mul i64) (Arg.var p_86) (Arg.imm 8) fun p_87 =>
         Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.uge i64,
                     args := (Arg.var p_82, Arg.var p_87, ()) } fun p_88 =>
         Expr.jnz (Arg.var p_88.fst)
           (ld64 776 fun ld =>
            Expr.let_ { sig := [i64], code := OpCode.trunc 64 32,
                        args := (Arg.var ld, ()) } fun p_90 =>
            ld64 776 fun ld =>
            op64 (OpCode.add i64) (Arg.var ld) (Arg.imm 1) fun p_92 =>
            op64 (OpCode.add i64) (Arg.var h) (Arg.imm 776) fun p_93 =>
            Expr.store (Arg.var p_92) (Arg.var p_93)
              (Expr.call "full_init_fresh_var" (as := [i64, i32]) (bs := [])
                (Arg.var h, Arg.var p_90.fst, ()) fun _ =>
               Expr.let_ { sig := [i32, i32], code := OpCode.shl i32,
                           args := (Arg.var p_90.fst, Arg.imm 1, ()) } fun p_95 =>
               bvaCommitTailExpr h scr_ptr p_95.fst p_71.fst mn))
           (Expr.jump Js_bi ()))
        (Expr.jump Js_bi ())) Blocks.nil)
    fun Js_3 =>
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32,
                args := (Arg.var p_71.snd.fst, Arg.var dn, ()) } fun p_72 =>
    Expr.jnz (Arg.var p_72.fst)
      (Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32,
                   args := (Arg.var p_71.fst, Arg.imm 8, ()) } fun p_73 =>
       Expr.jnz (Arg.var p_73.fst)
         (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                      args := (Arg.imm 64, Arg.var p_71.snd.fst, ()) } fun p_74 =>
          ldSb (Arg.var p_74.fst) fun ld =>
          Expr.group (fun Js_i => Blocks.cons (fun (p_7 : Tup Val [.bool, i32]) =>
            Expr.group (fun Js_ii => Blocks.cons (fun (p_8 : Tup Val [i32]) =>
              Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                           args := (Arg.var p_71.snd.fst, Arg.imm 1, ()) } fun p_9 =>
              Expr.jump Js_2.fst (Arg.var p_8.fst, Arg.var p_9.fst, ())) Blocks.nil)
            fun Js_ii => Expr.jnz (Arg.var p_7.fst)
              (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                           args := (Arg.imm 192, Arg.var p_71.fst, ()) } fun p_8 =>
               Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                           args := (Arg.var p_8.fst, ()) } fun p_9 =>
               op64 (OpCode.mul i64) (Arg.var p_9.fst) (Arg.imm 4) fun p_10 =>
               op64 (OpCode.add i64) (Arg.var scr_ptr) (Arg.var p_10) fun p_11 =>
               Expr.store (Arg.var ld) (Arg.var p_11)
                 (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                              args := (Arg.var p_71.fst, Arg.imm 1, ()) } fun p_12 =>
                  Expr.jump Js_ii.fst (Arg.var p_12.fst, ())))
              (Expr.jump Js_ii.fst (Arg.var p_71.fst, ()))) Blocks.nil)
          fun Js_i => bvaLoop3bInnerExpr h scr_ptr mn ld Js_i.fst)
         (Expr.jump Js_3.fst ()))
      (Expr.jump Js_3.fst ())) Blocks.nil)
  fun Js_2 => Expr.jump Js_2.fst (Arg.imm 2, Arg.var bi1, ())

private def bvaPost3aExpr (h scr_ptr : Val i64) (dn bi f0 f1 mn : Val i32) (J3 : Cont [i32]) :
    Expr Val Cont [.bool] :=
  let stSb (off : Val i32) (v : Val i32) (k : Expr Val Cont [.bool]) :=
    Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm off, ()) } fun p1 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                args := (Arg.var p1.fst, Arg.imm 4, ()) } fun p2 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var scr_ptr, Arg.var p2.fst, ()) } fun p3 =>
    Expr.store (Arg.var v) (Arg.var p3.fst) k
  Expr.group (fun Js => Blocks.cons (fun (_ : Tup Val []) =>
    Expr.let_ { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var bi, Arg.imm 1, ()) }
      fun p => Expr.jump J3 (Arg.var p.fst, ())) Blocks.nil)
  fun Js => Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.uge i32,
                        args := (Arg.var mn, Arg.imm 2, ()) } fun p_2 =>
  Expr.jnz (Arg.var p_2.fst)
    (stSb 192 f0 (stSb 193 f1 (Expr.let_
      { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var bi, Arg.imm 1, ()) }
      fun p_9 => bvaLoop3bExpr h scr_ptr dn mn p_9.fst Js.fst)))
    (Expr.jump Js.fst ())

private def bvaLoop3aExpr (h scr_ptr : Val i64) (qn f1 : Val i32)
    (after : Val i32 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  let ldSb (pidx : Arg Val i32) (k : Val i32 → Expr Val Cont [.bool]) :=
    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (pidx, ()) } fun p1 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                args := (Arg.var p1.fst, Arg.imm 4, ()) } fun p2 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var scr_ptr, Arg.var p2.fst, ()) } fun p3 =>
    Expr.load i32 (Arg.var p3.fst) k
  Expr.group (fun Js_1 => Blocks.cons (fun (p_61 : Tup Val [i32, i32]) =>
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32,
                args := (Arg.var p_61.snd.fst, Arg.var qn, ()) } fun p_62 =>
    Expr.jnz (Arg.var p_62.fst)
      (Expr.group (fun Js => Blocks.cons (fun (p : Tup Val [i32]) =>
        Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                    args := (Arg.var p_61.snd.fst, Arg.imm 1, ()) } fun p_63 =>
        Expr.jump Js_1.fst (Arg.var p.fst, Arg.var p_63.fst, ())) Blocks.nil)
       fun Js =>
       ldSb (Arg.var p_61.snd.fst) fun ld_10 =>
       Expr.call "full_has_bin" (as := [i64, i32, i32]) (bs := [.bool])
         (Arg.var h, Arg.var f1, Arg.var ld_10, ()) fun p =>
       Expr.jnz (Arg.var p.fst)
         (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                      args := (Arg.imm 128, Arg.var p_61.fst, ()) } fun p =>
          Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                      args := (Arg.var p.fst, ()) } fun p =>
          Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                      args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
          Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var scr_ptr, Arg.var p.fst, ()) } fun p =>
          ldSb (Arg.var p_61.snd.fst) fun ld =>
          Expr.store (Arg.var ld) (Arg.var p.fst)
            (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                         args := (Arg.var p_61.fst, Arg.imm 1, ()) } fun p =>
             Expr.jump Js.fst (Arg.var p.fst, ())))
         (Expr.jump Js.fst (Arg.var p_61.fst, ())))
      (after p_61.fst)) Blocks.nil)
  fun Js_1 => Expr.jump Js_1.fst (Arg.imm 0, Arg.imm 0, ())

private theorem bva_loop3a_wp (Γ : Env)
    (hHasBin : ∀ args m Q X, fullHasBinSpec args m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] args m Q X)
    (c : FullCfg) {F0 : CNF Nat} {F_cur : List (List Nat)} {s st3 : FullState}
    {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost} {ml3 : Mem 64}
    {qn f0 f1 : Val i32} {dn : Nat} {scr1 scr2 : List (BitVec 32)}
    (after : Val i32 → Expr Val Cont [.bool])
    (hscr_ge : 512 ≤ c.scratch_cap) (hqn_le : qn.toNat ≤ 32) (hdn_le : dn ≤ 16)
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hag : AgreesExcept bvaScrMask s st3) (hsb3 : st3.scratch.scratch_buf.length = c.scratch_cap)
    (hk1 : ∀ i < qn.toNat, st3.scratch.scratch_buf[i]? = scr1[i]?)
    (hk2 : ∀ j < dn, st3.scratch.scratch_buf[64 + j]? = scr2[64 + j]?)
    (hscr1_ent : ∀ i < qn.toNat, let qi := (scr1[i]?.getD 0#32).toNat
      qi < 2 * s.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [f0.toNat, qi]))
    (hml3 : (FullMem c st3 ⋆ R) ml3)
    (hAfter : ∀ (mn : Val i32) (st3a : FullState) (ml3a : Mem 64),
      BvaLoop3aInv c F_cur s f0.toNat f1.toNat qn.toNat dn scr1 scr2 qn.toNat mn.toNat st3a →
      (FullMem c st3a ⋆ R) ml3a → wp Γ Q X (after mn) ml3a) :
    wp Γ Q X (bvaLoop3aExpr c.hdr c.pScratchBuf qn f1 after) ml3 := by
  have h1_32 : (1#32 : BitVec 32).toNat = 1 := rfl
  have h128_32 : (128 : BitVec 32).toNat = 128 := rfl
  unfold bvaLoop3aExpr; dsimp only
  refine wp_loop_inv (fun (mn, qi, ()) ml3a => ∃ st3a : FullState,
      BvaLoop3aInv c F_cur s f0.toNat f1.toNat qn.toNat dn scr1 scr2
        qi.toNat mn.toNat st3a ∧ (FullMem c st3a ⋆ R) ml3a)
    (fun (_, qi, _) _ => qn.toNat - qi.toNat)
    (fun J3a hJ3a => by bf_steps; exact hJ3a (0#32, 0#32, ()) ml3 ⟨st3, ⟨hag, hsb3, Nat.le_refl _,
      by rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega, hk1, hk2,
      fun _ h => by simp at h⟩, hml3⟩)
    (fun J3a (mn, qi, ()) ml3a ⟨st3a, hinv3a, hml3a⟩ ih3a => ?_)
  have hst3a_eq := bva_scr_reconstruct hinv3a.1; have hsb3a := hinv3a.2.1
  have hmn_le := hinv3a.2.2.1; have hqi_le := hinv3a.2.2.2.1
  have hk1_3a := hinv3a.2.2.2.2.1; have hk2_3a := hinv3a.2.2.2.2.2.1
  have hscr3a_ok := hinv3a.2.2.2.2.2.2
  bf_fast
  · have hqi_lt : qi.toNat < qn.toNat := hc
    have hqi_n : (BitVec.setWidth 64 qi).toNat = qi.toNat := bv64_zext32_toNat qi
    have hqi_sb : (BitVec.setWidth 64 qi).toNat < st3a.scratch.scratch_buf.length := by
      rw [hqi_n, hsb3a]; omega
    have hqi1_n : (qi + 1#32).toNat = qi.toNat + 1 := bv32_add_toNat (by omega)
    have hmn1_n : (mn + 1#32).toNat = mn.toNat + 1 := bv32_add_toNat (by omega)
    have h128mn_n : ((128 : BitVec 32) + mn).toNat = 128 + mn.toNat := bv32_add_toNat (by omega)
    have hidx128 : (BitVec.setWidth 64 ((128 : BitVec 32) + mn)).toNat = 128 + mn.toNat := by
      rw [bv64_zext32_toNat, h128mn_n]
    have h128mn_sb : (BitVec.setWidth 64 ((128 : BitVec 32) + mn)).toNat <
        st3a.scratch.scratch_buf.length := by rw [hidx128, hsb3a]; omega
    have hqqi_info :
        (st3a.scratch.scratch_buf[(BitVec.setWidth 64 qi).toNat]'hqi_sb).toNat <
          2 * s.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [f0.toNat,
          (st3a.scratch.scratch_buf[(BitVec.setWidth 64 qi).toNat]'hqi_sb).toNat]) := by
      have h1 := hscr1_ent qi.toNat hqi_lt
      rw [← hk1_3a qi.toNat hqi_lt, ← hqi_n, List.getElem?_eq_getElem hqi_sb,
        Option.getD_some] at h1; exact h1
    bf_steps; c0_call hHasBin
    refine ⟨c, F0, F_cur, st3a, R, rfl, bva_scr_lengths hinv3a.1 hlen hsb3a,
      by rw [hst3a_eq]; exact hw, hml3a, fun rb hrb => ?_⟩
    bf_steps
    · have hrb_t := hrb hc
      refine ih3a (mn + 1#32, qi + 1#32, ()) m (by dsimp only; rw [hqi1_n]; omega) ⟨_, ?_, hm⟩
      rw [hqi1_n, hmn1_n, hidx128]
      exact bva_loop3a_push hinv3a hscr_ge hqn_le hdn_le hqi_lt hqqi_info.1 hqqi_info.2
        hrb_t.2.2.2.2
    · exact ih3a (mn, qi + 1#32, ()) ml3a (by dsimp only; rw [hqi1_n]; omega)
        ⟨st3a, ⟨hinv3a.1, hsb3a, by rw [hqi1_n]; omega, by rw [hqi1_n]; omega,
          hk1_3a, hk2_3a, hscr3a_ok⟩, hml3a⟩
  · have hqi_eq : qi.toNat = qn.toNat := by have : ¬ qi.toNat < qn.toNat := hc; omega
    exact hAfter mn st3a ml3a ⟨hinv3a.1, hsb3a, by omega, by omega, hk1_3a, hk2_3a, hscr3a_ok⟩
      hml3a

private theorem bva_loop3b_wp (Γ : Env)
    (hHasBin : ∀ args m Q X, fullHasBinSpec args m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] args m Q X)
    (hInitFresh : ∀ args m Q X, fullInitFreshVarSpec args m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] args m Q X)
    (hAddBin : ∀ args m Q X, fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X)
    (hDelBin : ∀ args m Q X, fullDeleteBinarySpec args m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] args m Q X)
    (c : FullCfg) {F0 : CNF Nat} {F_cur : List (List Nat)} {s st_init4 : FullState}
    {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost} {m_init4 : Mem 64}
    {dn mn bi1 : Val i32} {qn : Nat} {scr1 scr2 scr3 : List (BitVec 32)} {Js_bi : Cont []}
    (hcv_lt : s.core.cur_vars < c.max_vars) (hmx : c.max_vars < 2 * 2 ^ 28)
    (hscr_ge : 512 ≤ c.scratch_cap) (hqn_le : qn ≤ 32) (hdn_le : dn.toNat ≤ 16)
    (_hmn_ge2 : 2 ≤ mn.toNat) (hmn_le : mn.toNat ≤ 32)
    (hinv : FullDenseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core)
    (hscr2_lt : ∀ j < dn.toNat, (scr2[64 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hscr3_lt : ∀ k < mn.toNat, (scr3[128 + k]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hinit4 : BvaLoop3bInv c F_cur s qn dn.toNat mn.toNat scr1 scr2 scr3 bi1.toNat 2 st_init4)
    (hm_init4 : (FullMem c st_init4 ⋆ R) m_init4)
    (hJs_bi : ∀ st4x m4x, AgreesExcept bvaScrMask s st4x →
      st4x.scratch.scratch_buf.length = c.scratch_cap →
      (∀ i < qn, st4x.scratch.scratch_buf[i]? = scr1[i]?) →
      (∀ j < dn.toNat, st4x.scratch.scratch_buf[64 + j]? = scr2[64 + j]?) →
      (FullMem c st4x ⋆ R) m4x → Js_bi () m4x)
    (hQ : ∀ (r : Bool) (s' : FullState) (m' : Mem 64), FullDenseInv c F0 s' →
      s.core.cur_vars ≤ s'.core.cur_vars → s'.core.fuel = s.core.fuel →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (bvaLoop3bExpr c.hdr c.pScratchBuf dn mn bi1 Js_bi) m_init4 := by
  unfold bvaLoop3bExpr; dsimp only
  refine wp_loop_inv (fun (dm, dj, ()) ml4 => ∃ st4 : FullState,
      BvaLoop3bInv c F_cur s qn dn.toNat mn.toNat scr1 scr2 scr3
        dj.toNat dm.toNat st4 ∧ (FullMem c st4 ⋆ R) ml4)
    (fun (_, dj, _) _ => dn.toNat - dj.toNat)
    (fun J4 hJ4 => by
      bf_steps; exact hJ4 (2#32, bi1, ()) m_init4 ⟨st_init4, hinit4, hm_init4⟩)
    (fun J4 (dm, dj, ()) ml4 ⟨st4, hinv4, hml4⟩ ih4 => ?_)
  have hst4_eq := bva_scr_reconstruct hinv4.1; have hsb4 := hinv4.2.1
  have hdm_ge := hinv4.2.2.1; have hdm_le := hinv4.2.2.2.1
  have hdj_le := hinv4.2.2.2.2.1; have hk1_4 := hinv4.2.2.2.2.2.1
  have hk2_4 := hinv4.2.2.2.2.2.2.1; have hk3_4 := hinv4.2.2.2.2.2.2.2.1
  have hscr4_ok := hinv4.2.2.2.2.2.2.2.2
  refine wp_join_group (fun () ml4 => ∃ st4 : FullState,
      BvaLoop3bInv c F_cur s qn dn.toNat mn.toNat scr1 scr2 scr3
        dj.toNat dm.toNat st4 ∧ (FullMem c st4 ⋆ R) ml4)
    (fun _ () ml4 ⟨st4x, hinv4x, hml4x⟩ => ?_) (fun J4x hJ4x => ?_)
  · have hst4_eq := bva_scr_reconstruct hinv4x.1
    have hst4x_core : st4x.core = s.core := by rw [hst4_eq]
    have hsb4 := hinv4x.2.1; have hdm_ge := hinv4x.2.2.1; have hdm_le := hinv4x.2.2.2.1
    have hk1_4 := hinv4x.2.2.2.2.2.1; have hk2_4 := hinv4x.2.2.2.2.2.2.1
    bf_steps
    · try clear hc
      have hfv_n : (BitVec.setWidth 32 (BitVec.ofNat 64 s.core.cur_vars)).toNat =
          s.core.cur_vars := by
        rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hcv1_n : (BitVec.ofNat 64 s.core.cur_vars + 1#64).toNat = s.core.cur_vars + 1 := by
        rw [bv64_add_toNat (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                               show s.core.cur_vars + 1 < 2 ^ 64; omega),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; rfl
      c0_call hInitFresh
      refine ⟨c, _, R, rfl, bva_lengths_inc_cur_vars hinv4x.1 hinv.1.lengths hsb4 hcv_lt hcv1_n,
        by dsimp only; rw [hst4_eq]; dsimp only; rw [hcv1_n, hfv_n]; omega, by assumption,
        fun vals' mrk' flags' lvl' rsns' wvec' unass' sc_init m_init hlen_init hextp hsb_init
          hv0 hv1 hv_oth hmrk_fv hmrk_oth _ hlvl_oth _ hrsn_oth hwvec_0 hwvec_oth hm_init => ?_⟩
      dsimp only at hsb_init hv0 hv1 hv_oth hmrk_fv hmrk_oth hlvl_oth hrsn_oth hwvec_0 hwvec_oth
      have hll_init : sc_init.last_learned = st4x.scratch.last_learned := by simpa using hextp.1
      have hext_init : sc_init.extend_len = st4x.scratch.extend_len := by simpa using hextp.2
      simp only [hst4x_core, hfv_n] at hv0 hv1 hv_oth hmrk_fv hmrk_oth
      simp only [hst4x_core, hfv_n] at hlvl_oth hrsn_oth hwvec_0 hwvec_oth
      exact bva_commit_after_init Γ hAddBin hDelBin c hdm_le hmn_le hcv_lt hmx hscr_ge hinv hw
        hinv4x hscr3_lt hlen_init
        (by dsimp only; rw [hst4_eq]; dsimp only; rw [hcv1_n])
        hv0 hv1 hv_oth hmrk_fv hmrk_oth hlvl_oth hrsn_oth hwvec_0 hwvec_oth
        hll_init hext_init hsb_init hm_init hQ
    all_goals exact hJs_bi st4x ml4 hinv4x.1 hsb4 hk1_4 hk2_4 hml4x
  · bf_steps
    · have hdm_lt : dm.toNat < 8 := hc; have hdj_lt : dj.toNat < dn.toNat := by assumption
      have h64dj_n : ((64 : BitVec 32) + dj).toNat = 64 + dj.toNat :=
        bv32_add_toNat (show 64 + dj.toNat < 2 ^ 32 by omega)
      have h64dj_idx : (BitVec.setWidth 64 ((64 : BitVec 32) + dj)).toNat = 64 + dj.toNat := by
        rw [bv64_zext32_toNat, h64dj_n]
      have h64dj_sb : (BitVec.setWidth 64 ((64 : BitVec 32) + dj)).toNat <
          st4.scratch.scratch_buf.length := by rw [h64dj_idx, hsb4]; omega
      have hdj1_n : (dj + 1#32).toNat = dj.toNat + 1 :=
        bv32_add_toNat (show dj.toNat + 1 < 2 ^ 32 by omega)
      have hdm1_n : (dm + 1#32).toNat = dm.toNat + 1 :=
        bv32_add_toNat (show dm.toNat + 1 < 2 ^ 32 by omega)
      have h192dm_n : ((192 : BitVec 32) + dm).toNat = 192 + dm.toNat :=
        bv32_add_toNat (show 192 + dm.toNat < 2 ^ 32 by omega)
      have hidx192 : (BitVec.setWidth 64 ((192 : BitVec 32) + dm)).toNat = 192 + dm.toNat := by
        rw [bv64_zext32_toNat, h192dm_n]
      have h192dm_sb : (BitVec.setWidth 64 ((192 : BitVec 32) + dm)).toNat <
          st4.scratch.scratch_buf.length := by rw [hidx192, hsb4]; omega
      bf_steps
      have hfj_lt : (st4.scratch.scratch_buf[(BitVec.setWidth 64
          ((64 : BitVec 32) + dj)).toNat]'h64dj_sb).toNat < 2 * s.core.cur_vars := by
        have h1 := hscr2_lt dj.toNat hdj_lt
        rw [← hk2_4 dj.toNat hdj_lt, ← h64dj_idx, List.getElem?_eq_getElem h64dj_sb,
          Option.getD_some] at h1; exact h1
      generalize hfj_v : st4.scratch.scratch_buf[(BitVec.setWidth 64
          ((64 : BitVec 32) + dj)).toNat]'h64dj_sb = fj at *
      exact bva_loop3b_inner_wp Γ hHasBin c hscr_ge hmn_le hinv.1.lengths hw hinv4.1
        hsb4 hk3_4 hml4
        (fun _ ml4i hmi => by
          apply hJ; bf_steps; exact ih4 (dm, dj + 1#32, ()) ml4i (by dsimp only; rw [hdj1_n]; omega)
            ⟨st4, by rw [hdj1_n]; exact ⟨hinv4.1, hsb4, hdm_ge, hdm_le, by omega,
              hk1_4, hk2_4, hk3_4, hscr4_ok⟩, hmi⟩)
        (fun _ ml4i _ ham_ok hmi => by
          apply hJ; bf_fast
          refine ih4 (dm + 1#32, dj + 1#32, ()) m (by dsimp only; rw [hdj1_n]; omega) ⟨_, ?_, hm⟩
          rw [hdm1_n, hdj1_n, hidx192]
          exact bva_loop3b_push hinv4 hscr_ge hqn_le hdn_le hmn_le hdj_lt hdm_lt hfj_lt ham_ok)
    all_goals exact hJ4x () ml4 ⟨st4, hinv4, hml4⟩

theorem full_bva_try_lit_wp (Γ : Env)
    (hHasBin : ∀ args m Q X, fullHasBinSpec args m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] args m Q X)
    (hInitFresh : ∀ args m Q X, fullInitFreshVarSpec args m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] args m Q X)
    (hAddBin : ∀ args m Q X, fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X)
    (hDelBin : ∀ args m Q X, fullDeleteBinarySpec args m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, fullBvaTryLitSpec args m Q X →
      Func.wp Γ full_bva_try_lit_body args m Q X := by
  rintro ⟨h, f0, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hf0_lt, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap hscr_b
  have hlen := hinv.1.lengths.core_ok; have hcv_le := hlen.cur_vars_le
  have hvals_len := hlen.vals_len; have hwv_len := hlen.wvec_len
  have hws_len := hlen.wstk_len_arr; have hwlen_le := hlen.wlen_le
  have hsb_len := hinv.1.lengths.scratch_ok.scratch_buf_len
  obtain ⟨F_cur, hw⟩ := hinv.1.witness; have hdm := hinv.2.2.2.2.2
  have hdw : DenseWatchesInv F_cur s.core := by
    have h1 := hw.watches; unfold ModeWatchesInv at h1; rwa [ite_eq_right hdm] at h1
  unfold Func.wp full_bva_try_lit_body; dsimp only; bf_fast
  all_goals try exact hQ false s m hinv (Nat.le_refl _) rfl hm
  · have hcv_lt : s.core.cur_vars < c.max_vars := by c0_bound
    have hscr_ge : 512 ≤ c.scratch_cap := by c0_bound
    have hf0_64 := bv64_zext32_toNat f0
    have hf0_off_idx : (BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat = 2 * f0.toNat := by
      rw [bv64_shl1_toNat (by rw [hf0_64]; omega), hf0_64]
    have hf0_sz_idx : ((BitVec.setWidth 64 f0 <<< (1 : Nat)) + 1#64).toNat = 2 * f0.toNat + 1 :=
      by rw [bv64_add_toNat (by rw [hf0_off_idx]; c0_bound), hf0_off_idx]; rfl
    have hoff_eq : (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 f0 <<<
        (1 : Nat)).toNat]'(by omega))).toNat = fullWatchOffCore s.core f0.toNat := by
      unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
        BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by
          have := (s.core.wvec[2 * f0.toNat]'(by omega)).isLt; omega)]; congr 2
    have hsz_eq : (BitVec.setWidth 64 (s.core.wvec[((BitVec.setWidth 64 f0 <<< (1 : Nat)) +
        1#64).toNat]'(by omega))).toNat = fullWatchSizeCore s.core f0.toNat := by
      unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
        BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by
          have := (s.core.wvec[2 * f0.toNat + 1]'(by omega)).isLt; omega)]; congr 2
    have hbd_f0 := hdw.layout.bounds f0.toNat hf0_lt; have hslice_f0 := hdw.slices f0.toNat hf0_lt
    generalize hoff_v : BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 f0 <<<
        (1 : Nat)).toNat]'(by omega)) = off at *
    generalize hsz_v : BitVec.setWidth 64 (s.core.wvec[((BitVec.setWidth 64 f0 <<< (1 : Nat)) +
        1#64).toNat]'(by omega)) = sz at *
    have hend_n : (off + sz).toNat = off.toNat + sz.toNat := bv64_add_toNat (by omega)
    refine wp_loop_inv (fun (qn, p, ()) ml1 => ∃ st1 : FullState,
        BvaLoop1Inv c F_cur s f0.toNat off.toNat sz.toNat p.toNat qn.toNat st1 ∧
        (FullMem c st1 ⋆ R) ml1)
      (fun (_, p, _) _ => off.toNat + sz.toNat - p.toNat)
      (fun J1 hJ1 => by bf_steps; refine hJ1 (0#32, off, ()) m ⟨s, ⟨.refl _ _, hsb_len,
        Nat.le_refl _, by omega, by decide, by rw [show off.toNat + sz.toNat - off.toNat =
          sz.toNat by omega, hoff_eq, hsz_eq]; exact hslice_f0, fun _ h => by simp at h⟩, hm⟩)
      (fun J1 (qn, p, ()) ml1 ⟨st1, hinv1, hml1⟩ ih1 => ?_)
    have hst1_eq := bva_scr_reconstruct hinv1.1; have hsb1 := hinv1.2.1
    have hp1_ge := hinv1.2.2.1; have hp1_le := hinv1.2.2.2.1; have hqn_le := hinv1.2.2.2.2.1
    have hrem1 := hinv1.2.2.2.2.2.1; have hscr1_ok := hinv1.2.2.2.2.2.2
    have hst1_ws : st1.core.wstk = s.core.wstk := by rw [hst1_eq]
    have hws1_len : st1.core.wstk.length = c.wcap := by rw [hst1_ws]; exact hws_len
    have hst1_vals : st1.core.vals = s.core.vals := by rw [hst1_eq]
    refine wp_join_group (fun () ml1 => ∃ st1 : FullState, AgreesExcept bvaScrMask s st1 ∧
        st1.scratch.scratch_buf.length = c.scratch_cap ∧ qn.toNat ≤ 32 ∧
        (∀ i < qn.toNat, let qi := (st1.scratch.scratch_buf[i]?.getD 0#32).toNat
          qi < 2 * s.core.cur_vars ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause [f0.toNat, qi])) ∧
        (FullMem c st1 ⋆ R) ml1)
      (fun _ () ml1 ⟨st1, hag1, hsb1, hqn_le, hscr1_ok, hml1⟩ => ?_) (fun J1x hJ1x => ?_)
    · have hst1_eq := bva_scr_reconstruct hag1
      have hst1_wv : st1.core.wvec = s.core.wvec := by rw [hst1_eq]
      have hwv1_len : st1.core.wvec.length = 4 * c.max_vars := by rw [hst1_wv]; exact hwv_len
      bf_fast
      · exact hQ false st1 ml1 (bva_scr_dense hag1 hinv hsb1)
          (by rw [hst1_eq]; exact Nat.le_refl _) (by rw [hst1_eq]) hml1
      · have hqn_ge2 : 2 ≤ qn.toNat := by have : ¬ qn.toNat < 2 := hc; omega
        have h0n : (0#64 : BitVec 64).toNat = 0 := rfl
        have hq0_sb : (0#64 : BitVec 64).toNat < st1.scratch.scratch_buf.length := by
          rw [h0n]; omega
        generalize hq0_v : st1.scratch.scratch_buf[(0#64).toNat]'hq0_sb = q0 at *
        have hq0_lt : q0.toNat < 2 * s.core.cur_vars := by
          simpa only [← hq0_v, h0n, List.getElem?_eq_getElem
            (show 0 < st1.scratch.scratch_buf.length by omega), Option.getD_some] using
            (hscr1_ok 0 (by omega)).1
        have hq0_64 : (BitVec.setWidth 64 q0).toNat = q0.toNat := bv64_zext32_toNat q0
        have hq0_off_idx : (BitVec.setWidth 64 q0 <<< (1 : Nat)).toNat = 2 * q0.toNat := by
          rw [bv64_shl1_toNat (by rw [hq0_64]; omega), hq0_64]
        have hq0_sz_idx : ((BitVec.setWidth 64 q0 <<< (1 : Nat)) + 1#64).toNat = 2 * q0.toNat + 1 :=
          by rw [bv64_add_toNat (by rw [hq0_off_idx]; c0_bound), hq0_off_idx]; rfl
        have hq0_off_lt : (BitVec.setWidth 64 q0 <<< (1 : Nat)).toNat < st1.core.wvec.length := by
          rw [hq0_off_idx, hwv1_len]; omega
        have hq0_sz_lt : ((BitVec.setWidth 64 q0 <<< (1 : Nat)) + 1#64).toNat <
            st1.core.wvec.length := by rw [hq0_sz_idx, hwv1_len]; omega
        have h64_lt_sb : (64#64 : BitVec 64).toNat < st1.scratch.scratch_buf.length := by
          rw [hsb1]; show 64 < c.scratch_cap; omega
        have hqoff_eq : (BitVec.setWidth 64 (st1.core.wvec[(BitVec.setWidth 64 q0 <<<
            (1 : Nat)).toNat]'hq0_off_lt)).toNat = fullWatchOffCore s.core q0.toNat := by
          unfold fullWatchOffCore; rw [show st1.core.wvec[(BitVec.setWidth 64 q0 <<<
            (1 : Nat)).toNat]'hq0_off_lt = s.core.wvec[2 * q0.toNat]'(by omega) from by
            simp [hst1_wv, hq0_off_idx], List.getElem?_eq_getElem (by omega), Option.getD_some,
            BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by
              have := (s.core.wvec[2 * q0.toNat]'(by omega)).isLt; omega)]
        have hqsz_eq : (BitVec.setWidth 64 (st1.core.wvec[((BitVec.setWidth 64 q0 <<< (1 : Nat)) +
            1#64).toNat]'hq0_sz_lt)).toNat = fullWatchSizeCore s.core q0.toNat := by
          unfold fullWatchSizeCore; rw [show st1.core.wvec[((BitVec.setWidth 64 q0 <<< (1 : Nat)) +
            1#64).toNat]'hq0_sz_lt = s.core.wvec[2 * q0.toNat + 1]'(by omega) from by
            simp [hst1_wv, hq0_sz_idx], List.getElem?_eq_getElem (by omega), Option.getD_some,
            BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by
              have := (s.core.wvec[2 * q0.toNat + 1]'(by omega)).isLt; omega)]
        have hbd_q0 := hdw.layout.bounds q0.toNat hq0_lt
        have hslice_q0 := hdw.slices q0.toNat hq0_lt
        let scr1 := st1.scratch.scratch_buf; have hscr1_ent := hscr1_ok
        bf_fast; generalize hqoff_v : BitVec.setWidth 64 (st1.core.wvec[(BitVec.setWidth 64 q0 <<<
          (1 : Nat)).toNat]'(by omega)) = qoff at *
        generalize hqsz_v : BitVec.setWidth 64 (st1.core.wvec[((BitVec.setWidth 64 q0 <<<
          (1 : Nat)) + 1#64).toNat]'(by omega)) = qsz at *
        have hqend_n : (qoff + qsz).toNat = qoff.toNat + qsz.toNat := bv64_add_toNat (by omega)
        refine wp_loop_inv (fun (p2, dn, ()) ml2 => ∃ st2 : FullState,
            BvaLoop2Inv c F_cur s q0.toNat qoff.toNat qsz.toNat qn.toNat scr1
              p2.toNat dn.toNat st2 ∧ (FullMem c st2 ⋆ R) ml2)
          (fun (p2, _, _) _ => qoff.toNat + qsz.toNat - p2.toNat)
          (fun J2 hJ2 => by
            bf_steps; refine hJ2 (qoff, 1#32, ()) _ ⟨_, ⟨by exact hag1.trans rfl, by simp [hsb1],
              Nat.le_refl _, by omega, by decide, by decide,
              by rw [show qoff.toNat + qsz.toNat - qoff.toNat = qsz.toNat by omega,
                     hqoff_eq, hqsz_eq]; exact hslice_q0,
              fun i hi => by dsimp only; rw [show (64#64 : BitVec 64).toNat = 64 from rfl]
                             exact List.getElem?_set_ne (by omega),
              fun j hj => by
                have hj0 : j = 0 := by have : (1#32 : BitVec 32).toNat = 1 := rfl; omega
                subst hj0; dsimp only; rw [Nat.add_zero, show (64#64 : BitVec 64).toNat = 64 from
                  rfl, List.getElem?_set_self (by omega), Option.getD_some]; exact hf0_lt⟩, hm⟩)
          (fun J2 (p2, dn, ()) ml2 ⟨st2, hinv2, hml2⟩ ih2 => ?_)
        have hst2_eq := bva_scr_reconstruct hinv2.1; have hsb2 := hinv2.2.1
        have hp2_ge := hinv2.2.2.1; have hp2_le := hinv2.2.2.2.1; have hdn_ge := hinv2.2.2.2.2.1
        have hdn_le := hinv2.2.2.2.2.2.1; have hrem2 := hinv2.2.2.2.2.2.2.1
        have hkeep1_2 := hinv2.2.2.2.2.2.2.2.1; have hscr2_ok := hinv2.2.2.2.2.2.2.2.2
        have hst2_ws : st2.core.wstk = s.core.wstk := by rw [hst2_eq]
        have hws2_len : st2.core.wstk.length = c.wcap := by rw [hst2_ws]; exact hws_len
        have hst2_vals : st2.core.vals = s.core.vals := by rw [hst2_eq]
        refine wp_join_group (fun () ml2 => ∃ st2 : FullState, AgreesExcept bvaScrMask s st2 ∧
            st2.scratch.scratch_buf.length = c.scratch_cap ∧ 1 ≤ dn.toNat ∧ dn.toNat ≤ 16 ∧
            (∀ i < qn.toNat, st2.scratch.scratch_buf[i]? = scr1[i]?) ∧
            (∀ j < dn.toNat,
              (st2.scratch.scratch_buf[64 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
            (FullMem c st2 ⋆ R) ml2)
          (fun _ () ml2 ⟨st2x, hag2x, hsb2x, hdn_gex, hdn_lex, hk1_2x, hscr2_okx, hml2x⟩ => ?_)
          (fun J2x hJ2x => ?_)
        · -- Post-Loop-2 continuation: Loop 3 (`bi = 1..dn-1`)
          let scr2 := st2x.scratch.scratch_buf
          have hscr2_lt : ∀ j < dn.toNat, (scr2[64 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars :=
            hscr2_okx
          clear hst2_eq hsb2 hp2_ge hp2_le hdn_ge hdn_le hrem2 hkeep1_2 hscr2_ok hst2_ws hws2_len
            hst2_vals hqend_n hqoff_eq hqsz_eq hbd_q0 hslice_q0 hqsz_v hqoff_v hq0_off_lt hq0_sz_lt
            hq0_off_idx hq0_sz_idx h64_lt_sb hq0_64 hq0_lt hst1_eq hst1_wv hwv1_len hoff_v hsz_v
            hf0_off_idx hf0_sz_idx hoff_eq hsz_eq hbd_f0 hslice_f0 hend_n hst1_ws hws1_len
            hst1_vals hrem1 hscr1_ok hp1_ge hp1_le hinv1 hinv2 ih1 ih2 hml2
          bf_steps
          refine wp_loop_inv (fun (bi, ()) ml3 => ∃ st3 : FullState,
              AgreesExcept bvaScrMask s st3 ∧ st3.scratch.scratch_buf.length = c.scratch_cap ∧
              1 ≤ bi.toNat ∧ bi.toNat ≤ dn.toNat ∧
              (∀ i < qn.toNat, st3.scratch.scratch_buf[i]? = scr1[i]?) ∧
              (∀ j < dn.toNat, st3.scratch.scratch_buf[64 + j]? = scr2[64 + j]?) ∧
              (FullMem c st3 ⋆ R) ml3)
            (fun (bi, ()) _ => dn.toNat - bi.toNat)
            (fun J3 hJ3 => by
              bf_steps; exact hJ3 (1#32, ()) ml2 ⟨st2x, hag2x, hsb2x, by decide,
                by rw [show (1#32 : BitVec 32).toNat = 1 from rfl]; omega,
                hk1_2x, fun _ _ => rfl, hml2x⟩)
            (fun J3 (bi, ()) ml3 ⟨st3, hag3, hsb3, hbi_ge, hbi_le, hk1_3, hk2_3, hml3⟩ ih3 => ?_)
          have hst3_eq := bva_scr_reconstruct hag3; bf_steps
          · -- Loop 3 body (`bi < dn`)
            have hbi_lt : bi.toNat < dn.toNat := hc
            have h64bi_n : ((64 : BitVec 32) + bi).toNat = 64 + bi.toNat :=
              bv32_add_toNat (show 64 + bi.toNat < 2 ^ 32 by omega)
            have h64bi_lt : (BitVec.setWidth 64 ((64 : BitVec 32) + bi)).toNat <
                st3.scratch.scratch_buf.length := by
              rw [bv64_zext32_toNat, h64bi_n, hsb3]; omega
            bf_steps
            have hf1_lt : (st3.scratch.scratch_buf[(BitVec.setWidth 64
                ((64 : BitVec 32) + bi)).toNat]'h64bi_lt).toNat < 2 * s.core.cur_vars := by
              have hidx : (BitVec.setWidth 64 ((64 : BitVec 32) + bi)).toNat = 64 + bi.toNat := by
                rw [bv64_zext32_toNat, h64bi_n]
              have h1 := hscr2_lt bi.toNat hbi_lt
              rw [← hk2_3 bi.toNat hbi_lt, ← hidx, List.getElem?_eq_getElem h64bi_lt,
                Option.getD_some] at h1; exact h1
            generalize hf1_v : st3.scratch.scratch_buf[(BitVec.setWidth 64
                ((64 : BitVec 32) + bi)).toNat]'h64bi_lt = f1 at *
            -- Loop 3a (`qi < qn`): collect `scr[qi]` where `full_has_bin(h, f1, scr[qi])`
            suffices h3a : wp Γ Q X (bvaLoop3aExpr c.hdr c.pScratchBuf qn f1
                (fun mn => bvaPost3aExpr c.hdr c.pScratchBuf dn bi f0 f1 mn J3)) ml3 by
              unfold bvaLoop3aExpr bvaPost3aExpr at h3a; dsimp only at h3a; exact h3a
            refine bva_loop3a_wp Γ hHasBin c _ hscr_ge hqn_le hdn_lex hinv.1.lengths hw hag3
              hsb3 hk1_3 hk2_3 hscr1_ent hml3 fun mn st3a ml3a hinv3a hml3a => ?_
            have hbi1_n : (bi + 1#32).toNat = bi.toNat + 1 :=
              bv32_add_toNat (show bi.toNat + 1 < 2 ^ 32 by omega)
            have hmn_le := hinv3a.2.2.1; let scr3 := st3a.scratch.scratch_buf
            have hscr3_info := hinv3a.2.2.2.2.2.2
            unfold bvaPost3aExpr; dsimp only; bf_fast
            · have hmn_ge2 : 2 ≤ mn.toNat := by assumption
              have hmn_32 : mn.toNat ≤ 32 := by omega
              have hsb3a : st3a.scratch.scratch_buf.length = c.scratch_cap := hinv3a.2.1
              have h192_sb : (192#64 : BitVec 64).toNat < st3a.scratch.scratch_buf.length := by
                rw [hsb3a]; show 192 < c.scratch_cap; omega
              bf_fast
              refine bva_loop3b_wp Γ hHasBin hInitFresh hAddBin hDelBin c hcv_lt hmx hscr_ge
                hqn_le hdn_lex hmn_ge2 hmn_32 hinv hw hscr2_lt (fun k hk => (hscr3_info k hk).1)
                ?_ hm (fun st4x m4x hag4x hsb4x hk1_4x hk2_4x hm4x => by
                  apply hJ; bf_steps; exact ih3 (bi + 1#32, ()) m4x
                    (by dsimp only; rw [hbi1_n]; omega)
                    ⟨st4x, hag4x, hsb4x, by rw [hbi1_n]; omega, by rw [hbi1_n]; omega,
                     hk1_4x, hk2_4x, hm4x⟩) hQ
              try rw [show (192#64 : BitVec 64).toNat = 192 from rfl]
              try rw [show (193#64 : BitVec 64).toNat = 193 from rfl]
              rw [show (bi + 1 : BitVec 32) = bi + 1#32 from rfl, hbi1_n]
              exact bva_loop3b_init hinv3a hscr_ge hqn_le hdn_lex hbi_lt hf0_lt hf1_lt
            · exact ih3 (bi + 1#32, ()) ml3a (by dsimp only; rw [hbi1_n]; omega)
                ⟨st3a, hinv3a.1, hinv3a.2.1, by rw [hbi1_n]; omega, by rw [hbi1_n]; omega,
                 hinv3a.2.2.2.2.1, hinv3a.2.2.2.2.2.1, hml3a⟩
          · exact hQ false st3 ml3 (bva_scr_dense hag3 hinv hsb3)
              (by rw [hst3_eq]; exact Nat.le_refl _) (by rw [hst3_eq]) hml3
        · -- Loop 2 step (`p2 < qend && dn < 16u`)
          have h1_64 : (1#64 : BitVec 64).toNat = 1 := rfl
          have helem (h1 : p2.toNat < st2.core.wstk.length) (h2 : p2.toNat < s.core.wstk.length) :
              st2.core.wstk[p2.toNat]'h1 = s.core.wstk[p2.toNat]'h2 := Option.some.inj
            (by rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hst2_ws])
          bf_fast
          · have hp_lt : p2.toNat < qoff.toNat + qsz.toNat :=
              bv64_lt_add_of_hc (by assumption) (by omega)
            have hdn_lt : dn.toNat < 16 := by assumption
            have hp_ws : p2.toNat < s.core.wstk.length := by omega
            have hflag_c : (st2.core.wstk[p2.toNat]'(by rw [hst2_ws]; exact hp_ws) &&&
                0x80000000#32) ≠ 0#32 := by assumption
            have ⟨hcand_lt, _, hrem_next⟩ := bva_slice_bin_info hrem2 (by omega) hp_ws
              (by rw [← helem _ hp_ws]; exact hflag_c)
            have hcand_vals : (st2.core.wstk[p2.toNat]'(by rw [hst2_ws]; exact hp_ws) &&&
                0x7FFFFFFF#32).toNat < st2.core.vals.length := by
              rw [hst2_vals, hvals_len, helem _ hp_ws]; exact Nat.lt_of_lt_of_le hcand_lt (by omega)
            have hp1_n : (p2 + 1#64).toNat = p2.toNat + 1 := bv64_add_toNat (by omega)
            have hdn1_n : (dn + 1#32).toNat = dn.toNat + 1 :=
              bv32_add_toNat (show dn.toNat + 1 < 2 ^ 32 by omega)
            have h64dn_n : ((64 : BitVec 32) + dn).toNat = 64 + dn.toNat :=
              bv32_add_toNat (show 64 + dn.toNat < 2 ^ 32 by omega)
            have hidx64 : (BitVec.setWidth 64 ((64 : BitVec 32) + dn)).toNat = 64 + dn.toNat := by
              rw [bv64_zext32_toNat, h64dn_n]
            have h64dn_sb : (BitVec.setWidth 64 ((64 : BitVec 32) + dn)).toNat <
                st2.scratch.scratch_buf.length := by rw [hidx64, hsb2]; omega
            bf_steps
            · refine ih2 (p2 + 1#64, dn + 1#32, ()) m (by dsimp only; rw [hp1_n]; omega)
                ⟨_, ?_, hm⟩
              rw [hp1_n, hdn1_n, hidx64]
              exact bva_loop2_push hinv2 hscr_ge hqn_le hp_lt hdn_lt
                (helem _ hp_ws ▸ hcand_lt) hrem_next
            · exact ih2 (p2 + 1#64, dn, ()) ml2 (by dsimp only; rw [hp1_n]; omega)
                ⟨st2, by rw [hp1_n]; exact bva_loop2_skip hinv2 hp_lt hrem_next, hml2⟩
          iterate 2 (
            · have hp_lt := bv64_lt_add_of_hc (by assumption) (by omega)
              have ⟨_, _, hn⟩ := bva_slice_bin_info hrem2 (by omega) (by omega)
                (by rw [← helem _ (by omega)]; assumption)
              have hp1 : (p2 + 1#64).toNat = p2.toNat + 1 := bv64_add_toNat (by omega)
              exact ih2 (p2 + 1#64, dn, ()) ml2 (by dsimp only; rw [hp1]; omega)
                ⟨st2, by rw [hp1]; exact bva_loop2_skip hinv2 hp_lt hn, hml2⟩)
          · have hp_lt := bv64_lt_add_of_hc (by assumption) (by omega)
            have ⟨h2le, hn⟩ := bva_slice_occ_info hrem2 (by omega) (by omega)
              (by rw [← helem _ (by omega)]; assumption)
            have hp1_n : (p2 + 1#64).toNat = p2.toNat + 1 := bv64_add_toNat (by omega)
            have hp2_n : (p2 + 1#64 + 1#64).toNat = p2.toNat + 2 := by
              rw [bv64_add_toNat (by rw [hp1_n]; omega), hp1_n, h1_64]
            exact ih2 (p2 + 1#64 + 1#64, dn, ()) ml2 (by dsimp only; rw [hp2_n]; omega)
              ⟨st2, by rw [hp2_n]; exact bva_loop2_occ hinv2 hp_lt h2le hn, hml2⟩
          · exfalso; have hp_lt := bv64_lt_add_of_hc (by assumption) (by omega)
            have ⟨h2le, _⟩ := bva_slice_occ_info hrem2 (by omega) (by omega)
              (by rw [← helem _ (by omega)]; assumption)
            have hpc : ¬ (p2.toNat + 1) % 2 ^ 64 < (qoff.toNat + qsz.toNat) % 2 ^ 64 := by
              simpa only [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl] using hc
            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hpc; omega
          all_goals exact hJ2x () ml2 ⟨st2, hinv2.1, hsb2, hdn_ge, hdn_le, hkeep1_2, hscr2_ok, hml2⟩
    · have h1_64 : (1#64 : BitVec 64).toNat = 1 := rfl
      have h1_32 : (1#32 : BitVec 32).toNat = 1 := rfl
      have helem (h1 : p.toNat < st1.core.wstk.length) (h2 : p.toNat < s.core.wstk.length) :
          st1.core.wstk[p.toNat]'h1 = s.core.wstk[p.toNat]'h2 :=
        Option.some.inj (by rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hst1_ws])
      bf_fast
      · have hp_lt := bv64_lt_add_of_hc (by assumption) (by omega)
        have hqn_lt : qn.toNat < 32 := by assumption
        have hp_ws : p.toNat < s.core.wstk.length := by omega
        have ⟨hot_lt, hent_ot, hrem_next⟩ := bva_slice_bin_info hrem1 (by omega) hp_ws
          (by rw [← helem _ hp_ws]; assumption)
        have hot_vals : (st1.core.wstk[p.toNat]'(by rw [hst1_ws]; exact hp_ws) &&&
            0x7FFFFFFF#32).toNat < st1.core.vals.length := by
          rw [hst1_vals, hvals_len, helem _ hp_ws]; exact Nat.lt_of_lt_of_le hot_lt (by omega)
        have hp1_n : (p + 1#64).toNat = p.toNat + 1 := bv64_add_toNat (by omega)
        have hqn1_n : (qn + 1#32).toNat = qn.toNat + 1 := bv32_add_toNat (by omega)
        have hqn64 := bv64_zext32_toNat qn
        have hqn_sb : (BitVec.setWidth 64 qn).toNat < st1.scratch.scratch_buf.length := by
          rw [hqn64, hsb1]; omega
        bf_steps
        · refine ih1 (qn + 1#32, p + 1#64, ()) m (by dsimp only; rw [hp1_n]; omega) ⟨_, ?_, hm⟩
          rw [hp1_n, hqn1_n, hqn64]; exact bva_loop1_push hinv1 hscr_ge hp_lt hqn_lt
            (helem _ hp_ws ▸ hot_lt) (helem _ hp_ws ▸ hent_ot) hrem_next
        · exact ih1 (qn, p + 1#64, ()) ml1 (by dsimp only; rw [hp1_n]; omega)
            ⟨st1, by rw [hp1_n]; exact bva_loop1_skip hinv1 hp_lt hrem_next, hml1⟩
      · have hp_lt := bv64_lt_add_of_hc (by assumption) (by omega)
        have ⟨h2le, hn⟩ := bva_slice_occ_info hrem1 (by omega) (by omega)
          (by rw [← helem _ (by omega)]; assumption)
        have hp1_n : (p + 1#64).toNat = p.toNat + 1 := bv64_add_toNat (by omega)
        have hp2_n : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by
          rw [bv64_add_toNat (by rw [hp1_n]; omega), hp1_n, h1_64]
        exact ih1 (qn, p + 1#64 + 1#64, ()) ml1 (by dsimp only; rw [hp2_n]; omega)
          ⟨st1, by rw [hp2_n]; exact bva_loop1_occ hinv1 hp_lt h2le hn, hml1⟩
      · exfalso; have hp_lt := bv64_lt_add_of_hc (by assumption) (by omega)
        have ⟨h2le, _⟩ := bva_slice_occ_info hrem1 (by omega) (by omega)
          (by rw [← helem _ (by omega)]; assumption)
        have hpc : ¬ (p.toNat + 1) % 2 ^ 64 < (off.toNat + sz.toNat) % 2 ^ 64 := by
          simpa only [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl] using hc
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hpc; omega
      all_goals exact hJ1x () ml1 ⟨st1, hinv1.1, hsb1, hqn_le, hscr1_ok, hml1⟩

end LeanQbe.T.Examples.Kissat.Full
