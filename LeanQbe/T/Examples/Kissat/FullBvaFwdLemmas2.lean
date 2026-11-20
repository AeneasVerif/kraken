module

public import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Forward Subsumption `Func.wp` Proofs — Part 2 (`Stage 4`)

Proves parametric `(Γ : Env)` `Func.wp` contracts for Forward Subsumption (`Full.lean`):
1. `full_fwd_dedup_bins` (`full_fwd_dedup_bins_wp` → `fullFwdDedupBinsSpec`)
2. `full_forward_sub` (`full_forward_sub_wp` → `fullForwardSubSpec`)
(plus `full_fwd_check_cl_wp` once `#984`'s 1-line guard lands on `main`).
-/

set_option autoImplicit false

@[expose] public section

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

/-! ## 1. Helper lemmas for `full_forward_sub` and `full_fwd_dedup_bins` -/

private theorem zero_mem_fullArenaClauseRefs_of_pos {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k) (hpos : 0 < k.arena_len) :
    0 ∈ fullArenaClauseRefsCore k := by
  rcases ha.len_ok with hz | h3
  · omega
  · unfold fullArenaClauseRefsCore
    cases hal : k.arena_len with
    | zero => omega
    | succ n =>
      rw [fullArenaScanRefs]
      have hle : 0 + 3 ≤ n + 1 := by omega
      simp [hle]

private def dedupInnerMask (t : FullState) : FullState :=
  { t with core := { t.core with wstk := [], lit_mark := [], num_binary := 0#64 } }

private def dedupLmMask (t : FullState) : FullState :=
  { t with core := { t.core with lit_mark := [] } }

private def dedupWstkMask (t : FullState) : FullState :=
  { t with core := { t.core with wstk := [] } }

private theorem dedup_reconstruct_state {s st : FullState}
    (h : AgreesExcept dedupInnerMask s st) :
    st = { s with core := { s.core with
      wstk := st.core.wstk, lit_mark := st.core.lit_mark, num_binary := st.core.num_binary } } := by
  have hsc : st.scratch = s.scratch := h.get FullState.scratch
  have hc : st.core = { s.core with
      wstk := st.core.wstk, lit_mark := st.core.lit_mark, num_binary := st.core.num_binary } := by
    have h1 := congrArg FullState.core h
    cases st; cases s; rename_i sc1 _ sc2 _
    cases sc1; cases sc2
    simp only [dedupInnerMask] at h1
    cases h1; rfl
  cases st; cases s; simp only at hsc hc; rw [hsc]; exact congrArg (fun x => FullState.mk x _) hc

private theorem dedup_lm_reconstruct {s st : FullState}
    (h : AgreesExcept dedupLmMask s st) :
    st = { s with core := { s.core with lit_mark := st.core.lit_mark } } := by
  have hsc : st.scratch = s.scratch := h.get FullState.scratch
  have hc : st.core = { s.core with lit_mark := st.core.lit_mark } := by
    have h1 := congrArg FullState.core h
    cases st; cases s; rename_i sc1 _ sc2 _
    cases sc1; cases sc2
    simp only [dedupLmMask] at h1
    cases h1; rfl
  cases st; cases s; simp only at hsc hc; rw [hsc]; exact congrArg (fun x => FullState.mk x _) hc

private theorem dedup_wstk_reconstruct {s st : FullState}
    (h : AgreesExcept dedupWstkMask s st) :
    st = { s with core := { s.core with wstk := st.core.wstk } } := by
  have hsc : st.scratch = s.scratch := h.get FullState.scratch
  have hc : st.core = { s.core with wstk := st.core.wstk } := by
    have h1 := congrArg FullState.core h
    cases st; cases s; rename_i sc1 _ sc2 _
    cases sc1; cases sc2
    simp only [dedupWstkMask] at h1
    cases h1; rfl
  cases st; cases s; simp only at hsc hc; rw [hsc]; exact congrArg (fun x => FullState.mk x _) hc

/-! ## 2. `full_forward_sub_wp` -/

theorem full_forward_sub_wp (Γ : Env)
    (hDedup : ∀ args m Q X, fullFwdDedupBinsSpec args m Q X →
      Γ "full_fwd_dedup_bins" [i64] [.bool] args m Q X)
    (hArenaNext : ∀ args m Q X, fullArenaNextSpec args m Q X →
      Γ "full_arena_next" [i64, i32] [i32] args m Q X)
    (hCheckCl : ∀ args m Q X, fullFwdCheckClSpec args m Q X →
      Γ "full_fwd_check_cl" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullForwardSubSpec args m Q X →
      Func.wp Γ full_forward_sub_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have har_cap := c.harena; unfold dimacsBound at har_cap
  bf_steps
  obtain ⟨F_cur, hw⟩ := hinv.1.witness
  c0_call hDedup
  refine ⟨c, F0, F_cur, s, R, rfl, ⟨hinv.1.lengths, hw, hinv.2⟩, hm,
    fun ok s1 m1 hinv1W hcv1 hfuel1 hfalse1 hm1 => ?_⟩
  have hinv1 := hinv1W.toDense
  bf_steps
  · refine wp_loop_inv
      (fun (p, budget, ()) ml => ∃ st : FullState,
        FullDenseInv c F0 st ∧ st.core.cur_vars = s.core.cur_vars ∧
        st.core.fuel = s.core.fuel ∧ p.toNat ≤ st.core.arena_len ∧
        (p.toNat = st.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs st) ∧
        (FullMem c st ⋆ R) ml)
      (fun (p, _, _) _ => c.arena_cap - p.toNat)
      (fun J hJ => by
        bf_steps
        obtain ⟨F1, hw1⟩ := hinv1.1.witness
        refine hJ (0#64, 2048#64, ()) m1 ⟨s1, hinv1, hcv1, hfuel1, Nat.zero_le _, ?_, hm1⟩
        by_cases hz : s1.core.arena_len = 0
        · exact Or.inl hz.symm
        · exact Or.inr (zero_mem_fullArenaClauseRefs_of_pos hw1.arena (Nat.pos_of_ne_zero hz)))
      (fun J (p, budget, ()) ml ⟨st, hst, hcv_st, hfuel_st, hp_le, hp_mem, hml⟩ ih => ?_)
    have hlen_st := hst.1.lengths.core_ok
    have hal_le := hlen_st.arena_len_le
    have hal_arr := hlen_st.arena_len_arr
    obtain ⟨F_st, hw_st⟩ := hst.1.witness
    bf_steps
    · have hp_lt : p.toNat < st.core.arena_len := by c0_bound
      have hp_ref : p.toNat ∈ fullArenaClauseRefs st := hp_mem.resolve_left (by omega)
      have hwf_p := hw_st.arena.refs_wf p.toNat hp_ref
      have hp2_lt : p.toNat + 2 < st.core.arena.length := by omega
      have hp32 : (p.truncate 32).toNat = p.toNat := by
        rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
      bf_steps
      c0_call hArenaNext
      refine ⟨c, st, R, rfl, hst.1.lengths, hml, ?_⟩
      have hnb := fullArenaNextOff_bounds (ar := st.core.arena) (alen := st.core.arena_len)
        (cref := p.toNat) hwf_p.1
      have hnp_mem := fullArenaClauseRefs_next_mem hw_st.arena hp_ref
      have hnp_lt32 : fullArenaNextOff st.core.arena st.core.arena_len p.toNat < 2 ^ 32 := by omega
      have hnp_toNat : (BitVec.zeroExtend 64
          (BitVec.ofNat 32 (fullArenaNextOff st.core.arena st.core.arena_len
            (p.truncate 32).toNat))).toNat =
          fullArenaNextOff st.core.arena st.core.arena_len p.toNat := by
        rw [hp32, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hnp_lt32, Nat.mod_eq_of_lt (by omega)]
      bf_steps
      · c0_call hCheckCl
        refine ⟨c, F0, F_st, st, R, rfl, ⟨hst.1.lengths, hw_st, hst.2⟩, by rw [hp32]; exact hp_ref,
          hml, fun ok2 st2 m2 hst2W hcv2 hal2 hfuel2 hrefs2 hfalse2 hm2 => ?_⟩
        have hst2 := hst2W.toDense
        bf_steps
        · refine ih _ _ (by dsimp only; rw [hnp_toNat]; omega)
            ⟨st2, hst2, hcv2.trans hcv_st, hfuel2.trans hfuel_st, by rw [hnp_toNat, hal2]; omega,
             by rw [hnp_toNat, hal2, hrefs2]; exact hnp_mem, hm2⟩
        · exact hQ 20#64 st2 m2 hst2 (hcv2.trans hcv_st) (hfuel2.trans hfuel_st)
            (Or.inr rfl) (fun _ => hfalse2 hc) hm2
      · refine ih _ _ (by dsimp only; rw [hnp_toNat]; omega)
          ⟨st, hst, hcv_st, hfuel_st, by rw [hnp_toNat]; omega,
           by rw [hnp_toNat]; exact hnp_mem, hml⟩
      · refine ih _ _ (by dsimp only; rw [hnp_toNat]; omega)
          ⟨st, hst, hcv_st, hfuel_st, by rw [hnp_toNat]; omega,
           by rw [hnp_toNat]; exact hnp_mem, hml⟩
      · refine ih _ _ (by dsimp only; rw [hnp_toNat]; omega)
          ⟨st, hst, hcv_st, hfuel_st, by rw [hnp_toNat]; omega,
           by rw [hnp_toNat]; exact hnp_mem, hml⟩
    · exact hQ 20#64 st ml hst hcv_st hfuel_st (Or.inr rfl)
        (fun _ => hst.1.inconsistent_unsat hc) hml
    · exact hQ 20#64 st ml hst hcv_st hfuel_st (Or.inr rfl)
        (fun _ => hst.1.inconsistent_unsat hc) hml
    · exact hQ 1#64 st ml hst hcv_st hfuel_st (Or.inl rfl) (by simp) hml
    · exact hQ 20#64 st ml hst hcv_st hfuel_st (Or.inr rfl)
        (fun _ => hst.1.inconsistent_unsat hc) hml
    · exact hQ 1#64 st ml hst hcv_st hfuel_st (Or.inl rfl) (by simp) hml
  · exact hQ 20#64 s1 m1 hinv1 hcv1 hfuel1 (Or.inr rfl) (fun _ => hfalse1 hc) hm1

/-! ## 3. Factored pure lemmas & `full_fwd_dedup_bins_wp` -/

private def DedupLoop1Inv (c : FullCfg) (F_cur : List (List Nat)) (st : FullState)
    (l off sz p q : Nat) (ul : Bool) (st1 : FullState) : Prop :=
  AgreesExcept dedupInnerMask st st1 ∧
  st1.core.wstk.length = c.wcap ∧ st1.core.lit_mark.length = 2 * c.max_vars ∧
  off ≤ q ∧ q ≤ p ∧ p ≤ off + sz ∧
  (∀ idx, idx < off ∨ off + sz ≤ idx → st1.core.wstk[idx]? = st.core.wstk[idx]?) ∧
  (∀ idx, p ≤ idx → idx < off + sz → st1.core.wstk[idx]? = st.core.wstk[idx]?) ∧
  DenseWatchSliceOk F_cur st1.core l off (q - off) ∧
  DenseWatchSliceOk F_cur st1.core l p (off + sz - p) ∧
  (∀ x < 2 * c.max_vars, st1.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
    ∃ idx, off ≤ idx ∧ idx < q ∧
      (st1.core.wstk[idx]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 ∧
      (st1.core.wstk[idx]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat = x) ∧
  (ul = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [l]))

private theorem dedup_step_occ_ok {c : FullCfg} {F_cur : List (List Nat)} {st st1 : FullState}
    {l off sz p q : Nat} {ul : Bool}
    (h : DedupLoop1Inv c F_cur st l off sz p q ul st1)
    (hp_lt : p < off + sz) (hp_ws : p < st1.core.wstk.length)
    (hflag : (st1.core.wstk[p]'hp_ws &&& 0x80000000#32) = 0#32) :
    p + 1 < off + sz ∧
    ∀ (hp1_ws : p + 1 < st1.core.wstk.length),
      let w0 := st1.core.wstk[p]'hp_ws
      let wstk1 := st1.core.wstk.set q w0
      let w1 := wstk1[p + 1]'(by simp [wstk1, hp1_ws])
      DedupLoop1Inv c F_cur st l off sz (p + 2) (q + 2) ul
        { st1 with core := { st1.core with wstk := wstk1.set (q + 1) w1 } } := by
  obtain ⟨hag, hws, hlm, hq_ge, hq_le, hp_le, hout, hrem_eq, hpref, hrem, hlmi, hul⟩ := h
  rcases denseWatchSliceOk_step hrem (by omega) with
    ⟨w0, hw0_some, hbin_ne, _, _, _, _⟩ |
    ⟨w0, cr, h2le, hw0_some, hcr_some, hbin_eq, hw0_sz3, hcr_lt, hcr_mem, hrem_next⟩
  · have hw0_val : st1.core.wstk[p]'hp_ws = w0 := by
      rw [List.getElem?_eq_getElem hp_ws] at hw0_some; exact Option.some.inj hw0_some
    exact absurd (hw0_val ▸ hflag) hbin_ne
  · refine ⟨by omega, fun hp1_ws => ?_⟩
    have hw0_val : st1.core.wstk[p]'hp_ws = w0 := by
      rw [List.getElem?_eq_getElem hp_ws] at hw0_some; exact Option.some.inj hw0_some
    have hcr_val : st1.core.wstk[p + 1]'hp1_ws = cr := by
      rw [List.getElem?_eq_getElem hp1_ws] at hcr_some; exact Option.some.inj hcr_some
    have hq_ws : q < st1.core.wstk.length := by omega
    have hq1_ws : q + 1 < st1.core.wstk.length := by omega
    let wstk2 := (st1.core.wstk.set q (st1.core.wstk[p]'hp_ws)).set (q + 1)
      ((st1.core.wstk.set q (st1.core.wstk[p]'hp_ws))[p + 1]'(by simp [hp1_ws]))
    have hw1_eq : (st1.core.wstk.set q (st1.core.wstk[p]'hp_ws))[p + 1]'(by simp [hp1_ws]) =
        cr := by
      rw [List.getElem_set_ne (by omega)]; exact hcr_val
    let st2 : FullState := { st1 with core := { st1.core with wstk := wstk2 } }
    refine ⟨hag.trans rfl, by simp [hws], hlm, by omega, by omega, by omega,
      fun idx hidx => by
        dsimp only [st2, wstk2]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hout idx hidx,
      fun idx hi1 hi2 => by
        dsimp only [st2, wstk2]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hrem_eq idx (by omega) hi2,
      ?_, ?_, ?_, hul⟩
    · rw [show q + 2 - off = (q - off) + 2 by omega]
      refine denseWatchSliceOk_append
        (DenseWatchSliceOk.mono (k := st1.core) (k' := st2.core)
          (by rw [CNF.entails_def]; exact fun _ h => h) (Nat.le_refl _) (fun _ hr => hr)
          (fun idx hi1 hi2 => by
            dsimp only [st2, wstk2]
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]) hpref) ?_
      rw [show off + (q - off) = q by omega]
      have hq0_s : st2.core.wstk[q]? = some w0 := by
        dsimp only [st2, wstk2]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hq_ws, hw0_val]
      have hq1_s : st2.core.wstk[q + 1]? = some cr := by
        dsimp only [st2, wstk2]; rw [List.getElem?_set_self (by simp [hq1_ws]), hw1_eq]
      exact DenseWatchSliceOk.occ hq0_s hq1_s hbin_eq hw0_sz3 hcr_lt hcr_mem .empty
    · rw [show off + sz - (p + 2) = off + sz - p - 2 by omega]
      exact DenseWatchSliceOk.mono (k := st1.core) (k' := st2.core)
        (by rw [CNF.entails_def]; exact fun _ h => h) (Nat.le_refl _) (fun _ hr => hr)
        (fun idx hi1 hi2 => by
          dsimp only [st2, wstk2]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]) hrem_next
    · intro x hx hne
      obtain ⟨idx, hi1, hi2, hb, ho⟩ := hlmi x hx hne
      refine ⟨idx, hi1, by omega, ?_, ?_⟩
      · dsimp only [st2, wstk2]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hb
      · dsimp only [st2, wstk2]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact ho

private theorem dedup_step_bin_info {c : FullCfg} {F_cur : List (List Nat)} {st st1 : FullState}
    {l off sz p q : Nat} {ul : Bool}
    (h : DedupLoop1Inv c F_cur st l off sz p q ul st1)
    (hp_lt : p < off + sz) (hp_ws : p < st1.core.wstk.length)
    (hflag : (st1.core.wstk[p]'hp_ws &&& 0x80000000#32) ≠ 0#32) :
    let w0 := st1.core.wstk[p]'hp_ws
    w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * st.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
    DenseWatchSliceOk F_cur st1.core l (p + 1) (off + sz - (p + 1)) := by
  obtain ⟨hag, _, _, _, _, _, _, _, _, hrem, _, _⟩ := h
  have hcv : st1.core.cur_vars = st.core.cur_vars := by rw [dedup_reconstruct_state hag]
  rcases denseWatchSliceOk_step hrem (by omega) with
    ⟨w0, hw0_some, _, hneff, hot_lt, hent, hrem_next⟩ |
    ⟨w0, _, _, hw0_some, _, hbin_eq, _, _, _, _⟩
  · have hw0_val : st1.core.wstk[p]'hp_ws = w0 := by
      rw [List.getElem?_eq_getElem hp_ws] at hw0_some; exact Option.some.inj hw0_some
    rw [hw0_val]
    exact ⟨hneff, hcv ▸ hot_lt, hent,
      by rw [show off + sz - (p + 1) = off + sz - p - 1 by omega]; exact hrem_next⟩
  · have hw0_val : st1.core.wstk[p]'hp_ws = w0 := by
      rw [List.getElem?_eq_getElem hp_ws] at hw0_some; exact Option.some.inj hw0_some
    exact absurd (hw0_val.symm ▸ hbin_eq) hflag

private theorem dedup_step_bin_drop {c : FullCfg} {F_cur : List (List Nat)} {st st1 : FullState}
    {l off sz p q : Nat} {ul : Bool}
    (h : DedupLoop1Inv c F_cur st l off sz p q ul st1)
    (hp_lt : p < off + sz) (hp_ws : p < st1.core.wstk.length)
    (hflag : (st1.core.wstk[p]'hp_ws &&& 0x80000000#32) ≠ 0#32) (nb' : BitVec 64) :
    DedupLoop1Inv c F_cur st l off sz (p + 1) q ul
      { st1 with core := { st1.core with num_binary := nb' } } := by
  have ⟨_, _, _, hrem_next⟩ := dedup_step_bin_info h hp_lt hp_ws hflag
  obtain ⟨hag, hws, hlm, hq_ge, hq_le, hp_le, hout, hrem_eq, hpref, _, hlmi, hul⟩ := h
  let st2 : FullState := { st1 with core := { st1.core with num_binary := nb' } }
  exact ⟨hag.trans rfl, hws, hlm, hq_ge, by omega, by omega, hout,
    fun idx hi1 hi2 => hrem_eq idx (by omega) hi2,
    DenseWatchSliceOk.mono (k := st1.core) (k' := st2.core)
      (by rw [CNF.entails_def]; exact fun _ h => h) (Nat.le_refl _) (fun _ hr => hr)
      (fun _ _ _ => rfl) hpref,
    DenseWatchSliceOk.mono (k := st1.core) (k' := st2.core)
      (by rw [CNF.entails_def]; exact fun _ h => h) (Nat.le_refl _) (fun _ hr => hr)
      (fun _ _ _ => rfl) hrem_next,
    hlmi, hul⟩

private theorem dedup_step_bin_keep {c : FullCfg} {F_cur : List (List Nat)} {st st1 : FullState}
    {l off sz p q : Nat} {ul ul2 : Bool}
    (h : DedupLoop1Inv c F_cur st l off sz p q ul st1)
    (hp_lt : p < off + sz) (hp_ws : p < st1.core.wstk.length)
    (hflag : (st1.core.wstk[p]'hp_ws &&& 0x80000000#32) ≠ 0#32)
    (hul2 : ul2 = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [l])) :
    let w0 := st1.core.wstk[p]'hp_ws
    DedupLoop1Inv c F_cur st l off sz (p + 1) (q + 1) ul2
      { st1 with core := { st1.core with
        lit_mark := st1.core.lit_mark.set (w0 &&& 0x7FFFFFFF#32).toNat 1#8
        wstk := st1.core.wstk.set q w0 } } := by
  have ⟨hneff, hot_lt, hent, hrem_next⟩ := dedup_step_bin_info h hp_lt hp_ws hflag
  obtain ⟨hag, hws, hlm, hq_ge, hq_le, hp_le, hout, hrem_eq, hpref, _, hlmi, _⟩ := h
  have hcv : st1.core.cur_vars = st.core.cur_vars := by rw [dedup_reconstruct_state hag]
  have hq_ws : q < st1.core.wstk.length := by omega
  let w0 := st1.core.wstk[p]'hp_ws
  let st2 : FullState := { st1 with core := { st1.core with
    lit_mark := st1.core.lit_mark.set (w0 &&& 0x7FFFFFFF#32).toNat 1#8
    wstk := st1.core.wstk.set q w0 } }
  refine ⟨hag.trans rfl, by simp [hws], by simp [hlm], by omega, by omega, by omega,
    fun idx hidx => by dsimp only [st2]; rw [List.getElem?_set_ne (by omega)]; exact hout idx hidx,
    fun idx hi1 hi2 => by
      dsimp only [st2]; rw [List.getElem?_set_ne (by omega)]; exact hrem_eq idx (by omega) hi2,
    ?_, ?_, ?_, hul2⟩
  · rw [show q + 1 - off = (q - off) + 1 by omega]
    refine denseWatchSliceOk_append
      (DenseWatchSliceOk.mono (k := st1.core) (k' := st2.core)
        (by rw [CNF.entails_def]; exact fun _ h => h) (Nat.le_refl _) (fun _ hr => hr)
        (fun idx hi1 hi2 => by dsimp only [st2]; rw [List.getElem?_set_ne (by omega)]) hpref) ?_
    rw [show off + (q - off) = q by omega]
    have hq_s : st2.core.wstk[q]? = some w0 := by
      dsimp only [st2]; exact List.getElem?_set_self hq_ws
    exact DenseWatchSliceOk.bin hq_s hflag hneff (by dsimp only [st2]; rw [hcv]; exact hot_lt)
      hent .empty
  · exact DenseWatchSliceOk.mono (k := st1.core) (k' := st2.core)
      (by rw [CNF.entails_def]; exact fun _ h => h) (Nat.le_refl _) (fun _ hr => hr)
      (fun idx hi1 hi2 => by dsimp only [st2]; rw [List.getElem?_set_ne (by omega)]) hrem_next
  · intro x hx hne; dsimp only [st2] at hne
    by_cases hxo : x = (w0 &&& 0x7FFFFFFF#32).toNat
    · refine ⟨q, hq_ge, by omega, ?_, ?_⟩
      · dsimp only [st2]; rw [List.getElem?_set_self hq_ws, Option.getD_some]; exact hflag
      · dsimp only [st2]; rw [List.getElem?_set_self hq_ws, Option.getD_some]; exact hxo.symm
    · rw [List.getElem?_set_ne (Ne.symm hxo)] at hne
      obtain ⟨idx, hi1, hi2, hb, ho⟩ := hlmi x hx hne
      refine ⟨idx, hi1, by omega, ?_, ?_⟩
      · dsimp only [st2]; rw [List.getElem?_set_ne (by omega)]; exact hb
      · dsimp only [st2]; rw [List.getElem?_set_ne (by omega)]; exact ho

private theorem dedup_unit_of_neg_mark {c : FullCfg} {F_cur : List (List Nat)} {st st1 : FullState}
    {l off sz p q : Nat} {ul : Bool}
    (h : DedupLoop1Inv c F_cur st l off sz p q ul st1)
    (hcv_le : st.core.cur_vars ≤ c.max_vars)
    (hp_lt : p < off + sz) (hp_ws : p < st1.core.wstk.length)
    (hflag : (st1.core.wstk[p]'hp_ws &&& 0x80000000#32) ≠ 0#32)
    (hneg_lm : st1.core.lit_mark[((st1.core.wstk[p]'hp_ws &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat]?.getD
      0#8 ≠ 0#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l]) := by
  have ⟨_, hot_lt, hent, _⟩ := dedup_step_bin_info h hp_lt hp_ws hflag
  obtain ⟨_, _, _, hq_ge, _, _, _, _, hpref, _, hlmi, _⟩ := h
  have hnot_lt : ((st1.core.wstk[p]'hp_ws &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat < 2 * c.max_vars := by
    rw [FullBvaFwdTactics.bv32_xor1_toNat]
    exact Nat.lt_of_lt_of_le (litNeg_lt_two_mul hot_lt) (by omega)
  obtain ⟨idx, hi1, hi2, hb, ho⟩ := hlmi _ hnot_lt hneg_lm
  have hent_neg := (denseWatchSliceOk_bin_word_props hpref idx hi1 (by omega) hb).2
  rw [ho, FullBvaFwdTactics.bv32_xor1_toNat] at hent_neg
  exact entails_unit_of_bin_pair hent hent_neg

private theorem dedup_finalize_dense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {st st1 st2 st3 : FullState} {l off sz q : Nat} {ul : Bool}
    (hst : FullDenseInv c F0 st) (hw : FullWitnessInv c F0 F_cur st.core)
    (hl_lt : l < 2 * st.core.cur_vars)
    (hoff_eq : off = fullWatchOffCore st.core l) (hsz_eq : sz = fullWatchSizeCore st.core l)
    (h1 : DedupLoop1Inv c F_cur st l off sz (off + sz) q ul st1)
    (hag2 : AgreesExcept dedupLmMask st1 st2) (hlm2 : st2.core.lit_mark.length = 2 * c.max_vars)
    (hlm2_clear : ∀ x < 2 * c.max_vars, st2.core.lit_mark[x]?.getD 0#8 = 0#8)
    (hag3 : AgreesExcept dedupWstkMask st2 st3) (hws3 : st3.core.wstk.length = c.wcap)
    (hws3_eq : ∀ idx, idx < q ∨ off + sz ≤ idx → st3.core.wstk[idx]? = st1.core.wstk[idx]?)
    (wu' : BitVec 64) :
    let st4 : FullState :=
      { st3 with core := { st3.core with
        wvec := st3.core.wvec.set (2 * l + 1) (BitVec.ofNat 32 (q - off))
        wusable := wu' } }
    FullWitnessInv c F0 F_cur st4.core ∧ FullDenseInv c F0 st4 ∧
    st4.core.cur_vars = st.core.cur_vars ∧ st4.core.arena = st.core.arena ∧
    st4.core.arena_len = st.core.arena_len ∧ st4.core.fuel = st.core.fuel := by
  obtain ⟨hag1, _, _, hq_ge, hq_le, _, hout1, _, hpref1, _, _, _⟩ := h1
  have hst1_eq := dedup_reconstruct_state hag1
  have hst2_eq := dedup_lm_reconstruct hag2
  have hst3_eq := dedup_wstk_reconstruct hag3
  have hlm2_eq : st2.core.lit_mark = st.core.lit_mark := by
    apply List.ext_getElem (by rw [hlm2, hst.1.lengths.core_ok.lit_mark_len])
    intro i hi1 hi2
    have h1' := hlm2_clear i (by omega)
    have h2' := hst.2.1.2 i (by omega)
    rw [List.getElem?_eq_getElem hi1, Option.getD_some] at h1'
    rw [List.getElem?_eq_getElem hi2, Option.getD_some] at h2'
    exact h1'.trans h2'.symm
  let k4 : FullCoreState :=
    { st.core with
      wstk := st3.core.wstk
      wvec := st.core.wvec.set (2 * l + 1) (BitVec.ofNat 32 (q - off))
      wusable := wu'
      num_binary := st1.core.num_binary }
  have hk4_eq : ({ st3.core with
      wvec := st3.core.wvec.set (2 * l + 1) (BitVec.ofNat 32 (q - off))
      wusable := wu' } : FullCoreState) = k4 := by
    rw [hst3_eq, hst2_eq, hst1_eq]; dsimp only [k4]; rw [hlm2_eq]
  have hsc4_eq : st3.scratch = st.scratch := by rw [hst3_eq, hst2_eq, hst1_eq]
  have hst4_eq : ({ st3 with core := { st3.core with
      wvec := st3.core.wvec.set (2 * l + 1) (BitVec.ofNat 32 (q - off))
      wusable := wu' } } : FullState) = { st with core := k4 } := by
    cases st3; cases st; simp only at hk4_eq hsc4_eq; rw [hsc4_eq]
    exact congrArg (fun x => FullState.mk x _) hk4_eq
  have hrefs1 : fullArenaClauseRefsCore st1.core = fullArenaClauseRefsCore st.core := by
    unfold fullArenaClauseRefsCore; rw [hst1_eq]
  have hslice4 : DenseWatchSliceOk F_cur k4 l (fullWatchOffCore st.core l) (q - off) := by
    rw [← hoff_eq]
    have hcv1_eq : st1.core.cur_vars = st.core.cur_vars := by rw [hst1_eq]
    have hrefs_k4 : fullArenaClauseRefsCore k4 = fullArenaClauseRefsCore st.core := rfl
    exact DenseWatchSliceOk.mono (k := st1.core) (k' := k4)
      (by rw [CNF.entails_def]; exact fun _ h => h)
      (by dsimp only [k4]; omega)
      (by intro r hr; rw [hrefs_k4, ← hrefs1]; exact hr)
      (fun idx hi1 hi2 => by dsimp only [k4]; exact hws3_eq idx (Or.inl (by omega))) hpref1
  have ⟨hlen4, hw4⟩ := fullWitnessInv_update_dense_slice hst.1.lengths.core_ok hw hst.2.2.2.2.2
    hl_lt (nsz := q - off) (wstk' := st3.core.wstk) (wu' := wu') (nb' := st1.core.num_binary)
    hws3 (by omega)
    (fun idx hidx => by
      rw [← hoff_eq, ← hsz_eq] at hidx
      have hidx1 : idx < q ∨ off + sz ≤ idx := by
        rcases hidx with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      have hidx2 : idx < off ∨ off + sz ≤ idx := by
        rcases hidx with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      rw [hws3_eq idx hidx1]; exact hout1 idx hidx2)
    hslice4
  intro st4
  have hst4_rw : st4 = { st with core := k4 } := hst4_eq
  rw [hst4_rw]
  obtain ⟨⟨hslen, _, _⟩, hmrk, hnodup, hext, hl0, hdm⟩ := hst
  exact ⟨hw4, ⟨⟨{ hslen with core_ok := hlen4 }, F_cur, hw4⟩, hmrk, hnodup, hext, hl0, hdm⟩,
    rfl, rfl, rfl, rfl⟩

private theorem fullDenseInv_of_addUnit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hinv : FullDenseInv c F0 s) (hlen' : s'.LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hl0' : s'.core.cur_level = 0) (har' : s'.core.arena = s.core.arena)
    (hal' : s'.core.arena_len = s.core.arena_len) (hmrk' : s'.core.mrk = s.core.mrk)
    (hlm' : s'.core.lit_mark = s.core.lit_mark) (hdm' : s'.core.dense_mode = s.core.dense_mode)
    (hll' : s'.scratch.last_learned = s.scratch.last_learned)
    (hext' : s'.scratch.extend_len = s.scratch.extend_len) : FullDenseInv c F0 s' :=
  (fullDenseInv_of_fwd_call hinv hlen' hw' hl0' har' hal' hmrk' hlm' hdm' hll' hext').1

theorem full_fwd_dedup_bins_wp (Γ : Env)
    (hAddUnit : ∀ args m Q X, fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullFwdDedupBinsSpec args m Q X →
      Func.wp Γ full_fwd_dedup_bins_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinvW, hm, hQ⟩
  have hinv := hinvW.toDense; have hw := hinvW.2.1
  have hmx := c.hmaxv; have hwcap := c.hwcap; unfold dimacsBound at hmx hwcap
  have hcv_le_mx : s.core.cur_vars ≤ c.max_vars := hinv.1.lengths.core_ok.cur_vars_le
  have hnlits : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    c0_bound
  unfold Func.wp full_fwd_dedup_bins_body; dsimp only
  bf_fast
  refine wp_loop_inv
    (fun (l, ()) ml => ∃ st : FullState,
      l.toNat ≤ 2 * s.core.cur_vars ∧ FullDenseInv c F0 st ∧ FullWitnessInv c F0 F_cur st.core ∧
      st.core.cur_vars = s.core.cur_vars ∧ st.core.arena = s.core.arena ∧
      st.core.arena_len = s.core.arena_len ∧ st.core.fuel = s.core.fuel ∧
      (FullMem c st ⋆ R) ml)
    (fun (l, ()) _ => 2 * s.core.cur_vars - l.toNat)
    (fun J hJ => by
      bf_fast
      exact hJ (0#64, ()) m ⟨s, Nat.zero_le _, hinv, hw, rfl, rfl, rfl, rfl, hm⟩)
    (fun J (l, ()) ml ⟨st, hl_le, hst, hw, hcv_st, har_st, hal_st, hfuel_st, hml⟩ ih => ?_)
  have hlen := hst.1.lengths.core_ok
  have hcv_st_le : st.core.cur_vars ≤ c.max_vars := hlen.cur_vars_le
  have hwv_len := hlen.wvec_len; have hws_len := hlen.wstk_len_arr
  have hwlen_le := hlen.wlen_le; have hlm_len := hlen.lit_mark_len
  bf_fast
  · have hl_lt : l.toNat < 2 * st.core.cur_vars := by c0_bound
    have hl1_toNat : (l + 1#64).toNat = l.toNat + 1 := by c0_bound
    exact ih _ _
      (by dsimp only; rw [show (l + 1 : BitVec 64) = l + 1#64 from rfl, hl1_toNat]; omega)
      ⟨st, by rw [show (l + 1 : BitVec 64) = l + 1#64 from rfl, hl1_toNat]; omega,
       hst, hw, hcv_st, har_st, hal_st, hfuel_st, hml⟩
  · have hl_lt : l.toNat < 2 * st.core.cur_vars := by c0_bound
    have hdm : st.core.dense_mode ≠ 0#64 := hst.2.2.2.2.2
    have hdw : DenseWatchesInv F_cur st.core := by
      have h := hw.watches; unfold ModeWatchesInv at h; rwa [ite_eq_right hdm] at h
    have hoff_idx : (l <<< (1 : Nat)).toNat = 2 * l.toNat := by c0_bound
    have hsz_idx : ((l <<< (1 : Nat)) + 1#64).toNat = 2 * l.toNat + 1 := by c0_bound
    have hoff_eq : (BitVec.setWidth 64
        (st.core.wvec[(l <<< (1 : Nat)).toNat]'(by omega))).toNat =
        fullWatchOffCore st.core l.toNat := by
      unfold fullWatchOffCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (by have := (st.core.wvec[2 * l.toNat]'(by omega)).isLt; omega)]
      congr 2
    have hsz_eq : (BitVec.setWidth 64
        (st.core.wvec[((l <<< (1 : Nat)) + 1#64).toNat]'(by omega))).toNat =
        fullWatchSizeCore st.core l.toNat := by
      unfold fullWatchSizeCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (by have := (st.core.wvec[2 * l.toNat + 1]'(by omega)).isLt; omega)]
      congr 2
    have hbd_l := hdw.layout.bounds l.toNat hl_lt
    have hslice0 := hdw.slices l.toNat hl_lt
    generalize hoff_v : BitVec.setWidth 64
        (st.core.wvec[(l <<< (1 : Nat)).toNat]'(by omega)) = off at *
    generalize hsz_v : BitVec.setWidth 64
        (st.core.wvec[((l <<< (1 : Nat)) + 1#64).toNat]'(by omega)) = sz at *
    have hend_toNat : (off + sz).toNat = off.toNat + sz.toNat := by bv_omega
    -- Inner loop 1: deduplicate binary watches into `wstk[off..q)` and mark `lit_mark`
    refine wp_loop_inv
      (fun (p, q, ul, ()) ml1 => ∃ st1 : FullState,
        DedupLoop1Inv c F_cur st l.toNat off.toNat sz.toNat p.toNat q.toNat ul st1 ∧
        (FullMem c st1 ⋆ R) ml1)
      (fun (p, _, _, _) _ => off.toNat + sz.toNat - p.toNat)
      (fun J1 hJ1 => by
        bf_fast
        refine hJ1 (off, off, false, ()) ml
          ⟨st, ⟨.refl _ _, hws_len, hlm_len, Nat.le_refl _, Nat.le_refl _, by omega,
            fun _ _ => rfl, fun _ _ _ => rfl, by simpa using DenseWatchSliceOk.empty,
            by rw [show off.toNat + sz.toNat - off.toNat = sz.toNat by omega, hoff_eq, hsz_eq]
               exact hslice0,
            fun x hx hne => absurd (hst.2.1.2 x hx) hne, fun h => by cases h⟩, hml⟩)
      (fun J1 (p, q, ul, ()) ml1 ⟨st1, hinv1, hml1⟩ ih1 => ?_)
    have hws1 := hinv1.2.1; have hlm1 := hinv1.2.2.1
    have hq_ge := hinv1.2.2.2.1; have hq_le := hinv1.2.2.2.2.1; have hp_le := hinv1.2.2.2.2.2.1
    have hst1_eq := dedup_reconstruct_state hinv1.1
    have hcv1 : st1.core.cur_vars = st.core.cur_vars := by rw [hst1_eq]
    bf_fast
    · -- `occ` live: `(w0 & 0x80000000) = 0`, `p + 1 < end`
      have hp_lt : p.toNat < off.toNat + sz.toNat := by c0_bound
      have hflag_c : (st1.core.wstk[p.toNat]'(by omega) &&& 0x80000000#32) = 0#32 := by assumption
      have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
      have hp2_n : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by c0_bound
      have hq1_n : (q + 1#64).toNat = q.toNat + 1 := by c0_bound
      have hq2_n : (q + 2#64).toNat = q.toNat + 2 := by c0_bound
      have hp1_lt_end := (dedup_step_occ_ok hinv1 hp_lt (by omega) hflag_c).1
      have hocc := (dedup_step_occ_ok hinv1 hp_lt (by omega) hflag_c).2 (by omega)
      refine ih1 _ _
        (by dsimp only; rw [show (p + 1 + 1 : BitVec 64) = p + 1#64 + 1#64 from rfl, hp2_n]; omega)
        ⟨_, ?_, by assumption⟩
      rw [show (p + 1 + 1 : BitVec 64) = p + 1#64 + 1#64 from rfl,
          show (q + 2 : BitVec 64) = q + 2#64 from rfl, hp2_n, hq2_n]
      simpa only [show (q + 1 : BitVec 64) = q + 1#64 from rfl,
                  show (p + 1 : BitVec 64) = p + 1#64 from rfl, hq1_n, hp1_n] using hocc
    · -- `occ` dead: `(w0 & 0x80000000) = 0`, `¬(p + 1 < end)`
      have hp_lt : p.toNat < off.toNat + sz.toNat := by c0_bound
      have hflag_c : (st1.core.wstk[p.toNat]'(by omega) &&& 0x80000000#32) = 0#32 := by assumption
      have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
      have := (dedup_step_occ_ok hinv1 hp_lt (by omega) hflag_c).1
      exfalso; c0_bound
    · -- `bin` drop: `lm[ot] ≠ 0`, `l < ot`, `num_binary > 0`
      have hp_lt : p.toNat < off.toNat + sz.toNat := by c0_bound
      have hflag_c : (st1.core.wstk[p.toNat]'(by omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
      have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
      refine ih1 _ _
        (by dsimp only; rw [show (p + 1 : BitVec 64) = p + 1#64 from rfl, hp1_n]; omega)
        ⟨_, by rw [show (p + 1 : BitVec 64) = p + 1#64 from rfl, hp1_n]
               exact dedup_step_bin_drop hinv1 hp_lt (by omega) hflag_c (st1.core.num_binary - 1),
         by assumption⟩
    · -- `bin` drop: `lm[ot] ≠ 0`, `l < ot`, `num_binary == 0`
      have hp_lt : p.toNat < off.toNat + sz.toNat := by c0_bound
      have hflag_c : (st1.core.wstk[p.toNat]'(by omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
      have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
      refine ih1 _ _
        (by dsimp only; rw [show (p + 1 : BitVec 64) = p + 1#64 from rfl, hp1_n]; omega)
        ⟨st1, by rw [show (p + 1 : BitVec 64) = p + 1#64 from rfl, hp1_n]
                 exact dedup_step_bin_drop hinv1 hp_lt (by omega) hflag_c st1.core.num_binary, hml1⟩
    · -- `bin` drop: `lm[ot] ≠ 0`, `l >= ot`
      have hp_lt : p.toNat < off.toNat + sz.toNat := by c0_bound
      have hflag_c : (st1.core.wstk[p.toNat]'(by omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
      have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
      refine ih1 _ _
        (by dsimp only; rw [show (p + 1 : BitVec 64) = p + 1#64 from rfl, hp1_n]; omega)
        ⟨st1, by rw [show (p + 1 : BitVec 64) = p + 1#64 from rfl, hp1_n]
                 exact dedup_step_bin_drop hinv1 hp_lt (by omega) hflag_c st1.core.num_binary, hml1⟩
    · -- `bin` keep: `lm[ot] = 0`, `ot < nlits` — provide `lm[ot ^ 1]` bound and step!
      have hp_lt : p.toNat < off.toNat + sz.toNat := by c0_bound
      have hflag_c : (st1.core.wstk[p.toNat]'(by omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
      have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
      have hq1_n : (q + 1#64).toNat = q.toNat + 1 := by c0_bound
      have hot_lt := (dedup_step_bin_info hinv1 hp_lt (by omega) hflag_c).2.1
      have hlt_lm : ((st1.core.wstk[p.toNat]'(by omega) &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat <
          st1.core.lit_mark.length := by
        rw [FullBvaFwdTactics.bv32_xor1_toNat]
        exact Nat.lt_of_lt_of_le (litNeg_lt_two_mul hot_lt) (by omega)
      bf_fast
      · -- `lm[ot ^ 1] ≠ 0`, `ot < nlits` → `unit_l = true`
        have hneg_c : ¬ BitVec.setWidth 32 (st1.core.lit_mark[((st1.core.wstk[p.toNat]'(by omega)
            &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat]'hlt_lm) = 0#32 := by assumption
        have hneg_lm : st1.core.lit_mark[((st1.core.wstk[p.toNat]'(by omega) &&&
            0x7FFFFFFF#32) ^^^ 1#32).toNat]?.getD 0#8 ≠ 0#8 := by
          rw [List.getElem?_eq_getElem hlt_lm, Option.getD_some]
          exact fun h => hneg_c (by rw [h]; rfl)
        have hul_t := dedup_unit_of_neg_mark hinv1 hcv_st_le hp_lt (by omega) hflag_c hneg_lm
        refine ih1 _ _
          (by dsimp only; rw [show (p + 1 : BitVec 64) = p + 1#64 from rfl, hp1_n]; omega)
          ⟨_, by rw [show (p + 1 : BitVec 64) = p + 1#64 from rfl,
                     show (q + 1 : BitVec 64) = q + 1#64 from rfl, hp1_n, hq1_n]
                 exact dedup_step_bin_keep hinv1 hp_lt (by omega) hflag_c (fun _ => hul_t),
           by assumption⟩
      · -- `lm[ot ^ 1] = 0`, `ot < nlits` → keep `ul`
        refine ih1 _ _
          (by dsimp only; rw [show (p + 1 : BitVec 64) = p + 1#64 from rfl, hp1_n]; omega)
          ⟨_, by rw [show (p + 1 : BitVec 64) = p + 1#64 from rfl,
                     show (q + 1 : BitVec 64) = q + 1#64 from rfl, hp1_n, hq1_n]
                 exact dedup_step_bin_keep hinv1 hp_lt (by omega) hflag_c
                   hinv1.2.2.2.2.2.2.2.2.2.2.2,
           by assumption⟩
    · -- `bin` dead: `¬ ot < nlits` at outer `if`
      have hp_lt : p.toNat < off.toNat + sz.toNat := by c0_bound
      have hflag_c : (st1.core.wstk[p.toNat]'(by omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
      have hot_lt := (dedup_step_bin_info hinv1 hp_lt (by omega) hflag_c).2.1
      exfalso; rw [hcv_st] at hot_lt
      exact hc (by rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact hot_lt)
    · -- Exit of inner loop 1: `p = off + sz`
      have hp_eq : p.toNat = off.toNat + sz.toNat := by c0_bound
      have hinv1_done : DedupLoop1Inv c F_cur st l.toNat off.toNat sz.toNat
          (off.toNat + sz.toNat) q.toNat ul st1 := hp_eq ▸ hinv1
      have hpref1 := hinv1_done.2.2.2.2.2.2.2.2.1
      have hlm_inv1 := hinv1_done.2.2.2.2.2.2.2.2.2.2.1
      have hul1 := hinv1_done.2.2.2.2.2.2.2.2.2.2.2
      -- Inner loop 2: clear `lit_mark` for every binary watch in `wstk[off..q)`
      refine wp_loop_inv
        (fun (c0, ()) ml2 => ∃ st2 : FullState,
          AgreesExcept dedupLmMask st1 st2 ∧
          st2.core.lit_mark.length = 2 * c.max_vars ∧
          off.toNat ≤ c0.toNat ∧ c0.toNat ≤ q.toNat ∧
          (∀ x < 2 * c.max_vars, st2.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
            ∃ idx, c0.toNat ≤ idx ∧ idx < q.toNat ∧
              (st1.core.wstk[idx]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 ∧
              (st1.core.wstk[idx]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat = x) ∧
          (FullMem c st2 ⋆ R) ml2)
        (fun (c0, ()) _ => q.toNat - c0.toNat)
        (fun J2 hJ2 => by
          bf_fast
          exact hJ2 (off, ()) ml1 ⟨st1, .refl _ _, hlm1, Nat.le_refl _, hq_ge, hlm_inv1, hml1⟩)
        (fun J2 (c0, ()) ml2 ⟨st2, hag2, hlm2, hc0_ge, hc0_le, hlm_inv2, hml2⟩ ih2 => ?_)
      have hst2_eq := dedup_lm_reconstruct hag2
      have hws2 : st2.core.wstk = st1.core.wstk := by rw [hst2_eq]
      have hws2_len : st2.core.wstk.length = c.wcap := by rw [hws2]; exact hws1
      bf_fast
      · have hc0_lt : c0.toNat < q.toNat := by c0_bound
        have hc0_lt_ws : c0.toNat < st2.core.wstk.length := by rw [hws2]; omega
        have hc1_n : (c0 + 1#64).toNat = c0.toNat + 1 := by c0_bound
        have hbin_c : (st1.core.wstk[c0.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have helem : st2.core.wstk[c0.toNat]'hc0_lt_ws = st1.core.wstk[c0.toNat]'(by omega) := by
            simp [hws2]
          rw [← helem]; exact hc
        have hprops := denseWatchSliceOk_bin_word_props hpref1 c0.toNat hc0_ge (by omega) hbin_c
        have hot_lt_lm : (st2.core.wstk[c0.toNat]'hc0_lt_ws &&& 0x7FFFFFFF#32).toNat <
            st2.core.lit_mark.length := by
          have h1 := hprops.1
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
          simpa only [hws2, hlm2, hcv1] using Nat.lt_of_lt_of_le h1 (by omega)
        bf_fast
        refine ih2 _ _
          (by dsimp only; rw [show (c0 + 1 : BitVec 64) = c0 + 1#64 from rfl, hc1_n]; omega)
          ⟨_, by exact hag2.trans rfl, by simp [hlm2],
           by rw [show (c0 + 1 : BitVec 64) = c0 + 1#64 from rfl, hc1_n]; omega,
           by rw [show (c0 + 1 : BitVec 64) = c0 + 1#64 from rfl, hc1_n]; omega,
           fun x hx hne => ?_, hm⟩
        dsimp only at hne
        have hot64 : (BitVec.setWidth 64
            (st2.core.wstk[c0.toNat]'hc0_lt_ws &&& 0x7FFFFFFF)).toNat =
            (st2.core.wstk[c0.toNat]'hc0_lt_ws &&& 0x7FFFFFFF#32).toNat := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; rfl
        have hxne : x ≠ (st2.core.wstk[c0.toNat]'hc0_lt_ws &&& 0x7FFFFFFF#32).toNat := by
          intro heq; subst heq
          rw [← hot64, List.getElem?_set_self (by rw [hot64]; exact hot_lt_lm),
            Option.getD_some] at hne
          exact hne rfl
        rw [List.getElem?_set_ne (by rw [hot64]; exact Ne.symm hxne)] at hne
        obtain ⟨idx, hi1, hi2, hb, ho⟩ := hlm_inv2 x hx hne
        have hidx_ne : idx ≠ c0.toNat := by
          intro heq; subst heq
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at ho
          have helem : st2.core.wstk[c0.toNat]'hc0_lt_ws = st1.core.wstk[c0.toNat]'(by omega) := by
            simp [hws2]
          exact hxne (by rw [helem]; exact ho.symm)
        exact ⟨idx, by rw [show (c0 + 1 : BitVec 64) = c0 + 1#64 from rfl, hc1_n]; omega,
          hi2, hb, ho⟩
      · have hc0_lt : c0.toNat < q.toNat := by c0_bound
        have hc1_n : (c0 + 1#64).toNat = c0.toNat + 1 := by c0_bound
        refine ih2 _ _
          (by dsimp only; rw [show (c0 + 1 : BitVec 64) = c0 + 1#64 from rfl, hc1_n]; omega)
          ⟨st2, hag2, hlm2,
           by rw [show (c0 + 1 : BitVec 64) = c0 + 1#64 from rfl, hc1_n]; omega,
           by rw [show (c0 + 1 : BitVec 64) = c0 + 1#64 from rfl, hc1_n]; omega,
           fun x hx hne => ?_, hml2⟩
        obtain ⟨idx, hi1, hi2, hb, ho⟩ := hlm_inv2 x hx hne
        have hidx_ne : idx ≠ c0.toNat := by
          intro heq; subst heq
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hb
          have helem : st2.core.wstk[c0.toNat]'(by rw [hws2]; omega) =
              st1.core.wstk[c0.toNat]'(by omega) := by simp [hws2]
          rw [← helem] at hb; exact hb hc
        exact ⟨idx, by rw [show (c0 + 1 : BitVec 64) = c0 + 1#64 from rfl, hc1_n]; omega,
          hi2, hb, ho⟩
      · -- Exit of inner loop 2: `c0 = q`
        have hc0_eq : c0.toNat = q.toNat := by c0_bound
        have hlm2_clear : ∀ x < 2 * c.max_vars, st2.core.lit_mark[x]?.getD 0#8 = 0#8 := by
          intro x hx
          exact Classical.byContradiction fun hne => by
            obtain ⟨idx, hi1, hi2, _, _⟩ := hlm_inv2 x hx hne; omega
        -- Inner loop 3: fill `wstk[q..end)` with `0xFFFFFFFF#32`
        refine wp_loop_inv
          (fun (c1, ()) ml3 => ∃ st3 : FullState,
            AgreesExcept dedupWstkMask st2 st3 ∧
            st3.core.wstk.length = c.wcap ∧
            q.toNat ≤ c1.toNat ∧ c1.toNat ≤ off.toNat + sz.toNat ∧
            (∀ idx, idx < q.toNat ∨ off.toNat + sz.toNat ≤ idx →
              st3.core.wstk[idx]? = st1.core.wstk[idx]?) ∧
            (FullMem c st3 ⋆ R) ml3)
          (fun (c1, ()) _ => off.toNat + sz.toNat - c1.toNat)
          (fun J3 hJ3 => by
            bf_fast
            exact hJ3 (q, ()) ml2
              ⟨st2, .refl _ _, by rw [hws2]; exact hws1, Nat.le_refl _, by omega,
               fun _ _ => by rw [hws2], hml2⟩)
          (fun J3 (c1, ()) ml3 ⟨st3, hag3, hws3, hc1_ge, hc1_le, hws3_eq, hml3⟩ ih3 => ?_)
        have hst3_eq := dedup_wstk_reconstruct hag3
        bf_fast
        · have hc1_lt : c1.toNat < off.toNat + sz.toNat := by c0_bound
          have hc1_n : (c1 + 1#64).toNat = c1.toNat + 1 := by c0_bound
          refine ih3 _ _
            (by dsimp only; rw [show (c1 + 1 : BitVec 64) = c1 + 1#64 from rfl, hc1_n]; omega)
            ⟨_, by exact hag3.trans rfl, by simp [hws3],
             by rw [show (c1 + 1 : BitVec 64) = c1 + 1#64 from rfl, hc1_n]; omega,
             by rw [show (c1 + 1 : BitVec 64) = c1 + 1#64 from rfl, hc1_n]; omega,
             fun idx hidx => by
               dsimp only; rw [List.getElem?_set_ne (by omega)]; exact hws3_eq idx hidx,
             hm⟩
        · -- Exit of inner loop 3: finalize slice & optional `full_add_unit`
          have hwv_lt3 : ((l <<< (1 : Nat)) + 1#64).toNat < st3.core.wvec.length := by
            rw [hst3_eq, hst2_eq, hst1_eq]; dsimp only; omega
          have hqsub_eq : BitVec.setWidth 32 (q - off) = BitVec.ofNat 32 (q.toNat - off.toNat) := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_setWidth, BitVec.toNat_sub_of_le hq_ge, BitVec.toNat_ofNat]
          have ⟨hw4, hst4_dense, hcv4, har4, hal4, hfuel4⟩ :=
            dedup_finalize_dense hst hw hl_lt hoff_eq hsz_eq hinv1_done hag2 hlm2 hlm2_clear
              hag3 hws3 hws3_eq (st3.core.wusable + ((off + sz) - q))
          have hl1_n : (l + 1#64).toNat = l.toNat + 1 := by c0_bound
          have hl32_n : (BitVec.setWidth 32 l).toNat = l.toNat := by
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
          have hst4_rw : ({ st3 with core := { st3.core with
              wvec := st3.core.wvec.set ((l <<< (1 : Nat)) + 1).toNat
                (BitVec.setWidth 32 (q - off))
              wusable := st3.core.wusable + ((off + sz) - q) } } : FullState) =
            { st3 with core := { st3.core with
              wvec := st3.core.wvec.set (2 * l.toNat + 1) (BitVec.ofNat 32 (q.toNat - off.toNat))
              wusable := st3.core.wusable + ((off + sz) - q) } } := by
            rw [show (l <<< (1 : Nat) + 1 : BitVec 64) = l <<< (1 : Nat) + 1#64 from rfl,
              hsz_idx, hqsub_eq]
          bf_fast
          · -- `ul = true`: call `full_add_unit(h, (u32)l)`
            c0_call hAddUnit
            refine ⟨c, F0, F_cur, _, R, rfl, hst4_dense.1.lengths, hw4,
              fun _ => by rw [hl32_n]; exact hul1 hc, by rw [← hst4_rw]; exact hm,
              fun ok5 vals5 flags5 lvl5 rsns5 trl5 tp5 te5 prop5 cl5 unass5 unfl5 inc5
                  ph5 ta5 ba5 pt5 pb5 hp5 ps5 hl5 qsi5 qss5 m5 hlen5 hw5 hcl5 hfalse5 _ hm5 => ?_⟩
            have hst5_dense := fullDenseInv_of_addUnit hst4_dense hlen5 hw5 hcl5
              rfl rfl rfl rfl rfl rfl rfl
            bf_fast
            · refine ih _ _
                (by dsimp only; rw [show (l + 1 : BitVec 64) = l + 1#64 from rfl, hl1_n]; omega)
                ⟨_, by rw [show (l + 1 : BitVec 64) = l + 1#64 from rfl, hl1_n]; omega,
                 hst5_dense, hw5, hcv4.trans hcv_st, har4.trans har_st, hal4.trans hal_st,
                 hfuel4.trans hfuel_st, hm5⟩
            · exact hQ false _ m5 ⟨hlen5, hw5, hst5_dense.2⟩ (hcv4.trans hcv_st)
                (hfuel4.trans hfuel_st)
                (fun _ => (hfalse5 (by rw [hl32_n, hcv4]; exact hl_lt) hc).1) hm5
          · -- `ul = false`
            refine ih _ _
              (by dsimp only; rw [show (l + 1 : BitVec 64) = l + 1#64 from rfl, hl1_n]; omega)
              ⟨_, by rw [show (l + 1 : BitVec 64) = l + 1#64 from rfl, hl1_n]; omega,
               hst4_dense, hw4, hcv4.trans hcv_st, har4.trans har_st, hal4.trans hal_st,
               hfuel4.trans hfuel_st, by rw [← hst4_rw]; exact hm⟩
  · exact hQ true st ml ⟨hst.1.lengths, hw, hst.2⟩ hcv_st hfuel_st (by simp) hml

/-! ## 3. `full_init_fresh_var_wp` -/

private theorem initFreshVar_post {c : FullCfg} {s s' : FullState} {fv : BitVec 32}
    {R : Mem 64 → Prop} {Q : Post []} {m' : Mem 64}
    (hfv_lt : fv.toNat < s.core.cur_vars) (hclen : s.core.LengthsOk c)
    (hlen' : s'.LengthsOk c) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hcore : s'.core =
      { s.core with
        wvec := (((s.core.wvec.set (4 * fv.toNat) 0#32).set (4 * fv.toNat + 1) 0#32).set
          (4 * fv.toNat + 2) 0#32).set (4 * fv.toNat + 3) 0#32
        vals := (s.core.vals.set (2 * fv.toNat) 0#8).set (2 * fv.toNat + 1) 0#8
        mrk := s.core.mrk.set fv.toNat 0#8, lvl := s.core.lvl.set fv.toNat 0#32
        rsns := s.core.rsns.set fv.toNat 0xFFFFFFFF#32, flags := s.core.flags.set fv.toNat 1049#32
        unassigned := s.core.unassigned + 1#64 })
    (hext_pres : FullExtScratchPres s s') (hsb : s'.scratch.scratch_buf = s.scratch.scratch_buf)
    (hm' : (FullMem c s' ⋆ R) m')
    (hQ : ∀ vals' mrk' flags' lvl' rsns' wvec' unass' sc' m',
      let s1 : FullState :=
        { s with
          core := { s.core with vals := vals', mrk := mrk', flags := flags', lvl := lvl',
                                rsns := rsns', wvec := wvec', unassigned := unass' }
          scratch := sc' }
      s1.LengthsOk c → FullExtScratchPres s s1 → sc'.scratch_buf = s.scratch.scratch_buf →
      vals'[2 * fv.toNat]?.getD 1#8 = 0#8 → vals'[2 * fv.toNat + 1]?.getD 1#8 = 0#8 →
      (∀ l < 2 * c.max_vars, l / 2 ≠ fv.toNat → vals'[l]? = s.core.vals[l]?) →
      mrk'[fv.toNat]?.getD 1#8 = 0#8 →
      (∀ v < c.max_vars, v ≠ fv.toNat → mrk'[v]? = s.core.mrk[v]?) →
      lvl'[fv.toNat]?.getD 1#32 = 0#32 →
      (∀ v < c.max_vars, v ≠ fv.toNat → lvl'[v]? = s.core.lvl[v]?) →
      rsns'[fv.toNat]?.getD 0#32 = 0xFFFFFFFF#32 →
      (∀ v < c.max_vars, v ≠ fv.toNat → rsns'[v]? = s.core.rsns[v]?) →
      (∀ k < 4, wvec'[4 * fv.toNat + k]?.getD 1#32 = 0#32) →
      (∀ i < 4 * c.max_vars, i / 4 ≠ fv.toNat → wvec'[i]? = s.core.wvec[i]?) →
      (FullMem c s1 ⋆ R) m' → Q () m') : Q () m' := by
  have hs'_eq : s' = { s with core := s'.core, scratch := s'.scratch } := by cases s'; rfl
  exact hQ _ _ _ _ _ _ _ s'.scratch m'
    (by rw [← hcore, ← hs'_eq]; exact hlen') hext_pres hsb
    (by rw [List.getElem?_set_ne (by omega),
          List.getElem?_set_self (by rw [hclen.vals_len]; omega)]; rfl)
    (by rw [List.getElem?_set_self (by simp [hclen.vals_len]; omega)]; rfl)
    (fun l _ _ => by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
    (by rw [List.getElem?_set_self (by rw [hclen.mrk_len]; omega)]; rfl)
    (fun v _ hv => List.getElem?_set_ne (Ne.symm hv))
    (by rw [List.getElem?_set_self (by rw [hclen.lvl_len]; omega)]; rfl)
    (fun v _ hv => List.getElem?_set_ne (Ne.symm hv))
    (by rw [List.getElem?_set_self (by rw [hclen.rsns_len]; omega)]; rfl)
    (fun v _ hv => List.getElem?_set_ne (Ne.symm hv))
    (fun k hk => by
      rcases k with _ | _ | _ | _ | k
      · rw [show 4 * fv.toNat + 0 = 4 * fv.toNat from rfl, List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_self (by simp [hclen.wvec_len]; omega)]; rfl
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_self (by simp [hclen.wvec_len]; omega)]; rfl
      · rw [List.getElem?_set_ne (by omega),
          List.getElem?_set_self (by simp [hclen.wvec_len]; omega)]; rfl
      · rw [List.getElem?_set_self (by simp [hclen.wvec_len]; omega)]; rfl
      · omega)
    (fun i _ hi => by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
    (by rw [← hcore, ← hs'_eq]; exact hm')

theorem full_init_fresh_var_wp (Γ : Env)
    (hHeapPush : ∀ args m Q X, fullHeapPushSpec args m Q X →
      Γ "full_heap_push" [i64, i32] [] args m Q X) :
    ∀ args m Q X, fullInitFreshVarSpec args m Q X →
      Func.wp Γ full_init_fresh_var_body args m Q X := by
  rintro ⟨h, fv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hslen, hfv_lt, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hclen := hslen.core_ok; have hsc := hslen.scratch_ok; have hcv_le := hclen.cur_vars_le
  have hwv_len := hclen.wvec_len; have hvals_len := hclen.vals_len; have hmrk_len := hclen.mrk_len
  have hlvl_len := hclen.lvl_len; have hrsns_len := hclen.rsns_len; have hfl_len := hclen.flags_len
  have hpos_len := hsc.pos_len; have hph_len := hsc.phases_len; have hqp_len := hsc.q_prev_len
  have hqn_len := hsc.q_next_len; have hqs_len := hsc.q_stamp_len
  have hfv64 : (BitVec.setWidth 64 fv).toNat = fv.toNat := by c0_bound
  have hwb0 : (BitVec.setWidth 64 fv <<< (2 : Nat)).toNat = 4 * fv.toNat := by c0_bound
  have hwb1 : ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 1).toNat = 4 * fv.toNat + 1 := by
    change ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 1#64).toNat = _; c0_bound
  have hwb2 : ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 2).toNat = 4 * fv.toNat + 2 := by
    change ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 2#64).toNat = _; c0_bound
  have hwb3 : ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 3).toNat = 4 * fv.toNat + 3 := by
    change ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 3#64).toNat = _; c0_bound
  have hv2 : (BitVec.setWidth 64 fv <<< (1 : Nat)).toNat = 2 * fv.toNat := by c0_bound
  have hv2p1 : ((BitVec.setWidth 64 fv <<< (1 : Nat)) ||| 1).toNat = 2 * fv.toNat + 1 := by
    change ((BitVec.setWidth 64 fv <<< (1 : Nat)) ||| 1#64).toNat = _
    rw [FullBvaFwdTactics.bv64_or1_of_even (by rw [hv2]; omega), hv2]
  have hv2p1_lt : ((BitVec.setWidth 64 fv <<< (1 : Nat)) ||| 1).toNat < s.core.vals.length := by
    rw [hv2p1, hvals_len]; omega
  have hfl_or : (((1 : BitVec 32) ||| 8) ||| 16 ||| 1024) = 1049#32 := by decide
  unfold Func.wp full_init_fresh_var_body; dsimp only; bf_fast
  · c0_call hHeapPush
    refine ⟨c, _, R, rfl, ?_, hm, fun _ s' m' hcore_pres hlen' hprobe_pres hm' => ?_⟩
    · refine ⟨{ hclen with
          wvec_len := (by simp [hwv_len]), vals_len := (by simp [hvals_len]),
          mrk_len := (by simp [hmrk_len]), lvl_len := (by simp [hlvl_len]),
          rsns_len := (by simp [hrsns_len]), flags_len := (by simp [hfl_len]) },
        { hsc with
          phases_len := (by simp [hph_len]), pos_len := (by simp [hpos_len]),
          q_prev_len := (by simp [hqp_len]), q_next_len := (by simp [hqn_len]),
          q_stamp_len := (by simp [hqs_len]) }⟩
    · dsimp only [fullSafetySlice] at hm' hlen'; bf_fast
      have hpe : s'.core = _ := fullCoreState_agrees_with_scratch hcore_pres
      rw [hfv64, hwb0, hwb1, hwb2, hwb3, hv2, hv2p1, hfl_or] at hpe
      exact initFreshVar_post hfv_lt hclen hlen' hcv_le hpe hprobe_pres.1
        hprobe_pres.2.2.2.2.1 hm' hQ
  · refine initFreshVar_post hfv_lt hclen ?_ hcv_le ?_ ?_ ?_ hm hQ
    · refine ⟨
        { hclen with
          wvec_len := (by simp [hwv_len]), vals_len := (by simp [hvals_len]),
          mrk_len := (by simp [hmrk_len]), lvl_len := (by simp [hlvl_len]),
          rsns_len := (by simp [hrsns_len]), flags_len := (by simp [hfl_len]) },
        { hsc with
          phases_len := (by simp [hph_len]), pos_len := (by simp [hpos_len]),
          q_prev_len := (by simp [hqp_len]), q_next_len := (by simp [hqn_len]),
          q_stamp_len := (by simp [hqs_len]) }⟩
    · try dsimp only; rw [hfv64, hwb0, hwb1, hwb2, hwb3, hv2, hv2p1, hfl_or]; rfl
    all_goals first | exact ⟨rfl, rfl⟩ | rfl
  · c0_call hHeapPush
    refine ⟨c, _, R, rfl, ?_, hm, fun _ s' m' hcore_pres hlen' hprobe_pres hm' => ?_⟩
    · refine ⟨
        { hclen with
          wvec_len := (by simp [hwv_len]), vals_len := (by simp [hvals_len]),
          mrk_len := (by simp [hmrk_len]), lvl_len := (by simp [hlvl_len]),
          rsns_len := (by simp [hrsns_len]), flags_len := (by simp [hfl_len]) },
        { hsc with
          phases_len := (by simp [hph_len]), pos_len := (by simp [hpos_len]),
          q_prev_len := (by simp [hqp_len]), q_next_len := (by simp [hqn_len]),
          q_stamp_len := (by simp [hqs_len]) }⟩
    · dsimp only [fullSafetySlice] at hm' hlen'; bf_fast
      have hpe : s'.core = _ := fullCoreState_agrees_with_scratch hcore_pres
      rw [hfv64, hwb0, hwb1, hwb2, hwb3, hv2, hv2p1, hfl_or] at hpe
      exact initFreshVar_post hfv_lt hclen hlen' hcv_le hpe hprobe_pres.1
        hprobe_pres.2.2.2.2.1 hm' hQ
  · refine initFreshVar_post hfv_lt hclen ?_ hcv_le ?_ ?_ ?_ hm hQ
    · refine ⟨
        { hclen with
          wvec_len := (by simp [hwv_len]), vals_len := (by simp [hvals_len]),
          mrk_len := (by simp [hmrk_len]), lvl_len := (by simp [hlvl_len]),
          rsns_len := (by simp [hrsns_len]), flags_len := (by simp [hfl_len]) },
        { hsc with
          phases_len := (by simp [hph_len]), pos_len := (by simp [hpos_len]),
          q_prev_len := (by simp [hqp_len]), q_next_len := (by simp [hqn_len]),
          q_stamp_len := (by simp [hqs_len]) }⟩
    · try dsimp only; rw [hfv64, hwb0, hwb1, hwb2, hwb3, hv2, hv2p1, hfl_or]; rfl
    all_goals first | exact ⟨rfl, rfl⟩ | rfl

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
