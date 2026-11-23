module

public import LeanQbe.T.Examples.Kissat.PlainSearchLemmas1

/-!
# Kissat `D-Plain` Lucky-Assignment `Func.wp` Proofs (`Stage 3`)

Proves parametric `(Γ : Env)` `Func.wp` contracts for the Stage-3 lucky-assignment functions
in `LeanQbe/T/Examples/Kissat/Plain.lean` matching `plainSpecTable`:
1. `plain_lucky_scan_wp` (`plainLuckyScanSpec`)
2. `plain_lucky_wp` (`plainLuckySpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

section LuckyProofs

open PlainTopTactics
open scoped PlainTopTactics

/-! ## 1. `plain_lucky_scan_wp` -/

private theorem plainState_eq_of_luckyScan {s s' : PlainState}
    (hd1 : s'.d_cur = s.d_cur) (hd2 : s'.d_val = s.d_val) (hpr : s'.probing = s.probing) :
    { s with
      vals := s'.vals, lvl := s'.lvl, rsns := s'.rsns, trl := s'.trl, trail_pos := s'.trail_pos,
      trail_end := s'.trail_end, propagated := s'.propagated, cur_level := s'.cur_level,
      tmp_cnt := s'.tmp_cnt, tmp_len := s'.tmp_len, mrk := s'.mrk, tmp := s'.tmp,
      wvec := s'.wvec, arena := s'.arena, arena_len := s'.arena_len, wstk := s'.wstk,
      wlen := s'.wlen, wusable := s'.wusable, arena_garbage := s'.arena_garbage,
      first_reducible := s'.first_reducible, num_irred := s'.num_irred,
      num_redundant := s'.num_redundant, num_binary := s'.num_binary,
      unflushed := s'.unflushed, fuel := s'.fuel, confl_type := s'.confl_type,
      confl_ref := s'.confl_ref, confl_lit0 := s'.confl_lit0, confl_lit1 := s'.confl_lit1,
      oom := s'.oom, min_stk := s'.min_stk, min_clr := s'.min_clr,
      min_clr_len := s'.min_clr_len, min_clr_full := s'.min_clr_full, heur := s'.heur } = s' := by
  cases s; cases s'; simp_all

private theorem luckyScan_ret {c : PlainCfg} {F0 : CNF Nat} {s s' : PlainState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {r : BitVec 64} {m' : Mem 64}
    (hQ : ∀ r vals' lvl' rsns' trl' tp' te' prop' cl' tc' tl' mrk' tmp' wvec' arena' alen' wstk'
      wlen' wu' ag' fred' ni' nr' nb' unfl' fuel' ctype' cref' c0' c1' oom' mstk' mclr' mcl'
      mcf' heur' m',
      let s' : PlainState := { s with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', cur_level := cl', tmp_cnt := tc', tmp_len := tl',
        mrk := mrk', tmp := tmp', wvec := wvec', arena := arena', arena_len := alen',
        wstk := wstk', wlen := wlen', wusable := wu', arena_garbage := ag',
        first_reducible := fred', num_irred := ni', num_redundant := nr', num_binary := nb',
        unflushed := unfl', fuel := fuel', confl_type := ctype', confl_ref := cref',
        confl_lit0 := c0', confl_lit1 := c1', oom := oom', min_stk := mstk', min_clr := mclr',
        min_clr_len := mcl', min_clr_full := mcf', heur := heur' }
      s'.LengthsOk c → (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (r = 10#64 → PlainInv c F0 s') →
      (r = 0#64 → PlainInv c F0 s') → (PlainMem c s' ⋆ R) m' → Q (r, ()) m')
    (hd1 : s'.d_cur = s.d_cur) (hd2 : s'.d_val = s.d_val) (hpr : s'.probing = s.probing)
    (hlen' : s'.LengthsOk c) (hdom : r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64)
    (h20 : r = 20#64 → F0.Unsat) (h10 : r = 10#64 → PlainInv c F0 s')
    (h0 : r = 0#64 → PlainInv c F0 s') (hm' : (PlainMem c s' ⋆ R) m') : Q (r, ()) m' := by
  have heq := plainState_eq_of_luckyScan hd1 hd2 hpr
  exact hQ r s'.vals s'.lvl s'.rsns s'.trl s'.trail_pos s'.trail_end s'.propagated s'.cur_level
    s'.tmp_cnt s'.tmp_len s'.mrk s'.tmp s'.wvec s'.arena s'.arena_len s'.wstk s'.wlen
    s'.wusable s'.arena_garbage s'.first_reducible s'.num_irred s'.num_redundant s'.num_binary
    s'.unflushed s'.fuel s'.confl_type s'.confl_ref s'.confl_lit0 s'.confl_lit1 s'.oom
    s'.min_stk s'.min_clr s'.min_clr_len s'.min_clr_full s'.heur m'
    (heq.symm ▸ hlen') hdom h20 (fun h => heq.symm ▸ h10 h) (fun h => heq.symm ▸ h0 h)
    (heq.symm ▸ hm')

/-- After assigning unassigned `lit` at `sL.cur_level + 1`, propagating to `sP`, and backtracking
to `sL.cur_level`, the flipped literal `lit ^^^ 1#32` is unassigned in `sB`. -/
private theorem lucky_flip_unassigned {c : PlainCfg} {F0 : CNF Nat} {sL sA sP sB : PlainState}
    {lit : BitVec 32}
    (hcoreL : PlainCoreInv c F0 sL) (hcoreB : PlainCoreInv c F0 sB)
    (hlit : lit.toNat < 2 * c.mv) (hunL : sL.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hA_te : sA.trail_end = sL.trail_end + 1) (hA_cl : sA.cur_level = sL.cur_level + 1)
    (hA_trl : sA.trl = sL.trl.set sL.trail_end lit)
    (hA_lvl : sA.lvl = sL.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 (sL.cur_level + 1)))
    (_hP_te : sA.trail_end ≤ sP.trail_end)
    (hP_trl : ∀ i < sA.trail_end, sP.trl[i]? = sA.trl[i]?)
    (hP_lvl_old : ∀ i < sA.trail_end,
      sP.lvl[(sA.trl[i]?.getD 0#32).toNat / 2]? = sA.lvl[(sA.trl[i]?.getD 0#32).toNat / 2]?)
    (hP_lvl_new : ∀ i, sA.trail_end ≤ i → i < sP.trail_end →
      (sP.lvl[(sP.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = sA.cur_level)
    (hB_trl : sB.trl = sP.trl) (hB_te : sB.trail_end ≤ sP.trail_end)
    (hiff : ∀ i < sP.trail_end,
      ((sP.lvl[(sP.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ sL.cur_level ↔
        i < sB.trail_end)) :
    sB.vals[(lit ^^^ 1#32).toNat]?.getD 0#8 = 0#8 := by
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hte_lt : sL.trail_end < c.mv := hcoreL.trail_end_lt_of_unassigned hlit hunL
  have hcl_le : sL.cur_level ≤ sL.trail_end := hcoreL.cur_level_le
  have hcl1_lt : sL.cur_level + 1 < 2 ^ 32 := by omega
  have hxor : (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 := by
    rw [BitVec.toNat_xor]; rfl
  have hnlit_lt : (lit ^^^ 1#32).toNat < 2 * c.mv := by
    rw [hxor]; exact litNeg_lt_two_mul hlit
  have hnvar : (lit ^^^ 1#32).toNat / 2 = lit.toNat / 2 := by
    rw [hxor]; exact litVar_litNeg lit.toNat
  rw [hcoreB.vals_zero_iff hnlit_lt, hnvar]
  intro i hi
  have hli : (sP.lvl[(sP.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ sL.cur_level :=
    (hiff i (by omega)).mpr hi
  have hi_lt_sL : i < sL.trail_end := by
    cases Nat.lt_or_ge i sL.trail_end with
    | inl hlt => exact hlt
    | inr hge =>
      by_cases he : i = sL.trail_end
      · subst he
        have ht_at : sA.trl[sL.trail_end]? = some lit := by
          rw [hA_trl, List.getElem?_set_self (by rw [hcoreL.lengths.trl_len]; omega)]
        have htp : sP.trl[sL.trail_end]? = some lit := (hP_trl sL.trail_end (by omega)).trans ht_at
        have hlp : sP.lvl[lit.toNat / 2]? = sA.lvl[lit.toNat / 2]? := by
          have h := hP_lvl_old sL.trail_end (by omega)
          simpa [ht_at] using h
        have hla : sA.lvl[lit.toNat / 2]? = some (BitVec.ofNat 32 (sL.cur_level + 1)) := by
          rw [hA_lvl, List.getElem?_set_self (by rw [hcoreL.lengths.lvl_len]; omega)]
        rw [htp] at hli; simp only [Option.getD_some, hlp, hla, bv32_ofNat_toNat hcl1_lt] at hli
        omega
      · have hgeA : sA.trail_end ≤ i := by omega
        have hnew := hP_lvl_new i hgeA (by omega)
        omega
  have ht_eq : sB.trl[i]? = sL.trl[i]? := by
    rw [hB_trl, hP_trl i (by omega), hA_trl, List.getElem?_set_ne (by omega)]
  rw [ht_eq]
  exact (hcoreL.vals_zero_iff hlit).mp hunL i hi_lt_sL

theorem plain_lucky_scan_wp (Γ : Env)
    (hBt : ∀ args m Q X, plainBacktrackSpec args m Q X →
      Γ "plain_backtrack" [i64, i64] [] args m Q X)
    (hAssign : ∀ args m Q X, plainAssignSpec args m Q X →
      Γ "plain_assign" [i64, i32, i32] [] args m Q X)
    (hProp : ∀ args m Q X, plainPropagateSpec args m Q X →
      Γ "plain_propagate" [i64] [i64] args m Q X)
    (hAnalyze : ∀ args m Q X, plainAnalyzeSpec args m Q X →
      Γ "plain_analyze" [i64] [i64] args m Q X) :
    ∀ args m Q X, plainLuckyScanSpec args m Q X →
      Func.wp Γ plain_lucky_scan_body args m Q X := by
  rintro ⟨h, pos_mode, fwd, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmv := c.hmv; unfold dimacsBound at hmv
  unfold Func.wp plain_lucky_scan_body; wp_unfold
  refine ⟨_, load_arena_mv hm, _, load_arena_values hm, ?_⟩
  refine wp_loop_inv
    (fun (iv, ()) ml => ∃ sL : PlainState,
      sL.d_cur = s.d_cur ∧ sL.d_val = s.d_val ∧ sL.probing = s.probing ∧
      iv.toNat ≤ c.mv ∧ PlainInv c F0 sL ∧ (PlainMem c sL ⋆ R) ml)
    (fun (iv, ()) _ => c.mv - iv.toNat) ?_ ?_
  · intro J hJ; wp_unfold
    exact hJ (0#64, ()) m ⟨s, rfl, rfl, rfl, Nat.zero_le _, hinv, hm⟩
  · rintro J ⟨iv, ⟨⟩⟩ ml ⟨sL, hd1, hd2, hpr, hile, hinvL, hml⟩ ih
    wp_unfold
    refine ⟨fun hilt_b => ?_, fun _ =>
      luckyScan_ret hQ hd1 hd2 hpr hinvL.core.lengths (Or.inr (Or.inr (Or.inl rfl)))
        (fun h => by cases h) (fun _ => hinvL) (fun h => by cases h) hml⟩
    have hilt : iv.toNat < c.mv := by
      change iv.ult (BitVec.ofNat 64 c.mv) = true at hilt_b
      simp only [BitVec.ult, decide_eq_true_eq] at hilt_b; bv_omega
    have hi1 : (iv + 1#64).toNat = iv.toNat + 1 := by bv_omega
    -- v = fwd ? i : (mv - 1ULL - i)
    refine wp_join_group (fun (vv, ()) m_v => m_v = ml ∧ vv.toNat < c.mv) ?_ ?_
    · rintro _ ⟨vv, ⟨⟩⟩ m_v ⟨hm_v, hvlt⟩; subst m_v
      -- if (vals[v << 1] == 0) { ... } i = i + 1ULL;
      refine wp_join_group
        (fun (() : Tup Val []) m_if => ∃ sN : PlainState,
          sN.d_cur = s.d_cur ∧ sN.d_val = s.d_val ∧ sN.probing = s.probing ∧
          PlainInv c F0 sN ∧ (PlainMem c sN ⋆ R) m_if)
        (fun _ ⟨⟩ m_if ⟨sN, hd1N, hd2N, hprN, hinvN, hmN⟩ => by
          wp_unfold
          exact ih (iv + 1#64, ()) m_if (by dsimp; omega)
            ⟨sN, hd1N, hd2N, hprN, by omega, hinvN, hmN⟩)
        (fun Jif hJif => by
          wp_unfold
          have h2v : (vv <<< 1).toNat = 2 * vv.toNat := bv64_shl1_toNat (by omega)
          have hvl : sL.vals.length = 2 * c.mv := hinvL.core.lengths.vals_len
          refine ⟨_, c0_load_arena_vals (i := vv <<< 1) (by omega) hml, ?_⟩
          refine ⟨fun hz => ?_, fun _ => hJif () ml ⟨sL, hd1, hd2, hpr, hinvL, hml⟩⟩
          have hun : sL.vals[2 * vv.toNat]?.getD 0#8 = 0#8 := by
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            simpa [h2v] using bv8_sext32_eq_zero hz
          refine ⟨_, load_arena_fuel hml, ?_⟩
          refine ⟨fun _ => ?_, fun _ => ?_⟩
          · -- fuel == 0ULL
            c0_call hBt
            refine ⟨c, sL, R, rfl, hinvL.core.lengths, hinvL.core.trail_lits_lt, hml, ?_⟩
            intro valsB lvlB rsnsB teB propB heurB mB sB hlenB _ _ _ _ _ hmB
            exact luckyScan_ret hQ (s' := sB) hd1 hd2 hpr hlenB (Or.inr (Or.inl rfl))
              (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hmB
          · -- fuel != 0ULL
            refine ⟨_, load_arena_fuel hml, ?_⟩
            obtain ⟨hok_f, hml1⟩ := store_arena_fuel (sL.fuel - 1) hml
            refine ⟨hok_f, ?_⟩
            let sF : PlainState := { sL with fuel := sL.fuel - 1 }
            have hcoreF : PlainCoreInv c F0 sF := plainCoreInv_with_fuel hinvL.core (sL.fuel - 1)
            change (PlainMem c sF ⋆ R) _ at hml1
            generalize hmF_eq : storeMem ml i64 (c.hdr + 168) (sL.fuel - 1) = mF at hml1 ⊢
            -- lit = pos_mode ? (u32)(v << 1) : ((u32)(v << 1) | 1u)
            refine wp_join_group
              (fun (lit, ()) m_l => m_l = mF ∧ lit.toNat < 2 * c.mv ∧ lit.toNat / 2 = vv.toNat)
              ?_ ?_
            · rintro _ ⟨lit, ⟨⟩⟩ m_l ⟨hm_l, hlit_lt, hlit_v⟩; subst m_l
              have hun_lit : sL.vals[lit.toNat]?.getD 0#8 = 0#8 := by
                rw [hinvL.core.vals_zero_iff hlit_lt, hlit_v]
                have h0' := (hinvL.core.vals_zero_iff
                  (by omega : 2 * vv.toNat < 2 * c.mv)).mp hun
                simpa using h0'
              have hte_lt : sL.trail_end < c.mv :=
                hinvL.core.trail_end_lt_of_unassigned hlit_lt hun_lit
              have hcl_le : sL.cur_level ≤ sL.trail_end := hinvL.core.cur_level_le
              wp_unfold
              refine ⟨_, load_arena_cur_level hml1, ?_⟩
              dsimp only [sF]
              rw [show BitVec.ofNat 64 sL.cur_level + 1 = BitVec.ofNat 64 (sL.cur_level + 1) from by
                rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]]
              obtain ⟨hok_cl, hml2⟩ := store_arena_cur_level (sL.cur_level + 1) (by omega) hml1
              refine ⟨hok_cl, ?_⟩
              let s_pre : PlainState := { sF with cur_level := sL.cur_level + 1 }
              change (PlainMem c s_pre ⋆ R) _ at hml2
              c0_call hAssign
              refine ⟨c, s_pre, R, rfl, { hcoreF.lengths with }, by dsimp [s_pre]; omega, hml2, ?_⟩
              have hnot_oob : ¬ (c.mv ≤ lit.toNat / 2 ∨ c.mv ≤ s_pre.trail_end) := by
                dsimp [s_pre, sF]; omega
              simp only [hnot_oob, ↓reduceIte]
              intro phases' mA hph' _ hmA
              have hcl_ne0 : s_pre.cur_level ≠ 0 := by dsimp [s_pre]; omega
              simp only [hcl_ne0, ↓reduceIte] at hmA
              have hcoreA := decide_assign_preserves_core hcoreF hlit_lt hph' hun_lit
              let sA : PlainState := { s_pre with
                vals := (s_pre.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                lvl := s_pre.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 s_pre.cur_level)
                rsns := s_pre.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32
                trl := s_pre.trl.set s_pre.trail_end lit
                trail_pos := s_pre.trail_pos.set (lit.toNat / 2) (BitVec.ofNat 32 s_pre.trail_end)
                trail_end := s_pre.trail_end + 1
                heur := { s_pre.heur with phases := phases' } }
              change PlainCoreInv c F0 sA at hcoreA
              change (PlainMem c sA ⋆ R) mA at hmA
              c0_call hProp
              refine ⟨c, F0, sA, R, rfl, hcoreA, hmA, ?_⟩
              intro pr valsP lvlP rsnsP trlP tpP teP propP unflP wvecP arenaP wstkP wlenP wuP
                fuelP ctypeP crefP c0P c1P oomP heurP mP sP hcoreP hteA_le _ _ htrlP hlvlP_old
                hlvlP_new _ _ hpr1 _ _ hmP
              wp_unfold
              refine ⟨fun _ => ?_, fun _ => ?_⟩
              · -- pr == 2ULL
                c0_call hBt
                refine ⟨c, sP, R, rfl, hcoreP.lengths, hcoreP.trail_lits_lt, hmP, ?_⟩
                intro valsB lvlB rsnsB teB propB heurB mB sB hlenB _ _ _ _ _ hmB
                exact luckyScan_ret hQ (s' := sB) hd1 hd2 hpr hlenB (Or.inr (Or.inl rfl))
                  (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hmB
              · refine wp_join_group
                  (fun (() : Tup Val []) m_r => ∃ sN : PlainState,
                    sN.d_cur = s.d_cur ∧ sN.d_val = s.d_val ∧ sN.probing = s.probing ∧
                    PlainInv c F0 sN ∧ (PlainMem c sN ⋆ R) m_r)
                  (fun _ ⟨⟩ m_r hN => hJif () m_r hN)
                  (fun J1 hJ1 => by
                    wp_unfold
                    refine ⟨fun hpr1_eq => ?_, fun _ =>
                      hJ1 () mP ⟨sP, hd1, hd2, hpr, ⟨hcoreP, hinvL.marks⟩, hmP⟩⟩
                    obtain ⟨_, _, hconflP⟩ := hpr1 hpr1_eq
                    refine wp_join_group
                      (fun (() : Tup Val []) m_c => ∃ sN : PlainState,
                        sN.d_cur = s.d_cur ∧ sN.d_val = s.d_val ∧ sN.probing = s.probing ∧
                        PlainInv c F0 sN ∧ (PlainMem c sN ⋆ R) m_c)
                      (fun _ ⟨⟩ m_c hN => hJ1 () m_c hN)
                      (fun J2 hJ2 => by
                        wp_unfold
                        refine ⟨_, load_arena_cur_level hmP, ?_⟩
                        have hclP : sP.cur_level = sL.cur_level + 1 := rfl
                        rw [hclP, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
                          bv_ult_eq (by omega) (by omega)]
                        simp only [decide_eq_true_eq, decide_eq_false_iff_not]
                        refine ⟨fun hcl_gt1 => ?_, fun hcl_le1 => ?_⟩
                        · -- h->cur_level > 1ULL: backtrack to cur_level - 1 and try lit ^ 1
                          refine ⟨_, load_arena_cur_level hmP, ?_⟩
                          have hsub_cl :
                              BitVec.ofNat 64 sP.cur_level - 1#64 =
                                BitVec.ofNat 64 sL.cur_level := by
                            rw [hclP, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
                              bv_sub_ofNat (by omega) (by omega)]
                            simp
                          c0_call hBt
                          refine ⟨c, sP, R, rfl, hcoreP.lengths, hcoreP.trail_lits_lt, hmP, ?_⟩
                          intro valsB lvlB rsnsB teB propB heurB mB sB _ hteB_le _ _ _ hcoreB_fn hmB
                          have hbt_arg :
                              (BitVec.ofNat 64 sP.cur_level - 1#64).toNat = sL.cur_level := by
                            rw [hsub_cl, bv64_ofNat_toNat (by omega)]
                          obtain ⟨hcoreB, hiffB⟩ :=
                            hcoreB_fn F0 hcoreP (by rw [hbt_arg, hclP]; omega)
                          rw [hbt_arg] at hiffB
                          have hun_flip : sB.vals[(lit ^^^ 1#32).toNat]?.getD 0#8 = 0#8 :=
                            lucky_flip_unassigned (sA := sA) (sP := sP) hinvL.core hcoreB hlit_lt
                              hun_lit rfl rfl rfl rfl hteA_le htrlP hlvlP_old hlvlP_new rfl hteB_le
                              hiffB
                          wp_unfold
                          refine ⟨_, load_arena_fuel hmB, ?_⟩
                          refine ⟨fun _ => ?_, fun _ => ?_⟩
                          · -- fuel == 0ULL
                            c0_call hBt
                            refine ⟨c, sB, R, rfl, hcoreB.lengths, hcoreB.trail_lits_lt, hmB, ?_⟩
                            intro valsB2 lvlB2 rsnsB2 teB2 propB2 heurB2 mB2 sB2 hlenB2 _ _ _ _ _
                              hmB2
                            exact luckyScan_ret hQ (s' := sB2) hd1 hd2 hpr hlenB2
                              (Or.inr (Or.inl rfl)) (fun h => by cases h) (fun h => by cases h)
                              (fun h => by cases h) hmB2
                          · -- fuel != 0ULL: assign lit ^ 1 and propagate
                            have hfl_lt : (lit ^^^ 1).toNat < 2 * c.mv := by
                              rw [BitVec.toNat_xor]; exact litNeg_lt_two_mul hlit_lt
                            have hun_flip1 : sB.vals[(lit ^^^ 1).toNat]?.getD 0#8 = 0#8 := hun_flip
                            have hteB_lt : sB.trail_end < c.mv :=
                              hcoreB.trail_end_lt_of_unassigned hfl_lt hun_flip1
                            have hclB_le : sB.cur_level ≤ sB.trail_end := hcoreB.cur_level_le
                            refine ⟨_, load_arena_fuel hmB, ?_⟩
                            obtain ⟨hok_f2, hmB1⟩ := store_arena_fuel (sB.fuel - 1#64) hmB
                            refine ⟨hok_f2, _, load_arena_cur_level hmB1, ?_⟩
                            have hclB_add : BitVec.ofNat 64 sB.cur_level + 1#64 =
                                BitVec.ofNat 64 (sB.cur_level + 1) := by
                              rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
                                bv_add_ofNat]
                            dsimp only; rw [hclB_add]
                            obtain ⟨hok_cl2, hmB2⟩ :=
                              store_arena_cur_level (sB.cur_level + 1) (by omega) hmB1
                            refine ⟨hok_cl2, ?_⟩
                            let sB_pre : PlainState :=
                              { sB with fuel := sB.fuel - 1#64, cur_level := sB.cur_level + 1 }
                            change (PlainMem c sB_pre ⋆ R) _ at hmB2
                            c0_call hAssign
                            refine ⟨c, sB_pre, R, rfl, { hcoreB.lengths with },
                              by dsimp [sB_pre]; omega, hmB2, ?_⟩
                            have hnot_oob2 :
                                ¬ (c.mv ≤ (lit ^^^ 1).toNat / 2 ∨ c.mv ≤ sB_pre.trail_end) := by
                              dsimp only [sB_pre]; omega
                            simp only [hnot_oob2, ↓reduceIte]
                            intro phases2 mA2 hph2 _ hmA2
                            have hcl2_ne0 : sB_pre.cur_level ≠ 0 := by dsimp [sB_pre]; omega
                            simp only [hcl2_ne0, ↓reduceIte] at hmA2
                            have hcoreA2 := decide_assign_preserves_core
                              (plainCoreInv_with_fuel hcoreB (sB.fuel - 1#64)) hfl_lt hph2 hun_flip1
                            c0_call hProp
                            refine ⟨c, F0, _, R, rfl, hcoreA2, hmA2, ?_⟩
                            intro pr2 valsP2 lvlP2 rsnsP2 trlP2 tpP2 teP2 propP2 unflP2 wvecP2
                              arenaP2 wstkP2 wlenP2 wuP2 fuelP2 ctypeP2 crefP2 c0P2 c1P2 oomP2
                              heurP2 mP2 sP2 hcoreP2 _ _ _ _ _ _ _ _ _ _ _ hmP2
                            wp_unfold
                            refine ⟨fun _ => ?_, fun _ => ?_⟩
                            · -- pr2 == 2ULL
                              c0_call hBt
                              refine ⟨c, sP2, R, rfl, hcoreP2.lengths, hcoreP2.trail_lits_lt,
                                hmP2, ?_⟩
                              intro valsB3 lvlB3 rsnsB3 teB3 propB3 heurB3 mB3 sB3 hlenB3 _ _ _ _ _
                                hmB3
                              exact luckyScan_ret hQ (s' := sB3) hd1 hd2 hpr hlenB3
                                (Or.inr (Or.inl rfl)) (fun h => by cases h) (fun h => by cases h)
                                (fun h => by cases h) hmB3
                            · refine ⟨fun _ => ?_, fun _ =>
                                hJ2 () mP2 ⟨sP2, hd1, hd2, hpr, ⟨hcoreP2, hinvL.marks⟩, hmP2⟩⟩
                              -- pr2 == 1ULL -> backtrack to 0 and return 0ULL
                              c0_call hBt
                              refine ⟨c, sP2, R, rfl, hcoreP2.lengths, hcoreP2.trail_lits_lt,
                                hmP2, ?_⟩
                              intro valsB3 lvlB3 rsnsB3 teB3 propB3 heurB3 mB3 sB3 hlenB3 _ _ _ _
                                hcoreB3_fn hmB3
                              have hcoreB3 := (hcoreB3_fn F0 hcoreP2 (Nat.zero_le _)).1
                              exact luckyScan_ret hQ (s' := sB3) hd1 hd2 hpr hlenB3 (Or.inl rfl)
                                (fun h => by cases h) (fun h => by cases h)
                                (fun _ => ⟨hcoreB3, hinvL.marks⟩) hmB3
                        · -- h->cur_level <= 1ULL (sP.cur_level = 1): analyze + level-0 prop
                          c0_call hAnalyze
                          refine ⟨c, F0, sP, R, rfl, ⟨hcoreP, hinvL.marks⟩,
                            analyze_confl_of_prop hconflP, hmP, ?_⟩
                          intro ast valsAn lvlAn rsnsAn trlAn tpAn teAn propAn clAn fuelAn tcAn tlAn
                            mrkAn tmpAn wvecAn arenaAn alenAn wstkAn wlenAn wuAn agAn fredAn niAn
                            nrAn nbAn unflAn ctypeAn crefAn c0An c1An oomAn mstkAn mclrAn mclAn
                            mcfAn heurAn mAn sAn hlenAn _ _ htrlAn hast20 hast1 hmAn
                          wp_unfold
                          refine ⟨fun ha20 => ?_, fun _ => ?_⟩
                          · exact luckyScan_ret hQ (s' := sAn) hd1 hd2 hpr hlenAn
                              (Or.inr (Or.inr (Or.inr rfl))) (fun _ => hast20 ha20)
                              (fun h => by cases h) (fun h => by cases h) hmAn
                          · refine ⟨fun _ => ?_, fun ha1 => ?_⟩
                            · -- ast != 1ULL -> backtrack to 0 and return 2ULL
                              c0_call hBt
                              refine ⟨c, sAn, R, rfl, hlenAn, htrlAn, hmAn, ?_⟩
                              intro valsB2 lvlB2 rsnsB2 teB2 propB2 heurB2 mB2 sB2 hlenB2 _ _ _ _ _
                                hmB2
                              exact luckyScan_ret hQ (s' := sB2) hd1 hd2 hpr hlenB2
                                (Or.inr (Or.inl rfl)) (fun h => by cases h) (fun h => by cases h)
                                (fun h => by cases h) hmB2
                            · -- ast == 1ULL -> clAn < sP.cur_level = 1, so clAn = 0
                              obtain ⟨hinvAn, hclAn_lt⟩ := hast1 ha1
                              have hclAn0 : sAn.cur_level = 0 := by dsimp [sAn]; omega
                              c0_call hProp
                              refine ⟨c, F0, sAn, R, rfl, hinvAn.core, hmAn, ?_⟩
                              intro pr3 valsP3 lvlP3 rsnsP3 trlP3 tpP3 teP3 propP3 unflP3 wvecP3
                                arenaP3 wstkP3 wlenP3 wuP3 fuelP3 ctypeP3 crefP3 c0P3 c1P3 oomP3
                                heurP3 mP3 sP3 hcoreP3 _ _ _ _ _ _ _ _ hpr3_1 _ _ hmP3
                              wp_unfold
                              refine ⟨fun hpr3_1eq => ?_, fun _ => ?_⟩
                              · obtain ⟨_, _, hconfl3⟩ := hpr3_1 hpr3_1eq
                                have huns := level0_unsat_of_prop_conflict hcoreP3 hclAn0 hconfl3
                                exact luckyScan_ret hQ (s' := sP3) hd1 hd2 hpr hcoreP3.lengths
                                  (Or.inr (Or.inr (Or.inr rfl))) (fun _ => huns)
                                  (fun h => by cases h) (fun h => by cases h) hmP3
                              · refine ⟨fun _ => ?_, fun _ =>
                                  hJ2 () mP3 ⟨sP3, hd1, hd2, hpr, ⟨hcoreP3, hinvAn.marks⟩, hmP3⟩⟩
                                c0_call hBt
                                refine ⟨c, sP3, R, rfl, hcoreP3.lengths, hcoreP3.trail_lits_lt,
                                  hmP3, ?_⟩
                                intro valsB3 lvlB3 rsnsB3 teB3 propB3 heurB3 mB3 sB3 hlenB3 _ _ _ _
                                  _ hmB3
                                exact luckyScan_ret hQ (s' := sB3) hd1 hd2 hpr hlenB3
                                  (Or.inr (Or.inl rfl)) (fun h => by cases h)
                                  (fun h => by cases h) (fun h => by cases h) hmB3))
            · intro Jl hJl; wp_unfold
              have hsh1 : ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) = 1 := rfl
              refine ⟨fun _ => hJl _ mF ⟨rfl,
                  by rw [hsh1, bv32_lit_even_toNat (by omega)]; omega,
                  by rw [hsh1, bv32_lit_even_toNat (by omega)]; omega⟩,
                fun _ => hJl _ mF ⟨rfl,
                  by rw [hsh1, bv32_lit_odd_toNat (by omega)]; omega,
                  by rw [hsh1, bv32_lit_odd_toNat (by omega)]; omega⟩⟩)
    · intro Jv hJv; wp_unfold
      refine ⟨fun _ => hJv (iv, ()) ml ⟨rfl, hilt⟩, fun _ => ?_⟩
      have hrev : (BitVec.ofNat 64 c.mv - 1 - iv).toNat = c.mv - 1 - iv.toNat := by bv_omega
      exact hJv (BitVec.ofNat 64 c.mv - 1 - iv, ()) ml ⟨rfl, by omega⟩

/-! ## 2. `plain_lucky_wp` -/

private theorem bv64_add_const_toNat {x : BitVec 64} {k : Nat} (hk : k < 2 ^ 64)
    (h : x.toNat + k < 2 ^ 64) : (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, bv64_ofNat_toNat hk, Nat.mod_eq_of_lt h]

private theorem bv32_zext64_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.isLt; omega)]

private theorem bv64_trunc32_toNat {x : BitVec 64} (h : x.toNat < 2 ^ 32) :
    (x.setWidth 32).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h]

private theorem bv64_ult_ofNat_true {x : BitVec 64} {n : Nat} (hn : n < 2 ^ 64)
    (h : x.ult (BitVec.ofNat 64 n) = true) : x.toNat < n := by
  simp only [BitVec.ult, decide_eq_true_eq, bv64_ofNat_toNat hn] at h; exact h

/-- State bundle matching the postcondition fields of `plainLuckyScanSpec` / `plainLuckySpec`
while `probing = 1#64`. -/
private def LuckyState (c : PlainCfg) (F0 : CNF Nat) (s : PlainState)
    (R : Mem 64 → Prop) (r : BitVec 64) (m : Mem 64) : Prop :=
  ∃ vals' lvl' rsns' trl' tp' te' prop' cl' tc' tl' mrk' tmp' wvec' arena' alen' wstk'
    wlen' wu' ag' fred' ni' nr' nb' unfl' fuel' ctype' cref' c0' c1' oom' mstk' mclr' mcl'
    mcf' heur',
    let s' : PlainState := { s with
      vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
      trail_end := te', propagated := prop', cur_level := cl', tmp_cnt := tc', tmp_len := tl',
      mrk := mrk', tmp := tmp', wvec := wvec', arena := arena', arena_len := alen',
      wstk := wstk', wlen := wlen', wusable := wu', arena_garbage := ag',
      first_reducible := fred', num_irred := ni', num_redundant := nr', num_binary := nb',
      unflushed := unfl', probing := 1#64, fuel := fuel', confl_type := ctype',
      confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom',
      min_stk := mstk', min_clr := mclr', min_clr_len := mcl', min_clr_full := mcf',
      heur := heur' }
    s'.LengthsOk c ∧ (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → F0.Unsat) ∧ (r = 10#64 → PlainInv c F0 s') ∧
    (r = 0#64 → PlainInv c F0 s') ∧ (PlainMem c s' ⋆ R) m

private theorem luckyState_of_scan {c : PlainCfg} {F0 : CNF Nat} {s s0 : PlainState}
    {R : Mem 64 → Prop} {r : BitVec 64} {m' : Mem 64}
    (hd1 : s0.d_cur = s.d_cur) (hd2 : s0.d_val = s.d_val) (hpr : s0.probing = 1#64)
    {vals' lvl' rsns' trl' tp' te' prop' cl' tc' tl' mrk' tmp' wvec' arena' alen' wstk'
      wlen' wu' ag' fred' ni' nr' nb' unfl' fuel' ctype' cref' c0' c1' oom' mstk' mclr' mcl'
      mcf' heur'}
    {s' : PlainState}
    (hs'_def : s' = { s0 with
      vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
      trail_end := te', propagated := prop', cur_level := cl', tmp_cnt := tc', tmp_len := tl',
      mrk := mrk', tmp := tmp', wvec := wvec', arena := arena', arena_len := alen',
      wstk := wstk', wlen := wlen', wusable := wu', arena_garbage := ag',
      first_reducible := fred', num_irred := ni', num_redundant := nr', num_binary := nb',
      unflushed := unfl', fuel := fuel', confl_type := ctype', confl_ref := cref',
      confl_lit0 := c0', confl_lit1 := c1', oom := oom', min_stk := mstk', min_clr := mclr',
      min_clr_len := mcl', min_clr_full := mcf', heur := heur' })
    (hlen' : s'.LengthsOk c) (hdom : r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64)
    (h20 : r = 20#64 → F0.Unsat) (h10 : r = 10#64 → PlainInv c F0 s')
    (h0 : r = 0#64 → PlainInv c F0 s') (hm' : (PlainMem c s' ⋆ R) m') :
    LuckyState c F0 s R r m' := by
  have hs'_eq : s' = { s with
      vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
      trail_end := te', propagated := prop', cur_level := cl', tmp_cnt := tc', tmp_len := tl',
      mrk := mrk', tmp := tmp', wvec := wvec', arena := arena', arena_len := alen',
      wstk := wstk', wlen := wlen', wusable := wu', arena_garbage := ag',
      first_reducible := fred', num_irred := ni', num_redundant := nr', num_binary := nb',
      unflushed := unfl', probing := 1#64, fuel := fuel', confl_type := ctype',
      confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom',
      min_stk := mstk', min_clr := mclr', min_clr_len := mcl', min_clr_full := mcf',
      heur := heur' } := by
    rw [hs'_def]; simp only [hd1, hd2, hpr]
  rw [hs'_eq] at hlen' h10 h0 hm'
  exact ⟨vals', lvl', rsns', trl', tp', te', prop', cl', tc', tl', mrk', tmp', wvec', arena',
    alen', wstk', wlen', wu', ag', fred', ni', nr', nb', unfl', fuel', ctype', cref', c0', c1',
    oom', mstk', mclr', mcl', mcf', heur', hlen', hdom, h20, h10, h0, hm'⟩

private theorem luckyState_inv_zero {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {R : Mem 64 → Prop} {m : Mem 64} (h : LuckyState c F0 s R 0#64 m) :
    ∃ s' : PlainState, s'.d_cur = s.d_cur ∧ s'.d_val = s.d_val ∧ s'.probing = 1#64 ∧
      PlainInv c F0 s' ∧ (PlainMem c s' ⋆ R) m := by
  rcases h with ⟨vals', lvl', rsns', trl', tp', te', prop', cl', tc', tl', mrk', tmp', wvec',
    arena', alen', wstk', wlen', wu', ag', fred', ni', nr', nb', unfl', fuel', ctype', cref',
    c0', c1', oom', mstk', mclr', mcl', mcf', heur', _, _, _, _, h0, hm⟩
  exact ⟨{ s with
      vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
      trail_end := te', propagated := prop', cur_level := cl', tmp_cnt := tc', tmp_len := tl',
      mrk := mrk', tmp := tmp', wvec := wvec', arena := arena', arena_len := alen',
      wstk := wstk', wlen := wlen', wusable := wu', arena_garbage := ag',
      first_reducible := fred', num_irred := ni', num_redundant := nr', num_binary := nb',
      unflushed := unfl', probing := 1#64, fuel := fuel', confl_type := ctype',
      confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom',
      min_stk := mstk', min_clr := mclr', min_clr_len := mcl', min_clr_full := mcf',
      heur := heur' }, rfl, rfl, rfl, h0 rfl, hm⟩

/-- Step helper for `WatchSliceOk`: splits on binary vs large watch entry. -/
private theorem watchSlice_step {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {lit p rem : Nat} (h : WatchSliceOk c F0 s lit p rem) (hpos : 0 < rem) :
    ∃ w0 : BitVec 32, s.wstk[p]? = some w0 ∧
      (((w0 &&& 0x80000000#32) ≠ 0#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * c.mv ∧
          WatchSliceOk c F0 s lit (p + 1) (rem - 1)) ∨
       ((w0 &&& 0x80000000#32) = 0#32 ∧ 2 ≤ rem ∧
          WatchSliceOk c F0 s lit (p + 2) (rem - 2))) := by
  cases h with
  | empty => omega
  | @bin _ r' w0 hp hflag hlt _ hrest =>
    exact ⟨w0, hp, Or.inl ⟨hflag, hlt, by simpa using hrest⟩⟩
  | @large _ r' w0 _ hp _ hflag _ _ hrest =>
    exact ⟨w0, hp, Or.inr ⟨hflag, by omega, by simpa using hrest⟩⟩

theorem plain_lucky_wp (Γ : Env)
    (hNext : ∀ args m Q X, plainArenaNextSpec args m Q X →
      Γ "plain_arena_next" [i64, i32] [i32] args m Q X)
    (hBt : ∀ args m Q X, plainBacktrackSpec args m Q X →
      Γ "plain_backtrack" [i64, i64] [] args m Q X)
    (hAssign : ∀ args m Q X, plainAssignSpec args m Q X →
      Γ "plain_assign" [i64, i32, i32] [] args m Q X)
    (hProp : ∀ args m Q X, plainPropagateSpec args m Q X →
      Γ "plain_propagate" [i64] [i64] args m Q X)
    (hScan : ∀ args m Q X, plainLuckyScanSpec args m Q X →
      Γ "plain_lucky_scan" [i64, .bool, .bool] [i64] args m Q X) :
    ∀ args m Q X, plainLuckySpec args m Q X →
      Func.wp Γ plain_lucky_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmv := c.hmv; have har := c.harena; have hwc := c.hwcap
  unfold dimacsBound at hmv har hwc
  have hlen := hinv.core.lengths
  have halen_lt : s.arena_len < 2 ^ 30 := by have := hlen.arena_len_le; omega
  have hwlen_lt : s.wlen < 2 ^ 30 := by have := hlen.wlen_le; omega
  let s0 : PlainState := { s with probing := 1#64 }
  have hinv0 : PlainInv c F0 s0 := plainInv_with_probing hinv 1#64
  have hlen0 : s0.LengthsOk c := hinv0.core.lengths
  unfold Func.wp plain_lucky_body; wp_unfold
  refine ⟨_, load_arena_mv hm, _, load_arena_values hm, _, load_arena_arena_ptr hm,
    _, load_arena_watch_vec hm, _, load_arena_watch_stk hm, _, load_arena_len hm, ?_⟩
  obtain ⟨hok_pr, hm0⟩ := store_arena_probing 1#64 hm
  refine ⟨hok_pr, ?_⟩
  change (PlainMem c s0 ⋆ R) _ at hm0
  generalize hm0_eq : storeMem m i64 (c.hdr + 520) 1#64 = m0 at hm0 ⊢
  -- Loop 1: scan arena clauses (`while (p < alen && (!has_all_neg || !has_all_pos))`)
  refine wp_loop_inv
    (fun ((_hn, _hp, pv, ()) : Tup Val [.bool, .bool, i64]) ml =>
      ml = m0 ∧ (pv.toNat = s.arena_len ∨ pv.toNat ∈ arenaClauseRefs s))
    (fun ((_hn, _hp, pv, ()) : Tup Val [.bool, .bool, i64]) _ => s.arena_len - pv.toNat) ?_ ?_
  · intro J1 hJ1; c0_steps
    have h0_mem : (0#64 : BitVec 64).toNat = s.arena_len ∨
        (0#64 : BitVec 64).toNat ∈ arenaClauseRefs s := by
      rcases hinv.core.arena.len_ok with hz | h3
      · exact Or.inl (by simp [hz])
      · right; unfold arenaClauseRefs
        cases halen : s.arena_len with
        | zero => omega
        | succ f => unfold arenaScanRefs; simp [← halen, h3]
    exact hJ1 (false, false, 0#64, ()) m0 ⟨rfl, h0_mem⟩
  · rintro J1 ⟨hn1, hp1, pv, ⟨⟩⟩ ml ⟨hml, hp_mem⟩ ih1; subst ml
    -- Exit join of Loop 1 -> Loop 2
    refine wp_join_group (fun () mb => mb = m0) ?_ ?_
    · rintro _ ⟨⟩ mb hmb; subst mb
      -- Loop 2: scan binary watch lists (`while (v < mv && (!has_all_neg || !has_all_pos))`)
      refine wp_loop_inv
        (fun ((_hn2, _hp2, vv, ()) : Tup Val [.bool, .bool, i64]) ml2 =>
          ml2 = m0 ∧ vv.toNat ≤ c.mv)
        (fun ((_hn2, _hp2, vv, ()) : Tup Val [.bool, .bool, i64]) _ => c.mv - vv.toNat) ?_ ?_
      · intro J2 hJ2; c0_steps; exact hJ2 (hn1, hp1, 0#64, ()) m0 ⟨rfl, Nat.zero_le _⟩
      · rintro J2 ⟨hn2, hp2, vv, ⟨⟩⟩ ml2 ⟨hml2, hvle⟩ ih2; subst ml2
        -- Exit join of Loop 2 -> Loop 3 / 4x `plain_lucky_scan`
        refine wp_join_group (fun () mb2 => mb2 = m0) ?_ ?_
        · rintro _ ⟨⟩ mb2 hmb2; subst mb2
          -- Join for `if (!has_all_neg || !has_all_pos)` -> Loop 3
          refine wp_join_group (fun () m3 => m3 = m0) ?_ ?_
          · rintro _ ⟨⟩ m3 hm3; subst m3; wp_unfold
            -- Loop 3: assign remaining variables to uniform polarity
            refine wp_loop_inv
              (fun (vv3, ()) ml3 =>
                ∃ valsL lvlL rsnsL trlL tpL teL propL clL unflL wvecL arenaL wstkL
                  wlenL wuL fuelL ctypeL crefL c0L c1L oomL heurL,
                  let sL : PlainState := { s with
                    vals := valsL, lvl := lvlL, rsns := rsnsL, trl := trlL, trail_pos := tpL,
                    trail_end := teL, propagated := propL, cur_level := clL, unflushed := unflL,
                    probing := 1#64, wvec := wvecL, arena := arenaL, wstk := wstkL, wlen := wlenL,
                    wusable := wuL, fuel := fuelL, confl_type := ctypeL, confl_ref := crefL,
                    confl_lit0 := c0L, confl_lit1 := c1L, oom := oomL, heur := heurL }
                  vv3.toNat ≤ c.mv ∧ PlainInv c F0 sL ∧ (PlainMem c sL ⋆ R) ml3)
              (fun (vv3, ()) _ => c.mv - vv3.toNat) ?_ ?_
            · intro J3 hJ3; c0_steps
              exact hJ3 (0#64, ()) m0 ⟨s.vals, s.lvl, s.rsns, s.trl, s.trail_pos, s.trail_end,
                s.propagated, s.cur_level, s.unflushed, s.wvec, s.arena, s.wstk, s.wlen,
                s.wusable, s.fuel, s.confl_type, s.confl_ref, s.confl_lit0, s.confl_lit1, s.oom,
                s.heur, Nat.zero_le _, hinv0, hm0⟩
            · rintro J3 ⟨vv3, ⟨⟩⟩ ml3 ⟨valsL, lvlL, rsnsL, trlL, tpL, teL, propL, clL, unflL,
                wvecL, arenaL, wstkL, wlenL, wuL, fuelL, ctypeL, crefL, c0L, c1L, oomL, heurL,
                hvle3, hinvL, hml3⟩ ih3
              let sL : PlainState := { s with
                vals := valsL, lvl := lvlL, rsns := rsnsL, trl := trlL, trail_pos := tpL,
                trail_end := teL, propagated := propL, cur_level := clL, unflushed := unflL,
                probing := 1#64, wvec := wvecL, arena := arenaL, wstk := wstkL, wlen := wlenL,
                wusable := wuL, fuel := fuelL, confl_type := ctypeL, confl_ref := crefL,
                confl_lit0 := c0L, confl_lit1 := c1L, oom := oomL, heur := heurL }
              change PlainInv c F0 sL at hinvL; change (PlainMem c sL ⋆ R) ml3 at hml3
              wp_unfold
              refine ⟨fun hvlt_b => ?_, fun _ => ?_⟩
              · have hvlt3 : vv3.toNat < c.mv := by
                  change vv3.ult (BitVec.ofNat 64 c.mv) = true at hvlt_b
                  simp only [BitVec.ult, decide_eq_true_eq] at hvlt_b; bv_omega
                have h2v : (vv3 <<< 1).toNat = 2 * vv3.toNat := bv64_shl1_toNat (by omega)
                have hvl : sL.vals.length = 2 * c.mv := hinvL.core.lengths.vals_len
                have hv1 : (vv3 + 1#64).toNat = vv3.toNat + 1 := by bv_omega
                refine wp_join_group
                  (fun (() : Tup Val []) ml3' =>
                    ∃ vals' lvl' rsns' trl' tp' te' prop' cl' unfl' wvec' arena' wstk'
                      wlen' wu' fuel' ctype' cref' c0' c1' oom' heur',
                      let sL' : PlainState := { s with
                        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
                        trail_end := te', propagated := prop', cur_level := cl', unflushed := unfl',
                        probing := 1#64, wvec := wvec', arena := arena', wstk := wstk',
                        wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
                        confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom',
                        heur := heur' }
                      PlainInv c F0 sL' ∧ (PlainMem c sL' ⋆ R) ml3')
                  (fun _ ⟨⟩ ml3' ⟨vals', lvl', rsns', trl', tp', te', prop', cl', unfl', wvec',
                      arena', wstk', wlen', wu', fuel', ctype', cref', c0', c1', oom', heur',
                      hinv', hml'⟩ => by
                    wp_unfold
                    exact ih3 (vv3 + 1#64, ()) ml3' (by dsimp; omega)
                      ⟨vals', lvl', rsns', trl', tp', te', prop', cl', unfl', wvec', arena', wstk',
                        wlen', wu', fuel', ctype', cref', c0', c1', oom', heur', by omega,
                        hinv', hml'⟩)
                  (fun Jif hJif => by
                    wp_unfold
                    refine ⟨_, c0_load_arena_vals (i := vv3 <<< 1) (by omega) hml3, ?_⟩
                    refine ⟨fun hz => ?_, fun _ =>
                      hJif () ml3 ⟨valsL, lvlL, rsnsL, trlL, tpL, teL, propL, clL, unflL, wvecL,
                        arenaL, wstkL, wlenL, wuL, fuelL, ctypeL, crefL, c0L, c1L, oomL, heurL,
                        hinvL, hml3⟩⟩
                    have hun : sL.vals[2 * vv3.toNat]?.getD 0#8 = 0#8 := by
                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                      simpa [h2v] using bv8_sext32_eq_zero hz
                    refine ⟨_, load_arena_fuel hml3, ?_⟩
                    refine ⟨fun _ => ?_, fun _ => ?_⟩
                    · c0_call hBt
                      refine ⟨c, sL, R, rfl, hinvL.core.lengths, hinvL.core.trail_lits_lt, hml3, ?_⟩
                      intro valsB lvlB rsnsB teB propB heurB mB sB hlenB _ _ _ _ _ hmB
                      wp_unfold; obtain ⟨hok0, hmB'⟩ := store_arena_probing 0#64 hmB
                      exact ⟨hok0, hQ 2#64 valsB lvlB rsnsB trlL tpL teB propB 0 s.tmp_cnt s.tmp_len
                        s.mrk s.tmp wvecL arenaL s.arena_len wstkL wlenL wuL s.arena_garbage
                        s.first_reducible s.num_irred s.num_redundant s.num_binary unflL fuelL
                        ctypeL crefL c0L c1L oomL s.min_stk s.min_clr s.min_clr_len s.min_clr_full
                        heurB _ { hlenB with } (Or.inr (Or.inl rfl)) (fun h => by cases h)
                        (fun h => by cases h) (fun h => by cases h) hmB'⟩
                    · have hte_lt : sL.trail_end < c.mv :=
                        hinvL.core.trail_end_lt_of_unassigned (by omega) hun
                      have hcl_le : sL.cur_level ≤ sL.trail_end := hinvL.core.cur_level_le
                      dsimp only [sL] at hte_lt hcl_le
                      refine ⟨_, load_arena_fuel hml3, ?_⟩
                      obtain ⟨hok_f, hml1⟩ := store_arena_fuel (sL.fuel - 1) hml3
                      refine ⟨hok_f, _, load_arena_cur_level hml1, ?_⟩
                      dsimp only [sL]
                      rw [show BitVec.ofNat 64 clL + 1 = BitVec.ofNat 64 (clL + 1) from by
                        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]]
                      obtain ⟨hok_cl, hml2⟩ := store_arena_cur_level (clL + 1) (by omega) hml1
                      refine ⟨hok_cl, ?_⟩
                      let s_pre : PlainState := { sL with fuel := fuelL - 1, cur_level := clL + 1 }
                      change (PlainMem c s_pre ⋆ R) _ at hml2
                      refine wp_join_group
                        (fun (lit, ()) m_lit =>
                          m_lit = storeMem (storeMem ml3 i64 (c.hdr + 168) (fuelL - 1))
                            i64 (c.hdr + 160) (BitVec.ofNat 64 (clL + 1)) ∧
                          lit.toNat < 2 * c.mv ∧ lit.toNat / 2 = vv3.toNat) ?_ ?_
                      · rintro _ ⟨lit, ⟨⟩⟩ m_lit ⟨hm_lit, hlit_lt, hlit_v⟩; subst m_lit
                        have hun_lit : sL.vals[lit.toNat]?.getD 0#8 = 0#8 := by
                          rw [hinvL.core.vals_zero_iff hlit_lt, hlit_v]
                          have h0' := (hinvL.core.vals_zero_iff
                            (by omega : 2 * vv3.toNat < 2 * c.mv)).mp hun
                          simpa using h0'
                        c0_call hAssign
                        refine ⟨c, s_pre, R, rfl, { hinvL.core.lengths with },
                          by dsimp [s_pre, sL]; omega, hml2, ?_⟩
                        have hnot_oob : ¬ (c.mv ≤ lit.toNat / 2 ∨ c.mv ≤ s_pre.trail_end) := by
                          dsimp [s_pre, sL]; omega
                        simp only [hnot_oob, ↓reduceIte]
                        intro phases' mA hph' _ hmA
                        have hcl_ne0 : s_pre.cur_level ≠ 0 := by dsimp [s_pre]; omega
                        simp only [hcl_ne0, ↓reduceIte] at hmA
                        have hcoreA := decide_assign_preserves_core
                          (plainCoreInv_with_fuel hinvL.core (fuelL - 1)) hlit_lt hph' hun_lit
                        c0_call hProp
                        refine ⟨c, F0, _, R, rfl, hcoreA, hmA, ?_⟩
                        intro pr valsP lvlP rsnsP trlP tpP teP propP unflP wvecP arenaP wstkP wlenP
                          wuP fuelP ctypeP crefP c0P c1P oomP heurP mP sP hcoreP _ _ _ _ _ _ _ _ _ _
                          _ hmP
                        c0_steps
                        · c0_call hBt
                          refine ⟨c, sP, R, rfl, hcoreP.lengths, hcoreP.trail_lits_lt, hmP, ?_⟩
                          intro valsB lvlB rsnsB teB propB heurB mB sB hlenB _ _ _ _ hcoreB_fn hmB
                          have hcoreB := (hcoreB_fn F0 hcoreP (Nat.zero_le _)).1
                          wp_unfold; obtain ⟨hok0, hmB'⟩ := store_arena_probing 0#64 hmB
                          exact ⟨hok0, hQ 0#64 valsB lvlB rsnsB trlP tpP teB propB 0 s.tmp_cnt
                            s.tmp_len s.mrk s.tmp wvecP arenaP s.arena_len wstkP wlenP wuP
                            s.arena_garbage s.first_reducible s.num_irred s.num_redundant
                            s.num_binary unflP fuelP ctypeP crefP c0P c1P oomP s.min_stk s.min_clr
                            s.min_clr_len s.min_clr_full heurB _ { hlenB with }
                            (Or.inl rfl) (fun h => by cases h) (fun h => by cases h)
                            (fun _ => ⟨plainCoreInv_with_probing hcoreB 0#64, hinv.marks⟩) hmB'⟩
                        · exact hJif () mP
                            ⟨valsP, lvlP, rsnsP, trlP, tpP, teP, propP, clL + 1, unflP, wvecP,
                              arenaP, wstkP, wlenP, wuP, fuelP, ctypeP, crefP, c0P, c1P, oomP,
                              heurP, ⟨hcoreP, hinv.marks⟩, hmP⟩
                      · intro Jl hJl; c0_steps
                        · exact hJl _ _ ⟨rfl, by rw [bv32_lit_even_toNat (by omega)]; omega,
                            by rw [bv32_lit_even_toNat (by omega)]; omega⟩
                        · exact hJl _ _ ⟨rfl, by rw [bv32_lit_odd_toNat (by omega)]; omega,
                            by rw [bv32_lit_odd_toNat (by omega)]; omega⟩)
              · obtain ⟨hok0, hml'⟩ := store_arena_probing 0#64 hml3
                exact ⟨hok0, hQ 10#64 valsL lvlL rsnsL trlL tpL teL propL clL s.tmp_cnt s.tmp_len
                  s.mrk s.tmp wvecL arenaL s.arena_len wstkL wlenL wuL s.arena_garbage
                  s.first_reducible s.num_irred s.num_redundant s.num_binary unflL fuelL ctypeL
                  crefL c0L c1L oomL s.min_stk s.min_clr s.min_clr_len s.min_clr_full heurL _
                  { hinvL.core.lengths with } (Or.inr (Or.inr (Or.inl rfl)))
                  (fun h => by cases h) (fun _ => plainInv_with_probing hinvL 0#64)
                  (fun h => by cases h) hml'⟩
          · intro J3 hJ3; c0_steps
            · -- Both `has_all_neg` and `has_all_pos`: 4x `plain_lucky_scan`
              c0_call hScan; refine ⟨c, F0, s0, R, rfl, hinv0, hm0, ?_⟩
              intro r1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 s1
                hlen1 hdom1 h20_1 h10_1 h0_1 hm1
              have hL1 := luckyState_of_scan (s := s) (s0 := s0) rfl rfl rfl rfl hlen1 hdom1 h20_1
                h10_1 h0_1 hm1
              refine wp_join_group (fun (r, ()) m' => LuckyState c F0 s R r m') ?_ ?_
              · rintro _ ⟨r2, ⟨⟩⟩ m2 hL2
                refine wp_join_group (fun (r, ()) m' => LuckyState c F0 s R r m') ?_ ?_
                · rintro _ ⟨r3, ⟨⟩⟩ m3 hL3
                  refine wp_join_group (fun (r, ()) m' => LuckyState c F0 s R r m') ?_ ?_
                  · rintro _ ⟨r4, ⟨⟩⟩ m4 hL4
                    rcases hL4 with ⟨vals', lvl', rsns', trl', tp', te', prop', cl', tc', tl',
                      mrk', tmp', wvec', arena', alen', wstk', wlen', wu', ag', fred', ni', nr',
                      nb', unfl', fuel', ctype', cref', c0', c1', oom', mstk', mclr', mcl', mcf',
                      heur', hlen4, hdom4, h20_4, h10_4, h0_4, hm4⟩
                    wp_unfold; obtain ⟨hok0, hm4'⟩ := store_arena_probing 0#64 hm4
                    exact ⟨hok0, hQ r4 vals' lvl' rsns' trl' tp' te' prop' cl' tc' tl' mrk' tmp'
                      wvec' arena' alen' wstk' wlen' wu' ag' fred' ni' nr' nb' unfl' fuel' ctype'
                      cref' c0' c1' oom' mstk' mclr' mcl' mcf' heur' _ { hlen4 with } hdom4 h20_4
                      (fun h => plainInv_with_probing (h10_4 h) 0#64)
                      (fun h => plainInv_with_probing (h0_4 h) 0#64) hm4'⟩
                  · intro Jc3 hJc3; c0_steps
                    · subst r3; obtain ⟨s3, hd1, hd2, hpr, hinv3, hm3⟩ := luckyState_inv_zero hL3
                      c0_call hScan; refine ⟨c, F0, s3, R, rfl, hinv3, hm3, ?_⟩
                      intro r4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                        m4 _ hlen4 hdom4 h20_4 h10_4 h0_4 hm4
                      exact hJc3 (r4, ()) m4
                        (luckyState_of_scan hd1 hd2 hpr rfl hlen4 hdom4 h20_4 h10_4 h0_4 hm4)
                    · exact hJc3 (r3, ()) m3 hL3
                · intro Jc2 hJc2; c0_steps
                  · subst r2; obtain ⟨s2, hd1, hd2, hpr, hinv2, hm2⟩ := luckyState_inv_zero hL2
                    c0_call hScan; refine ⟨c, F0, s2, R, rfl, hinv2, hm2, ?_⟩
                    intro r3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                      m3 _ hlen3 hdom3 h20_3 h10_3 h0_3 hm3
                    exact hJc2 (r3, ()) m3
                      (luckyState_of_scan hd1 hd2 hpr rfl hlen3 hdom3 h20_3 h10_3 h0_3 hm3)
                  · exact hJc2 (r2, ()) m2 hL2
              · intro Jc1 hJc1; c0_steps
                · subst r1; obtain ⟨s1', hd1, hd2, hpr, hinv1', hm1'⟩ := luckyState_inv_zero hL1
                  c0_call hScan; refine ⟨c, F0, s1', R, rfl, hinv1', hm1', ?_⟩
                  intro r2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2
                    _ hlen2 hdom2 h20_2 h10_2 h0_2 hm2
                  exact hJc1 (r2, ()) m2
                    (luckyState_of_scan hd1 hd2 hpr rfl hlen2 hdom2 h20_2 h10_2 h0_2 hm2)
                · exact hJc1 (r1, ()) m1 hL1
            · exact hJ3 () m0 rfl
            · exact hJ3 () m0 rfl
        · intro B2 hB2; wp_unfold
          refine ⟨fun hvlt_b => ?_, fun _ => hB2 () m0 rfl⟩
          -- `v < mv`: join for `(!hn2 || !hp2)`
          refine wp_join_group (fun () m_b => m_b = m0) ?_ ?_
          · rintro _ ⟨⟩ m_b hm_b; subst m_b
            have hvlt : vv.toNat < c.mv := by
              change vv.ult (BitVec.ofNat 64 c.mv) = true at hvlt_b
              simp only [BitVec.ult, decide_eq_true_eq] at hvlt_b; bv_omega
            have h2v : (vv <<< 1).toNat = 2 * vv.toNat := bv64_shl1_toNat (by omega)
            have hvl : s.vals.length = 2 * c.mv := hlen.vals_len
            have hv1 : (vv + 1#64).toNat = vv.toNat + 1 := by bv_omega
            refine wp_join_group
              (fun ((_hn', _hp', ()) : Tup Val [.bool, .bool]) m_if => m_if = m0) ?_ ?_
            · rintro _ ⟨hn', hp', ⟨⟩⟩ m_if hm_if; subst m_if
              exact ih2 (hn', hp', vv + 1#64, ()) m0 (by dsimp only; omega) ⟨rfl, by omega⟩
            · intro Jv hJv; wp_unfold
              have hvl0 : s0.vals.length = 2 * c.mv := hlen0.vals_len
              refine ⟨_, c0_load_arena_vals (i := vv <<< 1) (by omega) hm0, ?_⟩
              refine ⟨fun _ => ?_, fun _ => hJv (hn2, hp2, ()) m0 rfl⟩
              have hwvl : s0.wvec.length = 4 * c.mv := hlen0.wvec_len
              have hwvl_s : s.wvec.length = 4 * c.mv := hlen.wvec_len
              have hwsl : s0.wstk.length = c.wcap := hlen0.wstk_len_arr
              have hwsl_s : s.wstk.length = c.wcap := hlen.wstk_len_arr
              have hwcap_le : s.wlen ≤ c.wcap := hlen.wlen_le
              -- nl = (v << 1) | 1
              let nl := ((vv <<< 1) ||| 1#64).setWidth 32
              have hnl_nat : nl.toNat = 2 * vv.toNat + 1 := by
                have := bv32_lit_odd_toNat (v := vv) (by omega)
                have heq : nl = ((vv <<< 1).setWidth 32) ||| 1 := by
                  dsimp only [nl]; rw [BitVec.setWidth_or]; rfl
                rw [heq]; exact this
              have hnl_w0 : (nl.setWidth 64 <<< 1).toNat = 2 * (2 * vv.toNat + 1) := by
                rw [bv64_shl1_toNat (by rw [bv32_zext64_toNat]; omega), bv32_zext64_toNat, hnl_nat]
              have hnl_w1 : ((nl.setWidth 64 <<< 1) + 1#64).toNat =
                  2 * (2 * vv.toNat + 1) + 1 := by
                rw [bv64_add_const_toNat (k := 1) (by decide) (by omega), hnl_w0]
              refine ⟨_, c0_load_arena_wvec (i := nl.setWidth 64 <<< 1) (by omega) hm0,
                _, c0_load_arena_wvec (i := (nl.setWidth 64 <<< 1) + 1#64) (by omega) hm0, ?_⟩
              have hnbnd := hinv.core.watches.bounds (2 * vv.toNat + 1) (by omega)
              have hnsl := hinv.core.watches.slices (2 * vv.toNat + 1) (by omega)
              have hoff_n : (s0.wvec[(nl.setWidth 64 <<< 1).toNat]'(by omega)).toNat =
                  watchOff s (2 * vv.toNat + 1) := by
                unfold watchOff
                have h1 : s0.wvec[(nl.setWidth 64 <<< 1).toNat]'(by omega) =
                    s.wvec[2 * (2 * vv.toNat + 1)]'(by omega) := by simp [s0, hnl_w0]
                rw [h1, List.getElem?_eq_getElem (by omega)]; rfl
              have hsz_n : (s0.wvec[((nl.setWidth 64 <<< 1) + 1#64).toNat]'(by omega)).toNat =
                  watchSize s (2 * vv.toNat + 1) := by
                unfold watchSize
                have h1 : s0.wvec[((nl.setWidth 64 <<< 1) + 1#64).toNat]'(by omega) =
                    s.wvec[2 * (2 * vv.toNat + 1) + 1]'(by omega) := by simp [s0, hnl_w1]
                rw [h1, List.getElem?_eq_getElem (by omega)]; rfl
              let endN := watchOff s (2 * vv.toNat + 1) + watchSize s (2 * vv.toNat + 1)
              have hendN_bv :
                  ((s0.wvec[(nl.setWidth 64 <<< 1).toNat]'(by omega)).setWidth 64 +
                    (s0.wvec[((nl.setWidth 64 <<< 1) + 1#64).toNat]'(by omega)).setWidth 64).toNat
                    = endN := by
                have ha := BitVec.toNat_add
                  ((s0.wvec[(nl.setWidth 64 <<< 1).toNat]'(by omega)).setWidth 64)
                  ((s0.wvec[((nl.setWidth 64 <<< 1) + 1#64).toNat]'(by omega)).setWidth 64)
                rw [ha, bv32_zext64_toNat, bv32_zext64_toNat, hoff_n, hsz_n,
                  Nat.mod_eq_of_lt (by omega)]
              -- Inner watch loop 1 (`nl`)
              refine wp_loop_inv
                (fun ((_hn_a, off_a, ()) : Tup Val [.bool, i64]) m_a =>
                  m_a = m0 ∧ off_a.toNat ≤ endN ∧
                  WatchSliceOk c F0 s (2 * vv.toNat + 1) off_a.toNat (endN - off_a.toNat))
                (fun ((_hn_a, off_a, ()) : Tup Val [.bool, i64]) _ => endN - off_a.toNat) ?_ ?_
              · intro Ja hJa; wp_unfold
                have hinit : ((s0.wvec[(nl.setWidth 64 <<< 1).toNat]'(by omega)).setWidth 64).toNat
                    = watchOff s (2 * vv.toNat + 1) := by
                  rw [bv32_zext64_toNat, hoff_n]
                refine hJa _ m0 ⟨rfl, by dsimp only [endN]; omega, ?_⟩
                change WatchSliceOk c F0 s (2 * vv.toNat + 1)
                  ((s0.wvec[(nl.setWidth 64 <<< 1).toNat]'(by omega)).setWidth 64).toNat
                  (endN - ((s0.wvec[(nl.setWidth 64 <<< 1).toNat]'(by omega)).setWidth 64).toNat)
                rw [hinit]; simpa [endN, Nat.add_sub_cancel_left] using hnsl
              · rintro Ja ⟨hn_a, off_a, ⟨⟩⟩ m_a ⟨hm_a, hle_a, hsl_a⟩ ih_a; subst m_a
                refine wp_join_group (fun (() : Tup Val []) m_ea => m_ea = m0) ?_ ?_
                · rintro _ ⟨⟩ m_ea hm_ea; subst m_ea
                  -- pl = v << 1
                  let pl := (vv <<< 1).setWidth 32
                  have hpl_nat : pl.toNat = 2 * vv.toNat := bv32_lit_even_toNat (by omega)
                  have hpl_w0 : (pl.setWidth 64 <<< 1).toNat = 2 * (2 * vv.toNat) := by
                    rw [bv64_shl1_toNat (by rw [bv32_zext64_toNat]; omega), bv32_zext64_toNat,
                      hpl_nat]
                  have hpl_w1 : ((pl.setWidth 64 <<< 1) + 1#64).toNat =
                      2 * (2 * vv.toNat) + 1 := by
                    rw [bv64_add_const_toNat (k := 1) (by decide) (by omega), hpl_w0]
                  wp_unfold
                  refine ⟨_, c0_load_arena_wvec (i := pl.setWidth 64 <<< 1) (by omega) hm0,
                    _, c0_load_arena_wvec (i := (pl.setWidth 64 <<< 1) + 1#64) (by omega) hm0, ?_⟩
                  have hpbnd := hinv.core.watches.bounds (2 * vv.toNat) (by omega)
                  have hpsl := hinv.core.watches.slices (2 * vv.toNat) (by omega)
                  have hoff_p : (s0.wvec[(pl.setWidth 64 <<< 1).toNat]'(by omega)).toNat =
                      watchOff s (2 * vv.toNat) := by
                    unfold watchOff
                    have h1 : s0.wvec[(pl.setWidth 64 <<< 1).toNat]'(by omega) =
                        s.wvec[2 * (2 * vv.toNat)]'(by omega) := by simp [s0, hpl_w0]
                    rw [h1, List.getElem?_eq_getElem (by omega)]; rfl
                  have hsz_p : (s0.wvec[((pl.setWidth 64 <<< 1) + 1#64).toNat]'(
                      by omega)).toNat = watchSize s (2 * vv.toNat) := by
                    unfold watchSize
                    have h1 : s0.wvec[((pl.setWidth 64 <<< 1) + 1#64).toNat]'(by omega) =
                        s.wvec[2 * (2 * vv.toNat) + 1]'(by omega) := by simp [s0, hpl_w1]
                    rw [h1, List.getElem?_eq_getElem (by omega)]; rfl
                  let endP := watchOff s (2 * vv.toNat) + watchSize s (2 * vv.toNat)
                  have hendP_bv :
                      ((s0.wvec[(pl.setWidth 64 <<< 1).toNat]'(by omega)).setWidth 64 +
                        (s0.wvec[((pl.setWidth 64 <<< 1) + 1#64).toNat]'(by omega)).setWidth
                          64).toNat = endP := by
                    have ha := BitVec.toNat_add
                      ((s0.wvec[(pl.setWidth 64 <<< 1).toNat]'(by omega)).setWidth 64)
                      ((s0.wvec[((pl.setWidth 64 <<< 1) + 1#64).toNat]'(by omega)).setWidth 64)
                    rw [ha, bv32_zext64_toNat, bv32_zext64_toNat, hoff_p, hsz_p,
                      Nat.mod_eq_of_lt (by omega)]
                  -- Inner watch loop 2 (`pl`)
                  refine wp_loop_inv
                    (fun ((_hp_b, off_b, ()) : Tup Val [.bool, i64]) m_b =>
                      m_b = m0 ∧ off_b.toNat ≤ endP ∧
                      WatchSliceOk c F0 s (2 * vv.toNat) off_b.toNat (endP - off_b.toNat))
                    (fun ((_hp_b, off_b, ()) : Tup Val [.bool, i64]) _ =>
                      endP - off_b.toNat) ?_ ?_
                  · intro Jb hJb; wp_unfold
                    have hinit : ((s0.wvec[(pl.setWidth 64 <<< 1).toNat]'(by omega)).setWidth
                        64).toNat = watchOff s (2 * vv.toNat) := by
                      rw [bv32_zext64_toNat, hoff_p]
                    refine hJb _ m0 ⟨rfl, by dsimp only [endP]; omega, ?_⟩
                    change WatchSliceOk c F0 s (2 * vv.toNat)
                      ((s0.wvec[(pl.setWidth 64 <<< 1).toNat]'(by omega)).setWidth 64).toNat
                      (endP - ((s0.wvec[(pl.setWidth 64 <<< 1).toNat]'(by omega)).setWidth
                        64).toNat)
                    rw [hinit]; simpa [endP, Nat.add_sub_cancel_left] using hpsl
                  · rintro Jb ⟨hp_b, off_b, ⟨⟩⟩ m_b ⟨hm_b, hle_b, hsl_b⟩ ih_b; subst m_b
                    wp_unfold
                    refine ⟨fun hoff_lt => ⟨fun _ => hJv (hn_a, hp_b, ()) m0 rfl, fun _ => ?_⟩,
                      fun _ => hJv (hn_a, hp_b, ()) m0 rfl⟩
                    have hlt_b : off_b.toNat < endP := by
                      simp only [BitVec.ult, decide_eq_true_eq] at hoff_lt; omega
                    obtain ⟨w0, hw0_get, hw0_cases⟩ := watchSlice_step hsl_b (by omega)
                    have hw0_eq : s0.wstk[off_b.toNat]'(by omega) = w0 := by
                      have := List.getElem?_eq_getElem (l := s.wstk) (i := off_b.toNat) (by omega)
                      rw [this] at hw0_get; exact Option.some.inj hw0_get
                    refine ⟨_, c0_load_arena_wstk (i := off_b) (by omega) hm0, ?_⟩
                    rw [hw0_eq]
                    refine wp_join_group
                      (fun ((_hp', off', ()) : Tup Val [.bool, i64]) m_w =>
                        m_w = m0 ∧ off'.toNat ≤ endP ∧ off_b.toNat < off'.toNat ∧
                        WatchSliceOk c F0 s (2 * vv.toNat) off'.toNat (endP - off'.toNat))
                      (fun _ ⟨hp', off', ⟨⟩⟩ m_w ⟨hm_w, hle', hgt', hsl'⟩ => by
                        subst m_w
                        exact ih_b (hp', off', ()) m0 (by dsimp only; omega) ⟨rfl, hle', hsl'⟩)
                      (fun Jw hJw => by
                        wp_unfold
                        rcases hw0_cases with ⟨hbin, hot_lt, hrest⟩ | ⟨hlrg, h2le, hrest⟩
                        · refine ⟨fun _ => ?_, fun h => absurd h hbin⟩
                          have hot_w : ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                              s0.vals.length := by
                            rw [bv32_zext64_toNat]; omega
                          have hoff1 : (off_b + 1#64).toNat = off_b.toNat + 1 :=
                            bv64_add_const_toNat (k := 1) (by decide) (by omega)
                          refine wp_join_group (fun ((_hp', ()) : Tup Val [.bool]) m_i => m_i = m0)
                            (fun _ ⟨hp', ⟨⟩⟩ m_i hm_i => by
                              subst m_i; wp_unfold
                              exact hJw (hp', off_b + 1#64, ()) m0
                                ⟨rfl, by omega, by omega,
                                  by simpa [hoff1, Nat.sub_sub] using hrest⟩)
                            (fun Ji hJi => by
                              wp_unfold
                              refine ⟨fun _ =>
                                ⟨_, c0_load_arena_vals (i := (w0 &&& 0x7FFFFFFF#32).setWidth 64)
                                  hot_w hm0,
                                  fun _ => hJi (true, ()) m0 rfl,
                                  fun _ => hJi (hp_b, ()) m0 rfl⟩,
                                fun _ => hJi (hp_b, ()) m0 rfl⟩)
                        · refine ⟨fun h => absurd hlrg h, fun _ => ?_⟩
                          have hoff2 : (off_b + 2#64).toNat = off_b.toNat + 2 :=
                            bv64_add_const_toNat (k := 2) (by decide) (by omega)
                          exact hJw (hp_b, off_b + 2#64, ()) m0
                            ⟨rfl, by omega, by omega, by simpa [hoff2, Nat.sub_sub] using hrest⟩)
                · intro Ba hBa; wp_unfold
                  refine ⟨fun hoff_lt => ⟨fun _ => hBa () m0 rfl, fun _ => ?_⟩,
                    fun _ => hBa () m0 rfl⟩
                  have hlt_a : off_a.toNat < endN := by
                    simp only [BitVec.ult, decide_eq_true_eq] at hoff_lt; omega
                  obtain ⟨w0, hw0_get, hw0_cases⟩ := watchSlice_step hsl_a (by omega)
                  have hw0_eq : s0.wstk[off_a.toNat]'(by omega) = w0 := by
                    have := List.getElem?_eq_getElem (l := s.wstk) (i := off_a.toNat) (by omega)
                    rw [this] at hw0_get; exact Option.some.inj hw0_get
                  refine ⟨_, c0_load_arena_wstk (i := off_a) (by omega) hm0, ?_⟩
                  rw [hw0_eq]
                  refine wp_join_group
                    (fun ((_hn', off', ()) : Tup Val [.bool, i64]) m_w =>
                      m_w = m0 ∧ off'.toNat ≤ endN ∧ off_a.toNat < off'.toNat ∧
                      WatchSliceOk c F0 s (2 * vv.toNat + 1) off'.toNat (endN - off'.toNat))
                    (fun _ ⟨hn', off', ⟨⟩⟩ m_w ⟨hm_w, hle', hgt', hsl'⟩ => by
                      subst m_w
                      exact ih_a (hn', off', ()) m0 (by dsimp only; omega) ⟨rfl, hle', hsl'⟩)
                    (fun Jw hJw => by
                      wp_unfold
                      rcases hw0_cases with ⟨hbin, hot_lt, hrest⟩ | ⟨hlrg, h2le, hrest⟩
                      · refine ⟨fun _ => ?_, fun h => absurd h hbin⟩
                        have hot_w : ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                            s0.vals.length := by
                          rw [bv32_zext64_toNat]; omega
                        have hoff1 : (off_a + 1#64).toNat = off_a.toNat + 1 :=
                          bv64_add_const_toNat (k := 1) (by decide) (by omega)
                        refine wp_join_group (fun ((_hn', ()) : Tup Val [.bool]) m_i => m_i = m0)
                          (fun _ ⟨hn', ⟨⟩⟩ m_i hm_i => by
                            subst m_i; wp_unfold
                            exact hJw (hn', off_a + 1#64, ()) m0
                              ⟨rfl, by omega, by omega,
                                by simpa [hoff1, Nat.sub_sub] using hrest⟩)
                          (fun Ji hJi => by
                            wp_unfold
                            refine ⟨fun _ =>
                              ⟨_, c0_load_arena_vals (i := (w0 &&& 0x7FFFFFFF#32).setWidth 64)
                                hot_w hm0,
                                fun _ => hJi (true, ()) m0 rfl,
                                fun _ => hJi (hn_a, ()) m0 rfl⟩,
                              fun _ => hJi (hn_a, ()) m0 rfl⟩)
                      · refine ⟨fun h => absurd hlrg h, fun _ => ?_⟩
                        have hoff2 : (off_a + 2#64).toNat = off_a.toNat + 2 :=
                          bv64_add_const_toNat (k := 2) (by decide) (by omega)
                        exact hJw (hn_a, off_a + 2#64, ()) m0
                          ⟨rfl, by omega, by omega, by simpa [hoff2, Nat.sub_sub] using hrest⟩)
          · intro Jb2 hJb2; wp_unfold
            exact ⟨fun _ => ⟨fun _ => hB2 () m0 rfl, fun _ => hJb2 () m0 rfl⟩,
              fun _ => hJb2 () m0 rfl⟩
    · intro B1 hB1; wp_unfold
      refine ⟨fun hplt_b => ?_, fun _ => hB1 () m0 rfl⟩
      -- `p < alen`: join for `(!hn1 || !hp1)`
      refine wp_join_group (fun () m_b => m_b = m0) ?_ ?_
      · rintro _ ⟨⟩ m_b hm_b; subst m_b
        have hplt : pv.toNat < s.arena_len :=
          bv64_ult_ofNat_true (by omega) hplt_b
        have hpref : pv.toNat ∈ arenaClauseRefs s := by
          rcases hp_mem with heq | hmem
          · omega
          · exact hmem
        have hwf := hinv.core.arena.refs_wf pv.toNat hpref
        have harl : s0.arena.length = c.arena_cap := hlen0.arena_len_arr
        have harl_s : s.arena.length = c.arena_cap := hlen.arena_len_arr
        have hcap : s.arena_len ≤ c.arena_cap := hlen.arena_len_le
        have hp2 : (pv + 2#64).toNat = pv.toNat + 2 :=
          bv64_add_const_toNat (k := 2) (by decide) (by omega)
        wp_unfold
        refine ⟨_, c0_load_arena_arena (i := pv) (by omega) hm0,
          _, c0_load_arena_arena (i := pv + 2#64) (by omega) hm0, ?_⟩
        c0_call hNext; refine ⟨c, s0, R, rfl, hlen0, hm0, ?_⟩
        have hpt32 : (pv.setWidth 32).toNat = pv.toNat := bv64_trunc32_toNat (by omega)
        have hnxt_eq :
            ((BitVec.ofNat 32 (arenaNextOff s0.arena s0.arena_len
              (pv.setWidth 32).toNat)).setWidth 64).toNat =
              arenaNextOff s.arena s.arena_len pv.toNat := by
          rw [bv32_zext64_toNat, hpt32]; dsimp only [s0]
          rw [bv32_ofNat_toNat (by have := hwf.2.2.2.1; omega)]
        have hnxt_gt : pv.toNat < arenaNextOff s.arena s.arena_len pv.toNat :=
          (arenaNextOff_bounds hwf.1).1
        have hnxt_le : arenaNextOff s.arena s.arena_len pv.toNat ≤ s.arena_len := hwf.2.2.2.1
        have hnxt_mem : arenaNextOff s.arena s.arena_len pv.toNat = s.arena_len ∨
            arenaNextOff s.arena s.arena_len pv.toNat ∈ arenaClauseRefs s :=
          if hlt : arenaNextOff s.arena s.arena_len pv.toNat < s.arena_len then
            Or.inr (arenaClauseRefs_next hinv.core.arena hpref hlt)
          else Or.inl (by omega)
        refine wp_join_group
          (fun ((_hn', _hp', ()) : Tup Val [.bool, .bool]) m_if => m_if = m0) ?_ ?_
        · rintro _ ⟨hn', hp', ⟨⟩⟩ m_if hm_if; subst m_if
          exact ih1 (hn', hp', _, ()) m0 (by dsimp only [Arg.val]; rw [hnxt_eq]; omega)
            ⟨rfl, by dsimp only [Arg.val]; rwa [hnxt_eq]⟩
        · intro Jc hJc; wp_unfold
          refine ⟨fun hgarb_b => ⟨fun _ => ⟨fun _ => ?_,
            fun _ => hJc (hn1, hp1, ()) m0 rfl⟩,
            fun _ => hJc (hn1, hp1, ()) m0 rfl⟩,
            fun _ => hJc (hn1, hp1, ()) m0 rfl⟩
          have hgarb : arenaClauseGarb s pv.toNat = false := by
            unfold arenaClauseGarb arenaHdr
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            simpa [s0] using hgarb_b
          have hsz_eq : (s0.arena[(pv + 2#64).toNat]'(by omega)).toNat =
              arenaClauseSize s pv.toNat := by
            unfold arenaClauseSize
            have h1 : s0.arena[(pv + 2#64).toNat]'(by omega) =
                s.arena[pv.toNat + 2]'(by omega) := by simp [s0, hp2]
            rw [h1, List.getElem?_eq_getElem (by omega)]; rfl
          refine wp_loop_inv
            (fun ((_ap, _an, kv, ()) : Tup Val [.bool, .bool, i32]) mk =>
              mk = m0 ∧ kv.toNat ≤ arenaClauseSize s pv.toNat)
            (fun ((_ap, _an, kv, ()) : Tup Val [.bool, .bool, i32]) _ =>
              arenaClauseSize s pv.toNat - kv.toNat) ?_ ?_
          · intro Jk hJk; wp_unfold; exact hJk (false, false, 0#32, ()) m0 ⟨rfl, Nat.zero_le _⟩
          · rintro Jk ⟨ap, an, kv, ⟨⟩⟩ mk ⟨hmk, hkle⟩ ihk; subst mk; wp_unfold
            refine ⟨fun hklt_b => ?_, fun _ => ?_⟩
            · have hklt : kv.toNat < arenaClauseSize s pv.toNat := by
                simp only [BitVec.ult, decide_eq_true_eq] at hklt_b; omega
              have hidx : (pv + 3 + kv.setWidth 64).toNat = pv.toNat + 3 + kv.toNat := by
                have hp3 : (pv + 3).toNat = pv.toNat + 3 :=
                  bv64_add_const_toNat (k := 3) (by decide) (by omega)
                rw [BitVec.toNat_add, hp3, bv32_zext64_toNat,
                  Nat.mod_eq_of_lt (by have := hwf.2.2.1; omega)]
              have hl_mem : (s0.arena[(pv + 3 + kv.setWidth 64).toNat]'(by omega)).toNat ∈
                  arenaClauseLits s pv.toNat := by
                rw [mem_arenaClauseLits_iff (by omega)]
                refine ⟨kv.toNat, hklt, ?_⟩
                simp only [s0, hidx]
              have hl_lt : (s0.arena[(pv + 3 + kv.setWidth 64).toNat]'(by omega)).toNat <
                  2 * c.mv := hinv.core.arena.lits_lt pv.toNat hpref hgarb _ hl_mem
              have hvl : s0.vals.length = 2 * c.mv := hlen0.vals_len
              have hk1 : (kv + 1#32).toNat = kv.toNat + 1 := by
                rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by have := hwf.2.2.1; omega)]
              refine ⟨_, c0_load_arena_arena (i := pv + 3 + kv.setWidth 64) (by omega) hm0, ?_⟩
              generalize hlv : s0.arena[(pv + 3 + kv.setWidth 64).toNat]'(by omega) = lv at hl_lt ⊢
              refine wp_join_group
                (fun ((_ap', _an', ()) : Tup Val [.bool, .bool]) m_k => m_k = m0)
                (fun _ ⟨ap', an', ⟨⟩⟩ m_k hm_k => by
                  subst m_k; wp_unfold
                  exact ihk (ap', an', kv + 1#32, ()) m0
                    (by show arenaClauseSize s pv.toNat - (kv + 1#32).toNat <
                          arenaClauseSize s pv.toNat - kv.toNat; omega)
                    ⟨rfl, by omega⟩)
                (fun Jik hJik => by
                  wp_unfold
                  refine ⟨_, c0_load_arena_vals (i := lv.setWidth 64)
                    (by rw [bv32_zext64_toNat]; omega) hm0, ?_⟩
                  refine ⟨fun _ => ?_, fun _ => hJik (ap, an, ()) m0 rfl⟩
                  refine wp_join_group
                    (fun ((_ap', _an', ()) : Tup Val [.bool, .bool]) m_j => m_j = m0)
                    (fun _ ⟨ap', an', ⟨⟩⟩ m_j hm_j => by
                      subst m_j; exact hJik (ap', an', ()) m0 rfl)
                    (fun Jj hJj => by
                      wp_unfold
                      exact ⟨fun _ => hJj (true, an, ()) m0 rfl,
                        fun _ => hJj (ap, true, ()) m0 rfl⟩))
            · refine wp_join_group (fun ((_hn', ()) : Tup Val [.bool]) m_p => m_p = m0)
                (fun _ ⟨hn', ⟨⟩⟩ m_p hm_p => by
                  subst m_p
                  refine wp_join_group (fun ((_hp', ()) : Tup Val [.bool]) m_q => m_q = m0)
                    (fun _ ⟨hp', ⟨⟩⟩ m_q hm_q => by subst m_q; exact hJc (hn', hp', ()) m0 rfl)
                    (fun Jq hJq => by
                      wp_unfold
                      exact ⟨fun _ => hJq (hp1, ()) m0 rfl, fun _ => hJq (true, ()) m0 rfl⟩))
                (fun Jp hJp => by
                  wp_unfold
                  exact ⟨fun _ => hJp (hn1, ()) m0 rfl, fun _ => hJp (true, ()) m0 rfl⟩)
      · intro Jb1 hJb1; wp_unfold
        exact ⟨fun _ => ⟨fun _ => hB1 () m0 rfl, fun _ => hJb1 () m0 rfl⟩,
          fun _ => hJb1 () m0 rfl⟩

end LuckyProofs

end LeanQbe.T.Examples.Kissat.Plain
