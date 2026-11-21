module

public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullWalkExtLemmas1
public import LeanQbe.T.Examples.Kissat.FullBveBvaLemmas3
public import LeanQbe.T.Examples.Kissat.FullBveVarLemmas2
public import LeanQbe.T.Examples.Kissat.FullSpec
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` M2 `TmkZero`-Preserving M1 Helper Proofs (`FullFastTmkLemmas`)

Proves the `4` unchanged M1 helper functions against the `TmkZero`-preserving contracts in
`FullFastBveBudgets` (zero edits to any M1 file, zero SAT/model proofs):
1. `fast_extend_push2_tmk_wp` (`Full.full_extend_push2_body` → `fullExtendPush2TmkSpec`)
2. `fast_extend_push_cl_tmk_wp` (`Full.full_extend_push_cl_body` → `fullExtendPushClTmkSpec`)
3. `fast_bve_weaken_tmk_wp` (`Full.full_bve_weaken_body` → `fullBveWeakenTmkSpec`)
4. `fast_bve_commit_res_tmk_wp` (`Full.full_bve_commit_res_body` → `fullBveCommitResTmkSpec`)
Plus the 1-line `fast_extend_push2_adapter` weakening `fullExtendPush2TmkSpec` to canonical
`Full.fullExtendPush2Spec` for `full_subst_elim_vars_bridge_wp`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFast

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open Kraken.Bedrock2.Test

/-! ## 1. `TmkZero`-preserving `full_extend_push2` & `full_extend_push_cl` -/

section ExtendTmk

open FullWalkExtSpecs FullWalkExtHelpers
open scoped FullArenaTactics FullWalkExtTactics

/-- Weakens a `fullExtendPush2TmkSpec` env hypothesis to canonical `Full.fullExtendPush2Spec`. -/
theorem fast_extend_push2_adapter {Γ : Env}
    (h : ∀ xs m Q X, fullExtendPush2TmkSpec xs m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] xs m Q X) :
    ∀ xs m Q X, Full.fullExtendPush2Spec xs m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] xs m Q X := by
  rintro ⟨h_ptr, blk, ot, ⟨⟩⟩ m Q X ⟨c, s, R, hpre, hlen, hm, hQ⟩
  exact h _ m Q X ⟨c, s, R, hpre, hlen, hm,
    fun r s' m' hcore hlen' ⟨h1, h2, h3, _⟩ hm' => hQ r s' m' hcore hlen' ⟨h1, h2, h3⟩ hm'⟩

theorem fast_extend_push2_tmk_wp (Γ : Env) :
    ∀ a m Q X, fullExtendPush2TmkSpec a m Q X →
      Func.wp Γ Full.full_extend_push2_body a m Q X := by
  rintro ⟨h, blk_lit, other, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hel⟩, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hlen hm hQ
  obtain hcap : c.extend_cap < dimacsBound := c.hext
  unfold dimacsBound at hcap
  obtain hesl := hlen.scratch_ok.extend_stk_len
  c0_steps
  · exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl, rfl⟩ hm
  · have hfit : s.scratch.extend_len + 2 ≤ c.extend_cap := by bv_omega
    have hi0 : (BitVec.ofNat 64 s.scratch.extend_len).toNat < s.scratch.extend_stk.length := by
      rw [hesl]; bv_omega
    have hi1 : (BitVec.ofNat 64 s.scratch.extend_len + 1).toNat <
        ((s.scratch.extend_stk.set (BitVec.ofNat 64 s.scratch.extend_len).toNat
          (blk_lit ||| 0x80000000#32))).length := by
      rw [List.length_set, hesl]; bv_omega
    have hadd2 : (BitVec.ofNat 64 s.scratch.extend_len + 2).toNat =
        s.scratch.extend_len + 2 := by bv_omega
    have hel' : (BitVec.ofNat 64 s.scratch.extend_len + 2).toNat ≤ c.extend_cap := hadd2 ▸ hfit
    c0_steps
    let s' : FullState :=
      { s with scratch := { s.scratch with
        extend_stk := (s.scratch.extend_stk.set (BitVec.ofNat 64 s.scratch.extend_len).toNat
          (blk_lit ||| 0x80000000#32)).set (BitVec.ofNat 64 s.scratch.extend_len + 1).toNat
          (other &&& 0x7FFFFFFF#32),
        extend_len := (BitVec.ofNat 64 s.scratch.extend_len + 2).toNat } }
    exact hQ (true, ()) s' _ rfl
      (hlen.with_scratch { hlen.scratch_ok with extend_stk_len := by simp [hesl] })
      ⟨rfl, hel', rfl, rfl⟩ hm

theorem fast_extend_push_cl_tmk_wp (Γ : Env) :
    ∀ a m Q X, fullExtendPushClTmkSpec a m Q X →
      Func.wp Γ Full.full_extend_push_cl_body a m Q X := by
  rintro ⟨h, blk_lit, cref, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hel⟩, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hlen hm hQ
  obtain haca : c.arena_cap < 2 * dimacsBound := c.harena
  obtain heca : c.extend_cap < dimacsBound := c.hext
  unfold dimacsBound at haca heca
  obtain harl := hlen.core_ok.arena_len_arr
  obtain hale := hlen.core_ok.arena_len_le
  obtain hesl := hlen.scratch_ok.extend_stk_len
  c0_steps
  · exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl, rfl⟩ hm
  · exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl, rfl⟩ hm
  · exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl, rfl⟩ hm
  · rename_i h_ar2 h_ar3
    have hcr3 : cref.toNat + 3 ≤ s.core.arena_len := by bv_omega
    have hcr2_eq : (cref.setWidth 64 + 2).toNat = cref.toNat + 2 := by bv_omega
    have hcr2_lt : (cref.setWidth 64 + 2).toNat < s.core.arena.length := by
      rw [hcr2_eq, harl]; omega
    let sz := (s.core.arena[cref.toNat + 2]'(by omega)).toNat
    have hsz32 : sz < 2 ^ 32 := (s.core.arena[cref.toNat + 2]'(by omega)).isLt
    have hc3sz : cref.toNat + 3 + sz ≤ s.core.arena_len := by
      simp only [show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
        show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
        Nat.mod_eq_of_lt (by omega : cref.toNat + 2 < 2 ^ 64)] at h_ar3
      dsimp only [sz]; bv_omega
    have hext1sz : s.scratch.extend_len + 1 + sz ≤ c.extend_cap := by
      simp only [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
        show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
        Nat.mod_eq_of_lt (by omega : cref.toNat + 2 < 2 ^ 64)] at hc
      dsimp only [sz]; bv_omega
    clear hc h_ar3
    have hp0_lt : (BitVec.ofNat 64 s.scratch.extend_len).toNat <
        s.scratch.extend_stk.length := by rw [hesl]; bv_omega
    c0_to_group
    refine wp_loop_inv
      (fun ((p : BitVec 64), (i : BitVec 32), ()) m1 =>
        i.toNat ≤ sz ∧ p.toNat ≤ s.scratch.extend_len + 1 + i.toNat ∧
        ∃ ext1 : List (BitVec 32), ext1.length = c.extend_cap ∧
          (FullMem c { s with scratch := { s.scratch with extend_stk := ext1 } } ⋆ R) m1)
      (fun ((_ : BitVec 64), (i : BitVec 32), ()) _ => sz - i.toNat) (fun J hLoop => ?_)
      (fun J ((p : BitVec 64), (i : BitVec 32), ()) m1 ⟨hle_sz, hp_ub, ext1, hext1_len, hm1⟩
          hLoop => ?_)
    · c0_steps
      refine hLoop _ _ ⟨by simp, by bv_omega, _, by rw [List.length_set, hesl], hm⟩
    · c0_split
      · simp only [show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
          Nat.mod_eq_of_lt (by omega : cref.toNat + 2 < 2 ^ 64)] at hc
        have hi_lt : i.toNat < sz := hc
        have hli_eq : (cref.setWidth 64 + 3 + i.setWidth 64).toNat = cref.toNat + 3 + i.toNat := by
          bv_omega
        have hli_lt : (cref.setWidth 64 + 3 + i.setWidth 64).toNat < s.core.arena.length := by
          rw [hli_eq, harl]; omega
        refine wp_load_of (FullArenaTactics.c0_load_full_arena
          (s := { s with scratch := { s.scratch with extend_stk := ext1 } }) hli_lt hm1) ?_
        have hi1 : (i + 1).toNat = i.toNat + 1 := by bv_omega
        refine wp_join_group
          (fun (p', ()) m' =>
            p'.toNat ≤ s.scratch.extend_len + 1 + (i.toNat + 1) ∧
            ∃ ext2 : List (BitVec 32), ext2.length = c.extend_cap ∧
              (FullMem c { s with scratch := { s.scratch with extend_stk := ext2 } } ⋆ R) m')
          (fun Js (p', ()) m' ⟨hp'ub, ext2, hext2_len, hm'⟩ => ?_) (fun Js hJs => ?_)
        · c0_steps
          refine hLoop (p', i + 1, ()) m' ?_ ⟨?_, ?_, ext2, hext2_len, hm'⟩
          · dsimp only; rw [hi1]; omega
          · rw [hi1]; omega
          · rw [hi1]; exact hp'ub
        · c0_split
          · have hp_lt_cap : p.toNat < c.extend_cap := by omega
            have hp_lt_ext1 : p.toNat < ext1.length := by rw [hext1_len]; exact hp_lt_cap
            c0_steps
            refine wp_store_sep (FullArenaTactics.c0_store_full_extend_stk _ hp_lt_ext1 hm1)
              fun m hm => ?_
            c0_steps
            have hp1 : (p + 1).toNat = p.toNat + 1 := by bv_omega
            exact hJs (p + 1, ()) m ⟨by omega, _, by rw [List.length_set, hext1_len], hm⟩
          · exact hJs (p, ()) m1 ⟨by omega, ext1, hext1_len, hm1⟩
      · have hcr2_mod : (cref.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = cref.toNat + 2 := by
          rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
        simp only [hcr2_mod] at hc
        have hieq : i.toNat = sz := by dsimp only [sz] at *; omega
        have hp_fin : p.toNat ≤ c.extend_cap := by rw [hieq] at hp_ub; omega
        c0_steps
        refine wp_store_sep (FullArenaTactics.c0_store_full_extend_len p hm1) fun m hm => ?_
        c0_steps
        let s' : FullState :=
          { s with scratch := { s.scratch with extend_stk := ext1, extend_len := p.toNat } }
        exact hQ (true, ()) s' m rfl
          ⟨hlen.core_ok, { hlen.scratch_ok with extend_stk_len := hext1_len }⟩
          ⟨rfl, hp_fin, rfl, rfl⟩ hm

end ExtendTmk

/-! ## 2. `TmkZero`-preserving `full_bve_weaken` -/

section WeakenTmk

open FullBveBvaTactics FullBveBvaSpecs FullBveBvaHelpers
open scoped FullArenaTactics FullBveBvaTactics

theorem fast_bve_weaken_tmk_wp (Γ : Env)
    (hExtPush2 : ∀ xs m Q X, fullExtendPush2TmkSpec xs m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] xs m Q X)
    (hDelBin : ∀ xs m Q X, Full.fullDeleteBinarySpec xs m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] xs m Q X)
    (hExtPushCl : ∀ xs m Q X, fullExtendPushClTmkSpec xs m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] xs m Q X) :
    ∀ args m Q X, fullBveWeakenTmkSpec args m Q X →
      Func.wp Γ Full.full_bve_weaken_body args m Q X := by
  rintro ⟨h, blk_lit, off, cnt, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hdw, htmk0, hblk, hoff, hitems, hm, hQ⟩
  have hmv := c.hmaxv; have hsc := c.hscr; have harc := c.harena
  unfold dimacsBound at hmv hsc harc
  unfold Func.wp Full.full_bve_weaken_body
  bve_steps!
  refine wp_loop_inv (ts := [i32])
    (fun (i, _) mi =>
      i.toNat ≤ cnt.toNat ∧
      ∃ si, FullBveBvaSpecs.FullDenseInvW c F0 F_cur si ∧ TmkZero si ∧
        si.core.cur_vars = s.core.cur_vars ∧ si.core.fuel = s.core.fuel ∧
        si.scratch.scratch_buf = s.scratch.scratch_buf ∧
        fullArenaClauseRefs si = fullArenaClauseRefs s ∧
        (FullMem c si ⋆ R) mi)
    (fun (i, _) _ => cnt.toNat - i.toNat)
    ?_ ?_
  · intro J hJ; bve_steps!
    exact hJ (0#32, PUnit.unit) m ⟨Nat.zero_le _, s, hdw, htmk0, rfl, rfl, rfl, rfl, hm⟩
  · rintro J ⟨i, ⟨⟩⟩ mi ⟨hi_le, si, hdw_i, htmk_i, hcv_eq, hfuel_eq, hscr_eq, hrefs_eq, hm_i⟩ ih
    have hcl_i := hdw_i.1.core_ok; have hsl_i := hdw_i.1.scratch_ok
    have hscrl_i : si.scratch.scratch_buf.length = c.scratch_cap := hsl_i.scratch_buf_len
    have harl_i : si.core.arena.length = c.arena_cap := hcl_i.arena_len_arr
    have harle_i : si.core.arena_len ≤ c.arena_cap := hcl_i.arena_len_le
    bve_steps
    · have hi_lt : i.toNat < cnt.toNat := by bv_omega
      have hoff_nat : (off + i).toNat = off.toNat + i.toNat := by bv_omega
      have hscr_lt : (BitVec.setWidth 64 (off + i)).toNat < si.scratch.scratch_buf.length := by
        rw [bv_c0_zext32_64, hscrl_i, hoff_nat]; omega
      have hw_eq : si.scratch.scratch_buf[(off + i).toNat]'(by
          rw [hscrl_i, hoff_nat]; omega) = s.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 :=
        Option.some.inj (by
          rw [← List.getElem?_eq_getElem (by rw [hscrl_i, hoff_nat]; omega), hscr_eq, hoff_nat,
            List.getElem?_eq_getElem (by rw [hdw.1.scratch_ok.scratch_buf_len]; omega)]; rfl)
      have hitem_i := hitems i.toNat hi_lt
      unfold Full.FullBveWeakItemOk at hitem_i
      have hbin : (si.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_lt &&&
          0x80000000#32) ≠ 0#32 := hc
      refine wp_call_of_spec _ _ (hExtPush2 _ mi _ X ⟨c, si, R,
        ⟨rfl, hdw_i.2.2.2.2.1.2⟩, hdw_i.1, hm_i, ?_⟩)
      rintro ok s1 m1 hcore1 hlen1 ⟨hll1, hel1, hscr1, htmk1_eq⟩ hm1
      dsimp only [fullSafetySlice_mem] at hm1
      have ⟨hdw1, hcv1, hfuel1, hrefs1⟩ := weaken_ext_step hdw_i hlen1 hcore1 hll1 hel1
      have htmk1 : TmkZero s1 := htmk_i.congr hcv1 htmk1_eq
      bve_steps!
      · refine wp_call_of_spec _ _ (hDelBin _ m1 _ X ⟨c, s1, R, rfl, hdw1.1,
          hdw1.2.1.watches.layout, hm1, ?_⟩)
        intro wvec' wstk' wu' nb' m2 _ hlen2 _hwl2 hwat2 hm2
        let s2 : FullState :=
          { s1 with core := { s1.core with
            wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } }
        have hdw2 := fullDenseInvW_of_delete_binary hdw1 hlen2 hwat2
        have htmk2 : TmkZero s2 := htmk1.congr rfl rfl
        have hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s1 := by
          unfold fullArenaClauseRefs fullArenaClauseRefsCore; rfl
        bve_steps!
        exact ih (i + 1#32, PUnit.unit) m2 (by bv_omega) ⟨by bv_omega, s2, hdw2, htmk2,
          hcv1.trans hcv_eq, hfuel1.trans hfuel_eq, hscr1.trans hscr_eq,
          hrefs2.trans (hrefs1.trans hrefs_eq), hm2⟩
      · exact hQ false s1 m1 hdw1 htmk1 (hcv1.trans hcv_eq) (hfuel1.trans hfuel_eq)
          (hscr1.trans hscr_eq) (hrefs1.trans hrefs_eq) hm1
    · have hi_lt : i.toNat < cnt.toNat := by bv_omega
      have hoff_nat : (off + i).toNat = off.toNat + i.toNat := by bv_omega
      have hscr_lt : (BitVec.setWidth 64 (off + i)).toNat < si.scratch.scratch_buf.length := by
        rw [bv_c0_zext32_64, hscrl_i, hoff_nat]; omega
      have hw_eq : si.scratch.scratch_buf[(off + i).toNat]'(by
          rw [hscrl_i, hoff_nat]; omega) = s.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 :=
        Option.some.inj (by
          rw [← List.getElem?_eq_getElem (by rw [hscrl_i, hoff_nat]; omega), hscr_eq, hoff_nat,
            List.getElem?_eq_getElem (by rw [hdw.1.scratch_ok.scratch_buf_len]; omega)]; rfl)
      have hitem_i := hitems i.toNat hi_lt
      unfold Full.FullBveWeakItemOk at hitem_i
      have hnb : ¬ (s.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 &&&
          0x80000000#32) ≠ 0#32 := by
        intro hne
        have hhc : si.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_lt &&&
            0x80000000#32 = 0#32 := hc
        simp only [bv_c0_zext32_64] at hhc; rw [hw_eq] at hhc; exact hne hhc
      rw [ite_eq_right hnb] at hitem_i
      have hitem_ref : (si.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_lt
          ).toNat ∈ fullArenaClauseRefs si := by
        simp only [bv_c0_zext32_64]; rw [hw_eq, hrefs_eq]; exact hitem_i
      refine wp_call_of_spec _ _ (hExtPushCl _ mi _ X ⟨c, si, R,
        ⟨rfl, hdw_i.2.2.2.2.1.2⟩, hdw_i.1, hm_i, ?_⟩)
      rintro ok s1 m1 hcore1 hlen1 ⟨hll1, hel1, hscr1, htmk1_eq⟩ hm1
      dsimp only [fullSafetySlice_mem] at hm1
      have ⟨hdw1, hcv1, hfuel1, hrefs1⟩ := weaken_ext_step hdw_i hlen1 hcore1 hll1 hel1
      have htmk1 : TmkZero s1 := htmk_i.congr hcv1 htmk1_eq
      have heq_core : s1.core = si.core := fullCoreState_agrees_with_scratch hcore1
      let w := si.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_lt
      have hw_ref1 : w.toNat ∈ fullArenaClauseRefs s1 := by
        unfold fullArenaClauseRefs; rw [heq_core]; exact hitem_ref
      have hwf1 := hdw1.2.1.arena.refs_wf w.toNat hw_ref1
      have har1 : s1.core.arena.length = c.arena_cap := hlen1.core_ok.arena_len_arr
      have harle1 : s1.core.arena_len ≤ c.arena_cap := hlen1.core_ok.arena_len_le
      have hbd1 : w.toNat + 3 + fullArenaClauseSize s1 w.toNat ≤ s1.core.arena_len := by
        unfold fullArenaClauseSize; omega
      have hw_ar : (BitVec.setWidth 64 w).toNat < s1.core.arena.length := by
        rw [bv_c0_zext32_64]; omega
      have hw2_ar : (BitVec.setWidth 64 w + 2).toNat < s1.core.arena.length := by bv_omega
      have hw_lt_ar : (si.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_lt).toNat +
          2 < s1.core.arena.length := by change w.toNat + 2 < _; omega
      bve_steps!
      · let w_hm := si.scratch.scratch_buf[(off + i).toNat]'(by rw [hscrl_i, hoff_nat]; omega)
        have hw_hm_eq : w_hm = w := Option.some.inj (by
          dsimp only [w_hm, w]
          rw [← List.getElem?_eq_getElem (by rw [hscrl_i, hoff_nat]; omega),
            ← List.getElem?_eq_getElem hscr_lt, bv_c0_zext32_64])
        have hw_hm_ref : w_hm.toNat ∈ fullArenaClauseRefs s1 := by rw [hw_hm_eq]; exact hw_ref1
        have hw_hm_ar : w_hm.toNat < s1.core.arena.length := by
          have h1 := hw_ar; rw [bv_c0_zext32_64, ← hw_hm_eq] at h1; exact h1
        have hw2_hm_ar : (BitVec.setWidth 64 w_hm + 2).toNat <
            (s1.core.arena.set w_hm.toNat
              (s1.core.arena[w_hm.toNat]'hw_hm_ar ||| 0x00080000#32)).length := by
          rw [List.length_set, hw_hm_eq]; exact hw2_ar
        let ag_hm := s1.core.arena_garbage + 3 + BitVec.setWidth 64
          ((s1.core.arena.set w_hm.toNat
            (s1.core.arena[w_hm.toNat]'hw_hm_ar ||| 0x00080000#32))[(BitVec.setWidth 64 w_hm +
              2).toNat]'hw2_hm_ar)
        have ⟨hrefs2, hdw2⟩ := weaken_markGarb_step hw_hm_ref hw_hm_ar ag_hm hdw1
        exact ih (i + 1#32, PUnit.unit) m (by bv_omega) ⟨by bv_omega, _, hdw2,
          htmk1.congr rfl rfl, hcv1.trans hcv_eq, hfuel1.trans hfuel_eq, hscr1.trans hscr_eq,
          hrefs2.trans (hrefs1.trans hrefs_eq), hm⟩
      · exact hQ false s1 m1 hdw1 htmk1 (hcv1.trans hcv_eq) (hfuel1.trans hfuel_eq)
          (hscr1.trans hscr_eq) (hrefs1.trans hrefs_eq) hm1
    · bve_steps!
      exact hQ true si mi hdw_i htmk_i hcv_eq hfuel_eq hscr_eq hrefs_eq hm_i

end WeakenTmk

/-! ## 3. `TmkZero`-preserving `full_bve_commit_res` -/

section CommitResTmk

open FullBveVarTactics FullBveVarSpecs FullBveVarHelpers
open scoped FullArenaTactics FullBveVarTactics

private theorem denseInvW_of_full {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : Full.FullDenseInvW c F0 F_cur s) :
    FullBveVarSpecs.FullDenseInvW c F0 F_cur s := h

private theorem denseInvW_to_full {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullBveVarSpecs.FullDenseInvW c F0 F_cur s) :
    Full.FullDenseInvW c F0 F_cur s := h

private theorem resBuf_to_bve {F_cur : List (List Nat)} {s : FullState} {r_end p : Nat}
    (h : Full.FullResBufOkW F_cur s r_end p) : FullBveVarSpecs.FullResBufOkW F_cur s r_end p := by
  induction h with
  | nil => exact .nil
  | cons hbd hsz hlts hnd hent _ ih => exact .cons hbd hsz hlts hnd hent ih

private theorem commit_res_garb_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sl : FullState} {ark : List (BitVec 32)} {wvec' wstk' wsort' : List (BitVec 32)}
    {wlen' : Nat} {wu' ag' : BitVec 64} {sz : Nat}
    (hinv : FullBveVarSpecs.FullDenseInvW c F0 F_cur sl)
    (hsz_ge3 : 3 ≤ sz) (hark_len : ark.length = c.arena_cap)
    (hark_hold : ∀ i < sl.core.arena_len, ark[i]? = sl.core.arena[i]?)
    (hns2 : (ark[sl.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hsz2_ar : (ark[sl.core.arena_len + 2]?.getD 0#32).toNat = sz)
    (har_cr_idx : sl.core.arena_len < ark.length)
    (hlenw' : ({ sl with
      core := { sl.core with arena := ark, arena_len := sl.core.arena_len + 3 + sz,
                             wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
      scratch := { sl.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hwatw' : ModeWatchesInv F_cur
      { sl.core with arena := ark, arena_len := sl.core.arena_len + 3 + sz,
                     wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' })
    (hrefs2 : fullArenaClauseRefsCore
      { sl.core with arena := ark, arena_len := sl.core.arena_len + 3 + sz } =
      fullArenaClauseRefsCore sl.core ++ [sl.core.arena_len]) :
    let cr0 := sl.core.arena_len
    let ark_g := ark.set cr0 ((ark[cr0]'har_cr_idx) ||| 0x00080000#32)
    Full.FullDenseInvW c F0 F_cur
      { sl with
        core := { sl.core with
          arena := ark_g, arena_len := cr0 + 3 + sz,
          wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
          arena_garbage := ag', oom := 1#64 }
        scratch := { sl.scratch with wsort := wsort' } } := by
  intro cr0 ark_g
  let s_ws : FullState := { sl with scratch := { sl.scratch with wsort := wsort' } }
  have hinv_ws : FullBveVarSpecs.FullDenseInvW c F0 F_cur s_ws :=
    ⟨⟨hinv.1.core_ok, { hinv.1.scratch_ok with wsort_len := hlenw'.scratch_ok.wsort_len }⟩,
     hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩
  have hhold_g : ∀ i < cr0, ark_g[i]? = sl.core.arena[i]? :=
    fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hark_hold i hi
  have hns_g : (ark_g[cr0]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
    rw [List.getElem?_set_self har_cr_idx, Option.getD_some, bv32_bit23_or_garb]
    have := hns2; rw [List.getElem?_eq_getElem har_cr_idx, Option.getD_some] at this; exact this
  have hng_g : (ark_g[cr0]?.getD 0#32 &&& 0x00080000#32) ≠ 0#32 := by
    rw [List.getElem?_set_self har_cr_idx, Option.getD_some]; exact bv32_bit19_or_garb_ne0 _
  have hsz_g : (ark_g[cr0 + 2]?.getD 0#32).toNat = sz := by
    rw [List.getElem?_set_ne (by omega)]; exact hsz2_ar
  have hlen_g : ({ s_ws with
    core := { s_ws.core with
      arena := ark_g, arena_len := cr0 + 3 + sz,
      wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
      arena_garbage := ag', oom := 1#64 } } : FullState).LengthsOk c :=
    ⟨{ hlenw'.core_ok with arena_len_arr := by simp [ark_g, hark_len] }, hlenw'.scratch_ok⟩
  have hrefs_g : fullArenaClauseRefsCore
      { s_ws.core with arena := ark_g, arena_len := cr0 + 3 + sz } =
      fullArenaClauseRefsCore sl.core ++ [cr0] :=
    fullArenaClauseRefsCore_append hinv.2.1.arena hsz_ge3 rfl hhold_g hns_g hsz_g
  have hwat_g : ModeWatchesInv F_cur
      { s_ws.core with
        arena := ark_g, arena_len := cr0 + 3 + sz,
        wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
        arena_garbage := ag', oom := 1#64 } :=
    hwatw'.with_wstk rfl rfl rfl rfl rfl (fun r hr => by
      change r ∈ fullArenaClauseRefsCore
        { sl.core with arena := ark, arena_len := cr0 + 3 + sz } at hr
      rw [hrefs2] at hr; exact hrefs_g ▸ hr)
  exact denseInvW_to_full (addGarbageClause_preserves_witness hinv_ws hlen_g hsz_ge3
    hhold_g hns_g hng_g hsz_g hwat_g)

private theorem commit_res_entailed_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sl : FullState} {ark : List (BitVec 32)} {wvecw wstkw wsortw : List (BitVec 32)}
    {wlenw : Nat} {wuw : BitVec 64} {p_nat sz : Nat}
    (hinv : FullBveVarSpecs.FullDenseInvW c F0 F_cur sl)
    (hsz_ge3 : 3 ≤ sz)
    (hlts : ∀ k < sz, (sl.scratch.scratch_buf[p_nat + 1 + k]?.getD 0#32).toNat <
      2 * sl.core.cur_vars)
    (hnd : ((List.range sz).map fun k =>
      (sl.scratch.scratch_buf[p_nat + 1 + k]?.getD 0#32).toNat / 2).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause ((List.range sz).map fun k =>
      (sl.scratch.scratch_buf[p_nat + 1 + k]?.getD 0#32).toNat)))
    (hark_hold : ∀ i < sl.core.arena_len, ark[i]? = sl.core.arena[i]?)
    (hns2 : (ark[sl.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hsz2_ar : (ark[sl.core.arena_len + 2]?.getD 0#32).toNat = sz)
    (hlits_eq : fullArenaClauseLitsCore
      { sl.core with arena := ark, arena_len := sl.core.arena_len + 3 + sz } sl.core.arena_len =
      (List.range sz).map fun j => (sl.scratch.scratch_buf[p_nat + 1 + j]?.getD 0#32).toNat)
    (hlenw : ({ sl with
      core := { sl.core with arena := ark, arena_len := sl.core.arena_len + 3 + sz,
                             wvec := wvecw, wstk := wstkw, wlen := wlenw, wusable := wuw }
      scratch := { sl.scratch with wsort := wsortw } } : FullState).LengthsOk c)
    (hwatw : ModeWatchesInv F_cur
      { sl.core with arena := ark, arena_len := sl.core.arena_len + 3 + sz,
                     wvec := wvecw, wstk := wstkw, wlen := wlenw, wusable := wuw }) :
    let cr0 := sl.core.arena_len
    FullBveVarSpecs.FullDenseInvW c F0 F_cur
      { sl with
        core := { sl.core with
          arena := ark, arena_len := cr0 + 3 + sz,
          wvec := wvecw, wstk := wstkw, wlen := wlenw, wusable := wuw,
          num_irred := sl.core.num_irred + 1#64 }
        scratch := { sl.scratch with wsort := wsortw } } := by
  intro cr0
  let s_ws : FullState := { sl with scratch := { sl.scratch with wsort := wsortw } }
  have hinv_ws : FullBveVarSpecs.FullDenseInvW c F0 F_cur s_ws :=
    ⟨⟨hinv.1.core_ok, { hinv.1.scratch_ok with wsort_len := hlenw.scratch_ok.wsort_len }⟩,
     hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩
  have hlen_c : ({ s_ws with
    core := { s_ws.core with
      arena := ark, arena_len := cr0 + 3 + sz,
      wvec := wvecw, wstk := wstkw, wlen := wlenw, wusable := wuw,
      num_irred := sl.core.num_irred + 1#64 } } : FullState).LengthsOk c :=
    ⟨{ hlenw.core_ok with arena_len_arr := hlenw.core_ok.arena_len_arr }, hlenw.scratch_ok⟩
  have hwat_c : ModeWatchesInv F_cur
      { s_ws.core with
        arena := ark, arena_len := cr0 + 3 + sz,
        wvec := wvecw, wstk := wstkw, wlen := wlenw, wusable := wuw,
        num_irred := sl.core.num_irred + 1#64 } :=
    hwatw.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
  exact addEntailedClause_preserves_witness hinv_ws hlen_c hsz_ge3
    (fun l hl => by
      have hl' : l ∈ (List.range sz).map fun j =>
          (sl.scratch.scratch_buf[p_nat + 1 + j]?.getD 0#32).toNat := by
        simpa only [← hlits_eq] using hl
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl'
      rw [List.mem_range] at hj; exact hlts j hj)
    (by rw [hlits_eq, List.map_map]; simpa only [Function.comp_def] using hnd)
    (by rw [hlits_eq]; exact hent)
    hark_hold hns2 hsz2_ar hwat_c

private theorem bveAddUnit_adapter {Γ : Env}
    (hAddUnit : ∀ a m Q X, Full.fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullBveVarSpecs.fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hent, hm, hQ⟩
  refine hAddUnit _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hent, hm,
    fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
      phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m' hlen' hw' hcl0 hltf hof hm' => ?_⟩
  exact hQ ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
    { s.scratch with
      phases := phases', target_assigned := ta', best_assigned := ba',
      phases_target := pt', phases_best := pb', heap := hp', pos := ps',
      heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' }
    m' hlen' hw' ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hcl0 hltf hof hm'

private theorem commit_arenaLits_eq_copied {k : FullCoreState} {scr : List (BitVec 32)}
    {cr0 p1 sz : Nat} (hbd : cr0 + 3 + sz ≤ k.arena.length) (hscr : p1 + sz ≤ scr.length)
    (hsz : (k.arena[cr0 + 2]?.getD 0#32).toNat = sz)
    (hcp : ∀ j < sz, k.arena[cr0 + 3 + j]? = scr[p1 + j]?) :
    fullArenaClauseLitsCore k cr0 =
      (List.range sz).map fun j => (scr[p1 + j]?.getD 0#32).toNat := by
  unfold fullArenaClauseLitsCore fullArenaClauseSizeCore
  rw [hsz]
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop,
      Nat.min_eq_left (by omega : sz ≤ k.arena.length - (cr0 + 3))]
  · intro j hj1 _
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range]
    have hj : j < sz := by simp [List.length_take, List.length_drop] at hj1; omega
    have hlt_ar : cr0 + 3 + j < k.arena.length := by omega
    have hlt_scr : p1 + j < scr.length := by omega
    have heq := hcp j hj
    rw [List.getElem?_eq_getElem hlt_ar, List.getElem?_eq_getElem hlt_scr, Option.some.injEq]
      at heq
    rw [List.getElem?_eq_getElem hlt_scr, Option.getD_some, heq]

private theorem commit_resBuf_head_step {F_cur : List (List Nat)} {s : FullState} {r_end p : Nat}
    (hres : FullBveVarSpecs.FullResBufOkW F_cur s r_end p) (hlt : p < r_end) :
    p + 1 + (s.scratch.scratch_buf[p]?.getD 0#32).toNat ≤ r_end ∧
      let sz := (s.scratch.scratch_buf[p]?.getD 0#32).toNat
      (∀ k < sz, (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      ((List.range sz).map fun k =>
        (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2).Nodup ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause ((List.range sz).map fun k =>
        (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat)) ∧
      FullBveVarSpecs.FullResBufOkW F_cur s r_end (p + 1 + sz) := by
  cases hres with
  | nil => exact absurd hlt (Nat.lt_irrefl _)
  | @cons _ sz0 hbd hsz hlts hnd hent htail =>
    subst hsz; exact ⟨hbd, hlts, hnd, hent, htail⟩

theorem fast_bve_commit_res_tmk_wp (Γ : Env)
    (hAlloc : ∀ xs m Q X, Full.fullAllocClSpec xs m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] xs m Q X)
    (hWPush : ∀ xs m Q X, Full.fullWatchPushSpec xs m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] xs m Q X)
    (hAddBin : ∀ xs m Q X, Full.fullAddBinSpec xs m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] xs m Q X)
    (hAddUnit : ∀ xs m Q X, Full.fullAddUnitSpec xs m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] xs m Q X) :
    ∀ args m Q X, fullBveCommitResTmkSpec args m Q X →
      Func.wp Γ Full.full_bve_commit_res_body args m Q X := by
  let hAU := bveAddUnit_adapter hAddUnit
  rintro ⟨h, r_off, r_end, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv0, htmk0, hle0, hcap0, hbuf0, hm0, hQ⟩
  have hmv := c.hmaxv; have harc := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmv harc hsc
  unfold Func.wp Full.full_bve_commit_res_body
  bve_steps!
  refine wp_loop_inv (ts := [i64])
    (fun (p, _) ml =>
      ∃ sl,
        FullBveVarSpecs.FullDenseInvW c F0 F_cur sl ∧ TmkZero sl ∧
        sl.core.cur_vars = s.core.cur_vars ∧ sl.core.fuel = s.core.fuel ∧ p.toNat ≤ r_end.toNat ∧
        FullBveVarSpecs.FullResBufOkW F_cur sl r_end.toNat p.toNat ∧ (FullMem c sl ⋆ R) ml)
    (fun (p, _) _ => r_end.toNat - p.toNat)
    (fun J hJ => by
      bve_steps!
      exact hJ (r_off, PUnit.unit) m
        ⟨s, denseInvW_of_full hinv0, htmk0, rfl, rfl, hle0, resBuf_to_bve hbuf0, hm0⟩)
    (fun J ⟨p, ⟨⟩⟩ ml ⟨sl, hinv, htmk, hcv_eq, hfl_eq, hp_le, hres, hm_lp⟩ ih => by
      have hcl := hinv.1.core_ok; have hsl := hinv.1.scratch_ok
      have hscrl := hsl.scratch_buf_len; have harl := hcl.arena_len_arr
      have harle := hcl.arena_len_le; have hcv := hcl.cur_vars_le
      bve_steps
      · -- sz == 0 -> inconsistent = 1, return 20
        have hp_lt : p.toNat < r_end.toNat := by bv_omega
        have hp_scr : p.toNat < sl.scratch.scratch_buf.length := by omega
        have hc0 : sl.scratch.scratch_buf[p.toNat]'hp_scr = 0#32 := by assumption
        obtain ⟨_, _, _, hent, _⟩ := commit_resBuf_head_step hres hp_lt
        have hsz0 : (sl.scratch.scratch_buf[p.toNat]?.getD 0#32).toNat = 0 := by
          rw [List.getElem?_eq_getElem hp_scr, Option.getD_some, hc0]; rfl
        rw [hsz0] at hent
        have hent_nil : (cnfOfClauses F_cur).EntailsClause (cnfClause []) := by simpa using hent
        have hunsat_cur : (cnfOfClauses F_cur).Unsat := unsat_of_entails_nil hent_nil
        have hunsat0 : F0.Unsat := hinv.2.1.ext_sound.2 hunsat_cur
        let sl' := { sl with core := { sl.core with inconsistent := 1#64 } }
        exact hQ 20#64 sl' _ (denseInvW_to_full (FullBveVarHelpers.FullDenseInvW.with_inconsistent
            hinv 1#64 (fun _ => hunsat_cur)))
          (htmk.congr rfl rfl) hcv_eq hfl_eq (Or.inr (Or.inr rfl)) (fun _ => hunsat0)
          (by assumption)
      · -- sz == 1 -> full_add_unit
        have hp_lt : p.toNat < r_end.toNat := by bv_omega
        have hp_scr : p.toNat < sl.scratch.scratch_buf.length := by omega
        have hc1 : sl.scratch.scratch_buf[p.toNat]'hp_scr = 1#32 := by assumption
        obtain ⟨hbd, hlts, _, hent, htail⟩ := commit_resBuf_head_step hres hp_lt
        have hsz1 : (sl.scratch.scratch_buf[p.toNat]?.getD 0#32).toNat = 1 := by
          rw [List.getElem?_eq_getElem hp_scr, Option.getD_some, hc1]; rfl
        rw [hsz1] at hbd hlts hent htail
        have hp1_nat : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
        have hp1_scr : (p + 1#64).toNat < sl.scratch.scratch_buf.length := by omega
        have hlit_lt : (sl.scratch.scratch_buf[(p + 1#64).toNat]'hp1_scr).toNat <
            2 * sl.core.cur_vars := by
          have := hlts 0 (by omega)
          rw [List.getElem?_eq_getElem
            (by omega : p.toNat + 1 < sl.scratch.scratch_buf.length), Option.getD_some] at this
          simpa [hp1_nat] using this
        have hent1 : (cnfOfClauses F_cur).EntailsClause
            (cnfClause [(sl.scratch.scratch_buf[(p + 1#64).toNat]'hp1_scr).toNat]) := by
          have hls : (List.range 1).map (fun k =>
              (sl.scratch.scratch_buf[p.toNat + 1 + k]?.getD 0#32).toNat) =
              [(sl.scratch.scratch_buf[(p + 1#64).toNat]'hp1_scr).toNat] := by
            simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero]
            simp only [hp1_nat, List.getElem?_eq_getElem
              (by omega : p.toNat + 1 < sl.scratch.scratch_buf.length), Option.getD_some]
          rw [← hls]; exact hent
        bve_steps
        refine wp_call_of_spec _ _ (hAU _ _ _ X ⟨c, F0, F_cur, sl, R, rfl, hinv.1,
          hinv.2.1, (fun _ => hent1), by assumption, ?_⟩)
        dsimp only
        rintro ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
          sc' m' hlen' hw' hpres' hcl0 hokf_lt hokf hm'
        have hinv' := FullBveVarHelpers.FullDenseInvW.of_addUnit hinv hlen' hw' hpres'.1 hcl0
        have htmk' : TmkZero { sl with
            core := { sl.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns',
              trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
              cur_level := cl', unassigned := unass', unflushed := unfl', inconsistent := inc' }
            scratch := sc' } := htmk.congr rfl hpres'.2.2.2.1
        cases ok
        · obtain ⟨hu0, _⟩ := hokf_lt hlit_lt rfl
          bve_steps!
          exact hQ 20#64 _ m' (denseInvW_to_full hinv') htmk' hcv_eq hfl_eq
            (Or.inr (Or.inr rfl)) (fun _ => hu0) hm'
        · bve_steps!
          all_goals (try exact Bool.noConfusion (by assumption))
          have hnext_nat : (p + 1 + BitVec.setWidth 64
              (sl.scratch.scratch_buf[p.toNat]'hp_scr)).toNat = p.toNat + 1 + 1 := by
            rw [show (1 : BitVec 64) = 1#64 from rfl]
            have hs : (sl.scratch.scratch_buf[p.toNat]'hp_scr).toNat = 1 := by rw [hc1]; rfl
            bv_omega
          have hres' := FullBveVarHelpers.FullResBufOkW.with_state (s := sl) (s' := { sl with
            core := { sl.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns',
              trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
              cur_level := cl', unassigned := unass', unflushed := unfl', inconsistent := inc' }
            scratch := sc' }) rfl (fun _ _ => by
              dsimp only; rw [hpres'.2.2.2.2.1]) htail
          refine ih _ m' (by dsimp only; rw [hnext_nat]; omega)
            ⟨_, hinv', htmk', hcv_eq, hfl_eq, by rw [hnext_nat]; omega, ?_, hm'⟩
          rw [hnext_nat]; exact hres'
      · -- sz == 2 -> full_add_bin
        have hp_lt : p.toNat < r_end.toNat := by bv_omega
        have hp_scr : p.toNat < sl.scratch.scratch_buf.length := by omega
        have hc2 : sl.scratch.scratch_buf[p.toNat]'hp_scr = 2#32 := by assumption
        obtain ⟨hbd, hlts, _, hent, htail⟩ := commit_resBuf_head_step hres hp_lt
        have hsz2 : (sl.scratch.scratch_buf[p.toNat]?.getD 0#32).toNat = 2 := by
          rw [List.getElem?_eq_getElem hp_scr, Option.getD_some, hc2]; rfl
        rw [hsz2] at hbd hlts hent htail
        have hp1_nat : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
        have hp1_scr : (p + 1#64).toNat < sl.scratch.scratch_buf.length := by omega
        have hp2_nat : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by bv_omega
        have hp2_scr : (p + 1#64 + 1#64).toNat < sl.scratch.scratch_buf.length := by omega
        have ha_lt : (sl.scratch.scratch_buf[(p + 1#64).toNat]'hp1_scr).toNat <
            2 * sl.core.cur_vars := by
          have := hlts 0 (by omega)
          rw [List.getElem?_eq_getElem
            (by omega : p.toNat + 1 < sl.scratch.scratch_buf.length), Option.getD_some] at this
          simpa [hp1_nat] using this
        have hb_lt : (sl.scratch.scratch_buf[(p + 1#64 + 1#64).toNat]'hp2_scr).toNat <
            2 * sl.core.cur_vars := by
          have := hlts 1 (by omega)
          rw [show p.toNat + 1 + 1 = p.toNat + 2 by omega,
            List.getElem?_eq_getElem
              (by omega : p.toNat + 2 < sl.scratch.scratch_buf.length), Option.getD_some] at this
          simpa [hp2_nat] using this
        have hent2 : (cnfOfClauses F_cur).EntailsClause (cnfClause
            [(sl.scratch.scratch_buf[(p + 1#64).toNat]'hp1_scr).toNat,
             (sl.scratch.scratch_buf[(p + 1#64 + 1#64).toNat]'hp2_scr).toNat]) := by
          have hls : (List.range 2).map (fun k =>
              (sl.scratch.scratch_buf[p.toNat + 1 + k]?.getD 0#32).toNat) =
              [(sl.scratch.scratch_buf[(p + 1#64).toNat]'hp1_scr).toNat,
               (sl.scratch.scratch_buf[(p + 1#64 + 1#64).toNat]'hp2_scr).toNat] := by
            simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append,
              List.map_cons, List.map_nil, Nat.add_zero]
            simp only [hp1_nat, hp2_nat,
              List.getElem?_eq_getElem
                (by omega : p.toNat + 1 < sl.scratch.scratch_buf.length),
              List.getElem?_eq_getElem
                (by omega : p.toNat + 2 < sl.scratch.scratch_buf.length),
              Option.getD_some, List.cons_append, List.nil_append]
          rw [← hls]; exact hent
        bve_steps
        refine wp_call_of_spec _ _ (hAddBin _ _ _ X ⟨c, F0, F_cur, sl, R, rfl, hinv.1,
          hinv.2.1, hinv.2.2.2.2.2.1, (fun _ _ => hent2), by assumption, ?_⟩)
        dsimp only
        rintro r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb'
          oom' inc' phases' wsort' m' hlen' hw' hrcodes hr20 hr2 hm'
        have hinv' := FullBveVarHelpers.FullDenseInvW.of_addBin hinv hlen' hw'
        have htmk' : TmkZero { sl with
            core := { sl.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns',
              trl := trl', trail_pos := tp', trail_end := te', unassigned := unass',
              unflushed := unfl', wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
              num_binary := nb', oom := oom', inconsistent := inc' }
            scratch := { sl.scratch with phases := phases', wsort := wsort' } } :=
          htmk.congr rfl rfl
        bve_steps!
        · exact hQ 20#64 _ m' (denseInvW_to_full hinv') htmk' hcv_eq hfl_eq (Or.inr (Or.inr rfl))
            (fun _ => (hr20 (by assumption)).1) hm'
        · exact hQ 2#64 _ m' (denseInvW_to_full hinv') htmk' hcv_eq hfl_eq (Or.inr (Or.inl rfl))
            (fun h => by cases h) hm'
        · have hnext_nat : (p + 1 + BitVec.setWidth 64
              (sl.scratch.scratch_buf[p.toNat]'hp_scr)).toNat = p.toNat + 1 + 2 := by
            rw [show (1 : BitVec 64) = 1#64 from rfl]
            have hs : (sl.scratch.scratch_buf[p.toNat]'hp_scr).toNat = 2 := by rw [hc2]; rfl
            bv_omega
          have hres' := FullBveVarHelpers.FullResBufOkW.with_state (s := sl) (s' := { sl with
            core := { sl.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns',
              trl := trl', trail_pos := tp', trail_end := te', unassigned := unass',
              unflushed := unfl', wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
              num_binary := nb', oom := oom', inconsistent := inc' }
            scratch := { sl.scratch with phases := phases', wsort := wsort' } })
            rfl (fun _ _ => rfl) htail
          refine ih _ m' (by dsimp only; rw [hnext_nat]; omega)
            ⟨_, hinv', htmk', hcv_eq, hfl_eq, by rw [hnext_nat]; omega, ?_, hm'⟩
          rw [hnext_nat]; exact hres'
      · -- sz >= 3 -> full_alloc_cl + copy + watch_push
        have hp_lt : p.toNat < r_end.toNat := by bv_omega
        have hp_scr : p.toNat < sl.scratch.scratch_buf.length := by omega
        obtain ⟨hbd, hlts, hnd, hent, htail⟩ := commit_resBuf_head_step hres hp_lt
        let sz := (sl.scratch.scratch_buf[p.toNat]'hp_scr).toNat
        have hsz_bv : (sl.scratch.scratch_buf[p.toNat]'hp_scr).toNat = sz := rfl
        have hsz_def : (sl.scratch.scratch_buf[p.toNat]?.getD 0#32).toNat = sz := by
          rw [List.getElem?_eq_getElem hp_scr, Option.getD_some]
        rw [hsz_def] at hbd hlts hnd hent htail
        have hp1_nat : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
        have hne0 : sl.scratch.scratch_buf[p.toNat]'hp_scr ≠ 0#32 := by assumption
        have hne1 : sl.scratch.scratch_buf[p.toNat]'hp_scr ≠ 1#32 := by assumption
        have hne2 : sl.scratch.scratch_buf[p.toNat]'hp_scr ≠ 2#32 := by assumption
        have hsz_ge3 : 3 ≤ sz := by
          rcases Nat.lt_or_ge sz 3 with hlt3 | hge3
          · exfalso
            rcases (by omega : sz = 0 ∨ sz = 1 ∨ sz = 2) with h0 | h1 | h2
            · exact hne0 (BitVec.eq_of_toNat_eq (by simp [hsz_bv, h0]))
            · exact hne1 (BitVec.eq_of_toNat_eq (by simp [hsz_bv, h1]))
            · exact hne2 (BitVec.eq_of_toNat_eq (by simp [hsz_bv, h2]))
          · exact hge3
        have hsz_lt31 : sz < 2 ^ 31 := by omega
        have hsz_lt64 : sz < 2 ^ 64 := by omega
        refine wp_call_of_spec _ _ (hAlloc _ _ _ X ⟨c, sl, R, rfl, hinv.1, by assumption, ?_⟩)
        simp only [LeanQbe.T.Arg.val_var]
        by_cases hoom_al : c.arena_cap - sl.core.arena_len < 3 +
            (sl.scratch.scratch_buf[p.toNat]'hp_scr).toNat
        · simp only [hoom_al, ite_true]
          bve_steps!
          · exact hQ 2#64 _ _ (denseInvW_to_full (FullBveVarHelpers.FullDenseInvW.with_oom
              hinv 1#64)) (htmk.congr rfl rfl) hcv_eq hfl_eq
              (Or.inr (Or.inl rfl)) (fun h => by cases h) (by assumption)
          · exfalso; exact (by assumption : (0xFFFFFFFF#64 : BitVec 64) ≠ 0xFFFFFFFF#64) rfl
        · simp only [hoom_al, ite_false]
          intro ar1 m1; try dsimp only
          intro hlen1 hhold1 hns1 hng1 hred1 hsz1 hm1
          have hoom_nat : ¬ c.arena_cap - sl.core.arena_len < 3 + sz := by
            simpa [hsz_bv] using hoom_al
          let cr0 := sl.core.arena_len
          have hcr0_le : cr0 + 3 + sz ≤ c.arena_cap := by dsimp only [cr0]; omega
          let cr : BitVec 64 := BitVec.ofNat 64 cr0
          have hcr0_lt31 : cr0 < 2 ^ 31 := by omega
          have hcr_nat : cr.toNat = cr0 := by
            simp [cr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cr0 < 2 ^ 64)]
          have hcr_ne : cr ≠ 0xFFFFFFFF#64 := by
            intro heq; have := congrArg BitVec.toNat heq; rw [hcr_nat] at this
            have h32 : (0xFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 32 - 1 := rfl
            omega
          bve_steps!
          refine wp_loop_inv (ts := [i32])
            (fun (k, _) mk =>
              ∃ ark,
                k.toNat ≤ sz ∧ ark.length = c.arena_cap ∧
                (∀ i < cr0, ark[i]? = sl.core.arena[i]?) ∧
                ark[cr0]? = ar1[cr0]? ∧ ark[cr0 + 2]? = ar1[cr0 + 2]? ∧
                (∀ j < k.toNat,
                  ark[cr0 + 3 + j]? = sl.scratch.scratch_buf[p.toNat + 1 + j]?) ∧
                (FullMem c { sl with core := { sl.core with
                  arena := ark, arena_len := cr0 + 3 + sz } } ⋆ R) mk)
            (fun (k, _) _ => sz - k.toNat)
            (fun Jc hJc => by
              bve_steps!
              refine hJc (0#32, PUnit.unit) m1 ⟨ar1, Nat.zero_le _, hlen1.core_ok.arena_len_arr,
                hhold1, rfl, rfl, (fun _ hj => by simp at hj), ?_⟩
              simpa [hsz_bv, cr0] using hm1)
            (fun Jc ⟨k, ⟨⟩⟩ mk ⟨ark, hk_le, hark_len, hark_hold, hark0, hark2, hark_cp,
                hmk⟩ ihc => by
              bve_steps
              · have hk_lt : k.toNat < sz := by bv_omega
                have hpk_scr : (p + 1#64 + BitVec.setWidth 64 k).toNat <
                    sl.scratch.scratch_buf.length := by bv_omega
                have hpk_nat : (p + 1#64 + BitVec.setWidth 64 k).toNat =
                    p.toNat + 1 + k.toNat := by bv_omega
                have hack_idx : (cr + 3#64 + BitVec.setWidth 64 k).toNat < ark.length := by
                  bv_omega
                have hack_nat : (cr + 3#64 + BitVec.setWidth 64 k).toNat =
                    cr0 + 3 + k.toNat := by bv_omega
                bve_steps!
                refine ihc (k + 1#32, PUnit.unit) _ (by bv_omega)
                  ⟨ark.set (cr0 + 3 + k.toNat)
                    (sl.scratch.scratch_buf[p.toNat + 1 + k.toNat]'(by omega)),
                    by bv_omega, by simp [hark_len], ?_, ?_, ?_, ?_, ?_⟩
                · intro i hi; rw [List.getElem?_set_ne (by omega)]; exact hark_hold i hi
                · rw [List.getElem?_set_ne (by omega)]; exact hark0
                · rw [List.getElem?_set_ne (by omega)]; exact hark2
                · intro j hj
                  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
                  rw [hk1] at hj
                  by_cases hjk : j = k.toNat
                  · subst hjk
                    rw [List.getElem?_set_self (by omega),
                      List.getElem?_eq_getElem (by omega : p.toNat + 1 + k.toNat <
                        sl.scratch.scratch_buf.length)]
                  · rw [List.getElem?_set_ne (by omega)]; exact hark_cp j (by omega)
                · have hack_hm :
                      (BitVec.ofNat 64 sl.core.arena_len + 3 + BitVec.setWidth 64 k).toNat =
                        cr0 + 3 + k.toNat := hack_nat
                  have hpk_hm : (p + 1 + BitVec.setWidth 64 k).toNat = p.toNat + 1 + k.toNat :=
                    hpk_nat
                  have hpk_scr' :
                      (p + 1 + BitVec.setWidth 64 k).toNat < sl.scratch.scratch_buf.length :=
                    hpk_scr
                  have hval_eq :
                      sl.scratch.scratch_buf[(p + 1 + BitVec.setWidth 64 k).toNat]'hpk_scr' =
                        sl.scratch.scratch_buf[p.toNat + 1 + k.toNat]'(by omega) :=
                    Option.some.inj (by
                      rw [← List.getElem?_eq_getElem hpk_scr', hpk_hm,
                        List.getElem?_eq_getElem (by omega)])
                  rw [← hval_eq, ← hack_hm]; assumption
              · have hk_eq : k.toNat = sz := by
                  have hlt_k : ¬ k.toNat < sz := by assumption
                  omega
                rw [hk_eq] at hark_cp
                let s2 : FullState :=
                  { sl with core := { sl.core with arena := ark, arena_len := cr0 + 3 + sz } }
                have hlen2 : s2.LengthsOk c :=
                  ⟨{ hcl with arena_len_arr := hark_len, arena_len_le := hcr0_le }, hsl⟩
                have hsz2_ar : (ark[cr0 + 2]?.getD 0#32).toNat = sz := by
                  rw [hark2]; simpa [hsz_bv] using hsz1
                have hs2_ar : cr0 + 3 + sz ≤ s2.core.arena.length := by
                  change cr0 + 3 + sz ≤ ark.length; rw [hark_len]; exact hcr0_le
                have hs2_scr : p.toNat + 1 + sz ≤ sl.scratch.scratch_buf.length := by omega
                have hlits_eq : fullArenaClauseLitsCore s2.core cr0 =
                    (List.range sz).map (fun j =>
                      (sl.scratch.scratch_buf[p.toNat + 1 + j]?.getD 0#32).toNat) :=
                  commit_arenaLits_eq_copied hs2_ar hs2_scr hsz2_ar hark_cp
                have hns2 : (ark[cr0]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
                  rw [hark0]; exact hns1
                have hng2 : (ark[cr0]?.getD 0#32 &&& 0x00080000#32) = 0#32 := by
                  rw [hark0]; exact hng1
                have hrefs2 : fullArenaClauseRefsCore s2.core =
                    fullArenaClauseRefsCore sl.core ++ [cr0] :=
                  fullArenaClauseRefsCore_append hinv.2.1.arena hsz_ge3 rfl
                    hark_hold hns2 hsz2_ar
                have hwat2 : ModeWatchesInv F_cur s2.core :=
                  hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl
                    (fun r hr => by rw [hrefs2]; exact List.mem_append_left _ hr)
                refine wp_loop_inv (ts := [i32])
                  (fun (kw, _) mw =>
                    ∃ wvecw wstkw wlenw wuw wsortw,
                      kw.toNat ≤ sz ∧
                      let sw : FullState :=
                        { s2 with
                          core := { s2.core with wvec := wvecw, wstk := wstkw,
                                                 wlen := wlenw, wusable := wuw }
                          scratch := { s2.scratch with wsort := wsortw } }
                      sw.LengthsOk c ∧ ModeWatchesInv F_cur sw.core ∧
                      (FullMem c sw ⋆ R) mw)
                  (fun (kw, _) _ => sz - kw.toNat)
                  (fun Jw hJw => by
                    bve_steps!
                    exact hJw (0#32, PUnit.unit) mk
                      ⟨sl.core.wvec, sl.core.wstk, sl.core.wlen, sl.core.wusable,
                       sl.scratch.wsort, Nat.zero_le _, hlen2, hwat2, hmk⟩)
                  (fun Jw ⟨kw, ⟨⟩⟩ mw ⟨wvecw, wstkw, wlenw, wuw, wsortw, hkw_le, hlenw, hwatw,
                      hmw⟩ ihw => by
                    bve_steps
                    · have hkw_lt : kw.toNat < sz := by bv_omega
                      have har_idx :
                          (cr + 3#64 + BitVec.setWidth 64 kw).toNat < ark.length := by
                        bv_omega
                      have har_nat : (cr + 3#64 + BitVec.setWidth 64 kw).toNat =
                          cr0 + 3 + kw.toNat := by bv_omega
                      let w0w := (sl.scratch.scratch_buf[p.toNat]'hp_scr) &&& 0x7FFFFFFF#32
                      let cr32 := BitVec.setWidth 32 cr
                      have hw0w_nat : w0w.toNat = sz := by
                        dsimp only [w0w]
                        rw [bv32_and_litMask_toNat, hsz_bv, Nat.mod_eq_of_lt hsz_lt31]
                      have hw0w_ne : w0w ≠ 0xFFFFFFFF#32 := by
                        intro heq; have := congrArg BitVec.toNat heq; rw [hw0w_nat] at this
                        have : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
                      have hw0w_msb : (w0w &&& 0x80000000#32) = 0#32 :=
                        bv32_and_msb_eq_zero_of_lt (by rw [hw0w_nat]; exact hsz_lt31)
                      have hcr32_nat : cr32.toNat = cr0 := by
                        dsimp only [cr32]
                        rw [BitVec.toNat_setWidth, hcr_nat,
                          Nat.mod_eq_of_lt (by omega : cr0 < 2 ^ 32)]
                      have hcr32_ne : cr32 ≠ 0xFFFFFFFF#32 := by
                        intro heq; have := congrArg BitVec.toNat heq; rw [hcr32_nat] at this
                        have : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
                      let sw : FullState :=
                        { s2 with
                          core := { s2.core with wvec := wvecw, wstk := wstkw,
                                                 wlen := wlenw, wusable := wuw }
                          scratch := { s2.scratch with wsort := wsortw } }
                      bve_steps
                      refine wp_call_of_spec _ _ (hWPush _ mw _ X ⟨c, sw, R, rfl, hlenw,
                        hwatw.layout, (fun h => by cases h),
                        (fun _ => ⟨hw0w_ne, hcr32_ne⟩), hmw, ?_⟩)
                      dsimp only
                      rintro okw wvec' wstk' wlen' wu' wsort' mw' hlenw' hlayw' hotherw
                        hokt hokf hm'
                      simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]
                        at hotherw hokt hokf
                      have hwatw' : ModeWatchesInv F_cur
                          { sw.core with wvec := wvec', wstk := wstk',
                                         wlen := wlen', wusable := wu' } := by
                        refine FullBveVarHelpers.fullWatchPush_preserves_modeWatchesInv
                          (cnt := 2#32) hwatw hlayw'
                          rfl rfl (fun _ hr => hr) (fun h => by cases h) ?_ hotherw hokt
                          (fun hf => (hokf hf).1)
                        intro _
                        refine ⟨hw0w_msb, (fun _ => by
                          change 3 ≤ w0w.toNat; rw [hw0w_nat]; exact hsz_ge3),
                          (by rw [hcr32_nat]; omega), ?_⟩
                        change cr32.toNat ∈ fullArenaClauseRefsCore s2.core
                        rw [hcr32_nat, hrefs2]
                        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
                      cases okw
                      · have har_cr_idx : cr0 < ark.length := by omega
                        have har_cr_bv :
                            (BitVec.ofNat 64 sl.core.arena_len).toNat < ark.length := by
                          change cr.toNat < ark.length; rw [hcr_nat]; exact har_cr_idx
                        bve_steps!
                        let ark_g := ark.set cr0 ((ark[cr0]'har_cr_idx) ||| 0x00080000#32)
                        let ag' := sw.core.arena_garbage + 3#64 +
                          BitVec.setWidth 64 (sl.scratch.scratch_buf[p.toNat]'hp_scr)
                        have hinv_g := commit_res_garb_inv (ag' := ag') hinv hsz_ge3 hark_len
                          hark_hold hns2 hsz2_ar har_cr_idx hlenw' hwatw' hrefs2
                        refine hQ 2#64 _ _ hinv_g (htmk.congr rfl rfl) hcv_eq hfl_eq
                          (Or.inr (Or.inl rfl)) (fun h => by cases h) ?_
                        have har_g_eq :
                            ark_g = ark.set (BitVec.ofNat 64 sl.core.arena_len).toNat
                              ((ark[(BitVec.ofNat 64 sl.core.arena_len).toNat]'(by
                                rw [show (BitVec.ofNat 64 sl.core.arena_len).toNat = cr0 from
                                  hcr_nat]; exact har_cr_idx)) ||| 0x00080000#32) := by
                          simp only [ark_g,
                            show (BitVec.ofNat 64 sl.core.arena_len).toNat = cr0 from hcr_nat, cr0]
                        have hst_g : ({ sl with
                          core := { sl.core with
                            arena := ark_g, arena_len := cr0 + 3 + sz,
                            wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
                            arena_garbage := ag', oom := 1#64 }
                          scratch := { sl.scratch with wsort := wsort' } } : FullState) =
                          { s2 with
                            core := { s2.core with
                              arena := ark.set (BitVec.ofNat 64 sl.core.arena_len).toNat
                                ((ark[(BitVec.ofNat 64 sl.core.arena_len).toNat]'(by
                                  rw [show (BitVec.ofNat 64 sl.core.arena_len).toNat = cr0 from
                                    hcr_nat]; exact har_cr_idx)) ||| 0x00080000#32),
                              wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
                              arena_garbage := sw.core.arena_garbage + 3 +
                                BitVec.setWidth 64 (sl.scratch.scratch_buf[p.toNat]'hp_scr),
                              oom := 1#64 }
                            scratch := { s2.scratch with wsort := wsort' } } := by
                          dsimp only [ag', s2, cr0]; rw [har_g_eq]; rfl
                        rw [hst_g]; assumption
                      · refine wp_jnz_of (fun _ => ?_) (fun hf => Bool.noConfusion hf)
                        bve_steps!
                        have hkw1 : (kw + 1#32).toNat = kw.toNat + 1 := by
                          rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                            Nat.mod_eq_of_lt (by omega : kw.toNat + 1 < 2 ^ 32)]
                        exact ihw (kw + 1#32, PUnit.unit) mw' (by dsimp only; rw [hkw1]; omega)
                          ⟨wvec', wstk', wlen', wu', wsort', by rw [hkw1]; omega,
                           hlenw', hwatw', hm'⟩
                    · bve_steps!
                      let s_fin : FullState :=
                        { sl with
                          core := { sl.core with
                            arena := ark, arena_len := cr0 + 3 + sz,
                            wvec := wvecw, wstk := wstkw, wlen := wlenw, wusable := wuw,
                            num_irred := sl.core.num_irred + 1#64 }
                          scratch := { sl.scratch with wsort := wsortw } }
                      have hinv_c := commit_res_entailed_inv hinv hsz_ge3 hlts hnd hent
                        hark_hold hns2 hsz2_ar hlits_eq hlenw hwatw
                      have hnext_nat : (p + 1 + BitVec.setWidth 64
                          (sl.scratch.scratch_buf[p.toNat]'hp_scr)).toNat =
                          p.toNat + 1 + sz := by
                        rw [show (1 : BitVec 64) = 1#64 from rfl, BitVec.toNat_add,
                          BitVec.toNat_add,
                          show (1#64 : BitVec 64).toNat = 1 from rfl, BitVec.toNat_setWidth,
                          Nat.mod_eq_of_lt hsz_lt64,
                          Nat.mod_eq_of_lt (by omega : p.toNat + 1 < 2 ^ 64),
                          Nat.mod_eq_of_lt (by omega : p.toNat + 1 + sz < 2 ^ 64)]
                      have hres_c := FullBveVarHelpers.FullResBufOkW.with_state
                        (s := sl) (s' := s_fin) rfl (fun _ _ => rfl) htail
                      refine ih _ _ (by dsimp only; rw [hnext_nat]; omega)
                        ⟨s_fin, hinv_c, htmk.congr rfl rfl, hcv_eq, hfl_eq,
                         by rw [hnext_nat]; omega, ?_, by assumption⟩
                      rw [hnext_nat]; exact hres_c))
      · exact hQ 1#64 sl ml (denseInvW_to_full hinv) htmk hcv_eq hfl_eq
          (Or.inl rfl) (fun h => by cases h) hm_lp)

end CommitResTmk

end LeanQbe.T.Examples.Kissat.FullFast
