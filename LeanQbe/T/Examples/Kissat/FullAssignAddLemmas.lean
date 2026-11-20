module

public import LeanQbe.T.Examples.Kissat.FullAssignAddLemmas2
public import LeanQbe.T.Logic.C0Step
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Watch-Push, Assign & Add-Clause Proofs — Top Module (`Stage 4`)

Builds on `FullAssignAddLemmas1` (`full_assign_lvl_wp`, `full_assign_wp`) and
`FullAssignAddLemmas2` (`full_watch_push_wp`) to provide `full_add_clause_wp`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap LeanQbe.T.C0Step
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FullAssignAddTactics
open FullAssignAddTactics FullAssignAddSpecs

private abbrev addClauseState (s : FullState) (len : Nat) (arena' wvec' wstk' : List (BitVec 32))
    (wlen' : Nat) (wusable' fred' ni' nr' : BitVec 64) (wsort' : List (BitVec 32)) :
    FullState :=
  { s with
    core :=
      { s.core with
        arena := arena', arena_len := s.core.arena_len + 3 + len
        wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable'
        first_reducible := fred', num_irred := ni', num_redundant := nr' }
    scratch := { s.scratch with wsort := wsort' } }

theorem full_add_clause_wp (Γ : Env)
    (hAlloc : ∀ args m Q X, fullAllocClSpec args m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] args m Q X)
    (hPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullAddClauseSpec args m Q X →
      Func.wp Γ full_add_clause_body args m Q X := by
  rintro ⟨h, len, glue, red, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, _hlen_bd, hcl_bd, hm, hQ⟩
  have hmv := c.hmaxv; have har := c.harena; have hwcap := c.hwcap
  unfold dimacsBound at hmv har hwcap; have hco := hlen.core_ok
  have hcv_lt : s.core.cur_vars < 2 ^ 29 := by have := hco.cur_vars_le; omega
  faa_head_steps
  refine wp_head_jnz_iff (b := decide (len.toNat = 2))
    (by simpa [Arg.val_var] using bv32_beq_nat_eq (x := len) (n := 2) (by decide)) ?_
  rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun h2 => ?_, fun hne2 => ?_⟩
  · simp only [h2, show ¬ (2 < 2) by omega, ↓reduceIte] at hQ hcl_bd
    obtain ⟨hlits_lt, _hnd2, hent2⟩ := hcl_bd (by omega)
    have htm_gt0 : 0 < s.core.tmp.length := by rw [hco.tmp_len_arr]; omega
    have htm_gt1 : 1 < s.core.tmp.length := by rw [hco.tmp_len_arr]; omega
    let l0 := s.core.tmp[0]'htm_gt0; let l1 := s.core.tmp[1]'htm_gt1
    have htmp_take2 : (s.core.tmp.take 2).map BitVec.toNat = [l0.toNat, l1.toNat] := by
      refine List.ext_getElem (by simp [hco.tmp_len_arr]; omega) fun k hk _ => ?_
      match k, hk with | 0, _ => simp [l0] | 1, _ => simp [l1]
    rw [htmp_take2] at hlits_lt hent2
    have hl0_lt : l0.toNat < 2 * s.core.cur_vars := hlits_lt _ (by simp)
    have hl1_lt : l1.toNat < 2 * s.core.cur_vars := hlits_lt _ (by simp)
    have hent2_swap := entails_swap2 hent2
    let b0 := (l1 &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    let b1 := (l0 &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    have hb0_ne : b0 ≠ 0xFFFFFFFF#32 := bv32_tag_bin_ne_sent (by omega)
    have hb1_ne : b1 ≠ 0xFFFFFFFF#32 := bv32_tag_bin_ne_sent (by omega)
    faa_steps; c0_call hPush
    refine ⟨c, s, R, rfl, hlen, hw.watches.layout, (fun _ => hb0_ne),
      (fun hc => absurd hc (by decide)), hm, ?_⟩
    intro ok1 wvec1 wstk1 wlen1 wu1 wsort1 m1 s1 hlen1 hlay1 hoth1 hok1t hok1f hm1
    have htm1_gt1 : 1 < s1.core.tmp.length := by rw [hlen1.core_ok.tmp_len_arr]; omega
    have hwat1 : ModeWatchesInv F_cur s1.core := fullWatchPush_preserves_modeWatchesInv hw.watches
      hlay1 rfl rfl (fun _ hr => hr)
      (fun _ => ⟨bv32_tag_bin_flag l1, hb0_ne,
        by rw [bv32_tag_bin_mask (by omega)]; exact hl1_lt,
        by rw [bv32_tag_bin_mask (by omega)]; exact hent2⟩)
      (fun hc => absurd hc (by decide)) hoth1 hok1t (fun h => (hok1f h).1)
    have hw1 : FullWitnessInv c F0 F_cur s1.core := watchUpdate_preserves_witness hw hwat1
    faa_steps
    · subst hc; c0_call hPush
      refine ⟨c, s1, R, rfl, hlen1, hlay1, (fun _ => hb1_ne),
        (fun hc => absurd hc (by decide)), hm1, ?_⟩
      intro ok2 wvec2 wstk2 wlen2 wu2 wsort2 m2 s2 hlen2 hlay2 hoth2 hok2t hok2f hm2
      have hwat2 : ModeWatchesInv F_cur s2.core := fullWatchPush_preserves_modeWatchesInv hwat1
        hlay2 rfl rfl (fun _ hr => hr)
        (fun _ => ⟨bv32_tag_bin_flag l0, hb1_ne,
          by rw [bv32_tag_bin_mask (by omega)]; exact hl0_lt,
          by rw [bv32_tag_bin_mask (by omega)]; exact hent2_swap⟩)
        (fun hc => absurd hc (by decide)) hoth2 hok2t (fun h => (hok2f h).1)
      have hw2 : FullWitnessInv c F0 F_cur s2.core := watchUpdate_preserves_witness hw1 hwat2
      faa_steps
      · have hwat_fin : ModeWatchesInv F_cur
            { s2.core with num_binary := s.core.num_binary + 1#64 } :=
          hwat2.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
        have hw_fin : FullWitnessInv c F0 F_cur
            { s2.core with num_binary := s.core.num_binary + 1#64 } :=
          watchUpdate_preserves_witness hw (oom' := s.core.oom) hwat_fin
        exact hQ 0xFFFFFFFE#64 wvec2 wstk2 wlen2 wu2 (s.core.num_binary + 1#64) wsort2 _
          (Or.inr rfl) { core_ok := { hlen2.core_ok with vals_len := hlen2.core_ok.vals_len },
                         scratch_ok := hlen2.scratch_ok } hw_fin ‹_›
      · exact hQ 0xFFFFFFFF#64 wvec2 wstk2 wlen2 wu2 s.core.num_binary wsort2 m2 (Or.inl rfl)
          hlen2 hw2 hm2
    · exact hQ 0xFFFFFFFF#64 wvec1 wstk1 wlen1 wu1 s.core.num_binary wsort1 m1 (Or.inl rfl)
        hlen1 hw1 hm1
  · faa_head_steps
    refine wp_head_jnz_iff (b := decide (len.toNat < 3))
      (by simp only [Arg.val_var]; simpa [bv_ofNat_toNat_eq len] using
        bv32_ult_eq len.isLt (b := 3) (by decide)) ?_
    rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun hlt3 => ?_, fun hge3 => ?_⟩
    · simp only [show len.toNat < 2 by omega, ↓reduceIte] at hQ; faa_steps; exact hQ
    · have hge3' : 3 ≤ len.toNat := by omega
      simp only [show ¬ (len.toNat < 2) by omega, hne2, ↓reduceIte] at hQ
      have hs_alen_lt32 : s.core.arena_len < 0xFFFFFFFF := by have := hco.arena_len_le; omega
      have hcref_ne : BitVec.ofNat 64 s.core.arena_len ≠ 0xFFFFFFFF#64 := fun he => by
        have h := congrArg BitVec.toNat he
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
        change s.core.arena_len = 0xFFFFFFFF at h; omega
      obtain ⟨hlits_lt, hnd_tmp, hent_cl⟩ := hcl_bd (by omega)
      faa_steps; c0_call hAlloc; refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
      split
      · faa_steps
        · exact hQ 0xFFFFFFFF#64 s.core.arena s.core.arena_len s.core.wvec s.core.wstk
            s.core.wlen s.core.wusable s.core.first_reducible s.core.num_irred
            s.core.num_redundant s.scratch.wsort m (Or.inl rfl) hlen hw (fun _ h => h) id
            (fun hc => absurd hc.symm hcref_ne) hm
        · exact absurd rfl (by assumption)
      · intro arena1 m1 alen1 s1_st hlen1 hhold1 hnoshrk1 hnogarb1 _hred1 hsz1 hm1
        faa_steps
        refine wp_loop_group (ts := [i32]) (fun r (iv, ()) mc => ∃ i arena',
          i ≤ len.toNat ∧ r = len.toNat - i ∧ iv = BitVec.ofNat 32 i ∧
          arena'.length = c.arena_cap ∧
          (∀ k < s.core.arena_len + 3, arena'[k]? = arena1[k]?) ∧
          (∀ k < i, arena'[s.core.arena_len + 3 + k]? = s.core.tmp[k]?) ∧
          (FullMem c { s1_st with core := { s1_st.core with arena := arena' } } ⋆ R) mc) ?_ ?_
        · rintro L r ⟨iv, ⟨⟩⟩ mc ih ⟨i, arena', hile, rfl, rfl, harl, hpre, hcp, hmc⟩
          faa_head_steps
          refine wp_head_jnz_iff (b := decide (i < len.toNat)) (by
            simp only [Arg.val_var]
            simpa [bv_ofNat_toNat_eq len] using bv32_ult_eq (a := i) (by omega) len.isLt) ?_
          rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun hilt => ?_, fun hige => ?_⟩
          · have htm_bd_i : i <
                ({ s1_st with core := { s1_st.core with arena := arena' } }).core.tmp.length := by
              simp [s1_st, hco.tmp_len_arr]; omega
            have har_bd : s.core.arena_len + 3 + i < arena'.length := by
              have := hlen1.core_ok.arena_len_le; simp [s1_st, alen1] at this; omega
            have hidx_eq : ((BitVec.ofNat 32 i).setWidth 64) * 4 = BitVec.ofNat 64 (4 * i) := by
              rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega)]; bv_omega
            have hidx2 : c.pArena + ((BitVec.ofNat 64 s.core.arena_len + (3 : BitVec 64) +
                BitVec.ofNat 64 i) * 4) =
                c.pArena + BitVec.ofNat 64 (4 * (s.core.arena_len + 3 + i)) := by bv_omega
            faa_lets; try rw [hidx_eq]
            refine wp_load_of (FullArenaTactics.load_full_tmp (i := i) htm_bd_i hmc) ?_
            faa_lets; rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega), hidx2]
            let lit_i := s.core.tmp[i]'(by rw [hco.tmp_len_arr]; omega)
            obtain ⟨ok_ar, hm_ar⟩ :=
              FullArenaTactics.store_full_arena (i := s.core.arena_len + 3 + i) lit_i
                (by simpa [s1_st] using har_bd) hmc
            refine ⟨ok_ar, ?_⟩; faa_lets
            rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
              show BitVec.ofNat 32 i + BitVec.ofNat 32 1 = BitVec.ofNat 32 (i + 1) by bv_omega]
            exact ih (len.toNat - (i + 1)) (BitVec.ofNat 32 (i + 1), ()) _ (by omega)
              ⟨i + 1, arena'.set (s.core.arena_len + 3 + i) lit_i, by omega, rfl, rfl,
                by simp [harl],
                (fun k hk => by rw [List.getElem?_set_ne (by omega)]; exact hpre k hk),
                (fun k hk => by
                  by_cases hki : k = i
                  · subst hki; rw [List.getElem?_set_self har_bd,
                      List.getElem?_eq_getElem (by rw [hco.tmp_len_arr]; omega)]
                  · rw [List.getElem?_set_ne (by omega)]; exact hcp k (by omega)), hm_ar⟩
          · have hieq : i = len.toNat := by omega
            subst hieq
            let s_cp : FullState := { s1_st with core := { s1_st.core with arena := arena' } }
            have hhold_cp : ∀ k < s.core.arena_len, arena'[k]? = s.core.arena[k]? := fun k hk =>
              (hpre k (by omega)).trans (hhold1 k hk)
            have hnoshrk_cp : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
              rw [hpre s.core.arena_len (by omega)]; exact hnoshrk1
            have hnogarb_cp : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00080000#32) = 0#32 := by
              rw [hpre s.core.arena_len (by omega)]; exact hnogarb1
            have hsz_cp : (arena'[s.core.arena_len + 2]?.getD 0#32).toNat = len.toNat := by
              rw [hpre (s.core.arena_len + 2) (by omega)]; exact hsz1
            have hrefs_cp :
                fullArenaClauseRefsCore s_cp.core =
                  fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
              fullArenaClauseRefsCore_append hw.arena hge3' rfl hhold_cp hnoshrk_cp hsz_cp
            have hwat_cp : ModeWatchesInv F_cur s_cp.core :=
              hw.watches.with_wstk rfl rfl rfl rfl rfl
                (fun r hr => hrefs_cp ▸ List.mem_append_left _ hr)
            have hlen_cp : s_cp.LengthsOk c :=
              { core_ok := { hlen1.core_ok with arena_len_arr := by simp [s_cp, harl] }
                scratch_ok := hlen1.scratch_ok }
            have hlits_cp : fullArenaClauseLits s_cp s.core.arena_len =
                (s.core.tmp.take len.toNat).map BitVec.toNat := by
              have hle_len : s.core.arena_len + 3 + len.toNat ≤ arena'.length := by
                have := hlen1.core_ok.arena_len_le; simp [s1_st, alen1] at this; omega
              apply List.ext_getElem
              · simp [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, s_cp,
                  hsz_cp, harl, hco.tmp_len_arr]
                omega
              · intro k hk1 _
                have hk_lt : k < len.toNat := by
                  simp [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, s_cp,
                    hsz_cp] at hk1
                  omega
                have hcpk := hcp k hk_lt
                rw [List.getElem?_eq_getElem (by omega),
                  List.getElem?_eq_getElem (by rw [hco.tmp_len_arr]; omega)] at hcpk
                simp [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, s_cp,
                  hsz_cp, Option.some.inj hcpk]
            have hcref32_ne : BitVec.ofNat 32 s.core.arena_len ≠ 0xFFFFFFFF#32 := fun he => by
              have ht := congrArg BitVec.toNat he
              rw [bv32_ofNat_toNat (by omega)] at ht
              change s.core.arena_len = 0xFFFFFFFF at ht; omega
            have hcref32_lt : (BitVec.ofNat 32 s.core.arena_len).toNat < 0x80000000 := by
              rw [bv32_ofNat_toNat (by omega)]; omega
            refine wp_join_group (ts := []) (fun () mf => ∃ wvec' wstk' wlen' wusable' wsort',
              let sf : FullState :=
                { s_cp with
                  core := { s_cp.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                           wusable := wusable' }
                  scratch := { s_cp.scratch with wsort := wsort' } }
              sf.LengthsOk c ∧ ModeWatchesInv F_cur sf.core ∧ (FullMem c sf ⋆ R) mf) ?_ ?_
            · rintro _ ⟨⟩ mf ⟨wvec', wstk', wlen', wusable', wsort', hlen_w, hwat_w, hmf⟩
              let s_w : FullState :=
                { s_cp with
                  core := { s_cp.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                           wusable := wusable' }
                  scratch := { s_cp.scratch with wsort := wsort' } }
              have har_bd0 : s.core.arena_len < s_w.core.arena.length := by
                have := hlen_w.core_ok.arena_len_le; have h2 := hlen_w.core_ok.arena_len_arr
                change s_w.core.arena.length = c.arena_cap at h2; omega
              faa_lets
              have haddr_ar : c.pArena + BitVec.ofNat 64 s.core.arena_len * 4 =
                  c.pArena + BitVec.ofNat 64 (4 * s.core.arena_len) := by
                rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat,
                  bv64_ofNat_toNat (by omega)]
              rw [haddr_ar]
              refine wp_load_of
                (FullArenaTactics.load_full_arena (i := s.core.arena_len) har_bd0 hmf) ?_
              faa_lets
              let hdr_g := arena'[s.core.arena_len]'(by omega) ||| 0x00080000#32
              let arena_g := arena'.set s.core.arena_len hdr_g
              let s_g : FullState := { s_w with core := { s_w.core with arena := arena_g } }
              obtain ⟨ok_g, hm_g⟩ := FullArenaTactics.store_full_arena (i := s.core.arena_len)
                hdr_g (by simpa [s_w] using har_bd0) hmf
              refine ⟨ok_g, ?_⟩; faa_lets
              have hhold_g : ∀ k < s.core.arena_len, arena_g[k]? = s.core.arena[k]? :=
                fun k hk => by rw [List.getElem?_set_ne (by omega)]; exact hhold_cp k hk
              have hnoshrk_g :
                  (arena_g[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
                rw [List.getElem?_set_self (by omega), Option.getD_some]
                exact bv32_or_garb_noshrk (by
                  rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hnoshrk_cp)
              have hnogarb_g :
                  (arena_g[s.core.arena_len]?.getD 0#32 &&& 0x00080000#32) ≠ 0#32 := by
                rw [List.getElem?_set_self (by omega), Option.getD_some]; exact bv32_or_garb_nz _
              have hsz_g : (arena_g[s.core.arena_len + 2]?.getD 0#32).toNat = len.toNat := by
                rw [List.getElem?_set_ne (by omega)]; exact hsz_cp
              have hlen_g : s_g.LengthsOk c :=
                { core_ok := { hlen_w.core_ok with arena_len_arr := by simp [s_g, arena_g, harl] }
                  scratch_ok := hlen_w.scratch_ok }
              have hrefs_g :
                  fullArenaClauseRefsCore s_g.core =
                    fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
                fullArenaClauseRefsCore_append hw.arena hge3' rfl hhold_g hnoshrk_g hsz_g
              have hwat_g : ModeWatchesInv F_cur s_g.core := hwat_w.with_wstk rfl rfl rfl rfl rfl
                (fun r hr => by
                  have h1 : fullArenaClauseRefsCore s_w.core =
                      fullArenaClauseRefsCore s.core ++ [s.core.arena_len] := hrefs_cp
                  rwa [hrefs_g, ← h1])
              obtain ⟨hw_g, hrefs_g', hnd_g⟩ := addGarbageClause_preserves_witness
                (ag' := s.core.arena_garbage) (oom' := s.core.oom) hlen hw hlen_g hge3' hhold_g
                hnoshrk_g hnogarb_g hsz_g hwat_g
              exact hQ 0xFFFFFFFF#64 arena_g alen1 wvec' wstk' wlen' wusable'
                s.core.first_reducible s.core.num_irred s.core.num_redundant wsort' _
                (Or.inl rfl) hlen_g hw_g
                (fun r hr => hrefs_g' ▸ List.mem_append_left _ hr) hnd_g
                (fun hc => absurd hc.symm hcref_ne) hm_g
            · intro Jw hJw
              have htm_cp0 : 0 < s_cp.core.tmp.length := by
                simp [s_cp, s1_st, hco.tmp_len_arr]; omega
              have htm_cp1 : 1 < s_cp.core.tmp.length := by
                simp [s_cp, s1_st, hco.tmp_len_arr]; omega
              faa_steps; rw [bv64_trunc32_ofNat (by omega)]; c0_call hPush
              refine ⟨c, s_cp, R, rfl, hlen_cp, hwat_cp.layout, (fun hc => absurd hc (by decide)),
                (fun _ => ⟨bv32_mask_ne_sent _, hcref32_ne⟩), hmc, ?_⟩
              intro ok1 wvec1 wstk1 wlen1 wu1 wsort1 m1 s1 hlen1 hlay1 hoth1 hok1t hok1f hm1
              have htm_s1_0 : 0 < s1.core.tmp.length := by
                simp [s1, s_cp, s1_st, hlen1.core_ok.tmp_len_arr]; omega
              have htm_s1_1 : 1 < s1.core.tmp.length := by
                simp [s1, s_cp, s1_st, hlen1.core_ok.tmp_len_arr]; omega
              have hrefs1 :
                  fullArenaClauseRefsCore s1.core = fullArenaClauseRefsCore s_cp.core := rfl
              have hwat1 : ModeWatchesInv F_cur s1.core := fullWatchPush_preserves_modeWatchesInv
                hwat_cp hlay1 rfl rfl (fun r hr => hrefs1 ▸ hr)
                (fun hc => absurd hc (by decide)) (fun _ => ⟨bv32_mask_flag0 _,
                  fun hdm' => absurd hdm hdm', hcref32_lt,
                  hrefs1 ▸ hrefs_cp ▸ List.mem_append_right _
                    (by simp [bv32_ofNat_toNat (by omega : s.core.arena_len < 2 ^ 32)])⟩)
                hoth1 hok1t (fun h => (hok1f h).1)
              faa_steps
              · rw [bv64_trunc32_ofNat (by omega)]; c0_call hPush
                refine ⟨c, s1, R, rfl, hlen1, hlay1, (fun hc => absurd hc (by decide)),
                  (fun _ => ⟨bv32_mask_ne_sent _, hcref32_ne⟩), hm1, ?_⟩
                intro ok2 wvec2 wstk2 wlen2 wu2 wsort2 m2 s2 hlen2 hlay2 hoth2 hok2t hok2f hm2
                have hrefs2 : fullArenaClauseRefsCore s2.core = fullArenaClauseRefsCore s1.core :=
                  rfl
                have hwat2 : ModeWatchesInv F_cur s2.core := fullWatchPush_preserves_modeWatchesInv
                  hwat1 hlay2 rfl rfl (fun r hr => hrefs2 ▸ hr)
                  (fun hc => absurd hc (by decide)) (fun _ => ⟨bv32_mask_flag0 _,
                    fun hdm' => absurd hdm hdm', hcref32_lt,
                    hrefs2 ▸ hrefs1 ▸ hrefs_cp ▸ List.mem_append_right _
                      (by simp [bv32_ofNat_toNat (by omega : s.core.arena_len < 2 ^ 32)])⟩)
                  hoth2 hok2t (fun h => (hok2f h).1)
                have hfin : ∀ fred' ni' nr' mf,
                    (FullMem c (addClauseState s len.toNat arena' wvec2 wstk2 wlen2 wu2
                      fred' ni' nr' wsort2) ⋆ R) mf → Q (BitVec.ofNat 64 s.core.arena_len, ()) mf :=
                  fun fred' ni' nr' mf hm_f => by
                    let s_fin := addClauseState s len.toNat arena' wvec2 wstk2 wlen2 wu2
                      fred' ni' nr' wsort2
                    have hlen_f : s_fin.LengthsOk c :=
                      { core_ok := { hlen2.core_ok with arena_len_arr := by simp [s_fin, harl] }
                        scratch_ok := hlen2.scratch_ok }
                    have hrefs_f0 :
                        fullArenaClauseRefsCore s_fin.core =
                          fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
                      fullArenaClauseRefsCore_append hw.arena hge3' rfl hhold_cp hnoshrk_cp hsz_cp
                    have hwat_f : ModeWatchesInv F_cur s_fin.core :=
                      hwat2.with_wstk rfl rfl rfl rfl rfl
                        (fun r hr => by
                          have h1 : fullArenaClauseRefsCore s2.core =
                              fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
                            hrefs2.trans (hrefs1.trans hrefs_cp)
                          rwa [hrefs_f0, ← h1])
                    have hlits_fin : fullArenaClauseLitsCore s_fin.core s.core.arena_len =
                        (s.core.tmp.take len.toNat).map BitVec.toNat := hlits_cp
                    obtain ⟨hw_f, hrefs_f, hhold_f⟩ := addEntailedClause_preserves_witness
                      hlen hw hlen_f hge3' hlits_lt hent_cl hhold_cp hnoshrk_cp hsz_cp hlits_fin
                      hwat_f
                    have hgarb_f : fullArenaClauseGarb s_fin s.core.arena_len = false := by
                      change (fullArenaHdrCore s_fin.core s.core.arena_len &&&
                        0x00080000#32 != 0#32) = false
                      unfold fullArenaHdrCore; simp [s_fin, hnogarb_cp]
                    have hnd_f : FullArenaVarsNodup s → FullArenaVarsNodup s_fin :=
                      fun hnd r hr hng => by
                        change r ∈ fullArenaClauseRefsCore s_fin.core at hr
                        rw [hrefs_f, List.mem_append, List.mem_singleton] at hr
                        rcases hr with hr | rfl
                        · change fullArenaClauseGarbCore s_fin.core r = false at hng
                          rw [(hhold_f r hr).1] at hng
                          unfold fullArenaClauseLits; rw [(hhold_f r hr).2]
                          exact hnd r hr hng
                        · unfold fullArenaClauseLits
                          rw [show fullArenaClauseLitsCore s_fin.core s.core.arena_len =
                              (s.core.tmp.take len.toNat).map BitVec.toNat from hlits_fin,
                            List.map_map]
                          exact hnd_tmp
                    exact hQ (BitVec.ofNat 64 s.core.arena_len) arena' alen1 wvec2 wstk2 wlen2 wu2
                      fred' ni' nr' wsort2 mf (Or.inr rfl) hlen_f hw_f
                      (fun r hr => by
                        change r ∈ fullArenaClauseRefsCore s_fin.core
                        rw [hrefs_f]; exact List.mem_append_left _ hr)
                      hnd_f
                      (fun _ => ⟨rfl,
                        by change s.core.arena_len ∈ fullArenaClauseRefsCore s_fin.core
                           rw [hrefs_f]; exact List.mem_append_right _ (by simp),
                        hgarb_f, hlits_fin⟩)
                      hm_f
                faa_steps
                · exact hfin (BitVec.ofNat 64 s.core.arena_len) s.core.num_irred
                    (s.core.num_redundant + 1#64) _ (by assumption)
                · exact hfin s.core.first_reducible s.core.num_irred
                    (s.core.num_redundant + 1#64) _ (by assumption)
                · exact hfin s.core.first_reducible (s.core.num_irred + 1#64)
                    s.core.num_redundant _ (by assumption)
                · exact hJw () m2 ⟨wvec2, wstk2, wlen2, wu2, wsort2, hlen2, hwat2, hm2⟩
              · exact hJw () m1 ⟨wvec1, wstk1, wlen1, wu1, wsort1, hlen1, hwat1, hm1⟩
        · intro L hL; faa_steps; exact hL len.toNat _ m1 ⟨0, arena1, Nat.zero_le _, by simp, rfl,
            hlen1.core_ok.arena_len_arr, fun _ _ => rfl, fun _ h => by omega, hm1⟩

end LeanQbe.T.Examples.Kissat.Full
