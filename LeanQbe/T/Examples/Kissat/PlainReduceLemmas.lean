module

public import LeanQbe.T.Examples.Kissat.PlainReduceLemmas4

/-!
# Kissat `D-Plain` Compaction GC (`plain_sweep`) & Reduction (`plain_reduce`) (`Wave 2b`)

Provides verified parametric `(Γ : Env)` `Func.wp` contracts for:
1. `plain_reduce` (`plainReduceSpec`)
2. `plain_sweep` (`plainSweepSpec`, in `PlainReduceLemmas3`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.C0Step
open Kraken.Bedrock2.Test

section
open scoped PlainReduceTactics
open PlainReduceHelpers

private def SameRd (s0 s : PlainState) : Prop :=
  s.d_cur = s0.d_cur ∧ s.d_val = s0.d_val ∧ s.probing = s0.probing ∧
  s.tmp_cnt = s0.tmp_cnt ∧ s.tmp_len = s0.tmp_len ∧
  s.min_clr_len = s0.min_clr_len ∧ s.min_clr_full = s0.min_clr_full ∧
  s.mrk = s0.mrk ∧ s.tmp = s0.tmp ∧ s.min_stk = s0.min_stk ∧ s.min_clr = s0.min_clr

private theorem SameRd.eq {s0 s : PlainState} (h : SameRd s0 s) :
    { s0 with
      vals := s.vals, lvl := s.lvl, rsns := s.rsns, trl := s.trl,
      trail_pos := s.trail_pos, trail_end := s.trail_end, propagated := s.propagated,
      cur_level := s.cur_level, fuel := s.fuel, unflushed := s.unflushed,
      wvec := s.wvec, wstk := s.wstk, arena := s.arena, arena_len := s.arena_len,
      wlen := s.wlen, wusable := s.wusable, arena_garbage := s.arena_garbage,
      first_reducible := s.first_reducible, num_irred := s.num_irred,
      num_redundant := s.num_redundant, num_binary := s.num_binary,
      confl_type := s.confl_type, confl_ref := s.confl_ref,
      confl_lit0 := s.confl_lit0, confl_lit1 := s.confl_lit1,
      oom := s.oom, heur := s.heur } = s := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  cases s0; cases s; simp only at *
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11; rfl

private theorem reduce_ret {c : PlainCfg} {F0 : CNF Nat} {s0 s1 : PlainState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {r : BitVec 64} {m1 : Mem 64}
    (hQ : ∀ r vals' lvl' rsns' trl' tp' te' prop' cl' fuel' unfl' wvec' wstk' arena' alen' wlen'
      wu' ag' fred' ni' nr' nb' ctype' cref' c0' c1' oom' heur' m',
      let s' : PlainState := { s0 with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', cur_level := cl', fuel := fuel',
        unflushed := unfl', wvec := wvec', wstk := wstk', arena := arena',
        arena_len := alen', wlen := wlen', wusable := wu', arena_garbage := ag',
        first_reducible := fred', num_irred := ni', num_redundant := nr', num_binary := nb',
        confl_type := ctype', confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
        oom := oom', heur := heur' }
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → fuel'.toNat ≤ s0.fuel.toNat →
      (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * c.mv) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → PlainCoreInv c F0 s' ∧ cl' ≤ s0.cur_level ∧ (s0.oom = 0#64 → oom' = 0#64)) →
      (r = 1#64 → 0 < cl' → cl' = s0.cur_level ∧ vals' = s0.vals ∧ lvl' = s0.lvl ∧
        trl' = s0.trl ∧ tp' = s0.trail_pos ∧ te' = s0.trail_end) →
      (PlainMem c s' ⋆ R) m' → Q (r, ()) m')
    (hsame : SameRd s0 s1) (hlen : s1.LengthsOk c) (hr : r = 0#64 ∨ r = 1#64 ∨ r = 20#64)
    (hfuel : s1.fuel.toNat ≤ s0.fuel.toNat)
    (htrl : ∀ i < s1.trail_end, (s1.trl[i]?.getD 0#32).toNat < 2 * c.mv)
    (hu : r = 20#64 → F0.Unsat)
    (h1 : r = 1#64 → PlainCoreInv c F0 s1 ∧ s1.cur_level ≤ s0.cur_level ∧
      (s0.oom = 0#64 → s1.oom = 0#64))
    (hk : r = 1#64 → 0 < s1.cur_level →
      s1.cur_level = s0.cur_level ∧ s1.vals = s0.vals ∧ s1.lvl = s0.lvl ∧
      s1.trl = s0.trl ∧ s1.trail_pos = s0.trail_pos ∧ s1.trail_end = s0.trail_end)
    (hm : (PlainMem c s1 ⋆ R) m1) : Q (r, ()) m1 := by
  have heq := hsame.eq
  exact hQ r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1
    (heq ▸ hlen) hr hfuel htrl hu (fun h => ⟨heq ▸ (h1 h).1, (h1 h).2⟩) hk (heq ▸ hm)

private def RdPreOk (c : PlainCfg) (F0 : CNF Nat) (s0 s1 : PlainState) : Prop :=
  PlainCoreInv c F0 s1 ∧ SameRd s0 s1 ∧ s1.fuel.toNat ≤ s0.fuel.toNat ∧
  s1.cur_level ≤ s0.cur_level ∧ (s0.oom = 0#64 → s1.oom = 0#64) ∧
  (0 < s1.cur_level → s1.cur_level = s0.cur_level ∧ s1.vals = s0.vals ∧
    s1.lvl = s0.lvl ∧ s1.trl = s0.trl ∧ s1.trail_pos = s0.trail_pos ∧
    s1.trail_end = s0.trail_end)

theorem plain_sweep_wp (Γ : Env)
    (hAN : ∀ args m Q X, plainArenaNextSpec args m Q X →
      Γ "plain_arena_next" [i64, i32] [i32] args m Q X)
    (hWD : ∀ args m Q X, plainWstackDefragSpec args m Q X →
      Γ "plain_wstack_defrag" [i64] [] args m Q X)
    (hWP : ∀ args m Q X, plainWatchPushSpec args m Q X →
      Γ "plain_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hAS : ∀ args m Q X, plainAssignSpec args m Q X →
      Γ "plain_assign" [i64, i32, i32] [] args m Q X)
    (hLR : ∀ args m Q X, plainLitRankSpec args m Q X →
      Γ "plain_lit_rank" [i64, i64, i32] [i64] args m Q X) :
    ∀ args m Q X, plainSweepSpec args m Q X →
      Func.wp Γ plain_sweep_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s0, R, rfl, hinv0, hrm0, hm0, hQ⟩
  have hlen0 := hinv0.lengths; have hmv := c.hmv; have har := c.harena; have hcw := c.hwcap
  unfold dimacsBound at hmv har hcw
  c0_unmdata; pr_steps!
  refine plain_sweep_p1_wp Γ _ hinv0 (by dsimp only [LeanQbe.T.lift2]; rfl) hm0 ?_
  intro s1 m1 hs1_all hag1 hb1_all hm1
  have hlen1 := hs1_all.2.1; have hsame1 := hs1_all.2.2.1
  c0_unmdata; pr_steps!
  refine wp_call_of_spec _ _ (hWD (c.hdr, ()) m1 _ X
    ⟨c, s1, R, rfl, hlen1, hb1_all.1.layout, hm1,
      fun wvec' wstk' wlen' wsort' m_p1 hlen_w hl_w hwle_w hws_w hm_p1 => ?_⟩)
  obtain ⟨s_p1, hlen_p1, hsame_p1, hrt_p1, hv_p1, hlvl_p1, hrsn_p1, htrl_p1, htp_p1, hte_p1,
    hunf_p1, har_p1, hal_p1, hag_p1, hoom_p1, hb_p1, hm_p1⟩ :=
    sw1_defrag_to_p2 hs1_all hag1 hlen_w hl_w hws_w hm_p1
  c0_unmdata; pr_let
  refine wp_load_of (load_arena_len hm_p1) ?_
  rw [hal_p1]; pr_let
  have hb0 : BinWatchesOnly c F0 s0 0 :=
    ⟨hinv0.watches, fun _ hl => absurd hl (Nat.not_lt_zero _)⟩
  refine wp_join_group (ts := [i64, i64, i64, i64, i64, .bool, .bool])
    (fun v m3 => ∃ s_e : PlainState,
      SwP2ExitInv c F0 s0 v.2.1.toNat v.2.2.2.2.2.1 v.2.2.2.2.2.2.1 s_e ∧
      (PlainMem c s_e ⋆ R) m3) ?_ ?_
  · rintro _ ⟨p15_0, dst, fred, irred, redd, unsat, new_unit, ⟨⟩⟩ m3 ⟨s_e, he, hm3⟩
    dsimp only
    exact plain_sweep_p3_wp Γ hWP hLR hinv0 he hm3 hQ
  · intro J_p2 hJ_p2
    refine wp_loop_inv (ts := [i64, i64, i64, i64, i64, .bool])
      (fun v m2 => ∃ s_2 : PlainState,
        SwP2Inv c F0 s0 v.1.toNat v.2.1.toNat v.2.2.2.2.2.1 s_2 ∧
        (PlainMem c s_2 ⋆ R) m2)
      (fun v _ => s0.arena_len - v.1.toNat) ?_ ?_
    · intro J2 hJ2; c0_unmdata; pr_steps!
      have hinit : SwP2Inv c F0 s0 0 0 false s_p1 :=
        ⟨hlen_p1, hsame_p1, hrt_p1, hal_p1, hag_p1, hoom_p1,
          trailValsInv_congr (trailValsInv_of_core hinv0) hsame_p1.cur_level hv_p1 hlvl_p1
            hrsn_p1 htrl_p1 htp_p1 hte_p1,
          hb_p1, arenaPrefix_init_eq hinv0 har_p1, rsnReloc_init_congr hrsn_p1,
          hsame_p1.cur_level, Nat.le_of_eq hte_p1.symm, fun h => (by cases h),
          fun _ => ⟨hv_p1, hlvl_p1, htrl_p1, htp_p1, hte_p1⟩⟩
      exact hJ2 (0#64, 0#64, 0xFFFFFFFF#64, 0#64, 0#64, false, ()) _
        ⟨s_p1, by dsimp only; exact hinit, hm_p1⟩
    · rintro J2 ⟨src, dst, fred, irred, redd, new_unit, ⟨⟩⟩ m2
        ⟨s_2, ⟨hlen_2, hsame_2, hrt_2, hal_2, hag_2, hoom_2, htv_2, hb_2, hp_2, hrr_2,
          hscl_2, hte_le_2, hnew_2, hkeep_2⟩, hm2⟩ hJ2
      clear s_p1 hlen_p1 hsame_p1 hrt_p1 hv_p1 hlvl_p1 hrsn_p1 htrl_p1 htp_p1 hte_p1 hunf_p1
        har_p1 hal_p1 hag_p1 hoom_p1 hb_p1 hm_p1
      dsimp only at *
      have hsrc_le := hp_2.src_le_alen; have hdst_le := hp_2.dst_le_src
      have hlen_a := hinv0.lengths.arena_len_le
      pr_jnz
      · have hsrc_lt : src.toNat < s0.arena_len := by bv_omega
        have hsuf_c := arenaPrefix_suffix_congr hinv0 hp_2 hsrc_lt
        have hsrc_ref : src.toNat ∈ arenaClauseRefs s0 := hsuf_c.1
        have hwf0 := hinv0.arena.refs_wf src.toNat hsrc_ref
        pr_jnz
        · exact absurd (show src.toNat + 3 ≤ s0.arena_len from hwf0.1) (by bv_omega)
        · obtain ⟨hsrc2_len, hsrc_len, hsrc2_eq, hsrc_t, hnsrc_eq, h2_ar, hnb0_lt, hnb0_le,
              hhdr_eq, hsz_eq, hsz_nat⟩ := sw2_hdr_prep hinv0 hlen_2 hsuf_c
          c0_unmdata; pr_let
          refine wp_load_of (c0_load_arena_arena (s := s_2) (i := src) hsrc_len hm2) ?_
          pr_let
          refine wp_load_of (c0_load_arena_arena (s := s_2) (i := src + 2#64) hsrc2_len hm2) ?_
          pr_let
          refine wp_call_of_spec _ _ (hAN (c.hdr, src.truncate 32, ()) m2 _ X
            ⟨c, s_2, R, rfl, hlen_2, hm2, ?_⟩)
          rw [hsrc_t, hal_2, hsuf_c.2.2.2.2]
          pr_let; pr_jnz
          · c0_unmdata; pr_steps!
            have hgb : (s0.arena[src.toNat]?.getD 0#32 &&& 0x00080000#32) ≠ 0#32 := by
              rw [← hhdr_eq, List.getElem?_eq_getElem hsrc_len, Option.getD_some]
              exact (by assumption)
            exact hJ2 (_, dst, fred, irred, redd, new_unit, ()) m2
              (by dsimp only; rw [hnsrc_eq]; omega)
              ⟨s_2, by dsimp only; rw [hnsrc_eq]; exact ⟨hlen_2, hsame_2, hrt_2, hal_2, hag_2,
                hoom_2, htv_2, hb_2, arenaPrefix_skip hinv0 hp_2 hsrc_lt,
                rsnReloc_skip hinv0 hrr_2 hsrc_ref (Or.inl hgb), hscl_2, hte_le_2, hnew_2,
                hkeep_2⟩, hm2⟩
          · pr_jnz
            · have : arenaClauseSize s0 src.toNat < 3 := by rw [← hsz_nat]; bv_omega
              exact absurd hwf0.2.1 (by omega)
            · pr_jnz
              · have hsr2 : (src.toNat + 2) % 2 ^ 64 = (src + 2#64).toNat := by bv_omega
                have hsz_mod :
                    (s_2.arena[(src.toNat + 2) % 2 ^ 64]'(by
                      rw [hsr2]; exact hsrc2_len)).toNat = arenaClauseSize s0 src.toNat := by
                  rw [← hsz_nat]; exact congrArg BitVec.toNat
                    (Option.some.inj (by simp only [← List.getElem?_eq_getElem, hsr2]))
                have : s0.arena_len < src.toNat + 3 + arenaClauseSize s0 src.toNat := by
                  rw [← hsz_mod]; bv_omega
                exact absurd hsuf_c.2.1 (by omega)
              · have hng0 : (s_2.arena[src.toNat] &&& 0x00080000#32) = 0#32 := by assumption
                have hng_s0 : arenaClauseGarb s0 src.toNat = false := by
                  unfold arenaClauseGarb arenaHdr
                  rw [← hhdr_eq, List.getElem?_eq_getElem hsrc_len, Option.getD_some,
                    hng0]; rfl
                have hsr2_eq :
                    (src.toNat + 2 % 2 ^ 64) % 2 ^ 64 = (src + 2#64).toNat := by bv_omega
                have hsz_mod2 :
                    (s_2.arena[(src.toNat + 2 % 2 ^ 64) % 2 ^ 64]'(by
                      rw [hsr2_eq]; exact hsrc2_len)).toNat =
                      arenaClauseSize s0 src.toNat := by
                  rw [← hsz_nat]; exact congrArg BitVec.toNat
                    (Option.some.inj (by simp only [← List.getElem?_eq_getElem, hsr2_eq]))
                refine wp_join_group (ts := [i64, .bool, .bool, i32])
                  (fun ve me => ∃ ar_e : List (BitVec 32), ve.1 = src ∧
                    ve.2.2.1 = new_unit ∧
                    SwEmitOk c F0 s0 s_2 src.toNat dst.toNat ve.2.2.2.1.toNat ar_e ∧
                    (PlainMem c { s_2 with arena := ar_e } ⋆ R) me) ?_ ?_
                · rintro _ ⟨vsrc, _, vnu, new_sz, ⟨⟩⟩ me ⟨ar_e, hvsrc, hnu, he, hme⟩
                  dsimp only at hvsrc hnu he; subst vsrc; subst vnu
                  obtain ⟨hge3, hle_old, har_e, hpre_e, hsuf_e, hlits_e, hent_e, hlits_c⟩ := he
                  have hemit := swP2_body4_emit hinv0 hp_2 hsrc_lt hge3 hle_old har_e hpre_e
                    hsuf_e hlits_e hent_e hng0
                  have har1_le : dst.toNat + 3 + new_sz.toNat ≤ c.arena_cap := by omega
                  have hd1_eq : (dst + 1#64).toNat = dst.toNat + 1 := bv64_add_toNat (by omega)
                  have hd2_eq : (dst + 2#64).toNat = dst.toNat + 2 := bv64_add_toNat (by omega)
                  have hd0_lt : dst.toNat < ar_e.length := by rw [har_e]; omega
                  let hdr' := s_2.arena[src.toNat] &&& ~~~0x00A00000#32
                  let ar0 := ar_e.set dst.toNat hdr'
                  let ar0b := ar0.set (dst + 1#64).toNat 2#32
                  let ar1_v := ((ar_e.set dst.toNat hdr').set (dst + 1#64).toNat 2#32).set
                    (dst + 2#64).toNat new_sz
                  have hd1_lt : (dst + 1#64).toNat < ar0.length := by
                    rw [List.length_set, har_e, hd1_eq]; omega
                  have hd2_lt : (dst + 2#64).toNat < ar0b.length := by
                    simp only [ar0b, ar0, List.length_set, har_e, hd2_eq]; omega
                  have hsz32_eq : BitVec.ofNat 32 new_sz.toNat = new_sz := by
                    apply BitVec.eq_of_toNat_eq
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                  have har1_eq :
                      ((ar_e.set dst.toNat hdr').set (dst.toNat + 1) 2#32).set
                        (dst.toNat + 2) (BitVec.ofNat 32 new_sz.toNat) = ar1_v := by
                    dsimp only [ar1_v]; rw [hd1_eq, hd2_eq, hsz32_eq]
                  have hemit' := hemit
                  dsimp only at hemit'
                  rw [har1_eq] at hemit'
                  c0_unmdata; pr_let
                  refine wp_store_sep (c0_store_arena_arena (s := { s_2 with arena := ar_e })
                    (i := dst) hdr' hd0_lt hme) fun md0 hm_d0 => ?_; pr_let
                  refine wp_store_sep (c0_store_arena_arena (s := { s_2 with arena := ar0 })
                    (i := dst + 1#64) 2#32 hd1_lt hm_d0) fun md1 hm_d1 => ?_; pr_let
                  refine wp_store_sep (c0_store_arena_arena (s := { s_2 with arena := ar0b })
                    (i := dst + 2#64) new_sz hd2_lt hm_d1) fun md2 hm_d2 => ?_
                  have hm_ar1 : (PlainMem c { s_2 with arena := ar1_v } ⋆ R) md2 := hm_d2
                  generalize har1_g : ar1_v = ar1 at hm_ar1 hemit'
                  clear har1_g ar1_v ar0b ar0 hdr' har1_eq hemit hm_d0 hm_d1 hm_d2
                    hd0_lt hd1_lt hd2_lt hme md0 md1
                  pr_let
                  refine wp_join_group (ts := [])
                    (fun _ mr => ∃ rsns' : List (BitVec 32),
                      RsnRelocInv s0 { s_2 with arena := ar1, rsns := rsns' }
                        (arenaNextOff s0.arena s0.arena_len src.toNat)
                        (dst.toNat + 3 + new_sz.toNat) ∧
                      TrailValsInv c F0 { s_2 with arena := ar1, rsns := rsns' } ∧
                      rsns'.length = c.mv ∧
                      (PlainMem c { s_2 with arena := ar1, rsns := rsns' } ⋆ R) mr) ?_ ?_
                  · rintro _ ⟨⟩ mr ⟨rsns', hrr_r, htv_r, hrs_len, hmr⟩
                    refine wp_join_group (ts := [i64, i64, i64])
                      (fun _ mc => (PlainMem c { s_2 with arena := ar1, rsns := rsns' } ⋆
                        R) mc) ?_ ?_
                    · rintro _ ⟨fred', irred', redd', ⟨⟩⟩ mc hmc
                      have hdn : (dst + 3 + new_sz.setWidth 64).toNat =
                          dst.toNat + 3 + new_sz.toNat := by
                        rw [BitVec.toNat_add, show (dst + 3 : BitVec 64) = dst + 3#64 from rfl,
                          bv64_add_toNat (by omega), bv_c0_zext32_64,
                          Nat.mod_eq_of_lt (by omega)]
                      c0_unmdata; pr_steps!
                      exact hJ2 (_, dst + 3 + new_sz.setWidth 64,
                          fred', irred', redd', new_unit, ()) mc
                        (by dsimp only; rw [hnsrc_eq]; omega)
                        ⟨{ s_2 with arena := ar1, rsns := rsns' },
                          by dsimp only; rw [hnsrc_eq, hdn]; exact ⟨
                            { lengthsOk_with_arena hlen_2 hemit'.1 with rsns_len := hrs_len },
                            hsame_2, hrt_2, hal_2, hag_2, hoom_2, htv_r,
                            binWatchesOnly_repack hb_2 rfl rfl rfl,
                            arenaPrefix_congr_arena hemit'.2.1 rfl, hrr_r, hscl_2,
                            hte_le_2, hnew_2, hkeep_2⟩, hmc⟩
                    · intro Jcnt hJcnt; pr_jnz
                      · refine wp_join_group (ts := [i64]) (fun _ mf =>
                            (PlainMem c { s_2 with arena := ar1, rsns := rsns' } ⋆ R) mf) ?_ ?_
                        · rintro _ ⟨fred', ⟨⟩⟩ mf hmf
                          c0_unmdata; pr_steps!
                          exact hJcnt (fred', irred, redd + 1#64, ()) mf hmf
                        · intro Jfr hJfr; pr_jnz <;> (c0_unmdata; pr_steps!)
                          · exact hJfr (dst, ()) _ hmr
                          · exact hJfr (fred, ()) _ hmr
                      · c0_unmdata; pr_steps!
                        exact hJcnt (fred, irred + 1#64, redd, ()) _ hmr
                  · intro Jrsn hJrsn
                    have htr_r := trailValsInv_congr (s' := { s_2 with arena := ar1 })
                      htv_2 rfl rfl rfl rfl rfl rfl rfl
                    have hrs_len2 : s_2.rsns.length = c.mv := hlen_2.rsns_len
                    have hnohit_s2 : 0 < s0.cur_level →
                        arenaClauseLits { s_2 with
                          arena := ar1, arena_len := dst.toNat + 3 + new_sz.toNat } dst.toNat =
                          arenaClauseLits s0 src.toNat := by
                      intro hcur; rw [hemit'.2.2.2.2.2.1]; exact hlits_c hcur
                    have hsz_ar1 : (ar1[dst.toNat + 2]?.getD 0#32).toNat = new_sz.toNat :=
                      hemit'.2.2.1
                    pr_jnz
                    · refine wp_join_group (ts := [i32])
                        (fun _ mr => ∃ rsns' : List (BitVec 32),
                          RsnRelocInv s0 { s_2 with arena := ar1, rsns := rsns' }
                            (arenaNextOff s0.arena s0.arena_len src.toNat)
                            (dst.toNat + 3 + new_sz.toNat) ∧
                          TrailValsInv c F0 { s_2 with arena := ar1, rsns := rsns' } ∧
                          rsns'.length = c.mv ∧
                          (PlainMem c { s_2 with arena := ar1, rsns := rsns' } ⋆ R) mr) ?_ ?_
                      · rintro _ ⟨_, ⟨⟩⟩ mr hmr; exact hJrsn () mr hmr
                      · intro J_rd hJrd
                        refine wp_loop_inv (ts := [i32])
                          (fun v mi => v.1.toNat ≤ new_sz.toNat ∧
                            (0 < s0.cur_level → ∀ k < v.1.toNat,
                              let lit := ar1[dst.toNat + 3 + k]?.getD 0#32;
                              ¬ (lit.toNat / 2 < c.mv ∧
                                (0#8).slt (s0.vals[lit.toNat]?.getD 0#8) = true ∧
                                s_2.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32 =
                                  BitVec.ofNat 32 src.toNat)) ∧
                            (PlainMem c { s_2 with arena := ar1 } ⋆ R) mi)
                          (fun v _ => new_sz.toNat - v.1.toNat) ?_ ?_
                        · intro Jri hJri; c0_unmdata; pr_steps!
                          exact hJri (0#32, ()) _ ⟨Nat.zero_le _,
                            fun _ _ h => absurd h (Nat.not_lt_zero _), hm_ar1⟩
                        · rintro Jri ⟨ir, ⟨⟩⟩ mi ⟨hir_le, hno_ir, hmi⟩ hJri
                          dsimp only at hir_le hno_ir hJri
                          pr_jnz
                          · have hir_lt : ir.toNat < new_sz.toNat := by bv_omega
                            have hir1 : (ir + 1#32).toNat = ir.toNat + 1 :=
                              bv32_add_toNat (by omega)
                            have hdi_eq : (dst + 3#64 + ir.setWidth 64).toNat =
                                dst.toNat + 3 + ir.toNat := by
                              rw [BitVec.toNat_add, bv64_add_toNat (by omega), bv_c0_zext32_64,
                                Nat.mod_eq_of_lt (by omega)]
                            have hdi_lt : (dst + 3#64 + ir.setWidth 64).toNat < ar1.length := by
                              rw [hemit'.1, hdi_eq]; omega
                            have hlit_ir :
                                (ar1[dst.toNat + 3 + ir.toNat]'(by
                                  rw [hemit'.1]; omega)).toNat < 2 * c.mv := by
                              have h0 := hlits_e ir.toNat hir_lt
                              rw [← hemit'.2.2.2.1 ir.toNat hir_lt,
                                List.getElem?_eq_getElem (by rw [hemit'.1]; omega),
                                Option.getD_some] at h0
                              exact h0
                            have hlit_ar :
                                ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt =
                                  ar1[dst.toNat + 3 + ir.toNat]'(by rw [hemit'.1]; omega) :=
                              Option.some.inj (by
                                rw [← List.getElem?_eq_getElem hdi_lt, hdi_eq,
                                  List.getElem?_eq_getElem (by rw [hemit'.1]; omega)])
                            c0_unmdata; pr_let
                            refine wp_load_of (c0_load_arena_arena
                              (s := { s_2 with arena := ar1 })
                              (i := dst + 3#64 + ir.setWidth 64) hdi_lt hmi) ?_
                            pr_let
                            refine wp_join_group (ts := [])
                              (fun _ mn => (0 < s0.cur_level →
                                let lit := ar1[dst.toNat + 3 + ir.toNat]?.getD 0#32;
                                ¬ (lit.toNat / 2 < c.mv ∧
                                  (0#8).slt (s0.vals[lit.toNat]?.getD 0#8) = true ∧
                                  s_2.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32 =
                                    BitVec.ofNat 32 src.toNat)) ∧
                                (PlainMem c { s_2 with arena := ar1 } ⋆ R) mn) ?_ ?_
                            · rintro _ ⟨⟩ mn ⟨hno_cur, hmn⟩
                              c0_unmdata; pr_steps!
                              exact hJri (ir + 1#32, ()) mn (by dsimp only; omega)
                                ⟨by dsimp only; omega, fun hc k hk => by
                                  dsimp only at hk; rw [hir1] at hk
                                  by_cases hkeq : k = ir.toNat
                                  · subst hkeq; exact hno_cur hc
                                  · exact hno_ir hc k (by omega), hmn⟩
                            · intro Jrn hJrn
                              have hva_l : s_2.vals.length = 2 * c.mv := hlen_2.vals_len
                              have hrs_l : s_2.rsns.length = c.mv := hrs_len2
                              obtain ⟨hlit_v, hlit_v64, hdom_v⟩ := sw2_rsn_prep htv_2 hva_l
                                hdi_lt hdi_eq (by rw [hemit'.1]; omega) hlit_ar hlit_ir
                              have hdi_mod : (dst.toNat + 3 + ir.toNat) % 2 ^ 64 =
                                  (dst + 3#64 + ir.setWidth 64).toNat := by bv_omega
                              have hb32_64 : ∀ x : BitVec 32, x.toNat < 2 ^ 64 :=
                                fun x => Nat.lt_trans x.isLt (by decide)
                              have hidx_eq :
                                  (ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt).toNat /
                                    2 % 2 ^ 64 =
                                  ((ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt >>>
                                    (1 : Nat)).setWidth 64).toNat := by
                                rw [bv_c0_zext32_64, PlainReduceTactics.bv_c0_shr1n_32,
                                  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
                                    (Nat.div_le_self _ 2) (hb32_64 _))]
                              pr_jnz
                              · c0_unmdata; pr_steps!
                                · rename_i h_pos
                                  simp only [hdi_mod, Nat.mod_eq_of_lt (hb32_64 _)] at h_pos
                                  simp only [hdi_mod, hidx_eq] at hc
                                  exact hJrd (ir, ()) _ (sw2_rsn_hit hinv0 hlen_2 htv_2 hrr_2
                                    hscl_2 hkeep_2 hsrc_ref hdst_le hge3 hemit'.1 har1_le
                                    hnohit_s2 hemit'.2.2.2.2.2.2.1 hemit'.2.2.2.2.2.2.2
                                    hemit'.2.2.2.2.1 hsz_ar1 htr_r hrs_len2 hdi_lt hdi_eq
                                    hir_lt hlit_ar hlit_ir hdom_v h_pos hc hm)
                                · simp only [hdi_mod, hidx_eq] at hc
                                  exact hJrn () mi ⟨fun _ => sw2_rsn_neg1 hemit'.1 hdi_lt
                                    hdi_eq hlit_ar (by omega) har hrs_l hlit_ir hc, hmi⟩
                                · simp only [hdi_mod, Nat.mod_eq_of_lt (hb32_64 _)] at hc
                                  exact hJrn () mi ⟨sw2_rsn_neg_le hemit'.1 hkeep_2 hva_l
                                    hdi_lt hdi_eq hlit_ar hlit_ir hdom_v (by rw [hc]; decide),
                                    hmi⟩
                              · c0_unmdata; pr_steps!
                                simp only [hdi_mod, hidx_eq,
                                  Nat.mod_eq_of_lt (show c.mv < 2 ^ 64 by omega)] at hc
                                exact hJrn () mi ⟨fun _ => sw2_rsn_neg_mv hdi_lt hdi_eq hlit_ar
                                  (by simpa only [bv_c0_zext32_64,
                                    PlainReduceTactics.bv_c0_shr1n_32] using hc), hmi⟩
                          · have hir_eq : ir.toNat = new_sz.toNat := by bv_omega
                            c0_unmdata; pr_steps!
                            have hres := sw2_rsn_nohit_done hinv0 hrm0 hrr_2 hsrc_ref
                              hemit'.2.2.1 hemit'.1 har1_le hnohit_s2 hemit'.2.2.2.2.1 htr_r
                              hrs_len2 fun hcur => Or.inr fun k hk => by
                                rw [hir_eq] at hno_ir; exact hno_ir hcur k hk
                            exact hJrd (ir, ()) mi ⟨s_2.rsns, hres.1, hres.2.1, hres.2.2, hmi⟩
                    · c0_unmdata; pr_steps!
                      have hnrsn0 : (s0.arena[src.toNat]?.getD 0#32 &&& 0x00200000#32) = 0#32 :=
                        by rw [← hhdr_eq, List.getElem?_eq_getElem hsrc_len, Option.getD_some]
                           exact (by assumption)
                      have hres := sw2_rsn_nohit_done hinv0 hrm0 hrr_2 hsrc_ref hemit'.2.2.1
                        hemit'.1 har1_le hnohit_s2 hemit'.2.2.2.2.1 htr_r hrs_len2
                        fun _ => Or.inl hnrsn0
                      exact hJrsn () _ ⟨s_2.rsns, hres.1, hres.2.1, hres.2.2, hm_ar1⟩
                · intro J_emit hJ_emit; pr_jnz
                  · have hcl_bd : s0.cur_level < 2 ^ 64 := by
                      have := hinv0.cur_level_le; have := hinv0.lengths.trail_end_le; omega
                    have hcl0 : s0.cur_level = 0 := by change s0.cur_level = 0; bv_omega
                    refine wp_join_group (ts := [i32, .bool, i32])
                      (fun vo mo => ∃ ar_o : List (BitVec 32),
                        (vo.2.1 = false → SwFiltInv c F0 s0 s_2 src.toNat dst.toNat
                          (arenaClauseSize s0 src.toNat) vo.1.toNat
                          (arenaClauseSize s0 src.toNat) ar_o) ∧
                        (vo.2.1 = true → ar_o.length = c.arena_cap ∧
                          (∀ k < dst.toNat, ar_o[k]? = s_2.arena[k]?) ∧
                          (∀ k, src.toNat + 3 + arenaClauseSize s0 src.toNat ≤ k →
                            k < s0.arena_len → ar_o[k]? = s_2.arena[k]?)) ∧
                        (PlainMem c { s_2 with arena := ar_o } ⋆ R) mo) ?_ ?_
                    · rintro _ ⟨new_sz, sat, _, ⟨⟩⟩ mo ⟨ar_o, hno, hyes, hmo⟩
                      dsimp only at hno hyes
                      pr_jnz
                      · obtain ⟨har_y, hpre_y, hsuf_y⟩ := hyes (by assumption)
                        c0_unmdata; pr_steps!
                        exact hJ2 (_, dst, fred, irred, redd, new_unit, ()) mo
                          (by dsimp only; rw [hnsrc_eq]; omega)
                          ⟨{ s_2 with arena := ar_o }, by
                            dsimp only; rw [hnsrc_eq]
                            exact sw2_sat_skip hinv0 hlen_2 hsame_2 hrt_2 hal_2 hag_2 hoom_2
                              htv_2 hb_2 hp_2 hrr_2 hscl_2 hte_le_2 hnew_2 hcl0 hsrc_lt har_y
                              hpre_y hsuf_y, hmo⟩
                      · obtain ⟨hn_le, _, har_o, hpre_o, hsuf_o, hlits_o, hent_o⟩ := hno
                          (by cases sat <;> first | rfl | contradiction)
                        have hlen_o := lengthsOk_with_arena hlen_2 har_o
                        have htv_o := trailValsInv_congr (s' := { s_2 with arena := ar_o })
                          htv_2 rfl rfl rfl rfl rfl rfl rfl
                        have hb_o : BinWatchesOnly c F0 { s_2 with arena := ar_o } (2 * c.mv) :=
                          binWatchesOnly_repack hb_2 rfl rfl rfl
                        have hent_fin : F0.EntailsClause (cnfClause
                            (((ar_o.drop (dst.toNat + 3)).take new_sz.toNat).map
                              BitVec.toNat)) := by
                          simpa only [Nat.sub_self, List.take_zero, List.map_nil,
                            List.append_nil] using hent_o
                        pr_jnz
                        · have hsz0 : new_sz.toNat = 0 := by bv_omega
                          rw [hsz0, List.take_zero, List.map_nil] at hent_fin
                          have hexit : SwP2ExitInv c F0 s0 dst.toNat true new_unit
                              { s_2 with arena := ar_o } :=
                            ⟨hlen_o, hsame_2, hrt_2, Nat.le_trans hdst_le hsrc_le,
                              htv_o.trail_lits_lt,
                              fun _ => ⟨hcl0, atRoot_unsat_of_nil hent_fin⟩,
                              fun h => by cases h⟩
                          c0_unmdata; pr_steps!
                          exact hJ_p2 (src, dst, fred, irred, redd, true, new_unit, ()) mo
                            ⟨{ s_2 with arena := ar_o }, by dsimp only; exact hexit, hmo⟩
                        · pr_jnz
                          · have hsz1 : new_sz.toNat = 1 := by bv_omega
                            have hu_eq : (dst + 3#64).toNat = dst.toNat + 3 :=
                              bv64_add_toNat (by omega)
                            have hud_lt : (dst + 3#64).toNat < ar_o.length := by
                              rw [hu_eq, har_o]; omega
                            obtain ⟨hulit, hl0_u, hvals_u, hdom_u⟩ := sw2_sz1_ctx hsz1 hu_eq
                              hud_lt hlits_o hent_fin hlen_o htv_o
                            c0_unmdata; pr_let
                            refine wp_load_of (c0_load_arena_arena
                              (s := { s_2 with arena := ar_o }) (i := dst + 3#64)
                              hud_lt hmo) ?_; pr_let
                            refine wp_load_of (c0_load_arena_vals
                              (s := { s_2 with arena := ar_o })
                              (i := (ar_o[(dst + 3#64).toNat]).setWidth 64)
                              (by dsimp only; rw [bv_c0_zext32_64]; exact hvals_u) hmo) ?_
                            pr_let; simp only [bv_c0_zext32_64]; pr_jnz
                            · have hfals_u : s_2.vals[(ar_o[(dst + 3#64).toNat]).toNat]?.getD
                                  0#8 = 0xFF#8 := by
                                rw [List.getElem?_eq_getElem hvals_u, Option.getD_some]
                                exact vals_eq_neg_of_sext_lt hdom_u (by assumption)
                              have hexit : SwP2ExitInv c F0 s0 dst.toNat true new_unit
                                  { s_2 with arena := ar_o } :=
                                ⟨hlen_o, hsame_2, hrt_2, Nat.le_trans hdst_le hsrc_le,
                                  htv_o.trail_lits_lt,
                                  fun _ => ⟨hcl0, atRoot_unsat_of_unit_neg htv_o
                                    (hsame_2.cur_level.trans hcl0) hulit hl0_u hfals_u⟩,
                                  fun h => by cases h⟩
                              c0_unmdata; pr_steps!
                              exact hJ_p2 (src, dst, fred, irred, redd, true, new_unit, ()) mo
                                ⟨{ s_2 with arena := ar_o }, by dsimp only; exact hexit, hmo⟩
                            · refine wp_join_group (ts := [.bool])
                                (fun vnu m_nu => ∃ s_nu : PlainState,
                                  s_nu.LengthsOk c ∧ SameSwPre s0 s_nu ∧
                                  s_nu.heur.rel_trigger = s0.heur.rel_trigger ∧
                                  s_nu.arena = ar_o ∧ s_nu.arena_len = s_2.arena_len ∧
                                  s_nu.arena_garbage = s_2.arena_garbage ∧
                                  s_nu.oom = s_2.oom ∧ TrailValsInv c F0 s_nu ∧
                                  BinWatchesOnly c F0 s_nu (2 * c.mv) ∧
                                  s0.trail_end ≤ s_nu.trail_end ∧
                                  (vnu.1 = true → s0.trail_end < s_nu.trail_end) ∧
                                  (PlainMem c s_nu ⋆ R) m_nu) ?_ ?_
                              · rintro _ ⟨nu', ⟨⟩⟩ m_nu ⟨s_nu, hlen_nu, hsame_nu, hrt_nu,
                                  har_nu, hal_nu, hag_nu, hoom_nu, htv_nu, hb_nu, hte_nu,
                                  hnew_nu, hmnu⟩
                                c0_unmdata; pr_steps!
                                exact hJ2 (_, dst, fred, irred, redd, nu', ()) m_nu
                                  (by dsimp only; rw [hnsrc_eq]; omega)
                                  ⟨s_nu, by
                                    dsimp only; rw [hnsrc_eq]
                                    exact sw2_unit_keep hinv0 hp_2 hsrc_lt hcl0 hal_2 hag_2
                                      hoom_2 har_o hpre_o hsuf_o hlen_nu hsame_nu hrt_nu har_nu
                                      hal_nu hag_nu hoom_nu htv_nu hb_nu hte_nu hnew_nu, hmnu⟩
                              · intro J_nu hJ_nu; c0_unmdata; pr_let
                                refine wp_load_of (c0_load_arena_vals
                                  (s := { s_2 with arena := ar_o })
                                  (i := (ar_o[(dst + 3#64).toNat]).setWidth 64)
                                  (by dsimp only; rw [bv_c0_zext32_64]; exact hvals_u) hmo) ?_
                                pr_let; simp only [bv_c0_zext32_64]; pr_jnz
                                · have hval0_u :
                                      s_2.vals[(ar_o[(dst + 3#64).toNat]).toNat]?.getD
                                        0#8 = 0#8 := by
                                    rw [List.getElem?_eq_getElem hvals_u, Option.getD_some]
                                    exact vals_eq_zero_of_sext_eq hdom_u (by assumption)
                                  have hte_lt := trailValsInv_te_lt htv_o hulit hval0_u
                                  dsimp only at hte_lt
                                  c0_unmdata; pr_steps!
                                  refine wp_call_of_spec _ _ (hAS (c.hdr, _, 0xFFFFFFFF#32, ())
                                    mo _ X ⟨c, { s_2 with arena := ar_o }, R, rfl, hlen_o,
                                      by rw [hsame_2.cur_level, hcl0]; omega, hmo, ?_⟩)
                                  have hno_ov : ¬ (c.mv ≤ (ar_o[(dst + 3#64).toNat]).toNat / 2 ∨
                                      c.mv ≤ s_2.trail_end) := by omega
                                  simp only [LeanQbe.T.Arg.val_var, hno_ov, ↓reduceIte]
                                  intro phases' m_as hph hlen_as hm_as
                                  have hs2_cl0 : s_2.cur_level = 0 :=
                                    hsame_2.cur_level.trans hcl0
                                  have hcl0_t : (s_2.cur_level = 0) = True := eq_true hs2_cl0
                                  simp only [hcl0_t, ↓reduceIte] at hlen_as hm_as
                                  have htv_as := trailValsInv_with_l0_assign hinv0 hlen_o htv_o
                                    hb_o hs2_cl0 hulit hval0_u
                                    (unfl' := s_2.unflushed + 1#64) hph hl0_u
                                  let l_u := ar_o[(dst + 3#64).toNat]
                                  let s_as : PlainState := { s_2 with
                                    arena := ar_o,
                                    vals := (s_2.vals.set l_u.toNat 1#8).set
                                      (l_u.toNat ^^^ 1) 0xFF#8,
                                    lvl := s_2.lvl.set (l_u.toNat / 2)
                                      (BitVec.ofNat 32 s_2.cur_level),
                                    rsns := s_2.rsns.set (l_u.toNat / 2) 0xFFFFFFFF#32,
                                    trl := s_2.trl.set s_2.trail_end l_u,
                                    trail_pos := s_2.trail_pos.set (l_u.toNat / 2)
                                      (BitVec.ofNat 32 s_2.trail_end),
                                    trail_end := s_2.trail_end + 1,
                                    unflushed := s_2.unflushed + 1#64,
                                    heur := { s_2.heur with phases := phases' } }
                                  c0_unmdata; pr_steps!
                                  exact hJ_nu (true, ()) m_as ⟨s_as, hlen_as, hsame_2, hrt_2,
                                    rfl, rfl, rfl, rfl, htv_as,
                                    binWatchesOnly_repack hb_o rfl rfl rfl,
                                    by dsimp only [s_as]; omega,
                                    fun _ => by dsimp only [s_as]; omega, hm_as⟩
                                · c0_unmdata; pr_steps!
                                  exact hJ_nu (new_unit, ()) mo ⟨{ s_2 with arena := ar_o },
                                    hlen_o, hsame_2, hrt_2, rfl, rfl, rfl, rfl, htv_o,
                                    hb_o, hte_le_2, fun h => (hnew_2 h).2, hmo⟩
                          · pr_jnz
                            · have hsz2 : new_sz.toNat = 2 := by
                                have heq : new_sz = 2#32 := by assumption
                                rw [heq]; rfl
                              have h3_eq : (dst + 3#64).toNat = dst.toNat + 3 :=
                                bv64_add_toNat (by omega)
                              have h4_eq : (dst + 4#64).toNat = dst.toNat + 4 :=
                                bv64_add_toNat (by omega)
                              have hd3_lt : (dst + 3#64).toNat < ar_o.length := by
                                rw [h3_eq, har_o]; omega
                              have hd4_lt : (dst + 4#64).toNat < ar_o.length := by
                                rw [h4_eq, har_o]; have := hwf0.2.1; omega
                              obtain ⟨hl0_2, hl1_2, hb0_2, hb1_2, hne0_2, hne1_2⟩ :=
                                sw2_sz2_prep hsz2 h3_eq h4_eq hd3_lt hd4_lt hlits_o hent_fin
                              c0_unmdata; pr_let
                              refine wp_load_of (c0_load_arena_arena
                                (s := { s_2 with arena := ar_o }) (i := dst + 3#64)
                                hd3_lt hmo) ?_; pr_let
                              refine wp_load_of (c0_load_arena_arena
                                (s := { s_2 with arena := ar_o }) (i := dst + 4#64)
                                hd4_lt hmo) ?_; pr_let
                              refine wp_join_group (ts := [])
                                (fun _ m_m => ∃ s_m : PlainState,
                                  s_m.LengthsOk c ∧ SameSwPre s0 s_m ∧
                                  s_m.heur.rel_trigger = s0.heur.rel_trigger ∧
                                  (∀ i < s_m.trail_end,
                                    (s_m.trl[i]?.getD 0#32).toNat < 2 * c.mv) ∧
                                  (PlainMem c s_m ⋆ R) m_m) ?_ ?_
                              · rintro _ ⟨⟩ m_m ⟨s_m, hlen_m, hsame_m, hrt_m, htrl_m, hmm⟩
                                have hexit : SwP2ExitInv c F0 s0 dst.toNat false new_unit
                                    { s_m with oom := 1#64 } :=
                                  ⟨{ hlen_m with },
                                    hsame_m, hrt_m, Nat.le_trans hdst_le hsrc_le, htrl_m,
                                    fun h => Bool.noConfusion h,
                                    fun _ hoom => by
                                      dsimp only at hoom; exact absurd hoom (by decide)⟩
                                c0_unmdata; pr_steps!
                                exact hJ_p2 (src, dst, fred, irred, redd, false, new_unit, ())
                                  _ ⟨{ s_m with oom := 1#64 }, by dsimp only; exact hexit,
                                    by assumption⟩
                              · intro J_o2 hJo2
                                refine wp_call_of_spec _ _
                                  (hWP (c.hdr, _, _, 0#32, 1#32, ()) mo _ X
                                    ⟨c, { s_2 with arena := ar_o }, R, rfl, hlen_o,
                                      hb_o.1.layout, fun _ => by
                                        simp only [LeanQbe.T.Arg.val_var,
                                          LeanQbe.T.Arg.val_imm, LeanQbe.T.lift2]
                                        exact hne0_2,
                                      fun h => absurd h (by decide), hmo,
                                      fun ok1 wv1 ws1 wl1 wu1 wso1 m_w1 hlen_w1 hlay_w1 hoth1
                                        hok1 _ hm_w1 => ?_⟩)
                                pr_jnz
                                · obtain ⟨_, _, hsz1, hpre1, hw1a, _⟩ := hok1 (by assumption)
                                  simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
                                    LeanQbe.T.lift2] at hw1a
                                  let sw1 := pushWatchState { s_2 with arena := ar_o }
                                    wv1 ws1 wso1 wl1 wu1
                                  have hb_w1 := binWatchesOnly_push hb_o hlay_w1
                                    (fun _ hr => hr) hb0_2 hoth1 hsz1 hpre1 hw1a
                                  refine wp_call_of_spec _ _
                                    (hWP (c.hdr, _, _, 0#32, 1#32, ()) m_w1 _ X
                                      ⟨c, sw1, R, rfl, hlen_w1, hlay_w1, fun _ => by
                                          simp only [LeanQbe.T.Arg.val_var,
                                            LeanQbe.T.Arg.val_imm, LeanQbe.T.lift2]
                                          exact hne1_2,
                                        fun h => absurd h (by decide), hm_w1,
                                        fun ok2 wv2 ws2 wl2 wu2 wso2 m_w2 hlen_w2 hlay_w2 hoth2
                                          hok2 _ hm_w2 => ?_⟩)
                                  pr_jnz
                                  · obtain ⟨_, _, hsz2w, hpre2, hw2a, _⟩ := hok2 (by assumption)
                                    simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
                                      LeanQbe.T.lift2] at hw2a
                                    have hinv_b2 := sw2_sz2_done hinv0 hp_2 hsrc_lt hcl0 hsame_2
                                      hrt_2 hal_2 hag_2 hoom_2 htv_o hb_2 hte_le_2 hnew_2 har_o
                                      hpre_o hsuf_o hb0_2 hb1_2 hlay_w1 hoth1 hsz1
                                      hpre1 hw1a hlen_w2 hlay_w2 hoth2 hsz2w hpre2 hw2a
                                    c0_unmdata; pr_steps!
                                    exact hJ2 (_, dst, fred, irred, redd, new_unit, ()) _
                                      (by dsimp only; rw [hnsrc_eq]; omega)
                                      ⟨_, by dsimp only; rw [hnsrc_eq]; exact hinv_b2,
                                        by assumption⟩
                                  · exact hJo2 () m_w2 ⟨pushWatchState sw1 wv2 ws2 wso2 wl2 wu2,
                                      hlen_w2, hsame_2, hrt_2, htv_o.trail_lits_lt, hm_w2⟩
                                · exact hJo2 () m_w1 ⟨pushWatchState { s_2 with arena := ar_o }
                                    wv1 ws1 wso1 wl1 wu1, hlen_w1, hsame_2, hrt_2,
                                    htv_o.trail_lits_lt, hm_w1⟩
                            · have h3_le : 3 ≤ new_sz.toNat := by bv_omega
                              c0_unmdata; pr_steps!
                              exact hJ_emit (src, false, new_unit, new_sz, ()) mo
                                ⟨ar_o, rfl, rfl, ⟨h3_le, hn_le, har_o, hpre_o, hsuf_o,
                                  hlits_o, hent_fin, fun h => absurd hcl0 (by omega)⟩, hmo⟩
                    · intro J_out hJ_out
                      refine wp_loop_inv (ts := [i32, i32])
                        (fun v mi => ∃ ar_i : List (BitVec 32),
                          SwFiltInv c F0 s0 s_2 src.toNat dst.toNat
                            (arenaClauseSize s0 src.toNat) v.1.toNat v.2.1.toNat ar_i ∧
                          (PlainMem c { s_2 with arena := ar_i } ⋆ R) mi)
                        (fun v _ => arenaClauseSize s0 src.toNat - v.2.1.toNat) ?_ ?_
                      · intro J_in hJ_in; c0_unmdata; pr_steps!
                        have hent0 : F0.EntailsClause (cnfClause (([] : List Nat) ++
                            (((s0.arena.drop (src.toNat + 3)).take
                              (arenaClauseSize s0 src.toNat)).map BitVec.toNat))) := by
                          rw [List.nil_append]
                          exact hinv0.arena.entails src.toNat hsrc_ref hng_s0
                        exact hJ_in (0#32, 0#32, ()) m2 ⟨s_2.arena,
                          ⟨Nat.zero_le _, Nat.zero_le _, h2_ar, fun _ _ => rfl,
                            fun _ _ _ => rfl, fun _ h => absurd h (by simp),
                            by simpa only [BitVec.toNat_zero, Nat.add_zero, Nat.sub_zero,
                              List.take_zero, List.map_nil] using hent0⟩, hm2⟩
                      · rintro J_in ⟨nsz, i, ⟨⟩⟩ mi ⟨ar_i, ⟨hnsz_le, hi_le, har_i, hpre_i,
                          hsuf_i, hlits_i, hent_i⟩, hmi⟩ hJ_in
                        dsimp only at hnsz_le hi_le hJ_in
                        pr_jnz
                        · have hi_lt : i.toNat < arenaClauseSize s0 src.toNat := by
                            rw [← hsz_nat]; bv_omega
                          dsimp only at hnsz_le hi_le hsuf_i hlits_i hent_i
                          obtain ⟨hi1_eq, hsi3_eq, hsi3_lt, hlit_ar, hlit_lt, hent_i⟩ :=
                            sw2_filt_prep hinv0 hp_2 hsrc_ref hng_s0 hsuf_c.2.1 har_i hsuf_i
                              hi_lt hent_i
                          c0_unmdata; pr_let
                          refine wp_load_of (c0_load_arena_arena
                            (s := { s_2 with arena := ar_i }) (i := src + 3#64 + i.setWidth 64)
                            hsi3_lt hmi) ?_; pr_let
                          refine wp_join_group (ts := [i32, .bool])
                            (fun vs ms => ∃ ar_s : List (BitVec 32),
                              SwFiltInv c F0 s0 s_2 src.toNat dst.toNat
                                (arenaClauseSize s0 src.toNat) vs.1.toNat (i.toNat + 1) ar_s ∧
                              (PlainMem c { s_2 with arena := ar_s } ⋆ R) ms) ?_ ?_
                          · rintro _ ⟨nsz', _, ⟨⟩⟩ ms ⟨ar_s, hf_s, hms⟩
                            c0_unmdata; pr_steps!
                            exact hJ_in (nsz', i + 1#32, ()) ms (by dsimp only; omega)
                              ⟨ar_s, by dsimp only; exact hi1_eq ▸ hf_s, hms⟩
                          · intro J_st hJ_st
                            refine wp_join_group (ts := [])
                              (fun _ mw => (PlainMem c { s_2 with arena := ar_i } ⋆ R) mw) ?_ ?_
                            · rintro _ ⟨⟩ mw hmw
                              have hdi_eq : (dst + 3#64 + nsz.setWidth 64).toNat =
                                  dst.toNat + 3 + nsz.toNat := by
                                rw [BitVec.toNat_add, bv64_add_toNat (by omega),
                                  bv_c0_zext32_64, Nat.mod_eq_of_lt (by omega)]
                              have hdi3 : (dst + 3#64 + nsz.setWidth 64).toNat <
                                  ({ s_2 with arena := ar_i } :
                                    PlainState).arena.length := by
                                dsimp only; rw [har_i, hdi_eq]; omega
                              have hnsz1 : (nsz + 1#32).toNat = nsz.toNat + 1 :=
                                bv32_add_toNat (by omega)
                              c0_unmdata; pr_let
                              refine wp_store_sep (c0_store_arena_arena
                                (s := { s_2 with arena := ar_i })
                                (i := dst + 3#64 + nsz.setWidth 64) _ hdi3 hmw)
                                fun _ hmw' => ?_
                              pr_let
                              exact hJ_st (nsz + 1#32, false, ()) _
                                (sw2_filt_push hnsz_le hi_lt hsuf_c.2.1 hlen_a hdst_le har_i
                                  hsi3_lt hpre_i hsuf_i hlits_i hent_i hlit_lt
                                  hlit_ar hdi_eq hnsz1 hmw')
                            · intro J_w hJ_w
                              have hlv_len : s_2.lvl.length = c.mv := hlen_2.lvl_len
                              have hva_len : s_2.vals.length = 2 * c.mv := hlen_2.vals_len
                              pr_jnz
                              · have hlv_d2 : ((ar_i[(src + 3#64 + i.setWidth 64).toNat] >>>
                                    (1 : Nat)).setWidth 64).toNat <
                                    ({ s_2 with arena := ar_i } : PlainState).lvl.length := by
                                  dsimp only; rw [bv_c0_zext32_64,
                                    PlainReduceTactics.bv_c0_shr1n_32, hlv_len]
                                  omega
                                c0_unmdata; pr_let
                                refine wp_load_of (c0_load_arena_lvl
                                  (s := { s_2 with arena := ar_i }) hlv_d2 hmi) ?_
                                pr_let; pr_jnz
                                · have hv_ar : ((ar_i[(src + 3#64 +
                                      i.setWidth 64).toNat]).setWidth 64).toNat <
                                      ({ s_2 with arena := ar_i } : PlainState).vals.length :=
                                    by dsimp only; rw [bv_c0_zext32_64, hva_len]; exact hlit_lt
                                  c0_unmdata; pr_let
                                  refine wp_load_of (c0_load_arena_vals
                                    (s := { s_2 with arena := ar_i }) hv_ar hmi) ?_
                                  pr_let; pr_jnz
                                  · refine wp_load_of (c0_load_arena_vals
                                      (s := { s_2 with arena := ar_i }) hv_ar hmi) ?_
                                    pr_let; pr_jnz
                                    · exact hJ_out (nsz, true, i, ()) mi ⟨ar_i,
                                        fun h => (Bool.false_ne_true h.symm).elim,
                                        fun _ => ⟨har_i, hpre_i, fun k hk1 hk2 =>
                                          hsuf_i k (by omega) hk2⟩, hmi⟩
                                    · rename_i hc_nz
                                      have hsi_m : (src.toNat + 3 + i.toNat) % 2 ^ 64 =
                                          (src + 3#64 + i.setWidth 64).toNat := by bv_omega
                                      have hb32_64 : ∀ x : BitVec 32, x.toNat < 2 ^ 64 :=
                                        fun x => Nat.lt_trans x.isLt (by decide)
                                      have hse0 : ∀ {w}, BitVec.signExtend 32
                                          (BitVec.setWidth 8 (0 : BitVec w)) = 0#32 :=
                                        fun {_} => by simp
                                      simp only [hsi_m, Nat.mod_eq_of_lt (hb32_64 _),
                                        hse0] at hc_nz hc
                                      exact hJ_st (nsz, false, ()) mi ⟨ar_i,
                                        sw2_filt_fals hsame_2 htv_2 hcl0 hva_len hnsz_le
                                          hi_lt har_i hsi3_lt hsi3_eq hpre_i hsuf_i hlits_i
                                          hlit_lt (by simpa [hlit_ar, hsi3_eq] using hent_i)
                                          hc_nz (by simp only [hc]; decide), hmi⟩
                                  · exact hJ_w () mi hmi
                                · exact hJ_w () mi hmi
                              · c0_unmdata; pr_steps!; exact hJ_w () mi hmi
                        · have hi_eq : i.toNat = arenaClauseSize s0 src.toNat := by
                            first | (rw [← hsz_nat]; bv_omega) |
                              (rw [hsz_mod2] at *; bv_omega)
                          c0_unmdata; pr_steps!
                          exact hJ_out (nsz, false, i, ()) mi ⟨ar_i, fun _ => by
                            rw [hi_eq] at hnsz_le hi_le hsuf_i hent_i
                            exact ⟨hnsz_le, hi_le, har_i, hpre_i, hsuf_i, hlits_i, hent_i⟩,
                            fun h => (Bool.false_ne_true h).elim, hmi⟩
                  · refine wp_loop_inv (ts := [i32]) (fun v mc => ∃ ar_c : List (BitVec 32),
                        v.1.toNat ≤ arenaClauseSize s0 src.toNat ∧
                        ar_c.length = c.arena_cap ∧
                        (∀ k < dst.toNat, ar_c[k]? = s_2.arena[k]?) ∧
                        (∀ k, src.toNat + 3 + v.1.toNat ≤ k → k < s0.arena_len →
                          ar_c[k]? = s_2.arena[k]?) ∧
                        (∀ k < v.1.toNat,
                          ar_c[dst.toNat + 3 + k]? = s0.arena[src.toNat + 3 + k]?) ∧
                        (PlainMem c { s_2 with arena := ar_c } ⋆ R) mc)
                      (fun v _ => arenaClauseSize s0 src.toNat - v.1.toNat) ?_ ?_
                    · intro Jc hJc; c0_unmdata; pr_steps!
                      exact hJc (0#32, ()) m2 ⟨s_2.arena, Nat.zero_le _, h2_ar,
                        fun _ _ => rfl, fun _ _ _ => rfl, fun _ h => absurd h (by simp), hm2⟩
                    · rintro Jc ⟨ic, ⟨⟩⟩ mc
                        ⟨ar_c, hic_le, har_c, hpre_c, hsuf_ic, hcp_c, hmc⟩ hJc
                      dsimp only at hic_le hJc; pr_jnz
                      · have hic_lt : ic.toNat < arenaClauseSize s0 src.toNat := by
                          rw [← hsz_nat]; bv_omega
                        obtain ⟨hic1, hsi_eq, hdi_eq, hsi_lt, hdi_lt, har_sc⟩ :=
                          sw2_copy_prep hinv0 hp_2 hsuf_c.2.1 hdst_le hic_lt har_c hsuf_ic
                        c0_unmdata; pr_let
                        refine wp_load_of (c0_load_arena_arena
                          (s := { s_2 with arena := ar_c })
                          (i := src + 3#64 + ic.setWidth 64) hsi_lt hmc) ?_; pr_let
                        refine wp_store_sep (c0_store_arena_arena
                          (s := { s_2 with arena := ar_c })
                          (i := dst + 3#64 + ic.setWidth 64) _ hdi_lt hmc)
                          fun _ hm_cp => ?_; pr_let
                        exact hJc (ic + 1#32, ()) _ (by dsimp only; omega)
                          (sw2_copy_step hic_lt hic1 hdst_le har_c hsi_lt hsi_eq hdi_eq hpre_c
                            hsuf_ic hcp_c har_sc hm_cp)
                      · have hic_eq : ic.toNat = arenaClauseSize s0 src.toNat := by
                          first | (rw [← hsz_nat]; bv_omega) |
                            (rw [hsz_mod2] at *; bv_omega)
                        c0_unmdata; pr_steps!
                        exact hJ_emit
                          (src, false, new_unit, s_2.arena[(src + 2#64).toNat], ()) mc
                          ⟨ar_c, rfl, rfl, sw2_copy_emit hinv0 hsrc_ref hng_s0 hwf0.2.1
                            hsuf_c.2.1 hdst_le hic_eq hsz_nat har_c hpre_c hsuf_ic hcp_c, hmc⟩
      · have hsrc_alen : src.toNat = s0.arena_len := by bv_omega
        have hexit : SwP2ExitInv c F0 s0 dst.toNat false new_unit s_2 :=
          ⟨hlen_2, hsame_2, hrt_2, by omega, htv_2.trail_lits_lt,
            fun h => (Bool.false_ne_true h).elim,
            fun _ _ => ⟨htv_2, hb_2, hsrc_alen ▸ hp_2, hsrc_alen ▸ hrr_2, hscl_2,
              hnew_2, hkeep_2⟩⟩
        c0_unmdata; pr_steps!
        exact hJ_p2 (src, dst, fred, irred, redd, false, new_unit, ()) m2
          ⟨s_2, by dsimp only; exact hexit, hm2⟩

theorem plain_reduce_wp (Γ : Env)
    (hIS : ∀ args m Q X, plainIsqrtSpec args m Q X →
      Γ "plain_isqrt" [i64] [i64] args m Q X)
    (hBT : ∀ args m Q X, plainBacktrackSpec args m Q X →
      Γ "plain_backtrack" [i64, i64] [] args m Q X)
    (hPR : ∀ args m Q X, plainPropagateSpec args m Q X →
      Γ "plain_propagate" [i64] [i64] args m Q X)
    (hRT : ∀ args m Q X, plainRecomputeTiersSpec args m Q X →
      Γ "plain_recompute_tiers" [i64] [] args m Q X)
    (hMR : ∀ args m Q X, plainMarkReasonsSpec args m Q X →
      Γ "plain_mark_reasons" [i64, .bool] [] args m Q X)
    (hAN : ∀ args m Q X, plainArenaNextSpec args m Q X →
      Γ "plain_arena_next" [i64, i32] [i32] args m Q X)
    (hSR : ∀ args m Q X, plainSortRedsSpec args m Q X →
      Γ "plain_sort_reds" [i64, i64] [] args m Q X)
    (hIL : ∀ args m Q X, plainIlog10Spec args m Q X →
      Γ "plain_ilog10" [i64] [i64] args m Q X)
    (hSW : ∀ args m Q X, plainSweepSpec args m Q X →
      Γ "plain_sweep" [i64] [i64] args m Q X) :
    ∀ args m Q X, plainReduceSpec args m Q X →
      Func.wp Γ plain_reduce_body args m Q X := by
  rintro ⟨h, force, ⟨⟩⟩ m Q X ⟨c, F0, s0, R, rfl, hinv0, hm0, hQ⟩
  have hlen0 := hinv0.lengths; have hmv := c.hmv; have har := c.harena; have hred := c.hred
  unfold dimacsBound at hmv har hred
  have hcl_bd : s0.cur_level < 2 ^ 64 := by
    have := hinv0.cur_level_le; have := hlen0.trail_end_le; omega
  c0_unmdata; pr_steps!
  refine wp_call_of_spec _ _ (hIS _ m _ X fun isqr _ _ _ => ?_)
  c0_step; c0_step; c0_step
  let s_pre : PlainState :=
    { s0 with
      heur :=
        { s0.heur with
          reductions := s0.heur.reductions + 1
          reduce_limit := s0.heur.conflicts + 1000#64 * isqr } }
  have hinv_pre : PlainCoreInv c F0 s_pre :=
    hinv0.with_heur (pr_with_reduce hlen0.heur_ok (s0.heur.reductions + 1)
      (s0.heur.conflicts + 1000#64 * isqr))
  have hsame_pre : SameRd s0 s_pre := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine wp_join_group (ts := []) (fun _ m1 => ∃ s1, RdPreOk c F0 s0 s1 ∧ (PlainMem c s1 ⋆ R) m1)
    ?_ ?_
  · rintro J_fl ⟨⟩ m_r ⟨s_r, ⟨hinv_r, hsame_r, hfuel_r, hcl_r, hoom_r, hkeep_r⟩, hm_r⟩
    clear_except [Γ hBT hPR hRT hMR hAN hSR hIL hSW Q X c F0 s0 R force hmv har hred
      hQ s_r hinv_r hsame_r hfuel_r hcl_r hoom_r hkeep_r hm_r]
    c0_unmdata; pr_steps!
    refine wp_call_of_spec _ _ (hRT (c.hdr, ()) m_r _ X ⟨c, s_r, R, rfl, hinv_r.lengths, hm_r,
      fun h_rt m_rt hok_rt hm_rt => ?_⟩)
    let s2 : PlainState := { s_r with heur := h_rt }
    have hinv2 : PlainCoreInv c F0 s2 := hinv_r.with_heur hok_rt
    c0_unmdata; pr_steps!
    refine wp_call_of_spec _ _ (hMR (c.hdr, true, ()) m_rt _ X ⟨c, F0, s2, R, rfl, hinv2, hm_rt,
      fun ar3 m3 href3 hprop3 hrm3 hinv3 hm3 => ?_⟩)
    have hs3_ex : ∃ s3 : PlainState, RdPreOk c F0 s0 s3 ∧ ReasonsMarked s3 ∧
        (PlainMem c s3 ⋆ R) m3 :=
      ⟨{ s2 with arena := ar3 }, ⟨hinv3, hsame_r, hfuel_r, hcl_r, hoom_r, hkeep_r⟩, hrm3 rfl, hm3⟩
    obtain ⟨s3, ⟨hinv3, hsame3, hfuel3, hcl3, hoom3, hkeep3⟩, hrm3', hm3⟩ := hs3_ex
    clear_except [Γ hPR hMR hAN hSR hIL hSW Q X c F0 s0 R force hmv har hred hQ s3 hinv3
      hsame3 hfuel3 hcl3 hoom3 hkeep3 hrm3' hm3]
    let mkL1 (ar rr : List (BitVec 32)) : PlainState :=
      { s3 with arena := ar, heur := { s3.heur with red_refs := rr } }
    have hlen3 := hinv3.lengths
    c0_unmdata; pr_steps!
    refine wp_loop_inv (ts := [i64, i64])
      (fun v m1 => ∃ ar' rr',
        v.1.toNat ≤ c.red_cap ∧ v.2.1.toNat ≤ s3.arena_len ∧
        (v.2.1.toNat = s3.arena_len ∨ v.2.1.toNat ∈ arenaClauseRefs s3) ∧
        ArenaMaskOk 0x07FFFFFF#32 s3 ar' ∧ rr'.length = c.red_cap ∧
        (∀ k < v.1.toNat, let cr := (rr'[k]?.getD 0#32).toNat;
          cr ∈ arenaClauseRefs s3 ∧ cr + 2 < c.arena_cap ∧
          (s3.arena[cr]?.getD 0#32 &&& 0x00200000#32) = 0#32) ∧
        (PlainMem c (mkL1 ar' rr') ⋆ R) m1)
      (fun v _ => s3.arena_len - v.2.1.toNat) ?_ ?_
    · intro J_l1 hJl1; c0_unmdata; pr_steps!
      exact hJl1 (0#64, 0#64, ()) m3 ⟨s3.arena, s3.heur.red_refs, Nat.zero_le _, Nat.zero_le _,
        (arenaScan_zero hinv3.arena.len_ok).imp Eq.symm id, arenaMask_refl _ _,
        hlen3.heur_ok.red_refs_len, fun _ h => absurd h (Nat.not_lt_zero _), hm3⟩
    · rintro J_l1 ⟨rc, p, ⟨⟩⟩ m1 ⟨ar', rr', hrc, hp_le, hp_ref, hmk, hrr_len, hrr_ok, hm1⟩ hJl1
      dsimp only at hrc hp_le hp_ref hJl1
      have har'_len : ar'.length = c.arena_cap := hmk.1.trans hlen3.arena_len_arr
      have hp_alen : s3.arena_len ≤ c.arena_cap := hlen3.arena_len_le
      pr_jnz
      · have hp_lt : p.toNat < s3.arena_len := by bv_omega
        have href : p.toNat ∈ arenaClauseRefs s3 := hp_ref.resolve_left (by omega)
        have hwf := hinv3.arena.refs_wf p.toNat href
        have hrm_p : p.toNat < ar'.length := by rw [har'_len]; omega
        c0_unmdata; pr_steps!
        have hn_bnd : (p.truncate 32).toNat = p.toNat := by
          change (p.setWidth 32).toNat = p.toNat
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
        refine wp_call_of_spec _ _ (hAN (c.hdr, p.truncate 32, ()) m1 _ X
          ⟨c, mkL1 ar' rr', R, rfl,
            { hlen3 with arena_len_arr := har'_len,
                         heur_ok := { hlen3.heur_ok with red_refs_len := hrr_len } },
            hm1, ?_⟩)
        have hnxt := arenaMask_next (mask := 0x07FFFFFF#32) (by decide) hinv3 hmk href
        have hnb := arenaNextOff_bounds (ar := s3.arena) (alen := s3.arena_len) (cref := p.toNat)
          hwf.1
        have hn_step := arenaScan_step (fun r hr => (hinv3.arena.refs_wf r hr).2.2.2.2) href
        rw [hn_bnd, hnxt]
        have hn32 :
            ((BitVec.ofNat 32 (arenaNextOff s3.arena s3.arena_len p.toNat)).setWidth 64).toNat =
            arenaNextOff s3.arena s3.arena_len p.toNat := by
          rw [bv_c0_zext32_64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        pr_let
        refine wp_join_group (ts := [i64])
          (fun v_rc mj => ∃ arj rrj, v_rc.1.toNat ≤ c.red_cap ∧
            ArenaMaskOk 0x07FFFFFF#32 s3 arj ∧ rrj.length = c.red_cap ∧
            (∀ k < v_rc.1.toNat, let cr := (rrj[k]?.getD 0#32).toNat;
              cr ∈ arenaClauseRefs s3 ∧ cr + 2 < c.arena_cap ∧
              (s3.arena[cr]?.getD 0#32 &&& 0x00200000#32) = 0#32) ∧
            (PlainMem c (mkL1 arj rrj) ⋆ R) mj) ?_ ?_
        · rintro _ ⟨rc', ⟨⟩⟩ mj ⟨arj, rrj, hrc', hmkj, hrrj_len, hrrj_ok, hmj⟩
          c0_unmdata; pr_steps!
          exact hJl1 _ mj (by dsimp only; rw [hn32]; omega)
            ⟨arj, rrj, hrc', (by dsimp only; rw [hn32]; omega),
              (by dsimp only; rw [hn32]; exact hn_step), hmkj, hrrj_len, hrrj_ok, hmj⟩
        · intro J2 hJ2
          pr_jnz
          · pr_jnz
            · refine wp_join_group (ts := [])
                (fun _ mu => ∃ aru, ArenaMaskOk 0x07FFFFFF#32 s3 aru ∧
                  (PlainMem c (mkL1 aru rr') ⋆ R) mu) ?_ ?_
              · rintro _ ⟨⟩ mu ⟨aru, hmku, hmu⟩
                refine wp_join_group (ts := [i64])
                  (fun v_rc mj => ∃ rrj, v_rc.1.toNat ≤ c.red_cap ∧ rrj.length = c.red_cap ∧
                    (∀ k < v_rc.1.toNat, let cr := (rrj[k]?.getD 0#32).toNat;
                      cr ∈ arenaClauseRefs s3 ∧ cr + 2 < c.arena_cap ∧
                      (s3.arena[cr]?.getD 0#32 &&& 0x00200000#32) = 0#32) ∧
                    (PlainMem c (mkL1 aru rrj) ⋆ R) mj) ?_ ?_
                · rintro _ ⟨rc', ⟨⟩⟩ mj ⟨rrj, hrc', hrrj_len, hrrj_ok, hmj⟩
                  c0_unmdata; pr_steps!
                  exact hJ2 _ mj ⟨aru, rrj, hrc', hmku, hrrj_len, hrrj_ok, hmj⟩
                · intro J4 hJ4; pr_jnz
                  · refine wp_join_group (ts := [.bool])
                      (fun _ mk => (PlainMem c (mkL1 aru rr') ⋆ R) mk) ?_ ?_
                    · rintro _ ⟨keep, ⟨⟩⟩ mk hmk_m
                      refine wp_join_group (ts := [i64])
                        (fun v_rc mj => ∃ rrj, v_rc.1.toNat ≤ c.red_cap ∧ rrj.length = c.red_cap ∧
                          (∀ k < v_rc.1.toNat, let cr := (rrj[k]?.getD 0#32).toNat;
                            cr ∈ arenaClauseRefs s3 ∧ cr + 2 < c.arena_cap ∧
                            (s3.arena[cr]?.getD 0#32 &&& 0x00200000#32) = 0#32) ∧
                          (PlainMem c (mkL1 aru rrj) ⋆ R) mj) ?_ ?_
                      · rintro _ ⟨rc', ⟨⟩⟩ mj hmj
                        c0_unmdata; pr_steps!; exact hJ4 (rc', ()) mj hmj
                      · intro J6 hJ6; pr_jnz
                        · c0_unmdata; pr_steps!
                          exact hJ6 (rc, ()) mk ⟨rr', hrc, hrr_len, hrr_ok, hmk_m⟩
                        · c0_unmdata; pr_steps
                          · have hrc_cap : rc.toNat < c.red_cap := by bv_omega
                            have hrc_len : rc.toNat < rr'.length := by rw [hrr_len]; exact hrc_cap
                            have hrc1 : (rc + 1).toNat = rc.toNat + 1 := by bv_omega
                            have hp_s3 : p.toNat + 3 ≤ s3.arena_len := hwf.1
                            have hp_bd : p.toNat + 2 < c.arena_cap :=
                              Nat.lt_of_lt_of_le (by omega) hp_alen
                            c0_unmdata; pr_steps!
                            have hnrsn_p :
                                (s3.arena[p.toNat]?.getD 0#32 &&& 0x00200000#32) = 0#32 := by
                              have hm21 := bv32_mask_sub_eq (sub := 0x00200000#32) (by decide)
                                (hmk.2.2 p.toNat href)
                              rw [List.getElem?_eq_getElem hrm_p, Option.getD_some] at hm21
                              rw [← hm21]; assumption
                            change ∀ k < rc.toNat, _ at hrr_ok
                            have hrr_ok' : ∀ k < (rc + 1).toNat,
                                let cr := ((rr'.set rc.toNat (p.truncate 32))[k]?.getD 0#32).toNat;
                                cr ∈ arenaClauseRefs s3 ∧ cr + 2 < c.arena_cap ∧
                                (s3.arena[cr]?.getD 0#32 &&& 0x00200000#32) = 0#32 := fun k hk => by
                              rw [hrc1] at hk
                              by_cases hkr : k = rc.toNat
                              · subst hkr; dsimp only
                                rw [List.getElem?_set_self hrc_len, Option.getD_some, hn_bnd]
                                exact ⟨href, hp_bd, hnrsn_p⟩
                              · dsimp only; rw [List.getElem?_set_ne (Ne.symm hkr)]
                                exact hrr_ok k (by omega)
                            exact hJ6 (rc + 1, ()) _ ⟨rr'.set rc.toNat (p.truncate 32),
                              by dsimp only; rw [hrc1]; omega, by rw [List.length_set, hrr_len],
                              hrr_ok', by assumption⟩
                          · exact hJ6 (rc, ()) mk ⟨rr', hrc, hrr_len, hrr_ok, hmk_m⟩
                    · intro J5 hJ5; c0_unmdata
                      refine wp_join_group (ts := [])
                        (fun _ mj6 => (PlainMem c (mkL1 aru rr') ⋆ R) mj6) ?_ ?_
                      · rintro _ ⟨⟩ mj6 hmj6; c0_unmdata; pr_steps! <;> exact hJ5 _ _ hmj6
                      · intro J6 hJ6; c0_unmdata; pr_steps! <;>
                          first | exact hJ5 _ _ hmu | exact hJ6 () _ hmu
                  · c0_unmdata; pr_steps!
                    exact hJ4 _ mu ⟨rr', hrc, hrr_len, hrr_ok, hmu⟩
              · intro J3 hJ3; c0_unmdata; pr_steps!
                · exact hJ3 () _
                    ⟨_, arenaMask_set hmk href hrm_p (bv32_use_mask _ _), by assumption⟩
                · exact hJ3 () m1 ⟨ar', hmk, hm1⟩
            · c0_unmdata; pr_steps!
              exact hJ2 _ m1 ⟨ar', rr', hrc, hmk, hrr_len, hrr_ok, hm1⟩
          · c0_unmdata; pr_steps!
            exact hJ2 _ m1 ⟨ar', rr', hrc, hmk, hrr_len, hrr_ok, hm1⟩
      · obtain ⟨_, _, hinv3'⟩ := arenaMask_core (by decide) (by decide) hinv3 hmk
        have hrm3a : ReasonsMarked { s3 with arena := ar' } :=
          arenaMask_reasonsMarked (by decide) hinv3 hrm3' hmk
        let s3a : PlainState := mkL1 ar' rr'
        have hinv3a : PlainCoreInv c F0 s3a :=
          hinv3'.with_heur { hlen3.heur_ok with red_refs_len := hrr_len }
        have hrm3a' : ReasonsMarked s3a := hrm3a
        have hrr_a : ∀ k < rc.toNat, let cr := (s3a.heur.red_refs[k]?.getD 0#32).toNat;
            cr ∈ arenaClauseRefs s3a ∧ cr + 2 < c.arena_cap ∧
            (s3a.arena[cr]?.getD 0#32 &&& 0x00200000#32) = 0#32 := fun k hk => by
          obtain ⟨hr, hbd, hz⟩ := hrr_ok k hk
          have href_eq := (arenaMask_core (by decide) (by decide) hinv3 hmk).1
          have hm21 := bv32_mask_sub_eq (sub := 0x00200000#32) (by decide) (hmk.2.2 _ hr)
          refine ⟨by change _ ∈ arenaClauseRefs { s3 with arena := ar' }; rw [href_eq]; exact hr,
            hbd, by change (ar'[ _ ]?.getD 0#32 &&& 0x00200000#32) = 0#32; exact hm21.trans hz⟩
        c0_unmdata
        refine wp_join_group (ts := [])
          (fun _ m4 => ∃ s4, RdPreOk c F0 s0 s4 ∧
            (0 < s4.cur_level → ReasonsMarked s4) ∧ (PlainMem c s4 ⋆ R) m4) ?_ ?_
        · rintro J_sw ⟨⟩ m4 ⟨s4, ⟨hinv4, hsame4, hfuel4, hcl4, hoom4, hkeep4⟩, hrm4, hm4⟩
          clear_except [Γ hPR hMR hSW Q X c F0 s0 R force hmv har hred
            hQ s4 hinv4 hsame4 hfuel4 hcl4 hoom4 hkeep4 hrm4 hm4]
          have hlen4 := hinv4.lengths
          pr_let
          refine wp_join_group (ts := [])
            (fun _ m_end => ∃ s_e, RdPreOk c F0 s0 s_e ∧ (PlainMem c s_e ⋆ R) m_end) ?_ ?_
          · rintro _ ⟨⟩ m_end ⟨s_e, ⟨hinv_e, hsame_e, hfuel_e, hcl_e, hoom_e, hkeep_e⟩, hm_e⟩
            c0_unmdata; pr_steps!
            exact reduce_ret hQ hsame_e hinv_e.lengths (Or.inr (Or.inl rfl)) hfuel_e
              hinv_e.trail_lits_lt (fun h => by cases h) (fun _ => ⟨hinv_e, hcl_e, hoom_e⟩)
              (fun _ => hkeep_e) hm_e
          · intro J_ret1 hJ_ret1; pr_let
            refine wp_join_group (ts := [])
              (fun _ m_j4 => ∃ s4', RdPreOk c F0 s0 s4' ∧
                (0 < s4'.cur_level → ReasonsMarked s4') ∧ (PlainMem c s4' ⋆ R) m_j4) ?_ ?_
            · rintro _ ⟨⟩ m_j4 ⟨s4', hpre4', hrm4', hm4'⟩
              c0_unmdata
              refine wp_join_group (ts := [])
                (fun _ m_lp => ∃ s_lp, RdPreOk c F0 s0 s_lp ∧ (PlainMem c s_lp ⋆ R) m_lp) ?_ ?_
              · rintro _ ⟨⟩ m_lp hmlp; c0_unmdata; pr_steps!; exact hJ_ret1 () m_lp hmlp
              · intro J_e hJe
                let meas : Mem 64 → Nat := fun mw =>
                  match loadVal mw i64 (c.hdr + 144) with
                  | some x => c.mv - x.toNat
                  | none => 0
                have hmeas : ∀ {sw mw}, PlainCoreInv c F0 sw → (PlainMem c sw ⋆ R) mw →
                    meas mw = c.mv - sw.trail_end := fun {sw mw} hiw hmw => by
                  dsimp only [meas]; rw [load_arena_trail_end hmw]; dsimp only
                  have := hiw.lengths.trail_end_le
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                refine wp_loop_inv (ts := [])
                  (fun _ m_w => ∃ s_w, RdPreOk c F0 s0 s_w ∧
                    (0 < s_w.cur_level → ReasonsMarked s_w) ∧ (PlainMem c s_w ⋆ R) m_w)
                  (fun _ m_w => meas m_w) ?_ ?_
                · intro J_w hJ_w; exact hJ_w () m_j4 ⟨s4', hpre4', hrm4', hm4'⟩
                · rintro J_w ⟨⟩ m_w ⟨s_w, ⟨hinv_w, hsame_w, hfuel_w, hcl_w, hoom_w, hkeep_w⟩,
                      hrm_w, hm_w⟩ hJ_w
                  c0_unmdata; pr_steps!
                  refine wp_call_of_spec _ _ (hSW (c.hdr, ()) m_w _ X
                    ⟨c, F0, s_w, R, rfl, hinv_w, hrm_w, hm_w,
                      fun sr vals' lvl' rsns' trl' tp' te' unfl' wvec' wstk' arena' alen'
                        wlen' wu' fred' ni' nr' nb' oom' heur' m_sw hlen_sw hsr_r hrt_sw
                        htrl_sw hok_sw h0_sw h1_sw h2_sw hm_sw => ?_⟩)
                  let s_sw : PlainState :=
                    { s_w with
                      vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
                      trail_end := te', unflushed := unfl', wvec := wvec', wstk := wstk',
                      arena := arena', arena_len := alen', wlen := wlen', wusable := wu',
                      arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
                      num_redundant := nr', num_binary := nb', oom := oom', heur := heur' }
                  c0_unmdata; pr_steps!
                  · exact reduce_ret hQ hsame_w (s1 := s_sw) hlen_sw (Or.inr (Or.inr rfl)) hfuel_w
                      htrl_sw (fun _ => (h2_sw (by assumption)).2) (fun h => by cases h)
                      (fun h => by cases h) hm_sw
                  · exact reduce_ret hQ hsame_w (s1 := s_sw) hlen_sw (Or.inl rfl) hfuel_w htrl_sw
                      (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm_sw
                  · obtain ⟨hinv_sw, hoom_sw⟩ := hok_sw (Or.inl (by assumption))
                    exact hJe () m_sw ⟨s_sw, ⟨hinv_sw, hsame_w, hfuel_w, hcl_w, fun _ => hoom_sw,
                      fun hpos => by
                        obtain ⟨h1, h2, h3, h4, h5⟩ := h0_sw hpos (by assumption)
                        obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := hkeep_w hpos
                        exact ⟨hc1, h1.trans hc2, h2.trans hc3, h3.trans hc4, h4.trans hc5,
                          h5.trans hc6⟩⟩, hm_sw⟩
                  · have hsr1 : sr = 1#64 := by
                      rcases hsr_r with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
                    obtain ⟨hinv_sw, _⟩ := hok_sw (Or.inr hsr1)
                    obtain ⟨hcl0_sw, hte_lt⟩ := h1_sw hsr1
                    refine wp_call_of_spec _ _ (hPR (c.hdr, ()) m_sw _ X
                      ⟨c, F0, s_sw, R, rfl, hinv_sw, hm_sw,
                        fun pr vals2 lvl2 rsns2 trl2 tp2 te2 prop2 unfl2 wvec2 arena2 wstk2
                          wlen2 wu2 fuel2 ctype2 cref2 c0_2 c1_2 oom2 heur2 m_p hinv_p hte_p
                          hfuel_p _ _ _ _ hpr_r hpr0 hpr1 _ _ hm_p => ?_⟩)
                    let s_p3 : PlainState :=
                      { s_sw with
                        vals := vals2, lvl := lvl2, rsns := rsns2, trl := trl2, trail_pos := tp2,
                        trail_end := te2, propagated := prop2, unflushed := unfl2, wvec := wvec2,
                        arena := arena2, wstk := wstk2, wlen := wlen2, wusable := wu2,
                        fuel := fuel2, confl_type := ctype2, confl_ref := cref2,
                        confl_lit0 := c0_2, confl_lit1 := c1_2, oom := oom2, heur := heur2 }
                    c0_unmdata; pr_steps!
                    · exact reduce_ret hQ hsame_w (s1 := s_p3) hinv_p.lengths (Or.inr (Or.inr rfl))
                        (Nat.le_trans hfuel_p hfuel_w) hinv_p.trail_lits_lt
                        (fun _ => level0_confl_unsat hinv_p hcl0_sw (hpr1 (by assumption)).2.2)
                        (fun h => by cases h) (fun h => by cases h) hm_p
                    · exact reduce_ret hQ hsame_w (s1 := s_p3) hinv_p.lengths (Or.inl rfl)
                        (Nat.le_trans hfuel_p hfuel_w) hinv_p.trail_lits_lt
                        (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm_p
                    · have hpr0' : pr = 0#64 := by
                        rcases hpr_r with rfl | rfl | rfl <;> first | rfl | contradiction
                      let s_fin : PlainState :=
                        { s_sw with
                          vals := vals2, lvl := lvl2, rsns := rsns2, trl := trl2, trail_pos := tp2,
                          trail_end := te2, propagated := prop2, unflushed := 0#64, wvec := wvec2,
                          arena := arena2, wstk := wstk2, wlen := wlen2, wusable := wu2,
                          fuel := fuel2, confl_type := ctype2, confl_ref := cref2,
                          confl_lit0 := c0_2, confl_lit1 := c1_2, oom := oom2, heur := heur2 }
                      have hinv_fin : PlainCoreInv c F0 s_fin := pr_with_unflushed hinv_p 0#64
                      have hm_lt : meas m < meas m_w := by
                        rw [hmeas hinv_fin hm, hmeas hinv_w hm_w]
                        have hle1 := hinv_w.lengths.trail_end_le
                        have hle2 := hinv_p.lengths.trail_end_le
                        dsimp only [s_fin, s_sw] at hte_p hle2 ⊢; omega
                      exact hJ_w () _ hm_lt ⟨s_fin, ⟨hinv_fin, hsame_w,
                        Nat.le_trans hfuel_p hfuel_w, by simp [s_fin, s_sw, hcl0_sw],
                        fun _ => (hpr0 hpr0').2 (by simp [s_sw]; exact (hok_sw (Or.inr hsr1)).2),
                        fun hp => by simp [s_fin, s_sw, hcl0_sw] at hp⟩,
                        fun hp => by simp [s_fin, s_sw, hcl0_sw] at hp, hm⟩
            · intro J4 hJ4; pr_jnz
              · exact hJ4 () m4 ⟨s4, ⟨hinv4, hsame4, hfuel4, hcl4, hoom4, hkeep4⟩, hrm4, hm4⟩
              · refine wp_join_group (ts := [])
                  (fun _ m_mr => ∃ sm, RdPreOk c F0 s0 sm ∧ (PlainMem c sm ⋆ R) m_mr) ?_ ?_
                · rintro _ ⟨⟩ m_mr ⟨sm, hprem, hmm⟩
                  refine wp_call_of_spec _ _ (hMR (c.hdr, false, ()) m_mr _ X ⟨c, F0, sm, R, rfl,
                    hprem.1, hmm, fun ar5 m5 _ _ _ hinv5 hm5 => ?_⟩)
                  c0_unmdata; pr_steps!
                  exact hJ_ret1 () m5 ⟨{ sm with arena := ar5 }, ⟨hinv5, hprem.2⟩, hm5⟩
                · intro J5 hJ5; c0_unmdata; pr_steps! <;>
                    first
                    | exact hJ4 () m4 ⟨s4, ⟨hinv4, hsame4, hfuel4, hcl4, hoom4, hkeep4⟩, hrm4, hm4⟩
                    | exact hJ5 () m4 ⟨s4, ⟨hinv4, hsame4, hfuel4, hcl4, hoom4, hkeep4⟩, hm4⟩
        · intro J_sw hJsw; c0_unmdata; pr_steps!
          · refine wp_call_of_spec _ _
              (hSR (c.hdr, rc, ()) m1 _ X ⟨c, s3a, R, rfl, hinv3a.lengths, hrc,
                fun k hk => by simpa [s3a, mkL1] using (hrr_a k hk).2.1, hm1,
                fun heur_sr m_sr hok_sr hrt_sr hperm hm_sr => ?_⟩)
            have hrr_b' : ∀ k < rc.toNat, let cr := (heur_sr.red_refs[k]?.getD 0#32).toNat;
                cr ∈ arenaClauseRefs { s3a with heur := heur_sr } ∧ cr + 2 < c.arena_cap ∧
                (s3a.arena[cr]?.getD 0#32 &&& 0x00200000#32) = 0#32 := fun k hk => by
              obtain ⟨j, hj, heq⟩ := hperm k hk
              change let cr := (heur_sr.red_refs[k]?.getD 0#32).toNat; _
              rw [heq]; exact hrr_a j hj
            have hs3b_ex : ∃ s3b : PlainState, RdPreOk c F0 s0 s3b ∧
                ReasonsMarked s3b ∧
                (∀ k < rc.toNat, let cr := (s3b.heur.red_refs[k]?.getD 0#32).toNat;
                  cr ∈ arenaClauseRefs s3b ∧ cr + 2 < c.arena_cap ∧
                  (s3b.arena[cr]?.getD 0#32 &&& 0x00200000#32) = 0#32) ∧
                (PlainMem c s3b ⋆ R) m_sr :=
              ⟨{ s3a with heur := heur_sr }, ⟨hinv3a.with_heur hok_sr, hsame3, hfuel3, hcl3, hoom3,
                hkeep3⟩, hrm3a', hrr_b', hm_sr⟩
            obtain ⟨s3b, ⟨hinv3b, hsame3b, hfuel3b, hcl3b, hoom3b, hkeep3b⟩,
              hrm3b, hrr_b, hm_sr⟩ := hs3b_ex
            clear_except [Γ hIL Q X c F0 s0 R hQ s3b hinv3b hsame3b hfuel3b hcl3b hoom3b
              hkeep3b hrm3b hrr_b hm_sr hJsw rc hrc hred]
            c0_unmdata; pr_steps!
            refine wp_call_of_spec _ _ (hIL (s3b.heur.reductions + 9#64, ()) m_sr _ X
              fun logv hlog1 _ => ?_)
            obtain ⟨hlog_ne, hpct⟩ := reducePct_le hlog1
            have htrg := reduceTarget_le (rc := rc) (by omega) hpct
            c0_unmdata; pr_steps!
            refine wp_loop_inv (ts := [i64])
              (fun v m2 => ∃ ar'' : List (BitVec 32), ∃ ag' : BitVec 64,
                v.1.toNat ≤ rc.toNat ∧ GarbMaskOk s3b ar'' ∧
                (PlainMem c { s3b with arena := ar'', arena_garbage := ag' } ⋆ R) m2)
              (fun v _ => rc.toNat - v.1.toNat) ?_ ?_
            · intro J_l2 hJl2; c0_unmdata; pr_steps!
              exact hJl2 (0#64, ()) m_sr ⟨s3b.arena, s3b.arena_garbage, Nat.zero_le _,
                garbMask_refl s3b, hm_sr⟩
            · rintro J_l2 ⟨i, ⟨⟩⟩ m2 ⟨ar'', ag', hi_le, hg, hm2⟩ hJl2
              dsimp only at hi_le hJl2
              have har''_len : ar''.length = c.arena_cap := hg.1.trans hinv3b.lengths.arena_len_arr
              pr_jnz
              · pr_jnz
                · have hi_lt : i.toNat < rc.toNat := by bv_omega
                  have hi1 : (i + 1).toNat = i.toNat + 1 := by bv_omega
                  have hi_rr : i.toNat < s3b.heur.red_refs.length := by
                    rw [hinv3b.lengths.heur_ok.red_refs_len]; omega
                  have hrr_len_s : i.toNat <
                      ({ s3b with arena := ar'', arena_garbage := ag' } :
                        PlainState).heur.red_refs.length :=
                    hi_rr
                  obtain ⟨hcr_ref, hcr_bd, hcr_nrsn⟩ := hrr_b i.toNat hi_lt
                  rw [List.getElem?_eq_getElem hi_rr, Option.getD_some] at hcr_ref hcr_bd hcr_nrsn
                  have hcr_len_cr : (s3b.heur.red_refs[i.toNat]'hi_rr).toNat < ar''.length := by
                    omega
                  have hcr_len :
                      (({ s3b with arena := ar'', arena_garbage := ag' } :
                        PlainState).heur.red_refs[i.toNat]'hrr_len_s).toNat < ar''.length :=
                    hcr_len_cr
                  have hcr_bd2 :
                      (({ s3b with arena := ar'', arena_garbage := ag' } :
                        PlainState).heur.red_refs[i.toNat]'hrr_len_s).toNat + 2 < ar''.length := by
                    change (s3b.heur.red_refs[i.toNat]'hi_rr).toNat + 2 < ar''.length; omega
                  have hm_rsn :
                      (ar''[(s3b.heur.red_refs[i.toNat]'hi_rr).toNat] &&&
                        0x00200000#32) = 0#32 := by
                    have hm21 := bv32_mask_sub_eq (sub := 0x00200000#32) (by decide)
                      (hg.2.2.1 _ hcr_ref)
                    rw [List.getElem?_eq_getElem hcr_len_cr, Option.getD_some] at hm21
                    exact hm21.trans hcr_nrsn
                  dsimp only [LeanQbe.T.lift2]; c0_unmdata; c0_step; c0_step
                  refine wp_join_group (ts := [])
                    (fun _ mj4 => ∃ ar''' : List (BitVec 32), ∃ ag'' : BitVec 64,
                      GarbMaskOk s3b ar''' ∧
                      (PlainMem c { s3b with arena := ar''', arena_garbage := ag'' } ⋆ R) mj4) ?_ ?_
                  · rintro _ ⟨⟩ mj4 ⟨ar''', ag'', hg''', hmj4⟩
                    c0_unmdata; pr_steps!
                    exact hJl2 (i + 1, ()) mj4 (by dsimp only; omega)
                      ⟨ar''', ag'', (by dsimp only; omega), hg''', hmj4⟩
                  · intro J_g hJg; pr_jnz
                    · have hg' := garbMask_set hg hcr_ref hcr_len_cr hm_rsn
                      pr_let
                      have hcr_len64 :
                          ((s3b.heur.red_refs[i.toNat]'hi_rr).setWidth 64).toNat < ar''.length := by
                        rw [bv_c0_zext32_64]; exact hcr_len_cr
                      refine wp_store_sep (c0_store_arena_arena
                        (s := { s3b with arena := ar'', arena_garbage := ag' })
                        (i := (s3b.heur.red_refs[i.toNat]'hi_rr).setWidth 64) _ hcr_len64 hm2) ?_
                      intro _ hm_s1
                      have hm_s1' : (PlainMem c { s3b with
                          arena := ar''.set ((s3b.heur.red_refs[i.toNat]'hi_rr).setWidth 64).toNat
                            (ar''[(s3b.heur.red_refs[i.toNat]'hi_rr).toNat] ||| 0x00080000#32),
                          arena_garbage := ag' } ⋆ R) _ := hm_s1
                      pr_let
                      refine wp_load_of (load_arena_garbage hm_s1') ?_
                      pr_let
                      have hcr2_len :
                          ((s3b.heur.red_refs[i.toNat]'hi_rr).setWidth 64 + 2#64).toNat <
                            (ar''.set ((s3b.heur.red_refs[i.toNat]'hi_rr).setWidth 64).toNat
                              (ar''[(s3b.heur.red_refs[i.toNat]'hi_rr).toNat] |||
                                0x00080000#32)).length := by
                        rw [List.length_set]; have := hcr_bd; have := har''_len; bv_omega
                      refine wp_load_of (c0_load_arena_arena
                        (i := (s3b.heur.red_refs[i.toNat]'hi_rr).setWidth 64 + 2#64)
                        hcr2_len hm_s1') ?_
                      pr_let
                      refine wp_store_sep (store_arena_garbage _ hm_s1') fun _ hm_s2 => ?_
                      pr_let
                      refine hJg () _ ⟨_, _, ?_, hm_s2⟩
                      simpa only [bv_c0_zext32_64] using hg'
                    · c0_unmdata; pr_steps!
                      exact hJg () m2 ⟨ar'', ag', hg, hm2⟩
                · c0_unmdata; pr_steps!
                  have hinv3b' := pr_with_ag hinv3b ag'
                  obtain ⟨hinv4, hrm4⟩ := garbMask_core hinv3b' (fun _ => hrm3b) hg
                  have hinv4' :
                      PlainCoreInv c F0 { s3b with arena := ar'', arena_garbage := ag' } := hinv4
                  exact hJsw () m2 ⟨{ s3b with arena := ar'', arena_garbage := ag' },
                    ⟨hinv4', hsame3b, hfuel3b, hcl3b, hoom3b, hkeep3b⟩, hrm4, hm2⟩
              · c0_unmdata; pr_steps!
                have hinv3b' := pr_with_ag hinv3b ag'
                obtain ⟨hinv4, hrm4⟩ := garbMask_core hinv3b' (fun _ => hrm3b) hg
                have hinv4' :
                    PlainCoreInv c F0 { s3b with arena := ar'', arena_garbage := ag' } := hinv4
                exact hJsw () m2 ⟨{ s3b with arena := ar'', arena_garbage := ag' },
                  ⟨hinv4', hsame3b, hfuel3b, hcl3b, hoom3b, hkeep3b⟩, hrm4, hm2⟩
          · exact hJsw () m1 ⟨s3a, ⟨hinv3a, hsame3, hfuel3, hcl3, hoom3, hkeep3⟩,
              fun _ => hrm3a', hm1⟩
  · intro J_fl hJ_fl
    c0_unmdata; c0_step; c0_step; c0_step
    · refine wp_join_group (ts := [])
        (fun _ m_b => ∃ s_b : PlainState, RdPreOk c F0 s0 s_b ∧
          s_b.cur_level = 0 ∧ (PlainMem c s_b ⋆ R) m_b) ?_ ?_
      · rintro _ ⟨⟩ m_b ⟨s_b, ⟨hinv_b, hsame_b, hfuel_b, hcl_b, hoom_b, hkeep_b⟩, hcl0_b, hm_b⟩
        c0_unmdata; pr_steps!
        refine wp_call_of_spec _ _ (hPR (c.hdr, ()) m_b _ X ⟨c, F0, s_b, R, rfl, hinv_b, hm_b,
          fun pr vals' lvl' rsns' trl' tp' te' prop' unfl' wvec' arena' wstk' wlen' wu' fuel'
            ctype' cref' c0' c1' oom' heur' m_p hinv_p hte_p hfuel_p hrt_p htrl_p hlvl_p hlvl_hi
            hpr_r hpr0 hpr1 _ _ hm_p => ?_⟩)
        let s_p : PlainState :=
          { s_b with
            vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
            trail_end := te', propagated := prop', unflushed := unfl', wvec := wvec',
            arena := arena', wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
            confl_type := ctype', confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
            oom := oom', heur := heur' }
        c0_unmdata; pr_steps!
        · exact reduce_ret hQ hsame_b (s1 := s_p) hinv_p.lengths (Or.inr (Or.inr rfl))
            (Nat.le_trans hfuel_p hfuel_b) hinv_p.trail_lits_lt
            (fun _ => level0_confl_unsat hinv_p hcl0_b (hpr1 (by assumption)).2.2)
            (fun h => by cases h) (fun h => by cases h) hm_p
        · exact reduce_ret hQ hsame_b (s1 := s_p) hinv_p.lengths (Or.inl rfl)
            (Nat.le_trans hfuel_p hfuel_b) hinv_p.trail_lits_lt
            (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm_p
        · have hpr0' : pr = 0#64 := by
            rcases hpr_r with rfl | rfl | rfl <;> first | rfl | contradiction
          have hoom_p : s0.oom = 0#64 → oom' = 0#64 := fun ho => (hpr0 hpr0').2 (hoom_b ho)
          exact hJ_fl () _ ⟨_,
            ⟨pr_with_unflushed hinv_p 0#64, hsame_b, Nat.le_trans hfuel_p hfuel_b,
            hcl_b, hoom_p, fun hp => by simp [hcl0_b] at hp⟩, by assumption⟩
      · intro J_bt hJ_bt; c0_unmdata; pr_steps!
        · refine wp_call_of_spec _ _ (hBT (c.hdr, 0#64, ()) m _ X ⟨c, s_pre, R, rfl,
            hinv_pre.lengths, hinv_pre.trail_lits_lt, by assumption,
            fun vals' lvl' rsns' te' prop' heur' m_b hlen_b hte_b hprop_b hrt_b htrl_b hcore_b
              hm_b => ?_⟩)
          have ⟨hinv_b, _⟩ := hcore_b F0 hinv_pre (Nat.zero_le _)
          exact hJ_bt () m_b ⟨_, ⟨hinv_b, hsame_pre, Nat.le_refl _, Nat.zero_le _, fun h => h,
            fun h => absurd h (Nat.lt_irrefl 0)⟩, rfl, hm_b⟩
        · have hcl0 : s_pre.cur_level = 0 := by change s0.cur_level = 0; bv_omega
          exact hJ_bt () m ⟨s_pre, ⟨hinv_pre, hsame_pre, Nat.le_refl _, Nat.le_refl _, fun h => h,
            fun hp => by simp [hcl0] at hp⟩, hcl0, by assumption⟩
    · pr_steps!
      exact hJ_fl () m ⟨s_pre, ⟨hinv_pre, hsame_pre, Nat.le_refl _, Nat.le_refl _, fun h => h,
        fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩, by assumption⟩

end

end LeanQbe.T.Examples.Kissat.Plain
