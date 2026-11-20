module

public import LeanQbe.T.Examples.Kissat.FullPropDecLemmas2
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Chronological BCP Branch Helpers (`Stage 4`, Part 3)

Factored branch helpers for `full_prop_lit_wp`:
- `propLit_finish` (post-loop watch slice compaction + `FullWitnessInv` restoration)
- `propLit_b1_swap` (replacement literal swap + `FullArenaPermEq`)
- `propLit_b1_after_push` (watch-stack relocation after `full_watch_push`)
- `propLit_b1_oom` (OOM revert swap + watch keep + `oom = 1`)
- `propLit_js3_swap` (`l0 == not_lit` swap into `ar[cref + 4]`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
  LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test
open scoped FullArenaTactics FullPropDecTactics
open FullPropDecSpecs

theorem propLit_finish {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {ignore_ref : BitVec 64} {not_lit : BitVec 32}
    {off_v p_v q_v end_v q_c : BitVec 64} {confl_v : Bool}
    {wstk_c wstk_k : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {idx1 : Nat}
    (hpi : PropLitInv c F0 F_cur s st not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat)
    (hdense : s.core.dense_mode = 0#64)
    (hnot_lt : not_lit.toNat < 2 * st.core.cur_vars) (hwl3 : wstk_k.length = c.wcap)
    (hpc_eq : q_c.toNat = q_v.toNat + (end_v.toNat - p_v.toNat))
    (hidx1 : idx1 = 2 * not_lit.toNat + 1)
    (hpre : ∀ k, off_v.toNat ≤ k → k < q_v.toNat → wstk_c[k]? = st.core.wstk[k]?)
    (hsuf : ∀ k < end_v.toNat - p_v.toNat, wstk_c[q_v.toNat + k]? = st.core.wstk[p_v.toNat + k]?)
    (hout : ∀ k, (k < off_v.toNat ∨ end_v.toNat ≤ k) → wstk_c[k]? = st.core.wstk[k]?)
    (hkeep : ∀ i, (i < q_v.toNat + (end_v.toNat - p_v.toNat) ∨ end_v.toNat ≤ i) →
      wstk_k[i]? = wstk_c[i]?)
    (hcf_f : confl_v = false → st.core.oom = 0#64)
    (hcf_t : confl_v = true → PropLitConfl F_cur ignore_ref st.core)
    (hm : (FullMem c { st with core := { st.core with
        wstk := wstk_k, wvec := st.core.wvec.set idx1 ((q_c - off_v).setWidth 32),
        wusable := st.core.wusable + (end_v - q_c) } } ⋆ R) m) :
    let st_fin : FullState :=
      { st with core :=
        { st.core with
          wstk := wstk_k, wusable := st.core.wusable + (end_v - q_c),
          wvec := st.core.wvec.set (2 * not_lit.toNat + 1)
            (BitVec.ofNat 32 (q_v.toNat + (end_v.toNat - p_v.toNat) - off_v.toNat)) } }
    st_fin.LengthsOk c ∧ FullWitnessInv c F0 F_cur st_fin.core ∧
    AgreesExcept propLitCoreMask s.core st_fin.core ∧
    FullTrailExt s.core st_fin.core ∧ FullArenaPermEq s.core st_fin.core ∧
    st_fin.scratch = { s.scratch with
      search_ticks := st_fin.scratch.search_ticks, wsort := st_fin.scratch.wsort,
      phases := st_fin.scratch.phases } ∧
    ((!confl_v) = false → PropLitConfl F_cur ignore_ref st_fin.core) ∧
    ((!confl_v) = true → st_fin.core.oom = 0#64) ∧
    (FullMem c st_fin ⋆ R) m := by
  intro st_fin
  have hq_ge := hpi.sw.q_ge; have hq_le := hpi.sw.q_le_p; have hp_le := hpi.sw.p_le_end
  have ⟨_, hwlen_le⟩ := hpi.end_lt_wcap hnot_lt
  have hwvec_len := hpi.len.core_ok.wvec_len; have hcv := hpi.len.core_ok.cur_vars_le
  have hset_wvec : (q_c - off_v).setWidth 32 =
      BitVec.ofNat 32 (q_v.toNat + (end_v.toNat - p_v.toNat) - off_v.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, bv64_sub_toNat (by omega), hpc_eq, BitVec.toNat_ofNat]
  have hwat_fin := hpi.sw.finish (c := c) hnot_lt hcv hwvec_len hwlen_le
    (fun k h1 h2 => (hkeep k (Or.inl (by omega))).trans (hpre k h1 h2))
    (fun k hk => (hkeep _ (Or.inl (by omega))).trans (hsuf k hk))
    (fun k hk => (hkeep k (hk.elim (fun _ => Or.inl (by omega)) Or.inr)).trans (hout k hk))
    (wu' := st.core.wusable + (end_v - q_c))
  have hlen_fin : st_fin.LengthsOk c :=
    ⟨{ hpi.len.core_ok with wvec_len := by simp [st_fin, hwvec_len], wstk_len_arr := hwl3 },
     hpi.len.scratch_ok⟩
  have hnw_fin := fullWitnessInv_nw_congr hlen_fin.core_ok.cur_vars_le hpi.nw
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hdm_fin : st_fin.core.dense_mode = 0#64 := by
    change st.core.dense_mode = 0#64; rw [hpi.dense_eq, hdense]
  refine ⟨hlen_fin, fullWitnessInv_of_nw hnw_fin hdm_fin hwat_fin,
    hpi.ag.update (fun k => { k with
      wstk := wstk_k, wvec := st_fin.core.wvec, wusable := st_fin.core.wusable }),
    hpi.tr.congr rfl rfl rfl, hpi.perm, hpi.sc_eq,
    fun hnf => (hcf_t (by cases confl_v <;> simp at hnf ⊢)).congr
      rfl rfl rfl rfl rfl rfl rfl rfl rfl,
    fun hnt => hcf_f (by cases confl_v <;> simp at hnt ⊢), ?_⟩
  subst hidx1; dsimp only [st_fin]; rw [← hset_wvec]; exact hm

theorem propLit_b1_swap {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st1 : FullState} {not_lit other cref repl : BitVec 32} {off_v p_v q_v end_v : BitVec 64}
    {r i4 ir : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hpi1 : PropLitInv c F0 F_cur s st1 not_lit.toNat off_v.toNat q_v.toNat (p_v.toNat + 2)
      end_v.toNat)
    (hcr_lt : cref.toNat < st1.core.arena_len)
    (hcr_ref1 : cref.toNat ∈ fullArenaClauseRefsCore st1.core)
    (hcr_fit : cref.toNat + 3 + fullArenaClauseSizeCore st1.core cref.toNat ≤ st1.core.arena_len)
    (har4 : st1.core.arena[cref.toNat + 4]? = some not_lit)
    (hr2 : 2 ≤ r) (hr_lt : r < fullArenaClauseSizeCore st1.core cref.toNat)
    (hi4 : i4 = cref.toNat + 4) (hir : ir = cref.toNat + 3 + r)
    (hrepl_def : repl = (st1.core.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r))[ir]'(by
      have := hpi1.len.core_ok.arena_len_arr; have := hpi1.len.core_ok.arena_len_le; simp; omega))
    (hcand : (st1.core.arena[cref.toNat + 3 + r]?.getD 0#32).toNat < 2 * st1.core.cur_vars ∧
      ((st1.core.vals[(st1.core.arena[cref.toNat + 3 + r]?.getD 0#32).toNat]?.getD 0#8).signExtend
        32).slt 0#32 = false)
    (hm : (FullMem c { st1 with core := { st1.core with
        arena := (((st1.core.arena.set (cref.toNat + 1)
          (BitVec.ofNat 32 r)).set i4 repl).set ir not_lit) } } ⋆ R) m) :
    let st3 : FullState := { st1 with core := { st1.core with
      arena := ((st1.core.arena.set (cref.toNat + 1)
        (BitVec.ofNat 32 r)).set (cref.toNat + 4) repl).set (cref.toNat + 3 + r) not_lit } }
    st3.LengthsOk c ∧ FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st3.core) ∧
    SplitWatchesInv F_cur st3.core not_lit.toNat off_v.toNat q_v.toNat (p_v.toNat + 2)
      end_v.toNat ∧
    FullArenaPermEq st1.core st3.core ∧
    cref.toNat ∈ fullArenaClauseRefsCore st3.core ∧
    fullArenaClauseSizeCore st3.core cref.toNat = fullArenaClauseSizeCore st1.core cref.toNat ∧
    repl.toNat < 2 * st1.core.cur_vars ∧ repl.toNat ≠ not_lit.toNat ∧
    (other &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 ∧ cref ≠ 0xFFFFFFFF#32 ∧
    (FullMem c st3 ⋆ R) m := by
  intro st3; subst hi4; subst hir
  let st2 : FullState := { st1 with core := { st1.core with
    arena := st1.core.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r) } }
  have har := c.harena; unfold dimacsBound at har
  have haren1 := hpi1.len.core_ok.arena_len_arr; have halen1_le := hpi1.len.core_ok.arena_len_le
  have ⟨hnw2, hperm12⟩ :=
    full_setSrch_preserves_nw hpi1.len.core_ok hpi1.nw hcr_ref1 (srch := BitVec.ofNat 32 r)
  have hlen2 : st2.LengthsOk c :=
    ⟨{ hpi1.len.core_ok with arena_len_arr := by simp [st2, haren1] }, hpi1.len.scratch_ok⟩
  have hsw2 := hpi1.sw.with_nonwatch (k' := st2.core) rfl rfl rfl rfl hperm12.1
  have hcr_ref2 : cref.toNat ∈ fullArenaClauseRefsCore st2.core := hperm12.1.symm ▸ hcr_ref1
  have hcsz2 : fullArenaClauseSizeCore st2.core cref.toNat =
      fullArenaClauseSizeCore st1.core cref.toNat := (hperm12.2 cref.toNat hcr_ref1).1
  have hrepl_get : st1.core.arena[cref.toNat + 3 + r]?.getD 0#32 = repl := by
    have h1 : st2.core.arena[cref.toNat + 3 + r]? = some repl := by
      rw [hrepl_def]; exact List.getElem?_eq_getElem (by simp [st2]; omega)
    rw [← List.getElem?_set_ne (by omega : cref.toNat + 1 ≠ cref.toNat + 3 + r),
      show (st1.core.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r))[cref.toNat + 3 + r]? =
        some repl from h1, Option.getD_some]
  obtain ⟨hrepl_lt, hrepl_slt⟩ := hcand; rw [hrepl_get] at hrepl_lt hrepl_slt
  have hrepl_ne_not : repl.toNat ≠ not_lit.toNat := fun heq =>
    i8_vals_ne_of_slt_false hpi1.not_f (heq ▸ hrepl_slt) rfl
  have hst2_ar4 : st2.core.arena[cref.toNat + 3 + 1]'(by simp [st2]; omega) = not_lit :=
    Option.some.inj ((List.getElem?_eq_getElem (by simp [st2]; omega)).symm.trans
      ((List.getElem?_set_ne (by omega)).trans har4))
  have ⟨hnw3, hperm23⟩ := full_swapLits_preserves_nw hlen2.core_ok hnw2 hcr_ref2 (k1 := 1) (k2 := r)
    (by change 1 < fullArenaClauseSizeCore st2.core cref.toNat; omega)
    (by change r < fullArenaClauseSizeCore st2.core cref.toNat; omega)
  have hst3_sw : st3.core = { st2.core with
    arena := (st2.core.arena.set (cref.toNat + 3 + 1)
        (st2.core.arena[cref.toNat + 3 + r]'(by simp [st2]; omega))).set
      (cref.toNat + 3 + r) (st2.core.arena[cref.toNat + 3 + 1]'(by simp [st2]; omega)) } := by
    simp only [st3, st2, hst2_ar4, ← hrepl_def]
  rw [← hst3_sw] at hnw3 hperm23
  have hw0_ne_ff : (other &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 := fun hff => by
    have h := bv32_mask7f_flag0 other; rw [hff] at h; exact absurd h (by decide)
  have hcr_ne_ff : cref ≠ 0xFFFFFFFF#32 := fun hff => by
    rw [hff] at hcr_lt; have : (0xFFFFFFFF#32).toNat = 0xFFFFFFFF := (by decide); omega
  exact ⟨⟨{ hlen2.core_ok with arena_len_arr := by simp [st3, haren1] }, hpi1.len.scratch_ok⟩,
    hnw3, hsw2.with_nonwatch (k' := st3.core) rfl rfl rfl rfl hperm23.1,
    hperm12.trans hperm23, hperm23.1.symm ▸ hcr_ref2,
    (hperm23.2 cref.toNat hcr_ref2).1.trans hcsz2, hrepl_lt, hrepl_ne_not, hw0_ne_ff, hcr_ne_ff, hm⟩

theorem propLit_b1_after_push {c : FullCfg} {F_cur : List (List Nat)}
    {st3 st4 : FullState} {lit other cref repl : BitVec 32} {off_v p_v q_v end_v : BitVec 64}
    {pok : Bool} {idx0 : Nat}
    (hidx0 : idx0 = 2 * (lit ^^^ 1#32).toNat)
    (hvars : st4.core.cur_vars = st3.core.cur_vars)
    (hnot_lt : (lit ^^^ 1#32).toNat < 2 * st3.core.cur_vars)
    (hlen4 : st4.LengthsOk c) (hlay4 : WatchStackLayout st4.core)
    (hsw3 : SplitWatchesInv F_cur st3.core (lit ^^^ 1#32).toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hrefs : fullArenaClauseRefsCore st4.core = fullArenaClauseRefsCore st3.core)
    (hrepl_lt : repl.toNat < 2 * st3.core.cur_vars) (hrepl_ne : repl.toNat ≠ (lit ^^^ 1#32).toNat)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref3 : cref.toNat ∈ fullArenaClauseRefsCore st3.core)
    (hp2_nat : (p_v + (1 : BitVec 64) + (1 : BitVec 64)).toNat = p_v.toNat + 2)
    (hq_le_p : q_v.toNat ≤ p_v.toNat)
    (hpres_o : ∀ l < 2 * st3.core.cur_vars, l ≠ repl.toNat →
      fullWatchSizeCore st4.core l = fullWatchSizeCore st3.core l ∧
      ∀ k < fullWatchSizeCore st3.core l,
        st4.core.wstk[fullWatchOffCore st4.core l + k]? =
          st3.core.wstk[fullWatchOffCore st3.core l + k]?)
    (hpok_t : pok = true →
      fullWatchSizeCore st4.core repl.toNat = fullWatchSizeCore st3.core repl.toNat + 2 ∧
      (∀ k < fullWatchSizeCore st3.core repl.toNat,
        st4.core.wstk[fullWatchOffCore st4.core repl.toNat + k]? =
          st3.core.wstk[fullWatchOffCore st3.core repl.toNat + k]?) ∧
      st4.core.wstk[fullWatchOffCore st4.core repl.toNat +
        fullWatchSizeCore st3.core repl.toNat]? = some (other &&& 0x7FFFFFFF#32) ∧
      st4.core.wstk[fullWatchOffCore st4.core repl.toNat +
        fullWatchSizeCore st3.core repl.toNat + 1]? = some cref)
    (hpok_f : pok = false →
      fullWatchSizeCore st4.core repl.toNat = fullWatchSizeCore st3.core repl.toNat ∧
      ∀ k < fullWatchSizeCore st3.core repl.toNat,
        st4.core.wstk[fullWatchOffCore st4.core repl.toNat + k]? =
          st3.core.wstk[fullWatchOffCore st3.core repl.toNat + k]?) :
    let off4_v : BitVec 64 :=
      (st4.core.wvec[idx0]'(by
        have := hlen4.core_ok.wvec_len; have := hlen4.core_ok.cur_vars_le; omega)).setWidth 64
    let q4_v := off4_v + (q_v - off_v)
    fullWatchOffCore st4.core (lit ^^^ 1#32).toNat + (end_v.toNat - off_v.toNat) ≤ st4.core.wlen ∧
    off4_v.toNat = fullWatchOffCore st4.core (lit ^^^ 1#32).toNat ∧
    (off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v)).toNat =
      fullWatchOffCore st4.core (lit ^^^ 1#32).toNat + (p_v.toNat + 2 - off_v.toNat) ∧
    q4_v.toNat = fullWatchOffCore st4.core (lit ^^^ 1#32).toNat + (q_v.toNat - off_v.toNat) ∧
    (off4_v + (end_v - off_v)).toNat =
      fullWatchOffCore st4.core (lit ^^^ 1#32).toNat + (end_v.toNat - off_v.toNat) ∧
    (q4_v + (1 : BitVec 64)).toNat = q4_v.toNat + 1 ∧
    (q4_v + (2 : BitVec 64)).toNat = q4_v.toNat + 2 ∧
    SplitWatchesInv F_cur st4.core (lit ^^^ 1#32).toNat off4_v.toNat q4_v.toNat
      (off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v)).toNat
      (off4_v + (end_v - off_v)).toNat := by
  intro off4_v q4_v
  have hwc := c.hwcap; unfold dimacsBound at hwc
  have hwlen4 := hlen4.core_ok.wlen_le; have hwvec4 := hlen4.core_ok.wvec_len
  have hcv4 := hlen4.core_ok.cur_vars_le
  have hq_ge := hsw3.q_ge; have hp_le := hsw3.p_le_end
  have hsw4 := hsw3.after_push (k' := st4.core) hvars hnot_lt hrepl_lt hrepl_ne hrefs hlay4
    (bv32_mask7f_flag0 other) hcr_lt hcr_ref3 hpres_o hpok_t hpok_f
  have hoff4_bd : fullWatchOffCore st4.core (lit ^^^ 1#32).toNat +
      (end_v.toNat - off_v.toNat) ≤ st4.core.wlen := by
    have hb := hlay4.bounds (lit ^^^ 1#32).toNat (hvars.symm ▸ hnot_lt)
    have hsz4 := hsw4.sz_eq
    have hsz_e : fullWatchSizeCore st4.core (lit ^^^ 1#32).toNat = end_v.toNat - off_v.toNat := by
      omega
    rw [hsz_e] at hb; exact hb
  have hoff4_nat : off4_v.toNat = fullWatchOffCore st4.core (lit ^^^ 1#32).toNat := by
    dsimp only [off4_v]; rw [bv_c0_zext32_64]; unfold fullWatchOffCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact congrArg BitVec.toNat (by congr 1)
  have hp4_nat : (off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v)).toNat =
      fullWatchOffCore st4.core (lit ^^^ 1#32).toNat + (p_v.toNat + 2 - off_v.toNat) := by
    rw [bv64_add_toNat (by rw [bv64_sub_toNat (by omega), hp2_nat]; omega),
      hoff4_nat, bv64_sub_toNat (by omega), hp2_nat]
  have hq4_nat : q4_v.toNat =
      fullWatchOffCore st4.core (lit ^^^ 1#32).toNat + (q_v.toNat - off_v.toNat) := by
    dsimp only [q4_v]
    rw [bv64_add_toNat (by rw [bv64_sub_toNat (by omega)]; omega),
      hoff4_nat, bv64_sub_toNat (by omega)]
  have hend4_nat : (off4_v + (end_v - off_v)).toNat =
      fullWatchOffCore st4.core (lit ^^^ 1#32).toNat + (end_v.toNat - off_v.toNat) := by
    rw [bv64_add_toNat (by rw [bv64_sub_toNat (by omega)]; omega),
      hoff4_nat, bv64_sub_toNat (by omega)]
  exact ⟨hoff4_bd, hoff4_nat, hp4_nat, hq4_nat, hend4_nat,
    bv64_add1_toNat (by omega), bv64_add2_toNat (by omega),
    by rw [hoff4_nat, hq4_nat, hp4_nat, hend4_nat]; exact hsw4⟩

theorem propLit_b1_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st1 st4 : FullState} {not_lit w0 cref repl : BitVec 32}
    {off_v p_v q_v end_v off4_v : BitVec 64} {r i4 ir q4_1 : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hpi1 : PropLitInv c F0 F_cur s st1 not_lit.toNat off_v.toNat q_v.toNat (p_v.toNat + 2)
      end_v.toNat)
    (hlen4 : st4.LengthsOk c) (hnw4 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st4.core))
    (hsw4' : SplitWatchesInv F_cur st4.core not_lit.toNat off4_v.toNat
      (off4_v + (q_v - off_v)).toNat
      (off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v)).toNat
      (off4_v + (end_v - off_v)).toNat)
    (hperm4 : FullArenaPermEq s.core st4.core)
    (har_eq : st4.core.arena = ((st1.core.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r)).set
      (cref.toNat + 4) repl).set (cref.toNat + 3 + r) not_lit)
    (hal_eq : st4.core.arena_len = st1.core.arena_len)
    (hag4 : AgreesExcept propLitCoreMask s.core st4.core) (htr4 : FullTrailExt s.core st4.core)
    (hsc4 : st4.scratch = { s.scratch with
      search_ticks := st4.scratch.search_ticks, wsort := st4.scratch.wsort,
      phases := st4.scratch.phases })
    (hnot4 : st4.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hnot_lt : not_lit.toNat < 2 * st4.core.cur_vars) (hq_le_p : q_v.toNat ≤ p_v.toNat)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref3 : cref.toNat ∈ fullArenaClauseRefsCore st4.core)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hcr_fit : cref.toNat + 3 + fullArenaClauseSizeCore st4.core cref.toNat ≤ st1.core.arena_len)
    (hr2 : 2 ≤ r) (hr_lt : r < fullArenaClauseSizeCore st4.core cref.toNat)
    (hi4 : i4 = cref.toNat + 4) (hir : ir = cref.toNat + 3 + r)
    (hq4_nat : (off4_v + (q_v - off_v)).toNat =
      fullWatchOffCore st4.core not_lit.toNat + (q_v.toNat - off_v.toNat))
    (hp4_nat : (off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v)).toNat =
      fullWatchOffCore st4.core not_lit.toNat + (p_v.toNat + 2 - off_v.toNat))
    (hend4_nat : (off4_v + (end_v - off_v)).toNat =
      fullWatchOffCore st4.core not_lit.toNat + (end_v.toNat - off_v.toNat))
    (hq4_1 : q4_1 = (off4_v + (q_v - off_v)).toNat + 1)
    (hq4_2 : (off4_v + (q_v - off_v) + (2 : BitVec 64)).toNat = (off4_v + (q_v - off_v)).toNat + 2)
    (hm : (FullMem c { st4 with core := { st4.core with
        arena := (st4.core.arena.set i4 not_lit).set ir repl,
        wstk := (st4.core.wstk.set (off4_v + (q_v - off_v)).toNat w0).set q4_1 cref,
        oom := (1 : BitVec 64) } } ⋆ R) m) :
    let q4_v := off4_v + (q_v - off_v)
    let st6 : FullState := { st4 with core := { st4.core with
      arena := (st4.core.arena.set (cref.toNat + 4) not_lit).set (cref.toNat + 3 + r) repl,
      wstk := (st4.core.wstk.set q4_v.toNat w0).set (q4_v.toNat + 1) cref, oom := 1#64 } }
    PropLitInv c F0 F_cur s st6 not_lit.toNat off4_v.toNat (q4_v + (2 : BitVec 64)).toNat
      (off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v)).toNat
      (off4_v + (end_v - off_v)).toNat ∧ (FullMem c st6 ⋆ R) m := by
  intro q4_v st6
  have haren4 := hlen4.core_ok.arena_len_arr; have halen4 := hlen4.core_ok.arena_len_le
  have hwstk4 := hlen4.core_ok.wstk_len_arr; have hwlen4 := hlen4.core_ok.wlen_le
  have hb4 := hsw4'.layout.bounds not_lit.toNat hnot_lt
  have hoff4 := hsw4'.off_eq; have hsz4 := hsw4'.sz_eq
  have hq4_ge := hsw4'.q_ge; have hq4_le := hsw4'.q_le_p; have hp4_le := hsw4'.p_le_end
  have hq_ge := hpi1.sw.q_ge; have hq_le := hpi1.sw.q_le_p; have hp_le := hpi1.sw.p_le_end
  have hst4_ar4 : st4.core.arena[cref.toNat + 3 + 1]'(by omega) = repl := by
    have h1 : st4.core.arena[cref.toNat + 4]'(by omega) = repl := by
      simp only [har_eq]; rw [List.getElem_set_ne (by omega), List.getElem_set_self]
    exact h1
  have hst4_arr : st4.core.arena[cref.toNat + 3 + r]'(by omega) = not_lit := by
    simp only [har_eq]; rw [List.getElem_set_self]
  have ⟨hnw5, hperm45⟩ := full_swapLits_preserves_nw hlen4.core_ok hnw4 hcr_ref3 (k1 := 1) (k2 := r)
    (by omega) (by omega)
  let st5 : FullState := { st4 with core := { st4.core with
    arena := (st4.core.arena.set (cref.toNat + 4) not_lit).set (cref.toNat + 3 + r) repl } }
  have hst5_sw : st5.core = { st4.core with
    arena := (st4.core.arena.set (cref.toNat + 3 + 1)
        (st4.core.arena[cref.toNat + 3 + r]'(by omega))).set
      (cref.toNat + 3 + r) (st4.core.arena[cref.toNat + 3 + 1]'(by omega)) } := by
    simp only [st5, hst4_ar4, hst4_arr]
  rw [← hst5_sw] at hnw5 hperm45
  have hcr_ref5 : cref.toNat ∈ fullArenaClauseRefsCore st5.core := hperm45.1.symm ▸ hcr_ref3
  have hsw5 := hsw4'.with_nonwatch (k' := st5.core) rfl rfl rfl rfl hperm45.1
  have hq4_e : q4_v.toNat =
      fullWatchOffCore st4.core not_lit.toNat + (q_v.toNat - off_v.toNat) := hq4_nat
  have hp4_split : (off4_v + (p_v + (1 : BitVec 64) + (1 : BitVec 64) - off_v)).toNat =
      (fullWatchOffCore st4.core not_lit.toNat + (p_v.toNat - off_v.toNat)) + 2 := by omega
  have hsw5_w := (by rwa [hp4_split] at hsw5 :
      SplitWatchesInv F_cur st5.core not_lit.toNat off4_v.toNat q4_v.toNat
        ((fullWatchOffCore st4.core not_lit.toNat + (p_v.toNat - off_v.toNat)) + 2)
        (off4_v + (end_v - off_v)).toNat).write_large hnot_lt (by omega)
    (by simp [st5]; omega) (by simp [st5]; omega) hflag hcr_lt hcr_ref5
  have hlen6 : st6.LengthsOk c :=
    ⟨{ hlen4.core_ok with
        arena_len_arr := by simp [st6, haren4], wstk_len_arr := by simp [st6, hwstk4] },
     hlen4.scratch_ok⟩
  refine ⟨{ len := hlen6
            nw := fullWitnessInv_nw_congr hlen6.core_ok.cur_vars_le hnw5
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            sw := by rw [hq4_2, hp4_split]; exact hsw5_w.with_nonwatch rfl rfl rfl rfl rfl
            ag := hag4.update (fun k =>
              { k with arena := st6.core.arena, wstk := st6.core.wstk, oom := 1#64 })
            tr := htr4.congr rfl rfl rfl, perm := hperm4.trans hperm45
            sc_eq := hsc4, not_f := hnot4 }, ?_⟩
  subst hi4; subst hir; subst hq4_1; exact hm

theorem propLit_js3_swap {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st_t : FullState} {not_lit cref l1 : BitVec 32} {off_v p_v q_v end_v : BitVec 64}
    {i3 i4 : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen_t : st_t.LengthsOk c)
    (hnw_t : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st_t.core))
    (hsw_t : SplitWatchesInv F_cur st_t.core not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hag_t : AgreesExcept propLitCoreMask s.core st_t.core) (htr : FullTrailExt s.core st_t.core)
    (hperm_t : FullArenaPermEq s.core st_t.core)
    (hsc_t : st_t.scratch = { s.scratch with
      search_ticks := st_t.scratch.search_ticks, wsort := st_t.scratch.wsort,
      phases := st_t.scratch.phases })
    (hnot_f : st_t.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore st_t.core)
    (hng_t : fullArenaClauseGarbCore st_t.core cref.toNat = false)
    (hcsz3 : 3 ≤ fullArenaClauseSizeCore st_t.core cref.toNat)
    (hcr_fit : cref.toNat + 3 + fullArenaClauseSizeCore st_t.core cref.toNat ≤ st_t.core.arena_len)
    (hi3 : i3 = cref.toNat + 3) (hi4 : i4 = cref.toNat + 4)
    (hl0_eq : st_t.core.arena[cref.toNat + 3]'(by
      have := hlen_t.core_ok.arena_len_arr; have := hlen_t.core_ok.arena_len_le; omega) = not_lit)
    (hl1_eq : st_t.core.arena[cref.toNat + 4]'(by
      have := hlen_t.core_ok.arena_len_arr; have := hlen_t.core_ok.arena_len_le; omega) = l1)
    (hm : (FullMem c { st_t with core := { st_t.core with
        arena := (st_t.core.arena.set i3 l1).set i4 not_lit } } ⋆ R) m) :
    let st1 : FullState := { st_t with core := { st_t.core with
      arena := (st_t.core.arena.set (cref.toNat + 3) l1).set (cref.toNat + 4) not_lit } }
    PropLitInv c F0 F_cur s st1 not_lit.toNat off_v.toNat q_v.toNat (p_v.toNat + 2) end_v.toNat ∧
    cref.toNat ∈ fullArenaClauseRefsCore st1.core ∧
    fullArenaClauseGarbCore st1.core cref.toNat = false ∧
    fullArenaClauseSizeCore st1.core cref.toNat = fullArenaClauseSizeCore st_t.core cref.toNat ∧
    st1.core.arena[cref.toNat + 3]? = some l1 ∧ st1.core.arena[cref.toNat + 4]? = some not_lit ∧
    (FullMem c st1 ⋆ R) m := by
  intro st1
  have haren := hlen_t.core_ok.arena_len_arr; have halen := hlen_t.core_ok.arena_len_le
  have ⟨hnw1, hperm_t1⟩ := full_swapLits_preserves_nw hlen_t.core_ok hnw_t hcr_ref (k1 := 0)
    (k2 := 1) (by omega) (by omega)
  have hst1_sw : st1.core = { st_t.core with
    arena := (st_t.core.arena.set (cref.toNat + 3 + 0)
        (st_t.core.arena[cref.toNat + 3 + 1]'(by omega))).set
      (cref.toNat + 3 + 1) (st_t.core.arena[cref.toNat + 3 + 0]'(by omega)) } := by
    simp only [st1, hl0_eq, hl1_eq]
  rw [← hst1_sw] at hnw1 hperm_t1
  have hlen1 : st1.LengthsOk c :=
    ⟨{ hlen_t.core_ok with arena_len_arr := by simp [st1, haren] }, hlen_t.scratch_ok⟩
  refine ⟨{ len := hlen1, nw := hnw1
            sw := hsw_t.with_nonwatch (k' := st1.core) rfl rfl rfl rfl hperm_t1.1
            ag := hag_t.update (fun k => { k with arena := st1.core.arena })
            tr := htr.congr rfl rfl rfl, perm := hperm_t.trans hperm_t1
            sc_eq := hsc_t, not_f := hnot_f },
    hperm_t1.1.symm ▸ hcr_ref, (hperm_t1.2 cref.toNat hcr_ref).2.1.trans hng_t,
    (hperm_t1.2 cref.toNat hcr_ref).1,
    by simp [st1, List.getElem?_set_ne (by omega : cref.toNat + 4 ≠ cref.toNat + 3),
         List.getElem?_set_self (show cref.toNat + 3 < st_t.core.arena.length by omega)],
    by rw [List.getElem?_set_self (by simp; omega)], ?_⟩
  subst hi3; subst hi4; exact hm

end LeanQbe.T.Examples.Kissat.Full
