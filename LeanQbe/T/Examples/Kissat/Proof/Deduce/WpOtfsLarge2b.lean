/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpOtfsLarge2
public import LeanQbe.T.Examples.Kissat.Src.Deduce
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpCommon
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import Kraken.Mem
import Kraken.Separation

/-!
# Large OTFS Full WP (`Proof.Deduce.WpOtfsLarge2b`)

Proves `full_otfs_large_wp` against `Proof.Deduce.Spec.step13OtfsLargeSpec` using
`WpOtfsLarge0`/`1`/`2` helpers (`<= 1,500`L/file, `<= 450`L/decl, `<= 100` cols).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Deduce

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics DeduceTactics

/-! ## 1. Pure Watch & Arena Preservation Helpers -/

private theorem s13_otfs_lits_all_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} {cref : BitVec 32} {old_sz : Nat}
    (hlen : s.LengthsOk c)
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (har_len : s.core.arena.length = c.arena_cap)
    (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap)
    (hsz_eq : old_sz = fullArenaClauseSize s cref.toNat)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref.toNat = false) :
    ∀ j < old_sz,
      (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ≠ 4294967295#32 := by
  intro j hj
  subst hsz_eq
  have hmem : (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat ∈
      fullArenaClauseLits s cref.toNat := by
    have hj_ar : cref.toNat + 3 + j < s.core.arena.length := by rw [har_len]; omega
    have hj_tk : j < (List.take (fullArenaClauseSize s cref.toNat)
        (List.drop (cref.toNat + 3) s.core.arena)).length := by
      rw [List.length_take, List.length_drop, har_len]; omega
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    refine List.mem_map.mpr ⟨_, List.getElem_mem hj_tk, ?_⟩
    change (List.take (fullArenaClauseSize s cref.toNat)
      (List.drop (cref.toNat + 3) s.core.arena))[j].toNat = _
    rw [List.getElem_take, List.getElem_drop, List.getElem?_eq_getElem hj_ar, Option.getD_some]
  have hlt := hw.arena.lits_lt cref.toNat hcref hng _ hmem
  have hm_lt := c.hmaxv; change c.max_vars < 2 * 268435456 at hm_lt
  have hcv := hlen.core_ok.cur_vars_le
  refine ⟨hlt, fun h => ?_⟩
  have hto := congrArg BitVec.toNat h; simp only [BitVec.reduceToNat] at hto; omega

private theorem s13_otfs_swap01_sw_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s s1 : FullState} {cref l0 uip : BitVec 32}
    {wv1 ws1 : List (BitVec 32)} {wl1 : Nat} {wu1 : BitVec 64}
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hnd : FullArenaVarsNodup s)
    (hs1_len : s1.LengthsOk c)
    (hs1_c : s1.core = { s.core with wvec := wv1, wstk := ws1, wlen := wl1, wusable := wu1 })
    (hmw1 : ModeWatchesInv F_cur s1.core) (har_len : s.core.arena.length = c.arena_cap)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cref.toNat = false) (hdm : s.core.dense_mode = 0#64)
    (hs01 : (l0 = s.core.arena[cref.toNat + 3]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 4]?.getD 0#32 = uip) ∨
      (l0 = s.core.arena[cref.toNat + 4]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 3]?.getD 0#32 = uip)) :
    let ar1 := (s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip
    let s_sw : FullState := { s1 with core := { s1.core with arena := ar1 } }
    s_sw.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut s_sw.core ∧
    FullArenaVarsNodup s_sw ∧ WatchesInv F_cur s_sw.core ∧
    fullArenaClauseRefs s_sw = fullArenaClauseRefs s1 ∧
    fullArenaClauseGarb s_sw cref.toNat = false := by
  intro ar1 s_sw
  obtain ⟨hw_s1, hnd_s1⟩ := s13_otfs_cut_nd_of_watch_eq hw hnd hs1_c hmw1
  have hng_s1 : fullArenaClauseGarb s1 cref.toNat = false := by
    change fullArenaClauseGarbCore s1.core cref.toNat = false; rw [hs1_c]; exact hng
  have hs01_s1 : (l0 = s1.core.arena[cref.toNat + 3]?.getD 0#32 ∧
      s1.core.arena[cref.toNat + 4]?.getD 0#32 = uip) ∨
    (l0 = s1.core.arena[cref.toNat + 4]?.getD 0#32 ∧
      s1.core.arena[cref.toNat + 3]?.getD 0#32 = uip) := by rw [hs1_c]; exact hs01
  obtain ⟨hw_sw, hnd_sw, hrefs_sw, _, hng_sw, _, _, _⟩ :=
    otfs_large_swap01 hs1_len hw_s1 hnd_s1
      (by change cref.toNat ∈ fullArenaClauseRefsCore s1.core
          unfold fullArenaClauseRefsCore; rw [hs1_c]; exact hcref)
      hng_s1 hs01_s1
  let ar1' := (s1.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip
  have har1_eq : ar1' = ar1 := by
    dsimp only [ar1', ar1]; rw [show s1.core.arena = s.core.arena by rw [hs1_c]]
  have hsw_eq : ({ s1 with core := { s1.core with arena := ar1' } } : FullState) = s_sw :=
    congrArg (fun a => { s1 with core := { s1.core with arena := a } }) har1_eq
  have hw_sw' : FullWitnessCutInv c F0 F_cur cut s_sw.core := hsw_eq ▸ hw_sw
  refine ⟨⟨{ hs1_len.core_ok with arena_len_arr := by simp [s_sw, ar1, har_len] },
      hs1_len.scratch_ok⟩, hw_sw', hsw_eq ▸ hnd_sw, ?_, hsw_eq ▸ hrefs_sw, hsw_eq ▸ hng_sw⟩
  simpa only [ModeWatchesInv, s_sw, hs1_c, hdm, ↓reduceIte] using hw_sw'.watches

private theorem s13_otfs_s2_refs_ng {s s1 s_sw s2 : FullState} {cref : BitVec 32}
    {wv1 ws1 wv2 ws2 : List (BitVec 32)} {wl1 : Nat} {wu1 wu2 : BitVec 64}
    (hs1_c : s1.core = { s.core with wvec := wv1, wstk := ws1, wlen := wl1, wusable := wu1 })
    (hs_sw_c : s_sw.core = { s.core with
      wvec := wv1, wstk := ws1, wlen := wl1, wusable := wu1, arena := s_sw.core.arena })
    (hs2_c : s2.core = { s.core with
      wvec := wv2, wstk := ws2, wlen := wl1, wusable := wu2, arena := s_sw.core.arena })
    (hrefs_sw : fullArenaClauseRefs s_sw = fullArenaClauseRefs s1)
    (hng_sw : fullArenaClauseGarb s_sw cref.toNat = false) :
    fullArenaClauseRefs s2 = fullArenaClauseRefs s ∧
    fullArenaClauseGarb s2 cref.toNat = false := by
  refine ⟨?_, ?_⟩
  · change fullArenaClauseRefsCore s2.core = fullArenaClauseRefsCore s.core
    change fullArenaClauseRefsCore s_sw.core = fullArenaClauseRefsCore s1.core at hrefs_sw
    have h2 : fullArenaClauseRefsCore s1.core = fullArenaClauseRefsCore s.core := by
      unfold fullArenaClauseRefsCore; rw [hs1_c]
    have h1 : fullArenaClauseRefsCore s2.core = fullArenaClauseRefsCore s_sw.core := by
      unfold fullArenaClauseRefsCore; rw [hs2_c, hs_sw_c]
    exact h1.trans (hrefs_sw.trans h2)
  · change fullArenaClauseGarbCore s2.core cref.toNat = false
    change fullArenaClauseGarbCore s_sw.core cref.toNat = false at hng_sw
    unfold fullArenaClauseGarbCore fullArenaHdrCore at hng_sw ⊢
    rw [hs2_c]; rw [hs_sw_c] at hng_sw; exact hng_sw

private theorem s13_otfs_oom_hpost {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u : Nat} {s s1 : FullState} {Q : Post [.bool]} {R : Mem 64 → Prop} {ml_o : Mem 64}
    {cref : BitVec 32} {wv1 ws1 wso1 : List (BitVec 32)} {wl1 : Nat} {wu1 : BitVec 64}
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hnd : FullArenaVarsNodup s)
    (hiu_cut : idx_u < cut) (hs1_len : s1.LengthsOk c)
    (hs1_c : s1.core = { s.core with wvec := wv1, wstk := ws1, wlen := wl1, wusable := wu1 })
    (hs1_sc : s1.scratch = { s.scratch with wsort := wso1 }) (hmw1 : ModeWatchesInv F_cur s1.core)
    (hml_o : (FullMem c { s1 with core := { s1.core with oom := 1#64 } } ⋆ R) ml_o)
    (hPost : ∀ (ok : Bool) flags' arena' wvec' wstk' wlen' wu' oom' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with flags := flags', arena := arena', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wu', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur idx_u s'.core → FullArenaVarsNodup s' →
      FullExtScratchPres s s' → sc'.work_stk1 = s.scratch.work_stk1 →
      sc'.work_stk2 = s.scratch.work_stk2 → sc'.res_sz = s.scratch.res_sz →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = true → cref.toNat ∈ fullArenaClauseRefs s' ∧
        fullArenaClauseGarb s' cref.toNat = false ∧
        ∀ l ∈ fullArenaClauseLits s' cref.toNat, s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
          ((s'.core.lvl[l / 2]?.getD 0#32).toNat = s'.core.cur_level →
            ∃ m < idx_u, (s'.core.trl[m]?.getD 0#32).toNat = l ^^^ 1)) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Q (false, ()) ml_o := by
  obtain ⟨hlo, hwo, hndo, hmo⟩ := s13_otfs_oom_core hw hnd hiu_cut hs1_len hs1_c hmw1 hml_o
  exact hPost false s.core.flags s.core.arena wv1 ws1 wl1 wu1 1#64 s1.scratch ml_o
    hlo hwo hndo ⟨by simp [hs1_sc], by simp [hs1_sc]⟩
    (by simp [hs1_sc]) (by simp [hs1_sc]) (by simp [hs1_sc]) rfl (fun h => absurd h (by decide)) hmo

private theorem s13_otfs_loop2_post_fin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u : Nat} {s s2 s3 s4 s5 : FullState} {Q : Post [.bool]} {R : Mem 64 → Prop}
    {m5 : Mem 64} {cref uip : BitVec 32} {fl3 ar3 ar4 wv2 ws2 wstk' wso1 : List (BitVec 32)}
    {wl1 : Nat} {wu2 otfs' : BitVec 64}
    (hlen : s.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cref.toNat = false)
    (hiu_cut : idx_u < cut) (hiu_te : idx_u < s.core.trail_end)
    (ht_u : (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat)
    (hr_u : s.core.rsns[uip.toNat / 2]?.getD 4294967295#32 = cref)
    (hs2_c : s2.core = { s.core with
      wvec := wv2, wstk := ws2, wlen := wl1, wusable := wu2, arena := s2.core.arena })
    (hs2_sc : s2.scratch = { s.scratch with wsort := wso1 })
    (hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s)
    (hs3_eq : s3 = { s2 with core := { s2.core with arena := ar3, flags := fl3 } })
    (hrefs3 : fullArenaClauseRefs s3 = fullArenaClauseRefs s2)
    (hsub3 : ∀ l ∈ fullArenaClauseLits s3 cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat)
    (hs4_eq : s4 = { s3 with core := { s3.core with arena := ar4 } })
    (hrefs4 : fullArenaClauseRefs s4 = fullArenaClauseRefs s3)
    (hperm4 : (fullArenaClauseLits s4 cref.toNat).Perm (fullArenaClauseLits s3 cref.toNat))
    (hs5_eq : s5 = { s4 with
      core := { s4.core with wstk := wstk' }
      scratch := { s4.scratch with otfs_cnt := otfs' } })
    (hlen5 : s5.LengthsOk c) (hw5 : FullWitnessCutInv c F0 F_cur idx_u s5.core)
    (hnd5 : FullArenaVarsNodup s5) (hrefs5 : fullArenaClauseRefs s5 = fullArenaClauseRefs s4)
    (hng5 : fullArenaClauseGarb s5 cref.toNat = false)
    (hlits5 : fullArenaClauseLits s5 cref.toNat = fullArenaClauseLits s4 cref.toNat)
    (hm5 : (FullMem c s5 ⋆ R) m5)
    (hPost : ∀ (ok : Bool) flags' arena' wvec' wstk' wlen' wu' oom' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with flags := flags', arena := arena', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wu', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur idx_u s'.core → FullArenaVarsNodup s' →
      FullExtScratchPres s s' → sc'.work_stk1 = s.scratch.work_stk1 →
      sc'.work_stk2 = s.scratch.work_stk2 → sc'.res_sz = s.scratch.res_sz →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = true → cref.toNat ∈ fullArenaClauseRefs s' ∧
        fullArenaClauseGarb s' cref.toNat = false ∧
        ∀ l ∈ fullArenaClauseLits s' cref.toNat, s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
          ((s'.core.lvl[l / 2]?.getD 0#32).toNat = s'.core.cur_level →
            ∃ m < idx_u, (s'.core.trl[m]?.getD 0#32).toNat = l ^^^ 1)) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Q (true, ()) m5 := by
  let core5 : FullCoreState :=
    { s.core with
      flags := fl3, arena := ar4, wvec := wv2,
      wstk := wstk', wlen := wl1, wusable := wu2, oom := s.core.oom }
  let sc5 : FullScratch := { s.scratch with wsort := wso1, otfs_cnt := otfs' }
  have hs5_c : s5.core = core5 := by
    rw [hs5_eq]; dsimp only; rw [hs4_eq, hs3_eq, hs2_c]
  have hs5_sc : s5.scratch = sc5 := by
    rw [hs5_eq]; dsimp only; rw [hs4_eq, hs3_eq, hs2_sc]
  have hs5_f : s5 = ⟨core5, sc5⟩ := congr (congrArg FullState.mk hs5_c) hs5_sc
  have hrefs5_s : fullArenaClauseRefs s5 = fullArenaClauseRefs s := by
    rw [hrefs5, hrefs4]; exact hrefs3.trans hrefs2
  have hsub5 : ∀ l ∈ fullArenaClauseLits s5 cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat := fun l hl => by
    rw [hlits5] at hl; exact hsub3 l (hperm4.subset hl)
  have hfin := s13_otfs_large_fin hlen hw hcref hng hiu_cut hiu_te ht_u hr_u
    (by rw [hs5_c]) (by rw [hs5_c]) (by rw [hs5_c]) (by rw [hs5_c]) hsub5
  have hmem_s' : cref.toNat ∈ fullArenaClauseRefs ⟨core5, sc5⟩ := by
    rw [← hs5_f, hrefs5_s]; exact hcref
  have hng_s' : fullArenaClauseGarb ⟨core5, sc5⟩ cref.toNat = false := by
    rw [← hs5_f]; exact hng5
  have hfin_s' : ∀ l ∈ fullArenaClauseLits ⟨core5, sc5⟩ cref.toNat,
      core5.vals[l]?.getD 0#8 = 0xFF#8 ∧
      ((core5.lvl[l / 2]?.getD 0#32).toNat = core5.cur_level →
        ∃ m < idx_u, (core5.trl[m]?.getD 0#32).toNat = l ^^^ 1) := fun l hl => by
    rw [← hs5_f] at hl; rw [← hs5_c]; exact (hfin l hl).2.2
  exact hPost true fl3 ar4 wv2 wstk' wl1 wu2 s.core.oom sc5 m5
    (hs5_f ▸ hlen5) (by change FullWitnessCutInv c F0 F_cur idx_u core5; rw [← hs5_c]; exact hw5)
    (hs5_f ▸ hnd5) ⟨rfl, rfl⟩ rfl rfl rfl (hs5_f ▸ hrefs5_s)
    (fun _ => ⟨hmem_s', hng_s', hfin_s'⟩) (hs5_f ▸ hm5)

private theorem s13_otfs_init_idx_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} {cref : BitVec 32}
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (har_len : s.core.arena.length = c.arena_cap)
    (hal : s.core.arena_len ≤ c.arena_cap) (hcap : c.arena_cap < 2 ^ 31 - 1)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s) :
    let old_sz := fullArenaClauseSize s cref.toNat
    3 ≤ old_sz ∧ cref.toNat + 3 + old_sz ≤ c.arena_cap ∧
    (cref.setWidth 64 + (2 : BitVec 64)).toNat = cref.toNat + 2 ∧
    (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3 ∧
    (cref.setWidth 64 + 3#64 + 1#64).toNat = cref.toNat + 4 ∧
    (cref.setWidth 64 + (2 : BitVec 64)).toNat < s.core.arena.length ∧
    (cref.setWidth 64 + 3#64).toNat < s.core.arena.length ∧
    (cref.setWidth 64 + 3#64 + 1#64).toNat < s.core.arena.length ∧
    s.core.arena[(cref.setWidth 64 + (2 : BitVec 64)).toNat]'(by
      have hwf := hw.arena.refs_wf cref.toNat hcref
      have hwf3 := hwf.2.2.1
      change cref.toNat + 3 + fullArenaClauseSizeCore s.core cref.toNat ≤
        fullArenaNextOff s.core.arena s.core.arena_len cref.toNat at hwf3
      have _h3o : cref.toNat + 3 + fullArenaClauseSize s cref.toNat ≤ c.arena_cap := by
        change cref.toNat + 3 + fullArenaClauseSizeCore s.core cref.toNat ≤ c.arena_cap
        exact Nat.le_trans hwf3 (Nat.le_trans hwf.2.2.2.1 hal)
      rw [BitVec.toNat_add, zext_toNat _ (by decide),
        show ((2 : BitVec 64)).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega), har_len]; omega) =
      BitVec.ofNat 32 old_sz := by
  have hwf := hw.arena.refs_wf cref.toNat hcref
  have hwf3 := hwf.2.2.1
  have h3o : cref.toNat + 3 + fullArenaClauseSize s cref.toNat ≤ c.arena_cap := by
    change cref.toNat + 3 + fullArenaClauseSizeCore s.core cref.toNat ≤
      fullArenaNextOff s.core.arena s.core.arena_len cref.toNat at hwf3
    change cref.toNat + 3 + fullArenaClauseSizeCore s.core cref.toNat ≤ c.arena_cap
    exact Nat.le_trans hwf3 (Nat.le_trans hwf.2.2.2.1 hal)
  have h2z : (cref.setWidth 64 + (2 : BitVec 64)).toNat = cref.toNat + 2 := by
    rw [BitVec.toNat_add, zext_toNat _ (by decide),
      show ((2 : BitVec 64)).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
  have h3z : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3 := by
    rw [BitVec.toNat_add, zext_toNat _ (by decide),
      show (3#64 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
  have h4z := otfs_bv_idx4_64 cref (by omega)
  have h2b : (cref.setWidth 64 + (2 : BitVec 64)).toNat < s.core.arena.length := by
    rw [h2z, har_len]; omega
  have h3b : (cref.setWidth 64 + 3#64).toNat < s.core.arena.length := by
    rw [h3z, har_len]; have := hwf.2.1; change 3 ≤ fullArenaClauseSize s cref.toNat at this; omega
  have h4b : (cref.setWidth 64 + 3#64 + 1#64).toNat < s.core.arena.length := by
    rw [h4z, har_len]; have := hwf.2.1; change 3 ≤ fullArenaClauseSize s cref.toNat at this; omega
  refine ⟨hwf.2.1, h3o, h2z, h3z, h4z, h2b, h3b, h4b, ?_⟩
  have hbd2 : cref.toNat + 2 < s.core.arena.length := by rw [har_len]; omega
  have h1 : fullArenaClauseSize s cref.toNat = (s.core.arena[cref.toNat + 2]?.getD 0#32).toNat :=
    rfl
  rw [List.getElem?_eq_getElem hbd2, Option.getD_some] at h1
  rw [getElem_eq_of_idx h2z]
  exact BitVec.eq_of_toNat_eq (by rw [bv32_ofNat_toNat (by omega), h1])

private theorem s13_otfs_hdr_prep {c : FullCfg} {s s2 : FullState} {ar1 ar_cur : List (BitVec 32)}
    {cref l0 uip : BitVec 32} {old_sz nsz : Nat}
    (har_len : s.core.arena.length = c.arena_cap) (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap)
    (har1_def : ar1 = (s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip)
    (har2_eq : s2.core.arena = ar1)
    (hout_cur : ∀ q, q < cref.toNat + 4 ∨ cref.toNat + 3 + nsz ≤ q → ar_cur[q]? = ar1[q]?) :
    ar_cur[cref.toNat]? = some (fullArenaHdrCore s2.core cref.toNat) ∧
    (∀ q, 2 ≤ q → ar1[cref.toNat + 3 + q]? = s.core.arena[cref.toNat + 3 + q]?) ∧
    (∀ i, i < cref.toNat + 3 ∨ cref.toNat + 5 ≤ i → ar1[i]? = s2.core.arena[i]?) := by
  refine ⟨?_, fun q hq => ?_, fun i _ => by rw [har2_eq]⟩
  · rw [hout_cur _ (Or.inl (by omega))]
    unfold fullArenaHdrCore; rw [har2_eq, har1_def]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_eq_getElem (by rw [har_len]; omega), Option.getD_some]
  · rw [har1_def, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

/-! ## 2. Full `full_otfs_large_wp` -/

theorem full_otfs_large_wp (Γ : Env)
    (hDefrag : Γ.Has "full_wstack_defrag" fullWstackDefragSpec)
    (hUnw : Γ.Has "full_unwatch_large" fullUnwatchLargeSpec)
    (hPush : Γ.Has "full_watch_push" fullWatchPushSpec) :
    ∀ a m Q X, Spec.step13OtfsLargeSpec a m Q X →
      Func.wp Γ Src.Deduce.full_otfs_large_body a m Q X := by
  rintro ⟨h, cref, uip, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, cut, idx_u, s, R, rfl, hlen, hw, hnd, hdm, hcref, hng, huip_lt, hiu_cut,
      ht_u, hr_u, hlu_eq, hent_orig, hm, hPost⟩
  have hcap : c.arena_cap < 2 ^ 31 - 1 := by
    have ha := c.harena; change c.arena_cap < 2 * 268435456 at ha; omega
  have hal := hlen.core_ok.arena_len_le
  have har_len := hlen.core_ok.arena_len_arr
  have hlvl_len := hlen.core_ok.lvl_len
  have hcv_le := hlen.core_ok.cur_vars_le
  have hiu_te : idx_u < s.core.trail_end := Nat.lt_of_lt_of_le hiu_cut hw.cut_le
  have hret_false_id : Q (false, ()) m := by
    refine hPost false s.core.flags s.core.arena s.core.wvec s.core.wstk s.core.wlen
      s.core.wusable s.core.oom s.scratch m hlen (s13_otfs_cut_shrink hw (Nat.le_of_lt hiu_cut))
      hnd (fullExtScratchPres_refl s) rfl rfl rfl rfl (fun h => absurd h (by decide)) hm
  let old_sz := fullArenaClauseSize s cref.toNat
  obtain ⟨h3_old, h3o, hcr2_z, hcr3_z, hcr4_z, hcr2_bd, hcr3_bd, hcr4_bd, hsz_eq⟩ :=
    s13_otfs_init_idx_facts hw har_len hal hcap hcref
  have hlits_all := s13_otfs_lits_all_ok hlen hw har_len h3o rfl hcref hng
  unfold Func.wp Src.Deduce.full_otfs_large_body
  c0_hstraight
  refine wp_join_group (ts := [i32])
    (fun (l0, ()) ml => ml = m ∧
      ((l0 = s.core.arena[cref.toNat + 3]?.getD 0#32 ∧
          s.core.arena[cref.toNat + 4]?.getD 0#32 = uip) ∨
        (l0 = s.core.arena[cref.toNat + 4]?.getD 0#32 ∧
          s.core.arena[cref.toNat + 3]?.getD 0#32 = uip))) ?_ ?_
  · rintro Js ⟨l0, ⟨⟩⟩ ml ⟨hm1, hs01⟩; subst ml
    have hl0_bd : l0.toNat < 2 * s.core.cur_vars ∧ l0 ≠ 0xFFFFFFFF#32 := by
      rcases hs01 with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hlits_all 0 (by omega)
      · exact hlits_all 1 (by omega)
    c0_hstraight
    have hcr3_of : BitVec.setWidth 64 cref + (3 : BitVec 64) =
        BitVec.setWidth 64 cref + 3#64 := rfl
    simp only [hsz_eq, hcr3_of]
    refine s13_otfs_loop1_wp hlen hm hcap h3o h3_old (fun j hj => (hlits_all j hj).1)
      (fun p_nsz => _) (fun nsz_p1 _ h3_p1 => ?_)
    c0_hstraight
    c0_hstep_np
    · c0_hstraight; exact hret_false_id
    · have hact_ge : 3 ≤ 1 + otfsActCnt s.core cref.toNat old_sz := by
        apply h3_p1
        have hc' : ¬ nsz_p1.toNat < (3#32 : BitVec 32).toNat := by c0_bound
        exact Nat.le_of_not_lt hc'
      have h4_old : 4 ≤ old_sz := by
        have := otfsActCnt_le s.core cref.toNat old_sz; omega
      clear hc
      refine wp_loop_inv (ts := [i32, i32, i32])
        (fun (i_v, _, _, ()) m1 =>
          m1 = m ∧ ∃ i_nat : Nat, 2 ≤ i_nat ∧ i_nat ≤ old_sz ∧ i_v = BitVec.ofNat 32 i_nat)
        (fun (i_v, _, _, ()) _ => old_sz - i_v.toNat) ?_ ?_
      · intro J0 hL0; c0_hstraight
        exact hL0 (2#32, 0#32, uip, ()) m ⟨rfl, 2, Nat.le_refl _, by omega, rfl⟩
      · rintro J0 ⟨i_v, bl_v, l1_v, ⟨⟩⟩ m1 ⟨hm1, i_nat, hi2, hile, rfl⟩ hL0; subst m1
        have hi_32 : (BitVec.ofNat 32 i_nat).toNat = i_nat := bv32_ofNat_toNat (by omega)
        have hold_32 : (BitVec.ofNat 32 old_sz).toNat = old_sz := bv32_ofNat_toNat (by omega)
        c0_hstraight
        c0_hstep_np
        · have hilt : i_nat < old_sz := by
            have hc' : (BitVec.ofNat 32 i_nat).toNat < (BitVec.ofNat 32 old_sz).toNat := by
              c0_bound
            rwa [hi_32, hold_32] at hc'
          obtain ⟨hz_idx, hidx_bd⟩ := s13_otfs_ar_idx3_lt_len hcap har_len h3o hilt
          have har_bd : cref.toNat + 3 + i_nat < s.core.arena.length := by rw [har_len]; omega
          let idx := (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i_nat).setWidth 64).toNat
          have hot_eq :
              s.core.arena[idx]'hidx_bd = s.core.arena[cref.toNat + 3 + i_nat]'har_bd :=
            getElem_eq_of_idx hz_idx
          have hv_bd : (s.core.arena[cref.toNat + 3 + i_nat]?.getD 0#32).toNat / 2 <
              s.core.lvl.length := by
            have := (hlits_all i_nat hilt).1; rw [hlvl_len]; omega
          have hlvl_bd : (BitVec.setWidth 64 ((s.core.arena[idx]'hidx_bd) >>> 1#32)).toNat <
              s.core.lvl.length := by
            rw [otfs_bv32_lshr1_zext_toNat, hot_eq]
            rw [List.getElem?_eq_getElem har_bd, Option.getD_some] at hv_bd; exact hv_bd
          have hi1_32 : BitVec.ofNat 32 i_nat + 1 = BitVec.ofNat 32 (i_nat + 1) :=
            otfs_bv32_ofNat_add1 i_nat
          clear hc; c0_hstraight
          refine wp_join_group (ts := [i32, i32]) (fun _ m2 => m2 = m) ?_ ?_
          · rintro J1 ⟨bl', l1', ⟨⟩⟩ m2 hm2; subst m2; c0_hstraight
            exact hL0 (_, bl', l1', ()) m (by
              dsimp only; rw [hi1_32, bv32_ofNat_toNat (by omega), hi_32]; omega)
              ⟨rfl, i_nat + 1, by omega, by omega, hi1_32⟩
          · intro J1 hJ1; c0_hstraight; c0_hstep_np
            · c0_hstraight; exact hJ1 (_, _, ()) m rfl
            · c0_hstraight; exact hJ1 (_, _, ()) m rfl
        · clear hc; c0_hstraight
          let l1 := l1_v
          refine wp_join_group (ts := [])
            (fun _ ml_d => ∃ s_d wv_d ws_d wl_d wu_d wso_d,
              s_d.core =
                { s.core with wvec := wv_d, wstk := ws_d, wlen := wl_d, wusable := wu_d } ∧
              s_d.scratch = { s.scratch with wsort := wso_d } ∧
              s_d.LengthsOk c ∧ ModeWatchesInv F_cur s_d.core ∧ (FullMem c s_d ⋆ R) ml_d) ?_ ?_
          · intro Js_e _ ml_d ⟨s_d, wv_d, ws_d, wl_d, wu_d, wso_d, hsd_c, hsd_sc, hsd_len, hmw_d,
              hml_d⟩
            c0_hstraight
            obtain ⟨hw_d, hnd_d⟩ := s13_otfs_cut_nd_of_watch_eq hw hnd hsd_c hmw_d
            have hmw_d' : WatchesInv F_cur s_d.core := by
              simpa only [ModeWatchesInv, hsd_c, hdm, ↓reduceIte] using hmw_d
            refine wp_call_of_spec _ _ (hPush _ _ _ _ ?_)
            dsimp only [vals, Arg.val]
            refine ⟨c, s_d, R, rfl, hsd_len, hmw_d'.layout, fun h => absurd h (by decide),
              fun _ => ⟨fun h => by
                  have h31 := congrArg (fun v : BitVec 32 => v.getLsbD 31) h; simp at h31,
                fun h => by have := congrArg BitVec.toNat h; simp at this; omega⟩,
              hml_d, fun ok_p wv1 ws1 wl1 wu1 wso1 m1 hs1_len hlay1 hother1 hok1T hok1F hm1 => ?_⟩
            let s1 : FullState :=
              { s_d with
                core := { s_d.core with wvec := wv1, wstk := ws1, wlen := wl1, wusable := wu1 }
                scratch := { s_d.scratch with wsort := wso1 } }
            have hs1_c : s1.core =
                { s.core with wvec := wv1, wstk := ws1, wlen := wl1, wusable := wu1 } := by
              dsimp only [s1]; rw [hsd_c]
            have hs1_sc : s1.scratch = { s.scratch with wsort := wso1 } := by
              dsimp only [s1]; rw [hsd_sc]
            by_cases hok1 : ok_p = true
            · subst hok1
              obtain ⟨hl1_lt, _, hsz1, hpres1, hw0_1, hw1_1⟩ := hok1T rfl
              have hw0_and : (l0 &&& 2147483647#32) &&& 2147483648#32 = 0#32 := by
                rw [BitVec.and_assoc,
                  show (2147483647#32 &&& 2147483648#32 : BitVec 32) = 0#32 from rfl,
                  BitVec.and_zero]
              have hcref_s1 : cref.toNat ∈ fullArenaClauseRefsCore s1.core := by
                rw [hs1_c]; exact hcref
              have hmw1 : ModeWatchesInv F_cur s1.core := by
                refine fullWatchPush_preserves_modeWatchesInv (ok := true) hmw_d hlay1 rfl rfl
                  (fun _ h => by simpa only [fullArenaClauseRefsCore, s1] using h)
                  (fun hc => absurd hc (by decide))
                  (fun _ => ⟨hw0_and, fun hd => absurd (by simpa [hsd_c] using hdm) hd,
                    by have h := hcap; rw [← har_len] at h; omega, hcref_s1⟩)
                  (fun l hl hne => by
                    simpa only [fullWatchSize, fullWatchOff, fullWatchSizeCore, fullWatchOffCore,
                      s1] using hother1 l hl hne)
                  (fun _ => ⟨hl1_lt, Or.inr rfl, hsz1, hpres1, hw0_1, fun _ => hw1_1 rfl⟩)
                  (fun hc => absurd hc (by decide))
              have hcr3_bd1 : (cref.setWidth 64 + 3#64).toNat < s1.core.arena.length := by
                rw [hs1_c, hcr3_z, har_len]; omega
              have hcr4_bd1 : (cref.setWidth 64 + 3#64 + 1#64).toNat <
                  (s1.core.arena.set (cref.setWidth 64 + 3#64).toNat l0).length := by
                rw [List.length_set, hs1_c, hcr4_z, har_len]; omega
              let ar1 := (s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip
              let s_sw : FullState := { s1 with core := { s1.core with arena := ar1 } }
              have har1_eq : ((s1.core.arena.set (cref.setWidth 64 + 3#64).toNat l0).set
                  (cref.setWidth 64 + 3#64 + 1#64).toNat uip) = ar1 := by
                dsimp only [ar1]; rw [hs1_c, hcr3_z, hcr4_z]
              obtain ⟨hs_sw_len, hw_sw', hnd_sw', hmw_sw', hrefs_sw, hng_sw⟩ :=
                s13_otfs_swap01_sw_ok hw hnd hs1_len hs1_c hmw1 har_len hcref hng hdm hs01
              c0_hstep_np
              · c0_hstraight
                refine wp_call_of_spec _ _ (hUnw _ _ _ _ ?_)
                dsimp only [vals, Arg.val]
                refine ⟨c, s_sw, R, rfl, hs_sw_len, hmw_sw'.layout,
                  by dsimp only [s_sw]; rw [← har1_eq]; exact (by assumption),
                  fun wv2 ws2 wu2 m2 hs2_len hlay2 hmw2 hm2 => ?_⟩
                let s2 : FullState :=
                  { s_sw with core := { s_sw.core with wvec := wv2, wstk := ws2, wusable := wu2 } }
                have hs2_c : s2.core = { s.core with
                    wvec := wv2, wstk := ws2, wlen := wl1, wusable := wu2, arena := ar1 } := by
                  dsimp only [s2, s_sw]; rw [hs1_c]
                have hs2_sc : s2.scratch = { s.scratch with wsort := wso1 } := by
                  dsimp only [s2, s_sw]; rw [hs1_sc]
                obtain ⟨hw2, hnd2⟩ := s13_otfs_cut_nd_of_watch_eq hw_sw' hnd_sw' rfl
                  (hmw2 F_cur hw_sw'.watches)
                have hs_sw_c : s_sw.core = { s.core with
                    wvec := wv1, wstk := ws1, wlen := wl1, wusable := wu1,
                    arena := s_sw.core.arena } := by
                  dsimp only [s_sw]; rw [hs1_c]
                obtain ⟨hrefs2, hng2⟩ :=
                  s13_otfs_s2_refs_ng hs1_c hs_sw_c hs2_c hrefs_sw hng_sw
                have har2_eq : s2.core.arena = ar1 := by rw [hs2_c]
                have hlvl2_eq : s2.core.lvl = s.core.lvl := by rw [hs2_c]
                have hcv2_eq : s2.core.cur_vars = s.core.cur_vars := by rw [hs2_c]
                have har2_len := hs2_len.core_ok.arena_len_arr
                have hlvl2_len := hs2_len.core_ok.lvl_len
                obtain ⟨orig0, hinv0⟩ := s13_otfs_loop2_init har_len h3o h4_old hs01
                dsimp only
                refine wp_loop_inv (ts := [i32, i32, i32, i32])
                  (fun (i_v, nsz_v, bp_v, bl_v, ()) m' =>
                    ∃ i_nat nsz bp ar_cur origMap,
                      i_v = BitVec.ofNat 32 i_nat ∧ nsz_v = BitVec.ofNat 32 nsz ∧
                      bp_v = BitVec.ofNat 32 bp ∧
                      (nsz = 1 → bp = 1 ∧ bl_v = 0#32) ∧ (2 ≤ nsz → 1 ≤ bp ∧ bp < nsz) ∧
                      S13OtfsShrinkInv c s ar1 cref l0 uip old_sz (old_sz - i_nat)
                        i_nat nsz ar_cur origMap ∧
                      (FullMem c { s2 with core := { s2.core with arena := ar_cur } } ⋆ R) m')
                  (fun (i_v, _, _, _, ()) _ => old_sz - i_v.toNat) ?_ ?_
                · intro J2 hL2; c0_hstraight
                  have hm0 : (FullMem c { s2 with core := { s2.core with arena := ar1 } } ⋆ R)
                      m2 := by
                    have hs2_eta : { s2 with core := { s2.core with arena := ar1 } } = s2 :=
                      congrArg (fun a => { s2 with core := { s2.core with arena := a } })
                        har2_eq.symm
                    rw [hs2_eta]; exact hm2
                  exact hL2 (2#32, 1#32, 1#32, 0#32, ()) m2
                    ⟨2, 1, 1, ar1, orig0, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩,
                      fun h => absurd h (by omega), hinv0, hm0⟩
                · rintro J2 ⟨i_v, nsz_v, bp_v, bl_v, ⟨⟩⟩ m2'
                    ⟨i_nat, nsz, bp, ar_cur, origMap, rfl, rfl, rfl, hbp1, hbp2, hinv, hm2'⟩ hL2
                  have hinv_cp := hinv
                  obtain ⟨har_c, _, hi2, hile, hns1, _, _, _, _, _, _, _, hout⟩ := hinv
                  have hnsz_lt_i : nsz < i_nat ∨ (i_nat = 2 ∧ nsz = 1) := by
                    have := otfsActCnt_le s.core cref.toNat i_nat; omega
                  have hi_32 : (BitVec.ofNat 32 i_nat).toNat = i_nat := bv32_ofNat_toNat (by omega)
                  have hns_32 : (BitVec.ofNat 32 nsz).toNat = nsz := bv32_ofNat_toNat (by omega)
                  have hold_32 : (BitVec.ofNat 32 old_sz).toNat = old_sz :=
                    bv32_ofNat_toNat (by omega)
                  have hbp_le : bp ≤ nsz := by
                    rcases Nat.eq_or_lt_of_le hns1 with rfl | hgt
                    · exact (hbp1 rfl).1 ▸ Nat.le_refl 1
                    · exact Nat.le_of_lt (hbp2 hgt).2
                  have hbp_ge1 : 1 ≤ bp := by
                    rcases Nat.eq_or_lt_of_le hns1 with rfl | hgt
                    · exact (hbp1 rfl).1 ▸ Nat.le_refl 1
                    · exact (hbp2 hgt).1
                  have hbp_32 : (BitVec.ofNat 32 bp).toNat = bp := bv32_ofNat_toNat (by omega)
                  c0_hstraight
                  c0_hstep_np
                  · have hilt : i_nat < old_sz := by
                      have hc' : (BitVec.ofNat 32 i_nat).toNat <
                          (BitVec.ofNat 32 old_sz).toNat := by c0_bound
                      rwa [hi_32, hold_32] at hc'
                    have hnsz_lt_i' : nsz < i_nat := by omega
                    obtain ⟨hz_idx, hidx_bd⟩ := s13_otfs_ar_idx3_lt_len hcap har_c h3o hilt
                    have har_bd : cref.toNat + 3 + i_nat < s.core.arena.length := by
                      rw [har_len]; omega
                    let idx := (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i_nat).setWidth 64).toNat
                    have hot_c_eq :
                        ar_cur[idx]'hidx_bd = s.core.arena[cref.toNat + 3 + i_nat]'har_bd := by
                      dsimp only [idx]
                      rw [← Option.some_inj, ← List.getElem?_eq_getElem har_bd,
                        ← List.getElem?_eq_getElem hidx_bd, hz_idx, hout _ (Or.inr (by omega))]
                      dsimp only [ar1]
                      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                    have hv_bd : (s.core.arena[cref.toNat + 3 + i_nat]?.getD 0#32).toNat / 2 <
                        s.core.lvl.length := by
                      have := (hlits_all i_nat hilt).1; rw [hlvl_len]; omega
                    have hlvl_bd : (BitVec.setWidth 64 ((ar_cur[idx]'hidx_bd) >>> 1#32)).toNat <
                        s2.core.lvl.length := by
                      rw [otfs_bv32_lshr1_zext_toNat, hot_c_eq, hlvl2_eq]
                      rw [List.getElem?_eq_getElem har_bd, Option.getD_some] at hv_bd; exact hv_bd
                    have hlvl_bd' : (ar_cur[idx]'hidx_bd).toNat / 2 < s2.core.lvl.length := by
                      rw [hot_c_eq, hlvl2_eq]
                      rw [List.getElem?_eq_getElem har_bd, Option.getD_some] at hv_bd; exact hv_bd
                    have hi1_32 : BitVec.ofNat 32 i_nat + 1 = BitVec.ofNat 32 (i_nat + 1) :=
                      otfs_bv32_ofNat_add1 i_nat
                    c0_hstraight
                    refine wp_join_group (ts := [i32, i32, i32])
                      (fun (nsz_next, bp_next, bl_next, ()) m3 =>
                        ∃ nsz' bp' ar' origMap',
                          nsz_next = BitVec.ofNat 32 nsz' ∧ bp_next = BitVec.ofNat 32 bp' ∧
                          (nsz' = 1 → bp' = 1 ∧ bl_next = 0#32) ∧
                          (2 ≤ nsz' → 1 ≤ bp' ∧ bp' < nsz') ∧
                          S13OtfsShrinkInv c s ar1 cref l0 uip old_sz
                            (old_sz - (i_nat + 1)) (i_nat + 1) nsz' ar' origMap' ∧
                          (FullMem c { s2 with core := { s2.core with arena := ar' } } ⋆ R) m3)
                      ?_ ?_
                    · rintro J3 ⟨nsz_next, bp_next, bl_next, ⟨⟩⟩ m3
                        ⟨nsz', bp', ar', origMap', hns', hbp', h1', h2', hinv', hm3⟩
                      c0_hstraight
                      exact hL2 (_, _, _, _, ()) m3 (by
                        dsimp only; rw [hi1_32, bv32_ofNat_toNat (by omega), hi_32]; omega)
                        ⟨i_nat + 1, nsz', bp', ar', origMap', hi1_32, hns', hbp', h1', h2',
                          hinv', hm3⟩
                    · intro J3 hJ3; c0_hstraight; c0_hstep_np
                      · have hhc : (cref.toNat + 3 + i_nat % 2 ^ 32) % 2 ^ 64 = idx := by
                          dsimp only [idx]
                          rw [hz_idx, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                        have hpos0 : (0#32 : BitVec 32).toNat <
                            (s2.core.lvl[(ar_cur[idx]'hidx_bd).toNat / 2]'hlvl_bd').toNat := by
                          rw [otfs_lvl_idx_eq _ hidx_bd _ hlvl_bd' hhc] at hc; exact hc
                        have hlv_pos := s13_otfs_p2_lv_pos har_bd hv_bd hlvl2_eq hot_c_eq hpos0
                        obtain ⟨hz_ns, hns_bd⟩ :=
                          s13_otfs_ar_idx3_lt_len hcap har_c h3o (j := nsz) (by omega)
                        let idx_ns :=
                          (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 nsz).setWidth 64).toNat
                        have har_set_eq : ar_cur.set idx_ns (ar_cur[idx]'hidx_bd) =
                            ar_cur.set (cref.toNat + 3 + nsz)
                              (s.core.arena[cref.toNat + 3 + i_nat]'har_bd) := by
                          dsimp only [idx_ns]; rw [hz_ns, hot_c_eq]
                        have hns1_32 : BitVec.ofNat 32 nsz + 1 = BitVec.ofNat 32 (nsz + 1) :=
                          otfs_bv32_ofNat_add1 nsz
                        have hstep := s13_otfs_shrink_loop_step har_len hinv_cp hilt h3o hlv_pos
                        c0_hstraight
                        refine wp_join_group (ts := [i32, i32])
                          (fun (bp_next, bl_next, ()) m3 =>
                            ∃ bp', bp_next = BitVec.ofNat 32 bp' ∧ 1 ≤ bp' ∧ bp' < nsz + 1 ∧
                              (FullMem c { s2 with core := { s2.core with
                                arena := ar_cur.set (cref.toNat + 3 + nsz)
                                  (s.core.arena[cref.toNat + 3 + i_nat]'har_bd) } } ⋆ R) m3)
                          ?_ ?_
                        · rintro J4 ⟨bp_next, bl_next, ⟨⟩⟩ m3 ⟨bp', hbp', hge1', hlt', hm3⟩
                          c0_hstraight
                          exact hJ3 (_, _, _, ()) m3
                            ⟨nsz + 1, bp', _, origMap ++ [i_nat], hns1_32, hbp',
                              fun h => absurd h (by omega), fun _ => ⟨hge1', hlt'⟩, hstep, hm3⟩
                        · intro J4 hJ4; c0_hstraight; c0_hstep_np
                          · c0_hstraight
                            exact hJ4 (_, _, ()) _
                              ⟨nsz, rfl, hns1, Nat.lt_succ_self _, by rw [← har_set_eq]; assumption⟩
                          · rcases Nat.eq_or_lt_of_le hns1 with rfl | hgt
                            · exfalso; obtain ⟨_, rfl⟩ := hbp1 rfl
                              have hno : ¬ (0#32 : BitVec 32).toNat <
                                  (s2.core.lvl[(ar_cur[idx]'hidx_bd).toNat / 2]'hlvl_bd').toNat :=
                                by rw [otfs_lvl_idx_eq _ hidx_bd _ hlvl_bd' hhc] at hc; exact hc
                              exact hno hpos0
                            · c0_hstraight
                              exact hJ4 (_, _, ()) _ ⟨bp, rfl, (hbp2 hgt).1,
                                Nat.lt_succ_of_lt (hbp2 hgt).2, by rw [← har_set_eq]; assumption⟩
                      · have hhc : (cref.toNat + 3 + i_nat % 2 ^ 32) % 2 ^ 64 = idx := by
                          dsimp only [idx]
                          rw [hz_idx, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                        have hzero0 : ¬ (0#32 : BitVec 32).toNat <
                            (s2.core.lvl[(ar_cur[idx]'hidx_bd).toNat / 2]'hlvl_bd').toNat := by
                          rw [otfs_lvl_idx_eq _ hidx_bd _ hlvl_bd' hhc] at hc; exact hc
                        have hinv_skip := s13_otfs_p2_skip_inv hinv_cp hilt har_bd hv_bd hlvl2_eq
                          hot_c_eq hzero0
                        c0_hstraight
                        exact hJ3 (_, _, _, ()) m2'
                          ⟨nsz, bp, ar_cur, origMap, rfl, rfl, hbp1, hbp2, hinv_skip, hm2'⟩
                  · have heq_old : i_nat = old_sz := by
                      have hc' : ¬ (BitVec.ofNat 32 i_nat).toNat <
                          (BitVec.ofNat 32 old_sz).toNat := by c0_bound
                      rw [hi_32, hold_32] at hc'; omega
                    subst heq_old
                    dsimp only [ar1] at hinv_cp
                    rw [Nat.sub_self] at hinv_cp
                    obtain ⟨har_c, _, _, _, _, hnsz_act, hlm, hpw, hlt_m, h01, hcov, hmapeq,
                      hout_cur⟩ := hinv_cp
                    have h3_nsz : 3 ≤ nsz := by omega
                    have hnsz_lt : nsz < old_sz := by omega
                    obtain ⟨hbp_ge1', hbp_lt'⟩ := hbp2 (by omega)
                    obtain ⟨hhdr_cur, har1_2', har1_s2'⟩ :=
                      s13_otfs_hdr_prep har_len h3o rfl har2_eq hout_cur
                    refine s13_otfs_hdr_wp (R := R) (_l0 := l0) hs2_len hm2' har_len har_c hcap
                      h3o h4_old h3_nsz hnsz_lt (by rw [hcv2_eq]; exact huip_lt) hlits_all hcv2_eq
                      hmapeq (fun k hk => by
                        rw [List.getElem?_eq_getElem (by rw [hlm]; exact hk), Option.getD_some]
                        exact hlt_m _ (List.getElem_mem _))
                      hout_cur har1_2' har1_s2' hhdr_cur _ (fun ml3 hpost_hdr => ?_)
                    obtain ⟨s3, _, _, ⟨ar3, fl3, hs3_eq⟩, hm3', hlen3, hw3, hnd3, hrefs3, _, hsz3,
                      hng3, _, hsub3⟩ :=
                      s13_otfs_shrink_ok_of_hdrPost hlen hw hnd hs2_len hw2 hnd2 hcv2_eq
                        (by rw [hs2_c]) (by rw [hs2_c]) hlvl2_eq (by rw [hs2_c]) (by rw [hs2_c])
                        hcref hng (hrefs2 ▸ hcref) hng2 rfl
                        (by change fullArenaClauseSizeCore s2.core cref.toNat =
                              fullArenaClauseSizeCore s.core cref.toNat
                            unfold fullArenaClauseSizeCore; rw [hs2_c]; dsimp only [ar1]
                            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
                        hiu_cut hiu_te ht_u hr_u hlu_eq hent_orig h3o h3_nsz hnsz_lt hlm hpw
                        hlt_m h01 hcov hpost_hdr
                    have hcref3 : cref.toNat ∈ fullArenaClauseRefs s3 := by
                      change cref.toNat ∈ fullArenaClauseRefsCore s3.core; rw [hrefs3]
                      change cref.toNat ∈ fullArenaClauseRefs s2; rw [hrefs2]; exact hcref
                    refine s13_otfs_swap_wp hlen3 hw3 hnd3 hm3' hcap hcref3 hng3 hbp_ge1'
                      (by change bp < fullArenaClauseSizeCore s3.core cref.toNat
                          rw [hsz3]; exact hbp_lt')
                      _ (fun s4 m4 ⟨ar4, hs4_eq⟩ hlen4 hw4 hnd4 hrefs4 hng4 hperm4 hm4 => ?_)
                    have hl0_4 : l0.toNat < 2 * s4.core.cur_vars := by
                      rw [hs4_eq, hs3_eq, hs2_c]; exact hl0_bd.1
                    have hdm4 : s4.core.dense_mode = 0#64 := by
                      rw [hs4_eq, hs3_eq, hs2_c]; exact hdm
                    have hcref4 : cref.toNat ∈ fullArenaClauseRefs s4 := by
                      rw [hrefs4]; exact hcref3
                    refine s13_otfs_loop4_wp hlen4 hw4 hnd4 hdm4 hm4 hcap hcref4 hng4 hl0_4 ?_
                    intro wstk' otfs' m5 s5 hlen5 hw5 hnd5 hrefs5 hng5 hlits5 hm5
                    exact s13_otfs_loop2_post_fin hlen hw hcref hng hiu_cut hiu_te ht_u hr_u
                      hs2_c hs2_sc hrefs2 hs3_eq hrefs3 hsub3 hs4_eq hrefs4 hperm4 rfl
                      hlen5 hw5 hnd5 hrefs5 hng5 hlits5 hm5 hPost
              · exact absurd hc (by decide)
            · have hok1f : ok_p = false := Bool.eq_false_iff.mpr hok1
              subst hok1f; obtain ⟨hother_l, _⟩ := hok1F rfl
              have hmw1 : ModeWatchesInv F_cur s1.core := by
                refine fullWstackDefrag_preserves_modeWatchesInv hmw_d hlay1 rfl rfl
                  (fun _ h => by simpa only [fullArenaClauseRefsCore, s1] using h) (fun l hl => ?_)
                by_cases hll : l = l1.toNat
                · subst hll; simpa only [fullWatchSize, fullWatchOff, fullWatchSizeCore,
                    fullWatchOffCore, s1] using hother_l hl
                · simpa only [fullWatchSize, fullWatchOff, fullWatchSizeCore, fullWatchOffCore,
                    s1] using hother1 l hl hll
              c0_hsteps_nogrp
              exact s13_otfs_oom_hpost hw hnd hiu_cut hs1_len hs1_c hs1_sc hmw1 (by assumption)
                hPost
          · intro Js_e hJs_e
            refine otfs_wstack_ensure2_ret_false_wp hDefrag hlen hdm hw.watches hm ?_ hJs_e
            intro s_i wv_i ws_i wl_i wu_i wso_i ml_o hsi_c hsi_sc hsi_len hmw_i hml_o
            exact s13_otfs_oom_hpost hw hnd hiu_cut hsi_len hsi_c hsi_sc hmw_i hml_o hPost
  · intro Js hJs
    have hbd3 : cref.toNat + 3 < s.core.arena.length := by rw [har_len]; omega
    have hbd4 : cref.toNat + 4 < s.core.arena.length := by rw [har_len]; omega
    have h3m : (cref.toNat + (3 : BitVec 64).toNat) % 2 ^ 64 = cref.toNat + 3 := by
      rw [show (3 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
    have h4m : (cref.toNat + (3 : BitVec 64).toNat + (1 : BitVec 64).toNat) % 2 ^ 64 =
        cref.toNat + 4 := by
      rw [show (3 : BitVec 64).toNat = 3 from rfl, show (1 : BitVec 64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by omega)]
    c0_hstraight; c0_hstep_np
    · c0_hstraight
      refine hJs _ m ⟨rfl, Or.inr ⟨(getElem_eq_of_idx (hj := hbd4) hcr4_z).trans
        (by rw [List.getElem?_eq_getElem hbd4, Option.getD_some]), ?_⟩⟩
      rw [List.getElem?_eq_getElem hbd3, Option.getD_some,
        ← getElem_eq_of_idx (hj := hbd3) h3m]; exact hc
    · clear hc; c0_hstraight; c0_hstep_np
      · c0_hstraight; exact hret_false_id
      · c0_hstraight
        refine hJs _ m ⟨rfl, Or.inl ⟨(getElem_eq_of_idx (hj := hbd3) hcr3_z).trans
          (by rw [List.getElem?_eq_getElem hbd3, Option.getD_some]), ?_⟩⟩
        rw [List.getElem?_eq_getElem hbd4, Option.getD_some,
          ← getElem_eq_of_idx (hj := hbd4) h4m]; exact hc

end LeanQbe.T.Examples.Kissat.Proof.Deduce
