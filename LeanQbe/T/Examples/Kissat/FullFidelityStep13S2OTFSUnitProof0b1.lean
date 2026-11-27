/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2OTFSUnitProof0b0

/-!
# Kissat Fidelity Step 13 `full_otfs_large` Header & Post-`J3` WP Proofs (`0b1`)

Proves the modular header/post-shrink sub-theorems for `full_otfs_large_step13_wp` (all `<= 230`
lines, `<= 100` cols):
1. `s13_otfs_j4_swap_state` & `s13_otfs_j4_swap_wp`: post-shrink `hp != 1` swap.
2. `s13_otfs_post_j3_wp`: post-`J3` (`shrink_ok_of_hdrPost`, `j4_swap`, `m5_loop4_sz_wp`, `fin`).
3. `s13_otfs_j3_hdr_wp`: Step-13 `PH_RED` glue tightening / `!PH_RED` `flags |= 24u` + `PH_SHRK`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S2

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM5Otfs
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open Kraken.Bedrock2.Test

theorem s13_otfs_j4_swap_state {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {idx_u nsz old_sz hp_n : Nat} {s s3 : FullState} {cref l0 uip : BitVec 32}
    {ar_sw : List (BitVec 32)} {R : Mem 64 → Prop} {ml4 : Mem 64}
    (hlen3 : s3.LengthsOk c) (hw3 : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u s3.core)
    (hnd3 : FullArenaVarsNodup s3) (hcref3 : cref.toNat ∈ fullArenaClauseRefs s3)
    (hsz_3 : fullArenaClauseSize s3 cref.toNat = nsz)
    (hng_3 : fullArenaClauseGarb s3 cref.toNat = false)
    (har3_l0 : s3.core.arena[cref.toNat + 3]? = some l0)
    (hlits_3 : ∀ l ∈ fullArenaClauseLits s3 cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat)
    (har3_s3_l : s3.core.arena.length = c.arena_cap) (_hnsz_lt : nsz < old_sz)
    (hcr4_z : (cref.setWidth 64 + 4#64).toNat = cref.toNat + 4) (hhp1 : 1 ≤ hp_n)
    (hhp_lt : hp_n < nsz) (h_hp_z : (cref.setWidth 64 + 3#64 +
      (BitVec.ofNat 32 hp_n).setWidth 64).toNat = cref.toNat + 3 + hp_n)
    (hbd_hp : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 hp_n).setWidth 64).toNat <
      s3.core.arena.length) (hbd_4 : (cref.setWidth 64 + 4#64).toNat < s3.core.arena.length)
    (har_sw : ar_sw = (s3.core.arena.set (cref.setWidth 64 + 4#64).toNat
      (s3.core.arena[(cref.setWidth 64 + 3#64 +
        (BitVec.ofNat 32 hp_n).setWidth 64).toNat]'hbd_hp)).set (cref.setWidth 64 + 3#64 +
        (BitVec.ofNat 32 hp_n).setWidth 64).toNat
        (s3.core.arena[(cref.setWidth 64 + 4#64).toNat]'hbd_4))
    (hm_sw : (FullMem c { s3 with core := { s3.core with arena := ar_sw } } ⋆ R) ml4) :
    ∃ ar4 : List (BitVec 32),
      (FullMem c { s3 with core := { s3.core with arena := ar4 } } ⋆ R) ml4 ∧
      ar4.length = c.arena_cap ∧
      FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u { s3.core with arena := ar4 } ∧
      FullArenaVarsNodup { s3 with core := { s3.core with arena := ar4 } } ∧
      fullArenaClauseRefsCore { s3.core with arena := ar4 } = fullArenaClauseRefsCore s3.core ∧
      fullArenaClauseSizeCore { s3.core with arena := ar4 } cref.toNat = nsz ∧
      fullArenaClauseGarbCore { s3.core with arena := ar4 } cref.toNat = false ∧
      ar4[cref.toNat + 3]? = some l0 ∧
      (∀ l ∈ fullArenaClauseLitsCore { s3.core with arena := ar4 } cref.toNat,
        l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat) := by
  have h4_s3 : cref.toNat + 4 < s3.core.arena.length := by rw [har3_s3_l]; omega
  have hhp_s3 : cref.toNat + 3 + hp_n < s3.core.arena.length := by rw [har3_s3_l]; omega
  have hget4 : s3.core.arena[(cref.setWidth 64 + 4#64).toNat]'hbd_4 =
      s3.core.arena[cref.toNat + 4]?.getD 0#32 := by
    rw [m5_list_getElem_of_idx (hj := h4_s3) hcr4_z, List.getElem?_eq_getElem h4_s3,
      Option.getD_some]
  have hget_hp : s3.core.arena[(cref.setWidth 64 + 3#64 +
      (BitVec.ofNat 32 hp_n).setWidth 64).toNat]'hbd_hp =
      s3.core.arena[cref.toNat + 3 + hp_n]?.getD 0#32 := by
    rw [m5_list_getElem_of_idx (hj := hhp_s3) h_hp_z, List.getElem?_eq_getElem hhp_s3,
      Option.getD_some]
  let ar4 := (s3.core.arena.set (cref.toNat + 4) (s3.core.arena[cref.toNat + 3 + hp_n]?.getD
    0#32)).set (cref.toNat + 3 + hp_n) (s3.core.arena[cref.toNat + 4]?.getD 0#32)
  have hsw_eq : ar_sw = ar4 := by
    rw [har_sw]; dsimp only [ar4]; rw [hget4, hget_hp, hcr4_z, h_hp_z]
  let s4 : FullState := { s3 with core := { s3.core with arena := ar4 } }
  obtain ⟨hw4, hrefs4, hsz4, hng4, hperm4, hother4⟩ :=
    fa_swapCl_preserves_fullWitnessCut hlen3.core_ok hw3 hcref3 (i := 1) (j := hp_n)
      (by rw [show fullArenaClauseSizeCore s3.core cref.toNat = nsz from hsz_3]; omega)
      (by rw [show fullArenaClauseSizeCore s3.core cref.toNat = nsz from hsz_3]; exact hhp_lt)
  have hnd4 : FullArenaVarsNodup s4 := fun r hr hngr => by
    change r ∈ fullArenaClauseRefsCore s4.core at hr; rw [hrefs4] at hr
    by_cases hrc : r = cref.toNat
    · subst r; exact (hperm4.map (· / 2)).nodup_iff.mpr (hnd3 cref.toNat hr hng_3)
    · have ho := hother4 r hr hrc; change ((fullArenaClauseLitsCore s4.core r).map (· / 2)).Nodup
      rw [ho.2.2]; exact hnd3 r hr (by
        change fullArenaClauseGarbCore s3.core r = false; rw [← ho.2.1]; exact hngr)
  exact ⟨ar4, m5_fullMem_of_eq hm_sw (by rw [hsw_eq]) rfl, by simp [ar4, har3_s3_l], hw4, hnd4,
    hrefs4, hsz4.trans hsz_3, hng4.trans hng_3,
    by dsimp only [ar4]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
       exact har3_l0, fun l hl => hlits_3 l (hperm4.mem_iff.mp hl)⟩

theorem s13_otfs_j4_swap_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {idx_u nsz old_sz hp_n : Nat}
    {s s3 : FullState} {cref l0 uip : BitVec 32} {R : Mem 64 → Prop} {ml3 : Mem 64}
    {J4 : Cont []}
    (hlen3 : s3.LengthsOk c)
    (hw3 : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u s3.core)
    (hnd3 : FullArenaVarsNodup s3) (hcref3 : cref.toNat ∈ fullArenaClauseRefsCore s3.core)
    (hsz_3 : fullArenaClauseSizeCore s3.core cref.toNat = nsz)
    (hng_3 : fullArenaClauseGarbCore s3.core cref.toNat = false)
    (har3_l0 : s3.core.arena[cref.toNat + 3]? = some l0)
    (hlits_3 : ∀ l ∈ fullArenaClauseLitsCore s3.core cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat)
    (har3_s3_l : s3.core.arena.length = c.arena_cap)
    (_hcap31 : c.arena_cap < 2 ^ 31 - 1) (_har_le : s.core.arena_len ≤ c.arena_cap)
    (_hold_bd : cref.toNat + 3 + old_sz ≤ s.core.arena_len)
    (hnsz_lt : nsz < old_sz) (hcr4_z : (cref.setWidth 64 + 4#64).toNat = cref.toNat + 4)
    (hcb1_eq : cref.setWidth 64 + 3#64 + 1#64 = cref.setWidth 64 + 4#64)
    (hhp1 : 1 ≤ hp_n) (hhp_lt : hp_n < nsz) (hm3' : (FullMem c s3 ⋆ R) ml3)
    (hJ4 : ∀ xs ml4, (∃ ar4 : List (BitVec 32),
      (FullMem c { s3 with core := { s3.core with arena := ar4 } } ⋆ R) ml4 ∧
      ar4.length = c.arena_cap ∧
      FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u { s3.core with arena := ar4 } ∧
      FullArenaVarsNodup { s3 with core := { s3.core with arena := ar4 } } ∧
      fullArenaClauseRefsCore { s3.core with arena := ar4 } = fullArenaClauseRefsCore s3.core ∧
      fullArenaClauseSizeCore { s3.core with arena := ar4 } cref.toNat = nsz ∧
      fullArenaClauseGarbCore { s3.core with arena := ar4 } cref.toNat = false ∧
      ar4[cref.toNat + 3]? = some l0 ∧
      (∀ l ∈ fullArenaClauseLitsCore { s3.core with arena := ar4 } cref.toNat,
        l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat)) → J4 xs ml4) :
    wp Γ Q X
      (Expr.let_ (Op.mk (.cmp .ne (.bits 32) .bool rfl)
          (Arg.var (BitVec.ofNat 32 hp_n), Arg.imm 1, ())) fun p =>
        Expr.jnz (Arg.var p.fst)
          (Expr.let_ (Op.mk (.add (.bits 64))
              (Arg.var (cref.setWidth 64 + 3#64), Arg.imm 1, ())) fun p =>
           Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
           Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
           Expr.load i32 (Arg.var p.fst) fun ld_8 =>
           Expr.let_ (Op.mk (.add (.bits 64))
             (Arg.var (cref.setWidth 64 + 3#64), Arg.imm 1, ())) fun p =>
           Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
           Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
           Expr.let_ (Op.mk (.zext 32 64) (Arg.var (BitVec.ofNat 32 hp_n), ())) fun p_39 =>
           Expr.let_ (Op.mk (.add (.bits 64))
             (Arg.var (cref.setWidth 64 + 3#64), Arg.var p_39.fst, ())) fun p_40 =>
           Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p_40.fst, Arg.imm 4, ())) fun p_41 =>
           Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pArena, Arg.var p_41.fst, ())) fun p_42 =>
           Expr.load i32 (Arg.var p_42.fst) fun ld_9 =>
           Expr.store (Arg.var ld_9) (Arg.var p.fst)
             (Expr.let_ (Op.mk (.zext 32 64) (Arg.var (BitVec.ofNat 32 hp_n), ())) fun p =>
              Expr.let_ (Op.mk (.add (.bits 64))
                (Arg.var (cref.setWidth 64 + 3#64), Arg.var p.fst, ())) fun p =>
              Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
              Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
              Expr.store (Arg.var ld_8) (Arg.var p.fst) (Expr.jump J4 ())))
          (Expr.jump J4 ())) ml3 := by
  have h_hp_z := m5_otfs_bv_idx3_64 cref hp_n (by omega) (by omega)
  have hbd_hp : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 hp_n).setWidth 64).toNat <
      s3.core.arena.length := by rw [h_hp_z, har3_s3_l]; omega
  have hbd_4 : (cref.setWidth 64 + 4#64).toNat < s3.core.arena.length := by
    rw [hcr4_z, har3_s3_l]; omega
  have hbd_cb1 : (BitVec.setWidth 64 cref + 3 + 1).toNat < s3.core.arena.length := by
    rw [show (3 : BitVec 64) = 3#64 from rfl, show (1 : BitVec 64) = 1#64 from rfl, hcb1_eq]
    exact hbd_4
  have hbd_hp_st : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 hp_n).setWidth 64).toNat <
      (s3.core.arena.set (BitVec.setWidth 64 cref + 3 + 1).toNat
        (s3.core.arena[(cref.setWidth 64 + 3#64 +
          (BitVec.ofNat 32 hp_n).setWidth 64).toNat]'hbd_hp)).length := by
    rw [List.length_set]; exact hbd_hp
  fa_fast_steps
  · let ar_sw_raw :=
      List.set
        (s3.core.arena.set (BitVec.setWidth 64 cref + 3 + 1).toNat
          (s3.core.arena[(cref.setWidth 64 + 3#64 +
            (BitVec.ofNat 32 hp_n).setWidth 64).toNat]'hbd_hp))
        (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 hp_n).setWidth 64).toNat
        (s3.core.arena[(BitVec.setWidth 64 cref + 3 + 1).toNat]'hbd_cb1)
    let ar_sw :=
      List.set
        (s3.core.arena.set (cref.setWidth 64 + 4#64).toNat
          (s3.core.arena[(cref.setWidth 64 + 3#64 +
            (BitVec.ofNat 32 hp_n).setWidth 64).toNat]'hbd_hp))
        (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 hp_n).setWidth 64).toNat
        (s3.core.arena[(cref.setWidth 64 + 4#64).toNat]'hbd_4)
    have har_sw_eq : ar_sw_raw = ar_sw := by
      dsimp only [ar_sw_raw, ar_sw]
      have h31 : (BitVec.setWidth 64 cref + 3 + 1 : BitVec 64) = cref.setWidth 64 + 4#64 := hcb1_eq
      simp only [h31]
    have hm_sw' : (FullMem c { s3 with core := { s3.core with arena := ar_sw } } ⋆ R) _ :=
      m5_fullMem_of_eq (s1 := { s3 with core := { s3.core with arena := ar_sw_raw } })
        (by assumption) (congrArg (fun a => { s3.core with arena := a }) har_sw_eq) rfl
    exact hJ4 () _ (s13_otfs_j4_swap_state hlen3 hw3 hnd3 hcref3 hsz_3 hng_3
      har3_l0 hlits_3 har3_s3_l hnsz_lt hcr4_z hhp1 hhp_lt h_hp_z hbd_hp hbd_4 rfl hm_sw')
  · exact hJ4 () _ ⟨s3.core.arena,
      m5_fullMem_of_eq hm3' (by rcases s3 with ⟨⟨⟩, _⟩; rfl) rfl,
      har3_s3_l, hw3, hnd3, rfl, hsz_3, hng_3, har3_l0, hlits_3⟩

theorem s13_otfs_post_j3_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut idx_u nsz old_sz hp_n : Nat}
    {s s2 : FullState} {ar1 : List (BitVec 32)} {ws2 wso_p : List (BitVec 32)}
    {cref l0 uip : BitVec 32} {origMap : List Nat} {R : Mem 64 → Prop} {ml3 : Mem 64}
    (hlen : s.LengthsOk c) (hw : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut s.core)
    (hnd : FullArenaVarsNodup s) (hlen2 : s2.LengthsOk c)
    (hw2 : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut s2.core)
    (hnd2 : FullArenaVarsNodup s2) (hdm : s.core.dense_mode = 0#64)
    (hsp_oom : s.core.oom = s2.core.oom) (_hws2 : s2.core.wstk = ws2)
    (hs2_base : s2.core =
      { s.core with arena := ar1, wvec := s2.core.wvec, wstk := ws2,
                    wlen := s2.core.wlen, wusable := s2.core.wusable })
    (hs2_sc : s2.scratch = { s.scratch with wsort := wso_p })
    (hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref.toNat = false)
    (hcref2 : cref.toNat ∈ fullArenaClauseRefs s2)
    (hng2 : fullArenaClauseGarb s2 cref.toNat = false)
    (hsz_orig : fullArenaClauseSize s cref.toNat = old_sz)
    (hsz2 : fullArenaClauseSize s2 cref.toNat = old_sz)
    (hiu_cut : idx_u < cut) (hiu_te : idx_u < s.core.trail_end)
    (ht_u : (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat)
    (hr_u : s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref)
    (hlev_u : (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s.core.cur_level)
    (hent_f : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((fullArenaClauseLits s cref.toNat).filter fun l =>
        decide (l ≠ uip.toNat ∧ (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∨
          l = (s.core.arena[cref.toNat + 3]?.getD 0#32).toNat ∨
          l = (s.core.arena[cref.toNat + 4]?.getD 0#32).toNat)))))
    (hcap31 : c.arena_cap < 2 ^ 31 - 1) (h2cv_lt : 2 * s.core.cur_vars < 2 ^ 31 - 1)
    (hl0_lt : l0.toNat < 2 * s.core.cur_vars) (hcr_lt31 : cref.toNat < 0x80000000)
    (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap)
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < old_sz) (hhp1 : 1 ≤ hp_n) (hhp_lt : hp_n < nsz)
    (hcr4_z : (cref.setWidth 64 + 4#64).toNat = cref.toNat + 4)
    (hcb1_eq : cref.setWidth 64 + 3#64 + 1#64 = cref.setWidth 64 + 4#64)
    (hlen_map : origMap.length = nsz) (hpw : origMap.Pairwise (· < ·))
    (hlt_map : ∀ p ∈ origMap, p < old_sz)
    (h01 : (l0 = s.core.arena[cref.toNat + 3]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 4]?.getD 0#32 = uip ∧ 0 ∈ origMap ∧ 1 ∉ origMap) ∨
      (l0 = s.core.arena[cref.toNat + 4]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 3]?.getD 0#32 = uip ∧ 1 ∈ origMap ∧ 0 ∉ origMap))
    (hcov : ∀ p, 2 ≤ p → p < old_sz →
      0 < (s.core.lvl[(s.core.arena[cref.toNat + 3 + p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
      p ∈ origMap)
    (hpost3 : S13OtfsHdrPost c s s2 R cref old_sz nsz origMap ml3)
    (hQ : ∀ (ok : Bool) (flags' arena' wvec' wstk' : List (BitVec 32)) (wlen' : Nat)
        (wu' oom' : BitVec 64) (sc' : FullScratch) (m' : Mem 64),
      let s' : FullState :=
        { core := { s.core with flags := flags', arena := arena', wvec := wvec', wstk := wstk',
                                wlen := wlen', wusable := wu', oom := oom' }
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
    wp Γ Q X
      (Expr.group (sig := [[]])
        (fun _J4 => Blocks.cons
          (fun _ =>
            Expr.let_ (Op.mk (.add (.bits 64))
                (Arg.var (cref.setWidth 64 + 3#64), Arg.imm 1, ())) fun p =>
            Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
            Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
            Expr.load i32 (Arg.var p.fst) fun ld =>
            Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.hdr, Arg.imm 104, ())) fun p =>
            Expr.load i64 (Arg.var p.fst) fun ld_1 =>
            Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.hdr, Arg.imm 120, ())) fun p =>
            Expr.load i64 (Arg.var p.fst) fun ld_2 =>
            Expr.group (sig := [[]])
              (fun _Js => Blocks.cons
                (fun _ =>
                  Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.hdr, Arg.imm 960, ())) fun p =>
                  Expr.load i64 (Arg.var p.fst) fun ld =>
                  Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var ld, Arg.imm 1, ())) fun p =>
                  Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.hdr, Arg.imm 960, ())) fun p_1 =>
                  Expr.store (Arg.var p.fst) (Arg.var p_1.fst) (Expr.ret (Arg.imm true, ())))
                Blocks.nil)
              (fun Js =>
                Expr.let_ (Op.mk (.and (.bits 32)) (Arg.var cref, Arg.imm 2147483648, ())) fun p =>
                Expr.let_ (Op.mk (.cmp .eq (.bits 32) .bool rfl) (Arg.var p.fst, Arg.imm 0, ()))
                  fun p =>
                Expr.jnz (Arg.var p.fst)
                  (Expr.let_ (Op.mk (.zext 32 64) (Arg.var l0, ())) fun p =>
                   Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun p_1 =>
                   Expr.let_ (Op.mk (.shl (.bits 64)) (Arg.var p.fst, Arg.var p_1.fst, ())) fun p =>
                   Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                   Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var ld_1, Arg.var p.fst, ())) fun p =>
                   Expr.load i32 (Arg.var p.fst) fun ld_3 =>
                   Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld_3, ())) fun p =>
                   Expr.let_ (Op.mk (.zext 32 64) (Arg.var l0, ())) fun p_1 =>
                   Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun p_2 =>
                   Expr.let_ (Op.mk (.shl (.bits 64)) (Arg.var p_1.fst, Arg.var p_2.fst, ()))
                     fun p_1 =>
                   Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var p_1.fst, Arg.imm 1, ())) fun p_1 =>
                   Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p_1.fst, Arg.imm 4, ())) fun p_1 =>
                   Expr.let_ (Op.mk (.add (.bits 64))
                     (Arg.var ld_1, Arg.var p_1.fst, ())) fun p_1 =>
                   Expr.load i32 (Arg.var p_1.fst) fun ld_4 =>
                   Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld_4, ())) fun p_1 =>
                   Expr.group (sig := [[]])
                     (fun _Js_2 => Blocks.cons (fun _ => Expr.jump Js.fst ()) Blocks.nil)
                     (fun Js_2 =>
                      Expr.let_ (Op.mk (.cmp .uge (.bits 64) .bool rfl)
                        (Arg.var p_1.fst, Arg.imm 2, ())) fun p_60 =>
                      Expr.jnz (Arg.var p_60.fst)
                        (Expr.let_ (Op.mk (.add (.bits 64))
                            (Arg.var p.fst, Arg.var p_1.fst, ())) fun p_61 =>
                         Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var p.fst, Arg.imm 2, ()))
                           fun p_62 =>
                         Expr.group (sig := [[i64]])
                           (fun _Js_b => Blocks.cons (fun _ => Expr.jump Js_2.fst ()) Blocks.nil)
                           (fun Js_b =>
                            Expr.group (sig := [[i64]])
                              (fun Js_1 => Blocks.cons (fun p_63 =>
                                Expr.let_ (Op.mk (.cmp .uge (.bits 64) .bool rfl)
                                  (Arg.var p_63.fst, Arg.var p_62.fst, ())) fun p_64 =>
                                Expr.jnz (Arg.var p_64.fst)
                                  (Expr.let_ (Op.mk (.sub (.bits 64))
                                      (Arg.var p_63.fst, Arg.imm 1, ())) fun p_65 =>
                                   Expr.let_ (Op.mk (.mul (.bits 64))
                                     (Arg.var p_65.fst, Arg.imm 4, ())) fun p_66 =>
                                   Expr.let_ (Op.mk (.add (.bits 64))
                                     (Arg.var ld_2, Arg.var p_66.fst, ())) fun p_67 =>
                                   Expr.load i32 (Arg.var p_67.fst) fun ld_10 =>
                                   Expr.let_ (Op.mk (.cmp .eq (.bits 32) .bool rfl)
                                     (Arg.var ld_10, Arg.var cref, ())) fun p_eq =>
                                   Expr.jnz (Arg.var p_eq.fst)
                                     (Expr.let_ (Op.mk (.sub (.bits 64))
                                         (Arg.var p_63.fst, Arg.imm 2, ())) fun p_a =>
                                      Expr.let_ (Op.mk (.mul (.bits 64))
                                        (Arg.var p_a.fst, Arg.imm 4, ())) fun p_b =>
                                      Expr.let_ (Op.mk (.add (.bits 64))
                                        (Arg.var ld_2, Arg.var p_b.fst, ())) fun p_c =>
                                      Expr.let_ (Op.mk (.and (.bits 32))
                                        (Arg.var ld, Arg.imm 2147483647, ())) fun p_68 =>
                                      Expr.store (Arg.var p_68.fst) (Arg.var p_c.fst)
                                        (Expr.jump Js_b.fst (Arg.var p_63.fst, ())))
                                     (Expr.let_ (Op.mk (.sub (.bits 64))
                                         (Arg.var p_63.fst, Arg.imm 2, ())) fun p_a =>
                                      Expr.let_ (Op.mk (.lshr (.bits 32))
                                        (Arg.var ld_10, Arg.imm 31, ())) fun p_68 =>
                                      Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_68.fst, ()))
                                        fun p_69 =>
                                      Expr.let_ (Op.mk (.add (.bits 64))
                                        (Arg.var p_a.fst, Arg.var p_69.fst, ())) fun p_b =>
                                      Expr.jump Js_1.fst (Arg.var p_b.fst, ())))
                                  (Expr.jump Js_b.fst (Arg.var p_63.fst, ()))) Blocks.nil)
                              (fun Js_l => Expr.jump Js_l.fst (Arg.var p_61.fst, ()))))
                        (Expr.jump Js_2.fst ())))
                  (Expr.jump Js.fst ())))
          Blocks.nil)
        (fun J4 =>
          Expr.let_ (Op.mk (.cmp .ne (.bits 32) .bool rfl)
              (Arg.var (BitVec.ofNat 32 hp_n), Arg.imm 1, ())) fun p =>
            Expr.jnz (Arg.var p.fst)
              (Expr.let_ (Op.mk (.add (.bits 64))
                  (Arg.var (cref.setWidth 64 + 3#64), Arg.imm 1, ())) fun p =>
               Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
               Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
               Expr.load i32 (Arg.var p.fst) fun ld_8 =>
               Expr.let_ (Op.mk (.add (.bits 64))
                 (Arg.var (cref.setWidth 64 + 3#64), Arg.imm 1, ())) fun p =>
               Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
               Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
               Expr.let_ (Op.mk (.zext 32 64) (Arg.var (BitVec.ofNat 32 hp_n), ())) fun p_39 =>
               Expr.let_ (Op.mk (.add (.bits 64))
                 (Arg.var (cref.setWidth 64 + 3#64), Arg.var p_39.fst, ())) fun p_40 =>
               Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p_40.fst, Arg.imm 4, ())) fun p_41 =>
               Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pArena, Arg.var p_41.fst, ()))
                 fun p_42 =>
               Expr.load i32 (Arg.var p_42.fst) fun ld_9 =>
               Expr.store (Arg.var ld_9) (Arg.var p.fst)
                 (Expr.let_ (Op.mk (.zext 32 64) (Arg.var (BitVec.ofNat 32 hp_n), ())) fun p =>
                  Expr.let_ (Op.mk (.add (.bits 64))
                    (Arg.var (cref.setWidth 64 + 3#64), Arg.var p.fst, ())) fun p =>
                  Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                  Expr.let_ (Op.mk (.add (.bits 64))
                    (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
                  Expr.store (Arg.var ld_8) (Arg.var p.fst) (Expr.jump J4.fst ())))
              (Expr.jump J4.fst ()))) ml3 := by
  have har_le := hlen.core_ok.arena_len_le
  have hcv2 : s2.core.cur_vars = s.core.cur_vars := by rw [hs2_base]
  have htrl2 : s2.core.trl = s.core.trl := by rw [hs2_base]
  have hrsns2 : s2.core.rsns = s.core.rsns := by rw [hs2_base]
  have hlvl2 : s2.core.lvl = s.core.lvl := by rw [hs2_base]
  have hte2 : s2.core.trail_end = s.core.trail_end := by rw [hs2_base]
  have hcl2 : s2.core.cur_level = s.core.cur_level := by rw [hs2_base]
  obtain ⟨s3, har3_s3_l, _hfl3_l, ⟨ar3, fl3, hs3_mk⟩, hm3', hlen3, hw3, hnd3, hrefs3, hcref3,
    hsz_3, hng_3, har3_l0, hlits_3⟩ :=
    s13_otfs_shrink_ok_of_hdrPost hlen hw hnd hlen2 hw2 hnd2 hcv2 htrl2 hrsns2 hlvl2 hte2 hcl2
      hcref hng hcref2 hng2 hsz_orig hsz2 hiu_cut hiu_te ht_u hr_u hlev_u hent_f
      h3o hnsz3 hnsz_lt hlen_map hpw hlt_map h01 hcov hpost3
  have hs3_c : s3.core = { s2.core with arena := ar3, flags := fl3 } := by rw [hs3_mk]
  have hs3_sc : s3.scratch = s2.scratch := by rw [hs3_mk]
  have hold_bd : cref.toNat + 3 + old_sz ≤ s.core.arena_len := by
    have := (hw.arena.refs_wf cref.toNat hcref).2.2.1
    have := (hw.arena.refs_wf cref.toNat hcref).2.2.2.1
    change fullArenaClauseSize s cref.toNat = old_sz at hsz_orig
    unfold fullArenaClauseSize at hsz_orig; rw [← hsz_orig]; omega
  have h_hp_bd_pre : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 hp_n).setWidth 64).toNat <
      s3.core.arena.length :=
    (s13_otfs_ar_idx3_lt_len (cref := cref) (old_sz := old_sz) (j := hp_n) hcap31 har3_s3_l
      h3o (Nat.lt_trans hhp_lt hnsz_lt)).2
  refine wp_join_group (ts := []) (fun () ml4 =>
    ∃ ar4 : List (BitVec 32),
      (FullMem c { s3 with core := { s3.core with arena := ar4 } } ⋆ R) ml4 ∧
      ar4.length = c.arena_cap ∧
      FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur idx_u { s3.core with arena := ar4 } ∧
      FullArenaVarsNodup { s3 with core := { s3.core with arena := ar4 } } ∧
      fullArenaClauseRefsCore { s3.core with arena := ar4 } = fullArenaClauseRefsCore s3.core ∧
      fullArenaClauseSizeCore { s3.core with arena := ar4 } cref.toNat = nsz ∧
      fullArenaClauseGarbCore { s3.core with arena := ar4 } cref.toNat = false ∧
      ar4[cref.toNat + 3]? = some l0 ∧
      (∀ l ∈ fullArenaClauseLitsCore { s3.core with arena := ar4 } cref.toNat,
        l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat)) ?_ ?_
  · rintro _ ⟨⟩ ml4 ⟨ar4, hm4, har4_l, hw4, hnd4, hrefs4, hsz4, hng4, har4_l0, hlits4⟩
    obtain ⟨s4, hs4_c, hs4_sc, hm4'⟩ :=
      m5_otfs_opaque_state { s2.core with arena := ar4, flags := fl3 } s3.scratch hm4
        (by dsimp only; rw [hs3_c]) rfl
    clear hm4 hm3'
    have hs4_sc' : s4.scratch = { s.scratch with wsort := wso_p } :=
      hs4_sc.trans (hs3_sc.trans hs2_sc)
    have hcv4 : s4.core.cur_vars = s.core.cur_vars := by rw [hs4_c, hs2_base]
    have h4bd : cref.toNat + 4 < ar4.length := by rw [har4_l]; omega
    obtain ⟨hlen4, hw4', hnd4', hcref4, hng4', hlits4', hnl1_lt5, hdm4, h2cv4, hcr_msb4,
      hrefs4_fin, h4_get, hshl0, h2l1_4, hoff64, hsz64⟩ :=
      s13_otfs_s4_facts hcref hdm hrefs2 hs2_base hs3_c hlen3 hrefs3 hcref3 hs4_c hs4_sc hcv4
        h2cv_lt hl0_lt hcr_lt31 hnsz3 (by omega) h4bd har4_l hcb1_eq hcr4_z hw4 hnd4 hrefs4
        hsz4 hng4 hlits4
    have hl0_lt5 : l0.toNat < 2 * s4.core.cur_vars := by rwa [hcv4]
    have hws4_c : s4.core.wstk = ws2 := by rw [hs4_c, hs2_base]
    have hw4_bd0 : (BitVec.setWidth 64 l0 <<< (1 : Nat)).toNat < s4.core.wvec.length := by
      rw [hshl0, hlen4.core_ok.wvec_len]; have := hlen4.core_ok.cur_vars_le; omega
    have hw4_bd1 : ((BitVec.setWidth 64 l0 <<< (1 : Nat)) + (1 : BitVec 64)).toNat <
        s4.core.wvec.length := by
      rw [h2l1_4, hlen4.core_ok.wvec_len]; have := hlen4.core_ok.cur_vars_le; omega
    have h4_z_bd : (BitVec.setWidth 64 cref + 3 + 1).toNat < s4.core.arena.length := by
      rw [hs4_c, hs2_base]
      have h4n : (BitVec.setWidth 64 cref + 3 + 1 : BitVec 64).toNat = cref.toNat + 4 := by
        rw [show (BitVec.setWidth 64 cref + 3 + 1 : BitVec 64) =
          cref.setWidth 64 + 4#64 from hcb1_eq]
        exact hcr4_z
      rw [h4n, har4_l]; omega
    fa_fast_steps_nogrp
    refine wp_join_group (ts := []) (fun () ml_f =>
      ∃ ws_f : List (BitVec 32),
        (FullMem c { s4 with core := { s4.core with wstk := ws_f } } ⋆ R) ml_f ∧
        ws_f.length = c.wcap ∧ ModeWatchesInv F_cur { s4.core with wstk := ws_f }) ?_ ?_
    · rintro _ ⟨⟩ ml_f ⟨ws_f, hm_f, hws_fl, hmw_f⟩
      fa_fast_steps
      exact s13_otfs_fin_wp hlen hw hcref hng hiu_cut hiu_te ht_u hr_u hsp_oom.symm hs2_base hs4_c
        hs4_sc' hw4' hlen4 hnd4' hrefs4_fin hcref4 hng4' hlits4' hws_fl hmw_f
        (by assumption) hQ
    · intro J_out hJ_out
      fa_fast_steps_nogrp
      · have h4_get_s : ∀ (hbd : (cref.setWidth 64 + 3#64 + 1).toNat < s4.core.arena.length),
            s4.core.arena[(cref.setWidth 64 + 3#64 + 1).toNat]'hbd =
              ar4[cref.toNat + 4]?.getD 0#32 := fun _ => h4_get
        rw [h4_get_s]
        exact m5_loop4_sz_wp hdm4 hw4'.watches hlen4 h2cv4 hl0_lt5 hnl1_lt5 hws4_c hcr_lt31
          hcref4 hoff64 hsz64 hm4' hJ_out
      · exact absurd hcr_msb4 ‹_›
  · intro J4 hJ4
    exact s13_otfs_j4_swap_wp hlen3 hw3 hnd3 hcref3 hsz_3 hng_3 har3_l0 hlits_3 har3_s3_l hcap31
      har_le hold_bd hnsz_lt hcr4_z hcb1_eq hhp1 hhp_lt hm3' hJ4

theorem s13_otfs_j3_hdr_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {s s2 : FullState} {ar1 ar_cur ar_in : List (BitVec 32)}
    {cref uip hdrV oldSzV : BitVec 32} {old_sz nsz : Nat} {origMap : List Nat}
    {R : Mem 64 → Prop} {ml_in : Mem 64} (k_j3 : Expr Val Cont [.bool])
    (har_len : s.core.arena.length = c.arena_cap) (har_c : ar_cur.length = c.arena_cap)
    (hfl_len : s2.core.flags.length = c.max_vars)
    (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap) (hcap31 : c.arena_cap < 2 ^ 31 - 1)
    (h4_old : 4 ≤ old_sz) (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < old_sz)
    (hcr0_z : (cref.setWidth 64).toNat = cref.toNat)
    (hcr1_z : (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1)
    (hcr2_z : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2)
    (hcr3_z : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (hhdr_v : hdrV = fullArenaHdrCore s2.core cref.toNat)
    (hold_v : oldSzV = BitVec.ofNat 32 old_sz)
    (har_in : ar_in = (ar_cur.set (cref.setWidth 64 + 2#64).toNat (BitVec.ofNat 32 nsz)).set
      (cref.setWidth 64 + 1#64).toNat 2#32)
    (h2cv_lt : 2 * s.core.cur_vars < 2 ^ 31 - 1) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hu_lt : uip.toNat < 2 * s.core.cur_vars)
    (hlits_info : ∀ j < old_sz,
      (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ≠ 0xFFFFFFFF#32)
    (hlen_m : origMap.length = nsz)
    (hlt_m : ∀ p ∈ origMap, p < old_sz)
    (hmapeq : ∀ k, k < nsz →
      ar_cur[cref.toNat + 3 + k]? = s.core.arena[cref.toNat + 3 + origMap[k]?.getD 0]?)
    (hout_m : ∀ q, q < cref.toNat + 4 ∨ cref.toNat + 3 + nsz ≤ q → ar_cur[q]? = ar1[q]?)
    (har1_q : ∀ q, 2 ≤ q → ar1[cref.toNat + 3 + q]? = s.core.arena[cref.toNat + 3 + q]?)
    (har1_s2 : ∀ i, i < cref.toNat + 3 ∨ cref.toNat + 5 ≤ i → ar1[i]? = s2.core.arena[i]?)
    (hhdr_eq : ar_cur[cref.toNat]? = some (fullArenaHdrCore s2.core cref.toNat))
    (hm_in : (FullMem c { s2 with core := { s2.core with arena := ar_in } } ⋆ R) ml_in)
    (hk_j3 : ∀ ml3, S13OtfsHdrPost c s s2 R cref old_sz nsz origMap ml3 → wp Γ Q X k_j3 ml3) :
    wp Γ Q X
      (Expr.group (sig := [[i32]])
        (fun _J_hdr1 => Blocks.cons
          (fun hdr_p =>
            Expr.group (sig := [[]])
              (fun _J3_g => Blocks.cons (fun _ => k_j3) Blocks.nil)
              (fun J3_g =>
                Expr.let_ (Op.mk (.and (.bits 32)) (Arg.var hdr_p.fst, Arg.imm 8388608, ()))
                  fun p_38 =>
                Expr.let_ (Op.mk (.cmp .eq (.bits 32) .bool rfl)
                    (Arg.var p_38.fst, Arg.imm 0, ())) fun p_39 =>
                Expr.jnz (Arg.var p_39.fst)
                  (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p =>
                   Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                   Expr.let_ (Op.mk (.add (.bits 64))
                     (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
                   Expr.let_ (Op.mk (.or (.bits 32)) (Arg.var hdr_p.fst, Arg.imm 8388608, ()))
                     fun p_40 =>
                   Expr.store (Arg.var p_40.fst) (Arg.var p.fst)
                     (Expr.let_ (Op.mk (.zext 32 64) (Arg.var oldSzV, ())) fun p =>
                      Expr.let_ (Op.mk (.add (.bits 64))
                        (Arg.var (cref.setWidth 64 + 3#64), Arg.var p.fst, ())) fun p =>
                      Expr.let_ (Op.mk (.sub (.bits 64)) (Arg.var p.fst, Arg.imm 1, ())) fun p =>
                      Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                      Expr.let_ (Op.mk (.add (.bits 64))
                        (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
                      Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p.fst)
                        (Expr.jump J3_g.fst ())))
                  (Expr.jump J3_g.fst ())))
          Blocks.nil)
        (fun J_hdr1 =>
          Expr.let_ (Op.mk (.and (.bits 32)) (Arg.var hdrV, Arg.imm 4194304, ())) fun p =>
          Expr.let_ (Op.mk (.cmp .ne (.bits 32) .bool rfl) (Arg.var p.fst, Arg.imm 0, ())) fun p =>
          Expr.jnz (Arg.var p.fst)
            (Expr.group (sig := [[i32]])
              (fun _J_g => Blocks.cons (fun pg => Expr.jump J_hdr1.fst (Arg.var pg.fst, ()))
                Blocks.nil)
              (fun J_g =>
                Expr.let_ (Op.mk (.and (.bits 32)) (Arg.var hdrV, Arg.imm 524287, ())) fun p =>
                Expr.let_ (Op.mk (.cmp .uge (.bits 32) .bool rfl)
                    (Arg.var p.fst, Arg.var (BitVec.ofNat 32 nsz), ())) fun p =>
                Expr.jnz (Arg.var p.fst)
                  (Expr.let_ (Op.mk (.not (.bits 32)) (Arg.imm 524287, ())) fun p =>
                   Expr.let_ (Op.mk (.and (.bits 32)) (Arg.var hdrV, Arg.var p.fst, ())) fun p =>
                   Expr.let_ (Op.mk (.sub (.bits 32))
                     (Arg.var (BitVec.ofNat 32 nsz), Arg.imm 1, ())) fun p_1 =>
                   Expr.let_ (Op.mk (.or (.bits 32)) (Arg.var p.fst, Arg.var p_1.fst, ())) fun p =>
                   Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p_2 =>
                   Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p_2.fst, Arg.imm 4, ())) fun p_3 =>
                   Expr.let_ (Op.mk (.add (.bits 64))
                     (Arg.var c.pArena, Arg.var p_3.fst, ())) fun p_4 =>
                   Expr.store (Arg.var p.fst) (Arg.var p_4.fst)
                     (Expr.jump J_g.fst (Arg.var p.fst, ())))
                  (Expr.jump J_g.fst (Arg.var hdrV, ()))))
            (Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.hdr, Arg.imm 800, ())) fun p =>
             Expr.load i64 (Arg.var p.fst) fun ld =>
             Expr.let_ (Op.mk (.lshr (.bits 32)) (Arg.var uip, Arg.imm 1, ())) fun p =>
             Expr.let_ (Op.mk (.zext 32 64) (Arg.var p.fst, ())) fun p =>
             Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
             Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var ld, Arg.var p.fst, ())) fun p =>
             Expr.let_ (Op.mk (.lshr (.bits 32)) (Arg.var uip, Arg.imm 1, ())) fun p_1 =>
             Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_1.fst, ())) fun p_2 =>
             Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p_2.fst, Arg.imm 4, ())) fun p_3 =>
             Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var ld, Arg.var p_3.fst, ())) fun p_4 =>
             Expr.load i32 (Arg.var p_4.fst) fun ld_1 =>
             Expr.let_ (Op.mk (.or (.bits 32)) (Arg.var ld_1, Arg.imm 24, ())) fun p_5 =>
             Expr.store (Arg.var p_5.fst) (Arg.var p.fst)
               (Expr.group (sig := [[i32]])
                 (fun J_o => Blocks.cons
                   (fun p_o =>
                     Expr.let_ (Op.mk (.cmp .ult (.bits 32) .bool rfl)
                         (Arg.var p_o.fst, Arg.var (BitVec.ofNat 32 nsz), ())) fun p_6 =>
                     Expr.jnz (Arg.var p_6.fst)
                       (Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_o.fst, ())) fun p_7 =>
                        Expr.let_ (Op.mk (.add (.bits 64))
                          (Arg.var (cref.setWidth 64 + 3#64), Arg.var p_7.fst, ())) fun p_8 =>
                        Expr.let_ (Op.mk (.mul (.bits 64))
                          (Arg.var p_8.fst, Arg.imm 4, ())) fun p_9 =>
                        Expr.let_ (Op.mk (.add (.bits 64))
                          (Arg.var c.pArena, Arg.var p_9.fst, ())) fun p_10 =>
                        Expr.load i32 (Arg.var p_10.fst) fun ld_2 =>
                        Expr.let_ (Op.mk (.lshr (.bits 32)) (Arg.var ld_2, Arg.imm 1, ())) fun pa =>
                        Expr.let_ (Op.mk (.zext 32 64) (Arg.var pa.fst, ())) fun pb =>
                        Expr.let_ (Op.mk (.mul (.bits 64))
                          (Arg.var pb.fst, Arg.imm 4, ())) fun pc =>
                        Expr.let_ (Op.mk (.add (.bits 64))
                          (Arg.var ld, Arg.var pc.fst, ())) fun pd =>
                        Expr.let_ (Op.mk (.lshr (.bits 32)) (Arg.var ld_2, Arg.imm 1, ())) fun pe =>
                        Expr.let_ (Op.mk (.zext 32 64) (Arg.var pe.fst, ())) fun pf =>
                        Expr.let_ (Op.mk (.mul (.bits 64))
                          (Arg.var pf.fst, Arg.imm 4, ())) fun pg =>
                        Expr.let_ (Op.mk (.add (.bits 64))
                          (Arg.var ld, Arg.var pg.fst, ())) fun ph =>
                        Expr.load i32 (Arg.var ph.fst) fun ld_3 =>
                        Expr.let_ (Op.mk (.or (.bits 32)) (Arg.var ld_3, Arg.imm 24, ())) fun pi =>
                        Expr.store (Arg.var pi.fst) (Arg.var pd.fst)
                          (Expr.let_ (Op.mk (.add (.bits 32))
                              (Arg.var p_o.fst, Arg.imm 1, ())) fun pj =>
                           Expr.jump J_o.fst (Arg.var pj.fst, ())))
                       (Expr.jump J_hdr1.fst (Arg.var hdrV, ())))
                   Blocks.nil)
                 (fun J_o => Expr.jump J_o.fst (Arg.imm 0, ())))))) ml_in := by
  subst hhdr_v hold_v
  let hdr0 := fullArenaHdrCore s2.core cref.toNat
  let hdr_gl :=
    if (hdr0 &&& 0x00400000#32) ≠ 0#32 ∧ nsz ≤ (hdr0 &&& 0x7FFFF#32).toNat
    then (hdr0 &&& ~~~0x7FFFF#32) ||| (BitVec.ofNat 32 nsz - 1#32) else hdr0
  let ar_mid :=
    if (hdr0 &&& 0x00400000#32) ≠ 0#32 ∧ nsz ≤ (hdr0 &&& 0x7FFFF#32).toNat
    then ar_in.set cref.toNat hdr_gl else ar_in
  have har_in_l : ar_in.length = c.arena_cap := by simp [har_in, har_c]
  have har_mid_l : ar_mid.length = c.arena_cap := by
    dsimp only [ar_mid]; split <;> simp [har_in_l]
  have hcr_end_z : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 old_sz).setWidth 64 - 1#64).toNat =
      cref.toNat + 3 + old_sz - 1 := by
    have hz : ((BitVec.ofNat 32 old_sz).setWidth 64).toNat = old_sz := by
      rw [zext_toNat _ (by decide), bv32_ofNat_toNat (by omega)]
    rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def, BitVec.toNat_add, hcr3_z, hz, Nat.mod_eq_of_lt (by omega),
        show (1#64).toNat = 1 from rfl]; omega),
      BitVec.toNat_add, hcr3_z, hz, Nat.mod_eq_of_lt (by omega), show (1#64).toNat = 1 from rfl]
  refine wp_join_group (ts := [i32]) (fun (hdr_v, ()) ml_j =>
    ∃ fl3 : List (BitVec 32), hdr_v = hdr_gl ∧ fl3.length = c.max_vars ∧
      (FullMem c { s2 with core := { s2.core with arena := ar_mid, flags := fl3 } } ⋆ R) ml_j)
    ?_ ?_
  · rintro _ ⟨hdr_v, ⟨⟩⟩ ml_j ⟨fl3, rfl, hfl3, hm_j⟩
    have har_c0_st : (cref.setWidth 64).toNat < ar_mid.length := by
      rw [har_mid_l, hcr0_z]; omega
    have har_end_st : (cref.setWidth 64 + 3#64 +
        (BitVec.ofNat 32 old_sz).setWidth 64 - 1#64).toNat <
        (ar_mid.set (cref.setWidth 64).toNat (hdr_gl ||| 0x00800000#32)).length := by
      rw [List.length_set, har_mid_l, hcr_end_z]; omega
    fa_fast_steps_nogrp
    refine wp_join_group (ts := []) (fun () ml3 =>
        S13OtfsHdrPost c s s2 R cref old_sz nsz origMap ml3) ?_ ?_
    · rintro _ ⟨⟩ ml3 hpost3; exact hk_j3 ml3 hpost3
    · intro J3_g hJ3_g; fa_fast_steps
      · have hsh0 : (hdr_gl &&& 0x00800000#32) = 0#32 := by assumption
        let ar3_raw :=
          (ar_mid.set (cref.setWidth 64).toNat (hdr_gl ||| 0x00800000#32)).set
            (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 old_sz).setWidth 64 - 1#64).toNat
            0xFFFFFFFF#32
        let ar_a := (ar_cur.set (cref.toNat + 2) (BitVec.ofNat 32 nsz)).set (cref.toNat + 1) 2#32
        let ar_b :=
          if (hdr0 &&& 0x00400000#32) ≠ 0#32 ∧ nsz ≤ (hdr0 &&& 0x7FFFF#32).toNat
          then ar_a.set cref.toNat hdr_gl else ar_a
        let ar3_can :=
          (ar_b.set cref.toNat (hdr_gl ||| 0x00800000#32)).set
            (cref.toNat + 3 + old_sz - 1) 0xFFFFFFFF#32
        have har3_eq : ar3_raw = ar3_can := by
          dsimp only [ar3_raw, ar3_can, ar_b, ar_a, ar_mid]
          rw [har_in, hcr0_z, hcr1_z, hcr2_z, hcr_end_z]
        let s3_r : FullState := { s2 with core := { s2.core with arena := ar3_raw, flags := fl3 } }
        let s3_c : FullState := { s2 with core := { s2.core with arena := ar3_can, flags := fl3 } }
        have hm3_c : (FullMem c s3_c ⋆ R) _ :=
          m5_fullMem_of_eq (s1 := s3_r) (by assumption)
            (congrArg (fun a => { s2.core with arena := a, flags := fl3 }) har3_eq) rfl
        exact hJ3_g () _ (s13_otfs_hdr_ok true har_len har_c h3o h4_old hnsz3 hnsz_lt hlits_info
          hmapeq hout_m har1_q har1_s2 hhdr_eq hfl3 (Or.inl ⟨rfl, hsh0⟩) hm3_c rfl)
      · have hsh1 : (hdr_gl &&& 0x00800000#32) ≠ 0#32 := by assumption
        let ar_a := (ar_cur.set (cref.toNat + 2) (BitVec.ofNat 32 nsz)).set (cref.toNat + 1) 2#32
        let ar3_can :=
          if (hdr0 &&& 0x00400000#32) ≠ 0#32 ∧ nsz ≤ (hdr0 &&& 0x7FFFF#32).toNat
          then ar_a.set cref.toNat hdr_gl else ar_a
        have har3_eq : ar_mid = ar3_can := by
          dsimp only [ar_mid, ar3_can, ar_a]; rw [har_in, hcr1_z, hcr2_z]
        let s3_r : FullState := { s2 with core := { s2.core with arena := ar_mid, flags := fl3 } }
        let s3_c : FullState := { s2 with core := { s2.core with arena := ar3_can, flags := fl3 } }
        have hm3_c : (FullMem c s3_c ⋆ R) _ :=
          m5_fullMem_of_eq (s1 := s3_r) hm_j
            (congrArg (fun a => { s2.core with arena := a, flags := fl3 }) har3_eq) rfl
        exact hJ3_g () _ (s13_otfs_hdr_ok false har_len har_c h3o h4_old hnsz3 hnsz_lt hlits_info
          hmapeq hout_m har1_q har1_s2 hhdr_eq hfl3 (Or.inr ⟨rfl, hsh1⟩) hm3_c rfl)
  · intro J_hdr1 hJ_hdr1; fa_fast_steps_nogrp
    · have hred_nz : (hdr0 &&& 0x00400000#32) ≠ 0#32 := by assumption
      refine wp_join_group (ts := [i32]) (fun (hdr_v, ()) ml_g =>
        hdr_v = hdr_gl ∧ (FullMem c { s2 with core :=
          { s2.core with arena := ar_mid } } ⋆ R) ml_g) ?_ ?_
      · rintro _ ⟨hdr_v, ⟨⟩⟩ ml_g ⟨rfl, hm_g⟩
        exact hJ_hdr1 (hdr_gl, ()) ml_g ⟨s2.core.flags, rfl, hfl_len,
          m5_fullMem_of_eq hm_g (by rcases s2 with ⟨⟨⟩, _⟩; rfl) rfl⟩
      · intro J_g hJ_g; fa_fast_steps_nogrp
        · have hge_sz : nsz ≤ (hdr0 &&& 0x7FFFF#32).toNat := by
            have hc' := hc
            rw [Nat.mod_eq_of_lt (by omega : nsz < 2 ^ 32)] at hc'; exact hc'
          have har_in_0 : (cref.setWidth 64).toNat < ar_in.length := by
            rw [har_in_l, hcr0_z]; omega
          fa_fast_steps
          have hgl_true : hdr_gl = (hdr0 &&& ~~~0x7FFFF#32) ||| (BitVec.ofNat 32 nsz - 1#32) := by
            dsimp only [hdr_gl]; rw [ite_eq_left ⟨hred_nz, hge_sz⟩]
          have hmid_true : ar_mid = ar_in.set cref.toNat hdr_gl := by
            dsimp only [ar_mid]; rw [ite_eq_left ⟨hred_nz, hge_sz⟩]
          have har_g_eq : ar_in.set (cref.setWidth 64).toNat ((hdr0 &&& ~~~524287) |||
              (BitVec.ofNat 32 nsz - 1)) = ar_mid := by
            rw [hmid_true, hcr0_z, hgl_true]; rfl
          exact hJ_g (hdr0 &&& ~~~524287 ||| BitVec.ofNat 32 nsz - 1, ()) _ ⟨hgl_true.symm,
            m5_fullMem_of_eq hm (congrArg (fun a => { s2.core with arena := a }) har_g_eq) rfl⟩
        · have hlt_sz : ¬ nsz ≤ (hdr0 &&& 0x7FFFF#32).toNat := by
            have hc' := hc
            rw [Nat.mod_eq_of_lt (by omega : nsz < 2 ^ 32)] at hc'; exact hc'
          have hgl_false : hdr_gl = hdr0 := by
            dsimp only [hdr_gl]; rw [ite_eq_right (fun h => hlt_sz h.2)]
          have hmid_false : ar_mid = ar_in := by
            dsimp only [ar_mid]; rw [ite_eq_right (fun h => hlt_sz h.2)]
          exact hJ_g (hdr0, ()) _ ⟨hgl_false.symm,
            m5_fullMem_of_eq hm_in (by rw [hmid_false]) rfl⟩
    · have hred_z : ¬ (hdr0 &&& 0x00400000#32) ≠ 0#32 := fun hn => hn hc
      have hgl_f : hdr_gl = hdr0 := by
        dsimp only [hdr_gl]; rw [ite_eq_right (fun h => hred_z h.1)]
      have hmid_f : ar_mid = ar_in := by
        dsimp only [ar_mid]; rw [ite_eq_right (fun h => hred_z h.1)]
      have hu_bd : ((uip >>> 1).setWidth 64).toNat < s2.core.flags.length := by
        rw [bv_c0_zext32_64, bv32_lshr_1, hfl_len]; omega
      fa_fast_steps_nogrp
      let fl1 := s2.core.flags.set ((uip >>> 1).setWidth 64).toNat
        (s2.core.flags[((uip >>> 1).setWidth 64).toNat]'hu_bd ||| 24)
      have hfl1_len : fl1.length = c.max_vars := by simp [fl1, hfl_len]
      refine wp_loop_group (fun r (oi_v, ()) ml_o => ∃ (oi : Nat) (fl_cur : List (BitVec 32)),
        r = nsz - oi ∧ oi ≤ nsz ∧ oi_v = BitVec.ofNat 32 oi ∧ fl_cur.length = c.max_vars ∧
        (FullMem c { s2 with core :=
          { s2.core with arena := ar_in, flags := fl_cur } } ⋆ R) ml_o) ?_ ?_
      · rintro Lo ro ⟨oi_v, ⟨⟩⟩ ml_o ih_o ⟨oi, fl_cur, rfl, hoi_le, rfl, hfl_c, hm_o⟩
        fa_fast_steps_nogrp
        · have hoi_lt : oi < nsz := by
            have hb : (BitVec.ofNat 32 oi).toNat < (BitVec.ofNat 32 nsz).toNat := ‹_›
            rwa [bv32_ofNat_toNat (by omega), bv32_ofNat_toNat (by omega)] at hb
          have hol_z : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 oi).setWidth 64).toNat =
              cref.toNat + 3 + oi := m5_otfs_bv_idx3_64 cref oi (by omega) (by omega)
          have hol_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 oi).setWidth 64).toNat <
              ar_in.length := by rw [hol_z, har_in_l]; omega
          have hol_ar : ar_in[(cref.setWidth 64 + 3#64 +
              (BitVec.ofNat 32 oi).setWidth 64).toNat]'hol_bd =
              ar_cur[cref.toNat + 3 + oi]?.getD 0#32 := by
            rw [m5_list_getElem_of_idx (hj := by rw [har_in_l]; omega) hol_z]
            have harin_ne : ar_in[cref.toNat + 3 + oi]? = ar_cur[cref.toNat + 3 + oi]? := by
              rw [har_in, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
            have hd := congrArg (·.getD 0#32) harin_ne
            rwa [List.getElem?_eq_getElem (by rw [har_in_l]; omega), Option.getD_some] at hd
          have hol_lt_2cv : (ar_in[(cref.setWidth 64 + 3#64 +
              (BitVec.ofNat 32 oi).setWidth 64).toNat]'hol_bd).toNat < 2 * s.core.cur_vars := by
            rw [hol_ar]
            have hp_oi : origMap[oi]?.getD 0 < old_sz := hlt_m _ (by
              rw [List.getElem?_eq_getElem (by rw [hlen_m]; omega), Option.getD_some]
              exact List.getElem_mem _)
            rw [hmapeq oi hoi_lt]; exact (hlits_info _ hp_oi).1
          have hfl_bd : ((ar_in[(cref.setWidth 64 + 3#64 +
              (BitVec.ofNat 32 oi).setWidth 64).toNat]'hol_bd >>> 1).setWidth 64).toNat <
              fl_cur.length := by
            rw [bv_c0_zext32_64, bv32_lshr_1, hfl_c]; omega
          fa_fast_steps; rw [m5_bv32_ofNat_add1]
          exact ih_o (nsz - (oi + 1)) _ _ (by omega)
            ⟨oi + 1, _, rfl, by omega, rfl, (List.length_set ..).trans hfl_c, by assumption⟩
        · have hoi_eq : oi = nsz := by
            have hba : ¬ (BitVec.ofNat 32 oi).toNat < (BitVec.ofNat 32 nsz).toNat := ‹_›
            rw [bv32_ofNat_toNat (by omega), bv32_ofNat_toNat (by omega)] at hba; omega
          subst hoi_eq
          exact hJ_hdr1 (hdr0, ()) _ ⟨fl_cur, hgl_f.symm, hfl_c,
            m5_fullMem_of_eq hm_o (by rw [hmid_f]) rfl⟩
      · intro Lo hLo
        exact hLo nsz (0#32, ()) _ ⟨0, fl1, rfl, Nat.zero_le _, rfl, hfl1_len, by assumption⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S2
