/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2OTFSUnitProof0b1

/-!
# Kissat Fidelity Step 13 `full_otfs_large` Main WP Proof (`0b2`)

Proves `full_otfs_large_step13_wp` against `step13OtfsLargeSpec` (every theorem `<= 320` lines,
`<= 100` cols), composing:
1. `s13_otfs_swap01_s1` & `s13_otfs_s2_of_unwatch`: swap01 + `full_unwatch_large` state transport.
2. `s13_otfs_shrink_tail_wp`: Pass 2+3 compaction loop -> `s13_otfs_j3_hdr_wp` ->
   `s13_otfs_post_j3_wp`.
3. `full_otfs_large_step13_wp`: `Jl0`, Pass 1, Pass 1b, `wstack_ensure2`, `full_watch_push`,
   `s13_otfs_swap01_s1`, `full_unwatch_large(uip)`, `s13_otfs_s2_of_unwatch`, and
   `s13_otfs_shrink_tail_wp`.
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

private theorem s13_otfs_swap01_s1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s s_p : FullState} {wv_p ws_p wso_p : List (BitVec 32)} {wl_p : Nat}
    {wu_p : BitVec 64} {cref l0 uip : BitVec 32} {R : Mem 64 → Prop} {m_sw : Mem 64}
    (hlen : s.LengthsOk c) (hnd : FullArenaVarsNodup s) (_hdm : s.core.dense_mode = 0#64)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref.toNat = false)
    (hs01 : (l0 = s.core.arena[cref.toNat + 3]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 4]?.getD 0#32 = uip) ∨
      (l0 = s.core.arena[cref.toNat + 4]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 3]?.getD 0#32 = uip))
    (hsp_c : s_p.core = { s.core with wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p })
    (hsp_sc : s_p.scratch = { s.scratch with wsort := wso_p })
    (hlen_p' : s_p.LengthsOk c) (hw_p : FullWitnessCutInv c F0 F_cur cut s_p.core)
    (hcr3_z : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (hcb1_z : (cref.setWidth 64 + 3#64 + 1#64).toNat = cref.toNat + 4)
    (_hcr3_bd : (cref.setWidth 64 + 3#64).toNat < s.core.arena.length)
    (_hcb1_bd : (cref.setWidth 64 + 3#64 + 1#64).toNat < s.core.arena.length)
    (hm_sw :
      let ar_sw := (s_p.core.arena.set (cref.setWidth 64 + 3#64).toNat l0).set
        (cref.setWidth 64 + 3#64 + 1#64).toNat uip
      (FullMem c { s_p with core := { s_p.core with arena := ar_sw } } ⋆ R) m_sw) :
    ∃ s1 : FullState,
      let ar1 := (s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip
      s1.core = { s.core with arena := ar1, wvec := wv_p, wstk := ws_p, wlen := wl_p,
                              wusable := wu_p } ∧
      s1.scratch = { s.scratch with wsort := wso_p } ∧
      (FullMem c s1 ⋆ R) m_sw ∧ s1.LengthsOk c ∧
      FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut s1.core ∧
      FullArenaVarsNodup s1 ∧ fullArenaClauseRefs s1 = fullArenaClauseRefs s ∧
      fullArenaClauseSize s1 cref.toNat = fullArenaClauseSize s cref.toNat ∧
      fullArenaClauseGarb s1 cref.toNat = false ∧
      (∀ q, 2 ≤ q → ((s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip)[
        cref.toNat + 3 + q]? = s.core.arena[cref.toNat + 3 + q]?) := by
  let ar1 := (s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip
  have hsp_ar : s_p.core.arena = s.core.arena := by rw [hsp_c]
  have hcref_p : cref.toNat ∈ fullArenaClauseRefsCore s_p.core := by
    change cref.toNat ∈ fullArenaClauseRefsCore s.core at hcref
    rwa [show fullArenaClauseRefsCore s_p.core = fullArenaClauseRefsCore s.core by
      simp [fullArenaClauseRefsCore, hsp_c]]
  have hnd_p : FullArenaVarsNodup s_p := fun r hr hngr => by
    change r ∈ fullArenaClauseRefsCore s_p.core at hr
    rw [show fullArenaClauseRefsCore s_p.core = fullArenaClauseRefsCore s.core by
      simp [fullArenaClauseRefsCore, hsp_c]] at hr
    change ((fullArenaClauseLitsCore s_p.core r).map (· / 2)).Nodup
    rw [show fullArenaClauseLitsCore s_p.core r = fullArenaClauseLitsCore s.core r by
      simp [fullArenaClauseLitsCore, fullArenaClauseSizeCore, hsp_c]]
    exact hnd r hr (by
      change fullArenaClauseGarbCore s.core r = false
      simpa [fullArenaClauseGarbCore, fullArenaHdrCore, hsp_c] using hngr)
  have hng_p : fullArenaClauseGarb s_p cref.toNat = false := by
    simpa [fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore, hsp_c] using hng
  have hs01_p : (l0 = s_p.core.arena[cref.toNat + 3]?.getD 0#32 ∧
      s_p.core.arena[cref.toNat + 4]?.getD 0#32 = uip) ∨
    (l0 = s_p.core.arena[cref.toNat + 4]?.getD 0#32 ∧
      s_p.core.arena[cref.toNat + 3]?.getD 0#32 = uip) := by rw [hsp_ar]; exact hs01
  obtain ⟨hw1, hnd1, hrefs1, hsz1, hng1, har1_q, _, _⟩ :=
    Full.otfs_large_swap01 hlen_p' (m5_canonCut_to_anaCut hw_p) hnd_p hcref_p hng_p hs01_p
  have har1_sym : (s_p.core.arena.set (cref.setWidth 64 + 3#64).toNat l0).set
      (cref.setWidth 64 + 3#64 + 1#64).toNat uip = ar1 := by
    dsimp only [ar1]; rw [hsp_ar, hcr3_z, hcb1_z]
  let ar1_ast := (s_p.core.arena.set (cref.setWidth 64 + 3#64).toNat l0).set
    (cref.setWidth 64 + 3#64 + 1#64).toNat uip
  obtain ⟨s1, hs1_c, hs1_sc, hm1'⟩ :=
    m5_otfs_opaque_state (s_old := { s_p with core := { s_p.core with arena := ar1_ast } })
      { s.core with arena := ar1, wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p }
      { s.scratch with wsort := wso_p } hm_sw
      (by dsimp only [ar1_ast]; rw [har1_sym, hsp_c]) hsp_sc
  obtain ⟨hlen1, hw1', hnd1', hrefs1', hsz1', hng1', har1_q'⟩ :=
    s13_otfs_s1_facts hsp_ar hsp_c hsp_sc hs1_c hs1_sc hlen.core_ok.arena_len_arr hlen_p' rfl
      hw1 hnd1 hrefs1 hsz1 hng1 har1_q rfl
  exact ⟨s1, hs1_c, hs1_sc, hm1', hlen1, hw1', hnd1', hrefs1', hsz1', hng1', har1_q'⟩

private theorem s13_otfs_s2_of_unwatch {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s s1 : FullState} {ar1 wv_p ws_p wv2 ws2 wso_p : List (BitVec 32)}
    {wl_p : Nat} {wu_p wu2 : BitVec 64} {cref : BitVec 32} {R : Mem 64 → Prop} {m2 : Mem 64}
    (hs1_c : s1.core = { s.core with arena := ar1, wvec := wv_p, wstk := ws_p,
                                      wlen := wl_p, wusable := wu_p })
    (hs1_sc : s1.scratch = { s.scratch with wsort := wso_p })
    (hlen2 : ({ s1 with core := { s1.core with wvec := wv2, wstk := ws2, wusable := wu2 } } :
      FullState).LengthsOk c)
    (hmw2 : ∀ F_cur, ModeWatchesInv F_cur s1.core →
      ModeWatchesInv F_cur { s1.core with wvec := wv2, wstk := ws2, wusable := wu2 })
    (hm2 : (FullMem c { s1 with core :=
      { s1.core with wvec := wv2, wstk := ws2, wusable := wu2 } } ⋆ R) m2)
    (hw1' : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut s1.core)
    (hnd1' : FullArenaVarsNodup s1)
    (hrefs1' : fullArenaClauseRefs s1 = fullArenaClauseRefs s)
    (hsz1' : fullArenaClauseSize s1 cref.toNat = fullArenaClauseSize s cref.toNat)
    (hng1' : fullArenaClauseGarb s1 cref.toNat = false) :
    ∃ s2 : FullState,
      s2.core = { s.core with arena := ar1, wvec := wv2, wstk := ws2,
                              wlen := wl_p, wusable := wu2, oom := s.core.oom } ∧
      s2.scratch = { s.scratch with wsort := wso_p } ∧
      (FullMem c s2 ⋆ R) m2 ∧ s2.LengthsOk c ∧
      FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut s2.core ∧
      FullArenaVarsNodup s2 ∧ fullArenaClauseRefs s2 = fullArenaClauseRefs s ∧
      fullArenaClauseSize s2 cref.toNat = fullArenaClauseSize s cref.toNat ∧
      fullArenaClauseGarb s2 cref.toNat = false := by
  obtain ⟨s2, hs2_base, hs2_sc, hm2_s2⟩ :=
    m5_otfs_opaque_state
      { s.core with arena := ar1, wvec := wv2, wstk := ws2, wlen := wl_p,
                    wusable := wu2, oom := s.core.oom }
      { s.scratch with wsort := wso_p } hm2 (by dsimp only; rw [hs1_c]) hs1_sc
  have hs2_s1_c : s2.core = { s1.core with wvec := wv2, wstk := ws2, wusable := wu2 } := by
    rw [hs2_base, hs1_c]
  have hlen2' : s2.LengthsOk c :=
    ⟨by rw [hs2_s1_c]; exact hlen2.core_ok, by rw [hs2_sc, ← hs1_sc]; exact hlen2.scratch_ok⟩
  have hw2 : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut s2.core := by
    rw [hs2_s1_c]; exact hw1'.with_watches (hmw2 F_cur hw1'.watches)
  have hnd2 : FullArenaVarsNodup s2 := by
    unfold FullArenaVarsNodup at hnd1' ⊢
    simpa only [hs2_s1_c, fullArenaClauseRefs, fullArenaClauseGarb, fullArenaClauseLits,
      fullArenaClauseRefsCore, fullArenaClauseGarbCore, fullArenaClauseLitsCore,
      fullArenaClauseSizeCore, fullArenaHdrCore] using hnd1'
  have hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s := by
    change fullArenaClauseRefsCore s2.core = fullArenaClauseRefsCore s.core
    change fullArenaClauseRefsCore s1.core = fullArenaClauseRefsCore s.core at hrefs1'
    rw [← hrefs1', hs2_s1_c]; rfl
  have hng2 : fullArenaClauseGarb s2 cref.toNat = false := by
    simpa only [fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore, hs2_s1_c]
      using hng1'
  have hsz2 : fullArenaClauseSize s2 cref.toNat = fullArenaClauseSize s cref.toNat := by
    change fullArenaClauseSizeCore s2.core cref.toNat = _
    exact (show fullArenaClauseSizeCore s2.core cref.toNat =
      fullArenaClauseSizeCore s1.core cref.toNat by
        simp [fullArenaClauseSizeCore, hs2_s1_c]).trans hsz1'
  exact ⟨s2, hs2_base, hs2_sc, hm2_s2, hlen2', hw2, hnd2, hrefs2, hsz2, hng2⟩

private abbrev s13OtfsShrinkExitExpr (c : FullCfg) (cref l0 : BitVec 32)
    (hp_v : Val i32) : Expr Val Cont [.bool] :=
  Expr.group (sig := [[]])
    (fun _J4 => Blocks.cons
      (fun _ =>
        Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var (cref.setWidth 64 + 3#64), Arg.imm 1, ()))
          fun p =>
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
               Expr.let_ (Op.mk (.shl (.bits 64)) (Arg.var p_1.fst, Arg.var p_2.fst, ())) fun p_1 =>
               Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var p_1.fst, Arg.imm 1, ())) fun p_1 =>
               Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p_1.fst, Arg.imm 4, ())) fun p_1 =>
               Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var ld_1, Arg.var p_1.fst, ())) fun p_1 =>
               Expr.load i32 (Arg.var p_1.fst) fun ld_4 =>
               Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld_4, ())) fun p_1 =>
               Expr.group (sig := [[]])
                 (fun _Js_2 => Blocks.cons (fun _ => Expr.jump Js.fst ()) Blocks.nil)
                 (fun Js_2 =>
                  Expr.let_ (Op.mk (.cmp .uge (.bits 64) .bool rfl)
                      (Arg.var p_1.fst, Arg.imm 2, ())) fun p_60 =>
                  Expr.jnz (Arg.var p_60.fst)
                    (Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var p.fst, Arg.var p_1.fst, ()))
                        fun p_61 =>
                     Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var p.fst, Arg.imm 2, ())) fun p_62 =>
                     Expr.group (sig := [[i64]])
                       (fun _Js_b => Blocks.cons (fun _ => Expr.jump Js_2.fst ()) Blocks.nil)
                       (fun Js_b =>
                        Expr.group (sig := [[i64]])
                          (fun Js_1 => Blocks.cons (fun p_63 =>
                            Expr.let_ (Op.mk (.cmp .uge (.bits 64) .bool rfl)
                                (Arg.var p_63.fst, Arg.var p_62.fst, ())) fun p_64 =>
                            Expr.jnz (Arg.var p_64.fst)
                              (Expr.let_ (Op.mk (.sub (.bits 64)) (Arg.var p_63.fst, Arg.imm 1, ()))
                                  fun p_65 =>
                               Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p_65.fst, Arg.imm 4, ()))
                                 fun p_66 =>
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
                                  Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_68.fst, ())) fun p_69 =>
                                  Expr.let_ (Op.mk (.add (.bits 64))
                                    (Arg.var p_a.fst, Arg.var p_69.fst, ())) fun p_b =>
                                  Expr.jump Js_1.fst (Arg.var p_b.fst, ())))
                              (Expr.jump Js_b.fst (Arg.var p_63.fst, ()))) Blocks.nil)
                          (fun Js_l => Expr.jump Js_l.fst (Arg.var p_61.fst, ()))))
                    (Expr.jump Js_2.fst ())))
              (Expr.jump Js.fst ()))) Blocks.nil)
    (fun J4 =>
      Expr.let_ (Op.mk (.cmp .ne (.bits 32) .bool rfl) (Arg.var hp_v, Arg.imm 1, ())) fun p =>
      Expr.jnz (Arg.var p.fst)
        (Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var (cref.setWidth 64 + 3#64), Arg.imm 1, ()))
            fun p =>
         Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
         Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
         Expr.load i32 (Arg.var p.fst) fun ld_8 =>
         Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var (cref.setWidth 64 + 3#64), Arg.imm 1, ()))
           fun p =>
         Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
         Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
         Expr.let_ (Op.mk (.zext 32 64) (Arg.var hp_v, ())) fun p_39 =>
         Expr.let_ (Op.mk (.add (.bits 64))
           (Arg.var (cref.setWidth 64 + 3#64), Arg.var p_39.fst, ())) fun p_40 =>
         Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p_40.fst, Arg.imm 4, ())) fun p_41 =>
         Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pArena, Arg.var p_41.fst, ())) fun p_42 =>
         Expr.load i32 (Arg.var p_42.fst) fun ld_9 =>
         Expr.store (Arg.var ld_9) (Arg.var p.fst)
           (Expr.let_ (Op.mk (.zext 32 64) (Arg.var hp_v, ())) fun p =>
            Expr.let_ (Op.mk (.add (.bits 64))
              (Arg.var (cref.setWidth 64 + 3#64), Arg.var p.fst, ())) fun p =>
            Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
            Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
            Expr.store (Arg.var ld_8) (Arg.var p.fst) (Expr.jump J4.fst ())))
        (Expr.jump J4.fst ()))

private abbrev s13OtfsShrinkTailExpr (c : FullCfg) (cref l0 uip oldSzV : BitVec 32) :
    Expr Val Cont [.bool] :=
  Expr.group (sig := [[i32, i32, i32, i32]])
    (fun J_p2 => Blocks.cons
      (fun p2 =>
        Expr.let_ (Op.mk (.cmp .ult (.bits 32) .bool rfl) (Arg.var p2.fst, Arg.var oldSzV, ()))
          fun p_c =>
        Expr.jnz (Arg.var p_c.fst)
          (Expr.let_ (Op.mk (.zext 32 64) (Arg.var p2.fst, ())) fun p_3 =>
           Expr.let_ (Op.mk (.add (.bits 64))
             (Arg.var (cref.setWidth 64 + 3#64), Arg.var p_3.fst, ())) fun p_4 =>
           Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p_4.fst, Arg.imm 4, ())) fun p_5 =>
           Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pArena, Arg.var p_5.fst, ())) fun p_6 =>
           Expr.load i32 (Arg.var p_6.fst) fun ot =>
           Expr.let_ (Op.mk (.lshr (.bits 32)) (Arg.var ot, Arg.imm 1, ())) fun p_7 =>
           Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_7.fst, ())) fun p_8 =>
           Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p_8.fst, Arg.imm 4, ())) fun p_9 =>
           Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pLevel, Arg.var p_9.fst, ())) fun p_10 =>
           Expr.load i32 (Arg.var p_10.fst) fun cl =>
           Expr.group (sig := [[i32, i32, i32]])
             (fun _J_s => Blocks.cons
               (fun ps =>
                 Expr.let_ (Op.mk (.add (.bits 32)) (Arg.var p2.fst, Arg.imm 1, ())) fun p_11 =>
                 Expr.jump J_p2.fst (Arg.var p_11.fst, Arg.var ps.fst, Arg.var ps.snd.fst,
                   Arg.var ps.snd.snd.fst, ())) Blocks.nil)
             (fun J_s =>
               Expr.let_ (Op.mk (.cmp .ugt (.bits 32) .bool rfl) (Arg.var cl, Arg.imm 0, ()))
                 fun p_11 =>
               Expr.jnz (Arg.var p_11.fst)
                 (Expr.let_ (Op.mk (.zext 32 64) (Arg.var p2.snd.fst, ())) fun p_12 =>
                  Expr.let_ (Op.mk (.add (.bits 64))
                    (Arg.var (cref.setWidth 64 + 3#64), Arg.var p_12.fst, ())) fun p_13 =>
                  Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p_13.fst, Arg.imm 4, ())) fun p_14 =>
                  Expr.let_ (Op.mk (.add (.bits 64))
                    (Arg.var c.pArena, Arg.var p_14.fst, ())) fun p_15 =>
                  Expr.store (Arg.var ot) (Arg.var p_15.fst)
                    (Expr.group (sig := [[i32, i32]])
                      (fun _J_hl => Blocks.cons
                        (fun phl =>
                          Expr.let_ (Op.mk (.add (.bits 32)) (Arg.var p2.snd.fst, Arg.imm 1, ()))
                            fun p_16 =>
                          Expr.jump J_s.fst (Arg.var p_16.fst, Arg.var phl.fst,
                            Arg.var phl.snd.fst, ())) Blocks.nil)
                      (fun J_hl =>
                        Expr.let_ (Op.mk (.cmp .ugt (.bits 32) .bool rfl)
                            (Arg.var cl, Arg.var p2.snd.snd.snd.fst, ())) fun p_17 =>
                        Expr.jnz (Arg.var p_17.fst)
                          (Expr.jump J_hl.fst (Arg.var p2.snd.fst, Arg.var cl, ()))
                          (Expr.jump J_hl.fst (Arg.var p2.snd.snd.fst,
                            Arg.var p2.snd.snd.snd.fst, ())))))
                 (Expr.jump J_s.fst (Arg.var p2.snd.fst, Arg.var p2.snd.snd.fst,
                   Arg.var p2.snd.snd.snd.fst, ()))))
          (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun ph_1 =>
           Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var ph_1.fst, Arg.imm 4, ())) fun ph_2 =>
           Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pArena, Arg.var ph_2.fst, ())) fun ph_3 =>
           Expr.load i32 (Arg.var ph_3.fst) fun hdr =>
           Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun ph_4 =>
           Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var ph_4.fst, Arg.imm 2, ())) fun ph_5 =>
           Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var ph_5.fst, Arg.imm 4, ())) fun ph_6 =>
           Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.pArena, Arg.var ph_6.fst, ())) fun ph_7 =>
           Expr.store (Arg.var p2.snd.fst) (Arg.var ph_7.fst)
             (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun ph_8 =>
              Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var ph_8.fst, Arg.imm 1, ())) fun ph_9 =>
              Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var ph_9.fst, Arg.imm 4, ())) fun ph_10 =>
              Expr.let_ (Op.mk (.add (.bits 64))
                (Arg.var c.pArena, Arg.var ph_10.fst, ())) fun ph_11 =>
              Expr.store (t := i32) (Arg.imm 2) (Arg.var ph_11.fst)
                (Expr.group (sig := [[i32]])
                  (fun _J_hdr1 => Blocks.cons
                    (fun hdr_p =>
                      Expr.group (sig := [[]])
                        (fun _J3_g => Blocks.cons
                          (fun _ => s13OtfsShrinkExitExpr c cref l0 p2.snd.snd.fst) Blocks.nil)
                        (fun J3_g =>
                          Expr.let_ (Op.mk (.and (.bits 32))
                              (Arg.var hdr_p.fst, Arg.imm 8388608, ())) fun p_38 =>
                          Expr.let_ (Op.mk (.cmp .eq (.bits 32) .bool rfl)
                              (Arg.var p_38.fst, Arg.imm 0, ())) fun p_39 =>
                          Expr.jnz (Arg.var p_39.fst)
                            (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p =>
                             Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ()))
                               fun p =>
                             Expr.let_ (Op.mk (.add (.bits 64))
                               (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
                             Expr.let_ (Op.mk (.or (.bits 32))
                               (Arg.var hdr_p.fst, Arg.imm 8388608, ())) fun p_40 =>
                             Expr.store (Arg.var p_40.fst) (Arg.var p.fst)
                               (Expr.let_ (Op.mk (.zext 32 64) (Arg.var oldSzV, ())) fun p =>
                                Expr.let_ (Op.mk (.add (.bits 64))
                                  (Arg.var (cref.setWidth 64 + 3#64), Arg.var p.fst, ())) fun p =>
                                Expr.let_ (Op.mk (.sub (.bits 64)) (Arg.var p.fst, Arg.imm 1, ()))
                                  fun p =>
                                Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ()))
                                  fun p =>
                                Expr.let_ (Op.mk (.add (.bits 64))
                                  (Arg.var c.pArena, Arg.var p.fst, ())) fun p =>
                                Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p.fst)
                                  (Expr.jump J3_g.fst ())))
                            (Expr.jump J3_g.fst ()))) Blocks.nil)
                  (fun J_hdr1 =>
                    Expr.let_ (Op.mk (.and (.bits 32)) (Arg.var hdr, Arg.imm 4194304, ())) fun p =>
                    Expr.let_ (Op.mk (.cmp .ne (.bits 32) .bool rfl) (Arg.var p.fst, Arg.imm 0, ()))
                      fun p =>
                    Expr.jnz (Arg.var p.fst)
                      (Expr.group (sig := [[i32]])
                        (fun _J_g => Blocks.cons
                          (fun pg => Expr.jump J_hdr1.fst (Arg.var pg.fst, ())) Blocks.nil)
                        (fun J_g =>
                          Expr.let_ (Op.mk (.and (.bits 32)) (Arg.var hdr, Arg.imm 524287, ()))
                            fun p =>
                          Expr.let_ (Op.mk (.cmp .uge (.bits 32) .bool rfl)
                              (Arg.var p.fst, Arg.var p2.snd.fst, ())) fun p =>
                          Expr.jnz (Arg.var p.fst)
                            (Expr.let_ (Op.mk (.not (.bits 32)) (Arg.imm 524287, ())) fun p =>
                             Expr.let_ (Op.mk (.and (.bits 32)) (Arg.var hdr, Arg.var p.fst, ()))
                               fun p =>
                             Expr.let_ (Op.mk (.sub (.bits 32))
                               (Arg.var p2.snd.fst, Arg.imm 1, ())) fun p_1 =>
                             Expr.let_ (Op.mk (.or (.bits 32)) (Arg.var p.fst, Arg.var p_1.fst, ()))
                               fun p =>
                             Expr.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p_2 =>
                             Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p_2.fst, Arg.imm 4, ()))
                               fun p_3 =>
                             Expr.let_ (Op.mk (.add (.bits 64))
                               (Arg.var c.pArena, Arg.var p_3.fst, ())) fun p_4 =>
                             Expr.store (Arg.var p.fst) (Arg.var p_4.fst)
                               (Expr.jump J_g.fst (Arg.var p.fst, ())))
                            (Expr.jump J_g.fst (Arg.var hdr, ()))))
                      (Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var c.hdr, Arg.imm 800, ())) fun p =>
                       Expr.load i64 (Arg.var p.fst) fun ld =>
                       Expr.let_ (Op.mk (.lshr (.bits 32)) (Arg.var uip, Arg.imm 1, ())) fun p =>
                       Expr.let_ (Op.mk (.zext 32 64) (Arg.var p.fst, ())) fun p =>
                       Expr.let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                       Expr.let_ (Op.mk (.add (.bits 64)) (Arg.var ld, Arg.var p.fst, ())) fun p =>
                       Expr.let_ (Op.mk (.lshr (.bits 32)) (Arg.var uip, Arg.imm 1, ())) fun p_1 =>
                       Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_1.fst, ())) fun p_2 =>
                       Expr.let_ (Op.mk (.mul (.bits 64))
                           (Arg.var p_2.fst, Arg.imm 4, ())) fun p_3 =>
                       Expr.let_ (Op.mk (.add (.bits 64))
                           (Arg.var ld, Arg.var p_3.fst, ())) fun p_4 =>
                       Expr.load i32 (Arg.var p_4.fst) fun ld_1 =>
                       Expr.let_ (Op.mk (.or (.bits 32)) (Arg.var ld_1, Arg.imm 24, ())) fun p_5 =>
                       Expr.store (Arg.var p_5.fst) (Arg.var p.fst)
                         (Expr.group (sig := [[i32]])
                           (fun J_o => Blocks.cons
                             (fun p_o =>
                               Expr.let_ (Op.mk (.cmp .ult (.bits 32) .bool rfl)
                                   (Arg.var p_o.fst, Arg.var p2.snd.fst, ())) fun p_6 =>
                               Expr.jnz (Arg.var p_6.fst)
                                 (Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_o.fst, ())) fun p_7 =>
                                  Expr.let_ (Op.mk (.add (.bits 64))
                                    (Arg.var (cref.setWidth 64 + 3#64), Arg.var p_7.fst, ()))
                                    fun p_8 =>
                                  Expr.let_ (Op.mk (.mul (.bits 64))
                                    (Arg.var p_8.fst, Arg.imm 4, ())) fun p_9 =>
                                  Expr.let_ (Op.mk (.add (.bits 64))
                                    (Arg.var c.pArena, Arg.var p_9.fst, ())) fun p_10 =>
                                  Expr.load i32 (Arg.var p_10.fst) fun ld_2 =>
                                  Expr.let_ (Op.mk (.lshr (.bits 32))
                                    (Arg.var ld_2, Arg.imm 1, ())) fun pa =>
                                  Expr.let_ (Op.mk (.zext 32 64) (Arg.var pa.fst, ())) fun pb =>
                                  Expr.let_ (Op.mk (.mul (.bits 64))
                                      (Arg.var pb.fst, Arg.imm 4, ()))
                                    fun pc =>
                                  Expr.let_ (Op.mk (.add (.bits 64))
                                    (Arg.var ld, Arg.var pc.fst, ())) fun pd =>
                                  Expr.let_ (Op.mk (.lshr (.bits 32))
                                    (Arg.var ld_2, Arg.imm 1, ())) fun pe =>
                                  Expr.let_ (Op.mk (.zext 32 64) (Arg.var pe.fst, ())) fun pf =>
                                  Expr.let_ (Op.mk (.mul (.bits 64))
                                      (Arg.var pf.fst, Arg.imm 4, ()))
                                    fun pg =>
                                  Expr.let_ (Op.mk (.add (.bits 64))
                                    (Arg.var ld, Arg.var pg.fst, ())) fun ph =>
                                  Expr.load i32 (Arg.var ph.fst) fun ld_3 =>
                                  Expr.let_ (Op.mk (.or (.bits 32))
                                    (Arg.var ld_3, Arg.imm 24, ())) fun pi =>
                                  Expr.store (Arg.var pi.fst) (Arg.var pd.fst)
                                    (Expr.let_ (Op.mk (.add (.bits 32))
                                        (Arg.var p_o.fst, Arg.imm 1, ())) fun pj =>
                                     Expr.jump J_o.fst (Arg.var pj.fst, ())))
                                 (Expr.jump J_hdr1.fst (Arg.var hdr, ())))
                             Blocks.nil)
                           (fun J_o => Expr.jump J_o.fst (Arg.imm 0, ())))))))))
      Blocks.nil)
    (fun J_p2 => Expr.jump J_p2.fst (Arg.imm 2, Arg.imm 1, Arg.imm 1, Arg.imm 0, ()))

private theorem s13_otfs_shrink_tail_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut idx_u old_sz : Nat}
    {s s2 : FullState} {ar1 ws2 wso_p : List (BitVec 32)} {cref l0 uip oldSzV : BitVec 32}
    {R : Mem 64 → Prop} {m2 : Mem 64}
    (hlen : s.LengthsOk c) (hw : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut s.core)
    (hnd : FullArenaVarsNodup s) (hlen2 : s2.LengthsOk c)
    (hw2 : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut s2.core)
    (hnd2 : FullArenaVarsNodup s2) (hdm : s.core.dense_mode = 0#64)
    (hsp_oom : s.core.oom = s2.core.oom) (_hws2 : s2.core.wstk = ws2)
    (hs2_base : s2.core = { s.core with arena := ar1, wvec := s2.core.wvec, wstk := ws2,
                                        wlen := s2.core.wlen, wusable := s2.core.wusable })
    (hs2_sc : s2.scratch = { s.scratch with wsort := wso_p })
    (hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref.toNat = false)
    (hcref2 : cref.toNat ∈ fullArenaClauseRefs s2)
    (hng2 : fullArenaClauseGarb s2 cref.toNat = false)
    (hsz_orig : fullArenaClauseSize s cref.toNat = old_sz)
    (hsz2 : fullArenaClauseSize s2 cref.toNat = old_sz)
    (hold_v : oldSzV = BitVec.ofNat 32 old_sz)
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
    (hl0_lt : l0.toNat < 2 * s.core.cur_vars) (hu_lt : uip.toNat < 2 * s.core.cur_vars)
    (hcr_lt31 : cref.toNat < 0x80000000)
    (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap) (h4_old : 4 ≤ old_sz)
    (hcnt3 : 3 ≤ 1 + Full.otfsActCnt s.core cref.toNat old_sz)
    (hact_lt : 1 + Full.otfsActCnt s.core cref.toNat old_sz < old_sz)
    (hcr0_z : (cref.setWidth 64).toNat = cref.toNat)
    (hcr1_z : (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1)
    (hcr2_z : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2)
    (hcr3_z : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (hcr4_z : (cref.setWidth 64 + 4#64).toNat = cref.toNat + 4)
    (hcb1_eq : cref.setWidth 64 + 3#64 + 1#64 = cref.setWidth 64 + 4#64)
    (hs01 : (l0 = s.core.arena[cref.toNat + 3]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 4]?.getD 0#32 = uip) ∨
      (l0 = s.core.arena[cref.toNat + 4]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 3]?.getD 0#32 = uip))
    (hlits_info : ∀ j < old_sz,
      (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ≠ 0xFFFFFFFF#32)
    (har1_def : ar1 = (s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip)
    (har1_l : ar1.length = c.arena_cap)
    (har1_q : ∀ q, 2 ≤ q → ar1[cref.toNat + 3 + q]? = s.core.arena[cref.toNat + 3 + q]?)
    (har1_s2 : ∀ i, i < cref.toNat + 3 ∨ cref.toNat + 5 ≤ i → ar1[i]? = s2.core.arena[i]?)
    (hm2 : (FullMem c s2 ⋆ R) m2)
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
    wp Γ Q X (s13OtfsShrinkTailExpr c cref l0 uip oldSzV) m2 := by
  subst hold_v
  have har_len := hlen.core_ok.arena_len_arr; have hcv_le := hlen.core_ok.cur_vars_le
  have hlvl_len := hlen.core_ok.lvl_len; have hs2_lvl : s2.core.lvl = s.core.lvl := by rw [hs2_base]
  have hfl_len2 : s2.core.flags.length = c.max_vars := hlen2.core_ok.flags_len
  refine wp_loop_group (fun r (iv, nszv, hpv, hlv, ()) ml =>
    ∃ (i_n nsz hp_n : Nat) (ar_cur : List (BitVec 32)) (origMap : List Nat),
      (FullMem c { s2 with core := { s2.core with arena := ar_cur } } ⋆ R) ml ∧
      iv = BitVec.ofNat 32 i_n ∧ nszv = BitVec.ofNat 32 nsz ∧
      hpv = BitVec.ofNat 32 hp_n ∧ (hp_n = 1 ∨ (1 ≤ hp_n ∧ hp_n < nsz)) ∧
      S13OtfsShrinkInv c s ar1 cref l0 uip old_sz r i_n nsz ar_cur origMap) ?_ ?_
  · rintro L2 r2 ⟨iv, nszv, hpv, hlv, ⟨⟩⟩ ml ih2
      ⟨i_nat, nsz, hp_n, ar_cur, origMap, hm_c, rfl, rfl, rfl, hhp_ok, hinv_l⟩
    have hr2_eq : r2 = old_sz - i_nat := hinv_l.2.1; subst r2
    have ⟨har_c, _, hi2, hile, hns1, hact, hlm, hpw, hlt_m, h01, hcov, hmapeq, hout_m⟩ := hinv_l
    fa_fast_steps_nogrp
    · have hilt : i_nat < old_sz := by
        have hb : (BitVec.ofNat 32 i_nat).toNat < (BitVec.ofNat 32 old_sz).toNat := ‹_›
        rwa [bv32_ofNat_toNat (by omega), bv32_ofNat_toNat (by omega)] at hb
      obtain ⟨hc_idx_bd, hc_z_bd, _har_nsz_bd2, har_bd, _hnsz_lt_i, _hc_idx, _hc_z, hnsz_z,
        hot_c_eq, hot_z_eq, h2_lvl_bd, hv_bd⟩ :=
        s13_otfs_loop2_step_bds hcap31 h3o hcv_le hlvl_len hlen2.core_ok.lvl_len har_len hinv_l
          hilt har1_q hlits_info
      fa_fast_steps_nogrp
      refine wp_join_group (ts := [i32, i32, i32])
        (fun (nszv', hpv', _hlv', ()) ml' =>
          ∃ (nsz' hp_n' : Nat) (ar' : List (BitVec 32)) (omap' : List Nat),
            (FullMem c { s2 with core := { s2.core with arena := ar' } } ⋆ R) ml' ∧
            nszv' = BitVec.ofNat 32 nsz' ∧ hpv' = BitVec.ofNat 32 hp_n' ∧
            (hp_n' = 1 ∨ (1 ≤ hp_n' ∧ hp_n' < nsz')) ∧
            S13OtfsShrinkInv c s ar1 cref l0 uip old_sz (old_sz - (i_nat + 1)) (i_nat + 1)
              nsz' ar' omap') ?_ ?_
      · rintro _ ⟨nszv', hpv', hlv', ⟨⟩⟩ ml' ⟨nsz', hp_n', ar', omap', hm', rfl, rfl, hhp', hinv'⟩
        fa_fast_steps; rw [m5_bv32_ofNat_add1]
        exact ih2 (old_sz - (i_nat + 1)) _ ml' (by omega)
          ⟨i_nat + 1, nsz', hp_n', ar', omap', hm', rfl, rfl, rfl, hhp', hinv'⟩
      · intro J2 hJ2; fa_fast_steps_nogrp
        · have hlv_pos := s13_otfs_p2_lv_pos har_bd hv_bd hs2_lvl hot_c_eq
            (by exact hc)
          let ar' := ar_cur.set (cref.toNat + 3 + nsz) (s.core.arena[cref.toNat + 3 + i_nat]'har_bd)
          let ar'_raw := ar_cur.set (cref.setWidth 64 + 3#64 +
              (BitVec.ofNat 32 nsz).setWidth 64).toNat
            (ar_cur[(cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i_nat).setWidth 64).toNat]'hc_z_bd)
          have har_st_eq : ar'_raw = ar' := by
            dsimp only [ar'_raw, ar']; rw [hnsz_z, hot_z_eq]
          have hm_st : (FullMem c { s2 with core := { s2.core with arena := ar' } } ⋆ R) _ :=
            m5_fullMem_of_eq (s1 := { s2 with core := { s2.core with arena := ar'_raw } })
              (by assumption) (congrArg (fun a => { s2.core with arena := a }) har_st_eq) rfl
          have hstep_ok := s13_otfs_shrink_loop_step har_len hinv_l hilt (by omega) hlv_pos
          refine wp_join_group (ts := [i32, i32]) (fun (hpv', _hlv', ()) ml' => ∃ hp_n' : Nat,
            (FullMem c { s2 with core := { s2.core with arena := ar' } } ⋆ R) ml' ∧
            hpv' = BitVec.ofNat 32 hp_n' ∧ (hp_n' = 1 ∨ (1 ≤ hp_n' ∧ hp_n' < nsz + 1))) ?_ ?_
          · rintro _ ⟨hpv', hlv', ⟨⟩⟩ ml' ⟨hp_n', hm_st', rfl, hhp'⟩
            fa_fast_steps; rw [m5_bv32_ofNat_add1]
            exact hJ2 _ _ ⟨nsz + 1, hp_n', ar', origMap ++ [i_nat], hm_st', rfl, rfl, hhp',
              hstep_ok⟩
          · intro Jhp hJhp; fa_fast_steps
            · exact hJhp _ _ ⟨nsz, hm_st, rfl, Or.inr ⟨hns1, Nat.lt_succ_self _⟩⟩
            · exact hJhp _ _ ⟨hp_n, hm_st, rfl,
                hhp_ok.imp_right fun ⟨h1, h2⟩ => ⟨h1, Nat.lt_succ_of_lt h2⟩⟩
        · exact hJ2 _ _ ⟨nsz, hp_n, ar_cur, origMap, hm_c, rfl, rfl, hhp_ok,
            s13_otfs_p2_skip_inv hinv_l hilt har_bd hv_bd hs2_lvl hot_c_eq
              (by exact hc)⟩
    · have hilt : i_nat = old_sz := by
        have hba : ¬ (BitVec.ofNat 32 i_nat).toNat < (BitVec.ofNat 32 old_sz).toNat := ‹_›
        rw [bv32_ofNat_toNat (by omega), bv32_ofNat_toNat (by omega)] at hba; omega
      subst i_nat
      have hnsz3 : 3 ≤ nsz := by rw [hact]; exact hcnt3
      have hnsz_lt : nsz < old_sz := by rw [hact]; exact hact_lt
      have hhp1 : 1 ≤ hp_n := hhp_ok.elim (fun h => by omega) And.left
      have hhp_lt : hp_n < nsz := hhp_ok.elim (fun h => by omega) And.right
      have har_c_0 : (cref.setWidth 64).toNat < ar_cur.length := by rw [har_c, hcr0_z]; omega
      have har_c_1 : (cref.setWidth 64 + 1#64).toNat < ar_cur.length := by rw [har_c, hcr1_z]; omega
      have har_c_2 : (cref.setWidth 64 + 2#64).toNat < ar_cur.length := by rw [har_c, hcr2_z]; omega
      have hhdr_eq : ar_cur[cref.toNat]? = some (fullArenaHdrCore s2.core cref.toNat) := by
        rw [hout_m cref.toNat (Or.inl (by omega))]
        unfold fullArenaHdrCore
        rw [hs2_base, List.getElem?_eq_getElem (by rw [har1_l]; omega), Option.getD_some]
      have hhdr_s2 : ar_cur[(cref.setWidth 64).toNat]'har_c_0 =
          fullArenaHdrCore s2.core cref.toNat := by
        have hg := hhdr_eq; rw [List.getElem?_eq_getElem (by rw [har_c]; omega)] at hg
        exact (m5_list_getElem_of_idx hcr0_z).trans (Option.some.inj hg)
      fa_fast_steps_nogrp
      exact s13_otfs_j3_hdr_wp _ har_len har_c hfl_len2 h3o hcap31 h4_old hnsz3 hnsz_lt
        hcr0_z hcr1_z hcr2_z hcr3_z hhdr_s2 rfl rfl h2cv_lt hcv_le hu_lt hlits_info hlm hlt_m
        hmapeq hout_m har1_q har1_s2 hhdr_eq (by assumption) fun ml3 hpost3 =>
          s13_otfs_post_j3_wp hlen hw hnd hlen2 hw2 hnd2 hdm hsp_oom _hws2 hs2_base hs2_sc hrefs2
            hcref hng hcref2 hng2 hsz_orig hsz2 hiu_cut hiu_te ht_u hr_u hlev_u hent_f hcap31
            h2cv_lt hl0_lt hcr_lt31 h3o hnsz3 hnsz_lt hhp1 hhp_lt hcr4_z hcb1_eq hlm hpw hlt_m
            h01 hcov hpost3 hQ
  · intro L2 hL2; fa_fast_steps
    subst har1_def
    have hs2_ar : s2.core.arena =
        (s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip := by
      rw [hs2_base]
    obtain ⟨omap0, hinv0⟩ := s13_otfs_loop2_init har_len h3o h4_old hs01
    exact hL2 (old_sz - 2) _ m2 ⟨2, 1, 1, _, omap0,
      m5_fullMem_of_eq (s1 := s2) hm2 (by rw [hs2_base]) rfl, rfl, rfl, rfl, Or.inl rfl,
      hs2_ar ▸ hinv0⟩

/-- Canonical `Func.wp` proof for `full_otfs_large` (`step13OtfsLargeSpec`): early `cnt >= 3` exit,
read-only `nl1_pre` scan, headroom check + `full_wstack_defrag` + `full_watch_push` before arena
swap and `full_unwatch_large(uip)`, fused compaction + `hp`, Step-13 `PH_RED` glue tightening /
`!PH_RED` `flags |= 24u` + `PH_SHRK`, `hp` swap, and `l0` blocker update. -/
theorem full_otfs_large_step13_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hUnw : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, step13OtfsLargeSpec a m Q X →
      Func.wp Γ fidStep13S2OtfsLargeFn.body a m Q X := by
  rintro ⟨h, cref, uip, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, cut, idx_u, s, R, rfl, hlen, hw_can, hnd, hdm, hcref, hng, hu_lt,
      hiu_cut, ht_u, hr_u, hlev_u, hent_f, hm, hQ⟩
  have hiu_te : idx_u < s.core.trail_end := Nat.lt_of_lt_of_le hiu_cut hw_can.cut_le
  have hw := m5_canonCut_to_anaCut hw_can
  have hwf := hw.arena.refs_wf cref.toNat hcref
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hlvl_len := hlen.core_ok.lvl_len
  have hcv_le := hlen.core_ok.cur_vars_le; have hcap31_orig := c.harena; have hmaxv := c.hmaxv
  have hwcap_orig := c.hwcap; unfold dimacsBound at hcap31_orig hmaxv hwcap_orig
  have hcap31 : c.arena_cap < 2 ^ 31 - 1 := by omega
  have h2cv_lt : 2 * s.core.cur_vars < 2 ^ 31 - 1 := by omega
  let old_sz := fullArenaClauseSizeCore s.core cref.toNat
  have hold_bd : cref.toNat + 3 + old_sz ≤ s.core.arena_len := by
    have := hwf.2.2.1; have := hwf.2.2.2.1; dsimp only [old_sz]; omega
  have h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap := Nat.le_trans hold_bd har_le
  have hlits_info : ∀ j < old_sz,
      (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ≠ 0xFFFFFFFF#32 := fun j hj => by
    have hm_j : (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat ∈
        fullArenaClauseLits s cref.toNat := by
      simp only [fullArenaClauseLits, fullArenaClauseLitsCore, List.mem_map]
      refine ⟨s.core.arena[cref.toNat + 3 + j]'(by omega), List.mem_iff_getElem.mpr
        ⟨j, by simp; omega, by simp [List.getElem_take, List.getElem_drop]⟩,
        by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]⟩
    have hl_lt := hw.arena.lits_lt cref.toNat hcref hng _ hm_j
    exact ⟨hl_lt, bv32_lit_neq_ff (Nat.lt_trans hl_lt h2cv_lt)⟩
  have hcr0_z : (cref.setWidth 64).toNat = cref.toNat := zext_toNat cref (by decide)
  have hcr_add {k : Nat} (hk : cref.toNat + k < 2 ^ 64) (hk' : k < 2 ^ 64) :
      (cref.setWidth 64 + BitVec.ofNat 64 k).toNat = cref.toNat + k := by
    rw [BitVec.toNat_add, hcr0_z, bv64_ofNat_toNat hk']; omega
  have hcr1_z := hcr_add (k := 1) (by omega) (by decide)
  have hcr2_z := hcr_add (k := 2) (by omega) (by decide)
  have hcr3_z := hcr_add (k := 3) (by omega) (by decide)
  have hcr4_z := hcr_add (k := 4) (by omega) (by decide)
  have hcb1_eq : cref.setWidth 64 + 3#64 + 1#64 = cref.setWidth 64 + 4#64 := by bv_omega
  have hcb1_z : (cref.setWidth 64 + 3#64 + 1#64).toNat = cref.toNat + 4 := by
    rw [hcb1_eq]; exact hcr4_z
  have hsz_eq : (s.core.arena[cref.toNat + 2]'(by omega)).toNat = old_sz := by
    unfold old_sz fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hsz32 : s.core.arena[cref.toNat + 2]'(by omega) = BitVec.ofNat 32 old_sz :=
    BitVec.eq_of_toNat_eq (by rw [hsz_eq, bv32_ofNat_toNat (by omega)])
  have hcr3_bd : (cref.setWidth 64 + 3#64).toNat < s.core.arena.length := by rw [hcr3_z]; omega
  have hcb1_bd : (cref.setWidth 64 + 3#64 + 1#64).toNat < s.core.arena.length := by
    rw [hcb1_z]; omega
  let orig0 := s.core.arena[cref.toNat + 3]?.getD 0#32
  let orig1 := s.core.arena[cref.toNat + 4]?.getD 0#32
  have hor0 : s.core.arena[(cref.setWidth 64 + 3#64).toNat]'hcr3_bd = orig0 := by
    rw [m5_list_getElem_of_idx (hj := by omega) hcr3_z]
    simp [orig0, List.getElem?_eq_getElem (by omega : cref.toNat + 3 < s.core.arena.length)]
  have hor1 : s.core.arena[(cref.setWidth 64 + 3#64 + 1#64).toNat]'hcb1_bd = orig1 := by
    rw [m5_list_getElem_of_idx (hj := by omega) hcb1_z]
    simp [orig1, List.getElem?_eq_getElem (by omega : cref.toNat + 4 < s.core.arena.length)]
  have hfail : Q (false, ()) m :=
    hQ false s.core.flags s.core.arena s.core.wvec s.core.wstk s.core.wlen s.core.wusable s.core.oom
      s.scratch _ hlen (m5_canonCut_shrink_cut hw_can (Nat.le_of_lt hiu_cut)) hnd ⟨rfl, rfl⟩
      rfl rfl rfl rfl (fun h => by cases h) hm
  dsimp only [Func.wp, fidStep13S2OtfsLargeFn]; unfold full_otfs_large_body; fa_fast_steps_nogrp
  refine wp_join_group (ts := [i32]) (fun p ml0 => ml0 = m ∧
      ((p.1 = orig0 ∧ orig1 = uip) ∨ (p.1 = orig1 ∧ orig0 = uip))) ?_ ?_
  · rintro _ ⟨l0, ⟨⟩⟩ ml0 ⟨hml0, hs01⟩; subst ml0
    have hl0_lt : l0.toNat < 2 * s.core.cur_vars := by
      rcases hs01 with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact (hlits_info 0 (by omega)).1
      · exact (hlits_info 1 (by omega)).1
    have hcr2_bd : (cref.setWidth 64 + 2#64).toNat < s.core.arena.length := by rw [hcr2_z]; omega
    fa_fast_steps_nogrp
    refine wp_loop_break_group (brkTs := [i32, i32]) (lpTs := [i32, i32])
      (fun (cnt, _iv, ()) ml => ml = m ∧
        (cnt.toNat < 3 ∨ 3 ≤ 1 + Full.otfsActCnt s.core cref.toNat old_sz))
      (fun r (cnt, iv, ()) ml => ∃ i_nat : Nat,
        ml = m ∧ r = old_sz - i_nat ∧ 2 ≤ i_nat ∧ i_nat ≤ old_sz ∧ iv = BitVec.ofNat 32 i_nat ∧
        cnt = BitVec.ofNat 32 (1 + Full.otfsActCnt s.core cref.toNat i_nat) ∧
        1 + Full.otfsActCnt s.core cref.toNat i_nat < 3) ?_ ?_ ?_
    · rintro _ ⟨cnt, iv, ⟨⟩⟩ ml ⟨hml, hcnt_res⟩; subst ml; fa_fast_steps_nogrp
      · exact hfail
      · have hcnt3 : 3 ≤ 1 + Full.otfsActCnt s.core cref.toNat old_sz :=
          hcnt_res.resolve_left (by simpa using (‹¬ cnt.toNat < (3#32).toNat›))
        have hact_lt : 1 + Full.otfsActCnt s.core cref.toNat old_sz < old_sz := by
          have := Full.otfsActCnt_le s.core cref.toNat old_sz; omega
        have h4_old : 4 ≤ old_sz := by omega
        refine wp_loop_group (fun r (iv1b, _hlp, nl1p, ()) ml => ∃ i_b : Nat, ml = m ∧
          r = old_sz - i_b ∧ 2 ≤ i_b ∧ i_b ≤ old_sz ∧ iv1b = BitVec.ofNat 32 i_b ∧
          nl1p.toNat < 2 * s.core.cur_vars) ?_ ?_
        · rintro L1b r1b ⟨iv1b, hlp, nl1p, ⟨⟩⟩ ml ih1b
            ⟨i_b, hml1b, rfl, hib2, hible, rfl, hnl1p_lt⟩
          subst ml; fa_fast_steps_nogrp
          · have hib_lt : i_b < old_sz := by
              have hb : (BitVec.ofNat 32 i_b).toNat <
                  (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd).toNat := ‹_›
              rw [bv32_ofNat_toNat (by omega), m5_list_getElem_of_idx (hj := by omega) hcr2_z,
                hsz_eq] at hb; exact hb
            obtain ⟨har_bd, hz_bd, hc_bd, hc_idx, hot_eq, _, hlvl1_bd_len, hv_bd⟩ :=
              s13_otfs_loop1_step_bds hcap31 hcv_le hlvl_len har_len h3o hib_lt hlits_info
            have hot_lt' : (s.core.arena[(cref.setWidth 64 + 3#64 +
                (BitVec.ofNat 32 i_b).setWidth 64).toNat]'hz_bd).toNat < 2 * s.core.cur_vars := by
              rw [m5_list_getElem_of_idx (m5_otfs_bv_idx3_64 cref i_b (by omega) (by omega))]
              have h1 := (hlits_info i_b hib_lt).1
              rwa [List.getElem?_eq_getElem har_bd, Option.getD_some] at h1
            fa_fast_steps_nogrp
            refine wp_join_group (ts := [i32, i32]) (fun (_hlp', nl1', ()) ml' =>
              ml' = m ∧ nl1'.toNat < 2 * s.core.cur_vars) ?_ ?_
            · rintro _ ⟨hlp', nl1', ⟨⟩⟩ ml' ⟨hml', hnl1'⟩; subst ml'; fa_fast_steps
              rw [m5_bv32_ofNat_add1]
              exact ih1b (old_sz - (i_b + 1)) _ m (by omega)
                ⟨i_b + 1, rfl, rfl, by omega, by omega, rfl, hnl1'⟩
            · intro J1b hJ1b; fa_fast_steps
              · exact hJ1b _ _ ⟨rfl, hot_lt'⟩
              · exact hJ1b _ _ ⟨rfl, hnl1p_lt⟩
          · have hcf_done : i_b = old_sz := by
              have hba : ¬ (BitVec.ofNat 32 i_b).toNat <
                  (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd).toNat := ‹_›
              rw [bv32_ofNat_toNat (by omega), m5_list_getElem_of_idx (hj := by omega) hcr2_z,
                hsz_eq] at hba; omega
            clear hcf_done
            have hl0_p := bv32_lit_lo31_props (l := l0) (by omega)
            have hcr_ne : cref ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff (by omega)
            have hcr_lt31 : cref.toNat < 0x80000000 := by omega
            have hl0_m_ne : l0 &&& 0x7FFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
              rw [hl0_p.1]; exact bv32_lit_neq_ff (by omega)
            fa_fast_steps_nogrp
            refine wp_join_group (ts := []) (fun () ml_d =>
              ∃ (s_d : FullState) (wv_d ws_d : List (BitVec 32)) (wl_d : Nat) (wu_d : BitVec 64)
                (wso_d : List (BitVec 32)),
                s_d.core = { s.core with wvec := wv_d, wstk := ws_d, wlen := wl_d,
                                         wusable := wu_d } ∧
                s_d.scratch = { s.scratch with wsort := wso_d } ∧
                s_d.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut s_d.core ∧
                (FullMem c s_d ⋆ R) ml_d) ?_ ?_
            · rintro _ ⟨⟩ ml_d ⟨s_d, wv_d, ws_d, wl_d, wu_d, wso_d, hsd_c, hsd_sc, hlen_d, hw_d,
                hm_d⟩
              have hsd_cv : s_d.core.cur_vars = s.core.cur_vars := by rw [hsd_c]
              have hsd_dm : s_d.core.dense_mode = 0#64 := by rw [hsd_c]; exact hdm
              have hcref_d : cref.toNat ∈ fullArenaClauseRefsCore s_d.core := by
                change cref.toNat ∈ fullArenaClauseRefsCore s.core at hcref
                rwa [show fullArenaClauseRefsCore s_d.core = fullArenaClauseRefsCore s.core by
                  simp [fullArenaClauseRefsCore, hsd_c]]
              c0_call (m5_anaWatchPush_adapter hPush)
              · refine ⟨c, s_d, R, rfl, hlen_d, by
                  have h := hw_d.watches; unfold ModeWatchesInv at h
                  simp only [hsd_dm, ↓reduceIte] at h; exact h.layout,
                  fun h => absurd h (by decide), fun _ => ⟨hl0_m_ne, hcr_ne⟩, hm_d,
                  fun ok_p wv_p ws_p wl_p wu_p wso_p m_p hlen_p hlay_p hother_p hok_pt hok_pf
                    hm_p => ?_⟩
                clear hm_d
                obtain ⟨s_p, hsp_d_eq, hm_p'⟩ : ∃ s_p : FullState,
                    s_p = { s_d with
                      core := { s_d.core with wvec := wv_p, wstk := ws_p, wlen := wl_p,
                                              wusable := wu_p }
                      scratch := { s_d.scratch with wsort := wso_p } } ∧
                    (FullMem c s_p ⋆ R) m_p := ⟨_, rfl, hm_p⟩
                clear hm_p
                have hsp_c : s_p.core = { s.core with wvec := wv_p, wstk := ws_p, wlen := wl_p,
                                                      wusable := wu_p } := by
                  rw [hsp_d_eq]; dsimp only; rw [hsd_c]
                have hsp_sc : s_p.scratch = { s.scratch with wsort := wso_p } := by
                  rw [hsp_d_eq]; dsimp only; rw [hsd_sc]
                have hlen_p' : s_p.LengthsOk c := by
                  rw [hsp_d_eq]; exact ⟨{ hlen_p.core_ok with }, hlen_p.scratch_ok⟩
                have hsp_w_eq : s_p.core = { s_d.core with
                    wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p } :=
                  congrArg FullState.core hsp_d_eq
                by_cases hok_pt_c : ok_p = true
                · subst hok_pt_c
                  obtain ⟨_, _, hsz_p, hsame_p, hw0_p, hw1_p⟩ := hok_pt rfl
                  have hm_wp : ModeWatchesInv F_cur s_p.core := by
                    rw [hsp_w_eq]
                    exact fa_watchPush_large_preserves hsd_dm hw_d.watches
                      (by rw [hsd_cv]; exact hnl1p_lt) hlay_p hother_p hsz_p hsame_p hw0_p
                      (hw1_p rfl) hl0_p.2.1 hcr_lt31 hcref_d
                  have hw_p : FullWitnessCutInv c F0 F_cur cut s_p.core := by
                    rw [hsp_w_eq] at hm_wp ⊢; exact m5_canonCut_with_watches hw_d hm_wp
                  have hsp3_bd : (cref.setWidth 64 + 3#64).toNat < s_p.core.arena.length := by
                    rw [hsp_c]; exact hcr3_bd
                  have hsp4_bd : (cref.setWidth 64 + 3#64 + 1#64).toNat <
                      (s_p.core.arena.set (cref.setWidth 64 + 3#64).toNat l0).length := by
                    rw [List.length_set, hsp_c]; exact hcb1_bd
                  fa_fast_steps_nogrp
                  obtain ⟨s1, hs1_c, hs1_sc, hm1', hlen1, hw1', hnd1', hrefs1', hsz1', hng1',
                    har1_q'⟩ :=
                    s13_otfs_swap01_s1 hlen hnd hdm hcref hng hs01 hsp_c hsp_sc hlen_p' hw_p
                      hcr3_z hcb1_z hcr3_bd hcb1_bd (by assumption)
                  c0_call hUnw
                  · refine ⟨c, s1, R, rfl, hlen1, by
                      have h := hw1'.watches; unfold ModeWatchesInv at h
                      rw [show s1.core.dense_mode = 0#64 by rw [hs1_c]; exact hdm] at h
                      simp only [↓reduceIte] at h; exact h.layout, hm1',
                      fun wv2 ws2 wu2 m2 hlen2 _ hmw2 hm2 => ?_⟩
                    obtain ⟨s2, hs2_base, hs2_sc, hm2_s2, hlen2', hw2, hnd2, hrefs2, hsz2, hng2⟩ :=
                      s13_otfs_s2_of_unwatch hs1_c hs1_sc hlen2 hmw2 hm2 hw1' hnd1' hrefs1' hsz1'
                        hng1'
                    have hs2_o : s.core.oom = s2.core.oom := by rw [hs2_base]
                    have hs2_w : s2.core.wstk = ws2 := by rw [hs2_base]
                    have har1_l : ((s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4)
                        uip).length = c.arena_cap := by simp [har_len]
                    have har1_s2 : ∀ i, i < cref.toNat + 3 ∨ cref.toNat + 5 ≤ i →
                        ((s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip)[i]? =
                          s2.core.arena[i]? := by
                      rw [hs2_base]; exact fun _ _ => rfl
                    have hs2_wvec : s2.core.wvec = wv2 := by rw [hs2_base]
                    have hs2_wlen : s2.core.wlen = wl_p := by rw [hs2_base]
                    have hs2_wu : s2.core.wusable = wu2 := by rw [hs2_base]
                    have hs2_base' : s2.core = { s.core with
                        arena := (s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip,
                        wvec := s2.core.wvec, wstk := ws2, wlen := s2.core.wlen,
                        wusable := s2.core.wusable } := by
                      rw [hs2_wvec, hs2_wlen, hs2_wu]; exact hs2_base
                    fa_fast_steps_nogrp
                    exact s13_otfs_shrink_tail_wp hlen hw hnd hlen2' hw2 hnd2 hdm hs2_o hs2_w
                      hs2_base' hs2_sc hrefs2 hcref hng (hrefs2 ▸ hcref) hng2 rfl hsz2
                      ((m5_list_getElem_of_idx (hj := by omega) hcr2_z).trans hsz32)
                      hiu_cut hiu_te ht_u hr_u hlev_u hent_f hcap31 h2cv_lt hl0_lt hu_lt hcr_lt31
                      h3o h4_old hcnt3 hact_lt hcr0_z hcr1_z hcr2_z hcr3_z hcr4_z hcb1_eq hs01
                      hlits_info rfl har1_l har1_q' har1_s2 hm2_s2 hQ
                · have hok_f : ok_p = false := Bool.eq_false_iff.mpr hok_pt_c
                  subst hok_f; obtain ⟨hsame_f, _⟩ := hok_pf rfl
                  have hm_wpf : ModeWatchesInv F_cur s_p.core := by
                    rw [hsp_w_eq]
                    exact fa_watchPush_fail_preserves hsd_dm hw_d.watches hlay_p fun l hl =>
                      if hle : l = nl1p.toNat then
                        by subst l; exact hsame_f (by rw [hsd_cv]; exact hnl1p_lt)
                      else hother_p l hl hle
                  have hw_pf : FullWitnessCutInv c F0 F_cur cut s_p.core := by
                    rw [hsp_w_eq] at hm_wpf ⊢; exact m5_canonCut_with_watches hw_d hm_wpf
                  fa_fast_steps
                  exact s13_otfs_oom_early_wp hsp_c hsp_sc hlen_p' hw_pf hnd hiu_cut
                    (by assumption) hQ
            · intro Jd hJd
              exact m5_wstack_ensure2_ret_false_wp hDefrag hlen hdm hw_can.watches hm
                (fun s_i wv_i ws_i wl_i wu_i wso_i ml_o hsi_c hsi_sc hlen_i hmw_i hm_o =>
                  s13_otfs_oom_early_wp hsi_c hsi_sc hlen_i (by
                    have hw_i : FullWitnessCutInv c F0 F_cur cut s_i.core := by
                      rw [hsi_c] at hmw_i ⊢; exact m5_canonCut_with_watches hw_can hmw_i
                    exact hw_i) hnd hiu_cut hm_o hQ)
                (fun xs ml_d ⟨s_d, wv_d, ws_d, wl_d, wu_d, wso_d, hsd_c, hsd_sc, hlen_d, hmw_d,
                    hm_d⟩ =>
                  hJd xs ml_d ⟨s_d, wv_d, ws_d, wl_d, wu_d, wso_d, hsd_c, hsd_sc, hlen_d, by
                    rw [hsd_c] at hmw_d ⊢; exact m5_canonCut_with_watches hw_can hmw_d, hm_d⟩)
        · intro L1b hL1b; fa_fast_steps
          exact hL1b (old_sz - 2) _ m ⟨2, rfl, rfl, Nat.le_refl _, by omega, rfl, hu_lt⟩
    · rintro B1 L1 r ⟨cnt, iv, ⟨⟩⟩ ml hB1 ih1 ⟨i_nat, hml, rfl, hi2, hile, rfl, rfl, hcnt_lt3⟩
      subst ml; fa_fast_steps_nogrp
      · have hilt : i_nat < old_sz := by
          have hb : (BitVec.ofNat 32 i_nat).toNat <
              (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd).toNat := ‹_›
          rw [bv32_ofNat_toNat (by omega), m5_list_getElem_of_idx (hj := by omega) hcr2_z,
            hsz_eq] at hb; exact hb
        obtain ⟨har_bd, hz_bd, hc_bd, hc_idx, hot_eq, _, hlvl1_bd_len, hv_bd⟩ :=
          s13_otfs_loop1_step_bds hcap31 hcv_le hlvl_len har_len h3o hilt hlits_info
        fa_fast_steps_nogrp
        refine wp_join_group (ts := [i32]) (fun (cnt', ()) ml' => ml' = m ∧
            cnt' = BitVec.ofNat 32 (1 + Full.otfsActCnt s.core cref.toNat (i_nat + 1)) ∧
            1 + Full.otfsActCnt s.core cref.toNat (i_nat + 1) < 3) ?_ ?_
        · rintro _ ⟨cnt', ⟨⟩⟩ ml' ⟨hml', rfl, hlt3'⟩; subst ml'; fa_fast_steps
          rw [m5_bv32_ofNat_add1]
          exact ih1 (old_sz - (i_nat + 1)) _ m (by omega)
            ⟨i_nat + 1, rfl, rfl, by omega, by omega, rfl, rfl, hlt3'⟩
        · intro J1 hJ1; fa_fast_steps
          · have hlv_pos := s13_otfs_p1_lv_pos har_bd hv_bd hot_eq ‹BitVec.toNat 0 < _›
            exact hB1 _ m ⟨rfl, Or.inr (s13_otfs_p1_brk hi2 hilt hlv_pos hcnt_lt3 hc)⟩
          · have hlv_pos := s13_otfs_p1_lv_pos har_bd hv_bd hot_eq ‹BitVec.toNat 0 < _›
            obtain ⟨hceq, hlt3'⟩ := s13_otfs_p1_inc hi2 hlv_pos hcnt_lt3 hc
            rw [hceq]; exact hJ1 _ _ ⟨rfl, rfl, hlt3'⟩
          · have hlv_0 := s13_otfs_p1_lv_zero har_bd hv_bd hot_eq ‹¬ BitVec.toNat 0 < _›
            have hcnt_eq : Full.otfsActCnt s.core cref.toNat (i_nat + 1) =
                Full.otfsActCnt s.core cref.toNat i_nat := by
              rw [Full.otfsActCnt_succ hi2, ite_eq_right hlv_0, Nat.add_zero]
            exact hJ1 _ _ ⟨rfl, congrArg (fun x => BitVec.ofNat 32 (1 + x)) hcnt_eq.symm,
              by rw [hcnt_eq]; exact hcnt_lt3⟩
      · have heq : i_nat = old_sz := by
          have hb : ¬ (BitVec.ofNat 32 i_nat).toNat <
              (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd).toNat := ‹_›
          rw [bv32_ofNat_toNat (by omega), m5_list_getElem_of_idx (hj := by omega) hcr2_z,
            hsz_eq] at hb; omega
        subst i_nat
        exact hB1 _ m ⟨rfl, Or.inl (by rw [bv32_ofNat_toNat (by omega)]; exact hcnt_lt3)⟩
    · intro B1 L1 _ hL1; fa_fast_steps
      exact hL1 (old_sz - 2) (1#32, 2#32, ()) m ⟨2, rfl, rfl, Nat.le_refl _, by omega, rfl,
        rfl, by rw [show Full.otfsActCnt s.core cref.toNat 2 = 0 from rfl]; omega⟩
  · intro Jl0 hJl0; fa_fast_steps
    · have h0_eq : s.core.arena[(cref.setWidth 64 + 3#64).toNat]'hcr3_bd = uip := ‹_›
      exact hJl0 _ _ ⟨rfl, Or.inr ⟨hor1, hor0.symm.trans h0_eq⟩⟩
    · exact hfail
    · have h1_eq : s.core.arena[(cref.setWidth 64 + 3#64 + 1#64).toNat]'hcb1_bd = uip := by
        refine (m5_list_getElem_of_idx (j := (cref.toNat + BitVec.toNat (3 : BitVec 64) +
          BitVec.toNat (1 : BitVec 64)) % 2 ^ 64) ?_).trans hc
        rw [hcb1_z]; simp only [BitVec.reduceToNat]; omega
      exact hJl0 _ _ ⟨rfl, Or.inl ⟨hor0, hor1.symm.trans h1_eq⟩⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S2
