module

public import LeanQbe.T.Examples.Kissat.FullM5ProbeProp
public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Examples.Kissat.FullFastCoreLemmas
public import LeanQbe.T.Examples.Kissat.FullProbeTransLemmas5

/-!
# Kissat M5 `full_probe_prop_lit_m5` Proof & UNSAT NV (`FullM5ProbePropProof`)

Proves:
1. `full_probe_prop_lit_m5_wp` against unchanged canonical `Full.fullProbePropLitSpec`
   (`FullSpec3.lean:473`), with satisfied blocking literal `vals[blk] > 0` checked before
   `PW_BIN_FLAG` and clean local probing ticks (zero `h->search_ticks` contamination).
2. Closed `m5ProbeProp_tableImpl` and `m5ProbeProp_moduleOk : ModuleOk m5ProbePropEnv
   m5ProbePropModule`.
3. Concrete `Mem 64` binary-watch UNSAT non-vacuity `nv_m5_probe_prop_sound` (`XPost := False`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5ProbeProp

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Full hiding
  full_probe_prop_lit_body full_probe_prop_lit_wf full_probe_prop_lit_wp
  full_probe_prop_lit_ext_wp bv64_add1_toNat
open FullProbeTransSpecs hiding
  fullHbrDomSpec fullFindReplSpec fullWatchPushSpec fullAssignLvlSpec FullMrkZero
open FullProbeTransHelpers
open scoped FullArenaTactics FullProbeTransTactics

section LocalHelpers

private theorem pt_vals_ne_ff_of_sgt_or_zero {vals : List (BitVec 8)} {i : Nat}
    (hi : i < vals.length) (hv : vals[i]?.getD 0#8 = 0xFF#8) :
    ((vals[i]'hi).signExtend 32).slt 0#32 = true := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some] at hv; rw [hv]; decide

private theorem entails_bin_swap {F : CNF Nat} {a b : Nat}
    (h : F.EntailsClause (cnfClause [a, b])) : F.EntailsClause (cnfClause [b, a]) := by
  rw [CNF.entails_clause_def] at h ⊢
  intro α hα
  obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α _).mp (h α hα)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  exact (clause_sat_cnfClause_iff α _).mpr ⟨l, by simp [hl.symm], hsat⟩

private theorem pt_vals_eq_1_of_sgt' {vals : List (BitVec 8)} {i : Nat} (hi : i < vals.length)
    (hdom : vals[i]?.getD 0#8 = 0#8 ∨ vals[i]?.getD 0#8 = 1#8 ∨ vals[i]?.getD 0#8 = 0xFF#8)
    (hsgt : (0#32).slt ((vals[i]'hi).signExtend 32) = true) : vals[i]?.getD 0#8 = 1#8 := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some] at hdom ⊢; exact (i8_vals_sgt0 hdom).mp hsgt

private theorem bv32_mask7f_toNat_eq {x : BitVec 32} (hx : x.toNat < 2 ^ 31) :
    (x &&& 0x7FFFFFFF#32).toNat = x.toNat :=
  bv32_mask7f_toNat_lt (by omega)

private theorem bv32_msb_zero_of_lt {x : BitVec 32} (hx : x.toNat < 0x80000000) :
    (x &&& 0x80000000#32) = 0#32 := by
  have h := bv32_mask7f_msb_zero x
  have hm : x &&& 0x7FFFFFFF#32 = x := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  rwa [hm] at h

private theorem arena_lit_ne_of_nodup {s : Full.FullState} {cref k1 k2 : Nat}
    (hnd : Full.FullArenaVarsNodup s) (hcref : cref ∈ Full.fullArenaClauseRefs s)
    (hng : Full.fullArenaClauseGarb s cref = false)
    (hbd : cref + 3 + Full.fullArenaClauseSize s cref ≤ s.core.arena.length)
    (hk1 : k1 < Full.fullArenaClauseSize s cref) (hk2 : k2 < Full.fullArenaClauseSize s cref)
    (hne : k1 ≠ k2) :
    (s.core.arena[cref + 3 + k1]'(by omega)).toNat ≠
      (s.core.arena[cref + 3 + k2]'(by omega)).toNat := by
  have hnod := hnd cref hcref hng
  have hlen : ((Full.fullArenaClauseLits s cref).map (· / 2)).length =
      Full.fullArenaClauseSize s cref := by
    rw [List.length_map]
    unfold Full.fullArenaClauseLits Full.fullArenaClauseLitsCore
    rw [List.length_map, List.length_take, List.length_drop, Nat.min_eq_left]
    change Full.fullArenaClauseSize s cref ≤ s.core.arena.length - (cref + 3); omega
  have hpw := List.pairwise_iff_getElem.mp hnod
  have hget : ∀ k (hk : k < Full.fullArenaClauseSize s cref),
      ((Full.fullArenaClauseLits s cref).map (· / 2))[k]'(by omega) =
        (s.core.arena[cref + 3 + k]'(by omega)).toNat / 2 := fun k hk => by
    rw [List.getElem_map]
    unfold Full.fullArenaClauseLits Full.fullArenaClauseLitsCore
    simp [List.getElem_take, List.getElem_drop]
  intro heq
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact absurd ((hget k1 hk1).trans (congrArg (· / 2) heq) |>.trans (hget k2 hk2).symm)
      (hpw k1 k2 (by omega) (by omega) hlt)
  · exact absurd ((hget k2 hk2).trans (congrArg (· / 2) heq.symm) |>.trans (hget k1 hk1).symm)
      (hpw k2 k1 (by omega) (by omega) hgt)

private theorem arena_setSrch_keep_inv {c : Full.FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : Full.FullState} (hlen : s.LengthsOk c)
    (hw : Full.FullWitnessInv c F0 F_cur (withEmptyModeWatches c s).core)
    (hnd : Full.FullArenaVarsNodup s) (hext : Full.FullExtScratchOk c s)
    {cref : Nat} {srch : BitVec 32} (hcref : cref ∈ Full.fullArenaClauseRefs s) :
    let s' : Full.FullState :=
      { s with core := { s.core with arena := s.core.arena.set (cref + 1) srch } }
    s'.LengthsOk c ∧ Full.FullWitnessInv c F0 F_cur (withEmptyModeWatches c s').core ∧
    Full.FullArenaVarsNodup s' ∧ Full.FullExtScratchOk c s' ∧
    Full.fullArenaClauseRefs s' = Full.fullArenaClauseRefs s := by
  intro s'
  obtain ⟨hw', hrefs, hper⟩ := arena_setSrch_preserves_nw hlen hw hcref (srch := srch)
  have hlen' : s'.LengthsOk c :=
    ⟨{ hlen.core_ok with arena_len_arr := by simp [s', hlen.core_ok.arena_len_arr] },
      hlen.scratch_ok⟩
  exact ⟨hlen', hw', fullArenaVarsNodup_of_lits_perm hnd hrefs fun r hr hg =>
    ⟨(hper r hr).2.1.symm.trans hg, (hper r hr).2.2⟩,
    ⟨fullLastLearnedWf_of_refs_eq hext.1 rfl hrefs, hext.2⟩, hrefs⟩

end LocalHelpers

/-! ## 1. Large-Clause Continuation with Local Probing Ticks -/

private def m5PropLitLargeExpr (h_arg pVals pWvec pWstk pArena pHstk : Val i64)
    (not_lit : Val i32) (nlits_v : Val i64) (cr_v w0_v l0_v : Val i32)
    (ticks_v off_v p2_v q_v end_v : Val i64)
    (Jtail : Cont [i64, i64, i64, i64, i64, Ty.bool])
    (Jloop : Cont [i64, i64, i64, i64, i64]) : Expr Val Cont [Ty.bool] :=
  Expr.let_ ⟨.zext 32 64, (.var l0_v, ())⟩ fun p_77 =>
  Expr.let_ ⟨.cmp .uge i64, (.var p_77.fst, .var nlits_v, ())⟩ fun p_78 =>
  Expr.jnz (.var p_78.fst)
    (Expr.jump Jloop (.var off_v, .var ticks_v, .var p2_v, .var q_v, .var end_v, ()))
    (Expr.let_ ⟨.zext 32 64, (.var l0_v, ())⟩ fun p_79 =>
     Expr.let_ ⟨.add i64, (.var pVals, .var p_79.fst, ())⟩ fun p_80 =>
     Expr.load i8 (.var p_80.fst) fun ld =>
     Expr.let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p_81 =>
     Expr.let_ ⟨.sext 8 32, (.var ld, ())⟩ fun p_82 =>
     Expr.let_ ⟨.sext 8 32, (.var p_81.fst, ())⟩ fun p_83 =>
     Expr.let_ ⟨.cmp .sgt i32, (.var p_82.fst, .var p_83.fst, ())⟩ fun p_84 =>
     Expr.jnz (.var p_84.fst)
       (Expr.let_ ⟨.mul i64, (.var q_v, .imm 4, ())⟩ fun p =>
        Expr.let_ ⟨.add i64, (.var pWstk, .var p.fst, ())⟩ fun p =>
        Expr.let_ ⟨.and i32, (.var l0_v, .imm 2147483647, ())⟩ fun p_85 =>
        Expr.store (.var p_85.fst) (.var p.fst)
          (Expr.let_ ⟨.add i64, (.var q_v, .imm 1, ())⟩ fun p =>
           Expr.let_ ⟨.mul i64, (.var p.fst, .imm 4, ())⟩ fun p =>
           Expr.let_ ⟨.add i64, (.var pWstk, .var p.fst, ())⟩ fun p =>
           Expr.store (.var cr_v) (.var p.fst)
             (Expr.let_ ⟨.add i64, (.var q_v, .imm 2, ())⟩ fun p =>
              Expr.jump Jloop
                (.var off_v, .var ticks_v, .var p2_v, .var p.fst, .var end_v, ()))))
       (Expr.let_ ⟨.zext 32 64, (.var cr_v, ())⟩ fun p_85 =>
        Expr.call "full_find_repl" (as := [i64, i64]) (bs := [i64]) (.var h_arg, .var p_85.fst, ())
          fun p_86 =>
        Expr.let_ ⟨.cmp .ne i64, (.var p_86.fst, .imm 4294967295, ())⟩ fun p_87 =>
        Expr.jnz (.var p_87.fst)
          (Expr.let_ ⟨.add i64, (.var ticks_v, .imm 1, ())⟩ fun p_tk =>
           Expr.let_ ⟨.zext 32 64, (.var cr_v, ())⟩ fun p_88 =>
           Expr.let_ ⟨.add i64, (.var p_88.fst, .imm 3, ())⟩ fun p_89 =>
           Expr.let_ ⟨.add i64, (.var p_89.fst, .var p_86.fst, ())⟩ fun p_90 =>
           Expr.let_ ⟨.mul i64, (.var p_90.fst, .imm 4, ())⟩ fun p_91 =>
           Expr.let_ ⟨.add i64, (.var pArena, .var p_91.fst, ())⟩ fun p_92 =>
           Expr.load i32 (.var p_92.fst) fun ld =>
           Expr.let_ ⟨.zext 32 64, (.var cr_v, ())⟩ fun p_93 =>
           Expr.let_ ⟨.add i64, (.var p_93.fst, .imm 4, ())⟩ fun p_94 =>
           Expr.let_ ⟨.mul i64, (.var p_94.fst, .imm 4, ())⟩ fun p_95 =>
           Expr.let_ ⟨.add i64, (.var pArena, .var p_95.fst, ())⟩ fun p_96 =>
           Expr.store (.var ld) (.var p_96.fst)
             (Expr.let_ ⟨.zext 32 64, (.var cr_v, ())⟩ fun p_97 =>
              Expr.let_ ⟨.add i64, (.var p_97.fst, .imm 3, ())⟩ fun p_98 =>
              Expr.let_ ⟨.add i64, (.var p_98.fst, .var p_86.fst, ())⟩ fun p_99 =>
              Expr.let_ ⟨.mul i64, (.var p_99.fst, .imm 4, ())⟩ fun p_100 =>
              Expr.let_ ⟨.add i64, (.var pArena, .var p_100.fst, ())⟩ fun p_101 =>
              Expr.store (.var not_lit) (.var p_101.fst)
                (Expr.let_ ⟨.sub i64, (.var p2_v, .var off_v, ())⟩ fun p_102 =>
                 Expr.let_ ⟨.sub i64, (.var q_v, .var off_v, ())⟩ fun p_103 =>
                 Expr.let_ ⟨.sub i64, (.var end_v, .var off_v, ())⟩ fun p_104 =>
                 Expr.let_ ⟨.and i32, (.var l0_v, .imm 2147483647, ())⟩ fun p_105 =>
                 Expr.call "full_watch_push" (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
                   (.var h_arg, .var ld, .var p_105.fst, .var cr_v, .imm 2, ()) fun p_106 =>
                 Expr.let_ ⟨.zext 32 64, (.var not_lit, ())⟩ fun p_107 =>
                 Expr.let_ ⟨.sext 32 64, (.imm 1, ())⟩ fun p_108 =>
                 Expr.let_ ⟨.shl i64, (.var p_107.fst, .var p_108.fst, ())⟩ fun p_109 =>
                 Expr.let_ ⟨.mul i64, (.var p_109.fst, .imm 4, ())⟩ fun p_110 =>
                 Expr.let_ ⟨.add i64, (.var pWvec, .var p_110.fst, ())⟩ fun p_111 =>
                 Expr.load i32 (.var p_111.fst) fun ld_16 =>
                 Expr.let_ ⟨.zext 32 64, (.var ld_16, ())⟩ fun p_112 =>
                 Expr.let_ ⟨.add i64, (.var p_112.fst, .var p_102.fst, ())⟩ fun p_113 =>
                 Expr.let_ ⟨.add i64, (.var p_112.fst, .var p_103.fst, ())⟩ fun p_114 =>
                 Expr.let_ ⟨.add i64, (.var p_112.fst, .var p_104.fst, ())⟩ fun p_115 =>
                 Expr.jnz (.var p_106.fst)
                   (Expr.jump Jloop (.var p_112.fst, .var p_tk.fst, .var p_113.fst,
                     .var p_114.fst, .var p_115.fst, ()))
                   (Expr.let_ ⟨.zext 32 64, (.var cr_v, ())⟩ fun p_116 =>
                    Expr.let_ ⟨.add i64, (.var p_116.fst, .imm 4, ())⟩ fun p_117 =>
                    Expr.let_ ⟨.mul i64, (.var p_117.fst, .imm 4, ())⟩ fun p_118 =>
                    Expr.let_ ⟨.add i64, (.var pArena, .var p_118.fst, ())⟩ fun p_119 =>
                    Expr.store (.var not_lit) (.var p_119.fst)
                      (Expr.let_ ⟨.zext 32 64, (.var cr_v, ())⟩ fun p_120 =>
                       Expr.let_ ⟨.add i64, (.var p_120.fst, .imm 3, ())⟩ fun p_121 =>
                       Expr.let_ ⟨.add i64, (.var p_121.fst, .var p_86.fst, ())⟩ fun p_122 =>
                       Expr.let_ ⟨.mul i64, (.var p_122.fst, .imm 4, ())⟩ fun p_123 =>
                       Expr.let_ ⟨.add i64, (.var pArena, .var p_123.fst, ())⟩ fun p_124 =>
                       Expr.store (.var ld) (.var p_124.fst)
                         (Expr.let_ ⟨.mul i64, (.var p_114.fst, .imm 4, ())⟩ fun p_125 =>
                          Expr.let_ ⟨.add i64, (.var pWstk, .var p_125.fst, ())⟩ fun p_126 =>
                          Expr.store (.var w0_v) (.var p_126.fst)
                            (Expr.let_ ⟨.add i64, (.var p_114.fst, .imm 1, ())⟩ fun p_127 =>
                             Expr.let_ ⟨.mul i64, (.var p_127.fst, .imm 4, ())⟩ fun p_128 =>
                             Expr.let_ ⟨.add i64, (.var pWstk, .var p_128.fst, ())⟩ fun p_129 =>
                             Expr.store (.var cr_v) (.var p_129.fst)
                               (Expr.let_ ⟨.add i64, (.var p_114.fst, .imm 2, ())⟩ fun p_130 =>
                                Expr.let_ ⟨.add i64, (.var h_arg, .imm 760, ())⟩ fun p =>
                                Expr.store (t := i64) (.imm 1) (.var p.fst)
                                  (Expr.jump Jtail (.var p_112.fst, .var p_tk.fst,
                                    .var p_113.fst, .var p_130.fst, .var p_115.fst,
                                    .imm true, ()))))))))))
          (Expr.let_ ⟨.mul i64, (.var q_v, .imm 4, ())⟩ fun p_88 =>
           Expr.let_ ⟨.add i64, (.var pWstk, .var p_88.fst, ())⟩ fun p_89 =>
           Expr.let_ ⟨.and i32, (.var l0_v, .imm 2147483647, ())⟩ fun p_90 =>
           Expr.store (.var p_90.fst) (.var p_89.fst)
             (Expr.let_ ⟨.add i64, (.var q_v, .imm 1, ())⟩ fun p_91 =>
              Expr.let_ ⟨.mul i64, (.var p_91.fst, .imm 4, ())⟩ fun p_92 =>
              Expr.let_ ⟨.add i64, (.var pWstk, .var p_92.fst, ())⟩ fun p_93 =>
              Expr.store (.var cr_v) (.var p_93.fst)
                (Expr.let_ ⟨.add i64, (.var q_v, .imm 2, ())⟩ fun p_94 =>
                 Expr.let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p_95 =>
                 Expr.let_ ⟨.sext 8 32, (.var ld, ())⟩ fun p_96 =>
                 Expr.let_ ⟨.sext 8 32, (.var p_95.fst, ())⟩ fun p_97 =>
                 Expr.let_ ⟨.cmp .slt i32, (.var p_96.fst, .var p_97.fst, ())⟩ fun p_98 =>
                 Expr.jnz (.var p_98.fst)
                   (Expr.let_ ⟨.add i64, (.var h_arg, .imm 528, ())⟩ fun p_99 =>
                    Expr.store (t := i64) (.imm 2) (.var p_99.fst)
                      (Expr.let_ ⟨.zext 32 64, (.var cr_v, ())⟩ fun p_100 =>
                       Expr.let_ ⟨.add i64, (.var h_arg, .imm 176, ())⟩ fun p =>
                       Expr.store (.var p_100.fst) (.var p.fst)
                         (Expr.jump Jtail (.var off_v, .var ticks_v, .var p2_v,
                           .var p_94.fst, .var end_v, .imm true, ()))))
                   (Expr.let_ ⟨.add i64, (.var ticks_v, .imm 1, ())⟩ fun p_tk =>
                    Expr.call "full_hbr_dom" (as := [i64, i32, i32]) (bs := [i32])
                      (.var h_arg, .var cr_v, .var l0_v, ()) fun p_99 =>
                    Expr.group (sig := [[]]) (fun Js => Blocks.cons (fun _p_100 =>
                      Expr.call "full_assign_lvl" (as := [i64, i32, i32, i32]) (bs := [])
                        (.var h_arg, .var l0_v, .var cr_v, .imm 1, ()) fun _p =>
                      Expr.jump Jloop (.var off_v, .var p_tk.fst, .var p2_v, .var p_94.fst,
                        .var end_v, ()))
                      .nil)
                    fun Js =>
                    Expr.let_ ⟨.cmp .ne i32, (.var p_99.fst, .imm 4294967295, ())⟩ fun p_100 =>
                    Expr.jnz (.var p_100.fst)
                      (Expr.let_ ⟨.add i64, (.var h_arg, .imm 184, ())⟩ fun p_101 =>
                       Expr.load i64 (.var p_101.fst) fun ld =>
                       Expr.let_ ⟨.add i64, (.var h_arg, .imm 776, ())⟩ fun p_102 =>
                       Expr.load i64 (.var p_102.fst) fun ld_16 =>
                       Expr.let_ ⟨.cmp .ult i64, (.var ld, .var ld_16, ())⟩ fun p_103 =>
                       Expr.jnz (.var p_103.fst)
                         (Expr.let_ ⟨.add i64, (.var h_arg, .imm 184, ())⟩ fun p_104 =>
                          Expr.load i64 (.var p_104.fst) fun ld =>
                          Expr.let_ ⟨.sext 32 64, (.imm 1, ())⟩ fun p_105 =>
                          Expr.let_ ⟨.shl i64, (.var ld, .var p_105.fst, ())⟩ fun p_106 =>
                          Expr.let_ ⟨.mul i64, (.var p_106.fst, .imm 4, ())⟩ fun p_107 =>
                          Expr.let_ ⟨.add i64, (.var pHstk, .var p_107.fst, ())⟩ fun p_108 =>
                          Expr.let_ ⟨.xor i32, (.var p_99.fst, .imm 1, ())⟩ fun p_109 =>
                          Expr.store (.var p_109.fst) (.var p_108.fst)
                            (Expr.let_ ⟨.sext 32 64, (.imm 1, ())⟩ fun p_110 =>
                             Expr.let_ ⟨.shl i64, (.var ld, .var p_110.fst, ())⟩ fun p_111 =>
                             Expr.let_ ⟨.add i64, (.var p_111.fst, .imm 1, ())⟩ fun p_112 =>
                             Expr.let_ ⟨.mul i64, (.var p_112.fst, .imm 4, ())⟩ fun p_113 =>
                             Expr.let_ ⟨.add i64, (.var pHstk, .var p_113.fst, ())⟩ fun p_114 =>
                             Expr.store (.var l0_v) (.var p_114.fst)
                               (Expr.let_ ⟨.add i64, (.var ld, .imm 1, ())⟩ fun p_115 =>
                                Expr.let_ ⟨.add i64, (.var h_arg, .imm 184, ())⟩ fun p =>
                                Expr.store (.var p_115.fst) (.var p.fst)
                                  (Expr.jump Js.fst ()))))
                         (Expr.jump Js.fst ()))
                      (Expr.jump Js.fst ())))))))

private theorem m5PropLitLarge_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : Full.FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s st : Full.FullState}
    {R : Mem 64 → Prop} {not_lit : BitVec 32}
    (hFindRepl : ∀ args m Q X, Full.fullFindReplSpec args m Q X →
      Γ "full_find_repl" [i64, i64] [i64] args m Q X)
    (hWatchPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hHbrDom : ∀ args m Q X, Full.fullHbrDomSpec args m Q X →
      Γ "full_hbr_dom" [i64, i32, i32] [i32] args m Q X)
    (hAssignLvl : ∀ args m Q X, Full.fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    {Jtail : Cont [i64, i64, i64, i64, i64, Ty.bool]}
    {Jloop : Cont [i64, i64, i64, i64, i64]}
    {h_arg pVals pWvec pWstk pArena pHstk nlits_v ticks_v off_v p_prev p2_v q_v end_v : Val i64}
    {cr_v w0_v l0_v : Val i32} {ml : Mem 64}
    (hnot_lt : not_lit.toNat < 2 * s.core.cur_vars)
    (hJtail : ∀ off_r tk_r p_r q_r end_r cf_r m,
      propLitTailInv c F0 F_cur s R not_lit (off_r, p_r, q_r, end_r, cf_r, ()) m →
      Jtail (off_r, tk_r, p_r, q_r, end_r, cf_r, ()) m)
    (hJloop : ∀ off_r tk_r p_r q_r end_r m,
      propLitMainInv c F0 F_cur s R not_lit (off_r, p_r, q_r, end_r, ()) m →
      end_r.toNat - p_r.toNat = end_v.toNat - p2_v.toNat →
      Jloop (off_r, tk_r, p_r, q_r, end_r, ()) m)
    (hh : h_arg = c.hdr) (hpv : pVals = c.pVals) (hpwv : pWvec = c.pWvec)
    (hpws : pWstk = c.pWstk) (hpa : pArena = c.pArena) (hphs : pHstk = c.pWorkStk2)
    (hnl : nlits_v = BitVec.ofNat 64 s.core.cur_vars <<< 1)
    (hp2_eq : p2_v.toNat = p_prev.toNat + 2)
    (hlen : st.LengthsOk c)
    (hw_nw : Full.FullWitnessInv c F0 F_cur (withEmptyModeWatches c st).core)
    (hmrk0 : Full.FullMrkZero c st) (hnd : Full.FullArenaVarsNodup st)
    (hext : Full.FullExtScratchOk c st)
    (hdm : st.core.dense_mode = 0#64) (hcl1 : st.core.cur_level = 1)
    (hcv : st.core.cur_vars = s.core.cur_vars) (hfu : st.core.fuel = s.core.fuel)
    (hlm : st.core.lit_mark = s.core.lit_mark)
    (hws1 : st.scratch.work_stk1 = s.scratch.work_stk1)
    (htr : Full.FullTrailRsnsExt s.core st.core)
    (hhbr : Full.FullHbrBufOkW F_cur st st.core.tmp_cnt)
    (hsplit : FullSplitWatchesInv F_cur st.core not_lit.toNat off_v.toNat q_v.toNat p2_v.toNat
      end_v.toNat)
    (hqp : q_v.toNat ≤ p_prev.toNat)
    (hnot_false : st.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8) (hoom0 : st.core.oom = 0#64)
    (hflag : (w0_v &&& 0x80000000#32) = 0#32)
    (hcr_lt : cr_v.toNat < 0x80000000) (hcr_ref : cr_v.toNat ∈ Full.fullArenaClauseRefs st)
    (hcr_ng : Full.fullArenaClauseGarb st cr_v.toNat = false)
    (hcr_sz : 3 ≤ Full.fullArenaClauseSize st cr_v.toNat)
    (hcr_bd : cr_v.toNat + 3 + Full.fullArenaClauseSize st cr_v.toNat ≤ st.core.arena_len)
    (hcr_arr : cr_v.toNat + 3 + Full.fullArenaClauseSize st cr_v.toNat ≤ st.core.arena.length)
    (hl0_at : (st.core.arena[cr_v.toNat + 3]'(by omega)).toNat = l0_v.toNat)
    (hnot_at : (st.core.arena[cr_v.toNat + 4]'(by omega)).toNat = not_lit.toNat)
    (hml : (Full.FullMem c st ⋆ R) ml) :
    wp Γ Q X
      (m5PropLitLargeExpr h_arg pVals pWvec pWstk pArena pHstk not_lit nlits_v cr_v w0_v l0_v
        ticks_v off_v p2_v q_v end_v Jtail Jloop)
      ml := by
  subst hh hpv hpwv hpws hpa hphs hnl
  have hcl := hlen.core_ok
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hcv_le := hcl.cur_vars_le
  have hnot_lt' : not_lit.toNat < 2 * st.core.cur_vars := hcv ▸ hnot_lt
  have hsz_pos_cr : 0 < Full.fullArenaClauseSizeCore st.core cr_v.toNat := by
    change 0 < Full.fullArenaClauseSize st cr_v.toNat; omega
  have hl0_mem : l0_v.toNat ∈ Full.fullArenaClauseLits st cr_v.toNat :=
    (Full.mem_fullArenaClauseLitsCore_iff hcr_arr).mpr ⟨0, hsz_pos_cr, hl0_at⟩
  have hl0_lt : l0_v.toNat < 2 * st.core.cur_vars :=
    hw_nw.arena.lits_lt cr_v.toNat hcr_ref hcr_ng _ hl0_mem
  have hnl_eq : (BitVec.ofNat 64 s.core.cur_vars <<< 1).toNat = 2 * st.core.cur_vars := by
    rw [bv64_shl1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
      bv64_ofNat_toNat (by omega), hcv]
  have hq_lt : q_v.toNat < st.core.wstk.length := by
    have := hsplit.layout.bounds not_lit.toNat hnot_lt'
    rw [hsplit.off_eq, hsplit.sz_eq] at this
    have := hcl.wlen_le; have := hcl.wstk_len_arr; have := hsplit.p_le_end; omega
  have hq1_lt : q_v.toNat + 1 < st.core.wstk.length := by
    have := hsplit.layout.bounds not_lit.toNat hnot_lt'
    rw [hsplit.off_eq, hsplit.sz_eq] at this
    have := hcl.wlen_le; have := hcl.wstk_len_arr; have := hsplit.p_le_end; omega
  have hsplit_prev : FullSplitWatchesInv F_cur st.core not_lit.toNat off_v.toNat q_v.toNat
      (p_prev.toNat + 2) end_v.toNat := by
    simpa only [← hp2_eq] using hsplit
  have hq2_64 : q_v.toNat + 2 < 2 ^ 64 := by
    have := c.hwcap; unfold dimacsBound at this; have := hcl.wstk_len_arr; omega
  have hq1_bv : (q_v + 1).toNat = q_v.toNat + 1 := by bv_omega
  have hw0l_eq : l0_v &&& 0x7FFFFFFF#32 = l0_v := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hw0l_msb : ((l0_v &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 :=
    bv32_mask7f_msb_zero l0_v
  have hl0_64 : (l0_v.setWidth 64).toNat < (BitVec.ofNat 64 s.core.cur_vars <<< 1).toNat := by
    rw [bv_c0_zext32_64, hnl_eq]; exact hl0_lt
  have hl0_val_lt : l0_v.toNat < st.core.vals.length := by rw [hcl.vals_len]; omega
  have hl0_val64 : (l0_v.setWidth 64).toNat < st.core.vals.length := by
    rw [bv_c0_zext32_64]; exact hl0_val_lt
  have hcr64 : (cr_v.setWidth 64).toNat = cr_v.toNat := bv_c0_zext32_64 _
  unfold m5PropLitLargeExpr
  pt_steps_nogrp
  · exfalso; pt_clear_big
    have hcv_m : s.core.cur_vars < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hcv_m, Nat.mod_eq_of_lt (by omega)] at hc; omega
  · have hsw := hsplit_prev.write_large hnot_lt' hqp hq_lt hq1_lt hw0l_msb hcr_lt hcr_ref
    let st' : Full.FullState := { st with core := { st.core with
      wstk := (st.core.wstk.set q_v.toNat (l0_v &&& 0x7FFFFFFF#32)).set
        (q_v.toNat + 1) cr_v } }
    have hsw2 : FullSplitWatchesInv F_cur st'.core not_lit.toNat off_v.toNat
        (q_v + 2#64).toNat p2_v.toNat end_v.toNat := by
      have hq2 : (q_v + 2#64).toNat = q_v.toNat + 2 := by bv_omega
      simpa only [st', hq2, hp2_eq] using hsw
    have hlen' : st'.LengthsOk c :=
      ⟨{ hcl with wstk_len_arr := (by simp [st', hcl.wstk_len_arr]) }, hlen.scratch_ok⟩
    have hw' := fullWitnessInv_nw_upd_watches hw_nw hlen'.core_ok rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl
    rw [hq1_bv] at hm
    refine hJloop off_v ticks_v p2_v (q_v + 2#64) end_v m
      ⟨st', hlen', hw', hmrk0, fullArenaVarsNodup_of_arena_eq hnd rfl rfl,
        ⟨fullLastLearnedWf_of_refs_eq hext.1 rfl rfl, hext.2⟩, hdm, hcl1, hcv, hfu, hlm, hws1,
        htr, hhbr, hsw2, hnot_false, hoom0, hm⟩ rfl
  · have hnsgt : ¬ (0#32).slt ((st.core.vals[l0_v.toNat]'hl0_val_lt).signExtend 32) = true := by
      pt_clear_big; simp [hc]
    pt_steps_nogrp
    c0_call hFindRepl
    refine ⟨c, st, R, rfl, hlen, by rw [hcr64]; omega, by rw [hcr64]; exact hcr_sz,
      by rw [hcr64]; exact hcr_bd, hml, ?_, ?_⟩
    · intro hfind_none
      rw [hcr64] at hfind_none
      have hfals := clause_falsified_of_find_repl_none hlen hw_nw hcr_ref hcr_ng hcr_arr
        hl0_at hnot_at hnot_false hfind_none
      have hsw := hsplit_prev.write_large hnot_lt' hqp hq_lt hq1_lt hw0l_msb hcr_lt hcr_ref
      let st_w : Full.FullState := { st with core := { st.core with
        wstk := (st.core.wstk.set q_v.toNat (l0_v &&& 0x7FFFFFFF#32)).set
          (q_v.toNat + 1) cr_v } }
      have hsw2 : FullSplitWatchesInv F_cur st_w.core not_lit.toNat off_v.toNat
          (q_v + 2#64).toNat p2_v.toNat end_v.toNat := by
        have hq2 : (q_v + 2#64).toNat = q_v.toNat + 2 := by bv_omega
        simpa only [st_w, hq2, hp2_eq] using hsw
      have hlen_w : st_w.LengthsOk c :=
        ⟨{ hcl with wstk_len_arr := (by simp [st_w, hcl.wstk_len_arr]) }, hlen.scratch_ok⟩
      have hw_w := fullWitnessInv_nw_upd_watches hw_nw hlen_w.core_ok
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      have hext_w : Full.FullExtScratchOk c st_w :=
        ⟨fullLastLearnedWf_of_refs_eq hext.1 rfl rfl, hext.2⟩
      have hnd_w : Full.FullArenaVarsNodup st_w := fullArenaVarsNodup_of_arena_eq hnd rfl rfl
      pt_steps_nogrp
      · rw [hq1_bv] at hm
        have hslt : ((st.core.vals[l0_v.toNat]'hl0_val_lt).signExtend 32).slt 0#32 = true := by
          pt_clear_big; exact hc
        have hl0_ff : st.core.vals[l0_v.toNat]?.getD 0#8 = 0xFF#8 :=
          pt_vals_eq_ff_of_slt hl0_val_lt (hw_nw.vals_domain _ hl0_lt) hslt
        let st_c : Full.FullState := { st_w with core := { st_w.core with
          confl_type := 2#64, confl_ref := cr_v.setWidth 64 } }
        have hlen_c : st_c.LengthsOk c :=
          ⟨{ hlen_w.core_ok with cur_vars_le := hcv_le }, hlen_w.scratch_ok⟩
        have hw_c := fullWitnessInv_nw_upd_watches hw_w hlen_c.core_ok
          rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        have hconfl_ok : Full.FullConflictOkW F_cur st_c := by
          refine Or.inr ⟨by simp [st_c], hcr_ref, hcr_ng, fun l hl => ?_⟩
          have hcr_eq : (cr_v.setWidth 64).toNat = cr_v.toNat := by bv_omega
          rw [hcr_eq] at hl
          rcases hfals l hl with rfl | hff <;> first | exact hl0_ff | exact hff
        refine hJtail off_v ticks_v p2_v (q_v + 2#64) end_v true m
          ⟨st_c, hlen_c, hw_c, hmrk0, fullArenaVarsNodup_of_arena_eq hnd_w rfl rfl,
            ⟨fullLastLearnedWf_of_refs_eq hext_w.1 rfl rfl, hext_w.2⟩, hdm, hcl1, hcv, hfu,
            hlm, hws1, htr, hhbr, hsw2.with_nonwatch rfl rfl rfl rfl fun _ h => h,
            fun _ => Or.inr hconfl_ok, fun hf => (by cases hf), hm⟩
      · rw [hq1_bv] at hm
        have hnslt : ¬ ((st.core.vals[l0_v.toNat]'hl0_val_lt).signExtend 32).slt 0#32 =
            true := by pt_clear_big; simp [hc]
        have hl0_0 : st.core.vals[l0_v.toNat]?.getD 0#8 = 0#8 :=
          pt_vals_eq_0_of_flags hl0_val_lt (hw_nw.vals_domain _ hl0_lt) hnsgt hnslt
        c0_call hHbrDom
        refine ⟨c, F0, F_cur, st_w, R, rfl, hlen_w,
          ⟨List.replicate (4 * c.max_vars) 0#32, st_w.core.wstk, 0, hw_w⟩,
          hmrk0, hcl1, hcr_ref, hcr_ng, ?_, fun l hl hne => ?_, hm, ?_⟩
        · simpa [st_w, Full.fullArenaClauseLits, Full.fullArenaClauseLitsCore,
            Full.fullArenaClauseSize, Full.fullArenaClauseSizeCore] using hl0_mem
        · have hfl := hfals l (by simpa [st_w, Full.fullArenaClauseLits,
            Full.fullArenaClauseLitsCore, Full.fullArenaClauseSize,
            Full.fullArenaClauseSizeCore] using hl)
          exact hfl.resolve_left hne
        · dsimp only; intro dom mrk' mclr' mh hlen_h hmrk_h hdom hm_h
          let st_h : Full.FullState := { st_w with core := { st_w.core with
            mrk := mrk', min_clr := mclr' } }
          have hw_h := fullWitnessInv_nw_upd_watches hw_w hlen_h.core_ok rfl rfl rfl rfl rfl rfl
            rfl rfl rfl rfl rfl rfl rfl
          have hsw_h := hsw2.with_nonwatch (k' := st_h.core) rfl rfl rfl rfl fun _ h => h
          have hext_h : Full.FullExtScratchOk c st_h :=
            ⟨fullLastLearnedWf_of_refs_eq hext_w.1 rfl rfl, hext_w.2⟩
          have hnd_h : Full.FullArenaVarsNodup st_h :=
            fullArenaVarsNodup_of_arena_eq hnd_w rfl rfl
          have hhbr_h : Full.FullHbrBufOkW F_cur st_h st_h.core.tmp_cnt :=
            fullHbrBufOkW_congr hhbr rfl rfl
          refine wp_join_group
            (fun () m_j => ∃ st_j : Full.FullState,
              st_j.LengthsOk c ∧
              Full.FullWitnessInv c F0 F_cur (withEmptyModeWatches c st_j).core ∧
              Full.FullMrkZero c st_j ∧ Full.FullArenaVarsNodup st_j ∧
              Full.FullExtScratchOk c st_j ∧
              st_j.core.dense_mode = 0#64 ∧ st_j.core.cur_level = 1 ∧
              st_j.core.cur_vars = s.core.cur_vars ∧ st_j.core.fuel = s.core.fuel ∧
              st_j.core.lit_mark = s.core.lit_mark ∧
              st_j.scratch.work_stk1 = s.scratch.work_stk1 ∧
              Full.FullTrailRsnsExt s.core st_j.core ∧
              Full.FullHbrBufOkW F_cur st_j st_j.core.tmp_cnt ∧
              FullSplitWatchesInv F_cur st_j.core not_lit.toNat off_v.toNat
                (q_v + 2#64).toNat p2_v.toNat end_v.toNat ∧
              st_j.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 ∧ st_j.core.oom = 0#64 ∧
              st_j.core.vals[l0_v.toNat]?.getD 0#8 = 0#8 ∧
              cr_v.toNat ∈ Full.fullArenaClauseRefs st_j ∧
              Full.fullArenaClauseGarb st_j cr_v.toNat = false ∧
              (∀ q ∈ Full.fullArenaClauseLits st_j cr_v.toNat,
                q = l0_v.toNat ∨ st_j.core.vals[q]?.getD 0#8 = 0xFF#8) ∧
              l0_v.toNat ∈ Full.fullArenaClauseLits st_j cr_v.toNat ∧ (Full.FullMem c st_j ⋆ R) m_j)
            (fun _ () m_j ⟨st_j, hj_len, hj_nw, hj_mrk, hj_nd, hj_ext, hj_dm, hj_cl1, hj_cv,
              hj_fu, hj_lm, hj_ws1, hj_tr, hj_hbr, hj_sw, hj_nf, hj_oom, hj_l00, hj_cref,
              hj_cng, hj_fals, hj_l0m, hm_j⟩ => by
              pt_steps_nogrp
              c0_call hAssignLvl
              refine ⟨c, st_j, R, rfl, hj_len, hm_j, ?_⟩
              have hl0_j : l0_v.toNat < 2 * st_j.core.cur_vars := by
                rw [hj_cv, ← hcv]; exact hl0_lt
              have hte_j : st_j.core.trail_end < st_j.core.cur_vars :=
                hj_nw.trail_end_lt_of_unassigned hl0_j hj_l00
              have hno_j : ¬ (st_j.core.cur_vars ≤ l0_v.toNat / 2 ∨
                  c.max_vars ≤ st_j.core.trail_end ∨
                  st_j.core.vals[l0_v.toNat]?.getD 0#8 ≠ 0#8) := by
                have := hj_len.core_ok.cur_vars_le
                intro hbad; rcases hbad with h1 | h2 | h3 <;> first | omega | exact h3 hj_l00
              rw [ite_eq_right hno_j]; dsimp only
              intro flags' unass' phases' m_a hfll hph hm_a
              have hnot_j : not_lit.toNat < 2 * st_j.core.cur_vars := by rw [hj_cv]; exact hnot_lt
              have hcr_msb : (cr_v &&& 0x80000000#32) = 0#32 := bv32_msb_zero_of_lt hcr_lt
              have hcr_ne_ff : cr_v ≠ 0xFFFFFFFF#32 := fun h => by
                rw [h] at hcr_lt; exact absurd hcr_lt (by decide)
              have hu := unitAssignLvl_preserves_witness hj_len hj_nw (other := l0_v)
                (rsn := cr_v) (alvl := 1#32) (not_lit := not_lit.toNat) (flags' := flags')
                (phases' := phases') (unass' := unass') (unfl' := st_j.core.unflushed) hl0_j
                hfll hph hj_l00 hnot_j hj_nf (by decide) (by rw [hj_cl1]; decide) hcr_ne_ff
                (by
                  rw [ite_eq_right (by intro hc; exact hc hcr_msb)]
                  refine ⟨hj_cref, hj_cng, fun q hq => ?_⟩
                  rcases hj_fals q hq with rfl | hq_ff
                  · exact Or.inl rfl
                  · right
                    have hq_lt : q < 2 * st_j.core.cur_vars :=
                      hj_nw.arena.lits_lt _ hj_cref hj_cng q hq
                    obtain ⟨k, hk, hkeq⟩ := (hj_nw.vals_false_iff q hq_lt).mp hq_ff
                    have hk_lvl := hj_nw.lvl_le k hk
                    dsimp only [withEmptyModeWatches] at hk_lvl
                    have hqvar : (st_j.core.trl[k]?.getD 0#32).toNat / 2 = q / 2 := by
                      rw [hkeq]; exact Full.fullInv_var_xor1 q
                    rw [hqvar, hj_cl1] at hk_lvl
                    exact ⟨k, hk, hkeq, by simpa using hk_lvl⟩)
                (fun _ => hj_l0m)
              dsimp only at hu hm_a
              let st_a : Full.FullState :=
                { st_j with
                  core := { st_j.core with
                    vals := (st_j.core.vals.set l0_v.toNat 1#8).set (l0_v.toNat ^^^ 1) 0xFF#8
                    flags := flags', lvl := st_j.core.lvl.set (l0_v.toNat / 2) 1#32
                    rsns := st_j.core.rsns.set (l0_v.toNat / 2) cr_v
                    trl := st_j.core.trl.set st_j.core.trail_end l0_v
                    trail_pos := st_j.core.trail_pos.set (l0_v.toNat / 2)
                      (BitVec.ofNat 32 st_j.core.trail_end)
                    trail_end := st_j.core.trail_end + 1, unassigned := unass' }
                  scratch := { st_j.scratch with phases := phases' } }
              have hlen_a : st_a.LengthsOk c :=
                ⟨{ hj_len.core_ok with
                    vals_len := (by simp [st_a, hj_len.core_ok.vals_len]),
                    flags_len := (by simp [st_a, hfll]),
                    lvl_len := (by simp [st_a, hj_len.core_ok.lvl_len]),
                    rsns_len := (by simp [st_a, hj_len.core_ok.rsns_len]),
                    trl_len := (by simp [st_a, hj_len.core_ok.trl_len]),
                    trail_pos_len := (by simp [st_a, hj_len.core_ok.trail_pos_len]),
                    trail_end_le := (by simp [st_a]; omega),
                    propagated_le :=
                      (by simp [st_a]; have := hj_len.core_ok.propagated_le; omega) },
                  { hj_len.scratch_ok with phases_len := (by simp [st_a, hph]) }⟩
              have htr_ja := fullTrailRsnsExt_trans
                (fullTrailRsnsExt_congr (k1 := st_j.core)
                  (k2 := (withEmptyModeWatches c st_j).core) rfl rfl rfl rfl)
                (fullTrailRsnsExt_trans
                  (fullTrailRsnsExt_of_assign_lvl (rsn := cr_v) (alvl := 1#32)
                    (flags' := flags') (unass' := unass') (unfl' := st_j.core.unflushed)
                    hj_nw hl0_j hj_l00)
                  (fullTrailRsnsExt_congr (k2 := st_a.core) rfl rfl rfl rfl))
              have htr_a := fullTrailRsnsExt_trans hj_tr htr_ja
              refine hJloop off_v (ticks_v + 1#64) p2_v (q_v + 2#64) end_v m_a ⟨st_a, hlen_a, hu.1,
                fun w hw => hj_mrk w hw, fullArenaVarsNodup_of_arena_eq hj_nd rfl rfl,
                ⟨fullLastLearnedWf_of_refs_eq hj_ext.1 rfl rfl, hj_ext.2⟩, hj_dm, hj_cl1,
                hj_cv, hj_fu, hj_lm, hj_ws1, htr_a, fullHbrBufOkW_congr hj_hbr rfl rfl,
                hj_sw.with_nonwatch rfl rfl rfl rfl fun _ h => h, hu.2, hj_oom, hm_a⟩ rfl)
            (fun Jh hJh => by
              have hdone_base : ∀ (st_x : Full.FullState) (mx : Mem 64), st_x.LengthsOk c →
                  Full.FullWitnessInv c F0 F_cur (withEmptyModeWatches c st_x).core →
                  Full.FullMrkZero c st_x → Full.FullArenaVarsNodup st_x →
                  Full.FullExtScratchOk c st_x →
                  st_x.core.dense_mode = 0#64 → st_x.core.cur_level = 1 →
                  st_x.core.cur_vars = s.core.cur_vars → st_x.core.fuel = s.core.fuel →
                  st_x.core.lit_mark = s.core.lit_mark →
                  st_x.scratch.work_stk1 = s.scratch.work_stk1 →
                  Full.FullTrailRsnsExt s.core st_x.core →
                  Full.FullHbrBufOkW F_cur st_x st_x.core.tmp_cnt →
                  FullSplitWatchesInv F_cur st_x.core not_lit.toNat off_v.toNat
                    (q_v + 2#64).toNat p2_v.toNat end_v.toNat →
                  st_x.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 → st_x.core.oom = 0#64 →
                  st_x.core.vals[l0_v.toNat]?.getD 0#8 = 0#8 →
                  cr_v.toNat ∈ Full.fullArenaClauseRefs st_x →
                  Full.fullArenaClauseGarb st_x cr_v.toNat = false →
                  (∀ q ∈ Full.fullArenaClauseLits st_x cr_v.toNat,
                    q = l0_v.toNat ∨ st_x.core.vals[q]?.getD 0#8 = 0xFF#8) →
                  l0_v.toNat ∈ Full.fullArenaClauseLits st_x cr_v.toNat →
                  (Full.FullMem c st_x ⋆ R) mx →
                  wp Γ Q X (Expr.jump Jh ()) mx := by
                intro st_x mx x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                  x20 x21 hm_x
                pt_steps_nogrp; exact hJh () mx ⟨st_x, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10,
                  x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, hm_x⟩
              have hl0_w : l0_v.toNat ∈ Full.fullArenaClauseLits st_h cr_v.toNat := by
                simpa [st_h, st_w, Full.fullArenaClauseLits, Full.fullArenaClauseLitsCore,
                  Full.fullArenaClauseSize, Full.fullArenaClauseSizeCore] using hl0_mem
              have hfals_h : ∀ q ∈ Full.fullArenaClauseLits st_h cr_v.toNat,
                  q = l0_v.toNat ∨ st_h.core.vals[q]?.getD 0#8 = 0xFF#8 := fun q hq => hfals q
                (by simpa [st_h, st_w, Full.fullArenaClauseLits, Full.fullArenaClauseLitsCore,
                  Full.fullArenaClauseSize, Full.fullArenaClauseSizeCore] using hq)
              pt_steps_nogrp
              · obtain ⟨hdom_lt, hent_dom⟩ := hdom.resolve_left (by pt_clear_big; assumption)
                have h_tc_le : st_h.core.tmp_cnt ≤ st_h.core.cur_vars := hhbr_h.1
                have hcv_h : st_h.core.cur_vars ≤ c.max_vars := hlen_h.core_ok.cur_vars_le
                have htc_lt : st_h.core.tmp_cnt < st_h.core.cur_vars := by
                  pt_clear_big
                  have hlt : st_h.core.tmp_cnt % 2 ^ 64 < st_h.core.cur_vars % 2 ^ 64 := by
                    assumption
                  rw [Nat.mod_eq_of_lt (by omega : st_h.core.cur_vars < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega)] at hlt; exact hlt
                have hshl_h : (BitVec.ofNat 64 st_h.core.tmp_cnt <<< 1).toNat =
                    2 * st_h.core.tmp_cnt := by
                  rw [bv64_shl1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
                    bv64_ofNat_toNat (by omega)]
                have h_idx0 : (BitVec.ofNat 64 st_h.core.tmp_cnt <<<
                    ((1#32 : BitVec 32).signExtend 64).toNat).toNat = 2 * st_h.core.tmp_cnt := by
                  simpa only [show ((1#32 : BitVec 32).signExtend 64).toNat = 1 from rfl]
                    using hshl_h
                have h_idx1 : ((BitVec.ofNat 64 st_h.core.tmp_cnt <<<
                    ((1#32 : BitVec 32).signExtend 64).toNat) + 1#64).toNat =
                    2 * st_h.core.tmp_cnt + 1 := by
                  rw [bv64_add1_toNat (by rw [h_idx0]; omega), h_idx0]
                have hws2_i0 : (BitVec.ofNat 64 st_h.core.tmp_cnt <<<
                    ((1#32 : BitVec 32).signExtend 64).toNat).toNat <
                    st_h.scratch.work_stk2.length := by
                  rw [hlen_h.scratch_ok.work_stk2_len, h_idx0]; omega
                have hws2_i1 : ((BitVec.ofNat 64 st_h.core.tmp_cnt <<<
                    ((1#32 : BitVec 32).signExtend 64).toNat) + 1#64).toNat <
                    st_h.scratch.work_stk2.length := by
                  rw [hlen_h.scratch_ok.work_stk2_len, h_idx1]; omega
                have hpush := fullHbrBufOkW_push hlen_h hhbr_h htc_lt
                  (a := dom ^^^ 1#32) (b := l0_v)
                  (by rw [bv32_toNat_xor1]; exact litNeg_lt_two_mul hdom_lt) hl0_lt
                  (by rw [bv32_toNat_xor1]; exact hent_dom)
                have h_tc_bv : (BitVec.ofNat 64 st_h.core.tmp_cnt + 1).toNat =
                    st_h.core.tmp_cnt + 1 := by
                  change (BitVec.ofNat 64 st_h.core.tmp_cnt + 1#64).toNat = _
                  rw [bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
                    bv64_ofNat_toNat (by omega)]
                have h_idx1_c0 : (BitVec.ofNat 64 st_h.core.tmp_cnt <<< 1 + 1).toNat =
                    2 * st_h.core.tmp_cnt + 1 := by
                  simpa only [show ((1#32 : BitVec 32).signExtend 64).toNat = 1 from rfl,
                    show (1#64 : BitVec 64) = 1 from rfl] using h_idx1
                pt_steps_nogrp
                let st_p := { st_h with
                  core := { st_h.core with tmp_cnt := st_h.core.tmp_cnt + 1 }
                  scratch := { st_h.scratch with
                    work_stk2 := (st_h.scratch.work_stk2.set (2 * st_h.core.tmp_cnt)
                      (dom ^^^ 1#32)).set (2 * st_h.core.tmp_cnt + 1) l0_v } }
                have hw_p := fullWitnessInv_nw_upd_watches hw_h hpush.1.core_ok rfl rfl rfl rfl
                  rfl rfl rfl rfl rfl rfl rfl rfl rfl
                have hm_p : (Full.FullMem c st_p ⋆ R) m := by
                  dsimp only [st_h] at hshl_h h_tc_bv h_idx1_c0; dsimp only [st_p, st_h]
                  simpa only [hshl_h, h_tc_bv, h_idx1_c0,
                    show (1#32 : BitVec 32) = 1 from rfl] using hm
                exact hdone_base st_p m hpush.1 hw_p hmrk_h
                  (fullArenaVarsNodup_of_arena_eq hnd_h rfl rfl)
                  ⟨fullLastLearnedWf_of_refs_eq hext_h.1 rfl rfl, hext_h.2⟩ hdm hcl1 hcv
                  hfu hlm hws1 htr hpush.2
                  (hsw_h.with_nonwatch (k' := st_p.core) rfl rfl rfl rfl fun _ h => h)
                  hnot_false hoom0 hl0_0 hcr_ref hcr_ng hfals_h hl0_w hm_p
              · exact hdone_base st_h mh hlen_h hw_h hmrk_h hnd_h hext_h hdm hcl1 hcv hfu hlm
                  hws1 htr hhbr_h hsw_h hnot_false hoom0 hl0_0 hcr_ref hcr_ng hfals_h hl0_w hm_h
              · exact hdone_base st_h mh hlen_h hw_h hmrk_h hnd_h hext_h hdm hcl1 hcv hfu hlm
                  hws1 htr hhbr_h hsw_h hnot_false hoom0 hl0_0 hcr_ref hcr_ng hfals_h hl0_w hm_h)
    · intro r m_fr hr_lo hr_hi ⟨hrepl_lt, _hrepl_nslt⟩ hm_fr
      rw [hcr64] at hr_hi hrepl_lt hm_fr
      let st_fr : Full.FullState := { st with core := { st.core with
        arena := st.core.arena.set (cr_v.toNat + 1) (BitVec.ofNat 32 r) } }
      have hfr_set := arena_setSrch_keep_inv hlen hw_nw hnd hext hcr_ref (srch := BitVec.ofNat 32 r)
      obtain ⟨hlen_fr, hw_fr, hnd_fr, hext_fr, hrefs_fr⟩ := hfr_set
      have hcr_ref_fr : cr_v.toNat ∈ Full.fullArenaClauseRefs st_fr := hrefs_fr ▸ hcr_ref
      have hcr_sz_fr : Full.fullArenaClauseSize st_fr cr_v.toNat =
          Full.fullArenaClauseSize st cr_v.toNat := by
        unfold Full.fullArenaClauseSize Full.fullArenaClauseSizeCore; dsimp only [st_fr]
        rw [List.getElem?_set_ne (by omega)]
      have hcr_ng_fr : Full.fullArenaClauseGarb st_fr cr_v.toNat = false := by
        unfold Full.fullArenaClauseGarb Full.fullArenaClauseGarbCore Full.fullArenaHdrCore
        dsimp only [st_fr]; rw [List.getElem?_set_ne (by omega)]; exact hcr_ng
      have hcr_arr_fr : cr_v.toNat + 3 + Full.fullArenaClauseSize st_fr cr_v.toNat ≤
          st_fr.core.arena.length := by simpa [st_fr, hcr_sz_fr] using hcr_arr
      have hnot_fr : (st_fr.core.arena[cr_v.toNat + 4]'(by omega)).toNat = not_lit.toNat := by
        dsimp only [st_fr]; rw [List.getElem_set_ne (by omega)]; exact hnot_at
      have hl_repl_idx : cr_v.toNat + 3 + r < st_fr.core.arena.length := by omega
      have hrepl_get : st_fr.core.arena[cr_v.toNat + 3 + r]'hl_repl_idx =
          st.core.arena[cr_v.toNat + 3 + r]'(by omega) := by
        dsimp only [st_fr]; rw [List.getElem_set_ne (by omega)]
      let repl := st.core.arena[cr_v.toNat + 3 + r]'(by omega)
      have hrepl_lt' : repl.toNat < 2 * st.core.cur_vars := by
        simpa [repl, List.getElem?_eq_getElem (by omega : cr_v.toNat + 3 + r <
          st.core.arena.length)] using hrepl_lt
      have hrepl_ne_not : repl.toNat ≠ not_lit.toNat := by
        have hne := arena_lit_ne_of_nodup hnd_fr hcr_ref_fr hcr_ng_fr hcr_arr_fr
          (k1 := r) (k2 := 1) (by rw [hcr_sz_fr]; omega) (by rw [hcr_sz_fr]; omega) (by omega)
        intro heq; apply hne
        have hnot_fr' : (st_fr.core.arena[cr_v.toNat + 3 + 1]'(by omega)).toNat =
            not_lit.toNat := by
          simpa only [show cr_v.toNat + 3 + 1 = cr_v.toNat + 4 by omega] using hnot_fr
        rw [hnot_fr', hrepl_get]; exact heq
      have hr_32 : r < 2 ^ 32 := by
        have : Full.fullArenaClauseSize st cr_v.toNat < 2 ^ 32 := BitVec.isLt _; omega
      have hr_idx64 : (cr_v.setWidth 64 + 3#64 + BitVec.ofNat 64 r).toNat =
          cr_v.toNat + 3 + r := by bv_omega
      have hcr4_idx64 : (cr_v.setWidth 64 + 4#64).toNat = cr_v.toNat + 4 := by bv_omega
      have hsw_lits := arena_swapLits_keep_inv hlen_fr hw_fr hnd_fr hext_fr
        hcr_ref_fr (k1 := 1) (k2 := r) (by rw [hcr_sz_fr]; omega) (by rw [hcr_sz_fr]; omega)
      dsimp only at hsw_lits
      have hl1_idx_fr : cr_v.toNat + 3 + 1 < st_fr.core.arena.length := by omega
      have hl1_sw_eq : st_fr.core.arena[cr_v.toNat + 3 + 1]'hl1_idx_fr = not_lit :=
        BitVec.eq_of_toNat_eq (by
          simpa only [show cr_v.toNat + 3 + 1 = cr_v.toNat + 4 by omega] using hnot_fr)
      have hl2_sw_eq : st_fr.core.arena[cr_v.toNat + 3 + r]'hl_repl_idx = repl := hrepl_get
      let ar_sw := (st_fr.core.arena.set (cr_v.toNat + 4) repl).set (cr_v.toNat + 3 + r) not_lit
      have har_sw_eq : (st_fr.core.arena.set (cr_v.toNat + 3 + 1)
          (st_fr.core.arena[cr_v.toNat + 3 + r]'hl_repl_idx)).set (cr_v.toNat + 3 + r)
          (st_fr.core.arena[cr_v.toNat + 3 + 1]'hl1_idx_fr) = ar_sw := by
        simp only [hl1_sw_eq, hl2_sw_eq]; rfl
      rw [har_sw_eq] at hsw_lits
      let st_sw : Full.FullState := { st_fr with core := { st_fr.core with arena := ar_sw } }
      obtain ⟨hlen_sw, hw_sw, hnd_sw, hext_sw, hrefs_sw', _⟩ :=
        (hsw_lits : st_sw.LengthsOk c ∧
          Full.FullWitnessInv c F0 F_cur (withEmptyModeWatches c st_sw).core ∧
          Full.FullArenaVarsNodup st_sw ∧ Full.FullExtScratchOk c st_sw ∧
          Full.fullArenaClauseRefs st_sw = Full.fullArenaClauseRefs st_fr ∧
          ∀ r0 ∈ Full.fullArenaClauseRefs st_fr,
            Full.fullArenaClauseSize st_sw r0 = Full.fullArenaClauseSize st_fr r0 ∧
            Full.fullArenaClauseGarb st_sw r0 = Full.fullArenaClauseGarb st_fr r0 ∧
            (Full.fullArenaClauseLits st_sw r0).Perm (Full.fullArenaClauseLits st_fr r0))
      have hrefs_sw : Full.fullArenaClauseRefs st_sw = Full.fullArenaClauseRefs st :=
        hrefs_sw'.trans hrefs_fr
      have hfr_r64 : (cr_v.setWidth 64 + 3#64 + BitVec.ofNat 64 r).toNat <
          st_fr.core.arena.length := by rw [hr_idx64]; exact hl_repl_idx
      have hfr_464 : (cr_v.setWidth 64 + 4#64).toNat < st_fr.core.arena.length := by
        rw [hcr4_idx64]; omega
      pt_step; pt_step
      · pt_steps_nogrp
        have hpr_sub : (p2_v - off_v).toNat = p2_v.toNat - off_v.toNat := by
          have := hsplit.q_ge; have := hsplit.q_le_p; bv_omega
        have hqr_sub : (q_v - off_v).toNat = q_v.toNat - off_v.toNat := by
          have := hsplit.q_ge; bv_omega
        have her_sub : (end_v - off_v).toNat = end_v.toNat - off_v.toNat := by
          have := hsplit.q_ge; have := hsplit.q_le_p; have := hsplit.p_le_end; bv_omega
        have hr_idx_c0 : (cr_v.setWidth 64 + 3 + BitVec.ofNat 64 r).toNat =
            cr_v.toNat + 3 + r := by bv_omega
        have hcr4_c0 : (cr_v.setWidth 64 + 4).toNat = cr_v.toNat + 4 := by bv_omega
        have hfr_r64_c0 : (cr_v.setWidth 64 + 3 + BitVec.ofNat 64 r).toNat <
            st_fr.core.arena.length := by rw [hr_idx_c0]; exact hl_repl_idx
        have hld_c0 : (st.core.arena.set (cr_v.toNat + 1) (BitVec.ofNat 32 r))[(cr_v.setWidth 64
            + 3 + BitVec.ofNat 64 r).toNat]'hfr_r64_c0 = repl := Option.some_inj.mp (by
          rw [← List.getElem?_eq_getElem hfr_r64_c0, hr_idx_c0]
          exact (List.getElem?_eq_getElem hl_repl_idx).trans (congrArg some hrepl_get))
        have hm_sw_ar : (Full.FullMem c st_sw ⋆ R) m := by
          dsimp only [st_sw, st_fr, ar_sw]
          simp only [hr_idx_c0, hcr4_c0] at hm
          rwa [show (st.core.arena.set (cr_v.toNat + 1)
            (BitVec.ofNat 32 r))[cr_v.toNat + 3 + r]'hl_repl_idx = repl from hrepl_get] at hm
        c0_call hWatchPush
        refine ⟨c, st_sw, R, rfl, hlen_sw,
          (hsplit.with_nonwatch (k' := st_sw.core) rfl rfl rfl rfl fun r0 hr0 => by
            rw [show Full.fullArenaClauseRefsCore st_sw.core = Full.fullArenaClauseRefs st_sw
              from rfl, hrefs_sw]; exact hr0).layout, fun h1 => (by cases h1),
          fun _ => ⟨fun heq => by
            have hlt : (l0_v &&& 0x7FFFFFFF#32).toNat < 0x80000000 := by rw [hw0l_eq]; omega
            rw [show l0_v &&& 0x7FFFFFFF#32 = 0xFFFFFFFF#32 from heq] at hlt
            exact absurd hlt (by decide),
            fun heq => absurd (heq ▸ hcr_lt) (by decide)⟩, hm_sw_ar, ?_⟩
        dsimp only
        intro pok wvec' wstk' wlen' wu' wsort' m_wp hlen_wp hlay_wp hpres_other
          hpok_t hpok_f hm_wp
        let st_wp : Full.FullState := { st_sw with
          core := { st_sw.core with
            wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
          scratch := { st_sw.scratch with wsort := wsort' } }
        have hnot_shl : (not_lit.setWidth 64 <<<
            ((1#32 : BitVec 32).signExtend 64).toNat).toNat = 2 * not_lit.toNat := by
          rw [show ((1#32 : BitVec 32).signExtend 64).toNat = 1 from rfl,
            bv64_shl1_toNat (by rw [bv_c0_zext32_64]; omega), bv_c0_zext32_64]
        have hwvec_not : (not_lit.setWidth 64 <<<
            ((1#32 : BitVec 32).signExtend 64).toNat).toNat < st_wp.core.wvec.length := by
          rw [hlen_wp.core_ok.wvec_len, hnot_shl]; omega
        have hwvec_off : (st_wp.core.wvec[(not_lit.setWidth 64 <<<
            ((1#32 : BitVec 32).signExtend 64).toNat).toNat]'hwvec_not).toNat =
            Full.fullWatchOffCore st_wp.core not_lit.toNat := by
          unfold Full.fullWatchOffCore
          rw [← hnot_shl, List.getElem?_eq_getElem hwvec_not, Option.getD_some]
        have hsw_orig := hsplit.with_nonwatch (k' := st_sw.core) rfl rfl rfl rfl fun r0 hr0 => by
          rw [show Full.fullArenaClauseRefsCore st_sw.core =
            Full.fullArenaClauseRefs st_sw from rfl, hrefs_sw]; exact hr0
        simp only [hld_c0] at hpres_other hpok_t hpok_f
        dsimp only [Full.fullWatchSize, Full.fullWatchOff] at hpres_other hpok_t hpok_f
        change Full.WatchStackLayout st_wp.core at hlay_wp
        have hap := hsw_orig.after_push (k' := st_wp.core) rfl hnot_lt' hrepl_lt' hrepl_ne_not rfl
          hlay_wp hw0l_msb hcr_lt (by change cr_v.toNat ∈ Full.fullArenaClauseRefs st_sw
                                      rw [hrefs_sw]; exact hcr_ref) hpres_other
          (fun hpt => by
            have h2 := hpok_t hpt; exact ⟨h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2.1, h2.2.2.2.2.2 rfl⟩)
          (fun hpf => (hpok_f hpf).1 hrepl_lt')
        dsimp only at hap
        have hend_wp_bd : Full.fullWatchOffCore st_wp.core not_lit.toNat +
            (end_v.toNat - off_v.toNat) ≤ st_wp.core.wlen := by
          have := hlay_wp.bounds not_lit.toNat hnot_lt'; have := hap.sz_eq; omega
        have hwp_wcap := c.hwcap; unfold dimacsBound at hwp_wcap
        have hwp_wlen_le : st_wp.core.wlen ≤ c.wcap := hlen_wp.core_ok.wlen_le
        have hoff_lt64 : Full.fullWatchOffCore st_wp.core not_lit.toNat +
            (end_v.toNat - off_v.toNat) < 2 ^ 64 := by omega
        let off'_bv := (st_wp.core.wvec[(not_lit.setWidth 64 <<<
          ((1#32 : BitVec 32).signExtend 64).toNat).toNat]'hwvec_not).setWidth 64
        have hoff'_eq : off'_bv.toNat = Full.fullWatchOffCore st_wp.core not_lit.toNat := by
          rw [bv_c0_zext32_64, hwvec_off]
        have hp2'_eq : (off'_bv + (p2_v - off_v)).toNat =
            off'_bv.toNat + (p2_v.toNat - off_v.toNat) := by
          rw [BitVec.toNat_add, hoff'_eq, hpr_sub,
            Nat.mod_eq_of_lt (by have := hsplit.p_le_end; omega)]
        have hq'_eq : (off'_bv + (q_v - off_v)).toNat =
            off'_bv.toNat + (q_v.toNat - off_v.toNat) := by
          rw [BitVec.toNat_add, hoff'_eq, hqr_sub,
            Nat.mod_eq_of_lt (by have := hsplit.q_le_p; have := hsplit.p_le_end; omega)]
        have hend'_eq : (off'_bv + (end_v - off_v)).toNat =
            off'_bv.toNat + (end_v.toNat - off_v.toNat) := by
          rw [BitVec.toNat_add, hoff'_eq, her_sub, Nat.mod_eq_of_lt hoff_lt64]
        have hap' : FullSplitWatchesInv F_cur st_wp.core not_lit.toNat off'_bv.toNat
            (off'_bv + (q_v - off_v)).toNat (off'_bv + (p2_v - off_v)).toNat
            (off'_bv + (end_v - off_v)).toNat := by
          simpa only [hoff'_eq, hp2'_eq, hq'_eq, hend'_eq] using hap
        pt_steps_nogrp
        · have hpok_eq : pok = true := by pt_clear_big; exact hc
          rw [hpok_eq] at *
          have hw_wp := fullWitnessInv_nw_upd_watches (s := st_sw) (s' := st_wp) hw_sw
            hlen_wp.core_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          have htr_wp := fullTrailRsnsExt_trans htr (fullTrailRsnsExt_congr rfl rfl rfl rfl)
          refine hJloop off'_bv (ticks_v + 1) (off'_bv + (p2_v - off_v)) (off'_bv + (q_v - off_v))
              (off'_bv + (end_v - off_v)) m_wp
            ⟨st_wp, hlen_wp, hw_wp, hmrk0, fullArenaVarsNodup_of_arena_eq hnd_sw rfl rfl,
              ⟨fullLastLearnedWf_of_refs_eq hext_sw.1 rfl rfl, hext_sw.2⟩, hdm, hcl1, hcv,
              hfu, hlm, hws1, htr_wp, fullHbrBufOkW_congr hhbr rfl rfl, hap', hnot_false,
              hoom0, hm_wp⟩ (by
                rw [hend'_eq, hp2'_eq]; have := hsplit.q_ge; have := hsplit.q_le_p
                have := hsplit.p_le_end; omega)
        · have hpok_eq : pok = false := by pt_clear_big; cases pok <;> simp_all
          have har_len_wp : st_wp.core.arena.length = st.core.arena.length := by
            simp [st_wp, st_sw, ar_sw, st_fr]
          have hsz_wp : Full.fullArenaClauseSize st_wp cr_v.toNat =
              Full.fullArenaClauseSize st cr_v.toNat := by
            unfold Full.fullArenaClauseSize Full.fullArenaClauseSizeCore
            dsimp only [st_wp, st_sw, ar_sw, st_fr]
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              List.getElem?_set_ne (by omega)]
          have har_wp_bd : cr_v.toNat + 3 + Full.fullArenaClauseSize st_wp cr_v.toNat ≤
              st_wp.core.arena.length := by rw [hsz_wp, har_len_wp]; exact hcr_arr
          have hsw_rb := arena_swapLits_keep_inv hlen_wp
            (fullWitnessInv_nw_upd_watches (s := st_sw) (s' := st_wp) hw_sw hlen_wp.core_ok
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
            (fullArenaVarsNodup_of_arena_eq hnd_sw rfl rfl)
            ⟨fullLastLearnedWf_of_refs_eq hext_sw.1 rfl rfl, hext_sw.2⟩
            (by change cr_v.toNat ∈ Full.fullArenaClauseRefs st_sw; rw [hrefs_sw]; exact hcr_ref)
            (k1 := 1) (k2 := r) (by rw [hsz_wp]; omega) (hsz_wp ▸ hr_hi)
          dsimp only at hsw_rb
          have h4 : cr_v.toNat + 3 + 1 = cr_v.toNat + 4 := by omega
          have hr_1_eq : (st_wp.core.arena[cr_v.toNat + 3 + 1]'(by omega)) = repl := by
            apply Option.some_inj.mp; rw [← List.getElem?_eq_getElem (by omega)]
            dsimp only [st_wp, st_sw, ar_sw]
            rw [List.getElem?_set_ne (by omega), h4, List.getElem?_set_self]
            all_goals first | rfl | (simp [st_fr]; omega)
          have hr_r_eq : (st_wp.core.arena[cr_v.toNat + 3 + r]'(by omega)) = not_lit := by
            apply Option.some_inj.mp; rw [← List.getElem?_eq_getElem (by omega)]
            dsimp only [st_wp, st_sw, ar_sw]; rw [List.getElem?_set_self]
            all_goals first | rfl | (simp [st_fr]; omega)
          rw [hr_1_eq, hr_r_eq] at hsw_rb
          have hq_bd := hsplit.q_ge; have hqp_bd := hsplit.q_le_p; have hpe_bd := hsplit.p_le_end
          have hwstk_q' : (off'_bv + (q_v - off_v)).toNat < st_wp.core.wstk.length := by
            rw [hlen_wp.core_ok.wstk_len_arr, hq'_eq, hoff'_eq]; omega
          have hwstk_q1' : (off'_bv + (q_v - off_v)).toNat + 1 < st_wp.core.wstk.length := by
            rw [hlen_wp.core_ok.wstk_len_arr, hq'_eq, hoff'_eq]; omega
          have hq'2_64 : (off'_bv + (q_v - off_v)).toNat + 2 < 2 ^ 64 := by
            rw [hq'_eq, hoff'_eq]; omega
          have hq'1_bv : ((off'_bv + (q_v - off_v)) + 1).toNat =
              (off'_bv + (q_v - off_v)).toNat + 1 := by bv_omega
          have hwstk_q1'_bv : ((off'_bv + (q_v - off_v)) + 1#64).toNat <
              st_wp.core.wstk.length := by
            rw [show (1#64 : BitVec 64) = 1 from rfl, hq'1_bv]; exact hwstk_q1'
          have hp_prev'_eq : (off'_bv + (p2_v - off_v)).toNat =
              (off'_bv.toNat + (p_prev.toNat - off_v.toNat)) + 2 := by
            rw [hp2'_eq, hoff'_eq, hp2_eq]; omega
          have hap_prev : FullSplitWatchesInv F_cur st_wp.core not_lit.toNat off'_bv.toNat
              (off'_bv + (q_v - off_v)).toNat (off'_bv.toNat + (p_prev.toNat - off_v.toNat) + 2)
              (off'_bv + (end_v - off_v)).toNat := by simpa only [← hp_prev'_eq] using hap'
          let ar_rb := (st_wp.core.arena.set (cr_v.toNat + 4) not_lit).set (cr_v.toNat + 3 + r)
            repl
          have har_rb_eq : (st_wp.core.arena.set (cr_v.toNat + 3 + 1) not_lit).set
              (cr_v.toNat + 3 + r) repl = ar_rb := rfl
          rw [har_rb_eq] at hsw_rb
          let st_rb : Full.FullState := { st_wp with core := { st_wp.core with arena := ar_rb } }
          have hap_rb := hap_prev.with_nonwatch (k' := st_rb.core) rfl rfl rfl rfl
            fun r0 hr0 => by
              change r0 ∈ Full.fullArenaClauseRefs st_rb; rw [hsw_rb.2.2.2.2.1]; exact hr0
          have hw_wl := hap_rb.write_large hnot_lt' (by rw [hq'_eq, hoff'_eq]; omega) hwstk_q'
            hwstk_q1' hflag hcr_lt (by
              change cr_v.toNat ∈ Full.fullArenaClauseRefs st_rb; rw [hsw_rb.2.2.2.2.1]
              change cr_v.toNat ∈ Full.fullArenaClauseRefs st_sw; rw [hrefs_sw]; exact hcr_ref)
          let wstk_fin := (st_wp.core.wstk.set (off'_bv + (q_v - off_v)).toNat w0_v).set
            ((off'_bv + (q_v - off_v)).toNat + 1) cr_v
          let st_oom : Full.FullState :=
            { st_rb with core := { st_rb.core with wstk := wstk_fin, oom := 1#64 } }
          have hw_wl' : FullSplitWatchesInv F_cur st_oom.core not_lit.toNat off'_bv.toNat
              ((off'_bv + (q_v - off_v)) + 2#64).toNat (off'_bv + (p2_v - off_v)).toNat
              (off'_bv + (end_v - off_v)).toNat := by
            have hq_p2 : ((off'_bv + (q_v - off_v)) + 2#64).toNat =
                (off'_bv + (q_v - off_v)).toNat + 2 := by bv_omega
            simpa only [hq_p2, hp_prev'_eq] using
              hw_wl.with_nonwatch (k' := st_oom.core) rfl rfl rfl rfl fun _ h => h
          have hlen_oom : st_oom.LengthsOk c :=
            ⟨{ hsw_rb.1.core_ok with
              wstk_len_arr := (by
                rw [List.length_set, List.length_set]; exact hlen_wp.core_ok.wstk_len_arr) },
              hsw_rb.1.scratch_ok⟩
          have hw_oom := fullWitnessInv_nw_upd_watches (s := st_rb) (s' := st_oom)
            (hsw_rb.2.1 : Full.FullWitnessInv c F0 F_cur (withEmptyModeWatches c st_rb).core)
            hlen_oom.core_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          have hwp_464 : (cr_v.setWidth 64 + 4).toNat < st_wp.core.arena.length := by
            rw [hcr4_c0, har_len_wp]; omega
          have hwp_r64 : (cr_v.setWidth 64 + 3 + BitVec.ofNat 64 r).toNat <
              st_wp.core.arena.length := by rw [hr_idx_c0, har_len_wp]; omega
          pt_steps_nogrp
          have hm_oom : (Full.FullMem c st_oom ⋆ R) m := by
            simp only [st_oom, st_rb, st_wp, ar_rb, wstk_fin, hcr4_c0, hr_idx_c0] at hm ⊢
            have hoff'_defeq :
                BitVec.setWidth 64 (wvec'[(BitVec.setWidth 64 not_lit <<< 1).toNat]'
                  (by simpa only [st_wp,
                    show ((1#32 : BitVec 32).signExtend 64).toNat = 1 from rfl] using
                    hwvec_not)) = off'_bv := rfl
            rw [hoff'_defeq, show (st.core.arena.set (cr_v.toNat + 1) (BitVec.ofNat 32 r))[
              cr_v.toNat + 3 + r]'hl_repl_idx = repl from hrepl_get, hq'1_bv] at hm
            rw [show (1#64 : BitVec 64) = 1 from rfl]; exact hm
          exact hJtail off'_bv (ticks_v + 1) (off'_bv + (p2_v - off_v))
              ((off'_bv + (q_v - off_v)) + 2#64) (off'_bv + (end_v - off_v)) true m
            ⟨st_oom, hlen_oom, hw_oom, hmrk0,
              fullArenaVarsNodup_of_arena_eq hsw_rb.2.2.1 rfl rfl,
              ⟨fullLastLearnedWf_of_refs_eq hsw_rb.2.2.2.1.1 rfl rfl, hsw_rb.2.2.2.1.2⟩,
              hdm, hcl1, hcv, hfu, hlm, hws1,
              fullTrailRsnsExt_trans htr (fullTrailRsnsExt_congr rfl rfl rfl rfl),
              fullHbrBufOkW_congr hhbr rfl rfl, hw_wl', fun _ => Or.inl (by simp [st_oom]),
              fun hf => (by cases hf), hm_oom⟩
      · exfalso; pt_clear_big
        have hsz32 : Full.fullArenaClauseSize st cr_v.toNat < 2 ^ 32 := BitVec.isLt _
        have hto := congrArg BitVec.toNat (by assumption : BitVec.ofNat 64 r = 4294967295#64)
        rw [bv64_ofNat_toNat (by omega),
          show (4294967295#64).toNat = 4294967295 from rfl] at hto; omega

/-! ## 2. Parametric `(Γ : Env)` `Func.wp` Contract (`Full.fullProbePropLitSpec`) -/

theorem full_probe_prop_lit_m5_wp (Γ : Env)
    (hFindRepl : ∀ args m Q X, Full.fullFindReplSpec args m Q X →
      Γ "full_find_repl" [i64, i64] [i64] args m Q X)
    (hWatchPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hHbrDom : ∀ args m Q X, Full.fullHbrDomSpec args m Q X →
      Γ "full_hbr_dom" [i64, i32, i32] [i32] args m Q X)
    (hAssignLvl : ∀ args m Q X, Full.fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X) :
    ∀ args m Q X, Full.fullProbePropLitSpec args m Q X →
      Func.wp Γ full_probe_prop_lit_m5_body args m Q X := by
  rintro ⟨h_arg, lit, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hmrk0, hnd0, hext0, hdm0, hcl10, hoom0, hhbr0, hm0, hQ⟩
  have hcl0 := hlen0.core_ok
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hcv_le := hcl0.cur_vars_le
  have hnl_eq : (BitVec.ofNat 64 s.core.cur_vars <<<
      ((1#32 : BitVec 32).signExtend 64).toNat).toNat = 2 * s.core.cur_vars := by
    rw [show ((1#32 : BitVec 32).signExtend 64).toNat = 1 from rfl,
      bv64_shl1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
      bv64_ofNat_toNat (by omega)]
  pt_steps_nogrp
  · exact hQ true s m hlen0 hw0 hmrk0 hnd0 hext0 hdm0 hcl10 rfl rfl rfl rfl
      (fullTrailRsnsExt_refl s.core) hhbr0 (fun hf => by cases hf) (fun _ => hoom0) hm0
  · have hnot_lt : (lit ^^^ 1#32).toNat < 2 * s.core.cur_vars := by
      pt_clear_big
      simp only [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl] at *
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc
      omega
    have hnot_vlt : (lit ^^^ 1#32).toNat < s.core.vals.length := by rw [hcl0.vals_len]; omega
    have hnot_v64 : ((lit ^^^ 1#32).setWidth 64).toNat < s.core.vals.length := by
      rw [bv_c0_zext32_64]; exact hnot_vlt
    pt_steps_nogrp
    · exact hQ true s m hlen0 hw0 hmrk0 hnd0 hext0 hdm0 hcl10 rfl rfl rfl rfl
        (fullTrailRsnsExt_refl s.core) hhbr0 (fun hf => by cases hf) (fun _ => hoom0) hm0
    · have hnot_false : s.core.vals[(lit ^^^ 1#32).toNat]?.getD 0#8 = 0xFF#8 := by
        apply pt_vals_eq_ff_of_nsge hnot_vlt (hw0.vals_domain _ hnot_lt)
        rw [Bool.not_eq_true]; pt_clear_big; exact hc
      have hnot_shl : ((lit ^^^ 1#32).setWidth 64 <<<
          ((1#32 : BitVec 32).signExtend 64).toNat).toNat = 2 * (lit ^^^ 1#32).toNat := by
        rw [show ((1#32 : BitVec 32).signExtend 64).toNat = 1 from rfl,
          bv64_shl1_toNat (by rw [bv_c0_zext32_64]; omega), bv_c0_zext32_64]
      have hwvec_i0 : ((lit ^^^ 1#32).setWidth 64 <<<
          ((1#32 : BitVec 32).signExtend 64).toNat).toNat < s.core.wvec.length := by
        rw [hcl0.wvec_len, hnot_shl]; omega
      have hwvec_i1 : (((lit ^^^ 1#32).setWidth 64 <<<
          ((1#32 : BitVec 32).signExtend 64).toNat) + 1#64).toNat < s.core.wvec.length := by
        rw [hcl0.wvec_len, bv64_add1_toNat (by rw [hnot_shl]; omega), hnot_shl]; omega
      pt_steps_nogrp
      · exact hQ true s m hlen0 hw0 hmrk0 hnd0 hext0 hdm0 hcl10 rfl rfl rfl rfl
          (fullTrailRsnsExt_refl s.core) hhbr0 (fun hf => by cases hf) (fun _ => hoom0) hm0
      · have hsz_pos : 0 < Full.fullWatchSizeCore s.core (lit ^^^ 1#32).toNat := by
          unfold Full.fullWatchSizeCore
          have hidx_eq : 2 * (lit ^^^ 1#32).toNat + 1 =
              (2 * (lit.toNat ^^^ 1) + 1) % 2 ^ 64 := by
            rw [show (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 from rfl, Nat.mod_eq_of_lt (by omega)]
          have hw_lt : 2 * (lit ^^^ 1#32).toNat + 1 < s.core.wvec.length := by
            rw [hcl0.wvec_len]; omega
          have heq_w : s.core.wvec[2 * (lit ^^^ 1#32).toNat + 1]'hw_lt =
              s.core.wvec[(2 * (lit.toNat ^^^ 1) + 1) % 2 ^ 64]'(by
                rw [← hidx_eq]; exact hw_lt) := by congr 1
          have hne : (s.core.wvec[2 * (lit ^^^ 1#32).toNat + 1]'hw_lt).setWidth 64 ≠ 0#64 := by
            rw [heq_w]; pt_clear_big; exact hc
          have hto : ((s.core.wvec[2 * (lit ^^^ 1#32).toNat + 1]'hw_lt).setWidth 64).toNat ≠
              0 := fun h0 => hne (BitVec.eq_of_toNat_eq (by simpa using h0))
          rw [bv_c0_zext32_64] at hto
          rw [List.getElem?_eq_getElem hw_lt, Option.getD_some]
          exact Nat.pos_of_ne_zero hto
        have hwat0 : Full.WatchesInv F_cur s.core := by
          have hw_w := hw0.watches; simp only [Full.ModeWatchesInv, hdm0, ↓reduceIte] at hw_w
          exact hw_w
        have hsplit0 := FullSplitWatchesInv.init hnot_lt hwat0 hsz_pos
        have h_off_eq : (s.core.wvec[((lit ^^^ 1#32).setWidth 64 <<<
            ((1#32 : BitVec 32).signExtend 64).toNat).toNat]'hwvec_i0).setWidth 64 =
            BitVec.ofNat 64 (Full.fullWatchOffCore s.core (lit ^^^ 1#32).toNat) := by
          apply BitVec.eq_of_toNat_eq; unfold Full.fullWatchOffCore
          rw [bv_c0_zext32_64, bv64_ofNat_toNat (Nat.lt_trans (BitVec.isLt _) (by decide)),
            ← hnot_shl, List.getElem?_eq_getElem hwvec_i0, Option.getD_some]
        have h_sz_eq : (s.core.wvec[(((lit ^^^ 1#32).setWidth 64 <<<
            ((1#32 : BitVec 32).signExtend 64).toNat) + 1#64).toNat]'hwvec_i1).setWidth 64 =
            BitVec.ofNat 64 (Full.fullWatchSizeCore s.core (lit ^^^ 1#32).toNat) := by
          apply BitVec.eq_of_toNat_eq; unfold Full.fullWatchSizeCore
          have hwv1_eq : (((lit ^^^ 1#32).setWidth 64 <<<
              ((1#32 : BitVec 32).signExtend 64).toNat) + 1#64).toNat =
              2 * (lit ^^^ 1#32).toNat + 1 := by
            rw [bv64_add1_toNat (by rw [hnot_shl]; omega), hnot_shl]
          rw [bv_c0_zext32_64, bv64_ofNat_toNat (Nat.lt_trans (BitVec.isLt _) (by decide)),
            ← hwv1_eq, List.getElem?_eq_getElem hwvec_i1, Option.getD_some]
        refine wp_join_group
          (fun (off_v, _tk, p_v, q_v, end_v, confl_v, ()) ml =>
            propLitTailInv c F0 F_cur s R (lit ^^^ 1#32)
              (off_v, p_v, q_v, end_v, confl_v, ()) ml)
          (fun _ (off_v, _tk, p_v, q_v, end_v, confl_v, ()) ml htail =>
            propLitTail_wp hnot_lt hQ rfl rfl rfl rfl htail)
          (fun Jtail hJtail => ?_)
        pt_steps_nogrp
        refine wp_loop_inv
          (fun (off_v, _tk, p_v, q_v, end_v, ()) ml =>
            propLitMainInv c F0 F_cur s R (lit ^^^ 1#32) (off_v, p_v, q_v, end_v, ()) ml)
          (fun (_off, _tk, p_v, _q, end_v, ()) _ => end_v.toNat - p_v.toNat)
          (fun Jloop hJloop => ?_)
          (fun Jloop (off_v, ticks_v, p_v, q_v, end_v, ()) ml hmain hJloop => ?_)
        · pt_steps_nogrp
          have hwcap := c.hwcap; unfold dimacsBound at hwcap
          have hbd0 := hwat0.layout.bounds _ hnot_lt
          have hwl0 := hcl0.wlen_le
          have hend0 : (BitVec.ofNat 64 (Full.fullWatchOffCore s.core (lit ^^^ 1#32).toNat) +
              BitVec.ofNat 64 (Full.fullWatchSizeCore s.core (lit ^^^ 1#32).toNat)).toNat =
              Full.fullWatchOffCore s.core (lit ^^^ 1#32).toNat +
              Full.fullWatchSizeCore s.core (lit ^^^ 1#32).toNat := by
            rw [BitVec.toNat_add, bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega),
              Nat.mod_eq_of_lt (by omega)]
          have h_off_c0 : (s.core.wvec[((lit ^^^ 1).setWidth 64 <<< 1).toNat]'
              (by simpa only [show ((1#32 : BitVec 32).signExtend 64).toNat = 1 from rfl,
                show ((1 : BitVec 32).signExtend 64).toNat = 1 from rfl,
                show (1#32 : BitVec 32) = 1 from rfl] using hwvec_i0)).setWidth 64 =
              BitVec.ofNat 64 (Full.fullWatchOffCore s.core (lit ^^^ 1#32).toNat) := by
            simpa only [show ((1#32 : BitVec 32).signExtend 64).toNat = 1 from rfl,
              show ((1 : BitVec 32).signExtend 64).toNat = 1 from rfl,
              show (1#32 : BitVec 32) = 1 from rfl] using h_off_eq
          have h_sz_c0 : (s.core.wvec[((lit ^^^ 1).setWidth 64 <<< 1 + 1).toNat]'
              (by simpa only [show ((1#32 : BitVec 32).signExtend 64).toNat = 1 from rfl,
                show ((1 : BitVec 32).signExtend 64).toNat = 1 from rfl,
                show (1#32 : BitVec 32) = 1 from rfl,
                show (1#64 : BitVec 64) = 1 from rfl] using hwvec_i1)).setWidth 64 =
              BitVec.ofNat 64 (Full.fullWatchSizeCore s.core (lit ^^^ 1#32).toNat) := by
            simpa only [show ((1#32 : BitVec 32).signExtend 64).toNat = 1 from rfl,
              show ((1 : BitVec 32).signExtend 64).toNat = 1 from rfl,
              show (1#32 : BitVec 32) = 1 from rfl,
              show (1#64 : BitVec 64) = 1 from rfl] using h_sz_eq
          rw [h_off_c0, h_sz_c0]
          have hoff0_lt : Full.fullWatchOffCore s.core (lit ^^^ 1#32).toNat < 2 ^ 64 :=
            Nat.lt_trans (BitVec.isLt _) (by decide)
          exact hJloop (BitVec.ofNat 64 (Full.fullWatchOffCore s.core (lit ^^^ 1#32).toNat),
            1 + (BitVec.ofNat 64 (Full.fullWatchSizeCore s.core (lit ^^^ 1#32).toNat) + 31) >>> 5,
            BitVec.ofNat 64 (Full.fullWatchOffCore s.core (lit ^^^ 1#32).toNat),
            BitVec.ofNat 64 (Full.fullWatchOffCore s.core (lit ^^^ 1#32).toNat),
            BitVec.ofNat 64 (Full.fullWatchOffCore s.core (lit ^^^ 1#32).toNat) +
              BitVec.ofNat 64 (Full.fullWatchSizeCore s.core (lit ^^^ 1#32).toNat), ())
            m ⟨s, hlen0, fullWitnessInv_to_nw hcl0 hw0, hmrk0, hnd0, hext0, hdm0, hcl10,
              rfl, rfl, rfl, rfl, fullTrailRsnsExt_refl s.core, hhbr0, by
                simpa only [bv64_ofNat_toNat hoff0_lt, hend0] using hsplit0,
              hnot_false, hoom0, hm0⟩
        · rcases hmain with ⟨st, hlen, hw_nw, hmrk, hnd, hext, hdm, hcl1, hcv, hfu, hlm, hws1,
            htr, hhbr, hsplit, hnf, hoom, hml⟩
          have hcl := hlen.core_ok
          have hnot_lt' : (lit ^^^ 1#32).toNat < 2 * st.core.cur_vars := hcv ▸ hnot_lt
          have hwcap := c.hwcap; unfold dimacsBound at hwcap
          have hbd_st := hsplit.layout.bounds _ hnot_lt'
          rw [hsplit.off_eq, hsplit.sz_eq] at hbd_st
          have hwl_st := hcl.wlen_le; have hwa_st := hcl.wstk_len_arr
          have hqp := hsplit.q_ge; have hqp_le := hsplit.q_le_p; have hpe := hsplit.p_le_end
          pt_steps_nogrp
          · have hp_lt : p_v.toNat < end_v.toNat := by pt_bound
            have hp_wa : p_v.toNat < st.core.wstk.length := by omega
            have hp1_64 : p_v.toNat + 1 < 2 ^ 64 := by omega
            have hp1_eq : (p_v + 1#64).toNat = p_v.toNat + 1 := bv64_add1_toNat hp1_64
            let w0_v := st.core.wstk[p_v.toNat]'hp_wa
            have hw0_get : st.core.wstk[p_v.toNat]? = some w0_v :=
              List.getElem?_eq_getElem hp_wa
            have hcv64 : s.core.cur_vars < 2 ^ 64 := by
              have := hcl0.cur_vars_le; omega
            have h2cv64 : 2 * s.core.cur_vars < 2 ^ 64 := by omega
            pt_steps_nogrp
            refine wp_join_group (ts := [])
              (fun () m1 => m1 = ml ∧
                ∀ hlt : (w0_v &&& 0x7FFFFFFF#32).toNat < 2 * st.core.cur_vars,
                  (0#32).slt ((st.core.vals[(w0_v &&& 0x7FFFFFFF#32).toNat]'(by
                    rw [hcl.vals_len]; have := hcl.cur_vars_le; omega)).signExtend 32) = false)
              ?_ ?_
            · rintro _ ⟨⟩ ml1 ⟨hml1, hblk_nsgt⟩
              subst ml1
              pt_steps_nogrp
              · have hflag_b : (w0_v &&& 0x80000000#32) ≠ 0#32 := by pt_clear_big; exact hc
                obtain ⟨hot_lt, hent_b, hrem'⟩ :=
                  Full.watchSlice_inv_bin hsplit.rem_slice (by omega) hw0_get hflag_b
                have hq_wa : q_v.toNat < st.core.wstk.length := by omega
                have hrem_p1 : end_v.toNat - (p_v.toNat + 1) =
                    end_v.toNat - p_v.toNat - 1 := by omega
                have hrem_p1' : Full.WatchSliceOk F_cur st.core (lit ^^^ 1#32).toNat
                    (p_v.toNat + 1) (end_v.toNat - (p_v.toNat + 1)) := by
                  simpa only [hrem_p1] using hrem'
                have hsw_pre : FullSplitWatchesInv F_cur st.core (lit ^^^ 1#32).toNat
                    off_v.toNat q_v.toNat (p_v.toNat + 1) end_v.toNat :=
                  ⟨hsplit.layout, hsplit.off_eq, hsplit.sz_eq, hsplit.sz_pos, hsplit.q_ge,
                    (by omega), (by omega), hsplit.other_slices, hsplit.kept_slice, hrem_p1'⟩
                have hsw_wb := FullSplitWatchesInv.write_bin (c := c) (p := p_v.toNat)
                  (w0 := w0_v) hsw_pre hnot_lt' hqp_le hq_wa hflag_b hot_lt hent_b
                  (by rw [hcv]; exact hcv_le)
                let st_wb : Full.FullState :=
                  { st with core := { st.core with wstk := st.core.wstk.set q_v.toNat w0_v } }
                have hlen_wb : st_wb.LengthsOk c :=
                  ⟨{ hcl with wstk_len_arr := by simp [st_wb, hwa_st] }, hlen.scratch_ok⟩
                have hw_wb := fullWitnessInv_nw_upd_watches (s := st) (s' := st_wb) hw_nw
                  hlen_wb.core_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                have hnd_wb := fullArenaVarsNodup_of_arena_eq hnd rfl rfl
                have hext_wb : Full.FullExtScratchOk c st_wb :=
                  ⟨fullLastLearnedWf_of_refs_eq hext.1 rfl rfl, hext.2⟩
                have htr_wb := fullTrailRsnsExt_trans htr
                  (fullTrailRsnsExt_congr rfl rfl rfl rfl)
                have hhbr_wb := fullHbrBufOkW_congr hhbr rfl rfl
                have hq1_64 : q_v.toNat + 1 < 2 ^ 64 := by omega
                have hq1_eq : (q_v + 1#64).toNat = q_v.toNat + 1 := bv64_add1_toNat hq1_64
                have hsw_wb' : FullSplitWatchesInv F_cur st_wb.core (lit ^^^ 1#32).toNat
                    off_v.toNat (q_v + 1#64).toNat (p_v + 1#64).toNat end_v.toNat := by
                  simpa only [st_wb, hq1_eq, hp1_eq] using hsw_wb
                have hot_vlt : (w0_v &&& 2147483647#32).toNat < st_wb.core.vals.length := by
                  rw [hlen_wb.core_ok.vals_len]
                  have hle_wb := hlen_wb.core_ok.cur_vars_le
                  exact Nat.lt_of_lt_of_le hot_lt (by omega)
                have hot_v64 : ((w0_v &&& 2147483647#32).setWidth 64).toNat <
                    st_wb.core.vals.length := by rw [bv_c0_zext32_64]; exact hot_vlt
                have hot_nsgt := hblk_nsgt hot_lt
                pt_steps_nogrp
                · exfalso
                  pt_clear_big
                  rw [Nat.mod_eq_of_lt hcv64, Nat.mod_eq_of_lt h2cv64] at hc
                  rw [hcv] at hot_lt
                  exact absurd hot_lt (Nat.not_lt.mpr hc)
                · have hot_ff : st_wb.core.vals[(w0_v &&& 2147483647#32).toNat]?.getD 0#8 =
                        0xFF#8 := by
                      apply pt_vals_eq_ff_of_slt hot_vlt (hw_wb.vals_domain _ hot_lt)
                      pt_clear_big; exact hc
                  let st_c : Full.FullState := { st_wb with core := { st_wb.core with
                    confl_type := 1#64, confl_lit0 := (lit ^^^ 1#32).setWidth 64,
                    confl_lit1 := (w0_v &&& 2147483647#32).setWidth 64 } }
                  have hlen_c : st_c.LengthsOk c :=
                    ⟨{ hlen_wb.core_ok with }, hlen_wb.scratch_ok⟩
                  have hw_c := fullWitnessInv_nw_upd_watches (s := st_wb) (s' := st_c) hw_wb
                    hlen_c.core_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                  have hconfl_ok : Full.FullConflictOkW F_cur st_c := by
                    refine Or.inl ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
                    · dsimp [st_c]; rw [bv_c0_zext32_64]; exact hnot_lt'
                    · dsimp [st_c]; rw [bv_c0_zext32_64]; exact hot_lt
                    · dsimp [st_c]; rw [bv_c0_zext32_64]; exact hnf
                    · dsimp [st_c]; rw [bv_c0_zext32_64]; exact hot_ff
                    · dsimp [st_c]; rw [bv_c0_zext32_64]; exact hent_b
                  pt_steps_nogrp
                  exact hJtail (off_v, ticks_v, p_v + 1#64, q_v + 1#64, end_v, true, ()) m
                    ⟨st_c, hlen_c, hw_c, hmrk,
                      fullArenaVarsNodup_of_arena_eq hnd_wb rfl rfl,
                      ⟨fullLastLearnedWf_of_refs_eq hext_wb.1 rfl rfl, hext_wb.2⟩,
                      hdm, hcl1, hcv, hfu, hlm, hws1,
                      fullTrailRsnsExt_trans htr_wb (fullTrailRsnsExt_congr rfl rfl rfl rfl),
                      fullHbrBufOkW_congr hhbr_wb rfl rfl,
                      hsw_wb'.with_nonwatch (k' := st_c.core) rfl rfl rfl rfl fun _ h => h,
                      fun _ => Or.inr hconfl_ok, (fun hf => by cases hf), hm⟩
                · have hot_0 : st_wb.core.vals[(w0_v &&& 2147483647#32).toNat]?.getD 0#8 =
                      0#8 := by
                    apply pt_vals_eq_0_of_flags hot_vlt (hw_wb.vals_domain _ hot_lt)
                      (by dsimp only [st_wb]; rw [hot_nsgt]; decide)
                    rw [Bool.not_eq_true]; dsimp only [st_wb, w0_v]; pt_clear_big; assumption
                  c0_call hAssignLvl
                  refine ⟨c, st_wb, R, rfl, hlen_wb, hm, ?_⟩
                  have hcur_wb : st_wb.core.cur_vars ≤ c.max_vars := hlen_wb.core_ok.cur_vars_le
                  have hte_wb : st_wb.core.trail_end < st_wb.core.cur_vars :=
                    hw_wb.trail_end_lt_of_unassigned hot_lt hot_0
                  have hno_wb : ¬ (st_wb.core.cur_vars ≤
                      (st.core.wstk[p_v.toNat] &&& (2147483647 : BitVec 32)).toNat / 2 ∨
                      c.max_vars ≤ st_wb.core.trail_end ∨
                      st_wb.core.vals[(st.core.wstk[p_v.toNat] &&&
                        (2147483647 : BitVec 32)).toNat]?.getD 0#8 ≠ 0#8) := by
                    intro hbad
                    rcases hbad with h1 | h2 | h3
                    · have hst_cv : st_wb.core.cur_vars = st.core.cur_vars := rfl
                      change st_wb.core.cur_vars ≤ (w0_v &&& 2147483647#32).toNat / 2 at h1
                      omega
                    · exact absurd h2 (Nat.not_le.mpr (Nat.lt_of_lt_of_le hte_wb hcur_wb))
                    · exact h3 hot_0
                  rw [ite_eq_right hno_wb]; dsimp only
                  intro flags' unass' phases' m_a hfll hph hm_a
                  have hnot_31 : (lit ^^^ 1#32).toNat < 0x7FFFFFFF := by omega
                  obtain ⟨hbs_msb, hbs_ne, hbs_lit⟩ := bv32_set_bin_watch_spec hnot_31
                  obtain ⟨kf, hkf, hkeq⟩ := (hw_wb.vals_false_iff _ hnot_lt').mp hnf
                  have hklvl := hw_wb.lvl_le kf hkf
                  dsimp only [withEmptyModeWatches] at hklvl
                  have hkv_eq : (st_wb.core.trl[kf]?.getD 0#32).toNat / 2 =
                      (lit ^^^ 1#32).toNat / 2 := by
                    rw [hkeq]; exact Full.fullInv_var_xor1 _
                  rw [hkv_eq, hcl1] at hklvl
                  have hu := unitAssignLvl_preserves_witness hlen_wb hw_wb
                    (other := w0_v &&& 2147483647#32)
                    (rsn := ((lit ^^^ 1#32) &&& 2147483647#32) ||| 2147483648#32)
                    (alvl := 1#32) (not_lit := (lit ^^^ 1#32).toNat)
                    (flags' := flags') (phases' := phases') (unass' := unass')
                    (unfl' := st_wb.core.unflushed) hot_lt hfll hph hot_0 hnot_lt' hnf
                    (by decide) (by rw [hcl1]; decide) hbs_ne (by
                      rw [ite_eq_left hbs_msb, hbs_lit]
                      refine ⟨hnot_lt', entails_bin_swap hent_b, kf, hkf, hkeq,
                        by simpa using hklvl⟩)
                    (fun hc_msb => absurd hc_msb hbs_msb)
                  dsimp only at hu hm_a
                  let st_a : Full.FullState :=
                    { st_wb with
                      core := { st_wb.core with
                        vals := (st_wb.core.vals.set (w0_v &&& 2147483647#32).toNat 1#8).set
                          ((w0_v &&& 2147483647#32).toNat ^^^ 1) 0xFF#8
                        flags := flags'
                        lvl := st_wb.core.lvl.set ((w0_v &&& 2147483647#32).toNat / 2) 1#32
                        rsns := st_wb.core.rsns.set ((w0_v &&& 2147483647#32).toNat / 2)
                          (((lit ^^^ 1#32) &&& 2147483647#32) ||| 2147483648#32)
                        trl := st_wb.core.trl.set st_wb.core.trail_end
                          (w0_v &&& 2147483647#32)
                        trail_pos := st_wb.core.trail_pos.set
                          ((w0_v &&& 2147483647#32).toNat / 2)
                          (BitVec.ofNat 32 st_wb.core.trail_end)
                        trail_end := st_wb.core.trail_end + 1, unassigned := unass' }
                      scratch := { st_wb.scratch with phases := phases' } }
                  have hlen_a : st_a.LengthsOk c :=
                    ⟨{ hlen_wb.core_ok with
                      vals_len := by simp [st_a, hlen_wb.core_ok.vals_len],
                      flags_len := by simp [st_a, hfll],
                      lvl_len := by simp [st_a, hlen_wb.core_ok.lvl_len],
                      rsns_len := by simp [st_a, hlen_wb.core_ok.rsns_len],
                      trl_len := by simp [st_a, hlen_wb.core_ok.trl_len],
                      trail_pos_len := by simp [st_a, hlen_wb.core_ok.trail_pos_len],
                      trail_end_le := by simp [st_a]; omega,
                      propagated_le := by
                        simp [st_a]; have := hlen_wb.core_ok.propagated_le; omega },
                      { hlen_wb.scratch_ok with phases_len := by simp [st_a, hph] }⟩
                  have htr_ja := fullTrailRsnsExt_trans
                    (fullTrailRsnsExt_congr (k1 := st_wb.core)
                      (k2 := (withEmptyModeWatches c st_wb).core) rfl rfl rfl rfl)
                    (fullTrailRsnsExt_trans
                      (fullTrailRsnsExt_of_assign_lvl
                        (rsn := ((lit ^^^ 1#32) &&& 2147483647#32) ||| 2147483648#32)
                        (alvl := 1#32) (flags' := flags') (unass' := unass')
                        (unfl' := st_wb.core.unflushed) hw_wb hot_lt hot_0)
                      (fullTrailRsnsExt_congr (k2 := st_a.core) rfl rfl rfl rfl))
                  have htr_a := fullTrailRsnsExt_trans htr_wb htr_ja
                  refine hJloop (off_v, ticks_v + 1#64, p_v + 1#64, q_v + 1#64, end_v, ()) m_a
                    (by dsimp only; rw [hp1_eq]; omega)
                    ⟨st_a, hlen_a, hu.1, fun w hw => hmrk w hw,
                      fullArenaVarsNodup_of_arena_eq hnd_wb rfl rfl,
                      ⟨fullLastLearnedWf_of_refs_eq hext_wb.1 rfl rfl, hext_wb.2⟩,
                      hdm, hcl1, hcv, hfu, hlm, hws1, htr_a,
                      fullHbrBufOkW_congr hhbr_wb rfl rfl,
                      hsw_wb'.with_nonwatch (k' := st_a.core) rfl rfl rfl rfl fun _ h => h,
                      hu.2, hoom, hm_a⟩
              · have hflag_l : (w0_v &&& 0x80000000#32) = 0#32 := by
                  change (st.core.wstk[p_v.toNat]'hp_wa &&& 2147483648#32) = 0#32
                  assumption
                obtain ⟨hrem2, _cr_v, _hcr_get, _hcr_lt, _hcr_ref, _hrem'⟩ :=
                  Full.watchSlice_inv_large hsplit.rem_slice (by omega) hw0_get hflag_l
                exfalso
                have hc' : end_v.toNat ≤ (p_v.toNat + 1) % 2 ^ 64 := hc
                rw [Nat.mod_eq_of_lt hp1_64] at hc'
                omega
              · have hflag_l : (w0_v &&& 0x80000000#32) = 0#32 := by pt_clear_big; assumption
                obtain ⟨hrem2, cr_v, hcr_get, hcr_lt, hcr_ref, hrem'⟩ :=
                  Full.watchSlice_inv_large hsplit.rem_slice (by omega) hw0_get hflag_l
                have hp1_wa : (p_v + 1#64).toNat < st.core.wstk.length := by omega
                have hcr_at : st.core.wstk[(p_v + 1#64).toNat]'hp1_wa = cr_v :=
                  Option.some_inj.mp
                    (by rw [← List.getElem?_eq_getElem hp1_wa, hp1_eq]; exact hcr_get)
                have hp2_64 : p_v.toNat + 2 < 2 ^ 64 := by omega
                have hp2_eq : (p_v + 2#64).toNat = p_v.toNat + 2 := by bv_omega
                have hsplit_prev : FullSplitWatchesInv F_cur st.core (lit ^^^ 1#32).toNat
                    off_v.toNat q_v.toNat (p_v.toNat + 2) end_v.toNat :=
                  hsplit.advance_rem (by omega) (by omega)
                    (by simpa only [show end_v.toNat - (p_v.toNat + 2) =
                      end_v.toNat - p_v.toNat - 2 by omega] using hrem')
                have hsplit_p2 : FullSplitWatchesInv F_cur st.core (lit ^^^ 1#32).toNat
                    off_v.toNat q_v.toNat (p_v + 2#64).toNat end_v.toNat := by
                  simpa only [← hp2_eq] using hsplit_prev
                have hwf_cr := hw_nw.arena.refs_wf cr_v.toNat hcr_ref
                have hcr_sz3 : 3 ≤ Full.fullArenaClauseSize st cr_v.toNat := hwf_cr.2.1
                have hcr_bd : cr_v.toNat + 3 + Full.fullArenaClauseSize st cr_v.toNat ≤
                    st.core.arena_len := Nat.le_trans hwf_cr.2.2.1 hwf_cr.2.2.2.1
                have hcr_arr : cr_v.toNat + 3 + Full.fullArenaClauseSize st cr_v.toNat ≤
                    st.core.arena.length := by
                  have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
                have ha_lt := c.harena; unfold dimacsBound at ha_lt
                have hcr64 : (cr_v.setWidth 64).toNat = cr_v.toNat := bv_c0_zext32_64 _
                have hcr_lt' : cr_v.toNat < st.core.arena.length := by omega
                have hcr2_lt : cr_v.toNat + 2 < st.core.arena.length := by omega
                have hcr3_lt : cr_v.toNat + 3 < st.core.arena.length := by omega
                have hcr4_lt : cr_v.toNat + 4 < st.core.arena.length := by omega
                have har_len : st.core.arena.length = c.arena_cap := hcl.arena_len_arr
                have har_64 : st.core.arena_len < 2 ^ 64 := by have := hcl.arena_len_le; omega
                have hp2_sum : p_v + 1 + 1 = p_v + 2#64 := by bv_omega
                have hcr_mod : st.core.wstk[(p_v.toNat + 1) % 2 ^ 64]'(by
                    rw [Nat.mod_eq_of_lt hp1_64, ← hp1_eq]; exact hp1_wa) = cr_v :=
                  Option.some_inj.mp (by
                    rw [← List.getElem?_eq_getElem, Nat.mod_eq_of_lt hp1_64]; exact hcr_get)
                have hsz_mod : (st.core.arena[(cr_v.toNat + 2) % 2 ^ 64]'(by
                    rw [Nat.mod_eq_of_lt (by omega : cr_v.toNat + 2 < 2 ^ 64)]
                    exact hcr2_lt)).toNat = Full.fullArenaClauseSize st cr_v.toNat := by
                  have hidx2 : (cr_v.toNat + 2) % 2 ^ 64 = cr_v.toNat + 2 :=
                    Nat.mod_eq_of_lt (by omega)
                  have heq : st.core.arena[(cr_v.toNat + 2) % 2 ^ 64]'(by
                      rw [hidx2]; exact hcr2_lt) = st.core.arena[cr_v.toNat + 2]'hcr2_lt :=
                    Option.some_inj.mp (by
                      rw [← List.getElem?_eq_getElem, hidx2, ← List.getElem?_eq_getElem hcr2_lt])
                  rw [heq]; unfold Full.fullArenaClauseSize Full.fullArenaClauseSizeCore
                  rw [List.getElem?_eq_getElem hcr2_lt, Option.getD_some]
                pt_steps_nogrp
                · exfalso
                  have h2 : cr_v.toNat + 3 < 2 ^ 64 := by omega
                  rw [hcr_mod, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt har_64] at hc
                  omega
                pt_steps_nogrp
                · rw [hp2_sum]
                  exact hJloop (off_v, ticks_v + 1, p_v + 2#64, q_v, end_v, ()) ml
                    (by dsimp only; rw [hp2_eq]; omega)
                    ⟨st, hlen, hw_nw, hmrk, hnd, hext, hdm, hcl1, hcv, hfu, hlm, hws1, htr,
                      hhbr, hsplit_p2, hnf, hoom, hml⟩
                · exfalso; simp only [hcr_mod, hsz_mod] at hc; omega
                · exfalso
                  simp only [hcr_mod, hsz_mod] at hc
                  have h2 : cr_v.toNat + 3 + Full.fullArenaClauseSize st cr_v.toNat < 2 ^ 64 :=
                    by omega
                  rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt har_64] at hc; omega
                · have hcr_ng : Full.fullArenaClauseGarb st cr_v.toNat = false := by
                    unfold Full.fullArenaClauseGarb Full.fullArenaClauseGarbCore
                      Full.fullArenaHdrCore
                    rw [List.getElem?_eq_getElem hcr_lt', Option.getD_some]
                    have hidx : cr_v.toNat =
                        st.core.wstk[(p_v.toNat + 1) % 2 ^ 64].toNat :=
                      congrArg BitVec.toNat hcr_mod.symm
                    have heq_w : st.core.arena[cr_v.toNat]'hcr_lt' =
                        st.core.arena[st.core.wstk[(p_v.toNat + 1) % 2 ^ 64].toNat]'(by
                          rw [← hidx]; exact hcr_lt') := by
                      congr 1
                    have heq0 : (st.core.arena[cr_v.toNat]'hcr_lt' &&& 0x00080000#32) =
                        0#32 := by
                      rw [heq_w]
                      change (_ &&& 524288#32) = 0#32
                      assumption
                    change ((_ &&& (BitVec.ofNat 32 524288)) != 0#32) = false
                    simp [heq0]
                  have hp1_c0 : st.core.wstk[(p_v + 1 : BitVec 64).toNat]'hp1_wa = cr_v := hcr_at
                  have hcr3_v : (cr_v.setWidth 64 + (3 : BitVec 64)).toNat = cr_v.toNat + 3 := by
                    rw [BitVec.toNat_add, hcr64, show (3 : BitVec 64).toNat = 3 from rfl,
                      Nat.mod_eq_of_lt (by omega)]
                  have hcr4_v : (cr_v.setWidth 64 + (4 : BitVec 64)).toNat = cr_v.toNat + 4 := by
                    rw [BitVec.toNat_add, hcr64, show (4 : BitVec 64).toNat = 4 from rfl,
                      Nat.mod_eq_of_lt (by omega)]
                  simp only [hp1_c0]
                  pt_steps_nogrp
                  try simp only [hcr3_v, hcr4_v]
                  let l0_v := st.core.arena[cr_v.toNat + 3]'hcr3_lt
                  let l1_v := st.core.arena[cr_v.toNat + 4]'hcr4_lt
                  refine wp_join_group
                    (fun (lv, ()) mj => ∃ st_x : Full.FullState,
                      st_x.LengthsOk c ∧
                      Full.FullWitnessInv c F0 F_cur (withEmptyModeWatches c st_x).core ∧
                      Full.FullMrkZero c st_x ∧ Full.FullArenaVarsNodup st_x ∧
                      Full.FullExtScratchOk c st_x ∧
                      st_x.core.dense_mode = 0#64 ∧ st_x.core.cur_level = 1 ∧
                      st_x.core.cur_vars = s.core.cur_vars ∧ st_x.core.fuel = s.core.fuel ∧
                      st_x.core.lit_mark = s.core.lit_mark ∧
                      st_x.scratch.work_stk1 = s.scratch.work_stk1 ∧
                      Full.FullTrailRsnsExt s.core st_x.core ∧
                      Full.FullHbrBufOkW F_cur st_x st_x.core.tmp_cnt ∧
                      FullSplitWatchesInv F_cur st_x.core (lit ^^^ 1#32).toNat off_v.toNat
                        q_v.toNat (p_v + 2#64).toNat end_v.toNat ∧
                      st_x.core.vals[(lit ^^^ 1#32).toNat]?.getD 0#8 = 0xFF#8 ∧
                      st_x.core.oom = 0#64 ∧ cr_v.toNat ∈ Full.fullArenaClauseRefs st_x ∧
                      Full.fullArenaClauseGarb st_x cr_v.toNat = false ∧
                      3 ≤ Full.fullArenaClauseSize st_x cr_v.toNat ∧
                      cr_v.toNat + 3 + Full.fullArenaClauseSize st_x cr_v.toNat ≤
                        st_x.core.arena_len ∧
                      cr_v.toNat + 3 + Full.fullArenaClauseSize st_x cr_v.toNat ≤
                        st_x.core.arena.length ∧
                      (st_x.core.arena[cr_v.toNat + 3]?.getD 0#32).toNat = lv.toNat ∧
                      (st_x.core.arena[cr_v.toNat + 4]?.getD 0#32).toNat =
                        (lit ^^^ 1#32).toNat ∧
                      (Full.FullMem c st_x ⋆ R) mj)
                    (fun _ (lv, ()) mj ⟨st_x, hx_len, hx_nw, hx_mrk, hx_nd, hx_ext, hx_dm,
                      hx_cl1, hx_cv, hx_fu, hx_lm, hx_ws1, hx_tr, hx_hbr, hx_sw, hx_nf,
                      hx_oom, hx_ref, hx_ng, hx_sz, hx_bd, hx_arr, hx_l0, hx_not, hm_x⟩ => by
                      rw [hp2_sum]
                      exact m5PropLitLarge_wp (not_lit := lit ^^^ 1#32) (p_prev := p_v)
                        (ticks_v := ticks_v + 1)
                        hFindRepl hWatchPush hHbrDom hAssignLvl hnot_lt
                        (fun off_r tk_r p_r q_r end_r cf_r m' hm' =>
                          hJtail (off_r, tk_r, p_r, q_r, end_r, cf_r, ()) m' hm')
                        (fun off_r tk_r p_r q_r end_r m' hm' hdec =>
                          hJloop (off_r, tk_r, p_r, q_r, end_r, ()) m'
                            (by dsimp only; rw [hdec, hp2_eq]; omega) hm')
                        rfl rfl rfl rfl rfl rfl rfl hp2_eq hx_len hx_nw hx_mrk hx_nd
                        hx_ext hx_dm hx_cl1 hx_cv hx_fu hx_lm hx_ws1 hx_tr hx_hbr hx_sw
                        hqp_le hx_nf hx_oom hflag_l hcr_lt hx_ref hx_ng hx_sz hx_bd hx_arr
                        (by rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hx_l0)
                        (by
                          rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hx_not)
                        hm_x)
                    (fun Js_3 hJs3 => by
                      pt_steps_nogrp
                      · have hl0_eq : l0_v = lit ^^^ 1#32 := by pt_clear_big; exact hc
                        have hsw_l := arena_swapLits_keep_inv hlen hw_nw hnd hext hcr_ref
                          (k1 := 0) (k2 := 1) (by omega) (by omega)
                        dsimp only at hsw_l
                        let ar_x := (st.core.arena.set (cr_v.toNat + 3) l1_v).set
                          (cr_v.toNat + 4) (lit ^^^ 1#32)
                        have har_x_eq : (st.core.arena.set (cr_v.toNat + 3 + 0) l1_v).set
                            (cr_v.toNat + 3 + 1) l0_v = ar_x := by
                          simp only [hl0_eq]; rfl
                        rw [har_x_eq] at hsw_l
                        let st_x : Full.FullState :=
                          { st with core := { st.core with arena := ar_x } }
                        obtain ⟨hx_len, hx_nw, hx_nd, hx_ext, hx_ref, hper_x⟩ :=
                          (hsw_l : st_x.LengthsOk c ∧
                            Full.FullWitnessInv c F0 F_cur (withEmptyModeWatches c st_x).core ∧
                            Full.FullArenaVarsNodup st_x ∧ Full.FullExtScratchOk c st_x ∧
                            Full.fullArenaClauseRefs st_x = Full.fullArenaClauseRefs st ∧
                            ∀ r0 ∈ Full.fullArenaClauseRefs st,
                              Full.fullArenaClauseSize st_x r0 = Full.fullArenaClauseSize st r0 ∧
                              Full.fullArenaClauseGarb st_x r0 = Full.fullArenaClauseGarb st r0 ∧
                              (Full.fullArenaClauseLits st_x r0).Perm
                                (Full.fullArenaClauseLits st r0))
                        have hsz_x : Full.fullArenaClauseSize st_x cr_v.toNat =
                            Full.fullArenaClauseSize st cr_v.toNat := (hper_x _ hcr_ref).1
                        have hng_x : Full.fullArenaClauseGarb st_x cr_v.toNat = false :=
                          (hper_x _ hcr_ref).2.1.trans hcr_ng
                        have harr_x : cr_v.toNat + 3 + Full.fullArenaClauseSize st_x cr_v.toNat ≤
                            st_x.core.arena.length := by
                          simpa only [st_x, ar_x, hsz_x, List.length_set] using hcr_arr
                        have hx_l3 : (st_x.core.arena[cr_v.toNat + 3]?.getD 0#32).toNat =
                            l1_v.toNat := by
                          dsimp only [st_x, ar_x]
                          rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
                            Option.getD_some]
                        have hx_l4 : (st_x.core.arena[cr_v.toNat + 4]?.getD 0#32).toNat =
                            (lit ^^^ 1#32).toNat := by
                          dsimp only [st_x, ar_x]
                          rw [List.getElem?_set_self (by simp only [List.length_set]; omega),
                            Option.getD_some]
                        have hm_x : (Full.FullMem c st_x ⋆ R) m := by
                          dsimp only [st_x, ar_x]
                          simp only [hcr3_v, hcr4_v] at hm
                          exact hm
                        exact hJs3 (l1_v, ()) m
                          ⟨st_x, hx_len, hx_nw, hmrk, hx_nd, hx_ext, hdm, hcl1, hcv, hfu, hlm,
                            hws1, fullTrailRsnsExt_trans htr
                              (fullTrailRsnsExt_congr rfl rfl rfl rfl),
                            fullHbrBufOkW_congr hhbr rfl rfl,
                            hsplit_p2.with_nonwatch (k' := st_x.core) rfl rfl rfl rfl fun r0 hr0 =>
                              by change r0 ∈ Full.fullArenaClauseRefs st_x; rw [hx_ref]; exact hr0,
                            hnf, hoom, hx_ref ▸ hcr_ref, hng_x, hsz_x ▸ hcr_sz3,
                            by simpa only [st_x, hsz_x] using hcr_bd, harr_x, hx_l3, hx_l4, hm_x⟩
                      · rw [hp2_sum]
                        exact hJloop (off_v, ticks_v + 1, p_v + 2#64, q_v, end_v, ()) ml
                          (by dsimp only; rw [hp2_eq]; omega)
                          ⟨st, hlen, hw_nw, hmrk, hnd, hext, hdm, hcl1, hcv, hfu, hlm, hws1,
                            htr, hhbr, hsplit_p2, hnf, hoom, hml⟩
                      · have hl1_eq : l1_v = lit ^^^ 1#32 := by
                          pt_clear_big; first | exact hc | exact not_ne_iff.mp hc
                        exact hJs3 (l0_v, ()) ml
                          ⟨st, hlen, hw_nw, hmrk, hnd, hext, hdm, hcl1, hcv, hfu, hlm, hws1,
                            htr, hhbr, hsplit_p2, hnf, hoom, hcr_ref, hcr_ng, hcr_sz3, hcr_bd,
                            hcr_arr,
                            by rw [List.getElem?_eq_getElem hcr3_lt, Option.getD_some],
                            by
                              rw [List.getElem?_eq_getElem hcr4_lt, Option.getD_some]
                              exact congrArg BitVec.toNat hl1_eq,
                            hml⟩)
            · rintro J2 hJ2
              pt_steps_nogrp
              · have hblk_lt : (w0_v &&& 0x7FFFFFFF#32).toNat < 2 * st.core.cur_vars := by
                  pt_clear_big
                  rw [Nat.mod_eq_of_lt hcv64, Nat.mod_eq_of_lt h2cv64] at hc
                  rw [hcv]; exact hc
                have hblk_vlt : (w0_v &&& 0x7FFFFFFF#32).toNat < st.core.vals.length := by
                  rw [hcl.vals_len]; have := hcl.cur_vars_le; omega
                have hblk_v64 : ((w0_v &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                    st.core.vals.length := by rw [bv_c0_zext32_64]; exact hblk_vlt
                pt_steps_nogrp
                · have hflag_b : (w0_v &&& 0x80000000#32) ≠ 0#32 := by pt_clear_big; exact hc
                  obtain ⟨hot_lt, hent_b, hrem'⟩ :=
                    Full.watchSlice_inv_bin hsplit.rem_slice (by omega) hw0_get hflag_b
                  have hq_wa : q_v.toNat < st.core.wstk.length := by omega
                  have hrem_p1 : end_v.toNat - (p_v.toNat + 1) =
                      end_v.toNat - p_v.toNat - 1 := by omega
                  have hrem_p1' : Full.WatchSliceOk F_cur st.core (lit ^^^ 1#32).toNat
                      (p_v.toNat + 1) (end_v.toNat - (p_v.toNat + 1)) := by
                    simpa only [hrem_p1] using hrem'
                  have hsw_pre : FullSplitWatchesInv F_cur st.core (lit ^^^ 1#32).toNat
                      off_v.toNat q_v.toNat (p_v.toNat + 1) end_v.toNat :=
                    ⟨hsplit.layout, hsplit.off_eq, hsplit.sz_eq, hsplit.sz_pos, hsplit.q_ge,
                      (by omega), (by omega), hsplit.other_slices, hsplit.kept_slice, hrem_p1'⟩
                  have hsw_wb := FullSplitWatchesInv.write_bin (c := c) (p := p_v.toNat)
                    (w0 := w0_v) hsw_pre hnot_lt' hqp_le hq_wa hflag_b hot_lt hent_b
                    (by rw [hcv]; exact hcv_le)
                  let st_wb : Full.FullState :=
                    { st with core := { st.core with wstk := st.core.wstk.set q_v.toNat w0_v } }
                  have hlen_wb : st_wb.LengthsOk c :=
                    ⟨{ hcl with wstk_len_arr := by simp [st_wb, hwa_st] }, hlen.scratch_ok⟩
                  have hw_wb := fullWitnessInv_nw_upd_watches (s := st) (s' := st_wb) hw_nw
                    hlen_wb.core_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                  have hq1_64 : q_v.toNat + 1 < 2 ^ 64 := by omega
                  have hq1_eq : (q_v + 1#64).toNat = q_v.toNat + 1 := bv64_add1_toNat hq1_64
                  have hsw_wb' : FullSplitWatchesInv F_cur st_wb.core (lit ^^^ 1#32).toNat
                      off_v.toNat (q_v + 1#64).toNat (p_v + 1#64).toNat end_v.toNat := by
                    simpa only [st_wb, hq1_eq, hp1_eq] using hsw_wb
                  pt_steps_nogrp
                  exact hJloop (off_v, ticks_v, p_v + 1#64, q_v + 1#64, end_v, ()) m
                    (by dsimp only; rw [hp1_eq]; omega)
                    ⟨st_wb, hlen_wb, hw_wb, hmrk, fullArenaVarsNodup_of_arena_eq hnd rfl rfl,
                      ⟨fullLastLearnedWf_of_refs_eq hext.1 rfl rfl, hext.2⟩,
                      hdm, hcl1, hcv, hfu, hlm, hws1,
                      fullTrailRsnsExt_trans htr (fullTrailRsnsExt_congr rfl rfl rfl rfl),
                      fullHbrBufOkW_congr hhbr rfl rfl, hsw_wb', hnf, hoom, hm⟩
                · have hflag_l : (w0_v &&& 0x80000000#32) = 0#32 := by assumption
                  obtain ⟨hrem2, cr_v, hcr_get, hcr_lt, hcr_ref, hrem'⟩ :=
                    Full.watchSlice_inv_large hsplit.rem_slice (by omega) hw0_get hflag_l
                  have hp1_wa : (p_v + 1#64).toNat < st.core.wstk.length := by omega
                  have hcr_at : st.core.wstk[(p_v + 1#64).toNat]'hp1_wa = cr_v :=
                    Option.some_inj.mp
                      (by rw [← List.getElem?_eq_getElem hp1_wa, hp1_eq]; exact hcr_get)
                  have hp2_64 : p_v.toNat + 2 < 2 ^ 64 := by omega
                  have hp2_eq : (p_v + 2#64).toNat = p_v.toNat + 2 := by bv_omega
                  have hsplit_prev : FullSplitWatchesInv F_cur st.core
                      (lit ^^^ 1#32).toNat off_v.toNat q_v.toNat (p_v.toNat + 2) end_v.toNat :=
                    hsplit.advance_rem (by omega) (by omega)
                      (by simpa only [show end_v.toNat - (p_v.toNat + 2) =
                        end_v.toNat - p_v.toNat - 2 by omega] using hrem')
                  have hq_wa : q_v.toNat < st.core.wstk.length := by omega
                  have hq1_wa : q_v.toNat + 1 < st.core.wstk.length := by omega
                  have hq2_64 : q_v.toNat + 2 < 2 ^ 64 := by omega
                  have hq1_eq : (q_v + 1#64).toNat = q_v.toNat + 1 :=
                    bv64_add1_toNat (by omega)
                  have hq2_eq : (q_v + 2#64).toNat = q_v.toNat + 2 := by bv_omega
                  have hq1_c0 : (q_v + 1 : BitVec 64).toNat = q_v.toNat + 1 := hq1_eq
                  have hp1_c0 : st.core.wstk[(p_v + 1 : BitVec 64).toNat]'hp1_wa = cr_v :=
                    hcr_at
                  have hq2_c0 : (q_v + 2 : BitVec 64) = q_v + 2#64 := rfl
                  have hp2_sum : p_v + 1 + 1 = p_v + 2#64 := by bv_omega
                  have hsw_wl := hsplit_prev.write_large (w0 := w0_v) (cref := cr_v) hnot_lt'
                    hqp_le hq_wa hq1_wa hflag_l hcr_lt hcr_ref
                  let st_wl : Full.FullState := { st with core := { st.core with
                    wstk := (st.core.wstk.set q_v.toNat w0_v).set (q_v.toNat + 1) cr_v } }
                  have hlen_wl : st_wl.LengthsOk c :=
                    ⟨{ hcl with wstk_len_arr := by simp [st_wl, hwa_st] }, hlen.scratch_ok⟩
                  have hw_wl := fullWitnessInv_nw_upd_watches (s := st) (s' := st_wl) hw_nw
                    hlen_wl.core_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                  have hsw_wl' : FullSplitWatchesInv F_cur st_wl.core
                      (lit ^^^ 1#32).toNat off_v.toNat (q_v + 2#64).toNat
                      (p_v + 2#64).toNat end_v.toNat := by
                    simpa only [st_wl, hq2_eq, hp2_eq] using hsw_wl
                  pt_steps_nogrp
                  have hm_wl : (Full.FullMem c st_wl ⋆ R) m := by
                    dsimp only [st_wl]; rw [hq1_c0, hp1_c0] at hm; exact hm
                  rw [hp2_sum, hq2_c0]
                  exact hJloop (off_v, ticks_v, p_v + 2#64, q_v + 2#64, end_v, ()) m
                    (by dsimp only; rw [hp2_eq]; omega)
                    ⟨st_wl, hlen_wl, hw_wl, hmrk,
                      fullArenaVarsNodup_of_arena_eq hnd rfl rfl,
                      ⟨fullLastLearnedWf_of_refs_eq hext.1 rfl rfl, hext.2⟩,
                      hdm, hcl1, hcv, hfu, hlm, hws1,
                      fullTrailRsnsExt_trans htr (fullTrailRsnsExt_congr rfl rfl rfl rfl),
                      fullHbrBufOkW_congr hhbr rfl rfl, hsw_wl', hnf, hoom, hm_wl⟩
                · exfalso
                  have hflag_l : (w0_v &&& 0x80000000#32) = 0#32 := by assumption
                  obtain ⟨hrem2, _, _, _, _, _⟩ :=
                    Full.watchSlice_inv_large hsplit.rem_slice (by omega) hw0_get hflag_l
                  have hc' : end_v.toNat ≤ (p_v.toNat + 1) % 2 ^ 64 := Nat.not_lt.mp hc
                  rw [Nat.mod_eq_of_lt hp1_64] at hc'
                  omega
                · pt_steps_nogrp
                  exact hJ2 () ml ⟨rfl, fun hlt => by pt_clear_big; exact hc⟩
              · pt_steps_nogrp
                exact hJ2 () ml ⟨rfl, fun hlt => by
                  pt_clear_big
                  rw [Nat.mod_eq_of_lt hcv64, Nat.mod_eq_of_lt h2cv64] at hc
                  rw [hcv] at hlt
                  exact absurd hlt hc⟩
          · have hp_eq : p_v = end_v := BitVec.eq_of_toNat_eq (by pt_bound)
            exact hJtail (off_v, ticks_v, p_v, q_v, end_v, false, ()) ml
              ⟨st, hlen, hw_nw, hmrk, hnd, hext, hdm, hcl1, hcv, hfu, hlm, hws1, htr, hhbr,
                hsplit, (fun hf => by cases hf), fun _ => ⟨hoom, hp_eq⟩, hml⟩

/-! ## 3. Closed `ModuleOk` & Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`) -/

/-- Canonical `FullSpec3` specification table for `m5ProbePropModule`. -/
def m5ProbePropSpecTable : List SpecEntry :=
  [ ⟨"full_probe_prop_lit_m5", [i64, i32], [.bool], Full.fullProbePropLitSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  , ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩
  , ⟨"full_find_repl", [i64, i64], [i64], Full.fullFindReplSpec, true⟩
  , ⟨"full_hbr_dom", [i64, i32, i32], [i32], Full.fullHbrDomSpec, true⟩
  ]

/-- Specification environment induced by `m5ProbePropSpecTable`. -/
def m5ProbePropEnv : Env := Env.ofTable m5ProbePropSpecTable

theorem m5ProbePropSpecTable_noExit : ∀ e ∈ m5ProbePropSpecTable, e.noExit = true := by
  intro e he
  simp only [m5ProbePropSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem m5ProbeProp_noExit :
    ∀ f as bs xs m Q X X',
      m5ProbePropEnv f as bs xs m Q X → m5ProbePropEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m5ProbePropSpecTable_noExit

private theorem m5ProbePropSpecTable_nodup :
    (m5ProbePropSpecTable.map SpecEntry.name).Nodup := by
  show (["full_probe_prop_lit_m5", "full_watch_push", "full_assign_lvl", "full_find_repl",
    "full_hbr_dom"] : List String).Nodup
  decide

private theorem m5ProbePropEnv_row_at (i : Nat) (e : SpecEntry)
    (hi : m5ProbePropSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → m5ProbePropEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) m5ProbePropSpecTable_nodup (hno xs m Q X h)

/-- Row-by-row `TableImpl` for `m5ProbeProp_fns` against `m5ProbePropSpecTable`. -/
theorem m5ProbeProp_tableImpl :
    TableImpl m5ProbePropEnv m5ProbeProp_fns m5ProbePropSpecTable := by
  let hPush := m5ProbePropEnv_row_at 1
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  let hAsgn := m5ProbePropEnv_row_at 2
    ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩
  let hFind := m5ProbePropEnv_row_at 3
    ⟨"full_find_repl", [i64, i64], [i64], Full.fullFindReplSpec, true⟩
  let hDom := m5ProbePropEnv_row_at 4
    ⟨"full_hbr_dom", [i64, i32, i32], [i32], Full.fullHbrDomSpec, true⟩
  exact ⟨.of (full_probe_prop_lit_m5_wp m5ProbePropEnv hFind hPush hDom hAsgn), trivial⟩

/-- Closed `ModuleOk` for standalone `m5ProbePropModule` under `m5ProbePropEnv`. -/
theorem m5ProbeProp_moduleOk : ModuleOk m5ProbePropEnv m5ProbePropModule :=
  Env.ofTable_moduleOk m5ProbeProp_acyclic
    ⟨full_probe_prop_lit_m5_wf, trivial⟩
    m5ProbeProp_tableImpl

/-- Concrete `Mem 64` probing state (`cur_level = 1`, `probing = 1`, literal `0` decision on trail,
binary watch `(1, 1)` = `(¬x0 ∨ ¬x0)` at `wstk[1]`). -/
def nvProbePropState : Full.FullState where
  core :=
    { FastCore.nvFastPropState.core with
      cur_level := 1
      probing := 1#64
      lvl := [1#32]
      rsns := [0xFFFFFFFF#32]
      frame_trail := [0#32, 0#32]
      frame_dec := [0#32, 0#32] }
  scratch := FastCore.nvFastPropState.scratch

def nvProbeBlockHdr : List UInt8 :=
  bytes64 [1#64, 2#64, 0#64, 0#64] ++
  bytes64 (Full.hdrTailWords FastCore.nvFastPropCfg nvProbePropState)

def nvProbeBlockU32A : List UInt8 :=
  (bytesOf (t := i32) nvProbePropState.core.flags ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvProbePropState.core.lvl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvProbePropState.core.rsns ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvProbePropState.core.trl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvProbePropState.core.trail_pos ++ List.replicate 4 0)

def nvProbePropBytes : List UInt8 :=
  nvProbeBlockHdr ++ FastCore.nvFastBlockBytes ++ nvProbeBlockU32A ++ FastCore.nvFastBlockU32B ++
  FastCore.nvFastBlockU32C ++ FastCore.nvFastBlockWvec ++ FastCore.nvFastBlockTail

/-- Concrete `Mem 64` heap mapped at `FastCore.nvFastPropCfg.hdr` (`0x1000`). -/
def nvProbePropMem : Mem 64 := nvProbePropBytes.At FastCore.nvFastPropCfg.hdr

theorem nvProbePropMem_ok :
    Full.FullMem FastCore.nvFastPropCfg nvProbePropState nvProbePropMem := by
  let c := FastCore.nvFastPropCfg; let s := nvProbePropState
  have hvb : valsBytes c.max_vars - 2 * c.max_vars = 6 := by decide
  have hmb : markBytes c.max_vars - c.max_vars = 7 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 0 := by decide
  have hmv1 : BitVec.ofNat 64 c.max_vars = 1#64 := rfl
  have hmv2 : BitVec.ofNat 64 (2 * c.max_vars) = 2#64 := rfl
  have hmv4 : BitVec.ofNat 64 (4 * c.max_vars) = 4#64 := rfl
  have hmv8 : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 8#64 := rfl
  have hHdr : nvProbeBlockHdr.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s))
        (nvProbeBlockHdr.At c.hdr) :=
    Full.nv_join_pair
      (Full.nv_arr64_p (a := c.hdr) (xs := [1#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
      (Full.nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide))
      (by decide) (by decide)
  have hBytes : FastCore.nvFastBlockBytes.length = 64 ∧
      (Full.FullCoreByteArrs c s.core ⋆ Full.FullScrByteArrs c s.scratch ⋆ c.padBytes)
        (FastCore.nvFastBlockBytes.At c.pVals) := by
    have h1 := Full.nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 2 6 rfl (by decide)
    have h2 := Full.nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals)
      2 6 rfl (by decide)
    have h3 := Full.nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark)
      2 6 rfl (by decide)
    have h4 := Full.nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 1 7 rfl (by decide)
    have h5 := Full.nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases)
      1 7 rfl (by decide)
    have h6 := Full.nv_arr_pad_p (t := i8) (a := c.pPhasesTarget)
      (xs := s.scratch.phases_target) 1 7 rfl (by decide)
    have h7 := Full.nv_arr_pad_p (t := i8) (a := c.pPhasesBest)
      (xs := s.scratch.phases_best) 1 7 rfl (by decide)
    have h8 := Full.nv_arr_pad_p (t := i8) (a := c.pWalkBest)
      (xs := s.scratch.walk_best) 1 7 rfl (by decide)
    let pB1 : Mem 64 → Prop :=
      region (c.pVals + 2#64) 6 ⋆ region (c.pWalkVals + 2#64) 6 ⋆
      region (c.pLitMark + 2#64) 6 ⋆ region (c.pMark + 1#64) 7
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_sep_reorg (Full.nv_join_pair h123 h4 (by decide) (by decide))
      (Q := (Full.FullCoreByteArrs c s.core ⋆ array (t := i8) c.pWalkVals s.scratch.walk_vals) ⋆
        pB1)
      fun _ hm => Full.nv_zip4 hm
    have h12345 := Full.nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := Full.nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := Full.nv_join_pair h123456 h7 (by decide) (by decide)
    have hall := Full.nv_join_pair h1234567 h8 (by decide) (by decide)
    exact Full.nv_sep_reorg hall fun _ hm => by
      have hfin := Full.nv_zip4_tail hm
      unfold Full.FullScrByteArrs Full.FullCfg.padBytes
      rw [hvb, hmb, hmv2, hmv1]
      simpa only [pB1, sep_assoc] using hfin
  have hU32A : nvProbeBlockU32A.length = 40 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        (nvProbeBlockU32A.At c.pFlags) := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 4 4 rfl
      (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 4 4 rfl (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 4 4 rfl
      (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 4 4 rfl (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 4 4 rfl
      (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold Full.FullCfg.padU32A; rw [hu4, hmv4]; exact sep_ac hm
  have hU32B : FastCore.nvFastBlockU32B.length = 40 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
        (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
         array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        (FastCore.nvFastBlockU32B.At c.pTmp) := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 4 4 rfl (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 4 4 rfl
      (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 4 4 rfl
      (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 4 4 rfl
      (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk)
      4 4 rfl (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold Full.FullCfg.padU32B; rw [hu4, hmv4]; exact sep_ac hm
  have hU32C : FastCore.nvFastBlockU32C.length = 40 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        (FastCore.nvFastBlockU32C.At c.pQPrev) := by
    have h1 := Full.nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 4 4 rfl
      (by decide)
    have h2 := Full.nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 4 4 rfl
      (by decide)
    have h3 := Full.nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 4 4 rfl
      (by decide)
    have h4 := Full.nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail)
      8 0 rfl (by decide)
    have h5 := Full.nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec)
      8 0 rfl (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold Full.FullCfg.padU32C; rw [hu4, hu8, hmv4, hmv8]; exact sep_ac hm
  have hWvec : FastCore.nvFastBlockWvec.length = 80 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        Full.FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        (FastCore.nvFastBlockWvec.At c.pWvec) := by
    have h1 := Full.nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 16 rfl (by decide)
    have h2 := Full.nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 8 rfl (by decide)
    have h3 := Full.nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 8 rfl (by decide)
    have h4 := Full.nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 8 rfl
      (by decide)
    have h5 := Full.nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 8 rfl
      (by decide)
    have h6 := Full.nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 8 rfl
      (by decide)
    have h7 := Full.nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach)
      8 rfl (by decide)
    have h8 := Full.nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 8 rfl (by decide)
    have h9 := Full.nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 8 rfl (by decide)
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := Full.nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := Full.nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := Full.nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := Full.nv_join_pair h1234567 h8 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold Full.FullScrWksArrs; exact sep_ac hm
  have hTail : FastCore.nvFastBlockTail.length = 344 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        Full.FullCoreDynArrs c s.core ⋆ Full.FullScrDynArrs c s.scratch ⋆
        region c.pSlack c.slack)
        (FastCore.nvFastBlockTail.At c.pMinStk) := by
    have h1 := Full.nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 16 rfl (by decide)
    have h2 := Full.nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256 rfl
      (by decide)
    have h3 := Full.nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned)
      64 rfl (by decide)
    have h4 := Full.nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 0 rfl (by decide)
    have h5 := Full.nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 8 rfl (by decide)
    have h6 := Full.nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl
      (by decide)
    have h7 := Full.nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl
      (by decide)
    have h8 := Full.nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl
      (by decide)
    have h9 := Full.nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 0 rfl
      (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 0).At c.pSlack) :=
      ⟨rfl, ⟨List.replicate 0 0, by decide, rfl⟩⟩
    have h12 := Full.nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := Full.nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := Full.nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := Full.nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := Full.nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := Full.nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := Full.nv_join_pair h1234567 h8 (by decide) (by decide)
    have h123456789 := Full.nv_join_pair h12345678 h9 (by decide) (by decide)
    exact Full.nv_sep_reorg (Full.nv_join_pair h123456789 h10 (by decide) (by decide))
      fun _ hm => by unfold Full.FullCoreDynArrs Full.FullScrDynArrs; exact sep_ac hm
  have h01 := Full.nv_join_pair hHdr hBytes (by decide) (by decide)
  have h02 := Full.nv_join_pair h01 hU32A (by decide) (by decide)
  have h03 := Full.nv_join_pair h02 hU32B (by decide) (by decide)
  have h04 := Full.nv_join_pair h03 hU32C (by decide) (by decide)
  have h05 := Full.nv_join_pair h04 hWvec (by decide) (by decide)
  exact (Full.nv_sep_reorg (Full.nv_join_pair h05 hTail (by decide) (by decide)) fun _ hm => by
    unfold Full.FullMem Full.FullCoreArrays Full.FullCoreU32A Full.FullCoreU32B
      Full.FullScratchArrays Full.FullScrU32A Full.FullScrMetaArrs Full.FullCfg.pad
    exact sep_ac hm).2

theorem nvProbeProp_lengths : nvProbePropState.LengthsOk FastCore.nvFastPropCfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Nat.le_refl _, Nat.le_refl _, by decide, by decide, Nat.le_refl _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem nvProbeProp_witness :
    Full.FullWitnessInv FastCore.nvFastPropCfg
      Full.nvOneLitF0 [[0], [1]] nvProbePropState.core := by
  have hrefs : Full.fullArenaClauseRefsCore nvProbePropState.core = [] := rfl
  have hrefs_fast : Full.fullArenaClauseRefsCore FastCore.nvFastPropState.core = [] := rfl
  have hte : nvProbePropState.core.trail_end = 1 := rfl
  have hcl : nvProbePropState.core.cur_level = 1 := rfl
  have hwat' : Full.ModeWatchesInv [[0], [1]] nvProbePropState.core :=
    Full.ModeWatchesInv.with_wstk FastCore.nvFastProp_witness.watches
      rfl rfl rfl rfl rfl (fun r hr => by rw [hrefs_fast] at hr; cases hr)
  have haren' : Full.FullArenaClausesInv FastCore.nvFastPropCfg [[0], [1]] nvProbePropState.core :=
    ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr,
      fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
      fun r hr => by simp [hrefs] at hr⟩
  refine
    { ext_sound := FastCore.nvFastProp_witness.ext_sound
      inconsistent_sound := fun h => absurd rfl h
      arena := haren'
      watches := hwat'
      cur_level_le := Nat.le_refl _
      trail_lits_lt := fun i hi => by
        rw [hte] at hi; obtain rfl : i = 0 := by omega
        decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hte] at hi hj; omega
      vals_domain := fun l hl => FastCore.nvFastProp_witness.vals_domain l hl
      vals_true_iff := fun l hl => FastCore.nvFastProp_witness.vals_true_iff l hl
      vals_false_iff := fun l hl => FastCore.nvFastProp_witness.vals_false_iff l hl
      lvl_le := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
      dec_earliest := fun i j hi hj _ _ => by rw [hte] at hi hj; omega
      levels_inhabited := fun L h1 h2 => by
        rw [hcl] at h2; obtain rfl : L = 1 := (by omega)
        exact ⟨0, by rw [hte]; exact Nat.zero_lt_one, rfl⟩
      level0_sound := fun i hi hl0 => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases hl0
      trail_pos_inv := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      level0_rsn_none := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      frame_trail_lt := fun L hL => by
        rw [hcl] at hL; rcases (by omega : L = 0 ∨ L = 1) with rfl | rfl <;> decide
      frame_trail_mono := fun L1 L2 h12 h2 => by
        rw [hcl] at h2
        rcases (by omega : L1 = 0 ∨ L1 = 1) with rfl | rfl <;>
          rcases (by omega : L2 = 0 ∨ L2 = 1) with rfl | rfl <;> decide
      frame_trail_before_lt := fun L h1 h2 i hi => by
        rw [hcl] at h2; obtain rfl : L = 1 := (by omega)
        cases hi
      frame_dec_lt := fun L h1 h2 => by rw [hcl] at h2; obtain rfl : L = 1 := (by omega); decide
      reason_inv := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne }

private theorem nvProbePropF0_unsat : Full.nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [Full.nvOneLitF0, cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [Full.nvOneLitF0, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1 <;> first
    | omega
    | (rcases (by omega : v0 = 0) with rfl; rcases (by omega : v1 = 0) with rfl;
       exact Bool.noConfusion (he0.symm.trans he1))

/-- Concrete `Mem 64` binary-watch UNSAT non-vacuity for `full_probe_prop_lit_m5_body` under
`m5ProbePropEnv` (`XPost := False`): proves non-vacuity and derives `nvOneLitF0.Unsat`. -/
theorem nv_m5_probe_prop_sound :
    Func.wp m5ProbePropEnv full_probe_prop_lit_m5_body (FastCore.nvFastPropCfg.hdr, 0#32, ())
      nvProbePropMem
      (fun (ok, ()) m' =>
        (ok = true ∨ ok = false) ∧ Full.nvOneLitF0.Unsat ∧
        ∃ s', (Full.FullMem FastCore.nvFastPropCfg s' ⋆ emp) m')
      (fun _ _ _ _ => False) := by
  let hPush := m5ProbePropEnv_row_at 1
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  let hAsgn := m5ProbePropEnv_row_at 2
    ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩
  let hFind := m5ProbePropEnv_row_at 3
    ⟨"full_find_repl", [i64, i64], [i64], Full.fullFindReplSpec, true⟩
  let hDom := m5ProbePropEnv_row_at 4
    ⟨"full_hbr_dom", [i64, i32, i32], [i32], Full.fullHbrDomSpec, true⟩
  apply full_probe_prop_lit_m5_wp m5ProbePropEnv hFind hPush hDom hAsgn
  have hmv1 : FastCore.nvFastPropCfg.max_vars = 1 := rfl
  refine ⟨FastCore.nvFastPropCfg, Full.nvOneLitF0, [[0], [1]], nvProbePropState, emp,
    rfl, nvProbeProp_lengths, nvProbeProp_witness, (fun w hw => by
      rw [hmv1] at hw; obtain rfl : w = 0 := (by omega); rfl),
    (fun _ h _ => by cases h),
    ⟨(fun i _ => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inl rfl),
      Nat.zero_le _⟩, rfl, rfl, rfl,
    ⟨Nat.zero_le _, (fun _ hk => by cases hk)⟩, (by rw [sep_emp]; exact nvProbePropMem_ok), ?_⟩
  intro ok s' m' _hl' _hw' _hmk' _hnd' _hext' _hdm' _hcl1' _hcv' _hfu' _hlm' _hws1'
    _htr' _hhbr' _hok_f _hok_t hm'
  exact ⟨by cases ok <;> simp, nvProbePropF0_unsat, s', hm'⟩

end LeanQbe.T.Examples.Kissat.FullM5ProbeProp
