/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5VivifyBackboneProof0a
import LeanQbe.T.Examples.Kissat.FullVivifyLemmas2
import LeanQbe.T.Examples.Kissat.FullVivifyLemmas3
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat Fidelity Step 13 Shard S5-B — Vivify Commit (`Proof0b`)

Proves UNSAT-sound `Func.wp` (`XPost := False`, `0` SAT model proofs) for
`FullFidelityStep13S5VivifyBackbone.full_viv_commit_m6_body` (`fullVivCommitM6Spec`, adding
`if ((nhdr & PH_RED) == 0u)` factorization flag updates `FL_SUBSUME | FL_ELIM_C | FL_FACT_*`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullVivTopTactics
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open scoped FullArenaTactics FullVivTopTactics

/-! ## 1. Local Framing, Pure Pack & `DecrCount` / `GlueShrk` Helpers -/

section Helpers

open FullVivifyHelpers

private theorem c0_load_ws1_z_s13 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pWorkStk1 + 0#64) = some s.scratch.work_stk1[0] :=
  FullArenaTactics.load_full_work_stk1 hi hm

private theorem c0_load_ws1_b_s13 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pWorkStk1 = some s.scratch.work_stk1[0] := by
  simpa using FullArenaTactics.load_full_work_stk1 hi hm

private theorem c0_load_ws2_z_s13 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pWorkStk2 + 0#64) = some s.scratch.work_stk2[0] :=
  FullArenaTactics.load_full_work_stk2 hi hm

private theorem c0_load_ws2_b_s13 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pWorkStk2 = some s.scratch.work_stk2[0] := by
  simpa using FullArenaTactics.load_full_work_stk2 hi hm

private theorem c0_load_ws2_4_s13 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 1 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pWorkStk2 + 4#64) = some s.scratch.work_stk2[1] :=
  FullArenaTactics.load_full_work_stk2 hi hm

private theorem s13_sparseW_with_counts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (ni' nr' : BitVec 64) :
    FullSparseInvW c F0 F_cur
      { s with core := { s.core with num_irred := ni', num_redundant := nr' } } :=
  ⟨⟨{ hsp.1.core_ok with }, hsp.1.scratch_ok⟩,
   { hsp.2.1 with
     arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
     watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem s13_sparseW_with_inc {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (hu : (cnfOfClauses F_cur).Unsat) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with inconsistent := 1#64 } } :=
  ⟨⟨{ hsp.1.core_ok with }, hsp.1.scratch_ok⟩,
   { hsp.2.1 with
     inconsistent_sound := fun _ => hu
     arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
     watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem s13_sparseW_with_vivcnt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (vc' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with viv_cnt := vc' } } :=
  ⟨⟨hsp.1.core_ok, { hsp.1.scratch_ok with }⟩, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1,
   hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem s13_sparseW_with_ws2 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) {ws2' : List (BitVec 32)}
    (hlen : ws2'.length = 2 * c.max_vars) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk2 := ws2' } } :=
  ⟨⟨hsp.1.core_ok, { hsp.1.scratch_ok with work_stk2_len := hlen }⟩, hsp.2.1, hsp.2.2.1,
   hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem s13_sparseW_with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (oom' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with oom := oom' } } :=
  fv_with_oomW hsp oom'

private theorem s13_watchLayout {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) : WatchStackLayout s.core := by
  have hmw := hsp.2.1.watches; unfold ModeWatchesInv at hmw
  simp only [hsp.2.2.2.2.2, ↓reduceIte] at hmw; exact hmw.layout

private theorem s13_unwatch_sparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {wvec' wstk' : List (BitVec 32)} {wu' : BitVec 64}
    (hlen' : ({ s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } } :
      FullState).LengthsOk c)
    (hmode' : ∀ Fc, ModeWatchesInv Fc s.core →
      ModeWatchesInv Fc { s.core with wvec := wvec', wstk := wstk', wusable := wu' }) :
    FullSparseInvW c F0 F_cur
      { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } } :=
  ⟨hlen',
   { hsp.2.1 with
     arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
     watches := hmode' F_cur hsp.2.1.watches },
   hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem s13_ws2_perm_props {F_cur : List (List Nat)} {ws2 ws2' : List (BitVec 32)}
    {n cv : Nat} (hws2 : n ≤ ws2.length) (hws2' : n ≤ ws2'.length)
    (hperm : (ws2'.take n).Perm (ws2.take n))
    (hlt : ∀ i < n, (ws2[i]?.getD 0#32).toNat < 2 * cv)
    (hnd : ((ws2.take n).map fun x => x.toNat / 2).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause ((ws2.take n).map BitVec.toNat))) :
    (∀ i < n, (ws2'[i]?.getD 0#32).toNat < 2 * cv) ∧
    (((ws2'.take n).map BitVec.toNat).map (· / 2)).Nodup ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause ((ws2'.take n).map BitVec.toNat)) := by
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · have hm : ws2'[i]'(by omega) ∈ ws2.take n := hperm.mem_iff.mp (by
      rw [List.mem_iff_getElem]
      exact ⟨i, by rw [List.length_take]; omega, by simp [List.getElem_take]⟩)
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hm
    have hj_n : j < n := by rw [List.length_take] at hj; omega
    rw [List.getElem_take] at heq
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← heq]
    have := hlt j hj_n
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
  · have hp2 : (((ws2'.take n).map BitVec.toNat).map (· / 2)).Perm
        (((ws2.take n).map BitVec.toNat).map (· / 2)) :=
      (hperm.map BitVec.toNat).map (· / 2)
    exact hp2.nodup_iff.mpr (by simpa only [List.map_map, Function.comp_def] using hnd)
  · rw [CNF.entails_clause_def] at hent ⊢
    intro α hα
    obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α _).mp (hent α hα)
    exact (clause_sat_cnfClause_iff α _).mpr ⟨l, (hperm.map BitVec.toNat).mem_iff.mpr hl, hsat⟩

private theorem s13_commit_shrk_hnonact {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s3 : FullState} (hsp3 : FullSparseInvW c F0 F_cur s3)
    {cref olen : Nat} (href3 : cref ∈ fullArenaClauseRefs s3)
    (hnonact : NonActiveReason s3.core cref) (hng3 : fullArenaClauseGarb s3 cref = false)
    (holen3 : 3 ≤ olen) (holen_lt : olen < fullArenaClauseSize s3 cref)
    (holen_le : olen ≤ s3.scratch.work_stk2.length)
    (hout_lt : ∀ j < olen, (s3.scratch.work_stk2[j]?.getD 0#32).toNat < 2 * s3.core.cur_vars)
    (hout_nd : (((s3.scratch.work_stk2.take olen).map BitVec.toNat).map (· / 2)).Nodup)
    (hout_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s3.scratch.work_stk2.take olen).map BitVec.toNat)))
    {nhdr2 : BitVec 32} {ar_p : List (BitVec 32)}
    (harp_len : ar_p.length = c.arena_cap)
    (hng2 : (nhdr2 &&& 0x00080000#32) = 0#32) (hsh2 : (nhdr2 &&& 0x00800000#32) ≠ 0#32)
    (hout_p : ∀ k, (k < cref ∨ cref + 3 + fullArenaClauseSize s3 cref ≤ k) →
      ar_p[k]? = s3.core.arena[k]?)
    (hsz_p : (ar_p[cref + 2]?.getD 0#32).toNat = olen)
    (hpay_p : ∀ j < olen, ar_p[cref + 3 + j]? = s3.scratch.work_stk2[j]?)
    (hpad_p : M6ShrkPad ar_p s3.core.arena cref (fullArenaClauseSize s3 cref) olen) :
    let ar_f := ar_p.set cref nhdr2
    let s_f : FullState := { s3 with core := { s3.core with arena := ar_f } }
    FullSparseInvW c F0 F_cur s_f ∧ fullArenaClauseRefs s_f = fullArenaClauseRefs s3 := by
  intro ar_f s_f
  have hw3 := hsp3.2.1; have hcl := hsp3.1.core_ok
  have hwf := hw3.arena.refs_wf cref href3; have halen_le := hcl.arena_len_le
  have hsz_def : fullArenaClauseSize s3 cref = fullArenaClauseSizeCore s3.core cref := rfl
  have harf_len : ar_f.length = c.arena_cap := by simp [ar_f, harp_len]
  have hsz_f : (ar_f[cref + 2]?.getD 0#32).toNat = olen := by
    dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hsz_p
  have hpay_f : ∀ j < olen, ar_f[cref + 3 + j]? = s3.scratch.work_stk2[j]? := fun j hj => by
    dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hpay_p j hj
  have hlits_eq : fullArenaClauseLitsCore { s3.core with arena := ar_f } cref =
      (s3.scratch.work_stk2.take olen).map BitVec.toNat := by
    have hbd' : cref + 3 + fullArenaClauseSizeCore { s3.core with arena := ar_f } cref ≤
        ar_f.length := by change cref + 3 + (ar_f[cref + 2]?.getD 0#32).toNat ≤ ar_f.length; omega
    have hlen_l : (fullArenaClauseLitsCore { s3.core with arena := ar_f } cref).length = olen := by
      unfold fullArenaClauseLitsCore fullArenaClauseSizeCore
      simp only [List.length_map, List.length_take, List.length_drop, hsz_f]; omega
    refine List.ext_getElem
      (by rw [hlen_l, List.length_map, List.length_take]; omega)
      fun t ht1 _ => ?_
    rw [hlen_l] at ht1
    have hgt : (fullArenaClauseLitsCore { s3.core with arena := ar_f } cref)[t]'(by
        rw [hlen_l]; exact ht1) =
        (ar_f[cref + 3 + t]'(by omega)).toNat := by
      unfold fullArenaClauseLitsCore; simp [List.getElem_map, List.getElem_take, List.getElem_drop]
    rw [hgt, List.getElem_map, List.getElem_take]
    have hg := hpay_f t ht1
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hg
    exact congrArg BitVec.toNat (Option.some.inj hg)
  have hpad_f : M6ShrkPad ar_f s3.core.arena cref (fullArenaClauseSize s3 cref) olen := by
    unfold M6ShrkPad at hpad_p ⊢; split
    · rename_i h0; rw [ite_eq_left h0] at hpad_p
      exact ⟨fun k hk1 hk2 => by
        dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hpad_p.1 k hk1 hk2,
        by dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hpad_p.2⟩
    · rename_i hne; rw [ite_eq_right hne] at hpad_p
      exact fun k hk1 hk2 => by
        dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hpad_p k hk1 hk2
  obtain ⟨hsp_f, hrefs_f, _, _⟩ := fullSparseInvW_of_inPlaceShrink_hnonact hsp3 href3 hnonact hng3
    holen3 holen_lt harf_len
    (fun k hk => by dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hout_p k hk)
    (by dsimp only [ar_f]; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hng2)
    (by dsimp only [ar_f]; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hsh2)
    hsz_f hpad_f (fun j hj => by rw [hpay_f j hj]; exact hout_lt j hj)
    (by rw [hlits_eq]; exact hout_nd) (by rw [hlits_eq]; exact hout_ent)
  exact ⟨hsp_f, hrefs_f⟩

private theorem s13_watchPush_pre {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {blk cref : BitVec 32} (hsp : FullSparseInvW c F0 F_cur s)
    (hcref : cref.toNat < 0x80000000) :
    s.LengthsOk c ∧ WatchStackLayout s.core ∧
    ((2#32 : BitVec 32).toNat = 1 → (blk &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32) ∧
    ((2#32 : BitVec 32).toNat = 2 →
      (blk &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 ∧ cref ≠ 0xFFFFFFFF#32) :=
  ⟨hsp.1, s13_watchLayout hsp, fun h => absurd h (by decide),
   fun _ => ⟨(FullVivifyTactics.bv32_mask_lo31_props _).2, bv32_ne_sentinel_of_lt hcref⟩⟩

private abbrev s13DecrCountExpr (h : Val i64) (hdr : Val i32) (k : Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) => k) Blocks.nil) fun Js =>
  fvOp (OpCode.and i32) (Arg.var hdr, Arg.imm 4194304, ()) fun p =>
  fvOp (OpCode.cmp .ne i32 .bool rfl) (Arg.var p.fst, Arg.imm 0, ()) fun p =>
  Expr.jnz (Arg.var p.fst)
    (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ => Expr.jump Js.fst ()) Blocks.nil)
       fun Js1 =>
     fvOp (OpCode.add i64) (Arg.var h, Arg.imm 496, ()) fun p =>
     Expr.load i64 (Arg.var p.fst) fun ld =>
     fvOp (OpCode.cmp .ugt i64 .bool rfl) (Arg.var ld, Arg.imm 0, ()) fun p =>
     Expr.jnz (Arg.var p.fst)
       (fvOp (OpCode.add i64) (Arg.var h, Arg.imm 496, ()) fun p =>
        Expr.load i64 (Arg.var p.fst) fun ld =>
        fvOp (OpCode.sub i64) (Arg.var ld, Arg.imm 1, ()) fun p1 =>
        fvOp (OpCode.add i64) (Arg.var h, Arg.imm 496, ()) fun p =>
        Expr.store (Arg.var p1.fst) (Arg.var p.fst) (Expr.jump Js1.fst ()))
       (Expr.jump Js1.fst ()))
    (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ => Expr.jump Js.fst ()) Blocks.nil)
       fun Js2 =>
     fvOp (OpCode.add i64) (Arg.var h, Arg.imm 488, ()) fun p =>
     Expr.load i64 (Arg.var p.fst) fun ld =>
     fvOp (OpCode.cmp .ugt i64 .bool rfl) (Arg.var ld, Arg.imm 0, ()) fun p =>
     Expr.jnz (Arg.var p.fst)
       (fvOp (OpCode.add i64) (Arg.var h, Arg.imm 488, ()) fun p =>
        Expr.load i64 (Arg.var p.fst) fun ld =>
        fvOp (OpCode.sub i64) (Arg.var ld, Arg.imm 1, ()) fun p1 =>
        fvOp (OpCode.add i64) (Arg.var h, Arg.imm 488, ()) fun p =>
        Expr.store (Arg.var p1.fst) (Arg.var p.fst) (Expr.jump Js2.fst ()))
       (Expr.jump Js2.fst ()))

private theorem s13_decr_count_wp (Γ : Env) {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {hdr : Val i32} {k : Expr Val Cont [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (ni' nr' : BitVec 64) mg,
      (FullMem c { s with core := { s.core with num_irred := ni', num_redundant := nr' } } ⋆ R) mg →
      wp Γ Q X k mg) :
    wp Γ Q X (s13DecrCountExpr c.hdr hdr k) m := by
  dsimp only [s13DecrCountExpr, fvOp]
  refine wp_join_group (ts := [])
    (fun _ mg => ∃ ni' nr' : BitVec 64,
      (FullMem c { s with core := { s.core with num_irred := ni', num_redundant := nr' } } ⋆ R) mg)
    (fun _ _ mg ⟨ni', nr', hmg⟩ => hk ni' nr' mg hmg)
    (fun Jg hJg => by
      fvt_to_group
      · refine wp_join_group (ts := [])
          (fun _ mg => ∃ ni' nr' : BitVec 64,
            (FullMem c { s with core := { s.core with num_irred := ni', num_redundant := nr' } }
              ⋆ R) mg)
          (fun _ _ mg h => hJg () mg h)
          (fun J1 hJ1 => by
            fvt_steps
            · exact hJ1 () _ ⟨_, _, by assumption⟩
            · exact hJ1 () _ ⟨_, _, by assumption⟩)
      · refine wp_join_group (ts := [])
          (fun _ mg => ∃ ni' nr' : BitVec 64,
            (FullMem c { s with core := { s.core with num_irred := ni', num_redundant := nr' } }
              ⋆ R) mg)
          (fun _ _ mg h => hJg () mg h)
          (fun J2 hJ2 => by
            fvt_steps
            · exact hJ2 () _ ⟨_, _, by assumption⟩
            · exact hJ2 () _ ⟨_, _, by assumption⟩))

private abbrev s13TermPtr (pArena : Val i64) (cref old_sz : Val i32)
    (k : Val i64 → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  fvOp (OpCode.zext 32 64) (Arg.var cref, ()) fun p =>
  fvOp (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p =>
  fvOp (OpCode.zext 32 64) (Arg.var old_sz, ()) fun pz =>
  fvOp (OpCode.add i64) (Arg.var p.fst, Arg.var pz.fst, ()) fun p =>
  fvOp (OpCode.sub i64) (Arg.var p.fst, Arg.imm 1, ()) fun p =>
  fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
  fvOp (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p => k p.fst

private theorem s13_bv32_or_shrk_garb (x : BitVec 32) :
    ((x ||| 0x00800000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) := by
  rw [BitVec.and_or_distrib_right, show (0x00800000#32 &&& 0x00080000#32) = 0#32 by decide,
    BitVec.or_zero]

private theorem s13_bv32_or_shrk_ne0 (x : BitVec 32) :
    ((x ||| 0x00800000#32) &&& 0x00800000#32) ≠ 0#32 := fun h => by
  have := congrArg (BitVec.getLsbD · 23) h
  simp at this

private abbrev s13GlueShrkExpr (pArena : Val i64) (cref hdr old_sz nsz : Val i32)
    (k : Val i32 → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun (p_g : Tup Val [i32]) =>
    Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun (p_s : Tup Val [i32]) =>
      arBasePtr pArena cref fun p =>
      Expr.store (Arg.var p_s.fst) (Arg.var p) (k p_s.fst)) Blocks.nil) fun Js_s =>
    fvOp (OpCode.and i32) (Arg.var p_g.fst, Arg.imm 8388608, ()) fun p =>
    fvOp (OpCode.cmp .eq i32 .bool rfl) (Arg.var p.fst, Arg.imm 0, ()) fun p =>
    Expr.jnz (Arg.var p.fst)
      (s13TermPtr pArena cref old_sz fun pt =>
       Expr.store (Arg.imm (t := i32) 4294967295) (Arg.var pt)
         (fvOp (OpCode.or i32) (Arg.var p_g.fst, Arg.imm 8388608, ()) fun p =>
          Expr.jump Js_s.fst (Arg.var p.fst, ())))
      (Expr.jump Js_s.fst (Arg.var p_g.fst, ()))) Blocks.nil) fun Js_g =>
  fvOp (OpCode.and i32) (Arg.var hdr, Arg.imm 4194304, ()) fun p =>
  fvOp (OpCode.cmp .ne i32 .bool rfl) (Arg.var p.fst, Arg.imm 0, ()) fun p =>
  Expr.jnz (Arg.var p.fst)
    (fvOp (OpCode.and i32) (Arg.var hdr, Arg.imm 524287, ()) fun pg =>
     Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun (p : Tup Val [i32]) =>
       Expr.jump Js_g.fst (Arg.var p.fst, ())) Blocks.nil) fun Js_i =>
     fvOp (OpCode.cmp .uge i32 .bool rfl) (Arg.var pg.fst, Arg.var nsz, ()) fun p =>
     Expr.jnz (Arg.var p.fst)
       (fvOp (OpCode.not i32) (Arg.imm 524287, ()) fun pm =>
        fvOp (OpCode.and i32) (Arg.var hdr, Arg.var pm.fst, ()) fun pa =>
        fvOp (OpCode.sub i32) (Arg.var nsz, Arg.imm 1, ()) fun ps =>
        fvOp (OpCode.and i32) (Arg.var ps.fst, Arg.imm 524287, ()) fun pb =>
        fvOp (OpCode.or i32) (Arg.var pa.fst, Arg.var pb.fst, ()) fun pr =>
        Expr.jump Js_i.fst (Arg.var pr.fst, ()))
       (Expr.jump Js_i.fst (Arg.var hdr, ())))
    (Expr.jump Js_g.fst (Arg.var hdr, ()))

private theorem s13_glue_shrk_wp (Γ : Env) {c : FullCfg} {s3 : FullState} {R : Mem 64 → Prop}
    {cref hdr old_sz nsz : Val i32} {ar_sz : List (BitVec 32)}
    {k : Val i32 → Expr Val Cont [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hhdr_eq : fullArenaHdr s3 cref.toNat = hdr) (hhdr_ng : (hdr &&& 0x00080000#32) = 0#32)
    (hold_sz_3 : 3 ≤ old_sz.toNat) (hnsz3 : 3 ≤ nsz.toNat) (hnsz_lt : nsz.toNat < old_sz.toNat)
    (hcap : c.arena_cap < 2 * 2 ^ 28) (hbd : cref.toNat + 3 + old_sz.toNat ≤ c.arena_cap)
    (hasz_cap : ar_sz.length = c.arena_cap) (hcref0_eq : (cref.setWidth 64).toNat = cref.toNat)
    (hcref3_eq : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (hasz_out : ∀ p, (p < cref.toNat ∨ cref.toNat + 3 + old_sz.toNat ≤ p) →
      ar_sz[p]? = s3.core.arena[p]?)
    (hasz_sz : (ar_sz[cref.toNat + 2]?.getD 0#32).toNat = nsz.toNat)
    (hasz_pad : ∀ p, cref.toNat + 3 + nsz.toNat ≤ p → p < cref.toNat + 3 + old_sz.toNat →
      ar_sz[p]? = s3.core.arena[p]?)
    (hm : (FullMem c { s3 with core := { s3.core with arena := ar_sz } } ⋆ R) m)
    (hk : ∀ (nhdr2 : Val i32) (ar_p : List (BitVec 32)) mf,
      ar_p.length = c.arena_cap →
      (nhdr2 &&& 0x00080000#32) = 0#32 → (nhdr2 &&& 0x00800000#32) ≠ 0#32 →
      (∀ p, (p < cref.toNat ∨ cref.toNat + 3 + old_sz.toNat ≤ p) → ar_p[p]? = s3.core.arena[p]?) →
      (ar_p[cref.toNat + 2]?.getD 0#32).toNat = nsz.toNat →
      (∀ j < nsz.toNat, ar_p[cref.toNat + 3 + j]? = ar_sz[cref.toNat + 3 + j]?) →
      M6ShrkPad ar_p s3.core.arena cref.toNat old_sz.toNat nsz.toNat →
      ShrkPad ar_p s3.core.arena cref.toNat old_sz.toNat nsz.toNat →
      (FullMem c { s3 with core := { s3.core with arena := ar_p.set cref.toNat nhdr2 } } ⋆ R) mf →
      wp Γ Q X (k nhdr2) mf) :
    wp Γ Q X (s13GlueShrkExpr c.pArena cref hdr old_sz nsz k) m := by
  have hterm_eq : (cref.setWidth 64 + 3#64 + old_sz.setWidth 64 - 1#64).toNat =
      cref.toNat + 3 + old_sz.toNat - 1 := by
    have hos64 : (old_sz.setWidth 64).toNat = old_sz.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
        (Nat.lt_trans old_sz.isLt (by decide : 2 ^ 32 < 2 ^ 64))]
    have hadd : (cref.setWidth 64 + 3#64 + old_sz.setWidth 64).toNat =
        cref.toNat + 3 + old_sz.toNat := by
      rw [BitVec.toNat_add, hcref3_eq, hos64, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hadd]; show 1 ≤ _; omega), hadd]; rfl
  have hterm_lt : (cref.setWidth 64 + 3#64 + old_sz.setWidth 64 - 1#64).toNat < ar_sz.length := by
    rw [hterm_eq, hasz_cap]; omega
  dsimp only [s13GlueShrkExpr, s13TermPtr, arBasePtr, fvOp]
  refine wp_join_group (ts := [i32])
    (fun (nhdr, ()) m_g => m = m_g ∧ (nhdr &&& 0x00080000#32) = 0#32 ∧
      (nhdr &&& 0x00800000#32) = (hdr &&& 0x00800000#32))
    (fun _ ⟨nhdr, ⟨⟩⟩ m_g ⟨hm_g, hng_nh, hsh_nh⟩ => by
      subst hm_g
      refine wp_join_group (ts := [i32])
        (fun (nhdr2, ()) m_p => ∃ ar_p : List (BitVec 32), ar_p.length = c.arena_cap ∧
          (nhdr2 &&& 0x00080000#32) = 0#32 ∧ (nhdr2 &&& 0x00800000#32) ≠ 0#32 ∧
          (∀ p, (p < cref.toNat ∨ cref.toNat + 3 + old_sz.toNat ≤ p) →
            ar_p[p]? = s3.core.arena[p]?) ∧
          (ar_p[cref.toNat + 2]?.getD 0#32).toNat = nsz.toNat ∧
          (∀ j < nsz.toNat, ar_p[cref.toNat + 3 + j]? = ar_sz[cref.toNat + 3 + j]?) ∧
          M6ShrkPad ar_p s3.core.arena cref.toNat old_sz.toNat nsz.toNat ∧
          ShrkPad ar_p s3.core.arena cref.toNat old_sz.toNat nsz.toNat ∧
          (FullMem c { s3 with core := { s3.core with arena := ar_p } } ⋆ R) m_p)
        (fun _ ⟨nhdr2, ⟨⟩⟩ m_p
            ⟨ar_p, harp_len, hng2, hsh2, hout_p, hsz_p, hpay_p, hmpad, hspad, hmp⟩ => by
          have hcref_ltp : (cref.setWidth 64).toNat < ar_p.length := by
            rw [hcref0_eq, harp_len]; omega
          fvt_steps
          have hmf := fullMem_eq_of_arena_eq
            (show ar_p.set (cref.setWidth 64).toNat nhdr2 = ar_p.set cref.toNat nhdr2 by
              rw [hcref0_eq]) hm
          exact hk nhdr2 ar_p _ harp_len hng2 hsh2 hout_p hsz_p hpay_p hmpad hspad hmf)
        (fun Jp hJp => by
          fvt_steps
          · have hsh0 : (nhdr &&& 0x00800000#32) = 0#32 := by c0_bound
            let term := (cref.setWidth 64 + 3#64 + old_sz.setWidth 64 - 1#64).toNat
            have hraw0 : (s3.core.arena[cref.toNat]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
              have : fullArenaHdr s3 cref.toNat = s3.core.arena[cref.toNat]?.getD 0#32 := rfl
              rw [← this, hhdr_eq, ← hsh_nh, hsh0]
            have hpad_pr : (∀ p, cref.toNat + 3 + nsz.toNat ≤ p →
                p < cref.toNat + 3 + old_sz.toNat - 1 →
                (ar_sz.set term 0xFFFFFFFF#32)[p]? = s3.core.arena[p]?) ∧
                (ar_sz.set term 0xFFFFFFFF#32)[cref.toNat + 3 + old_sz.toNat - 1]? =
                  some 0xFFFFFFFF#32 :=
              ⟨fun p hp1 hp2 => by
                 rw [List.getElem?_set_ne (by omega)]; exact hasz_pad p hp1 (by omega),
               by rw [show cref.toNat + 3 + old_sz.toNat - 1 = term by omega]
                  exact List.getElem?_set_self (by omega)⟩
            refine hJp (nhdr ||| 0x00800000#32, ()) _
              ⟨ar_sz.set term 0xFFFFFFFF#32, by simp [hasz_cap],
               by rw [s13_bv32_or_shrk_garb, hng_nh], s13_bv32_or_shrk_ne0 nhdr,
               fun p hp => by rw [List.getElem?_set_ne (by omega)]; exact hasz_out p hp,
               by rw [List.getElem?_set_ne (by omega)]; exact hasz_sz,
               fun j hj => List.getElem?_set_ne (by omega),
               by unfold M6ShrkPad; rw [ite_eq_left hraw0]; exact hpad_pr,
               by unfold ShrkPad; rw [ite_eq_left hraw0]; exact hpad_pr, hm⟩
          · have hsh_ne : (nhdr &&& 0x00800000#32) ≠ 0#32 := by c0_bound
            have hraw_ne : (s3.core.arena[cref.toNat]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
              have : fullArenaHdr s3 cref.toNat = s3.core.arena[cref.toNat]?.getD 0#32 := rfl
              rw [← this, hhdr_eq, ← hsh_nh]; exact hsh_ne
            refine hJp (nhdr, ()) _ ⟨ar_sz, hasz_cap, hng_nh, hsh_ne, hasz_out, hasz_sz,
              fun _ _ => rfl,
              by unfold M6ShrkPad; rw [ite_eq_right hraw_ne]; exact hasz_pad,
              by unfold ShrkPad; rw [ite_eq_right hraw_ne]; exact hasz_pad, hm⟩))
    (fun Jg hJg => by
      fvt_to_group
      · refine wp_join_group (ts := [i32])
          (fun (nhdr, ()) m_i => m = m_i ∧ (nhdr &&& 0x00080000#32) = 0#32 ∧
            (nhdr &&& 0x00800000#32) = (hdr &&& 0x00800000#32))
          (fun _ ⟨nhdr, ⟨⟩⟩ m_i h => hJg (nhdr, ()) m_i h)
          (fun Ji hJi => by
            fvt_steps
            · exact hJi ((hdr &&& ~~~0x7FFFF#32) ||| ((nsz - 1#32) &&& 0x7FFFF#32), ()) _
                ⟨rfl, by rw [bv32_set_glue_garb hdr _ (bv32_glue_mask_garb _), hhdr_ng],
                 bv32_set_glue_shrk hdr _ (bv32_glue_mask_shrk _)⟩
            · exact hJi (hdr, ()) _ ⟨rfl, hhdr_ng, rfl⟩)
      · exact hJg (hdr, ()) _ ⟨rfl, hhdr_ng, rfl⟩)

end Helpers

attribute [local c0_load] c0_load_ws1_z_s13 c0_load_ws1_b_s13 c0_load_ws2_z_s13 c0_load_ws2_b_s13
  c0_load_ws2_4_s13

/-! ## 2. Step-13 Commit Flag-Mark Loop & Shrink Tail (`full_viv_commit_m6_s5_wp`) -/

section CommitProof

open FullVivifyHelpers

private abbrev s13CommitFlagLoopExpr (c : FullCfg) (nhdr olen : Val i32)
    (k : Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) => k) Blocks.nil) fun Jfv =>
  fvOp (OpCode.and i32) (Arg.var nhdr, Arg.imm 4194304, ()) fun pred =>
  fvOp (OpCode.cmp .eq i32 .bool rfl) (Arg.var pred.fst, Arg.imm 0, ()) fun cpred =>
  Expr.jnz (Arg.var cpred.fst)
    (fvOp (OpCode.add i64) (Arg.var c.hdr, Arg.imm 800, ()) fun pfl =>
     Expr.load i64 (Arg.var pfl.fst) fun fl_v =>
     Expr.group (sig := [[i32]]) (fun Jkv => Blocks.cons (fun (pkv : Tup Val [i32]) =>
       fvOp (OpCode.cmp .ult i32 .bool rfl) (Arg.var pkv.fst, Arg.var olen, ()) fun ckv =>
       Expr.jnz (Arg.var ckv.fst)
         (fvOp (OpCode.zext 32 64) (Arg.var pkv.fst, ()) fun kv64 =>
          fvOp (OpCode.mul i64) (Arg.var kv64.fst, Arg.imm 4, ()) fun off_v =>
          fvOp (OpCode.add i64) (Arg.var c.pWorkStk2, Arg.var off_v.fst, ()) fun pout_v =>
          Expr.load i32 (Arg.var pout_v.fst) fun lv =>
          Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun (pfb : Tup Val [i32]) =>
            fvOp (OpCode.lshr i32) (Arg.var lv, Arg.imm 1, ()) fun lvh =>
            fvOp (OpCode.zext 32 64) (Arg.var lvh.fst, ()) fun lvh64 =>
            fvOp (OpCode.mul i64) (Arg.var lvh64.fst, Arg.imm 4, ()) fun off_f =>
            fvOp (OpCode.add i64) (Arg.var fl_v, Arg.var off_f.fst, ()) fun pfv =>
            fvOp (OpCode.lshr i32) (Arg.var lv, Arg.imm 1, ()) fun lvh2 =>
            fvOp (OpCode.zext 32 64) (Arg.var lvh2.fst, ()) fun lvh64b =>
            fvOp (OpCode.mul i64) (Arg.var lvh64b.fst, Arg.imm 4, ()) fun off_fb =>
            fvOp (OpCode.add i64) (Arg.var fl_v, Arg.var off_fb.fst, ()) fun pfvb =>
            Expr.load i32 (Arg.var pfvb.fst) fun fl_old =>
            fvOp (OpCode.or i32) (Arg.var fl_old, Arg.imm 8, ()) fun fl1 =>
            fvOp (OpCode.or i32) (Arg.var fl1.fst, Arg.imm 16, ()) fun fl2 =>
            fvOp (OpCode.or i32) (Arg.var fl2.fst, Arg.var pfb.fst, ()) fun fl3 =>
            Expr.store (Arg.var fl3.fst) (Arg.var pfv.fst)
              (fvOp (OpCode.add i32) (Arg.var pkv.fst, Arg.imm 1, ()) fun kv1 =>
               Expr.jump Jkv.fst (Arg.var kv1.fst, ()))) Blocks.nil) fun Jfb =>
          fvOp (OpCode.and i32) (Arg.var lv, Arg.imm 1, ()) fun lv1 =>
          fvOp (OpCode.cmp .ne i32 .bool rfl) (Arg.var lv1.fst, Arg.imm 0, ()) fun clv1 =>
          Expr.jnz (Arg.var clv1.fst) (Expr.jump Jfb.fst (Arg.imm 64, ()))
            (Expr.jump Jfb.fst (Arg.imm 32, ())))
         (Expr.jump Jfv.fst ())) Blocks.nil) fun Jkv => Expr.jump Jkv.fst (Arg.imm 0, ()))
    (Expr.jump Jfv.fst ())

private theorem s13_commit_flag_loop_wp (Γ : Env) {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s_f : FullState} {R : Mem 64 → Prop} {nhdr olen : Val i32}
    {k : Expr Val Cont [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hsp_f : FullSparseInvW c F0 F_cur s_f)
    (holen_le : olen.toNat ≤ s_f.scratch.work_stk2.length)
    (hout_lt : ∀ j < olen.toNat,
      (s_f.scratch.work_stk2[j]?.getD 0#32).toNat < 2 * s_f.core.cur_vars)
    (hm : (FullMem c s_f ⋆ R) m)
    (hk : ∀ (fl' : List (BitVec 32)) m', fl'.length = c.max_vars →
      (FullMem c { s_f with core := { s_f.core with flags := fl' } } ⋆ R) m' →
      wp Γ Q X k m') :
    wp Γ Q X (s13CommitFlagLoopExpr c nhdr olen k) m := by
  have hcl := hsp_f.1.core_ok; have hcv := hcl.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  dsimp only [s13CommitFlagLoopExpr, fvOp]
  refine wp_join_group (ts := [])
    (fun _ mf => ∃ fl' : List (BitVec 32), fl'.length = c.max_vars ∧
      (FullMem c { s_f with core := { s_f.core with flags := fl' } } ⋆ R) mf)
    (fun _ _ mf ⟨fl', hfl', hmf⟩ => hk fl' mf hfl' hmf)
    (fun Jfv hJfv => ?_)
  fvt_steps
  · refine wp_loop_inv (ts := [i32])
      (fun (kv, ()) mk => kv.toNat ≤ olen.toNat ∧ ∃ fl_k : List (BitVec 32),
        fl_k.length = c.max_vars ∧
        (FullMem c { s_f with core := { s_f.core with flags := fl_k } } ⋆ R) mk)
      (fun (kv, ()) _ => olen.toNat - kv.toNat)
      (fun Jkv hJkv => by
        fvt_steps
        exact hJkv (0#32, ()) m ⟨Nat.zero_le _, s_f.core.flags, hcl.flags_len, hm⟩)
      (fun Jkv (kv, ()) mk ⟨hkv_le, fl_k, hfl_k, hmk⟩ ihk => ?_)
    fvt_step; fvt_step
    · have hkv_lt : kv.toNat < olen.toNat := by c0_bound
      have hkv1 : (kv + 1#32).toNat = kv.toNat + 1 := by bv_omega
      have hkv_ws : (kv.setWidth 64).toNat < s_f.scratch.work_stk2.length := by bv_omega
      let lv := s_f.scratch.work_stk2[(kv.setWidth 64).toNat]'hkv_ws
      have hlv_lt : lv.toNat < 2 * s_f.core.cur_vars := by
        have h1 := hout_lt kv.toNat hkv_lt
        have hidx : (kv.setWidth 64).toNat = kv.toNat := by bv_omega
        have hkv_ws' : kv.toNat < s_f.scratch.work_stk2.length := by omega
        rw [List.getElem?_eq_getElem hkv_ws', Option.getD_some] at h1
        have hlv_eq : lv = s_f.scratch.work_stk2[kv.toNat]'hkv_ws' := Option.some.inj (by
          rw [← List.getElem?_eq_getElem hkv_ws, ← List.getElem?_eq_getElem hkv_ws']
          exact congrArg (s_f.scratch.work_stk2[·]?) hidx)
        rw [hlv_eq]; exact h1
      have hlv_fl : ((lv >>> 1#32).setWidth 64).toNat < fl_k.length := by
        have hshr : (lv >>> 1#32).toNat = lv.toNat / 2 := bv32_lshr1_toNat lv
        rw [hfl_k, BitVec.toNat_setWidth, hshr, Nat.mod_eq_of_lt (by omega)]; omega
      fvt_steps
      all_goals (
        refine ihk (kv + 1#32, ()) _ (by dsimp only; omega) ⟨by omega, _, ?_, by assumption⟩
        rw [List.length_set, hfl_k])
    · fvt_steps
      exact hJfv () mk ⟨fl_k, hfl_k, hmk⟩
  · exact hJfv () m ⟨s_f.core.flags, hcl.flags_len, hm⟩

private abbrev s13CommitShrkTailBody (c : FullCfg) (cref hdr old_sz olen : Val i32) :
    Expr Val Cont [i64] :=
  arOffPtr c.pArena cref 1 fun p => Expr.store (Arg.imm (t := i32) 2) (Arg.var p)
    (s13GlueShrkExpr c.pArena cref hdr old_sz olen fun nhdr_out =>
     s13CommitFlagLoopExpr c nhdr_out olen
      (fvOp (OpCode.sext 32 64) (Arg.imm 0, ()) fun p =>
       fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
       fvOp (OpCode.add i64) (Arg.var c.pWorkStk2, Arg.var p.fst, ()) fun p =>
       Expr.load i32 (Arg.var p.fst) fun l0 =>
       fvOp (OpCode.sext 32 64) (Arg.imm 1, ()) fun p =>
       fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
       fvOp (OpCode.add i64) (Arg.var c.pWorkStk2, Arg.var p.fst, ()) fun p =>
       Expr.load i32 (Arg.var p.fst) fun l1 =>
       Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
         fvOp (OpCode.add i64) (Arg.var c.hdr, Arg.imm 760, ()) fun p =>
         Expr.store (Arg.imm (t := i64) 1) (Arg.var p.fst)
           (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
              Expr.ret (Arg.imm 2, ())) Blocks.nil) fun Jbo =>
            fvOp (OpCode.add i64) (Arg.var c.hdr, Arg.imm 160, ()) fun p =>
            Expr.load i64 (Arg.var p.fst) fun ld =>
            fvOp (OpCode.cmp .ne i64 .bool rfl) (Arg.var ld, Arg.imm 0, ()) fun p =>
            Expr.jnz (Arg.var p.fst)
              (Expr.call "full_backtrack" (as := [i64, i64]) (bs := [])
                 (Arg.var c.hdr, Arg.imm 0, ()) fun _ => Expr.jump Jbo.fst ())
              (Expr.jump Jbo.fst ()))) Blocks.nil) fun Jo =>
       fvOp (OpCode.and i32) (Arg.var l1, Arg.imm 2147483647, ()) fun b1 =>
       Expr.call "full_watch_push" (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
         (Arg.var c.hdr, Arg.var l0, Arg.var b1.fst, Arg.var cref, Arg.imm 2, ()) fun ok1 =>
       Expr.jnz (Arg.var ok1.fst)
         (fvOp (OpCode.and i32) (Arg.var l0, Arg.imm 2147483647, ()) fun b0 =>
          Expr.call "full_watch_push" (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
            (Arg.var c.hdr, Arg.var l1, Arg.var b0.fst, Arg.var cref, Arg.imm 2, ()) fun ok2 =>
          Expr.jnz (Arg.var ok2.fst) (Expr.ret (Arg.imm 1, ())) (Expr.jump Jo.fst ()))
         (Expr.jump Jo.fst ())))

private abbrev s13CommitShrkTailExpr (c : FullCfg) (cref hdr old_sz olen : Val i32) :
    Expr Val Cont [i64] :=
  Expr.store (Arg.var olen) (Arg.var (c.pArena + (cref.setWidth 64 + 2) * 4))
    (s13CommitShrkTailBody c cref hdr old_sz olen)

private theorem s13_commit_shrk_tail_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s3 : FullState}
    {R : Mem 64 → Prop} {cref hdr old_sz olen : Val i32} {ar4 : List (BitVec 32)}
    {m4 : Mem 64} {Q : Post [i64]} {X : XPost}
    (hsp3 : FullSparseInvW c F0 F_cur s3)
    (href : cref.toNat ∈ fullArenaClauseRefs s3)
    (hrefs3 : fullArenaClauseRefs s3 = fullArenaClauseRefs s)
    (hnonact3 : NonActiveReason s3.core cref.toNat)
    (hng3 : fullArenaClauseGarb s3 cref.toNat = false)
    (hhdr3 : fullArenaHdr s3 cref.toNat = hdr) (hhdr_ng : (hdr &&& 0x00080000#32) = 0#32)
    (hsz3 : fullArenaClauseSize s3 cref.toNat = old_sz.toNat)
    (hold_sz_3 : 3 ≤ old_sz.toNat) (holen3 : 3 ≤ olen.toNat) (holen_lt : olen.toNat < old_sz.toNat)
    (hcv3 : s3.core.cur_vars = s.core.cur_vars) (hal3 : s3.core.arena_len = s.core.arena_len)
    (hpr3 : s3.core.probing = s.core.probing) (hfu3 : s3.core.fuel = s.core.fuel)
    (hrr3 : s3.scratch.red_refs = s.scratch.red_refs)
    (htr3 : s3.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (holen_le : olen.toNat ≤ s3.scratch.work_stk2.length)
    (hout_lt : ∀ j < olen.toNat,
      (s3.scratch.work_stk2[j]?.getD 0#32).toNat < 2 * s3.core.cur_vars)
    (hout_nd : (((s3.scratch.work_stk2.take olen.toNat).map BitVec.toNat).map (· / 2)).Nodup)
    (hout_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s3.scratch.work_stk2.take olen.toNat).map BitVec.toNat)))
    (har4_len : ar4.length = c.arena_cap)
    (hcp4 : ∀ k < olen.toNat, ar4[cref.toNat + 3 + k]? = s3.scratch.work_stk2[k]?)
    (hout4 : ∀ p, (p < cref.toNat + 3 ∨ cref.toNat + 3 + olen.toNat ≤ p) →
      ar4[p]? = s3.core.arena[p]?)
    (hm4 : (FullMem c { s3 with core := { s3.core with arena := ar4 } } ⋆ R) m4)
    (hQ : ∀ r s' m', FullSparseInvW c F0 F_cur s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena_len = s.core.arena_len →
      s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs → s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (s13CommitShrkTailExpr c cref hdr old_sz olen) m4 := by
  have hw3 := hsp3.2.1; have hcl3 := hsp3.1.core_ok
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have hbd : cref.toNat + 3 + old_sz.toNat ≤ c.arena_cap := by
    have := hcl3.arena_len_le
    have := (hw3.arena.refs_wf cref.toNat href).2.2.1
    have := (hw3.arena.refs_wf cref.toNat href).2.2.2.1
    have : fullArenaClauseSizeCore s3.core cref.toNat = old_sz.toNat := hsz3
    omega
  have hcref0_eq : (cref.setWidth 64).toNat = cref.toNat := by bv_omega
  have hcref1_eq : (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1 := by bv_omega
  have hcref2_eq : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by bv_omega
  have hcref3_eq : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3 := by bv_omega
  have har4_lt2 : (cref.setWidth 64 + 2).toNat < ar4.length := by
    change (cref.setWidth 64 + 2#64).toNat < ar4.length; omega
  have har4_lt1 : (cref.setWidth 64 + 1#64).toNat < ar4.length := by omega
  let ar_sz :=
    (ar4.set (cref.setWidth 64 + 2).toNat olen).set (cref.setWidth 64 + 1#64).toNat 2#32
  obtain ⟨hasz_len, hasz_out, hasz_sz, hasz_pay, hasz_pad, _⟩ :=
    ar_set_sz_props (ar0 := ar4) (ar_orig := s3.core.arena)
      (by rw [hcl3.arena_len_arr]; exact har4_len)
      holen3 holen_lt (by rw [har4_len]; omega) rfl hcref2_eq hcref1_eq hout4
  have hasz_cap : ar_sz.length = c.arena_cap := by simp [ar_sz, har4_len]
  dsimp only [s13CommitShrkTailExpr, s13CommitShrkTailBody, arOffPtr, fvOp]
  fvt_to_group
  refine s13_glue_shrk_wp Γ hhdr3 hhdr_ng hold_sz_3 holen3 holen_lt hcap hbd hasz_cap
    hcref0_eq hcref3_eq hasz_out hasz_sz hasz_pad hm
    fun nhdr2 ar_p mf harp_len hng2 hsh2 hout_p hsz_p hpay_p hmpad _ hmf => ?_
  have hpay_ws2 : ∀ j < olen.toNat, ar_p[cref.toNat + 3 + j]? = s3.scratch.work_stk2[j]? :=
    fun j hj => (hpay_p j hj).trans ((hasz_pay j hj).trans (hcp4 j hj))
  have hcref_lt8 : cref.toNat < 0x80000000 := by omega
  have h0_ws2 : 0 < s3.scratch.work_stk2.length := by omega
  have h1_ws2 : 1 < s3.scratch.work_stk2.length := by omega
  obtain ⟨hsp_f0, hrefs_f0⟩ := s13_commit_shrk_hnonact hsp3 href hnonact3 hng3 holen3
    (by rw [hsz3]; exact holen_lt) holen_le hout_lt hout_nd hout_ent harp_len hng2 hsh2
    (by rw [hsz3]; exact hout_p) hsz_p hpay_ws2 (by rw [hsz3]; exact hmpad)
  let s_f0 : FullState := { s3 with core := { s3.core with arena := ar_p.set cref.toNat nhdr2 } }
  refine s13_commit_flag_loop_wp Γ hsp_f0 holen_le hout_lt hmf fun fl' mf1 hfl' hmf1 => ?_
  let s_f : FullState := { s_f0 with core := { s_f0.core with flags := fl' } }
  have hsp_f : FullSparseInvW c F0 F_cur s_f := fullSparseInvW_with_flags hsp_f0 hfl'
  have hrefs_fs : fullArenaClauseRefs s_f = fullArenaClauseRefs s := hrefs_f0.trans hrefs3
  have h0_sf : 0 < s_f.scratch.work_stk2.length := h0_ws2
  have h1_sf : 1 < s_f.scratch.work_stk2.length := h1_ws2
  fvt_to_group
  refine wp_join_group (ts := [])
    (fun _ m_oom => ∃ s_o : FullState, FullSparseInvW c F0 F_cur s_o ∧
      s_o.core.cur_vars = s.core.cur_vars ∧ s_o.core.arena_len = s.core.arena_len ∧
      s_o.core.probing = s.core.probing ∧ s_o.core.fuel = s.core.fuel ∧
      fullArenaClauseRefs s_o = fullArenaClauseRefs s ∧
      s_o.scratch.red_refs = s.scratch.red_refs ∧
      s_o.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ (FullMem c s_o ⋆ R) m_oom)
    (fun _ _ m_oom ⟨s_o, hsp_o, hcv_o, hal_o, hpr_o, hfu_o, href_o, hrr_o, htr_o, hm_o⟩ => by
      let s_o1 := { s_o with core := { s_o.core with oom := 1#64 } }
      have hsp_o1 := s13_sparseW_with_oom hsp_o 1#64
      have hcl_o64 : s_o1.core.cur_level < 2 ^ 64 := by
        change s_o.core.cur_level < 2 ^ 64
        have := hsp_o.2.1.cur_level_le; have := hsp_o.1.core_ok.trail_end_le
        have := hsp_o.1.core_ok.cur_vars_le; omega
      have hbt_o : (0#64 : BitVec 64).toNat < s_o1.core.cur_level →
          (0#64 : BitVec 64).toNat < c.max_vars := fun h => by
        change (0#64 : BitVec 64).toNat < s_o.core.cur_level at h
        have := hsp_o.2.1.cur_level_le; have := hsp_o.1.core_ok.trail_end_le
        have := hsp_o.1.core_ok.cur_vars_le; omega
      fvt_to_group
      refine wp_join_group (ts := [])
        (fun _ mf2 => ∃ sf : FullState, FullSparseInvW c F0 F_cur sf ∧
          sf.core.cur_vars = s.core.cur_vars ∧ sf.core.arena_len = s.core.arena_len ∧
          sf.core.probing = s.core.probing ∧ sf.core.fuel = s.core.fuel ∧
          fullArenaClauseRefs sf = fullArenaClauseRefs s ∧
          sf.scratch.red_refs = s.scratch.red_refs ∧
          sf.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ (FullMem c sf ⋆ R) mf2)
        (fun _ _ mf2 ⟨sf, hspf, hcvf, half, hprf, hfuf, hreff, hrrf, htrf, hmf2⟩ => by
          fvt_steps
          exact hQ 2#64 sf mf2 hspf hcvf half hprf hfuf hreff hrrf htrf
            (Or.inr (Or.inl rfl)) (fun h => by cases h) hmf2)
        (fun Jbo hJbo => by
          fvt_steps
          · c0_call hBacktrack
            refine ⟨c, s_o1, R, rfl, hsp_o1.1, hcl_o64, hbt_o, hsp_o1.2.1.trail_lits_lt, hm,
              fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
                hlen_bt _ _ _ hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
            have hsp_bt := FullVivTop.FullSparseInvW.of_backtrack hsp_o1 (Nat.zero_le _) hlen_bt
              hpres_bt (hw_bt F0 F_cur hsp_o1.2.1 (Nat.zero_le _))
            rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
            fvt_steps
            exact hJbo () m_bt ⟨_, hsp_bt, hcv_o, hal_o, hpr_o, hfu_o, href_o, hrr_o, htr_o, hm_bt⟩
          · exact hJbo () _ ⟨s_o1, hsp_o1, hcv_o, hal_o, hpr_o, hfu_o, href_o, hrr_o, htr_o, hm⟩))
    (fun Jo hJo => by
      fvt_steps; c0_call hWatchPush
      let l0 := s_f.scratch.work_stk2[0]'h0_sf
      let l1 := s_f.scratch.work_stk2[1]'h1_sf
      obtain ⟨hl1, lay1, hp1_1, hp1_2⟩ := s13_watchPush_pre (blk := l1) hsp_f hcref_lt8
      refine ⟨c, s_f, R, rfl, hl1, lay1, hp1_1, hp1_2, hmf1,
        fun ok1 wvec3 wstk3 wlen3 wu3 wsort3 m5 hlen5 hlay5 hoth5 hok1_t hok1_f hm5 => ?_⟩
      have hsp5 := fullWatchPush_large_preserves_sparseInvW hsp_f
        (FullVivifyTactics.bv32_mask_lo31_props l1).1 hcref_lt8 (hrefs_f0 ▸ href) hlen5 hlay5
        hoth5 (fun h => let t := hok1_t h;
          ⟨t.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2 rfl⟩) (fun h => (hok1_f h).1)
      fvt_steps
      · c0_call hWatchPush
        obtain ⟨hl2, lay2, hp2_1, hp2_2⟩ := s13_watchPush_pre (blk := l0) hsp5 hcref_lt8
        refine ⟨c, _, R, rfl, hl2, lay2, hp2_1, hp2_2, hm5,
          fun ok2 wvec4 wstk4 wlen4 wu4 wsort4 m6 hlen6 hlay6 hoth6 hok2_t hok2_f hm6 => ?_⟩
        have hsp6 := fullWatchPush_large_preserves_sparseInvW hsp5
          (FullVivifyTactics.bv32_mask_lo31_props l0).1 hcref_lt8
          (hrefs_f0 ▸ href)
          hlen6 hlay6 hoth6 (fun h => let t := hok2_t h;
            ⟨t.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2 rfl⟩) (fun h => (hok2_f h).1)
        fvt_steps
        · exact hQ 1#64 _ m6 hsp6 hcv3 hal3 hpr3 hfu3 hrefs_fs hrr3 htr3 (Or.inl rfl)
            (fun h => by cases h) hm6
        · exact hJo () m6 ⟨_, hsp6, hcv3, hal3, hpr3, hfu3, hrefs_fs, hrr3, htr3, hm6⟩
      · exact hJo () m5 ⟨_, hsp5, hcv3, hal3, hpr3, hfu3, hrefs_fs, hrr3, htr3, hm5⟩)

theorem full_viv_commit_m6_s5_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hUnwatch : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBinM6 : ∀ a m Q X, fullAddBinM6Spec a m Q X →
      Γ "full_add_bin_m6" [i64, i32, i32] [i64] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hUnreason : ∀ a m Q X, fullVivUnreasonM6Spec a m Q X →
      Γ "full_viv_unreason_m6" [i64, i32] [] a m Q X)
    (hBestWatch : ∀ a m Q X, fullVivBestWatchM6Spec a m Q X →
      Γ "full_viv_best_watch_m6" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullVivCommitM6Spec a m Q X →
      Func.wp Γ FullFidelityStep13S5VivifyBackbone.full_viv_commit_m6_body a m Q X := by
  rintro ⟨h, cref, olen, implied, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hsp, href, hng, holen_le_mv, hout_ok, hm0, hQ⟩
  have hw := hsp.2.1; have hcl := hsp.1.core_ok; have hscl := hsp.1.scratch_ok
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have har_len := hcl.arena_len_arr; have halen_le := hcl.arena_len_le
  have hws2_len := hscl.work_stk2_len; have hcref_wf := hw.arena.refs_wf cref.toNat href
  have holen_le : olen.toNat ≤ 2 * c.max_vars := by omega
  have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
    have := hw.cur_level_le; have := hcl.trail_end_le; have := hcl.cur_vars_le; omega
  obtain ⟨hcref_lt, _, hcref0_eq, _, hcref2_eq, hcref3_eq, hcref4_eq, hhdr_ng_raw⟩ :=
    cref_hdr_facts (fv_sparseW_to_sparse hsp) hw href hng
  let hdr := s.core.arena[(cref.setWidth 64).toNat]'(by rw [hcref0_eq]; exact hcref_lt)
  let old_sz := s.core.arena[(cref.setWidth 64 + 2#64).toNat]'(by rw [hcref2_eq]; omega)
  have hhdr_eq : hdr = fullArenaHdr s cref.toNat := ar_get_eq_getD hcref0_eq _
  have hold_sz_eq : old_sz.toNat = fullArenaClauseSizeCore s.core cref.toNat :=
    congrArg BitVec.toNat (ar_get_eq_getD hcref2_eq _)
  have hold_sz_3 : 3 ≤ old_sz.toNat := by rw [hold_sz_eq]; exact hcref_wf.2.1
  have hold_sz_bd : cref.toNat + 3 + old_sz.toNat ≤ s.core.arena.length := by
    rw [hold_sz_eq]; omega
  have hhdr_ng : (hdr &&& 0x00080000#32) = 0#32 := by
    simpa [hhdr_eq, fullArenaHdr, fullArenaHdrCore] using hhdr_ng_raw
  have hcref3_lt : (cref.setWidth 64 + 3#64).toNat < s.core.arena.length := by omega
  have hcref4_lt : (cref.setWidth 64 + 4#64).toNat < s.core.arena.length := by omega
  have hsz_s_eq : fullArenaClauseSize s cref.toNat = old_sz.toNat := hold_sz_eq.symm
  let s1 : FullState :=
    { s with scratch := { s.scratch with viv_cnt := s.scratch.viv_cnt + 1#64 } }
  have hsp1 : FullSparseInvW c F0 F_cur s1 := s13_sparseW_with_vivcnt hsp _
  have hbt_lt_mv : ∀ t : BitVec 64, t.toNat < s1.core.cur_level → t.toNat < c.max_vars :=
    fun t h => by
      have := hw.cur_level_le; have := hcl.trail_end_le; have := hcl.cur_vars_le
      change t.toNat < s.core.cur_level at h; omega
  unfold Func.wp FullFidelityStep13S5VivifyBackbone.full_viv_commit_m6_body
  fvt_to_group
  · exact hQ 1#64 s m0 hsp rfl rfl rfl rfl rfl rfl rfl (Or.inl rfl) (fun h => by cases h) hm0
  · have holen_lt : olen.toNat < old_sz.toNat := by dsimp only [old_sz]; c0_bound
    obtain ⟨_, _, hout_ent⟩ := hout_ok (by rw [hsz_s_eq]; exact holen_lt)
    have holen0 : olen.toNat = 0 := by c0_bound
    have hu : (cnfOfClauses F_cur).Unsat :=
      unsat_of_entails_nil (by simpa [holen0] using hout_ent)
    refine wp_join_group (ts := [])
      (fun _ mb => ∃ sb : FullState, FullSparseInvW c F0 F_cur sb ∧
        sb.core.cur_vars = s.core.cur_vars ∧ sb.core.arena_len = s.core.arena_len ∧
        sb.core.probing = s.core.probing ∧ sb.core.fuel = s.core.fuel ∧
        fullArenaClauseRefs sb = fullArenaClauseRefs s ∧
        sb.scratch.red_refs = s.scratch.red_refs ∧
        sb.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ (FullMem c sb ⋆ R) mb)
      (fun _ _ mb ⟨sb, hspb, hcvb, halb, hprb, hfub, hrefb, hrrb, htrb, hmb⟩ => by
        fvt_steps
        exact hQ 20#64 _ _ (s13_sparseW_with_inc hspb hu) hcvb halb hprb hfub hrefb hrrb htrb
          (Or.inr (Or.inr rfl)) (fun _ => hw.ext_sound.2 hu) hm)
      (fun Jb hJb => by
        fvt_steps
        · c0_call hBacktrack
          refine ⟨c, s1, R, rfl, hsp1.1, hcl_lt64, hbt_lt_mv 0#64, hw.trail_lits_lt, hm,
            fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
              hlen_bt _ _ _ hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
          have hsp_bt := FullVivTop.FullSparseInvW.of_backtrack hsp1 (Nat.zero_le _) hlen_bt
            hpres_bt (hw_bt F0 F_cur hw (Nat.zero_le _))
          rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
          fvt_steps
          exact hJb () m_bt ⟨_, hsp_bt, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm_bt⟩
        · exact hJb () _ ⟨s1, hsp1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm⟩)
  · have holen_lt : olen.toNat < old_sz.toNat := by dsimp only [old_sz]; c0_bound
    obtain ⟨hout_lt, _, hout_ent⟩ := hout_ok (by rw [hsz_s_eq]; exact holen_lt)
    have holen_ne0 : olen.toNat ≠ 0 := fun h =>
      (by c0_bound : olen ≠ 0#32) (BitVec.eq_of_toNat_eq h)
    have holen_le2 : olen.toNat ≤ 2 := by c0_bound
    refine wp_join_group (ts := [])
      (fun _ mb => ∃ sb : FullState, FullSparseInvW c F0 F_cur sb ∧ sb.core.cur_level = 0 ∧
        sb.core.arena = s.core.arena ∧ sb.core.cur_vars = s.core.cur_vars ∧
        sb.core.arena_len = s.core.arena_len ∧ sb.core.probing = s.core.probing ∧
        sb.core.fuel = s.core.fuel ∧ sb.scratch.work_stk2 = s.scratch.work_stk2 ∧
        sb.scratch.red_refs = s.scratch.red_refs ∧
        sb.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ (FullMem c sb ⋆ R) mb)
      (fun _ _ mb ⟨sb, hspb, hl0b, harb, hcvb, halb, hprb, hfub, hws2b, hrrb, htrb, hmb⟩ => by
        have hcv_pos : 0 < s.core.cur_vars := by have := hout_lt 0 (by omega); omega
        have hcv_le_mv : s.core.cur_vars ≤ c.max_vars := hcl.cur_vars_le
        have hrefb : fullArenaClauseRefs sb = fullArenaClauseRefs s := by
          unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [harb, halb]
        have hhdrb : fullArenaHdr sb cref.toNat = hdr := by
          unfold fullArenaHdr fullArenaHdrCore; rw [harb]; exact hhdr_eq.symm
        have hcref3_b : (cref.setWidth 64 + 3#64).toNat < sb.core.arena.length := by
          rw [harb]; exact hcref3_lt
        have hcref4_b : (cref.setWidth 64 + 4#64).toNat < sb.core.arena.length := by
          rw [harb]; exact hcref4_lt
        fvt_steps; c0_call hUnwatch
        refine ⟨c, sb, R, rfl, hspb.1, s13_watchLayout hspb, hmb,
          fun wvec1 wstk1 wu1 m2 hlen1 hlay1 hmode1 hm2 => ?_⟩
        have hsp_w1 := s13_unwatch_sparse hspb hlen1 hmode1
        fvt_steps; c0_call hUnwatch
        refine ⟨c, _, R, rfl, hsp_w1.1, s13_watchLayout hsp_w1, hm2,
          fun wvec2 wstk2 wu2 m3 hlen2 hlay2 hmode2 hm3 => ?_⟩
        let s3 : FullState := { sb with core :=
          { sb.core with wvec := wvec2, wstk := wstk2, wusable := wu2 } }
        have hsp3 : FullSparseInvW c F0 F_cur s3 := s13_unwatch_sparse hsp_w1 hlen2 hmode2
        have hm3' : (FullMem c s3 ⋆ R) m3 := hm3
        clear hsp_w1 hlen1 hlay1 hmode1 hm2 hm3 wvec1 wstk1 wu1 m2 hlen2 hlay2 hmode2
        have hcref_lt3 : cref.toNat < s3.core.arena.length := by
          change cref.toNat < sb.core.arena.length; rw [harb]; exact hcref_lt
        fvt_to_group
        obtain ⟨hsp_g, hrefs_g0, _⟩ :=
          fv_markGarbW hsp3 hl0b (hrefb ▸ href) (sb.core.arena_garbage + 3#64 + old_sz.setWidth 64)
        let s_g : FullState := { s3 with core := { s3.core with
          arena := s3.core.arena.set cref.toNat (fullArenaHdr s3 cref.toNat ||| 0x00080000#32)
          arena_garbage := sb.core.arena_garbage + 3#64 + old_sz.setWidth 64 } }
        have hm_g : (FullMem c s_g ⋆ R) m := by
          have har_eq :
              s3.core.arena.set (cref.setWidth 64).toNat (hdr ||| 0x00080000#32) =
              s3.core.arena.set cref.toNat (fullArenaHdr s3 cref.toNat ||| 0x00080000#32) := by
            rw [hcref0_eq, show fullArenaHdr s3 cref.toNat = hdr from hhdrb]
          exact fullMem_eq_of_arena_ag_eq har_eq hm
        clear hm
        have hrefs_g : fullArenaClauseRefs s_g = fullArenaClauseRefs s := hrefs_g0.trans hrefb
        have hws2_g : s_g.scratch.work_stk2 = s.scratch.work_stk2 := hws2b
        refine s13_decr_count_wp Γ hm_g fun ni' nr' mg hmg => ?_
        let sg1 : FullState :=
          { s_g with core := { s_g.core with num_irred := ni', num_redundant := nr' } }
        have hmg' : (FullMem c sg1 ⋆ R) mg := hmg
        clear hmg
        have hsp_g1 := s13_sparseW_with_counts hsp_g ni' nr'
        have h0_ws2 : 0 < sg1.scratch.work_stk2.length := by
          change 0 < sb.scratch.work_stk2.length; rw [hws2b, hws2_len]; omega
        fvt_steps
        · have holen1 : olen.toNat = 1 := by c0_bound
          have hu0_lt : (sg1.scratch.work_stk2[0]'h0_ws2).toNat < 2 * sg1.core.cur_vars := by
            have h := hout_lt 0 (by omega)
            rwa [← hws2_g, List.getElem?_eq_getElem h0_ws2, Option.getD_some, ← hcvb] at h
          have hu0_ent : (cnfOfClauses F_cur).EntailsClause
              (cnfClause [(sg1.scratch.work_stk2[0]'h0_ws2).toNat]) := by
            simpa only [← hws2_g] using take_entails_1 holen1 (by rw [hws2_len]; omega) hout_ent
          c0_call hAddUnit
          refine ⟨c, F0, F_cur, sg1, R, rfl, hsp_g1.1, hsp_g1.2.1, fun _ => hu0_ent, hmg',
            fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
              ph' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m4 hlen4 hw4 _ hltf _ hm4 => ?_⟩
          have hsp4 : FullSparseInvW c F0 F_cur _ :=
            ⟨hlen4, hw4, hsp_g1.2.2.1, hsp_g1.2.2.2.1, hsp_g1.2.2.2.2.1, hsp_g1.2.2.2.2.2⟩
          fvt_steps
          · exact hQ 1#64 _ m4 hsp4 hcvb halb hprb hfub hrefs_g hrrb htrb
              (Or.inl rfl) (fun h => by cases h) hm4
          · exact hQ 20#64 _ m4 hsp4 hcvb halb hprb hfub hrefs_g hrrb htrb
              (Or.inr (Or.inr rfl)) (fun _ => (hltf hu0_lt hc).1) hm4
        · have holen2 : olen.toNat = 2 := by
            have : olen ≠ 1#32 := by c0_bound
            have : olen.toNat ≠ 1 := fun h => this (BitVec.eq_of_toNat_eq h)
            omega
          have h1_ws2 : 1 < sg1.scratch.work_stk2.length := by
            change 1 < sb.scratch.work_stk2.length; rw [hws2b, hws2_len]; omega
          have hu0_lt : (sg1.scratch.work_stk2[0]'h0_ws2).toNat < 2 * sg1.core.cur_vars := by
            have h := hout_lt 0 (by omega)
            rwa [← hws2_g, List.getElem?_eq_getElem h0_ws2, Option.getD_some, ← hcvb] at h
          have hu1_lt : (sg1.scratch.work_stk2[1]'h1_ws2).toNat < 2 * sg1.core.cur_vars := by
            have h := hout_lt 1 (by omega)
            rwa [← hws2_g, List.getElem?_eq_getElem h1_ws2, Option.getD_some, ← hcvb] at h
          have hbin_ent : (cnfOfClauses F_cur).EntailsClause
              (cnfClause [(sg1.scratch.work_stk2[0]'h0_ws2).toNat,
                          (sg1.scratch.work_stk2[1]'h1_ws2).toNat]) := by
            simpa only [← hws2_g] using take_entails_2 holen2 (by rw [hws2_len]; omega) hout_ent
          fvt_steps; c0_call hAddBinM6
          refine ⟨c, F0, F_cur, sg1, R, rfl, hsp_g1.1, hsp_g1.2.1, hl0b, fun _ _ => hbin_ent,
            hmg', fun br vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu'
              nb' oom' inc' ph' wso' m4 hlen4 hw4 _ h20 _ hm4 => ?_⟩
          have hsp4 : FullSparseInvW c F0 F_cur _ :=
            ⟨hlen4, hw4, hsp_g1.2.2.1, hsp_g1.2.2.2.1, hsp_g1.2.2.2.2.1, hsp_g1.2.2.2.2.2⟩
          fvt_steps
          · exact hQ 20#64 _ m4 hsp4 hcvb halb hprb hfub hrefs_g hrrb htrb
              (Or.inr (Or.inr rfl)) (fun _ => (h20 hc).1) hm4
          · exact hQ 2#64 _ m4 hsp4 hcvb halb hprb hfub hrefs_g hrrb htrb
              (Or.inr (Or.inl rfl)) (fun h => by cases h) hm4
          · exact hQ 1#64 _ m4 hsp4 hcvb halb hprb hfub hrefs_g hrrb htrb
              (Or.inl rfl) (fun h => by cases h) hm4)
      (fun Jb hJb => by
        fvt_steps
        · c0_call hBacktrack
          refine ⟨c, s1, R, rfl, hsp1.1, hcl_lt64, hbt_lt_mv 0#64, hw.trail_lits_lt, hm,
            fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
              hlen_bt _ _ hcl_bt hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
          have hsp_bt := FullVivTop.FullSparseInvW.of_backtrack hsp1 (Nat.zero_le _) hlen_bt
            hpres_bt (hw_bt F0 F_cur hw (Nat.zero_le _))
          rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
          fvt_steps
          exact hJb () m_bt ⟨_, hsp_bt, by simpa using hcl_bt, rfl, rfl, rfl, rfl, rfl, rfl,
            rfl, rfl, hm_bt⟩
        · have hcl0 : s1.core.cur_level = 0 := by
            have h0 : BitVec.ofNat 64 s.core.cur_level = 0#64 := by assumption
            have := congrArg BitVec.toNat h0
            rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_lt64] at this
          exact hJb () _ ⟨s1, hsp1, hcl0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm⟩)
  · have holen_lt : olen.toNat < old_sz.toNat := by dsimp only [old_sz]; c0_bound
    obtain ⟨hout_lt, hout_nd, hout_ent⟩ := hout_ok (by rw [hsz_s_eq]; exact holen_lt)
    have holen3 : 3 ≤ olen.toNat := by
      have hgt2 : 2 < olen.toNat := by c0_bound
      omega
    refine wp_join_group (ts := [])
      (fun _ mp => ∃ sp : FullState, FullSparseInvW c F0 F_cur sp ∧
        sp.core.arena = s.core.arena ∧ sp.core.cur_vars = s.core.cur_vars ∧
        sp.core.arena_len = s.core.arena_len ∧ sp.core.probing = s.core.probing ∧
        sp.core.fuel = s.core.fuel ∧ sp.scratch.work_stk2 = s.scratch.work_stk2 ∧
        sp.scratch.red_refs = s.scratch.red_refs ∧
        sp.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ (FullMem c sp ⋆ R) mp)
      (fun _ _ mp ⟨sp, hspp, harp, hcvp, halp, hprp, hfup, hws2p, hrrp, htrp, hmp⟩ => by
        fvt_steps; c0_call hUnreason
        refine ⟨c, F0, F_cur, sp, R, rfl, hspp, hmp,
          fun su mu hspu hnonact hcvu haru halu hpru hfuu _ hws2u hrru htru hmu => ?_⟩
        have hlt_u : ∀ i < olen.toNat,
            (su.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * su.core.cur_vars := by
          rw [hws2u, hws2p, hcvu, hcvp]; exact hout_lt
        fvt_steps; c0_call hBestWatch
        refine ⟨c, su, R, rfl, hspu.1, holen_le_mv, hlt_u, hmu,
          fun ws2' mw hws2'_len hperm hmw => ?_⟩
        let sbw : FullState := { su with scratch := { su.scratch with work_stk2 := ws2' } }
        have hsp_bw : FullSparseInvW c F0 F_cur sbw := s13_sparseW_with_ws2 hspu hws2'_len
        obtain ⟨hout_lt', hout_nd', hout_ent'⟩ := s13_ws2_perm_props
          (by rw [hws2_len]; omega) (by rw [hws2'_len]; omega)
          (by rw [hws2u, hws2p] at hperm; exact hperm) hout_lt hout_nd hout_ent
        have hcref3_bw : (cref.setWidth 64 + 3#64).toNat < sbw.core.arena.length := by
          change _ < su.core.arena.length; rw [haru, harp]; exact hcref3_lt
        have hcref4_bw : (cref.setWidth 64 + 4#64).toNat < sbw.core.arena.length := by
          change _ < su.core.arena.length; rw [haru, harp]; exact hcref4_lt
        fvt_steps; c0_call hUnwatch
        refine ⟨c, sbw, R, rfl, hsp_bw.1, s13_watchLayout hsp_bw, hmw,
          fun wvec1 wstk1 wu1 m2 hlen1 hlay1 hmode1 hm2 => ?_⟩
        have hsp_w1 := s13_unwatch_sparse hsp_bw hlen1 hmode1
        fvt_steps; c0_call hUnwatch
        refine ⟨c, _, R, rfl, hsp_w1.1, s13_watchLayout hsp_w1, hm2,
          fun wvec2 wstk2 wu2 m3 hlen2 hlay2 hmode2 hm3 => ?_⟩
        let s3 : FullState := { sbw with core :=
          { sbw.core with wvec := wvec2, wstk := wstk2, wusable := wu2 } }
        have hsp3 : FullSparseInvW c F0 F_cur s3 := s13_unwatch_sparse hsp_w1 hlen2 hmode2
        have har3_eq : s3.core.arena = s.core.arena := haru.trans harp
        have hcv3 : s3.core.cur_vars = s.core.cur_vars := hcvu.trans hcvp
        have hal3 : s3.core.arena_len = s.core.arena_len := halu.trans halp
        have hpr3 : s3.core.probing = s.core.probing := hpru.trans hprp
        have hfu3 : s3.core.fuel = s.core.fuel := hfuu.trans hfup
        have hrr3 : s3.scratch.red_refs = s.scratch.red_refs := hrru.trans hrrp
        have htr3 : s3.scratch.tarjan_reach = s.scratch.tarjan_reach := htru.trans htrp
        have hrefs3 : fullArenaClauseRefs s3 = fullArenaClauseRefs s := by
          unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har3_eq, hal3]
        have hng3 : fullArenaClauseGarb s3 cref.toNat = false := by
          unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
          rw [har3_eq]; exact hng
        have hsz3 : fullArenaClauseSize s3 cref.toNat = old_sz.toNat := by
          unfold fullArenaClauseSize fullArenaClauseSizeCore; rw [har3_eq]; exact hsz_s_eq
        have hhdr3 : fullArenaHdr s3 cref.toNat = hdr := by
          unfold fullArenaHdr fullArenaHdrCore; rw [har3_eq]; exact hhdr_eq.symm
        have hnonact3 : NonActiveReason s3.core cref.toNat := hnonact
        have hm3' : (FullMem c s3 ⋆ R) m3 := hm3
        clear hsp_w1 hlen1 hlay1 hmode1 hm2 hm3 wvec1 wstk1 wu1 m2 hlen2 hlay2 hmode2 hsp_bw hmw
          hspu hmu hspp hmp
        fvt_to_group
        refine wp_loop_inv (ts := [i32])
          (fun (i, ()) m4 => ∃ ar4 : List (BitVec 32), i.toNat ≤ olen.toNat ∧
            ar4.length = c.arena_cap ∧
            (∀ k < i.toNat, ar4[cref.toNat + 3 + k]? = ws2'[k]?) ∧
            (∀ p, (p < cref.toNat + 3 ∨ cref.toNat + 3 + i.toNat ≤ p) →
              ar4[p]? = s3.core.arena[p]?) ∧
            (FullMem c { s3 with core := { s3.core with arena := ar4 } } ⋆ R) m4)
          (fun (i, ()) _ => olen.toNat - i.toNat) ?_ ?_
        · intro Jc hJc; fvt_steps
          exact hJc (0#32, ()) m3 ⟨s3.core.arena, by simp, by rw [har3_eq]; exact har_len,
            fun _ hk => by simp at hk, fun _ _ => rfl, hm3'⟩
        · rintro Jc ⟨i, ⟨⟩⟩ m4 ⟨ar4, hi_le, har4_len, hcp4, hout4, hm4⟩ ihc
          fvt_step; fvt_step
          · have hi_lt : i.toNat < olen.toNat := by c0_bound
            have hi_idx : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat =
                cref.toNat + 3 + i.toNat := by bv_omega
            have hi_lt_ar : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat < ar4.length := by
              omega
            have hi_lt_ws2 : i.toNat < ws2'.length := by omega
            have hi1_eq : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
            fvt_steps
            let ar5 := ar4.set (cref.toNat + 3 + i.toNat) (ws2'[i.toNat]'hi_lt_ws2)
            have har5_eq : ar4.set (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat
                (ws2'[i.toNat]'hi_lt_ws2) = ar5 := by simp only [ar5, hi_idx]
            refine ihc (i + 1#32, ()) _ (by dsimp only; omega)
              ⟨ar5, by omega, by simp [ar5, har4_len], fun k hk => ?_, fun p hp => ?_,
                fullMem_eq_of_arena_eq har5_eq hm⟩
            · rcases (by omega : k < i.toNat ∨ k = i.toNat) with hk' | rfl
              · dsimp only [ar5]; rw [List.getElem?_set_ne (by omega)]; exact hcp4 k hk'
              · dsimp only [ar5]
                rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem hi_lt_ws2]
            · dsimp only [ar5]; rw [List.getElem?_set_ne (by omega)]; exact hout4 p (by omega)
          · have hi_eq : i.toNat = olen.toNat := by c0_bound
            exact s13_commit_shrk_tail_wp Γ hBacktrack hWatchPush hsp3
              (hrefs3 ▸ href) hrefs3 hnonact3 hng3 hhdr3 hhdr_ng hsz3 hold_sz_3 holen3 holen_lt
              hcv3 hal3 hpr3 hfu3 hrr3 htr3 (by change olen.toNat ≤ ws2'.length; omega)
              (by change ∀ j < olen.toNat, (ws2'[j]?.getD 0#32).toNat < 2 * s3.core.cur_vars
                  rw [hcv3]; exact hout_lt')
              hout_nd' hout_ent' har4_len (fun k hk => hcp4 k (by omega))
              (fun p hp => hout4 p (by omega)) hm4 hQ)
      (fun Jp hJp => by
        fvt_to_group
        · refine wp_join_group (ts := [])
            (fun _ mp => ∃ sp : FullState, FullSparseInvW c F0 F_cur sp ∧
              sp.core.arena = s.core.arena ∧ sp.core.cur_vars = s.core.cur_vars ∧
              sp.core.arena_len = s.core.arena_len ∧ sp.core.probing = s.core.probing ∧
              sp.core.fuel = s.core.fuel ∧ sp.scratch.work_stk2 = s.scratch.work_stk2 ∧
              sp.scratch.red_refs = s.scratch.red_refs ∧
              sp.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ (FullMem c sp ⋆ R) mp)
            (fun _ _ mp h => hJp () mp h)
            (fun Ji hJi => by
              fvt_steps
              · have htgt_lt : ((olen - 2#32).setWidth 64).toNat < s1.core.cur_level := by
                  have h1 : ((olen - 2#32).setWidth 64).toNat <
                      (BitVec.ofNat 64 s.core.cur_level).toNat := by c0_bound
                  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_lt64] at h1
                c0_call hBacktrack
                refine ⟨c, s1, R, rfl, hsp1.1, hcl_lt64,
                  hbt_lt_mv ((olen - 2#32).setWidth 64), hw.trail_lits_lt, hm,
                  fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
                    hlen_bt _ _ _ hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
                have hsp_bt := FullVivTop.FullSparseInvW.of_backtrack hsp1 (Nat.le_of_lt htgt_lt)
                  hlen_bt hpres_bt (hw_bt F0 F_cur hw (Nat.le_of_lt htgt_lt))
                rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
                fvt_steps
                exact hJi () m_bt ⟨_, hsp_bt, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm_bt⟩
              · exact hJi () _ ⟨s1, hsp1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm⟩)
        · exact hJp () _ ⟨s1, hsp1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm⟩)

end CommitProof

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

end
