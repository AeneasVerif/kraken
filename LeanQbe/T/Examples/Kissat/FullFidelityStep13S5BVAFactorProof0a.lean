/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5BVAFactor
public import LeanQbe.T.Examples.Kissat.FullSpec2
public import LeanQbe.T.Examples.Kissat.FullBinLuckyLemmas1
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof0
public import LeanQbe.T.Examples.Kissat.FullM7V2RobustProof0
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullAssignAddLemmas1
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullReduceLemmas1
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S5-C — BVA & Factor Proofs Part 0a

Step-13 `S5-C` specifications and parametric `(Γ : Env)` `Func.wp` proofs (`public section`,
`0` `@[expose]` on theorems/lemmas, `0` `import all`, `std3`, `XPost`-polymorphic):
1. `step13AddClauseSpec` (`full_add_clause`) — adds `flags'` update in the `len = 2` branch.
2. `step13DeleteBinarySpec` (`full_delete_binary`) — adds `< 2 * c.max_vars` bounds & `flags'`.
3. `step13BvaScanCandsSpec` (`full_bva_scan_cands`) — `cand ≤ init_lits` & `ncntd ≤ 2 * max_vars`.
4. Proofs for `full_add_bin_m6`, `full_add_clause`, and `full_delete_binary`.
-/

set_option autoImplicit false

local elab "c0_hfast" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local elab "c0_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullAssignAddTactics
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullFidelityBva
open LeanQbe.T.Examples.Kissat.FullFidelityStep13S5BVAFactor
open scoped Full.FullArenaTactics Full.FullAssignAddTactics Full.FullBinLuckyTactics

/-! ## 1. Step-13 S5-C `Spec` Definitions -/

/-- Step-13 `full_add_clause`: extends `Full.fullAddClauseSpec` with `flags'` mutation on
`len = 2` (`fl[v0]` / `fl[v1]` `FL_SUBSUME | FL_ELIM_C | FL_FACT_*`). -/
@[expose] def step13AddClauseSpec : Spec [i64, i32, i32, .bool] [i64] :=
  fun (h, len, _glue, _red, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      s.core.dense_mode = 0#64 ∧ len.toNat ≤ c.max_vars ∧
      (2 ≤ len.toNat →
        (∀ l ∈ (s.core.tmp.take len.toNat).map BitVec.toNat, l < 2 * s.core.cur_vars) ∧
        ((s.core.tmp.take len.toNat).map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.core.tmp.take len.toNat).map BitVec.toNat))) ∧
      (FullMem c s ⋆ R) m ∧
      if len.toNat < 2 then Q (0xFFFFFFFF#64, ()) m
      else if len.toNat = 2 then
        ∀ r flags' wvec' wstk' wlen' wusable' nb' wsort' m',
          let s' : FullState :=
            { s with
              core := { s.core with flags := flags', wvec := wvec', wstk := wstk',
                                    wlen := wlen', wusable := wusable', num_binary := nb' }
              scratch := { s.scratch with wsort := wsort' } }
          (r = 0xFFFFFFFF#64 ∨ r = 0xFFFFFFFE#64) →
          s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → (FullMem c s' ⋆ R) m' → Q (r, ()) m'
      else
        ∀ r arena' alen' wvec' wstk' wlen' wusable' fred' ni' nr' wsort' m',
          let s' : FullState :=
            { s with
              core := { s.core with arena := arena', arena_len := alen', wvec := wvec',
                                    wstk := wstk', wlen := wlen', wusable := wusable',
                                    first_reducible := fred', num_irred := ni',
                                    num_redundant := nr' }
              scratch := { s.scratch with wsort := wsort' } }
          (r = 0xFFFFFFFF#64 ∨ r = BitVec.ofNat 64 s.core.arena_len) →
          s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
          (∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s') →
          (FullArenaVarsNodup s → FullArenaVarsNodup s') →
          (r = BitVec.ofNat 64 s.core.arena_len → alen' = s.core.arena_len + 3 + len.toNat ∧
            s.core.arena_len ∈ fullArenaClauseRefs s' ∧
            fullArenaClauseGarb s' s.core.arena_len = false ∧
            fullArenaClauseLits s' s.core.arena_len =
              (s.core.tmp.take len.toNat).map BitVec.toNat) →
          (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem step13AddClauseSpec_monoX {xs : Tup Val [i64, i32, i32, .bool]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : step13AddClauseSpec xs m Q X) :
    step13AddClauseSpec xs m Q X' :=
  let (_, _, _, _, ()) := xs; h

theorem step13AddClauseSpec_noExit : ∀ xs m Q X, step13AddClauseSpec xs m Q X →
    step13AddClauseSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step13AddClauseSpec_monoX h

/-- Step-13 `full_delete_binary`: extends `Full.fullDeleteBinarySpec` with `a, b < 2 * max_vars`
bounds and `flags'` update (`FL_ELIM_C | FL_FACT_*`). -/
@[expose] def step13DeleteBinarySpec : Spec [i64, i32, i32] [] := fun (h, a, b, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧
    a.toNat < 2 * c.max_vars ∧ b.toNat < 2 * c.max_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ flags' wvec' wstk' wu' nb' m',
      let s' : FullState :=
        { s with core := { s.core with flags := flags', wvec := wvec', wstk := wstk',
                                       wusable := wu', num_binary := nb' } }
      s'.LengthsOk c → WatchStackLayout s'.core →
      (∀ F_cur, ModeWatchesInv F_cur s.core → ModeWatchesInv F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'

theorem step13DeleteBinarySpec_monoX {xs : Tup Val [i64, i32, i32]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : step13DeleteBinarySpec xs m Q X) : step13DeleteBinarySpec xs m Q X' :=
  let (_, _, _, ()) := xs; h

theorem step13DeleteBinarySpec_noExit : ∀ xs m Q X, step13DeleteBinarySpec xs m Q X →
    step13DeleteBinarySpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step13DeleteBinarySpec_monoX h

/-- Step-13 `full_bva_scan_cands`: relaxes candidate guard to `cand ≤ init_lits` and caps
`ncntd ≤ 2 * max_vars` (matching `work_stk1.length = 2 * max_vars`). -/
@[expose] def step13BvaScanCandsSpec : Spec [i64, i32, i32, i64] [i32] :=
  fun (h, row_off, cur_qn, init_lits, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧
      s.core.dense_mode ≠ 0#64 ∧
      init_lits.toNat ≤ 2 * s.core.cur_vars ∧
      (∀ l < 2 * c.max_vars, (s.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
      row_off.toNat + cur_qn.toNat ≤ c.scratch_cap ∧
      (∀ qi < cur_qn.toNat,
        let w := s.scratch.scratch_buf[row_off.toNat + qi]?.getD 0#32
        if (w &&& 0x80000000#32) ≠ 0#32 then (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars
        else w.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s w.toNat = false) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ncntd : BitVec 32) wsort' ws1' ws2' ant' m',
        let s' : FullState :=
          { s with scratch :=
            { s.scratch with wsort := wsort', work_stk1 := ws1', work_stk2 := ws2',
                             ant_sz := ant' } }
        s'.LengthsOk c → ncntd.toNat ≤ 2 * c.max_vars →
        (∀ i < ncntd.toNat,
          (ws1'[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧
          (ws1'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
        (FullMem c s' ⋆ R) m' → Q (ncntd, ()) m'

theorem step13BvaScanCandsSpec_monoX {xs : Tup Val [i64, i32, i32, i64]} {m : Mem 64}
    {Q : Post [i32]} {X X' : XPost} (h : step13BvaScanCandsSpec xs m Q X) :
    step13BvaScanCandsSpec xs m Q X' :=
  let (_, _, _, _, ()) := xs; h

theorem step13BvaScanCandsSpec_noExit : ∀ xs m Q X, step13BvaScanCandsSpec xs m Q X →
    step13BvaScanCandsSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step13BvaScanCandsSpec_monoX h

/-- Exposed `full_watch_pop_c0` spec matching `FullM7V2Robust.fullWatchPopC0Spec`. -/
@[expose] def step13WatchPopC0Spec : Spec [i64, i32, i32] [] :=
  fun (h, lit, cnt, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧
      lit.toNat < 2 * s.core.cur_vars ∧
      0 < cnt.toNat ∧ cnt.toNat ≤ fullWatchSize s lit.toNat ∧ (FullMem c s ⋆ R) m ∧
      ∀ wvec' wstk' wusable' m',
        let s' : FullState :=
          { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wusable' } }
        s'.LengthsOk c → WatchStackLayout s'.core →
        (∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
          fullWatchOff s' l = fullWatchOff s l ∧ fullWatchSize s' l = fullWatchSize s l ∧
          ∀ k < fullWatchSize s l,
            s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
        fullWatchOff s' lit.toNat = fullWatchOff s lit.toNat →
        fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat - cnt.toNat →
        (∀ k < fullWatchSize s lit.toNat - cnt.toNat,
          s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
            s.core.wstk[fullWatchOff s lit.toNat + k]?) →
        (FullMem c s' ⋆ R) m' → Q () m'

/-! ## 2. `full_add_bin_m6` (`FullM6VivBackbone.fullAddBinM6Spec`) -/

private theorem s13_entails_collapse_eq {F : List (List Nat)} {a : Nat}
    (h : (cnfOfClauses F).EntailsClause (cnfClause [a, a])) :
    (cnfOfClauses F).EntailsClause (cnfClause [a]) :=
  entails_of_mem_or_false h fun l hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> exact Or.inl (by simp)

theorem full_add_bin_m6_s5_wp (Γ : Env)
    (hhas : ∀ a m Q X, Full.fullHasBinSpec a m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] a m Q X)
    (halvl : ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hwpush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ args m Q X, fullAddBinM6Spec args m Q X →
      Func.wp Γ FullFidelityStep13S5BVAFactor.full_add_bin_m6_body args m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hcl0, hent, hm, hQ⟩
  have hcl := hlen.core_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl.cur_vars_le; have hvl := hcl.vals_len; have hfll0 := hcl.flags_len
  have hret0 : Q (0#64, ()) m :=
    hQ 0#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
      s.core.trail_end s.core.unassigned s.core.unflushed s.core.wvec s.core.wstk s.core.wlen
      s.core.wusable s.core.num_binary s.core.oom s.core.inconsistent s.scratch.phases
      s.scratch.wsort m hlen hw (Or.inl rfl) (fun h2 => by cases h2) (fun h2 => by cases h2) hm
  unfold Func.wp FullFidelityStep13S5BVAFactor.full_add_bin_m6_body; dsimp only
  c0_hfast_nogrp
  c0_hsplit
  · exact hret0
  · exact hret0
  · exact hret0
  · have ha_lt : a.toNat < 2 * s.core.cur_vars := by
      have h1 := Nat.lt_of_not_le (by assumption : ¬ _ ≤ a.toNat)
      rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
        show (2 : Nat) ^ (OfNat.ofNat 1 : Nat) = 2 from rfl,
        Nat.mod_eq_of_lt (by omega)] at h1; omega
    have hb_lt : b.toNat < 2 * s.core.cur_vars := by
      have h1 := Nat.lt_of_not_le (by assumption : ¬ _ ≤ b.toNat)
      rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
        show (2 : Nat) ^ (OfNat.ofNat 1 : Nat) = 2 from rfl,
        Nat.mod_eq_of_lt (by omega)] at h1; omega
    have hne_neg : a ≠ b ^^^ 1#32 := by assumption
    c0_hfast_nogrp
    all_goals try exact hret0
    have hent_ab := hent ha_lt hb_lt
    have hdom_a := hw.vals_domain a.toNat ha_lt
    have hdom_b := hw.vals_domain b.toNat hb_lt
    refine wp_join_group (ts := [])
      (fun _ mJ => mJ = m ∧
        ¬ (s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8 ∧
           s.core.vals[b.toNat]?.getD 0#8 = 0xFF#8) ∧
        s.core.vals[a.toNat]?.getD 0#8 ≠ 1#8 ∧
        s.core.vals[b.toNat]?.getD 0#8 ≠ 1#8)
      ?_ ?_
    rotate_left
    · intro J hJ
      have ha_pos : s.core.vals[a.toNat]?.getD 0#8 ≠ 1#8 := by
        have h0 : BitVec.slt 0#32
            (BitVec.signExtend 32 (s.core.vals[a.toNat]'(by omega))) = false := by assumption
        intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
        rw [heq] at h0; revert h0; decide
      have hb_pos : s.core.vals[b.toNat]?.getD 0#8 ≠ 1#8 := by
        have h0 : BitVec.slt 0#32
            (BitVec.signExtend 32 (s.core.vals[b.toNat]'(by omega))) = false := by assumption
        intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
        rw [heq] at h0; revert h0; decide
      c0_hfast
      · have hva_neg : s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8 := by
          have hlt : BitVec.slt (BitVec.signExtend 32
              (s.core.vals[a.toNat]'(by omega))) 0#32 = true := by assumption
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom_a ⊢
          rcases hdom_a with h | h | h <;> rw [h] at hlt
          · exact absurd hlt (by decide)
          · exact absurd hlt (by decide)
          · exact h
        have hvb_neg : s.core.vals[b.toNat]?.getD 0#8 = 0xFF#8 := by
          have hlt : BitVec.slt (BitVec.signExtend 32
              (s.core.vals[b.toNat]'(by omega))) 0#32 = true := by assumption
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom_b ⊢
          rcases hdom_b with h | h | h <;> rw [h] at hlt
          · exact absurd hlt (by decide)
          · exact absurd hlt (by decide)
          · exact h
        have hFcur_unsat : (cnfOfClauses F_cur).Unsat := by
          refine unsat_of_entails_nil (entails_of_mem_or_false hent_ab fun l hl => Or.inr ?_)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl
          · obtain ⟨ia, hia, haeq⟩ := (hw.vals_false_iff _ ha_lt).mp hva_neg
            have hs := hw.level0_sound ia hia (by have := hw.lvl_le ia hia; omega)
            rwa [haeq] at hs
          · obtain ⟨ib, hib, hbeq⟩ := (hw.vals_false_iff _ hb_lt).mp hvb_neg
            have hs := hw.level0_sound ib hib (by have := hw.lvl_le ib hib; omega)
            rwa [hbeq] at hs
        have hlen_inc : ({ s with core := { s.core with inconsistent := 1#64 } } :
            FullState).LengthsOk c := ⟨{ hcl with }, hlen.scratch_ok⟩
        have hw' : FullWitnessInv c F0 F_cur { s.core with inconsistent := 1#64 } :=
          { hw with
            inconsistent_sound := fun _ => hFcur_unsat
            arena := { hw.arena with len_ok := hw.arena.len_ok }
            watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
        exact hQ 20#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl
          s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed s.core.wvec
          s.core.wstk s.core.wlen s.core.wusable s.core.num_binary s.core.oom 1#64
          s.scratch.phases s.scratch.wsort _ hlen_inc hw'
          (Or.inr (Or.inr (Or.inr rfl))) (fun _ => ⟨hw.ext_sound.2 hFcur_unsat, by decide⟩)
          (fun h2 => by cases h2) (by assumption)
      · have hnb : s.core.vals[b.toNat]?.getD 0#8 ≠ 0xFF#8 := by
          have h0 : BitVec.slt (BitVec.signExtend 32
              (s.core.vals[b.toNat]'(by omega))) 0#32 = false := by assumption
          intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
          rw [heq] at h0; revert h0; decide
        exact hJ PUnit.unit _ ⟨rfl, fun ⟨_, hb⟩ => hnb hb, ha_pos, hb_pos⟩
      · have hna : s.core.vals[a.toNat]?.getD 0#8 ≠ 0xFF#8 := by
          have h0 : BitVec.slt (BitVec.signExtend 32
              (s.core.vals[a.toNat]'(by omega))) 0#32 = false := by assumption
          intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
          rw [heq] at h0; revert h0; decide
        exact hJ PUnit.unit _ ⟨rfl, fun ⟨ha, _⟩ => hna ha, ha_pos, hb_pos⟩
    rintro _ _ mJ ⟨rfl, hnot_both, ha_pos, hb_pos⟩
    have hassign_lit : ∀ (lit : BitVec 32), lit.toNat < 2 * s.core.cur_vars →
        s.core.vals[lit.toNat]?.getD 0#8 = 0#8 →
        (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]) →
        wp Γ Q X (Expr.call (as := [i64, i32, i32, i32]) (bs := []) "full_assign_lvl"
          (Arg.var c.hdr, Arg.var lit, Arg.imm (4294967295#32 : Val i32),
            Arg.imm (0#32 : Val i32), ())
          fun _ => Expr.ret (Arg.imm (1#64 : Val i64), ())) mJ := by
      intro lit hlit hun hunit
      c0_call halvl
      refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
      have hte_lt : s.core.trail_end < c.max_vars := by
        have := hw.trail_end_lt_of_unassigned hlit hun; omega
      have hnot_cond : ¬ (s.core.cur_vars ≤ lit.toNat / 2 ∨
          c.max_vars ≤ s.core.trail_end ∨ s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
        intro h; rcases h with h1 | h2 | h3 <;> first | omega | exact h3 hun
      rw [ite_eq_right hnot_cond]; dsimp only
      intro flags' unassigned' phases' m' hfll hphl hm'
      obtain ⟨hlen', hw'⟩ :=
        fbl_assignLevel0_preserves_fullWitness hlen hw hcl0 hfll hphl hlit hun hunit
      c0_hfast
      exact hQ 1#64 _ flags' _ _ _ _ _ unassigned' _ s.core.wvec s.core.wstk s.core.wlen
        s.core.wusable s.core.num_binary s.core.oom s.core.inconsistent phases' s.scratch.wsort
        m' hlen' hw' (Or.inr (Or.inl rfl)) (fun h2 => by cases h2) (fun h2 => by cases h2) hm'
    c0_hfast_nogrp
    refine wp_join_group (ts := []) (fun _ mK => mK = mJ ∧
      (s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8 ∨ a = b))
      ?_ ?_
    rotate_left
    · intro J hJ
      c0_hfast
      · have hva_neg : s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8 := by
          have hlt : BitVec.slt (BitVec.signExtend 32
              (s.core.vals[a.toNat]'(by omega))) 0#32 = true := by assumption
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom_a ⊢
          rcases hdom_a with h | h | h <;> rw [h] at hlt
          · exact absurd hlt (by decide)
          · exact absurd hlt (by decide)
          · exact h
        exact hJ () _ ⟨rfl, Or.inl hva_neg⟩
      · exact hJ () _ ⟨rfl, Or.inr (by assumption)⟩
      · have hna_neg : s.core.vals[a.toNat]?.getD 0#8 ≠ 0xFF#8 := by
          have h0 : BitVec.slt (BitVec.signExtend 32
              (s.core.vals[a.toNat]'(by omega))) 0#32 = false := by assumption
          intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
          rw [heq] at h0; revert h0; decide
        have hva0 : s.core.vals[a.toNat]?.getD 0#8 = 0#8 := by
          rcases hdom_a with h | h | h <;> first | exact h | contradiction
        have hvb_neg : s.core.vals[b.toNat]?.getD 0#8 = 0xFF#8 := by
          have hlt : BitVec.slt (BitVec.signExtend 32
              (s.core.vals[b.toNat]'(by omega))) 0#32 = true := by assumption
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom_b ⊢
          rcases hdom_b with h | h | h <;> rw [h] at hlt
          · exact absurd hlt (by decide)
          · exact absurd hlt (by decide)
          · exact h
        have hunit_a : (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat]) := by
          refine entails_of_mem_or_false hent_ab fun l hl => ?_
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl
          · exact Or.inl (by simp)
          · obtain ⟨ib, hib, hbeq⟩ := (hw.vals_false_iff _ hb_lt).mp hvb_neg
            have hs := hw.level0_sound ib hib (by have := hw.lvl_le ib hib; omega)
            right; rwa [hbeq] at hs
        exact hassign_lit a ha_lt hva0 hunit_a
      · have hna_neg : s.core.vals[a.toNat]?.getD 0#8 ≠ 0xFF#8 := by
            have h0 : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[a.toNat]'(by omega))) 0#32 = false := by assumption
            intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
            rw [heq] at h0; revert h0; decide
        have hva0 : s.core.vals[a.toNat]?.getD 0#8 = 0#8 := by
          rcases hdom_a with h | h | h <;> first | exact h | contradiction
        c0_call hhas
        refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, ?_⟩
        intro r _
        · c0_hfast
          · exact hret0
          · have hwpc := fbl_bv32_mask_bin b (by omega)
            have hwpc1 := fbl_bv32_mask_bin a (by omega)
            c0_call hwpush
            refine ⟨c, s, R, rfl, hlen, hw.watches.layout, fun _ => hwpc.1,
              fun h2 => absurd h2 (by decide), hm, ?_⟩
            dsimp only
            intro ok1 wvec1 wstk1 wlen1 wu1 wsort1 m1 hlen1 hlay1 hother1 hok1t hok1f hm1
            let s1 : FullState :=
              { s with
                core := { s.core with wvec := wvec1, wstk := wstk1,
                                      wlen := wlen1, wusable := wu1 }
                scratch := { s.scratch with wsort := wsort1 } }
            c0_hfast_nogrp
            · obtain ⟨_, _, hsz1, hpref1, hw0_1, _⟩ := hok1t (by assumption)
              have hok1 : ok1 = true := by assumption
              have hw1_ok : ModeWatchesInv F_cur s1.core :=
                fbl_watchPush_bin_preserves_modeWatches (ok := ok1) hw.watches hlay1 rfl rfl
                  (fun _ r => r) ⟨hwpc.2.1, hwpc.1, hwpc.2.2 ▸ hb_lt, hwpc.2.2 ▸ hent_ab⟩
                  hother1 (fun _ => ⟨ha_lt, hsz1, hpref1, hw0_1⟩)
                  (fun hf => by rw [hok1] at hf; cases hf)
              c0_call hwpush
              refine ⟨c, s1, R, rfl, hlen1, hlay1, fun _ => hwpc1.1,
                fun h2 => absurd h2 (by decide), hm1, ?_⟩
              dsimp only
              intro ok2 wvec2 wstk2 wlen2 wu2 wsort2 m2 hlen2 hlay2 hother2 hok2t hok2f hm2
              let s2 : FullState :=
                { s1 with
                  core := { s1.core with wvec := wvec2, wstk := wstk2, wlen := wlen2,
                                         wusable := wu2 }
                  scratch := { s.scratch with wsort := wsort2 } }
              have hva_lt : (BitVec.setWidth 64 (a >>> (1 : Nat))).toNat <
                  s2.core.flags.length := by
                dsimp only [s2, s1]; rw [hfll0]; c0_bound
              have hvb_lt : (BitVec.setWidth 64 (b >>> (1 : Nat))).toNat <
                  s2.core.flags.length := by
                dsimp only [s2, s1]; rw [hfll0]; c0_bound
              c0_hfast_nogrp
              · obtain ⟨_, _, hsz2, hpref2, hw0_2, _⟩ := hok2t (by assumption)
                have hok2 : ok2 = true := by assumption
                have hw2_ok : ModeWatchesInv F_cur s2.core :=
                  fbl_watchPush_bin_preserves_modeWatches (ok := ok2) hw1_ok hlay2 rfl rfl
                    (fun _ r => r) ⟨hwpc1.2.1, hwpc1.1, hwpc1.2.2 ▸ ha_lt,
                      hwpc1.2.2 ▸ fbl_entailsClause_swap2 hent_ab⟩
                    hother2 (fun _ => ⟨hb_lt, hsz2, hpref2, hw0_2⟩)
                    (fun hf => by rw [hok2] at hf; cases hf)
                refine wp_join_group (ts := [i32]) (fun _ ma => (FullMem c s2 ⋆ R) ma) ?_ ?_
                rotate_left
                · intro Ja hJa
                  c0_hsplit
                  · c0_hfast; exact hJa (64#32, ()) _ (by assumption)
                  · c0_hfast; exact hJa (32#32, ()) _ (by assumption)
                · intro _ p ma hma
                  c0_hfast_nogrp
                  let addf : BitVec 32 := 512 ||| 128 ||| 256 ||| 8 ||| 16
                  let fl1 := s2.core.flags.set (BitVec.setWidth 64 (a >>> (1 : Nat))).toNat
                    ((s2.core.flags[(BitVec.setWidth 64 (a >>> (1 : Nat))).toNat]'hva_lt) |||
                      addf ||| p.1)
                  have hfl1_len : fl1.length = c.max_vars := by
                    simpa [fl1, s2, s1] using hlen2.core_ok.flags_len
                  have hvb_lt1 : (BitVec.setWidth 64 (b >>> (1 : Nat))).toNat < fl1.length := by
                    simpa [fl1, s2, s1, hfll0] using hvb_lt
                  refine wp_join_group (ts := [i32])
                    (fun _ mb => (FullMem c { s2 with core := { s2.core with flags := fl1 } } ⋆
                      R) mb) ?_ ?_
                  rotate_left
                  · intro Jb hJb
                    c0_hsplit
                    · c0_hfast; exact hJb (64#32, ()) _ (by assumption)
                    · c0_hfast; exact hJb (32#32, ()) _ (by assumption)
                  · intro _ q mb hmb
                    c0_hfast
                    let fl2 := fl1.set (BitVec.setWidth 64 (b >>> (1 : Nat))).toNat
                      ((fl1[(BitVec.setWidth 64 (b >>> (1 : Nat))).toNat]'hvb_lt1) |||
                        addf ||| q.1)
                    have hfl2_len : fl2.length = c.max_vars := by simpa [fl2] using hfl1_len
                    have hlen2' : ({ s2 with core := { s2.core with
                        flags := fl2, num_binary := s.core.num_binary + 1#64 } } :
                        FullState).LengthsOk c :=
                      ⟨{ hlen2.core_ok with flags_len := hfl2_len }, hlen2.scratch_ok⟩
                    have hw2' : FullWitnessInv c F0 F_cur
                        { s2.core with flags := fl2, num_binary := s.core.num_binary + 1#64 } :=
                      { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
                                watches := hw2_ok.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
                    exact hQ 1#64 s.core.vals fl2 s.core.lvl s.core.rsns s.core.trl
                      s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed
                      wvec2 wstk2 wlen2 wu2 (s.core.num_binary + 1#64) s.core.oom
                      s.core.inconsistent s.scratch.phases wsort2 m hlen2' hw2'
                      (Or.inr (Or.inl rfl)) (fun h2 => by cases h2) (fun h2 => by cases h2)
                      (by simpa only [fl2, fl1, addf, s2, s1,
                        show (1 : BitVec 64) = 1#64 from rfl] using hm)
              · have hw2_fail : ModeWatchesInv F_cur s2.core := by
                  refine fbl_watchPush_fail_preserves_modeWatches hw1_ok hlay2 rfl rfl
                    (fun _ r => r) ?_
                  intro l hl
                  by_cases hle : l = b.toNat
                  · subst hle; exact (hok2f (by assumption)).1 hb_lt
                  · exact hother2 l hl hle
                exact hQ 2#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl
                  s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed
                  wvec2 wstk2 wlen2 wu2 s.core.num_binary 1#64 s.core.inconsistent
                  s.scratch.phases wsort2 m ⟨{ hlen2.core_ok with }, hlen2.scratch_ok⟩
                  { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
                            watches := hw2_fail.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
                  (Or.inr (Or.inr (Or.inl rfl))) (fun h2 => by cases h2) (fun _ => by decide)
                  (by simpa only [s2, s1, show (1 : BitVec 64) = 1#64 from rfl] using hm)
            · have hw1_fail : ModeWatchesInv F_cur s1.core := by
                refine fbl_watchPush_fail_preserves_modeWatches hw.watches hlay1 rfl rfl
                  (fun _ r => r) ?_
                intro l hl
                by_cases hle : l = a.toNat
                · subst hle; exact (hok1f (by assumption)).1 ha_lt
                · exact hother1 l hl hle
              exact hQ 2#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl
                s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed
                wvec1 wstk1 wlen1 wu1 s.core.num_binary 1#64 s.core.inconsistent
                s.scratch.phases wsort1 m ⟨{ hlen1.core_ok with }, hlen1.scratch_ok⟩
                { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
                          watches := hw1_fail.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
                (Or.inr (Or.inr (Or.inl rfl))) (fun h2 => by cases h2) (fun _ => by decide)
                (by simpa only [s1, show (1 : BitVec 64) = 1#64 from rfl] using hm)
    · rintro _ _ mK ⟨rfl, hcond⟩
      have hvb0 : s.core.vals[b.toNat]?.getD 0#8 = 0#8 := by
        have hnb : s.core.vals[b.toNat]?.getD 0#8 ≠ 0xFF#8 := by
          rcases hcond with hva_neg | rfl
          · exact fun hb => hnot_both ⟨hva_neg, hb⟩
          · exact fun hb => hnot_both ⟨hb, hb⟩
        rcases hdom_b with h | h | h <;> first | exact h | contradiction
      have hunit_b : (cnfOfClauses F_cur).EntailsClause (cnfClause [b.toNat]) := by
        rcases hcond with hva_neg | rfl
        · refine entails_of_mem_or_false hent_ab fun l hl => ?_
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl
          · obtain ⟨ia, hia, haeq⟩ := (hw.vals_false_iff _ ha_lt).mp hva_neg
            have hs := hw.level0_sound ia hia (by have := hw.lvl_le ia hia; omega)
            right; rwa [haeq] at hs
          · exact Or.inl (by simp)
        · exact s13_entails_collapse_eq hent_ab
      exact hassign_lit b hb_lt hvb0 hunit_b

/-! ## 3. `full_add_clause` (`step13AddClauseSpec`) -/

private abbrev s13AddClauseState (s : FullState) (len : Nat)
    (arena' wvec' wstk' : List (BitVec 32)) (wlen' : Nat)
    (wusable' fred' ni' nr' : BitVec 64) (wsort' : List (BitVec 32)) : FullState :=
  { s with
    core :=
      { s.core with
        arena := arena', arena_len := s.core.arena_len + 3 + len
        wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable'
        first_reducible := fred', num_irred := ni', num_redundant := nr' }
    scratch := { s.scratch with wsort := wsort' } }

private theorem s13AddClauseRollback_preserves_witness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {arena' wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wusable' : BitVec 64}
    {wsort' : List (BitVec 32)}
    (hlen' : ({ s with
      core := { s.core with arena := arena', wvec := wvec', wstk := wstk', wlen := wlen',
                            wusable := wusable' }
      scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hlay' : WatchStackLayout
      { s.core with arena := arena', wvec := wvec', wstk := wstk', wlen := wlen',
                    wusable := wusable' })
    (hhold : ∀ k < s.core.arena_len, arena'[k]? = s.core.arena[k]?)
    (hw_pres : ∀ l < 2 * s.core.cur_vars,
      fullWatchSizeCore
        { s.core with arena := arena', wvec := wvec', wstk := wstk', wlen := wlen',
                      wusable := wusable' } l = fullWatchSizeCore s.core l ∧
      ∀ idx < fullWatchSizeCore s.core l,
        wstk'[fullWatchOffCore
          { s.core with arena := arena', wvec := wvec', wstk := wstk', wlen := wlen',
                        wusable := wusable' } l + idx]? =
          s.core.wstk[fullWatchOffCore s.core l + idx]?) :
    let s' : FullState :=
      { s with
        core := { s.core with arena := arena', wvec := wvec', wstk := wstk', wlen := wlen',
                              wusable := wusable' }
        scratch := { s.scratch with wsort := wsort' } }
    FullWitnessInv c F0 F_cur s'.core ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (FullArenaVarsNodup s → FullArenaVarsNodup s') := by
  intro s'
  have hcl := hlen.core_ok; have hcl' := hlen'.core_ok
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff s'.core.arena s'.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := fun r hr =>
    hw.arena.arenaNextOff_extend (alen' := s.core.arena_len) (Nat.le_refl _) hhold r hr
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hmeta : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaHdrCore s'.core r = fullArenaHdrCore s.core r ∧
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr => by
    have hwf := hw.arena.refs_wf r hr
    have h1 : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena_len := by omega
    have hlen_ar : s.core.arena.length = c.arena_cap := hcl.arena_len_arr
    have hlen_ar' : s'.core.arena.length = c.arena_cap := hcl'.arena_len_arr
    have hbd : s.core.arena_len ≤ c.arena_cap := hcl.arena_len_le
    have h0 := hhold r (by omega); have h2 := hhold (r + 2) (by omega)
    have hsz : fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := by
      unfold fullArenaClauseSizeCore s'; rw [h2]
    refine ⟨by unfold fullArenaHdrCore s'; rw [h0], hsz,
      by unfold fullArenaClauseGarbCore fullArenaHdrCore s'; rw [h0],
      fullArenaClauseLitsCore_eq_of_hold (k := s.core) (k' := s'.core)
        (by rw [hlen_ar]; omega) (by rw [hlen_ar']; omega) hsz
        fun j hj => hhold (r + 3 + j) (by omega)⟩
  have ha' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := hw.arena.refs_wf r hr
      rw [hnxt r hr, (hmeta r hr).2.1]; exact hwf
    · intro r hr hsh; rw [hrefs] at hr; rw [(hmeta r hr).1] at hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh
      exact ⟨t, by rw [(hmeta r hr).2.1]; exact ht1, ht2,
        by dsimp only [s']; rw [hhold t ht2]; exact hsent⟩
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [(hmeta r hr).2.2.1] at hng; rw [(hmeta r hr).2.2.2] at hl
      exact hw.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      rw [(hmeta r hr).2.2.1] at hng; rw [(hmeta r hr).2.2.2]
      exact hw.arena.entails r hr hng
  have hwat' : ModeWatchesInv F_cur s'.core := by
    have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
      rw [CNF.entails_def]; exact fun _ h => h
    have hm0 := hw.watches; unfold ModeWatchesInv at hm0 ⊢
    by_cases hc : s.core.dense_mode = 0#64
    · rw [ite_eq_left hc] at hm0 ⊢
      refine ⟨hlay', fun l hl => ?_⟩
      obtain ⟨hsz, hslice⟩ := hw_pres l hl; rw [hsz]
      exact FullAssignAddSpecs.watchSlice_relocate (k := s.core) (k' := s'.core)
        hrefl (Nat.le_refl _) (fun r hr => hrefs ▸ hr) hslice (hm0.slices l hl)
    · rw [ite_eq_right hc] at hm0 ⊢
      refine ⟨hlay', fun l hl => ?_⟩
      obtain ⟨hsz, hslice⟩ := hw_pres l hl; rw [hsz]
      exact FullAssignAddSpecs.denseWatchSlice_relocate (k := s.core) (k' := s'.core)
        hrefl (Nat.le_refl _) (fun r hr => hrefs ▸ hr) hslice (hm0.slices l hl)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := ha', watches := hwat'
      reason_inv := fun idx hidx hne => by
        have hrs := hw.reason_inv idx hidx hne
        change if (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then _ else _
        split
        · rename_i hbin; rw [ite_eq_left hbin] at hrs; exact hrs
        · rename_i hlg; rw [ite_eq_right hlg] at hrs
          obtain ⟨hr, hng, hall⟩ := hrs
          exact ⟨hrefs ▸ hr, (hmeta _ hr).2.2.1.trans hng,
            fun q hq => hall q ((hmeta _ hr).2.2.2 ▸ hq)⟩
      reason_lit_mem := fun idx hidx hne hlg => by
        have hmem := hw.reason_lit_mem idx hidx hne hlg
        have hrs := hw.reason_inv idx hidx hne
        rw [ite_eq_right (fun h => h hlg)] at hrs
        change (s.core.trl[idx]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore s'.core _
        rw [(hmeta _ hrs.1).2.2.2]; exact hmem }
  have hnd' : FullArenaVarsNodup s → FullArenaVarsNodup s' := fun hnd r hr hng => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs] at hr
    change fullArenaClauseGarbCore s'.core r = false at hng
    rw [(hmeta r hr).2.2.1] at hng
    unfold fullArenaClauseLits; rw [(hmeta r hr).2.2.2]; exact hnd r hr hng
  exact ⟨hw', hrefs, hnd'⟩

private theorem s13_bv32_tag_bin_ne_sent {l : BitVec 32} (hl : l.toNat < 2 ^ 30) :
    ((l &&& 0x7FFFFFFF#32) ||| 0x80000000#32) ≠ 0xFFFFFFFF#32 := by
  intro h
  have h30 := congrArg (fun x : BitVec 32 => x.toNat.testBit 30) h
  have hmask : (l &&& 0x7FFFFFFF#32).toNat < 2 ^ 30 := by
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    have := Nat.mod_le l.toNat (2 ^ 31); omega
  have hbit_mask : (l &&& 0x7FFFFFFF#32).toNat.testBit 30 = false :=
    Nat.testBit_lt_two_pow hmask
  have hbit_or : ((l &&& 0x7FFFFFFF#32) ||| 0x80000000#32).toNat.testBit 30 = false := by
    rw [BitVec.toNat_or, Nat.testBit_or, hbit_mask]
    decide
  rw [hbit_or] at h30
  revert h30; decide

private theorem s13_add_clause_bin_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hPop : ∀ args m Q X, step13WatchPopC0Spec args m Q X →
      Γ "full_watch_pop_c0" [i64, i32, i32] [] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {glue : Val i32} {red : Val .bool}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hc_mv : 2 ≤ c.max_vars)
    (hlits_lt : ∀ l ∈ (s.core.tmp.take 2).map BitVec.toNat, l < 2 * s.core.cur_vars)
    (hent2 : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take 2).map BitVec.toNat)))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ r flags' wvec' wstk' wlen' wusable' nb' wsort' m',
      let s' : FullState :=
        { s with
          core := { s.core with flags := flags', wvec := wvec', wstk := wstk',
                                wlen := wlen', wusable := wusable', num_binary := nb' }
          scratch := { s.scratch with wsort := wsort' } }
      (r = 0xFFFFFFFF#64 ∨ r = 0xFFFFFFFE#64) →
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    Func.wp Γ FullFidelityStep13S5BVAFactor.full_add_clause_body (c.hdr, 2#32, glue, red, ())
      m Q X := by
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hco := hlen.core_ok
  have hcv_lt : s.core.cur_vars < 2 ^ 29 := by have := hco.cur_vars_le; omega
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
  have hb0_ne : b0 ≠ 0xFFFFFFFF#32 := s13_bv32_tag_bin_ne_sent (by omega)
  have hb1_ne : b1 ≠ 0xFFFFFFFF#32 := s13_bv32_tag_bin_ne_sent (by omega)
  unfold Func.wp FullFidelityStep13S5BVAFactor.full_add_clause_body; dsimp only
  c0_hfast
  all_goals try exact absurd rfl (by assumption)
  c0_call hPush
  refine ⟨c, s, R, rfl, hlen, hw.watches.layout, (fun _ => hb0_ne),
    (fun hc => absurd hc (by decide)), hm, ?_⟩
  intro ok1 wvec1 wstk1 wlen1 wu1 wsort1 m1 s1 hlen1 hlay1 hoth1 hok1t hok1f hm1
  have htm1_gt0 : 0 < s1.core.tmp.length := by rw [hlen1.core_ok.tmp_len_arr]; omega
  have htm1_gt1 : 1 < s1.core.tmp.length := by rw [hlen1.core_ok.tmp_len_arr]; omega
  have hwat1 : ModeWatchesInv F_cur s1.core :=
    FullAssignAddSpecs.fullWatchPush_preserves_modeWatchesInv
      hw.watches hlay1 rfl rfl (fun _ hr => hr)
      (fun _ => ⟨bv32_tag_bin_flag l1, hb0_ne,
        by rw [bv32_tag_bin_mask (by omega)]; exact hl1_lt,
        by rw [bv32_tag_bin_mask (by omega)]; exact hent2⟩)
      (fun hc => absurd hc (by decide)) hoth1 hok1t (fun h => (hok1f h).1)
  have hw1 : FullWitnessInv c F0 F_cur s1.core :=
    FullAssignAddSpecs.watchUpdate_preserves_witness hw hwat1
  c0_hfast
  · subst hc; c0_call hPush
    refine ⟨c, s1, R, rfl, hlen1, hlay1, (fun _ => hb1_ne),
      (fun hc => absurd hc (by decide)), hm1, ?_⟩
    intro ok2 wvec2 wstk2 wlen2 wu2 wsort2 m2 s2 hlen2 hlay2 hoth2 hok2t hok2f hm2
    have hwat2 : ModeWatchesInv F_cur s2.core :=
      FullAssignAddSpecs.fullWatchPush_preserves_modeWatchesInv hwat1 hlay2 rfl rfl
        (fun _ hr => hr)
        (fun _ => ⟨bv32_tag_bin_flag l0, hb1_ne,
          by rw [bv32_tag_bin_mask (by omega)]; exact hl0_lt,
          by rw [bv32_tag_bin_mask (by omega)]; exact hent2_swap⟩)
        (fun hc => absurd hc (by decide)) hoth2 hok2t (fun h => (hok2f h).1)
    have htm2_gt0 : 0 < s2.core.tmp.length := by rw [hlen2.core_ok.tmp_len_arr]; omega
    have htm2_gt1 : 1 < s2.core.tmp.length := by rw [hlen2.core_ok.tmp_len_arr]; omega
    have hv0_lt : (BitVec.setWidth 64 (s2.core.tmp[0]'htm2_gt0 >>> (1 : Nat))).toNat <
        s2.core.flags.length := by
      have ht0 : s2.core.tmp[0]'htm2_gt0 = l0 := rfl
      rw [ht0, zext_toNat _ (by decide), bv32_lshr1, hlen2.core_ok.flags_len]
      have := hco.cur_vars_le; omega
    have hv1_lt : (BitVec.setWidth 64 (s2.core.tmp[1]'htm2_gt1 >>> (1 : Nat))).toNat <
        s2.core.flags.length := by
      have ht1 : s2.core.tmp[1]'htm2_gt1 = l1 := rfl
      rw [ht1, zext_toNat _ (by decide), bv32_lshr1, hlen2.core_ok.flags_len]
      have := hco.cur_vars_le; omega
    c0_hfast_nogrp
    · -- `push2` succeeded: update `flags` and `num_binary`
      have hwat_fin : ModeWatchesInv F_cur
          { s2.core with num_binary := s.core.num_binary + 1#64 } :=
        hwat2.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
      have hw_base : FullWitnessInv c F0 F_cur
          { s2.core with num_binary := s.core.num_binary + 1#64 } :=
        FullAssignAddSpecs.watchUpdate_preserves_witness hw (oom' := s.core.oom) hwat_fin
      have hfin_post : ∀ fl', fl'.length = c.max_vars →
          ({ s2 with core := { s2.core with
            flags := fl', num_binary := s.core.num_binary + 1#64 } } : FullState).LengthsOk c ∧
          FullWitnessInv c F0 F_cur
            { s2.core with flags := fl', num_binary := s.core.num_binary + 1#64 } :=
        fun fl' hfl' =>
          ⟨{ core_ok := { hlen2.core_ok with flags_len := hfl' }, scratch_ok := hlen2.scratch_ok },
           { hw_base with
             arena := { hw_base.arena with len_ok := hw_base.arena.len_ok }
             watches := hw_base.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }⟩
      refine wp_join_group (ts := [i32]) (fun _ m_a => m_a = m2) ?_ ?_
      rotate_left
      · intro J0 hJ0
        c0_hsplit
        · c0_hfast; exact hJ0 (64#32, ()) m2 rfl
        · c0_hfast; exact hJ0 (32#32, ()) m2 rfl
      · intro _ f0 m_a hm_a
        rw [hm_a] at *
        c0_hfast_nogrp
        let fl_a := s2.core.flags.set (BitVec.setWidth 64 (l0 >>> (1 : Nat))).toNat
          ((s2.core.flags[(BitVec.setWidth 64 (l0 >>> (1 : Nat))).toNat]'hv0_lt) ||| 8#32 |||
            16#32 ||| f0.1)
        have hfl_a_len : fl_a.length = c.max_vars := by simp [fl_a, hlen2.core_ok.flags_len]
        have hv1_a : (BitVec.setWidth 64 (l1 >>> (1 : Nat))).toNat < fl_a.length := by
          have := hlen2.core_ok.cur_vars_le
          have hcv2 : s2.core.cur_vars = s.core.cur_vars := rfl
          rw [hfl_a_len, zext_toNat _ (by decide), bv32_lshr1]; omega
        refine wp_join_group (ts := [i32])
          (fun _ m_b =>
            (FullMem c { s2 with core := { s2.core with flags := fl_a } } ⋆ R) m_b) ?_ ?_
        rotate_left
        · intro J1 hJ1
          c0_hsplit
          · c0_hfast; exact hJ1 (64#32, ()) _ (by assumption)
          · c0_hfast; exact hJ1 (32#32, ()) _ (by assumption)
        · intro _ f1 m_b hm_b
          c0_hfast
          let fl_b := fl_a.set (BitVec.setWidth 64 (l1 >>> (1 : Nat))).toNat
            ((fl_a[(BitVec.setWidth 64 (l1 >>> (1 : Nat))).toNat]'hv1_a) ||| 8#32 ||| 16#32 |||
              f1.1)
          have hfl_b_len : fl_b.length = c.max_vars := by simp [fl_b, hfl_a_len]
          exact hQ 0xFFFFFFFE#64 fl_b wvec2 wstk2 wlen2 wu2 (s.core.num_binary + 1#64) wsort2 _
            (Or.inr rfl) (hfin_post fl_b hfl_b_len).1 (hfin_post fl_b hfl_b_len).2
            (by assumption)
    · -- `push2` failed: `full_watch_pop_c0` rollback
      obtain ⟨_, _, hsz1, hpre1, _, _⟩ := hok1t rfl
      have ht1_1 : (s1.core.tmp[1]'htm1_gt1) = l1 := rfl
      have ht0_0 : (s.core.tmp[0]'htm_gt0) = l0 := rfl
      have hsz1' : fullWatchSize s1 l0.toNat = fullWatchSize s l0.toNat + 1 := by
        simpa [BitVec.toNat_ofNat] using hsz1
      have hsz2_l0 : fullWatchSize s2 l0.toNat = fullWatchSize s l0.toNat + 1 ∧
          ∀ k < fullWatchSize s l0.toNat,
            s2.core.wstk[fullWatchOff s2 l0.toNat + k]? =
              s.core.wstk[fullWatchOff s l0.toNat + k]? := by
        by_cases heql : l0.toNat = l1.toNat
        · have hs2' := (hok2f hc).1 (by dsimp only [s1]; exact hl1_lt)
          change fullWatchSize s2 (s1.core.tmp[1]'htm1_gt1).toNat =
            fullWatchSize s1 (s1.core.tmp[1]'htm1_gt1).toNat ∧
            ∀ k < fullWatchSize s1 (s1.core.tmp[1]'htm1_gt1).toNat,
              s2.core.wstk[fullWatchOff s2 (s1.core.tmp[1]'htm1_gt1).toNat + k]? =
                s1.core.wstk[fullWatchOff s1 (s1.core.tmp[1]'htm1_gt1).toNat + k]? at hs2'
          rw [ht1_1, ← heql] at hs2'
          exact ⟨hs2'.1.trans hsz1', fun k hk =>
            (hs2'.2 k (by rw [hsz1']; exact Nat.lt_succ_of_lt hk)).trans (hpre1 k hk)⟩
        · have hne' : l0.toNat ≠ (s1.core.tmp[1]'htm1_gt1).toNat := by
            rw [ht1_1]; exact heql
          obtain ⟨hs2, hk2⟩ := hoth2 l0.toNat (by dsimp only [s1]; exact hl0_lt) hne'
          change fullWatchSize s2 l0.toNat = fullWatchSize s1 l0.toNat at hs2
          change ∀ k < fullWatchSize s1 l0.toNat,
            s2.core.wstk[fullWatchOff s2 l0.toNat + k]? =
              s1.core.wstk[fullWatchOff s1 l0.toNat + k]? at hk2
          exact ⟨hs2.trans hsz1', fun k hk =>
            (hk2 k (by rw [hsz1']; exact Nat.lt_succ_of_lt hk)).trans (hpre1 k hk)⟩
      have hs2_t0 : s2.core.tmp[0]'htm2_gt0 = l0 := rfl
      c0_call hPop
      refine ⟨c, s2, R, rfl, hlen2, hlay2, by simpa [BitVec.toNat_ofNat] using hl0_lt, by decide,
        by change 1 ≤ fullWatchSize s2 (s2.core.tmp[0]'htm2_gt0).toNat
           rw [hs2_t0, hsz2_l0.1]; exact Nat.le_add_left 1 _, hm2, ?_⟩
      intro wvec3 wstk3 wu3 m3 s3 hlen3 hlay3 hoth3 hoff3 hsz3 hslice3 hm3
      simp only [BitVec.toNat_ofNat] at hsz3 hslice3 hoth3
      rw [hs2_t0] at hsz3 hslice3 hoth3
      have hoth3' : ∀ l < 2 * s.core.cur_vars, l ≠ l0.toNat →
          fullWatchSizeCore s3.core l = fullWatchSizeCore s2.core l ∧
          ∀ j < fullWatchSizeCore s2.core l,
            s3.core.wstk[fullWatchOffCore s3.core l + j]? =
              s2.core.wstk[fullWatchOffCore s2.core l + j]? := fun l hl hne => by
        obtain ⟨_, hs3, hk3⟩ := hoth3 l (by dsimp only [s2, s1]; exact hl) hne
        exact ⟨hs3, hk3⟩
      have hsz3_sub : fullWatchSize s3 l0.toNat = fullWatchSize s l0.toNat := by
        change fullWatchSize s3 l0.toNat = fullWatchSize s2 l0.toNat - 1 at hsz3
        rw [hsz3, hsz2_l0.1, Nat.add_sub_cancel]
      have hwat3 : ModeWatchesInv F_cur s3.core :=
        FullM7V2Robust.modeWatchesInv_of_pop hw.watches hwat2 hlay3 rfl rfl rfl rfl
          (fun _ hr => hr) (fun _ hr => hr) hl0_lt
          ⟨hsz3_sub, fun k hk =>
            (hslice3 k (by
              change fullWatchSize s2 l0.toNat - 1 > k
              rw [hsz2_l0.1, Nat.add_sub_cancel]; exact hk)).trans (hsz2_l0.2 k hk)⟩
          hoth3'
      have hw3 : FullWitnessInv c F0 F_cur s3.core :=
        FullAssignAddSpecs.watchUpdate_preserves_witness hw hwat3
      c0_hfast
      exact hQ 0xFFFFFFFF#64 s.core.flags wvec3 wstk3 wlen2 wu3 s.core.num_binary wsort2 m3
        (Or.inl rfl) hlen3 hw3 hm3
  · exact hQ 0xFFFFFFFF#64 s.core.flags wvec1 wstk1 wlen1 wu1 s.core.num_binary wsort1 m1
      (Or.inl rfl) hlen1 hw1 hm1

private theorem s13_add_clause_large_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hAlloc : ∀ args m Q X, fullAllocClSpec args m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] args m Q X)
    (hPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hPop : ∀ args m Q X, step13WatchPopC0Spec args m Q X →
      Γ "full_watch_pop_c0" [i64, i32, i32] [] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {len glue : Val i32} {red : Val .bool}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core) (hdm : s.core.dense_mode = 0#64)
    (hge3 : 3 ≤ len.toNat) (hlen_mv : len.toNat ≤ c.max_vars)
    (hlits_lt : ∀ l ∈ (s.core.tmp.take len.toNat).map BitVec.toNat, l < 2 * s.core.cur_vars)
    (hnd_tmp : ((s.core.tmp.take len.toNat).map fun x => x.toNat / 2).Nodup)
    (hent_cl : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take len.toNat).map BitVec.toNat)))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ r arena' alen' wvec' wstk' wlen' wusable' fred' ni' nr' wsort' m',
      let s' : FullState :=
        { s with
          core := { s.core with arena := arena', arena_len := alen', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wusable',
                                first_reducible := fred', num_irred := ni', num_redundant := nr' }
          scratch := { s.scratch with wsort := wsort' } }
      (r = 0xFFFFFFFF#64 ∨ r = BitVec.ofNat 64 s.core.arena_len) →
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      (∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s') →
      (FullArenaVarsNodup s → FullArenaVarsNodup s') →
      (r = BitVec.ofNat 64 s.core.arena_len → alen' = s.core.arena_len + 3 + len.toNat ∧
        s.core.arena_len ∈ fullArenaClauseRefs s' ∧
        fullArenaClauseGarb s' s.core.arena_len = false ∧
        fullArenaClauseLits s' s.core.arena_len =
          (s.core.tmp.take len.toNat).map BitVec.toNat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    Func.wp Γ FullFidelityStep13S5BVAFactor.full_add_clause_body (c.hdr, len, glue, red, ())
      m Q X := by
  have hmv := c.hmaxv; have har := c.harena; have hwcap := c.hwcap
  unfold dimacsBound at hmv har hwcap; have hco := hlen.core_ok
  have hs_alen_lt32 : s.core.arena_len < 0xFFFFFFFF := by have := hco.arena_len_le; omega
  have hs_alen_lt64 : s.core.arena_len < 2 ^ 64 := by omega
  have hcref_ne : BitVec.ofNat 64 s.core.arena_len ≠ 0xFFFFFFFF#64 := fun he => by
    have h := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs_alen_lt64] at h
    change s.core.arena_len = 0xFFFFFFFF at h; omega
  unfold Func.wp FullFidelityStep13S5BVAFactor.full_add_clause_body; dsimp only
  c0_hfast
  · exfalso; have h2 : len = 2#32 := by assumption
    rw [h2] at hge3; revert hge3; decide
  · exfalso
    have hlt : len.toNat < (3#32 : BitVec 32).toNat := by assumption
    change len.toNat < 3 at hlt; omega
  · c0_call hAlloc
    refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
    split
    · c0_hfast
      · exact hQ 0xFFFFFFFF#64 s.core.arena s.core.arena_len s.core.wvec s.core.wstk
          s.core.wlen s.core.wusable s.core.first_reducible s.core.num_irred
          s.core.num_redundant s.scratch.wsort m (Or.inl rfl) hlen hw (fun _ h => h) id
          (fun hc => absurd hc.symm hcref_ne) hm
      · exact absurd rfl (by assumption)
    · intro arena1 m1 alen1 s1_st hlen1 hhold1 hnoshrk1 hnogarb1 _hred1 hsz1 hm1
      c0_hfast_nogrp
      try exact absurd (by assumption) hcref_ne
      refine wp_loop_group (ts := [i32]) (fun r (iv, ()) mc => ∃ i arena',
        i ≤ len.toNat ∧ r = len.toNat - i ∧ iv = BitVec.ofNat 32 i ∧
        arena'.length = c.arena_cap ∧
        (∀ k < s.core.arena_len + 3, arena'[k]? = arena1[k]?) ∧
        (∀ k < i, arena'[s.core.arena_len + 3 + k]? = s.core.tmp[k]?) ∧
        (FullMem c { s1_st with core := { s1_st.core with arena := arena' } } ⋆ R) mc) ?_ ?_
      · rintro L r ⟨iv, ⟨⟩⟩ mc ih ⟨i, arena', hile, rfl, rfl, harl, hpre, hcp, hmc⟩
        c0_hfast
        · have hilt32 : i < 2 ^ 32 := Nat.lt_of_le_of_lt hile len.isLt
          have hilt : i < len.toNat := by
            have h := (by assumption : i % 2 ^ 32 < len.toNat)
            rwa [Nat.mod_eq_of_lt hilt32] at h
          have htm_bd_i : i <
              ({ s1_st with core := { s1_st.core with arena := arena' } }).core.tmp.length := by
            simp [s1_st, hco.tmp_len_arr]; omega
          have har_bd : s.core.arena_len + 3 + i < arena'.length := by
            have := hlen1.core_ok.arena_len_le; simp [s1_st, alen1] at this; omega
          have hidx_eq : ((BitVec.ofNat 32 i).setWidth 64) * 4 = BitVec.ofNat 64 (4 * i) := by
            rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega)]; bv_omega
          have hidx2 : c.pArena + ((BitVec.ofNat 64 s.core.arena_len + (3 : BitVec 64) +
              BitVec.ofNat 64 i) * 4) =
              c.pArena + BitVec.ofNat 64 (4 * (s.core.arena_len + 3 + i)) := by bv_omega
          c0_hfast
          let lit_i := s.core.tmp[i]'(by rw [hco.tmp_len_arr]; omega)
          have hl_tmp_lt : (BitVec.setWidth 64 (BitVec.ofNat 32 i)).toNat <
              ({ s1_st with core := { s1_st.core with arena := arena' } }).core.tmp.length := by
            simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt hilt32, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
            exact htm_bd_i
          have har_idx_lt : (BitVec.ofNat 64 s.core.arena_len + 3 +
              BitVec.setWidth 64 (BitVec.ofNat 32 i)).toNat < arena'.length := by
            simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
              show BitVec.toNat (3 : BitVec 64) = 3 from rfl]
            repeat rw [Nat.mod_eq_of_lt (by omega)]
            exact har_bd
          c0_hfast
          have hi1 : BitVec.ofNat 32 i + 1 = BitVec.ofNat 32 (i + 1) := by bv_omega
          rw [hi1]
          refine ih (len.toNat - (i + 1)) (BitVec.ofNat 32 (i + 1), ()) _ (by omega)
            ⟨i + 1, _, by omega, rfl, rfl, ?_, ?_, ?_, (by assumption)⟩
          · rw [List.length_set, harl]
          · intro k hk
            rw [List.getElem?_set_ne (by
              simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                show BitVec.toNat (3 : BitVec 64) = 3 from rfl]
              repeat rw [Nat.mod_eq_of_lt (by omega)]
              omega)]
            exact hpre k hk
          · intro k hk
            have heq_idx : (BitVec.ofNat 64 s.core.arena_len + 3 +
                BitVec.setWidth 64 (BitVec.ofNat 32 i)).toNat = s.core.arena_len + 3 + i := by
              simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                show BitVec.toNat (3 : BitVec 64) = 3 from rfl]
              repeat rw [Nat.mod_eq_of_lt (by omega)]
            by_cases hki : k = i
            · rw [hki, heq_idx, List.getElem?_set_self har_bd]
              change some (s1_st.core.tmp[
                (BitVec.setWidth 64 (BitVec.ofNat 32 i)).toNat]'hl_tmp_lt) = s.core.tmp[i]?
              rw [List.getElem?_eq_getElem (by rw [hco.tmp_len_arr]; omega)]
              congr 1; simp only [s1_st, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt hilt32, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
            · rw [heq_idx, List.getElem?_set_ne (by omega)]; exact hcp k (by omega)
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
          have hrefs_cp : fullArenaClauseRefsCore s_cp.core =
              fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
            fullArenaClauseRefsCore_append hw.arena hge3 rfl hhold_cp hnoshrk_cp hsz_cp
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
                hsz_cp, harl, hco.tmp_len_arr]; omega
            · intro k hk1 _
              have hk_lt : k < len.toNat := by
                simp [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, s_cp,
                  hsz_cp] at hk1; omega
              have hcpk := hcp k hk_lt
              rw [List.getElem?_eq_getElem (by omega),
                List.getElem?_eq_getElem (by rw [hco.tmp_len_arr]; omega)] at hcpk
              simp [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, s_cp,
                hsz_cp, Option.some.inj hcpk]
          have hcref32_ne : BitVec.ofNat 32 s.core.arena_len ≠ 0xFFFFFFFF#32 := fun he => by
            have ht := congrArg BitVec.toNat he; rw [bv32_ofNat_toNat (by omega)] at ht
            change s.core.arena_len = 0xFFFFFFFF at ht; omega
          have hcref32_lt : (BitVec.ofNat 32 s.core.arena_len).toNat < 0x80000000 := by
            rw [bv32_ofNat_toNat (by omega)]; omega
          have htm_cp0 : 0 < s_cp.core.tmp.length := by simp [s_cp, s1_st, hco.tmp_len_arr]; omega
          have htm_cp1 : 1 < s_cp.core.tmp.length := by simp [s_cp, s1_st, hco.tmp_len_arr]; omega
          have hl0_lt : (s.core.tmp[0]'htm_cp0).toNat < 2 * s.core.cur_vars := by
            have hlt := hlits_lt (s.core.tmp[0]'htm_cp0).toNat
              (List.mem_map.mpr ⟨s.core.tmp[0]'htm_cp0,
                List.mem_iff_getElem.mpr ⟨0, by simp [hco.tmp_len_arr]; omega, by simp⟩, rfl⟩)
            simpa using hlt
          have hl1_lt : (s.core.tmp[1]'htm_cp1).toNat < 2 * s.core.cur_vars := by
            have hlt := hlits_lt (s.core.tmp[1]'htm_cp1).toNat
              (List.mem_map.mpr ⟨s.core.tmp[1]'htm_cp1,
                List.mem_iff_getElem.mpr ⟨1, by simp [hco.tmp_len_arr]; omega, by simp⟩, rfl⟩)
            simpa using hlt
          c0_hfast; rw [bv64_trunc32_ofNat (by omega)]; c0_call hPush
          refine ⟨c, s_cp, R, rfl, hlen_cp, hwat_cp.layout, (fun hc => absurd hc (by decide)),
            (fun _ => ⟨bv32_mask_ne_sent _, hcref32_ne⟩), hmc, ?_⟩
          intro ok1 wvec1 wstk1 wlen1 wu1 wsort1 m1 s1 hlen1' hlay1 hoth1 hok1t hok1f hm1'
          have htm_s1_0 : 0 < s1.core.tmp.length := by
            simp [s1, s_cp, s1_st, hlen1'.core_ok.tmp_len_arr]; omega
          have htm_s1_1 : 1 < s1.core.tmp.length := by
            simp [s1, s_cp, s1_st, hlen1'.core_ok.tmp_len_arr]; omega
          have hrefs1 : fullArenaClauseRefsCore s1.core = fullArenaClauseRefsCore s_cp.core := rfl
          have hwat1 : ModeWatchesInv F_cur s1.core :=
            FullAssignAddSpecs.fullWatchPush_preserves_modeWatchesInv
              hwat_cp hlay1 rfl rfl (fun r hr => hrefs1 ▸ hr)
              (fun hc => absurd hc (by decide)) (fun _ => ⟨bv32_mask_flag0 _,
                fun hdm' => absurd hdm hdm', hcref32_lt,
                hrefs1 ▸ hrefs_cp ▸ List.mem_append_right _
                  (by simp [bv32_ofNat_toNat (by omega : s.core.arena_len < 2 ^ 32)])⟩)
              hoth1 hok1t (fun h => (hok1f h).1)
          c0_hfast
          · rw [bv64_trunc32_ofNat (by omega)]; c0_call hPush
            refine ⟨c, s1, R, rfl, hlen1', hlay1, (fun hc => absurd hc (by decide)),
              (fun _ => ⟨bv32_mask_ne_sent _, hcref32_ne⟩), hm1', ?_⟩
            intro ok2 wvec2 wstk2 wlen2 wu2 wsort2 m2 s2 hlen2 hlay2 hoth2 hok2t hok2f hm2
            have hrefs2 : fullArenaClauseRefsCore s2.core = fullArenaClauseRefsCore s1.core := rfl
            have hwat2 : ModeWatchesInv F_cur s2.core :=
              FullAssignAddSpecs.fullWatchPush_preserves_modeWatchesInv
                hwat1 hlay2 rfl rfl (fun r hr => hrefs2 ▸ hr)
                (fun hc => absurd hc (by decide)) (fun _ => ⟨bv32_mask_flag0 _,
                  fun hdm' => absurd hdm hdm', hcref32_lt,
                  hrefs2 ▸ hrefs1 ▸ hrefs_cp ▸ List.mem_append_right _
                    (by simp [bv32_ofNat_toNat (by omega : s.core.arena_len < 2 ^ 32)])⟩)
                hoth2 hok2t (fun h => (hok2f h).1)
            have hfin : ∀ fred' ni' nr' mf,
                (FullMem c (s13AddClauseState s len.toNat arena' wvec2 wstk2 wlen2 wu2
                  fred' ni' nr' wsort2) ⋆ R) mf → Q (BitVec.ofNat 64 s.core.arena_len, ()) mf :=
              fun fred' ni' nr' mf hm_f => by
                let s_fin := s13AddClauseState s len.toNat arena' wvec2 wstk2 wlen2 wu2
                  fred' ni' nr' wsort2
                have hlen_f : s_fin.LengthsOk c :=
                  { core_ok := { hlen2.core_ok with arena_len_arr := by simp [s_fin, harl] }
                    scratch_ok := hlen2.scratch_ok }
                have hrefs_f0 : fullArenaClauseRefsCore s_fin.core =
                    fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
                  fullArenaClauseRefsCore_append hw.arena hge3 rfl hhold_cp hnoshrk_cp hsz_cp
                have hwat_f : ModeWatchesInv F_cur s_fin.core :=
                  hwat2.with_wstk rfl rfl rfl rfl rfl (fun r hr => by
                    have h1 : fullArenaClauseRefsCore s2.core =
                        fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
                      hrefs2.trans (hrefs1.trans hrefs_cp)
                    rwa [hrefs_f0, ← h1])
                obtain ⟨hw_f, hrefs_f, hhold_f⟩ :=
                  FullAssignAddSpecs.addEntailedClause_preserves_witness
                    hlen hw hlen_f hge3 hlits_lt hent_cl hhold_cp hnoshrk_cp hsz_cp hlits_cp hwat_f
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
                      unfold fullArenaClauseLits; rw [(hhold_f r hr).2]; exact hnd r hr hng
                    · unfold fullArenaClauseLits
                      rw [show fullArenaClauseLitsCore s_fin.core s.core.arena_len =
                          (s.core.tmp.take len.toNat).map BitVec.toNat from hlits_cp, List.map_map]
                      exact hnd_tmp
                exact hQ (BitVec.ofNat 64 s.core.arena_len) arena' alen1 wvec2 wstk2 wlen2 wu2
                  fred' ni' nr' wsort2 mf (Or.inr rfl) hlen_f hw_f
                  (fun r hr => by
                    change r ∈ fullArenaClauseRefsCore s_fin.core
                    rw [hrefs_f]; exact List.mem_append_left _ hr)
                  hnd_f (fun _ => ⟨rfl, by
                    change s.core.arena_len ∈ fullArenaClauseRefsCore s_fin.core
                    rw [hrefs_f]; exact List.mem_append_right _ (by simp), hgarb_f, hlits_cp⟩)
                  hm_f
            c0_hfast
            · exact hfin (BitVec.ofNat 64 s.core.arena_len) s.core.num_irred
                (s.core.num_redundant + 1#64) _ (by assumption)
            · exact hfin s.core.first_reducible s.core.num_irred
                (s.core.num_redundant + 1#64) _ (by assumption)
            · exact hfin s.core.first_reducible (s.core.num_irred + 1#64)
                s.core.num_redundant _ (by assumption)
            · obtain ⟨_, _, hsz1, hpre1, _, _⟩ := hok1t (by assumption)
              have hsz1_s : fullWatchSize s1 (s.core.tmp[0]'htm_cp0).toNat =
                  fullWatchSize s (s.core.tmp[0]'htm_cp0).toNat + 2 := hsz1
              have hpre1_s : ∀ k < fullWatchSize s (s.core.tmp[0]'htm_cp0).toNat,
                  s1.core.wstk[fullWatchOff s1 (s.core.tmp[0]'htm_cp0).toNat + k]? =
                    s.core.wstk[fullWatchOff s (s.core.tmp[0]'htm_cp0).toNat + k]? := hpre1
              have hsz2_l0 : fullWatchSize s2 (s.core.tmp[0]'htm_cp0).toNat =
                  fullWatchSize s (s.core.tmp[0]'htm_cp0).toNat + 2 ∧
                  ∀ k < fullWatchSize s (s.core.tmp[0]'htm_cp0).toNat,
                    s2.core.wstk[fullWatchOff s2 (s.core.tmp[0]'htm_cp0).toNat + k]? =
                      s.core.wstk[fullWatchOff s (s.core.tmp[0]'htm_cp0).toNat + k]? := by
                by_cases heql : (s.core.tmp[0]'htm_cp0).toNat = (s.core.tmp[1]'htm_cp1).toNat
                · obtain ⟨hs2, hk2⟩ := (hok2f hc).1 (by dsimp only [s1, s_cp, s1_st]; exact hl1_lt)
                  have ht1_1 : (s1.core.tmp[1]'htm_s1_1) = s.core.tmp[1]'htm_cp1 := rfl
                  change fullWatchSize s2 (s1.core.tmp[1]'htm_s1_1).toNat =
                    fullWatchSize s1 (s1.core.tmp[1]'htm_s1_1).toNat at hs2
                  change ∀ k < fullWatchSize s1 (s1.core.tmp[1]'htm_s1_1).toNat,
                    s2.core.wstk[fullWatchOff s2 (s1.core.tmp[1]'htm_s1_1).toNat + k]? =
                      s1.core.wstk[fullWatchOff s1 (s1.core.tmp[1]'htm_s1_1).toNat + k]? at hk2
                  rw [ht1_1, ← heql] at hs2 hk2
                  exact ⟨hs2.trans hsz1_s,
                    fun k hk => (hk2 k (by rw [hsz1_s]; omega)).trans (hpre1_s k hk)⟩
                · obtain ⟨hs2, hk2⟩ := hoth2 (s.core.tmp[0]'htm_cp0).toNat
                    (by dsimp only [s1, s_cp, s1_st]; exact hl0_lt) heql
                  change fullWatchSize s2 (s.core.tmp[0]'htm_cp0).toNat =
                    fullWatchSize s1 (s.core.tmp[0]'htm_cp0).toNat at hs2
                  change ∀ k < fullWatchSize s1 (s.core.tmp[0]'htm_cp0).toNat,
                    s2.core.wstk[fullWatchOff s2 (s.core.tmp[0]'htm_cp0).toNat + k]? =
                      s1.core.wstk[fullWatchOff s1 (s.core.tmp[0]'htm_cp0).toNat + k]? at hk2
                  exact ⟨hs2.trans hsz1_s,
                    fun k hk => (hk2 k (by rw [hsz1_s]; omega)).trans (hpre1_s k hk)⟩
              have hsz2_oth : ∀ l < 2 * s.core.cur_vars,
                  l ≠ (s.core.tmp[0]'htm_cp0).toNat →
                  fullWatchSize s2 l = fullWatchSize s l ∧
                  ∀ k < fullWatchSize s l,
                    s2.core.wstk[fullWatchOff s2 l + k]? =
                      s.core.wstk[fullWatchOff s l + k]? := fun l hl hne => by
                obtain ⟨hs1o, hk1o⟩ := hoth1 l (by dsimp only [s_cp, s1_st]; exact hl) hne
                change fullWatchSize s1 l = fullWatchSize s l at hs1o
                change ∀ k < fullWatchSize s l,
                  s1.core.wstk[fullWatchOff s1 l + k]? = s.core.wstk[fullWatchOff s l + k]? at hk1o
                by_cases heql : l = (s.core.tmp[1]'htm_cp1).toNat
                · subst heql
                  obtain ⟨hs2o, hk2o⟩ := (hok2f hc).1 (by dsimp only [s1, s_cp, s1_st]; exact hl)
                  have ht1_1 : (s1.core.tmp[1]'htm_s1_1) = s.core.tmp[1]'htm_cp1 := rfl
                  change fullWatchSize s2 (s1.core.tmp[1]'htm_s1_1).toNat =
                    fullWatchSize s1 (s1.core.tmp[1]'htm_s1_1).toNat at hs2o
                  change ∀ k < fullWatchSize s1 (s1.core.tmp[1]'htm_s1_1).toNat,
                    s2.core.wstk[fullWatchOff s2 (s1.core.tmp[1]'htm_s1_1).toNat + k]? =
                      s1.core.wstk[fullWatchOff s1 (s1.core.tmp[1]'htm_s1_1).toNat + k]? at hk2o
                  rw [ht1_1] at hs2o hk2o
                  exact ⟨hs2o.trans hs1o,
                    fun k hk => (hk2o k (by rw [hs1o]; exact hk)).trans (hk1o k hk)⟩
                · obtain ⟨hs2o, hk2o⟩ := hoth2 l (by dsimp only [s1, s_cp, s1_st]; exact hl) heql
                  change fullWatchSize s2 l = fullWatchSize s1 l at hs2o
                  change ∀ k < fullWatchSize s1 l,
                    s2.core.wstk[fullWatchOff s2 l + k]? =
                      s1.core.wstk[fullWatchOff s1 l + k]? at hk2o
                  exact ⟨hs2o.trans hs1o,
                    fun k hk => (hk2o k (by rw [hs1o]; exact hk)).trans (hk1o k hk)⟩
              have htm2_gt0 : 0 < s2.core.tmp.length := by rw [hlen2.core_ok.tmp_len_arr]; omega
              c0_call hPop
              refine ⟨c, s2, R, rfl, hlen2, hlay2,
                by dsimp only [s2, s1, s_cp, s1_st]; exact hl0_lt,
                by decide,
                by dsimp only [s2, s1, s_cp, s1_st]; simp only [BitVec.toNat_ofNat];
                   rw [hsz2_l0.1]; omega,
                hm2, ?_⟩
              intro wvec3 wstk3 wu3 m3 s3 hlen3 hlay3 hoth3 hoff3 hsz3 hslice3 hm3
              have hsz3_2 : fullWatchSize s3 (s.core.tmp[0]'htm_cp0).toNat =
                  fullWatchSize s2 (s.core.tmp[0]'htm_cp0).toNat - 2 := hsz3
              have hslice3_2 : ∀ idx < fullWatchSize s2 (s.core.tmp[0]'htm_cp0).toNat - 2,
                  s3.core.wstk[fullWatchOff s3 (s.core.tmp[0]'htm_cp0).toNat + idx]? =
                    s2.core.wstk[fullWatchOff s2 (s.core.tmp[0]'htm_cp0).toNat + idx]? := hslice3
              c0_hfast
              let s_r2 : FullState :=
                { s with
                  core := { s.core with arena := arena', wvec := wvec3, wstk := wstk3,
                                        wlen := wlen2, wusable := wu3 }
                  scratch := { s.scratch with wsort := wsort2 } }
              have hlen_r2 : s_r2.LengthsOk c :=
                { core_ok := { hlen3.core_ok with
                    arena_len_le := by
                      change s.core.arena_len ≤ c.arena_cap; exact hco.arena_len_le }
                  scratch_ok := hlen3.scratch_ok }
              have hlay_r2 : WatchStackLayout s_r2.core := hlay3.with_wstk rfl rfl rfl rfl
              have hpres_r2 : ∀ l < 2 * s.core.cur_vars,
                  fullWatchSizeCore s_r2.core l = fullWatchSizeCore s.core l ∧
                  ∀ idx < fullWatchSizeCore s.core l,
                    wstk3[fullWatchOffCore s_r2.core l + idx]? =
                      s.core.wstk[fullWatchOffCore s.core l + idx]? := fun l hl => by
                by_cases hll0 : l = (s.core.tmp[0]'htm_cp0).toNat
                · subst hll0
                  refine ⟨by
                      change fullWatchSize s3 (s.core.tmp[0]'htm_cp0).toNat =
                        fullWatchSize s (s.core.tmp[0]'htm_cp0).toNat
                      rw [hsz3_2, hsz2_l0.1, Nat.add_sub_cancel],
                    fun idx hidx =>
                      (hslice3_2 idx (by rw [hsz2_l0.1, Nat.add_sub_cancel]; exact hidx)).trans
                        (hsz2_l0.2 idx hidx)⟩
                · obtain ⟨_, hs32, hk32⟩ :=
                    hoth3 l (by dsimp only [s2, s1, s_cp, s1_st]; exact hl) hll0
                  obtain ⟨hs20, hk20⟩ := hsz2_oth l hl hll0
                  change fullWatchSize s2 l = fullWatchSize s l at hs20
                  change ∀ idx < fullWatchSize s l,
                    s2.core.wstk[fullWatchOff s2 l + idx]? =
                      s.core.wstk[fullWatchOff s l + idx]? at hk20
                  exact ⟨hs32.trans hs20,
                    fun idx hidx => (hk32 idx (by rw [hs20]; exact hidx)).trans (hk20 idx hidx)⟩
              obtain ⟨hw_r2, hrefs_r2, hnd_r2⟩ := s13AddClauseRollback_preserves_witness
                hlen hw hlen_r2 hlay_r2 hhold_cp hpres_r2
              exact hQ 0xFFFFFFFF#64 arena' s.core.arena_len wvec3 wstk3 wlen2 wu3
                s.core.first_reducible s.core.num_irred s.core.num_redundant wsort2 m
                (Or.inl rfl) hlen_r2 hw_r2 (fun r hr => hrefs_r2 ▸ hr) hnd_r2
                (fun hc' => absurd hc'.symm hcref_ne)
                (by simpa only [s_r2, s3, s2, s1, s_cp, s1_st] using hm)
          · c0_hfast
            let s_r1 : FullState :=
              { s with
                core := { s.core with arena := arena', wvec := wvec1, wstk := wstk1,
                                      wlen := wlen1, wusable := wu1 }
                scratch := { s.scratch with wsort := wsort1 } }
            have hlen_r1 : s_r1.LengthsOk c :=
              { core_ok := { hlen1'.core_ok with
                  arena_len_le := by change s.core.arena_len ≤ c.arena_cap; exact hco.arena_len_le }
                scratch_ok := hlen1'.scratch_ok }
            have hlay_r1 : WatchStackLayout s_r1.core := hlay1.with_wstk rfl rfl rfl rfl
            have hpres_r1 : ∀ l < 2 * s.core.cur_vars,
                fullWatchSizeCore s_r1.core l = fullWatchSizeCore s.core l ∧
                ∀ idx < fullWatchSizeCore s.core l,
                  wstk1[fullWatchOffCore s_r1.core l + idx]? =
                    s.core.wstk[fullWatchOffCore s.core l + idx]? := fun l hl => by
              by_cases hll0 : l = (s.core.tmp[0]'htm_cp0).toNat
              · subst hll0
                exact (hok1f hc).1 (by simpa [s_cp, s1_st, BitVec.toNat_ofNat] using hl0_lt)
              · exact hoth1 l (by dsimp only [s_cp, s1_st]; omega) hll0
            obtain ⟨hw_r1, hrefs_r1, hnd_r1⟩ := s13AddClauseRollback_preserves_witness
              hlen hw hlen_r1 hlay_r1 hhold_cp hpres_r1
            exact hQ 0xFFFFFFFF#64 arena' s.core.arena_len wvec1 wstk1 wlen1 wu1
              s.core.first_reducible s.core.num_irred s.core.num_redundant wsort1 m
              (Or.inl rfl) hlen_r1 hw_r1 (fun r hr => hrefs_r1 ▸ hr) hnd_r1
              (fun hc' => absurd hc'.symm hcref_ne)
              (by simpa only [s_r1, s1, s_cp, s1_st] using hm)
      · intro J hJ; c0_hfast
        exact hJ len.toNat (0#32, ()) m1 ⟨0, arena1, Nat.zero_le _, Nat.sub_zero _, rfl,
          hlen1.core_ok.arena_len_arr, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _), hm1⟩

theorem full_add_clause_s5_wp (Γ : Env)
    (hAlloc : ∀ args m Q X, fullAllocClSpec args m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] args m Q X)
    (hPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hPop : ∀ args m Q X, step13WatchPopC0Spec args m Q X →
      Γ "full_watch_pop_c0" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, step13AddClauseSpec args m Q X →
      Func.wp Γ FullFidelityStep13S5BVAFactor.full_add_clause_body args m Q X := by
  rintro ⟨h, len, glue, red, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hlen_bd, hcl_bd, hm, hQ⟩
  by_cases h2 : len = 2#32
  · subst h2
    simp only [show (2#32 : BitVec 32).toNat = 2 from rfl,
      show ¬ (2 < 2) by omega, ↓reduceIte] at hQ hcl_bd hlen_bd
    obtain ⟨hlits_lt, _, hent2⟩ := hcl_bd (by omega)
    exact s13_add_clause_bin_wp hPush hPop hlen hw hlen_bd hlits_lt hent2 hm hQ
  · have hne2 : len.toNat ≠ 2 := fun he => h2 (BitVec.eq_of_toNat_eq he)
    by_cases hlt3 : len.toNat < 3
    · have hlt2 : len.toNat < 2 := by omega
      simp only [hlt2, ↓reduceIte] at hQ
      unfold Func.wp FullFidelityStep13S5BVAFactor.full_add_clause_body; dsimp only
      c0_hfast
      · exact absurd (by assumption : len = 2#32) h2
      · exact hQ
      · exfalso
        have hge : ¬ len.toNat < (3#32 : BitVec 32).toNat := by assumption
        change ¬ len.toNat < 3 at hge; omega
    · have hge3 : 3 ≤ len.toNat := by omega
      simp only [show ¬ (len.toNat < 2) by omega, hne2, ↓reduceIte] at hQ
      obtain ⟨hlits_lt, hnd_tmp, hent_cl⟩ := hcl_bd (by omega)
      exact s13_add_clause_large_wp hAlloc hPush hPop hlen hw hdm hge3 hlen_bd hlits_lt hnd_tmp
        hent_cl hm hQ

/-! ## 4. `full_delete_binary` (`step13DeleteBinarySpec`) -/

theorem full_delete_binary_s5_wp (Γ : Env)
    (hdbs : ∀ a m Q X, Full.fullDeleteBinSideSpec a m Q X →
      Γ "full_delete_bin_side" [i64, i32, i32] [] a m Q X) :
    ∀ args m Q X, step13DeleteBinarySpec args m Q X →
      Func.wp Γ FullFidelityStep13S5BVAFactor.full_delete_binary_body args m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, ha_mv, hb_mv, hm, hQ⟩
  unfold Func.wp FullFidelityStep13S5BVAFactor.full_delete_binary_body; dsimp only
  c0_hfast
  c0_call hdbs
  refine ⟨c, s, R, rfl, hlen, fun ha => hlay.bounds a.toNat ha, hm, ?_⟩
  dsimp only
  intro wvec1 wstk1 wu1 m1 hlen1 _ _ _ _ _ hlay1_fn hmw1_fn hm1
  let s1 : FullState :=
    { s with core := { s.core with wvec := wvec1, wstk := wstk1, wusable := wu1 } }
  have hlay1 : WatchStackLayout s1.core := hlay1_fn hlay
  c0_call hdbs
  refine ⟨c, s1, R, rfl, hlen1, fun hb => hlay1.bounds b.toNat hb, hm1, ?_⟩
  dsimp only
  intro wvec2 wstk2 wu2 m2 hlen2 _ _ _ _ _ hlay2_fn hmw2_fn hm2
  let s2 : FullState :=
    { s with core := { s.core with wvec := wvec2, wstk := wstk2, wusable := wu2 } }
  have hlay2 : WatchStackLayout s2.core := hlay2_fn hlay1
  have ha_fl : (BitVec.setWidth 64 (a >>> (1 : Nat))).toNat < s2.core.flags.length := by
    rw [zext_toNat _ (by decide), bv32_lshr1, hlen2.core_ok.flags_len]; omega
  have hb_fl : (BitVec.setWidth 64 (b >>> (1 : Nat))).toNat < s2.core.flags.length := by
    rw [zext_toNat _ (by decide), bv32_lshr1, hlen2.core_ok.flags_len]; omega
  c0_hfast_nogrp
  refine wp_join_group (ts := [i32])
    (fun _ ma => (FullMem c s2 ⋆ R) ma) ?_ ?_
  rotate_left
  · intro Ja hJa
    c0_hsplit
    · c0_hfast; exact hJa (64#32, ()) _ (by assumption)
    · c0_hfast; exact hJa (32#32, ()) _ (by assumption)
  · intro _ p ma hma
    c0_hfast_nogrp
    let fl1 := s2.core.flags.set (BitVec.setWidth 64 (a >>> (1 : Nat))).toNat
      ((s2.core.flags[(BitVec.setWidth 64 (a >>> (1 : Nat))).toNat]'ha_fl) ||| 16#32 ||| p.1)
    have hfl1_len : fl1.length = c.max_vars := by simpa [fl1, s2, s1] using hlen2.core_ok.flags_len
    have hb_fl1 : (BitVec.setWidth 64 (b >>> (1 : Nat))).toNat < fl1.length := by
      rw [hfl1_len, zext_toNat _ (by decide), bv32_lshr1]; omega
    refine wp_join_group (ts := [i32])
      (fun _ mb => (FullMem c { s2 with core := { s2.core with flags := fl1 } } ⋆ R) mb) ?_ ?_
    rotate_left
    · intro Jb hJb
      c0_hsplit
      · c0_hfast; exact hJb (64#32, ()) _ (by assumption)
      · c0_hfast; exact hJb (32#32, ()) _ (by assumption)
    · intro _ q mb hmb
      let fl2 := fl1.set (BitVec.setWidth 64 (b >>> (1 : Nat))).toNat
        ((fl1[(BitVec.setWidth 64 (b >>> (1 : Nat))).toNat]'hb_fl1) ||| 16#32 ||| q.1)
      have hfl2_len : fl2.length = c.max_vars := by simpa [fl2] using hfl1_len
      have hlen_f : ({ s2 with core := { s2.core with flags := fl2 } } :
          FullState).LengthsOk c :=
        ⟨{ hlen2.core_ok with flags_len := hfl2_len }, hlen2.scratch_ok⟩
      c0_hfast
      · exact hQ fl2 wvec2 wstk2 wu2 (s2.core.num_binary - 1#64) _ ⟨{ hlen_f.core_ok with },
          hlen_f.scratch_ok⟩ (hlay2.with_wstk rfl rfl rfl rfl) (fun F_cur hmw =>
          (hmw2_fn F_cur (hmw1_fn F_cur hmw)).with_wstk rfl rfl rfl rfl rfl (fun _ r => r))
          (by assumption)
      · exact hQ fl2 wvec2 wstk2 wu2 s2.core.num_binary _ ⟨{ hlen_f.core_ok with },
          hlen_f.scratch_ok⟩ (hlay2.with_wstk rfl rfl rfl rfl) (fun F_cur hmw =>
          (hmw2_fn F_cur (hmw1_fn F_cur hmw)).with_wstk rfl rfl rfl rfl rfl (fun _ r => r))
          (by assumption)

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

end
