/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
public import LeanQbe.T.Examples.Kissat.Src.Vivify
import LeanQbe.T.Examples.Kissat.Proof.Vivify.InvArena
import LeanQbe.T.Examples.Kissat.Proof.Vivify.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Vivify Red-Refs Sort WP Proofs (`Proof.Vivify.WpSortFid`)

Parametric `(Γ : Env)` `Func.wp` proofs for:
1. `full_viv_sort2_fid_wp` (`Spec.fullVivSort2FidSpec`)
2. `full_viv_sort_fid_wp` (`Spec.fullVivSortFidSpec`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Vivify

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Vivify
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Vivify.VivTactics

private def sortState (s : FullState) (rri scri : List (BitVec 32)) : FullState :=
  { s with scratch := { s.scratch with red_refs := rri, scratch_buf := scri } }

@[simp] private theorem sortState_core (s : FullState) (rri scri : List (BitVec 32)) :
    (sortState s rri scri).core = s.core := rfl

@[simp] private theorem sortState_tarjan_reach (s : FullState) (rri scri : List (BitVec 32)) :
    (sortState s rri scri).scratch.tarjan_reach = s.scratch.tarjan_reach := rfl

@[simp] private theorem sortState_red_refs (s : FullState) (rri scri : List (BitVec 32)) :
    (sortState s rri scri).scratch.red_refs = rri := rfl

@[simp] private theorem sortState_scratch_buf (s : FullState) (rri scri : List (BitVec 32)) :
    (sortState s rri scri).scratch.scratch_buf = scri := rfl

private theorem sortState_self (s : FullState) :
    sortState s s.scratch.red_refs s.scratch.scratch_buf = s := by
  rcases s with ⟨core, scratch⟩; cases scratch; rfl

private theorem sortState_eq (s : FullState) (rr' scr' : List (BitVec 32)) :
    sortState s rr' scr' =
      { core := s.core,
        scratch := { s.scratch with red_refs := rr', scratch_buf := scr' } } := by
  rcases s with ⟨core, scratch⟩; cases scratch; rfl

private theorem sortState_set_red_refs (s : FullState) (rri scri : List (BitVec 32))
    (idx : Nat) (v : BitVec 32) :
    { (sortState s rri scri) with
      scratch := { (sortState s rri scri).scratch with
        red_refs := (sortState s rri scri).scratch.red_refs.set idx v } } =
    sortState s (rri.set idx v) scri := by
  rcases s with ⟨core, scratch⟩; cases scratch; rfl

private theorem sortState_set_scratch_buf (s : FullState) (rri scri : List (BitVec 32))
    (idx : Nat) (v : BitVec 32) :
    { (sortState s rri scri) with
      scratch := { (sortState s rri scri).scratch with
        scratch_buf := (sortState s rri scri).scratch.scratch_buf.set idx v } } =
    sortState s rri (scri.set idx v) := by
  rcases s with ⟨core, scratch⟩; cases scratch; rfl

private theorem c0_load_sort_arena {c : FullCfg} {s : FullState} {rri scri : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (hi : i.toNat < s.core.arena.length)
    (hm : (FullMem c (sortState s rri scri) ⋆ R) m) :
    loadVal m i32 (c.pArena + i * 4) = some s.core.arena[i.toNat] :=
  FullArenaTactics.c0_load_full_arena (s := sortState s rri scri) hi hm

private theorem c0_load_sort_tarjan_reach {c : FullCfg} {s : FullState}
    {rri scri : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.scratch.tarjan_reach.length)
    (hm : (FullMem c (sortState s rri scri) ⋆ R) m) :
    loadVal m i32 (c.pTarjanReach + i * 4) = some s.scratch.tarjan_reach[i.toNat] :=
  FullArenaTactics.c0_load_full_tarjan_reach (s := sortState s rri scri) hi hm

private theorem c0_load_sort_red_refs {c : FullCfg} {s : FullState}
    {rri scri : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < rri.length)
    (hm : (FullMem c (sortState s rri scri) ⋆ R) m) :
    loadVal m i32 (c.pRedRefs + i * 4) = some rri[i.toNat] :=
  FullArenaTactics.c0_load_full_red_refs (s := sortState s rri scri) hi hm

attribute [local c0_load] c0_load_sort_arena c0_load_sort_tarjan_reach c0_load_sort_red_refs

local macro "not_jnz" : tactic =>
  `(tactic| fail_if_success (change wp _ _ _ (.jnz _ _ _) _))

local macro "fast_line" : tactic =>
  `(tactic| repeat (first
    | (not_jnz; c0_hstep_np)
    | rw [wp_jump]; dsimp only [vals, Arg.val]
    | rw [wp_ret]; dsimp only [vals, Arg.val]))

local macro "fast_split" : tactic =>
  `(tactic| (fast_line; c0_hsplit))

local macro "step_lets" : tactic =>
  `(tactic| repeat (
    rw [wp_let]
    try dsimp only [Op.wp, vals, Arg.val, OpCode.wp, liftCmp, lift2, lift1,
      CmpOp.evalBits, CmpOp.evalBool, Bool.toNat]))

local macro "step_jnz" : tactic =>
  `(tactic| (
    try simp only [Blocks.get]
    fast_line
    step_lets
    rw [wp_jnz]; try dsimp only [vals, Arg.val]
    refine ⟨fun hc => ?_, fun hc => ?_⟩))

private def SortInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (bn n : BitVec 64) (rr scr : List (BitVec 32)) (m : Mem 64) : Prop :=
  n.toNat ≤ bn.toNat ∧ rr.length = c.red_cap ∧ scr.length = c.scratch_cap ∧
  (∀ k < bn.toNat, (rr[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
  (FullMem c (sortState s rr scr) ⋆ R) m

private abbrev sortKeyPtr (c : FullCfg) (bn : BitVec 64) (useRR : Bool) : BitVec 64 :=
  if useRR = true then c.pRedRefs + bn * 4#64 else c.pScratchBuf

private theorem sort_key_ptr_rr (base a b : BitVec 64) :
    (base + a * 4#64) + b * 4#64 = base + (a + b) * 4#64 := by bv_omega

private theorem bv64_shl1_toNat {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< 1#64).toNat = 2 * x.toNat := by
  have h1 : x <<< 1#64 = x <<< 1 := rfl
  rw [h1, BitVec.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq, Nat.pow_one]
  omega

private theorem bv64_succ_le {x bn : BitVec 64} (hx : x.toNat < bn.toNat) :
    (x + 1#64).toNat ≤ bn.toNat ∧ bn.toNat - (x + 1#64).toNat < bn.toNat - x.toNat := by
  have : (x + 1#64).toNat = x.toNat + 1 := by bv_omega
  omega

private theorem bv32_succ_le {u sz : BitVec 32} (hu : u.toNat < sz.toNat) :
    (u + 1#32).toNat ≤ sz.toNat ∧ sz.toNat - (u + 1#32).toNat < sz.toNat - u.toNat := by
  have : (u + 1#32).toNat = u.toNat + 1 := by bv_omega
  omega

private theorem bv64_shl1_add1 {x : BitVec 64} (h2 : (x <<< 1#64).toNat = 2 * x.toNat)
    (_hx : 2 * x.toNat + 1 < 2 ^ 64) :
    ((x <<< 1#64) + 1#64).toNat = 2 * x.toNat + 1 := by
  have : ((x <<< 1#64) + 1#64).toNat = (x <<< 1#64).toNat + 1 := by bv_omega
  omega

private theorem bv64_sub_dec {j gap bn : BitVec 64} (hj : j.toNat < bn.toNat)
    (hgap_pos : 0 < gap.toNat) (hjg : gap.toNat ≤ j.toNat) :
    (j - gap).toNat < bn.toNat ∧ (j - gap).toNat < j.toNat := by
  have : (j - gap).toNat = j.toNat - gap.toNat := by bv_omega
  omega

private theorem tarjan_lt_of_cmp {c : FullCfg} {s : FullState} {x : BitVec 32}
    (hcv : s.core.cur_vars ≤ c.max_vars) (hmv : c.max_vars < 2 * dimacsBound)
    (htr : s.scratch.tarjan_reach.length = 2 * c.max_vars)
    (hlt : (BitVec.setWidth 64 x).toNat < (BitVec.ofNat 64 s.core.cur_vars <<< 1#64).toNat) :
    (BitVec.setWidth 64 x).toNat < s.scratch.tarjan_reach.length := by
  unfold dimacsBound at hmv
  have hshl : (BitVec.ofNat 64 s.core.cur_vars <<< 1#64).toNat = 2 * s.core.cur_vars := by
    rw [bv64_shl1_toNat]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  omega

private theorem tarjan_lt_of_nat {c : FullCfg} {s : FullState} {v : BitVec 32}
    (hcv : s.core.cur_vars ≤ c.max_vars) (hmv : c.max_vars < 2 * dimacsBound)
    (htr : s.scratch.tarjan_reach.length = 2 * c.max_vars)
    (hlt : v.toNat < 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64) :
    (BitVec.setWidth 64 v).toNat < s.scratch.tarjan_reach.length := by
  unfold dimacsBound at hmv; bv_omega

private theorem knuth_gap_step {gap bn : BitVec 64} (hbn : bn.toNat < 2 ^ 64)
    (hgap : gap.toNat < (bn / (3 : BitVec 64)).toNat) :
    (gap * 3#64 + 1#64).toNat ≤ bn.toNat ∧ gap.toNat < (gap * 3#64 + 1#64).toNat := by
  have hdiv : (bn / (3 : BitVec 64)).toNat = bn.toNat / 3 := by rw [BitVec.toNat_udiv]; rfl
  rw [hdiv] at hgap
  have hstep : (gap * 3#64 + 1#64).toNat = gap.toNat * 3 + 1 := by
    have : gap.toNat * 3 + 1 ≤ bn.toNat := by omega
    bv_omega
  rw [hstep]
  exact ⟨by omega, by omega⟩

private theorem knuth_gap_div3 {gap : BitVec 64} (hpos : 0 < gap.toNat) :
    (gap / 3#64).toNat < gap.toNat := by
  have hdiv : (gap / 3#64).toNat = gap.toNat / 3 := by rw [BitVec.toNat_udiv]; rfl
  rw [hdiv]; omega

private theorem sort_rr_set_mem {p : Nat → Prop} {rr : List (BitVec 32)} {n idx : Nat}
    {v : BitVec 32} (hn : n ≤ rr.length) (hidx : idx < n)
    (hrr : ∀ k < n, p (rr[k]?.getD 0#32).toNat) (hv : p v.toNat) :
    ∀ k < n, p ((rr.set idx v)[k]?.getD 0#32).toNat := by
  intro k hk
  have hk_len : k < (rr.set idx v).length := by rw [List.length_set]; omega
  rw [List.getElem?_eq_getElem hk_len, Option.getD_some]
  by_cases heq : k = idx
  · subst heq; rw [List.getElem_set_self (by omega)]; exact hv
  · simp only [List.getElem_set_ne (Ne.symm heq)]
    have hk_prev := hrr k hk
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hk_prev

private theorem sort_rr_get_mem {p : Nat → Prop} {rr : List (BitVec 32)} {n idx : Nat}
    (hn : n ≤ rr.length) (hidx : idx < n) (hrr : ∀ k < n, p (rr[k]?.getD 0#32).toNat) :
    p (rr[idx]'(by omega)).toNat := by
  have h := hrr idx hidx
  rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at h

private theorem sort_cref_bounds {c : FullCfg} {F0 : CNF Nat} {s : FullState} {cr : BitVec 32}
    (hsp : FullSparseInv c F0 s) (hmem : cr.toNat ∈ fullArenaClauseRefs s) :
    cr.toNat + 3 ≤ s.core.arena_len ∧ s.core.arena_len ≤ s.core.arena.length ∧
    s.core.arena_len < 2 ^ 32 ∧
    (BitVec.setWidth 64 cr + 2#64).toNat = cr.toNat + 2 ∧
    cr.toNat + 2 < s.core.arena.length ∧
    cr.toNat + 3 + (s.core.arena[cr.toNat + 2]'(by
      rcases hsp.1.witness with ⟨_, hw⟩
      have hwf := hw.arena.refs_wf cr.toNat hmem
      have har_len := hsp.1.lengths.core_ok.arena_len_arr
      have har_le := hsp.1.lengths.core_ok.arena_len_le
      omega)).toNat ≤ s.core.arena.length := by
  rcases hsp.1.witness with ⟨_, hw⟩
  have hwf := hw.arena.refs_wf cr.toNat hmem
  have har_cap := c.harena; unfold dimacsBound at har_cap
  have har_len := hsp.1.lengths.core_ok.arena_len_arr
  have har_le := hsp.1.lengths.core_ok.arena_len_le
  have hlt_sz : cr.toNat + 2 < s.core.arena.length := by omega
  have hsz_eq : fullArenaClauseSizeCore s.core cr.toNat =
      (s.core.arena[cr.toNat + 2]'hlt_sz).toNat := by
    rw [fullArenaClauseSizeCore, List.getElem?_eq_getElem hlt_sz, Option.getD_some]
  refine ⟨hwf.1, by omega, by omega, by bv_omega, hlt_sz, ?_⟩
  rw [← hsz_eq]
  have := hwf.2.1; have := hwf.2.2.1; have := hwf.2.2.2.1; omega

private theorem sort_key_load_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {useRR : Bool} {bn : BitVec 64}
    {rri scri : List (BitVec 32)} {off : BitVec 64} {cont : Val i32 → Expr Val Cont rs}
    {mi : Mem 64} {limit : Nat}
    (hrr : rri.length = c.red_cap) (hscr : scri.length = c.scratch_cap)
    (hbound : (useRR = true ∧ bn.toNat + limit ≤ c.red_cap) ∨
              (useRR = false ∧ limit ≤ c.scratch_cap))
    (hoff : off.toNat < limit) (_hbn64 : bn.toNat + limit < 2 ^ 64)
    (hm : (FullMem c (sortState s rri scri) ⋆ R) mi)
    (hcont : ∀ v : BitVec 32, wp Γ Q X (cont v) mi) :
    wp Γ Q X (.load i32 (.var (sortKeyPtr c bn useRR + off * 4#64)) cont) mi := by
  rcases hbound with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
  · dsimp only [sortKeyPtr]; simp only [↓reduceIte]
    rw [sort_key_ptr_rr]
    have hidx : (bn + off).toNat < (sortState s rri scri).scratch.red_refs.length := by
      rw [sortState_red_refs]; bv_omega
    exact wp_load_of (FullArenaTactics.c0_load_full_red_refs hidx hm) (hcont _)
  · dsimp only [sortKeyPtr]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hidx : off.toNat < (sortState s rri scri).scratch.scratch_buf.length := by
      rw [sortState_scratch_buf]; omega
    exact wp_load_of (FullArenaTactics.c0_load_full_scratch_buf hidx hm) (hcont _)

private theorem sort_key_store_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {useRR : Bool} {bn : BitVec 64}
    {rri scri : List (BitVec 32)} {off : BitVec 64} {v : Val i32}
    {e : Expr Val Cont rs} {mi : Mem 64} {refs : Nat → Prop} {limit : Nat}
    (hrr : rri.length = c.red_cap) (hscr : scri.length = c.scratch_cap)
    (hbound : (useRR = true ∧ bn.toNat + limit ≤ c.red_cap) ∨
              (useRR = false ∧ limit ≤ c.scratch_cap))
    (hoff : off.toNat < limit) (hbn64 : bn.toNat + limit < 2 ^ 64)
    (hmem : ∀ k < bn.toNat, refs (rri[k]?.getD 0#32).toNat)
    (hm : (FullMem c (sortState s rri scri) ⋆ R) mi)
    (hcont : ∀ rri' scri' mi', rri'.length = c.red_cap → scri'.length = c.scratch_cap →
      (∀ k < bn.toNat, refs (rri'[k]?.getD 0#32).toNat) →
      (FullMem c (sortState s rri' scri') ⋆ R) mi' → wp Γ Q X e mi') :
    wp Γ Q X (.store (.var v) (.var (sortKeyPtr c bn useRR + off * 4#64)) e) mi := by
  rcases hbound with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
  · dsimp only [sortKeyPtr]; simp only [↓reduceIte]
    rw [sort_key_ptr_rr]
    have hidx : (bn + off).toNat < (sortState s rri scri).scratch.red_refs.length := by
      rw [sortState_red_refs]; bv_omega
    refine wp_store_sep (FullArenaTactics.c0_store_full_red_refs v hidx hm) fun mi' hm' => ?_
    rw [sortState_set_red_refs] at hm'
    refine hcont (rri.set (bn + off).toNat v) scri mi'
      (by rw [List.length_set]; exact hrr) hscr ?_ hm'
    intro k hk
    have hk_ne : (bn + off).toNat ≠ k := by bv_omega
    have hk_len : k < (rri.set (bn + off).toNat v).length := by rw [List.length_set]; omega
    rw [List.getElem?_eq_getElem hk_len, Option.getD_some]
    simp only [List.getElem_set_ne hk_ne]
    have hprev := hmem k hk
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hprev
  · dsimp only [sortKeyPtr]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hidx : off.toNat < (sortState s rri scri).scratch.scratch_buf.length := by
      rw [sortState_scratch_buf]; omega
    refine wp_store_sep (FullArenaTactics.c0_store_full_scratch_buf v hidx hm) fun mi' hm' => ?_
    rw [sortState_set_scratch_buf] at hm'
    exact hcont rri (scri.set off.toNat v) mi' hrr (by rw [List.length_set]; exact hscr) hmem hm'

private theorem sort_rr_store_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {rri scri : List (BitVec 32)}
    {off : BitVec 64} {v : Val i32} {e : Expr Val Cont rs} {mi : Mem 64} {refs : Nat → Prop}
    {bn : BitVec 64} (hoff : off.toNat < bn.toNat) (hbn : bn.toNat ≤ rri.length)
    (hmem : ∀ k < bn.toNat, refs (rri[k]?.getD 0#32).toNat) (hv : refs v.toNat)
    (hm : (FullMem c (sortState s rri scri) ⋆ R) mi)
    (hcont : ∀ rri' mi', rri'.length = rri.length →
      (∀ k < bn.toNat, refs (rri'[k]?.getD 0#32).toNat) →
      (FullMem c (sortState s rri' scri) ⋆ R) mi' → wp Γ Q X e mi') :
    wp Γ Q X (.store (.var v) (.var (c.pRedRefs + off * 4#64)) e) mi := by
  have hidx : off.toNat < (sortState s rri scri).scratch.red_refs.length := by
    rw [sortState_red_refs]; omega
  refine wp_store_sep (FullArenaTactics.c0_store_full_red_refs v hidx hm) fun mi' hm' => ?_
  rw [sortState_set_red_refs] at hm'
  exact hcont (rri.set off.toNat v) mi' (by rw [List.length_set])
    (sort_rr_set_mem hbn hoff hmem hv) hm'

private theorem sort_tarjan_load_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {rri scri : List (BitVec 32)}
    {off : BitVec 64} {cont : Val i32 → Expr Val Cont rs} {mi : Mem 64}
    (hi : off.toNat < s.scratch.tarjan_reach.length)
    (hm : (FullMem c (sortState s rri scri) ⋆ R) mi)
    (hcont : ∀ v : BitVec 32, wp Γ Q X (cont v) mi) :
    wp Γ Q X (.load i32 (.var (c.pTarjanReach + off * 4#64)) cont) mi := by
  have hi' : off.toNat < (sortState s rri scri).scratch.tarjan_reach.length := by
    rw [sortState_tarjan_reach]; exact hi
  exact wp_load_of (FullArenaTactics.c0_load_full_tarjan_reach hi' hm) (hcont _)

private theorem sort_tarjan_guard_wp {Γ : Env} {Q : Post []} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {s : FullState} {rri scri : List (BitVec 32)}
    {R : Mem 64 → Prop} {mi : Mem 64} (x : BitVec 32)
    (J : Cont [i32]) (hJ : ∀ v : BitVec 32, J (v, ()) mi)
    (hsp : FullSparseInv c F0 s) (hm : (FullMem c (sortState s rri scri) ⋆ R) mi) :
    wp Γ Q X
      (Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (.var x, ()) } fun p =>
        Expr.let_
          { sig := [i64, i64], code := OpCode.cmp .ult i64 Ty.bool (by decide),
            args := (.var p.1, .var (BitVec.ofNat 64 s.core.cur_vars <<< 1), ()) } fun p =>
        Expr.jnz (.var p.1)
          (Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (.var x, ()) } fun p =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.mul i64,
                args := (.var p.1, .imm 4, ()) } fun p =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.add i64,
                args := (.var c.pTarjanReach, .var p.1, ()) } fun p =>
            Expr.load i32 (.var p.1) fun ld => Expr.jump J (.var ld, ()))
          (Expr.jump J (.imm 0, ()))) mi := by
  viv_steps
  · exact sort_tarjan_load_wp (tarjan_lt_of_nat hsp.1.lengths.core_ok.cur_vars_le c.hmaxv
      hsp.1.lengths.scratch_ok.tarjan_reach_len hc) hm (fun v => by fast_line; exact hJ v)
  · exact hJ 0#32

private theorem u_loop_lt_sz' {ar : List (BitVec 32)} {cr u : BitVec 32}
    {hlt : cr.toNat + 2 < ar.length} {_hc_len : cr.toNat + 2 < 2 ^ 64}
    (hc : u.toNat < (ar[(cr.toNat + (2 : BitVec 64).toNat) % 2 ^ 64]'(by
      have h2 : (cr.toNat + (2 : BitVec 64).toNat) % 2 ^ 64 = cr.toNat + 2 := by
        have : (2 : BitVec 64).toNat = 2 := rfl; omega
      omega)).toNat) :
    u.toNat < (ar[cr.toNat + 2]'hlt).toNat := by
  have h2 : (cr.toNat + (2 : BitVec 64).toNat) % 2 ^ 64 = cr.toNat + 2 := by
    have : (2 : BitVec 64).toNat = 2 := rfl; omega
  have heq : (ar[(cr.toNat + (2 : BitVec 64).toNat) % 2 ^ 64]'(by omega)) =
      ar[cr.toNat + 2]'hlt := by simp only [h2]
  exact heq ▸ hc

private theorem full_viv_sort2_fid_wp_aux (Γ : Env) (c : FullCfg) (F0 : CNF Nat)
    (s : FullState) (bn mode : BitVec 64) (m : Mem 64) (Q : Post []) (X : XPost)
    (R : Mem 64 → Prop) (hsp : FullSparseInv c F0 s) (hbn_le : bn.toNat ≤ c.red_cap)
    (hmode : (mode = 1#64 ∧ bn.toNat + 2 * bn.toNat ≤ c.red_cap) ∨
             (mode ≠ 1#64 ∧ 2 * bn.toNat ≤ c.scratch_cap))
    (hmem : ∀ k < bn.toNat, (s.scratch.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ rr' scr' m', rr'.length = c.red_cap → scr'.length = c.scratch_cap →
      (∀ k < bn.toNat, (rr'[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) →
      (FullMem c (sortState s rr' scr') ⋆ R) m' → Q () m') :
    Func.wp Γ full_viv_sort2_fid_body (c.hdr, bn, mode, ()) m Q X := by
  have hred_bound := c.hred; unfold dimacsBound at hred_bound
  have hscr_bound := c.hscr; unfold dimacsBound at hscr_bound
  have hmv_bound := c.hmaxv; unfold dimacsBound at hmv_bound
  have hbn3_64 : bn.toNat + 2 * bn.toNat < 2 ^ 64 := by
    rcases hmode with ⟨_, h1⟩ | ⟨_, h2⟩ <;> omega
  have hm0 : (FullMem c (sortState s s.scratch.red_refs s.scratch.scratch_buf) ⋆ R) m := by
    rwa [sortState_self]
  unfold Func.wp full_viv_sort2_fid_body
  viv_to_group
  · exact hQ s.scratch.red_refs s.scratch.scratch_buf m
      hsp.1.lengths.scratch_ok.red_refs_len hsp.1.lengths.scratch_ok.scratch_buf_len hmem hm0
  · refine wp_join_state1 (t := i64) (α := Bool) (fun st => sortKeyPtr c bn st)
      (fun useRR mk =>
        mk = m ∧
        ((useRR = true ∧ bn.toNat + 2 * bn.toNat ≤ c.red_cap) ∨
         (useRR = false ∧ 2 * bn.toNat ≤ c.scratch_cap)))
      ?_ ?_
    · rintro _ useRR mk ⟨hmk, hbound2⟩
      subst mk
      viv_to_group
      refine wp_while_state1 (α := BitVec 64 × List (BitVec 32) × List (BitVec 32))
        (fun st => st.1) (fun st => bn.toNat - st.1.toNat)
        (fun (i, rri, scri) mi => SortInv c s R bn i rri scri mi) ?_ ?_
      · intro Ji hJi; fast_line
        exact hJi (0#64, s.scratch.red_refs, s.scratch.scratch_buf) m
          ⟨Nat.zero_le _, hsp.1.lengths.scratch_ok.red_refs_len,
           hsp.1.lengths.scratch_ok.scratch_buf_len, hmem, hm0⟩
      · rintro Ji ⟨i, rri, scri⟩ mi ⟨hi_le, hrr_len, hscr_len, hrr_mem, hm_i⟩ ihi
        viv_steps
        · have hi_lt : i.toNat < bn.toNat := hc
          have hcr_mem := sort_rr_get_mem (by omega) hi_lt hrr_mem
          have hcr_b := sort_cref_bounds hsp hcr_mem
          viv_to_group
          refine wp_while_state
            (α := BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32)
            (fun st => (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2, ()))
            (fun st =>
              (s.core.arena[(rri[i.toNat]'(by omega)).toNat + 2]'(hcr_b.2.2.2.2.1)).toNat -
                st.2.2.2.2.toNat)
            (fun (_, _, _, _, u) ml =>
              ml = mi ∧
              u.toNat ≤
                (s.core.arena[(rri[i.toNat]'(by omega)).toNat + 2]'(hcr_b.2.2.2.2.1)).toNat)
            ?_ ?_
          · intro Jl hJl; fast_line
            exact hJl (0xFFFFFFFF#32, 0#32, 0xFFFFFFFF#32, 0#32, 0#32) mi ⟨rfl, Nat.zero_le _⟩
          · rintro Jl ⟨m0, k0, m1, k1, u⟩ ml ⟨hml, hu_le⟩ ihl
            subst ml
            viv_steps
            · have hu_lt : u.toNat <
                  (s.core.arena[(rri[i.toNat]'(by omega)).toNat + 2]'(hcr_b.2.2.2.2.1)).toNat :=
                u_loop_lt_sz' (_hc_len := by have := hcr_b.1; have := hcr_b.2.2.1; omega) hc
              have hlit_lt : (BitVec.setWidth 64 rri[i.toNat] + 3#64 +
                  BitVec.setWidth 64 u).toNat < s.core.arena.length := by
                have := hcr_b.2.2.2.2.2; bv_omega
              viv_to_group
              refine wp_join_state1 (t := i32) (α := BitVec 32) (fun v => v)
                (fun _ mw => mw = mi) ?_ ?_
              · rintro _ w mw hmw
                subst mw
                viv_to_group
                refine wp_join_state
                  (α := BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32)
                  (fun st => (st.1, st.2.1, st.2.2.1, st.2.2.2, ()))
                  (fun _ mu => mu = mi) ?_ ?_
                · rintro _ ⟨m0', k0', m1', k1'⟩ mu hmu
                  subst mu
                  fast_line
                  have hst := bv32_succ_le hu_lt
                  exact ihl (m0', k0', m1', k1', u + 1#32) mi hst.2 ⟨rfl, hst.1⟩
                · intro Ju hJu
                  viv_steps <;> exact hJu (_, _, _, _) mi rfl
              · intro Jw hJw
                dsimp only [sortState_core]
                exact sort_tarjan_guard_wp _ Jw (fun v => hJw v mi rfl) hsp hm_i
            · have hshl1 : (i <<< 1#64).toNat = 2 * i.toNat := bv64_shl1_toNat (by omega)
              have hshl1_add1 := bv64_shl1_add1 hshl1 (by omega)
              apply sort_key_store_wp hrr_len hscr_len hbound2 (off := i <<< 1#64)
                (by omega) hbn3_64 hrr_mem hm_i
              intro rr1 scr1 m1 hrr1 hscr1 hrr1_mem hm1
              fast_line
              apply sort_key_store_wp hrr1 hscr1 hbound2 (off := (i <<< 1#64) + 1#64)
                (by omega) hbn3_64 hrr1_mem hm1
              intro rr2 scr2 m2 hrr2 hscr2 hrr2_mem hm2
              fast_line
              have hst := bv64_succ_le hi_lt
              exact ihi (i + 1#64, rr2, scr2) m2 hst.2 ⟨hst.1, hrr2, hscr2, hrr2_mem, hm2⟩
        · fast_line
          viv_to_group
          refine wp_while_state1 (α := BitVec 64) (fun st => st)
            (fun st => bn.toNat - st.toNat)
            (fun g mg => mg = mi ∧ 0 < g.toNat ∧ g.toNat ≤ bn.toNat) ?_ ?_
          · intro Jg hJg; fast_line
            exact hJg 1#64 mi ⟨rfl, by decide, by bv_omega⟩
          · rintro Jg g mg ⟨hmg, hg_pos, hg_le⟩ ihg
            subst mg
            c0_hsplit
            · have hg_step := knuth_gap_step bn.isLt hc
              exact ihg (g * 3#64 + 1#64) mi (by omega) ⟨rfl, by omega, hg_step.1⟩
            · viv_to_group
              refine wp_while_state1 (α := BitVec 64 × List (BitVec 32) × List (BitVec 32))
                (fun st => st.1) (fun st => st.1.toNat)
                (fun (gap, rrg, scrg) mgg => SortInv c s R bn gap rrg scrg mgg) ?_ ?_
              · intro Jsh hJsh; fast_line
                exact hJsh (g, rri, scri) mi ⟨hg_le, hrr_len, hscr_len, hrr_mem, hm_i⟩
              · rintro Jsh ⟨gap, rrg, scrg⟩ mgg
                  ⟨hgap_le, hrrg, hscrg, hrrg_mem, hm_gg⟩ ihsh
                c0_hsplit
                · have hgap_pos : 0 < gap.toNat := by simpa using hc
                  viv_to_group
                  refine wp_while_state1 (α := BitVec 64 × List (BitVec 32) × List (BitVec 32))
                    (fun st => st.1) (fun st => bn.toNat - st.1.toNat)
                    (fun (i2, rrl, scrl) mll => SortInv c s R bn i2 rrl scrl mll) ?_ ?_
                  · intro Jl hJl; fast_line
                    exact hJl (gap, rrg, scrg) mgg ⟨hgap_le, hrrg, hscrg, hrrg_mem, hm_gg⟩
                  · rintro Jl ⟨i2, rrl, scrl⟩ mll ⟨hi2_le, hrrl, hscrl, hrrl_mem, hm_ll⟩ ihl
                    viv_steps
                    · have hi2_lt : i2.toNat < bn.toNat := hc
                      have hshl2 : (i2 <<< 1#64).toNat = 2 * i2.toNat :=
                        bv64_shl1_toNat (by omega)
                      have hshl2_add1 := bv64_shl1_add1 hshl2 (by omega)
                      apply sort_key_load_wp hrrl hscrl hbound2 (off := i2 <<< 1#64)
                        (by omega) hbn3_64 hm_ll
                      intro lk0
                      fast_line
                      apply sort_key_load_wp hrrl hscrl hbound2 (off := (i2 <<< 1#64) + 1#64)
                        (by omega) hbn3_64 hm_ll
                      intro lk1
                      have hcr2_mem := sort_rr_get_mem (by omega) hi2_lt hrrl_mem
                      have hcr2_b := sort_cref_bounds hsp hcr2_mem
                      viv_to_group
                      refine wp_join_state1 (t := i32) (α := BitVec 32) (fun v => v)
                        (fun _ m3 => m3 = mll) ?_ ?_
                      · rintro _ lt0 m3 hm3
                        subst m3
                        viv_to_group
                        refine wp_join_state1 (t := i32) (α := BitVec 32) (fun v => v)
                          (fun _ m4 => m4 = mll) ?_ ?_
                        · rintro _ lt1 m4 hm4
                          subst m4
                          viv_to_group
                          refine wp_join_state1 (t := i64)
                            (α := BitVec 64 × List (BitVec 32) × List (BitVec 32))
                            (fun st => st.1)
                            (fun (jf, rrj, scrj) mj =>
                              jf.toNat < bn.toNat ∧ SortInv c s R bn jf rrj scrj mj)
                            ?_ ?_
                          · rintro _ ⟨jf, rrj, scrj⟩ mj
                              ⟨hjf_lt, _, hrrj, hscrj, hrrj_mem, hm_j⟩
                            fast_line
                            apply sort_rr_store_wp (refs := fun x => x ∈ fullArenaClauseRefs s)
                              (bn := bn) hjf_lt (by omega) hrrj_mem hcr2_mem hm_j
                            intro rrj' mj' hrrj' hmem' hm_j'
                            fast_line
                            have hshlf : (jf <<< 1#64).toNat = 2 * jf.toNat :=
                              bv64_shl1_toNat (by omega)
                            have hshlf_add1 := bv64_shl1_add1 hshlf (by omega)
                            apply sort_key_store_wp (hrrj'.trans hrrj) hscrj hbound2
                              (off := jf <<< 1#64) (by omega) hbn3_64 hmem' hm_j'
                            intro rrk1 scrk1 mk1 hrrk1 hscrk1 hrrk1_mem hm_k1
                            fast_line
                            apply sort_key_store_wp hrrk1 hscrk1 hbound2
                              (off := (jf <<< 1#64) + 1#64) (by omega) hbn3_64 hrrk1_mem hm_k1
                            intro rrk2 scrk2 mk2 hrrk2 hscrk2 hrrk2_mem hm_k2
                            fast_line
                            have hst := bv64_succ_le hi2_lt
                            exact ihl (i2 + 1#64, rrk2, scrk2) mk2 hst.2
                              ⟨hst.1, hrrk2, hscrk2, hrrk2_mem, hm_k2⟩
                          · intro Jbrk hJbrk
                            viv_to_group
                            refine wp_while_state1
                              (α := BitVec 64 × List (BitVec 32) × List (BitVec 32))
                              (fun st => st.1) (fun st => st.1.toNat)
                              (fun (j, rrj, scrj) mj =>
                                j.toNat < bn.toNat ∧ SortInv c s R bn j rrj scrj mj)
                              ?_ ?_
                            · intro Jj hJj; fast_line
                              exact hJj (i2, rrl, scrl) mll
                                ⟨hi2_lt, hi2_le, hrrl, hscrl, hrrl_mem, hm_ll⟩
                            · rintro Jj ⟨j, rrj, scrj⟩ mj
                                ⟨hj_lt, hj_le, hrrj, hscrj, hrrj_mem, hm_j⟩ ihj
                              viv_steps
                              · have hjg : gap.toNat ≤ j.toNat := by bv_omega
                                have hsub := bv64_sub_dec hj_lt hgap_pos hjg
                                have hdiff_lt := hsub.1
                                have hshld : ((j - gap) <<< 1#64).toNat =
                                    2 * (j - gap).toNat := bv64_shl1_toNat (by omega)
                                have hshld_add1 := bv64_shl1_add1 hshld (by omega)
                                apply sort_key_load_wp hrrj hscrj hbound2
                                  (off := (j - gap) <<< 1#64) (by omega) hbn3_64 hm_j
                                intro uk0
                                fast_line
                                apply sort_key_load_wp hrrj hscrj hbound2
                                  (off := ((j - gap) <<< 1#64) + 1#64) (by omega) hbn3_64 hm_j
                                intro uk1
                                have hucr_mem := sort_rr_get_mem (by omega) hdiff_lt hrrj_mem
                                have hucr_b := sort_cref_bounds hsp hucr_mem
                                viv_to_group
                                refine wp_join_state1 (t := i32) (α := BitVec 32) (fun v => v)
                                  (fun _ m6 => m6 = mj) ?_ ?_
                                · rintro _ ut0 m6 hm6; subst m6
                                  viv_to_group
                                  refine wp_join_state1 (t := i32) (α := BitVec 32) (fun v => v)
                                    (fun _ m7 => m7 = mj) ?_ ?_
                                  · rintro _ ut1 m7 hm7; subst m7
                                    viv_to_group
                                    refine wp_join_group (fun _ m8 => m8 = mj) ?_ ?_
                                    · intro _ _ m8 hm8; subst m8
                                      viv_to_group
                                      refine wp_join_group (fun _ m9 => m9 = mj) ?_ ?_
                                      · intro _ _ m9 hm9; subst m9
                                        fast_line
                                        have hu_mem :=
                                          sort_rr_get_mem (by omega) hdiff_lt hrrj_mem
                                        apply sort_rr_store_wp
                                          (refs := fun x => x ∈ fullArenaClauseRefs s)
                                          (bn := bn) hj_lt (by omega) hrrj_mem hu_mem hm_j
                                        intro rrj' mj' hrrj' hmem' hm_j'
                                        fast_line
                                        have hshlj : (j <<< 1#64).toNat = 2 * j.toNat :=
                                          bv64_shl1_toNat (by omega)
                                        have hshlj_add1 := bv64_shl1_add1 hshlj (by omega)
                                        apply sort_key_store_wp (hrrj'.trans hrrj) hscrj hbound2
                                          (off := j <<< 1#64) (by omega) hbn3_64 hmem' hm_j'
                                        intro rrs1 scrs1 ms1 hrrs1 hscrs1 hrrs1_mem hms1
                                        fast_line
                                        apply sort_key_store_wp hrrs1 hscrs1 hbound2
                                          (off := (j <<< 1#64) + 1#64) (by omega) hbn3_64
                                          hrrs1_mem hms1
                                        intro rrs2 scrs2 ms2 hrrs2 hscrs2 hrrs2_mem hms2
                                        fast_line
                                        exact ihj (j - gap, rrs2, scrs2) ms2 hsub.2
                                          ⟨hdiff_lt, by omega, hrrs2, hscrs2, hrrs2_mem, hms2⟩
                                      · intro Jgo2 hJgo2; repeat step_jnz
                                        · exact hJbrk (j, rrj, scrj) mj
                                            ⟨hj_lt, hj_le, hrrj, hscrj, hrrj_mem, hm_j⟩
                                        · refine wp_join_group (fun _ ma => ma = mj) ?_ ?_
                                          · intro _ _ ma hma; subst ma; fast_line
                                            exact hJgo2 () mj rfl
                                          · intro J14 hJ14; repeat step_jnz
                                            · exact hJbrk (j, rrj, scrj) mj
                                                ⟨hj_lt, hj_le, hrrj, hscrj, hrrj_mem, hm_j⟩
                                            · refine wp_join_group (fun _ mb => mb = mj) ?_ ?_
                                              · intro _ _ mb hmb; subst mb; fast_line
                                                exact hJ14 () mj rfl
                                              · intro J15 hJ15; repeat step_jnz
                                                · exact hJbrk (j, rrj, scrj) mj
                                                    ⟨hj_lt, hj_le, hrrj, hscrj, hrrj_mem, hm_j⟩
                                                · refine wp_join_group
                                                    (fun _ mc => mc = mj) ?_ ?_
                                                  · intro _ _ mc hmc; subst mc; fast_line
                                                    exact hJ15 () mj rfl
                                                  · intro J16 hJ16
                                                    repeat (any_goals step_jnz)
                                                    all_goals first
                                                    | exact hJ16 () mj rfl
                                                    | exact hJbrk (j, rrj, scrj) mj
                                                        ⟨hj_lt, hj_le, hrrj, hscrj, hrrj_mem,
                                                         hm_j⟩
                                                · exact hJ15 () mj rfl
                                            · exact hJ14 () mj rfl
                                        · exact hJgo2 () mj rfl
                                    · intro Jgo1 hJgo1
                                      repeat (any_goals step_jnz)
                                      all_goals first
                                      | exact hJgo1 () mj rfl
                                      | exact hJbrk (j, rrj, scrj) mj
                                          ⟨hj_lt, hj_le, hrrj, hscrj, hrrj_mem, hm_j⟩
                                  · intro Jut1 hJut1
                                    dsimp only [sortState_core]
                                    exact sort_tarjan_guard_wp _ Jut1
                                      (fun v => hJut1 v mj rfl) hsp hm_j
                                · intro Jut0 hJut0
                                  dsimp only [sortState_core]
                                  exact sort_tarjan_guard_wp _ Jut0
                                    (fun v => hJut0 v mj rfl) hsp hm_j
                              · exact hJbrk (j, rrj, scrj) mj
                                  ⟨hj_lt, hj_le, hrrj, hscrj, hrrj_mem, hm_j⟩
                        · intro Jlt1 hJlt1
                          dsimp only [sortState_core]
                          exact sort_tarjan_guard_wp _ Jlt1 (fun v => hJlt1 v mll rfl) hsp hm_ll
                      · intro Jlt0 hJlt0
                        dsimp only [sortState_core]
                        exact sort_tarjan_guard_wp _ Jlt0 (fun v => hJlt0 v mll rfl) hsp hm_ll
                    · have hgap_pos' : 0 < gap.toNat := by omega
                      have hdiv_le : (gap / 3#64).toNat ≤ bn.toNat := by
                        have hle := knuth_gap_div3 hgap_pos'; omega
                      exact ihsh (gap / 3#64, rrl, scrl) mll (knuth_gap_div3 hgap_pos')
                        ⟨hdiv_le, hrrl, hscrl, hrrl_mem, hm_ll⟩
                · exact hQ rrg scrg mgg hrrg hscrg hrrg_mem hm_gg
    · intro Jk hJk
      viv_steps
      · refine hJk true m ⟨rfl, Or.inl ⟨rfl, ?_⟩⟩
        rcases hmode with ⟨_, h1⟩ | ⟨hmod, _⟩
        · omega
        · exact absurd hc hmod
      · refine hJk false m ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
        rcases hmode with ⟨hmod, _⟩ | ⟨_, h2⟩
        · exfalso; rw [hmod] at hc; revert hc; decide
        · exact h2

private theorem full_viv_sort_fid_wp_aux (Γ : Env)
    (hSort2 : Γ.Has "full_viv_sort2_fid" Spec.fullVivSort2FidSpec)
    (c : FullCfg) (F0 : CNF Nat) (s : FullState) (bn : BitVec 64) (m : Mem 64)
    (Q : Post []) (X : XPost) (R : Mem 64 → Prop) (hsp : FullSparseInv c F0 s)
    (hbn_le : bn.toNat ≤ c.red_cap)
    (hmem : ∀ k < bn.toNat, (s.scratch.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ rr' scr' m', rr'.length = c.red_cap → scr'.length = c.scratch_cap →
      (∀ k < bn.toNat, (rr'[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) →
      (FullMem c (sortState s rr' scr') ⋆ R) m' → Q () m') :
    Func.wp Γ full_viv_sort_fid_body (c.hdr, bn, ()) m Q X := by
  have hred_bound := c.hred; unfold dimacsBound at hred_bound
  have hscr_bound := c.hscr; unfold dimacsBound at hscr_bound
  have hmv_bound := c.hmaxv; unfold dimacsBound at hmv_bound
  have hm0 : (FullMem c (sortState s s.scratch.red_refs s.scratch.scratch_buf) ⋆ R) m := by
    rwa [sortState_self]
  unfold Func.wp full_viv_sort_fid_body
  viv_to_group
  · exact hQ s.scratch.red_refs s.scratch.scratch_buf m
      hsp.1.lengths.scratch_ok.red_refs_len hsp.1.lengths.scratch_ok.scratch_buf_len hmem hm0
  · viv_call hSort2
    refine ⟨c, F0, s, R, rfl, hsp, hbn_le, Or.inl ⟨rfl, ?_⟩, hmem, hm, ?_⟩
    · have hdiv : (BitVec.ofNat 64 c.red_cap / 3#64).toNat = c.red_cap / 3 := by
        rw [BitVec.toNat_udiv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; rfl
      have hle : bn.toNat ≤ c.red_cap / 3 := hdiv ▸ hc
      omega
    · intro rr' scr' m' hrr' hscr' hmem' hm'
      fast_line
      rw [← sortState_eq] at hm'
      exact hQ rr' scr' m' hrr' hscr' hmem' hm'
  · viv_call hSort2
    refine ⟨c, F0, s, R, rfl, hsp, hbn_le, Or.inr ⟨rfl, ?_⟩, hmem, hm, ?_⟩
    · have hshr : (BitVec.ofNat 64 c.scratch_cap >>> 1#64).toNat = c.scratch_cap / 2 := by
        simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
          Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64)]
      have hle : bn.toNat ≤ c.scratch_cap / 2 := hshr ▸ hc
      omega
    · intro rr' scr' m' hrr' hscr' hmem' hm'
      fast_line
      rw [← sortState_eq] at hm'
      exact hQ rr' scr' m' hrr' hscr' hmem' hm'
  · refine wp_join_state0 (α := Bool)
      (fun useRR m_u =>
        m_u = m ∧
        ((useRR = true ∧ bn.toNat + bn.toNat ≤ c.red_cap) ∨
         (useRR = false ∧ c.red_cap / 2 < bn.toNat ∧ bn.toNat ≤ c.scratch_cap)))
      ?_ ?_
    · intro _ useRR m_u ⟨hmu, hbound1⟩
      subst m_u
      have hbn1_64 : bn.toNat + bn.toNat < 2 ^ 64 := by
        rcases hbound1 with ⟨_, h1⟩ | ⟨_, _, h2⟩ <;> omega
      viv_to_group
      refine wp_join_state1 (t := i64) (α := Bool) (fun st => sortKeyPtr c bn st)
        (fun useRR' mk =>
          mk = m ∧
          ((useRR' = true ∧ bn.toNat + bn.toNat ≤ c.red_cap) ∨
           (useRR' = false ∧ bn.toNat ≤ c.scratch_cap)))
        ?_ ?_
      · rintro _ useRR' mk ⟨hmk, hbound'⟩
        subst mk
        viv_to_group
        refine wp_while_state1 (α := BitVec 64 × List (BitVec 32) × List (BitVec 32))
          (fun st => st.1) (fun st => bn.toNat - st.1.toNat)
          (fun (i, rri, scri) mi => SortInv c s R bn i rri scri mi) ?_ ?_
        · intro Ji hJi; fast_line
          exact hJi (0#64, s.scratch.red_refs, s.scratch.scratch_buf) m
            ⟨Nat.zero_le _, hsp.1.lengths.scratch_ok.red_refs_len,
             hsp.1.lengths.scratch_ok.scratch_buf_len, hmem, hm0⟩
        · rintro Ji ⟨i, rri, scri⟩ mi ⟨hi_le, hrr_len, hscr_len, hrr_mem, hm_i⟩ ihi
          viv_steps
          · have hi_lt : i.toNat < bn.toNat := hc
            have hcr_mem := sort_rr_get_mem (by omega) hi_lt hrr_mem
            have hcr_b := sort_cref_bounds hsp hcr_mem
            viv_to_group
            refine wp_while_state (α := BitVec 32 × BitVec 32 × BitVec 32)
              (fun st => (st.1, st.2.1, st.2.2, ()))
              (fun st =>
                (s.core.arena[(rri[i.toNat]'(by omega)).toNat + 2]'(hcr_b.2.2.2.2.1)).toNat -
                  st.2.2.toNat)
              (fun (_, _, u) ml =>
                ml = mi ∧
                u.toNat ≤
                  (s.core.arena[(rri[i.toNat]'(by omega)).toNat + 2]'(hcr_b.2.2.2.2.1)).toNat)
              ?_ ?_
            · intro Jl hJl; fast_line
              exact hJl (0xFFFFFFFF#32, 0#32, 0#32) mi ⟨rfl, Nat.zero_le _⟩
            · rintro Jl ⟨m0, k0, u⟩ ml ⟨hml, hu_le⟩ ihl
              subst ml
              viv_steps
              · have hu_lt : u.toNat <
                    (s.core.arena[(rri[i.toNat]'(by omega)).toNat + 2]'(hcr_b.2.2.2.2.1)).toNat :=
                  u_loop_lt_sz' (_hc_len := by have := hcr_b.1; have := hcr_b.2.2.1; omega) hc
                have hlit_lt : (BitVec.setWidth 64 rri[i.toNat] + 3#64 +
                    BitVec.setWidth 64 u).toNat < s.core.arena.length := by
                  have := hcr_b.2.2.2.2.2; bv_omega
                viv_to_group
                refine wp_join_state1 (t := i32) (α := BitVec 32) (fun v => v)
                  (fun _ mw => mw = mi) ?_ ?_
                · rintro _ w mw hmw; subst mw
                  viv_to_group
                  refine wp_join_state (α := BitVec 32 × BitVec 32) (fun st => (st.1, st.2, ()))
                    (fun _ mu => mu = mi) ?_ ?_
                  · rintro _ ⟨m0', k0'⟩ mu hmu; subst mu
                    fast_line
                    have hst := bv32_succ_le hu_lt
                    exact ihl (m0', k0', u + 1#32) mi hst.2 ⟨rfl, hst.1⟩
                  · intro Ju hJu
                    viv_steps <;> exact hJu (_, _) mi rfl
                · intro Jw hJw
                  dsimp only [sortState_core]
                  exact sort_tarjan_guard_wp _ Jw (fun v => hJw v mi rfl) hsp hm_i
              · apply sort_key_store_wp hrr_len hscr_len hbound' (off := i)
                  (by omega) hbn1_64 hrr_mem hm_i
                intro rr1 scr1 m1 hrr1 hscr1 hrr1_mem hm1
                fast_line
                have hst := bv64_succ_le hi_lt
                exact ihi (i + 1#64, rr1, scr1) m1 hst.2 ⟨hst.1, hrr1, hscr1, hrr1_mem, hm1⟩
          · fast_line
            viv_to_group
            refine wp_while_state1 (α := BitVec 64) (fun st => st)
              (fun st => bn.toNat - st.toNat)
              (fun g mg => mg = mi ∧ 0 < g.toNat ∧ g.toNat ≤ bn.toNat) ?_ ?_
            · intro Jg hJg; fast_line
              exact hJg 1#64 mi ⟨rfl, by decide, by bv_omega⟩
            · rintro Jg g mg ⟨hmg, hg_pos, hg_le⟩ ihg
              subst mg
              c0_hsplit
              · have hg_step := knuth_gap_step bn.isLt hc
                exact ihg (g * 3#64 + 1#64) mi (by omega) ⟨rfl, by omega, hg_step.1⟩
              · viv_to_group
                refine wp_while_state1 (α := BitVec 64 × List (BitVec 32) × List (BitVec 32))
                  (fun st => st.1) (fun st => st.1.toNat)
                  (fun (gap, rrg, scrg) mgg => SortInv c s R bn gap rrg scrg mgg) ?_ ?_
                · intro Jsh hJsh; fast_line
                  exact hJsh (g, rri, scri) mi ⟨hg_le, hrr_len, hscr_len, hrr_mem, hm_i⟩
                · rintro Jsh ⟨gap, rrg, scrg⟩ mgg
                    ⟨hgap_le, hrrg, hscrg, hrrg_mem, hm_gg⟩ ihsh
                  c0_hsplit
                  · have hgap_pos : 0 < gap.toNat := by simpa using hc
                    viv_to_group
                    refine wp_while_state1 (α := BitVec 64 × List (BitVec 32) × List (BitVec 32))
                      (fun st => st.1) (fun st => bn.toNat - st.1.toNat)
                      (fun (i2, rrl, scrl) mll => SortInv c s R bn i2 rrl scrl mll) ?_ ?_
                    · intro Jl hJl; fast_line
                      exact hJl (gap, rrg, scrg) mgg ⟨hgap_le, hrrg, hscrg, hrrg_mem, hm_gg⟩
                    · rintro Jl ⟨i2, rrl, scrl⟩ mll ⟨hi2_le, hrrl, hscrl, hrrl_mem, hm_ll⟩ ihl
                      viv_steps
                      · have hi2_lt : i2.toNat < bn.toNat := hc
                        apply sort_key_load_wp hrrl hscrl hbound' (off := i2)
                          (by omega) hbn1_64 hm_ll
                        intro lk0
                        have hcr2_mem := sort_rr_get_mem (by omega) hi2_lt hrrl_mem
                        have hcr2_b := sort_cref_bounds hsp hcr2_mem
                        viv_to_group
                        refine wp_join_state1 (t := i32) (α := BitVec 32) (fun v => v)
                          (fun _ m4 => m4 = mll) ?_ ?_
                        · rintro _ lt0 m4 hm4; subst m4
                          viv_to_group
                          refine wp_join_state1 (t := i64)
                            (α := BitVec 64 × List (BitVec 32) × List (BitVec 32))
                            (fun st => st.1)
                            (fun (jf, rrj, scrj) mj =>
                              jf.toNat < bn.toNat ∧ SortInv c s R bn jf rrj scrj mj)
                            ?_ ?_
                          · rintro _ ⟨jf, rrj, scrj⟩ mj
                              ⟨hjf_lt, _, hrrj, hscrj, hrrj_mem, hm_j⟩
                            fast_line
                            apply sort_rr_store_wp (refs := fun x => x ∈ fullArenaClauseRefs s)
                              (bn := bn) hjf_lt (by omega) hrrj_mem hcr2_mem hm_j
                            intro rrj' mj' hrrj' hmem' hm_j'
                            fast_line
                            apply sort_key_store_wp (hrrj'.trans hrrj) hscrj hbound' (off := jf)
                              (by omega) hbn1_64 hmem' hm_j'
                            intro rrk1 scrk1 mk1 hrrk1 hscrk1 hrrk1_mem hm_k1
                            fast_line
                            have hst := bv64_succ_le hi2_lt
                            exact ihl (i2 + 1#64, rrk1, scrk1) mk1 hst.2
                              ⟨hst.1, hrrk1, hscrk1, hrrk1_mem, hm_k1⟩
                          · intro Jbrk hJbrk
                            viv_to_group
                            refine wp_while_state1
                              (α := BitVec 64 × List (BitVec 32) × List (BitVec 32))
                              (fun st => st.1) (fun st => st.1.toNat)
                              (fun (j, rrj, scrj) mj =>
                                j.toNat < bn.toNat ∧ SortInv c s R bn j rrj scrj mj)
                              ?_ ?_
                            · intro Jj hJj; fast_line
                              exact hJj (i2, rrl, scrl) mll
                                ⟨hi2_lt, hi2_le, hrrl, hscrl, hrrl_mem, hm_ll⟩
                            · rintro Jj ⟨j, rrj, scrj⟩ mj
                                ⟨hj_lt, hj_le, hrrj, hscrj, hrrj_mem, hm_j⟩ ihj
                              viv_steps
                              · have hjg : gap.toNat ≤ j.toNat := by bv_omega
                                have hsub := bv64_sub_dec hj_lt hgap_pos hjg
                                have hdiff_lt := hsub.1
                                apply sort_key_load_wp hrrj hscrj hbound' (off := j - gap)
                                  (by omega) hbn1_64 hm_j
                                intro uk0
                                have hucr_mem := sort_rr_get_mem (by omega) hdiff_lt hrrj_mem
                                have hucr_b := sort_cref_bounds hsp hucr_mem
                                viv_to_group
                                refine wp_join_state1 (t := i32) (α := BitVec 32) (fun v => v)
                                  (fun _ m5 => m5 = mj) ?_ ?_
                                · rintro _ ut0 m5 hm5; subst m5
                                  viv_to_group
                                  refine wp_join_group (fun _ m6 => m6 = mj) ?_ ?_
                                  · intro _ _ m6 hm6; subst m6
                                    viv_to_group
                                    refine wp_join_group (fun _ m7 => m7 = mj) ?_ ?_
                                    · intro _ _ m7 hm7; subst m7
                                      fast_line
                                      have hu_mem := sort_rr_get_mem (by omega) hdiff_lt hrrj_mem
                                      apply sort_rr_store_wp
                                        (refs := fun x => x ∈ fullArenaClauseRefs s)
                                        (bn := bn) hj_lt (by omega) hrrj_mem hu_mem hm_j
                                      intro rrj' mj' hrrj' hmem' hm_j'
                                      fast_line
                                      apply sort_key_store_wp (hrrj'.trans hrrj) hscrj hbound'
                                        (off := j) (by omega) hbn1_64 hmem' hm_j'
                                      intro rrs1 scrs1 ms1 hrrs1 hscrs1 hrrs1_mem hms1
                                      fast_line
                                      exact ihj (j - gap, rrs1, scrs1) ms1 hsub.2
                                        ⟨hdiff_lt, by omega, hrrs1, hscrs1, hrrs1_mem, hms1⟩
                                    · intro Jgo2 hJgo2; viv_steps <;> first
                                      | exact hJgo2 () mj rfl
                                      | exact hJbrk (j, rrj, scrj) mj
                                          ⟨hj_lt, hj_le, hrrj, hscrj, hrrj_mem, hm_j⟩
                                  · intro Jgo1 hJgo1; viv_steps <;> first
                                    | exact hJgo1 () mj rfl
                                    | exact hJbrk (j, rrj, scrj) mj
                                        ⟨hj_lt, hj_le, hrrj, hscrj, hrrj_mem, hm_j⟩
                                · intro Jut0 hJut0
                                  dsimp only [sortState_core]
                                  exact sort_tarjan_guard_wp _ Jut0
                                    (fun v => hJut0 v mj rfl) hsp hm_j
                              · exact hJbrk (j, rrj, scrj) mj
                                  ⟨hj_lt, hj_le, hrrj, hscrj, hrrj_mem, hm_j⟩
                        · intro Jlt0 hJlt0
                          dsimp only [sortState_core]
                          exact sort_tarjan_guard_wp _ Jlt0 (fun v => hJlt0 v mll rfl) hsp hm_ll
                      · have hgap_pos' : 0 < gap.toNat := by omega
                        have hdiv_le : (gap / 3#64).toNat ≤ bn.toNat := by
                          have hle := knuth_gap_div3 hgap_pos'; omega
                        exact ihsh (gap / 3#64, rrl, scrl) mll (knuth_gap_div3 hgap_pos')
                          ⟨hdiv_le, hrrl, hscrl, hrrl_mem, hm_ll⟩
                  · exact hQ rrg scrg mgg hrrg hscrg hrrg_mem hm_gg
      · intro Jk hJk
        have hshr : (BitVec.ofNat 64 c.red_cap >>> 1).toNat = c.red_cap / 2 := by
          rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; rfl
        viv_steps
        · refine hJk true m ⟨rfl, Or.inl ⟨rfl, ?_⟩⟩
          rcases hbound1 with ⟨_, h1⟩ | ⟨_, hgt, _⟩
          · exact h1
          · exfalso; rw [hshr] at hc; omega
        · refine hJk false m ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
          rcases hbound1 with ⟨_, _⟩ | ⟨_, _, h2⟩
          · exfalso; rw [hshr] at hc; omega
          · exact h2
    · intro Ju hJu
      viv_steps
      · viv_to_group
        refine wp_while_state (ts := [i64, i64])
          (α := BitVec 64 × BitVec 64 × List (BitVec 32) × List (BitVec 32))
          (fun st => (st.1, st.2.1, ())) (fun st => st.2.1.toNat - st.1.toNat)
          (fun (lo, hi, rr, scr) mp =>
            lo.toNat ≤ bn.toNat ∧ hi.toNat < bn.toNat ∧ SortInv c s R bn 0#64 rr scr mp)
          ?_ ?_
        · intro J1 hJ1; fast_line
          exact hJ1 (0#64, bn - 1#64, s.scratch.red_refs, s.scratch.scratch_buf) m
            ⟨Nat.zero_le _, by bv_omega, Nat.zero_le _,
             hsp.1.lengths.scratch_ok.red_refs_len,
             hsp.1.lengths.scratch_ok.scratch_buf_len, hmem, hm0⟩
        · rintro J1 ⟨lo, hi, rr, scr⟩ mp ⟨hlo_le, hhi_lt, _, hrr_len, hscr_len, hrr_mem, hm_p⟩ ih1
          (try simp only [Blocks.get]; step_lets; rw [wp_jnz]; try dsimp only [vals, Arg.val]
           refine ⟨fun hc => ?_, fun hc => ?_⟩)
          · have hlo_hi : lo.toNat < hi.toNat := by
              rw [BitVec.ult] at hc
              exact of_decide_eq_true hc
            have hlo_lt : lo.toNat < bn.toNat := by omega
            have hlo_rr_lt : lo.toNat < rr.length := by omega
            have hlo_mem := sort_rr_get_mem (by omega) hlo_lt hrr_mem
            have hlo_b := sort_cref_bounds hsp hlo_mem
            step_lets
            try dsimp only
            apply wp_load_of (a := Arg.var _) (c0_load_sort_red_refs hlo_rr_lt hm_p)
            try dsimp only
            refine wp_join_state (ts := [i64, i64])
              (α := BitVec 64 × BitVec 64 × List (BitVec 32) × List (BitVec 32))
              (fun st => (st.1, st.2.1, ()))
              (fun (lo', hi', rr', scr') m2 =>
                lo'.toNat ≤ bn.toNat ∧ hi'.toNat < bn.toNat ∧
                hi'.toNat - lo'.toNat < hi.toNat - lo.toNat ∧
                SortInv c s R bn 0#64 rr' scr' m2)
              ?_ ?_
            · rintro _ ⟨lo', hi', rr', scr'⟩ m2 ⟨hlo', hhi', hdec, hS'⟩
              fast_line
              exact ih1 (lo', hi', rr', scr') m2 hdec ⟨hlo', hhi', hS'⟩
            · intro J2 hJ2
              have hlo_ar : (BitVec.setWidth 64 (rr[lo.toNat]'(by omega))).toNat <
                  s.core.arena.length := by have := hlo_b.1; have := hlo_b.2.1; bv_omega
              fast_line
              try dsimp only
              try (apply wp_load_of (a := Arg.var _) (c0_load_sort_arena hlo_ar hm_p))
              have hlo1 : (lo + 1#64).toNat = lo.toNat + 1 := by bv_omega
              have hhi1 : (hi - 1#64).toNat = hi.toNat - 1 := by
                have := BitVec.isLt hi; bv_omega
              step_jnz
              · fast_line
                exact hJ2 (lo + 1#64, hi, rr, scr) mp
                  ⟨by bv_omega, hhi_lt, by (try rw [hlo1]); (try rw [hhi1]); omega,
                   Nat.zero_le _, hrr_len, hscr_len, hrr_mem, hm_p⟩
              · have hhi_mem := sort_rr_get_mem (by omega) hhi_lt hrr_mem
                have hhi_b := sort_cref_bounds hsp hhi_mem
                step_lets
                try dsimp only
                apply wp_load_of (a := Arg.var _) (c0_load_sort_red_refs (by omega) hm_p)
                try dsimp only
                refine wp_join_state (ts := [i64, i64])
                  (α := BitVec 64 × BitVec 64 × List (BitVec 32) × List (BitVec 32))
                  (fun st => (st.1, st.2.1, ()))
                  (fun (lo', hi', rr', scr') m3 =>
                    lo'.toNat ≤ bn.toNat ∧ hi'.toNat < bn.toNat ∧
                    hi'.toNat - lo'.toNat < hi.toNat - lo.toNat ∧
                    SortInv c s R bn 0#64 rr' scr' m3)
                  ?_ ?_
                · rintro _ ⟨lo', hi', rr', scr'⟩ m3 ⟨hlo', hhi', hdec, hS'⟩
                  fast_line
                  exact hJ2 (lo', hi', rr', scr') m3 ⟨hlo', hhi', hdec, hS'⟩
                · intro J3 hJ3
                  have hhi_ar : (BitVec.setWidth 64 (rr[hi.toNat]'(by omega))).toNat <
                      s.core.arena.length := by have := hhi_b.1; have := hhi_b.2.1; bv_omega
                  fast_line
                  try dsimp only
                  try (apply wp_load_of (a := Arg.var _) (c0_load_sort_arena hhi_ar hm_p))
                  step_jnz
                  · fast_line
                    exact hJ3 (lo, hi - 1#64, rr, scr) mp
                      ⟨hlo_le, by bv_omega, by (try rw [hlo1]); (try rw [hhi1]); omega,
                       Nat.zero_le _, hrr_len, hscr_len, hrr_mem, hm_p⟩
                  · apply sort_rr_store_wp (refs := fun x => x ∈ fullArenaClauseRefs s)
                      (bn := bn) hlo_lt (by omega) hrr_mem hhi_mem hm_p
                    intro rr1 m1 hrr1 hmem1 hm1
                    fast_line
                    apply sort_rr_store_wp (refs := fun x => x ∈ fullArenaClauseRefs s)
                      (bn := bn) hhi_lt (by omega) hmem1 hlo_mem hm1
                    intro rr2 m2 hrr2 hmem2 hm2
                    fast_line
                    exact hJ3 (lo + 1#64, hi - 1#64, rr2, scr) m2
                      ⟨by bv_omega, by bv_omega, by (try rw [hlo1]); (try rw [hhi1]); omega,
                       Nat.zero_le _, by omega, hscr_len, hmem2, hm2⟩
          · exact hQ rr scr mp hrr_len hscr_len hrr_mem hm_p
      · rename_i _ hgt_rc
        refine hJu false m ⟨rfl, Or.inr ⟨rfl, ?_, ?_⟩⟩
        · have hshr : (BitVec.ofNat 64 c.red_cap >>> 1).toNat = c.red_cap / 2 := by
            rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; rfl
          exact hshr ▸ hgt_rc
        · omega
      · refine hJu true m ⟨rfl, Or.inl ⟨rfl, ?_⟩⟩
        have hshr : (BitVec.ofNat 64 c.red_cap >>> 1).toNat = c.red_cap / 2 := by
          rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; rfl
        rw [hshr] at hc; omega

public section

theorem full_viv_sort2_fid_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullVivSort2FidSpec a m Q X →
      Func.wp Γ full_viv_sort2_fid_body a m Q X := by
  intro ⟨h, bn, mode, ⟨⟩⟩ m Q X hs
  rcases hs with ⟨c, F0, s, R, rfl, hsp, hbn_le, hmode, hmem, hm, hQ⟩
  refine full_viv_sort2_fid_wp_aux Γ c F0 s bn mode m Q X R hsp hbn_le ?_ hmem hm
    (fun rr' scr' m' hrr' hscr' hmem' hm' => ?_)
  · rcases hmode with ⟨rfl, h1⟩ | ⟨rfl, h2⟩
    · exact Or.inl ⟨rfl, by omega⟩
    · exact Or.inr ⟨by decide, by omega⟩
  · rw [sortState_eq] at hm'
    exact hQ rr' scr' m' hrr' hscr' hmem' hm'

theorem full_viv_sort_fid_wp (Γ : Env)
    (hSort2 : Γ.Has "full_viv_sort2_fid" Spec.fullVivSort2FidSpec) :
    ∀ a m Q X, Spec.fullVivSortFidSpec a m Q X →
      Func.wp Γ full_viv_sort_fid_body a m Q X := by
  intro ⟨h, bn, ⟨⟩⟩ m Q X hs
  rcases hs with ⟨c, F0, s, R, rfl, hsp, hbn_le, hmem, hm, hQ⟩
  exact full_viv_sort_fid_wp_aux Γ hSort2 c F0 s bn m Q X R hsp hbn_le hmem hm
    (fun rr' scr' m' hrr' hscr' hmem' hm' => by
      rw [sortState_eq] at hm'
      exact hQ rr' scr' m' hrr' hscr' hmem' hm')

end

end LeanQbe.T.Examples.Kissat.Proof.Vivify
