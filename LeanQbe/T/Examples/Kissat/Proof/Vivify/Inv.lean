/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.InvArena

/-!
# Shared BFS Deduction & Promotion Invariants (`Proof.Vivify.Inv`)

Provides canonical (`0` legacy `Full*` imports) invariants and soundness proofs for
`full_viv_deduce_m6` (`VivQueueOk`, `VivClosedOk`, `VivOutOk`, `VivSeedOk`,
`deduce_phase2_sound`, `S13ArPres`, `S13SubRefOk`, `deducePushExpr`, `deduce_push_wp`)
plus shared watch/clause call combinators
(`watch2_calls_wp`, `addUnit_call_wp`, `unwatch2_state_pack`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Vivify

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Vivify.VivTactics
open Kraken.Bedrock2.Test

public section

/-! ## 1. Simplify / Commit Watch & Clause Call Helpers -/

theorem unwatch2_state_pack {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s_in : FullState} {R : Mem 64 → Prop} {m : Mem 64} {cref : Nat} {old_sz hdr : BitVec 32}
    (hsp : FullSparseInv c F0 s_in) (hw : FullWitnessInv c F0 F_cur s_in.core)
    (hm : (FullMem c s_in ⋆ R) m) (hng : fullArenaClauseGarb s cref = false)
    (hsz_eq : fullArenaClauseSize s cref = old_sz.toNat) (hhdr_eq : hdr = fullArenaHdr s cref)
    (hs_ar : s_in.core.arena = s.core.arena) (hs_v : s_in.core.vals = s.core.vals)
    (hs_cv : s_in.core.cur_vars = s.core.cur_vars) (hs_al : s_in.core.arena_len = s.core.arena_len)
    (hs_l0 : s_in.core.cur_level = 0) (hs_pr : s_in.core.probing = s.core.probing)
    (hs_fu : s_in.core.fuel = s.core.fuel) (hws2 : s_in.scratch.work_stk2 = s.scratch.work_stk2)
    (hrr : s_in.scratch.red_refs = s.scratch.red_refs)
    (htr : s_in.scratch.tarjan_reach = s.scratch.tarjan_reach) :
    ∃ s2 : FullState, s2.core.arena = s.core.arena ∧ s2.core.vals = s.core.vals ∧
      s2.scratch.work_stk2 = s.scratch.work_stk2 ∧
      s2.scratch.red_refs = s.scratch.red_refs ∧
      s2.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
      VivMetaEq s s2 ∧
      fullArenaClauseRefs s2 = fullArenaClauseRefs s ∧ fullArenaClauseGarb s2 cref = false ∧
      fullArenaClauseSize s2 cref = old_sz.toNat ∧ fullArenaHdr s2 cref = hdr ∧
      FullSparseInvW c F0 F_cur s2 ∧ (FullMem c s2 ⋆ R) m :=
  ⟨s_in, hs_ar, hs_v, hws2, hrr, htr, ⟨hs_al, hs_cv, hs_l0, hs_pr, hs_fu⟩,
    by unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [hs_ar, hs_al],
    by unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [hs_ar]; exact hng,
    by unfold fullArenaClauseSize fullArenaClauseSizeCore; rw [hs_ar]; exact hsz_eq,
    by unfold fullArenaHdr fullArenaHdrCore; rw [hs_ar]; exact hhdr_eq.symm,
    ⟨hsp.1.lengths, hw, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2⟩, hm⟩

private theorem viv_watch2_pre_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {blk cref : BitVec 32} (hsp : FullSparseInvW c F0 F_cur s)
    (hcref : cref ≠ 0xFFFFFFFF#32) :
    s.LengthsOk c ∧ WatchStackLayout s.core ∧
    ((2#32 : BitVec 32).toNat = 1 → (blk &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32) ∧
    ((2#32 : BitVec 32).toNat = 2 →
      (blk &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 ∧ cref ≠ 0xFFFFFFFF#32) :=
  ⟨hsp.1, viv_watchLayout_of_sparse hsp, fun h => absurd h (by decide),
    fun _ => ⟨(bv32_mask_lo31_props _).2, hcref⟩⟩

abbrev watch2Expr (h : Val i64) (cref la lb : Val i32)
    (k_ok k_oom : Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
    fvOp (OpCode.add i64) (Arg.var h, Arg.imm 760, ()) fun p =>
    Expr.store (Arg.imm (t := i64) 1) (Arg.var p.fst) k_oom) Blocks.nil) fun Js =>
  fvOp (OpCode.and i32) (Arg.var lb, Arg.imm 2147483647, ()) fun p =>
  Expr.call "full_watch_push" (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
    (Arg.var h, Arg.var la, Arg.var p.fst, Arg.var cref, Arg.imm 2, ()) fun p =>
  Expr.jnz (Arg.var p.fst) (fvOp (OpCode.and i32) (Arg.var la, Arg.imm 2147483647, ()) fun p =>
    Expr.call "full_watch_push" (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
      (Arg.var h, Arg.var lb, Arg.var p.fst, Arg.var cref, Arg.imm 2, ()) fun p =>
    Expr.jnz (Arg.var p.fst) k_ok (Expr.jump Js.fst ())) (Expr.jump Js.fst ())

theorem watch2_calls_wp (Γ : Env)
    (hWatchPush : Γ.Has "full_watch_push" fullWatchPushSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s_f : FullState}
    {R : Mem 64 → Prop} {cref la lb : Val i32} {k_ok k_oom : Expr Val Cont [i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} (hsp : FullSparseInvW c F0 F_cur s_f)
    (hcref : cref.toNat < 0x80000000) (href : cref.toNat ∈ fullArenaClauseRefs s)
    (hsref : fullArenaClauseRefs s_f = fullArenaClauseRefs s)
    (hmeta : s_f.core.arena_len = s.core.arena_len ∧ s_f.core.cur_vars = s.core.cur_vars ∧
      s_f.core.probing = s.core.probing ∧ s_f.core.fuel = s.core.fuel)
    (hm : (FullMem c s_f ⋆ R) m)
    (hok : ∀ s' m', FullSparseInvW c F0 F_cur s' → s'.core.arena = s_f.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.cur_vars = s.core.cur_vars →
      s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
      s'.core.cur_level = s_f.core.cur_level →
      s'.scratch.red_refs = s_f.scratch.red_refs →
      s'.scratch.tarjan_reach = s_f.scratch.tarjan_reach →
      fullArenaClauseRefs s' = fullArenaClauseRefs s → (FullMem c s' ⋆ R) m' → wp Γ Q X k_ok m')
    (hoom : ∀ s' m', FullSparseInvW c F0 F_cur s' → s'.core.arena = s_f.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.cur_vars = s.core.cur_vars →
      s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
      s'.core.cur_level = s_f.core.cur_level →
      s'.scratch.red_refs = s_f.scratch.red_refs →
      s'.scratch.tarjan_reach = s_f.scratch.tarjan_reach →
      fullArenaClauseRefs s' = fullArenaClauseRefs s → (FullMem c s' ⋆ R) m' → wp Γ Q X k_oom m') :
    wp Γ Q X (watch2Expr c.hdr cref la lb k_ok k_oom) m := by
  have hne : cref ≠ 0xFFFFFFFF#32 := bv32_ne_sentinel_of_lt hcref
  dsimp only [watch2Expr, fvOp]
  refine wp_join_group
    (fun _ m' => ∃ s' : FullState, FullSparseInvW c F0 F_cur s' ∧
      s'.core.arena = s_f.core.arena ∧
      s'.core.arena_len = s.core.arena_len ∧ s'.core.cur_vars = s.core.cur_vars ∧
      s'.core.probing = s.core.probing ∧ s'.core.fuel = s.core.fuel ∧
      s'.core.cur_level = s_f.core.cur_level ∧
      s'.scratch.red_refs = s_f.scratch.red_refs ∧
      s'.scratch.tarjan_reach = s_f.scratch.tarjan_reach ∧
      fullArenaClauseRefs s' = fullArenaClauseRefs s ∧ (FullMem c s' ⋆ R) m')
    (fun _ _ m' ⟨s', hsp', har', hal', hcv', hpr', hfu', hcl', hrr', htr', href', hm'⟩ => by
      viv_steps
      exact hoom _ _ (viv_with_oomW hsp' 1#64) har' hal' hcv' hpr' hfu' hcl' hrr' htr' href'
        (by assumption))
    (fun Js hJs => ?_)
  viv_steps; viv_call hWatchPush
  obtain ⟨hl1, lay1, hp1_1, hp1_2⟩ := viv_watch2_pre_ok (blk := lb) hsp hne
  refine ⟨c, s_f, R, rfl, hl1, lay1, hp1_1, hp1_2, hm,
    fun ok1 wvec3 wstk3 wlen3 wu3 wsort3 m4 hlen4 hlay4 hoth4 hok1_t hok1_f hm4 => ?_⟩
  have hsp4 := fullWatchPush_large_preserves_sparseInvW hsp (bv32_mask_lo31_props lb).1 hcref
    (by rw [hsref]; exact href) hlen4 hlay4 hoth4
    (fun h => let t := hok1_t h; ⟨t.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2 rfl⟩)
    (fun h => (hok1_f h).1)
  viv_steps
  · viv_call hWatchPush
    obtain ⟨hl2, lay2, hp2_1, hp2_2⟩ := viv_watch2_pre_ok (blk := la) hsp4 hne
    refine ⟨c, _, R, rfl, hl2, lay2, hp2_1, hp2_2, hm4,
      fun ok2 wvec4 wstk4 wlen4 wu4 wsort4 m5 hlen5 hlay5 hoth5 hok2_t hok2_f hm5 => ?_⟩
    have hsp5 := fullWatchPush_large_preserves_sparseInvW hsp4 (bv32_mask_lo31_props la).1 hcref
      (by change cref.toNat ∈ fullArenaClauseRefs s_f; rw [hsref]; exact href) hlen5 hlay5 hoth5
      (fun h => let t := hok2_t h; ⟨t.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2 rfl⟩)
      (fun h => (hok2_f h).1)
    viv_steps
    · exact hok _ m5 hsp5 rfl hmeta.1 hmeta.2.1 hmeta.2.2.1 hmeta.2.2.2 rfl rfl rfl hsref hm5
    · exact hJs () m5 ⟨_, hsp5, rfl, hmeta.1, hmeta.2.1, hmeta.2.2.1, hmeta.2.2.2,
        rfl, rfl, rfl, hsref, hm5⟩
  · exact hJs () m4 ⟨_, hsp4, rfl, hmeta.1, hmeta.2.1, hmeta.2.2.1, hmeta.2.2.2,
      rfl, rfl, rfl, hsref, hm4⟩

/-! ## 2. Deduce BFS Invariants & Soundness -/

/-- Arena-promotion preservation invariant across `full_viv_recompute_promote_fid` calls
inside `full_viv_deduce_m6`. -/
@[expose] def S13ArPres (s0 s : FullState) : Prop :=
  fullArenaClauseRefs s = fullArenaClauseRefs s0 ∧
  (∀ r ∈ fullArenaClauseRefs s0,
    fullArenaClauseGarb s r = fullArenaClauseGarb s0 r ∧
    fullArenaClauseSize s r = fullArenaClauseSize s0 r ∧
    fullArenaClauseLits s r = fullArenaClauseLits s0 r)

theorem s13ArPres_refl (s : FullState) : S13ArPres s s :=
  ⟨rfl, fun _ _ => ⟨rfl, rfl, rfl⟩⟩

theorem s13ArPres_trans {s0 s1 s2 : FullState} (h1 : S13ArPres s0 s1) (h2 : S13ArPres s1 s2) :
    S13ArPres s0 s2 :=
  ⟨h2.1.trans h1.1, fun r hr =>
    let ⟨hg1, hs1, hl1⟩ := h1.2 r hr
    let ⟨hg2, hs2, hl2⟩ := h2.2 r (h1.1.symm ▸ hr)
    ⟨hg2.trans hg1, hs2.trans hs1, hl2.trans hl1⟩⟩

theorem s13ArPres_with_fields {s0 s1 : FullState} (h : S13ArPres s0 s1)
    {mrk1 lm1 : List (BitVec 8)} {ws1 ws2 : List (BitVec 32)} {asz rsz : BitVec 64} :
    S13ArPres s0
      { s1 with
        core := { s1.core with mrk := mrk1, lit_mark := lm1 }
        scratch := { s1.scratch with
          work_stk1 := ws1, work_stk2 := ws2, ant_sz := asz, res_sz := rsz } } := by
  rcases h with ⟨hrefs, hpres⟩
  refine ⟨?_, fun r hr => ?_⟩
  · unfold fullArenaClauseRefs fullArenaClauseRefsCore at hrefs ⊢; exact hrefs
  · exact hpres r hr

@[expose] def S13SubRefOk (s : FullState) (asz : BitVec 64) : Prop :=
  M6SubRefOk s asz ∧
  (asz ≠ 0xFFFFFFFFFFFFFFFF#64 → asz ≠ 0xFFFFFFFFFFFFFFFE#64 →
    asz.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s asz.toNat = false)

theorem s13_subRef_set_ref {s : FullState} {r : BitVec 32}
    (hr : r.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s r.toNat = false) :
    S13SubRefOk s (r.setWidth 64) :=
  ⟨Or.inr (Or.inr (by
    simpa [BitVec.toNat_setWidth,
      (Nat.mod_eq_of_lt (Nat.lt_trans r.isLt (by decide : 2 ^ 32 < 2 ^ 64)))] using hr)),
   fun _ _ => by
     have h : (r.setWidth 64).toNat = r.toNat := by
       rw [BitVec.toNat_setWidth,
         Nat.mod_eq_of_lt (Nat.lt_trans r.isLt (by decide : 2 ^ 32 < 2 ^ 64))]
     rw [h]; exact ⟨hr, hng⟩⟩

theorem s13_subRef_of_pres {s0 s : FullState} {asz : BitVec 64}
    (hpres : S13ArPres s0 s) (h : S13SubRefOk s0 asz) : S13SubRefOk s asz :=
  ⟨by rcases h.1 with rfl | rfl | hr
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (hpres.1.symm ▸ hr)),
   fun h1 h2 =>
     let ⟨hr, hng⟩ := h.2 h1 h2
     ⟨hpres.1.symm ▸ hr, (hpres.2 _ hr).1.symm ▸ hng⟩⟩

theorem s13_noMark_of_sparseW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) : S13SparseInvNoMark c F0 F_cur s :=
  ⟨hsp.1, hsp.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

theorem s13_deduce_finish_sparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : S13SparseInvNoMark c F0 F_cur s)
    {mrk' lm' : List (BitVec 8)} {ws1' ws2' : List (BitVec 32)} {asz' rsz' : BitVec 64}
    (hmrk : mrk'.length = c.max_vars) (hlm : lm'.length = 2 * c.max_vars)
    (hws1 : ws1'.length = 2 * c.max_vars) (hws2 : ws2'.length = 2 * c.max_vars)
    (hmrk_clr : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8)
    (hlm_clr : ∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 = 0#8) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with mrk := mrk', lit_mark := lm' }
        scratch := { s.scratch with
          work_stk1 := ws1', work_stk2 := ws2', ant_sz := asz', res_sz := rsz' } } :=
  ⟨⟨{ hsp.1.core_ok with mrk_len := hmrk, lit_mark_len := hlm },
    { hsp.1.scratch_ok with work_stk1_len := hws1, work_stk2_len := hws2 }⟩,
   { hsp.2.1 with
     arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
     watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   ⟨hmrk_clr, hlm_clr⟩, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2⟩

theorem s13_deduce_state_len {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    {mrk' lm' : List (BitVec 8)} {ws1' ws2' : List (BitVec 32)} {asz' rsz' : BitVec 64}
    (hmrk : mrk'.length = c.max_vars) (hlm : lm'.length = 2 * c.max_vars)
    (hws1 : ws1'.length = 2 * c.max_vars) (hws2 : ws2'.length = 2 * c.max_vars) :
    ({ s with
      core := { s.core with mrk := mrk', lit_mark := lm' }
      scratch := { s.scratch with
        work_stk1 := ws1', work_stk2 := ws2', ant_sz := asz', res_sz := rsz' } } :
      FullState).LengthsOk c :=
  ⟨{ hlen.core_ok with mrk_len := hmrk, lit_mark_len := hlm },
   { hlen.scratch_ok with work_stk1_len := hws1, work_stk2_len := hws2 }⟩

theorem s13_deduce_state_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core)
    {mrk' lm' : List (BitVec 8)} :
    FullWitnessInv c F0 F_cur { s.core with mrk := mrk', lit_mark := lm' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

theorem s13_deduce_state_noMark {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : S13SparseInvNoMark c F0 F_cur s)
    {mrk' lm' : List (BitVec 8)} {ws1' ws2' : List (BitVec 32)} {asz' rsz' : BitVec 64}
    (hmrk : mrk'.length = c.max_vars) (hlm : lm'.length = 2 * c.max_vars)
    (hws1 : ws1'.length = 2 * c.max_vars) (hws2 : ws2'.length = 2 * c.max_vars) :
    S13SparseInvNoMark c F0 F_cur
      { s with
        core := { s.core with mrk := mrk', lit_mark := lm' }
        scratch := { s.scratch with
          work_stk1 := ws1', work_stk2 := ws2', ant_sz := asz', res_sz := rsz' } } :=
  ⟨s13_deduce_state_len hsp.1 hmrk hlm hws1 hws2, s13_deduce_state_witness hsp.2.1,
    hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2⟩

@[expose] def VivQueueOk (c : FullCfg) (s : FullState) (mrk : List (BitVec 8))
    (ws1 : List (BitVec 32)) (qlen : Nat) : Prop :=
  mrk.length = c.max_vars ∧ ws1.length = 2 * c.max_vars ∧ qlen ≤ s.core.cur_vars ∧
  (∀ i < qlen, (ws1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
  ((ws1.take qlen).map BitVec.toNat).Nodup ∧
  (∀ i < qlen,
    0 < (s.core.lvl[(ws1[i]?.getD 0#32).toNat]?.getD 0#32).toNat ∧
    ∃ idx < s.core.trail_end,
      (s.core.trl[idx]?.getD 0#32).toNat / 2 = (ws1[i]?.getD 0#32).toNat) ∧
  (∀ v < s.core.cur_vars, mrk[v]?.getD 0#8 = 1#8 ↔ v ∈ (ws1.take qlen).map BitVec.toNat) ∧
  (∀ v < s.core.cur_vars, mrk[v]?.getD 0#8 = 0#8 ∨ mrk[v]?.getD 0#8 = 1#8) ∧
  (∀ v, s.core.cur_vars ≤ v → v < c.max_vars → mrk[v]?.getD 0#8 = 0#8)

theorem mem_map_take_iff {xs : List (BitVec 32)} {n x : Nat} (hn : n ≤ xs.length) :
    x ∈ (xs.take n).map BitVec.toNat ↔ ∃ i < n, (xs[i]?.getD 0#32).toNat = x := by
  rw [List.mem_map]; constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    have hlt : i < n := by rw [List.length_take] at hi; omega
    exact ⟨i, hlt, by rw [List.getElem_take, List.getElem?_eq_getElem (by omega), Option.getD_some]⟩
  · rintro ⟨i, hi, heq⟩
    refine ⟨xs[i]'(by omega), ?_, ?_⟩
    · rw [List.mem_iff_getElem]
      exact ⟨i, by rw [List.length_take]; omega, by simp [List.getElem_take]⟩
    · rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq

theorem push_queue_lt {c : FullCfg} {s : FullState} {mrk : List (BitVec 8)}
    {ws1 : List (BitVec 32)} {qlen : Nat} (hq : VivQueueOk c s mrk ws1 qlen)
    (hcv : s.core.cur_vars ≤ c.max_vars) {v : Nat} (hv : v < s.core.cur_vars)
    (hm0 : mrk[v]?.getD 0#8 = 0#8) : qlen < s.core.cur_vars := by
  have hql := hq.2.2.1; have hsl := hq.2.1
  have hlen : qlen ≤ ws1.length := by omega
  refine viv_queue_missing_lt hlen hq.2.2.2.1 hq.2.2.2.2.1 hv fun i hi heq => ?_
  have h1 := (hq.2.2.2.2.2.2.1 v hv).mpr ((mem_map_take_iff hlen).mpr ⟨i, hi, heq⟩)
  rw [hm0] at h1; cases h1

theorem push_queue_step {c : FullCfg} {s : FullState} {mrk : List (BitVec 8)}
    {ws1 : List (BitVec 32)} {qlen : Nat} (hq : VivQueueOk c s mrk ws1 qlen)
    (hcv : s.core.cur_vars ≤ c.max_vars) {v : BitVec 32} (hv : v.toNat < s.core.cur_vars)
    (hlvl : 0 < (s.core.lvl[v.toNat]?.getD 0#32).toNat) (hm0 : mrk[v.toNat]?.getD 0#8 = 0#8)
    (htrl : ∃ idx < s.core.trail_end, (s.core.trl[idx]?.getD 0#32).toNat / 2 = v.toNat) :
    let mrk' := mrk.set v.toNat 1#8
    let ws1' := ws1.set qlen v
    qlen < s.core.cur_vars ∧ VivQueueOk c s mrk' ws1' (qlen + 1) ∧
    (∀ j < qlen, ws1'[j]? = ws1[j]?) ∧
    ∀ x, x ∈ (ws1.take qlen).map BitVec.toNat →
      x ∈ (ws1'.take (qlen + 1)).map BitVec.toNat := by
  have hq_lt : qlen < s.core.cur_vars := push_queue_lt hq hcv hv hm0
  have hmrk_len : mrk.length = c.max_vars := hq.1
  have hws1_len : ws1.length = 2 * c.max_vars := hq.2.1
  have hv_mrk : v.toNat < mrk.length := by omega
  have hq_ws1 : qlen < ws1.length := by omega
  have hnot : v.toNat ∉ (ws1.take qlen).map BitVec.toNat := fun hmem => by
    have h1 := (hq.2.2.2.2.2.2.1 v.toNat hv).mpr hmem; rw [hm0] at h1; cases h1
  have htake : (ws1.set qlen v).take (qlen + 1) = ws1.take qlen ++ [v] := by
    refine List.ext_getElem (by simp [List.length_take]; try omega) fun i hi _ => ?_
    simp only [List.length_take, List.length_set] at hi
    rw [List.getElem_take]
    by_cases hlt : i < qlen
    · rw [List.getElem_set_ne (by omega),
        List.getElem_append_left (by simp [List.length_take]; omega), List.getElem_take]
    · have hieq : i = qlen := by omega
      simp only [hieq]
      rw [List.getElem_set_self, List.getElem_append_right (by simp [List.length_take]; omega)]
      simp [List.length_take, Nat.min_eq_left (by omega : qlen ≤ ws1.length)]
  have hmap : ((ws1.set qlen v).take (qlen + 1)).map BitVec.toNat =
      (ws1.take qlen).map BitVec.toNat ++ [v.toNat] := by rw [htake, List.map_append]; rfl
  refine ⟨hq_lt, ⟨by simp [hmrk_len], by simp [hws1_len], by omega, fun i hi => ?_, ?_,
      fun i hi => ?_, fun u hu => ?_, fun u hu => ?_, fun u hu1 hu2 => ?_⟩,
      fun j hj => List.getElem?_set_ne (by omega),
      fun x hx => by rw [hmap]; exact List.mem_append.mpr (Or.inl hx)⟩
  · rcases (by omega : i < qlen ∨ i = qlen) with hi' | rfl
    · rw [List.getElem?_set_ne (by omega)]; exact hq.2.2.2.1 i hi'
    · rw [List.getElem?_set_self hq_ws1, Option.getD_some]; exact hv
  · rw [hmap, List.nodup_append]
    exact ⟨hq.2.2.2.2.1, List.nodup_cons.mpr ⟨by simp, .nil⟩, fun a ha b hb => by
      simp only [List.mem_singleton] at hb; subst hb; exact fun heq => hnot (heq ▸ ha)⟩
  · rcases (by omega : i < qlen ∨ i = qlen) with hi' | rfl
    · rw [List.getElem?_set_ne (by omega)]; exact hq.2.2.2.2.2.1 i hi'
    · rw [List.getElem?_set_self hq_ws1, Option.getD_some]; exact ⟨hlvl, htrl⟩
  · rw [hmap]; simp only [List.mem_append, List.mem_singleton]
    by_cases huv : u = v.toNat
    · subst huv; rw [List.getElem?_set_self hv_mrk, Option.getD_some]; simp
    · rw [List.getElem?_set_ne (Ne.symm huv), hq.2.2.2.2.2.2.1 u hu]; simp [huv]
  · by_cases huv : u = v.toNat
    · subst huv; right; rw [List.getElem?_set_self hv_mrk, Option.getD_some]
    · rw [List.getElem?_set_ne (Ne.symm huv)]; exact hq.2.2.2.2.2.2.2.1 u hu
  · rw [List.getElem?_set_ne (by omega)]; exact hq.2.2.2.2.2.2.2.2 u hu1 hu2

@[expose] def VivClosedOk (s : FullState) (implied : BitVec 32)
    (ws1 ws2 : List (BitVec 32)) (qi qlen olen : Nat) (taut : Bool) : Prop :=
  ∀ k < qi, ∀ idx < s.core.trail_end,
    (s.core.trl[idx]?.getD 0#32).toNat / 2 = (ws1[k]?.getD 0#32).toNat →
      if s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 then
        taut = false →
          (s.core.trl[idx]?.getD 0#32).toNat ≠ implied.toNat ∧
          ((s.core.trl[idx]?.getD 0#32).toNat ^^^ 1) ∈ (ws2.take olen).map BitVec.toNat
      else if
          (s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
          then
        let ov := (s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 &&&
          0x7FFFFFFF#32).toNat / 2
        (s.core.lvl[ov]?.getD 0#32).toNat = 0 ∨ ov ∈ (ws1.take qlen).map BitVec.toNat
      else
        ∀ q ∈ fullArenaClauseLitsCore s.core
            (s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat,
          q ≠ (s.core.trl[idx]?.getD 0#32).toNat →
          (s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨
            q / 2 ∈ (ws1.take qlen).map BitVec.toNat

@[expose] def VivOutOk (s : FullState) (implied : BitVec 32)
    (ws1 ws2 : List (BitVec 32)) (qi olen : Nat) (taut : Bool) : Prop :=
  taut = false →
    olen ≤ s.core.cur_vars ∧
    (∀ i < olen, (ws2[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (((ws2.take olen).map BitVec.toNat).map (· / 2)).Nodup ∧
    (∀ i < olen,
      let v := (ws2[i]?.getD 0#32).toNat / 2
      (implied ≠ 0xFFFFFFFF#32 ∧ i = 0 ∧ v = implied.toNat / 2) ∨
      v ∈ (ws1.take qi).map BitVec.toNat) ∧
    (implied ≠ 0xFFFFFFFF#32 → 0 < olen ∧ ws2[0]? = some implied) ∧
    (∀ j < qi,
      implied = 0xFFFFFFFF#32 ∨ (ws1[j]?.getD 0#32).toNat ≠ implied.toNat / 2 ∨
      s.core.rsns[(ws1[j]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)

@[expose] def VivSeedOk (s : FullState) (cref implied : BitVec 32)
    (ws1 ws2 : List (BitVec 32)) (qlen olen : Nat) (taut : Bool) : Prop :=
  taut = false →
    if implied ≠ 0xFFFFFFFF#32 then
      implied.toNat ∈ (ws2.take olen).map BitVec.toNat
    else if s.core.confl_type = 1#64 then
      let a := s.core.confl_lit0.toNat
      let b := s.core.confl_lit1.toNat
      ((s.core.lvl[a / 2]?.getD 0#32).toNat = 0 ∨ a / 2 ∈ (ws1.take qlen).map BitVec.toNat) ∧
      ((s.core.lvl[b / 2]?.getD 0#32).toNat = 0 ∨ b / 2 ∈ (ws1.take qlen).map BitVec.toNat)
    else
      let src := if s.core.confl_type = 2#64 then s.core.confl_ref.toNat else cref.toNat
      ∀ l ∈ fullArenaClauseLits s src,
        (s.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∨ l / 2 ∈ (ws1.take qlen).map BitVec.toNat

theorem vivClosed_mono_q {s : FullState} {implied : BitVec 32}
    {ws1 ws1' ws2 : List (BitVec 32)} {qi qlen qlen' olen : Nat} {taut : Bool}
    (hc : VivClosedOk s implied ws1 ws2 qi qlen olen taut)
    (hqi : qi ≤ qlen) (hql : qlen ≤ qlen') (hl1 : qlen ≤ ws1.length) (hql' : qlen' ≤ ws1'.length)
    (heq : ∀ j < qlen, ws1'[j]? = ws1[j]?) :
    VivClosedOk s implied ws1' ws2 qi qlen' olen taut := by
  intro k hk idx hidx htrl
  have hkeq : ws1'[k]? = ws1[k]? := heq k (by omega)
  have hmem : ∀ x, x ∈ (ws1.take qlen).map BitVec.toNat →
      x ∈ (ws1'.take qlen').map BitVec.toNat := fun x hx => by
    obtain ⟨j, hj, rfl⟩ := (mem_map_take_iff hl1).mp hx
    exact (mem_map_take_iff hql').mpr ⟨j, by omega, by rw [heq j hj]⟩
  have hc' := hc k hk idx hidx (by rwa [← hkeq])
  rw [hkeq]
  by_cases h1 :
      s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
  · rw [ite_eq_left h1] at hc' ⊢; exact hc'
  · rw [ite_eq_right h1] at hc' ⊢
    by_cases h2 :
        (s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
    · rw [ite_eq_left h2] at hc' ⊢; exact hc'.elim Or.inl (fun hm => Or.inr (hmem _ hm))
    · rw [ite_eq_right h2] at hc' ⊢
      intro q hq hqp; exact (hc' q hq hqp).elim Or.inl (fun hm => Or.inr (hmem _ hm))

theorem vivOut_mono_qi_len {s : FullState} {implied : BitVec 32}
    {ws1 ws2 : List (BitVec 32)} {qi qlen olen : Nat} {taut : Bool}
    (ho : VivOutOk s implied ws1 ws2 qi olen taut)
    (hqi1 : qi + 1 ≤ qlen) (hq_len : qlen ≤ ws1.length)
    (hne : implied = 0xFFFFFFFF#32 ∨ (ws1[qi]?.getD 0#32).toNat ≠ implied.toNat / 2 ∨
      s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) :
    VivOutOk s implied ws1 ws2 (qi + 1) olen taut := by
  intro hf; obtain ⟨hle, hlt, hnd, hmem, himp, hnot⟩ := ho hf
  refine ⟨hle, hlt, hnd, fun i hi => ?_, himp, fun j hj => ?_⟩
  · refine (hmem i hi).elim Or.inl fun hm => Or.inr ?_
    obtain ⟨k, hk, heq⟩ := (mem_map_take_iff (by omega)).mp hm
    exact (mem_map_take_iff (by omega)).mpr ⟨k, by omega, heq⟩
  · rcases (by omega : j < qi ∨ j = qi) with hj' | rfl
    · exact hnot j hj'
    · exact hne

theorem vivOut_mono_qlen {s : FullState} {implied : BitVec 32}
    {ws1 ws1' ws2 : List (BitVec 32)} {qi qlen olen : Nat} {taut : Bool}
    (ho : VivOutOk s implied ws1 ws2 qi olen taut) (hqi : qi ≤ qlen)
    (hl1 : qlen ≤ ws1.length) (hl2 : qlen ≤ ws1'.length)
    (heq : ∀ j < qlen, ws1'[j]? = ws1[j]?) :
    VivOutOk s implied ws1' ws2 qi olen taut := by
  intro hf; obtain ⟨hle, hlt, hnd, hmem, himp, hnot⟩ := ho hf
  have htake : ws1'.take qi = ws1.take qi := List.ext_getElem
    (by simp [List.length_take]; omega) fun i hi _ => by
      simp only [List.length_take] at hi
      rw [List.getElem_take, List.getElem_take]
      have h := heq i (by omega)
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h
      exact Option.some.inj h
  exact ⟨hle, hlt, hnd, fun i hi => by rw [htake]; exact hmem i hi, himp,
    fun j hj => by rw [heq j (by omega)]; exact hnot j hj⟩

theorem vivOut_push_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {mrk : List (BitVec 8)} {ws1 ws2 : List (BitVec 32)}
    {implied : BitVec 32} {qi qlen olen : Nat}
    (hw : FullWitnessInv c F0 F_cur s.core) (hq : VivQueueOk c s mrk ws1 qlen)
    (_hcv : s.core.cur_vars ≤ c.max_vars)
    (hqi : qi < qlen) (ho : VivOutOk s implied ws1 ws2 qi olen false)
    (himp : implied ≠ 0xFFFFFFFF#32 →
      implied.toNat < 2 * s.core.cur_vars ∧ s.core.vals[implied.toNat]?.getD 0#8 = 1#8)
    {idx : Nat} (hidx : idx < s.core.trail_end)
    (htrl : (s.core.trl[idx]?.getD 0#32).toNat / 2 = (ws1[qi]?.getD 0#32).toNat)
    (hne_imp : implied ≠ 0xFFFFFFFF#32 → (s.core.trl[idx]?.getD 0#32) ≠ implied)
    (hws2 : olen ≤ ws2.length) :
    let v := (ws1[qi]?.getD 0#32).toNat
    olen < s.core.cur_vars ∧ v < s.core.cur_vars ∧
    (implied ≠ 0xFFFFFFFF#32 → v ≠ implied.toNat / 2) ∧
    v ∉ ((ws2.take olen).map BitVec.toNat).map (· / 2) := by
  intro v
  have hql := hq.2.2.1; have hws1_l := hq.2.1
  obtain ⟨hle, hlt, hnd, hmem, _, _⟩ := ho rfl
  have hv_lt : v < s.core.cur_vars := hq.2.2.2.1 qi hqi
  have hv_ne_imp : implied ≠ 0xFFFFFFFF#32 → v ≠ implied.toNat / 2 := by
    intro hne heq
    obtain ⟨hil, hiv⟩ := himp hne
    obtain ⟨idx0, hidx0, heq0⟩ := (hw.vals_true_iff implied.toNat hil).mp hiv
    have hidx_eq : idx = idx0 := hw.trail_vars_nodup idx idx0 hidx hidx0 (by
      rw [htrl, show (ws1[qi]?.getD 0#32).toNat = v from rfl, heq, ← heq0])
    rw [← hidx_eq] at heq0; exact hne_imp hne (BitVec.eq_of_toNat_eq heq0)
  have hv_not_qi : v ∉ (ws1.take qi).map BitVec.toNat := by
    intro hm
    obtain ⟨j, hj, hj_eq⟩ := (mem_map_take_iff (by omega)).mp hm
    have hql' : ((ws1.take qlen).map BitVec.toNat).length = qlen := by
      rw [List.length_map, List.length_take]; omega
    have hj_lt : j < ((ws1.take qlen).map BitVec.toNat).length := by omega
    have hq_lt : qi < ((ws1.take qlen).map BitVec.toNat).length := by omega
    have hpair := List.pairwise_iff_getElem.mp hq.2.2.2.2.1 j qi hj_lt hq_lt hj
    simp only [List.getElem_map, List.getElem_take] at hpair
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hj_eq
    have hqi_eq : v = ws1[qi].toNat := by
      dsimp only [v]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact hpair (hj_eq.trans hqi_eq)
  have hv_not : v ∉ ((ws2.take olen).map BitVec.toNat).map (· / 2) := by
    intro hm; obtain ⟨_, hm', hw_eq⟩ := List.mem_map.mp hm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm'
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    have hi' : i < olen := by rw [List.length_take] at hi; omega
    have hmi := hmem i hi'
    rw [List.getElem_take] at hw_eq
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hmi
    rcases hmi with ⟨hne, _, heq⟩ | hm_qi
    · exact hv_ne_imp hne (by rw [← hw_eq, heq])
    · rw [hw_eq] at hm_qi; exact hv_not_qi hm_qi
  have hnd' : (v :: ((ws2.take olen).map BitVec.toNat).map (· / 2)).Nodup :=
    List.nodup_cons.mpr ⟨hv_not, hnd⟩
  have hlt' : ∀ x ∈ (v :: ((ws2.take olen).map BitVec.toNat).map (· / 2)),
      x < s.core.cur_vars := fun x hx => by
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hv_lt
    · obtain ⟨_, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨_, hb, rfl⟩ := List.mem_map.mp hy
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
      have hi' : i < olen := by rw [List.length_take] at hi; omega
      have hb_lt := hlt i hi'
      rw [List.getElem_take]
      have hbi : (ws2[i]'(by omega)).toNat = (ws2[i]?.getD 0#32).toNat := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      omega
  have hlen_le := viv_nodup_lt_length_le _ _ hnd' hlt'
  simp only [List.length_cons, List.length_map, List.length_take] at hlen_le
  exact ⟨by omega, hv_lt, hv_ne_imp, hv_not⟩

theorem vivOut_push_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {mrk : List (BitVec 8)} {ws1 ws2 : List (BitVec 32)}
    {implied : BitVec 32} {qi qlen olen : Nat}
    (hw : FullWitnessInv c F0 F_cur s.core) (hq : VivQueueOk c s mrk ws1 qlen)
    (hqi : qi < qlen) (ho : VivOutOk s implied ws1 ws2 qi olen false)
    (hc : VivClosedOk s implied ws1 ws2 qi qlen olen false)
    (himp : implied ≠ 0xFFFFFFFF#32 →
      implied.toNat < 2 * s.core.cur_vars ∧ s.core.vals[implied.toNat]?.getD 0#8 = 1#8)
    {idx : Nat} (hidx : idx < s.core.trail_end)
    (htrl : (s.core.trl[idx]?.getD 0#32).toNat / 2 = (ws1[qi]?.getD 0#32).toNat)
    (hrsn : s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hne_imp : implied ≠ 0xFFFFFFFF#32 → (s.core.trl[idx]?.getD 0#32) ≠ implied)
    (hws2 : ws2.length = 2 * c.max_vars) (hcv : s.core.cur_vars ≤ c.max_vars) :
    let tl := s.core.trl[idx]?.getD 0#32
    let ws2' := ws2.set olen (tl ^^^ 1#32)
    olen < s.core.cur_vars ∧ olen < ws2.length ∧
    VivOutOk s implied ws1 ws2' (qi + 1) (olen + 1) false ∧
    VivClosedOk s implied ws1 ws2' (qi + 1) qlen (olen + 1) false ∧
    (∀ j < olen, ws2'[j]? = ws2[j]?) := by
  intro tl ws2'
  have hql := hq.2.2.1; have hws1_l := hq.2.1
  obtain ⟨_, hlt, hnd, hmem, himp_out, hnot_qi⟩ := ho rfl
  obtain ⟨hol_lt, _, hv_ne_imp, hv_not⟩ :=
    vivOut_push_lt hw hq hcv hqi ho himp hidx htrl hne_imp (by omega)
  have hol_ws2 : olen < ws2.length := by omega
  have htake2 : ws2'.take (olen + 1) = ws2.take olen ++ [tl ^^^ 1#32] := by
    refine List.ext_getElem (by simp [ws2', List.length_take]; try omega) fun i hi _ => ?_
    simp only [List.length_take, List.length_set, ws2'] at hi
    rw [List.getElem_take]
    by_cases hlt_i : i < olen
    · rw [List.getElem_set_ne (by omega),
        List.getElem_append_left (by simp [List.length_take]; omega), List.getElem_take]
    · have hieq : i = olen := by omega
      simp only [hieq]
      rw [List.getElem_set_self, List.getElem_append_right (by simp [List.length_take]; omega)]
      simp [List.length_take, Nat.min_eq_left (by omega : olen ≤ ws2.length)]
  have htl_lt : tl.toNat < 2 * s.core.cur_vars := hw.trail_lits_lt idx hidx
  have hxor_lt : (tl ^^^ 1#32).toNat < 2 * s.core.cur_vars := viv_bv32_xor1_lt htl_lt
  have hdiv_eq : (tl ^^^ 1#32).toNat / 2 = (ws1[qi]?.getD 0#32).toNat := by
    rw [viv_bv32_xor1_div2, ← htrl]
  have hq_ws1 : qi < ws1.length := by omega
  have htake1 : ws1.take (qi + 1) = ws1.take qi ++ [ws1[qi]'hq_ws1] := by
    refine List.ext_getElem (by simp [List.length_take, hws1_l]; try omega) fun i hi _ => ?_
    simp only [List.length_take, hws1_l] at hi
    rw [List.getElem_take]
    by_cases hlt_i : i < qi
    · rw [List.getElem_append_left (by simp [List.length_take]; omega), List.getElem_take]
    · have hieq : i = qi := by omega
      simp only [hieq]; rw [List.getElem_append_right (by simp [List.length_take]; omega)]
      simp [List.length_take, Nat.min_eq_left (by omega : qi ≤ ws1.length)]
  refine ⟨hol_lt, hol_ws2, fun _ => ⟨by omega, fun i hi => ?_, ?_, fun i hi => ?_,
      fun hne => ?_, fun j hj => ?_⟩, fun k hk idx' hidx' htrl' => ?_,
      fun j hj => List.getElem?_set_ne (by omega)⟩
  · rcases (by omega : i < olen ∨ i = olen) with hi' | rfl
    · rw [List.getElem?_set_ne (by omega)]; exact hlt i hi'
    · rw [List.getElem?_set_self hol_ws2, Option.getD_some]; exact hxor_lt
  · rw [htake2, List.map_append, List.map_append, List.nodup_append]
    refine ⟨hnd, List.nodup_cons.mpr ⟨by simp, .nil⟩, fun a ha b hb => ?_⟩
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb; subst hb
    rw [hdiv_eq]; exact fun heq => hv_not (heq ▸ ha)
  · rcases (by omega : i < olen ∨ i = olen) with hi' | rfl
    · rw [List.getElem?_set_ne (by omega)]
      refine (hmem i hi').elim Or.inl fun hm => Or.inr ?_
      rw [htake1, List.map_append]; exact List.mem_append.mpr (Or.inl hm)
    · right; rw [List.getElem?_set_self hol_ws2, Option.getD_some, hdiv_eq, htake1,
        List.map_append]
      exact List.mem_append.mpr (Or.inr (by simp [List.getElem?_eq_getElem hq_ws1]))
  · obtain ⟨_, hw0⟩ := himp_out hne
    exact ⟨by omega, by dsimp only [ws2']; rw [List.getElem?_set_ne (by omega)]; exact hw0⟩
  · rcases (by omega : j < qi ∨ j = qi) with hj' | rfl
    · exact hnot_qi j hj'
    · by_cases hne : implied = 0xFFFFFFFF#32
      · exact Or.inl hne
      · exact Or.inr (Or.inl (hv_ne_imp hne))
  · have hmem2 : ∀ l, l ∈ (ws2.take olen).map BitVec.toNat →
        l ∈ (ws2'.take (olen + 1)).map BitVec.toNat := fun l hl => by
      rw [htake2, List.map_append]; exact List.mem_append.mpr (Or.inl hl)
    rcases (by omega : k < qi ∨ k = qi) with hk' | rfl
    · have hc' := hc k hk' idx' hidx' htrl'
      by_cases hrsn_k :
          s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
      · simp only [hrsn_k, ↓reduceIte] at hc' ⊢
        exact fun hf => ⟨(hc' hf).1, hmem2 _ (hc' hf).2⟩
      · simp only [hrsn_k, ↓reduceIte] at hc' ⊢; exact hc'
    · rw [ite_eq_left hrsn]; intro _
      have hidx_eq : idx' = idx := hw.trail_vars_nodup idx' idx hidx' hidx (by rw [htrl', htrl])
      subst hidx_eq
      refine ⟨fun heq => hne_imp ?_ (BitVec.eq_of_toNat_eq heq), ?_⟩
      · intro himp0; simp [himp0] at heq
        have := hw.trail_lits_lt idx' hidx'
        have := c.hmaxv; unfold dimacsBound at this; omega
      · rw [htake2, List.map_append, ← viv_bv32_xor1_toNat tl]
        simp only [List.mem_append, List.map_cons, List.map_nil, List.mem_singleton, or_true]

theorem vivClosed_step_bin {s : FullState} {implied : BitVec 32}
    {ws1 ws2 : List (BitVec 32)} {qi qlen olen : Nat} {taut : Bool}
    (hc : VivClosedOk s implied ws1 ws2 qi qlen olen taut)
    (htrl_nodup : ∀ i j, i < s.core.trail_end → j < s.core.trail_end →
      (s.core.trl[i]?.getD 0#32).toNat / 2 = (s.core.trl[j]?.getD 0#32).toNat / 2 → i = j)
    {idx0 : Nat} (hidx0 : idx0 < s.core.trail_end)
    (htrl0 : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = (ws1[qi]?.getD 0#32).toNat)
    (hrsn_ne : s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hbin : (s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32)
    (hcov : (s.core.lvl[(s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 &&&
        0x7FFFFFFF#32).toNat / 2]?.getD 0#32).toNat = 0 ∨
      (s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat / 2 ∈
        (ws1.take qlen).map BitVec.toNat) :
    VivClosedOk s implied ws1 ws2 (qi + 1) qlen olen taut := by
  intro k hk idx hidx htrl
  rcases (by omega : k < qi ∨ k = qi) with hk' | hk_eq
  · exact hc k hk' idx hidx htrl
  · rw [hk_eq] at htrl ⊢
    have := htrl_nodup idx idx0 hidx hidx0 (htrl.trans htrl0.symm)
    subst this; rw [ite_eq_right hrsn_ne, ite_eq_left hbin]; exact hcov

theorem vivClosed_step_large {s : FullState} {implied : BitVec 32}
    {ws1 ws2 : List (BitVec 32)} {qi qlen olen : Nat} {taut : Bool}
    (hc : VivClosedOk s implied ws1 ws2 qi qlen olen taut)
    (htrl_nodup : ∀ i j, i < s.core.trail_end → j < s.core.trail_end →
      (s.core.trl[i]?.getD 0#32).toNat / 2 = (s.core.trl[j]?.getD 0#32).toNat / 2 → i = j)
    {idx0 : Nat} (hidx0 : idx0 < s.core.trail_end)
    (htrl0 : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = (ws1[qi]?.getD 0#32).toNat)
    (hrsn_ne : s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hlg : (s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32)
    (hcov : ∀ q ∈ fullArenaClauseLitsCore s.core
        (s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat,
      q / 2 ≠ (ws1[qi]?.getD 0#32).toNat →
      (s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ q / 2 ∈ (ws1.take qlen).map BitVec.toNat)
    (hreason : ∀ q ∈ fullArenaClauseLitsCore s.core
        (s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat,
      q = (s.core.trl[idx0]?.getD 0#32).toNat ∨
      ∃ m < idx0, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1) :
    VivClosedOk s implied ws1 ws2 (qi + 1) qlen olen taut := by
  intro k hk idx hidx htrl
  rcases (by omega : k < qi ∨ k = qi) with hk' | hk_eq
  · exact hc k hk' idx hidx htrl
  · rw [hk_eq] at htrl ⊢
    have := htrl_nodup idx idx0 hidx hidx0 (htrl.trans htrl0.symm)
    subst this; rw [ite_eq_right hrsn_ne, ite_eq_right (by simp [hlg])]
    intro q hq hqp
    have hq_ne_v : q / 2 ≠ (ws1[qi]?.getD 0#32).toNat := by
      rcases hreason q hq with hsame | ⟨m, hm_lt, hmeq⟩
      · exact absurd hsame hqp
      · intro heqv; have hmi : m = idx := htrl_nodup m idx (by omega) hidx (by
          rw [hmeq, fullInv_var_xor1 q, heqv, ← htrl0])
        omega
    exact hcov q hq hq_ne_v

theorem vivClosed_taut_true {s : FullState} {implied : BitVec 32}
    {ws1 ws2 : List (BitVec 32)} {qi qlen olen : Nat}
    (hc : VivClosedOk s implied ws1 ws2 qi qlen olen false)
    (hrsn : s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    VivClosedOk s implied ws1 ws2 (qi + 1) qlen olen true := by
  intro k hk idx hidx htrl
  rcases (by omega : k < qi ∨ k = qi) with hk' | hk_eq
  · have hc' := hc k hk' idx hidx htrl
    by_cases hrsn_k :
        s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
    · rw [ite_eq_left hrsn_k] at hc' ⊢; intro h; cases h
    · rw [ite_eq_right hrsn_k] at hc' ⊢; exact hc'
  · rw [hk_eq, ite_eq_left hrsn]; intro h; cases h

theorem s13_vivClosed_taut_true {s : FullState} {implied : BitVec 32}
    {ws1 ws2 ws2' : List (BitVec 32)} {qi qlen olen olen' : Nat} {taut : Bool}
    (hcb : VivClosedOk s implied ws1 ws2 qi qlen olen taut)
    (hrsn : s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    VivClosedOk s implied ws1 ws2' (qi + 1) qlen olen' true := by
  intro k hk idx hidx ht
  rcases (by omega : k < qi ∨ k = qi) with hk' | rfl
  · have h := hcb k hk' idx hidx ht
    by_cases hr : s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
    · simp only [hr, ↓reduceIte]; intro h1; cases h1
    · simp only [hr, ↓reduceIte] at h ⊢; exact h
  · simp only [hrsn, ↓reduceIte]; intro h1; cases h1

theorem s13_vivSeed_mono_ws2 {s : FullState} {cref implied : BitVec 32}
    {ws1 ws2 ws2' : List (BitVec 32)} {qlen olen olen' : Nat}
    (hsd : VivSeedOk s cref implied ws1 ws2 qlen olen false)
    (hle : olen ≤ olen') (hlen : olen ≤ ws2.length) (hlen' : olen' ≤ ws2'.length)
    (hpre : ∀ j < olen, ws2'[j]? = ws2[j]?) :
    VivSeedOk s cref implied ws1 ws2' qlen olen' false := by
  intro _; have h := hsd rfl
  by_cases hi : implied = 0xFFFFFFFF#32
  · simp only [hi, ne_eq, not_true_eq_false, ↓reduceIte] at h ⊢; exact h
  · simp only [hi, ne_eq, not_false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨j, hj, hjeq⟩ := (mem_map_take_iff hlen).mp h
    exact (mem_map_take_iff hlen').mpr ⟨j, by omega, by rw [hpre j hj, hjeq]⟩

theorem viv_clear_mrk_init {c : FullCfg} {s : FullState} {mrk : List (BitVec 8)}
    {ws1 : List (BitVec 32)} {qlen : Nat}
    (hq : VivQueueOk c s mrk ws1 qlen) (_hcv : s.core.cur_vars ≤ c.max_vars) :
    ∀ v < c.max_vars, mrk[v]?.getD 0#8 = 0#8 ∨
      ∃ k, 0 ≤ k ∧ k < qlen ∧ (ws1[k]?.getD 0#32).toNat = v := by
  intro v hv
  by_cases hv_cv : v < s.core.cur_vars
  · rcases hq.2.2.2.2.2.2.2.1 v hv_cv with h0 | h1
    · exact Or.inl h0
    · obtain ⟨k, hk, heq⟩ :=
        (mem_map_take_iff (by have := hq.2.1; have := hq.2.2.1; omega)).mp
          ((hq.2.2.2.2.2.2.1 v hv_cv).mp h1)
      exact Or.inr ⟨k, Nat.zero_le _, hk, heq⟩
  · exact Or.inl (hq.2.2.2.2.2.2.2.2 v (by omega) hv)

theorem viv_clear_mrk_step {c : FullCfg} {_s : FullState} {mrk : List (BitVec 8)}
    {ws1 : List (BitVec 32)} {qi qlen : Nat}
    (hmrk_len : mrk.length = c.max_vars)
    (hws1_lt : ∀ i < qlen, (ws1[i]?.getD 0#32).toNat < _s.core.cur_vars)
    (hcv : _s.core.cur_vars ≤ c.max_vars) (hqi : qi < qlen)
    (hinv : ∀ v < c.max_vars,
      mrk[v]?.getD 0#8 = 0#8 ∨ ∃ k, qi ≤ k ∧ k < qlen ∧ (ws1[k]?.getD 0#32).toNat = v) :
    let v := (ws1[qi]?.getD 0#32).toNat
    v < mrk.length ∧
    ∀ u < c.max_vars, (mrk.set v 0#8)[u]?.getD 0#8 = 0#8 ∨
      ∃ k, qi + 1 ≤ k ∧ k < qlen ∧ (ws1[k]?.getD 0#32).toNat = u := by
  intro v; have hv_lt : v < c.max_vars := by have := hws1_lt qi hqi; omega
  refine ⟨by omega, fun u hu => ?_⟩
  by_cases huv : u = v
  · subst huv; left; rw [List.getElem?_set_self (by omega), Option.getD_some]
  · rw [List.getElem?_set_ne (Ne.symm huv)]
    refine (hinv u hu).elim Or.inl fun ⟨k, hk1, hk2, hkeq⟩ => Or.inr ?_
    exact ⟨k, by have : k ≠ qi := fun e => huv (e ▸ hkeq).symm; omega, hk2, hkeq⟩

theorem vivSeed_mono_q {s : FullState} {cref implied : BitVec 32}
    {ws1 ws1' ws2 : List (BitVec 32)} {qlen qlen' olen : Nat} {taut : Bool}
    (hsd : VivSeedOk s cref implied ws1 ws2 qlen olen taut)
    (hql : qlen ≤ qlen') (hql' : qlen' ≤ ws1'.length) (hl1 : qlen ≤ ws1.length)
    (heq : ∀ j < qlen, ws1'[j]? = ws1[j]?) :
    VivSeedOk s cref implied ws1' ws2 qlen' olen taut := by
  intro hf; have hsd' := hsd hf
  have hmem : ∀ x, x ∈ (ws1.take qlen).map BitVec.toNat →
      x ∈ (ws1'.take qlen').map BitVec.toNat := fun x hx => by
    obtain ⟨j, hj, rfl⟩ := (mem_map_take_iff hl1).mp hx
    exact (mem_map_take_iff hql').mpr ⟨j, by omega, by rw [heq j hj]⟩
  by_cases himp : implied = 0xFFFFFFFF#32 <;>
    simp only [himp, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] at hsd' ⊢
  · by_cases hct : s.core.confl_type = 1#64 <;> simp only [hct, ↓reduceIte] at hsd' ⊢
    · exact ⟨hsd'.1.elim Or.inl (fun hm => Or.inr (hmem _ hm)),
        hsd'.2.elim Or.inl (fun hm => Or.inr (hmem _ hm))⟩
    · exact fun l hl => (hsd' l hl).elim Or.inl (fun hm => Or.inr (hmem _ hm))
  · exact hsd'

theorem s13_vivClosed_ar_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} {mrk : List (BitVec 8)} {implied : BitVec 32} {ws1 ws2 : List (BitVec 32)}
    {qi qlen olen : Nat} {taut : Bool}
    (hw : FullWitnessInv c F0 F_cur s.core) (_hq : VivQueueOk c s mrk ws1 qlen) (_hqi : qi ≤ qlen)
    (_hcore : s'.core.cur_vars = s.core.cur_vars) (hlvl : s'.core.lvl = s.core.lvl)
    (hrsns : s'.core.rsns = s.core.rsns) (htrl : s'.core.trl = s.core.trl)
    (hte : s'.core.trail_end = s.core.trail_end) (hpres : S13ArPres s s')
    (hcb : VivClosedOk s implied ws1 ws2 qi qlen olen taut) :
    VivClosedOk s' implied ws1 ws2 qi qlen olen taut := by
  intro k hk idx hidx htrk
  rw [hte] at hidx; rw [htrl] at htrk
  have hcbk := hcb k hk idx hidx htrk
  rw [hrsns, hlvl]
  by_cases hdec : s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
  · simp only [hdec, ↓reduceIte] at hcbk ⊢; rwa [htrl]
  · simp only [hdec, ↓reduceIte] at hcbk ⊢
    by_cases hbin : (s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 &&&
        0x80000000#32) ≠ 0#32
    · rw [ite_eq_left hbin] at hcbk ⊢; exact hcbk
    · rw [ite_eq_right hbin] at hcbk ⊢
      let r := (s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat
      have href_r : r ∈ fullArenaClauseRefs s := by
        have hri := hw.reason_inv idx hidx (by rwa [htrk])
        rw [htrk, ite_eq_right hbin] at hri; exact hri.1
      have hlits_eq : fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r :=
        (hpres.2 r href_r).2.2
      dsimp only [r] at hlits_eq
      rw [hlits_eq, htrl]; exact hcbk

theorem s13_vivOut_ar_eq {s s' : FullState} {implied : BitVec 32} {ws1 ws2 : List (BitVec 32)}
    {qi olen : Nat} {taut : Bool}
    (hcv : s'.core.cur_vars = s.core.cur_vars) (hrsns : s'.core.rsns = s.core.rsns)
    (ho : VivOutOk s implied ws1 ws2 qi olen taut) :
    VivOutOk s' implied ws1 ws2 qi olen taut := by
  intro ht; have h := ho ht; rwa [hcv, hrsns]

theorem s13_vivSeed_ar_eq {_c : FullCfg} {_F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} {cref implied : BitVec 32} {ws1 ws2 : List (BitVec 32)}
    {qlen olen : Nat} {taut : Bool}
    (hconfl : implied = 0xFFFFFFFF#32 →
      FullVivConflictOk F_cur s ∨
      (s.core.confl_type = 0#64 ∧
        ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8))
    (href : cref.toNat ∈ fullArenaClauseRefs s)
    (hlvl : s'.core.lvl = s.core.lvl) (hct : s'.core.confl_type = s.core.confl_type)
    (hcr : s'.core.confl_ref = s.core.confl_ref)
    (hcl0 : s'.core.confl_lit0 = s.core.confl_lit0)
    (hcl1 : s'.core.confl_lit1 = s.core.confl_lit1) (hpres : S13ArPres s s')
    (hsd : VivSeedOk s cref implied ws1 ws2 qlen olen taut) :
    VivSeedOk s' cref implied ws1 ws2 qlen olen taut := by
  intro ht; have h := hsd ht
  by_cases hi : implied ≠ 0xFFFFFFFF#32
  · dsimp only [VivSeedOk] at h ⊢; rw [ite_eq_left hi] at h ⊢; exact h
  · have hieq : implied = 0xFFFFFFFF#32 := by
      cases Classical.em (implied = 0xFFFFFFFF#32) with
      | inl he => exact he
      | inr hne => exact absurd hne hi
    simp only [hi, ↓reduceIte] at h ⊢
    rw [hct, hlvl]
    by_cases hct1 : s.core.confl_type = 1#64
    · simp only [hct1, ↓reduceIte] at h ⊢; rwa [hcl0, hcl1]
    · simp only [hct1, ↓reduceIte] at h ⊢; rw [hcr]
      have href_src : (if s.core.confl_type = 2#64 then s.core.confl_ref.toNat else cref.toNat) ∈
          fullArenaClauseRefs s := by
        by_cases hct2 : s.core.confl_type = 2#64
        · simp only [hct2, ↓reduceIte]
          rcases hconfl hieq with (⟨h1, _⟩ | ⟨_, hr2, _⟩) | ⟨h0, _⟩
          · exact absurd h1 hct1
          · exact hr2
          · rw [h0] at hct2; cases hct2
        · simp only [hct2, ↓reduceIte]; exact href
      have hlits := (hpres.2 _ href_src).2.2
      intro l hl; exact h l (by rwa [hlits] at hl)

theorem s13_vivQueue_ar_eq {c : FullCfg} {s s' : FullState} {mrk : List (BitVec 8)}
    {ws1 : List (BitVec 32)} {qlen : Nat}
    (hcv : s'.core.cur_vars = s.core.cur_vars) (hlvl : s'.core.lvl = s.core.lvl)
    (hte : s'.core.trail_end = s.core.trail_end) (htrl : s'.core.trl = s.core.trl)
    (hq : VivQueueOk c s mrk ws1 qlen) : VivQueueOk c s' mrk ws1 qlen := by
  simpa only [VivQueueOk, hcv, hlvl, hte, htrl] using hq

theorem deduce_phase2_sound {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {mrk : List (BitVec 8)} {ws1 ws2 : List (BitVec 32)}
    {cref implied : BitVec 32} {qlen olen : Nat}
    (hw : FullWitnessInv c F0 F_cur s.core) (hq : VivQueueOk c s mrk ws1 qlen)
    (_hcv : s.core.cur_vars ≤ c.max_vars)
    (href_c : cref.toNat ∈ fullArenaClauseRefs s) (hng_c : fullArenaClauseGarb s cref.toNat = false)
    (hc : VivClosedOk s implied ws1 ws2 qlen qlen olen false)
    (hsd : VivSeedOk s cref implied ws1 ws2 qlen olen false)
    (himp : implied ≠ 0xFFFFFFFF#32 →
      implied.toNat < 2 * s.core.cur_vars ∧ s.core.vals[implied.toNat]?.getD 0#8 = 1#8)
    (hconfl : implied = 0xFFFFFFFF#32 →
      FullVivConflictOk F_cur s ∨ (s.core.confl_type = 0#64 ∧
        ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8))
    (hsd_imp : implied ≠ 0xFFFFFFFF#32 →
      (s.core.lvl[implied.toNat / 2]?.getD 0#32).toNat = 0 ∨
      implied.toNat / 2 ∈ (ws1.take qlen).map BitVec.toNat) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause ((ws2.take olen).map BitVec.toNat)) := by
  rw [CNF.entails_clause_def]; intro α hsat
  refine Classical.byContradiction fun hunsat => ?_
  have hfalse : ∀ l ∈ (ws2.take olen).map BitVec.toNat, ¬ (cnfClause [l]).Sat α := by
    intro l hl hls; apply hunsat; rw [clause_sat_cnfClause_iff]
    exact ⟨l, hl, (sat_cnfClause_singleton α l).mp hls⟩
  have htrail : ∀ idx, idx < s.core.trail_end →
      ((s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 ∨
       (s.core.trl[idx]?.getD 0#32).toNat / 2 ∈ (ws1.take qlen).map BitVec.toNat) →
      (cnfClause [(s.core.trl[idx]?.getD 0#32).toNat]).Sat α := by
    intro idx; induction idx using Nat.strongRecOn with
    | ind idx ih =>
      intro hidx hcond
      let p := (s.core.trl[idx]?.getD 0#32).toNat
      let v := p / 2
      let rsn := s.core.rsns[v]?.getD 0xFFFFFFFF#32
      rcases hcond with hl0 | hv_mem
      · exact (CNF.entails_clause_def.mp (hw.level0_sound idx hidx hl0)) α hsat
      · obtain ⟨k, hk, hk_eq⟩ := (mem_map_take_iff (by
          have := hq.2.1; have := hq.2.2.1; have := hw.trail_lits_lt idx hidx; omega)).mp hv_mem
        have hc_k := hc k hk idx hidx hk_eq.symm
        rw [hk_eq] at hc_k
        by_cases hrsn0 : rsn = 0xFFFFFFFF#32
        · dsimp only [rsn, v, p] at hrsn0
          rw [ite_eq_left hrsn0] at hc_k
          by_cases hp_sat : (cnfClause [p]).Sat α
          · exact hp_sat
          · exact absurd ((sat_cnfClause_litNeg_iff α p).mpr hp_sat)
              (hfalse _ (hc_k rfl).2)
        · by_cases hbin : (rsn &&& 0x80000000#32) ≠ 0#32
          · dsimp only [rsn, v, p] at hrsn0 hbin
            rw [ite_eq_right hrsn0, ite_eq_left hbin] at hc_k
            have hri := hw.reason_inv idx hidx hrsn0
            rw [ite_eq_left hbin] at hri
            obtain ⟨_, hent, m, hm_lt, hmeq, _⟩ := hri
            have hm_cond : (s.core.lvl[(s.core.trl[m]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 ∨
                (s.core.trl[m]?.getD 0#32).toNat / 2 ∈ (ws1.take qlen).map BitVec.toNat := by
              rw [hmeq, fullInv_var_xor1]; exact hc_k
            have hsat_ot : (cnfClause [(rsn &&& 0x7FFFFFFF#32).toNat ^^^ 1]).Sat α := by
              rw [← hmeq]; exact ih m hm_lt (by omega) hm_cond
            have hnot_ot : ¬ (cnfClause [(rsn &&& 0x7FFFFFFF#32).toNat]).Sat α := by
              rw [← sat_cnfClause_litNeg_iff]; simpa [litNeg] using hsat_ot
            have hcl := (clause_sat_cnfClause_iff α _).mp
              (CNF.entails_clause_def.mp hent α hsat)
            rcases hcl with ⟨l, hl, hls⟩
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl
            · exact (sat_cnfClause_singleton α _).mpr hls
            · exact absurd ((sat_cnfClause_singleton α _).mpr hls) hnot_ot
          · dsimp only [rsn, v, p] at hrsn0 hbin
            rw [ite_eq_right hrsn0, ite_eq_right hbin] at hc_k
            have hri := hw.reason_inv idx hidx hrsn0
            rw [ite_eq_right hbin] at hri
            obtain ⟨href_r, hng_r, hlits_r⟩ := hri
            have hent_r := hw.arena.entails rsn.toNat href_r hng_r
            obtain ⟨q, hq_mem, hq_sat⟩ :=
              (clause_sat_cnfClause_iff α _).mp (CNF.entails_clause_def.mp hent_r α hsat)
            by_cases hqp : q = p
            · subst hqp; exact (sat_cnfClause_singleton α _).mpr hq_sat
            · rcases hlits_r q hq_mem with hq' | ⟨m, hm_lt, hmeq, _⟩
              · exact absurd hq' hqp
              · have hm_cond :
                    (s.core.lvl[(s.core.trl[m]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 ∨
                    (s.core.trl[m]?.getD 0#32).toNat / 2 ∈ (ws1.take qlen).map BitVec.toNat := by
                  rw [hmeq, fullInv_var_xor1]; exact hc_k q hq_mem hqp
                have hsat_q : (cnfClause [q ^^^ 1]).Sat α := by
                  rw [← hmeq]; exact ih m hm_lt (by omega) hm_cond
                exact absurd ((sat_cnfClause_singleton α _).mpr hq_sat)
                  ((sat_cnfClause_litNeg_iff α q).mp (by simpa [litNeg] using hsat_q))
  by_cases himp0 : implied = 0xFFFFFFFF#32
  · have hsd' := hsd rfl; simp only [himp0, ne_eq, not_true_eq_false, ↓reduceIte] at hsd'
    rcases hconfl himp0 with hok | ⟨hct0, hfal_c⟩
    · rcases hok with ⟨hct1, ha_lt, hb_lt, hent_ab, hva, hvb⟩ |
          ⟨hct2, href_cr, hng_cr, hfal_cr⟩
      · simp only [hct1, ↓reduceIte] at hsd'
        obtain ⟨l, hl, hls⟩ := (clause_sat_cnfClause_iff α _).mp
          (CNF.entails_clause_def.mp hent_ab α hsat)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · obtain ⟨idx, hidx, heq⟩ := (hw.vals_false_iff _ ha_lt).mp hva
          have hs := htrail idx hidx (by rw [heq, fullInv_var_xor1]; exact hsd'.1)
          have hns := (sat_cnfClause_litNeg_iff α _).mp (by
            change (cnfClause [_ ^^^ 1]).Sat α; rwa [← heq])
          exact hns ((sat_cnfClause_singleton α _).mpr hls)
        · obtain ⟨idx, hidx, heq⟩ := (hw.vals_false_iff _ hb_lt).mp hvb
          have hs := htrail idx hidx (by rw [heq, fullInv_var_xor1]; exact hsd'.2)
          have hns := (sat_cnfClause_litNeg_iff α _).mp (by
            change (cnfClause [_ ^^^ 1]).Sat α; rwa [← heq])
          exact hns ((sat_cnfClause_singleton α _).mpr hls)
      · simp only [hct2, ↓reduceIte] at hsd'
        obtain ⟨l, hl, hls⟩ := (clause_sat_cnfClause_iff α _).mp
          (CNF.entails_clause_def.mp (hw.arena.entails _ href_cr hng_cr) α hsat)
        obtain ⟨idx, hidx, heq⟩ :=
          (hw.vals_false_iff l (hw.arena.lits_lt _ href_cr hng_cr l hl)).mp (hfal_cr l hl)
        have hs := htrail idx hidx (by rw [heq, fullInv_var_xor1]; exact hsd' l hl)
        have hns := (sat_cnfClause_litNeg_iff α l).mp (by
          change (cnfClause [l ^^^ 1]).Sat α; rwa [← heq])
        exact hns ((sat_cnfClause_singleton α _).mpr hls)
    · have hne1 : s.core.confl_type ≠ 1#64 := by rw [hct0]; decide
      have hne2 : s.core.confl_type ≠ 2#64 := by rw [hct0]; decide
      simp only [hne1, hne2, ↓reduceIte] at hsd'
      obtain ⟨l, hl, hls⟩ := (clause_sat_cnfClause_iff α _).mp
        (CNF.entails_clause_def.mp (hw.arena.entails _ href_c hng_c) α hsat)
      obtain ⟨idx, hidx, heq⟩ :=
        (hw.vals_false_iff l (hw.arena.lits_lt _ href_c hng_c l hl)).mp (hfal_c l hl)
      have hs := htrail idx hidx (by rw [heq, fullInv_var_xor1]; exact hsd' l hl)
      have hns := (sat_cnfClause_litNeg_iff α l).mp (by
        change (cnfClause [l ^^^ 1]).Sat α; rwa [← heq])
      exact hns ((sat_cnfClause_singleton α _).mpr hls)
  · obtain ⟨hl_lt, hv1⟩ := himp himp0
    obtain ⟨idx, hidx, heq⟩ := (hw.vals_true_iff _ hl_lt).mp hv1
    have hs := htrail idx hidx (by rw [heq]; exact hsd_imp himp0)
    have hsd' := hsd rfl; simp only [himp0, ne_eq, not_false_eq_true, ↓reduceIte] at hsd'
    exact hfalse implied.toNat hsd' (by rwa [heq] at hs)

abbrev deducePushExpr (pVars pMark pLevel pWs1 : Val i64)
    (ov : Val i32) (qlen : Val i64) (J : Cont [i64]) : Expr Val Cont [i32] :=
  fvOp (OpCode.zext 32 64) (Arg.var ov, ()) fun p =>
  fvOp (OpCode.cmp .ult i64 .bool (by decide)) (Arg.var p.fst, Arg.var pVars, ()) fun p =>
  Expr.jnz (Arg.var p.fst)
    (fvOp (OpCode.zext 32 64) (Arg.var ov, ()) fun p =>
     fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
     fvOp (OpCode.add i64) (Arg.var pLevel, Arg.var p.fst, ()) fun p =>
     Expr.load i32 (Arg.var p.fst) fun ld =>
     fvOp (OpCode.cmp .ugt i32 .bool (by decide)) (Arg.var ld, Arg.imm 0, ()) fun p =>
     Expr.jnz (Arg.var p.fst)
       (fvOp (OpCode.zext 32 64) (Arg.var ov, ()) fun p =>
        fvOp (OpCode.add i64) (Arg.var pMark, Arg.var p.fst, ()) fun p =>
        Expr.load i8 (Arg.var p.fst) fun ld =>
        fvOp (OpCode.trunc 32 8) (Arg.imm 0, ()) fun p0 =>
        fvOp (OpCode.zext 8 32) (Arg.var ld, ()) fun p1 =>
        fvOp (OpCode.zext 8 32) (Arg.var p0.fst, ()) fun p2 =>
        fvOp (OpCode.cmp .eq i32 .bool (by decide))
          (Arg.var p1.fst, Arg.var p2.fst, ()) fun p =>
        Expr.jnz (Arg.var p.fst)
          (fvOp (OpCode.cmp .ult i64 .bool (by decide))
             (Arg.var qlen, Arg.var pVars, ()) fun p =>
           Expr.jnz (Arg.var p.fst)
             (fvOp (OpCode.zext 32 64) (Arg.var ov, ()) fun p =>
              fvOp (OpCode.add i64) (Arg.var pMark, Arg.var p.fst, ()) fun p =>
              fvOp (OpCode.trunc 32 8) (Arg.imm 1, ()) fun pm =>
              Expr.store (Arg.var pm.fst) (Arg.var p.fst)
                (fvOp (OpCode.mul i64) (Arg.var qlen, Arg.imm 4, ()) fun p =>
                 fvOp (OpCode.add i64) (Arg.var pWs1, Arg.var p.fst, ()) fun p =>
                 Expr.store (Arg.var ov) (Arg.var p.fst)
                   (fvOp (OpCode.add i64) (Arg.var qlen, Arg.imm 1, ()) fun p =>
                    Expr.jump J (Arg.var p.fst, ()))))
             (Expr.jump J (Arg.var qlen, ())))
          (Expr.jump J (Arg.var qlen, ())))
       (Expr.jump J (Arg.var qlen, ())))
    (Expr.jump J (Arg.var qlen, ()))

theorem deduce_push_wp (Γ : Env) {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {mrk_cur : List (BitVec 8)} {ws1_cur ws2_cur : List (BitVec 32)} {rsz_cur : BitVec 64}
    {qlen : Val i64} {ov : Val i32} {m : Mem 64}
    {Q : Post [i32]} {X : XPost} {J : Cont [i64]}
    (hsp : FullSparseInv c F0 s) (_hw : FullWitnessInv c F0 F_cur s.core)
    (hq : VivQueueOk c s mrk_cur ws1_cur qlen.toNat) (hws2 : ws2_cur.length = 2 * c.max_vars)
    (hov_lt : ov.toNat < s.core.cur_vars)
    (hov_trl : ∃ idx < s.core.trail_end, (s.core.trl[idx]?.getD 0#32).toNat / 2 = ov.toNat)
    (hm : (FullMem c { s with
      core := { s.core with mrk := mrk_cur }
      scratch := { s.scratch with
        work_stk1 := ws1_cur, work_stk2 := ws2_cur, res_sz := rsz_cur } } ⋆ R) m)
    (hJ : ∀ (qlen' : Val i64) (mrk_n : List (BitVec 8)) (ws1_n : List (BitVec 32)) mn,
      qlen.toNat ≤ qlen'.toNat → qlen'.toNat ≤ s.core.cur_vars →
      (∀ j < qlen.toNat, ws1_n[j]? = ws1_cur[j]?) →
      VivQueueOk c s mrk_n ws1_n qlen'.toNat →
      ((s.core.lvl[ov.toNat]?.getD 0#32).toNat = 0 ∨
        ov.toNat ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat) →
      (FullMem c { s with
        core := { s.core with mrk := mrk_n }
        scratch := { s.scratch with
          work_stk1 := ws1_n, work_stk2 := ws2_cur, res_sz := rsz_cur } } ⋆ R) mn →
      J (qlen', ()) mn) :
    wp Γ Q X (deducePushExpr (BitVec.ofNat 64 s.core.cur_vars)
      c.pMark c.pLevel c.pWorkStk1 ov qlen J) m := by
  have hcl := hsp.1.lengths.core_ok
  have hcv_le := hcl.cur_vars_le
  have hcv_bd : s.core.cur_vars < 2 ^ 31 := by
    have := c.hmaxv; unfold dimacsBound at this; omega
  have hov_lvl : ov.toNat < s.core.lvl.length := by rw [hcl.lvl_len]; omega
  have hov_mrk : ov.toNat < mrk_cur.length := by rw [hq.1]; omega
  have hql_le := hq.2.2.1
  have hcv_64 : s.core.cur_vars < 2 ^ 64 := by omega
  dsimp only [deducePushExpr, fvOp]
  viv_steps
  · have hlvl_pos : 0 < (s.core.lvl[ov.toNat]'hov_lvl).toNat := by c0_bound
    have hm0 : mrk_cur[ov.toNat]'hov_mrk = 0#8 := by
      have hm032 : (mrk_cur[ov.toNat]'hov_mrk).setWidth 32 = 0#32 := by assumption
      exact (bv8_zext32_eq0_iff _).mp hm032
    have hlvl_pos' : 0 < (s.core.lvl[ov.toNat]?.getD 0#32).toNat := by
      rwa [List.getElem?_eq_getElem hov_lvl, Option.getD_some]
    have hm0' : mrk_cur[ov.toNat]?.getD 0#8 = 0#8 := by
      rwa [List.getElem?_eq_getElem hov_mrk, Option.getD_some]
    have hql_lt := push_queue_lt hq hcv_le hov_lt hm0'
    have hql_ws1 : qlen.toNat < ws1_cur.length := by have := hq.2.1; omega
    have hql1 : (qlen + 1#64).toNat = qlen.toNat + 1 := by bv_omega
    obtain ⟨_, hq_next, hpre_next, _⟩ :=
      push_queue_step hq hcv_le hov_lt hlvl_pos' hm0' hov_trl
    viv_steps
    have hov_mod : ov.toNat % 2 ^ 64 = ov.toNat := Nat.mod_eq_of_lt (by omega)
    refine hJ (qlen + 1#64) _ _ _ (by omega) (by omega) hpre_next ?_ (Or.inr ?_) hm
    · simpa [hql1, hov_mod] using hq_next
    · rw [hql1]
      exact (mem_map_take_iff (by simp [hq.2.1]; omega)).mpr
        ⟨qlen.toNat, by omega, by rw [List.getElem?_set_self hql_ws1]; rfl⟩
  · have hm0 : mrk_cur[ov.toNat]'hov_mrk = 0#8 := by
      have hm032 : (mrk_cur[ov.toNat]'hov_mrk).setWidth 32 = 0#32 := by assumption
      exact (bv8_zext32_eq0_iff _).mp hm032
    have hm0' : mrk_cur[ov.toNat]?.getD 0#8 = 0#8 := by
      rwa [List.getElem?_eq_getElem hov_mrk, Option.getD_some]
    have hql_lt := push_queue_lt hq hcv_le hov_lt hm0'
    have hcv_le_q : s.core.cur_vars % 2 ^ 64 ≤ qlen.toNat := by c0_bound
    rw [Nat.mod_eq_of_lt hcv_64] at hcv_le_q; omega
  · have hm_ne0 : mrk_cur[ov.toNat]'hov_mrk ≠ 0#8 := fun h => by
      have hne32 : (mrk_cur[ov.toNat]'hov_mrk).setWidth 32 ≠ 0#32 := by assumption
      exact hne32 ((bv8_zext32_eq0_iff _).mpr h)
    have hm1 : mrk_cur[ov.toNat]?.getD 0#8 = 1#8 := by
      rcases hq.2.2.2.2.2.2.2.1 ov.toNat hov_lt with h0 | h1
      · rw [List.getElem?_eq_getElem hov_mrk, Option.getD_some] at h0; exact absurd h0 hm_ne0
      · exact h1
    exact hJ qlen mrk_cur ws1_cur m (Nat.le_refl _) hql_le (fun _ _ => rfl) hq
      (Or.inr ((hq.2.2.2.2.2.2.1 ov.toNat hov_lt).mp hm1)) hm
  · have hlvl0 : (s.core.lvl[ov.toNat]'hov_lvl).toNat = 0 := by c0_bound
    exact hJ qlen mrk_cur ws1_cur m (Nat.le_refl _) hql_le (fun _ _ => rfl) hq
      (Or.inl (by rwa [List.getElem?_eq_getElem hov_lvl, Option.getD_some])) hm

end

end LeanQbe.T.Examples.Kissat.Proof.Vivify
