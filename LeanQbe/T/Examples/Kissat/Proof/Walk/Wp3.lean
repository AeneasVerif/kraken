/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Walk.Helpers
public import LeanQbe.T.Examples.Kissat.Proof.Walk.Spec
public import LeanQbe.T.Examples.Kissat.Src.Walk

import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Walk WP Proofs — Part 3 (`Proof.Walk.Wp3`)

Proves canonical WP correctness for the `4` remaining Walk / Warmup / Rephase functions in
`Src.Walk`:
1. `full_walk_m7_wp` (`fullWalkM7Spec`)
2. `full_warmup_m7_wp` (`fullWarmupM7Spec`)
3. `full_walk_wp` (`fullWalkM6Spec`)
4. `full_rephase_wp` (`fullRephaseM6Spec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Walk

open Std.Sat
open Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
open LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
open LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
open LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
open LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
open LeanQbe.T.Examples.Kissat.Proof.Walk.Spec
open LeanQbe.T.Examples.Kissat.Src.Walk

open scoped FullArenaTactics
open scoped WalkMemTactics

/-! ## 1. Shared Walk / Warmup / Rephase Helpers -/

private theorem bv64_add1_lt {x : BitVec 64} {n : Nat}
    (h1 : x.toNat < n) (h2 : n + 1 < 2 ^ 64) : (x + 1#64).toNat = x.toNat + 1 := by
  bv_omega

private theorem bv64_rshift32_lt {x : BitVec 64} : (x >>> 32#64).toNat < 2 ^ 32 := by
  change (x >>> (32 : Nat)).toNat < 2 ^ 32
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt; omega

private theorem bv64_shr2_add1_le {cv mv : Nat} (hcv_pos : 0 < cv) (hcv : cv ≤ mv)
    (hmv : mv < 2 * dimacsBound) :
    ((BitVec.ofNat 64 cv >>> BitVec.signExtend 64 2#32) + 1#64).toNat ≤ 2 * mv := by
  unfold dimacsBound at hmv
  have hsh : (BitVec.ofNat 64 cv >>> BitVec.signExtend 64 2#32).toNat = cv / 4 := by
    change (BitVec.ofNat 64 cv >>> (2 : Nat)).toNat = cv / 4
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftRight_eq_div_pow]
  rw [BitVec.toNat_add, hsh, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega)]
  omega

private theorem lit_pos_shl64 {r : BitVec 64} (hr : r.toNat < 2 * dimacsBound) :
    ((r <<< (1 : Nat)).setWidth 32).toNat = 2 * r.toNat := by
  unfold dimacsBound at hr
  rw [BitVec.toNat_setWidth, bv64_shl1_toNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem lit_neg_shl64 {r : BitVec 64} (hr : r.toNat < 2 * dimacsBound) :
    (((r <<< (1 : Nat)).setWidth 32) ||| 1#32).toNat = 2 * r.toNat + 1 := by
  rw [BitVec.toNat_or, lit_pos_shl64 hr, show (1#32 : BitVec 32).toNat = 1 from rfl]
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => simp
  | succ k =>
    rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    simp [show (2 * r.toNat) / 2 = r.toNat by omega,
      show (2 * r.toNat + 1) / 2 = r.toNat by omega]

private theorem coreLengths_with_fuel {c : FullCfg} {k : FullCoreState} {f : BitVec 64}
    (h : k.LengthsOk c) : ({ k with fuel := f } : FullCoreState).LengthsOk c :=
  ⟨h.vals_len, h.lit_mark_len, h.mrk_len, h.flags_len, h.lvl_len, h.rsns_len, h.trl_len,
   h.trail_pos_len, h.tmp_len_arr, h.min_clr_len_arr, h.frame_trail_len, h.frame_dec_len,
   h.wvec_len, h.repr_len, h.min_stk_len, h.arena_len_arr, h.wstk_len_arr, h.cur_vars_ge,
   h.cur_vars_le, h.arena_len_le, h.wlen_le, h.trail_end_le, h.propagated_le, h.tmp_len_le,
   h.min_clr_len_le⟩

private theorem arenaPermEq_with_fuel {s1 s2 : FullCoreState} {fuel' : BitVec 64}
    (h : FullArenaPermEq s1 s2) : FullArenaPermEq s1 { s2 with fuel := fuel' } := h

private theorem sparse_with_probing_st {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s) (p st : BitVec 64) :
    FullSparseInv c F0 (FullState.mk { s.core with probing := p }
      { s.scratch with search_ticks := st }) := by
  obtain ⟨⟨⟨hc, hs⟩, F_cur, hw⟩, hlm, hnd, hscr, hd0⟩ := hsp
  refine ⟨⟨⟨{ hc with }, { hs with }⟩, F_cur,
    { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
              watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }⟩,
    hlm, hnd, hscr, hd0⟩

private theorem fullExtScratchPres_trans' {s1 s2 s3 : FullState}
    (h12 : FullExtScratchPres s1 s2) (h23 : FullExtScratchPres s2 s3) :
    FullExtScratchPres s1 s3 :=
  fullExtScratchPres_trans h12 h23

private theorem fullSparseInv_of_scratch {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (hsp : FullSparseInv c F0 s) (hcore : s'.core = s.core) (hlen : s'.LengthsOk c)
    (hpres : FullExtScratchPres s s') : FullSparseInv c F0 s' :=
  fullSparseInv_of_core_eq hsp hlen hcore hpres

private theorem walk_call_init_vals {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont rs}
    (hIv : Γ.Has "full_walk_init_vals_m7" initValsSpec)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hargs : vals args = (c.hdr, ())) (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_walk_init_vals_m7" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  refine hIv _ _ _ _ ?_; dsimp only [initValsSpec, scratchOnly]
  exact FullContract.intro (w := PUnit.unit) hlen trivial hm fun () s' m' hs' ⟨hc, hext⟩ hm' =>
    hk s' m' hc hs' hext hm'

private theorem walk_call_collect {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hCol : Γ.Has "full_walk_collect_m7" collectSpec)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hargs : vals args = (c.hdr, ())) (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_walk_collect_m7" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  refine hCol _ _ _ _ ?_; dsimp only [collectSpec, scratchOnly]
  exact FullContract.intro (w := PUnit.unit) hlen trivial hm
    fun (r, ()) s' m' hs' ⟨hc, hext⟩ hm' => hk r s' m' hc hs' hext hm'

private theorem walk_call_cb_inv {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {args : Tup (Arg Val) [i64, i64, i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hCb : Γ.Has "full_walk_cb_inv_m7" cbInvSpec)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hargs : vals args = (c.hdr, args.2.1.val, args.2.2.1.val, ()))
    (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      (r ≠ 0#64 → WalkTblExpsOk s') → (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_walk_cb_inv_m7" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  refine hCb _ _ _ _ ?_; dsimp only [cbInvSpec]
  exact FullContract.intro (w := PUnit.unit) hlen trivial hm
    fun (r, ()) s' m' hs' ⟨hc, hext, hexps⟩ hm' => hk r s' m' hc hs' hext hexps hm'

private theorem walk_call_build_occ {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hBo : Γ.Has "full_walk_build_occ_m7" buildOccSpec)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hargs : vals args = (c.hdr, args.2.1.val, ()))
    (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      WalkScrPrefixPres s s' → r.toNat ≤ args.2.1.val.toNat → (FullMem c s' ⋆ R) m' →
      wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_walk_build_occ_m7" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  refine hBo _ _ _ _ ?_; dsimp only [buildOccSpec]
  exact FullContract.intro (w := PUnit.unit) hlen trivial hm
    fun (r, ()) s' m' hs' ⟨hc, hext, hpre, hle⟩ hm' => hk r s' m' hc hs' hext hpre hle hm'

private theorem walk_call_effort {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hEff : Γ.Has "full_walk_effort_m7" effortSpec)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hargs : vals args = (c.hdr, args.2.1.val, ()))
    (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r m', (FullMem c s ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_walk_effort_m7" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  refine hEff _ _ _ _ ?_; dsimp only [effortSpec, readOnly]
  exact FullContract.intro (w := PUnit.unit) hlen trivial hm fun (r, ()) s' m' _ heq hm' => by
    subst s'; exact hk r m' hm'

private theorem walk_call_pick {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {args : Tup (Arg Val) [i64, i32, i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hPick : Γ.Has "full_walk_pick_m7" pickSpec)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hargs : vals args = (c.hdr, args.2.1.val, args.2.2.1.val, ()))
    (hexps : WalkTblExpsOk s) (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      WalkTblExpsOk s' → (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_walk_pick_m7" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  refine hPick _ _ _ _ ?_; dsimp only [pickSpec]
  exact FullContract.intro (w := PUnit.unit) hlen hexps hm
    fun (r, ()) s' m' hs' ⟨hc, hext, hexps'⟩ hm' => hk r s' m' hc hs' hext hexps' hm'

private theorem walk_call_flip {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {args : Tup (Arg Val) [i64, i32, i64, i64]}
    {k : Tup Val [i64] → Expr Val Cont rs}
    (hFlip : Γ.Has "full_walk_flip_m7" flipSpec)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hargs : vals args = (c.hdr, args.2.1.val, args.2.2.1.val, args.2.2.2.1.val, ()))
    (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      WalkScrPrefixPres s s' → (r &&& 0xFFFFFFFF#64).toNat ≤ args.2.2.1.val.toNat →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_walk_flip_m7" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  refine hFlip _ _ _ _ ?_; dsimp only [flipSpec]
  exact FullContract.intro (w := PUnit.unit) hlen trivial hm
    fun (r, ()) s' m' hs' ⟨hc, hext, hpre, hle⟩ hm' => hk r s' m' hc hs' hext hpre hle hm'

private theorem walk_call_save_min {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {args : Tup (Arg Val) [i64, i64, .bool]}
    {k : Tup Val [] → Expr Val Cont rs}
    (hSm : Γ.Has "full_walk_save_min_m7" saveMinSpec)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hargs : vals args = (c.hdr, args.2.1.val, args.2.2.1.val, ()))
    (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_walk_save_min_m7" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  refine hSm _ _ _ _ ?_; dsimp only [saveMinSpec, scratchOnly]
  exact FullContract.intro (w := PUnit.unit) hlen trivial hm
    fun () s' m' hs' ⟨hc, hext⟩ hm' => hk s' m' hc hs' hext hm'

private theorem decide_preserves_fullCore {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullCoreInv c F0 s) {v : Nat} {lit : BitVec 32}
    {flags' : List (BitVec 32)} {unas' unfl' : BitVec 64} {scratch' : FullScratch}
    (hsok' : scratch'.LengthsOk c) (hfll : flags'.length = c.max_vars)
    (hv_lt : v < s.core.cur_vars) (hval0 : s.core.vals[2 * v]?.getD 0#8 = 0#8)
    (hlit_eq : lit.toNat = 2 * v ∨ lit.toNat = 2 * v + 1) :
    let nlvl := s.core.cur_level + 1
    let ftrl' := s.core.frame_trail.set nlvl (BitVec.ofNat 32 s.core.trail_end)
    let fdec' := s.core.frame_dec.set nlvl lit
    let s' : FullState :=
      { core :=
          { s.core with
            vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := s.core.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 nlvl)
            rsns := s.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32
            trl := s.core.trl.set s.core.trail_end lit
            trail_pos := s.core.trail_pos.set (lit.toNat / 2) (BitVec.ofNat 32 s.core.trail_end)
            frame_trail := ftrl', frame_dec := fdec', trail_end := s.core.trail_end + 1
            cur_level := nlvl, unassigned := unas', unflushed := unfl' }
        scratch := scratch' }
    FullCoreInv c F0 s' ∧ s.core.vals[lit.toNat]?.getD 0#8 = 0#8 ∧
    s.core.trail_end < s.core.cur_vars ∧ nlvl ≤ c.max_vars := by
  intro nlvl ftrl' fdec' s'
  obtain ⟨F_cur, hw⟩ := hinv.witness; have hcl := hinv.lengths.core_ok
  have hcv := hcl.cur_vars_le; have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by omega
  have hlit_v : lit.toNat / 2 = v := by omega
  have hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
    rcases hlit_eq with he | ho
    · rw [he]; exact hval0
    · have hnot0 := (hw.vals_zero_iff (by omega : 2 * v < 2 * s.core.cur_vars)).mp hval0
      rw [ho]
      exact (hw.vals_zero_iff (by omega : 2 * v + 1 < 2 * s.core.cur_vars)).mpr fun i hi => by
        have := hnot0 i hi; omega
  have hte_lt : s.core.trail_end < s.core.cur_vars := hw.trail_end_lt_of_unassigned hlit_lt hun
  have hcl_le : s.core.cur_level ≤ s.core.trail_end := hw.cur_level_le
  have hnlvl_le : nlvl ≤ c.max_vars := by dsimp [nlvl]; omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by omega
  have hnot_var : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 :=
    (hw.vals_zero_iff hlit_lt).mp hun
  have hft_get : ∀ L ≤ nlvl, (ftrl'[L]?.getD 0#32).toNat =
      if L = nlvl then s.core.trail_end
      else (s.core.frame_trail[L]?.getD 0#32).toNat := fun L _ => by
    by_cases hL : L = nlvl
    · subst hL; dsimp only [ftrl']
      rw [List.getElem?_set_self (by rw [hcl.frame_trail_len]; omega), Option.getD_some,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp
    · dsimp only [ftrl']; rw [List.getElem?_set_ne (Ne.symm hL)]; simp [hL]
  have hfd_get : ∀ L ≤ nlvl, (fdec'[L]?.getD 0#32).toNat =
      if L = nlvl then lit.toNat else (s.core.frame_dec[L]?.getD 0#32).toNat := fun L _ => by
    by_cases hL : L = nlvl
    · subst hL; dsimp only [fdec']
      rw [List.getElem?_set_self (by rw [hcl.frame_dec_len]; omega), Option.getD_some]; simp
    · dsimp only [fdec']; rw [List.getElem?_set_ne (Ne.symm hL)]; simp [hL]
  have hcore' := chronoAssign_preserves_fullCore hinv (lit := lit) (rsn := 0xFFFFFFFF#32)
    (alvl := nlvl) (cur_level' := nlvl) (propagated' := s.core.propagated)
    (flags' := flags') (frame_trail' := ftrl') (frame_dec' := fdec')
    (unassigned' := unas') (unflushed' := unfl') (scratch' := scratch')
    hsok' hfll (by simp [ftrl', hcl.frame_trail_len]) (by simp [fdec', hcl.frame_dec_len])
    hlit_lt hun (Nat.le_refl _) (by have := hcl.propagated_le; omega) (by dsimp [nlvl]; omega)
    (fun L hL => by
      rw [hft_get L hL]; split
      · omega
      · have := hw.frame_trail_lt L (by dsimp [nlvl] at *; omega); omega)
    (fun L1 L2 h12 h2 => by
      rw [hft_get L1 (by omega), hft_get L2 h2]
      by_cases h2e : L2 = nlvl
      · by_cases h1e : L1 = nlvl
        · simp [h1e, h2e]
        · simp only [h1e, h2e, ↓reduceIte]; exact hw.frame_trail_lt L1 (by dsimp [nlvl] at *; omega)
      · have h1n : L1 ≠ nlvl := by omega
        simp only [h1n, h2e, ↓reduceIte]
        exact hw.frame_trail_mono L1 L2 h12 (by dsimp [nlvl] at *; omega))
    (fun L hL1 hLle i hi => by
      rw [hft_get L hLle] at hi
      by_cases hLe : L = nlvl
      · subst hLe; simp only [↓reduceIte] at hi
        have hne_i : i ≠ s.core.trail_end := by omega
        have hnv : (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := hnot_var i hi
        simp only [hne_i, hnv, ↓reduceIte]
        have := hw.lvl_le i hi; dsimp [nlvl]; omega
      · simp only [hLe, ↓reduceIte] at hi
        have hLle' : L ≤ s.core.cur_level := by dsimp [nlvl] at *; omega
        have hi_lt : i < s.core.trail_end := Nat.lt_of_lt_of_le hi (hw.frame_trail_lt L hLle')
        have hne_i : i ≠ s.core.trail_end := by omega
        have hnv : (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := hnot_var i hi_lt
        simp only [hne_i, hnv, ↓reduceIte]
        exact hw.frame_trail_before_lt L hL1 hLle' i hi)
    (fun L hL1 hLle => by
      rw [hfd_get L hLle]; split
      · exact hlit_lt
      · exact hw.frame_dec_lt L hL1 (by dsimp [nlvl] at *; omega))
    (fun i hi => by have := hw.lvl_le i hi; dsimp [nlvl]; omega)
    (fun L hL1 hLle => by
      by_cases hLe : L = nlvl
      · exact Or.inl hLe
      · exact Or.inr (hw.levels_inhabited L hL1 (by dsimp [nlvl] at *; omega)))
    (fun _ _ i hi => by have := hw.lvl_le i hi; dsimp [nlvl]; omega)
    (fun hz => by dsimp [nlvl] at hz; omega)
    (fun _ hne => absurd rfl hne)
    (fun _ hne _ => absurd rfl hne)
  have hnlvl_ne0 : nlvl ≠ 0 := by dsimp [nlvl]; omega
  simpa only [s', hnlvl_ne0, ↓reduceIte] using ⟨hcore', hun, hte_lt, hnlvl_le⟩

/-! ## 2. `full_walk_m7` (`fullWalkM7Spec`) -/

theorem full_walk_m7_wp (Γ : Env)
    (hRoundtrip : Γ.Has "full_dense_bin_roundtrip_fid" fullDenseBinRoundtripFidSpec)
    (hWatchLarge : Γ.Has "full_watch_large_clauses_fid" fullWatchLargeClausesSpec)
    (hInitVals : Γ.Has "full_walk_init_vals_m7" initValsSpec)
    (hCollect : Γ.Has "full_walk_collect_m7" collectSpec)
    (hCbInv : Γ.Has "full_walk_cb_inv_m7" cbInvSpec)
    (hBuildOcc : Γ.Has "full_walk_build_occ_m7" buildOccSpec)
    (hEffort : Γ.Has "full_walk_effort_m7" effortSpec)
    (hPick : Γ.Has "full_walk_pick_m7" pickSpec)
    (hFlip : Γ.Has "full_walk_flip_m7" flipSpec)
    (hSaveMin : Γ.Has "full_walk_save_min_m7" saveMinSpec) :
    ∀ a m Q X, walkCoreSpec a m Q X → Func.wp Γ full_walk_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  unfold walkCoreSpec at hs
  obtain ⟨c, s, F0, R, rfl, hlen, hsp, hm, hQ0⟩ := FullContract.elim hs
  let hQ : ∀ s' m', FullSparseInv c F0 s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.probing = s.core.probing →
      FullExtScratchPres s s' → (FullMem c s' ⋆ R) m' → Q () m' :=
    fun s' m' hsp' hap hcv hcl hfu hpr hext hm' =>
      hQ0 () s' m' hsp'.lengths ⟨hsp', hap, hcv, hcl, hfu, hpr, hext⟩ hm'
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmax := c.hmaxv; have hscr := c.hscr; unfold dimacsBound at hmax hscr
  have hret0 : Q () m :=
    hQ s m hsp (fullArenaPermEq_refl _) rfl rfl (Nat.le_refl _) rfl ⟨rfl, rfl⟩ hm
  unfold Func.wp full_walk_m7_body
  c0_hsplit; · c0_hsteps; exact hret0
  have hcv_pos : 0 < s.core.cur_vars := Nat.pos_of_ne_zero fun h0 => hc (by rw [h0]; rfl)
  c0_hsplit; · c0_hsteps; exact hret0
  c0_hsplit; · c0_hsteps; exact hret0
  c0_hsplit; · c0_hsteps; exact hret0
  have hcap2300 : 2300 ≤ c.scratch_cap := by
    rw [Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64),
      show (2300 : BitVec 64).toNat = 2300 from rfl] at hc; omega
  c0_hsteps_nogrp
  refine walk_call_bin_roundtrip hRoundtrip rfl hsp hm
    fun sR1 mR1 hspR1 hpermR1 hcvR1 hclR1 hfuR1 hprR1 hpresR1 hmR1 => ?_
  c0_hsteps_nogrp
  refine walk_call_watch_large hWatchLarge rfl hspR1 hmR1
    fun sW mW hspW hpermW hcvW hclW hfuW hprW hpresW hmW => ?_
  have hlenW := hspW.lengths
  have hpermW0 : FullArenaPermEq s.core sW.core := fullArenaPermEq_trans hpermR1 hpermW
  have hcvW0 : sW.core.cur_vars = s.core.cur_vars := hcvW.trans hcvR1
  have hclW0 : sW.core.cur_level = s.core.cur_level := hclW.trans hclR1
  have hfuW0 : sW.core.fuel = s.core.fuel := hfuW.trans hfuR1
  have hprW0 : sW.core.probing = s.core.probing := hprW.trans hprR1
  have hpresW0 : FullExtScratchPres s sW := fullExtScratchPres_trans' hpresR1 hpresW
  c0_hsteps_nogrp
  refine walk_call_init_vals hInitVals rfl hlenW hmW fun s1 m1 hcore1 hlen1 hpres1 hm1 => ?_
  c0_hsteps_nogrp
  refine walk_call_collect hCollect rfl hlen1 hm1 fun rcol s2 m2 hcore2 hlen2 hpres2 hm2 => ?_
  have hcore20 : s2.core = sW.core := hcore2.trans hcore1
  have hpres20 : FullExtScratchPres s s2 :=
    fullExtScratchPres_trans' hpresW0 (fullExtScratchPres_trans' hpres1 hpres2)
  c0_hsteps_nogrp
  refine wp_join_group (ts := [])
    (fun _ mE => ∃ sE : FullState, sE.core = sW.core ∧ sE.LengthsOk c ∧
      FullExtScratchPres s sE ∧ (FullMem c sE ⋆ R) mE)
    (fun _ ⟨⟩ mE ⟨sE, hcoreE, hlenE, hpresE, _hmE⟩ => by
      c0_hsteps
      let sE' : FullState := { sE with scratch :=
        { sE.scratch with walk_cnt_stat := sE.scratch.walk_cnt_stat + 1#64 } }
      have hlenE' : sE'.LengthsOk c := ⟨hlenE.core_ok, { hlenE.scratch_ok with }⟩
      have hcoreE' : sE'.core = { sW.core with fuel := sW.core.fuel } := by simp [sE', hcoreE]
      have hspE' : FullSparseInv c F0 sE' :=
        hspW.with_fuel_scratch hlenE' hcoreE'
          ⟨(hpresE.1.trans hpresW0.1.symm), (hpresE.2.trans hpresW0.2.symm)⟩
      exact hQ sE' _ hspE' (by simpa [sE', hcoreE] using hpermW0) (by simp [sE', hcoreE, hcvW0])
        (by simp [sE', hcoreE, hclW0]) (by simp [sE', hcoreE, hfuW0])
        (by simp [sE', hcoreE, hprW0]) hpresE ‹_›)
    (fun J26 hJ26 => by
      c0_hsplit; · c0_hsteps; exact hJ26 () m2 ⟨s2, hcore20, hlen2, hpres20, hm2⟩
      have hncl_ne := hc; clear hc
      c0_hsplit; · c0_hsteps; exact hJ26 () m2 ⟨s2, hcore20, hlen2, hpres20, hm2⟩
      clear hc
      c0_hsplit; · c0_hsteps; exact hJ26 () m2 ⟨s2, hcore20, hlen2, hpres20, hm2⟩
      have hcap_le := hc; clear hc
      let ncl := rcol >>> 32#64
      have hncl_lt : ncl.toNat < 2 ^ 32 := bv64_rshift32_lt
      have hncl_pos : 0 < ncl.toNat :=
        Nat.pos_of_ne_zero fun h0 => hncl_ne (BitVec.eq_of_toNat_eq h0)
      have hcap5 : 2200 + 5 * ncl.toNat ≤ c.scratch_cap := by
        change ¬ c.scratch_cap % 2 ^ 64 < (2200 + 5 * ncl.toNat) % 2 ^ 64 at hcap_le
        rw [Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 2200 + 5 * ncl.toNat < 2 ^ 64)] at hcap_le; omega
      c0_hsteps_nogrp
      refine walk_call_cb_inv hCbInv rfl hlen2 hm2
        fun rcb s3 m3 hcore3 hlen3 hpres3 hexps3 hm3 => ?_
      have hcore30 : s3.core = sW.core := hcore3.trans hcore20
      have hpres30 : FullExtScratchPres s s3 := fullExtScratchPres_trans' hpres20 hpres3
      c0_hsplit; · c0_hsteps; exact hJ26 () m3 ⟨s3, hcore30, hlen3, hpres30, hm3⟩
      have hexps3_ok : WalkTblExpsOk s3 := hexps3 hc
      clear hc
      c0_hsteps_nogrp
      refine walk_call_build_occ hBuildOcc rfl hlen3 hm3
        fun ru s4 m4 hcore4 hlen4 hpres4 hpre4 _ hm4 => ?_
      have hcore40 : s4.core = sW.core := hcore4.trans hcore30
      have hpres40 : FullExtScratchPres s s4 := fullExtScratchPres_trans' hpres30 hpres4
      have hexps4 : WalkTblExpsOk s4 := walkScrPrefixPres_tblExpsOk hpre4 hexps3_ok
      c0_hsteps_nogrp
      refine walk_call_effort hEffort rfl hlen4 hm4 fun step_lim m5 hm5 => ?_
      c0_hsteps_nogrp
      have hwcap := bv64_shr2_add1_le hcv_pos hlen.core_ok.cur_vars_le hmax
      have hbase : (2200#64 + 4#64 * ncl).toNat = 2200 + 4 * ncl.toNat := by
        rw [BitVec.toNat_add, BitVec.toNat_mul, show (2200#64 : BitVec 64).toNat = 2200 from rfl,
          show (4#64 : BitVec 64).toNat = 4 from rfl,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      refine wp_join_group (ts := [i64, i64, i64, i64, .bool, i64, i64])
        (fun _ mX => ∃ sX fuelX, sX.core = { sW.core with fuel := fuelX } ∧
          fuelX.toNat ≤ sW.core.fuel.toNat ∧ sX.LengthsOk c ∧
          FullExtScratchPres s sX ∧ (FullMem c sX ⋆ R) mX)
        (fun _ ⟨_, _, _, _, _, _, _, ⟨⟩⟩ mX ⟨sX, fuelX, hcoreX, hfuelX, hlenX, hpresX, hmX⟩ => by
          c0_hsteps_nogrp
          refine wp_join_group (ts := [])
            (fun _ mZ => ∃ sZ, sZ.core = { sW.core with fuel := fuelX } ∧
              sZ.LengthsOk c ∧ FullExtScratchPres s sZ ∧ (FullMem c sZ ⋆ R) mZ)
            (fun _ ⟨⟩ mZ ⟨sZ, hcoreZ, hlenZ, hpresZ, _hmZ⟩ => by
              c0_hsteps
              let sZ' : FullState := { sZ with scratch :=
                { sZ.scratch with walk_cnt_stat := sZ.scratch.walk_cnt_stat + 1#64 } }
              have hlenZ' : sZ'.LengthsOk c := ⟨hlenZ.core_ok, { hlenZ.scratch_ok with }⟩
              have hspZ' : FullSparseInv c F0 sZ' :=
                hspW.with_fuel_scratch hlenZ' hcoreZ
                  ⟨hpresZ.1.trans hpresW0.1.symm, hpresZ.2.trans hpresW0.2.symm⟩
              exact hQ sZ' _ hspZ' (by simpa [sZ', hcoreZ] using arenaPermEq_with_fuel hpermW0)
                (by simp [sZ', hcoreZ, hcvW0]) (by simp [sZ', hcoreZ, hclW0])
                (by simp [sZ', hcoreZ, hfuW0] at *; omega) (by simp [sZ', hcoreZ, hprW0])
                hpresZ ‹_›)
            (fun _ hJsave => by
              c0_hsplit
              · c0_hsteps_nogrp
                refine walk_call_save_min hSaveMin rfl hlenX hmX
                  fun sY mY hcoreY hlenY hpresY hmY => ?_
                c0_hsteps; exact hJsave () mY ⟨sY, hcoreY.trans hcoreX, hlenY,
                  fullExtScratchPres_trans' hpresX hpresY, hmY⟩
              · c0_hsteps; exact hJsave () mX ⟨sX, hcoreX, hlenX, hpresX, hmX⟩))
        (fun J53X hJ53X => by
          refine wp_loop_group (ts := [i64, i64, i64, i64, .bool, i64, i64])
            (fun fn _ mL => ∃ sL fuelL, sL.core = { sW.core with fuel := fuelL } ∧
              fuelL.toNat = fn ∧ fuelL.toNat ≤ sW.core.fuel.toNat ∧ sL.LengthsOk c ∧
              FullExtScratchPres s sL ∧ WalkTblExpsOk sL ∧ (FullMem c sL ⋆ R) mL) ?_ ?_
          · intro J53 fn ⟨uc, ml, bc, bu, fl, flp, tks, ⟨⟩⟩ mL hJ53
              ⟨sL, fuelL, hcoreL, hfnL, hfuelL, hlenL, hpresL, hexpsL, hmL⟩
            have hcoreL_fl : sL.core.fuel = fuelL := by rw [hcoreL]
            have hX0 := fun xs => hJ53X xs mL ⟨sL, fuelL, hcoreL, hfuelL, hlenL, hpresL, hmL⟩
            c0_hsplit; rotate_left; · c0_hsteps; exact hX0 _
            have huc_pos : 0 < uc.toNat := by simpa using hc
            c0_hsplit; rotate_left; · c0_hsteps; exact hX0 _
            have huc_le : uc.toNat ≤ ncl.toNat := hc
            c0_hsplit; rotate_left; · c0_hsteps; exact hX0 _
            c0_hsplit; rotate_left; · c0_hsteps; exact hX0 _
            have hf_pos : 0 < fuelL.toNat := by simpa [hcoreL_fl] using hc
            have hfn_sub : (fuelL - 1#64).toNat = fn - 1 := by bv_omega
            have hlt_n : fn - 1 < fn := by omega
            have hurem_lt : (flp % uc).toNat < uc.toNat := by
              rw [BitVec.toNat_umod]; exact Nat.mod_lt _ huc_pos
            have hslot_sb : (2200#64 + 4#64 * (rcol >>> 32#64) + flp % uc).toNat <
                sL.scratch.scratch_buf.length := by
              rw [hlenL.scratch_ok.scratch_buf_len, BitVec.toNat_add,
                show (2200#64 + 4#64 * (rcol >>> 32#64)).toNat = 2200 + 4 * ncl.toNat from hbase,
                Nat.mod_eq_of_lt (by omega)]; omega
            have huc_ne : uc ≠ 0#64 := fun h0 => by rw [h0] at huc_pos; simp at huc_pos
            c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
            c0_hstep; c0_hstep; c0_hstep; c0_hstep
            let sL1 : FullState := { sL with core := { sL.core with fuel := fuelL - 1#64 } }
            have hcoreL1 : sL1.core = { sW.core with fuel := fuelL - 1#64 } := by simp [sL1, hcoreL]
            have hfuelL1 : (fuelL - 1#64).toNat ≤ sW.core.fuel.toNat := by omega
            have hlenL1 : sL1.LengthsOk c :=
              ⟨coreLengths_with_fuel hlenL.core_ok, hlenL.scratch_ok⟩
            have hslot_sb1 : (2200#64 + 4#64 * (rcol >>> 32#64) + flp % uc).toNat <
                sL1.scratch.scratch_buf.length := hslot_sb
            have hmL1 : (FullMem c sL1 ⋆ R) m := by rw [hcoreL_fl] at hm; exact hm
            refine C0HeadStep.head_wp_load rfl
              (FullArenaTactics.c0_load_full_scratch_buf hslot_sb1 hmL1) ?_
            c0_hsplit
            · c0_hsteps; exact hJ53X _ m ⟨sL1, fuelL - 1#64, hcoreL1, hfuelL1, hlenL1, hpresL, ‹_›⟩
            · c0_hsteps_nogrp
              have hexpsL1 : WalkTblExpsOk sL1 := hexpsL
              refine walk_call_pick hPick rfl hexpsL1 hlenL1 hmL1
                fun rpick sL2 mL2 hcoreL2 hlenL2 hpresL2 hexpsL2 hmL2 => ?_
              have hcoreL2' : sL2.core = { sW.core with fuel := fuelL - 1#64 } :=
                hcoreL2.trans hcoreL1
              have hpresL20 : FullExtScratchPres s sL2 := fullExtScratchPres_trans' hpresL hpresL2
              c0_hsteps_nogrp; c0_hsplit
              · c0_hsteps; exact hJ53 (fn - 1) _ _ hlt_n
                  ⟨sL2, fuelL - 1#64, hcoreL2', hfn_sub, hfuelL1, hlenL2, hpresL20, hexpsL2, hmL2⟩
              · c0_hsteps_nogrp
                refine walk_call_flip hFlip rfl hlenL2 hmL2
                  fun rflip sL3 mL3 hcoreL3 hlenL3 hpresL3 hpreL3 _ hmL3 => ?_
                have hcoreL3' : sL3.core = { sW.core with fuel := fuelL - 1#64 } :=
                  hcoreL3.trans hcoreL2'
                have hpresL30 : FullExtScratchPres s sL3 :=
                  fullExtScratchPres_trans' hpresL20 hpresL3
                have hexpsL3 : WalkTblExpsOk sL3 := walkScrPrefixPres_tblExpsOk hpreL3 hexpsL2
                c0_hsteps_nogrp
                let PStep (mS : Mem 64) : Prop :=
                  ∃ sS, sS.core = { sW.core with fuel := fuelL - 1#64 } ∧ sS.LengthsOk c ∧
                    FullExtScratchPres s sS ∧ WalkTblExpsOk sS ∧ (FullMem c sS ⋆ R) mS
                refine wp_join_group (ts := [i64, i64, .bool]) (fun _ mFin => PStep mFin)
                  (fun _ ⟨_, _, _, ⟨⟩⟩ mFin
                      ⟨sFin, hcoreFin, hlenFin, hpresFin, hexpsFin, hmFin⟩ => by
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := [i64, i64, i64, .bool]) (fun _ mD => PStep mD)
                      (fun _ _ mD ⟨sD, hcoreD, hlenD, hpresD, hexpsD, hmD⟩ => by
                        c0_hsteps; exact hJ53 (fn - 1) _ _ hlt_n
                          ⟨sD, fuelL - 1#64, hcoreD, hfn_sub, hfuelL1, hlenD, hpresD, hexpsD, hmD⟩)
                      (fun J_done hJ_done => by
                        c0_hsplit; rotate_left
                        · c0_hsteps
                          exact hJ_done _ mFin ⟨sFin, hcoreFin, hlenFin, hpresFin, hexpsFin, hmFin⟩
                        refine wp_join_group (ts := [i64, i64, .bool]) (fun _ m14 => PStep m14)
                          (fun _ _ m14 h => by c0_hsteps; exact hJ_done _ m14 h)
                          (fun J14 hJ14 => by
                            c0_hsplit
                            · c0_hsteps
                              exact hJ14 _ mFin ⟨sFin, hcoreFin, hlenFin, hpresFin, hexpsFin, hmFin⟩
                            · refine wp_loop_group (ts := [i64])
                                (fun nb ⟨idx, ⟨⟩⟩ mB => idx.toNat ≤ s.core.cur_vars ∧
                                  nb = s.core.cur_vars - idx.toNat ∧ PStep mB) ?_ ?_
                              · intro J97 nb ⟨idx, ⟨⟩⟩ mB hJ97
                                  ⟨hidx, hnb, sB, hcoreB, hlenB, hpresB, hexpsB, hmB⟩
                                c0_hsplit; rotate_left
                                · c0_hsteps
                                  exact hJ14 _ mB ⟨sB, hcoreB, hlenB, hpresB, hexpsB, hmB⟩
                                have hidx_lt : idx.toNat < s.core.cur_vars := by
                                  have hcvB := hlenB.core_ok.cur_vars_le
                                  rw [hcoreB, hcvW0] at hcvB
                                  rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                                  exact hc
                                have h2idx : (idx <<< (1 : BitVec 64)).toNat <
                                    sB.scratch.walk_vals.length := by
                                  change (idx <<< (1 : Nat)).toNat < sB.scratch.walk_vals.length
                                  rw [bv64_shl1_toNat_lt (by omega), hlenB.scratch_ok.walk_vals_len]
                                  omega
                                have hidx_wb : idx.toNat < sB.scratch.walk_best.length := by
                                  rw [hlenB.scratch_ok.walk_best_len]; omega
                                have hidx1 : (idx + 1).toNat = idx.toNat + 1 := bv64_add1_lt hidx_lt
                                  (by omega)
                                c0_hsteps
                                let sB' : FullState := { sB with scratch := { sB.scratch with
                                  walk_best := sB.scratch.walk_best.set idx.toNat
                                    (sB.scratch.walk_vals[
                                      (idx <<< (1 : BitVec 64)).toNat]'h2idx) } }
                                have hlenB' : sB'.LengthsOk c := ⟨hlenB.core_ok,
                                  { hlenB.scratch_ok with
                                    walk_best_len := by
                                      simp [sB', hlenB.scratch_ok.walk_best_len] }⟩
                                exact hJ97 (s.core.cur_vars - (idx.toNat + 1)) _ _ (by omega)
                                  ⟨by rw [hidx1]; omega, by rw [hidx1], sB', hcoreB, hlenB',
                                    hpresB, hexpsB, ‹_›⟩
                              · intro J97 hJ97; c0_hsteps
                                exact hJ97 s.core.cur_vars _ mFin
                                  ⟨Nat.zero_le _, rfl, sFin, hcoreFin, hlenFin, hpresFin,
                                    hexpsFin, hmFin⟩)))
                  (fun J_fin hJ_fin => by
                    c0_hsplit; rotate_left
                    · c0_hsteps
                      exact hJ_fin _ mL3 ⟨sL3, hcoreL3', hlenL3, hpresL30, hexpsL3, hmL3⟩
                    clear hc
                    refine wp_join_group (ts := [i64, i64, .bool]) (fun _ m93 => PStep m93)
                      (fun _ ⟨ml0, _, _, ⟨⟩⟩ m93
                          ⟨s93, hcore93, hlen93, hpres93, hexps93, hm93⟩ => by
                        refine wp_join_group (ts := [i64]) (fun _ m96 => PStep m96)
                          (fun _ _ m96 h => by c0_hsteps; exact hJ_fin _ m96 h)
                          (fun J96 hJ96 => by
                            c0_hsplit; rotate_left
                            · c0_hsteps
                              exact hJ96 _ m93 ⟨s93, hcore93, hlen93, hpres93, hexps93, hm93⟩
                            clear hc
                            c0_hsplit; rotate_left
                            · c0_hsteps
                              exact hJ96 _ m93 ⟨s93, hcore93, hlen93, hpres93, hexps93, hm93⟩
                            have hml_ws : ml0.toNat < s93.scratch.wsort.length := by
                              rw [hlen93.scratch_ok.wsort_len]
                              have hlt : ml0.toNat < (BitVec.ofNat 64 s.core.cur_vars >>>
                                BitVec.signExtend 64 2#32 + 1#64).toNat := hc
                              omega
                            c0_hsteps
                            let s96 : FullState := { s93 with scratch := { s93.scratch with
                              wsort := s93.scratch.wsort.set ml0.toNat
                                ((BitVec.setWidth 32 (rpick &&& 4294967295#64)) >>> 1#32) } }
                            have hlen96 : s96.LengthsOk c := ⟨hlen93.core_ok,
                              { hlen93.scratch_ok with
                                wsort_len := by simp [s96, hlen93.scratch_ok.wsort_len] }⟩
                            exact hJ96 _ _ ⟨s96, hcore93, hlen96, hpres93, hexps93, ‹_›⟩))
                      (fun J93 hJ93 => by
                        c0_hsplit; rotate_left
                        · c0_hsteps
                          exact hJ93 _ mL3 ⟨sL3, hcoreL3', hlenL3, hpresL30, hexpsL3, hmL3⟩
                        refine wp_join_group (ts := [i64, i64, .bool]) (fun _ mB => PStep mB)
                          (fun _ _ mB h => by c0_hsteps; exact hJ93 _ mB h)
                          (fun J93b hJ93b => by
                            c0_hsplit; rotate_left
                            · c0_hsteps
                              exact hJ93b _ mL3 ⟨sL3, hcoreL3', hlenL3, hpresL30, hexpsL3, hmL3⟩
                            clear hc
                            c0_hsplit; rotate_left
                            · c0_hsteps
                              exact hJ93b _ mL3 ⟨sL3, hcoreL3', hlenL3, hpresL30, hexpsL3, hmL3⟩
                            have hbc_le : bc.toNat ≤ ml.toNat := hc; clear hc
                            c0_hsplit; rotate_left
                            · c0_hsteps
                              exact hJ93b _ mL3 ⟨sL3, hcoreL3', hlenL3, hpresL30, hexpsL3, hmL3⟩
                            have hml_wsort : ml.toNat ≤ 2 * c.max_vars := by
                              have hml_le : ml.toNat ≤ (BitVec.ofNat 64 s.core.cur_vars >>>
                                BitVec.signExtend 64 2#32 + 1#64).toNat := hc
                              omega
                            refine wp_loop_group (ts := [i64])
                              (fun nk ⟨k, ⟨⟩⟩ mK => k.toNat ≤ bc.toNat ∧ nk = bc.toNat - k.toNat ∧
                                PStep mK) ?_ ?_
                            · intro J97 nk ⟨k, ⟨⟩⟩ mK hJ97
                                ⟨hk_le, hnk, sK, hcoreK, hlenK, hpresK, hexpsK, hmK⟩
                              c0_hsplit
                              · have hk_lt : k.toNat < bc.toNat := hc; clear hc
                                have hk_ws : k.toNat < sK.scratch.wsort.length := by
                                  rw [hlenK.scratch_ok.wsort_len]; omega
                                have hk1 : (k + 1).toNat = k.toNat + 1 :=
                                  bv64_add1_lt hk_lt (by omega)
                                c0_hsteps_nogrp
                                refine wp_join_group (ts := []) (fun _ m99 => PStep m99)
                                  (fun _ ⟨⟩ m99 ⟨s99, hcore99, hlen99, hpres99, hexps99, hm99⟩ => by
                                    c0_hsteps; exact hJ97 (bc.toNat - (k.toNat + 1)) _ _ (by omega)
                                      ⟨by rw [hk1]; omega, by rw [hk1], s99, hcore99, hlen99,
                                        hpres99, hexps99, hm99⟩)
                                  (fun J99 hJ99 => by
                                    c0_hsplit; rotate_left
                                    · c0_hsteps
                                      exact hJ99 () mK ⟨sK, hcoreK, hlenK, hpresK, hexpsK, hmK⟩
                                    have hw_lt : (sK.scratch.wsort[k.toNat]'hk_ws).toNat <
                                        sK.scratch.walk_best.length := by
                                      rw [hlenK.scratch_ok.walk_best_len]
                                      have hcvK := hlenK.core_ok.cur_vars_le
                                      rw [hcoreK, hcvW0] at hcvK
                                      rw [Nat.mod_eq_of_lt
                                        (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                                      omega
                                    have hw64_lt :
                                        ((sK.scratch.wsort[k.toNat]'hk_ws).setWidth 64).toNat <
                                          sK.scratch.walk_best.length := by
                                      rw [bv32_lit_toNat_mod64]; exact hw_lt
                                    c0_hsteps_nogrp
                                    refine wp_join_group (ts := [i32]) (fun _ mP => mK = mP) ?_ ?_
                                    · intro _ ⟨phP, ⟨⟩⟩ mP hmEq; rcases hmEq with rfl
                                      c0_hsteps!
                                      let sP : FullState := { sK with scratch := { sK.scratch with
                                        walk_best := sK.scratch.walk_best.set
                                          ((sK.scratch.wsort[k.toNat]'hk_ws).setWidth 64).toNat
                                          (phP.setWidth 8) } }
                                      have hlenP : sP.LengthsOk c := ⟨hlenK.core_ok,
                                        { hlenK.scratch_ok with
                                          walk_best_len := by
                                            simp [sP, hlenK.scratch_ok.walk_best_len] }⟩
                                      exact hJ99 () _ ⟨sP, hcoreK, hlenP, hpresK, hexpsK, ‹_›⟩
                                    · intro J106 hJ106; c0_hsteps <;> exact hJ106 _ _ rfl)
                              · c0_hsteps_nogrp
                                refine wp_loop_group (ts := [i64])
                                  (fun nj ⟨j, ⟨⟩⟩ mJ => j.toNat ≤ (ml - bc).toNat ∧
                                    nj = (ml - bc).toNat - j.toNat ∧ PStep mJ) ?_ ?_
                                · intro J100 nj ⟨j, ⟨⟩⟩ mJ hJ100
                                    ⟨hj_le, hnj, sJ, hcoreJ, hlenJ, hpresJ, hexpsJ, hmJ⟩
                                  c0_hsplit; rotate_left
                                  · c0_hsteps
                                    exact hJ93b _ mJ ⟨sJ, hcoreJ, hlenJ, hpresJ, hexpsJ, hmJ⟩
                                  have hj_lt : j.toNat < (ml - bc).toNat := hc
                                  have hsub_eq : (ml - bc).toNat = ml.toNat - bc.toNat := by
                                    bv_omega
                                  have hsrc : (bc + j).toNat < sJ.scratch.wsort.length := by
                                    rw [hlenJ.scratch_ok.wsort_len, BitVec.toNat_add,
                                      Nat.mod_eq_of_lt (by omega)]; omega
                                  have hdst : j.toNat < sJ.scratch.wsort.length := by
                                    rw [hlenJ.scratch_ok.wsort_len]; omega
                                  have hj1 : (j + 1).toNat = j.toNat + 1 :=
                                    bv64_add1_lt hj_lt (by omega)
                                  c0_hsteps
                                  let sJ' : FullState := { sJ with scratch := { sJ.scratch with
                                    wsort := sJ.scratch.wsort.set j.toNat
                                      (sJ.scratch.wsort[(bc + j).toNat]'hsrc) } }
                                  have hlenJ' : sJ'.LengthsOk c := ⟨hlenJ.core_ok,
                                    { hlenJ.scratch_ok with
                                      wsort_len := by simp [sJ', hlenJ.scratch_ok.wsort_len] }⟩
                                  exact hJ100 ((ml - bc).toNat - (j.toNat + 1)) _ _ (by omega)
                                    ⟨by rw [hj1]; omega, by rw [hj1], sJ', hcoreJ, hlenJ',
                                      hpresJ, hexpsJ, ‹_›⟩
                                · intro J100 hJ100; c0_hsteps
                                  exact hJ100 (ml - bc).toNat _ mK
                                    ⟨Nat.zero_le _, rfl, sK, hcoreK, hlenK, hpresK, hexpsK, hmK⟩
                            · intro J97 hJ97; c0_hsteps
                              exact hJ97 bc.toNat _ mL3 ⟨Nat.zero_le _, rfl, sL3, hcoreL3',
                                hlenL3, hpresL30, hexpsL3, hmL3⟩)))
          · intro J53 hJ53; c0_hsteps
            exact hJ53 sW.core.fuel.toNat _ m5
              ⟨s4, sW.core.fuel, hcore40, rfl, Nat.le_refl _, hlen4, hpres40, hexps4, hm5⟩))

/-! ## 3. `full_warmup_m7` (`fullWarmupM7Spec`) -/

theorem full_warmup_m7_wp (Γ : Env)
    (hNdv : Γ.Has "full_next_dec_var" fullNextDecVarSpec)
    (hAssign : Γ.Has "full_assign" fullAssignSpec)
    (hPropBey : Γ.Has "full_propagate_beyond_m7" propagateBeyondM6Spec)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec) :
    ∀ a m Q X, walkSpec a m Q X → Func.wp Γ full_warmup_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  unfold walkSpec at hs
  obtain ⟨c, ext, s, F0, R, rfl, hcfg, hext, _, hsp, hm, hQ0⟩ := M6HdrContract.elim hs
  have hinv : FullM6HdrInv c F0 ext s := ⟨hcfg, hext, hsp⟩
  let hQ : ∀ ext' s' m', FullM6HdrInv c F0 ext' s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (s.core.probing = 0#64 → s'.core.probing = 0#64) →
      FullExtScratchPres s s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m' :=
    fun ext' s' m' hinv' hap hcv hcl hfu hpr hext' hm' =>
      hQ0 () ext' s' m' hinv'.extOk trivial hinv'.sparse.lengths
        ⟨hinv'.sparse, hap, hcv, hcl, hfu, hpr, hext'⟩ hm'
  have hlen := hsp.lengths; have hmax := c.hmaxv; unfold dimacsBound at hmax
  have hcl0_lt : s.core.cur_level ≤ s.core.cur_vars := by
    obtain ⟨_, hw0⟩ := hsp.1.witness; exact Nat.le_trans hw0.cur_level_le hlen.core_ok.trail_end_le
  rw [fullM6HdrMem_iff] at hm
  have hret0 : Q () m := hQ ext s m hinv (fullArenaPermEq_refl _) rfl rfl
    (Nat.le_refl _) (fun h => h) ⟨rfl, rfl⟩ ((fullM6HdrMem_iff ..).mpr hm)
  unfold Func.wp full_warmup_m7_body
  c0_hsteps_nogrp; c0_hsteps_nogrp
  all_goals try exact hret0
  have hcv_le_entry : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have hcl_entry : s.core.cur_level = 0 := by
    have hcl_eq0 : BitVec.ofNat 64 s.core.cur_level = 0 := by assumption
    have h1 := congrArg BitVec.toNat hcl_eq0
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : s.core.cur_level < 2 ^ 64)] using h1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun _ mE => ∃ extE sE, FullM6HdrInv c F0 extE sE ∧ FullArenaPermEq s.core sE.core ∧
      sE.core.cur_vars = s.core.cur_vars ∧ sE.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      FullExtScratchPres s sE ∧ (FullMem c sE ⋆ (array64 (c.hdr - 2304) extE ⋆ R)) mE)
    (fun _ _ mE ⟨extE, sE, hinvE, hpermE, hcvE, hfuelE, hpresE, _hmE⟩ => by
      c0_hsteps_nogrp
      let sE1 : FullState := FullState.mk { sE.core with probing := 1#64 } sE.scratch
      have hspE1 : FullSparseInv c F0 sE1 :=
        sparse_with_probing_st hinvE.sparse 1#64 sE.scratch.search_ticks
      have hinvE1 : FullM6HdrInv c F0 extE sE1 := FullM6HdrInv.mk_inv hcfg hinvE.extOk hspE1
      have hpermE1 : FullArenaPermEq s.core sE1.core := hpermE
      refine walk_call_backtrack_m6 hBt rfl hinvE1 (Nat.zero_le _)
        ((fullM6HdrMem_iff ..).mpr ‹_›)
        fun sB mB hinvB hpermB hcvB hclB _ hfuelB _ hpresB hmB => ?_
      rw [fullM6HdrMem_iff] at hmB
      c0_hsteps
      let sF : FullState := FullState.mk { sB.core with probing := s.core.probing }
        { sB.scratch with search_ticks := s.scratch.search_ticks }
      have hinvF : FullM6HdrInv c F0 extE sF := .mk_inv hcfg hinvE.extOk
        (sparse_with_probing_st hinvB.sparse s.core.probing s.scratch.search_ticks)
      have hclF : sF.core.cur_level = s.core.cur_level := by
        show sB.core.cur_level = s.core.cur_level; rw [hclB, hcl_entry]; simp
      have hfuelF : sF.core.fuel.toNat ≤ s.core.fuel.toNat := by
        change sB.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hfuelB]; exact hfuelE
      exact hQ extE sF _ hinvF (fullArenaPermEq_trans hpermE1 hpermB) (hcvB.trans hcvE) hclF hfuelF
        (fun h => h) (fullExtScratchPres_trans' hpresE hpresB)
        ((fullM6HdrMem_iff ..).mpr ‹_›))
    (fun J46E hJ46E => by
      refine wp_loop_group (ts := [i64])
        (fun fn ⟨k, ⟨⟩⟩ mL => ∃ extL sL, k.toNat ≤ s.core.cur_vars ∧
          fn = s.core.cur_vars - k.toNat ∧ FullM6HdrInv c F0 extL sL ∧
          FullArenaPermEq s.core sL.core ∧ sL.core.cur_vars = s.core.cur_vars ∧
          sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧ FullExtScratchPres s sL ∧
          (FullMem c sL ⋆ (array64 (c.hdr - 2304) extL ⋆ R)) mL) ?_ ?_
      · intro J46 fn ⟨k, ⟨⟩⟩ mL hJ46
          ⟨extL, sL, hk_le, hfn, hinvL, hpermL, hcvL, hfuelL, hpresL, hmL⟩
        have hlenL := hinvL.sparse.lengths
        c0_hsplit; rotate_left
        · c0_hsteps; exact hJ46E (k, ()) mL ⟨extL, sL, hinvL, hpermL, hcvL, hfuelL, hpresL, hmL⟩
        have hk_lt : k.toNat < s.core.cur_vars := by
          rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc; exact hc
        have hk1 : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_lt hk_lt (by omega)
        have hlt_n : s.core.cur_vars - (k.toNat + 1) < fn := by omega
        c0_hsplit; rotate_left
        · c0_hsteps; exact hJ46E (k, ()) mL ⟨extL, sL, hinvL, hpermL, hcvL, hfuelL, hpresL, hmL⟩
        c0_hsplit; rotate_left
        · c0_hsteps; exact hJ46E (k, ()) mL ⟨extL, sL, hinvL, hpermL, hcvL, hfuelL, hpresL, hmL⟩
        c0_hsplit; rotate_left
        · c0_hsteps; exact hJ46E (k, ()) mL ⟨extL, sL, hinvL, hpermL, hcvL, hfuelL, hpresL, hmL⟩
        c0_hsteps_nogrp
        refine walk_call_next_dec_var_m6 hNdv rfl hinvL ((fullM6HdrMem_iff ..).mpr hmL)
          fun r sL2 mL2 hinvL2 hcoreL2 hpresL2 hresL2 hmL2 => ?_
        rw [fullM6HdrMem_iff] at hmL2
        have hlenL2 := hinvL2.sparse.lengths
        have hpermL2 : FullArenaPermEq s.core sL2.core := by rw [hcoreL2]; exact hpermL
        have hcvL2 : sL2.core.cur_vars = s.core.cur_vars := by rw [hcoreL2]; exact hcvL
        have hfuelL2 : sL2.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcoreL2]; exact hfuelL
        have hpresL20 : FullExtScratchPres s sL2 := fullExtScratchPres_trans' hpresL hpresL2
        c0_hsteps_nogrp; c0_hsplit
        · c0_hsteps; exact hJ46E (k, ()) mL2
            ⟨extL, sL2, hinvL2, hpermL2, hcvL2, hfuelL2, hpresL20, hmL2⟩
        have hr_spec : r.toNat < sL2.core.cur_vars ∧
            sL2.core.vals[2 * r.toNat]?.getD 0#8 = 0#8 := by
          rcases hresL2 with h0 | hok
          · exact absurd h0 hc
          · simpa [hcoreL2] using hok
        have hr_lt : r.toNat < c.max_vars := by have := hlenL2.core_ok.cur_vars_le; omega
        have hr_ph : r.toNat < sL2.scratch.phases.length := by
          rw [hlenL2.scratch_ok.phases_len]; exact hr_lt
        have hr_pt : r.toNat < sL2.scratch.phases_target.length := by
          rw [hlenL2.scratch_ok.phases_target_len]; exact hr_lt
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i8])
          (fun _ m61 => (FullMem c sL2 ⋆ (array64 (c.hdr - 2304) extL ⋆ R)) m61)
          (fun _ ⟨_, ⟨⟩⟩ m61 hm61 => by
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i32])
              (fun ⟨lit, ⟨⟩⟩ m62 =>
                (lit.toNat = 2 * r.toNat ∨ lit.toNat = 2 * r.toNat + 1) ∧
                (FullMem c sL2 ⋆ (array64 (c.hdr - 2304) extL ⋆ R)) m62)
              (fun _ ⟨lit, ⟨⟩⟩ m62 ⟨hlit_eq, hm62⟩ => by
                have hcl_L2 : sL2.core.cur_level ≤ sL2.core.cur_vars := by
                  obtain ⟨_, hwL2⟩ := hinvL2.sparse.1.witness
                  exact Nat.le_trans hwL2.cur_level_le hlenL2.core_ok.trail_end_le
                c0_hsplit
                · c0_hsteps; exact hJ46E (k, ()) m62
                    ⟨extL, sL2, hinvL2, hpermL2, hcvL2, hfuelL2, hpresL20, hm62⟩
                have hnlvl_le : sL2.core.cur_level + 1 ≤ c.max_vars := by
                  have hcv := hlenL2.core_ok.cur_vars_le
                  change ¬ c.max_vars % 2 ^ 64 < (sL2.core.cur_level + 1) % 2 ^ 64 at hc
                  rw [Nat.mod_eq_of_lt (by omega : c.max_vars < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : sL2.core.cur_level + 1 < 2 ^ 64)] at hc; omega
                have hnlvl_ft : sL2.core.cur_level + 1 < sL2.core.frame_trail.length := by
                  rw [hlenL2.core_ok.frame_trail_len]; omega
                have hnlvl_fd : sL2.core.cur_level + 1 < sL2.core.frame_dec.length := by
                  rw [hlenL2.core_ok.frame_dec_len]; omega
                c0_hsteps_nogrp
                let nlvl := sL2.core.cur_level + 1
                let ft' := sL2.core.frame_trail.set nlvl (BitVec.ofNat 32 sL2.core.trail_end)
                let fd' := sL2.core.frame_dec.set nlvl lit
                let sDec : FullState := { sL2 with core := { sL2.core with
                  frame_trail := ft', frame_dec := fd', cur_level := nlvl } }
                have hlenDec : sDec.LengthsOk c :=
                  ⟨{ hlenL2.core_ok with
                    frame_trail_len := by
                      dsimp [sDec, ft']; rw [List.length_set, hlenL2.core_ok.frame_trail_len]
                    frame_dec_len := by
                      dsimp [sDec, fd']; rw [List.length_set, hlenL2.core_ok.frame_dec_len] },
                   hlenL2.scratch_ok⟩
                have hdec_probe := decide_preserves_fullCore
                  (unas' := sL2.core.unassigned) (unfl' := sL2.core.unflushed)
                  hinvL2.sparse.1 hlenL2.scratch_ok hlenL2.core_ok.flags_len hr_spec.1 hr_spec.2
                  hlit_eq
                have hguard_false : ¬(sDec.core.cur_vars ≤ lit.toNat / 2 ∨
                    c.max_vars ≤ sDec.core.trail_end ∨
                    sDec.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
                  have hcv_le2 := hlenL2.core_ok.cur_vars_le
                  rintro (h1 | h2 | h3)
                  · exact absurd (show lit.toNat / 2 = r.toNat by omega ▸ h1)
                      (Nat.not_le.mpr hr_spec.1)
                  · exact absurd h2 (Nat.not_le.mpr (Nat.lt_of_lt_of_le hdec_probe.2.2.1 hcv_le2))
                  · exact h3 hdec_probe.2.1
                have hte_bv : (BitVec.ofNat 64 sL2.core.trail_end).setWidth 32 =
                    BitVec.ofNat 32 sL2.core.trail_end := by apply BitVec.eq_of_toNat_eq; simp
                have hnlvl_nat : (BitVec.ofNat 64 sL2.core.cur_level + 1#64).toNat = nlvl := by
                  dsimp [nlvl]; bv_omega
                refine wp_call_of_spec _ _ (hAssign _ _ _ _ ?_)
                refine ⟨c, sDec, array64 (c.hdr - 2304) extL ⋆ R, rfl, hlenDec,
                  (by dsimp [sDec, nlvl]; omega),
                  (by simp only [sDec, nlvl, ft', fd', ← hnlvl_nat, ← hte_bv]; exact hm), ?_⟩
                split
                · rename_i h; exact False.elim (hguard_false h)
                · dsimp only
                  intro flagsA unassA phasesA mA hflA hphA hmA
                  have hdec_ok := decide_preserves_fullCore
                    (unas' := unassA) (unfl' := sL2.core.unflushed)
                    (scratch' := { sL2.scratch with phases := phasesA }) hinvL2.sparse.1
                    { hlenL2.scratch_ok with phases_len := hphA } hflA
                    hr_spec.1 hr_spec.2 hlit_eq
                  let sA : FullState :=
                    { core := { sL2.core with
                        unassigned := unassA, trail_end := sL2.core.trail_end + 1,
                        vals := (sL2.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 255#8,
                        flags := flagsA,
                        lvl := sL2.core.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 nlvl),
                        rsns := sL2.core.rsns.set (lit.toNat / 2) 4294967295#32,
                        trl := sL2.core.trl.set sL2.core.trail_end lit,
                        trail_pos := sL2.core.trail_pos.set (lit.toNat / 2)
                          (BitVec.ofNat 32 sL2.core.trail_end),
                        frame_trail := ft', frame_dec := fd', cur_level := nlvl },
                      scratch := { sL2.scratch with phases := phasesA } }
                  have hinvA : FullM6HdrInv c F0 extL sA := .mk_inv hcfg hinvL2.extOk
                    ⟨hdec_ok.1, hinvL2.sparse.2.1, hinvL2.sparse.2.2.1, hinvL2.sparse.2.2.2.1,
                      hinvL2.sparse.2.2.2.2⟩
                  have hnlvl_nz : nlvl ≠ 0 := by dsimp [nlvl]; omega
                  have hsA_hm : (FullMem c sA ⋆ (array64 (c.hdr - 2304) extL ⋆ R)) mA := by
                    simpa [sA, sDec, nlvl, hnlvl_nz] using hmA
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [])
                    (fun _ mJ => ∃ extJ sJ, FullM6HdrInv c F0 extJ sJ ∧
                      FullArenaPermEq s.core sJ.core ∧ sJ.core.cur_vars = s.core.cur_vars ∧
                      sJ.core.fuel.toNat ≤ s.core.fuel.toNat ∧ FullExtScratchPres s sJ ∧
                      (FullMem c sJ ⋆ (array64 (c.hdr - 2304) extJ ⋆ R)) mJ)
                    (fun _ ⟨⟩ mJ ⟨extJ, sJ, hinvJ, hpermJ, hcvJ, hfuelJ, hpresJ, hmJ⟩ => by
                      c0_hsteps
                      exact hJ46 (s.core.cur_vars - (k.toNat + 1)) (k + 1#64, ()) mJ hlt_n
                        ⟨extJ, sJ, by rw [hk1]; omega, by rw [hk1], hinvJ, hpermJ, hcvJ, hfuelJ,
                          hpresJ, hmJ⟩)
                    (fun J75 hJ75 => by
                      refine wp_loop_group (ts := [])
                        (fun fn _ mP => ∃ extP sP, fn = sP.core.fuel.toNat ∧
                          FullM6HdrInv c F0 extP sP ∧ FullArenaPermEq s.core sP.core ∧
                          sP.core.cur_vars = s.core.cur_vars ∧
                          sP.core.fuel.toNat ≤ s.core.fuel.toNat ∧ FullExtScratchPres s sP ∧
                          (FullMem c sP ⋆ (array64 (c.hdr - 2304) extP ⋆ R)) mP) ?_ ?_
                      · intro J_prop fn ⟨⟩ mP hJ_prop
                          ⟨extP, sP, hfnP, hinvP, hpermP, hcvP, hfuelP, hpresP, hmP⟩
                        have hlenP := hinvP.sparse.lengths
                        c0_hsplit; rotate_left
                        · c0_hsteps; exact hJ75 () mP
                            ⟨extP, sP, hinvP, hpermP, hcvP, hfuelP, hpresP, hmP⟩
                        have hprop_lt : sP.core.propagated < sP.core.trail_end := by
                          have := hlenP.core_ok.trail_end_le; have := hlenP.core_ok.propagated_le
                          have := hlenP.core_ok.cur_vars_le
                          change (BitVec.ofNat 64 sP.core.propagated).toNat <
                            (BitVec.ofNat 64 sP.core.trail_end).toNat at hc
                          rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc
                          exact hc
                        c0_hsplit; rotate_left
                        · c0_hsteps; exact hJ75 () mP
                            ⟨extP, sP, hinvP, hpermP, hcvP, hfuelP, hpresP, hmP⟩
                        c0_hsplit; rotate_left
                        · c0_hsteps; exact hJ75 () mP
                            ⟨extP, sP, hinvP, hpermP, hcvP, hfuelP, hpresP, hmP⟩
                        c0_hsteps_nogrp
                        refine walk_call_propagate_beyond_m7_m6 hPropBey rfl hinvP
                          ((fullM6HdrMem_iff ..).mpr hmP)
                          fun pr extP2 sP2 mP2 hinvP2 hpermP2 hcvP2 _ _ hfuelP2 _ hpr0
                              hpresP2 hmP2 => ?_
                        rw [fullM6HdrMem_iff] at hmP2
                        have hpermP0 := fullArenaPermEq_trans hpermP hpermP2
                        have hcvP0 := hcvP2.trans hcvP
                        have hfuelP0 : sP2.core.fuel.toNat ≤ s.core.fuel.toNat :=
                          Nat.le_trans hfuelP2 hfuelP
                        have hpresP0 : FullExtScratchPres s sP2 :=
                          fullExtScratchPres_trans' hpresP hpresP2
                        c0_hsplit
                        · c0_hsteps; exact hJ75 () mP2
                            ⟨extP2, sP2, hinvP2, hpermP0, hcvP0, hfuelP0, hpresP0, hmP2⟩
                        · have hlt_fuel : sP2.core.fuel.toNat < fn := by
                            have hpr_nz : pr ≠ 2#64 := hc
                            have hpr_0 : pr = 0#64 := ‹pr = 0#64 ∨ pr = 2#64›.resolve_right hpr_nz
                            rw [hfnP]; exact (hpr0 hpr_0).2 hprop_lt
                          c0_hsteps; exact hJ_prop sP2.core.fuel.toNat () mP2 hlt_fuel
                            ⟨extP2, sP2, rfl, hinvP2, hpermP0, hcvP0, hfuelP0, hpresP0, hmP2⟩
                      · intro J_prop hJ_prop; c0_hsteps
                        exact hJ_prop sA.core.fuel.toNat () mA
                          ⟨extL, sA, rfl, hinvA, hpermL2, hcvL2, hfuelL2, hpresL20, hsA_hm⟩))
              (fun J62 hJ62 => by
                have hr_dim : r.toNat < 2 * dimacsBound := by
                  have := hlenL2.core_ok.cur_vars_le; unfold dimacsBound; omega
                c0_hsplit
                · c0_hsteps; exact hJ62
                    (((r <<< (1 : Nat)).setWidth 32 ||| 1#32), ()) _
                    ⟨Or.inr (lit_neg_shl64 hr_dim), hm61⟩
                · c0_hsteps; exact hJ62 (((r <<< (1 : Nat)).setWidth 32), ()) _
                    ⟨Or.inl (lit_pos_shl64 hr_dim), hm61⟩))
          (fun J61 hJ61 => by
            c0_hsplit
            · c0_hsplit
              · c0_hsteps; exact hJ61 _ _ hmL2
              · c0_hsteps; exact hJ61 _ _ hmL2
            · c0_hsteps; exact hJ61 _ _ hmL2)
      · intro J46 hJ46; c0_hsteps
        exact hJ46 s.core.cur_vars (0#64, ()) m
          ⟨ext, s, Nat.zero_le _, by simp, hinv, fullArenaPermEq_refl _, rfl, Nat.le_refl _,
            ⟨rfl, rfl⟩, hm⟩)

/-! ## 4. `full_walk` (`fullWalkM6Spec`) -/

theorem full_walk_wp (Γ : Env)
    (hWarmup : Γ.Has "full_warmup_m7" walkSpec)
    (hWalkM7 : Γ.Has "full_walk_m7" walkCoreSpec) :
    ∀ a m Q X, walkSpec a m Q X → Func.wp Γ full_walk_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  unfold walkSpec at hs
  obtain ⟨c, ext, s, F0, R, rfl, hcfg, hext, hlen, hsp, hm, hQ⟩ := M6HdrContract.elim hs
  unfold Func.wp full_walk_body
  refine wp_call_of_spec _ _ (hWarmup _ _ _ _ ?_)
  dsimp only [walkSpec]
  refine M6HdrContract.intro hcfg hext hlen hsp hm
    fun () ext1 s1 m1 hext1 _ _ ⟨hsp1, hperm1, hcv1, hcl1, hfu1, hprob1, hpres1⟩ hm1 => ?_
  have hinv1 : FullM6HdrInv c F0 ext1 s1 := ⟨hcfg, hext1, hsp1⟩
  refine walk_m6_frame_walk_m7 hWalkM7 rfl hinv1 hm1
    fun s2 m2 hinv2 hperm2 hcv2 hcl2 hfu2 hprob2 hpres2 hm2 => ?_
  exact hQ () ext1 s2 m2 hinv2.extOk trivial hinv2.sparse.lengths
    ⟨hinv2.sparse, fullArenaPermEq_trans hperm1 hperm2, hcv2.trans hcv1,
      hcl2.trans hcl1, Nat.le_trans hfu2 hfu1, fun h0 => hprob2.trans (hprob1 h0),
      fullExtScratchPres_trans' hpres1 hpres2⟩ hm2

/-! ## 5. `full_rephase` (`rephaseSpec`) -/

theorem full_rephase_wp (Γ : Env)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hWalk : Γ.Has "full_walk" walkSpec)
    (hNlog : Γ.Has "f64u_nlogpown" f64uPure2Spec)
    (hTo : Γ.Has "f64u_to_u64" f64uPure1Spec) :
    ∀ a m Q X, rephaseSpec a m Q X → Func.wp Γ full_rephase_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  unfold rephaseSpec at hs
  obtain ⟨c, ext, s, F0, R, rfl, hcfg, hext, _, hsp, hm, hQ0⟩ := M6HdrContract.elim hs
  have hinv : FullM6HdrInv c F0 ext s := ⟨hcfg, hext, hsp⟩
  let hQ : ∀ ext' s' m', FullM6HdrInv c F0 ext' s' → FullArenaPermEq s.core s'.core →
      (s.scratch.stable ≠ 0#64 → s'.core.cur_level = 0) →
      s'.core.cur_level ≤ s.core.cur_level → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      FullExtScratchPres s s' → (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m' :=
    fun ext' s' m' hinv' hap hst hcl hfu hext' hm' =>
      hQ0 () ext' s' m' hinv'.extOk trivial hinv'.sparse.lengths
        ⟨hinv'.sparse, hap, hst, hcl, hfu, hext'⟩ hm'
  have hlen := hsp.lengths; have hmax := c.hmaxv; unfold dimacsBound at hmax
  rw [fullM6HdrMem_iff] at hm
  unfold Func.wp full_rephase_body
  c0_hsteps_nogrp
  · let s0 : FullState := { s with scratch := { s.scratch with
      rephase_limit := s.scratch.mode_confl_lim } }
    have hinv0 : FullM6HdrInv c F0 ext s0 := .mk_inv hcfg hext
      (fullSparseInv_of_scratch hsp rfl ⟨hlen.core_ok, { hlen.scratch_ok with }⟩ ⟨rfl, rfl⟩)
    exact hQ ext s0 _ hinv0 (fullArenaPermEq_refl _) (fun hne => absurd hc hne)
      (Nat.le_refl _) (Nat.le_refl _) ⟨rfl, rfl⟩ ((fullM6HdrMem_iff ..).mpr ‹_›)
  · refine wp_join_group (ts := [])
      (fun _ m1 => ∃ s1, FullSparseInv c F0 s1 ∧ FullArenaPermEq s.core s1.core ∧
        s1.core.cur_level = 0 ∧ s1.core.fuel = s.core.fuel ∧ FullExtScratchPres s s1 ∧
        (FullMem c s1 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m1)
      (fun _ ⟨⟩ m1 ⟨s1, hsp1, hperm1, hcl1, hfuel1, hpres1, hm1⟩ => ?_)
      (fun J hJ => by
        c0_hsplit
        · c0_hsteps_nogrp
          refine walk_call_backtrack_m6 hBt rfl hinv (Nat.zero_le _)
            ((fullM6HdrMem_iff ..).mpr hm)
            fun sB mB hinvB hpermB _ hclB _ hfuelB _ hpresB hmB => ?_
          rw [fullM6HdrMem_iff] at hmB
          c0_hsteps; exact hJ () mB ⟨sB, hinvB.sparse, hpermB, by simpa using hclB, hfuelB,
            hpresB, hmB⟩
        · have hcl0 : s.core.cur_level = 0 := by
            have := hlen.core_ok.trail_end_le; have := hlen.core_ok.cur_vars_le
            obtain ⟨_, hw⟩ := hsp.1.witness; have := hw.cur_level_le
            have h0 : (0 : BitVec 64).toNat = 0 := rfl
            rw [Nat.mod_eq_of_lt (by omega : s.core.cur_level < 2 ^ 64)] at hc; omega
          c0_hsteps; exact hJ () m ⟨s, hsp, fullArenaPermEq_refl _, hcl0, rfl, ⟨rfl, rfl⟩, hm⟩)
    have hlen1 := hsp1.lengths
    c0_hsteps_nogrp
    let s2 : FullState := { s1 with scratch := { s1.scratch with
      rephased := s1.scratch.rephased + 1#64 } }
    have hlen2 : s2.LengthsOk c := ⟨hlen1.core_ok, { hlen1.scratch_ok with }⟩
    have hsp2 : FullSparseInv c F0 s2 := fullSparseInv_of_scratch hsp1 rfl hlen2 ⟨rfl, rfl⟩
    have hcv2_le : s2.core.cur_vars ≤ c.max_vars := hlen2.core_ok.cur_vars_le
    refine wp_join_group (ts := [])
      (fun _ m3 => ∃ ext3 s3, FullM6HdrInv c F0 ext3 s3 ∧ FullArenaPermEq s.core s3.core ∧
        s3.core.cur_vars = s2.core.cur_vars ∧ s3.core.cur_level = 0 ∧
        s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧ FullExtScratchPres s s3 ∧
        (FullMem c s3 ⋆ (array64 (c.hdr - 2304) ext3 ⋆ R)) m3)
      (fun _ ⟨⟩ m3 ⟨ext3, s3, hinv3, hperm3, hcv3, hcl3, hfuel3, hpres3, hm3⟩ => ?_)
      (fun J_ph hJ_ph => ?_)
    · c0_hsteps_nogrp
      refine wp_loop_group (ts := [i64])
        (fun nk ⟨k, ⟨⟩⟩ mK => ∃ sK, k.toNat ≤ s2.core.cur_vars ∧
          nk = s2.core.cur_vars - k.toNat ∧ sK.core = s3.core ∧ sK.LengthsOk c ∧
          FullExtScratchPres s3 sK ∧ (FullMem c sK ⋆ (array64 (c.hdr - 2304) ext3 ⋆ R)) mK) ?_ ?_
      · intro JK nk ⟨k, ⟨⟩⟩ mK hJK ⟨sK, hk_le, hnk, hcoreK, hlenK, hpresK, hmK⟩
        c0_hsplit
        · have hk_lt : k.toNat < s2.core.cur_vars := by
            rw [Nat.mod_eq_of_lt (by omega : s2.core.cur_vars < 2 ^ 64)] at hc; exact hc
          have hk_ph : k.toNat < sK.scratch.phases.length := by
            rw [hlenK.scratch_ok.phases_len]; omega
          have hk_pt : k.toNat < sK.scratch.phases_target.length := by
            rw [hlenK.scratch_ok.phases_target_len]; omega
          have hk1 : (k + 1).toNat = k.toNat + 1 := bv64_add1_lt hk_lt (by omega)
          c0_hsteps
          let sK' : FullState := { sK with scratch := { sK.scratch with
            phases_target := sK.scratch.phases_target.set k.toNat
              (sK.scratch.phases[k.toNat]'hk_ph) } }
          have hlenK' : sK'.LengthsOk c := ⟨hlenK.core_ok,
            { hlenK.scratch_ok with
              phases_target_len := by simp [sK', hlenK.scratch_ok.phases_target_len] }⟩
          exact hJK (s2.core.cur_vars - (k.toNat + 1)) _ _ (by omega)
            ⟨sK', by rw [hk1]; omega, by rw [hk1], hcoreK, hlenK', hpresK, ‹_›⟩
        · c0_hsteps_nogrp
          refine wp_call_of_spec _ _ (hNlog _ _ _ _ fun _ => ?_)
          c0_hsteps_nogrp
          refine wp_call_of_spec _ _ (hTo _ _ _ _ fun sc_v => ?_)
          c0_hsteps
          let sF : FullState := { sK with scratch := { sK.scratch with
            target_assigned := 0#64, rephase_limit := sK.scratch.conflicts + 1000#64 * sc_v } }
          have hlenF : sF.LengthsOk c := ⟨hlenK.core_ok, { hlenK.scratch_ok with }⟩
          have hinvF : FullM6HdrInv c F0 ext3 sF :=
            .mk_inv hcfg hinv3.extOk (fullSparseInv_of_scratch hinv3.sparse hcoreK hlenF hpresK)
          exact hQ ext3 sF _ hinvF (by rw [hcoreK]; exact hperm3)
            (fun _ => by rw [hcoreK]; exact hcl3)
            (by rw [hcoreK, hcl3]; exact Nat.zero_le _) (by rw [hcoreK]; exact hfuel3)
            (fullExtScratchPres_trans' hpres3 hpresK) ((fullM6HdrMem_iff ..).mpr ‹_›)
      · intro JK hJK; c0_hsteps
        exact hJK s2.core.cur_vars (0#64, ()) m3
          ⟨s3, Nat.zero_le _, by simp, rfl, hinv3.sparse.lengths, ⟨rfl, rfl⟩, hm3⟩
    · c0_hsteps_nogrp
      refine wp_join_group (ts := [])
        (fun _ mA => (FullMem c s2 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) mA)
        (fun _ ⟨⟩ mA hmA => by
          refine wp_loop_group (ts := [i64])
            (fun nv ⟨v, ⟨⟩⟩ mV => ∃ sV, v.toNat ≤ s2.core.cur_vars ∧
              nv = s2.core.cur_vars - v.toNat ∧ sV.core = s2.core ∧ sV.LengthsOk c ∧
              FullExtScratchPres s2 sV ∧
              (FullMem c sV ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) mV) ?_ ?_
          · intro JV nv ⟨v, ⟨⟩⟩ mV hJV ⟨sV, hv_le, hnv, hcoreV, hlenV, hpresV, hmV⟩
            c0_hsplit
            · have hv_lt : v.toNat < s2.core.cur_vars := by
                rw [Nat.mod_eq_of_lt (by omega : s2.core.cur_vars < 2 ^ 64)] at hc; exact hc
              have hv_pb : v.toNat < sV.scratch.phases_best.length := by
                rw [hlenV.scratch_ok.phases_best_len]; omega
              have hv_ph : v.toNat < sV.scratch.phases.length := by
                rw [hlenV.scratch_ok.phases_len]; omega
              have hv1 : (v + 1).toNat = v.toNat + 1 := bv64_add1_lt hv_lt (by omega)
              c0_hsteps_nogrp
              refine wp_join_group (ts := [])
                (fun _ mW => ∃ sW, sW.core = s2.core ∧ sW.LengthsOk c ∧
                  FullExtScratchPres s2 sW ∧
                  (FullMem c sW ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) mW)
                (fun _ ⟨⟩ mW ⟨sW, hcoreW, hlenW, hpresW, hmW⟩ => by
                  c0_hsteps; exact hJV (s2.core.cur_vars - (v.toNat + 1)) _ mW (by omega)
                    ⟨sW, by rw [hv1]; omega, by rw [hv1], hcoreW, hlenW, hpresW, hmW⟩)
                (fun JW hJW => by
                  c0_hsplit
                  · c0_hsteps
                    let sW : FullState := { sV with scratch := { sV.scratch with
                      phases := sV.scratch.phases.set v.toNat
                        (sV.scratch.phases_best[v.toNat]'hv_pb) } }
                    have hlenW : sW.LengthsOk c := ⟨hlenV.core_ok,
                      { hlenV.scratch_ok with
                        phases_len := by simp [sW, hlenV.scratch_ok.phases_len] }⟩
                    exact hJW () _ ⟨sW, hcoreV, hlenW, hpresV, ‹_›⟩
                  · c0_hsteps; exact hJW () mV ⟨sV, hcoreV, hlenV, hpresV, hmV⟩)
            · c0_hsteps
              let sF : FullState :=
                { sV with scratch := { sV.scratch with best_assigned := 0#64 } }
              have hinvF : FullM6HdrInv c F0 ext sF := .mk_inv hcfg hext
                (fullSparseInv_of_scratch hsp2 hcoreV ⟨hlenV.core_ok, { hlenV.scratch_ok with }⟩
                  hpresV)
              exact hJ_ph () _ ⟨ext, sF, hinvF, by rw [hcoreV]; exact hperm1, by rw [hcoreV],
                by rw [hcoreV]; exact hcl1, by rw [hcoreV, hfuel1]; exact Nat.le_refl _,
                fullExtScratchPres_trans' hpres1 hpresV, ‹_›⟩
          · intro JV hJV; c0_hsteps
            exact hJV s2.core.cur_vars (0#64, ()) mA ⟨s2, Nat.zero_le _, by simp, rfl, hlen2,
              ⟨rfl, rfl⟩, hmA⟩)
        (fun J03 hJ03 => by
          c0_hsplit; · c0_hsteps; exact hJ03 () _ ‹_›
          c0_hsplit; · c0_hsteps; exact hJ03 () _ ‹_›
          let RephPost (mW : Mem 64) : Prop :=
            ∃ extW sW, FullM6HdrInv c F0 extW sW ∧ FullArenaPermEq s.core sW.core ∧
              sW.core.cur_vars = s2.core.cur_vars ∧ sW.core.cur_level = 0 ∧
              sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧ FullExtScratchPres s sW ∧
              (FullMem c sW ⋆ (array64 (c.hdr - 2304) extW ⋆ R)) mW
          refine wp_join_group (ts := []) (fun _ mW => RephPost mW)
            (fun _ ⟨⟩ mW hW => by c0_hsteps; exact hJ_ph () mW hW)
            (fun J14 hJ14 => by
              refine wp_join_group (ts := [])
                (fun _ mW => (FullMem c s2 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) mW)
                (fun _ ⟨⟩ mW hmW => by
                  c0_hsteps_nogrp
                  refine wp_call_of_spec _ _ (hWalk _ _ _ _ ?_)
                  dsimp only [walkSpec]
                  refine M6HdrContract.intro hcfg hext hlen2 hsp2 ((fullM6HdrMem_iff ..).mpr hmW)
                    fun () extW sW mW' hextW _ _ ⟨hspW, hpermW, hcvW, hclW, hfuelW, _, hpresW⟩
                      hmW' => ?_
                  have hinvW : FullM6HdrInv c F0 extW sW := ⟨hcfg, hextW, hspW⟩
                  rw [fullM6HdrMem_iff] at hmW'; c0_hsteps
                  exact hJ14 () mW' ⟨extW, sW, hinvW, fullArenaPermEq_trans hperm1 hpermW, hcvW,
                    by rw [hclW]; exact hcl1, by rw [← hfuel1]; exact hfuelW,
                    fullExtScratchPres_trans' hpres1 hpresW, hmW'⟩)
                (fun Jwalk hJwalk => by
                  c0_hsplit; · c0_hsteps; exact hJwalk () _ ‹_›
                  c0_hsplit; · c0_hsteps; exact hJwalk () _ ‹_›
                  refine wp_join_group (ts := []) (fun _ mW => RephPost mW)
                    (fun _ ⟨⟩ mW hW => by c0_hsteps; exact hJ14 () mW hW)
                    (fun J2e hJ2e => by
                      c0_hsplit
                      · refine wp_loop_group (ts := [i64])
                          (fun nv ⟨v, ⟨⟩⟩ mV => ∃ sV, v.toNat ≤ s2.core.cur_vars ∧
                            nv = s2.core.cur_vars - v.toNat ∧ sV.core = s2.core ∧ sV.LengthsOk c ∧
                            FullExtScratchPres s2 sV ∧
                            (FullMem c sV ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) mV) ?_ ?_
                        · intro JV nv ⟨v, ⟨⟩⟩ mV hJV ⟨sV, hv_le, hnv, hcoreV, hlenV, hpresV, hmV⟩
                          c0_hsplit
                          · have hv_lt : v.toNat < s2.core.cur_vars := by
                              rw [Nat.mod_eq_of_lt (by omega : s2.core.cur_vars < 2 ^ 64)] at hc
                              exact hc
                            have hv_ph : v.toNat < sV.scratch.phases.length := by
                              rw [hlenV.scratch_ok.phases_len]; omega
                            have hv1 : (v + 1).toNat = v.toNat + 1 := bv64_add1_lt hv_lt (by omega)
                            c0_hsteps
                            let sW : FullState := { sV with scratch := { sV.scratch with
                              phases := sV.scratch.phases.set v.toNat 255#8 } }
                            have hlenW : sW.LengthsOk c := ⟨hlenV.core_ok,
                              { hlenV.scratch_ok with
                                phases_len := by simp [sW, hlenV.scratch_ok.phases_len] }⟩
                            exact hJV (s2.core.cur_vars - (v.toNat + 1)) _ _ (by omega)
                              ⟨sW, by rw [hv1]; omega, by rw [hv1], hcoreV, hlenW, hpresV, ‹_›⟩
                          · c0_hsteps
                            exact hJ2e () mV ⟨ext, sV, .mk_inv hcfg hext
                              (fullSparseInv_of_scratch hsp2 hcoreV hlenV hpresV),
                              by rw [hcoreV]; exact hperm1, by rw [hcoreV],
                              by rw [hcoreV]; exact hcl1,
                              by rw [hcoreV, hfuel1]; exact Nat.le_refl _,
                              fullExtScratchPres_trans' hpres1 hpresV, hmV⟩
                        · intro JV hJV; c0_hsteps
                          exact hJV s2.core.cur_vars (0#64, ()) _ ⟨s2, Nat.zero_le _, by simp, rfl,
                            hlen2, ⟨rfl, rfl⟩, ‹_›⟩
                      · refine wp_loop_group (ts := [i64])
                          (fun nv ⟨v, ⟨⟩⟩ mV => ∃ sV, v.toNat ≤ s2.core.cur_vars ∧
                            nv = s2.core.cur_vars - v.toNat ∧ sV.core = s2.core ∧ sV.LengthsOk c ∧
                            FullExtScratchPres s2 sV ∧
                            (FullMem c sV ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) mV) ?_ ?_
                        · intro JV nv ⟨v, ⟨⟩⟩ mV hJV ⟨sV, hv_le, hnv, hcoreV, hlenV, hpresV, hmV⟩
                          c0_hsplit
                          · have hv_lt : v.toNat < s2.core.cur_vars := by
                              rw [Nat.mod_eq_of_lt (by omega : s2.core.cur_vars < 2 ^ 64)] at hc
                              exact hc
                            have hv_ph : v.toNat < sV.scratch.phases.length := by
                              rw [hlenV.scratch_ok.phases_len]; omega
                            have hv1 : (v + 1).toNat = v.toNat + 1 := bv64_add1_lt hv_lt (by omega)
                            c0_hsteps
                            let sW : FullState := { sV with scratch := { sV.scratch with
                              phases := sV.scratch.phases.set v.toNat 1#8 } }
                            have hlenW : sW.LengthsOk c := ⟨hlenV.core_ok,
                              { hlenV.scratch_ok with
                                phases_len := by simp [sW, hlenV.scratch_ok.phases_len] }⟩
                            exact hJV (s2.core.cur_vars - (v.toNat + 1)) _ _ (by omega)
                              ⟨sW, by rw [hv1]; omega, by rw [hv1], hcoreV, hlenW, hpresV, ‹_›⟩
                          · c0_hsteps
                            exact hJ2e () mV ⟨ext, sV, .mk_inv hcfg hext
                              (fullSparseInv_of_scratch hsp2 hcoreV hlenV hpresV),
                              by rw [hcoreV]; exact hperm1, by rw [hcoreV],
                              by rw [hcoreV]; exact hcl1,
                              by rw [hcoreV, hfuel1]; exact Nat.le_refl _,
                              fullExtScratchPres_trans' hpres1 hpresV, hmV⟩
                        · intro JV hJV; c0_hsteps
                          exact hJV s2.core.cur_vars (0#64, ()) _ ⟨s2, Nat.zero_le _, by simp, rfl,
                            hlen2, ⟨rfl, rfl⟩, ‹_›⟩))))

end LeanQbe.T.Examples.Kissat.Proof.Walk
