/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3Walk
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3Spec
public import LeanQbe.T.Examples.Kissat.FullM7WalkProof0
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullM7WalkProof

/-!
# Kissat Fidelity Step 13 Shard S3-A Proofs — Part 2 (`FullFidelityStep13S3WalkProof2`)

Callee-parametric (`Γ : Env`, `XPost := False`, `0` SAT model proofs) `Func.wp` proofs for:
1. `full_walk_pick_m7_step13_wp` (`step13WalkPickSpec`)
2. `full_walk_m7_step13_wp` (`step13WalkM7Spec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S3

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullM7Walk
open Kraken.Bedrock2.Test
open scoped FullArenaTactics
open scoped S3WalkMemTactics

/-! ## 1. Shared Helpers & Call Bridges -/

section Helpers

private theorem w2_zext32 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat :=
  zext_toNat x (by decide)

private theorem w2_shl1_32 (x : BitVec 32) : (x.setWidth 64 <<< (1 : Nat)).toNat = 2 * x.toNat := by
  have hx := x.isLt
  rw [BitVec.toNat_shiftLeft, w2_zext32, Nat.shiftLeft_eq, Nat.pow_one,
    Nat.mod_eq_of_lt (by omega : x.toNat * 2 < 2 ^ 64)]
  omega

private theorem w2_shl1 {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show 2 ^ 1 = 2 from rfl,
    show x.toNat * 2 = 2 * x.toNat by omega, Nat.mod_eq_of_lt hx]

private theorem w2_add1 {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by bv_omega

private theorem w2_add1_32 {k s : BitVec 32} (h : k.toNat < s.toNat) :
    (k + 1#32).toNat = k.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by have := s.isLt; omega)]

private theorem w2_xor1_lt {x : BitVec 32} {n : Nat} (hx : x.toNat < 2 * n) :
    (x ^^^ 1#32).toNat < 2 * n := by
  have h1 : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := rfl
  rw [h1]; exact litNeg_lt_two_mul hx

private theorem w2_len_sb_u64 {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 64}
    (h : s.LengthsOk c) :
    ({ s with scratch :=
      { s.scratch with scratch_buf := setU64In32 s.scratch.scratch_buf i v } }).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with
    scratch_buf_len := by rw [setU64In32_length, h.scratch_ok.scratch_buf_len] }⟩

private theorem w2_len_wk1_wk2_u64 {c : FullCfg} {s : FullState} {i : Nat}
    {v1 : BitVec 32} {v2 : BitVec 64} (h : s.LengthsOk c) :
    ({ s with scratch := { s.scratch with
      work_stk1 := s.scratch.work_stk1.set i v1
      work_stk2 := setU64In32 s.scratch.work_stk2 i v2 } }).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with
    work_stk1_len := by rw [List.length_set, h.scratch_ok.work_stk1_len]
    work_stk2_len := by rw [setU64In32_length, h.scratch_ok.work_stk2_len] }⟩

private theorem w2_walkTblExpsOk_getElem {s : FullState}
    (hok : WalkTblExpsOk s) (h1 : 2161 < s.scratch.scratch_buf.length) :
    (u64Of32Pair (s.scratch.scratch_buf[2160]'(by omega))
      (s.scratch.scratch_buf[2161]'h1)).toNat ≤ 1080 := by
  unfold WalkTblExpsOk at hok
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem h1,
    Option.getD_some, Option.getD_some] at hok
  exact hok

private theorem w2_walkTblExpsOk_wk1_wk2 {s : FullState} {i : Nat}
    {v1 : BitVec 32} {v2 : BitVec 64} (hok : WalkTblExpsOk s) :
    WalkTblExpsOk { s with scratch := { s.scratch with
      work_stk1 := s.scratch.work_stk1.set i v1
      work_stk2 := setU64In32 s.scratch.work_stk2 i v2 } } := hok

private theorem w2_break_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i32, i64]} {k : Tup Val [i32] → Expr Val Cont rs}
    (hBrk : ∀ a m Q X, step13WalkBreakSpec a m Q X →
      Γ "full_walk_break_m7" [i64, i32, i64] [i32] a m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hHdr : args.1.val = c.hdr) (hSafe : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r m', (FullMem c s ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_walk_break_m7" args k) m := by
  refine wp_call_of_spec args k (hBrk _ m _ X ⟨c, s, R, hHdr, hSafe, hm, ?_⟩)
  intro ⟨r, ⟨⟩⟩ _ m' _ _ rfl hm'
  exact hk r m' hm'

private theorem w2_cbInv_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i64, i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hCb : ∀ a m Q X, step13WalkCbInvSpec a m Q X →
      Γ "full_walk_cb_inv_m7" [i64, i64, i64] [i64] a m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hHdr : args.1.val = c.hdr) (hSafe : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      (r ≠ 0#64 → WalkTblExpsOk s') → (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_walk_cb_inv_m7" args k) m := by
  refine wp_call_of_spec args k (hCb _ m _ X ⟨c, s, R, hHdr, hSafe, hm, ?_⟩)
  intro ⟨r, ⟨⟩⟩ s' m' hcore hs' ⟨hext, hexps⟩ hm'
  exact hk r s' m' hcore hs' hext hexps hm'

private theorem w2_buildOcc_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hBo : ∀ a m Q X, step13WalkBuildOccSpec a m Q X →
      Γ "full_walk_build_occ_m7" [i64, i64] [i64] a m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hHdr : args.1.val = c.hdr) (hSafe : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      WalkScrPrefixPres s s' → r.toNat ≤ args.2.1.val.toNat → (FullMem c s' ⋆ R) m' →
      wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_walk_build_occ_m7" args k) m := by
  refine wp_call_of_spec args k (hBo _ m _ X ⟨c, s, R, hHdr, hSafe, hm, ?_⟩)
  intro ⟨r, ⟨⟩⟩ s' m' hcore hs' ⟨hext, hpre, hle⟩ hm'
  exact hk r s' m' hcore hs' hext hpre hle hm'

private theorem w2_effort_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hEff : ∀ a m Q X, step13WalkEffortSpec a m Q X →
      Γ "full_walk_effort_m7" [i64, i64] [i64] a m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hHdr : args.1.val = c.hdr) (hSafe : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r m', (FullMem c s ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_walk_effort_m7" args k) m := by
  refine wp_call_of_spec args k (hEff _ m _ X ⟨c, s, R, hHdr, hSafe, hm, ?_⟩)
  intro ⟨r, ⟨⟩⟩ _ m' _ _ rfl hm'
  exact hk r m' hm'

private theorem w2_pick_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i32, i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hPick : ∀ a m Q X, step13WalkPickSpec a m Q X →
      Γ "full_walk_pick_m7" [i64, i32, i64] [i64] a m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hHdr : args.1.val = c.hdr) (hexps : WalkTblExpsOk s)
    (hSafe : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      WalkTblExpsOk s' → (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_walk_pick_m7" args k) m := by
  refine wp_call_of_spec args k (hPick _ m _ X ⟨c, s, R, ⟨hHdr, hexps⟩, hSafe, hm, ?_⟩)
  intro ⟨r, ⟨⟩⟩ s' m' hcore hs' ⟨hext, hexps'⟩ hm'
  exact hk r s' m' hcore hs' hext hexps' hm'

private theorem w2_flip_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i32, i64, i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hFlip : ∀ a m Q X, step13WalkFlipSpec a m Q X →
      Γ "full_walk_flip_m7" [i64, i32, i64, i64] [i64] a m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hHdr : args.1.val = c.hdr) (hSafe : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      WalkScrPrefixPres s s' → (r &&& 0xFFFFFFFF#64).toNat ≤ args.2.2.1.val.toNat →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_walk_flip_m7" args k) m := by
  refine wp_call_of_spec args k (hFlip _ m _ X ⟨c, s, R, hHdr, hSafe, hm, ?_⟩)
  intro ⟨r, ⟨⟩⟩ s' m' hcore hs' ⟨hext, hpre, hle⟩ hm'
  exact hk r s' m' hcore hs' hext hpre hle hm'

private theorem w2_arenaPermEq_refl (s : FullCoreState) : FullArenaPermEq s s :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩

private theorem w2_arenaPermEq_trans {s1 s2 s3 : FullCoreState}
    (h1 : FullArenaPermEq s1 s2) (h2 : FullArenaPermEq s2 s3) : FullArenaPermEq s1 s3 := by
  refine ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun r hr => ?_⟩
  have hr1 : r ∈ fullArenaClauseRefsCore s2 := by rw [h1.2.1]; exact hr
  obtain ⟨hs1, hg1, hp1⟩ := h1.2.2 r hr
  obtain ⟨hs2, hg2, hp2⟩ := h2.2.2 r hr1
  exact ⟨hs2.trans hs1, hg2.trans hg1, hp2.trans hp1⟩

private theorem w2_sparse_with_fuel_and_scratch {c : FullCfg} {F0 : CNF Nat}
    {s s' : FullState} {fuel' : BitVec 64}
    (hsp : FullSparseInv c F0 s) (hcore : s'.core = { s.core with fuel := fuel' })
    (hlen : s'.LengthsOk c) (hpres : FullExtScratchPres s s') :
    FullSparseInv c F0 s' :=
  hsp.with_fuel_scratch hlen hcore hpres

private theorem w2_arenaPermEq_with_fuel {s1 s2 : FullCoreState} {fuel' : BitVec 64}
    (h : FullArenaPermEq s1 s2) : FullArenaPermEq s1 { s2 with fuel := fuel' } := h

private theorem w2_core_lengths_with_fuel {c : FullCfg} {s : FullCoreState} {f : BitVec 64}
    (h : s.LengthsOk c) : ({ s with fuel := f } : FullCoreState).LengthsOk c :=
  ⟨h.vals_len, h.lit_mark_len, h.mrk_len, h.flags_len, h.lvl_len, h.rsns_len, h.trl_len,
   h.trail_pos_len, h.tmp_len_arr, h.min_clr_len_arr, h.frame_trail_len, h.frame_dec_len,
   h.wvec_len, h.repr_len, h.min_stk_len, h.arena_len_arr, h.wstk_len_arr, h.cur_vars_ge,
   h.cur_vars_le, h.arena_len_le, h.wlen_le, h.trail_end_le, h.propagated_le, h.tmp_len_le,
   h.min_clr_len_le⟩

private theorem w2_rshift32_lt {x : BitVec 64} : (x >>> 32#64).toNat < 2 ^ 32 := by
  change (x >>> (32 : Nat)).toNat < 2 ^ 32
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt; omega

private theorem w2_shr2_add1_le {cv mv : Nat} (hcv_pos : 0 < cv) (hcv : cv ≤ mv)
    (hmv : mv < 2 * 2 ^ 28) :
    (BitVec.ofNat 64 cv >>> BitVec.signExtend 64 2#32 + 1#64).toNat ≤ 2 * mv := by
  have hsh : (BitVec.ofNat 64 cv >>> BitVec.signExtend 64 2#32).toNat = cv / 4 := by
    change (BitVec.ofNat 64 cv >>> (2 : Nat)).toNat = cv / 4
    rw [BitVec.toNat_ushiftRight, bv64_ofNat_toNat (by omega), Nat.shiftRight_eq_div_pow]
  rw [BitVec.toNat_add, hsh, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega)]
  omega

private theorem w2_arena_lit_ar {ar : List (BitVec 32)} {e0 k : BitVec 32} {alen acap : Nat}
    (hal : ar.length = acap) (hale : alen ≤ acap) (haca : acap < 2 * 2 ^ 28)
    (he0k : e0.toNat + 3 + k.toNat < alen) :
    (e0.setWidth 64 + 3#64 + k.setWidth 64).toNat < ar.length := by
  have := e0.isLt; have := k.isLt
  rw [BitVec.toNat_add, BitVec.toNat_add, w2_zext32, w2_zext32,
    show (3#64 : BitVec 64).toNat = 3 from rfl,
    Nat.mod_eq_of_lt (by omega : e0.toNat + 3 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : e0.toNat + 3 + k.toNat < 2 ^ 64), hal]; omega

private theorem w2_arena_lit_def {ar : List (BitVec 32)} {e0 k : BitVec 32}
    (h1 : (e0.toNat + BitVec.toNat (3 : BitVec 64) + k.toNat) % 2 ^ 64 < ar.length)
    (h2 : (e0.setWidth 64 + 3#64 + k.setWidth 64).toNat < ar.length)
    (he : e0.toNat + 3 < 2 ^ 64) :
    ar[(e0.toNat + BitVec.toNat (3 : BitVec 64) + k.toNat) % 2 ^ 64]'h1 =
      ar[(e0.setWidth 64 + 3#64 + k.setWidth 64).toNat]'h2 := by
  congr 1
  rw [BitVec.toNat_add, BitVec.toNat_add, w2_zext32, w2_zext32,
    show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
    show (3#64 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt he]

private theorem w2_lit_lt_2cv {x : BitVec 32} {cv mv : Nat} (hcv : cv ≤ mv) (hmv : mv < 2 * 2 ^ 28)
    (hc : x.toNat < 2 * (cv % 2 ^ 64) % 2 ^ 64) : x.toNat < 2 * cv := by
  rw [Nat.mod_eq_of_lt (by omega : cv < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 2 * cv < 2 ^ 64)] at hc; exact hc

end Helpers

/-! ## 2. `full_walk_pick_m7_step13_wp` (`step13WalkPickSpec`) -/

/-- Step-13 `full_walk_pick_m7` satisfies `step13WalkPickSpec`: requires & preserves
`WalkTblExpsOk` (`tbl[1080] ≤ 1080`), uses `f64u_*` and `u64 *wk2` on `work_stk2`. -/
theorem full_walk_pick_m7_step13_wp (Γ : Env)
    (hBrk : ∀ a m Q X, step13WalkBreakSpec a m Q X →
      Γ "full_walk_break_m7" [i64, i32, i64] [i32] a m Q X)
    (hAdd : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_add" [i64, i64] [i64] a m Q X)
    (hMul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X)
    (hFrom : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_from_u64" [i64] [i64] a m Q X) :
    ∀ a m Q X, step13WalkPickSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_walk_pick_m7_body a m Q X := by
  rintro ⟨h, cl, ncl, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hexps⟩, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  dsimp only [Func.wp, FullFidelityStep13S3.full_walk_pick_m7_body]
  have hmax := c.hmaxv; have haca := c.harena; have hscr := c.hscr
  unfold dimacsBound at hmax haca hscr
  have hcv_le := hlen.core_ok.cur_vars_le; have harl := hlen.core_ok.arena_len_arr
  have hale := hlen.core_ok.arena_len_le; have hvl := hlen.core_ok.vals_len
  have hsbl := hlen.scratch_ok.scratch_buf_len; have htrl := hlen.scratch_ok.tarjan_reach_len
  have hws1 := hlen.scratch_ok.work_stk1_len; have hws2 := hlen.scratch_ok.work_stk2_len
  have hretFF : Q (0xffffffff#64, ()) m :=
    hQ (0xffffffff#64, ()) s m rfl hlen ⟨⟨rfl, rfl⟩, hexps⟩ hm
  c0_hsplit; · c0_hsteps; exact hretFF
  have hcv_pos : 0 < s.core.cur_vars := Nat.pos_of_ne_zero fun h0 => hc (by rw [h0]; rfl)
  c0_hsplit; · c0_hsteps; exact hretFF
  c0_hsplit; · c0_hsteps; exact hretFF
  have hncl_pos : 0 < ncl.toNat := Nat.pos_of_ne_zero fun h0 =>
    hc (BitVec.eq_of_toNat_eq (by simpa using h0))
  c0_hsplit; · c0_hsteps; exact hretFF
  have hcl_lt : cl.toNat < ncl.toNat := Nat.lt_of_not_le hc
  c0_hsplit; · c0_hsteps; exact hretFF
  have hncl_le : ncl.toNat ≤ c.scratch_cap := by
    rw [Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64)] at hc; omega
  c0_hsplit; · c0_hsteps; exact hretFF
  have hcap_ok : 2200 + 5 * ncl.toNat ≤ c.scratch_cap := by
    rw [show (2200 : BitVec 64).toNat = 2200 from rfl, show (5 : BitVec 64).toNat = 5 from rfl,
      Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 2200 + 5 * ncl.toNat < 2 ^ 64)] at hc; omega
  have h1080_sb : 2 * 1080 + 1 < s.scratch.scratch_buf.length := by rw [hsbl]; omega
  have hi0_eq : (2200#64 + cl.setWidth 64 <<< 1).toNat = 2200 + 2 * cl.toNat := by
    rw [BitVec.toNat_add, w2_shl1_32, show (2200#64 : BitVec 64).toNat = 2200 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hi1_eq : (2200#64 + cl.setWidth 64 <<< 1 + 1#64).toNat = 2200 + 2 * cl.toNat + 1 := by
    rw [BitVec.toNat_add, hi0_eq, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hi0_sb : (2200#64 + cl.setWidth 64 <<< 1).toNat < s.scratch.scratch_buf.length := by
    rw [hi0_eq, hsbl]; omega
  have hi1_sb : (2200#64 + cl.setWidth 64 <<< 1 + 1#64).toNat < s.scratch.scratch_buf.length := by
    rw [hi1_eq, hsbl]; omega
  have h1080_m : (8640#64 : BitVec 64).toNat % 8 = 0 := by decide
  have h1081_m : (8648#64 : BitVec 64).toNat % 8 = 0 := by decide
  have h1080_sb' : 2 * ((8640#64 : BitVec 64).toNat / 8) + 1 < s.scratch.scratch_buf.length := by
    rw [hsbl, show (8640#64 : BitVec 64).toNat = 8640 from rfl]; omega
  have h1081_sb' : 2 * ((8648#64 : BitVec 64).toNat / 8) + 1 < s.scratch.scratch_buf.length := by
    rw [hsbl, show (8648#64 : BitVec 64).toNat = 8648 from rfl]; omega
  have h1082_sb' : 2 * ((8656#64 : BitVec 64).toNat / 8) + 1 < s.scratch.scratch_buf.length := by
    rw [hsbl, show (8656#64 : BitVec 64).toNat = 8656 from rfl]; omega
  let exps := u64Of32Pair (s.scratch.scratch_buf[2160]'(by omega))
    (s.scratch.scratch_buf[2161]'h1080_sb)
  have hexps_le : exps.toNat ≤ 1080 := w2_walkTblExpsOk_getElem hexps h1080_sb
  let e0 := s.scratch.scratch_buf[(2200#64 + cl.setWidth 64 <<< 1).toNat]'hi0_sb
  let e1 := s.scratch.scratch_buf[(2200#64 + cl.setWidth 64 <<< 1 + 1#64).toNat]'hi1_sb
  have he0_def : s.scratch.scratch_buf[(BitVec.toNat (2200 : BitVec 64) + 2 * cl.toNat) %
      2 ^ 64]'(by rw [show BitVec.toNat (2200 : BitVec 64) = 2200 from rfl,
        Nat.mod_eq_of_lt (by omega : 2200 + 2 * cl.toNat < 2 ^ 64), hsbl]; omega) = e0 := by
    dsimp only [e0]; congr 1
    rw [hi0_eq, show BitVec.toNat (2200 : BitVec 64) = 2200 from rfl, Nat.mod_eq_of_lt (by omega)]
  have he1_def : s.scratch.scratch_buf[(BitVec.toNat (2200 : BitVec 64) + 2 * cl.toNat +
      BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
      rw [show BitVec.toNat (2200 : BitVec 64) = 2200 from rfl,
        show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
        Nat.mod_eq_of_lt (by omega : 2200 + 2 * cl.toNat + 1 < 2 ^ 64), hsbl]; omega) = e1 := by
    dsimp only [e1]; congr 1
    rw [hi1_eq, show BitVec.toNat (2200 : BitVec 64) = 2200 from rfl,
      show BitVec.toNat (1 : BitVec 64) = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  c0_hsteps_nogrp; c0_hsplit
  · -- Binary clause branch
    clear hc; let a0 := e0 &&& 0x7FFFFFFF#32
    refine wp_join_group (ts := [Ty.bool])
      (fun (fa, ()) m1 => m = m1 ∧ (fa = true → a0.toNat < 2 * s.core.cur_vars))
      (fun _ ⟨fa, ⟨⟩⟩ m1 ⟨hm1, hfa_lt⟩ => ?_)
      (fun J0 hJ0 => by
        c0_hsplit; rotate_left; · c0_hsteps; exact hJ0 (false, ()) m ⟨rfl, Bool.noConfusion⟩
        have ha0_lt : a0.toNat < 2 * s.core.cur_vars := by
          have him : (2147483647 : BitVec 32) = 0x7FFFFFFF#32 := rfl
          dsimp only [a0]; exact w2_lit_lt_2cv hcv_le hmax (by simpa only [he0_def, him] using hc)
        have ha0_v : (a0.setWidth 64).toNat < s.core.vals.length := by rw [w2_zext32, hvl]; omega
        c0_hsteps_nogrp; c0_hsplit
        · c0_hsteps; exact hJ0 (true, ()) m ⟨rfl, fun _ => ha0_lt⟩
        · c0_hsteps; exact hJ0 (false, ()) m ⟨rfl, Bool.noConfusion⟩)
    rcases hm1 with rfl
    refine wp_join_group (ts := [Ty.bool])
      (fun (fb, ()) m2 => m = m2 ∧ (fb = true → e1.toNat < 2 * s.core.cur_vars))
      (fun _ ⟨fb, ⟨⟩⟩ m2 ⟨hm2, hfb_lt⟩ => ?_)
      (fun J1 hJ1 => by
        c0_hsplit; rotate_left; · c0_hsteps; exact hJ1 (false, ()) m ⟨rfl, Bool.noConfusion⟩
        have he1_lt : e1.toNat < 2 * s.core.cur_vars :=
          w2_lit_lt_2cv hcv_le hmax (by simpa only [he1_def] using hc)
        have he1_v : (e1.setWidth 64).toNat < s.core.vals.length := by rw [w2_zext32, hvl]; omega
        c0_hsteps_nogrp; c0_hsplit
        · c0_hsteps; exact hJ1 (true, ()) m ⟨rfl, fun _ => he1_lt⟩
        · c0_hsteps; exact hJ1 (false, ()) m ⟨rfl, Bool.noConfusion⟩)
    rcases hm2 with rfl
    refine wp_join_group (ts := []) (fun () m3 => m = m3 ∧ (fa = true ∨ fb = true))
      (fun _ _ m3 ⟨hm3, hor⟩ => ?_)
      (fun J2 hJ2 => by
        c0_hsplit; · c0_hsteps; exact hJ2 () m ⟨rfl, Or.inl (by assumption)⟩
        c0_hsplit; · c0_hsteps; exact hJ2 () m ⟨rfl, Or.inr (by assumption)⟩
        · c0_hsteps; exact hretFF)
    rcases hm3 with rfl
    refine wp_join_group (ts := []) (fun () m4 => m = m4 ∧ fb = true)
      (fun _ _ m4 ⟨hm4, hfb⟩ => ?_)
      (fun J3 hJ3 => by
        c0_hsplit
        · c0_hsplit; · c0_hsteps; exact hJ3 () m ⟨rfl, by assumption⟩
          · c0_hsteps; exact hQ (a0.setWidth 64, ()) s m rfl hlen ⟨⟨rfl, rfl⟩, hexps⟩ hm
        · have hfb : fb = true := by rcases hor with ha | hb; · rw [ha] at hc; cases hc
                                     · exact hb
          c0_hsteps; exact hJ3 () m ⟨rfl, hfb⟩)
    rcases hm4 with rfl
    refine wp_join_group (ts := []) (fun () m5 => m = m5 ∧ fa = true)
      (fun _ _ m5 ⟨hm5, hfa⟩ => ?_)
      (fun J4 hJ4 => by
        c0_hsplit; · c0_hsteps; exact hJ4 () m ⟨rfl, by assumption⟩
        c0_hsplit
        · c0_hsteps; exact hQ (e1.setWidth 64, ()) s m rfl hlen ⟨⟨rfl, rfl⟩, hexps⟩ hm
        · rw [hfb] at *; contradiction)
    rcases hm5 with rfl
    have ha0x_lt : (a0 ^^^ 1#32).toNat < 2 * s.core.cur_vars := w2_xor1_lt (hfa_lt hfa)
    have he1x_lt : (e1 ^^^ 1#32).toNat < 2 * s.core.cur_vars := w2_xor1_lt (hfb_lt hfb)
    c0_hsteps_nogrp
    refine w2_break_call hBrk rfl hlen hm fun b0 m6 hm6 => ?_
    c0_hsteps_nogrp
    refine w2_break_call hBrk rfl hlen hm6 fun b1 m7 hm7 => ?_
    refine wp_join_group (ts := [i64]) (fun _ m8 => m7 = m8)
      (fun _ ⟨s0, ⟨⟩⟩ m8 hm8 => ?_)
      (fun J5 hJ5 => by
        c0_hsplit
        · have hb0_lt : b0.toNat < exps.toNat := hc
          have hb0_sb : 2 * (b0.setWidth 64).toNat + 1 < s.scratch.scratch_buf.length := by
            rw [w2_zext32, hsbl]; omega
          c0_hsteps; exact hJ5 (_, ()) m7 rfl
        · c0_hsteps; exact hJ5 (_, ()) m7 rfl)
    rcases hm8 with rfl
    refine wp_join_group (ts := [i64]) (fun _ m9 => m7 = m9)
      (fun _ ⟨s1, ⟨⟩⟩ m9 hm9 => ?_)
      (fun J6 hJ6 => by
        c0_hsplit
        · have hb1_lt : b1.toNat < exps.toNat := hc
          have hb1_sb : 2 * (b1.setWidth 64).toNat + 1 < s.scratch.scratch_buf.length := by
            rw [w2_zext32, hsbl]; omega
          c0_hsteps; exact hJ6 (_, ()) m7 rfl
        · c0_hsteps; exact hJ6 (_, ()) m7 rfl)
    rcases hm9 with rfl; c0_hsteps_nogrp; c0_call hAdd; intro sum
    have h1082_m : (8656#64 : BitVec 64).toNat % 8 = 0 := by decide
    c0_hsteps_nogrp
    let s1 : FullState := { s with scratch := { s.scratch with
      scratch_buf := setU64In32 s.scratch.scratch_buf ((8656#64 : BitVec 64).toNat / 8)
        (u64Of32Pair (s.scratch.scratch_buf[2 * ((8656#64 : BitVec 64).toNat / 8)]'(by omega))
          (s.scratch.scratch_buf[2 * ((8656#64 : BitVec 64).toNat / 8) + 1]'h1082_sb') *
          6364136223846793005#64 + 1442695040888963407#64) } }
    have hlen1 : s1.LengthsOk c := w2_len_sb_u64 hlen
    have hexps1 : WalkTblExpsOk s1 := walkTblExpsOk_of_setU64_ne (by decide) hexps
    have hm8 : (FullMem c s1 ⋆ R) _ := hm
    refine wp_join_group (ts := [i64]) (fun _ m9 => (FullMem c s1 ⋆ R) m9)
      (fun _ ⟨rnd, ⟨⟩⟩ m9 hm9 => ?_)
      (fun J7 hJ7 => by
        c0_hsplit; · c0_hsteps; exact hJ7 (0#64, ()) _ hm8
        · c0_hsteps_nogrp; c0_call hFrom; intro _; c0_hsteps; exact hJ7 (_, ()) _ hm8)
    c0_hsteps_nogrp; c0_call hMul; intro thr
    have hax_tr : ((a0 ^^^ 1#32).setWidth 64).toNat < s1.scratch.tarjan_reach.length := by
      rw [w2_zext32, hlen1.scratch_ok.tarjan_reach_len]; omega
    have hex_tr : ((e1 ^^^ 1#32).setWidth 64).toNat < s1.scratch.tarjan_reach.length := by
      rw [w2_zext32, hlen1.scratch_ok.tarjan_reach_len]; omega
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ mA => (FullMem c s1 ⋆ R) mA)
      (fun _ _ mA hmA => by
        refine wp_join_group (ts := [i32]) (fun _ mB => (FullMem c s1 ⋆ R) mB)
          (fun _ _ mB hmB => by
            c0_hsteps; exact hQ _ s1 mB rfl hlen1 ⟨⟨rfl, rfl⟩, hexps1⟩ hmB)
          (fun J9 hJ9 => by c0_hsteps <;> exact hJ9 (_, ()) mA hmA))
      (fun J8 hJ8 => by c0_hsteps <;> exact hJ8 (_, ()) m9 hm9)
  · c0_hsteps; exact hretFF
  · c0_hsteps; exact hretFF
  · c0_hsteps; exact hretFF
  · -- Large clause branch
    have he0_3 : e0.toNat + 3 ≤ s.core.arena_len := by
      have := e0.isLt; simp only [he0_def, show (3 : BitVec 64).toNat = 3 from rfl] at *; omega
    have he02_ar : (e0.setWidth 64 + 2#64).toNat < s.core.arena.length := by
      rw [BitVec.toNat_add, w2_zext32, show (2#64 : BitVec 64).toNat = 2 from rfl,
        Nat.mod_eq_of_lt (by have := e0.isLt; omega), harl]; omega
    let sz := s.core.arena[(e0.setWidth 64 + 2#64).toNat]'he02_ar
    have hsz_def : s.core.arena[(e0.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
        rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
          Nat.mod_eq_of_lt (by have := e0.isLt; omega), harl]; omega) = sz := by
      dsimp only [sz]; congr 1
    have he0sz : e0.toNat + 3 + sz.toNat ≤ s.core.arena_len := by
      simp only [he0_def, hsz_def] at hc
      rw [show (3 : BitVec 64).toNat = 3 from rfl,
        Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64),
        Nat.mod_eq_of_lt (by have := e0.isLt; have := sz.isLt; omega)] at hc; omega
    clear hc
    -- Loop 1 (`j < sz`)
    refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
      (fun sK (_sum, stored, _cnt, _psteps, tail_i, _last, j, ()) =>
        j.toNat ≤ sz.toNat ∧ stored.toNat ≤ c.max_vars ∧ tail_i.toNat ≤ sz.toNat ∧
        FullExtScratchPres s sK ∧ WalkTblExpsOk sK ∧
        sK.scratch.scratch_buf = s.scratch.scratch_buf)
      (fun (_, _, _, _, _, _, j, ()) => sz.toNat - j.toNat)
      (fun J0 hJ0 => by
        c0_hsteps; exact hJ0 s (0#64, 0#64, 0#64, 0#64, sz, 0xffffffff#32, 0#32, ()) m hm rfl hlen
          ⟨Nat.zero_le _, Nat.zero_le _, Nat.le_refl _, ⟨rfl, rfl⟩, hexps, rfl⟩)
      (fun J0 sK (sum, stored, cnt, psteps, tail_i, last_lit, j, ()) mK
          hcoreK hsK ⟨hj_le, hst_le, hti_le, hpresK, hexpsK, hsbK⟩ hmK hJ0 => ?_)
    dsimp only [fullSafetySlice] at hsK hmK; have hceqK : sK.core = s.core := hcoreK
    c0_hsplit
    · have hj_lt : j.toNat < sz.toNat := by simp only [he0_def, hsz_def] at hc; exact hc
      clear hc; have hj1 : (j + 1#32).toNat = j.toNat + 1 := w2_add1_32 hj_lt
      have hl_ar : (e0.setWidth 64 + 3#64 + j.setWidth 64).toNat < sK.core.arena.length :=
        w2_arena_lit_ar (by rw [hceqK, harl]) hale haca (by omega)
      c0_hsteps_nogrp
      let lit := sK.core.arena[(e0.setWidth 64 + 3#64 + j.setWidth 64).toNat]'hl_ar
      have hlit_def := w2_arena_lit_def (ar := sK.core.arena) (e0 := e0) (k := j)
        (by rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
          Nat.mod_eq_of_lt (by omega : e0.toNat + 3 + j.toNat < 2 ^ 64), hceqK, harl]; omega)
        hl_ar (by omega)
      refine wp_join_group (ts := [i64, i64, i64, i64, i32, i32])
        (fun (_, st', _, _, ti', _, ()) mN => ∃ sN : FullState,
          PreservesCoreSlice FullState.core sK sN ∧ sN.LengthsOk c ∧
          st'.toNat ≤ c.max_vars ∧ ti'.toNat ≤ sz.toNat ∧ FullExtScratchPres s sN ∧
          WalkTblExpsOk sN ∧ sN.scratch.scratch_buf = s.scratch.scratch_buf ∧ (FullMem c sN ⋆ R) mN)
        (fun _ ⟨sum', st', cnt', ps', ti', ll', ⟨⟩⟩ mN
            ⟨sN, hcoreN, hsN, hst', hti', hpresN, hexpsN, hsbN, hmN⟩ => by
          c0_hsteps; exact hJ0 sN (sum', st', cnt', ps', ti', ll', j + 1#32, ()) mN hmN
            (by dsimp only; rw [hj1]; omega) hcoreN hsN
            ⟨by rw [hj1]; omega, hst', hti', hpresN, hexpsN, hsbN⟩)
        (fun J1 hJ1 => by
          c0_hsplit; rotate_left
          · c0_hsteps; exact hJ1 (sum, stored, cnt, psteps, tail_i, last_lit, ()) mK
              ⟨sK, rfl, hsK, hst_le, hti_le, hpresK, hexpsK, hsbK, hmK⟩
          have hlit_lt : lit.toNat < 2 * s.core.cur_vars :=
            w2_lit_lt_2cv hcv_le hmax (by simpa only [he0_def, hlit_def] using hc)
          have hlit_v : (lit.setWidth 64).toNat < sK.core.vals.length := by
            rw [w2_zext32, hsK.core_ok.vals_len]; omega
          c0_hsteps_nogrp; c0_hsplit; rotate_left
          · c0_hsteps; exact hJ1 (sum, stored, cnt, psteps, tail_i, last_lit, ()) mK
              ⟨sK, rfl, hsK, hst_le, hti_le, hpresK, hexpsK, hsbK, hmK⟩
          have hlx_lt : (lit ^^^ 1#32).toNat < 2 * s.core.cur_vars := w2_xor1_lt hlit_lt
          c0_hsteps_nogrp
          refine w2_break_call hBrk rfl hsK hmK fun b mL hmL => ?_
          refine wp_join_group (ts := [i64]) (fun _ m1 => mL = m1)
            (fun _ ⟨sc, ⟨⟩⟩ m1 hm1 => ?_)
            (fun J2 hJ2 => by
              c0_hsplit
              · have hb_lt : b.toNat < exps.toNat := hc
                have hb_sb : 2 * (b.setWidth 64).toNat + 1 < sK.scratch.scratch_buf.length := by
                  rw [w2_zext32, hsK.scratch_ok.scratch_buf_len]; omega
                c0_hsteps; exact hJ2 (_, ()) mL rfl
              · c0_hsteps; exact hJ2 (_, ()) mL rfl)
          rcases hm1 with rfl; c0_hsteps_nogrp; c0_call hAdd; intro sum'
          have hlx_tr : ((lit ^^^ 1#32).setWidth 64).toNat < sK.scratch.tarjan_reach.length := by
            rw [w2_zext32, hsK.scratch_ok.tarjan_reach_len]; omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64, i32])
            (fun (st', ti', ()) m2 => ∃ sN : FullState, PreservesCoreSlice FullState.core sK sN ∧
              sN.LengthsOk c ∧ st'.toNat ≤ c.max_vars ∧ ti'.toNat ≤ sz.toNat ∧
              FullExtScratchPres s sN ∧ WalkTblExpsOk sN ∧
              sN.scratch.scratch_buf = s.scratch.scratch_buf ∧ (FullMem c sN ⋆ R) m2)
            (fun _ ⟨st', ti', ⟨⟩⟩ m2 ⟨sN, hcoreN, hsN, hst', hti', hpresN, hexpsN, hsbN, hm2⟩ => by
              c0_hsteps; exact hJ1 (sum', st', cnt + 1#64, _, ti', lit, ()) m2
                ⟨sN, hcoreN, hsN, hst', hti', hpresN, hexpsN, hsbN, hm2⟩)
            (fun J3 hJ3 => by
              c0_hsplit
              · have hst_lt : stored.toNat < c.max_vars := by
                  rw [Nat.mod_eq_of_lt (by omega : c.max_vars < 2 ^ 64)] at hc; exact hc
                have hst_w1 : stored.toNat < sK.scratch.work_stk1.length := by
                  rw [hsK.scratch_ok.work_stk1_len]; omega
                have hst_w2 : 2 * stored.toNat + 1 < sK.scratch.work_stk2.length := by
                  rw [hsK.scratch_ok.work_stk2_len]; omega
                have hst1 : (stored + 1#64).toNat = stored.toNat + 1 := w2_add1 (by omega)
                c0_hsteps
                exact hJ3 (stored + 1#64, tail_i, ()) _
                  ⟨{ sK with scratch := { sK.scratch with
                      work_stk1 := sK.scratch.work_stk1.set stored.toNat lit
                      work_stk2 := setU64In32 sK.scratch.work_stk2 stored.toNat sc } },
                    rfl, w2_len_wk1_wk2_u64 hsK, by omega, hti_le, ⟨hpresK.1, hpresK.2⟩,
                    w2_walkTblExpsOk_wk1_wk2 hexpsK, hsbK, hm⟩
              · refine wp_join_group (ts := [i32])
                  (fun (ti', ()) m2 => mL = m2 ∧ ti'.toNat ≤ sz.toNat)
                  (fun _ ⟨ti', ⟨⟩⟩ m2 ⟨hm2, hti'⟩ => by
                    rcases hm2 with rfl; c0_hsteps
                    exact hJ3 (stored, ti', ()) mL
                      ⟨sK, rfl, hsK, hst_le, hti', hpresK, hexpsK, hsbK, hmL⟩)
                  (fun J4 hJ4 => by
                    c0_hsplit
                    · c0_hsteps; exact hJ4 (j, ()) mL ⟨rfl, by omega⟩
                    · c0_hsteps; exact hJ4 (tail_i, ()) mL ⟨rfl, hti_le⟩)))
    · -- Exit Loop 1 (`j ≥ sz`)
      clear hc
      c0_hsplit; · c0_hsteps; exact hQ (0xffffffff#64, ()) sK mK hceqK hsK ⟨hpresK, hexpsK⟩ hmK
      c0_hsplit; · c0_hsteps; exact hQ (0xffffffff#64, ()) sK mK hceqK hsK ⟨hpresK, hexpsK⟩ hmK
      have h1082_m : (8656#64 : BitVec 64).toNat % 8 = 0 := by decide
      have h1082_sbK : 2 * ((8656#64 : BitVec 64).toNat / 8) + 1 <
          sK.scratch.scratch_buf.length := by
        rw [hsK.scratch_ok.scratch_buf_len, show (8656#64 : BitVec 64).toNat = 8656 from rfl]; omega
      c0_hsteps_nogrp
      let s1 : FullState := { sK with scratch := { sK.scratch with
        scratch_buf := setU64In32 sK.scratch.scratch_buf ((8656#64 : BitVec 64).toNat / 8)
          (u64Of32Pair (sK.scratch.scratch_buf[2 * ((8656#64 : BitVec 64).toNat / 8)]'(by omega))
            (sK.scratch.scratch_buf[2 * ((8656#64 : BitVec 64).toNat / 8) + 1]'h1082_sbK) *
            6364136223846793005#64 + 1442695040888963407#64) } }
      have hlen1 : s1.LengthsOk c := w2_len_sb_u64 hsK
      have hexps1 : WalkTblExpsOk s1 := walkTblExpsOk_of_setU64_ne (by decide) hexpsK
      have hm1 : (FullMem c s1 ⋆ R) _ := hm
      refine wp_join_group (ts := [i64]) (fun _ m2 => (FullMem c s1 ⋆ R) m2)
        (fun _ ⟨rnd, ⟨⟩⟩ m2 hm2 => ?_)
        (fun J1 hJ1 => by
          c0_hsplit; · c0_hsteps; exact hJ1 (0#64, ()) _ hm1
          · c0_hsteps_nogrp; c0_call hFrom; intro _; c0_hsteps; exact hJ1 (_, ()) _ hm1)
      c0_hsteps_nogrp; c0_call hMul; intro thr; c0_hsteps_nogrp
      -- Loop 2 (`sidx < stored`)
      refine wp_join_group (ts := [i64, i32, i64]) (fun _ m3 => (FullMem c s1 ⋆ R) m3)
        (fun _ ⟨acc, chosen, _sidx, ⟨⟩⟩ m3 hm3 => ?_)
        (fun J2 hJ2 => by
          refine wp_loop_safety_slice_pure (fullSafetySlice c) s1 R
            (fun sL (_, sidx, ()) => sL = s1 ∧ sidx.toNat ≤ stored.toNat)
            (fun (_, sidx, ()) => stored.toNat - sidx.toNat)
            (fun J3 hJ3 => by
              c0_hsteps; exact hJ3 s1 (0#64, 0#64, ()) m2 hm2 rfl hlen1 ⟨rfl, Nat.zero_le _⟩)
            (fun J3 sL (accL, sidx, ()) mL _ hsL ⟨hsLeq, hsi_le⟩ hmL hJ3 => by
              dsimp only [fullSafetySlice] at hsL hmL; subst sL
              c0_hsplit; rotate_left; · c0_hsteps; exact hJ2 (accL, 0xffffffff#32, sidx, ()) mL hmL
              have hsi_lt : sidx.toNat < stored.toNat := hc
              have hsi_w2 : 2 * sidx.toNat + 1 < s1.scratch.work_stk2.length := by
                rw [hlen1.scratch_ok.work_stk2_len]; omega
              have hsi_w1 : sidx.toNat < s1.scratch.work_stk1.length := by
                rw [hlen1.scratch_ok.work_stk1_len]; omega
              c0_hsteps_nogrp; c0_call hAdd; intro acc'; c0_hsteps_nogrp; c0_hsplit
              · c0_hsteps; exact hJ2 (acc', _, sidx, ()) mL hmL
              · have hsi1 : (sidx + 1#64).toNat = sidx.toNat + 1 := w2_add1 (by omega)
                c0_hsteps; exact hJ3 s1 (acc', sidx + 1#64, ()) mL hmL
                  (by dsimp only; omega) rfl hlen1 ⟨rfl, by omega⟩))
      -- Tail loop (`if (chosen == 0xFFFFFFFF && tail_i < sz)`)
      refine wp_join_group (ts := [i64, i32]) (fun _ m4 => (FullMem c s1 ⋆ R) m4)
        (fun _ ⟨_, _, ⟨⟩⟩ m4 hm4 => by
          refine wp_join_group (ts := [i32]) (fun _ m5 => m4 = m5)
            (fun _ _ m5 hm5 => by
              rcases hm5 with rfl
              refine wp_join_group (ts := [i64]) (fun _ m6 => m4 = m6)
                (fun _ _ m6 hm6 => by
                  rcases hm6 with rfl; c0_hsteps
                  exact hQ _ s1 m4 hceqK hlen1 ⟨hpresK, hexps1⟩ hm4)
                (fun J5 hJ5 => by c0_hsteps <;> exact hJ5 (_, ()) m4 rfl))
            (fun J4 hJ4 => by c0_hsteps <;> exact hJ4 (_, ()) m4 rfl))
        (fun J3 hJ3 => by
          c0_hsplit; rotate_left; · c0_hsteps; exact hJ3 (acc, chosen, ()) m3 hm3
          c0_hsplit; rotate_left; · c0_hsteps; exact hJ3 (acc, chosen, ()) m3 hm3
          refine wp_join_group (ts := [i64, i32, i32]) (fun _ m4 => (FullMem c s1 ⋆ R) m4)
            (fun _ ⟨acc3, ch3, _, ⟨⟩⟩ m4 hm4 => by c0_hsteps; exact hJ3 (acc3, ch3, ()) m4 hm4)
            (fun J4 hJ4 => by
              refine wp_loop_safety_slice_pure (fullSafetySlice c) s1 R
                (fun sL (_, k2, ()) => sL = s1 ∧ k2.toNat ≤ sz.toNat)
                (fun (_, k2, ()) => sz.toNat - k2.toNat)
                (fun J5 hJ5 => by
                  c0_hsteps; exact hJ5 s1 (acc, tail_i, ()) m3 hm3 rfl hlen1 ⟨rfl, hti_le⟩)
                (fun J5 sL (accL, k2, ()) mL _ hsL ⟨hsLeq, hk2_le⟩ hmL hJ5 => by
                  dsimp only [fullSafetySlice] at hsL hmL; subst sL
                  c0_hsplit; rotate_left; · c0_hsteps; exact hJ4 (accL, chosen, k2, ()) mL hmL
                  have hk2_lt : k2.toNat < sz.toNat := by
                    simp only [he0_def, hsz_def] at hc; exact hc
                  clear hc; have hk2_1 : (k2 + 1#32).toNat = k2.toNat + 1 := w2_add1_32 hk2_lt
                  have hl2_ar : (e0.setWidth 64 + 3#64 + k2.setWidth 64).toNat <
                      s1.core.arena.length :=
                    w2_arena_lit_ar (by rw [hceqK, harl]) hale haca (by omega)
                  c0_hsteps_nogrp
                  let lit2 := s1.core.arena[(e0.setWidth 64 + 3#64 + k2.setWidth 64).toNat]'hl2_ar
                  have hlit2_def := w2_arena_lit_def (ar := s1.core.arena) (e0 := e0) (k := k2)
                    (by rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                      Nat.mod_eq_of_lt (by omega : e0.toNat + 3 + k2.toNat < 2 ^ 64),
                      hceqK, harl]; omega) hl2_ar (by omega)
                  refine wp_join_group (ts := [i64, i32]) (fun _ mM => (FullMem c s1 ⋆ R) mM)
                    (fun _ ⟨accM, _, ⟨⟩⟩ mM hmM => by
                      c0_hsteps; exact hJ5 s1 (accM, k2 + 1#32, ()) mM hmM
                        (by dsimp only; rw [hk2_1]; omega) rfl hlen1 ⟨rfl, by rw [hk2_1]; omega⟩)
                    (fun J6 hJ6 => by
                      c0_hsplit; rotate_left; · c0_hsteps; exact hJ6 (accL, chosen, ()) mL hmL
                      have hlit2_lt : lit2.toNat < 2 * s.core.cur_vars :=
                        w2_lit_lt_2cv hcv_le hmax (by simpa only [he0_def, hlit2_def] using hc)
                      have hlit2_v : (lit2.setWidth 64).toNat < s1.core.vals.length := by
                        rw [w2_zext32, hceqK, hvl]; omega
                      c0_hsteps_nogrp
                      c0_hsplit; rotate_left; · c0_hsteps; exact hJ6 (accL, chosen, ()) mL hmL
                      c0_hsteps_nogrp
                      refine w2_break_call hBrk rfl hlen1 hmL fun b2 mA hmA => ?_
                      refine wp_join_group (ts := [i64]) (fun _ mB => mA = mB)
                        (fun _ ⟨sc2, ⟨⟩⟩ mB hmB => ?_)
                        (fun J7 hJ7 => by
                          c0_hsplit
                          · have hb2_lt : b2.toNat < exps.toNat := hc
                            have hb2_sb : 2 * (b2.setWidth 64).toNat + 1 <
                                s1.scratch.scratch_buf.length := by
                              rw [w2_zext32, hlen1.scratch_ok.scratch_buf_len]; omega
                            c0_hsteps; exact hJ7 (_, ()) mA rfl
                          · c0_hsteps; exact hJ7 (_, ()) mA rfl)
                      rcases hmB with rfl; c0_hsteps_nogrp; c0_call hAdd; intro acc2
                      c0_hsteps_nogrp; c0_hsplit
                      · c0_hsteps; exact hJ4 (acc2, lit2, k2, ()) mA hmA
                      · c0_hsteps; exact hJ6 (acc2, chosen, ()) mA hmA))))

/-! ## 3. `full_walk_m7_step13_wp` (`step13WalkM7Spec`) -/

/-- Step-13 `full_walk_m7` satisfies `step13WalkM7Spec`: calls `S1`'s binary roundtrip & large
watch reconnect, then runs the ProbSAT walk loop with `WalkTblExpsOk` preserved end-to-end. -/
theorem full_walk_m7_step13_wp (Γ : Env)
    (hRoundtrip : ∀ a m Q X, step13WatchRoundtripSpec a m Q X →
      Γ "full_dense_bin_roundtrip_fid" [i64] [] a m Q X)
    (hWatchLarge : ∀ a m Q X, step13WatchRoundtripSpec a m Q X →
      Γ "full_watch_large_clauses_fid" [i64] [] a m Q X)
    (hInitVals : ∀ a m Q X, m7InitValsSpec a m Q X →
      Γ "full_walk_init_vals_m7" [i64] [] a m Q X)
    (hCollect : ∀ a m Q X, m7CollectSpec a m Q X →
      Γ "full_walk_collect_m7" [i64] [i64] a m Q X)
    (hCbInv : ∀ a m Q X, step13WalkCbInvSpec a m Q X →
      Γ "full_walk_cb_inv_m7" [i64, i64, i64] [i64] a m Q X)
    (hBuildOcc : ∀ a m Q X, step13WalkBuildOccSpec a m Q X →
      Γ "full_walk_build_occ_m7" [i64, i64] [i64] a m Q X)
    (hEffort : ∀ a m Q X, step13WalkEffortSpec a m Q X →
      Γ "full_walk_effort_m7" [i64, i64] [i64] a m Q X)
    (hPick : ∀ a m Q X, step13WalkPickSpec a m Q X →
      Γ "full_walk_pick_m7" [i64, i32, i64] [i64] a m Q X)
    (hFlip : ∀ a m Q X, step13WalkFlipSpec a m Q X →
      Γ "full_walk_flip_m7" [i64, i32, i64, i64] [i64] a m Q X)
    (hSaveMin : ∀ a m Q X, m7SaveMinSpec a m Q X →
      Γ "full_walk_save_min_m7" [i64, i64, Ty.bool] [] a m Q X) :
    ∀ a m Q X, step13WalkM7Spec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_walk_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
  have hlen := hsp.lengths
  have hmax := c.hmaxv; have hscr := c.hscr; unfold dimacsBound at hmax hscr
  have hret0 : Q () m :=
    hQ s m hsp (w2_arenaPermEq_refl _) rfl rfl (Nat.le_refl _) rfl ⟨rfl, rfl⟩ hm
  dsimp only [Func.wp, FullFidelityStep13S3.full_walk_m7_body]
  c0_hsplit; · c0_hsteps; exact hret0
  have hcv_pos : 0 < s.core.cur_vars := Nat.pos_of_ne_zero fun h0 => hc (by rw [h0]; rfl)
  c0_hsplit; · c0_hsteps; exact hret0
  c0_hsplit; · c0_hsteps; exact hret0
  c0_hsplit; · c0_hsteps; exact hret0
  have hcap2300 : 2300 ≤ c.scratch_cap := by
    rw [Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64),
      show (2300 : BitVec 64).toNat = 2300 from rfl] at hc; omega
  c0_hsteps_nogrp
  -- 1. `full_dense_bin_roundtrip_fid` & `full_watch_large_clauses_fid`
  c0_call hRoundtrip
  refine ⟨c, F0, s, R, rfl, hsp, hm,
    fun sR1 mR1 hspR1 hpermR1 hcvR1 hclR1 hfuR1 hprR1 hpresR1 hmR1 => ?_⟩
  c0_hsteps_nogrp
  c0_call hWatchLarge
  refine ⟨c, F0, sR1, R, rfl, hspR1, hmR1,
    fun sW mW hspW hpermW hcvW hclW hfuW hprW hpresW hmW => ?_⟩
  have hlenW := hspW.lengths
  have hpermW0 : FullArenaPermEq s.core sW.core := w2_arenaPermEq_trans hpermR1 hpermW
  have hcvW0 : sW.core.cur_vars = s.core.cur_vars := hcvW.trans hcvR1
  have hclW0 : sW.core.cur_level = s.core.cur_level := hclW.trans hclR1
  have hfuW0 : sW.core.fuel = s.core.fuel := hfuW.trans hfuR1
  have hprW0 : sW.core.probing = s.core.probing := hprW.trans hprR1
  have hpresW0 : FullExtScratchPres s sW :=
    ⟨hpresW.1.trans hpresR1.1, hpresW.2.trans hpresR1.2⟩
  c0_hsteps_nogrp
  -- 2. `full_walk_init_vals_m7` & `full_walk_collect_m7`
  refine m7InitVals_call hInitVals rfl hlenW hmW fun s1 m1 hcore1 hlen1 hpres1 hm1 => ?_
  c0_hsteps_nogrp
  refine m7Collect_call hCollect rfl hlen1 hm1 fun rcol s2 m2 hcore2 hlen2 hpres2 hm2 => ?_
  have hcore20 : s2.core = sW.core := hcore2.trans hcore1
  have hpres20 : FullExtScratchPres s s2 :=
    ⟨hpres2.1.trans (hpres1.1.trans hpresW0.1), hpres2.2.trans (hpres1.2.trans hpresW0.2)⟩
  c0_hsteps_nogrp
  -- Join block for early return (`h->walk_cnt_stat++`)
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
        w2_sparse_with_fuel_and_scratch hspW hcoreE' hlenE'
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
      have hncl_lt : ncl.toNat < 2 ^ 32 := w2_rshift32_lt
      have hncl_pos : 0 < ncl.toNat :=
        Nat.pos_of_ne_zero fun h0 => hncl_ne (BitVec.eq_of_toNat_eq h0)
      have hcap5 : 2200 + 5 * ncl.toNat ≤ c.scratch_cap := by
        change ¬ c.scratch_cap % 2 ^ 64 < (2200 + 5 * ncl.toNat) % 2 ^ 64 at hcap_le
        rw [Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 2200 + 5 * ncl.toNat < 2 ^ 64)] at hcap_le; omega
      c0_hsteps_nogrp
      -- 3. `full_walk_cb_inv_m7`
      refine w2_cbInv_call hCbInv rfl hlen2 hm2 fun rcb s3 m3 hcore3 hlen3 hpres3 hexps3 hm3 => ?_
      have hcore30 : s3.core = sW.core := hcore3.trans hcore20
      have hpres30 : FullExtScratchPres s s3 := ⟨hpres3.1.trans hpres20.1, hpres3.2.trans hpres20.2⟩
      c0_hsplit; · c0_hsteps; exact hJ26 () m3 ⟨s3, hcore30, hlen3, hpres30, hm3⟩
      have hexps3_ok : WalkTblExpsOk s3 := hexps3 hc
      clear hc
      c0_hsteps_nogrp
      -- 4. `full_walk_build_occ_m7` & `full_walk_effort_m7`
      refine w2_buildOcc_call hBuildOcc rfl hlen3 hm3
        fun ru s4 m4 hcore4 hlen4 hpres4 hpre4 _ hm4 => ?_
      have hcore40 : s4.core = sW.core := hcore4.trans hcore30
      have hpres40 : FullExtScratchPres s s4 := ⟨hpres4.1.trans hpres30.1, hpres4.2.trans hpres30.2⟩
      have hexps4 : WalkTblExpsOk s4 := walkTblExpsOk_of_prefixPres hpre4 hexps3_ok
      c0_hsteps_nogrp
      refine w2_effort_call hEffort rfl hlen4 hm4 fun step_lim m5 hm5 => ?_
      c0_hsteps_nogrp
      have hwcap := w2_shr2_add1_le hcv_pos hlen.core_ok.cur_vars_le hmax
      have hbase : (2200#64 + 4#64 * ncl).toNat = 2200 + 4 * ncl.toNat := by
        rw [BitVec.toNat_add, BitVec.toNat_mul, show (2200#64 : BitVec 64).toNat = 2200 from rfl,
          show (4#64 : BitVec 64).toNat = 4 from rfl,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      -- 5. Main ProbSAT walk loop
      refine wp_join_group (ts := [i64, i64, i64, i64, Ty.bool, i64, i64])
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
                w2_sparse_with_fuel_and_scratch hspW hcoreZ hlenZ'
                  ⟨hpresZ.1.trans hpresW0.1.symm, hpresZ.2.trans hpresW0.2.symm⟩
              exact hQ sZ' _ hspZ' (by simpa [sZ', hcoreZ] using w2_arenaPermEq_with_fuel hpermW0)
                (by simp [sZ', hcoreZ, hcvW0]) (by simp [sZ', hcoreZ, hclW0])
                (by simp [sZ', hcoreZ, hfuW0] at *; omega) (by simp [sZ', hcoreZ, hprW0])
                hpresZ ‹_›)
            (fun _ hJsave => by
              c0_hsplit
              · c0_hsteps_nogrp
                refine m7SaveMin_call hSaveMin rfl hlenX hmX fun sY mY hcoreY hlenY hpresY hmY => ?_
                c0_hsteps; exact hJsave () mY ⟨sY, hcoreY.trans hcoreX, hlenY,
                  ⟨hpresY.1.trans hpresX.1, hpresY.2.trans hpresX.2⟩, hmY⟩
              · c0_hsteps; exact hJsave () mX ⟨sX, hcoreX, hlenX, hpresX, hmX⟩))
        (fun J53X hJ53X => by
          refine wp_loop_group (ts := [i64, i64, i64, i64, Ty.bool, i64, i64])
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
              ⟨w2_core_lengths_with_fuel hlenL.core_ok, hlenL.scratch_ok⟩
            have hslot_sb1 : (2200#64 + 4#64 * (rcol >>> 32#64) + flp % uc).toNat <
                sL1.scratch.scratch_buf.length := hslot_sb
            have hmL1 : (FullMem c sL1 ⋆ R) m := by rw [hcoreL_fl] at hm; exact hm
            refine C0HeadStep.head_wp_load rfl
              (FullArenaTactics.c0_load_full_scratch_buf hslot_sb1 hmL1) ?_
            c0_hsplit
            · c0_hsteps; exact hJ53X _ m ⟨sL1, fuelL - 1#64, hcoreL1, hfuelL1, hlenL1, hpresL, ‹_›⟩
            · c0_hsteps_nogrp
              have hexpsL1 : WalkTblExpsOk sL1 := hexpsL
              refine w2_pick_call hPick rfl hexpsL1 hlenL1 hmL1
                fun rpick sL2 mL2 hcoreL2 hlenL2 hpresL2 hexpsL2 hmL2 => ?_
              have hcoreL2' : sL2.core = { sW.core with fuel := fuelL - 1#64 } :=
                hcoreL2.trans hcoreL1
              have hpresL20 : FullExtScratchPres s sL2 :=
                ⟨hpresL2.1.trans hpresL.1, hpresL2.2.trans hpresL.2⟩
              c0_hsteps_nogrp; c0_hsplit
              · c0_hsteps; exact hJ53 (fn - 1) _ _ hlt_n
                  ⟨sL2, fuelL - 1#64, hcoreL2', hfn_sub, hfuelL1, hlenL2, hpresL20, hexpsL2, hmL2⟩
              · c0_hsteps_nogrp
                refine w2_flip_call hFlip rfl hlenL2 hmL2
                  fun rflip sL3 mL3 hcoreL3 hlenL3 hpresL3 hpreL3 _ hmL3 => ?_
                have hcoreL3' : sL3.core = { sW.core with fuel := fuelL - 1#64 } :=
                  hcoreL3.trans hcoreL2'
                have hpresL30 : FullExtScratchPres s sL3 :=
                  ⟨hpresL3.1.trans hpresL20.1, hpresL3.2.trans hpresL20.2⟩
                have hexpsL3 : WalkTblExpsOk sL3 := walkTblExpsOk_of_prefixPres hpreL3 hexpsL2
                c0_hsteps_nogrp
                -- Trail & best-snapshot join
                let PStep (mS : Mem 64) : Prop :=
                  ∃ sS, sS.core = { sW.core with fuel := fuelL - 1#64 } ∧ sS.LengthsOk c ∧
                    FullExtScratchPres s sS ∧ WalkTblExpsOk sS ∧ (FullMem c sS ⋆ R) mS
                refine wp_join_group (ts := [i64, i64, Ty.bool]) (fun _ mFin => PStep mFin)
                  (fun _ ⟨_, _, _, ⟨⟩⟩ mFin
                      ⟨sFin, hcoreFin, hlenFin, hpresFin, hexpsFin, hmFin⟩ => by
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := [i64, i64, i64, Ty.bool]) (fun _ mD => PStep mD)
                      (fun _ _ mD ⟨sD, hcoreD, hlenD, hpresD, hexpsD, hmD⟩ => by
                        c0_hsteps; exact hJ53 (fn - 1) _ _ hlt_n
                          ⟨sD, fuelL - 1#64, hcoreD, hfn_sub, hfuelL1, hlenD, hpresD, hexpsD, hmD⟩)
                      (fun J_done hJ_done => by
                        c0_hsplit; rotate_left
                        · c0_hsteps
                          exact hJ_done _ mFin ⟨sFin, hcoreFin, hlenFin, hpresFin, hexpsFin, hmFin⟩
                        refine wp_join_group (ts := [i64, i64, Ty.bool]) (fun _ m14 => PStep m14)
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
                                  rw [w2_shl1 (by omega), hlenB.scratch_ok.walk_vals_len]; omega
                                have hidx_wb : idx.toNat < sB.scratch.walk_best.length := by
                                  rw [hlenB.scratch_ok.walk_best_len]; omega
                                have hidx1 : (idx + 1).toNat = idx.toNat + 1 := w2_add1 (by omega)
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
                    refine wp_join_group (ts := [i64, i64, Ty.bool]) (fun _ m93 => PStep m93)
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
                        refine wp_join_group (ts := [i64, i64, Ty.bool]) (fun _ mB => PStep mB)
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
                                have hk1 : (k + 1).toNat = k.toNat + 1 := w2_add1 (by omega)
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
                                      rw [w2_zext32]; exact hw_lt
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
                              · -- Compact `wsort[0..ml-bc)`
                                c0_hsteps_nogrp
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
                                  have hj1 : (j + 1).toNat = j.toNat + 1 := w2_add1 (by omega)
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

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S3
