/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Forward
public import LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Forward.Lemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Forward WP Proofs Part 1a (`Proof.Forward.Wp1a`)

Shared helpers and watch-emission WP (`s13_bin_roundtrip_emit_wp`) for
`full_dense_bin_roundtrip_fid_wp` (both sparse `Walk` and dense `Probe`/`Factor` modes).

Zero legacy imports (`Full*`, `PatchModule`, `Solver`), `0` `@[expose]` on theorems/lemmas,
every file `<= 1,500`L, every decl `<= 450`L, every line `<= 100` cols.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Forward

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Forward
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

/-! ## 1. Shared Watch-Slice & Binary-Pair Invariants -/

theorem s13_modeSlice_step_bin {F_cur : List (List Nat)} {k : FullCoreState}
    {l p rem : Nat} {w0 : BitVec 32} (h : ModeWatchSliceOk F_cur k l p rem)
    (hrem : 0 < rem) (hw0 : k.wstk[p]? = some w0)
    (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) :
    w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
    ModeWatchSliceOk F_cur k l (p + 1) (rem - 1) := by
  rcases h.cases_step hrem with
    ⟨r1, w0', hr1, hp, hf, hne, hlt, hent, hrest⟩ | ⟨_, w0', _, _, hp, _, hf, _⟩
  · rw [hw0] at hp; cases Option.some.inj hp
    exact ⟨hne, hlt, hent, by rw [show rem - 1 = r1 by omega]; exact hrest⟩
  · rw [hw0] at hp; cases Option.some.inj hp; exact absurd hf hbin

private theorem s13_lt31_and_high {x : BitVec 32} (hx : x.toNat < 2 ^ 31) :
    (x &&& 0x80000000#32) = 0#32 := by
  have hand : (x &&& 0x7FFFFFFF#32) = x := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx]
  rw [← hand, BitVec.and_assoc, show (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 by decide,
    BitVec.and_zero]

theorem s13_modeSlice_step_nonbin {F_cur : List (List Nat)} {k : FullCoreState}
    {l p rem : Nat} {w0 : BitVec 32} (h : ModeWatchSliceOk F_cur k l p rem)
    (hrem : 0 < rem) (hw0 : k.wstk[p]? = some w0)
    (hnb : (w0 &&& 0x80000000#32) = 0#32) :
    2 ≤ rem ∧ (∃ w1 : BitVec 32, k.wstk[p + 1]? = some w1 ∧
      (w1 &&& 0x80000000#32) = 0#32) ∧
    ModeWatchSliceOk F_cur k l (p + 2) (rem - 2) := by
  unfold ModeWatchSliceOk at h
  by_cases hc : k.dense_mode = 0#64 <;> simp only [hc, ↓reduceIte] at h
  · cases h with
    | empty => omega
    | bin hw_p hf_p _ _ _ _ =>
      rw [hw0] at hw_p; cases Option.some.inj hw_p; exact absurd hnb hf_p
    | large =>
      refine ⟨by omega,
        ⟨_, by assumption, by first | assumption | exact s13_lt31_and_high (by assumption)⟩, ?_⟩
      rw [Nat.add_sub_cancel]; unfold ModeWatchSliceOk; simp only [hc, ↓reduceIte]; assumption
  · cases h with
    | empty => omega
    | bin hw_p hf_p _ _ _ _ =>
      rw [hw0] at hw_p; cases Option.some.inj hw_p; exact absurd hnb hf_p
    | occ =>
      refine ⟨by omega,
        ⟨_, by assumption, by first | assumption | exact s13_lt31_and_high (by assumption)⟩, ?_⟩
      rw [Nat.add_sub_cancel]; unfold ModeWatchSliceOk; simp only [hc, ↓reduceIte]; assumption

private theorem s13_bin_word_props {x : BitVec 32} (hx : x.toNat < 2 ^ 30) :
    let w := (x &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    (w &&& 0x80000000#32) ≠ 0#32 ∧ w ≠ 0xFFFFFFFF#32 ∧ (w &&& 0x7FFFFFFF#32) = x := by
  have hx_lt : x.toNat < 2 ^ 31 := by omega
  have hand : (x &&& 0x7FFFFFFF#32) = x := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx_lt]
  have hbit : (x &&& 0x80000000#32) = 0#32 := by
    rw [← hand, BitVec.and_assoc, show (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 by decide,
      BitVec.and_zero]
  have hf : (((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x80000000#32) ≠ 0#32 := by
    rw [hand]; intro heq
    have h31 := congrArg (·[31]) heq
    simp at h31
  have hne : ((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32) ≠ 0xFFFFFFFF#32 := by
    rw [hand]; intro heq
    have : (x ||| 0x80000000#32) &&& 0x7FFFFFFF#32 = 0x7FFFFFFF#32 := by rw [heq]; decide
    have hdisj : (x ||| 0x80000000#32) &&& 0x7FFFFFFF#32 = x := by
      ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or]
      by_cases h31 : i = 31
      · subst h31; have hxb := congrArg (·[31]) hbit; simp at hxb; simp [hxb]
      · have h0 : (0x80000000#32 : BitVec 32)[i] = false := by revert i hi h31; decide
        have h1 : (0x7FFFFFFF#32 : BitVec 32)[i] = true := by revert i hi h31; decide
        simp [h0, h1]
    rw [hdisj] at this; rw [this] at hx; revert hx; decide
  have hmask : (((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x7FFFFFFF#32) = x := by
    rw [hand]; ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or]
    by_cases h31 : i = 31
    · subst h31; have hxb := congrArg (·[31]) hbit; simp at hxb; simp [hxb]
    · have h0 : (0x80000000#32 : BitVec 32)[i] = false := by revert i hi h31; decide
      have h1 : (0x7FFFFFFF#32 : BitVec 32)[i] = true := by revert i hi h31; decide
      simp [h0, h1]
  exact ⟨hf, hne, hmask⟩

/-- Binary watch pairs `(scr[2*i], scr[2*i+1])` buffered in `scratch_buf[0 ..< 2*nb)`. -/
@[expose] def BinPairsOk (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (nb : Nat) (scr : List (BitVec 32)) : Prop :=
  scr.length = c.scratch_cap ∧ 2 * nb ≤ c.scratch_cap ∧
  ∀ i < nb,
    let a := scr[2 * i]?.getD 0#32
    let b := scr[2 * i + 1]?.getD 0#32
    a.toNat < 2 * s.core.cur_vars ∧ b.toNat < 2 * s.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat])

theorem s13_binPairsOk_push {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {nb : Nat} {scr : List (BitVec 32)} (h : BinPairsOk c F_cur s nb scr)
    (hlt : 2 * nb + 1 < c.scratch_cap) {a b : BitVec 32}
    (ha : a.toNat < 2 * s.core.cur_vars) (hb : b.toNat < 2 * s.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat])) :
    BinPairsOk c F_cur s (nb + 1) ((scr.set (2 * nb) a).set (2 * nb + 1) b) := by
  refine ⟨by simp [h.1], by omega, fun i hi => ?_⟩
  by_cases hin : i = nb
  · subst hin; dsimp only
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by rw [h.1]; omega),
      List.getElem?_set_self (by simp [h.1]; omega), Option.getD_some, Option.getD_some]
    exact ⟨ha, hb, hent⟩
  · dsimp only
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact h.2.2 i (by omega)

private theorem s13_empty_modeWatchesInv {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (_hwvec : k.wvec.length = 4 * c.max_vars) (_hcv : k.cur_vars ≤ c.max_vars)
    (hwl : k.wlen = 1)
    (hz : ∀ l < 2 * k.cur_vars, k.wvec[2 * l]? = some 0#32 ∧ k.wvec[2 * l + 1]? = some 0#32) :
    ModeWatchesInv F_cur k := by
  have hlay : WatchStackLayout k :=
    ⟨fun l hl => by
       obtain ⟨h0, h1⟩ := hz l hl
       simp only [fullWatchOffCore, fullWatchSizeCore, h0, h1, Option.getD_some, hwl]
       decide,
     fun l hl hpos => by
       obtain ⟨_, h1⟩ := hz l hl
       simp only [fullWatchSizeCore, h1, Option.getD_some] at hpos
       exact absurd hpos (by decide),
     fun l1 _ hl1 _ _ hp1 _ => by
       obtain ⟨_, h1⟩ := hz l1 hl1
       simp only [fullWatchSizeCore, h1, Option.getD_some] at hp1
       exact absurd hp1 (by decide),
     fun l hl idx hidx => by
       obtain ⟨_, h1⟩ := hz l hl
       simp only [fullWatchSizeCore, h1, Option.getD_some] at hidx
       simp at hidx⟩
  unfold ModeWatchesInv
  by_cases hc : k.dense_mode = 0#64 <;> simp only [hc, ↓reduceIte]
  · refine ⟨hlay, fun l hl => ?_⟩
    obtain ⟨_, h1⟩ := hz l hl
    simp only [fullWatchSizeCore, h1, Option.getD_some]; exact .empty
  · refine ⟨hlay, fun l hl => ?_⟩
    obtain ⟨_, h1⟩ := hz l hl
    simp only [fullWatchSizeCore, h1, Option.getD_some]; exact .empty

/-! ## 2. `full_watch_push` Binary Call & Emission Phase WP -/

private theorem s13_bin_roundtrip_call_push {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hPush : Γ.Has "full_watch_push" Proof.Spec.fullWatchPushSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {a b : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64}
    {cont : Tup Val [.bool] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (_ha_lt : a.toNat < 2 * s.core.cur_vars) (hb_lt : b.toNat < 2 * s.core.cur_vars)
    (hb_bd : b.toNat < 2 ^ 30)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat]))
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.dense_mode = s.core.dense_mode →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.vals = s.core.vals → s'.core.lvl = s.core.lvl → s'.core.flags = s.core.flags →
      s'.core.fuel = s.core.fuel → s'.core.inconsistent = s.core.inconsistent →
      s'.core.d_cur = s.core.d_cur → s'.core.d_val = s.core.d_val →
      s'.core.frame_trail = s.core.frame_trail → s'.core.frame_dec = s.core.frame_dec →
      s'.core.trail_end = s.core.trail_end → s'.core.propagated = s.core.propagated →
      s'.core.probing = s.core.probing →
      s'.scratch.extend_len = s.scratch.extend_len →
      s'.scratch.walk_vals = s.scratch.walk_vals →
      s'.scratch.walk_best = s.scratch.walk_best →
      s'.scratch.last_learned = s.scratch.last_learned →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.core.lit_mark = s.core.lit_mark → s'.core.mrk = s.core.mrk →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (cont (ok, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
      "full_watch_push"
      (Arg.var c.hdr, Arg.var a, Arg.var ((b &&& 0x7FFFFFFF#32) ||| 0x80000000#32),
        Arg.imm 0, Arg.imm 1, ()) cont) m := by
  have hwp := s13_bin_word_props hb_bd
  refine wp_call_of_spec _ cont
    (hPush (c.hdr, a, (b &&& 0x7FFFFFFF#32) ||| 0x80000000#32, 0#32, 1#32, ()) m
      (fun r m' => wp Γ Q X (cont r) m') X
      ⟨c, s, R, rfl, hlen, hw.watches.layout, fun _ => hwp.2.1,
        fun h => by exfalso; revert h; decide, hm, ?_⟩)
  intro ok wvec' wstk' wlen' wu' ws' m' _ hlen' hlay' hoth' hokT' hokF' hm'
  let s' : FullState :=
    { s with
      core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
      scratch := { s.scratch with wsort := ws' } }
  have hwat' : ModeWatchesInv F_cur s'.core :=
    fullWatchPush_preserves_modeWatchesInv hw.watches hlay' rfl rfl (fun _ hr => hr)
      (fun _ => ⟨hwp.1, hwp.2.1, by rw [hwp.2.2]; exact hb_lt,
        by rw [hwp.2.2]; exact hent⟩)
      (fun h2 => by exfalso; revert h2; decide)
      hoth' hokT' (fun hf ha => (hokF' hf).1 ha)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat' }
  exact hk ok s' m' hlen' hw' rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl hm'

/-- Watch-clearing and buffered binary-watch re-emission WP lemma shared by
`full_dense_bin_roundtrip_fid_wp`. -/
theorem s13_bin_roundtrip_emit_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hPush : Γ.Has "full_watch_push" Proof.Spec.fullWatchPushSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {nb : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {exitE : Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hlm : FullLitMarksClear c s) (hnd : FullArenaVarsNodup s) (hext : FullExtScratchOk c s)
    (hwcap : 0 < c.wcap) (hcv_bd : 2 * s.core.cur_vars < 2 ^ 30)
    (hbp : BinPairsOk c F_cur s nb.toNat s.scratch.scratch_buf) (hm : (FullMem c s ⋆ R) m)
    (hExit : ∀ (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.dense_mode = s.core.dense_mode →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.vals = s.core.vals → s'.core.lvl = s.core.lvl → s'.core.flags = s.core.flags →
      s'.core.fuel = s.core.fuel → s'.core.inconsistent = s.core.inconsistent →
      s'.core.d_cur = s.core.d_cur → s'.core.d_val = s.core.d_val →
      s'.core.frame_trail = s.core.frame_trail → s'.core.frame_dec = s.core.frame_dec →
      s'.core.trail_end = s.core.trail_end → s'.core.propagated = s.core.propagated →
      s'.core.probing = s.core.probing →
      s'.scratch.extend_len = s.scratch.extend_len →
      s'.scratch.walk_vals = s.scratch.walk_vals →
      s'.scratch.walk_best = s.scratch.walk_best →
      s'.scratch.last_learned = s.scratch.last_learned →
      (FullMem c s' ⋆ R) m' → wp Γ Q X exitE m') :
    let nlits : BitVec 64 := BitVec.ofNat 64 s.core.cur_vars <<< 1#64
    let pwvec : Val i64 := c.pWvec
    let pwstk : Val i64 := c.pWstk
    let ppairs : Val i64 := c.pScratchBuf
    wp Γ Q X
      (Expr.group (sig := [[i64]]) (fun Js =>
        Blocks.cons (fun (l, ()) =>
          Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var l, Arg.var nlits, ()))
            (fun (bl, ()) =>
          Expr.jnz (Arg.var bl)
            (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (c1, ()) =>
            Expr.let_ (Op.mk (.shl i64) (Arg.var l, Arg.var c1, ())) (fun (l2, ()) =>
            Expr.let_ (Op.mk (.mul i64) (Arg.var l2, Arg.imm 4, ())) (fun (o0, ()) =>
            Expr.let_ (Op.mk (.add i64) (Arg.var pwvec, Arg.var o0, ())) (fun (a0, ()) =>
            Expr.store (t := i32) (Arg.imm 0) (Arg.var a0)
              (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (c1b, ()) =>
              Expr.let_ (Op.mk (.shl i64) (Arg.var l, Arg.var c1b, ())) (fun (l2b, ()) =>
              Expr.let_ (Op.mk (.add i64) (Arg.var l2b, Arg.imm 1, ())) (fun (l2p, ()) =>
              Expr.let_ (Op.mk (.mul i64) (Arg.var l2p, Arg.imm 4, ())) (fun (o1, ()) =>
              Expr.let_ (Op.mk (.add i64) (Arg.var pwvec, Arg.var o1, ())) (fun (a1, ()) =>
              Expr.store (t := i32) (Arg.imm 0) (Arg.var a1)
                (Expr.let_ (Op.mk (.add i64) (Arg.var l, Arg.imm 1, ())) (fun (ln, ()) =>
                Expr.jump Js.fst (Arg.var ln, ()))))))))))))))
            (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 0, ())) (fun (z0, ()) =>
            Expr.let_ (Op.mk (.mul i64) (Arg.var z0, Arg.imm 4, ())) (fun (oz, ()) =>
            Expr.let_ (Op.mk (.add i64) (Arg.var pwstk, Arg.var oz, ())) (fun (az, ()) =>
            Expr.store (t := i32) (Arg.imm 0) (Arg.var az)
              (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 56, ())) (fun (pwl, ()) =>
              Expr.store (t := i64) (Arg.imm 1) (Arg.var pwl)
                (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 464, ())) (fun (pwu, ()) =>
                Expr.store (t := i64) (Arg.imm 0) (Arg.var pwu)
                  (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 504, ()))
                    (fun (pnb, ()) =>
                  Expr.store (t := i64) (Arg.var nb) (Arg.var pnb)
                    (Expr.group (sig := [[i64]]) (fun Jk =>
                      Blocks.cons (fun (k, ()) =>
                        Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var k, Arg.var nb, ()))
                          (fun (bk, ()) =>
                        Expr.jnz (Arg.var bk)
                          (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (c1, ()) =>
                          Expr.let_ (Op.mk (.shl i64) (Arg.var k, Arg.var c1, ()))
                            (fun (k2, ()) =>
                          Expr.let_ (Op.mk (.mul i64) (Arg.var k2, Arg.imm 4, ()))
                            (fun (ok0, ()) =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var ppairs, Arg.var ok0, ()))
                            (fun (ak0, ()) =>
                          Expr.load i32 (Arg.var ak0) (fun a =>
                          Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) (fun (c1b, ()) =>
                          Expr.let_ (Op.mk (.shl i64) (Arg.var k, Arg.var c1b, ()))
                            (fun (k2b, ()) =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var k2b, Arg.imm 1, ()))
                            (fun (k2p, ()) =>
                          Expr.let_ (Op.mk (.mul i64) (Arg.var k2p, Arg.imm 4, ()))
                            (fun (ok1, ()) =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var ppairs, Arg.var ok1, ()))
                            (fun (ak1, ()) =>
                          Expr.load i32 (Arg.var ak1) (fun b =>
                          Expr.let_ (Op.mk (.and i32) (Arg.var b, Arg.imm 0x7FFFFFFF, ()))
                            (fun (bm, ()) =>
                          Expr.let_ (Op.mk (.or i32) (Arg.var bm, Arg.imm 0x80000000, ()))
                            (fun (wb, ()) =>
                          Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
                            "full_watch_push"
                            (Arg.var c.hdr, Arg.var a, Arg.var wb, Arg.imm 0, Arg.imm 1, ())
                            (fun (_, ()) =>
                          Expr.let_ (Op.mk (.and i32) (Arg.var a, Arg.imm 0x7FFFFFFF, ()))
                            (fun (am, ()) =>
                          Expr.let_ (Op.mk (.or i32) (Arg.var am, Arg.imm 0x80000000, ()))
                            (fun (wa, ()) =>
                          Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
                            "full_watch_push"
                            (Arg.var c.hdr, Arg.var b, Arg.var wa, Arg.imm 0, Arg.imm 1, ())
                            (fun (_, ()) =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var k, Arg.imm 1, ()))
                            (fun (kn, ()) =>
                          Expr.jump Jk.fst (Arg.var kn, ()))))))))))))))))))))
                          exitE))
                      Blocks.nil) (fun Jk => Expr.jump Jk.fst (Arg.imm 0, ())))))))))))))))
        Blocks.nil) (fun Js => Expr.jump Js.fst (Arg.imm 0, ()))) m := by
  intro nlits pwvec pwstk ppairs
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwv_len := hlen.core_ok.wvec_len
  have hws_len := hlen.core_ok.wstk_len_arr
  have hnlits : nlits.toNat = 2 * s.core.cur_vars := by
    dsimp only [nlits]
    have hmx := c.hmaxv; unfold dimacsBound at hmx
    rw [show BitVec.ofNat 64 s.core.cur_vars <<< 1#64 =
        BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat) from rfl,
      BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
      Nat.shiftLeft_eq, Nat.pow_one,
      Nat.mod_eq_of_lt (by omega : s.core.cur_vars * 2 < 2 ^ 64)]; omega
  refine wp_loop_inv (ts := [i64])
    (fun (l, ()) mL => l.toNat ≤ 2 * s.core.cur_vars ∧ ∃ wvecL : List (BitVec 32),
      wvecL.length = 4 * c.max_vars ∧
      (∀ i < l.toNat, wvecL[2 * i]? = some 0#32 ∧ wvecL[2 * i + 1]? = some 0#32) ∧
      (FullMem c { s with core := { s.core with wvec := wvecL } } ⋆ R) mL)
    (fun (l, ()) _ => 2 * s.core.cur_vars - l.toNat)
    (fun Js hLoopL => by
      c0_hsteps_nogrp
      exact hLoopL (0#64, ()) m ⟨Nat.zero_le _, s.core.wvec, hwv_len, fun _ h => by simp at h, hm⟩)
    (fun Js ⟨l, ⟨⟩⟩ mL ⟨hl_le, wvecL, hwvL, hzeroL, hmL⟩ hLoopL => ?_)
  c0_hsplit
  · have hl_lt : l.toNat < 2 * s.core.cur_vars := by rw [← hnlits]; exact hc
    have hidx0 : (l <<< 1#64).toNat = 2 * l.toNat := by
      have hmx := c.hmaxv; unfold dimacsBound at hmx
      rw [show l <<< 1#64 = l <<< (1 : Nat) from rfl, BitVec.toNat_shiftLeft,
        Nat.shiftLeft_eq, Nat.pow_one,
        Nat.mod_eq_of_lt (by omega : l.toNat * 2 < 2 ^ 64)]; omega
    have hidx1 : ((l <<< 1#64) + 1#64).toNat = 2 * l.toNat + 1 := by
      have hmx := c.hmaxv; unfold dimacsBound at hmx
      rw [BitVec.toNat_add, hidx0, show (1#64 : BitVec 64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by omega)]
    have h0_lt : (l <<< 1#64).toNat <
        ({ s with core := { s.core with wvec := wvecL } }).core.wvec.length := by
      dsimp only; omega
    let w1 := wvecL.set (l <<< 1#64).toNat 0#32
    have h1_lt : ((l <<< 1#64) + 1#64).toNat <
        ({ s with core := { s.core with wvec := w1 } }).core.wvec.length := by
      dsimp only [w1]; rw [List.length_set]; omega
    have hl1 : (l + 1#64).toNat = l.toNat + 1 := by bv_omega
    c0_hsteps_nogrp
    have hmL' : (FullMem c { s with core := { s.core with
        wvec := (wvecL.set (2 * l.toNat) 0#32).set (2 * l.toNat + 1) 0#32 } } ⋆ R) m := by
      change (FullMem c { s with core := { s.core with
          wvec := (wvecL.set (l <<< 1#64).toNat 0#32).set
            ((l <<< 1#64 + 1#64).toNat) 0#32 } } ⋆ R) m at hm
      rw [hidx0, hidx1] at hm
      exact hm
    exact hLoopL (l + 1#64, ()) _ (by dsimp only; omega)
      ⟨by omega, _, by simp [hwvL], fun i hi => by
        by_cases hil : i = l.toNat
        · subst hil
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
            List.getElem?_set_self (by simp [hwvL]; omega)]; exact ⟨rfl, rfl⟩
        · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
          exact hzeroL i (by omega),
       hmL'⟩
  · have hl_eq : l.toNat = 2 * s.core.cur_vars := by
      have hlt : ¬ l.toNat < nlits.toNat := hc
      omega
    clear hLoopL Js
    have h0_ws : (BitVec.ofNat 64 (0#32 : BitVec 32).toNat).toNat <
        ({ s with core := { s.core with wvec := wvecL } }).core.wstk.length := by
      dsimp only; rw [hws_len]
      simp only [BitVec.toNat_ofNat, Nat.zero_mod]; exact hwcap
    have hmL_f : (FullMem c { s with core := { s.core with wvec := wvecL } } ⋆ R) mL := hmL
    c0_hsteps_nogrp
    let wstk0 := s.core.wstk.set 0 0#32
    let s0 : FullState :=
      { s with core := { s.core with wvec := wvecL, wstk := wstk0, wlen := 1,
                                     wusable := 0#64, num_binary := nb } }
    have hws_a : wstk0.length = c.wcap := by simp [wstk0, hws_len]
    have hwl_l : 1 ≤ c.wcap := hwcap
    have hlen0 : s0.LengthsOk c :=
      ⟨{ hlen.core_ok with wvec_len := hwvL, wstk_len_arr := hws_a, wlen_le := hwl_l },
       hlen.scratch_ok⟩
    have hwat0 : ModeWatchesInv F_cur s0.core :=
      s13_empty_modeWatchesInv hwvL hcv_le rfl fun i hi => by
        dsimp only [s0] at hi; exact hzeroL i (by omega)
    have hw0 : FullWitnessInv c F0 F_cur s0.core :=
      { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat0 }
    have hbp0 : BinPairsOk c F_cur s0 nb.toNat s0.scratch.scratch_buf :=
      ⟨hbp.1, hbp.2.1, fun i hi => hbp.2.2 i hi⟩
    refine wp_loop_inv (ts := [i64])
      (fun (k, ()) mK => k.toNat ≤ nb.toNat ∧ ∃ sK : FullState,
        sK.LengthsOk c ∧ FullWitnessInv c F0 F_cur sK.core ∧
        sK.core.cur_vars = s.core.cur_vars ∧ sK.core.cur_level = s.core.cur_level ∧
        sK.core.dense_mode = s.core.dense_mode ∧ sK.core.arena = s.core.arena ∧
        sK.core.arena_len = s.core.arena_len ∧ sK.core.vals = s.core.vals ∧
        sK.core.lvl = s.core.lvl ∧ sK.core.flags = s.core.flags ∧
        sK.core.fuel = s.core.fuel ∧ sK.core.inconsistent = s.core.inconsistent ∧
        sK.core.d_cur = s.core.d_cur ∧ sK.core.d_val = s.core.d_val ∧
        sK.core.frame_trail = s.core.frame_trail ∧ sK.core.frame_dec = s.core.frame_dec ∧
        sK.core.trail_end = s.core.trail_end ∧ sK.core.propagated = s.core.propagated ∧
        sK.core.probing = s.core.probing ∧
        sK.scratch.extend_len = s.scratch.extend_len ∧
        sK.scratch.walk_vals = s.scratch.walk_vals ∧
        sK.scratch.walk_best = s.scratch.walk_best ∧
        sK.scratch.last_learned = s.scratch.last_learned ∧
        sK.scratch.scratch_buf = s.scratch.scratch_buf ∧
        sK.core.lit_mark = s.core.lit_mark ∧ sK.core.mrk = s.core.mrk ∧
        (FullMem c sK ⋆ R) mK)
      (fun (k, ()) _ => nb.toNat - k.toNat)
      (fun Jk hLoopK => by
        c0_hsteps_nogrp
        refine hLoopK (0#64, ()) _ ⟨Nat.zero_le _, s0, hlen0, hw0, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, ?_⟩
        let wstk0_c0 := s.core.wstk.set (BitVec.setWidth 64 0#32).toNat 0#32
        let s0_c0 : FullState :=
          { s with core := { s.core with wvec := wvecL, wstk := wstk0_c0,
                                         wlen := (1#64).toNat, wusable := 0#64, num_binary := nb } }
        change (FullMem c s0_c0 ⋆ R) _ at *; exact (by assumption))
      (fun Jk ⟨k, ⟨⟩⟩ mK ⟨hk_le, sK, hlenK, hwK, hcvK, hclK, hdmK, harK, halK, hvalK, hlvlK,
          hflK, hfuK, hincK, hdcK, hdvK, hftK, hfdK, hteK, hprK, hprbK, helK, hwvK, hwbK, hllK,
          hsbK, hlmkK, hmrkK, hmK⟩ hLoopK => ?_)
    c0_hsplit
    · have hk_lt : k.toNat < nb.toNat := hc
      have hnb_bd : 2 * nb.toNat ≤ c.scratch_cap := hbp.2.1
      have hsc_cap := c.hscr; unfold dimacsBound at hsc_cap
      have hsc_len : sK.scratch.scratch_buf.length = c.scratch_cap :=
        hlenK.scratch_ok.scratch_buf_len
      have hk0 : (k <<< 1#64).toNat = 2 * k.toNat := by
        rw [show k <<< 1#64 = k <<< (1 : Nat) from rfl, BitVec.toNat_shiftLeft,
          Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]; omega
      have hk1 : ((k <<< 1#64) + 1#64).toNat = 2 * k.toNat + 1 := by
        rw [BitVec.toNat_add, hk0, show (1#64 : BitVec 64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      have ha_lt : (k <<< 1#64).toNat < sK.scratch.scratch_buf.length := by omega
      have hb_lt : ((k <<< 1#64) + 1#64).toNat < sK.scratch.scratch_buf.length := by omega
      obtain ⟨hpa, hpb, hpent⟩ := hbp.2.2 k.toNat hk_lt
      have hk0_gen : (k <<< OfNat.ofNat 1).toNat = 2 * k.toNat := by
        rw [show (k <<< OfNat.ofNat 1) = k <<< 1#64 from rfl, hk0]
      have hk1_gen : (k <<< OfNat.ofNat 1 + (1 : BitVec 64)).toNat = 2 * k.toNat + 1 := by
        rw [show (k <<< OfNat.ofNat 1) = k <<< 1#64 from rfl,
          show (1 : BitVec 64) = 1#64 from rfl, hk1]
      have hsc_get : ∀ (sX : FullState) (hsX : sX.scratch.scratch_buf = s.scratch.scratch_buf)
          (idx mIdx : Nat) (hEq : idx = mIdx) (hBd : idx < sX.scratch.scratch_buf.length),
          sX.scratch.scratch_buf[idx]'hBd = s.scratch.scratch_buf[mIdx]?.getD 0#32 := by
        intro sX hsX idx mIdx hEq hBd
        have hBd' : mIdx < s.scratch.scratch_buf.length := by rw [← hsX, ← hEq]; exact hBd
        rw [List.getElem?_eq_getElem hBd', Option.getD_some]
        apply Option.some.inj
        rw [← List.getElem?_eq_getElem hBd, ← List.getElem?_eq_getElem hBd', hsX, hEq]
      have ha_k : ∀ (hBd : (k <<< OfNat.ofNat 1).toNat < sK.scratch.scratch_buf.length),
          sK.scratch.scratch_buf[(k <<< OfNat.ofNat 1).toNat]'hBd =
          s.scratch.scratch_buf[2 * k.toNat]?.getD 0#32 :=
        fun hBd => hsc_get sK hsbK _ _ hk0_gen hBd
      have hb_k : ∀ (hBd : (k <<< OfNat.ofNat 1 + (1 : BitVec 64)).toNat <
          sK.scratch.scratch_buf.length),
          sK.scratch.scratch_buf[(k <<< OfNat.ofNat 1 + (1 : BitVec 64)).toNat]'hBd =
          s.scratch.scratch_buf[2 * k.toNat + 1]?.getD 0#32 :=
        fun hBd => hsc_get sK hsbK _ _ hk1_gen hBd
      have hkn : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
      have hpent_sw : (cnfOfClauses F_cur).EntailsClause (cnfClause
          [(s.scratch.scratch_buf[2 * k.toNat + 1]?.getD 0#32).toNat,
           (s.scratch.scratch_buf[2 * k.toNat]?.getD 0#32).toNat]) := by
        rw [CNF.entails_clause_def] at hpent ⊢
        intro α hα
        have h1 := hpent α hα
        rw [clause_sat_cnfClause_iff] at h1 ⊢
        obtain ⟨lit, hlit, hs⟩ := h1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hlit
        exact ⟨lit, by rcases hlit with rfl | rfl <;> simp, hs⟩
      c0_hsteps_nogrp
      refine s13_bin_roundtrip_call_push hPush hlenK hwK
        (by rw [ha_k, hcvK]; exact hpa)
        (by rw [hb_k, hcvK]; exact hpb)
        (by rw [hb_k]; omega)
        (by rw [ha_k, hb_k]; exact hpent) hmK ?_
      intro _ok1 sK1 mK1 hlenK1 hwK1 hcvK1 hclK1 hdmK1 harK1 halK1 hvalK1 hlvlK1 hflK1 hfuK1
        hincK1 hdcK1 hdvK1 hftK1 hfdK1 hteK1 hprK1 hprbK1 helK1 hwvK1 hwbK1 hllK1 hsbK1 hlmkK1
        hmrkK1 hmK1
      c0_hsteps_nogrp
      refine s13_bin_roundtrip_call_push hPush hlenK1 hwK1
        (by rw [hb_k, hcvK1, hcvK]; exact hpb)
        (by rw [ha_k, hcvK1, hcvK]; exact hpa)
        (by rw [ha_k]; omega)
        (by rw [ha_k, hb_k]; exact hpent_sw)
        hmK1 ?_
      intro _ok2 sK2 mK2 hlenK2 hwK2 hcvK2 hclK2 hdmK2 harK2 halK2 hvalK2 hlvlK2 hflK2 hfuK2
        hincK2 hdcK2 hdvK2 hftK2 hfdK2 hteK2 hprK2 hprbK2 helK2 hwvK2 hwbK2 hllK2 hsbK2 hlmkK2
        hmrkK2 hmK2
      c0_hsteps_nogrp
      exact hLoopK (k + 1#64, ()) mK2 (by dsimp only; omega)
        ⟨by omega, sK2, hlenK2, hwK2,
         hcvK2.trans (hcvK1.trans hcvK), hclK2.trans (hclK1.trans hclK),
         hdmK2.trans (hdmK1.trans hdmK), harK2.trans (harK1.trans harK),
         halK2.trans (halK1.trans halK), hvalK2.trans (hvalK1.trans hvalK),
         hlvlK2.trans (hlvlK1.trans hlvlK), hflK2.trans (hflK1.trans hflK),
         hfuK2.trans (hfuK1.trans hfuK), hincK2.trans (hincK1.trans hincK),
         hdcK2.trans (hdcK1.trans hdcK), hdvK2.trans (hdvK1.trans hdvK),
         hftK2.trans (hftK1.trans hftK), hfdK2.trans (hfdK1.trans hfdK),
         hteK2.trans (hteK1.trans hteK), hprK2.trans (hprK1.trans hprK),
         hprbK2.trans (hprbK1.trans hprbK), helK2.trans (helK1.trans helK),
         hwvK2.trans (hwvK1.trans hwvK), hwbK2.trans (hwbK1.trans hwbK),
         hllK2.trans (hllK1.trans hllK), hsbK2.trans (hsbK1.trans hsbK),
         hlmkK2.trans (hlmkK1.trans hlmkK), hmrkK2.trans (hmrkK1.trans hmrkK), hmK2⟩
    · c0_hsteps_nogrp
      have hlmK : FullLitMarksClear c sK :=
        ⟨by simpa only [FullMrkZero, hmrkK] using hlm.1,
          fun l hl => by rw [hlmkK]; exact hlm.2 l hl⟩
      have hndK : FullArenaVarsNodup sK := by
        simpa [FullArenaVarsNodup, fullArenaClauseRefs, fullArenaClauseRefsCore,
          fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore, fullArenaClauseLits,
          fullArenaClauseLitsCore, fullArenaClauseSizeCore, harK, halK] using hnd
      have hextK : FullExtScratchOk c sK :=
        FullExtScratchOk.of_pres hext ⟨hllK, by omega⟩
          fun r hr => by
            simpa [fullArenaClauseRefs, fullArenaClauseRefsCore, harK, halK] using hr
      exact hExit sK mK hlenK hwK hlmK hndK hextK
        hcvK hclK hdmK harK halK hvalK hlvlK hflK hfuK hincK hdcK hdvK hftK hfdK hteK hprK hprbK
        helK hwvK hwbK hllK hmK

end LeanQbe.T.Examples.Kissat.Proof.Forward
