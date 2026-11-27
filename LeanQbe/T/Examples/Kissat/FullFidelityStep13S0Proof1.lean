/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S0Proof0
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullParseInitLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step-13 Shard `S0` Header & Watermark Proofs (`FullFidelityStep13S0Proof1`)

Parametric `(Γ : Env)` WP proofs (`0` `import all`, `public section`, `0` `@[expose]` on
theorems, `std3`, `XPost`-polymorphic) for the remaining `5` `S0` functions (`2` ADD + `3` MOD):
1. `m6_wm4_get` (`m6Wm4GetSpec`)
2. `m6_wm4_set` (`m6HdrW2aSpec [i64] []`)
3. `m6_hdr_init` (`m6HdrInitSpec`)
4. `m6_hdr_recompute_tiers_mode` (`m6HdrW2aSpec [i64] []`, calling soft-float `f64u_*`)
5. `full_init_hdr` (`Full.fullInitHdrSpec`, Step-13 f64u/init-constant updates)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S0

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.Full.FullParseInitSpecs
open LeanQbe.T.Examples.Kissat.Full.FullParseInitHelpers
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullParseInitTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics
open Kraken.Bedrock2.Test

private theorem bv64_add_small_s0 {k x : BitVec 64} {n : Nat} (hk : k.toNat = n)
    (hsum : n + x.toNat < 2 ^ 64) : (k + x).toNat = n + x.toNat := by
  rw [BitVec.toNat_add, hk, Nat.mod_eq_of_lt hsum]

private theorem bv64_add_toNat_small_s0 {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

private theorem bv64_add1_toNat_s0 {g : BitVec 64} (h : g.toNat + 1 < 2 ^ 64) :
    (g + 1).toNat = g.toNat + 1 := by
  rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem w2a_pres_of_init_s0 {ext ext1 ext' : List (BitVec 64)}
    (h1 : M6HdrExtInitOk ext → ext1 = ext) (h2 : M6HdrExtInitOk ext')
    (h3 : M6ExtW2bPres ext1 ext') :
    M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext' :=
  fun hi => ⟨h2, (h1 hi) ▸ h3⟩

/-! ## 1. Watermark-4 & `M6HdrExt` Proofs (`4` Functions) -/

@[expose]
def m6Wm4GetSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧ ∀ r : BitVec 64, Q (r, ()) m

theorem m6Wm4GetSpec_xfree : m6Wm4GetSpec.XFree := by xfree

theorem m6Wm4GetSpec_le_w2a : (m6HdrW2aSpec [] [i64]).Le m6Wm4GetSpec := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  exact ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, fun r =>
    hQ (r, ()) ext s m rfl hlen (M6HdrScratchPres.refl s) hext
      (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) hm⟩

theorem has_m6Wm4Get_to_w2a {Γ : Env} (h : Γ.Has "m6_wm4_get" m6Wm4GetSpec) :
    Γ.Has "m6_wm4_get" (m6HdrW2aSpec [] [i64]) :=
  Env.Has.of_le h m6Wm4GetSpec_le_w2a

theorem m6_wm4_get_s13_wp (Γ : Env) :
    ∀ a m Q X, m6Wm4GetSpec a m Q X → Func.wp Γ m6_wm4_get_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩
  have h0 : (0 : BitVec 64).toNat < ext.length := by rw [hext.len]; decide
  have h28 : (28 : BitVec 64).toNat < ext.length := by rw [hext.len]; decide
  rw [fullM6HdrMem_iff] at hm
  unfold Func.wp m6_wm4_get_body
  c0_hsteps <;> exact hQ _

theorem m6_wm4_get_s13_w2a_wp (Γ : Env) :
    ∀ a m Q X, m6HdrW2aSpec [] [i64] a m Q X → Func.wp Γ m6_wm4_get_body a m Q X :=
  fun _ _ _ _ hs => m6_wm4_get_s13_wp Γ _ _ _ _ (m6Wm4GetSpec_le_w2a _ _ _ _ hs)

theorem m6_wm4_set_s13_wp (Γ : Env) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X → Func.wp Γ m6_wm4_set_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  have h0 : (0 : BitVec 64).toNat < ext.length := by rw [hext.len]; decide
  have h28 : (28 : BitVec 64).toNat < ext.length := by rw [hext.len]; decide
  have hl0 : ext.length = 288 := hext.len
  rw [fullM6HdrMem_iff] at hm
  unfold Func.wp m6_wm4_set_body
  c0_hsteps
  · exact hQ () ext s _ rfl hlen (M6HdrScratchPres.refl s) hext
      (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) ((fullM6HdrMem_iff ..).mpr hm)
  · let ext2 := ext.set 28 v
    have hext2 : M6HdrExtOk ext2 := M6HdrExtOk.of_len (by simp [ext2, hl0])
    have hw2 : M6HdrExtInitOk ext → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext ext2 :=
      fun hi => ⟨hi.set_pos v (by decide), M6ExtW2bPres.set_ge8 v (by decide)⟩
    exact hQ () ext2 s _ rfl hlen (M6HdrScratchPres.refl s) hext2 hw2
      ((fullM6HdrMem_iff ..).mpr (by assumption))

/-- Identical exposed copy of `FullM6Hdr.m6HdrInitSpec` (`m6HdrInitSpec` in
`FullM6HdrProof0.lean` lacks `@[expose]` and `_elim`, so `0 import all` Wave-1 proof shards
prove `m6_hdr_init` against `s13M6HdrInitSpec` without busting the upstream cache). -/
@[expose]
def s13M6HdrInitSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ ext' m', ext'.length = fullM6ExtWords → ext'[0]? = some fullM6HdrMagic →
      (FullM6HdrMem c ext' s ⋆ R) m' → Q () m'

theorem s13M6HdrInitSpec_xfree : s13M6HdrInitSpec.XFree := by xfree

theorem s13M6HdrInitSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : s13M6HdrInitSpec xs m Q X) : s13M6HdrInitSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem s13M6HdrInitSpec_to_m6Hdr {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X : XPost}
    (h : s13M6HdrInitSpec xs m Q X) : m6HdrInitSpec xs m Q X := by
  rcases xs with ⟨_, ⟨⟩⟩
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := h
  exact m6HdrInitSpec_of hcfg hext hlen hm fun ext' m' hi hm' =>
    hQ ext' m' hi.toOk.len hi.magic hm'

theorem m6_hdr_init_s13_wp (Γ : Env) :
    ∀ a m Q X, s13M6HdrInitSpec a m Q X → Func.wp Γ m6_hdr_init_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩
  rw [fullM6HdrMem_iff] at hm
  unfold Func.wp m6_hdr_init_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (i, ()) m1 => i.toNat ≤ 288 ∧ ∃ ext1 : List (BitVec 64),
      ext1.length = 288 ∧ (FullMem c s ⋆ (array64 (c.hdr - 2304) ext1 ⋆ R)) m1)
    (fun (i, ()) _ => 288 - i.toNat)
    (fun L hL => by c0_hsteps; exact hL (0#64, ()) m ⟨by simp, ext, hext.len, hm⟩)
    (fun L (i, ()) m1 ⟨hi_le, ext1, hl1, hm1⟩ ih => ?_)
  c0_hsteps
  · have hi_lt : i.toNat < 288 := by c0_bound
    have hi_len : i.toNat < ext1.length := by rw [hl1]; exact hi_lt
    c0_hsteps
    exact ih _ _ (by c0_bound) ⟨by c0_bound, ext1.set i.toNat 0, by simp [hl1], by assumption⟩
  · have h288 : ext1.length = 288 := hl1
    c0_hsteps
    refine hQ _ _ ?_ ?_ ((fullM6HdrMem_iff ..).mpr hm)
    · simp only [List.length_set, h288, fullM6ExtWords]
    · rw [show (0 : BitVec 64).toNat = 0 from rfl,
        List.getElem?_set_self (by simp only [List.length_set, h288]; omega)]
      rfl

theorem m6_hdr_recompute_tiers_mode_s13_wp (Γ : Env)
    (hEnsure : Γ.Has "m6_ext_ensure_init" m6ExtEnsureInitSpec)
    (hSync : Γ.Has "m6_hdr_sync_legacy_tiers" (m6HdrW2aSpec [] []))
    (hFrom : Γ.Has "f64u_from_u64" f64uPure1Spec)
    (hMul : Γ.Has "f64u_mul" f64uPure2Spec)
    (hTo : Γ.Has "f64u_to_u64" f64uPure1Spec) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Func.wp Γ m6_hdr_recompute_tiers_mode_body a m Q X := by
  rintro ⟨h, st, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp m6_hdr_recompute_tiers_mode_body
  c0_hsteps_nogrp
  refine LeanQbe.T.wp_call_of_spec _ _ (hEnsure _ _ _ _ ?_)
  refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
  have hl1 : ext1.length = 288 := hinit1.toOk.len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (mode, ()) m2 => m2 = m1 ∧ (mode = 0#64 ∨ mode = 1#64))
    (fun _ (mode, ()) m2 ⟨hm2, hmode⟩ => ?_)
    (fun _ hJm => by
      c0_hsteps
      · exact hJm (1#64, ()) m1 ⟨rfl, Or.inr rfl⟩
      · exact hJm (0#64, ()) m1 ⟨rfl, Or.inl rfl⟩)
  subst m2
  have hmode_le : mode.toNat ≤ 1 := by rcases hmode with rfl | rfl <;> decide
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (base, ()) m2 => m2 = m1 ∧ (base = 32#64 ∨ base = 160#64))
    (fun _ (base, ()) m2 ⟨hm2, hbase⟩ => ?_)
    (fun _ hJb => by
      c0_hsteps
      · exact hJb (32#64, ()) m1 ⟨rfl, Or.inl rfl⟩
      · exact hJb (160#64, ()) m1 ⟨rfl, Or.inr rfl⟩)
  subst m2
  have hbase_le : base.toNat ≤ 160 := by rcases hbase with rfl | rfl <;> decide
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64, i64])
    (fun (_tot, g, ()) mL => g.toNat ≤ 128 ∧ mL = m1)
    (fun (_, g, ()) _ => 128 - g.toNat)
    (fun Jl hJl => by c0_hsteps; exact hJl (0#64, 0#64, ()) m1 ⟨by decide, rfl⟩)
    (fun Jl (tot, g, ()) mL ⟨hg128, hmL⟩ ih => ?_)
  subst mL
  c0_hsteps_nogrp
  · have hg_lt : g.toNat < 128 := by
      have h128 : (128 : BitVec 64).toNat = 128 := rfl; omega
    have hidx : (base + g).toNat < ext1.length := by
      rw [hl1, bv64_add_toNat_small_s0 (by omega)]; omega
    have hg1 : (g + 1).toNat = g.toNat + 1 := bv64_add1_toNat_s0 (by omega)
    c0_hsteps
    all_goals exact ih (_, g + 1, ()) m1 (by dsimp only; omega) ⟨by omega, rfl⟩
  · have htu_idx : ((14 : BitVec 64) + mode).toNat = 14 + mode.toNat :=
      bv64_add_small_s0 (n := 14) rfl (by omega)
    have htu_lt : ((14 : BitVec 64) + mode).toNat < ext1.length := by rw [hl1, htu_idx]; omega
    c0_hsteps_nogrp
    let ext2 := ext1.set ((14 : BitVec 64) + mode).toNat tot
    have hl2 : ext2.length = 288 := by simp [ext2, hl1]
    have hinit2 : M6HdrExtInitOk ext2 := hinit1.set_pos tot (by rw [htu_idx]; omega)
    have hw2 : M6ExtW2bPres ext1 ext2 := M6ExtW2bPres.set_ge8 tot (by rw [htu_idx]; omega)
    let m2 := m
    have hm2 : (FullMem c s ⋆ (array64 (c.hdr - 2304) ext2 ⋆ R)) m2 := hm
    refine wp_join_group (ts := [i64, i64, i64]) (fun _ m3 => m3 = m2)
      (fun _ (_g', t1, t2, ()) m3 hm3 => ?_) ?_
    · subst m3
      refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = m2)
        (fun _ (t2c, ()) m3 hm3 => ?_) ?_
      · subst m3
        have ht1_idx : ((8 : BitVec 64) + mode).toNat = 8 + mode.toNat :=
          bv64_add_small_s0 (n := 8) rfl (by omega)
        have ht2_idx : ((10 : BitVec 64) + mode).toNat = 10 + mode.toNat :=
          bv64_add_small_s0 (n := 10) rfl (by omega)
        have ht1_lt : ((8 : BitVec 64) + mode).toNat < ext2.length := by rw [hl2, ht1_idx]; omega
        have ht2_lt : ((10 : BitVec 64) + mode).toNat <
            (ext2.set ((8 : BitVec 64) + mode).toNat t1).length := by
          rw [List.length_set, hl2, ht2_idx]; omega
        c0_hsteps_nogrp
        let ext3 := (ext2.set ((8 : BitVec 64) + mode).toNat t1).set
          ((10 : BitVec 64) + mode).toNat t2c
        have hinit3 : M6HdrExtInitOk ext3 :=
          (hinit2.set_pos t1 (by rw [ht1_idx]; omega)).set_pos t2c (by rw [ht2_idx]; omega)
        have hw3 : M6ExtW2bPres ext1 ext3 :=
          hw2.trans ((M6ExtW2bPres.set_ge8 t1 (by rw [ht1_idx]; omega)).trans
            (M6ExtW2bPres.set_ge8 t2c (by rw [ht2_idx]; omega)))
        refine LeanQbe.T.wp_call_of_spec _ _ (hSync _ _ _ _ ?_)
        refine m6HdrW2aSpec_of rfl hcfg hinit3.toOk hlen
          ((fullM6HdrMem_iff ..).mpr (by assumption))
          fun () ext4 s4 m4 hcore4 hlen4 hpres4 hok4 hw4 hm4 => ?_
        have ⟨hinit4, hw34⟩ := hw4 hinit3
        exact hQ () ext4 s4 m4 hcore4 hlen4 hpres4 hok4
          (w2a_pres_of_init_s0 hpres1 hinit4 (hw3.trans hw34)) hm4
      · intro _ hJt2c; c0_hsteps <;> exact hJt2c (_, ()) m2 rfl
    · intro _ hJt; c0_hsteps_nogrp
      · refine LeanQbe.T.wp_call_of_spec _ _ (hFrom _ _ _ _ fun tf => ?_)
        c0_hsteps_nogrp
        refine LeanQbe.T.wp_call_of_spec _ _ (hMul _ _ _ _ fun tm => ?_)
        c0_hsteps_nogrp
        refine LeanQbe.T.wp_call_of_spec _ _ (hTo _ _ _ _ fun lim2 => ?_)
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64, i64, i64, i64, .bool, .bool])
          (fun _ m5 => m5 = m2)
          (fun _ (_g', _t1, _t2, _acc, _g1, _g2, ()) m5 hm5 => by
            subst m5; c0_hsteps <;> exact hJt (_, _, _, ()) m2 rfl)
          ?_
        intro _ hJb
        c0_hsteps_nogrp
        refine wp_loop_inv (ts := [i64, i64, i64, .bool])
          (fun (g, _t1, _acc, _g1, ()) mL => g.toNat ≤ 128 ∧ mL = m2)
          (fun (g, _, _, _, ()) _ => 128 - g.toNat)
          (fun Ja hJa => by c0_hsteps; exact hJa (0#64, _, _, _, ()) m2 ⟨by decide, rfl⟩)
          (fun Ja (g, t1, acc, g1, ()) mL ⟨hg128', hmL⟩ ih2 => ?_)
        subst mL
        c0_hsteps_nogrp
        · have hg_lt : g.toNat < 128 := by
            have h128 : (128 : BitVec 64).toNat = 128 := rfl; omega
          have hidx2 : (base + g).toNat < ext2.length := by
            rw [hl2, bv64_add_toNat_small_s0 (by omega)]; omega
          have hg1 : (g + 1).toNat = g.toNat + 1 := bv64_add1_toNat_s0 (by omega)
          c0_hsteps
          all_goals
            try exact ih2 (g + 1, _, _, _, ()) m2 (by dsimp only; omega) ⟨by omega, rfl⟩
          all_goals (c0_hsteps; exact hJb (_, _, _, _, _, _, ()) m2 rfl)
        · c0_hsteps <;> exact hJb (_, _, _, _, _, _, ()) m2 rfl
      · exact hJt (_, _, _, ()) m2 rfl

/-! ## 2. Step-13 `full_init_hdr` Proof (`Full.fullInitHdrSpec`) -/

private def s13HdrW0 (fuel : BitVec 64) (w0 : List (BitVec 64)) : List (BitVec 64) :=
  ((((((((((((((((w0.set 2 0#64).set 3 1#64).set 14 0#64).set 15 0#64).set 16 0#64).set
    17 fuel).set 18 0xFFFFFFFF#64).set 19 0#64).set 20 0#64).set
    27 0#64).set 28 0x3FF0000000000000#64).set 30 0#64).set 31 0#64).set
    32 1024#64).set 33 1048576#64).set 34 1024#64)

private def s13HdrW1 (w1 : List (BitVec 64)) : List (BitVec 64) :=
  ((((((((((((((((((((((w1.set 18 0#64).set 19 0#64).set 20 0#64).set
    21 0xFFFFFFFF#64).set 22 0#64).set 23 0#64).set 24 0#64).set 25 0#64).set
    26 0#64).set 27 0#64).set 28 0#64).set 29 0#64).set 0 1#64).set 1 1#64).set
    2 0#64).set 3 0#64).set 4 0#64).set 5 0#64).set 30 0#64).set 31 0#64).set
    32 0#64).set 33 1000#64).set 34 0#64

private def s13HdrW2 (mv max_v : Nat) (w2 : List (BitVec 64)) : List (BitVec 64) :=
  (((((((((((((((((((((((((w2.set 22 (BitVec.ofNat 64 max_v)).set
    23 (BitVec.ofNat 64 mv)).set 24 (BitVec.ofNat 64 (max_v - mv))).set
    25 0#64).set 0 0#64).set 1 0#64).set 2 0xFFFFFFFF#64).set 3 0xFFFFFFFF#64).set
    4 0xFFFFFFFF#64).set 5 0#64).set 6 0#64).set 7 0#64).set 8 0#64).set
    9 1000#64).set 10 0#64).set 11 1000#64).set 12 0#64).set 13 2#64).set 14 6#64).set
    15 0#64).set 16 1#64).set 17 0#64).set 18 0x3FF0000000000000#64).set 19 0#64).set
    20 0x3FF0000000000000#64).set 21 0#64

private def s13HdrW3 (mv : Nat) (w3 : List (BitVec 64)) : List (BitVec 64) :=
  let rng := 0x9E3779B97F4A7C15#64 ^^^ (BitVec.ofNat 64 mv + 1#64)
  ((((((((((((((((((((((((((w3.set 5 0#64).set 9 rng).set 10 100#64).set 11 0#64).set
    12 0#64).set 13 2000#64).set 14 0#64).set 15 5000#64).set 16 0#64).set 17 0#64).set
    18 0#64).set 19 0#64).set 20 0#64).set 21 0#64).set 22 0#64).set 23 0#64).set
    24 0#64).set 25 0#64).set 26 0#64).set 27 0#64).set 28 0#64).set 29 0#64).set
    30 0#64).set 31 0#64).set 32 0#64).set 33 0#64).set 34 0#64

@[local simp] private theorem s13HdrW0_len {fu : BitVec 64} {w : List (BitVec 64)} :
    (s13HdrW0 fu w).length = w.length := by simp [s13HdrW0]
@[local simp] private theorem s13HdrW1_len {w : List (BitVec 64)} :
    (s13HdrW1 w).length = w.length := by simp [s13HdrW1]
@[local simp] private theorem s13HdrW2_len {mv mx : Nat} {w : List (BitVec 64)} :
    (s13HdrW2 mv mx w).length = w.length := by simp [s13HdrW2]
@[local simp] private theorem s13HdrW3_len {mv : Nat} {w : List (BitVec 64)} :
    (s13HdrW3 mv w).length = w.length := by simp [s13HdrW3]

private def s13InitHdrWitness (c : FullCfg) (fuel : BitVec 64) : FullState :=
  { core :=
      { d_cur := 0#64, d_val := 0#64, cur_vars := c.mv, unassigned := 0#64
        arena_len := 0, wlen := 1, wusable := 0#64, arena_garbage := 0#64
        first_reducible := 0xFFFFFFFF#64, num_irred := 0#64, num_redundant := 0#64,
        num_binary := 0#64
        unflushed := 0#64, probing := 0#64, trail_end := 0, propagated := 0, cur_level := 0
        fuel := fuel, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64, confl_lit0 := 0#64
        confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0, min_clr_len := 0, min_clr_full := 0#64
        oom := 0#64, dense_mode := 0#64, inconsistent := 0#64
        vals := [], lit_mark := [], mrk := [], flags := [], lvl := [], rsns := [], trl := []
        trail_pos := [], tmp := [], min_clr := [], frame_trail := [], frame_dec := [], wvec := []
        repr := [], min_stk := [], arena := [], wstk := [] }
    scratch :=
      { heap_len := 0, scinc := 0x3FF0000000000000#64, rel_period := 1024#64
        rel_limit := 1048576#64, rel_wait := 1024#64, rel_u := 1#64, rel_v := 1#64
        rel_trigger := 0#64, conflicts := 0#64, learned_lits := 0#64, min_removed := 0#64
        delayed_len := 0, stable := 0#64, switched := 0#64, mode_count := 0#64
        mode_confl_lim := 1000#64, mode_tick_lim := 0#64, mode_saved_ticks := 0#64
        search_ticks := 0#64, q_first := 0xFFFFFFFF#64, q_last := 0xFFFFFFFF#64
        q_search_idx := 0xFFFFFFFF#64, q_search_stamp := 0#64, q_cur_stamp := 0#64
        target_assigned := 0#64, best_assigned := 0#64, rephase_limit := 1000#64
        rephased := 0#64, reduce_limit := 1000#64, reductions := 0#64, tier1 := 2#64
        tier2 := 6#64, restarts := 0#64, restart_limit := 1#64, ema_fast_biased := 0#64
        ema_fast_exp := 0x3FF0000000000000#64, ema_slow_biased := 0#64
        ema_slow_exp := 0x3FF0000000000000#64, extend_len := 0
        rng_state := 0x9E3779B97F4A7C15#64 ^^^ (BitVec.ofNat 64 c.mv + 1#64)
        chrono_levels := 100#64, otfs_cnt := 0#64, eager_sub_cnt := 0#64, probe_limit := 2000#64
        probings := 0#64, elim_limit := 5000#64, eliminations := 0#64, elim_bound := 0#64
        iterating := 0#64, hbr_cnt := 0#64, trans_cnt := 0#64, viv_cnt := 0#64, subst_cnt := 0#64
        cong_cnt := 0#64, sweep_cnt := 0#64, bve_cnt := 0#64, bce_cnt := 0#64, bva_cnt := 0#64
        walk_cnt_stat := 0#64, fwd_sub_cnt := 0#64, fwd_str_cnt := 0#64, ant_sz := 0#64
        res_sz := 0#64, walk_vals := [], phases := [], phases_target := [], phases_best := []
        walk_best := [], heap := [], pos := [], shrink_stk := [], q_prev := [], q_next := []
        q_stamp := [], wsort := [], work_stk1 := [], work_stk2 := [], tarjan_mark := []
        tarjan_reach := [], score := [], sim_sig := [], glue_used := [], last_learned := []
        delayed := [], red_refs := [], extend_stk := [], scratch_buf := [] } }

private theorem len_cons10_s0 {α : Type} (xs : List α) (n : Nat) (h : xs.length = n + 10) :
    ∃ a b c d e f g h1 i j ys, ys.length = n ∧
      xs = a :: b :: c :: d :: e :: f :: g :: h1 :: i :: j :: ys := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h1, _ | ⟨i, _ |
    ⟨j, ys⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨a, b, c, d, e, f, g, h1, i, j, ys, h, rfl⟩

private theorem decompose35_s0 {α : Type} (xs : List α) (h : xs.length = 35) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 d0 d1 d2 d3 d4,
      xs = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
        c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4] := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, xs1, h1, rfl⟩ := len_cons10_s0 xs 25 h
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, xs2, h2, rfl⟩ := len_cons10_s0 xs1 15 h1
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, xs3, h3, rfl⟩ := len_cons10_s0 xs2 5 h2
  rcases xs3 with _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, _ | ⟨d3, _ | ⟨d4, _ | _⟩⟩⟩⟩⟩ <;> simp at h3
  exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩

private theorem s13HdrW0_eq (c : FullCfg) (fuel : BitVec 64) (w0 : List (BitVec 64))
    (h0 : w0.length = 35)
    (hw : ∀ i ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29],
      w0[i]? = (hdrTailWords0 c (s13InitHdrWitness c fuel))[i]?) :
    s13HdrW0 fuel w0 = hdrTailWords0 c (s13InitHdrWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35_s0 w0 h0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e0 := hw 0 (by simp); have e1 := hw 1 (by simp); have e4 := hw 4 (by simp)
  have e5 := hw 5 (by simp); have e6 := hw 6 (by simp); have e7 := hw 7 (by simp)
  have e8 := hw 8 (by simp); have e9 := hw 9 (by simp); have e10 := hw 10 (by simp)
  have e11 := hw 11 (by simp); have e12 := hw 12 (by simp); have e13 := hw 13 (by simp)
  have e21 := hw 21 (by simp); have e22 := hw 22 (by simp); have e23 := hw 23 (by simp)
  have e24 := hw 24 (by simp); have e25 := hw 25 (by simp); have e26 := hw 26 (by simp)
  have e29 := hw 29 (by simp)
  simp only [hdrTailWords0, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
    at e0 e1 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e21 e22 e23 e24 e25 e26 e29
  simp [s13HdrW0, hdrTailWords0, s13InitHdrWitness, e0, e1, e4, e5, e6, e7, e8, e9, e10, e11,
    e12, e13, e21, e22, e23, e24, e25, e26, e29]

private theorem s13HdrW1_eq (c : FullCfg) (fuel : BitVec 64) (w1 : List (BitVec 64))
    (h1 : w1.length = 35)
    (hw : ∀ i ∈ [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
      w1[i]? = (hdrTailWords1 c (s13InitHdrWitness c fuel))[i]?) :
    s13HdrW1 w1 = hdrTailWords1 c (s13InitHdrWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35_s0 w1 h1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e6 := hw 6 (by simp); have e7 := hw 7 (by simp); have e8 := hw 8 (by simp)
  have e9 := hw 9 (by simp); have e10 := hw 10 (by simp); have e11 := hw 11 (by simp)
  have e12 := hw 12 (by simp); have e13 := hw 13 (by simp); have e14 := hw 14 (by simp)
  have e15 := hw 15 (by simp); have e16 := hw 16 (by simp); have e17 := hw 17 (by simp)
  simp only [hdrTailWords1, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
    at e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
  simp [s13HdrW1, hdrTailWords1, s13InitHdrWitness, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15,
    e16, e17]

private theorem s13HdrW2_eq (c : FullCfg) (fuel : BitVec 64) (w2 : List (BitVec 64))
    (h2 : w2.length = 35)
    (hw : ∀ i ∈ [26, 27, 28, 29, 30, 31, 32, 33, 34],
      w2[i]? = (hdrTailWords2 c (s13InitHdrWitness c fuel))[i]?) :
    s13HdrW2 c.mv c.max_vars w2 = hdrTailWords2 c (s13InitHdrWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35_s0 w2 h2
  have hbva : c.max_vars - c.mv = c.bva_cap := by have := c.hbva; omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e26 := hw 26 (by simp); have e27 := hw 27 (by simp); have e28 := hw 28 (by simp)
  have e29 := hw 29 (by simp); have e30 := hw 30 (by simp); have e31 := hw 31 (by simp)
  have e32 := hw 32 (by simp); have e33 := hw 33 (by simp); have e34 := hw 34 (by simp)
  simp only [hdrTailWords2, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
    at e26 e27 e28 e29 e30 e31 e32 e33 e34
  simp [s13HdrW2, hdrTailWords2, s13InitHdrWitness, hbva, e26, e27, e28, e29, e30, e31, e32,
    e33, e34]

private theorem s13HdrW3_eq (c : FullCfg) (fuel : BitVec 64) (w3 : List (BitVec 64))
    (h3 : w3.length = 35)
    (hw : ∀ i ∈ [0, 1, 2, 3, 4, 6, 7, 8],
      w3[i]? = (hdrTailWords3 c (s13InitHdrWitness c fuel))[i]?) :
    s13HdrW3 c.mv w3 = hdrTailWords3 c (s13InitHdrWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35_s0 w3 h3
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e0 := hw 0 (by simp); have e1 := hw 1 (by simp); have e2 := hw 2 (by simp)
  have e3 := hw 3 (by simp); have e4 := hw 4 (by simp); have e6 := hw 6 (by simp)
  have e7 := hw 7 (by simp); have e8 := hw 8 (by simp)
  simp only [hdrTailWords3, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq]
    at e0 e1 e2 e3 e4 e6 e7 e8
  simp [s13HdrW3, hdrTailWords3, s13InitHdrWitness, e0, e1, e2, e3, e4, e6, e7, e8]

theorem full_init_hdr_s13_wp (Γ : Env) :
    ∀ a m Q X, Full.fullInitHdrSpec a m Q X → Func.wp Γ full_init_hdr_body a m Q X := by
  rintro ⟨h, mv, max_v, fuel, ⟨⟩⟩ m Q X ⟨c, ws, R, rfl, rfl, rfl, hw, hws, hm, hQ⟩
  let s0 := s13InitHdrWitness c fuel
  have hws0 := hws s0
  have hmv' := c.hmv; have hmx' := c.hmaxv; unfold dimacsBound at hmv' hmx'
  have hmv_to : (BitVec.ofNat 64 c.mv).toNat = c.mv := bv64_ofNat_toNat (by omega)
  have hmx_to : (BitVec.ofNat 64 c.max_vars).toNat = c.max_vars := bv64_ofNat_toNat (by omega)
  let w0 := ws.take 35; let w1 := (ws.drop 35).take 35
  let w2 := (ws.drop 70).take 35; let w3 := (ws.drop 105).take 35
  have h0l : w0.length = 35 := by simp [w0, hw]
  have h1l : w1.length = 35 := by simp [w1, hw]
  have h2l : w2.length = 35 := by simp [w2, hw]
  have h3l : w3.length = 35 := by simp [w3, hw]
  have hw_len0 : (hdrTailWords0 c s0).length = 35 := by simp [hdrTailWords0]
  have hw_len1 : (hdrTailWords1 c s0).length = 35 := by simp [hdrTailWords1]
  have hw_len2 : (hdrTailWords2 c s0).length = 35 := by simp [hdrTailWords2]
  have hm := array64_to_hdrTail4 hw hm
  have hsub_bva : BitVec.ofNat 64 c.max_vars - BitVec.ofNat 64 c.mv =
      BitVec.ofNat 64 (c.max_vars - c.mv) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, hmv_to, hmx_to, BitVec.toNat_ofNat]
    have := c.hbva; omega
  unfold Func.wp full_init_hdr_body
  fp_head_steps
  rw [hsub_bva] at hm
  have hm_arr : (array64 (c.hdr + 32) (s13HdrW0 fuel w0 ++ s13HdrW1 w1 ++
      s13HdrW2 c.mv c.max_vars w2 ++ s13HdrW3 c.mv w3) ⋆ R) m := by
    rw [← hdrTail4_eq_array64 (by simp [h0l]) (by simp [h1l]) (by simp [h2l]) (by simp [h3l])]
    exact hm
  have hi0 : ∀ j ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29],
      j < 35 ∧ j ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have hi1 : ∀ j ∈ [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
      j < 35 ∧ (35 + j) ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have hi2 : ∀ j ∈ [26, 27, 28, 29, 30, 31, 32, 33, 34],
      j < 35 ∧ (70 + j) ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have hi3 : ∀ j ∈ [0, 1, 2, 3, 4, 6, 7, 8],
      j < 35 ∧ (105 + j) ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have heq0 : s13HdrW0 fuel w0 = hdrTailWords0 c s0 := s13HdrW0_eq c fuel w0 h0l fun i hi => by
    have ⟨hi', hm'⟩ := hi0 i hi
    have hgi := hws0 i hm'
    dsimp only [w0]; rw [List.getElem?_take_of_lt hi', hgi]
    unfold Full.hdrTailWords; exact append4_getElem?_0 hw_len0 hi'
  have heq1 : s13HdrW1 w1 = hdrTailWords1 c s0 := s13HdrW1_eq c fuel w1 h1l fun i hi => by
    have ⟨hi35, hm'⟩ := hi1 i hi
    have hgi := hws0 (35 + i) hm'
    dsimp only [w1]; rw [drop_take_getElem? ws 35 35 i hi35, hgi]
    unfold Full.hdrTailWords
    rw [append4_getElem?_1 hw_len0 hw_len1 (by omega) (by omega), show 35 + i - 35 = i by omega]
  have heq2 : s13HdrW2 c.mv c.max_vars w2 = hdrTailWords2 c s0 :=
    s13HdrW2_eq c fuel w2 h2l fun i hi => by
      have ⟨hi35, hm'⟩ := hi2 i hi
      have hgi := hws0 (70 + i) hm'
      dsimp only [w2]; rw [drop_take_getElem? ws 70 35 i hi35, hgi]
      unfold Full.hdrTailWords
      rw [append4_getElem?_2 hw_len0 hw_len1 hw_len2 (by omega) (by omega),
        show 70 + i - 70 = i by omega]
  have heq3 : s13HdrW3 c.mv w3 = hdrTailWords3 c s0 := s13HdrW3_eq c fuel w3 h3l fun i hi => by
    have ⟨hi35, hm'⟩ := hi3 i hi
    have hgi := hws0 (105 + i) hm'
    dsimp only [w3]; rw [drop_take_getElem? ws 105 35 i hi35, hgi]
    unfold Full.hdrTailWords
    rw [append4_getElem?_3 hw_len0 hw_len1 hw_len2 (by omega), show 105 + i - 105 = i by omega]
  rw [heq0, heq1, heq2, heq3] at hm_arr
  change (array64 (c.hdr + 32) (Full.hdrTailWords c s0) ⋆ R) m at hm_arr
  exact hQ s0 m rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hm_arr

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S0
