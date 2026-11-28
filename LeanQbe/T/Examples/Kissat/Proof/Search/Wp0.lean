/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Search.Helpers

/-!
# Verification of `full_preprocess_m6` and `full_simplify_m6` (`Proof.Search.Wp0`)

Proves `full_simplify_m6_wp` (`Spec.simplifySpec`) and
`full_preprocess_m6_wp` (`Spec.preprocessSpec`) in `Γ.Sat searchDeps`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Search

open Std Std.Sat Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src LeanQbe.T.Examples.Kissat.Src.Search
open LeanQbe.T.Examples.Kissat.Proof LeanQbe.T.Examples.Kissat.Proof.Spec

/-! ## 1. Preprocessing Measure & Reusable Sub-block Helpers -/

private def prepMeasure (c : FullCfg) (s : FullState) : Nat :=
  s.core.fuel.toNat * (c.max_vars + 2) + (c.max_vars + 1 - s.core.trail_end)

private theorem prepMeasure_lt_of_fuel {c0 c1 : FullCfg} {s0 s1 : FullState}
    (hc : FullCfgCompat c0 c1) (hl1 : s1.LengthsOk c1)
    (hfl : s1.core.fuel.toNat < s0.core.fuel.toNat) :
    prepMeasure c1 s1 < prepMeasure c0 s0 := by
  unfold prepMeasure
  have h1 := hl1.core_ok.trail_end_le
  have h2 := hl1.core_ok.cur_vars_le
  rw [hc.max_vars] at h2 ⊢
  have hm : s1.core.fuel.toNat + 1 ≤ s0.core.fuel.toNat := hfl
  have hmul := Nat.mul_le_mul_right (c0.max_vars + 2) hm
  rw [Nat.add_mul, Nat.one_mul] at hmul
  omega

private theorem prepMeasure_lt_of_trail {c : FullCfg} {s0 s1 : FullState}
    (hl1 : s1.LengthsOk c) (hfl : s1.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hte : s0.core.trail_end < s1.core.trail_end) :
    prepMeasure c s1 < prepMeasure c s0 := by
  unfold prepMeasure
  have h1 := hl1.core_ok.trail_end_le
  have h2 := hl1.core_ok.cur_vars_le
  rcases Nat.eq_or_lt_of_le hfl with heq | hlt
  · rw [heq]; omega
  · have hm : s1.core.fuel.toNat + 1 ≤ s0.core.fuel.toNat := hlt
    have hmul := Nat.mul_le_mul_right (c.max_vars + 2) hm
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega

private theorem step_load_oom_ret0 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {a : Arg Val i64} {e1 e2 : Expr Val Cont rs}
    (ha : a.val = c.hdr) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hne : s.core.oom ≠ 0#64 → wp Γ Q X e1 m)
    (heq : s.core.oom = 0#64 → wp Γ Q X e2 m) :
    wp Γ Q X (.let_ (op2 (.add i64) a (Arg.imm 760)) fun p =>
      .load i64 (Arg.var p.fst) fun ld =>
        .let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun cmp =>
          .jnz (Arg.var cmp.fst) e1 e2) m := by
  rw [show (op2 (.add i64) a (Arg.imm 760)) =
      Op.mk (.add i64) (a, Arg.imm 760, ()) from rfl]
  c0_hstraight
  rw [wp_load]
  refine ⟨_, ha ▸ m6Hdr_load_off .oom 760 rfl hm, ?_⟩
  c0_hstraight
  exact jnz_bv_ne rfl hne heq

private theorem step_load_fuel_ret0 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {a : Arg Val i64} {e1 e2 : Expr Val Cont rs}
    (ha : a.val = c.hdr) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (heq : s.core.fuel = 0#64 → wp Γ Q X e1 m)
    (hne : s.core.fuel ≠ 0#64 → wp Γ Q X e2 m) :
    wp Γ Q X (.let_ (op2 (.add i64) a (Arg.imm 168)) fun p =>
      .load i64 (Arg.var p.fst) fun ld =>
        .let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun cmp =>
          .jnz (Arg.var cmp.fst) e1 e2) m := by
  rw [show (op2 (.add i64) a (Arg.imm 168)) =
      Op.mk (.add i64) (a, Arg.imm 168, ()) from rfl]
  c0_hstraight
  rw [wp_load]
  refine ⟨_, ha ▸ m6Hdr_load_off .fuel 168 rfl hm, ?_⟩
  c0_hstraight
  exact jnz_bv_eq rfl heq hne

private theorem step_load_inc_ret20 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {a : Arg Val i64} {e1 e2 : Expr Val Cont rs}
    (ha : a.val = c.hdr) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hne : s.core.inconsistent ≠ 0#64 → wp Γ Q X e1 m)
    (heq : s.core.inconsistent = 0#64 → wp Γ Q X e2 m) :
    wp Γ Q X (.let_ (op2 (.add i64) a (Arg.imm 1024)) fun p =>
      .load i64 (Arg.var p.fst) fun ld =>
        .let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun cmp =>
          .jnz (Arg.var cmp.fst) e1 e2) m := by
  rw [show (op2 (.add i64) a (Arg.imm 1024)) =
      Op.mk (.add i64) (a, Arg.imm 1024, ()) from rfl]
  c0_hstraight
  rw [wp_load]
  refine ⟨_, ha ▸ m6Hdr_load_off .inconsistent 1024 rfl hm, ?_⟩
  c0_hstraight
  exact jnz_bv_ne rfl hne heq

private theorem step_load_unass_ret10 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {a : Arg Val i64} {e1 e2 : Expr Val Cont rs}
    (ha : a.val = c.hdr) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (heq : s.core.unassigned = 0#64 → wp Γ Q X e1 m)
    (hne : s.core.unassigned ≠ 0#64 → wp Γ Q X e2 m) :
    wp Γ Q X (.let_ (op2 (.add i64) a (Arg.imm 792)) fun p =>
      .load i64 (Arg.var p.fst) fun ld =>
        .let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun cmp =>
          .jnz (Arg.var cmp.fst) e1 e2) m := by
  rw [show (op2 (.add i64) a (Arg.imm 792)) =
      Op.mk (.add i64) (a, Arg.imm 792, ()) from rfl]
  c0_hstraight
  rw [wp_load]
  refine ⟨_, ha ▸ m6Hdr_load_off .unassigned 792 rfl hm, ?_⟩
  c0_hstraight
  exact jnz_bv_eq rfl heq hne

private theorem step_scale_store_scr {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hΓ : Γ.Sat searchDeps)
    {a : Arg Val i64} (ha : a.val = c.hdr) (base : BitVec 64)
    (f : HdrWordField) (off : Nat) (hoff : HdrWordField.ofOff? off = some f)
    (hmut : f.isMutable = true) (hscr : f.isScrPres = true)
    {k : Expr Val Cont rs}
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ v, let s' := f.set s v
      FullM6HdrInv c F0 ext s' →
      (FullM6HdrMem c ext s' ⋆ R) (storeMem m i64 (c.hdr + BitVec.ofNat 64 off) v) →
      wp Γ Q X k (storeMem m i64 (c.hdr + BitVec.ofNat 64 off) v)) :
    wp Γ Q X (.call (as := [i64, i64]) (bs := [i64]) "full_scale_delta_m5"
      (a, Arg.imm base, ()) fun p =>
      .let_ (op2 (.add i64) a (Arg.imm off)) fun q =>
        .store (Arg.var p.fst) (Arg.var q.fst) k) m := by
  refine search_call_scale_delta base (by simp [vals, ha])
    (deps_has_scale_delta hΓ) hinv hm fun delta => ?_
  c0_hstraight
  have ⟨hok, hinv', hm'⟩ := m6Hdr_store_scr f off hoff hmut hscr delta hinv hm
  rw [wp_store]
  exact ⟨by simpa [vals, ha] using hok, by simpa [vals, ha] using hk delta hinv' hm'⟩

/-! ## 2. `full_simplify_m6_wp` -/

private abbrev simpTailExpr (h : Val i64) : Expr Val Cont [i64] :=
  .group (sig := [[]])
    (fun _ => Blocks.cons (fun _ =>
      .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 1024)) fun p13 =>
        .load i64 (Arg.var p13.fst) fun ld =>
          .let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p14 =>
            .jnz (Arg.var p14.fst) (.ret (Arg.imm 20, ()))
              (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 760)) fun q =>
                .load i64 (Arg.var q.fst) fun ld =>
                  .let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun q2 =>
                    .jnz (Arg.var q2.fst) (.ret (Arg.imm 0, ())) (.ret (Arg.imm 1, ())))) .nil)
    (fun Js =>
      .call (as := [i64]) (bs := [.bool]) "full_compact_needed" (Arg.var h, ()) fun b =>
        .jnz (Arg.var b.fst)
          (.call (as := [i64]) (bs := [i64]) "full_compact" (Arg.var h, ()) fun r =>
            .let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var r.fst, Arg.imm 20, ())) fun r20 =>
              .jnz (Arg.var r20.fst) (.ret (Arg.imm 20, ()))
                (.let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var r.fst, Arg.imm 1, ())) fun r1 =>
                  .jnz (Arg.var r1.fst) (.ret (Arg.imm 0, ())) (.jump Js.fst ())))
          (.jump Js.fst ()))

private abbrev simpElimExpr (h : Val i64) (de : Val .bool) : Expr Val Cont [i64] :=
  .group (sig := [[]])
    (fun _ => Blocks.cons (fun _ =>
      .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 1024)) fun p8 =>
        .load i64 (Arg.var p8.fst) fun ld =>
          .let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p9 =>
            .jnz (Arg.var p9.fst) (.ret (Arg.imm 20, ()))
              (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 760)) fun p10 =>
                .load i64 (Arg.var p10.fst) fun ld =>
                  .let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p11 =>
                    .jnz (Arg.var p11.fst) (.ret (Arg.imm 0, ())) (simpTailExpr h))) .nil)
    (fun Js => .jnz (Arg.var de)
      (.call (as := [i64, .bool]) (bs := [i64]) "full_eliminate_m6"
        (Arg.var h, Arg.imm false, ()) fun p =>
        .let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var p.fst, Arg.imm 20, ())) fun p2 =>
          .jnz (Arg.var p2.fst) (.ret (Arg.imm 20, ())) (.jump Js.fst ()))
      (.jump Js.fst ()))

private theorem simplify_compact_tail_wp {Γ : Env} (hΓ : Γ.Sat searchDeps)
    {c0 c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s0 s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hc0 : FullCfgCompat c0 c) (hinv : FullM6HdrInv c F0 ext s) (hl0 : s.core.cur_level = 0)
    (hfl : s.core.fuel.toNat ≤ s0.core.fuel.toNat) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r c' ext' s' m',
      FullCfgCompat c0 c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (simpTailExpr c0.hdr) m := by
  dsimp only [simpTailExpr]
  refine wp_join0 (fun m4 => ∃ c4 ext4 s4,
      FullCfgCompat c0 c4 ∧ FullM6HdrInv c4 F0 ext4 s4 ∧ s4.core.cur_level = 0 ∧
      s4.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullM6HdrMem c4 ext4 s4 ⋆ R) m4) ?_ ?_
  · intro _ m4 ⟨c4, ext4, s4, hc4, hinv4, hl4, hfl4, hm4⟩
    refine step_load_inc_ret20 (a := Arg.var c0.hdr) (c := c4) hc4.hdr.symm hm4
      (fun hinc => ?_) (fun _ => ?_)
    · c0_hstraight
      exact hk 20#64 c4 ext4 s4 m4 hc4 hinv4.sparse.lengths hinv4.cfgOk hinv4.extOk
        (.inr (.inr rfl)) hfl4 (fun _ => fullM6HdrInv_inconsistent_unsat hinv4 hinc)
        (fun h => absurd h (by decide)) hm4
    · refine step_load_oom_ret0 (a := Arg.var c0.hdr) (c := c4) hc4.hdr.symm hm4
        (fun _ => ?_) (fun _ => ?_) <;> c0_hstraight
      · exact hk 0#64 c4 ext4 s4 m4 hc4 hinv4.sparse.lengths hinv4.cfgOk hinv4.extOk
          (.inl rfl) hfl4 (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm4
      · exact hk 1#64 c4 ext4 s4 m4 hc4 hinv4.sparse.lengths hinv4.cfgOk hinv4.extOk
          (.inr (.inl rfl)) hfl4 (fun h => absurd h (by decide)) (fun _ => ⟨hinv4, hl4⟩) hm4
  · intro J4 hJ4
    refine search_call_compact_needed (by simp [vals, hc0.hdr]) (deps_has_compact_needed hΓ)
      hinv hm fun b => ?_
    c0_hstraight
    refine wp_jnz_decide (b = true) (by cases b <;> rfl) (fun _ => ?_) (fun _ => ?_)
    · refine search_call_compact (by simp [vals, hc0.hdr]) (deps_has_compact hΓ) hinv hm
        fun r c' ext' s' m' hc' hinv' _ _ hfl' h20 h1 hm' => ?_
      c0_hstraight
      refine jnz_bv_eq rfl (fun eq20 => ?_) (fun _ => ?_)
      · c0_hstraight
        exact hk 20#64 c' ext' s' m' (fullCfgCompat_trans hc0 hc') hinv'.sparse.lengths
          hinv'.cfgOk hinv'.extOk (.inr (.inr rfl)) (Nat.le_trans hfl' hfl)
          (fun _ => h20 eq20) (fun h => absurd h (by decide)) hm'
      · c0_hstraight
        refine jnz_bv_ne rfl (fun _ => ?_) (fun eq1 => ?_) <;> c0_hstraight
        · exact hk 0#64 c' ext' s' m' (fullCfgCompat_trans hc0 hc') hinv'.sparse.lengths
            hinv'.cfgOk hinv'.extOk (.inl rfl) (Nat.le_trans hfl' hfl)
            (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm'
        · exact hJ4 m' ⟨c', ext', s', fullCfgCompat_trans hc0 hc', hinv', h1 eq1,
            Nat.le_trans hfl' hfl, hm'⟩
    · c0_hstraight
      exact hJ4 m ⟨c, ext, s, hc0, hinv, hl0, hfl, hm⟩

private theorem simplify_elim_tail_wp {Γ : Env} (hΓ : Γ.Sat searchDeps)
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s0 s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (do_elim : Bool) (hinv : FullM6HdrInv c F0 ext s) (hl0 : s.core.cur_level = 0)
    (hfl : s.core.fuel.toNat ≤ s0.core.fuel.toNat) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r c' ext' s' m',
      FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (simpElimExpr c.hdr do_elim) m := by
  dsimp only [simpElimExpr]
  refine wp_join0 (fun m3 => ∃ ext3 s3, FullM6HdrInv c F0 ext3 s3 ∧ s3.core.cur_level = 0 ∧
      s3.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullM6HdrMem c ext3 s3 ⋆ R) m3) ?_ ?_
  · intro _ m3 ⟨ext3, s3, hinv3, hl3, hfl3, hm3⟩
    refine step_load_inc_ret20 rfl hm3 (fun hinc => ?_) (fun _ => ?_)
    · c0_hstraight
      exact hk 20#64 c ext3 s3 m3 (fullCfgCompat_refl c) hinv3.sparse.lengths hinv3.cfgOk
        hinv3.extOk (.inr (.inr rfl)) hfl3 (fun _ => fullM6HdrInv_inconsistent_unsat hinv3 hinc)
        (fun h => absurd h (by decide)) hm3
    · refine step_load_oom_ret0 rfl hm3 (fun _ => ?_) (fun _ => ?_)
      · c0_hstraight
        exact hk 0#64 c ext3 s3 m3 (fullCfgCompat_refl c) hinv3.sparse.lengths hinv3.cfgOk
          hinv3.extOk (.inl rfl) hfl3 (fun h => absurd h (by decide))
          (fun h => absurd h (by decide)) hm3
      · exact simplify_compact_tail_wp hΓ (fullCfgCompat_refl c) hinv3 hl3 hfl3 hm3 hk
  · intro J3 hJ3
    refine wp_jnz_decide (do_elim = true) (by cases do_elim <;> rfl) (fun _ => ?_) (fun _ => ?_)
    · refine search_call_eliminate false (by simp [vals]) (deps_has_eliminate hΓ) hinv hl0 hm
        fun r ext' s' m' hinv' hl' hfl' _ h20 hm' => ?_
      c0_hstraight
      refine jnz_bv_eq rfl (fun eq20 => ?_) (fun _ => ?_)
      · c0_hstraight
        exact hk 20#64 c ext' s' m' (fullCfgCompat_refl c) hinv'.sparse.lengths hinv'.cfgOk
          hinv'.extOk (.inr (.inr rfl)) (Nat.le_trans hfl' hfl) (fun _ => h20 eq20)
          (fun h => absurd h (by decide)) hm'
      · c0_hstraight
        exact hJ3 m' ⟨ext', s', hinv', hl', Nat.le_trans hfl' hfl, hm'⟩
    · c0_hstraight
      exact hJ3 m ⟨ext, s, hinv, hl0, hfl, hm⟩

theorem full_simplify_m6_wp {Γ : Env} (hΓ : Γ.Sat searchDeps) :
    SpecEntry.Impl Γ full_simplify_m6
      ⟨"full_simplify_m6", [i64, .bool, .bool], [i64], Spec.simplifySpec, true⟩ := by
  refine ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X hs => ?_⟩
  dsimp only [full_simplify_m6] at xs Q m hs ⊢
  change Spec.simplifySpec xs m Q X at hs
  rcases xs with ⟨h, dp, de, ⟨⟩⟩
  unfold Spec.simplifySpec at hs
  obtain ⟨c, ext, s, F0, R, rfl, hcfg, hext, _, hsp, hm, hk_raw⟩ := M6HdrCfgContract.elim hs
  have hinv : FullM6HdrInv c F0 ext s := ⟨hcfg, hext, hsp⟩
  let hk : ∀ r c' ext' s' m',
      FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m' :=
    fun r c' ext' s' m' hc' hlen' hcfg' hext' hr hfl h20 h1 hm' =>
      hk_raw (r, ()) c' ext' s' m' hc' hcfg' hext' trivial hlen'
        ⟨hr, hfl, h20, fun eq1 => let x := h1 eq1; ⟨x.1.sparse, x.2⟩⟩ hm'
  dsimp only [Func.wp, full_simplify_m6_body]
  refine wp_join0 (fun m1 => ∃ s1, FullM6HdrInv c F0 ext s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel = s.core.fuel ∧ (FullM6HdrMem c ext s1 ⋆ R) m1) ?_ ?_
  · intro _ m1 ⟨s1, hinv1, hl1, hfl1, hm1⟩
    c0_hstraight
    refine wp_join0 (fun m2 => ∃ ext2 s2, FullM6HdrInv c F0 ext2 s2 ∧ s2.core.cur_level = 0 ∧
        s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext2 s2 ⋆ R) m2) ?_ ?_
    · intro _ m2 ⟨ext2, s2, hinv2, hl2, hfl2, hm2⟩
      refine step_load_oom_ret0 rfl hm2 (fun _ => ?_) (fun _ => ?_)
      · c0_hstraight
        exact hk 0#64 c ext2 s2 m2 (fullCfgCompat_refl c) hinv2.sparse.lengths hinv2.cfgOk
          hinv2.extOk (.inl rfl) hfl2 (fun h => absurd h (by decide))
          (fun h => absurd h (by decide)) hm2
      · refine step_load_fuel_ret0 rfl hm2 (fun _ => ?_) (fun _ => ?_)
        · c0_hstraight
          exact hk 0#64 c ext2 s2 m2 (fullCfgCompat_refl c) hinv2.sparse.lengths hinv2.cfgOk
            hinv2.extOk (.inl rfl) hfl2 (fun h => absurd h (by decide))
            (fun h => absurd h (by decide)) hm2
        · exact simplify_elim_tail_wp hΓ de hinv2 hl2 hfl2 hm2 hk
    · intro J2 hJ2
      refine wp_jnz_decide (dp = true) (by cases dp <;> rfl) (fun _ => ?_) (fun _ => ?_)
      · refine search_call_probe false (by simp [vals]) (deps_has_probe hΓ) hinv1 hl1 hm1
          fun r ext' s' m' hlen' hext' hfl' hr h20 h1 hm' => ?_
        c0_hstraight
        refine jnz_bv_eq rfl (fun eq20 => ?_) (fun ne20 => ?_)
        · c0_hstraight
          exact hk 20#64 c ext' s' m' (fullCfgCompat_refl c) hlen' hinv1.cfgOk hext'
            (.inr (.inr rfl)) (Nat.le_trans hfl' (hfl1 ▸ Nat.le_refl _)) (fun _ => h20 eq20)
            (fun h => absurd h (by decide)) hm'
        · have ⟨hinv', hl'⟩ := h1 (Or.resolve_right hr ne20)
          c0_hstraight
          exact hJ2 m' ⟨ext', s', hinv', hl', hfl1 ▸ hfl', hm'⟩
      · c0_hstraight
        exact hJ2 m1 ⟨ext, s1, hinv1, hl1, hfl1 ▸ Nat.le_refl _, hm1⟩
  · intro J1 hJ1
    c0_hstraight
    rw [wp_load]
    refine ⟨_, m6Hdr_load_off .cur_level 160 rfl hm, ?_⟩
    c0_hstraight
    have hcl_lt : s.core.cur_level < 2 ^ 64 := (fullM6HdrInv_nat_lt hinv).2.1
    refine jnz_bv_ult0 hcl_lt rfl (fun _ => ?_) (fun hl0 => ?_)
    · refine search_call_backtrack0 (by simp [vals]) (deps_has_backtrack hΓ) hinv hm
        fun s1 m1 hinv1 hl1 hfl1 _ _ hm1 => ?_
      c0_hstraight
      exact hJ1 m1 ⟨s1, hinv1, hl1, hfl1, hm1⟩
    · c0_hstraight
      exact hJ1 m ⟨s, hinv, hl0, rfl, hm⟩

/-! ## 3. `full_preprocess_m6_wp` -/

private abbrev prepL50Expr (h : Val i64) : Expr Val Cont [i64] :=
  .group (sig := [[]])
    (fun _ => Blocks.cons (fun _ =>
      .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 1024)) fun p39 =>
        .load i64 (Arg.var p39.fst) fun ld =>
          .let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p40 =>
            .jnz (Arg.var p40.fst) (.ret (Arg.imm 20, ()))
              (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 760)) fun p41 =>
                .load i64 (Arg.var p41.fst) fun ld =>
                  .let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p42 =>
                    .jnz (Arg.var p42.fst) (.ret (Arg.imm 0, ()))
                      (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 792)) fun p43 =>
                        .load i64 (Arg.var p43.fst) fun ld =>
                          .let_ (Op.mk (.cmp .eq i64 .bool rfl)
                            (Arg.var ld, Arg.imm 0, ())) fun p44 =>
                            .jnz (Arg.var p44.fst) (.ret (Arg.imm 10, ()))
                              (.call (as := [i64, i64]) (bs := [i64]) "full_scale_delta_m5"
                                (Arg.var h, Arg.imm 100, ()) fun p45 =>
                                .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 976)) fun p46 =>
                                  .store (Arg.var p45.fst) (Arg.var p46.fst)
                                    (.call (as := [i64, i64]) (bs := [i64]) "full_scale_delta_m5"
                                      (Arg.var h, Arg.imm 500, ()) fun p47 =>
                                      .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 992)) fun q =>
                                        .store (Arg.var p47.fst) (Arg.var q.fst)
                                          (.ret (Arg.imm 1, ()))))))) .nil)
    (fun Js =>
      .call (as := [i64]) (bs := [.bool]) "full_compact_needed" (Arg.var h, ()) fun p38 =>
        .jnz (Arg.var p38.fst)
          (.call (as := [i64]) (bs := [i64]) "full_compact" (Arg.var h, ()) fun p =>
            .let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var p.fst, Arg.imm 20, ())) fun p39 =>
              .jnz (Arg.var p39.fst) (.ret (Arg.imm 20, ()))
                (.let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var p.fst, Arg.imm 1, ())) fun p2 =>
                  .jnz (Arg.var p2.fst) (.ret (Arg.imm 0, ())) (.jump Js.fst ())))
          (.jump Js.fst ()))

private abbrev prepL25AfterProbeExpr (h : Val i64) : Expr Val Cont [i64] :=
  .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 1024)) fun p32 =>
    .load i64 (Arg.var p32.fst) fun ld =>
      .let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p33 =>
        .jnz (Arg.var p33.fst) (.ret (Arg.imm 20, ()))
          (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 760)) fun p34 =>
            .load i64 (Arg.var p34.fst) fun ld =>
              .let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p35 =>
                .jnz (Arg.var p35.fst) (.ret (Arg.imm 0, ()))
                  (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 168)) fun p36 =>
                    .load i64 (Arg.var p36.fst) fun ld =>
                      .let_ (Op.mk (.cmp .eq i64 .bool rfl)
                        (Arg.var ld, Arg.imm 0, ())) fun p37 =>
                        .jnz (Arg.var p37.fst) (.ret (Arg.imm 0, ())) (prepL50Expr h)))

private abbrev prepL25BodyExpr (h : Val i64) : Expr Val Cont [i64] :=
  .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 1024)) fun p20 =>
    .load i64 (Arg.var p20.fst) fun ld =>
      .let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p21 =>
        .jnz (Arg.var p21.fst) (.ret (Arg.imm 20, ()))
          (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 760)) fun p22 =>
            .load i64 (Arg.var p22.fst) fun ld =>
              .let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p23 =>
                .jnz (Arg.var p23.fst) (.ret (Arg.imm 0, ()))
                  (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 792)) fun p24 =>
                    .load i64 (Arg.var p24.fst) fun ld =>
                      .let_ (Op.mk (.cmp .eq i64 .bool rfl)
                        (Arg.var ld, Arg.imm 0, ())) fun p25 =>
                        .jnz (Arg.var p25.fst) (.ret (Arg.imm 10, ()))
                          (.call (as := [i64, i64]) (bs := [i64]) "full_scale_delta_m5"
                            (Arg.var h, Arg.imm 100, ()) fun p26 =>
                            .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 976)) fun p27 =>
                              .store (Arg.var p26.fst) (Arg.var p27.fst)
                                (.call (as := [i64, i64]) (bs := [i64]) "full_scale_delta_m5"
                                  (Arg.var h, Arg.imm 500, ()) fun p28 =>
                                  .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 992)) fun p29 =>
                                    .store (Arg.var p28.fst) (Arg.var p29.fst)
                                      (.call (as := [i64, .bool]) (bs := [i64]) "full_probe_m6"
                                        (Arg.var h, Arg.imm true, ()) fun p30 =>
                                        .let_ (Op.mk (.cmp .eq i64 .bool rfl)
                                          (Arg.var p30.fst, Arg.imm 20, ())) fun p31 =>
                                          .jnz (Arg.var p31.fst) (.ret (Arg.imm 20, ()))
                                            (prepL25AfterProbeExpr h))))))

private abbrev prepL25Expr (h : Val i64) : Expr Val Cont [i64] :=
  .group (sig := [[]])
    (fun _ => Blocks.cons (fun _ => prepL25BodyExpr h) .nil)
    (fun Js =>
      .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 144)) fun p19 =>
        .load i64 (Arg.var p19.fst) fun ld =>
          .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p20 =>
            .jnz (Arg.var p20.fst)
              (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 792)) fun p21 =>
                .load i64 (Arg.var p21.fst) fun ld =>
                  .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p22 =>
                    .jnz (Arg.var p22.fst)
                      (.call (as := [i64]) (bs := [i64]) "full_compact" (Arg.var h, ()) fun p =>
                        .let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var p.fst, Arg.imm 20, ()))
                          fun p23 =>
                          .jnz (Arg.var p23.fst) (.ret (Arg.imm 20, ()))
                            (.let_ (Op.mk (.cmp .ne i64 .bool rfl)
                              (Arg.var p.fst, Arg.imm 1, ())) fun p2 =>
                              .jnz (Arg.var p2.fst) (.ret (Arg.imm 0, ())) (.jump Js.fst ())))
                      (.jump Js.fst ()))
              (.jump Js.fst ()))

private abbrev prepSweepExpr (h : Val i64) (Js24 : Cont []) : Expr Val Cont [i64] :=
  .group (sig := [[]])
    (fun _ => Blocks.cons (fun _ =>
      .group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
        .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 512)) fun p =>
          .store (t := i64) (Arg.imm 0) (Arg.var p.fst) (.jump Js24 ())) .nil)
        (fun Js78 =>
          .group (sig := [[]]) (fun Js80 => Blocks.cons (fun _ =>
            .jnz (Arg.imm true)
              (.call (as := [i64]) (bs := [i64]) "full_arena_sweep" (Arg.var h, ()) fun p20 =>
                .let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var p20.fst, Arg.imm 2, ())) fun p21 =>
                  .jnz (Arg.var p21.fst) (.ret (Arg.imm 20, ()))
                    (.let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var p20.fst, Arg.imm 3, ()))
                      fun p22 =>
                      .jnz (Arg.var p22.fst) (.jump Js78.fst ())
                        (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 760)) fun p23 =>
                          .load i64 (Arg.var p23.fst) fun ld =>
                            .let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var ld, Arg.imm 0, ()))
                              fun p24 =>
                              .jnz (Arg.var p24.fst) (.jump Js78.fst ())
                                (.call (as := [i64]) (bs := [i64]) "full_propagate"
                                  (Arg.var h, ()) fun p25 =>
                                  .let_ (Op.mk (.cmp .eq i64 .bool rfl)
                                    (Arg.var p25.fst, Arg.imm 1, ())) fun p26 =>
                                    .jnz (Arg.var p26.fst) (.ret (Arg.imm 20, ()))
                                      (.let_ (Op.mk (.cmp .eq i64 .bool rfl)
                                        (Arg.var p25.fst, Arg.imm 2, ())) fun p27 =>
                                        .jnz (Arg.var p27.fst) (.jump Js78.fst ())
                                          (.let_ (Op.mk (.cmp .eq i64 .bool rfl)
                                            (Arg.var p20.fst, Arg.imm 0, ())) fun p28 =>
                                            .jnz (Arg.var p28.fst)
                                              (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 152))
                                                fun p29 =>
                                                .load i64 (Arg.var p29.fst) fun ld1 =>
                                                  .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 144))
                                                    fun q =>
                                                    .load i64 (Arg.var q.fst) fun ld2 =>
                                                      .let_ (Op.mk (.cmp .uge i64 .bool rfl)
                                                        (Arg.var ld1, Arg.var ld2, ())) fun cnd =>
                                                        .jnz (Arg.var cnd.fst) (.jump Js78.fst ())
                                                          (.jump Js80.fst ()))
                                              (.jump Js80.fst ())))))))
              (.jump Js78.fst ())) .nil)
            (fun Js80 => .jump Js80.fst ()))) .nil)
    (fun Js77 =>
      .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 512)) fun p18 =>
        .load i64 (Arg.var p18.fst) fun ld =>
          .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p19 =>
            .jnz (Arg.var p19.fst) (.jump Js77.fst ())
              (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 144)) fun q =>
                .load i64 (Arg.var q.fst) fun ld =>
                  .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun q2 =>
                    .jnz (Arg.var q2.fst) (.jump Js77.fst ()) (.jump Js24 ())))

private theorem preprocess_l50_wp {Γ : Env} (hΓ : Γ.Sat searchDeps)
    {c0 c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s0 s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hc0 : FullCfgCompat c0 c) (hinv : FullM6HdrInv c F0 ext s) (hl0 : s.core.cur_level = 0)
    (hfl : s.core.fuel.toNat ≤ s0.core.fuel.toNat) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r c' ext' s' m',
      FullCfgCompat c0 c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (prepL50Expr c0.hdr) m := by
  dsimp only [prepL50Expr]
  refine wp_join0 (fun m1 => ∃ c1 ext1 s1,
      FullCfgCompat c0 c1 ∧ FullM6HdrInv c1 F0 ext1 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullM6HdrMem c1 ext1 s1 ⋆ R) m1) ?_ ?_
  · intro _ m1 ⟨c1, ext1, s1, hc1, hinv1, hl1, hfl1, hm1⟩
    refine step_load_inc_ret20 hc1.hdr.symm hm1 (fun hinc => ?_) (fun _ => ?_)
    · c0_hstraight
      exact hk 20#64 c1 ext1 s1 m1 hc1 hinv1.sparse.lengths hinv1.cfgOk hinv1.extOk
        (.inr (.inr (.inr rfl))) hfl1 (fun _ => fullM6HdrInv_inconsistent_unsat hinv1 hinc)
        (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm1
    · refine step_load_oom_ret0 hc1.hdr.symm hm1 (fun _ => ?_) (fun _ => ?_)
      · c0_hstraight
        exact hk 0#64 c1 ext1 s1 m1 hc1 hinv1.sparse.lengths hinv1.cfgOk hinv1.extOk
          (.inl rfl) hfl1 (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
          (fun h => absurd h (by decide)) hm1
      · refine step_load_unass_ret10 hc1.hdr.symm hm1 (fun _ => ?_) (fun _ => ?_)
        · c0_hstraight
          exact hk 10#64 c1 ext1 s1 m1 hc1 hinv1.sparse.lengths hinv1.cfgOk hinv1.extOk
            (.inr (.inr (.inl rfl))) hfl1 (fun h => absurd h (by decide))
            (fun h => absurd h (by decide)) (fun _ => hinv1.sparse.2.2.2.1.2) hm1
        · refine step_scale_store_scr hΓ (a := Arg.var c0.hdr) (c := c1) hc1.hdr.symm
            100#64 .probe_limit 976 rfl rfl rfl hinv1 hm1 fun _ hinv2 hm2 => ?_
          refine step_scale_store_scr hΓ (a := Arg.var c0.hdr) (c := c1) hc1.hdr.symm
            500#64 .elim_limit 992 rfl rfl rfl hinv2 hm2 fun _ hinv3 hm3 => ?_
          c0_hstraight
          exact hk 1#64 c1 ext1 _ _ hc1 hinv3.sparse.lengths hinv3.cfgOk hinv3.extOk
            (.inr (.inl rfl)) hfl1 (fun h => absurd h (by decide))
            (fun _ => ⟨hinv3, hl1⟩) (fun h => absurd h (by decide)) hm3
  · intro J50 hJ50
    refine search_call_compact_needed (by simp [vals, hc0.hdr]) (deps_has_compact_needed hΓ)
      hinv hm fun b => ?_
    c0_hstraight
    refine wp_jnz_decide (b = true) (by cases b <;> rfl) (fun _ => ?_) (fun _ => ?_)
    · refine search_call_compact (by simp [vals, hc0.hdr]) (deps_has_compact hΓ) hinv hm
        fun r c' ext' s' m' hc' hinv' _ _ hfl' h20 h1 hm' => ?_
      c0_hstraight
      refine jnz_bv_eq rfl (fun eq20 => ?_) (fun _ => ?_)
      · c0_hstraight
        exact hk 20#64 c' ext' s' m' (fullCfgCompat_trans hc0 hc') hinv'.sparse.lengths
          hinv'.cfgOk hinv'.extOk (.inr (.inr (.inr rfl))) (Nat.le_trans hfl' hfl)
          (fun _ => h20 eq20) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm'
      · c0_hstraight
        refine jnz_bv_ne rfl (fun _ => ?_) (fun eq1 => ?_) <;> c0_hstraight
        · exact hk 0#64 c' ext' s' m' (fullCfgCompat_trans hc0 hc') hinv'.sparse.lengths
            hinv'.cfgOk hinv'.extOk (.inl rfl) (Nat.le_trans hfl' hfl)
            (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
            (fun h => absurd h (by decide)) hm'
        · exact hJ50 m' ⟨c', ext', s', fullCfgCompat_trans hc0 hc', hinv', h1 eq1,
            Nat.le_trans hfl' hfl, hm'⟩
    · c0_hstraight
      exact hJ50 m ⟨c, ext, s, hc0, hinv, hl0, hfl, hm⟩

private theorem preprocess_l25_wp {Γ : Env} (hΓ : Γ.Sat searchDeps)
    {c0 : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s0 s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInv c0 F0 ext s) (hl0 : s.core.cur_level = 0)
    (hfl : s.core.fuel.toNat ≤ s0.core.fuel.toNat) (hm : (FullM6HdrMem c0 ext s ⋆ R) m)
    (hk : ∀ r c' ext' s' m',
      FullCfgCompat c0 c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (prepL25Expr c0.hdr) m := by
  dsimp only [prepL25Expr]
  refine wp_join0 (fun m1 => ∃ c1 ext1 s1,
      FullCfgCompat c0 c1 ∧ FullM6HdrInv c1 F0 ext1 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullM6HdrMem c1 ext1 s1 ⋆ R) m1) ?_ ?_
  · intro _ m1 ⟨c1, ext1, s1, hc1, hinv1, hl1, hfl1, hm1⟩
    refine step_load_inc_ret20 hc1.hdr.symm hm1 (fun hinc => ?_) (fun _ => ?_)
    · c0_hstraight
      exact hk 20#64 c1 ext1 s1 m1 hc1 hinv1.sparse.lengths hinv1.cfgOk hinv1.extOk
        (.inr (.inr (.inr rfl))) hfl1 (fun _ => fullM6HdrInv_inconsistent_unsat hinv1 hinc)
        (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm1
    · refine step_load_oom_ret0 hc1.hdr.symm hm1 (fun _ => ?_) (fun _ => ?_)
      · c0_hstraight
        exact hk 0#64 c1 ext1 s1 m1 hc1 hinv1.sparse.lengths hinv1.cfgOk hinv1.extOk
          (.inl rfl) hfl1 (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
          (fun h => absurd h (by decide)) hm1
      · refine step_load_unass_ret10 hc1.hdr.symm hm1 (fun _ => ?_) (fun _ => ?_)
        · c0_hstraight
          exact hk 10#64 c1 ext1 s1 m1 hc1 hinv1.sparse.lengths hinv1.cfgOk hinv1.extOk
            (.inr (.inr (.inl rfl))) hfl1 (fun h => absurd h (by decide))
            (fun h => absurd h (by decide)) (fun _ => hinv1.sparse.2.2.2.1.2) hm1
        · refine step_scale_store_scr hΓ (a := Arg.var c0.hdr) (c := c1) hc1.hdr.symm
            100#64 .probe_limit 976 rfl rfl rfl hinv1 hm1 fun _ hinv2 hm2 => ?_
          refine step_scale_store_scr hΓ (a := Arg.var c0.hdr) (c := c1) hc1.hdr.symm
            500#64 .elim_limit 992 rfl rfl rfl hinv2 hm2 fun _ hinv3 hm3 => ?_
          refine search_call_probe true (by simp [vals, hc1.hdr]) (deps_has_probe hΓ)
            hinv3 hl1 hm3 fun r ext' s' m' hlen' hext' hflp hr h20 h1 hm' => ?_
          c0_hstraight
          refine jnz_bv_eq rfl (fun eq20 => ?_) (fun ne20 => ?_)
          · c0_hstraight
            exact hk 20#64 c1 ext' s' m' hc1 hlen' hinv3.cfgOk hext' (.inr (.inr (.inr rfl)))
              (Nat.le_trans hflp hfl1) (fun _ => h20 eq20) (fun h => absurd h (by decide))
              (fun h => absurd h (by decide)) hm'
          · have ⟨hinv4, hl4⟩ := h1 (Or.resolve_right hr ne20)
            have hfl4 : s'.core.fuel.toNat ≤ s0.core.fuel.toNat := Nat.le_trans hflp hfl1
            refine step_load_inc_ret20 hc1.hdr.symm hm' (fun hinc => ?_) (fun _ => ?_)
            · c0_hstraight
              exact hk 20#64 c1 ext' s' m' hc1 hinv4.sparse.lengths hinv4.cfgOk hinv4.extOk
                (.inr (.inr (.inr rfl))) hfl4
                (fun _ => fullM6HdrInv_inconsistent_unsat hinv4 hinc)
                (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm'
            · refine step_load_oom_ret0 hc1.hdr.symm hm' (fun _ => ?_) (fun _ => ?_)
              · c0_hstraight
                exact hk 0#64 c1 ext' s' m' hc1 hinv4.sparse.lengths hinv4.cfgOk hinv4.extOk
                  (.inl rfl) hfl4 (fun h => absurd h (by decide))
                  (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm'
              · refine step_load_fuel_ret0 hc1.hdr.symm hm' (fun _ => ?_) (fun _ => ?_)
                · c0_hstraight
                  exact hk 0#64 c1 ext' s' m' hc1 hinv4.sparse.lengths hinv4.cfgOk hinv4.extOk
                    (.inl rfl) hfl4 (fun h => absurd h (by decide))
                    (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm'
                · exact preprocess_l50_wp hΓ hc1 hinv4 hl4 hfl4 hm' hk
  · intro J25 hJ25
    c0_hstraight
    rw [wp_load]; refine ⟨_, m6Hdr_load_off .trail_end 144 rfl hm, ?_⟩
    c0_hstraight
    refine jnz_bv_ult0 (fullM6HdrInv_nat_lt hinv).2.2.1 rfl (fun _ => ?_) (fun _ => ?_)
    · c0_hstraight
      rw [wp_load]; refine ⟨_, m6Hdr_load_off .unassigned 792 rfl hm, ?_⟩
      c0_hstraight
      refine jnz_bv_ult rfl (fun _ => ?_) (fun _ => ?_)
      · refine search_call_compact (by simp [vals]) (deps_has_compact hΓ) hinv hm
          fun r c' ext' s' m' hc' hinv' _ _ hfl' h20 h1 hm' => ?_
        c0_hstraight
        refine jnz_bv_eq rfl (fun eq20 => ?_) (fun _ => ?_)
        · c0_hstraight
          exact hk 20#64 c' ext' s' m' hc' hinv'.sparse.lengths hinv'.cfgOk hinv'.extOk
            (.inr (.inr (.inr rfl))) (Nat.le_trans hfl' hfl) (fun _ => h20 eq20)
            (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm'
        · c0_hstraight
          refine jnz_bv_ne rfl (fun _ => ?_) (fun eq1 => ?_) <;> c0_hstraight
          · exact hk 0#64 c' ext' s' m' hc' hinv'.sparse.lengths hinv'.cfgOk hinv'.extOk
              (.inl rfl) (Nat.le_trans hfl' hfl) (fun h => absurd h (by decide))
              (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm'
          · exact hJ25 m' ⟨c', ext', s', hc', hinv', h1 eq1, Nat.le_trans hfl' hfl, hm'⟩
      · c0_hstraight
        exact hJ25 m ⟨c0, ext, s, fullCfgCompat_refl c0, hinv, hl0, hfl, hm⟩
    · c0_hstraight
      exact hJ25 m ⟨c0, ext, s, fullCfgCompat_refl c0, hinv, hl0, hfl, hm⟩

private theorem preprocess_sweep_wp {Γ : Env} (hΓ : Γ.Sat searchDeps)
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s0 s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {Js24 : Cont []}
    (hJ24 : ∀ ext' s' m',
      FullM6HdrInv c F0 ext' s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s0.core.fuel.toNat → (FullM6HdrMem c ext' s' ⋆ R) m' →
      Js24 () m')
    (hinv : FullM6HdrInv c F0 ext s) (hl0 : s.core.cur_level = 0)
    (hfl : s.core.fuel.toNat ≤ s0.core.fuel.toNat) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r c' ext' s' m',
      FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (prepSweepExpr c.hdr Js24) m := by
  dsimp only [prepSweepExpr]
  refine wp_join0 (fun m1 => ∃ ext1 s1, FullM6HdrInv c F0 ext1 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullM6HdrMem c ext1 s1 ⋆ R) m1) ?_ ?_
  · intro _ m1 ⟨ext1, s1, hinv1, hl1, hfl1, hm1⟩
    refine wp_join0 (fun m2 => ∃ ext2 s2, FullM6HdrInv c F0 ext2 s2 ∧ s2.core.cur_level = 0 ∧
        s2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullM6HdrMem c ext2 s2 ⋆ R) m2) ?_ ?_
    · intro _ m2 ⟨ext2, s2, hinv2, hl2, hfl2, hm2⟩
      c0_hstraight
      have ⟨hok, hinv3, hm3⟩ := m6Hdr_store_unflushed0 hinv2 hm2
      rw [wp_store]
      exact ⟨hok, hJ24 ext2 _ _ hinv3 hl2 hfl2 hm3⟩
    · intro J78 hJ78
      refine wp_while_state0 (fun st : FullState × List (BitVec 64) => prepMeasure c st.1)
        (fun st m' => FullM6HdrInv c F0 st.2 st.1 ∧ st.1.core.cur_level = 0 ∧
          st.1.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullM6HdrMem c st.2 st.1 ⋆ R) m')
        (fun J80 hJ80 => by c0_hstraight; exact hJ80 (s1, ext1) m1 ⟨hinv1, hl1, hfl1, hm1⟩)
        (fun _ ⟨sa, exta⟩ ma ⟨hinva, hla, hfla, hma⟩ ih => ?_)
      refine wp_jnz_true rfl ?_
      refine search_call_arena_sweep (by simp [vals]) (deps_has_arena_sweep hΓ) hinva hla hma
        fun r1 s1' m1' hinv1' _ hl1' hfl1' hr1 _ hte1 h20_1 _ hm1' => ?_
      c0_hstraight
      refine jnz_bv_eq rfl (fun eq2 => ?_) (fun ne2 => ?_)
      · c0_hstraight
        exact hk 20#64 c exta s1' m1' (fullCfgCompat_refl c) hinv1'.sparse.lengths hinv1'.cfgOk
          hinv1'.extOk (.inr (.inr (.inr rfl))) (hfl1' ▸ hfla) (fun _ => h20_1 eq2)
          (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm1'
      · c0_hstraight
        refine jnz_bv_eq rfl (fun _ => ?_) (fun ne3 => ?_)
        · c0_hstraight; exact hJ78 m1' ⟨exta, s1', hinv1', hl1', hfl1' ▸ hfla, hm1'⟩
        · refine step_load_oom_ret0 rfl hm1' (fun _ => ?_) (fun _ => ?_)
          · c0_hstraight; exact hJ78 m1' ⟨exta, s1', hinv1', hl1', hfl1' ▸ hfla, hm1'⟩
          · refine search_call_propagate (by simp [vals]) (deps_has_propagate hΓ) hinv1' hm1'
              fun r2 ext2' s2' m2' hinv2' _ hl2' hfl2' hr2 hte2 h0_2 h1_2 _ hm2' => ?_
            have hl2_eq : s2'.core.cur_level = 0 := hl2'.trans hl1'
            have hfl2_le : s2'.core.fuel.toNat ≤ s0.core.fuel.toNat :=
              Nat.le_trans hfl2' (hfl1' ▸ hfla)
            c0_hstraight
            refine jnz_bv_eq rfl (fun eq1 => ?_) (fun ne1 => ?_)
            · obtain ⟨F_cur, _, _, _, hw2, hconfl⟩ := h1_2 eq1
              c0_hstraight
              exact hk 20#64 c ext2' s2' m2' (fullCfgCompat_refl c) hinv2'.sparse.lengths
                hinv2'.cfgOk hinv2'.extOk (.inr (.inr (.inr rfl))) hfl2_le
                (fun _ => level0_unsat_of_conflict_okW hw2 hl2_eq hconfl)
                (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm2'
            · c0_hstraight
              refine jnz_bv_eq rfl (fun _ => ?_) (fun ne2_2 => ?_)
              · c0_hstraight; exact hJ78 m2' ⟨ext2', s2', hinv2', hl2_eq, hfl2_le, hm2'⟩
              · have hr2_0 : r2 = 0#64 := by
                  rcases hr2 with rfl | rfl | rfl
                  · rfl
                  · exact absurd rfl ne1
                  · exact absurd rfl ne2_2
                have hprop_eq := (h0_2 hr2_0).1
                c0_hstraight
                refine jnz_bv_eq rfl (fun _ => ?_) (fun ne0 => ?_)
                · c0_hstraight
                  rw [wp_load]; refine ⟨_, m6Hdr_load_off .propagated 152 rfl hm2', ?_⟩
                  c0_hstraight
                  rw [wp_load]; refine ⟨_, m6Hdr_load_off .trail_end 144 rfl hm2', ?_⟩
                  c0_hstraight
                  have hlt2 := fullM6HdrInv_nat_lt hinv2'
                  refine jnz_bv_ule_nat hlt2.2.2.2 hlt2.2.2.1 rfl
                    (fun _ => by
                      c0_hstraight; exact hJ78 m2' ⟨ext2', s2', hinv2', hl2_eq, hfl2_le, hm2'⟩)
                    (fun hlt => absurd hprop_eq (by omega))
                · have hr1_1 : r1 = 1#64 := by
                    rcases hr1 with rfl | rfl | rfl | rfl
                    · exact absurd rfl ne0
                    · rfl
                    · exact absurd rfl ne2
                    · exact absurd rfl ne3
                  have hte_lt : sa.core.trail_end < s2'.core.trail_end :=
                    Nat.lt_of_lt_of_le (hte1 hr1_1) hte2
                  c0_hstraight
                  exact ih (s2', ext2') m2'
                    (prepMeasure_lt_of_trail hinv2'.sparse.lengths (hfl1' ▸ hfl2') hte_lt)
                    ⟨hinv2', hl2_eq, hfl2_le, hm2'⟩
  · intro J77 hJ77
    c0_hstraight
    rw [wp_load]; refine ⟨_, m6Hdr_load_off .unflushed 512 rfl hm, ?_⟩
    c0_hstraight
    refine jnz_bv_ult rfl
      (fun _ => by c0_hstraight; exact hJ77 m ⟨ext, s, hinv, hl0, hfl, hm⟩) (fun _ => ?_)
    c0_hstraight
    rw [wp_load]; refine ⟨_, m6Hdr_load_off .trail_end 144 rfl hm, ?_⟩
    c0_hstraight
    refine jnz_bv_ult0 (fullM6HdrInv_nat_lt hinv).2.2.1 rfl
      (fun _ => by c0_hstraight; exact hJ77 m ⟨ext, s, hinv, hl0, hfl, hm⟩)
      (fun _ => by c0_hstraight; exact hJ24 ext s m hinv hl0 hfl hm)

theorem full_preprocess_m6_wp {Γ : Env} (hΓ : Γ.Sat searchDeps) :
    SpecEntry.Impl Γ full_preprocess_m6
      ⟨"full_preprocess_m6", [i64], [i64], Spec.preprocessSpec, true⟩ := by
  refine ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X hs => ?_⟩
  dsimp only [full_preprocess_m6] at xs Q m hs ⊢
  change Spec.preprocessSpec xs m Q X at hs
  rcases xs with ⟨h, ⟨⟩⟩
  unfold Spec.preprocessSpec at hs
  obtain ⟨c, ext, s, F0, R, rfl, hcfg, hext, _, ⟨hsp, hl0⟩, hm, hk_raw⟩ := M6HdrCfgContract.elim hs
  have hinv : FullM6HdrInv c F0 ext s := ⟨hcfg, hext, hsp⟩
  let hk : ∀ r c' ext' s' m',
      FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m' :=
    fun r c' ext' s' m' hc' hlen' hcfg' hext' hr hfl h20 h1 h10 hm' =>
      hk_raw (r, ()) c' ext' s' m' hc' hcfg' hext' trivial hlen'
        ⟨hr, hfl, h20, fun eq1 => let x := h1 eq1; ⟨x.1.sparse, x.2⟩, h10⟩ hm'
  dsimp only [Func.wp, full_preprocess_m6_body]
  refine step_load_oom_ret0 rfl hm (fun _ => ?_) (fun _ => ?_)
  · c0_hstraight
    exact hk 0#64 c ext s m (fullCfgCompat_refl c) hinv.sparse.lengths hinv.cfgOk hinv.extOk
      (.inl rfl) (Nat.le_refl _) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) hm
  · refine step_load_fuel_ret0 rfl hm (fun _ => ?_) (fun _ => ?_)
    · c0_hstraight
      exact hk 0#64 c ext s m (fullCfgCompat_refl c) hinv.sparse.lengths hinv.cfgOk hinv.extOk
        (.inl rfl) (Nat.le_refl _) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
        (fun h => absurd h (by decide)) hm
    · c0_hstraight
      rw [wp_load]; refine ⟨_, m6Hdr_load_off .search_ticks 600 rfl hm, ?_⟩
      refine search_call_lucky_late (by simp [vals]) (deps_has_lucky_late hΓ) hinv hm
        fun r1 ext1 s1 m1 hlen1 hext1 hr1 hfl1 h20_1 h02_1 h10_1 hm1 => ?_
      c0_hstraight
      have ⟨hok, hlen1', hcore1', hextlen1', hm1'⟩ :=
        m6Hdr_store_search_ticks_len s.scratch.search_ticks hlen1 hm1
      rw [wp_store]
      refine ⟨hok, ?_⟩
      c0_hstraight
      refine jnz_bv_eq rfl (fun eq20 => ?_) (fun ne20 => ?_)
      · c0_hstraight
        rw [eq20]
        exact hk 20#64 c ext1 _ _ (fullCfgCompat_refl c) hlen1' hinv.cfgOk hext1
          (.inr (.inr (.inr rfl))) (hcore1' ▸ hfl1) (fun _ => h20_1 eq20)
          (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm1'
      · c0_hstraight
        refine jnz_bv_eq rfl (fun eq10 => ?_) (fun ne10 => ?_)
        · c0_hstraight
          rw [eq10]
          exact hk 10#64 c ext1 _ _ (fullCfgCompat_refl c) hlen1' hinv.cfgOk hext1
            (.inr (.inr (.inl rfl))) (hcore1' ▸ hfl1) (fun h => absurd h (by decide))
            (fun h => absurd h (by decide)) (fun _ => hextlen1' ▸ h10_1 eq10) hm1'
        · have hr02 : r1 = 0#64 ∨ r1 = 2#64 := by
            rcases hr1 with rfl | rfl | rfl | rfl
            · exact .inl rfl
            · exact .inr rfl
            · exact absurd rfl ne10
            · exact absurd rfl ne20
          have ⟨hinv1, hl1⟩ := h02_1 hr02
          have hinv1' : FullM6HdrInv c F0 ext1
              (HdrWordField.search_ticks.set s1 s.scratch.search_ticks) :=
            fullM6HdrInv_upd_scrHdr .search_ticks rfl hinv1 s.scratch.search_ticks
          have hl1' :
              (HdrWordField.search_ticks.set s1 s.scratch.search_ticks).core.cur_level = 0 :=
            hcore1' ▸ hl1
          refine step_load_inc_ret20 rfl hm1' (fun hinc => ?_) (fun _ => ?_)
          · c0_hstraight
            exact hk 20#64 c ext1 _ _ (fullCfgCompat_refl c) hinv1'.sparse.lengths hinv1'.cfgOk
              hinv1'.extOk (.inr (.inr (.inr rfl))) (hcore1' ▸ hfl1)
              (fun _ => fullM6HdrInv_inconsistent_unsat hinv1' hinc)
              (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm1'
          · refine search_call_propagate (by simp [vals]) (deps_has_propagate hΓ) hinv1' hm1'
              fun r2 ext2 s2 m2 hinv2 _ hl2 hfl2 _ _ _ h1_2 _ hm2 => ?_
            have hl2_eq : s2.core.cur_level = 0 := hl2.trans hl1'
            have hfl2_le : s2.core.fuel.toNat ≤ s.core.fuel.toNat :=
              Nat.le_trans hfl2 (hcore1' ▸ hfl1)
            c0_hstraight
            refine jnz_bv_eq rfl (fun eq1 => ?_) (fun _ => ?_)
            · obtain ⟨F_cur, _, _, _, hw2, hconfl⟩ := h1_2 eq1
              c0_hstraight
              exact hk 20#64 c ext2 s2 m2 (fullCfgCompat_refl c) hinv2.sparse.lengths hinv2.cfgOk
                hinv2.extOk (.inr (.inr (.inr rfl))) hfl2_le
                (fun _ => level0_unsat_of_conflict_okW hw2 hl2_eq hconfl)
                (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm2
            · refine step_load_oom_ret0 rfl hm2 (fun _ => ?_) (fun _ => ?_)
              · c0_hstraight
                exact hk 0#64 c ext2 s2 m2 (fullCfgCompat_refl c) hinv2.sparse.lengths hinv2.cfgOk
                  hinv2.extOk (.inl rfl) hfl2_le (fun h => absurd h (by decide))
                  (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm2
              · refine step_load_fuel_ret0 rfl hm2 (fun _ => ?_) (fun _ => ?_)
                · c0_hstraight
                  exact hk 0#64 c ext2 s2 m2 (fullCfgCompat_refl c) hinv2.sparse.lengths
                    hinv2.cfgOk hinv2.extOk (.inl rfl) hfl2_le (fun h => absurd h (by decide))
                    (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm2
                · refine wp_join0 (fun m3 => ∃ ext3 s3, FullM6HdrInv c F0 ext3 s3 ∧
                      s3.core.cur_level = 0 ∧ s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                      (FullM6HdrMem c ext3 s3 ⋆ R) m3) ?_ ?_
                  · intro _ m3 ⟨ext3, s3, hinv3, hl3, hfl3, hm3⟩
                    exact preprocess_l25_wp hΓ hinv3 hl3 hfl3 hm3 hk
                  · intro J24 hJ24
                    exact preprocess_sweep_wp hΓ
                      (fun ext' s' m' hi hl hf hm' => hJ24 m' ⟨ext', s', hi, hl, hf, hm'⟩)
                      hinv2 hl2_eq hfl2_le hm2 hk

end LeanQbe.T.Examples.Kissat.Proof.Search