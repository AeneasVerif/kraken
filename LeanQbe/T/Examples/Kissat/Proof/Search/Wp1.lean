/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Search.Wp0

/-!
# Verification of `full_search_m6` (`Proof.Search.Wp1`)

Proves `full_search_m6_wp` (`Spec.searchSpec`) in `CanonicalEnv`
over `searchDeps` and `Γ.Has "full_simplify_m6" Spec.simplifySpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Search

open Std Std.Sat Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src LeanQbe.T.Examples.Kissat.Src.Search
open LeanQbe.T.Examples.Kissat.Proof LeanQbe.T.Examples.Kissat.Proof.Spec

/-! ## 1. Search Measure & Call/Fuel Helpers -/

private def searchMeasure (c : FullCfg) (s : FullState) : Nat :=
  s.core.fuel.toNat * (c.max_vars + 2) + (c.max_vars + 1 - s.core.trail_end)

private theorem searchMeasure_lt_of_fuel {c0 c1 : FullCfg} {s0 s1 : FullState}
    (hc : FullCfgCompat c0 c1) (hl1 : s1.LengthsOk c1)
    (hfl : s1.core.fuel.toNat < s0.core.fuel.toNat) :
    searchMeasure c1 s1 < searchMeasure c0 s0 := by
  unfold searchMeasure
  have h1 := hl1.core_ok.trail_end_le
  have h2 := hl1.core_ok.cur_vars_le
  rw [hc.max_vars] at h2 ⊢
  have hm : s1.core.fuel.toNat + 1 ≤ s0.core.fuel.toNat := hfl
  have hmul := Nat.mul_le_mul_right (c0.max_vars + 2) hm
  rw [Nat.add_mul, Nat.one_mul] at hmul
  omega

private theorem searchMeasure_lt_of_trail {c : FullCfg} {s0 s1 : FullState}
    (hl1 : s1.LengthsOk c) (hfl : s1.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hte : s0.core.trail_end < s1.core.trail_end) :
    searchMeasure c s1 < searchMeasure c s0 := by
  unfold searchMeasure
  have h1 := hl1.core_ok.trail_end_le
  have h2 := hl1.core_ok.cur_vars_le
  rcases Nat.eq_or_lt_of_le hfl with heq | hlt
  · rw [heq]; omega
  · have hm : s1.core.fuel.toNat + 1 ≤ s0.core.fuel.toNat := hlt
    have hmul := Nat.mul_le_mul_right (c.max_vars + 2) hm
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega

private abbrev decFuelExpr (h : Val i64) (k : Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 168)) fun p =>
    .load i64 (Arg.var p.fst) fun ld =>
      .let_ (op2 (.sub i64) (Arg.var ld) (Arg.imm 1)) fun q =>
        .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 168)) fun r =>
          .store (t := i64) (Arg.var q.fst) (Arg.var r.fst) k

private theorem step_dec_fuel {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {h : Val i64} {k : Expr Val Cont [i64]}
    (ha : h = c.hdr) (hinv : FullM6HdrInv c F0 ext s) (hfl : s.core.fuel ≠ 0#64)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : let s' := HdrWordField.fuel.set s (s.core.fuel - 1#64)
      FullM6HdrInv c F0 ext s' → s'.core.fuel.toNat < s.core.fuel.toNat →
      (FullM6HdrMem c ext s' ⋆ R) (storeMem m i64 (c.hdr + 168#64) (s.core.fuel - 1#64)) →
      wp Γ Q X k (storeMem m i64 (c.hdr + 168#64) (s.core.fuel - 1#64))) :
    wp Γ Q X (decFuelExpr h k) m := by
  dsimp only [decFuelExpr, op2]
  c0_hstraight
  rw [wp_load]; refine ⟨_, ha ▸ m6Hdr_load_off .fuel 168 rfl hm, ?_⟩
  c0_hstraight
  have ⟨hok, hinv', hm'⟩ := m6Hdr_store_fuel_sub1 hinv hm
  rw [wp_store]
  exact ⟨ha ▸ hok, ha ▸ hk hinv' (bv64_sub1_lt hfl) hm'⟩

private theorem search_call_simplify {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64, .bool, .bool]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost} (dp de : Bool)
    (hargs : vals args = (c.hdr, dp, de, ()))
    (hSimp : Γ.Has "full_simplify_m6" Spec.simplifySpec)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r c' ext' s' m',
      FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_simplify_m6" args k) m := by
  refine wp_call_of_spec args k (hSimp _ _ _ _ ?_)
  rw [hargs]
  unfold Spec.simplifySpec
  refine M6HdrCfgContract.intro hinv.cfgOk hinv.extOk hinv.sparse.lengths hinv.sparse hm ?_
  rintro ⟨r, ⟨⟩⟩ c' ext' s' m' hc' hcfg' hext' _ hlen' ⟨hr, hfl, h20, h1⟩ hm'
  exact hk r c' ext' s' m' hc' hlen' hcfg' hext' hr hfl h20
    (fun eq1 => let x := h1 eq1; ⟨⟨hcfg', hext', x.1⟩, x.2⟩) hm'

private theorem search_call_analyze_full {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hAna : Γ.Has "full_analyze_m6_hdr" m6HdrAnalyzeSpec)
    (hinvW : FullM6HdrInvW c F0 F_cur ext s) (hconfl : FullConflictOkW F_cur s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r ext' s' m',
      M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.fuel.toNat ≤ s.core.fuel.toNat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_analyze_m6_hdr" args k) m := by
  refine wp_call_of_spec args k (hAna _ _ _ _ ?_)
  rw [hargs]
  exact m6HdrAnalyzeSpec_of hinvW hconfl hm fun r ext' s' m' hext' hlen' hr _ hfl' _ h20 _ h1 hm' =>
    hk r ext' s' m' hext' hlen' hr h20 (fun eq1 => ⟨(h1 eq1).1.toInv, hfl'⟩) hm'

/-! ## 2. Post-Propagate Maintenance Stages -/

private abbrev searchDecideExpr (h : Val i64) (J_el0 : Cont []) : Expr Val Cont [i64] :=
  .call (as := [i64]) (bs := [i64]) "m6_hdr_decide_fid" (Arg.var h, ()) fun p30 =>
    .let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var p30.fst, Arg.imm 0, ())) fun p31 =>
      .jnz (Arg.var p31.fst)
        (.group (sig := [[i64]])
          (fun _ => Blocks.cons (fun p => .ret (Arg.var p.fst, ())) .nil)
          (fun Js =>
            .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 792)) fun p =>
              .load i64 (Arg.var p.fst) fun ld =>
                .let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p =>
                  .jnz (Arg.var p.fst) (.jump Js.fst (Arg.imm 10, ()))
                    (.jump Js.fst (Arg.imm 0, ()))))
        (.jump J_el0 ())

private abbrev searchElimExpr (h ls : Val i64) (J_pr0 : Cont []) : Expr Val Cont [i64] :=
  .group (sig := [[]])
    (fun _ => Blocks.cons (fun _ => .jump J_pr0 ()) .nil)
    (fun Js =>
      .group (sig := [[]])
        (fun _ => Blocks.cons (fun _ => searchDecideExpr h Js.fst) .nil)
        (fun Js6 =>
          .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 336)) fun p29 =>
            .load i64 (Arg.var p29.fst) fun ld =>
              .let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var ld, Arg.var ls, ())) fun p30 =>
                .jnz (Arg.var p30.fst)
                  (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 336)) fun p31 =>
                    .load i64 (Arg.var p31.fst) fun ld =>
                      .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 992)) fun p32 =>
                        .load i64 (Arg.var p32.fst) fun ld1 =>
                          .let_ (Op.mk (.cmp .uge i64 .bool rfl)
                            (Arg.var ld, Arg.var ld1, ())) fun p33 =>
                            .jnz (Arg.var p33.fst)
                              (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 488)) fun p34 =>
                                .load i64 (Arg.var p34.fst) fun ld =>
                                  .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 504)) fun p35 =>
                                    .load i64 (Arg.var p35.fst) fun ld2 =>
                                      .let_ (op2 (.add i64) (Arg.var ld) (Arg.var ld2)) fun p36 =>
                                        .let_ (Op.mk (.cmp .ugt i64 .bool rfl)
                                          (Arg.var p36.fst, Arg.imm 0, ())) fun p37 =>
                                          .jnz (Arg.var p37.fst)
                                            (decFuelExpr h
                                              (.call (as := [i64, .bool, .bool]) (bs := [i64])
                                                "full_simplify_m6"
                                                (Arg.var h, Arg.imm false, Arg.imm true, ())
                                                fun p =>
                                                .let_ (Op.mk (.cmp .eq i64 .bool rfl)
                                                  (Arg.var p.fst, Arg.imm 20, ())) fun p41 =>
                                                  .jnz (Arg.var p41.fst) (.ret (Arg.imm 20, ()))
                                                    (.let_ (Op.mk (.cmp .ne i64 .bool rfl)
                                                      (Arg.var p.fst, Arg.imm 1, ())) fun p =>
                                                      .jnz (Arg.var p.fst) (.ret (Arg.imm 0, ()))
                                                        (.jump Js.fst ()))))
                                            (.jump Js6.fst ()))
                              (.jump Js6.fst ()))
                  (.jump Js6.fst ())))

private abbrev searchProbeExpr (h ls : Val i64) (J_rp0 : Cont []) : Expr Val Cont [i64] :=
  .group (sig := [[]])
    (fun _ => Blocks.cons (fun _ => .jump J_rp0 ()) .nil)
    (fun Js =>
      .group (sig := [[]])
        (fun _ => Blocks.cons (fun _ => searchElimExpr h ls Js.fst) .nil)
        (fun Js5 =>
          .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 336)) fun p28 =>
            .load i64 (Arg.var p28.fst) fun ld =>
              .let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var ld, Arg.var ls, ())) fun p29 =>
                .jnz (Arg.var p29.fst)
                  (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 336)) fun p30 =>
                    .load i64 (Arg.var p30.fst) fun ld =>
                      .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 976)) fun p31 =>
                        .load i64 (Arg.var p31.fst) fun ld1 =>
                          .let_ (Op.mk (.cmp .ugt i64 .bool rfl)
                            (Arg.var ld, Arg.var ld1, ())) fun p32 =>
                            .jnz (Arg.var p32.fst)
                              (decFuelExpr h
                                (.call (as := [i64, .bool, .bool]) (bs := [i64])
                                  "full_simplify_m6"
                                  (Arg.var h, Arg.imm true, Arg.imm false, ()) fun p =>
                                  .let_ (Op.mk (.cmp .eq i64 .bool rfl)
                                    (Arg.var p.fst, Arg.imm 20, ())) fun p36 =>
                                    .jnz (Arg.var p36.fst) (.ret (Arg.imm 20, ()))
                                      (.let_ (Op.mk (.cmp .ne i64 .bool rfl)
                                        (Arg.var p.fst, Arg.imm 1, ())) fun p =>
                                        .jnz (Arg.var p.fst) (.ret (Arg.imm 0, ()))
                                          (.jump Js.fst ()))))
                              (.jump Js5.fst ()))
                  (.jump Js5.fst ())))

private abbrev searchRephaseExpr (h nr rc ls : Val i64) (J_ro : Cont [i64, i64]) :
    Expr Val Cont [i64] :=
  .group (sig := [[]])
    (fun _ => Blocks.cons (fun _ => .jump J_ro (Arg.var nr, Arg.var rc, ())) .nil)
    (fun Js =>
      .group (sig := [[]])
        (fun _ => Blocks.cons (fun _ => searchProbeExpr h ls Js.fst) .nil)
        (fun Js4 =>
          .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 552)) fun p27 =>
            .load i64 (Arg.var p27.fst) fun ld =>
              .let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p28 =>
                .jnz (Arg.var p28.fst)
                  (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 336)) fun p29 =>
                    .load i64 (Arg.var p29.fst) fun ld =>
                      .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 664)) fun p30 =>
                        .load i64 (Arg.var p30.fst) fun ld1 =>
                          .let_ (Op.mk (.cmp .ugt i64 .bool rfl)
                            (Arg.var ld, Arg.var ld1, ())) fun p31 =>
                            .jnz (Arg.var p31.fst)
                              (decFuelExpr h
                                (.call (as := [i64]) (bs := []) "full_rephase"
                                  (Arg.var h, ()) fun _ => .jump Js.fst ()))
                              (.jump Js4.fst ()))
                  (.jump Js4.fst ())))

private abbrev searchReorderExpr (h nr rc ls : Val i64) (J_rst : Cont [i64, i64]) :
    Expr Val Cont [i64] :=
  .group (sig := [[i64, i64]])
    (fun _ => Blocks.cons (fun p => .jump J_rst (Arg.var p.fst, Arg.var p.snd.fst, ())) .nil)
    (fun Js =>
      .group (sig := [[]])
        (fun _ => Blocks.cons (fun _ => searchRephaseExpr h nr rc ls Js.fst) .nil)
        (fun Js3 =>
          .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 160)) fun p26 =>
            .load i64 (Arg.var p26.fst) fun ld =>
              .let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p27 =>
                .jnz (Arg.var p27.fst)
                  (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 336)) fun p28 =>
                    .load i64 (Arg.var p28.fst) fun ld =>
                      .let_ (Op.mk (.cmp .uge i64 .bool rfl)
                        (Arg.var ld, Arg.var nr, ())) fun p29 =>
                        .jnz (Arg.var p29.fst)
                          (.let_ (op2 (.add i64) (Arg.var rc) (Arg.imm 1)) fun p30 =>
                            .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 336)) fun p31 =>
                              .load i64 (Arg.var p31.fst) fun ld =>
                                .let_ (op2 (.mul i64) (Arg.imm 10000) (Arg.var p30.fst)) fun p32 =>
                                  .let_ (op2 (.add i64) (Arg.var ld) (Arg.var p32.fst)) fun p33 =>
                                    decFuelExpr h
                                      (.call (as := [i64, i64]) (bs := [i64]) "full_reorder_m6"
                                        (Arg.var h, Arg.imm 256, ()) fun _ =>
                                        .jump Js.fst (Arg.var p33.fst, Arg.var p30.fst, ())))
                          (.jump Js3.fst ()))
                  (.jump Js3.fst ())))

private abbrev searchRestartExpr (h nr rc ls : Val i64) (J_nr_rc : Cont [i64, i64]) :
    Expr Val Cont [i64] :=
  .group (sig := [[i64, i64]])
    (fun _ => Blocks.cons (fun p => .jump J_nr_rc (Arg.var p.fst, Arg.var p.snd.fst, ())) .nil)
    (fun Js =>
      .call (as := [i64]) (bs := [i64]) "full_restart_due" (Arg.var h, ()) fun p24 =>
        .let_ (Op.mk (.cmp .ne i64 .bool rfl) (Arg.var p24.fst, Arg.imm 0, ())) fun p25 =>
          .jnz (Arg.var p25.fst)
            (decFuelExpr h
              (.call (as := [i64]) (bs := []) "full_restart" (Arg.var h, ()) fun _ =>
                .jump Js.fst (Arg.var nr, Arg.var rc, ())))
            (searchReorderExpr h nr rc ls Js.fst))

private abbrev searchModeExpr (h nr rc ls : Val i64) (J_outer : Cont [i64, i64, i64]) :
    Expr Val Cont [i64] :=
  .group (sig := [[i64, i64]])
    (fun _ => Blocks.cons (fun p =>
      .jump J_outer (Arg.var p.fst, Arg.var p.snd.fst, Arg.var ls, ())) .nil)
    (fun Js =>
      .group (sig := [[i32]])
        (fun _ => Blocks.cons (fun p22 =>
          .let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var p22.fst, Arg.imm 0, ())) fun p23 =>
            .jnz (Arg.var p23.fst)
              (decFuelExpr h
                (.call (as := [i64]) (bs := []) "full_switch_mode_m7" (Arg.var h, ()) fun _ =>
                  .jump Js.fst (Arg.var nr, Arg.var rc, ())))
              (searchRestartExpr h nr rc ls Js.fst)) .nil)
        (fun JsM =>
          .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 552)) fun p22 =>
            .load i64 (Arg.var p22.fst) fun ld =>
              .let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p23 =>
                .jnz (Arg.var p23.fst)
                  (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 336)) fun p24 =>
                    .load i64 (Arg.var p24.fst) fun ld =>
                      .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 576)) fun p =>
                        .load i64 (Arg.var p.fst) fun ld1 =>
                          .let_ (Op.mk (.cmp .uge i64 .bool rfl)
                            (Arg.var ld, Arg.var ld1, ())) fun p =>
                            .let_ (Op.mk (.ofBool 32) (Arg.var p.fst, ())) fun p =>
                              .jump JsM.fst (Arg.var p.fst, ()))
                  (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 600)) fun p24 =>
                    .load i64 (Arg.var p24.fst) fun ld =>
                      .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 584)) fun p =>
                        .load i64 (Arg.var p.fst) fun ld1 =>
                          .let_ (Op.mk (.cmp .uge i64 .bool rfl)
                            (Arg.var ld, Arg.var ld1, ())) fun p =>
                            .let_ (Op.mk (.ofBool 32) (Arg.var p.fst, ())) fun p =>
                              .jump JsM.fst (Arg.var p.fst, ()))))

private abbrev searchPostPropExpr (h nr rc ls : Val i64) (J_loop : Cont [i64, i64, i64]) :
    Expr Val Cont [i64] :=
  .group (sig := [[i64, i64, i64]])
    (fun _ => Blocks.cons (fun p =>
      .jump J_loop (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p.snd.snd.fst, ())) .nil)
    (fun Js =>
      .group (sig := [[]])
        (fun _ => Blocks.cons (fun _ => searchModeExpr h nr rc ls Js.fst) .nil)
        (fun Js1 =>
          .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 496)) fun p21 =>
            .load i64 (Arg.var p21.fst) fun ld =>
              .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p22 =>
                .jnz (Arg.var p22.fst)
                  (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 336)) fun p23 =>
                    .load i64 (Arg.var p23.fst) fun ld =>
                      .let_ (op2 (.add i64) (Arg.var h) (Arg.imm 680)) fun p24 =>
                        .load i64 (Arg.var p24.fst) fun ld1 =>
                          .let_ (Op.mk (.cmp .uge i64 .bool rfl)
                            (Arg.var ld, Arg.var ld1, ())) fun p25 =>
                            .jnz (Arg.var p25.fst)
                              (.let_ (op2 (.add i64) (Arg.var h) (Arg.imm 336)) fun p26 =>
                                .load i64 (Arg.var p26.fst) fun ld =>
                                  decFuelExpr h
                                    (.call (as := [i64, .bool]) (bs := [i64]) "full_reduce_m6"
                                      (Arg.var h, Arg.imm false, ()) fun p =>
                                      .let_ (Op.mk (.cmp .eq i64 .bool rfl)
                                        (Arg.var p.fst, Arg.imm 20, ())) fun p30 =>
                                        .jnz (Arg.var p30.fst) (.ret (Arg.imm 20, ()))
                                          (.let_ (Op.mk (.cmp .ne i64 .bool rfl)
                                            (Arg.var p.fst, Arg.imm 1, ())) fun p =>
                                            .jnz (Arg.var p.fst) (.ret (Arg.imm 0, ()))
                                              (.jump Js.fst
                                                (Arg.var nr, Arg.var rc, Arg.var ld, ())))))
                              (.jump Js1.fst ()))
                  (.jump Js1.fst ())))

private theorem search_decide_wp {Γ : Env} (hΓ : Γ.Sat searchDeps)
    {c0 c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s0 s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost} {J_el0 : Cont []}
    (hc : FullCfgCompat c0 c) (hinv : FullM6HdrInv c F0 ext s)
    (hfl_le : s.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hte_le : s0.core.trail_end ≤ s.core.trail_end)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hBack : ∀ c' ext' s' m',
      FullCfgCompat c0 c' → FullM6HdrInv c' F0 ext' s' →
      searchMeasure c' s' < searchMeasure c s0 → (FullM6HdrMem c' ext' s' ⋆ R) m' → J_el0 () m')
    (hk : ∀ r c' ext' s' m',
      FullCfgCompat c0 c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (searchDecideExpr c0.hdr J_el0) m := by
  dsimp only [searchDecideExpr]
  refine search_call_decide (by simp [vals, hc.hdr]) (deps_has_decide hΓ) hinv hm
    fun r ext' s' m' hinv' hfl' hr h1 hm' => ?_
  c0_hstraight
  refine jnz_bv_eq rfl (fun _ => ?_) (fun ne0 => ?_)
  · refine wp_join_state1 (fun rv : BitVec 64 => rv)
      (fun rv m'' => m'' = m' ∧ (rv = 0#64 ∨ rv = 10#64)) ?_ ?_
    · intro _ rv m'' ⟨hm'', hrv⟩
      rw [hm'']
      c0_hstraight
      exact hk rv c ext' s' m' hc hinv'.sparse.lengths hinv'.cfgOk hinv'.extOk
        (by rcases hrv with rfl | rfl; exact .inl rfl; exact .inr (.inl rfl))
        (fun h => by rcases hrv with rfl | rfl <;> exact absurd h (by decide))
        (fun _ => hinv'.sparse.2.2.2.1.2) hm'
    · intro J hJ
      c0_hstraight
      rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .unassigned 792 rfl hm', ?_⟩
      c0_hstraight
      refine jnz_bv_eq rfl
        (fun _ => by c0_hstraight; exact hJ 10#64 m' ⟨rfl, .inr rfl⟩)
        (fun _ => by c0_hstraight; exact hJ 0#64 m' ⟨rfl, .inl rfl⟩)
  · have ⟨_, hte'⟩ := h1 (Or.resolve_left hr ne0)
    have hlt : searchMeasure c s' < searchMeasure c s0 :=
      searchMeasure_lt_of_trail hinv'.sparse.lengths (hfl' ▸ hfl_le) (by omega)
    c0_hstraight
    exact hBack c ext' s' m' hc hinv' hlt hm'

private theorem search_elim_wp {Γ : Env} (hΓ : Γ.Sat searchDeps)
    (hSimp : Γ.Has "full_simplify_m6" Spec.simplifySpec)
    {c0 c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s0 s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost} {ls : Val i64} {J_pr0 : Cont []}
    (hc : FullCfgCompat c0 c) (hinv : FullM6HdrInv c F0 ext s) (hfl0 : s.core.fuel ≠ 0#64)
    (hfl_le : s.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hte_le : s0.core.trail_end ≤ s.core.trail_end)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hBack : ∀ c' ext' s' m',
      FullCfgCompat c0 c' → FullM6HdrInv c' F0 ext' s' →
      searchMeasure c' s' < searchMeasure c s0 → (FullM6HdrMem c' ext' s' ⋆ R) m' → J_pr0 () m')
    (hk : ∀ r c' ext' s' m',
      FullCfgCompat c0 c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (searchElimExpr c0.hdr ls J_pr0) m := by
  dsimp only [searchElimExpr]
  refine wp_join0 (fun m' => ∃ c' ext' s', FullCfgCompat c0 c' ∧ FullM6HdrInv c' F0 ext' s' ∧
      searchMeasure c' s' < searchMeasure c s0 ∧ (FullM6HdrMem c' ext' s' ⋆ R) m') ?_ ?_
  · intro _ m' ⟨c', ext', s', hc', hinv', hlt, hm'⟩
    c0_hstraight
    exact hBack c' ext' s' m' hc' hinv' hlt hm'
  · intro Jel hJel
    refine wp_join0 (fun m' => m' = m) ?_ ?_
    · intro _ m' hm_eq; subst hm_eq
      exact search_decide_wp hΓ hc hinv hfl_le hte_le hm
        (fun c' ext' s' m'' hc' hinv' hlt hm'' => hJel m'' ⟨c', ext', s', hc', hinv', hlt, hm''⟩)
        hk
    · intro J6 hJ6
      c0_hstraight
      rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .conflicts 336 rfl hm, ?_⟩
      c0_hstraight
      refine jnz_bv_ne rfl (fun _ => ?_) (fun _ => by c0_hstraight; exact hJ6 m rfl)
      c0_hstraight
      rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .conflicts 336 rfl hm, ?_⟩
      c0_hstraight
      rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .elim_limit 992 rfl hm, ?_⟩
      c0_hstraight
      refine jnz_bv_ule rfl (fun _ => ?_) (fun _ => by c0_hstraight; exact hJ6 m rfl)
      c0_hstraight
      rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .num_irred 488 rfl hm, ?_⟩
      c0_hstraight
      rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .num_binary 504 rfl hm, ?_⟩
      c0_hstraight
      refine jnz_bv_ult rfl (fun _ => ?_) (fun _ => by c0_hstraight; exact hJ6 m rfl)
      refine step_dec_fuel hc.hdr.symm hinv hfl0 hm fun hinv1 hfl1 hm1 => ?_
      refine search_call_simplify false true (by simp [vals, hc.hdr]) hSimp hinv1 hm1
        fun r c' ext' s' m' hc' hlen' hcfg' hext' _ hfl' h20 h1 hm' => ?_
      c0_hstraight
      refine jnz_bv_eq rfl (fun eq20 => ?_) (fun _ => ?_)
      · c0_hstraight
        exact hk 20#64 c' ext' s' m' (fullCfgCompat_trans hc hc') hlen' hcfg' hext'
          (.inr (.inr rfl)) (fun _ => h20 eq20) (fun h => absurd h (by decide)) hm'
      · c0_hstraight
        refine jnz_bv_ne rfl (fun _ => ?_) (fun eq1 => ?_) <;> c0_hstraight
        · exact hk 0#64 c' ext' s' m' (fullCfgCompat_trans hc hc') hlen' hcfg' hext'
            (.inl rfl) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm'
        · have ⟨hinv', _⟩ := h1 eq1
          have hlt := searchMeasure_lt_of_fuel hc' hlen'
            (Nat.lt_of_le_of_lt hfl' (Nat.lt_of_lt_of_le hfl1 hfl_le))
          exact hJel m' ⟨c', ext', s', fullCfgCompat_trans hc hc', hinv', hlt, hm'⟩

private theorem search_probe_wp {Γ : Env} (hΓ : Γ.Sat searchDeps)
    (hSimp : Γ.Has "full_simplify_m6" Spec.simplifySpec)
    {c0 c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s0 s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost} {ls : Val i64} {J_rp0 : Cont []}
    (hc : FullCfgCompat c0 c) (hinv : FullM6HdrInv c F0 ext s) (hfl0 : s.core.fuel ≠ 0#64)
    (hfl_le : s.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hte_le : s0.core.trail_end ≤ s.core.trail_end)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hBack : ∀ c' ext' s' m',
      FullCfgCompat c0 c' → FullM6HdrInv c' F0 ext' s' →
      searchMeasure c' s' < searchMeasure c s0 → (FullM6HdrMem c' ext' s' ⋆ R) m' → J_rp0 () m')
    (hk : ∀ r c' ext' s' m',
      FullCfgCompat c0 c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (searchProbeExpr c0.hdr ls J_rp0) m := by
  dsimp only [searchProbeExpr]
  refine wp_join0 (fun m' => ∃ c' ext' s', FullCfgCompat c0 c' ∧ FullM6HdrInv c' F0 ext' s' ∧
      searchMeasure c' s' < searchMeasure c s0 ∧ (FullM6HdrMem c' ext' s' ⋆ R) m') ?_ ?_
  · intro _ m' ⟨c', ext', s', hc', hinv', hlt, hm'⟩
    c0_hstraight
    exact hBack c' ext' s' m' hc' hinv' hlt hm'
  · intro Jpr hJpr
    refine wp_join0 (fun m' => m' = m) ?_ ?_
    · intro _ m' hm_eq; subst hm_eq
      exact search_elim_wp hΓ hSimp hc hinv hfl0 hfl_le hte_le hm
        (fun c' ext' s' m'' hc' hinv' hlt hm'' => hJpr m'' ⟨c', ext', s', hc', hinv', hlt, hm''⟩)
        hk
    · intro J5 hJ5
      c0_hstraight
      rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .conflicts 336 rfl hm, ?_⟩
      c0_hstraight
      refine jnz_bv_ne rfl (fun _ => ?_) (fun _ => by c0_hstraight; exact hJ5 m rfl)
      c0_hstraight
      rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .conflicts 336 rfl hm, ?_⟩
      c0_hstraight
      rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .probe_limit 976 rfl hm, ?_⟩
      c0_hstraight
      refine jnz_bv_ult rfl (fun _ => ?_) (fun _ => by c0_hstraight; exact hJ5 m rfl)
      refine step_dec_fuel hc.hdr.symm hinv hfl0 hm fun hinv1 hfl1 hm1 => ?_
      refine search_call_simplify true false (by simp [vals, hc.hdr]) hSimp hinv1 hm1
        fun r c' ext' s' m' hc' hlen' hcfg' hext' _ hfl' h20 h1 hm' => ?_
      c0_hstraight
      refine jnz_bv_eq rfl (fun eq20 => ?_) (fun _ => ?_)
      · c0_hstraight
        exact hk 20#64 c' ext' s' m' (fullCfgCompat_trans hc hc') hlen' hcfg' hext'
          (.inr (.inr rfl)) (fun _ => h20 eq20) (fun h => absurd h (by decide)) hm'
      · c0_hstraight
        refine jnz_bv_ne rfl (fun _ => ?_) (fun eq1 => ?_) <;> c0_hstraight
        · exact hk 0#64 c' ext' s' m' (fullCfgCompat_trans hc hc') hlen' hcfg' hext'
            (.inl rfl) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm'
        · have ⟨hinv', _⟩ := h1 eq1
          have hlt := searchMeasure_lt_of_fuel hc' hlen'
            (Nat.lt_of_le_of_lt hfl' (Nat.lt_of_lt_of_le hfl1 hfl_le))
          exact hJpr m' ⟨c', ext', s', fullCfgCompat_trans hc hc', hinv', hlt, hm'⟩

private theorem search_rephase_wp {Γ : Env} (hΓ : Γ.Sat searchDeps)
    (hSimp : Γ.Has "full_simplify_m6" Spec.simplifySpec)
    {c0 c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s0 s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {nr rc ls : Val i64} {J_ro : Cont [i64, i64]}
    (hc : FullCfgCompat c0 c) (hinv : FullM6HdrInv c F0 ext s) (hfl0 : s.core.fuel ≠ 0#64)
    (hfl_le : s.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hte_le : s0.core.trail_end ≤ s.core.trail_end)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hBack : ∀ c' ext' s' m' nr' rc',
      FullCfgCompat c0 c' → FullM6HdrInv c' F0 ext' s' →
      searchMeasure c' s' < searchMeasure c s0 → (FullM6HdrMem c' ext' s' ⋆ R) m' →
      J_ro (nr', rc', ()) m')
    (hk : ∀ r c' ext' s' m',
      FullCfgCompat c0 c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (searchRephaseExpr c0.hdr nr rc ls J_ro) m := by
  dsimp only [searchRephaseExpr]
  refine wp_join0 (fun m' => ∃ c' ext' s', FullCfgCompat c0 c' ∧ FullM6HdrInv c' F0 ext' s' ∧
      searchMeasure c' s' < searchMeasure c s0 ∧ (FullM6HdrMem c' ext' s' ⋆ R) m') ?_ ?_
  · intro _ m' ⟨c', ext', s', hc', hinv', hlt, hm'⟩
    c0_hstraight
    exact hBack c' ext' s' m' nr rc hc' hinv' hlt hm'
  · intro Jrp hJrp
    refine wp_join0 (fun m' => m' = m) ?_ ?_
    · intro _ m' hm_eq; subst hm_eq
      exact search_probe_wp hΓ hSimp hc hinv hfl0 hfl_le hte_le hm
        (fun c' ext' s' m'' hc' hinv' hlt hm'' => hJrp m'' ⟨c', ext', s', hc', hinv', hlt, hm''⟩)
        hk
    · intro J4 hJ4
      c0_hstraight
      rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .stable 552 rfl hm, ?_⟩
      c0_hstraight
      refine jnz_bv_ne rfl (fun _ => ?_) (fun _ => by c0_hstraight; exact hJ4 m rfl)
      c0_hstraight
      rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .conflicts 336 rfl hm, ?_⟩
      c0_hstraight
      rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .rephase_limit 664 rfl hm, ?_⟩
      c0_hstraight
      refine jnz_bv_ult rfl (fun _ => ?_) (fun _ => by c0_hstraight; exact hJ4 m rfl)
      refine step_dec_fuel hc.hdr.symm hinv hfl0 hm fun hinv1 hfl1 hm1 => ?_
      refine search_call_rephase (by simp [vals, hc.hdr]) (deps_has_rephase hΓ) hinv1 hm1
        fun ext' s' m' hinv' _ hfl' hm' => ?_
      have hlt := searchMeasure_lt_of_fuel (fullCfgCompat_refl c) hinv'.sparse.lengths
        (Nat.lt_of_le_of_lt hfl' (Nat.lt_of_lt_of_le hfl1 hfl_le))
      c0_hstraight
      exact hJrp m' ⟨c, ext', s', hc, hinv', hlt, hm'⟩

private theorem search_reorder_wp {Γ : Env} (hΓ : Γ.Sat searchDeps)
    (hSimp : Γ.Has "full_simplify_m6" Spec.simplifySpec)
    {c0 c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s0 s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {nr rc ls : Val i64} {J_rst : Cont [i64, i64]}
    (hc : FullCfgCompat c0 c) (hinv : FullM6HdrInv c F0 ext s) (hfl0 : s.core.fuel ≠ 0#64)
    (hfl_le : s.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hte_le : s0.core.trail_end ≤ s.core.trail_end)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hBack : ∀ c' ext' s' m' nr' rc',
      FullCfgCompat c0 c' → FullM6HdrInv c' F0 ext' s' →
      searchMeasure c' s' < searchMeasure c s0 → (FullM6HdrMem c' ext' s' ⋆ R) m' →
      J_rst (nr', rc', ()) m')
    (hk : ∀ r c' ext' s' m',
      FullCfgCompat c0 c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (searchReorderExpr c0.hdr nr rc ls J_rst) m := by
  dsimp only [searchReorderExpr]
  refine wp_join_state (fun st : BitVec 64 × BitVec 64 => (st.1, st.2, ()))
    (fun st m' => ∃ c' ext' s', FullCfgCompat c0 c' ∧ FullM6HdrInv c' F0 ext' s' ∧
      searchMeasure c' s' < searchMeasure c s0 ∧ (FullM6HdrMem c' ext' s' ⋆ R) m') ?_ ?_
  · intro _ ⟨nr', rc'⟩ m' ⟨c', ext', s', hc', hinv', hlt, hm'⟩
    c0_hstraight
    exact hBack c' ext' s' m' nr' rc' hc' hinv' hlt hm'
  · intro Jro hJro
    refine wp_join0 (fun m' => m' = m) ?_ ?_
    · intro _ m' hm_eq; subst hm_eq
      exact search_rephase_wp hΓ hSimp hc hinv hfl0 hfl_le hte_le hm
        (fun c' ext' s' m'' nr' rc' hc' hinv' hlt hm'' =>
          hJro (nr', rc') m'' ⟨c', ext', s', hc', hinv', hlt, hm''⟩) hk
    · intro J3 hJ3
      c0_hstraight
      rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .cur_level 160 rfl hm, ?_⟩
      c0_hstraight
      refine jnz_bv_eq rfl (fun _ => ?_) (fun _ => by c0_hstraight; exact hJ3 m rfl)
      c0_hstraight
      rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .conflicts 336 rfl hm, ?_⟩
      c0_hstraight
      refine jnz_bv_ule rfl (fun _ => ?_) (fun _ => by c0_hstraight; exact hJ3 m rfl)
      c0_hstraight
      rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .conflicts 336 rfl hm, ?_⟩
      c0_hstraight
      refine step_dec_fuel hc.hdr.symm hinv hfl0 hm fun hinv1 hfl1 hm1 => ?_
      refine search_call_reorder 256#64 (by simp [vals, hc.hdr]) (deps_has_reorder hΓ) hinv1 hm1
        fun _ s' m' hinv' _ hfl' hm' => ?_
      have hlt := searchMeasure_lt_of_fuel (fullCfgCompat_refl c) hinv'.sparse.lengths
        (hfl' ▸ Nat.lt_of_lt_of_le hfl1 hfl_le)
      c0_hstraight
      exact hJro (_, _) m' ⟨c, ext, s', hc, hinv', hlt, hm'⟩

private theorem search_restart_wp {Γ : Env} (hΓ : Γ.Sat searchDeps)
    (hSimp : Γ.Has "full_simplify_m6" Spec.simplifySpec)
    {c0 c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s0 s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {nr rc ls : Val i64} {J_nr_rc : Cont [i64, i64]}
    (hc : FullCfgCompat c0 c) (hinv : FullM6HdrInv c F0 ext s) (hfl0 : s.core.fuel ≠ 0#64)
    (hfl_le : s.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hte_le : s0.core.trail_end ≤ s.core.trail_end)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hBack : ∀ c' ext' s' m' nr' rc',
      FullCfgCompat c0 c' → FullM6HdrInv c' F0 ext' s' →
      searchMeasure c' s' < searchMeasure c s0 → (FullM6HdrMem c' ext' s' ⋆ R) m' →
      J_nr_rc (nr', rc', ()) m')
    (hk : ∀ r c' ext' s' m',
      FullCfgCompat c0 c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (searchRestartExpr c0.hdr nr rc ls J_nr_rc) m := by
  dsimp only [searchRestartExpr]
  refine wp_join_state (fun st : BitVec 64 × BitVec 64 => (st.1, st.2, ()))
    (fun st m' => ∃ c' ext' s', FullCfgCompat c0 c' ∧ FullM6HdrInv c' F0 ext' s' ∧
      searchMeasure c' s' < searchMeasure c s0 ∧ (FullM6HdrMem c' ext' s' ⋆ R) m') ?_ ?_
  · intro _ ⟨nr', rc'⟩ m' ⟨c', ext', s', hc', hinv', hlt, hm'⟩
    c0_hstraight
    exact hBack c' ext' s' m' nr' rc' hc' hinv' hlt hm'
  · intro Jrst hJrst
    refine search_call_restart_due (by simp [vals, hc.hdr]) (deps_has_restart_due hΓ) hinv hm
      fun r s1 m1 hinv1 _ _ hte1 hfl1 _ hm1 => ?_
    c0_hstraight
    refine jnz_bv_ne rfl (fun _ => ?_) (fun _ => ?_)
    · refine step_dec_fuel hc.hdr.symm hinv1 (hfl1 ▸ hfl0) hm1 fun hinv2 hfl2 hm2 => ?_
      refine search_call_restart (by simp [vals, hc.hdr]) (deps_has_restart hΓ) hinv2 hm2
        fun s' m' hinv' hfl' _ hm' => ?_
      have hlt := searchMeasure_lt_of_fuel (fullCfgCompat_refl c) hinv'.sparse.lengths
        (hfl' ▸ Nat.lt_of_lt_of_le hfl2 (hfl1 ▸ hfl_le))
      c0_hstraight
      exact hJrst (nr, rc) m' ⟨c, ext, s', hc, hinv', hlt, hm'⟩
    · exact search_reorder_wp hΓ hSimp hc hinv1 (hfl1 ▸ hfl0) (hfl1 ▸ hfl_le) (hte1 ▸ hte_le) hm1
        (fun c' ext' s' m'' nr' rc' hc' hinv' hlt hm'' =>
          hJrst (nr', rc') m'' ⟨c', ext', s', hc', hinv', hlt, hm''⟩) hk

private theorem search_mode_wp {Γ : Env} (hΓ : Γ.Sat searchDeps)
    (hSimp : Γ.Has "full_simplify_m6" Spec.simplifySpec)
    {c0 c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s0 s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {nr rc ls : Val i64} {J_outer : Cont [i64, i64, i64]}
    (hc : FullCfgCompat c0 c) (hinv : FullM6HdrInv c F0 ext s) (hfl0 : s.core.fuel ≠ 0#64)
    (hfl_le : s.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hte_le : s0.core.trail_end ≤ s.core.trail_end)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hBack : ∀ c' ext' s' m' nr' rc' ls',
      FullCfgCompat c0 c' → FullM6HdrInv c' F0 ext' s' →
      searchMeasure c' s' < searchMeasure c s0 → (FullM6HdrMem c' ext' s' ⋆ R) m' →
      J_outer (nr', rc', ls', ()) m')
    (hk : ∀ r c' ext' s' m',
      FullCfgCompat c0 c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (searchModeExpr c0.hdr nr rc ls J_outer) m := by
  dsimp only [searchModeExpr]
  refine wp_join_state (fun st : BitVec 64 × BitVec 64 => (st.1, st.2, ()))
    (fun st m' => ∃ c' ext' s', FullCfgCompat c0 c' ∧ FullM6HdrInv c' F0 ext' s' ∧
      searchMeasure c' s' < searchMeasure c s0 ∧ (FullM6HdrMem c' ext' s' ⋆ R) m') ?_ ?_
  · intro _ ⟨nr', rc'⟩ m' ⟨c', ext', s', hc', hinv', hlt, hm'⟩
    c0_hstraight
    exact hBack c' ext' s' m' nr' rc' ls hc' hinv' hlt hm'
  · intro Jnr hJnr
    refine wp_join_state1 (fun b : BitVec 32 => b) (fun _ m' => m' = m) ?_ ?_
    · intro _ b m' hm_eq; subst hm_eq
      c0_hstraight
      refine wp_jnz_decide (b ≠ 0#32)
        (by cases hb : (b == 0#32) <;> simp_all [bne, beq_iff_eq])
        (fun _ => ?_) (fun _ => ?_)
      · refine step_dec_fuel hc.hdr.symm hinv hfl0 hm fun hinv1 hfl1 hm1 => ?_
        refine search_call_switch_mode (by simp [vals, hc.hdr]) (deps_has_switch_mode hΓ)
          hinv1 hm1 fun ext' s' m' hinv' hcore' hm' => ?_
        have hfl_lt : s'.core.fuel.toNat < s0.core.fuel.toNat := by
          rw [hcore']; exact Nat.lt_of_lt_of_le hfl1 hfl_le
        have hlt := searchMeasure_lt_of_fuel (fullCfgCompat_refl c) hinv'.sparse.lengths hfl_lt
        c0_hstraight
        exact hJnr (nr, rc) m' ⟨c, ext', s', hc, hinv', hlt, hm'⟩
      · exact search_restart_wp hΓ hSimp hc hinv hfl0 hfl_le hte_le hm
          (fun c' ext' s' m'' nr' rc' hc' hinv' hlt hm'' =>
            hJnr (nr', rc') m'' ⟨c', ext', s', hc', hinv', hlt, hm''⟩) hk
    · intro JM hJM
      c0_hstraight
      rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .stable 552 rfl hm, ?_⟩
      c0_hstraight
      refine jnz_bv_eq rfl (fun _ => ?_) (fun _ => ?_)
      · c0_hstraight
        rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .conflicts 336 rfl hm, ?_⟩
        c0_hstraight
        rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .mode_confl_lim 576 rfl hm, ?_⟩
        c0_hstraight
        exact hJM _ m rfl
      · c0_hstraight
        rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .search_ticks 600 rfl hm, ?_⟩
        c0_hstraight
        rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .mode_tick_lim 584 rfl hm, ?_⟩
        c0_hstraight
        exact hJM _ m rfl

private theorem search_post_prop_wp {Γ : Env} (hΓ : Γ.Sat searchDeps)
    (hSimp : Γ.Has "full_simplify_m6" Spec.simplifySpec)
    {c0 c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s0 s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {nr rc ls : Val i64} {J_loop : Cont [i64, i64, i64]}
    (hc : FullCfgCompat c0 c) (hinv : FullM6HdrInv c F0 ext s) (hfl0 : s.core.fuel ≠ 0#64)
    (hfl_le : s.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hte_le : s0.core.trail_end ≤ s.core.trail_end)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hBack : ∀ c' ext' s' m' nr' rc' ls',
      FullCfgCompat c0 c' → FullM6HdrInv c' F0 ext' s' →
      searchMeasure c' s' < searchMeasure c s0 → (FullM6HdrMem c' ext' s' ⋆ R) m' →
      J_loop (nr', rc', ls', ()) m')
    (hk : ∀ r c' ext' s' m',
      FullCfgCompat c0 c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (searchPostPropExpr c0.hdr nr rc ls J_loop) m := by
  dsimp only [searchPostPropExpr]
  refine wp_join_state (fun st : BitVec 64 × BitVec 64 × BitVec 64 => (st.1, st.2.1, st.2.2, ()))
    (fun st m' => ∃ c' ext' s', FullCfgCompat c0 c' ∧ FullM6HdrInv c' F0 ext' s' ∧
      searchMeasure c' s' < searchMeasure c s0 ∧ (FullM6HdrMem c' ext' s' ⋆ R) m') ?_ ?_
  · intro _ ⟨nr', rc', ls'⟩ m' ⟨c', ext', s', hc', hinv', hlt, hm'⟩
    c0_hstraight
    exact hBack c' ext' s' m' nr' rc' ls' hc' hinv' hlt hm'
  · intro Jout hJout
    refine wp_join0 (fun m' => m' = m) ?_ ?_
    · intro _ m' hm_eq; subst hm_eq
      exact search_mode_wp hΓ hSimp hc hinv hfl0 hfl_le hte_le hm
        (fun c' ext' s' m'' nr' rc' ls' hc' hinv' hlt hm'' =>
          hJout (nr', rc', ls') m'' ⟨c', ext', s', hc', hinv', hlt, hm''⟩) hk
    · intro J1 hJ1
      c0_hstraight
      rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .num_redundant 496 rfl hm, ?_⟩
      c0_hstraight
      refine jnz_bv_ult rfl (fun _ => ?_) (fun _ => by c0_hstraight; exact hJ1 m rfl)
      c0_hstraight
      rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .conflicts 336 rfl hm, ?_⟩
      c0_hstraight
      rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .reduce_limit 680 rfl hm, ?_⟩
      c0_hstraight
      refine jnz_bv_ule rfl (fun _ => ?_) (fun _ => by c0_hstraight; exact hJ1 m rfl)
      c0_hstraight
      rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .conflicts 336 rfl hm, ?_⟩
      refine step_dec_fuel hc.hdr.symm hinv hfl0 hm fun hinv1 hfl1 hm1 => ?_
      refine search_call_reduce (by simp [vals, hc.hdr]) (deps_has_reduce hΓ) hinv1 hm1
        fun r c' ext' s' m' hc' hinv' _ _ hfl' h20 _ hm' => ?_
      c0_hstraight
      refine jnz_bv_eq rfl (fun eq20 => ?_) (fun _ => ?_)
      · c0_hstraight
        exact hk 20#64 c' ext' s' m' (fullCfgCompat_trans hc hc') hinv'.sparse.lengths hinv'.cfgOk
          hinv'.extOk (.inr (.inr rfl)) (fun _ => h20 eq20) (fun h => absurd h (by decide)) hm'
      · c0_hstraight
        refine jnz_bv_ne rfl (fun _ => ?_) (fun _ => ?_) <;> c0_hstraight
        · exact hk 0#64 c' ext' s' m' (fullCfgCompat_trans hc hc') hinv'.sparse.lengths
            hinv'.cfgOk hinv'.extOk (.inl rfl) (fun h => absurd h (by decide))
            (fun h => absurd h (by decide)) hm'
        · have hlt := searchMeasure_lt_of_fuel hc' hinv'.sparse.lengths
            (Nat.lt_of_le_of_lt hfl' (Nat.lt_of_lt_of_le hfl1 hfl_le))
          exact hJout (nr, rc, _) m' ⟨c', ext', s', fullCfgCompat_trans hc hc', hinv', hlt, hm'⟩

/-! ## 3. `full_search_m6_wp` -/

theorem full_search_m6_wp {Γ : Env} (hΓ : Γ.Sat searchDeps)
    (hSimp : Γ.Has "full_simplify_m6" Spec.simplifySpec) :
    SpecEntry.Impl Γ full_search_m6
      ⟨"full_search_m6", [i64], [i64], Spec.searchSpec, true⟩ := by
  refine ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X hs => ?_⟩
  dsimp only [full_search_m6] at xs Q m hs ⊢
  change Spec.searchSpec xs m Q X at hs
  rcases xs with ⟨h, ⟨⟩⟩
  unfold Spec.searchSpec at hs
  obtain ⟨c0, ext0, s0, F0, R, rfl, hcfg0, hext0, _, ⟨hsp0, _⟩, hm0, hk_raw⟩ :=
    M6HdrCfgContract.elim hs
  have hinv0 : FullM6HdrInv c0 F0 ext0 s0 := ⟨hcfg0, hext0, hsp0⟩
  let hk : ∀ r c' ext' s' m',
      FullCfgCompat c0 c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m' :=
    fun r c' ext' s' m' hc' hlen' hcfg' hext' hr h20 h10 hm' =>
      hk_raw (r, ()) c' ext' s' m' hc' hcfg' hext' trivial hlen' ⟨hr, h20, h10⟩ hm'
  dsimp only [Func.wp, full_search_m6_body]
  refine search_call_lucky_late (by simp [vals]) (deps_has_lucky_late hΓ) hinv0 hm0
    fun r1 ext1 s1 m1 hlen1 hext1 hr1 _ h20_1 h02_1 h10_1 hm1 => ?_
  c0_hstraight
  refine jnz_bv_eq rfl (fun eq10 => ?_) (fun ne10 => ?_)
  · c0_hstraight; rw [eq10]
    exact hk 10#64 c0 ext1 s1 m1 (fullCfgCompat_refl c0) hlen1 hinv0.cfgOk hext1
      (.inr (.inl rfl)) (fun h => absurd h (by decide)) (fun _ => h10_1 eq10) hm1
  · c0_hstraight
    refine jnz_bv_eq rfl (fun eq20 => ?_) (fun ne20 => ?_)
    · c0_hstraight; rw [eq20]
      exact hk 20#64 c0 ext1 s1 m1 (fullCfgCompat_refl c0) hlen1 hinv0.cfgOk hext1
        (.inr (.inr rfl)) (fun _ => h20_1 eq20) (fun h => absurd h (by decide)) hm1
    · have hr02 : r1 = 0#64 ∨ r1 = 2#64 := by
        rcases hr1 with rfl | rfl | rfl | rfl
        · exact .inl rfl
        · exact .inr rfl
        · exact absurd rfl ne10
        · exact absurd rfl ne20
      have ⟨hinv1, _⟩ := h02_1 hr02
      c0_hstraight
      have ⟨hok1, hinv2, hm2⟩ := m6Hdr_store_scr .search_ticks 600 rfl rfl rfl 0#64 hinv1 hm1
      rw [wp_store]; refine ⟨hok1, ?_⟩
      c0_hstraight
      have ⟨hok2, hinv3, hm3⟩ := m6Hdr_store_scr .mode_saved_ticks 592 rfl rfl rfl 0#64 hinv2 hm2
      rw [wp_store]; refine ⟨hok2, ?_⟩
      refine search_call_update_classify (by simp [vals]) (deps_has_update_classify hΓ) hinv3 hm3
        fun ext4 s4 m4 hinv4 _ hm4 => ?_
      refine search_call_set_watermark 0#64 0#64 (by simp [vals]) (deps_has_set_watermark hΓ)
        hinv4 hm4 fun ext5 s5 m5 hinv5 _ hm5 => ?_
      c0_hstraight
      have ⟨hok5, hinv6, hm6⟩ := m6Hdr_store_scr .fwd_str_cnt 1128 rfl rfl rfl 0#64 hinv5 hm5
      rw [wp_store]; refine ⟨hok5, ?_⟩
      refine wp_while_state
        (fun st : FullCfg × List (BitVec 64) × FullState × BitVec 64 × BitVec 64 × BitVec 64 =>
          (st.2.2.2.1, st.2.2.2.2.1, st.2.2.2.2.2, ()))
        (fun st => searchMeasure st.1 st.2.2.1)
        (fun st m' => FullCfgCompat c0 st.1 ∧ FullM6HdrInv st.1 F0 st.2.1 st.2.2.1 ∧
          (FullM6HdrMem st.1 st.2.1 st.2.2.1 ⋆ R) m')
        (fun J hJ => by
          c0_hstraight
          exact hJ (c0, ext5, _, 10000#64, 0#64, 18446744073709551615#64) _
            ⟨fullCfgCompat_refl c0, hinv6, hm6⟩)
        (fun _ ⟨c, ext, s, nr, rc, ls⟩ m' ⟨hc, hinv, hm⟩ ih => ?_)
      dsimp only at hc hinv hm ih
      refine wp_jnz_true rfl ?_
      c0_hstraight
      rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .oom 760 rfl hm, ?_⟩
      c0_hstraight
      refine jnz_bv_ne rfl (fun _ => ?_) (fun _ => ?_)
      · c0_hstraight
        exact hk 0#64 c ext s m' hc hinv.sparse.lengths hinv.cfgOk hinv.extOk (.inl rfl)
          (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm
      · c0_hstraight
        rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .fuel 168 rfl hm, ?_⟩
        c0_hstraight
        refine jnz_bv_eq rfl (fun _ => ?_) (fun _ => ?_)
        · c0_hstraight
          exact hk 0#64 c ext s m' hc hinv.sparse.lengths hinv.cfgOk hinv.extOk (.inl rfl)
            (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm
        · refine search_call_propagate (by simp [vals, hc.hdr]) (deps_has_propagate hΓ) hinv hm
            fun rp extp sp mp hinvp _ _ hflp _ htep _ h1p _ hmp => ?_
          c0_hstraight
          refine jnz_bv_eq rfl (fun _ => ?_) (fun _ => ?_)
          · c0_hstraight
            exact hk 0#64 c extp sp mp hc hinvp.sparse.lengths hinvp.cfgOk hinvp.extOk (.inl rfl)
              (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hmp
          · refine wp_join_state
              (fun st : BitVec 64 × BitVec 64 × BitVec 64 => (st.1, st.2.1, st.2.2, ()))
              (fun st m'' => ∃ c' ext' s', FullCfgCompat c0 c' ∧ FullM6HdrInv c' F0 ext' s' ∧
                searchMeasure c' s' < searchMeasure c s ∧ (FullM6HdrMem c' ext' s' ⋆ R) m'') ?_ ?_
            · intro _ ⟨nr', rc', ls'⟩ m'' ⟨c', ext', s', hc', hinv', hlt, hm''⟩
              c0_hstraight
              exact ih (c', ext', s', nr', rc', ls') m'' hlt ⟨hc', hinv', hm''⟩
            · intro Jb hJb
              c0_hstraight
              refine jnz_bv_eq rfl (fun eq1 => ?_) (fun _ => ?_)
              · obtain ⟨F_cur, hfl_lt, _, hinvW, _, hconfl⟩ := h1p eq1
                refine search_call_analyze_full (by simp [vals, hc.hdr]) (deps_has_analyze hΓ)
                  hinvW hconfl hmp fun ra exta sa ma hexta hlena _ h20a h1a hma => ?_
                c0_hstraight
                refine jnz_bv_eq rfl (fun eq20 => ?_) (fun _ => ?_)
                · c0_hstraight
                  exact hk 20#64 c exta sa ma hc hlena hinvp.cfgOk hexta
                    (.inr (.inr rfl)) (fun _ => h20a eq20) (fun h => absurd h (by decide)) hma
                · c0_hstraight
                  refine jnz_bv_ne rfl (fun _ => ?_) (fun eq1a => ?_) <;> c0_hstraight
                  · exact hk 0#64 c exta sa ma hc hlena hinvp.cfgOk hexta
                      (.inl rfl) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
                      hma
                  · have ⟨hinva, hfla⟩ := h1a eq1a
                    have hlt := searchMeasure_lt_of_fuel (fullCfgCompat_refl c)
                      hinva.sparse.lengths (Nat.lt_of_le_of_lt hfla hfl_lt)
                    exact hJb (nr, rc, ls) ma ⟨c, exta, sa, hc, hinva, hlt, hma⟩
              · c0_hstraight
                rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .unassigned 792 rfl hmp, ?_⟩
                c0_hstraight
                refine jnz_bv_eq rfl (fun _ => ?_) (fun _ => ?_)
                · c0_hstraight
                  exact hk 10#64 c extp sp mp hc hinvp.sparse.lengths hinvp.cfgOk hinvp.extOk
                    (.inr (.inl rfl)) (fun h => absurd h (by decide))
                    (fun _ => hinvp.sparse.2.2.2.1.2) hmp
                · c0_hstraight
                  rw [wp_load]; refine ⟨_, hc.hdr.symm ▸ m6Hdr_load_off .fuel 168 rfl hmp, ?_⟩
                  c0_hstraight
                  refine jnz_bv_eq rfl (fun _ => ?_) (fun hflp0 => ?_)
                  · c0_hstraight
                    exact hk 0#64 c extp sp mp hc hinvp.sparse.lengths hinvp.cfgOk hinvp.extOk
                      (.inl rfl) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
                      hmp
                  · exact search_post_prop_wp hΓ hSimp hc hinvp hflp0 hflp htep hmp
                      (fun c' ext' s' m'' nr' rc' ls' hc' hinv' hlt hm'' =>
                        hJb (nr', rc', ls') m'' ⟨c', ext', s', hc', hinv', hlt, hm''⟩) hk

end LeanQbe.T.Examples.Kissat.Proof.Search
