module

public import LeanQbe.T.Examples.Kissat.FullFastCoreBcpLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat Stage-5 Hot-Loop BCP `Func.wp` Proofs (`FullFastCoreBcpLemmas`)

Proves canonical `FullSpec2`-compatible `Func.wp` contracts for the Stage-5 optimized BCP core:
1. `full_prop_lit_wp` (`FullSpec2.fullPropLitSpec`): inline value check & two-pass replacement
   search (`srch`), non-chronological `nl_lvl == cur_lvl` fast path, delayed header sync
   (`trail_end`, `unassigned`, `unflushed`, `search_ticks`), and zero dead watch-tail sentinel loop.
2. `full_propagate_ignore_wp` (`FullSpec2.fullPropagateIgnoreSpec`): register-cached `prop`/`fuel`
   with eager `h->propagated = prop` and delayed exit `h->fuel = fuel`.
3. `full_propagate_wp` (`FullSpec2.fullPropagateSpec`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FastCore

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Full hiding
  full_prop_lit_body full_prop_lit_wf full_prop_lit_wp
  full_propagate_ignore_body full_propagate_ignore_wf full_propagate_ignore_wp
  full_propagate_body full_propagate_wf full_propagate_wp
open LeanQbe.T.Examples.Kissat.Full.FullPropDecSpecs hiding
  fullPropLitSpec fullPropagateIgnoreSpec fullPropagateSpec fullWatchPushSpec
  FullTrailExt FullArenaPermEq
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

attribute [local irreducible] fastPropMem

local macro "fc_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

local elab "fc_head_steps" : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)))
  fcHeadRun false

local elab "fc_head_split" : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)))
  fcHeadRun true

private def fastPropReplSearchExpr (srch_v csz : Val i32) (nlits cbase ar_p vals_p : Val i64)
    (j6_body : Tup Val [i32, i32, i32] → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  .group (sig := [[i32, i32, i32]])
    (fun L10 => .cons (fun p1 =>
      .group (sig := [[i32, i32, i32]])
        (fun L11 => .cons (fun pf => j6_body pf) .nil)
        (fun L11 =>
          .let_ (Op.mk (.cmp .eq i32) (.var p1.1, (.imm (4294967295 : BitVec 32), ())))
            fun ceq =>
          .jnz (.var ceq.1) (
            .group (sig := [[i32, i32, i32]])
              (fun L21 => .cons (fun p2 =>
                .jump L11.1 (.var p2.1, (.var p2.2.1, (.var p2.2.2.1, ())))
              ) .nil)
              (fun L21 =>
                .group (sig := [[i32]])
                  (fun L22 => .cons (fun r2 =>
                    .let_ (Op.mk (.cmp .ult i32) (.var r2.1, (.var srch_v, ()))) fun clt =>
                    .jnz (.var clt.1) (
                      .let_ (Op.mk (.zext 32 64) (.var r2.1, ())) fun r64 =>
                      .let_ (Op.mk (.add i64) (.var cbase, (.var r64.1, ()))) fun idx0 =>
                      .let_ (Op.mk (.mul i64) (.var idx0.1, (.imm (4 : BitVec 64), ())))
                        fun off4 =>
                      .let_ (Op.mk (.add i64) (.var ar_p, (.var off4.1, ()))) fun par =>
                      .load i32 (.var par.1) fun cand =>
                      .group (sig := [[]])
                        (fun L23 => .cons (fun _ =>
                          .let_ (Op.mk (.add i32) (.var r2.1, (.imm (1 : BitVec 32), ())))
                            fun r2' =>
                          .jump L22.1 (.var r2'.1, ())
                        ) .nil)
                        (fun L23 =>
                          .let_ (Op.mk (.zext 32 64) (.var cand, ())) fun c64 =>
                          .let_ (Op.mk (.cmp .ult i64) (.var c64.1, (.var nlits, ())))
                            fun cb =>
                          .jnz (.var cb.1) (
                            .let_ (Op.mk (.zext 32 64) (.var cand, ())) fun c64' =>
                            .let_ (Op.mk (.add i64) (.var vals_p, (.var c64'.1, ()))) fun pv =>
                            .load i8 (.var pv.1) fun cv =>
                            .let_ (Op.mk (.trunc 32 8) (.imm (0 : BitVec 32), ())) fun z8 =>
                            .let_ (Op.mk (.sext 8 32) (.var cv, ())) fun cv32 =>
                            .let_ (Op.mk (.sext 8 32) (.var z8.1, ())) fun z32 =>
                            .let_ (Op.mk (.cmp .sge i32) (.var cv32.1, (.var z32.1, ())))
                              fun csge =>
                            .jnz (.var csge.1)
                              (.jump L21.1 (.var r2.1, (.var cand, (.var r2.1, ()))))
                              (.jump L23.1 ())
                          ) (.jump L23.1 ())
                        )
                    ) (.jump L21.1 (.var p1.1, (.var p1.2.1, (.var r2.1, ()))))
                  ) .nil)
                  (fun L22 => .jump L22.1 (.imm (2 : BitVec 32), ()))
              )
          ) (.jump L11.1 (.var p1.1, (.var p1.2.1, (.var p1.2.2.1, ()))))
        )
    ) .nil)
    (fun L10 =>
      .group (sig := [[i32]])
        (fun L24 => .cons (fun r1 =>
          .let_ (Op.mk (.cmp .ult i32) (.var r1.1, (.var csz, ()))) fun clt =>
          .jnz (.var clt.1) (
            .let_ (Op.mk (.zext 32 64) (.var r1.1, ())) fun r64 =>
            .let_ (Op.mk (.add i64) (.var cbase, (.var r64.1, ()))) fun idx0 =>
            .let_ (Op.mk (.mul i64) (.var idx0.1, (.imm (4 : BitVec 64), ()))) fun off4 =>
            .let_ (Op.mk (.add i64) (.var ar_p, (.var off4.1, ()))) fun par =>
            .load i32 (.var par.1) fun cand =>
            .group (sig := [[]])
              (fun L25 => .cons (fun _ =>
                .let_ (Op.mk (.add i32) (.var r1.1, (.imm (1 : BitVec 32), ()))) fun r1' =>
                .jump L24.1 (.var r1'.1, ())
              ) .nil)
              (fun L25 =>
                .let_ (Op.mk (.zext 32 64) (.var cand, ())) fun c64 =>
                .let_ (Op.mk (.cmp .ult i64) (.var c64.1, (.var nlits, ()))) fun cb =>
                .jnz (.var cb.1) (
                  .let_ (Op.mk (.zext 32 64) (.var cand, ())) fun c64' =>
                  .let_ (Op.mk (.add i64) (.var vals_p, (.var c64'.1, ()))) fun pv =>
                  .load i8 (.var pv.1) fun cv =>
                  .let_ (Op.mk (.trunc 32 8) (.imm (0 : BitVec 32), ())) fun z8 =>
                  .let_ (Op.mk (.sext 8 32) (.var cv, ())) fun cv32 =>
                  .let_ (Op.mk (.sext 8 32) (.var z8.1, ())) fun z32 =>
                  .let_ (Op.mk (.cmp .sge i32) (.var cv32.1, (.var z32.1, ()))) fun csge =>
                  .jnz (.var csge.1)
                    (.jump L10.1 (.var r1.1, (.var cand, (.var r1.1, ()))))
                    (.jump L25.1 ())
                ) (.jump L25.1 ())
              )
          ) (.jump L10.1 (.imm (4294967295 : BitVec 32), (.imm (0 : BitVec 32), (.var r1.1, ()))))
        ) .nil)
        (fun L24 => .jump L24.1 (.var srch_v, ()))
    )


private theorem fastProp_repl_search_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sem1 : FullState} {not_lit cref srch_v csz32 : BitVec 32}
    {nlits off_v p_v q_v end_v : BitVec 64} {R : Mem 64 → Prop} {mj : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    {j6_body : Tup Val [i32, i32, i32] → Expr Val Cont [.bool]}
    (hmaxv : c.max_vars < 2 * dimacsBound) (har : c.arena_cap < 2 * dimacsBound)
    (hcv0 : s.core.cur_vars ≤ c.max_vars)
    (hnlits_eq : nlits.toNat = 2 * s.core.cur_vars)
    (hpi1 : PropLitInv c F0 F_cur s sem1 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hlen1_mem : (fastPropMem s sem1).LengthsOk c)
    (hfit1 : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (h3_idx : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (hcsz32_nat : csz32.toNat = fullArenaClauseSizeCore sem1.core cref.toNat)
    (hsrch2 : 2 ≤ srch_v.toNat)
    (hsrch_lt : srch_v.toNat < fullArenaClauseSizeCore sem1.core cref.toNat)
    (hm : (FullMem c (fastPropMem s sem1) ⋆ R) mj)
    (hj6 : ∀ ri_f repl_f _rf : BitVec 32,
      ((ri_f = 0xFFFFFFFF#32 ∧ ∀ k, 2 ≤ k → k < fullArenaClauseSizeCore sem1.core cref.toNat →
          fullFindReplBad sem1 cref.toNat k) ∨
       (ri_f ≠ 0xFFFFFFFF#32 ∧ 2 ≤ ri_f.toNat ∧
          ∃ hr_lt : ri_f.toNat < fullArenaClauseSizeCore sem1.core cref.toNat,
          repl_f = sem1.core.arena[cref.toNat + 3 + ri_f.toNat]'(by
            rw [hpi1.len.core_ok.arena_len_arr]
            exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hr_lt _)
              (Nat.le_trans hfit1 hpi1.len.core_ok.arena_len_le)) ∧
          repl_f.toNat < 2 * sem1.core.cur_vars ∧
          ((sem1.core.vals[repl_f.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false)) →
      wp Γ Q X (j6_body (ri_f, repl_f, _rf, ())) mj) :
    wp Γ Q X (fastPropReplSearchExpr srch_v csz32 nlits
      (cref.setWidth 64 + 3#64) c.pArena c.pVals j6_body) mj := by
  unfold dimacsBound at hmaxv har
  have haren1 := hpi1.len.core_ok.arena_len_arr
  have halen1_le := hpi1.len.core_ok.arena_len_le
  have hvals1 := hpi1.len.core_ok.vals_len
  have hm1_aren := hlen1_mem.core_ok.arena_len_arr
  have hm1_vals := hlen1_mem.core_ok.vals_len
  have hfit_csz : cref.toNat + 3 + csz32.toNat ≤ c.arena_cap := by
    rw [hcsz32_nat]; exact Nat.le_trans hfit1 halen1_le
  have h2cv_le : 2 * s.core.cur_vars ≤ 2 * c.max_vars := Nat.mul_le_mul_left 2 hcv0
  have hcv1_eq := hpi1.cur_vars_eq
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hcv0 (Nat.lt_trans hmaxv (by decide))
  have h2cv_lt64 : 2 * s.core.cur_vars < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 hcv0)
      (Nat.lt_trans (Nat.mul_lt_mul_of_pos_left hmaxv (by decide)) (by decide))
  have hfit1_ar : ∀ {r}, r < fullArenaClauseSizeCore sem1.core cref.toNat →
      cref.toNat + 3 + r < sem1.core.arena.length := fun hr => by
    rw [haren1]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hr _) (Nat.le_trans hfit1 halen1_le)
  have hcsz_lt32 : fullArenaClauseSizeCore sem1.core cref.toNat < 2 ^ 32 :=
    hcsz32_nat ▸ csz32.isLt
  have hcsz_lt_ff : fullArenaClauseSizeCore sem1.core cref.toNat < 0xFFFFFFFF :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left _ _) hfit1)
      (Nat.lt_of_le_of_lt halen1_le (Nat.lt_trans har (by decide)))
  refine wp_loop_break_group
    (brkTs := [i32, i32, i32]) (lpTs := [i32])
    (fun (ri1, repl1, r1, ()) mb1 => mb1 = mj ∧
      ((ri1 = 0xFFFFFFFF#32 ∧ ∀ k, srch_v.toNat ≤ k →
          k < fullArenaClauseSizeCore sem1.core cref.toNat → fullFindReplBad sem1 cref.toNat k) ∨
       (ri1 ≠ 0xFFFFFFFF#32 ∧ 2 ≤ ri1.toNat ∧
          ∃ hr_lt : ri1.toNat < fullArenaClauseSizeCore sem1.core cref.toNat,
          repl1 = sem1.core.arena[cref.toNat + 3 + ri1.toNat]'(hfit1_ar hr_lt) ∧
          repl1.toNat < 2 * sem1.core.cur_vars ∧
          ((sem1.core.vals[repl1.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false)))
    (fun rem1 (r1, ()) ml1 => rem1 = csz32.toNat - r1.toNat ∧
      srch_v.toNat ≤ r1.toNat ∧ r1.toNat ≤ csz32.toNat ∧ ml1 = mj ∧
      ∀ k, srch_v.toNat ≤ k → k < r1.toNat → fullFindReplBad sem1 cref.toNat k) ?_ ?_ ?_
  · rintro _ ⟨ri1, repl1, r1, ⟨⟩⟩ mb1 ⟨hmb1, hres1⟩
    subst mb1
    refine wp_join_group (fun (ri_f, repl_f, rf, ()) mf => mf = mj ∧
        ((ri_f = 0xFFFFFFFF#32 ∧ ∀ k, 2 ≤ k → k < fullArenaClauseSizeCore sem1.core cref.toNat →
            fullFindReplBad sem1 cref.toNat k) ∨
         (ri_f ≠ 0xFFFFFFFF#32 ∧ 2 ≤ ri_f.toNat ∧
            ∃ hr_lt : ri_f.toNat < fullArenaClauseSizeCore sem1.core cref.toNat,
            repl_f = sem1.core.arena[cref.toNat + 3 + ri_f.toNat]'(hfit1_ar hr_lt) ∧
            repl_f.toNat < 2 * sem1.core.cur_vars ∧
            ((sem1.core.vals[repl_f.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false))) ?_ ?_
    · rintro _ ⟨ri_f, repl_f, rf, ⟨⟩⟩ mf ⟨hmf, hfin⟩
      subst mf
      exact hj6 ri_f repl_f rf hfin
    · intro Jri hJri; fc_head_steps
      · have hri1 : ri1 = 0xFFFFFFFF#32 := hc
        have hnone1 : ∀ k, srch_v.toNat ≤ k →
            k < fullArenaClauseSizeCore sem1.core cref.toNat → fullFindReplBad sem1 cref.toNat k :=
          hres1.elim And.right fun h => absurd hri1 h.1
        refine wp_loop_break_group
          (brkTs := [i32, i32, i32]) (lpTs := [i32])
          (fun (ri2, repl2, r2, ()) mb2 => mb2 = mj ∧
            ((ri2 = 0xFFFFFFFF#32 ∧ ∀ k, 2 ≤ k →
                k < fullArenaClauseSizeCore sem1.core cref.toNat →
                fullFindReplBad sem1 cref.toNat k) ∨
             (ri2 ≠ 0xFFFFFFFF#32 ∧ 2 ≤ ri2.toNat ∧
                ∃ hr_lt : ri2.toNat < fullArenaClauseSizeCore sem1.core cref.toNat,
                repl2 = sem1.core.arena[cref.toNat + 3 + ri2.toNat]'(hfit1_ar hr_lt) ∧
                repl2.toNat < 2 * sem1.core.cur_vars ∧
                ((sem1.core.vals[repl2.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false)))
          (fun rem2 (r2, ()) ml2 => rem2 = srch_v.toNat - r2.toNat ∧
            2 ≤ r2.toNat ∧ r2.toNat ≤ srch_v.toNat ∧ ml2 = mj ∧
            ∀ k, 2 ≤ k → k < r2.toNat → fullFindReplBad sem1 cref.toNat k) ?_ ?_ ?_
        · rintro _ ⟨ri2, repl2, r2, ⟨⟩⟩ mb2 ⟨hmb2, hres2⟩
          subst mb2
          fc_head_steps; exact hJri (ri2, repl2, r2, ()) mj ⟨rfl, hres2⟩
        · rintro B2 L2 _ ⟨r2, ⟨⟩⟩ ml2 hB2 ih2 ⟨rfl, hr2_ge, hr2_le, hml2, hseen2⟩
          subst ml2
          fc_head_split
          · have hr2_lt : r2.toNat < srch_v.toNat := by assumption
            have hr2_csz : r2.toNat < fullArenaClauseSizeCore sem1.core cref.toNat :=
              Nat.lt_trans hr2_lt hsrch_lt
            have hidx_r2 : (cref.setWidth 64 + 3#64 + r2.setWidth 64).toNat =
                cref.toNat + 3 + r2.toNat := by
              rw [bv64_add_toNat (by
                rw [h3_idx, bv_c0_zext32_64]
                exact Nat.lt_of_lt_of_le (hfit1_ar hr2_csz) (Nat.le_trans
                  (Nat.le_of_eq haren1) (Nat.le_of_lt (Nat.lt_trans har (by decide))))),
                h3_idx, bv_c0_zext32_64]
            have hidx_r2_lt : (cref.setWidth 64 + 3#64 + r2.setWidth 64).toNat < c.arena_cap := by
              rw [hidx_r2]; omega
            have hr2_1 : (r2 + (1 : BitVec 32)).toNat = r2.toNat + 1 := by
              rw [BitVec.toNat_add]
              exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hr2_csz) hcsz_lt32)
            fc_head_steps
            refine wp_join_group (fun () m23 => m23 = mj ∧ fullFindReplBad sem1 cref.toNat r2.toNat)
              ?_ ?_
            · rintro _ ⟨⟩ m23 ⟨hm23, hbad⟩
              subst m23
              fc_head_steps
              exact ih2 _ _ mj (by
                  rw [show (1 : BitVec 32) = (1 : BitVec 32) from rfl, hr2_1]
                  exact Nat.sub_lt (Nat.sub_pos_of_lt hr2_lt) Nat.zero_lt_one)
                ⟨rfl, by rw [hr2_1]; exact Nat.le_trans hr2_ge (Nat.le_succ _),
                 by rw [hr2_1]; exact Nat.succ_le_of_lt hr2_lt, rfl,
                 fun k hk1 hk2 => by
                   rw [hr2_1] at hk2
                   rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk2) with hk' | hkr
                   · exact hseen2 k hk1 hk'
                   · subst hkr; exact hbad⟩
            · intro J23 hJ23; fc_head_split
              · have hidx_r2_ar : (cref.setWidth 64 + 3#64 + r2.setWidth 64).toNat <
                    sem1.core.arena.length := by
                  rw [hidx_r2]; exact hfit1_ar hr2_csz
                have hcand_cv : (sem1.core.arena[(cref.setWidth 64 + 3#64 + r2.setWidth 64).toNat]'
                    hidx_r2_ar).toNat < 2 * sem1.core.cur_vars := by
                  have hlt : (sem1.core.arena[cref.toNat + 3 + r2.toNat]'(hfit1_ar hr2_csz)).toNat <
                      nlits.toNat := by
                    have hc' := hc
                    simp only [fastPropMem_arena,
                      Nat.mod_eq_of_lt (by omega : cref.toNat + 3 + r2.toNat < 2 ^ 64)] at hc'
                    exact hc'
                  rw [hnlits_eq, ← hcv1_eq] at hlt
                  simpa only [hidx_r2] using hlt
                have hcand_cv_raw : (sem1.core.arena[cref.toNat + 3 + r2.toNat]'(
                    hfit1_ar hr2_csz)).toNat < 2 * sem1.core.cur_vars := by
                  simpa only [hidx_r2] using hcand_cv
                have hcand_max : (sem1.core.arena[(cref.setWidth 64 + 3#64 + r2.setWidth 64).toNat]'
                    hidx_r2_ar).toNat < 2 * c.max_vars :=
                  Nat.lt_of_lt_of_le hcand_cv (Nat.mul_le_mul_left 2 (hcv1_eq ▸ hcv0))
                have hcand_max_raw : (sem1.core.arena[cref.toNat + 3 + r2.toNat]'(
                    hfit1_ar hr2_csz)).toNat < 2 * c.max_vars := by
                  simpa only [hidx_r2] using hcand_max
                have hidx_r2_mod : (cref.toNat + 3 + r2.toNat) % 2 ^ 64 =
                    cref.toNat + 3 + r2.toNat :=
                  Nat.mod_eq_of_lt (by omega)
                let cand2_m := (fastPropMem s sem1).core.arena[(cref.setWidth 64 + 3#64 +
                  r2.setWidth 64).toNat]'(by rw [fastPropMem_arena]; exact hidx_r2_ar)
                have hcand2_eq : cand2_m = sem1.core.arena[cref.toNat + 3 + r2.toNat]'(
                    hfit1_ar hr2_csz) :=
                  (fc_getElem_arena s sem1).trans
                    (fc_getElem_eq_of_idx hidx_r2 _ (hfit1_ar hr2_csz))
                fc_head_steps
                · have hok := fastProp_findRepl_ok (st := sem1) (cref := cref.toNat) (r := r2.toNat)
                    (hi_lt := hfit1_ar hr2_csz) (hj_lt := hvals1 ▸ Nat.lt_of_lt_of_le
                      hcand_cv_raw (Nat.mul_le_mul_left 2 hpi1.len.core_ok.cur_vars_le))
                    hcand_cv_raw
                    (by simpa only [fastPropMem_arena, fastPropMem_vals, hidx_r2_mod] using hc)
                  have hr2_ne : r2 ≠ 0xFFFFFFFF#32 := fun heq => by
                    have heq' : r2.toNat = 0xFFFFFFFF := by rw [heq]; decide
                    exact absurd (heq' ▸ hr2_csz) (Nat.not_lt.mpr (Nat.le_of_lt hcsz_lt_ff))
                  exact hB2 (r2, cand2_m, r2, ()) mj ⟨rfl, Or.inr ⟨hr2_ne, hr2_ge, hr2_csz,
                    hcand2_eq, by simpa only [hcand2_eq,
                      List.getElem?_eq_getElem (hfit1_ar hr2_csz), Option.getD_some] using hok⟩⟩
                · exact hJ23 () mj ⟨rfl, fastProp_findRepl_bad_slt (st := sem1) (cref := cref.toNat)
                    (r := r2.toNat) (hi_lt := hfit1_ar hr2_csz)
                    (hj_lt := hvals1 ▸ Nat.lt_of_lt_of_le hcand_cv_raw
                      (Nat.mul_le_mul_left 2 hpi1.len.core_ok.cur_vars_le))
                    (by simpa only [fastPropMem_arena, fastPropMem_vals, hidx_r2_mod] using hc)⟩
              · have hge_mod : nlits.toNat ≤
                    (sem1.core.arena[(cref.toNat + 3 + r2.toNat) % 2 ^ 64]'(
                      by rw [Nat.mod_eq_of_lt (by omega)]; exact hfit1_ar hr2_csz)).toNat :=
                  Nat.le_of_not_lt (by simpa only [fastPropMem_arena] using hc)
                have hcand_ge : ¬ (sem1.core.arena[cref.toNat + 3 + r2.toNat]'(
                    hfit1_ar hr2_csz)).toNat < 2 * sem1.core.cur_vars := by
                  have hge : nlits.toNat ≤ (sem1.core.arena[cref.toNat + 3 + r2.toNat]'(
                      hfit1_ar hr2_csz)).toNat := by
                    simpa only [Nat.mod_eq_of_lt (by omega : cref.toNat + 3 + r2.toNat < 2 ^ 64)]
                      using hge_mod
                  rw [hnlits_eq, ← hcv1_eq] at hge
                  exact Nat.not_lt.mpr hge
                fc_head_steps
                exact hJ23 () mj ⟨rfl, fastProp_findRepl_bad_oob (st := sem1) (cref := cref.toNat)
                  (r := r2.toNat) (hi_lt := hfit1_ar hr2_csz) hcand_ge⟩
          · have hr2_eq : r2.toNat = srch_v.toNat := Nat.le_antisymm hr2_le (Nat.le_of_not_lt hc)
            fc_head_steps
            exact hB2 (ri1, repl1, r2, ()) mj ⟨rfl, Or.inl ⟨hri1,
              fun k hk2 hksz => if hks : k < srch_v.toNat then hseen2 k hk2 (hr2_eq ▸ hks)
                else hnone1 k (Nat.le_of_not_lt hks) hksz⟩⟩
        · intro B2 L2 _ hL2; fc_head_steps
          exact hL2 _ (2#32, ()) mj ⟨rfl, by decide, hsrch2, rfl,
            fun _ hk1 hk2 => absurd (Nat.lt_of_le_of_lt hk1 hk2) (by decide)⟩
      · exact hJri (ri1, repl1, r1, ()) mj ⟨rfl, Or.inr (hres1.resolve_left (fun h => hc h.1))⟩
  · rintro B1 L1 _ ⟨r1, ⟨⟩⟩ ml1 hB1 ih1 ⟨rfl, hr1_ge, hr1_le, hml1, hseen1⟩
    subst ml1
    fc_head_split
    · have hr1_lt : r1.toNat < csz32.toNat := by assumption
      have hr1_csz : r1.toNat < fullArenaClauseSizeCore sem1.core cref.toNat := hcsz32_nat ▸ hr1_lt
      have hidx_r1 : (cref.setWidth 64 + 3#64 + r1.setWidth 64).toNat =
          cref.toNat + 3 + r1.toNat := by
        rw [bv64_add_toNat (by
          rw [h3_idx, bv_c0_zext32_64]
          exact Nat.lt_of_lt_of_le (hfit1_ar hr1_csz) (Nat.le_trans
            (Nat.le_of_eq haren1) (Nat.le_of_lt (Nat.lt_trans har (by decide))))),
          h3_idx, bv_c0_zext32_64]
      have hidx_r1_lt : (cref.setWidth 64 + 3#64 + r1.setWidth 64).toNat < c.arena_cap := by
        rw [hidx_r1]; omega
      have hr1_1 : (r1 + (1 : BitVec 32)).toNat = r1.toNat + 1 := by
        rw [BitVec.toNat_add]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hr1_csz) hcsz_lt32)
      fc_head_steps
      refine wp_join_group (fun () m25 => m25 = mj ∧ fullFindReplBad sem1 cref.toNat r1.toNat)
        ?_ ?_
      · rintro _ ⟨⟩ m25 ⟨hm25, hbad⟩
        subst m25
        fc_head_steps
        exact ih1 _ _ mj (by
            rw [hr1_1]
            exact Nat.sub_lt (Nat.sub_pos_of_lt hr1_lt) Nat.zero_lt_one)
          ⟨rfl, by rw [hr1_1]; exact Nat.le_trans hr1_ge (Nat.le_succ _),
           by rw [hr1_1]; exact Nat.succ_le_of_lt hr1_lt, rfl,
           fun k hk1 hk2 => by
             rw [hr1_1] at hk2
             rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk2) with hk' | hkr
             · exact hseen1 k hk1 hk'
             · subst hkr; exact hbad⟩
      · intro J25 hJ25; fc_head_split
        · have hidx_r1_ar : (cref.setWidth 64 + 3#64 + r1.setWidth 64).toNat <
              sem1.core.arena.length := by
            rw [hidx_r1]; exact hfit1_ar hr1_csz
          have hcand_cv : (sem1.core.arena[(cref.setWidth 64 + 3#64 + r1.setWidth 64).toNat]'
              hidx_r1_ar).toNat < 2 * sem1.core.cur_vars := by
            have hlt : (sem1.core.arena[cref.toNat + 3 + r1.toNat]'(hfit1_ar hr1_csz)).toNat <
                nlits.toNat := by
              have hc' := hc
              simp only [fastPropMem_arena,
                Nat.mod_eq_of_lt (by omega : cref.toNat + 3 + r1.toNat < 2 ^ 64)] at hc'
              exact hc'
            rw [hnlits_eq, ← hcv1_eq] at hlt
            simpa only [hidx_r1] using hlt
          have hcand_cv_raw : (sem1.core.arena[cref.toNat + 3 + r1.toNat]'(
              hfit1_ar hr1_csz)).toNat < 2 * sem1.core.cur_vars := by
            simpa only [hidx_r1] using hcand_cv
          have hcand_max : (sem1.core.arena[(cref.setWidth 64 + 3#64 + r1.setWidth 64).toNat]'
              hidx_r1_ar).toNat < 2 * c.max_vars :=
            Nat.lt_of_lt_of_le hcand_cv (Nat.mul_le_mul_left 2 (hcv1_eq ▸ hcv0))
          have hcand_max_raw : (sem1.core.arena[cref.toNat + 3 + r1.toNat]'(
              hfit1_ar hr1_csz)).toNat < 2 * c.max_vars := by
            simpa only [hidx_r1] using hcand_max
          have hidx_r1_mod : (cref.toNat + 3 + r1.toNat) % 2 ^ 64 = cref.toNat + 3 + r1.toNat :=
            Nat.mod_eq_of_lt (by omega)
          let cand1_m := (fastPropMem s sem1).core.arena[(cref.setWidth 64 + 3#64 +
            r1.setWidth 64).toNat]'(by rw [fastPropMem_arena]; exact hidx_r1_ar)
          have hcand1_eq : cand1_m = sem1.core.arena[cref.toNat + 3 + r1.toNat]'(
              hfit1_ar hr1_csz) :=
            (fc_getElem_arena s sem1).trans (fc_getElem_eq_of_idx hidx_r1 _ (hfit1_ar hr1_csz))
          fc_head_steps
          · have hok := fastProp_findRepl_ok (st := sem1) (cref := cref.toNat) (r := r1.toNat)
              (hi_lt := hfit1_ar hr1_csz) (hj_lt := hvals1 ▸ Nat.lt_of_lt_of_le
                hcand_cv_raw (Nat.mul_le_mul_left 2 hpi1.len.core_ok.cur_vars_le))
              hcand_cv_raw
              (by simpa only [fastPropMem_arena, fastPropMem_vals, hidx_r1_mod] using hc)
            have hr1_ne : r1 ≠ 0xFFFFFFFF#32 := fun heq => by
              have heq' : r1.toNat = 0xFFFFFFFF := by rw [heq]; decide
              exact absurd (heq' ▸ hr1_csz) (Nat.not_lt.mpr (Nat.le_of_lt hcsz_lt_ff))
            exact hB1 (r1, cand1_m, r1, ()) mj ⟨rfl, Or.inr ⟨hr1_ne, Nat.le_trans hsrch2 hr1_ge,
              hr1_csz, hcand1_eq, by simpa only [hcand1_eq,
                List.getElem?_eq_getElem (hfit1_ar hr1_csz), Option.getD_some] using hok⟩⟩
          · exact hJ25 () mj ⟨rfl, fastProp_findRepl_bad_slt (st := sem1) (cref := cref.toNat)
              (r := r1.toNat) (hi_lt := hfit1_ar hr1_csz)
              (hj_lt := hvals1 ▸ Nat.lt_of_lt_of_le hcand_cv_raw
                (Nat.mul_le_mul_left 2 hpi1.len.core_ok.cur_vars_le))
              (by simpa only [fastPropMem_arena, fastPropMem_vals, hidx_r1_mod] using hc)⟩
        · have hge_mod : nlits.toNat ≤ (sem1.core.arena[(cref.toNat + 3 + r1.toNat) % 2 ^ 64]'(
              by rw [Nat.mod_eq_of_lt (by omega)]; exact hfit1_ar hr1_csz)).toNat :=
            Nat.le_of_not_lt (by simpa only [fastPropMem_arena] using hc)
          have hcand_ge : ¬ (sem1.core.arena[cref.toNat + 3 + r1.toNat]'(
              hfit1_ar hr1_csz)).toNat < 2 * sem1.core.cur_vars := by
            have hge : nlits.toNat ≤ (sem1.core.arena[cref.toNat + 3 + r1.toNat]'(
                hfit1_ar hr1_csz)).toNat := by
              simpa only [Nat.mod_eq_of_lt (by omega : cref.toNat + 3 + r1.toNat < 2 ^ 64)]
                using hge_mod
            rw [hnlits_eq, ← hcv1_eq] at hge
            exact Nat.not_lt.mpr hge
          fc_head_steps
          exact hJ25 () mj ⟨rfl, fastProp_findRepl_bad_oob (st := sem1) (cref := cref.toNat)
            (r := r1.toNat) (hi_lt := hfit1_ar hr1_csz) hcand_ge⟩
    · have hr1_eq : r1.toNat = csz32.toNat := Nat.le_antisymm hr1_le (Nat.le_of_not_lt hc)
      fc_head_steps
      exact hB1 (0xFFFFFFFF#32, 0#32, r1, ()) mj ⟨rfl, Or.inl ⟨rfl, fun k hk1 hk2 => by
        rw [← hcsz32_nat, ← hr1_eq] at hk2; exact hseen1 k hk1 hk2⟩⟩
  · intro B1 L1 _ hL1; fc_head_steps
    exact hL1 _ (srch_v, ()) mj ⟨rfl, Nat.le_refl _, hcsz32_nat ▸ Nat.le_of_lt hsrch_lt, rfl,
      fun _ hk1 hk2 => absurd hk1 (Nat.not_le.mpr hk2)⟩

private def fastPropLargePushExpr (h_p cbase pAr pWvec pWstk off_v p2_v q_v end_v : Val i64)
    (ri_f repl_f cref not_lit other w0 : Val i32)
    (k_ok k_oom : Val i64 → Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  .let_ (Op.mk (.zext 32 64) (.var cref, ())) fun x166 =>
  .let_ (Op.mk (.add i64) (.var x166.1, (.imm (1 : BitVec 64), ()))) fun x167 =>
  .let_ (Op.mk (.mul i64) (.var x167.1, (.imm (4 : BitVec 64), ()))) fun x168 =>
  .let_ (Op.mk (.add i64) (.var pAr, (.var x168.1, ()))) fun x169 =>
  .store (.var ri_f) (.var x169.1) (
    .let_ (Op.mk (.add i64) (.var cbase, (.imm (1 : BitVec 64), ()))) fun x170 =>
    .let_ (Op.mk (.mul i64) (.var x170.1, (.imm (4 : BitVec 64), ()))) fun x171 =>
    .let_ (Op.mk (.add i64) (.var pAr, (.var x171.1, ()))) fun x172 =>
    .store (.var repl_f) (.var x172.1) (
      .let_ (Op.mk (.zext 32 64) (.var ri_f, ())) fun x173 =>
      .let_ (Op.mk (.add i64) (.var cbase, (.var x173.1, ()))) fun x174 =>
      .let_ (Op.mk (.mul i64) (.var x174.1, (.imm (4 : BitVec 64), ()))) fun x175 =>
      .let_ (Op.mk (.add i64) (.var pAr, (.var x175.1, ()))) fun x176 =>
      .store (.var not_lit) (.var x176.1) (
        .let_ (Op.mk (.sub i64) (.var p2_v, (.var off_v, ()))) fun x177 =>
        .let_ (Op.mk (.sub i64) (.var q_v, (.var off_v, ()))) fun x178 =>
        .let_ (Op.mk (.sub i64) (.var end_v, (.var off_v, ()))) fun x179 =>
        .let_ (Op.mk (.and i32) (.var other, (.imm (2147483647 : BitVec 32), ()))) fun x180 =>
        .call "full_watch_push" (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
          (.var h_p, (.var repl_f, (.var x180.1, (.var cref, (.imm (2 : BitVec 32), ())))))
          fun x181 =>
        .let_ (Op.mk (.zext 32 64) (.var not_lit, ())) fun x182 =>
        .let_ (Op.mk (.sext 32 64) (.imm (1 : BitVec 32), ())) fun x183 =>
        .let_ (Op.mk (.shl i64) (.var x182.1, (.var x183.1, ()))) fun x184 =>
        .let_ (Op.mk (.mul i64) (.var x184.1, (.imm (4 : BitVec 64), ()))) fun x185 =>
        .let_ (Op.mk (.add i64) (.var pWvec, (.var x185.1, ()))) fun x186 =>
        .load i32 (.var x186.1) fun x187 =>
        .let_ (Op.mk (.zext 32 64) (.var x187, ())) fun x188 =>
        .let_ (Op.mk (.add i64) (.var x188.1, (.var x177.1, ()))) fun x189 =>
        .let_ (Op.mk (.add i64) (.var x188.1, (.var x178.1, ()))) fun x190 =>
        .let_ (Op.mk (.add i64) (.var x188.1, (.var x179.1, ()))) fun x191 =>
        .jnz (.var x181.1)
          (k_ok x188.1 x189.1 x190.1 x191.1) (
          .let_ (Op.mk (.add i64) (.var cbase, (.imm (1 : BitVec 64), ()))) fun x192 =>
          .let_ (Op.mk (.mul i64) (.var x192.1, (.imm (4 : BitVec 64), ()))) fun x193 =>
          .let_ (Op.mk (.add i64) (.var pAr, (.var x193.1, ()))) fun x194 =>
          .store (.var not_lit) (.var x194.1) (
            .let_ (Op.mk (.zext 32 64) (.var ri_f, ())) fun x195 =>
            .let_ (Op.mk (.add i64) (.var cbase, (.var x195.1, ()))) fun x196 =>
            .let_ (Op.mk (.mul i64) (.var x196.1, (.imm (4 : BitVec 64), ()))) fun x197 =>
            .let_ (Op.mk (.add i64) (.var pAr, (.var x197.1, ()))) fun x198 =>
            .store (.var repl_f) (.var x198.1) (
              .let_ (Op.mk (.mul i64) (.var x190.1, (.imm (4 : BitVec 64), ()))) fun x199 =>
              .let_ (Op.mk (.add i64) (.var pWstk, (.var x199.1, ()))) fun x200 =>
              .store (.var w0) (.var x200.1) (
                .let_ (Op.mk (.add i64) (.var x190.1, (.imm (1 : BitVec 64), ()))) fun x201 =>
                .let_ (Op.mk (.mul i64) (.var x201.1, (.imm (4 : BitVec 64), ()))) fun x202 =>
                .let_ (Op.mk (.add i64) (.var pWstk, (.var x202.1, ()))) fun x203 =>
                .store (.var cref) (.var x203.1) (
                  .let_ (Op.mk (.add i64) (.var x190.1, (.imm (2 : BitVec 64), ()))) fun x204 =>
                  .let_ (Op.mk (.add i64) (.var h_p, (.imm (760 : BitVec 64), ()))) fun x205 =>
                  .store (t := i64) (.imm (1 : BitVec 64)) (.var x205.1)
                    (k_oom x188.1 x189.1 x204.1 x191.1)
                )
              )
            )
          )
        )
      )
    )
  )

private theorem fastProp_large_push_wp {Γ : Env}
    (hPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sem1 : FullState}
    {not_lit w0 other cref ri_f repl_f : BitVec 32}
    {off_v p_v q_v end_v tend_v unass_v unfl_v : BitVec 64}
    {nl_lvl0 : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    {k_ok k_oom : Val i64 → Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]}
    (_hmaxv : c.max_vars < 2 * dimacsBound) (har : c.arena_cap < 2 * dimacsBound)
    (hlen0 : s.LengthsOk c) (_hcv0 : s.core.cur_vars ≤ c.max_vars)
    (hpi1 : PropLitInv c F0 F_cur s sem1 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hlen1_mem : (fastPropMem s sem1).LengthsOk c)
    (hcr_lt : cref.toNat < 0x80000000)
    (hcr_ref1 : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    (hfit1 : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (har4 : sem1.core.arena[cref.toNat + 4]? = some not_lit)
    (hnot_st1 : not_lit.toNat < 2 * sem1.core.cur_vars)
    (_hother_lt : other.toNat < 2 * sem1.core.cur_vars)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hr2 : 2 ≤ ri_f.toNat) (hr_lt : ri_f.toNat < fullArenaClauseSizeCore sem1.core cref.toNat)
    (hrepl_def : repl_f = sem1.core.arena[cref.toNat + 3 + ri_f.toNat]'(by
      rw [hpi1.len.core_ok.arena_len_arr]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hr_lt _)
        (Nat.le_trans hfit1 hpi1.len.core_ok.arena_len_le)))
    (hcand : repl_f.toNat < 2 * sem1.core.cur_vars ∧
      ((sem1.core.vals[repl_f.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false)
    (h1_idx : (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1)
    (h3_idx : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (h4_idx : (cref.setWidth 64 + 3#64 + 1#64).toNat = cref.toNat + 4)
    (htend1_eq : tend_v.toNat = sem1.core.trail_end) (hunass1_eq : unass_v = sem1.core.unassigned)
    (hunfl1_eq : unfl_v = sem1.core.unflushed)
    (hnl1 : sem1.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0)
    (hoom1 : sem1.core.oom = 0#64) (hct1 : sem1.core.confl_type = s.core.confl_type)
    (hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2) (hq_le : q_v.toNat ≤ p_v.toNat)
    (hq_lt : q_v.toNat < c.wcap)
    (hm : (FullMem c (fastPropMem s sem1) ⋆ R) m)
    (hk_ok : ∀ (st4 : FullState) (off4_v : BitVec 64) (m_p : Mem 64),
      (off4_v + (end_v - off_v)).toNat -
        (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat < end_v.toNat - p_v.toNat →
      PropLitInv c F0 F_cur s st4 not_lit.toNat off4_v.toNat
        (off4_v + (q_v - off_v)).toNat (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat
        (off4_v + (end_v - off_v)).toNat →
      tend_v.toNat = st4.core.trail_end → unass_v = st4.core.unassigned →
      unfl_v = st4.core.unflushed → st4.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 →
      st4.core.oom = 0#64 → st4.core.confl_type = s.core.confl_type →
      (FullMem c (fastPropMem s st4) ⋆ R) m_p →
      wp Γ Q X (k_ok off4_v (off4_v + (p_v + 1#64 + 1#64 - off_v)) (off4_v + (q_v - off_v))
        (off4_v + (end_v - off_v))) m_p)
    (hk_oom : ∀ (st6 : FullState) (off4_v : BitVec 64) (m_f : Mem 64),
      PropLitInv c F0 F_cur s st6 not_lit.toNat off4_v.toNat
        (off4_v + (q_v - off_v) + 2#64).toNat (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat
        (off4_v + (end_v - off_v)).toNat →
      tend_v.toNat = st6.core.trail_end → unass_v = st6.core.unassigned →
      unfl_v = st6.core.unflushed → st6.core.oom ≠ 0#64 →
      (FullMem c (fastPropMem s st6) ⋆ R) m_f →
      wp Γ Q X (k_oom off4_v (off4_v + (p_v + 1#64 + 1#64 - off_v))
        (off4_v + (q_v - off_v) + 2#64) (off4_v + (end_v - off_v))) m_f) :
    wp Γ Q X (fastPropLargePushExpr c.hdr (cref.setWidth 64 + 3#64) c.pArena c.pWvec c.pWstk
      off_v (p_v + 1#64 + 1#64) q_v end_v ri_f repl_f cref not_lit other w0 k_ok k_oom) m := by
  unfold dimacsBound at har
  have haren1 := hpi1.len.core_ok.arena_len_arr
  have halen1_le := hpi1.len.core_ok.arena_len_le
  have _hm1_aren := hlen1_mem.core_ok.arena_len_arr
  have _hm1_wvec := hlen1_mem.core_ok.wvec_len
  have hfit1_ar : ∀ {r}, r < fullArenaClauseSizeCore sem1.core cref.toNat →
      cref.toNat + 3 + r < sem1.core.arena.length := fun hr => by
    rw [haren1]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hr _) (Nat.le_trans hfit1 halen1_le)
  have h3r_idx : (cref.setWidth 64 + 3#64 + ri_f.setWidth 64).toNat =
      cref.toNat + 3 + ri_f.toNat := by
    rw [bv64_add_toNat (by
      rw [h3_idx, bv_c0_zext32_64]
      exact Nat.lt_of_lt_of_le (hfit1_ar hr_lt) (Nat.le_trans
        (Nat.le_of_eq haren1) (Nat.le_of_lt (Nat.lt_trans har (by decide))))),
      h3_idx, bv_c0_zext32_64]
  have h1_lt_ar : cref.toNat + 1 < c.arena_cap := by
    have := Nat.lt_of_lt_of_le (hfit1_ar hr_lt) (Nat.le_of_eq haren1); omega
  have h4_lt_ar : cref.toNat + 4 < c.arena_cap := by
    have := Nat.lt_of_lt_of_le (hfit1_ar hr_lt) (Nat.le_of_eq haren1); omega
  have h3r_lt_ar : cref.toNat + 3 + ri_f.toNat < c.arena_cap :=
    Nat.lt_of_lt_of_le (hfit1_ar hr_lt) (Nat.le_of_eq haren1)
  have hcr_lt_alen1 : cref.toNat < sem1.core.arena_len := by omega
  unfold fastPropLargePushExpr
  fc_head_steps
  let st3 : FullState :=
    { sem1 with core := { sem1.core with
        arena := ((sem1.core.arena.set (cref.toNat + 1) (BitVec.ofNat 32 ri_f.toNat)).set
          (cref.toNat + 4) repl_f).set (cref.toNat + 3 + ri_f.toNat) not_lit } }
  have h3r_ne1 : cref.toNat + 1 ≠ cref.toNat + 3 + ri_f.toNat := by omega
  have hrepl_set1 : repl_f = (sem1.core.arena.set (cref.toNat + 1)
      (BitVec.ofNat 32 ri_f.toNat))[cref.toNat + 3 + ri_f.toNat]'(by
        simp [hfit1_ar hr_lt]) := by
    rw [List.getElem_set_ne h3r_ne1]; exact hrepl_def
  have ⟨hlen3, hnw3, hsw3, hperm13, hcr_ref3, hcsz3, hrepl_lt,
      hrepl_ne_not, hw0_ne_ff, hcr_ne_ff⟩ :=
    fastProp_b1_swap (other := other) (r := ri_f.toNat) hpi1 hcr_lt_alen1
      hcr_ref1 hfit1 har4 hr2 hr_lt hrepl_set1
      (by simpa only [List.getElem?_eq_getElem (hfit1_ar hr_lt), Option.getD_some,
        ← hrepl_def] using hcand)
  have hri32 : BitVec.setWidth 32 ri_f = ri_f := by apply BitVec.eq_of_toNat_eq; simp
  have hm3 : (FullMem c (fastPropMem s st3) ⋆ R) m := by
    simpa only [st3, fastPropMem_arena, BitVec.ofNat_eq_ofNat, BitVec.ofNat_toNat, hri32,
      h1_idx, h4_idx, h3r_idx, fastPropMem_with_arena] using hm
  c0_call hPush
  refine ⟨c, fastPropMem s st3, R, rfl,
    fastPropMem_lengthsOk hlen0 hlen3 (hpi1.ag.get FullCoreState.cur_vars)
      (hpi1.ag.get FullCoreState.propagated) rfl,
    fastPropMem_watchLayout hsw3.layout rfl,
    fun h => absurd h (by decide), fun _ => ⟨hw0_ne_ff, hcr_ne_ff⟩,
    hm3, fun pok wvec' wstk' wlen' wu' wsort' m_p hlen_p hlay_p hpres_o
      hpok_t hpok_f hm_p => ?_⟩
  let st4 : FullState :=
    { st3 with
      core := { st3.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
      scratch := { st3.scratch with wsort := wsort' } }
  have hs4_eq :
      { fastPropMem s st3 with
        core := { (fastPropMem s st3).core with
          wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        scratch := { (fastPropMem s st3).scratch with wsort := wsort' } } =
      fastPropMem s st4 :=
    fastPropMem_with_push_rec s st3 wvec' wstk' wlen' wu' wsort'
  rw [hs4_eq] at hpres_o hpok_t hpok_f hm_p
  unfold fullWatchSize fullWatchOff at hpres_o hpok_t hpok_f
  simp only [fastPropMem_watchSize, fastPropMem_watchOff, fastPropMem_wstk,
    fastPropMem_cur_vars] at hpres_o hpok_t hpok_f
  have hlen4 : st4.LengthsOk c :=
    ⟨{ hlen3.core_ok with
        wvec_len := by simpa only [st4, fastPropMem_wvec] using hlen_p.core_ok.wvec_len
        wstk_len_arr := by
          simpa only [st4, fastPropMem_wstk] using hlen_p.core_ok.wstk_len_arr
        wlen_le := by simpa only [st4, fastPropMem_wlen] using hlen_p.core_ok.wlen_le },
     { hlen3.scratch_ok with
        wsort_len := by simpa only [st4, fastPropMem_wsort] using hlen_p.scratch_ok.wsort_len }⟩
  have hnw4 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st4.core) :=
    fullWitnessInv_nw_congr hlen4.core_ok.cur_vars_le hnw3
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hst4_alen := hlen4.core_ok.arena_len_arr
  have hwvec'_len := hlen4.core_ok.wvec_len
  have hwstk'_len := hlen4.core_ok.wstk_len_arr
  have hidx0_nat : (not_lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * not_lit.toNat :=
    fc_bv64_shl1_u32_nat not_lit
  have hnl_eq_xor : (not_lit ^^^ 1#32) ^^^ 1#32 = not_lit := by
    rw [BitVec.xor_assoc, show (1#32 ^^^ 1#32 : BitVec 32) = 0#32 from by decide,
      BitVec.xor_zero]
  have hlay4 : WatchStackLayout st4.core :=
    hlay_p.with_wstk (by dsimp only [st4]; exact (fastPropMem_cur_vars s st3).symm) rfl rfl rfl
  have ⟨hoff4_bd, hoff4_nat, hp4_nat, hq4_nat, hend4_nat, hq4_1, hq4_2,
      hsw4'⟩ := propLit_b1_after_push (c := c) (F_cur := F_cur) (lit := not_lit ^^^ 1#32)
    (st3 := st3) (st4 := st4) (other := other) (pok := pok) (off_v := off_v) (p_v := p_v)
    (q_v := q_v) (end_v := end_v) (idx0 := (not_lit.setWidth 64 <<< (1 : Nat)).toNat)
    (by rw [hidx0_nat, hnl_eq_xor]) rfl
    (by rw [hnl_eq_xor]; exact hnot_st1) hlen4 hlay4
    (by rw [hnl_eq_xor]; exact hsw3) rfl hrepl_lt
    (by rw [hnl_eq_xor]; exact hrepl_ne_not) hcr_lt hcr_ref3 hp2_nat hq_le
    (fun l hl hne => hpres_o l hl hne)
    (fun ht => let ⟨_, _, hsz, hpre, hw0, hw1⟩ := hpok_t ht; ⟨hsz, hpre, hw0, hw1 rfl⟩)
    (fun hf => (hpok_f hf).1 hrepl_lt)
  simp only [hnl_eq_xor] at hoff4_bd hoff4_nat hp4_nat hq4_nat hend4_nat hsw4'
  have hnot_max4 : not_lit.toNat < 2 * c.max_vars :=
    Nat.lt_of_lt_of_le hnot_st1 (Nat.mul_le_mul_left 2 hlen4.core_ok.cur_vars_le)
  have hidx0_lt4 : (not_lit.setWidth 64 <<< (1 : Nat)).toNat < st4.core.wvec.length := by
    rw [hidx0_nat, hwvec'_len, show 4 * c.max_vars = 2 * (2 * c.max_vars) from by omega]
    exact Nat.mul_lt_mul_of_pos_left hnot_max4 (by decide)
  have hm4_mem_len := fastPropMem_lengthsOk hlen0 hlen4
    (by dsimp [st4, st3]; exact hpi1.cur_vars_eq)
    (by dsimp [st4, st3]; exact hpi1.ag.get FullCoreState.propagated) rfl
  have hm4_wvec := hm4_mem_len.core_ok.wvec_len
  let off4_v : BitVec 64 := (st4.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
    hidx0_lt4).setWidth 64
  let q4_v := off4_v + (q_v - off_v)
  have hq4_lt_c : q4_v.toNat < c.wcap := by
    rw [hq4_nat]; have := hoff4_bd; have := hpi1.sw.q_ge; have := hpi1.sw.p_le_end
    have := hlen4.core_ok.wlen_le; omega
  have hq4_1_lt_c : (q4_v + (1 : BitVec 64)).toNat < c.wcap := by
    rw [hq4_1, hq4_nat]; have := hoff4_bd; have := hpi1.sw.q_ge; have := hpi1.sw.p_le_end
    have := hlen4.core_ok.wlen_le; omega
  have hidx0_lt4_m :
      (not_lit.setWidth 64 <<< (1 : Nat)).toNat < (fastPropMem s st4).core.wvec.length := by
    rw [hm4_wvec, hidx0_nat]; omega
  have hoff4_mem_eq :
      ((fastPropMem s st4).core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
        hidx0_lt4_m).setWidth 64 = off4_v :=
    congrArg (BitVec.setWidth 64) (fc_getElem_wvec s st4)
  have hq4_mem_lt_c :
      (BitVec.setWidth 64 ((fastPropMem s st4).core.wvec[
        (not_lit.setWidth 64 <<< (1 : Nat)).toNat]'hidx0_lt4_m) + (q_v - off_v)).toNat <
        c.wcap := by
    rw [hoff4_mem_eq]; exact hq4_lt_c
  have hq4_1_mem_lt_c :
      (BitVec.setWidth 64 ((fastPropMem s st4).core.wvec[
        (not_lit.setWidth 64 <<< (1 : Nat)).toNat]'hidx0_lt4_m) + (q_v - off_v) +
        (1 : BitVec 64)).toNat < c.wcap := by
    rw [hoff4_mem_eq]; exact hq4_1_lt_c
  have hidx0_lt4_2 : 2 * not_lit.toNat < st4.core.wvec.length := by
    rw [← hidx0_nat]; exact hidx0_lt4
  have hoff4_eq_2 :
      (st4.core.wvec[2 * not_lit.toNat]'hidx0_lt4_2).setWidth 64 = off4_v :=
    congrArg (BitVec.setWidth 64) (fc_getElem_eq_of_idx hidx0_nat hidx0_lt4 hidx0_lt4_2).symm
  have hq4_2_lt_c :
      (BitVec.setWidth 64 (st4.core.wvec[2 * not_lit.toNat]'hidx0_lt4_2) +
        (q_v - off_v)).toNat < c.wcap := by
    rw [hoff4_eq_2]; exact hq4_lt_c
  have hq4_1_2_lt_c :
      (BitVec.setWidth 64 (st4.core.wvec[2 * not_lit.toNat]'hidx0_lt4_2) +
        (q_v - off_v) + (1 : BitVec 64)).toNat < c.wcap := by
    rw [hoff4_eq_2]; exact hq4_1_lt_c
  have hag4 : AgreesExcept propLitCoreMask s.core st4.core :=
    hpi1.ag.update (fun k => { k with
      arena := st4.core.arena, wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' })
  have hperm4 : FullPropDecSpecs.FullArenaPermEq s.core st4.core := hpi1.perm.trans hperm13
  have hsc4 : st4.scratch = { s.scratch with
      search_ticks := st4.scratch.search_ticks, wsort := st4.scratch.wsort,
      phases := st4.scratch.phases } := by
    dsimp only [st4, st3]; rw [hpi1.sc_eq]
  have hnl4 : st4.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 := hnl1
  have hm4_aren := hm4_mem_len.core_ok.arena_len_arr
  have hm4_wstk := hm4_mem_len.core_ok.wstk_len_arr
  fc_head_steps
  · dsimp only
    simp only [hoff4_mem_eq]
    exact hk_ok st4 off4_v m_p (by
      have he4 : (off4_v + (end_v - off_v)).toNat =
          fullWatchOffCore st4.core not_lit.toNat + (end_v.toNat - off_v.toNat) := hend4_nat
      have hp4 : (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat =
          fullWatchOffCore st4.core not_lit.toNat + (p_v.toNat + 2 - off_v.toNat) := by
        simpa only [BitVec.ofNat_eq_ofNat] using hp4_nat
      rw [he4, hp4]
      exact propLit_measure_lt (Nat.le_trans hpi1.sw.q_ge hq_le) hpi1.sw.p_le_end)
      ⟨hlen4, hnw4, hsw4', hag4, hpi1.tr.congr rfl rfl rfl, hperm4, hsc4, hpi1.not_f⟩
      htend1_eq hunass1_eq hunfl1_eq hnl4 hoom1 hct1 hm_p
  · have hfit4 : cref.toNat + 3 + fullArenaClauseSizeCore st4.core cref.toNat ≤
        sem1.core.arena_len := by
      change _ + fullArenaClauseSizeCore st3.core _ ≤ _; rw [hcsz3]; exact hfit1
    have hr_lt4 : ri_f.toNat < fullArenaClauseSizeCore st4.core cref.toNat := by
      change ri_f.toNat < fullArenaClauseSizeCore st3.core _; rw [hcsz3]; exact hr_lt
    have hpi6 := fastProp_b1_oom (off4_v := off4_v) hpi1 hlen4 hnw4
      hsw4' hperm4 rfl rfl hag4 (hpi1.tr.congr rfl rfl rfl) hsc4 hpi1.not_f
      hnot_st1 hq_le hcr_lt hcr_ref3 hflag hfit4 hr2 hr_lt4 hq4_nat
      hp4_nat hq4_2
    have hq4_1_off : (off4_v + (q_v - off_v) + 1#64).toNat =
        (off4_v + (q_v - off_v)).toNat + 1 := by
      simpa only [BitVec.ofNat_eq_ofNat] using hq4_1
    have hm6 : (FullMem c (fastPropMem s { st4 with core := { st4.core with
        arena := (st4.core.arena.set (cref.toNat + 4) not_lit).set
          (cref.toNat + 3 + ri_f.toNat) repl_f,
        wstk := (st4.core.wstk.set q4_v.toNat w0).set (q4_v.toNat + 1) cref,
        oom := 1#64 } }) ⋆ R) m := by
      simp only [BitVec.ofNat_eq_ofNat, hoff4_mem_eq, fastPropMem_arena, fastPropMem_wstk] at hm
      rw [h4_idx, h3r_idx, hq4_1_off] at hm
      rw [← fastPropMem_with_oom_revert]
      exact hm
    dsimp only
    simp only [hoff4_mem_eq, BitVec.ofNat_eq_ofNat]
    exact hk_oom _ off4_v m hpi6 htend1_eq hunass1_eq hunfl1_eq
      (by show (1 : BitVec 64) ≠ 0#64; decide) hm6

private def fastPropBinWatchExpr
    (h_p pWstk vals_p fl_p lvl_p rsns_p tpos_p trl_p ph_p nlits max_v q_v tend_v
      unass_v unfl_v : Val i64)
    (not_lit w0 nl_lvl rsn_bin : Val i32) (rec_ph : Val .bool)
    (k_cont : Val i64 → Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool])
    (k_confl : Val i64 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  .let_ (Op.mk (.mul i64) (.var q_v, (.imm (4 : BitVec 64), ()))) fun v92 =>
  .let_ (Op.mk (.add i64) (.var pWstk, (.var v92.1, ()))) fun v93 =>
  .store (.var w0) (.var v93.1) (
    .let_ (Op.mk (.add i64) (.var q_v, (.imm (1 : BitVec 64), ()))) fun v94 =>
    .let_ (Op.mk (.and i32) (.var w0, (.imm (2147483647 : BitVec 32), ()))) fun v95 =>
    .let_ (Op.mk (.zext 32 64) (.var v95.1, ())) fun v96 =>
    .let_ (Op.mk (.cmp .uge i64) (.var v96.1, (.var nlits, ()))) fun v97 =>
    .jnz (.var v97.1) (k_cont tend_v unass_v unfl_v v94.1) (
      .let_ (Op.mk (.zext 32 64) (.var v95.1, ())) fun v98 =>
      .let_ (Op.mk (.add i64) (.var vals_p, (.var v98.1, ()))) fun v99 =>
      .load i8 (.var v99.1) fun v100 =>
      .let_ (Op.mk (.trunc 32 8) (.imm (0 : BitVec 32), ())) fun v101 =>
      .let_ (Op.mk (.sext 8 32) (.var v100, ())) fun v102 =>
      .let_ (Op.mk (.sext 8 32) (.var v101.1, ())) fun v103 =>
      .let_ (Op.mk (.cmp .sgt i32) (.var v102.1, (.var v103.1, ()))) fun v104 =>
      .jnz (.var v104.1) (k_cont tend_v unass_v unfl_v v94.1) (
        .let_ (Op.mk (.trunc 32 8) (.imm (0 : BitVec 32), ())) fun v105 =>
        .let_ (Op.mk (.sext 8 32) (.var v100, ())) fun v106 =>
        .let_ (Op.mk (.sext 8 32) (.var v105.1, ())) fun v107 =>
        .let_ (Op.mk (.cmp .slt i32) (.var v106.1, (.var v107.1, ()))) fun v108 =>
        .jnz (.var v108.1) (
          .let_ (Op.mk (.add i64) (.var h_p, (.imm (528 : BitVec 64), ()))) fun v109 =>
          .store (t := i64) (.imm (1 : BitVec 64)) (.var v109.1) (
            .let_ (Op.mk (.zext 32 64) (.var not_lit, ())) fun v110 =>
            .let_ (Op.mk (.add i64) (.var h_p, (.imm (536 : BitVec 64), ()))) fun v111 =>
            .store (.var v110.1) (.var v111.1) (
              .let_ (Op.mk (.zext 32 64) (.var v95.1, ())) fun v112 =>
              .let_ (Op.mk (.add i64) (.var h_p, (.imm (544 : BitVec 64), ()))) fun v113 =>
              .store (.var v112.1) (.var v113.1) (
                .let_ (Op.mk (.add i64) (.var h_p, (.imm (176 : BitVec 64), ()))) fun v114 =>
                .store (t := i64) (.imm (4294967295 : BitVec 64)) (.var v114.1)
                  (k_confl v94.1)
              )
            )
          )
        ) (
          fastPropAssignExpr v95.1 nl_lvl rsn_bin rec_ph tend_v unass_v unfl_v max_v
            vals_p fl_p lvl_p rsns_p tpos_p trl_p ph_p
            (fun te un uf => k_cont te un uf v94.1)
        )
      )
    )
  )

private theorem fastProp_bin_watch_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sem : FullState}
    {lit w0 nl_lvl0 rsn_bin : BitVec 32} {rec_ph : Bool}
    {off_v p_v q_v end_v tend_v unass_v unfl_v nlits ignore_ref : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    {k_cont : Val i64 → Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]}
    {k_confl : Val i64 → Expr Val Cont [.bool]}
    (hmaxv : c.max_vars < 2 * dimacsBound) (hwc : c.wcap < 2 * dimacsBound)
    (hlen0 : s.LengthsOk c) (hcv0 : s.core.cur_vars ≤ c.max_vars)
    (hpi : PropLitInv c F0 F_cur s sem (lit ^^^ 1#32).toNat off_v.toNat q_v.toNat
      p_v.toNat end_v.toNat)
    (hlen_mem : (fastPropMem s sem).LengthsOk c)
    (hnlits_eq : nlits.toNat = 2 * s.core.cur_vars)
    (hp_lt : p_v.toNat < end_v.toNat) (_hend_wcap : end_v.toNat ≤ c.wcap)
    (hp_lt_w : p_v.toNat < sem.core.wstk.length)
    (hw0_def : w0 = sem.core.wstk[p_v.toNat]'hp_lt_w)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32)
    (hrsn_eq : rsn_bin = ((lit ^^^ 1#32) &&& 0x7FFFFFFF#32) ||| 0x80000000#32)
    (hnot_st : (lit ^^^ 1#32).toNat < 2 * sem.core.cur_vars)
    (hnl_eq : sem.core.lvl[(lit ^^^ 1#32).toNat / 2]?.getD 0#32 = nl_lvl0)
    (htend_eq : tend_v.toNat = sem.core.trail_end) (hunass_eq : unass_v = sem.core.unassigned)
    (hunfl_eq : unfl_v = sem.core.unflushed) (hoom_st : sem.core.oom = 0#64)
    (hct_st : sem.core.confl_type = s.core.confl_type)
    (hp1_nat : (p_v + 1#64).toNat = p_v.toNat + 1)
    (hq1_nat : (q_v + 1#64).toNat = q_v.toNat + 1)
    (hq_lt_ws : q_v.toNat < sem.core.wstk.length)
    (hm : (FullMem c (fastPropMem s sem) ⋆ R) m)
    (hk_cont : ∀ (sem' : FullState) (tend_n unass_n unfl_n : BitVec 64) (m' : Mem 64),
      PropLitInv c F0 F_cur s sem' (lit ^^^ 1#32).toNat off_v.toNat (q_v + 1#64).toNat
        (p_v.toNat + 1) end_v.toNat →
      tend_n.toNat = sem'.core.trail_end → unass_n = sem'.core.unassigned →
      unfl_n = sem'.core.unflushed →
      sem'.core.lvl[(lit ^^^ 1#32).toNat / 2]?.getD 0#32 = nl_lvl0 →
      sem'.core.oom = 0#64 → sem'.core.confl_type = s.core.confl_type →
      (FullMem c (fastPropMem s sem') ⋆ R) m' →
      wp Γ Q X (k_cont tend_n unass_n unfl_n (q_v + 1#64)) m')
    (hk_confl : ∀ (sem' : FullState) (m' : Mem 64),
      PropLitInv c F0 F_cur s sem' (lit ^^^ 1#32).toNat off_v.toNat (q_v + 1#64).toNat
        (p_v.toNat + 1) end_v.toNat →
      tend_v.toNat = sem'.core.trail_end → unass_v = sem'.core.unassigned →
      unfl_v = sem'.core.unflushed → PropLitConfl F_cur ignore_ref sem'.core →
      (FullMem c (fastPropMem s sem') ⋆ R) m' →
      wp Γ Q X (k_confl (q_v + 1#64)) m') :
    wp Γ Q X (fastPropBinWatchExpr c.hdr c.pWstk c.pVals c.pFlags c.pLevel c.pReason
      c.pTrailPos c.pTrail c.pPhases nlits (BitVec.ofNat 64 c.max_vars)
      q_v tend_v unass_v unfl_v (lit ^^^ 1#32) w0 nl_lvl0 rsn_bin rec_ph k_cont k_confl) m := by
  subst hrsn_eq
  let not_lit : BitVec 32 := lit ^^^ 1#32
  unfold dimacsBound at hmaxv hwc
  have hm_wstk := hlen_mem.core_ok.wstk_len_arr
  have hm_vals := hlen_mem.core_ok.vals_len
  have hcv_eq : sem.core.cur_vars = s.core.cur_vars := hpi.cur_vars_eq
  have hwstk_len := hpi.len.core_ok.wstk_len_arr
  have hp_rem_pos : 0 < end_v.toNat - p_v.toNat := Nat.sub_pos_of_lt hp_lt
  have hq_ge := hpi.sw.q_ge; have hq_le := hpi.sw.q_le_p
  have hw0_get : sem.core.wstk[p_v.toNat]? = some w0 := by
    rw [hw0_def]; exact List.getElem?_eq_getElem hp_lt_w
  have ⟨hother_lt, hent, hrem1⟩ :=
    watchSlice_inv_bin hpi.sw.rem_slice hp_rem_pos hw0_get hflag
  have hsw1 := (hpi.sw.advance_rem (p' := p_v.toNat + 1) (Nat.le_succ _) hp_lt
    (by simpa [Nat.sub_sub] using hrem1)).write_bin
    (c := c) hpi.len.core_ok.cur_vars_le hnot_st hq_le hq_lt_ws hflag hother_lt hent
  let other := w0 &&& 0x7FFFFFFF#32
  have hother_lt' : other.toNat < 2 * sem.core.cur_vars := hother_lt
  let wstk1 := sem.core.wstk.set q_v.toNat w0
  let sem1 : FullState := { sem with core := { sem.core with wstk := wstk1 } }
  have hlen1 : sem1.LengthsOk c :=
    ⟨{ hpi.len.core_ok with wstk_len_arr := by simp [sem1, wstk1, hwstk_len] },
     hpi.len.scratch_ok⟩
  have hnw1 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem1.core) :=
    fullWitnessInv_nw_congr hlen1.core_ok.cur_vars_le hpi.nw
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hpi1 : PropLitInv c F0 F_cur s sem1 not_lit.toNat off_v.toNat (q_v + 1#64).toNat
      (p_v.toNat + 1) end_v.toNat :=
    { len := hlen1, nw := hnw1, sw := by rw [hq1_nat]; exact hsw1
      ag := hpi.ag.update (fun k => { k with wstk := wstk1 })
      tr := hpi.tr.congr rfl rfl rfl, perm := hpi.perm, sc_eq := hpi.sc_eq, not_f := hpi.not_f }
  have hwc64 : c.wcap + 1 < 2 ^ 64 :=
    Nat.lt_trans (Nat.add_lt_add_right hwc 1) (by decide)
  have hq_lt_cap : q_v.toNat < c.wcap := hwstk_len ▸ hq_lt_ws
  have _hq1_lt64 : q_v.toNat + 1 < 2 ^ 64 := by omega
  unfold fastPropBinWatchExpr
  fc_head_steps
  · have hge : 2 * s.core.cur_vars ≤ other.toNat := by
      dsimp only [other]
      simpa only [BitVec.ofNat_eq_ofNat, hnlits_eq] using hc
    exact absurd hother_lt (Nat.not_lt.mpr (hcv_eq.symm ▸ hge))
  · exact hk_cont sem1 tend_v unass_v unfl_v m hpi1 htend_eq hunass_eq hunfl_eq hnl_eq hoom_st
      hct_st (by simpa only [BitVec.ofNat_eq_ofNat, fastPropMem_wstk,
        fastPropMem_with_wstk] using hm)
  · have hov_f := propLit_vals_neg hpi.nw hother_lt (fastProp_lt_vals hpi.len.core_ok hother_lt)
      (by simpa only [BitVec.ofNat_eq_ofNat, fastPropMem_wstk, fastPropMem_vals] using hc)
    have ⟨hpi_c, hcf_c⟩ := propLit_bin_confl (ignore_ref := ignore_ref) hpi hsw1 hnot_st
      hother_lt hent hov_f hp1_nat hq1_nat
    let sem_c : FullState :=
      { sem with core :=
          { sem.core with
            wstk := sem.core.wstk.set q_v.toNat w0, confl_type := 1#64,
            confl_lit0 := not_lit.setWidth 64, confl_lit1 := other.setWidth 64,
            confl_ref := 0xFFFFFFFF#64 } }
    rw [hp1_nat] at hpi_c
    exact hk_confl sem_c m hpi_c htend_eq hunass_eq hunfl_eq hcf_c (by
      simpa only [sem_c, not_lit, other, BitVec.ofNat_eq_ofNat, fastPropMem_wstk,
        fastPropMem_with_bin_confl_wstk] using hm)
  · have hov_un : sem1.core.vals[other.toNat]?.getD 0#8 = 0#8 :=
      propLit_vals_un hnw1 hother_lt' (fastProp_lt_vals hlen1.core_ok hother_lt')
        (by simp only [BitVec.ofNat_eq_ofNat, fastPropMem_wstk, fastPropMem_vals] at *; assumption)
        (by simpa only [other, BitVec.ofNat_eq_ofNat, fastPropMem_wstk, fastPropMem_vals] using hc)
    have hte_lt : sem.core.trail_end < sem.core.cur_vars :=
      hnw1.trail_end_lt_of_unassigned hother_lt' hov_un
    have htend_max : tend_v.toNat < c.max_vars := by
      rw [htend_eq]; exact Nat.lt_of_lt_of_le hte_lt hpi.len.core_ok.cur_vars_le
    have hlen1_mem := fastPropMem_lengthsOk hlen0 hlen1 hcv_eq
      (hpi.ag.get FullCoreState.propagated) rfl
    refine fastProp_assign_wp hmaxv hcv0 hlen1_mem
      hpi.cur_vars_eq hother_lt' hte_lt htend_eq
      (by simpa only [BitVec.ofNat_eq_ofNat, fastPropMem_wstk, fastPropMem_with_wstk] using hm) ?_
    intro flags' ph' unass_n unfl_n m' hfl' hph' hm'
    dsimp only at hm'
    simp only [BitVec.ofNat_eq_ofNat] at hm'
    rw [fastPropMem_assign_eq (te' := sem.core.trail_end + 1)
      (un' := unass_n) (uf' := unfl_n)] at hm'
    have hassign := full_bin_assign_nw_step hlen1.core_ok hnw1 hnot_st hother_lt' hov_un
      hpi.not_f hent (flags' := flags') (unas' := unass_n) (unfl' := unfl_n)
    rw [show sem1.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 from hnl_eq] at hassign
    have ⟨hlen2, hnw2, hsw2, hag2, htr2, hperm2, hsc2, hnot_f2, hnl2⟩ :=
      fastPropMem_eq_of_eq hpi hsw1 (by simp [hwstk_len]) hfl' hph' hnot_st
        hother_lt' hov_un hnl_eq hassign
    have hmv64 : c.max_vars + 1 < 2 ^ 64 :=
      Nat.lt_trans (Nat.add_lt_add_right hmaxv 1) (by decide)
    have ht1_lt : tend_v.toNat + 1 < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.le_of_lt (htend_eq ▸ htend_max)) 1) hmv64
    have htend1 : (tend_v + 1#64).toNat = sem.core.trail_end + 1 := by
      rw [BitVec.toNat_add, htend_eq]
      change (sem.core.trail_end + 1) % 2 ^ 64 = sem.core.trail_end + 1
      exact Nat.mod_eq_of_lt (htend_eq ▸ ht1_lt)
    exact hk_cont _ (tend_v + 1#64) unass_n unfl_n m'
      ⟨hlen2, hnw2, by rwa [hq1_nat], hag2, htr2, hperm2, hsc2, hnot_f2⟩
      htend1 rfl rfl hnl2 hoom_st hct_st hm'

private def fastPropLargeNoReplExpr
    (h_p ignore_ref cbase pAr pWstk vals_p fl_p lvl_p rsns_p tpos_p trl_p ph_p
      max_v q_v tend_v unass_v unfl_v : Val i64)
    (cref other nl_lvl cur_lvl csz : Val i32) (ov : Val i8) (rec_ph : Val .bool)
    (k_cont : Val i64 → Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool])
    (k_confl : Val i64 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  .let_ (Op.mk (.mul i64) (.var q_v, (.imm (4 : BitVec 64), ()))) fun x166 =>
  .let_ (Op.mk (.add i64) (.var pWstk, (.var x166.1, ()))) fun x167 =>
  .let_ (Op.mk (.and i32) (.var other, (.imm (2147483647 : BitVec 32), ()))) fun x168 =>
  .store (.var x168.1) (.var x167.1) (
    .let_ (Op.mk (.add i64) (.var q_v, (.imm (1 : BitVec 64), ()))) fun x169 =>
    .let_ (Op.mk (.mul i64) (.var x169.1, (.imm (4 : BitVec 64), ()))) fun x170 =>
    .let_ (Op.mk (.add i64) (.var pWstk, (.var x170.1, ()))) fun x171 =>
    .store (.var cref) (.var x171.1) (
      .let_ (Op.mk (.add i64) (.var q_v, (.imm (2 : BitVec 64), ()))) fun x172 =>
      .let_ (Op.mk (.zext 32 64) (.var cref, ())) fun x173 =>
      .let_ (Op.mk (.cmp .eq i64) (.var x173.1, (.var ignore_ref, ()))) fun x174 =>
      .jnz (.var x174.1) (k_cont tend_v unass_v unfl_v x172.1) (
        .let_ (Op.mk (.trunc 32 8) (.imm (0 : BitVec 32), ())) fun x175 =>
        .let_ (Op.mk (.sext 8 32) (.var ov, ())) fun x176 =>
        .let_ (Op.mk (.sext 8 32) (.var x175.1, ())) fun x177 =>
        .let_ (Op.mk (.cmp .slt i32) (.var x176.1, (.var x177.1, ()))) fun x178 =>
        .jnz (.var x178.1) (
          .let_ (Op.mk (.add i64) (.var h_p, (.imm (528 : BitVec 64), ()))) fun x179 =>
          .store (t := i64) (.imm (2 : BitVec 64)) (.var x179.1) (
            .let_ (Op.mk (.zext 32 64) (.var cref, ())) fun x180 =>
            .let_ (Op.mk (.add i64) (.var h_p, (.imm (176 : BitVec 64), ()))) fun x181 =>
            .store (.var x180.1) (.var x181.1) (k_confl x172.1)
          )
        ) (
          fastPropAlvlAssignExpr nl_lvl cur_lvl csz other cref rec_ph cbase pAr
            tend_v unass_v unfl_v max_v vals_p fl_p lvl_p rsns_p tpos_p trl_p ph_p
            (fun te un uf => k_cont te un uf x172.1)
        )
      )
    )
  )

private theorem fastProp_large_norepl_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sem1 : FullState}
    {not_lit other cref nl_lvl0 cur_lvl csz32 : BitVec 32} {ov : BitVec 8} {rec_ph : Bool}
    {off_v p_v q_v end_v tend_v unass_v unfl_v ignore_ref : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    {k_cont : Val i64 → Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]}
    {k_confl : Val i64 → Expr Val Cont [.bool]}
    (hmaxv : c.max_vars < 2 * dimacsBound) (har : c.arena_cap < 2 * dimacsBound)
    (hwc : c.wcap < 2 * dimacsBound)
    (hlen0 : s.LengthsOk c) (hcv0 : s.core.cur_vars ≤ c.max_vars)
    (hpi1 : PropLitInv c F0 F_cur s sem1 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hlen1_mem : (fastPropMem s sem1).LengthsOk c)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref1 : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    (hng1 : fullArenaClauseGarbCore sem1.core cref.toNat = false)
    (hfit1 : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (hother_lt : other.toNat < 2 * sem1.core.cur_vars)
    (hnot_st1 : not_lit.toNat < 2 * sem1.core.cur_vars)
    (hother_mem : other.toNat ∈ fullArenaClauseLitsCore sem1.core cref.toNat)
    (hnot_mem : not_lit.toNat ∈ fullArenaClauseLitsCore sem1.core cref.toNat)
    (hunit : ∀ l ∈ fullArenaClauseLitsCore sem1.core cref.toNat,
      l = other.toNat ∨ sem1.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hother_lt1_vals : other.toNat < sem1.core.vals.length)
    (hov_eq : ov = sem1.core.vals[other.toNat]'hother_lt1_vals)
    (hov_np : (0#32).slt ((sem1.core.vals[other.toNat]'hother_lt1_vals).signExtend 32) = false)
    (hnl1 : sem1.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0)
    (hcur_eq : cur_lvl.toNat = s.core.cur_level)
    (hclv_lt32 : s.core.cur_level < 2 ^ 32)
    (hcsz32 : csz32.toNat = fullArenaClauseSizeCore sem1.core cref.toNat)
    (h3_idx : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (htend1_eq : tend_v.toNat = sem1.core.trail_end) (hunass1_eq : unass_v = sem1.core.unassigned)
    (hunfl1_eq : unfl_v = sem1.core.unflushed) (hoom1 : sem1.core.oom = 0#64)
    (hct1 : sem1.core.confl_type = s.core.confl_type)
    (hq1_nat : (q_v + 1#64).toNat = q_v.toNat + 1)
    (hq2_nat : (q_v + 2#64).toNat = q_v.toNat + 2)
    (hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2)
    (hq_le : q_v.toNat ≤ p_v.toNat)
    (hq_lt_ws1 : q_v.toNat < sem1.core.wstk.length)
    (hq1_lt_ws1 : q_v.toNat + 1 < sem1.core.wstk.length)
    (hm : (FullMem c (fastPropMem s sem1) ⋆ R) m)
    (hk_cont : ∀ (sem' : FullState) (tend_n unass_n unfl_n : BitVec 64) (m' : Mem 64),
      PropLitInv c F0 F_cur s sem' not_lit.toNat off_v.toNat (q_v + 2#64).toNat
        (p_v.toNat + 2) end_v.toNat →
      tend_n.toNat = sem'.core.trail_end → unass_n = sem'.core.unassigned →
      unfl_n = sem'.core.unflushed → sem'.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 →
      sem'.core.oom = 0#64 → sem'.core.confl_type = s.core.confl_type →
      (FullMem c (fastPropMem s sem') ⋆ R) m' →
      wp Γ Q X (k_cont tend_n unass_n unfl_n (q_v + 2#64)) m')
    (hk_confl : ∀ (sem' : FullState) (m' : Mem 64),
      PropLitInv c F0 F_cur s sem' not_lit.toNat off_v.toNat (q_v + 2#64).toNat
        (p_v.toNat + 2) end_v.toNat →
      tend_v.toNat = sem'.core.trail_end → unass_v = sem'.core.unassigned →
      unfl_v = sem'.core.unflushed → PropLitConfl F_cur ignore_ref sem'.core →
      (FullMem c (fastPropMem s sem') ⋆ R) m' →
      wp Γ Q X (k_confl (q_v + 2#64)) m') :
    wp Γ Q X (fastPropLargeNoReplExpr c.hdr ignore_ref (cref.setWidth 64 + 3#64) c.pArena c.pWstk
      c.pVals c.pFlags c.pLevel c.pReason c.pTrailPos c.pTrail c.pPhases
      (BitVec.ofNat 64 c.max_vars) q_v tend_v unass_v unfl_v cref other nl_lvl0 cur_lvl csz32
      ov rec_ph k_cont k_confl) m := by
  subst hov_eq
  unfold dimacsBound at hmaxv har hwc
  have hm1_wstk := hlen1_mem.core_ok.wstk_len_arr
  have hm1_aren := hlen1_mem.core_ok.arena_len_arr
  have hm1_alen := hlen1_mem.core_ok.arena_len_le
  have hm1_vals := hlen1_mem.core_ok.vals_len
  have hwstk1 := hpi1.len.core_ok.wstk_len_arr
  have hwc64_2 : c.wcap + 2 < 2 ^ 64 :=
    Nat.lt_trans (Nat.add_lt_add_right hwc 2) (by decide)
  have _hq_lt_cap : q_v.toNat < c.wcap := hwstk1 ▸ hq_lt_ws1
  have _hq1_lt_cap : q_v.toNat + 1 < c.wcap := hwstk1 ▸ hq1_lt_ws1
  unfold fastPropLargeNoReplExpr
  fc_head_steps
  · let sem2 : FullState :=
      { sem1 with core :=
          { sem1.core with
            wstk := (sem1.core.wstk.set q_v.toNat (other &&& 0x7FFFFFFF#32)).set
              (q_v + 1#64).toNat cref } }
    have hinv2 := propLit_inv_keep_large hpi1 hpi1.sw hnot_st1 hq1_nat hq2_nat hp2_nat
      (Nat.add_le_add_right hq_le 2) hpi1.sw.p_le_end (bv32_mask7f_flag0 other)
      hcr_lt hcr_ref1
    simp only [BitVec.ofNat_eq_ofNat, hp2_nat] at hinv2
    refine hk_cont sem2 tend_v unass_v unfl_v m hinv2
      htend1_eq hunass1_eq hunfl1_eq hnl1 hoom1 hct1
      (by simpa only [sem2, BitVec.ofNat_eq_ofNat, fastPropMem_wstk,
        fastPropMem_with_wstk] using hm)
  · have hne_ign : cref.setWidth 64 ≠ ignore_ref := by assumption
    have hov_f := propLit_vals_neg hpi1.nw hother_lt hother_lt1_vals hc
    have ⟨hpi_c, hcf_c⟩ := propLit_large_confl hpi1 hnot_st1 hq_le
      hq1_nat hq2_nat hp2_nat hcr_lt hcr_ref1 hng1 hne_ign hov_f hunit
    let sem_c : FullState :=
      { sem1 with core :=
          { sem1.core with
            wstk := (sem1.core.wstk.set q_v.toNat (other &&& 0x7FFFFFFF#32)).set
              (q_v + 1#64).toNat cref,
            confl_type := 2#64, confl_ref := cref.setWidth 64 } }
    simp only [BitVec.ofNat_eq_ofNat, hp2_nat] at hpi_c
    exact hk_confl sem_c m hpi_c htend1_eq hunass1_eq hunfl1_eq hcf_c
      (by simpa only [sem_c, BitVec.ofNat_eq_ofNat, fastPropMem_wstk,
        fastPropMem_with_large_confl_wstk] using hm)
  · have hov_un := propLit_vals_un hpi1.nw hother_lt hother_lt1_vals hov_np hc
    have hsw2 := hpi1.sw.write_large hnot_st1 hq_le
      hq_lt_ws1 hq1_lt_ws1 (bv32_mask7f_flag0 other) hcr_lt hcr_ref1
    let wstk2 := (sem1.core.wstk.set q_v.toNat (other &&& 0x7FFFFFFF#32)).set (q_v.toNat + 1) cref
    let sem2 : FullState := { sem1 with core := { sem1.core with wstk := wstk2 } }
    have hlen2 : sem2.LengthsOk c :=
      ⟨{ hpi1.len.core_ok with wstk_len_arr := by simp [sem2, wstk2, hwstk1] },
       hpi1.len.scratch_ok⟩
    have hlen2_mem := fastPropMem_lengthsOk hlen0 hlen2 hpi1.cur_vars_eq
      (hpi1.ag.get FullCoreState.propagated) rfl
    have hnw2 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem2.core) :=
      fullWitnessInv_nw_congr hlen2.core_ok.cur_vars_le hpi1.nw
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    have hpi2 : PropLitInv c F0 F_cur s sem2 not_lit.toNat off_v.toNat
        (q_v + 2#64).toNat (p_v.toNat + 2) end_v.toNat :=
      { len := hlen2, nw := hnw2, sw := by rw [hq2_nat]; exact hsw2
        ag := hpi1.ag.update (fun k => { k with wstk := wstk2 })
        tr := hpi1.tr.congr rfl rfl rfl, perm := hpi1.perm,
        sc_eq := hpi1.sc_eq, not_f := hpi1.not_f }
    have hclv_sem2 : sem2.core.cur_level < 2 ^ 32 := by
      rw [hpi2.ag.get FullCoreState.cur_level]; exact hclv_lt32
    have hcur_eq2 : cur_lvl = BitVec.ofNat 32 sem2.core.cur_level := by
      apply BitVec.eq_of_toNat_eq
      rw [hcur_eq, ← hpi2.ag.get FullCoreState.cur_level,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_sem2]
    refine fastProp_large_assign_wp hmaxv har hcv0 hpi2 hlen2_mem hcr_lt hcr_ref1 hng1 hfit1
      hother_lt hov_un hnot_st1 hother_mem hnot_mem hunit hnl1 hcur_eq2 hclv_sem2 hcsz32 h3_idx
      htend1_eq hoom1 hct1
      (by simpa only [sem2, wstk2, BitVec.ofNat_eq_ofNat, hq1_nat, fastPropMem_wstk,
        fastPropMem_with_wstk] using hm) ?_
    intro sem3 tend_n unass_n unfl_n m' hpi3 ht3 hu3 huf3 hnl3 hoom3 hct3 hm'
    exact hk_cont sem3 tend_n unass_n unfl_n m' hpi3 ht3 hu3 huf3 hnl3 hoom3 hct3 hm'

theorem full_prop_lit_wp (Γ : Env)
    (hPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullPropLitSpec args m Q X →
      Func.wp Γ full_prop_lit_body args m Q X := by
  rintro ⟨h, lit, ignore_ref, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hoom0, hm, hQ⟩
  have hmaxv := c.hmaxv; have har := c.harena; have hwc := c.hwcap
  unfold dimacsBound at hmaxv har hwc
  have hcv0 := hlen0.core_ok.cur_vars_le
  let not_lit : BitVec 32 := lit ^^^ 1#32
  have hret_st : ∀ (ok : Bool) (st : FullState) (ml : Mem 64),
      st.LengthsOk c → FullWitnessInv c F0 F_cur st.core →
      AgreesExcept propLitCoreMask s.core st.core →
      FullPropDecSpecs.FullTrailExt s.core st.core →
      FullPropDecSpecs.FullArenaPermEq s.core st.core →
      st.scratch = { s.scratch with
        search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
        phases := st.scratch.phases } →
      (ok = false → PropLitConfl F_cur ignore_ref st.core) →
      (ok = true → st.core.oom = 0#64 ∧ st.core.confl_type = s.core.confl_type) →
      (FullMem c st ⋆ R) ml → Q (ok, ()) ml := by
    intro ok st ml hst_l hst_w hag htr hperm hsc hcf hok_oom hml
    have hst_eq := propLit_eq_upd hag hsc
    have hst_l' := hst_l; have hst_w' := hst_w
    have htr' : FullTrailExt s.core st.core := ⟨htr.te_ge, htr.trl_pref, htr.lvl_pres⟩
    have hperm' : FullArenaPermEq s.core st.core := ⟨hag.get FullCoreState.arena_len, hperm⟩
    rw [hst_eq] at hst_l' hst_w' htr' hperm' hml
    refine hQ ok st.core.vals st.core.flags st.core.lvl st.core.rsns st.core.trl st.core.trail_pos
      st.core.trail_end st.core.unassigned st.core.unflushed st.core.wvec st.core.arena
      st.core.wstk st.core.wlen st.core.wusable st.core.confl_type st.core.confl_ref
      st.core.confl_lit0 st.core.confl_lit1 st.core.oom st.scratch.search_ticks st.scratch.wsort
      st.scratch.phases ml hst_l' hst_w' htr' hperm' ?_ hok_oom hml
    intro hf; rcases (hcf hf) with ho | ⟨hc1, hc2⟩
    · exact Or.inl ho
    · refine Or.inr ⟨?_, hc2⟩
      have hc1' : FullConflictOkW F_cur st := fullConflOkW_to_fullConflictOkW hc1
      rwa [hst_eq] at hc1'
  have hret_noop : Q (true, ()) m :=
    hret_st true s m hlen0 hw0 (.refl _ _) (.refl _) (.refl _) rfl (by simp)
      (fun _ => ⟨hoom0, rfl⟩) hm
  have hvl0 := hlen0.core_ok.vals_len; have hwv0 := hlen0.core_ok.wvec_len
  have hlvl0 := hlen0.core_ok.lvl_len
  have hclv_lt32 : s.core.cur_level < 2 ^ 32 := by
    have := hw0.cur_level_le; have := hlen0.core_ok.trail_end_le; omega
  have hte0_lt64 : s.core.trail_end < 2 ^ 64 := by
    have := hlen0.core_ok.trail_end_le; omega
  unfold Func.wp full_prop_lit_body
  fc_head_steps
  · exact hret_noop
  · exact hret_noop
  · exact hret_noop
  · have hnot_xor : not_lit.toNat = lit.toNat ^^^ 1 := bv32_xor_1 lit
    have hnot_lt : not_lit.toNat < 2 * s.core.cur_vars := by
      have h1 : ¬ 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 ≤ lit.toNat ^^^ 1 := by assumption
      rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at h1; omega
    have hnot_f0 : s.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 := by
      have hsge : (0#32).sle ((s.core.vals[not_lit.toNat]'(by omega)).signExtend 32) = false := by
        have h2 : (0#32).sle ((s.core.vals[lit.toNat ^^^ 1]'(by omega)).signExtend 32) = false := by
          assumption
        simpa only [hnot_xor] using h2
      rw [bv32_sle0_eq_not_slt0, Bool.not_eq_false'] at hsge
      have hget : s.core.vals[not_lit.toNat]?.getD 0#8 = s.core.vals[not_lit.toNat]'(by omega) := by
        simp [List.getElem?_eq_getElem (show not_lit.toNat < s.core.vals.length by omega)]
      rw [hget]; exact (full_i8_vals_slt0 (by rw [← hget]; exact hw0.vals_domain _ hnot_lt)).mp hsge
    have hidx0 : ((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)).toNat =
        2 * not_lit.toNat := bv64_shl1_u32 not_lit
    have hidx1 : (((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
        (1 : BitVec 64)).toNat = 2 * not_lit.toNat + 1 := by
      rw [bv64_add1_toNat (by rw [hidx0]; omega), hidx0]
    have hoff0_eq : (s.core.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<<
        (1 : BitVec 64)).toNat]'(by omega)).toNat = fullWatchOffCore s.core not_lit.toNat := by
      unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact congrArg BitVec.toNat (by congr 1)
    have hsz0_eq : (s.core.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
        (1 : BitVec 64)).toNat]'(by omega)).toNat = fullWatchSizeCore s.core not_lit.toNat := by
      unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact congrArg BitVec.toNat (by congr 1)
    have hsz0_pos : 0 < fullWatchSizeCore s.core not_lit.toNat := by
      rw [← hsz0_eq]
      have h1 : (2 * (lit.toNat ^^^ 1) + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
          (((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
            (1 : BitVec 64)).toNat := by
        rw [hidx1, ← hnot_xor]; change (2 * not_lit.toNat + 1) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      have heq_w : s.core.wvec[(2 * (lit.toNat ^^^ 1) + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(
            by omega) = s.core.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
            (1 : BitVec 64)).toNat]'(by omega) := by congr 1
      have hne0 : (s.core.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
          (1 : BitVec 64)).toNat]'(by omega)).setWidth 64 ≠ 0#64 := fun heq => hc (by
        change (s.core.wvec[(2 * (lit.toNat ^^^ 1) + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(
          by omega)).setWidth 64 = 0#64
        rw [heq_w]; exact heq)
      exact Nat.pos_of_ne_zero fun h0 =>
        hne0 (BitVec.eq_of_toNat_eq (by rw [bv_c0_zext32_64, h0]; rfl))
    clear hc; clear hc
    have hwat0 : WatchesInv F_cur s.core := by
      have h := hw0.watches; unfold ModeWatchesInv at h; simpa [hdense0] using h
    have hnw0 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c s.core) :=
      fullWitnessInv_to_nw hcv0 hw0
    have hpi0 : PropLitInv c F0 F_cur s s not_lit.toNat (fullWatchOffCore s.core not_lit.toNat)
        (fullWatchOffCore s.core not_lit.toNat) (fullWatchOffCore s.core not_lit.toNat)
        (fullWatchOffCore s.core not_lit.toNat + fullWatchSizeCore s.core not_lit.toNat) :=
      { len := hlen0, nw := hnw0, sw := SplitWatchesInv.init hnot_lt hwat0 hsz0_pos
        ag := .refl _ _, tr := .refl _, perm := .refl _, sc_eq := rfl, not_f := hnot_f0 }
    have hnl_lvl_idx :
        (BitVec.setWidth 64 ((lit ^^^ (1 : BitVec 32)) >>> (1 : Nat))).toNat <
          s.core.lvl.length := by
      rw [bv_c0_zext32_64, bv32_lshr_1, bv32_xor_1, hlen0.core_ok.lvl_len]; omega
    let nl_lvl0 :=
      s.core.lvl[(BitVec.setWidth 64 ((lit ^^^ (1 : BitVec 32)) >>> (1 : Nat))).toNat]'hnl_lvl_idx
    have hnl_eq0 : s.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 := by
      have hidx : (BitVec.setWidth 64 ((lit ^^^ (1 : BitVec 32)) >>> (1 : Nat))).toNat =
          not_lit.toNat / 2 := by
        rw [bv_c0_zext32_64, bv32_lshr_1]; rfl
      rw [← hidx, List.getElem?_eq_getElem hnl_lvl_idx, Option.getD_some]
    fc_head_steps
    refine wp_loop_break_group
      (brkTs := [i64, i64, i64, i64, i64, i64, i64, i64, .bool])
      (lpTs := [i64, i64, i64, i64, i64, i64, i64, i64])
      (fun (off_v, tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, end_v, confl_v, ()) mb =>
        ∃ sem : FullState,
          PropLitInv c F0 F_cur s sem not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat ∧
          tend_v.toNat = sem.core.trail_end ∧ unass_v = sem.core.unassigned ∧
          unfl_v = sem.core.unflushed ∧
          (confl_v = false → sem.core.oom = 0#64 ∧ sem.core.confl_type = s.core.confl_type) ∧
          (confl_v = true → PropLitConfl F_cur ignore_ref sem.core) ∧
          (FullMem c (fastPropMem s sem) ⋆ R) mb)
      (fun rem (off_v, tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, end_v, ()) ml =>
        ∃ sem : FullState,
          rem = end_v.toNat - p_v.toNat ∧
          PropLitInv c F0 F_cur s sem not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat ∧
          tend_v.toNat = sem.core.trail_end ∧ unass_v = sem.core.unassigned ∧
          unfl_v = sem.core.unflushed ∧
          sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 ∧
          sem.core.oom = 0#64 ∧ sem.core.confl_type = s.core.confl_type ∧
          (FullMem c (fastPropMem s sem) ⋆ R) ml) ?_ ?_ ?_
    · rintro _ ⟨off_v, tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, end_v, confl_v, ⟨⟩⟩ mb
        ⟨sem, hpi, htend_eq, hunass_eq, hunfl_eq, hcf_f, hcf_t, hmb⟩
      exact fastProp_finish_wp c.hwcap hcv0 hdense0 hnot_lt hpi htend_eq hunass_eq
        hunfl_eq hcf_f hcf_t hmb fun ok st ml hl hw hag htr hperm hsc hcf hoom hml =>
        hret_st ok st ml hl hw hag htr hperm hsc hcf hoom hml
    · -- Loop 1 body `L`
      rintro B L rem ⟨off_v, tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, end_v, ⟨⟩⟩ ml hB ih
        ⟨sem, rfl, hpi, htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_st, hct_st, hml⟩
      have hcv_eq : sem.core.cur_vars = s.core.cur_vars := hpi.cur_vars_eq
      have hnot_st : not_lit.toNat < 2 * sem.core.cur_vars := hcv_eq.symm ▸ hnot_lt
      clear hret_noop hoff0_eq hsz0_eq hsz0_pos hpi0 hnw0 hnot_f0 hm hw0 hwat0
      have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_st
      have hend_wcap : end_v.toNat ≤ c.wcap := Nat.le_trans hend_le hwlen_le
      have hwc64 : c.wcap + 1 < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_right hwc 1) (by decide)
      have hwc64_2 : c.wcap + 2 < 2 ^ 64 :=
        Nat.lt_trans (Nat.add_lt_add_right hwc 2) (by decide)
      have hq_ge := hpi.sw.q_ge; have hq_le := hpi.sw.q_le_p; have hp_le := hpi.sw.p_le_end
      have hpr_eq_sem : sem.core.propagated = s.core.propagated :=
        hpi.ag.get FullCoreState.propagated
      have hlen_mem := fastPropMem_lengthsOk hlen0 hpi.len hcv_eq hpr_eq_sem rfl
      have hm_wstk := hlen_mem.core_ok.wstk_len_arr; have hm_vals := hlen_mem.core_ok.vals_len
      have hm_aren := hlen_mem.core_ok.arena_len_arr
      have hm_alen := hlen_mem.core_ok.arena_len_le
      have hm_wvec := hlen_mem.core_ok.wvec_len; have hm_lvl := hlen_mem.core_ok.lvl_len
      have hm_fl := hlen_mem.core_ok.flags_len; have hm_trl := hlen_mem.core_ok.trl_len
      have hm_tp := hlen_mem.core_ok.trail_pos_len; have hm_rsn := hlen_mem.core_ok.rsns_len
      have hm_ph := hlen_mem.scratch_ok.phases_len
      have hwstk_len := hpi.len.core_ok.wstk_len_arr; have hvals_len := hpi.len.core_ok.vals_len
      have hwstk_mem : (fastPropMem s sem).core.wstk.length = c.wcap := by
        rw [fastPropMem_wstk]; exact hwstk_len
      have haren_len := hpi.len.core_ok.arena_len_arr; have halen_le := hpi.len.core_ok.arena_len_le
      have hwvec_len := hpi.len.core_ok.wvec_len; have hlvl_len := hpi.len.core_ok.lvl_len
      have hfl_len := hpi.len.core_ok.flags_len; have htrl_len := hpi.len.core_ok.trl_len
      have htp_len := hpi.len.core_ok.trail_pos_len; have hrsn_len := hpi.len.core_ok.rsns_len
      have hph_len := hpi.len.scratch_ok.phases_len
      have hcv_lt64 : s.core.cur_vars < 2 ^ 64 :=
        Nat.lt_of_le_of_lt hcv0 (Nat.lt_trans hmaxv (by decide))
      have h2cv_lt64 : 2 * s.core.cur_vars < 2 ^ 64 :=
        Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 hcv0)
          (Nat.lt_trans (Nat.mul_lt_mul_of_pos_left hmaxv (by decide)) (by decide))
      have hp1_pre : (p_v + (1 : BitVec 64)).toNat = p_v.toNat + 1 :=
        bv64_add1_toNat (Nat.lt_of_le_of_lt
          (Nat.add_le_add_right (Nat.le_trans hp_le hend_wcap) 1) hwc64)
      fc_head_split
      · -- Active watch iteration `p_v < end_v`
        have hp_lt : p_v.toNat < end_v.toNat := by assumption
        have hp_lt_w : p_v.toNat < sem.core.wstk.length :=
          hwstk_len ▸ Nat.lt_of_lt_of_le hp_lt hend_wcap
        have hp_rem_pos : 0 < end_v.toNat - p_v.toNat := Nat.sub_pos_of_lt hp_lt
        have hp1_nat : (p_v + 1#64).toNat = p_v.toNat + 1 := hp1_pre
        have hq1_nat : (q_v + 1#64).toNat = q_v.toNat + 1 :=
          bv64_add1_toNat (Nat.lt_of_le_of_lt
            (Nat.add_le_add_right (Nat.le_trans hq_le (Nat.le_trans hp_le hend_wcap)) 1) hwc64)
        have hq_lt_ws : q_v.toNat < sem.core.wstk.length :=
          hwstk_len ▸ Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hq_le hp_lt) hend_wcap
        fc_head_split
        · -- Binary watch `(w0 &&& 0x80000000) ≠ 0`
          have hflag : (sem.core.wstk[p_v.toNat]'hp_lt_w &&& 0x80000000#32) ≠ 0#32 := by
            simpa only [ne_eq, ← BitVec.ofNat_eq_ofNat, fc_getElem_wstk, fastPropMem_wstk]
              using hc
          refine fastProp_bin_watch_wp
            (ignore_ref := ignore_ref)
            (q_v := q_v) (tend_v := tend_v) (unass_v := unass_v) (unfl_v := unfl_v)
            (nl_lvl0 := nl_lvl0)
            (rsn_bin := ((lit ^^^ 1#32) &&& 0x7FFFFFFF#32) ||| 0x80000000#32)
            (rec_ph := s.core.probing == 0#64)
            (k_cont := fun te un uf qn => .jump L (.var off_v, (.var te, (.var un,
              (.var uf, (.var ticks_v, (.var (p_v + (1 : BitVec 64)), (.var qn,
              (.var end_v, ())))))))))
            (k_confl := fun qn => .jump B (.var off_v, (.var tend_v, (.var unass_v,
              (.var unfl_v, (.var ticks_v, (.var (p_v + (1 : BitVec 64)), (.var qn,
              (.var end_v, (.imm true, ()))))))))))
            c.hmaxv c.hwcap hlen0 hcv0 hpi hlen_mem ?_ hp_lt
            hend_wcap hp_lt_w (fc_getElem_wstk s sem)
            ((fc_getElem_wstk s sem).symm ▸ hflag) rfl hnot_st hnl_eq htend_eq
            hunass_eq hunfl_eq hoom_st hct_st hp1_nat hq1_nat hq_lt_ws hml ?_ ?_
          · rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt64,
              Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm, Nat.mod_eq_of_lt h2cv_lt64]
          · intro sem' tend_n unass_n unfl_n m' hpi' ht' hu' huf' hnl' hoom' hct' hm'
            exact ih (end_v.toNat - (p_v.toNat + 1)) (off_v, tend_n, unass_n, unfl_n, ticks_v,
              p_v + 1#64, q_v + 1#64, end_v, ()) m'
              (Nat.sub_lt hp_rem_pos Nat.zero_lt_one)
              ⟨sem', by rw [hp1_nat], by rwa [hp1_nat], ht', hu', huf', hnl',
                hoom', hct', hm'⟩
          · intro sem' m' hpi' ht' hu' huf' hcf' hm'
            exact hB (off_v, tend_v, unass_v, unfl_v, ticks_v, p_v + 1#64, q_v + 1#64, end_v,
              true, ()) m' ⟨sem', by rwa [hp1_nat], ht', hu', huf', by simp,
                fun _ => hcf', hm'⟩
        · -- Large watch `(w0 &&& 0x80000000) == 0`
          have hw0_get : sem.core.wstk[p_v.toNat]? = some (sem.core.wstk[p_v.toNat]'hp_lt_w) :=
            List.getElem?_eq_getElem hp_lt_w
          have hflag : (sem.core.wstk[p_v.toNat]'hp_lt_w &&& 0x80000000#32) = 0#32 := by
            simpa only [← BitVec.ofNat_eq_ofNat, fc_getElem_wstk, fastPropMem_wstk] using hc
          have ⟨h2le, cref0, hcr_get, hcr_lt, hcr_ref, hrem2⟩ :=
            watchSlice_inv_large hpi.sw.rem_slice hp_rem_pos hw0_get hflag
          fc_head_split
          · -- Dead `p + 1 >= end`
            have hge : end_v.toNat ≤ (p_v + (1 : BitVec 64)).toNat := hc
            rw [hp1_pre] at hge
            have h2_le_end : p_v.toNat + 2 ≤ end_v.toNat :=
              Nat.add_sub_cancel' hp_le ▸ Nat.add_le_add_left h2le p_v.toNat
            exact absurd hge (Nat.not_le.mpr (Nat.lt_of_succ_le h2_le_end))
          · fc_head_steps
            have h2_le_end : p_v.toNat + 2 ≤ end_v.toNat :=
              Nat.add_sub_cancel' hp_le ▸ Nat.add_le_add_left h2le p_v.toNat
            have hrem_dec : end_v.toNat - (p_v.toNat + 2) < end_v.toNat - p_v.toNat :=
              fc_rem2_lt h2_le_end
            have hp2_wcap : p_v.toNat + 2 ≤ c.wcap := Nat.le_trans h2_le_end hend_wcap
            have hp2_64 : p_v.toNat + 2 < 2 ^ 64 :=
              Nat.lt_of_le_of_lt hp2_wcap (Nat.lt_trans hwc (by decide))
            have hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2 := by
              rw [bv64_add_toNat (a := p_v + 1#64) (b := 1#64) (by rw [hp1_nat]; exact hp2_64),
                hp1_nat]; rfl
            have hq2_nat : (q_v + 2#64).toNat = q_v.toNat + 2 :=
              bv64_add2_toNat (a := q_v) (Nat.lt_of_le_of_lt
                (Nat.add_le_add_right (Nat.le_trans hq_le (Nat.le_trans hp_le hend_wcap)) 2)
                hwc64_2)
            have hq_lt_ws2 : q_v.toNat < sem.core.wstk.length :=
              hwstk_len ▸ Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hq_le
                (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 2)) h2_le_end))
                hend_wcap
            have hq1_lt_ws2 : q_v.toNat + 1 < sem.core.wstk.length :=
              hwstk_len ▸ Nat.lt_of_lt_of_le
                (Nat.lt_of_le_of_lt (Nat.add_le_add_right hq_le 1)
                  (Nat.lt_of_lt_of_le (Nat.lt_succ_self (p_v.toNat + 1)) h2_le_end)) hend_wcap
            have hcr_idx_lt : (p_v + 1#64).toNat < sem.core.wstk.length := by
              rw [hp1_nat, hwstk_len]
              exact Nat.lt_of_lt_of_le (Nat.lt_of_succ_le h2_le_end) hend_wcap
            have hcr_eq : sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx_lt = cref0 := by
              have h1 : sem.core.wstk[p_v.toNat + 1]? =
                  some (sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx_lt) := by
                rw [← hp1_nat]; exact List.getElem?_eq_getElem hcr_idx_lt
              exact Option.some.inj (h1.symm.trans hcr_get)
            simp only [fastPropMem_wstk]
            generalize hcr_gen :
              sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx_lt = cref at hcr_eq ⊢
            generalize hw0_gen : sem.core.wstk[p_v.toNat]'(hwstk_len ▸
              Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 2))
                h2_le_end) hend_wcap) = w0 at hflag ⊢
            rw [← hcr_eq] at hcr_lt hcr_ref
            have hsw_drop : SplitWatchesInv F_cur sem.core not_lit.toNat off_v.toNat q_v.toNat
                (p_v.toNat + 2) end_v.toNat :=
              hpi.sw.advance_rem (p' := p_v.toNat + 2) (by omega) h2_le_end
                (by simpa [Nat.sub_sub] using hrem2)
            -- Join `Js_2`: blocking literal did NOT satisfy clause
            refine wp_join_group (fun () m1 => m1 = ml) ?_ ?_
            · rintro _ ⟨⟩ ml1 hml1; subst ml1
              have hcr_wf := hpi.nw.arena.refs_wf cref.toNat hcr_ref
              have hcr3_le : cref.toNat + 3 ≤ sem.core.arena_len := hcr_wf.1
              have hcsz3 : 3 ≤ fullArenaClauseSizeCore sem.core cref.toNat := hcr_wf.2.1
              have hcr_next : cref.toNat + 3 + fullArenaClauseSizeCore sem.core cref.toNat ≤
                  fullArenaNextOff sem.core.arena sem.core.arena_len cref.toNat := hcr_wf.2.2.1
              have hnext_le : fullArenaNextOff sem.core.arena sem.core.arena_len cref.toNat ≤
                  sem.core.arena_len := hcr_wf.2.2.2.1
              have hcr_fit : cref.toNat + 3 + fullArenaClauseSizeCore sem.core cref.toNat ≤
                  sem.core.arena_len := Nat.le_trans hcr_next hnext_le
              have ⟨hcr0_lt_ar, hcr2_lt_ar, hcr3_lt_ar, hcr4_lt_ar, hcr3_lt64, hal_lt64⟩ :=
                fc_cref_bounds hpi.len.core_ok (Nat.lt_trans har (by decide)) hcsz3 hcr_fit
              have hcr64 : (cref.setWidth 64).toNat = cref.toNat := bv_c0_zext32_64 cref
              have hcr_u64 : (cref.setWidth 64).toNat + 4 < 2 ^ 64 := by
                rw [hcr64]; exact Nat.lt_trans (Nat.add_lt_add_right cref.isLt 4) (by decide)
              have h1_idx : (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1 := by
                rw [bv64_add_toNat (a := cref.setWidth 64) (b := 1#64)
                  (Nat.lt_trans (Nat.add_lt_add_left (by decide) _) hcr_u64), hcr64]; rfl
              have h2_idx : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by
                rw [bv64_add_toNat (a := cref.setWidth 64) (b := 2#64)
                  (Nat.lt_trans (Nat.add_lt_add_left (by decide) _) hcr_u64), hcr64]; rfl
              have h3_idx : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3 := by
                rw [bv64_add_toNat (a := cref.setWidth 64) (b := 3#64)
                  (Nat.lt_trans (Nat.add_lt_add_left (by decide) _) hcr_u64), hcr64]; rfl
              have h4_idx : (cref.setWidth 64 + 4#64).toNat = cref.toNat + 4 := by
                rw [bv64_add_toNat (a := cref.setWidth 64) (b := 4#64) hcr_u64, hcr64]; rfl
              fc_head_steps
              · -- Dead `cref + 3 > alen`
                have halen_eq : sem.core.arena_len = s.core.arena_len :=
                  hpi.ag.get FullCoreState.arena_len
                have hgt : sem.core.arena_len % 2 ^ 64 < (cref.toNat + 3) % 2 ^ 64 := by
                  simpa only [halen_eq, fastPropMem_arena_len, hcr64, BitVec.reduceToNat] using hc
                rw [Nat.mod_eq_of_lt hal_lt64, Nat.mod_eq_of_lt hcr3_lt64] at hgt
                exact absurd hgt (Nat.not_lt.mpr hcr3_le)
              · exact ih _ (off_v, tend_v, unass_v, unfl_v, ticks_v + 1#64, p_v + 1#64 + 1#64,
                  q_v, end_v, ()) ml hrem_dec
                  ⟨sem, by rw [hp2_nat], propLit_inv_drop (ticks' := sem.scratch.search_ticks) hpi
                    hsw_drop hp2_nat, htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_st, hct_st, hml⟩
              · exact ih _ (off_v, tend_v, unass_v, unfl_v, ticks_v + 1#64, p_v + 1#64 + 1#64,
                  q_v, end_v, ()) ml hrem_dec
                  ⟨sem, by rw [hp2_nat], propLit_inv_drop (ticks' := sem.scratch.search_ticks) hpi
                    hsw_drop hp2_nat, htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_st, hct_st, hml⟩
              · exact ih _ (off_v, tend_v, unass_v, unfl_v, ticks_v + 1#64, p_v + 1#64 + 1#64,
                  q_v, end_v, ()) ml hrem_dec
                  ⟨sem, by rw [hp2_nat], propLit_inv_drop (ticks' := sem.scratch.search_ticks) hpi
                    hsw_drop hp2_nat, htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_st, hct_st, hml⟩
              · -- Live clause: `if (l0 == not_lit) ... else if (l1 != not_lit)` -> join `Js_3`
                have hng_t : fullArenaClauseGarbCore sem.core cref.toNat = false := by
                  unfold fullArenaClauseGarbCore fullArenaHdrCore
                  have hget : sem.core.arena[cref.toNat]? =
                      some (sem.core.arena[cref.toNat]'hcr0_lt_ar) :=
                    List.getElem?_eq_getElem hcr0_lt_ar
                  rw [hget, Option.getD_some]
                  have hh : ((fastPropMem s sem).core.arena[(cref.setWidth 64).toNat]'
                      (by rw [fastPropMem_arena, hcr64]; exact hcr0_lt_ar) &&&
                        0x00080000#32) = 0#32 := by
                    assumption
                  have h0 : (sem.core.arena[cref.toNat]'hcr0_lt_ar &&& 0x00080000#32) = 0#32 := by
                    have hh' := hh
                    simp only [← BitVec.ofNat_eq_ofNat, fastPropMem_arena, hcr64] at hh'
                    exact hh'
                  rw [h0]; rfl
                try clear hc; try clear hc; try clear hc; try clear hc
                refine wp_join_group
                  (fun (other, ()) mj => ∃ sem1 : FullState,
                    PropLitInv c F0 F_cur s sem1 not_lit.toNat off_v.toNat q_v.toNat
                      (p_v.toNat + 2) end_v.toNat ∧
                    sem1.core.oom = 0#64 ∧ sem1.core.confl_type = s.core.confl_type ∧
                    sem1.core.arena_len = sem.core.arena_len ∧
                    sem1.core.trail_end = sem.core.trail_end ∧
                    sem1.core.unassigned = sem.core.unassigned ∧
                    sem1.core.unflushed = sem.core.unflushed ∧
                    sem1.core.cur_level = sem.core.cur_level ∧
                    sem1.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 ∧
                    cref.toNat ∈ fullArenaClauseRefsCore sem1.core ∧
                    fullArenaClauseGarbCore sem1.core cref.toNat = false ∧
                    fullArenaClauseSizeCore sem1.core cref.toNat =
                      fullArenaClauseSizeCore sem.core cref.toNat ∧
                    sem1.core.arena[cref.toNat + 3]? = some other ∧
                    sem1.core.arena[cref.toNat + 4]? = some not_lit ∧
                    (FullMem c (fastPropMem s sem1) ⋆ R) mj) ?_ ?_
                · rintro _ ⟨other, ⟨⟩⟩ mj ⟨sem1, hpi1, hoom1, hct1, halen1, hte1_eq, hun1_eq,
                    huf1_eq, hcl1_eq, hnl1, hcr_ref1, hng1, hcsz1, har3, har4, hmj⟩
                  have htend1_eq : tend_v.toNat = sem1.core.trail_end := htend_eq.trans hte1_eq.symm
                  have hunass1_eq : unass_v = sem1.core.unassigned := hunass_eq.trans hun1_eq.symm
                  have hunfl1_eq : unfl_v = sem1.core.unflushed := hunfl_eq.trans huf1_eq.symm
                  have hlen1_mem := fastPropMem_lengthsOk hlen0 hpi1.len hpi1.cur_vars_eq
                    (hpi1.ag.get FullCoreState.propagated) rfl
                  have hm1_aren := hlen1_mem.core_ok.arena_len_arr
                  have hm1_alen := hlen1_mem.core_ok.arena_len_le
                  have hm1_vals := hlen1_mem.core_ok.vals_len
                  have haren1 := hpi1.len.core_ok.arena_len_arr
                  have halen1_le := hpi1.len.core_ok.arena_len_le
                  have hvals1 := hpi1.len.core_ok.vals_len
                  have hwstk1 := hpi1.len.core_ok.wstk_len_arr
                  have hwvec1 := hpi1.len.core_ok.wvec_len; have hlvl1 := hpi1.len.core_ok.lvl_len
                  have hfl1 := hpi1.len.core_ok.flags_len; have htrl1 := hpi1.len.core_ok.trl_len
                  have htp1 := hpi1.len.core_ok.trail_pos_len
                  have hrsn1 := hpi1.len.core_ok.rsns_len
                  have hph1 := hpi1.len.scratch_ok.phases_len
                  have hcv1_eq := hpi1.cur_vars_eq
                  have hnot_st1 : not_lit.toNat < 2 * sem1.core.cur_vars := hcv1_eq.symm ▸ hnot_lt
                  have hcsz3_1 : 3 ≤ fullArenaClauseSizeCore sem1.core cref.toNat :=
                    hcsz1.symm ▸ hcsz3
                  have hfit1 : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤
                      sem1.core.arena_len := by rw [hcsz1, halen1]; exact hcr_fit
                  have hcr3_le1 : cref.toNat + 3 ≤ sem1.core.arena_len :=
                    Nat.le_trans (Nat.le_add_right _ _) hfit1
                  have hcr_lt_alen1 : cref.toNat < sem1.core.arena_len :=
                    Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 3)) hcr3_le1
                  have ⟨_, hcr2_lt_ar1, hcr3_lt_ar1, hcr4_lt_ar1, _, _⟩ :=
                    fc_cref_bounds hpi1.len.core_ok (Nat.lt_trans har (by decide)) hcsz3_1 hfit1
                  have hfit1_ar : ∀ {k}, k < fullArenaClauseSizeCore sem1.core cref.toNat →
                      cref.toNat + 3 + k < sem1.core.arena.length := fun hk =>
                    haren1 ▸ Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk (cref.toNat + 3))
                      (Nat.le_trans hfit1 halen1_le)
                  have hother_mem : other.toNat ∈ fullArenaClauseLitsCore sem1.core cref.toNat := by
                    refine (mem_fullArenaClauseLitsCore_iff (haren1 ▸ Nat.le_trans hfit1
                      halen1_le)).mpr ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 3) hcsz3_1, ?_⟩
                    exact congrArg BitVec.toNat (Option.some.inj
                      ((List.getElem?_eq_getElem hcr3_lt_ar1).symm.trans har3))
                  have hother_lt : other.toNat < 2 * sem1.core.cur_vars :=
                    hpi1.nw.arena.lits_lt cref.toNat hcr_ref1 hng1 other.toNat hother_mem
                  have hother_lt1_vals : other.toNat < sem1.core.vals.length :=
                    fastProp_lt_vals hpi1.len.core_ok hother_lt
                  have hq_lt_ws1 : q_v.toNat < sem1.core.wstk.length := by
                    rw [hwstk1, ← hwstk_len]; exact hq_lt_ws2
                  have hq1_lt_ws1 : q_v.toNat + 1 < sem1.core.wstk.length := by
                    rw [hwstk1, ← hwstk_len]; exact hq1_lt_ws2
                  have hcsz_eq1 :
                      (sem1.core.arena[(cref.setWidth 64 + 2#64).toNat]'(h2_idx ▸
                        hcr2_lt_ar1)).toNat = fullArenaClauseSizeCore sem1.core cref.toNat := by
                    unfold fullArenaClauseSizeCore
                    rw [List.getElem?_eq_getElem hcr2_lt_ar1, Option.getD_some]
                    exact congrArg BitVec.toNat
                      (fc_getElem_eq_of_idx h2_idx (h2_idx ▸ hcr2_lt_ar1) hcr2_lt_ar1)
                  fc_head_steps
                  · -- Dead `other >= nlits`
                    have hge : 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 ≤ other.toNat := by
                      simpa only [fastPropMem_cur_vars] using hc
                    rw [Nat.mod_eq_of_lt hcv_lt64, Nat.mod_eq_of_lt h2cv_lt64] at hge
                    exact absurd (hcv1_eq ▸ hother_lt) (Nat.not_lt.mpr hge)
                  · -- `vals[other] > 0`: keep large watch & continue
                    exact ih _ (off_v, tend_v, unass_v, unfl_v, ticks_v + 1#64,
                        p_v + 1#64 + 1#64, q_v + 2#64, end_v, ()) m hrem_dec
                      ⟨_, by rw [hp2_nat], propLit_inv_keep_large hpi1 hpi1.sw hnot_st1 hq1_nat
                        hq2_nat hp2_nat (Nat.add_le_add_right hq_le 2)
                        hpi1.sw.p_le_end (bv32_mask7f_flag0 other) hcr_lt hcr_ref1,
                        htend1_eq, hunass1_eq, hunfl1_eq, hnl1, hoom1, hct1, by
                          simpa only [← BitVec.ofNat_eq_ofNat, fastPropMem_wstk,
                            fastPropMem_with_wstk] using hm⟩
                  · -- `vals[other] ≤ 0`: inline two-pass replacement search
                    have hov_np :
                        (0#32).slt ((sem1.core.vals[other.toNat]'hother_lt1_vals).signExtend 32) =
                          false := by
                      simpa only [fastPropMem_vals] using hc
                    try clear hc; try clear hc
                    -- Join for `if (srch < 2u || srch >= csz) { srch = 2u; }`
                    refine wp_join_group (fun (srch_v, ()) ms =>
                        2 ≤ srch_v.toNat ∧
                        srch_v.toNat < fullArenaClauseSizeCore sem1.core cref.toNat ∧
                        ms = mj) ?_ ?_
                    · rintro _ ⟨srch_v, ⟨⟩⟩ ms ⟨hsrch2, hsrch_lt, hms⟩
                      subst ms
                      have hm0_aren := hlen_mem.core_ok.arena_len_arr
                      let csz32 := (fastPropMem s sem).core.arena[
                        (cref.setWidth 64 + 2#64).toNat]'(by
                          rw [hm0_aren, ← haren_len, h2_idx]; exact hcr2_lt_ar)
                      have hcsz32_nat :
                          csz32.toNat = fullArenaClauseSizeCore sem1.core cref.toNat := by
                        rw [hcsz1]
                        have h1 := congrArg BitVec.toNat
                          ((fc_getElem_arena s sem (hi := (by
                              rw [hm0_aren, ← haren_len, h2_idx]; exact hcr2_lt_ar))).trans
                            (fc_getElem_eq_of_idx h2_idx (h2_idx ▸ hcr2_lt_ar) hcr2_lt_ar))
                        have h2 : (sem.core.arena[cref.toNat + 2]'hcr2_lt_ar).toNat =
                            fullArenaClauseSizeCore sem.core cref.toNat := by
                          unfold fullArenaClauseSizeCore
                          rw [List.getElem?_eq_getElem hcr2_lt_ar, Option.getD_some]
                        exact h1.trans h2
                      have hcsz_lt32 : fullArenaClauseSizeCore sem1.core cref.toNat < 2 ^ 32 :=
                        hcsz32_nat ▸ csz32.isLt
                      have hcsz_lt_ff : fullArenaClauseSizeCore sem1.core cref.toNat < 0xFFFFFFFF :=
                        Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left _ _) hfit1)
                          (Nat.lt_of_le_of_lt halen1_le
                            (Nat.lt_trans har (by decide : 2 * 2 ^ 28 < 0xFFFFFFFF)))
                      fc_head_steps
                      refine fastProp_repl_search_wp
                        (nlits := BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat))
                        c.hmaxv c.harena hcv0 ?_ hpi1 hlen1_mem hfit1
                        h3_idx hcsz32_nat hsrch2 hsrch_lt hmj ?_
                      · rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt64,
                          Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm, Nat.mod_eq_of_lt h2cv_lt64]
                      · rintro ri_f repl_f _rf hres_f
                        rcases hres_f with ⟨rfl, hfind_bad⟩ | ⟨hri_ne, hr2, hr_lt, hrepl_def, hcand⟩
                        · -- No replacement (`ri_f == 0xFFFFFFFF`): keep watch, check confl/assign
                          have hunit := propLit_hunit hpi1.nw hcr_ref1 hng1
                            (haren1 ▸ Nat.le_trans hfit1 halen1_le) har3 har4
                            hpi1.not_f fun k hk1 hk2 => by
                              change k < fullArenaClauseSizeCore sem1.core cref.toNat at hk2
                              have hb := hfind_bad k hk1 (by rwa [← hcr64] at hk2)
                              unfold fullFindReplBad at hb ⊢; rwa [hcr64]
                          have hnot_mem : not_lit.toNat ∈
                              fullArenaClauseLitsCore sem1.core cref.toNat := by
                            refine (mem_fullArenaClauseLitsCore_iff
                              (haren1 ▸ Nat.le_trans hfit1 halen1_le)).mpr
                                ⟨1, Nat.lt_of_lt_of_le (by decide : 1 < 3) hcsz3_1, ?_⟩
                            exact congrArg BitVec.toNat (Option.some.inj
                              ((List.getElem?_eq_getElem hcr4_lt_ar1).symm.trans har4))
                          have hcur_eq1 :
                              ((BitVec.ofNat 64 s.core.cur_level).setWidth 32).toNat =
                                s.core.cur_level := by
                            have hcl64 : s.core.cur_level < 2 ^ 64 :=
                              Nat.lt_trans hclv_lt32 (by decide)
                            rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                              Nat.mod_eq_of_lt hcl64, Nat.mod_eq_of_lt hclv_lt32]
                          fc_head_split
                          all_goals first
                            | exact absurd rfl hc
                            | exact fastProp_large_norepl_wp
                                (nl_lvl0 := nl_lvl0)
                                (cur_lvl := (BitVec.ofNat 64 s.core.cur_level).setWidth 32)
                                (rec_ph := s.core.probing == 0#64)
                                (k_cont := fun te un uf qn => .jump L (.var off_v, (.var te,
                                  (.var un, (.var uf, (.var (ticks_v + 1#64),
                                  (.var (p_v + 1#64 + 1#64), (.var qn, (.var end_v, ())))))))))
                                (k_confl := fun qn => .jump B (.var off_v, (.var tend_v,
                                  (.var unass_v, (.var unfl_v, (.var (ticks_v + 1#64),
                                  (.var (p_v + 1#64 + 1#64), (.var qn, (.var end_v,
                                  (.imm true, ()))))))))))
                                c.hmaxv c.harena c.hwcap hlen0 hcv0
                                hpi1 hlen1_mem hcr_lt hcr_ref1 hng1 hfit1 hother_lt hnot_st1
                                hother_mem hnot_mem hunit hother_lt1_vals (fc_getElem_vals s sem1)
                                hov_np hnl1 hcur_eq1 hclv_lt32 hcsz32_nat h3_idx htend1_eq
                                hunass1_eq hunfl1_eq hoom1 hct1 hq1_nat hq2_nat hp2_nat
                                hq_le hq_lt_ws1 hq1_lt_ws1 hmj
                                (fun sem' tend_n unass_n unfl_n m' hpi' ht' hu' huf' hnl'
                                    hoom' hct' hm' => by
                                  fc_head_steps
                                  exact ih _ (off_v, tend_n, unass_n, unfl_n, ticks_v + 1#64,
                                    p_v + 1#64 + 1#64, q_v + 2#64, end_v, ()) m' hrem_dec
                                    ⟨sem', by rw [hp2_nat], by rwa [hp2_nat], ht', hu', huf',
                                     hnl', hoom', hct', hm'⟩)
                                (fun sem' m' hpi' ht' hu' huf' hcf' hm' => by
                                  fc_head_steps
                                  exact hB (off_v, tend_v, unass_v, unfl_v, ticks_v + 1#64,
                                    p_v + 1#64 + 1#64, q_v + 2#64, end_v, true, ()) m'
                                    ⟨sem', by rwa [hp2_nat], ht', hu', huf', by simp,
                                     fun _ => hcf', hm'⟩)
                        · -- Replacement found (`ri_f ≠ 0xFFFFFFFF`)
                          have hri_ne : ri_f ≠ 0xFFFFFFFF#32 := hri_ne
                          have h3_1_idx : (cref.setWidth 64 + 3#64 + 1#64).toNat =
                              cref.toNat + 4 := by
                            rw [bv64_add_toNat (by
                              rw [h3_idx, ← hcr64, show (1#64).toNat = 1 from rfl]
                              exact hcr_u64), h3_idx]
                            rfl
                          fc_head_split
                          · refine fastProp_large_push_wp hPush (nl_lvl0 := nl_lvl0)
                              (k_ok := fun o4 pn qn en => .jump L (.var o4, (.var tend_v,
                                (.var unass_v, (.var unfl_v, (.var (ticks_v + 1#64),
                                (.var pn, (.var qn, (.var en, ())))))))))
                              (k_oom := fun o4 pn qn en => .jump B (.var o4, (.var tend_v,
                                (.var unass_v, (.var unfl_v, (.var (ticks_v + 1#64),
                                (.var pn, (.var qn, (.var en, (.imm true, ()))))))))))
                              c.hmaxv c.harena hlen0 hcv0
                              hpi1 hlen1_mem hcr_lt hcr_ref1 hfit1 har4 hnot_st1 hother_lt
                              hflag hr2 hr_lt hrepl_def hcand h1_idx h3_idx h3_1_idx
                              htend1_eq hunass1_eq hunfl1_eq hnl1 hoom1 hct1 hp2_nat hq_le
                              (hwstk1 ▸ hq_lt_ws1) hmj ?_ ?_
                            · intro st4 off4_v m_p hdec4 hpi4 ht4 hu4 huf4 hnl4 hoom4 hct4 hm4
                              exact ih _ (off4_v, tend_v, unass_v, unfl_v, ticks_v + 1#64,
                                off4_v + (p_v + 1#64 + 1#64 - off_v), off4_v + (q_v - off_v),
                                off4_v + (end_v - off_v), ()) m_p hdec4
                                ⟨st4, rfl, hpi4, ht4, hu4, huf4, hnl4, hoom4, hct4, hm4⟩
                            · intro st6 off4_v m_f hpi6 ht6 hu6 huf6 hoom6 hm6
                              exact hB (off4_v, tend_v, unass_v, unfl_v, ticks_v + 1#64,
                                off4_v + (p_v + 1#64 + 1#64 - off_v),
                                off4_v + (q_v - off_v) + 2#64,
                                off4_v + (end_v - off_v), true, ()) m_f
                                ⟨_, hpi6, ht6, hu6, huf6, by simp, fun _ => Or.inl hoom6, hm6⟩
                          · exact absurd hc hri_ne
                    · intro Jsrch hJsrch; fc_head_steps
                      · exact hJsrch (2#32, ()) mj
                          ⟨by decide,
                           Nat.lt_of_lt_of_le (by decide : (2#32).toNat < 3) hcsz3_1, rfl⟩
                      · exact hJsrch (2#32, ()) mj
                          ⟨by decide,
                           Nat.lt_of_lt_of_le (by decide : (2#32).toNat < 3) hcsz3_1, rfl⟩
                      · have h1_mod : (cref.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 =
                            cref.toNat + 1 := by
                          simp only [BitVec.reduceToNat]
                          exact Nat.mod_eq_of_lt (by omega)
                        have h2_mod : (cref.toNat + (2 : BitVec 64).toNat) % 2 ^ 64 =
                            cref.toNat + 2 := by
                          simp only [BitVec.reduceToNat]
                          exact Nat.mod_eq_of_lt (by omega)
                        have hnot_le_srch :
                            ¬ fullArenaClauseSizeCore sem1.core cref.toNat ≤
                              (sem1.core.arena[cref.toNat + 1]'(by rw [haren1]; omega)).toNat := by
                          have hh : ¬ (sem.core.arena[(cref.toNat + (2 : BitVec 64).toNat) %
                                  2 ^ 64]'(by rw [h2_mod]; exact hcr2_lt_ar)).toNat ≤
                              (sem1.core.arena[(cref.toNat + (1 : BitVec 64).toNat) %
                                  2 ^ 64]'(by rw [h1_mod, haren1]; omega)).toNat := by
                            simpa only [fc_getElem_arena, fastPropMem_arena] using hc
                          have hcsz_0 : (sem.core.arena[cref.toNat + 2]'hcr2_lt_ar).toNat =
                              fullArenaClauseSizeCore sem1.core cref.toNat := by
                            rw [hcsz1]; unfold fullArenaClauseSizeCore
                            rw [List.getElem?_eq_getElem hcr2_lt_ar, Option.getD_some]
                          simp only [fc_getElem_eq_of_idx h2_mod _ hcr2_lt_ar, hcsz_0,
                            fc_getElem_eq_of_idx h1_mod _ (by rw [haren1]; omega)] at hh
                          exact hh
                        have h1_mod' : (cref.toNat + 1) % 2 ^ 64 = cref.toNat + 1 :=
                          Nat.mod_eq_of_lt (by omega)
                        have hnot_lt_2 :
                            ¬ (sem1.core.arena[cref.toNat + 1]'(by rw [haren1]; omega)).toNat < 2 :=
                          by
                          have hh : ¬ ((fastPropMem s sem1).core.arena[(cref.toNat +
                                (1 : BitVec 64).toNat) % 2 ^ 64]'(by
                              rw [fastPropMem_arena, h1_mod, haren1]; omega)).toNat <
                              (2 : BitVec 32).toNat := by assumption
                          simpa only [fc_getElem_arena, fastPropMem_arena, BitVec.reduceToNat,
                            h1_mod'] using hh
                        have hsrch_mem :
                            (fastPropMem s sem1).core.arena[(cref.setWidth 64 + 1).toNat]'(by
                              rw [show (1 : BitVec 64) = 1#64 from rfl, fastPropMem_arena,
                                h1_idx, haren1]
                              omega) =
                            sem1.core.arena[cref.toNat + 1]'(by rw [haren1]; omega) := by
                          rw [fc_getElem_arena]
                          exact fc_getElem_eq_of_idx
                            (by rw [show (1 : BitVec 64) = 1#64 from rfl]; exact h1_idx) _ _
                        refine hJsrch _ mj
                          ⟨by simpa only [hsrch_mem] using Nat.le_of_not_lt hnot_lt_2,
                           by simpa only [hsrch_mem] using Nat.lt_of_not_le hnot_le_srch, rfl⟩
                · intro J3 hJ3; fc_head_steps
                  · let l1 := sem.core.arena[(cref.setWidth 64 + 4#64).toNat]'(h4_idx ▸ hcr4_lt_ar)
                    have h3_mod : (cref.toNat + BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 =
                        cref.toNat + 3 := by
                      simp only [BitVec.reduceToNat]
                      exact Nat.mod_eq_of_lt hcr3_lt64
                    have hl0_is_not : sem.core.arena[cref.toNat + 3]'hcr3_lt_ar = not_lit :=
                      (fc_getElem_eq_of_idx h3_mod _ _).symm.trans
                        ((fc_getElem_arena s sem).symm.trans hc)
                    have hpi_drop : PropLitInv c F0 F_cur s sem not_lit.toNat off_v.toNat
                        q_v.toNat (p_v.toNat + 2) end_v.toNat :=
                      ⟨hpi.len, hpi.nw, hsw_drop, hpi.ag, hpi.tr, hpi.perm, hpi.sc_eq,
                       hpi.not_f⟩
                    have ⟨hpi1, href1, hng1, hcsz1, har3, har4⟩ := fastProp_js3_swap hpi_drop
                      hcr_ref hng_t hcsz3 hcr_fit hl0_is_not
                      (fc_getElem_eq_of_idx h4_idx.symm hcr4_lt_ar (h4_idx ▸ hcr4_lt_ar))
                    have h3_1_idx : (cref.setWidth 64 + 3#64 + 1#64).toNat = cref.toNat + 4 := by
                      rw [bv64_add_toNat (by
                        rw [h3_idx, ← hcr64, show (1#64).toNat = 1 from rfl]; exact hcr_u64),
                        h3_idx]; rfl
                    have hl1_mem_eq :
                        (fastPropMem s sem).core.arena[
                          (cref.setWidth 64 + 3#64 + 1#64).toNat]'(by
                            rw [fastPropMem_arena, h3_1_idx]; exact hcr4_lt_ar) = l1 := by
                      rw [fc_getElem_arena]
                      exact (fc_getElem_eq_of_idx h3_1_idx _ hcr4_lt_ar).trans
                        (fc_getElem_eq_of_idx h4_idx.symm hcr4_lt_ar (h4_idx ▸ hcr4_lt_ar))
                    have hm1 : (FullMem c (fastPropMem s { sem with core := { sem.core with
                        arena := (sem.core.arena.set (cref.toNat + 3) l1).set
                          (cref.toNat + 4) not_lit } }) ⋆ R) m := by
                      simp only [BitVec.ofNat_eq_ofNat, fastPropMem_arena,
                        h3_idx, h3_1_idx] at hm
                      have hl1_idx : sem.core.arena[cref.toNat + 4]'hcr4_lt_ar = l1 :=
                        fc_getElem_eq_of_idx h4_idx.symm hcr4_lt_ar (h4_idx ▸ hcr4_lt_ar)
                      rw [hl1_idx, show (lit ^^^ 1#32) = not_lit from rfl] at hm
                      simpa only [← fastPropMem_with_arena] using hm
                    simp only [BitVec.ofNat_eq_ofNat]
                    rw [hl1_mem_eq]
                    exact hJ3 (l1, ()) m ⟨_, hpi1, hoom_st, hct_st, rfl, rfl, rfl, rfl, rfl,
                      hnl_eq, href1, hng1, hcsz1, har3, har4, hm1⟩
                  · exact ih _ (off_v, tend_v, unass_v, unfl_v, ticks_v + 1#64, p_v + 1#64 + 1#64,
                      q_v, end_v, ()) ml hrem_dec
                      ⟨sem, by rw [hp2_nat], propLit_inv_drop (ticks' := sem.scratch.search_ticks)
                        hpi hsw_drop hp2_nat, htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_st,
                        hct_st, hml⟩
                  · have h4_mod :
                        (cref.toNat + BitVec.toNat (3 : BitVec 64) + BitVec.toNat (1 : BitVec 64)) %
                          2 ^ 64 = cref.toNat + 4 := by
                      simp only [BitVec.reduceToNat]
                      exact Nat.mod_eq_of_lt (by omega)
                    have hl1_eq4 : sem.core.arena[cref.toNat + 4]'(hcr4_lt_ar) = not_lit :=
                      (fc_getElem_eq_of_idx h4_mod _ _).symm.trans
                        ((fc_getElem_arena s sem).symm.trans hc)
                    exact hJ3 (_, ()) ml ⟨sem, ⟨hpi.len, hpi.nw, hsw_drop, hpi.ag, hpi.tr,
                        hpi.perm, hpi.sc_eq, hpi.not_f⟩, hoom_st, hct_st, rfl, rfl, rfl, rfl, rfl,
                      hnl_eq, hcr_ref, hng_t, rfl,
                      by rw [fc_getElem_arena, List.getElem?_eq_getElem hcr3_lt_ar]
                         exact congrArg some
                           (fc_getElem_eq_of_idx
                             (by rw [show (3 : BitVec 64) = 3#64 from rfl]; exact h3_idx.symm)
                             hcr3_lt_ar _),
                      by change sem.core.arena[cref.toNat + 4]? = some not_lit
                         rw [← hl1_eq4]; exact List.getElem?_eq_getElem hcr4_lt_ar,
                      hml⟩
            · intro J2 hJ2; fc_head_steps
              · exact ih _ (off_v, tend_v, unass_v, unfl_v, ticks_v, p_v + 1#64 + 1#64,
                  q_v + 2#64, end_v, ()) m hrem_dec
                  ⟨_, by rw [hp2_nat], propLit_inv_keep_large hpi hsw_drop hnot_st hq1_nat hq2_nat
                    hp2_nat (Nat.add_le_add_right hq_le 2) h2_le_end hflag hcr_lt hcr_ref,
                    htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_st, hct_st, by
                      simpa only [fastPropMem_wstk, fastPropMem_with_wstk] using hm⟩
              · exact hJ2 () ml rfl
              · exact hJ2 () ml rfl
      · -- Loop exit `!(p < end)`: jump to `B` with `confl = false`
        exact hB (off_v, tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, end_v, false, ()) ml
          ⟨sem, hpi, htend_eq, hunass_eq, hunfl_eq, fun _ => ⟨hoom_st, hct_st⟩, by simp, hml⟩
    · intro B L _ hL; fc_head_steps
      have hoff_bd := hwat0.layout.bounds not_lit.toNat hnot_lt
      have hwlen_le := hlen0.core_ok.wlen_le
      have hoff_nat :
          ((s.core.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)).toNat]'(by
            rw [fc_bv64_shl1_u32_nat, show (lit ^^^ (1 : BitVec 32)) = not_lit from rfl, hwv0]
            have := Nat.mul_le_mul_left 2 hcv0; omega)).setWidth 64).toNat =
          fullWatchOffCore s.core not_lit.toNat := by
        unfold fullWatchOffCore
        rw [bv_c0_zext32_64]
        exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx (fc_bv64_shl1_u32_nat _) _)
      have hsz_nat : ((s.core.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)) +
          (1 : BitVec 64)).toNat]'(by
            rw [fc_bv64_shl1_add1_nat, show (lit ^^^ (1 : BitVec 32)) = not_lit from rfl, hwv0]
            have := Nat.mul_le_mul_left 2 hcv0; omega)).setWidth 64).toNat =
          fullWatchSizeCore s.core not_lit.toNat := by
        unfold fullWatchSizeCore
        rw [bv_c0_zext32_64]
        exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx (fc_bv64_shl1_add1_nat _) _)
      have hend_nat :
          ((s.core.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)).toNat]'(by
            rw [fc_bv64_shl1_u32_nat, show (lit ^^^ (1 : BitVec 32)) = not_lit from rfl, hwv0]
            have := Nat.mul_le_mul_left 2 hcv0; omega)).setWidth 64 +
          (s.core.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)) +
            (1 : BitVec 64)).toNat]'(by
              rw [fc_bv64_shl1_add1_nat, show (lit ^^^ (1 : BitVec 32)) = not_lit from rfl, hwv0]
              have := Nat.mul_le_mul_left 2 hcv0; omega)).setWidth 64).toNat =
          fullWatchOffCore s.core not_lit.toNat + fullWatchSizeCore s.core not_lit.toNat := by
        rw [bv64_add_toNat (by
          rw [hoff_nat, hsz_nat]
          exact Nat.lt_of_le_of_lt (Nat.le_trans hoff_bd hwlen_le) (Nat.lt_trans hwc (by decide))),
          hoff_nat, hsz_nat]
      have hoff_g : ∀ h,
          ((s.core.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)).toNat]'h).setWidth
            64).toNat = fullWatchOffCore s.core not_lit.toNat := fun _ => hoff_nat
      have hend_g : ∀ h1 h2,
          ((s.core.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)).toNat]'h1).setWidth
            64 +
          (s.core.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)) +
            (1 : BitVec 64)).toNat]'h2).setWidth 64).toNat =
          fullWatchOffCore s.core not_lit.toNat + fullWatchSizeCore s.core not_lit.toNat :=
        fun _ _ => hend_nat
      have htend0 : (BitVec.ofNat 64 s.core.trail_end).toNat = s.core.trail_end := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hte0_lt64]
      refine hL _ _ m ⟨s, rfl, ?_, htend0, rfl, rfl, hnl_eq0, hoom0, rfl, ?_⟩
      · rw [hend_g, hoff_g]; exact hpi0
      · rw [fastPropMem_self]; exact hm

theorem full_propagate_ignore_wp (Γ : Env)
    (hPropLit : ∀ args m Q X, fullPropLitSpec args m Q X →
      Γ "full_prop_lit" [i64, i32, i64] [.bool] args m Q X) :
    ∀ args m Q X, fullPropagateIgnoreSpec args m Q X →
      Func.wp Γ full_propagate_ignore_body args m Q X := by
  rintro ⟨h, ignore_ref, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hret_st : ∀ (r : BitVec 64) (st : FullState) (ml : Mem 64),
      st.LengthsOk c → FullWitnessInv c F0 F_cur st.core →
      AgreesExcept fastPropCoreMask s.core st.core →
      FullTrailExt s.core st.core → FullArenaPermEq s.core st.core →
      st.core.fuel.toNat ≤ s.core.fuel.toNat →
      st.scratch = { s.scratch with
        search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
        phases := st.scratch.phases } →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → st.core.propagated = st.core.trail_end ∧
        st.core.confl_type = s.core.confl_type ∧
        (s.core.oom = 0#64 → st.core.oom = 0#64) ∧
        (s.core.propagated < s.core.trail_end → st.core.fuel.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → st.core.fuel.toNat < s.core.fuel.toNat ∧ st.core.oom = 0#64 ∧
        FullConflictOkW F_cur st ∧
        (st.core.confl_type = 2#64 → st.core.confl_ref ≠ ignore_ref)) →
      (r = 2#64 → st.core.oom ≠ 0#64 ∨ st.core.fuel = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ st = s) →
      (FullMem c st ⋆ R) ml → Q (r, ()) ml := by
    intro r st ml hst_l hst_w hag htr hperm hfl hsc hr hr0 hr1 hr2 hnoop hml
    have hst_eq : st =
        { core :=
            { s.core with
              vals := st.core.vals, flags := st.core.flags, lvl := st.core.lvl,
              rsns := st.core.rsns, trl := st.core.trl, trail_pos := st.core.trail_pos,
              trail_end := st.core.trail_end, propagated := st.core.propagated,
              unassigned := st.core.unassigned, unflushed := st.core.unflushed,
              wvec := st.core.wvec, arena := st.core.arena, wstk := st.core.wstk,
              wlen := st.core.wlen, wusable := st.core.wusable, fuel := st.core.fuel,
              confl_type := st.core.confl_type, confl_ref := st.core.confl_ref,
              confl_lit0 := st.core.confl_lit0, confl_lit1 := st.core.confl_lit1,
              oom := st.core.oom }
          scratch := { s.scratch with
            search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
            phases := st.scratch.phases } } := by
      have h1 := hag.get FullCoreState.d_cur; have h2 := hag.get FullCoreState.d_val
      have h3 := hag.get FullCoreState.cur_vars; have h4 := hag.get FullCoreState.arena_len
      have h5 := hag.get FullCoreState.arena_garbage
      have h6 := hag.get FullCoreState.first_reducible
      have h7 := hag.get FullCoreState.num_irred; have h8 := hag.get FullCoreState.num_redundant
      have h9 := hag.get FullCoreState.num_binary; have h10 := hag.get FullCoreState.probing
      have h11 := hag.get FullCoreState.cur_level; have h12 := hag.get FullCoreState.tmp_cnt
      have h13 := hag.get FullCoreState.tmp_len; have h14 := hag.get FullCoreState.min_clr_len
      have h15 := hag.get FullCoreState.min_clr_full; have h16 := hag.get FullCoreState.dense_mode
      have h17 := hag.get FullCoreState.inconsistent; have h18 := hag.get FullCoreState.lit_mark
      have h19 := hag.get FullCoreState.mrk; have h20 := hag.get FullCoreState.tmp
      have h21 := hag.get FullCoreState.min_clr; have h22 := hag.get FullCoreState.frame_trail
      have h23 := hag.get FullCoreState.frame_dec; have h24 := hag.get FullCoreState.repr
      have h25 := hag.get FullCoreState.min_stk
      cases st with | mk stc stsc =>
      cases s with | mk sc ssc =>
      dsimp only at hsc; rw [hsc]
      cases stc; cases sc; simp only at *; subst_vars; rfl
    have hst_l' := hst_l; have hst_w' := hst_w; have htr' := htr; have hperm' := hperm
    rw [hst_eq] at hst_l' hst_w' htr' hperm' hml
    refine hQ r st.core.vals st.core.flags st.core.lvl st.core.rsns st.core.trl st.core.trail_pos
      st.core.trail_end st.core.propagated st.core.unassigned st.core.unflushed st.core.wvec
      st.core.arena st.core.wstk st.core.wlen st.core.wusable st.core.fuel st.core.confl_type
      st.core.confl_ref st.core.confl_lit0 st.core.confl_lit1 st.core.oom
      st.scratch.search_ticks st.scratch.wsort st.scratch.phases ml
      hst_l' hst_w' htr' hperm' hfl hr hr0 ?_ hr2 ?_ hml
    · intro h1; have hcf := hr1 h1; rw [hst_eq] at hcf; exact hcf
    · intro hpe; obtain ⟨h0, heq⟩ := hnoop hpe; exact ⟨h0, hst_eq ▸ heq⟩
  unfold Func.wp full_propagate_ignore_body
  fc_hsteps
  refine wp_loop_group
    (fun rem (prop_v, fuel_v, ()) ml => ∃ memSt : FullState,
      rem = fuel_v.toNat ∧ memSt.LengthsOk c ∧ FullWitnessInv c F0 F_cur memSt.core ∧
      memSt.core.fuel = s.core.fuel ∧ memSt.core.propagated = prop_v.toNat ∧
      AgreesExcept fastPropCoreMask s.core memSt.core ∧
      FullTrailExt s.core memSt.core ∧ FullArenaPermEq s.core memSt.core ∧
      fuel_v.toNat ≤ s.core.fuel.toNat ∧
      memSt.scratch = { s.scratch with
        search_ticks := memSt.scratch.search_ticks, wsort := memSt.scratch.wsort,
        phases := memSt.scratch.phases } ∧
      (s.core.oom = 0#64 → memSt.core.oom = 0#64) ∧
      memSt.core.confl_type = s.core.confl_type ∧
      (fuel_v.toNat = s.core.fuel.toNat →
        { memSt with core := { memSt.core with fuel := fuel_v } } = s) ∧
      (s.core.propagated = s.core.trail_end → memSt = s ∧ fuel_v = s.core.fuel) ∧
      (FullMem c memSt ⋆ R) ml) ?_ ?_
  · rintro L rem ⟨prop_v, fuel_v, ⟨⟩⟩ ml ih
      ⟨memSt, rfl, hml_l, hml_w, hmfuel, hmprop, hag, htr, hperm, hfuel_le, hsc, hoom_pres,
        hct_pres, hsame, hnoop, hml⟩
    have hcl := hml_l.core_ok
    have hcv_le := hcl.cur_vars_le
    have htl := hcl.trl_len; have hte_le := hcl.trail_end_le; have hpr_le := hcl.propagated_le
    have hdm_st : memSt.core.dense_mode = 0#64 := (hag.get FullCoreState.dense_mode).trans hdense0
    fc_hsteps
    · -- `prop < trail_end` and `oom ≠ 0`
      have hpr_lt : prop_v.toNat < memSt.core.trail_end := by c0_bound
      have hne_end : s.core.propagated ≠ s.core.trail_end := fun h => by
        obtain ⟨hm_s, _⟩ := hnoop h; subst hm_s; omega
      let finSt : FullState :=
        { memSt with core := { memSt.core with propagated := prop_v.toNat, fuel := fuel_v } }
      exact hret_st 2#64 finSt m
        ⟨{ hcl with propagated_le := by dsimp [finSt]; omega }, hml_l.scratch_ok⟩
        (hml_w.with_fuel_prop fuel_v prop_v.toNat)
        (hag.update fun k => { k with propagated := prop_v.toNat, fuel := fuel_v })
        (fastTrailExt_congr htr rfl rfl rfl) hperm hfuel_le hsc (Or.inr (Or.inr rfl))
        (by simp) (by simp) (fun _ => Or.inl hc) (fun hpe => absurd hpe hne_end)
        (by simpa [finSt, hmprop] using hm)
    · -- `prop < trail_end` and `fuel == 0`
      have hpr_lt : prop_v.toNat < memSt.core.trail_end := by c0_bound
      have hne_end : s.core.propagated ≠ s.core.trail_end := fun h => by
        obtain ⟨hm_s, _⟩ := hnoop h; subst hm_s; omega
      let finSt : FullState :=
        { memSt with core := { memSt.core with propagated := prop_v.toNat, fuel := fuel_v } }
      exact hret_st 2#64 finSt m
        ⟨{ hcl with propagated_le := by dsimp [finSt]; omega }, hml_l.scratch_ok⟩
        (hml_w.with_fuel_prop fuel_v prop_v.toNat)
        (hag.update fun k => { k with propagated := prop_v.toNat, fuel := fuel_v })
        (fastTrailExt_congr htr rfl rfl rfl) hperm hfuel_le hsc (Or.inr (Or.inr rfl))
        (by simp) (by simp) (fun _ => Or.inr hc) (fun hpe => absurd hpe hne_end)
        (by simpa [finSt, hmprop] using hm)
    · -- Active iteration: `fuel ≠ 0 ∧ oom == 0 ∧ prop < trail_end`
      have hpr_lt : prop_v.toNat < memSt.core.trail_end := by c0_bound
      have hne_end : s.core.propagated ≠ s.core.trail_end := fun h => by
        obtain ⟨hm_s, _⟩ := hnoop h; subst hm_s; omega
      have hoom0_st : memSt.core.oom = 0#64 := by assumption
      have hfuel_sub : (fuel_v - 1#64).toNat = fuel_v.toNat - 1 := bv64_sub1_toNat hc
      have hfuel_pos : 0 < fuel_v.toNat :=
        Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
      have hpr1 : (prop_v + (1 : BitVec 64)).toNat = prop_v.toNat + 1 := by c0_bound
      let memSt1 : FullState :=
        { memSt with core := { memSt.core with propagated := prop_v.toNat + 1 } }
      have hlen1 : memSt1.LengthsOk c :=
        ⟨{ hcl with propagated_le := by dsimp [memSt1]; omega }, hml_l.scratch_ok⟩
      have hw1 : FullWitnessInv c F0 F_cur memSt1.core := hml_w.with_fuel_prop _ _
      have hm1_mem : (FullMem c memSt1 ⋆ R) m := by
        simpa only [memSt1, show (prop_v + (1 : BitVec 64)).toNat = prop_v.toNat + 1 from hpr1]
          using hm
      c0_call hPropLit
      refine ⟨c, F0, F_cur, memSt1, R, rfl, hlen1, hw1, hdm_st, hoom0_st, hm1_mem,
        fun ok vals' flags' lvl' rsns' trl' tp' te' unas' unfl' wvec' arena' wstk' wlen' wu'
          ctype' cref' c0' c1' oom' ticks' wsort' phases' m2 hlen2 hw2 htr2 hperm2
          hcf hok_t_spec hm2 => ?_⟩
      let memSt2 : FullState :=
        { core :=
            { memSt1.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', unassigned := unas', unflushed := unfl',
              wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
              confl_type := ctype', confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
              oom := oom' }
          scratch := { memSt1.scratch with
            search_ticks := ticks', wsort := wsort', phases := phases' } }
      have hag1 : AgreesExcept fastPropCoreMask s.core memSt1.core :=
        hag.update fun k => { k with propagated := memSt1.core.propagated }
      have hag2 : AgreesExcept fastPropCoreMask s.core memSt2.core :=
        hag1.update fun k => { k with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', unassigned := unas', unflushed := unfl',
          wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
          confl_type := ctype', confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
          oom := oom' }
      have htr12 : FullTrailExt s.core memSt2.core :=
        fastTrailExt_trans (fastTrailExt_congr htr (k2 := memSt1.core) rfl rfl rfl) htr2
      have hperm12 : FullArenaPermEq s.core memSt2.core := fastArenaPerm_trans hperm hperm2
      have hsc2 : memSt2.scratch = { s.scratch with
          search_ticks := memSt2.scratch.search_ticks, wsort := memSt2.scratch.wsort,
          phases := memSt2.scratch.phases } := by dsimp [memSt2, memSt1]; rw [hsc]
      have hfl2_lt : (fuel_v - 1#64).toNat < s.core.fuel.toNat := by omega
      fc_hsteps
      · -- `ok = true`: continue loop
        have hok_t : ok = true := by assumption
        exact ih (fuel_v - 1#64).toNat (prop_v + 1#64, fuel_v - 1#64, ()) m2 (by omega)
          ⟨memSt2, rfl, hlen2, hw2, hmfuel, hpr1.symm, hag2, htr12, hperm12, by omega, hsc2,
            fun _ => (hok_t_spec hok_t).1, (hok_t_spec hok_t).2.trans hct_pres,
            fun heq => by omega, fun hpe => absurd hpe hne_end, hm2⟩
      · -- `ok = false` and `oom ≠ 0`: write `h->fuel = fuel - 1` & return `2ULL`
        have hok_f : ok = false := by assumption
        let finSt2 : FullState := { memSt2 with core := { memSt2.core with fuel := fuel_v - 1#64 } }
        exact hret_st 2#64 finSt2 m
          ⟨{ hlen2.core_ok with vals_len := hlen2.core_ok.vals_len }, hlen2.scratch_ok⟩
          (hw2.with_fuel_prop _ _)
          (hag2.update fun k => { k with fuel := fuel_v - 1#64 })
          (fastTrailExt_congr htr12 rfl rfl rfl) hperm12 (by dsimp [finSt2]; omega) hsc2
          (Or.inr (Or.inr rfl)) (by simp) (by simp) (fun _ => Or.inl hc)
          (fun hpe => absurd hpe hne_end) hm
      · -- `ok = false` and `oom == 0`: write `h->fuel = fuel - 1` & return `1ULL`
        have hok_f : ok = false := by assumption
        have hoom2_0 : oom' = 0#64 := by assumption
        have ⟨hcf_ok, hcf_ign⟩ := (hcf hok_f).resolve_left (fun h => h hoom2_0)
        let finSt2 : FullState := { memSt2 with core := { memSt2.core with fuel := fuel_v - 1#64 } }
        exact hret_st 1#64 finSt2 m
          ⟨{ hlen2.core_ok with vals_len := hlen2.core_ok.vals_len }, hlen2.scratch_ok⟩
          (hw2.with_fuel_prop _ _)
          (hag2.update fun k => { k with fuel := fuel_v - 1#64 })
          (fastTrailExt_congr htr12 rfl rfl rfl) hperm12 (by dsimp [finSt2]; omega) hsc2
          (Or.inr (Or.inl rfl)) (by simp)
          (fun _ => ⟨by dsimp [finSt2]; exact hfl2_lt, hoom2_0,
            by simpa only [FullConflictOkW, fullArenaClauseRefs, fullArenaClauseGarb,
                 fullArenaClauseLits, fullArenaClauseRefsCore, fullArenaClauseGarbCore,
                 fullArenaClauseLitsCore, fullArenaClauseSizeCore, fullArenaHdrCore,
                 finSt2] using hcf_ok,
            hcf_ign⟩)
          (by simp) (fun hpe => absurd hpe hne_end) hm
    · -- Loop exit `!(prop < trail_end)`: store `propagated`, `fuel`, return `0ULL`
      have hpr_eq : prop_v.toNat = memSt.core.trail_end := by c0_bound
      let finSt : FullState :=
        { memSt with core := { memSt.core with propagated := prop_v.toNat, fuel := fuel_v } }
      exact hret_st 0#64 finSt m
        ⟨{ hcl with propagated_le := by dsimp [finSt]; omega }, hml_l.scratch_ok⟩
        (hml_w.with_fuel_prop fuel_v prop_v.toNat)
        (hag.update fun k => { k with propagated := prop_v.toNat, fuel := fuel_v })
        (fastTrailExt_congr htr rfl rfl rfl) hperm hfuel_le hsc (Or.inl rfl)
        (fun _ => ⟨by dsimp [finSt]; exact hpr_eq, hct_pres, hoom_pres, fun hlt => by
          by_cases hf : fuel_v.toNat = s.core.fuel.toNat
          · have hsame_st := hsame hf
            have : finSt = s := by
              rw [← hsame_st]; dsimp [finSt]; rw [← hmprop]
            subst this; dsimp [finSt] at hlt; omega
          · dsimp [finSt]; omega⟩)
        (by simp) (by simp)
        (fun hpe => by
          obtain ⟨hm_s, hf_s⟩ := hnoop hpe
          refine ⟨rfl, ?_⟩
          dsimp [finSt]; rw [← hmprop, hm_s, hf_s])
        hm
  · intro L hL; fc_hsteps
    have hpr_lt64 : s.core.propagated < 2 ^ 64 := by
      have := hlen0.core_ok.propagated_le; have := hlen0.core_ok.trail_end_le
      have := hlen0.core_ok.cur_vars_le; omega
    exact hL s.core.fuel.toNat (BitVec.ofNat 64 s.core.propagated, s.core.fuel, ()) m
      ⟨s, rfl, hlen0, hw0, rfl, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpr_lt64],
       .refl _ _, ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl⟩,
       ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, .refl _⟩⟩, Nat.le_refl _, rfl, fun h => h, rfl,
       fun _ => by cases s with | mk sc ssc => cases sc; rfl, fun _ => ⟨rfl, rfl⟩, hm⟩

theorem full_propagate_wp (Γ : Env)
    (hPropIgn : ∀ args m Q X, fullPropagateIgnoreSpec args m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, fullPropagateSpec args m Q X →
      Func.wp Γ full_propagate_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm, hQ⟩
  unfold Func.wp full_propagate_body
  fc_hsteps
  c0_call hPropIgn
  refine ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm,
    fun r vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' hlen' hw' htr' hperm' hfl' hr hr0
      hr1 hr2 hnoop hm' => ?_⟩
  fc_hsteps
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' hlen' hw' htr' hperm'
    hfl' hr
    (fun h0 => let ⟨hp, _, ho, hf⟩ := hr0 h0; ⟨hp, ho, hf⟩)
    (fun h1 => let ⟨hf, ho, hca, _⟩ := hr1 h1; ⟨hf, ho, hca⟩) hr2 hnoop hm'

end LeanQbe.T.Examples.Kissat.FastCore
