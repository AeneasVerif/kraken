module

public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas1
import LeanQbe.T.Logic.ControlComb
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Variable & Dense `kitten` Cone Sweeping `Func.wp` Proofs (`Part 5`)

Proves the parametric `(Γ : Env)` `Func.wp` contracts for the `2` top-level `kitten`
cone-sweeping functions in `FullDefSweep`:
1. `full_sweep_var_wp`
2. `full_sweep_dense_wp`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullDefSweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullArenaTactics FullSweepFwdHelpers FullSweepVarHelpers
open scoped FullArenaTactics FullCongTactics FullDefSweepTactics

local macro "ds_steps" : tactic =>
  `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _)
      (repeat ds_strip)
      c0_hsteps!))

/-! ## 1. Semantic Helpers for `kitten` Assumption Solving -/

private theorem nat_xor1_eq_litNeg (l : Nat) : l ^^^ 1 = litNeg l := by
  simp [litNeg]

private theorem bv64_add1_lt {x : BitVec 64} (h : x.toNat < 2 ^ 63) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x.toNat + 1 < 2 ^ 64)]

private theorem cone_stk_lt {F_cur : List (List Nat)} {s : FullState}
    {cls : List (Nat × List Nat)} {nv nc : Nat} (h : fullSweepKittenConeOk F_cur s cls nv nc) :
    ∀ i < nv, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars := h.2.2.2.2.2.1

private theorem cone_cls {F_cur : List (List Nat)} {s : FullState}
    {cls : List (Nat × List Nat)} {nv nc : Nat} (h : fullSweepKittenConeOk F_cur s cls nv nc) :
    ∀ c ∈ cls, (∀ l ∈ c.2, l < 2 * nv) ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause (c.2.map (fullSweepGlobalLit s))) :=
  h.2.2.2.2.2.2

private theorem kitten_unsat_of_solve0 {F_cur : List (List Nat)} {s : FullState}
    {cls : List (Nat × List Nat)} {scr : List (BitVec 32)}
    (hcl : ∀ cl ∈ cls, (cnfOfClauses F_cur).EntailsClause
      (cnfClause (cl.2.map (fullSweepGlobalLit s))))
    (h0 : (scr[256 + 18]?.getD 0#32).toNat = 0)
    (hu : (cnfOfClauses (cls.map Prod.snd ++ kittenAssumpClauses scr)).Unsat) :
    (cnfOfClauses F_cur).Unsat := by
  have hass : kittenAssumpClauses scr = [] := by simp [kittenAssumpClauses, h0]
  rw [hass, List.append_nil, CNF.unsat_iff_not_sat] at hu
  rw [CNF.unsat_iff_not_sat]; intro α hα
  apply hu (fun i => α (s.scratch.work_stk1[i]?.getD 0#32).toNat)
  rw [cnf_sat_cnfOfClauses_iff]; intro cl hcl_m
  rw [List.mem_map] at hcl_m; obtain ⟨p, hp, rfl⟩ := hcl_m
  have hent := hcl p hp
  rw [CNF.entails_clause_def] at hent
  have hsat := hent α hα
  rw [fullSweepGlobalLit_eq_coneLift'] at hsat
  exact (coneLift_clause_sat_iff (α := α) (cone_v := s.scratch.work_stk1)).mpr
    (by simpa [List.map_map, Function.comp_def, fullSweepGlobalLit_eq_coneLift'] using hsat)

private theorem kitten_assump1_eq {scr : List (BitVec 32)} {a0 : BitVec 32}
    (h1 : scr[256 + 18]? = some 1#32) (ha0 : scr[256 + 1184]? = some a0) :
    kittenAssumpClauses scr = [[a0.toNat]] := by simp [kittenAssumpClauses, h1, ha0]

private theorem kitten_assump2_eq {scr : List (BitVec 32)} {a0 a1 : BitVec 32}
    (h2 : scr[256 + 18]? = some 2#32) (ha0 : scr[256 + 1184]? = some a0)
    (ha1 : scr[256 + 1185]? = some a1) :
    kittenAssumpClauses scr = [[a0.toNat], [a1.toNat]] := by
  have hr : List.range 2 = [0, 1] := rfl
  have h2n : (scr[256 + 18]?.getD 0#32).toNat = 2 := by simp [h2]
  simp [kittenAssumpClauses, h2n, hr, ha0, ha1]

private theorem kitten_unsat_entails_unit {F_cur : List (List Nat)} {s : FullState}
    {cls : List (Nat × List Nat)} {scr : List (BitVec 32)} {root_v test : BitVec 32}
    (hcl : ∀ cl ∈ cls, (cnfOfClauses F_cur).EntailsClause
      (cnfClause (cl.2.map (fullSweepGlobalLit s))))
    (hroot : (s.scratch.work_stk1[0]?.getD 0#32).toNat = root_v.toNat)
    (hroot_lt : root_v.toNat < 2 ^ 31) (htest : test = 0#32 ∨ test = 1#32)
    (h18 : scr[256 + 18]? = some 1#32) (ha0 : scr[256 + 1184]? = some test)
    (hu : (cnfOfClauses (cls.map Prod.snd ++ kittenAssumpClauses scr)).Unsat) :
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [((root_v <<< (1 : Nat)) ||| (1#32 - test)).toNat]) := by
  rw [kitten_assump1_eq h18 ha0, CNF.unsat_iff_not_sat] at hu
  rw [CNF.entails_clause_def]; intro α hα
  exact Classical.byContradiction fun hnot => by
    apply hu (fun i => α (s.scratch.work_stk1[i]?.getD 0#32).toNat)
    rw [cnf_sat_cnfOfClauses_iff]; intro cl hcl_m
    rw [List.mem_append, List.mem_map, List.mem_singleton] at hcl_m
    rcases hcl_m with ⟨p, hp, rfl⟩ | rfl
    · have hsat := (CNF.entails_clause_def.mp (hcl p hp)) α hα
      exact (coneLift_clause_sat_iff (α := α) (cone_v := s.scratch.work_stk1)).mpr
        (by simpa [List.map_map, Function.comp_def, fullSweepGlobalLit_eq_coneLift'] using hsat)
    · have h1sub : (1#32 - test).toNat < 2 := by rcases htest with rfl | rfl <;> decide
      have hlit : ((root_v <<< (1 : Nat)) ||| (1#32 - test)).toNat =
          fullSweepGlobalLit s test.toNat ^^^ 1 := by
        rw [FullSweepVarHelpers.bv32_shl1_or_pol root_v (1#32 - test) hroot_lt h1sub,
          bv32_1_sub_toNat test htest]
        unfold fullSweepGlobalLit
        rcases htest with rfl | rfl
        · simp [hroot, ← (nat_2x_xor1 root_v.toNat).1]
        · simp [hroot, (nat_2x_xor1 root_v.toNat).2]
      rw [hlit, fullSweepGlobalLit_eq_coneLift', nat_xor1_eq_litNeg] at hnot
      rw [sat_cnfClause_singleton] at hnot ⊢
      have hd := litVar_litNeg (FullSweepFwdSpecs.coneLift s.scratch.work_stk1 test.toNat)
      have hs := litSign_litNeg (FullSweepFwdSpecs.coneLift s.scratch.work_stk1 test.toNat)
      rw [hd, hs, Bool.not_not] at hnot
      have hsat_gl :
          (cnfClause [FullSweepFwdSpecs.coneLift s.scratch.work_stk1 test.toNat]).Sat α := by
        rw [sat_cnfClause_singleton]
        generalize FullSweepFwdSpecs.coneLift s.scratch.work_stk1 test.toNat = l at hnot ⊢
        cases hb : α (litVar l) <;> cases hc : litSign l <;> simp [hb, hc] at hnot ⊢
      exact (sat_cnfClause_singleton _ _).mp (coneLift_sat_iff.mpr hsat_gl)

private theorem kitten_unsat_entails_bin1 {F_cur : List (List Nat)} {s : FullState}
    {cls : List (Nat × List Nat)} {scr : List (BitVec 32)} {root_v ov j pol : BitVec 32}
    (hcl : ∀ cl ∈ cls, (cnfOfClauses F_cur).EntailsClause
      (cnfClause (cl.2.map (fullSweepGlobalLit s))))
    (hroot : (s.scratch.work_stk1[0]?.getD 0#32).toNat = root_v.toNat)
    (hov : (s.scratch.work_stk1[j.toNat]?.getD 0#32).toNat = ov.toNat)
    (hj_lt : j.toNat < 2 ^ 31) (hpol : pol = 0#32 ∨ pol = 1#32)
    (hroot_lt : root_v.toNat < 2 ^ 31) (hov_lt : ov.toNat < 2 ^ 31)
    (h18 : scr[256 + 18]? = some 2#32) (ha0 : scr[256 + 1184]? = some 0#32)
    (ha1 : scr[256 + 1185]? = some ((j <<< (1 : Nat)) ||| (1#32 ^^^ pol)))
    (hu : (cnfOfClauses (cls.map Prod.snd ++ kittenAssumpClauses scr)).Unsat) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause
      [((root_v <<< (1 : Nat)) ^^^ 1#32).toNat, ((ov <<< (1 : Nat)) ||| pol).toNat]) := by
  rw [kitten_assump2_eq h18 ha0 ha1, CNF.unsat_iff_not_sat] at hu
  rw [CNF.entails_clause_def]; intro α hα; exact Classical.byContradiction fun hnot => by
    have hnot1 : ¬ (cnfClause [((root_v <<< (1 : Nat)) ^^^ 1#32).toNat]).Sat α := fun h1 =>
      hnot ((clause_sat_cnfClause_iff _ _).mpr ⟨_, List.mem_cons_self ..,
        (sat_cnfClause_singleton _ _).mp h1⟩)
    have hnot2 : ¬ (cnfClause [((ov <<< (1 : Nat)) ||| pol).toNat]).Sat α := fun h2 =>
      hnot ((clause_sat_cnfClause_iff _ _).mpr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
        (sat_cnfClause_singleton _ _).mp h2⟩)
    apply hu (fun i => α (s.scratch.work_stk1[i]?.getD 0#32).toNat)
    rw [cnf_sat_cnfOfClauses_iff]; intro cl hcl_m
    rw [List.mem_append, List.mem_map, List.mem_cons, List.mem_singleton] at hcl_m
    rcases hcl_m with ⟨p, hp, rfl⟩ | rfl | rfl
    · have hsat := (CNF.entails_clause_def.mp (hcl p hp)) α hα
      exact (coneLift_clause_sat_iff (α := α) (cone_v := s.scratch.work_stk1)).mpr
        (by simpa [List.map_map, Function.comp_def, fullSweepGlobalLit_eq_coneLift'] using hsat)
    · have hl0 : ((root_v <<< (1 : Nat)) ^^^ 1#32).toNat = fullSweepGlobalLit s 0 ^^^ 1 := by
        rw [bv32_xor1_toNat, bv32_shl1_toNat root_v hroot_lt]
        unfold fullSweepGlobalLit; simp [hroot]
      rw [hl0, fullSweepGlobalLit_eq_coneLift', nat_xor1_eq_litNeg, sat_cnfClause_singleton,
        litVar_litNeg, litSign_litNeg, Bool.not_not] at hnot1
      refine coneLift_sat_iff.mpr ((sat_cnfClause_singleton _ _).mpr ?_)
      cases hb : α (litVar (FullSweepFwdSpecs.coneLift s.scratch.work_stk1 0)) <;>
        cases hc : litSign (FullSweepFwdSpecs.coneLift s.scratch.work_stk1 0) <;>
        simp [hb, hc] at hnot1 ⊢
    · have hxp_lt : (1#32 ^^^ pol).toNat < 2 := by rcases hpol with rfl | rfl <;> decide
      have hp_lt : pol.toNat < 2 := by rcases hpol with rfl | rfl <;> decide
      have ha1_eq : ((j <<< (1 : Nat)) ||| (1#32 ^^^ pol)).toNat =
          2 * j.toNat + (1#32 ^^^ pol).toNat :=
        FullSweepVarHelpers.bv32_shl1_or_pol j (1#32 ^^^ pol) hj_lt hxp_lt
      have hl1 : ((ov <<< (1 : Nat)) ||| pol).toNat =
          fullSweepGlobalLit s (((j <<< (1 : Nat)) ||| (1#32 ^^^ pol)).toNat) ^^^ 1 := by
        rw [FullSweepVarHelpers.bv32_shl1_or_pol ov pol hov_lt hp_lt]
        unfold fullSweepGlobalLit; rw [ha1_eq]
        rcases hpol with rfl | rfl
        · have hxp : (1#32 ^^^ 0#32).toNat = 1 := rfl
          rw [hxp]; simp [show (2 * j.toNat + 1) / 2 = j.toNat by omega,
            show (2 * j.toNat + 1) % 2 = 1 by omega, hov, (nat_2x_xor1 ov.toNat).2]
        · have hxp : (1#32 ^^^ 1#32).toNat = 0 := rfl
          rw [hxp]; simp [hov, (nat_2x_xor1 ov.toNat).1]
      rw [hl1, fullSweepGlobalLit_eq_coneLift', nat_xor1_eq_litNeg, sat_cnfClause_singleton,
        litVar_litNeg, litSign_litNeg, Bool.not_not] at hnot2
      refine coneLift_sat_iff.mpr ((sat_cnfClause_singleton _ _).mpr ?_)
      generalize FullSweepFwdSpecs.coneLift s.scratch.work_stk1
        (((j <<< (1 : Nat)) ||| (1#32 ^^^ pol)).toNat) = l at hnot2 ⊢
      cases hb : α (litVar l) <;> cases hc : litSign l <;> simp [hb, hc] at hnot2 ⊢

private theorem kitten_unsat_entails_bin2 {F_cur : List (List Nat)} {s : FullState}
    {cls : List (Nat × List Nat)} {scr : List (BitVec 32)} {root_v ov j pol : BitVec 32}
    (hcl : ∀ cl ∈ cls, (cnfOfClauses F_cur).EntailsClause
      (cnfClause (cl.2.map (fullSweepGlobalLit s))))
    (hroot : (s.scratch.work_stk1[0]?.getD 0#32).toNat = root_v.toNat)
    (hov : (s.scratch.work_stk1[j.toNat]?.getD 0#32).toNat = ov.toNat)
    (hj_lt : j.toNat < 2 ^ 31) (hpol : pol = 0#32 ∨ pol = 1#32)
    (hroot_lt : root_v.toNat < 2 ^ 31) (hov_lt : ov.toNat < 2 ^ 31)
    (h18 : scr[256 + 18]? = some 2#32) (ha0 : scr[256 + 1184]? = some 1#32)
    (ha1 : scr[256 + 1185]? = some ((j <<< (1 : Nat)) ||| pol))
    (hu : (cnfOfClauses (cls.map Prod.snd ++ kittenAssumpClauses scr)).Unsat) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause
      [(root_v <<< (1 : Nat)).toNat, (((ov <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat]) := by
  rw [kitten_assump2_eq h18 ha0 ha1, CNF.unsat_iff_not_sat] at hu
  rw [CNF.entails_clause_def]; intro α hα; exact Classical.byContradiction fun hnot => by
    have hnot1 : ¬ (cnfClause [(root_v <<< (1 : Nat)).toNat]).Sat α := fun h1 =>
      hnot ((clause_sat_cnfClause_iff _ _).mpr ⟨_, List.mem_cons_self ..,
        (sat_cnfClause_singleton _ _).mp h1⟩)
    have hnot2 : ¬ (cnfClause [(((ov <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat]).Sat α := fun h2 =>
      hnot ((clause_sat_cnfClause_iff _ _).mpr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
        (sat_cnfClause_singleton _ _).mp h2⟩)
    apply hu (fun i => α (s.scratch.work_stk1[i]?.getD 0#32).toNat)
    rw [cnf_sat_cnfOfClauses_iff]; intro cl hcl_m
    rw [List.mem_append, List.mem_map, List.mem_cons, List.mem_singleton] at hcl_m
    rcases hcl_m with ⟨p, hp, rfl⟩ | rfl | rfl
    · have hsat := (CNF.entails_clause_def.mp (hcl p hp)) α hα
      exact (coneLift_clause_sat_iff (α := α) (cone_v := s.scratch.work_stk1)).mpr
        (by simpa [List.map_map, Function.comp_def, fullSweepGlobalLit_eq_coneLift'] using hsat)
    · have hl0 : (root_v <<< (1 : Nat)).toNat = fullSweepGlobalLit s 1 ^^^ 1 := by
        rw [bv32_shl1_toNat root_v hroot_lt]
        unfold fullSweepGlobalLit
        simp [hroot, (nat_2x_xor1 root_v.toNat).2]
      rw [hl0, fullSweepGlobalLit_eq_coneLift', nat_xor1_eq_litNeg, sat_cnfClause_singleton,
        litVar_litNeg, litSign_litNeg, Bool.not_not] at hnot1
      refine coneLift_sat_iff.mpr ((sat_cnfClause_singleton _ _).mpr ?_)
      cases hb : α (litVar (FullSweepFwdSpecs.coneLift s.scratch.work_stk1 1)) <;>
        cases hc : litSign (FullSweepFwdSpecs.coneLift s.scratch.work_stk1 1) <;>
        simp [hb, hc] at hnot1 ⊢
    · have hp_lt : pol.toNat < 2 := by rcases hpol with rfl | rfl <;> decide
      have ha1_eq : ((j <<< (1 : Nat)) ||| pol).toNat = 2 * j.toNat + pol.toNat :=
        FullSweepVarHelpers.bv32_shl1_or_pol j pol hj_lt hp_lt
      have hl1 : (((ov <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat =
          fullSweepGlobalLit s ((j <<< (1 : Nat)) ||| pol).toNat ^^^ 1 := by
        rw [bv32_xor1_toNat, FullSweepVarHelpers.bv32_shl1_or_pol ov pol hov_lt hp_lt]
        unfold fullSweepGlobalLit; rw [ha1_eq]
        rcases hpol with rfl | rfl
        · simp [show (0#32).toNat = 0 from rfl, hov]
        · simp [show (1#32).toNat = 1 from rfl, show (2 * j.toNat + 1) / 2 = j.toNat by omega,
            show (2 * j.toNat + 1) % 2 = 1 by omega, hov]
      rw [hl1, fullSweepGlobalLit_eq_coneLift', nat_xor1_eq_litNeg, sat_cnfClause_singleton,
        litVar_litNeg, litSign_litNeg, Bool.not_not] at hnot2
      refine coneLift_sat_iff.mpr ((sat_cnfClause_singleton _ _).mpr ?_)
      generalize FullSweepFwdSpecs.coneLift s.scratch.work_stk1
        (((j <<< (1 : Nat)) ||| pol).toNat) = l at hnot2 ⊢
      cases hb : α (litVar l) <;> cases hc : litSign l <;> simp [hb, hc] at hnot2 ⊢

/-! ## 2. `full_sweep_var_wp` (`FullDefSweep` #8) -/

private theorem sweep_tmk_clear_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {sX : FullState}
    {R : Mem 64 → Prop} {nv : BitVec 32} {ws1' tmk' : List (BitVec 32)}
    {pWorkStk1 pTarjanMark : BitVec 64} {mX : Mem 64} {cont : Expr Val Cont rs}
    (hpws : pWorkStk1 = c.pWorkStk1) (hptmk : pTarjanMark = c.pTarjanMark)
    (hnv_mx : nv.toNat ≤ 2 * c.max_vars) (hinvX : FullDenseInvW c F0 F_cur sX)
    (hwsX : sX.scratch.work_stk1 = ws1') (htmkX : sX.scratch.tarjan_mark = tmk')
    (hconeX : ∀ i < nv.toNat, (sX.scratch.work_stk1[i]?.getD 0#32).toNat < sX.core.cur_vars)
    (htmk1' : ∀ u < sX.core.cur_vars, tmk'[u]?.getD 0#32 ≠ 0#32 →
      ∃ k < nv.toNat, (ws1'[k]?.getD 0#32).toNat = u)
    (hmX : (FullMem c sX ⋆ R) mX)
    (hcont : ∀ (tmk_c : List (BitVec 32)) m_end,
      tmk_c.length = 2 * c.max_vars →
      TmkZero { sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } →
      (FullMem c { sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } ⋆ R) m_end →
      wp Γ Q X cont m_end) :
    wp Γ Q X
      (Expr.group (sig := [[i32]])
        (fun Js =>
          Blocks.cons
            (fun (p : Tup Val [i32]) =>
              Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i32) (Arg.var p.fst, Arg.var nv, ()))
                fun p_1 =>
                Expr.jnz (Arg.var p_1.fst)
                  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.fst, ()))
                    fun p_2 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_2.fst, Arg.imm 4, ()))
                      fun p_3 =>
                      Expr.let_
                        (Op.mk (OpCode.add i64) (Arg.var pWorkStk1, Arg.var p_3.fst, ()))
                        fun p_4 =>
                        Expr.load i32 (Arg.var p_4.fst) fun ld =>
                          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld, ()))
                            fun p_5 =>
                            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_5.fst, Arg.imm 4, ()))
                              fun p_6 =>
                              Expr.let_
                                (Op.mk (OpCode.add i64)
                                  (Arg.var pTarjanMark, Arg.var p_6.fst, ()))
                                fun p_7 =>
                                Expr.store (t := i32) (Arg.imm 0) (Arg.var p_7.fst)
                                  (Expr.let_
                                    (Op.mk (OpCode.add i32) (Arg.var p.fst, Arg.imm 1, ()))
                                    fun p => Expr.jump Js.fst (Arg.var p.fst, ())))
                  cont)
            Blocks.nil)
        (fun Js => Expr.jump Js.fst (Arg.imm 0, ())))
      mX := by
  subst hpws hptmk
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hws_len := hinvX.1.scratch_ok.work_stk1_len
  have hcvX_le := hinvX.1.core_ok.cur_vars_le
  have htmkX_sym : tmk' = sX.scratch.tarjan_mark := htmkX.symm
  refine wp_loop_inv (ts := [i32])
    (fun (i, ()) mi => i.toNat ≤ nv.toNat ∧ ∃ tmk_c : List (BitVec 32),
      tmk_c.length = 2 * c.max_vars ∧
      (∀ u < sX.core.cur_vars, tmk_c[u]?.getD 0#32 ≠ 0#32 →
        ∃ k, i.toNat ≤ k ∧ k < nv.toNat ∧ (ws1'[k]?.getD 0#32).toNat = u) ∧
      (FullMem c { sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } ⋆ R) mi)
    (fun (i, ()) _ => nv.toNat - i.toNat)
    (fun _ hLc => by
      ds_steps
      exact hLc (0#32, ()) mX ⟨Nat.zero_le _, tmk',
        htmkX ▸ hinvX.1.scratch_ok.tarjan_mark_len,
        fun u hu hne => let ⟨k, hk, hwk⟩ := htmk1' u hu hne; ⟨k, Nat.zero_le _, hk, hwk⟩,
        htmkX_sym ▸ hmX⟩)
    (fun _ (i, ()) mi ⟨hi_le, tmk_c, ht_len, ht_inv, hmi⟩ hLc => by
      ds_split
      · have hi_lt : i.toNat < nv.toNat := by bv_omega
        have hv_lt : (ws1'[i.toNat]'(by rw [← hwsX, hws_len]; omega)).toNat <
            2 * c.max_vars := by
          have := hconeX i.toNat hi_lt
          rw [hwsX, List.getElem?_eq_getElem (by rw [← hwsX, hws_len]; omega),
            Option.getD_some] at this
          omega
        have hi_ws : (BitVec.setWidth 64 i).toNat <
            ({ sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } :
              FullState).scratch.work_stk1.length := by
          change (BitVec.setWidth 64 i).toNat < sX.scratch.work_stk1.length
          rw [hws_len, bv_c0_zext32_64]; omega
        have hwsX_eq : ({ sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } :
            FullState).scratch.work_stk1 = ws1' := hwsX
        have hgv_tmk : (BitVec.setWidth 64 (({ sX with scratch :=
            { sX.scratch with tarjan_mark := tmk_c } } :
            FullState).scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'hi_ws)).toNat <
            ({ sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } :
              FullState).scratch.tarjan_mark.length :=
          tmk_idx_lt hwsX_eq (by rw [← hwsX, hws_len]; omega) (by rw [ht_len]; exact hv_lt) hi_ws
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := dsSweep_bv32_add1_lt (by omega)
        ds_steps
        refine hLc (i + 1#32, ()) _ (by dsimp only; omega)
          ⟨by omega, _, List.length_set.trans ht_len, fun u hu hne => ?_, by assumption⟩
        have h64_i : (BitVec.setWidth 64 i).toNat = i.toNat := bv_c0_zext32_64 i
        have hcur1 : sX.scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'hi_ws =
            sX.scratch.work_stk1[i.toNat]'(by rw [hws_len]; omega) := Option.some.inj (by
          rw [← List.getElem?_eq_getElem hi_ws,
            ← List.getElem?_eq_getElem (by rw [hws_len]; omega), h64_i])
        have hcur2 : sX.scratch.work_stk1[i.toNat]'(by rw [hws_len]; omega) =
            ws1'[i.toNat]'(by rw [← hwsX, hws_len]; omega) := by cases hwsX; rfl
        have hcur_eq : ({ sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } :
            FullState).scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'hi_ws =
            ws1'[i.toNat]'(by rw [← hwsX, hws_len]; omega) := hcur1.trans hcur2
        rw [hcur_eq, bv_c0_zext32_64] at hne
        by_cases huv : u = (ws1'[i.toNat]'(by rw [← hwsX, hws_len]; omega)).toNat
        · rw [huv] at hne
          rw [List.getElem?_set_self (by rw [ht_len]; exact hv_lt)] at hne
          exact absurd rfl hne
        · rw [List.getElem?_set_ne (Ne.symm huv)] at hne
          obtain ⟨k, hk1, hk2, hwk⟩ := ht_inv u hu hne
          have hkne : k ≠ i.toNat := by
            rintro rfl
            rw [List.getElem?_eq_getElem (by rw [← hwsX, hws_len]; omega), Option.getD_some]
              at hwk
            exact huv hwk.symm
          exact ⟨k, by omega, hk2, hwk⟩
      · have hge : ¬ i.toNat < nv.toNat := by bv_omega
        refine hcont tmk_c mi ht_len (fun u hu => ?_) hmi
        exact Classical.byContradiction fun hne => by
          obtain ⟨k, hk1, hk2, _⟩ := ht_inv u hu hne; omega)

private theorem sweep_kitten_add_bins_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    (haddB : EnvSpec Γ "full_add_bin" FullSweepVarSpecs.fullAddBinSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {sB : FullState}
    {R : Mem 64 → Prop} {nv nc : Nat} {cls : List (Nat × List Nat)}
    {ws1' tmk' : List (BitVec 32)} {hdrPtr : BitVec 64} {rl1 rl ol : BitVec 32} {mB : Mem 64}
    {iArg : Val i32} {Jret : Cont []} {Jnext : Cont [i32]}
    (hhdr : hdrPtr = c.hdr) (hinvB : FullDenseInvW c F0 F_cur sB)
    (hwsB : sB.scratch.work_stk1 = ws1') (htmkB : sB.scratch.tarjan_mark = tmk')
    (hconeB : fullSweepKittenConeOk F_cur sB cls nv nc)
    (hent1 : (cnfOfClauses F_cur).EntailsClause (cnfClause [rl1.toNat, ol.toNat]))
    (hent2 : (cnfOfClauses F_cur).EntailsClause (cnfClause [rl.toNat, (ol ^^^ 1#32).toNat]))
    (hmB : (FullMem c sB ⋆ R) mB)
    (hJret : ∀ sX mX, FullDenseInvW c F0 F_cur sX → sX.core.cur_vars = sB.core.cur_vars →
      sX.core.fuel.toNat ≤ sB.core.fuel.toNat → sX.scratch.work_stk1 = ws1' →
      sX.scratch.tarjan_mark = tmk' → fullSweepKittenConeOk F_cur sX cls nv nc →
      F0.Unsat → (FullMem c sX ⋆ R) mX → Jret () mX)
    (hJnext : ∀ sX mX, FullDenseInvW c F0 F_cur sX → sX.core.cur_vars = sB.core.cur_vars →
      sX.core.fuel.toNat ≤ sB.core.fuel.toNat → sX.scratch.work_stk1 = ws1' →
      sX.scratch.tarjan_mark = tmk' → sX.scratch.scratch_buf = sB.scratch.scratch_buf →
      fullSweepKittenConeOk F_cur sX cls nv nc →
      (FullMem c sX ⋆ R) mX → Jnext (iArg, ()) mX) :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i32]) (bs := [i64]) "full_add_bin"
        (Arg.var hdrPtr, Arg.var rl1, Arg.var ol, ())
        fun (p : Tup Val [i64]) =>
        Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i64) (Arg.var p.fst, Arg.imm 20, ())) fun p =>
          Expr.jnz (Arg.var p.fst) (Expr.jump Jret ())
            (Expr.let_ (Op.mk (OpCode.xor i32) (Arg.var ol, Arg.imm 1, ())) fun p =>
              Expr.call (as := [i64, i32, i32]) (bs := [i64]) "full_add_bin"
                (Arg.var hdrPtr, Arg.var rl, Arg.var p.fst, ())
                fun (p : Tup Val [i64]) =>
                Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i64) (Arg.var p.fst, Arg.imm 20, ()))
                  fun p =>
                  Expr.jnz (Arg.var p.fst) (Expr.jump Jret ())
                    (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var hdrPtr, Arg.imm 1080, ()))
                      fun p =>
                      Expr.load i64 (Arg.var p.fst) fun ld =>
                        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var ld, Arg.imm 1, ())) fun p =>
                          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var hdrPtr, Arg.imm 1080, ()))
                            fun p_1 => Expr.store (t := i64) (Arg.var p.fst) (Arg.var p_1.fst)
                              (Expr.jump Jnext (Arg.var iArg, ())))))
      mB := by
  subst hhdr
  c0_call haddB
  refine ⟨c, F0, F_cur, sB, R, rfl, hinvB.1, hinvB.2.1, hinvB.2.2.2.2.2.1,
    fun _ _ => hent1, hmB, ?_⟩
  intro rb1 vals1 flags1 lvl1 rsns1 trl1 tp1 te1 unass1 unfl1 wvec1 wstk1 wlen1 wu1 nb1 oom1
    inc1 phases1 wsort1 mC _ hlenC hwC hrb1_dom hrb1_uns hrb1_oom hmC
  obtain ⟨sC, hsC⟩ : ∃ sC : FullState, sC =
    { sB with
      core := { sB.core with
        vals := vals1, flags := flags1, lvl := lvl1, rsns := rsns1, trl := trl1,
        trail_pos := tp1, trail_end := te1, unassigned := unass1, unflushed := unfl1,
        wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wu1, num_binary := nb1,
        oom := oom1, inconsistent := inc1 }
      scratch := { sB.scratch with phases := phases1, wsort := wsort1 } } := ⟨_, rfl⟩
  have hinvC := fullDenseInvW_after_addBin hinvB sC hsC (hsC ▸ hlenC) (hsC ▸ hwC)
  have hconeC : fullSweepKittenConeOk F_cur sC cls nv nc :=
    hsC ▸ hconeB
  have hwsC : sC.scratch.work_stk1 = ws1' := by rw [hsC]; exact hwsB
  have htmkC : sC.scratch.tarjan_mark = tmk' := by rw [hsC]; exact htmkB
  have hcvC : sC.core.cur_vars = sB.core.cur_vars := by rw [hsC]
  have hfuelC : sC.core.fuel.toNat ≤ sB.core.fuel.toNat := by rw [hsC]; exact Nat.le_refl _
  have hmC' : (FullMem c sC ⋆ R) mC := hsC ▸ hmC
  ds_split
  · have hrb1_20 : rb1 = 20#64 := by bv_omega
    ds_steps
    exact hJret sC mC hinvC hcvC hfuelC hwsC htmkC hconeC (hrb1_uns hrb1_20).1 hmC'
  · c0_call haddB
    refine ⟨c, F0, F_cur, sC, R, rfl, hinvC.1, hinvC.2.1, hinvC.2.2.2.2.2.1,
      fun _ _ => hent2, hmC', ?_⟩
    intro rb2 vals2 flags2 lvl2 rsns2 trl2 tp2 te2 unass2 unfl2 wvec2 wstk2 wlen2 wu2 nb2 oom2
      inc2 phases2 wsort2 mD _ hlenD hwD hrb2_dom hrb2_uns hrb2_oom hmD
    obtain ⟨sD, hsD⟩ : ∃ sD : FullState, sD =
      { sC with
        core := { sC.core with
          vals := vals2, flags := flags2, lvl := lvl2, rsns := rsns2, trl := trl2,
          trail_pos := tp2, trail_end := te2, unassigned := unass2, unflushed := unfl2,
          wvec := wvec2, wstk := wstk2, wlen := wlen2, wusable := wu2, num_binary := nb2,
          oom := oom2, inconsistent := inc2 }
        scratch := { sC.scratch with phases := phases2, wsort := wsort2 } } := ⟨_, rfl⟩
    have hinvD := fullDenseInvW_after_addBin hinvC sD hsD (hsD ▸ hlenD) (hsD ▸ hwD)
    have hconeD : fullSweepKittenConeOk F_cur sD cls nv nc := hsD ▸ hconeC
    have hwsD : sD.scratch.work_stk1 = ws1' := by rw [hsD]; exact hwsC
    have htmkD : sD.scratch.tarjan_mark = tmk' := by rw [hsD]; exact htmkC
    have hcvD : sD.core.cur_vars = sB.core.cur_vars := by rw [hsD]; exact hcvC
    have hfuelD : sD.core.fuel.toNat ≤ sB.core.fuel.toNat := by rw [hsD]; exact hfuelC
    have hmD' : (FullMem c sD ⋆ R) mD := hsD ▸ hmD
    ds_split
    · have hrb2_20 : rb2 = 20#64 := by bv_omega
      ds_steps
      exact hJret sD mD hinvD hcvD hfuelD hwsD htmkD hconeD (hrb2_uns hrb2_20).1 hmD'
    · ds_steps
      exact hJnext _ _ (fullDenseInvW_with_sweep_cnt hinvD (sD.scratch.sweep_cnt + 1#64))
        hcvD hfuelD hwsD htmkD (by rw [hsD, hsC]) hconeD (by assumption)

private structure ConeState
    (KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop)
    (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cv0 fuel0 : Nat)
    (cls' : List (Nat × List Nat)) (nv nc : Nat) (ws1' tmk' : List (BitVec 32))
    (R : Mem 64 → Prop) (sN : FullState) (mN : Mem 64) : Prop where
  inv : FullDenseInvW c F0 F_cur sN
  cv : sN.core.cur_vars = cv0
  fuel : sN.core.fuel.toNat ≤ fuel0
  cone : fullSweepKittenConeOk F_cur sN cls' nv nc
  ws : sN.scratch.work_stk1 = ws1'
  tmk : sN.scratch.tarjan_mark = tmk'
  kinv : KInv nv cls' false .solved sN.scratch.scratch_buf
  mem : (FullMem c sN ⋆ R) mN

private theorem ConeState.after_refine
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 fuel0 : Nat}
    {cls' : List (Nat × List Nat)} {nv nc : Nat} {ws1' tmk' : List (BitVec 32)}
    {R : Mem 64 → Prop} {sN : FullState} {mN m' : Mem 64} {sig' : List (BitVec 64)}
    (cs : ConeState KInv c F0 F_cur cv0 fuel0 cls' nv nc ws1' tmk' R sN mN)
    (hsig : sig'.length = c.max_vars)
    (hm' : (FullMem c { sN with scratch := { sN.scratch with sim_sig := sig' } } ⋆ R) m') :
    ConeState KInv c F0 F_cur cv0 fuel0 cls' nv nc ws1' tmk' R
      { sN with scratch := { sN.scratch with sim_sig := sig' } } m' :=
  ⟨fullDenseInvW_after_refine cs.inv hsig, cs.cv, cs.fuel, cs.cone, cs.ws, cs.tmk, cs.kinv, hm'⟩

private theorem ConeState.with_fuel_scr
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 fuel0 : Nat}
    {cls' : List (Nat × List Nat)} {nv nc : Nat} {ws1' tmk' : List (BitVec 32)}
    {R : Mem 64 → Prop} {sN : FullState} {mN m' : Mem 64}
    {fuel' : BitVec 64} {scr' : List (BitVec 32)}
    (cs : ConeState KInv c F0 F_cur cv0 fuel0 cls' nv nc ws1' tmk' R sN mN)
    (hsl : scr'.length = c.scratch_cap) (hfl : fuel'.toNat ≤ sN.core.fuel.toNat)
    (hK' : KInv nv cls' false .solved scr')
    (hm' : (FullMem c
      { sN with
        core := { sN.core with fuel := fuel' }
        scratch := { sN.scratch with scratch_buf := scr' } } ⋆ R) m') :
    ConeState KInv c F0 F_cur cv0 fuel0 cls' nv nc ws1' tmk' R
      { sN with
        core := { sN.core with fuel := fuel' }
        scratch := { sN.scratch with scratch_buf := scr' } } m' :=
  ⟨fullDenseInvW_with_fuel_scratch cs.inv
     { cs.inv.1.scratch_ok with scratch_buf_len := hsl } rfl rfl,
   cs.cv, Nat.le_trans hfl cs.fuel, cs.cone, cs.ws, cs.tmk, hK', hm'⟩

private theorem ConeState.with_scr
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 fuel0 : Nat}
    {cls' : List (Nat × List Nat)} {nv nc : Nat} {ws1' tmk' : List (BitVec 32)}
    {R : Mem 64 → Prop} {sN : FullState} {mN m' : Mem 64} {scr' : List (BitVec 32)}
    (cs : ConeState KInv c F0 F_cur cv0 fuel0 cls' nv nc ws1' tmk' R sN mN)
    (hsl : scr'.length = c.scratch_cap) (hK' : KInv nv cls' false .solved scr')
    (hm' : (FullMem c { sN with scratch := { sN.scratch with scratch_buf := scr' } } ⋆ R) m') :
    ConeState KInv c F0 F_cur cv0 fuel0 cls' nv nc ws1' tmk' R
      { sN with scratch := { sN.scratch with scratch_buf := scr' } } m' :=
  ⟨fullDenseInvW_with_fuel_scratch cs.inv
     { cs.inv.1.scratch_ok with scratch_buf_len := hsl } rfl rfl,
   cs.cv, cs.fuel, cs.cone, cs.ws, cs.tmk, hK', hm'⟩

private theorem ConeState.with_sweep_cnt
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 fuel0 : Nat}
    {cls' : List (Nat × List Nat)} {nv nc : Nat} {ws1' tmk' : List (BitVec 32)}
    {R : Mem 64 → Prop} {sN : FullState} {mN m' : Mem 64}
    (cs : ConeState KInv c F0 F_cur cv0 fuel0 cls' nv nc ws1' tmk' R sN mN)
    (sc' : BitVec 64)
    (hm' : (FullMem c { sN with scratch := { sN.scratch with sweep_cnt := sc' } } ⋆ R) m') :
    ConeState KInv c F0 F_cur cv0 fuel0 cls' nv nc ws1' tmk' R
      { sN with scratch := { sN.scratch with sweep_cnt := sc' } } m' :=
  ⟨fullDenseInvW_with_sweep_cnt cs.inv sc', cs.cv, cs.fuel, cs.cone, cs.ws, cs.tmk, cs.kinv, hm'⟩

private theorem kinv_assump1
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    (hLaws : KittenInvLaws KInv) {nv : Nat} {cls' : List (Nat × List Nat)} {ph : KittenPhase}
    {scr : List (BitVec 32)} {cap : Nat} {test : BitVec 32}
    (hK : KInv nv cls' false ph scr) (hsl : scr.length = cap) (hcap : 10240 ≤ cap)
    (htest : test = 0#32 ∨ test = 1#32) (hnv : 1 ≤ nv) :
    let scrU := (scr.set (256 + 18) 1#32).set (256 + 1184) test
    scrU[256 + 18]? = some 1#32 ∧ scrU[256 + 1184]? = some test ∧
      KInv nv cls' false .solved scrU := by
  intro scrU
  have h18 : scrU[256 + 18]? = some 1#32 := by
    dsimp only [scrU]
    rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by rw [hsl]; omega)]
  have h0 : scrU[256 + 1184]? = some test :=
    List.getElem?_set_self (by rw [List.length_set, hsl]; omega)
  refine ⟨h18, h0, hLaws.set_assumps hK (by simp [scrU]) (fun i hi18 hi84 _ => ?_)
    (by rw [h18]; decide) (fun i hi => ?_)⟩
  · simp [scrU, List.getElem?_set_ne (Ne.symm hi18), List.getElem?_set_ne (Ne.symm hi84)]
  · have hi1 : i < 1 := by rw [h18] at hi; simp at hi; omega
    have hi0 : i = 0 := by omega
    subst hi0; rw [h0]; simp; rcases htest with rfl | rfl <;> simp <;> omega

private theorem kinv_assump2_a
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    (hLaws : KittenInvLaws KInv) {nv : Nat} {cls' : List (Nat × List Nat)} {ph : KittenPhase}
    {scr : List (BitVec 32)} {cap : Nat} {lit : BitVec 32}
    (hK : KInv nv cls' false ph scr) (hsl : scr.length = cap) (hcap : 10240 ≤ cap)
    (hlit : lit.toNat < 2 * nv) (hnv : 1 ≤ nv) :
    let scrA := ((scr.set (256 + 18) 2#32).set (256 + 1184) 0#32).set (256 + 1185) lit
    scrA[256 + 18]? = some 2#32 ∧ scrA[256 + 1184]? = some 0#32 ∧
      scrA[256 + 1185]? = some lit ∧ KInv nv cls' false .solved scrA := by
  intro scrA
  have h18 : scrA[256 + 18]? = some 2#32 := by
    dsimp only [scrA]
    rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
      List.getElem?_set_self (by rw [hsl]; omega)]
  have h0 : scrA[256 + 1184]? = some 0#32 := by
    dsimp only [scrA]
    rw [List.getElem?_set_ne (by decide),
      List.getElem?_set_self (by rw [List.length_set, hsl]; omega)]
  have h1 : scrA[256 + 1185]? = some lit :=
    List.getElem?_set_self (by rw [List.length_set, List.length_set, hsl]; omega)
  refine ⟨h18, h0, h1, hLaws.set_assumps hK (by simp [scrA]) (fun i hi18 hi84 hi85 => ?_)
    (by rw [h18]; decide) (fun i hi => ?_)⟩
  · simp [scrA, List.getElem?_set_ne (Ne.symm hi18),
      List.getElem?_set_ne (Ne.symm hi84), List.getElem?_set_ne (Ne.symm hi85)]
  · have hi2 : i < 2 := by rw [h18] at hi; simp at hi; omega
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [h0]; simp; omega
    · rw [h1]; simp; exact hlit

private theorem kinv_assump2_b
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    (hLaws : KittenInvLaws KInv) {nv : Nat} {cls' : List (Nat × List Nat)} {ph : KittenPhase}
    {scr : List (BitVec 32)} {cap : Nat} {lit : BitVec 32}
    (hK : KInv nv cls' false ph scr) (hsl : scr.length = cap) (hcap : 10240 ≤ cap)
    (h18_in : scr[256 + 18]? = some 2#32) (hlit : lit.toNat < 2 * nv) (hnv : 1 ≤ nv) :
    let scrB := (scr.set (256 + 1184) 1#32).set (256 + 1185) lit
    scrB[256 + 18]? = some 2#32 ∧ scrB[256 + 1184]? = some 1#32 ∧
      scrB[256 + 1185]? = some lit ∧ KInv nv cls' false .solved scrB := by
  intro scrB
  have h18 : scrB[256 + 18]? = some 2#32 := by
    dsimp only [scrB]
    rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide), h18_in]
  have h0 : scrB[256 + 1184]? = some 1#32 := by
    dsimp only [scrB]
    rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by rw [hsl]; omega)]
  have h1 : scrB[256 + 1185]? = some lit :=
    List.getElem?_set_self (by rw [List.length_set, hsl]; omega)
  refine ⟨h18, h0, h1, hLaws.set_assumps hK (by simp [scrB]) (fun i _ hi84 hi85 => ?_)
    (by rw [h18]; decide) (fun i hi => ?_)⟩
  · simp [scrB, List.getElem?_set_ne (Ne.symm hi84), List.getElem?_set_ne (Ne.symm hi85)]
  · have hi2 : i < 2 := by rw [h18] at hi; simp at hi; omega
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [h0]; simp; omega
    · rw [h1]; simp; exact hlit

private theorem after_addUnit_cone
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 fuel0 : Nat}
    {cls' : List (Nat × List Nat)} {nv nc : Nat} {ws1' tmk' : List (BitVec 32)}
    {R : Mem 64 → Prop} {sU2 : FullState} {mU mV : Mem 64}
    (csU : ConeState KInv c F0 F_cur cv0 fuel0 cls' nv nc ws1' tmk' R sU2 mU)
    {valsV : List (BitVec 8)} {flagsV lvlV rsnsV trlV tpV : List (BitVec 32)}
    {teV propV clV : Nat} {unassV unflV incV : BitVec 64} {scV : FullScratch}
    (hlenV : ({ sU2 with
      core := { sU2.core with
        vals := valsV, flags := flagsV, lvl := lvlV, rsns := rsnsV, trl := trlV,
        trail_pos := tpV, trail_end := teV, propagated := propV, cur_level := clV,
        unassigned := unassV, unflushed := unflV, inconsistent := incV }
      scratch := scV } : FullState).LengthsOk c)
    (hwV : FullWitnessInv c F0 F_cur
      { sU2.core with
        vals := valsV, flags := flagsV, lvl := lvlV, rsns := rsnsV, trl := trlV,
        trail_pos := tpV, trail_end := teV, propagated := propV, cur_level := clV,
        unassigned := unassV, unflushed := unflV, inconsistent := incV })
    (hpresV : FullSweepVarSpecs.FullProbeScratchPres sU2
      { sU2 with
        core := { sU2.core with
          vals := valsV, flags := flagsV, lvl := lvlV, rsns := rsnsV, trl := trlV,
          trail_pos := tpV, trail_end := teV, propagated := propV, cur_level := clV,
          unassigned := unassV, unflushed := unflV, inconsistent := incV }
        scratch := scV })
    (hclV : clV = 0)
    (hmV : (FullMem c
      { sU2 with
        core := { sU2.core with
          vals := valsV, flags := flagsV, lvl := lvlV, rsns := rsnsV, trl := trlV,
          trail_pos := tpV, trail_end := teV, propagated := propV, cur_level := clV,
          unassigned := unassV, unflushed := unflV, inconsistent := incV }
        scratch := scV } ⋆ R) mV) :
    ∃ sV : FullState,
      sV = { sU2 with
        core := { sU2.core with
          vals := valsV, flags := flagsV, lvl := lvlV, rsns := rsnsV, trl := trlV,
          trail_pos := tpV, trail_end := teV, propagated := propV, cur_level := clV,
          unassigned := unassV, unflushed := unflV, inconsistent := incV }
        scratch := scV } ∧
      ConeState KInv c F0 F_cur cv0 fuel0 cls' nv nc ws1' tmk' R sV mV := by
  let sV : FullState :=
    { sU2 with
      core := { sU2.core with
        vals := valsV, flags := flagsV, lvl := lvlV, rsns := rsnsV, trl := trlV,
        trail_pos := tpV, trail_end := teV, propagated := propV, cur_level := clV,
        unassigned := unassV, unflushed := unflV, inconsistent := incV }
      scratch := scV }
  have hinvV := fullDenseInvW_after_addUnit csU.inv sV rfl hlenV hwV hpresV hclV
  have hws_raw : scV.work_stk1 = sU2.scratch.work_stk1 := hpresV.2.1
  have hcv_raw : sV.core.cur_vars = sU2.core.cur_vars := rfl
  have hconeV : fullSweepKittenConeOk F_cur sV cls' nv nc := by
    rcases csU.cone with ⟨h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨h1, h2, h3, h4, h5, fun i hi => ?_, fun cl hcl => ?_⟩
    · change (scV.work_stk1[i]?.getD 0#32).toNat < sV.core.cur_vars
      rw [hws_raw, hcv_raw]; exact h6 i hi
    · have h7c := h7 cl hcl
      refine ⟨h7c.1, ?_⟩
      have hgl : fullSweepGlobalLit sV = fullSweepGlobalLit sU2 := funext fun l => by
        simp only [fullSweepGlobalLit, sV, hws_raw]
      rw [hgl]; exact h7c.2
  have hwsV : sV.scratch.work_stk1 = ws1' := hws_raw.trans csU.ws
  have htmkV : sV.scratch.tarjan_mark = tmk' := hpresV.2.2.2.1.trans csU.tmk
  have hK' : KInv nv cls' false .solved sV.scratch.scratch_buf :=
    hpresV.2.2.2.2.1.symm ▸ csU.kinv
  exact ⟨sV, rfl, ⟨hinvV, csU.cv, csU.fuel, hconeV, hwsV, htmkV, hK', hmV⟩⟩

/-- **`full_sweep_var`**: `kitten`-backed dense cone SAT sweeping for one root variable,
cleaning up `tmk` to `TmkZero` on every exit and certifying `F0.Unsat` whenever returning `20`. -/
theorem full_sweep_var_wp (Γ : Env)
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    (hLaws : KittenInvLaws KInv)
    (hcone : EnvSpec Γ "full_sweep_cone" (fullSweepConeKittenSpec KInv))
    (hsolve : EnvSpec Γ "full_kitten_solve" (fullKittenSolveSpec KInv))
    (hrefine : EnvSpec Γ "full_sweep_refine_kitten" fullSweepRefineKittenSpec)
    (hflip : EnvSpec Γ "full_kitten_flip" (fullKittenFlipSpec KInv))
    (haddU : EnvSpec Γ "full_add_unit" FullSweepVarSpecs.fullAddUnitSpec)
    (haddB : EnvSpec Γ "full_add_bin" FullSweepVarSpecs.fullAddBinSpec) :
    ∀ args m Q X, fullSweepVarKittenSpec args m Q X →
      Func.wp Γ full_sweep_var_body args m Q X := by
  rintro ⟨h, root_v, tick_lim, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hcap, hroot_lt, htmk, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hinv.1.core_ok.cur_vars_le
  have hroot_lt31 : root_v.toNat < 2 ^ 31 := by omega
  unfold Func.wp full_sweep_var_body
  refine wp_call_of_spec _ _ (hcone _ _ _ _ ?_)
  dsimp only [vals, Arg.val_var]
  refine ⟨c, F0, F_cur, s, R, rfl, hinv, hcap, hroot_lt, htmk, hm, ?_⟩
  intro pk tmp' ws1' tmk' scr' m1
  dsimp only
  intro cls' hinv1 hcv1 hfuel1 hvals1 hinc1 hcone1 hK1 hws0 htmk1 hm1
  let s1 : FullState :=
    { s with
      core := { s.core with tmp := tmp' }
      scratch := { s.scratch with work_stk1 := ws1', tarjan_mark := tmk', scratch_buf := scr' } }
  let nv : BitVec 32 := (pk &&& 0xFFFF#64).setWidth 32
  let nc : BitVec 32 := (pk >>> (16 : Nat)).setWidth 32
  have hnv_eq : nv.toNat = (pk &&& 0xFFFF#64).toNat :=
    bv64_to32_toNat _ (by have := hcone1.2.1; omega)
  have hnc_eq : nc.toNat = (pk >>> (16 : Nat)).toNat :=
    bv64_to32_toNat _ (by have := hcone1.2.2.2.1; have := hcone1.2.2.2.2.1; omega)
  have hnv128 : nv.toNat ≤ 128 := by rw [hnv_eq]; exact hcone1.2.1
  have hnv_pos : 1 ≤ nv.toNat := by rw [hnv_eq]; exact hcone1.1
  have hcone1' : fullSweepKittenConeOk F_cur s1 cls' nv.toNat nc.toNat := by
    rw [hnv_eq, hnc_eq]; exact hcone1
  have hK1' : KInv nv.toNat cls' false .fresh scr' := hnv_eq ▸ hK1
  have hws1_len : ws1'.length = 2 * c.max_vars := hinv1.1.scratch_ok.work_stk1_len
  have htmk1_len : tmk'.length = 2 * c.max_vars := hinv1.1.scratch_ok.tarjan_mark_len
  have hscr1_len : scr'.length = c.scratch_cap := hinv1.1.scratch_ok.scratch_buf_len
  have htmk1' : ∀ v < s.core.cur_vars, tmk'[v]?.getD 0#32 ≠ 0#32 →
      ∃ i < nv.toNat, (ws1'[i]?.getD 0#32).toNat = v :=
    fun v hv hne => let ⟨k, hk, hwk⟩ := htmk1 v hv hne; ⟨k, hnv_eq ▸ hk, hwk⟩
  have hnv_cv : nv.toNat ≤ s.core.cur_vars := hcone1'.2.2.1
  have hnv_mx : nv.toNat ≤ 2 * c.max_vars := by omega
  have hsig1_len : s1.scratch.sim_sig.length = c.max_vars := hinv1.1.scratch_ok.sim_sig_len
  ds_to_group
  -- Early exit: `if (nv < 2u || nc == 0u)`
  refine wp_join_group (ts := []) (fun (_ : Tup Val []) mJ => mJ = m1) ?_ ?_
  · intro _ () mJ hmJ; subst hmJ; ds_to_group
    refine sweep_tmk_clear_wp rfl rfl hnv_mx hinv1 rfl rfl (cone_stk_lt hcone1') htmk1' hm1
      fun tmk_c m_end ht_len ht_done hm_end => by
        ds_steps
        exact hQ 1#64 _ m_end (fullDenseInvW_with_tmk hinv1 ht_len) rfl
          (hfuel1 ▸ Nat.le_refl _) ht_done (Or.inl rfl) (fun h => by cases h) hm_end
  intro _ hJflg
  ds_steps
  · exact hJflg () m1 rfl
  · exact hJflg () m1 rfl
  dsimp only [LeanQbe.T.lift2, LeanQbe.T.Arg.val, LeanQbe.T.Arg.imm, Prod.fst] at *
  have hnv_ge2 : 2 ≤ nv.toNat := by
    dsimp only [nv]
    have hc1 : ¬ ((pk &&& 0xFFFF#64).setWidth 32).toNat < 2 := by bv_omega
    omega
  -- Zero `sig[cone_v[0..nv)]`
  refine wp_loop_inv (ts := [i32])
    (fun (i, ()) ms => i.toNat ≤ nv.toNat ∧ ∃ sig0 : List (BitVec 64),
      sig0.length = c.max_vars ∧
      (FullMem c { s1 with scratch := { s1.scratch with sim_sig := sig0 } } ⋆ R) ms)
    (fun (i, ()) _ => nv.toNat - i.toNat) ?_ ?_
  · intro _ hLs
    ds_steps; exact hLs (0#32, ()) m1 ⟨Nat.zero_le _, s1.scratch.sim_sig, hsig1_len, hm1⟩
  intro _ (i, ()) ms ⟨hi_le, sig0, hsig0_len, hms⟩ hLs
  ds_split
  · have hi_lt : i.toNat < nv.toNat := by bv_omega
    have hgv_lt : (ws1'[i.toNat]'(by rw [hws1_len]; omega)).toNat < c.max_vars := by
      have h0 := cone_stk_lt hcone1' i.toNat hi_lt
      dsimp only [s1] at h0
      rw [List.getElem?_eq_getElem (by rw [hws1_len]; omega), Option.getD_some] at h0
      omega
    have hi_ws : (BitVec.setWidth 64 i).toNat <
        ({ s1 with scratch := { s1.scratch with sim_sig := sig0 } } :
          FullState).scratch.work_stk1.length := by
      change (BitVec.setWidth 64 i).toNat < ws1'.length
      rw [hws1_len, bv_c0_zext32_64]; omega
    have hgv_sig : (BitVec.setWidth 64 (({ s1 with scratch :=
        { s1.scratch with sim_sig := sig0 } } :
        FullState).scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'hi_ws)).toNat <
        sig0.length := by
      have heqv : ({ s1 with scratch := { s1.scratch with sim_sig := sig0 } } :
          FullState).scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'hi_ws =
          ws1'[i.toNat]'(by rw [hws1_len]; omega) :=
        Option.some.inj (by
          rw [← List.getElem?_eq_getElem hi_ws,
            ← List.getElem?_eq_getElem (by rw [hws1_len]; omega), bv_c0_zext32_64])
      rw [heqv, hsig0_len, bv_c0_zext32_64]; exact hgv_lt
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := dsSweep_bv32_add1_lt (by omega)
    ds_steps
    exact hLs (i + 1#32, ()) _ (by dsimp only; omega)
      ⟨by omega, _, List.length_set.trans hsig0_len, by assumption⟩
  -- `k[18] = 0u; st0 = full_kitten_solve(h, tick_lim)`
  let s1' : FullState := { s1 with scratch := { s1.scratch with sim_sig := sig0 } }
  have hinv1' : FullDenseInvW c F0 F_cur s1' := fullDenseInvW_after_refine hinv1 hsig0_len
  let scrA := scr'.set (256 + 18) 0#32
  let sA : FullState := { s1' with scratch := { s1'.scratch with scratch_buf := scrA } }
  have hscrA_len : scrA.length = c.scratch_cap := by simp [scrA, hscr1_len]
  have hinvA : FullDenseInvW c F0 F_cur sA :=
    fullDenseInvW_with_fuel_scratch hinv1'
      { hinv1'.1.scratch_ok with scratch_buf_len := hscrA_len } rfl rfl
  have h18_A_eq : scrA[256 + 18]? = some 0#32 := List.getElem?_set_self (by rw [hscr1_len]; omega)
  have hKA : KInv nv.toNat cls' false .solved scrA :=
    hLaws.set_assumps hK1' (by simp [scrA])
      (fun j hj18 _ _ => List.getElem?_set_ne (Ne.symm hj18))
      (by rw [h18_A_eq]; decide) (fun j hj => by rw [h18_A_eq] at hj; simp at hj)
  have h18_A : (scrA[256 + 18]?.getD 0#32).toNat = 0 := by rw [h18_A_eq]; rfl
  have hk274 : 256 + 72 / 4 < scr'.length := by rw [hscr1_len]; omega
  ds_steps; c0_call hsolve
  refine ⟨c, sA, nv.toNat, cls', false, .solved, R, rfl, hinvA.1, hcap, hKA,
    (by simp only [sA, s1', scrA]; assumption),
    fun st0 fuel2 scr2 m2 hsl2 hfuel2 _ h18_2 hK2 _ huns2 _ hm2 => ?_⟩
  let s2 : FullState :=
    { sA with
      core := { sA.core with fuel := fuel2 }
      scratch := { sA.scratch with scratch_buf := scr2 } }
  have hinv2 : FullDenseInvW c F0 F_cur s2 :=
    fullDenseInvW_with_fuel_scratch hinvA
      { hinvA.1.scratch_ok with scratch_buf_len := hsl2 } rfl rfl
  have hcone2 : fullSweepKittenConeOk F_cur s2 cls' nv.toNat nc.toNat := hcone1'
  have hfuel2_0 : s2.core.fuel.toNat ≤ s.core.fuel.toNat := by
    change fuel2.toNat ≤ s.core.fuel.toNat; rw [← hfuel1]; exact hfuel2
  ds_split
  · have hst0_20 : st0 = 20#64 := by bv_omega
    have hu_fcur : (cnfOfClauses F_cur).Unsat :=
      kitten_unsat_of_solve0 (scr := scrA) (fun cl hcl => (cone_cls hcone2 cl hcl).2) h18_A
        (huns2 hst0_20)
    have huns_f0 : F0.Unsat := hinv2.2.1.ext_sound.2 hu_fcur
    ds_to_group
    refine sweep_tmk_clear_wp rfl rfl hnv_mx hinv2 rfl rfl (cone_stk_lt hcone2) htmk1' hm2
      fun tmk_c m_end ht_len ht_done hm_end => by
        ds_steps
        have hinv2' := fullDenseInvW_with_inconsistent (fullDenseInvW_with_tmk hinv2 ht_len) hu_fcur
        exact hQ 20#64 _ _ hinv2' rfl hfuel2_0 ht_done (Or.inr rfl) (fun _ => huns_f0)
          (by assumption)
  ds_split
  · ds_to_group
    refine sweep_tmk_clear_wp rfl rfl hnv_mx hinv2 rfl rfl (cone_stk_lt hcone2) htmk1' hm2
      fun tmk_c m_end ht_len ht_done hm_end => by
        ds_steps
        exact hQ 1#64 _ m_end (fullDenseInvW_with_tmk hinv2 ht_len) rfl hfuel2_0 ht_done
          (Or.inl rfl) (fun h => by cases h) hm_end
  -- `st0 == 10`: refine bit 0, then flip loop
  ds_steps; c0_call hrefine
  refine ⟨c, s2, R, rfl, hinv2.1, hcap, hnv128, hnv_mx, cone_stk_lt hcone2, hm2,
    fun sig2' m2' hsig2' hm2' => ?_⟩
  let s2' : FullState := { s2 with scratch := { s2.scratch with sim_sig := sig2' } }
  have cs2' : ConeState KInv c F0 F_cur s.core.cur_vars s.core.fuel.toNat cls'
      nv.toNat nc.toNat ws1' tmk' R s2' m2' :=
    ⟨fullDenseInvW_after_refine hinv2 hsig2', rfl, hfuel2_0, hcone2, rfl, rfl,
     (by simpa using hK2), hm2'⟩
  let CS : Mem 64 → Prop := fun mN => ∃ sN,
    ConeState KInv c F0 F_cur s.core.cur_vars s.core.fuel.toNat cls'
      nv.toNat nc.toNat ws1' tmk' R sN mN
  ds_to_group
  refine wp_loop_inv (ts := [i32, i32]) (fun (rbit, _, ()) mr => rbit.toNat ≤ 4 ∧ CS mr)
    (fun (_, s_idx, ()) _ => nv.toNat - s_idx.toNat) ?_ ?_
  · intro _ hLs_lp
    ds_steps; exact hLs_lp (1#32, 1#32, ()) m2' ⟨by decide, s2', cs2'⟩
  intro _ (rbit, s_idx, ()) mr ⟨hrbit_le, sr, cs_r⟩ hLs_lp
  refine wp_join_group (ts := []) (fun (_ : Tup Val []) mEx => mEx = mr) ?_ ?_
  rotate_left
  · intro _ hJex
    have hm_r := cs_r.mem
    ds_split; rotate_left; · ds_steps; exact hJex () mr rfl
    ds_split; rotate_left; · ds_steps; exact hJex () mr rfl
    dsimp only [LeanQbe.T.lift2, LeanQbe.T.Arg.val, LeanQbe.T.Arg.imm, Prod.fst] at *
    have hs_lt : s_idx.toNat < nv.toNat := by bv_omega
    have hs_lt_sh : s_idx.toNat < 2 ^ 31 := by omega
    have hr_lt4 : rbit.toNat < 4 := by bv_omega
    have hs1_idx : (s_idx + 1#32).toNat = s_idx.toNat + 1 := dsSweep_bv32_add1_lt (by omega)
    have hr1_bit : (rbit + 1#32).toNat = rbit.toNat + 1 := dsSweep_bv32_add1_lt (by omega)
    have hr1_le : (rbit + 1#32).toNat ≤ 4 := by omega
    have hlit0 : (s_idx <<< (1 : Nat)).toNat < 2 * nv.toNat := by
      rw [bv32_shl1_toNat s_idx hs_lt_sh]; omega
    have hlit1 : ((s_idx <<< (1 : Nat)) ||| 1#32).toNat < 2 * nv.toNat := by
      rw [FullSweepVarHelpers.bv32_shl1_or_pol s_idx 1#32 hs_lt_sh (by decide),
        show (1#32).toNat = 1 from rfl]
      omega
    ds_to_group
    refine wp_join_group (ts := [i32]) (fun (rbit_n, ()) mrn => rbit_n.toNat ≤ 4 ∧ CS mrn) ?_ ?_
    · intro _ (rbit_n, ()) mrn ⟨hrbn, cs_rn⟩
      ds_steps; exact hLs_lp (rbit_n, s_idx + 1#32, ()) mrn (by dsimp only; omega) ⟨hrbn, cs_rn⟩
    intro _ hJrn
    refine wp_join_group (ts := []) (fun () mrf => CS mrf) ?_ ?_
    · intro _ () mrf ⟨srf, cs_f⟩
      have hm_f := cs_f.mem
      c0_call hrefine
      refine ⟨c, srf, R, rfl, cs_f.inv.1, hcap, hnv128, hnv_mx, cone_stk_lt cs_f.cone, hm_f,
        fun sigf mf' hsigf hmf' => ?_⟩
      ds_steps; exact hJrn (rbit + 1#32, ()) mf' ⟨hr1_le, _, cs_f.after_refine hsigf hmf'⟩
    intro _ hJrf
    c0_call hflip
    refine ⟨c, sr, nv.toNat, cls', false, .solved, R, rfl, cs_r.inv.1, hcap, cs_r.kinv, hlit0, hm_r,
      fun ok1 scr_f1 m_f1 hsl_f1 _ _ hKf1 hm_f1 => ?_⟩
    have cs_f1 := cs_r.with_scr hsl_f1 hKf1 hm_f1
    ds_split
    · ds_steps; exact hJrf () m_f1 ⟨_, cs_f1⟩
    c0_call hflip
    refine ⟨c, _, nv.toNat, cls', false, .solved, R, rfl, cs_f1.inv.1, hcap, hKf1, hlit1, hm_f1,
      fun ok2 scr_f2 m_f2 hsl_f2 _ _ hKf2 hm_f2 => ?_⟩
    have cs_f2 := cs_f1.with_scr hsl_f2 hKf2 hm_f2
    ds_split
    · ds_steps; exact hJrf () m_f2 ⟨_, cs_f2⟩
    · ds_steps; exact hJrn (rbit, ()) m_f2 ⟨by omega, _, cs_f2⟩
  -- Flip loop exit: `smask`, `s0` unit test, `j`-loop
  intro _ () mEx hEx; subst mEx
  ds_to_group
  refine wp_join_group (ts := [i64]) (fun (_smask, ()) msm => msm = mr) ?_ ?_
  rotate_left
  · intro _ hJsm
    have hm_r := cs_r.mem
    ds_split <;> · ds_steps; exact hJsm _ mr rfl
  intro _ (smask, ()) msm hmsm; subst msm
  have hsig_r_len : sr.scratch.sim_sig.length = c.max_vars := cs_r.inv.1.scratch_ok.sim_sig_len
  have hroot_sig : (BitVec.setWidth 64 root_v).toNat < sr.scratch.sim_sig.length := by
    rw [hsig_r_len, bv_c0_zext32_64]; omega
  have hm_r := cs_r.mem
  ds_to_group
  refine wp_join_group (ts := [i32, i32, i64]) (fun (_i3, _rbit3, _smask3, ()) m3 => CS m3) ?_ ?_
  rotate_left
  · intro _ hJu
    refine wp_join_group (ts := []) (fun (_ : Tup Val []) mJ => mJ = mr) ?_ ?_
    rotate_left
    · intro _ hdo
      ds_split; · ds_steps; exact hdo () mr rfl
      ds_split; · ds_steps; exact hdo () mr rfl
      ds_steps; exact hJu (_, rbit, smask, ()) mr ⟨sr, cs_r⟩
    intro _ () mJ hmJ; subst mJ
    refine wp_join_group (ts := [i32])
      (fun (test, ()) mT => mT = mr ∧ (test = 0#32 ∨ test = 1#32)) ?_ ?_
    rotate_left
    · intro _ hJtest
      ds_steps; · exact hJtest (0#32, ()) mr ⟨rfl, Or.inl rfl⟩
      · exact hJtest (1#32, ()) mr ⟨rfl, Or.inr rfl⟩
    intro _ (test, ()) mT ⟨hmT, htest⟩; subst mT
    have htest_x_lt : (test ^^^ 1#32).toNat < 2 * nv.toNat := by
      rcases htest with rfl | rfl <;> simp <;> omega
    refine wp_join_group (ts := [i32, i32, i64]) (fun _ mU => CS mU) ?_ ?_
    · intro _ _ mU h; ds_steps; exact hJu _ mU h
    intro _ hJu3
    c0_call hflip
    refine ⟨c, sr, nv.toNat, cls', false, .solved, R, rfl, cs_r.inv.1, hcap, cs_r.kinv,
      htest_x_lt, hm_r, fun okF scrF mF hslF _ _ hKF hmF => ?_⟩
    let sF : FullState := { sr with scratch := { sr.scratch with scratch_buf := scrF } }
    have csF := cs_r.with_scr hslF hKF hmF
    ds_split
    · refine wp_join_group (ts := [i32, i64]) (fun _ mR => CS mR) ?_ ?_
      · intro _ _ mR h; ds_steps; exact hJu3 _ mR h
      intro _ hJrR
      ds_split
      · c0_call hrefine
        refine ⟨c, sF, R, rfl, csF.inv.1, hcap, hnv128, hnv_mx, cone_stk_lt csF.cone, hmF,
          fun sigF mF' hsigF hmF' => ?_⟩
        ds_steps; exact hJrR _ mF' ⟨_, csF.after_refine hsigF hmF'⟩
      · ds_steps; exact hJrR (rbit, smask, ()) mF ⟨sF, csF⟩
    -- `!flip == true`: `k[18] = 1; k[1184] = test; d = full_kitten_solve`
    let scrU := (scrF.set (256 + 18) 1#32).set (256 + 1184) test
    let sU : FullState := { sF with scratch := { sF.scratch with scratch_buf := scrU } }
    have hscrU_len : scrU.length = c.scratch_cap := by simp [scrU, hslF]
    have hinvU : FullDenseInvW c F0 F_cur sU :=
      fullDenseInvW_with_fuel_scratch csF.inv
        { csF.inv.1.scratch_ok with scratch_buf_len := hscrU_len } rfl rfl
    obtain ⟨hU18, hU0, hKU⟩ := kinv_assump1 hLaws hKF hslF hcap htest hnv_pos
    have hk72F : 256 + 72 / 4 < scrF.length := by rw [hslF]; omega
    have hk4736F : 256 + 4736 / 4 < scrF.length := by rw [hslF]; omega
    ds_steps; c0_call hsolve
    refine ⟨c, sU, nv.toNat, cls', false, .solved, R, rfl, hinvU.1, hcap, hKU,
      (by simp only [sU, scrU]; assumption),
      fun dU fuelU scrU2 mU hslU2 hfuelU _ _ hKU2 _ hunsU _ hmU => ?_⟩
    let sU2 : FullState :=
      { sU with
        core := { sU.core with fuel := fuelU }
        scratch := { sU.scratch with scratch_buf := scrU2 } }
    have csU2 := csF.with_fuel_scr hslU2 hfuelU (by simpa using hKU2) hmU
    refine wp_join_group (ts := [i32, i32, i64]) (fun _ mM => CS mM) ?_ ?_
    · intro _ _ mM h; ds_steps; exact hJu3 _ mM h
    intro _ hJdU
    ds_split
    · have hdU20 : dU = 20#64 := by bv_omega
      have hentU := kitten_unsat_entails_unit (s := sU2) (cls := cls') (scr := scrU)
        (fun cl hcl => (cone_cls csU2.cone cl hcl).2) (csU2.ws ▸ hws0) hroot_lt31 htest
        hU18 hU0 (hunsU hdU20)
      have hlitU_lt : ((root_v <<< (1 : Nat)) ||| (1#32 - test)).toNat <
          2 * sU2.core.cur_vars := by
        have h1sub : (1#32 - test).toNat < 2 := by rcases htest with rfl | rfl <;> decide
        rw [FullSweepVarHelpers.bv32_shl1_or_pol root_v (1#32 - test) hroot_lt31 h1sub,
          bv32_1_sub_toNat test htest, csU2.cv]
        omega
      c0_call haddU
      refine ⟨c, F0, F_cur, sU2, R, rfl, csU2.inv.1, csU2.inv.2.1, fun _ => hentU, hmU, ?_⟩
      intro okU valsV flagsV lvlV rsnsV trlV tpV teV propV clV unassV unflV incV
        scV mV _ hlenV hwV hpresV hclV hokF _ hmV
      obtain ⟨sV, _, csV⟩ := after_addUnit_cone csU2 hlenV hwV hpresV hclV hmV
      have hmV1 : (FullMem c sV ⋆ R) mV := csV.mem
      ds_split
      · ds_steps; exact hJdU _ _ ⟨_, csV.with_sweep_cnt _ (by assumption)⟩
      · have hok_f : okU = false := by cases okU <;> simp_all
        have hunsV : F0.Unsat := (hokF hlitU_lt hok_f).1
        ds_to_group
        refine sweep_tmk_clear_wp rfl rfl hnv_mx csV.inv csV.ws csV.tmk (cone_stk_lt csV.cone)
          (fun u hu => htmk1' u (csV.cv ▸ hu)) hmV1 fun tmk_c m_end ht_len ht_done hm_end => by
            ds_steps
            exact hQ 20#64 _ m_end (fullDenseInvW_with_tmk csV.inv ht_len) csV.cv csV.fuel
              ht_done (Or.inr rfl) (fun _ => hunsV) hm_end
    refine wp_join_group (ts := [i32, i64]) (fun _ mR2 => CS mR2) ?_ ?_
    · intro _ _ mR2 h; ds_steps; exact hJdU _ mR2 h
    intro _ hJdU10
    ds_split
    · ds_split
      · c0_call hrefine
        refine ⟨c, sU2, R, rfl, csU2.inv.1, hcap, hnv128, hnv_mx, cone_stk_lt csU2.cone, hmU,
          fun sigU mU' hsigU hmU' => ?_⟩
        ds_steps; exact hJdU10 _ mU' ⟨_, csU2.after_refine hsigU hmU'⟩
      · ds_steps; exact hJdU10 (rbit, smask, ()) mU ⟨sU2, csU2⟩
    · ds_steps; exact hJdU10 (rbit, smask, ()) mU ⟨sU2, csU2⟩
  -- `j`-loop: `while (j < nv && h->inconsistent == 0 && h->fuel > 0)`
  intro _ (_i3, rbit3, smask3, ()) m3 ⟨s3, cs3⟩
  refine wp_loop_inv (ts := [i32, i64, i32])
    (fun (_, _, j, ()) ml => j.toNat ≤ nv.toNat ∧ CS ml)
    (fun (_, _, j, ()) _ => nv.toNat - j.toNat) ?_ ?_
  · intro _ hJL
    ds_steps; exact hJL (rbit3, smask3, 1#32, ()) m3 ⟨Nat.le_trans (by decide) hnv_pos, s3, cs3⟩
  intro _ (rbitL, smaskL, j, ()) ml ⟨hj_le, sL, csL⟩ hJL
  refine wp_join_group (ts := []) (fun (_ : Tup Val []) mEx => mEx = ml) ?_ ?_
  · intro _ () mEx hEx; subst mEx
    ds_to_group
    refine sweep_tmk_clear_wp rfl rfl hnv_mx csL.inv csL.ws csL.tmk (cone_stk_lt csL.cone)
      (fun u hu => htmk1' u (csL.cv ▸ hu)) csL.mem fun tmk_c m_end ht_len ht_done hm_end => by
        ds_steps
        exact hQ 1#64 _ m_end (fullDenseInvW_with_tmk csL.inv ht_len) csL.cv csL.fuel
          ht_done (Or.inl rfl) (fun h => by cases h) hm_end
  intro _ hJexJ
  have hml := csL.mem
  have hcvL := csL.cv
  ds_split; rotate_left; · ds_steps; exact hJexJ () ml rfl
  ds_split; rotate_left; · ds_steps; exact hJexJ () ml rfl
  ds_split; rotate_left; · ds_steps; exact hJexJ () ml rfl
  dsimp only [LeanQbe.T.lift2, LeanQbe.T.Arg.val, LeanQbe.T.Arg.imm, Prod.fst] at *
  have hj_lt : j.toNat < nv.toNat := by bv_omega
  have hj_lt31 : j.toNat < 2 ^ 31 := by omega
  have hwsL_len := csL.inv.1.scratch_ok.work_stk1_len
  have hsigL_len := csL.inv.1.scratch_ok.sim_sig_len
  have hscrL_len := csL.inv.1.scratch_ok.scratch_buf_len
  have hov_lt : (ws1'[j.toNat]'(by rw [← csL.ws, hwsL_len]; omega)).toNat < s.core.cur_vars := by
    have h0 := cone_stk_lt csL.cone j.toNat hj_lt
    rw [csL.ws, List.getElem?_eq_getElem (by rw [← csL.ws, hwsL_len]; omega),
      Option.getD_some] at h0
    omega
  have hj1 : (j + 1#32).toNat = j.toNat + 1 := dsSweep_bv32_add1_lt (by omega)
  have hj_ws : (BitVec.setWidth 64 j).toNat < sL.scratch.work_stk1.length := by
    rw [hwsL_len, bv_c0_zext32_64]; omega
  have hgv_sig : (BitVec.setWidth 64
      (sL.scratch.work_stk1[(BitVec.setWidth 64 j).toNat]'hj_ws)).toNat <
      sL.scratch.sim_sig.length :=
    tmk_idx_lt csL.ws (by rw [hws1_len]; omega)
      (by rw [hsigL_len]; exact lt_of_lt_of_le hov_lt hcv_le) hj_ws
  have hroot_sigL : (BitVec.setWidth 64 root_v).toNat < sL.scratch.sim_sig.length := by
    rw [hsigL_len, bv_c0_zext32_64]; omega
  ds_to_group
  refine wp_join_group (ts := [i32, i32, i64]) (fun _ mN => CS mN) ?_ ?_
  · intro _ (_iN, rbitN, smaskN, ()) mN hN
    ds_steps; exact hJL (rbitN, smaskN, j + 1#32, ()) mN (by dsimp only; omega)
      ⟨by dsimp only; omega, hN⟩
  intro _ hJif
  let ov := ws1'[j.toNat]'(by rw [← csL.ws, hwsL_len]; omega)
  have hov_lt31 : ov.toNat < 2 ^ 31 := lt_trans hov_lt (by omega)
  have hk_bd : 256 + 4740 / 4 < sL.scratch.scratch_buf.length := by rw [hscrL_len]; omega
  have hk72_L : 256 + 72 / 4 < sL.scratch.scratch_buf.length := by rw [hscrL_len]; omega
  have hk4736_L : 256 + 4736 / 4 < sL.scratch.scratch_buf.length := by rw [hscrL_len]; omega
  refine wp_join_group (ts := []) (fun (_ : Tup Val []) mJ => mJ = ml) ?_ ?_
  rotate_left
  · intro _ hdo
    ds_split; · ds_steps; exact hdo () ml rfl
    ds_split; · ds_steps; exact hdo () ml rfl
    ds_steps; exact hJif (_, rbitL, smaskL, ()) ml ⟨sL, csL⟩
  intro _ () mJ hmJ; subst mJ
  refine wp_join_group (ts := [i32])
    (fun (pol, ()) mP => mP = ml ∧ (pol = 0#32 ∨ pol = 1#32)) ?_ ?_
  rotate_left
  · intro _ hJpol
    ds_steps; · exact hJpol (0#32, ()) ml ⟨rfl, Or.inl rfl⟩
    · exact hJpol (1#32, ()) ml ⟨rfl, Or.inr rfl⟩
  intro _ (pol, ()) mP ⟨hmP, hpol⟩; subst mP
  have hxp_lt : ((j <<< (1 : Nat)) ||| (1#32 ^^^ pol)).toNat < 2 * nv.toNat := by
    have h1 : (1#32 ^^^ pol).toNat < 2 := by rcases hpol with rfl | rfl <;> decide
    rw [FullSweepVarHelpers.bv32_shl1_or_pol j (1#32 ^^^ pol) hj_lt31 h1]; omega
  let scrA :=
    ((sL.scratch.scratch_buf.set (256 + 18) 2#32).set (256 + 1184) 0#32).set (256 + 1185)
      ((j <<< (1 : Nat)) ||| (1#32 ^^^ pol))
  let sA : FullState := { sL with scratch := { sL.scratch with scratch_buf := scrA } }
  have hscrA_len : scrA.length = c.scratch_cap := by simp [scrA, hscrL_len]
  have hinvA : FullDenseInvW c F0 F_cur sA :=
    fullDenseInvW_with_fuel_scratch csL.inv
      { csL.inv.1.scratch_ok with scratch_buf_len := hscrA_len } rfl rfl
  obtain ⟨hA_18, hA_0, hA_1, hKA⟩ := kinv_assump2_a hLaws csL.kinv hscrL_len hcap hxp_lt hnv_pos
  ds_steps; c0_call hsolve
  refine ⟨c, sA, nv.toNat, cls', false, .solved, R, rfl, hinvA.1, hcap, hKA,
    (by simp only [sA, scrA]; assumption),
    fun d1 fuel1 scr1 m1_d hsl1 hfuel1 _ h18_1 hK1_d _ huns1 _ hm1_d => ?_⟩
  let s1_d : FullState :=
    { sA with
      core := { sA.core with fuel := fuel1 }
      scratch := { sA.scratch with scratch_buf := scr1 } }
  have cs1_d := csL.with_fuel_scr hsl1 hfuel1 (by simpa using hK1_d) hm1_d
  have h1_18 : scr1[256 + 18]? = some 2#32 := h18_1.trans hA_18
  refine wp_join_group (ts := [i32, i32, i64]) (fun _ mN => CS mN) ?_ ?_
  · intro _ _ mN h; ds_steps; exact hJif _ mN h
  intro _ hJd1
  refine wp_join_group (ts := []) (fun (_ : Tup Val []) mE => mE = m1_d) ?_ ?_
  rotate_left
  · intro _ hJd1_e2
    ds_split
    · ds_split
      · c0_call hrefine
        refine ⟨c, s1_d, R, rfl, cs1_d.inv.1, hcap, hnv128, hnv_mx,
          cone_stk_lt cs1_d.cone, hm1_d, fun sig1 m1' hsig1 hm1' => ?_⟩
        ds_steps; exact hJd1 _ m1' ⟨_, cs1_d.after_refine hsig1 hm1'⟩
      · ds_steps; exact hJd1_e2 () m1_d rfl
    · ds_steps; exact hJd1_e2 () m1_d rfl
  intro _ () mE hmE; subst mE
  refine wp_join_group (ts := [i32, i32, i64]) (fun _ mN => CS mN) ?_ ?_
  · intro _ _ mN h; ds_steps; exact hJd1 _ mN h
  intro _ hJd1_e
  ds_split; rotate_left
  · ds_steps; exact hJd1_e _ m1_d ⟨s1_d, cs1_d⟩
  have hd1_20 : d1 = 20#64 := by bv_omega
  have hpol_lt : ((j <<< (1 : Nat)) ||| pol).toNat < 2 * nv.toNat := by
    have h1 : pol.toNat < 2 := by rcases hpol with rfl | rfl <;> decide
    rw [FullSweepVarHelpers.bv32_shl1_or_pol j pol hj_lt31 h1]; omega
  let scrB := (scr1.set (256 + 1184) 1#32).set (256 + 1185) ((j <<< (1 : Nat)) ||| pol)
  let sB : FullState := { s1_d with scratch := { s1_d.scratch with scratch_buf := scrB } }
  have hscrB_len : scrB.length = c.scratch_cap := by simp [scrB, hsl1]
  have hinvB : FullDenseInvW c F0 F_cur sB :=
    fullDenseInvW_with_fuel_scratch cs1_d.inv
      { cs1_d.inv.1.scratch_ok with scratch_buf_len := hscrB_len } rfl rfl
  obtain ⟨hB_18, hB_0, hB_1, hKB⟩ := kinv_assump2_b hLaws cs1_d.kinv hsl1 hcap h1_18 hpol_lt hnv_pos
  have hk4736_1 : 256 + 4736 / 4 < scr1.length := by rw [hsl1]; omega
  have hk4740_1 : 256 + 4740 / 4 < scr1.length := by rw [hsl1]; omega
  ds_steps; c0_call hsolve
  refine ⟨c, sB, nv.toNat, cls', false, .solved, R, rfl, hinvB.1, hcap, hKB,
    (by simp only [sB, scrB]; assumption),
    fun d2 fuel2 scr2 m2_d hsl2 hfuel2 _ _ hK2_d _ huns2 _ hm2_d => ?_⟩
  let s2_d : FullState :=
    { sB with
      core := { sB.core with fuel := fuel2 }
      scratch := { sB.scratch with scratch_buf := scr2 } }
  have cs2_d := cs1_d.with_fuel_scr hsl2 hfuel2 (by simpa using hK2_d) hm2_d
  refine wp_join_group (ts := [i32, i32, i64]) (fun _ mN => CS mN) ?_ ?_
  · intro _ _ mN h; ds_steps; exact hJd1_e _ mN h
  intro _ hJd2
  refine wp_join_group (ts := []) (fun (_ : Tup Val []) mE2 => mE2 = m2_d) ?_ ?_
  rotate_left
  · intro _ hJd2_e2
    ds_split
    · ds_split
      · c0_call hrefine
        refine ⟨c, s2_d, R, rfl, cs2_d.inv.1, hcap, hnv128, hnv_mx,
          cone_stk_lt cs2_d.cone, hm2_d, fun sig2 m2' hsig2 hm2' => ?_⟩
        ds_steps; exact hJd2 _ m2' ⟨_, cs2_d.after_refine hsig2 hm2'⟩
      · ds_steps; exact hJd2_e2 () m2_d rfl
    · ds_steps; exact hJd2_e2 () m2_d rfl
  intro _ () mE2 hmE2; subst mE2
  refine wp_join_group (ts := [i32]) (fun (_iE, ()) mE3 => CS mE3) ?_ ?_
  · intro _ _ mE3 h; ds_steps; exact hJd2 _ mE3 h
  intro _ hJd2_e
  ds_split; rotate_left
  · ds_steps; exact hJd2_e _ m2_d ⟨s2_d, cs2_d⟩
  have hd2_20 : d2 = 20#64 := by bv_omega
  have hws2_len := cs2_d.inv.1.scratch_ok.work_stk1_len
  have hent1 := kitten_unsat_entails_bin1 (s := s2_d) (cls := cls') (scr := scrA)
    (fun cl hcl => (cone_cls cs2_d.cone cl hcl).2) (cs2_d.ws ▸ hws0)
    (by rw [cs2_d.ws, List.getElem?_eq_getElem (by rw [hws1_len]; omega), Option.getD_some])
    hj_lt31 hpol hroot_lt31 hov_lt31 hA_18 hA_0 hA_1 (huns1 hd1_20)
  have hent2 := kitten_unsat_entails_bin2 (s := s2_d) (cls := cls') (scr := scrB)
    (fun cl hcl => (cone_cls cs2_d.cone cl hcl).2) (cs2_d.ws ▸ hws0)
    (by rw [cs2_d.ws, List.getElem?_eq_getElem (by rw [hws1_len]; omega), Option.getD_some])
    hj_lt31 hpol hroot_lt31 hov_lt31 hB_18 hB_0 hB_1 (huns2 hd2_20)
  have hov_eq : s2_d.scratch.work_stk1[(BitVec.setWidth 64 j).toNat]'(by
      rw [hws2_len, bv_c0_zext32_64]; omega) = ov :=
    Option.some.inj (by
      rw [← List.getElem?_eq_getElem (by rw [hws2_len, bv_c0_zext32_64]; omega),
        ← List.getElem?_eq_getElem (by rw [hws1_len]; omega), bv_c0_zext32_64, cs2_d.ws])
  have hent1' : (cnfOfClauses F_cur).EntailsClause (cnfClause
      [((root_v <<< (1 : Nat)) ^^^ 1#32).toNat,
        ((s2_d.scratch.work_stk1[(BitVec.setWidth 64 j).toNat]'(by
          rw [hws2_len, bv_c0_zext32_64]; omega) <<< (1 : Nat)) ||| pol).toNat]) := by
    rw [hov_eq]; exact hent1
  have hent2' : (cnfOfClauses F_cur).EntailsClause (cnfClause
      [(root_v <<< (1 : Nat)).toNat,
        (((s2_d.scratch.work_stk1[(BitVec.setWidth 64 j).toNat]'(by
          rw [hws2_len, bv_c0_zext32_64]; omega) <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat]) := by
    rw [hov_eq]; exact hent2
  ds_to_group
  refine wp_join_group (ts := []) (fun (_ : Tup Val []) mRt => ∃ sRt,
      FullDenseInvW c F0 F_cur sRt ∧ sRt.core.cur_vars = s.core.cur_vars ∧
      sRt.core.fuel.toNat ≤ s.core.fuel.toNat ∧ sRt.scratch.work_stk1 = ws1' ∧
      sRt.scratch.tarjan_mark = tmk' ∧
      fullSweepKittenConeOk F_cur sRt cls' nv.toNat nc.toNat ∧
      F0.Unsat ∧ (FullMem c sRt ⋆ R) mRt) ?_ ?_
  · intro _ () mRt ⟨sRt, hinvRt, hcvRt, hfuelRt, hwsRt, htmkRt, hconeRt, hunsRt, hmRt⟩
    ds_to_group
    refine sweep_tmk_clear_wp rfl rfl hnv_mx hinvRt hwsRt htmkRt (cone_stk_lt hconeRt)
      (fun u hu => htmk1' u (hcvRt ▸ hu)) hmRt fun _c m_end ht_len ht_done hm_end => by
        ds_steps
        exact hQ 20#64 _ m_end (fullDenseInvW_with_tmk hinvRt ht_len) hcvRt hfuelRt ht_done
          (Or.inr rfl) (fun _ => hunsRt) hm_end
  intro _ hJretB
  ds_steps
  exact sweep_kitten_add_bins_wp haddB rfl cs2_d.inv cs2_d.ws cs2_d.tmk cs2_d.cone
    hent1' hent2' cs2_d.mem
    (fun sX mX hinvX hcvX hfuelX hwsX htmkX hconeX hunsX hmX => hJretB () mX
      ⟨sX, hinvX, hcvX.trans cs2_d.cv, Nat.le_trans hfuelX cs2_d.fuel, hwsX, htmkX,
       hconeX, hunsX, hmX⟩)
    (fun sX mX hinvX hcvX hfuelX hwsX htmkX hscrX hconeX hmX => hJd2_e _ mX
      ⟨sX, hinvX, hcvX.trans cs2_d.cv, Nat.le_trans hfuelX cs2_d.fuel, hconeX, hwsX,
       htmkX, hscrX ▸ cs2_d.kinv, hmX⟩)

/-! ## 3. `full_sweep_dense_wp` (`FullDefSweep` #9) -/

/-- **`full_sweep_dense`**: dense-mode variable sweep driver, zeroing `tarjan_mark[0..cv)` and
invoking `full_sweep_var` across eligible `FL_ACTIVE | FL_SWEEP` unassigned variables. -/
theorem full_sweep_dense_wp (Γ : Env)
    (hvar : EnvSpec Γ "full_sweep_var" fullSweepVarKittenSpec) :
    ∀ args m Q X, fullSweepDenseSpec args m Q X →
      Func.wp Γ full_sweep_dense_body args m Q X := by
  rintro ⟨h, budget, tick_lim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hinv.lengths.core_ok.cur_vars_le
  have htmk_len := hinv.lengths.scratch_ok.tarjan_mark_len
  unfold Func.wp full_sweep_dense_body; ds_steps
  ds_split
  · ds_steps; exact hQ 1#64 s m hinv rfl (le_refl _) (Or.inl rfl) (fun h => by cases h) hm
  ds_split
  · ds_steps; exact hQ 1#64 s m hinv rfl (le_refl _) (Or.inl rfl) (fun h => by cases h) hm
  have h10240 : 10240 ≤ c.scratch_cap := by bv_omega
  ds_to_group
  refine wp_loop_inv (ts := [i64])
    (fun (i, ()) m0 => i.toNat ≤ s.core.cur_vars ∧ ∃ tmk0 : List (BitVec 32),
      tmk0.length = 2 * c.max_vars ∧ (∀ u < i.toNat, tmk0[u]?.getD 0#32 = 0#32) ∧
      (FullMem c { s with scratch := { s.scratch with tarjan_mark := tmk0 } } ⋆ R) m0)
    (fun (i, ()) _ => s.core.cur_vars - i.toNat)
    (fun _ hLi => by
      ds_steps
      exact hLi (0#64, ()) m
        ⟨Nat.zero_le _, s.scratch.tarjan_mark, htmk_len, fun _ hu => by simp at hu, hm⟩)
    (fun _ (i, ()) m0 ⟨hi_le, tmk0, ht0_len, ht0_cov, hm0⟩ hLi => by
      ds_split
      · have hi_lt : i.toNat < s.core.cur_vars := by bv_omega
        have hi_bd : i.toNat < tmk0.length := by omega
        have hi1 : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_lt (by omega)
        ds_steps; refine hLi (i + 1#64, ()) _ (by dsimp only; omega)
          ⟨by omega, tmk0.set i.toNat 0#32, List.length_set.trans ht0_len, fun u hu => ?_,
           by assumption⟩
        by_cases hui : u = i.toNat
        · subst hui; rw [List.getElem?_set_self (by omega)]; rfl
        · rw [List.getElem?_set_ne (Ne.symm hui)]; exact ht0_cov u (by omega)
      · have hi_eq : i.toNat = s.core.cur_vars := by
          have hlt : ¬ i.toNat < s.core.cur_vars := by bv_omega
          omega
        let s0 : FullState := { s with scratch := { s.scratch with tarjan_mark := tmk0 } }
        have hinv0 : FullDenseInv c F0 s0 := fullDenseInv_with_tmk hinv ht0_len
        have ht0_zero : TmkZero s0 := fun u hu => ht0_cov u (hi_eq ▸ hu)
        refine wp_join_group (ts := [i64, i64, i64])
          (fun (_bB, _vB, resB, ()) mB => ∃ sB, FullDenseInv c F0 sB ∧
            sB.core.cur_vars = s.core.cur_vars ∧ sB.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (resB = 1#64 ∨ resB = 20#64) ∧ (resB = 20#64 → F0.Unsat) ∧ (FullMem c sB ⋆ R) mB)
          (fun _ (_bB, _vB, resB, ()) mB ⟨sB, hinvB, hcvB, hfuelB, hresB, hunsB, hmB⟩ => by
            ds_steps; exact hQ resB sB mB hinvB hcvB hfuelB hresB hunsB hmB)
          (fun _ hJbrk => by
            refine wp_loop_inv (ts := [i64, i64])
              (fun (budgetL, vL, ()) ml => 10240 ≤ c.scratch_cap ∧ vL.toNat ≤ s.core.cur_vars ∧
                ∃ sL, FullDenseInv c F0 sL ∧ sL.core.cur_vars = s.core.cur_vars ∧
                  sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧ TmkZero sL ∧ (FullMem c sL ⋆ R) ml)
              (fun (_, vL, ()) _ => s.core.cur_vars - vL.toNat)
              (fun _ hLv => by
                ds_steps; exact hLv (budget, 0#64, ()) m0
                  ⟨h10240, Nat.zero_le _, s0, hinv0, rfl, le_refl _, ht0_zero, hm0⟩)
              (fun _ (budgetL, vL, ()) ml
                  ⟨hcapL, hv_le, sL, hinvL, hcvL, hfuelL, htmkL, hml⟩ hLv => by
                have hbrk := hJbrk (budgetL, vL, 1#64, ()) ml
                  ⟨sL, hinvL, hcvL, hfuelL, Or.inl rfl, (fun h => by cases h), hml⟩
                ds_split; rotate_left; · ds_steps; exact hbrk
                ds_split; rotate_left; · ds_steps; exact hbrk
                ds_split; rotate_left; · ds_steps; exact hbrk
                ds_split; rotate_left; · ds_steps; exact hbrk
                have hcvL_le := hinvL.lengths.core_ok.cur_vars_le
                have hv_lt : vL.toNat < sL.core.cur_vars := by
                  have : vL.toNat < sL.core.cur_vars % 2 ^ 64 := by bv_omega
                  omega
                have hfl_len := hinvL.lengths.core_ok.flags_len
                have hval_len := hinvL.lengths.core_ok.vals_len
                have hv_fl : vL.toNat < sL.core.flags.length := by omega
                have h2v_shl : (vL <<< (1 : Nat)).toNat = 2 * vL.toNat := by
                  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
                    Nat.mod_eq_of_lt (by omega : vL.toNat * 2 < 2 ^ 64)]; omega
                have h2v_vals : (vL <<< (1 : Nat)).toNat < sL.core.vals.length := by omega
                have hv1 : (vL + 1#64).toNat = vL.toNat + 1 := bv64_add1_lt (by omega)
                ds_steps
                · -- Sweep eligible variable `vL`
                  let flL' := sL.core.flags.set vL.toNat
                    ((sL.core.flags[vL.toNat]'hv_fl) &&& ~~~1024#32)
                  let sL' : FullState := { sL with core := { sL.core with flags := flL' } }
                  have hinvL' : FullDenseInv c F0 sL' :=
                    fullDenseInv_with_flags hinvL (List.length_set.trans hfl_len)
                  have htmkL' : TmkZero sL' := htmkL.congr rfl rfl
                  obtain ⟨F_curL, hwL⟩ := hinvL'.exists_witness
                  have hv32 : (vL.setWidth 32).toNat < sL'.core.cur_vars := by
                    rw [bv64_to32_toNat vL (by omega)]; exact hv_lt
                  c0_call hvar
                  refine ⟨c, F0, F_curL, sL', R, rfl, hwL, hcapL, hv32, htmkL',
                    by assumption, fun rV sV mV hwV hcvV hfuelV htmkV hrV_dom hrV_uns hmV => ?_⟩
                  have hfuelV0 := Nat.le_trans hfuelV hfuelL
                  ds_split
                  · have hrV20 : rV = 20#64 := by bv_omega
                    ds_steps; exact hJbrk (budgetL - 1#64, vL, 20#64, ()) mV
                      ⟨sV, hwV.toDense, hcvV.trans hcvL, hfuelV0, Or.inr rfl,
                       (fun _ => hrV_uns hrV20), hmV⟩
                  · ds_steps; exact hLv (budgetL - 1#64, vL + 1#64, ()) mV (by dsimp only; omega)
                      ⟨hcapL, by omega, sV, hwV.toDense, hcvV.trans hcvL, hfuelV0, htmkV, hmV⟩
                · ds_steps; exact hLv (budgetL, vL + 1#64, ()) ml (by dsimp only; omega)
                    ⟨hcapL, by omega, sL, hinvL, hcvL, hfuelL, htmkL, hml⟩
                · ds_steps; exact hLv (budgetL, vL + 1#64, ()) ml (by dsimp only; omega)
                    ⟨hcapL, by omega, sL, hinvL, hcvL, hfuelL, htmkL, hml⟩)))

end LeanQbe.T.Examples.Kissat.FullDefSweep
